// A backend for x86-64 without AVX, which requires the SSE4.2 target feature
// (Nehalem, 2008).
//
// SSE has no per-instruction rounding mode, and saving, setting and restoring
// MXCSR around every operation serializes them: about 9 ns per operation on Zen
// 2 (see BENCHMARKS.md). So the operations that round upward use the method of
// the generic backend (see `generic.rs`) instead: the fast paths are the same,
// computed on both lanes at once, and the few inputs that fail their checks in
// either lane are recomputed by the generic backend. `mul_ru` goes further: where
// x and y are nonzero and |RN(x * y)| < 2^-968, which sends the generic backend
// to its slow path, it computes RU(x * y) itself (see `mul_ru_tiny`). Without
// FMA, Dekker's TwoProduct is used throughout. The scalar operations are those
// of the generic backend.
//
// This is a port of the `wasm32` backend, which is the same method on a
// different instruction set. The parts that do not depend on having an FMA are
// in `lanewise.rs`, which the `fma` backend shares, and the operations that do
// not depend on the rounding mode are in the parent module, which every x86-64
// backend shares.

use super::lanewise::{
    add_i64, andnot, div_rn, exponent_gt, exponent_in, exponent_le, gt_i64, is_finite, is_special,
    lane0, mul_rn, not, or_generic, select, splat_i64, sqrt_rn, step_up, sub_i64, two_sum_err,
    zero,
};
use super::{add_rn, all, and, eq, extract, gt, lt, or, splat, sub_rn, xor, F64X2};
use crate::simd::generic;
use std::arch::x86_64::*;

pub(crate) use super::lanewise::{add_ru, sqrt1_ru, sub1_ru, sub_ru};
#[cfg(test)]
pub(crate) use super::lanewise::{sqrt1_rd_mxcsr, sqrt1_ru_mxcsr};

/// `div_ru([x0, x1], [y0, y1]) = [x0 / y0, x1 / y1]` rounded toward +∞.
pub(crate) fn div_ru(x: F64X2, y: F64X2) -> F64X2 {
    // See `generic::div1_ru_fast`, Dekker's variant.
    let q = div_rn(x, y);
    let special = is_special(x, y);
    let exact = and(exponent_in(q, -1022, 1023), exponent_gt(x, -968));
    let p = mul_rn(q, y);
    let dekker = and(
        and(exponent_le(q, 995), exponent_le(y, 995)),
        exponent_le(x, 1021),
    );
    let r = sub_rn(sub_rn(x, p), two_prod_err(q, y, p));
    let ok = or(special, and(exact, dekker));
    // x / y > q ⟺ r / y > 0. y is nonzero and r is not NaN unless special.
    let up = or(
        and(gt(r, zero()), gt(y, zero())),
        and(lt(r, zero()), lt(y, zero())),
    );
    let res = select(andnot(up, special), step_up(q), q);
    or_generic(ok, res, || generic::div_ru(extract(x), extract(y)))
}

/// `mul_add_ru([x0, x1], [y0, y1], [z0, z1]) = [x0 * y0 + z0, x1 * y1 + z1]`
/// rounded toward +∞ (with a single rounding).
pub(crate) fn mul_add_ru(a: F64X2, b: F64X2, c: F64X2) -> F64X2 {
    // See `generic::mul_add1_ru_fast` for the algorithm (ErrFma) and its
    // hypotheses, with the FMA emulated by `generic::mul_add1_rn_emulated`.
    let u1 = mul_rn(a, b);
    let u2 = two_prod_err(a, b, u1);
    let t1 = add_rn(c, u1);
    let t2 = two_sum_err(c, u1, t1);
    let r1 = add_rn(t1, add_odd(t2, u2));
    let alpha1 = add_rn(c, u2);
    let alpha2 = two_sum_err(c, u2, alpha1);
    let beta1 = add_rn(u1, alpha1);
    let beta2 = two_sum_err(u1, alpha1, beta1);
    let gamma = add_rn(sub_rn(beta1, r1), beta2);
    let err = add_rn(gamma, alpha2);

    let finite_ab = and(is_finite(a), is_finite(b));
    let special = or(not(is_finite(c)), is_special(a, b));
    let not_tiny = |x: F64X2, e_min: i64| or(eq(x, zero()), exponent_gt(x, e_min - 1));
    let ok = or(
        special,
        and(
            and(
                and(two_prod_is_exact(a, b, u1), exponent_le(u1, 1021)),
                and(exponent_le(c, 1021), is_finite(r1)),
            ),
            and(
                not_tiny(r1, -1022),
                and(not_tiny(alpha1, -1021), not_tiny(beta1, -1020)),
            ),
        ),
    );
    // `generic::mul_add1_special`: a * b is finite (though RN(a * b) may
    // overflow) and c is not, or else a * b is exact and adding c is exact too.
    let special_r = select(andnot(finite_ab, is_finite(c)), c, add_rn(mul_rn(a, b), c));
    // If err > 0, then r1 is inexact and thus nonzero.
    let r = select(special, special_r, select(gt(err, zero()), step_up(r1), r1));
    or_generic(ok, r, || {
        generic::mul_add_ru(extract(a), extract(b), extract(c))
    })
}

/// `mul_ru([x0, x1], [y0, y1]) = [x0 * y0, x1 * y1]` rounded toward +∞.
pub(crate) fn mul_ru(x: F64X2, y: F64X2) -> F64X2 {
    // See `generic::mul1_ru_fast`.
    let p = mul_rn(x, y);
    let special = is_special(x, y);
    let ok = or(special, two_prod_is_exact(x, y, p));
    // Each branch rounds by itself, as in `fma::mul_ru`.
    if all(ok) {
        mul_ru_fast(x, y, p, special)
    } else {
        mul_ru_tiny(x, y, p, ok, special)
    }
}

/// Returns RU(x * y) from p = RN(x * y), in the lanes that are `special` or
/// where `two_prod_is_exact(x, y, p)`.
fn mul_ru_fast(x: F64X2, y: F64X2, p: F64X2, special: F64X2) -> F64X2 {
    let e = two_prod_err(x, y, p);
    let up = andnot(gt(e, zero()), special);
    select(up, step_up(p), p)
}

/// `mul_ru` where some lane fails `ok`: there, x and y are finite and nonzero,
/// and p = RN(x * y) is below 2^-968 or at least 2^1023 in magnitude, or x or y
/// is at least 2^996 in magnitude.
///
/// This is `fma::mul_ru_tiny` with Dekker's TwoProduct, which also bounds the
/// factors. See there for why the result is RU(x * y).
fn mul_ru_tiny(x: F64X2, y: F64X2, p: F64X2, ok: F64X2, special: F64X2) -> F64X2 {
    // Powers of two, so that scaling by them is exact unless it overflows or
    // underflows.
    const TWO_POW_64: f64 = 18446744073709551616.0;
    const TWO_POW_128: f64 = TWO_POW_64 * TWO_POW_64;
    const TWO_POW_M128: f64 = 1.0 / TWO_POW_128;
    // Let z = x * y exactly, and S = 2^128. If |p| < 2^-968, then |z| < 2^-968,
    // and as |x|, |y| >= 2^-1074, |x|, |y| < 2^106. So x * S is exact, and
    // |x * S| < 2^234 and |y| < 2^106 are below the 2^996 that `split` needs.
    // In a lane that fails `ok` for another reason, |y| >= 2^996, or x * S or ps
    // overflows, and the lane fails the check at the end.
    let xs = mul_rn(x, splat(TWO_POW_128));
    let ps = mul_rn(xs, y);
    // rs = RU(z * S) where `two_prod_is_exact(xs, y, ps)`, as in `mul_ru`.
    let rs = mul_ru_fast(xs, y, ps, special);
    // RU(z) = RU(rs / S), which is q = RN(rs / S) or its successor. q * S is
    // exact, so comparing it with rs decides which.
    let q = mul_rn(rs, splat(TWO_POW_M128));
    let q = select(lt(mul_rn(q, splat(TWO_POW_128)), rs), step_up(q), q);
    // If p = ±0, then |z| <= 2^-1075, and RU(z) is 2^-1074 for z > 0 and -0 for
    // z < 0. p has the sign of z, and as integers, -0 < 0 and 2^-1074 = 1.
    // Otherwise |z| > 2^-1075, so 2^-947 < |z * S| < 2^-840, and
    // `two_prod_is_exact(xs, y, ps)` holds: every lane with |p| < 2^-968 is
    // computed here, and only those with |p| >= 2^1023, or with a factor of 2^996
    // or more, go to the generic backend.
    let p_zero = eq(p, zero());
    let zero_rule = select(gt_i64(zero(), p), p, splat_i64(1));
    let r = mul_ru_fast(x, y, p, special);
    let res = select(ok, r, select(p_zero, zero_rule, q));
    let ok = or(ok, or(p_zero, two_prod_is_exact(xs, y, ps)));
    or_generic(ok, res, || generic::mul_ru(extract(x), extract(y)))
}

/// `sqrt_rd_ru([x0, x1]) = [√x0, √x1]`, the first rounded toward -∞ and the
/// second toward +∞.
pub(crate) fn sqrt_rd_ru(x: F64X2) -> F64X2 {
    // The lane-wise form of `generic::sqrt1_fast`, Dekker's variant, correcting
    // the two lanes in opposite directions.
    let s = sqrt_rn(x);
    let p = mul_rn(s, s);
    // x - p is exact by Sterbenz's lemma, and so is the last subtraction.
    let r = sub_rn(sub_rn(x, p), two_prod_err(s, s, p));
    // The remainder is representable if 2^-966 <= x < 2^1022, which also excludes
    // ±0, +∞ and NaN, but not negative numbers: for those, s and r are NaN, the
    // comparisons below are false, and NaN is returned.
    let ok = exponent_in(x, -966, 1021);
    // √x < s ⟺ x - s² < 0, and then the result is the predecessor of s. Lane 0
    // rounds toward -∞, lane 1 toward +∞. Where a lane is corrected, s >= 2^-483,
    // so stepping is incrementing or decrementing its bits.
    let down = and(lt(r, zero()), lane0());
    let up = andnot(gt(r, zero()), lane0());
    let stepped = sub_i64(add_i64(s, down), up);
    or_generic(ok, stepped, || generic::sqrt_rd_ru(extract(x)))
}

/// `sqrt1_rd(x) = √x` rounded toward -∞.
// Part of the backend interface, but nothing calls it here: `Interval::sqrt`
// needs a lone square root only for an interval containing zero, which rounds
// up, and `sqrt_rd_ru` falls back to `generic` as a pair.
#[allow(dead_code)]
pub(crate) fn sqrt1_rd(x: f64) -> f64 {
    generic::sqrt1_rd(x)
}

/// Splits x into x_hi + x_lo, each with at most 26 significant bits. See `generic::split`.
fn split(x: F64X2) -> (F64X2, F64X2) {
    // 2^27 + 1.
    let t = mul_rn(splat(134217729.0), x);
    let hi = sub_rn(t, sub_rn(t, x));
    (hi, sub_rn(x, hi))
}

/// Returns the error e = x * y - p, where p = RN(x * y), with Dekker's algorithm.
/// See `generic::two_prod_err`.
fn two_prod_err(x: F64X2, y: F64X2, p: F64X2) -> F64X2 {
    let (xh, xl) = split(x);
    let (yh, yl) = split(y);
    let t = add_rn(
        add_rn(sub_rn(mul_rn(xh, yh), p), mul_rn(xh, yl)),
        mul_rn(xl, yh),
    );
    add_rn(t, mul_rn(xl, yl))
}

// The lanes where `two_prod_err(x, y, x * y)` is exact. See `generic::two_prod_is_exact`.
fn two_prod_is_exact(x: F64X2, y: F64X2, p: F64X2) -> F64X2 {
    and(
        exponent_in(p, -968, 1022),
        and(exponent_le(x, 995), exponent_le(y, 995)),
    )
}

// Returns RN(x + y) rounded to odd instead. See `generic::add_odd`.
fn add_odd(x: F64X2, y: F64X2) -> F64X2 {
    let s = add_rn(x, y);
    let e = two_sum_err(x, y, s);
    let even = eq_i64(and(s, splat_i64(1)), zero());
    let inexact_even = and(ne(e, zero()), even);
    // s is nonzero if inexact. Moving toward the larger magnitude increments the
    // bit pattern, and toward the smaller one decrements it.
    let toward_larger = not(xor(gt(e, zero()), gt(s, zero())));
    let odd = select(
        toward_larger,
        add_i64(s, splat_i64(1)),
        sub_i64(s, splat_i64(1)),
    );
    select(inexact_even, odd, s)
}

fn eq_i64(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_castsi128_pd(_mm_cmpeq_epi64(_mm_castpd_si128(x), _mm_castpd_si128(y))) }
}

fn ne(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_cmpneq_pd(x, y) }
}
