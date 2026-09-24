// The default backend for x86-64, which requires the AVX and FMA target
// features (Haswell, 2013).
//
// It is the method of `sse42` — the fast paths of the generic backend computed
// on both lanes at once, with the few inputs that fail their checks in either
// lane recomputed by the generic backend (see `lanewise.rs`) — with the FMA,
// which makes TwoProduct and the remainders of division and of the square root
// one instruction each instead of Dekker's algorithm.
//
// The obvious alternative is to let the hardware round: `vaddpd` and friends
// with MXCSR set to round toward +∞. That is what this backend replaced, and it
// is slower, because MXCSR has to be saved, set and restored around every
// operation, which serializes them. Computing the fast path explicitly takes
// more instructions, but they pipeline: on Zen 2 it makes interval addition
// 0.47× and a 3×3 determinant 0.33× of the rounding-mode-switching version (see
// BENCHMARKS.md). Only three latency-bound primitives lose, by 3 to 12%.
//
// The scalar operations are those of the generic backend, which uses the FMA
// here as well.

use super::lanewise::{
    add_i64, andnot, div_rn, exponent_gt, exponent_in, exponent_le, is_finite, is_special, lane0,
    mul_rn, not, or_generic, select, sqrt_rn, step_up, sub_i64, two_sum_err, zero,
};
use super::{add_rn, and, eq, extract, gt, lt, or, sub_rn, F64X2};
use crate::simd::generic;
use std::arch::x86_64::*;

pub(crate) use super::lanewise::{add_ru, sqrt1_ru, sub1_ru, sub_ru};
#[cfg(test)]
pub(crate) use super::lanewise::{sqrt1_rd_mxcsr, sqrt1_ru_mxcsr};

/// `div_ru([x0, x1], [y0, y1]) = [x0 / y0, x1 / y1]` rounded toward +∞.
pub(crate) fn div_ru(x: F64X2, y: F64X2) -> F64X2 {
    // See `generic::div1_ru_fast`, the FMA variant.
    let q = div_rn(x, y);
    let special = is_special(x, y);
    // The remainder is representable where the check passes, so the FMA computes
    // it exactly.
    let r = fnmadd(q, y, x);
    let ok = or(
        special,
        and(exponent_in(q, -1022, 1023), exponent_gt(x, -968)),
    );
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
    // hypotheses. Rounding to nearest is the FMA itself here, so the emulation
    // that `sse42` needs, and the TwoSum it is built from, are gone.
    let u1 = mul_rn(a, b);
    let u2 = two_prod_err(a, b, u1);
    let r1 = fmadd(a, b, c);
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
                and(two_prod_is_exact(u1), exponent_le(u1, 1021)),
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
    let e = two_prod_err(x, y, p);
    let special = is_special(x, y);
    let ok = or(special, two_prod_is_exact(p));
    let up = andnot(gt(e, zero()), special);
    or_generic(ok, select(up, step_up(p), p), || {
        generic::mul_ru(extract(x), extract(y))
    })
}

/// `sqrt_rd_ru([x0, x1]) = [√x0, √x1]`, the first rounded toward -∞ and the
/// second toward +∞.
pub(crate) fn sqrt_rd_ru(x: F64X2) -> F64X2 {
    // The lane-wise form of `generic::sqrt1_fast` with an FMA, correcting the two
    // lanes in opposite directions.
    let s = sqrt_rn(x);
    // x - s² is representable where the check passes, so the FMA computes it
    // exactly.
    let r = fnmadd(s, s, x);
    // The remainder is representable if 2^-966 <= x < 2^1024, which also excludes
    // ±0, +∞ and NaN, but not negative numbers: for those, s and r are NaN, the
    // comparisons below are false, and NaN is returned.
    let ok = exponent_in(x, -966, 1023);
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

/// `fmadd([x0, x1], [y0, y1], [z0, z1]) = [x0 * y0 + z0, x1 * y1 + z1]` with a
/// single rounding to nearest.
fn fmadd(x: F64X2, y: F64X2, z: F64X2) -> F64X2 {
    unsafe { _mm_fmadd_pd(x, y, z) }
}

/// `fnmadd([x0, x1], [y0, y1], [z0, z1]) = [z0 - x0 * y0, z1 - x1 * y1]` with a
/// single rounding to nearest.
fn fnmadd(x: F64X2, y: F64X2, z: F64X2) -> F64X2 {
    unsafe { _mm_fnmadd_pd(x, y, z) }
}

/// Returns the error e = x * y - p, where p = RN(x * y). See `generic::two_prod_err`.
fn two_prod_err(x: F64X2, y: F64X2, p: F64X2) -> F64X2 {
    unsafe { _mm_fmsub_pd(x, y, p) }
}

// The lanes where `two_prod_err(x, y, x * y)` is exact, which with an FMA depends
// on the product alone. See `generic::two_prod_is_exact`.
fn two_prod_is_exact(p: F64X2) -> F64X2 {
    exponent_in(p, -968, 1023)
}
