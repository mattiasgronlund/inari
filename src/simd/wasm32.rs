// A backend for wasm32 with the `simd128` target feature, which keeps `F64X2` in
// a `v128` register.
//
// WebAssembly has only round-to-nearest arithmetic, so the operations that round
// upward use the method of the generic backend (see `generic.rs`): the fast paths
// are the same, computed on both lanes at once, and the few inputs that fail
// their checks in either lane are recomputed by the generic backend. `mul_ru`
// goes further: where x and y are nonzero and |RN(x * y)| < 2^-968, which its
// fast path rejects, it computes RU(x * y) itself, as `generic::mul1_ru_tiny`
// does (see `mul_ru_tiny`). WebAssembly has no FMA (relaxed-simd's
// `f64x2.relaxed_madd` may round twice), so Dekker's TwoProduct is used
// throughout. The scalar operations are those of the generic backend.

use super::generic;
use std::arch::wasm32::*;

pub(crate) const HAS_MAXIMUM: bool = true;

pub(crate) type F64X2 = v128;

pub(crate) fn abs(x: F64X2) -> F64X2 {
    f64x2_abs(x)
}

/// `add_rn([x0, x1], [y0, y1]) = [x0 + y0, x1 + y1]` rounded to nearest.
pub(crate) fn add_rn(x: F64X2, y: F64X2) -> F64X2 {
    f64x2_add(x, y)
}

/// `add_ru([x0, x1], [y0, y1]) = [x0 + y0, x1 + y1]` rounded toward +∞.
pub(crate) fn add_ru(x: F64X2, y: F64X2) -> F64X2 {
    // See `generic::add1_ru_fast`.
    let s = f64x2_add(x, y);
    let e = two_sum_err(x, y, s);
    let finite = and(is_finite(x), is_finite(y));
    let ok = or(
        v128_not(finite),
        and(
            and(exponent_le(x, 1022), exponent_le(y, 1022)),
            is_finite(s),
        ),
    );
    let up = and(finite, f64x2_gt(e, ZERO));
    or_generic(ok, select(up, step_up(s), s), || {
        generic::add_ru(extract(x), extract(y))
    })
}

pub(crate) fn all(x: F64X2) -> bool {
    bitmask(x) == 3
}

pub(crate) fn and(x: F64X2, y: F64X2) -> F64X2 {
    v128_and(x, y)
}

pub(crate) fn any(x: F64X2) -> bool {
    bitmask(x) != 0
}

pub(crate) fn bitmask(x: F64X2) -> u32 {
    i64x2_bitmask(x) as u32
}

pub(crate) fn ceil(x: F64X2) -> F64X2 {
    f64x2_ceil(x)
}

pub(crate) fn constant(x: f64, y: f64) -> F64X2 {
    f64x2(x, y)
}

/// `div_ru([x0, x1], [y0, y1]) = [x0 / y0, x1 / y1]` rounded toward +∞.
pub(crate) fn div_ru(x: F64X2, y: F64X2) -> F64X2 {
    // See `generic::div1_ru_fast`, Dekker's variant.
    let q = f64x2_div(x, y);
    let special = is_special(x, y);
    let exact = and(exponent_in(q, -1022, 1023), v128_not(exponent_le(x, -968)));
    let p = f64x2_mul(q, y);
    let dekker = and(
        and(exponent_le(q, 995), exponent_le(y, 995)),
        exponent_le(x, 1021),
    );
    let r = f64x2_sub(f64x2_sub(x, p), two_prod_err(q, y, p));
    let ok = or(special, and(exact, dekker));
    // x / y > q ⟺ r / y > 0. y is nonzero and r is not NaN unless special.
    let up = or(
        and(f64x2_gt(r, ZERO), f64x2_gt(y, ZERO)),
        and(f64x2_lt(r, ZERO), f64x2_lt(y, ZERO)),
    );
    let res = select(v128_andnot(up, special), step_up(q), q);
    or_generic(ok, res, || generic::div_ru(extract(x), extract(y)))
}

pub(crate) fn eq(x: F64X2, y: F64X2) -> F64X2 {
    f64x2_eq(x, y)
}

pub(crate) fn extract(x: F64X2) -> [f64; 2] {
    [extract0(x), extract1(x)]
}

pub(crate) fn extract0(x: F64X2) -> f64 {
    f64x2_extract_lane::<0>(x)
}

pub(crate) fn extract1(x: F64X2) -> f64 {
    f64x2_extract_lane::<1>(x)
}

pub(crate) fn floor(x: F64X2) -> F64X2 {
    f64x2_floor(x)
}

pub(crate) fn ge(x: F64X2, y: F64X2) -> F64X2 {
    f64x2_ge(x, y)
}

pub(crate) fn gt(x: F64X2, y: F64X2) -> F64X2 {
    f64x2_gt(x, y)
}

/// `hadd_rn([x0, x1], [y0, y1]) = [x0 + x1, y0 + y1]` rounded to nearest.
pub(crate) fn hadd_rn(x: F64X2, y: F64X2) -> F64X2 {
    f64x2_add(shuffle02(x, y), shuffle13(x, y))
}

pub(crate) fn le(x: F64X2, y: F64X2) -> F64X2 {
    f64x2_le(x, y)
}

pub(crate) fn lt(x: F64X2, y: F64X2) -> F64X2 {
    f64x2_lt(x, y)
}

// The vector version of the `maximumNumber` operation defined in IEEE 754-2019,
// which does not propagate NaNs.
pub(crate) fn max(x: F64X2, y: F64X2) -> F64X2 {
    let m = f64x2_max(x, y);
    select(is_nan(x), y, select(is_nan(y), x, m))
}

// The vector version of the `maximum` operation defined in IEEE 754-2019,
// which propagates NaNs. This is `f64x2.max`.
pub(crate) fn maximum(x: F64X2, y: F64X2) -> F64X2 {
    f64x2_max(x, y)
}

pub(crate) fn min(x: F64X2, y: F64X2) -> F64X2 {
    let m = f64x2_min(x, y);
    select(is_nan(x), y, select(is_nan(y), x, m))
}

pub(crate) fn minimum(x: F64X2, y: F64X2) -> F64X2 {
    f64x2_min(x, y)
}

/// `mul_add_ru([x0, x1], [y0, y1], [z0, z1]) = [x0 * y0 + z0, x1 * y1 + z1]`
/// rounded toward +∞ (with a single rounding).
pub(crate) fn mul_add_ru(a: F64X2, b: F64X2, c: F64X2) -> F64X2 {
    // See `generic::mul_add1_ru_fast` for the algorithm (ErrFma) and its
    // hypotheses, with the FMA emulated by `generic::mul_add1_rn_emulated`.
    let u1 = f64x2_mul(a, b);
    let u2 = two_prod_err(a, b, u1);
    let t1 = f64x2_add(c, u1);
    let t2 = two_sum_err(c, u1, t1);
    let r1 = f64x2_add(t1, add_odd(t2, u2));
    let alpha1 = f64x2_add(c, u2);
    let alpha2 = two_sum_err(c, u2, alpha1);
    let beta1 = f64x2_add(u1, alpha1);
    let beta2 = two_sum_err(u1, alpha1, beta1);
    let gamma = f64x2_add(f64x2_sub(beta1, r1), beta2);
    let err = f64x2_add(gamma, alpha2);

    let finite_ab = and(is_finite(a), is_finite(b));
    let special = or(v128_not(is_finite(c)), is_special(a, b));
    let not_tiny =
        |x: F64X2, e_min: i64| or(f64x2_eq(x, ZERO), v128_not(exponent_le(x, e_min - 1)));
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
    let special_r = select(
        v128_andnot(finite_ab, is_finite(c)),
        c,
        f64x2_add(f64x2_mul(a, b), c),
    );
    // If err > 0, then r1 is inexact and thus nonzero.
    let r = select(
        special,
        special_r,
        select(f64x2_gt(err, ZERO), step_up(r1), r1),
    );
    or_generic(ok, r, || {
        generic::mul_add_ru(extract(a), extract(b), extract(c))
    })
}

/// `mul_ru([x0, x1], [y0, y1]) = [x0 * y0, x1 * y1]` rounded toward +∞.
pub(crate) fn mul_ru(x: F64X2, y: F64X2) -> F64X2 {
    // See `generic::mul1_ru_fast`.
    let p = f64x2_mul(x, y);
    let special = is_special(x, y);
    let ok = or(special, two_prod_is_exact(x, y, p));
    // Each branch rounds by itself, as in `x86_64::fma::mul_ru`.
    if i64x2_all_true(ok) {
        mul_ru_fast(x, y, p, special)
    } else {
        mul_ru_tiny(x, y, p, ok, special)
    }
}

/// Returns RU(x * y) from p = RN(x * y), in the lanes that are `special` or
/// where `two_prod_is_exact(x, y, p)`.
fn mul_ru_fast(x: F64X2, y: F64X2, p: F64X2, special: F64X2) -> F64X2 {
    let e = two_prod_err(x, y, p);
    let up = v128_andnot(f64x2_gt(e, ZERO), special);
    select(up, step_up(p), p)
}

/// `mul_ru` where some lane fails `ok`: there, x and y are finite and nonzero,
/// and p = RN(x * y) is below 2^-968 or at least 2^1023 in magnitude, or x or y
/// is at least 2^996 in magnitude.
///
/// This is `x86_64::fma::mul_ru_tiny` with Dekker's TwoProduct, which also
/// bounds the factors. See there for why the result is RU(x * y).
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
    let xs = f64x2_mul(x, splat(TWO_POW_128));
    let ps = f64x2_mul(xs, y);
    // rs = RU(z * S) where `two_prod_is_exact(xs, y, ps)`, as in `mul_ru`.
    let rs = mul_ru_fast(xs, y, ps, special);
    // RU(z) = RU(rs / S), which is q = RN(rs / S) or its successor. q * S is
    // exact, so comparing it with rs decides which.
    let q = f64x2_mul(rs, splat(TWO_POW_M128));
    let qs = f64x2_mul(q, splat(TWO_POW_128));
    let q = select(f64x2_lt(qs, rs), step_up(q), q);
    // If p = ±0, then |z| <= 2^-1075, and RU(z) is 2^-1074 for z > 0 and -0 for
    // z < 0. p has the sign of z, and as integers, -0 < 0 and 2^-1074 = 1.
    // Otherwise |z| > 2^-1075, so 2^-947 < |z * S| < 2^-840, and
    // `two_prod_is_exact(xs, y, ps)` holds: every lane with |p| < 2^-968 is
    // computed here, and only those with |p| >= 2^1023, or with a factor of 2^996
    // or more, go to the generic backend.
    let p_zero = f64x2_eq(p, ZERO);
    let zero_rule = select(i64x2_lt(p, ZERO), p, i64x2_splat(1));
    let r = mul_ru_fast(x, y, p, special);
    let res = select(ok, r, select(p_zero, zero_rule, q));
    let ok = or(ok, or(p_zero, two_prod_is_exact(xs, y, ps)));
    or_generic(ok, res, || generic::mul_ru(extract(x), extract(y)))
}

pub(crate) fn neg(x: F64X2) -> F64X2 {
    f64x2_neg(x)
}

/// `neg0([x0, x1]) = [-x0, x1]`
pub(crate) fn neg0(x: F64X2) -> F64X2 {
    v128_xor(x, constant(-0.0, 0.0))
}

pub(crate) fn or(x: F64X2, y: F64X2) -> F64X2 {
    v128_or(x, y)
}

// WebAssembly has no instruction that rounds ties away from zero.
pub(crate) fn round(x: F64X2) -> F64X2 {
    constant(extract0(x).round(), extract1(x).round())
}

pub(crate) fn round_ties_even(x: F64X2) -> F64X2 {
    f64x2_nearest(x)
}

/// `shuffle02([x0, x1], [x2, x3]) = [x0, x2]`
pub(crate) fn shuffle02(x: F64X2, y: F64X2) -> F64X2 {
    i64x2_shuffle::<0, 2>(x, y)
}

/// `shuffle03([x0, x1], [x2, x3]) = [x0, x3]`
pub(crate) fn shuffle03(x: F64X2, y: F64X2) -> F64X2 {
    i64x2_shuffle::<0, 3>(x, y)
}

/// `shuffle13([x0, x1], [x2, x3]) = [x1, x3]`
pub(crate) fn shuffle13(x: F64X2, y: F64X2) -> F64X2 {
    i64x2_shuffle::<1, 3>(x, y)
}

pub(crate) fn splat(x: f64) -> F64X2 {
    f64x2_splat(x)
}

/// `sqrt_rd_ru([x0, x1]) = [√x0, √x1]`, the first rounded toward -∞ and the
/// second toward +∞.
pub(crate) fn sqrt_rd_ru(x: F64X2) -> F64X2 {
    // The lane-wise form of `generic::sqrt1_fast`, Dekker's variant, correcting
    // the two lanes in opposite directions.
    let s = f64x2_sqrt(x);
    let p = f64x2_mul(s, s);
    // x - p is exact by Sterbenz's lemma, and so is the last subtraction.
    let r = f64x2_sub(f64x2_sub(x, p), two_prod_err(s, s, p));
    // The remainder is representable if 2^-966 <= x < 2^1022, which also excludes
    // ±0, +∞ and NaN, but not negative numbers: for those, s and r are NaN, the
    // comparisons below are false, and NaN is returned.
    let ok = exponent_in(x, -966, 1021);
    // √x < s ⟺ x - s² < 0, and then the result is the predecessor of s. Lane 0
    // rounds toward -∞, lane 1 toward +∞. Where a lane is corrected, s >= 2^-483,
    // so stepping is incrementing or decrementing its bits.
    let down = and(f64x2_lt(r, ZERO), LANE0);
    let up = v128_andnot(f64x2_gt(r, ZERO), LANE0);
    let stepped = i64x2_sub(i64x2_add(s, down), up);
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

/// `sqrt1_ru(x) = √x` rounded toward +∞.
pub(crate) fn sqrt1_ru(x: f64) -> f64 {
    generic::sqrt1_ru(x)
}

/// `sub_rn([x0, x1], [y0, y1]) = [x0 - y0, x1 - y1]` rounded to nearest.
pub(crate) fn sub_rn(x: F64X2, y: F64X2) -> F64X2 {
    f64x2_sub(x, y)
}

/// `sub_ru([x0, x1], [y0, y1]) = [x0 - y0, x1 - y1]` rounded toward +∞.
pub(crate) fn sub_ru(x: F64X2, y: F64X2) -> F64X2 {
    // x - y is defined as x + (-y) by IEEE 754, including the signs of zeros.
    add_ru(x, neg(y))
}

/// `sub1_ru(x, y) = x - y` rounded toward +∞.
pub(crate) fn sub1_ru(x: f64, y: f64) -> f64 {
    generic::sub1_ru(x, y)
}

pub(crate) fn swap(x: F64X2) -> F64X2 {
    i64x2_shuffle::<1, 0>(x, x)
}

pub(crate) fn trunc(x: F64X2) -> F64X2 {
    f64x2_trunc(x)
}

// Lane-wise versions of the helpers of the generic backend. Masks have all bits
// of a lane set for true, and none for false.

const ZERO: F64X2 = f64x2(0.0, 0.0);

/// The mask of lane 0 alone.
const LANE0: F64X2 = i64x2(-1, 0);

/// `select(m, x, y)` takes the lanes of x where m is set, and those of y elsewhere.
fn select(m: F64X2, x: F64X2, y: F64X2) -> F64X2 {
    v128_bitselect(x, y, m)
}

// Returns `r` if the fast path is valid in both lanes (`ok`), and otherwise the
// result of the generic backend, which recomputes the lanes that are not.
fn or_generic(ok: F64X2, r: F64X2, generic: impl FnOnce() -> [f64; 2]) -> F64X2 {
    if i64x2_all_true(ok) {
        r
    } else {
        let [r0, r1] = generic();
        constant(r0, r1)
    }
}

// The unbiased exponents of the lanes of x as i64 lanes: floor(log2(|x|)) if x
// is normal, -1023 if x is zero or subnormal, and 1024 if x is infinite or NaN.
fn exponent(x: F64X2) -> v128 {
    i64x2_sub(
        v128_and(u64x2_shr(x, 52), i64x2_splat(0x7ff)),
        i64x2_splat(1023),
    )
}

// The lanes where exponent(x) <= hi.
fn exponent_le(x: F64X2, hi: i64) -> F64X2 {
    i64x2_le(exponent(x), i64x2_splat(hi))
}

// The lanes where lo <= exponent(x) <= hi.
fn exponent_in(x: F64X2, lo: i64, hi: i64) -> F64X2 {
    let e = exponent(x);
    and(i64x2_ge(e, i64x2_splat(lo)), i64x2_le(e, i64x2_splat(hi)))
}

fn is_finite(x: F64X2) -> F64X2 {
    exponent_le(x, 1023)
}

fn is_nan(x: F64X2) -> F64X2 {
    f64x2_ne(x, x)
}

// The lanes where x or y is ±0, ±∞ or NaN, for which the product and the
// quotient in the default rounding mode are exact.
fn is_special(x: F64X2, y: F64X2) -> F64X2 {
    or(
        v128_not(and(is_finite(x), is_finite(y))),
        or(f64x2_eq(x, ZERO), f64x2_eq(y, ZERO)),
    )
}

/// Returns the successors of the lanes of x that are finite. See `generic::step_up`.
fn step_up(x: F64X2) -> F64X2 {
    // The masks are -1 as integers: subtracting the mask of x > 0 increments the
    // bit pattern, and adding that of x < 0 decrements it.
    let b = i64x2_add(i64x2_sub(x, f64x2_gt(x, ZERO)), f64x2_lt(x, ZERO));
    select(f64x2_eq(x, ZERO), i64x2_splat(1), b)
}

/// Returns the error e = (x + y) - s, where s = RN(x + y). See `generic::two_sum_err`.
fn two_sum_err(x: F64X2, y: F64X2, s: F64X2) -> F64X2 {
    let a = f64x2_sub(s, y);
    let b = f64x2_sub(s, a);
    f64x2_add(f64x2_sub(x, a), f64x2_sub(y, b))
}

/// Splits x into x_hi + x_lo, each with at most 26 significant bits. See `generic::split`.
fn split(x: F64X2) -> (F64X2, F64X2) {
    // 2^27 + 1.
    let t = f64x2_mul(splat(134217729.0), x);
    let hi = f64x2_sub(t, f64x2_sub(t, x));
    (hi, f64x2_sub(x, hi))
}

/// Returns the error e = x * y - p, where p = RN(x * y), with Dekker's algorithm.
/// See `generic::two_prod_err`.
fn two_prod_err(x: F64X2, y: F64X2, p: F64X2) -> F64X2 {
    let (xh, xl) = split(x);
    let (yh, yl) = split(y);
    let t = f64x2_add(
        f64x2_add(f64x2_sub(f64x2_mul(xh, yh), p), f64x2_mul(xh, yl)),
        f64x2_mul(xl, yh),
    );
    f64x2_add(t, f64x2_mul(xl, yl))
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
    let s = f64x2_add(x, y);
    let e = two_sum_err(x, y, s);
    let even = i64x2_eq(v128_and(s, i64x2_splat(1)), i64x2_splat(0));
    let inexact_even = and(f64x2_ne(e, ZERO), even);
    // s is nonzero if inexact. Moving toward the larger magnitude increments the
    // bit pattern, and toward the smaller one decrements it.
    let toward_larger = v128_not(v128_xor(f64x2_gt(e, ZERO), f64x2_gt(s, ZERO)));
    let odd = select(
        toward_larger,
        i64x2_add(s, i64x2_splat(1)),
        i64x2_sub(s, i64x2_splat(1)),
    );
    select(inexact_even, odd, s)
}
