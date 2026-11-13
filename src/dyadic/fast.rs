// The shared layer of the fast paths in front of the dyadic kernel: Fast2Sum and TwoSum, the
// normalization of a double-double (`normalize`), its quotient (`dd_div`) and its square root
// (`dd_sqrt`), the rounding tests of an approximation in double-double, with the error bound
// 2^-68 or one given as an argument (`round_dir_err`, `round_near_err`), and the scaling of their
// results. `src/dyadic/exp.rs` uses it for e^x, 2^x, 10^x, sinh, cosh and tanh,
// `src/dyadic/log.rs` for ln x, log2 x, log10 x, asinh, acosh and atanh, whose results can be
// negative (`round_dir_signed`, `round_near_signed`), `src/dyadic/trig.rs` for sin, cos and tan,
// with the same tests, `src/dyadic/pow.rs` for x^y and x^n, `src/dyadic/atan.rs` for atan,
// atan2, asin and acos, which put the sign back themselves, and `src/dyadic/root.rs` for cbrt,
// which puts the sign back itself too, and hypot.
//
// A fast path computes a scaled result y = f(x) 2^-e, for an integer e in [-1021, 1022], as an
// unevaluated sum h + l of two `f64`s with h = RN(h + l), 1/2 < h < 2, and a proved bound
// |y - (h + l)| <= 2^-68 (`ERR`). `round_dir` and `round_near` then decide the rounding of y by
// comparisons of l, or of |l| in `round_dir`, with bounds that depend only on h, which round
// nothing, and scale it by 2^e, which is exact as the result is a normal `f64`. Where they cannot
// decide, they return `None`, and the caller calls `ziv` or `ziv_near` as it did before. The
// cases:
//
// - Since h = RN(h + l), |l| is at most half the gap between h and the `f64` next to it on the
//   side of l. If l > 2^-68, then h < h + l - 2^-68 <= y <= h + l + 2^-68 < h + 2 l <= the
//   `f64` after h, so y rounds down to h and up to the `f64` after h. If l < -2^-68, the same
//   holds the other way around. Otherwise the test fails: y may be h itself. So `round_dir`
//   tests |l| > 2^-68, and then takes the step from h that the sign bit of l gives.
// - Rounded to nearest, h is y's rounding if y is strictly within half a gap of h on each side.
//   The gaps above and below h are 2^-52 for 1 < h < 2, and 2^-53 for 1/2 < h < 1, and for
//   h = 1 the gap below is 2^-53 and the one above 2^-52. So the test passes if l is below
//   `NEAR1` = 2^-53 - 2^-68 (or `NEAR0` = 2^-54 - 2^-68) and above the negative of the bound
//   on its side. The inequalities are strict, so a midpoint of two `f64`s never passes.
//
// `round_dir_wide` and `round_near_wide` take an e in [-1085, 1023] instead, for the results of
// e^x, 2^x, 10^x, sinh and cosh that are below 2^-1021, subnormal ones included, or in the last
// finite binade, and return `None` for a larger e. Where e < -1022, or e = -1022 and h <= 1, so
// that h 2^e <= 2^-1022, they round C + y once, on the grid of the `f64`s in [C, 2C] for
// C = 2^(-1022 - e), instead of rounding h and scaling it, which would round a second time
// (`round_dir_sub`, `round_near_sub`). Elsewhere `round_dir` and `round_near` are right, at
// e = 1023 too: there the scaling of the `f64` after h = 2 - 2^-52 is +∞, the rounding up of a
// y 2^1023 above the largest `f64`. `round_dir_err` and `round_near_err` are right at e = 1023
// in the same way.
//
// `round_dir_wide_err` and `round_near_wide_err` are the same tests for a bound `err` = 2^-p, for
// an integer p in [55, 105], in place of 2^-68, which x^y and x^n call at 2^-67 on the results
// of `fast_exp_edge`. Their sub tests `round_dir_sub_err` and `round_near_sub_err` compare
// u = RN(t + l), for s + t = C + h by Fast2Sum, with 2 err C (directed) and (2^-53 - 2 err) C
// (to nearest), where `round_dir_sub` and `round_near_sub` take 2^-67 C and (2^-53 - 2^-67) C:
// 2 err C bounds err and the rounding of u together, as C >= 1 and p <= 105. Where |u| is above
// (2^-53 + 2 err) C, or (2^-53 + 2^-67) C in `round_near_sub`, C + y rounds to nearest to the
// `f64` after or before s. Elsewhere they call `round_dir_err` and `round_near_err`.
//
// `rocq/theories/Model.v` transcribes this file except its tests and the test-only switch and
// counter (`set_fast_path`, `fast_counts`), so it has to be updated along with it.
// `rocq/theories/FastRound.v` proves `round_dir` and `round_near` correct,
// `rocq/theories/FastRoundErr.v` `two_sum`, `normalize`, `round_dir_err` and `round_near_err`,
// `rocq/theories/FastDiv.v` `dd_div`, `rocq/theories/FastDdSqrt.v` `dd_sqrt`,
// `rocq/theories/FastSign.v` `round_dir_signed` and `round_near_signed`,
// `rocq/theories/FastRoundSub.v` `round_dir_sub` and `round_near_sub`, and
// `rocq/theories/FastRoundWide.v` `round_dir_wide` and `round_near_wide`, and `round_dir_err`
// and `round_near_err` at e = 1023 and at e = -1022 with h > 1.
// `rocq/theories/FastRoundWideErr.v` proves `round_dir_sub_err`, `round_near_sub_err`,
// `round_dir_wide_err` and `round_near_wide_err` correct.
//
// References:
//
// - [Dekker] T. J. Dekker, A floating-point technique for extending the available precision,
//   Numer. Math. 18 (1971) (Fast2Sum, and the quotient in double-double).
// - [Knuth] D. E. Knuth, The Art of Computer Programming, vol. 2, 3rd ed., 1998, 4.2.2
//   (TwoSum, which needs no order of the magnitudes).
// - [Boldo-Daumas] S. Boldo and M. Daumas, Representable correcting terms for possibly
//   underflowing floating point operations, ARITH 16 (2003) (the remainder of a division).
// - [Ziv] A. Ziv, Fast evaluation of elementary mathematical functions with correctly rounded
//   last bit, ACM TOMS 17(3), 1991 (a fast approximation with an error bound, and a slower one
//   where its rounding test fails).

use crate::simd::{two_prod_err, HAS_FMA};

// 2^-68: the bound on |y - (h + l)| that the rounding tests assume.
const ERR: f64 = 1.0 / 295_147_905_179_352_825_856.0;

// 2^-53 - 2^-68 and 2^-54 - 2^-68: half the gap between h and the next `f64`, less `ERR`, for a
// gap of 2^-52 and of 2^-53.
const NEAR1: f64 = 32_767.0 / 295_147_905_179_352_825_856.0;
const NEAR0: f64 = 16_383.0 / 295_147_905_179_352_825_856.0;

// 2^-53 and 2^-54: half the gap between h and the next `f64`, for a gap of 2^-52 and of 2^-53.
const GAP1: f64 = f64::EPSILON / 2.0;
const GAP0: f64 = f64::EPSILON / 4.0;

#[cfg(test)]
thread_local! {
    // Whether the fast paths are enabled on this thread, and how many of their rounding tests
    // have passed and failed since `reset_fast_counts`.
    static FAST: std::cell::Cell<(bool, usize, usize)> =
        const { std::cell::Cell::new((true, 0, 0)) };
}

/// Enables or disables the fast paths on this thread. Disabled, `round_dir` and `round_near`
/// return `None`, so that every function computes its result with the kernel.
#[cfg(test)]
pub(crate) fn set_fast_path(enabled: bool) {
    FAST.with(|f| {
        let (_, passed, failed) = f.get();
        f.set((enabled, passed, failed));
    });
}

/// Forgets the rounding tests of the fast paths on this thread, so that `fast_counts` is
/// `(0, 0)` until one is taken again.
#[cfg(test)]
pub(crate) fn reset_fast_counts() {
    FAST.with(|f| {
        let (enabled, _, _) = f.get();
        f.set((enabled, 0, 0));
    });
}

/// The numbers of rounding tests of the fast paths that have passed and failed on this thread
/// since `reset_fast_counts`, as `(passed, failed)`. A disabled test counts as neither.
#[cfg(test)]
pub(crate) fn fast_counts() -> (usize, usize) {
    FAST.with(|f| {
        let (_, passed, failed) = f.get();
        (passed, failed)
    })
}

// Whether the fast paths are enabled on this thread. The fast path of `pow` reads it too, for
// its rules on th, the high part of y ln x, which take no rounding test.
#[cfg(test)]
pub(crate) fn fast_enabled() -> bool {
    FAST.with(|f| f.get().0)
}

// Records that a rounding test passed if `passed`, and that it failed otherwise.
#[cfg(test)]
fn record_fast(passed: bool) {
    FAST.with(|f| {
        let (enabled, p, q) = f.get();
        f.set((enabled, p + passed as usize, q + !passed as usize));
    });
}

/// Returns (s, e) with s = RN(a + b) and e = a + b - s exactly, for |a| >= |b| (or a = 0) and
/// a + b that does not overflow. [Dekker]
pub(crate) fn fast_two_sum(a: f64, b: f64) -> (f64, f64) {
    let s = a + b;
    (s, b + (a - s))
}

/// Returns (s, e) with s = RN(a + b) and e = a + b - s exactly, for any a and b whose sum and
/// intermediate differences do not overflow. [Knuth]
pub(crate) fn two_sum(a: f64, b: f64) -> (f64, f64) {
    let s = a + b;
    let a1 = s - b;
    let b1 = s - a1;
    (s, (a - a1) + (b - b1))
}

// r 2^e, for e in [-1021, 1022], which is exact where the result is a normal `f64`.
fn scale(r: f64, e: i64) -> f64 {
    r * f64::from_bits(((e + 1023) as u64) << 52)
}

/// (h 2^-k, l 2^-k, k) for the k with 2^k <= h < 2^(k + 1), so that h 2^-k is in [1, 2), for a
/// positive normal h below 2, which makes -k in [0, 1022] and both products exact.
pub(crate) fn normalize(h: f64, l: f64) -> (f64, f64, i64) {
    let k = (h.to_bits() >> 52) as i64 - 1023;
    (scale(h, -k), scale(l, -k), k)
}

/// The quotient (nh + nl) / (dh + dl) in double-double, as (qh, ql) with qh = RN(qh + ql) and
/// |qh + ql - q| <= 2^-98 q for the quotient q, for 2^-80 <= nh <= 4, |nl| <= 2^-50 nh,
/// 1/2 <= dh <= 4 and |dl| <= 2^-52 dh. [Dekker]
pub(crate) fn dd_div(nh: f64, nl: f64, dh: f64, dl: f64) -> (f64, f64) {
    let qh = nh / dh;
    // nh - qh dh exactly: p + pe = qh dh exactly, nh - p is exact by Sterbenz's lemma, and the
    // remainder nh - qh dh of a division rounded to nearest is an `f64` [Boldo-Daumas], so
    // (nh - p) - pe is exact too.
    let p = qh * dh;
    let pe = two_prod_err::<HAS_FMA>(qh, dh, p);
    // (nh + nl) - qh (dh + dl), up to roundings below 2^-100 nh.
    let r = (((nh - p) - pe) + nl) - qh * dl;
    fast_two_sum(qh, r / dh)
}

/// The rounding of y 2^e toward +∞ if `up` and toward -∞ otherwise, for h, l and e from a fast
/// path, which bounds |y - (h + l)| by 2^-68, or `None` where l cannot decide it: where
/// |l| <= 2^-68, or l is NaN.
pub(crate) fn round_dir(h: f64, l: f64, e: i64, up: bool) -> Option<f64> {
    #[cfg(test)]
    if !fast_enabled() {
        return None;
    }
    // Where |l| > ERR, h < y < the `f64` after h if l > 0, and the `f64` before h < y < h if
    // l < 0. The sign of l is unpredictable on random arguments, so the result is computed from
    // it rather than branched on: its bits are those of h, plus 1 if `up`, less the sign bit of
    // l, which is 1 for l < 0 as l is not zero. The sum stays within `u64` for 1/2 < h < 2. Only
    // |l| <= ERR, which is rare, and a NaN l take the branch.
    let passed = l.abs() > ERR;
    #[cfg(test)]
    record_fast(passed);
    if passed {
        Some(scale(
            f64::from_bits(h.to_bits() + up as u64 - (l.to_bits() >> 63)),
            e,
        ))
    } else {
        None
    }
}

/// The rounding of y 2^e to nearest, for h, l and e from a fast path, which bounds
/// |y - (h + l)| by 2^-68, or `None` where the comparisons of l cannot decide it.
pub(crate) fn round_near(h: f64, l: f64, e: i64) -> Option<f64> {
    #[cfg(test)]
    if !fast_enabled() {
        return None;
    }
    // Half the gap above h, and below it, less `ERR`.
    let above = if h >= 1.0 { NEAR1 } else { NEAR0 };
    let below = if h > 1.0 { NEAR1 } else { NEAR0 };
    let passed = l < above && l > -below;
    #[cfg(test)]
    record_fast(passed);
    if passed {
        Some(scale(h, e))
    } else {
        None
    }
}

/// `round_dir` for a fast path that bounds |y - (h + l)| by `err` = 2^-p, for an integer p in
/// [55, 105], in place of 2^-68, and that leaves 1/2 < h < 2 to this test: it returns `None`,
/// a failed test, where h is outside that range.
pub(crate) fn round_dir_err(h: f64, l: f64, e: i64, err: f64, up: bool) -> Option<f64> {
    #[cfg(test)]
    if !fast_enabled() {
        return None;
    }
    // The step from h by the sign bit of l, without a branch on it, as in `round_dir`, for the
    // err > 0 of the fast paths.
    let passed = h > 0.5 && h < 2.0 && l.abs() > err;
    #[cfg(test)]
    record_fast(passed);
    if passed {
        Some(scale(
            f64::from_bits(h.to_bits() + up as u64 - (l.to_bits() >> 63)),
            e,
        ))
    } else {
        None
    }
}

/// `round_near` for a fast path that bounds |y - (h + l)| by `err` = 2^-p, for an integer p in
/// [55, 105], in place of 2^-68, and that leaves 1/2 < h < 2 to this test, as `round_dir_err`.
pub(crate) fn round_near_err(h: f64, l: f64, e: i64, err: f64) -> Option<f64> {
    #[cfg(test)]
    if !fast_enabled() {
        return None;
    }
    // Half the gap above h, and below it, less `err`. The subtractions are exact: 2^-53 - 2^-p
    // has at most 52 significant bits for p <= 105.
    let above = if h >= 1.0 { GAP1 - err } else { GAP0 - err };
    let below = if h > 1.0 { GAP1 - err } else { GAP0 - err };
    let passed = h > 0.5 && h < 2.0 && l < above && l > -below;
    #[cfg(test)]
    record_fast(passed);
    if passed {
        Some(scale(h, e))
    } else {
        None
    }
}

// 2^-67, 2^-53 - 2^-67 and 2^-53 + 2^-67: the bounds of `round_dir_sub` and `round_near_sub` on
// u, in units of C. 2^-67 C bounds `ERR` and the rounding of u together, as C >= 1, and 2^-53 C
// is half the gap between the `f64`s in [C, 2C].
const SUB_ERR: f64 = f64::EPSILON / 32768.0;
const SUB_NEAR: f64 = 16_383.0 / 147_573_952_589_676_412_928.0;
const SUB_FAR: f64 = 16_385.0 / 147_573_952_589_676_412_928.0;

// C = 2^(-1022 - e), for an e in [-2045, -1022], from its bits.
fn sub_unit(e: i64) -> f64 {
    f64::from_bits(((1 - e) as u64) << 52)
}

// `round_dir` for an e in [-1085, -1022], where y 2^e is below 2^-1021 and can be subnormal, so
// that scaling a rounded h by 2^e would round a second time. It rounds C + y instead, for
// C = 2^(-1022 - e) >= 1: the `f64`s in [C, 2C] are g = 2^-52 C apart, which is 2^-1074 in units
// of 2^-e, the gap between the `f64`s from 0 to 2^-1021. s + t = C + h exactly by Fast2Sum
// [Dekker], as C >= h where s < 2C, and u = RN(t + l) is within 2^-54 g of t + l, as
// |t + l| <= 3g/4, so C + y is within 2^-67 C (`SUB_ERR`) of s + u. The tests of `round_dir`,
// with u for l and 2^-67 C for `ERR`, then decide the rounding r of C + y, where s < 2C, and the
// rounding of y 2^e is (r - C) 2^e = (r - C) / g 2^-1074, whose bits are those of r less those
// of C: the `f64`s in [C, 2C] have consecutive bits, and so do those from 0 to 2^-1022. s = C
// never needs the `f64` before it: then t = h, and u = RN(h + l) > 0.
fn round_dir_sub(h: f64, l: f64, e: i64, up: bool) -> Option<f64> {
    #[cfg(test)]
    if !fast_enabled() {
        return None;
    }
    let c = sub_unit(e);
    let (s, t) = fast_two_sum(c, h);
    let u = t + l;
    // C 2^-67, exact as C is a power of 2.
    let b = c * SUB_ERR;
    let r = if s >= 2.0 * c {
        // The gap above s is 2g, or C < h.
        #[cfg(test)]
        record_fast(false);
        return None;
    } else if u.abs() > b {
        // s < C + y < the `f64` after s if u > 0, and the `f64` before s < C + y < s if u < 0.
        // As in `round_dir`, the sign of u is unpredictable on random arguments, so the step
        // from s is computed from it rather than branched on: the bits of s, plus 1 if `up`,
        // less the sign bit of u, which is 1 for u < 0 as u is not zero. The sum stays within
        // `u64` for C <= s < 2C.
        f64::from_bits(s.to_bits() + up as u64 - (u.to_bits() >> 63))
    } else {
        #[cfg(test)]
        record_fast(false);
        return None;
    };
    #[cfg(test)]
    record_fast(true);
    Some(f64::from_bits(r.to_bits() - c.to_bits()))
}

// `round_near` for an e as in `round_dir_sub`: C + y rounds to s where |u| < 2^-53 C - 2^-67 C,
// and y 2^e to (s - C) 2^e. Where |u| > 2^-53 C + 2^-67 C, C + y is more than half a gap and
// less than a gap away from s, so it rounds to the `f64` after s where u > 0 and to the one
// before where u < 0, whose bits are those of s plus or minus 1. As in `round_dir_sub`, s = C
// never needs the `f64` before it. The comparisons are strict, so a midpoint never passes. Only
// a C + h that is itself a midpoint of two `f64`s leaves |u| beyond 2^-53 C: t is a multiple of
// the ulp of h, and |l| is at most half of it, so |t + l| > 2^-53 C only where |t| = 2^-53 C,
// where Fast2Sum has rounded C + h to the even one, s.
fn round_near_sub(h: f64, l: f64, e: i64) -> Option<f64> {
    #[cfg(test)]
    if !fast_enabled() {
        return None;
    }
    let c = sub_unit(e);
    let (s, t) = fast_two_sum(c, h);
    let u = t + l;
    let b = c * SUB_NEAR;
    let r = if s >= 2.0 * c {
        // The gap above s is 2g, or C < h.
        #[cfg(test)]
        record_fast(false);
        return None;
    } else if u < b && u > -b {
        s
    } else if u > c * SUB_FAR {
        // s + g/2 < C + y < the `f64` after s.
        f64::from_bits(s.to_bits() + 1)
    } else if u < -(c * SUB_FAR) {
        // The `f64` before s < C + y < s - g/2.
        f64::from_bits(s.to_bits() - 1)
    } else {
        #[cfg(test)]
        record_fast(false);
        return None;
    };
    #[cfg(test)]
    record_fast(true);
    Some(f64::from_bits(r.to_bits() - c.to_bits()))
}

/// `round_dir` for an e in [-1085, 1023], where y 2^e can be subnormal or above the largest
/// `f64`, and `None` for a larger e. Where e < -1022, or e = -1022 and h <= 1, it rounds as
/// `round_dir_sub`; elsewhere `round_dir` is right: at e = -1022 with h > 1 the `f64`s next to h
/// are in [1, 2] and their scaling is exact, and at e = 1023 the scaling of the `f64` after
/// h = 2 - 2^-52 is +∞, the rounding up of a y 2^1023 above the largest `f64`.
pub(crate) fn round_dir_wide(h: f64, l: f64, e: i64, up: bool) -> Option<f64> {
    if e > 1023 {
        None
    } else if e < -1022 || (e == -1022 && h <= 1.0) {
        round_dir_sub(h, l, e, up)
    } else {
        round_dir(h, l, e, up)
    }
}

/// `round_near` for an e in [-1085, 1023], as `round_dir_wide`. At e = 1023, h passes only where
/// y < 2 - 2^-53, so y 2^1023 is below 2^1024 - 2^970 and rounds to h 2^1023.
pub(crate) fn round_near_wide(h: f64, l: f64, e: i64) -> Option<f64> {
    if e > 1023 {
        None
    } else if e < -1022 || (e == -1022 && h <= 1.0) {
        round_near_sub(h, l, e)
    } else {
        round_near(h, l, e)
    }
}

// `round_dir_sub` for a fast path that bounds |y - (h + l)| by `err` = 2^-p, for an integer p in
// [55, 105], in place of 2^-68: C + y is then within 2^-p + 2^-106 C of s + u, which is at most
// 2 err C, as C >= 1 and p <= 105, so b = 2 err C is the bound on u (2^-67 C at err = 2^-68,
// `round_dir_sub`'s bound).
fn round_dir_sub_err(h: f64, l: f64, e: i64, err: f64, up: bool) -> Option<f64> {
    #[cfg(test)]
    if !fast_enabled() {
        return None;
    }
    let c = sub_unit(e);
    let (s, t) = fast_two_sum(c, h);
    let u = t + l;
    // 2 err C, exact as err and C are powers of 2.
    let b = c * (2.0 * err);
    let r = if s >= 2.0 * c {
        // The gap above s is 2g, or C < h.
        #[cfg(test)]
        record_fast(false);
        return None;
    } else if u > b {
        // s < C + y < the `f64` after s.
        if up {
            f64::from_bits(s.to_bits() + 1)
        } else {
            s
        }
    } else if u < -b {
        // The `f64` before s < C + y < s.
        if up {
            s
        } else {
            f64::from_bits(s.to_bits() - 1)
        }
    } else {
        #[cfg(test)]
        record_fast(false);
        return None;
    };
    #[cfg(test)]
    record_fast(true);
    Some(f64::from_bits(r.to_bits() - c.to_bits()))
}

// `round_near_sub` for a bound `err` as in `round_dir_sub_err`: C + y rounds to s where
// |u| < 2^-53 C - 2 err C, and to the `f64` after or before s where |u| > 2^-53 C + 2 err C.
fn round_near_sub_err(h: f64, l: f64, e: i64, err: f64) -> Option<f64> {
    #[cfg(test)]
    if !fast_enabled() {
        return None;
    }
    let c = sub_unit(e);
    let (s, t) = fast_two_sum(c, h);
    let u = t + l;
    // (2^-53 - 2 err) C: the subtraction is exact, as 2^-53 - 2^(1 - p) has at most 52
    // significant bits for p <= 105, and so is the product by the power of 2 C.
    let b = c * (GAP1 - 2.0 * err);
    let r = if s >= 2.0 * c {
        // The gap above s is 2g, or C < h.
        #[cfg(test)]
        record_fast(false);
        return None;
    } else if u < b && u > -b {
        s
    } else if u > c * (GAP1 + 2.0 * err) {
        // s + g/2 < C + y < the `f64` after s. (2^-53 + 2 err) C is exact as the bound above.
        f64::from_bits(s.to_bits() + 1)
    } else if u < -(c * (GAP1 + 2.0 * err)) {
        // The `f64` before s < C + y < s - g/2.
        f64::from_bits(s.to_bits() - 1)
    } else {
        #[cfg(test)]
        record_fast(false);
        return None;
    };
    #[cfg(test)]
    record_fast(true);
    Some(f64::from_bits(r.to_bits() - c.to_bits()))
}

/// `round_dir_wide` for a fast path that bounds |y - (h + l)| by `err` = 2^-p, for an integer p
/// in [55, 105], in place of 2^-68: `round_dir_sub_err` where `round_dir_wide` calls
/// `round_dir_sub`, and `round_dir_err` where it calls `round_dir`.
pub(crate) fn round_dir_wide_err(h: f64, l: f64, e: i64, err: f64, up: bool) -> Option<f64> {
    if e > 1023 {
        None
    } else if e < -1022 || (e == -1022 && h <= 1.0) {
        round_dir_sub_err(h, l, e, err, up)
    } else {
        round_dir_err(h, l, e, err, up)
    }
}

/// `round_near_wide` for a bound `err` as in `round_dir_wide_err`.
pub(crate) fn round_near_wide_err(h: f64, l: f64, e: i64, err: f64) -> Option<f64> {
    if e > 1023 {
        None
    } else if e < -1022 || (e == -1022 && h <= 1.0) {
        round_near_sub_err(h, l, e, err)
    } else {
        round_near_err(h, l, e, err)
    }
}

/// `round_dir` for an h of either sign, with 1/2 < |h| < 2: where h < 0, the rounding of y 2^e
/// is the negative of the rounding of -y 2^e in the other direction, which `round_dir` decides
/// from -h and -l.
pub(crate) fn round_dir_signed(h: f64, l: f64, e: i64, up: bool) -> Option<f64> {
    if h < 0.0 {
        round_dir(-h, -l, e, !up).map(|r| -r)
    } else {
        round_dir(h, l, e, up)
    }
}

/// `round_near` for an h of either sign, with 1/2 < |h| < 2: where h < 0, the rounding of y 2^e
/// to nearest is the negative of that of -y 2^e.
pub(crate) fn round_near_signed(h: f64, l: f64, e: i64) -> Option<f64> {
    if h < 0.0 {
        round_near(-h, -l, e).map(|r| -r)
    } else {
        round_near(h, l, e)
    }
}

/// The square root of ah + al in double-double, as (sh, sl) with sh = RN(sh + sl) and
/// |sh + sl - √(ah + al)| <= 2^-100 √(ah + al), for 2^-900 <= ah <= 2^900 and |al| <= 2^-52 ah:
/// s = RN(√ah) and one correction step. [Dekker]
pub(crate) fn dd_sqrt(ah: f64, al: f64) -> (f64, f64) {
    let s = ah.sqrt();
    // ah - s^2 exactly: p + pe = s^2 exactly, ah - p is exact by Sterbenz's lemma, and the
    // remainder ah - s^2 of a square root rounded to nearest is an `f64`, so (ah - p) - pe is
    // exact too.
    let p = s * s;
    let pe = two_prod_err::<HAS_FMA>(s, s, p);
    let c = (((ah - p) - pe) + al) / (2.0 * s);
    fast_two_sum(s, c)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dyadic::tests::Rng;

    // `round_dir_err` as it was before it took the step from h by the sign bit of l: by the
    // comparisons l > err and l < -err. `round_dir` was the same without the check of h, at
    // err = `ERR`.
    fn by_comparisons(h: f64, l: f64, e: i64, err: f64, up: bool) -> Option<f64> {
        let r = if l > err {
            if up {
                f64::from_bits(h.to_bits() + 1)
            } else {
                h
            }
        } else if l < -err {
            if up {
                h
            } else {
                f64::from_bits(h.to_bits() - 1)
            }
        } else {
            return None;
        };
        Some(scale(r, e))
    }

    // Checks `round_dir` (at err = `ERR`) and `round_dir_err` against `by_comparisons` at
    // (h, l), in both directions and at both ends of the range of e, by the bits of the results.
    fn check(h: f64, l: f64, err: f64) {
        let in_range = h > 0.5 && h < 2.0;
        for up in [false, true] {
            for e in [-1022, 0, 1023] {
                let want = if in_range {
                    by_comparisons(h, l, e, err, up)
                } else {
                    None
                };
                let got = round_dir_err(h, l, e, err, up);
                assert_eq!(
                    got.map(f64::to_bits),
                    want.map(f64::to_bits),
                    "round_dir_err({h:e}, {l:e}, {e}, {err:e}, {up})"
                );
                if in_range && err == ERR {
                    let got = round_dir(h, l, e, up);
                    assert_eq!(
                        got.map(f64::to_bits),
                        want.map(f64::to_bits),
                        "round_dir({h:e}, {l:e}, {e}, {up})"
                    );
                }
            }
        }
    }

    // h in (1/2, 2): next to its ends, at and next to 1, where the gap changes, and 3/4 and 3/2.
    fn h_grid() -> [f64; 7] {
        [
            f64::from_bits(0.5f64.to_bits() + 1),
            0.75,
            f64::from_bits(1f64.to_bits() - 1),
            1.0,
            f64::from_bits(1f64.to_bits() + 1),
            1.5,
            f64::from_bits(2f64.to_bits() - 1),
        ]
    }

    // A random h in (1/2, 2), and a random l of either sign with |l| in [2^-110, 2^-49).
    fn random_hl(rng: &mut Rng) -> (f64, f64) {
        let lo = 0.5f64.to_bits() + 1;
        let hi = 2f64.to_bits() - 1;
        let h = f64::from_bits(lo + rng.below(hi - lo + 1));
        // sign, a biased exponent for -110 to -50, and a random significand.
        let k = 1023 - 110 + rng.below(61);
        let l = f64::from_bits((rng.next() & (1 << 63)) | k << 52 | rng.next() >> 12);
        (h, l)
    }

    // The step from h by the sign bit of l is the step that the comparisons of l with err and
    // -err choose: on both signs of l, on the band |l| <= err where both return `None`, at
    // its ends, on ±0, ±∞ and NaNs of either sign, and on random h in (1/2, 2) and l of either
    // sign with |l| in [2^-110, 2^-49).
    #[test]
    fn round_dir_by_sign_bit() {
        set_fast_path(true);
        let errs = [ERR, 2f64.powi(-55), 2f64.powi(-67), 2f64.powi(-105)];
        let hs = h_grid();
        let neg_nan = f64::from_bits(f64::NAN.to_bits() | 1 << 63);
        for err in errs {
            let ls = [
                0.0,
                err,
                f64::from_bits(err.to_bits() - 1),
                f64::from_bits(err.to_bits() + 1),
                err / 2.0,
                2.0 * err,
                2f64.powi(-60),
                2f64.powi(-54),
                f64::MIN_POSITIVE,
                f64::from_bits(1),
                1.0,
                f64::INFINITY,
            ];
            for l in ls {
                for h in hs {
                    check(h, l, err);
                    check(h, -l, err);
                }
            }
            for h in hs {
                check(h, f64::NAN, err);
                check(h, neg_nan, err);
            }
            // `round_dir_err` checks h itself.
            for h in [0.5, 2.0, 0.25, 4.0, -1.0, 0.0, f64::NAN] {
                check(h, 2.0 * err, err);
                check(h, -2.0 * err, err);
            }
        }
        let mut rng = Rng(117);
        for _ in 0..100_000 {
            let (h, l) = random_hl(&mut rng);
            check(h, l, errs[rng.below(4) as usize]);
        }
    }

    // `round_dir_sub` as it was before it took the step from s by the sign bit of u: by the
    // comparisons u > b and u < -b.
    fn sub_by_comparisons(h: f64, l: f64, e: i64, up: bool) -> Option<f64> {
        let c = sub_unit(e);
        let (s, t) = fast_two_sum(c, h);
        let u = t + l;
        let b = c * SUB_ERR;
        let r = if s >= 2.0 * c {
            return None;
        } else if u > b {
            if up {
                f64::from_bits(s.to_bits() + 1)
            } else {
                s
            }
        } else if u < -b {
            if up {
                s
            } else {
                f64::from_bits(s.to_bits() - 1)
            }
        } else {
            return None;
        };
        Some(f64::from_bits(r.to_bits() - c.to_bits()))
    }

    // Checks `round_dir_sub` against `sub_by_comparisons` at (h, l), in both directions and
    // across the range of e, by the bits of the results. At e < -1074, C > 2^52 and s can be C,
    // from which u = -∞ would step below C, and the subtraction of the bits of C would overflow:
    // the callers' l is finite, and an infinite one is checked at the other e only.
    fn check_sub(h: f64, l: f64) {
        for up in [false, true] {
            for e in [-1085, -1080, -1060, -1023, -1022] {
                if l.is_infinite() && e < -1074 {
                    continue;
                }
                let want = sub_by_comparisons(h, l, e, up);
                let got = round_dir_sub(h, l, e, up);
                assert_eq!(
                    got.map(f64::to_bits),
                    want.map(f64::to_bits),
                    "round_dir_sub({h:e}, {l:e}, {e}, {up})"
                );
            }
        }
    }

    // The step from s by the sign bit of u is the step that the comparisons of u with b and -b
    // choose: on both signs of l, on the band |u| <= b where both return `None` (u = l at
    // h = 3/4 and e = -1022 or -1023, where b is 2^-67 or 2^-66), at its ends, on ±0, ±∞ and
    // NaNs of either sign, and on random h in (1/2, 2) and l of either sign with |l| in
    // [2^-110, 2^-49).
    #[test]
    fn round_dir_sub_by_sign_bit() {
        set_fast_path(true);
        let ls = [
            0.0,
            SUB_ERR,
            f64::from_bits(SUB_ERR.to_bits() - 1),
            f64::from_bits(SUB_ERR.to_bits() + 1),
            SUB_ERR / 2.0,
            2.0 * SUB_ERR,
            f64::from_bits((2.0 * SUB_ERR).to_bits() + 1),
            2f64.powi(-60),
            2f64.powi(-54),
            f64::MIN_POSITIVE,
            f64::from_bits(1),
            f64::INFINITY,
        ];
        let neg_nan = f64::from_bits(f64::NAN.to_bits() | 1 << 63);
        for h in h_grid() {
            for l in ls {
                check_sub(h, l);
                check_sub(h, -l);
            }
            check_sub(h, f64::NAN);
            check_sub(h, neg_nan);
        }
        let mut rng = Rng(1117);
        for _ in 0..100_000 {
            let (h, l) = random_hl(&mut rng);
            check_sub(h, l);
        }
    }
}
