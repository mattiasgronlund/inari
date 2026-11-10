// The shared layer of the fast paths in front of the dyadic kernel: Fast2Sum and TwoSum, the
// normalization of a double-double (`normalize`) and its quotient (`dd_div`), the rounding tests
// of an approximation in double-double, with the error bound 2^-68 or one given as an argument
// (`round_dir_err`, `round_near_err`), and the scaling of their results. `src/dyadic/exp.rs`
// uses it for e^x, 2^x, 10^x, sinh, cosh and tanh.
//
// A fast path computes a scaled result y = f(x) 2^-e, for an integer e in [-1021, 1022], as an
// unevaluated sum h + l of two `f64`s with h = RN(h + l), 1/2 < h < 2, and a proved bound
// |y - (h + l)| <= 2^-68 (`ERR`). `round_dir` and `round_near` then decide the rounding of y by
// comparisons of l with bounds that depend only on h, which round nothing, and scale it by 2^e,
// which is exact as the result is a normal `f64`. Where they cannot decide, they return `None`,
// and the caller calls `ziv` or `ziv_near` as it did before. The cases:
//
// - Since h = RN(h + l), |l| is at most half the gap between h and the `f64` next to it on the
//   side of l. If l > 2^-68, then h < h + l - 2^-68 <= y <= h + l + 2^-68 < h + 2 l <= the
//   `f64` after h, so y rounds down to h and up to the `f64` after h. If l < -2^-68, the same
//   holds the other way around. Otherwise the test fails: y may be h itself.
// - Rounded to nearest, h is y's rounding if y is strictly within half a gap of h on each side.
//   The gaps above and below h are 2^-52 for 1 < h < 2, and 2^-53 for 1/2 < h < 1, and for
//   h = 1 the gap below is 2^-53 and the one above 2^-52. So the test passes if l is below
//   `NEAR1` = 2^-53 - 2^-68 (or `NEAR0` = 2^-54 - 2^-68) and above the negative of the bound
//   on its side. The inequalities are strict, so a midpoint of two `f64`s never passes.
//
// `rocq/theories/Model.v` transcribes this file except its tests and the test-only switch and
// counter (`set_fast_path`, `fast_counts`), so it has to be updated along with it.
// `rocq/theories/FastRound.v` proves `round_dir` and `round_near` correct,
// `rocq/theories/FastRoundErr.v` `two_sum`, `normalize`, `round_dir_err` and `round_near_err`,
// and `rocq/theories/FastDiv.v` `dd_div`.
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

// Whether the fast paths are enabled on this thread.
#[cfg(test)]
fn fast_enabled() -> bool {
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
/// path, which bounds |y - (h + l)| by 2^-68, or `None` where the comparisons of l cannot
/// decide it.
pub(crate) fn round_dir(h: f64, l: f64, e: i64, up: bool) -> Option<f64> {
    #[cfg(test)]
    if !fast_enabled() {
        return None;
    }
    let r = if l > ERR {
        // h < y < the `f64` after h.
        if up {
            f64::from_bits(h.to_bits() + 1)
        } else {
            h
        }
    } else if l < -ERR {
        // The `f64` before h < y < h.
        if up {
            h
        } else {
            f64::from_bits(h.to_bits() - 1)
        }
    } else {
        #[cfg(test)]
        record_fast(false);
        return None;
    };
    #[cfg(test)]
    record_fast(true);
    Some(scale(r, e))
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
    let r = if !(h > 0.5 && h < 2.0) {
        #[cfg(test)]
        record_fast(false);
        return None;
    } else if l > err {
        // h < y < the `f64` after h.
        if up {
            f64::from_bits(h.to_bits() + 1)
        } else {
            h
        }
    } else if l < -err {
        // The `f64` before h < y < h.
        if up {
            h
        } else {
            f64::from_bits(h.to_bits() - 1)
        }
    } else {
        #[cfg(test)]
        record_fast(false);
        return None;
    };
    #[cfg(test)]
    record_fast(true);
    Some(scale(r, e))
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
