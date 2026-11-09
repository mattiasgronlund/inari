// The inverse trigonometric functions atan, asin, acos and atan2 with the dyadic kernel, each
// rounded to an `f64` toward +∞ if `up` and toward -∞ otherwise, and, as `atan_near` and the
// others, to nearest, ties to even, as MPFR rounds them (`src/dyadic.rs` says what `ziv` and
// `ziv_near` return at their caps). `src/mpfr_calls/kernel.rs` makes the first the `atan_rd`,
// `atan_ru` and the others that `src/elementary.rs` calls, `src/cr.rs` makes both the
// `atan_rn`, `atan_rd`, `atan_ru` and the others of `inari::cr`, and the tests on 64-bit Linux
// and macOS compare them with those of MPFR, `src/mpfr_calls/mpfr.rs`.
//
// Each function first settles some arguments by rules: NaN, ±∞, the arguments outside the
// domains of asin and acos, the arguments of atan and asin of magnitude below 2^-26 and 2^-27,
// whose results are within an ulp of x, those of atan of magnitude at least 2^54, whose results
// round as ±π/2 do, and those of atan2 at which it is a zero, ±π/4, ±π/2, ±3π/4 or ±π, or, for
// x > 0, within an ulp of a quotient y / x that is an `f64` of magnitude below 2^-26, or, to
// nearest, within 2^-3000 of a quotient midway between two `f64`s below 2^-1021, which Ziv's
// strategy would settle only at 32 or 64 limbs, all as MPFR gives them. Ziv's strategy cannot
// settle an argument whose result is an `f64` unless an enclosure has that `f64` as its bound
// in the direction of the rounding (the header of `src/dyadic/exp.rs` says why). The only
// other argument with such a result is 1 for acos, for which the evaluations below give the
// exact enclosure [0, 0]. `ziv` computes the rest from an `Eval`. The functions rounded to
// nearest have the same rules, with 2^-27 (`TINY_NEAR`) for atan and for the quotients of
// atan2, below which the results are less than half an ulp from x and from y / x, and the
// rule of the midway quotients (`midpoint_quotient`). `ziv_near` computes the rest from the
// same `Eval`s.
//
// The evaluations reduce every function to atan w for an enclosure of numbers w >= 0
// (`atan_encl`), which takes atan w = atan u for u = w if w <= `T1`,
// π/4 - atan((1 - w) / (1 + w)) if w < 1, π/4 + atan((w - 1) / (w + 1)) if w <= `T2`, and
// π/2 - atan(1 / w) otherwise, so that |u| <= 0.4144 for an exact w, and then, unless u is at
// most `NO_HALVE`, halves u once, atan u = 2 atan v for v = u / (1 + √(1 + u^2)), so that
// |v| <= 0.199 (`atan_series`). The series atan v = Σ_{k >= 0} (-1)^k v^(2k + 1) / (2k + 1) is
// alternating, so Horner's scheme starts from the enclosure [0, 1 / (2n + 1)] of the scaled
// remainder of the n terms that it leaves out (`series`), where n follows from the exponent of
// v^2 (`terms`). asin and acos take atan(t / √(1 - t^2)) or atan(√(1 - t^2) / t), which
// avoids the cancellation of π/2 - asin t near 1, and atan2 takes atan of |y| / |x| or of
// |x| / |y|, whichever is at most 1. Every quotient is by an enclosure of positive numbers, for
// which `Encl::div` takes 2 quotients of bounds rather than 8.
//
// `rocq/theories/Model.v` transcribes each function of this file except the tests, so it has
// to be updated along with them. `rocq/theories/DyAtan.v` and `rocq/theories/DyAsin.v` prove
// that each of the four functions, at finite arguments in its domain and where it does not
// panic, returns a value on the side of its result that the rounding is on, and, where a rule
// that does not call `pi_times` settles the arguments or a rounding test of `ziv` passes, its
// result rounded as `mpfr_round` in `rocq/theories/Mpfr.v` says, with the rule of atan at
// |x| >= `HUGE_ATAN`, which calls `pi_times`, proved by `atan_huge_post` in `DyAtan.v`. They
// build on `rocq/theories/DyAtanCore.v` for `series`, `atan_series`, `atan_encl` and
// `asin_parts`, `rocq/theories/AtanSeries.v` for the bounds of the series and the halving,
// `rocq/theories/AtanIdent.v` for the identities that the evaluations use,
// `rocq/theories/DyConstPi.v` for π, and `rocq/theories/DyAtanTiny.v` for the rules of atan,
// asin and atan2 at tiny arguments and quotients. `rocq/theories/DyAtanNear.v` proves that
// each of the four functions rounded to nearest, at finite arguments in its domain, where a
// rule settles the arguments or a rounding test of `ziv_near` passes, returns its result
// rounded to nearest as `near_round` in `rocq/theories/NearF64.v` says, from the same
// enclosures and bounds and the cells of `rocq/theories/NearCells.v`. It builds on
// `rocq/theories/DyAtanMidQ.v` for `midpoint_quotient`, which uses
// `rocq/theories/MidQuot.v` for its quotient, `rocq/theories/MidRound.v` for its rounding
// toward zero and `rocq/theories/NearAtanMid.v` for atan at the midway quotients. That a test
// passes by the cap of `ziv` or of `ziv_near` is not proved, nor that the evaluations do not
// panic.

use super::{
    consts::pi,
    exp::{away, toward_zero, TINY_HYP, TINY_NEAR},
    ziv, ziv_near, Dyadic, Encl, Eval,
};

#[cfg(test)]
mod tests;

// 53/128 and 309/128, just below tan(π/8) = √2 - 1 = 0.41421... and 1 + √2 = 2.41421...: the
// bounds of the four cases of `atan_encl`, which keep the argument of the series at most
// (1 - T1) / (1 + T1) = 0.41437 for an exact w.
const T1: f64 = 0.4140625;
const T2: f64 = 2.4140625;

// 3/4: asin and acos take atan(t / √(1 - t^2)) up to it, whose divisor is then at least 0.66,
// and atan(√(1 - t^2) / t) above it.
const ASIN_SPLIT: f64 = 0.75;

// 2^-27: the arguments of smaller magnitude have results within an ulp of x for asin. atan
// takes `TINY_HYP`, 2^-26.
const TINY_ASIN: f64 = 1.0 / 134_217_728.0;

// 2^54: for x >= 2^54, atan x = π/2 - atan(1 / x) is above π/2 - 2^-54, as
// 0 < atan(1 / x) < 1 / x, and so above 1.5707963267948966, the `f64` below π/2, which is
// π/2 - 6.1e-17 (2^-54 is 5.6e-17). atan x and π/2 then lie between the same two adjacent
// `f64`s, and round alike in both directions.
const HUGE_ATAN: f64 = 18_014_398_509_481_984.0;

// 2^-8: `atan_series` takes the series at u itself if the upper bound of u is at most this. For
// u in [0, 2^-8], z = u^2 <= 2^-16 gives at least 15 bits a term, so that `terms` gives at most
// 5 at one limb, and the halving, which costs a square root and a quotient, would save at most
// one of them.
const NO_HALVE: f64 = 1.0 / 256.0;

// The terms of `series` at `N` limbs for the enclosure `z` of v^2: 1 if z is [0, 0], where
// the series is exact, and otherwise 14 N + 2, or ceil((64 N + 4) / e) if that is fewer, for
// z < 2^-e. The upper bound of z is m 2^exp for a mantissa m of 64 N bits, so that it is below
// 2^(exp + 64 N), and e = -(exp + 64 N) if that is positive. ceil((64 N + 4) / e) makes
// z^n < 2^-(64 N + 4), and so does 14 N + 2 for z <= 0.0396, which gives 4.65 bits a term:
// v^2 for v = u / (1 + √(1 + u^2)) and |u| <= 0.4144 is at most that.
fn terms<const N: usize>(z: &Encl<N>) -> u64 {
    let cap = 14 * N as u64 + 2;
    let bits = 64 * N as i64;
    if z.hi.is_zero() {
        1
    } else if z.hi.exp >= -bits {
        cap
    } else {
        // -bits - exp > 0 does not overflow, as -bits < 0.
        let e = (-bits - z.hi.exp) as u64;
        // ceil((64 N + 4) / e); `div_ceil` needs Rust 1.73.
        cap.min((64 * N as u64 + 3 + e) / e)
    }
}

// atan v for every v of `v`, by Horner's scheme on the scaled remainders of the series of
// atan v, T_k = (-1)^k (atan v - Σ_{i < k} (-1)^i v^(2i + 1) / (2i + 1)) / v^(2k + 1), with
// T_k = 1 / (2k + 1) at v = 0. They satisfy T_k = 1 / (2k + 1) - v^2 T_(k + 1), and
// atan v = v T_0. The series is alternating with terms that decrease in magnitude, so each T_k
// is in [0, 1 / (2k + 1)], from which the scheme starts at k = `terms`.
fn series<const N: usize>(v: &Encl<N>) -> Encl<N> {
    let one = Encl::point(1.0);
    let z = v.mul(v);
    let n = terms(&z);
    let mut t = Encl {
        lo: Dyadic::ZERO,
        hi: Dyadic::from_f64(1.0).div_u64(2 * n + 1, true),
    };
    for k in (0..n).rev() {
        t = one.div_u64(2 * k + 1).sub(&z.mul(&t));
    }
    v.mul(&t)
}

// atan u for every u of `u`: the series at u if the upper bound of u is at most `NO_HALVE`, and
// otherwise one halving, atan u = 2 atan v for v = u / (1 + √(1 + u^2)), as
// tan(2 atan v) = 2 v / (1 - v^2) = u for that v, and |v| < 1, and the series at v.
fn atan_series<const N: usize>(u: &Encl<N>) -> Encl<N> {
    if u.hi <= Dyadic::from_f64(NO_HALVE) {
        series(u)
    } else {
        let one = Encl::point(1.0);
        series(&u.div(&one.add(&one.add(&u.mul(u)).sqrt()))).shl(1)
    }
}

// atan w for every w of `w`, whose numbers have to be at least 0, by the case of the header
// that the bounds of `w` choose: atan w = π/4 - atan((1 - w) / (1 + w)) and
// π/4 + atan((w - 1) / (w + 1)) for w > -1, and π/2 - atan(1 / w) for w > 0. Each result
// other than that of the series is above π/8 - 2^-12, and atan u is below π/8 + 2^-12, as
// |u| <= 0.4144 for an exact w, so that the sums cancel at most about a bit.
fn atan_encl<const N: usize>(w: &Encl<N>) -> Encl<N> {
    assert!(!w.lo.neg, "atan of a negative enclosure");
    let one = Encl::point(1.0);
    if w.hi <= Dyadic::from_f64(T1) {
        atan_series(w)
    } else if w.hi < one.hi {
        let u = one.sub(w).div(&one.add(w));
        pi::<N>().shl(-2).sub(&atan_series(&u))
    } else if w.lo <= Dyadic::from_f64(T2) {
        let u = w.sub(&one).div(&w.add(&one));
        pi::<N>().shl(-2).add(&atan_series(&u))
    } else {
        pi::<N>().shl(-1).sub(&atan_series(&one.div(w)))
    }
}

// (a, below) for t in [0, 1], where a encloses atan(t / r) = asin t if `below`, that is, if
// t <= `ASIN_SPLIT`, and atan(r / t) = acos t otherwise, for r = √(1 - t^2). 1 - t^2 is
// (1 - t)(1 + t), where 1 - t is exact for t in [1/2, 1], so that r keeps its relative
// precision near t = 1, where it is 0. At t = 1, r and atan(r / t) are the exact [0, 0].
fn asin_parts<const N: usize>(t: f64) -> (Encl<N>, bool) {
    let x = Encl::point(t);
    let one = Encl::point(1.0);
    let r = one.sub(&x).mul(&one.add(&x)).sqrt();
    if t <= ASIN_SPLIT {
        (atan_encl(&x.div(&r)), true)
    } else {
        (atan_encl(&r.div(&x)), false)
    }
}

// c π, for an `f64` c.
struct PiMul(f64);

impl Eval for PiMul {
    fn eval<const N: usize>(&self) -> Encl<N> {
        Encl::point(self.0).mul(&pi::<N>())
    }
}

// c π rounded toward +∞ if `up` and toward -∞ otherwise, for an `f64` c != 0, which makes c π
// irrational.
fn pi_times(c: f64, up: bool) -> f64 {
    ziv(&PiMul(c), up, 1)
}

// c π rounded to nearest, ties to even, for an `f64` c != 0.
fn pi_times_near(c: f64) -> f64 {
    ziv_near(&PiMul(c), 1)
}

// atan x, for a finite x, from atan t for t = |x|, as atan is odd.
struct Atan(f64);

impl Eval for Atan {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let r = atan_encl(&Encl::point(self.0.abs()));
        if self.0 < 0.0 {
            r.neg()
        } else {
            r
        }
    }
}

// atan2(y, x), for finite y != 0 and x != 0, by the octant of (|x|, |y|): atan2(|y|, x) is
// atan(|y| / |x|) for x > 0 and π - atan(|y| / |x|) for x < 0 if |y| <= |x|, and
// π/2 - atan(|x| / |y|) for x > 0 and π/2 + atan(|x| / |y|) for x < 0 otherwise, and
// atan2(-|y|, x) = -atan2(|y|, x). The argument of atan is then in (0, 1].
struct Atan2(f64, f64);

impl Eval for Atan2 {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let (y, x) = (self.0, self.1);
        let (a, b) = (Encl::point(y.abs()), Encl::point(x.abs()));
        let r = if y.abs() <= x.abs() {
            let t = atan_encl(&a.div(&b));
            if x > 0.0 {
                t
            } else {
                pi::<N>().sub(&t)
            }
        } else {
            let t = atan_encl(&b.div(&a));
            let h = pi::<N>().shl(-1);
            if x > 0.0 {
                h.sub(&t)
            } else {
                h.add(&t)
            }
        };
        if y < 0.0 {
            r.neg()
        } else {
            r
        }
    }
}

// asin x, for x in [-1, 1], from asin t for t = |x|, as asin is odd: asin t = π/2 - acos t
// for t above `ASIN_SPLIT`.
struct Asin(f64);

impl Eval for Asin {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let (a, below) = asin_parts(self.0.abs());
        let r = if below { a } else { pi::<N>().shl(-1).sub(&a) };
        if self.0 < 0.0 {
            r.neg()
        } else {
            r
        }
    }
}

// acos x, for x in [-1, 1], from acos t for t = |x|, as acos(-t) = π - acos t:
// acos t = π/2 - asin t for t up to `ASIN_SPLIT`.
struct Acos(f64);

impl Eval for Acos {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let (a, below) = asin_parts(self.0.abs());
        let r = if below { pi::<N>().shl(-1).sub(&a) } else { a };
        if self.0 < 0.0 {
            pi::<N>().sub(&r)
        } else {
            r
        }
    }
}

// y / x, for finite y != 0 and x != 0, if it is an `f64` of magnitude below `TINY_HYP`. The
// exponents of the `Dyadic`s give |y / x| > 2^(a.exp - b.exp - 1), so that the check of them
// only saves the division for quotients that are at least 2^-26. q = `lo.to_f64(false)` <=
// `lo` <= y / x <= `hi` <= `hi.to_f64(true)`, so that y / x = q if the two `f64`s are equal.
// Two `f64`s whose quotient is a dyadic number have one of at most 53 bits, which 64 bits hold
// exactly, so that the check finds every such quotient that is an `f64`.
fn tiny_quotient(y: f64, x: f64) -> Option<f64> {
    let (a, b) = (Dyadic::<1>::from_f64(y), Dyadic::<1>::from_f64(x));
    if a.exp - b.exp >= -25 {
        return None;
    }
    let (lo, hi) = (a.div(&b, false), a.div(&b, true));
    let q = lo.to_f64(false);
    if q == hi.to_f64(true) && q.abs() < TINY_HYP {
        Some(q)
    } else {
        None
    }
}

// y / x rounded toward zero to an `f64`, for finite y and x != 0, if it is an odd multiple of
// 2^-1075 and the exponents of the `Dyadic`s give |y / x| < 2^-1021. The `f64`s below 2^-1021
// are the multiples of 2^-1074, so that such a quotient q is the midpoint between the two
// `f64`s q - 2^-1075 and q + 2^-1075. For q > 0, atan q is in (q - q^3 / 3, q), and q^3 / 3
// < 2^-3000 is less than half an ulp, 2^-1075, so that atan q is between q and the `f64` f next
// to q toward zero, and rounds to nearest to f, as it does for q < 0, since atan is odd. Ziv's
// strategy settles that only at an enclosure of atan q narrower than q^3 / 3, which is
// q^2 / 3, 2^-2045 to 2^-2150, relative to q, at 32 or 64 limbs.
//
// The mantissas of `a` and `b` are in [2^63, 2^64), so that |y / x| < 2^(a.exp - b.exp + 1),
// which is at most 2^-1021 if a.exp - b.exp <= -1022. The quotients that this check leaves out
// are above 2^(a.exp - b.exp - 1) >= 2^-1022, where no quotient of two `f64`s is a midpoint
// between two `f64`s: for y = Y 2^i and x = X 2^j with odd Y and X, y / x = m 2^c with an odd m
// needs Y = m X, so that m <= |Y| < 2^53, and q = m 2^-1075 < 2^-1022 here, while the midpoints
// above 2^-1022 are the m 2^c with odd m in [2^53, 2^54). Every other quotient q is more than
// |q| 2^-108 from each such midpoint M within a factor 2 of it (|M| >= |q| / 2 gives
// 2^c > |q| 2^-55): q - M = (Y 2^i - m X 2^(j + c)) / (X 2^j), whose numerator is a nonzero
// multiple of 2^min(i, j + c), so that |q - M| >= 2^c / |X| > |q| 2^-108 if j + c <= i, and
// |q - M| >= 2^(i - j) / |X| = |q| / |Y| > |q| 2^-53 otherwise. atan q, within |q|^3 / 3 of
// q, is then more than |q| 2^-109 from every midpoint for |q| < 2^-54, which few limbs settle.
//
// The quotient at 1 limb is exact, `lo` = `hi`, if it is a multiple of 2^-1075 below 2^-1021,
// which has at most 54 bits. `lo` is then m 2^exp for its mantissa m = o 2^t, with o odd and t
// its trailing zeros, so that y / x is an odd multiple of 2^-1075 exactly when exp + t = -1075.
// `lo.to_f64(lo.neg)` rounds it toward -∞ if it is positive and toward +∞ if it is negative.
fn midpoint_quotient(y: f64, x: f64) -> Option<f64> {
    let (a, b) = (Dyadic::<1>::from_f64(y), Dyadic::<1>::from_f64(x));
    if a.exp - b.exp > -1022 {
        return None;
    }
    let (lo, hi) = (a.div(&b, false), a.div(&b, true));
    if lo == hi && lo.exp + i64::from(lo.m[0].trailing_zeros()) == -1075 {
        Some(lo.to_f64(lo.neg))
    } else {
        None
    }
}

/// atan x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn atan(x: f64, up: bool) -> f64 {
    if x.is_nan() {
        x
    } else if x.abs() >= HUGE_ATAN {
        // ±∞ among them, where atan is ±π/2.
        pi_times(0.5_f64.copysign(x), up)
    } else if x.abs() < TINY_HYP {
        // x - x^3 / 3 <= atan x < x for x in (0, 1], and atan is odd.
        toward_zero(x, up)
    } else {
        ziv(&Atan(x), up, 1)
    }
}

/// atan x rounded to nearest, ties to even.
pub(crate) fn atan_near(x: f64) -> f64 {
    if x.is_nan() {
        x
    } else if x.abs() >= HUGE_ATAN {
        // π/2 - 2^-54 < atan x < π/2 for x >= 2^54, and both ends round to the `f64`
        // π/2 - 6.12... 10^-17, whose half-ulp is 2^-53.
        pi_times_near(0.5_f64.copysign(x))
    } else if x.abs() < TINY_NEAR {
        // x - x^3 / 3 <= atan x < x for x in (0, 1], and atan is odd.
        x
    } else {
        ziv_near(&Atan(x), 1)
    }
}

/// asin x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn asin(x: f64, up: bool) -> f64 {
    if x.is_nan() {
        x
    } else if x.abs() > 1.0 {
        f64::NAN
    } else if x.abs() < TINY_ASIN {
        // x < asin x <= x / √(1 - x^2) <= x + x^3 for x in (0, 1/2], and asin is odd.
        away(x, up)
    } else {
        ziv(&Asin(x), up, 1)
    }
}

/// asin x rounded to nearest, ties to even.
pub(crate) fn asin_near(x: f64) -> f64 {
    if x.is_nan() {
        x
    } else if x.abs() > 1.0 {
        f64::NAN
    } else if x.abs() < TINY_ASIN {
        // x < asin x <= x + x^3 for x in (0, 1/2], and asin is odd.
        x
    } else {
        ziv_near(&Asin(x), 1)
    }
}

/// acos x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn acos(x: f64, up: bool) -> f64 {
    if x.is_nan() {
        x
    } else if x.abs() > 1.0 {
        f64::NAN
    } else {
        ziv(&Acos(x), up, 1)
    }
}

/// acos x rounded to nearest, ties to even.
pub(crate) fn acos_near(x: f64) -> f64 {
    if x.is_nan() {
        x
    } else if x.abs() > 1.0 {
        f64::NAN
    } else {
        ziv_near(&Acos(x), 1)
    }
}

/// atan2(y, x) rounded toward +∞ if `up` and toward -∞ otherwise, with the values of MPFR's
/// `mpfr_atan2` at the zeros and infinities.
pub(crate) fn atan2(y: f64, x: f64, up: bool) -> f64 {
    if y.is_nan() || x.is_nan() {
        f64::NAN
    } else if y == 0.0 {
        // y for x >= +0, and π with the sign of y for x <= -0.
        if x.is_sign_positive() {
            y
        } else {
            pi_times(1.0_f64.copysign(y), up)
        }
    } else if y.is_infinite() {
        let c: f64 = if x == f64::INFINITY {
            0.25
        } else if x == f64::NEG_INFINITY {
            0.75
        } else {
            0.5
        };
        pi_times(c.copysign(y), up)
    } else if x == f64::INFINITY {
        0.0_f64.copysign(y)
    } else if x == f64::NEG_INFINITY {
        pi_times(1.0_f64.copysign(y), up)
    } else if x == 0.0 {
        pi_times(0.5_f64.copysign(y), up)
    } else {
        // atan2(y, x) = atan(y / x) for x > 0, which the rule of `atan` settles for a tiny
        // `f64` quotient.
        let q = if x > 0.0 { tiny_quotient(y, x) } else { None };
        match q {
            Some(q) => toward_zero(q, up),
            None => ziv(&Atan2(y, x), up, 1),
        }
    }
}

/// atan2(y, x) rounded to nearest, ties to even, with the values of MPFR's `mpfr_atan2` at the
/// zeros and infinities.
pub(crate) fn atan2_near(y: f64, x: f64) -> f64 {
    if y.is_nan() || x.is_nan() {
        f64::NAN
    } else if y == 0.0 {
        // y for x >= +0, and π with the sign of y for x <= -0.
        if x.is_sign_positive() {
            y
        } else {
            pi_times_near(1.0_f64.copysign(y))
        }
    } else if y.is_infinite() {
        let c: f64 = if x == f64::INFINITY {
            0.25
        } else if x == f64::NEG_INFINITY {
            0.75
        } else {
            0.5
        };
        pi_times_near(c.copysign(y))
    } else if x == f64::INFINITY {
        0.0_f64.copysign(y)
    } else if x == f64::NEG_INFINITY {
        pi_times_near(1.0_f64.copysign(y))
    } else if x == 0.0 {
        pi_times_near(0.5_f64.copysign(y))
    } else if x > 0.0 {
        // atan2(y, x) = atan(y / x) for x > 0, which `midpoint_quotient` settles for a
        // quotient midway between two `f64`s below 2^-1021, and the rule of `atan_near` for an
        // `f64` quotient below 2^-27.
        match midpoint_quotient(y, x) {
            Some(f) => f,
            None => match tiny_quotient(y, x) {
                Some(q) if q.abs() < TINY_NEAR => q,
                _ => ziv_near(&Atan2(y, x), 1),
            },
        }
    } else {
        ziv_near(&Atan2(y, x), 1)
    }
}
