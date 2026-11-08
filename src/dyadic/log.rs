// The logarithms ln x, log2 x and log10 x and the inverse hyperbolic functions asinh, acosh and
// atanh with the dyadic kernel, each rounded to an `f64` toward +∞ if `up` and toward -∞
// otherwise, as MPFR rounds them (`src/dyadic.rs` says what `ziv` returns at its cap).
// `src/mpfr_calls/kernel.rs` makes them the `ln_rd`, `ln_ru` and the others that
// `src/elementary.rs` calls, and the tests on 64-bit Linux and macOS compare them with those
// of the MPFR backend, `src/mpfr_calls/mpfr.rs`.
//
// Each function first settles some arguments by rules: NaN, ±∞, the arguments outside its
// domain, the zeros of ln, log2 and log10 and the ±1 of atanh, whose results are infinite, the
// arguments of asinh and atanh whose results are within an ulp of x, and the powers 10^k from
// 1 to 10^22 for log10, whose results are the integers k. Ziv's strategy cannot settle an
// argument whose result is an `f64` unless an enclosure has that `f64` as its bound in the
// direction of the rounding (the header of `src/dyadic/exp.rs` says why). The other arguments
// with such results are 1 for ln and acosh and 2^k for log2, for which the evaluations below
// give exact enclosures. `ziv` computes the rest from an `Eval`.
//
// The evaluations reduce ln x to ln x = e ln 2 + ln m for m = x / 2^e in [1/√2, √2), where
// ln m = 2 atanh s for s = (m - 1) / (m + 1), as (1 + s) / (1 - s) = m, with
// |s| <= 3 - 2√2 < 0.172. The series atanh u = Σ_{k >= 0} u^(2k + 1) / (2k + 1) has positive
// terms, so Horner's scheme starts from an enclosure of the scaled remainder of the terms that
// it leaves out, which `atanh_sum_bounds` of `rocq/theories/AtanhSeries.v` gives
// (`atanh_series`). asinh, acosh and atanh near 0 and 1 are atanh of a small number, which
// avoids the cancellation of a logarithm near 1. Every product is of enclosures of nonnegative
// numbers, and every quotient is by an enclosure of positive numbers, for which `Encl::mul`
// and `Encl::div` take 2 products or quotients of bounds rather than 8.
//
// `rocq/theories/Model.v` transcribes each function of this file except the tests, so it has
// to be updated along with them. `rocq/theories/DyLog.v` and `rocq/theories/DyLogHyp.v` prove
// that each of the six functions, at a finite argument in its domain and where it does not
// panic, returns a value on the side of its result that the rounding is on, and, where a rule
// settles the argument or a rounding test of `ziv` passes, its result rounded as `mpfr_round`
// in `rocq/theories/Mpfr.v` says. They build on `rocq/theories/DyLogCore.v` for
// `atanh_series`, `reduce`, `ln_dy` and `ln_encl`, `rocq/theories/DyLogRules.v` for the
// identities that the evaluations use and the rules of `log_rules` and of the powers of 10,
// and `rocq/theories/DyLogTiny.v` for the rules of asinh and atanh at tiny arguments. That a
// test passes by the cap of `ziv` is not proved, nor that the evaluations do not panic.

use super::{
    consts::{ln10, ln2},
    exp::{away, mul_int, toward_zero, POW10, TINY_HYP},
    ziv, Dyadic, Encl, Eval,
};

#[cfg(test)]
mod tests;

// floor(2^64 / √2): a normalized `Dyadic` whose top limb is at least this is at least 1 / √2
// times the next power of 2 above it, up to 2^-64 of it.
const SQRT_HALF: u64 = 0xb504_f333_f9de_6484;

// 11/64: atanh, and asinh through atanh(t / √(1 + t^2)), take the series for arguments up to
// it, which keeps u^2 below 2^-5 in `atanh_series`. Above it, the logarithms that they take
// instead are of numbers above 1.186, whose logarithms are above 0.17.
const SERIES_MAX: f64 = 0.171875;

// 1 + 2^-6: acosh takes the series up to it, at u = √(x^2 - 1) / x, whose square is then below
// 2^-5.
const ACOSH_SERIES_MAX: f64 = 1.015625;

// The terms of `atanh_series` at `N` limbs, which make 2 z^n < 2^-(64 N + 4) for z <= 2^-5.
// Any number of terms up to 1,024 gives an enclosure, and the proofs bound the exponents of its
// bounds for those.
fn terms<const N: usize>() -> u64 {
    (64 * N as u64 + 10) / 5
}

// atanh u for the u of `u`, which has to be in [0, 1/2], by Horner's scheme on the scaled
// remainders of its series, T_k = (atanh u - Σ_{i < k} u^(2i + 1) / (2i + 1)) / u^(2k + 1),
// with T_k = 1 / (2k + 1) at u = 0. They satisfy T_k = 1 / (2k + 1) + u^2 T_(k + 1), and
// atanh u = u T_0. The remainders are at least 0, as the terms are positive, and at most
// u^(2k + 1) / (1 - u^2), so each T_k is in [0, 4/3] for u <= 1/2, and the scheme starts from
// [0, 2] at k = `terms`.
fn atanh_series<const N: usize>(u: &Encl<N>) -> Encl<N> {
    assert!(
        u.lo >= Dyadic::ZERO && u.hi <= Dyadic::from_f64(0.5),
        "series out of range"
    );
    let z = u.mul(u);
    let one = Encl::point(1.0);
    let mut t = Encl {
        lo: Dyadic::ZERO,
        hi: Dyadic::from_f64(2.0),
    };
    for k in (0..terms::<N>()).rev() {
        t = one.div_u64(2 * k + 1).add(&z.mul(&t));
    }
    u.mul(&t)
}

// (e, a, less) for a positive `d`, with d = m 2^e for m in [1/√2, √2) up to 2^-64 m, an
// enclosure `a` of 2 atanh |s| = |ln m| for s = (m - 1) / (m + 1), and whether m < 1, so that
// ln d = e ln 2 - a if `less` and e ln 2 + a otherwise. The check of e keeps the proofs from
// having to bound it.
pub(super) fn reduce<const N: usize>(d: &Dyadic<N>) -> (i64, Encl<N>, bool) {
    assert!(!d.neg && !d.is_zero(), "logarithm of a nonpositive number");
    // 2^(b - 1) <= d < 2^b, which fits an `i128`, as `round_up` of `src/dyadic.rs` takes it.
    let b = i128::from(d.exp) + 64 * N as i128;
    let e = if d.m[N - 1] >= SQRT_HALF { b } else { b - 1 };
    assert!(e.unsigned_abs() <= 2048, "reduction out of range");
    let e = e as i64;
    let m = d.shl(-e);
    let (m, one) = (Encl { lo: m, hi: m }, Encl::point(1.0));
    let less = m.lo < one.lo;
    // |m - 1|, which is exact, and 1 / m = (1 + s) / (1 - s) for s = (1 - m) / (1 + m) if m < 1.
    let num = if less { one.sub(&m) } else { m.sub(&one) };
    let s = num.div(&m.add(&one));
    (e, atanh_series(&s).shl(1), less)
}

// ln d for a positive `d`: e ln 2 ± a for the (e, a, less) of `reduce`, where ln 2 = h + l as
// `ln2` gives it, so that e h is exact as |e| <= 2048 < 2^12. For e != 0, |e ln 2| >= 0.69
// and |ln m| <= 0.35, so that the sum cancels at most about a bit.
fn ln_dy<const N: usize>(d: &Dyadic<N>) -> Encl<N> {
    let (e, a, less) = reduce(d);
    let (h, l) = ln2::<N>();
    let k = mul_int(&Encl { lo: h, hi: h }, e).add(&mul_int(&l, e));
    k.add(&if less { a.neg() } else { a })
}

// ln y for the y of `a`, which has to be positive: [ln lo, ln lo + (hi - lo) / lo] encloses it,
// as ln y <= ln x + (y - x) / x for 0 < x <= y, from ln t <= t - 1. This takes one series where
// ln lo and ln hi would take two.
fn ln_encl<const N: usize>(a: &Encl<N>) -> Encl<N> {
    let l = ln_dy(&a.lo);
    let w = a.hi.sub(&a.lo, true).div(&a.lo, true);
    Encl {
        lo: l.lo,
        hi: l.hi.add(&w, true),
    }
}

// ln x, for a positive finite x.
struct Ln(f64);

impl Eval for Ln {
    fn eval<const N: usize>(&self) -> Encl<N> {
        ln_dy(&Dyadic::from_f64(self.0))
    }
}

// log2 x = e + ln m / ln 2, for a positive finite x, for the e and m of `reduce`. At x = 2^e,
// m = 1, so that s = 0 and the quotient are the exact enclosure [0, 0], and log2 x = e is exact.
struct Log2(f64);

impl Eval for Log2 {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let (e, a, less) = reduce(&Dyadic::from_f64(self.0));
        let (h, l) = ln2::<N>();
        let r = a.div(&Encl { lo: h, hi: h }.add(&l));
        mul_int(&Encl::point(1.0), e).add(&if less { r.neg() } else { r })
    }
}

// log10 x = ln x / ln 10, for a positive finite x.
struct Log10(f64);

impl Eval for Log10 {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let (h, l) = ln10::<N>();
        ln_dy(&Dyadic::from_f64(self.0)).div(&Encl { lo: h, hi: h }.add(&l))
    }
}

// asinh x, for a finite x with |x| >= 2^-26, from asinh t for t = |x|, as asinh is odd:
// atanh(t / c) for c = √(1 + t^2) if t <= `SERIES_MAX`, as tanh(asinh t) = t / c, and
// ln(t + c) otherwise.
struct Asinh(f64);

impl Eval for Asinh {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let t = Encl::point(self.0.abs());
        let c = Encl::point(1.0).add(&t.mul(&t)).sqrt();
        let r = if self.0.abs() <= SERIES_MAX {
            atanh_series(&t.div(&c))
        } else {
            ln_encl(&t.add(&c))
        };
        if self.0 < 0.0 {
            r.neg()
        } else {
            r
        }
    }
}

// acosh x, for a finite x >= 1: atanh(r / x) for r = √(x^2 - 1) if x <= `ACOSH_SERIES_MAX`,
// as tanh(acosh x) = r / x, and ln(x + r) otherwise. x^2 - 1 = (x - 1)(x + 1), where x - 1 is
// exact for x in [1, 2], so that r keeps its relative precision near x = 1, where it is 0.
struct Acosh(f64);

impl Eval for Acosh {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let x = Encl::point(self.0);
        let one = Encl::point(1.0);
        let r = x.sub(&one).mul(&x.add(&one)).sqrt();
        if self.0 <= ACOSH_SERIES_MAX {
            atanh_series(&r.div(&x))
        } else {
            ln_encl(&x.add(&r))
        }
    }
}

// atanh x, for 2^-26 <= |x| < 1, from atanh t for t = |x|, as atanh is odd: the series if
// t <= `SERIES_MAX`, and otherwise ln q / 2 for q = (1 + t) / (1 - t), where 1 + t and 1 - t
// are exact, as t >= 1/8 has no bit below 2^-55, and q > 1.4.
struct Atanh(f64);

impl Eval for Atanh {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let t = Encl::point(self.0.abs());
        let r = if self.0.abs() <= SERIES_MAX {
            atanh_series(&t)
        } else {
            let one = Encl::point(1.0);
            ln_encl(&one.add(&t).div(&one.sub(&t))).shl(-1)
        };
        if self.0 < 0.0 {
            r.neg()
        } else {
            r
        }
    }
}

// The rules of `ln`, `log2` and `log10`: NaN and +∞ give themselves, ±0 gives -∞ in both
// directions, as MPFR gives it, and the negative numbers give NaN.
fn log_rules(x: f64) -> Option<f64> {
    if x.is_nan() || x == f64::INFINITY {
        Some(x)
    } else if x == 0.0 {
        Some(f64::NEG_INFINITY)
    } else if x < 0.0 {
        Some(f64::NAN)
    } else {
        None
    }
}

/// ln x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn ln(x: f64, up: bool) -> f64 {
    match log_rules(x) {
        Some(r) => r,
        None => ziv(&Ln(x), up, 1),
    }
}

/// log2 x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn log2(x: f64, up: bool) -> f64 {
    match log_rules(x) {
        Some(r) => r,
        None => ziv(&Log2(x), up, 1),
    }
}

/// log10 x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn log10(x: f64, up: bool) -> f64 {
    match log_rules(x) {
        Some(r) => r,
        None => match POW10.iter().position(|&p| p == x) {
            // log10(10^k) = k.
            Some(k) => k as f64,
            None => ziv(&Log10(x), up, 1),
        },
    }
}

/// asinh x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn asinh(x: f64, up: bool) -> f64 {
    if x.is_nan() || x.is_infinite() {
        x
    } else if x.abs() < TINY_HYP {
        // x - x^3 / 6 <= asinh x <= x for x in [0, 1], and asinh is odd.
        toward_zero(x, up)
    } else {
        ziv(&Asinh(x), up, 1)
    }
}

/// acosh x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn acosh(x: f64, up: bool) -> f64 {
    if x.is_nan() || x == f64::INFINITY {
        x
    } else if x < 1.0 {
        f64::NAN
    } else {
        ziv(&Acosh(x), up, 1)
    }
}

/// atanh x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn atanh(x: f64, up: bool) -> f64 {
    let t = x.abs();
    if x.is_nan() {
        x
    } else if t > 1.0 {
        f64::NAN
    } else if t == 1.0 {
        // atanh(±1) = ±∞ in both directions, as MPFR gives it.
        if x > 0.0 {
            f64::INFINITY
        } else {
            f64::NEG_INFINITY
        }
    } else if t < TINY_HYP {
        // x <= atanh x <= x + x^3 / (3 (1 - x^2)) for x in [0, 1), and atanh is odd.
        away(x, up)
    } else {
        ziv(&Atanh(x), up, 1)
    }
}
