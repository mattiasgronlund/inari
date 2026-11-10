// The logarithms ln x, log2 x and log10 x and the inverse hyperbolic functions asinh, acosh and
// atanh with the dyadic kernel, each rounded to an `f64` toward +∞ if `up` and toward -∞
// otherwise, and, as `ln_near` and the others, to nearest, ties to even, as MPFR rounds them
// (`src/dyadic.rs` says what `ziv` and `ziv_near` return at their caps).
// `src/mpfr_calls/kernel.rs` makes the first the `ln_rd`, `ln_ru` and the others that
// `src/elementary.rs` calls, `src/cr.rs` makes both the `ln_rn`, `ln_rd`, `ln_ru` and the
// others of `inari::cr`, and the tests on 64-bit Linux and macOS compare them with those of
// MPFR, `src/mpfr_calls/mpfr.rs`.
//
// Each function first settles some arguments by rules: NaN, ±∞, the arguments outside its
// domain, the zeros of ln, log2 and log10 and the ±1 of atanh, whose results are infinite, the
// arguments of asinh and atanh whose results are within an ulp of x, and the powers 10^k from
// 1 to 10^22 for log10, whose results are the integers k. Ziv's strategy cannot settle an
// argument whose result is an `f64` unless an enclosure has that `f64` as its bound in the
// direction of the rounding (the header of `src/dyadic/exp.rs` says why). The other arguments
// with such results are 1 for ln and acosh and 2^k for log2, for which the evaluations below
// give exact enclosures. `ziv` computes the rest from an `Eval`. The functions rounded to
// nearest have the same rules, with |x| < 2^-27 (`TINY_NEAR`) for asinh and atanh, below which
// the results are less than half an ulp from x, and `ziv_near` computes the rest from the same
// `Eval`s. None of the results is the midpoint of two adjacent `f64`s, which an enclosure
// could settle only if the midpoint were one of its bounds: log2 x and log10 x are rational
// only at the powers of 2 and of 10, where they are integers, and ln x, asinh x, acosh x and
// atanh x are transcendental wherever they are not 0, by the theorem of Lindemann and
// Weierstrass.
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
// or the fast path settles the argument or a rounding test of `ziv` passes, its result rounded
// as `mpfr_round` in `rocq/theories/Mpfr.v` says. They build on `rocq/theories/DyLogCore.v` for
// `atanh_series`, `reduce`, `ln_dy` and `ln_encl`, `rocq/theories/DyLogRules.v` for the
// identities that the evaluations use and the rules of `log_rules` and of the powers of 10,
// and `rocq/theories/DyLogTiny.v` for the rules of asinh and atanh at tiny arguments.
// `rocq/theories/DyLogNear.v` proves that each of the six functions rounded to nearest, at a
// finite argument in its domain, where a rule settles the argument or a rounding test of
// `ziv_near` passes, returns its result rounded to nearest as `near_round` in
// `rocq/theories/NearF64.v` says, from the same enclosures and bounds and the cells of
// `rocq/theories/NearCells.v`. `rocq/theories/DyLogExact.v` proves that each of the six
// functions returns its result, in both directions, at every finite argument in its domain at
// which it is an `f64`, asinh and acosh under the hypothesis `exp_not_quadratic` of
// `rocq/theories/ExpQuadratic.v` that e^r, for a rational r other than 0, is not a root of a
// nonzero polynomial of degree at most 2 with integer coefficients, so that these are the
// arguments above: from `ev_ln_one`, `ev_log2_exact` and
// `ev_acosh_one` in `rocq/theories/DyLogPoint.v` for the exact enclosures, `pow2_rational` and
// `pow10_rational` in `rocq/theories/PowFactor.v` and `exp_irrational` in
// `rocq/theories/ExpIrrational.v`. Other than that, it is not proved that a test passes by the
// cap of `ziv` or of `ziv_near`, nor that the evaluations do not panic, nor that no result is
// a midpoint.
//
// ln x, log2 x and log10 x try a fast path in double-double after their rules, and log10 x
// after the powers of 10, before `ziv` and `ziv_near` (`fast_ln` and `fast_log_by`). It
// computes the result times 2^-k, for an integer k, as h + l within 2^-68 with 1 <= |h| < 2,
// and rounds it with the tests of `src/dyadic/fast.rs`, or returns `None` at x = 1, where the
// result is 0, and where a test fails, and then the function calls `ziv` or `ziv_near` as
// before. At x = 2^n other than 1, where log2 x = n is an `f64`, the fast path computes n
// exactly, with l = 0, so that the directed test fails, as for 2^x in `src/dyadic/exp.rs`, and
// the exact enclosures settle x as above, and the test rounded to nearest passes and returns
// n. asinh, acosh and atanh do not have a fast path. `rocq/theories/FastLogCore.v` bounds the
// error of `ln_core`, from `rocq/theories/FastLogReduce.v` for its reduction,
// `rocq/theories/FastLogTables.v` for its table and constants, and
// `rocq/theories/FastLogPoly.v` for its polynomial, `rocq/theories/FastLogLn.v` and
// `rocq/theories/FastLogBy.v` bound those of `fast_ln` and `fast_log_by`,
// `rocq/theories/FastSign.v` proves the rounding tests for a negative h, and
// `rocq/theories/FastLog.v` proves that the fast path returns ln x, log2 x and log10 x
// rounded, with and without an FMA.

use super::{
    consts::{ln10, ln2},
    exp::{away, mul_int, toward_zero, POW10, TINY_HYP, TINY_NEAR},
    fast::{fast_two_sum, round_dir_signed, round_near_signed},
    ziv, ziv_near, Dyadic, Encl, Eval,
};
use crate::simd::{two_prod_err, HAS_FMA};
use tables::LOG_TABLE;

mod tables;
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

// The constants of the fast path, as the bits of `f64`s, since `f64::from_bits` is not `const`
// before Rust 1.83. `LN2H` is ln 2 with its significand cut to 42 bits, so that e LN2H is exact
// for |e| < 2^11, and `LN2L` = RN(ln 2 - LN2H); `LG2` is log10(2) cut and rounded the same way,
// [LG2H, LG2L], and `ONE` is [1, 0]. `C2` and `C10` are 1/ln 2 and 1/ln 10 in double-double,
// [RN(v), RN(v - RN(v))]. `Q3`, `Q5`, `Q6` and `Q7` are RN(1/3), RN(1/5), RN(-1/6) and RN(1/7),
// the coefficients of the Taylor polynomial of ln(1 + z) that are not powers of 2.
const LN2H: u64 = 0x3fe62e42fefa3800;
const LN2L: u64 = 0x3d2ef35793c76730;
const LG2: [u64; 2] = [0x3fd34413509f7800, 0x3d1fef311f12b358];
const ONE: [u64; 2] = [0x3ff0000000000000, 0];
const C2: [u64; 2] = [0x3ff71547652b82fe, 0x3c7777d0ffda0d24];
const C10: [u64; 2] = [0x3fdbcb7b1526e50e, 0x3c695355baaafad3];
const Q3: u64 = 0x3fd5555555555555;
const Q5: u64 = 0x3fc999999999999a;
const Q6: u64 = 0xbfc5555555555555;
const Q7: u64 = 0x3fc2492492492492;

// 2^52, which scales a subnormal `f64` to a normal one exactly, and the mask of the fraction
// field of an `f64`.
const TWO52: f64 = 4_503_599_627_370_496.0;
const FRAC: u64 = 0x000f_ffff_ffff_ffff;

// (e, m, i) with x = 2^e m exactly, m in [(362 + i) / 512, (363 + i) / 512) and i in [0, 361],
// for a finite x > 0. Then m is in [0.707, 1.415) and e in [-1074, 1024].
// `rocq/theories/FastLogReduce.v` proves it (`ln_split_correct`).
fn ln_split(x: f64) -> (i64, f64, usize) {
    let (mut b, mut e) = (x.to_bits(), 0);
    if b < 1 << 52 {
        // A subnormal x: x 2^52 is exact and normal.
        b = (x * TWO52).to_bits();
        e = -52;
    }
    // x = 2^e M with M in [1, 2), whose top 9 fraction bits are j, so that M is in
    // [1 + j / 512, 1 + (j + 1) / 512). Where M >= 1 + 212/512, m = M / 2, so that
    // floor(512 m) = 256 + j / 2, and otherwise m = M, so that floor(512 m) = 512 + j.
    let j = (b >> 43) & 0x1ff;
    let c = (j >= 212) as u64;
    e += (b >> 52) as i64 - 1023 + c as i64;
    let m = f64::from_bits((b & FRAC) | ((1023 - c) << 52));
    let i = if c == 1 { (j >> 1) - 106 } else { j + 150 };
    (e, m, i as usize)
}

// ln(1 + z) for z = z1 + z2 with |z1| <= 2^-9 and |z2| <= 2^-53 |z1|, as ah + pl: the Taylor
// polynomial z - z^2/2 + z^3/3 - ... - z^8/8 at z1, with z1 - z1^2/2 in double-double, as z1^2 is
// exact as sh + sl (`two_prod_err`) and Fast2Sum is exact as |sh / 2| < |z1| [Dekker], the
// terms of degree 3 to 8 by Horner's scheme in `f64`, and z2 (1 - z1), the term of ln(1 + z) of
// first order in z2. `rocq/theories/FastLogPoly.v` proves the bound (`log1p_poly_correct`).
fn log1p_poly(z1: f64, z2: f64) -> (f64, f64) {
    let sh = z1 * z1;
    let sl = two_prod_err::<HAS_FMA>(z1, z1, sh);
    let (q3, q5, q6, q7) = (
        f64::from_bits(Q3),
        f64::from_bits(Q5),
        f64::from_bits(Q6),
        f64::from_bits(Q7),
    );
    let q = z1 * sh * (q3 + z1 * (-0.25 + z1 * (q5 + z1 * (q6 + z1 * (q7 + z1 * -0.125)))));
    let (ah, al) = fast_two_sum(z1, -0.5 * sh);
    (ah, al + ((q - 0.5 * sl) + z2 * (1.0 - z1)))
}

// ln x = e ln 2 + a_h + a_l up to 3 * 2^-71 |ln m|, for a finite x > 0, as (e, a_h, a_l), with
// m = x / 2^e and a_h = RN(a_h + a_l). The reduction and the size of the table are those of
// CORE-MATH's `log` [CORE-MATH]: ln m = -ln r + ln(1 + z) for z = r m - 1 and the r of
// `LOG_TABLE` for the interval of m, with |z| <= 3/2048, or z = m - 1 with |z| <= 2^-9 for the
// two intervals around 1, where r = 1. Unlike CORE-MATH, r has 53 bits and z is computed exactly
// with `two_prod_err`, and the polynomial is the Taylor polynomial of degree 8 rather than a
// minimax one. `rocq/theories/FastLogCore.v` proves the bound (`ln_core_correct`), from
// `rocq/theories/FastLogReduce.v` for the reduction and z, `rocq/theories/FastLogTables.v` for
// the table and `rocq/theories/FastLogPoly.v` for the polynomial.
//
// [CORE-MATH] P. Zimmermann et al., the CORE-MATH project, `src/binary64/log/log.c` (MIT
// license); no constant or table is copied from it.
fn ln_core(x: f64) -> (i64, f64, f64) {
    let (e, m, i) = ln_split(x);
    let [r, th, tl] = LOG_TABLE[i];
    let (r, th, tl) = (f64::from_bits(r), f64::from_bits(th), f64::from_bits(tl));
    // z = r m - 1 = z1 + z2 exactly: p = RN(r m) is within 2^-8 of 1, so p - 1 is exact
    // (Sterbenz), pe = r m - p exactly (`two_prod_err`), and |pe| <= ulp(p) / 2 <= |p - 1|
    // unless p = 1, so Fast2Sum is exact. [Dekker]
    let p = r * m;
    let pe = two_prod_err::<HAS_FMA>(r, m, p);
    let (z1, z2) = fast_two_sum(p - 1.0, pe);
    let (ah, pl) = log1p_poly(z1, z2);
    // ln m = th + tl + ah + pl, where |th| >= 2^-9 > |ah| unless r = 1 and th = tl = 0.
    let (u, v) = fast_two_sum(th, ah);
    let (a_h, a_l) = fast_two_sum(u, v + (tl + pl));
    (e, a_h, a_l)
}

// (h 2^-k, l 2^-k, k) for the exponent k of h, so that 1 <= |h 2^-k| < 2, or `None` if h = 0.
// The fast paths below pass 2^-56 <= |h| < 2^11, so k is in [-56, 10], h 2^-k is exact and
// l 2^-k is exact unless it is below 2^-1022. `rocq/theories/FastLogNorm.v` proves the bound
// (`normalize_correct`).
fn normalize(h: f64, l: f64) -> Option<(f64, f64, i64)> {
    if h == 0.0 {
        return None;
    }
    let k = ((h.to_bits() >> 52) & 0x7ff) as i64 - 1023;
    let s = f64::from_bits(((1023 - k) as u64) << 52);
    Some((h * s, l * s, k))
}

// ln x as (h, l, k) with |ln x 2^-k - (h + l)| <= 2^-68, h = RN(h + l) and 1 <= |h| < 2, for a
// finite x > 0, or `None` for x = 1, where ln x = 0. e LN2H is exact, and |e LN2H| > 1/2 > |a_h|
// unless e = 0. `rocq/theories/FastLogLn.v` proves it, with 1/2 < |h| < 2, which the rounding
// tests take (`fast_ln_correct`).
fn fast_ln(x: f64) -> Option<(f64, f64, i64)> {
    let (e, a_h, a_l) = ln_core(x);
    let ef = e as f64;
    let (s, t) = fast_two_sum(ef * f64::from_bits(LN2H), a_h);
    let (h, l) = fast_two_sum(s, t + (a_l + ef * f64::from_bits(LN2L)));
    normalize(h, l)
}

// The same for e (dh + dl) + (a_h + a_l) (ch + cl), with c and d given as the bits [ch, cl] and
// [dh, dl]: log2 x for c = 1/ln 2 (`C2`) and d = 1 (`ONE`), and log10 x for c = 1/ln 10 (`C10`)
// and d = log10(2) (`LG2`). a_h ch is exact as ph + `two_prod_err`, e dh is exact, and
// |e dh| > |ph| unless e = 0, as |a_h| < 0.35. `rocq/theories/FastLogBy.v` proves it for log2
// and log10, with 1/2 < |h| < 2 as for ln (`fast_log2_correct`, `fast_log10_correct`).
fn fast_log_by(x: f64, c: [u64; 2], d: [u64; 2]) -> Option<(f64, f64, i64)> {
    let (e, a_h, a_l) = ln_core(x);
    let ef = e as f64;
    let (ch, cl) = (f64::from_bits(c[0]), f64::from_bits(c[1]));
    let (dh, dl) = (f64::from_bits(d[0]), f64::from_bits(d[1]));
    let ph = a_h * ch;
    let pl = two_prod_err::<HAS_FMA>(a_h, ch, ph) + (a_h * cl + a_l * ch);
    let (s, t) = fast_two_sum(ef * dh, ph);
    let (h, l) = fast_two_sum(s, t + (pl + ef * dl));
    normalize(h, l)
}

// ln x, log2 x and log10 x rounded toward +∞ if `up` and toward -∞ otherwise, and to nearest,
// by the fast path, or `None` where its rounding test fails or x = 1.
fn fast_ln_dir(x: f64, up: bool) -> Option<f64> {
    let (h, l, k) = fast_ln(x)?;
    round_dir_signed(h, l, k, up)
}

fn fast_log2_dir(x: f64, up: bool) -> Option<f64> {
    let (h, l, k) = fast_log_by(x, C2, ONE)?;
    round_dir_signed(h, l, k, up)
}

fn fast_log10_dir(x: f64, up: bool) -> Option<f64> {
    let (h, l, k) = fast_log_by(x, C10, LG2)?;
    round_dir_signed(h, l, k, up)
}

fn fast_ln_near(x: f64) -> Option<f64> {
    let (h, l, k) = fast_ln(x)?;
    round_near_signed(h, l, k)
}

fn fast_log2_near(x: f64) -> Option<f64> {
    let (h, l, k) = fast_log_by(x, C2, ONE)?;
    round_near_signed(h, l, k)
}

fn fast_log10_near(x: f64) -> Option<f64> {
    let (h, l, k) = fast_log_by(x, C10, LG2)?;
    round_near_signed(h, l, k)
}

/// ln x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn ln(x: f64, up: bool) -> f64 {
    match log_rules(x) {
        Some(r) => r,
        None => match fast_ln_dir(x, up) {
            Some(r) => r,
            None => ziv(&Ln(x), up, 1),
        },
    }
}

/// ln x rounded to nearest, ties to even.
pub(crate) fn ln_near(x: f64) -> f64 {
    match log_rules(x) {
        Some(r) => r,
        None => match fast_ln_near(x) {
            Some(r) => r,
            None => ziv_near(&Ln(x), 1),
        },
    }
}

/// log2 x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn log2(x: f64, up: bool) -> f64 {
    match log_rules(x) {
        Some(r) => r,
        None => match fast_log2_dir(x, up) {
            Some(r) => r,
            None => ziv(&Log2(x), up, 1),
        },
    }
}

/// log2 x rounded to nearest, ties to even.
pub(crate) fn log2_near(x: f64) -> f64 {
    match log_rules(x) {
        Some(r) => r,
        None => match fast_log2_near(x) {
            Some(r) => r,
            None => ziv_near(&Log2(x), 1),
        },
    }
}

/// log10 x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn log10(x: f64, up: bool) -> f64 {
    match log_rules(x) {
        Some(r) => r,
        None => match POW10.iter().position(|&p| p == x) {
            // log10(10^k) = k.
            Some(k) => k as f64,
            None => match fast_log10_dir(x, up) {
                Some(r) => r,
                None => ziv(&Log10(x), up, 1),
            },
        },
    }
}

/// log10 x rounded to nearest, ties to even.
pub(crate) fn log10_near(x: f64) -> f64 {
    match log_rules(x) {
        Some(r) => r,
        None => match POW10.iter().position(|&p| p == x) {
            // log10(10^k) = k.
            Some(k) => k as f64,
            None => match fast_log10_near(x) {
                Some(r) => r,
                None => ziv_near(&Log10(x), 1),
            },
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

/// asinh x rounded to nearest, ties to even.
pub(crate) fn asinh_near(x: f64) -> f64 {
    if x.is_nan() || x.is_infinite() {
        x
    } else if x.abs() < TINY_NEAR {
        // x - x^3 / 6 <= asinh x <= x for x in [0, 1], and asinh is odd.
        x
    } else {
        ziv_near(&Asinh(x), 1)
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

/// acosh x rounded to nearest, ties to even.
pub(crate) fn acosh_near(x: f64) -> f64 {
    if x.is_nan() || x == f64::INFINITY {
        x
    } else if x < 1.0 {
        f64::NAN
    } else {
        ziv_near(&Acosh(x), 1)
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

/// atanh x rounded to nearest, ties to even.
pub(crate) fn atanh_near(x: f64) -> f64 {
    let t = x.abs();
    if x.is_nan() {
        x
    } else if t > 1.0 {
        f64::NAN
    } else if t == 1.0 {
        if x > 0.0 {
            f64::INFINITY
        } else {
            f64::NEG_INFINITY
        }
    } else if t < TINY_NEAR {
        // x <= atanh x <= x + x^3 / (3 (1 - x^2)) for x in [0, 1), and atanh is odd.
        x
    } else {
        ziv_near(&Atanh(x), 1)
    }
}
