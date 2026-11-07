// The exponentials e^x, 2^x and 10^x and the hyperbolic functions sinh, cosh and tanh with the
// dyadic kernel, each rounded to an `f64` toward +∞ if `up` and toward -∞ otherwise, as
// `exp_rd`, `exp_ru` and the others of `src/mpfr_calls/mpfr.rs` round them with MPFR.
//
// Each function first settles some arguments by rules: NaN and ±∞, the arguments beyond a
// threshold past which the results overflow or are below 2^-1075 in magnitude, those whose
// results are within an ulp of 1 or of x, and the integers from 1 to 22 for 10^x, whose results
// are `f64`s. Ziv's strategy cannot settle an argument whose result is an `f64` unless an enclosure
// has that `f64` as its bound in the direction of the rounding, as the exact enclosures of 2^x
// at an integer x do, since the two bounds of any other enclosure round to different `f64`s.
// The rules also keep the reductions below in range. `ziv` computes the rest from an `Eval`.
//
// The evaluations reduce e^x to e^-y for y in [0, 2]: e^x = 2^k e^-y for y = k ln 2 - x. Then
// e^-y = (e^-s)^(2^j) for s = y / 2^j, and the Taylor series of e^-s alternates, so that
// Horner's scheme can start from [0, 1], which encloses the scaled remainder of the terms that
// it leaves out (`series`). Every product is of enclosures of nonnegative numbers, for which
// `Encl::mul` takes 2 products of bounds rather than 8.
//
// `rocq/theories/Model.v` transcribes each function of this file except the tests, so it has
// to be updated along with them. `rocq/theories/DyExp.v` and `rocq/theories/DyHyp.v` prove
// that each of the six functions, at a finite argument and where it returns rather than
// panics, returns its result rounded as `mpfr_round` in `rocq/theories/Mpfr.v` says. They
// build on `rocq/theories/DyConst.v` for the constants, `rocq/theories/DyExpCore.v` for
// `series`, `exp_neg` and `expm1_neg`, and `rocq/theories/DyExpRules.v`,
// `rocq/theories/DyHypRules.v`, `rocq/theories/DySinhTiny.v` and
// `rocq/theories/DyTanhTiny.v` for the rules. That `ziv` returns is not proved.

use super::{
    consts::{ln10, ln2},
    ziv, Dyadic, Encl, Eval,
};
use std::f64::consts::{LOG2_10, LOG2_E};

#[cfg(test)]
mod tests;

// 2^-26, 2^-54 and 2^-56: the arguments of smaller magnitude have results within an ulp of x
// for sinh and tanh, and for asinh and atanh in `src/dyadic/log.rs`, and of 1 for cosh
// (`TINY_HYP`), e^x and 2^x (`TINY_EXP`), and 10^x (`TINY_EXP10`).
pub(super) const TINY_HYP: f64 = 1.0 / 67_108_864.0;
const TINY_EXP: f64 = f64::EPSILON / 4.0;
const TINY_EXP10: f64 = f64::EPSILON / 16.0;

// 10^n for n from 0 to 22, which are the `f64`s that these literals give, as 10^n = 2^n 5^n
// and 5^22 < 2^53.
pub(super) const POW10: [f64; 23] = [
    1e0, 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9, 1e10, 1e11, 1e12, 1e13, 1e14, 1e15, 1e16,
    1e17, 1e18, 1e19, 1e20, 1e21, 1e22,
];

// The halvings j and the terms K of `exp_neg` and `expm1_neg` at `N` limbs, which make
// (y / 2^j)^K / K! < 2^-(64 N + 8) for y <= ln 2. Any j from 1 to 16 and any K from 1 to 256
// give an enclosure, and the proofs bound the exponents of its bounds for those: these make it
// narrow at little cost, as each halving costs about a bit of the precision of the result, and
// each term a product and a quotient.
fn params<const N: usize>() -> (i64, u64) {
    match N {
        1 => (4, 11),
        2 => (8, 13),
        4 => (12, 18),
        8 => (16, 27),
        16 => (16, 50),
        32 => (16, 95),
        _ => (16, 182),
    }
}

// 1 - e^-s for the s of `s`, which has to be in [0, 1], by Horner's scheme on the scaled
// remainders of the Taylor series of e^-s, T_i = (e^-s - Σ_{l < i} (-s)^l / l!) i! / (-s)^i,
// with T_i = 1 at s = 0. They satisfy T_(i - 1) = 1 - s T_i / i, and 1 - e^-s = s T_1. For
// s in [0, 1], the terms of the series alternate and decrease in magnitude, so that each T_i is
// in [0, 1], from which the scheme starts at i = `k`.
fn series<const N: usize>(s: &Encl<N>, k: u64) -> Encl<N> {
    let one = Encl::point(1.0);
    let mut t = Encl {
        lo: Dyadic::ZERO,
        hi: Dyadic::from_f64(1.0),
    };
    for i in (2..=k).rev() {
        t = one.sub(&s.mul(&t).div_u64(i));
    }
    s.mul(&t)
}

// e^-y for the y of `y`, which has to be in [0, 2]: (e^-s)^(2^j) for s = y / 2^j, which is in
// [0, 1].
fn exp_neg<const N: usize>(y: &Encl<N>) -> Encl<N> {
    let (j, k) = params::<N>();
    let mut e = Encl::point(1.0).sub(&series(&y.shl(-j), k));
    for _ in 0..j {
        e = e.mul(&e);
    }
    e
}

// 1 - e^-y for the y of `y`, which has to be in [0, 2], without the cancellation of
// 1 - `exp_neg(y)` for a small y: u = 1 - e^-s for s = y / 2^j, and then j times
// 1 - e^-2a = u (2 - u) for u = 1 - e^-a.
fn expm1_neg<const N: usize>(y: &Encl<N>) -> Encl<N> {
    let (j, k) = params::<N>();
    let two = Encl::point(2.0);
    let mut u = series(&y.shl(-j), k);
    for _ in 0..j {
        u = u.mul(&two.sub(&u));
    }
    u
}

// The integer `c`, a ceiling that a reduction below takes. The rules before the loop keep it
// below about 1,100 in magnitude, and this check keeps the proofs from having to show it.
fn to_k(c: f64) -> i64 {
    let k = c as i64;
    assert!(k.unsigned_abs() <= 2048, "reduction out of range");
    k
}

// `a` times the integer `k`.
pub(super) fn mul_int<const N: usize>(a: &Encl<N>, k: i64) -> Encl<N> {
    let p = a.mul_u64(k.unsigned_abs());
    if k < 0 {
        p.neg()
    } else {
        p
    }
}

// `a` times the `f64` `x`, as a product of enclosures of nonnegative numbers if `a` is one.
fn mul_f64<const N: usize>(a: &Encl<N>, x: f64) -> Encl<N> {
    let p = Encl::point(x.abs()).mul(a);
    if x < 0.0 {
        p.neg()
    } else {
        p
    }
}

// 2^k e^-y for the enclosure `y` of y = k ln 2 - x, which gives e^x, where ln 2 = h + l as
// `ln2` gives it. If `y` holds negative numbers, the reduction takes k + 1 and y + ln 2 instead.
// The reductions then put y in [0, 2 ln 2], up to their rounding, and the check that `y` is in
// [0, 2] keeps the proofs from having to show it.
fn scaled<const N: usize>(mut y: Encl<N>, mut k: i64, h: &Dyadic<N>, l: &Encl<N>) -> Encl<N> {
    if y.lo < Dyadic::ZERO {
        k += 1;
        y = y.add(&Encl { lo: *h, hi: *h }).add(l);
    }
    assert!(
        y.lo >= Dyadic::ZERO && y.hi <= Dyadic::from_f64(2.0),
        "reduction out of range"
    );
    exp_neg(&y).shl(k)
}

// e^x for |x| below about 1,400, for k = ceil(x log2(e)): y = k ln 2 - x = (k h - x) + k l,
// where k h and x are exact, so that their difference, in which most of their bits cancel, is
// rounded only once.
fn exp_encl<const N: usize>(x: f64) -> Encl<N> {
    let k = to_k((x * LOG2_E).ceil());
    let (h, l) = ln2::<N>();
    let y = mul_int(&Encl { lo: h, hi: h }, k)
        .sub(&Encl::point(x))
        .add(&mul_int(&l, k));
    scaled(y, k, &h, &l)
}

// e^x, for |x| < 746.
struct Exp(f64);

impl Eval for Exp {
    fn eval<const N: usize>(&self) -> Encl<N> {
        exp_encl(self.0)
    }
}

// 2^x, for |x| <= 1,075: 2^m e^-y for m = ceil(x) and y = (m - x) ln 2, which is 0 for an
// integer x, so that 2^x is then exact.
struct Exp2(f64);

impl Eval for Exp2 {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let x = self.0;
        let c = x.ceil();
        let m = to_k(c);
        let (h, l) = ln2::<N>();
        let ln2 = Encl { lo: h, hi: h }.add(&l);
        let y = Encl::point(c).sub(&Encl::point(x)).mul(&ln2);
        scaled(y, m, &h, &l)
    }
}

// 10^x = e^(x ln 10), for |x| < 324, for k = ceil(x log2(10)):
// y = k ln 2 - x ln 10 = (k h2 - x h10) + (k l2 - x l10), where k h2 and x h10 are exact, so
// that their difference, in which most of their bits cancel, is rounded only once.
struct Exp10(f64);

impl Eval for Exp10 {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let x = self.0;
        let k = to_k((x * LOG2_10).ceil());
        let (h2, l2) = ln2::<N>();
        let (h10, l10) = ln10::<N>();
        let y = mul_int(&Encl { lo: h2, hi: h2 }, k)
            .sub(&mul_f64(&Encl { lo: h10, hi: h10 }, x))
            .add(&mul_int(&l2, k).sub(&mul_f64(&l10, x)));
        scaled(y, k, &h2, &l2)
    }
}

// cosh t = (e^t + 1 / e^t) / 2, for t = |x| in [2^-26, 711).
struct Cosh(f64);

impl Eval for Cosh {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let e = exp_encl::<N>(self.0);
        e.add(&Encl::point(1.0).div(&e)).shl(-1)
    }
}

// sinh x, for |x| in [2^-26, 711), from sinh t for t = |x|, as sinh is odd: (e^t - 1 / e^t) / 2
// for t > 1, and otherwise u (2 - u) / (2 (1 - u)) for u = 1 - e^-t, without the cancellation
// of e^t - 1 / e^t.
struct Sinh(f64);

impl Eval for Sinh {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let t = self.0.abs();
        let one = Encl::point(1.0);
        let s = if t > 1.0 {
            let e = exp_encl::<N>(t);
            e.sub(&one.div(&e)).shl(-1)
        } else {
            let u = expm1_neg(&Encl::point(t));
            u.mul(&Encl::point(2.0).sub(&u)).div(&one.sub(&u).shl(1))
        };
        if self.0 < 0.0 {
            s.neg()
        } else {
            s
        }
    }
}

// tanh x, for |x| in [2^-26, 19), from tanh t for t = |x|, as tanh is odd:
// (1 - e^-2t) / (1 + e^-2t) = u / (2 - u) for u = 1 - e^-2t, which `expm1_neg` gives without
// cancellation for t <= 1.
struct Tanh(f64);

impl Eval for Tanh {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let t = self.0.abs();
        let u = if t > 1.0 {
            Encl::point(1.0).sub(&exp_encl(-2.0 * t))
        } else {
            expm1_neg(&Encl::point(2.0 * t))
        };
        let r = u.div(&Encl::point(2.0).sub(&u));
        if self.0 < 0.0 {
            r.neg()
        } else {
            r
        }
    }
}

// The rounding of a number above MAX.
fn overflow(up: bool) -> f64 {
    if up {
        f64::INFINITY
    } else {
        f64::MAX
    }
}

// The rounding of a number in (0, 2^-1074).
fn underflow(up: bool) -> f64 {
    if up {
        f64::from_bits(1)
    } else {
        0.0
    }
}

// The rounding of a number that is 1 if x = 0, in (1, 1 + 2^-52) if x > 0, and in
// (1 - 2^-53, 1) if x < 0.
pub(super) fn near_one(x: f64, up: bool) -> f64 {
    if x == 0.0 {
        1.0
    } else if x > 0.0 {
        if up {
            1.0 + f64::EPSILON
        } else {
            1.0
        }
    } else if up {
        1.0
    } else {
        1.0 - f64::EPSILON / 2.0
    }
}

// The rounding of a number that is x if x = 0, and otherwise strictly between x and the next
// `f64` away from 0.
pub(super) fn away(x: f64, up: bool) -> f64 {
    if x == 0.0 || (x > 0.0) != up {
        x
    } else {
        f64::from_bits(x.to_bits() + 1)
    }
}

// The rounding of a number that is x if x = 0, and otherwise strictly between x and the next
// `f64` toward 0.
pub(super) fn toward_zero(x: f64, up: bool) -> f64 {
    if x == 0.0 || (x > 0.0) == up {
        x
    } else {
        f64::from_bits(x.to_bits() - 1)
    }
}

/// e^x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn exp(x: f64, up: bool) -> f64 {
    if x.is_nan() || x == f64::INFINITY {
        x
    } else if x == f64::NEG_INFINITY {
        0.0
    } else if x >= 710.0 {
        // e^x > 2^1024, as 710 > 1024 ln 2 = 709.78...
        overflow(up)
    } else if x <= -746.0 {
        // e^x < 2^-1075, as -746 < -1075 ln 2 = -745.13...
        underflow(up)
    } else if x.abs() < TINY_EXP {
        // 1 + x <= e^x <= 1 / (1 - x) for x < 1.
        near_one(x, up)
    } else {
        ziv(&Exp(x), up, 1)
    }
}

/// 2^x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn exp2(x: f64, up: bool) -> f64 {
    if x.is_nan() || x == f64::INFINITY {
        x
    } else if x == f64::NEG_INFINITY {
        0.0
    } else if x >= 1024.0 {
        overflow(up)
    } else if x < -1075.0 {
        underflow(up)
    } else if x.abs() < TINY_EXP {
        // 2^x = e^(x ln 2), and |x ln 2| < |x|.
        near_one(x, up)
    } else {
        ziv(&Exp2(x), up, 1)
    }
}

/// 10^x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn exp10(x: f64, up: bool) -> f64 {
    if x.is_nan() || x == f64::INFINITY {
        x
    } else if x == f64::NEG_INFINITY {
        0.0
    } else if x >= 309.0 {
        // 10^x > 2^1024, as 309 > 1024 log10(2) = 308.25...
        overflow(up)
    } else if x <= -324.0 {
        // 10^x < 2^-1075, as -324 < -1075 log10(2) = -323.6...
        underflow(up)
    } else if x.abs() < TINY_EXP10 {
        // 10^x = e^(x ln 10), and |x ln 10| < 4 |x| < 2^-54.
        near_one(x, up)
    } else if (1.0..=22.0).contains(&x) && x == x.floor() {
        POW10[x as usize]
    } else {
        ziv(&Exp10(x), up, 1)
    }
}

/// sinh x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn sinh(x: f64, up: bool) -> f64 {
    if x.is_nan() || x.is_infinite() {
        x
    } else if x >= 711.0 {
        // sinh x > 2^1024, as 711 > 1025 ln 2 = 710.47...
        overflow(up)
    } else if x <= -711.0 {
        -overflow(!up)
    } else if x.abs() < TINY_HYP {
        // x <= sinh x <= x + x^3 / 3 for x in [0, 1], and sinh is odd.
        away(x, up)
    } else {
        ziv(&Sinh(x), up, 1)
    }
}

/// cosh x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn cosh(x: f64, up: bool) -> f64 {
    let t = x.abs();
    if t.is_nan() || t == f64::INFINITY {
        t
    } else if t >= 711.0 {
        // cosh t > sinh t > 2^1024.
        overflow(up)
    } else if t < TINY_HYP {
        // 1 <= cosh t <= 1 + t^2 for t in [0, 1].
        near_one(t, up)
    } else {
        ziv(&Cosh(t), up, 1)
    }
}

/// tanh x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn tanh(x: f64, up: bool) -> f64 {
    if x.is_nan() {
        x
    } else if x == f64::INFINITY {
        1.0
    } else if x == f64::NEG_INFINITY {
        -1.0
    } else if x >= 19.0 {
        // 1 - 2^-53 < tanh x < 1, as 1 - tanh x = 2 / (e^2x + 1) and 38 > 54 ln 2 = 37.43...
        if up {
            1.0
        } else {
            1.0 - f64::EPSILON / 2.0
        }
    } else if x <= -19.0 {
        if up {
            -(1.0 - f64::EPSILON / 2.0)
        } else {
            -1.0
        }
    } else if x.abs() < TINY_HYP {
        // x - x^3 / 3 <= tanh x <= x for x in [0, 1], and tanh is odd.
        toward_zero(x, up)
    } else {
        ziv(&Tanh(x), up, 1)
    }
}
