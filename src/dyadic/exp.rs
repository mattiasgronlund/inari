// The exponentials e^x, 2^x and 10^x and the hyperbolic functions sinh, cosh and tanh with the
// dyadic kernel, each rounded to an `f64` toward +∞ if `up` and toward -∞ otherwise, and, as
// `exp_near` and the others, to nearest, ties to even, as MPFR rounds them (`src/dyadic.rs`
// says what `ziv` and `ziv_near` return at their caps). `src/mpfr_calls/kernel.rs` makes the
// first the `exp_rd`, `exp_ru` and the others that `src/elementary.rs` calls, `src/cr.rs`
// makes both the `exp_rn`, `exp_rd`, `exp_ru` and the others of `inari::cr`, and the tests on
// 64-bit Linux and macOS compare them with those of MPFR, `src/mpfr_calls/mpfr.rs`.
//
// Each function first settles some arguments by rules: NaN and ±∞, the arguments beyond a
// threshold past which the results overflow or are below 2^-1075 in magnitude, those whose
// results are within an ulp of 1 or of x, and the integers from 1 to 22 for 10^x, whose results
// are `f64`s. Ziv's strategy cannot settle an argument whose result is an `f64` unless an enclosure
// has that `f64` as its bound in the direction of the rounding, as the exact enclosures of 2^x
// at an integer x do, since the two bounds of any other enclosure round to different `f64`s.
// The only finite arguments whose results are `f64`s are 0 and, for 2^x and 10^x, the integers
// whose powers are `f64`s, as e^r and tanh r are irrational for every rational r other than 0,
// sinh r and cosh r too if e^r is not a quadratic irrational, which follows from the theorem of
// Hermite and Lindemann, and 2^r and 10^r are rational only for an integer r. The rules settle
// them all but the integers other than 0 of 2^x, which the exact enclosures settle. The rules
// also keep the reductions below in range. `ziv` computes the rest from an `Eval`.
//
// The functions rounded to nearest have rules of the same kinds, with thresholds of their own:
// |x| >= 20 for tanh, as tanh 19 is more than half an ulp below 1, and |x| < 2^-27
// (`TINY_NEAR`) for sinh, cosh and tanh, as below 2^-26 tanh x can be more than half an ulp
// from x, and the bounds that prove the rules of sinh and cosh, x + x^3 / 3 and 1 + t^2, do
// not keep sinh x and cosh x within half an ulp of x and 1 up to 2^-26. Rounded to nearest,
// Ziv's strategy cannot settle an argument whose result is the midpoint of two adjacent
// `f64`s unless the midpoint is a bound of an enclosure, as in an exact one, since the two
// bounds of an enclosure that holds it strictly inside round to different `f64`s.
// 10^23 = 5^23 2^23, with 5^23 odd and in [2^53, 2^54), has a rule, and 2^-1075, 2^x at
// x = -1075, an exact enclosure. No other result is a midpoint: 2^x at any other integer x
// is an `f64`, below 2^-1075 or at least 2^1024; 10^x at an integer x is an `f64` for
// 0 <= x <= 22, has the odd part 5^x > 2^54 for x > 23 and is not dyadic for x < 0; 2^x and
// 10^x at a non-integer x are irrational; and e^x, sinh x, cosh x and tanh x at a nonzero
// `f64` x are transcendental, by the theorem of Lindemann and Weierstrass. Of this, the proofs
// show only that 2^r and 10^r are irrational for every rational r that is not an integer and
// e^r for every rational r other than 0 (see below), and not that no result is a midpoint.
// `ziv_near` computes the rest from the same `Eval`s.
//
// The evaluations reduce e^x to e^-y for y in [0, 2]: e^x = 2^k e^-y for y = k ln 2 - x. Then
// e^-y = (e^-s)^(2^j) for s = y / 2^j, and the Taylor series of e^-s alternates, so that
// Horner's scheme can start from [0, 1], which encloses the scaled remainder of the terms that
// it leaves out (`series`). Every product is of enclosures of nonnegative numbers, for which
// `Encl::mul` takes 2 products of bounds rather than 8.
//
// `rocq/theories/Model.v` transcribes each function of this file except the tests, so it has
// to be updated along with them. `rocq/theories/DyExp.v` and `rocq/theories/DyHyp.v` prove
// that each of the six functions, at a finite argument and where it does not panic, returns a
// value on the side of its result that the rounding is on, and, where a rule settles the
// argument, the fast path below returns or a rounding test of `ziv` passes, its result rounded
// as `mpfr_round` in `rocq/theories/Mpfr.v` says. They build on `rocq/theories/DyConst.v` for
// the constants, `rocq/theories/DyExpCore.v` for `series`, `exp_neg` and `expm1_neg`, and
// `rocq/theories/DyExpRules.v`, `rocq/theories/DyHypRules.v`, `rocq/theories/DySinhTiny.v`
// and `rocq/theories/DyTanhTiny.v` for the rules. `rocq/theories/DyExpNear.v` proves that
// each of the six functions rounded to nearest, at a finite argument, where a rule settles the
// argument, the fast path returns or a rounding test of `ziv_near` passes, returns its result
// rounded to nearest as `near_round` in `rocq/theories/NearF64.v` says, from the same
// enclosures and bounds and the cells of `rocq/theories/NearCells.v`.
// `rocq/theories/DyExpExact.v` proves that each of the six functions returns its result, in
// both directions, at every finite argument at which it is an `f64`, sinh and cosh under the
// hypothesis `exp_not_quadratic` of
// `rocq/theories/ExpQuadratic.v` that e^r, for a rational r other than 0, is not a root of a
// nonzero polynomial of degree at most 2 with integer coefficients, from `ev_exp2_exact` in
// `rocq/theories/DyExpPoint.v` for the exact enclosures of 2^x, `pow2_rational` and
// `pow10_rational` in `rocq/theories/PowFactor.v` and `exp_irrational` in
// `rocq/theories/ExpIrrational.v`. Other than that, it is not proved that a test passes by the
// cap of `ziv` or of `ziv_near`, nor that the evaluations do not panic.
//
// e^x, 2^x and 10^x try a fast path in double-double after their rules and before `ziv` and
// `ziv_near` (`fast_exp`), whose rounding tests are in `src/dyadic/fast.rs`. Where a test
// fails, the function calls `ziv` or `ziv_near` as before. At an integer x in its range, where
// 2^x is an `f64`, the directed test fails, as it passes only where the result lies strictly
// between two adjacent `f64`s, so that the exact enclosures settle x as above, and the test
// rounded to nearest passes and returns 2^x. `rocq/theories/FastExpCore.v` bounds the
// error of `fast_exp`, from `rocq/theories/FastExpReduce.v` for its reduction,
// `rocq/theories/FastExpTables.v` for its tables and constants, and
// `rocq/theories/FastExpPoly.v`, `rocq/theories/FastExpTbl.v` and
// `rocq/theories/FastExpProd.v` for its steps, `rocq/theories/FastRound.v` proves the rounding
// tests, and `rocq/theories/FastExp.v` proves that the fast path returns e^x, 2^x and 10^x
// rounded, with and without an FMA. Beyond the range [-707, 709] of `fast_exp`, where the
// results are below about 2^-1020 or above about 2^1022.87, `fast_exp_edge` shifts z by
// 64 ln 2 or -4 ln 2 into that range, and the rounding tests `round_dir_wide` and
// `round_near_wide` round its result once, on the grid of the subnormals where it is below
// 2^-1021, and return `None` where its exponent is above 1023. Besides the arguments at which
// a test fails, `ziv` and `ziv_near` then get only those that the rules leave whose results
// are 2^1024 or more, or less than 2^-13 below it, relative: e^x for x in about
// (709.78263, 710), 2^x in about (1023.99988, 1024) and 10^x in about (308.25468, 309), where
// the exponent of `fast_exp_edge` is 1024 or more. `rocq/theories/FastExpEdge.v`
// bounds the error of `fast_exp_edge`, `rocq/theories/FastExpByEdge.v` that of its argument
// for 2^x and 10^x, and `rocq/theories/FastRoundSub.v` and `rocq/theories/FastRoundWide.v`
// prove its rounding tests.
//
// sinh, cosh and tanh try fast paths in the same place (`fast_sinh_dir` and the others). They
// call `fast_sinh_pos`, `fast_cosh_pos` and `fast_tanh_pos`, which compute the scaled result of
// |x| from `fast_exp`, from a quotient in double-double (`dd_div`) or, for small |x|, from
// Taylor polynomials, together with a bound on its error, from 2^-68 to 2^-63, that they pass
// to the rounding tests `round_dir_err` and `round_near_err` of `src/dyadic/fast.rs`. Above
// |x| = 709, beyond the range of `fast_exp`, sinh and cosh take e^|x| from `fast_exp_edge`, up
// to about 710.47578, just below 1025 ln 2, where e^|x| / 2 reaches 2^1024; from there to the
// rule at 711 they go to `ziv` and `ziv_near`. `rocq/theories/FastRoundErr.v` proves those
// rounding tests, `rocq/theories/FastRoundWide.v` them at e = 1023, `rocq/theories/FastDiv.v`
// `dd_div`, `rocq/theories/FastHypPoly.v` and `rocq/theories/FastCoshPoly.v` the Taylor
// polynomials (with `rocq/theories/HypTaylor.v`, `rocq/theories/FastSinhHorner.v` and
// `rocq/theories/FastSinhSteps.v`), `rocq/theories/FastHypPos.v`,
// `rocq/theories/FastCoshPos.v` and `rocq/theories/FastTanhPos.v` the bounds of
// `fast_sinh_pos` and the others, and `rocq/theories/FastHyp.v` proves that the fast paths
// return sinh x, cosh x and tanh x rounded, with and without an FMA.
//
// The fast path of x^y and x^n in `src/dyadic/pow.rs` also calls `fast_exp`, at y ln x in
// double-double, and rounds its result with the bound `ERR67`. Where th, the high part of
// y ln x, is out of the range of `fast_exp` but short of the bounds past which its rules on th
// settle overflow and underflow, it then calls `fast_exp_edge` and rounds that result once at
// the same 2^-67, subnormal results included, with `round_dir_wide_err` and
// `round_near_wide_err` of `src/dyadic/fast.rs`, which fail where the exponent of
// `fast_exp_edge` is above 1023, as the header of `src/dyadic/pow.rs` says.

use super::{
    consts::{ln10, ln2},
    fast::{
        dd_div, fast_two_sum, normalize, round_dir, round_dir_err, round_dir_wide, round_near,
        round_near_err, round_near_wide, two_sum,
    },
    level::level_entry,
    ziv, ziv_near, Dyadic, Encl, Eval,
};
use crate::simd::two_prod_err;
use std::f64::consts::{LOG2_10, LOG2_E};
use tables::{T1, T2};

mod tables;
#[cfg(test)]
mod tests;

// 2^-26, 2^-54 and 2^-56: the arguments of smaller magnitude have results within an ulp of x
// for sinh and tanh, and for asinh and atanh in `src/dyadic/log.rs`, and of 1 for cosh
// (`TINY_HYP`), e^x and 2^x (`TINY_EXP`), and 10^x (`TINY_EXP10`).
pub(super) const TINY_HYP: f64 = 1.0 / 67_108_864.0;
const TINY_EXP: f64 = f64::EPSILON / 4.0;
const TINY_EXP10: f64 = f64::EPSILON / 16.0;

// 2^-27: the arguments of smaller magnitude have results within half an ulp of x, or of 1,
// for the functions rounded to nearest that take it, as x^2 < 2^-54.
pub(super) const TINY_NEAR: f64 = 1.0 / 134_217_728.0;

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
pub(super) fn mul_f64<const N: usize>(a: &Encl<N>, x: f64) -> Encl<N> {
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
pub(super) fn scaled<const N: usize>(
    mut y: Encl<N>,
    mut k: i64,
    h: &Dyadic<N>,
    l: &Encl<N>,
) -> Encl<N> {
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
pub(super) fn overflow(up: bool) -> f64 {
    if up {
        f64::INFINITY
    } else {
        f64::MAX
    }
}

// The rounding of a number in (0, 2^-1074).
pub(super) fn underflow(up: bool) -> f64 {
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

// The constants of `fast_exp`, as the bits of `f64`s, since `f64::from_bits` is not `const`
// before Rust 1.83. c = ln 2 / 4096; `C1` is c with its significand cut to 31 bits, so that
// k C1 is exact for |k| < 2^22, and `C2` = RN(c - C1), with |c - C1 - C2| < 2^-98. `INV` =
// RN(1 / c), `P3` = RN(1/6) and `P4` = RN(1/24). `LN2` and `LN10` are ln 2 and ln 10 in
// double-double, [RN(v), RN(v - RN(v))], within 2^-106 and 2^-105 of them.
const C1: u64 = 0x3f262e42fec00000;
const C2: u64 = 0x3d3d1cf79abc9e3b;
const INV: u64 = 0x40b71547652b82fe;
const P3: u64 = 0x3fc5555555555555;
const P4: u64 = 0x3fa5555555555555;
const LN2: [u64; 2] = [0x3fe62e42fefa39ef, 0x3c7abc9e3b39803f];
const LN10: [u64; 2] = [0x40026bb1bbb55516, 0xbcaf48ad494ea3e9];

// 64 ln 2 and 4 ln 2 as [SH, SL], the bits of `f64`s, for `fast_exp_edge`: SH is m LN2[0]
// rounded to a multiple of 2^-43, so that zh + SH and zh - SH are exact where zh and the result
// are in [512, 1024) in magnitude, and SL = RN(m LN2[0] - SH + m LN2[1]), with
// |SH + SL - m ln 2| < 2^-98 and |SL| < 2^-46.
const LN2_64: [u64; 2] = [0x40462e42fefa39f0, 0xbcf950d871319ff0];
const LN2_4: [u64; 2] = [0x40062e42fefa3a00, 0xbd00ca86c3898d00];

// 1.5 * 2^52: for |t| < 2^51, (t + SHIFTER) - SHIFTER is t rounded to an integer.
pub(super) const SHIFTER: f64 = 6_755_399_441_055_744.0;

// The coefficients of the Taylor polynomials of the fast paths of sinh, cosh and tanh, as the
// bits of `f64`s: `SH<n>` = RN(1/n!) for the odd n from 5 to 15 and `CH<n>` = RN(1/n!) for the
// even n from 4 to 12, and `SH3` is 1/6 in double-double, [RN(1/6), RN(1/6 - RN(1/6))], within
// 2^-110 of it, which the series of acosh near 1 in `src/dyadic/log.rs` takes too.
pub(super) const SH3: [u64; 2] = [0x3fc5555555555555, 0x3c65555555555555];
const SH5: u64 = 0x3f81111111111111;
const SH7: u64 = 0x3f2a01a01a01a01a;
const SH9: u64 = 0x3ec71de3a556c734;
const SH11: u64 = 0x3e5ae64567f544e4;
const SH13: u64 = 0x3de6124613a86d09;
const SH15: u64 = 0x3d6ae7f3e733b81f;
const CH4: u64 = 0x3fa5555555555555;
const CH6: u64 = 0x3f56c16c16c16c17;
const CH8: u64 = 0x3efa01a01a01a01a;
const CH10: u64 = 0x3e927e4fb7789f5c;
const CH12: u64 = 0x3e21eed8eff8d898;

// 2^-63, 2^-67 and 2^-68: the error bounds of the fast paths of sinh, cosh and tanh that are
// not computed from an exponent, and 2^-67 also that of x^y and x^n in `src/dyadic/pow.rs` and
// of asinh, acosh and atanh near their zeros in `src/dyadic/log.rs`.
const ERR63: f64 = f64::EPSILON / 2048.0;
pub(super) const ERR67: f64 = f64::EPSILON / 32768.0;
const ERR68: f64 = f64::EPSILON / 65536.0;

// e^z for z = zh + zl, as (h, l, e) with e^z 2^-e within 2^-68 - 2^-72 of h + l, h = RN(h + l),
// 1/2 < h < 2 and e in [-1021, 1022], for zh in [-707, 709] and |zl| <= 2^-40, and `None` for
// any other zh, NaN included. The reduction and the tables are those of CORE-MATH's `exp`
// [CORE-MATH] (and of pxfm's): z = k ln 2 / 4096 + r with k = 4096 e + 64 j + i and
// |r| < 2^-13, so that e^z = 2^e 2^(j/64) 2^(i/4096) e^r. The polynomial is the Taylor
// polynomial of degree 4 rather than a minimax one, and every product is either exact or
// rounded on its own: `f64::mul_add` is used only in `two_prod_err`, where it is exact, so that
// h and l are the same `f64`s on every target. `rocq/theories/FastExpCore.v` proves the bound
// (`fast_exp_correct`), from the bounds of `rocq/theories/FastExpTables.v` on the tables and
// constants.
//
// [CORE-MATH] P. Zimmermann et al., the CORE-MATH project, `src/binary64/exp/exp.c` (MIT
// license); no constant or table is copied from it.
#[cfg_attr(inari_kernel_dispatch, inline(always))]
pub(super) fn fast_exp<const FMA: bool>(zh: f64, zl: f64) -> Option<(f64, f64, i64)> {
    if !(-707.0..=709.0).contains(&zh) {
        return None;
    }
    let (c1, c2) = (f64::from_bits(C1), f64::from_bits(C2));
    // k is zh / c rounded to an integer up to the roundings of `INV` and of the product, and
    // |k| < 2^22: |zh INV| < 2^51, so adding and subtracting `SHIFTER` rounds RN(zh INV) to an
    // integer, within 1/2 of it.
    let ks = zh * f64::from_bits(INV) + SHIFTER;
    let kf = ks - SHIFTER;
    // ks is the integer SHIFTER + k, so its low 32 bits are k.
    let k = ks.to_bits() as i32 as i64;
    // r = z - k c = rh + rl up to the rounding of rl and |k| |c - C1 - C2|. kf C1 is exact, and
    // so is rh: zh and kf C1 are multiples of 2^-66 where k != 0, and |rh| < 2^-13.
    let rh = zh - kf * c1;
    let rl = zl - kf * c2;
    // q = e^r - 1 - r, from rr = RN(rh + rl), by Horner's scheme on the Taylor polynomial.
    let rr = rh + rl;
    let q = rr * rr * (0.5 + rr * (f64::from_bits(P3) + rr * f64::from_bits(P4)));
    // e^r = s + pl up to the truncation of the series and the roundings of rr, q and pl, with
    // s + t = 1 + rh exactly. [Dekker]
    let (s, t) = fast_two_sum(1.0, rh);
    let pl = (t + rl) + q;
    // 2^(j/64) 2^(i/4096) = th + tl, from the exact product of the high parts, [Dekker], and
    // the cross products. The product of the low parts is below 2^-104 and left out.
    let [a1h, a1l] = T1[(k & 63) as usize];
    let [a2h, a2l] = T2[((k >> 6) & 63) as usize];
    let (a1h, a1l) = (f64::from_bits(a1h), f64::from_bits(a1l));
    let (a2h, a2l) = (f64::from_bits(a2h), f64::from_bits(a2l));
    let th = a1h * a2h;
    let tl = two_prod_err::<FMA>(a1h, a2h, th) + (a1h * a2l + a1l * a2h);
    // (s + pl) (th + tl), with s th exact and pl tl, below 2^-70, left out.
    let ph = s * th;
    let low = two_prod_err::<FMA>(s, th, ph) + (s * tl + pl * th);
    let (h, l) = fast_two_sum(ph, low);
    Some((h, l, k >> 12))
}

// e^(x c) for c = ch + cl, given as the bits [ch, cl], from `fast_exp`: z = x ch + x cl, with
// x ch in double-double. The product is exact for 2^-56 <= |x| <= 1075, which the rules of
// `exp2` and `exp10` leave.
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_exp_by<const FMA: bool>(x: f64, c: [u64; 2]) -> Option<(f64, f64, i64)> {
    let (ch, cl) = (f64::from_bits(c[0]), f64::from_bits(c[1]));
    let zh = x * ch;
    let zl = two_prod_err::<FMA>(x, ch, zh) + x * cl;
    fast_exp::<FMA>(zh, zl)
}

// e^z as `fast_exp` returns it, with e in [-1085, 1026], for the zh below -707 and above 709
// that the rules leave, from e^z = 2^-64 e^(z + 64 ln 2) and e^z = 2^4 e^(z - 4 ln 2), which
// `fast_exp` covers: zh is a multiple of 2^-43 there, so zh + SH and zh - SH are exact, and the
// shift moves z by less than 2^-91, the error of SH + SL and of RN(zl + SL), which moves the
// scaled result by less than 2^-87 (`rocq/theories/FastExpEdge.v`).
// Always inlined, as is `fast_exp_by_edge`: out of line, the call made `exp`, `exp2` and
// `fast_cosh_pos` set up a stack frame on every call, also where x never comes here, which
// cost 3 to 5 instructions per call on the arguments of the normal range (cachegrind).
// The fast path of x^y and x^n calls it too, for the th out of the range of `fast_exp` that its
// rules on th leave (`src/dyadic/pow.rs`).
#[inline(always)]
pub(super) fn fast_exp_edge<const FMA: bool>(zh: f64, zl: f64) -> Option<(f64, f64, i64)> {
    if zh < 0.0 {
        let (h, l, e) = fast_exp::<FMA>(
            zh + f64::from_bits(LN2_64[0]),
            zl + f64::from_bits(LN2_64[1]),
        )?;
        Some((h, l, e - 64))
    } else {
        let (h, l, e) =
            fast_exp::<FMA>(zh - f64::from_bits(LN2_4[0]), zl - f64::from_bits(LN2_4[1]))?;
        Some((h, l, e + 4))
    }
}

// `fast_exp_by` with `fast_exp_edge` in place of `fast_exp`, always inlined as it is.
#[inline(always)]
fn fast_exp_by_edge<const FMA: bool>(x: f64, c: [u64; 2]) -> Option<(f64, f64, i64)> {
    let (ch, cl) = (f64::from_bits(c[0]), f64::from_bits(c[1]));
    let zh = x * ch;
    let zl = two_prod_err::<FMA>(x, ch, zh) + x * cl;
    fast_exp_edge::<FMA>(zh, zl)
}

// e^x, 2^x and 10^x rounded toward +∞ if `up` and toward -∞ otherwise, and to nearest, by the
// fast path, or `None` where its rounding test fails or x is out of its range; outside the
// range of `fast_exp`, by `fast_exp_edge` with `round_dir_wide` and `round_near_wide`.
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_exp_dir<const FMA: bool>(x: f64, up: bool) -> Option<f64> {
    match fast_exp::<FMA>(x, 0.0) {
        Some((h, l, e)) => round_dir(h, l, e, up),
        None => {
            let (h, l, e) = fast_exp_edge::<FMA>(x, 0.0)?;
            round_dir_wide(h, l, e, up)
        }
    }
}

#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_exp2_dir<const FMA: bool>(x: f64, up: bool) -> Option<f64> {
    match fast_exp_by::<FMA>(x, LN2) {
        Some((h, l, e)) => round_dir(h, l, e, up),
        None => {
            let (h, l, e) = fast_exp_by_edge::<FMA>(x, LN2)?;
            round_dir_wide(h, l, e, up)
        }
    }
}

#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_exp10_dir<const FMA: bool>(x: f64, up: bool) -> Option<f64> {
    match fast_exp_by::<FMA>(x, LN10) {
        Some((h, l, e)) => round_dir(h, l, e, up),
        None => {
            let (h, l, e) = fast_exp_by_edge::<FMA>(x, LN10)?;
            round_dir_wide(h, l, e, up)
        }
    }
}

#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_exp_near<const FMA: bool>(x: f64) -> Option<f64> {
    match fast_exp::<FMA>(x, 0.0) {
        Some((h, l, e)) => round_near(h, l, e),
        None => {
            let (h, l, e) = fast_exp_edge::<FMA>(x, 0.0)?;
            round_near_wide(h, l, e)
        }
    }
}

#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_exp2_near<const FMA: bool>(x: f64) -> Option<f64> {
    match fast_exp_by::<FMA>(x, LN2) {
        Some((h, l, e)) => round_near(h, l, e),
        None => {
            let (h, l, e) = fast_exp_by_edge::<FMA>(x, LN2)?;
            round_near_wide(h, l, e)
        }
    }
}

#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_exp10_near<const FMA: bool>(x: f64) -> Option<f64> {
    match fast_exp_by::<FMA>(x, LN10) {
        Some((h, l, e)) => round_near(h, l, e),
        None => {
            let (h, l, e) = fast_exp_by_edge::<FMA>(x, LN10)?;
            round_near_wide(h, l, e)
        }
    }
}

// 2^e, for e in [-1022, 1023], from its bits.
pub(super) fn two_pow(e: i64) -> f64 {
    f64::from_bits(((e + 1023) as u64) << 52)
}

// sinh t as sh + sl, with sh = RN(sh + sl), for t in [2^-27, 1/4), from the odd Taylor
// polynomial t + t^3 (1/6 + u (1/5! + u (1/7! + ... + u 1/15!))) for u = t^2, whose
// truncation is below 2^-80 sinh t. u = uh + ul exactly, and t^3 = t3h + t3l up to the roundings
// of t ul and of its sum with the error of t uh, by `two_prod_err` [Dekker]; the tail after 1/6
// is in plain `f64`, and 1/6 + u A in double-double, normalized by [Dekker]'s Fast2Sum as
// 1/6 > u A.
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_sinh_poly<const FMA: bool>(t: f64) -> (f64, f64) {
    let uh = t * t;
    let ul = two_prod_err::<FMA>(t, t, uh);
    let a = f64::from_bits(SH5)
        + uh * (f64::from_bits(SH7)
            + uh * (f64::from_bits(SH9)
                + uh * (f64::from_bits(SH11)
                    + uh * (f64::from_bits(SH13) + uh * f64::from_bits(SH15)))));
    let (bh, b0) = fast_two_sum(f64::from_bits(SH3[0]), uh * a);
    let bl = b0 + f64::from_bits(SH3[1]);
    let t3h = t * uh;
    let t3l = two_prod_err::<FMA>(t, uh, t3h) + t * ul;
    // t^3 (bh + bl), with the product of the low parts, below 2^-100 t, left out.
    let ch = t3h * bh;
    let cl = two_prod_err::<FMA>(t3h, bh, ch) + (t3h * bl + t3l * bh);
    // ch is about sinh t - t < t^3 / 5 < t / 80, so t > ch and Fast2Sum applies, twice.
    let (sh, s0) = fast_two_sum(t, ch);
    fast_two_sum(sh, s0 + cl)
}

// cosh t as ch + cl, with |cl| <= 2^-52 ch, for t in [2^-27, 1/8), from
// the even Taylor polynomial 1 + u / 2 + u^2 (1/4! + u (1/6! + ... + u 1/12!)) for u = t^2,
// whose truncation is below 2^-78. u / 2 + u^2 A in double-double, then 1 + u / 2 + u^2 A, by
// Fast2Sum [Dekker] as 1 > u / 2 > u^2 A. ch need not be RN(ch + cl): cl adds m0 + ul / 2 to
// the error of 1 + mh, which can pass half an ulp of ch. `dd_div` needs only the bound on cl.
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_cosh_poly<const FMA: bool>(t: f64) -> (f64, f64) {
    let uh = t * t;
    let ul = two_prod_err::<FMA>(t, t, uh);
    let a = f64::from_bits(CH4)
        + uh * (f64::from_bits(CH6)
            + uh * (f64::from_bits(CH8) + uh * (f64::from_bits(CH10) + uh * f64::from_bits(CH12))));
    let v = (uh * uh) * a;
    let (mh, m0) = fast_two_sum(uh * 0.5, v);
    let (ch, c0) = fast_two_sum(1.0, mh);
    (ch, c0 + (m0 + ul * 0.5))
}

// sinh t for t >= 0 as (h, l, e, err), with sinh t 2^-e within err of h + l, h = RN(h + l),
// e in [-1021, 1023] and err = 2^-p for an integer p in [55, 105], or `None`; the rounding
// tests check 1/2 < h < 2. Below 1/4, the Taylor polynomial, scaled to [1, 2). From 1/4,
// sinh t = (e^t - e^-t) / 2 with e^t = y 2^e from `fast_exp` and e^-t 2^-e = 2^-2e / y from
// the quotient of `dd_div`; from 26 on, e^-t 2^-e < 2^-74 is left out.
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_sinh_pos<const FMA: bool>(t: f64) -> Option<(f64, f64, i64, f64)> {
    if t < TINY_NEAR {
        return None;
    }
    if t < 0.25 {
        let (sh, sl) = fast_sinh_poly::<FMA>(t);
        let (h, l, k) = normalize(sh, sl);
        return Some((h, l, k, ERR63));
    }
    let (h, l, e) = match fast_exp::<FMA>(t, 0.0) {
        Some(r) => r,
        None => {
            // t > 709: e^t from `fast_exp_edge`, with e^-t 2^-e left out as from 26 on, and
            // `None` where e - 1 would be above 1023.
            let (h, l, e) = fast_exp_edge::<FMA>(t, 0.0)?;
            return if e > 1024 {
                None
            } else {
                Some((h, l, e - 1, ERR68))
            };
        }
    };
    if t >= 26.0 {
        return Some((h, l, e - 1, ERR68));
    }
    let (wh, wl) = dd_div::<FMA>(two_pow(-2 * e), 0.0, h, l);
    // TwoSum [Knuth] for both sums: it needs no order of the terms, so the proof shows none.
    let (s, s0) = two_sum(h, -wh);
    let (h, l) = two_sum(s, (s0 + l) - wl);
    Some((h, l, e - 1, ERR67))
}

// cosh t for t >= 0 as `fast_sinh_pos` returns sinh t, from (e^t + e^-t) / 2 for every t, as
// the sum does not cancel, halved where it is 2 or more.
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_cosh_pos<const FMA: bool>(t: f64) -> Option<(f64, f64, i64, f64)> {
    let (h, l, e) = match fast_exp::<FMA>(t, 0.0) {
        Some(r) => r,
        None => {
            // t > 709, as in `fast_sinh_pos`.
            let (h, l, e) = fast_exp_edge::<FMA>(t, 0.0)?;
            return if e > 1024 {
                None
            } else {
                Some((h, l, e - 1, ERR68))
            };
        }
    };
    if t >= 26.0 {
        return Some((h, l, e - 1, ERR68));
    }
    let (wh, wl) = dd_div::<FMA>(two_pow(-2 * e), 0.0, h, l);
    let (s, s0) = two_sum(h, wh);
    // s >= h > 1/2 and |(s0 + l) + wl| < 2^-50, so Fast2Sum applies.
    let (h, l) = fast_two_sum(s, (s0 + l) + wl);
    if h >= 2.0 {
        Some((h * 0.5, l * 0.5, e, ERR67))
    } else {
        Some((h, l, e - 1, ERR67))
    }
}

// tanh t for t >= 0 as `fast_sinh_pos` returns sinh t. Below 1/8, sinh t / cosh t from the
// Taylor polynomials; from 1/8, (1 - w) / (1 + w) for w = e^-2t = wh + wl from `fast_exp`,
// where 1 + wh and 1 - wh are exact in double-double by Fast2Sum [Dekker], as wh < 1. Both
// scale the quotient to [1, 2), and err is 2^-63 below 1/8 and, from 1/8 on, the 2^-67 that
// bounds the error of the unscaled quotient, scaled with it.
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_tanh_pos<const FMA: bool>(t: f64) -> Option<(f64, f64, i64, f64)> {
    if t < TINY_NEAR {
        return None;
    }
    if t < 0.125 {
        let (sh, sl) = fast_sinh_poly::<FMA>(t);
        let (ch, cl) = fast_cosh_poly::<FMA>(t);
        let (qh, ql) = dd_div::<FMA>(sh, sl, ch, cl);
        let (h, l, k) = normalize(qh, ql);
        return Some((h, l, k, ERR63));
    }
    let (h, l, e) = fast_exp::<FMA>(-2.0 * t, 0.0)?;
    // w = (h + l) 2^e: h 2^e is exact, and l 2^e rounds only where it is subnormal.
    let p = two_pow(e);
    let (wh, wl) = (h * p, l * p);
    let (dh, d0) = fast_two_sum(1.0, wh);
    let (nh, n0) = fast_two_sum(1.0, -wh);
    let (qh, ql) = dd_div::<FMA>(nh, n0 - wl, dh, d0 + wl);
    let (h, l, k) = normalize(qh, ql);
    Some((h, l, k, two_pow(-67 - k)))
}

// sinh x, cosh t for t = |x| and tanh x rounded toward +∞ if `up` and toward -∞ otherwise, and
// to nearest, by the fast paths, or `None` where the rounding test fails or the argument is
// out of their range. sinh and tanh are odd: for x < 0, f(x) rounded up is -f(-x) rounded down.
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_sinh_dir<const FMA: bool>(x: f64, up: bool) -> Option<f64> {
    let (h, l, e, err) = fast_sinh_pos::<FMA>(x.abs())?;
    let r = round_dir_err(h, l, e, err, up != (x < 0.0))?;
    Some(if x < 0.0 { -r } else { r })
}

#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_cosh_dir<const FMA: bool>(t: f64, up: bool) -> Option<f64> {
    let (h, l, e, err) = fast_cosh_pos::<FMA>(t)?;
    round_dir_err(h, l, e, err, up)
}

#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_tanh_dir<const FMA: bool>(x: f64, up: bool) -> Option<f64> {
    let (h, l, e, err) = fast_tanh_pos::<FMA>(x.abs())?;
    let r = round_dir_err(h, l, e, err, up != (x < 0.0))?;
    Some(if x < 0.0 { -r } else { r })
}

#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_sinh_near<const FMA: bool>(x: f64) -> Option<f64> {
    let (h, l, e, err) = fast_sinh_pos::<FMA>(x.abs())?;
    let r = round_near_err(h, l, e, err)?;
    Some(if x < 0.0 { -r } else { r })
}

#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_cosh_near<const FMA: bool>(t: f64) -> Option<f64> {
    let (h, l, e, err) = fast_cosh_pos::<FMA>(t)?;
    round_near_err(h, l, e, err)
}

#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_tanh_near<const FMA: bool>(x: f64) -> Option<f64> {
    let (h, l, e, err) = fast_tanh_pos::<FMA>(x.abs())?;
    let r = round_near_err(h, l, e, err)?;
    Some(if x < 0.0 { -r } else { r })
}

level_entry! {
    /// e^x rounded toward +∞ if `up` and toward -∞ otherwise.
    #[cfg_attr(inari_kernel_dispatch, inline(always))]
    pub(crate) fn exp(x: f64, up: bool) -> f64 = exp_with;
}

// The body of `exp`, with `FMA` for the products (`level_entry!`).
#[inline(always)]
fn exp_with<const FMA: bool>(x: f64, up: bool) -> f64 {
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
    } else if let Some(r) = fast_exp_dir::<FMA>(x, up) {
        r
    } else {
        ziv(&Exp(x), up, 1)
    }
}

level_entry! {
    /// e^x rounded to nearest, ties to even.
    pub(crate) fn exp_near(x: f64) -> f64 = exp_near_with;
}

// The body of `exp_near`, with `FMA` for the products (`level_entry!`).
#[inline(always)]
fn exp_near_with<const FMA: bool>(x: f64) -> f64 {
    if x.is_nan() || x == f64::INFINITY {
        x
    } else if x == f64::NEG_INFINITY {
        0.0
    } else if x >= 710.0 {
        f64::INFINITY
    } else if x <= -746.0 {
        // e^x < 2^-1075, half of the least subnormal number.
        0.0
    } else if x.abs() < TINY_EXP {
        // 1 - 2^-54 < 1 + x <= e^x <= 1 / (1 - x) < 1 + 2^-53.
        1.0
    } else if let Some(r) = fast_exp_near::<FMA>(x) {
        r
    } else {
        ziv_near(&Exp(x), 1)
    }
}

level_entry! {
    /// 2^x rounded toward +∞ if `up` and toward -∞ otherwise.
    #[cfg_attr(inari_kernel_dispatch, inline(always))]
    pub(crate) fn exp2(x: f64, up: bool) -> f64 = exp2_with;
}

// The body of `exp2`, with `FMA` for the products (`level_entry!`).
#[inline(always)]
fn exp2_with<const FMA: bool>(x: f64, up: bool) -> f64 {
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
    } else if let Some(r) = fast_exp2_dir::<FMA>(x, up) {
        r
    } else {
        ziv(&Exp2(x), up, 1)
    }
}

level_entry! {
    /// 2^x rounded to nearest, ties to even.
    pub(crate) fn exp2_near(x: f64) -> f64 = exp2_near_with;
}

// The body of `exp2_near`, with `FMA` for the products (`level_entry!`).
#[inline(always)]
fn exp2_near_with<const FMA: bool>(x: f64) -> f64 {
    if x.is_nan() || x == f64::INFINITY {
        x
    } else if x == f64::NEG_INFINITY {
        0.0
    } else if x >= 1024.0 {
        f64::INFINITY
    } else if x < -1075.0 {
        // 2^x < 2^-1075. At -1075 itself the enclosure is exact, and its tie goes to +0.
        0.0
    } else if x.abs() < TINY_EXP {
        // 2^x = e^(x ln 2), and |x ln 2| < |x|.
        1.0
    } else if let Some(r) = fast_exp2_near::<FMA>(x) {
        r
    } else {
        ziv_near(&Exp2(x), 1)
    }
}

level_entry! {
    /// 10^x rounded toward +∞ if `up` and toward -∞ otherwise.
    #[cfg_attr(inari_kernel_dispatch, inline(always))]
    pub(crate) fn exp10(x: f64, up: bool) -> f64 = exp10_with;
}

// The body of `exp10`, with `FMA` for the products (`level_entry!`).
#[inline(always)]
fn exp10_with<const FMA: bool>(x: f64, up: bool) -> f64 {
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
    } else if let Some(r) = fast_exp10_dir::<FMA>(x, up) {
        r
    } else {
        ziv(&Exp10(x), up, 1)
    }
}

level_entry! {
    /// 10^x rounded to nearest, ties to even.
    pub(crate) fn exp10_near(x: f64) -> f64 = exp10_near_with;
}

// The body of `exp10_near`, with `FMA` for the products (`level_entry!`).
#[inline(always)]
fn exp10_near_with<const FMA: bool>(x: f64) -> f64 {
    if x.is_nan() || x == f64::INFINITY {
        x
    } else if x == f64::NEG_INFINITY {
        0.0
    } else if x >= 309.0 {
        f64::INFINITY
    } else if x <= -324.0 {
        // 10^x < 2^-1075, half of the least subnormal number.
        0.0
    } else if x.abs() < TINY_EXP10 {
        // 10^x = e^(x ln 10), and |x ln 10| < 4 |x| < 2^-54.
        1.0
    } else if (1.0..=22.0).contains(&x) && x == x.floor() {
        POW10[x as usize]
    } else if x == 23.0 {
        // 10^23 = 5^23 2^23, with 5^23 odd and in [2^53, 2^54), is the midpoint of two
        // adjacent `f64`s, which an enclosure settles only if it is one of its bounds. `1e23`
        // is its rounding, ties to even.
        1e23
    } else if let Some(r) = fast_exp10_near::<FMA>(x) {
        r
    } else {
        ziv_near(&Exp10(x), 1)
    }
}

/// sinh x rounded toward +∞ if `up` and toward -∞ otherwise.
#[inline(always)]
pub(crate) fn sinh(x: f64, up: bool) -> f64 {
    // A copy per direction, where `up` is a constant.
    if up {
        sinh_dir::<true>(x)
    } else {
        sinh_dir::<false>(x)
    }
}

level_entry! {
    // `sinh` toward +∞ if `UP` and toward -∞ otherwise.
    fn sinh_dir<const UP: bool>(x: f64) -> f64 = sinh_dir_with;
}

// The body of `sinh_dir`, with `FMA` for the products (`level_entry!`).
#[inline(always)]
fn sinh_dir_with<const FMA: bool, const UP: bool>(x: f64) -> f64 {
    if x.is_nan() || x.is_infinite() {
        x
    } else if x >= 711.0 {
        // sinh x > 2^1024, as 711 > 1025 ln 2 = 710.47...
        overflow(UP)
    } else if x <= -711.0 {
        -overflow(!UP)
    } else if x.abs() < TINY_HYP {
        // x <= sinh x <= x + x^3 / 3 for x in [0, 1], and sinh is odd.
        away(x, UP)
    } else if let Some(r) = fast_sinh_dir::<FMA>(x, UP) {
        r
    } else {
        ziv(&Sinh(x), UP, 1)
    }
}

level_entry! {
    /// sinh x rounded to nearest, ties to even.
    pub(crate) fn sinh_near(x: f64) -> f64 = sinh_near_with;
}

// The body of `sinh_near`, with `FMA` for the products (`level_entry!`).
#[inline(always)]
fn sinh_near_with<const FMA: bool>(x: f64) -> f64 {
    if x.is_nan() || x.is_infinite() {
        x
    } else if x >= 711.0 {
        f64::INFINITY
    } else if x <= -711.0 {
        f64::NEG_INFINITY
    } else if x.abs() < TINY_NEAR {
        // x <= sinh x <= x + x^3 / 3 for x in [0, 1], and sinh is odd.
        x
    } else if let Some(r) = fast_sinh_near::<FMA>(x) {
        r
    } else {
        ziv_near(&Sinh(x), 1)
    }
}

level_entry! {
    /// cosh x rounded toward +∞ if `up` and toward -∞ otherwise.
    #[cfg_attr(inari_kernel_dispatch, inline(always))]
    pub(crate) fn cosh(x: f64, up: bool) -> f64 = cosh_with;
}

// The body of `cosh`, with `FMA` for the products (`level_entry!`).
#[inline(always)]
fn cosh_with<const FMA: bool>(x: f64, up: bool) -> f64 {
    let t = x.abs();
    if t.is_nan() || t == f64::INFINITY {
        t
    } else if t >= 711.0 {
        // cosh t > sinh t > 2^1024.
        overflow(up)
    } else if t < TINY_HYP {
        // 1 <= cosh t <= 1 + t^2 for t in [0, 1].
        near_one(t, up)
    } else if let Some(r) = fast_cosh_dir::<FMA>(t, up) {
        r
    } else {
        ziv(&Cosh(t), up, 1)
    }
}

level_entry! {
    /// cosh x rounded to nearest, ties to even.
    pub(crate) fn cosh_near(x: f64) -> f64 = cosh_near_with;
}

// The body of `cosh_near`, with `FMA` for the products (`level_entry!`).
#[inline(always)]
fn cosh_near_with<const FMA: bool>(x: f64) -> f64 {
    let t = x.abs();
    if t.is_nan() || t == f64::INFINITY {
        t
    } else if t >= 711.0 {
        f64::INFINITY
    } else if t < TINY_NEAR {
        // 1 <= cosh t <= 1 + t^2 for t in [0, 1].
        1.0
    } else if let Some(r) = fast_cosh_near::<FMA>(t) {
        r
    } else {
        ziv_near(&Cosh(t), 1)
    }
}

level_entry! {
    /// tanh x rounded toward +∞ if `up` and toward -∞ otherwise.
    #[cfg_attr(inari_kernel_dispatch, inline(always))]
    pub(crate) fn tanh(x: f64, up: bool) -> f64 = tanh_with;
}

// The body of `tanh`, with `FMA` for the products (`level_entry!`).
#[inline(always)]
fn tanh_with<const FMA: bool>(x: f64, up: bool) -> f64 {
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
    } else if let Some(r) = fast_tanh_dir::<FMA>(x, up) {
        r
    } else {
        ziv(&Tanh(x), up, 1)
    }
}

level_entry! {
    /// tanh x rounded to nearest, ties to even.
    pub(crate) fn tanh_near(x: f64) -> f64 = tanh_near_with;
}

// The body of `tanh_near`, with `FMA` for the products (`level_entry!`).
#[inline(always)]
fn tanh_near_with<const FMA: bool>(x: f64) -> f64 {
    if x.is_nan() {
        x
    } else if x >= 20.0 {
        // 1 - 2^-54 < tanh x <= 1, as 1 - tanh x = 2 / (e^2x + 1) and 40 > 55 ln 2 = 38.12...
        // `tanh`'s 19 is not enough here: 1 - tanh 19 > 2^-54.
        1.0
    } else if x <= -20.0 {
        -1.0
    } else if x.abs() < TINY_NEAR {
        // x - x^3 / 3 <= tanh x <= x for x in [0, 1], and tanh is odd.
        x
    } else if let Some(r) = fast_tanh_near::<FMA>(x) {
        r
    } else {
        ziv_near(&Tanh(x), 1)
    }
}
