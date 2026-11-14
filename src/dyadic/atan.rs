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
// that each of the four functions, at finite arguments in its domain (y != 0 or x > 0 for
// atan2) and where it does not panic, returns a value on the side of its result that the
// rounding is on, and, where a rule settles the arguments or a rounding test of `ziv` passes,
// its result rounded as `mpfr_round` in `rocq/theories/Mpfr.v` says. The rules that return
// ±π/4, ±π/2, ±3π/4 or ±π rounded, among them that of atan at |x| >= `HUGE_ATAN`, whose
// result rounds as ±π/2 does (`atan_huge_post` in `DyAtan.v`), take the rounded multiple of π
// from the constants of `pi_times`, not from `ziv`. `DyAtan.v` and `DyAsin.v` build on
// `rocq/theories/DyAtanCore.v` for `series`, `atan_series`, `atan_encl` and `asin_parts`,
// `rocq/theories/AtanSeries.v` for the bounds of the series and the halving,
// `rocq/theories/AtanIdent.v` for the identities that the evaluations use,
// `rocq/theories/DyConstPi.v` for π, `rocq/theories/AtanPiConst.v` for the constants of
// `pi_times` and `pi_times_near`, c π rounded in both directions and to nearest, and
// `rocq/theories/DyAtanTiny.v` for the rules of atan, asin and atan2 at tiny arguments and
// quotients, with `rocq/theories/AtanExactDiv.v` for the quotients that `exact_div` decides in
// `f64`. `rocq/theories/DyAtanNear.v` proves that each of the four functions rounded to
// nearest, at the same arguments, where a rule settles the arguments or a rounding
// test of `ziv_near` passes, returns its result rounded to nearest as `near_round` in
// `rocq/theories/NearF64.v` says, from the same enclosures, bounds and constants and the cells
// of `rocq/theories/NearCells.v`. It builds on
// `rocq/theories/DyAtanMidQ.v` for `midpoint_quotient`, which uses `AtanExactDiv.v` and
// `rocq/theories/MidQuot.v` for its quotient, `rocq/theories/MidRound.v` for its rounding
// toward zero and `rocq/theories/NearAtanMid.v` for atan at the midway quotients.
// `rocq/theories/DyAtanExact.v` proves that each of the four functions returns its result, in
// both directions, at every finite argument in its domain at which it is an `f64`. These are
// ±0 for atan and asin, y = ±0 with x > 0 for atan2, and 1 for acos: at a result r that is an
// `f64`, cos 2r is rational, (1 - x^2) / (1 + x^2) for atan x, 1 - 2 x^2 for asin x and
// (x^2 - y^2) / (x^2 + y^2) for atan2(y, x), and so is cos r = x for acos x, and
// `cos_irrational` in `rocq/theories/CosIrrational.v` shows that cos r is irrational for every
// rational r other than 0. Other than that, it is not proved that a test passes by the cap of
// `ziv` or of `ziv_near`, nor that the evaluations do not panic.
//
// atan, asin, acos and atan2 try a fast path after their rules and before `ziv` and `ziv_near`
// (`fast_atan_dir`, `fast_atan_near` and the others), with the rounding tests of
// `src/dyadic/fast.rs` (`round_dir_err` and `round_near_err`), which take a positive result:
// atan, asin and atan2 apply them to |f| and put the sign back. The fast path has two stages,
// which compute the same angles by the same identities: a first stage (`fast_atan_pos1` and the
// others), which computes a part of them in plain `f64`, and, where that returns `None` or its
// test fails, a second stage in double-double (`fast_atan_pos` and the others), whose test takes
// 2^-70. Where that test fails too, or the fast path declines the argument, the function calls
// `ziv` or `ziv_near` as before. The core of the second stage (`fast_atan_core`) takes atan t, for
// a double-double t = th + tl in [2^-61, 129/128], as atan c + atan u for c = i / 64, with i the
// integer nearest 64 th, and u = (t - c) / (1 + t c), with atan c in double-double from a table
// (`ATAN_TABLE` of `src/dyadic/atan/tables.rs`), u from `dd_div`, so that |u| <= 2^-7, and atan u
// from the odd Taylor polynomial of degree 11 (`fast_atan_poly`), within 2^-74 of atan t
// relatively. atan takes the core at |x| up to 1 and π/2 - atan(1 / |x|) above it. atan2
// takes atan of the quotient of the smaller of |y| and |x| by the larger, and then atan q,
// π - atan q, π/2 - atan q or π/2 + atan q by the octant, as the kernel's `Atan2` does
// (`octant`). asin and acos take atan(t / r) up to `ASIN_S` and atan(r / t) above it, for
// r = √(1 - t^2) in double-double (`fast_sqrt1m`, with `dd_sqrt`), as the kernel's
// `asin_parts` does with its own split, and acos takes π/2 - x in double-double at
// |x| < 2^-27, where no rule settles it. The fast path declines atan2 where its result is below
// 2^-1021, as the rounding tests scale by 2^e only for e >= -1021, acos at 1, whose result 0
// the kernel settles exactly, and the arguments at which the core meets 0 < |t - c| < 2^-80, a
// numerator that `dd_div` does not take. The table's points are rational, unlike the
// tan(j π / 256) of CORE-MATH's `atan` [CORE-MATH], so that each c is an `f64` and the table
// is checked from partial sums of the series of atan at rationals. The first stage does the
// same with `fast_atan1` in place of the core: the core's c, n = t - c, d = 1 + t c and table
// entry, and then, in plain `f64`, uh = RN(nh / dh) and the rest of the quotient from the
// remainder nh - uh dh, as in `dd_div`, and atan u from the odd Taylor polynomial of degree 9,
// within 2^-64 of atan t relatively, or `None` where |t - c| < 2^-80, t = c among them, which
// it leaves to the second stage. In place of `dd_div`, it takes 1 / |x| for atan from
// `fast_recip`, and the quotient of the significands for atan2 from `fast_quot`. It gives its
// test 2^-62 (`ERR62`) where it calls `fast_atan1`, and 2^-70 on its other arms.
// `rocq/theories/FastAtanCore.v` bounds the error of `fast_atan_core`, from
// `rocq/theories/FastAtanTables.v` for the table and the constants,
// `rocq/theories/FastAtanPoly.v` for the polynomial and `rocq/theories/FastAtanIdent.v` for
// atan c + atan u, and `rocq/theories/FastAtan1.v` that of `fast_atan1`, from
// `rocq/theories/FastAtan1Poly.v` for its polynomial and `rocq/theories/FastAtan1Div.v` and
// `rocq/theories/FastAtan1Rem.v` for its quotient. `rocq/theories/FastAtan1Quot.v` bounds
// `fast_quot` and `fast_recip`, with `rocq/theories/FastAtan1Mid.v`, and
// `rocq/theories/FastAtanAsm.v` proves `pio2_add`, `split` and `octant`, and bounds `octant`
// for an input within a given error d, which the first stage needs (`octant_bound`).
// `rocq/theories/FastAtan.v` proves that the fast paths of atan and atan2 return their results
// rounded, from either stage, with and without an FMA, with `rocq/theories/FastAtanQuot.v` for
// the quotients of the second stage.
// `rocq/theories/FastAsin.v` proves the same of asin and acos, from
// `rocq/theories/FastDdSqrt.v` for `dd_sqrt` and `rocq/theories/FastAsinSqrt.v`,
// `rocq/theories/FastAsinQuot.v`, `rocq/theories/FastAsinAngle.v` and
// `rocq/theories/FastAsinReal.v` for the steps. As those are correct roundings, the theorems
// of `DyAtan.v`, `DyAsin.v` and `DyAtanNear.v` above hold where the fast path returns too.
//
// [CORE-MATH] P. Zimmermann et al., the CORE-MATH project, `src/binary64/atan/atan.c` (MIT
// license); no constant or table is copied from it.

use super::{
    consts::pi,
    exp::{away, toward_zero, two_pow, SHIFTER, TINY_HYP, TINY_NEAR},
    fast::{dd_div, dd_sqrt, fast_two_sum, normalize, round_dir_err, round_near_err, two_sum},
    ziv, ziv_near, Dyadic, Encl, Eval,
};
use crate::simd::{two_prod_err, HAS_FMA};
use tables::ATAN_TABLE;

mod tables;
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

// k π rounded toward -∞ and toward +∞, as the bits of `f64`s, for k = 1/4, 1/2, 3/4 and 1: the
// `f64`s just below and just above k π. k π lies 0.28 of an ulp above the first for k = 1/4, 1/2
// and 1, where it is `FRAC_PI_4`, `FRAC_PI_2` and `PI`, and 0.21 of an ulp for k = 3/4, so that
// the first is also k π rounded to nearest. `rocq/theories/AtanPiConst.v` proves that the bits
// that `rocq/theories/Model.v` transcribes are these roundings, and the test
// `pi_bounds_are_roundings` checks those here against MPFR.
const PI_QUARTER: [u64; 2] = [0x3fe921fb54442d18, 0x3fe921fb54442d19];
const PI_HALF: [u64; 2] = [0x3ff921fb54442d18, 0x3ff921fb54442d19];
const PI_THREE_QUARTERS: [u64; 2] = [0x4002d97c7f3321d2, 0x4002d97c7f3321d3];
const PI_ONE: [u64; 2] = [0x400921fb54442d18, 0x400921fb54442d19];

// The bounds of k π above for k = 1/4, 1/2, 3/4 and 1, and `None` for any other k.
fn pi_bounds(k: f64) -> Option<[u64; 2]> {
    if k == 0.25 {
        Some(PI_QUARTER)
    } else if k == 0.5 {
        Some(PI_HALF)
    } else if k == 0.75 {
        Some(PI_THREE_QUARTERS)
    } else if k == 1.0 {
        Some(PI_ONE)
    } else {
        None
    }
}

// c π rounded toward +∞ if `up` and toward -∞ otherwise, for an `f64` c != 0, which makes c π
// irrational: from `pi_bounds` for |c| = 1/4, 1/2, 3/4 and 1, the c that `atan` and `atan2`
// pass up to their signs, and from `ziv` for any other c.
fn pi_times(c: f64, up: bool) -> f64 {
    match pi_bounds(c.abs()) {
        // c π lies between lo and hi for c > 0, and between -hi and -lo for c < 0.
        Some([lo, hi]) => {
            f64::from_bits(if up == c.is_sign_positive() { hi } else { lo }).copysign(c)
        }
        None => ziv(&PiMul(c), up, 1),
    }
}

// c π rounded to nearest, ties to even, for an `f64` c != 0: the lower bound of `pi_bounds`, with
// the sign of c, for |c| = 1/4, 1/2, 3/4 and 1, and `ziv_near` otherwise.
fn pi_times_near(c: f64) -> f64 {
    match pi_bounds(c.abs()) {
        Some([lo, _]) => f64::from_bits(lo).copysign(c),
        None => ziv_near(&PiMul(c), 1),
    }
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

// 2^25 and 2^1021, by which `tiny_quotient` and `midpoint_quotient` scale |y| to compare it
// with x in `f64`, before they divide.
const TWO_25: f64 = 33_554_432.0;
const TWO_1021: f64 = 0.5 / f64::MIN_POSITIVE;

// 2^-968, 2^128 and 2^996, the bound below which `exact_div` scales y, the scale, and the
// bound on x from which `tiny_quotient` and `midpoint_quotient` divide with `Dyadic`s, and
// 2^-1021, below which the `f64`s are the multiples of 2^-1074.
const TWO_M968: f64 = f64::MIN_POSITIVE * 18_014_398_509_481_984.0;
const TWO_128: f64 = 340_282_366_920_938_463_463_374_607_431_768_211_456.0;
const TWO_996: f64 = TWO_1021 / TWO_25;
const TWO_M1021: f64 = 2.0 * f64::MIN_POSITIVE;

// y / x if it is an `f64`, and `None` otherwise, for finite y != 0 and |y| < x < 2^996.
// q = y / x rounded to nearest is y / x if that is an `f64`, so that y / x is an `f64` exactly
// when q x = y. The function checks q s x = y s for s = 2^128 if |y| < 2^-968 and s = 1
// otherwise, which scales both sides exactly, as |q| <= 1, and |y| < 2^-968 where s = 2^128:
// the product p = qs x rounded to nearest is ys = y s, and the error qs x - p of the product
// is 0, which `two_prod_err` computes exactly where p = ys (T. J. Dekker, A floating-point
// technique for extending the available precision, Numer. Math. 18, 1971, without an FMA).
// There |p| = |ys| is in [2^-968, 2^996), since 2^-1074 2^128 = 2^-946, |qs| <= 2^128 and
// x < 2^996, which are the conditions of `two_prod_is_exact` in `src/simd/generic.rs`. Where
// p != ys, qs x != ys, as ys is an `f64` and would be p. Without the scale, the error of a
// product below 2^-968 can be below the subnormals: y = 2^-1073 and x = 1 + 2^-52 give
// q = 2^-1073, and q x - y = 2^-1125 rounds to 0, while y / x is not an `f64`.
// `rocq/theories/AtanExactDiv.v` proves that an `f64` that the function returns is y / x
// (`exact_div_correct`), and that the function returns the same with and without an FMA
// (`exact_div_fma`).
#[inline(always)]
fn exact_div(y: f64, x: f64) -> Option<f64> {
    let q = y / x;
    let s = if y.abs() < TWO_M968 { TWO_128 } else { 1.0 };
    let (qs, ys) = (q * s, y * s);
    let p = qs * x;
    if p == ys && two_prod_err::<HAS_FMA>(qs, x, p) == 0.0 {
        Some(q)
    } else {
        None
    }
}

// y / x, for finite y != 0 and x > 0, if it is an `f64` of magnitude below `TINY_HYP`. The
// first check leaves out, in `f64`, the y and x with |y| 2^25 >= x, at which |y / x| >= 2^-25,
// above `TINY_HYP`, so that the last check gives `None` too: |y| 2^25 is exact for
// |y| < 2^999, subnormal or not, and +∞ otherwise, where |y / x| > 2^999 / 2^1024. Then
// |y| < x, and `exact_div` decides the quotient for x < 2^996, and `tiny_quotient_dyadic`
// from 2^996 on. `rocq/theories/DyAtanTiny.v` proves that an `f64` that the function returns
// is y / x, below `TINY_HYP` in magnitude (`tiny_quotient_correct`), on both paths, with
// `exact_div_correct` for the first; that the function returns every such quotient, the same
// map as the `Dyadic` division alone, the tests check and Rocq does not prove.
//
// `exact_div`, `tiny_quotient` and `midpoint_quotient` are always inlined, and
// `tiny_quotient_dyadic` and `midpoint_quotient_dyadic` never: the `f64` checks then run in
// `atan2` and `atan2_near` without a stack frame of their own, which LLVM by itself builds for
// the `Dyadic`s in every call, so that atan2 takes 2.02 (rn) and 2.10 (rd, ru) times the
// instructions of CORE-MATH in the same rounding on uniform angles (cachegrind, 4,096 arguments,
// log-uniform radii in [2^-4, 2^4)), against 2.11 to 2.17 without the attributes, 10 to 14 more
// instructions per call. The attributes keep that layout if the `Dyadic` parts change.
#[inline(always)]
fn tiny_quotient(y: f64, x: f64) -> Option<f64> {
    if y.abs() * TWO_25 >= x {
        return None;
    }
    if x >= TWO_996 {
        return tiny_quotient_dyadic(y, x);
    }
    match exact_div(y, x) {
        Some(q) if q.abs() < TINY_HYP => Some(q),
        _ => None,
    }
}

// `tiny_quotient` with `Dyadic`s, for finite y != 0 and x > 0. q = `lo.to_f64(false)` <= `lo`
// <= y / x <= `hi` <= `hi.to_f64(true)`, so that y / x = q if the two `f64`s are equal. Two
// `f64`s whose quotient is a dyadic number have one of at most 53 bits, which 64 bits hold
// exactly, so that the check finds every such quotient that is an `f64`.
#[inline(never)]
fn tiny_quotient_dyadic(y: f64, x: f64) -> Option<f64> {
    let (a, b) = (Dyadic::<1>::from_f64(y), Dyadic::<1>::from_f64(x));
    let (lo, hi) = (a.div(&b, false), a.div(&b, true));
    let q = lo.to_f64(false);
    if q == hi.to_f64(true) && q.abs() < TINY_HYP {
        Some(q)
    } else {
        None
    }
}

// y / x rounded toward zero to an `f64`, for finite y != 0 and x > 0, if it is an odd multiple
// of 2^-1075, which, for two `f64`s, is below 2^-1022 in magnitude (see
// `midpoint_quotient_dyadic`). The `f64`s below 2^-1021 are the multiples of 2^-1074, so that
// such a quotient q is the midpoint between the two `f64`s q - 2^-1075 and q + 2^-1075. For
// q > 0, atan q is in (q - q^3 / 3, q), and q^3 / 3 < 2^-3000 is less than half an ulp,
// 2^-1075, so that atan q is between q and the `f64` f next to q toward zero, and rounds to
// nearest to f, as it does for q < 0, since atan is odd. Ziv's strategy settles that only at an
// enclosure of atan q narrower than q^3 / 3, which is q^2 / 3, 2^-2045 to 2^-2150, relative to
// q, at 32 or 64 limbs.
//
// The first check leaves out, in `f64`, the y and x with |y| 2^1021 >= x, at which
// |y / x| >= 2^-1021: |y| 2^1021 is exact for |y| < 8, subnormal or not, and +∞ otherwise,
// where |y / x| > 2^3 / 2^1024. For x < 2^996 the function then decides the quotient in `f64`:
// 2y is exact, |2y| < x, and y / x is an odd multiple m 2^-1075 of 2^-1075 below 2^-1022
// exactly when 2y / x, of magnitude below 2^-1020, is an `f64` q (`exact_div`) below 2^-1021
// whose bits are odd: below 2^-1021 the bits of |q| are the integer |q| / 2^-1074. The `f64` with
// the bits of q minus 1 is then (m - 1) 2^-1074 with the sign of y, -0 for m = 1 and y < 0, and
// its product by 0.5, exact as m - 1 is even, the `f64` next to y / x toward zero, with that
// sign. `midpoint_quotient_dyadic` decides it for x >= 2^996. `rocq/theories/DyAtanMidQ.v`
// proves that an `f64` that the function returns is atan(y / x) rounded to nearest
// (`midpoint_quotient_correct`), on both paths, with `exact_div_correct` for the first; that
// the function returns every such quotient, the same map as the `Dyadic` division alone, the
// tests check and Rocq does not prove.
#[inline(always)]
fn midpoint_quotient(y: f64, x: f64) -> Option<f64> {
    if y.abs() * TWO_1021 >= x {
        return None;
    }
    if x >= TWO_996 {
        return midpoint_quotient_dyadic(y, x);
    }
    match exact_div(2.0 * y, x) {
        Some(q) if q.abs() < TWO_M1021 && q.to_bits() & 1 == 1 => {
            Some(f64::from_bits(q.to_bits() - 1) * 0.5)
        }
        _ => None,
    }
}

// `midpoint_quotient` with `Dyadic`s, for finite y != 0 and x > 0.
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
//
// The first check of `midpoint_quotient` leaves out, in `f64` and before the `Dyadic`s, the y
// and x with |y| 2^1021 >= x, which the check of the exponents leaves out too, so that on this
// path it only saves the `Dyadic`s: that check passes only where |y| < 2^(a.exp + 64) <=
// 2^(b.exp + 63 - 1021) <= x 2^-1021, and so |y| < 8, as x < 2^1024, at which |y| 2^1021 is
// exact, subnormal or not. The tests check this, and Rocq does not prove it:
// `midpoint_quotient_dyadic_correct` of `rocq/theories/DyAtanMidQ.v` uses only the check of
// the exponents.
#[inline(never)]
fn midpoint_quotient_dyadic(y: f64, x: f64) -> Option<f64> {
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

// 2^-70: the bound on |y - (h + l)| of the second stage of every fast path below, for the result
// y scaled by 2^-e, with slack over the 2^-74 relative bound of `fast_atan_core`, and of the arms
// of the first stages that do not call `fast_atan1`, which the second stages have too.
const ERR70: f64 = f64::EPSILON / 262_144.0;

// 2^-62: the same bound for the first stage of every fast path below where it calls
// `fast_atan1`, with slack over the 2^-64 relative bound of `fast_atan1`.
const ERR62: f64 = f64::EPSILON / 1024.0;

// 2^-80: the smallest numerator that `dd_div` takes.
const TWO_M80: f64 = f64::EPSILON / 268_435_456.0;

// 181/256, just below 1/√2: the fast paths of asin and acos take atan(t / √(1 - t^2)) up to it,
// whose quotient is then at most 0.9998, and atan(√(1 - t^2) / t) above it, whose quotient is
// below 1.0003.
const ASIN_S: f64 = 0.70703125;

// π/2 in double-double, [RN(π/2), RN(π/2 - RN(π/2))], within 2^-107 of it, as the bits of
// `f64`s. π is 2 (π/2), exactly.
const PIO2: [u64; 2] = [0x3ff921fb54442d18, 0x3c91a62633145c07];

// The coefficients of the odd Taylor polynomial of atan, as the bits of `f64`s: `A3` is 1/3 in
// double-double, [RN(1/3), RN(1/3 - RN(1/3))], within 2^-108 of it, and `A<n>` = RN(1/n) for
// n = 5, 7, 9 and 11.
const A3: [u64; 2] = [0x3fd5555555555555, 0x3c75555555555555];
const A5: u64 = 0x3fc999999999999a;
const A7: u64 = 0x3fc2492492492492;
const A9: u64 = 0x3fbc71c71c71c71c;
const A11: u64 = 0x3fb745d1745d1746;

// atan u in double-double for u = uh + ul with 2^-82 <= |uh| <= 2^-7 and |ul| <= 2^-53 |uh|, as
// (ph, pl) with ph = RN(ph + pl): the odd Taylor polynomial u - u^3 B of degree 11, with
// B = 1/3 - v (1/5 - v (1/7 - v (1/9 - v / 11))) for v = u^2, whose truncation is below
// |u|^13 / 13 < 2^-87 |u|, as the series alternates with terms that decrease in magnitude. v and
// u^3 are double-doubles from `two_prod_err` [Dekker], B is 1/3 in double-double less v times
// the rest in plain `f64`, where Fast2Sum applies as v < 2^-14, and u^3 B is the exact product of
// the high parts plus the cross products. u^3 / 3 rounded alone would cost 2^-68.6 of atan u at
// |u| = 2^-7. `rocq/theories/FastAtanPoly.v` proves that ph + pl is within 2^-78 |u| of atan u,
// and that it is the same with and without an FMA (`fast_atan_poly_correct` and
// `fast_atan_poly_fma`).
fn fast_atan_poly(uh: f64, ul: f64) -> (f64, f64) {
    let vh = uh * uh;
    let vl = two_prod_err::<HAS_FMA>(uh, uh, vh) + 2.0 * (uh * ul);
    let a = f64::from_bits(A5)
        - vh * (f64::from_bits(A7) - vh * (f64::from_bits(A9) - vh * f64::from_bits(A11)));
    let (bh, b0) = fast_two_sum(f64::from_bits(A3[0]), -(vh * a));
    let bl = b0 + f64::from_bits(A3[1]);
    let wh = uh * vh;
    let wl = two_prod_err::<HAS_FMA>(uh, vh, wh) + (uh * vl + ul * vh);
    let ch = wh * bh;
    let cl = two_prod_err::<HAS_FMA>(wh, bh, ch) + (wh * bl + wl * bh);
    // ch is about u^3 / 3, below |u| 2^-15, so that Fast2Sum applies, twice.
    let (sh, s0) = fast_two_sum(uh, -ch);
    fast_two_sum(sh, (s0 + ul) - cl)
}

// atan t in double-double for t = th + tl with 2^-61 <= th <= 129/128 and |tl| <= 2^-53 th, as
// (ah, al) with ah = RN(ah + al) and |ah + al - atan t| <= 2^-74 atan t, or `None` where
// 0 < |t - c| < 2^-80 for the c below, which no t with tl = 0 gives. For c = i / 64, with i
// = 64 th rounded to an integer, atan t = atan c + atan u for u = (t - c) / (1 + t c), with
// |u| <= 2^-7, atan c in double-double from `ATAN_TABLE`, and atan u from `fast_atan_poly`.
// Where i = 0, t <= 1/128, and the polynomial takes t itself. th - c is exact and th c is
// exact as a pair, as the comments below say.
// `rocq/theories/FastAtanCore.v` proves the bound, and that the result is the same with and
// without an FMA (`fast_atan_core_correct` and `fast_atan_core_fma`).
fn fast_atan_core(th: f64, tl: f64) -> Option<(f64, f64)> {
    // 64 th < 2^51, so adding and subtracting `SHIFTER` rounds it to an integer, within 1/2, and
    // i is in [0, 64]. ks is the integer SHIFTER + i, so its low 32 bits are i.
    let ks = th * 64.0 + SHIFTER;
    let kf = ks - SHIFTER;
    let i = ks.to_bits() as i32 as i64;
    if i == 0 {
        return Some(fast_atan_poly(th, tl));
    }
    let [gh, gl] = ATAN_TABLE[i as usize];
    let (gh, gl) = (f64::from_bits(gh), f64::from_bits(gl));
    let c = kf * (1.0 / 64.0);
    // n = t - c = nh + nl exactly: th - c is exact by Sterbenz's lemma, as c / 2 <= th <= 2 c,
    // and a multiple of ulp(th), so that it is 0 or above |tl| in magnitude and Fast2Sum
    // applies [Dekker].
    let (nh, nl) = fast_two_sum(th - c, tl);
    if nh == 0.0 {
        // t = c.
        return Some((gh, gl));
    }
    if nh.abs() < TWO_M80 {
        return None;
    }
    // d = 1 + t c = dh + dl up to 2^-104 d: th c = p + pe exactly [Dekker], and 1 + p = s + s0
    // exactly by TwoSum [Knuth], as p may exceed 1.
    let p = th * c;
    let pe = two_prod_err::<HAS_FMA>(th, c, p);
    let (s, s0) = two_sum(1.0, p);
    let (dh, dl) = fast_two_sum(s, s0 + (pe + tl * c));
    // u = n / d, by `dd_div`, which takes a positive numerator.
    let (uh, ul) = if nh > 0.0 {
        dd_div(nh, nl, dh, dl)
    } else {
        let (qh, ql) = dd_div(-nh, -nl, dh, dl);
        (-qh, -ql)
    };
    let (ph, pl) = fast_atan_poly(uh, ul);
    // atan c >= atan(1/64) > 2^-7 >= |atan u|, so that Fast2Sum applies, twice.
    let (sh, s1) = fast_two_sum(gh, ph);
    Some(fast_two_sum(sh, s1 + (gl + pl)))
}

// atan t in double-double for t = th + tl as `fast_atan_core` takes it, with the same c, n and
// d, but in plain `f64` past them, as (ah, al) with ah = RN(ah + al) and
// |ah + al - atan t| <= 2^-64 atan t, or `None` where |t - c| < 2^-80, also at t = c, where the
// core returns atan c from its table. u = n / d is uh = RN(nh / dh) and ul, the rest of the
// quotient from the remainder nh - uh dh, which is an `f64` [Boldo-Daumas] and exact as in
// `dd_div`, without its sign split. atan u is u - u^3 B for the odd Taylor polynomial of degree
// 9, with B = 1/3 - v (1/5 - v (1/7 - v / 9)) for v = uh^2, all in `f64`, whose truncation is
// below |u|^11 / 11 < 2^-80 for |u| <= 2^-7. Where i = 0, the polynomial takes th itself.
// `rocq/theories/FastAtan1.v` proves the bound, and that the result is the same with and
// without an FMA (`fast_atan1_correct` and `fast_atan1_fma`).
fn fast_atan1(th: f64, tl: f64) -> Option<(f64, f64)> {
    // ks is the integer SHIFTER + i, so its low 32 bits are i.
    let ks = th * 64.0 + SHIFTER;
    let kf = ks - SHIFTER;
    let i = ks.to_bits() as i32 as i64;
    if i == 0 {
        // th <= 2^-7, and th^3 B < 2^-15 th, so that Fast2Sum applies.
        let v = th * th;
        let b = f64::from_bits(A3[0])
            - v * (f64::from_bits(A5) - v * (f64::from_bits(A7) - v * f64::from_bits(A9)));
        return Some(fast_two_sum(th, tl - (th * v) * b));
    }
    let [gh, gl] = ATAN_TABLE[i as usize];
    let (gh, gl) = (f64::from_bits(gh), f64::from_bits(gl));
    let c = kf * (1.0 / 64.0);
    // n = t - c = nh + nl and d = 1 + t c = dh + dl as in `fast_atan_core`.
    let (nh, nl) = fast_two_sum(th - c, tl);
    if nh.abs() < TWO_M80 {
        return None;
    }
    let p = th * c;
    let pe = two_prod_err::<HAS_FMA>(th, c, p);
    let (s, s0) = two_sum(1.0, p);
    let (dh, dl) = fast_two_sum(s, s0 + (pe + tl * c));
    // (nh - q) - qe = nh - uh dh exactly: q + qe = uh dh exactly [Dekker], and nh - q is exact
    // by Sterbenz's lemma.
    let uh = nh / dh;
    let q = uh * dh;
    let qe = two_prod_err::<HAS_FMA>(uh, dh, q);
    let ul = ((((nh - q) - qe) + nl) - uh * dl) / dh;
    let v = uh * uh;
    let b = f64::from_bits(A3[0])
        - v * (f64::from_bits(A5) - v * (f64::from_bits(A7) - v * f64::from_bits(A9)));
    // atan c >= atan(1/64) > 2^-7 >= |uh|, so that Fast2Sum applies, twice.
    let (sh, s1) = fast_two_sum(gh, uh);
    Some(fast_two_sum(sh, s1 + (gl + (ul - (uh * v) * b))))
}

// n / d in double-double for n and d in [1, 2), as (qh, ql) with qh = RN(n / d) and
// |ql| <= 2^-53 qh: p + pe = qh d exactly [Dekker], n - p is exact by Sterbenz's lemma, and
// the remainder n - qh d is an `f64` [Boldo-Daumas], so that n / d = qh + (n - qh d) / d.
// `rocq/theories/FastAtan1Quot.v` proves that qh + ql is within 2^-105 of n / d relatively
// (`fast_quot_correct`).
fn fast_quot(n: f64, d: f64) -> (f64, f64) {
    let qh = n / d;
    let p = qh * d;
    let pe = two_prod_err::<HAS_FMA>(qh, d, p);
    (qh, ((n - p) - pe) / d)
}

// 1 / t in double-double for t in (1, 2^54), as `fast_quot` with n = 1, but with the remainder
// r = 1 - qh t times qh in place of r / t: 1 / t = qh + r / t, and r / t - r qh = r^2 / t.
// `rocq/theories/FastAtan1Quot.v` proves that qh + ql is within 2^-104 of 1 / t relatively
// (`fast_recip_correct`).
fn fast_recip(t: f64) -> (f64, f64) {
    let qh = 1.0 / t;
    let p = qh * t;
    let pe = two_prod_err::<HAS_FMA>(qh, t, p);
    (qh, ((1.0 - p) - pe) * qh)
}

// f π/2 + (rh + rl) in double-double, for f = 1/2 or 1, |rh| <= f and |rl| <= 2^-52, as (h, l)
// with h = RN(h + l) within 2^-102 of it: f `PIO2` is within 2^-107 of f π/2, and its high part
// is above |rh|, so that Fast2Sum applies, twice [Dekker]. `rocq/theories/FastAtanAsm.v` proves
// it (`pio2_add_correct`).
fn pio2_add(f: f64, rh: f64, rl: f64) -> (f64, f64) {
    let (s, s0) = fast_two_sum(f64::from_bits(PIO2[0]) * f, rh);
    fast_two_sum(s, (s0 + f64::from_bits(PIO2[1]) * f) + rl)
}

// (m, e) with v = m 2^e exactly and m in [1, 2), for a finite v > 0 (`split_correct` in
// `rocq/theories/FastAtanAsm.v`).
fn split(v: f64) -> (f64, i64) {
    let (mut b, mut e) = (v.to_bits(), 0);
    if b < 1 << 52 {
        // A subnormal v: v 2^52 is exact and normal.
        b = (v * two_pow(52)).to_bits();
        e = -52;
    }
    e += (b >> 52) as i64 - 1023;
    (
        f64::from_bits((b & 0x000f_ffff_ffff_ffff) | 0x3ff0_0000_0000_0000),
        e,
    )
}

// The result of every fast path below from r = rh + rl in [0, 4/5], an angle in double-double:
// (h, l, e, err) with |f 2^-e - (h + l)| <= err for f = r if not `swap` and not `neg`, π - r
// if `neg` only, π/2 - r if `swap` only, and π/2 + r if both, as in the octants of atan2. Each
// sum other than r is at least π/2 - 4/5 > 3/4, and those that reach above 2 are halved, so
// that h is in (1/2, 2), as the rounding tests take it. `rocq/theories/FastAtanAsm.v` proves the
// bound with err = 2^-70 for r within 2^-73 of an angle in (0, 4/5], and within 2^-73 of it
// relatively, with the angle at least 2^-1020, where f is that angle itself (`octant_correct`),
// and bounds |f 2^-e - (h + l)| by 3 d for r within d of the angle in the same senses, for
// 2^-100 <= d <= 2^-60, which the first stages need (`octant_bound`).
fn octant(swap: bool, neg: bool, rh: f64, rl: f64) -> (f64, f64, i64, f64) {
    match (swap, neg) {
        (false, false) => {
            let (h, l, k) = normalize(rh, rl);
            (h, l, k, ERR70)
        }
        // π - r = 2 (π/2 - r / 2), in [π - 4/5, π].
        (false, true) => {
            let (h, l) = pio2_add(1.0, -0.5 * rh, -0.5 * rl);
            (h, l, 1, ERR70)
        }
        // π/2 - r, in [π/2 - 4/5, π/2].
        (true, false) => {
            let (h, l) = pio2_add(1.0, -rh, -rl);
            (h, l, 0, ERR70)
        }
        // π/2 + r = 2 (π/4 + r / 2), in [π/2, π/2 + 4/5].
        (true, true) => {
            let (h, l) = pio2_add(0.5, 0.5 * rh, 0.5 * rl);
            (h, l, 1, ERR70)
        }
    }
}

// atan t as (h, l, e, err), with |atan t 2^-e - (h + l)| <= err, for t in [2^-27, 2^54), or
// `None` where the core returns `None`: the core at t itself up to 1, and π/2 - atan(1 / t)
// above it, with 1 / t in double-double from `dd_div` at m in [1, 2), for t = m 2^k, scaled
// by 2^-k, which is exact but for the low part where it is subnormal.
// `rocq/theories/FastAtan.v` proves the bound, with err = 2^-p for a p in [55, 105] and e in
// [-1021, 1022], and that the result is the same with and without an FMA
// (`fast_atan_pos_correct` and `fast_atan_pos_fma`), and the same of `fast_atan2_pos` below
// (`fast_atan2_pos_correct` and `fast_atan2_pos_fma`).
fn fast_atan_pos(t: f64) -> Option<(f64, f64, i64, f64)> {
    if t <= 1.0 {
        let (ah, al) = fast_atan_core(t, 0.0)?;
        Some(octant(false, false, ah, al))
    } else {
        let (m, k) = split(t);
        let (qh, ql) = dd_div(1.0, 0.0, m, 0.0);
        let p = two_pow(-k);
        let (ah, al) = fast_atan_core(qh * p, ql * p)?;
        Some(octant(true, false, ah, al))
    }
}

// atan2(a, x) as (h, l, e, err) for a = |y| and b = |x|, finite and nonzero, and neg = x < 0, or
// `None` where the result is below 2^-1021 or the core returns `None`. For n = min(a, b),
// d = max(a, b) and q = n / d in (0, 1], atan2(a, x) is atan q, π - atan q, π/2 - atan q or
// π/2 + atan q, by the octant, as in the kernel's `Atan2`. q is (mn / md) 2^(en - ed) for
// n = mn 2^en and d = md 2^ed with mn and md in [1, 2), whose quotient `dd_div` takes.
fn fast_atan2_pos(a: f64, b: f64, neg: bool) -> Option<(f64, f64, i64, f64)> {
    let swap = a > b;
    let (n, d) = if swap { (b, a) } else { (a, b) };
    let (mn, en) = split(n);
    let (md, ed) = split(d);
    let e = en - ed;
    let (qh, ql) = dd_div(mn, 0.0, md, 0.0);
    let (rh, rl) = if e >= -60 {
        // q >= 2^-61, scaled as in `fast_atan_pos`.
        let p = two_pow(e);
        fast_atan_core(qh * p, ql * p)?
    } else if swap || neg {
        // q < 2^-59, and atan q is within q^3 / 3 + 2^-53 q + 2^-1075 < 2^-110 of RN(n / d), which
        // only adds to π/2 or π.
        (n / d, 0.0)
    } else {
        // atan q is within q^3 / 3 < 2^-118 q of q. The results below 2^-1021 fall through to
        // the kernel: the rounding tests scale by 2^e only for e >= -1021.
        let (h, l, k) = normalize(qh, ql);
        return if e + k < -1021 {
            None
        } else {
            Some((h, l, e + k, ERR70))
        };
    };
    Some(octant(swap, neg, rh, rl))
}

// √(1 - t^2) in double-double for t in [2^-27, 1): t^2 = p + pe exactly [Dekker], 1 - p = s + s0
// exactly by Fast2Sum, and m = 1 - t^2 within 2^-106 of it, with m >= 2^-53 and |ml| <= 2^-53 mh,
// which `dd_sqrt` takes. Where p >= 1/2, 1 - p is exact by Sterbenz's lemma, and so is m.
// `rocq/theories/FastAsinSqrt.v` proves that the result is within 2^-99 of √(1 - t^2)
// relatively (`fast_sqrt1m_correct`).
fn fast_sqrt1m(t: f64) -> (f64, f64) {
    let p = t * t;
    let pe = two_prod_err::<HAS_FMA>(t, t, p);
    let (s, s0) = fast_two_sum(1.0, -p);
    let (mh, ml) = fast_two_sum(s, s0 - pe);
    dd_sqrt(mh, ml)
}

// atan(t / r), which is asin t, for t <= `ASIN_S`, and atan(r / t), which is acos t, above it,
// for r = √(1 - t^2) and t in [2^-27, 1), as the kernel's `asin_parts`, in double-double.
// `rocq/theories/FastAsin.v` proves that it is within 2^-73 of that relatively
// (`fast_asin_atan_correct`).
fn fast_asin_atan(t: f64) -> Option<(f64, f64)> {
    let (rh, rl) = fast_sqrt1m(t);
    let (qh, ql) = if t <= ASIN_S {
        dd_div(t, 0.0, rh, rl)
    } else {
        dd_div(rh, rl, t, 0.0)
    };
    fast_atan_core(qh, ql)
}

// asin t as (h, l, e, err), for t in [2^-27, 1], or `None` where the core returns `None`:
// asin 1 = π/2, and π/2 - acos t above `ASIN_S`.
fn fast_asin_pos(t: f64) -> Option<(f64, f64, i64, f64)> {
    if t == 1.0 {
        return Some((f64::from_bits(PIO2[0]), f64::from_bits(PIO2[1]), 0, ERR70));
    }
    let (ch, cl) = fast_asin_atan(t)?;
    Some(octant(t > ASIN_S, false, ch, cl))
}

// acos x as (h, l, e, err), for |x| <= 1, or `None` at x = 1, whose result 0 the kernel settles,
// and where the core returns `None`. For |x| < 2^-27, acos x = π/2 - asin x is within
// |x|^3 < 2^-81 of π/2 - x, as x < asin x <= x + x^3 for 0 < x < 2^-27. Otherwise, for
// t = |x|, acos t is π/2 - asin t up to `ASIN_S`, and acos(-t) = π - acos t.
// `rocq/theories/FastAsin.v` proves the bounds of this function and of `fast_asin_pos`, as
// `fast_atan_pos` has them, and that they are the same with and without an FMA
// (`fast_asin_pos_correct`, `fast_acos_val_correct`, `fast_asin_pos_fma` and
// `fast_acos_val_fma`).
fn fast_acos_val(x: f64) -> Option<(f64, f64, i64, f64)> {
    if x == 1.0 {
        return None;
    }
    if x.abs() < TINY_ASIN {
        let (h, l) = pio2_add(1.0, -x, 0.0);
        return Some((h, l, 0, ERR70));
    }
    if x == -1.0 {
        // π.
        return Some((f64::from_bits(PIO2[0]), f64::from_bits(PIO2[1]), 1, ERR70));
    }
    // π/2 - asin t and π/2 + asin t up to `ASIN_S`, and acos t and π - acos t above it.
    let t = x.abs();
    let (ch, cl) = fast_asin_atan(t)?;
    Some(octant(t <= ASIN_S, x < 0.0, ch, cl))
}

// The first stage of `fast_atan_pos`: the same, from `fast_atan1` in place of the core, with
// err = `ERR62`, and with 1 / t from `fast_recip` above 1. `rocq/theories/FastAtan.v` proves it
// as `fast_atan_pos` (`fast_atan_pos1_correct` and `fast_atan_pos1_fma`), and the same of the
// first stages of `fast_atan2_pos` below (`fast_atan2_pos1_correct` and `fast_atan2_pos1_fma`).
fn fast_atan_pos1(t: f64) -> Option<(f64, f64, i64, f64)> {
    if t <= 1.0 {
        let (ah, al) = fast_atan1(t, 0.0)?;
        let (h, l, e, _) = octant(false, false, ah, al);
        Some((h, l, e, ERR62))
    } else {
        let (qh, ql) = fast_recip(t);
        let (ah, al) = fast_atan1(qh, ql)?;
        let (h, l, e, _) = octant(true, false, ah, al);
        Some((h, l, e, ERR62))
    }
}

// The first stage of `fast_atan2_pos`: the same, from `fast_atan1` in place of the core, with
// err = `ERR62` where it is taken, and with the quotient of the significands from `fast_quot`,
// as `Some(Some(..))`. The results below 2^-1021 are `Some(None)`: the second stage would send
// them to the kernel too. `None` is where `fast_atan1` returns `None`.
// Always inlined: LLVM by itself keeps it out of line, with a stack frame of its own and its
// result through memory, at which atan2 takes 24 to 27 more instructions per call, 247.9 (rn),
// 260.2 (rd) and 259.7 (ru) against 221.2, 235.5 and 235.5 on y and x uniform in [-10, 10), and
// 248.9, 262.8 and 262.8 against 221.7, 238.1 and 238.1 on uniform angles with log-uniform
// radii in [2^-4, 2^4) (cachegrind, 4,096 arguments per set, in a test build for haswell
// without the tests module of this file).
#[inline(always)]
fn fast_atan2_pos1(a: f64, b: f64, neg: bool) -> Option<Option<(f64, f64, i64, f64)>> {
    let swap = a > b;
    let (n, d) = if swap { (b, a) } else { (a, b) };
    let (mn, en) = split(n);
    let (md, ed) = split(d);
    let e = en - ed;
    let (qh, ql) = fast_quot(mn, md);
    if e >= -60 {
        let p = two_pow(e);
        let (rh, rl) = fast_atan1(qh * p, ql * p)?;
        let (h, l, k, _) = octant(swap, neg, rh, rl);
        Some(Some((h, l, k, ERR62)))
    } else if swap || neg {
        Some(Some(octant(swap, neg, n / d, 0.0)))
    } else {
        let (h, l, k) = normalize(qh, ql);
        if e + k < -1021 {
            Some(None)
        } else {
            Some(Some((h, l, e + k, ERR70)))
        }
    }
}

// The first stage of `fast_asin_atan`: the same, from `fast_atan1` in place of the core.
// `rocq/theories/FastAsin.v` proves that it is within 2^-64 + 2^-84 of that relatively
// (`fast_asin_atan1_correct`).
fn fast_asin_atan1(t: f64) -> Option<(f64, f64)> {
    let (rh, rl) = fast_sqrt1m(t);
    let (qh, ql) = if t <= ASIN_S {
        dd_div(t, 0.0, rh, rl)
    } else {
        dd_div(rh, rl, t, 0.0)
    };
    fast_atan1(qh, ql)
}

// The first stages of `fast_asin_pos` and `fast_acos_val`: the same, from `fast_asin_atan1`, with
// err = `ERR62` where it is taken. `rocq/theories/FastAsin.v` proves them as those
// (`fast_asin_pos1_correct`, `fast_acos_val1_correct`, `fast_asin_pos1_fma` and
// `fast_acos_val1_fma`).
fn fast_asin_pos1(t: f64) -> Option<(f64, f64, i64, f64)> {
    if t == 1.0 {
        return Some((f64::from_bits(PIO2[0]), f64::from_bits(PIO2[1]), 0, ERR70));
    }
    let (ch, cl) = fast_asin_atan1(t)?;
    let (h, l, e, _) = octant(t > ASIN_S, false, ch, cl);
    Some((h, l, e, ERR62))
}

// Always inlined, as `fast_atan2_pos1`: LLVM by itself keeps it out of line, with its result
// through memory and, where it calls `fast_asin_atan1`, a stack frame of its own, at which acos
// takes 18 to 23 more instructions per call, 206.3 (rn), 205.5 (rd) and 205.0 (ru) against
// 184.0, 186.8 and 186.9 on x uniform in [-1, 1), and 205.9, 205.6 and 206.1 against 183.0,
// 186.5 and 186.5 on 1 - 2^-8 < |x| <= 1, and 15 to 17 more on 2^-60 <= |x| < 2^-27, 62.0, 61.3
// and 61.3 against 45.0, 46.2 and 46.7 (counted as for `fast_atan2_pos1`).
#[inline(always)]
fn fast_acos_val1(x: f64) -> Option<(f64, f64, i64, f64)> {
    if x == 1.0 {
        return None;
    }
    if x.abs() < TINY_ASIN {
        let (h, l) = pio2_add(1.0, -x, 0.0);
        return Some((h, l, 0, ERR70));
    }
    if x == -1.0 {
        return Some((f64::from_bits(PIO2[0]), f64::from_bits(PIO2[1]), 1, ERR70));
    }
    let t = x.abs();
    let (ch, cl) = fast_asin_atan1(t)?;
    let (h, l, e, _) = octant(t <= ASIN_S, x < 0.0, ch, cl);
    Some((h, l, e, ERR62))
}

#[cfg(test)]
thread_local! {
    // Whether the first stages of the fast paths are enabled on this thread.
    static STAGE1: std::cell::Cell<bool> = const { std::cell::Cell::new(true) };
}

/// Enables or disables the first stages of the fast paths of atan, asin, acos and atan2 on this
/// thread. Disabled, `fast_atan_dir1` and the others return `None`, so that every fast path
/// takes its second stage (`fast_atan_dir2` and the others).
#[cfg(test)]
pub(crate) fn set_atan_stage1(enabled: bool) {
    STAGE1.with(|s| s.set(enabled));
}

#[cfg(test)]
fn stage1_enabled() -> bool {
    STAGE1.with(|s| s.get())
}

// atan x, asin x, acos x and atan2(y, x) rounded toward +∞ if `up` and toward -∞ otherwise, and
// to nearest, by the fast paths, or `None` where the rounding test fails or the fast path does
// not apply. atan and asin are odd, and atan2 has the sign of y: for x < 0, f(x) rounded up is
// -f(-x) rounded down. `rocq/theories/FastAtan.v` and `rocq/theories/FastAsin.v` prove that they
// return those roundings, for 2^-27 <= |x| < 2^54 for atan, finite y and x other than 0 for
// atan2, 2^-27 <= |x| <= 1 for asin and |x| <= 1 for acos (`fast_atan_dir_correct` and the
// others), and the same with and without an FMA (`fast_atan_dir_fma` and the others). Each
// tries its first stage (`fast_atan_dir1` and the others, from `fast_atan_pos1` and the others),
// and its second stage (`fast_atan_dir2` and the others, from `fast_atan_pos` and the others)
// where that returns `None`. The comment of the second stages says which of them are inlined.
fn fast_atan_dir(x: f64, up: bool) -> Option<f64> {
    if let Some(r) = fast_atan_dir1(x, up) {
        return Some(r);
    }
    fast_atan_dir2(x, up)
}

fn fast_asin_dir(x: f64, up: bool) -> Option<f64> {
    if let Some(r) = fast_asin_dir1(x, up) {
        return Some(r);
    }
    fast_asin_dir2(x, up)
}

fn fast_acos_dir(x: f64, up: bool) -> Option<f64> {
    if let Some(r) = fast_acos_dir1(x, up) {
        return Some(r);
    }
    fast_acos_dir2(x, up)
}

fn fast_atan2_dir(y: f64, x: f64, up: bool) -> Option<f64> {
    if let Some(r) = fast_atan2_dir1(y, x, up) {
        return r;
    }
    fast_atan2_dir2(y, x, up)
}

fn fast_atan_near(x: f64) -> Option<f64> {
    if let Some(r) = fast_atan_near1(x) {
        return Some(r);
    }
    fast_atan_near2(x)
}

fn fast_asin_near(x: f64) -> Option<f64> {
    if let Some(r) = fast_asin_near1(x) {
        return Some(r);
    }
    fast_asin_near2(x)
}

fn fast_acos_near(x: f64) -> Option<f64> {
    if let Some(r) = fast_acos_near1(x) {
        return Some(r);
    }
    fast_acos_near2(x)
}

fn fast_atan2_near(y: f64, x: f64) -> Option<f64> {
    if let Some(r) = fast_atan2_near1(y, x) {
        return r;
    }
    fast_atan2_near2(y, x)
}

fn fast_atan_dir1(x: f64, up: bool) -> Option<f64> {
    #[cfg(test)]
    if !stage1_enabled() {
        return None;
    }
    let (h, l, e, err) = fast_atan_pos1(x.abs())?;
    let r = round_dir_err(h, l, e, err, up != (x < 0.0))?;
    Some(if x < 0.0 { -r } else { r })
}

fn fast_asin_dir1(x: f64, up: bool) -> Option<f64> {
    #[cfg(test)]
    if !stage1_enabled() {
        return None;
    }
    let (h, l, e, err) = fast_asin_pos1(x.abs())?;
    let r = round_dir_err(h, l, e, err, up != (x < 0.0))?;
    Some(if x < 0.0 { -r } else { r })
}

fn fast_acos_dir1(x: f64, up: bool) -> Option<f64> {
    #[cfg(test)]
    if !stage1_enabled() {
        return None;
    }
    let (h, l, e, err) = fast_acos_val1(x)?;
    round_dir_err(h, l, e, err, up)
}

// `Some(r)` is the answer of the fast path, where r = `None` sends atan2 to the kernel, and
// `None` is the second stage's turn, also where the rounding test fails.
fn fast_atan2_dir1(y: f64, x: f64, up: bool) -> Option<Option<f64>> {
    #[cfg(test)]
    if !stage1_enabled() {
        return None;
    }
    let (h, l, e, err) = match fast_atan2_pos1(y.abs(), x.abs(), x < 0.0)? {
        Some(v) => v,
        None => return Some(None),
    };
    let r = round_dir_err(h, l, e, err, up != (y < 0.0))?;
    Some(Some(if y < 0.0 { -r } else { r }))
}

fn fast_atan_near1(x: f64) -> Option<f64> {
    #[cfg(test)]
    if !stage1_enabled() {
        return None;
    }
    let (h, l, e, err) = fast_atan_pos1(x.abs())?;
    let r = round_near_err(h, l, e, err)?;
    Some(if x < 0.0 { -r } else { r })
}

fn fast_asin_near1(x: f64) -> Option<f64> {
    #[cfg(test)]
    if !stage1_enabled() {
        return None;
    }
    let (h, l, e, err) = fast_asin_pos1(x.abs())?;
    let r = round_near_err(h, l, e, err)?;
    Some(if x < 0.0 { -r } else { r })
}

fn fast_acos_near1(x: f64) -> Option<f64> {
    #[cfg(test)]
    if !stage1_enabled() {
        return None;
    }
    let (h, l, e, err) = fast_acos_val1(x)?;
    round_near_err(h, l, e, err)
}

fn fast_atan2_near1(y: f64, x: f64) -> Option<Option<f64>> {
    #[cfg(test)]
    if !stage1_enabled() {
        return None;
    }
    let (h, l, e, err) = match fast_atan2_pos1(y.abs(), x.abs(), x < 0.0)? {
        Some(v) => v,
        None => return Some(None),
    };
    let r = round_near_err(h, l, e, err)?;
    Some(Some(if y < 0.0 { -r } else { r }))
}

// The second stages. LLVM inlines them into the dir and near functions, which then call
// `fast_atan_pos`, `fast_asin_atan`, `fast_acos_val` and `fast_atan2_pos` out of line. The
// exception is `fast_atan2_dir2`, which is never inlined: inlined, it costs atan2 1.8 to 2.3
// more instructions per call in rd and ru. Never inlined, the others would cost more too: atan
// 3.5 to 8.8 per call on x uniform in [-10, 10) and [-1, 1) and |x| log-uniform in
// [2^-30, 2^30), and asin 3.4 to 4.1 on x uniform in [-1, 1) and |x| log-uniform in
// [2^-30, 1) and [2^-26, 2^-8). acos would cost 2.9 to 4.9 more, and atan2 3.0 more in rn.
// The arguments of acos and atan2 are those in the comments of `fast_acos_val1` and
// `fast_atan2_pos1`, and all these counts are made as there. Either way, the first stage runs
// in a stack frame, which its call of `fast_atan1` or `fast_asin_atan1` needs, as their result
// comes back through memory.
fn fast_atan_dir2(x: f64, up: bool) -> Option<f64> {
    let (h, l, e, err) = fast_atan_pos(x.abs())?;
    let r = round_dir_err(h, l, e, err, up != (x < 0.0))?;
    Some(if x < 0.0 { -r } else { r })
}

fn fast_asin_dir2(x: f64, up: bool) -> Option<f64> {
    let (h, l, e, err) = fast_asin_pos(x.abs())?;
    let r = round_dir_err(h, l, e, err, up != (x < 0.0))?;
    Some(if x < 0.0 { -r } else { r })
}

fn fast_acos_dir2(x: f64, up: bool) -> Option<f64> {
    let (h, l, e, err) = fast_acos_val(x)?;
    round_dir_err(h, l, e, err, up)
}

#[inline(never)]
fn fast_atan2_dir2(y: f64, x: f64, up: bool) -> Option<f64> {
    let (h, l, e, err) = fast_atan2_pos(y.abs(), x.abs(), x < 0.0)?;
    let r = round_dir_err(h, l, e, err, up != (y < 0.0))?;
    Some(if y < 0.0 { -r } else { r })
}

fn fast_atan_near2(x: f64) -> Option<f64> {
    let (h, l, e, err) = fast_atan_pos(x.abs())?;
    let r = round_near_err(h, l, e, err)?;
    Some(if x < 0.0 { -r } else { r })
}

fn fast_asin_near2(x: f64) -> Option<f64> {
    let (h, l, e, err) = fast_asin_pos(x.abs())?;
    let r = round_near_err(h, l, e, err)?;
    Some(if x < 0.0 { -r } else { r })
}

fn fast_acos_near2(x: f64) -> Option<f64> {
    let (h, l, e, err) = fast_acos_val(x)?;
    round_near_err(h, l, e, err)
}

fn fast_atan2_near2(y: f64, x: f64) -> Option<f64> {
    let (h, l, e, err) = fast_atan2_pos(y.abs(), x.abs(), x < 0.0)?;
    let r = round_near_err(h, l, e, err)?;
    Some(if y < 0.0 { -r } else { r })
}

// atan2(y, x) rounded to nearest by the fast path, or by `ziv_near` where it returns `None`.
fn atan2_fast_near(y: f64, x: f64) -> f64 {
    match fast_atan2_near(y, x) {
        Some(r) => r,
        None => ziv_near(&Atan2(y, x), 1),
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
    } else if let Some(r) = fast_atan_dir(x, up) {
        r
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
    } else if let Some(r) = fast_atan_near(x) {
        r
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
    } else if let Some(r) = fast_asin_dir(x, up) {
        r
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
    } else if let Some(r) = fast_asin_near(x) {
        r
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
    } else if let Some(r) = fast_acos_dir(x, up) {
        r
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
    } else if let Some(r) = fast_acos_near(x) {
        r
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
            None => match fast_atan2_dir(y, x, up) {
                Some(r) => r,
                None => ziv(&Atan2(y, x), up, 1),
            },
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
                _ => atan2_fast_near(y, x),
            },
        }
    } else {
        atan2_fast_near(y, x)
    }
}
