// The trigonometric functions sin, cos and tan with the dyadic kernel, each rounded to an `f64`
// toward +∞ if `up` and toward -∞ otherwise, and, as `sin_near` and the others, to nearest,
// ties to even, as MPFR rounds them (`src/dyadic.rs` says what `ziv` and `ziv_near` return at
// their caps). `src/mpfr_calls/kernel.rs` makes the first the `sin_rd`, `sin_ru` and the
// others that `src/elementary.rs` calls, `src/cr.rs` makes both the `sin_rn`, `sin_rd`,
// `sin_ru` and the others of `inari::cr`, and the tests on 64-bit Linux and macOS compare them
// with those of MPFR, `src/mpfr_calls/mpfr.rs`.
//
// Each function first settles some arguments by rules: NaN and ±∞, at which it is NaN, the
// arguments of magnitude below 2^-26, whose results are within an ulp of x for sin and tan and
// of 1 for cos, and some of those of magnitude in [2^-26, 2^-13) for sin and [2^-26, 2^-14)
// for cos and tan, at which the first two terms of the series and a bound on the rest put the
// result strictly between two adjacent `f64`s (`sin_small`, `cos_small` and `tan_small`), all
// as MPFR gives them. The last rules are for arguments with few bits, such as m 2^-26 for an
// integer m, at which the result can lie closer to an `f64` than the first level of `ziv`
// resolves: cos t is above the `f64` 1 - t^2 / 2 by less than t^4 / 24 there. Ziv's strategy
// cannot settle an argument whose result is an `f64` unless an enclosure has that `f64` as its
// bound in the direction of the rounding (the header of `src/dyadic/exp.rs` says why), and no
// nonzero `f64` has a sin, cos or tan that is one, as an `f64` is rational and cos r is
// irrational for every rational r other than 0, and cos 2r is 1 - 2 (sin r)^2 and
// (1 - (tan r)^2) / (1 + (tan r)^2). `ziv` computes the rest from an `Eval`. The functions
// rounded to nearest have the rules of NaN, ±∞ and of the arguments of magnitude below 2^-27
// (`TINY_NEAR`), whose results are less than half an ulp from x or 1, and `ziv_near` computes
// the rest from the same `Eval`s. They have no rules at
// small arguments, which only save levels of `ziv`. At some arguments with few bits, sin and
// tan lie close to the midpoint of two `f64`s, as the results of those rules lie close to an
// `f64`: t - t^3 / 6 is a midpoint at t = 21 2^-24, and sin t lies above it by about t^5 / 120,
// and t + t^3 / 3 is one at t = 3 2^-26. `ziv_near` settles them at a later level, as no sin,
// cos or tan of a nonzero `f64` is a midpoint, which is rational too.
//
// The evaluations take t = |x|, as sin and tan are odd and cos is even, and reduce it to
// t = k π/2 + σ ρ for an integer k >= 0, a sign σ and an enclosure of ρ (`reduce`). The
// reduction divides t 2^(s + 1) by the top limbs P of `PI`, for which
// π/2 = (P + δ) 2^-(s + 1) with δ in [0, 1), in integers: t 2^(s + 1) = k P + R with
// 0 <= R < P, so that t - k π/2 = (R - k δ) 2^-(s + 1). That holds for every k, and the
// division only makes |ρ| small: about π/4, or k + 1 and P - R in place of k and R when R is
// above P/2. Its width, k 2^-(s + 1), shrinks with the number of limbs of P, which grows with
// the level and with the exponent of t, so that ρ keeps its relative precision near the
// multiples of π/2, where it cancels, up to the 66 limbs of `PI`. The least distance from an
// `f64` to a multiple of π/2 other than 0 is about 2^-61, at 6381956970095103 2^797 (the case
// of Kahan and McDonald; J.-M. Muller, Elementary Functions, 3rd ed., the chapter on range
// reduction). `km_distance` in `rocq/theories/KahanMcDonald.v` proves that it is at least
// 2^-61, and the search of every binade for the hard cases of the tests found none closer.
//
// sin(k π/2 + σ ρ) is ±sin ρ or ±cos ρ by k mod 4 and σ (`sin_k`), and cos t = sin(t + π/2).
// The series sin ρ = Σ_{i >= 0} (-1)^i ρ^(2i + 1) / (2i + 1)! and
// cos ρ = Σ_{i >= 0} (-1)^i ρ^(2i) / (2i)! are alternating, with terms that decrease in
// magnitude for |ρ| <= 1, so Horner's scheme starts from the enclosure [0, 1] of the scaled
// remainder of the n terms that it leaves out (`series`), where n follows from the level and
// from the exponent of ρ^2 (`terms`). tan t is σ sin ρ / cos ρ for an even k and
// -σ cos ρ / sin ρ for an odd k, from one series: cos ρ = √((1 - sin ρ)(1 + sin ρ)), as
// cos ρ > 0 for |ρ| <= 1. The divisor cos ρ is positive. The divisor sin ρ is positive where
// the enclosure of ρ is, and `Encl::div` panics where it contains 0, which for an odd k needs
// the distance from t to k π/2 to be below the width of the reduction: below 2^-(64 N + 63)
// at `N` limbs, or 2^-3199 where the 66 limbs of `PI` cap it. No `f64` is that close by the
// bound above. `tan_div_pos` in `rocq/theories/DyTrigPos.v` proves, from that bound, that the
// enclosure of the divisor is above 0 at every level for either parity of k, and
// `sin_dir_sign` and `cos_dir_sign` there that `sin(x, false)` is below 0 exactly where
// sin x is, and `cos(x, true)` above 0 exactly where cos x is, wherever they return, whether
// a rounding test of `ziv` passes or not, as the enclosures of sin and cos exclude 0 at every
// level.
//
// `rocq/theories/Model.v` transcribes each function of this file except the tests and the
// scratch buffer of `reduce`, so it has to be updated along with them.
// `rocq/theories/DyTrig.v` proves that each of the three functions, at finite arguments and
// where it does not panic, returns a value on the side of its result that the rounding is on,
// and, where a rule settles the argument, the fast path below returns or a rounding test of
// `ziv` passes, its result rounded as `mpfr_round` in `rocq/theories/Mpfr.v` says. It builds on
// `rocq/theories/DyTrigReduce.v` for `reduce`, `rocq/theories/DyTrigCore.v` for `series` and
// `sin_k`, `rocq/theories/TrigSeries.v` for the bounds of the series and the identities that
// the evaluations use, `rocq/theories/DyTrigTiny.v` for the rules at tiny arguments, and
// `rocq/theories/DyTrigSmall.v`, `rocq/theories/DyCosSmall.v`, `rocq/theories/DySinSmall.v`
// and `rocq/theories/DyTanSmall.v` for those at small arguments. `rocq/theories/DyTrigNear.v`
// proves that each of the three functions rounded to nearest, at a finite argument, where a
// rule settles the argument, the fast path returns or a rounding test of `ziv_near` passes,
// returns its result rounded to nearest as `near_round` in `rocq/theories/NearF64.v` says,
// from the same enclosures and bounds and the cells of `rocq/theories/NearCells.v`.
// `rocq/theories/DyTrigExact.v` proves that each of the three functions returns its result,
// in both directions, at every finite argument at which it is an `f64`, which is only ±0,
// where the rules of tiny arguments return it, with `cos_irrational` in
// `rocq/theories/CosIrrational.v` that cos r is irrational for every rational r other than 0
// (I. Niven, Irrational Numbers, 1956, ch. 2). That no result is a midpoint is not stated in
// the proofs. Other than that, it is not proved that a test passes by the cap of `ziv` or of
// `ziv_near`, nor that the evaluations do not panic.
//
// sin, cos and tan try a fast path in double-double after their rules and before `ziv` and
// `ziv_near` (`fast_sin`, `fast_cos` and `fast_tan`), with the rounding tests for an h of either
// sign, `round_dir_signed` and `round_near_signed` of `src/dyadic/fast.rs`, after a scaling by a
// power of 2 (`fast_round_dir` and `fast_round_near`). Where a test fails, other than where
// `fast_one_dir` decides sin or cos rounded down or up (below), or the fast path declines the
// argument, the function calls `ziv` or `ziv_near` as before. The fast path
// reduces a finite x to n u + ρ for u = π/4096 and |ρ| <= u/2 (1 + 2^-24): for |x| < 2^16
// (`LIMIT`) with u in three parts as Cody and Waite do (`fast_reduce`), and for larger x as
// Payne and Hanek do [Payne-Hanek], in integers, from 192 bits of 1/(2π) in `INV2PI` picked by
// the exponent of x (`fast_reduce_big`), which gives n only modulo 8192, as 8192 u = 2π. With
// n = 2048 q + i, so that x is i u + ρ past q π/2 up to a multiple of 2π, it takes
// sin(i u + ρ) = sin(i u) cos ρ + cos(i u) sin ρ, with sin and cos of i u from the table `SC`
// (`fast_sc`) and the Taylor polynomials of cos ρ - 1 to degree 4 and of sin ρ - ρ to degree 5
// (`fast_eval`), and tan x as the quotient of the two (`fast_div`). At n = 0, which only
// `fast_reduce` returns, the Taylor polynomials of sin x and cos x themselves (`fast_sin0` and
// `fast_cos0`). At i = 0, other than at that n = 0 of `fast_reduce`, x is within
// u/2 (1 + 2^-24) of a multiple of π/2 other than 0, the band, where sin x, cos x or tan x is
// close to 0 or has a pole, and |ρ| >= 2^-61 (`km_distance`). There the fast path takes a
// reduction with rh + rl within 2^-74 |ρ| of ρ, in place of the absolute bounds of
// `fast_reduce` and `fast_reduce_big`: below `LIMIT`, `fast_band` and `fast_tan_band` refine
// that of `fast_reduce` with the exact error of n U3 and a fourth part `U4` of u
// (`fast_band_reduce`), and above it, `fast_band_big` and `fast_tan_band_big` recompute the
// window of `fast_reduce_big` and read the fraction ρ/u that it gives from its leading bit
// rather than from 2^-1 (`fast_reduce_band_big`). sin x and cos t are then ±sin ρ or ±cos ρ,
// which it evaluates by their Taylor polynomials (`fast_band_sin` and `fast_cos0`), and tan x
// is tan ρ or -1/tan ρ, from their quotient (`fast_band_tan`). Elsewhere i u + ρ lies in
// [u/2 (1 - 2^-24), π/2 - u/2 (1 - 2^-24)], where sin and cos are above 2^-12, and the error of
// the reduction is small relative to them. The fast path declines x where i != 0 and the
// computed rh is 0, or, from `fast_reduce_big`, below 2^-65 in magnitude, which the proof of
// `fast_eval` excludes, and NaN and the infinities. Where the test of sin or cos rounded down or
// up fails at h = ±1, as it does in the band where the result is ±cos ρ and |ρ| is below about
// 2^-34, `fast_one_dir` decides the rounding, as the result then lies strictly between
// 1 - 2^-53 and 1 in magnitude. The shape, a reduction by a multiple of a fraction of π, sin and
// cos of that multiple from tables and short polynomials of the remainder, is that of
// CORE-MATH's `sin` [CORE-MATH], whose fast path takes multiples of π/2^14, minimax polynomials
// and a bound on the absolute error. That fast path takes sin and cos of its multiple, mod π,
// from a row of each of two tables of 128 rows, of j π/2^7 and of j π/2^14, 4,096 bytes each,
// by the formulas for the sine and cosine of a sum, over all of [0, π), with no fold into
// [0, π/2] (sin.c notes that halving the first table by its symmetries leads to slower code).
// Here the multiple is i u past q π/2, with i in [0, 2047], and one table of 1,025 rows, of i u
// for i in [0, 1024], 32,800 bytes, gives sin and cos of i u with no such formula: the row at i
// up to 1024, and above it the row at 2048 - i with sin and cos swapped. `fast_reduce_big` has
// the shape of CORE-MATH's `reduce_large`, a window of the bits of 1/(2π) picked by the
// exponent and products of integers, with three 64-bit limbs where it takes two.
// `rocq/theories/FastTrigCore.v` bounds the error of `fast_sin`, `fast_cos` and `fast_tan`
// relative to sin x, cos t and tan x by 2^-71, 2^-71 and 3 2^-71, from
// `rocq/theories/FastTrigReduce.v` and `rocq/theories/FastTrigBig.v` for the reductions, the
// latter with `rocq/theories/FastTrigBigInt.v`, `rocq/theories/FastTrigBigMul.v`,
// `rocq/theories/FastTrigBigDec.v` and `rocq/theories/FastTrigBigSum.v`,
// `rocq/theories/FastTrigBandRed.v` and `rocq/theories/FastTrigBandBig.v` for those of the
// band, the latter with `rocq/theories/FastTrigBandInt.v` and `rocq/theories/FastTrigBandMul.v`,
// `rocq/theories/FastTrigTables.v` for `SC`, `INV`, `U1`, `U2` and `U3`,
// `rocq/theories/FastTrigSC.v`, `rocq/theories/FastTrigEval.v` and
// `rocq/theories/FastTrigDiv.v` for the steps, and `rocq/theories/FastTrigBandEval.v` and
// `rocq/theories/FastTrigBandDiv.v` for those of the band. `rocq/theories/FastTrigRound.v`
// proves the scaling and, with `rocq/theories/FastSign.v`, the tests,
// `rocq/theories/FastTrigOne.v` the rule of `fast_one_dir`, and `rocq/theories/FastTrig.v`
// that the fast path returns sin x, cos t and tan x rounded, with and without an FMA. As those
// are correct roundings, `sin_dir_sign` and `cos_dir_sign` hold where the fast path returns too.
//
// [CORE-MATH] P. Zimmermann et al., the CORE-MATH project, `src/binary64/sin/sin.c` (MIT
// license); no constant or table is copied from it.
//
// [Payne-Hanek] M. H. Payne and R. N. Hanek, "Radian reduction for trigonometric functions",
// ACM SIGNUM Newsletter 18(1), 1983, pp. 19-24.

use super::{
    consts::PI,
    exp::{away, near_one, toward_zero, TINY_HYP, TINY_NEAR},
    fast::{fast_two_sum, round_dir_signed, round_near_signed, two_sum},
    level::level_entry,
    round, ziv, ziv_near, Dyadic, Encl, Eval,
};
use crate::limbs;
use crate::simd::two_prod_err;
use sc_table::SC;
use std::cmp::Ordering;
use tables::INV2PI;

mod sc_table;
mod tables;
#[cfg(test)]
mod tests;

// 201/256 = 0.78515625, below π/4 = 0.78539...: the arguments up to it are not reduced, as
// k = 0 and ρ = t for them.
const NO_REDUCE: f64 = 0.78515625;

// The limbs of P beyond those of the level and of the integer part of t, which make the width
// of the reduction at most 2^-(64 N + 63), with 64 bits to spare for the cancellation of
// t - k π/2.
const GUARD_LIMBS: usize = 2;

// (k mod 4, σ = -1, ρ) for t = k π/2 + σ ρ and a finite t >= 0, as the header says, with
// ρ in [-1, 1]. For t > `NO_REDUCE`, t = m 2^exp for the mantissa m of one limb of
// `Dyadic::<1>::from_f64(t)`, so that t < 2^b for b = exp + 64, which is in [0, 1024] as t > 1/2.
// P is the top L = min(66, N + `GUARD_LIMBS` + floor(b / 64)) limbs of `PI`, so that
// π ∈ [P, P + 1) 2^-s for s = 64 L - 2, as `PI` is floor(π 2^4222). X = t 2^(s + 1) =
// m 2^(exp + s + 1), which is an integer below 2^(b + 64 L - 1), and so fits in the
// nx = L + 1 + floor(b / 64) limbs that it is written in. Its quotient by P is below 2^b, as
// P >= 2^(64 L - 1), so that k, the quotient or the quotient plus 1, is at most 2^b. The
// width that δ adds to ρ is k 2^-(s + 1) rounded up, at most the power of 2
// 2^(b - 64 L + 1) <= 2^-(64 N + 63) below the cap of 66 limbs, and at most 2^-3199 at it.
fn reduce<const N: usize>(t: f64) -> (u64, bool, Encl<N>) {
    if t <= NO_REDUCE {
        return (0, false, Encl::point(t));
    }
    let d = Dyadic::<1>::from_f64(t);
    let b = (d.exp + 64) as usize;
    let l = (N + GUARD_LIMBS + b / 64).min(66);
    let s = 64 * l as i64 - 2;
    let nx = l + 1 + b / 64;
    let p = &PI[66 - l..];
    // X, the quotient, R, P - R, and the scratch of `div_rem`, of nx + L + 2 limbs: on the
    // stack where they fit, as they do at every level up to 4 limbs, where the most is 185
    // limbs, at N = 4 and b = 1024, and on the heap otherwise.
    let need = 3 * nx + 3 * l + 2;
    let mut stack = [0; 192];
    let mut heap = Vec::new();
    let buf: &mut [u64] = if need <= stack.len() {
        &mut stack
    } else {
        heap.resize(need, 0);
        &mut heap
    };
    let (x, buf) = buf.split_at_mut(nx);
    let (q, buf) = buf.split_at_mut(nx);
    let (r, buf) = buf.split_at_mut(l);
    let (c, scratch) = buf.split_at_mut(l);
    // exp + s + 1 >= -64 + 64 (N + 2) - 1 > 0.
    limbs::shl_into(x, &d.m, (d.exp + s + 1) as u64);
    // X = k P + R, with R < P.
    limbs::div_rem(q, r, x, p, scratch);
    // C = P - R > 0, without a borrow.
    c.copy_from_slice(p);
    limbs::sub_assign(c, r, false);
    // R > P - R, that is, 2 R > P: take k + 1, for which t - (k + 1) π/2 = -(C + (k + 1) δ)
    // 2^-(s + 1). k + 1 <= 2^b, so the sum has no carry out of the nx limbs.
    let up = limbs::cmp(r, c) == Ordering::Greater;
    if up {
        limbs::add_assign(q, &[1]);
    }
    let e = -(s + 1);
    // An upper bound of k δ 2^-(s + 1), from δ < 1.
    let k = round::<N>(false, q, e, false, true);
    let center: &[u64] = if up { c } else { r };
    let w = Encl {
        lo: round(false, center, e, false, false),
        hi: round(false, center, e, false, true),
    };
    let kd = Encl {
        lo: Dyadic::ZERO,
        hi: k,
    };
    // ρ = (C + k δ) 2^-(s + 1) with σ = -1 if `up`, and (R - k δ) 2^-(s + 1) with σ = 1
    // otherwise.
    let rho = if up { w.add(&kd) } else { w.sub(&kd) };
    assert!(
        rho.lo >= Dyadic::from_f64(-1.0) && rho.hi <= Dyadic::from_f64(1.0),
        "reduction out of range"
    );
    (q[0] & 3, up, rho)
}

// The terms of `series` at `N` limbs for the enclosure `z` of ρ^2: 6 N + 5, or
// ceil((64 N + 4) / e) if that is fewer, for z < 2^-e. The upper bound of z is m 2^exp for a
// mantissa m of 64 N bits, so that it is below 2^(exp + 64 N), and e = -(exp + 64 N) if that
// is positive. ceil((64 N + 4) / e) makes z^n < 2^-(64 N + 4), and 6 N + 5 makes
// z^n / (2n)! < 2^-(64 N + 4) for z <= 0.62, which holds for |ρ| <= π/4 + 2^-60, at each
// level from 1 to 64 limbs.
fn terms<const N: usize>(z: &Encl<N>) -> u64 {
    let cap = 6 * N as u64 + 5;
    let bits = 64 * N as i64;
    if z.hi.exp >= -bits {
        cap
    } else {
        // -bits - exp > 0 does not overflow, as -bits < 0.
        let e = (-bits - z.hi.exp) as u64;
        // ceil((64 N + 4) / e); `div_ceil` needs Rust 1.73.
        cap.min((64 * N as u64 + 3 + e) / e)
    }
}

// sin ρ if `odd` and cos ρ otherwise, for every ρ of `r`, whose numbers have to be in
// [-1, 1], by Horner's scheme on the scaled remainders of the series, with z = ρ^2:
// S_k = (-1)^k (sin ρ - Σ_{i < k} (-1)^i ρ^(2i + 1) / (2i + 1)!) (2k + 1)! / ρ^(2k + 1) and
// C_k = (-1)^k (cos ρ - Σ_{i < k} (-1)^i ρ^(2i) / (2i)!) (2k)! / ρ^(2k), both 1 at ρ = 0.
// They satisfy S_k = 1 - z S_(k + 1) / ((2k + 2)(2k + 3)) and
// C_k = 1 - z C_(k + 1) / ((2k + 1)(2k + 2)), and sin ρ = ρ S_0 and cos ρ = C_0. Both series
// are alternating with terms that decrease in magnitude for |ρ| <= 1, so each S_k and C_k is
// in [0, 1], from which the scheme starts at k = `terms`.
fn series<const N: usize>(r: &Encl<N>, odd: bool) -> Encl<N> {
    let one = Encl::point(1.0);
    let z = r.mul(r);
    let n = terms(&z);
    let o = u64::from(odd);
    let mut t = Encl {
        lo: Dyadic::ZERO,
        hi: one.hi,
    };
    for k in (0..n).rev() {
        t = one.sub(&z.mul(&t).div_u64((2 * k + 1 + o) * (2 * k + 2 + o)));
    }
    if odd {
        r.mul(&t)
    } else {
        t
    }
}

// sin(k π/2 + σ ρ) for every ρ of `r`, whose numbers have to be in [-1, 1], k mod 4 = `quad`
// mod 4 and σ = -1 if `neg` and 1 otherwise: σ sin ρ, cos ρ, -σ sin ρ and -cos ρ for
// k mod 4 = 0, 1, 2 and 3.
fn sin_k<const N: usize>(quad: u64, neg: bool, r: &Encl<N>) -> Encl<N> {
    let (v, flip) = if quad % 2 == 0 {
        (series(r, true), neg != (quad % 4 == 2))
    } else {
        (series(r, false), quad % 4 == 3)
    };
    if flip {
        v.neg()
    } else {
        v
    }
}

// sin x, for a finite x, from sin t for t = |x|, as sin is odd.
struct Sin(f64);

impl Eval for Sin {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let (quad, neg, r) = reduce(self.0.abs());
        let v = sin_k(quad, neg, &r);
        if self.0 < 0.0 {
            v.neg()
        } else {
            v
        }
    }
}

// cos t for a finite t >= 0, as cos t = sin(t + π/2) = sin((k + 1) π/2 + σ ρ).
struct Cos(f64);

impl Eval for Cos {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let (quad, neg, r) = reduce(self.0);
        sin_k(quad + 1, neg, &r)
    }
}

// tan x, for a finite x, from tan t for t = |x|, as tan is odd: σ S / C for an even k and
// -σ C / S for an odd k, with S = sin ρ and C = √((1 - S)(1 + S)) = cos ρ.
struct Tan(f64);

impl Eval for Tan {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let (quad, neg, r) = reduce(self.0.abs());
        let one = Encl::point(1.0);
        let s = series(&r, true);
        let c = one.sub(&s).mul(&one.add(&s)).sqrt();
        let odd = quad % 2 == 1;
        let v = if odd { c.div(&s) } else { s.div(&c) };
        if (neg != odd) != (self.0 < 0.0) {
            v.neg()
        } else {
            v
        }
    }
}

// m^3 = h 2^64 + l as (h, l), for m < 2^53, as m^3 has up to 159 bits: m^2 < 2^106 splits at
// bit 64, and each part times m fits in a `u128`.
fn cube(m: u128) -> (u128, u64) {
    let sq = m * m;
    let lo = u128::from(sq as u64) * m;
    ((sq >> 64) * m + (lo >> 64), lo as u64)
}

// cos t rounded toward +∞ if `up` and toward -∞ otherwise, for a t in [2^-26, 2^-14) at which
// 1 - t^2 / 2 and a bound on the rest of the series put cos t strictly between two adjacent
// `f64`s, as below, and `None` otherwise. t = m 2^(be - 1075) for the biased
// exponent `be` of t, in 997..=1008 there, and m in [2^52, 2^53). Then
// t^2 / 2 = m^2 2^-(s + 53) = (k + r 2^-s) 2^-53 exactly, for s = 2098 - 2 be in [82, 104],
// k = m^2 >> s, at least 1, and r = m^2 mod 2^s. The series puts cos t in
// (1 - t^2 / 2, 1 - t^2 / 2 + t^4 / 24], and t^4 / 24 < 2^(4 E + 4) / 24 < 2^(104 - 2 s),
// with E = be - 1023 = 26 - s / 2, as t < 2^(E + 1). If r = 0, 1 - t^2 / 2 is the `f64`
// 1 - k 2^-53, and cos t lies above it by less than 2^-53, as s >= 82. If r >= 2^(157 - s),
// 1 - t^2 / 2 lies strictly between the `f64`s 1 - (k + 1) 2^-53 and 1 - k 2^-53, at least
// 2^(104 - 2 s) below the second, more than t^4 / 24, so that cos t lies between them too.
// In both cases cos t lies strictly between 1 - j 2^-53 and the next `f64`, for
// j = k + (r != 0), as their bits are those of 1 minus j and that plus 1.
fn cos_small(t: f64, up: bool) -> Option<f64> {
    let b = t.to_bits();
    let be = b >> 52;
    if !(997..=1008).contains(&be) {
        return None;
    }
    let m = u128::from((b & ((1 << 52) - 1)) | 1 << 52);
    let s = 2098 - 2 * be;
    let sq = m * m;
    let k = sq >> s;
    let r = sq & ((1u128 << s) - 1);
    if r != 0 && r >> (157 - s) == 0 {
        return None;
    }
    let j = k as u64 + u64::from(r != 0);
    Some(f64::from_bits(1.0f64.to_bits() - j + u64::from(up)))
}

// sin x rounded toward +∞ if `up` and toward -∞ otherwise, for an |x| in [2^-26, 2^-13) at
// which t - t^3 / 6, for t = |x|, and a bound on the rest of the series put sin t strictly
// between two adjacent `f64`s of the binade of t, as below, and `None` otherwise. For t = m g,
// with g = 2^(be - 1075) the ulp of t as in `cos_small`, `be` in 997..=1009 there, and
// N = m^3 = h 2^64 + l (`cube`), t^3 / 6 = c g with c = N / D, D = 6 2^(s + 64) and
// s = 2086 - 2 be in [68, 92]. The series puts sin t in (t - c g, t - (c - w) g], with
// w = t^5 / (120 g) < 2^(4 E + 57) / 120 < 2^(64 + d) / D, for E = be - 1023 and
// d = 2 be - 1953 in [41, 65]. j = floor((N - 1) / D), computed from the floor of
// (N - 1) / 2^64, which is h if l > 0 and h - 1 if l = 0, is the integer below c and at least
// c - 1. It equals floor((N - 2^(64 + d)) / D) exactly when j <= c - 2^(64 + d) / D, and
// then j < c - w < c <= j + 1, so sin t lies strictly between t - (j + 1) g and t - j g.
// They are the `f64`s whose bits are those of t minus j + 1, and those plus 1, if the stored
// significand f of t is above j, so that the first is in the binade of t. sin is odd, so the
// rounding of sin x for x < 0 is minus that of sin t in the other direction.
fn sin_small(x: f64, up: bool) -> Option<f64> {
    let b = x.abs().to_bits();
    let be = b >> 52;
    if !(997..=1009).contains(&be) {
        return None;
    }
    let f = b & ((1 << 52) - 1);
    let (h, l) = cube(u128::from(f | 1 << 52));
    let s = 2086 - 2 * be;
    let j = ((h - u128::from(l == 0)) >> s) / 6;
    if ((h - (1u128 << (2 * be - 1953))) >> s) / 6 != j || u128::from(f) <= j {
        return None;
    }
    let neg = x < 0.0;
    let v = f64::from_bits(b - (j as u64 + 1) + u64::from(up != neg));
    Some(if neg { -v } else { v })
}

// tan x rounded toward +∞ if `up` and toward -∞ otherwise, for an |x| in [2^-26, 2^-14) at
// which t + t^3 / 3, for t = |x|, and a bound on the rest put tan t strictly between two
// adjacent `f64`s, as below, and `None` otherwise. With g, `be`, in
// 997..=1008 there, N, s and E as in `sin_small`, t^3 / 3 = c g with c = N / D and
// D = 3 2^(s + 64). The series of sin and cos put tan t in (t + c g, t + (c + w) g) with
// w = t^5 / (4 g) < 2^(4 E + 55) < 2^(64 + d) / D, for d = 2 be - 1949 in [45, 67].
// j = floor(N / D) equals floor((N + 2^(64 + d)) / D) exactly when
// c + 2^(64 + d) / D < j + 1, and then j <= c < c + w < j + 1, so tan t lies strictly between
// t + j g and t + (j + 1) g. They are the `f64`s whose bits are those of t plus j, and those
// plus 1, if f + j < 2^52 for the stored significand f of t, so that the first is in the
// binade of t. tan is odd, as sin is.
fn tan_small(x: f64, up: bool) -> Option<f64> {
    let b = x.abs().to_bits();
    let be = b >> 52;
    if !(997..=1008).contains(&be) {
        return None;
    }
    let f = b & ((1 << 52) - 1);
    let (h, _) = cube(u128::from(f | 1 << 52));
    let s = 2086 - 2 * be;
    let j = (h >> s) / 3;
    if ((h + (1u128 << (2 * be - 1949))) >> s) / 3 != j || u128::from(f) + j >= 1 << 52 {
        return None;
    }
    let neg = x < 0.0;
    let v = f64::from_bits(b + j as u64 + u64::from(up != neg));
    Some(if neg { -v } else { v })
}

// The constants of the fast path, as the bits of `f64`s, since `f64::from_bits` is not `const`
// before Rust 1.83. u = π/4096; `INV` = RN(1 / u); `U1` is u with its significand cut to 26
// bits (25 significant bits, as the 26th is 0), so that n U1 is exact for |n| < 2^27, `U2` is
// u - U1 cut to 26 bits (24 significant bits), so that n U2 is exact too, and
// `U3` = RN(u - U1 - U2), with |u - U1 - U2 - U3| < 2^-120, and `U4` = RN(u - U1 - U2 - U3),
// with |u - U1 - U2 - U3 - U4| < 2^-174, which only `fast_band_reduce` takes. `S3` = RN(1/6),
// `S5` = RN(1/120) and `C4` = RN(1/24). `rocq/theories/FastTrigTables.v` proves that `INV` u is
// within 2^-52 of 1 and U1 + U2 + U3 within 2^-119 of u (`fast_trig_consts`), and
// `rocq/theories/FastTrigBandRed.v` that |U4| <= 2^-120 and U1 + U2 + U3 + U4 within 2^-174 of u
// (`band_consts`).
const INV: u64 = 0x40945f306dc9c883;
const U1: u64 = 0x3f4921fb50000000;
const U2: u64 = 0x3da110b460000000;
const U3: u64 = 0x3be1a62633145c07;
const U4: u64 = 0xb86f1976b7ed8fbc;
const S3: u64 = 0x3fc5555555555555;
const S5: u64 = 0x3f81111111111111;
const C4: u64 = 0x3fa5555555555555;

// 1.5 * 2^52: for |t| < 2^51, (t + SHIFTER) - SHIFTER is t rounded to an integer.
const SHIFTER: f64 = 6_755_399_441_055_744.0;

// 2^16: `fast_reduce` reduces |x| < LIMIT, and `fast_reduce_big` the others.
const LIMIT: f64 = 65_536.0;

// (n, rh, rl, rr) with x = n u + ρ, |ρ| <= u/2 (1 + 2^-24), |ρ - (rh + rl)| <= 2^-90 and
// rr = RN(rh + rl), for |x| < `LIMIT`, and `None` for any other x, NaN included.
// `rocq/theories/FastTrigReduce.v` proves these bounds (`fast_reduce_correct`).
fn fast_reduce(x: f64) -> Option<(i64, f64, f64, f64)> {
    if x.is_nan() || x.abs() >= LIMIT {
        return None;
    }
    // n is x / u rounded to an integer up to the roundings of `INV` and of the product, and
    // |n| < 2^27: |x INV| < 2^51, so adding and subtracting `SHIFTER` rounds RN(x INV) to an
    // integer, within 1/2 of it.
    let ks = x * f64::from_bits(INV) + SHIFTER;
    let kf = ks - SHIFTER;
    // rh = x - n U1 - n U2 exactly: both products are exact, and so are both differences. At
    // n = 0 they subtract 0. Elsewhere |x| > 2^-12, so that x, n U1 and n U2 are multiples of
    // 2^g, the smaller of the quantum of x and 2^-60, and both differences are below 2^-7 and
    // below 2^(k + 1) for 2^k <= |x| < 2^(k + 1), so below 2^(g + 53) in magnitude. rl is
    // -n U3 rounded once.
    let (u1, u2) = (f64::from_bits(U1), f64::from_bits(U2));
    let rh = (x - kf * u1) - kf * u2;
    let rl = -(kf * f64::from_bits(U3));
    // ks is the integer SHIFTER + n, so its low 32 bits are n.
    Some((ks.to_bits() as i32 as i64, rh, rl, rh + rl))
}

// (ah + al) (bh + bl) as p + e, with p = RN(ah bh), from the exact error of that product
// [Dekker] and the cross products. al bl is left out.
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_mul<const FMA: bool>(ah: f64, al: f64, bh: f64, bl: f64) -> (f64, f64) {
    let p = ah * bh;
    (p, two_prod_err::<FMA>(ah, bh, p) + (ah * bl + al * bh))
}

// (n, rh, rl, rr) for a finite x with |x| >= `LIMIT`, as `fast_reduce` gives them below it, but
// with x = N u + ρ for an integer N and n = N mod 8192, in [0, 8191], which is all that
// `fast_quad` and `fast_tan` read of an n other than 0, as 8192 u = 2π: a reduction of Payne
// and Hanek [Payne-Hanek], in integers, by the bits of 1/(2π) in `INV2PI`. `None` for any other
// x, NaN included, where n mod 2048 = 0, which `fast_reduce_band_big` reduces, and where
// |rh| < 2^-65.
// `rocq/theories/FastTrigBig.v` proves these bounds (`fast_reduce_big_correct`).
// Always inlined, into `fast_reduce_any`, whose comment gives the count of the two attributes.
#[inline(always)]
fn fast_reduce_big<const FMA: bool>(x: f64) -> Option<(i64, f64, f64, f64)> {
    // |x| = m 2^e, with m in [2^52, 2^53) and e = be - 1075 for the biased exponent be, which
    // is in [1039, 2046] for a finite |x| >= 2^16.
    let b = x.to_bits() & (u64::MAX >> 1);
    let be = b >> 52;
    if !(1039..=2046).contains(&be) {
        return None;
    }
    let m = (b & ((1 << 52) - 1)) | (1 << 52);
    // |x| / (2π) = m 2^e / (2π): the bits of 1/(2π) down to 2^-e give an integer times m,
    // which only adds multiples of 2π to x, and those below 2^-(e + 192) give less than
    // m 2^-192 < 2^-139. The 192 bits between, read as an integer W, start at bit k = e + 64
    // from the top of `INV2PI`: limb k / 64, shifted left by f = k mod 64. `>> 1 >> (63 - f)`
    // is `>> (64 - f)`, which is not defined at f = 0. w(0) is the top limb of W.
    let k = (be - 1011) as usize;
    let (i, f) = (k >> 6, k & 63);
    let w = |j: usize| (INV2PI[i + j] << f) | ((INV2PI[i + j + 1] >> 1) >> (63 - f));
    // R = m W mod 2^192 = r2 2^128 + r1 2^64 + r0 from the three products; r0 is only the low
    // half of m w(2), whose high half carries into r1 and r2.
    let p0 = u128::from(m) * u128::from(w(2));
    let p1 = u128::from(m) * u128::from(w(1));
    let c = (p0 >> 64) + (p1 & u128::from(u64::MAX));
    let r1 = c as u64;
    let r2 = m
        .wrapping_mul(w(0))
        .wrapping_add((p1 >> 64) as u64)
        .wrapping_add((c >> 64) as u64);
    // |x| / u = 8192 |x| / (2π) is R 2^-179 up to a multiple of 8192 and less than 2^-126: n is
    // R 2^-179 rounded to an integer, ties up, mod 8192, from r2 alone, as the bits below it
    // cannot carry into the sum, and F = R 2^-179 - that integer, in [-1/2, 1/2), is the rest.
    let n = (r2.wrapping_add(1 << 50) >> 51) as i64;
    if n & 2047 == 0 {
        return None;
    }
    // a is the 64 bits of R below those of n, F 2^64 rounded down, as an `i64`, which is
    // negative where F is. fh = (a >> 11) 2^-53 and fl, the next 53 bits of R times 2^-106, are
    // exact, and F - fh - fl is in [0, 2^-106).
    let a = ((r2 << 13) | (r1 >> 51)) as i64;
    let fh = (a >> 11) as f64 * f64::from_bits(0x3ca0000000000000);
    let fl = ((r1 >> 9) & ((1 << 53) - 1)) as i64 as f64 * f64::from_bits(0x3950000000000000);
    // For x < 0, x = (-N) u - ρ.
    let (n, fh, fl) = if x < 0.0 {
        ((-n) & 8191, -fh, -fl)
    } else {
        (n, fh, fl)
    };
    // ρ is (fh + fl) u, which `fast_mul` computes with (U1 + U2) + U3, within 2^-119 of u, in
    // place of u. U1 + U2 is exact: U1 is a multiple of 2^-35 below 2^-10, and U2 a multiple of
    // 2^-60 below 2^-35.
    let uh = f64::from_bits(U1) + f64::from_bits(U2);
    let (rh, rl) = fast_mul::<FMA>(fh, fl, uh, f64::from_bits(U3));
    if rh.abs() < f64::from_bits(0x3be0000000000000) {
        return None;
    }
    Some((n, rh, rl, rh + rl))
}

// The reduction of `fast_reduce` for |x| < `LIMIT` and of `fast_reduce_big` for the others.
// As `fast_reduce_big` never gives an n with n mod 2048 = 0, n = 0 comes only from
// `fast_reduce`, where |x| <= u/2 (1 + 2^-24), as `fast_sin`, `fast_cos` and `fast_tan` take it.
// `rocq/theories/FastTrigBig.v` proves it (`fast_reduce_any_correct`).
// Always inlined, as is `fast_reduce_big`. This was `fast_reduce(x).or_else(||
// fast_reduce_big(x))` with neither attribute, which LLVM kept out of line with the two inlined
// into it. With the `match` and both attributes, `sin`, `cos` and `tan` take 13 to 25, 18 to 38
// and 19 to 24 fewer instructions per call, in each rounding, over 4,096 calls on each of five
// sets of arguments: uniform in [0.1, 10) and [-10, 10), of either sign with a magnitude
// log-uniform in [2^-30, 2^1024) and in [2^60, 2^1024), and the function's hard cases in
// `src/cr/tests/mpfr/hard_cases.wc`, taken in turn, in a crate that links `cr` (cachegrind,
// row 121). With
// `or_else` and both attributes, `Option::or_else` stayed out of line, and in the release build
// of the tests the three took 24 to 31 more instructions per call on the first two sets than
// with neither attribute.
#[inline(always)]
fn fast_reduce_any<const FMA: bool>(x: f64) -> Option<(i64, f64, f64, f64)> {
    match fast_reduce(x) {
        Some(r) => Some(r),
        None => fast_reduce_big::<FMA>(x),
    }
}

// (n, rh, rl, rr) for a finite x with |x| >= `LIMIT` and n mod 2048 = 0, where
// `fast_reduce_big` declines x, with x = N u + ρ for an integer N, n = N mod 8192, rr =
// RN(rh + rl) and rh + rl within 2^-74 |ρ| of ρ, and `None` for any other x, NaN included.
// N mod 2048 = 0 and N != 0 put x within u/2 (1 + 2^-24) of a multiple of π/2 other than 0, and
// |ρ| >= 2^-61 there (`km_distance` in `rocq/theories/KahanMcDonald.v`), so that the 2^-126 of
// the window of `fast_reduce_big`, in units of u, is at most 2^-75.3 |ρ|. The steps up to n are
// those of `fast_reduce_big`, and so are their integers. F, R 2^-179 less the integer nearest it
// as in `fast_reduce_big`, is then read from the first bit after its sign rather than from 2^-1:
// 106 of the 128 bits of R below those of n. The last 13 of those 128 come from the low limb r0
// of R, which `fast_reduce_big` does not read. `rocq/theories/FastTrigBandBig.v` proves these
// bounds (`fast_reduce_band_big_correct`).
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_reduce_band_big<const FMA: bool>(x: f64) -> Option<(i64, f64, f64, f64)> {
    let b = x.to_bits() & (u64::MAX >> 1);
    let be = b >> 52;
    if !(1039..=2046).contains(&be) {
        return None;
    }
    let m = (b & ((1 << 52) - 1)) | (1 << 52);
    let k = (be - 1011) as usize;
    let (i, f) = (k >> 6, k & 63);
    let w = |j: usize| (INV2PI[i + j] << f) | ((INV2PI[i + j + 1] >> 1) >> (63 - f));
    let p0 = u128::from(m) * u128::from(w(2));
    let p1 = u128::from(m) * u128::from(w(1));
    let c = (p0 >> 64) + (p1 & u128::from(u64::MAX));
    let r1 = c as u64;
    let r2 = m
        .wrapping_mul(w(0))
        .wrapping_add((p1 >> 64) as u64)
        .wrapping_add((c >> 64) as u64);
    let n = (r2.wrapping_add(1 << 50) >> 51) as i64;
    if n & 2047 != 0 {
        return None;
    }
    // a 2^64 + lo = A, the 128 bits of R below those of n, F 2^128 rounded down, with a an `i64`,
    // as in `fast_reduce_big`, and lo the next 64 bits, from r1 and r0, the low half of m w(2).
    // s is the number of bits below the sign bit of a that repeat it, at most 49, as
    // |F| >= 2^-61/u > 2^-50.7 gives |a| > 2^13. t 2^64 + v = A 2^s, with 2^62 <= |t| <= 2^63;
    // `>> 1 >> (63 - s)` is `>> (64 - s)`, which is not defined at s = 0.
    let a = ((r2 << 13) | (r1 >> 51)) as i64;
    let lo = (r1 << 13) | ((p0 as u64) >> 51);
    let s = (a ^ (a >> 63)).leading_zeros() - 1;
    let t = (a << s) | (((lo >> 1) >> (63 - s)) as i64);
    let v = lo << s;
    // fh = (t >> 11) 2^(-53 - s) and fl, the next 53 bits of t 2^64 + v times 2^(-106 - s), are
    // exact, and F - fh - fl is in [0, 2^(-106 - s) + 2^-128), at most 2^-104 |F| + 2^-128.
    let fh = (t >> 11) as f64 * f64::from_bits(u64::from(970 - s) << 52);
    let fl =
        ((((t & 2047) as u64) << 42) | (v >> 22)) as f64 * f64::from_bits(u64::from(917 - s) << 52);
    let (n, fh, fl) = if x < 0.0 {
        ((-n) & 8191, -fh, -fl)
    } else {
        (n, fh, fl)
    };
    let uh = f64::from_bits(U1) + f64::from_bits(U2);
    let (rh, rl) = fast_mul::<FMA>(fh, fl, uh, f64::from_bits(U3));
    Some((n, rh, rl, rh + rl))
}

// (sh, sl, ch, cl) with sh + sl and ch + cl sin and cos of i u, for i in [1, 2047], from the
// row of `SC` at i for i <= 1024, and above it from the row at 2048 - i with its halves
// swapped, as sin(i u) = cos((2048 - i) u) and cos(i u) = sin((2048 - i) u) with 2048 u = π/2.
// `rocq/theories/FastTrigSC.v` proves that they are within 2^-88 of sin(i u) and cos(i u)
// relative to them (`fast_sc_correct`).
// The row is read in one arm per side of 1024 rather than at the one index 1024 - |1024 - i|:
// with that index, the release build of the tests for x86-64 with haswell kept a bounds check
// there, and with it `sin` and `cos` saved registers before their first tests, about 4 more
// instructions per call when rounding down or up on arguments of magnitude next to 2^-26
// (cachegrind, row 119). With the two arms, that build and the library built for the same
// target read the row without a branch or a bounds check.
// Always inlined: out of line, `sin` and `cos` took 23 to 27 more instructions per call and
// `tan` 12 to 13 more, when this was a product of two rows, on each of five sets of 4,096
// arguments: uniform in [0.1, 10), [-10, 10) and [-π/4, π/4), and of either sign with a
// magnitude log-uniform in [2^-30, 2^1024) and in [2^60, 2^1024) (cachegrind, row 107).
#[inline(always)]
fn fast_sc(i: i64) -> (f64, f64, f64, f64) {
    let r = if i > 1024 {
        &SC[(2048 - i) as usize]
    } else {
        &SC[i as usize]
    };
    // The halves are picked by index, k = 2 above 1024, so that the swap needs no branch.
    let k = if i > 1024 { 2 } else { 0 };
    (
        f64::from_bits(r[k]),
        f64::from_bits(r[k + 1]),
        f64::from_bits(r[2 - k]),
        f64::from_bits(r[3 - k]),
    )
}

// sin(j u + ρ) = S cos ρ + C sin ρ as h + l, h = RN(h + l), for S = sh + sl and C = ch + cl
// near sin(j u) and cos(j u), j in [1, 2047], and ρ near rh + rl, rr = RN(rh + rl). The
// Taylor polynomials of cos ρ - 1 to degree 4 and of sin ρ - ρ to degree 5 are evaluated in
// plain `f64` from rr, and C ρ in double-double. `rocq/theories/FastTrigEval.v` bounds the
// error (`fast_eval_correct`).
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_eval<const FMA: bool>(
    sh: f64,
    sl: f64,
    ch: f64,
    cl: f64,
    rh: f64,
    rl: f64,
    rr: f64,
) -> (f64, f64) {
    // ch rh exactly [Dekker], and ch rl + cl rr, which leaves out cl (rh + rl - rr).
    let a = ch * rh;
    let ae = two_prod_err::<FMA>(ch, rh, a) + (ch * rl + cl * rr);
    let z = rr * rr;
    let cm = z * (z * f64::from_bits(C4) - 0.5);
    let s3 = rr * z * (z * f64::from_bits(S5) - f64::from_bits(S3));
    // S + C rh is the largest part, and |C rh| < S: see `fast_two_sum`.
    let (h, t) = fast_two_sum(sh, a);
    let l = t + (((sl + ae) + sh * cm) + ch * s3);
    fast_two_sum(h, l)
}

// sin x as h + l, h = RN(h + l), for 2^-27 <= |x| <= u/2 (1 + 2^-24), by the Taylor polynomial
// of degree 5. `rocq/theories/FastTrigEval.v` bounds the error (`fast_sin0_correct`).
fn fast_sin0(x: f64) -> (f64, f64) {
    let z = x * x;
    fast_two_sum(x, x * z * (z * f64::from_bits(S5) - f64::from_bits(S3)))
}

// cos x as h + l, h = RN(h + l), for |x| <= u/2 (1 + 2^-24), by the Taylor polynomial of
// degree 4. `rocq/theories/FastTrigEval.v` bounds the error for 2^-27 <= |x|, the x that the
// rules leave (`fast_cos0_correct`), and `rocq/theories/FastTrigBandEval.v` the error relative
// to cos ρ at x = rr for ρ, rh, rl and rr as in `fast_band_sin` (`band_cos_correct`), which
// `fast_band_eval` and `fast_band_tan` take.
fn fast_cos0(x: f64) -> (f64, f64) {
    let z = x * x;
    fast_two_sum(1.0, z * (z * f64::from_bits(C4) - 0.5))
}

// (sh, sl, sr) with ρ = x - n u within 2^-74 |ρ| of sh + sl and sr = RN(sh + sl), from the
// reduction (n, rh, rl, rr) of `fast_reduce` at an x with n mod 2048 = 0 and n != 0, where
// |ρ| >= 2^-61 (`km_distance`), but rh + rl is only within 2^-90 of ρ. rh = x - n U1 - n U2 is
// exact there, and so is n as an `f64`, as |n| < 2^27, so that
// ρ = rh - n U3 - n U4 - n (u - U1 - U2 - U3 - U4). rl = -RN(n U3); pl, the error of that
// product, is exact [Dekker], and so is the error e of RN(rh + rl) [Knuth], so that only n U4,
// the two sums of the tail and n (u - U1 - U2 - U3 - U4) are not, less than 2^-143 + 2^-105 |ρ|
// together.
// `rocq/theories/FastTrigBandRed.v` proves the bound (`fast_band_reduce_correct`).
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_band_reduce<const FMA: bool>(n: i64, rh: f64, rl: f64) -> (f64, f64, f64) {
    let kf = n as f64;
    let pl = two_prod_err::<FMA>(kf, f64::from_bits(U3), -rl);
    let (s, e) = two_sum(rh, rl);
    let t = e - (pl + kf * f64::from_bits(U4));
    (s, t, s + t)
}

// sin ρ as h + l, h = RN(h + l), for 2^-61 <= |ρ| <= u/2 (1 + 2^-24) within 2^-74 |ρ| of
// rh + rl, rr = RN(rh + rl) and |rl| <= 2^-24 |rh|, by the Taylor polynomial of degree 5, as
// `fast_sin0` at a double-double. `rocq/theories/FastTrigBandEval.v` bounds the error
// (`band_sin_correct`).
fn fast_band_sin(rh: f64, rl: f64, rr: f64) -> (f64, f64) {
    let z = rr * rr;
    fast_two_sum(
        rh,
        rl + rr * z * (z * f64::from_bits(S5) - f64::from_bits(S3)),
    )
}

// sin(q π/2 + ρ) as h + l, h = RN(h + l), for ρ as in `fast_band_sin`: ±sin ρ at an even q and
// ±cos ρ at an odd one, from `fast_band_sin` and `fast_cos0`. `rocq/theories/FastTrigBandEval.v`
// bounds the error (`band_eval_correct`).
fn fast_band_eval(q: i64, rh: f64, rl: f64, rr: f64) -> (f64, f64) {
    let (h, l) = if q & 1 == 0 {
        fast_band_sin(rh, rl, rr)
    } else {
        fast_cos0(rr)
    };
    if q & 2 == 0 {
        (h, l)
    } else {
        (-h, -l)
    }
}

// sin(x + s π/2) as h + l, from the reduction (n, rh, rl, rr) of `fast_reduce` at an x with
// n mod 2048 = 0 and n != 0: x is within u/2 (1 + 2^-24) of n u = (n / 2048) π/2. Out of line,
// as `fast_quad` is inlined into both copies of `sin_dir` and of `cos_dir` and into `sin_near`
// and `cos_near`, and only these x take it.
#[inline(never)]
fn fast_band<const FMA: bool>(n: i64, s: i64, rh: f64, rl: f64) -> (f64, f64) {
    let (rh, rl, rr) = fast_band_reduce::<FMA>(n, rh, rl);
    fast_band_eval((n >> 11) + s, rh, rl, rr)
}

// sin(x + s π/2) as h + l, as `fast_band`, for the x where `fast_reduce_big` declines x as
// n mod 2048 = 0, from the reduction of `fast_reduce_band_big`, and `None` at any other x, such
// as those where it declines x as |rh| < 2^-65, NaN and the infinities. Out of line, as
// `fast_band`.
#[inline(never)]
fn fast_band_big<const FMA: bool>(x: f64, s: i64) -> Option<(f64, f64)> {
    let (n, rh, rl, rr) = fast_reduce_band_big::<FMA>(x)?;
    Some(fast_band_eval((n >> 11) + s, rh, rl, rr))
}

// sin(x + s π/2) as h + l, from the reduction (n, rh, rl, rr) of x with n != 0, and `None`
// where rh = 0 and i = n mod 2048 is not 0. With n = 2048 q + i, x + s π/2 =
// (q + s) π/2 + i u + ρ, and sin(i u + ρ) and cos(i u + ρ) = sin((2048 - i) u - ρ) are both
// `fast_eval` with j in [1, 2047]. At i = 0, which only `fast_reduce` gives, the result can be
// near 0, and `fast_band` takes x.
// Always inlined: out of line, `sin` and `cos` took 8 to 18 more instructions per call on the
// same arguments as `fast_sc` (cachegrind, row 107).
#[inline(always)]
fn fast_quad<const FMA: bool>(n: i64, s: i64, rh: f64, rl: f64, rr: f64) -> Option<(f64, f64)> {
    let i = n & 2047;
    if i == 0 {
        return Some(fast_band::<FMA>(n, s, rh, rl));
    }
    if rh == 0.0 {
        return None;
    }
    let q = (n >> 11) + s;
    let (sh, sl, ch, cl) = fast_sc(i);
    let (h, l) = if q & 1 == 0 {
        fast_eval::<FMA>(sh, sl, ch, cl, rh, rl, rr)
    } else {
        fast_eval::<FMA>(ch, cl, sh, sl, -rh, -rl, -rr)
    };
    Some(if q & 2 == 0 { (h, l) } else { (-h, -l) })
}

// sin x as h + l, h = RN(h + l), within 2^-71 |sin x| of it, for a finite x with 2^-27 <= |x|,
// or `None`. `rocq/theories/FastTrigCore.v` proves the bound (`fast_sin_correct`).
// Always inlined, as `fast_sin_dir`: LLVM stopped inlining `fast_sin` and `fast_cos` into
// `sin`, `sin_near`, `cos` and `cos_near` when the band calls were added, and out of line they
// cost 15 to 21 more instructions per call on the same arguments as `fast_sc` (cachegrind, row
// 107).
#[inline(always)]
fn fast_sin<const FMA: bool>(x: f64) -> Option<(f64, f64)> {
    let (n, rh, rl, rr) = match fast_reduce_any::<FMA>(x) {
        Some(r) => r,
        None => return fast_band_big::<FMA>(x, 0),
    };
    if n == 0 {
        Some(fast_sin0(x))
    } else {
        fast_quad::<FMA>(n, 0, rh, rl, rr)
    }
}

// cos t as h + l, as `fast_sin` does sin x, for t = |x| (`fast_cos_correct`).
#[inline(always)]
fn fast_cos<const FMA: bool>(t: f64) -> Option<(f64, f64)> {
    let (n, rh, rl, rr) = match fast_reduce_any::<FMA>(t) {
        Some(r) => r,
        None => return fast_band_big::<FMA>(t, 1),
    };
    if n == 0 {
        Some(fast_cos0(t))
    } else {
        fast_quad::<FMA>(n, 1, rh, rl, rr)
    }
}

// (nh + nl) / (dh + dl) as h + l, h = RN(h + l): qh = RN(nh / dh), and the remainder
// nh - qh dh exactly [Dekker], with nl - qh dl, divided by dh. `rocq/theories/FastTrigDiv.v`
// bounds the error (`fast_div_correct`).
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_div<const FMA: bool>(nh: f64, nl: f64, dh: f64, dl: f64) -> (f64, f64) {
    let qh = nh / dh;
    let p = qh * dh;
    let pe = two_prod_err::<FMA>(qh, dh, p);
    fast_two_sum(qh, (((nh - p) - pe) + (nl - qh * dl)) / dh)
}

// tan(n u + ρ) = tan ρ at an even q = n / 2048 and -1 / tan ρ at an odd one, as h + l,
// h = RN(h + l), for n mod 2048 = 0 and ρ as in `fast_band_sin`: the quotient of sin ρ and
// cos ρ from `fast_band_sin` and `fast_cos0`. `rocq/theories/FastTrigBandEval.v` bounds the
// error (`band_tan_correct`).
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_band_tan<const FMA: bool>(n: i64, rh: f64, rl: f64, rr: f64) -> (f64, f64) {
    let ((sh, sl), (ch, cl)) = (fast_band_sin(rh, rl, rr), fast_cos0(rr));
    if n & 2048 == 0 {
        fast_div::<FMA>(sh, sl, ch, cl)
    } else {
        let (h, l) = fast_div::<FMA>(ch, cl, sh, sl);
        (-h, -l)
    }
}

// tan x as h + l, as `fast_band` does sin x, from the reduction (n, rh, rl, rr) of
// `fast_reduce` at an x with n mod 2048 = 0 and n != 0. Out of line, as `fast_band`.
#[inline(never)]
fn fast_tan_band<const FMA: bool>(n: i64, rh: f64, rl: f64) -> (f64, f64) {
    let (rh, rl, rr) = fast_band_reduce::<FMA>(n, rh, rl);
    fast_band_tan::<FMA>(n, rh, rl, rr)
}

// tan x as h + l, as `fast_band_big` does sin x. Out of line, as `fast_band`.
#[inline(never)]
fn fast_tan_band_big<const FMA: bool>(x: f64) -> Option<(f64, f64)> {
    let (n, rh, rl, rr) = fast_reduce_band_big::<FMA>(x)?;
    Some(fast_band_tan::<FMA>(n, rh, rl, rr))
}

// tan x as h + l, as `fast_sin` does sin x: sin and cos from the same reduction and `fast_sc`,
// and their quotient, tan(i u + ρ) at an even q and -1 / tan(i u + ρ) at an odd one, within
// 3 2^-71 |tan x| of tan x (`fast_tan_correct` in `rocq/theories/FastTrigCore.v`).
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_tan<const FMA: bool>(x: f64) -> Option<(f64, f64)> {
    let (n, rh, rl, rr) = match fast_reduce_any::<FMA>(x) {
        Some(r) => r,
        None => return fast_tan_band_big::<FMA>(x),
    };
    if n == 0 {
        let ((sh, sl), (ch, cl)) = (fast_sin0(x), fast_cos0(x));
        return Some(fast_div::<FMA>(sh, sl, ch, cl));
    }
    let i = n & 2047;
    if i == 0 {
        return Some(fast_tan_band::<FMA>(n, rh, rl));
    }
    if rh == 0.0 {
        return None;
    }
    let (sh, sl, ch, cl) = fast_sc(i);
    let (s, c) = (
        fast_eval::<FMA>(sh, sl, ch, cl, rh, rl, rr),
        fast_eval::<FMA>(ch, cl, sh, sl, -rh, -rl, -rr),
    );
    Some(if n & 2048 == 0 {
        fast_div::<FMA>(s.0, s.1, c.0, c.1)
    } else {
        let (h, l) = fast_div::<FMA>(c.0, c.1, s.0, s.1);
        (-h, -l)
    })
}

// (h 2^-e, l 2^-e, e) with 2^e <= |h| < 2^(e + 1), for h = RN(h + l) and 2^-1022 <= |h| <
// 2^1023 of either sign, where l 2^-e is rounded if it is below 2^-1022 in magnitude: the
// scaled pair that the rounding tests of `src/dyadic/fast.rs` take, whose |h| lies in [1, 2).
// The mask drops the sign bit, so that e is the exponent of |h|.
fn fast_unscale(h: f64, l: f64) -> (f64, f64, i64) {
    let e = ((h.to_bits() >> 52) & 0x7ff) as i64 - 1023;
    let s = f64::from_bits(((1023 - e) as u64) << 52);
    (h * s, l * s, e)
}

// The rounding of y toward +∞ if `up` and toward -∞ otherwise, for h = RN(h + l) with
// 2^-1000 <= |h| <= 2^1000, as the fast paths give it, and h + l within 3 2^-71 |y| of y, or
// `None` where the test of `round_dir_signed`, which takes the sign, fails.
fn fast_round_dir(h: f64, l: f64, up: bool) -> Option<f64> {
    let (h, l, e) = fast_unscale(h, l);
    round_dir_signed(h, l, e, up)
}

// The rounding of y to nearest, as `fast_round_dir`. `rocq/theories/FastTrigRound.v` proves
// both (`fast_round_dir_correct` and `fast_round_near_correct`).
fn fast_round_near(h: f64, l: f64) -> Option<f64> {
    let (h, l, e) = fast_unscale(h, l);
    round_near_signed(h, l, e)
}

// sin x, cos t and tan x rounded toward +∞ if `up` and toward -∞ otherwise, and to nearest, by
// the fast path, or `None` where the argument is out of its range, where it declines the
// argument, or where its rounding test fails, other than where `fast_one_dir` decides sin x or
// cos t.
// `rocq/theories/FastTrig.v` proves that they return those roundings (`fast_sin_dir_correct`
// and the others), and the same with and without an FMA (`fast_sin_dir_fma` and the others).
// Always inlined, into the copies `sin_dir`, `cos_dir` and `tan_dir`, where sin and cos rounded
// down and up take 1.6 to 1.7 times the instructions of CORE-MATH in the same rounding
// (cachegrind, row 121, 4,096 arguments in [0.1, 10), [-10, 10) or [-π/4, π/4), in the release
// build of the tests for x86-64 with haswell). Before those copies, LLVM inlined the three into
// `sin`, `cos` and `tan` by itself from 09e972a on; out of line, they cost 7 to 15 more
// instructions per call there (cachegrind, at 09e972a). The attribute keeps that layout if the
// fast path grows.
#[inline(always)]
fn fast_sin_dir<const FMA: bool>(x: f64, up: bool) -> Option<f64> {
    let (h, l) = fast_sin::<FMA>(x)?;
    fast_round_dir(h, l, up).or_else(|| fast_one_dir(h, up))
}

#[inline(always)]
fn fast_cos_dir<const FMA: bool>(t: f64, up: bool) -> Option<f64> {
    let (h, l) = fast_cos::<FMA>(t)?;
    fast_round_dir(h, l, up).or_else(|| fast_one_dir(h, up))
}

// The rounding of y toward +∞ if `up` and toward -∞ otherwise, as `fast_round_dir`, where its
// test failed and h = ±1, for y = sin x or cos t, h + l within 2^-71 |y| of y and h = RN(h + l),
// and `None` for any other h. RN(h + l) = 1 puts h + l in [1 - 2^-54, 1 + 2^-53], and with
// |y| <= 1, y in [1 - 2^-54 - 2^-71, 1]. y = 1 would make x, or t, which `cos` passes only from
// 2^-26 up, a multiple of π/2 other than 0, which no `f64` is (`km_distance`). y is then
// strictly between 1 - 2^-53 and 1, where the rounding of y is one or the other, and the same
// for h = -1. The test fails there when |ρ| is below about 2^-34, as the gap between cos ρ and 1
// is then below the error.
// `rocq/theories/FastTrigOne.v` proves it (`fast_one_dir_correct`).
#[cold]
fn fast_one_dir(h: f64, up: bool) -> Option<f64> {
    #[cfg(test)]
    if !super::fast::fast_enabled() {
        return None;
    }
    if h.abs() != 1.0 {
        return None;
    }
    let v = near_one(-1.0, up != (h < 0.0));
    Some(if h < 0.0 { -v } else { v })
}

#[inline(always)]
fn fast_tan_dir<const FMA: bool>(x: f64, up: bool) -> Option<f64> {
    let (h, l) = fast_tan::<FMA>(x)?;
    fast_round_dir(h, l, up)
}

#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_sin_near<const FMA: bool>(x: f64) -> Option<f64> {
    let (h, l) = fast_sin::<FMA>(x)?;
    fast_round_near(h, l)
}

#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_cos_near<const FMA: bool>(t: f64) -> Option<f64> {
    let (h, l) = fast_cos::<FMA>(t)?;
    fast_round_near(h, l)
}

#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_tan_near<const FMA: bool>(x: f64) -> Option<f64> {
    let (h, l) = fast_tan::<FMA>(x)?;
    fast_round_near(h, l)
}

/// sin x rounded toward +∞ if `up` and toward -∞ otherwise.
#[inline(always)]
pub(crate) fn sin(x: f64, up: bool) -> f64 {
    // A copy per direction, where `up` is a constant.
    if up {
        sin_dir::<true>(x)
    } else {
        sin_dir::<false>(x)
    }
}

level_entry! {
    // `sin` toward +∞ if `UP` and toward -∞ otherwise.
    fn sin_dir<const UP: bool>(x: f64) -> f64 = sin_dir_with;
}

// The body of `sin_dir`, with `FMA` for the products (`level_entry!`). Without the dispatch,
// the rule and the fast path are tried with `Option::or_else`, as before the dispatch: in an
// `if let` chain, LLVM kept `fast_eval` out of line in those builds, and with `fast_eval`
// inlined, `sin_dir` and `cos_dir` still grew. With the dispatch, they are tried in an `if let`
// chain: where LLVM keeps `or_else` or its closure out of line, they are compiled without
// `fma`, also in the copy that has it, and the fast path with them.
#[inline(always)]
fn sin_dir_with<const FMA: bool, const UP: bool>(x: f64) -> f64 {
    if !x.is_finite() {
        f64::NAN
    } else if x.abs() < TINY_HYP {
        // x - x^3 / 6 <= sin x < x for x in (0, 1], and sin is odd.
        toward_zero(x, UP)
    } else {
        #[cfg(not(inari_kernel_dispatch))]
        let r = sin_small(x, UP)
            .or_else(|| fast_sin_dir::<FMA>(x, UP))
            .unwrap_or_else(|| ziv(&Sin(x), UP, 1));
        #[cfg(inari_kernel_dispatch)]
        let r = if let Some(r) = sin_small(x, UP) {
            r
        } else if let Some(r) = fast_sin_dir::<FMA>(x, UP) {
            r
        } else {
            ziv(&Sin(x), UP, 1)
        };
        r
    }
}

level_entry! {
    /// sin x rounded to nearest, ties to even.
    pub(crate) fn sin_near(x: f64) -> f64 = sin_near_with;
}

// The body of `sin_near`, with `FMA` for the products (`level_entry!`).
#[inline(always)]
fn sin_near_with<const FMA: bool>(x: f64) -> f64 {
    if !x.is_finite() {
        f64::NAN
    } else if x.abs() < TINY_NEAR {
        // x - x^3 / 6 <= sin x < x for x in (0, 1], and sin is odd.
        x
    } else {
        // No rule as `sin_small`, which only saves levels (the header says why `ziv_near`
        // does without one).
        fast_sin_near::<FMA>(x).unwrap_or_else(|| ziv_near(&Sin(x), 1))
    }
}

/// cos x rounded toward +∞ if `up` and toward -∞ otherwise.
#[inline(always)]
pub(crate) fn cos(x: f64, up: bool) -> f64 {
    // A copy per direction, where `up` is a constant.
    if up {
        cos_dir::<true>(x)
    } else {
        cos_dir::<false>(x)
    }
}

level_entry! {
    // `cos` toward +∞ if `UP` and toward -∞ otherwise.
    fn cos_dir<const UP: bool>(x: f64) -> f64 = cos_dir_with;
}

// The body of `cos_dir`, with `FMA` for the products (`level_entry!`), in the two forms of
// `sin_dir_with`, for the same reasons.
#[inline(always)]
fn cos_dir_with<const FMA: bool, const UP: bool>(x: f64) -> f64 {
    let t = x.abs();
    if !t.is_finite() {
        f64::NAN
    } else if t < TINY_HYP {
        // 1 - t^2 / 2 <= cos t < 1 for t in (0, 1], and 1 - t^2 / 2 > 1 - 2^-53 for
        // t < 2^-26. cos 0 = 1.
        near_one(-t, UP)
    } else {
        #[cfg(not(inari_kernel_dispatch))]
        let r = cos_small(t, UP)
            .or_else(|| fast_cos_dir::<FMA>(t, UP))
            .unwrap_or_else(|| ziv(&Cos(t), UP, 1));
        #[cfg(inari_kernel_dispatch)]
        let r = if let Some(r) = cos_small(t, UP) {
            r
        } else if let Some(r) = fast_cos_dir::<FMA>(t, UP) {
            r
        } else {
            ziv(&Cos(t), UP, 1)
        };
        r
    }
}

level_entry! {
    /// cos x rounded to nearest, ties to even.
    pub(crate) fn cos_near(x: f64) -> f64 = cos_near_with;
}

// The body of `cos_near`, with `FMA` for the products (`level_entry!`).
#[inline(always)]
fn cos_near_with<const FMA: bool>(x: f64) -> f64 {
    let t = x.abs();
    if !t.is_finite() {
        f64::NAN
    } else if t < TINY_NEAR {
        // 1 - 2^-55 < 1 - t^2 / 2 <= cos t <= 1.
        1.0
    } else {
        fast_cos_near::<FMA>(t).unwrap_or_else(|| ziv_near(&Cos(t), 1))
    }
}

/// tan x rounded toward +∞ if `up` and toward -∞ otherwise.
#[inline(always)]
pub(crate) fn tan(x: f64, up: bool) -> f64 {
    // A copy per direction, where `up` is a constant.
    if up {
        tan_dir::<true>(x)
    } else {
        tan_dir::<false>(x)
    }
}

level_entry! {
    // `tan` toward +∞ if `UP` and toward -∞ otherwise.
    fn tan_dir<const UP: bool>(x: f64) -> f64 = tan_dir_with;
}

// The body of `tan_dir`, with `FMA` for the products (`level_entry!`), in the two forms of
// `sin_dir_with`, for the same reasons.
#[inline(always)]
fn tan_dir_with<const FMA: bool, const UP: bool>(x: f64) -> f64 {
    if !x.is_finite() {
        f64::NAN
    } else if x.abs() < TINY_HYP {
        // x < tan x < x + x^3 / 2 for x in (0, 2^-26), and tan is odd.
        away(x, UP)
    } else {
        #[cfg(not(inari_kernel_dispatch))]
        let r = tan_small(x, UP)
            .or_else(|| fast_tan_dir::<FMA>(x, UP))
            .unwrap_or_else(|| ziv(&Tan(x), UP, 1));
        #[cfg(inari_kernel_dispatch)]
        let r = if let Some(r) = tan_small(x, UP) {
            r
        } else if let Some(r) = fast_tan_dir::<FMA>(x, UP) {
            r
        } else {
            ziv(&Tan(x), UP, 1)
        };
        r
    }
}

level_entry! {
    /// tan x rounded to nearest, ties to even.
    pub(crate) fn tan_near(x: f64) -> f64 = tan_near_with;
}

// The body of `tan_near`, with `FMA` for the products (`level_entry!`).
#[inline(always)]
fn tan_near_with<const FMA: bool>(x: f64) -> f64 {
    if !x.is_finite() {
        f64::NAN
    } else if x.abs() < TINY_NEAR {
        // x < tan x < x + x^3 / 2 for x in (0, 2^-26), and tan is odd.
        x
    } else {
        fast_tan_near::<FMA>(x).unwrap_or_else(|| ziv_near(&Tan(x), 1))
    }
}
