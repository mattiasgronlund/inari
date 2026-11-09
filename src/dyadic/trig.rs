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
// nonzero `f64` has a sin, cos or tan that is one, by the theorem of Lindemann and
// Weierstrass, as an `f64` is algebraic, which is not proved here. `ziv` computes the rest
// from an `Eval`. The functions rounded to nearest have the rules of NaN, ±∞ and of the
// arguments of magnitude below 2^-27 (`TINY_NEAR`), whose results are less than half an ulp
// from x or 1, and `ziv_near` computes the rest from the same `Eval`s. They have no rules at
// small arguments, which only save levels of `ziv`. At some arguments with few bits, sin and
// tan lie close to the midpoint of two `f64`s, as the results of those rules lie close to an
// `f64`: t - t^3 / 6 is a midpoint at t = 21 2^-24, and sin t lies above it by about t^5 / 120,
// and t + t^3 / 3 is one at t = 3 2^-26. `ziv_near` settles them at a later level, as no sin,
// cos or tan of a nonzero `f64` is a midpoint, by the same theorem.
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
// and, where a rule settles the argument or a rounding test of `ziv` passes, its result
// rounded as `mpfr_round` in `rocq/theories/Mpfr.v` says. It builds on
// `rocq/theories/DyTrigReduce.v` for `reduce`, `rocq/theories/DyTrigCore.v` for `series` and
// `sin_k`, `rocq/theories/TrigSeries.v` for the bounds of the series and the identities that
// the evaluations use, `rocq/theories/DyTrigTiny.v` for the rules at tiny arguments, and
// `rocq/theories/DyTrigSmall.v`, `rocq/theories/DyCosSmall.v`, `rocq/theories/DySinSmall.v`
// and `rocq/theories/DyTanSmall.v` for those at small arguments. `rocq/theories/DyTrigNear.v`
// proves that each of the three functions rounded to nearest, at a finite argument, where a
// rule settles the argument or a rounding test of `ziv_near` passes, returns its result
// rounded to nearest as `near_round` in `rocq/theories/NearF64.v` says, from the same
// enclosures and bounds and the cells of `rocq/theories/NearCells.v`. That a test passes by
// the cap of `ziv` or of `ziv_near` is not proved, nor that the evaluations do not panic.

use super::{
    consts::PI,
    exp::{away, near_one, toward_zero, TINY_HYP, TINY_NEAR},
    round, ziv, ziv_near, Dyadic, Encl, Eval,
};
use crate::limbs;
use std::cmp::Ordering;

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

/// sin x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn sin(x: f64, up: bool) -> f64 {
    if !x.is_finite() {
        f64::NAN
    } else if x.abs() < TINY_HYP {
        // x - x^3 / 6 <= sin x < x for x in (0, 1], and sin is odd.
        toward_zero(x, up)
    } else {
        sin_small(x, up).unwrap_or_else(|| ziv(&Sin(x), up, 1))
    }
}

/// sin x rounded to nearest, ties to even.
pub(crate) fn sin_near(x: f64) -> f64 {
    if !x.is_finite() {
        f64::NAN
    } else if x.abs() < TINY_NEAR {
        // x - x^3 / 6 <= sin x < x for x in (0, 1], and sin is odd.
        x
    } else {
        // No rule as `sin_small`, which only saves levels (the header says why `ziv_near`
        // does without one).
        ziv_near(&Sin(x), 1)
    }
}

/// cos x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn cos(x: f64, up: bool) -> f64 {
    let t = x.abs();
    if !t.is_finite() {
        f64::NAN
    } else if t < TINY_HYP {
        // 1 - t^2 / 2 <= cos t < 1 for t in (0, 1], and 1 - t^2 / 2 > 1 - 2^-53 for
        // t < 2^-26. cos 0 = 1.
        near_one(-t, up)
    } else {
        cos_small(t, up).unwrap_or_else(|| ziv(&Cos(t), up, 1))
    }
}

/// cos x rounded to nearest, ties to even.
pub(crate) fn cos_near(x: f64) -> f64 {
    let t = x.abs();
    if !t.is_finite() {
        f64::NAN
    } else if t < TINY_NEAR {
        // 1 - 2^-55 < 1 - t^2 / 2 <= cos t <= 1.
        1.0
    } else {
        ziv_near(&Cos(t), 1)
    }
}

/// tan x rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn tan(x: f64, up: bool) -> f64 {
    if !x.is_finite() {
        f64::NAN
    } else if x.abs() < TINY_HYP {
        // x < tan x < x + x^3 / 2 for x in (0, 2^-26), and tan is odd.
        away(x, up)
    } else {
        tan_small(x, up).unwrap_or_else(|| ziv(&Tan(x), up, 1))
    }
}

/// tan x rounded to nearest, ties to even.
pub(crate) fn tan_near(x: f64) -> f64 {
    if !x.is_finite() {
        f64::NAN
    } else if x.abs() < TINY_NEAR {
        // x < tan x < x + x^3 / 2 for x in (0, 2^-26), and tan is odd.
        x
    } else {
        ziv_near(&Tan(x), 1)
    }
}
