// The cube root cbrt x and hypot(x, y) = √(x^2 + y^2) with the dyadic kernel, each rounded to
// an `f64` toward +∞ if `up` and toward -∞ otherwise, and, as `cbrt_near` and `hypot_near`, to
// nearest, ties to even, as MPFR rounds them. `src/cr.rs` makes them the `cbrt_rn`, `cbrt_rd`,
// `cbrt_ru`, `hypot_rn`, `hypot_rd` and `hypot_ru` of `inari::cr`, and the tests on 64-bit
// Linux and macOS compare them with those of MPFR, `src/mpfr_calls/mpfr.rs`.
//
// Unlike the other functions of the kernel, these two do not use Ziv's strategy: they have no
// levels and no cap. Each computes, in integers, the floor s of its result scaled by a power of
// two 2^-e, with 2^53 <= s, and whether the scaled result is above s, exactly (`icbrt` and
// `isqrt`). The number (2 s + 1) 2^(e - 1) if it is, and s 2^e otherwise, is the result rounded
// to odd at the bits of s and one more (`odd`): no `f64`, no midpoint of two adjacent `f64`s and
// no overflow threshold lies strictly between it and the result, as each of them is a multiple
// of 2^e there. So that one number rounds toward -∞, toward +∞ and to nearest to the same `f64`
// as the result (Boldo and Melquiond, Emulation of FMA and correctly rounded sums: proved
// algorithms using rounding to odd, IEEE Trans. Computers 57(4), 2008, Theorem 2, for nearest).
// Exact results and results midway between two `f64`s therefore need no rule. cbrt has no
// midpoints: its results other than 0 are at least 2^-358 in magnitude, where a midpoint is an
// odd multiple of a power of two with 54 significant bits, whose cube has at least 160 of
// them. hypot has some, such as hypot(134217729, 9007199388958720) = 9007199388958721 =
// 2^53 + 2^27 + 1.
//
// cbrt scales |x| = M 2^e, 2^63 <= M < 2^64, to X = M 2^k, 2^159 <= X < 2^162, with k in
// {96, 97, 98} such that e - k is a multiple of 3, and takes s = floor(cbrt X) by Newton's
// iteration on integers from a seed that `f64` arithmetic computes. hypot of |x| >= |y| > 0
// with |x| = M 2^e and |y| = m 2^f, 2^63 <= M, m < 2^64, takes, for a gap g = e - f of at
// least 27, s = M / 2^10, the significand of x and one zero bit, as the result is then above
// |x| by less than 2^(e + 10) (`hypot_odd`); and otherwise the integer square root of the
// exact sum (M 2^g)^2 + m^2, scaled by an even power of two to the shape that `isqrt` takes.
//
// `cbrt_odd` and `hypot_odd` are the seams for a faster evaluation in `f64` in front of them.
//
// `rocq/theories/Model.v` transcribes each function of this file except the tests, so it has
// to be updated along with them. `rocq/theories/RootRound.v` proves that `odd` returns the
// number above and that it rounds as the result does, `rocq/theories/DyIcbrt.v` that `icbrt`
// returns floor(cbrt X) and whether it is exact, `rocq/theories/DyHypotOdd.v` that `hypot_odd`
// returns the number above, with `rocq/theories/DyHypotExact.v` for its branch below the gap
// of 27, and `rocq/theories/DyCbrt.v` and `rocq/theories/DyHypot.v` that each of the four
// functions returns, at every finite argument, its result rounded as `mpfr_round` in
// `rocq/theories/Mpfr.v` and `near_round` in `rocq/theories/NearF64.v` say, and the values at
// the zeros, the infinities and NaN. `rocq/theories/RootReal.v` proves the rule of hypot at a
// gap of at least 27 (`hypot_cut`).

use super::{isqrt, round, Dyadic};
use crate::limbs;
use std::cmp::Ordering;

#[cfg(test)]
mod tests;

// The `Dyadic<N>` of (-1)^neg (2 s + 1) 2^(e - 1) if `inexact`, and of (-1)^neg s 2^e
// otherwise, for 2^53 <= s and 2 s + 1 < 2^(64 N): the number (-1)^neg (s + t) 2^e with
// 0 <= t < 1, t = 0 exactly when not `inexact`, rounded to odd at the bits of s and one more.
// It has at most 64 N bits, so `round` keeps it exactly.
fn odd<const N: usize>(neg: bool, s: &[u64], e: i64, inexact: bool) -> Dyadic<N> {
    let mut w = [0; N];
    limbs::shl_into(&mut w, s, 1);
    w[0] |= u64::from(inexact);
    round(neg, &w, e - 1, false, false)
}

// `(floor(cbrt(x)), floor(cbrt(x))^3 != x)` for `x.len() == 3` and 2^159 <= x < 2^162, so that
// 2^53 <= floor(cbrt(x)) < 2^54.
fn icbrt(x: &[u64]) -> (u64, bool) {
    // The seed: x = t 2^99 + (x mod 2^99) with 2^60 <= t < 2^63, so cbrt(x) is near
    // cbrt(t) 2^33. The bits of an `f64` are about 2^52 (log2 + 1023) of it, so the bits of
    // `t as f64` divided by 3, plus a constant a little below two thirds of the bits of 1.0
    // (its top 32 bits are B1 of `cbrt` in FreeBSD's msun, after Kahan), are those of an `f64`
    // near cbrt(t), and three Newton steps in `f64`, c - (c^3 - t) / (3 c^2), bring c close
    // enough that the integer iteration below usually takes one step. The bits of an `f64` are
    // below 2^64, so the sum does not overflow. Only the clamp of s to [2^53, 2^54] matters for
    // the result, whatever the `f64` operations give.
    let mut t = [0];
    limbs::shr_into(&mut t, x, 99);
    let t = t[0] as f64;
    let mut c = f64::from_bits(t.to_bits() / 3 + 0x2a9f_7893_782d_a1ce);
    for _ in 0..3 {
        c -= (c * c * c - t) / (3.0 * c * c);
    }
    let mut s = ((c * 8_589_934_592.0) as u64).clamp(1 << 53, 1 << 54);
    // Newton's iteration for the integer k-th root, k = 3 (Brent and Zimmermann, Modern
    // Computer Arithmetic, 1.5.2): y = floor((2 s + floor(x / s^2)) / 3). Each step makes
    // y >= floor(cbrt(x)) from any s > 0, as (r - s)^2 (r + 2 s) >= 0 gives
    // 3 r s^2 - 2 s^3 <= r^3 <= x for r = floor(cbrt(x)), and y < s while s > r. So y^3 <= x
    // means y = r, and otherwise y > r and the next s is lower. s stays in [2^53, 2^55):
    // y >= r >= 2^53, and y < 2^55 as floor(x / s^2) < 2^56, and < 2^54 for s >= 2^54 (s
    // passes 2^54 only after a seed below r). So floor(x / s^2) is limb 0 of the quotient,
    // 2 s + floor(x / s^2) < 3 * 2^55, and the cube of y, which is less than 2^165, is the
    // sticky bit.
    loop {
        let sq = u128::from(s) * u128::from(s);
        let (mut q, mut r, mut scratch) = ([0; 3], [0; 2], [0; 7]);
        limbs::div_rem(
            &mut q,
            &mut r,
            x,
            &[sq as u64, (sq >> 64) as u64],
            &mut scratch,
        );
        let y = (2 * s + q[0]) / 3;
        let yy = u128::from(y) * u128::from(y);
        let mut cube = [0; 3];
        limbs::mul_into(&mut cube, &[y], &[yy as u64, (yy >> 64) as u64]);
        match limbs::cmp(&cube, x) {
            Ordering::Greater => s = y,
            o => return (y, o == Ordering::Less),
        }
    }
}

// cbrt x rounded to odd, as `odd` says, for a finite nonzero `x`.
fn cbrt_odd(x: f64) -> Dyadic<1> {
    // |x| = M 2^e with 2^63 <= M < 2^64, and cbrt x = (-1)^neg cbrt(M 2^k) 2^((e - k) / 3).
    let a = Dyadic::<1>::from_f64(x);
    let k = 96 + (a.exp - 96).rem_euclid(3);
    let mut big = [0; 3];
    limbs::shl_into(&mut big, &a.m, k as u64);
    let (s, inexact) = icbrt(&big);
    odd(a.neg, &[s], (a.exp - k) / 3, inexact)
}

/// cbrt x rounded toward +∞ if `up` and toward -∞ otherwise, with ±0, ±∞ and NaN at ±0, ±∞
/// and NaN, as MPFR's `mpfr_cbrt` gives them.
pub(crate) fn cbrt(x: f64, up: bool) -> f64 {
    if x == 0.0 || !x.is_finite() {
        x
    } else {
        cbrt_odd(x).to_f64(up)
    }
}

/// cbrt x rounded to nearest, ties to even, with ±0, ±∞ and NaN at ±0, ±∞ and NaN, as MPFR's
/// `mpfr_cbrt` gives them.
pub(crate) fn cbrt_near(x: f64) -> f64 {
    if x == 0.0 || !x.is_finite() {
        x
    } else {
        cbrt_odd(x).to_f64_near()
    }
}

// hypot(x, y) rounded to odd, as `odd` says, for finite nonzero `x` and `y`.
fn hypot_odd(x: f64, y: f64) -> Dyadic<3> {
    let (big, small) = if x.abs() >= y.abs() {
        (x.abs(), y.abs())
    } else {
        (y.abs(), x.abs())
    };
    // big = M 2^e and small = m 2^f with 2^63 <= M, m < 2^64, and so e >= f.
    let (a, b) = (Dyadic::<1>::from_f64(big), Dyadic::<1>::from_f64(small));
    let g = a.exp - b.exp;
    if g >= 27 {
        // 0 < hypot(x, y) - big = small^2 / (hypot(x, y) + big) < small^2 / (2 big)
        // < 2^(2 f + 128) / 2^(e + 64) = 2^(e - 2 g + 64) <= 2^(e + 10) (`hypot_cut`), and the
        // low 11 bits of M are 0, as `big` has at most 53 significant bits, so s = M / 2^10 at
        // 2^(e + 10) is big.
        odd(false, &[a.m[0] >> 10], a.exp + 10, true)
    } else {
        // S = (M 2^g)^2 + m^2, which is exact, and 2^126 <= S < 2^181, so that
        // hypot(x, y) = √S 2^f. X = S 2^(2 h) with h such that 2^255 <= X < 2^257, the shape
        // that `isqrt` takes for n = 2, 76 <= 2 h <= 130, and √S 2^f = √X 2^(f - h).
        let mut wide = [0; 2];
        limbs::shl_into(&mut wide, &a.m, g as u64);
        let mut sum = [0; 4];
        limbs::mul_into(&mut sum, &wide, &wide);
        let mm = u128::from(b.m[0]) * u128::from(b.m[0]);
        limbs::add_assign(&mut sum, &[mm as u64, (mm >> 64) as u64]);
        let h = (257 - limbs::bit_len(&sum)) / 2;
        let mut xx = [0; 5];
        limbs::shl_into(&mut xx, &sum, 2 * h);
        let (mut s, mut scratch) = ([0; 3], [0; 21]);
        isqrt(&mut s, &xx, &mut scratch);
        let mut sq = [0; 6];
        limbs::mul_into(&mut sq, &s, &s);
        let inexact = limbs::cmp(&sq, &xx) != Ordering::Equal;
        odd(false, &s, b.exp - h as i64, inexact)
    }
}

/// hypot(x, y) = √(x^2 + y^2) rounded toward +∞ if `up` and toward -∞ otherwise, with the values
/// of MPFR's `mpfr_hypot` at the zeros, the infinities and NaN: +∞ if `x` or `y` is infinite,
/// even if the other is NaN, NaN otherwise if one is NaN, and |x| at y = ±0, +0 at two zeros.
pub(crate) fn hypot(x: f64, y: f64, up: bool) -> f64 {
    if x.is_infinite() || y.is_infinite() {
        f64::INFINITY
    } else if x.is_nan() || y.is_nan() {
        f64::NAN
    } else if y == 0.0 {
        x.abs()
    } else if x == 0.0 {
        y.abs()
    } else {
        hypot_odd(x, y).to_f64(up)
    }
}

/// hypot(x, y) = √(x^2 + y^2) rounded to nearest, ties to even, with the values of `hypot` at
/// the zeros, the infinities and NaN.
pub(crate) fn hypot_near(x: f64, y: f64) -> f64 {
    if x.is_infinite() || y.is_infinite() {
        f64::INFINITY
    } else if x.is_nan() || y.is_nan() {
        f64::NAN
    } else if y == 0.0 {
        x.abs()
    } else if x == 0.0 {
        y.abs()
    } else {
        hypot_odd(x, y).to_f64_near()
    }
}
