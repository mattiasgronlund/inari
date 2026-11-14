// The cube root cbrt x and hypot(x, y) = √(x^2 + y^2) with the dyadic kernel, each rounded to
// an `f64` toward +∞ if `up` and toward -∞ otherwise, and, as `cbrt_near` and `hypot_near`, to
// nearest, ties to even, as MPFR rounds them. `src/cr.rs` makes them the `cbrt_rn`, `cbrt_rd`,
// `cbrt_ru`, `hypot_rn`, `hypot_rd` and `hypot_ru` of `inari::cr`, and the tests on 64-bit
// Linux and macOS compare them with those of MPFR, `src/mpfr_calls/mpfr.rs`.
//
// Each first tries a fast path in `f64` (below), and only where that cannot decide the rounding
// calls the kernel, which, unlike the other functions of the kernel, does not use Ziv's
// strategy: it has no levels and no cap. It computes, in integers, the floor s of its result
// scaled by a power of two 2^-e, with 2^53 <= s, and whether the scaled result is above s,
// exactly (`icbrt` and `isqrt`). The number (2 s + 1) 2^(e - 1) if it is, and s 2^e otherwise, is
// the result rounded to odd at the bits of s and one more (`odd`): no `f64`, no midpoint of two
// adjacent `f64`s and no overflow threshold lies strictly between it and the result, as each of
// them is a multiple of 2^e there. So that one number rounds toward -∞, toward +∞ and to
// nearest to the same `f64` as the result (Boldo and Melquiond, Emulation of FMA and correctly
// rounded sums: proved algorithms using rounding to odd, IEEE Trans. Computers 57(4), 2008,
// Theorem 2, for nearest). Exact results and results midway between two `f64`s therefore need no
// rule. cbrt has no midpoints: its results other than 0 are at least 2^-358 in magnitude, where a
// midpoint is an odd multiple of a power of two with 54 significant bits, whose cube has at least
// 160 of them. hypot has some, such as hypot(134217729, 9007199388958720) = 9007199388958721 =
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
// The fast paths compute the result scaled by 2^-e, for an integer e in [-1021, 1022], as an
// unevaluated sum h + l of two `f64`s with h = RN(h + l) and a proved error bound, and decide
// its rounding with `round_dir_err` and `round_near_err` of `src/dyadic/fast.rs`, which return
// `None` unless 1/2 < h < 2; only the rule of `fast_hypot` below, at a gap of 27 or more,
// decides without them. Where a fast path returns `None`, `cbrt_odd` or `hypot_odd` computes
// the result. An exact result fails the directed tests, and a midpoint of two `f64`s the tests
// to nearest, which are strict, so those always go to the kernel: the rule meets neither.
//
// `fast_cbrt` follows CORE-MATH's `cbrt` [CORE-MATH]. It writes |x| = zz 2^(3 (et - 1365))
// with zz in [1, 8) from the bits of x, the significand of a subnormal x shifted to the top
// first, and takes an approximation y of cbrt zz from a cubic in the significand, one step of
// a third-order iteration and a factor 2^(i/3), none of whose errors is proved. `cbrt_step`
// then checks that the residual y^3 - zz, as computed, is at most 2^-32 in magnitude, and takes
// one Newton step with y^3 in double-double [Dekker], whose result is within 2^-65 of cbrt zz.
// cbrt's results lie in [2^-358, 2^342), so e = et - 1365 is in [-358, 341]. For some zz just
// below 8, h is 2, and those go to the kernel too.
//
// `fast_hypot` returns big = max(|x|, |y|), or the `f64` after it, at once where the biased
// exponents of big and small = min(|x|, |y|) differ by 27 or more, as hypot(x, y) is then above
// big by less than half an ulp of big. Below that, `hypot_dd` scales both by the same power of
// two, exactly, computes the sum of their squares in double-double, as CORE-MATH's `hypot`
// does [CORE-MATH], and its square root with `dd_sqrt`, within 2^-98. It returns `None` where
// big is subnormal or at least 2^1022.
//
// `rocq/theories/Model.v` transcribes each function of this file except the tests and the
// test-only switch of `fast_hypot` and `fast_hypot_near` (`fast_enabled`), so it has to be
// updated along with them. `rocq/theories/RootRound.v` proves that `odd` returns the
// number above and that it rounds as the result does, `rocq/theories/DyIcbrt.v` that `icbrt`
// returns floor(cbrt X) and whether it is exact, `rocq/theories/DyHypotOdd.v` that `hypot_odd`
// returns the number above, with `rocq/theories/DyHypotExact.v` for its branch below the gap
// of 27, and `rocq/theories/DyCbrt.v` and `rocq/theories/DyHypot.v` that each of the four
// functions returns, at every finite argument, its result rounded as `mpfr_round` in
// `rocq/theories/Mpfr.v` and `near_round` in `rocq/theories/NearF64.v` say, and the values at
// the zeros, the infinities and NaN. `rocq/theories/RootReal.v` proves the rule of hypot at a
// gap of at least 27 (`hypot_cut`). For the fast paths, `rocq/theories/FastCbrtReduce.v`
// proves the reduction of `fast_cbrt`, `rocq/theories/FastCbrtNewton.v` and
// `rocq/theories/FastCbrtStep.v` the bound of `cbrt_step`, and `rocq/theories/FastCbrt.v` the
// bound of `fast_cbrt` and that `fast_cbrt_dir` and `fast_cbrt_near` return cbrt x rounded.
// `rocq/theories/FastHypotFar.v` proves the rule at a difference of 27,
// `rocq/theories/FastHypotSum.v` and `rocq/theories/FastHypotDd.v` the bound of `hypot_dd`,
// from `rocq/theories/FastDdSqrt.v` for `dd_sqrt`, and `rocq/theories/FastHypot.v` that
// `fast_hypot` and `fast_hypot_near` return hypot(x, y) rounded. Each holds with and without an
// FMA, and the theorems of `DyCbrt.v` and `DyHypot.v` cover the calls of the fast paths.
//
// [CORE-MATH] P. Zimmermann et al., the CORE-MATH project, `src/binary64/cbrt/cbrt.c` and
// `src/binary64/hypot/hypot.c` by A. Sibidanov (MIT license), at commit 660067d. The
// coefficients of the cubic, `CBRT_C`, are a Remez fit of our own, not those of cbrt.c; the
// other constants are the `f64`s nearest 1/3, 2/9 and 2^(i/3).
// [Dekker] T. J. Dekker, A floating-point technique for extending the available precision,
// Numer. Math. 18 (1971) (the exact product of two `f64`s without an FMA, and Fast2Sum).

use super::{
    fast::{dd_sqrt, fast_two_sum, round_dir_err, round_near_err},
    isqrt,
    level::level_entry,
    round, Dyadic,
};
use crate::limbs;
use crate::simd::two_prod_err;
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

// The bits of the coefficients of a cubic c0 + c1 z + (c2 + c3 z) z^2 with a relative error
// against z^(1/3) on [1, 2] measured below 7.4e-5, not proved (a Remez fit), of RN(1/3) and
// RN(2/9), and of RN(2^(i/3)) for i = 0, 1, 2. `f64::from_bits` is not `const` before Rust 1.83.
const CBRT_C: [u64; 4] = [
    0x3fe1_b0ba_bcb6_1b30,
    0x3fe2_c9a3_e9ac_d5ba,
    0xbfc4_dc30_b2d8_c7f2,
    0x3f97_a8d3_e76f_9633,
];
const THIRD: u64 = 0x3fd5_5555_5555_5555;
const TWO_NINTHS: u64 = 0x3fcc_71c7_1c71_c71c;
const ESCALE: [u64; 3] = [
    0x3ff0_0000_0000_0000,
    0x3ff4_28a2_f98d_728b,
    0x3ff9_65fe_a53d_6e3d,
];
// 2^-32, the bound on the residual of the approximation that `cbrt_step` takes, and 2^-65, the
// bound on the error of its result.
const CBRT_RES: f64 = 1.0 / 4_294_967_296.0;
const ERR_CBRT: f64 = f64::EPSILON / 8192.0;

// One Newton step from an approximation y of cbrt zz, for zz in [1, 8) and rr within 2^-53 of
// 1/zz relatively: (h, l) with h = RN(h + l) and |cbrt zz - (h + l)| <= 2^-65, or `None` where
// the residual y^3 - zz, as computed, is not at most 2^-32 in magnitude. y can be any `f64`: the
// check bounds it. For y = (1 + eps) cbrt zz, y (1 - (y^3/zz - 1)/3) is
// (1 - 2 eps^2 - 4 eps^3/3 - eps^4/3) cbrt zz. [CORE-MATH] `rocq/theories/FastCbrtStep.v`
// proves the bound (`cbrt_step_correct`), from `rocq/theories/FastCbrtNewton.v` for the step on
// real numbers and its roundings.
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn cbrt_step<const FMA: bool>(y: f64, zz: f64, rr: f64) -> Option<(f64, f64)> {
    let y2 = y * y;
    let y3 = y * y2;
    // Exact by Sterbenz's lemma where the check passes.
    let d = y3 - zz;
    if d.abs() <= CBRT_RES {
        // y^3 = y3 + (y y2 - y3) + y y2l exactly, with y2l = y^2 - y2. [Dekker]
        let y2l = two_prod_err::<FMA>(y, y, y2);
        let y3l = two_prod_err::<FMA>(y, y2, y3) + y * y2l;
        let h = (d + y3l) * rr;
        let dy = h * (y * f64::from_bits(THIRD));
        Some(fast_two_sum(y, -dy))
    } else {
        None
    }
}

// (h, l, e) with h = RN(h + l), |cbrt |x| 2^-e - (h + l)| <= 2^-65 and e in [-358, 341], for a
// finite nonzero x, or `None` where `cbrt_step` returns it. [CORE-MATH]
// `rocq/theories/FastCbrt.v` proves the bound (`fast_cbrt_correct`), from
// `rocq/theories/FastCbrtReduce.v` for the reduction.
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_cbrt<const FMA: bool>(x: f64) -> Option<(f64, f64, i64)> {
    // |x| = z 2^(e - 1023) with z in [1, 2) from its bits, after shifting the significand of a
    // subnormal to the top.
    let bits = x.to_bits() & 0x7fff_ffff_ffff_ffff;
    let mut m = bits & 0x000f_ffff_ffff_ffff;
    let mut e = (bits >> 52) as i64;
    if e == 0 {
        let nz = bits.leading_zeros() - 11;
        m = (m << nz) & 0x000f_ffff_ffff_ffff;
        e = 1 - i64::from(nz);
    }
    // e + 3072 = 3 et + i, so |x| = zz 2^(3 (et - 1365)) for zz = z 2^i in [1, 8).
    let (et, i) = ((e + 3072) / 3, (e + 3072) % 3);
    let z = f64::from_bits(m | 0x3ff0_0000_0000_0000);
    let zz = f64::from_bits((m | 0x3ff0_0000_0000_0000) + ((i as u64) << 52));
    let r = 1.0 / z;
    // RN(1/z) 2^-i, exactly.
    let rr = r * f64::from_bits(((1023 - i) as u64) << 52);
    // A cubic for cbrt z, one step of a third-order iteration, and the factor 2^(i/3). Nothing
    // depends on its accuracy but how often `cbrt_step` returns `None`.
    let z2 = z * z;
    let c0 = f64::from_bits(CBRT_C[0]) + z * f64::from_bits(CBRT_C[1]);
    let c2 = f64::from_bits(CBRT_C[2]) + z * f64::from_bits(CBRT_C[3]);
    let mut y = c0 + z2 * c2;
    let y2 = y * y;
    let t = y2 * (y * r) - 1.0;
    y -= (t * y) * (f64::from_bits(THIRD) - f64::from_bits(TWO_NINTHS) * t);
    y *= f64::from_bits(ESCALE[i as usize]);
    let (h, l) = cbrt_step::<FMA>(y, zz, rr)?;
    Some((h, l, et - 1365))
}

// cbrt x rounded toward +∞ if `up` and toward -∞ otherwise, and to nearest, by the fast path, or
// `None` where the rounding test fails or `fast_cbrt` returns `None`, for a finite nonzero x. cbrt
// is odd: for x < 0, cbrt x rounded up is -cbrt(-x) rounded down. `rocq/theories/FastCbrt.v`
// proves both (`fast_cbrt_dir_correct`, `fast_cbrt_near_correct`), and that an FMA changes
// neither (`fast_cbrt_dir_fma`, `fast_cbrt_near_fma`).
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_cbrt_dir<const FMA: bool>(x: f64, up: bool) -> Option<f64> {
    let (h, l, e) = fast_cbrt::<FMA>(x)?;
    let r = round_dir_err(h, l, e, ERR_CBRT, up != (x < 0.0))?;
    Some(if x < 0.0 { -r } else { r })
}

#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_cbrt_near<const FMA: bool>(x: f64) -> Option<f64> {
    let (h, l, e) = fast_cbrt::<FMA>(x)?;
    let r = round_near_err(h, l, e, ERR_CBRT)?;
    Some(if x < 0.0 { -r } else { r })
}

level_entry! {
    /// cbrt x rounded toward +∞ if `up` and toward -∞ otherwise, with ±0, ±∞ and NaN at ±0, ±∞
    /// and NaN, as MPFR's `mpfr_cbrt` gives them.
    #[cfg_attr(inari_kernel_dispatch, inline(always))]
    pub(crate) fn cbrt(x: f64, up: bool) -> f64 = cbrt_with;
}

// The body of `cbrt`, with `FMA` for the products (`level_entry!`).
#[inline(always)]
fn cbrt_with<const FMA: bool>(x: f64, up: bool) -> f64 {
    if x == 0.0 || !x.is_finite() {
        x
    } else if let Some(r) = fast_cbrt_dir::<FMA>(x, up) {
        r
    } else {
        cbrt_odd(x).to_f64(up)
    }
}

level_entry! {
    /// cbrt x rounded to nearest, ties to even, with ±0, ±∞ and NaN at ±0, ±∞ and NaN, as MPFR's
    /// `mpfr_cbrt` gives them.
    pub(crate) fn cbrt_near(x: f64) -> f64 = cbrt_near_with;
}

// The body of `cbrt_near` (`level_entry!`).
#[inline(always)]
fn cbrt_near_with<const FMA: bool>(x: f64) -> f64 {
    if x == 0.0 || !x.is_finite() {
        x
    } else if let Some(r) = fast_cbrt_near::<FMA>(x) {
        r
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

// 2^-98, the bound on the error of `hypot_dd`.
const ERR_HYPOT: f64 = f64::EPSILON / 70_368_744_177_664.0;

// (h, l, e) with h = RN(h + l), |hypot(big, small) 2^-e - (h + l)| <= 2^-98 and e in
// [-1021, 1022], for finite big >= small > 0 whose biased exponents differ by less than 27, or
// `None` where big is subnormal or at least 2^1022. Scaled by 2^-e, big is in [1/2, 1) and small
// at least 2^-78, so the scaling and the squares by `two_prod_err` are exact, and
// x^2 + y^2 = r2 + e2 + dx2 + dy2 exactly. [CORE-MATH] `rocq/theories/FastHypotDd.v` proves
// the bound (`hypot_dd_correct`), from `rocq/theories/FastHypotSum.v` for the sum of the
// squares and `rocq/theories/FastDdSqrt.v` for `dd_sqrt`.
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn hypot_dd<const FMA: bool>(big: f64, small: f64) -> Option<(f64, f64, i64)> {
    let eb = (big.to_bits() >> 52) as i64;
    if eb == 0 || eb > 2044 {
        return None;
    }
    // 2^(1022 - eb).
    let s = f64::from_bits(((2045 - eb) as u64) << 52);
    let (x, y) = (big * s, small * s);
    let (x2, y2) = (x * x, y * y);
    let dx2 = two_prod_err::<FMA>(x, x, x2);
    let dy2 = two_prod_err::<FMA>(y, y, y2);
    let (r2, e2) = fast_two_sum(x2, y2);
    // Renormalized, so that |al| <= 2^-52 ah, as `dd_sqrt` takes it.
    let (ah, al) = fast_two_sum(r2, e2 + (dx2 + dy2));
    let (h, l) = dd_sqrt::<FMA>(ah, al);
    Some((h, l, eb - 1022))
}

// hypot(x, y) rounded toward +∞ if `up` and toward -∞ otherwise, and to nearest, by the fast
// path, or `None` where the rounding test fails or `hypot_dd` returns `None`, for finite nonzero
// x and y. Where the biased exponents of big = max(|x|, |y|) and small = min(|x|, |y|) differ by
// 27 or more, big is normal and big < hypot(x, y) < big + small^2 / (2 big) < big + ulp(big)/2,
// so the result is big, or the `f64` after it rounded up (+∞ after the largest `f64`).
// `rocq/theories/FastHypotFar.v` proves that rule (`hypot_far_dir`, `hypot_far_near`), and
// `rocq/theories/FastHypot.v` both functions (`fast_hypot_dir_correct`,
// `fast_hypot_near_correct`), and that an FMA changes neither (`fast_hypot_dir_fma`,
// `fast_hypot_near_fma`).
#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_hypot<const FMA: bool>(x: f64, y: f64, up: bool) -> Option<f64> {
    #[cfg(test)]
    if !super::fast::fast_enabled() {
        return None;
    }
    let (big, small) = if x.abs() >= y.abs() {
        (x.abs(), y.abs())
    } else {
        (y.abs(), x.abs())
    };
    if (big.to_bits() >> 52) as i64 - (small.to_bits() >> 52) as i64 >= 27 {
        return Some(if up {
            f64::from_bits(big.to_bits() + 1)
        } else {
            big
        });
    }
    let (h, l, e) = hypot_dd::<FMA>(big, small)?;
    round_dir_err(h, l, e, ERR_HYPOT, up)
}

#[cfg_attr(inari_kernel_dispatch, inline(always))]
fn fast_hypot_near<const FMA: bool>(x: f64, y: f64) -> Option<f64> {
    #[cfg(test)]
    if !super::fast::fast_enabled() {
        return None;
    }
    let (big, small) = if x.abs() >= y.abs() {
        (x.abs(), y.abs())
    } else {
        (y.abs(), x.abs())
    };
    if (big.to_bits() >> 52) as i64 - (small.to_bits() >> 52) as i64 >= 27 {
        return Some(big);
    }
    let (h, l, e) = hypot_dd::<FMA>(big, small)?;
    round_near_err(h, l, e, ERR_HYPOT)
}

/// hypot(x, y) = √(x^2 + y^2) rounded toward +∞ if `up` and toward -∞ otherwise, with the values
/// of MPFR's `mpfr_hypot` at the zeros, the infinities and NaN: +∞ if `x` or `y` is infinite,
/// even if the other is NaN, NaN otherwise if one is NaN, and |x| at y = ±0, +0 at two zeros.
#[inline(always)]
pub(crate) fn hypot(x: f64, y: f64, up: bool) -> f64 {
    // A copy per direction, where `up` is a constant.
    if up {
        hypot_dir::<true>(x, y)
    } else {
        hypot_dir::<false>(x, y)
    }
}

level_entry! {
    // `hypot` toward +∞ if `UP` and toward -∞ otherwise. Never inlined in the build without the
    // dispatch, which keeps that build as it was: LLVM inlines the one-call wrapper otherwise.
    #[cfg_attr(not(inari_kernel_dispatch), inline(never))]
    fn hypot_dir<const UP: bool>(x: f64, y: f64) -> f64 = hypot_dir_with;
}

// The body of `hypot_dir` (`level_entry!`).
#[inline(always)]
fn hypot_dir_with<const FMA: bool, const UP: bool>(x: f64, y: f64) -> f64 {
    if x.is_infinite() || y.is_infinite() {
        f64::INFINITY
    } else if x.is_nan() || y.is_nan() {
        f64::NAN
    } else if y == 0.0 {
        x.abs()
    } else if x == 0.0 {
        y.abs()
    } else if let Some(r) = fast_hypot::<FMA>(x, y, UP) {
        r
    } else {
        hypot_odd(x, y).to_f64(UP)
    }
}

level_entry! {
    /// hypot(x, y) = √(x^2 + y^2) rounded to nearest, ties to even, with the values of `hypot` at
    /// the zeros, the infinities and NaN.
    pub(crate) fn hypot_near(x: f64, y: f64) -> f64 = hypot_near_with;
}

// The body of `hypot_near` (`level_entry!`).
#[inline(always)]
fn hypot_near_with<const FMA: bool>(x: f64, y: f64) -> f64 {
    if x.is_infinite() || y.is_infinite() {
        f64::INFINITY
    } else if x.is_nan() || y.is_nan() {
        f64::NAN
    } else if y == 0.0 {
        x.abs()
    } else if x == 0.0 {
        y.abs()
    } else if let Some(r) = fast_hypot_near::<FMA>(x, y) {
        r
    } else {
        hypot_odd(x, y).to_f64_near()
    }
}
