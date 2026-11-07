// Tests of the trigonometric functions of the dyadic kernel. Every generator runs in both
// feature sets through `check`, which checks that the two directions give the same `f64` or two
// adjacent ones, or NaN for both. With `gmp`, it also compares both directions with the
// function of `src/mpfr_calls/mpfr.rs` that computes the same function with MPFR, which they
// have to agree with bit for bit. The generator of the `f64`s nearest to multiples of π/2
// needs π to more bits than an `f64` has, so it runs only with `gmp`.

use super::*;
use crate::dyadic::tests::Rng;

type Directed = fn(f64, bool) -> f64;

const SIN: usize = 0;
const COS: usize = 1;
const TAN: usize = 2;

const FUNCTIONS: [(&str, Directed); 3] = [("sin", sin), ("cos", cos), ("tan", tan)];

// The `f64` after `x` toward +∞, for `x` below +∞: 2^-1074 after either zero, and -0 after
// -2^-1074. `f64::next_up` needs a Rust after the MSRV.
fn next_up(x: f64) -> f64 {
    if x == 0.0 {
        f64::from_bits(1)
    } else if x > 0.0 {
        f64::from_bits(x.to_bits() + 1)
    } else {
        f64::from_bits(x.to_bits() - 1)
    }
}

// The `f64` before `x` toward -∞, for `x` above -∞.
fn next_down(x: f64) -> f64 {
    -next_up(-x)
}

// 2^n, for n in [-1074, 1023].
fn pow2(n: i32) -> f64 {
    if n < -1022 {
        f64::from_bits(1 << (n + 1074))
    } else {
        f64::from_bits(u64::try_from(n + 1023).unwrap() << 52)
    }
}

// An integer uniform in [lo, hi].
fn uniform(rng: &mut Rng, lo: i32, hi: i32) -> i32 {
    lo + rng.below(u64::try_from(hi - lo + 1).unwrap()) as i32
}

// m 2^e for a random m in [1, 2) and an e uniform in [lo, hi], for lo and hi in
// [-1074, 1023], rounded to a subnormal below e = -1022.
fn log_uniform(rng: &mut Rng, lo: i32, hi: i32) -> f64 {
    let e = uniform(rng, lo, hi);
    let m = 1.0 + rng.below(1 << 52) as f64 / (1u64 << 52) as f64;
    m * pow2(e)
}

// 1 or -1, at random.
fn random_sign(rng: &mut Rng) -> f64 {
    if rng.below(2) == 0 {
        -1.0
    } else {
        1.0
    }
}

// `lo` and `hi`, the two directions of `name` at `x`, are equal or adjacent, or NaN both.
fn check_pair(name: &str, x: f64, lo: f64, hi: f64) {
    if lo.is_nan() || hi.is_nan() {
        assert!(
            lo.is_nan() && hi.is_nan(),
            "{}({:e}): {:e} {:e}",
            name,
            x,
            lo,
            hi
        );
    } else {
        assert!(
            lo.to_bits() == hi.to_bits() || next_up(lo).to_bits() == hi.to_bits(),
            "{}({:e}): {:e} and {:e} are neither equal nor adjacent",
            name,
            x,
            lo,
            hi
        );
    }
}

// Checks the function `i` at `x` in both directions, as the header says.
fn check(i: usize, x: f64) {
    let (name, f) = FUNCTIONS[i];
    let (lo, hi) = (f(x, false), f(x, true));
    check_pair(name, x, lo, hi);
    #[cfg(feature = "gmp")]
    mpfr::check(i, x, lo, hi);
}

// Checks each function at `x` and at -x.
fn check_all(x: f64) {
    for i in 0..FUNCTIONS.len() {
        check(i, x);
        check(i, -x);
    }
}

// `x` and the `k` `f64`s on each side of it, for an `x` that has `k` finite `f64`s on each
// side of it.
fn around(x: f64, k: usize) -> Vec<f64> {
    let (mut a, mut b) = (x, x);
    let mut v = vec![x];
    for _ in 0..k {
        a = next_down(a);
        b = next_up(b);
        v.push(a);
        v.push(b);
    }
    v
}

// Arguments on which mismatches were found, as `(function, argument)`, each with what it broke
// and where it was found.
fn regressions() -> Vec<(&'static str, &'static str)> {
    vec![]
}

#[test]
fn regressions_hold() {
    for (name, x) in regressions() {
        let i = FUNCTIONS.iter().position(|(n, _)| *n == name).unwrap();
        check(i, x.parse().unwrap());
    }
}

// Special values, both signs of each: the zeros, the infinities and NaN, at which the rules give
// results, and finite values from the least to the greatest.
const SPECIAL: [f64; 9] = [
    0.0,
    // 2^-1074, the least `f64` above 0. `f64::from_bits` is `const` only after the MSRV.
    5e-324,
    f64::MIN_POSITIVE,
    0.5,
    1.0,
    2.0,
    f64::MAX,
    f64::INFINITY,
    f64::NAN,
];

#[test]
fn special_and_exact() {
    for x in SPECIAL {
        check_all(x);
    }
    for up in [false, true] {
        // sin and tan keep the sign of a zero, and cos is 1 at both.
        for x in [0.0, -0.0] {
            assert_eq!(sin(x, up).to_bits(), x.to_bits());
            assert_eq!(tan(x, up).to_bits(), x.to_bits());
            assert_eq!(cos(x, up), 1.0);
        }
        for x in [f64::INFINITY, f64::NEG_INFINITY, f64::NAN] {
            for (_, f) in FUNCTIONS {
                assert!(f(x, up).is_nan());
            }
        }
    }
}

// Each rule and the reduction at its threshold and the 3 `f64`s on each side of it, both signs
// of them: `TINY_HYP` for the three functions, and `NO_REDUCE` and π/4, between which the
// reduction starts with k = 0.
#[test]
fn rules_at_their_thresholds() {
    for t in [TINY_HYP, NO_REDUCE, std::f64::consts::FRAC_PI_4] {
        for x in around(t, 3) {
            check_all(x);
        }
    }
}

// The `f64` nearest to a multiple of π/2, of Kahan and McDonald (the header of `trig.rs`), and
// the `f64`s around it.
#[test]
fn nearest_to_a_multiple() {
    let x = 6_381_956_970_095_103.0 * pow2(797);
    for y in around(x, 3) {
        check_all(y);
    }
}

// Arguments whose results are close to an `f64`, and the 3 `f64`s on each side of each, both
// signs of them, all checked as `check` checks them, and those at which the series put the
// result between an `f64` and the one above it also against those two `f64`s.
//
// cos at x = i 2^-26 for i from 1 to 64. The series of cos is alternating, with terms that
// decrease in magnitude for 0 < x <= 1, so that 1 - x^2 / 2 < cos x < 1 - x^2 / 2 + x^4 / 24.
// 1 - x^2 / 2 = 1 - i^2 2^-53 is an `f64`, as it is in [1/2, 1), where the `f64`s are the
// multiples of 2^-53, and x^4 / 24 < 2^-53, as x <= 2^-20, so that cos x is between it and the
// `f64` above it, which is 1 for i = 1.
//
// sin and tan at x = 3 2^-j for j from 1 to 60, which `TINY_HYP` = 2^-26 settles for j >= 28.
// In the same way, x - x^3 / 6 < sin x < x - x^3 / 6 + x^5 / 120 for 0 < x <= 1, and
// x + x^3 / 3 < tan x < x + x^3 / 3 + x^5 / 4 for 0 < x <= 3/4, from tan x = sin x / cos x and
// the bounds of sin x and cos x by two and by three terms of their series. For j from 15 to 25,
// x - x^3 / 6 = (3 2^(2j + 1) - 9) 2^(-3j - 1) and x + x^3 / 3 = (3 2^(2j) + 9) 2^(-3j) are
// `f64`s, as their odd numerators are below 2^53. They are in [2^(1 - j), 2^(2 - j)), where the
// `f64`s are the multiples of 2^(-j - 51), and x^5 / 4 = 243 2^(-5j) / 4 is below 2^(-j - 51),
// so that sin x and tan x are each between one of them and the `f64` above it. `f64`
// arithmetic computes both exactly, as they are `f64`s.
#[test]
fn close_to_an_f64() {
    let expect = |i: usize, x: f64, lo: f64, hi: f64| {
        let (name, f) = FUNCTIONS[i];
        let (a, b) = (f(x, false), f(x, true));
        assert!(
            a == lo && b == hi,
            "{}({:e}): ({:e}, {:e}) != ({:e}, {:e})",
            name,
            x,
            a,
            b,
            lo,
            hi
        );
    };
    for i in 1..=64 {
        let i = f64::from(i);
        let x = i * pow2(-26);
        for y in around(x, 3) {
            check_all(y);
        }
        let lo = 1.0 - i * i * pow2(-53);
        expect(COS, x, lo, next_up(lo));
        expect(COS, -x, lo, next_up(lo));
    }
    for j in 1..=60 {
        let x = 3.0 * pow2(-j);
        for y in around(x, 3) {
            check_all(y);
        }
        if (15..=25).contains(&j) {
            let s = x - 9.0 * pow2(-3 * j - 1);
            let t = x + 9.0 * pow2(-3 * j);
            expect(SIN, x, s, next_up(s));
            expect(SIN, -x, -next_up(s), -s);
            expect(TAN, x, t, next_up(t));
            expect(TAN, -x, -next_up(t), -t);
        }
    }
}

// The hardest arguments that four searches found, as (function, x): those at which `ziv`
// first settles a direction at level 2 (`ziv_at::<N>` for N = 1, 2, 4, .., 64 limbs). None of
// the searches found an argument that needs a level above 2.
// - The first ran the three functions at each level from 1 to 64 limbs, in both directions, at
//   21 arguments: 14 ordinary ones of magnitude from 10^-5 to 10^22, 10^300, `f64::MAX`, the
//   case of Kahan and McDonald, F, F/2, 6134899525417045 and 2^-26, where F and F/2 are the
//   `f64`s nearest π and π/2. Every other direction settled at level 1.
// - The second took the 8 `f64`s nearest to a multiple of π/2 in each binade [2^e, 2^(e + 1))
//   for e from 0 to 1023, which it found from continued fractions.
// - The third ran larger versions of the families of `close_to_an_f64` and
//   `nearest_to_multiples`, and the arguments of the tests of MPFR (those of `mpfr_cases`) and
//   of pxfm.
// - The fourth drew 2^24 random arguments from each of six sets: uniform in [-10, 10) and in
//   [-π/4, π/4), log-uniform from 2^-30 and from 2^60 up, any finite `f64`, and the `f64`s
//   nearest to random multiples of π/2.
// Each comment gives the bits that its case needs, -log2 of the distance from f(x) to the
// nearest `f64` relative to |f(x)|, with MPFR at 2048 bits, and its levels down and up.
const HARD_CASES: [(usize, f64); 19] = [
    (SIN, 5.319372648326541e255), // 6381956970095103 2^797: 122.8 bits, level 2 down, 1 up.
    (SIN, std::f64::consts::FRAC_PI_2), // F/2: 108.7 bits, level 2 down, 1 up.
    (COS, std::f64::consts::PI),  // F: 106.7 bits, level 1 down, 2 up.
    // The "worst case on 53 bits" of sin in MPFR's `tsin.c`, close to a multiple of π: 107.5
    // bits, level 1 down, 2 up.
    (COS, 6.134899525417045e15),
    (COS, 1.4901161193847656e-8), // 2^-26: 108.6 bits, level 1 down, 2 up.
    (TAN, 5.5e0),                 // 61.9 bits, level 2 both ways.
    // Of the second search, close to a multiple of π/2. The `f64` nearest 29π/2, which is the
    // nearest to a nonzero multiple of π/2 that the search found after the case of Kahan and
    // McDonald, at 2^-60.5: 122.0 bits, level 2 down, 1 up.
    (SIN, 4.5553093477052e1),      // 3205513981387887 2^-46
    (COS, 9.1106186954104e1),      // Its double: 120.0 bits, level 1 down, 2 up.
    (COS, 1.0638745296653083e256), // 6381956970095103 2^798: 120.8 bits, level 1 down, 2 up.
    (COS, 2.1277490593306166e256), // 6381956970095103 2^799: 118.8 bits, level 2 down, 1 up.
    (SIN, 1.446117667027838e7),    // 7763785107565477 2^-29: 119.1 bits, level 1 down, 2 up.
    (SIN, 3.576149729694266e39),   // 5916243447979695 2^79: 118.9 bits, level 1 down, 2 up.
    // Of the second search too, with results close to 0 or of tan, which are hard to round by
    // chance, not by the reduction.
    (TAN, 1.4683145432691257e10),  // 65.6 bits, level 2 both ways.
    (COS, 3.9446795267527314e226), // 64.7 bits, level 2 both ways.
    (SIN, 4.108275769650464e178),  // 63.4 bits, level 2 both ways.
    // Of the third search: the negation of an argument of tan in the tests of pxfm,
    // 3040685725624191 2^5, at 2^-50.9 from a multiple of π: 102.8 bits, level 2 down, 1 up.
    (COS, 9.730194321997411e16),
    (TAN, 6.75678039970825e4), // Near 43015π/2: 71.7 bits, level 2 both ways.
    (TAN, 8.940696716308584e-8), // 3 2^-25 - 7 2^-76: 101.7 bits, level 2 both ways.
    // Of the fourth search: of the arguments of tan that it found, the one that needs the most
    // bits, 79.2, level 2 both ways.
    (TAN, 6.3533203123387895e4),
];

// Each case and its negation.
#[test]
fn hard_cases() {
    for (i, x) in HARD_CASES {
        check(i, x);
        check(i, -x);
    }
}

#[test]
fn random_arguments() {
    let mut rng = Rng(73);
    for _ in 0..2000 {
        // Of any exponent, from the bits of a positive finite `f64`, and its negation.
        check_all(f64::from_bits(rng.below(0x7ff0_0000_0000_0000)));
        // Uniform in [-10, 10).
        let u = rng.below(1 << 53) as f64 / (1u64 << 52) as f64 - 1.0;
        for i in [SIN, COS, TAN] {
            check(i, 10.0 * u);
        }
    }
    for _ in 0..2000 {
        // Huge: log-uniform in [2^60, 2^1024), with a random sign.
        for i in [SIN, COS, TAN] {
            check(i, random_sign(&mut rng) * log_uniform(&mut rng, 60, 1023));
        }
    }
}

#[cfg(feature = "gmp")]
mod mpfr {
    use super::*;
    use crate::mpfr_calls::*;

    type Mpfr = fn(f64) -> f64;

    const MPFR: [(Mpfr, Mpfr); 3] = [(sin_rd, sin_ru), (cos_rd, cos_ru), (tan_rd, tan_ru)];

    fn same(a: f64, b: f64) -> bool {
        a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan())
    }

    // `lo` and `hi`, which the function `i` gave at `x`, are MPFR's roundings, or NaN where
    // MPFR gives NaN.
    pub(super) fn check(i: usize, x: f64, lo: f64, hi: f64) {
        let (want_lo, want_hi) = (MPFR[i].0(x), MPFR[i].1(x));
        assert!(
            same(lo, want_lo) && same(hi, want_hi),
            "{}({:e}): ({:e}, {:e}) != MPFR's ({:e}, {:e})",
            FUNCTIONS[i].0,
            x,
            lo,
            hi,
            want_lo,
            want_hi
        );
    }

    // The `f64`s x nearest to k π/2 and the 3 `f64`s on each side of each, both signs of them,
    // for two random k at each exponent e from 0 to 1023: k is y / (π/2) rounded to an integer,
    // for a y of `log_uniform` at e. For small e, the `f64`s around x are close to k π/2 too, as
    // they are 2^(e - 52) apart, and tan is huge at those of an odd k. With π to 1,300 bits, the
    // computed k π/2 is within 2^-275 of k π/2, as k π/2 < 2^1024, so that x is the `f64` nearest
    // to k π/2 unless that is as close to the midpoint of two `f64`s, and is next to it otherwise.
    #[test]
    fn nearest_to_multiples() {
        use rug::{float::Constant, Float};
        const PREC: u32 = 1300;
        let half_pi = Float::with_val(PREC, Constant::Pi) / 2u32;
        let mut rng = Rng(732);
        for e in 0..=1023 {
            for _ in 0..2 {
                let y = Float::with_val(PREC, log_uniform(&mut rng, e, e));
                let k = (y / &half_pi).to_integer().unwrap();
                let x = Float::with_val(PREC, &half_pi * &k).to_f64();
                for z in around(x, 3) {
                    check_all(z);
                }
            }
        }
    }
}

mod levels;
mod mpfr_cases;
