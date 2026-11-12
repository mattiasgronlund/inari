// Tests of the trigonometric functions of the dyadic kernel. Every generator runs on every
// platform through `check`, which checks that the two directions give the same `f64` or two
// adjacent ones, or NaN for both, and that the function of `NEAR`, which rounds to nearest,
// gives one of them, or NaN where they do. On 64-bit Linux and macOS, where the tests have
// MPFR, it also compares the three roundings with the functions of `src/mpfr_calls/mpfr.rs`
// that compute the same function with MPFR, which they have to agree with bit for bit. The
// generator of the `f64`s nearest to multiples of π/2 needs π to more bits than an `f64` has,
// so it runs only where the tests have MPFR.

use super::*;
use crate::dyadic::fast::{fast_counts, reset_fast_counts, set_fast_path};
use crate::dyadic::tests::Rng;

type Directed = fn(f64, bool) -> f64;

const SIN: usize = 0;
const COS: usize = 1;
const TAN: usize = 2;

const FUNCTIONS: [(&str, Directed); 3] = [("sin", sin), ("cos", cos), ("tan", tan)];

type Near = fn(f64) -> f64;

// The functions of `FUNCTIONS` rounded to nearest, in the same order. They skip the rules of
// `sin_small`, `cos_small` and `tan_small`, and below their tiny threshold, `TINY_NEAR` =
// 2^-27, give x for sin and tan and 1 for cos.
const NEAR: [Near; 3] = [sin_near, cos_near, tan_near];

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

// `near`, the rounding to nearest of the number that `lo` and `hi` round, is one of them, or NaN
// if they are. This holds for zeros too: a number of magnitude at most 2^-1075 rounds to
// nearest to the zero of its sign, which the direction toward 0 also gives.
fn check_near(name: &str, x: f64, lo: f64, hi: f64, near: f64) {
    let ok = if lo.is_nan() {
        near.is_nan()
    } else {
        near.to_bits() == lo.to_bits() || near.to_bits() == hi.to_bits()
    };
    assert!(
        ok,
        "{}({:e}): {:e} to nearest, outside ({:e}, {:e})",
        name, x, near, lo, hi
    );
}

// Checks the function `i` at `x` in both directions and to nearest, as the header says.
fn check(i: usize, x: f64) {
    let (name, f) = FUNCTIONS[i];
    let (lo, hi) = (f(x, false), f(x, true));
    let near = NEAR[i](x);
    check_pair(name, x, lo, hi);
    check_near(name, x, lo, hi, near);
    #[cfg(all(
        target_pointer_width = "64",
        any(target_os = "linux", target_os = "macos")
    ))]
    {
        mpfr::check(i, x, lo, hi);
        mpfr::check_near(i, x, near);
    }
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

// The `f64` m 2^(be - 1075), for a biased exponent `be` in [1, 2046] and an m in
// [2^52, 2^53): its bits are those of `be` and of m without its leading bit.
fn from_parts(be: u64, m: u128) -> f64 {
    assert!((1 << 52..1 << 53).contains(&m), "{}", m);
    f64::from_bits(be << 52 | (m - (1 << 52)) as u64)
}

// The least m with m^2 >= n, for n < 2^106. The square root in `f64` is within a few units of
// it, as n has fewer than 2^53 units of 2^53.
fn ceil_sqrt(n: u128) -> u128 {
    let mut m = (n as f64).sqrt() as u128;
    while m * m < n {
        m += 1;
    }
    while m > 0 && (m - 1) * (m - 1) >= n {
        m -= 1;
    }
    m
}

// The least m with m^3 >= n 2^64, for n < 2^95. m^3 >= n 2^64 if and only if h >= n for
// m^3 = h 2^64 + l (`cube`), as l < 2^64.
fn ceil_cbrt(n: u128) -> u128 {
    let mut m = (n as f64 * pow2(64)).cbrt() as u128;
    while cube(m).0 < n {
        m += 1;
    }
    while m > 0 && cube(m - 1).0 >= n {
        m -= 1;
    }
    m
}

// The rule of small arguments of the function `i` at `x`: `sin_small`, `cos_small` at |x|,
// as `cos` takes it, or `tan_small`.
fn small(i: usize, x: f64, up: bool) -> Option<f64> {
    match i {
        SIN => sin_small(x, up),
        COS => cos_small(x.abs(), up),
        _ => tan_small(x, up),
    }
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
    // The same to nearest.
    for x in [0.0, -0.0] {
        assert_eq!(sin_near(x).to_bits(), x.to_bits());
        assert_eq!(tan_near(x).to_bits(), x.to_bits());
        assert_eq!(cos_near(x), 1.0);
    }
    for x in [f64::INFINITY, f64::NEG_INFINITY, f64::NAN] {
        for f in NEAR {
            assert!(f(x).is_nan());
        }
    }
}

// Each rule and the reduction at its threshold and the 3 `f64`s on each side of it, both signs
// of them: `TINY_HYP` = 2^-26 for the three functions, at which the rules of small arguments
// take over from those of tiny ones, the bounds of their ranges, 2^-14 for `cos_small` and
// `tan_small` and 2^-13 for `sin_small`, and `NO_REDUCE` and π/4, between which the reduction
// starts with k = 0. For the roundings to nearest: `TINY_NEAR` = 2^-27, below which they give x
// for sin and tan and 1 for cos, and the arguments past which x or 1 is no longer the nearest
// `f64`, where the test also checks that the third `f64` below gives x or 1 and the third above
// does not:
// - sin at ∛3 2^-26, where x^3 / 6 = 2^-79 is half the gap from x to the `f64` below it, as x
//   is in (2^-26, 2^-25), and x - x^3 / 6 < sin x < x - x^3 / 6 + x^5 / 120.
// - cos at 2^-26 / √2, where t^2 / 2 = 2^-54 is half the gap from 1 to the `f64` below it, and
//   1 - t^2 / 2 < cos t < 1 - t^2 / 2 + t^4 / 24.
// - tan at ∛6 2^-27 = ∛3 2^(-80/3), where x^3 / 3 = 2^-80 is half the gap from x to the `f64`
//   above it, as x is in (2^-27, 2^-26), and x + x^3 / 3 < tan x < x + x^3 / 3 + x^5 / 4.
// The test computes each argument to within about an `f64`, so the third `f64`s on each side
// are at least 2 gaps from it, a relative distance of at least 2^-52. That moves x^3 or t^2 by
// at least 6 2^-53 or 4 2^-53 of it, more than the last term of its bounds, x^5 / 120, t^4 / 24
// or x^5 / 4, so the result at each of them is on the side of the midpoint that the `f64` is on
// of the argument.
#[test]
fn rules_at_their_thresholds() {
    for t in [
        TINY_NEAR,
        TINY_HYP,
        pow2(-14),
        pow2(-13),
        NO_REDUCE,
        std::f64::consts::FRAC_PI_4,
    ] {
        for x in around(t, 3) {
            check_all(x);
        }
    }
    for (i, t) in [
        (SIN, 3f64.cbrt() * pow2(-26)),
        (COS, pow2(-26) / 2f64.sqrt()),
        (TAN, 6f64.cbrt() * pow2(-27)),
    ] {
        let tiny = |x: f64| if i == COS { 1.0 } else { x };
        let below = next_down(next_down(next_down(t)));
        let above = next_up(next_up(next_up(t)));
        let name = FUNCTIONS[i].0;
        assert_eq!(NEAR[i](below), tiny(below), "{}({:e})", name, below);
        assert_ne!(NEAR[i](above), tiny(above), "{}({:e})", name, above);
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

// The short dyadics from 2^-26 to 2^-12, as `check_all` checks them: 2^-k for k from 12 to 26
// and the 3 `f64`s on each side of each, and t = m 2^-26 for m from 1 to 4096, at which cos is
// also checked against the two `f64`s that hold it. Literals and bisection give arguments of
// this kind, and the rules of small arguments meet the cases that they leave to `ziv` at them.
// 1. t^2 / 2 = m^2 2^-53 is a multiple of 2^-53, so that 1 - t^2 / 2 is an `f64`, and cos t
//    lies above it by less than t^4 / 24 <= 2^-56 / 24, as in `close_to_an_f64`. That is
//    below 2^-64, the unit of a `Dyadic<1>` in [1/2, 1), for t <= 2^-15. `cos_small` settles
//    these centres for t < 2^-14 (`small_rules_near_their_centres`).
// 2. sin t < t < tan t, so that sin t is in the binade below t at the powers of 2, where
//    `sin_small` falls through, as the test checks, and tan t can be in the binade above t at
//    the `f64`s just below them, where `tan_small` falls through.
#[test]
fn short_dyadics() {
    for k in 12..=26 {
        let x = pow2(-k);
        for y in around(x, 3) {
            check_all(y);
        }
        if k >= 14 {
            assert_eq!(sin_small(x, false), None, "sin_small({:e})", x);
        }
    }
    for m in 1..=4096 {
        let m = f64::from(m);
        let x = m * pow2(-26);
        check_all(x);
        let lo = 1.0 - m * m * pow2(-53);
        for y in [x, -x] {
            assert_eq!(
                (cos(y, false), cos(y, true)),
                (lo, next_up(lo)),
                "cos({:e})",
                y
            );
        }
    }
}

// n 2^-26 and the 255 `f64`s on each side of it for n from 1 to 8, as `check_all` checks them.
// For t = n 2^-26 + i u, with u the ulp of t, at most 2^-75, and |i| <= 255:
// 1. t^2 / 2 - n^2 2^-53 = n 2^-26 i u + (i u)^2 / 2 is below 2^-90 in magnitude, and
//    0 < cos t - (1 - t^2 / 2) < t^4 / 24 < 2^-96, so that cos t is within 2^-89 of the `f64`
//    1 - n^2 2^-53.
// 2. At n = 6, t is near 3 2^-25, where t - t^3 / 6 and t + t^3 / 3 are the `f64`s t - 9 u and
//    t + 18 u (`close_to_an_f64`). t^3 / 3 is within 255 t^2 u < 2^-38 u of 18 u at the others,
//    and sin t and tan t are within 2^-37 u of t - 9 u and t + 18 u.
#[test]
fn grid() {
    for n in 1..=8 {
        for x in around(f64::from(n) * pow2(-26), 255) {
            check_all(x);
        }
    }
}

// The 2^12 `f64`s from the 2^11-th below `TINY_HYP` = 2^-26 to the 2047-th above it, as
// `check_all` checks them: there the rules of tiny arguments hand over to those of small
// arguments. For t = 2^-26 (1 + i 2^-52) with i from 1 to 2047,
// t^2 / 2 = 2^-53 + i 2^-104 + i^2 2^-157, so that cos t is below the `f64` 1 - 2^-53 by about
// i 2^-104, and 2^-26 is the centre with m = 1 of `short_dyadics`.
#[test]
fn near_tiny_hyp() {
    let b = TINY_HYP.to_bits();
    for i in 0..4096 {
        check_all(f64::from_bits(b + i - 2048));
    }
}

// sin and tan, and cos with them, at t = 3 j 2^-e for the odd j from 1 to 255 and each e that
// puts t in [2^-27, 2^-12), as `check_all` checks them. t^3 / 6 = 9 j^3 2^-(3 e + 1) and
// t^3 / 3 = 9 j^3 2^-3e have few bits, so that t - t^3 / 6 and t + t^3 / 3 are `f64`s where
// they are multiples of the ulp u of t, as for j = 1 and e from 15 to 25
// (`close_to_an_f64`), and lie a fraction of u with few bits from one otherwise. These are
// centres of `sin_small` and `tan_small`. `grid` has 3 2^-25 and the 255 `f64`s on each side
// of it.
#[test]
fn sin_and_tan_centres() {
    for j in (1..=255).step_by(2) {
        for e in 1..=40 {
            let x = f64::from(3 * j) * pow2(-e);
            if (pow2(-27)..pow2(-12)).contains(&x) {
                check_all(x);
            }
        }
    }
}

// The rules of small arguments at their centres, and at the arguments next to the centres in
// each binade of their ranges, where they fall through to `ziv` or settle results close to
// `f64`s.
// 1. `cos_small` settles cos at m 2^-26 for m from 1 to 4095 with the `f64`s of
//    `short_dyadics`, as r = 0 in its comment, `sin_small` sin at 3 2^-e for e from 15 to 25
//    and `tan_small` tan for e from 16 to 25 with those of `close_to_an_f64`. 3 2^-15 is
//    above 2^-14, the bound of `tan_small`.
// 2. A search in each binade, with t = m 2^(be - 1075) as in `cos_small`. cos t is above
//    1 - t^2 / 2 by less than t^4 / 24, and is close to the `f64` 1 - k 2^-53 where t^2 / 2
//    is just above k 2^-53, for m^2 just above k 2^s: the search takes m = ⌈√(k 2^s)⌉ for the
//    first 64 integers k at which m is in [2^52, 2^53), or for all of them in the binades
//    that have fewer. sin t is above t - t^3 / 6 by less than t^5 / 120, and close to an
//    `f64` where t^3 / 6 = c u, with u the ulp of t, is just
//    above an integer multiple C u, for m^3 just above 6 C 2^(s + 64), with s as in
//    `sin_small`: the search takes m = ⌈∛(6 C 2^(s + 64))⌉ for the first 64 integers C at
//    which m is in [2^52, 2^53), or for all of them where there are fewer. tan t is above
//    t + t^3 / 3 by less than t^5 / 4, and close to
//    an `f64` where t^3 / 3 is just below C u, for m^3 just below 3 C 2^(s + 64), next to the
//    m = ⌈∛(3 C 2^(s + 64))⌉ that the search takes. It checks each such m and the `f64`s next
//    to it, both signs of them, as `check` checks them, and that each rule falls through at
//    some of them.
// 3. Cases of the search at which the rules fall through (`SMALL_FALL_THROUGH`).
#[test]
fn small_rules_near_their_centres() {
    for m in 1..4096 {
        let m = f64::from(m);
        let x = m * pow2(-26);
        let lo = 1.0 - m * m * pow2(-53);
        for y in [x, -x] {
            let got = (cos_small(y.abs(), false), cos_small(y.abs(), true));
            assert_eq!(got, (Some(lo), Some(next_up(lo))), "cos_small({:e})", y);
        }
    }
    for e in 15..=25 {
        let x = 3.0 * pow2(-e);
        let s = x - 9.0 * pow2(-3 * e - 1);
        let t = x + 9.0 * pow2(-3 * e);
        let got = [false, true].map(|up| [x, -x].map(|y| sin_small(y, up)));
        let want = [[Some(s), Some(-next_up(s))], [Some(next_up(s)), Some(-s)]];
        assert_eq!(got, want, "sin_small({:e})", x);
        let got = [false, true].map(|up| [x, -x].map(|y| tan_small(y, up)));
        let want = if e >= 16 {
            [[Some(t), Some(-next_up(t))], [Some(next_up(t)), Some(-t)]]
        } else {
            [[None; 2]; 2]
        };
        assert_eq!(got, want, "tan_small({:e})", x);
    }
    // The bound of the range of the rule of small arguments of the function `i`.
    let bound = |i: usize| pow2(if i == SIN { -13 } else { -14 });
    let mut fell = [0; 3];
    let mut near = |i: usize, be: u64, m: u128| {
        for x in around(from_parts(be, m), 1) {
            for y in [x, -x] {
                check(i, y);
                if (TINY_HYP..bound(i)).contains(&x) && small(i, y, false).is_none() {
                    fell[i] += 1;
                }
            }
        }
    };
    for be in 997..=1008 {
        let s = 2098 - 2 * be;
        let k0 = 1u128 << (104 - s);
        for k in k0..(k0 + 64).min(4 * k0) {
            near(COS, be, ceil_sqrt(k << s));
        }
    }
    for (i, f, last) in [(SIN, 6, 1009), (TAN, 3, 1008)] {
        for be in 997..=last {
            let s = 2086 - 2 * be;
            // The least C with C f 2^(s + 64) >= 2^156, and so m >= 2^52.
            let c0 = ((1u128 << (92 - s)) + f - 1) / f;
            for c in (c0.max(1)..c0.max(1) + 64).take_while(|c| (c * f) << s < 1 << 95) {
                near(i, be, ceil_cbrt((c * f) << s));
            }
        }
    }
    for i in [SIN, COS, TAN] {
        assert!(fell[i] > 0, "{}", FUNCTIONS[i].0);
    }
    for (i, x) in SMALL_FALL_THROUGH {
        for y in [x, -x] {
            assert_eq!(small(i, y, false), None, "{}({:e})", FUNCTIONS[i].0, y);
            check(i, y);
        }
    }
}

// Arguments at which the rules of small arguments fall through to `ziv`, which the search of
// `small_rules_near_their_centres` found, as (function, x): all those that it found in the
// binade [2^-26, 2^-25). The search does not take sin at 2^-26, at which `sin_small` falls
// through too (`short_dyadics`). Each comment gives the bits that its case needs and
// its levels down and up, as those of `HARD_CASES` do.
const SMALL_FALL_THROUGH: [(usize, f64); 5] = [
    (COS, 2.1073424255447017e-8), // ⌈√2 2^52⌉ 2^-78: 105.2 bits, level 2 down, 1 up.
    (COS, 2.580956827951785e-8),  // ⌈√3 2^52⌉ 2^-78: 104.8 bits, level 2 down, 1 up.
    (SIN, 2.7077206862451727e-8), // ⌈∛6 2^52⌉ 2^-78: 108.4 bits, level 2 both ways.
    (TAN, 2.149119332890821e-8),  // ⌈∛3 2^52⌉ 2^-78 - 2^-78: 108.2 bits, level 2 both ways.
    (TAN, 2.7077206862451724e-8), // ⌈∛6 2^52⌉ 2^-78 - 2^-78: 105.9 bits, level 2 both ways.
];

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
    // 2^-26: 108.6 bits, level 1 down, 2 up. `cos_small` settles it now, before `ziv`.
    (COS, 1.4901161193847656e-8),
    (TAN, 5.5e0), // 61.9 bits, level 2 both ways.
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
    // 3 2^-25 - 7 2^-76: 101.7 bits, level 2 both ways. `tan_small` falls through at it, as
    // t^3 / 3 is just below 18 ulps of t.
    (TAN, 8.940696716308584e-8),
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

// A random argument of the fast path: uniform in [-`LIMIT`, `LIMIT`) if `wide`, as
// -2^16 + k 2^-36 for a k uniform in [0, 2^53), which is exact, and otherwise of an exponent
// uniform in [-27, 15] and a random sign, so that 2^-27 <= |x| < 2^16.
fn fast_arg(rng: &mut Rng, wide: bool) -> f64 {
    if wide {
        -LIMIT + rng.below(1 << 53) as f64 * pow2(-36)
    } else {
        random_sign(rng) * log_uniform(rng, -27, 15)
    }
}

// The three roundings of the function `i` at `x`: down, up and to nearest.
fn roundings(i: usize, x: f64) -> [f64; 3] {
    let f = FUNCTIONS[i].1;
    [f(x, false), f(x, true), NEAR[i](x)]
}

// The function `i` gives the same `f64`s at `x` in its three roundings with the fast path as with
// it disabled, and those `f64`s are MPFR's where the tests have MPFR, as `check` checks them.
fn check_fast(i: usize, x: f64) {
    let fast = roundings(i, x);
    set_fast_path(false);
    let kernel = roundings(i, x);
    set_fast_path(true);
    assert!(
        fast.iter()
            .zip(&kernel)
            .all(|(a, b)| a.to_bits() == b.to_bits()),
        "{}({:e}): {:?} with the fast path != {:?} without it",
        FUNCTIONS[i].0,
        x,
        fast,
        kernel
    );
    check(i, x);
}

// sin, cos and tan give the same `f64`s, in both directions and to nearest, with the fast path
// as with it disabled, on random arguments of its range, and most of its rounding tests pass.
#[test]
fn fast_path_agrees_with_kernel() {
    let mut rng = Rng(90);
    for i in [SIN, COS, TAN] {
        reset_fast_counts();
        for k in 0..4000 {
            check_fast(i, fast_arg(&mut rng, k % 2 == 0));
        }
        let (passed, failed) = fast_counts();
        assert!(
            passed > 100 * failed && passed > 5000,
            "{}: {passed} passed, {failed} failed",
            FUNCTIONS[i].0
        );
    }
}

// sin, cos and tan on random arguments of the fast path, as `check` checks them (against MPFR
// where the tests have it): uniform over its range, and of each exponent from -27 to 15. Most of
// its rounding tests pass on both sets.
#[test]
fn fast_range_random() {
    let mut rng = Rng(901);
    for i in [SIN, COS, TAN] {
        let mut counts = [(0, 0); 2];
        for (wide, c) in [true, false].into_iter().zip(&mut counts) {
            reset_fast_counts();
            for _ in 0..20_000 {
                check(i, fast_arg(&mut rng, wide));
            }
            *c = fast_counts();
        }
        assert!(
            counts.iter().all(|&(p, f)| p > 100 * f && p > 20_000),
            "{}: (passed, failed) = {:?} on uniform arguments and on the others",
            FUNCTIONS[i].0,
            counts
        );
    }
}

// u = π/4096, the step of the reduction of the fast path, rounded to an `f64`: RN(π)/4096 is
// RN(π/4096), as 4096 is a power of 2.
const STEP: f64 = std::f64::consts::PI / 4096.0;

// The integer n of the reduction of the fast path at `x`, for |x| < `LIMIT`.
fn reduced(x: f64) -> i64 {
    fast_reduce(x).unwrap().0
}

// Whether the fast paths of sin, cos and tan all decline `x`, before any rounding test: cos at
// |x|, as `cos` takes it.
fn declined(x: f64) -> bool {
    fast_sin(x).is_none() && fast_cos(x.abs()).is_none() && fast_tan(x).is_none()
}

// Whether the fast paths of sin, cos and tan all take `x`, before any rounding test, as
// `declined` reads them.
fn answered(x: f64) -> bool {
    fast_sin(x).is_some() && fast_cos(x.abs()).is_some() && fast_tan(x).is_some()
}

// The n = 2048 q + i of items 1 and 2 of `reduction_edges`: q from 0 to 3 and on across the
// range of the fast path, and i = 0 and next to the ends of [1, 2047], to the multiples of 64 and
// to 1024, where (n + 1) u is below `LIMIT` too.
fn edge_ns() -> Vec<i64> {
    let mut qs: Vec<i64> = (0..4).chain((4..41_721).step_by(701)).collect();
    qs.push(41_721);
    let mut ns = vec![];
    for q in qs {
        for i in [
            0, 1, 2, 63, 64, 65, 127, 128, 1024, 1983, 1984, 1985, 2046, 2047,
        ] {
            let n = 2048 * q + i;
            if ((n + 1) as f64 * STEP) < LIMIT {
                ns.push(n);
            }
        }
    }
    ns
}

// The (n, x) of item 3 of `reduction_edges`: x = n (U1 + U2) for n = m 2^k with m in
// {1, 3, 5, 7}, where x is below `LIMIT`.
fn exact_rh() -> Vec<(i64, f64)> {
    let u12 = f64::from_bits(U1) + f64::from_bits(U2);
    let mut v = vec![];
    for m in [1, 3, 5, 7] {
        for k in 0..27 {
            let n: i64 = m << k;
            let x = n as f64 * u12;
            if x < LIMIT {
                v.push((n, x));
            }
        }
    }
    v
}

// The fast path of the function `i` at `x`, before its rounding test: cos at |x|, as `cos` takes
// it.
fn fast_parts(i: usize, x: f64) -> Option<(f64, f64)> {
    match i {
        SIN => fast_sin(x),
        COS => fast_cos(x.abs()),
        _ => fast_tan(x),
    }
}

// The reduction of the fast path at its edges, and sin, cos and tan there, both signs of each
// argument, as `check_fast` checks them. The reduction writes x = n u + ρ, and with
// n = 2048 q + i, x is i u + ρ past q π/2.
// 1. At RN(n u) and the 2 `f64`s on each side of it, the reduction gives n, for q from 0 to 3
//    and on across the range, and for i = 0 and next to the ends of [1, 2047] and to the
//    multiples of 64, where `fast_sc` takes a row of `SC1` alone, a row of `SC2` alone or one of
//    each, and at 1024, where i u = π/4. At i = 0 and n != 0, x is close to q π/2, where sin,
//    cos or tan is close to 0 or has a pole, and `fast_band` and `fast_tan_band` take x.
// 2. Next to RN((n + 1/2) u), where |ρ| is at its largest, u/2, the reduction gives n on one side
//    and n + 1 on the other, and nothing else among the 8 `f64`s on each side of it. The n = 0
//    of `fast_sin0` and `fast_cos0` meets n = 1 at u/2.
// 3. At x = n (U1 + U2) for n = m 2^k with m in {1, 3, 5, 7}, an `f64`, as U1 + U2 is an odd
//    multiple of 2^-60 below 2^-10 and m < 8, the reduction gives n and rh = x - n U1 - n U2 = 0,
//    and the fast paths decline x, other than at n mod 2048 = 0, where `fast_band` and
//    `fast_tan_band` take x.
// 4. Around `LIMIT`, at and above which `fast_reduce_big` takes x instead of `fast_reduce`.
#[test]
fn reduction_edges() {
    for n in edge_ns() {
        let x = n as f64 * STEP;
        for y in around(x, 2) {
            assert_eq!(reduced(y), n, "{y:e}");
            assert_eq!(reduced(-y), -n, "{:e}", -y);
            assert!(
                n % 2048 != 0 || n == 0 || (answered(y) && answered(-y)),
                "{y:e}"
            );
            for j in [SIN, COS, TAN] {
                check_fast(j, y);
                check_fast(j, -y);
            }
        }
        let x = (n as f64 + 0.5) * STEP;
        let ns: Vec<i64> = around(x, 8).into_iter().map(reduced).collect();
        assert!(
            ns.contains(&n) && ns.contains(&(n + 1)) && ns.iter().all(|&k| k == n || k == n + 1),
            "around {x:e}: {ns:?}"
        );
        for y in around(x, 2) {
            for j in [SIN, COS, TAN] {
                check_fast(j, y);
                check_fast(j, -y);
            }
        }
    }
    let u12 = f64::from_bits(U1) + f64::from_bits(U2);
    assert_eq!(
        u12 - f64::from_bits(U1),
        f64::from_bits(U2),
        "U1 + U2 is not exact"
    );
    for (n, x) in exact_rh() {
        for y in [x, -x] {
            let (got, rh, _, _) = fast_reduce(y).unwrap();
            assert!(
                got == if y > 0.0 { n } else { -n }
                    && rh == 0.0
                    && if n % 2048 == 0 {
                        answered(y)
                    } else {
                        declined(y)
                    },
                "{y:e}: n = {got}, rh = {rh:e}"
            );
            for j in [SIN, COS, TAN] {
                check_fast(j, y);
            }
        }
    }
    for x in [LIMIT, -LIMIT] {
        assert!(
            fast_reduce(x).is_none() && fast_reduce_big(x).is_some(),
            "{x:e}"
        );
        assert!(
            fast_reduce(next_down(x.abs()).copysign(x)).is_some(),
            "{x:e}"
        );
        for y in around(x, 3) {
            for j in [SIN, COS, TAN] {
                check_fast(j, y);
            }
        }
    }
}

// 2^-68, the bound on the error of the scaled h + l that the rounding tests of
// `src/dyadic/fast.rs` assume, and 2^-58, 2^10 times as large.
const FAST_ERR: f64 = 1.0 / 295_147_905_179_352_825_856.0;
const WIDE: f64 = 1.0 / 288_230_376_151_711_744.0;

// sin, cos and tan where a rounding test of the fast path passes, but would fail with `WIDE` in
// place of the bound 2^-68, as `widened` in `src/dyadic/exp/tests.rs` checks e^x: the h + l of
// `fast_unscale`, negated where h < 0, with h in [1, 2), is within 2^-58 of h, which a directed
// rounding cannot cross, or of a midpoint between h and the `f64` next to it, which the rounding
// to nearest cannot cross. There an error in the bound would show first, so the fast path has to
// give the kernel's `f64`s, and MPFR's, as `check_fast` checks them. A narrow pass of the
// directed tests counts only where the rules of tiny and small arguments leave x to the fast
// path. The arguments are those of `fast_arg`, which `fast_reduce` reduces, and of `big_arg`,
// which `fast_reduce_big` reduces, and both kinds need narrow passes of both tests.
#[test]
fn widened() {
    let mut rng = Rng(906);
    for i in [SIN, COS, TAN] {
        // The narrow passes of the directed tests and of the test to nearest, below `LIMIT` and
        // at or above it.
        let mut counts = [[0; 2]; 2];
        for k in 0..6000 {
            let x = match k % 3 {
                0 => fast_arg(&mut rng, true),
                1 => fast_arg(&mut rng, false),
                _ => big_arg(&mut rng),
            };
            let Some((h, l)) = fast_parts(i, x) else {
                continue;
            };
            // The scaled pair, negated where h < 0, as `round_dir_signed` does.
            let (h, l, _) = fast_unscale(h, l);
            let (h, l) = if h < 0.0 { (-h, -l) } else { (h, l) };
            // Half the gap between h and the next `f64` above it, and below it.
            let above = f64::EPSILON / 2.0;
            let below = if h > 1.0 {
                f64::EPSILON / 2.0
            } else {
                f64::EPSILON / 4.0
            };
            let directed =
                x.abs() >= TINY_HYP && small(i, x, false).is_none() && small(i, x, true).is_none();
            let narrow_dir = directed && FAST_ERR < l.abs() && l.abs() <= WIDE;
            let narrow_near = l < above - FAST_ERR
                && l > -(below - FAST_ERR)
                && (l >= above - WIDE || l <= -(below - WIDE));
            if !narrow_dir && !narrow_near {
                continue;
            }
            let c = &mut counts[usize::from(x.abs() >= LIMIT)];
            c[0] += usize::from(narrow_dir);
            c[1] += usize::from(narrow_near);
            check_fast(i, x);
        }
        assert!(
            counts.iter().flatten().all(|&c| c >= 20),
            "{}: {counts:?} narrow passes of the directed tests and of the test to nearest, \
             below `LIMIT` and at or above it",
            FUNCTIONS[i].0
        );
    }
}

// The bits of a reduction, so that two of them compare equal only if their n and the bits of
// their rh, rl and rr are, the signs of zeros included.
fn reduction_bits(r: Option<(i64, f64, f64, f64)>) -> Option<(i64, u64, u64, u64)> {
    r.map(|(n, rh, rl, rr)| (n, rh.to_bits(), rl.to_bits(), rr.to_bits()))
}

// `fast_reduce_any(x)` is `fast_reduce(x)` for |x| < `LIMIT` and `fast_reduce_big(x)` for the
// other x, NaN included. `fast_reduce_big(x)` is `None` unless x is finite with |x| >= `LIMIT`,
// and otherwise meets the conjuncts of `fast_reduce_big_correct` in
// `rocq/theories/FastTrigBig.v` that do not need π: n is in [1, 8191] with n mod 2048 != 0, so
// that `fast_sin`, `fast_cos` and `fast_tan` never take it for the n = 0 of
// |x| <= u/2 (1 + 2^-24), rh, rl and rr are finite, rr = RN(rh + rl), |rl| <= 2^-37 and
// |rh| >= 2^-65. Returns whether `fast_reduce_big` takes x.
fn check_big(x: f64) -> bool {
    let big = fast_reduce_big(x);
    let want = if x.abs() < LIMIT { fast_reduce(x) } else { big };
    assert_eq!(
        reduction_bits(fast_reduce_any(x)),
        reduction_bits(want),
        "fast_reduce_any({x:e})"
    );
    let Some((n, rh, rl, rr)) = big else {
        return false;
    };
    assert!(
        x.is_finite()
            && x.abs() >= LIMIT
            && (1..8192).contains(&n)
            && n & 2047 != 0
            && rh.is_finite()
            && rl.is_finite()
            && rr.is_finite()
            && rr.to_bits() == (rh + rl).to_bits()
            && rl.abs() <= pow2(-37)
            && rh.abs() >= pow2(-65),
        "fast_reduce_big({x:e}) = ({n}, {rh:e}, {rl:e}, {rr:e})"
    );
    true
}

// 6381956970095103 2^797, the `f64` nearest to a multiple of π/2 of Kahan and McDonald (the
// header of `trig.rs`): there i = 0, so that `fast_reduce_big` declines it.
const KM: f64 = 5.319372648326541e255;

// Arguments x = m 2^E at less than 2^-64 from a multiple N u of u = π/4096 with
// i = N mod 2048 != 0, as (x, whether `fast_reduce_big` takes x), each with ρ = x - N u and i,
// from MPFR at 1,400 bits. ρ / u is the F of `fast_reduce_big` up to less than 2^-126.
// `fast_reduce_big` declines x where 0 <= F < 2^-53, that is, up to less than 2^-126 u at either
// end, where 0 <= ρ < 2^-53 u, about 2^-63.35, which a random argument reaches with a chance of
// about 2^-53: there fh, F rounded down to a multiple of 2^-53, is 0, and so is rh. Where
// -2^-53 <= F < 0, fh = -2^-53, and rh and rl, both of about 2^-63.35 in magnitude, nearly
// cancel, which `fast_reduce_big_correct` allows: it takes those x. A search found them from the
// continued fractions of 2^(E + 12) / π: in each binade, x / u = m 2^(E + 12) / π.
const NEAR_STEPS: [(f64, bool); 12] = [
    // 6381956970095103 2^786, the m of `KM` 11 binades lower: ρ = 2^-71.9, i = 1461.
    (2.597349925940694e252, false),
    (1.7461668602022784e36, true), // 5916243447979695 2^68: -2^-69.9, i = 1959.
    (1.91615904031879e295, true),  // 8444920710073313 2^928: -2^-69.8, i = 1205.
    (1.0588239478072454e17, true), // 6617649673795284 2^4: -2^-68.4, i = 159.
    (1.515713510270437e304, true), // 6221301883130153 2^958: -2^-68.1, i = 1091.
    (2.751058338380003e8, true),   // 4615509997160240 2^-24: -2^-66.9, i = 645.
    // 7763785107565477 2^-36, of the lowest binade above `LIMIT`: -2^-66.03, i = 2032.
    (1.1297794273654984e5, true),
    (2.2595588547309968e5, true), // Its double, 7763785107565477 2^-35: -2^-65.03, i = 2016.
    (7.797439572557102e213, false), // 6519508725532052 2^658: 2^-65.002, i = 1879.
    (4.125141702366462e147, false), // 5811667653394439 2^438: 2^-64.997, i = 1395.
    (1.1004233353520012e9, true), // 4615509997160240 2^-22: -2^-64.89, i = 532.
    (2.4838578073150272e14, false), // 7948344983408087 2^-5: 2^-64.81, i = 477.
];

// The positive arguments of `fast_reduce_big` at its edges:
// 1. For each biased exponent be from 1039 to 2046, those of the `f64`s from 2^16 up to
//    `f64::MAX`, m 2^(be - 1075) for m = 2^52, 2^53 - 1 and a random m between. Its window of
//    `INV2PI` starts at bit k = be - 1011 from the top, at limb k / 64 shifted by k mod 64, so
//    that these take every limb and every shift.
// 2. 8 random m at k = 64 j - 1, 64 j and 64 j + 1 for j from 1 to 16, where the shift wraps
//    from 63 to 0 and the window moves to the next limb.
// 3. The 3 `f64`s on each side of `LIMIT` and of `KM`, and the 4 largest `f64`s.
// 4. The x of `NEAR_STEPS`.
fn big_edge_args() -> Vec<f64> {
    let mut rng = Rng(950);
    let mut random_m = || (1 << 52) + u128::from(rng.below(1 << 52));
    let mut v = vec![];
    for be in 1039..=2046 {
        for m in [1 << 52, (1 << 53) - 1, random_m()] {
            v.push(from_parts(be, m));
        }
    }
    for j in 1..=16 {
        for be in [1010, 1011, 1012] {
            for _ in 0..8 {
                v.push(from_parts(be + 64 * j, random_m()));
            }
        }
    }
    v.extend(around(LIMIT, 3));
    v.extend(around(KM, 3));
    let mut x = f64::MAX;
    v.push(x);
    for _ in 0..3 {
        x = next_down(x);
        v.push(x);
    }
    v.extend(NEAR_STEPS.iter().map(|&(x, _)| x));
    v
}

// `fast_reduce_big` and `fast_reduce_any` at the arguments of `big_edge_args` and their
// negations, as `check_big` checks them, and sin, cos and tan there, as `check_fast` checks
// them. Both reductions decline NaN and the infinities, `fast_reduce_big` declines ±`KM` and
// the x of `NEAR_STEPS` with 0 <= ρ < 2^-53 u and their negations, and takes the others of
// `NEAR_STEPS` and most of the other arguments.
#[test]
fn big_reduction_edges() {
    for x in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY, KM, -KM] {
        assert!(!check_big(x), "{x:e}");
    }
    for (x, takes) in NEAR_STEPS {
        for y in [x, -x] {
            assert_eq!(check_big(y), takes, "fast_reduce_big({y:e})");
        }
    }
    let args = big_edge_args();
    let mut taken = 0;
    for &x in &args {
        for y in [x, -x] {
            taken += usize::from(check_big(y));
            for i in [SIN, COS, TAN] {
                check_fast(i, y);
            }
        }
    }
    assert!(
        taken > 2 * args.len() * 99 / 100,
        "fast_reduce_big takes {taken} of {} arguments",
        2 * args.len()
    );
}

// A random argument of `fast_reduce_big`: log-uniform in [2^16, 2^1024), with a random sign.
fn big_arg(rng: &mut Rng) -> f64 {
    random_sign(rng) * log_uniform(rng, 16, 1023)
}

// sin, cos and tan on random arguments of `big_arg`, as `check_big` and `check_fast` check them.
// The fast path takes more than 99% of them, and most of its rounding tests pass. It declines
// only the x where `fast_reduce_big` finds |rh| < 2^-65, close to a multiple of u that is not
// one of π/2, as `fast_band_big` and `fast_tan_band_big` take the x where i = 0.
#[test]
fn big_random() {
    let mut rng = Rng(951);
    for i in [SIN, COS, TAN] {
        reset_fast_counts();
        let mut taken = 0;
        for _ in 0..3000 {
            let x = big_arg(&mut rng);
            check_big(x);
            taken += usize::from(fast_parts(i, x).is_some());
            check_fast(i, x);
        }
        let (passed, failed) = fast_counts();
        assert!(
            taken > 2970 && passed > 100 * failed && passed > 15_000,
            "{}: the fast path takes {taken} of 3000 arguments, and its rounding tests passed \
             {passed} times and failed {failed} times",
            FUNCTIONS[i].0
        );
    }
}

// RN(π/2 - RN(π/2)), the part of π/2 below `FRAC_PI_2`.
const HALF_PI_LO: f64 = 6.123233995736766e-17;

// The largest k with k π/2 below `LIMIT`: 41721 π/2 is about 65535.4.
const LAST_K: i64 = 41_721;

// RN(k π/2) for k in [1, `LAST_K`], or an `f64` next to it. p + e is k RN(π/2) exactly
// [Dekker], and p + RN(e + RN(k `HALF_PI_LO`)) is within 2^-89 of k π/2: k (π/2 - RN(π/2) -
// `HALF_PI_LO`) and the errors of the two roundings, of numbers below 2^-37, are each at most
// 2^-91. So the result is RN(k π/2) unless k π/2 is within 2^-89 of the midpoint of two
// `f64`s, and `mpfr::band_reductions` checks that it is RN(k π/2) for every such k.
fn near_multiple(k: i64) -> f64 {
    let (kf, h) = (k as f64, std::f64::consts::FRAC_PI_2);
    let p = kf * h;
    p + (two_prod_err::<HAS_FMA>(kf, h, p) + kf * HALF_PI_LO)
}

// What gives the function `i` at `x` in the rounding `r` of `roundings` (0 down, 1 up and 2 to
// nearest), for an x that its fast path takes and that no rule of `small` takes: 0 for the
// rounding test of the fast path, 1 for `fast_one_dir`, which sin and cos take in a direction
// where that test fails, and 2 for neither, where the kernel computes the result.
fn band_outcome(i: usize, x: f64, r: usize) -> usize {
    let (h, l) = fast_parts(i, x).unwrap();
    let up = r == 1;
    let passed = if r == 2 {
        fast_round_near(h, l).is_some()
    } else {
        fast_round_dir(h, l, up).is_some()
    };
    if passed {
        0
    } else if r != 2 && i != TAN && fast_one_dir(h, up).is_some() {
        1
    } else {
        2
    }
}

// sin, cos and tan at RN(k π/2) and the 2 `f64`s on each side of it, both signs of each, for
// every k from 1 to `LAST_K`, as `check_fast` checks them. There x = n u + ρ with n = ±2048 k and
// |ρ| < 2^-35, which the reduction gives and the fast paths take (`fast_band` and
// `fast_tan_band`), and the result is ±sin ρ, ±cos ρ, tan ρ or -1 / tan ρ. The kernel computes
// fewer than 1 in 10,000 of the results of each function. The rounding test of the fast path
// gives the others, but for ±cos ρ in a direction, where cos ρ is within 2^-72 of 1, closer than
// the error bound of the test, 2^-68, and `fast_one_dir` gives every one of those.
#[test]
fn near_multiples() {
    // outcomes[i][o]: the results of the function `i` that `band_outcome` gives o for.
    let mut outcomes = [[0usize; 3]; 3];
    // ±cos ρ is sin at an odd k and cos at an even one, at 10 arguments in 2 directions each.
    let last = usize::try_from(LAST_K).unwrap();
    let cos_half = [20 * ((last + 1) / 2), 20 * (last / 2), 0];
    for k in 1..=LAST_K {
        for y in around(near_multiple(k), 2) {
            for (z, n) in [(y, 2048 * k), (-y, -2048 * k)] {
                assert_eq!(reduced(z), n, "{z:e}");
                assert!(answered(z), "{z:e}");
                for i in [SIN, COS, TAN] {
                    check_fast(i, z);
                    for r in 0..3 {
                        outcomes[i][band_outcome(i, z, r)] += 1;
                    }
                }
            }
        }
    }
    for i in [SIN, COS, TAN] {
        let [test, one, kernel] = outcomes[i];
        assert!(
            one == cos_half[i] && 10_000 * kernel < test + one + kernel,
            "{}: the rounding test gives {test} results, `fast_one_dir` {one} and the kernel \
             {kernel}",
            FUNCTIONS[i].0
        );
    }
}

// sin at an odd k and cos at an even k, at x = RN(k π/2) ± 2^-e and at -x, for e from 25 to 40
// and k from 1 to 16 and at 255, 256, 599 and 600, as `check_fast` checks them. The result is
// ±cos ρ, with ρ = x - k π/2 within 2^-44 of ±2^-e, as RN(k π/2) < 2^10 is within 2^-44 of
// k π/2, and 1 - cos ρ is about 2^(-2e - 1). In a direction, the rounding test of the fast path
// gives the result for e from 27 to 33, where 1 - cos ρ is above the error bound of the test,
// 2^-68, and `fast_one_dir` for e from 34 to 40, where it is below and cos ρ is above
// 1 - 2^-54, so that h = 1. To nearest, the test gives the result for e from 27 to 40.
// At e = 25 and 26, cos ρ is close to the `f64` 1 - 2^(-2e - 1), not to 1, and `fast_one_dir`
// does not take it.
#[test]
fn near_one_edge() {
    // outcomes[e - 25][r]: how many results in the rounding `r` `band_outcome` gives 0, 1 and 2
    // for, of the 80 at each e: 20 k, 2 offsets and 2 signs.
    let mut outcomes = [[[0usize; 3]; 3]; 16];
    for k in (1..=16).chain([255, 256, 599, 600]) {
        let i = if k % 2 == 0 { COS } else { SIN };
        let x = near_multiple(k);
        for (e, c) in (25..=40).zip(&mut outcomes) {
            for y in [x + pow2(-e), x - pow2(-e)] {
                assert_eq!((y - x).abs(), pow2(-e), "{x:e} ± 2^-{e} is not an `f64`");
                for z in [y, -y] {
                    check_fast(i, z);
                    for (r, c) in c.iter_mut().enumerate() {
                        c[band_outcome(i, z, r)] += 1;
                    }
                }
            }
        }
    }
    for (e, c) in (25..=40).zip(&outcomes) {
        let one = usize::from(e >= 34);
        let ok = if e < 27 {
            c[0][1] == 0 && c[1][1] == 0
        } else {
            c[0][one] == 80 && c[1][one] == 80 && c[2][0] == 80
        };
        assert!(ok, "2^-{e}: {c:?}");
    }
}

#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
mod mpfr {
    use super::*;
    use crate::mpfr_calls::mpfr::*;
    use rug::{
        float::{Constant, Round},
        Float, Integer,
    };

    type Mpfr = fn(f64) -> f64;

    const MPFR: [(Mpfr, Mpfr); 3] = [(sin_rd, sin_ru), (cos_rd, cos_ru), (tan_rd, tan_ru)];

    const MPFR_NEAR: [Mpfr; 3] = [sin_rn, cos_rn, tan_rn];

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

    // `near`, which the function `i` gave at `x` to nearest, is MPFR's rounding to nearest, or
    // NaN where MPFR gives NaN.
    pub(super) fn check_near(i: usize, x: f64, near: f64) {
        let want = MPFR_NEAR[i](x);
        assert!(
            same(near, want),
            "{}({:e}): {:e} to nearest != MPFR's {:e}",
            FUNCTIONS[i].0,
            x,
            near,
            want
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

    // The precision of the values that the tables, the constants and the results of the fast
    // path are checked against, far above that of the bounds checked.
    const PREC: u32 = 300;

    // The bits `h` and `l` are those of RN(v) and RN(v - RN(v)), within 2^n of v, with
    // |l| <= 2^-53 h.
    fn check_double(name: &str, h: u64, l: u64, v: &Float, n: i32) {
        let (h, l) = (f64::from_bits(h), f64::from_bits(l));
        assert_eq!(h.to_bits(), v.to_f64().to_bits(), "{name}: {h:e} != RN(v)");
        let rest = Float::with_val(PREC, v - h);
        let mut err = Float::with_val(PREC, &rest - l);
        err.abs_mut();
        assert!(
            l.to_bits() == rest.to_f64().to_bits() && err < pow2(n) && l.abs() <= pow2(-53) * h,
            "{name}: {l:e} != RN(v - h) = {:e}, or |v - h - l| = {:e} is not below 2^{n}, or \
             |l| > 2^-53 h",
            rest.to_f64(),
            err.to_f64()
        );
    }

    // The tables and the constants of the fast path of `trig.rs` are what the comments on them
    // say, with the bounds that `rocq/theories/FastTrigTables.v` proves (`sc1_correct`,
    // `sc2_correct`, `fast_trig_consts`) and, for `U4`, `rocq/theories/FastTrigBandRed.v`
    // (`band_consts`). π is to 300 bits, so that the angles and u = π/4096 are within 2^-280 of
    // theirs.
    #[test]
    fn fast_tables_and_constants() {
        let pi = Float::with_val(PREC, Constant::Pi);
        for (name, table, d) in [("SC1", &SC1[..], 64u32), ("SC2", &SC2[..], 4096)] {
            for (i, row) in table.iter().enumerate() {
                let a: Float = Float::with_val(PREC, &pi * u32::try_from(i).unwrap()) / d;
                let (s, c) = (a.clone().sin(), a.cos());
                check_double(&format!("{name}[{i}] sin"), row[0], row[1], &s, -104);
                check_double(&format!("{name}[{i}] cos"), row[2], row[3], &c, -104);
            }
        }
        let u = Float::with_val(PREC, &pi / 4096);
        // `U1` and `U2` are cut toward 0 to 26 bits, so that their last 27 bits are 0.
        let u1 = Float::with_val_round(26, &u, Round::Zero).0.to_f64();
        assert_eq!(U1, u1.to_bits(), "U1: {:e} != {u1:e}", f64::from_bits(U1));
        let rest = Float::with_val(PREC, &u - u1);
        let u2 = Float::with_val_round(26, &rest, Round::Zero).0.to_f64();
        assert_eq!(U2, u2.to_bits(), "U2: {:e} != {u2:e}", f64::from_bits(U2));
        for b in [U1, U2] {
            assert_eq!(b & ((1 << 27) - 1), 0, "{b:x}");
        }
        let rest = rest - u2;
        let u3 = f64::from_bits(U3);
        assert_eq!(U3, rest.to_f64().to_bits(), "U3: {u3:e} != RN(u - U1 - U2)");
        // u - U1 - U2 - U3, exact to `PREC` bits, as are the differences above.
        let rest = rest - u3;
        let err = Float::with_val(PREC, rest.abs_ref());
        assert!(err < pow2(-120), "|u - U1 - U2 - U3| = {:e}", err.to_f64());
        let u4 = f64::from_bits(U4);
        assert_eq!(
            U4,
            rest.to_f64().to_bits(),
            "U4: {u4:e} != RN(u - U1 - U2 - U3)"
        );
        assert!(u4.abs() <= pow2(-120), "|U4| = {u4:e}");
        let mut err = rest - u4;
        err.abs_mut();
        assert!(
            err <= pow2(-174),
            "|u - U1 - U2 - U3 - U4| = {:e}",
            err.to_f64()
        );
        let inv = Float::with_val(PREC, 4096) / &pi;
        assert_eq!(INV, inv.to_f64().to_bits(), "INV");
        let mut err = Float::with_val(PREC, &u * f64::from_bits(INV)) - 1u32;
        err.abs_mut();
        assert!(err <= pow2(-52), "|INV u - 1| = {:e}", err.to_f64());
        for (name, bits, d) in [("S3", S3, 6), ("S5", S5, 120), ("C4", C4, 24)] {
            let want = Float::with_val(PREC, d).recip().to_f64();
            assert_eq!(bits, want.to_bits(), "{name}: {:e}", f64::from_bits(bits));
        }
        assert_eq!(SHIFTER, 1.5 * pow2(52));
        assert_eq!(LIMIT, pow2(16));
    }

    // The function `i` at `x`, to `PREC` bits.
    fn value(i: usize, x: f64) -> Float {
        let x = Float::with_val(PREC, x);
        match i {
            SIN => x.sin(),
            COS => x.cos(),
            _ => x.tan(),
        }
    }

    // The fast path of the function `i` at `x`, before its rounding test, at x itself for cos
    // too: its core takes either sign.
    fn core(i: usize, x: f64) -> Option<(f64, f64)> {
        match i {
            SIN => fast_sin(x),
            COS => fast_cos(x),
            _ => fast_tan(x),
        }
    }

    // The positive arguments below `LIMIT` of `reduction_edges`: RN(n u) and RN((n + 1/2) u) and
    // the 2 `f64`s on each side of each, for each n of `edge_ns`, the x of `exact_rh`, and the 3
    // `f64`s below `LIMIT`. Those around 0 include 0 and negative subnormals.
    fn edge_args() -> Vec<f64> {
        let mut v = vec![];
        for n in edge_ns() {
            v.extend(around(n as f64 * STEP, 2));
            v.extend(around((n as f64 + 0.5) * STEP, 2));
        }
        v.extend(exact_rh().into_iter().map(|(_, x)| x));
        let mut x = LIMIT;
        for _ in 0..3 {
            x = next_down(x);
            v.push(x);
        }
        v
    }

    // The arguments of the bound tests of the fast path: those of `edge_args`, and 4,000 of
    // `fast_arg`, half of them uniform over its range, with the negations of all of them.
    fn bound_args() -> Vec<f64> {
        let mut rng = Rng(905);
        let mut v = edge_args();
        for k in 0..4000 {
            v.push(fast_arg(&mut rng, k % 2 == 0));
        }
        let negated: Vec<f64> = v.iter().map(|x| -x).collect();
        v.extend(negated);
        v
    }

    // `fast_reduce(x)` meets the conjuncts of `fast_reduce_correct` in
    // `rocq/theories/FastTrigReduce.v` on the arguments of `bound_args`: for ρ = x - n u, with
    // u = π/4096, |n| < 2^27, rh, rl and rr are finite, rr = RN(rh + rl),
    // |ρ - (rh + rl)| <= 2^-90, |ρ| <= u/2 (1 + 2^-24), |rl| <= 2^-37, and |rh| >= 2^-65 where n
    // and rh are not 0. The computed ρ is within 2^-283 of it, the rounding of n u to `PREC` bits
    // for |n u| < 2^17.
    #[test]
    fn fast_reduce_bound() {
        let u = Float::with_val(PREC, Constant::Pi) / 4096u32;
        let mut half = Float::with_val(PREC, &u * (1.0 + pow2(-24)));
        half >>= 1;
        for x in bound_args() {
            let (n, rh, rl, rr) = fast_reduce(x).unwrap();
            let mut nu = Float::with_val(PREC, n);
            nu *= &u;
            let rho = x - nu;
            let mut err = Float::with_val(PREC, &rho - rh);
            err -= rl;
            err.abs_mut();
            let mut size = rho.clone();
            size.abs_mut();
            assert!(
                n.abs() < 1 << 27
                    && rh.is_finite()
                    && rl.is_finite()
                    && rr.is_finite()
                    && rr.to_bits() == (rh + rl).to_bits()
                    && err <= pow2(-90)
                    && size <= half
                    && rl.abs() <= pow2(-37)
                    && (n == 0 || rh == 0.0 || rh.abs() >= pow2(-65)),
                "fast_reduce({x:e}) = ({n}, {rh:e}, {rl:e}, {rr:e}), with ρ = {:e} and \
                 |ρ - (rh + rl)| = {:e}",
                rho.to_f64(),
                err.to_f64()
            );
        }
    }

    // (h, l), from the fast path at an argument where the function has the value y, have
    // h = RN(h + l), 2^-1000 <= |h| <= 2^1000, and |y - (h + l)| <= k 2^-71 |y|.
    fn check_core(what: &str, y: &Float, (h, l): (f64, f64), k: u32) {
        let mut d = Float::with_val(PREC, y - h);
        d -= l;
        d.abs_mut();
        let mut bound = Float::with_val(PREC, y * k);
        bound.abs_mut();
        bound >>= 71;
        assert!(
            h + l == h && pow2(-1000) <= h.abs() && h.abs() <= pow2(1000) && d <= bound,
            "{what}: ({h:e}, {l:e}), with |y - (h + l)| = 2^{:.2} |y|",
            (d.to_f64() / y.to_f64().abs()).log2()
        );
    }

    // The core of the function `i` meets the bound of `fast_<f>_correct` in
    // `rocq/theories/FastTrigCore.v`, with k 2^-71, on the arguments of `bound_args` with
    // |x| >= 2^-27 that it takes. Those include the n = 0 of `fast_sin0` and `fast_cos0`,
    // |x| <= u/2 (1 + 2^-24), and negative arguments of cos, which `cos` does not pass but its
    // core takes.
    fn check_cores(i: usize, k: u32) {
        let (mut taken, mut at_zero) = (0, 0);
        for x in bound_args() {
            if x.abs() < pow2(-27) {
                continue;
            }
            if let Some(parts) = core(i, x) {
                let what = format!("fast {}({x:e})", FUNCTIONS[i].0);
                check_core(&what, &value(i, x), parts, k);
                taken += 1;
                at_zero += usize::from(reduced(x) == 0);
            }
        }
        assert!(
            taken > 10_000 && at_zero > 500,
            "{}: {taken} arguments, {at_zero} of them with n = 0",
            FUNCTIONS[i].0
        );
    }

    // `fast_sin` and `fast_cos` are within 2^-71 |f(x)| of sin x and cos x
    // (`fast_sin_correct`, `fast_cos_correct`).
    #[test]
    fn fast_sin_cos_bound() {
        check_cores(SIN, 1);
        check_cores(COS, 1);
    }

    // `fast_tan` is within 3 2^-71 |tan x| of tan x (`fast_tan_correct`).
    #[test]
    fn fast_tan_bound() {
        check_cores(TAN, 3);
    }

    // The directed rounding tests of the fast path fail at the arguments of `HARD_CASES` and
    // `SMALL_FALL_THROUGH`, and their negations, with 2^-27 <= |x| < `LIMIT` and y = f(x) within
    // 2^-72 |y| of an `f64` g. The bound of the core puts h + l within (2^-72 + 3 2^-71) |y| of
    // g, which is below 2^-68 after the scaling of `fast_unscale` to |h| in [1, 2), so that h is g
    // and |l| is below 2^-68, where neither direction passes. Where sin or cos gives g = ±1,
    // `fast_one_dir` rounds y instead, to MPFR's roundings.
    #[test]
    fn hard_cases_fall_through() {
        let mut reached = 0;
        for &(i, x) in HARD_CASES.iter().chain(&SMALL_FALL_THROUGH) {
            for x in [x, -x] {
                if x.abs() < pow2(-27) || x.abs() >= LIMIT {
                    continue;
                }
                let y = value(i, x);
                let mut d = Float::with_val(PREC, &y - y.to_f64());
                d.abs_mut();
                let mut bound = y.clone();
                bound.abs_mut();
                bound >>= 72;
                if d > bound {
                    continue;
                }
                for up in [false, true] {
                    let r = match i {
                        SIN => fast_sin_dir(x, up),
                        COS => fast_cos_dir(x, up),
                        _ => fast_tan_dir(x, up),
                    };
                    let want = if i != TAN && y.to_f64().abs() == 1.0 {
                        Some(if up { MPFR[i].1(x) } else { MPFR[i].0(x) })
                    } else {
                        None
                    };
                    assert!(
                        r.map(f64::to_bits) == want.map(f64::to_bits),
                        "{}({x:e}): the fast path rounds it {} to {r:?}",
                        FUNCTIONS[i].0,
                        if up { "up" } else { "down" }
                    );
                }
                reached += usize::from(core(i, x).is_some());
            }
        }
        assert!(reached >= 16, "{reached} hard cases reach a rounding test");
    }

    // `INV2PI` is floor(2^1216 / (2π)) = floor(2^1215 / π), as its comment says: 2^1215 / π is
    // between 2^1215 / π rounded down to 1,400 bits, with π rounded up, and 2^1215 / π rounded
    // up, with π rounded down, whose floors are equal, so they are that of 2^1215 / π.
    #[test]
    fn inv2pi_table() {
        use rug::integer::Order;
        let floor = |r, pi_r| {
            let (pi, _) = Float::with_val_round(1400, Constant::Pi, pi_r);
            let (q, _) = Float::with_val_round(1400, pi.recip_ref(), r);
            (q << 1215u32).to_integer_round(Round::Down).unwrap().0
        };
        let t = floor(Round::Down, Round::Up);
        assert_eq!(t, floor(Round::Up, Round::Down));
        assert_eq!(t.significant_bits(), 1214);
        let mut limbs = [0; 20];
        t.write_digits(&mut limbs, Order::Msf);
        let rows: String = limbs
            .iter()
            .map(|l| {
                let h = format!("{:016x}", l);
                format!(
                    "    0x{}_{}_{}_{},\n",
                    &h[..4],
                    &h[4..8],
                    &h[8..12],
                    &h[12..]
                )
            })
            .collect();
        assert!(limbs == INV2PI, "INV2PI should be\n{}", rows);
    }

    // The precision of the reductions of the arguments of `fast_reduce_big`: x / u is below 2^1037
    // for |x| < 2^1024, so that k, x / u rounded to an integer, is right unless x / u is within
    // about 2^-360 of a midpoint between two integers, and ρ = x - k u, from u and k u to 1,400
    // bits, is within about 2^-370 of it.
    const BIG_PREC: u32 = 1400;

    // u = π/4096 to `BIG_PREC` bits.
    fn big_u() -> Float {
        Float::with_val(BIG_PREC, Constant::Pi) / 4096u32
    }

    // k = x / u rounded to an integer, and ρ = x - k u, for the u of `big_u`.
    fn big_rho(x: f64, u: &Float) -> (Integer, Float) {
        let k = Float::with_val(BIG_PREC, x / u).to_integer().unwrap();
        let ku = Float::with_val(BIG_PREC, u * &k);
        (k, x - ku)
    }

    // What `fast_reduce_big` does with an x, as `check_big_bound` finds it: it takes x, or it
    // declines x, at i = k mod 2048 = 0 or at a small ρ.
    #[derive(Clone, Copy, Debug, PartialEq)]
    enum Big {
        Taken,
        AtZero,
        Small,
    }

    // `fast_reduce_big(x)`, for |x| >= `LIMIT`, meets `fast_reduce_big_correct` in
    // `rocq/theories/FastTrigBig.v` with N = k, for k and ρ = x - k u of `big_rho`. With s the
    // sign of x, so that s ρ is the ρ of |x|, it is `None` where k mod 2048 = 0 or
    // 0 <= s ρ < 2^-53 u (see `NEAR_STEPS`), here checked up to 2^-100 on each side. Otherwise it
    // is (n, rh, rl, rr) with n = k mod 8192, |ρ - (rh + rl)| <= 2^-90 and |ρ| <= u/2 (1 + 2^-24),
    // for `half` = u/2 (1 + 2^-24), and the bounds that `check_big` checks. Returns k and what
    // `fast_reduce_big` does.
    fn check_big_bound(x: f64, u: &Float, half: &Float) -> (Integer, Big) {
        let (k, rho) = big_rho(x, u);
        let mut size = rho.clone();
        size.abs_mut();
        let s_rho = if x < 0.0 {
            Float::with_val(BIG_PREC, -&rho)
        } else {
            rho.clone()
        };
        let margin = pow2(-100);
        let step = Float::with_val(BIG_PREC, u * pow2(-53));
        let step_hi = Float::with_val(BIG_PREC, &step + margin);
        let step_lo = Float::with_val(BIG_PREC, &step - margin);
        let at_zero = k.mod_u(2048) == 0;
        let Some((n, rh, rl, rr)) = fast_reduce_big(x) else {
            assert!(
                at_zero || (s_rho >= -margin && s_rho <= step_hi),
                "fast_reduce_big({x:e}) declines it, with k = {k} and ρ = {:e}",
                rho.to_f64()
            );
            return (k, if at_zero { Big::AtZero } else { Big::Small });
        };
        check_big(x);
        let mut err = Float::with_val(BIG_PREC, &rho - rh);
        err -= rl;
        err.abs_mut();
        assert!(
            !at_zero
                && (s_rho <= margin || s_rho >= step_lo)
                && n == i64::from(k.mod_u(8192))
                && err <= pow2(-90)
                && size <= *half,
            "fast_reduce_big({x:e}) = ({n}, {rh:e}, {rl:e}, {rr:e}), with k = {k}, ρ = {:e} and \
             |ρ - (rh + rl)| = {:e}",
            rho.to_f64(),
            err.to_f64()
        );
        (k, Big::Taken)
    }

    // u/2 (1 + 2^-24), the bound on |ρ| of `check_big_bound`, for the u of `big_u`.
    fn big_half(u: &Float) -> Float {
        let mut half = Float::with_val(BIG_PREC, u * (1.0 + pow2(-24)));
        half >>= 1;
        half
    }

    // `fast_reduce_big` on the arguments of `big_edge_args` and 4,000 of `big_arg`, and their
    // negations, as `check_big_bound` checks it. It declines `KM` and the x of `NEAR_STEPS` with
    // 0 <= ρ < 2^-53 u and their negations, so that both kinds of decline occur, and takes the
    // others of `NEAR_STEPS`.
    #[test]
    fn fast_reduce_big_bound() {
        let u = big_u();
        let half = big_half(&u);
        for (x, takes) in NEAR_STEPS {
            for y in [x, -x] {
                let want = if takes { Big::Taken } else { Big::Small };
                assert_eq!(check_big_bound(y, &u, &half).1, want, "{y:e}");
            }
        }
        assert_eq!(check_big_bound(KM, &u, &half).1, Big::AtZero);
        let mut rng = Rng(952);
        let mut args = big_edge_args();
        args.extend((0..4000).map(|_| big_arg(&mut rng)));
        let mut counts = [0; 3];
        for x in args {
            for y in [x, -x] {
                if y.abs() >= LIMIT {
                    counts[check_big_bound(y, &u, &half).1 as usize] += 1;
                }
            }
        }
        assert!(
            counts[0] > 10_000 && counts[1] > 0 && counts[2] > 0,
            "fast_reduce_big takes {} arguments, and declines {} at i = 0 and {} at a small ρ",
            counts[0],
            counts[1],
            counts[2]
        );
    }

    // The arguments next to the steps of the reduction of `fast_reduce_big`, as (N, x, whether x
    // is near a midpoint): x = RN(N u) and RN((N + 1/2) u), for N = N0 + 2048 q + d with q from
    // -4 to 4 and d in {-1, 0, 1}, where N0 is the multiple of 8192 nearest to 1.5 2^e / u, for e
    // in {16, 17, 20, 24, 28, 32, 36, 39}. There i = N mod 2048 is 2047, 0 or 1, and q changes.
    // As N u < 2^40, the `f64`s there are at most 2^-13 apart, so that the 2 `f64`s on each side
    // of RN(N u) are within u/2 of N u too, and those of RN((N + 1/2) u) within u/2 of N u on one
    // side of (N + 1/2) u and of (N + 1) u on the other.
    fn step_args(u: &Float) -> Vec<(i64, f64, bool)> {
        let mut v = vec![];
        for e in [16, 17, 20, 24, 28, 32, 36, 39] {
            let n0 = Float::with_val(BIG_PREC, 1.5 * pow2(e) / u) / 8192u32;
            let n0 = n0.to_integer().unwrap().to_i64().unwrap() * 8192;
            for q in -4..=4 {
                for d in -1..=1 {
                    let n = n0 + 2048 * q + d;
                    let x = Float::with_val(BIG_PREC, u * n);
                    let mut mid = Float::with_val(BIG_PREC, u * (2 * n + 1));
                    mid >>= 1;
                    v.push((n, x.to_f64(), false));
                    v.push((n, mid.to_f64(), true));
                }
            }
        }
        v
    }

    // At the arguments of `step_args` and the 2 `f64`s on each side of each, x / u rounds to N
    // around RN(N u), and to N on one side of RN((N + 1/2) u) and N + 1 on the other, where
    // `fast_reduce_big` meets its bounds as `check_big_bound` checks them, both signs of each,
    // and sin, cos and tan there are as `check_fast` checks them.
    #[test]
    fn big_steps() {
        let u = big_u();
        let half = big_half(&u);
        for (n, x, mid) in step_args(&u) {
            let mut ks = vec![];
            for y in around(x, 2) {
                ks.push(check_big_bound(y, &u, &half).0.to_i64().unwrap());
                check_big_bound(-y, &u, &half);
                for i in [SIN, COS, TAN] {
                    check_fast(i, y);
                    check_fast(i, -y);
                }
            }
            let ok = if mid {
                ks.contains(&n) && ks.contains(&(n + 1)) && ks.iter().all(|&k| k == n || k == n + 1)
            } else {
                ks.iter().all(|&k| k == n)
            };
            assert!(ok, "around {x:e}, N = {n}: {ks:?}");
        }
    }

    // `HALF_PI_LO` is RN(π/2 - RN(π/2)), and `near_multiple(k)` is RN(k π/2) for every k from 1
    // to `LAST_K`. At it and the 2 `f64`s on each side of it, both signs of each, where
    // `fast_reduce` gives n = ±2048 k, `fast_band_reduce` gives (sh, sl, sr) with the bounds that
    // `fast_band_reduce_correct` in `rocq/theories/FastTrigBandRed.v` proves: sh, sl and sr are
    // finite, sr = RN(sh + sl), 2^-61 <= |ρ| <= u/2 (1 + 2^-24) for ρ = x - n u,
    // |ρ - (sh + sl)| <= 2^-74 |ρ| and |sl| <= 2^-24 |sh|. π is to `PREC` bits, so that n u is
    // within 2^-280 of n π/4096, and x - n u, sh and sl are exact to `PREC` bits.
    #[test]
    fn band_reductions() {
        let pi = Float::with_val(PREC, Constant::Pi);
        let half_pi = Float::with_val(PREC, &pi / 2u32);
        let lo = Float::with_val(PREC, &half_pi - std::f64::consts::FRAC_PI_2).to_f64();
        assert_eq!(HALF_PI_LO.to_bits(), lo.to_bits(), "HALF_PI_LO: {lo:e}");
        let u = Float::with_val(PREC, &pi / 4096u32);
        let far = Float::with_val(PREC, &u / 2u32) * (1.0 + pow2(-24));
        for k in 1..=LAST_K {
            let x = near_multiple(k);
            let want = Float::with_val(PREC, &half_pi * k).to_f64();
            assert_eq!(x.to_bits(), want.to_bits(), "k = {k}: {x:e} != {want:e}");
            for y in around(x, 2) {
                for z in [y, -y] {
                    let (n, rh, rl, _) = fast_reduce(z).unwrap();
                    let (sh, sl, sr) = fast_band_reduce(n, rh, rl);
                    let rho = Float::with_val(PREC, z) - Float::with_val(PREC, &u * n);
                    let mut err = Float::with_val(PREC, &rho - sh) - sl;
                    err.abs_mut();
                    let rho = rho.abs();
                    assert!(
                        [sh, sl, sr].iter().all(|v| v.is_finite())
                            && sr.to_bits() == (sh + sl).to_bits()
                            && rho >= pow2(-61)
                            && rho <= far
                            && err <= Float::with_val(PREC, &rho * pow2(-74))
                            && sl.abs() <= pow2(-24) * sh.abs(),
                        "{z:e}: n = {n}, (sh, sl, sr) = ({sh:e}, {sl:e}, {sr:e}), |ρ| = {:e}, \
                         |ρ - (sh + sl)| = {:e}",
                        rho.to_f64(),
                        err.to_f64()
                    );
                }
            }
        }
    }
}

mod band;
mod levels;
mod mpfr_cases;
