// Tests of the inverse trigonometric functions of the dyadic kernel. Every generator runs on
// every platform through `check` and `check2`, which check that the two directions give the
// same `f64` or two adjacent ones, or NaN for both, and that the rounding to nearest gives one
// of them, or NaN if they are. On 64-bit Linux and macOS, where the tests have MPFR, they also
// compare the two directions and the rounding to nearest with the functions of
// `src/mpfr_calls/mpfr.rs` that compute the same function with MPFR, which they have to agree
// with bit for bit.

use super::*;
use crate::dyadic::{
    fast::{fast_counts, reset_fast_counts, set_fast_path},
    tests::Rng,
};
use std::f64::consts::{FRAC_1_SQRT_2, FRAC_PI_2, PI, SQRT_2};

type Directed = fn(f64, bool) -> f64;

const ATAN: usize = 0;
const ASIN: usize = 1;
const ACOS: usize = 2;

const FUNCTIONS: [(&str, Directed); 3] = [("atan", atan), ("asin", asin), ("acos", acos)];

type Near = fn(f64) -> f64;

// The functions of `FUNCTIONS` rounded to nearest, in the same order.
const NEAR: [Near; 3] = [atan_near, asin_near, acos_near];

// The signs of (y, x) in the four quadrants.
const QUADRANTS: [(f64, f64); 4] = [(1.0, 1.0), (1.0, -1.0), (-1.0, 1.0), (-1.0, -1.0)];

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

// `lo` and `hi`, the two directions of `name` at `args`, are equal or adjacent, or NaN both.
fn check_pair(name: &str, args: &str, lo: f64, hi: f64) {
    if lo.is_nan() || hi.is_nan() {
        assert!(
            lo.is_nan() && hi.is_nan(),
            "{}({}): {:e} {:e}",
            name,
            args,
            lo,
            hi
        );
    } else {
        assert!(
            lo.to_bits() == hi.to_bits() || next_up(lo).to_bits() == hi.to_bits(),
            "{}({}): {:e} and {:e} are neither equal nor adjacent",
            name,
            args,
            lo,
            hi
        );
    }
}

// `near`, the rounding to nearest of `name` at `args`, is one of `lo` and `hi`, its two
// directions, or NaN if they are. This holds for zeros too: a number of magnitude at most
// 2^-1075 rounds to nearest to the zero of its sign, which the direction toward 0 also gives.
fn check_near(name: &str, args: &str, lo: f64, hi: f64, near: f64) {
    let ok = if lo.is_nan() {
        near.is_nan()
    } else {
        near.to_bits() == lo.to_bits() || near.to_bits() == hi.to_bits()
    };
    assert!(
        ok,
        "{}({}): {:e} to nearest, outside ({:e}, {:e})",
        name, args, near, lo, hi
    );
}

// Checks the function `i` at `x` in both directions and to nearest, as the header says.
fn check(i: usize, x: f64) {
    let (name, f) = FUNCTIONS[i];
    let (lo, hi) = (f(x, false), f(x, true));
    let near = NEAR[i](x);
    let args = format!("{:e}", x);
    check_pair(name, &args, lo, hi);
    check_near(name, &args, lo, hi, near);
    #[cfg(all(
        target_pointer_width = "64",
        any(target_os = "linux", target_os = "macos")
    ))]
    {
        mpfr::check(i, x, lo, hi);
        mpfr::check_near(i, x, near);
    }
}

// Checks atan2 at (y, x) in both directions and to nearest, as the header says.
fn check2(y: f64, x: f64) {
    let (lo, hi) = (atan2(y, x, false), atan2(y, x, true));
    let near = atan2_near(y, x);
    let args = format!("{:e}, {:e}", y, x);
    check_pair("atan2", &args, lo, hi);
    check_near("atan2", &args, lo, hi, near);
    #[cfg(all(
        target_pointer_width = "64",
        any(target_os = "linux", target_os = "macos")
    ))]
    {
        mpfr::check2(y, x, lo, hi);
        mpfr::check2_near(y, x, near);
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

// Arguments on which mismatches were found, as `(function, arguments)`, each with what it
// broke and where it was found. The arguments of atan2 are `"y, x"`.
fn regressions() -> Vec<(&'static str, &'static str)> {
    vec![]
}

#[test]
fn regressions_hold() {
    for (name, args) in regressions() {
        if name == "atan2" {
            let (y, x) = args.split_once(", ").unwrap();
            check2(y.parse().unwrap(), x.parse().unwrap());
        } else {
            let i = FUNCTIONS.iter().position(|(n, _)| *n == name).unwrap();
            check(i, args.parse().unwrap());
        }
    }
}

// Special values, both signs of each: the zeros, the infinities and NaN, at which the rules give
// results, and finite values from the least to the greatest, among them 1, where the domains of
// asin and acos end.
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
    for i in 0..FUNCTIONS.len() {
        for x in SPECIAL {
            check(i, x);
            check(i, -x);
        }
    }
    for y in SPECIAL {
        for x in SPECIAL {
            for (sy, sx) in QUADRANTS {
                check2(sy * y, sx * x);
            }
        }
    }
    for up in [false, true] {
        // atan and asin keep the sign of a zero, and acos(1) is +0.
        for x in [0.0, -0.0] {
            assert_eq!(atan(x, up).to_bits(), x.to_bits());
            assert_eq!(asin(x, up).to_bits(), x.to_bits());
        }
        assert_eq!(acos(1.0, up).to_bits(), 0);
        // atan2 at the zeros and infinities, as `mpfr_atan2` gives it.
        for y in [0.0, -0.0] {
            for x in [0.0, 1.0, f64::INFINITY] {
                assert_eq!(atan2(y, x, up).to_bits(), y.to_bits());
            }
            for x in [-0.0, -1.0, f64::NEG_INFINITY] {
                assert_eq!(atan2(y, x, up), pi_times(1.0_f64.copysign(y), up));
            }
        }
        for y in [1.0, -1.0, f64::MAX, -f64::MAX] {
            assert_eq!(
                atan2(y, f64::INFINITY, up).to_bits(),
                0.0_f64.copysign(y).to_bits()
            );
            assert_eq!(
                atan2(y, f64::NEG_INFINITY, up),
                pi_times(1.0_f64.copysign(y), up)
            );
            for x in [0.0, -0.0] {
                assert_eq!(atan2(y, x, up), pi_times(0.5_f64.copysign(y), up));
            }
        }
        for s in [1.0, -1.0] {
            let y = s * f64::INFINITY;
            assert_eq!(atan2(y, f64::INFINITY, up), pi_times(0.25 * s, up));
            assert_eq!(atan2(y, f64::NEG_INFINITY, up), pi_times(0.75 * s, up));
            for x in [0.0, -0.0, 1.0, -1.0, f64::MAX, -f64::MAX] {
                assert_eq!(atan2(y, x, up), pi_times(0.5 * s, up));
            }
        }
    }
    // To nearest: atan and asin keep the sign of a zero, atan(±2^54) and asin(1) are the `f64`
    // nearest ±π/2, acos(1) is +0 and acos(-1) the `f64` nearest π.
    for x in [0.0, -0.0] {
        assert_eq!(atan_near(x).to_bits(), x.to_bits());
        assert_eq!(asin_near(x).to_bits(), x.to_bits());
    }
    assert_eq!(atan_near(HUGE_ATAN), FRAC_PI_2);
    assert_eq!(atan_near(-HUGE_ATAN), -FRAC_PI_2);
    assert_eq!(asin_near(1.0), FRAC_PI_2);
    assert_eq!(acos_near(1.0).to_bits(), 0);
    assert_eq!(acos_near(-1.0), PI);
}

// The exact enclosure of acos 1, which no rule settles: `Acos` gives the point 0 there, whose
// `f64` is +0 (`ev_acos_one`).
#[test]
fn exact_enclosure() {
    crate::dyadic::tests::check_exact(&Acos(1.0), 0.0, "acos(1)");
}

// Each rule and each case of `atan_encl` at its threshold and the 3 `f64`s on each side of it,
// both signs of them: `TINY_HYP` and `HUGE_ATAN` for atan, `TINY_ASIN` for asin, 1 for asin
// and acos, where their domains end, `T1`, 1 and `T2` for atan, and `ASIN_SPLIT` for asin and
// acos. The rules to nearest take `TINY_NEAR` and `HUGE_ATAN` for atan and `TINY_ASIN` for
// asin, and atan is checked at 2^53 too, where `ziv_near` settles atan x to nearest. For
// atan2, y = q d and x = d for q at `TINY_NEAR` and `TINY_HYP` and the `f64`s around them,
// where y / x = q exactly for d = 1 and 2^1000, which the rule of `tiny_quotient` takes below
// `TINY_HYP` and that of `atan2_near` below `TINY_NEAR`, and the quotients |y| / |x| at the
// thresholds of `atan_encl`, in each quadrant.
#[test]
fn rules_at_their_thresholds() {
    let thresholds = [
        (ATAN, TINY_NEAR),
        (ATAN, TINY_HYP),
        (ATAN, pow2(53)),
        (ATAN, HUGE_ATAN),
        (ATAN, T1),
        (ATAN, 1.0),
        (ATAN, T2),
        (ASIN, TINY_ASIN),
        (ASIN, ASIN_SPLIT),
        (ASIN, 1.0),
        (ACOS, ASIN_SPLIT),
        (ACOS, 1.0),
    ];
    for (i, t) in thresholds {
        for x in around(t, 3) {
            check(i, x);
            check(i, -x);
        }
    }
    for q in [around(TINY_NEAR, 3), around(TINY_HYP, 3)].concat() {
        // y = q d, which is exact for d = 1 and 2^1000, and rounded for the other d unless
        // q d fits in an `f64`: for 2^-1000 it is subnormal, with fewer bits than q.
        for d in [1.0, pow2(-1000), pow2(1000), 3.0, 0.75, f64::MAX / 3.0] {
            for (y, x) in [(q * d, d), (-q * d, d), (q * d, -d), (-q * d, -d)] {
                check2(y, x);
                check2(x, y);
            }
        }
    }
    for t in [T1, 1.0, T2] {
        for q in around(t, 3) {
            for (y, x) in [(q, 1.0), (1.0, q)] {
                for (sy, sx) in QUADRANTS {
                    check2(sy * y, sx * x);
                }
            }
        }
    }
}

// The arguments around the edges of the reductions, both signs of them: asin and acos around
// 1/2 and 2^-11, where 1 - t is exact by Sterbenz's lemma for t >= 1/2, and 1 - t and 1 + t,
// multiples of 2^-63 of at most 2 for t >= 2^-11, are exact in 64 bits; atan around
// tan(π/8) = √2 - 1 and tan(3π/8) = 1 + √2, which `T1` and `T2` approximate from below; and
// atan2 at the quotients |y| / |x| around √2 - 1 and their inverses, in each quadrant.
#[test]
fn reductions_at_their_edges() {
    for t in [0.5, pow2(-11)] {
        for x in around(t, 3) {
            for i in [ASIN, ACOS] {
                check(i, x);
                check(i, -x);
            }
        }
    }
    for t in [SQRT_2 - 1.0, 1.0 + SQRT_2] {
        for x in around(t, 3) {
            check(ATAN, x);
            check(ATAN, -x);
        }
    }
    for q in around(SQRT_2 - 1.0, 3) {
        for (y, x) in [(q, 1.0), (1.0, q)] {
            for (sy, sx) in QUADRANTS {
                check2(sy * y, sx * x);
            }
        }
    }
}

// `atan_series` around `NO_HALVE` = 2^-8, up to which it takes the series at u itself and above
// which it halves u first, at the arguments around those at which u = 2^-8, both signs of them:
// atan at 2^-8, where u = w, at 255/257 and 257/255, where u = (1 - w) / (1 + w) and
// (w - 1) / (w + 1), and at 256, where u = 1 / w; asin and acos at 2^-8 / √(1 + 2^-16) and
// 1 / √(1 + 2^-16), at which t / √(1 - t^2) and √(1 - t^2) / t are 2^-8; and atan2 at y around
// 2^-8, 1 and 255 with x = 1, 256 and 257, where |y| / |x| is 2^-8 or 255/257, in each
// quadrant, and at (x, y). The `f64` arithmetic gives each of these arguments within 2 `f64`s
// of the number at which u = 2^-8, and the enclosures of u are far narrower than the steps of u
// between adjacent `f64`s, so that the 3 `f64`s on each side of it take both branches (a check
// of u at one limb found both in each family).
#[test]
fn halving_at_its_threshold() {
    let s = (1.0 + NO_HALVE * NO_HALVE).sqrt();
    for t in [NO_HALVE, 255.0 / 257.0, 257.0 / 255.0, 1.0 / NO_HALVE] {
        for x in around(t, 3) {
            check(ATAN, x);
            check(ATAN, -x);
        }
    }
    for t in [NO_HALVE / s, 1.0 / s] {
        for x in around(t, 3) {
            for i in [ASIN, ACOS] {
                check(i, x);
                check(i, -x);
            }
        }
    }
    for (y0, x) in [(NO_HALVE, 1.0), (1.0, 1.0 / NO_HALVE), (255.0, 257.0)] {
        for y in around(y0, 3) {
            for (sy, sx) in QUADRANTS {
                check2(sy * y, sx * x);
                check2(sx * x, sy * y);
            }
        }
    }
}

// Arguments whose results are close to an `f64`, so that `ziv` may need more than one level
// for them, with the roundings that follow where bounds determine them, both signs of each.
//
// atan at 2^k for k from -60 to 60, and asin and acos at 2^-k for k from 1 to 60. For
// 0 < x < 1, x - x^3 / 3 < atan x < x, as the series of atan alternates with terms that
// decrease, and x < asin x < x + x^3 / (6 (1 - x^2)), as the coefficients of the series
// x + x^3 / 6 + 3 x^5 / 40 + ... of asin are positive and decrease. For x = 2^k with
// k <= -26, x^3 / 3 is below 2^-53 x, the distance from x to the `f64` below it, so that
// atan x is between the two. For x = 2^-k with k >= 25, x^3 / (6 (1 - x^2)) is below 2^-52 x,
// the distance from x to the `f64` above it, so that asin x is between the two. The rules
// settle the arguments below 2^-26 and from 2^54 up for atan and below 2^-27 for asin, and
// `ziv` the others.
//
// asin and acos at 1 - y for y = 2^-k and k from 1 to 53. acos(1 - y) = 2 asin s for
// s = √(y / 2), as cos 2θ = 1 - 2 sin^2 θ, so that 2 s < acos(1 - y) < 2 s (1 + s^2 / (6 (1 -
// s^2))) by the bounds of asin above. For odd k, 2 s = 2^((1 - k) / 2) is an `f64`, and for
// k >= 49 also s^2 / (6 (1 - s^2)) < 2^-52, as s^2 = 2^-(k + 1), so that acos(1 - y) is
// between 2 s and the `f64` above it.
//
// atan2(y, x) in each quadrant at exact quotients y / x = q = j 2^-a, for j in [2^10, 2^11)
// and a from 36 to 50, with x = i 2^(a + s - 1074) and y = i j 2^(s - 1074): for an i in
// [1, 2^(52 - a)), y and x are subnormal at s = 0, and `f64`s for s up to 2046. |q| is in
// [2^-40, 2^-25), on both sides of `TINY_HYP` = 2^-26, below which the rule of atan2 settles
// the quotients for x > 0. The cases are q = j 2^-36 for j in 1024..1028, from 2^-26 up, and
// q = j 2^-37 for j in 2044..2048, below 2^-26, with i = 1 and s in {0, 60, 1074, 2046}, and
// 1,000 random ones, with s uniform in [0, 60], across which y and x become normal, half of
// the time, and in [0, 2046] otherwise.
//
// For x > 0, atan2(y, x) = atan q, which the bounds of atan above put between q and the
// `f64` t next to it toward 0 if |q|^3 / 3 < |q - t|. That holds for every |q| < 2^-26, as
// |q - t| >= 2^-53 |q| and q^2 < 2^-52, and the test also takes it where it holds above 2^-26.
// q has at most 11 bits, so that `f64` arithmetic gives |q|^3 and 3 |q - t| exactly. Each case
// also checks atan2(x, y), whose quotient |x / y| is above 2^25.
#[test]
fn close_to_an_f64() {
    let expect = |i: usize, x: f64, lo: f64, hi: f64| {
        check(i, x);
        let (name, f) = FUNCTIONS[i];
        assert!(
            f(x, false) == lo && f(x, true) == hi,
            "{}({:e}): ({:e}, {:e}) != ({:e}, {:e})",
            name,
            x,
            f(x, false),
            f(x, true),
            lo,
            hi
        );
    };
    for k in -60..=60 {
        let x = pow2(k);
        if k <= -26 {
            expect(ATAN, x, next_down(x), x);
            expect(ATAN, -x, -x, next_up(-x));
        } else {
            check(ATAN, x);
            check(ATAN, -x);
        }
    }
    for k in 1..=60 {
        let x = pow2(-k);
        if k >= 25 {
            expect(ASIN, x, x, next_up(x));
            expect(ASIN, -x, next_down(-x), -x);
        } else {
            check(ASIN, x);
            check(ASIN, -x);
        }
        check(ACOS, x);
        check(ACOS, -x);
    }
    for k in 1..=53 {
        let x = 1.0 - pow2(-k);
        if k % 2 == 1 && k >= 49 {
            let p = pow2((1 - k) / 2);
            expect(ACOS, x, p, next_up(p));
        } else {
            check(ACOS, x);
        }
        check(ACOS, -x);
        check(ASIN, x);
        check(ASIN, -x);
    }
    let mut cases = vec![];
    for (a, js) in [(36, 1024..1028), (37, 2044..2048)] {
        for j in js {
            for s in [0, 60, 1074, 2046] {
                cases.push((1, j, a, s));
            }
        }
    }
    let mut rng = Rng(70);
    for _ in 0..1000 {
        let a = uniform(&mut rng, 36, 50);
        let i = 1 + rng.below((1 << (52 - a)) - 1);
        let j = 1024 + rng.below(1024);
        let s = if rng.below(2) == 0 {
            uniform(&mut rng, 0, 60)
        } else {
            uniform(&mut rng, 0, 2046)
        };
        cases.push((i, j, a, s));
    }
    // v 2^s, exact for the v and s here.
    let scaled = |v: f64, s: i32| v * pow2(s.min(1023)) * pow2(s - s.min(1023));
    for (i, j, a, s) in cases {
        let (y, x) = (
            scaled(f64::from_bits(i * j), s),
            scaled(f64::from_bits(i << a), s),
        );
        for (sy, sx) in QUADRANTS {
            let (y, x) = (sy * y, sx * x);
            check2(y, x);
            check2(x, y);
            let q = y / x;
            let t = if q > 0.0 { next_down(q) } else { next_up(q) };
            if x > 0.0 && q * q * q.abs() < 3.0 * (q - t).abs() {
                let (lo, hi) = (atan2(y, x, false), atan2(y, x, true));
                assert!(
                    lo == q.min(t) && hi == q.max(t),
                    "atan2({:e}, {:e}): ({:e}, {:e}) is not q = {:e} and the `f64` next to it \
                     toward 0",
                    y,
                    x,
                    lo,
                    hi,
                    q
                );
            }
        }
    }
}

// An odd number of `bits` bits, at random, for `bits` in [1, 63].
fn odd(rng: &mut Rng, bits: u32) -> u64 {
    (1 << (bits - 1)) | rng.below(1 << (bits - 1)) | 1
}

// atan2 at y = X m 2^(k - 1075) and x = X 2^k for odd X and m with X m < 2^53 and k >= 1, so
// that y / x = m 2^-1075 is midway between the `f64`s (m - 1) 2^-1075 and (m + 1) 2^-1075, and
// atan(y / x) rounds to nearest to the first, which `midpoint_quotient` gives, and for -y. The
// cases are X = 1 with m = 1 at k = 1, which is atan2(2^-1074, 2) = atan 2^-1075, m = 2^53 - 1
// at k = 1, the greatest quotient, and m = 0x1272d1a7f62303 at k = 785, which is
// atan2(0x1.272d1a7f62303p-238, 2^785), at which `ziv_near` took 64 limbs before the rule, in
// the CORE-MATH run of `src/cr/tests/mpfr/hard_cases.rs`, and 2,000 random ones: X = 1, so
// that x = 2^k, with m of 1 to 53 bits for half of them, and otherwise X of b in [2, 52] bits
// with m of 1 to 53 - b bits, and k uniform in [1, 1024 - b], so that x <= `f64::MAX`.
//
// Each case also checks atan2 at the `f64`s y' next to y and -y, at which `midpoint_quotient`
// gives `None`: y' / x = m 2^-1075 ± u / x for the step u <= 2^(k - 1075), a power of 2, from
// y to y', which is not a dyadic number for X > 1, the `f64` (m ± 1) 2^-1075 for X = 1 and
// u = 2^(k - 1075), and an odd multiple of u / x < 2^-1075 otherwise. On 64-bit Linux and
// macOS, `atan2_near` takes at most 4 limbs at each argument.
#[test]
fn midpoint_quotients() {
    let mut cases = vec![
        (1, 1, 1),
        (1, (1 << 53) - 1, 1),
        (1, 0x0012_72d1_a7f6_2303, 785),
    ];
    let mut rng = Rng(1075);
    for _ in 0..2000 {
        let (xo, bm, kmax) = if rng.below(2) == 0 {
            (1, 53, 1023)
        } else {
            let b = uniform(&mut rng, 2, 52);
            (odd(&mut rng, b as u32), 53 - b, 1024 - b)
        };
        let bits = uniform(&mut rng, 1, bm) as u32;
        let m = odd(&mut rng, bits);
        let k = uniform(&mut rng, 1, kmax);
        cases.push((xo, m, k));
    }
    for (xo, m, k) in cases {
        // X m < 2^53 and X are exact, and so are their products by 2^(k - 1075) and 2^k.
        let (y, x) = ((xo * m) as f64 * pow2(k - 1075), xo as f64 * pow2(k));
        // (m - 1) 2^-1075 = ((m - 1) / 2) 2^-1074, below 2^-1022.
        let f = f64::from_bits((m - 1) / 2);
        for s in [1.0, -1.0] {
            let (y, f) = (s * y, s * f);
            let args = format!("{:e}, {:e}", y, x);
            assert_eq!(
                midpoint_quotient(y, x).map(f64::to_bits),
                Some(f.to_bits()),
                "midpoint_quotient({})",
                args
            );
            assert_eq!(
                atan2_near(y, x).to_bits(),
                f.to_bits(),
                "atan2({}) to nearest",
                args
            );
            for y1 in around(y, 1) {
                if y1 != y {
                    assert_eq!(
                        midpoint_quotient(y1, x),
                        None,
                        "midpoint_quotient({:e}, {:e})",
                        y1,
                        x
                    );
                }
                check2(y1, x);
                #[cfg(all(
                    target_pointer_width = "64",
                    any(target_os = "linux", target_os = "macos")
                ))]
                {
                    let level = mpfr::near_level2(y1, x);
                    assert!(level <= 4, "atan2({:e}, {:e}): {} limbs", y1, x, level);
                }
            }
        }
    }
}

// The hardest arguments that three searches found, as (function, x), and as (y, x) for atan2:
// those whose results are the closest to an `f64` relative to the result, so that a directed
// rounding of them needs the most bits. The searches, harnesses outside the crate, rounded each
// argument that no rule settles down and up at the first level of `ziv` that settles it
// (`ziv_at::<N>` for N = 1, 2, 4, .., 64 limbs), and measured the bits that each needs, -log2
// of the distance from f(x) to the nearest `f64` relative to |f(x)|, with MPFR at 1024 bits.
// F and F/2 are the `f64`s nearest π and π/2, both below them.
//
// The list search ran on atan at m 2^e in [2^-26, 2^-8] and asin at m 2^e in [2^-27, 2^-8],
// for odd m < 2^12 with 3 | m; atan at tan G and acos at cos G, each rounded down, to nearest
// and up, for G = F/2 - k 2^-52, and acos also for G = F/2 + k 2^-52, with k in 0..=64 and 2^j
// for j in 7..=30; asin and acos at ±(1 - j 2^-k) for odd j up to 15; atan at 2^k and 3 2^k
// for k in -60..=60; the 50 `f64`s on each side of `T1`, 1, `T2` and `TINY_HYP` for atan, of
// `ASIN_SPLIT`, 1/√2, 1/2 and 2^-11 for asin and acos, and of `TINY_ASIN` for asin; atan2 at
// the `f64`s y within 2 steps of q x, for x in {1 + j 2^-52 (j in 1..=8), 3, 5, 7} and
// q = 2^-k (k in 26..=60) or 1,000 random q in [2^-60, 2^-26); and atan2 in each quadrant at
// |y / x| = (m1 / m2) 2^±k, for 10 pairs of mantissas and k in 26..=80. None of them needed
// more than level 2.
//
// The random search ran on 10^7 arguments per set: atan uniform in [-10, 10) and log-uniform
// over the finite `f64`s, asin and acos uniform in [-1, 1) and log-uniform in magnitude over
// [2^-27, 1) with a random sign, and atan2 at y and x log-uniform with random signs. It also
// ran on 10^6 r per set, at the roundings down and up of tan r for r uniform in [-F/2, F/2)
// and for r = ±(F/2 - d) with d log-uniform in [2^-52, 1), of sin r for r in [-F/2, F/2), of
// cos r for r in [0, F), and, for atan2, of (sin r, cos r) times 2^k, for r in (-F, F] and k
// in [-900, 900]. None of them needed more than level 2 either.
//
// The continued-fraction search ran on atan2 at pairs (y, x) built from an `f64` G so that
// atan2(y, x) is close to G: the smaller of |y| and |x| over the larger is p 2^-s / r, for p / r
// a convergent or semiconvergent, with p, r < 2^53, of the continued fraction of q 2^s, where
// q = |tan G| or 1 / |tan G|, whichever is at most 1, and y and x have the signs of sin G and
// cos G. It took G = F - k, F/2 - k and F/2 + k, the `f64`s k steps from F and F/2, for k in
// 0..=64 and 2^j for j <= 30, with all four signs of (y, x), and 10^6 random G in (-π, π].
// Each of those G near F and F/2 has a pair that needs level 4, as do 9 of the pairs from the
// random G, and none needs level 8.
//
// Each comment gives the search and family of its cases, the bits that they need, and their
// levels down and up, where the search recorded them.
const HARD_CASES: [(usize, f64); 19] = [
    // The list search at the roundings of tan G for atan and of cos G for acos: the hardest of
    // each, at G = F/2, and one more of each, at G = F/2 - 17 2^-52 for atan, which the random
    // search also found at tan r for r near ±F/2, and at G = F/2 + 2^-52 for acos, where
    // cos G < 0. Level 2 both ways.
    (ATAN, 1.633123935319537e16),    // 110.4 bits.
    (ACOS, 6.123233995736766e-17),   // 109.7 bits.
    (ATAN, 2.6068885409315966e14),   // 108.0 bits.
    (ACOS, -1.6081226496766366e-16), // 106.8 bits.
    // The list search at m 2^e with 3 | m, the hardest, at 3 2^-25 for both: 97.4 bits for
    // asin, level 2 both ways, and 96.0 bits for atan, also the hardest of atan at 2^k and
    // 3 2^k, level 1 down, 2 up.
    (ASIN, 8.940696716308594e-8),
    (ATAN, 8.940696716308594e-8),
    // The list search at ±(1 - j 2^-k): the hardest for acos, one for acos with x < 0, and the
    // hardest for asin.
    (ACOS, 9.99999999999984e-1), // 1 - 9 2^-49: 97.4 bits, level 2 both ways.
    (ACOS, -9.999986886978149e-1), // -(1 - 11 2^-23): 64.4 bits, level 2 both ways.
    (ASIN, 9.999999993597157e-1), // 1 - 11 2^-34: 64.4 bits, level 2 down, 1 up.
    // The list search around the thresholds, the hardest, around 1/2 for acos and asin: 63.0
    // bits, level 2 both ways.
    (ACOS, 5.000000000000043e-1),  // 1/2 + 39 2^-53.
    (ASIN, 4.9999999999999784e-1), // 1/2 - 39 2^-54.
    // The random search, the hardest of each set except the log-uniform ones of atan and acos,
    // which it did not keep. Level 2 in the direction given; it did not record the other.
    (ATAN, 1.5505446268308878e11), // tan r for r near ±F/2: 108.5 bits, level 2 down.
    (ATAN, 8.915406962099676e-1),  // tan r: 85.1 bits, level 2 down.
    (ATAN, -3.727914694724161e0),  // Uniform: 80.3 bits, level 2 down.
    (ASIN, -9.983078951290868e-1), // sin r: 76.6 bits, level 2 down.
    (ASIN, 1.6362731384061311e-3), // Log-uniform: 76.6 bits, level 2 down.
    (ASIN, 1.1106174921949541e-1), // Uniform: 76.6 bits, level 2 down.
    (ACOS, 1.1379607369459111e-4), // cos r: 81.2 bits, level 2 down.
    (ACOS, -3.47639092730899e-1),  // Uniform: 76.7 bits, level 2 down.
];

const HARD_CASES2: [(f64, f64); 21] = [
    // The continued-fraction search, every pair that it kept: G near F and F/2, then random G.
    // Level 4 both ways, unless the comment says otherwise.
    (8.348261586694187e15, -3.1961893001271595e0), // G = F/2 + 2: 162.4 bits.
    (4.1201915676139095e1, -6.988558433347855e15), // G = F - 13: 160.3 bits.
    (4.04619298314177e-1, -3.303967303845392e15),  // G = F: 159.7 bits.
    (8.489318394131119e15, 1.748488697008458e1),   // G = F/2 - 9: 159.6 bits.
    (3.303967303845392e15, 2.023096491570885e-1),  // G = F/2: 159.5 bits.
    (6.696859921733803e15, 3.9916395715555847e8),  // G = F/2 - 2^28: 136.2 bits.
    (6.233561154109819e15, -1.4861967927238917e9), // G = F/2 + 2^30: 133.5 bits.
    (2.392500748241855e9, -5.017437727887909e15),  // G = F - 2^30: 128.8 bits.
    (4.364319539732576e15, 1.0405348636754832e9),  // G = F/2 - 2^30: 128.2 bits, level 2 down.
    (3.041429972524739e15, 3.568075885211432e8),   // G ≈ π/2 - 1.2e-7: 130.5 bits.
    (-5.623987414280757e15, 3.0515394011885803e11), // G ≈ -π/2 + 5.4e-5: 128.6 bits.
    (6.905814737551836e15, -6.601961719691604e9),  // G ≈ π/2 + 9.6e-7: 127.7 bits, level 2 down.
    (-4.407321304926047e15, 7.348978608197395e14), // G ≈ -1.4056: 127.4 bits, level 2 up.
    (-5.83492264382218e9, -8.000348713048871e15),  // G ≈ -π + 7.3e-7: 127.0 bits, level 2 down.
    (-6.4610141479295e14, -1.607126037342111e15),  // G ≈ -2.7593: 126.9 bits, level 2 down.
    // The list search at y next to q x for x > 0, the hardest and two others: y = 2^-51 -
    // 2^-104 and x = 1 + 2^-52 (106.6 bits), y = 2^-50 + 2^-100 and x = 1 + 5 2^-52 (105.6
    // bits), and y = 3 2^-26 - 2^-77, the `f64` below 3 2^-26, and x = 3 (104.2 bits). Level 2
    // both ways.
    (4.4408920985006257e-16, 1.0000000000000002e0),
    (8.88178419700126e-16, 1.000000000000001e0),
    (4.470348358154296e-8, 3e0),
    // The list search at |y / x| = (m1 / m2) 2^±k, the hardest: 63.5 bits, level 1 down, 2 up.
    (-1.1815284661573021e-23, 5.328167642752469e-3),
    // The random search, the hardest of atan2 at (sin r, cos r) rounded and scaled (80.7 bits,
    // level 2 down), and of atan2 log-uniform, where y is subnormal (76.9 bits, level 2 up).
    (2.3810621280335295e-95, -4.788119905650108e-94),
    (-5.978e-319, 7.440514250656314e-30),
];

// Each case, and its negation, at (-y, x) for atan2, where atan, asin and atan2 give the
// negated results, which need as many bits.
#[test]
fn hard_cases() {
    for (i, x) in HARD_CASES {
        check(i, x);
        check(i, -x);
    }
    for (y, x) in HARD_CASES2 {
        check2(y, x);
        check2(-y, x);
    }
}

#[test]
fn random_arguments() {
    let mut rng = Rng(64);
    for _ in 0..2000 {
        // Of any exponent, from the bits of a positive finite `f64`, and its negation: in
        // [0, 1) for asin and acos.
        for i in 0..FUNCTIONS.len() {
            let bits = match i {
                ATAN => rng.below(0x7ff0_0000_0000_0000),
                _ => rng.below(0x3ff0_0000_0000_0000),
            };
            let x = f64::from_bits(bits);
            check(i, x);
            check(i, -x);
            // Uniform in [-10, 10) for atan and in [-1, 1) for asin and acos.
            let u = rng.below(1 << 53) as f64 / (1u64 << 52) as f64 - 1.0;
            check(i, if i == ATAN { 10.0 * u } else { u });
        }
        // atan2 in all four quadrants: both arguments of any exponent, and y = q x, rounded,
        // for a q of magnitude in [2^-60, 2^61).
        let (y, x) = (
            f64::from_bits(rng.below(0x7ff0_0000_0000_0000)),
            f64::from_bits(rng.below(0x7ff0_0000_0000_0000)),
        );
        let x2 = 1.0 + rng.below(1 << 52) as f64 / (1u64 << 52) as f64;
        let q = (1.0 + rng.below(1 << 52) as f64 / (1u64 << 52) as f64)
            * pow2(rng.below(121) as i32 - 60);
        for (sy, sx) in QUADRANTS {
            check2(sy * y, sx * x);
            check2(sy * q * x2, sx * x2);
        }
    }
    for _ in 0..2000 {
        // Log-uniform, with a random sign: e in [-1074, 1023] for atan, and in [-60, -1] for
        // asin and acos, so that |x| < 1, which also take 1 - m 2^e for e in [-53, -2], in
        // [1/2, 1) and log-uniform in its distance from 1, which is at least 2^-53.
        for i in 0..FUNCTIONS.len() {
            let x = if i == ATAN {
                log_uniform(&mut rng, -1074, 1023)
            } else {
                let d = log_uniform(&mut rng, -53, -2);
                check(i, random_sign(&mut rng) * (1.0 - d));
                log_uniform(&mut rng, -60, -1)
            };
            check(i, random_sign(&mut rng) * x);
        }
        // atan2 in all four quadrants at y = my 2^(e + k) and x = mx 2^e, rounded as
        // `log_uniform` rounds them, so that |y / x| is about 2^k my / mx: k uniform in
        // [-2100, 2100] and clamped to [-2097, 2097], the most by which the exponents of two
        // `f64`s differ, and e uniform among the exponents for which e and e + k are both in
        // [-1074, 1023].
        let k = uniform(&mut rng, -2100, 2100).clamp(-2097, 2097);
        let e = uniform(&mut rng, (-1074).max(-1074 - k), 1023.min(1023 - k));
        let (y, x) = (
            log_uniform(&mut rng, e + k, e + k),
            log_uniform(&mut rng, e, e),
        );
        for (sy, sx) in QUADRANTS {
            check2(sy * y, sx * x);
        }
    }
}

// The three roundings of the function `i` at x, as the bits of the `f64`s: toward -∞, toward +∞
// and to nearest.
fn roundings(i: usize, x: f64) -> [u64; 3] {
    let f = FUNCTIONS[i].1;
    [
        f(x, false).to_bits(),
        f(x, true).to_bits(),
        NEAR[i](x).to_bits(),
    ]
}

// The same for atan2 at (y, x).
fn roundings2(y: f64, x: f64) -> [u64; 3] {
    [
        atan2(y, x, false).to_bits(),
        atan2(y, x, true).to_bits(),
        atan2_near(y, x).to_bits(),
    ]
}

// The function `i` gives the same `f64`s at x, in both directions and to nearest, with the fast
// path as with it disabled (`set_fast_path`), where the kernel computes every result that the
// rules leave, and `check` holds.
fn check_fast(i: usize, x: f64) {
    let fast = roundings(i, x);
    set_fast_path(false);
    let kernel = roundings(i, x);
    set_fast_path(true);
    assert!(
        fast == kernel,
        "{}({:e}): {:?} with the fast path != {:?} without it",
        FUNCTIONS[i].0,
        x,
        fast.map(f64::from_bits),
        kernel.map(f64::from_bits)
    );
    check(i, x);
}

// The same for atan2 at (y, x), with `check2`.
fn check2_fast(y: f64, x: f64) {
    let fast = roundings2(y, x);
    set_fast_path(false);
    let kernel = roundings2(y, x);
    set_fast_path(true);
    assert!(
        fast == kernel,
        "atan2({:e}, {:e}): {:?} with the fast path != {:?} without it",
        y,
        x,
        fast.map(f64::from_bits),
        kernel.map(f64::from_bits)
    );
    check2(y, x);
}

// atan, asin, acos and atan2 give the same `f64`s, in both directions and to nearest, with the
// fast path as with it disabled, and agree with MPFR, on random arguments of any exponent and of
// a moderate magnitude, and most of their rounding tests pass.
#[test]
fn fast_path_agrees_with_kernel() {
    let mut rng = Rng(91);
    for (i, (name, _)) in FUNCTIONS.iter().enumerate() {
        reset_fast_counts();
        for n in 0..3000 {
            let x = if n % 2 == 0 {
                // Of any exponent, from the bits of a positive finite `f64`, in [0, 1) for asin
                // and acos, with a random sign.
                let bits = match i {
                    ATAN => rng.below(0x7ff0_0000_0000_0000),
                    _ => rng.below(0x3ff0_0000_0000_0000),
                };
                random_sign(&mut rng) * f64::from_bits(bits)
            } else {
                // Uniform in [-10, 10) for atan and in [-1, 1) for asin and acos.
                let u = rng.below(1 << 53) as f64 / (1u64 << 52) as f64 - 1.0;
                if i == ATAN {
                    10.0 * u
                } else {
                    u
                }
            };
            check_fast(i, x);
        }
        let (passed, failed) = fast_counts();
        assert!(
            passed > 100 * failed,
            "{name}: {passed} passed, {failed} failed"
        );
    }
    // atan2 with both arguments of any exponent and random signs, and at y = q x, rounded, for a
    // q of magnitude in [2^-60, 2^61), in a random quadrant.
    reset_fast_counts();
    for n in 0..3000 {
        let (y, x) = if n % 2 == 0 {
            (
                random_sign(&mut rng) * f64::from_bits(rng.below(0x7ff0_0000_0000_0000)),
                random_sign(&mut rng) * f64::from_bits(rng.below(0x7ff0_0000_0000_0000)),
            )
        } else {
            let x = 1.0 + rng.below(1 << 52) as f64 / (1u64 << 52) as f64;
            let q = (1.0 + rng.below(1 << 52) as f64 / (1u64 << 52) as f64)
                * pow2(rng.below(121) as i32 - 60);
            (random_sign(&mut rng) * q * x, random_sign(&mut rng) * x)
        };
        check2_fast(y, x);
    }
    let (passed, failed) = fast_counts();
    assert!(
        passed > 100 * failed,
        "atan2: {passed} passed, {failed} failed"
    );
}

// The branches of the fast paths of atan, asin and acos, as (function, a, b) for the arguments x
// with |x| in [a, b) of each, which both signs of x take. atan takes the polynomial at |x|
// itself below about 1/128, where 64 |x| rounds to 0, from `TINY_NEAR` on (the directed rule
// settles |x| below `TINY_HYP`), the table up to 1, and π/2 - atan(1 / |x|) up to `HUGE_ATAN`.
// asin and acos take atan(t / √(1 - t^2)) up to `ASIN_S` and atan(√(1 - t^2) / t) above it, for
// t = |x|, and acos takes π/2 - x below `TINY_ASIN`, down to 2^-1074, and π - acos t for x < 0.
const BRANCHES: [(usize, f64, f64); 8] = [
    (ATAN, TINY_NEAR, 1.0 / 128.0),
    (ATAN, 1.0 / 128.0, 1.0),
    (ATAN, 1.0, HUGE_ATAN),
    (ASIN, TINY_ASIN, ASIN_S),
    (ASIN, ASIN_S, 1.0),
    (ACOS, 5e-324, TINY_ASIN),
    (ACOS, TINY_ASIN, ASIN_S),
    (ACOS, ASIN_S, 1.0),
];

// The branches of the fast path of atan2, as (swap, neg, lo, hi) for the arguments (y, x) with
// |y| > |x| if `swap`, x < 0 if `neg`, and q = min(|y|, |x|) / max(|y|, |x|) in [2^lo, 2^hi),
// in each of the four octants that `octant` takes. The core takes q where the exponents of the
// two arguments differ by at most 60, which q >= 2^-59 ensures, and q < 2^-62 ensures that they
// differ by more: there the fast path takes q itself for x > 0 and |y| < |x|, and π/2 ± q or
// π - q otherwise.
const BRANCHES2: [(bool, bool, i32, i32); 8] = [
    (false, false, -59, 0),
    (false, true, -59, 0),
    (true, false, -59, 0),
    (true, true, -59, 0),
    (false, false, -1000, -62),
    (false, true, -1000, -62),
    (true, false, -1000, -62),
    (true, true, -1000, -62),
];

// A random `f64` in [a, b), for 0 < a < b: uniform if `log` is false, and otherwise with an
// exponent uniform over those of [a, b] and a random significand.
fn in_range(rng: &mut Rng, a: f64, b: f64, log: bool) -> f64 {
    let exponent = |x: f64| (x.to_bits() >> 52) as i32 - 1023;
    loop {
        let t = if log {
            log_uniform(rng, exponent(a), exponent(b))
        } else {
            a + (b - a) * (rng.below(1 << 53) as f64 / (1u64 << 53) as f64)
        };
        if a <= t && t < b {
            return t;
        }
    }
}

// A random (y, x) in the branch (swap, neg, lo, hi) of `BRANCHES2`, with a random sign of y: q
// in [2^lo, 2^hi) from `in_range`, d = m 2^e for a random m in [1, 2) and an e uniform in
// [-20, 1000], and q d rounded, which is normal, as the other argument.
fn in_branch2(rng: &mut Rng, (swap, neg, lo, hi): (bool, bool, i32, i32), log: bool) -> (f64, f64) {
    let q = in_range(rng, pow2(lo), pow2(hi), log);
    let d = log_uniform(rng, -20, 1000);
    let (a, b) = if swap { (d, q * d) } else { (q * d, d) };
    (random_sign(rng) * a, if neg { -b } else { b })
}

// atan, asin, acos and atan2 on random arguments of each branch of their fast paths (`BRANCHES`
// and `BRANCHES2`), half uniform over the branch and half of any exponent in it, with either
// sign, against MPFR. Most of the rounding tests pass in each branch.
#[test]
fn fast_range_random() {
    let mut rng = Rng(911);
    for (i, a, b) in BRANCHES {
        reset_fast_counts();
        for n in 0..2000 {
            let t = in_range(&mut rng, a, b, n % 2 == 1);
            check(i, random_sign(&mut rng) * t);
        }
        let (passed, failed) = fast_counts();
        assert!(
            passed > 100 * failed,
            "{} on [{a:e}, {b:e}): {passed} passed, {failed} failed",
            FUNCTIONS[i].0
        );
    }
    for branch in BRANCHES2 {
        reset_fast_counts();
        for n in 0..2000 {
            let (y, x) = in_branch2(&mut rng, branch, n % 2 == 1);
            check2(y, x);
        }
        let (passed, failed) = fast_counts();
        assert!(
            passed > 100 * failed,
            "atan2 on {branch:?}: {passed} passed, {failed} failed"
        );
    }
}

// (h, l, e, err) of the fast path of the function `i` at x, as the function computes them before
// its rounding tests, or `None` where the fast path leaves x to the kernel, for an x that the
// rules leave: atan and asin take |x|, and give the sign of x to the rounding.
fn fast_parts(i: usize, x: f64) -> Option<(f64, f64, i64, f64)> {
    match i {
        ATAN => fast_atan_pos(x.abs()),
        ASIN => fast_asin_pos(x.abs()),
        ACOS => fast_acos_val(x),
        _ => unreachable!(),
    }
}

// The same for atan2 at (y, x), which takes |y| and |x| and gives the sign of y to the rounding.
fn fast_parts2(y: f64, x: f64) -> Option<(f64, f64, i64, f64)> {
    fast_atan2_pos(y.abs(), x.abs(), x < 0.0)
}

// atan, asin, acos and atan2 next to the edges of the table, of its index, of the reductions and
// of the ranges of their fast paths, both signs of each, where they give the same `f64`s with the
// fast path as with it disabled, and as MPFR (`check_fast`, `check2_fast`):
// - atan at the points j/64 of the table, at the ties (2j + 1)/128 of its index, and at their
//   inverses, which π/2 - atan(1 / t) takes, and the 2 `f64`s on each side of them;
// - asin and acos at the t at which t / √(1 - t^2) or √(1 - t^2) / t is one of those points, as
//   the `f64` arithmetic gives them, and the `f64` on each side;
// - atan at `TINY_NEAR`, `TINY_HYP`, 1 and `HUGE_ATAN`, asin and acos at `TINY_ASIN`, `ASIN_S`,
//   1/√2, where both quotients are 1, and 1, and the 3 `f64`s on each side of them, and acos at
//   0 and at 2^k for k in [-1074, -28], which π/2 - x takes;
// - atan2, in each quadrant and with y and x swapped, at |y| / |x| at the points and ties of the
//   table, at |y| = |x|, next to the axes, at exponents of |y| and |x| that differ by 59 to 62,
//   where the core stops, for x > 0 at quotients around 2^-1021, below which the results are left
//   to the kernel, and at the arguments of its rules: the zeros, infinities and NaN, the tiny
//   quotients of `rules_at_their_thresholds`, and odd multiples of 2^-1075, the midway quotients
//   of `midpoint_quotient`, and next to them.
// The fast path computes its parts at every argument of atan in [2^-27, 1], whose core has no
// quotient, of acos below 2^-27 and at -1, and of asin at ±1, and not of acos at 1; and for x > 0
// and exponents that differ by more than 60, exactly at the results of at least 2^-1021.
#[test]
fn fast_edges() {
    let mut args = vec![];
    for j in 0..=64 {
        let c = f64::from(j) / 64.0;
        let tie = f64::from(2 * j + 1) / 128.0;
        for t in [c, tie, 1.0 / c, 1.0 / tie] {
            if t.is_finite() && t > 0.0 {
                args.extend(around(t, 2).into_iter().map(|x| (ATAN, x)));
            }
        }
        // t / √(1 - t^2) = s for t = s / √(1 + s^2), and √(1 - t^2) / t = s for
        // t = 1 / √(1 + s^2).
        for s in [c, tie] {
            let r = (1.0 + s * s).sqrt();
            for t in [s / r, 1.0 / r] {
                if t > 0.0 && t < 1.0 {
                    for x in around(t, 1) {
                        args.push((ASIN, x));
                        args.push((ACOS, x));
                    }
                }
            }
        }
    }
    for t in [TINY_NEAR, TINY_HYP, 1.0, HUGE_ATAN] {
        args.extend(around(t, 3).into_iter().map(|x| (ATAN, x)));
    }
    for t in [TINY_ASIN, ASIN_S, FRAC_1_SQRT_2, 1.0] {
        for x in around(t, 3) {
            args.push((ASIN, x));
            args.push((ACOS, x));
        }
    }
    args.push((ACOS, 0.0));
    args.extend((-1074..=-28).map(|k| (ACOS, pow2(k))));
    for (i, x) in args {
        for x in [x, -x] {
            check_fast(i, x);
            let always = match i {
                ATAN => (TINY_NEAR..=1.0).contains(&x.abs()),
                ASIN => x.abs() == 1.0,
                _ => x.abs() < TINY_ASIN || x == -1.0,
            };
            assert!(
                !always || fast_parts(i, x).is_some(),
                "{}({:e}): no parts",
                FUNCTIONS[i].0,
                x
            );
        }
    }
    assert!(fast_parts(ACOS, 1.0).is_none());

    let mut args2 = vec![];
    // The points and ties of the table, as y / x.
    for j in 1..=64 {
        for (y, x) in [(f64::from(j), 64.0), (f64::from(2 * j - 1), 128.0)] {
            args2.extend(around(y, 1).into_iter().map(|y| (y, x)));
        }
    }
    // |y| = |x|, and next to it.
    for d in [
        1.0,
        3.0,
        0.75,
        pow2(-1000),
        pow2(1000),
        5e-324,
        f64::MIN_POSITIVE,
    ] {
        args2.extend(around(d, 2).into_iter().map(|y| (y, d)));
    }
    args2.push((f64::MAX, f64::MAX));
    args2.push((next_down(f64::MAX), f64::MAX));
    // Next to the axes.
    for t in [5e-324, 1.5e-323, f64::MIN_POSITIVE, pow2(-1000)] {
        for d in [1.0, 3.0, f64::MAX] {
            args2.push((t, d));
        }
    }
    // Exponents that differ by 59 to 62, scaled by powers of 2, which keeps the quotients.
    for n in [
        pow2(-62),
        pow2(-61),
        next_down(pow2(-60)),
        pow2(-60),
        1.5 * pow2(-60),
        next_down(pow2(-59)),
        pow2(-59),
        next_down(pow2(-58)),
    ] {
        for d in [1.0, next_up(1.0), 1.5, next_down(2.0)] {
            for s in [1.0, pow2(-500), pow2(500)] {
                args2.push((n * s, d * s));
            }
        }
    }
    // For x > 0, the quotients y / x = (my / mx) 2^e at the results around 2^-1021, at which the
    // fast path takes y / x itself, `normalize` scales my / mx into [1, 2), by 2 if my < mx,
    // which takes 1 from e, and the rounding tests scale the result back only if it is at least
    // 2^-1021.
    let ms = [1.0, next_up(1.0), 1.25, 1.5, next_down(2.0)];
    for e in -1024..=-1019 {
        for my in ms {
            for mx in ms {
                for k in [2, 30, 500, 1000] {
                    let (y, x) = (my * pow2(e + k), mx * pow2(k));
                    args2.push((y, x));
                    let scaled = e + if my < mx { -1 } else { 0 };
                    assert_eq!(
                        fast_parts2(y, x).is_some(),
                        scaled >= -1021,
                        "atan2({y:e}, {x:e})"
                    );
                }
            }
        }
    }
    // The rules: the zeros, infinities and NaN with each other and with finite values, the tiny
    // quotients, and the midway quotients (2m + 1) 2^-1075, here (2m + 1) 2^(j - 1074) / 2^(j + 1),
    // and next to them.
    for y in SPECIAL {
        for x in SPECIAL {
            args2.push((y, x));
        }
    }
    for q in [around(TINY_NEAR, 3), around(TINY_HYP, 3)].concat() {
        for d in [1.0, pow2(-1000), pow2(1000), 3.0, 0.75, f64::MAX / 3.0] {
            args2.push((q * d, d));
        }
    }
    for m in [0.0, 1.0, 2.0, 1e6] {
        for j in [0, 1, 30, 52] {
            let y = (2.0 * m + 1.0) * pow2(j - 1074);
            args2.extend(around(pow2(j + 1), 1).into_iter().map(|x| (y, x)));
        }
    }
    for (y, x) in args2 {
        for (sy, sx) in QUADRANTS {
            check2_fast(sy * y, sx * x);
            check2_fast(sx * x, sy * y);
        }
    }
}

// The rounding tests of the fast paths at (h, l, err), as `round_dir_err` and `round_near_err`
// take them: whether the directed tests pass but would fail with 2^6 err in place of err, and
// the same for the test to nearest.
fn narrow((h, l, _, err): (f64, f64, i64, f64)) -> (bool, bool) {
    let wide = 64.0 * err;
    // Half the gap between h and the next `f64` above it, and below it.
    let above = if h >= 1.0 {
        f64::EPSILON / 2.0
    } else {
        f64::EPSILON / 4.0
    };
    let below = if h > 1.0 {
        f64::EPSILON / 2.0
    } else {
        f64::EPSILON / 4.0
    };
    let h_ok = 0.5 < h && h < 2.0;
    (
        h_ok && err < l.abs() && l.abs() <= wide,
        h_ok && l < above - err
            && l > -(below - err)
            && (l >= above - wide || l <= -(below - wide)),
    )
}

// atan, asin, acos and atan2 where a rounding test of their fast paths passes, but would fail
// with 2^6 err in place of the bound err that the fast path returns, as in `hyp_widened` of
// `src/dyadic/exp/tests.rs`: there an error in the bound would show first, so the fast paths
// have to give the same `f64`s as the kernel, and as MPFR. Each branch of `BRANCHES` and
// `BRANCHES2` is sampled until it has 40 narrow passes of the directed tests and 40 of the test
// to nearest, but for the branches of atan2 at which the fast path adds a q below 2^-62 to π/2
// or π, or subtracts it, where the low part stays within 2^-62 of that of π/2 and the tests
// pass by far. A directed test is taken from `TINY_HYP` on for atan.
#[test]
fn widened() {
    let mut rng = Rng(912);
    for (i, a, b) in BRANCHES {
        let (mut dir, mut near, mut n) = (0, 0, 0);
        while dir < 40 || near < 40 {
            n += 1;
            assert!(
                n <= 1_000_000,
                "{} on [{a:e}, {b:e}): {dir} narrow passes of the directed tests and {near} of \
                 the test to nearest in 1000000 arguments",
                FUNCTIONS[i].0
            );
            let x = random_sign(&mut rng) * in_range(&mut rng, a, b, n % 2 == 1);
            let Some(parts) = fast_parts(i, x) else {
                continue;
            };
            let (narrow_dir, narrow_near) = narrow(parts);
            let narrow_dir = narrow_dir && (i != ATAN || x.abs() >= TINY_HYP);
            if !narrow_dir && !narrow_near {
                continue;
            }
            dir += usize::from(narrow_dir);
            near += usize::from(narrow_near);
            check_fast(i, x);
        }
    }
    for branch in BRANCHES2 {
        let (swap, neg, lo, _) = branch;
        if lo < -60 && (swap || neg) {
            continue;
        }
        let (mut dir, mut near, mut n) = (0, 0, 0);
        while dir < 40 || near < 40 {
            n += 1;
            assert!(
                n <= 1_000_000,
                "atan2 on {branch:?}: {dir} narrow passes of the directed tests and {near} of \
                 the test to nearest in 1000000 arguments"
            );
            let (y, x) = in_branch2(&mut rng, branch, n % 2 == 1);
            let Some(parts) = fast_parts2(y, x) else {
                continue;
            };
            let (narrow_dir, narrow_near) = narrow(parts);
            if !narrow_dir && !narrow_near {
                continue;
            }
            dir += usize::from(narrow_dir);
            near += usize::from(narrow_near);
            check2_fast(y, x);
        }
    }
}

#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
mod mpfr {
    use super::*;
    use crate::{
        dyadic::{consts::PI, reset_ziv_level, ziv_level},
        mpfr_calls::mpfr::*,
    };
    use rug::{
        float::{Constant, Round},
        Float,
    };

    type Mpfr = fn(f64) -> f64;

    const MPFR: [(Mpfr, Mpfr); 3] = [(atan_rd, atan_ru), (asin_rd, asin_ru), (acos_rd, acos_ru)];

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

    // The same for atan2 at (y, x), against `atan2_rd(y, x)` and `atan2_ru(y, x)`, whose first
    // argument is y, as for `mpfr_atan2`.
    pub(super) fn check2(y: f64, x: f64, lo: f64, hi: f64) {
        let (want_lo, want_hi) = (atan2_rd(y, x), atan2_ru(y, x));
        assert!(
            same(lo, want_lo) && same(hi, want_hi),
            "atan2({:e}, {:e}): ({:e}, {:e}) != MPFR's ({:e}, {:e})",
            y,
            x,
            lo,
            hi,
            want_lo,
            want_hi
        );
    }

    const MPFR_NEAR: [Mpfr; 3] = [atan_rn, asin_rn, acos_rn];

    // `near`, which the function `i` gave at `x` rounded to nearest, is MPFR's rounding to
    // nearest, or NaN where MPFR gives NaN.
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

    // The same for atan2 at (y, x), against `atan2_rn(y, x)`, whose first argument is y, as for
    // `mpfr_atan2`.
    pub(super) fn check2_near(y: f64, x: f64, near: f64) {
        let want = atan2_rn(y, x);
        assert!(
            same(near, want),
            "atan2({:e}, {:e}): {:e} to nearest != MPFR's {:e}",
            y,
            x,
            near,
            want
        );
    }

    // The highest level, in limbs, at which `ziv_near` returned in `atan2_near(y, x)`, as
    // `ziv_level` gives it: 0 where a rule settled it. `ziv_level` has the `cfg` of this module.
    pub(super) fn near_level2(y: f64, x: f64) -> usize {
        reset_ziv_level();
        atan2_near(y, x);
        ziv_level().0
    }

    // `PI` is floor(π 2^4222): the floors of π 2^4222 rounded down and up to 4,300 bits are
    // equal, so they are that of π 2^4222.
    #[test]
    fn pi_table() {
        use rug::integer::Order;
        let floor = |r| {
            let (f, _) = Float::with_val_round(4300, Constant::Pi, r);
            (f << 4222u32).to_integer_round(Round::Down).unwrap().0
        };
        let t = floor(Round::Down);
        assert_eq!(t, floor(Round::Up));
        assert_eq!(t.significant_bits(), 4224);
        let mut limbs = [0; 66];
        t.write_digits(&mut limbs, Order::Lsf);
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
        assert!(limbs == PI, "PI should be\n{}", rows);
    }

    // The precision of the values that the table and the constants of the fast path are checked
    // against, far above that of the bounds checked.
    const PREC: u32 = 300;

    // `pair` is the bits of [h, l] with h = RN(v), l = RN(v - h) and |h + l - v| <= 2^n.
    fn check_pair(name: &str, pair: [u64; 2], v: &Float, n: i32) {
        let (h, l) = (f64::from_bits(pair[0]), f64::from_bits(pair[1]));
        assert_eq!(h.to_bits(), v.to_f64().to_bits(), "{name}: {h:e} != RN(v)");
        let rest = Float::with_val(PREC, v - h);
        let mut err = Float::with_val(PREC, &rest - l);
        err.abs_mut();
        assert!(
            l.to_bits() == rest.to_f64().to_bits() && err <= pow2(n),
            "{name}: {l:e} != RN(v - h) = {:e}, or |h + l - v| = {:e} is above 2^{n}",
            rest.to_f64(),
            err.to_f64()
        );
    }

    // The table and the constants of the fast path of `atan.rs` are what the comments on them
    // say, with the bounds that `fast_atan_table_correct`, `fast_pio2_correct` and
    // `fast_atan_consts` in `rocq/theories/FastAtanTables.v` prove (the last with 2^-109 for
    // `A3`, below the 2^-108 of its comment).
    #[test]
    fn fast_atan_table_and_constants() {
        // Entry 0 is never read.
        assert_eq!(ATAN_TABLE[0], [0, 0], "ATAN_TABLE[0]");
        for (i, &pair) in ATAN_TABLE.iter().enumerate().skip(1) {
            let name = format!("ATAN_TABLE[{i}]");
            // atan(i / 64), with i / 64 exact.
            let mut v = Float::with_val(PREC, u32::try_from(i).unwrap());
            v /= 64;
            v.atan_mut();
            check_pair(&name, pair, &v, -104);
            // 2^-7 <= h <= 4/5 and |l| <= 2^-53 h, as `fast_atan_table_correct` states. h is at
            // most RN(π/4), and so below 4/5.
            let (h, l) = (f64::from_bits(pair[0]), f64::from_bits(pair[1]));
            assert!(
                pow2(-7) <= h && h <= std::f64::consts::FRAC_PI_4 && l.abs() <= pow2(-53) * h,
                "{name}: [{h:e}, {l:e}]"
            );
        }
        let pio2 = Float::with_val(PREC, Constant::Pi) / 2;
        check_pair("PIO2", PIO2, &pio2, -107);
        check_pair("A3", A3, &Float::with_val(PREC, 3).recip(), -108);
        for (name, a, n) in [
            ("A5", A5, 5),
            ("A7", A7, 7),
            ("A9", A9, 9),
            ("A11", A11, 11),
        ] {
            let want = Float::with_val(PREC, n).recip().to_f64();
            assert_eq!(
                a,
                want.to_bits(),
                "{name}: {:e} != RN(1/{n}) = {want:e}",
                f64::from_bits(a)
            );
        }
    }
}

mod levels;
mod mpfr_cases;
