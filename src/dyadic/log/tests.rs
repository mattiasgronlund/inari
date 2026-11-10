// Tests of the logarithms and inverse hyperbolic functions of the dyadic kernel. Every generator
// runs on every platform through `check`, which checks that the two directions give the same
// `f64` or two adjacent ones, or NaN for both, and that the function rounded to nearest gives
// one of them, or NaN. On 64-bit Linux and macOS, where the tests have MPFR, `check` also
// compares both directions and the rounding to nearest with the functions of
// `src/mpfr_calls/mpfr.rs` that compute the same function with MPFR, which they have to agree
// with bit for bit.

use super::*;
use crate::dyadic::tests::Rng;
use std::f64::consts::{FRAC_1_SQRT_2, SQRT_2};

type Directed = fn(f64, bool) -> f64;

const LN: usize = 0;
const LOG2: usize = 1;
const LOG10: usize = 2;
const ASINH: usize = 3;
const ACOSH: usize = 4;
const ATANH: usize = 5;

const FUNCTIONS: [(&str, Directed); 6] = [
    ("ln", ln),
    ("log2", log2),
    ("log10", log10),
    ("asinh", asinh),
    ("acosh", acosh),
    ("atanh", atanh),
];

type Near = fn(f64) -> f64;

// The functions of `FUNCTIONS` rounded to nearest, in the same order.
const NEAR: [Near; 6] = [
    ln_near, log2_near, log10_near, asinh_near, acosh_near, atanh_near,
];

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

// Arguments on which mismatches were found, as `(function, x)`, each with what it broke and
// where it was found.
fn regressions() -> Vec<(&'static str, &'static str)> {
    vec![]
}

// The index in `FUNCTIONS` of the function `name`.
fn index(name: &str) -> usize {
    FUNCTIONS.iter().position(|(n, _)| *n == name).unwrap()
}

#[test]
fn regressions_hold() {
    for (name, x) in regressions() {
        check(index(name), x.parse().unwrap());
    }
}

// The special values, and 2^k, 10^k and 1, whose results are exact.
#[test]
fn special_and_exact() {
    let special = [
        0.0,
        f64::from_bits(1),
        f64::MIN_POSITIVE,
        0.5,
        1.0,
        2.0,
        f64::MAX,
        f64::INFINITY,
    ];
    for i in 0..FUNCTIONS.len() {
        for x in special {
            check(i, x);
            check(i, -x);
        }
        check(i, f64::NAN);
    }
    for k in -1074..=1023 {
        let x = pow2(k);
        assert_eq!(log2(x, false), f64::from(k));
        assert_eq!(log2(x, true), f64::from(k));
        assert_eq!(log2_near(x), f64::from(k));
        for i in 0..FUNCTIONS.len() {
            check(i, x);
        }
    }
    for (k, &x) in POW10.iter().enumerate() {
        assert_eq!(log10(x, false), k as f64);
        assert_eq!(log10(x, true), k as f64);
    }
    // 10^k as the literal gives it, not as `POW10` holds it.
    for k in 0..=22 {
        let x: f64 = format!("1e{}", k).parse().unwrap();
        assert_eq!(log10_near(x), f64::from(k));
    }
    for i in [LN, LOG2, LOG10, ACOSH] {
        assert_eq!(FUNCTIONS[i].1(1.0, false).to_bits(), 0);
        assert_eq!(FUNCTIONS[i].1(1.0, true).to_bits(), 0);
        assert_eq!(NEAR[i](1.0).to_bits(), 0);
    }
    // asinh and atanh keep the sign of a zero.
    for i in [ASINH, ATANH] {
        for x in [0.0, -0.0] {
            for up in [false, true] {
                assert_eq!(FUNCTIONS[i].1(x, up).to_bits(), x.to_bits());
            }
            assert_eq!(NEAR[i](x).to_bits(), x.to_bits());
        }
    }
    assert_eq!(atanh_near(1.0), f64::INFINITY);
    assert_eq!(atanh_near(-1.0), f64::NEG_INFINITY);
}

// The exact enclosures of log2 2^k, for k from -1074 to 1023, and of ln 1 and acosh 1, which no
// rule settles: `Log2` gives the point k at 2^k, and `Ln` and `Acosh` the point 0 at 1, whose
// `f64` is +0 (`ev_log2_exact`, `ev_ln_one` and `ev_acosh_one`).
#[test]
fn exact_enclosures() {
    use crate::dyadic::tests::check_exact;
    for k in -1074..=1023 {
        check_exact(&Log2(pow2(k)), f64::from(k), &format!("log2(2^{})", k));
    }
    check_exact(&Ln(1.0), 0.0, "ln(1)");
    check_exact(&Acosh(1.0), 0.0, "acosh(1)");
}

// Each rule of `log.rs` at its threshold and the 3 `f64`s on each side of it, both signs of
// them, and the special values. The thresholds are `TINY_HYP`, below which asinh and atanh are
// within an ulp of x, `TINY_NEAR`, below which `asinh_near` and `atanh_near` give x, 1 for
// acosh and atanh, where their domains end, and for the logarithms the smallest positive `f64`,
// below which come zero and the negative numbers, the smallest normal one, and the 4 largest
// ones, below +∞. log10 also has the powers of 10 of `POW10`, which its rule takes.
#[test]
fn rules_at_their_thresholds() {
    let smallest = f64::from_bits(1);
    let thresholds: [&[f64]; 6] = [
        &[smallest, f64::MIN_POSITIVE],
        &[smallest, f64::MIN_POSITIVE],
        &[smallest, f64::MIN_POSITIVE],
        &[TINY_NEAR, TINY_HYP],
        &[1.0],
        &[TINY_NEAR, TINY_HYP, 1.0],
    ];
    let special = [
        0.0,
        smallest,
        f64::MIN_POSITIVE,
        1.0,
        f64::MAX,
        f64::INFINITY,
    ];
    for (i, thresholds) in thresholds.iter().enumerate() {
        for &x in *thresholds {
            for x in around(x, 3) {
                check(i, x);
                check(i, -x);
            }
        }
        let mut x = f64::MAX;
        for _ in 0..4 {
            check(i, x);
            check(i, -x);
            x = next_down(x);
        }
        for x in special {
            check(i, x);
            check(i, -x);
        }
        check(i, f64::NAN);
    }
    for &x in &POW10 {
        for x in around(x, 3) {
            check(LOG10, x);
        }
    }
}

// The arguments at which the reductions of `log.rs` change their e or their branch, with the 3
// `f64`s on each side of them. `reduce` takes m = 2^-e x in [1/√2, √2), so that e changes at
// 2^k / √2, up to 2^-64 of it, near which `FRAC_1_SQRT_2` 2^k is taken for every k, rounded
// for the subnormals, and 2^1023 √2. asinh, acosh and atanh take the series up to
// `SERIES_MAX` and `ACOSH_SERIES_MAX`, and above them ln of t + √(t^2 + 1), x + √(x^2 - 1)
// and (1 + t) / (1 - t), which are y = 2^k / √2 at t = (y - 1 / y) / 2, x = (y + 1 / y) / 2
// and t = (y - 1) / (y + 1). Those are taken as `f64` computes them, near the arguments at
// which e changes.
#[test]
fn reductions_at_their_edges() {
    let edges = (-1074..=1023)
        .map(|k| FRAC_1_SQRT_2 * pow2(k))
        .chain([SQRT_2 * pow2(1023)]);
    for x in edges {
        for x in around(x, 3) {
            for i in [LN, LOG2, LOG10] {
                check(i, x);
            }
        }
    }
    for x in around(SERIES_MAX, 3) {
        for i in [ASINH, ATANH] {
            check(i, x);
            check(i, -x);
        }
    }
    for x in around(ACOSH_SERIES_MAX, 3) {
        check(ACOSH, x);
    }
    for k in 1..=1023 {
        let y = FRAC_1_SQRT_2 * pow2(k);
        for x in around((y - 1.0 / y) / 2.0, 3) {
            check(ASINH, x);
            check(ASINH, -x);
        }
        for x in around((y + 1.0 / y) / 2.0, 3) {
            check(ACOSH, x);
        }
        // At k = 1, t is below `SERIES_MAX`. Above 2^52, y ± 1 rounds, and at k = 53 and 54,
        // e changes between two of the 3 `f64`s below 1 that `rules_at_their_thresholds`
        // takes, 1 - j 2^-53 for j = 1, 2, 3, at which (1 + t) / (1 - t) is about 2^54 / j.
        if (2..=52).contains(&k) {
            for x in around((y - 1.0) / (y + 1.0), 3) {
                check(ATANH, x);
                check(ATANH, -x);
            }
        }
    }
}

// Arguments whose results are close to an `f64`, so that `ziv` may need more than one level
// for them, with the roundings that follow where bounds determine them.
//
// ln and log2 at 1 ± y for y = 2^-k, where only ln has bounds. For 0 < y < 1,
// y - y^2 / 2 < ln(1 + y) < y - y^2 / 2 + y^3 / 3. For 26 <= k <= 52, f = y - y^2 / 2 is an
// `f64` of [2^-(k + 1), 2^-k), whose ulp 2^-(k + 53) is above y^3 / 3, so that ln(1 + y) is
// between f and the next `f64` up. For 0 < y <= 1/2, -g - y^3 / (3 (1 - y)) < ln(1 - y) < -g
// for g = y + y^2 / 2. For 26 <= k <= 51, g is an `f64` of (2^-k, 2^(1 - k)), whose ulp
// 2^-(k + 52) is above y^3 / (3 (1 - y)), so that ln(1 - y) is between -g and the next `f64`
// down. For k = 52 and 53, g + y^3 / (3 (1 - y)) is below y + 2^-(k + 52), the next `f64`
// above y, so that ln(1 - y) is between -y and the next `f64` down.
//
// log10 at the `f64` x nearest 10^k, as `parse` gives it, for k from -323 to -1 and from 23
// to 308, where 10^k is not an `f64`. For x normal, from k = -307 on, |x / 10^k - 1| <= 2^-53,
// so that 0 < |log10 x - k| <= 2^-53 / ((1 - 2^-53) ln 10) < 2^-54, and the `f64`s next to k
// are at least 2^-53 from it. So log10 x is between k and the `f64` next to k on its side.
//
// log2 at the `f64`s x next to 2^k. For k >= -1022, |x / 2^k - 1| <= 2^-52, so that
// 0 < |log2 x - k| <= 2^-52 / ((1 - 2^-52) ln 2) < 2^-51, and for |k| >= 3 the `f64`s next to
// k are at least 2^-51 from it. So log2 x is between k and the `f64` next to k on its side.
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
    for k in 1..=53 {
        let y = pow2(-k);
        if k <= 52 {
            check(LOG2, 1.0 + y);
            if k >= 26 {
                let f = y - y * y / 2.0;
                expect(LN, 1.0 + y, f, next_up(f));
            } else {
                check(LN, 1.0 + y);
            }
        }
        check(LOG2, 1.0 - y);
        if k >= 26 {
            let g = if k <= 51 { y + y * y / 2.0 } else { y };
            expect(LN, 1.0 - y, next_down(-g), -g);
        } else {
            check(LN, 1.0 - y);
        }
    }
    for k in (-323..=-1).chain(23..=308) {
        let x: f64 = format!("1e{}", k).parse().unwrap();
        check(LOG10, x);
        if x >= f64::MIN_POSITIVE {
            let (lo, hi) = (log10(x, false), log10(x, true));
            let k = f64::from(k);
            assert!(
                (lo == k && hi == next_up(k)) || (lo == next_down(k) && hi == k),
                "log10({:e}): ({:e}, {:e}) is not k = {} and an `f64` next to it",
                x,
                lo,
                hi,
                k
            );
        }
    }
    for k in -1074..=1023 {
        let (above, below) = (next_up(pow2(k)), next_down(pow2(k)));
        if k >= -1022 && k.abs() >= 3 {
            let k = f64::from(k);
            expect(LOG2, above, k, next_up(k));
            expect(LOG2, below, next_down(k), k);
        } else {
            check(LOG2, above);
            check(LOG2, below);
        }
    }
}

// The hardest arguments that a search found, as (function, x): those whose results are the
// closest to an `f64` relative to the result, so that a directed rounding of them needs the
// most bits. The search, a harness outside the crate, rounded each argument down and up at the
// first level of `ziv` that settles it (`ziv_at::<N>` for N = 1, 2, 4, .., 64 limbs), compared
// both roundings with MPFR's, and measured the bits that each needs, -log2 of the distance from
// f(x) to the nearest `f64` relative to |f(x)|, with MPFR at 1024 bits. It ran on lists: ln,
// log2 and log10 at 1 ± j 2^-k for j in 1, 3, 5, 7, 9, 15, acosh at 1 + j 2^-k and at
// 1 + m 2^-52 for m up to 4096, atanh at ±(1 - j 2^-k); ln and log2 within two `f64`s of 2^k;
// log10 next to 10^k; ln at the `f64`s nearest e^k, log2 nearest 2^(k + 1/2), log10 nearest
// 10^k and 10^(k + 1/2), asinh nearest sinh(k) and acosh nearest cosh(k), with their
// neighbours; asinh and atanh just above 2^-26 to 2^-20; tlog.c l.91-169; the test inputs of
// pxfm 0.1.30; and each function at the results of the cases of `src/dyadic/exp/tests.rs`,
// rounded down and up. It also ran on 2.4 million random arguments per function, half uniform
// in [0.1, 10] (in [-10, 10] for asinh, [1, 10] for acosh and [-1, 1] for atanh) and half
// log-uniform over the exponents from -1074 (-26 for asinh and atanh, 0 for acosh) to 1023 (-1
// for atanh), with a random sign for asinh and atanh, from `Rng(1_000_003 (i + 1) + 7919 t + 6)`
// for function i in thread t of 6, and on 1.2 million per function, f^-1(r) rounded down and up
// for r uniform in a range of the function, from `Rng(1_000_003 (i + 1) + 7919 t + 7)`. It
// found no mismatch with MPFR, and every rounding settled at level 1 or 2. Each comment gives
// the source of its cases, the bits that they need, and their level down and up. Some settle at
// level 1 in one direction although they need more bits than the level-1 enclosure gives.
const HARD_CASES: [(usize, f64); 40] = [
    // tlog.c l.91-169, also in `MPFR_RESULTS`: 114.2 bits, level 2 both ways.
    (LN, 4.2831524716519823e2),
    // ln at 1 ± j 2^-k, the case that needs the most bits for each j and sign. 1 + 2^-52 is also
    // the hardest for ln next to 2^k, near e^k and at exp's results. Level 1 in the direction of
    // the `f64` nearest the result, and 2 in the other.
    (LN, 1.0000000000000002e0), // 1 + 2^-52: 105.6 bits, level 1 down, 2 up.
    (LN, 9.999999999999996e-1), // 1 - 2^-51: 103.6 bits, level 2 down, 1 up.
    (LN, 1.0000000000000027e0), // 1 + 3 2^-50: 98.4 bits, level 1 down, 2 up.
    (LN, 9.999999999999973e-1), // 1 - 3 2^-50: 98.4 bits, level 2 down, 1 up.
    (LN, 1.0000000000000089e0), // 1 + 5 2^-49: 94.9 bits, level 1 down, 2 up.
    (LN, 9.999999999999911e-1), // 1 - 5 2^-49: 94.9 bits, level 2 down, 1 up.
    (LN, 1.0000000000000124e0), // 1 + 7 2^-49: 94.0 bits, level 1 down, 2 up.
    (LN, 9.999999999999876e-1), // 1 - 7 2^-49: 94.0 bits, level 2 down, 1 up.
    (LN, 9.99999999999968e-1),  // 1 - 9 2^-48: 91.2 bits, level 2 down, 1 up.
    (LN, 1.0000000000000533e0), // 1 + 15 2^-48: 89.8 bits, level 1 down, 2 up.
    (LN, 9.999999999999467e-1), // 1 - 15 2^-48: 89.8 bits, level 2 down, 1 up.
    // acosh at 1 + 9 2^-49, the hardest of acosh at 1 + j 2^-k and at 1 + m 2^-52: 97.4 bits,
    // level 2 both ways.
    (ACOSH, 1.000000000000016e0),
    // ln near e^-652, the hardest near e^k away from 1: 74.0 bits, level 2 both ways.
    (LN, 6.918274648626584e-284),
    // ln at the second `f64` below 2^-488, the hardest next to 2^k away from 1 (65.3 bits, level
    // 2 both ways), and at the subnormal after 2^-1052 (64.5 bits, level 1 down, 2 up).
    (LN, 1.2513019344894378e-147),
    (LN, 2.072262e-317),
    // log2 next to 2^1023, the hardest next to 2^k: 62.5 bits, level 1 both ways.
    (LOG2, 8.988465674311579e307),
    // log2 near 2^1023.5, the hardest near 2^(k + 1/2): 63.2 bits, level 1 both ways.
    (LOG2, 1.2711610061536464e308),
    // log10 near 10^288.5, the hardest near 10^(k + 1/2): 72.4 bits, level 2 both ways.
    (LOG10, 3.1622776601683793e288),
    // log10 at the `f64` nearest 10^303, the hardest near 10^k for k outside 0..=22: 71.9 bits,
    // level 2 both ways.
    (LOG10, 1e303),
    // log10 next to 10^21, the hardest next to 10^k for k in 1..=22: 58.4 bits, level 1 both
    // ways.
    (LOG10, 1.0000000000000001e21),
    // asinh near sinh(430) and acosh near cosh(430), the hardest near sinh(k) and cosh(k): 71.6
    // bits, level 2 both ways.
    (ASINH, 2.789955155893247e186),
    (ACOSH, 2.789955155893247e186),
    // asinh at 2^-20, the hardest just above 2^-26 to 2^-20: 54.6 bits, level 1 both ways.
    (ASINH, 9.5367431640625e-7),
    // The hardest test input of pxfm: 58.7 bits, level 1 both ways.
    (ASINH, 1.0526885986327326e0),
    // The hardest asinh and acosh at the results of exp's cases: 62.6 bits, level 1 down, 2 up,
    // and 65.5 bits, level 2 both ways.
    (ASINH, 7.852690016575733e6),
    (ACOSH, 1.0086311513636718e77),
    // The hardest random arguments, per function, the second of atanh in the range of its
    // series. Level 2 both ways, except log2 (level 2 down, 1 up).
    (LN, 7.775120507232605e169),     // 75.2 bits.
    (LOG2, 1.51136190664259e107),    // 74.1 bits.
    (LOG10, 8.194942093406975e-100), // 75.4 bits.
    (ASINH, -3.8735164202812555e-1), // 74.7 bits.
    (ACOSH, 2.383645937454283e0),    // 75.2 bits.
    (ATANH, 4.4796266295664355e-1),  // 79.7 bits.
    (ATANH, 9.104567831125394e-7),   // 78.9 bits.
    // The hardest f^-1(r) rounded, per function: level 2 both ways.
    (LN, 9.946339317862028e240),    // 81.6 bits.
    (LOG2, 5.543726686531611e-64),  // 83.4 bits.
    (LOG10, 9.383416516329039e213), // 81.3 bits.
    (ASINH, 6.91487967188642e67),   // 82.2 bits.
    (ACOSH, 3.397882864903889e298), // 81.9 bits.
    (ATANH, 4.6179927454093633e-1), // 72.5 bits.
];

#[test]
fn hard_cases() {
    for (i, x) in HARD_CASES {
        check(i, x);
    }
}

#[test]
fn random_arguments() {
    let mut rng = Rng(64);
    for i in 0..FUNCTIONS.len() {
        for _ in 0..2000 {
            // Of any exponent, from the bits of a positive finite `f64`, which are of [0, 1)
            // for atanh, and of [1, +∞) for acosh, and its negation, which is outside the
            // domains of the logarithms and acosh.
            let bits = match i {
                ACOSH => {
                    0x3ff0_0000_0000_0000 + rng.below(0x7ff0_0000_0000_0000 - 0x3ff0_0000_0000_0000)
                }
                ATANH => rng.below(0x3ff0_0000_0000_0000),
                _ => rng.below(0x7ff0_0000_0000_0000),
            };
            let x = f64::from_bits(bits);
            check(i, x);
            check(i, -x);
            // Uniform in [0, 2] for atanh and [0, 64] otherwise, and above 1 for acosh.
            let u = rng.below(1 << 53) as f64 / (1u64 << 53) as f64;
            let x = match i {
                ACOSH => 1.0 + 63.0 * u,
                ATANH => 2.0 * u,
                _ => 64.0 * u,
            };
            check(i, x);
            check(i, -x);
            // m 2^e for a random m in [1, 2) and a random e, rounded to a subnormal below
            // e = -1022: e in [-1074, 1023] for the logarithms, [0, 1023] for acosh, so that
            // x >= 1, and [-60, 60] for asinh and [-60, -1] for atanh, so that |x| < 1, both
            // with a random sign.
            let (lo, hi) = match i {
                ASINH => (-60, 60),
                ACOSH => (0, 1023),
                ATANH => (-60, -1),
                _ => (-1074, 1023),
            };
            let e = lo + rng.below(u64::try_from(hi - lo + 1).unwrap()) as i32;
            let m = 1.0 + rng.below(1 << 52) as f64 / (1u64 << 52) as f64;
            let s = if (i == ASINH || i == ATANH) && rng.below(2) == 0 {
                -1.0
            } else {
                1.0
            };
            check(i, s * m * pow2(e));
        }
    }
}

// ln x, log2 x and log10 x give the same `f64`s, in both directions and to nearest, with the fast
// path as with it disabled, and agree with MPFR, on random arguments of every exponent and near
// 1, and most of its rounding tests pass.
#[test]
fn fast_path_agrees_with_kernel() {
    let mut rng = Rng(88);
    for i in [LN, LOG2, LOG10] {
        crate::dyadic::fast::reset_fast_counts();
        for n in 0..3000 {
            let x = if n % 2 == 0 {
                // Any positive finite `f64`, subnormals included.
                f64::from_bits(1 + rng.below(0x7fef_ffff_ffff_ffff))
            } else {
                // Within 2^-8 of 1.
                1.0 + (rng.below(1 << 53) as f64 / (1u64 << 53) as f64 - 0.5) / 128.0
            };
            let fast = (
                FUNCTIONS[i].1(x, false),
                FUNCTIONS[i].1(x, true),
                NEAR[i](x),
            );
            crate::dyadic::fast::set_fast_path(false);
            let kernel = (
                FUNCTIONS[i].1(x, false),
                FUNCTIONS[i].1(x, true),
                NEAR[i](x),
            );
            crate::dyadic::fast::set_fast_path(true);
            assert!(
                fast.0.to_bits() == kernel.0.to_bits()
                    && fast.1.to_bits() == kernel.1.to_bits()
                    && fast.2.to_bits() == kernel.2.to_bits(),
                "{}({:e}): {:?} with the fast path != {:?} without it",
                FUNCTIONS[i].0,
                x,
                fast,
                kernel
            );
            check(i, x);
        }
        let (passed, failed) = crate::dyadic::fast::fast_counts();
        assert!(
            passed > 100 * failed,
            "{}: {passed} passed, {failed} failed",
            FUNCTIONS[i].0
        );
    }
}

// (h, l, k) of the fast path of ln, log2 or log10 (the function `i`) at a finite x > 0, as the
// function computes them, or `None` at x = 1.
fn fast_parts(i: usize, x: f64) -> Option<(f64, f64, i64)> {
    match i {
        LN => fast_ln(x),
        LOG2 => fast_log_by(x, C2, ONE),
        LOG10 => fast_log_by(x, C10, LG2),
        _ => unreachable!(),
    }
}

// A random positive finite `f64`, subnormals included, from uniform bits, so that its exponent
// is about uniform.
fn any_positive(rng: &mut Rng) -> f64 {
    f64::from_bits(1 + rng.below(0x7fef_ffff_ffff_ffff))
}

// 1 + d or 1 - d, rounded, for a random d with an exponent in [lo, hi] and a random significand.
fn near_one(rng: &mut Rng, lo: i32, hi: i32) -> f64 {
    let e = lo + rng.below(u64::try_from(hi - lo + 1).unwrap()) as i32;
    let d = (1.0 + rng.below(1 << 52) as f64 / (1u64 << 52) as f64) * pow2(e);
    if rng.below(2) == 0 {
        1.0 + d
    } else {
        1.0 - d
    }
}

// ln x, log2 x and log10 x on random arguments of the fast path: of any exponent, subnormals
// included, and 1 ± d for d with an exponent in [-30, -9], which the two intervals of the table
// around 1 take, where r = 1. Most of its rounding tests pass on both. Closer to 1, 1 ± d for d
// with an exponent in [-53, -31], are only checked: there z = x - 1 has few bits, so that for
// the smallest d, z - z^2/2 is often an `f64`, from which ln x differs by about |z|^3/3, less
// than 2^-68 relative, so that the directed tests of ln fail at some of them.
#[test]
fn fast_range_random() {
    let mut rng = Rng(881);
    for i in [LN, LOG2, LOG10] {
        crate::dyadic::fast::reset_fast_counts();
        for _ in 0..2000 {
            check(i, any_positive(&mut rng));
        }
        let (passed, failed) = crate::dyadic::fast::fast_counts();
        crate::dyadic::fast::reset_fast_counts();
        for _ in 0..2000 {
            check(i, near_one(&mut rng, -30, -9));
        }
        let (near_passed, near_failed) = crate::dyadic::fast::fast_counts();
        for _ in 0..1000 {
            check(i, near_one(&mut rng, -53, -31));
        }
        assert!(
            passed > 100 * failed && near_passed > 100 * near_failed,
            "{}: {passed} passed, {failed} failed on arguments of any exponent, {near_passed} \
             passed, {near_failed} failed near 1",
            FUNCTIONS[i].0
        );
    }
}

// The exponents k of the arguments of `table_and_reduction_edges`: the ends, those of the
// subnormals at which (1 + j/512) 2^k is exact, those around 2^-1022 and 1, and every 51st in
// between.
fn edge_exponents() -> Vec<i32> {
    [
        -1065, -1064, -1053, -1052, -1023, -1022, -1021, -2, -1, 0, 1, 2, 1022, 1023,
    ]
    .into_iter()
    .chain((-1020..=1020).step_by(51))
    .collect()
}

// ln x, log2 x and log10 x next to the edges of the table and of the reduction of the fast path:
// x = (1 + j/512) 2^k, at which j, the top 9 bits of the significand, and with them the index of
// `LOG_TABLE`, change, for every j in [0, 511]. From j = 211 to 212, the index wraps from 361 to
// 0 and m from M to M / 2, and for k = -1 and 0, 511/512 and 513/512 are the ends of the two
// intervals around 1, where r = 1. Then 1 ± n ulp for n up to 64, the smallest subnormals and
// the largest `f64`s. The fast path computes (h, l, k) at all of them but 1.
#[test]
fn table_and_reduction_edges() {
    let mut args = vec![];
    for k in edge_exponents() {
        for j in 0..512 {
            args.extend(around((1.0 + f64::from(j) / 512.0) * pow2(k), 1));
        }
    }
    args.extend(around(1.0, 64));
    args.extend((1..=64).map(f64::from_bits));
    let mut x = f64::MAX;
    for _ in 0..64 {
        args.push(x);
        x = next_down(x);
    }
    for i in [LN, LOG2, LOG10] {
        for &x in &args {
            check(i, x);
            assert_eq!(
                fast_parts(i, x).is_some(),
                x != 1.0,
                "{}({:e})",
                FUNCTIONS[i].0,
                x
            );
        }
    }
}

// 2^-68, the bound on |y - (h + l)| that the rounding tests of `src/dyadic/fast.rs` assume, and
// 2^-58, 2^10 times as large.
const FAST_ERR: f64 = 1.0 / 295_147_905_179_352_825_856.0;
const WIDE: f64 = 1.0 / 288_230_376_151_711_744.0;

// ln x, log2 x and log10 x where a rounding test of the fast path passes, but would fail with
// `WIDE` in place of the bound 2^-68: h + l is within 2^-58 of h, which a directed rounding
// cannot cross, or of a midpoint between h and the next `f64`, which the rounding to nearest
// cannot cross. There an error in the bound would show first, so the fast path has to give the
// same `f64`s as the kernel, and as MPFR. The arguments are of the two kinds that
// `fast_range_random` counts.
#[test]
fn widened() {
    let mut rng = Rng(882);
    for i in [LN, LOG2, LOG10] {
        let (mut dir, mut near) = (0, 0);
        for n in 0..8000 {
            let x = if n % 2 == 0 {
                any_positive(&mut rng)
            } else {
                near_one(&mut rng, -30, -9)
            };
            let Some((h, l, _)) = fast_parts(i, x) else {
                continue;
            };
            // |h| and l with the sign of h, which `round_dir_signed` and `round_near_signed`
            // pass to the rounding tests. 1 <= |h| < 2, so that half the gap between |h| and the
            // next `f64` above it is 2^-53, and below it 2^-53 too, or 2^-54 at |h| = 1.
            let (h, l) = if h < 0.0 { (-h, -l) } else { (h, l) };
            let above = f64::EPSILON / 2.0;
            let below = if h > 1.0 {
                f64::EPSILON / 2.0
            } else {
                f64::EPSILON / 4.0
            };
            let narrow_dir = FAST_ERR < l.abs() && l.abs() <= WIDE;
            let narrow_near = l < above - FAST_ERR
                && l > -(below - FAST_ERR)
                && (l >= above - WIDE || l <= -(below - WIDE));
            if !narrow_dir && !narrow_near {
                continue;
            }
            dir += usize::from(narrow_dir);
            near += usize::from(narrow_near);
            let f = FUNCTIONS[i].1;
            let fast = (f(x, false), f(x, true), NEAR[i](x));
            crate::dyadic::fast::set_fast_path(false);
            let kernel = (f(x, false), f(x, true), NEAR[i](x));
            crate::dyadic::fast::set_fast_path(true);
            assert!(
                fast.0.to_bits() == kernel.0.to_bits()
                    && fast.1.to_bits() == kernel.1.to_bits()
                    && fast.2.to_bits() == kernel.2.to_bits(),
                "{}({:e}): {:?} with the fast path != {:?} without it",
                FUNCTIONS[i].0,
                x,
                fast,
                kernel
            );
            check(i, x);
        }
        assert!(
            dir >= 20 && near >= 20,
            "{}: {dir} narrow passes of the directed tests and {near} of the test to nearest",
            FUNCTIONS[i].0
        );
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
        Float,
    };

    type Mpfr = fn(f64) -> f64;

    const MPFR: [(Mpfr, Mpfr); 6] = [
        (ln_rd, ln_ru),
        (log2_rd, log2_ru),
        (log10_rd, log10_ru),
        (asinh_rd, asinh_ru),
        (acosh_rd, acosh_ru),
        (atanh_rd, atanh_ru),
    ];

    // `lo` and `hi`, which the function `i` gave at `x`, are MPFR's roundings, or NaN where
    // MPFR gives NaN.
    pub(super) fn check(i: usize, x: f64, lo: f64, hi: f64) {
        let (want_lo, want_hi) = (MPFR[i].0(x), MPFR[i].1(x));
        let same = |a: f64, b: f64| a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan());
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

    const MPFR_NEAR: [Mpfr; 6] = [ln_rn, log2_rn, log10_rn, asinh_rn, acosh_rn, atanh_rn];

    // `near`, which the function `i` rounded to nearest gave at `x`, is MPFR's rounding to
    // nearest, or NaN where MPFR gives NaN.
    pub(super) fn check_near(i: usize, x: f64, near: f64) {
        let want = MPFR_NEAR[i](x);
        assert!(
            near.to_bits() == want.to_bits() || (near.is_nan() && want.is_nan()),
            "{}({:e}): {:e} to nearest != MPFR's {:e}",
            FUNCTIONS[i].0,
            x,
            near,
            want
        );
    }

    // The precision of the values that the table, the constants and the results of the fast path
    // are checked against, far above that of the bounds checked.
    const PREC: u32 = 300;

    // `l` = RN(v - h) and |v - h - l| < 2^n.
    fn check_low(name: &str, v: &Float, h: f64, l: f64, n: i32) {
        let rest = Float::with_val(PREC, v - h);
        let mut err = Float::with_val(PREC, &rest - l);
        err.abs_mut();
        assert!(
            l.to_bits() == rest.to_f64().to_bits() && err < pow2(n),
            "{name}: {l:e} != RN(v - h) = {:e}, or |v - h - l| = {:e} is not below 2^{n}",
            rest.to_f64(),
            err.to_f64()
        );
    }

    // `pair` is the bits of [RN(v), RN(v - RN(v))], within 2^n of v.
    fn check_pair(name: &str, pair: [u64; 2], v: &Float, n: i32) {
        let h = f64::from_bits(pair[0]);
        assert_eq!(h.to_bits(), v.to_f64().to_bits(), "{name}: {h:e} != RN(v)");
        check_low(name, v, h, f64::from_bits(pair[1]), n);
    }

    // The table and the constants of the fast path of `log.rs` are what the comments on them
    // say, with the bounds that `ltbl_correct` and the theorems on the constants in
    // `rocq/theories/FastLogTables.v` prove.
    #[test]
    fn fast_log_table_and_constants() {
        for (i, &[r, th, tl]) in LOG_TABLE.iter().enumerate() {
            let name = format!("LOG_TABLE[{i}]");
            let i = u32::try_from(i).unwrap();
            let (rf, h, l) = (f64::from_bits(r), f64::from_bits(th), f64::from_bits(tl));
            if i == 149 || i == 150 {
                assert!(
                    rf == 1.0 && th == 0 && tl == 0,
                    "{name}: [{rf:e}, {h:e}, {l:e}] != [1, 0, 0]"
                );
                continue;
            }
            // r = RN(1024 / (725 + 2 i)), with 1024 / (725 + 2 i) not a midpoint.
            let want = Float::with_val(PREC, 1024) / (725 + 2 * i);
            assert_eq!(r, want.to_f64().to_bits(), "{name}: r");
            let mut v = Float::with_val(PREC, rf);
            v.ln_mut();
            v = -v;
            check_pair(&name, [th, tl], &v, -104);
            assert!(
                pow2(-9) <= h.abs() && h.abs() <= 0.375 && l.abs() <= pow2(-53) * h.abs(),
                "{name}: [{h:e}, {l:e}]"
            );
            // |r m - 1| <= 3/2048 at both ends of the interval of m, and so on all of it.
            for end in [362 + i, 363 + i] {
                let mut z = Float::with_val(PREC, rf) * end;
                z /= 512;
                z -= 1;
                z.abs_mut();
                assert!(
                    z <= 3.0 / 2048.0,
                    "{name}: |r {end}/512 - 1| = {:e}",
                    z.to_f64()
                );
            }
        }
        let ln2 = Float::with_val(PREC, Constant::Log2);
        // `LN2H` is ln 2 with its significand cut to 42 bits, and `LG2[0]` log10(2).
        let lnh = Float::with_val_round(42, &ln2, Round::Zero).0.to_f64();
        assert_eq!(
            LN2H,
            lnh.to_bits(),
            "LN2H: {:e} != {lnh:e}",
            f64::from_bits(LN2H)
        );
        check_low("LN2L", &ln2, lnh, f64::from_bits(LN2L), -100);
        let lg2 = Float::with_val(PREC, 2).log10();
        let lgh = Float::with_val_round(42, &lg2, Round::Zero).0.to_f64();
        assert_eq!(
            LG2[0],
            lgh.to_bits(),
            "LG2[0]: {:e}",
            f64::from_bits(LG2[0])
        );
        check_low("LG2[1]", &lg2, lgh, f64::from_bits(LG2[1]), -100);
        assert_eq!(ONE, [1.0f64.to_bits(), 0], "ONE");
        check_pair("C2", C2, &Float::with_val(PREC, ln2.recip_ref()), -104);
        let ln10 = Float::with_val(PREC, 10).ln();
        check_pair("C10", C10, &Float::with_val(PREC, ln10.recip_ref()), -104);
        for (name, q, k) in [("Q3", Q3, 3), ("Q5", Q5, 5), ("Q6", Q6, -6), ("Q7", Q7, 7)] {
            let want = Float::with_val(PREC, k).recip().to_f64();
            assert_eq!(
                q,
                want.to_bits(),
                "{name}: {:e} != {want:e}",
                f64::from_bits(q)
            );
        }
        assert_eq!(TWO52, pow2(52), "TWO52");
        assert_eq!(FRAC, (1 << 52) - 1, "FRAC");
    }

    // `ln_core(x)` meets the bounds of `ln_core_correct` in `rocq/theories/FastLogCore.v`:
    // a_h = RN(a_h + a_l), e in [-1074, 1024], and |ln m| <= 7/20 and
    // |ln m - (a_h + a_l)| <= 3 2^-71 |ln m| for m = 2^-e x. And the fast paths of ln, log2 and
    // log10 (`fast_parts`) give (h, l, k) with h = RN(h + l), 1 <= |h| < 2, k in [-1021, 1022]
    // and |y 2^-k - (h + l)| <= 2^-69 |h| for y = ln x, log2 x and log10 x, which is what the
    // design of the fast path aims at, below the 2^-68 that the theorems of
    // `rocq/theories/FastLogLn.v` and `FastLogBy.v` state. The arguments are those of
    // `table_and_reduction_edges`, on fewer exponents, and random ones as in
    // `fast_range_random`, closer to 1 too.
    #[test]
    fn fast_ln_bound() {
        let mut rng = Rng(883);
        let mut args = vec![];
        for k in edge_exponents().into_iter().step_by(4) {
            for j in 0..512 {
                args.extend(around((1.0 + f64::from(j) / 512.0) * pow2(k), 1));
            }
        }
        args.extend(around(1.0, 64));
        args.extend((1..=64).map(f64::from_bits));
        args.push(f64::MAX);
        for _ in 0..2000 {
            args.push(any_positive(&mut rng));
            args.push(near_one(&mut rng, -53, -9));
        }
        for x in args {
            let (e, ah, al) = ln_core(x);
            // m = 2^-e x is exact in 300 bits.
            let mut lm = Float::with_val(PREC, x) >> i32::try_from(e).unwrap();
            lm.ln_mut();
            let mut d = Float::with_val(PREC, &lm - ah);
            d -= al;
            d.abs_mut();
            assert!(
                ah + al == ah
                    && (-1074..=1024).contains(&e)
                    && lm.clone().abs() <= 0.35
                    && d <= lm.clone().abs() * 3 * pow2(-71),
                "ln_core({x:e}): ({e}, {ah:e}, {al:e}), with |ln m - (a_h + a_l)| = {:e} and \
                 ln m = {:e}",
                d.to_f64(),
                lm.to_f64()
            );
            for i in [LN, LOG2, LOG10] {
                let Some((h, l, k)) = fast_parts(i, x) else {
                    assert_eq!(x, 1.0, "{}({x:e}): no fast path", FUNCTIONS[i].0);
                    continue;
                };
                let mut y = Float::with_val(PREC, x);
                match i {
                    LN => y.ln_mut(),
                    LOG2 => y.log2_mut(),
                    _ => y.log10_mut(),
                }
                let mut d = y >> i32::try_from(k).unwrap();
                d -= h;
                d -= l;
                d.abs_mut();
                assert!(
                    h + l == h
                        && 1.0 <= h.abs()
                        && h.abs() < 2.0
                        && (-1021..=1022).contains(&k)
                        && d <= pow2(-69) * h.abs(),
                    "{}({x:e}): ({h:e}, {l:e}, {k}), with |y 2^-k - (h + l)| = {:e}",
                    FUNCTIONS[i].0,
                    d.to_f64()
                );
            }
        }
    }
}

mod levels;
mod mpfr_cases;
