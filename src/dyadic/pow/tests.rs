// Tests of the powers of the dyadic kernel. Every generator runs on every platform through
// `check_pow` and `check_pown`, which check that the two directions give the same `f64` or two
// adjacent ones, or NaN for both, and that `pow_near` and `pown_near`, which round to nearest,
// give one of them, or NaN. On 64-bit Linux and macOS, where the tests have MPFR, they
// also compare both directions with `pow_rd`, `pow_ru`, `pown_rd` and `pown_ru` of
// `src/mpfr_calls/mpfr.rs`, and nearest with its `pow_rn` and `pown_rn`, which compute them
// with MPFR and which they have to agree with bit for bit, `pow` except at x < 0.

use super::*;
use crate::dyadic::tests::Rng;
use crate::simd::HAS_FMA;

// The `f64` after `x` toward +∞, for `x` below +∞. `f64::next_up` came with Rust 1.86, after
// the MSRV of the time, 1.65.
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
fn pow2(n: i64) -> f64 {
    if n < -1022 {
        f64::from_bits(1 << (n + 1074))
    } else {
        f64::from_bits(u64::try_from(n + 1023).unwrap() << 52)
    }
}

// `x` and the `k` `f64`s on each side of it, for a finite `x`.
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

// The number that `s` stands for: after `0b`, a binary number as `mpfr_set_str_binary` reads
// it, with a sign, binary digits with a point, and an exponent of 2 after `E` or `e`, which
// has to be an `f64`; otherwise a decimal number, which `str::parse` rounds to nearest.
fn num(s: &str) -> f64 {
    let (sign, t) = match s.strip_prefix('-') {
        Some(t) => (-1.0, t),
        None => (1.0, s),
    };
    let t = match t.strip_prefix("0b") {
        Some(t) => t,
        None => return s.parse().unwrap(),
    };
    let (digits, mut e) = match t.find(['e', 'E']) {
        Some(i) => (&t[..i], t[i + 1..].parse::<i64>().unwrap()),
        None => (t, 0),
    };
    let (mut m, mut point) = (0u64, false);
    for c in digits.chars() {
        if c == '.' {
            point = true;
        } else {
            m = 2 * m + u64::from(c.to_digit(2).unwrap());
            e -= i64::from(point);
        }
    }
    // m has at most 53 bits and m 2^e is in range, so that the product is exact.
    assert!(m < 1 << 53 && m != 0, "{}", s);
    let top = e + 63 - i64::from(m.leading_zeros());
    let shift = e.max(-1074).min(1023 - (top - e));
    let v = m as f64 * pow2(shift) * pow2(e - shift);
    assert!(e >= -1074 && top <= 1023, "{}", s);
    sign * v
}

// `lo` and `hi`, the roundings of a result toward -∞ and toward +∞, give `want` in the
// rounding `rnd` of a test of MPFR or pxfm: `E` exact (both are `want`), `W` (`lo` is `want`
// and `hi` the next `f64`, as `check_worst_case` of MPFR's tests), `D`, `U`, `Z` (toward zero)
// or `N` (to nearest, so one of the two). Signed zeros have to agree.
fn check_rounding(what: &str, lo: f64, hi: f64, rnd: &str, want: f64) {
    let same = |a: f64, b: f64| a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan());
    let ok = match rnd {
        "E" => same(lo, want) && same(hi, want),
        "W" => same(lo, want) && same(hi, next_up(want)),
        "D" => same(lo, want),
        "U" => same(hi, want),
        "Z" => same(if want > 0.0 { lo } else { hi }, want),
        "N" => same(lo, want) || same(hi, want),
        _ => panic!("{}: no rounding {}", what, rnd),
    };
    assert!(
        ok,
        "{}: ({:e}, {:e}), {} {:e} expected",
        what, lo, hi, rnd, want
    );
}

// `lo` and `hi` are equal or adjacent, or both NaN.
fn check_pair(what: &str, lo: f64, hi: f64) {
    if lo.is_nan() || hi.is_nan() {
        assert!(lo.is_nan() && hi.is_nan(), "{}: {:e} {:e}", what, lo, hi);
    } else {
        assert!(
            lo.to_bits() == hi.to_bits() || next_up(lo).to_bits() == hi.to_bits(),
            "{}: {:e} and {:e} are neither equal nor adjacent",
            what,
            lo,
            hi
        );
    }
}

// `near`, the rounding to nearest of the number that `lo` and `hi` round, is one of them, or NaN
// if they are. This holds for zeros too: a number of magnitude at most 2^-1075 rounds to
// nearest to the zero of its sign, which the direction toward 0 also gives.
fn check_near(what: &str, lo: f64, hi: f64, near: f64) {
    let ok = if lo.is_nan() {
        near.is_nan()
    } else {
        near.to_bits() == lo.to_bits() || near.to_bits() == hi.to_bits()
    };
    assert!(
        ok,
        "{}: {:e} to nearest, outside ({:e}, {:e})",
        what, near, lo, hi
    );
}

// Checks x^y in both directions and to nearest, as the header says.
fn check_pow(x: f64, y: f64) {
    let (lo, hi) = (pow(x, y, false), pow(x, y, true));
    check_pow_results(x, y, lo, hi, pow_near(x, y));
}

// Checks `lo`, `hi` and `near`, which `pow` and `pow_near` gave at (x, y), as `check_pow`.
fn check_pow_results(x: f64, y: f64, lo: f64, hi: f64, near: f64) {
    let what = format!("pow({:e}, {:e})", x, y);
    check_pair(&what, lo, hi);
    check_near(&what, lo, hi, near);
    #[cfg(all(
        target_pointer_width = "64",
        any(target_os = "linux", target_os = "macos")
    ))]
    mpfr::check_pow(x, y, lo, hi, near);
}

// Checks x^n in both directions and to nearest, as the header says.
fn check_pown(x: f64, n: i32) {
    let (lo, hi) = (pown(x, n, false), pown(x, n, true));
    check_pown_results(x, n, lo, hi, pown_near(x, n));
}

// Checks `lo`, `hi` and `near`, which `pown` and `pown_near` gave at (x, n), as `check_pown`.
fn check_pown_results(x: f64, n: i32, lo: f64, hi: f64, near: f64) {
    let what = format!("pown({:e}, {})", x, n);
    check_pair(&what, lo, hi);
    check_near(&what, lo, hi, near);
    #[cfg(all(
        target_pointer_width = "64",
        any(target_os = "linux", target_os = "macos")
    ))]
    mpfr::check_pown(x, n, lo, hi, near);
}

// Arguments on which mismatches were found, as `("pow", x, y)` or `("pown", x, n)`, each with
// what it broke and where it was found.
fn regressions() -> Vec<(&'static str, &'static str, &'static str)> {
    vec![]
}

#[test]
fn regressions_hold() {
    for (name, x, y) in regressions() {
        if name == "pow" {
            check_pow(x.parse().unwrap(), y.parse().unwrap());
        } else {
            check_pown(x.parse().unwrap(), y.parse().unwrap());
        }
    }
}

// The special values, and some exact cases.
#[test]
fn special_and_exact() {
    let special = [
        0.0,
        -0.0,
        f64::from_bits(1),
        0.5,
        1.0,
        2.0,
        4.0,
        9.0,
        f64::MAX,
        f64::INFINITY,
        f64::NAN,
    ];
    let ys = [
        0.0, -0.0, 0.5, -0.5, 1.0, -1.0, 1.5, 2.0, 3.0, -3.0, 1e300, -1e300,
    ];
    for &x in &special {
        for &y in ys.iter().chain(&special) {
            check_pow(x, y);
            check_pow(x, -y);
        }
        for n in [0, 1, -1, 2, -2, 3, -3, 1024, -1075, i32::MAX, i32::MIN] {
            check_pown(x, n);
            check_pown(-x, n);
        }
    }
    assert_eq!(pow(4.0, 1.5, false), 8.0);
    assert_eq!(pow(9.0, 0.5, true), 3.0);
}

// The powers at the strings `x` and `y`, which `num` reads, each as (call, rounding toward -∞,
// rounding toward +∞), after `check_pow` or `check_pown` of it: x^y but for x < 0, where `pow`
// gives NaN, and x^n for n = y if y is an `i32`, where x^y and x^n are the same.
fn powers(x: &str, y: &str) -> Vec<(String, f64, f64)> {
    let (x, y) = (num(x), num(y));
    let mut v = vec![];
    if x.is_nan() || x >= 0.0 {
        check_pow(x, y);
        let what = format!("pow({:e}, {:e})", x, y);
        v.push((what, pow(x, y, false), pow(x, y, true)));
    }
    let n = y as i32;
    if f64::from(n) == y {
        check_pown(x, n);
        let what = format!("pown({:e}, {})", x, n);
        v.push((what, pown(x, n, false), pown(x, n, true)));
    }
    assert!(!v.is_empty(), "no power at ({:e}, {:e})", x, y);
    v
}

// Fixed cases of the tests of MPFR 4.2.2 (`tests/tpow.c`, by function) and of pxfm 0.1.30
// (`src/pow.rs`), as (x, y, rounding, result) for `powers` and `check_rounding`, with x, y and
// the result as `num` reads them. Where MPFR's test is at another exponent range or of a C
// type, the case is at the `f64` and `i32` ones, with `i32::MAX` and `i32::MIN` for the ends
// of `long` and `unsigned long`.
const RESULTS: [(&str, &str, &str, &str); 73] = [
    // `special`: those at 53 bits, (-0)^(17 + 2^-48) for (-0)^(the number after 17), and
    // (+∞)^1024.
    ("2", "-2", "E", "0.25"),
    (
        "5.68824667828621954868e-01",
        "9.03327850535952658895e-01",
        "Z",
        "0.60071044650456473235",
    ),
    ("-0", "17.000000000000004", "E", "0"),
    ("inf", "0b1E10", "E", "inf"),
    // `overflows`, `overflows2` and `bug20110320`, which overflow or are exact at `f64`.
    ("5.1e32", "5.1e32", "W", "1.7976931348623157e308"),
    ("0b1E-64", "-0.5", "E", "4294967296"),
    ("0b1E215", "1024", "W", "1.7976931348623157e308"),
    // `tst20140422`.
    ("1296", "0.75", "E", "216"),
    // `check_pow_ui`: 1^(2^32 - 1), (-∞)^n for odd and even n, the underflows and overflows,
    // the zeros, and the three worst cases, of 2006-11-25 and 2006-11-26.
    ("1", "2147483647", "E", "1"),
    ("-inf", "2147483647", "E", "-inf"),
    ("-inf", "30002752", "E", "inf"),
    ("0.5", "2147483647", "W", "0"),
    ("0b1E-10", "2147483647", "W", "0"),
    ("0b1E10", "2147483647", "W", "1.7976931348623157e308"),
    ("-0b1E10", "2147483647", "W", "-inf"),
    ("0", "1", "E", "0"),
    ("-0", "5", "E", "-0"),
    ("-0", "6", "E", "0"),
    (
        "0b1.0000010110000100001000101101101001011101101011010111",
        "35",
        "N",
        "0b1.0000110111101111011010110100001100010000001010110100E1",
    ),
    (
        "0b1.0110100111010001101001010111001110010100111111000011",
        "36",
        "D",
        "0b1.1111010011101110001111010110000101110000110110101100E17",
    ),
    (
        "0b1.1001010100001110000110111111100011011101110011000100",
        "36",
        "U",
        "0b1.1100011101101101100010110001000001110001111110010001E23",
    ),
    // `check_pow_si`.
    ("NaN", "-1", "E", "NaN"),
    ("inf", "-1", "E", "0"),
    ("-inf", "-1", "E", "-0"),
    ("-inf", "-2", "E", "0"),
    ("0", "-1", "E", "inf"),
    ("-0", "-1", "E", "-inf"),
    ("-0", "-2", "E", "inf"),
    ("2", "2147483647", "W", "1.7976931348623157e308"),
    ("2", "-2147483648", "W", "0"),
    ("2", "-2147483647", "W", "0"),
    ("0.5", "-2147483648", "W", "1.7976931348623157e308"),
    // `check_pown_ieee754_2019`.
    ("NaN", "0", "E", "1"),
    ("inf", "0", "E", "1"),
    ("-inf", "0", "E", "1"),
    ("0", "0", "E", "1"),
    ("-0", "0", "E", "1"),
    ("17", "0", "E", "1"),
    ("-17", "0", "E", "1"),
    ("0", "-17", "E", "inf"),
    ("-0", "-17", "E", "-inf"),
    ("0", "-42", "E", "inf"),
    ("-0", "-42", "E", "inf"),
    ("0", "42", "E", "0"),
    ("-0", "42", "E", "0"),
    ("0", "17", "E", "0"),
    ("-0", "17", "E", "-0"),
    ("inf", "17", "E", "inf"),
    ("-inf", "17", "E", "-inf"),
    ("-inf", "42", "E", "inf"),
    ("inf", "-17", "E", "0"),
    ("inf", "-42", "E", "0"),
    ("-inf", "-17", "E", "-0"),
    ("-inf", "-42", "E", "0"),
    // `check_special_pow_si` and `pow_si_long_min`.
    ("-2", "-10000", "W", "0"),
    ("1.5", "-2147483648", "W", "0"),
    // pxfm's `f_pow_test` and `powi_test`, which round to nearest, and whose 2^3 and 0.5^2
    // are exact.
    (
        "1.35264499699371e-309",
        "-0.5",
        "N",
        "2.7189929701044785e154",
    ),
    (
        "2.1798599361155193e-53",
        "-2",
        "N",
        "2.1044703967713977e105",
    ),
    ("-2.519228172390062e307", "-2", "W", "0"),
    (
        "2.1799650661798696e-53",
        "-2",
        "N",
        "2.1042674230844515e105",
    ),
    ("1.4916691520383755e-154", "-2", "N", "4.49422677644136e307"),
    ("1", "inf", "E", "1"),
    ("2", "inf", "E", "inf"),
    ("inf", "-0.5", "E", "0"),
    ("2", "3", "E", "8"),
    ("0.5", "2", "E", "0.25"),
    ("2.1", "2.7", "N", "7.412967494768546"),
    ("27", "0.3333333333333333", "N", "3"),
    ("0b1E-51", "102", "W", "0"),
    ("3", "3", "E", "27"),
    ("3", "-3", "N", "0.037037037037037035"),
    ("3", "102", "N", "4.638397686588102e48"),
    (
        "1.1074474670636028e-14",
        "-22",
        "N",
        "1.0589880229528372e307",
    ),
];

// The other arguments of the same tests, as (x, y) for `powers`, at which they give no 53-bit
// result as a number.
const ARGUMENTS: [(&str, &str); 8] = [
    // `special`, at other precisions.
    (
        "0.5",
        "0b0.11010110011100101010110011001010100111000001000101110E-1",
    ),
    (
        "0b0.111011000111100000111010000101010100110011010000011",
        "0b0.111110010100110000011101100011010111000010000100101",
    ),
    ("0b1.00000000001010111110001111011e1", "-0.5"),
    ("0b1.11111100100001100101", "-0.5"),
    // `underflows`, whose result underflows here too.
    (
        "0b0.110011010011101001110001110100010000110111101",
        "0b0.101110010011111001011010100011011100111110011E40",
    ),
    // `x_near_one`: (1 - 2^-32)^(11/4).
    ("0b0.11111111111111111111111111111111", "2.75"),
    // `check_pow_ui`.
    ("0.6926773", "10"),
    ("0b1.0000000000000000000000001111", "2055225053"),
];

#[test]
fn fixed_cases() {
    for (x, y, rnd, want) in RESULTS {
        for (what, lo, hi) in powers(x, y) {
            check_rounding(&what, lo, hi, rnd, num(want));
        }
    }
    for (x, y) in ARGUMENTS {
        powers(x, y);
    }
    // `coverage` of tpow.c: (0.75)^99.5, (0.75)^100.5 and (0.75)^101.5, with the neighbours of
    // x and y, and (-2)^(2^i + 1) for each i from 8 at which 2^i + 1 is an `i32`.
    for y in [99.5, 100.5, 101.5] {
        for &x in &around(0.75, 1) {
            for &y in &around(y, 1) {
                check_pow(x, y);
            }
        }
    }
    for i in 8..=30 {
        let n = (1 << i) + 1;
        let (lo, hi) = (pown(-2.0, n, false), pown(-2.0, n, true));
        let what = format!("pown(-2, {})", n);
        if n <= 1023 {
            check_rounding(&what, lo, hi, "E", -pow2(n.into()));
        } else {
            check_rounding(&what, lo, hi, "W", f64::NEG_INFINITY);
        }
        check_pown(-2.0, n);
    }
}

// x^y at a special value, as MPFR gives it and as `pow_c` of `rocq/theories/Contract.v` takes
// it where that states one: 1 at y = ±0 and at x = 1, then NaN at a NaN, the zeros and the
// infinities at x = ±0, at x = +∞ and at y = ±∞, and NaN at x < 0, which is `pow`'s own
// choice (see its header). `None` at a finite x > 0 other than 1 and a finite y != 0.
fn special_pow(x: f64, y: f64) -> Option<f64> {
    let inf = f64::INFINITY;
    let v = if y == 0.0 || x == 1.0 {
        1.0
    } else if x.is_nan() || y.is_nan() || x < 0.0 {
        f64::NAN
    } else if x == 0.0 {
        // +∞ for y < 0 and +0 for y > 0, negated for x = -0 and an odd integer y.
        let r = if y < 0.0 { inf } else { 0.0 };
        if x.is_sign_negative() && (y % 2.0).abs() == 1.0 {
            -r
        } else {
            r
        }
    } else if x == inf {
        if y > 0.0 {
            inf
        } else {
            0.0
        }
    } else if y.is_infinite() {
        if (x > 1.0) == (y > 0.0) {
            inf
        } else {
            0.0
        }
    } else {
        return None;
    };
    Some(v)
}

// x^n at a special value, as MPFR gives it and as `pown_c` takes it where that states one: 1
// at n = 0, then NaN at x = NaN, and the zeros and the infinities at x = ±0 and x = ±∞. `None`
// at a finite x != 0 and n != 0.
fn special_pown(x: f64, n: i32) -> Option<f64> {
    let v = if n == 0 {
        1.0
    } else if x.is_nan() {
        f64::NAN
    } else if x == 0.0 || x.is_infinite() {
        // +∞ at a zero for n < 0 and at an infinity for n > 0, and +0 otherwise, negated for
        // x = -0 or x = -∞ and an odd n.
        let r = if (x == 0.0) == (n < 0) {
            f64::INFINITY
        } else {
            0.0
        };
        if x.is_sign_negative() && n % 2 != 0 {
            -r
        } else {
            r
        }
    } else {
        return None;
    };
    Some(v)
}

// `special_pow` and `special_pown` in both directions, signs of zeros included, and
// `check_pow` and `check_pown`, over a grid of special and ordinary arguments.
#[test]
fn special_values() {
    let (inf, max, tiny) = (f64::INFINITY, f64::MAX, f64::from_bits(1));
    let mut xs = vec![f64::NAN, 3.0, 0.75];
    for x in [inf, 0.0, 1.0, 2.0, 0.5, max, f64::MIN_POSITIVE, tiny] {
        xs.extend([x, -x]);
    }
    let mut ys = vec![f64::NAN, next_up(17.0)];
    for y in [
        inf,
        0.0,
        0.5,
        1.0,
        1.5,
        2.0,
        3.0,
        17.0,
        42.0,
        pow2(53),
        pow2(1023),
        max,
        tiny,
    ] {
        ys.extend([y, -y]);
    }
    let mut ns = vec![0, i32::MAX, i32::MIN, i32::MIN + 1];
    for n in [1, 2, 3, 17, 42, 1024, 1075] {
        ns.extend([n, -n]);
    }
    for &x in &xs {
        for &y in &ys {
            check_pow(x, y);
            if let Some(v) = special_pow(x, y) {
                let (lo, hi) = (pow(x, y, false), pow(x, y, true));
                check_rounding(&format!("pow({:e}, {:e})", x, y), lo, hi, "E", v);
            }
        }
        for &n in &ns {
            check_pown(x, n);
            if let Some(v) = special_pown(x, n) {
                let (lo, hi) = (pown(x, n, false), pown(x, n, true));
                check_rounding(&format!("pown({:e}, {})", x, n), lo, hi, "E", v);
            }
        }
    }
}

// Random finite arguments: x log-uniform over (0, MAX], y in [-40, 40], and n in [-40, 40].
#[test]
fn random() {
    let mut rng = Rng(78);
    for _ in 0..2000 {
        let x = f64::from_bits(rng.below(0x7fef_ffff_ffff_ffff) + 1);
        let y = (rng.below(1 << 53) as f64 / (1u64 << 53) as f64 - 0.5) * 80.0;
        check_pow(x, y);
        let n = rng.below(81) as i32 - 40;
        check_pown(x, n);
        check_pown(-x, n);
    }
}

// Random finite arguments with a wide y or n, and x log-uniform over (0, MAX] as in `random`:
// - y with a random sign and bits uniform from +0 to MAX, so that its exponent field is uniform:
//   y is log-uniform over [2^-1022, MAX], and +0 and the subnormals take one binade's share. About
//   half of these x^y overflow or underflow, and most of the others have |y ln x| < 2^-54;
// - y = ±m 2^e with m uniform in [1, 2) (52 random bits) and e uniform in [-60, 12];
// - n uniform over all of `i32`, at x and -x, where nearly all x^n overflow or underflow.
#[test]
fn random_wide() {
    let mut rng = Rng(7801);
    let x = |rng: &mut Rng| f64::from_bits(rng.below(0x7fef_ffff_ffff_ffff) + 1);
    let sign = |rng: &mut Rng| if rng.below(2) == 0 { -1.0 } else { 1.0 };
    for _ in 0..100_000 {
        let x = x(&mut rng);
        let y = sign(&mut rng) * f64::from_bits(rng.below(0x7ff0_0000_0000_0000));
        check_pow(x, y);
    }
    for _ in 0..20_000 {
        let x = x(&mut rng);
        let m = 1.0 + rng.below(1 << 52) as f64 / (1u64 << 52) as f64;
        let y = sign(&mut rng) * m * pow2(rng.below(73) as i64 - 60);
        check_pow(x, y);
    }
    for _ in 0..100_000 {
        let x = x(&mut rng);
        let n = rng.next() as i32;
        check_pown(x, n);
        check_pown(-x, n);
    }
}

// A random `f64` uniform in [0, 1).
fn unit(rng: &mut Rng) -> f64 {
    rng.below(1 << 53) as f64 / (1u64 << 53) as f64
}

// -1 or 1, at random.
fn sign(rng: &mut Rng) -> f64 {
    if rng.below(2) == 0 {
        -1.0
    } else {
        1.0
    }
}

// m 2^e for m uniform in [1, 2) (52 random bits) and e uniform in [lo, hi], rounded to a
// subnormal below e = -1022.
fn log_uniform(rng: &mut Rng, lo: i64, hi: i64) -> f64 {
    let e = lo + rng.below(u64::try_from(hi - lo + 1).unwrap()) as i64;
    (1.0 + rng.below(1 << 52) as f64 / (1u64 << 52) as f64) * pow2(e)
}

// x within 2^-20 of 1 and not 1: 1 + k 2^-52 or 1 - k 2^-53 for k log-uniform in [1, 2^32).
fn near_one(rng: &mut Rng) -> f64 {
    let j = rng.below(32);
    let k = ((1u64 << j) + rng.below(1 << j)) as f64;
    if rng.below(2) == 0 {
        1.0 + k * pow2(-52)
    } else {
        1.0 - k * pow2(-53)
    }
}

// ±2^u for u uniform in ±1000 / |n| (±1000 at n = 0), so that x^n is in [2^-1000, 2^1000].
fn pown_x(rng: &mut Rng, n: i32) -> f64 {
    let u = (2.0 * unit(rng) - 1.0) * 1000.0 / f64::from(n).abs().max(1.0);
    sign(rng) * u.exp2()
}

// n with |n| uniform in [2^(b - 1), 2^b) for b uniform in [1, 31], and a random sign.
fn wide_n(rng: &mut Rng) -> i32 {
    let b = 1 + rng.below(31);
    let a = (1i64 << (b - 1)) + rng.below(1 << (b - 1)) as i64;
    i32::try_from(if rng.below(2) == 0 { -a } else { a }).unwrap()
}

// (x, y) at which x^y is an `f64`, as the `exact` set of the counts of `pow` (row 78) draws them:
// for an even i, x = 2^e and y = j / 2^k, where x^y = 2^(j e / 2^k), and for an odd i,
// x = r^(2^k) 2^(2^k f) and y = m / 2^k for an odd r, where x^y = r^m 2^(m f).
fn exact_pair(rng: &mut Rng, i: usize) -> (f64, f64) {
    if i % 2 == 0 {
        // k <= min(tz(e), 10), q = e / 2^k, j q in [-1074, 1023], and j odd if k > 0.
        let e = loop {
            let e = -1074 + rng.below(2098) as i64;
            if e != 0 {
                break e;
            }
        };
        let k = rng.below(u64::from(e.trailing_zeros().min(10)) + 1) as i64;
        let q = e >> k;
        let (jlo, jhi) = if q > 0 {
            (-(1074 / q), 1023 / q)
        } else {
            (-(1023 / -q), 1074 / -q)
        };
        let j = loop {
            let j = jlo + rng.below(u64::try_from(jhi - jlo + 1).unwrap()) as i64;
            if j != 0 && (k == 0 || j % 2 != 0) {
                break j;
            }
        };
        (pow2(e), j as f64 / (1u64 << k) as f64)
    } else {
        // r^(2^k) < 2^53 for r <= RMAX[k], r^m < 2^53 with m <= 33, m odd if k > 0, and f in
        // [-20, 20].
        const RMAX: [u64; 6] = [(1 << 53) - 1, 94_906_265, 9741, 97, 9, 3];
        let k = rng.below(6) as usize;
        let bits = 64 - RMAX[k].leading_zeros();
        let r = loop {
            let b = 2 + rng.below(u64::from(bits - 1)) as u32;
            let r = (1u64 << (b - 1)) + rng.below(1 << (b - 1));
            if r % 2 == 1 && r <= RMAX[k] {
                break r;
            }
        };
        let (mut mmax, mut p) = (0u64, 1u128);
        while mmax < 33 && p * u128::from(r) < 1 << 53 {
            p *= u128::from(r);
            mmax += 1;
        }
        let m = loop {
            let m = 1 + rng.below(mmax);
            if k == 0 || m % 2 == 1 {
                break m;
            }
        };
        let f = -20 + rng.below(41) as i64;
        let x = r.pow(1 << k) as f64 * pow2(f << k);
        (x, m as f64 / (1u64 << k) as f64)
    }
}

// (x, y) moved by one ulp of x or of y, at random.
fn moved(rng: &mut Rng, (x, y): (f64, f64)) -> (f64, f64) {
    match rng.below(4) {
        0 => (next_up(x), y),
        1 => (next_down(x), y),
        2 => (x, next_up(y)),
        _ => (x, next_down(y)),
    }
}

// The names of the sets of `pow_case` and of `pown_case`, as `fast_path_agrees_with_kernel` and
// `copies_agree` draw them.
const POW_SETS: [&str; 9] = [
    "lu4", "near1", "mid", "int", "intlu", "t745", "edge", "exact", "nexact",
];
const POWN_SETS: [&str; 9] = [
    "pn2", "pnm2", "pn3", "pn17", "pnint", "pnlu", "pnany", "pnexact", "pnnexact",
];

// The i-th argument (x, y) of `pow` in the set `name` of `fast_path_agrees_with_kernel`, as the
// counts of `pow` (rows 78, 84 and 89) draw them:
// - `lu4`: x log-uniform over the positive `f64`s, subnormals included, and y uniform in [-4, 4);
// - `near1`: x within 2^-20 of 1, and y = t / ln x for |t| log-uniform in [2^-10, 745];
// - `mid`: x log-uniform in [2^-64, 2^64), and |y| log-uniform in [2^-8, 2^13);
// - `int`: x log-uniform in [2^-30, 2^31), and an integer y with |y| in [1, 40];
// - `intlu`: an integer y = n with |n| log-uniform over `i32`, and x^n in [2^-1000, 2^1000];
// - `t745`: x as in `lu4`, and y = t / ln x for |t| uniform in [100, 745];
// - `edge`: x as in `lu4`, and y = t / ln x for t uniform in [700, 745.2] or [-746, -700], next to
//   the ends of the range of `fast_exp` and to overflow and underflow;
// - `exact`: x^y is an `f64` (`exact_pair`), which the test to nearest of the fast path settles,
//   and which `exact` settles in both directions, before the fast path at a normal x;
// - `nexact`: those moved by one ulp of x or of y.
fn pow_case(name: &str, rng: &mut Rng, i: usize) -> (f64, f64) {
    let any = |rng: &mut Rng| log_uniform(rng, -1074, 1023);
    match name {
        "lu4" => (any(rng), 8.0 * unit(rng) - 4.0),
        "near1" => {
            let x = near_one(rng);
            let t = sign(rng) * log_uniform(rng, -10, 9).min(745.0);
            (x, t / x.ln())
        }
        "mid" => (
            log_uniform(rng, -64, 63),
            sign(rng) * log_uniform(rng, -8, 12),
        ),
        "int" => (
            log_uniform(rng, -30, 30),
            sign(rng) * (1 + rng.below(40)) as f64,
        ),
        "intlu" => {
            let n = wide_n(rng);
            (pown_x(rng, n).abs(), f64::from(n))
        }
        "t745" => {
            let x = any(rng);
            (x, sign(rng) * (100.0 + 645.0 * unit(rng)) / x.ln())
        }
        "edge" => {
            let x = any(rng);
            let t = if rng.below(2) == 0 {
                700.0 + 45.2 * unit(rng)
            } else {
                -700.0 - 46.0 * unit(rng)
            };
            (x, t / x.ln())
        }
        "exact" => exact_pair(rng, i),
        "nexact" => {
            let p = exact_pair(rng, i);
            moved(rng, p)
        }
        _ => unreachable!(),
    }
}

// The i-th argument (x, n) of `pown` in the set `name` of `fast_path_agrees_with_kernel`:
// - `pn2`, `pnm2`, `pn3` and `pn17`: n = 2, -2, 3 and 17, and x = ±2^u with x^n in
//   [2^-1000, 2^1000] (`pown_x`);
// - `pnint`: ±x for x log-uniform in [2^-30, 2^31), and |n| in [1, 40];
// - `pnlu`: n with |n| log-uniform over `i32`, and x as in `pn2`;
// - `pnany`: n uniform over `i32`, and x as in `pn2`;
// - `pnexact`: ±r 2^f for an odd r, f in [-20, 20] and n in [1, 33] with r^n < 2^53, at which x^n
//   is an `f64`, and which reach the fast path, whose directed tests fail;
// - `pnnexact`: those with x moved by one ulp.
fn pown_case(name: &str, rng: &mut Rng) -> (f64, i32) {
    match name {
        "pn2" | "pnm2" | "pn3" | "pn17" => {
            let n = match name {
                "pn2" => 2,
                "pnm2" => -2,
                "pn3" => 3,
                _ => 17,
            };
            (pown_x(rng, n), n)
        }
        "pnint" => {
            let x = sign(rng) * log_uniform(rng, -30, 30);
            (x, (sign(rng) * (1 + rng.below(40)) as f64) as i32)
        }
        "pnlu" => {
            let n = wide_n(rng);
            (pown_x(rng, n), n)
        }
        "pnany" => {
            let n = rng.next() as i32;
            (pown_x(rng, n), n)
        }
        "pnexact" | "pnnexact" => {
            let bits = 1 + rng.below(26);
            let r = 2 * rng.below(1 << bits) + 1;
            let mut n = 1;
            while n < 33 && u128::from(r).pow(n + 1) < 1 << 53 {
                n += 1;
            }
            let n = 1 + rng.below(n.into()) as i32;
            let x = sign(rng) * r as f64 * pow2(rng.below(41) as i64 - 20);
            if name == "pnexact" {
                (x, n)
            } else if rng.below(2) == 0 {
                (next_up(x), n)
            } else {
                (next_down(x), n)
            }
        }
        _ => unreachable!(),
    }
}

// The calls of a set of arguments, and the rounding tests of the fast path that passed and failed
// in them. A call without a test is settled by a rule, by `exact`, or by the kernel where y ln x is
// outside the range of `fast_exp`; a failed test also leaves the call to the kernel.
#[derive(Default)]
struct Tally {
    calls: usize,
    passed: usize,
    failed: usize,
}

impl Tally {
    // Adds the three calls at one argument, with their tests as `agree_pow` gives them.
    fn add(&mut self, (passed, failed): (usize, usize)) {
        self.calls += 3;
        self.passed += passed;
        self.failed += failed;
    }

    fn print(&self, name: &str) {
        eprintln!(
            "fast path, {name}: {} calls, {} by the fast path, {} failed tests, {} without a test",
            self.calls,
            self.passed,
            self.failed,
            self.calls - self.passed - self.failed
        );
    }
}

// x^y in both directions and to nearest gives the same `f64`s with the fast path as with it
// disabled, and agrees with MPFR (`check_pow_results`). Returns the rounding tests of the fast path
// that passed and failed in the three calls.
fn agree_pow(x: f64, y: f64) -> (usize, usize) {
    crate::dyadic::fast::reset_fast_counts();
    let fast = (pow(x, y, false), pow(x, y, true), pow_near(x, y));
    let counts = crate::dyadic::fast::fast_counts();
    crate::dyadic::fast::set_fast_path(false);
    let kernel = (pow(x, y, false), pow(x, y, true), pow_near(x, y));
    crate::dyadic::fast::set_fast_path(true);
    assert!(
        fast.0.to_bits() == kernel.0.to_bits()
            && fast.1.to_bits() == kernel.1.to_bits()
            && fast.2.to_bits() == kernel.2.to_bits(),
        "pow({:e}, {:e}): {:?} with the fast path != {:?} without it",
        x,
        y,
        fast,
        kernel
    );
    check_pow_results(x, y, fast.0, fast.1, fast.2);
    counts
}

// `agree_pow` for x^n.
fn agree_pown(x: f64, n: i32) -> (usize, usize) {
    crate::dyadic::fast::reset_fast_counts();
    let fast = (pown(x, n, false), pown(x, n, true), pown_near(x, n));
    let counts = crate::dyadic::fast::fast_counts();
    crate::dyadic::fast::set_fast_path(false);
    let kernel = (pown(x, n, false), pown(x, n, true), pown_near(x, n));
    crate::dyadic::fast::set_fast_path(true);
    assert!(
        fast.0.to_bits() == kernel.0.to_bits()
            && fast.1.to_bits() == kernel.1.to_bits()
            && fast.2.to_bits() == kernel.2.to_bits(),
        "pown({:e}, {}): {:?} with the fast path != {:?} without it",
        x,
        n,
        fast,
        kernel
    );
    check_pown_results(x, n, fast.0, fast.1, fast.2);
    counts
}

// x^y and x^n give the same `f64`s, in both directions and to nearest, with the fast path as with
// it disabled, and agree with MPFR, on 2000 arguments of each set of `pow_case` and `pown_case`,
// and print how many calls the fast path settled. Most of its rounding tests pass on the sets in
// its range. On the set `exact`, the tests to nearest pass at every argument (next to 2^1024,
// where the set does not go, the fast path returns `None` without a test), and no x^y at a
// normal x reaches the directed tests, as `maybe_exact` sends it to `exact` first. At a
// subnormal x it can reach them, and they fail, as do the directed tests at the exact x^n, as
// they have to, so that `exact` and the kernel compute those.
#[test]
fn fast_path_agrees_with_kernel() {
    let mut rng = Rng(89);
    let mut total = Tally::default();
    for name in POW_SETS {
        let (mut t, mut normal) = (Tally::default(), Tally::default());
        for i in 0..2000 {
            let (x, y) = pow_case(name, &mut rng, i);
            let c = agree_pow(x, y);
            t.add(c);
            if x >= f64::MIN_POSITIVE {
                normal.add(c);
            }
        }
        t.print(&format!("pow {name}"));
        match name {
            "exact" => assert!(
                t.passed == 2000 && normal.failed == 0,
                "pow exact: {} passed, {} failed, {} at a normal x",
                t.passed,
                t.failed,
                normal.failed
            ),
            "nexact" => (),
            _ => assert!(
                t.passed > 100 * t.failed && t.passed > 0,
                "pow {name}: {} passed, {} failed",
                t.passed,
                t.failed
            ),
        }
        total.passed += t.passed;
        total.failed += t.failed;
    }
    for name in POWN_SETS {
        let mut t = Tally::default();
        for _ in 0..2000 {
            let (x, n) = pown_case(name, &mut rng);
            t.add(agree_pown(x, n));
        }
        t.print(&format!("pown {name}"));
        match name {
            // Both directed tests fail at each of the 2000 exact x^n.
            "pnexact" => assert!(
                t.failed >= 4000,
                "pown exact: {} passed, {} failed",
                t.passed,
                t.failed
            ),
            "pnnexact" => (),
            // n = 1 in about 1 case of 80 (pnint) or 62 (pnlu), and x^1 = x is exact, so both
            // directed tests fail there.
            "pnint" | "pnlu" => assert!(
                t.passed > 20 * t.failed && t.passed > 0,
                "pown {name}: {} passed, {} failed",
                t.passed,
                t.failed
            ),
            _ => assert!(
                t.passed > 100 * t.failed && t.passed > 0,
                "pown {name}: {} passed, {} failed",
                t.passed,
                t.failed
            ),
        }
        total.passed += t.passed;
        total.failed += t.failed;
    }
    assert!(total.passed > 0 && total.failed > 0);
}

// Whether (x, y) passes the rules of `pow` and `pow_near` before their fast path,
// `fast_pow_dir_call` and `fast_pow_near_call`: a finite x > 0 other than 1 and a finite y != 0
// at which s = `expo(y) + ln_expo(x)`, with 2^s <= |y ln x| < 2^(s + 4), is from -57 to 9. `pow`
// still tries `exact` first where `maybe_exact` says so.
fn calls_fast_pow(x: f64, y: f64) -> bool {
    x > 0.0
        && x != 1.0
        && x < f64::INFINITY
        && y != 0.0
        && y.is_finite()
        && (-57..=9).contains(&(expo(y) + ln_expo(x)))
}

// Whether `pown` and `pown_near` call `pown_pos` and `pown_pos_near` at (|x|, n): at a finite
// x != 0 and n != 0.
fn calls_pown_pos(x: f64, n: i32) -> bool {
    x != 0.0 && x.is_finite() && n != 0
}

// The fast path of x^y toward -∞, toward +∞ and to nearest, by the copy of each entry without an
// FMA in its products, by the copy with one (`level_entry!`), and by the entries
// `fast_pow_dir_call` and `fast_pow_near_call`, which call one of the two.
fn fast_pow_copies(x: f64, y: f64) -> [[Option<f64>; 3]; 3] {
    [
        [
            fast_pow_dir::<false>(x, y, false),
            fast_pow_dir::<false>(x, y, true),
            fast_pow_near::<false>(x, y),
        ],
        [
            fast_pow_dir::<true>(x, y, false),
            fast_pow_dir::<true>(x, y, true),
            fast_pow_near::<true>(x, y),
        ],
        [
            fast_pow_dir_call::<false>(x, y),
            fast_pow_dir_call::<true>(x, y),
            fast_pow_near_call(x, y),
        ],
    ]
}

// `fast_pow_copies` for x^n, for a finite x > 0 and n != 0, by `pown_pos_with`,
// `pown_pos_near_with` and the entries `pown_pos` and `pown_pos_near`, each as `Some`, the shape
// that `assert_copies_agree` takes.
fn pown_copies(x: f64, n: i32) -> [[Option<f64>; 3]; 3] {
    [
        [
            pown_pos_with::<false>(x, n, false),
            pown_pos_with::<false>(x, n, true),
            pown_pos_near_with::<false>(x, n),
        ],
        [
            pown_pos_with::<true>(x, n, false),
            pown_pos_with::<true>(x, n, true),
            pown_pos_near_with::<true>(x, n),
        ],
        [
            pown_pos(x, n, false),
            pown_pos(x, n, true),
            pown_pos_near(x, n),
        ],
    ]
    .map(|row| row.map(Some))
}

// Checks that the three rows of `copies` are the same, bit for bit: the same `f64`s, or `None`.
fn assert_copies_agree(what: &str, copies: [[Option<f64>; 3]; 3]) {
    let bits = copies.map(|row| row.map(|v| v.map(f64::to_bits)));
    assert!(
        bits[0] == bits[1] && bits[1] == bits[2],
        "{what}: {:?} without an FMA, {:?} with one, {:?} by the entries",
        copies[0],
        copies[1],
        copies[2]
    );
}

// The copies of the fast path of x^y and of `pown_pos` and `pown_pos_near` without an FMA and
// with one, and the entries, give the same `f64`s, or `None`, bit for bit, in both directions and
// to nearest, on 2000 arguments of each set of `pow_case` and `pown_case` (drawn as in
// `fast_path_agrees_with_kernel`, from another seed) and on `regressions()`, where they pass the
// rules before the fast path (`calls_fast_pow`) or before `pown_pos` and `pown_pos_near`, which
// take them at |x| (`calls_pown_pos`). `rocq/theories/FastPow.v` proves it of the fast path
// (`fast_pow_dir_fma` and `fast_pow_near_fma`), the only part of `pown_pos_with` and
// `pown_pos_near_with` that takes their `FMA`; this test checks the code as compiled, where the
// entries call the copy built with the target feature `fma` in a build with the dispatch, on a
// CPU that has it.
#[test]
fn copies_agree() {
    let mut rng = Rng(894);
    let mut checked = 0;
    for name in POW_SETS {
        for i in 0..2000 {
            let (x, y) = pow_case(name, &mut rng, i);
            if calls_fast_pow(x, y) {
                checked += 1;
                assert_copies_agree(&format!("pow({x:e}, {y:e})"), fast_pow_copies(x, y));
            }
        }
    }
    for name in POWN_SETS {
        for _ in 0..2000 {
            let (x, n) = pown_case(name, &mut rng);
            if calls_pown_pos(x, n) {
                checked += 1;
                let x = x.abs();
                assert_copies_agree(&format!("pown({x:e}, {n})"), pown_copies(x, n));
            }
        }
    }
    // Every argument of `pown_case`, and all but about 1 in 30 of those of `pow_case`, at which
    // `pow` and `pow_near` apply a rule instead.
    assert!(checked > 35_000, "{checked} arguments checked");
    for (name, x, y) in regressions() {
        let x: f64 = x.parse().unwrap();
        if name == "pow" {
            let y: f64 = y.parse().unwrap();
            if calls_fast_pow(x, y) {
                assert_copies_agree(&format!("pow({x:e}, {y:e})"), fast_pow_copies(x, y));
            }
        } else {
            let n: i32 = y.parse().unwrap();
            if calls_pown_pos(x, n) {
                let x = x.abs();
                assert_copies_agree(&format!("pown({x:e}, {n})"), pown_copies(x, n));
            }
        }
    }
}

// x^y and x^n next to the edges of the fast path, as `agree_pow` and `agree_pown` check them:
// - x next to (362 + i) / 512 2^k, the ends of the intervals of `LOG_TABLE` (and of the reduction
//   from M to M / 2 at i = 0 and 362), with 511/512 and 513/512, the ends of the two intervals
//   around 1 where r = 1, at k = 0, at subnormal, normal and the largest exponents;
// - x = 1 ± j ulp for j up to 64, with |y ln x| up to past 709, and y and n at the ends of `i32`;
// - subnormal x, at which ln x is from about -744 to -708, with y ln x from -707 to 709;
// - y ln x next to -707 and 709, the ends of the range of `fast_exp`, to -1022 ln 2 and
//   -1074 ln 2, the subnormal results, and to 1024 ln 2 and -1075 ln 2, overflow and underflow;
// - y and n at the ends of `i32`, and the integers just past them, with x^y in range.
#[test]
fn fast_path_edges() {
    let mut rng = Rng(891);
    let mut t = Tally::default();
    for k in [-1065, -1022, -1, 0, 1, 1023] {
        for i in 362..=724 {
            for x in around(f64::from(i) / 512.0 * pow2(k), 1) {
                for s in [-700.0, -0.75, pow2(-50), 1.5, 700.0] {
                    t.add(agree_pow(x, s / x.ln()));
                }
                t.add(agree_pow(x, 2.5));
                t.add(agree_pow(x, -0.3));
                if k == 0 || k == -1 {
                    for n in [2, 3, -3, 17] {
                        t.add(agree_pown(x, n));
                    }
                }
            }
        }
    }
    t.print("table edges");
    let mut t = Tally::default();
    let ends = [
        i32::MAX,
        i32::MAX - 1,
        i32::MIN,
        i32::MIN + 1,
        1 << 30,
        -(1 << 30),
    ];
    for j in 1..=64 {
        for x in [
            1.0 + f64::from(j) * pow2(-52),
            1.0 - f64::from(j) * pow2(-53),
        ] {
            for s in [0.5, 50.0, 700.0, 708.9, 709.5, 745.0] {
                t.add(agree_pow(x, s / x.ln()));
                t.add(agree_pow(x, -s / x.ln()));
            }
            for n in ends {
                t.add(agree_pow(x, f64::from(n)));
                t.add(agree_pown(x, n));
                t.add(agree_pown(-x, n));
            }
        }
    }
    t.print("1 ± j ulp");
    let mut t = Tally::default();
    let mut subnormals: Vec<f64> = (1..=64).map(f64::from_bits).collect();
    subnormals.extend((1..=16).map(|j| f64::from_bits((1 << 52) - j)));
    subnormals.extend((0..64).map(|_| f64::from_bits(1 + rng.below((1 << 52) - 1))));
    for &x in &subnormals {
        for s in [-707.0, -706.5, -300.0, -1e-3, 1e-3, 300.0, 708.5, 709.0] {
            t.add(agree_pow(x, s / x.ln()));
        }
        for y in [0.25, 0.95] {
            t.add(agree_pow(x, y));
            t.add(agree_pow(x, -y));
        }
        for n in [1, -1, 2, -2] {
            t.add(agree_pown(x, n));
        }
    }
    t.print("subnormal x");
    let mut t = Tally::default();
    let ln2 = std::f64::consts::LN_2;
    let ends = [
        -707.0,
        709.0,
        -1022.0 * ln2,
        -1074.0 * ln2,
        1024.0 * ln2,
        -1075.0 * ln2,
    ];
    for _ in 0..200 {
        let x = log_uniform(&mut rng, -1074, 1023);
        for s in ends {
            for y in around(s / x.ln(), 2) {
                t.add(agree_pow(x, y));
            }
        }
    }
    t.print("range ends");
    let mut t = Tally::default();
    let big = [
        2_147_483_648.0,
        -2_147_483_649.0,
        4_294_967_296.0,
        -4_294_967_296.0,
    ];
    for n in [i32::MAX, i32::MAX - 1, i32::MIN, i32::MIN + 1] {
        for _ in 0..100 {
            let x = pown_x(&mut rng, n);
            t.add(agree_pown(x, n));
            t.add(agree_pow(x.abs(), f64::from(n)));
        }
    }
    for y in big {
        for _ in 0..100 {
            t.add(agree_pow(pown_x(&mut rng, i32::MAX).abs(), y));
        }
    }
    t.print("i32 ends");
}

// The th = RN(y lh) of `pow_t` past the range of `fast_exp` at which the fast path of x^y changes
// arms or its result changes binade: `T_OVER`, from which a rule gives the overflow, and
// 1024 ln 2 = 709.78271..., above which x^y overflows; (1024 - 1/8192) ln 2, from which the
// exponent of `fast_exp_edge` is 1024, so that its tests fail; `T_UNDER` = -746, from which a
// rule gives the underflow; -1075 ln 2 = -745.133... and -1074 ln 2 = -744.440..., where x^y
// crosses 2^-1075 and 2^-1074; -1022 ln 2 = -708.396..., where it crosses 2^-1022; -707 and
// 709, the ends of the range of `fast_exp`; and -707 - 64 ln 2 = -751.36... and
// 709 + 4 ln 2 = 711.77..., the ends of that of `fast_exp_edge`, past the rules.
fn th_edges() -> [f64; 11] {
    let ln2 = std::f64::consts::LN_2;
    [
        T_OVER,
        1024.0 * ln2,
        (1024.0 - 1.0 / 8192.0) * ln2,
        T_UNDER,
        -1075.0 * ln2,
        -1074.0 * ln2,
        -1022.0 * ln2,
        -707.0,
        709.0,
        -707.0 - 64.0 * ln2,
        709.0 + 4.0 * ln2,
    ]
}

// x near 1, mid, large, small and subnormal x, at which y ln x reaches the th of `th_edges` at
// |y| from about 1 to about 2^62.
fn edge_xs() -> [f64; 18] {
    [
        1.0 + pow2(-52),
        1.0 - pow2(-53),
        1.0 + 3.0 * pow2(-40),
        1.0 - 5.0 * pow2(-30),
        1.0 + 1.37 * pow2(-21),
        0.7,
        1.5,
        3.3,
        10.1,
        1.3 * pow2(100),
        1.7 * pow2(1000),
        f64::MAX,
        0.9 * pow2(-100),
        1.1 * pow2(-1000),
        pow2(-1022),
        f64::from_bits(1),
        f64::from_bits(1 << 40),
        f64::from_bits((1 << 52) - 1),
    ]
}

// x^y and x^n at the th of `th_edges`, as `agree_pow` and `agree_pown` check them: y within 8
// `f64`s of t / ln x for each t and each x of `edge_xs`, at which th crosses each t that is an
// `f64` (`T_OVER`, `T_UNDER`, -707 and 709), and n within 2 of t / ln x where that is an `i32`.
// Most failed tests are next to -1075 ln 2, -1074 ln 2 and -1022 ln 2, where x^y is within the
// bound 2^-67 2^e of 2^-1075, a midpoint, or of the `f64`s 2^-1074 and 2^-1022, and at n = 1,
// where x^1 = x is exact.
#[test]
fn fast_path_wide_edges() {
    let mut t = Tally::default();
    for s in th_edges() {
        for x in edge_xs() {
            let ys = around(s / x.ln(), 8);
            if [T_OVER, T_UNDER, -707.0, 709.0].contains(&s) {
                let ths: Vec<f64> = ys.iter().map(|&y| pow_t::<HAS_FMA>(x, y).0).collect();
                assert!(
                    ths.iter().any(|&th| th < s) && ths.iter().any(|&th| th > s),
                    "x = {x:e}: th does not cross {s}"
                );
            }
            for y in ys {
                t.add(agree_pow(x, y));
            }
            // `as` saturates, so that an n out of the range of `i32` fails `try_from`.
            let n = (s / x.ln()).round() as i64;
            for m in n - 2..=n + 2 {
                if let Ok(m) = i32::try_from(m) {
                    t.add(agree_pown(x, m));
                }
            }
        }
    }
    t.print("wide edges");
}

// e^(th + tl) for the th and tl of `pow_t`, as (h, l, e) with x^y 2^-e within 2^-67 of h + l,
// or `None` where th is out of the range of `fast_exp`: the part of `fast_pow_dir` and
// `fast_pow_near` before their rounding tests in that range (`fast_pow_correct`).
fn fast_pow(x: f64, y: f64) -> Option<(f64, f64, i64)> {
    let (th, tl) = pow_t::<HAS_FMA>(x, y);
    fast_exp::<HAS_FMA>(th, tl)
}

// 2^-57, 2^10 times the bound 2^-67 of the fast path (`ERR67`).
const WIDE: f64 = 1024.0 * ERR67;

// x^y where a rounding test of the fast path passes, but would fail with `WIDE` in place of the
// bound 2^-67: h + l is within 2^-57 of h, which a directed rounding cannot cross, or of a
// midpoint between h and the next `f64`, which the rounding to nearest cannot cross. There an
// error in the bound would show first, so the fast path has to give the same `f64`s as the
// kernel, and as MPFR. The arguments are those of the sets `lu4`, `near1` and `mid`.
#[test]
fn widened() {
    let mut rng = Rng(892);
    let (mut dir, mut near) = (0, 0);
    for i in 0..6000 {
        let (x, y) = pow_case(["lu4", "near1", "mid"][i % 3], &mut rng, i);
        let Some((h, l, _)) = fast_pow(x, y) else {
            continue;
        };
        // 1/2 < h < 2: half the gap between h and the next `f64` above it is 2^-53 for h >= 1
        // and 2^-54 below, and the gap below it is the same but at h = 1, where it is 2^-54.
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
        let narrow_dir = ERR67 < l.abs() && l.abs() <= WIDE;
        let narrow_near = l < above - ERR67
            && l > -(below - ERR67)
            && (l >= above - WIDE || l <= -(below - WIDE));
        if !narrow_dir && !narrow_near {
            continue;
        }
        dir += usize::from(narrow_dir);
        near += usize::from(narrow_near);
        agree_pow(x, y);
    }
    assert!(
        dir >= 20 && near >= 20,
        "{dir} narrow passes of the directed tests and {near} of the test to nearest"
    );
}

#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
mod mpfr {
    use super::{fast_pow, pow2, pow_case, pown_case, Rng};
    use crate::mpfr_calls::mpfr::*;
    use rug::{float::Round, ops::Pow as _, Float};

    fn same(a: f64, b: f64) -> bool {
        a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan())
    }

    // `lo` and `hi`, which `pow` gave at (x, y), are MPFR's roundings, and `near`, which
    // `pow_near` gave, is MPFR's rounding to nearest, ties to even, which `pow_rn` rounds once
    // with the subnormals of an `f64`.
    pub(super) fn check_pow(x: f64, y: f64, lo: f64, hi: f64, near: f64) {
        // At x < 0, -∞ included, the three are NaN unless y is ±0, where they are 1, and MPFR
        // differs from that at integer y; `Interval::pow` never passes such an x, and
        // `src/cr.rs` tests the signed wrapper of `pow` there.
        if x < 0.0 {
            return;
        }
        let (want_lo, want_hi) = (pow_rd(x, y), pow_ru(x, y));
        assert!(
            same(lo, want_lo) && same(hi, want_hi),
            "pow({:e}, {:e}): ({:e}, {:e}) != MPFR's ({:e}, {:e})",
            x,
            y,
            lo,
            hi,
            want_lo,
            want_hi
        );
        let want = pow_rn(x, y);
        assert!(
            same(near, want),
            "pow({:e}, {:e}): {:e} to nearest != MPFR's {:e}",
            x,
            y,
            near,
            want
        );
    }

    // `lo` and `hi`, which `pown` gave at (x, n), are MPFR's roundings, and `near`, which
    // `pown_near` gave, is MPFR's rounding to nearest, ties to even, which `pown_rn` rounds
    // once with the subnormals of an `f64`.
    pub(super) fn check_pown(x: f64, n: i32, lo: f64, hi: f64, near: f64) {
        let (want_lo, want_hi) = (pown_rd(x, n), pown_ru(x, n));
        assert!(
            same(lo, want_lo) && same(hi, want_hi),
            "pown({:e}, {}): ({:e}, {:e}) != MPFR's ({:e}, {:e})",
            x,
            n,
            lo,
            hi,
            want_lo,
            want_hi
        );
        let want = pown_rn(x, n);
        assert!(
            same(near, want),
            "pown({:e}, {}): {:e} to nearest != MPFR's {:e}",
            x,
            n,
            near,
            want
        );
    }

    // The precision of the values that the results of the fast path are checked against, far
    // above that of the bound checked.
    const PREC: u32 = 300;

    // |x^y 2^-e - (h + l)| in units of 2^-67, for the (h, l, e) that `fast_pow` gave at (x, y),
    // after checking that they meet the bounds of `fast_pow_correct` in
    // `rocq/theories/FastPow.v`: h = RN(h + l), 1/2 < h < 2, e in [-1021, 1022] and
    // |x^y 2^-e - (h + l)| <= 2^-67. `None` where `fast_pow` gives `None`, and where (x, y) is
    // outside the hypotheses of the theorem: a finite x > 0, a finite y, and x = 1 and
    // |y| <= 2^900, or 2^-60 <= |y ln x|.
    fn fast_pow_error(x: f64, y: f64) -> Option<f64> {
        if !(x.is_finite() && x > 0.0 && y.is_finite()) {
            return None;
        }
        // t is y ln x with ln x and the product rounded toward zero, so that |t| <= |y ln x|,
        // and |t| >= 2^-60 shows that 2^-60 <= |y ln x|.
        let ln = Float::with_val_round(PREC, Float::with_val(53, x).ln_ref(), Round::Zero).0;
        let t = Float::with_val_round(PREC, &ln * y, Round::Zero).0;
        if !((x == 1.0 && y.abs() <= pow2(900)) || t.abs() >= pow2(-60)) {
            return None;
        }
        let (h, l, e) = fast_pow(x, y)?;
        let f = |v: f64| Float::with_val(53, v);
        let mut d = Float::with_val(PREC, (&f(x)).pow(&f(y))) >> i32::try_from(e).unwrap();
        d -= h;
        d -= l;
        d.abs_mut();
        assert!(
            h + l == h && 0.5 < h && h < 2.0 && (-1021..=1022).contains(&e) && d <= pow2(-67),
            "fast_pow({x:e}, {y:e}): ({h:e}, {l:e}, {e}), with |x^y 2^-e - (h + l)| = {:e}",
            d.to_f64()
        );
        Some(d.to_f64() / pow2(-67))
    }

    // `fast_pow` meets the bounds of `fast_pow_correct` (`fast_pow_error`) on 2000 arguments of
    // each set of `pow_case`, and of each set of `pown_case` as `pown` passes them to it, |x|
    // and y = n, and on at least a tenth of each set it gives (h, l, e) inside the hypotheses of
    // the theorem. The test prints how many of each set it checked and their largest error.
    #[test]
    fn fast_pow_bound() {
        let mut rng = Rng(893);
        let mut sets = vec![];
        for name in [
            "lu4", "near1", "mid", "int", "intlu", "t745", "edge", "exact", "nexact",
        ] {
            let args: Vec<(f64, f64)> = (0..2000).map(|i| pow_case(name, &mut rng, i)).collect();
            sets.push((format!("pow {name}"), args));
        }
        for name in [
            "pn2", "pnm2", "pn3", "pn17", "pnint", "pnlu", "pnany", "pnexact", "pnnexact",
        ] {
            let args: Vec<(f64, f64)> = (0..2000)
                .map(|_| {
                    let (x, n) = pown_case(name, &mut rng);
                    (x.abs(), f64::from(n))
                })
                .collect();
            sets.push((format!("pown {name}"), args));
        }
        for (name, args) in sets {
            let errs: Vec<f64> = args
                .iter()
                .filter_map(|&(x, y)| fast_pow_error(x, y))
                .collect();
            let worst = errs.iter().fold(0.0, |a: f64, &b| a.max(b));
            eprintln!(
                "fast_pow, {name}: {} of {} arguments checked, largest error {worst:.4} 2^-67",
                errs.len(),
                args.len()
            );
            // The fewest are in `edge`, where y ln x is mostly outside the range of `fast_exp`.
            assert!(
                errs.len() >= args.len() / 10,
                "fast_pow, {name}: only {} arguments checked",
                errs.len()
            );
        }
    }
}

mod exact;
mod levels;
mod near;
mod near_floats;
mod rules;
mod wide_random;
mod wide_signs;
