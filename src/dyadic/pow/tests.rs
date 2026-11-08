// Tests of the powers of the dyadic kernel. Every generator runs on every platform through
// `check_pow` and `check_pown`, which check that the two directions give the same `f64` or two
// adjacent ones, or NaN for both. On 64-bit Linux and macOS, where the tests have MPFR, they
// also compare both directions with `pow_rd`, `pow_ru`, `pown_rd` and `pown_ru` of
// `src/mpfr_calls/mpfr.rs`, which compute them with MPFR, which they have to agree with bit for
// bit.

use super::*;
use crate::dyadic::tests::Rng;

// The `f64` after `x` toward +∞, for `x` below +∞. `f64::next_up` needs a Rust after the MSRV.
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

// Checks x^y in both directions, as the header says.
fn check_pow(x: f64, y: f64) {
    let (lo, hi) = (pow(x, y, false), pow(x, y, true));
    check_pair(&format!("pow({:e}, {:e})", x, y), lo, hi);
    #[cfg(all(
        target_pointer_width = "64",
        any(target_os = "linux", target_os = "macos")
    ))]
    mpfr::check_pow(x, y, lo, hi);
}

// Checks x^n in both directions, as the header says.
fn check_pown(x: f64, n: i32) {
    let (lo, hi) = (pown(x, n, false), pown(x, n, true));
    check_pair(&format!("pown({:e}, {})", x, n), lo, hi);
    #[cfg(all(
        target_pointer_width = "64",
        any(target_os = "linux", target_os = "macos")
    ))]
    mpfr::check_pown(x, n, lo, hi);
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

#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
mod mpfr {
    use crate::mpfr_calls::mpfr::*;

    fn same(a: f64, b: f64) -> bool {
        a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan())
    }

    // `lo` and `hi`, which `pow` gave at (x, y), are MPFR's roundings.
    pub(super) fn check_pow(x: f64, y: f64, lo: f64, hi: f64) {
        // NaN here for x < 0, where MPFR differs at integer y; `Interval::pow` never passes it.
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
    }

    // `lo` and `hi`, which `pown` gave at (x, n), are MPFR's roundings.
    pub(super) fn check_pown(x: f64, n: i32, lo: f64, hi: f64) {
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
    }
}

mod exact;
mod levels;
mod near_floats;
mod rules;
