// The cases of MPFR's own tests of these functions, from MPFR 4.2.2's `tests/` (as gmp-mpfr-sys
// 1.7.1 ships them), on every platform: `tatan.c` for atan and atan2, `tasin.c` and
// `tacos.c`. The files that these tests read with `data_check`, `tests/data/atan` and the like,
// are not in the crate, and their `test_generic` and `bad_cases` draw their arguments at
// random, so none of their cases are here.

use super::*;

// MPFR's results at 53 bits in these tests, as "function arguments rounding result". The
// numbers are MPFR's strings for `mpfr_set_str_binary`, which `binary` reads, or, for a result
// that a test computes, such as π/2 from `mpfr_const_pi`, that result in the same notation.
// `D`, `U` and `N` are MPFR's roundings down, up and to nearest; where a test loops over the
// roundings, the others are one of these. `E` marks an exact result, a zero or NaN, which the
// test checks in one rounding; as it is exact, it is MPFR's result in every rounding, so both
// directions have to give it. Every comparison is bit for bit, so the sign of a zero counts.
const MPFR_RESULTS: [&str; 45] = [
    // tatan.c l.35-36, `special`, at 53 bits, rounded to nearest.
    "atan 1.0000100110000001100111100011001110101110100111011101 N 1.1001101101110100101100110011011101101000011010111110e-1",
    // tatan.c l.51-80: atan(±∞) = ±π/2 in every rounding at 53 bits, with π rounded by
    // `mpfr_const_pi` toward the same side as the result (π's 53-bit roundings down and to
    // nearest are the same).
    "atan inf D 1.1001001000011111101101010100010001000010110100011000",
    "atan inf N 1.1001001000011111101101010100010001000010110100011000",
    "atan inf U 1.1001001000011111101101010100010001000010110100011001",
    "atan -inf D -1.1001001000011111101101010100010001000010110100011001",
    "atan -inf N -1.1001001000011111101101010100010001000010110100011000",
    "atan -inf U -1.1001001000011111101101010100010001000010110100011000",
    // tatan.c l.82-118: atan(NaN) = NaN and atan(±0) = ±0, at 53 bits.
    "atan nan E nan",
    "atan 0 E 0",
    "atan -0 E -0",
    // tatan.c l.315-382, `special_atan2`, at 4 bits: the arguments with a NaN (l.318-324), and
    // those whose results are zeros (l.327-333, l.351-357 and l.376-382). Both are exact, so
    // they are the same at 53 bits.
    "atan2 0 nan E nan",
    "atan2 nan 0 E nan",
    "atan2 0 0 E 0",
    "atan2 -0 0 E -0",
    "atan2 -0 1 E -0",
    "atan2 0 1 E 0",
    "atan2 -1 inf E -0",
    "atan2 1 inf E 0",
    // tatan.c l.489-496, `atan2_bug_20071003`, at 53 bits, rounded to nearest.
    "atan2 -0.10100110110100110111010110111111100110100010001110110E2 0.10100101010110010100010010111000110110011110001011110E3 N -0.11101111001101101100111011001101000010010111101110110E-1",
    // tatan.c l.548-554, `atan2_pow_of_2`: atan2(42 2^d, 2^d) = atan 42 for d = 0, -1 and 1, at
    // 53 bits, rounded to nearest.
    "atan2 101010 1 N 1100011000000011110011111001100110101000011010010011E-51",
    "atan2 10101 0.1 N 1100011000000011110011111001100110101000011010010011E-51",
    "atan2 1010100 10 N 1100011000000011110011111001100110101000011010010011E-51",
    // tasin.c l.37-92, `special`, at 53 bits: asin is NaN at NaN, ±∞ and ±2, and asin(±0) =
    // ±0, which l.196-215, `test20071215`, checks again.
    "asin nan E nan",
    "asin inf E nan",
    "asin -inf E nan",
    "asin 10 E nan",
    "asin -10 E nan",
    "asin 0 E 0",
    "asin -0 E -0",
    // tasin.c l.94-123: asin(±1) = ±π/2 in every rounding at 53 bits, with π rounded as for
    // atan(±∞) above.
    "asin 1 D 1.1001001000011111101101010100010001000010110100011000",
    "asin 1 N 1.1001001000011111101101010100010001000010110100011000",
    "asin 1 U 1.1001001000011111101101010100010001000010110100011001",
    "asin -1 D -1.1001001000011111101101010100010001000010110100011001",
    "asin -1 N -1.1001001000011111101101010100010001000010110100011000",
    "asin -1 U -1.1001001000011111101101010100010001000010110100011000",
    // tacos.c l.111-141, `main`, at 53 bits: acos is NaN at NaN and ±2, and acos 1 = +0.
    "acos nan E nan",
    "acos 10 E nan",
    "acos -10 E nan",
    "acos 1 E 0",
    // tacos.c l.143-171: acos 0 = π/2 and acos(-1) = π in every rounding at 53 bits, with π
    // rounded in the direction of the result.
    "acos 0 D 1.1001001000011111101101010100010001000010110100011000",
    "acos 0 N 1.1001001000011111101101010100010001000010110100011000",
    "acos 0 U 1.1001001000011111101101010100010001000010110100011001",
    "acos -1 D 11.001001000011111101101010100010001000010110100011000",
    "acos -1 N 11.001001000011111101101010100010001000010110100011000",
    "acos -1 U 11.001001000011111101101010100010001000010110100011001",
];

// The other arguments of these tests, as "function arguments", for which they give no 53-bit
// result: they round it to another precision, or in a smaller exponent range. Each has at most
// 53 bits, so it is an `f64`, here in the notation of `MPFR_RESULTS`.
const MPFR_ARGUMENTS: [&str; 35] = [
    // tatan.c l.125 and l.135, each rounded to nearest to 32 bits.
    "atan 0.10000100001100101001001001011001",
    "atan -0.1100001110110000010101011001011",
    // tatan.c l.149, -1 of 3 bits, rounded down to 192 bits; l.175 rounds it to nearest to 51
    // bits and checks the sign.
    "atan -0.100e1",
    // tatan.c l.163-164, of 51 bits, rounded to nearest to 51 bits, under l.160's "Test
    // regression".
    "atan 0.101100100000101111111010001111111000001000000000000E-11",
    // tatan.c l.182, of 48 bits, rounded down to 48 bits.
    "atan 1.11001110010000011111100000010000000000000000000e-19",
    // tatan.c l.227, `special_overflow`, of 24 bits, rounded to nearest to 48 bits with the
    // exponents [-125, 128].
    "atan 0.101101010001001101111010E0",
    // tatan.c l.267: 1, whose result π/4 l.264-302 rounds to 48 bits with the largest exponent
    // 1, and to 2 bits with the least exponent 1. l.237-262 round atan(+∞) = π/2 to 48 bits with
    // the largest exponent 1 and with the least exponent 3; `MPFR_RESULTS` has +∞.
    "atan 1",
    // tatan.c l.585, `reduced_expo_range`: 2^-6, of 12 bits, rounded to nearest to 12 bits with
    // the exponents [-5, -5].
    "atan 0.1e-5",
    // tatan.c l.334-416, `special_atan2`: the other arguments, whose results ±π, ±π/2, ±π/4
    // and ±3π/4 l.315 rounds to 4 bits, and l.415-416 the last also to 905 bits toward zero.
    "atan2 -0 -0",
    "atan2 0 -0",
    "atan2 0 -1",
    "atan2 -0 -1",
    "atan2 1 0",
    "atan2 1 -0",
    "atan2 -1 -0",
    "atan2 -1 0",
    "atan2 1 -inf",
    "atan2 -1 -inf",
    "atan2 -inf -1",
    "atan2 inf -1",
    "atan2 inf -inf",
    "atan2 inf inf",
    "atan2 -inf inf",
    "atan2 -inf -inf",
    // tatan.c l.424-477, `smallvals_atan2`, divides numbers of MPFR's least exponent, which are
    // below every `f64`, by 1, 1.5, 1.25 and 4. Here the same divisors divide -2^-1074,
    // 3 2^-1074, 2^-1074 and 2^-1074 instead, so that the quotients are at or near 2^-1074, the
    // least `f64` above 0. tatan.c l.518-532, `atan2_different_prec`, is not here: its y,
    // 1 - 2^-86, is not an `f64`.
    "atan2 -1e-1074 1",
    "atan2 11e-1074 1.1",
    "atan2 1e-1074 1.01",
    "atan2 1e-1074 100",
    // tasin.c l.128 and l.137, each rounded to nearest to 32 bits.
    "asin 0.1101110111111111001011101000101",
    "asin -0.01110111000011101010111100000101",
    // tasin.c l.150, of 9 bits, rounded down to 19 bits.
    "asin 0.110000000E-6",
    // tasin.c l.179 and tacos.c l.82, `special_overflow`, of 24 bits, each rounded to nearest to
    // 48 bits with the exponents [-125, 128]. tasin.c l.230, `reduced_expo_range`, rounds
    // asin(-1) away from zero to 4 bits with the exponents [1, 1], and tacos.c l.55-61 acos 0
    // to nearest to 2 bits; `MPFR_RESULTS` has both arguments.
    "asin 0.101100100000000000110100E0",
    "acos 0.101100100000000000110100E0",
    // tacos.c l.36, rounded to nearest to 32 bits, and l.45, rounded toward zero to 32 bits.
    "acos 0.10001000001001011000100001E-6",
    "acos -0.01101011110111100111010011001011",
];

// The number that MPFR's `mpfr_set_str_binary` reads from `s` (an optional sign, binary digits
// with an optional point, and an optional power of 2 after `e` or `E`), or `inf`, `-inf` or
// `nan` as `str::parse` reads them. Each number here has at most 53 significant bits and is a
// multiple of 2^-1074 below 2^1024, so it is an `f64`.
fn binary(s: &str) -> f64 {
    if matches!(s, "inf" | "-inf" | "nan") {
        return s.parse().unwrap();
    }
    let (neg, t) = match s.strip_prefix('-') {
        Some(t) => (true, t),
        None => (false, s),
    };
    let (digits, e) = match t.find(['e', 'E']) {
        Some(i) => (&t[..i], t[i + 1..].parse::<i32>().unwrap()),
        None => (t, 0),
    };
    let (int, frac) = digits.split_once('.').unwrap_or((digits, ""));
    let m = u64::from_str_radix(&[int, frac].concat(), 2).unwrap();
    let x = if m == 0 {
        0.0
    } else {
        // m 2^(e - the digits after the point) = m' 2^k with m' odd.
        let z = m.trailing_zeros();
        let k = e - i32::try_from(frac.len()).unwrap() + i32::try_from(z).unwrap();
        // m' 2^k is exact for an m' below 2^53 and a k in [-1074, 970].
        assert!(
            m >> z < 1 << 53 && (-1074..=970).contains(&k),
            "{} is not an f64",
            s
        );
        (m >> z) as f64 * pow2(k)
    };
    if neg {
        -x
    } else {
        x
    }
}

// The two directions of the function `v[0]` at the arguments after it, which `check` or
// `check2` has checked, and the number of words of `v` that they took.
fn directions(v: &[&str]) -> ((f64, f64), usize) {
    if v[0] == "atan2" {
        let (y, x) = (binary(v[1]), binary(v[2]));
        check2(y, x);
        ((atan2(y, x, false), atan2(y, x, true)), 3)
    } else {
        let i = FUNCTIONS.iter().position(|(n, _)| *n == v[0]).unwrap();
        let x = binary(v[1]);
        check(i, x);
        ((FUNCTIONS[i].1(x, false), FUNCTIONS[i].1(x, true)), 2)
    }
}

// `a` and `b` are the same `f64`, bit for bit, or NaN both.
fn same(a: f64, b: f64) -> bool {
    a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan())
}

#[test]
fn mpfr_test_cases() {
    for case in MPFR_RESULTS {
        let v: Vec<&str> = case.split(' ').collect();
        let ((lo, hi), n) = directions(&v);
        let (rnd, want) = (v[n], binary(v[n + 1]));
        let ok = match rnd {
            "D" => same(lo, want),
            "U" => same(hi, want),
            "N" => same(lo, want) || same(hi, want),
            "E" => same(lo, want) && same(hi, want),
            _ => panic!("{}: no rounding {}", case, rnd),
        };
        assert!(
            ok,
            "{}: ({:e}, {:e}), MPFR's tests {:e}",
            case, lo, hi, want
        );
    }
    for case in MPFR_ARGUMENTS {
        directions(&case.split(' ').collect::<Vec<_>>());
    }
}
