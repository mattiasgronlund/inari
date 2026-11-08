// The cases of MPFR's own tests of these functions, from MPFR 4.2.2's `tests/` (as gmp-mpfr-sys
// 1.7.1 ships them): `tsin.c`, `tcos.c`, `ttan.c` and `tsin_cos.c`, whose `mpfr_sin_cos`
// computes sin and cos at once. The files that these tests read with `data_check`,
// `tests/data/sin` and the like, are not in the crate, and their `test_generic` and `bad_cases`
// draw their arguments at random, so none of their cases are here. Nor are the cases whose
// arguments are not `f64`s: in `tsin.c`, π at 190 bits (l.435-444), the precisions above 53 of
// `test_sign` (l.103), 2^(emin - 1) and its negation for MPFR's least exponent emin
// (`check_tiny`), and the arguments of 113 and 212 bits of `check_binary128` and `check_212`; in
// `tcos.c`, the argument of 57 bits of l.285-296, and π/2 at 20,000 bits of l.119-130, which is
// commented out; in `ttan.c`, the argument of 804 bits of `bug20171218`, π/2 at 20,000 bits of
// l.69-80, and the precisions above 53 of l.140; and in `tsin_cos.c`, the arguments of 1,000
// bits of `bug20091007`, `bug20091008`, `bug20091013` and `test_mpfr_sincos_fast`, the
// ±2^(emin - 1) of `tiny` and `consistency`, which draws its other arguments at random, and
// `large_test`, which runs only on the arguments of its command line.

use super::*;

// MPFR's results at 53 bits in these tests, as "function argument rounding result". The
// numbers are MPFR's strings in base 2, for `mpfr_set_str_binary` or `mpfr_set_str` in base 2,
// which `binary` reads. `D`, `U` and `N` are MPFR's roundings down, up and to nearest; a
// rounding toward zero is `D` here, as each of those results is above 0. `E` marks an exact
// result, a zero, 1 or NaN, which the test checks in one rounding and at its own precision; as
// it is exact, it is MPFR's result in every rounding and at 53 bits, so both directions have to
// give it. Every comparison is bit for bit, so the sign of a zero counts.
const MPFR_RESULTS: [&str; 19] = [
    // tsin.c l.127-133, `test_sign`, "worst case on 53 bits": 6134899525417045, which l.130
    // reads in base 10, rounded to nearest.
    "sin 10101110010111010100010011010111100011111100001010101 N 11011010111101011110111100010101010101110000000001011E-106",
    // tsin.c l.135-144, "Bug on Special cases", rounded to nearest.
    "sin 0.100011011010111101E-32 N 0.10001101101011110100000000000000000000000000000000000E-32",
    // tsin.c l.146-151, which l.426-433 repeats, rounded toward zero.
    "sin 1.1001001000011111101101010100010001000010110100010011 D 1.1111111111111111111111111111111111111111111111111111e-1",
    // tsin.c l.159-193, `check_nans`, at 123 bits: sin is NaN at NaN and ±∞.
    "sin nan E nan",
    "sin inf E nan",
    "sin -inf E nan",
    // tsin.c l.377-383, `check53b`, "Other worst cases showing a bug introduced on 2005-01-29",
    // rounded up.
    "sin 1.0111001111010111010111111000010011010001110001111011e-21 U 1.0111001111010111010111111000010011010001101001110001e-21",
    "sin 1.1011101111111010000001010111000010000111100100101101 U 1.1111100100101100001111100000110011110011010001010101e-1",
    // tcos.c l.71-117, `check_nans`, at 123 bits: cos is NaN at NaN and ±∞, and cos(±0) = 1.
    "cos nan E nan",
    "cos inf E nan",
    "cos -inf E nan",
    "cos 0 E 1",
    "cos -0 E 1",
    // ttan.c l.28-58, `check_nans`, at 123 bits: tan is NaN at NaN and ±∞.
    "tan nan E nan",
    "tan inf E nan",
    "tan -inf E nan",
    // ttan.c l.82-88, "bug found by Kaveh Ghazi on 13 Jul 2007", rounded to nearest.
    "tan 0.10011100110111000001000010110100101000000000000000000E34 N 0.1000010011001010001000010100000110100111000011010101E41",
    // tsin_cos.c l.140-148, `check_nans`, at 123 bits: sin(±0) = ±0. Its other cases are those
    // of tsin.c and tcos.c above, and `overflowed_sin_cos0` (l.164-252) checks sin(-0) = -0
    // again.
    "sin 0 E 0",
    "sin -0 E -0",
];

// The results of `check53` in tsin.c (l.367-375) and tcos.c (l.347-357, where l.357 repeats
// l.355), which tsin_cos.c checks again with `mpfr_sin_cos` (l.694-714), as MPFR's tests have
// them, in base 10, with the roundings of `MPFR_RESULTS`. `mpfr_set_str1` reads the argument
// and `mpfr_cmp_str1` the result in base 10, rounded to nearest at 53 bits, as `str::parse`
// reads them here. The roundings toward zero of the first argument (tsin.c l.370 and tcos.c
// l.350) give the same results as its roundings down, so they are not repeated.
const MPFR_DECIMAL_RESULTS: [&str; 14] = [
    // The first argument is "worst case from PhD thesis of Vincent Lefe`vre:
    // x=8980155785351021/2^54" (tsin.c l.367).
    "sin 4.984987858808754279e-1 N 4.781075595393330379e-1",
    "sin 4.984987858808754279e-1 D 4.781075595393329824e-1",
    "sin 4.984987858808754279e-1 U 4.781075595393330379e-1",
    "sin 1.00031274099908640274 N 8.416399183372403892e-1",
    "sin 1.00229256850978698523 D 8.427074524447979442e-1",
    "sin 1.00288304857059840103 D 8.430252033025980029e-1",
    "sin 1.00591265847407274059 N 8.446508805292128885e-1",
    "cos 4.984987858808754279e-1 N 8.783012931285841817e-1",
    "cos 4.984987858808754279e-1 D 8.783012931285840707e-1",
    "cos 4.984987858808754279e-1 U 8.783012931285841817e-1",
    "cos 1.00031274099908640274 N 0.540039116973283217504",
    "cos 1.00229256850978698523 D 0.538371757797526551137",
    "cos 1.00288304857059840103 D 0.537874062022526966409",
    "cos 1.00591265847407274059 N 0.53531755997839769456",
];

// The other arguments of these tests, as "function argument", for which they give no 53-bit
// result: they round it to another precision, or in a smaller exponent range. Each has at most
// 53 bits, so it is an `f64`, here in the notation of `MPFR_RESULTS`. An argument of
// `mpfr_sin_cos` is here for both sin and cos. `mpfr_pi_arguments` has those that the tests
// compute from π.
const MPFR_ARGUMENTS: [&str; 27] = [
    // tsin.c l.203-226, `check_regression`, of 39 bits, rounded to nearest to 39 bits.
    "sin 0.111011111110110000111000001100000111110E-1",
    // tsin.c l.385-393: 0.5, which l.387 reads in base 10, rounded down to 2 bits.
    "sin 0.1",
    // tsin.c l.406-424, "Can fail on an assert": 77291789194529019661184401408, which l.408
    // reads in base 10, whose sin l.412 rounds to nearest to 42 bits and cos l.413 to 4 bits,
    // and l.414 both with `mpfr_sin_cos`.
    "sin 111110011011111001000101E72",
    "cos 111110011011111001000101E72",
    // tcos.c l.136-158, `special_overflow`, of 24 bits, rounded toward zero to 73 bits with the
    // exponents [-125, 128].
    "cos 0.111101010110110011101101E6",
    // tcos.c l.160-238, `overflowed_cos0`: ±2^-512, of 8 bits, rounded to 8 bits in each
    // rounding with the largest exponent -1 or 0, at which 1 overflows; the third argument, 0,
    // is in `MPFR_RESULTS`.
    "cos 1e-512",
    "cos -1e-512",
    // tcos.c l.240-251, `bug20091030`, of 5 bits, rounded to nearest to 2 bits.
    "cos -0.11001E3",
    // tcos.c l.267-270: 9.81333845856942e-1, which l.269 reads in base 10 to nearest at 53
    // bits, rounded to nearest to 2 bits.
    "cos 0.11111011001110001011000111100110011010011101100101",
    // tcos.c l.272-283, of 30 bits, rounded up to 30 bits.
    "cos 1.00001010001101110010100010101e-1",
    // tcos.c l.298-308, of 5 bits, rounded down to 5 bits.
    "cos 1.1100e-2",
    // tcos.c l.310-339, each rounded to nearest to 32 bits; l.331 calls the last "huge argument
    // reduction".
    "cos 0.10001000001001011000100001E-6",
    "cos -0.1101011110111100111010011001011E-1",
    "cos 0.10000010000001101011101111001011E40",
    // tcos.c l.341-345, of 3 bits, rounded down to 3 bits.
    "cos 0.110E60",
    // tcos.c l.362-369, "check inexact flag", of 3 bits, rounded up to 13 bits.
    "cos -0.100E196",
    // ttan.c l.60-67, "exercise recomputation", of 14 bits, rounded up to 24 bits.
    "tan 0.10100000101010E0",
    // ttan.c l.113-132, `coverage`: 3 2^-4, the greatest number of 2 bits with the largest
    // exponent -2, rounded away from zero to 2 bits with that exponent, at which it overflows.
    "tan 0.11E-2",
    // ttan.c l.150-159: 0.5, which l.151 reads in base 10, rounded down to 2 bits.
    "tan 0.1",
    // tsin_cos.c l.150-157, in `check_nans`: 4, of 2 bits, rounded to nearest to 2 bits.
    "sin 100",
    "cos 100",
    // tsin_cos.c l.276-305, `test20071214`: 3 2^-4, of 4 bits, rounded down, up and to nearest
    // to 4 bits.
    "sin 0.11E-2",
    "cos 0.11E-2",
    // tsin_cos.c l.512-554, `bug20091122`, of 5 bits, rounded to nearest to 3 bits.
    "sin 0.11111E49",
    "cos 0.11111E49",
    // tsin_cos.c l.638-665, `coverage_01032011`: -0.7, which l.649 reads in base 10 to nearest
    // at 1 bit, as -0.5, rounded to nearest to 1 bit.
    "sin -0.1",
    "cos -0.1",
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

// The number that `str::parse` reads from `s` in base 10, rounded to nearest.
fn decimal(s: &str) -> f64 {
    s.parse().unwrap()
}

// The index in `FUNCTIONS` of the function `name`.
fn index(name: &str) -> usize {
    FUNCTIONS.iter().position(|(n, _)| *n == name).unwrap()
}

// `a` and `b` are the same `f64`, bit for bit, or NaN both.
fn same(a: f64, b: f64) -> bool {
    a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan())
}

// Checks the case `case` of `MPFR_RESULTS` or `MPFR_DECIMAL_RESULTS`, whose numbers `read`
// reads: both directions through `check`, and the one of the rounding against MPFR's result.
fn check_case(case: &str, read: fn(&str) -> f64) {
    let v: Vec<&str> = case.split(' ').collect();
    let (i, x) = (index(v[0]), read(v[1]));
    check(i, x);
    let (lo, hi) = (FUNCTIONS[i].1(x, false), FUNCTIONS[i].1(x, true));
    let (rnd, want) = (v[2], read(v[3]));
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

#[test]
fn mpfr_test_cases() {
    for case in MPFR_RESULTS {
        check_case(case, binary);
    }
    for case in MPFR_DECIMAL_RESULTS {
        check_case(case, decimal);
    }
    for case in MPFR_ARGUMENTS {
        let v: Vec<&str> = case.split(' ').collect();
        check(index(v[0]), binary(v[1]));
    }
}

// The arguments that tsin.c and ttan.c compute from π as `mpfr_const_pi` rounds it, computed
// here as the tests compute them, with rug, so only where the tests have MPFR. Each has at most
// 53 bits, and none has a 53-bit result in these tests.
#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
#[test]
fn mpfr_pi_arguments() {
    use rug::{
        float::{Constant, Round},
        Float,
    };
    // tsin.c l.395-404, "bug found by Kevin Ryde": 3π/2 at 2 bits, from π rounded to nearest,
    // times 3 and over 2, each rounded to nearest, whose sin l.399 rounds to nearest to 2 bits.
    let mut x = Float::with_val(2, Constant::Pi);
    x *= 3;
    x /= 2;
    check(SIN, x.to_f64());
    // tsin.c l.91-125, `test_sign`: k π for k = 2, 4 and 6, from π rounded down and up to 4,096
    // bits, times k, rounded down and up to p bits, for the p from 8 to 53 of l.103's 8 to 128,
    // whose sin l.108 and l.117 round to nearest to 2 bits.
    let pid = Float::with_val_round(4096, Constant::Pi, Round::Down).0;
    let piu = Float::with_val_round(4096, Constant::Pi, Round::Up).0;
    for p in 8..=53 {
        for k in [2u32, 4, 6] {
            let lo = Float::with_val_round(p, &pid * k, Round::Down).0;
            let hi = Float::with_val_round(p, &piu * k, Round::Up).0;
            check(SIN, lo.to_f64());
            check(SIN, hi.to_f64());
        }
    }
    // ttan.c l.161-189: 3π/4 at each precision of l.139, and 7π/4 at those of l.140 up to 53
    // bits, from π rounded to nearest, times 3 or 7 and over 4, each rounded to nearest, whose
    // tan l.168 and l.183 round to nearest at the same precision.
    let precisions: [(u32, &[u32]); 2] = [
        (3, &[14, 15, 19, 22, 23, 24, 25, 40, 41, 52]),
        (7, &[4, 5, 6, 19]),
    ];
    for (k, ps) in precisions {
        for &p in ps {
            let mut x = Float::with_val(p, Constant::Pi);
            x *= k;
            x /= 4;
            check(TAN, x.to_f64());
        }
    }
}
