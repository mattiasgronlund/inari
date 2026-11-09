// Tests of the evaluations of the powers of the dyadic kernel at each level of Ziv's strategy
// that is forced with `ziv_at` and `ziv_near_at`, as `src/dyadic/exp/tests/levels.rs` has them
// for the exponentials.
//
// Each evaluation is taken at a few ordinary arguments, which neither a rule of `pow.rs` nor
// `exact` or `exact_near` settles, at each of the 64 levels from 1 to 64 limbs, not only at
// those that `ziv` and `ziv_near` try. At each of them, `ziv_at` either fails or gives the
// rounding of the power, in each direction, and `ziv_near_at` either fails or gives its
// rounding to nearest, `pow_near` or `pown_near`, on every platform. From 2 limbs on, each of
// these tests passes. `ziv_cap` and `ziv_near_cap`, the steps of `ziv` and `ziv_near` at their
// cap of 64 limbs, also give the roundings at each argument, in both directions and to
// nearest. On 64-bit Linux and macOS, where the tests have MPFR, each enclosure also holds the
// value of the power that MPFR computes, each doubling of the precision at least halves its
// width, and the rounding to nearest has the bits of MPFR's, `pow_rn` or `pown_rn` of
// `src/mpfr_calls/mpfr.rs`.

use super::*;
use crate::dyadic::{ziv_at, ziv_cap, ziv_near_at, ziv_near_cap};

// The array of `$f::<N, _> $args` for each N from 1 to 64, in that order.
macro_rules! at_each_level {
    ($f:ident $args:tt) => {
        at_each_level!(
            @ $f $args;
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
            17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
            33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
            49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64
        )
    };
    (@ $f:ident $args:tt; $($n:literal),*) => {
        [$($f::<$n, _> $args),*]
    };
}

// An evaluation of `pow.rs` at its arguments, by the name of its `Eval`.
#[derive(Clone, Copy, Debug)]
enum Case {
    // (x, y) for x^y.
    Pow(f64, f64),
    // (x, n) for x^n.
    Pown(f64, i32),
}

impl Case {
    // The rounding of the value of the case toward +∞ if `up` and toward -∞ otherwise, by the
    // function of `pow.rs` that computes it.
    fn rounded(self, up: bool) -> f64 {
        match self {
            Case::Pow(x, y) => pow(x, y, up),
            Case::Pown(x, n) => pown(x, n, up),
        }
    }

    // The rounding of the value of the case to nearest, ties to even, by the function of
    // `pow.rs` that computes it. Every x of `CASES` is positive, so that `pown_near` rounds the
    // value that `Pown` encloses, rather than negating the rounding of (-x)^n.
    fn near(self) -> f64 {
        match self {
            Case::Pow(x, y) => pow_near(x, y),
            Case::Pown(x, n) => pown_near(x, n),
        }
    }
}

// 1 + 2^-40 and 1 - 2^-40, which are `f64`s.
const ABOVE_ONE: f64 = 1.0 + 1.0 / 1_099_511_627_776.0;
const BELOW_ONE: f64 = 1.0 - 1.0 / 1_099_511_627_776.0;

// The cases, with t = y ln x for x^y and t = n ln x for x^n.
// - x^y: four ordinary ones, at which |t| is between 1.6 and 8.8, and (2.5, 100.3), where t is
//   91.9. Then four at which |t| is between 700 and 745: e^t is near the largest `f64` for
//   (10.1, 306.3) and (1e300, 1.02), and subnormal for (0.3, 615.7) and (1e-300, 1.07). For
//   1e300 and 1e-300, the x = m 2^e of `reduce` has e = ±997, so that most of the bits of k
//   and y e cancel. (2^-1074, 0.7), where t is -521.1, has e = -1074 and m = 1, for which
//   `reduce` gives a = [0, 0]. Last, x near 1 with a huge y, at which |t| is between 570 and
//   690: 1 ± 2^-40 with y = 6.3e14, and the `f64`s 1 + 2^-52 and 1 - 2^-53 beside 1 with
//   y = 3.1e18 and y = -6e18. `reduce` takes 1.7, 1e300, 1 - 2^-40 and 1 - 2^-53 to an m below
//   1, and the others to an m of at least 1.
// - x^n: four ordinary ones, with |n| from 3 to 40, and 1.0000001 with n = 2^20 + 1 and
//   1 ± 2^-40 with n = i32::MAX and n = i32::MIN, for which binary powering takes 20, 30 and 31
//   squarings. Then three at which |t| is between 700 and 745: 1.7^1335, near the largest
//   `f64`, and 0.51^1100 and 3.3^-600, which are subnormal.
// None of the results is an `f64`, nor a midpoint between two adjacent `f64`s, which an
// enclosure settles to nearest only if it is one of its bounds. Both are dyadic numbers whose
// odd part is below 2^54, as `exact_near` takes them. x^y is one only at a power of 2 or at a
// y = p / 2^k > 0 with p < 35 and k <= 5, from the conditions of `exact_near`: the odd part o
// of x is then that of a dyadic number r to the 2^k, and that of r^p is below 2^54, so that
// 3^(2^k) <= o < 2^53 and 3^p < 2^54 if o > 1. The only power of 2 here is 2^-1074, where
// 0.7 · -1074 is not an integer, and the only such y is 2.5, where 0.3 is not the square of a
// dyadic number, as its o is not a square. x^n is one only if o^n < 2^54 for n > 0 and o = 1
// for n < 0, and here each o is above 2^26 and each |n| at least 3, so that o^|n| > 2^78.
// 1.1^3 and 2.9^12 have an o^n of 154 and 631 bits, so that their enclosures are exact, of
// width 0, from 3 and 10 limbs on.
const CASES: [Case; 24] = [
    Case::Pow(0.3, 2.5),
    Case::Pow(1.7, -3.3),
    Case::Pow(10.1, 0.7),
    Case::Pow(0.3, -7.25),
    Case::Pow(2.5, 100.3),
    Case::Pow(10.1, 306.3),
    Case::Pow(1e300, 1.02),
    Case::Pow(0.3, 615.7),
    Case::Pow(1e-300, 1.07),
    Case::Pow(5e-324, 0.7),
    Case::Pow(ABOVE_ONE, 6.3e14),
    Case::Pow(BELOW_ONE, 6.3e14),
    Case::Pow(1.0 + f64::EPSILON, 3.1e18),
    Case::Pow(1.0 - f64::EPSILON / 2.0, -6e18),
    Case::Pown(1.1, 3),
    Case::Pown(0.7, -5),
    Case::Pown(2.9, 12),
    Case::Pown(10.1, -40),
    Case::Pown(1.0000001, (1 << 20) + 1),
    Case::Pown(ABOVE_ONE, i32::MAX),
    Case::Pown(BELOW_ONE, i32::MIN),
    Case::Pown(1.7, 1335),
    Case::Pown(0.51, 1100),
    Case::Pown(3.3, -600),
];

// `ziv_at::<N>` on `f`, the evaluation of `c`, either fails or gives `want[0]` rounding toward
// -∞ and `want[1]` toward +∞. Returns whether it passed in both directions.
fn rounds_at<const N: usize, E: Eval>(f: &E, c: Case, want: [f64; 2]) -> bool {
    let mut passed = true;
    for up in [false, true] {
        match ziv_at::<N, E>(f, up) {
            // The bits, as none of the results is a zero.
            Some(y) => assert!(
                y.to_bits() == want[usize::from(up)].to_bits(),
                "{:?} at {} limbs, up = {}: {:e} != {:e}",
                c,
                N,
                up,
                y,
                want[usize::from(up)]
            ),
            None => passed = false,
        }
    }
    passed
}

// `ziv_near_at::<N>` on `f`, the evaluation of `c`, either fails or gives `want`, the rounding
// to nearest. Returns whether it passed.
fn near_at<const N: usize, E: Eval>(f: &E, c: Case, want: f64) -> bool {
    match ziv_near_at::<N, E>(f) {
        // The bits, as none of the results is a zero.
        Some(y) => {
            assert!(
                y.to_bits() == want.to_bits(),
                "{:?} at {} limbs to nearest: {:e} != {:e}",
                c,
                N,
                y,
                want
            );
            true
        }
        None => false,
    }
}

// Checks `f`, the evaluation of `c`, at each level, as the header says.
fn forced<E: Eval>(f: &E, c: Case) {
    let want = [c.rounded(false), c.rounded(true)];
    let passed = at_each_level!(rounds_at(f, c, want));
    let near = c.near();
    let passed_near = at_each_level!(near_at(f, c, near));
    // From 2 limbs on, the enclosures at these arguments are far narrower than the distances
    // from their values to the `f64`s and to the midpoints between them, and each level passes
    // in each direction and to nearest, so that the test compares the roundings of each level,
    // and not only of the first that passes.
    for (l, (&p, &q)) in passed.iter().zip(&passed_near).enumerate().skip(1) {
        assert!(p, "{:?} fails at {} limbs", c, l + 1);
        assert!(q, "{:?} fails at {} limbs to nearest", c, l + 1);
    }
    // As level 64 passes, `ziv_cap` and `ziv_near_cap`, the steps of `ziv` and `ziv_near` at
    // their cap, give the roundings.
    for up in [false, true] {
        let y = ziv_cap(f, up);
        assert!(
            y.to_bits() == want[usize::from(up)].to_bits(),
            "{:?} at the cap, up = {}: {:e} != {:e}",
            c,
            up,
            y,
            want[usize::from(up)]
        );
    }
    let y = ziv_near_cap(f);
    assert!(
        y.to_bits() == near.to_bits(),
        "{:?} at the cap to nearest: {:e} != {:e}",
        c,
        y,
        near
    );
    #[cfg(all(
        target_pointer_width = "64",
        any(target_os = "linux", target_os = "macos")
    ))]
    {
        mpfr::enclosures(f, c);
        mpfr::near(c, near);
    }
}

#[test]
fn forced_levels() {
    for c in CASES {
        match c {
            Case::Pow(x, y) => forced(&Pow(x, y), c),
            Case::Pown(x, n) => forced(&Pown(x, n), c),
        }
    }
}

// The hardest arguments that two searches found, those at which `ziv` settles a direction at
// level 2 (`ziv_at::<N>` for N = 1, 2, 4, .., 64 limbs). Neither search found an argument that
// needs a level above 2, so these are the hardest few of each set by the bits they need, and
// `ziv` settles each of them at level 2 in both directions.
// - The first drew 4,096 arguments from each of 20 sets. For x^y: x log-uniform over the
//   positive finite `f64`s, with y uniform in [-4, 4); x as before, with y = t / ln x for a |t|
//   uniform in [100, 745); x at k ulps from 1, for a k of bit length uniform from 1 to 32, with
//   y = t / ln x for a |t| log-uniform in [2^-10, 2^10), where those above 745 are taken as 745;
//   x log-uniform in [2^-64, 2^64), with |y| log-uniform in [2^-8, 2^13); x log-uniform in
//   [2^-30, 2^31), with an integer y from 1 to 40 of either sign; arguments at which x^y is an
//   `f64`, with x a power of 2 or x = r^(2^k) and y = m / 2^k; and those arguments with x or y
//   moved by one ulp. For x^n: n = ±2, ±3, ±5, ±17, ±2^20 and ±(2^31 - 1), and an n of bit
//   length uniform from 1 to 31 and either sign, each with x = ±2^u for a u uniform in
//   [-1000 / |n|, 1000 / |n|).
// - The second drew 10^7 arguments from each of four of those sets: x^y with |t| in
//   [100, 745), with x next to 1 and with x in [2^-64, 2^64), and x^n with n of a uniform bit
//   length.
// Since these searches, the arguments with an integer y from -2^31 to 2^31 - 1 that would
// reach `Pow`, as in the set with an integer y and in the case at y = 2 below, go to `Pown`.
// Each comment gives the bits that its case needs, -log2 of the distance from its value to the
// nearest `f64` relative to the value, with MPFR at 1024 bits for the first search and 512 for
// the second. The two cases at n = 36 of `check_pow_ui` in the tests of MPFR (`tests/tpow.c`),
// which are in `RESULTS`, are harder than those of x^n here: they need about 110 bits, and
// `ziv` settles them at level 2 too.
const HARD_CASES: [(f64, f64); 11] = [
    // Of the first search, next to arguments at which x^y is an `f64`. 7^8 2^56 + 2^26, one ulp
    // above 7^8 2^56, whose 7/8th power is 7^7 2^49: 109.1 bits.
    (4.153976901674411e23, 8.75e-1),
    // 2^-59 - 2^-112, the `f64` below 2^-59, squared: 106.0 bits.
    (1.7347234759768069e-18, 2e0),
    // Of the second search, with |t| in [100, 745).
    (6.798182575293842e-164, 3.213934443778089e-1), // 76.4 bits.
    (2.9234638657778187e162, 7.429005076724499e-1), // 75.8 bits.
    (4.554969755220012e-74, -2.2807364476884926e0), // 75.4 bits.
    // With x next to 1.
    (1.0000000237535767e0, 9.02931815197687e9), // 79.5 bits.
    (9.999999999999869e-1, -1.0468951042097778e16), // 75.8 bits.
    (9.999999999997785e-1, 7.369319119584011e14), // 75.6 bits.
    // With x in [2^-64, 2^64).
    (2.3496494059676592e-12, 3.005149445016049e-1), // 75.2 bits.
    (9.279910986772628e-9, 1.9028607774224946e0),   // 74.2 bits.
    (1.492260342911782e-2, 1.7818319360893456e-1),  // 74.1 bits.
];

// The same for x^n.
const HARD_CASES_N: [(f64, i32); 9] = [
    // Of the second search.
    (-1.0585115533531426e0, 8556),      // 77.9 bits.
    (-1.3041311346334183e1, -251),      // 76.6 bits.
    (1.000001853356881e0, 243_403_058), // 76.3 bits.
    // Of the first search, the hardest at each n that is among its ten hardest arguments of x^n.
    (9.997788587445883e-1, 1 << 20), // 69.4 bits.
    (2.400573939052576e39, -5),      // 69.3 bits.
    (1.0595215055589266e7, -3),      // 68.0 bits.
    // 67.0 bits. Binary powering to n = 2^31 - 1 loses about 30 of the 128 bits of 2 limbs, so
    // that its enclosure there is 2^-98 of its value wide, the widest of the six of the first
    // search here.
    (9.999997626737668e-1, i32::MAX),
    (-7.018110465112488e-7, -17), // 66.2 bits.
    (8.42676785860937e-102, -2),  // 65.8 bits.
];

// Each case of x^y, and each case of x^n at x and at -x.
#[test]
fn hard_cases() {
    for (x, y) in HARD_CASES {
        check_pow(x, y);
    }
    for (x, n) in HARD_CASES_N {
        check_pown(x, n);
        check_pown(-x, n);
    }
}

#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
mod mpfr {
    use super::*;
    use crate::dyadic::tests::check_normal;
    use crate::mpfr_calls::mpfr::{pow_rn, pown_rn};
    use rug::{float::Round, integer::Order, ops::Pow as _, Float, Integer};

    // MPFR's precision for the values of the powers, above that of the last level, so that
    // each bound of an enclosure is a number at it. Then lo <= v if and only if lo <= RD(v),
    // and v <= hi if and only if RU(v) <= hi, for the roundings RD and RU at it.
    const PREC: u32 = 8192;

    // The value of `c` rounded by MPFR at `PREC` bits in the direction `r`.
    fn value(c: Case, r: Round) -> Float {
        let f = |x: f64| Float::with_val(53, x);
        let (v, _) = match c {
            Case::Pow(x, y) => Float::with_val_round(PREC, (&f(x)).pow(&f(y)), r),
            Case::Pown(x, n) => Float::with_val_round(PREC, (&f(x)).pow(n), r),
        };
        v
    }

    // The value of `x` at its precision, which holds it exactly, as in `src/dyadic/tests.rs`.
    fn float<const N: usize>(x: &Dyadic<N>) -> Float {
        let mut f = Float::with_val(64 * N as u32, Integer::from_digits(&x.m, Order::Lsf));
        if x.neg {
            f = -f;
        }
        f <<= i32::try_from(x.exp).unwrap();
        f
    }

    // hi - lo, exactly, as in `src/dyadic/tests.rs`.
    fn width<const N: usize>(x: &Encl<N>) -> Float {
        // Both bounds are multiples of 2^e, for the lower exponent e of the nonzero ones, and
        // below 2^(e + d + p) for the difference d of their exponents, so that their difference
        // fits in d + p + 1 bits.
        let d = if x.lo.is_zero() || x.hi.is_zero() {
            0
        } else {
            x.lo.exp.abs_diff(x.hi.exp)
        };
        let prec = 64 * N as u32 + u32::try_from(d).unwrap() + 1;
        let (w, o) = Float::with_val_round(prec, &float(&x.hi) - &float(&x.lo), Round::Down);
        assert_eq!(o, std::cmp::Ordering::Equal);
        w
    }

    // The enclosure of `f`, the evaluation of `c`, at `N` limbs is normalized and holds the
    // value whose roundings at `PREC` bits are `v`. Returns its width.
    fn enclosure_at<const N: usize, E: Eval>(f: &E, c: Case, v: &[Float; 2]) -> Float {
        let e = f.eval::<N>();
        check_normal(&e.lo);
        check_normal(&e.hi);
        assert!(
            float(&e.lo) <= v[0] && v[1] <= float(&e.hi),
            "{:?} at {} limbs: {:?}",
            c,
            N,
            e
        );
        width(&e)
    }

    // Each enclosure of `f`, the evaluation of `c`, holds its value, and the width at 2 N limbs
    // is at most half of that at N limbs, for N from 1 to 32.
    pub(super) fn enclosures<E: Eval>(f: &E, c: Case) {
        let v = &[value(c, Round::Down), value(c, Round::Up)];
        let w = at_each_level!(enclosure_at(f, c, v));
        assert!(w[0] > 0, "{:?}", c);
        for n in 1..=32 {
            assert!(
                w[2 * n - 1].clone() << 1 <= w[n - 1],
                "{:?} from {} to {} limbs",
                c,
                n,
                2 * n
            );
        }
    }

    // `near`, the rounding of `c` to nearest that `pow_near` or `pown_near` gave, is MPFR's,
    // which `pow_rn` and `pown_rn` round once with the subnormals of an `f64`: the same bits,
    // or NaN for both.
    pub(super) fn near(c: Case, near: f64) {
        let want = match c {
            Case::Pow(x, y) => pow_rn(x, y),
            Case::Pown(x, n) => pown_rn(x, n),
        };
        assert!(
            near.to_bits() == want.to_bits() || (near.is_nan() && want.is_nan()),
            "{:?} to nearest: {:e} != MPFR's {:e}",
            c,
            near,
            want
        );
    }
}
