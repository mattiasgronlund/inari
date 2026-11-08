// Tests of the evaluations of the logarithms and inverse hyperbolic functions of the dyadic
// kernel at each level of Ziv's strategy that is forced with `ziv_at`, as
// `src/dyadic/exp/tests/levels.rs` has them for the exponentials.
//
// Each function is taken at a few ordinary arguments, which no rule of `log.rs` settles, at
// each of the 64 levels from 1 to 64 limbs, not only at those that `ziv` tries. At each of them,
// `ziv_at` either fails or gives the rounding of the function, in both feature sets. `ziv_cap`,
// the step of `ziv` at its cap of 64 limbs, also gives the rounding at each argument, in both
// directions. With `gmp`, each enclosure also holds the value of the function that MPFR
// computes, and each doubling of the precision at least halves its width.

use super::*;
use crate::dyadic::{ziv_at, ziv_cap};

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

// The arguments of each function, in the order of `FUNCTIONS`, which take each branch of its
// evaluation.
// - ln, log2 and log10: four ordinary ones, and two near the ends of the range, where `reduce`
//   takes an e of about a thousand in magnitude. `reduce` takes them to an m above 1 for 0.3,
//   2.5, 10.1 and 1e-300, and below 1 for 1.7 and 1e300.
// - asinh: the series, below `SERIES_MAX`, for ±0.1 and 1e-5, and the logarithm for 0.3, -2.5
//   and 1e10.
// - acosh: the series, below `ACOSH_SERIES_MAX`, for 1.01, and the logarithm for the others,
//   up to 1e300, whose square is far above the largest `f64`.
// - atanh: the series, below `SERIES_MAX`, for ±0.1, and the logarithm for 0.3, -0.5, 0.9 and
//   1 - 2^-30, the last near the pole at 1, where 1 - t = 2^-30.
// None of them is where the result of its function can be an `f64`: 1 for ln and acosh, a power
// of 2 for log2, a power of 10 for log10, and 0 for asinh and atanh. So none of the results is
// an `f64`.
const ARGS: [[f64; 6]; 6] = [
    [0.3, 2.5, 1.7, 10.1, 1e-300, 1e300],
    [0.3, 2.5, 1.7, 10.1, 1e-300, 1e300],
    [0.3, 2.5, 1.7, 10.1, 1e-300, 1e300],
    [0.1, -0.1, 0.3, -2.5, 1e10, 1e-5],
    [1.01, 1.7, 2.5, 10.1, 1e10, 1e300],
    [0.1, -0.1, 0.3, -0.5, 0.9, 1.0 - 1.0 / 1_073_741_824.0],
];

// `ziv_at::<N>` on `f`, the evaluation of the function `i` at `x`, either fails or gives
// `want[0]` rounding toward -∞ and `want[1]` toward +∞. Returns whether it passed in both
// directions.
fn rounds_at<const N: usize, E: Eval>(f: &E, i: usize, x: f64, want: [f64; 2]) -> bool {
    let mut passed = true;
    for up in [false, true] {
        match ziv_at::<N, E>(f, up) {
            // The bits, as none of the results is a zero.
            Some(y) => assert!(
                y.to_bits() == want[usize::from(up)].to_bits(),
                "{}({:e}) at {} limbs, up = {}: {:e} != {:e}",
                FUNCTIONS[i].0,
                x,
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

// Checks `f`, the evaluation of the function `i` at `x`, at each level, as the header says.
fn forced<E: Eval>(f: &E, i: usize, x: f64) {
    let g = FUNCTIONS[i].1;
    let want = [g(x, false), g(x, true)];
    let passed = at_each_level!(rounds_at(f, i, x, want));
    // From 2 limbs on, the enclosures at these arguments are far narrower than the distances
    // from their values to the `f64`s, and each level passes, so that the test compares the
    // roundings of each level, and not only of the first that passes.
    for (l, &p) in passed.iter().enumerate().skip(1) {
        assert!(p, "{}({:e}) fails at {} limbs", FUNCTIONS[i].0, x, l + 1);
    }
    // As level 64 passes, `ziv_cap`, the step of `ziv` at its cap, gives the rounding.
    for up in [false, true] {
        let y = ziv_cap(f, up);
        assert!(
            y.to_bits() == want[usize::from(up)].to_bits(),
            "{}({:e}) at the cap, up = {}: {:e} != {:e}",
            FUNCTIONS[i].0,
            x,
            up,
            y,
            want[usize::from(up)]
        );
    }
    #[cfg(feature = "gmp")]
    mpfr::enclosures(f, i, x);
}

#[test]
fn forced_levels() {
    for (i, args) in ARGS.iter().enumerate() {
        for &x in args {
            match i {
                LN => forced(&Ln(x), i, x),
                LOG2 => forced(&Log2(x), i, x),
                LOG10 => forced(&Log10(x), i, x),
                ASINH => forced(&Asinh(x), i, x),
                ACOSH => forced(&Acosh(x), i, x),
                ATANH => forced(&Atanh(x), i, x),
                _ => unreachable!(),
            }
        }
    }
}

#[cfg(feature = "gmp")]
mod mpfr {
    use super::*;
    use crate::dyadic::tests::check_normal;
    use rug::{float::Round, integer::Order, Float, Integer};

    // MPFR's precision for the values of the functions, above that of the last level, so that
    // each bound of an enclosure is a number at it. Then lo <= v if and only if lo <= RD(v),
    // and v <= hi if and only if RU(v) <= hi, for the roundings RD and RU at it.
    const PREC: u32 = 8192;

    // The value of the function `i` at `x`, rounded by MPFR at `PREC` bits in the direction
    // `r`.
    fn value(i: usize, x: f64, r: Round) -> Float {
        let x = Float::with_val(53, x);
        let (v, _) = match i {
            LN => Float::with_val_round(PREC, x.ln_ref(), r),
            LOG2 => Float::with_val_round(PREC, x.log2_ref(), r),
            LOG10 => Float::with_val_round(PREC, x.log10_ref(), r),
            ASINH => Float::with_val_round(PREC, x.asinh_ref(), r),
            ACOSH => Float::with_val_round(PREC, x.acosh_ref(), r),
            ATANH => Float::with_val_round(PREC, x.atanh_ref(), r),
            _ => unreachable!(),
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

    // The enclosure of `f`, the evaluation of the function `i` at `x`, at `N` limbs is
    // normalized and holds the value whose roundings at `PREC` bits are `v`. Returns its width.
    fn enclosure_at<const N: usize, E: Eval>(f: &E, i: usize, x: f64, v: &[Float; 2]) -> Float {
        let e = f.eval::<N>();
        check_normal(&e.lo);
        check_normal(&e.hi);
        assert!(
            float(&e.lo) <= v[0] && v[1] <= float(&e.hi),
            "{}({:e}) at {} limbs: {:?}",
            FUNCTIONS[i].0,
            x,
            N,
            e
        );
        width(&e)
    }

    // Each enclosure of `f`, the evaluation of the function `i` at `x`, holds its value, and the
    // width at 2 N limbs is at most half of that at N limbs, for N from 1 to 32.
    pub(super) fn enclosures<E: Eval>(f: &E, i: usize, x: f64) {
        let v = &[value(i, x, Round::Down), value(i, x, Round::Up)];
        let w = at_each_level!(enclosure_at(f, i, x, v));
        assert!(w[0] > 0, "{}({:e})", FUNCTIONS[i].0, x);
        for n in 1..=32 {
            assert!(
                w[2 * n - 1].clone() << 1 <= w[n - 1],
                "{}({:e}) from {} to {} limbs",
                FUNCTIONS[i].0,
                x,
                n,
                2 * n
            );
        }
    }
}
