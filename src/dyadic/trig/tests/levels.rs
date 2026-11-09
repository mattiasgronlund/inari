// Tests of the evaluations of the trigonometric functions of the dyadic kernel at each level of
// Ziv's strategy that is forced with `ziv_at` and `ziv_near_at`, as
// `src/dyadic/atan/tests/levels.rs` has them for the inverse trigonometric functions.
//
// Each function is taken at a few ordinary arguments, which no rule of `trig.rs` settles, and at
// some near multiples of π/2 and some huge ones, at each of the 64 levels from 1 to 64 limbs,
// not only at those that `ziv` and `ziv_near` try. At each of them, on every platform, `ziv_at`
// either fails or gives the rounding of the function in each direction, and `ziv_near_at`
// either fails or gives its rounding to nearest, and both pass from 2 limbs on. `ziv_cap` and
// `ziv_near_cap`, the steps of `ziv` and `ziv_near` at their cap of 64 limbs, also give the
// roundings at each argument, in both directions and to nearest. On 64-bit Linux and macOS,
// where the tests have MPFR, the rounding to nearest is that of `src/mpfr_calls/mpfr.rs`, each
// enclosure also holds the value of the function that MPFR computes, each doubling of the
// precision at least halves its width, and at each level at which `reduce` is under its cap of
// the 66 limbs of `PI`, the width at `N` limbs is at most 2^(8 - 64 N) times the magnitude of
// the value.
//
// Where its enclosures are widened so that no rounding test passes, `ziv` also gives the
// directed roundings, at its cap (`check_widened` of `src/dyadic/tests.rs`).

use super::*;
use crate::dyadic::tests::check_widened;
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

// 6381956970095103 2^797, the `f64` nearest to a multiple of π/2, of Kahan and McDonald (the
// header of `trig.rs`), as `forced_levels` checks.
const KM: f64 = 5.319372648326541e255;

// The arguments of each of the three functions, which take each branch of the evaluations. cos
// takes the magnitude t = |x| of each, as `Cos` does.
// - `reduce`: it leaves 1e-5, 0.5 and 0.785, up to `NO_REDUCE`, as they are, and takes k = 0 for
//   0.7852, between `NO_REDUCE` and π/4. Above π/4, it takes each k mod 4 with each sign σ:
//   k mod 4 = 1 with σ = -1 for 0.786, just above π/4, and for 1.0, and with σ = 1 for 2.0;
//   2 with σ = -1 for 3.0 and -2.5, and with σ = 1 for 3.3; 3 with σ = -1 for 4.0, and with
//   σ = 1 for 5.0; and 0 with σ = -1 for 5.5, and with σ = 1 for 6.5.
// - The cap of `reduce` at the 66 limbs of `PI`, as `mpfr::capped` states it: 1e10, below
//   2^34, stays under it at each level, and it holds at 64 limbs for 1e19, above 2^63, from 52
//   limbs for `KM`, above 2^849, from 50 limbs for 1e300 and from 49 limbs for `f64::MAX`.
// - `terms`: its cap 6 N + 5 where the enclosure of ρ^2 reaches 1/2, for 0.785, 0.7852, 0.786,
//   4 and 5.5, and fewer terms where ρ^2 is small, down to 1 at 1 limb for the four near the
//   multiples of π/2 below.
// - Near the multiples of π/2, where t - k π/2 cancels: `PI`, `FRAC_PI_2`, 6134899525417045, a
//   worst case of MPFR's `tests/tsin.c` near a multiple of π, and `KM`, whose ρ are about
//   2^-53, 2^-54, 2^-53 and 2^-61. `Tan` divides by sin ρ for the odd k of `FRAC_PI_2` and
//   `KM`, at each level, at which `Encl::div` would panic if the enclosure of sin ρ held 0.
// - `TINY_HYP` = 2^-26, the least argument that the rules of sin leave to `ziv`. Those of cos
//   and tan settle it (`cos_small` and `tan_small`), but `forced` takes the evaluations
//   themselves. To nearest, `ziv_near` takes it for each of the three, as their only rule
//   at finite arguments is for magnitudes below `TINY_NEAR` = 2^-27.
// None of the results is an `f64` or the midpoint between two, which are rational, by the
// theorem that the header of `trig.rs` names.
const ARGS: [f64; 23] = [
    1e-5,
    0.5,
    0.785,
    0.7852,
    0.786,
    1.0,
    2.0,
    3.0,
    -2.5,
    3.3,
    4.0,
    5.0,
    5.5,
    6.5,
    1e10,
    1e19,
    KM,
    1e300,
    f64::MAX,
    std::f64::consts::PI,
    std::f64::consts::FRAC_PI_2,
    6_134_899_525_417_045.0,
    TINY_HYP,
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

// `ziv_near_at::<N>` on `f`, the evaluation of the function `i` at `x`, either fails or gives
// `want`, the rounding to nearest. Returns whether it passed.
fn rounds_near_at<const N: usize, E: Eval>(f: &E, i: usize, x: f64, want: f64) -> bool {
    match ziv_near_at::<N, E>(f) {
        // The bits, as none of the results is a zero.
        Some(y) => {
            assert!(
                y.to_bits() == want.to_bits(),
                "{}({:e}) at {} limbs, to nearest: {:e} != {:e}",
                FUNCTIONS[i].0,
                x,
                N,
                y,
                want
            );
            true
        }
        None => false,
    }
}

// Checks `f`, the evaluation of the function `i` at `x`, at each level, as the header says.
fn forced<E: Eval>(f: &E, i: usize, x: f64) {
    let g = FUNCTIONS[i].1;
    let want = [g(x, false), g(x, true)];
    let passed = at_each_level!(rounds_at(f, i, x, want));
    // From 2 limbs on, the enclosures at these arguments are narrower than the distances from
    // their values to the `f64`s, and each level passes, so that the test compares the roundings
    // of each level, and not only of the first that passes. At 1 limb, `ziv_at` fails in one
    // direction or both for those whose values are within 2^-61 of an `f64` relative to their
    // magnitudes: sin at `KM` and `FRAC_PI_2`, within 2^-122 and 2^-108 below 1, cos at `PI` and
    // 6134899525417045, within 2^-106 and 2^-107 above -1, and at `TINY_HYP`, within 2^-108
    // above 1 - 2^-53, and tan at 5.5.
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
    // Where no rounding test passes, `ziv` returns the bound on the side of the rounding.
    check_widened(f, want, &format!("{}({:e})", FUNCTIONS[i].0, x));
    // The same to nearest. `NEAR[i]` leaves each of these arguments to `ziv_near`, as they are
    // at least `TINY_NEAR`, and cos takes |x| there as `f` does.
    let near = NEAR[i](x);
    let passed_near = at_each_level!(rounds_near_at(f, i, x, near));
    // From 2 limbs on, the enclosures are also narrower than the distances from the values to
    // the midpoints between adjacent `f64`s, the least of which is 2^-60.8 relative to the
    // magnitude, at sin(-2.5), and each level passes. At 1 limb, `ziv_near_at` passes at each
    // of these arguments as well, but the test does not require it: the width there is at most
    // 2^(4.6 - 64) times the magnitude (`mpfr::enclosures`), which is above that distance.
    for (l, &p) in passed_near.iter().enumerate().skip(1) {
        assert!(
            p,
            "{}({:e}) fails at {} limbs to nearest",
            FUNCTIONS[i].0,
            x,
            l + 1
        );
    }
    // As level 64 passes, `ziv_near_cap`, the step of `ziv_near` at its cap, gives the
    // rounding to nearest.
    let y = ziv_near_cap(f);
    assert!(
        y.to_bits() == near.to_bits(),
        "{}({:e}) at the cap, to nearest: {:e} != {:e}",
        FUNCTIONS[i].0,
        x,
        y,
        near
    );
    // The rounding to nearest is MPFR's, by the check of the parent module, which the local
    // `mod mpfr` hides from the glob import.
    #[cfg(all(
        target_pointer_width = "64",
        any(target_os = "linux", target_os = "macos")
    ))]
    super::mpfr::check_near(i, x, near);
    #[cfg(all(
        target_pointer_width = "64",
        any(target_os = "linux", target_os = "macos")
    ))]
    mpfr::enclosures(f, i, x);
}

#[test]
fn forced_levels() {
    assert_eq!(KM, 6_381_956_970_095_103.0 * pow2(797));
    for x in ARGS {
        forced(&Sin(x), SIN, x);
        forced(&Cos(x.abs()), COS, x);
        forced(&Tan(x), TAN, x);
    }
}

#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
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
            SIN => Float::with_val_round(PREC, x.sin_ref(), r),
            COS => Float::with_val_round(PREC, x.cos_ref(), r),
            TAN => Float::with_val_round(PREC, x.tan_ref(), r),
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

    // Whether `reduce` at `n` limbs is held at its cap for the argument t: it takes
    // L = min(66, n + `GUARD_LIMBS` + floor(b / 64)) limbs of `PI` for t in [2^(b - 1), 2^b),
    // and the cap holds where the sum is above 66. There, the width that δ adds to ρ is at
    // most 2^(b - 4223), and no longer shrinks with the level.
    fn capped(t: f64, n: usize) -> bool {
        t > NO_REDUCE && n + GUARD_LIMBS + (Dyadic::<1>::from_f64(t).exp + 64) as usize / 64 > 66
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

    // Each enclosure of `f`, the evaluation of the function `i` at `x`, holds its value, the
    // width at 2 N limbs is at most half of that at N limbs, for N from 1 to 32, and the width
    // at N limbs is at most 2^(8 - 64 N) times the magnitude of the value where `reduce` is
    // under its cap.
    pub(super) fn enclosures<E: Eval>(f: &E, i: usize, x: f64) {
        let v = &[value(i, x, Round::Down), value(i, x, Round::Up)];
        let w = at_each_level!(enclosure_at(f, i, x, v));
        assert!(w[0] > 0, "{}({:e})", FUNCTIONS[i].0, x);
        // The levels up to 48 limbs are under the cap for every `f64`, as b <= 1024, and the
        // width at the cap, at most about 2^-3100 relative to the value at these arguments, is
        // far below half of that at 32 limbs, so the halving needs no exemption.
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
        // The relative width, which the reduction keeps near the multiples of π/2, where
        // t - k π/2 cancels, as the header of `trig.rs` says. `mag`, the bound of the value
        // nearer to 0, is at most its magnitude, as none of the values is 0. At these
        // arguments, the width is at most 2^(4.6 - 64 N) times the magnitude, with 3.4 bits to
        // spare below the bound.
        let mag = if v[0] > 0 {
            v[0].clone()
        } else {
            -v[1].clone()
        };
        for n in 1..=64 {
            if !capped(x.abs(), n) {
                assert!(
                    w[n - 1].clone() << u32::try_from(64 * n - 8).unwrap() <= mag,
                    "{}({:e}) at {} limbs: too wide",
                    FUNCTIONS[i].0,
                    x,
                    n
                );
            }
        }
    }
}
