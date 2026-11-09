// Tests of the evaluations of the inverse trigonometric functions of the dyadic kernel, and of
// its π, at each level of Ziv's strategy that is forced with `ziv_at` and `ziv_near_at`, as
// `src/dyadic/log/tests/levels.rs` has them for the logarithms.
//
// Each evaluation is taken at a few ordinary arguments, which no rule of `atan.rs` settles but
// atan at 1e300, above `HUGE_ATAN`, at each of the 64 levels from 1 to 64 limbs, not only at
// those that `ziv` and `ziv_near` try. At each of them, on every platform, `ziv_at` either
// fails or gives the rounding of the function in its direction, and `ziv_near_at` either fails
// or gives its rounding to nearest, which is one of the two directed roundings. `ziv_cap`, the
// step of `ziv` at its cap of 64 limbs, also gives the rounding at each argument, in both
// directions, and `ziv_near_cap`, the step of `ziv_near` at its cap, the rounding to nearest.
// On 64-bit Linux and macOS, where the tests have MPFR, the rounding to nearest is also MPFR's,
// each enclosure holds the value of the function that MPFR computes, and each doubling of the
// precision at least halves its width.

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

// An evaluation of `atan.rs` at its arguments, by the name of its `Eval`, or π itself.
#[derive(Clone, Copy, Debug)]
enum Case {
    Atan(f64),
    // (y, x), y first, as for `atan2`.
    Atan2(f64, f64),
    Asin(f64),
    Acos(f64),
    PiMul(f64),
    Pi,
}

impl Case {
    // The rounding of the value of the case toward +∞ if `up` and toward -∞ otherwise, by the
    // function of `atan.rs` that computes it. π, 3.14159265358979323..., is between the `f64`
    // nearest to it, `PI` = 3.14159265358979311..., and the next one, 3.14159265358979356...,
    // so that those are its roundings.
    fn rounded(self, up: bool) -> f64 {
        match self {
            Case::Atan(x) => atan(x, up),
            Case::Atan2(y, x) => atan2(y, x, up),
            Case::Asin(x) => asin(x, up),
            Case::Acos(x) => acos(x, up),
            Case::PiMul(c) => pi_times(c, up),
            Case::Pi if up => next_up(std::f64::consts::PI),
            Case::Pi => std::f64::consts::PI,
        }
    }

    // The rounding of the value of the case to nearest, ties to even, by the function of
    // `atan.rs` that computes it, and for π, `PI`, the `f64` nearest to it.
    fn near(self) -> f64 {
        match self {
            Case::Atan(x) => atan_near(x),
            Case::Atan2(y, x) => atan2_near(y, x),
            Case::Asin(x) => asin_near(x),
            Case::Acos(x) => acos_near(x),
            Case::PiMul(c) => pi_times_near(c),
            Case::Pi => std::f64::consts::PI,
        }
    }
}

// `pi::<N>()` as an evaluation.
struct Pi;

impl Eval for Pi {
    fn eval<const N: usize>(&self) -> Encl<N> {
        pi::<N>()
    }
}

// The cases, which take each branch of the evaluations.
// - atan: `atan_encl` takes its series alone for 0.3 and 0.003, below `T1`, its case 1 - w for
//   0.7, below 1, w - 1 for 1.7, up to `T2`, and 1 / w for 10.1, 1e10, 1e300, where 1 / w is
//   1e-300, and -2.5, whose sign `Atan` takes.
// - asin: `asin_parts` takes atan(t / r) for t = |x| up to `ASIN_SPLIT`, for which
//   `atan_encl` takes its series for 0.3 and 1e-5, its case 1 - w for -0.6, where
//   t / r = 3/4, and its case w - 1 for 0.72, where t / r = 1.0375..., and atan(r / t) above
//   it, with the case 1 - w for 0.8, where r / t = 3/4, and the series for 0.99 and -0.999,
//   near 1, where r is small. 1e-5 is above `TINY_ASIN`.
// - acos: the same, 0.72 and its case w - 1 among them, and 0.0 and -1.0, where t / r and
//   r / t are 0, so that `Acos` gives π/2 and π.
// - atan2: the four cases of `Atan2`, at the quotients 1/3 and 1/4, for which `atan_encl`
//   takes its series: (1, 3), (3, 1) and (1, -3), and (-3, -1) and (2, -0.5), the last case
//   for both signs of y. (2, 3) has the quotient 2/3, for which `atan_encl` takes its case
//   1 - w, and (1, 1), where |y| = |x|, has the quotient [1, 1], for which it takes its case
//   w - 1 at w = 1, where (w - 1) / (w + 1) is the exact [0, 0] and the value is π/4. The
//   quotient of `Atan2` is at most 1, below `T2`, so that `atan_encl` never takes its case
//   1 / w for it. (1e-300, 1e300) has the quotient 1e-600, below 2^-1074 and so not an `f64`,
//   which `tiny_quotient` leaves to `ziv`, and its value rounds to +0 and to 2^-1074.
//   (1e-5, 1) has the exact quotient 1e-5, an `f64` above `TINY_HYP`, which `tiny_quotient`
//   also leaves to `ziv`.
// - atan_series: it takes the series at u itself, without the halving, where the upper bound
//   of u is at most `NO_HALVE`, 2^-8, with the terms that `terms` counts from u^2: for atan at
//   0.003, where u = w = 0.003 is below 2^-8 = 0.0039, and at 1e10, where u = 1 / w is 1e-10,
//   and for atan2 at (1e-5, 1), where u = w is 1e-5. It also takes it for atan at 1e300, asin
//   and acos at 1e-5 and atan2 at (1e-300, 1e300), where u is about 1e-300, 1e-5 and 1e-600,
//   and for acos at 0.0 and -1.0 and atan2 at (1, 1), where u is 0. It halves u for the other
//   arguments of atan, asin, acos and atan2.
// - c π: 1/4, 1/2, -3/4 and 1, which are the c that `atan` and `atan2` pass to `pi_times` up
//   to their signs.
// None of the results is an `f64`, which Ziv's strategy could settle only with an exact bound:
// the header of `atan.rs` names 1 for acos as the only argument outside the rules with such a
// result, atan 1e300 lies strictly between two adjacent `f64`s, as the comment of `HUGE_ATAN`
// says, and c π is irrational for c != 0. Nor is any of them the midpoint of two adjacent
// `f64`s, which the test to nearest could settle only with an exact bound in the same way:
// each is a nonzero angle whose cosine and sine are algebraic, which makes it transcendental by
// the Lindemann-Weierstrass theorem, and so not a dyadic number.
const CASES: [Case; 38] = [
    Case::Atan(0.3),
    Case::Atan(0.003),
    Case::Atan(0.7),
    Case::Atan(1.7),
    Case::Atan(10.1),
    Case::Atan(1e10),
    Case::Atan(1e300),
    Case::Atan(-2.5),
    Case::Asin(0.3),
    Case::Asin(-0.6),
    Case::Asin(0.72),
    Case::Asin(0.8),
    Case::Asin(0.99),
    Case::Asin(-0.999),
    Case::Asin(1e-5),
    Case::Acos(0.3),
    Case::Acos(-0.6),
    Case::Acos(0.72),
    Case::Acos(0.8),
    Case::Acos(0.99),
    Case::Acos(-0.999),
    Case::Acos(1e-5),
    Case::Acos(0.0),
    Case::Acos(-1.0),
    Case::Atan2(1.0, 3.0),
    Case::Atan2(3.0, 1.0),
    Case::Atan2(1.0, -3.0),
    Case::Atan2(-3.0, -1.0),
    Case::Atan2(1e-300, 1e300),
    Case::Atan2(1e-5, 1.0),
    Case::Atan2(2.0, -0.5),
    Case::Atan2(2.0, 3.0),
    Case::Atan2(1.0, 1.0),
    Case::PiMul(0.25),
    Case::PiMul(0.5),
    Case::PiMul(-0.75),
    Case::PiMul(1.0),
    Case::Pi,
];

// `ziv_at::<N>` on `f`, the evaluation of `c`, either fails or gives `want[0]` rounding toward
// -∞ and `want[1]` toward +∞. Returns whether it passed in both directions.
fn rounds_at<const N: usize, E: Eval>(f: &E, c: Case, want: [f64; 2]) -> bool {
    let mut passed = true;
    for up in [false, true] {
        match ziv_at::<N, E>(f, up) {
            // The bits, which tell +0 from -0: atan2(1e-300, 1e300) rounds down to +0.
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

// `ziv_near_at::<N>` on `f`, the evaluation of `c`, either fails or gives `want`, its rounding
// to nearest. Returns whether it passed.
fn rounds_near_at<const N: usize, E: Eval>(f: &E, c: Case, want: f64) -> bool {
    match ziv_near_at::<N, E>(f) {
        // The bits, which tell +0 from -0: atan2(1e-300, 1e300) rounds to nearest to +0.
        Some(y) => {
            assert!(
                y.to_bits() == want.to_bits(),
                "{:?} to nearest at {} limbs: {:e} != {:e}",
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
    let near = c.near();
    assert!(
        near.to_bits() == want[0].to_bits() || near.to_bits() == want[1].to_bits(),
        "{:?}: {:e} to nearest, outside ({:e}, {:e})",
        c,
        near,
        want[0],
        want[1]
    );
    let passed = at_each_level!(rounds_at(f, c, want));
    let passed_near = at_each_level!(rounds_near_at(f, c, near));
    // From 2 limbs on, the enclosures at these arguments are far narrower than the distances
    // from their values to the `f64`s and to the midpoints between them, and each level passes
    // in each direction and to nearest, so that the test compares the roundings of each level,
    // and not only of the first that passes.
    for (l, (&p, &q)) in passed.iter().zip(&passed_near).enumerate().skip(1) {
        assert!(p, "{:?} fails at {} limbs", c, l + 1);
        assert!(q, "{:?} fails to nearest at {} limbs", c, l + 1);
    }
    // As level 64 passes, `ziv_cap`, the step of `ziv` at its cap, gives the rounding.
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
    // As level 64 passes to nearest, `ziv_near_cap`, the step of `ziv_near` at its cap, gives
    // the rounding to nearest.
    let y = ziv_near_cap(f);
    assert!(
        y.to_bits() == near.to_bits(),
        "{:?} to nearest at the cap: {:e} != {:e}",
        c,
        y,
        near
    );
    #[cfg(all(
        target_pointer_width = "64",
        any(target_os = "linux", target_os = "macos")
    ))]
    {
        mpfr::near(c, near);
        mpfr::enclosures(f, c);
    }
}

#[test]
fn forced_levels() {
    for c in CASES {
        match c {
            Case::Atan(x) => forced(&Atan(x), c),
            Case::Atan2(y, x) => forced(&Atan2(y, x), c),
            Case::Asin(x) => forced(&Asin(x), c),
            Case::Acos(x) => forced(&Acos(x), c),
            Case::PiMul(x) => forced(&PiMul(x), c),
            Case::Pi => forced(&Pi, c),
        }
    }
}

#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
mod mpfr {
    use super::*;
    // The checks of the parent's `mpfr`, which this module hides from `use super::*`. They take
    // the place of the parent's own `check_near`, which the glob imports.
    use super::super::mpfr::{check2_near, check_near};
    use crate::dyadic::tests::check_normal;
    use rug::{
        float::{Constant, Round},
        integer::Order,
        Float, Integer,
    };

    // MPFR's precision for the values of the functions, above that of the last level, so that
    // each bound of an enclosure is a number at it. Then lo <= v if and only if lo <= RD(v),
    // and v <= hi if and only if RU(v) <= hi, for the roundings RD and RU at it.
    const PREC: u32 = 8192;

    // The value of `c` rounded by MPFR at `PREC` bits in the direction `r`, or, for c π, a
    // number at `PREC` bits beyond c π in that direction.
    fn value(c: Case, r: Round) -> Float {
        let f = |x: f64| Float::with_val(53, x);
        let (v, _) = match c {
            Case::Atan(x) => Float::with_val_round(PREC, f(x).atan_ref(), r),
            Case::Atan2(y, x) => Float::with_val_round(PREC, f(y).atan2_ref(&f(x)), r),
            Case::Asin(x) => Float::with_val_round(PREC, f(x).asin_ref(), r),
            Case::Acos(x) => Float::with_val_round(PREC, f(x).acos_ref(), r),
            Case::PiMul(c) => {
                // c p for the rounding p of π in the direction r if c > 0, and in the other
                // otherwise, is beyond c π in the direction r, and so is its rounding in that
                // direction. It can be a little further than the rounding of c π, which only
                // makes the test stricter.
                let s = if (c > 0.0) == (r == Round::Down) {
                    Round::Down
                } else {
                    Round::Up
                };
                let (p, _) = Float::with_val_round(PREC, Constant::Pi, s);
                Float::with_val_round(PREC, &p * c, r)
            }
            Case::Pi => Float::with_val_round(PREC, Constant::Pi, r),
        };
        v
    }

    // `near`, the rounding of `c` to nearest by `atan.rs`, is MPFR's: that of `mpfr_atan`,
    // `mpfr_asin`, `mpfr_acos` or `mpfr_atan2`, as the parent's `check_near` and `check2_near`
    // compare them, and for c π and π, the rounding to nearest of the two bounds of `value`,
    // which have to agree, so that it is that of the number between them, as rounding to
    // nearest is monotonic.
    pub(super) fn near(c: Case, near: f64) {
        match c {
            Case::Atan(x) => check_near(ATAN, x, near),
            Case::Atan2(y, x) => check2_near(y, x, near),
            Case::Asin(x) => check_near(ASIN, x, near),
            Case::Acos(x) => check_near(ACOS, x, near),
            Case::PiMul(_) | Case::Pi => {
                let want =
                    [Round::Down, Round::Up].map(|r| value(c, r).to_f64_round(Round::Nearest));
                assert!(
                    want[0].to_bits() == want[1].to_bits() && near.to_bits() == want[0].to_bits(),
                    "{:?}: {:e} to nearest != MPFR's ({:e}, {:e})",
                    c,
                    near,
                    want[0],
                    want[1]
                );
            }
        }
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
    // value that `v` bounds below and above. Returns its width.
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
}
