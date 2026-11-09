// Tests of the exponentials and hyperbolic functions of the dyadic kernel. Every generator runs
// on every platform through `check`, which checks that the two directions give the same `f64`
// or two adjacent ones, that the rounding to nearest is one of them, and that the directions
// give the roundings that bounds on the functions determine (`known`). On 64-bit Linux and
// macOS, where the tests have MPFR, `check` also compares both directions and the rounding to
// nearest with the functions of `src/mpfr_calls/mpfr.rs` that compute the same function with
// MPFR, which they have to agree with bit for bit.

use super::*;
use crate::dyadic::tests::Rng;
use std::f64::consts::{LN_2, LOG10_2};

type Directed = fn(f64, bool) -> f64;

const EXP: usize = 0;
const EXP2: usize = 1;
const EXP10: usize = 2;
const SINH: usize = 3;
const COSH: usize = 4;
const TANH: usize = 5;

const FUNCTIONS: [(&str, Directed); 6] = [
    ("exp", exp),
    ("exp2", exp2),
    ("exp10", exp10),
    ("sinh", sinh),
    ("cosh", cosh),
    ("tanh", tanh),
];

type Near = fn(f64) -> f64;

// The functions of `FUNCTIONS` rounded to nearest, in the same order.
const NEAR: [Near; 6] = [
    exp_near, exp2_near, exp10_near, sinh_near, cosh_near, tanh_near,
];

// 1.25 * 2^-26, below which sinh, cosh and tanh are within an ulp of x or 1 (`known`).
const SMALL: f64 = 5.0 / 268_435_456.0;

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

// The roundings of the function `i` at `x` toward -∞ and toward +∞, where bounds on the
// function determine them. The thresholds are those of the bounds, not those of the rules of
// `exp.rs`, so that the evaluations give some of these roundings too.
fn known(i: usize, x: f64) -> Option<(f64, f64)> {
    let (max, inf, min) = (f64::MAX, f64::INFINITY, f64::from_bits(1));
    let t = x.abs();
    // e^y is strictly between 1 and the `f64` beside 1 on the side of y for 0 < |y| <= 2^-53,
    // as 1 + y < e^y < 1 / (1 - y) < 1 + 2 y for 0 < |y| < 1/2. 2^x = e^(x ln 2) and
    // 10^x = e^(x ln 10), where |x ln 2| < |x| and |x ln 10| < 4 |x|.
    let near_one = |y: f64| {
        if y == 0.0 {
            (1.0, 1.0)
        } else if y > 0.0 {
            (1.0, 1.0 + f64::EPSILON)
        } else {
            (1.0 - f64::EPSILON / 2.0, 1.0)
        }
    };
    let r = match i {
        EXP | EXP2 | EXP10 if x == inf => (inf, inf),
        EXP | EXP2 | EXP10 if x == -inf => (0.0, 0.0),
        // ln MAX = 709.78..., and e^x < 2^-1074 below -1074 ln 2 = -744.44...
        EXP if x > 709.79 => (max, inf),
        EXP if x < -744.45 => (0.0, min),
        EXP | EXP2 if t <= f64::EPSILON / 2.0 => near_one(x),
        EXP2 if x >= 1024.0 => (max, inf),
        EXP2 if x < -1074.0 => (0.0, min),
        EXP2 if x == x.floor() => {
            let p = pow2(x as i32);
            (p, p)
        }
        // log10 MAX = 308.25..., and 10^x < 2^-1074 below -1074 log10(2) = -323.30...
        EXP10 if x > 308.26 => (max, inf),
        EXP10 if x < -323.31 => (0.0, min),
        EXP10 if t <= f64::EPSILON / 8.0 => near_one(x),
        // 10^n for n <= 22 is an `f64`, as 5^22 < 2^53, and so is each product here.
        EXP10 if x == x.floor() && (0.0..=22.0).contains(&x) => {
            let p = (0..x as i32).fold(1.0, |p, _| p * 10.0);
            (p, p)
        }
        SINH if x == 0.0 || t == inf => (x, x),
        // asinh MAX = 710.47..., and sinh is odd.
        SINH if x > 710.48 => (max, inf),
        SINH if x < -710.48 => (-inf, -max),
        // t < sinh t < t + t^3 / 5 for 0 < t < 1, and t^3 / 5 is less than the gap from t to
        // the next `f64` for t < 1.25 * 2^-26: that gap is more than 2^-53 t, and
        // (1.25 * 2^-26)^2 / 5 < 2^-53.
        SINH if t < SMALL && x > 0.0 => (x, next_up(x)),
        SINH if t < SMALL => (next_down(x), x),
        COSH if t == inf => (inf, inf),
        COSH if t == 0.0 => (1.0, 1.0),
        COSH if t > 710.48 => (max, inf),
        // 1 < cosh t < 1 + t^2 / 2 + t^4 / 12 < 1 + 2^-52 for 0 < t < 1.25 * 2^-26.
        COSH if t < SMALL => (1.0, 1.0 + f64::EPSILON),
        TANH if x == 0.0 => (x, x),
        TANH if x == inf => (1.0, 1.0),
        TANH if x == -inf => (-1.0, -1.0),
        // 0 < 1 - tanh x = 2 / (e^2x + 1) < 2^-53 for x > 27 ln 2 = 18.71..., and tanh is odd.
        TANH if x > 18.72 => (1.0 - f64::EPSILON / 2.0, 1.0),
        TANH if x < -18.72 => (-1.0, -(1.0 - f64::EPSILON / 2.0)),
        // t - t^3 / 3 < tanh t < t for 0 < t < 1, and t^3 / 3 is less than the gap from t to
        // the `f64` before it for t < 1.25 * 2^-26. That gap is 2^-1074 for a subnormal t,
        // 2^-53 t for a normal power of 2 t, where t^2 / 3 < 2^-53 as t <= 2^-26, and
        // 2^-52 t / m for any other normal t = m 2^e with 1 < m < 2, where t^2 m / 3 < 2^-52.
        TANH if t < SMALL && x > 0.0 => (next_down(x), x),
        TANH if t < SMALL => (x, next_up(x)),
        _ => return None,
    };
    Some(r)
}

// `near`, the rounding to nearest of the number that `lo` and `hi` round, which the function `i`
// gave at `x`, is one of them, or NaN if they are. This holds for zeros too: a number of
// magnitude at most 2^-1075 rounds to nearest to the zero of its sign, which the direction
// toward 0 also gives.
fn check_near(i: usize, x: f64, lo: f64, hi: f64, near: f64) {
    let ok = if lo.is_nan() {
        near.is_nan()
    } else {
        near.to_bits() == lo.to_bits() || near.to_bits() == hi.to_bits()
    };
    assert!(
        ok,
        "{}({:e}): {:e} to nearest, outside ({:e}, {:e})",
        FUNCTIONS[i].0, x, near, lo, hi
    );
}

// Checks the function `i` at `x` in both directions and to nearest, as the header says.
fn check(i: usize, x: f64) {
    let (name, f) = FUNCTIONS[i];
    let (lo, hi) = (f(x, false), f(x, true));
    let near = NEAR[i](x);
    check_near(i, x, lo, hi, near);
    #[cfg(all(
        target_pointer_width = "64",
        any(target_os = "linux", target_os = "macos")
    ))]
    mpfr::check_near(i, x, near);
    if x.is_nan() {
        assert!(
            lo.is_nan() && hi.is_nan(),
            "{}(NaN): {:e} {:e}",
            name,
            lo,
            hi
        );
        return;
    }
    assert!(
        !lo.is_nan() && (lo.to_bits() == hi.to_bits() || next_up(lo).to_bits() == hi.to_bits()),
        "{}({:e}): {:e} and {:e} are neither equal nor adjacent",
        name,
        x,
        lo,
        hi
    );
    if let Some((l, h)) = known(i, x) {
        assert!(
            lo.to_bits() == l.to_bits() && hi.to_bits() == h.to_bits(),
            "{}({:e}): ({:e}, {:e}) != ({:e}, {:e})",
            name,
            x,
            lo,
            hi,
            l,
            h
        );
    }
    #[cfg(all(
        target_pointer_width = "64",
        any(target_os = "linux", target_os = "macos")
    ))]
    mpfr::check(i, x, lo, hi);
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

// Each rule of `exp.rs` at its threshold and the 3 `f64`s on each side of it, the thresholds of
// the bounds of `known`, where the evaluations have to give the same roundings, and the
// special values.
#[test]
fn rules_at_their_thresholds() {
    let tiny_hyp = 1.0 / 67_108_864.0;
    let thresholds: [&[f64]; 6] = [
        &[
            710.0,
            709.782712893384,
            -746.0,
            -744.4400719213812,
            -745.1332191019412,
            f64::EPSILON / 4.0,
            f64::EPSILON / 2.0,
        ],
        &[
            1024.0,
            -1075.0,
            -1074.0,
            -1022.0,
            f64::EPSILON / 4.0,
            f64::EPSILON / 2.0,
        ],
        &[
            309.0,
            308.25471555991675,
            -324.0,
            -323.3062153431158,
            f64::EPSILON / 16.0,
            f64::EPSILON / 8.0,
            1.0,
            22.0,
        ],
        &[711.0, 710.475860073944, tiny_hyp, SMALL, 1.0],
        &[711.0, 710.475860073944, tiny_hyp, SMALL],
        &[19.0, 18.714973875118524, tiny_hyp, SMALL, 1.0],
    ];
    let special = [
        0.0,
        f64::from_bits(1),
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
        for x in special {
            check(i, x);
            check(i, -x);
        }
        check(i, f64::NAN);
    }
}

// Each rule of the functions of `exp.rs` rounded to nearest at its threshold and the 3 `f64`s
// on each side of it, with both signs, and other arguments at which the rounding to nearest
// changes: -1074 and -1076 for 2^x, where 2^x is 2^-1074 and 2^-1076, below the tie 2^-1075
// between 0 and 2^-1074; the integers from 1 to 24 for 10^x, where 10^x is an `f64` up to 22,
// 10^23 is the midpoint of two `f64`s, and 10^24 is neither; and for tanh, 19, the threshold
// of its directions, and 27.5 ln 2, within an ulp of where 1 - tanh x = 2 / (e^2x + 1) is
// 2^-54, as e^(55 ln 2) = 2^55.
#[test]
fn near_rules_at_their_thresholds() {
    let thresholds: [&[f64]; 6] = [
        &[710.0, -746.0, f64::EPSILON / 4.0],
        &[1024.0, -1074.0, -1075.0, -1076.0, f64::EPSILON / 4.0],
        &[309.0, -324.0, f64::EPSILON / 16.0],
        &[711.0, TINY_NEAR, TINY_HYP],
        &[711.0, TINY_NEAR, TINY_HYP],
        &[19.0, 19.061547465398498, 20.0, TINY_NEAR],
    ];
    for (i, thresholds) in thresholds.iter().enumerate() {
        for &x in *thresholds {
            for x in around(x, 3) {
                check(i, x);
                check(i, -x);
            }
        }
    }
    for n in 1..=24 {
        for x in around(f64::from(n), 3) {
            check(EXP10, x);
            check(EXP10, -x);
        }
    }
}

// Roundings to nearest that follow without bounds: 10^n for n up to 22 is an `f64`, which
// `str::parse` gives; 10^23 is the midpoint of two `f64`s, and its tie goes to the even one,
// 0x44b5_2d02_c7e1_4af6, which `1e23` also is; 2^-1074 is an `f64`, 2^-1075 is the midpoint of
// 0 and 2^-1074, whose tie goes to 0, and 2^-1076 is below it. 1 - 2^-53 < tanh 19 < 1 - 2^-54
// and 1 - 2^-54 < tanh 20 < 1, as 1 - tanh x = 2 / (e^2x + 1) and 54 ln 2 < 38 < 55 ln 2 < 40.
#[test]
fn near_exact_values() {
    assert_eq!(exp10_near(23.0).to_bits(), 0x44b5_2d02_c7e1_4af6);
    for k in 1..=22 {
        let want: f64 = format!("1e{}", k).parse().unwrap();
        assert_eq!(
            exp10_near(f64::from(k)).to_bits(),
            want.to_bits(),
            "10^{}",
            k
        );
    }
    assert_eq!(exp2_near(-1074.0).to_bits(), 1);
    assert_eq!(exp2_near(-1075.0).to_bits(), 0);
    assert_eq!(exp2_near(-1076.0).to_bits(), 0);
    assert_eq!(tanh_near(19.0).to_bits(), next_down(1.0).to_bits());
    assert_eq!(tanh_near(20.0).to_bits(), 1f64.to_bits());
}

// The arguments at which the reductions of `exp.rs` change their k or their branch, with the 2
// `f64`s on each side of them: k ln 2 for e^x, sinh and cosh, k log10(2) for 10^x, k ln 2 / 2
// for tanh, the integers and the halves of integers for 2^x, and 1 for sinh and tanh. Each
// product is within 2 ulps of the number that it rounds.
#[test]
fn reductions_at_their_edges() {
    for k in -1076..=1024 {
        let k = f64::from(k);
        for x in around(k * LN_2, 2) {
            check(EXP, x);
        }
        for x in around(k * LOG10_2, 2) {
            check(EXP10, x);
        }
        for x in around(k, 2) {
            check(EXP2, x);
        }
        check(EXP2, k + 0.5);
    }
    for k in 0..=1025 {
        for x in around(f64::from(k) * LN_2, 2) {
            for i in [SINH, COSH] {
                check(i, x);
                check(i, -x);
            }
        }
    }
    for k in 0..=56 {
        for x in around(f64::from(k) * LN_2 / 2.0, 2) {
            check(TANH, x);
            check(TANH, -x);
        }
    }
}

// The integers, around and beyond the range in which each function neither overflows nor
// underflows. 2^n is an `f64` from -1074 to 1023 and 10^n from 0 to 22, which `known` checks.
// Beyond, 10^n has 5^|n| as its numerator or denominator, and the only lower bound on its
// distance to the nearest `f64` shrinks with 5^|n|, so these may need high levels.
#[test]
fn integers() {
    for n in -1080..=1030 {
        check(EXP2, f64::from(n));
    }
    for n in -330..=315 {
        check(EXP10, f64::from(n));
    }
    for n in -750..=715 {
        for i in [EXP, SINH, COSH, TANH] {
            check(i, f64::from(n));
        }
    }
}

// The exact enclosures of 2^n at the integers n other than 0 from -1074 to 1023, which no rule
// settles: `Exp2` gives the point 2^n there, as (n - x) ln 2 = 0 (`ev_exp2_exact`).
#[test]
fn exact_enclosures() {
    use crate::dyadic::tests::check_exact;
    for n in (-1074..=1023).filter(|&n| n != 0) {
        check_exact(&Exp2(f64::from(n)), pow2(n), &format!("exp2({})", n));
    }
}

// MPFR's results at 53 bits in its tests of e^x and 2^x, from MPFR 4.2.2's `tests/texp.c` and
// `tests/texp2.c` (as gmp-mpfr-sys 1.7.1 ships them), as "function x rounding result". `W` is
// `check_worst_case`, which checks the rounding down and that the rounding up is the next
// `f64`; `D`, `U`, `N` and `Z` are the roundings of `check3`, where `Z` is `D` as the results
// are positive. These are strings, as `clippy::excessive_precision` rejects most of them as
// literals, and `str::parse` rounds them to nearest at 53 bits, as these tests of MPFR do.
const MPFR_RESULTS: [&str; 53] = [
    // texp.c l.104-110, which l.95 calls "worst cases communicated by Jean-Michel Muller and
    // Vincent Lefevre".
    "exp 4.44089209850062517562e-16 W 1.00000000000000022204",
    "exp 6.39488462184069720009e-14 W 1.00000000000006372680",
    "exp 1.84741111297455401935e-12 W 1.00000000000184718907",
    "exp 1.76177628026265550074e-10 W 1.00000000017617751702",
    "exp 1.76177628026265550074e-10 N 1.00000000017617773906",
    "exp 7.54175277499595900852e-10 W 1.00000000075417516676",
    "exp 7.54175277499595900852e-10 N 1.00000000075417538881",
    // texp.c l.112-119.
    "exp -5.42410311287441459172e+02 N 2.7176584868845723e-236",
    "exp -1.32920285897904911589e-10 N 0.999999999867079769622",
    "exp -1.44037948245738330735e-10 N 0.9999999998559621072757",
    "exp -1.66795910430705305937e-10 Z 0.9999999998332040895832",
    "exp -1.64310953745426656203e-10 N 0.9999999998356891017792",
    "exp -1.38323574826034659172e-10 Z 0.9999999998616764251835",
    "exp -1.23621668465115401498e-10 Z 0.9999999998763783315425",
    // texp.c l.1011-1050; l.1018-1019 call 3.4657... "worst case for argument reduction, very
    // near from 5*log(2)".
    "exp 0.0 U 1.0",
    "exp -1e-170 U 1.0",
    "exp -1e-170 N 1.0",
    "exp -8.88024741073346941839e-17 U 1.0",
    "exp 8.70772839244701057915e-01 N 2.38875626491680437269",
    "exp 1.0 N 2.71828182845904509080",
    "exp -3.42135637628104173534e-07 Z 0.999999657864420798958",
    "exp 3.4657359027997265421 N 32.0",
    "exp 3.4657359027997265421 U 32.0",
    "exp 3.4657359027997265421 D 31.999999999999996447",
    "exp 2.26523754332090625496e+01 D 6.8833785261699581146e9",
    "exp 1.31478962104089092122e+01 Z 5.12930793917860137299e+05",
    "exp 4.25637507920002378103e-01 U 1.53056585656161181497e+00",
    "exp 6.26551618962329307459e-16 U 1.00000000000000066613e+00",
    "exp -3.35589513871216568383e-03 D 9.96649729583626853291e-01",
    "exp 1.95151388850007272424e+01 U 2.98756340674767792225e+08",
    "exp 2.45045953503350730784e+01 N 4.38743344916128387451e+10",
    "exp 2.58165606081678085104e+01 D 1.62925781879432281494e+11",
    "exp -2.36539020084338638128e+01 Z 5.33630792749924762447e-11",
    "exp 2.39211946135858077866e+01 U 2.44817704330214385986e+10",
    "exp -2.78190533055889162029e+01 Z 8.2858803483596879512e-13",
    "exp 2.64028186174889789584e+01 D 2.9281844652878973388e11",
    "exp 2.92086338843268329413e+01 Z 4.8433797301907177734e12",
    "exp -2.46355324071459982349e+01 Z 1.9995129297760994791e-11",
    "exp -2.23509444608605427618e+01 Z 1.9638492867489702307e-10",
    "exp -2.41175390197331687148e+01 D 3.3564940885530624592e-11",
    "exp 2.46363885231578088053e+01 U 5.0055014282693267822e10",
    "exp 111.1263531080090984914932050742208957672119140625 N 1.8262572323517295459e48",
    "exp -3.56196340354684821250e+02 N 2.0225297096141478156e-155",
    "exp 6.59678273772710895173e+02 U 3.1234469273830195529e286",
    "exp 5.13772529701934331570e+02 D 1.3445427121297197752e223",
    "exp 3.57430211008718345056e+02 D 1.6981197246857298443e155",
    "exp 3.82001814471465536371e+02 U 7.9667300591087367805e165",
    "exp 5.92396038219384422518e+02 D 1.880747529554661989e257",
    "exp -5.02678550462488090034e+02 U 4.8919201895446217839e-219",
    "exp 5.30015757134837031117e+02 D 1.5237672861171573939e230",
    "exp 5.16239362447650933063e+02 Z 1.5845518406744492105e224",
    "exp 6.00812634798592370977e-01 N 1.823600119339019443",
    // texp2.c l.339-342: -1683977482443233 / 2^41.
    "exp2 -7.6578429909351734750089235603809357e2 N 2.991959870867646566478e-231",
];

// The other arguments of MPFR's tests of these functions, from the same directory, as
// (function, x), for which these tests give no 53-bit result as a number. A decimal one is
// MPFR's string, which `str::parse` rounds to nearest at 53 bits. A binary or hex one is the
// `f64` nearest to MPFR's string, which Python's `fractions` computed, with MPFR's string in a
// comment (an exponent after `E`, `e` or `p` is of 2, and one after `@` of 16).
const MPFR_ARGUMENTS: [(usize, &str); 71] = [
    // texp.c l.122: 0.88b6ba510e10450edc258748bc9dfdd466f21b47ed264cdf24aa8f64af1f3fad9ec2301d43
    // c0743f534b5aa20091ff6d352df458ef1ba519811ef6f5b11853534fd8fa32764a0a6d2d0dd20@0 (hex).
    (EXP, "0.5340382049453761"),
    // texp.c l.149: 0.1110010100011101010000111110011E-86, with 87 zeros before the `E`.
    (EXP, "1.1567316975535585e-26"),
    // texp.c l.275: 0.1011000101110010000101111111010100001100000001110001100111001101E30.
    (EXP, "744261117.2617458"),
    // texp.c l.288: -0.1011000101110010000101111111011111010001110011110111100110101100E30,
    // and l.617: -2.c5c85fdf473de6af278ece700fcbdabd03cd0cb9ca62d8b62c@7 (hex), which round to
    // the same `f64`.
    (EXP, "-744261117.954893"),
    // texp.c l.298: -0.1011001101110010000101111111011111010001110011110111100110111101E30.
    (EXP, "-752649725.954893"),
    // texp.c l.367 and l.384: -0.1E-3 and 0.1E-3.
    (EXP, "-0.0625"),
    (EXP, "0.0625"),
    // texp.c l.401: 1.1101011000111101011110000111010010101001101001110111e28.
    (EXP, "493082503.29141945"),
    // texp.c l.427: 0.1111E4, with 103 zeros before the `E`.
    (EXP, "15"),
    // texp.c l.451: -4.28ac8fceeadcda06bb56359017b1c81b85b392e7 (hex), near -6 ln 2.
    (EXP, "-4.1588830833596715"),
    // texp.c l.465: -1E-400.
    (EXP, "-3.8725919148493183e-121"),
    // texp.c l.488: 1.0000000000001001000110100100101000001101101011100101e2.
    (EXP, "4.000555584256948"),
    // texp.c l.546, texp2.c l.158 and texp10.c l.133: i 2^(-512 |i|) for i = -1, 0, 1.
    (EXP, "-7.458340731200207e-155"),
    (EXP, "0"),
    (EXP, "7.458340731200207e-155"),
    (EXP2, "-7.458340731200207e-155"),
    (EXP2, "0"),
    (EXP2, "7.458340731200207e-155"),
    (EXP10, "-7.458340731200207e-155"),
    (EXP10, "0"),
    (EXP10, "7.458340731200207e-155"),
    // texp.c l.985, near -ln 2.
    (
        EXP,
        concat!(
            "-6.931471612838458767846632362191520641738579607794787447166215928349244597924154",
            "9847386366371775938082803907383582e-01"
        ),
    ),
    // texp2.c l.45 and texp10.c l.45: 0.101100100000000000110100E15.
    (EXP2, "22784.1015625"),
    (EXP10, "22784.1015625"),
    // texp2.c l.123, l.297, l.317, l.353 and l.368.
    (EXP2, "5"),
    (EXP2, "4"),
    (EXP2, "-4"),
    (EXP2, "-12"),
    (EXP2, "11"),
    // texp2.c l.230: -0.11011101010000110000000000000011100110010101101110111010101100001101101
    // 1001101111111110100110001110100111000111101010010100010001101100001010111101110100010000
    // 101011111001101011000011101000000001010001011110011110101010111000000E17.
    (EXP2, "-113286.00010983447"),
    // texp2.c l.409.
    (EXP2, "10000000000.5"),
    // texp2.c l.421: -1.0E-26.
    (EXP2, "-1.4901161193847656e-08"),
    // texp.c l.508 and texp10.c l.98, l.392, l.417 and l.432.
    (EXP10, "4"),
    (EXP10, "-4"),
    // texp10.c l.212-213: 0x1.34413504b3ccdbd5dd8p+28 and
    // 0x1.34413509f79fef2c4e0dd14a7ae0ecfbacdbp+60 (hex).
    (EXP10, "323228496.29389656"),
    (EXP10, "1.3882558221308393e+18"),
    // texp10.c l.288-289: -0.1001101000100000100110101000011E29 and
    // -0.100110100010000010011010100001001111101111001111111101111001101E61.
    (EXP10, "-323228496.75"),
    (EXP10, "-1.3882558221308393e+18"),
    // texp10.c l.475.
    (EXP10, "3010299957"),
    // tsinh.c l.49 and ttanh.c l.49: -0.1001011001.
    (SINH, "-0.5869140625"),
    (TANH, "-0.5869140625"),
    // tsinh.c l.55: 1E-6.
    (SINH, "0.015625"),
    // tsinh.c l.106 and l.116.
    (SINH, "3196577161300663915"),
    (SINH, "3196577161300663914.5"),
    // tcosh.c l.63.
    (COSH, "0"),
    // tcosh.c l.81 and l.90: 0.1101110111111111001011101000101 and
    // -0.1110111000011101010111100000101E-1.
    (COSH, "0.867175015155226"),
    (COSH, "-0.4650678050238639"),
    // tcosh.c l.151 and l.160, and ttanh.c l.72: 0.101100100000000000110100E7 and E8.
    (COSH, "89.00039672851562"),
    (COSH, "178.00079345703125"),
    (TANH, "89.00039672851562"),
    // ttanh.c l.128: -8.17cd20bfc17ae00935dc3abad8e17ab43d3ef7740c320798eefb93191f4a62dba9a2d
    // aa5efb6eace21130abd87e3ee2eadd2ad8ddae883d2f2db5dee1ac7ce3c59d16eca09e2ca3f21dc2a0386c037a
    // 0d3972e62d5b6e82446032020705553c566b1df24f40@-1 (hex).
    (TANH, "-0.5058108596095667"),
    // tsinh_cosh.c l.111-120, for sinh and cosh: x = FEDCBA987654321p-48 (hex) rounded to 53
    // bits, then 10 times x = (i - x) / 4 for i = 0, ..., 9, with the difference rounded down.
    (SINH, "-1019.4488888888889"),
    (SINH, "255.11222222222221"),
    (SINH, "-63.278055555555554"),
    (SINH, "16.56951388888889"),
    (SINH, "-3.142378472222222"),
    (SINH, "2.0355946180555553"),
    (SINH, "0.9911013454861112"),
    (SINH, "1.5022246636284722"),
    (SINH, "1.624443834092882"),
    (SINH, "1.8438890414767795"),
    (COSH, "-1019.4488888888889"),
    (COSH, "255.11222222222221"),
    (COSH, "-63.278055555555554"),
    (COSH, "16.56951388888889"),
    (COSH, "-3.142378472222222"),
    (COSH, "2.0355946180555553"),
    (COSH, "0.9911013454861112"),
    (COSH, "1.5022246636284722"),
    (COSH, "1.624443834092882"),
    (COSH, "1.8438890414767795"),
];

#[test]
fn mpfr_test_cases() {
    for case in MPFR_RESULTS {
        let v: Vec<&str> = case.split(' ').collect();
        let (i, x, rnd, want) = (index(v[0]), v[1].parse().unwrap(), v[2], v[3]);
        let want: f64 = want.parse().unwrap();
        check(i, x);
        let (lo, hi) = (FUNCTIONS[i].1(x, false), FUNCTIONS[i].1(x, true));
        let ok = match rnd {
            "W" => lo == want && hi == next_up(want),
            "D" | "Z" => lo == want,
            "U" => hi == want,
            "N" => lo == want || hi == want,
            _ => panic!("{}: no rounding {}", case, rnd),
        };
        assert!(
            ok,
            "{}: ({:e}, {:e}), MPFR's tests {:e}",
            case, lo, hi, want
        );
    }
    for (i, x) in MPFR_ARGUMENTS {
        check(i, x.parse().unwrap());
    }
}

// Arguments whose results are close above an `f64`, so that `ziv` may need more than one level
// for them, with the roundings that follow. For 0 < |y| < 1/2, e^y = 1 + y + d with
// 0 < d < y^2. For y = m 2^-52 and y = -m 2^-53 with 0 < m <= 64, 1 + y is an `f64` and
// d < 2^-92, less than the gap from 1 + y to the next `f64` up. For 0 < |y| < 1,
// cosh y = 1 + y^2 / 2 + d with 0 < d < y^4 / 12. For y = ±m 2^-26 with 0 < m <= 64,
// y^2 / 2 = m^2 2^-53 and d < 2^-80, so cosh y is between 1 + floor(m^2 / 2) 2^-52 and the next
// `f64` up, and close above the first for even m: 1 + 2^-51 for cosh(2^-25). `integers` has
// 10^n for n from 23 to 308.
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
    let ulp = f64::EPSILON;
    for m in 1..=64 {
        let k = f64::from(m);
        expect(EXP, k * ulp, 1.0 + k * ulp, 1.0 + (k + 1.0) * ulp);
        expect(
            EXP,
            -k * ulp / 2.0,
            1.0 - k * ulp / 2.0,
            1.0 - (k - 1.0) * ulp / 2.0,
        );
        let x = k / 67_108_864.0;
        let lo = 1.0 + f64::from(m * m / 2) * ulp;
        expect(COSH, x, lo, lo + ulp);
        expect(COSH, -x, lo, lo + ulp);
    }
}

#[test]
fn random_arguments() {
    let mut rng = Rng(63);
    for i in 0..FUNCTIONS.len() {
        for _ in 0..2000 {
            // Uniform in [-800, 800], and of any exponent in [-60, 10].
            let x = (rng.below(1 << 53) as f64 / (1u64 << 52) as f64 - 1.0) * 800.0;
            check(i, x);
            let e = rng.below(71) as i32 - 60;
            let m = 1.0 + rng.below(1 << 52) as f64 / (1u64 << 52) as f64;
            let s = if rng.below(2) == 0 { -1.0 } else { 1.0 };
            check(i, s * m * 2f64.powi(e));
        }
    }
}

#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
mod mpfr {
    use super::*;
    use crate::mpfr_calls::mpfr::*;

    type Mpfr = fn(f64) -> f64;

    const MPFR: [(Mpfr, Mpfr); 6] = [
        (exp_rd, exp_ru),
        (exp2_rd, exp2_ru),
        (exp10_rd, exp10_ru),
        (sinh_rd, sinh_ru),
        (cosh_rd, cosh_ru),
        (tanh_rd, tanh_ru),
    ];

    // `lo` and `hi`, which the function `i` gave at `x`, are MPFR's roundings.
    pub(super) fn check(i: usize, x: f64, lo: f64, hi: f64) {
        let (want_lo, want_hi) = (MPFR[i].0(x), MPFR[i].1(x));
        assert!(
            lo.to_bits() == want_lo.to_bits() && hi.to_bits() == want_hi.to_bits(),
            "{}({:e}): ({:e}, {:e}) != MPFR's ({:e}, {:e})",
            FUNCTIONS[i].0,
            x,
            lo,
            hi,
            want_lo,
            want_hi
        );
    }

    // MPFR's roundings to nearest, once and with IEEE subnormals, in the order of `FUNCTIONS`.
    const MPFR_NEAR: [Mpfr; 6] = [exp_rn, exp2_rn, exp10_rn, sinh_rn, cosh_rn, tanh_rn];

    // `near`, which the function `i` gave at `x` rounded to nearest, is MPFR's rounding to
    // nearest, or NaN if MPFR's is.
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
}

mod levels;
