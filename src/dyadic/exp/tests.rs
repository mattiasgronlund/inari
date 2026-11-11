// Tests of the exponentials and hyperbolic functions of the dyadic kernel. Every generator runs
// on every platform through `check`, which checks that the two directions give the same `f64`
// or two adjacent ones, that the rounding to nearest is one of them, and that the directions
// give the roundings that bounds on the functions determine (`known`). On 64-bit Linux and
// macOS, where the tests have MPFR, `check` also compares both directions and the rounding to
// nearest with the functions of `src/mpfr_calls/mpfr.rs` that compute the same function with
// MPFR, which they have to agree with bit for bit.

use super::*;
use crate::dyadic::tests::Rng;
use std::f64::consts::{LN_10, LN_2, LOG10_2};

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

// Every function of `FUNCTIONS` gives the same `f64`s, in both directions and to nearest, with
// the fast paths as with them disabled, on random arguments uniform in [-a, a), and most of
// their rounding tests pass. a is beyond the range of the fast path: 800 for e^x, 2^x and 10^x,
// 712 for sinh and cosh, whose fast paths stop near 710.48, and 21 for tanh, whose rules settle
// |x| >= 20.
#[test]
fn fast_path_agrees_with_kernel() {
    let mut rng = Rng(87);
    for (i, a) in [
        (EXP, 800.0),
        (EXP2, 800.0),
        (EXP10, 800.0),
        (SINH, 712.0),
        (COSH, 712.0),
        (TANH, 21.0),
    ] {
        crate::dyadic::fast::reset_fast_counts();
        for _ in 0..2000 {
            let x = (rng.below(1 << 53) as f64 / (1u64 << 52) as f64 - 1.0) * a;
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
        }
        let (passed, failed) = crate::dyadic::fast::fast_counts();
        assert!(
            passed > 100 * failed,
            "{}: {passed} passed, {failed} failed",
            FUNCTIONS[i].0
        );
    }
}

// c in z = x c, the argument of e^z that the fast path computes, for exp, exp2 and exp10 in the
// order of `FUNCTIONS`. The fast path takes z in [-707, 709].
const SCALES: [f64; 3] = [1.0, LN_2, LN_10];

// (h, l, e) of the fast path of exp, exp2 or exp10 (the function `i`) at `x`, as the function
// computes them, or `None` out of the range of the fast path.
fn fast_parts(i: usize, x: f64) -> Option<(f64, f64, i64)> {
    match i {
        EXP => fast_exp(x, 0.0),
        EXP2 => fast_exp_by(x, LN2),
        EXP10 => fast_exp_by(x, LN10),
        _ => unreachable!(),
    }
}

// (h, l, e) of the fast path of exp, exp2 or exp10 (the function `i`) at an `x` beyond the
// range of `fast_parts`, from `fast_exp_edge`, as the function computes them.
fn edge_parts(i: usize, x: f64) -> Option<(f64, f64, i64)> {
    match i {
        EXP => fast_exp_edge(x, 0.0),
        EXP2 => fast_exp_by_edge(x, LN2),
        EXP10 => fast_exp_by_edge(x, LN10),
        _ => unreachable!(),
    }
}

// A random `f64` in [a, b].
fn uniform(rng: &mut Rng, a: f64, b: f64) -> f64 {
    a + (b - a) * (rng.below(1 << 53) as f64 / (1u64 << 53) as f64)
}

// A random `f64` of either sign, with an exponent in [lo, hi] and a random significand.
fn log_uniform(rng: &mut Rng, lo: i32, hi: i32) -> f64 {
    let e = lo + rng.below((hi - lo + 1) as u64) as i32;
    let m = 1.0 + rng.below(1 << 52) as f64 / (1u64 << 52) as f64;
    let s = if rng.below(2) == 0 { -1.0 } else { 1.0 };
    s * m * pow2(e)
}

// e^x, 2^x and 10^x on random arguments of the fast path: uniform over its range, and of any
// exponent from -56 to 9, where z is small or out of the range. Most of its rounding tests pass.
#[test]
fn fast_range_random() {
    let mut rng = Rng(871);
    for i in [EXP, EXP2, EXP10] {
        let c = SCALES[i];
        crate::dyadic::fast::reset_fast_counts();
        for _ in 0..2000 {
            check(i, uniform(&mut rng, -707.0 / c, 709.0 / c));
        }
        let (passed, failed) = crate::dyadic::fast::fast_counts();
        crate::dyadic::fast::reset_fast_counts();
        for _ in 0..2000 {
            check(i, log_uniform(&mut rng, -56, 9));
        }
        let (small_passed, small_failed) = crate::dyadic::fast::fast_counts();
        assert!(
            passed > 100 * failed && small_passed > 100 * small_failed,
            "{}: {passed} passed, {failed} failed on uniform arguments, {small_passed} passed, \
             {small_failed} failed on the others",
            FUNCTIONS[i].0
        );
    }
}

// e^x, 2^x and 10^x where x / c, for c = ln 2 / 4096, 1/4096 and log10(2) / 4096, is next to
// k = 4096 e + o, at which the indices of the tables wrap (o = -1 and 0, i = 63 and 0, and
// o = 63 and 64, i = 63 and 0 with j = 0 and 1), and next to k + 1/2, where the reduction
// rounds x / c to the other integer and |r| is at its largest.
#[test]
fn table_and_reduction_edges() {
    for (i, c) in [(EXP, LN_2), (EXP2, 1.0), (EXP10, LOG10_2)] {
        let c = c / 4096.0;
        for e in -1020..=1022 {
            for o in [-1, 0, 63, 64] {
                for d in [0.0, 0.5] {
                    for x in around((f64::from(4096 * e + o) + d) * c, 2) {
                        check(i, x);
                    }
                }
            }
        }
    }
}

// e^x, 2^x and 10^x around the ends of the range of the fast path, z = 709 and z = -707, where
// it gives way to the kernel: around each end, it takes some of the arguments and leaves
// others.
#[test]
fn range_ends() {
    for i in [EXP, EXP2, EXP10] {
        for end in [709.0, -707.0] {
            let (mut taken, mut left) = (0, 0);
            for x in around(end / SCALES[i], 4) {
                check(i, x);
                if fast_parts(i, x).is_some() {
                    taken += 1;
                } else {
                    left += 1;
                }
            }
            assert!(
                taken > 0 && left > 0,
                "{}: around z = {end}, the fast path takes {taken} arguments and leaves {left}",
                FUNCTIONS[i].0
            );
        }
    }
}

// Asserts that the function `i` gives the same `f64`s at `x`, in both directions and to
// nearest, with the fast paths as with them disabled.
fn same_without_fast_path(i: usize, x: f64) {
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
}

// e^x, 2^x, 10^x, sinh and cosh on random arguments beyond the range of `fast_exp`, which
// `fast_exp_edge` covers: results below about 2^-1020, subnormal ones included, and above
// about 2^1022.87. Most of the rounding tests pass, and the results are the same with the fast
// paths disabled. 2^x also at the integers from -1076 to -1019 and from 1022 to 1024, where it
// is a power of 2, a subnormal `f64` from -1074 to -1023, and at the `f64`s next to them.
#[test]
fn edges_random() {
    let mut rng = Rng(931);
    for (i, a, b) in [
        (EXP, -745.9, -707.0),
        (EXP, 709.0, 709.78),
        (EXP2, -1075.0, -1020.0),
        (EXP2, 1022.87, 1023.99),
        (EXP10, -323.9, -307.05),
        (EXP10, 307.92, 308.25),
        (SINH, 709.0, 710.47),
        (SINH, -710.47, -709.0),
        (COSH, 709.0, 710.47),
    ] {
        crate::dyadic::fast::reset_fast_counts();
        for _ in 0..2000 {
            let x = uniform(&mut rng, a, b);
            check(i, x);
            same_without_fast_path(i, x);
        }
        let (passed, failed) = crate::dyadic::fast::fast_counts();
        assert!(
            passed > 100 * failed,
            "{} on [{a}, {b}]: {passed} passed, {failed} failed",
            FUNCTIONS[i].0
        );
    }
    for n in (-1076..=-1019).chain(1022..=1024) {
        for x in around(f64::from(n), 2) {
            check(EXP2, x);
            same_without_fast_path(EXP2, x);
        }
    }
}

// e^x, 2^x, 10^x, sinh and cosh at the edges that `fast_exp_edge` and the tests of
// `round_dir_wide` and `round_near_wide` meet, and at the 4 `f64`s on each side of each: where
// the result crosses 2^-1022, 2^-1074, 2^-1075 and 2^1024, at the rules' thresholds next to
// them, at the ends -707 and 709 of the range of `fast_exp`, and, for sinh and cosh, at 709,
// 1025 ln 2 and the rule at 711. 1025 ln 2 - ln 2 / 8192 and the like are where the results
// below 2^1024 that go to the kernel start, as there the exponent of `fast_exp_edge` is 1024
// (1025 for sinh and cosh). The results are the same with the fast paths disabled.
#[test]
fn edge_points() {
    let mut points = vec![];
    for (i, c) in [(EXP, LN_2), (EXP2, 1.0), (EXP10, LOG10_2)] {
        for n in [-1022.0, -1074.0, -1075.0, 1024.0 - 1.0 / 8192.0, 1024.0] {
            points.push((i, n * c));
        }
        let z = SCALES[i];
        points.push((i, -707.0 / z));
        points.push((i, 709.0 / z));
    }
    points.extend([
        (EXP, -746.0),
        (EXP, 710.0),
        (EXP2, -1076.0),
        (EXP10, -324.0),
        (EXP10, 309.0),
    ]);
    for i in [SINH, COSH] {
        for t in [709.0, 1025.0 * LN_2 - LN_2 / 8192.0, 1025.0 * LN_2, 711.0] {
            points.push((i, t));
            points.push((i, -t));
        }
    }
    for (i, x) in points {
        for x in around(x, 4) {
            check(i, x);
            same_without_fast_path(i, x);
        }
    }
}

// 2^-68, the bound on |y - (h + l)| that the rounding tests of `src/dyadic/fast.rs` assume, and
// 2^-58, 2^10 times as large.
const FAST_ERR: f64 = 1.0 / 295_147_905_179_352_825_856.0;
const WIDE: f64 = 1.0 / 288_230_376_151_711_744.0;

// e^x, 2^x and 10^x where a rounding test of the fast path passes, but would fail with `WIDE`
// in place of the bound 2^-68: h + l is within 2^-58 of h, which a directed rounding cannot
// cross, or of a midpoint between h and the next `f64`, which the rounding to nearest cannot
// cross. There an error in the bound would show first, so the fast path has to give the same
// `f64`s as the kernel, and as MPFR. About 1 random argument in 16 is such a narrow pass.
#[test]
fn widened() {
    let mut rng = Rng(872);
    for i in [EXP, EXP2, EXP10] {
        let c = SCALES[i];
        let (mut dir, mut near) = (0, 0);
        for _ in 0..4000 {
            let x = uniform(&mut rng, -707.0 / c, 709.0 / c);
            let Some((h, l, _)) = fast_parts(i, x) else {
                continue;
            };
            let (narrow_dir, narrow_near) = narrow(h, l);
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

// Whether a directed test of `round_dir` and the test of `round_near` pass narrowly at (h, l),
// as `widened` says.
fn narrow(h: f64, l: f64) -> (bool, bool) {
    // Half the gap between h and the next `f64` above it, and below it.
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
    (
        FAST_ERR < l.abs() && l.abs() <= WIDE,
        l < above - FAST_ERR
            && l > -(below - FAST_ERR)
            && (l >= above - WIDE || l <= -(below - WIDE)),
    )
}

// `widened` beyond the range of `fast_exp`, on the ranges of e^x, 2^x and 10^x of
// `edges_random`. Where `round_dir_wide` and `round_near_wide` round C + y on the grid of the
// `f64`s in [C, 2C] (`round_dir_sub` and `round_near_sub`), with s + t = C + h, they compare
// |u| for u = RN(t + l) with 2^-67 C in the directions, and with 2^-53 C, half the gap at s,
// less 2^-67 C to nearest, where the result is s; `far_side_ties_random` checks the passes of
// the far arms, beyond 2^-53 C + 2^-67 C, on the same ranges. A pass there is narrow where
// 2^-57 C, 2^10 times as much, in place of 2^-67 C would make it fail. Elsewhere, narrow is as
// in `widened`. About 1 random argument
// in 8 is such a narrow pass on the ranges of the results below 2^-1020, and 1 in 16 on the
// others.
#[test]
fn edges_widened() {
    let mut rng = Rng(933);
    for (i, a, b) in [
        (EXP, -745.9, -707.0),
        (EXP, 709.0, 709.78),
        (EXP2, -1075.0, -1020.0),
        (EXP2, 1022.87, 1023.99),
        (EXP10, -323.9, -307.05),
        (EXP10, 307.92, 308.25),
    ] {
        let (mut dir, mut near) = (0, 0);
        for _ in 0..4000 {
            let x = uniform(&mut rng, a, b);
            if fast_parts(i, x).is_some() {
                continue;
            }
            let Some((h, l, e)) = edge_parts(i, x) else {
                continue;
            };
            let (narrow_dir, narrow_near) = if e < -1022 || (e == -1022 && h <= 1.0) {
                let c = pow2(-1022 - i32::try_from(e).unwrap());
                let (s, t) = fast_two_sum(c, h);
                let u = (t + l).abs();
                // 2^-67 C, 2^-57 C and 2^-53 C.
                let (err, wide, half) =
                    (2.0 * FAST_ERR * c, 2.0 * WIDE * c, f64::EPSILON / 2.0 * c);
                (
                    s < 2.0 * c && err < u && u <= wide,
                    s < 2.0 * c && u < half - err && u >= half - wide,
                )
            } else {
                narrow(h, l)
            };
            if !narrow_dir && !narrow_near {
                continue;
            }
            dir += usize::from(narrow_dir);
            near += usize::from(narrow_near);
            same_without_fast_path(i, x);
            check(i, x);
        }
        assert!(
            dir >= 20 && near >= 20,
            "{} on [{a}, {b}]: {dir} narrow passes of the directed tests and {near} of the test \
             to nearest",
            FUNCTIONS[i].0
        );
    }
}

// u / C at (h, l, e) where `round_near_wide` rounds with `round_near_sub` and C + h is a
// midpoint of two `f64`s of [C, 2C) below 2C: |t| = 2^-53 C for (s, t) = Fast2Sum(C, h), with
// s < 2C, and u = RN(t + l). `None` elsewhere. The quotient is exact, as C is a power of 2.
fn sub_tie(h: f64, l: f64, e: i64) -> Option<f64> {
    if e > -1022 || (e == -1022 && h > 1.0) {
        return None;
    }
    let c = pow2(-1022 - i32::try_from(e).unwrap());
    let (s, t) = fast_two_sum(c, h);
    (s < 2.0 * c && t.abs() == f64::EPSILON / 2.0 * c).then_some((t + l) / c)
}

// 2^-53 + 2^-67, exact: the far bound of `round_near_sub` on u, in units of C.
const TIE_FAR: f64 = f64::EPSILON / 2.0 + 2.0 * FAST_ERR;

// The arguments of the `lo` sets of the counts of exp, exp2 and exp10 (row 93) at which the
// test to nearest of the fast path failed before `round_near_sub` had its far arms, as
// (function, x, MPFR's rounding to nearest), in bits. The kernel gave the right results there,
// so these cost only time: they were not mismatches, and are not in `regressions()`.
const FAR_SIDE_TIES: [(usize, u64, u64); 91] = [
    (EXP, 0xc086_28ac_869e_da32, 0x0008_0aef_0d9d_fc43),
    (EXP, 0xc086_2a64_a2ec_7c1f, 0x0006_7cc9_0738_4e1b),
    (EXP, 0xc086_25fb_9296_5b44, 0x000b_424e_c0b9_0507),
    (EXP, 0xc086_28ce_7f59_f01e, 0x0007_e910_01f8_b43d),
    (EXP, 0xc086_2f78_e1f3_7d70, 0x0003_7035_a3c2_02ef),
    (EXP, 0xc086_257e_3111_cf1d, 0x000b_f847_7d86_5231),
    (EXP, 0xc086_334b_e345_82db, 0x0002_21bb_afb0_7203),
    (EXP, 0xc086_3091_b55c_7f56, 0x0002_ff6c_422c_3391),
    (EXP, 0xc086_2ba1_2303_ade0, 0x0005_8ef9_74a4_87b7),
    (EXP, 0xc086_2467_be9a_9d08, 0x000d_b68c_f6d4_e1a1),
    (EXP, 0xc086_286d_9ed5_440a, 0x0008_4b28_04df_6ab5),
    (EXP, 0xc086_2c5a_e1c4_0a23, 0x0005_1398_976a_de5f),
    (EXP, 0xc086_26ad_7f3e_13f6, 0x000a_5278_4ed3_fb2d),
    (EXP, 0xc086_2b12_00b6_cdc4, 0x0005_f5fb_ba2f_049b),
    (EXP, 0xc086_2447_3091_f46a, 0x000d_eecc_c724_18bd),
    (EXP, 0xc086_27fa_5058_6899, 0x0008_c61f_a08f_cccf),
    (EXP, 0xc086_2618_0eeb_b603, 0x000b_1a7e_bca9_96a7),
    (EXP, 0xc086_2468_66d1_adef, 0x000d_b56c_aab7_c8df),
    (EXP, 0xc086_39b3_068f_87f2, 0x0000_f520_1904_28e9),
    (EXP, 0xc086_25b2_ab37_28a2, 0x000b_aac2_4179_17c3),
    (EXP, 0xc086_29cc_dd87_219e, 0x0006_fc89_43b9_7863),
    (EXP, 0xc086_287a_5ae2_5b51, 0x0008_3dfe_d176_44e3),
    (EXP, 0xc086_3147_b3af_13d1, 0x0002_be2b_3ebb_eca5),
    (EXP, 0xc086_2896_a4d3_0e43, 0x0008_210c_f318_e397),
    (EXP, 0xc086_2548_f2e9_0b75, 0x000c_48fc_c060_cc33),
    (EXP, 0xc086_2b9b_f976_f5c3, 0x0005_9290_d794_65cb),
    (EXP, 0xc086_2a93_0d75_0fa8, 0x0006_5791_7f02_934f),
    (EXP, 0xc086_2785_6bf1_fdea, 0x0009_4a0d_9774_e427),
    (EXP, 0xc086_276d_64f1_e634, 0x0009_661d_f0d7_8b49),
    (EXP, 0xc086_2be6_7382_8794, 0x0005_5f9e_ad2b_31af),
    (EXP2, 0xc08f_fa87_e56f_29df, 0x0006_6cbd_9d0b_6f85),
    (EXP2, 0xc08f_ffdd_4452_7a8a, 0x0004_0c1b_ce07_eb05),
    (EXP2, 0xc090_104b_d194_ed5f, 0x0000_3ccc_5b4b_adaf),
    (EXP2, 0xc08f_f09e_5271_9b29, 0x000f_2a4b_b6da_668f),
    (EXP2, 0xc090_08d3_038a_182d, 0x0000_ddec_ef50_6a2d),
    (EXP2, 0xc08f_f940_f406_ca3a, 0x0007_2d30_74bf_35ed),
    (EXP2, 0xc090_01b8_3e74_1ff3, 0x0002_f81d_7d35_920f),
    (EXP2, 0xc08f_f2df_66f8_f434, 0x000c_797c_ae24_b60b),
    (EXP2, 0xc090_0174_bc0e_4070, 0x0003_1ba7_fccf_0f89),
    (EXP2, 0xc08f_f678_cdf8_f1ba, 0x0009_21ec_fd18_4fc9),
    (EXP2, 0xc08f_f7b2_5438_85dd, 0x0008_368d_2344_6359),
    (EXP2, 0xc08f_f0f9_8564_58dd, 0x000e_b44b_3ad4_de5d),
    (EXP2, 0xc08f_fefe_0d82_9d1a, 0x0004_5d6a_855f_60a7),
    (EXP2, 0xc08f_f4b7_a0ea_11c4, 0x000a_a1c9_109f_e181),
    (EXP2, 0xc08f_f1b5_d7d1_4121, 0x000d_cbda_49c2_5ba9),
    (EXP2, 0xc08f_f4c9_6fd6_0fe9, 0x000a_916e_0f8b_2797),
    (EXP2, 0xc08f_f2af_6d6c_579a, 0x000c_adc3_66cd_5d13),
    (EXP2, 0xc090_00ca_4b60_1418, 0x0003_7cf4_fbc9_bf5d),
    (EXP2, 0xc090_015c_7418_62ea, 0x0003_28d7_72d4_8eb7),
    (EXP2, 0xc08f_f454_6298_f2ef, 0x000a_fec2_9df6_181d),
    (EXP2, 0xc090_0027_de3e_2642, 0x0003_e4bc_2d40_23b1),
    (EXP2, 0xc08f_f33e_abcf_f37e, 0x000c_1428_bd9a_159f),
    (EXP2, 0xc08f_f5c4_b887_6132, 0x0009_b4da_6c11_8843),
    (EXP2, 0xc08f_fb6c_3eab_39f9, 0x0005_f26a_4644_a88b),
    (EXP2, 0xc08f_f138_5d49_39e5, 0x000e_6513_3c50_fed3),
    (EXP2, 0xc090_0ce7_4074_408f, 0x0000_6d73_fa4d_a9d1),
    (EXP2, 0xc08f_f70f_93c7_f049, 0x0008_ad9d_c1bb_2d41),
    (EXP2, 0xc08f_fc19_7ec3_0e48, 0x0005_9bb6_6808_8e7f),
    (EXP2, 0xc08f_f3ae_17bc_ef88, 0x000b_a1b9_0f46_89e9),
    (EXP2, 0xc08f_f606_7dd0_f6e3, 0x0009_7e26_b221_a157),
    (EXP2, 0xc08f_f329_a4be_5387, 0x000c_2a3e_7394_11c1),
    (EXP2, 0xc090_0e43_16b0_a67b, 0x0000_567d_c859_e65f),
    (EXP2, 0xc08f_f555_2805_3ee0, 0x000a_1479_0f8f_8b4d),
    (EXP2, 0xc08f_f6a8_a2b2_5b78, 0x0008_fc62_130d_8a91),
    (EXP10, 0xc073_3b0b_6981_45c6, 0x000e_ac08_5811_d1db),
    (EXP10, 0xc073_3cc7_d2da_7062, 0x000b_6db4_546e_b443),
    (EXP10, 0xc073_3cac_7223_9d0d, 0x000b_9b14_b5e6_0b8d),
    (EXP10, 0xc073_3c2e_77f6_86e4, 0x000c_751e_4ef0_4d7b),
    (EXP10, 0xc073_4084_2bd3_07d6, 0x0006_ad05_2288_1a43),
    (EXP10, 0xc073_3c95_e75d_f6b0, 0x000b_c0f8_6bbc_cb9b),
    (EXP10, 0xc073_3ea9_8591_59ee, 0x0008_b7a9_68c4_fa6d),
    (EXP10, 0xc073_4196_9a01_70ac, 0x0005_b8b2_3972_de23),
    (EXP10, 0xc073_430b_d537_3ce3, 0x0004_a37b_1bf6_07b5),
    (EXP10, 0xc073_3eda_f0b8_64c9, 0x0008_7a84_7ad2_599b),
    (EXP10, 0xc073_40e4_7000_cb88, 0x0006_52fd_e446_4b93),
    (EXP10, 0xc073_3db8_cb92_3c19, 0x0009_fb0c_f26e_8b01),
    (EXP10, 0xc073_3d96_557b_aaae, 0x000a_2d07_f130_8337),
    (EXP10, 0xc073_424a_84ba_1816, 0x0005_2bcc_ebd2_498d),
    (EXP10, 0xc073_3e20_a698_20fd, 0x0009_6a26_7ee8_6755),
    (EXP10, 0xc073_4b95_d4f8_9621, 0x0001_5b7c_094f_893b),
    (EXP10, 0xc073_41a4_7be1_4bce, 0x0005_ad4f_6755_4575),
    (EXP10, 0xc073_3e28_5652_6d82, 0x0009_5fc2_37df_3341),
    (EXP10, 0xc073_3d7b_a947_b046, 0x000a_5462_b5ee_0f47),
    (EXP10, 0xc073_3d16_8e89_f0f8, 0x000a_ef09_388d_05a9),
    (EXP10, 0xc073_4823_971d_2085, 0x0002_3a97_d274_9ddf),
    (EXP10, 0xc073_3d15_39a1_70bc, 0x000a_f121_d672_8e93),
    (EXP10, 0xc073_466c_5bf6_36d1, 0x0002_da66_574b_5865),
    (EXP10, 0xc073_4053_2545_6ae5, 0x0006_dcc6_902d_ea0d),
    (EXP10, 0xc073_3c9f_2a68_67dd, 0x000b_b158_367f_3fc1),
    (EXP10, 0xc073_3cb6_ab6b_47e1, 0x000b_8a0d_d997_3971),
    (EXP10, 0xc073_47ba_0716_d54d, 0x0002_5d7a_7363_8cdf),
];

// e^x, 2^x and 10^x at `FAR_SIDE_TIES`, beyond the range of `fast_exp`, where C + h is a
// midpoint and |u| > 2^-53 C + 2^-67 C (`sub_tie`): the test to nearest of the fast path passes
// in a far arm of `round_near_sub`, gives MPFR's result, and the same `f64`s as with the fast
// paths disabled.
#[test]
fn far_side_ties() {
    use crate::dyadic::fast::{fast_counts, reset_fast_counts};
    for (i, x, r) in FAR_SIDE_TIES {
        let x = f64::from_bits(x);
        let name = FUNCTIONS[i].0;
        reset_fast_counts();
        let near = NEAR[i](x);
        assert_eq!(fast_counts(), (1, 0), "{name}({x:e})");
        assert_eq!(near.to_bits(), r, "{name}({x:e}) = {near:e}");
        assert!(fast_parts(i, x).is_none(), "{name}({x:e})");
        let (h, l, e) = edge_parts(i, x).unwrap();
        let u = sub_tie(h, l, e);
        assert!(
            matches!(u, Some(u) if u.abs() > TIE_FAR),
            "{name}({x:e}): ({h:e}, {l:e}, {e}), u = {u:?} C"
        );
        same_without_fast_path(i, x);
        check(i, x);
    }
}

// `far_side_ties` at random arguments beyond the range of `fast_exp`, on the three low ranges
// of `edges_widened`. Of 4000 arguments of each function, 28 (exp), 38 (exp2) and
// 35 (exp10) are such ties, about 1 in 105-143; the test asks for at least 14, 19 and 17, about
// half as many.
#[test]
fn far_side_ties_random() {
    use crate::dyadic::fast::{fast_counts, reset_fast_counts};
    let mut rng = Rng(934);
    for (i, a, b, min) in [
        (EXP, -745.9, -707.0, 14),
        (EXP2, -1075.0, -1020.0, 19),
        (EXP10, -323.9, -307.05, 17),
    ] {
        let mut found = 0;
        for _ in 0..4000 {
            let x = uniform(&mut rng, a, b);
            if fast_parts(i, x).is_some() {
                continue;
            }
            let Some((h, l, e)) = edge_parts(i, x) else {
                continue;
            };
            if !matches!(sub_tie(h, l, e), Some(u) if u.abs() > TIE_FAR) {
                continue;
            }
            found += 1;
            reset_fast_counts();
            NEAR[i](x);
            assert_eq!(fast_counts(), (1, 0), "{}({x:e})", FUNCTIONS[i].0);
            same_without_fast_path(i, x);
            check(i, x);
        }
        assert!(
            found >= min,
            "{}: {found} ties beyond 2^-53 C + 2^-67 C",
            FUNCTIONS[i].0
        );
    }
}

// `round_near_wide` at constructed ties of `round_near_sub`: for C = 2^(-1022 - e),
// g = 2^-52 C and h = (m + 1/2) g, C + h is the midpoint of C + m g and C + (m + 1) g, which
// Fast2Sum rounds to the even one, so that t = g/2 for an even m and -g/2 for an odd one. The
// l satisfy h = RN(h + l), as the pairs of the fast paths do, so |l| <= ulp(h)/2 < g/2, and
// y = h + l gives y 2^e = (m + 1/2 + l/g) 2^-1074, which rounds to (m + 1) 2^-1074 where l > 0
// and to m 2^-1074 where l < 0, whichever s is. Except at m = 2^52 - 1, the fast path gives
// that result where u is one ulp beyond the far bound 2^-53 C + 2^-67 C (a far arm) or below
// the near bound 2^-53 C - 2^-67 C (s). It fails where u is at a bound, as the comparisons are
// strict, and between them, as at l = 0. An m >= 2^39 makes ulp(h)/2 >= 2^-66 C, above the |l|
// of at most 2^-67 C + 2^-105 C that the test takes. Not every h is in (1/2, 2), the range of
// the fast paths, which this arithmetic does not need: those in it are at m >= 2^51 for
// e = -1022, m >= 2^50 for e = -1023 and m in [2^43, 2^45) for e = -1030. At m = 2^52 - 1,
// Fast2Sum rounds C + h = 2C - g/2 to s = 2C, and the fast path fails for every l. It also
// fails at every tie where C >= 2^14 and h < 2: there |l| <= ulp(h)/2 <= 2^-53 <= 2^-67 C, so u
// is neither beyond the far bound nor below the near one. The test takes h in [1, 2) there at
// e = -1036 and -1040, with l = ±2^-53, the extremes, and l = 0, and the only ties with h in
// (1/2, 2) at e = -1074 and -1075: h = 3/2 (C = 2^52, g = 1), which Fast2Sum rounds up to
// s = C + 2, with l = ±2^-53 and 0, and h = 1 (g = 2), which it rounds down to s = C, the
// smallest s, with l = -2^-54, 0 and 2^-53, all of which leave u = g/2. Below e = -1075,
// g/2 >= 2 > h, so C + h rounds to C with t = h, and no h < 2 is a tie.
#[test]
fn far_side_ties_constructed() {
    use crate::dyadic::fast::{fast_counts, reset_fast_counts};
    // The bits of `round_near_wide(h, l, e)`, for a pair (h, l) of the fast paths. It counts
    // one rounding test, which passed where the result is `Some`.
    let round = |h: f64, l: f64, e: i32| {
        assert_eq!(h + l, h, "({h:e}, {l:e}) is not a pair of the fast paths");
        reset_fast_counts();
        let r = round_near_wide(h, l, i64::from(e));
        let counts = if r.is_some() { (1, 0) } else { (0, 1) };
        assert_eq!(fast_counts(), counts, "({h:e}, {l:e}, {e})");
        r.map(f64::to_bits)
    };
    for e in [-1022, -1023, -1030] {
        let c = pow2(-1022 - e);
        let g = f64::EPSILON * c;
        // 2^-67 C, and the ulps of u just beyond the far bound and just below the near one.
        let (d, far, near) = (2.0 * FAST_ERR * c, pow2(-105) * c, pow2(-106) * c);
        for m in [
            1 << 39,
            (1 << 39) + 1,
            (1 << 43) + 0x1234,
            (1 << 43) + 0x1235,
            0x000a_7f31_c4d2_9e56,
            0x000a_7f31_c4d2_9e57,
            (1 << 52) - 2,
        ] {
            let h = (m as f64 + 0.5) * g;
            let sign = if m % 2 == 0 { 1.0 } else { -1.0 };
            assert_eq!(
                sub_tie(h, 0.0, i64::from(e)),
                Some(sign * f64::EPSILON / 2.0)
            );
            for (l, passes) in [
                (sign * (d + far), true),
                (sign * d, false),
                (0.0, false),
                (-sign * d, false),
                (-sign * (d + near), true),
            ] {
                let oracle = if l > 0.0 { m + 1 } else { m };
                assert_eq!(
                    round(h, l, e),
                    passes.then_some(oracle),
                    "m = {m}, ({h:e}, {l:e}, {e})"
                );
            }
        }
        // m = 2^52 - 1.
        let h = ((1u64 << 52) as f64 - 0.5) * g;
        assert_eq!(fast_two_sum(c, h).0, 2.0 * c);
        for l in [-(d + far), 0.0, d + far] {
            assert_eq!(round(h, l, e), None, "({h:e}, {l:e}, {e})");
        }
    }
    let half = f64::EPSILON / 2.0;
    for e in [-1036, -1040] {
        let k = -1022 - e;
        let g = f64::EPSILON * pow2(k);
        for m in [(1u64 << (52 - k)) + 0x1234, (1 << (52 - k)) + 0x1235] {
            let h = (m as f64 + 0.5) * g;
            assert!((1.0..2.0).contains(&h));
            // The l beyond 2^-53 = ulp(h)/2 are not valid.
            assert!(h + next_up(half) != h && h - next_up(half) != h);
            for l in [-half, 0.0, half] {
                assert_eq!(round(h, l, e), None, "({h:e}, {l:e}, {e})");
            }
        }
    }
    // (e, h, s - C, t) at the ties of e = -1074 and -1075.
    for (e, h, ds, t, ls) in [
        (-1074, 1.5, 2.0, -0.5, [-half, 0.0, half]),
        (-1075, 1.0, 0.0, 1.0, [-half / 2.0, 0.0, half]),
    ] {
        let c = pow2(-1022 - e);
        assert_eq!(fast_two_sum(c, h), (c + ds, t));
        assert_eq!(sub_tie(h, 0.0, i64::from(e)), Some(t / c));
        for l in ls {
            assert_eq!(round(h, l, e), None, "({h:e}, {l:e}, {e})");
        }
    }
}

// The branches of the fast paths of sinh, cosh and tanh, as (function, a, b) for the arguments
// t = |x| in [a, b) of each: the Taylor polynomials of sinh below 1/4 and of tanh below 1/8,
// e^t with e^-t up to 26 (sinh and cosh), e^-2t up to 20 (tanh, whose rules settle |x| >= 19
// in the directions and |x| >= 20 to nearest), e^t alone from 26 to 709, where `fast_exp`
// stops, and e^t from `fast_exp_edge` from 709 to 710.47, near the end of the fast paths of
// sinh and cosh at about 710.47578. Below `TINY_NEAR` (and `TINY_HYP` in the directions), the
// rules settle all three.
const HYP_BRANCHES: [(usize, f64, f64); 9] = [
    (SINH, TINY_NEAR, 0.25),
    (SINH, 0.25, 26.0),
    (SINH, 26.0, 709.0),
    (SINH, 709.0, 710.47),
    (COSH, TINY_NEAR, 26.0),
    (COSH, 26.0, 709.0),
    (COSH, 709.0, 710.47),
    (TANH, TINY_NEAR, 0.125),
    (TANH, 0.125, 20.0),
];

// (h, l, e, err) of the fast path of sinh, cosh or tanh (the function `i`) at t = |x|, as the
// function computes them, or `None` out of the range of the fast path.
fn hyp_parts(i: usize, t: f64) -> Option<(f64, f64, i64, f64)> {
    match i {
        SINH => fast_sinh_pos(t),
        COSH => fast_cosh_pos(t),
        TANH => fast_tanh_pos(t),
        _ => unreachable!(),
    }
}

// A random `f64` in [a, b], for 0 < a < b: uniform if `log` is false, and otherwise with an
// exponent uniform over those of [a, b] and a random significand, in [a, b).
fn in_range(rng: &mut Rng, a: f64, b: f64, log: bool) -> f64 {
    if !log {
        return uniform(rng, a, b);
    }
    let exponent = |x: f64| (x.to_bits() >> 52) as i32 - 1023;
    loop {
        let t = log_uniform(rng, exponent(a), exponent(b)).abs();
        if a <= t && t < b {
            return t;
        }
    }
}

// `t` or `-t`, at random.
fn either_sign(rng: &mut Rng, t: f64) -> f64 {
    if rng.below(2) == 0 {
        t
    } else {
        -t
    }
}

// sinh, cosh and tanh on random arguments of each branch of their fast paths (`HYP_BRANCHES`),
// half uniform over the branch and half of any exponent in it, with either sign. Most of the
// rounding tests pass in each branch.
#[test]
fn fast_hyp_range_random() {
    let mut rng = Rng(921);
    for (i, a, b) in HYP_BRANCHES {
        crate::dyadic::fast::reset_fast_counts();
        for n in 0..2000 {
            let t = in_range(&mut rng, a, b, n % 2 == 1);
            check(i, either_sign(&mut rng, t));
        }
        let (passed, failed) = crate::dyadic::fast::fast_counts();
        assert!(
            passed > 100 * failed,
            "{} on [{a:e}, {b:e}): {passed} passed, {failed} failed",
            FUNCTIONS[i].0
        );
    }
}

// sinh, cosh and tanh around the thresholds of their rules and of the branches of their fast
// paths, with both signs: the tiny arguments' rules at 2^-27 (to nearest) and 2^-26
// (directions), the polynomials' ends at 1/8 and 1/4, tanh's rules at 19 and 20, the end of
// the reciprocal at 26, the end of `fast_exp` at 709 and the overflow rules at 711. At 709,
// the fast paths of sinh and cosh take 709 and the `f64`s on both sides of it: `fast_exp_edge`
// continues `fast_exp` above it.
#[test]
fn hyp_thresholds() {
    let thresholds = [
        TINY_NEAR, TINY_HYP, 0.125, 0.25, 19.0, 20.0, 26.0, 709.0, 711.0,
    ];
    for i in [SINH, COSH, TANH] {
        for &x in &thresholds {
            for x in around(x, 4) {
                check(i, x);
                check(i, -x);
            }
        }
    }
    for t in around(709.0, 4) {
        for i in [SINH, COSH] {
            assert!(hyp_parts(i, t).is_some(), "{}({t:e})", FUNCTIONS[i].0);
        }
    }
}

// sinh, cosh and tanh where a rounding test of their fast paths passes, but would fail with
// 2^6 err in place of the bound err that the fast path returns, as in `widened`: there an error
// in the bound would show first, so the fast paths have to give the same `f64`s as the kernel,
// and as MPFR. Each branch is sampled until it has 40 narrow passes of the directed tests and
// 40 of the test to nearest, which took from about 700 random arguments (err = 2^-63) to about
// 26,000 (err = 2^-68) with this seed. A directed test is taken from `TINY_HYP` on, and for
// tanh below 19.
#[test]
fn hyp_widened() {
    let mut rng = Rng(922);
    for (i, a, b) in HYP_BRANCHES {
        let (mut dir, mut near, mut n) = (0, 0, 0);
        while dir < 40 || near < 40 {
            n += 1;
            assert!(
                n <= 100_000,
                "{} on [{a:e}, {b:e}): {dir} narrow passes of the directed tests and {near} of \
                 the test to nearest in 100000 arguments",
                FUNCTIONS[i].0
            );
            let t = in_range(&mut rng, a, b, n % 2 == 1);
            let Some((h, l, _, err)) = hyp_parts(i, t) else {
                continue;
            };
            let wide = 64.0 * err;
            // Half the gap between h and the next `f64` above it, and below it.
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
            let h_ok = 0.5 < h && h < 2.0;
            let dir_taken = t >= TINY_HYP && (i != TANH || t < 19.0);
            let narrow_dir = h_ok && dir_taken && err < l.abs() && l.abs() <= wide;
            let narrow_near = h_ok
                && l < above - err
                && l > -(below - err)
                && (l >= above - wide || l <= -(below - wide));
            if !narrow_dir && !narrow_near {
                continue;
            }
            dir += usize::from(narrow_dir);
            near += usize::from(narrow_near);
            let x = either_sign(&mut rng, t);
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
    use std::ops::RangeInclusive;

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

    // The precision of the values that the tables, the constants and the results of the fast
    // path are checked against, far above that of the bounds checked.
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

    // The tables and the constants of the fast path of `exp.rs` are what the comments on them
    // say, with the bounds that `rocq/theories/FastExpTables.v` proves.
    #[test]
    fn fast_tables_and_constants() {
        for (name, table, d) in [("T1", &T1, 4096), ("T2", &T2, 64)] {
            for (i, &pair) in table.iter().enumerate() {
                // 2^(i/d), with i/d exact.
                let mut v = Float::with_val(PREC, u32::try_from(i).unwrap());
                v /= d;
                v.exp2_mut();
                check_pair(&format!("{name}[{i}]"), pair, &v, -104);
            }
        }
        let ln2 = Float::with_val(PREC, Constant::Log2);
        let c = Float::with_val(PREC, &ln2 / 4096);
        // `C1` is c with its significand cut to 31 bits.
        let c1 = Float::with_val_round(31, &c, Round::Zero).0.to_f64();
        assert_eq!(C1, c1.to_bits(), "C1: {:e} != {c1:e}", f64::from_bits(C1));
        check_low("C2", &c, c1, f64::from_bits(C2), -98);
        let inv = Float::with_val(PREC, 4096) / &ln2;
        assert_eq!(INV, inv.to_f64().to_bits(), "INV");
        assert_eq!(
            P3,
            Float::with_val(PREC, 6).recip().to_f64().to_bits(),
            "P3"
        );
        assert_eq!(
            P4,
            Float::with_val(PREC, 24).recip().to_f64().to_bits(),
            "P4"
        );
        check_pair("LN2", LN2, &ln2, -106);
        check_pair("LN10", LN10, &Float::with_val(PREC, 10).ln(), -105);
    }

    // (h, l, e), from the fast path at z, have h = RN(h + l), 1/2 < h < 2, e in `es`, and
    // |y 2^-e - (h + l)| <= `bound` for y = e^z.
    fn check_parts(
        what: &str,
        y: Float,
        (h, l, e): (f64, f64, i64),
        es: RangeInclusive<i64>,
        bound: f64,
    ) {
        let mut d = y >> i32::try_from(e).unwrap();
        d -= h;
        d -= l;
        d.abs_mut();
        assert!(
            h + l == h && 0.5 < h && h < 2.0 && es.contains(&e) && d <= bound,
            "{what}: ({h:e}, {l:e}, {e}), with |e^z 2^-e - (h + l)| = {:e}",
            d.to_f64()
        );
    }

    // `fast_exp(zh, zl)` meets the bounds of `fast_exp_correct` in
    // `rocq/theories/FastExpCore.v`, with |e^z 2^-e - (h + l)| <= 2^-68 - 2^-72 for
    // z = zh + zl, on random zh in [-707, 709] with |zl| <= 2^-40, at the ends of that range,
    // and next to the edges of the tables and of the reduction (as in
    // `table_and_reduction_edges`).
    #[test]
    fn fast_exp_bound() {
        let mut rng = Rng(873);
        let tiny = pow2(-40);
        let mut args = vec![];
        for zh in [-707.0, 709.0, 0.0] {
            for zl in [-tiny, 0.0, tiny] {
                args.push((zh, zl));
            }
        }
        for e in (-1020..=1022).step_by(7) {
            for o in [-1, 0, 63, 64] {
                for d in [0.0, 0.5] {
                    let zh = (f64::from(4096 * e + o) + d) * (LN_2 / 4096.0);
                    if (-707.0..=709.0).contains(&zh) {
                        args.push((zh, uniform(&mut rng, -tiny, tiny)));
                    }
                }
            }
        }
        for _ in 0..4000 {
            args.push((
                uniform(&mut rng, -707.0, 709.0),
                uniform(&mut rng, -tiny, tiny),
            ));
        }
        for (zh, zl) in args {
            // zh + zl is exact in 300 bits.
            let mut y = Float::with_val(PREC, zh) + zl;
            y.exp_mut();
            check_parts(
                &format!("fast_exp({zh:e}, {zl:e})"),
                y,
                fast_exp(zh, zl).unwrap(),
                -1021..=1022,
                pow2(-68) - pow2(-72),
            );
        }
    }

    // `fast_exp_by(x, LN2)` and `fast_exp_by(x, LN10)` meet the bounds of `fe_by_correct` in
    // `rocq/theories/FastExp.v`, with |e^(x k) 2^-e - (h + l)| <= 2^-68 for k = ln 2 and ln 10,
    // on random x of the fast path with 2^-56 <= |x|, as in `fast_range_random`.
    #[test]
    fn fast_exp_by_bound() {
        let mut rng = Rng(874);
        let ln2 = Float::with_val(PREC, Constant::Log2);
        let ln10 = Float::with_val(PREC, 10).ln();
        for (i, c, k) in [(EXP2, LN2, &ln2), (EXP10, LN10, &ln10)] {
            let s = SCALES[i];
            for _ in 0..2000 {
                for x in [
                    uniform(&mut rng, -707.0 / s, 709.0 / s),
                    log_uniform(&mut rng, -56, 9),
                ] {
                    if let Some(parts) = fast_exp_by(x, c) {
                        let mut y = Float::with_val(PREC, k * x);
                        y.exp_mut();
                        let what = format!("fast_exp_by({x:e}) of {}", FUNCTIONS[i].0);
                        check_parts(&what, y, parts, -1021..=1022, pow2(-68));
                    }
                }
            }
        }
    }

    // `fast_exp_edge(zh, zl)` meets the bounds of `fast_exp_edge_correct` in
    // `rocq/theories/FastExpEdge.v`, with |e^z 2^-e - (h + l)| <= 2^-68 - 2^-73 and e in
    // [-1085, 1026] for z = zh + zl, on random zh in [-745.9, -707] and [709, 711.5], beyond the
    // range of `fast_exp`, with |zl| <= 3 2^-42, and next to their ends, where |zh| >= 2^9 as
    // the theorem assumes; and `fast_exp_by_edge(x, LN2)` and
    // `fast_exp_by_edge(x, LN10)` meet those of `fe_by_edge_correct` in
    // `rocq/theories/FastExpByEdge.v`, the same for e^(x k), k = ln 2 and ln 10, on random x
    // beyond the range of `fast_exp_by` that the rules leave.
    #[test]
    fn fast_exp_edge_bound() {
        let mut rng = Rng(875);
        let tiny = 3.0 * pow2(-42);
        let mut args = vec![];
        for zh in [-745.9, -707.0, 709.0, 710.0, 711.5] {
            for x in around(zh, 4) {
                args.push((x, 0.0));
            }
        }
        for _ in 0..4000 {
            for (a, b) in [(-745.9, -707.0), (709.0, 711.5)] {
                args.push((uniform(&mut rng, a, b), uniform(&mut rng, -tiny, tiny)));
            }
        }
        for (zh, zl) in args {
            let what = format!("fast_exp_edge({zh:e}, {zl:e})");
            let parts = fast_exp_edge(zh, zl).expect(&what);
            // zh + zl is exact in 300 bits.
            let mut y = Float::with_val(PREC, zh) + zl;
            y.exp_mut();
            check_parts(&what, y, parts, -1085..=1026, pow2(-68) - pow2(-73));
        }
        let ln2 = Float::with_val(PREC, Constant::Log2);
        let ln10 = Float::with_val(PREC, 10).ln();
        for (i, c, k, ranges) in [
            (EXP2, LN2, &ln2, [(-1075.0, -1019.0), (1022.0, 1024.0)]),
            (EXP10, LN10, &ln10, [(-324.0, -307.0), (307.0, 309.0)]),
        ] {
            for (a, b) in ranges {
                for _ in 0..2000 {
                    let x = uniform(&mut rng, a, b);
                    if fast_exp_by(x, c).is_some() {
                        continue;
                    }
                    let parts = fast_exp_by_edge(x, c).unwrap();
                    let mut y = Float::with_val(PREC, k * x);
                    y.exp_mut();
                    let what = format!("fast_exp_by_edge({x:e}) of {}", FUNCTIONS[i].0);
                    check_parts(&what, y, parts, -1085..=1026, pow2(-68) - pow2(-73));
                }
            }
        }
    }

    // 1/n!, at `PREC` bits.
    fn recip_factorial(n: u32) -> Float {
        Float::with_val(PREC, Float::factorial(n)).recip()
    }

    // The coefficients and the error bounds of the fast paths of sinh, cosh and tanh are what
    // the comments on them say.
    #[test]
    fn fast_hyp_constants() {
        for (n, c) in [
            (5, SH5),
            (7, SH7),
            (9, SH9),
            (11, SH11),
            (13, SH13),
            (15, SH15),
            (4, CH4),
            (6, CH6),
            (8, CH8),
            (10, CH10),
            (12, CH12),
        ] {
            let want = recip_factorial(n).to_f64();
            assert_eq!(
                c,
                want.to_bits(),
                "{:e} != RN(1/{n}!) = {want:e}",
                f64::from_bits(c)
            );
        }
        check_pair("SH3", SH3, &recip_factorial(3), -110);
        for (c, n) in [(ERR63, -63), (ERR67, -67), (ERR68, -68)] {
            assert_eq!(c.to_bits(), pow2(n).to_bits(), "2^{n}");
        }
    }

    // f(t) at `PREC` bits for the function `i`, sinh, cosh or tanh.
    fn hyp(i: usize, t: f64) -> Float {
        let mut y = Float::with_val(PREC, t);
        match i {
            SINH => y.sinh_mut(),
            COSH => y.cosh_mut(),
            TANH => y.tanh_mut(),
            _ => unreachable!(),
        }
        y
    }

    // (h, l, e, err), from the fast path of the function `i` at t >= 0, are finite, with
    // h = RN(h + l), e in [-1021, 1023] ([-1021, 1022] for tanh), err = 2^-p for an integer p
    // in [55, 105], and |f(t) 2^-e - (h + l)| <= err, as `fast_sinh_pos_correct` in
    // `rocq/theories/FastHypPos.v`, `fast_cosh_pos_correct` in `FastCoshPos.v` and
    // `fast_tanh_pos_correct` in `FastTanhPos.v` state.
    // Returns |f(t) 2^-e - (h + l)| / err.
    fn check_hyp_parts(i: usize, t: f64, (h, l, e, err): (f64, f64, i64, f64)) -> f64 {
        let mut d = hyp(i, t) >> i32::try_from(e).unwrap();
        d -= h;
        d -= l;
        d.abs_mut();
        // err = 2^-p, from its bits: a zero significand and the biased exponent 1023 - p.
        let p = 1023 - i64::try_from(err.to_bits() >> 52).unwrap();
        let pow2_err = err.to_bits() & ((1 << 52) - 1) == 0;
        assert!(
            h.is_finite()
                && l.is_finite()
                && h + l == h
                && (-1021..=if i == TANH { 1022 } else { 1023 }).contains(&e)
                && pow2_err
                && (55..=105).contains(&p)
                && d <= err,
            "fast path of {}({t:e}): ({h:e}, {l:e}, {e}, {err:e}), with |f(t) 2^-e - (h + l)| \
             = {:e}",
            FUNCTIONS[i].0,
            d.to_f64()
        );
        (d / err).to_f64()
    }

    // `fast_sinh_pos`, `fast_cosh_pos` and `fast_tanh_pos` meet their bounds (`check_hyp_parts`)
    // on random arguments of each branch of `HYP_BRANCHES`, uniform and of any exponent in it,
    // around the thresholds of the branches and rules, and, for tanh, on [20, 353.5], where the
    // rules of `tanh` and `tanh_near` take over but the bound still holds. The fast paths take
    // every t from `TINY_NEAR` (sinh and tanh) or 0 (cosh) to about 710.47578 (sinh and cosh,
    // whose results reach 2^1024 near 710.48) or 353.5 (tanh, where -2t reaches the end -707 of
    // `fast_exp`), and none beyond: for sinh and cosh, the test checks that they take the t it
    // tries up to 710.47, and none above 710.5. With `--nocapture`, prints the largest error
    // found in each branch, as a fraction of err.
    #[test]
    fn fast_hyp_bound() {
        let mut rng = Rng(923);
        let mut branches = HYP_BRANCHES.to_vec();
        branches.push((TANH, 20.0, 353.5));
        for (i, a, b) in branches {
            let mut worst: f64 = 0.0;
            for n in 0..4000 {
                let t = in_range(&mut rng, a, b, n % 2 == 1);
                let parts = hyp_parts(i, t).unwrap();
                worst = worst.max(check_hyp_parts(i, t, parts));
            }
            println!(
                "{} on [{a:e}, {b:e}): largest error {worst:.4} err",
                FUNCTIONS[i].0
            );
        }
        for t in [
            0.0,
            f64::from_bits(1),
            f64::MIN_POSITIVE,
            TINY_NEAR,
            TINY_HYP,
        ]
        .into_iter()
        .chain([0.125, 0.25, 1.0, 19.0, 20.0, 26.0, 353.5, 709.0, 711.0])
        .chain([1025.0 * LN_2 - LN_2 / 8192.0, 1025.0 * LN_2])
        .flat_map(|x| around(x, 4))
        .filter(|&t| t >= 0.0)
        {
            // The fast path takes every t in [start, end] and none above `last`.
            for (i, start, end, last) in [
                (SINH, TINY_NEAR, 710.47, 710.5),
                (COSH, 0.0, 710.47, 710.5),
                (TANH, TINY_NEAR, 353.5, 353.5),
            ] {
                match hyp_parts(i, t) {
                    Some(parts) => {
                        assert!(start <= t && t <= last, "{}({t:e})", FUNCTIONS[i].0);
                        check_hyp_parts(i, t, parts);
                    }
                    None => assert!(t < start || t > end, "{}({t:e})", FUNCTIONS[i].0),
                }
            }
        }
    }

    // `fast_sinh_poly` and `fast_cosh_poly` meet the bounds of `sinh_poly_correct` in
    // `rocq/theories/FastHypPoly.v` and `cosh_poly_correct` in `FastCoshPoly.v` on random t of
    // their ranges, [2^-27, 1/4) and [2^-27, 1/8), uniform and of any exponent, and around their
    // ends:
    // sh = RN(sh + sl), 2^-27 <= sh <= 1/2, |sl| <= 2^-52 sh and sh + sl within 2^-65 of sinh t
    // relatively; 1 <= ch <= 2, |cl| <= 2^-52 ch and ch + cl within 2^-66 of cosh t relatively.
    #[test]
    fn fast_hyp_poly_bound() {
        let mut rng = Rng(924);
        for (i, end) in [(SINH, 0.25), (COSH, 0.125)] {
            let mut args: Vec<f64> = (0..4000)
                .map(|n| in_range(&mut rng, TINY_NEAR, end, n % 2 == 1))
                .collect();
            args.extend(around(TINY_NEAR, 4).into_iter().filter(|&t| t >= TINY_NEAR));
            args.extend(around(end, 4).into_iter().filter(|&t| t < end));
            for t in args {
                let y = hyp(i, t);
                let (h, l) = if i == SINH {
                    fast_sinh_poly(t)
                } else {
                    fast_cosh_poly(t)
                };
                let mut d = Float::with_val(PREC, &y - h);
                d -= l;
                d.abs_mut();
                // Whether h is in its range and RN(h + l), and the relative bound 2^-rel.
                let (range, rn, rel): (bool, bool, i32) = if i == SINH {
                    ((TINY_NEAR..=0.5).contains(&h), h + l == h, 65)
                } else {
                    ((1.0..=2.0).contains(&h), true, 66)
                };
                assert!(
                    range && rn && l.abs() <= f64::EPSILON * h && d <= y >> rel,
                    "polynomial of {}({t:e}): ({h:e}, {l:e}), with |f(t) - (h + l)| = {:e}",
                    FUNCTIONS[i].0,
                    d.to_f64()
                );
            }
        }
    }

    // `dd_div(nh, nl, dh, dl)` meets the bounds of `dd_div_correct` in
    // `rocq/theories/FastDiv.v`, qh = RN(qh + ql) and qh + ql within 2^-98 of the quotient q
    // relatively, on random arguments with 2^-80 <= nh <= 4, |nl| <= 2^-50 nh, 1/2 <= dh <= 4
    // and |dl| <= 2^-52 dh, of any exponent in those ranges and at their ends.
    #[test]
    fn dd_div_bound() {
        let mut rng = Rng(925);
        // A high part: a or b, or random in [a, b] of any exponent.
        let high = |rng: &mut Rng, a: f64, b: f64| match rng.below(4) {
            0 => a,
            1 => b,
            _ => in_range(rng, a, b, true),
        };
        // A low part for the high part h: 0, ±2^n h, or uniform in [-2^n h, 2^n h]. The
        // product rounds to at most 2^n h, which is exact.
        let low = |rng: &mut Rng, h: f64, n: i32| {
            let u = match rng.below(4) {
                0 => 0.0,
                1 => pow2(n),
                _ => uniform(rng, 0.0, pow2(n)),
            };
            either_sign(rng, h * u)
        };
        for _ in 0..20000 {
            let nh = high(&mut rng, pow2(-80), 4.0);
            let dh = high(&mut rng, 0.5, 4.0);
            let nl = low(&mut rng, nh, -50);
            let dl = low(&mut rng, dh, -52);
            let (qh, ql) = dd_div(nh, nl, dh, dl);
            let q = (Float::with_val(PREC, nh) + nl) / (Float::with_val(PREC, dh) + dl);
            let mut d = Float::with_val(PREC, &q - qh);
            d -= ql;
            d.abs_mut();
            assert!(
                qh + ql == qh && d <= q >> 98,
                "dd_div({nh:e}, {nl:e}, {dh:e}, {dl:e}) = ({qh:e}, {ql:e}), with |q - (qh + ql)| \
                 = {:e}",
                d.to_f64()
            );
        }
    }
}

mod levels;
