// Tests the linked MPFR against what `rocq/theories/Mpfr.v` assumes of it: the special
// values of the `<f>_ok` definitions, `get_d_ok` at its edges, and the conversions of
// `parse_ok`. MPFR is called as `mpfr_fn!`, `mpfr_fn2!`, `mpfr_fn_si!` and
// `rational_to_f64` call it.
//
// Each check names, in a comment, the definition of `Mpfr.v` and the clause of it that it
// checks. A clause stated `forall rnd` is checked with `RNDD` and with `RNDU`. The checks
// look at the MPFR number itself, not only at its `mpfr::get_d`: `value` reads it as `mpfr_t`
// in `rocq/theories/Model.v` has it, so that a special value is checked with the sign of a
// zero. Where `Mpfr.v` states a rounding (`mpfr_round`), which gives a result of 0 as a zero
// of either sign, the check compares `Float`s or `f64`s with `==`, which does not tell the
// zeros apart.
//
// MPFR's exponent range is per thread, as `gmp-mpfr-sys` builds MPFR thread-safe. The tests
// read it with `mpfr::get_emin` and `mpfr::get_emax` rather than assume MPFR's default, and
// `at_parse_range` restores it.

use crate::*;
use gmp_mpfr_sys::mpfr::{
    self,
    rnd_t::{RNDD, RNDU},
};
use rug::{Float, Rational};
use Interval as I;

const PREC: u32 = f64::MANTISSA_DIGITS;
const DIRS: [mpfr::rnd_t; 2] = [RNDD, RNDU];

// The value of an MPFR number, as `mpfr_t` in `rocq/theories/Model.v` has it: NaN, an
// infinity or a zero with its sign, `true` for negative as there, or a number other than 0.
#[derive(Debug, PartialEq)]
enum Value {
    NaN,
    Inf(bool),
    Zero(bool),
    Num(Float),
}

use Value::{Inf, Num, Zero};

// The value of the MPFR number `x`.
fn value(x: &Float) -> Value {
    if x.is_nan() {
        Value::NaN
    } else if x.is_infinite() {
        Inf(x.is_sign_negative())
    } else if x.is_zero() {
        Zero(x.is_sign_negative())
    } else {
        Num(x.clone())
    }
}

// The value `MNum x` of the finite `f64` `x` other than 0.
fn num(x: f64) -> Value {
    assert!(x.is_finite() && x != 0.0);
    Num(Float::with_val(PREC, x))
}

// The `f64` `x` as an MPFR number of 53 bits, which holds it exactly (`with_val`).
fn of_f64(x: f64) -> Float {
    Float::with_val(PREC, x)
}

// The MPFR number `m * 2^e` of 53 bits, for an integer `m` with `|m| <= 2^53`, which it holds
// exactly if `e` is in MPFR's exponent range.
fn float(m: i64, e: i32) -> Float {
    assert!(m.unsigned_abs() <= 1 << 53);
    Float::with_val(PREC, m) << e
}

// The rational `m * 2^e`.
fn rational(m: i64, e: i32) -> Rational {
    Rational::from(m) << e
}

// The `f64` `k * 2^-1074`, for `0 <= k < 2^52`: 0 or a subnormal number.
fn sub(k: u64) -> f64 {
    assert!(k < 1 << 52);
    f64::from_bits(k)
}

// `d` is `e`, where an `e` of 0 stands for a zero of either sign.
fn is_f64(d: f64, e: f64) -> bool {
    if e == 0.0 {
        d == 0.0
    } else {
        d.to_bits() == e.to_bits()
    }
}

// MPFR's exponent range in this thread, `emin` and `emax`.
fn range() -> (i32, i32) {
    let (emin, emax) = unsafe { (mpfr::get_emin(), mpfr::get_emax()) };
    (emin.try_into().unwrap(), emax.try_into().unwrap())
}

// The largest MPFR number of 53 bits, `(1 - 2^-53) * 2^emax`.
fn largest() -> Float {
    let (_, emax) = range();
    float((1 << 53) - 1, emax - 53)
}

// The least positive MPFR number, `2^(emin - 1)`, as MPFR writes a number as `m * 2^e` with
// `1/2 <= |m| < 1`.
fn least() -> Float {
    let (emin, _) = range();
    float(1, emin - 1)
}

// The MPFR number that `mpfr_fn!($mpfr_f(x, rnd))` in `src/elementary.rs` passes to
// `mpfr::get_d`, made the same way.
macro_rules! call {
    ($mpfr_f:ident($x:expr, $rnd:expr)) => {{
        let x: f64 = $x;
        let mut x = Float::with_val(f64::MANTISSA_DIGITS, x);
        let rnd = $rnd;
        unsafe {
            mpfr::$mpfr_f(x.as_raw_mut(), x.as_raw(), rnd);
        }
        x
    }};
}

// The same for `mpfr_fn2!($mpfr_f(x, y, rnd))`.
macro_rules! call2 {
    ($mpfr_f:ident($x:expr, $y:expr, $rnd:expr)) => {{
        let (x, y): (f64, f64) = ($x, $y);
        let mut x = Float::with_val(f64::MANTISSA_DIGITS, x);
        let y = Float::with_val(f64::MANTISSA_DIGITS, y);
        let rnd = $rnd;
        unsafe {
            mpfr::$mpfr_f(x.as_raw_mut(), x.as_raw(), y.as_raw(), rnd);
        }
        x
    }};
}

// The same for `mpfr_fn_si!($mpfr_f(x, y, rnd))`.
macro_rules! call_si {
    ($mpfr_f:ident($x:expr, $y:expr, $rnd:expr)) => {{
        let (x, y): (f64, i32) = ($x, $y);
        let mut x = Float::with_val(f64::MANTISSA_DIGITS, x);
        let rnd = $rnd;
        unsafe {
            mpfr::$mpfr_f(x.as_raw_mut(), x.as_raw(), y.into(), rnd);
        }
        x
    }};
}

// `mpfr::get_d` of the MPFR number `x`, rounded in the direction `rnd`.
fn get_d(x: &Float, rnd: mpfr::rnd_t) -> f64 {
    unsafe { mpfr::get_d(x.as_raw(), rnd) }
}

// `f()` at the exponent range that `rational_to_f64` in `src/parse.rs` sets, `emin = -1073`
// and `emax = 1024`, set and restored as it does.
fn at_parse_range<T>(f: impl FnOnce() -> T) -> T {
    let (orig_emin, orig_emax) = unsafe { (mpfr::get_emin(), mpfr::get_emax()) };
    unsafe {
        assert_eq!(
            mpfr::set_emin((f64::MIN_EXP - (f64::MANTISSA_DIGITS as i32) + 1).into()),
            0
        );
        assert_eq!(mpfr::set_emax(f64::MAX_EXP.into()), 0);
    }
    let r = f();
    unsafe {
        mpfr::set_emin(orig_emin);
        mpfr::set_emax(orig_emax);
    }
    r
}

// `ternary_ok r v t` of `Mpfr.v`: `t` is the ternary value of the MPFR result `v` for the
// exact result `r`.
fn ternary_ok(r: &Rational, v: &Value, t: i32) -> bool {
    match v {
        Value::NaN => false,
        Inf(s) => {
            if *s {
                t < 0
            } else {
                0 < t
            }
        }
        Zero(_) => (t < 0) == (*r > 0) && (t == 0) == (*r == 0),
        Num(y) => (t < 0) == (*y < *r) && (t == 0) == (*y == *r),
    }
}

// `range_ok emin emax`: MPFR's exponent range in this thread, the one that
// `src/elementary.rs` runs in, contains that of `f64`.
#[test]
fn range_ok() {
    let (emin, emax) = range();
    assert!(emin <= -1073, "{emin}");
    assert!(1024 <= emax, "{emax}");
}

// `with_val` of `rocq/theories/Model.v`, which `Mpfr.v` relies on to read the arguments:
// `Float::with_val(f64::MANTISSA_DIGITS, x)` holds `x` exactly, and keeps the sign of a zero
// and the infinities.
#[test]
fn with_val() {
    for x in [0.0f64, -0.0] {
        let y = Float::with_val(PREC, x);
        assert_eq!(value(&y), Zero(x.is_sign_negative()));
    }
    for x in [f64::INFINITY, f64::NEG_INFINITY] {
        let y = Float::with_val(PREC, x);
        assert_eq!(value(&y), Inf(x.is_sign_negative()));
    }
    for x in [5e-324, f64::MIN_POSITIVE, 1.0 / 3.0, 1.0, f64::MAX] {
        for x in [x, -x] {
            let y = Float::with_val(PREC, x);
            assert_eq!(y.prec(), 53);
            assert!(y.is_normal() && y == x, "{x:e}");
            assert_eq!(get_d(&y, RNDD).to_bits(), x.to_bits());
        }
    }
}

// `acosh_ok`, `mpfr_acosh m RNDU (MInf false) = MInf false`.
#[test]
fn acosh_ok() {
    assert_eq!(value(&call!(acosh(f64::INFINITY, RNDU))), Inf(false));
}

// `asinh_ok`, `mpfr_asinh m RNDD (MInf true) = MInf true` and
// `mpfr_asinh m RNDU (MInf false) = MInf false`.
#[test]
fn asinh_ok() {
    assert_eq!(value(&call!(asinh(f64::NEG_INFINITY, RNDD))), Inf(true));
    assert_eq!(value(&call!(asinh(f64::INFINITY, RNDU))), Inf(false));
}

// `atan_ok`, `mpfr_round (mpfr_format emin emax) RNDD (- (PI / 2)) (mpfr_atan m RNDD (MInf
// true))` and `mpfr_round (mpfr_format emin emax) RNDU (PI / 2) (mpfr_atan m RNDU (MInf
// false))`. `rocq/theories/ConstPi.v` proves that the bounds of `Interval::FRAC_PI_2` are
// π/2 rounded down and up to `f64`, which is rounding to 53 bits, as π/2 is a normal number.
#[test]
fn atan_ok() {
    assert_eq!(
        value(&call!(atan(f64::NEG_INFINITY, RNDD))),
        num(-I::FRAC_PI_2.sup())
    );
    assert_eq!(
        value(&call!(atan(f64::INFINITY, RNDU))),
        num(I::FRAC_PI_2.sup())
    );
}

// `atan2_ok`, the seven special values, in both directions. `mpfr_atan2 m rnd y x` is
// `call2!(atan2(y, x, rnd))`. The bounds of `Interval::PI` and `Interval::FRAC_PI_2` are π and
// π/2 rounded down and up (`rocq/theories/ConstPi.v`).
#[test]
fn atan2_ok() {
    let inf = f64::INFINITY;
    let ys = [5e-324, f64::MIN_POSITIVE, 0.5, 1.0, f64::MAX];
    let xs = [0.0, -0.0, 5e-324, -5e-324, 1.0, -1.0, f64::MAX, -f64::MAX];

    for rnd in DIRS {
        for y in ys {
            // `forall rnd y, 0 < y -> mpfr_atan2 m rnd (MNum y) (MInf false) = MZero false`
            assert_eq!(
                value(&call2!(atan2(y, inf, rnd))),
                Zero(false),
                "{y:e}, {rnd:?}"
            );
            // `forall rnd y, y < 0 -> mpfr_atan2 m rnd (MNum y) (MInf false) = MZero true`
            assert_eq!(
                value(&call2!(atan2(-y, inf, rnd))),
                Zero(true),
                "{:e}, {rnd:?}",
                -y
            );
        }

        // `forall rnd s, mpfr_atan2 m rnd (MZero s) (MInf false) = MZero s`, with the sign of
        // `y`, as MPFR's `src/atan2.c` gives it (review AT2)
        for y in [0.0f64, -0.0] {
            assert_eq!(
                value(&call2!(atan2(y, inf, rnd))),
                Zero(y.is_sign_negative()),
                "{y:e}, {rnd:?}"
            );
        }
    }

    for (rnd, pi_rnd, neg_pi_rnd) in [
        (RNDD, I::PI.inf(), -I::PI.sup()),
        (RNDU, I::PI.sup(), -I::PI.inf()),
    ] {
        for y in ys {
            // `forall rnd y, 0 < y -> mpfr_round (mpfr_format emin emax) rnd PI
            // (mpfr_atan2 m rnd (MNum y) (MInf true))`
            assert_eq!(
                value(&call2!(atan2(y, -inf, rnd))),
                num(pi_rnd),
                "{y:e}, {rnd:?}"
            );
            // `forall rnd y, y < 0 -> mpfr_round (mpfr_format emin emax) rnd (- PI)
            // (mpfr_atan2 m rnd (MNum y) (MInf true))`
            assert_eq!(
                value(&call2!(atan2(-y, -inf, rnd))),
                num(neg_pi_rnd),
                "{:e}, {rnd:?}",
                -y
            );
        }
    }

    for (rnd, frac_pi_2_rnd, neg_frac_pi_2_rnd) in [
        (RNDD, I::FRAC_PI_2.inf(), -I::FRAC_PI_2.sup()),
        (RNDU, I::FRAC_PI_2.sup(), -I::FRAC_PI_2.inf()),
    ] {
        for x in xs {
            // `forall rnd (x : f64), is_finite x = true -> mpfr_round (mpfr_format emin emax)
            // rnd (PI / 2) (mpfr_atan2 m rnd (MInf false) (with_val x))`
            assert_eq!(
                value(&call2!(atan2(inf, x, rnd))),
                num(frac_pi_2_rnd),
                "{x:e}, {rnd:?}"
            );
            // `forall rnd (x : f64), is_finite x = true -> mpfr_round (mpfr_format emin emax)
            // rnd (- (PI / 2)) (mpfr_atan2 m rnd (MInf true) (with_val x))`
            assert_eq!(
                value(&call2!(atan2(-inf, x, rnd))),
                num(neg_frac_pi_2_rnd),
                "{x:e}, {rnd:?}"
            );
        }
    }
}

// `atanh_ok`, `mpfr_atanh m RNDD (MNum (-1)) = MInf true` and
// `mpfr_atanh m RNDU (MNum 1) = MInf false`.
#[test]
fn atanh_ok() {
    assert_eq!(value(&call!(atanh(-1.0, RNDD))), Inf(true));
    assert_eq!(value(&call!(atanh(1.0, RNDU))), Inf(false));
}

// `cosh_ok`, `forall s, mpfr_cosh m RNDU (MInf s) = MInf false`.
#[test]
fn cosh_ok() {
    assert_eq!(value(&call!(cosh(f64::NEG_INFINITY, RNDU))), Inf(false));
    assert_eq!(value(&call!(cosh(f64::INFINITY, RNDU))), Inf(false));
}

// `exp_ok`, `exp10_ok` and `exp2_ok`, `mpfr_<f> m RNDD (MInf true) = MZero false` and
// `mpfr_<f> m RNDU (MInf false) = MInf false`.
#[test]
fn exp_ok() {
    let inf = f64::INFINITY;
    assert_eq!(value(&call!(exp(-inf, RNDD))), Zero(false));
    assert_eq!(value(&call!(exp(inf, RNDU))), Inf(false));
    assert_eq!(value(&call!(exp10(-inf, RNDD))), Zero(false));
    assert_eq!(value(&call!(exp10(inf, RNDU))), Inf(false));
    assert_eq!(value(&call!(exp2(-inf, RNDD))), Zero(false));
    assert_eq!(value(&call!(exp2(inf, RNDU))), Inf(false));
}

// `ln_ok`, `log10_ok` and `log2_ok`, `forall s, mpfr_<f> m RNDD (MZero s) = MInf true` and
// `mpfr_<f> m RNDU (MInf false) = MInf false`, where `mpfr_log` is `mpfr::log`.
#[test]
fn ln_ok() {
    let inf = f64::INFINITY;
    for x in [0.0f64, -0.0] {
        assert_eq!(value(&call!(log(x, RNDD))), Inf(true), "{x:e}");
        assert_eq!(value(&call!(log10(x, RNDD))), Inf(true), "{x:e}");
        assert_eq!(value(&call!(log2(x, RNDD))), Inf(true), "{x:e}");
    }
    assert_eq!(value(&call!(log(inf, RNDU))), Inf(false));
    assert_eq!(value(&call!(log10(inf, RNDU))), Inf(false));
    assert_eq!(value(&call!(log2(inf, RNDU))), Inf(false));
}

// `pow_ok`, the fourteen special values, in both directions. `mpfr_pow m rnd x y` is
// `call2!(pow(x, y, rnd))`; the clauses call the base `y` where it is a number.
#[test]
fn pow_ok() {
    let inf = f64::INFINITY;
    // Below 0: odd and even integers, and numbers that are not integers.
    let neg = [-5e-324, -0.5, -1.0, -2.0, -3.0, -f64::MAX];
    // Above 0, and between 0 and 1 and above 1.
    let pos = [5e-324, 0.5, 1.0, 2.0, 3.0, f64::MAX];
    let below_1 = [5e-324, f64::MIN_POSITIVE, 0.5, 1.0 - f64::EPSILON / 2.0];
    let above_1 = [1.0 + f64::EPSILON, 2.0, f64::MAX];

    for rnd in DIRS {
        for y in neg {
            // `forall rnd y, y < 0 -> mpfr_pow m rnd (MZero false) (MNum y) = MInf false`
            assert_eq!(
                value(&call2!(pow(0.0, y, rnd))),
                Inf(false),
                "{y:e}, {rnd:?}"
            );
        }
        // `forall rnd, mpfr_pow m rnd (MZero false) (MInf true) = MInf false`
        assert_eq!(value(&call2!(pow(0.0, -inf, rnd))), Inf(false), "{rnd:?}");
        // `forall rnd, mpfr_pow m rnd (MZero false) (MInf false) = MZero false`
        assert_eq!(value(&call2!(pow(0.0, inf, rnd))), Zero(false), "{rnd:?}");

        for s in [0.0f64, -0.0] {
            // `forall rnd s, mpfr_pow m rnd (MZero false) (MZero s) = MNum 1`
            assert_eq!(value(&call2!(pow(0.0, s, rnd))), num(1.0), "{s:e}, {rnd:?}");
            // `forall rnd s, mpfr_pow m rnd (MInf false) (MZero s) = MNum 1`
            assert_eq!(value(&call2!(pow(inf, s, rnd))), num(1.0), "{s:e}, {rnd:?}");
        }
        for s in [-inf, inf] {
            // `forall rnd s, mpfr_pow m rnd (MNum 1) (MInf s) = MNum 1`
            assert_eq!(value(&call2!(pow(1.0, s, rnd))), num(1.0), "{s:e}, {rnd:?}");
        }

        for y in below_1 {
            // `forall rnd y, 0 < y < 1 -> mpfr_pow m rnd (MNum y) (MInf true) = MInf false`
            assert_eq!(
                value(&call2!(pow(y, -inf, rnd))),
                Inf(false),
                "{y:e}, {rnd:?}"
            );
            // `forall rnd y, 0 < y < 1 -> mpfr_pow m rnd (MNum y) (MInf false) = MZero false`
            assert_eq!(
                value(&call2!(pow(y, inf, rnd))),
                Zero(false),
                "{y:e}, {rnd:?}"
            );
        }
        for y in above_1 {
            // `forall rnd y, 1 < y -> mpfr_pow m rnd (MNum y) (MInf true) = MZero false`
            assert_eq!(
                value(&call2!(pow(y, -inf, rnd))),
                Zero(false),
                "{y:e}, {rnd:?}"
            );
            // `forall rnd y, 1 < y -> mpfr_pow m rnd (MNum y) (MInf false) = MInf false`
            assert_eq!(
                value(&call2!(pow(y, inf, rnd))),
                Inf(false),
                "{y:e}, {rnd:?}"
            );
        }

        for y in neg {
            // `forall rnd y, y < 0 -> mpfr_pow m rnd (MInf false) (MNum y) = MZero false`
            assert_eq!(
                value(&call2!(pow(inf, y, rnd))),
                Zero(false),
                "{y:e}, {rnd:?}"
            );
        }
        // `forall rnd, mpfr_pow m rnd (MInf false) (MInf true) = MZero false`
        assert_eq!(value(&call2!(pow(inf, -inf, rnd))), Zero(false), "{rnd:?}");
        for y in pos {
            // `forall rnd y, 0 < y -> mpfr_pow m rnd (MInf false) (MNum y) = MInf false`
            assert_eq!(
                value(&call2!(pow(inf, y, rnd))),
                Inf(false),
                "{y:e}, {rnd:?}"
            );
        }
        // `forall rnd, mpfr_pow m rnd (MInf false) (MInf false) = MInf false`
        assert_eq!(value(&call2!(pow(inf, inf, rnd))), Inf(false), "{rnd:?}");
    }
}

// `pown_ok`, the seven special values, in both directions, for `i32`s `n`. `mpfr_pow_si m rnd
// x n` is `call_si!(pow_si(x, n, rnd))`.
#[test]
fn pown_ok() {
    let inf = f64::INFINITY;
    let neg_even = [i32::MIN, -2];
    let neg_odd = [-i32::MAX, -3, -1];
    let pos = [1, 2, 3, i32::MAX];
    let pos_odd = [1, 3, i32::MAX];

    for rnd in DIRS {
        for s in [0.0f64, -0.0] {
            for n in neg_even {
                // `forall rnd s n, is_i32 n -> (n < 0)%Z -> Z.even n = true ->
                // mpfr_pow_si m rnd (MZero s) n = MInf false`
                assert_eq!(
                    value(&call_si!(pow_si(s, n, rnd))),
                    Inf(false),
                    "{s:e}, {n}, {rnd:?}"
                );
            }
            for n in neg_odd {
                // `forall rnd s n, is_i32 n -> (n < 0)%Z -> Z.odd n = true ->
                // mpfr_pow_si m rnd (MZero s) n = MInf s`
                assert_eq!(
                    value(&call_si!(pow_si(s, n, rnd))),
                    Inf(s.is_sign_negative()),
                    "{s:e}, {n}, {rnd:?}"
                );
            }
        }

        for n in neg_even.into_iter().chain(neg_odd) {
            // `forall rnd n, is_i32 n -> (n < 0)%Z -> mpfr_pow_si m rnd (MInf false) n =
            // MZero false`
            assert_eq!(
                value(&call_si!(pow_si(inf, n, rnd))),
                Zero(false),
                "{n}, {rnd:?}"
            );
        }
        // `forall rnd, mpfr_pow_si m rnd (MInf false) 0 = MNum 1`
        assert_eq!(value(&call_si!(pow_si(inf, 0, rnd))), num(1.0), "{rnd:?}");
        for n in pos {
            // `forall rnd n, is_i32 n -> (0 < n)%Z -> mpfr_pow_si m rnd (MInf false) n =
            // MInf false`
            assert_eq!(
                value(&call_si!(pow_si(inf, n, rnd))),
                Inf(false),
                "{n}, {rnd:?}"
            );
        }
        for n in neg_odd {
            // `forall rnd n, is_i32 n -> (n < 0)%Z -> Z.odd n = true ->
            // mpfr_pow_si m rnd (MInf true) n = MZero true`
            assert_eq!(
                value(&call_si!(pow_si(-inf, n, rnd))),
                Zero(true),
                "{n}, {rnd:?}"
            );
        }
        for n in pos_odd {
            // `forall rnd n, is_i32 n -> (0 < n)%Z -> Z.odd n = true ->
            // mpfr_pow_si m rnd (MInf true) n = MInf true`
            assert_eq!(
                value(&call_si!(pow_si(-inf, n, rnd))),
                Inf(true),
                "{n}, {rnd:?}"
            );
        }
    }
}

// `sinh_ok`, `mpfr_sinh m RNDD (MInf true) = MInf true` and
// `mpfr_sinh m RNDU (MInf false) = MInf false`.
#[test]
fn sinh_ok() {
    assert_eq!(value(&call!(sinh(f64::NEG_INFINITY, RNDD))), Inf(true));
    assert_eq!(value(&call!(sinh(f64::INFINITY, RNDU))), Inf(false));
}

// `tanh_ok`, `mpfr_tanh m RNDD (MInf true) = MNum (-1)` and
// `mpfr_tanh m RNDU (MInf false) = MNum 1`.
#[test]
fn tanh_ok() {
    assert_eq!(value(&call!(tanh(f64::NEG_INFINITY, RNDD))), num(-1.0));
    assert_eq!(value(&call!(tanh(f64::INFINITY, RNDU))), num(1.0));
}

// The first clause of each `<f>_ok`, `mpfr_correct emin emax D f (mpfr_<f> m)` (or
// `mpfr_correct2`, or the first clause of `pown_ok`), at points of `D` where the value of
// `f` is 0 or an MPFR number, so that `mpfr_round` gives it in both directions: a zero of
// either sign (`RNDD, MZero _` and `RNDU, MZero _`), or that number (`RNDD, MNum y` and
// `RNDU, MNum y`).
#[test]
fn exact() {
    for rnd in DIRS {
        for (f, y, v) in [
            ("acos(1)", call!(acos(1.0, rnd)), 0.0),
            ("acosh(1)", call!(acosh(1.0, rnd)), 0.0),
            ("asin(-0)", call!(asin(-0.0, rnd)), 0.0),
            ("asinh(+0)", call!(asinh(0.0, rnd)), 0.0),
            ("atan(-0)", call!(atan(-0.0, rnd)), 0.0),
            ("atan2(+0, 1)", call2!(atan2(0.0, 1.0, rnd)), 0.0),
            ("atan2(-0, 5e-324)", call2!(atan2(-0.0, 5e-324, rnd)), 0.0),
            ("atanh(+0)", call!(atanh(0.0, rnd)), 0.0),
            ("cos(-0)", call!(cos(-0.0, rnd)), 1.0),
            ("cosh(+0)", call!(cosh(0.0, rnd)), 1.0),
            ("exp(-0)", call!(exp(-0.0, rnd)), 1.0),
            ("exp10(2)", call!(exp10(2.0, rnd)), 100.0),
            ("exp2(-1074)", call!(exp2(-1074.0, rnd)), 5e-324),
            ("exp2(1023)", call!(exp2(1023.0, rnd)), 2f64.powi(1023)),
            ("log(1)", call!(log(1.0, rnd)), 0.0),
            ("log10(100)", call!(log10(100.0, rnd)), 2.0),
            ("log2(5e-324)", call!(log2(5e-324, rnd)), -1074.0),
            ("pow(4, 0.5)", call2!(pow(4.0, 0.5, rnd)), 2.0),
            ("pow(2, -1074)", call2!(pow(2.0, -1074.0, rnd)), 5e-324),
            ("pow(+0, 0.5)", call2!(pow(0.0, 0.5, rnd)), 0.0),
            ("pow(-0, 3)", call2!(pow(-0.0, 3.0, rnd)), 0.0),
            ("pow_si(-2, 3)", call_si!(pow_si(-2.0, 3, rnd)), -8.0),
            ("pow_si(-0.5, -1)", call_si!(pow_si(-0.5, -1, rnd)), -2.0),
            (
                "pow_si(2, -1074)",
                call_si!(pow_si(2.0, -1074, rnd)),
                5e-324,
            ),
            ("pow_si(-0, 3)", call_si!(pow_si(-0.0, 3, rnd)), 0.0),
            ("sin(+0)", call!(sin(0.0, rnd)), 0.0),
            ("sinh(-0)", call!(sinh(-0.0, rnd)), 0.0),
            ("tan(+0)", call!(tan(0.0, rnd)), 0.0),
            ("tanh(-0)", call!(tanh(-0.0, rnd)), 0.0),
        ] {
            assert_eq!(y, v, "{f}, {rnd:?}");
        }
    }
}

// The overflow reading of `mpfr_round` (audit A6 of `elem-mono`). The manual's §4.6 gives the
// result of an overflow only when it is rounded to nearest, and `mpfr_round` reads the
// directed results from §4.4: a positive real above every MPFR number rounds down to the
// largest one and up to +inf, and a positive real below every MPFR number other than 0 rounds
// down to a zero and up to the least one, `2^(emin - 1)`. Checked through the first clauses
// of `exp_ok` and `sinh_ok`, `mpfr_correct emin emax real_dom exp (mpfr_exp m)` and the same
// for `sinh`, and then `get_d_ok` of the results, as `mpfr_fn!` converts them.
#[test]
fn overflow() {
    let largest = largest();
    let least = least();

    // `mpfr_round`, `RNDD, MNum y => y <> 0 /\ Rnd_DN_pt F r y`, for `r = exp(MAX)`, with `y`
    // the largest MPFR number
    let y = call!(exp(f64::MAX, RNDD));
    assert_eq!(value(&y), Num(largest.clone()));
    // `get_d_ok`, the first clause: `y` rounded down to `f64` is `f64::MAX`
    assert_eq!(get_d(&y, RNDD), f64::MAX);

    // `mpfr_round`, `RNDU, MInf false => forall g, F g -> g < r`, for `r = exp(MAX)`
    let y = call!(exp(f64::MAX, RNDU));
    assert_eq!(value(&y), Inf(false));
    // `get_d_ok`, the third clause: `mpfr_get_d m rnd (MInf s) = B754_infinity s`
    assert_eq!(get_d(&y, RNDU), f64::INFINITY);

    // `mpfr_round`, `RNDU, MNum y => y <> 0 /\ Rnd_UP_pt F r y`, for `r = sinh(-MAX)`, with
    // `y` minus the largest MPFR number
    let y = call!(sinh(-f64::MAX, RNDU));
    assert_eq!(value(&y), Num(-largest));
    // `get_d_ok`, the first clause
    assert_eq!(get_d(&y, RNDU), -f64::MAX);

    // `mpfr_round`, `RNDD, MInf true => forall g, F g -> r < g`, for `r = sinh(-MAX)`
    let y = call!(sinh(-f64::MAX, RNDD));
    assert_eq!(value(&y), Inf(true));
    // `get_d_ok`, the third clause
    assert_eq!(get_d(&y, RNDD), f64::NEG_INFINITY);

    // `mpfr_round`, `RNDD, MZero _ => Rnd_DN_pt F r 0`, for `r = exp(-MAX)`: a zero of either
    // sign
    let y = call!(exp(-f64::MAX, RNDD));
    assert!(y.is_zero(), "{y}");
    // `get_d_ok`, the second clause: a zero converts to a zero of either sign
    assert_eq!(get_d(&y, RNDD), 0.0);

    // `mpfr_round`, `RNDU, MNum y => y <> 0 /\ Rnd_UP_pt F r y`, for `r = exp(-MAX)`, with
    // `y` the least MPFR number
    let y = call!(exp(-f64::MAX, RNDU));
    assert_eq!(value(&y), Num(least));
    // `get_d_ok`, the first clause: `2^(emin - 1)` rounds up to 2^-1074 and down to a zero
    assert_eq!(get_d(&y, RNDU), 5e-324);
    assert_eq!(get_d(&y, RNDD), 0.0);
}

// `get_d_ok emin emax` at its edges, in MPFR's exponent range in this thread, and the same
// cases at the range of `rational_to_f64`, `get_d_ok (-1073) 1024` of `parse_ok`, where they
// are MPFR numbers.
#[test]
fn get_d_ok() {
    let max = f64::MAX;
    let inf = f64::INFINITY;
    // `2^1024` and `2^-1075` below are MPFR numbers only if the range is wider than
    // `range_ok` asks, as MPFR's default range is.
    let (emin, emax) = range();
    assert!(emin < -1074 && 1024 < emax, "{emin}, {emax}");

    // `(y, y rounded down to f64, y rounded up to f64, whether y is an MPFR number at the
    // range of rational_to_f64)`, for MPFR numbers `y > 0`. A rounding of 0 is a zero of
    // either sign.
    let cases = [
        // The largest `f64`, `(1 - 2^-53) * 2^1024`.
        (of_f64(max), max, max, true),
        // `2^1024`, just above it.
        (float(1, 1024), max, inf, false),
        // The largest MPFR number.
        (largest(), max, inf, false),
        // The least MPFR number, `2^(emin - 1)`.
        (least(), 0.0, sub(1), false),
        // `2^-1075`, `3 * 2^-1075` and `2^-1074` around the least positive `f64`.
        (float(1, -1075), 0.0, sub(1), false),
        (float(3, -1075), sub(1), sub(2), true),
        (float(1, -1074), sub(1), sub(1), true),
        // `(1 - 2^-53) * 2^-1073`, the largest MPFR number with the exponent -1073.
        (float((1 << 53) - 1, -1126), sub(1), sub(2), true),
        // `2^-1050 * (1 + 2^-52)`, 53 bits in the subnormal range of `f64`.
        (
            float((1 << 52) + 1, -1102),
            sub(1 << 24),
            sub((1 << 24) + 1),
            true,
        ),
        // `(1 - 2^-53) * 2^-1022`, just below `f64::MIN_POSITIVE`.
        (
            float((1 << 53) - 1, -1075),
            sub((1 << 52) - 1),
            f64::MIN_POSITIVE,
            true,
        ),
        // `f64::MIN_POSITIVE` and the `f64` just above it.
        (
            Float::with_val(PREC, f64::MIN_POSITIVE),
            f64::MIN_POSITIVE,
            f64::MIN_POSITIVE,
            true,
        ),
        (
            float((1 << 52) + 1, -1074),
            f64::from_bits((1 << 52) + 1),
            f64::from_bits((1 << 52) + 1),
            true,
        ),
    ];

    for (y, lo, hi, at_parse) in cases {
        let neg_y = Float::with_val(PREC, -&y);
        // `get_d_ok`, the first clause: `forall rnd y, y <> 0 -> mpfr_format emin emax y ->
        // mpfr_round f64_format rnd y (with_val (mpfr_get_d m rnd (MNum y)))`, for `y` and
        // `-y`
        let checks = [
            (&y, RNDD, lo),
            (&y, RNDU, hi),
            (&neg_y, RNDD, -hi),
            (&neg_y, RNDU, -lo),
        ];
        for (y, rnd, d) in checks {
            assert!(is_f64(get_d(y, rnd), d), "{y}, {rnd:?}");
            if at_parse {
                // The same in `get_d_ok (-1073) 1024` of `parse_ok`.
                let e = at_parse_range(|| get_d(y, rnd));
                assert!(is_f64(e, d), "{y}, {rnd:?}");
            }
        }
    }

    for rnd in DIRS {
        for x in [0.0f64, -0.0] {
            let y = Float::with_val(PREC, x);
            // `get_d_ok`, the second clause: `forall rnd s, exists s', mpfr_get_d m rnd
            // (MZero s) = B754_zero s'`
            assert_eq!(get_d(&y, rnd), 0.0, "{x:e}, {rnd:?}");
            assert_eq!(at_parse_range(|| get_d(&y, rnd)), 0.0, "{x:e}, {rnd:?}");
        }
        for x in [inf, -inf] {
            let y = Float::with_val(PREC, x);
            // `get_d_ok`, the third clause: `forall rnd s, mpfr_get_d m rnd (MInf s) =
            // B754_infinity s`
            assert_eq!(get_d(&y, rnd), x, "{rnd:?}");
            assert_eq!(at_parse_range(|| get_d(&y, rnd)), x, "{rnd:?}");
        }
    }
}

// `parse_ok`: `set_q_ok (-1073) 1024` and `subnormalize_ok (-1073) 1024`, with the calls of
// `rational_to_f64` in `src/parse.rs`, and `get_d_ok (-1073) 1024` of the result. The
// rationals are small (PF3 of the review of rows 14-18): `mpfr_set_q` aborts on an operand
// wider than `MPFR_PREC_MAX` bits, which `set_q_ok` leaves out.
#[test]
fn parse_ok() {
    let max = f64::MAX;
    let inf = f64::INFINITY;
    let one_3rd_dn = f64::from_bits(0x3fd5555555555555);
    let one_3rd_up = f64::from_bits(0x3fd5555555555556);

    // `(q, rnd, set_q, subnormalize)`: the rational, the direction, `q` rounded to
    // `mpfr_format (-1073) 1024` and `q` rounded to `sub_format (-1073) 1024`. A rounding of
    // 0 is a zero of either sign.
    let cases = [
        // 1, exactly, with the ternary value 0.
        (Rational::from(1), RNDD, of_f64(1.0), of_f64(1.0)),
        (Rational::from(1), RNDU, of_f64(1.0), of_f64(1.0)),
        // 1/3: `mpfr_subnormalize` keeps `x`, and its ternary value is that against `q`, not
        // 0, as that against `x` would be.
        (
            Rational::from((1, 3)),
            RNDD,
            of_f64(one_3rd_dn),
            of_f64(one_3rd_dn),
        ),
        (
            Rational::from((1, 3)),
            RNDU,
            of_f64(one_3rd_up),
            of_f64(one_3rd_up),
        ),
        // `2^-1075` and `3 * 2^-1076`, below the least MPFR number at this range,
        // `2^(emin - 1) = 2^-1074`.
        (rational(1, -1075), RNDD, of_f64(0.0), of_f64(0.0)),
        (rational(1, -1075), RNDU, of_f64(sub(1)), of_f64(sub(1))),
        (rational(3, -1076), RNDD, of_f64(0.0), of_f64(0.0)),
        (rational(3, -1076), RNDU, of_f64(sub(1)), of_f64(sub(1))),
        // `3 * 2^-1075`, just above the least positive `f64`: an MPFR number with 2 bits, so
        // exact for `mpfr_set_q`, which `mpfr_subnormalize` rounds to a multiple of `2^-1074`.
        (rational(3, -1075), RNDD, float(3, -1075), of_f64(sub(1))),
        (rational(3, -1075), RNDU, float(3, -1075), of_f64(sub(2))),
        // `2^-1060 + 2^-1100`, an MPFR number, so exact for `mpfr_set_q`, but not a multiple of
        // `2^-1074`.
        (
            rational((1 << 40) + 1, -1100),
            RNDD,
            float((1 << 40) + 1, -1100),
            of_f64(sub(1 << 14)),
        ),
        (
            rational((1 << 40) + 1, -1100),
            RNDU,
            float((1 << 40) + 1, -1100),
            of_f64(sub((1 << 14) + 1)),
        ),
        // Around `f64::MIN_POSITIVE = 2^-1022`, the threshold below which `mpfr_subnormalize`
        // keeps fewer than 53 bits: 52 bits just below it, and 53 at and above it.
        // `(1 - 2^-53) * 2^-1022`, an MPFR number, so exact for `mpfr_set_q`, which
        // `mpfr_subnormalize` rounds to 52 bits.
        (
            rational((1 << 53) - 1, -1075),
            RNDD,
            float((1 << 53) - 1, -1075),
            of_f64(sub((1 << 52) - 1)),
        ),
        (
            rational((1 << 53) - 1, -1075),
            RNDU,
            float((1 << 53) - 1, -1075),
            of_f64(f64::MIN_POSITIVE),
        ),
        // `2^-1022 - 2^-1100`, just below it, inexact for `mpfr_set_q`. Toward -inf,
        // `mpfr_subnormalize` rounds `x` again, and toward +inf, `x` is `2^-1022`, which it
        // keeps, with the nonzero ternary value of `mpfr_set_q`.
        (
            rational(1, -1022) - rational(1, -1100),
            RNDD,
            float((1 << 53) - 1, -1075),
            of_f64(sub((1 << 52) - 1)),
        ),
        (
            rational(1, -1022) - rational(1, -1100),
            RNDU,
            of_f64(f64::MIN_POSITIVE),
            of_f64(f64::MIN_POSITIVE),
        ),
        // `2^-1022 + 2^-1100`, just above it, inexact for `mpfr_set_q`. `mpfr_subnormalize`
        // keeps `x` in both directions, with the nonzero ternary value of `mpfr_set_q`.
        (
            rational(1, -1022) + rational(1, -1100),
            RNDD,
            of_f64(f64::MIN_POSITIVE),
            of_f64(f64::MIN_POSITIVE),
        ),
        (
            rational(1, -1022) + rational(1, -1100),
            RNDU,
            float((1 << 52) + 1, -1074),
            float((1 << 52) + 1, -1074),
        ),
        // `2^1024` and `-2^1024`, above and below every MPFR number at this range.
        (rational(1, 1024), RNDD, of_f64(max), of_f64(max)),
        (rational(1, 1024), RNDU, of_f64(inf), of_f64(inf)),
        (rational(-1, 1024), RNDD, of_f64(-inf), of_f64(-inf)),
        (rational(-1, 1024), RNDU, of_f64(-max), of_f64(-max)),
        // `(2^53 - 1) * 2^971`, the largest MPFR number at this range, `f64::MAX`.
        (rational((1 << 53) - 1, 971), RNDD, of_f64(max), of_f64(max)),
        (rational((1 << 53) - 1, 971), RNDU, of_f64(max), of_f64(max)),
    ];

    // Each case, and its negation in the other direction: `mpfr_format` and `sub_format` are
    // symmetric, so `-q` rounds to `-x` and `-y` there, and the cases cover both signs.
    let flip = |rnd| match rnd {
        RNDD => RNDU,
        _ => RNDD,
    };
    let cases = cases.into_iter().flat_map(|(q, rnd, x, y)| {
        [
            (q.clone(), rnd, x.clone(), y.clone()),
            (-q, flip(rnd), -x, -y),
        ]
    });

    for (q, rnd, x_ok, y_ok) in cases {
        // `rational_to_f64`, with the MPFR number and the ternary value after each call.
        let mut f = Float::new(f64::MANTISSA_DIGITS);
        let (x, t, y, u, d) = at_parse_range(|| {
            let t = unsafe { mpfr::set_q(f.as_raw_mut(), q.as_raw(), rnd) };
            let x = f.clone();
            let u = unsafe { mpfr::subnormalize(f.as_raw_mut(), t, rnd) };
            let y = f.clone();
            let d = unsafe { mpfr::get_d(f.as_raw(), rnd) };
            (x, t, y, u, d)
        });

        // `set_q_ok`: `mpfr_round (mpfr_format emin emax) rnd (Q2R q) (fst (mpfr_set_q m emin
        // emax rnd q))` and `ternary_ok (Q2R q) (fst ..) (snd ..)`
        assert_eq!(x, x_ok, "{q}, {rnd:?}");
        assert!(ternary_ok(&q, &value(&x), t), "{q}, {rnd:?}, {t}");

        // `subnormalize_ok`: `mpfr_round (sub_format emin emax) rnd r (fst (mpfr_subnormalize
        // m emin emax rnd x t))` and `ternary_ok r (fst ..) (snd ..)`, with `r = Q2R q`, the
        // real that `x` rounds
        assert_eq!(y, y_ok, "{q}, {rnd:?}");
        assert!(ternary_ok(&q, &value(&y), u), "{q}, {rnd:?}, {u}");

        // `get_d_ok`: the first clause for `y`, which is in `sub_format`, so an `f64`, or the
        // second or the third
        assert_eq!(y, d, "{q}, {rnd:?}");
    }
}
