// The MPFR backend of `src/mpfr_calls.rs`, which only the tests compile. `src/mpfr_calls.rs`
// says what calls it.

use gmp_mpfr_sys::mpfr::{
    self,
    rnd_t::{RNDD, RNDN, RNDU},
};
use rug::{Float, Rational};
use std::{
    ffi::CString,
    os::raw::{c_char, c_int},
};

// Panics unless the linked MPFR is built thread-safe, as the MPFR that `gmp-mpfr-sys` builds
// is. A system MPFR, which the feature `use-system-libs` of `gmp-mpfr-sys` links, need not be,
// and one that is not keeps its flags and its exponent range global rather than per thread
// (§4.7 "Memory Handling" of the MPFR manual), and its caches of constants such as π too
// (`MPFR_CACHE_ATTR` in MPFR's `mpfr-impl.h`). There, two threads that call MPFR at once can
// write the same flags and the same cache, and another thread, such as another test, can
// change the range that `with_parse_range` sets before it restores it. The `let` arms of
// `mpfr_fn!`, `mpfr_fn2!` and `mpfr_fn_si!`, all below, call this before their MPFR call, and
// `with_parse_range` and `fmt_bound_mpfr` call it too, so that with such an MPFR, a test
// panics on its first MPFR call through any of them, whether or not it runs more than one
// thread. `get_d` does not call it, and the MPFR calls that the tests make themselves, not
// through this file, are not checked. The library calls no MPFR. `mpfr::buildopt_tls_p` (§5.12
// "Miscellaneous Functions") returns whether MPFR was built thread-safe, which is fixed when
// MPFR is built, so calling it every time gives the same answer as calling it once.
// `rocq/theories/Model.v` leaves this function out of `mpfr_fn`, `mpfr_fn2` and `mpfr_fn_si`,
// as it either panics or does nothing, so a change that makes it do anything else has to be
// modelled there.
pub(crate) fn assert_thread_safe() {
    assert!(
        unsafe { mpfr::buildopt_tls_p() } != 0,
        "inari needs an MPFR built thread-safe, and the linked one is not; the feature \
         `use-system-libs` of `gmp-mpfr-sys` links a system MPFR, which need not be"
    );
}

// `mpfr::get_d` of the MPFR number `x`, rounded in the direction `rnd`. The functions that
// `mpfr_fn!`, `mpfr_fn2!` and `mpfr_fn_si!` below define convert their results with it, as
// `round_rational` does, and `mpfr_tests` tests it.
// `rocq/theories/Model.v` transcribes it as `mpfr_get_d m rnd` in `mpfr_fn`, `mpfr_fn2` and
// `mpfr_fn_si`, so it has to be updated along with them.
// `rocq/theories/Mpfr.v` states what the proofs assume of `mpfr::get_d` (`get_d_ok`). A
// release build can put `get_d` and its callers in different codegen units, and `#[inline]`
// gives each codegen unit that calls it a copy of its own.
#[inline]
pub(crate) fn get_d(x: &Float, rnd: mpfr::rnd_t) -> f64 {
    unsafe { mpfr::get_d(x.as_raw(), rnd) }
}

// `f()` at the exponent range `emin = -1073`, `emax = 1024`, at which `round_rational` below
// rounds to the numbers that an `f64` holds: it saves MPFR's exponent range, sets it to that
// one, calls `f` and restores it. `mpfr_tests` calls it too, and `round_rational_oracle` there
// checks the range during `f()` and after it. `round_rational` takes MPFR's exponent range to
// stay as this function sets it until it restores it. No
// other thread, such as another test, can change it in between where MPFR keeps it per
// thread, as the MPFR that `gmp-mpfr-sys` builds does, which `range_per_thread` in
// `src/elementary/mpfr_tests.rs` tests. A system MPFR built without thread-local storage,
// which the feature `use-system-libs` of `gmp-mpfr-sys` can link, keeps it global instead,
// and fails that test, and with such an MPFR, `assert_thread_safe` above panics before this
// function reads or sets the range.
pub(crate) fn with_parse_range<T>(f: impl FnOnce() -> T) -> T {
    assert_thread_safe();
    let (orig_emin, orig_emax) = unsafe { (mpfr::get_emin(), mpfr::get_emax()) };
    unsafe {
        mpfr::set_emin((f64::MIN_EXP - (f64::MANTISSA_DIGITS as i32) + 1).into());
        mpfr::set_emax(f64::MAX_EXP.into());
    }
    let x = f();
    unsafe {
        mpfr::set_emin(orig_emin);
        mpfr::set_emax(orig_emax);
    }
    x
}

// The MPFR calls with which `rational_to_f64` in `src/parse.rs` rounded a rational to an
// `f64` before it had its own rounding, and against which `src/parse/diff_tests.rs` checks
// it: `r` rounded in the direction `rnd` to an MPFR number `f` of 53 bits with
// `mpfr::set_q`, then `f` set with `mpfr::subnormalize` to `r` rounded in the same direction
// to the numbers that an `f64` holds, which have fewer than 53 bits below
// `f64::MIN_POSITIVE`, and converted with `get_d`, all at the range that `with_parse_range`
// sets. It returns `f`, the ternary value of `mpfr::subnormalize` and the `f64`.
// `after_set_q` gets `f` and the ternary value after `mpfr::set_q`, for
// `round_rational_oracle` in `mpfr_tests`, which checks this function against what the MPFR
// manual states of `mpfr_set_q`, `mpfr_subnormalize` and `mpfr_get_d`.
// `src/parse/diff_tests.rs` passes one that does nothing.
pub(crate) fn round_rational(
    r: &Rational,
    rnd: mpfr::rnd_t,
    after_set_q: impl FnOnce(&Float, i32),
) -> (Float, i32, f64) {
    let mut f = Float::new(f64::MANTISSA_DIGITS);
    let (t, d) = with_parse_range(|| {
        let t = unsafe { mpfr::set_q(f.as_raw_mut(), r.as_raw(), rnd) };
        after_set_q(&f, t);
        let t = unsafe { mpfr::subnormalize(f.as_raw_mut(), t, rnd) };
        (t, get_d(&f, rnd))
    });
    (f, t, d)
}

// `rocq/theories/Model.v` transcribes the functions that this macro defines, as `mpfr_fn`
// of an abstract MPFR function in the fields of `mpfr_point`, for the proofs of the
// functions of `src/elementary.rs` with this backend in `rocq/theories/Elem.v`,
// `rocq/theories/ClosedDom.v`, `rocq/theories/Atanh.v`, `rocq/theories/Cosh.v`,
// `rocq/theories/Cos.v`, `rocq/theories/Sin.v` and `rocq/theories/Tan.v`, and of `quadrant`
// there, which calls `sin_rd` and `cos_ru`, in `rocq/theories/TrigQuad.v`, for `mpfr_acos_c`
// and the other theorems of `rocq/theories/MpfrPoint.v` about them, and for
// `mpfr_point_of_point` in `rocq/theories/OfPoint.v`, so it has to be updated along with it.
// `rocq/theories/Mpfr.v` states what those proofs assume of the MPFR functions and of
// `mpfr::get_d`, and `mpfr_tests` tests the linked MPFR against it.
macro_rules! mpfr_fn {
    ($mpfr_f:ident, $f_rd:ident, $f_ru:ident) => {
        pub(crate) fn $f_rd(x: f64) -> f64 {
            mpfr_fn!(let x = $mpfr_f(x, RNDD));
            get_d(&x, RNDD)
        }

        pub(crate) fn $f_ru(x: f64) -> f64 {
            mpfr_fn!(let x = $mpfr_f(x, RNDU));
            get_d(&x, RNDU)
        }
    };

    // Calls `assert_thread_safe` above, then binds `$z` to the MPFR number that the functions
    // above convert with `get_d`: `x` as an MPFR number of 53 bits, set to `$mpfr_f` of it
    // rounded in the direction `rnd`.
    (let $z:ident = $mpfr_f:ident($x:expr, $rnd:expr)) => {
        crate::mpfr_calls::mpfr::assert_thread_safe();
        let x: f64 = $x;
        let mut $z = Float::with_val(f64::MANTISSA_DIGITS, x);
        let rnd = $rnd;
        unsafe {
            mpfr::$mpfr_f($z.as_raw_mut(), $z.as_raw(), rnd);
        }
    };

    // That MPFR number as a value. `mpfr_tests` calls MPFR through this arm.
    ($mpfr_f:ident($x:expr, $rnd:expr)) => {{
        mpfr_fn!(let x = $mpfr_f($x, $rnd));
        x
    }};
}
// For `mpfr_tests`, which calls MPFR through the arms of this macro and of the two below.
pub(crate) use mpfr_fn;

// `rocq/theories/Model.v` transcribes the functions that this macro defines, as `mpfr_fn2`
// of an abstract MPFR function in the fields of `mpfr_point`, for the proofs of
// `(Dec)Interval::atan2` in `rocq/theories/Atan2.v` and of `(Dec)Interval::pow` in
// `rocq/theories/Pow.v`, for `mpfr_atan2_c` and `mpfr_pow_c` in `rocq/theories/MpfrPoint.v`
// and for `mpfr_point_of_point` in `rocq/theories/OfPoint.v`, so it has to be updated along
// with it.
// `rocq/theories/Mpfr.v` states what those proofs assume of `mpfr::atan2`, `mpfr::pow` and
// `mpfr::get_d`.
macro_rules! mpfr_fn2 {
    ($mpfr_f:ident, $f_rd:ident, $f_ru:ident) => {
        pub(crate) fn $f_rd(x: f64, y: f64) -> f64 {
            mpfr_fn2!(let x = $mpfr_f(x, y, RNDD));
            get_d(&x, RNDD)
        }

        pub(crate) fn $f_ru(x: f64, y: f64) -> f64 {
            mpfr_fn2!(let x = $mpfr_f(x, y, RNDU));
            get_d(&x, RNDU)
        }
    };

    // The same as for `mpfr_fn!`, with `y` as an MPFR number of 53 bits too. Like `$z`, it
    // lives to the end of the caller's block, so the functions above clear it after `get_d`.
    (let $z:ident = $mpfr_f:ident($x:expr, $y:expr, $rnd:expr)) => {
        crate::mpfr_calls::mpfr::assert_thread_safe();
        let (x, y): (f64, f64) = ($x, $y);
        let mut $z = Float::with_val(f64::MANTISSA_DIGITS, x);
        let y = Float::with_val(f64::MANTISSA_DIGITS, y);
        let rnd = $rnd;
        unsafe {
            mpfr::$mpfr_f($z.as_raw_mut(), $z.as_raw(), y.as_raw(), rnd);
        }
    };

    ($mpfr_f:ident($x:expr, $y:expr, $rnd:expr)) => {{
        mpfr_fn2!(let x = $mpfr_f($x, $y, $rnd));
        x
    }};
}
pub(crate) use mpfr_fn2;

// `rocq/theories/Model.v` transcribes the functions that this macro defines, as `mpfr_fn_si`
// of an abstract MPFR function in the field `p_pown` of `mpfr_point`, with the `i32` `y` as
// an integer, which `y.into()` converts to a `c_long` exactly, for the proofs of
// `(Dec)Interval::powi` in `rocq/theories/Powi.v`, for `mpfr_pown_c` in
// `rocq/theories/MpfrPoint.v` and for `mpfr_point_of_point` in `rocq/theories/OfPoint.v`, so
// it has to be updated along with it.
// `rocq/theories/Mpfr.v` states what those proofs assume of `mpfr::pow_si` and of
// `mpfr::get_d`.
macro_rules! mpfr_fn_si {
    ($mpfr_f:ident, $f_rd:ident, $f_ru:ident) => {
        pub(crate) fn $f_rd(x: f64, y: i32) -> f64 {
            mpfr_fn_si!(let x = $mpfr_f(x, y, RNDD));
            get_d(&x, RNDD)
        }

        pub(crate) fn $f_ru(x: f64, y: i32) -> f64 {
            mpfr_fn_si!(let x = $mpfr_f(x, y, RNDU));
            get_d(&x, RNDU)
        }
    };

    // The same as for `mpfr_fn!`, with the `i32` `y` passed as a `c_long`.
    (let $z:ident = $mpfr_f:ident($x:expr, $y:expr, $rnd:expr)) => {
        crate::mpfr_calls::mpfr::assert_thread_safe();
        let (x, y): (f64, i32) = ($x, $y);
        let mut $z = Float::with_val(f64::MANTISSA_DIGITS, x);
        let rnd = $rnd;
        unsafe {
            mpfr::$mpfr_f($z.as_raw_mut(), $z.as_raw(), y.into(), rnd);
        }
    };

    ($mpfr_f:ident($x:expr, $y:expr, $rnd:expr)) => {{
        mpfr_fn_si!(let x = $mpfr_f($x, $y, $rnd));
        x
    }};
}
pub(crate) use mpfr_fn_si;

mpfr_fn!(acos, acos_rd, acos_ru);
mpfr_fn!(acosh, acosh_rd, acosh_ru);
mpfr_fn!(asin, asin_rd, asin_ru);
mpfr_fn!(asinh, asinh_rd, asinh_ru);
mpfr_fn!(atan, atan_rd, atan_ru);
mpfr_fn2!(atan2, atan2_rd, atan2_ru);
mpfr_fn!(atanh, atanh_rd, atanh_ru);
mpfr_fn!(cos, cos_rd, cos_ru);
mpfr_fn!(cosh, cosh_rd, cosh_ru);
mpfr_fn!(exp, exp_rd, exp_ru);
mpfr_fn!(exp10, exp10_rd, exp10_ru);
mpfr_fn!(exp2, exp2_rd, exp2_ru);
mpfr_fn!(log, ln_rd, ln_ru);
mpfr_fn!(log10, log10_rd, log10_ru);
mpfr_fn!(log2, log2_rd, log2_ru);
mpfr_fn2!(pow, pow_rd, pow_ru);
mpfr_fn_si!(pow_si, pown_rd, pown_ru);
mpfr_fn!(sin, sin_rd, sin_ru);
mpfr_fn!(sinh, sinh_rd, sinh_ru);
mpfr_fn!(tan, tan_rd, tan_ru);
mpfr_fn!(tanh, tanh_rd, tanh_ru);

// `z` set by `call` to an MPFR function of it rounded to nearest, ties to even, then rounded
// to the numbers that an `f64` holds, as an `f64`. `call` returns the ternary value of the
// MPFR function. Rounding to nearest at 53 bits in MPFR's default exponent range and then with
// `get_d` would round twice below `f64::MIN_POSITIVE`, where an `f64` has fewer than 53 bits,
// and a value just off a midpoint of those numbers could round to the midpoint first and
// then to the even neighbour on the wrong side. So `call` rounds once at the range that
// `with_parse_range` sets, where MPFR's overflow and underflow are those of an `f64`, then
// `mpfr::subnormalize` rounds `z` to the bits that an `f64` has at its exponent from that
// ternary value, as `round_rational` does (§5.13 "Exception Related Functions" of the MPFR
// manual shows this use for the IEEE 754 binary64 format), and `get_d` converts it exactly.
// Every `f64` argument is in that range, as the manual asks of the inputs.
fn round_near(z: &mut Float, call: impl FnOnce(&mut Float) -> c_int) -> f64 {
    with_parse_range(|| {
        let t = call(z);
        unsafe { mpfr::subnormalize(z.as_raw_mut(), t, RNDN) };
        get_d(z, RNDN)
    })
}

// `$mpfr_f` rounded to nearest, ties to even, to an `f64`, against which `src/cr.rs` tests its
// functions rounded to nearest, with the arguments of `mpfr_fn!`, `mpfr_fn2!` and
// `mpfr_fn_si!`: `x`, then `y` as an `f64` or an `i32` for the arms with `f64` and `i32`, so
// that `atan2_rn(y, x)` is atan2(y, x), as `mpfr::atan2` takes `y` first. Only the tests use
// the functions that this macro defines, and `rocq/theories/Model.v` transcribes none of them,
// unlike those of `mpfr_fn!`, `mpfr_fn2!` and `mpfr_fn_si!`.
macro_rules! mpfr_near {
    ($mpfr_f:ident, $f_rn:ident) => {
        pub(crate) fn $f_rn(x: f64) -> f64 {
            let mut z = Float::with_val(f64::MANTISSA_DIGITS, x);
            round_near(&mut z, |z| unsafe {
                mpfr::$mpfr_f(z.as_raw_mut(), z.as_raw(), RNDN)
            })
        }
    };

    ($mpfr_f:ident, $f_rn:ident, f64) => {
        pub(crate) fn $f_rn(x: f64, y: f64) -> f64 {
            let mut z = Float::with_val(f64::MANTISSA_DIGITS, x);
            let y = Float::with_val(f64::MANTISSA_DIGITS, y);
            round_near(&mut z, |z| unsafe {
                mpfr::$mpfr_f(z.as_raw_mut(), z.as_raw(), y.as_raw(), RNDN)
            })
        }
    };

    // `y.into()` converts the `i32` `y` to a `c_long` exactly.
    ($mpfr_f:ident, $f_rn:ident, i32) => {
        pub(crate) fn $f_rn(x: f64, y: i32) -> f64 {
            let mut z = Float::with_val(f64::MANTISSA_DIGITS, x);
            round_near(&mut z, |z| unsafe {
                mpfr::$mpfr_f(z.as_raw_mut(), z.as_raw(), y.into(), RNDN)
            })
        }
    };
}

mpfr_near!(acos, acos_rn);
mpfr_near!(acosh, acosh_rn);
mpfr_near!(asin, asin_rn);
mpfr_near!(asinh, asinh_rn);
mpfr_near!(atan, atan_rn);
mpfr_near!(atan2, atan2_rn, f64);
mpfr_near!(atanh, atanh_rn);
mpfr_near!(cos, cos_rn);
mpfr_near!(cosh, cosh_rn);
mpfr_near!(exp, exp_rn);
mpfr_near!(exp10, exp10_rn);
mpfr_near!(exp2, exp2_rn);
mpfr_near!(log, ln_rn);
mpfr_near!(log10, log10_rn);
mpfr_near!(log2, log2_rn);
mpfr_near!(pow, pow_rn, f64);
mpfr_near!(pow_si, pown_rn, i32);
mpfr_near!(sin, sin_rn);
mpfr_near!(sinh, sinh_rn);
mpfr_near!(tan, tan_rn);
mpfr_near!(tanh, tanh_rn);

// The bound `x` of an interval as inari printed it with MPFR before it had digits of its own,
// against which `src/format/diff_tests.rs` checks `bound` of `src/format.rs`: rounded toward
// +∞ if `up` and toward -∞ otherwise by `mpfr::asprintf`, with the conversion `conv` (`'f'`,
// `'e'` or `'a'`, as in C's `printf`) and `prec` digits after the point, or MPFR's default for
// `conv` if `prec` is `None`, and an infinite `x` as `-inf` or `inf`. It calls
// `assert_thread_safe` before the MPFR call. It reads all the `len` bytes that MPFR wrote,
// where inari used to stop at the first NUL, so that a NUL that MPFR writes in a digit (see
// `mpfr_bumps_exact` in `src/format/diff_tests.rs`) shows.
pub(crate) fn fmt_bound_mpfr(x: f64, prec: Option<usize>, conv: char, up: bool) -> String {
    assert!(!x.is_nan());
    if x.is_infinite() {
        return String::from(if x < 0.0 { "-inf" } else { "inf" });
    }
    let prec = match prec {
        Some(p) => format!(".{}", p),
        None => String::new(),
    };
    let template = format!("%{}R{}{}", prec, if up { 'U' } else { 'D' }, conv);
    assert_thread_safe();
    let f = Float::with_val(f64::MANTISSA_DIGITS, x);
    let mut p: *mut c_char = std::ptr::null_mut();
    let c_template = CString::new(template).unwrap();
    let bytes = unsafe {
        let len = mpfr::asprintf(&mut p, c_template.as_ptr(), f.as_raw());
        assert!(len >= 0);
        let bytes = std::slice::from_raw_parts(p as *const u8, len as usize).to_vec();
        mpfr::free_str(p);
        bytes
    };
    String::from_utf8(bytes).unwrap()
}
