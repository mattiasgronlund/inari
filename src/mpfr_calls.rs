// Calls to MPFR that more than one of `src/elementary.rs`, `src/parse.rs` and the tests in
// `src/elementary/mpfr_tests.rs` make, as the tests call MPFR through the same functions as
// the code. They are here, rather than in `elementary` or `parse`, so that neither of those
// modules imports the other. `rocq/theories/Model.v` transcribes `get_d`, `with_parse_range`
// and `round_rational`, as their comments say. Other code calls MPFR itself, such as
// `mpfr_fn!`, `mpfr_fn2!` and `mpfr_fn_si!` in `src/elementary.rs`, and `src/format.rs`.

use gmp_mpfr_sys::mpfr;
use rug::{Float, Rational};

// `mpfr::get_d` of the MPFR number `x`, rounded in the direction `rnd`. The functions that
// `mpfr_fn!`, `mpfr_fn2!` and `mpfr_fn_si!` in `src/elementary.rs` define, and
// `round_rational` below, convert their results with it, and `mpfr_tests` tests it.
// `rocq/theories/Model.v` transcribes it as `mpfr_get_d m rnd` in `mpfr_fn`, `mpfr_fn2`,
// `mpfr_fn_si` and `rational_to_f64`, so it has to be updated along with them.
// `rocq/theories/Mpfr.v` states what the proofs assume of `mpfr::get_d` (`get_d_ok`). A
// release build can put `get_d` and its callers in different codegen units. Without
// `#[inline]`, LLVM then first optimizes a call seeing only a declaration of `get_d`, so it
// cannot tell that the call does not unwind, and the functions that call `number_to_f64` in
// `src/parse.rs` while they hold an `NInterval` keep a landing pad that drops the
// `NInterval`.
#[inline]
pub(crate) fn get_d(x: &Float, rnd: mpfr::rnd_t) -> f64 {
    unsafe { mpfr::get_d(x.as_raw(), rnd) }
}

// `f()` at the exponent range of `rational_to_f64` in `src/parse.rs`, `emin = -1073` and
// `emax = 1024`: it saves MPFR's exponent range, sets it to that one, calls `f` and restores
// it. `mpfr_tests` calls it too, and `parse_ok` there checks the range during `f()` and after
// it. `rocq/theories/Model.v` transcribes this function as part of `rational_to_f64`, so it
// has to be updated along with it. The proof of `rational_to_f64` takes MPFR's exponent
// range to stay as this function sets it until it restores it. No other thread can change it
// in between where MPFR keeps it per thread, as the MPFR that `gmp-mpfr-sys` builds does,
// which `range_per_thread` in `src/elementary/mpfr_tests.rs` tests. A system MPFR built
// without thread-local storage, which the feature `use-system-libs` of `gmp-mpfr-sys` can
// link, keeps it global instead, and fails that test. It is `#[inline]` for the reason that
// `round_rational` is.
#[inline]
pub(crate) fn with_parse_range<T>(f: impl FnOnce() -> T) -> T {
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

// The MPFR calls of `rational_to_f64` in `src/parse.rs`: `r` rounded in the direction `rnd` to
// an MPFR number `f` of 53 bits with `mpfr::set_q`, then `f` set with `mpfr::subnormalize` to
// `r` rounded in the same direction to the numbers that an `f64` holds, which have fewer than
// 53 bits below `f64::MIN_POSITIVE`, and converted with `get_d`, all at the range that
// `with_parse_range` sets. It returns `f`, the ternary value of `mpfr::subnormalize` and the
// `f64`. `after_set_q` gets `f` and the ternary value after `mpfr::set_q`, for `parse_ok` in
// `mpfr_tests`, which calls MPFR through this function. `rational_to_f64` passes one that
// does nothing. `rocq/theories/Model.v` transcribes this function as part of
// `rational_to_f64`, so it has to be updated along with it. A release build puts the
// instances of a free generic function that is not `#[inline]` in the codegen unit of the
// module that defines it, not in that of the caller. Without `#[inline]`, this one and
// `rational_to_f64` can then be in different codegen units, and the functions that call
// `number_to_f64` in `src/parse.rs` while they hold an `NInterval` keep a landing pad that
// drops the `NInterval`, as for `get_d` above. In such a build, `#[inline]` gives each codegen
// unit that calls it a copy of its own.
#[inline]
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
