use crate::dyadic;

// Test-only: in a test that has switched to MPFR with `with_mpfr` of
// `src/mpfr_calls/tests.rs`, the function `$f` that the macros below define returns `$f` of the
// MPFR backend `src/mpfr_calls/mpfr.rs` instead, so that the test can compute an elementary
// function of `src/elementary.rs` with either backend and compare the two. The switch is per
// thread, so no other test sees it. This macro expands to nothing outside the tests, and in the
// tests on a platform without the MPFR backend, so that the functions that the library uses,
// which `rocq/theories/DyPoint.v` models, are only the calls of the kernel after it.
macro_rules! mpfr_in_tests {
    ($f:ident($($x:ident),*)) => {
        #[cfg(all(
            test,
            target_pointer_width = "64",
            any(target_os = "linux", target_os = "macos")
        ))]
        if super::tests::use_mpfr() {
            return super::mpfr::$f($($x),*);
        }
    };
}

// The functions that compute the bounds of the elementary functions of `src/elementary.rs`:
// `$f_rd(x)` and `$f_ru(x)` are `dyadic::$f(x, up)` of `src/dyadic.rs` with `up` false and
// true, the real function at `x` rounded down and up (`src/dyadic.rs` says what `ziv` returns
// at its cap). They have the names and the arguments of the functions of
// `src/mpfr_calls/mpfr.rs`, the MPFR backend that the tests compare them with.
// `rocq/theories/DyPoint.v` models the functions that this macro defines as `kernel_field` of
// the function `<f>_dir_with ziv_strict` of `rocq/theories/Model.v` that transcribes
// `dyadic::$f`, in the fields of `kernel_point`, for the theorems about `kernel_point` in
// `rocq/theories/DyPoint.v` and `rocq/theories/DyPointDec.v` and the constructors
// `made_kernel_<f>` and `dmade_kernel_<f>` of `rocq/theories/Valid.v`, so it has to be updated
// along with them.
macro_rules! kernel_fn {
    ($f:ident, $f_rd:ident, $f_ru:ident) => {
        pub(crate) fn $f_rd(x: f64) -> f64 {
            mpfr_in_tests!($f_rd(x));
            dyadic::$f(x, false)
        }

        pub(crate) fn $f_ru(x: f64) -> f64 {
            mpfr_in_tests!($f_ru(x));
            dyadic::$f(x, true)
        }
    };
}

// The same for a function of two `f64`s, in the order of `mpfr_fn2!`: `atan2_rd(y, x)` and
// `pow_rd(x, y)`. `rocq/theories/DyPoint.v` models them with `kernel_field2`.
macro_rules! kernel_fn2 {
    ($f:ident, $f_rd:ident, $f_ru:ident) => {
        pub(crate) fn $f_rd(x: f64, y: f64) -> f64 {
            mpfr_in_tests!($f_rd(x, y));
            dyadic::$f(x, y, false)
        }

        pub(crate) fn $f_ru(x: f64, y: f64) -> f64 {
            mpfr_in_tests!($f_ru(x, y));
            dyadic::$f(x, y, true)
        }
    };
}

// The same for a function of an `f64` and an `i32`, as `mpfr_fn_si!`.
// `rocq/theories/DyPoint.v` models them with `kernel_field_z`, with the `i32` as an integer.
macro_rules! kernel_fn_si {
    ($f:ident, $f_rd:ident, $f_ru:ident) => {
        pub(crate) fn $f_rd(x: f64, y: i32) -> f64 {
            mpfr_in_tests!($f_rd(x, y));
            dyadic::$f(x, y, false)
        }

        pub(crate) fn $f_ru(x: f64, y: i32) -> f64 {
            mpfr_in_tests!($f_ru(x, y));
            dyadic::$f(x, y, true)
        }
    };
}

kernel_fn!(acos, acos_rd, acos_ru);
kernel_fn!(acosh, acosh_rd, acosh_ru);
kernel_fn!(asin, asin_rd, asin_ru);
kernel_fn!(asinh, asinh_rd, asinh_ru);
kernel_fn!(atan, atan_rd, atan_ru);
kernel_fn2!(atan2, atan2_rd, atan2_ru);
kernel_fn!(atanh, atanh_rd, atanh_ru);
kernel_fn!(cos, cos_rd, cos_ru);
kernel_fn!(cosh, cosh_rd, cosh_ru);
kernel_fn!(exp, exp_rd, exp_ru);
kernel_fn!(exp10, exp10_rd, exp10_ru);
kernel_fn!(exp2, exp2_rd, exp2_ru);
kernel_fn!(ln, ln_rd, ln_ru);
kernel_fn!(log10, log10_rd, log10_ru);
kernel_fn!(log2, log2_rd, log2_ru);
kernel_fn2!(pow, pow_rd, pow_ru);
kernel_fn_si!(pown, pown_rd, pown_ru);
kernel_fn!(sin, sin_rd, sin_ru);
kernel_fn!(sinh, sinh_rd, sinh_ru);
kernel_fn!(tan, tan_rd, tan_ru);
kernel_fn!(tanh, tanh_rd, tanh_ru);
