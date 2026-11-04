// inari's calls into MPFR, which it makes through `rug::Float` and `gmp_mpfr_sys::mpfr`: the
// functions that compute the bounds of the elementary functions of `src/elementary.rs`, which
// `mpfr_fn!`, `mpfr_fn2!` and `mpfr_fn_si!` define; `fmt_bounds`, which prints the bounds of
// an interval for `src/format.rs`; and `assert_thread_safe`, `get_d` and `mpfr_printf`, which
// those call. `src/parse.rs` calls neither MPFR nor GMP. Only the tests compile
// `round_rational` and `with_parse_range`, the MPFR rounding of a rational to an `f64`
// against which `src/parse/diff_tests.rs` checks `rational_to_f64` of `src/parse.rs`. The
// tests in `src/elementary/mpfr_tests.rs` call MPFR through `get_d` and the `let` arms of the
// macros, as the code does, through `round_rational` and `with_parse_range`, as
// `src/parse/diff_tests.rs` does, and also directly. `rocq/theories/Model.v` transcribes
// `get_d` and the functions that the macros define, as their comments say, and models
// neither `round_rational` nor `with_parse_range`.
//
// MPFR is the only backend, in `src/mpfr_calls/mpfr.rs`. The `cfg_if!` below compiles it with
// the feature `gmp`, which is also the only feature with which `src/lib.rs` compiles this
// module.

cfg_if::cfg_if! {
    if #[cfg(feature = "gmp")] {
        mod mpfr;
        pub(crate) use self::mpfr::*;
    }
}
