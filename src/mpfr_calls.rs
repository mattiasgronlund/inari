// inari's calls into MPFR, which it makes through `rug::Float` and `gmp_mpfr_sys::mpfr`: the
// functions that compute the bounds of the elementary functions of `src/elementary.rs`, which
// `mpfr_fn!`, `mpfr_fn2!` and `mpfr_fn_si!` define; `round_rational`, through which
// `rational_to_f64` in `src/parse.rs` rounds a rational to an `f64`; `fmt_bounds`, which
// prints the bounds of an interval for `src/format.rs`; and `assert_thread_safe`, `get_d`,
// `with_parse_range` and `mpfr_printf`, which those call. The tests in
// `src/elementary/mpfr_tests.rs` call MPFR through `get_d`, `with_parse_range`,
// `round_rational` and the `let` arms of the macros, as the code does, and also directly.
// Other than that, `src/parse.rs` names the MPFR types `mpfr::rnd_t` and `mpfr::prec_t`, and
// drops the MPFR number that `round_rational` returns; it calls GMP itself, for its big
// integers and rationals. `rocq/theories/Model.v` transcribes `get_d`, `with_parse_range`,
// `round_rational` and the functions that the macros define, as their comments say.
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
