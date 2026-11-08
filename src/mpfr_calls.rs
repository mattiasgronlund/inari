// The functions that compute the bounds of the elementary functions of `src/elementary.rs`,
// `<f>_rd` and `<f>_ru`, the real function rounded down and up to an `f64`. They have two
// backends with the same names and arguments:
//
// - `src/mpfr_calls/kernel.rs`, which calls the dyadic kernel of `src/dyadic.rs`. No `cfg`
//   gates it, and it is the one that the library uses.
// - `src/mpfr_calls/mpfr.rs`, which calls MPFR through `rug::Float` and `gmp_mpfr_sys::mpfr`.
//   Only the tests compile it, on the platforms where `gmp-mpfr-sys` builds GMP and MPFR (the
//   `cfg` of the dev-dependencies in `Cargo.toml`), and they reach it as `mpfr_calls::mpfr`.
//   Its `round_rational` and `with_parse_range`, the MPFR rounding of a rational to an `f64`,
//   are what `src/parse/diff_tests.rs` checks `rational_to_f64` of `src/parse.rs` against,
//   and its `fmt_bound_mpfr`, the MPFR printing of a bound of an interval, is what
//   `src/format/diff_tests.rs` checks `bound` of `src/format.rs` against. The tests in
//   `src/elementary/mpfr_tests.rs` call MPFR through its `get_d` and the `let` arms of its
//   macros, through `round_rational` and `with_parse_range`, and also directly.
//
// `src/parse.rs` and `src/format.rs` call neither backend. `rocq/theories/DyPoint.v` models
// the functions of the kernel backend, and `rocq/theories/Model.v` transcribes `get_d` and the
// functions that the macros of the MPFR backend define, as their comments say, and models none
// of `round_rational`, `with_parse_range` and `fmt_bound_mpfr`.

mod kernel;
pub(crate) use self::kernel::*;

#[cfg(all(
    test,
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
pub(crate) mod mpfr;

#[cfg(all(
    test,
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
mod tests;
