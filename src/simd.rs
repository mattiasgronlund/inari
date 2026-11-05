// A SIMD vector [x0; x1] stored in a register is usually depicted as:
//
//   +----------------+----------------+
//   |       x1       |       x0       |
//   +----------------+----------------+
//   |127           64|63             0|
//
//   r[63:0] = x0, r[127:64] = x1.

cfg_if::cfg_if! {
    if #[cfg(docsrs)] {
        mod unimplemented;
        pub(crate) use unimplemented::*;

        // The generic backend provides `round_up_exact`, which `src/parse.rs` calls, and so
        // does `src/dyadic.rs`, which only the tests compile.
        #[cfg(any(feature = "gmp", test))]
        #[allow(dead_code)] // Only `round_up_exact` and `pow2`, which it calls, are used.
        mod generic;
        #[cfg(any(feature = "gmp", test))]
        pub(crate) use generic::round_up_exact;
    } else if #[cfg(feature = "force-generic")] {
        mod generic;
        pub(crate) use generic::*;
    } else if #[cfg(target_arch = "aarch64")] {
        mod aarch64;
        pub(crate) use aarch64::*;

        // The generic backend provides `round_up_exact`, which `src/parse.rs` calls, and so
        // does `src/dyadic.rs`, which only the tests compile.
        #[cfg(any(feature = "gmp", test))]
        #[allow(dead_code)] // Only `round_up_exact` and `pow2`, which it calls, are used.
        mod generic;
        #[cfg(any(feature = "gmp", test))]
        pub(crate) use generic::round_up_exact;
    } else if #[cfg(target_arch = "x86_64")] {
        mod x86_64;
        pub(crate) use x86_64::*;

        // The generic backend provides the slow paths and the scalar operations of
        // `fma` and `sse42`, and is tested against whichever backend the target
        // selects. `src/parse.rs` calls its `round_up_exact`, and so does `src/dyadic.rs`,
        // which only the tests compile.
        //
        // Only part of it is used. Under `fma` and `sse42`, with or without `gmp`: the
        // functions that they call (`add_ru`, `div_ru`, `mul_add_ru`, `mul_ru`,
        // `sqrt_rd_ru`, `sqrt1_rd`, `sqrt1_ru` and `sub1_ru`) and the functions these call,
        // among them `round_up_exact` and `pow2`; the tests also use `round_ties_even` and
        // `sub_ru`. Under `avx512f`: nothing without `gmp`, and only `round_up_exact` and
        // `pow2` with it; the tests use `add_ru`, `sub_ru`, `sub1_ru`, `round_ties_even`,
        // `round_up_exact`, the `*_impl` functions and the functions these call.
        #[allow(dead_code)]
        mod generic;
        #[cfg(any(feature = "gmp", test))]
        pub(crate) use generic::round_up_exact;
        #[cfg(test)]
        mod differential_tests;
    } else if #[cfg(all(target_arch = "wasm32", target_feature = "simd128"))] {
        mod wasm32;
        pub(crate) use wasm32::*;

        // The generic backend provides the slow paths and the scalar operations of
        // `wasm32`, and is tested against it. `src/parse.rs` calls its `round_up_exact`, and
        // so does `src/dyadic.rs`, which only the tests compile.
        //
        // Only part of it is used: the functions that `wasm32` calls (`add_ru`, `div_ru`,
        // `mul_add_ru`, `mul_ru`, `sqrt_rd_ru`, `sqrt1_rd`, `sqrt1_ru` and `sub1_ru`) and the
        // functions these call, among them `round_up_exact` and `pow2`; the tests also use
        // `round_ties_even` and `sub_ru`.
        #[allow(dead_code)]
        mod generic;
        #[cfg(any(feature = "gmp", test))]
        pub(crate) use generic::round_up_exact;
        #[cfg(test)]
        mod differential_tests;
    } else {
        mod generic;
        pub(crate) use generic::*;
    }
}
