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

        // The generic backend provides `round_up_exact`, which `src/parse.rs` and
        // `src/dyadic.rs` call, and `two_prod_err` and `HAS_FMA`, which the fast paths of
        // `src/dyadic` use.
        #[allow(dead_code)] // Only these and the functions that they call are used.
        mod generic;
        pub(crate) use generic::{round_up_exact, two_prod_err, HAS_FMA};
    } else if #[cfg(feature = "force-generic")] {
        mod generic;
        pub(crate) use generic::*;
    } else if #[cfg(target_arch = "aarch64")] {
        mod aarch64;
        pub(crate) use aarch64::*;

        // The generic backend provides `round_up_exact`, which `src/parse.rs` and
        // `src/dyadic.rs` call, and `two_prod_err` and `HAS_FMA`, which the fast paths of
        // `src/dyadic` use.
        #[allow(dead_code)] // Only these and the functions that they call are used.
        mod generic;
        pub(crate) use generic::{round_up_exact, two_prod_err, HAS_FMA};
    } else if #[cfg(target_arch = "x86_64")] {
        mod x86_64;
        pub(crate) use x86_64::*;

        // The generic backend provides the slow paths and the scalar operations of
        // `fma` and `sse42`, and is tested against whichever backend the target
        // selects. `src/parse.rs` and `src/dyadic.rs` call its `round_up_exact`, and the fast
        // paths of `src/dyadic` its `two_prod_err` and `HAS_FMA`.
        //
        // Only part of it is used. Under `fma` and `sse42`: the functions that they call
        // (`add_ru`, `div_ru`, `mul_add_ru`, `mul_ru`, `sqrt_rd_ru`, `sqrt1_rd`, `sqrt1_ru`
        // and `sub1_ru`) and the functions these call, among them `round_up_exact`, `pow2`
        // and `two_prod_err`; the tests also use `round_ties_even` and `sub_ru`. Under
        // `avx512f`: only `round_up_exact`, `pow2`, `two_prod_err` and `split`; the tests use
        // `add_ru`, `sub_ru`, `sub1_ru`, `round_ties_even`, `round_up_exact`, the `*_impl`
        // functions and the functions these call.
        #[allow(dead_code)]
        mod generic;
        pub(crate) use generic::{round_up_exact, two_prod_err, HAS_FMA};
        #[cfg(test)]
        mod differential_tests;
    } else if #[cfg(all(target_arch = "wasm32", target_feature = "simd128"))] {
        mod wasm32;
        pub(crate) use wasm32::*;

        // The generic backend provides the slow paths and the scalar operations of
        // `wasm32`, and is tested against it. `src/parse.rs` and `src/dyadic.rs` call its
        // `round_up_exact`, and the fast paths of `src/dyadic` its `two_prod_err` and
        // `HAS_FMA`.
        //
        // Only part of it is used: the functions that `wasm32` calls (`add_ru`, `div_ru`,
        // `mul_add_ru`, `mul_ru`, `sqrt_rd_ru`, `sqrt1_rd`, `sqrt1_ru` and `sub1_ru`) and the
        // functions these call, among them `round_up_exact` and `pow2`, and `two_prod_err`
        // and `split`; the tests also use `round_ties_even` and `sub_ru`.
        #[allow(dead_code)]
        mod generic;
        pub(crate) use generic::{round_up_exact, two_prod_err, HAS_FMA};
        #[cfg(test)]
        mod differential_tests;
    } else {
        mod generic;
        pub(crate) use generic::*;
    }
}
