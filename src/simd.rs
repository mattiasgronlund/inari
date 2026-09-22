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
    } else if #[cfg(feature = "force-generic")] {
        mod generic;
        pub(crate) use generic::*;
    } else if #[cfg(target_arch = "aarch64")] {
        mod aarch64;
        pub(crate) use aarch64::*;
    } else if #[cfg(target_arch = "x86_64")] {
        mod x86_64;
        pub(crate) use x86_64::*;

        // The generic backend provides the square root of `avx_fma`, and is tested
        // against the hardware backend.
        #[allow(dead_code)] // Only the square root and, in tests, the rounding functions are used.
        mod generic;
        #[cfg(test)]
        mod differential_tests;
    } else if #[cfg(all(target_arch = "wasm32", target_feature = "simd128"))] {
        mod wasm32;
        pub(crate) use wasm32::*;

        // The generic backend provides the slow paths and the scalar operations of
        // `wasm32`, and is tested against it.
        #[allow(dead_code)] // Only the rounding functions are used.
        mod generic;
        #[cfg(test)]
        mod differential_tests;
    } else {
        mod generic;
        pub(crate) use generic::*;
    }
}
