// Sets `cfg(inari_kernel_dispatch)` where the kernel of the elementary functions (`src/dyadic`)
// picks, at run time, between a copy of each entry compiled with the target feature `fma` and one
// with Dekker's products (`src/dyadic/level.rs`): on x86-64 targets without `fma`, such as plain
// `x86-64`, whose `Interval` uses the portable backend, and `x86-64-v2`, whose `Interval` uses
// `sse42` (see `src/simd.rs`), unless the feature `force-generic` asks for the portable backend
// and no dispatch. Every other build compiles one copy, with `HAS_FMA` (`src/simd/generic.rs`).
//
// The predicate is named once here, as a `cfg`, because about a hundred functions of the kernel
// carry `#[cfg_attr(inari_kernel_dispatch, inline(always))]`, which written out in full would not
// fit on a line.

use std::env;

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    println!("cargo::rustc-check-cfg=cfg(inari_kernel_dispatch)");
    // Set in RUSTFLAGS to make the dispatch take the Dekker copies on a CPU that has `fma`, to
    // test and count them there (`src/dyadic/level.rs`).
    println!("cargo::rustc-check-cfg=cfg(inari_force_no_fma)");
    // `CARGO_CFG_TARGET_FEATURE` lists the target features of the target CPU and of
    // `-Ctarget-feature`, as `cfg(target_feature)` does.
    let arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();
    let features = env::var("CARGO_CFG_TARGET_FEATURE").unwrap_or_default();
    let has = |feature: &str| features.split(',').any(|f| f == feature);
    if arch == "x86_64" && !has("fma") && env::var_os("CARGO_FEATURE_FORCE_GENERIC").is_none() {
        println!("cargo::rustc-cfg=inari_kernel_dispatch");
    }
}
