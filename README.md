# 🦊 inari

[![crates.io](https://img.shields.io/crates/v/inari.svg)](https://crates.io/crates/inari)
[![docs](https://img.shields.io/docsrs/inari)](https://docs.rs/inari)
[![coverage](https://img.shields.io/coveralls/github/unageek/inari/main)](https://coveralls.io/github/unageek/inari?branch=main)
[![rustc 1.65+](https://img.shields.io/badge/rustc-1.65%2B-lightgrey)](https://blog.rust-lang.org/2022/11/03/Rust-1.65.0.html)

**inari** is a Rust implementation of [interval arithmetic](https://en.wikipedia.org/wiki/Interval_arithmetic).

It [conforms](https://docs.rs/inari/latest/inari/_docs/conformance/index.html) to [IEEE Std 1788.1-2017](https://doi.org/10.1109/IEEESTD.2018.8277144). It also implements a subset of [IEEE Std 1788-2015](https://doi.org/10.1109/IEEESTD.2015.7140721).

## Supported Platforms

The following CPUs are supported and continuously tested:

- **x86-64**

  Haswell-based and newer processors are supported by a backend that needs AVX and FMA (`fma`). Nehalem-based and newer ones are supported by a separate backend that uses only SSE instructions (`sse42`), which is selected at compile time when the target CPU lacks AVX or FMA. A third backend (`avx512f`) uses the embedded rounding of AVX-512F, and is selected when the target CPU has AVX-512F and Rust is 1.89 or later; earlier stable versions do not report `avx512f` to `cfg(target_feature)`, so they select `fma` instead. CI tests `avx512f` only when its runner has AVX-512F. No backend for x86-64 changes the rounding mode; the SSE-only one is slower because it has to emulate the fused multiply-add, most of all for `sqrt`, `mul_add` and division (see [BENCHMARKS.md](BENCHMARKS.md)).

  Unless you enable `force-generic` (see below), you need to specify the target CPU when building a crate that depends on inari. One way to do that is by using a [configuration file](https://doc.rust-lang.org/cargo/reference/config.html) in your project (see [example](https://github.com/unageek/graphest/blob/main/.cargo/config.toml); you may want to change `native` to `haswell`, or to `nehalem` for even wider compatibility, if you are going to distribute binaries).

- **AArch64 (ARM64)**

Other architectures, such as WebAssembly (`wasm32`) and RISC-V (`riscv64`), are supported by a portable backend (experimental). It only relies on floating-point arithmetic in the default rounding mode, and requires no target features, but it is slower than the backends for x86-64 and AArch64. It uses fused multiply-add instructions where the target has them. On WebAssembly, building with `RUSTFLAGS='-Ctarget-feature=+simd128'` selects a faster variant that uses 128-bit SIMD instructions.

When using the Cargo feature `gmp` (see below), target platforms are limited to those that are supported by the [`gmp-mpfr-sys`](https://crates.io/crates/gmp-mpfr-sys) crate. For example, MSVC is not supported. With `gmp`, inari supports 64-bit Linux and macOS (CI tests x86-64 Linux and AArch64 macOS). Other targets, such as 32-bit targets and 64-bit Windows, are not supported with `gmp` and are not tested. If `gmp-mpfr-sys` links a system MPFR, through its feature `use-system-libs`, that MPFR has to be built thread-safe, as it is by default where the system supports thread-local storage, and inari panics on its first operation that calls MPFR, such as an elementary function, if it is not: such an MPFR keeps its flags, its exponent range and its caches of constants such as π global, so threads that call it at the same time can interfere.

## Building for Several x86-64 Levels

inari picks its x86-64 backend at compile time, from the target features that `cfg(target_feature)` reports for the target CPU, not by detecting the CPU at run time. As target CPUs, the microarchitecture levels of the [x86-64 psABI](https://gitlab.com/x86-psABIs/x86-64-ABI) select these backends: `x86-64`, the default for `x86_64-unknown-linux-gnu`, selects none, and the build fails unless `force-generic` is enabled; `x86-64-v2` selects `sse42`; `x86-64-v3` selects `fma`, as `haswell` does; and `x86-64-v4` selects `avx512f` with Rust 1.89 or later, and `fma` with earlier stable versions (see above). CI does not build for these levels by name.

To give each CPU the code for its level without your users having to compile anything, build the whole program once per level, and pick one of the builds when it starts:

```bash
for level in x86-64-v2 x86-64-v3 x86-64-v4; do
    RUSTFLAGS="-Ctarget-cpu=$level" cargo build --release --target x86_64-unknown-linux-gnu --target-dir target/$level
done
# Below x86-64-v2, only the portable backend builds.
RUSTFLAGS="-Ctarget-cpu=x86-64" cargo build --release --target x86_64-unknown-linux-gnu --target-dir target/x86-64 --features inari/force-generic
```

Each build lands in `target/<level>/x86_64-unknown-linux-gnu/release/`. `--features inari/force-generic` needs inari as a direct dependency of the package you build. The separate `--target-dir`s keep the builds from overwriting one another, and `--target` keeps `RUSTFLAGS` away from build scripts and procedural macros, which run on the build machine (see [`build.rustflags`](https://doc.rust-lang.org/cargo/reference/config.html#buildrustflags)): without it, a build for `x86-64-v4` on a machine without AVX-512 can die with SIGILL in a build script, such as that of `gmp-mpfr-sys`.

For a program, a small launcher, itself built for `x86-64`, can run the build for the highest level the CPU has. It must test the whole level as the psABI defines it, not only the features that select inari's backend, because a build for a level lets the compiler use any feature of the level in any code it compiles. In Rust 1.96, `std::is_x86_feature_detected!` has a name for each feature that `x86-64-v2`, `x86-64-v3` and `x86-64-v4` add to `x86-64` but LAHF-SAHF and OSXSAVE; it tests OSXSAVE as part of AVX, and for AVX and AVX-512 it also tests that the operating system has enabled them.

For a shared library (a `cdylib`) on Linux with glibc 2.33 or later, the dynamic loader can do the picking. Install the builds for `x86-64-v2`, `x86-64-v3` and `x86-64-v4` in the subdirectories `glibc-hwcaps/x86-64-v2/`, `glibc-hwcaps/x86-64-v3/` and `glibc-hwcaps/x86-64-v4/` of the directory the library is found in, and the loader loads the copy for the highest level the CPU supports (see [ld.so(8)](https://man7.org/linux/man-pages/man8/ld.so.8.html), "glibc Hardware capabilities"). It does so in the directories of `LD_LIBRARY_PATH`, `RUNPATH` and `RPATH`, and for `dlopen` of a name without a slash; a name with a slash is a path, and the loader loads that file. Glibc before 2.33, a CPU that has none of the levels in `glibc-hwcaps/`, and a program that loads the library by its path in that directory get the copy in the directory itself, which must therefore be the lowest level you ship. This is glibc's mechanism: musl, macOS and Windows do not have it.

## Cargo Features

- `gmp` (enabled by default) - Enables [operations](https://docs.rs/inari/latest/inari/_docs/conformance/) that depend on GMP and MPFR. You can opt out of the feature to reduce dependencies. Even in that case, you still have access to all operations required by certain kinds of tasks, such as making fast robust predicates for computational geometry.
- `force-generic` - Uses the portable backend (see above) on x86-64, AArch64 and WebAssembly with `simd128` too. It is slower. Unlike the AArch64 backend, it does not change the rounding mode, and on x86-64 it also builds for target CPUs without SSE4.2, such as the default `x86-64`.

## [Changelog](CHANGELOG.md)

## Building the Documentation Locally

```bash
RUSTDOCFLAGS="--cfg docsrs --html-in-header /path/to/inari/src/_docs/header.html" cargo doc --open
```

Ensure that the absolute path to [`header.html`](src/_docs/header.html) is specified.

## Related Project

- [Graphest](https://github.com/unageek/graphest) - A faithful graphing calculator.

## References

- IEEE Std 1788-2015 - IEEE Standard for Interval Arithmetic. [DOI: 10.1109/IEEESTD.2015.7140721](https://doi.org/10.1109/IEEESTD.2015.7140721)
- IEEE Std 1788.1-2017 - IEEE Standard for Interval Arithmetic (Simplified). [DOI: 10.1109/IEEESTD.2018.8277144](https://doi.org/10.1109/IEEESTD.2018.8277144)
