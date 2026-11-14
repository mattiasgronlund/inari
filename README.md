# 🦊 inari

[![crates.io](https://img.shields.io/crates/v/inari.svg)](https://crates.io/crates/inari)
[![docs](https://img.shields.io/docsrs/inari)](https://docs.rs/inari)
[![coverage](https://img.shields.io/coveralls/github/unageek/inari/main)](https://coveralls.io/github/unageek/inari?branch=main)
[![rustc 1.86+](https://img.shields.io/badge/rustc-1.86%2B-lightgrey)](https://blog.rust-lang.org/2025/04/03/Rust-1.86.0/)

**inari** is a Rust implementation of [interval arithmetic](https://en.wikipedia.org/wiki/Interval_arithmetic).

It [conforms](https://docs.rs/inari/latest/inari/_docs/conformance/index.html) to [IEEE Std 1788.1-2017](https://doi.org/10.1109/IEEESTD.2018.8277144). It also implements a subset of [IEEE Std 1788-2015](https://doi.org/10.1109/IEEESTD.2015.7140721).

## Supported Platforms

The following CPUs are supported and continuously tested:

- **x86-64**

  Haswell-based and newer processors are supported by a backend that needs AVX and FMA (`fma`). Nehalem-based and newer ones are supported by a separate backend that uses only SSE instructions (`sse42`), which is selected at compile time when the target CPU lacks AVX or FMA. A third backend (`avx512f`) uses the embedded rounding of AVX-512F, and is selected when the target CPU has AVX-512F and Rust is 1.89 or later; earlier stable versions do not report `avx512f` to `cfg(target_feature)`, so they select `fma` instead. CI tests `avx512f` only when its runner has AVX-512F. No backend for x86-64 changes the rounding mode; the SSE-only one is slower because it has to emulate the fused multiply-add, most of all for `sqrt`, `mul_add` and division (see [BENCHMARKS.md](BENCHMARKS.md)).

  To get one of these backends, you need to specify the target CPU when building a crate that depends on inari. A build for a target CPU without SSE4.2, such as `x86-64`, the default for `x86_64-unknown-linux-gnu`, uses the portable backend (see below), and, unless `force-generic` is enabled, the multi-precision kernel of the elementary functions checks at run time whether the CPU has FMA (see [Building for Several x86-64 Levels](#building-for-several-x86-64-levels)). One way to specify the target CPU is by using a [configuration file](https://doc.rust-lang.org/cargo/reference/config.html) in your project (see [example](https://github.com/unageek/graphest/blob/main/.cargo/config.toml); you may want to change `native` to `haswell`, or to `nehalem` for even wider compatibility, if you are going to distribute binaries).

- **AArch64 (ARM64)**

Other architectures, such as 32-bit x86 (`i686`), WebAssembly (`wasm32`) and RISC-V (`riscv64`), are supported by a portable backend (experimental). It only relies on floating-point arithmetic in the default rounding mode, and requires no target features, but it is slower than the backends for x86-64 and AArch64. It uses fused multiply-add instructions where the target has them. On WebAssembly, building with `RUSTFLAGS='-Ctarget-feature=+simd128'` selects a faster variant that uses 128-bit SIMD instructions.

Interval literals, formatting and the elementary functions need neither GMP nor MPFR, nor a Cargo feature: inari computes them with code of its own, a multi-precision kernel for the elementary functions. CI tests x86-64 Linux, x86-64 Windows with MSVC (`x86_64-pc-windows-msvc`), AArch64 macOS, 32-bit x86 Linux (`i686-unknown-linux-gnu`) and WebAssembly (`wasm32-wasip1`, with and without `simd128`), and only builds for `wasm32-unknown-unknown` and `riscv64gc-unknown-linux-gnu`. On 64-bit Linux and macOS, the tests also compare inari's results with MPFR's, through the dev-dependencies `rug` and [`gmp-mpfr-sys`](https://crates.io/crates/gmp-mpfr-sys); on the other targets, they run without these comparisons.

## Building for Several x86-64 Levels

inari picks its x86-64 backend at compile time, from the target features that `cfg(target_feature)` reports for the target CPU, not by detecting the CPU at run time. As target CPUs, the microarchitecture levels of the [x86-64 psABI](https://gitlab.com/x86-psABIs/x86-64-ABI) select these backends: `x86-64`, the default for `x86_64-unknown-linux-gnu`, selects none of them, so that intervals use the portable backend; `x86-64-v2` selects `sse42`; `x86-64-v3` selects `fma`, as `haswell` does; and `x86-64-v4` selects `avx512f` with Rust 1.89 or later, and `fma` with earlier stable versions (see above).

The one part of inari that detects the CPU at run time is the multi-precision kernel with which the elementary functions and those of `inari::cr` are computed, and only in a build for a target CPU without SSE4.2, such as `x86-64`, unless `force-generic` is enabled. There each function of the kernel runs its fast path in a copy compiled with the target feature `fma` on a CPU that has FMA, and in a copy that computes the exact errors of its products with Dekker's algorithm on any other. The two return the same results: the Rocq proofs show that the fast paths of the kernel return the same with and without an FMA. The kernel detects FMA on its first call and keeps the answer, which each later call tests. CI builds for `x86-64`, and tests both copies there, but does not build for the other levels by name.

To give each CPU the code for its level without your users having to compile anything, build the whole program once per level, and pick one of the builds when it starts:

```bash
for level in x86-64 x86-64-v2 x86-64-v3 x86-64-v4; do
    RUSTFLAGS="-Ctarget-cpu=$level" cargo build --release --target x86_64-unknown-linux-gnu --target-dir target/$level
done
```

Each build lands in `target/<level>/x86_64-unknown-linux-gnu/release/`. The separate `--target-dir`s keep the builds from overwriting one another, and `--target` keeps `RUSTFLAGS` away from build scripts and procedural macros, which run on the build machine (see [`build.rustflags`](https://doc.rust-lang.org/cargo/reference/config.html#buildrustflags)): without it, a build for `x86-64-v4` on a machine without AVX-512 can die with SIGILL in one of them.

For a program, a small launcher, itself built for `x86-64`, can run the build for the highest level the CPU has. It must test the whole level as the psABI defines it, not only the features that select inari's backend, because a build for a level lets the compiler use any feature of the level in any code it compiles. In Rust 1.96, `std::is_x86_feature_detected!` has a name for each feature that `x86-64-v2`, `x86-64-v3` and `x86-64-v4` add to `x86-64` but LAHF-SAHF and OSXSAVE; it tests OSXSAVE as part of AVX, and for AVX and AVX-512 it also tests that the operating system has enabled them.

For a shared library (a `cdylib`) on Linux with glibc 2.33 or later, the dynamic loader can do the picking. Install the builds for `x86-64-v2`, `x86-64-v3` and `x86-64-v4` in the subdirectories `glibc-hwcaps/x86-64-v2/`, `glibc-hwcaps/x86-64-v3/` and `glibc-hwcaps/x86-64-v4/` of the directory the library is found in, and the loader loads the copy for the highest level the CPU supports (see [ld.so(8)](https://man7.org/linux/man-pages/man8/ld.so.8.html), "glibc Hardware capabilities"). It does so in the directories of `LD_LIBRARY_PATH`, `RUNPATH` and `RPATH`, and for `dlopen` of a name without a slash; a name with a slash is a path, and the loader loads that file. Glibc before 2.33, a CPU that has none of the levels in `glibc-hwcaps/`, and a program that loads the library by its path in that directory get the copy in the directory itself, which must therefore be the lowest level you ship. This is glibc's mechanism: musl, macOS and Windows do not have it.

## Correctly Rounded Functions

The module `inari::cr` has the elementary functions of intervals other than `cbrt` and `hypot` as functions of an `f64` (of two for `atan2` and `pow`, and of an `f64` and an `i32` for `powi`), each rounded to nearest with ties to even (`_rn`), toward -∞ (`_rd`) and toward +∞ (`_ru`), computed with the same kernel:

```rust
use inari::cr;
assert_eq!(cr::exp_rn(0.0), 1.0);
assert!(cr::sin_rd(1.0) < cr::sin_ru(1.0));
assert_eq!(cr::pow_rn(-2.0, 3.0), -8.0);
```

They are correctly rounded wherever a rule or Ziv's strategy, with enclosures of up to 4,096 bits, settles the argument. At an argument that reaches that cap, they return the rounding of a bound of the last enclosure, which is not known to be correctly rounded, but none of the hard-to-round arguments that CORE-MATH lists for these functions reaches it. The documentation of the module gives their values at the zeros, at the infinities and outside the domains, which are MPFR's, and those of `pow` at x < 0. Tests on 64-bit Linux and macOS compare them with MPFR in all three roundings.

The module also has `cbrt`, `hypot` (of two `f64`s) and `sqrt` in the same three roundings. `cbrt` and `hypot` compute an exact integer cube or square root where a fast path in `f64` does not decide the rounding, without Ziv's strategy and so with no cap, `sqrt_rn` is `f64::sqrt`, and `sqrt_rd` and `sqrt_ru` are those of the backend of the interval arithmetic. The Rocq proofs show these correctly rounded at every finite argument (x >= 0 for `sqrt`), `sqrt_rd` and `sqrt_ru` as the portable backend computes them, and tests compare them with MPFR too. `Interval::cbrt` and `Interval::hypot` compute their bounds with the functions of the kernel that `cbrt_rd`, `cbrt_ru`, `hypot_rd` and `hypot_ru` call.

## Cargo Features

- `gmp` - Deprecated, and does nothing; to be removed in the next major release. It used to be enabled by default, and to enable interval literals, formatting and the elementary functions, which need neither GMP nor MPFR now (see above). The features `gmp-mpfr-sys`, `nom` and `rug`, which Cargo used to derive from the optional dependencies of `gmp`, are deprecated and do nothing too.
- `force-generic` - Uses the portable backend (see above) on x86-64, AArch64 and WebAssembly with `simd128` too. It is slower. Unlike the AArch64 backend, it does not change the rounding mode, and on x86-64 it also keeps the multi-precision kernel from detecting the CPU at run time (see [Building for Several x86-64 Levels](#building-for-several-x86-64-levels)): the kernel then uses FMA instructions only where the target CPU has FMA.

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
