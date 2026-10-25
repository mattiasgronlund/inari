# Changelog

Items marked with ⚠️ are breaking changes.

## Unreleased

### Added

- Added support for architectures other than x86-64 and AArch64, such as wasm32 and riscv64, with a portable backend that does not change the rounding mode.
- Added the Cargo feature `force-generic`, which uses the portable backend on x86-64 and AArch64 too.
- Added a backend for WebAssembly that uses 128-bit SIMD instructions, enabled by the target feature `simd128`. It makes interval operations about twice as fast as the portable backend.
- Added a backend for x86-64 processors that have SSE4.2 but neither AVX nor FMA, which lowers the lowest supported processor from Haswell to Nehalem. Like the WebAssembly backend, it does not change the rounding mode. It is 1.2 to 2.1 times faster than the portable backend on such a processor.
- Added machine-checked proofs, in Rocq with the Flocq library, that addition, subtraction, multiplication, division and fused multiply-add rounded toward +∞, and the square root rounded toward -∞ and +∞, in the portable backend (`add_ru`, `sub_ru`, `sub1_ru`, `mul_ru`, `div_ru`, `mul_add_ru`, `sqrt_rd_ru`, `sqrt1_rd` and `sqrt1_ru`, the last six with and without an FMA) are correctly rounded for all inputs, and that `(Dec)Interval::abs`, `(Dec)Interval::floor`, `(Dec)Interval::ceil`, `(Dec)Interval::max`, `(Dec)Interval::min`, `(Dec)Interval::round`, `(Dec)Interval::round_ties_even`, `(Dec)Interval::sign` and `(Dec)Interval::trunc` with the portable backend return the tightest interval and the decoration that IEEE 1788 asks for. See [rocq/README.md](rocq/README.md).

### Changed

- Made the default backend for x86-64 processors with AVX and FMA compute the directed roundings explicitly, instead of switching the rounding mode around every instruction. No backend for x86-64 changes the rounding mode any more. On a Zen 2 processor, interval addition and subtraction take 0.47 times as long as before, multiplication 0.49 to 0.62 (0.81 to 0.83 where the products are below 2^-968), division 0.67 to 0.69, evaluating a degree-8 polynomial 0.41 to 0.45, and a 3×3 determinant 0.33. Only the latency of a chain of dependent `add_ru`, `div_ru` and `mul_add_ru` operations became slightly worse, by 3 to 12 percent.
- Made `(Dec)Interval::sqrt` about 2.5 times faster on x86-64 processors without AVX-512F, by computing the square root without changing the rounding mode.
- Made `(Dec)Interval::sqrt` compute both endpoints in a single vector square root when the interval does not contain zero: about 1.8 times faster on x86-64 processors without AVX-512F, and about 1.5 times faster on WebAssembly with `simd128`.

### Fixed

- Fixed `(Dec)Interval::rad` to return `0.0` instead of `-0.0` for the interval [0, 0] when its upper bound is `-0.0`, as in `const_interval!(0.0, -0.0)`. It returned `-0.0` with Rust 1.96 on x86-64, because `f64::max` may return either zero when given `0.0` and `-0.0`.

## v2.0.0 - 2024-08-07

### Added

- Implemented the traits `Send`, `Sync`, and `Unpin` for `(Dec)Interval`.

### Changed

- ⚠️ Renamed `(Dec)Interval::round_ties_to_even` to `(DecInterval)::round_ties_even`.

## v1.1.0 - 2023-04-02

### Added

- Implemented `(Dec)Interval::mul_rev_to_pair`.

### Changed

- ⚠️ Bumped the minimum supported Rust version to 1.65.0.
- ⚠️ Updated the following dependencies:
  - `gmp-mpfr-sys` from 1.4 to 1.5.
  - `rug` from 1.11 to 1.19.

## v1.0.0 - 2022-07-09

### Changed

- ⚠️ Bumped the minimum supported Rust version to 1.61.0.

### Removed

- ⚠️ Removed the macro `interval!(s, exact)`.

  Use the macro `interval_exact!(s)` [introduced](#v0140---2022-02-11) in v0.14.0 instead. (The removal should have been made in that version.)

## v0.15.0 - 2022-04-03

This is the first version of the crate that covers all required operations of IEEE Std 1788.1-2017.

### Added

- Implemented `(Dec)Interval::cancel_minus` and `cancel_plus`.

## v0.14.0 - 2022-02-11

### Changed

- ⚠️ Revised the syntax of the macro `interval!(s, exact)` to `interval_exact!(s)`.

## v0.13.0 - 2022-02-09

### Changed

- ⚠️ Renamed `(Dec)Interval::pown` to `(Dec)Interval::powi` so that it matches with the standard method `f64::powi`.

### Added

- Implemented the standard arithmetic operators `std::ops::{Neg, Add, Sub, Mul, Div}` and the corresponding assignment operators `std::ops::{AddAssign, SubAssign, MulAssign, DivAssign}` for `(Dec)Interval` for the cases when one or both of the arguments are given by reference.

## v0.12.0 - 2021-12-16

The crate requires a nightly toolchain >= `nightly-2021-12-16`.

### Fixed

- Fixed build failure on the latest nightly toolchain.

## v0.11.0 - 2021-12-07

The crate requires a nightly toolchain >= `nightly-2021-10-05`.

### Fixed

- Downstream crates are no longer required to specify the `static_assertions` crate as their dependency.

## v0.10.9 - 2021-10-10

- Now inari supports `x86_64-pc-windows-gnu` as a target.

## v0.10.0 - 2021-06-30

### Added

- Implemented the trait `Hash` for `Interval`, `Decoration`, and `Overlap`.

### Removed

- ⚠️ Removed the method `IntervalError::value`.

  Previously, the following values were returned by the method:

  | `err.kind()`                                    | `err.value()`                           |
  | ----------------------------------------------- | --------------------------------------- |
  | `IntervalErrorKind::UndefinedOperation`         | `Interval::EMPTY` or `DecInterval::NAI` |
  | `IntervalErrorKind::PossiblyUndefinedOperation` | `(Dec)Interval::ENTIRE`                 |

### Changed

- ⚠️ Changed the return type of the functions `(Dec)Interval::try_from_be_bytes`, `try_from_le_bytes` and `try_from_ne_bytes` to `Option<(Dec)Interval>`.
- ⚠️ Changed the struct `IntervalError` to be non-generic due to the removal of the `value` method.

## v0.9.9 - 2021-06-18

### Fixed

- Fixed the macros `interval!(s)` and `dec_interval!(s)` to return an `Err` with `IntervalErrorKind::PossiblyUndefinedOperation` when the mantissa has too many digits after the decimal point.

## v0.9.8 - 2021-06-06

### Fixed

- Fixed build failure with the latest nightly rust compiler: `rustc 1.54.0-nightly (6c2dd251b 2021-06-05)`.

## v0.9.4 - 2021-05-09

### Fixed

- Fixed the functions `(Dec)Interval::try_from_be_bytes`, `try_from_le_bytes` and `try_from_ne_bytes` to correctly deserialize the empty interval.

## v0.9.2 - 2021-03-09

### Added

- Experimental support for AArch64.

## v0.9.0 - 2021-02-20

### Changed

- ⚠️ Explicitly check the target CPU features during compilation. From this version, you need to specify `RUSTFLAGS='-Ctarget-cpu=<CPU>'`, where `<CPU>` must be `haswell` or a newer microarchitecture; otherwise, build fails.

## v0.8.0 - 2020-11-24

### Added

- Experimental support for AVX-512F.
  - To try it out, run cargo with `RUSTFLAGS='-Ctarget-feature=+avx512f'`.
  - Basic arithmetic operations are expected to get faster, but it is not benchmarked yet.

### Removed

- ⚠️ Removed the enum variant `IntervalErrorKind::IntvlPartOfNaI`.

### Changed

- ⚠️ Renamed the method `(Dec)Interval::round_ties_to_away` to `round`.
- ⚠️ Renamed the methods `DecInterval::interval_part` and `decoration_part` to `interval` and `decoration`, respectively.
- ⚠️ Changed the return type of the method `DecInterval::interval` (former `interval_part`) to `Option<Interval>` from `Result<Interval>`.
- ⚠️ Renamed the enum `OverlappingState` to `Overlap`.

## v0.7.0 - 2020-11-14

### Changed

- ⚠️ Renamed `DecoratedInterval` to `DecInterval`. Now its name is consistent with the macro `(const_)dec_interval!`.

## v0.6.1 - 2020-09-25

### Fixed

- Fixed the build failure on docs.rs.

## v0.6.0 - 2020-09-24

### Added

- Implemented the trait `Eq` for the enum `OverlappingState`.

### Removed

- ⚠️ Removed the enum variant `OverlappingState::Undefined`.

### Changed

- ⚠️ Changed the return type of the method `DecoratedInterval::overlap` to `Option<OverlappingState>` from `OverlappingState`.
  - Now it returns `None` if at least one of its arguments is NaI.
- ⚠️ Renamed the enum variant `OverlappingState::Equal` to `Equals`.

## v0.5.1 - 2020-08-31

### Fixed

- Fixed the macro `const_dec_interval!` to be usable without importing the macro `const_interval!`.

## v0.5.0 - 2020-08-31

### Changed

- ⚠️ Renamed the method `(Decorated)Interval::log` to `ln` to make them consistent with `f64::ln`.

## v0.4.0 - 2020-08-25

### Added

- Added type conversions between intervals and byte arrays.
  - `(Decorated)Interval::to_be_bytes`, `to_le_bytes` and `to_ne_bytes` convert intervals into byte arrays.
  - `(Decorated)Interval::try_from_be_bytes`, `try_from_le_bytes` and `try_from_ne_bytes` convert byte arrays into intervals.
- Added the type alias `Result<T> = std::result::Result<T, IntervalError<T>>`.

### Fixed

- Fixed the decoration returned by `atan2`.
  - Previously, `Def` was returned instead of `Dac` in certain cases.
- Fixed the Clippy warning `double_neg` caused by passing a negative value as the lower bound to the macro `const_interval!`.

## v0.3.1 - 2020-08-14

### Fixed

- Fixed decorations returned by constructors of `DecoratedInterval` and elementary functions `acos`, `acosh`, `asin`, `atan2`, `atanh`, `log`, `log2`, `log10` and `pow`.
  - `atan2` is still under investigation. so use it with caution.
  - Fixed broken unit tests.

## v0.3.0 - 2020-08-03

### Added

- Added the elementary functions `(Decorated)Interval::pown`, `pow`, `exp`, `exp2`, `exp10`, `log`, `log2`, `log10`, `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2`, `sinh`, `cosh`, `tanh`, `asinh`, `acosh` and `atanh`.

- Added the macros `const_interval!` and `const_dec_interval!` which let you make intervals from `f64` numbers in const contexts.

- Added the constants `(Decorated)Interval::EMPTY`, `ENTIRE` and `DecoratedInterval::NAI`.

### Removed

- ⚠️ Removed the functions `(Decorated)Interval::empty`, `entire` and `DecoratedInterval::nai` in favor of the new constants.

### Changed

- ⚠️ Changeed the representation of the struct `DecoratedInterval` to `#[repr(C)]` from the default one, while users must not rely on it.

## v0.2.1 - 2020-07-17

### Fixed

- Fixed the methods `Interval::rad` and `wid` to round the results up.

## v0.2.0 - 2020-07-09

### Added

- Added the decoration system.
  - Added the struct `DecoratedInterval`.
  - Added the macro `dec_interval!` that constructs a decorated interval.
  - Added the enum `Decoration`.
  - ⚠️ Added the enum variant `IntervalErrorKind::IntvlPartOfNaI`.
  - ⚠️ Added the enum variant `OverlappingState::Undefined`.
- Added the macro rule `interval!("...", exact)` that constructs an interval from an exact interval literal (`exactToInterval` in the standard).

### Changed

- ⚠️ Renamed the function `Interval::is_member` to `contains` and swapped the order of parameters to make it a method.
- ⚠️ Changed the method `IntervalError<T>::value` to take `self` instead of `&self`.

## v0.1.0 - 2020-07-03

Initial release.
