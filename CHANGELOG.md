# Changelog

Items marked with ⚠️ are breaking changes.

## Unreleased

### Added

- Added support for architectures other than x86-64 and AArch64, such as wasm32 and riscv64, with a portable backend that does not change the rounding mode.
- Added the Cargo feature `force-generic`, which uses the portable backend on x86-64 and AArch64 too.
- Added a backend for WebAssembly that uses 128-bit SIMD instructions, enabled by the target feature `simd128`. It makes most interval operations other than multiplication 1.6 to 1.9 times as fast as the portable backend, and multiplication 1.3 to 1.5 times as fast.
- Added a backend for x86-64 processors that have SSE4.2 but neither AVX nor FMA, which lowers the lowest supported processor from Haswell to Nehalem. Like the WebAssembly backend, it does not change the rounding mode. On such a processor, it makes most interval operations 1.6 to 2.5 times as fast as the portable backend.
- Added machine-checked proofs, in Rocq with the Flocq library, that addition, subtraction, multiplication, division and fused multiply-add rounded toward +∞, and the square root rounded toward -∞ and +∞, in the portable backend (`add_ru`, `sub_ru`, `sub1_ru`, `mul_ru`, `div_ru`, `mul_add_ru`, `sqrt_rd_ru`, `sqrt1_rd` and `sqrt1_ru`, the last six with and without an FMA) are correctly rounded for all inputs, and that `(Dec)Interval::abs`, `(Dec)Interval::floor`, `(Dec)Interval::ceil`, `(Dec)Interval::max`, `(Dec)Interval::min`, `(Dec)Interval::mul_add`, `(Dec)Interval::recip`, `(Dec)Interval::round`, `(Dec)Interval::round_ties_even`, `(Dec)Interval::sign`, `(Dec)Interval::sqr`, `(Dec)Interval::sqrt`, `(Dec)Interval::trunc`, and `-x`, `x + y`, `x - y`, `x * y` and `x / y` of `(Dec)Interval`s with the portable backend return the tightest interval and the decoration that IEEE 1788 asks for. They also show that `(Dec)Interval::mul_rev_to_pair` with the portable backend returns the tightest interval that contains each connected component of its set, of which there are at most two, in order, and the empty interval in the outputs that are left, and that it decorates its outputs as its documentation states. They show that `Interval::cancel_minus` with the portable backend returns what its documentation states, the tightest interval `z` such that `rhs + z` contains `self` where IEEE 1788's cancelMinus has a value, which is what IEEE 1788 asks for, and `Interval::ENTIRE` otherwise, that `Interval::cancel_plus` returns the same with `-rhs` in place of `rhs`, and that `DecInterval::cancel_minus` and `DecInterval::cancel_plus` return NaI for a NaI argument and otherwise that interval decorated `trv`. They show that `(Dec)Interval::acos`, `(Dec)Interval::acosh`, `(Dec)Interval::asin`, `(Dec)Interval::asinh`, `(Dec)Interval::atan`, `(Dec)Interval::atan2`, `(Dec)Interval::atanh`, `(Dec)Interval::cos`, `(Dec)Interval::cosh`, `(Dec)Interval::exp`, `(Dec)Interval::exp10`, `(Dec)Interval::exp2`, `(Dec)Interval::ln`, `(Dec)Interval::log10`, `(Dec)Interval::log2`, `(Dec)Interval::pow`, `(Dec)Interval::powi`, `(Dec)Interval::sin`, `(Dec)Interval::sinh`, `(Dec)Interval::tan` and `(Dec)Interval::tanh` with the portable backend return the tightest interval and the decoration that IEEE 1788 asks for, assuming that the MPFR functions that they call, and `mpfr_get_d`, round and return the special values as the MPFR manual states, and that MPFR's exponent range contains that of `f64`, as its default range does. They show that `FromStr` for `Interval` and `DecInterval`, `interval!(s)` and `dec_interval!(s)` with the portable backend round the bounds that they parse to the tightest interval that contains the reals that the literal denotes, with the decoration that IEEE 1788 asks for, and that `interval_exact!` returns that interval, which then holds exactly these reals, if both bounds are infinities or values of finite `f64`s, and an error otherwise, with the loops of the operations of `Nat`, the big integer of inari's own, with which they round the bounds proved too, Knuth's Algorithm D for its division included, assuming that the grammar returns each finite bound as a fraction with a positive denominator, times 2^a and 5^b for `i32`s a and b, with a numerator and a denominator of at most 2^63 bits, i.e. 2^60 bytes, more memory than any machine has, held in `Nat`s with no zero limb at the top, and, except for `interval_exact!`, returns bounds in order, which is checked by reading but not proved. For such bounds, they show that the step of the grammar that decorates a literal gives `com` only to bounded literals and only `trv` or `ill` to empty ones, returns `ill` only as NaI, and rejects a literal whose decoration it would have to change, such as `[1,inf]_com`. That the rest of the grammar passes each literal to this step and returns what it returns is checked by reading. They show that the functions with which `Display`, `LowerExp` and `LowerHex` of `(Dec)Interval`s compute the digits of a finite bound other than 0 round it toward -∞ or +∞, as they are asked, to the closest number in that direction with as many digits as the style and the precision keep, with the operations of `Nat` that they call proved too. That they are asked to round the lower bound toward -∞ and the upper one toward +∞ is checked by reading, and the text written from the digits is tested against MPFR, but neither is proved. They show that these assumptions about MPFR can all hold at once, for every exponent range that contains that of `f64`: an ideal MPFR, which rounds each of these functions correctly in the direction asked and returns the special values that the proofs assume, satisfies all of them. They also state, at the level of `f64`s, what the functions that round the bounds of the elementary functions must do, show that inari's, which call MPFR, do it under these assumptions, and restate for any functions that do it the theorems of `Interval::acos`, `Interval::acosh`, `Interval::asin`, `Interval::asinh`, `Interval::atan`, `Interval::atan2`, `Interval::atanh`, `Interval::cos`, `Interval::cosh`, `Interval::exp`, `Interval::exp10`, `Interval::exp2`, `Interval::ln`, `Interval::log10`, `Interval::log2`, `Interval::pow`, `Interval::powi`, `Interval::sin`, `Interval::sinh`, `Interval::tan` and `Interval::tanh`. They show that the arithmetic operations of a multi-precision kernel of inari's own on dyadic numbers, which only its tests use so far, return their exact results rounded toward -∞ or +∞, as asked, to their precision of 64 to 4,096 bits, for exponents far from the ends of the range of `i64`, and that Ziv's strategy with it, which rounds a real number to an `f64` from enclosures of it at increasing precisions, returns that number rounded toward -∞ or +∞ as MPFR rounds it wherever a rounding test passes, and a value on the side of it that the rounding is on wherever its evaluation does not panic, also where no test passes by its cap of 4,096 bits, where it now returns the bound of its enclosure on that side rounded outward rather than panicking, a value that is not proved to be within one `f64` of the correct rounding. They show that e^x, 2^x, 10^x, sinh, cosh, tanh, ln x, log2 x, log10 x, asinh, acosh, atanh, atan, atan2, asin, acos, sin, cos, tan, x^y and x^n computed with this kernel, which also only its tests use so far, do what the statements at the level of `f64`s above ask of the functions that round the bounds of `(Dec)Interval::exp`, `(Dec)Interval::exp2`, `(Dec)Interval::exp10`, `(Dec)Interval::sinh`, `(Dec)Interval::cosh`, `(Dec)Interval::tanh`, `(Dec)Interval::ln`, `(Dec)Interval::log2`, `(Dec)Interval::log10`, `(Dec)Interval::asinh`, `(Dec)Interval::acosh`, `(Dec)Interval::atanh`, `(Dec)Interval::atan`, `(Dec)Interval::atan2`, `(Dec)Interval::asin`, `(Dec)Interval::acos`, `(Dec)Interval::sin`, `(Dec)Interval::cos`, `(Dec)Interval::tan`, `(Dec)Interval::pow` and `(Dec)Interval::powi`, wherever a rounding test passes or a rule that does not call Ziv's strategy settles the argument, and that they return a value on the side of the result that the rounding is on wherever they do not panic, with the first 4,224 bits of ln 2 and ln 10 that they use checked against series of atanh, and those of π against Machin's formula. That a rounding test passes by the cap is not proved, nor that they do not panic, except that x^y, for x > 0, and x^n, for x other than 0, return at every finite argument whose exact result is an `f64`, and return that `f64`. They show that the constants of `Interval` and `DecInterval` from `E` to `TAU`, such as `Interval::PI` and `DecInterval::LN_2`, are the tightest intervals that contain their values, as the documentation of those of `Interval` states, and that `com`, the decoration of those of `DecInterval`, is the strongest decoration that IEEE 1788 allows for them. They also show that `DecInterval::EMPTY`, `DecInterval::ENTIRE` and `DecInterval::NAI` are decorated `trv`, `dac` and `ill`, as IEEE 1788 asks. The proofs of `(Dec)Interval::max` and `(Dec)Interval::min` cover both of their code paths, including the one that the x86-64 backends take, though with the portable backend's functions, such as `max` and `min`, in place of the x86-64 backends' own. The proofs of the decorations of `DecInterval::atan`, `DecInterval::atan2`, `DecInterval::cos`, `DecInterval::exp`, `DecInterval::exp10`, `DecInterval::exp2`, `DecInterval::max`, `DecInterval::min`, `DecInterval::pow`, `DecInterval::recip`, `DecInterval::sign`, `DecInterval::sin`, `DecInterval::tanh`, and `x * y` and `x / y` of `DecInterval`s assume that an argument is `com` only if its interval is nonempty and bounded, the proof of `DecInterval::mul_add` assumes the same of `self` and `rhs`, and that of `DecInterval::powi` assumes it of `self` for an exponent that is not positive. This is proved for every place in the library that makes a `DecInterval`. The proofs also assume that each argument is a valid interval, i.e. empty or with bounds that `TryFrom<(f64, f64)>` accepts. That is proved, with the portable backend, for every interval that the library's constructors make, such as the constants, `TryFrom<(f64, f64)>` and `FromStr`, and for every interval that these operations, `(Dec)Interval::convex_hull` and `(Dec)Interval::intersection` compute from such intervals, any number of times, under the same assumptions about MPFR for the functions that call it. See [rocq/README.md](rocq/README.md).

### Changed

- Made the default backend for x86-64 processors with AVX and FMA compute the directed roundings explicitly, instead of switching the rounding mode around every instruction. No backend for x86-64 changes the rounding mode any more. On a Zen 2 processor, interval addition and subtraction take 0.47 times as long as before, multiplication 0.49 to 0.62 (0.78 to 0.79 where the products are below 2^-968), division 0.67 to 0.69, evaluating a degree-8 polynomial 0.41 to 0.45, and a 3×3 determinant 0.33. Only the latency of a chain of dependent `add_ru`, `div_ru` and `mul_add_ru` operations became slightly worse, by 3 to 12 percent.
- Made `(Dec)Interval::sqrt` about 2.5 times faster on x86-64 processors without AVX-512F, by computing the square root without changing the rounding mode.
- Made `(Dec)Interval::sqrt` compute both endpoints in a single vector square root when the interval does not contain zero: about 1.8 times faster on x86-64 processors without AVX-512F, and about 1.5 times faster on WebAssembly with `simd128`.
- Made interval literals parse without GMP and MPFR, with a big integer of inari's own. They still need the Cargo feature `gmp`. That the magnitude of a number is above 2^1024 or below 2^-1074, the smallest positive `f64`, is now told from the numbers of bits of its numerator and denominator and from its exponents where these suffice, without computing its power of ten. On a Zen 2 processor, `[1e1900000000]` and `[1e-2147483648]`, whose powers of ten have over 6 × 10^9 bits, parse in less than a microsecond, where GMP and MPFR took over 20 s and 2 GB of memory. A literal with a decimal significand, or a `p` or `q` in `p/q`, of 10^5 or more digits can take longer to parse than with GMP, as inari's big integer reads and multiplies such numbers in a time that grows with the square of their number of digits: one with a significand of 10^5 digits takes about 7 ms instead of 1.6 ms, and one with 10^6 digits about 0.7 s instead of 28 ms, or 1.3 s instead of 0.23 s with the exponent `e-999999`, and `p/q` with 10^6 digits in each of `p` and `q` 1.3 s instead of 0.34 s. So can an interval literal whose bounds are close in magnitude, where one has a decimal exponent of large magnitude k and the other a hexadecimal significand of at least k bits, as inari compares them by computing 5^k exactly and multiplying by it where the numbers of bits and the exponents do not suffice: `[0x8…p-1728771, 1e-400000]`, with a hexadecimal significand of 10^5 digits, or 4 × 10^5 bits, takes about 0.13 s instead of 5.2 ms, and one with 10^6 digits and `1e-4000000` 13 s instead of 65 ms.
- Made intervals format without MPFR, with digits of inari's own, to the same text as before, as tests against MPFR check, except for the fix below. They still need the Cargo feature `gmp`. On a Zen 2 processor, formatting `Interval::PI` takes about half as long as before with `{}` and `{:.6}`, two thirds with `{:e}` and two fifths with `{:x}`. A bound whose text has hundreds of digits from its first nonzero digit to its last takes longer, mostly in converting inari's big integer to decimal, which takes a time that grows with the square of the number of digits: [`f64::MAX`, `f64::MAX`] with `{}` takes about 1.4 times as long, and [2^-1074, 2^-1074] with `{:.1100}` about 2.5 times. So can a bound of small magnitude, as inari computes its exact decimal expansion, of hundreds of digits, even where it prints few of them: [1e-200, 1e-200] with `{:e}` takes about 1.15 times as long, [1e-300, 1e-300] with `{:e}` about 1.6 times, and [1e-310, 1e-310] with `{}` about 1.15 times.
- Narrowed the platforms that inari supports with the Cargo feature `gmp` to 64-bit Linux and macOS, which leaves out some that `gmp-mpfr-sys` supports, such as 64-bit Windows with the GNU toolchain.
- ⚠️ Made the operations that call MPFR with the Cargo feature `gmp`, such as the elementary functions, panic if the linked MPFR is not built thread-safe. The MPFR that `gmp-mpfr-sys` builds is thread-safe, but a system MPFR that its feature `use-system-libs` links need not be. Such an MPFR keeps its flags, its exponent range and its caches of constants global, so a program linked with it now panics on its first such operation, even if it runs only one thread.

### Fixed

- Fixed `(Dec)Interval::rad` to return `0.0` instead of `-0.0` for the interval [0, 0] when its upper bound is `-0.0`, as in `const_interval!(0.0, -0.0)`. It returned `-0.0` with Rust 1.96 on x86-64, because `f64::max` may return either zero when given `0.0` and `-0.0`.
- Fixed `(Dec)Interval::cancel_minus` and `(Dec)Interval::cancel_plus` to return the tightest interval instead of `(Dec)Interval::ENTIRE` for some arguments whose widths round to the same float and that have a bound of `f64::MIN` or `f64::MAX`, such as `x.cancel_minus(x)` for `x` = [`f64::MIN`, -3 × 2^970], which is [0, 0]. An intermediate result of the error-free sum that compares the widths overflowed.
- Fixed `(Dec)Interval::cos`, `(Dec)Interval::sin` and `(Dec)Interval::tan` to return the tightest interval, and `DecInterval::tan` the strongest decoration, for every argument, as the documentation states. They located the multiples of π/2 in the argument by dividing it by `Interval::PI` or `Interval::FRAC_PI_2`, which only encloses the quotient, so that a bound close to such a multiple, relative to its magnitude, could give a wider result. For example, `tan` of [7.853981633974484, 7.853981633974485], just above the pole 5π/2, was [-∞, +∞], decorated `trv`, and is now [-1718163698371049, -680181816043107], decorated `com`. Where the division cannot tell, they now find the multiples from the signs of the sine and the cosine of the bounds, which MPFR rounds correctly.
- Fixed `{:.0x}` of `(Dec)Interval`s to print the exact digit of a positive upper bound or a negative lower bound of at most 4 significant bits, which MPFR printed one too large, as in `[0x8p-3,0x9p-3]` for [1, 1], or, where that made 16, as `0x` alone, as in `[0xfp+0,0x]` for [15, 15]. They are now `[0x8p-3,0x8p-3]` and `[0xfp+0,0xfp+0]`.

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
