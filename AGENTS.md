# Working in this repo (inari)

## Must pass before every commit (mirrors .github/workflows/ci-x86-64.yml)
CI runs with RUSTFLAGS="-Ctarget-cpu=haswell -Dwarnings", so warnings are errors.
- cargo fmt -- --check
- cargo clippy --all-targets
- cargo test --release
- cargo test --release --no-default-features --lib --tests
- cargo rustdoc   (docs must build without warnings)
- cargo check --no-default-features --all-targets
- cargo rustc --lib --all-features --profile check -- --cfg docsrs   (the docs.rs configuration must compile)
- rocq/check-sites.sh   (as in ci-rocq.yml; if it fails, update what its message names)
If the machine has AVX-512F, also run clippy and tests with -Ctarget-cpu=native
(CI compiles both backends in every run, but tests `avx512f` only when its runner
has AVX-512F). Repeat everything with any new feature flags enabled.
Default rustfmt settings. Do not add rustfmt.toml or clippy.toml, and do not add
crate-wide `#[allow]`s. Local allows need a comment explaining why.

## Code style: match the neighbouring files
- New SIMD backends mirror the existing ones in `src/simd/`: same function order
  and names as `unimplemented.rs`, `pub(crate)` visibility, small `#[inline]`-free
  functions, and a `macro_rules!` where the existing backends use one
  (`impl_op_round!`).
- Document semantics in the existing notation, e.g.
  `/// \`add_rn([x0, x1], [y0, y1]) = [x0 + y0, x1 + y1]\` rounded to nearest.`
  and keep the lane-layout comment convention from `src/simd.rs`.
- Explain every non-obvious numerical step with a short comment, and cite the
  paper/algorithm for error-free transformations.
- Use `cfg_if!` for target selection, as in `src/simd.rs` and `src/lib.rs`.
- Keep `unsafe` blocks minimal, as in the existing code.
- Every mismatch that a random test or a fuzzer finds goes into a `regressions()`
  list, with what it broke and where it was found: SIMD operations in
  `src/simd/differential_tests.rs`, literals (the parser) in `src/parse/diff_tests.rs`,
  formatted bounds in `src/format/diff_tests.rs`, operations of the dyadic kernel in
  `src/dyadic/tests.rs`, its exponentials and hyperbolic functions in
  `src/dyadic/exp/tests.rs`, its logarithms and inverse hyperbolic functions in
  `src/dyadic/log/tests.rs`, its inverse trigonometric functions in
  `src/dyadic/atan/tests.rs`, its trigonometric functions in
  `src/dyadic/trig/tests.rs`, and its powers in `src/dyadic/pow/tests.rs`.

## Documentation to update alongside code
- README.md, "Supported Platforms": add new architectures in the same format,
  including any required RUSTFLAGS / target features.
- README.md, "Cargo Features": document any new feature in the same one-line style
  as `gmp`.
- CHANGELOG.md: add entries under a new "## Unreleased" heading using the existing
  "### Added / ### Changed" sections. Mark breaking changes with ⚠️. Past-tense
  sentences, backticked identifiers, e.g.
  "- Added support for the wasm32 and riscv64 architectures."
- Public-facing docs live in `src/_docs/*.md`. Only touch them if user-visible
  behaviour changes.
- Don't bump the version or `rust-version` in Cargo.toml unless asked.

## Commits
Follow the style of `git log --oneline` in this repo: short, imperative,
capitalized subject with no trailing period, identifiers in backticks
(e.g. "Implement `Debug` by hand for Interval"). One logical change per commit.
