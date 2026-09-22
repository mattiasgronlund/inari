# Benchmarks

A comparison of the backends of inari: the hardware backend for x86-64
(`avx_fma`), the portable backend (`generic`, see `src/simd/generic.rs`) and the
WebAssembly backend (`wasm32`, see `src/simd/wasm32.rs`), measured on 2026-09-22.

## Setup

- CPU: AMD Ryzen 9 3900X (Zen 2, 12 cores). It has no AVX-512, so the `avx512f`
  backend could not be measured.
- Linux 7.0, `schedutil` governor, rustc 1.96.0, criterion 0.7.0, wasmtime 49.0.
- `lto = "fat"` and `codegen-units = 1`, so that the primitives are inlined into
  the benchmarks as they are within inari.
- Each run was pinned to one core with `taskset -c 11`, on an otherwise idle
  machine (load average 1 to 3).

Native configurations:

| Column | Backend | Flags |
|---|---|---|
| avx_fma | `avx_fma` (default) | `RUSTFLAGS=-Ctarget-cpu=haswell` |
| generic, FMA | `generic` with FMA | `RUSTFLAGS=-Ctarget-cpu=haswell`, `--features force-generic` |
| generic, no FMA | `generic` with Dekker's algorithm | `RUSTFLAGS=-Ctarget-cpu=x86-64`, `--features force-generic` |

WebAssembly configurations, all on `wasm32-wasip1` under wasmtime, and all
without an FMA, which WebAssembly does not have:

| Column | Backend | Flags |
|---|---|---|
| scalar | `generic` | none |
| simd128 | `generic`, which the compiler may auto-vectorize | `RUSTFLAGS=-Ctarget-feature=+simd128`, `--features force-generic` |
| wasm32 | `wasm32` (`F64X2` in a `v128`) | `RUSTFLAGS=-Ctarget-feature=+simd128` |

## Variance

Every configuration was run twice, interleaved. The tables show the lower of the
two medians, and "spread" is the largest difference between the two runs of any
one configuration in that row, relative to the lower one. All spreads are at or
below 3%; treat differences below about 5% as not significant.

## Results

Times are the median per operation: per `F64X2` operation (two lanes) for the
primitives, and per interval operation otherwise. Ratios are relative to the
first column; below 1 means faster than it.

### x86-64

Interval operations (1024 independent operations; P: positive, N: negative,
M: containing zero):

| Benchmark | avx_fma (ns) | generic, FMA (ns) | ratio | generic, no FMA (ns) | ratio | spread |
|---|--:|--:|--:|--:|--:|--:|
| add/PP | 9.25 | 9.22 | 1.00× | 12.35 | 1.33× | 0% |
| add/PM | 9.25 | 9.89 | 1.07× | 10.68 | 1.15× | 0% |
| add/MM | 9.25 | 9.70 | 1.05× | 12.32 | 1.33× | 0% |
| sub/PP | 9.26 | 8.64 | 0.93× | 8.86 | 0.96× | 0% |
| sub/PM | 9.25 | 9.79 | 1.06× | 10.11 | 1.09× | 0% |
| sub/MM | 9.25 | 9.64 | 1.04× | 11.83 | 1.28× | 0% |
| mul/PP | 10.42 | 13.10 | 1.26× | 15.82 | 1.52× | 0% |
| mul/PN | 10.43 | 12.96 | 1.24× | 15.51 | 1.49× | 1% |
| mul/PM | 10.41 | 12.89 | 1.24× | 15.82 | 1.52× | 0% |
| mul/NP | 10.41 | 13.15 | 1.26× | 15.73 | 1.51× | 0% |
| mul/NN | 10.43 | 13.17 | 1.26× | 15.82 | 1.52× | 0% |
| mul/NM | 10.42 | 12.96 | 1.24× | 15.67 | 1.50× | 2% |
| mul/MP | 10.41 | 13.00 | 1.25× | 15.51 | 1.49× | 2% |
| mul/MN | 10.42 | 12.88 | 1.24× | 15.86 | 1.52× | 0% |
| mul/MM | 18.91 | 22.28 | 1.18× | 30.16 | 1.60× | 3% |
| div/PP | 10.18 | 26.16 | 2.57× | 25.94 | 2.55× | 0% |
| div/PN | 10.20 | 18.31 | 1.80× | 26.64 | 2.61× | 0% |
| div/MP | 10.19 | 26.98 | 2.65× | 25.39 | 2.49× | 0% |
| div/NN | 10.18 | 26.29 | 2.58× | 25.49 | 2.50× | 1% |
| div/PM (= ℝ) | 3.76 | 4.90 | 1.30× | 4.93 | 1.31× | 0% |
| sqrt/P | 6.85 | 8.25 | 1.20× | 11.83 | 1.73× | 3% |
| Horner, degree 8, P | 308.30 | 169.24 | 0.55× | 226.63 | 0.74× | 2% |
| Horner, degree 8, M | 355.61 | 272.37 | 0.77× | 375.36 | 1.06× | 2% |
| 3×3 determinant | 236.04 | 255.37 | 1.08× | 321.71 | 1.36× | 1% |

Primitives (`throughput`: 1024 independent operations; `latency`: a chain of
1024 dependent operations):

| Benchmark | avx_fma (ns) | generic, FMA (ns) | ratio | generic, no FMA (ns) | ratio | spread |
|---|--:|--:|--:|--:|--:|--:|
| add_ru/throughput | 9.28 | 8.15 | 0.88× | 8.37 | 0.90× | 0% |
| add_ru/latency | 8.76 | 13.01 | 1.49× | 13.07 | 1.49× | 0% |
| mul_ru/throughput | 9.26 | 9.16 | 0.99× | 11.01 | 1.19× | 1% |
| mul_ru/latency | 8.75 | 13.11 | 1.50× | 16.24 | 1.86× | 0% |
| div_ru/throughput | 9.28 | 9.84 | 1.06× | 31.99 | 3.45× | 0% |
| div_ru/latency | 8.76 | 15.34 | 1.75× | 35.01 | 4.00× | 0% |
| mul_add_ru/throughput | 9.00 | 19.40 | 2.16× | 37.60 | 4.18× | 1% |
| mul_add_ru/latency | 8.52 | 11.25 | 1.32× | 23.60 | 2.77× | 0% |
| sqrt1_ru/throughput | 2.32 | 2.13 | 0.92× | 4.07 | 1.76× | 1% |
| sqrt1_ru/latency | 7.33 | 7.33 | 1.00× | 7.75 | 1.06× | 0% |

`avx_fma` takes `sqrt1_rd` and `sqrt1_ru` from `generic`, which is why its
square roots match it. Before that change, with the rounding mode switched
around `vsqrtsd`, `sqrt1_ru/throughput` was 8.65 ns and interval `sqrt/P` was
17.72 ns (measured on a loaded machine, spread 15%).

### WebAssembly

| Benchmark | scalar (ns) | simd128 (ns) | ratio | wasm32 (ns) | ratio | spread |
|---|--:|--:|--:|--:|--:|--:|
| add/PP | 15.48 | 15.33 | 0.99× | 9.02 | 0.58× | 0% |
| add/PM | 14.60 | 14.51 | 0.99× | 9.01 | 0.62× | 0% |
| add/MM | 15.53 | 15.19 | 0.98× | 9.01 | 0.58× | 0% |
| sub/PP | 10.96 | 11.15 | 1.02× | 8.84 | 0.81× | 1% |
| sub/PM | 13.91 | 13.95 | 1.00× | 8.83 | 0.63× | 0% |
| sub/MM | 15.26 | 15.38 | 1.01× | 8.83 | 0.58× | 1% |
| mul/PP | 30.54 | 31.21 | 1.02× | 14.56 | 0.48× | 0% |
| mul/PN | 35.31 | 32.76 | 0.93× | 14.61 | 0.41× | 0% |
| mul/PM | 30.61 | 31.22 | 1.02× | 14.60 | 0.48× | 0% |
| mul/NP | 33.58 | 31.92 | 0.95× | 14.58 | 0.43× | 0% |
| mul/NN | 32.07 | 32.35 | 1.01× | 14.63 | 0.46× | 0% |
| mul/NM | 30.67 | 31.05 | 1.01× | 14.60 | 0.48× | 0% |
| mul/MP | 30.73 | 30.96 | 1.01× | 14.56 | 0.47× | 0% |
| mul/MN | 30.30 | 30.50 | 1.01× | 14.64 | 0.48× | 1% |
| mul/MM | 55.13 | 55.28 | 1.00× | 25.08 | 0.46× | 1% |
| div/PP | 30.92 | 31.44 | 1.02× | 16.35 | 0.53× | 0% |
| div/PN | 31.53 | 31.53 | 1.00× | 16.53 | 0.52× | 0% |
| div/MP | 30.35 | 30.49 | 1.00× | 16.31 | 0.54× | 0% |
| div/NN | 30.99 | 31.63 | 1.02× | 16.18 | 0.52× | 1% |
| div/PM (= ℝ) | 9.89 | 9.21 | 0.93× | 7.88 | 0.80× | 0% |
| sqrt/P | 15.96 | 15.57 | 0.98× | 15.71 | 0.98× | 1% |
| Horner, degree 8, P | 310.73 | 309.73 | 1.00× | 160.74 | 0.52× | 2% |
| Horner, degree 8, M | 465.52 | 461.92 | 0.99× | 240.37 | 0.52× | 1% |
| 3×3 determinant | 378.60 | 376.21 | 0.99× | 136.88 | 0.36× | 0% |

| Benchmark | scalar (ns) | simd128 (ns) | ratio | wasm32 (ns) | ratio | spread |
|---|--:|--:|--:|--:|--:|--:|
| add_ru/throughput | 10.56 | 11.18 | 1.06× | 7.88 | 0.75× | 0% |
| add_ru/latency | 10.30 | 15.05 | 1.46× | 9.08 | 0.88× | 0% |
| mul_ru/throughput | 23.67 | 23.70 | 1.00× | 10.96 | 0.46× | 1% |
| mul_ru/latency | 17.46 | 24.11 | 1.38× | 11.52 | 0.66× | 0% |
| div_ru/throughput | 24.89 | 26.75 | 1.07× | 13.57 | 0.55× | 0% |
| div_ru/latency | 20.66 | 29.50 | 1.43× | 16.02 | 0.78× | 0% |
| mul_add_ru/throughput | 28.85 | 29.64 | 1.03× | 18.59 | 0.64× | 0% |
| mul_add_ru/latency | 22.56 | 24.42 | 1.08× | 21.00 | 0.93× | 0% |
| sqrt1_ru/throughput | 4.55 | 4.54 | 1.00× | 4.54 | 1.00× | 2% |
| sqrt1_ru/latency | 7.22 | 7.21 | 1.00× | 7.22 | 1.00× | 0% |

## Observations

- Every `avx_fma` primitive but the square root costs about 9 ns, both in
  throughput and in latency, whatever the operation. The backend saves, sets and
  restores MXCSR (`vstmxcsr`/`vldmxcsr`) around each instruction. As throughput
  equals latency, this apparently serializes the operations on Zen 2, and
  dominates the cost. The square root, which no longer switches the rounding
  mode, is the exception: 2.32 ns in throughput.
- `generic` has no such fixed cost, but needs more instructions per operation.
  On x86-64 it is on par for addition and subtraction, about 1.25× slower for
  interval multiplication, and 1.8–2.7× slower for division. It wins on
  polynomial evaluation (Horner with P: 0.55×), where the MXCSR switches of
  `avx_fma` cannot overlap.
- Without an FMA, multiplication and especially division and `mul_add` get
  slower, as Dekker's TwoProduct replaces a single FMA.
- On WebAssembly, `+simd128` alone changes almost nothing: the compiler does not
  usefully auto-vectorize the scalar code, and it makes the latency of the
  primitives 1.4× worse. Writing the fast paths against `v128` explicitly, as
  the `wasm32` backend does, is what pays: interval operations take 0.4–0.6× the
  time, and the 3×3 determinant 0.36×.
- `sqrt` is the same in all three WebAssembly configurations, because `wasm32`
  takes it from `generic`: it is a scalar operation with nothing to vectorize.

## Conclusion

On x86-64 processors without AVX-512, `generic` should not replace `avx_fma` as
the default. It is not uniformly faster: it wins on polynomial evaluation and
loses on multiplication and division, which dominate typical interval code such
as the determinant. The differences are mostly within 1.3×, except division, so
`force-generic` is a reasonable choice where changing MXCSR is undesirable, or
on x86-64 processors without AVX, which `avx_fma` does not support.
Measurements on a processor with a cheaper `vldmxcsr` could change the picture.

On WebAssembly, build with `-Ctarget-feature=+simd128` where the runtime
supports it: the `wasm32` backend is roughly twice as fast as the portable one
on interval operations.

## Running the benchmarks

The benchmarks are in `bench/`, a separate package, so that criterion does not
affect inari's minimum supported Rust version. They need a recent Rust
(tested with 1.96). Primitives are exposed through the hidden `__bench`
feature, which is not public API.

```bash
cd bench
RUSTFLAGS=-Ctarget-cpu=haswell cargo bench -- --save-baseline avx_fma
RUSTFLAGS=-Ctarget-cpu=haswell cargo bench --features force-generic -- --baseline avx_fma
```

For WebAssembly, with wasmtime on the path:

```bash
cd bench
export CARGO_TARGET_WASM32_WASIP1_RUNNER=wasmtime
RUSTFLAGS=-Ctarget-feature=+simd128 cargo bench --target wasm32-wasip1
```
