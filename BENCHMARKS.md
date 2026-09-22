# Benchmarks

A comparison of the hardware backend for x86-64 (`avx_fma`) with the portable
backend (`generic`, see `src/simd/generic.rs`), measured on 2026-09-22.

## Setup

- CPU: AMD Ryzen 9 3900X (Zen 2, 12 cores). It has no AVX-512, so the `avx512f`
  backend could not be measured.
- Linux 7.0, `schedutil` governor, rustc 1.96.0, criterion 0.7.0.
- `lto = "fat"` and `codegen-units = 1`, so that the primitives are inlined into
  the benchmarks as they are within inari.
- Each run was pinned to one core with `taskset -c 11`.

Three configurations:

| Column | Backend | Flags |
|---|---|---|
| avx_fma | `avx_fma` (default) | `RUSTFLAGS=-Ctarget-cpu=haswell` |
| generic, FMA | `generic` with FMA | `RUSTFLAGS=-Ctarget-cpu=haswell`, `--features force-generic` |
| generic, no FMA | `generic` with Dekker's algorithm | `RUSTFLAGS=-Ctarget-cpu=x86-64`, `--features force-generic` |

The last one stands in for targets without FMA, such as wasm32.

## Variance

The machine was shared with other jobs (load average 3 to 14 during the runs),
so the numbers are noisy. Every configuration was run twice, interleaved. The
table shows the lower of the two medians, and "spread" is the largest
difference between the two runs of any one configuration, relative to the lower
one. Most spreads are below 15%. Treat rows with a larger spread as only
indicative, and differences below about 15% as not significant.

## Results

Times are the median per operation: per `F64X2` operation (two lanes) for the
primitives, and per interval operation otherwise. Ratios are relative to
`avx_fma`; below 1 means `generic` is faster.

Primitives (`throughput`: 1024 independent operations; `latency`: a chain of
1024 dependent operations):

| Benchmark | avx_fma (ns) | generic, FMA (ns) | ratio | generic, no FMA (ns) | ratio | spread |
|---|--:|--:|--:|--:|--:|--:|
| add_ru/throughput | 9.29 | 11.07 | 1.19× | 8.48 | 0.91× | 2% |
| add_ru/latency | 8.75 | 13.22 | 1.51× | 13.18 | 1.51× | 11% |
| mul_ru/throughput | 9.32 | 9.23 | 0.99× | 11.04 | 1.19× | 51% |
| mul_ru/latency | 8.76 | 13.10 | 1.50× | 16.38 | 1.87× | 10% |
| div_ru/throughput | 9.34 | 10.03 | 1.07× | 32.09 | 3.44× | 56% |
| div_ru/latency | 8.77 | 15.51 | 1.77× | 35.34 | 4.03× | 8% |
| mul_add_ru/throughput | 9.08 | 19.81 | 2.18× | 38.01 | 4.19× | 33% |
| mul_add_ru/latency | 8.56 | 11.23 | 1.31× | 23.65 | 2.76× | 64% |
| sqrt1_ru/throughput | 8.65 | 2.12 | 0.25× | 4.08 | 0.47× | 3% |
| sqrt1_ru/latency | 8.32 | 7.32 | 0.88× | 7.75 | 0.93× | 7% |

Interval operations (1024 independent operations; P: positive, N: negative,
M: containing zero):

| Benchmark | avx_fma (ns) | generic, FMA (ns) | ratio | generic, no FMA (ns) | ratio | spread |
|---|--:|--:|--:|--:|--:|--:|
| add/PP | 9.30 | 7.42 | 0.80× | 12.06 | 1.30× | 25% |
| add/PM | 9.25 | 8.67 | 0.94× | 10.74 | 1.16× | 14% |
| add/MM | 9.25 | 8.20 | 0.89× | 12.35 | 1.34× | 18% |
| sub/PP | 9.27 | 6.06 | 0.65× | 8.90 | 0.96× | 43% |
| sub/PM | 9.38 | 8.53 | 0.91× | 10.36 | 1.10× | 35% |
| sub/MM | 9.32 | 8.18 | 0.88× | 11.94 | 1.28× | 32% |
| mul/PP | 10.42 | 13.21 | 1.27× | 16.01 | 1.54× | 2% |
| mul/PN | 10.54 | 13.09 | 1.24× | 15.98 | 1.52× | 2% |
| mul/PM | 10.48 | 13.10 | 1.25× | 16.22 | 1.55× | 3% |
| mul/NP | 10.49 | 13.13 | 1.25× | 15.48 | 1.48× | 3% |
| mul/NN | 10.42 | 13.14 | 1.26× | 15.81 | 1.52× | 48% |
| mul/NM | 10.41 | 13.06 | 1.25× | 15.88 | 1.52× | 48% |
| mul/MP | 10.43 | 13.04 | 1.25× | 16.24 | 1.56× | 10% |
| mul/MN | 10.41 | 13.02 | 1.25× | 15.74 | 1.51× | 3% |
| mul/MM | 18.87 | 23.17 | 1.23× | 30.77 | 1.63× | 2% |
| div/PP | 10.17 | 25.97 | 2.55× | 25.25 | 2.48× | 2% |
| div/PN | 10.21 | 16.41 | 1.61× | 26.03 | 2.55× | 5% |
| div/MP | 10.17 | 26.38 | 2.59× | 27.26 | 2.68× | 33% |
| div/NN | 10.19 | 26.08 | 2.56× | 25.72 | 2.52× | 18% |
| div/PM (= ℝ) | 3.78 | 4.94 | 1.31× | 4.99 | 1.32× | 83% |
| sqrt/P | 17.72 | 7.22 | 0.41× | 11.37 | 0.64× | 15% |
| Horner, degree 8, P | 252.98 | 170.89 | 0.68× | 231.03 | 0.91× | 43% |
| Horner, degree 8, M | 319.61 | 367.73 | 1.15× | 383.56 | 1.20× | 38% |
| 3×3 determinant | 281.84 | 324.16 | 1.15× | 323.66 | 1.15× | 13% |

## Observations

- Every `avx_fma` primitive costs about 9 ns, both in throughput and in latency,
  whatever the operation (even `sqrt`). The backend saves, sets and restores
  MXCSR (`vstmxcsr`/`vldmxcsr`) around each instruction. As throughput equals
  latency, this apparently serializes the operations on Zen 2, and dominates
  the cost.
- `generic` has no such fixed cost, but needs more instructions per operation.
  It is faster for square roots (2.4× in interval `sqrt`) and roughly on par
  for addition and subtraction. It is about 1.25× slower for interval
  multiplication and 1.6–2.6× slower for division.
- On the composite benchmarks, the two are within about 15% of each other
  (Horner with M: 1.15× slower, Horner with P: 0.68×, determinant: 1.15× slower).
- Without FMA, multiplication and especially division and `mul_add` get
  slower, as Dekker's TwoProduct replaces a single FMA.
- Not explained: interval division is about as slow with FMA as without it
  (except P/N), although the `div_ru` primitive is 3× slower without FMA.

## Conclusion

On x86-64 processors without AVX-512, `generic` should not replace `avx_fma` as
the default. It is not uniformly faster: it wins clearly only on square roots,
and it loses on multiplication and division, which dominate typical interval
code such as the determinant. The differences are small enough, though (mostly
within 1.3×, except division), that `force-generic` is a reasonable choice
where changing MXCSR is undesirable, or on x86-64 processors without AVX,
which `avx_fma` does not support. Measurements on an idle machine, and on a
processor with a cheaper `vldmxcsr`, could change the picture.

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
