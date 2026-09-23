# Benchmarks

A comparison of the backends of inari: the hardware backend for x86-64
(`avx_fma`), the portable backend (`generic`, see `src/simd/generic.rs`) and the
WebAssembly backend (`wasm32`, see `src/simd/wasm32.rs`), measured on 2026-09-22.
The backend for x86-64 without AVX (`sse42`, see `src/simd/x86_64/sse42.rs`) was
added later and measured on 2026-09-23; it has a section of its own below.

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
| sse42 | `sse42` (`F64X2` in an `__m128d`, no MXCSR switching) | `RUSTFLAGS=-Ctarget-cpu=nehalem` |
| generic, Nehalem | `generic` with Dekker's algorithm | `RUSTFLAGS=-Ctarget-cpu=nehalem`, `--features force-generic` |

WebAssembly configurations, all on `wasm32-wasip1` under wasmtime, and all
without an FMA, which WebAssembly does not have:

| Column | Backend | Flags |
|---|---|---|
| scalar | `generic` | none |
| simd128 | `generic`, which the compiler may auto-vectorize | `RUSTFLAGS=-Ctarget-feature=+simd128`, `--features force-generic` |
| wasm32 | `wasm32` (`F64X2` in a `v128`) | `RUSTFLAGS=-Ctarget-feature=+simd128` |

## Variance

Every configuration was run twice, interleaved. The tables show the lower of the
two medians, and "spread" is the largest difference between the runs of any one
configuration in that row, relative to the lower one. Treat differences below
about 5% as not significant.

All spreads are at or below 3%, except the `sqrt` rows on x86-64, which were
measured over five rounds instead of two. There the two `generic` columns land
in one of two clusters about 15% apart, depending on the process, while
`sqrt1_ru` in the same process stays within 1%; `avx_fma` and the WebAssembly
columns do not show it. The same two clusters appear before the change that
vectorized `sqrt`, so the `generic` numbers below should be read as unchanged
from the previous measurement rather than as an improvement.

The `sse42` section was measured over twelve rounds, which shows that the same
bimodality affects more than `sqrt`: `generic, Nehalem` runs `sub/PP` at 6.3 ns
in two rounds out of twelve and at 8.85 ns in the other ten, and `avx_fma` runs
the determinant at 211 ns in seven and at 239 ns in five. Because the clusters
are per process and not per round, the lowest of twelve rounds is drawn from the
faster cluster far more often than the lowest of two, which would flatter a
column measured over many rounds. That section therefore reports the **median**
over the twelve rounds rather than the lowest, and its spread column is the
widest of the three configurations in that row, which is why rows dominated by a
bimodal `generic` or `avx_fma` cell show 40–51%. The `sse42` column itself is
within about 1% in every row, and the `sse42` ratios are the same to two decimal
places whether the lowest or the median is used.

## Results

Times are the median per operation: per `F64X2` operation (two lanes) for the
primitives, except `sqrt1_ru`, which is scalar and is timed per square root,
and per interval operation otherwise. Note that an interval `sqrt` needs the
square roots of both endpoints, and that everything around them (the empty test,
taking the two endpoints apart and building the result) goes through `F64X2`,
which is why it does not follow `sqrt1_ru` from one backend to the next.

Ratios are relative to the first column; below 1 means faster than it.

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
| sqrt/P | 3.70 | 7.21 | 1.95× | 11.27 | 3.05× | 17% |
| sqrt/M | 7.88 | 7.80 | 0.99× | 9.20 | 1.17× | 10% |
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

### x86-64 without AVX

The `sse42` backend applies the method of `wasm32` to `__m128d`: it computes the
round-toward-+∞ fast paths explicitly and never touches MXCSR. It is compared
with `avx_fma`, the default where AVX and FMA are available, and with `generic`
at the same feature level, which is the alternative on a processor without them.
Medians over twelve rounds; see "Variance" above.

| Benchmark | avx_fma (ns) | sse42 (ns) | ratio | generic, Nehalem (ns) | ratio | spread |
|---|--:|--:|--:|--:|--:|--:|
| add/PP | 9.24 | 5.01 | 0.54× | 12.10 | 1.31× | 6% |
| add/PM | 9.25 | 5.00 | 0.54× | 10.70 | 1.16× | 10% |
| add/MM | 9.26 | 5.00 | 0.54× | 12.25 | 1.32× | 5% |
| sub/PP | 9.25 | 5.14 | 0.56× | 8.85 | 0.96× | 41% |
| sub/PM | 9.26 | 5.14 | 0.56× | 10.17 | 1.10× | 13% |
| sub/MM | 9.26 | 5.14 | 0.55× | 11.84 | 1.28× | 4% |
| mul/PP | 10.40 | 7.71 | 0.74× | 15.87 | 1.53× | 4% |
| mul/PN | 10.41 | 7.75 | 0.74× | 15.66 | 1.50× | 3% |
| mul/PM | 10.40 | 7.77 | 0.75× | 15.99 | 1.54× | 3% |
| mul/NP | 10.42 | 7.79 | 0.75× | 16.27 | 1.56× | 3% |
| mul/NN | 10.41 | 7.83 | 0.75× | 16.11 | 1.55× | 1% |
| mul/NM | 10.41 | 7.79 | 0.75× | 15.60 | 1.50× | 3% |
| mul/MP | 10.40 | 7.80 | 0.75× | 16.04 | 1.54× | 4% |
| mul/MN | 10.42 | 7.80 | 0.75× | 15.64 | 1.50× | 1% |
| mul/MM | 18.91 | 13.59 | 0.72× | 30.03 | 1.59× | 3% |
| div/PP | 10.18 | 9.80 | 0.96× | 23.04 | 2.26× | 6% |
| div/PN | 10.18 | 9.90 | 0.97× | 24.70 | 2.43× | 4% |
| div/MP | 10.17 | 9.90 | 0.97× | 21.50 | 2.11× | 7% |
| div/NN | 10.18 | 9.77 | 0.96× | 22.82 | 2.24× | 6% |
| div/PM (= ℝ) | 3.76 | 2.99 | 0.79× | 4.93 | 1.31× | 1% |
| sqrt/P | 3.69 | 6.64 | 1.80× | 12.98 | 3.52× | 8% |
| sqrt/M | 7.93 | 9.56 | 1.21× | 10.22 | 1.29× | 11% |
| Horner, degree 8, P | 263.63 | 143.38 | 0.54× | 225.31 | 0.85× | 9% |
| Horner, degree 8, M | 401.61 | 173.66 | 0.43× | 375.31 | 0.93× | 5% |
| 3×3 determinant | 210.90 | 96.20 | 0.46× | 322.63 | 1.53× | 14% |

| Benchmark | avx_fma (ns) | sse42 (ns) | ratio | generic, Nehalem (ns) | ratio | spread |
|---|--:|--:|--:|--:|--:|--:|
| add_ru/throughput | 9.29 | 5.21 | 0.56× | 8.36 | 0.90× | 51% |
| add_ru/latency | 8.76 | 9.05 | 1.03× | 13.03 | 1.49× | 0% |
| mul_ru/throughput | 9.26 | 6.76 | 0.73× | 11.00 | 1.19× | 7% |
| mul_ru/latency | 8.76 | 10.66 | 1.22× | 16.28 | 1.86× | 0% |
| div_ru/throughput | 9.27 | 9.21 | 0.99× | 31.61 | 3.41× | 1% |
| div_ru/latency | 8.76 | 14.66 | 1.67× | 33.15 | 3.78× | 0% |
| mul_add_ru/throughput | 9.01 | 15.06 | 1.67× | 36.10 | 4.01× | 1% |
| mul_add_ru/latency | 8.53 | 15.82 | 1.86× | 22.90 | 2.68× | 1% |
| sqrt1_ru/throughput | 2.32 | 5.82 | 2.51× | 5.82 | 2.51× | 0% |
| sqrt1_ru/latency | 7.33 | 7.51 | 1.02× | 7.51 | 1.02× | 0% |

`sse42` takes `sqrt1_rd`, `sqrt1_ru` and `sub1_ru` from `generic`, which is why
its scalar square root matches the `generic, Nehalem` column exactly.

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
| sqrt/P | 15.84 | 15.19 | 0.96× | 10.20 | 0.64× | 1% |
| sqrt/M | 13.55 | 14.92 | 1.10× | 13.58 | 1.00× | 0% |
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
- `sqrt/P` is where the vectorized square root pays: `avx_fma` takes 0.51× the
  time of `generic` with an FMA, and `wasm32` 0.64× that of the scalar
  configuration. Both do the two endpoints in one vector square root, correcting
  the lanes in opposite directions. The scalar `sqrt1_ru` is unchanged, so the
  two WebAssembly `generic` columns are unchanged too.
- `sqrt/M` does not benefit: an interval containing zero has the square root of
  only one endpoint to compute, so `Interval::sqrt` keeps a scalar branch for it
  rather than feeding a zero lane to a fast path that would reject it. The
  vectorized backends are then on par with the portable one, as the table shows.
  Going through the vector path instead cost 1.9× on `sqrt/M`, which is what
  that branch avoids.
- The fallback of `avx_fma::sqrt_rd_ru`, for the rare arguments its fast path
  rejects, is kept out of line. Inlined, it brings two whole scalar square roots
  with it, which makes `Interval::sqrt` too large for its callers to inline: that
  alone cost 1.6× on `sqrt/M`, which never reaches the fallback.
- `sse42` beats `avx_fma` on most of what interval code does, despite having
  neither AVX nor FMA: 0.54× on addition, 0.55× on subtraction, 0.74× on
  multiplication, 0.46× on the determinant and 0.43–0.54× on Horner. The reason
  is the fixed ~9 ns MXCSR cost above: computing the fast path explicitly takes
  more instructions but they pipeline, whereas `avx_fma`'s do not. The gain is
  largest where `avx_fma` is purely MXCSR-bound (addition) and shrinks as the
  real work grows (multiplication, then division).
- Where `sse42` loses, it loses to the FMA rather than to the rounding mode.
  `mul_add_ru` is 1.67× slower and the scalar `sqrt1_ru` 2.51×, because both fall
  back to Dekker's TwoProduct: seven multiplications where an FMA would do one.
  `sqrt/P` is 1.80× slower for the same reason. This suggests that the same
  method with FMA enabled, rather than SSE-only, would beat `avx_fma` across the
  board; that has not been measured.
- Division is the one place where `avx_fma`'s serialization is nearly hidden:
  `div_ru/throughput` is 0.99× and the interval divisions 0.96–0.97×, because a
  `vdivpd` is slow enough on Zen 2 to cover the MXCSR switches around it.
  `sse42`'s division latency is still 1.67× worse.
- `add_ru/latency` is 1.03× and `mul_ru/latency` 1.22×, against 0.56× and 0.73×
  in throughput. The fast paths are long dependency chains, so `sse42` wins only
  where independent operations can overlap — which is the common case in
  interval code, and is why the composite benchmarks favour it so strongly.

## Conclusion

On x86-64 processors without AVX-512, `generic` should not replace `avx_fma` as
the default. It is not uniformly faster: it wins on polynomial evaluation and
loses on multiplication and division, which dominate typical interval code such
as the determinant. The differences are mostly within 1.3×, except division, so
`force-generic` is a reasonable choice where changing MXCSR is undesirable.

`sse42` is a different matter. On processors without AVX it is the only backend
besides `force-generic`, and it is 1.2–2.1× faster than `generic` at the same
feature level on everything but subtraction and Horner. But it is also faster
than `avx_fma` on a processor that could run `avx_fma`: 0.54× on addition and
0.46× on the determinant, losing only on `sqrt`, `mul_add` and division latency,
all of which trace to the missing FMA rather than to the method. Whether the
method should therefore replace `avx_fma` as the default — as an FMA-enabled
variant, which would remove exactly those losses — is an open question that
these measurements do not settle, because no such backend exists yet.
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
