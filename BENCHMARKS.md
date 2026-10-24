# Benchmarks

A comparison of the backends of inari, in four sittings:

- 2026-09-22: `avx_fma`, then the default for x86-64, which set MXCSR around
  every instruction to make the hardware round, against the portable backend
  (`generic`, see `src/simd/generic.rs`) and the WebAssembly backend (`wasm32`,
  see `src/simd/wasm32.rs`).
- 2026-09-23: `sse42` (see `src/simd/x86_64/sse42.rs`), for x86-64 without AVX,
  which computes the directed roundings explicitly instead of switching MXCSR.
- 2026-09-23, later: `fma` (see `src/simd/x86_64/fma.rs`), the same method where
  an FMA is available. It is now the default on x86-64 with AVX and FMA, and
  `avx_fma` has been removed from the crate.
- 2026-10-24: `fma` on multiplications whose products are below 2^-968, before
  and after the change that keeps them on its fast path, against inari 2.0.0.

`avx_fma` is the base column of the first three x86-64 sections, so that the
two explicit backends are measured against what they replaced, and against each
other. The fourth uses inari 2.0.0 instead, as `avx_fma` had been removed by
then. The x86-64 backend of 2.0.0 is `avx_fma` as it was before its square root
changed, so its multiplication is `avx_fma`'s. No backend for x86-64 changes the
rounding mode any more: `avx512f` uses per-instruction embedded rounding, and
the other two round by correcting a round-to-nearest result.

## Setup

- CPU: AMD Ryzen 9 3900X (Zen 2, 12 cores). It has no AVX-512, so the `avx512f`
  backend could not be measured.
- Linux 7.0, `schedutil` governor, rustc 1.96.0, criterion 0.7.0, wasmtime 49.0.
- `lto = "fat"` and `codegen-units = 1`, so that the primitives are inlined into
  the benchmarks as they are within inari.
- Each run was pinned to one core with `taskset -c 11`, on an otherwise idle
  machine (load average 1 to 3). Rounds measured on a loaded machine were
  discarded; see "Variance".

Native configurations:

| Column | Backend | Flags |
|---|---|---|
| avx_fma | `avx_fma`, since removed (MXCSR switched around every instruction) | `RUSTFLAGS=-Ctarget-cpu=haswell` |
| fma | `fma` (default; `F64X2` in an `__m128d`, no MXCSR switching) | `RUSTFLAGS=-Ctarget-cpu=haswell` |
| generic, FMA | `generic` with FMA | `RUSTFLAGS=-Ctarget-cpu=haswell`, `--features force-generic` |
| generic, no FMA | `generic` with Dekker's algorithm | `RUSTFLAGS=-Ctarget-cpu=x86-64`, `--features force-generic` |
| sse42 | `sse42` (`F64X2` in an `__m128d`, no MXCSR switching) | `RUSTFLAGS=-Ctarget-cpu=nehalem` |
| generic, Nehalem | `generic` with Dekker's algorithm | `RUSTFLAGS=-Ctarget-cpu=nehalem`, `--features force-generic` |

`avx_fma` and `fma` take the same flags because the target features are what
selects a backend. They were measured against each other from a snapshot of the
tree that still had both, with a temporary Cargo feature choosing between them;
that snapshot is the code the `fma` section below reports.

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

The `fma` section was also run over twelve rounds, but peer builds on the
machine pushed the load average to between 20 and 70 during rounds 1–4 and
9–12, so only rounds 5–8, which ran at a load average of 1 to 2, are reported.
Those four rounds are unusually quiet: `avx_fma` and `fma` each repeat every
primitive to within 0.5% across them, and the two rows where both backends run
identical code — `sqrt1_ru`, which both take from `generic`, and `div/PM`,
which returns ℝ without arithmetic — come out at 1.00×. The `fma` ratios are
again the same to two decimal places whether the lowest or the median is used;
the medians are reported, as above. The wide spreads in that section come from
the bimodal `generic, FMA` column, except on the determinant, where `avx_fma`
runs at 226 ns in round 5 and at 192.5 ns in the other three.

The tiny-products section was measured over eight rounds, with the load average
and the idle time of the pinned core's SMT sibling recorded for every run. Peer
jobs pushed the load average up to 22 and the sibling's idle time down to 23%
during rounds 1 and 2, which are discarded. Rounds 3–8 ran at a load average
below 3 with the sibling at least 99.4% idle, but not all of them ran the same
configurations: rounds 3 and 4 ran 2.0.0, `fma` before the change and a first
version of the change, rounds 5 and 6 the code before the change and both
versions of it, and only rounds 7 and 8 ran the three configurations of the
table, interleaved. Those two are reported, as the mean of their two medians,
which is within 0.4% of the lower one since the spread is at most 0.7% in every
row. Rounds 3–6 agree with them to within 1% on every configuration they share.
The first version of the change is the subject of an observation below.

Composite benchmarks drift between sittings in a way the primitives do not: the
`avx_fma` 3×3 determinant is 236 ns in the first section, 211 ns in the `sse42`
section and 193 ns in the `fma` section, while its `add/PP` is 9.25, 9.24 and
9.25 ns. Compare ratios within a section, not times across sections.

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

### x86-64 with AVX and FMA

The `fma` backend applies the method of `sse42` — the fast paths of `generic`
computed on both lanes at once, with the few inputs whose checks fail in either
lane recomputed by `generic` — to a target that has an FMA. The FMA makes
TwoProduct and the remainders of division and of the square root one instruction
each instead of Dekker's algorithm, and widens their exactness hypotheses enough
that some of the exponent checks drop out. It is compared with `avx_fma`, which
it replaced as the default, and with `generic` at the same feature level.
Medians over the four idle rounds; see "Variance" above.

| Benchmark | avx_fma (ns) | fma (ns) | ratio | generic, FMA (ns) | ratio | spread |
|---|--:|--:|--:|--:|--:|--:|
| add/PP | 9.25 | 4.32 | 0.47× | 9.22 | 1.00× | 23% |
| add/PM | 9.25 | 4.32 | 0.47× | 9.93 | 1.07× | 15% |
| add/MM | 9.25 | 4.32 | 0.47× | 9.70 | 1.05× | 18% |
| sub/PP | 9.26 | 4.43 | 0.48× | 8.63 | 0.93× | 42% |
| sub/PM | 9.25 | 4.43 | 0.48× | 9.81 | 1.06× | 15% |
| sub/MM | 9.26 | 4.42 | 0.48× | 9.72 | 1.05× | 19% |
| mul/PP | 10.41 | 6.23 | 0.60× | 13.22 | 1.27× | 1% |
| mul/PN | 10.42 | 6.35 | 0.61× | 13.13 | 1.26× | 2% |
| mul/PM | 10.40 | 6.24 | 0.60× | 13.25 | 1.27× | 1% |
| mul/NP | 10.42 | 6.35 | 0.61× | 13.27 | 1.27× | 1% |
| mul/NN | 10.42 | 6.46 | 0.62× | 13.43 | 1.29× | 2% |
| mul/NM | 10.41 | 6.46 | 0.62× | 13.05 | 1.25× | 0% |
| mul/MP | 10.41 | 6.23 | 0.60× | 12.91 | 1.24× | 1% |
| mul/MN | 10.41 | 6.23 | 0.60× | 13.14 | 1.26× | 1% |
| mul/MM | 18.91 | 9.24 | 0.49× | 22.57 | 1.19× | 2% |
| div/PP | 10.17 | 6.84 | 0.67× | 26.15 | 2.57× | 1% |
| div/PN | 10.18 | 6.84 | 0.67× | 18.37 | 1.80× | 5% |
| div/MP | 10.18 | 7.05 | 0.69× | 26.97 | 2.65× | 0% |
| div/NN | 10.18 | 7.05 | 0.69× | 26.27 | 2.58× | 0% |
| div/PM (= ℝ) | 4.22 | 4.22 | 1.00× | 4.91 | 1.16× | 1% |
| sqrt/P | 3.70 | 3.81 | 1.03× | 8.20 | 2.22× | 20% |
| sqrt/M | 8.22 | 6.82 | 0.83× | 8.27 | 1.01× | 8% |
| Horner, degree 8, P | 249.13 | 112.83 | 0.45× | 168.96 | 0.68× | 1% |
| Horner, degree 8, M | 321.84 | 132.68 | 0.41× | 273.12 | 0.85× | 4% |
| 3×3 determinant | 192.51 | 64.00 | 0.33× | 252.91 | 1.31× | 17% |

| Benchmark | avx_fma (ns) | fma (ns) | ratio | generic, FMA (ns) | ratio | spread |
|---|--:|--:|--:|--:|--:|--:|
| add_ru/throughput | 9.31 | 5.01 | 0.54× | 8.13 | 0.87× | 48% |
| add_ru/latency | 8.76 | 8.99 | 1.03× | 12.99 | 1.48× | 0% |
| mul_ru/throughput | 9.25 | 3.99 | 0.43× | 9.16 | 0.99× | 17% |
| mul_ru/latency | 8.75 | 7.06 | 0.81× | 13.09 | 1.50× | 0% |
| div_ru/throughput | 9.25 | 5.43 | 0.59× | 9.83 | 1.06× | 8% |
| div_ru/latency | 8.76 | 9.82 | 1.12× | 15.33 | 1.75× | 1% |
| mul_add_ru/throughput | 9.01 | 7.54 | 0.84× | 19.34 | 2.15× | 1% |
| mul_add_ru/latency | 8.53 | 9.44 | 1.11× | 11.23 | 1.32× | 1% |
| sqrt1_ru/throughput | 2.32 | 2.32 | 1.00× | 2.32 | 1.00× | 2% |
| sqrt1_ru/latency | 7.33 | 7.33 | 1.00× | 7.33 | 1.00× | 1% |

`fma` takes `sqrt1_rd` and `sqrt1_ru` from `generic`, as `avx_fma` did, which is
why all three columns agree on `sqrt1_ru`.

### x86-64 with AVX and FMA, tiny products

`fma`'s `mul_ru` rounds a product upward by computing its rounding error with an
FMA, and relies on that error being exact only where the product's exponent is
at least -968. It used to hand every pair with a lane below that to `generic`,
whose slow path rounds the exact product in 128-bit integer arithmetic. It now
scales one factor of such a lane by 2^128, rounds the scaled product on the fast
path and scales the result back (`mul_ru_tiny` in `src/simd/x86_64/fma.rs`), so
that only products that overflow still go to `generic`. The `mul_tiny`
benchmark multiplies the same intervals as `mul`, with the first factor scaled
by 2^-1010, so that every product lies between 2^-1010 and 2^-1006: normal, but
below 2^-968. Operations recorded from rcad, a CAD kernel, had most of their
products that small.

The columns are the same benchmark built against inari 2.0.0 from crates.io,
and `fma` before and after that change. 2.0.0 lets the hardware round, so its
products cost the same at any size. Means of rounds 7 and 8; see "Variance"
above.

| Benchmark | 2.0.0 (ns) | fma before (ns) | ratio | fma after (ns) | ratio | spread |
|---|--:|--:|--:|--:|--:|--:|
| mul/PP | 10.48 | 6.39 | 0.61× | 6.40 | 0.61× | 0% |
| mul/PN | 10.50 | 6.39 | 0.61× | 6.42 | 0.61× | 1% |
| mul/PM | 10.46 | 6.38 | 0.61× | 6.41 | 0.61× | 0% |
| mul/NP | 10.48 | 6.62 | 0.63× | 6.64 | 0.63× | 0% |
| mul/NN | 10.48 | 6.40 | 0.61× | 6.41 | 0.61× | 0% |
| mul/NM | 10.50 | 6.38 | 0.61× | 6.40 | 0.61× | 0% |
| mul/MP | 10.50 | 6.42 | 0.61× | 6.40 | 0.61× | 1% |
| mul/MN | 10.49 | 6.41 | 0.61× | 6.43 | 0.61× | 0% |
| mul/MM | 19.03 | 9.75 | 0.51× | 9.55 | 0.50× | 1% |
| mul_tiny/PP | 10.48 | 49.75 | 4.75× | 8.57 | 0.82× | 0% |
| mul_tiny/PN | 10.51 | 49.41 | 4.70× | 8.62 | 0.82× | 1% |
| mul_tiny/PM | 10.53 | 49.37 | 4.69× | 8.59 | 0.82× | 1% |
| mul_tiny/NP | 10.53 | 49.60 | 4.71× | 8.78 | 0.83× | 1% |
| mul_tiny/NN | 10.53 | 50.06 | 4.75× | 8.66 | 0.82× | 0% |
| mul_tiny/NM | 10.51 | 49.46 | 4.71× | 8.59 | 0.82× | 0% |
| mul_tiny/MP | 10.53 | 49.08 | 4.66× | 8.57 | 0.81× | 1% |
| mul_tiny/MN | 10.52 | 49.43 | 4.70× | 8.57 | 0.81× | 1% |
| mul_tiny/MM | 19.02 | 95.64 | 5.03× | 15.32 | 0.81× | 0% |

The operations recorded from rcad are not part of this repository. rcad's own
benchmark replays four streams of them, timing this crate and 2.0.0 in the same
process and reporting the best of three passes. For `a * b`, in ns per interval
multiplication, `fma` / 2.0.0:

| Stream | before (ns) | ratio | after (ns) | ratio |
|---|--:|--:|--:|--:|
| 0228ef21 | 33.79 / 10.93 | 3.09× | 12.51 / 12.64 | 0.99× |
| 150ecee9 | 32.65 / 10.89 | 3.00× | 12.70 / 12.15 | 1.05× |
| 347a8978 | 33.42 / 10.88 | 3.07× | 12.64 / 12.42 | 1.02× |
| 481232f8 | 15.57 / 9.04 | 1.72× | 13.12 / 9.12 | 1.44× |

Over all the operations of a stream, timed one kind at a time, the total went
from 1.96, 1.90, 1.94 and 1.16 times 2.0.0's to 0.84, 0.86, 0.84 and 1.02. Both
versions give results bit-identical to 2.0.0's on every operation. Two things
are unexplained. 2.0.0's own `a * b` takes 12.2–12.6 ns on the first three
streams in the benchmark rebuilt for "after", but 10.9 ns in the one that
measured "before", although both build 2.0.0 from the same source; the two
builds differ only in how they depend on this crate and in some extra counters,
and on 481232f8 they agree. Against 10.9 ns, the 12.5–12.7 ns of `fma` would be
1.14–1.17×. And 481232f8's `a * b` is 1.23 times 2.0.0's even with the exponent
of every operand set to 0, so most of its remaining 1.44× is not caused by tiny
products.

### x86-64 without AVX

The `sse42` backend applies the method of `wasm32` to `__m128d`: it computes the
round-toward-+∞ fast paths explicitly and never touches MXCSR. It is compared
with `avx_fma`, then the default where AVX and FMA are available, and with
`generic` at the same feature level, which is the alternative on a processor
without them.
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
- `sqrt_rd_ru` in the removed `avx_fma` backend kept its fallback, for the rare
  arguments the fast path rejects, out of line. Inlined, it brings two whole
  scalar square roots with it, which makes `Interval::sqrt` too large for its
  callers to inline: that alone cost 1.6× on `sqrt/M`, which never reaches the
  fallback.
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
  `sqrt/P` is 1.80× slower for the same reason. This suggested that the same
  method with FMA enabled, rather than SSE-only, would beat `avx_fma` across the
  board, which the `fma` section confirms.
- Division is the one place where `avx_fma`'s serialization is nearly hidden:
  `div_ru/throughput` is 0.99× and the interval divisions 0.96–0.97×, because a
  `vdivpd` is slow enough on Zen 2 to cover the MXCSR switches around it.
  `sse42`'s division latency is still 1.67× worse.
- `add_ru/latency` is 1.03× and `mul_ru/latency` 1.22×, against 0.56× and 0.73×
  in throughput. The fast paths are long dependency chains, so `sse42` wins only
  where independent operations can overlap — which is the common case in
  interval code, and is why the composite benchmarks favour it so strongly.
- `fma` extends that win and removes the losses. Against `avx_fma` it is 0.47×
  on addition and subtraction, 0.49–0.62× on multiplication, 0.67–0.69× on
  division, 0.41–0.45× on Horner and 0.33× on the determinant. The three rows
  where `sse42` lost to the missing FMA come back to par or better:
  `mul_add_ru/throughput` from 1.67× to 0.84×, `sqrt/P` from 1.80× to 1.03× and
  the scalar `sqrt1_ru` from 2.51× to 1.00×.
- With an FMA the multiplication fast path is shorter than the addition's, which
  still needs a TwoSum: `mul_ru/throughput` is 0.43×, the largest gain of any
  primitive, against 0.54× for `add_ru/throughput`. Without an FMA the order is
  the other way round (`sse42`: 0.73× and 0.56×).
- Division gains where `sse42` could not: 0.59× in the primitive and 0.67–0.69×
  on intervals, against 0.99× and 0.96–0.97×. A `vdivpd` is slow enough on Zen 2
  to hide `avx_fma`'s MXCSR switches, but not slow enough to hide Dekker's
  TwoProduct in the remainder, which the FMA replaces with one instruction.
- The latency rows are where `fma` loses, and the losses are real rather than
  noise: `add_ru/latency` 1.03×, `mul_add_ru/latency` 1.11× and `div_ru/latency`
  1.12×, while the two rows that run identical code in both backends sit at
  1.00×. Correcting a round-to-nearest result adds to the dependency chain, and
  `avx_fma`'s MXCSR switches, being fixed overhead, do not. It is not uniform,
  though: `mul_ru/latency` is 0.81×, because there the FMA removes more of the
  chain than the correction adds. No composite benchmark is latency-bound, which
  is why they all favour `fma` by 2 to 3 times.
- `sqrt/M` is 0.83×, which the square root itself does not explain: both
  backends take `sqrt1_rd` and `sqrt1_ru` from `generic` and neither reaches the
  vector path for an interval containing zero. The remaining difference is in
  the code around it, and has not been traced further.
- Products below 2^-968 used to cost `fma` 4.7–5.0 times what they cost 2.0.0,
  which lets the hardware round and so has no such boundary: 49–50 ns per
  interval multiplication, and 96 ns on `mul/MM`, against 10.5 and 19.0 ns.
  Rounding them on the fast path brings this down to 0.81–0.83× of 2.0.0, and to
  0.16–0.18× of what it was. They still cost 1.32–1.35 times as much as ordinary
  products, and 1.60 times on `mul/MM`, for the scaling and the second
  correction.
- Ordinary products do not pay for it: on `mul`, `fma` after the change takes
  0.997–1.004 times as long as before, except on `mul/MM`, where it takes 0.98
  times as long (0.975 in rounds 5 and 6). That has not been traced.
- The first version of the change handed the lanes it had already rounded to
  `mul_ru_tiny`. LLVM then computed that rounding before the branch to the tiny
  path rather than after it, which made `mul` 3–4% slower than before on every
  class but `mul/MM` (1.00×), with no tiny product in the input. Having each
  branch round by itself removed the cost. As with `sqrt_rd_ru` above, the rare
  path cost the common one through the code the compiler generated around it,
  not through being taken.

## Conclusion

Letting the hardware round was the wrong default on x86-64. `avx_fma` spent
about 9 ns per operation saving, setting and restoring MXCSR, which is more than
the arithmetic costs and more than correcting a round-to-nearest result costs.
`fma` does the latter and is faster on every interval operation but `sqrt/P`,
where it is 1.03×: 0.47× on addition, 0.60× on multiplication, 0.67× on
division, 0.41–0.45× on Horner and 0.33× on a 3×3 determinant. It pays for this
with 3 to 12% on the latency of three primitives, where the correction lengthens
a dependency chain — a trade worth making, since interval code has independent
operations to overlap far more often than it has serial ones. The operands of
all these benchmarks are of ordinary size: products below 2^-968 made `fma`'s
multiplication 4.7–5.0 times slower than 2.0.0's until it rounded them on its
fast path too, and it now takes 0.81–0.83 times as long on them. `fma` is
therefore the default, and `avx_fma` has been removed.

`generic` is not a replacement for either. It has no fixed rounding-mode cost
but needs many more instructions: against `avx_fma` it was within about 1.3×
either way except on division, but against `fma` it is slower on every row of
both tables except `sqrt1_ru`, which the two share, by 1.2× on the rows that do
almost no arithmetic and by 1.5–4× on the rest. `force-generic` remains the
portable fallback rather than a faster one.

`sse42` is the same method as `fma` without an FMA, and is 1.2–2.1× faster than
`generic` at the same feature level on everything but subtraction and Horner.
Where it loses to `fma` it loses to the missing FMA — `sqrt`, `mul_add` and the
remainder in division — not to the method.

All of this is one microarchitecture. `fma`'s advantage is bounded by what
`vldmxcsr` costs — it trades a fixed per-operation overhead for more
instructions that pipeline — so a processor on which switching the rounding
mode is cheap could reverse the comparison entirely. That has not been measured.
The comparison with `generic`, which switches nothing either, does not depend on
this.

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
RUSTFLAGS=-Ctarget-cpu=haswell cargo bench -- --save-baseline fma
RUSTFLAGS=-Ctarget-cpu=haswell cargo bench --features force-generic -- --baseline fma
```

The 2.0.0 column of the tiny-products section comes from `benches/intervals.rs`
copied into a package of its own that depends on `inari = "=2.0.0"` with
`default-features = false`, with the same `[profile.bench]`.

For WebAssembly, with wasmtime on the path:

```bash
cd bench
export CARGO_TARGET_WASM32_WASIP1_RUNNER=wasmtime
RUSTFLAGS=-Ctarget-feature=+simd128 cargo bench --target wasm32-wasip1
```
