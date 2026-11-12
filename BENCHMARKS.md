# Benchmarks

A comparison of the backends of inari, in eleven sittings:

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
- 2026-10-30: the `mul_add_ru` rows of the `fma` section again, after
  `fma::mul_add_ru` stopped computing a separate result for its special cases.
- 2026-11-02: `sin`, `cos` and `tan` of intervals with `fma`, before and after
  the change that made them tightest.
- 2026-11-03: `sse42`, `wasm32` and `generic` on multiplications whose products
  are below 2^-968, before and after the changes that round them on the fast
  path after scaling, as `fma` does.
- 2026-11-04: `sse42`, `wasm32` and `fma` on the same products, before and after
  the change that rounds them with one TwoProduct.
- 2026-11-05: `generic` before and after the change that rounds up without a
  branch where there is no FMA, and `fma` against inari 2.0.0 again, on the same
  products.
- 2026-11-08: multiplication in `generic` without an FMA and on WebAssembly
  again, after that change, with the composite benchmarks on WebAssembly, and
  two builds of the same source against each other.
- 2026-11-12: `sin`, `cos` and `tan` of intervals with `fma` again, after they
  moved from MPFR to inari's own kernel, against the last commit that computed
  them with MPFR.

`avx_fma` is the base column of the first three x86-64 sections, so that the
two explicit backends are measured against what they replaced, and against each
other. The fourth uses inari 2.0.0 instead, as `avx_fma` had been removed by
then. The x86-64 backend of 2.0.0 is `avx_fma` as it was before its square root
changed, so its multiplication is `avx_fma`'s. The fifth sitting, which replaces
two rows of the `fma` section, builds `avx_fma` from `cc5e384`, the commit
before its removal. The sixth compares builds of three commits, all with `fma`,
rather than backends. The seventh, like the sixth, compares builds of commits:
two, each in five configurations, and the eighth and the ninth two, each in
four. The ninth also compares the first of its two, the main branch then, with
inari 2.0.0, both with `fma`'s flags. The tenth compares two builds of the
source of `5543a69` with each other, and with builds of `d894347` and
`0a7c306`, and measures rows of the sections on x86-64, x86-64 without AVX and
WebAssembly again, the first two against `avx_fma` built from `cc5e384`, as the
fifth does. The eleventh compares two builds of the source of `893b06c` with
each other, and with a build of `036d2f8`, the commit before `3f625c0` moved the
bounds of the elementary functions from MPFR to the kernel. No backend for
x86-64 changes the rounding mode any more: `avx512f` uses per-instruction
embedded rounding, and the other two round by correcting a round-to-nearest
result.

## Setup

- CPU: AMD Ryzen 9 3900X (Zen 2, 12 cores). It has no AVX-512, so the `avx512f`
  backend could not be measured.
- Linux 7.0, rustc 1.96.0, criterion 0.7.0, wasmtime 49.0. The governor was
  `schedutil` in the first sitting and in the fifth; the second and the third
  ran without a restart since the first, and the fourth without one before the
  fifth. Read before and after the eleventh, it was `powersave`, with boost on;
  the driver, read after it, was `amd-pstate-epp`. The sixth to the tenth did
  not record the governor, and the machine had run without a restart since
  2026-11-01, before the sixth, so they may have run under `powersave` too.
- `lto = "fat"` and `codegen-units = 1`, so that the primitives are inlined into
  the benchmarks as they are within inari.
- The first table of the trigonometric section, and the `036d2f8` column of its
  second, measure builds in which `sin`, `cos` and `tan` computed their bounds
  with MPFR. They linked GMP 6.3.0 and MPFR 4.2.2, as built by `gmp-mpfr-sys`
  1.7.1. inari now computes those bounds with its own multi-precision kernel
  (`src/dyadic.rs`), which the other columns of the second table measure.
- Each run was pinned to one core with `taskset -c 11`, on an otherwise idle
  machine (load average below 3). Rounds measured on a loaded machine were
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
that snapshot is the code the `fma` section below reports, except in its two
`mul_add_ru` rows, which were measured again later from separate builds (see
"Variance").

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

The two `mul_add_ru` rows of the `fma` section were measured again on
2026-10-30, as the first measurement predates `a6650cb`, after which
`fma::mul_add_ru` no longer computes a separate result for its special cases.
`avx_fma` was built from `cc5e384`, the commit before its removal, and `fma` and
`generic, FMA` from `8bbcf64`, with the flags above. Twelve rounds ran the
configurations interleaved, in an order rotated from round to round, with the
load average, the idle time of the pinned core's SMT sibling and the busy time
of the other cores recorded for every run. A round was kept only if, in each of
its runs, the load average was below 3 at the start and at the end, the sibling
was at least 99% idle and the other cores were busy for at most two cores' worth
of time in total. All twelve were, at a load average of 1.0 to 2.0, and the rows
report their medians; the `fma` ratios are the same to two decimal places
whether the lowest or the median is used. `fma` as it was before `a6650cb`,
built from `469f00b`, ran in the same rounds as a control. It takes 0.84× the
time of `avx_fma` on `mul_add_ru/throughput` and 1.11× on `mul_add_ru/latency`,
as in the first measurement, so the move from 0.84× to 0.78× is not the
sitting's. `fma` now takes 0.93× the time it did in throughput and 1.00× in
latency, and the fast path of the throughput loop is 110 instructions long
instead of 124. These builds cannot tell how much of the 0.93× is the change,
though: `sqrt1_ru`, which ran alongside, came out at 0.95× between the same two
builds in throughput, although the code of its benchmark is the same in both but
for addresses. Against `avx_fma`, where `sqrt1_ru` compiled to the same code but
for one range check, it came out at 1.04× for `fma` and at 1.10× for `fma`
before `a6650cb`. In latency, all of them run `sqrt1_ru` at 1.00× of `avx_fma`.
A throughput row can therefore move by 5% between two builds of the same code,
and the same difference in the code came out at 4% in one pair of builds and at
10% in another. The longer `mul_add_ru` loop moved less in the one comparison
there is: against `avx_fma`, `fma` before `a6650cb` runs `sqrt1_ru/throughput`
at 1.10× here and ran it at 1.00× in the first measurement, but runs both
`mul_add_ru` rows at the same ratios as then. One comparison does not show how
sensitive that loop is.

The trigonometric section was measured on 2026-11-02 between 03:00 and 03:55.
`ced0d5f`, the commit before `216e5f5`, `216e5f5` itself and `b2390de` were
built with the `trig` benchmark of `416ba9a` added (the measured copy differed
only in comments), with
`RUSTFLAGS=-Ctarget-cpu=haswell`, so with `fma`, and with the bench package's
`--features gmp`, which the `trig` benchmark needed then, as the trigonometric
functions called MPFR. Each
benchmark took criterion's default 3 s of warm-up and 5 s of measurement, with
flat sampling, as one iteration takes milliseconds. Nine rounds ran the three
builds interleaved, in an order rotated from round to round, and were kept
under the rule of the `mul_add_ru` rows above. All nine were, at a load average
of at most 1.4 with the sibling at least 99.6% idle, and the rows report their
medians. The ratios differ by at most 0.02 when the lowest of the nine or
criterion's own median estimate is used instead. On `narrow`, the code that the
three builds run differs only by the comparison that `216e5f5` adds, which finds
the two floors equal, and by the two later changes that the section lists. There
the later builds take 0.99–1.00 times as long as `ced0d5f`, and single rounds
range from 0.97 to 1.01: that is how far these builds move on code they almost
share.

The section on tiny products in `sse42`, `wasm32` and `generic` was measured on
2026-11-03 between 03:00 and 03:57. `0a7c306`, the commit before `76d2bab`, and
`1259e7f` were built with the `bench/` manifest of `1259e7f`
(`benches/intervals.rs` is the same in both), each in five configurations:
`sse42`, `generic, Nehalem` and `generic, FMA` with the flags of "Setup", and
`wasm32` and `scalar` on `wasm32-wasip1`. Each WebAssembly build was compiled
once with `wasmtime compile`, for the host's processor, and run precompiled, so
that every run executed the same machine code and none spent time compiling it.
Each benchmark took 2 s of warm-up and 3 s of measurement. Nine rounds ran the
ten builds, the two builds of each configuration one after the other, in an
order rotated from round to round and with the two swapped every other round,
and were kept under the rule of the `mul_add_ru` rows above. All nine were, at a
load average of 0.3 to 2.0, with the sibling at least 99.5% idle and the other
cores busy for at most 0.31 cores' worth of time, and the rows report their
medians. The spread of a row is the largest, over its four cells, of the
difference between a cell's slowest and fastest round, relative to the fastest.
The ratios differ by at most 0.02 when the lowest of the nine or criterion's
own median estimate is used instead. In the three `generic` configurations, the
interval multiplication and the `generic::mul_ru` it calls compile to the same
instructions in both builds (for WebAssembly, to the same machine code from
wasmtime), but for addresses and for the cold function that `mul_ru` calls on
the lanes its fast path rejects. There `mul` takes 0.99–1.02 times as long after
as before, and single rounds range from 0.96 to 1.03: that is how far these
builds move on code they share. Not all of it is noise between rounds, though:
`scalar` takes 1.015–1.032 times as long on `mul/MM` in every one of the nine.

The section on tiny products with one TwoProduct was measured on 2026-11-04
between 03:00 and 03:55. `3c0a19c`, the main branch then, and `77a4138`, which
changes `mul_ru_tiny` in `sse42`, `wasm32` and `fma` and nothing in `bench/`,
were built in four configurations: `sse42`, `fma` and `generic, Nehalem` with
the flags of "Setup", and `wasm32` on `wasm32-wasip1`, compiled and run as in
the previous sitting. The builds of `77a4138` were made from a commit with the
same files and an earlier message. Each benchmark took 2 s of warm-up and 3 s of
measurement. Eleven rounds ran the eight builds, in an order rotated and swapped
as in the previous sitting, and ten were kept under the rule of the `mul_add_ru`
rows above: in round 9, the sibling was 98.0% idle during one run. The ten ran
at a load average of at most 1.3, with the sibling at least 99.5% idle and the
other cores busy for at most 0.24 cores' worth of time, and the rows report
their medians, and the spread as the previous sitting defines it. The ratios
differ by at most 0.01 when the lowest of the ten or criterion's own median
estimate is used instead. With `force-generic`, none of the three files that
`77a4138` changes is compiled, so the two builds of `generic, Nehalem` compile
the same source. There the ratios range from 0.98 to 1.06, and single rounds
from 0.965 to 1.076. Not all of it is noise between rounds: `generic, Nehalem`
takes 1.04–1.08 times as long on `mul/PP` after as before in every one of the
ten. Before the change, `sse42`, `wasm32` and `generic, Nehalem` take within 2%
of the "after" column of the previous sitting, whose code for these
multiplications is the same.

The section on rounding up without a branch, and the section on `fma` against
inari 2.0.0 after it, were measured on 2026-11-05 between 03:00 and 03:56.
`d894347`, the main branch then, and `d2a2f0c`, which changes
`generic::mul1_ru_fast` and nothing in `bench/`, were built in four
configurations: `generic, Nehalem`, `generic, FMA` and `fma` with the flags of
"Setup", and `scalar` on `wasm32-wasip1`, compiled and run as in the seventh
sitting. The builds of `d2a2f0c` were made from the same change on top of
`d894347`. With `-Ctarget-cpu=nehalem` and `force-generic`, `generic::mul_ru`
and `generic::mul1_ru_tiny` compile to the same instructions, at the same
addresses, in the build measured and in one of `d2a2f0c` itself. inari 2.0.0
was built as in "Running the benchmarks", with `RUSTFLAGS=-Ctarget-cpu=haswell`.
Each benchmark took 2 s of warm-up and 3 s of measurement. Nine rounds ran the
nine builds, the two of each configuration, and 2.0.0 with those of `fma`, one
after the other, in an order rotated from round to round and reversed within
each configuration every other round, and six were kept under the rule of the
`mul_add_ru` rows above: in rounds 5, 6 and 7, the load average was between 3.0
and 3.6 at the start or the end of two or three runs, although the sibling
stayed at least 99.8% idle and the other cores were busy for at most 0.30 cores'
worth of time. The six ran at a load average of at most 3.0, with the sibling at
least 99.4% idle and the other cores busy for at most 0.37 cores' worth of time,
and the rows report their medians, and the spread as the seventh sitting
defines it: over the four cells of a row in the first of the two sections, and
over the two in the second. The ratios differ by at most 0.01 when the lowest
of the six or criterion's own median estimate is used instead, except for the
lowest in `generic, Nehalem`. In round 4, its build of `d2a2f0c` ran all six
benchmarks faster than in the other five rounds, `mul_tiny/PP` and
`mul_tiny/PM` at 43.3–43.7 ns against 47.9–49.1 ns, and it did the same in
round 7, which is not kept. This is where the spreads of 11–12% come from, and
the lowest gives 0.86–0.87 on `mul/PP` and `mul/PM`, 0.84 on `mul_tiny/PP` and
`mul_tiny/PM`, and 0.95 on `mul_tiny/MM`. In `fma`, `fma::mul_ru` and the
`generic::mul1_ru_tiny` that it can fall back on compile to the same
instructions, at the same addresses, in both builds. There the ratios are 1.00
on every row, and single rounds range from 0.99 to 1.01: that is how far these
builds move on code they share. Before the change, `generic, Nehalem`,
`generic, FMA` and `scalar` take within 2.5% of the "after" column of the
seventh sitting, whose code for these multiplications is the same. 2.0.0 takes
within 0.5% of the time it took in the fourth sitting on each of the six rows of
its table. `fma` at `d894347` takes up to 5% longer on `mul`, and up to 3% on
`mul_tiny`, than in the "after" column of the previous sitting, whose code for
these multiplications is the same; on `mul`, it is within 1% of that sitting's
"before" column.

The section on two builds of the same source, and the cells of the sections on
x86-64, x86-64 without AVX and WebAssembly that their notes name, were measured
on 2026-11-08 between 00:08 and 01:41. Copies A and B of the source of `5543a69`
were built in `generic, Nehalem`, `generic, FMA` and `wasm32`, and copy A also
in `generic, no FMA`, `scalar` and `simd128`, with the flags of "Setup", and the
WebAssembly builds were compiled and run as in the seventh sitting. These builds
run the code of `8aef5d1`, the main branch then: of the files in `src/`,
`bench/` and the manifests, the two commits differ only in `src/dyadic.rs` and
the files under `src/dyadic/`, which are compiled only for inari's own tests.
`d894347` was built in `generic, Nehalem` and `generic, FMA`, `0a7c306` in
`wasm32`, and `avx_fma` from `cc5e384`, as in the fifth sitting, all with the
`bench/` of `5543a69` and one `Cargo.lock`. Each benchmark took 2 s of warm-up
and 3 s of measurement. Each comparison ran in rounds of its own, seven for
`mul` and `mul_ru` on WebAssembly, seven on x86-64, seven for the composite
benchmarks on WebAssembly, ten for the copies in `generic` and twelve for those
in `wasm32`, the builds in an order rotated from round to round and reversed
every other round, and all were kept under the rule of the `mul_add_ru` rows
above. They ran at a load average of 1.00 to 1.46, with the sibling at least
99.3% idle and the other cores busy for at most 0.60 cores' worth of time, and
the rows report their medians, and the spread as the seventh sitting defines
it, over the cells measured in this sitting. The ratios differ by at most 0.02
when criterion's own median estimate is used instead, and when the lowest is,
except in the `generic, Nehalem` cells of the table of x86-64 without AVX, where
the lowest gives ratios 0.02–0.04 lower on `mul` in every class but `MM`, and
0.08 lower on `mul_ru/throughput`, which is bimodal there (see the note under
that table). `scalar` ran both `mul_ru` rows slower in one round of the seven,
by 18% in throughput and 6% in latency, which is where their spreads come
from. On the composite
benchmarks, copy B of `wasm32` takes 0.997–0.998 times as long as copy A, and
single rounds range from 0.987 to 1.016. The build of copy A in `generic,
Nehalem` ran in the rounds on x86-64 and in those of the copies, and takes
1.000–1.015 times as long on `mul/PP`, `mul/PM` and `mul/MM` in the first as in
the second, each inside the range that copy B takes against copy A there in
single rounds. `avx_fma` takes within 1.3% of its columns in the sections on
x86-64 and x86-64 without AVX on every row measured. On `mul`, `d894347` takes
within 2.4% of the "before" column of the ninth sitting, copy A in the same two
configurations within 1.7% of that sitting's "after" column, and `0a7c306`
within 1.1% of the "before" column of the seventh. The probe on DAZ
and FTZ (see "Observations") ran fifteen rounds of copy A in `generic, FMA`,
`fma` and `generic, Nehalem`, and twelve were kept: in rounds 2, 4 and 13, the
sibling was 98.2–98.7% idle during one or two runs.

The second table of the trigonometric section was measured on 2026-11-12
between 19:49 and 20:23. Copies A and B of the source of `893b06c`, the main
branch then, the same byte for byte but at paths of different lengths, and
`036d2f8`, the commit before `3f625c0`, were each built with its own `bench/`
and `RUSTFLAGS=-Ctarget-cpu=haswell`, so with `fma`, and `036d2f8` with the
bench package's `--features gmp`, which its `trig` benchmark needed.
The binaries of the two copies differ in 89% of their bytes. Each benchmark
took 2 s of warm-up and 3 s of measurement, with flat sampling. Nine rounds ran
the three builds, in an order rotated from round to round and reversed every
other round, and were kept under the rule of the `mul_add_ru` rows above. All
nine were, at a load average of 0.93 to 2.25, with the sibling at least 99.3%
idle and the other cores busy for at most 1.38 cores' worth of time, and the
rows report their medians, and the spread as the seventh sitting defines it.
The ratios to `036d2f8` differ by at most 1% of their value, and B/A by at most
0.01, when the lowest of the nine or criterion's own median estimate is used
instead. Copy B takes 0.98–1.01 times as long as copy A on every row but
`tan/narrow`, and single rounds range from 0.965 to 1.028 on those rows: that
is how far two builds of the same code move here. Not all of it is noise
between rounds, though: on `tan/narrow`, copy B takes 1.05 times as long as
copy A, and 1.03–1.07 times in every one of the nine. `036d2f8` takes 3–4%
longer than `b2390de` did in the first table on every row, so compare the times
of the second table with those of the first only through its `036d2f8` column.

Composite benchmarks drift between sittings more than the primitives do: the
`avx_fma` 3×3 determinant is 236 ns in the first section, 211 ns in the `sse42`
section and 193 ns in the `fma` section, while its `add/PP` is 9.25, 9.24 and
9.25 ns. Of its primitives, only `sqrt1_ru/throughput` has moved by more than
1%: it takes 2.32 ns in all three sections, but 2.13 ns in the fifth sitting,
built from `cc5e384`. Compare ratios within a section, not times across
sections.

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
| mul/PP | 10.42 | 13.10 | 1.26× | 14.53 | 1.38× | 1% |
| mul/PN | 10.43 | 12.96 | 1.24× | 14.65 | 1.39× | 1% |
| mul/PM | 10.41 | 12.89 | 1.24× | 14.65 | 1.39× | 1% |
| mul/NP | 10.41 | 13.15 | 1.26× | 14.61 | 1.39× | 1% |
| mul/NN | 10.43 | 13.17 | 1.26× | 14.63 | 1.39× | 1% |
| mul/NM | 10.42 | 12.96 | 1.24× | 14.57 | 1.39× | 2% |
| mul/MP | 10.41 | 13.00 | 1.25× | 14.61 | 1.39× | 2% |
| mul/MN | 10.42 | 12.88 | 1.24× | 14.50 | 1.38× | 1% |
| mul/MM | 18.91 | 22.28 | 1.18× | 32.01 | 1.67× | 3% |
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
| mul_ru/throughput | 9.26 | 9.16 | 0.99× | 11.12 | 1.19× | 1% |
| mul_ru/latency | 8.75 | 13.11 | 1.50× | 16.09 | 1.82× | 1% |
| div_ru/throughput | 9.28 | 9.84 | 1.06× | 31.99 | 3.45× | 0% |
| div_ru/latency | 8.76 | 15.34 | 1.75× | 35.01 | 4.00× | 0% |
| mul_add_ru/throughput | 9.00 | 19.40 | 2.16× | 37.60 | 4.18× | 1% |
| mul_add_ru/latency | 8.52 | 11.25 | 1.32× | 23.60 | 2.77× | 0% |
| sqrt1_ru/throughput | 2.32 | 2.13 | 0.92× | 4.07 | 1.76× | 1% |
| sqrt1_ru/latency | 7.33 | 7.33 | 1.00× | 7.75 | 1.06× | 0% |

The `generic, no FMA` cells of the `mul` and `mul_ru` rows were measured again
on 2026-11-08, after `d2a2f0c` changed how `generic` rounds up without an FMA:
medians over seven rounds (see "Variance"). Their ratios are against `avx_fma`
built from `cc5e384` and timed in the same rounds, within 1.3% of the `avx_fma`
column on each of these rows, and their spread is the larger of the two
measurements'. The other cells of these rows are from the first sitting.

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
Medians over the four idle rounds, except in the `mul_add_ru` rows, which were
measured again later over twelve; see "Variance" above.

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
| mul_add_ru/throughput | 9.07 | 7.06 | 0.78× | 19.32 | 2.13× | 2% |
| mul_add_ru/latency | 8.58 | 9.52 | 1.11× | 11.38 | 1.33× | 1% |
| sqrt1_ru/throughput | 2.32 | 2.32 | 1.00× | 2.32 | 1.00× | 2% |
| sqrt1_ru/latency | 7.33 | 7.33 | 1.00× | 7.33 | 1.00× | 1% |

`fma` takes `sqrt1_rd` and `sqrt1_ru` from `generic`, as `avx_fma` did, which is
why all three columns agree on `sqrt1_ru`.

### x86-64 with AVX and FMA, tiny products

`fma`'s `mul_ru` rounds a product upward by computing its rounding error with an
FMA, and relies on that error being exact only where the product's exponent is
at least -968. It used to hand every pair with a lane below that to `generic`,
whose slow path rounded the exact product in 128-bit integer arithmetic. It now
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

### `sse42`, `wasm32` and `generic`, tiny products

`sse42` and `wasm32` round a product upward as `fma` does, but compute its
rounding error with Dekker's TwoProduct, which they rely on only where the
product is at least 2^-968 and below 2^1023 in magnitude and both factors are
below 2^996. They used to hand to `generic` every pair with a lane of finite,
nonzero factors that failed this check. `generic` checks each lane by itself:
in the same way without an FMA, and with one only that the product is finite
and at least 2^-968 in magnitude. It rounded the lanes that failed in 128-bit
integer arithmetic (`mul1_ru_slow`). `76d2bab` gave `sse42` and `wasm32` the
`mul_ru_tiny` of `fma`, with Dekker's TwoProduct in place of the FMA, and
`6fa4f83` gave `generic` `mul1_ru_tiny`, which does the same for one lane (in
`src/simd/x86_64/sse42.rs`, `src/simd/wasm32.rs` and `src/simd/generic.rs`).
Products below 2^-968 in magnitude are now rounded there, and only the lanes
that fail the check for another reason still go to `mul1_ru_slow`. The
benchmarks are `mul` and `mul_tiny` of the section above.

The columns are `0a7c306`, the commit before `76d2bab`, and `1259e7f`, the main
branch when this was measured, each built in the configurations of "Setup" that
the first column names. Only the classes `PP`, `PM` and `MM` were run, so that
more rounds fit into the time the host was idle. Times are in ns per interval
multiplication, medians over nine rounds; see "Variance" above.

| Configuration | Class | mul before (ns) | after (ns) | ratio | mul_tiny before (ns) | after (ns) | ratio | spread |
|---|---|--:|--:|--:|--:|--:|--:|--:|
| sse42 | PP | 7.72 | 7.76 | 1.00× | 68.90 | 30.06 | 0.44× | 2% |
| sse42 | PM | 7.80 | 7.75 | 0.99× | 69.39 | 29.77 | 0.43× | 1% |
| sse42 | MM | 14.12 | 13.91 | 0.99× | 136.35 | 58.59 | 0.43× | 1% |
| generic, Nehalem | PP | 16.14 | 16.07 | 1.00× | 72.75 | 52.20 | 0.72× | 4% |
| generic, Nehalem | PM | 16.15 | 16.17 | 1.00× | 68.88 | 51.85 | 0.75× | 4% |
| generic, Nehalem | MM | 31.18 | 31.00 | 0.99× | 131.28 | 102.00 | 0.78× | 2% |
| generic, FMA | PP | 13.37 | 13.30 | 0.99× | 50.58 | 25.94 | 0.51× | 3% |
| generic, FMA | PM | 13.19 | 13.20 | 1.00× | 50.08 | 26.32 | 0.53× | 5% |
| generic, FMA | MM | 23.01 | 22.70 | 0.99× | 99.34 | 49.41 | 0.50× | 4% |
| wasm32 | PP | 14.60 | 14.98 | 1.03× | 91.45 | 40.17 | 0.44× | 3% |
| wasm32 | PM | 14.64 | 15.12 | 1.03× | 91.23 | 38.66 | 0.42× | 3% |
| wasm32 | MM | 25.28 | 25.89 | 1.02× | 174.72 | 74.54 | 0.43× | 2% |
| scalar | PP | 31.43 | 31.40 | 1.00× | 87.89 | 63.80 | 0.73× | 1% |
| scalar | PM | 30.74 | 30.84 | 1.00× | 88.07 | 63.52 | 0.72× | 1% |
| scalar | MM | 54.34 | 55.53 | 1.02× | 162.02 | 123.80 | 0.76× | 1% |

On `mul`, the `generic` configurations run the same code in both builds but for
addresses (see "Variance"). In `sse42` and `wasm32`, `mul_ru` used to round
both lanes and then test whether both passed the check; it now tests first, as
`fma`'s does, and each branch rounds by itself.

### `sse42`, `wasm32` and `fma`, tiny products with one TwoProduct

Where the fast path of `mul_ru` rejects a lane, `mul_ru_tiny` in these three
backends rounded two products upward in both lanes: `x * y`, which it keeps in
the lanes that the fast path accepts, and `x * 2^128 * y`, which it scales back
in the others. `77a4138` makes it select the factors in each lane and round one
product: `x * y` where the fast path accepts the lane, and the scaled product
where it rejects it. Every lane's result is the same as before, bit for bit.
The branch of `mul_ru` that takes no tiny lane, which `mul` runs, compiles to
the same instructions in `sse42` and `fma`, with other registers, and to the
same WebAssembly in `wasm32`, with other locals; wasmtime's code for `mul_ru`
saves one callee-saved register fewer.

The columns are `3c0a19c`, the main branch when this was measured, and
`77a4138`, each built in the configuration that the first column names, with
the flags of "Setup" and `wasm32` on `wasm32-wasip1`. The classes are those of
the section above. Times are in ns per interval multiplication, medians over
ten rounds; see "Variance" above.

| Configuration | Class | mul before (ns) | after (ns) | ratio | mul_tiny before (ns) | after (ns) | ratio | spread |
|---|---|--:|--:|--:|--:|--:|--:|--:|
| sse42 | PP | 7.73 | 7.70 | 1.00× | 30.13 | 11.67 | 0.39× | 2% |
| sse42 | PM | 7.76 | 7.73 | 1.00× | 29.71 | 11.63 | 0.39× | 1% |
| sse42 | MM | 13.95 | 13.91 | 1.00× | 59.11 | 22.37 | 0.38× | 2% |
| fma | PP | 6.38 | 6.15 | 0.96× | 8.54 | 8.14 | 0.95× | 1% |
| fma | PM | 6.39 | 6.37 | 1.00× | 8.55 | 8.30 | 0.97× | 1% |
| fma | MM | 9.52 | 9.27 | 0.97× | 15.23 | 14.75 | 0.97× | 2% |
| wasm32 | PP | 14.99 | 15.09 | 1.01× | 40.52 | 21.23 | 0.52× | 2% |
| wasm32 | PM | 14.97 | 15.04 | 1.00× | 39.02 | 21.24 | 0.54× | 2% |
| wasm32 | MM | 25.83 | 25.74 | 1.00× | 75.31 | 39.74 | 0.53× | 1% |
| generic, Nehalem | PP | 15.99 | 16.91 | 1.06× | 52.12 | 52.01 | 1.00× | 4% |
| generic, Nehalem | PM | 15.89 | 15.98 | 1.01× | 51.53 | 50.68 | 0.98× | 4% |
| generic, Nehalem | MM | 30.74 | 31.01 | 1.01× | 101.76 | 101.25 | 0.99× | 1% |

On `mul`, `sse42` takes 1.00 times as long as before and `wasm32` 1.00–1.01,
within the 0.98–1.06 of `generic, Nehalem`, whose two builds compile the same
source. `fma` takes 0.96–1.00 times as long, and less than 0.99 times on
`mul/PP` and `mul/MM` in every round, but as `generic, Nehalem` takes more than
1.04 times as long on `mul/PP` in every round, these builds cannot tell whether
that comes from the change.

### `generic`, rounding up without a branch

Without an FMA, `generic::mul1_ru_fast` rounded a product `p` upward by
branching on the sign of its error `e`, which Dekker's TwoProduct computes:
`step_up(p)` if `e > 0`, and `p` otherwise. `d2a2f0c` computes it from the bit
pattern of `p` without a branch (`step_up_if`, in `src/simd/generic.rs`), with
the same result wherever `mul_ru` uses it. With an FMA, the code is unchanged:
`generic::mul_ru` and `generic::mul1_ru_tiny` in `generic, FMA`, and
`fma::mul_ru` in `fma`, compile to the same instructions before and after, but
for addresses. In `generic, Nehalem`, `generic::mul_ru` now has 205
instructions and 11 conditional jumps, against 221 and 19 before: `seta` reads
the comparison of each lane's error with zero, where the code before branched
with `ja` or `jbe` on eight comparisons with zero.

The columns are `d894347`, the main branch when this was measured, and
`d2a2f0c` (see "Variance"), each built in the configuration that the first
column names, with the flags of "Setup" and `scalar` on `wasm32-wasip1`. The
classes are those of the section above. Times are in ns per interval
multiplication, medians over six rounds; see "Variance" above.

| Configuration | Class | mul before (ns) | after (ns) | ratio | mul_tiny before (ns) | after (ns) | ratio | spread |
|---|---|--:|--:|--:|--:|--:|--:|--:|
| generic, Nehalem | PP | 16.37 | 14.49 | 0.89× | 52.04 | 48.85 | 0.94× | 12% |
| generic, Nehalem | PM | 16.28 | 14.56 | 0.89× | 51.59 | 47.98 | 0.93× | 11% |
| generic, Nehalem | MM | 30.77 | 32.24 | 1.05× | 100.72 | 97.43 | 0.97× | 3% |
| generic, FMA | PP | 13.33 | 13.36 | 1.00× | 25.85 | 26.10 | 1.01× | 3% |
| generic, FMA | PM | 13.19 | 13.22 | 1.00× | 25.68 | 25.97 | 1.01× | 2% |
| generic, FMA | MM | 22.70 | 23.24 | 1.02× | 50.00 | 49.42 | 0.99× | 2% |
| scalar | PP | 31.53 | 20.27 | 0.64× | 63.84 | 48.27 | 0.76× | 1% |
| scalar | PM | 31.08 | 20.47 | 0.66× | 64.07 | 47.91 | 0.75× | 2% |
| scalar | MM | 56.05 | 39.22 | 0.70× | 124.65 | 98.27 | 0.79× | 1% |
| fma | PP | 6.43 | 6.40 | 1.00× | 8.34 | 8.38 | 1.00× | 1% |
| fma | PM | 6.42 | 6.42 | 1.00× | 8.36 | 8.39 | 1.00× | 1% |
| fma | MM | 9.54 | 9.55 | 1.00× | 14.84 | 14.81 | 1.00× | 2% |

`generic, Nehalem` takes 1.05 times as long as before on `mul/MM`, and 1.03–1.08
times in every round. `generic, FMA`, whose `mul_ru` and `mul1_ru_tiny` compile
to the same instructions in both builds but for addresses, takes 1.02 times as
long there, and 1.01–1.04 times in every round, so these builds cannot tell how
much of the 1.05 comes from the change. `fma`, whose code for these
multiplications is the same in both builds, takes 1.00 times as long on every
row. Measured again on 2026-11-08, against two builds of the source of
`5543a69`, which comes after `d2a2f0c`, the ratio of `generic, Nehalem` on
`mul/MM` is 1.03, more than those two builds differ there, but `generic, FMA`
takes 1.01 times as long, and up to 1.035 times in single rounds, so these
builds cannot tell either; see the section on two builds of the same source
below.

### `fma` against inari 2.0.0, tiny products with one TwoProduct

The columns are `mul` and `mul_tiny` built against inari 2.0.0 from crates.io,
as in the first section on tiny products, and at `d894347`, the main branch
when this was measured, which includes `77a4138`. Both were built with
`RUSTFLAGS=-Ctarget-cpu=haswell` and ran in the same rounds: the `fma` column is
the "before" column of `fma` in the section above. The classes are those of the
section above. Times are in ns per interval multiplication, medians over six
rounds; see "Variance" above.

| Benchmark | 2.0.0 (ns) | fma (ns) | ratio | spread |
|---|--:|--:|--:|--:|
| mul/PP | 10.50 | 6.43 | 0.61× | 1% |
| mul/PM | 10.50 | 6.42 | 0.61× | 1% |
| mul/MM | 19.06 | 9.54 | 0.50× | 2% |
| mul_tiny/PP | 10.50 | 8.34 | 0.79× | 1% |
| mul_tiny/PM | 10.53 | 8.36 | 0.79× | 1% |
| mul_tiny/MM | 18.99 | 14.84 | 0.78× | 1% |

2.0.0 takes 1.00 times as long on `mul_tiny` as on `mul` in each class, as it
lets the hardware round.

### `generic` and `wasm32`, two builds of the same source

Two copies of the source of `5543a69`, the same byte for byte but at paths of
different lengths and depths, copy A and copy B, were each built in three
configurations: `generic, Nehalem` and `generic, FMA` with the flags of "Setup",
and `wasm32` on `wasm32-wasip1`, compiled and run as in the seventh sitting.
Their binaries differ in 63–71% of their bytes. In `generic, Nehalem` and
`generic, FMA`, `generic::mul_ru` compiles to the same instructions in both
copies but for addresses. They ran in the same rounds as `d894347`, the "before"
column of the section on rounding up without a branch, and `0a7c306`, the
"before" column of the section on tiny products in `sse42`, `wasm32` and
`generic`; see "Variance" above. Times are in ns per interval multiplication,
medians over ten rounds for `generic` and twelve for `wasm32`.

| Configuration | Class | d894347 (ns) | copy A (ns) | ratio | copy B (ns) | ratio | B/A | spread |
|---|---|--:|--:|--:|--:|--:|--:|--:|
| generic, Nehalem | PP | 16.76 | 14.38 | 0.86× | 14.49 | 0.86× | 1.01× | 4% |
| generic, Nehalem | PM | 16.01 | 14.32 | 0.89× | 14.53 | 0.91× | 1.01× | 5% |
| generic, Nehalem | MM | 31.13 | 31.91 | 1.03× | 31.92 | 1.03× | 1.00× | 3% |
| generic, FMA | PP | 13.42 | 13.41 | 1.00× | 13.29 | 0.99× | 0.99× | 3% |
| generic, FMA | PM | 13.21 | 13.27 | 1.00× | 13.59 | 1.03× | 1.02× | 2% |
| generic, FMA | MM | 22.85 | 23.12 | 1.01× | 23.20 | 1.02× | 1.00× | 3% |

| Class | 0a7c306 (ns) | copy A (ns) | ratio | copy B (ns) | ratio | B/A | spread |
|---|--:|--:|--:|--:|--:|--:|--:|
| PP | 14.77 | 14.98 | 1.01× | 15.00 | 1.02× | 1.00× | 7% |
| PM | 14.79 | 14.93 | 1.01× | 15.00 | 1.01× | 1.00× | 7% |
| MM | 25.44 | 25.48 | 1.00× | 25.47 | 1.00× | 1.00× | 9% |

Copy B takes 0.99–1.02 times as long as copy A on every row, and single rounds
range from 0.958 to 1.038 in `generic, Nehalem` (0.991 to 1.013 on `mul/MM`),
from 0.973 to 1.038 in `generic, FMA`, and from 0.928 to 1.011 in `wasm32`,
where copy A ran 6–8% slower in one round of the twelve than in the others.
That is how far two builds of the same code move here.

Against `d894347`, `generic, Nehalem` takes 0.86–0.91 times as long on `mul/PP`
and `mul/PM`, where the section on rounding up without a branch has 0.89, and
1.03 times as long on `mul/MM`, more than its two copies differ there (by at
most 1.3% in single rounds), and 1.010–1.035 times in single rounds. `generic,
FMA`, whose `generic::mul_ru` compiles to the same instructions at `d894347`
and in copy A but for addresses, takes 1.01 times as long on `mul/MM`, and
0.996–1.035 times in single rounds, so these builds cannot tell how much of the
1.03 comes from `d2a2f0c` either.
`wasm32` takes 1.00–1.01 times as long in copy A as at `0a7c306`, inside the
0.93–1.08 that either of its two copies takes against the other in single
rounds.

### x86-64 with AVX and FMA, trigonometric functions

`Interval::sin`, `cos` and `tan` locate the multiples of π/2 (of π for `cos`) in
their argument [a, b] by dividing it by `Interval::FRAC_PI_2` (`Interval::PI`)
and taking the floors of the bounds of the quotient. The division only encloses
the exact quotient, so when a bound was close to such a multiple, relative to
its magnitude, its floor could be wrong, and the result could then be wider than
the tightest. `216e5f5` keeps the division as the fast path. Where the two floors
differ, unless the argument is a singleton or at least 8 wide (4 for `tan`),
`floors_exact` divides each bound alone to confirm them, and where it cannot,
`quadrants` reads the quadrants of the bounds from the signs of `sin_rd` and
`cos_ru` of each. That is four calls, of MPFR in the builds of the first table
below and in `036d2f8`, and of the kernel in `893b06c`, where the result itself
makes at most two.

The `trig` benchmark times each function on the same 1024 intervals of each of
four classes, drawn with a fixed seed:

- `small`: `a` in [-100, 100) and `b - a` up to 0.5;
- `narrow`: the same with `b - a` up to 10^-9;
- `near`: one bound within 3 ulps of the float `k * FRAC_PI_2`, for an integer
  0 < |k| ≤ 2^20, and `b - a` up to about 10^-6;
- `big`: |a| in [2^30, 2^50) and `b - a` up to 1.

How many of the 1024 intervals of each class reach `floors_exact` in
`216e5f5` and `b2390de`, and how many of those go on to `quadrants`:

| Class | `floors_exact`: sin / cos / tan | `quadrants`: sin / cos / tan |
|---|--:|--:|
| small | 153 / 74 / 153 | 0 / 0 / 0 |
| narrow | 0 / 0 / 0 | 0 / 0 / 0 |
| near | 626 / 336 / 626 | 245 / 119 / 245 |
| big | 338 / 165 / 338 | 24 / 13 / 24 |

The columns of the first table are `216e5f5^` (`ced0d5f`), `216e5f5` and
`b2390de`, the main branch when it was measured. All three computed the bounds
with MPFR 4.2.2, built by `gmp-mpfr-sys` 1.7.1 (see "Setup"), so these are not
times of the current code, which the second table measures. Times are in µs per
interval operation, medians over nine rounds; see "Variance" above.

| Benchmark | ced0d5f (µs) | 216e5f5 (µs) | ratio | b2390de (µs) | ratio | spread |
|---|--:|--:|--:|--:|--:|--:|
| sin/small | 2.41 | 2.40 | 1.00× | 2.40 | 1.00× | 2% |
| cos/small | 1.86 | 1.84 | 0.99× | 1.85 | 0.99× | 2% |
| tan/small | 2.47 | 2.45 | 0.99× | 2.45 | 0.99× | 3% |
| sin/narrow | 2.44 | 2.43 | 1.00× | 2.44 | 1.00× | 3% |
| cos/narrow | 1.84 | 1.82 | 0.99× | 1.83 | 0.99× | 2% |
| tan/narrow | 2.69 | 2.67 | 0.99× | 2.67 | 0.99× | 3% |
| sin/near | 6.54 | 9.16 | 1.40× | 9.18 | 1.40× | 2% |
| cos/near | 3.62 | 4.59 | 1.27× | 4.61 | 1.27× | 3% |
| tan/near | 5.85 | 8.94 | 1.53× | 9.02 | 1.54× | 3% |
| sin/big | 2.58 | 2.70 | 1.05× | 2.70 | 1.05× | 3% |
| cos/big | 1.99 | 2.05 | 1.03× | 2.05 | 1.03× | 2% |
| tan/big | 2.50 | 2.64 | 1.06× | 2.65 | 1.06× | 3% |

Of the commits between `216e5f5` and `b2390de`, two change the code that the
benchmark runs: `eb67023` removed an interval multiplication that `tan` made on
every interval of the benchmark, and `91b59e7` changed how the MPFR calls are
written. `b2390de` takes 1.00–1.01 times as long as `216e5f5` on every row, which is
within how far these builds move on `narrow` (see "Variance").

`3f625c0` moved the bounds of `sin`, `cos` and `tan`, and of the other
elementary functions, from MPFR to inari's own kernel. The second table
compares two copies of the source of `893b06c`, the main branch when it was
measured, the same byte for byte but at paths of different lengths, copy A and
copy B, with `036d2f8`, the commit before `3f625c0`. In all three,
`sin`, `cos`, `tan`, `floors_exact` and `quadrants` are those of `b2390de`, and
the benchmark is the one that the first table ran, both but for comments; the
functions that they call for the bounds are MPFR's in `036d2f8` and the
kernel's in `893b06c`. Times are in µs per interval operation for `036d2f8` and
in ns for the copies, medians over nine rounds; see "Variance" above.

| Benchmark | 036d2f8 (µs) | copy A (ns) | ratio | copy B (ns) | ratio | B/A | spread |
|---|--:|--:|--:|--:|--:|--:|--:|
| sin/small | 2.49 | 72.70 | 0.029× | 72.46 | 0.029× | 1.00× | 4% |
| cos/small | 1.91 | 68.04 | 0.036× | 66.81 | 0.035× | 0.98× | 2% |
| tan/small | 2.55 | 84.14 | 0.033× | 85.20 | 0.033× | 1.01× | 5% |
| sin/narrow | 2.53 | 71.44 | 0.028× | 71.48 | 0.028× | 1.00× | 5% |
| cos/narrow | 1.89 | 67.49 | 0.036× | 66.82 | 0.035× | 0.99× | 2% |
| tan/narrow | 2.76 | 89.47 | 0.032× | 94.22 | 0.034× | 1.05× | 5% |
| sin/near | 9.42 | 140.97 | 0.015× | 141.27 | 0.015× | 1.00× | 4% |
| cos/near | 4.76 | 111.10 | 0.023× | 112.20 | 0.024× | 1.01× | 3% |
| tan/near | 9.28 | 134.24 | 0.014× | 133.30 | 0.014× | 0.99× | 4% |
| sin/big | 2.80 | 89.89 | 0.032× | 89.28 | 0.032× | 0.99× | 6% |
| cos/big | 2.11 | 85.85 | 0.041× | 84.77 | 0.040× | 0.99× | 2% |
| tan/big | 2.74 | 92.99 | 0.034× | 92.25 | 0.034× | 0.99× | 9% |

With the kernel, the three take 0.014–0.041 times as long as with MPFR, 67–141
ns per interval against 1.89–9.42 µs, while copy B takes 0.965–1.067 times as
long as copy A in single rounds (see "Variance"). `near` stays the slowest
class: it takes 1.6–1.9 times as long as `small` with the kernel, and 2.5–3.8
times with MPFR.

### x86-64 without AVX

The `sse42` backend applies the method of `wasm32` to `__m128d`: it computes the
round-toward-+∞ fast paths explicitly and never touches MXCSR. It is compared
with `avx_fma`, then the default where AVX and FMA are available, and with
`generic` at the same feature level, which is the alternative on a processor
without them.
Medians over twelve rounds, except in the `generic, Nehalem` cells of the `mul`
and `mul_ru` rows, which were measured again later over seven; see "Variance"
above.

| Benchmark | avx_fma (ns) | sse42 (ns) | ratio | generic, Nehalem (ns) | ratio | spread |
|---|--:|--:|--:|--:|--:|--:|
| add/PP | 9.24 | 5.01 | 0.54× | 12.10 | 1.31× | 6% |
| add/PM | 9.25 | 5.00 | 0.54× | 10.70 | 1.16× | 10% |
| add/MM | 9.26 | 5.00 | 0.54× | 12.25 | 1.32× | 5% |
| sub/PP | 9.25 | 5.14 | 0.56× | 8.85 | 0.96× | 41% |
| sub/PM | 9.26 | 5.14 | 0.56× | 10.17 | 1.10× | 13% |
| sub/MM | 9.26 | 5.14 | 0.55× | 11.84 | 1.28× | 4% |
| mul/PP | 10.40 | 7.71 | 0.74× | 14.52 | 1.38× | 4% |
| mul/PN | 10.41 | 7.75 | 0.74× | 14.52 | 1.38× | 4% |
| mul/PM | 10.40 | 7.77 | 0.75× | 14.53 | 1.38× | 5% |
| mul/NP | 10.42 | 7.79 | 0.75× | 14.46 | 1.38× | 3% |
| mul/NN | 10.41 | 7.83 | 0.75× | 14.62 | 1.39× | 3% |
| mul/NM | 10.41 | 7.79 | 0.75× | 14.40 | 1.37× | 3% |
| mul/MP | 10.40 | 7.80 | 0.75× | 14.54 | 1.38× | 4% |
| mul/MN | 10.42 | 7.80 | 0.75× | 14.46 | 1.38× | 3% |
| mul/MM | 18.91 | 13.59 | 0.72× | 31.91 | 1.67× | 3% |
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
| mul_ru/throughput | 9.26 | 6.76 | 0.73× | 11.03 | 1.18× | 11% |
| mul_ru/latency | 8.76 | 10.66 | 1.22× | 16.10 | 1.82× | 1% |
| div_ru/throughput | 9.27 | 9.21 | 0.99× | 31.61 | 3.41× | 1% |
| div_ru/latency | 8.76 | 14.66 | 1.67× | 33.15 | 3.78× | 0% |
| mul_add_ru/throughput | 9.01 | 15.06 | 1.67× | 36.10 | 4.01× | 1% |
| mul_add_ru/latency | 8.53 | 15.82 | 1.86× | 22.90 | 2.68× | 1% |
| sqrt1_ru/throughput | 2.32 | 5.82 | 2.51× | 5.82 | 2.51× | 0% |
| sqrt1_ru/latency | 7.33 | 7.51 | 1.02× | 7.51 | 1.02× | 0% |

`sse42` takes `sqrt1_rd`, `sqrt1_ru` and `sub1_ru` from `generic`, which is why
its scalar square root matches the `generic, Nehalem` column exactly.

The `generic, Nehalem` cells of the `mul` and `mul_ru` rows were measured again
on 2026-11-08, after `d2a2f0c`, as in the section on x86-64 above: their ratios
are against `avx_fma` built from `cc5e384` and timed in the same rounds, and
their spread is the larger of the two measurements'. In those rounds,
`generic, Nehalem` ran `mul_ru/throughput` at 10.2–10.3 ns in three and at
11.0–11.4 ns in the other four.

### WebAssembly

| Benchmark | scalar (ns) | simd128 (ns) | ratio | wasm32 (ns) | ratio | spread |
|---|--:|--:|--:|--:|--:|--:|
| add/PP | 15.48 | 15.33 | 0.99× | 9.02 | 0.58× | 0% |
| add/PM | 14.60 | 14.51 | 0.99× | 9.01 | 0.62× | 0% |
| add/MM | 15.53 | 15.19 | 0.98× | 9.01 | 0.58× | 0% |
| sub/PP | 10.96 | 11.15 | 1.02× | 8.84 | 0.81× | 1% |
| sub/PM | 13.91 | 13.95 | 1.00× | 8.83 | 0.63× | 0% |
| sub/MM | 15.26 | 15.38 | 1.01× | 8.83 | 0.58× | 1% |
| mul/PP | 20.27 | 21.10 | 1.04× | 14.96 | 0.74× | 1% |
| mul/PN | 20.47 | 21.23 | 1.04× | 15.00 | 0.73× | 1% |
| mul/PM | 20.52 | 21.11 | 1.03× | 15.02 | 0.73× | 1% |
| mul/NP | 20.32 | 20.94 | 1.03× | 15.06 | 0.74× | 2% |
| mul/NN | 20.60 | 21.06 | 1.02× | 15.00 | 0.73× | 2% |
| mul/NM | 20.30 | 20.89 | 1.03× | 15.12 | 0.74× | 2% |
| mul/MP | 20.25 | 20.94 | 1.03× | 14.89 | 0.74× | 2% |
| mul/MN | 20.58 | 21.06 | 1.02× | 15.13 | 0.73× | 1% |
| mul/MM | 39.20 | 40.23 | 1.03× | 25.44 | 0.65× | 1% |
| div/PP | 30.92 | 31.44 | 1.02× | 16.35 | 0.53× | 0% |
| div/PN | 31.53 | 31.53 | 1.00× | 16.53 | 0.52× | 0% |
| div/MP | 30.35 | 30.49 | 1.00× | 16.31 | 0.54× | 0% |
| div/NN | 30.99 | 31.63 | 1.02× | 16.18 | 0.52× | 1% |
| div/PM (= ℝ) | 9.89 | 9.21 | 0.93× | 7.88 | 0.80× | 0% |
| sqrt/P | 15.84 | 15.19 | 0.96× | 10.20 | 0.64× | 1% |
| sqrt/M | 13.55 | 14.92 | 1.10× | 13.58 | 1.00× | 0% |
| Horner, degree 8, P | 231.57 | 231.38 | 1.00× | 162.94 | 0.70× | 2% |
| Horner, degree 8, M | 262.78 | 262.85 | 1.00× | 243.21 | 0.93× | 1% |
| 3×3 determinant | 240.61 | 241.40 | 1.00× | 137.68 | 0.57× | 2% |

| Benchmark | scalar (ns) | simd128 (ns) | ratio | wasm32 (ns) | ratio | spread |
|---|--:|--:|--:|--:|--:|--:|
| add_ru/throughput | 10.56 | 11.18 | 1.06× | 7.88 | 0.75× | 0% |
| add_ru/latency | 10.30 | 15.05 | 1.46× | 9.08 | 0.88× | 0% |
| mul_ru/throughput | 13.89 | 14.93 | 1.07× | 11.35 | 0.82× | 18% |
| mul_ru/latency | 14.22 | 17.02 | 1.20× | 11.60 | 0.82× | 6% |
| div_ru/throughput | 24.89 | 26.75 | 1.07× | 13.57 | 0.55× | 0% |
| div_ru/latency | 20.66 | 29.50 | 1.43× | 16.02 | 0.78× | 0% |
| mul_add_ru/throughput | 28.85 | 29.64 | 1.03× | 18.59 | 0.64× | 0% |
| mul_add_ru/latency | 22.56 | 24.42 | 1.08× | 21.00 | 0.93× | 0% |
| sqrt1_ru/throughput | 4.55 | 4.54 | 1.00× | 4.54 | 1.00× | 2% |
| sqrt1_ru/latency | 7.22 | 7.21 | 1.00× | 7.22 | 1.00× | 0% |

The `mul`, `mul_ru`, Horner and determinant rows were measured again, whole, on
2026-11-08, after `d2a2f0c` changed how `generic` rounds up without an FMA:
medians over seven rounds (see "Variance"). The other rows are from the first
sitting.

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
  usefully auto-vectorize the scalar code, and it makes the latency of `add_ru`
  and `div_ru` 1.43–1.46× worse, and that of `mul_ru` 1.20×. Writing the fast
  paths against `v128` explicitly, as the `wasm32` backend does, is what pays:
  most interval operations other than multiplication take 0.52–0.64× the time,
  multiplication 0.65–0.74×, the 3×3 determinant 0.57×, and Horner of degree 8
  0.70× on `P` and 0.93× on `M`.
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
  `mul_add_ru/throughput` from 1.67× to 0.78×, `sqrt/P` from 1.80× to 1.03× and
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
- Rounding products below 2^-968 on the fast path after scaling pays in the
  other backends too: on `mul_tiny`, `sse42` now takes 0.43–0.44 times as long
  as before, `wasm32` 0.42–0.44, `generic, FMA` 0.50–0.53, and the two `generic`
  configurations without an FMA, `generic, Nehalem` and `scalar`, 0.72–0.78.
- Before the change, `sse42` and `wasm32`, which handed tiny products to
  `generic`, took about as long on them as `generic, Nehalem` and `scalar`:
  0.95–1.04 and 1.04–1.08 times. They now take 0.57–0.58 and 0.60–0.63 times as
  long, against 0.45–0.48 and 0.47–0.49 on `mul`.
- Tiny products still cost these backends far more, relative to ordinary ones,
  than they cost `fma`: after the change, `mul_tiny` took 3.8–4.2 times as long
  as `mul` with `sse42`, 2.6–2.9 times with `wasm32`, 3.2–3.3 times with
  `generic, Nehalem` and 2.0–2.2 times with `generic, FMA` and `scalar`, against
  1.32–1.35 times (1.60 on `mul/MM`) with `fma`. In `sse42`, most of the
  difference was a TwoProduct that the tiny lanes did not need: `mul_ru_tiny`
  also rounded `x * y` itself in every lane, by Dekker's TwoProduct, some of
  whose partial products can underflow when the product is near 2^-1010, and
  on Zen 2 a multiplication whose result is subnormal and inexact costs more.
  In a probe on a loaded host, `mulpd` with such a result took 1.7 times as
  long in throughput as with a normal one, and Dekker's TwoProduct with one
  factor between 2^-1010 and 2^-1009 3.7 times as long as with ordinary ones,
  while multiplications with subnormal inputs and a normal or exact result, and
  additions with subnormal inputs or results, cost nothing extra. With MXCSR's
  DAZ and FTZ set, which treat subnormal inputs and results as zero, `sse42`
  took 0.40–0.44 times as long on `mul_tiny` in that probe, and as long as
  before on `mul`. That `wasm32` paid in the same way is inferred only from
  what removing that TwoProduct gained (below). Without an FMA, `generic`'s
  `mul1_ru_fast` computes Dekker's TwoProduct of a lane's factors before it
  checks whether it may use it, and in the same probe, DAZ and FTZ made
  `generic, Nehalem` 1.5–1.6 times as fast on `mul_tiny`, which removed about
  half of its extra cost. Whether that TwoProduct is what pays there, the rest
  of that cost, and whether `scalar` pays in the same way have not been traced.
  Nor has the extra cost of `generic, FMA`, but DAZ and FTZ do not remove it:
  in a probe on 2026-11-08, on an idle host, they made `generic, FMA` take
  1.06–1.12 times as long on `mul_tiny`, and as long on `mul`, while `fma` took
  as long with them as without on both.
- Ordinary products do not pay measurably for the change in `sse42`: on `mul`
  it takes 0.99–1.00 times as long as before, within the 0.99–1.02 of the
  `generic` configurations, which run the same code in both builds. `wasm32`
  takes 1.02–1.03 times as long, and more than 1.01 times in every round. That
  is at the edge of what the same code shows, as `scalar` takes more than 1.01
  times as long on `mul/MM` in every round too, so these builds cannot tell
  whether `wasm32` pays 2–3% on ordinary products or nothing. Measured again on
  2026-11-08, since `0a7c306`, through `76d2bab` and `77a4138` in `wasm32` and
  `6fa4f83` and `d2a2f0c` in the `generic::mul_ru` that it falls back to,
  `wasm32` takes 1.00–1.01 times as long on `mul`, inside the range of two
  builds of the same source, so the 2–3% did not recur, and those builds cannot
  tell 1% from nothing either; see the section on two builds of the same source.
  `76d2bab` reports that the fast path of `wasm32`'s `mul_ru` grew from 155
  to 159 WebAssembly instructions, by four `local.tee`s.
- Rounding only the product that each lane needs removes most of the extra cost
  of tiny products in `sse42` and `wasm32`: on `mul_tiny`, `sse42` takes
  0.38–0.39 times as long as before and `wasm32` 0.52–0.54. `mul_tiny` now takes
  1.50–1.61 times as long as `mul` with `sse42` and 1.41–1.54 times with
  `wasm32`, against 1.30–1.59 times with `fma` in the same rounds, where it took
  3.83–4.24 and 2.61–2.92 times as long before. `fma` gains least, 0.95–0.97,
  about as much as on `mul/PP` and `mul/MM`, which do not reach `mul_ru_tiny`;
  in the probe above, DAZ and FTZ changed nothing in `fma`.
- Since `77a4138`, `fma` takes 0.61 times as long as 2.0.0 on `mul` (0.50 on
  `mul/MM`) and 0.78–0.79 times on `mul_tiny`, measured in the same rounds,
  where the first section on tiny products had 0.81–0.82 on the same three
  classes. `mul_tiny` takes 1.30 times as long as `mul` with `fma` there, and
  1.56 times on `MM`.
- Rounding up without a branch in `generic::mul1_ru_fast`, which `d2a2f0c` does
  only without an FMA, makes `generic, Nehalem` take 0.89 times as long as
  before on `mul/PP` and `mul/PM`, and `scalar` 0.64–0.70 times on `mul`. But
  `generic, Nehalem` takes 1.05 times as long on `mul/MM`, and at least 1.03
  times in every round, where `generic, FMA`, whose `mul_ru` compiles to the
  same instructions in both builds but for addresses, takes 1.02 times as long.
  On `mul_tiny`, `generic, Nehalem` takes 0.93–0.97 times as long as before, and
  `scalar` 0.75–0.79. `d2a2f0c` does not move Dekker's TwoProduct, which
  `mul1_ru_fast` computes before it checks whether the lane may use it (above),
  and tiny products still cost `generic, Nehalem` far more than ordinary ones:
  `mul_tiny` takes 3.0–3.4 times as long as `mul` after the change, against
  3.2–3.3 times before. In a probe outside criterion, on a host at a load
  average of 1.2–1.6, DAZ and FTZ made `generic, Nehalem` about 1.7 times as
  fast on `mul_tiny` after the change. The columns of `generic` without an FMA
  in the sections on x86-64, x86-64 without AVX and WebAssembly, `generic, no
  FMA`, `generic, Nehalem`, `scalar` and `simd128`, were measured before
  `d2a2f0c`, except in the `mul` and `mul_ru` rows, and on WebAssembly in those
  of the composite benchmarks, which were measured again on 2026-11-08 (see the
  notes under those tables).
- In the builds that called MPFR, making `sin`, `cos` and `tan` of intervals
  tightest costs nothing measurable on `small` and `narrow`, whose bounds are
  within about 100 of 0 and not chosen near a multiple of π/2: all three take
  0.99–1.00 times as long as before there, the range within which builds of
  shared code move here. `floors_exact` adds two interval divisions, which take
  about 7 ns each in the `fma` section, to calls that take 1.8 µs or more there,
  and `small`, which reaches it on 7–15% of its intervals but never goes on to
  `quadrants`, does not show it. What it costs with the kernel, where those
  calls take 67–141 ns, has not been measured.
- Arguments with a bound near a multiple of π/2 pay for the new path in those
  builds: on `near`, `sin` takes 1.40 times as long as before, `tan` 1.53 times
  and `cos` 1.27 times. `quadrants` runs on 24% of those intervals for `sin` and
  `tan`, and on 12% for `cos`. Where `tan` used to return [-∞, +∞] there, which
  needs no MPFR call, its tightest result may need two.
- On `big`, where 1.3–2.3% of the intervals take `quadrants`, the three take
  1.03–1.06 times as long in those builds, beyond the range of `narrow`. Whether
  that share accounts for all of it has not been checked.
- With the kernel, `sin`, `cos` and `tan` of intervals take 0.014–0.041 times
  as long as with MPFR in `036d2f8` on all four classes, 67–141 ns per interval
  against 1.89–9.42 µs. `near` is still the slowest class, but by less: it takes
  1.6–1.9 times as long as `small` with the kernel, against 2.5–3.8 times with
  MPFR.

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
fast path too, after which it took 0.81–0.83 times as long on them (0.81–0.82
on `PP`, `PM` and `MM`), and 0.78–0.79 times on those three once it rounded
only the product that each lane needs. `fma` is therefore the default, and
`avx_fma` has been removed.

`generic` is not a replacement for either. It has no fixed rounding-mode cost
but needs many more instructions: against `avx_fma` it was within about 1.3×
either way on most rows and at worst 2.7× slower, but against `fma` it is slower
on every row of both tables except `sqrt1_ru`, which the two share. It takes 1.2×
as long on the two interval rows that do almost no arithmetic, `div/PM` and
`sqrt/M`, 1.2–1.6× as long on the latency of the three primitives where `fma`'s
correction lengthens the chain, and 1.5–4× as long on the rest. `force-generic`
remains the portable fallback rather than a faster one.

`sse42` is the same method as `fma` without an FMA, and is 1.4–2.5 times as fast
as `generic` at the same feature level on every row of the two tables of x86-64
without AVX but five: 3.4 times on the 3×3 determinant and `div_ru/throughput`,
and 1.00–1.07 times on `sqrt/M` and both rows of `sqrt1_ru`, which run the
scalar square root that it takes from `generic`.
Where it loses to `fma` it loses to the missing FMA — `sqrt`, `mul_add` and the
remainder in division — not to the method.

All of this is one microarchitecture. `fma`'s advantage is bounded by what
`vldmxcsr` costs — it trades a fixed per-operation overhead for more
instructions that pipeline — so a processor on which switching the rounding
mode is cheap could reverse the comparison entirely. That has not been measured.
The comparison with `generic`, which switches nothing either, does not depend on
this.

On WebAssembly, build with `-Ctarget-feature=+simd128` where the runtime
supports it: the `wasm32` backend is 1.6–1.9 times as fast as the portable one
on most interval operations other than multiplication, and 1.3–1.5 times as
fast on multiplication.

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

The 2.0.0 columns of the sections on tiny products come from
`benches/intervals.rs` copied into a package of its own that depends on
`inari = "=2.0.0"` with `default-features = false`, with the same
`[profile.bench]`.

The trigonometric functions compute their bounds with inari's own kernel, so
their benchmark, `benches/trig.rs`, needs no feature, and `cargo bench` runs it
with the others. To run it alone:

```bash
cd bench
RUSTFLAGS=-Ctarget-cpu=haswell cargo bench --bench trig
```

The first table of the trigonometric section above was measured before that,
and the `036d2f8` column of its second with a build of a commit from before
that, both with the package's `gmp` feature, which built GMP and MPFR through
`gmp-mpfr-sys`. The package no longer has that feature.

For WebAssembly, with wasmtime on the path:

```bash
cd bench
export CARGO_TARGET_WASM32_WASIP1_RUNNER=wasmtime
RUSTFLAGS=-Ctarget-feature=+simd128 cargo bench --target wasm32-wasip1
```
