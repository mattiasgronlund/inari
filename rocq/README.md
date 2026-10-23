# Proofs of the portable backend

Machine-checked proofs, in [Rocq](https://rocq-prover.org) with the [Flocq](https://flocq.gitlabpages.inria.fr) library, that parts of [`src/simd/generic.rs`](../src/simd/generic.rs) round correctly.

## What is proved

`add_ru_correct` in [`AddRu.v`](theories/AddRu.v):

```coq
Theorem add_ru_correct : forall x y,
  Generic.add_ru x y =
    Some (Bplus mode_UP (fst x) (fst y), Bplus mode_UP (snd x) (snd y)).
```

For all inputs, both lanes of `add_ru` are IEEE 754 binary64 addition rounded toward +∞. This includes the sign of a zero result, overflow, the infinities and NaN. The specification `Bplus mode_UP` is Flocq's. With the modelling choices below, `Some` also means that `add_ru` does not panic.

It follows from the theorems for the two paths that `lanewise2` chooses between:

```coq
Theorem add1_ru_fast_correct : forall x y,
  snd (Generic.add1_ru_fast x y) = true ->
  fst (Generic.add1_ru_fast x y) = Bplus mode_UP x y.

Theorem add1_ru_slow_correct : forall x y,
  Generic.add1_ru_slow x y = Some (Bplus mode_UP x y).
```

`sub_ru_correct` and `sub1_ru_correct` in [`SubRu.v`](theories/SubRu.v) do the same for subtraction rounded toward +∞, Flocq's `Bminus mode_UP`:

```coq
Theorem sub_ru_correct : forall x y,
  Generic.sub_ru x y =
    Some (Bminus mode_UP (fst x) (fst y), Bminus mode_UP (snd x) (snd y)).

Theorem sub1_ru_correct : forall x y,
  Generic.sub1_ru x y = Some (Bminus mode_UP x y).
```

`sub_ru` and `sub1_ru` add `-y` with the functions above. Flocq defines `Bminus` by its own case analysis, and `Bminus_Bplus_Bopp` shows that it agrees with `Bplus` of `Bopp y`.

On the way, the other files prove:

- [`Encoding.v`](theories/Encoding.v): `is_finite_eq`, i.e. `is_finite` agrees with Flocq's, and `abs_B2R_lt_exponent`, i.e. `|x| < 2^(exponent(x) + 1)`. `step_up_Bsucc` shows that `step_up` is Flocq's `Bsucc` (IEEE 754 `nextUp`) on finite floats.
- [`TwoSum.v`](theories/TwoSum.v): `two_sum_err_correct`. If `|x|, |y| < 2^1023` and `x + y` is finite, `two_sum_err` computes the exact error `(x + y) - s` without overflowing. It uses Flocq's proof of TwoSum (`Pff2Flocq.TwoSum_correct`), which allows underflow.
- [`Decompose.v`](theories/Decompose.v): `decompose_correct`, i.e. `decompose` gives the sign, the integral significand and the exponent of a finite nonzero float. `pow2_correct`, i.e. `pow2(e)` is `2^e` for `e ∈ [-1074, 1023]`. `of_u64_exact`, i.e. `k as f64` is exact for `k <= 2^53`. `add_special`: where `add1_ru_slow` returns `x + y`, the rounding mode does not matter.
- [`RoundUpExact.v`](theories/RoundUpExact.v): `round_up_exact_correct`. `round_up_exact(neg, m, e, sticky)` rounds `(-1)^neg * (m + δ) * 2^e` toward +∞, under the precondition `round_up_exact_pre` in [`Spec.v`](theories/Spec.v), which bounds `m` and `e` and requires `m >= 2^52` if `sticky`.
- [`SumRoundUp.v`](theories/SumRoundUp.v): `sum_round_up_reduce`. For significands in `(0, 2^106)` and exponents in `[-2^19, 2^19]`, `sum_round_up` returns +0 if the sum is zero, and otherwise calls `round_up_exact` with arguments that meet its precondition.

## What is assumed

[`Model.v`](theories/Model.v) transcribes the Rust functions line by line. It is the only file that has to be checked against `generic.rs` by reading, and it has to be updated whenever those functions change. Its modelling choices:

- `f64` is Flocq's binary64, and Rust's `+` and `-` are Flocq's `Bplus` and `Bminus` rounded to nearest, ties to even. `generic.rs` relies on this default rounding mode.
- NaN payloads and signs are not modelled: all NaNs are the same value, so `Bopp` keeps a NaN as it is where Rust's unary `-` flips its sign bit. The functions proved here only read the exponent field of a NaN, which is all ones for every NaN.
- Bit patterns are integers rather than `u64`, so `b + 1` and `b - 1` in `step_up` cannot wrap around. `step_up_no_wrap` in `Encoding.v` shows that for finite floats they stay in the range of `u64`, so they don't wrap around (or panic) in Rust either. The same holds for ±∞ and NaN, but is not proved: `b + 1` is only computed if `x > 0`, so the sign bit of `b` is clear, and `b - 1` only if `x < 0`, so it is set.
- The other integer types, `u128`, `u64`, `u32` and `i32`, are integers too. In the slow path, every operation that panics in a debug build returns `None`: one whose result does not fit its type, a shift by a negative amount or by at least the width of the type, and the `debug_assert!` in `sum_round_up`. A release build would wrap around instead, so a theorem that a function returns `Some` covers both kinds of build. Arithmetic on the fields of a bit pattern, in `exponent` and `decompose`, cannot overflow and is not checked.
- Casts that could change a value reduce it modulo the size of the target type, as Rust does: `(e + 1023) as u64`, `kept as u64` and `(ex - ey) as u32`. Casts that keep the value are left out: those of the 11-bit exponent field in `exponent` and `decompose`, and, each with a comment, `m.leading_zeros() as i32`, `kept.leading_zeros() as i32`, `sh as i32` and `mx as u128`.
- `kept as f64` is Flocq's `binary_normalize` rounded to nearest, ties to even, like Rust's conversion from `u64`. `*` is Flocq's `Bmult` rounded to nearest, ties to even, and unary `-` is `Bopp`.
- `F64X2` is a pair, and `lanewise2` takes the two paths as functions.

The theorems depend on four axioms. Three come from Stdlib's real numbers: `sig_forall_dec`, `sig_not_dec` and `functional_extensionality_dep`. The fourth is excluded middle (`classic`), which Flocq uses. `make` fails if [`Assumptions.v`](Assumptions.v) finds any other axiom, e.g. a proof left `Admitted`.

## What is not proved yet

- The SIMD backends that vectorize the same algorithm, such as `src/simd/x86_64/lanewise.rs` and `src/simd/wasm32.rs`.
- Every other operation. `round_up_exact_correct` already covers the last step of `mul1_ru_slow` and `div1_ru_slow`, given that they meet its precondition.

## Building

You need Rocq 9.1, its Stdlib and Flocq 4.2.2. With [opam](https://opam.ocaml.org):

```bash
opam repo add rocq-released https://coq.inria.fr/opam/released
opam install rocq-core.9.1.1 rocq-stdlib.9.0.0 coq-flocq.4.2.2
make -C rocq
```

You can also use Docker, as CI does ([`ci-rocq.yml`](../.github/workflows/ci-rocq.yml)). The container's user (uid 1000) must be able to write to `rocq/`.

```bash
docker run --rm -v "$PWD/rocq:/w" -w /w rocq/rocq-prover:9.1 \
  bash -c 'opam install -y coq-flocq.4.2.2 && make'
```

Warnings are errors. `make clean` removes the build outputs.
