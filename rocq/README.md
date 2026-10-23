# Proofs of the portable backend

Machine-checked proofs, in [Rocq](https://rocq-prover.org) with the [Flocq](https://flocq.gitlabpages.inria.fr) library, that parts of [`src/simd/generic.rs`](../src/simd/generic.rs) round correctly.

## What is proved

`add1_ru_fast_correct` in [`AddRu.v`](theories/AddRu.v):

```coq
Theorem add1_ru_fast_correct : forall x y,
  snd (Generic.add1_ru_fast x y) = true ->
  fst (Generic.add1_ru_fast x y) = Bplus mode_UP x y.
```

Whenever the fast path of `add_ru` reports that its result is valid, the result is IEEE 754 binary64 addition rounded toward +∞. This includes the sign of a zero result, overflow, the infinities and NaN. The specification `Bplus mode_UP` is Flocq's.

On the way, the other files prove:

- [`Encoding.v`](theories/Encoding.v): `is_finite_eq`, i.e. `is_finite` agrees with Flocq's, and `abs_B2R_lt_exponent`, i.e. `|x| < 2^(exponent(x) + 1)`. `step_up_Bsucc` shows that `step_up` is Flocq's `Bsucc` (IEEE 754 `nextUp`) on finite floats.
- [`TwoSum.v`](theories/TwoSum.v): `two_sum_err_correct`. If `|x|, |y| < 2^1023` and `x + y` is finite, `two_sum_err` computes the exact error `(x + y) - s` without overflowing. It uses Flocq's proof of TwoSum (`Pff2Flocq.TwoSum_correct`), which allows underflow.

## What is assumed

[`Model.v`](theories/Model.v) transcribes the Rust functions line by line. It is the only file that has to be checked against `generic.rs` by reading, and it has to be updated whenever those functions change. Its modelling choices:

- `f64` is Flocq's binary64, and Rust's `+` and `-` are Flocq's `Bplus` and `Bminus` rounded to nearest, ties to even. `generic.rs` relies on this default rounding mode.
- NaN payloads are not modelled. The fast path only reads the exponent field of a NaN, which is all ones for every NaN.
- Bit patterns are integers rather than `u64`, so `b + 1` and `b - 1` in `step_up` cannot wrap around. `step_up_no_wrap` in `Encoding.v` shows that for finite floats they stay in the range of `u64`, so they don't wrap around (or panic) in Rust either.

The theorems depend on four axioms. Three come from Stdlib's real numbers: `sig_forall_dec`, `sig_not_dec` and `functional_extensionality_dep`. The fourth is excluded middle (`classic`), which Flocq uses. `make` fails if [`Assumptions.v`](Assumptions.v) finds any other axiom, e.g. a proof left `Admitted`.

## What is not proved yet

- `add1_ru_slow`, which `add_ru` calls when the fast path reports an invalid result. That happens if `|x|` or `|y|` is at least 2^1023, or if `x + y` overflows. The `lanewise2` wrapper that chooses between the two paths isn't covered either.
- The SIMD backends that vectorize the same algorithm, such as `src/simd/x86_64/lanewise.rs` and `src/simd/wasm32.rs`.
- Every other operation.

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
