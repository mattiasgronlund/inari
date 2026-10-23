(** * A model of the parts of [src/simd/generic.rs] that are proved here

    Each definition in [Generic] transcribes the Rust function of the same
    name, line by line, so that the two can be compared side by side. This
    file is the only one that has to be checked against the Rust code; the
    other files prove properties of the definitions here.

    Rust's [f64] is Flocq's IEEE 754 binary64 type, and its [+] and [-] are
    Flocq's [Bplus] and [Bminus] rounded to nearest, ties to even, which is
    the default rounding mode that [generic.rs] relies on.

    NaN payloads are not modelled: all NaNs are the same value. [generic.rs]
    never looks at a payload, only at the exponent field, which is all ones
    for every NaN, so [to_bits] can give every NaN the bits of one of them. *)

From Stdlib Require Import ZArith.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Flocq Require IEEE754.Binary IEEE754.Bits.

Open Scope Z_scope.
Open Scope bool_scope.

#[global] Instance prec_gt_0_53 : Prec_gt_0 53 := eq_refl.
#[global] Instance prec_lt_emax_53_1024 : Prec_lt_emax 53 1024 := eq_refl.

(** [f64], with 53 bits of precision (including the implicit bit) and
    the infinities at exponent 1024. *)
Definition f64 := binary_float 53 1024.

(** [x + y] and [x - y]. *)
Definition add (x y : f64) : f64 := Bplus mode_NE x y.
Definition sub (x y : f64) : f64 := Bminus mode_NE x y.

(** [x > y] and [x < y], which are false if either is NaN. *)
Definition gt (x y : f64) : bool := Bltb y x.
Definition lt (x y : f64) : bool := Bltb x y.

(** [0.0]. *)
Definition zero : f64 := B754_zero false.

(** [x.to_bits()] and [f64::from_bits(b)]. The bit patterns are integers
    instead of [u64], so an addition to one cannot wrap around;
    [Encoding.step_up_no_wrap] shows that those in [step_up] stay in range
    anyway. *)
Definition to_bits (x : f64) : Z :=
  Bits.bits_of_b64 (Binary.BSN2B 53 1024 Bits.default_nan_pl64 x).
Definition from_bits (b : Z) : f64 := Binary.B2BSN 53 1024 (Bits.b64_of_bits b).

Module Generic.

(** [fn exponent(x: f64) -> i32] *)
Definition exponent (x : f64) : Z :=
  Z.land (Z.shiftr (to_bits x) 52) 0x7ff - 1023.

(** [fn step_up(x: f64) -> f64] *)
Definition step_up (x : f64) : f64 :=
  let b := to_bits x in
  from_bits (if gt x zero then b + 1 else if lt x zero then b - 1 else 1).

(** [fn two_sum_err(x: f64, y: f64, s: f64) -> f64] *)
Definition two_sum_err (x y s : f64) : f64 :=
  let a := sub s y in
  let b := sub s a in
  add (sub x a) (sub y b).

(** [fn is_finite(x: f64) -> bool] *)
Definition is_finite (x : f64) : bool := exponent x <? 1024.

(** [fn add1_ru_fast(x: f64, y: f64) -> (f64, bool)] *)
Definition add1_ru_fast (x y : f64) : f64 * bool :=
  let s := add x y in
  let e := two_sum_err x y s in
  let finite := is_finite x && is_finite y in
  let ok :=
    negb finite
    || ((exponent x <=? 1022) && (exponent y <=? 1022) && is_finite s) in
  let r := if finite && gt e zero then step_up s else s in
  (r, ok).

End Generic.
