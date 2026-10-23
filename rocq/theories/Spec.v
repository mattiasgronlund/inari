(** * What the slow path of [add_ru] computes

    The statements that [Decompose.v], [RoundUpExact.v] and [SumRoundUp.v]
    prove, and [AddRu.v] puts together. None of them is part of what has to
    be trusted: the theorems in [AddRu.v] are stated in terms of Flocq's
    [Bplus] alone. *)

From Stdlib Require Import ZArith Reals Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding.

(** ** Integer operations that do not overflow *)

Open Scope Z_scope.

Lemma checked_u_ok : forall w z, 0 <= z < 2^w -> checked_u w z = Some z.
Proof.
intros w z Hz. unfold checked_u.
destruct (Z.leb_spec 0 z), (Z.ltb_spec z (2^w)); [reflexivity | lia ..].
Qed.

Lemma checked_i_ok :
  forall w z, - 2^(w - 1) <= z < 2^(w - 1) -> checked_i w z = Some z.
Proof.
intros w z Hz. unfold checked_i.
destruct (Z.leb_spec (- 2^(w - 1)) z), (Z.ltb_spec z (2^(w - 1)));
  [reflexivity | lia ..].
Qed.

Lemma shl_ok :
  forall w a s, 0 <= s < w -> 0 <= a -> a * 2^s < 2^w ->
  shl w a s = Some (a * 2^s).
Proof.
intros w a s Hs Ha Hw. unfold shl.
destruct (Z.leb_spec 0 s), (Z.ltb_spec s w); try lia.
rewrite Z.shiftl_mul_pow2, Z.mod_small by (try split; nia).
reflexivity.
Qed.

Lemma shr_ok : forall w a s, 0 <= s < w -> shr w a s = Some (a / 2^s).
Proof.
intros w a s Hs. unfold shr.
destruct (Z.leb_spec 0 s), (Z.ltb_spec s w); try lia.
now rewrite Z.shiftr_div_pow2.
Qed.

Lemma leading_zeros_pos :
  forall w a, 0 < a -> leading_zeros w a = w - 1 - Z.log2 a.
Proof.
intros w a Ha. unfold leading_zeros.
now destruct (Z.eqb_spec a 0); [lia|].
Qed.

(** ** The specification of [round_up_exact] *)

Open Scope R_scope.

(** Rounding toward +inf in binary64 without overflow. *)
Notation RU := (round radix2 fexp64 Zceil).

(** [r] is [v] rounded toward +inf by IEEE 754: [RU v] with the sign of
    [v] if [|RU v| < 2^1024], and otherwise what Flocq's [binary_overflow]
    gives, i.e. +inf if [v > 0] and -MAX if [v < 0]. [v] is nonzero. *)
Definition rounds_up_to (v : R) (r : f64) : Prop :=
  if Rlt_bool (Rabs (RU v)) (bpow radix2 1024) then
    B2R r = RU v /\ is_finite r = true /\ Bsign r = Rlt_bool v 0
  else
    B2SF r = binary_overflow 53 1024 mode_UP (Rlt_bool v 0).

(** The arguments of [round_up_exact neg m e sticky] describe [v]: [v]
    has the sign [neg], [|v| = m * 2^e] if not [sticky], and
    [m * 2^e < |v| < (m + 1) * 2^e] if [sticky]. The bounds on [m] and [e]
    keep the arithmetic within its types, and [m >= 2^52] if [sticky] puts
    the part of [|v|] beyond [m * 2^e] below the last bit of the result. *)
Definition round_up_exact_pre (neg : bool) (m e : Z) (sticky : bool) (v : R) :
    Prop :=
  (0 < m < 2^128)%Z /\ (-2^20 <= e <= 2^20)%Z /\
  (sticky = true -> 2^52 <= m)%Z /\
  Rlt_bool v 0 = neg /\
  if sticky then
    F2R (Float radix2 m e) < Rabs v < F2R (Float radix2 (m + 1) e)
  else
    Rabs v = F2R (Float radix2 m e).
