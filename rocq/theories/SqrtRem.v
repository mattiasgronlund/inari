(** * The remainder of a rounded square root is a float

    The fast path of [sqrt_rd_ru], [sqrt1_fast], computes [s = RN(sqrt x)]
    and the remainder [r = x - s * s] with one FMA or with Dekker's
    TwoProduct, and steps [s] by the sign of [r]. That needs two facts,
    proved here for real numbers.

    First, [r] is a float, so that it is computed exactly
    ([sqrt_rem_format]). This is [BD03] (S. Boldo, M. Daumas,
    Representable correcting terms for possibly underflowing floating point
    operations, ARITH 2003). Flocq proves it without subnormals
    ([sqrt_error_FLX_N]). With [x >= 2^-966], [sqrt x >= 2^-483] is far
    above the subnormals, so [s] is also the rounding without them, and
    [r] is a float without subnormals. If [|r| >= 2^-1022], that is a
    binary64 float. Below, [r] is still a multiple of [2^-1074], as [x] is
    one and [s] is a multiple of [2^-537], and the multiples of [2^-1074]
    below [2^-1022] are all binary64 floats.

    Second, the sign of [r] tells whether [s] is below or above [sqrt x]
    ([sqrt_rem_sign]), as [x - s * s = (sqrt x - s) * (sqrt x + s)]. *)

From Stdlib Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.Core Div_sqrt_error.
From Inari Require Import Model Encoding TwoSum.

Open Scope R_scope.

(** The binary64 floats, as reals. *)
Local Notation format := (generic_format radix2 fexp64).

(** [x - s * s] is a float for [s = RN(sqrt x)] and a float [x >= 2^-966]
    [BD03]. *)
Lemma sqrt_rem_format :
  forall x, format x -> bpow radix2 (-966) <= x ->
  format (x - RN (sqrt x) * RN (sqrt x)).
Proof.
intros x Fx Hx.
(* [sqrt x >= sqrt (2^-966) = 2^-483], and so is its rounding. *)
assert (Hsq : bpow radix2 (-483) <= sqrt x).
{ rewrite <- (sqrt_bpow radix2 (-483)).
  apply sqrt_le_1_alt. exact Hx. }
pose proof (generic_format_round radix2 fexp64 ZnearestE (sqrt x)) as Fs.
assert (Hs : bpow radix2 (-483) <= RN (sqrt x)).
{ apply round_ge_generic; [typeclasses eauto | typeclasses eauto | | exact Hsq].
  apply generic_format_FLT_bpow; [typeclasses eauto | lia]. }
set (s := RN (sqrt x)) in *.
(* [sqrt x >= 2^-1022], so subnormals play no part in rounding it. *)
assert (HsF : s = round radix2 (FLX_exp 53) ZnearestE (sqrt x)).
{ unfold s. apply round_FLT_FLX.
  rewrite Rabs_pos_eq by apply sqrt_pos.
  apply Rle_trans with (2 := Hsq). apply bpow_le. lia. }
(* So [x - s * s] is a float without subnormals [BD03]. *)
assert (Fr : generic_format radix2 (FLX_exp 53) (x - s * s)).
{ assert (Hp1 : (1 < 53)%Z) by lia.
  pose proof (sqrt_error_FLX_N radix2 53 (fun z => negb (Z.even z)) Hp1 x
    (generic_format_FLX_FLT radix2 (-1074) 53 x Fx)) as H.
  unfold Rsqr in H. rewrite <- HsF in H. exact H. }
destruct (Rle_or_lt (bpow radix2 (-1022)) (Rabs (x - s * s)))
  as [Hbig|Hsmall].
{ apply generic_format_FLT_FLX; [exact Hbig | exact Fr]. }
(* Below [2^-1022]: [x] is a multiple of [2^-1074], like every float. *)
assert (Ex : exists mx, x = F2R (Float radix2 mx (-1074))).
{ exists (Ztrunc (scaled_mantissa radix2 fexp64 x)
    * radix2 ^ (cexp radix2 fexp64 x - -1074))%Z.
  unfold generic_format in Fx. rewrite Fx at 1.
  apply F2R_change_exp. unfold cexp, FLT_exp. lia. }
(* [s >= 2^-483] has [mag s >= -482], so its exponent is at least
   [-482 - 53 >= -537], and [s * s] is a multiple of [2^-1074]. *)
assert (Hms : (-484 <= mag radix2 s)%Z).
{ apply mag_ge_bpow.
  rewrite Rabs_pos_eq by (apply Rle_trans with (2 := Hs); apply bpow_ge_0).
  apply Rle_trans with (2 := Hs). apply bpow_le. lia. }
assert (Es : exists ns, s = F2R (Float radix2 ns (-537))).
{ exists (Ztrunc (scaled_mantissa radix2 fexp64 s)
    * radix2 ^ (cexp radix2 fexp64 s - -537))%Z.
  unfold generic_format in Fs. rewrite Fs at 1.
  apply F2R_change_exp. unfold cexp, FLT_exp. lia. }
destruct Ex as [mx Hmx], Es as [ns Hns].
assert (HM : x - s * s = F2R (Float radix2 (mx - ns * ns) (-1074))).
{ rewrite Hmx, Hns. unfold F2R; cbn [Fnum Fexp].
  rewrite minus_IZR, mult_IZR.
  change (-1074)%Z with (-537 + -537)%Z. rewrite bpow_plus. ring. }
(* A multiple of [2^-1074] below [2^-1022] has exponent [-1074]. *)
rewrite HM. apply generic_format_F2R. intros Hnz.
assert (Hm : (mag radix2 (F2R (Float radix2 (mx - ns * ns) (-1074)))
  <= -1022)%Z).
{ apply mag_le_bpow.
  - apply F2R_neq_0. exact Hnz.
  - rewrite <- HM. exact Hsmall. }
unfold cexp, FLT_exp. lia.
Qed.

(** The sign of [a - s * s] compares [s] with [sqrt a]. *)
Lemma sqrt_rem_sign :
  forall a s, 0 <= a -> 0 < s ->
  (0 < a - s * s <-> s < sqrt a) /\ (a - s * s < 0 <-> sqrt a < s).
Proof.
intros a s Ha Hs.
(* [a - s * s = (sqrt a - s) * (sqrt a + s)] with [sqrt a + s > 0]. *)
pose proof (sqrt_sqrt a Ha) as Hsq.
pose proof (sqrt_pos a) as Ht.
set (t := sqrt a) in *.
split; split; intros H; nra.
Qed.
