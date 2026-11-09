(** * Rounding a dyadic number to nearest

    [Dyadic.to_f64_near] rounds a dyadic number to the nearest [f64],
    ties to even, as [near_round] says, and gives +0 for a zero
    ([to_f64_near_correct]). *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs IdealGetD DyRound DyConv DyOps OfPointCore
  NearF64 NearCells NearRound.
From Inari Require RoundUpExact Spec.

Open Scope Z_scope.

(** ** Helpers *)

(** The exponent of the format at a number of magnitude [k], as in
    [NearCells.v], where it is [Local]. *)
Local Lemma cexp_at :
  forall r k, (bpow radix2 (k - 1) <= Rabs r < bpow radix2 k)%R ->
  cexp radix2 (FLT_exp (-1074) 53) r = Z.max (k - 53) (-1074).
Proof.
intros r k H. unfold cexp, FLT_exp. now rewrite (mag_unique radix2 r k H).
Qed.

(** [round_near n x] rounds [|x|] to nearest: [b = exp + 64 n] is the
    exponent of the bit above the top of [|x|], so [|x| >= 2^1024]
    overflows if [b >= 1025], [|x| < 2^-1075] rounds to +0 if
    [b <= -1075], and otherwise the window [q] of [round_up_window], with
    [q 2^(b - 128)] at or just below [|x|], keeps its bits from [lsb], the
    exponent of the format at [|x|], up: [near_window] says that they and
    the round bit are [|x| 2^-lsb] rounded to the nearest integer [k], so
    [k 2^lsb] is [|x|] rounded to nearest, which [round_up_exact] gives
    exactly. *)
Local Lemma round_near_abs :
  forall n x,
  level_ok n -> dy_ok n x -> Dyadic.is_zero n x = false ->
  exists v, Dyadic.round_near n x = Some v /\ near_round (Rabs (Dyadic.dy_R x)) v.
Proof.
intros n x Hn Hx Hz.
pose proof (dprec_bounds n Hn) as Hp.
pose proof Hx as (Hm & Hl & He & _).
destruct (dy_cases n x Hn Hx) as [(Hz' & _) | (_ & HM & Hb1 & Hb2)];
  [rewrite Hz' in Hz; discriminate Hz |].
pose proof (round_up_window n (Dyadic.dy_m x) (Dyadic.dy_exp x) Hn Hm Hl (proj1 HM)) as Hw.
cbv zeta in Hw. rewrite <- dy_abs in Hw by exact Hm.
unfold Dyadic.round_near.
change (64 * Z.of_nat n) with (dprec n).
rewrite (checked_i128 (Dyadic.dy_exp x + dprec n)) by lia.
cbv beta iota zeta.
set (b := Dyadic.dy_exp x + dprec n) in *.
set (A := Rabs (Dyadic.dy_R x)) in *.
assert (HA : (0 < A)%R) by (pose proof (bpow_gt_0 radix2 (b - 1)); lra).
destruct (Z.leb_spec 1025 b) as [Hh | Hh].
{ (* [|x| >= 2^(b - 1) >= 2^1024] *)
  exists infinity. split; [reflexivity |]. apply near_inf.
  assert (bpow radix2 1024 <= bpow radix2 (b - 1))%R by (apply bpow_le; lia).
  pose proof (bpow_gt_0 radix2 970). lra. }
destruct (Z.leb_spec b (-1075)) as [Ht | Ht].
{ (* [0 < |x| < 2^b <= 2^-1075] *)
  exists zero. split; [reflexivity |]. apply near_zero. split; [exact HA |].
  apply Rlt_le. apply Rlt_le_trans with (1 := Hb2). apply bpow_le. exact Ht. }
destruct Hw as (Hq & Hw).
set (q := Z.lor _ _) in *.
set (sticky := existsb _ _) in *.
clearbody q sticky.
set (lsb := Z.max (b - 53) (-1074)) in *.
set (s := lsb - (b - 128)) in *.
(* [lsb] is [b - 53] for [b >= -1021], where [s = 75], and -1074 below,
   where [s = -946 - b] is at most 128. *)
assert (Hs : 75 <= s <= 128) by (unfold s, lsb; lia).
(* [kept] and [rest] are [q / 2^s] and [q mod 2^s], also at [s = 128],
   where [q < 2^128]. *)
assert (Hkr : (if s =? 128 then (0, q) else (Z.shiftr q s, Z.land q (Z.shiftl 1 s - 1))) =
              (q / 2 ^ s, q mod 2 ^ s)).
{ destruct (Z.eqb_spec s 128) as [Es | Es].
  - rewrite Es, Z.div_small, Z.mod_small by lia. reflexivity.
  - rewrite Z.shiftr_div_pow2 by lia.
    replace (Z.shiftl 1 s - 1) with (Z.ones s) by (rewrite Z.ones_equiv, Z.shiftl_1_l; lia).
    rewrite Z.land_ones by lia. reflexivity. }
rewrite Hkr. cbv beta iota.
rewrite Z.shiftl_1_l.
(* [X = |x| 2^(128 - b)] is [q], or strictly between [q] and [q + 1]. *)
assert (HX : if sticky then (IZR q < A * bpow radix2 (128 - b) < IZR q + 1)%R
             else (A * bpow radix2 (128 - b) = IZR q)%R).
{ assert (Hc : forall a, (F2R (Float radix2 a (b - 128)) * bpow radix2 (128 - b) = IZR a)%R).
  { intros a. unfold F2R; cbn [Fnum Fexp]. rewrite Rmult_assoc, <- bpow_plus.
    replace (b - 128 + (128 - b)) with 0 by ring. change (bpow radix2 0) with 1%R. ring. }
  pose proof (bpow_gt_0 radix2 (128 - b)) as H0.
  destruct sticky; cbv iota in Hw |- *.
  - destruct Hw as (H1 & H2).
    replace (IZR q + 1)%R with (IZR (q + 1)) by apply plus_IZR.
    split; [rewrite <- (Hc q) | rewrite <- (Hc (q + 1))];
      apply Rmult_lt_compat_r; assumption.
  - rewrite Hw. apply Hc. }
(* [X 2^-s = |x| 2^-lsb] *)
assert (Hsc : (A * bpow radix2 (128 - b) * bpow radix2 (- s) = A * bpow radix2 (- lsb))%R).
{ rewrite Rmult_assoc, <- bpow_plus.
  replace (128 - b + - s) with (- lsb) by (unfold s; ring). reflexivity. }
pose proof (near_window q s sticky (A * bpow radix2 (128 - b)) ltac:(lia) ltac:(lia) HX)
  as Hk.
rewrite Hsc in Hk. rewrite <- Hk.
set (k := ZnearestE (A * bpow radix2 (- lsb))) in *.
(* [q / 2^s < 2^(128 - s) <= 2^53], so [k <= 2^53]. *)
assert (Hdiv : 0 <= q / 2 ^ s < 2 ^ 53).
{ split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] |].
  apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia |].
  rewrite <- Z.pow_add_r by lia.
  apply Z.lt_le_trans with (2 ^ 128); [lia |]. apply Z.pow_le_mono_r; lia. }
assert (Hk0 : 0 <= k <= 2 ^ 53).
{ rewrite Hk. match goal with |- context [if ?c then _ else _] => destruct c end; lia. }
(* The exponent of the format at [|x|] is [lsb], so [RN |x| = k 2^lsb]. *)
assert (HRN : round radix2 (FLT_exp (-1074) 53) ZnearestE A = (IZR k * bpow radix2 lsb)%R).
{ unfold round, scaled_mantissa, F2R.
  rewrite (cexp_at A b) by (rewrite Rabs_pos_eq by lra; split; assumption).
  reflexivity. }
destruct (Z.eqb_spec k 0) as [Hk00 | Hk00].
- (* [RN |x| = 0 < 2^1024], so [|x|] is below the bound of overflow
     ([RN_ge_T]), and +0 is the rounding of the positive [|x|]. *)
  exists zero. split; [reflexivity |].
  assert (HAT : (A < bpow radix2 1024 - bpow radix2 970)%R).
  { destruct (Rlt_le_dec A (bpow radix2 1024 - bpow radix2 970)) as [H | H]; [exact H |].
    apply RN_ge_T in H. rewrite HRN, Hk00, Rmult_0_l in H.
    pose proof (bpow_gt_0 radix2 1024). lra. }
  unfold near_round. rewrite (Rabs_pos_eq A) by lra.
  destruct (Rle_dec _ _) as [H | _]; [lra |].
  split; [reflexivity |]. split.
  + rewrite HRN, Hk00. change (B2R zero) with 0%R. ring.
  + intros _ _. rewrite Rlt_bool_false by lra. reflexivity.
- (* [round_up_exact] gives the positive [k 2^lsb] exactly, which is
     [RN |x|] ([near_of_up]). *)
  assert (Hv : (0 <= IZR k * bpow radix2 lsb)%R).
  { apply Rmult_le_pos; [apply IZR_le; lia | apply bpow_ge_0]. }
  destruct (RoundUpExact.round_up_exact_correct false k lsb false (IZR k * bpow radix2 lsb)%R)
    as (r & Hr & Hu).
  { unfold Spec.round_up_exact_pre.
    split; [lia |]. split; [unfold lsb; lia |]. split; [intros H; discriminate H |].
    split; [apply Rlt_bool_false; exact Hv |].
    cbv iota. rewrite Rabs_pos_eq by exact Hv. reflexivity. }
  exists r. split; [exact Hr |].
  apply near_of_up; [exact HA |]. rewrite HRN. exact Hu.
Qed.

(** ** The theorem *)

Lemma to_f64_near_correct :
  forall n x,
  level_ok n -> dy_ok n x ->
  exists v, Dyadic.to_f64_near n x = Some v /\ near_round (Dyadic.dy_R x) v /\
  (Dyadic.dy_R x = 0%R -> v = zero).
Proof.
intros n x Hn Hx. unfold Dyadic.to_f64_near.
destruct (dy_cases n x Hn Hx) as [(Hz & _ & _ & _ & H0) | (Hz & _ & Hb & _)]; rewrite Hz.
- (* 0 rounds to +0. *)
  exists zero. split; [reflexivity |]. split; [| intros _; reflexivity].
  rewrite H0. unfold near_round. rewrite Rabs_R0.
  destruct (Rle_dec _ _) as [H | _].
  { assert (bpow radix2 970 < bpow radix2 1024)%R by (apply bpow_lt; lia). lra. }
  split; [reflexivity |]. split.
  + rewrite round_0 by auto with typeclass_instances. reflexivity.
  + intros H. exfalso. apply H. reflexivity.
- (* [round_near] rounds [|x|], and a negative [x] rounds to the
     negation ([near_opp]). *)
  assert (Hm : limbs_ok (Dyadic.dy_m x)) by exact (proj1 Hx).
  assert (Hv0 : Dyadic.dy_R x <> 0%R).
  { intros E0. rewrite E0, Rabs_R0 in Hb.
    pose proof (bpow_gt_0 radix2 (Dyadic.dy_exp x + dprec n - 1)). lra. }
  destruct (round_near_abs n x Hn Hx Hz) as (v & Hr & Hv).
  rewrite Hr.
  pose proof (dy_R_sign x Hm) as Hs.
  destruct (Dyadic.dy_neg x).
  + exists (opp v). split; [reflexivity |]. split; [| intros E0; contradiction].
    rewrite Hs. apply near_opp. exact Hv.
  + exists v. split; [reflexivity |]. split; [| intros E0; contradiction].
    rewrite Hs. exact Hv.
Qed.
