(** * The ideal MPFR rounds correctly to an MPFR number of 53 bits

    [round_mpfr_correct]: [round_mpfr emin emax rnd r] is [r] rounded in
    the direction [rnd] to [mpfr_format emin emax], as [mpfr_round] says,
    for every real [r], overflow and underflow included. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Mpfr MpfrRound MpfrIdeal.

Open Scope R_scope.

(** [mpfr_format] is symmetric. *)
Lemma mpfr_format_opp :
  forall emin emax y, mpfr_format emin emax y -> mpfr_format emin emax (- y).
Proof.
intros emin emax y [H0|[Hf Hb]].
- left. rewrite H0. apply Ropp_0.
- right. split; [exact (generic_format_opp _ _ _ Hf)|]. rewrite Rabs_Ropp. exact Hb.
Qed.

(** [mpfr_max emax] is [2^emax - 2^(emax - 53)]: its significand is
    [2^53 - 1], and [2^emax] is [2^53 * 2^(emax - 53)]. *)
Lemma mpfr_max_eq :
  forall emax, mpfr_max emax = bpow radix2 emax - bpow radix2 (emax - 53).
Proof.
intros emax. unfold mpfr_max, F2R. cbn [Fnum Fexp].
assert (E : IZR (2 ^ 53) = bpow radix2 53) by (rewrite <- IZR_Zpower by lia; reflexivity).
rewrite minus_IZR, E.
replace emax with (53 + (emax - 53))%Z at 2 by lia. rewrite bpow_plus. ring.
Qed.

(** [mpfr_max emax] has 53 bits. *)
Lemma mpfr_max_FLX :
  forall emax, generic_format radix2 (FLX_exp 53) (mpfr_max emax).
Proof.
intros emax. apply generic_format_FLX.
apply (FLX_spec _ _ _ (Float radix2 (2 ^ 53 - 1) (emax - 53))); [reflexivity|].
cbn [Fnum radix_val radix2]. rewrite Z.abs_eq by lia. lia.
Qed.

(** No MPFR number is above [mpfr_max] in magnitude. *)
Lemma mpfr_format_abs_le :
  forall emin emax y, mpfr_format emin emax y -> Rabs y <= mpfr_max emax.
Proof.
intros emin emax y [->|[Hf [_ Hlt]]].
- rewrite Rabs_R0. apply F2R_ge_0. cbn [Fnum]. lia.
- (* [|y|] has 53 bits and is below [2^emax], which has 53 bits too, so
     it is at most the float of 53 bits just below [2^emax]. *)
  rewrite mpfr_max_eq. change (emax - 53)%Z with (FLX_exp 53 emax).
  rewrite <- (pred_bpow radix2 (FLX_exp 53)).
  apply pred_ge_gt; [typeclasses eauto | exact (generic_format_abs _ _ _ Hf) | | exact Hlt].
  apply generic_format_bpow. unfold FLX_exp. lia.
Qed.

(** [mpfr_max] is an MPFR number. *)
Lemma mpfr_max_format :
  forall emin emax, range_ok emin emax -> mpfr_format emin emax (mpfr_max emax).
Proof.
intros emin emax [Hmin Hmax]. right. split; [exact (mpfr_max_FLX emax)|].
(* [2^(emin - 1) <= 2^(emax - 53) <= (2^53 - 1) * 2^(emax - 53)], and
   [mpfr_max emax = 2^emax - 2^(emax - 53) < 2^emax]. *)
assert (Hb : bpow radix2 (emin - 1) <= bpow radix2 (emax - 53)) by (apply bpow_le; lia).
assert (Hp : 0 < bpow radix2 (emax - 53)) by apply bpow_gt_0.
assert (H1 : bpow radix2 (emax - 53) <= mpfr_max emax).
{ unfold mpfr_max, F2R. cbn [Fnum Fexp].
  rewrite <- (Rmult_1_l (bpow radix2 (emax - 53))) at 1.
  apply Rmult_le_compat_r; [lra|]. apply IZR_le. lia. }
rewrite Rabs_pos_eq by lra. split; [lra|].
rewrite mpfr_max_eq. lra.
Qed.

(** The least positive MPFR number, [2^(emin - 1)], has 53 bits. *)
Lemma bpow_emin_FLX :
  forall emin, generic_format radix2 (FLX_exp 53) (bpow radix2 (emin - 1)).
Proof.
intros emin. apply generic_format_bpow. unfold FLX_exp. lia.
Qed.

Lemma round_dn_correct :
  forall emin emax r, range_ok emin emax ->
  mpfr_round (mpfr_format emin emax) RNDD r (round_dn emin emax r).
Proof.
intros emin emax r Hr. pose proof (mpfr_max_format emin emax Hr) as FM.
destruct Hr as [Hmin Hmax].
assert (HM : forall g, mpfr_format emin emax g -> - mpfr_max emax <= g <= mpfr_max emax)
  by (intros g Fg; exact (Rabs_le_inv _ _ (mpfr_format_abs_le _ _ _ Fg))).
assert (HM0 : 0 < mpfr_max emax).
{ rewrite mpfr_max_eq. assert (bpow radix2 (emax - 53) < bpow radix2 emax) by (apply bpow_lt; lia).
  lra. }
assert (HMe : mpfr_max emax < bpow radix2 emax).
{ rewrite mpfr_max_eq. pose proof (bpow_gt_0 radix2 (emax - 53)). lra. }
assert (He0 : 0 < bpow radix2 (emin - 1)) by apply bpow_gt_0.
assert (Hee : bpow radix2 (emin - 1) < bpow radix2 emax) by (apply bpow_lt; lia).
unfold round_dn.
destruct (Rlt_dec r (- mpfr_max emax)) as [Hlo|Hlo]; cbn [mpfr_round].
{ (* (a) Every MPFR number is at least [-mpfr_max], which is above [r]. *)
  intros g Fg. pose proof (HM g Fg). lra. }
destruct (Rle_dec (bpow radix2 emax) r) as [Hhi|Hhi]; cbn [mpfr_round].
{ (* (b) [mpfr_max] is the largest MPFR number, and it is below [r]. *)
  split; [lra|]. split; [exact FM|]. split; [lra|].
  intros g Fg _. exact (proj2 (HM g Fg)). }
destruct (Rle_dec (bpow radix2 (emin - 1)) (Rabs r)) as [Hab|Hab]; cbn [mpfr_round].
- (* (c) [r] is rounded down to 53 bits, to [d]. As [|r|] is at least the
     least positive MPFR number, which has 53 bits, and [r] is at least
     [-mpfr_max], which has 53 bits too, and below [2^emax], [d] is an MPFR
     number. *)
  set (d := round radix2 (FLX_exp 53) Zfloor r).
  destruct (round_DN_pt radix2 (FLX_exp 53) r) as (Fd & Hdr & Hdmax). fold d in Fd, Hdr, Hdmax.
  assert (Hpos : 0 < r -> bpow radix2 (emin - 1) <= d).
  { intros H0. rewrite Rabs_pos_eq in Hab by lra.
    exact (Hdmax _ (bpow_emin_FLX emin) Hab). }
  assert (Hneg : r < 0 -> - mpfr_max emax <= d).
  { intros _. apply Hdmax; [exact (generic_format_opp _ _ _ (mpfr_max_FLX emax)) | lra]. }
  assert (Hr0 : r <> 0) by (intros H0; rewrite H0, Rabs_R0 in Hab; lra).
  assert (Hd0 : d <> 0).
  { destruct (Rlt_or_le 0 r) as [H0|H0]; [pose proof (Hpos H0); lra|].
    assert (r < 0) by lra. lra. }
  split; [exact Hd0|]. split; [|split; [exact Hdr|]].
  + right. split; [exact Fd|].
    destruct (Rlt_or_le 0 r) as [H0|H0].
    * pose proof (Hpos H0). rewrite Rabs_pos_eq by lra. lra.
    * assert (Hn : r < 0) by lra. pose proof (Hneg Hn).
      rewrite Rabs_left in Hab by exact Hn. rewrite Rabs_left by lra. lra.
  + (* An MPFR number at or below [r] is 0, which is then below [d] as [r]
       is positive, or has 53 bits, so is at or below [d]. *)
    intros g [->|[Fg _]] Hg.
    * destruct (Rlt_or_le 0 r) as [H0|H0]; [pose proof (Hpos H0); lra | lra].
    * exact (Hdmax g Fg Hg).
- apply Rnot_le_lt in Hab.
  destruct (Rle_dec 0 r) as [H0|H0]; cbn [mpfr_round].
  + (* (d) [0 <= r < 2^(emin - 1)]: a positive MPFR number is at least
       [2^(emin - 1)], so above [r]. *)
    split; [exact (mpfr_format_0 emin emax)|]. split; [exact H0|].
    intros g [->|[_ [Hg _]]] Hgr; [apply Rle_refl|].
    apply Rnot_lt_le. intros Hg0.
    rewrite Rabs_pos_eq in Hg, Hab by lra. lra.
  + (* (e) [-2^(emin - 1) < r < 0]: a negative MPFR number is at most
       [-2^(emin - 1)], the MPFR number just below 0. *)
    apply Rnot_le_lt in H0. rewrite Rabs_left in Hab by exact H0.
    split; [lra|]. split; [|split; [lra|]].
    * right. split; [exact (generic_format_opp _ _ _ (bpow_emin_FLX emin))|].
      rewrite Rabs_Ropp, Rabs_pos_eq by lra. lra.
    * intros g [->|[_ [Hg _]]] Hgr; [lra|].
      rewrite Rabs_left in Hg by lra. lra.
Qed.

(** Rounding up is the negation of rounding the negation down, for a
    symmetric [F]. *)
Lemma mpfr_round_mneg :
  forall (F : R -> Prop) r v, (forall y, F y -> F (- y)) ->
  mpfr_round F RNDD (- r) v -> mpfr_round F RNDU r (mneg v).
Proof.
intros F r [|[|]|s|y] HF H; cbn [mpfr_round mneg negb] in *; try contradiction.
- intros g Fg. pose proof (H (- g) (HF g Fg)). lra.
- pose proof (Rnd_UP_pt_opp F HF _ _ H) as H'. rewrite Ropp_involutive, Ropp_0 in H'.
  exact H'.
- destruct H as [Hy H]. split; [lra|].
  pose proof (Rnd_UP_pt_opp F HF _ _ H) as H'. rewrite Ropp_involutive in H'. exact H'.
Qed.

Theorem round_mpfr_correct :
  forall emin emax rnd r, range_ok emin emax ->
  mpfr_round (mpfr_format emin emax) rnd r (round_mpfr emin emax rnd r).
Proof.
intros emin emax [|] r Hr; cbn [round_mpfr].
- exact (round_dn_correct emin emax r Hr).
- apply mpfr_round_mneg; [apply mpfr_format_opp|].
  exact (round_dn_correct emin emax (- r) Hr).
Qed.
