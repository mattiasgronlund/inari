(** * The conversions of the ideal MPFR

    [ideal_set_q_ok] and [ideal_subnormalize_ok]: the [mpfr_set_q] and
    [mpfr_subnormalize] of the ideal MPFR satisfy [set_q_ok] and
    [subnormalize_ok] at every range with [range_ok]. *)

From Stdlib Require Import ZArith Reals Qreals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Mpfr MpfrRound MpfrIdeal IdealRound.

Open Scope R_scope.

(** [ternary] is the ternary value of any rounding. A rounding is never
    NaN, and for the other results [ternary] is the sign of [v - r] by
    definition, or that of the infinity. *)
Lemma ternary_correct :
  forall F rnd r v, mpfr_round F rnd r v -> ternary_ok r v (ternary r v).
Proof.
intros F rnd r [|[|]|s|y] H; cbn [ternary ternary_ok mval].
- destruct rnd; contradiction.
- lia.
- lia.
- destruct (Rcompare_spec 0 r) as [H0|H0|H0]; cbv iota;
    (split; split; intros; first [lia | lra | exfalso; lra]).
- destruct (Rcompare_spec y r) as [H0|H0|H0]; cbv iota;
    (split; split; intros; first [lia | lra | exfalso; lra]).
Qed.

Theorem ideal_set_q_ok :
  forall emin emax a b, range_ok emin emax -> set_q_ok emin emax (ideal a b).
Proof.
intros emin emax a b Hr rnd q. cbn [mpfr_set_q ideal ideal_set_q fst snd].
pose proof (round_mpfr_correct emin emax rnd (Q2R q) Hr) as H.
split; [exact H | exact (ternary_correct _ _ _ _ H)].
Qed.

(** [mpfr_max] is below [2^emax]: its significand [2^53 - 1] is below
    [2^53]. *)
Lemma mpfr_max_lt : forall emax, mpfr_max emax < bpow radix2 emax.
Proof.
intros emax. unfold mpfr_max, F2R. cbn [Fnum Fexp].
replace (bpow radix2 emax) with (bpow radix2 53 * bpow radix2 (emax - 53))
  by (rewrite <- bpow_plus; f_equal; lia).
apply Rmult_lt_compat_r; [apply bpow_gt_0|].
rewrite <- IZR_Zpower by lia. apply IZR_lt. reflexivity.
Qed.

(** [sub_format] is symmetric, as [mpfr_format] and the format of
    [FLT_exp (emin - 1) 53] are. *)
Lemma sub_format_opp :
  forall emin emax y, sub_format emin emax y -> sub_format emin emax (- y).
Proof.
intros emin emax y [Fy Gy]. split.
- exact (mpfr_format_opp _ _ _ Fy).
- exact (generic_format_opp _ _ _ Gy).
Qed.

(** An MPFR number [y] other than 0, rounded toward -inf to the multiples
    of [2^(emin - 1)] with 53 bits ([round_sub]), is [y] rounded toward
    -inf to [sub_format], and is not 0. The rounding [z] is the largest
    element of the format of [FLT_exp (emin - 1) 53] at or below [y], so
    it is an MPFR number if its magnitude is in MPFR's range. It is at
    least [2^(emin - 1)] in magnitude: for [y > 0], [2^(emin - 1)] is in
    that format and at or below [y], so at or below [z]; for [y < 0],
    [z <= y <= -2^(emin - 1)]. It is below [2^emax] in magnitude: for
    [y > 0], [z <= y]; for [y < 0], [-mpfr_max] is in that format and at
    or below [y], so at or below [z]. *)
Lemma round_sub_dn :
  forall emin emax y, range_ok emin emax -> y <> 0 -> mpfr_format emin emax y ->
  round_sub emin RNDD y <> 0 /\ Rnd_DN_pt (sub_format emin emax) y (round_sub emin RNDD y).
Proof.
intros emin emax y [Hmin Hmax] Hy Fy.
pose proof (mpfr_format_abs_le _ _ _ Fy) as Habs.
destruct Fy as [Hy0 | (_ & Hlo & Hhi)]; [contradiction|].
unfold round_sub. cbn [f64_mode round_mode].
pose proof (round_DN_pt radix2 (FLT_exp (emin - 1) 53) y) as (Gz & Hzy & Hzmax).
set (z := round radix2 (FLT_exp (emin - 1) 53) Zfloor y) in *.
assert (Hb : 0 < bpow radix2 (emin - 1)) by apply bpow_gt_0.
pose proof (mpfr_max_lt emax) as HM.
assert (Gb : generic_format radix2 (FLT_exp (emin - 1) 53) (bpow radix2 (emin - 1)))
  by (apply generic_format_FLT_bpow; [exact prec_gt_0_53 | lia]).
assert (GM : generic_format radix2 (FLT_exp (emin - 1) 53) (- mpfr_max emax)).
{ apply generic_format_opp. apply generic_format_FLT.
  (* [mpfr_max] is [(2^53 - 1) * 2^(emax - 53)], and [emax - 53] is at
     least [emin - 1] by [range_ok]. *)
  apply (FLT_spec _ _ _ _ (Float radix2 (2 ^ 53 - 1) (emax - 53))); cbn [Fnum Fexp].
  - reflexivity.
  - reflexivity.
  - lia. }
assert (Hz : bpow radix2 (emin - 1) <= Rabs z < bpow radix2 emax).
{ destruct (Rle_or_lt 0 y) as [Hy1 | Hy1].
  - rewrite Rabs_pos_eq in Hlo, Hhi by exact Hy1.
    pose proof (Hzmax _ Gb Hlo) as Hbz.
    rewrite Rabs_pos_eq by lra. lra.
  - rewrite Rabs_left in Hlo, Hhi, Habs by exact Hy1.
    assert (HMy : - mpfr_max emax <= y) by lra.
    pose proof (Hzmax _ GM HMy) as HMz.
    rewrite Rabs_left by lra. lra. }
split.
- intros Hz0. rewrite Hz0, Rabs_R0 in Hz. lra.
- split; [split|split; [exact Hzy|]].
  + right. split; [|exact Hz].
    exact (generic_format_FLX_FLT radix2 (emin - 1) 53 z Gz).
  + exact Gz.
  + intros g (_ & Gg) Hg. exact (Hzmax g Gg Hg).
Qed.

(** Toward +inf, by symmetry: [round_sub] toward +inf of [y] is the
    negation of [round_sub] toward -inf of [-y]. *)
Lemma round_sub_up :
  forall emin emax y, range_ok emin emax -> y <> 0 -> mpfr_format emin emax y ->
  round_sub emin RNDU y <> 0 /\ Rnd_UP_pt (sub_format emin emax) y (round_sub emin RNDU y).
Proof.
intros emin emax y Hr Hy Fy.
assert (E : round_sub emin RNDU y = - round_sub emin RNDD (- y)).
{ unfold round_sub. cbn [f64_mode round_mode].
  rewrite round_DN_opp, Ropp_involutive. reflexivity. }
destruct (round_sub_dn emin emax (- y) Hr) as [Hz HDN].
- lra.
- exact (mpfr_format_opp _ _ _ Fy).
- rewrite E. split; [lra|].
  pose proof (Rnd_UP_pt_opp _ (sub_format_opp emin emax) _ _ HDN) as H.
  rewrite Ropp_involutive in H. exact H.
Qed.

(** An infinity and a zero stay, and are already the rounding to
    [sub_format], which is contained in [mpfr_format] and contains 0. An
    MPFR number [y] other than 0, the rounding of [r], rounds again to
    [z], the rounding of [y] to [sub_format] ([round_sub_dn],
    [round_sub_up]), so of [r] ([round_compose]). If [z = y], the
    ternary value stays; otherwise [z] is on the far side of [y] from [r],
    so the ternary value is -1 toward -inf and 1 toward +inf. *)
Theorem ideal_subnormalize_ok :
  forall emin emax a b, range_ok emin emax -> subnormalize_ok emin emax (ideal a b).
Proof.
intros emin emax a b Hr rnd r x t Hx Ht. cbn [mpfr_subnormalize ideal].
assert (Hsub : forall g, sub_format emin emax g -> mpfr_format emin emax g)
  by (intros g [Fg _]; exact Fg).
destruct x as [|s|s|y].
- destruct rnd; contradiction.
- cbn [ideal_subnormalize fst snd].
  split; [exact (round_inf_sub _ _ rnd r s Hsub Hx) | exact Ht].
- cbn [ideal_subnormalize fst snd]. split; [|exact Ht].
  apply (round_compose (sub_format emin emax) (mpfr_format emin emax) rnd r 0 (MZero s) Hsub).
  + destruct rnd; exact Hx.
  + apply mpfr_round_zero. split; [apply mpfr_format_0 | apply generic_format_0].
- assert (Hy : y <> 0 /\ rnd_pt (mpfr_format emin emax) rnd r y)
    by (destruct rnd; exact Hx).
  destruct Hy as [Hy0 Hpt].
  assert (Fy : mpfr_format emin emax y) by (destruct rnd; exact (proj1 Hpt)).
  assert (Hz : round_sub emin rnd y <> 0 /\
               rnd_pt (sub_format emin emax) rnd y (round_sub emin rnd y)).
  { destruct rnd; [apply round_sub_dn | apply round_sub_up]; assumption. }
  destruct Hz as [Hz0 Hzpt].
  assert (Hround : mpfr_round (sub_format emin emax) rnd r (MNum (round_sub emin rnd y))).
  { apply (round_compose _ _ rnd r y _ Hsub Hpt).
    destruct rnd; cbn [mpfr_round]; split; assumption. }
  cbn [ideal_subnormalize].
  destruct (Req_dec_T (round_sub emin rnd y) y) as [E|E]; cbn [fst snd].
  + rewrite E in Hround. split; [exact Hround | exact Ht].
  + split; [exact Hround|].
    destruct rnd; cbn [ternary_ok];
      destruct Hpt as (_ & Hyr & _); destruct Hzpt as (_ & Hzy & _).
    * (* Toward -inf: [z < y <= r]. *)
      assert (Hlt : round_sub emin RNDD y < y) by (destruct Hzy as [Hzy|Hzy]; [assumption | contradiction]).
      split; split; intros; first [lia | lra | exfalso; lra].
    * (* Toward +inf: [r <= y < z]. *)
      assert (Hlt : y < round_sub emin RNDU y)
        by (destruct Hzy as [Hzy|Hzy]; [assumption | symmetry in Hzy; contradiction]).
      split; split; intros; first [lia | lra | exfalso; lra].
Qed.
