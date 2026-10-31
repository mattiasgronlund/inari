(** * [Interval::PI], [TAU] and [FRAC_PI_2] to [FRAC_PI_8] are the tightest intervals around their values

    [PI_Q] bounds π by two rationals [10^-18] apart, from the partial sums
    of the series of the Machin-like formula
    [PI / 4 = 2 * atan (/3) + atan (/7)] in [PiBounds.v] ([PI_2_3_7_ineq]
    in Stdlib's [Machin.v]). These rationals for [PI], twice them for
    [TAU], and them divided by 2, 3, 4, 6 or 8 for [FRAC_PI_2] to
    [FRAC_PI_8] lie strictly between the bounds of the constant, which
    [vm_compute] checks, and [const_tightest_Q] concludes. Each theorem
    also covers the [DecInterval] constant that [def_com!] makes from the
    [Interval] one, whose interval is the same. *)

From Stdlib Require Import ZArith Reals Lra QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 PiBounds ConstTight.

Open Scope R_scope.

(** π to 18 decimals, below and above. *)
Definition pi_lo : Q := 3141592653589793238 # 1000000000000000000.
Definition pi_hi : Q := 3141592653589793239 # 1000000000000000000.

Lemma PI_Q : Q2R pi_lo < PI < Q2R pi_hi.
Proof.
  (* [PI_2_3_7_ineq 9] puts PI / 4 between the partial sums of that series
     up to the terms 19 and 18, which [pb_sumQ_R] computes in [Q]. *)
  destruct (PI_2_3_7_ineq 9) as [H1 H2].
  change (S (2 * 9)) with 19%nat in H1; change (2 * 9)%nat with 18%nat in H2.
  rewrite <- pb_sumQ_R in H1, H2.
  assert (H3 : (pi_lo < 4 * pb_sumQ pb_altQ 19)%Q) by (vm_compute; reflexivity).
  assert (H4 : (4 * pb_sumQ pb_altQ 18 < pi_hi)%Q) by (vm_compute; reflexivity).
  apply Qlt_Rlt in H3, H4.
  rewrite Q2R_mult in H3, H4.
  replace (Q2R 4) with 4 in H3, H4 by (unfold Q2R; simpl; lra).
  lra.
Qed.

Theorem PI_tightest :
  is_tightest (fun r => r = PI) Interval.PI /\
  is_tightest (fun r => r = PI) (itv DecInterval.PI).
Proof.
  assert (H : is_tightest (fun r => r = PI) Interval.PI).
  { apply (const_tightest_Q _ _ _ pi_lo pi_hi).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply B2SF_inj; vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - pose proof PI_Q; lra. }
  (* [DecInterval.PI] is [new_unchecked Interval.PI Com]. *)
  split; exact H.
Qed.

Theorem TAU_tightest :
  is_tightest (fun r => r = 2 * PI) Interval.TAU /\
  is_tightest (fun r => r = 2 * PI) (itv DecInterval.TAU).
Proof.
  assert (H : is_tightest (fun r => r = 2 * PI) Interval.TAU).
  { apply (const_tightest_Q _ _ _ (2 * pi_lo)%Q (2 * pi_hi)%Q).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply B2SF_inj; vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - pose proof PI_Q; rewrite !Q2R_mult.
      replace (Q2R 2) with 2 by (unfold Q2R; simpl; lra).
      lra. }
  (* [DecInterval.TAU] is [new_unchecked Interval.TAU Com]. *)
  split; exact H.
Qed.

Theorem FRAC_PI_2_tightest :
  is_tightest (fun r => r = PI / 2) Interval.FRAC_PI_2 /\
  is_tightest (fun r => r = PI / 2) (itv DecInterval.FRAC_PI_2).
Proof.
  assert (H : is_tightest (fun r => r = PI / 2) Interval.FRAC_PI_2).
  { apply (const_tightest_Q _ _ _ (pi_lo * (1 # 2))%Q (pi_hi * (1 # 2))%Q).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply B2SF_inj; vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - pose proof PI_Q; rewrite !Q2R_mult.
      replace (Q2R (1 # 2)) with (/ 2) by (unfold Q2R; simpl; lra).
      lra. }
  (* [DecInterval.FRAC_PI_2] is [new_unchecked Interval.FRAC_PI_2 Com]. *)
  split; exact H.
Qed.

Theorem FRAC_PI_3_tightest :
  is_tightest (fun r => r = PI / 3) Interval.FRAC_PI_3 /\
  is_tightest (fun r => r = PI / 3) (itv DecInterval.FRAC_PI_3).
Proof.
  assert (H : is_tightest (fun r => r = PI / 3) Interval.FRAC_PI_3).
  { apply (const_tightest_Q _ _ _ (pi_lo * (1 # 3))%Q (pi_hi * (1 # 3))%Q).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply B2SF_inj; vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - pose proof PI_Q; rewrite !Q2R_mult.
      replace (Q2R (1 # 3)) with (/ 3) by (unfold Q2R; simpl; lra).
      lra. }
  (* [DecInterval.FRAC_PI_3] is [new_unchecked Interval.FRAC_PI_3 Com]. *)
  split; exact H.
Qed.

Theorem FRAC_PI_4_tightest :
  is_tightest (fun r => r = PI / 4) Interval.FRAC_PI_4 /\
  is_tightest (fun r => r = PI / 4) (itv DecInterval.FRAC_PI_4).
Proof.
  assert (H : is_tightest (fun r => r = PI / 4) Interval.FRAC_PI_4).
  { apply (const_tightest_Q _ _ _ (pi_lo * (1 # 4))%Q (pi_hi * (1 # 4))%Q).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply B2SF_inj; vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - pose proof PI_Q; rewrite !Q2R_mult.
      replace (Q2R (1 # 4)) with (/ 4) by (unfold Q2R; simpl; lra).
      lra. }
  (* [DecInterval.FRAC_PI_4] is [new_unchecked Interval.FRAC_PI_4 Com]. *)
  split; exact H.
Qed.

Theorem FRAC_PI_6_tightest :
  is_tightest (fun r => r = PI / 6) Interval.FRAC_PI_6 /\
  is_tightest (fun r => r = PI / 6) (itv DecInterval.FRAC_PI_6).
Proof.
  assert (H : is_tightest (fun r => r = PI / 6) Interval.FRAC_PI_6).
  { apply (const_tightest_Q _ _ _ (pi_lo * (1 # 6))%Q (pi_hi * (1 # 6))%Q).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply B2SF_inj; vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - pose proof PI_Q; rewrite !Q2R_mult.
      replace (Q2R (1 # 6)) with (/ 6) by (unfold Q2R; simpl; lra).
      lra. }
  (* [DecInterval.FRAC_PI_6] is [new_unchecked Interval.FRAC_PI_6 Com]. *)
  split; exact H.
Qed.

Theorem FRAC_PI_8_tightest :
  is_tightest (fun r => r = PI / 8) Interval.FRAC_PI_8 /\
  is_tightest (fun r => r = PI / 8) (itv DecInterval.FRAC_PI_8).
Proof.
  assert (H : is_tightest (fun r => r = PI / 8) Interval.FRAC_PI_8).
  { apply (const_tightest_Q _ _ _ (pi_lo * (1 # 8))%Q (pi_hi * (1 # 8))%Q).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply B2SF_inj; vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - pose proof PI_Q; rewrite !Q2R_mult.
      replace (Q2R (1 # 8)) with (/ 8) by (unfold Q2R; simpl; lra).
      lra. }
  (* [DecInterval.FRAC_PI_8] is [new_unchecked Interval.FRAC_PI_8 Com]. *)
  split; exact H.
Qed.
