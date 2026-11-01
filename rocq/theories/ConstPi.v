(** * [Interval::PI], [TAU] and [FRAC_PI_2] to [FRAC_PI_8] are the tightest intervals around their values

    The bounds of [Interval::PI] and [Interval::FRAC_PI_2] are finite and
    adjacent floats ([pt_PI_facts] and [pt_FRAC_PI_2_facts] in
    [PiTight.v]), below and above π and π/2 ([PI_bounds], [pb_frac_lo]
    and [pb_frac_hi] in [PiBounds.v]), and [const_tightest] concludes.
    For the other constants, [PI_Q] in [PiBounds.v] bounds π by two
    rationals [10^-18] apart. [vm_compute] checks that the bounds of each
    constant are finite and adjacent floats, and that twice these
    rationals for [TAU], and these divided by 3, 4, 6 or 8 for
    [FRAC_PI_3] to [FRAC_PI_8], lie strictly between those bounds, and
    [const_tightest_Q] concludes. Each theorem also covers the
    [DecInterval] constant that [def_com!] makes from the [Interval] one,
    whose interval is the same, and shows that its decoration, [com], is
    the strongest ([strongest0]), as its interval is common
    ([const_strongest0] in [ConstTight.v]). *)

From Stdlib Require Import ZArith Reals Lra QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 PiBounds PiTight ConstTight.

Open Scope R_scope.

Theorem PI_tightest :
  is_tightest (fun r => r = PI) Interval.PI /\
  is_tightest (fun r => r = PI) (itv DecInterval.PI) /\
  strongest0 (dec DecInterval.PI) PI (itv DecInterval.PI).
Proof.
  assert (H : is_tightest (fun r => r = PI) Interval.PI).
  { (* [const_tightest] is about the [const_interval] of the bounds of
       [Interval.PI], which computes to [Interval.PI]: [inf_raw] negates
       the first lane, and [const_interval] negates it back. *)
    destruct pt_PI_facts as (F0 & F1 & Hs).
    exact (const_tightest _ _ PI F0 F1 Hs PI_bounds). }
  (* [DecInterval.PI] is [new_unchecked Interval.PI Com]. *)
  split; [exact H | split; [exact H |]].
  apply const_strongest0; vm_compute; reflexivity.
Qed.

Theorem TAU_tightest :
  is_tightest (fun r => r = 2 * PI) Interval.TAU /\
  is_tightest (fun r => r = 2 * PI) (itv DecInterval.TAU) /\
  strongest0 (dec DecInterval.TAU) (2 * PI) (itv DecInterval.TAU).
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
  split; [exact H | split; [exact H |]].
  apply const_strongest0; vm_compute; reflexivity.
Qed.

Theorem FRAC_PI_2_tightest :
  is_tightest (fun r => r = PI / 2) Interval.FRAC_PI_2 /\
  is_tightest (fun r => r = PI / 2) (itv DecInterval.FRAC_PI_2) /\
  strongest0 (dec DecInterval.FRAC_PI_2) (PI / 2) (itv DecInterval.FRAC_PI_2).
Proof.
  assert (H : is_tightest (fun r => r = PI / 2) Interval.FRAC_PI_2).
  { (* As for [PI_tightest], the [const_interval] of the bounds of
       [Interval.FRAC_PI_2] computes to [Interval.FRAC_PI_2]. *)
    destruct pt_FRAC_PI_2_facts as (F0 & F1 & Hs).
    apply (const_tightest _ _ (PI / 2) F0 F1 Hs).
    rewrite pb_frac_lo, pb_frac_hi. pose proof PI_bounds. lra. }
  (* [DecInterval.FRAC_PI_2] is [new_unchecked Interval.FRAC_PI_2 Com]. *)
  split; [exact H | split; [exact H |]].
  apply const_strongest0; vm_compute; reflexivity.
Qed.

Theorem FRAC_PI_3_tightest :
  is_tightest (fun r => r = PI / 3) Interval.FRAC_PI_3 /\
  is_tightest (fun r => r = PI / 3) (itv DecInterval.FRAC_PI_3) /\
  strongest0 (dec DecInterval.FRAC_PI_3) (PI / 3) (itv DecInterval.FRAC_PI_3).
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
  split; [exact H | split; [exact H |]].
  apply const_strongest0; vm_compute; reflexivity.
Qed.

Theorem FRAC_PI_4_tightest :
  is_tightest (fun r => r = PI / 4) Interval.FRAC_PI_4 /\
  is_tightest (fun r => r = PI / 4) (itv DecInterval.FRAC_PI_4) /\
  strongest0 (dec DecInterval.FRAC_PI_4) (PI / 4) (itv DecInterval.FRAC_PI_4).
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
  split; [exact H | split; [exact H |]].
  apply const_strongest0; vm_compute; reflexivity.
Qed.

Theorem FRAC_PI_6_tightest :
  is_tightest (fun r => r = PI / 6) Interval.FRAC_PI_6 /\
  is_tightest (fun r => r = PI / 6) (itv DecInterval.FRAC_PI_6) /\
  strongest0 (dec DecInterval.FRAC_PI_6) (PI / 6) (itv DecInterval.FRAC_PI_6).
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
  split; [exact H | split; [exact H |]].
  apply const_strongest0; vm_compute; reflexivity.
Qed.

Theorem FRAC_PI_8_tightest :
  is_tightest (fun r => r = PI / 8) Interval.FRAC_PI_8 /\
  is_tightest (fun r => r = PI / 8) (itv DecInterval.FRAC_PI_8) /\
  strongest0 (dec DecInterval.FRAC_PI_8) (PI / 8) (itv DecInterval.FRAC_PI_8).
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
  split; [exact H | split; [exact H |]].
  apply const_strongest0; vm_compute; reflexivity.
Qed.
