(** * [Interval::PI] and [Interval::FRAC_PI_2] enclose π and π/2

    [Interval::cos] divides its argument by [Interval::PI], and
    [Interval::sin] and [Interval::tan] by [Interval::FRAC_PI_2]. The
    theorems about them need only that each is an interval [[lo, hi]] of
    finite floats with [1 <= lo < c < hi] for [c] = π or π/2
    ([trig_const]). The bounds of π come from Machin's formula
    [PI / 4 = 2 * atan (/3) + atan (/7)] and the alternating series of
    [atan] ([PI_2_3_7_ineq] in Stdlib's [Machin.v]). *)

From Stdlib Require Import ZArith Reals Lra Lia QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788.

Open Scope R_scope.

(** [C] is an interval [[lo, hi]] of finite floats with [1 <= lo < c < hi]. *)
Definition trig_const (C : Interval) (c : R) : Prop :=
  valid C /\ Interval.is_empty C = false /\
  is_finite (Interval.inf_raw C) = true /\ is_finite (Interval.sup_raw C) = true /\
  1 <= B2R (Interval.inf_raw C) /\ B2R (Interval.inf_raw C) < c /\
  c < B2R (Interval.sup_raw C).

(** ** The partial sums of Machin's series, in [Q]

    [PI_2_3_7_ineq] bounds [PI / 4] by partial sums of
    [tg_alt PI_2_3_7_tg], whose terms are real powers and quotients. Their
    copies below are in [Q], where [vm_compute] decides the comparisons
    with the bounds of [Interval::PI], and [Q2R] maps them back term by
    term. *)

Fixpoint pb_powQ (q : Q) (n : nat) : Q :=
  match n with O => 1%Q | S n => (q * pb_powQ q n)%Q end.

(** [PI_2_3_7_tg n = 2 * Ratan_seq (/3) n + Ratan_seq (/7) n], with
    [Ratan_seq x n = x ^ (2 * n + 1) / INR (2 * n + 1)]. The divisor
    [2 * n + 1] is [Pos.of_succ_nat (2 * n)], so it is visibly nonzero. *)
Definition pb_tgQ (n : nat) : Q :=
  (2 * (pb_powQ (1 # 3) (2 * n + 1) * (1 # Pos.of_succ_nat (2 * n))) +
   pb_powQ (1 # 7) (2 * n + 1) * (1 # Pos.of_succ_nat (2 * n)))%Q.

(** [tg_alt Un n = (-1) ^ n * Un n]. *)
Definition pb_altQ (n : nat) : Q := (pb_powQ (-1 # 1) n * pb_tgQ n)%Q.

(** [sum_f_R0] in [Q]. *)
Fixpoint pb_sumQ (f : nat -> Q) (n : nat) : Q :=
  match n with O => f O | S n => (pb_sumQ f n + f (S n))%Q end.

Lemma pb_powQ_R : forall q n, Q2R (pb_powQ q n) = Q2R q ^ n.
Proof.
  intros q n; induction n as [|n IH]; simpl pb_powQ.
  - unfold Q2R; simpl; lra.
  - rewrite Q2R_mult, IH; reflexivity.
Qed.

Lemma pb_inv_R : forall p, Q2R (1 # p) = / IZR (Zpos p).
Proof. intros p; unfold Q2R; simpl Qnum; simpl Qden; lra. Qed.

Lemma pb_INR_odd : forall n, INR (2 * n + 1) = IZR (Zpos (Pos.of_succ_nat (2 * n))).
Proof.
  intros n; rewrite INR_IZR_INZ, Zpos_P_of_succ_nat; f_equal; lia.
Qed.

Lemma pb_tgQ_R : forall n, Q2R (pb_tgQ n) = PI_2_3_7_tg n.
Proof.
  intros n; unfold pb_tgQ, PI_2_3_7_tg, Ratan_seq.
  rewrite Q2R_plus, !Q2R_mult, !pb_powQ_R, !pb_inv_R, <- pb_INR_odd.
  replace (Q2R 2) with 2 by (unfold Q2R; simpl; lra).
  unfold Rdiv; ring.
Qed.

Lemma pb_altQ_R : forall n, Q2R (pb_altQ n) = tg_alt PI_2_3_7_tg n.
Proof.
  intros n; unfold pb_altQ, tg_alt.
  rewrite Q2R_mult, pb_powQ_R, pb_tgQ_R.
  replace (Q2R (-1 # 1)) with (-1) by (unfold Q2R; simpl; lra).
  reflexivity.
Qed.

Lemma pb_sumQ_R : forall n, Q2R (pb_sumQ pb_altQ n) = sum_f_R0 (tg_alt PI_2_3_7_tg) n.
Proof.
  intros n; induction n as [|n IH]; simpl pb_sumQ; simpl sum_f_R0.
  - apply pb_altQ_R.
  - rewrite Q2R_plus, IH, pb_altQ_R; reflexivity.
Qed.

(** ** The bounds of [Interval::PI] as rationals

    They are [7074237752028440 * 2^-51] and [7074237752028441 * 2^-51].
    [vm_compute] decodes the bit patterns, and [cbn] turns [bpow radix2
    (-51)] into [/ IZR (Z.pow_pos 2 51)], which [lra] evaluates. *)

Lemma pb_lo_R :
  B2R (Interval.inf_raw Interval.PI) = Q2R (7074237752028440 # 2251799813685248).
Proof.
  let v := eval vm_compute in (Interval.inf_raw Interval.PI) in
  change (Interval.inf_raw Interval.PI) with v.
  unfold Q2R, B2R, F2R; cbn [Fnum Fexp bpow radix_val radix2 cond_Zopp Qnum Qden].
  lra.
Qed.

Lemma pb_hi_R :
  B2R (Interval.sup_raw Interval.PI) = Q2R (7074237752028441 # 2251799813685248).
Proof.
  let v := eval vm_compute in (Interval.sup_raw Interval.PI) in
  change (Interval.sup_raw Interval.PI) with v.
  unfold Q2R, B2R, F2R; cbn [Fnum Fexp bpow radix_val radix2 cond_Zopp Qnum Qden].
  lra.
Qed.

(** The partial sums for [N = 9] in [PI_2_3_7_ineq], times 4. Each is
    within 4 times its first omitted term of π, at most
    [4 * PI_2_3_7_tg 19 < 10^-19], while the bounds of [Interval::PI] are
    more than [10^-16] from π. *)

Lemma pb_sum_lo :
  (7074237752028440 # 2251799813685248 < 4 * pb_sumQ pb_altQ 19)%Q.
Proof. vm_compute; reflexivity. Qed.

Lemma pb_sum_hi :
  (4 * pb_sumQ pb_altQ 18 < 7074237752028441 # 2251799813685248)%Q.
Proof. vm_compute; reflexivity. Qed.

(** The bounds of [Interval::PI] are below and above π. *)
Lemma PI_bounds :
  B2R (Interval.inf_raw Interval.PI) < PI < B2R (Interval.sup_raw Interval.PI).
Proof.
  destruct (PI_2_3_7_ineq 9) as [H1 H2].
  change (S (2 * 9)) with 19%nat in H1; change (2 * 9)%nat with 18%nat in H2.
  rewrite <- pb_sumQ_R in H1, H2.
  pose proof (Qlt_Rlt _ _ pb_sum_lo) as H3; pose proof (Qlt_Rlt _ _ pb_sum_hi) as H4.
  rewrite Q2R_mult in H3, H4.
  replace (Q2R 4) with 4 in H3, H4 by (unfold Q2R; simpl; lra).
  rewrite pb_lo_R, pb_hi_R; lra.
Qed.

Lemma PI_const : trig_const Interval.PI PI.
Proof.
  destruct PI_bounds as [H1 H2].
  unfold trig_const; split; [|split; [|split; [|split; [|split; [|split]]]]].
  - unfold valid; vm_compute; right; split; [reflexivity | split; discriminate].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - rewrite pb_lo_R; unfold Q2R; cbn [Qnum Qden]; lra.
  - exact H1.
  - exact H2.
Qed.

(** The bounds of [Interval::FRAC_PI_2] are those of [Interval::PI]
    halved: the same significands at the exponent [-52]. *)

Lemma pb_frac_lo :
  B2R (Interval.inf_raw Interval.FRAC_PI_2) = B2R (Interval.inf_raw Interval.PI) / 2.
Proof.
  let v := eval vm_compute in (Interval.inf_raw Interval.FRAC_PI_2) in
  change (Interval.inf_raw Interval.FRAC_PI_2) with v.
  rewrite pb_lo_R.
  unfold Q2R, B2R, F2R; cbn [Fnum Fexp bpow radix_val radix2 cond_Zopp Qnum Qden].
  lra.
Qed.

Lemma pb_frac_hi :
  B2R (Interval.sup_raw Interval.FRAC_PI_2) = B2R (Interval.sup_raw Interval.PI) / 2.
Proof.
  let v := eval vm_compute in (Interval.sup_raw Interval.FRAC_PI_2) in
  change (Interval.sup_raw Interval.FRAC_PI_2) with v.
  rewrite pb_hi_R.
  unfold Q2R, B2R, F2R; cbn [Fnum Fexp bpow radix_val radix2 cond_Zopp Qnum Qden].
  lra.
Qed.

Lemma FRAC_PI_2_const : trig_const Interval.FRAC_PI_2 (PI / 2).
Proof.
  destruct PI_bounds as [H1 H2].
  unfold trig_const; split; [|split; [|split; [|split; [|split; [|split]]]]].
  - unfold valid; vm_compute; right; split; [reflexivity | split; discriminate].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - rewrite pb_frac_lo, pb_lo_R; unfold Q2R; cbn [Qnum Qden]; lra.
  - rewrite pb_frac_lo; lra.
  - rewrite pb_frac_hi; lra.
Qed.
