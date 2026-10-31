(** * [Interval::LOG10_2], [LOG10_E], [LOG2_10] and [LOG2_E] are the tightest intervals around their values

    [Rlog b r] is [ln r / ln b] ([Elementary.v]), and [ln (exp 1) = 1], so
    the values are [ln 2 / ln 10], [1 / ln 10], [ln 10 / ln 2] and
    [1 / ln 2]. The rational bounds of [ln 2] and [ln 10] in [ConstLn.v]
    ([LN_2_Q] and [LN_10_Q]), all positive, bound these quotients by
    quotients of rationals, which [vm_compute] compares with the bounds of
    each constant. Each theorem also covers the [DecInterval] constant that
    [def_com!] makes from the [Interval] one, whose interval is the
    same. *)

From Stdlib Require Import ZArith Reals Lra QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary ConstTight ConstLn.

Open Scope R_scope.

(** A positive rational is positive as a real ([Q2R_pos]) and is not 0
    ([Q_nonzero], the side condition of [Q2R_div] and [Q2R_inv]). *)
Lemma Q2R_pos : forall q : Q, (0 < q)%Q -> 0 < Q2R q.
Proof.
  intros q Hq. apply Qlt_Rlt in Hq.
  replace (Q2R 0) with 0 in Hq by (unfold Q2R; simpl; ring).
  exact Hq.
Qed.

Lemma Q_nonzero : forall q : Q, (0 < q)%Q -> ~ (q == 0)%Q.
Proof.
  intros q Hq. apply Qnot_eq_sym, Qlt_not_eq, Hq.
Qed.

(** Bounds of [/ y] and [x / y] from bounds of positive [x] and [y]:
    [/] decreases on the positive reals, and [*] increases in each
    nonnegative argument. *)
Lemma inv_bounds :
  forall b1 b2 y : R, 0 < b1 -> b1 <= y <= b2 -> / b2 <= / y <= / b1.
Proof.
  intros b1 b2 y Hb [Hy1 Hy2].
  split; apply Rinv_le_contravar; lra.
Qed.

Lemma div_bounds :
  forall a1 a2 b1 b2 x y : R,
  0 < a1 -> 0 < b1 -> a1 <= x <= a2 -> b1 <= y <= b2 ->
  a1 / b2 <= x / y <= a2 / b1.
Proof.
  intros a1 a2 b1 b2 x y Ha Hb Hx Hy.
  pose proof (inv_bounds b1 b2 y Hb Hy) as Hi.
  assert (0 < / b2) by (apply Rinv_0_lt_compat; lra).
  unfold Rdiv; split; apply Rmult_le_compat; lra.
Qed.

(** The rational bounds of [ln 2] and [ln 10] as positive reals. *)
Lemma LN_Q_pos :
  0 < Q2R ln2_lo /\ 0 < Q2R ln10_lo.
Proof.
  split; apply Q2R_pos; vm_compute; reflexivity.
Qed.

Theorem LOG10_2_tightest :
  is_tightest (fun r => r = Rlog10 2) Interval.LOG10_2 /\
  is_tightest (fun r => r = Rlog10 2) (itv DecInterval.LOG10_2).
Proof.
  assert (H : is_tightest (fun r => r = Rlog10 2) Interval.LOG10_2).
  { apply (const_tightest_Q _ _ _ (ln2_lo / ln10_hi) (ln2_hi / ln10_lo)).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply B2SF_inj; vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - unfold Rlog10, Rlog.
      rewrite !Q2R_div by (apply Q_nonzero; vm_compute; reflexivity).
      pose proof LN_2_Q; pose proof LN_10_Q; pose proof LN_Q_pos.
      apply div_bounds; lra. }
  split; exact H.
Qed.

Theorem LOG10_E_tightest :
  is_tightest (fun r => r = Rlog10 (exp 1)) Interval.LOG10_E /\
  is_tightest (fun r => r = Rlog10 (exp 1)) (itv DecInterval.LOG10_E).
Proof.
  assert (H : is_tightest (fun r => r = Rlog10 (exp 1)) Interval.LOG10_E).
  { apply (const_tightest_Q _ _ _ (/ ln10_hi) (/ ln10_lo)).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply B2SF_inj; vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - (* [ln (exp 1) / ln b = / ln b]. *)
      unfold Rlog10, Rlog. rewrite ln_exp, Rdiv_1_l.
      rewrite !Q2R_inv by (apply Q_nonzero; vm_compute; reflexivity).
      pose proof LN_2_Q; pose proof LN_10_Q; pose proof LN_Q_pos.
      apply inv_bounds; lra. }
  split; exact H.
Qed.

Theorem LOG2_10_tightest :
  is_tightest (fun r => r = Rlog2 10) Interval.LOG2_10 /\
  is_tightest (fun r => r = Rlog2 10) (itv DecInterval.LOG2_10).
Proof.
  assert (H : is_tightest (fun r => r = Rlog2 10) Interval.LOG2_10).
  { apply (const_tightest_Q _ _ _ (ln10_lo / ln2_hi) (ln10_hi / ln2_lo)).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply B2SF_inj; vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - unfold Rlog2, Rlog.
      rewrite !Q2R_div by (apply Q_nonzero; vm_compute; reflexivity).
      pose proof LN_2_Q; pose proof LN_10_Q; pose proof LN_Q_pos.
      apply div_bounds; lra. }
  split; exact H.
Qed.

Theorem LOG2_E_tightest :
  is_tightest (fun r => r = Rlog2 (exp 1)) Interval.LOG2_E /\
  is_tightest (fun r => r = Rlog2 (exp 1)) (itv DecInterval.LOG2_E).
Proof.
  assert (H : is_tightest (fun r => r = Rlog2 (exp 1)) Interval.LOG2_E).
  { apply (const_tightest_Q _ _ _ (/ ln2_hi) (/ ln2_lo)).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply B2SF_inj; vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - (* [ln (exp 1) / ln b = / ln b]. *)
      unfold Rlog2, Rlog. rewrite ln_exp, Rdiv_1_l.
      rewrite !Q2R_inv by (apply Q_nonzero; vm_compute; reflexivity).
      pose proof LN_2_Q; pose proof LN_10_Q; pose proof LN_Q_pos.
      apply inv_bounds; lra. }
  split; exact H.
Qed.
