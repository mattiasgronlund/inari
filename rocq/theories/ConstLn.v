(** * [Interval::E], [LN_2] and [LN_10] are the tightest intervals around their values

    [exp_Q_bounds] in [ExpSeries.v] bounds [exp q] for a rational
    [0 <= q <= 1] by rationals, which gives [e = exp 1] directly. For a
    rational [q], [q < ln y] if [exp q < y], and [ln y < q] if
    [0 < y < exp q], as [ln] increases and [ln (exp q) = q]. That bounds
    [ln 2] by two rationals [10^-24] apart
    ([LN_2_Q]). [ln 10] is above 1, so [LN_10_Q] uses
    [exp q = (exp (q / 3))^3] instead. The bounds of [Interval::LN_2] and
    [Interval::LN_10] lie strictly outside these rationals, which
    [vm_compute] checks. Each theorem also covers the [DecInterval]
    constant that [def_com!] makes from the [Interval] one, whose interval
    is the same. *)

From Stdlib Require Import ZArith Reals Lra QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 ConstTight ExpSeries.

Open Scope R_scope.

(** [ln 2] and [ln 10] to 24 decimals, below and above. *)
Definition ln2_lo : Q := 693147180559945309417232 # 1000000000000000000000000.
Definition ln2_hi : Q := 693147180559945309417233 # 1000000000000000000000000.
Definition ln10_lo : Q := 2302585092994045684017991 # 1000000000000000000000000.
Definition ln10_hi : Q := 2302585092994045684017992 # 1000000000000000000000000.

(** [q < ln y] follows from [exp q < y], and [ln y < q] from
    [0 < y < exp q], as [ln] increases and [ln (exp q) = q]. Stdlib's [ln]
    is 0 at 0 and below, so the second needs [0 < y]. *)
Lemma lt_ln_of_exp_lt : forall q y, exp q < y -> q < ln y.
Proof.
  intros q y H. rewrite <- (ln_exp q).
  apply ln_increasing; [apply exp_pos | exact H].
Qed.

Lemma ln_lt_of_lt_exp : forall q y, 0 < y -> y < exp q -> ln y < q.
Proof.
  intros q y Hy H. rewrite <- (ln_exp q).
  apply ln_increasing; [exact Hy | exact H].
Qed.

(** The cube increases on the nonnegative reals. *)
Lemma cube_le : forall a b, 0 <= a -> a <= b -> a * a * a <= b * b * b.
Proof.
  intros a b Ha Hab.
  assert (Hsq : a * a <= b * b) by (apply Rmult_le_compat; lra).
  apply Rmult_le_compat; [apply Rmult_le_pos; lra | lra | exact Hsq | exact Hab].
Qed.

(** [Q2R] of the small rationals that the proofs compare with. *)
Lemma Q2R_0 : Q2R 0 = 0.
Proof. unfold Q2R; simpl; lra. Qed.

Lemma Q2R_1 : Q2R 1 = 1.
Proof. unfold Q2R; simpl; lra. Qed.

Lemma Q2R_2 : Q2R 2 = 2.
Proof. unfold Q2R; simpl; lra. Qed.

Lemma Q2R_10 : Q2R 10 = 10.
Proof. unfold Q2R; simpl; lra. Qed.

Lemma Q2R_1_3 : Q2R (1 # 3) = / 3.
Proof. unfold Q2R; simpl; lra. Qed.

Lemma LN_2_Q : Q2R ln2_lo < ln 2 < Q2R ln2_hi.
Proof.
  (* [exp ln2_lo <= exp_hiQ ln2_lo 13 < 2 < exp_loQ ln2_hi 13 <= exp ln2_hi]. *)
  assert (Hlo : (exp_hiQ ln2_lo 13 < 2)%Q) by (vm_compute; reflexivity).
  assert (Hhi : (2 < exp_loQ ln2_hi 13)%Q) by (vm_compute; reflexivity).
  apply Qlt_Rlt in Hlo, Hhi. rewrite Q2R_2 in Hlo, Hhi.
  destruct (exp_Q_bounds ln2_lo 13) as [_ Elo].
  { apply Qle_bool_imp_le; vm_compute; reflexivity. }
  { apply Qle_bool_imp_le; vm_compute; reflexivity. }
  { vm_compute; reflexivity. }
  destruct (exp_Q_bounds ln2_hi 13) as [Ehi _].
  { apply Qle_bool_imp_le; vm_compute; reflexivity. }
  { apply Qle_bool_imp_le; vm_compute; reflexivity. }
  { vm_compute; reflexivity. }
  split.
  - apply lt_ln_of_exp_lt; lra.
  - apply ln_lt_of_lt_exp; lra.
Qed.

Lemma LN_10_Q : Q2R ln10_lo < ln 10 < Q2R ln10_hi.
Proof.
  (* [ln10_lo] and [ln10_hi] are above 1, outside the domain of
     [exp_Q_bounds], so bound [exp] at a third of them and cube:
     [exp (3 * y) = exp y * exp y * exp y]. *)
  set (y := (ln10_lo * (1 # 3))%Q).
  set (z := (ln10_hi * (1 # 3))%Q).
  assert (Hy : Q2R ln10_lo = Q2R y + Q2R y + Q2R y).
  { unfold y. rewrite Q2R_mult, Q2R_1_3. lra. }
  assert (Hz : Q2R ln10_hi = Q2R z + Q2R z + Q2R z).
  { unfold z. rewrite Q2R_mult, Q2R_1_3. lra. }
  assert (Hlo : (exp_hiQ y 13 * exp_hiQ y 13 * exp_hiQ y 13 < 10)%Q)
    by (vm_compute; reflexivity).
  assert (Hhi : (10 < exp_loQ z 13 * exp_loQ z 13 * exp_loQ z 13)%Q)
    by (vm_compute; reflexivity).
  (* [exp_loQ z 13] is positive, so its cube is below [exp z]'s. *)
  assert (Hpos : (0 <= exp_loQ z 13)%Q)
    by (apply Qle_bool_imp_le; vm_compute; reflexivity).
  apply Qlt_Rlt in Hlo, Hhi. apply Qle_Rle in Hpos.
  rewrite !Q2R_mult, Q2R_10 in Hlo, Hhi. rewrite Q2R_0 in Hpos.
  destruct (exp_Q_bounds y 13) as [_ Ey].
  { apply Qle_bool_imp_le; vm_compute; reflexivity. }
  { apply Qle_bool_imp_le; vm_compute; reflexivity. }
  { vm_compute; reflexivity. }
  destruct (exp_Q_bounds z 13) as [Ez _].
  { apply Qle_bool_imp_le; vm_compute; reflexivity. }
  { apply Qle_bool_imp_le; vm_compute; reflexivity. }
  { vm_compute; reflexivity. }
  pose proof (cube_le _ _ (Rlt_le _ _ (exp_pos (Q2R y))) Ey) as Cy.
  pose proof (cube_le _ _ Hpos Ez) as Cz.
  split.
  - apply lt_ln_of_exp_lt. rewrite Hy, !exp_plus. lra.
  - apply ln_lt_of_lt_exp; [lra |]. rewrite Hz, !exp_plus. lra.
Qed.

Theorem E_tightest :
  is_tightest (fun r => r = exp 1) Interval.E /\
  is_tightest (fun r => r = exp 1) (itv DecInterval.E).
Proof.
  destruct (exp_Q_bounds 1 13) as [El Eu].
  { apply Qle_bool_imp_le; vm_compute; reflexivity. }
  { apply Qle_bool_imp_le; vm_compute; reflexivity. }
  { vm_compute; reflexivity. }
  rewrite Q2R_1 in El, Eu.
  assert (H : is_tightest (fun r => r = exp 1) Interval.E).
  { apply (const_tightest_Q _ _ _ (exp_loQ 1 13) (exp_hiQ 1 13)).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply B2SF_inj; vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - split; assumption. }
  (* [DecInterval.E] is [Interval.E] decorated [com]. *)
  split; exact H.
Qed.

Theorem LN_2_tightest :
  is_tightest (fun r => r = ln 2) Interval.LN_2 /\
  is_tightest (fun r => r = ln 2) (itv DecInterval.LN_2).
Proof.
  assert (H : is_tightest (fun r => r = ln 2) Interval.LN_2).
  { apply (const_tightest_Q _ _ _ ln2_lo ln2_hi).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply B2SF_inj; vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - pose proof LN_2_Q; lra. }
  split; exact H.
Qed.

Theorem LN_10_tightest :
  is_tightest (fun r => r = ln 10) Interval.LN_10 /\
  is_tightest (fun r => r = ln 10) (itv DecInterval.LN_10).
Proof.
  assert (H : is_tightest (fun r => r = ln 10) Interval.LN_10).
  { apply (const_tightest_Q _ _ _ ln10_lo ln10_hi).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply B2SF_inj; vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - pose proof LN_10_Q; lra. }
  split; exact H.
Qed.
