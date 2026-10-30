(** * The point function [pow] on the reals

    Facts about [Rpow] of [Elementary.v] that the proofs of [Pow.v] use:
    its values at a base of 0 or 1 and at an exponent of 0, its sign, its
    monotonicity in the base and in the exponent, its limits as the base
    or the exponent grows without bound or the base tends to 0, and its
    continuity at each point of its domain relative to the domain,
    including the positive [y] axis. *)

From Stdlib Require Import ZArith Reals Lra.
From Inari Require Import Ieee1788 Elementary.

Open Scope R_scope.

(** ** Helpers: [exp] and [ln] *)

Lemma pr_exp_le : forall x y, x <= y -> exp x <= exp y.
Proof.
intros x y H. destruct (Rle_lt_or_eq_dec x y H) as [Hlt | ->].
- left. apply exp_increasing. exact Hlt.
- apply Rle_refl.
Qed.

Lemma pr_ln_le : forall x y, 0 < x -> x <= y -> ln x <= ln y.
Proof.
intros x y Hx H. destruct (Rle_lt_or_eq_dec x y H) as [Hlt | ->].
- left. apply ln_increasing; assumption.
- apply Rle_refl.
Qed.

Lemma pr_ln_ge0 : forall r, 1 <= r -> 0 <= ln r.
Proof. intros r H. rewrite <- ln_1. apply pr_ln_le; lra. Qed.

Lemma pr_ln_le0 : forall r, 0 < r <= 1 -> ln r <= 0.
Proof. intros r H. rewrite <- ln_1. apply pr_ln_le; lra. Qed.

Lemma pr_ln_gt0 : forall r, 1 < r -> 0 < ln r.
Proof. intros r H. rewrite <- ln_1. apply ln_increasing; lra. Qed.

Lemma pr_ln_lt0 : forall r, 0 < r < 1 -> ln r < 0.
Proof. intros r H. rewrite <- ln_1. apply ln_increasing; lra. Qed.

(** [exp x < eps] as soon as [x < ln eps]. *)
Lemma pr_exp_lt_eps : forall x eps, 0 < eps -> x < ln eps -> exp x < eps.
Proof.
intros x eps He H. apply Rlt_le_trans with (exp (ln eps)).
- apply exp_increasing. exact H.
- rewrite exp_ln by exact He. apply Rle_refl.
Qed.

(** [M <= exp x] as soon as [ln (Rmax M 1) <= x]; [Rmax M 1] is above 0,
    so that its [ln] is meaningful. *)
Lemma pr_exp_ge_M : forall x M, ln (Rmax M 1) <= x -> M <= exp x.
Proof.
intros x M H. assert (HK : 0 < Rmax M 1) by (pose proof (Rmax_r M 1); lra).
apply Rle_trans with (Rmax M 1); [apply Rmax_l|].
rewrite <- (exp_ln (Rmax M 1)) by exact HK. apply pr_exp_le. exact H.
Qed.

(** The epsilon-delta form of [continuity_pt]. *)
Lemma pr_cont_eps :
  forall f x0, continuity_pt f x0 ->
  forall eps, 0 < eps -> exists alp, 0 < alp /\
    forall x, Rabs (x - x0) < alp -> Rabs (f x - f x0) < eps.
Proof.
intros f x0 Hc eps Heps. destruct (Hc eps Heps) as (alp & Halp & H).
exists alp. split; [exact Halp|]. intros x Hx.
destruct (Req_dec x x0) as [-> | Hne].
- unfold Rminus. rewrite Rplus_opp_r, Rabs_R0. exact Heps.
- apply (H x). split; [split; [exact I | intro E; apply Hne; symmetry; exact E] | exact Hx].
Qed.

Lemma pr_exp_cont : forall y, continuity_pt exp y.
Proof. intros y. apply derivable_continuous_pt, derivable_pt_exp. Qed.

Lemma pr_ln_cont : forall r, 0 < r -> continuity_pt ln r.
Proof.
intros r Hr. apply derivable_continuous_pt. exists (/ r).
apply derivable_pt_lim_ln. exact Hr.
Qed.

Lemma Rpow_pos : forall r t, 0 < r -> Rpow r t = Rpower r t.
Proof.
intros r t Hr. unfold Rpow. destruct (Rle_dec r 0); [lra | reflexivity].
Qed.

Lemma Rpow_0_l : forall t, Rpow 0 t = 0.
Proof.
intros t. unfold Rpow. destruct (Rle_dec 0 0); [reflexivity | lra].
Qed.

Lemma Rpow_gt_0 : forall r t, 0 < r -> 0 < Rpow r t.
Proof.
intros r t Hr. rewrite Rpow_pos by exact Hr. apply exp_pos.
Qed.

Lemma Rpow_ge_0 : forall r t, 0 <= r -> 0 <= Rpow r t.
Proof.
intros r t Hr. unfold Rpow. destruct (Rle_dec r 0); [lra | left; apply exp_pos].
Qed.

Lemma Rpow_1_l : forall t, Rpow 1 t = 1.
Proof.
intros t. rewrite Rpow_pos by lra. unfold Rpower.
rewrite ln_1, Rmult_0_r. apply exp_0.
Qed.

Lemma Rpow_0_r : forall r, 0 < r -> Rpow r 0 = 1.
Proof.
intros r Hr. rewrite Rpow_pos by exact Hr. apply Rpower_O. exact Hr.
Qed.

(** ** Monotonicity *)

(** Increasing in the base for an exponent above 0, from a base of 0. *)
Lemma Rpow_le_base_pos :
  forall r r' t, 0 <= r <= r' -> 0 < t -> Rpow r t <= Rpow r' t.
Proof.
intros r r' t [H0 H1] Ht. destruct (Rle_lt_or_eq_dec 0 r H0) as [Hr | <-].
- rewrite !Rpow_pos by lra. apply Rle_Rpower_l; lra.
- rewrite Rpow_0_l. apply Rpow_ge_0. exact H1.
Qed.

(** Decreasing in the base above 0 for an exponent at most 0. *)
Lemma Rpow_le_base_neg :
  forall r r' t, 0 < r <= r' -> t <= 0 -> Rpow r' t <= Rpow r t.
Proof.
intros r r' t [H0 H1] Ht. rewrite !Rpow_pos by lra. unfold Rpower.
apply pr_exp_le. pose proof (pr_ln_le r r' H0 H1). nra.
Qed.

(** Increasing in the exponent for a base at least 1. *)
Lemma Rpow_le_exp_ge1 :
  forall r t t', 1 <= r -> t <= t' -> Rpow r t <= Rpow r t'.
Proof.
intros r t t' Hr Ht. rewrite !Rpow_pos by lra. unfold Rpower.
apply pr_exp_le. pose proof (pr_ln_ge0 r Hr). nra.
Qed.

(** Decreasing in the exponent for a base above 0 and at most 1. *)
Lemma Rpow_le_exp_le1 :
  forall r t t', 0 < r <= 1 -> t <= t' -> Rpow r t' <= Rpow r t.
Proof.
intros r t t' Hr Ht. rewrite !Rpow_pos by lra. unfold Rpower.
apply pr_exp_le. pose proof (pr_ln_le0 r Hr). nra.
Qed.

(** ** Limits *)

(** As the base grows, toward 0 for an exponent below 0, and without
    bound for one above 0. *)
Lemma Rpow_base_large_neg :
  forall t eps, t < 0 -> 0 < eps ->
  exists r0, 0 < r0 /\ forall r, r0 <= r -> Rpow r t < eps.
Proof.
intros t eps Ht Heps. exists (exp (ln eps / t + 1)).
split; [apply exp_pos|]. intros r Hr.
pose proof (exp_pos (ln eps / t + 1)) as Hp.
rewrite Rpow_pos by lra. unfold Rpower. apply pr_exp_lt_eps; [exact Heps|].
assert (H1 : ln eps / t + 1 <= ln r)
  by (rewrite <- (ln_exp (ln eps / t + 1)); apply pr_ln_le; lra).
assert (H2 : t * (ln eps / t) = ln eps) by (field; lra).
set (q := ln eps / t) in *. nra.
Qed.

Lemma Rpow_base_large_pos :
  forall t M, 0 < t -> exists r0, 0 < r0 /\ forall r, r0 <= r -> M <= Rpow r t.
Proof.
intros t M Ht. exists (exp (ln (Rmax M 1) / t)).
split; [apply exp_pos|]. intros r Hr.
pose proof (exp_pos (ln (Rmax M 1) / t)) as Hp.
rewrite Rpow_pos by lra. unfold Rpower. apply pr_exp_ge_M.
assert (H1 : ln (Rmax M 1) / t <= ln r)
  by (rewrite <- (ln_exp (ln (Rmax M 1) / t)); apply pr_ln_le; lra).
assert (H2 : t * (ln (Rmax M 1) / t) = ln (Rmax M 1)) by (field; lra).
set (q := ln (Rmax M 1) / t) in *. nra.
Qed.

(** As the base tends to 0 from above, without bound for an exponent below
    0. *)
Lemma Rpow_base_small_neg :
  forall t M, t < 0 -> exists r0, 0 < r0 /\ forall r, 0 < r <= r0 -> M <= Rpow r t.
Proof.
intros t M Ht. exists (exp (ln (Rmax M 1) / t)).
split; [apply exp_pos|]. intros r [Hr0 Hr].
rewrite Rpow_pos by lra. unfold Rpower. apply pr_exp_ge_M.
assert (H1 : ln r <= ln (Rmax M 1) / t)
  by (rewrite <- (ln_exp (ln (Rmax M 1) / t)); apply pr_ln_le; lra).
assert (H2 : t * (ln (Rmax M 1) / t) = ln (Rmax M 1)) by (field; lra).
set (q := ln (Rmax M 1) / t) in *. nra.
Qed.

(** As the exponent grows or falls without bound, for a base above 1 and
    for one between 0 and 1. *)
Lemma Rpow_exp_large_gt1 :
  forall r M, 1 < r -> exists t0, forall t, t0 <= t -> M <= Rpow r t.
Proof.
intros r M Hr. pose proof (pr_ln_gt0 r Hr) as Hl.
exists (ln (Rmax M 1) / ln r). intros t Ht.
rewrite Rpow_pos by lra. unfold Rpower. apply pr_exp_ge_M.
assert (H2 : ln (Rmax M 1) / ln r * ln r = ln (Rmax M 1)) by (field; lra).
set (q := ln (Rmax M 1) / ln r) in *. nra.
Qed.

Lemma Rpow_exp_small_gt1 :
  forall r eps, 1 < r -> 0 < eps -> exists t0, forall t, t <= t0 -> Rpow r t < eps.
Proof.
intros r eps Hr Heps. pose proof (pr_ln_gt0 r Hr) as Hl.
exists (ln eps / ln r - 1). intros t Ht.
rewrite Rpow_pos by lra. unfold Rpower. apply pr_exp_lt_eps; [exact Heps|].
assert (H2 : ln eps / ln r * ln r = ln eps) by (field; lra).
set (q := ln eps / ln r) in *. nra.
Qed.

Lemma Rpow_exp_large_lt1 :
  forall r eps, 0 < r < 1 -> 0 < eps -> exists t0, forall t, t0 <= t -> Rpow r t < eps.
Proof.
intros r eps Hr Heps. pose proof (pr_ln_lt0 r Hr) as Hl.
exists (ln eps / ln r + 1). intros t Ht.
rewrite Rpow_pos by lra. unfold Rpower. apply pr_exp_lt_eps; [exact Heps|].
assert (H2 : ln eps / ln r * ln r = ln eps) by (field; lra).
set (q := ln eps / ln r) in *. nra.
Qed.

Lemma Rpow_exp_small_lt1 :
  forall r M, 0 < r < 1 -> exists t0, forall t, t <= t0 -> M <= Rpow r t.
Proof.
intros r M Hr. pose proof (pr_ln_lt0 r Hr) as Hl.
exists (ln (Rmax M 1) / ln r). intros t Ht.
rewrite Rpow_pos by lra. unfold Rpower. apply pr_exp_ge_M.
assert (H2 : ln (Rmax M 1) / ln r * ln r = ln (Rmax M 1)) by (field; lra).
set (q := ln (Rmax M 1) / ln r) in *. nra.
Qed.

(** ** Continuity relative to the domain *)

Lemma Rpow_continuous :
  forall r t, pow_dom r t -> continue_in2_set Rpow pow_dom r t.
Proof.
intros r t Hd eps Heps. destruct Hd as [Hr | [-> Ht]].
- (* At r > 0: Rpow is [exp (t * ln r)] near (r, t), as delta <= r keeps
     r' above 0. [exp] is continuous at [t * ln r], and
     [|t' ln r' - t ln r| <= |t'| |ln r' - ln r| + |t' - t| |ln r|], where
     [|t'| < |t| + 1] and [ln] is continuous at r. *)
  destruct (pr_cont_eps exp (t * ln r) (pr_exp_cont _) eps Heps) as (a1 & Ha1 & H1).
  pose proof (Rabs_pos t) as Hat. pose proof (Rabs_pos (ln r)) as Hal.
  set (e2 := a1 / (2 * (Rabs t + 1))).
  assert (He2 : 0 < e2) by (unfold e2; apply Rdiv_lt_0_compat; lra).
  assert (He2' : e2 * (Rabs t + 1) = a1 / 2) by (unfold e2; field; lra).
  destruct (pr_cont_eps ln r (pr_ln_cont r Hr) e2 He2) as (a2 & Ha2 & H2).
  set (e3 := a1 / (2 * (Rabs (ln r) + 1))).
  assert (He3 : 0 < e3) by (unfold e3; apply Rdiv_lt_0_compat; lra).
  assert (He3' : e3 * (Rabs (ln r) + 1) = a1 / 2) by (unfold e3; field; lra).
  set (d := Rmin (Rmin r 1) (Rmin a2 e3)).
  assert (Hd : d <= r /\ d <= 1 /\ d <= a2 /\ d <= e3).
  { unfold d. pose proof (Rmin_l (Rmin r 1) (Rmin a2 e3)).
    pose proof (Rmin_r (Rmin r 1) (Rmin a2 e3)).
    pose proof (Rmin_l r 1). pose proof (Rmin_r r 1).
    pose proof (Rmin_l a2 e3). pose proof (Rmin_r a2 e3). lra. }
  exists d. split; [unfold d; repeat apply Rmin_glb_lt; lra|].
  intros r' t' _ Hr' Ht'.
  destruct (Rabs_def2 _ _ Hr') as [Hr1 Hr2].
  rewrite (Rpow_pos r' t'), (Rpow_pos r t) by lra. unfold Rpower. apply H1.
  replace (t' * ln r' - t * ln r) with (t' * (ln r' - ln r) + (t' - t) * ln r)
    by ring.
  eapply Rle_lt_trans; [apply Rabs_triang|]. rewrite !Rabs_mult.
  assert (Ht1 : Rabs t' < Rabs t + 1)
    by (pose proof (Rabs_triang_inv t' t); lra).
  assert (Hl : Rabs (ln r' - ln r) < e2) by (apply H2; lra).
  pose proof (Rabs_pos t') as Hat'. pose proof (Rabs_pos (ln r' - ln r)) as Hl0.
  pose proof (Rabs_pos (t' - t)) as Hdt0.
  assert (A : Rabs t' * Rabs (ln r' - ln r) < a1 / 2).
  { set (u := Rabs t') in *. set (v := Rabs (ln r' - ln r)) in *.
    set (w := Rabs t) in *. nra. }
  assert (B : Rabs (t' - t) * Rabs (ln r) < a1 / 2).
  { set (u := Rabs (t' - t)) in *. set (v := Rabs (ln r)) in *. nra. }
  lra.
- (* At (0, t) with t > 0: Rpow is 0 at r' <= 0, and for 0 < r' < delta
     <= 1 and t' > t / 2, [t' ln r' <= t / 2 * ln r' < ln eps] once
     [r' < exp (2 ln eps / t)], as [ln r' < 0]. *)
  rewrite Rpow_0_l. set (d0 := exp (2 * ln eps / t)).
  assert (Hd0 : 0 < d0) by apply exp_pos.
  set (d := Rmin (Rmin 1 (t / 2)) d0).
  assert (Hd : d <= 1 /\ d <= t / 2 /\ d <= d0).
  { unfold d. pose proof (Rmin_l (Rmin 1 (t / 2)) d0).
    pose proof (Rmin_r (Rmin 1 (t / 2)) d0).
    pose proof (Rmin_l 1 (t / 2)). pose proof (Rmin_r 1 (t / 2)). lra. }
  exists d. split; [unfold d; repeat apply Rmin_glb_lt; lra|].
  intros r' t' _ Hr' Ht'. rewrite Rminus_0_r in Hr' |- *.
  destruct (Rle_dec r' 0) as [Hle | Hgt].
  + unfold Rpow. destruct (Rle_dec r' 0) as [_ | Hn]; [|contradiction].
    rewrite Rabs_R0. exact Heps.
  + rewrite Rpow_pos by lra. unfold Rpower.
    rewrite Rabs_pos_eq by (left; apply exp_pos).
    apply pr_exp_lt_eps; [exact Heps|].
    rewrite Rabs_pos_eq in Hr' by lra.
    destruct (Rabs_def2 _ _ Ht') as [Ht1 Ht2].
    assert (Hl0 : ln r' < 0) by (apply pr_ln_lt0; lra).
    assert (Hl1 : ln r' < 2 * ln eps / t).
    { rewrite <- (ln_exp (2 * ln eps / t)). apply ln_increasing; [lra|].
      fold d0. lra. }
    assert (H2 : t * (2 * ln eps / t) = 2 * ln eps) by (field; lra).
    set (q := 2 * ln eps / t) in *. set (L := ln r') in *. nra.
Qed.
