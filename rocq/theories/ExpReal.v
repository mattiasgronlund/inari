(** * Facts about [exp], [exp2], [exp10], [sinh], [cosh], [tanh] and
    [asinh] on the reals

    What [Elem.v] and [Cosh.v] need of these functions: that they are
    monotone and continuous, and their bounds at -inf and +inf. *)

From Stdlib Require Import Reals Lra.
From Inari Require Import Elementary RealBounds.

Open Scope R_scope.

(** ** [exp] *)

Lemma exp_inc : forall r t, r <= t -> exp r <= exp t.
Proof.
  intros r t [H | ->].
  - apply Rlt_le, exp_increasing; exact H.
  - apply Rle_refl.
Qed.

Lemma exp_cont : forall r, continuity_pt exp r.
Proof.
  intros r; apply derivable_continuous_pt, derivable_pt_exp.
Qed.

Lemma exp_glb : glb_of exp 0.
Proof.
  split.
  - intros r; left; apply exp_pos.
  - (* [exp (ln (eps / 2)) = eps / 2]. *)
    intros eps Heps; exists (ln (eps / 2)).
    rewrite exp_ln by lra; lra.
Qed.

Lemma exp_unbounded : unbounded_above exp.
Proof.
  (* [1 + M <= exp M]. *)
  intros M; exists M; pose proof (exp_ineq1_le M); lra.
Qed.

(** ** [exp2] and [exp10] *)

(** [Rpower b r = exp (r * ln b)] for a base [b] with [0 < ln b], i.e.
    [1 < b]. *)
Section Rpower_base.

Variable b : R.
Hypothesis Hb : 0 < ln b.

Lemma Rpower_inc : forall r t, r <= t -> Rpower b r <= Rpower b t.
Proof.
  intros r t H; unfold Rpower; apply exp_inc.
  apply Rmult_le_compat_r; lra.
Qed.

Lemma Rpower_cont : forall r, continuity_pt (Rpower b) r.
Proof.
  intros r.
  (* [Rpower b] is [exp] after [fun t => t * ln b]. *)
  change (continuity_pt (comp exp (mult_fct id (fct_cte (ln b)))) r).
  apply continuity_pt_comp.
  - apply continuity_pt_mult.
    + apply derivable_continuous_pt, derivable_pt_id.
    + apply continuity_pt_const; intros ? ?; reflexivity.
  - apply exp_cont.
Qed.

Lemma Rpower_glb : glb_of (Rpower b) 0.
Proof.
  split.
  - intros r; left; apply exp_pos.
  - (* [Rpower b (ln (eps / 2) / ln b) = exp (ln (eps / 2)) = eps / 2]. *)
    intros eps Heps; exists (ln (eps / 2) / ln b); unfold Rpower.
    replace (ln (eps / 2) / ln b * ln b) with (ln (eps / 2)) by (field; lra).
    rewrite exp_ln by lra; lra.
Qed.

Lemma Rpower_unbounded : unbounded_above (Rpower b).
Proof.
  (* [Rpower b (M / ln b) = exp M >= 1 + M]. *)
  intros M; exists (M / ln b); unfold Rpower.
  replace (M / ln b * ln b) with M by (field; lra).
  pose proof (exp_ineq1_le M); lra.
Qed.

End Rpower_base.

Lemma ln_2_pos : 0 < ln 2.
Proof.
  pose proof ln_lt_2; lra.
Qed.

Lemma ln_10_pos : 0 < ln 10.
Proof.
  rewrite <- ln_1; apply ln_increasing; lra.
Qed.

Lemma exp2_inc : forall r t, r <= t -> Rexp2 r <= Rexp2 t.
Proof.
  apply Rpower_inc, ln_2_pos.
Qed.

Lemma exp2_cont : forall r, continuity_pt Rexp2 r.
Proof.
  apply Rpower_cont.
Qed.

Lemma exp2_glb : glb_of Rexp2 0.
Proof.
  apply Rpower_glb, ln_2_pos.
Qed.

Lemma exp2_unbounded : unbounded_above Rexp2.
Proof.
  apply Rpower_unbounded, ln_2_pos.
Qed.

Lemma exp10_inc : forall r t, r <= t -> Rexp10 r <= Rexp10 t.
Proof.
  apply Rpower_inc, ln_10_pos.
Qed.

Lemma exp10_cont : forall r, continuity_pt Rexp10 r.
Proof.
  apply Rpower_cont.
Qed.

Lemma exp10_glb : glb_of Rexp10 0.
Proof.
  apply Rpower_glb, ln_10_pos.
Qed.

Lemma exp10_unbounded : unbounded_above Rexp10.
Proof.
  apply Rpower_unbounded, ln_10_pos.
Qed.

(** ** [sinh] *)

Lemma sinh_inc : forall r t, r <= t -> sinh r <= sinh t.
Proof.
  intros r t [H | ->].
  - apply Rlt_le, sinh_lt; exact H.
  - apply Rle_refl.
Qed.

Lemma sinh_cont : forall r, continuity_pt sinh r.
Proof.
  intros r; apply derivable_continuous_pt, derivable_pt_sinh.
Qed.

(** [sinh (arcsinh M) = M]. *)
Lemma sinh_unbounded_below : unbounded_below sinh.
Proof.
  intros M; exists (arcsinh M); rewrite sinh_arcsinh; apply Rle_refl.
Qed.

Lemma sinh_unbounded_above : unbounded_above sinh.
Proof.
  intros M; exists (arcsinh M); rewrite sinh_arcsinh; apply Rle_refl.
Qed.

(** ** [tanh] *)

(** [tanh r = (e - 1 / e) / (e + 1 / e) = 1 - 2 / (e^2 + 1)] with
    [e = exp r]. *)
Lemma tanh_eq : forall r, tanh r = 1 - 2 * / (exp (2 * r) + 1).
Proof.
  intros r; unfold tanh, sinh, cosh.
  rewrite exp_Ropp.
  replace (2 * r) with (r + r) by ring; rewrite exp_plus.
  pose proof (exp_pos r).
  field; split; nra.
Qed.

(** The [/ (e^2 + 1)] above is in [(0, 1)]. *)
Lemma tanh_inv_bounds : forall r, 0 < / (exp (2 * r) + 1) < 1.
Proof.
  intros r; pose proof (exp_pos (2 * r)).
  assert (Hi : 0 < / (exp (2 * r) + 1)) by (apply Rinv_0_lt_compat; lra).
  assert (He : / (exp (2 * r) + 1) * (exp (2 * r) + 1) = 1)
    by (apply Rinv_l; lra).
  split; [exact Hi | nra].
Qed.

(** [tanh r + 1 = 2 e^2 / (e^2 + 1) <= 2 e^2]. *)
Lemma tanh_plus_1_le : forall r, tanh r + 1 <= 2 * exp (2 * r).
Proof.
  intros r; rewrite tanh_eq.
  pose proof (exp_pos (2 * r)); pose proof (tanh_inv_bounds r).
  assert (He : / (exp (2 * r) + 1) * (exp (2 * r) + 1) = 1)
    by (apply Rinv_l; lra).
  nra.
Qed.

Lemma tanh_odd : forall r, tanh (- r) = - tanh r.
Proof.
  intros r; unfold tanh, sinh, cosh; rewrite Ropp_involutive.
  pose proof (exp_pos r); pose proof (exp_pos (- r)).
  field; lra.
Qed.

Lemma tanh_inc : forall r t, r <= t -> tanh r <= tanh t.
Proof.
  intros r t H; rewrite !tanh_eq.
  pose proof (exp_pos (2 * r)).
  assert (exp (2 * r) <= exp (2 * t)) by (apply exp_inc; lra).
  (* [e^2] grows with [r], so [/ (e^2 + 1)] decreases. *)
  assert (/ (exp (2 * t) + 1) <= / (exp (2 * r) + 1))
    by (apply Rinv_le_contravar; lra).
  lra.
Qed.

Lemma tanh_cont : forall r, continuity_pt tanh r.
Proof.
  intros r; change (continuity_pt (div_fct sinh cosh) r).
  apply continuity_pt_div.
  - apply sinh_cont.
  - apply derivable_continuous_pt, derivable_pt_cosh.
  - unfold cosh; pose proof (exp_pos r); pose proof (exp_pos (- r)); lra.
Qed.

Lemma tanh_glb : glb_of tanh (-1).
Proof.
  split.
  - intros r; rewrite tanh_eq; pose proof (tanh_inv_bounds r); lra.
  - (* At [r = ln (eps / 4) / 2], [tanh r + 1 <= 2 e^2 = eps / 2]. *)
    intros eps Heps; exists (ln (eps / 4) / 2).
    pose proof (tanh_plus_1_le (ln (eps / 4) / 2)).
    replace (2 * (ln (eps / 4) / 2)) with (ln (eps / 4)) in H by field.
    rewrite exp_ln in H by lra; lra.
Qed.

Lemma tanh_lub : lub_of tanh 1.
Proof.
  split.
  - intros r; rewrite tanh_eq; pose proof (tanh_inv_bounds r); lra.
  - (* [tanh] is odd, so this is the bound of [tanh_glb] at [- r]. *)
    intros eps Heps; destruct (proj2 tanh_glb eps Heps) as [r Hr].
    exists (- r); rewrite tanh_odd; lra.
Qed.

(** ** [asinh], Stdlib's [arcsinh] *)

Lemma asinh_inc : forall r t, r <= t -> arcsinh r <= arcsinh t.
Proof.
  apply arcsinh_le.
Qed.

Lemma asinh_cont : forall r, continuity_pt arcsinh r.
Proof.
  intros r; apply derivable_continuous_pt.
  exists (/ sqrt (r ^ 2 + 1)); apply derivable_pt_lim_arcsinh.
Qed.

(** [arcsinh (sinh M) = M]. *)
Lemma asinh_unbounded_below : unbounded_below arcsinh.
Proof.
  intros M; exists (sinh M); rewrite arcsinh_sinh; apply Rle_refl.
Qed.

Lemma asinh_unbounded_above : unbounded_above arcsinh.
Proof.
  intros M; exists (sinh M); rewrite arcsinh_sinh; apply Rle_refl.
Qed.

(** ** [cosh] *)

Lemma cosh_even : forall r, cosh (- r) = cosh r.
Proof.
  intros r; unfold cosh; rewrite Ropp_involutive; lra.
Qed.

Lemma cosh_inc : forall r t, 0 <= r -> r <= t -> cosh r <= cosh t.
Proof.
  intros r t Hr Hrt; unfold cosh; rewrite !exp_Ropp.
  assert (Ha : 1 <= exp r) by (rewrite <- exp_0; apply exp_inc; exact Hr).
  assert (Hab : exp r <= exp t) by (apply exp_inc; exact Hrt).
  set (a := exp r) in *; set (b := exp t) in *.
  (* [(b + 1 / b) - (a + 1 / a) = (b - a) (a b - 1) / (a b)], and
     [1 <= a <= b]. *)
  assert (E : b + / b - (a + / a) = (b - a) * (a * b - 1) * / (a * b))
    by (field; lra).
  assert (0 <= (b - a) * (a * b - 1) * / (a * b)).
  { apply Rmult_le_pos; [apply Rmult_le_pos; nra |].
    left; apply Rinv_0_lt_compat; nra. }
  lra.
Qed.

Lemma cosh_dec : forall r t, r <= t -> t <= 0 -> cosh t <= cosh r.
Proof.
  intros r t Hrt Ht; rewrite <- (cosh_even t), <- (cosh_even r).
  apply cosh_inc; lra.
Qed.

Lemma cosh_ge_1 : forall r, 1 <= cosh r.
Proof.
  (* [cosh 0 = 1] is the least value, at [0 <= |r|]. *)
  intros r; rewrite <- cosh_0; destruct (Rle_dec 0 r) as [H | H].
  - apply cosh_inc; lra.
  - rewrite <- (cosh_even r); apply cosh_inc; lra.
Qed.

Lemma cosh_cont : forall r, continuity_pt cosh r.
Proof.
  intros r; apply derivable_continuous_pt, derivable_pt_cosh.
Qed.

Lemma cosh_unbounded : forall M, exists r, 0 <= r /\ M <= cosh r.
Proof.
  (* [cosh r >= exp r / 2 >= (1 + r) / 2] at [r = 2 |M|]. *)
  intros M; exists (2 * Rabs M); split.
  - pose proof (Rabs_pos M); lra.
  - unfold cosh; pose proof (exp_ineq1_le (2 * Rabs M)).
    pose proof (exp_pos (- (2 * Rabs M))); pose proof (Rle_abs M); lra.
Qed.
