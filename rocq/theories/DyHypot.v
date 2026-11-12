(** * [hypot] of the dyadic kernel

    [DyadicRoot.hypot] and [DyadicRoot.hypot_near] return, at every
    finite [x] and [y], [sqrt (x * x + y * y)] rounded toward -inf or +inf
    ([hypot_dir_correct]) and to nearest ([hypot_near_correct]); +inf
    if [x] or [y] is infinite, even if the other is NaN ([hypot_inf]);
    otherwise NaN if one is NaN ([hypot_nan]); and +0 at two zeros
    ([hypot_zeros]). If [y] is 0 the result is [|x|], and if [x] is 0 it
    is [|y|], which are their own roundings. Otherwise
    [hypot_odd_correct] of [DyHypotOdd.v] gives the odd value, and
    [odd_window_dir] or [odd_window_near] the rounding, and
    [to_f64_correct] or [to_f64_near_correct] the [f64]. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Knuth DyRound DyConv DyConvNear NearF64 NearCells
  Decompose RootRound DyHypotOdd.
From Inari Require FastHypot.

Open Scope Z_scope.

(** ** Lemmas *)

Local Lemma hy_inf : infinity = B754_infinity false.
Proof. now apply B2SF_inj. Qed.

Local Lemma hy_ninf : DyadicExp.neg_infinity = B754_infinity true.
Proof. now apply B2SF_inj. Qed.

(** A finite [x] or a NaN is neither +inf nor -inf. *)
Local Lemma hy_not_inf :
  forall x : f64, is_finite x = true \/ is_nan x = true ->
  (eq x infinity || eq x DyadicExp.neg_infinity) = false.
Proof.
intros x H. rewrite hy_inf, hy_ninf.
destruct x as [s|s| |s m e Hx]; destruct H as [H | H]; try discriminate H; reflexivity.
Qed.

Local Lemma hy_not_nan : forall x : f64, is_finite x = true -> is_nan x = false.
Proof. intros [s|s| |s m e Hx] H; first [discriminate H | reflexivity]. Qed.

(** [x == 0.0] of a finite [x] says whether [x] is 0. *)
Local Lemma hy_eq_zero :
  forall x : f64, is_finite x = true -> (eq x zero = true <-> B2R x = 0%R).
Proof.
intros x Fx. unfold eq. rewrite Beqb_correct by (first [exact Fx | reflexivity]).
change (B2R zero) with 0%R.
destruct (Req_bool_spec (B2R x) 0) as [H | H]; split; intros H';
  first [exact H | reflexivity | discriminate H' | contradiction].
Qed.

(** [sqrt (x x + 0 0)] and [sqrt (0 0 + x x)] are [|x|]. *)
Local Lemma hy_sqrt_l : forall x : f64, (sqrt (B2R x * B2R x + 0 * 0) = B2R (fabs x))%R.
Proof.
intros x. unfold fabs. rewrite B2R_Babs.
replace (B2R x * B2R x + 0 * 0)%R with (Rabs (B2R x) * Rabs (B2R x))%R
  by (unfold Rabs; destruct (Rcase_abs (B2R x)); ring).
apply sqrt_square. apply Rabs_pos.
Qed.

Local Lemma hy_sqrt_r : forall x : f64, (sqrt (0 * 0 + B2R x * B2R x) = B2R (fabs x))%R.
Proof. intros x. rewrite Rplus_comm. apply hy_sqrt_l. Qed.

Local Lemma hy_fabs_finite : forall x : f64, is_finite x = true -> is_finite (fabs x) = true.
Proof. intros x Fx. unfold fabs. rewrite is_finite_Babs. exact Fx. Qed.

(** A finite [f64] is its own rounding in either direction. *)
Local Lemma hy_exact_dir :
  forall (w : f64) (up : bool), is_finite w = true ->
  mpfr_round f64_format (if up then RNDU else RNDD) (B2R w) (with_val w).
Proof.
intros w up Fw.
assert (F : f64_format (B2R w)) by (exists w; split; [exact Fw | reflexivity]).
destruct w as [s|s| |s m e Hw]; try discriminate Fw.
- change (B2R (B754_zero s)) with 0%R in *.
  destruct up; cbn [with_val mpfr_round];
    (split; [exact F | split; [apply Rle_refl | intros g _ Hg; exact Hg]]).
- assert (H0 : B2R (B754_finite s m e Hw) <> 0%R).
  { cbn [B2R]. apply F2R_neq_0. destruct s; cbn; discriminate. }
  destruct up; cbn [with_val mpfr_round]; (split; [exact H0 |]);
    (split; [exact F | split; [apply Rle_refl | intros g _ Hg; exact Hg]]).
Qed.

(** ** The theorems *)

Theorem hypot_dir_correct :
  forall x y up,
  is_finite x = true -> is_finite y = true ->
  exists v, DyadicRoot.hypot x y up = Some v /\
  mpfr_round f64_format (if up then RNDU else RNDD)
    (sqrt (B2R x * B2R x + B2R y * B2R y)) (with_val v).
Proof.
intros x y up Fx Fy.
unfold DyadicRoot.hypot.
rewrite (hy_not_inf x (or_introl Fx)), (hy_not_inf y (or_introl Fy)), (hy_not_nan x Fx),
  (hy_not_nan y Fy).
cbn [orb].
destruct (eq y zero) eqn:Zy.
- (* [hypot(x, 0) = |x|], which rounds to itself. *)
  destruct (proj1 (Decompose.eq_zero_iff y) Zy) as (sy & ->).
  exists (fabs x). split; [reflexivity |].
  change (B2R (B754_zero sy)) with 0%R. rewrite hy_sqrt_l.
  apply hy_exact_dir. apply hy_fabs_finite. exact Fx.
- destruct (eq x zero) eqn:Zx.
  + (* [hypot(0, y) = |y|]. *)
    destruct (proj1 (Decompose.eq_zero_iff x) Zx) as (sx & ->).
    exists (fabs y). split; [reflexivity |].
    change (B2R (B754_zero sx)) with 0%R. rewrite hy_sqrt_r.
    apply hy_exact_dir. apply hy_fabs_finite. exact Fy.
  + assert (Hx0 : B2R x <> 0%R).
    { intros H. rewrite (proj2 (hy_eq_zero x Fx) H) in Zx. discriminate Zx. }
    assert (Hy0 : B2R y <> 0%R).
    { intros H. rewrite (proj2 (hy_eq_zero y Fy) H) in Zy. discriminate Zy. }
    (* The fast path, where it returns. *)
    destruct (DyadicRoot.fast_hypot false x y up) as [w |] eqn:F.
    { exists w. split; [reflexivity |].
      exact (FastHypot.fast_hypot_dir_correct false x y up w Fx Fy Hx0 Hy0 F). }
    destruct (hypot_odd_correct x y Fx Fy Hx0 Hy0) as (d & s & E & b & Hd & Od & Vd & Hs & Hw & Hb).
    rewrite Hd.
    assert (Hn : level_ok 3) by (unfold level_ok; lia).
    destruct (to_f64_correct 3 d up Hn Od) as (v & Ev & Rv).
    exists v. split; [exact Ev |].
    pose proof (proj1 (odd_window_dir false s E b _ up (with_val v) Hs Hw Hb)) as H.
    cbn [cond_Ropp] in H. apply H. rewrite <- Vd. exact Rv.
Qed.

Theorem hypot_near_correct :
  forall x y,
  is_finite x = true -> is_finite y = true ->
  exists v, DyadicRoot.hypot_near x y = Some v /\
  near_round (sqrt (B2R x * B2R x + B2R y * B2R y)) v.
Proof.
intros x y Fx Fy.
unfold DyadicRoot.hypot_near.
rewrite (hy_not_inf x (or_introl Fx)), (hy_not_inf y (or_introl Fy)), (hy_not_nan x Fx),
  (hy_not_nan y Fy).
cbn [orb].
destruct (eq y zero) eqn:Zy.
- (* [hypot(x, 0) = |x|], which rounds to itself. *)
  destruct (proj1 (Decompose.eq_zero_iff y) Zy) as (sy & ->).
  exists (fabs x). split; [reflexivity |].
  change (B2R (B754_zero sy)) with 0%R. rewrite hy_sqrt_l.
  apply near_exact. apply hy_fabs_finite. exact Fx.
- destruct (eq x zero) eqn:Zx.
  + (* [hypot(0, y) = |y|]. *)
    destruct (proj1 (Decompose.eq_zero_iff x) Zx) as (sx & ->).
    exists (fabs y). split; [reflexivity |].
    change (B2R (B754_zero sx)) with 0%R. rewrite hy_sqrt_r.
    apply near_exact. apply hy_fabs_finite. exact Fy.
  + assert (Hx0 : B2R x <> 0%R).
    { intros H. rewrite (proj2 (hy_eq_zero x Fx) H) in Zx. discriminate Zx. }
    assert (Hy0 : B2R y <> 0%R).
    { intros H. rewrite (proj2 (hy_eq_zero y Fy) H) in Zy. discriminate Zy. }
    (* The fast path, where it returns. *)
    destruct (DyadicRoot.fast_hypot_near false x y) as [w |] eqn:F.
    { exists w. split; [reflexivity |].
      exact (FastHypot.fast_hypot_near_correct false x y w Fx Fy Hx0 Hy0 F). }
    destruct (hypot_odd_correct x y Fx Fy Hx0 Hy0) as (d & s & E & b & Hd & Od & Vd & Hs & Hw & Hb).
    rewrite Hd.
    assert (Hn : level_ok 3) by (unfold level_ok; lia).
    destruct (to_f64_near_correct 3 d Hn Od) as (v & Ev & Rv & _).
    exists v. split; [exact Ev |].
    pose proof (proj1 (odd_window_near false s E b _ v Hs Hw Hb)) as H.
    cbn [cond_Ropp] in H. apply H. rewrite <- Vd. exact Rv.
Qed.

Theorem hypot_inf :
  forall x y up,
  (is_finite x = false /\ is_nan x = false) \/ (is_finite y = false /\ is_nan y = false) ->
  DyadicRoot.hypot x y up = Some infinity /\ DyadicRoot.hypot_near x y = Some infinity.
Proof.
intros x y up H.
unfold DyadicRoot.hypot, DyadicRoot.hypot_near.
(* An [f64] that is neither finite nor NaN is +inf or -inf. *)
replace ((eq x infinity || eq x DyadicExp.neg_infinity)
         || (eq y infinity || eq y DyadicExp.neg_infinity)) with true.
- split; reflexivity.
- symmetry. rewrite hy_inf, hy_ninf. apply Bool.orb_true_iff.
  destruct H as [(F & N) | (F & N)]; [left; destruct x | right; destruct y];
    try discriminate F; try discriminate N; destruct s; reflexivity.
Qed.

Theorem hypot_nan :
  forall x y up,
  (is_finite x = true \/ is_nan x = true) -> (is_finite y = true \/ is_nan y = true) ->
  is_nan x = true \/ is_nan y = true ->
  DyadicRoot.hypot x y up = Some B754_nan /\ DyadicRoot.hypot_near x y = Some B754_nan.
Proof.
intros x y up Hx Hy Hn.
unfold DyadicRoot.hypot, DyadicRoot.hypot_near.
rewrite (hy_not_inf x Hx), (hy_not_inf y Hy). cbn [orb].
replace (is_nan x || is_nan y) with true by (symmetry; apply Bool.orb_true_iff; exact Hn).
split; reflexivity.
Qed.

Theorem hypot_zeros :
  forall x y up,
  is_finite x = true -> is_finite y = true -> B2R x = 0%R -> B2R y = 0%R ->
  DyadicRoot.hypot x y up = Some zero /\ DyadicRoot.hypot_near x y = Some zero.
Proof.
intros x y up Fx Fy Hx Hy.
(* Both are zeros, and [|+-0| = +0]. *)
destruct (proj1 (Decompose.eq_zero_iff x) (proj2 (hy_eq_zero x Fx) Hx)) as (sx & ->).
destruct (proj1 (Decompose.eq_zero_iff y) (proj2 (hy_eq_zero y Fy) Hy)) as (sy & ->).
unfold DyadicRoot.hypot, DyadicRoot.hypot_near. rewrite hy_inf, hy_ninf.
destruct sx, sy; split; reflexivity.
Qed.
