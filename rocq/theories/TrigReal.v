(** * Facts about [atan], [asin] and [acos] on the reals

    What [Elem.v] and [ClosedDom.v] need of these functions: that they are
    monotone and continuous on their domains, and the bounds of [atan] at
    -inf and +inf. [asin] and [acos] are continuous at -1 and 1 relative
    to their domain [[-1, 1]], where Stdlib's [derivable_pt_asin] does not
    apply. *)

From Stdlib Require Import Reals Lra.
From Inari Require Import Elementary RealBounds.

Open Scope R_scope.

(** ** [continue_in] as epsilon-delta *)

Lemma continue_in_intro :
  forall f D x0,
  (forall eps, 0 < eps -> exists d, 0 < d /\
     forall x, D x -> Rabs (x - x0) < d -> Rabs (f x - f x0) < eps) ->
  continue_in f D x0.
Proof.
  intros f D x0 H eps Heps.
  destruct (H eps Heps) as [d [Hd Hx]].
  exists d; split; [exact Hd |].
  intros x [[HD _] Hdx]; exact (Hx x HD Hdx).
Qed.

Lemma continue_in_elim :
  forall f D x0, continue_in f D x0 ->
  forall eps, 0 < eps -> exists d, 0 < d /\
    forall x, D x -> x0 <> x -> Rabs (x - x0) < d -> Rabs (f x - f x0) < eps.
Proof.
  intros f D x0 H eps Heps.
  destruct (H eps Heps) as [d [Hd Hx]].
  exists d; split; [exact Hd |].
  intros x HD Hne Hdx; exact (Hx x (conj (conj HD Hne) Hdx)).
Qed.

(** Continuity on R gives continuity relative to any domain. *)
Lemma continuity_pt_continue_in_dom :
  forall f D x0, continuity_pt f x0 -> continue_in f D x0.
Proof.
  intros f D x0 H eps Heps.
  destruct (H eps Heps) as [d [Hd Hx]].
  exists d; split; [exact Hd |].
  intros x [[_ Hne] Hdx]; apply Hx.
  split; [split; [exact I | exact Hne] | exact Hdx].
Qed.

(** ** [atan] *)

Lemma atan_inc : forall r t, r <= t -> atan r <= atan t.
Proof.
  intros r t [Hlt | <-].
  - left; apply atan_increasing, Hlt.
  - right; reflexivity.
Qed.

Lemma atan_cont : forall r, continuity_pt atan r.
Proof.
  intros r; apply derivable_continuous_pt, derivable_pt_atan.
Qed.

(** For the bounds, [atan (tan t) = t] for every [t] in [(-PI/2, PI/2)], so
    [atan] takes values within [eps] of [-PI/2] and of [PI/2]. *)

Lemma atan_glb : glb_of atan (- (PI / 2)).
Proof.
  assert (HPI := PI_RGT_0).
  split.
  - intros r; destruct (atan_bound r); lra.
  - intros eps Heps.
    set (e := Rmin (eps / 2) (PI / 2)).
    assert (He1 : e <= eps / 2) by apply Rmin_l.
    assert (He2 : e <= PI / 2) by apply Rmin_r.
    assert (He0 : 0 < e) by (apply Rmin_glb_lt; lra).
    exists (tan (- (PI / 2) + e)).
    rewrite atan_tan by (split; lra).
    lra.
Qed.

Lemma atan_lub : lub_of atan (PI / 2).
Proof.
  assert (HPI := PI_RGT_0).
  split.
  - intros r; destruct (atan_bound r); lra.
  - intros eps Heps.
    set (e := Rmin (eps / 2) (PI / 2)).
    assert (He1 : e <= eps / 2) by apply Rmin_l.
    assert (He2 : e <= PI / 2) by apply Rmin_r.
    assert (He0 : 0 < e) by (apply Rmin_glb_lt; lra).
    exists (tan (PI / 2 - e)).
    rewrite atan_tan by (split; lra).
    lra.
Qed.

(** ** [asin] and [acos] *)

(** [asin] is increasing: if [asin t < asin r], then [sin], which is
    increasing on [[-PI/2, PI/2]], would give [t < r]. *)
Lemma asin_inc :
  forall r t, -1 <= r -> r <= t -> t <= 1 -> asin r <= asin t.
Proof.
  intros r t Hr Hrt Ht.
  destruct (Rle_or_lt (asin r) (asin t)) as [H | H]; [exact H |].
  exfalso.
  destruct (asin_bound r), (asin_bound t).
  assert (Hs : sin (asin t) < sin (asin r)) by (apply sin_increasing_1; lra).
  rewrite !sin_asin in Hs by lra.
  lra.
Qed.

Lemma asin_m1 : asin (-1) = - (PI / 2).
Proof.
  replace (-1) with (- (1)) by ring.
  rewrite asin_opp, asin_1; reflexivity.
Qed.

(** At 1, [asin] has no derivative. Given [eps], [asin x] is within [e < eps]
    of [asin 1 = PI/2] once [x >= sin (PI/2 - e)], which is below 1. *)
Lemma asin_cont_1 : continue_in asin asin_dom 1.
Proof.
  assert (HPI := PI_RGT_0).
  apply continue_in_intro; intros eps Heps.
  set (e := Rmin (eps / 2) (PI / 2)).
  assert (He1 : e <= eps / 2) by apply Rmin_l.
  assert (He2 : e <= PI / 2) by apply Rmin_r.
  assert (He0 : 0 < e) by (apply Rmin_glb_lt; lra).
  assert (Hs : sin (PI / 2 - e) < 1).
  { rewrite <- sin_PI2; apply sin_increasing_1; lra. }
  assert (Hs1 := SIN_bound (PI / 2 - e)).
  exists (1 - sin (PI / 2 - e)); split; [lra |].
  intros x [Hx1 Hx2] Hdx.
  assert (Hdx' : - (x - 1) <= Rabs (x - 1)) by (rewrite <- Rabs_Ropp; apply Rle_abs).
  assert (Hlo : asin (sin (PI / 2 - e)) <= asin x) by (apply asin_inc; lra).
  rewrite asin_sin in Hlo by lra.
  destruct (asin_bound x).
  rewrite asin_1; apply Rabs_def1; lra.
Qed.

(** At -1, symmetrically, [asin x] is within [e] of [-PI/2] once
    [x <= sin (-PI/2 + e)], which is above -1. *)
Lemma asin_cont_m1 : continue_in asin asin_dom (-1).
Proof.
  assert (HPI := PI_RGT_0).
  apply continue_in_intro; intros eps Heps.
  set (e := Rmin (eps / 2) (PI / 2)).
  assert (He1 : e <= eps / 2) by apply Rmin_l.
  assert (He2 : e <= PI / 2) by apply Rmin_r.
  assert (He0 : 0 < e) by (apply Rmin_glb_lt; lra).
  assert (Hs : -1 < sin (- (PI / 2) + e)).
  { replace (-1) with (sin (- (PI / 2))) by (rewrite sin_neg, sin_PI2; ring).
    apply sin_increasing_1; lra. }
  assert (Hs1 := SIN_bound (- (PI / 2) + e)).
  exists (sin (- (PI / 2) + e) + 1); split; [lra |].
  intros x [Hx1 Hx2] Hdx.
  assert (Hdx' : x - -1 <= Rabs (x - -1)) by apply Rle_abs.
  assert (Hhi : asin x <= asin (sin (- (PI / 2) + e))) by (apply asin_inc; lra).
  rewrite asin_sin in Hhi by lra.
  destruct (asin_bound x).
  rewrite asin_m1; apply Rabs_def1; lra.
Qed.

Lemma asin_cont : forall r, asin_dom r -> continue_in asin asin_dom r.
Proof.
  intros r [Hr1 Hr2].
  destruct (Rle_lt_or_eq_dec _ _ Hr1) as [Hlo | <-]; [| exact asin_cont_m1].
  destruct (Rle_lt_or_eq_dec _ _ Hr2) as [Hhi | ->]; [| exact asin_cont_1].
  (* Inside (-1, 1), [asin] is differentiable. *)
  apply continuity_pt_continue_in_dom, derivable_continuous_pt.
  apply derivable_pt_asin; lra.
Qed.

Lemma acos_dec :
  forall r t, -1 <= r -> r <= t -> t <= 1 -> acos t <= acos r.
Proof.
  intros r t Hr Hrt Ht.
  rewrite !acos_asin by lra.
  assert (H := asin_inc r t Hr Hrt Ht); lra.
Qed.

(** On [[-1, 1]], [acos = PI/2 - asin], so it inherits the continuity of
    [asin]. *)
Lemma acos_cont : forall r, acos_dom r -> continue_in acos acos_dom r.
Proof.
  intros r Hr.
  apply continue_in_intro; intros eps Heps.
  destruct (continue_in_elim _ _ _ (asin_cont r Hr) eps Heps) as [d [Hd H]].
  exists d; split; [exact Hd |].
  intros x Hx Hdx.
  unfold acos_dom in Hr, Hx.
  rewrite !acos_asin by lra.
  replace (PI / 2 - asin x - (PI / 2 - asin r)) with (- (asin x - asin r))
    by ring.
  rewrite Rabs_Ropp.
  destruct (Req_dec r x) as [<- | Hne].
  - replace (asin r - asin r) with 0 by ring; rewrite Rabs_R0; exact Heps.
  - apply H; [exact Hx | exact Hne | exact Hdx].
Qed.
