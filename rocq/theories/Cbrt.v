(** * [cbrt] of intervals and decorated intervals

    [Interval::cbrt] is [impl_mono_inc!(cbrt, cbrt_rd, cbrt_ru)], so its
    theorems are those of [MonoInc.v] for the real cube root [Rcbrt],
    which is increasing ([Rcbrt_lt] of [RootReal.v]) and continuous
    ([Rcbrt_continuous]). Each assumes what [Mpfr.v] says of MPFR. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr RealBounds ComCommon
  MpfrRound Interior MonoInc RootReal.

Open Scope R_scope.

(** ** The real cube root, in the form of [MonoInc.v]'s hypotheses *)

Lemma cbrt_inc : forall r t, r <= t -> Rcbrt r <= Rcbrt t.
Proof.
intros r t H.
destruct (Rle_lt_or_eq_dec _ _ H) as [Hl | He].
- left. apply Rcbrt_lt. exact Hl.
- rewrite He. apply Rle_refl.
Qed.

(** Cubing is strictly increasing: if [t^3 <= r^3], their cube roots
    [t] and [r] ([Rcbrt_unique]) are in the same order ([cbrt_inc]). *)
Local Lemma cube_lt : forall r t, r < t -> r * r * r < t * t * t.
Proof.
intros r t H.
destruct (Rlt_or_le (r * r * r) (t * t * t)) as [Hl | Hle]; [exact Hl |].
apply cbrt_inc in Hle.
rewrite (Rcbrt_unique _ r eq_refl), (Rcbrt_unique _ t eq_refl) in Hle.
lra.
Qed.

(** Epsilon-delta at [r0], with [c = Rcbrt r0]: the cubes of [c - eps]
    and [c + eps] lie on either side of [r0 = c^3] ([cube_lt]), so for
    [r] closer to [r0] than both, [(c - eps)^3 < r < (c + eps)^3], and
    taking cube roots ([Rcbrt_lt], [Rcbrt_unique]) gives
    [c - eps < Rcbrt r < c + eps]. *)
Lemma Rcbrt_continuous : forall r, continuity_pt Rcbrt r.
Proof.
intros r0 eps Heps.
set (c := Rcbrt r0).
pose proof (Rcbrt_cube r0) as Hc. fold c in Hc.
set (lo := (c - eps) * (c - eps) * (c - eps)).
set (hi := (c + eps) * (c + eps) * (c + eps)).
assert (Hlo : lo < r0) by (rewrite <- Hc; apply cube_lt; lra).
assert (Hhi : r0 < hi) by (rewrite <- Hc; apply cube_lt; lra).
exists (Rmin (r0 - lo) (hi - r0)).
split; [apply Rmin_pos; lra |].
intros r [_ Hr].
change (Rabs (r - r0) < Rmin (r0 - lo) (hi - r0)) in Hr.
change (Rabs (Rcbrt r - c) < eps).
pose proof (Rmin_l (r0 - lo) (hi - r0)) as Hml.
pose proof (Rmin_r (r0 - lo) (hi - r0)) as Hmr.
destruct (Rabs_def2 _ _ Hr) as [Hr1 Hr2].
assert (H1 : Rcbrt lo < Rcbrt r) by (apply Rcbrt_lt; lra).
assert (H2 : Rcbrt r < Rcbrt hi) by (apply Rcbrt_lt; lra).
rewrite (Rcbrt_unique lo (c - eps) eq_refl) in H1.
rewrite (Rcbrt_unique hi (c + eps) eq_refl) in H2.
apply Rabs_def1; lra.
Qed.

(** [Rcbrt (M^3) = M]. *)
Lemma cbrt_unbounded_below : unbounded_below Rcbrt.
Proof.
intros M. exists (M * M * M). rewrite (Rcbrt_unique _ M eq_refl). apply Rle_refl.
Qed.

Lemma cbrt_unbounded_above : unbounded_above Rcbrt.
Proof.
intros M. exists (M * M * M). rewrite (Rcbrt_unique _ M eq_refl). apply Rle_refl.
Qed.

(** ** [impl_mono_inc!] *)

Theorem cbrt_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> cbrt_ok emin emax m ->
  forall x, valid x -> is_tightest (image_dom real_dom Rcbrt x) (Interval.cbrt m x).
Proof.
intros emin emax m Hr Hget [Hg [Hlo Hhi]] x Hx.
change (Interval.cbrt m x) with
  (Interval.mono_inc (mpfr_fn m (mpfr_cbrt m) RNDD) (mpfr_fn m (mpfr_cbrt m) RNDU) x).
eapply mono_inc_correct;
  first
    [ eassumption | exact cbrt_inc | exact Rcbrt_continuous
    | right; split; [exact cbrt_unbounded_below | exact Hlo]
    | right; split; [exact cbrt_unbounded_above | exact Hhi] ].
Qed.

Theorem dec_cbrt_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> cbrt_ok emin emax m ->
  forall x, valid (itv x) ->
  let y := DecInterval.cbrt m x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom Rcbrt (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d Rcbrt (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros emin emax m Hr Hget [Hg [Hlo Hhi]] x Hx.
change (DecInterval.cbrt m x) with
  (DecInterval.elem_dec
     (Interval.mono_inc (mpfr_fn m (mpfr_cbrt m) RNDD) (mpfr_fn m (mpfr_cbrt m) RNDU)) x).
eapply dec_mono_inc_correct;
  first
    [ eassumption | exact cbrt_inc | exact Rcbrt_continuous
    | right; split; [exact cbrt_unbounded_below | exact Hlo]
    | right; split; [exact cbrt_unbounded_above | exact Hhi]
    | right; split; [exact cbrt_unbounded_below | exact cbrt_unbounded_above] ].
Qed.
