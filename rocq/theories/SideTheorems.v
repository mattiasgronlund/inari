(** * The elementary functions contain the image for a record on the correct side

    For every record [p] whose fields satisfy the parts of
    [ContractSide.v] that they need, the interval functions of [Model.v]
    return intervals that contain the image of their argument
    ([encloses] of [Ieee1788.v]). The proof goes through [side_tight p]
    of [SideTight.v]: its fields satisfy [Contract.v], so the theorems
    of [PointTheorems.v] give the tightest intervals for it, and [p]'s
    fields are outward of its fields, so [p] gives wider intervals
    ([SideMono.v], [SideMonoB.v]). [sin], [cos] and [tan] also need the
    same [quadrant] for both records ([quadrant_tight]). *)

From Stdlib Require Import ZArith Reals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Contract ContractSide SideDefs SideMono
  SideMonoB SideTight PointTheorems.

Open Scope R_scope.

(** A tightest interval encloses its set, and so does a wider one. *)
Lemma tightest_wider : forall s y y', is_tightest s y' -> wider y y' -> encloses s y.
Proof.
intros s y y' (V & S & _) W. exact (encloses_wider s y y' (conj V S) W).
Qed.

(** The theorems of the functions of one argument with no other
    parameter: [<f>_correct_point] for [side_tight p], then
    [<f>_wider]. *)
Ltac side_simple correct tight_c tight_out wider :=
  let p := fresh "p" in let H := fresh "H" in let x := fresh "x" in let Hx := fresh "Hx" in
  intros p H x Hx;
  exact (tightest_wider _ _ _ (correct (side_tight p) (tight_c p H) x Hx)
    (wider p (side_tight p) (tight_out p H) x)).

Theorem exp_encloses_side :
  forall p, exp_s (p_exp p) ->
  forall x, valid x -> encloses (image_dom real_dom exp x) (Interval.exp p x).
Proof.
side_simple exp_correct_point exp_tight_c exp_tight_out exp_wider.
Qed.

Theorem exp2_encloses_side :
  forall p, exp2_s (p_exp2 p) ->
  forall x, valid x -> encloses (image_dom real_dom Rexp2 x) (Interval.exp2 p x).
Proof.
side_simple exp2_correct_point exp2_tight_c exp2_tight_out exp2_wider.
Qed.

Theorem exp10_encloses_side :
  forall p, exp10_s (p_exp10 p) ->
  forall x, valid x -> encloses (image_dom real_dom Rexp10 x) (Interval.exp10 p x).
Proof.
side_simple exp10_correct_point exp10_tight_c exp10_tight_out exp10_wider.
Qed.

Theorem sinh_encloses_side :
  forall p, sinh_s (p_sinh p) ->
  forall x, valid x -> encloses (image_dom real_dom sinh x) (Interval.sinh p x).
Proof.
side_simple sinh_correct_point sinh_tight_c sinh_tight_out sinh_wider.
Qed.

Theorem tanh_encloses_side :
  forall p, tanh_s (p_tanh p) ->
  forall x, valid x -> encloses (image_dom real_dom tanh x) (Interval.tanh p x).
Proof.
side_simple tanh_correct_point tanh_tight_c tanh_tight_out tanh_wider.
Qed.

Theorem ln_encloses_side :
  forall p, ln_s (p_ln p) ->
  forall x, valid x -> encloses (image_dom log_dom ln x) (Interval.ln p x).
Proof.
side_simple ln_correct_point ln_tight_c ln_tight_out ln_wider.
Qed.

Theorem log2_encloses_side :
  forall p, log2_s (p_log2 p) ->
  forall x, valid x -> encloses (image_dom log_dom Rlog2 x) (Interval.log2 p x).
Proof.
side_simple log2_correct_point log2_tight_c log2_tight_out log2_wider.
Qed.

Theorem log10_encloses_side :
  forall p, log10_s (p_log10 p) ->
  forall x, valid x -> encloses (image_dom log_dom Rlog10 x) (Interval.log10 p x).
Proof.
side_simple log10_correct_point log10_tight_c log10_tight_out log10_wider.
Qed.

Theorem asinh_encloses_side :
  forall p, asinh_s (p_asinh p) ->
  forall x, valid x -> encloses (image_dom real_dom arcsinh x) (Interval.asinh p x).
Proof.
side_simple asinh_correct_point asinh_tight_c asinh_tight_out asinh_wider.
Qed.

Theorem acosh_encloses_side :
  forall p, acosh_s (p_acosh p) ->
  forall x, valid x -> encloses (image_dom acosh_dom Racosh x) (Interval.acosh p x).
Proof.
side_simple acosh_correct_point acosh_tight_c acosh_tight_out acosh_wider.
Qed.

Theorem atanh_encloses_side :
  forall p, atanh_s (p_atanh p) ->
  forall x, valid x -> encloses (image_dom atanh_dom Ratanh x) (Interval.atanh p x).
Proof.
side_simple atanh_correct_point atanh_tight_c atanh_tight_out atanh_wider.
Qed.

Theorem atan_encloses_side :
  forall p, atan_s (p_atan p) ->
  forall x, valid x -> encloses (image_dom real_dom atan x) (Interval.atan p x).
Proof.
side_simple atan_correct_point atan_tight_c atan_tight_out atan_wider.
Qed.

Theorem asin_encloses_side :
  forall p, asin_s (p_asin p) ->
  forall x, valid x -> encloses (image_dom asin_dom asin x) (Interval.asin p x).
Proof.
side_simple asin_correct_point asin_tight_c asin_tight_out asin_wider.
Qed.

Theorem acos_encloses_side :
  forall p, acos_s (p_acos p) ->
  forall x, valid x -> encloses (image_dom acos_dom acos x) (Interval.acos p x).
Proof.
side_simple acos_correct_point acos_tight_c acos_tight_out acos_wider.
Qed.

Theorem cosh_encloses_side :
  forall p, cosh_s (p_cosh p) ->
  forall first x, valid x -> encloses (image_dom real_dom cosh x) (Interval.cosh p first x).
Proof.
intros p H first x Hx.
exact (tightest_wider _ _ _ (cosh_correct_point (side_tight p) (cosh_tight_c p H) first x Hx)
  (cosh_wider p (side_tight p) (cosh_tight_out p H) first x)).
Qed.

Theorem atan2_encloses_side :
  forall p, atan2_s (p_atan2 p) ->
  forall y x, valid y -> valid x ->
  exists z, Interval.atan2 p y x = Some z /\ encloses (image2_set atan2_dom Ratan2 y x) z.
Proof.
intros p H y x Hy Hx.
destruct (atan2_correct_point (side_tight p) (atan2_tight_c p H) y x Hy Hx) as (z & Ez & T).
destruct (atan2_wider p (side_tight p) (atan2_tight_out p H) y x z Ez) as (z' & Ez' & W).
exists z'. split; [exact Ez' | exact (tightest_wider _ _ _ T W)].
Qed.

Theorem sin_encloses_side :
  forall p, sin_s (p_sin p) -> cos_s (p_cos p) ->
  forall has_fma first x, valid x ->
  exists y, Interval.sin p has_fma first x = Some y /\ encloses (image_dom real_dom sin x) y.
Proof.
intros p Hs Hc has_fma first x Hx.
destruct (sin_correct_point (side_tight p) (sin_tight_c p Hs) (cos_tight_c p Hc) has_fma first x Hx)
  as (y & Ey & T).
destruct (sin_wider p (side_tight p) (sin_tight_out p Hs) (quadrant_tight p Hs Hc)
  has_fma first x y Ey) as (y' & Ey' & W).
exists y'. split; [exact Ey' | exact (tightest_wider _ _ _ T W)].
Qed.

Theorem cos_encloses_side :
  forall p, cos_s (p_cos p) -> sin_s (p_sin p) ->
  forall has_fma first x, valid x ->
  exists y, Interval.cos p has_fma first x = Some y /\ encloses (image_dom real_dom cos x) y.
Proof.
intros p Hc Hs has_fma first x Hx.
destruct (cos_correct_point (side_tight p) (cos_tight_c p Hc) (sin_tight_c p Hs) has_fma first x Hx)
  as (y & Ey & T).
destruct (cos_wider p (side_tight p) (cos_tight_out p Hc) (quadrant_tight p Hs Hc)
  has_fma first x y Ey) as (y' & Ey' & W).
exists y'. split; [exact Ey' | exact (tightest_wider _ _ _ T W)].
Qed.

Theorem tan_encloses_side :
  forall p, tan_s (p_tan p) -> sin_s (p_sin p) -> cos_s (p_cos p) ->
  forall has_fma x, valid x ->
  exists y, Interval.tan p has_fma x = Some y /\ encloses (image_dom tan_dom tan x) y.
Proof.
intros p Ht Hs Hc has_fma x Hx.
destruct (tan_correct_point (side_tight p) (tan_tight_c p Ht) (sin_tight_c p Hs) (cos_tight_c p Hc)
  has_fma x Hx) as (y & Ey & T).
destruct (tan_wider p (side_tight p) (tan_tight_out p Ht) (quadrant_tight p Hs Hc) has_fma x y Ey)
  as (y' & Ey' & W).
exists y'. split; [exact Ey' | exact (tightest_wider _ _ _ T W)].
Qed.

Theorem pow_encloses_side :
  forall p, pow_s (p_pow p) ->
  forall first_min first_max x y, valid x -> valid y ->
  encloses (image2_set pow_dom Rpow x y) (Interval.pow p first_min first_max x y).
Proof.
intros p H first_min first_max x y Hx Hy.
exact (tightest_wider _ _ _
  (pow_correct_point (side_tight p) (pow_tight_c p H) first_min first_max x y Hx Hy)
  (pow_wider p (side_tight p) (pow_tight_out p H) first_min first_max x y)).
Qed.

Theorem pown_encloses_side :
  forall p, pown_s (p_pown p) ->
  forall n x, is_i32 n -> valid x ->
  exists y, Interval.powi p n x = Some y /\
    encloses (image_dom (pown_dom n) (fun r => powerRZ r n) x) y.
Proof.
intros p H n x Hn Hx.
destruct (pown_correct_point (side_tight p) (pown_tight_c p H) n x Hn Hx) as (y & Ey & T).
destruct (pown_wider p (side_tight p) (pown_tight_out p H) n x y Ey) as (y' & Ey' & W).
exists y'. split; [exact Ey' | exact (tightest_wider _ _ _ T W)].
Qed.
