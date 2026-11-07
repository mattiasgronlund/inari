(** * Theorems stated for a record [point]

    [exp_correct], [exp2_correct], [exp10_correct], [sinh_correct],
    [tanh_correct], [cosh_correct], [ln_correct], [log2_correct],
    [log10_correct], [asinh_correct], [acosh_correct], [atanh_correct],
    [atan_correct], [asin_correct], [acos_correct], [atan2_correct],
    [sin_correct], [cos_correct] and [tan_correct] stated for every
    record [p] whose fields satisfy the parts of [Contract.v] that they
    need, through [of_point p] ([OfPoint.v]). No other theorem is
    restated this way.
    [DyPoint.v] applies them to the dyadic kernel's functions. Another
    theorem about the elementary functions would carry over the same way
    if its only hypotheses on [m] are [get_d_ok] and hypotheses [<f>_ok]
    of [Mpfr.v], at any exponent range with [range_ok], and its conclusion
    uses [m] only through [mpfr_point m]: at the exponent range of [f64]
    ([range_ok_f64]), with [of_point_get_d_ok], the theorems
    [of_point_<f>_ok] and [mpfr_point_of_point]. *)

From Stdlib Require Import ZArith Reals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Elem Cosh Atanh ClosedDom Atan2
  Contract OfPointCore OfPoint OfPointElem OfPointPow.
From Inari Require Sin Cos Tan.

Open Scope R_scope.

Theorem exp_correct_point :
  forall p, exp_c (p_exp p) ->
  forall x, valid x -> is_tightest (image_dom real_dom exp x) (Interval.exp p x).
Proof.
intros p Hp x Hx. rewrite <- (mpfr_point_of_point p).
exact (exp_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_exp_ok p Hp) x Hx).
Qed.

Theorem exp2_correct_point :
  forall p, exp2_c (p_exp2 p) ->
  forall x, valid x -> is_tightest (image_dom real_dom Rexp2 x) (Interval.exp2 p x).
Proof.
intros p Hp x Hx. rewrite <- (mpfr_point_of_point p).
exact (exp2_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_exp2_ok p Hp) x Hx).
Qed.

Theorem exp10_correct_point :
  forall p, exp10_c (p_exp10 p) ->
  forall x, valid x -> is_tightest (image_dom real_dom Rexp10 x) (Interval.exp10 p x).
Proof.
intros p Hp x Hx. rewrite <- (mpfr_point_of_point p).
exact (exp10_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_exp10_ok p Hp) x Hx).
Qed.

Theorem sinh_correct_point :
  forall p, sinh_c (p_sinh p) ->
  forall x, valid x -> is_tightest (image_dom real_dom sinh x) (Interval.sinh p x).
Proof.
intros p Hp x Hx. rewrite <- (mpfr_point_of_point p).
exact (sinh_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_sinh_ok p Hp) x Hx).
Qed.

Theorem tanh_correct_point :
  forall p, tanh_c (p_tanh p) ->
  forall x, valid x -> is_tightest (image_dom real_dom tanh x) (Interval.tanh p x).
Proof.
intros p Hp x Hx. rewrite <- (mpfr_point_of_point p).
exact (tanh_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_tanh_ok p Hp) x Hx).
Qed.

Theorem cosh_correct_point :
  forall p, cosh_c (p_cosh p) ->
  forall first x, valid x -> is_tightest (image_dom real_dom cosh x) (Interval.cosh p first x).
Proof.
intros p Hp first x Hx. rewrite <- (mpfr_point_of_point p).
exact (cosh_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_cosh_ok p Hp) first x Hx).
Qed.

Theorem ln_correct_point :
  forall p, ln_c (p_ln p) ->
  forall x, valid x -> is_tightest (image_dom log_dom ln x) (Interval.ln p x).
Proof.
intros p Hp x Hx. rewrite <- (mpfr_point_of_point p).
exact (ln_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_ln_ok p Hp) x Hx).
Qed.

Theorem log2_correct_point :
  forall p, log2_c (p_log2 p) ->
  forall x, valid x -> is_tightest (image_dom log_dom Rlog2 x) (Interval.log2 p x).
Proof.
intros p Hp x Hx. rewrite <- (mpfr_point_of_point p).
exact (log2_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_log2_ok p Hp) x Hx).
Qed.

Theorem log10_correct_point :
  forall p, log10_c (p_log10 p) ->
  forall x, valid x -> is_tightest (image_dom log_dom Rlog10 x) (Interval.log10 p x).
Proof.
intros p Hp x Hx. rewrite <- (mpfr_point_of_point p).
exact (log10_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_log10_ok p Hp) x Hx).
Qed.

Theorem asinh_correct_point :
  forall p, asinh_c (p_asinh p) ->
  forall x, valid x -> is_tightest (image_dom real_dom arcsinh x) (Interval.asinh p x).
Proof.
intros p Hp x Hx. rewrite <- (mpfr_point_of_point p).
exact (asinh_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_asinh_ok p Hp) x Hx).
Qed.

Theorem acosh_correct_point :
  forall p, acosh_c (p_acosh p) ->
  forall x, valid x -> is_tightest (image_dom acosh_dom Racosh x) (Interval.acosh p x).
Proof.
intros p Hp x Hx. rewrite <- (mpfr_point_of_point p).
exact (acosh_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_acosh_ok p Hp) x Hx).
Qed.

Theorem atanh_correct_point :
  forall p, atanh_c (p_atanh p) ->
  forall x, valid x -> is_tightest (image_dom atanh_dom Ratanh x) (Interval.atanh p x).
Proof.
intros p Hp x Hx. rewrite <- (mpfr_point_of_point p).
exact (atanh_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_atanh_ok p Hp) x Hx).
Qed.

Theorem atan_correct_point :
  forall p, atan_c (p_atan p) ->
  forall x, valid x -> is_tightest (image_dom real_dom atan x) (Interval.atan p x).
Proof.
intros p Hp x Hx. rewrite <- (mpfr_point_of_point p).
exact (atan_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_atan_ok p Hp) x Hx).
Qed.

Theorem asin_correct_point :
  forall p, asin_c (p_asin p) ->
  forall x, valid x -> is_tightest (image_dom asin_dom asin x) (Interval.asin p x).
Proof.
intros p Hp x Hx. rewrite <- (mpfr_point_of_point p).
exact (asin_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_asin_ok p Hp) x Hx).
Qed.

Theorem acos_correct_point :
  forall p, acos_c (p_acos p) ->
  forall x, valid x -> is_tightest (image_dom acos_dom acos x) (Interval.acos p x).
Proof.
intros p Hp x Hx. rewrite <- (mpfr_point_of_point p).
exact (acos_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_acos_ok p Hp) x Hx).
Qed.

Theorem atan2_correct_point :
  forall p, atan2_c (p_atan2 p) ->
  forall y x, valid y -> valid x ->
  exists z, Interval.atan2 p y x = Some z /\ is_tightest (image2_set atan2_dom Ratan2 y x) z.
Proof.
intros p Hp y x Hy Hx. rewrite <- (mpfr_point_of_point p).
exact (atan2_correct (-1073) 1024 (of_point p) y x range_ok_f64 (of_point_get_d_ok p)
  (of_point_atan2_ok p Hp) Hy Hx).
Qed.

Theorem sin_correct_point :
  forall p, sin_c (p_sin p) -> cos_c (p_cos p) ->
  forall has_fma first x, valid x ->
  exists y, Interval.sin p has_fma first x = Some y /\ is_tightest (image_dom real_dom sin x) y.
Proof.
intros p Hs Hc has_fma first x Hx. rewrite <- (mpfr_point_of_point p).
exact (Sin.sin_correct (-1073) 1024 (of_point p) has_fma first x range_ok_f64
  (of_point_get_d_ok p) (of_point_sin_ok p Hs) (of_point_cos_ok p Hc) Hx).
Qed.

Theorem cos_correct_point :
  forall p, cos_c (p_cos p) -> sin_c (p_sin p) ->
  forall has_fma first x, valid x ->
  exists y, Interval.cos p has_fma first x = Some y /\ is_tightest (image_dom real_dom cos x) y.
Proof.
intros p Hc Hs has_fma first x Hx. rewrite <- (mpfr_point_of_point p).
exact (Cos.cos_correct (-1073) 1024 (of_point p) has_fma first x range_ok_f64
  (of_point_get_d_ok p) (of_point_cos_ok p Hc) (of_point_sin_ok p Hs) Hx).
Qed.

Theorem tan_correct_point :
  forall p, tan_c (p_tan p) -> sin_c (p_sin p) -> cos_c (p_cos p) ->
  forall has_fma x, valid x ->
  exists y, Interval.tan p has_fma x = Some y /\ is_tightest (image_dom tan_dom tan x) y.
Proof.
intros p Ht Hs Hc has_fma x Hx. rewrite <- (mpfr_point_of_point p).
exact (Tan.tan_correct (-1073) 1024 (of_point p) has_fma x range_ok_f64
  (of_point_get_d_ok p) (of_point_tan_ok p Ht) (of_point_sin_ok p Hs) (of_point_cos_ok p Hc) Hx).
Qed.
