(** * Theorems stated for a record [point]

    [exp_correct], [exp2_correct], [exp10_correct], [sinh_correct],
    [tanh_correct] and [cosh_correct] stated for every record [p] whose
    fields satisfy the parts of [Contract.v] that they need, through
    [of_point p] ([OfPoint.v]). No other theorem is restated this way.
    [DyPoint.v] applies them to the dyadic kernel's functions. Another
    theorem about the elementary functions would carry over the same way
    if its only hypotheses on [m] are [get_d_ok] and hypotheses [<f>_ok]
    of [Mpfr.v], at any exponent range with [range_ok], and its conclusion
    uses [m] only through [mpfr_point m]: at the exponent range of [f64]
    ([range_ok_f64]), with [of_point_get_d_ok], the theorems
    [of_point_<f>_ok] and [mpfr_point_of_point]. *)

From Stdlib Require Import ZArith Reals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Elem Cosh Contract
  OfPointCore OfPoint OfPointElem.

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
