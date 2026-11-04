(** * A theorem stated for a record [point]

    [exp_correct] stated for every record [p] whose fields satisfy the
    parts of [Contract.v] that it needs, through [of_point p]
    ([OfPoint.v]). No other theorem is restated this way. Another theorem
    about the elementary functions would carry over the same way if its
    only hypotheses on [m] are [get_d_ok] and hypotheses [<f>_ok] of
    [Mpfr.v], at any exponent range with [range_ok], and its conclusion
    uses [m] only through [mpfr_point m]: at the exponent range of [f64]
    ([range_ok_f64]), with [of_point_get_d_ok], the theorems
    [of_point_<f>_ok] and [mpfr_point_of_point]. *)

From Stdlib Require Import ZArith Reals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Elem Contract
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
