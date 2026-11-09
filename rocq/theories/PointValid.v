(** * The elementary functions return [valid] intervals, for a record [point]

    [exp_valid], [dec_exp_valid] and the other theorems of [ValidElem.v]
    stated for every record [p] whose fields satisfy the parts of
    [Contract.v] that they need, by the recipe of [PointTheorems.v]:
    apply the theorem at [of_point p] and the exponent range of [f64],
    and rewrite with [mpfr_point_of_point]. [pown_valid_point] and
    [dec_pown_valid_point] are those of [powi_valid] and [dec_powi_valid].
    [Valid.v] applies them to the dyadic kernel's functions, in the
    constructors [made_kernel_exp] and the others. *)

From Stdlib Require Import ZArith Reals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr ValidElem Contract OfPointCore OfPoint
  OfPointElem OfPointPow.

Theorem exp_valid_point :
  forall p, exp_c (p_exp p) ->
  forall x, valid x -> valid (Interval.exp p x).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (exp_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_exp_ok p Hp)).
Qed.

Theorem dec_exp_valid_point :
  forall p, exp_c (p_exp p) ->
  forall x, valid (itv x) -> valid (itv (DecInterval.exp p x)).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (dec_exp_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_exp_ok p Hp)).
Qed.

Theorem exp2_valid_point :
  forall p, exp2_c (p_exp2 p) ->
  forall x, valid x -> valid (Interval.exp2 p x).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (exp2_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_exp2_ok p Hp)).
Qed.

Theorem dec_exp2_valid_point :
  forall p, exp2_c (p_exp2 p) ->
  forall x, valid (itv x) -> valid (itv (DecInterval.exp2 p x)).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (dec_exp2_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_exp2_ok p Hp)).
Qed.

Theorem exp10_valid_point :
  forall p, exp10_c (p_exp10 p) ->
  forall x, valid x -> valid (Interval.exp10 p x).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (exp10_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_exp10_ok p Hp)).
Qed.

Theorem dec_exp10_valid_point :
  forall p, exp10_c (p_exp10 p) ->
  forall x, valid (itv x) -> valid (itv (DecInterval.exp10 p x)).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (dec_exp10_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_exp10_ok p Hp)).
Qed.

Theorem sinh_valid_point :
  forall p, sinh_c (p_sinh p) ->
  forall x, valid x -> valid (Interval.sinh p x).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (sinh_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_sinh_ok p Hp)).
Qed.

Theorem dec_sinh_valid_point :
  forall p, sinh_c (p_sinh p) ->
  forall x, valid (itv x) -> valid (itv (DecInterval.sinh p x)).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (dec_sinh_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_sinh_ok p Hp)).
Qed.

Theorem tanh_valid_point :
  forall p, tanh_c (p_tanh p) ->
  forall x, valid x -> valid (Interval.tanh p x).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (tanh_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_tanh_ok p Hp)).
Qed.

Theorem dec_tanh_valid_point :
  forall p, tanh_c (p_tanh p) ->
  forall x, valid (itv x) -> valid (itv (DecInterval.tanh p x)).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (dec_tanh_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_tanh_ok p Hp)).
Qed.

Theorem cosh_valid_point :
  forall p, cosh_c (p_cosh p) ->
  forall first x, valid x -> valid (Interval.cosh p first x).
Proof.
intros p Hp first x. rewrite <- (mpfr_point_of_point p).
exact (cosh_valid (-1073) 1024 (of_point p) first x range_ok_f64 (of_point_get_d_ok p)
  (of_point_cosh_ok p Hp)).
Qed.

Theorem dec_cosh_valid_point :
  forall p, cosh_c (p_cosh p) ->
  forall first x, valid (itv x) -> valid (itv (DecInterval.cosh p first x)).
Proof.
intros p Hp first x. rewrite <- (mpfr_point_of_point p).
exact (dec_cosh_valid (-1073) 1024 (of_point p) first x range_ok_f64 (of_point_get_d_ok p)
  (of_point_cosh_ok p Hp)).
Qed.

Theorem ln_valid_point :
  forall p, ln_c (p_ln p) ->
  forall x, valid x -> valid (Interval.ln p x).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (ln_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_ln_ok p Hp)).
Qed.

Theorem dec_ln_valid_point :
  forall p, ln_c (p_ln p) ->
  forall x, valid (itv x) -> valid (itv (DecInterval.ln p x)).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (dec_ln_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_ln_ok p Hp)).
Qed.

Theorem log2_valid_point :
  forall p, log2_c (p_log2 p) ->
  forall x, valid x -> valid (Interval.log2 p x).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (log2_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_log2_ok p Hp)).
Qed.

Theorem dec_log2_valid_point :
  forall p, log2_c (p_log2 p) ->
  forall x, valid (itv x) -> valid (itv (DecInterval.log2 p x)).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (dec_log2_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_log2_ok p Hp)).
Qed.

Theorem log10_valid_point :
  forall p, log10_c (p_log10 p) ->
  forall x, valid x -> valid (Interval.log10 p x).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (log10_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_log10_ok p Hp)).
Qed.

Theorem dec_log10_valid_point :
  forall p, log10_c (p_log10 p) ->
  forall x, valid (itv x) -> valid (itv (DecInterval.log10 p x)).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (dec_log10_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_log10_ok p Hp)).
Qed.

Theorem asinh_valid_point :
  forall p, asinh_c (p_asinh p) ->
  forall x, valid x -> valid (Interval.asinh p x).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (asinh_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_asinh_ok p Hp)).
Qed.

Theorem dec_asinh_valid_point :
  forall p, asinh_c (p_asinh p) ->
  forall x, valid (itv x) -> valid (itv (DecInterval.asinh p x)).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (dec_asinh_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_asinh_ok p Hp)).
Qed.

Theorem acosh_valid_point :
  forall p, acosh_c (p_acosh p) ->
  forall x, valid x -> valid (Interval.acosh p x).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (acosh_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_acosh_ok p Hp)).
Qed.

Theorem dec_acosh_valid_point :
  forall p, acosh_c (p_acosh p) ->
  forall x, valid (itv x) -> valid (itv (DecInterval.acosh p x)).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (dec_acosh_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_acosh_ok p Hp)).
Qed.

Theorem atanh_valid_point :
  forall p, atanh_c (p_atanh p) ->
  forall x, valid x -> valid (Interval.atanh p x).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (atanh_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_atanh_ok p Hp)).
Qed.

Theorem dec_atanh_valid_point :
  forall p, atanh_c (p_atanh p) ->
  forall x, valid (itv x) -> valid (itv (DecInterval.atanh p x)).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (dec_atanh_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_atanh_ok p Hp)).
Qed.

Theorem atan_valid_point :
  forall p, atan_c (p_atan p) ->
  forall x, valid x -> valid (Interval.atan p x).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (atan_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_atan_ok p Hp)).
Qed.

Theorem dec_atan_valid_point :
  forall p, atan_c (p_atan p) ->
  forall x, valid (itv x) -> valid (itv (DecInterval.atan p x)).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (dec_atan_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_atan_ok p Hp)).
Qed.

Theorem asin_valid_point :
  forall p, asin_c (p_asin p) ->
  forall x, valid x -> valid (Interval.asin p x).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (asin_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_asin_ok p Hp)).
Qed.

Theorem dec_asin_valid_point :
  forall p, asin_c (p_asin p) ->
  forall x, valid (itv x) -> valid (itv (DecInterval.asin p x)).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (dec_asin_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_asin_ok p Hp)).
Qed.

Theorem acos_valid_point :
  forall p, acos_c (p_acos p) ->
  forall x, valid x -> valid (Interval.acos p x).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (acos_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_acos_ok p Hp)).
Qed.

Theorem dec_acos_valid_point :
  forall p, acos_c (p_acos p) ->
  forall x, valid (itv x) -> valid (itv (DecInterval.acos p x)).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (dec_acos_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_acos_ok p Hp)).
Qed.

Theorem atan2_valid_point :
  forall p, atan2_c (p_atan2 p) ->
  forall y x z, valid y -> valid x -> Interval.atan2 p y x = Some z -> valid z.
Proof.
intros p Hp y x z. rewrite <- (mpfr_point_of_point p).
exact (atan2_valid (-1073) 1024 (of_point p) y x z range_ok_f64 (of_point_get_d_ok p)
  (of_point_atan2_ok p Hp)).
Qed.

Theorem dec_atan2_valid_point :
  forall p, atan2_c (p_atan2 p) ->
  forall y x w, valid (itv y) -> valid (itv x) -> DecInterval.atan2 p y x = Some w ->
  valid (itv w).
Proof.
intros p Hp y x w. rewrite <- (mpfr_point_of_point p).
exact (dec_atan2_valid (-1073) 1024 (of_point p) y x w range_ok_f64 (of_point_get_d_ok p)
  (of_point_atan2_ok p Hp)).
Qed.

Theorem sin_valid_point :
  forall p, sin_c (p_sin p) -> cos_c (p_cos p) ->
  forall has_fma first x y, valid x -> Interval.sin p has_fma first x = Some y -> valid y.
Proof.
intros p Hs Hc has_fma first x y. rewrite <- (mpfr_point_of_point p).
exact (sin_valid (-1073) 1024 (of_point p) has_fma first x y range_ok_f64
  (of_point_get_d_ok p) (of_point_sin_ok p Hs) (of_point_cos_ok p Hc)).
Qed.

Theorem dec_sin_valid_point :
  forall p, sin_c (p_sin p) -> cos_c (p_cos p) ->
  forall has_fma first x y, valid (itv x) -> DecInterval.sin p has_fma first x = Some y ->
  valid (itv y).
Proof.
intros p Hs Hc has_fma first x y. rewrite <- (mpfr_point_of_point p).
exact (dec_sin_valid (-1073) 1024 (of_point p) has_fma first x y range_ok_f64
  (of_point_get_d_ok p) (of_point_sin_ok p Hs) (of_point_cos_ok p Hc)).
Qed.

Theorem cos_valid_point :
  forall p, cos_c (p_cos p) -> sin_c (p_sin p) ->
  forall has_fma first x y, valid x -> Interval.cos p has_fma first x = Some y -> valid y.
Proof.
intros p Hc Hs has_fma first x y. rewrite <- (mpfr_point_of_point p).
exact (cos_valid (-1073) 1024 (of_point p) has_fma first x y range_ok_f64
  (of_point_get_d_ok p) (of_point_cos_ok p Hc) (of_point_sin_ok p Hs)).
Qed.

Theorem dec_cos_valid_point :
  forall p, cos_c (p_cos p) -> sin_c (p_sin p) ->
  forall has_fma first x y, valid (itv x) -> DecInterval.cos p has_fma first x = Some y ->
  valid (itv y).
Proof.
intros p Hc Hs has_fma first x y. rewrite <- (mpfr_point_of_point p).
exact (dec_cos_valid (-1073) 1024 (of_point p) has_fma first x y range_ok_f64
  (of_point_get_d_ok p) (of_point_cos_ok p Hc) (of_point_sin_ok p Hs)).
Qed.

Theorem tan_valid_point :
  forall p, tan_c (p_tan p) -> sin_c (p_sin p) -> cos_c (p_cos p) ->
  forall has_fma x y, valid x -> Interval.tan p has_fma x = Some y -> valid y.
Proof.
intros p Ht Hs Hc has_fma x y. rewrite <- (mpfr_point_of_point p).
exact (tan_valid (-1073) 1024 (of_point p) has_fma x y range_ok_f64
  (of_point_get_d_ok p) (of_point_tan_ok p Ht) (of_point_sin_ok p Hs) (of_point_cos_ok p Hc)).
Qed.

Theorem dec_tan_valid_point :
  forall p, tan_c (p_tan p) -> sin_c (p_sin p) -> cos_c (p_cos p) ->
  forall has_fma x y, valid (itv x) -> DecInterval.tan p has_fma x = Some y -> valid (itv y).
Proof.
intros p Ht Hs Hc has_fma x y. rewrite <- (mpfr_point_of_point p).
exact (dec_tan_valid (-1073) 1024 (of_point p) has_fma x y range_ok_f64
  (of_point_get_d_ok p) (of_point_tan_ok p Ht) (of_point_sin_ok p Hs) (of_point_cos_ok p Hc)).
Qed.

Theorem pow_valid_point :
  forall p, pow_c (p_pow p) ->
  forall first_min first_max x y, valid x -> valid y ->
  valid (Interval.pow p first_min first_max x y).
Proof.
intros p Hp f1 f2 x y. rewrite <- (mpfr_point_of_point p).
exact (pow_valid (-1073) 1024 (of_point p) f1 f2 x y range_ok_f64 (of_point_get_d_ok p)
  (of_point_pow_ok p Hp)).
Qed.

Theorem dec_pow_valid_point :
  forall p, pow_c (p_pow p) ->
  forall first_min first_max x y, valid (itv x) -> valid (itv y) ->
  valid (itv (DecInterval.pow p first_min first_max x y)).
Proof.
intros p Hp f1 f2 x y. rewrite <- (mpfr_point_of_point p).
exact (dec_pow_valid (-1073) 1024 (of_point p) f1 f2 x y range_ok_f64 (of_point_get_d_ok p)
  (of_point_pow_ok p Hp)).
Qed.

Theorem pown_valid_point :
  forall p, pown_c (p_pown p) ->
  forall n x y, is_i32 n -> valid x -> Interval.powi p n x = Some y -> valid y.
Proof.
intros p Hp n x y. rewrite <- (mpfr_point_of_point p).
exact (powi_valid (-1073) 1024 (of_point p) n x y range_ok_f64 (of_point_get_d_ok p)
  (of_point_pown_ok p Hp)).
Qed.

Theorem dec_pown_valid_point :
  forall p, pown_c (p_pown p) ->
  forall n x y, is_i32 n -> valid (itv x) -> DecInterval.powi p n x = Some y -> valid (itv y).
Proof.
intros p Hp n x y. rewrite <- (mpfr_point_of_point p).
exact (dec_powi_valid (-1073) 1024 (of_point p) n x y range_ok_f64 (of_point_get_d_ok p)
  (of_point_pown_ok p Hp)).
Qed.

Theorem cbrt_valid_point :
  forall p, cbrt_c (p_cbrt p) ->
  forall x, valid x -> valid (Interval.cbrt p x).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (cbrt_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_cbrt_ok p Hp)).
Qed.

Theorem dec_cbrt_valid_point :
  forall p, cbrt_c (p_cbrt p) ->
  forall x, valid (itv x) -> valid (itv (DecInterval.cbrt p x)).
Proof.
intros p Hp x. rewrite <- (mpfr_point_of_point p).
exact (dec_cbrt_valid (-1073) 1024 (of_point p) x range_ok_f64 (of_point_get_d_ok p)
  (of_point_cbrt_ok p Hp)).
Qed.

Theorem hypot_valid_point :
  forall p, hypot_c (p_hypot p) ->
  forall x y z, valid x -> valid y -> Interval.hypot p x y = Some z -> valid z.
Proof.
intros p Hp x y z. rewrite <- (mpfr_point_of_point p).
exact (hypot_valid (-1073) 1024 (of_point p) x y z range_ok_f64 (of_point_get_d_ok p)
  (of_point_hypot_ok p Hp)).
Qed.

Theorem dec_hypot_valid_point :
  forall p, hypot_c (p_hypot p) ->
  forall x y w, valid (itv x) -> valid (itv y) -> DecInterval.hypot p x y = Some w ->
  valid (itv w).
Proof.
intros p Hp x y w. rewrite <- (mpfr_point_of_point p).
exact (dec_hypot_valid (-1073) 1024 (of_point p) x y w range_ok_f64 (of_point_get_d_ok p)
  (of_point_hypot_ok p Hp)).
Qed.
