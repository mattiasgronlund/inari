(** * The decorated elementary functions stated for a record [point]

    [dec_exp_correct] and the other theorems about the decorated
    elementary functions ([Elem.v], [Cosh.v], [Atanh.v], [ClosedDom.v],
    [Atan2.v], [Sin.v], [Cos.v], [Tan.v], [Pow.v] and [Powi.v]) stated
    for every record [p] whose fields satisfy the parts of [Contract.v]
    that they need, by the recipe of [PointTheorems.v]: apply the theorem
    at [of_point p] and the exponent range of [f64], and rewrite with
    [mpfr_point_of_point]. [dec_pown_correct_point] is that of
    [dec_powi_correct]. [DyPointDec.v] applies them to the dyadic
    kernel's functions. *)

From Stdlib Require Import ZArith Reals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr ComCommon Elem Cosh Atanh ClosedDom Atan2
  Contract OfPointCore OfPoint OfPointElem OfPointPow.
From Inari Require Sin Cos Tan Pow Powi.

Open Scope R_scope.

Theorem dec_exp_correct_point :
  forall p, exp_c (p_exp p) ->
  forall x, valid (itv x) -> com_common x ->
  let y := DecInterval.exp p x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom exp (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d exp (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros p Hp. rewrite <- (mpfr_point_of_point p).
exact (dec_exp_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_exp_ok p Hp)).
Qed.

Theorem dec_exp2_correct_point :
  forall p, exp2_c (p_exp2 p) ->
  forall x, valid (itv x) -> com_common x ->
  let y := DecInterval.exp2 p x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom Rexp2 (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d Rexp2 (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros p Hp. rewrite <- (mpfr_point_of_point p).
exact (dec_exp2_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_exp2_ok p Hp)).
Qed.

Theorem dec_exp10_correct_point :
  forall p, exp10_c (p_exp10 p) ->
  forall x, valid (itv x) -> com_common x ->
  let y := DecInterval.exp10 p x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom Rexp10 (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d Rexp10 (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros p Hp. rewrite <- (mpfr_point_of_point p).
exact (dec_exp10_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_exp10_ok p Hp)).
Qed.

Theorem dec_sinh_correct_point :
  forall p, sinh_c (p_sinh p) ->
  forall x, valid (itv x) ->
  let y := DecInterval.sinh p x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom sinh (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d sinh (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros p Hp. rewrite <- (mpfr_point_of_point p).
exact (dec_sinh_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_sinh_ok p Hp)).
Qed.

Theorem dec_tanh_correct_point :
  forall p, tanh_c (p_tanh p) ->
  forall x, valid (itv x) -> com_common x ->
  let y := DecInterval.tanh p x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom tanh (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d tanh (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros p Hp. rewrite <- (mpfr_point_of_point p).
exact (dec_tanh_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_tanh_ok p Hp)).
Qed.

Theorem dec_cosh_correct_point :
  forall p, cosh_c (p_cosh p) ->
  forall first x, valid (itv x) ->
  let y := DecInterval.cosh p first x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom cosh (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d cosh (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros p Hp. rewrite <- (mpfr_point_of_point p).
exact (dec_cosh_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_cosh_ok p Hp)).
Qed.

Theorem dec_ln_correct_point :
  forall p, ln_c (p_ln p) ->
  forall x, valid (itv x) ->
  let y := DecInterval.ln p x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom log_dom ln (itv x)) (itv y) /\
    exists d, strongest_dom log_dom d ln (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros p Hp. rewrite <- (mpfr_point_of_point p).
exact (dec_ln_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_ln_ok p Hp)).
Qed.

Theorem dec_log2_correct_point :
  forall p, log2_c (p_log2 p) ->
  forall x, valid (itv x) ->
  let y := DecInterval.log2 p x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom log_dom Rlog2 (itv x)) (itv y) /\
    exists d, strongest_dom log_dom d Rlog2 (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros p Hp. rewrite <- (mpfr_point_of_point p).
exact (dec_log2_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_log2_ok p Hp)).
Qed.

Theorem dec_log10_correct_point :
  forall p, log10_c (p_log10 p) ->
  forall x, valid (itv x) ->
  let y := DecInterval.log10 p x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom log_dom Rlog10 (itv x)) (itv y) /\
    exists d, strongest_dom log_dom d Rlog10 (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros p Hp. rewrite <- (mpfr_point_of_point p).
exact (dec_log10_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_log10_ok p Hp)).
Qed.

Theorem dec_asinh_correct_point :
  forall p, asinh_c (p_asinh p) ->
  forall x, valid (itv x) ->
  let y := DecInterval.asinh p x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom arcsinh (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d arcsinh (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros p Hp. rewrite <- (mpfr_point_of_point p).
exact (dec_asinh_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_asinh_ok p Hp)).
Qed.

Theorem dec_acosh_correct_point :
  forall p, acosh_c (p_acosh p) ->
  forall x, valid (itv x) ->
  let y := DecInterval.acosh p x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom acosh_dom Racosh (itv x)) (itv y) /\
    exists d, strongest_dom acosh_dom d Racosh (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros p Hp. rewrite <- (mpfr_point_of_point p).
exact (dec_acosh_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_acosh_ok p Hp)).
Qed.

Theorem dec_atanh_correct_point :
  forall p, atanh_c (p_atanh p) ->
  forall x, valid (itv x) ->
  let y := DecInterval.atanh p x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom atanh_dom Ratanh (itv x)) (itv y) /\
    exists d, strongest_dom atanh_dom d Ratanh (itv x) (itv y) /\
      dec y = dec_min d (dec x).
Proof.
intros p Hp. rewrite <- (mpfr_point_of_point p).
exact (dec_atanh_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_atanh_ok p Hp)).
Qed.

Theorem dec_atan_correct_point :
  forall p, atan_c (p_atan p) ->
  forall x, valid (itv x) -> com_common x ->
  let y := DecInterval.atan p x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom atan (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d atan (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros p Hp. rewrite <- (mpfr_point_of_point p).
exact (dec_atan_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_atan_ok p Hp)).
Qed.

Theorem dec_asin_correct_point :
  forall p, asin_c (p_asin p) ->
  forall x, valid (itv x) ->
  let y := DecInterval.asin p x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom asin_dom asin (itv x)) (itv y) /\
    exists d, strongest_dom asin_dom d asin (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros p Hp. rewrite <- (mpfr_point_of_point p).
exact (dec_asin_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_asin_ok p Hp)).
Qed.

Theorem dec_acos_correct_point :
  forall p, acos_c (p_acos p) ->
  forall x, valid (itv x) ->
  let y := DecInterval.acos p x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom acos_dom acos (itv x)) (itv y) /\
    exists d, strongest_dom acos_dom d acos (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros p Hp. rewrite <- (mpfr_point_of_point p).
exact (dec_acos_correct (-1073) 1024 (of_point p) range_ok_f64 (of_point_get_d_ok p)
  (of_point_acos_ok p Hp)).
Qed.

Theorem dec_atan2_correct_point :
  forall p, atan2_c (p_atan2 p) ->
  forall y x, valid (itv y) -> valid (itv x) -> com_common y -> com_common x ->
  exists w, DecInterval.atan2 p y x = Some w /\
    if DecInterval.is_nai y || DecInterval.is_nai x then w = DecInterval.NAI
    else
      is_tightest (image2_set atan2_dom Ratan2 (itv y) (itv x)) (itv w) /\
      exists d, strongest2_set atan2_dom d Ratan2 (itv y) (itv x) (itv w) /\
        dec w = dec_min d (dec_min (dec y) (dec x)).
Proof.
intros p Hp y x. rewrite <- (mpfr_point_of_point p).
exact (dec_atan2_correct (-1073) 1024 (of_point p) y x range_ok_f64 (of_point_get_d_ok p)
  (of_point_atan2_ok p Hp)).
Qed.

Theorem dec_sin_correct_point :
  forall p, sin_c (p_sin p) -> cos_c (p_cos p) ->
  forall has_fma first x, valid (itv x) -> com_common x ->
  exists y, DecInterval.sin p has_fma first x = Some y /\
    if DecInterval.is_nai x then y = DecInterval.NAI
    else
      is_tightest (image_dom real_dom sin (itv x)) (itv y) /\
      exists d, strongest_dom real_dom d sin (itv x) (itv y) /\
        dec y = dec_min d (dec x).
Proof.
intros p Hs Hc has_fma first x. rewrite <- (mpfr_point_of_point p).
exact (Sin.dec_sin_correct (-1073) 1024 (of_point p) has_fma first x range_ok_f64
  (of_point_get_d_ok p) (of_point_sin_ok p Hs) (of_point_cos_ok p Hc)).
Qed.

Theorem dec_cos_correct_point :
  forall p, cos_c (p_cos p) -> sin_c (p_sin p) ->
  forall has_fma first x, valid (itv x) -> com_common x ->
  exists y, DecInterval.cos p has_fma first x = Some y /\
    if DecInterval.is_nai x then y = DecInterval.NAI
    else
      is_tightest (image_dom real_dom cos (itv x)) (itv y) /\
      exists d, strongest_dom real_dom d cos (itv x) (itv y) /\
        dec y = dec_min d (dec x).
Proof.
intros p Hc Hs has_fma first x. rewrite <- (mpfr_point_of_point p).
exact (Cos.dec_cos_correct (-1073) 1024 (of_point p) has_fma first x range_ok_f64
  (of_point_get_d_ok p) (of_point_cos_ok p Hc) (of_point_sin_ok p Hs)).
Qed.

Theorem dec_tan_correct_point :
  forall p, tan_c (p_tan p) -> sin_c (p_sin p) -> cos_c (p_cos p) ->
  forall has_fma x, valid (itv x) ->
  exists y, DecInterval.tan p has_fma x = Some y /\
    if DecInterval.is_nai x then y = DecInterval.NAI
    else
      is_tightest (image_dom tan_dom tan (itv x)) (itv y) /\
      exists d, strongest_dom tan_dom d tan (itv x) (itv y) /\
        dec y = dec_min d (dec x).
Proof.
intros p Ht Hs Hc has_fma x. rewrite <- (mpfr_point_of_point p).
exact (Tan.dec_tan_correct (-1073) 1024 (of_point p) has_fma x range_ok_f64
  (of_point_get_d_ok p) (of_point_tan_ok p Ht) (of_point_sin_ok p Hs) (of_point_cos_ok p Hc)).
Qed.

Theorem dec_pow_correct_point :
  forall p, pow_c (p_pow p) ->
  forall first_min first_max x y,
  valid (itv x) -> valid (itv y) -> com_common x -> com_common y ->
  let z := DecInterval.pow p first_min first_max x y in
  if DecInterval.is_nai x || DecInterval.is_nai y then z = DecInterval.NAI
  else
    is_tightest (image2_set pow_dom Rpow (itv x) (itv y)) (itv z) /\
    exists d, strongest2_set pow_dom d Rpow (itv x) (itv y) (itv z) /\
      dec z = dec_min d (dec_min (dec x) (dec y)).
Proof.
intros p Hp f1 f2 x y. rewrite <- (mpfr_point_of_point p).
exact (Pow.dec_pow_correct (-1073) 1024 (of_point p) f1 f2 x y range_ok_f64
  (of_point_get_d_ok p) (of_point_pow_ok p Hp)).
Qed.

Theorem dec_pown_correct_point :
  forall p, pown_c (p_pown p) ->
  forall n x, is_i32 n -> valid (itv x) -> (0 < n)%Z \/ com_common x ->
  exists y, DecInterval.powi p n x = Some y /\
    if DecInterval.is_nai x then y = DecInterval.NAI
    else
      is_tightest (image_dom (pown_dom n) (fun r => powerRZ r n) (itv x)) (itv y) /\
      exists d, strongest_dom (pown_dom n) d (fun r => powerRZ r n) (itv x) (itv y) /\
        dec y = dec_min d (dec x).
Proof.
intros p Hp n x. rewrite <- (mpfr_point_of_point p).
exact (Powi.dec_powi_correct (-1073) 1024 (of_point p) n x range_ok_f64 (of_point_get_d_ok p)
  (of_point_pown_ok p Hp)).
Qed.
