(** * The dyadic kernel's decorated elementary functions

    The theorems of [PointDec.v] applied to [kernel_point] of [DyPoint.v],
    with the contracts [k_exp_c] and the others. Like the theorems of
    [DyPoint.v], they cover the calls of the kernel at which a rounding
    test passes or that a rule settles without [ziv], and say nothing
    about the calls that reach the cap of Ziv's strategy without a test
    passing, or that panic (see [DyPoint.v]). [kernel_dec_cbrt_correct]
    and [kernel_dec_hypot_correct] hold with no condition on the calls of
    the kernel, as [DyadicRoot.cbrt] and [DyadicRoot.hypot] use no driver
    and return at every argument ([k_cbrt_some] and [k_hypot_some] of
    [DyPoint.v]). *)

From Stdlib Require Import ZArith Reals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr ComCommon Contract PointDec DyPoint.

Open Scope R_scope.

Theorem kernel_dec_exp_correct :
  forall x, valid (itv x) -> com_common x ->
  let y := DecInterval.exp kernel_point x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom exp (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d exp (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
exact (dec_exp_correct_point kernel_point k_exp_c).
Qed.

Theorem kernel_dec_exp2_correct :
  forall x, valid (itv x) -> com_common x ->
  let y := DecInterval.exp2 kernel_point x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom Rexp2 (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d Rexp2 (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
exact (dec_exp2_correct_point kernel_point k_exp2_c).
Qed.

Theorem kernel_dec_exp10_correct :
  forall x, valid (itv x) -> com_common x ->
  let y := DecInterval.exp10 kernel_point x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom Rexp10 (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d Rexp10 (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
exact (dec_exp10_correct_point kernel_point k_exp10_c).
Qed.

Theorem kernel_dec_sinh_correct :
  forall x, valid (itv x) ->
  let y := DecInterval.sinh kernel_point x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom sinh (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d sinh (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
exact (dec_sinh_correct_point kernel_point k_sinh_c).
Qed.

Theorem kernel_dec_tanh_correct :
  forall x, valid (itv x) -> com_common x ->
  let y := DecInterval.tanh kernel_point x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom tanh (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d tanh (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
exact (dec_tanh_correct_point kernel_point k_tanh_c).
Qed.

Theorem kernel_dec_cosh_correct :
  forall first x, valid (itv x) ->
  let y := DecInterval.cosh kernel_point first x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom cosh (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d cosh (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
exact (dec_cosh_correct_point kernel_point k_cosh_c).
Qed.

Theorem kernel_dec_ln_correct :
  forall x, valid (itv x) ->
  let y := DecInterval.ln kernel_point x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom log_dom ln (itv x)) (itv y) /\
    exists d, strongest_dom log_dom d ln (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
exact (dec_ln_correct_point kernel_point k_ln_c).
Qed.

Theorem kernel_dec_log2_correct :
  forall x, valid (itv x) ->
  let y := DecInterval.log2 kernel_point x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom log_dom Rlog2 (itv x)) (itv y) /\
    exists d, strongest_dom log_dom d Rlog2 (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
exact (dec_log2_correct_point kernel_point k_log2_c).
Qed.

Theorem kernel_dec_log10_correct :
  forall x, valid (itv x) ->
  let y := DecInterval.log10 kernel_point x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom log_dom Rlog10 (itv x)) (itv y) /\
    exists d, strongest_dom log_dom d Rlog10 (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
exact (dec_log10_correct_point kernel_point k_log10_c).
Qed.

Theorem kernel_dec_asinh_correct :
  forall x, valid (itv x) ->
  let y := DecInterval.asinh kernel_point x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom arcsinh (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d arcsinh (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
exact (dec_asinh_correct_point kernel_point k_asinh_c).
Qed.

Theorem kernel_dec_acosh_correct :
  forall x, valid (itv x) ->
  let y := DecInterval.acosh kernel_point x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom acosh_dom Racosh (itv x)) (itv y) /\
    exists d, strongest_dom acosh_dom d Racosh (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
exact (dec_acosh_correct_point kernel_point k_acosh_c).
Qed.

Theorem kernel_dec_atanh_correct :
  forall x, valid (itv x) ->
  let y := DecInterval.atanh kernel_point x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom atanh_dom Ratanh (itv x)) (itv y) /\
    exists d, strongest_dom atanh_dom d Ratanh (itv x) (itv y) /\
      dec y = dec_min d (dec x).
Proof.
exact (dec_atanh_correct_point kernel_point k_atanh_c).
Qed.

Theorem kernel_dec_atan_correct :
  forall x, valid (itv x) -> com_common x ->
  let y := DecInterval.atan kernel_point x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom atan (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d atan (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
exact (dec_atan_correct_point kernel_point k_atan_c).
Qed.

Theorem kernel_dec_asin_correct :
  forall x, valid (itv x) ->
  let y := DecInterval.asin kernel_point x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom asin_dom asin (itv x)) (itv y) /\
    exists d, strongest_dom asin_dom d asin (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
exact (dec_asin_correct_point kernel_point k_asin_c).
Qed.

Theorem kernel_dec_acos_correct :
  forall x, valid (itv x) ->
  let y := DecInterval.acos kernel_point x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom acos_dom acos (itv x)) (itv y) /\
    exists d, strongest_dom acos_dom d acos (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
exact (dec_acos_correct_point kernel_point k_acos_c).
Qed.

Theorem kernel_dec_atan2_correct :
  forall y x, valid (itv y) -> valid (itv x) -> com_common y -> com_common x ->
  exists w, DecInterval.atan2 kernel_point y x = Some w /\
    if DecInterval.is_nai y || DecInterval.is_nai x then w = DecInterval.NAI
    else
      is_tightest (image2_set atan2_dom Ratan2 (itv y) (itv x)) (itv w) /\
      exists d, strongest2_set atan2_dom d Ratan2 (itv y) (itv x) (itv w) /\
        dec w = dec_min d (dec_min (dec y) (dec x)).
Proof.
exact (dec_atan2_correct_point kernel_point k_atan2_c).
Qed.

Theorem kernel_dec_sin_correct :
  forall has_fma first x, valid (itv x) -> com_common x ->
  exists y, DecInterval.sin kernel_point has_fma first x = Some y /\
    if DecInterval.is_nai x then y = DecInterval.NAI
    else
      is_tightest (image_dom real_dom sin (itv x)) (itv y) /\
      exists d, strongest_dom real_dom d sin (itv x) (itv y) /\
        dec y = dec_min d (dec x).
Proof.
exact (dec_sin_correct_point kernel_point k_sin_c k_cos_c).
Qed.

Theorem kernel_dec_cos_correct :
  forall has_fma first x, valid (itv x) -> com_common x ->
  exists y, DecInterval.cos kernel_point has_fma first x = Some y /\
    if DecInterval.is_nai x then y = DecInterval.NAI
    else
      is_tightest (image_dom real_dom cos (itv x)) (itv y) /\
      exists d, strongest_dom real_dom d cos (itv x) (itv y) /\
        dec y = dec_min d (dec x).
Proof.
exact (dec_cos_correct_point kernel_point k_cos_c k_sin_c).
Qed.

Theorem kernel_dec_tan_correct :
  forall has_fma x, valid (itv x) ->
  exists y, DecInterval.tan kernel_point has_fma x = Some y /\
    if DecInterval.is_nai x then y = DecInterval.NAI
    else
      is_tightest (image_dom tan_dom tan (itv x)) (itv y) /\
      exists d, strongest_dom tan_dom d tan (itv x) (itv y) /\
        dec y = dec_min d (dec x).
Proof.
exact (dec_tan_correct_point kernel_point k_tan_c k_sin_c k_cos_c).
Qed.

Theorem kernel_dec_pow_correct :
  forall first_min first_max x y,
  valid (itv x) -> valid (itv y) -> com_common x -> com_common y ->
  let z := DecInterval.pow kernel_point first_min first_max x y in
  if DecInterval.is_nai x || DecInterval.is_nai y then z = DecInterval.NAI
  else
    is_tightest (image2_set pow_dom Rpow (itv x) (itv y)) (itv z) /\
    exists d, strongest2_set pow_dom d Rpow (itv x) (itv y) (itv z) /\
      dec z = dec_min d (dec_min (dec x) (dec y)).
Proof.
exact (dec_pow_correct_point kernel_point k_pow_c).
Qed.

Theorem kernel_dec_pown_correct :
  forall n x, is_i32 n -> valid (itv x) -> (0 < n)%Z \/ com_common x ->
  exists y, DecInterval.powi kernel_point n x = Some y /\
    if DecInterval.is_nai x then y = DecInterval.NAI
    else
      is_tightest (image_dom (pown_dom n) (fun r => powerRZ r n) (itv x)) (itv y) /\
      exists d, strongest_dom (pown_dom n) d (fun r => powerRZ r n) (itv x) (itv y) /\
        dec y = dec_min d (dec x).
Proof.
exact (dec_pown_correct_point kernel_point k_pown_c).
Qed.

Theorem kernel_dec_cbrt_correct :
  forall x, valid (itv x) ->
  let y := DecInterval.cbrt kernel_point x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom Rcbrt (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d Rcbrt (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
exact (dec_cbrt_correct_point kernel_point k_cbrt_c).
Qed.

Theorem kernel_dec_hypot_correct :
  forall x y, valid (itv x) -> valid (itv y) ->
  exists z, DecInterval.hypot kernel_point x y = Some z /\
    if DecInterval.is_nai x || DecInterval.is_nai y then z = DecInterval.NAI
    else
      is_tightest (image2 Rhypot (itv x) (itv y)) (itv z) /\
      exists d, strongest2 d Rhypot (itv x) (itv y) (itv z) /\
        dec z = dec_min d (dec_min (dec x) (dec y)).
Proof.
exact (dec_hypot_correct_point kernel_point k_hypot_c).
Qed.
