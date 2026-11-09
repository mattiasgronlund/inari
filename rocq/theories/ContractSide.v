(** * What the functions that compute bounds must do, on the correct side

    [Contract.v] states what the fields of a record [point] must do for
    the elementary functions to return the tightest intervals: round a
    real function once, in the direction asked, to an [f64]. The dyadic
    kernel does that where a rounding test of Ziv's strategy passes, and
    at its cap of 4,096 bits it returns an [f64] on the correct side of
    the real result instead ([exp_dir_side] and the others). This file
    states that weaker property, for which [SideTheorems.v] proves that
    the elementary functions return intervals that contain the image of
    their argument ([encloses] of [Ieee1788.v]), though not always the
    tightest ones. Like [Contract.v], it has to be checked by reading.

    Each of the definitions [acos_s] to [tanh_s] below is the definition
    [acos_c] to [tanh_c] of [Contract.v], with [point_side] for
    [point_correct], [point_side2] for [point_correct2], and the special
    values copied unchanged. [sin_s] and [cos_s] also ask for the sign
    that [quadrant] of [Model.v] reads: a [sin] rounded down is below 0
    exactly where [sin] is, and a [cos] rounded up is above 0 exactly
    where [cos] is. *)

From Stdlib Require Import ZArith Reals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Mpfr.

Open Scope R_scope.

(** [v] is on the side [rnd] of [r]: at or below [r] if [rnd] is [RNDD],
    and at or above it if [rnd] is [RNDU]. It is not a NaN; an infinity
    is the one of that side, -inf for [RNDD] and +inf for [RNDU]. *)
Definition on_side (rnd : mpfr_rnd) (r : R) (v : f64) : Prop :=
  match v with
  | B754_infinity s => s = match rnd with RNDD => true | RNDU => false end
  | B754_nan => False
  | _ => match rnd with RNDD => B2R v <= r | RNDU => r <= B2R v end
  end.

(** [h] computes [f] on the correct side on the domain [D]: for a finite
    [f64] [x] in [D], [h rnd x] is on the side [rnd] of [f x]. *)
Definition point_side (D : R -> Prop) (f : R -> R) (h : mpfr_rnd -> f64 -> f64) : Prop :=
  forall rnd (x : f64), is_finite x = true -> D (B2R x) -> on_side rnd (f (B2R x)) (h rnd x).

(** The same for a function [h] of two [f64]s, which computes [f] on the
    domain [D] of points of R². *)
Definition point_side2 (D : R -> R -> Prop) (f : R -> R -> R)
    (h : mpfr_rnd -> f64 -> f64 -> f64) : Prop :=
  forall rnd (x y : f64), is_finite x = true -> is_finite y = true ->
  D (B2R x) (B2R y) -> on_side rnd (f (B2R x) (B2R y)) (h rnd x y).

(** ** The functions *)

Definition acos_s (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_side acos_dom acos h.

(** [acosh(+inf) = +inf] *)
Definition acosh_s (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_side acosh_dom Racosh h /\
  h RNDU (B754_infinity false) = B754_infinity false.

Definition asin_s (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_side asin_dom asin h.

(** [asinh(-inf) = -inf] and [asinh(+inf) = +inf] *)
Definition asinh_s (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_side real_dom arcsinh h /\
  h RNDD (B754_infinity true) = B754_infinity true /\
  h RNDU (B754_infinity false) = B754_infinity false.

(** [atan(-inf)] and [atan(+inf)] are [-PI/2] and [PI/2], rounded. *)
Definition atan_s (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_side real_dom atan h /\
  mpfr_round f64_format RNDD (- (PI / 2)) (with_val (h RNDD (B754_infinity true))) /\
  mpfr_round f64_format RNDU (PI / 2) (with_val (h RNDU (B754_infinity false))).

(** [atan2(y, x)] at the points of [atan2_c] in [Contract.v]. *)
Definition atan2_s (h : mpfr_rnd -> f64 -> f64 -> f64) : Prop :=
  point_side2 (fun y x => y <> 0 \/ 0 < x) Ratan2 h /\
  (forall rnd (y : f64), is_finite y = true -> 0 < B2R y ->
   exists s', h rnd y (B754_infinity false) = B754_zero s') /\
  (forall rnd (y : f64), is_finite y = true -> B2R y < 0 ->
   exists s', h rnd y (B754_infinity false) = B754_zero s') /\
  (forall rnd s, exists s', h rnd (B754_zero s) (B754_infinity false) = B754_zero s') /\
  (forall rnd (y : f64), is_finite y = true -> 0 < B2R y ->
   mpfr_round f64_format rnd PI (with_val (h rnd y (B754_infinity true)))) /\
  (forall rnd (y : f64), is_finite y = true -> B2R y < 0 ->
   mpfr_round f64_format rnd (- PI) (with_val (h rnd y (B754_infinity true)))) /\
  (forall rnd (x : f64), is_finite x = true ->
   mpfr_round f64_format rnd (PI / 2) (with_val (h rnd (B754_infinity false) x))) /\
  (forall rnd (x : f64), is_finite x = true ->
   mpfr_round f64_format rnd (- (PI / 2)) (with_val (h rnd (B754_infinity true) x))).

(** [atanh(-1) = -inf] and [atanh(1) = +inf] *)
Definition atanh_s (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_side atanh_dom Ratanh h /\
  (forall x : f64, is_finite x = true -> B2R x = -1 -> h RNDD x = B754_infinity true) /\
  (forall x : f64, is_finite x = true -> B2R x = 1 -> h RNDU x = B754_infinity false).

(** A [cos] rounded up is above 0 exactly where [cos] is. *)
Definition cos_s (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_side real_dom cos h /\
  forall x : f64, is_finite x = true ->
  (Model.lt Model.zero (h RNDU x) = true <-> 0 < cos (B2R x)).

(** [cosh(-inf) = cosh(+inf) = +inf] *)
Definition cosh_s (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_side real_dom cosh h /\
  forall s, h RNDU (B754_infinity s) = B754_infinity false.

(** [exp(-inf)] is a zero and [exp(+inf) = +inf], and the same for [exp10]
    and [exp2]. *)
Definition exp_s (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_side real_dom exp h /\
  (exists s, h RNDD (B754_infinity true) = B754_zero s) /\
  h RNDU (B754_infinity false) = B754_infinity false.

Definition exp10_s (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_side real_dom Rexp10 h /\
  (exists s, h RNDD (B754_infinity true) = B754_zero s) /\
  h RNDU (B754_infinity false) = B754_infinity false.

Definition exp2_s (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_side real_dom Rexp2 h /\
  (exists s, h RNDD (B754_infinity true) = B754_zero s) /\
  h RNDU (B754_infinity false) = B754_infinity false.

(** [log(+0) = log(-0) = -inf] and [log(+inf) = +inf], and the same for
    [log10] and [log2]. *)
Definition ln_s (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_side log_dom ln h /\
  (forall s, h RNDD (B754_zero s) = B754_infinity true) /\
  h RNDU (B754_infinity false) = B754_infinity false.

Definition log10_s (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_side log_dom Rlog10 h /\
  (forall s, h RNDD (B754_zero s) = B754_infinity true) /\
  h RNDU (B754_infinity false) = B754_infinity false.

Definition log2_s (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_side log_dom Rlog2 h /\
  (forall s, h RNDD (B754_zero s) = B754_infinity true) /\
  h RNDU (B754_infinity false) = B754_infinity false.

(** [pow(x, y)] at the points of [pow_c] in [Contract.v]. *)
Definition pow_s (h : mpfr_rnd -> f64 -> f64 -> f64) : Prop :=
  point_side2 pow_dom Rpow h /\
  (forall rnd (y : f64), is_finite y = true -> B2R y < 0 ->
   h rnd (B754_zero false) y = B754_infinity false) /\
  (forall rnd, h rnd (B754_zero false) (B754_infinity true) = B754_infinity false) /\
  (forall rnd, exists s, h rnd (B754_zero false) (B754_infinity false) = B754_zero s) /\
  (forall rnd s,
   mpfr_round f64_format rnd 1 (with_val (h rnd (B754_zero false) (B754_zero s)))) /\
  (forall rnd s,
   mpfr_round f64_format rnd 1 (with_val (h rnd (B754_infinity false) (B754_zero s)))) /\
  (forall rnd (x : f64) s, is_finite x = true -> B2R x = 1 ->
   mpfr_round f64_format rnd 1 (with_val (h rnd x (B754_infinity s)))) /\
  (forall rnd (x : f64), is_finite x = true -> 0 < B2R x < 1 ->
   h rnd x (B754_infinity true) = B754_infinity false) /\
  (forall rnd (x : f64), is_finite x = true -> 1 < B2R x ->
   exists s, h rnd x (B754_infinity true) = B754_zero s) /\
  (forall rnd (x : f64), is_finite x = true -> 0 < B2R x < 1 ->
   exists s, h rnd x (B754_infinity false) = B754_zero s) /\
  (forall rnd (x : f64), is_finite x = true -> 1 < B2R x ->
   h rnd x (B754_infinity false) = B754_infinity false) /\
  (forall rnd (y : f64), is_finite y = true -> B2R y < 0 ->
   exists s, h rnd (B754_infinity false) y = B754_zero s) /\
  (forall rnd, exists s, h rnd (B754_infinity false) (B754_infinity true) = B754_zero s) /\
  (forall rnd (y : f64), is_finite y = true -> 0 < B2R y ->
   h rnd (B754_infinity false) y = B754_infinity false) /\
  (forall rnd, h rnd (B754_infinity false) (B754_infinity false) = B754_infinity false).

(** [pow_si(x, n)] at the points of [pown_c] in [Contract.v]. *)
Definition pown_s (h : mpfr_rnd -> f64 -> Z -> f64) : Prop :=
  (forall rnd (x : f64) n, is_i32 n -> is_finite x = true -> pown_dom n (B2R x) ->
   on_side rnd (powerRZ (B2R x) n) (h rnd x n)) /\
  (forall rnd s n, is_i32 n -> (n < 0)%Z -> Z.even n = true ->
   h rnd (B754_zero s) n = B754_infinity false) /\
  (forall rnd s n, is_i32 n -> (n < 0)%Z -> Z.odd n = true ->
   h rnd (B754_zero s) n = B754_infinity s) /\
  (forall rnd n, is_i32 n -> (n < 0)%Z ->
   exists s, h rnd (B754_infinity false) n = B754_zero s) /\
  (forall rnd, mpfr_round f64_format rnd 1 (with_val (h rnd (B754_infinity false) 0%Z))) /\
  (forall rnd n, is_i32 n -> (0 < n)%Z -> h rnd (B754_infinity false) n = B754_infinity false) /\
  (forall rnd n, is_i32 n -> (n < 0)%Z -> Z.odd n = true ->
   exists s, h rnd (B754_infinity true) n = B754_zero s) /\
  (forall rnd n, is_i32 n -> (0 < n)%Z -> Z.odd n = true ->
   h rnd (B754_infinity true) n = B754_infinity true).

(** A [sin] rounded down is below 0 exactly where [sin] is. *)
Definition sin_s (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_side real_dom sin h /\
  forall x : f64, is_finite x = true ->
  (Model.lt (h RNDD x) Model.zero = true <-> sin (B2R x) < 0).

(** [sinh(-inf) = -inf] and [sinh(+inf) = +inf] *)
Definition sinh_s (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_side real_dom sinh h /\
  h RNDD (B754_infinity true) = B754_infinity true /\
  h RNDU (B754_infinity false) = B754_infinity false.

Definition tan_s (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_side tan_dom tan h.

(** [tanh(-inf) = -1] and [tanh(+inf) = 1] *)
Definition tanh_s (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_side real_dom tanh h /\
  mpfr_round f64_format RNDD (-1) (with_val (h RNDD (B754_infinity true))) /\
  mpfr_round f64_format RNDU 1 (with_val (h RNDU (B754_infinity false))).
