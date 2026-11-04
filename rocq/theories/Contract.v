(** * What the functions that compute bounds must do

    The elementary functions take as their first argument a record
    [point] of [Model.v]: the functions of [src/mpfr_calls.rs] that
    compute their bounds, each a function of a rounding direction and of
    its arguments. This file states, for each field, what it must do, at
    the level of [f64]s: that it rounds a real function once, in the
    direction asked, to an [f64], for finite arguments in the domain of
    that function, and the special values that the Rust code passes it,
    at infinities and at some finite points. Like [Model.v], [Ieee1788.v]
    and [Mpfr.v], it has to be checked by reading.

    Each of the definitions [acos_c] to [tanh_c] below transcribes the
    hypothesis of the same name in [Mpfr.v], with [_c] for [_ok], as
    [point_correct] and [point_correct2] transcribe [mpfr_correct] and
    [mpfr_correct2], from MPFR numbers to [f64]s: an argument [with_val x]
    becomes [x], a zero or an infinity of MPFR the [f64] zero or infinity
    of the same sign, and [MNum 1] and [MNum (-1)] the finite [f64]s whose
    real is 1 and -1. A result rounded to an MPFR number of 53 bits
    becomes one rounded to an [f64], and a result 1 or -1 becomes that
    real rounded to an [f64], which is the [f64] 1 or -1. A special value
    that is a zero again need only be a zero, of either sign.

    [MpfrPoint.v] shows that the record [mpfr_point m], which
    [src/mpfr_calls/mpfr.rs] makes of the MPFR functions [m], satisfies
    each of these where [m] satisfies the hypotheses of [Mpfr.v] that it
    needs: for each function [f], [f_c] where [m] satisfies [get_d_ok] and
    [f_ok] at an exponent range that satisfies [range_ok]. [OfPoint.v],
    [OfPointElem.v] and [OfPointPow.v] go the other way: of every record
    [p], they make MPFR functions [of_point p] with
    [mpfr_point (of_point p) = p], which satisfy [get_d_ok] at the
    exponent range of [f64] and [f_ok] at that range where [p] satisfies
    [f_c]. With them, [PointTheorems.v] proves [exp_correct] for every
    record [p] that does what it needs of it, as [exp_correct_point]. The
    other theorems about the elementary functions are stated for MPFR
    functions [m], and what they assume of [m] is stated in [Mpfr.v]. *)

From Stdlib Require Import ZArith Reals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Mpfr.

Open Scope R_scope.

(** [h] computes [f] on the domain [D]: for a finite [f64] [x] in [D],
    [h rnd x] is [f x] rounded in the direction [rnd] to an [f64]. *)
Definition point_correct (D : R -> Prop) (f : R -> R) (h : mpfr_rnd -> f64 -> f64) :
    Prop :=
  forall rnd (x : f64), is_finite x = true -> D (B2R x) ->
  mpfr_round f64_format rnd (f (B2R x)) (with_val (h rnd x)).

(** The same for a function [h] of two [f64]s, which computes [f] on the
    domain [D] of points of R². *)
Definition point_correct2 (D : R -> R -> Prop) (f : R -> R -> R)
    (h : mpfr_rnd -> f64 -> f64 -> f64) : Prop :=
  forall rnd (x y : f64), is_finite x = true -> is_finite y = true ->
  D (B2R x) (B2R y) ->
  mpfr_round f64_format rnd (f (B2R x) (B2R y)) (with_val (h rnd x y)).

(** ** The functions

    For each function, [point_correct] and the special values that
    [src/elementary.rs] passes it, as in [Mpfr.v]. *)

Definition acos_c (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_correct acos_dom acos h.

(** [acosh(+inf) = +inf] *)
Definition acosh_c (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_correct acosh_dom Racosh h /\
  h RNDU (B754_infinity false) = B754_infinity false.

Definition asin_c (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_correct asin_dom asin h.

(** [asinh(-inf) = -inf] and [asinh(+inf) = +inf] *)
Definition asinh_c (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_correct real_dom arcsinh h /\
  h RNDD (B754_infinity true) = B754_infinity true /\
  h RNDU (B754_infinity false) = B754_infinity false.

(** [atan(-inf)] and [atan(+inf)] are [-PI/2] and [PI/2], rounded. *)
Definition atan_c (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_correct real_dom atan h /\
  mpfr_round f64_format RNDD (- (PI / 2)) (with_val (h RNDD (B754_infinity true))) /\
  mpfr_round f64_format RNDU (PI / 2) (with_val (h RNDU (B754_infinity false))).

(** [atan2(y, x)] at the points that [atan2_ok] in [Mpfr.v] describes. *)
Definition atan2_c (h : mpfr_rnd -> f64 -> f64 -> f64) : Prop :=
  point_correct2 (fun y x => y <> 0 \/ 0 < x) Ratan2 h /\
  (* [atan2(y, +inf)] is a zero for a finite [y > 0], for a finite [y < 0]
     and for [y] = ±0 *)
  (forall rnd (y : f64), is_finite y = true -> 0 < B2R y ->
   exists s', h rnd y (B754_infinity false) = B754_zero s') /\
  (forall rnd (y : f64), is_finite y = true -> B2R y < 0 ->
   exists s', h rnd y (B754_infinity false) = B754_zero s') /\
  (forall rnd s, exists s', h rnd (B754_zero s) (B754_infinity false) = B754_zero s') /\
  (* [atan2(y, -inf)] is [PI] for a finite [y > 0] and [-PI] for a finite
     [y < 0], rounded *)
  (forall rnd (y : f64), is_finite y = true -> 0 < B2R y ->
   mpfr_round f64_format rnd PI (with_val (h rnd y (B754_infinity true)))) /\
  (forall rnd (y : f64), is_finite y = true -> B2R y < 0 ->
   mpfr_round f64_format rnd (- PI) (with_val (h rnd y (B754_infinity true)))) /\
  (* [atan2(+inf, x)] is [PI / 2] and [atan2(-inf, x)] is [- (PI / 2)] for
     a finite [x], rounded *)
  (forall rnd (x : f64), is_finite x = true ->
   mpfr_round f64_format rnd (PI / 2) (with_val (h rnd (B754_infinity false) x))) /\
  (forall rnd (x : f64), is_finite x = true ->
   mpfr_round f64_format rnd (- (PI / 2)) (with_val (h rnd (B754_infinity true) x))).

(** [atanh(-1) = -inf] and [atanh(1) = +inf] *)
Definition atanh_c (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_correct atanh_dom Ratanh h /\
  (forall x : f64, is_finite x = true -> B2R x = -1 -> h RNDD x = B754_infinity true) /\
  (forall x : f64, is_finite x = true -> B2R x = 1 -> h RNDU x = B754_infinity false).

Definition cos_c (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_correct real_dom cos h.

(** [cosh(-inf) = cosh(+inf) = +inf] *)
Definition cosh_c (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_correct real_dom cosh h /\
  forall s, h RNDU (B754_infinity s) = B754_infinity false.

(** [exp(-inf)] is a zero and [exp(+inf) = +inf], and the same for [exp10]
    and [exp2]. *)
Definition exp_c (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_correct real_dom exp h /\
  (exists s, h RNDD (B754_infinity true) = B754_zero s) /\
  h RNDU (B754_infinity false) = B754_infinity false.

Definition exp10_c (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_correct real_dom Rexp10 h /\
  (exists s, h RNDD (B754_infinity true) = B754_zero s) /\
  h RNDU (B754_infinity false) = B754_infinity false.

Definition exp2_c (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_correct real_dom Rexp2 h /\
  (exists s, h RNDD (B754_infinity true) = B754_zero s) /\
  h RNDU (B754_infinity false) = B754_infinity false.

(** [log(+0) = log(-0) = -inf] and [log(+inf) = +inf], and the same for
    [log10] and [log2]. *)
Definition ln_c (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_correct log_dom ln h /\
  (forall s, h RNDD (B754_zero s) = B754_infinity true) /\
  h RNDU (B754_infinity false) = B754_infinity false.

Definition log10_c (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_correct log_dom Rlog10 h /\
  (forall s, h RNDD (B754_zero s) = B754_infinity true) /\
  h RNDU (B754_infinity false) = B754_infinity false.

Definition log2_c (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_correct log_dom Rlog2 h /\
  (forall s, h RNDD (B754_zero s) = B754_infinity true) /\
  h RNDU (B754_infinity false) = B754_infinity false.

(** [pow(x, y)] at the points that [pow_ok] in [Mpfr.v] describes. *)
Definition pow_c (h : mpfr_rnd -> f64 -> f64 -> f64) : Prop :=
  point_correct2 pow_dom Rpow h /\
  (* [pow(+0, y) = +inf] for [y < 0], [-inf] included; [pow(+0, +inf)] is
     a zero *)
  (forall rnd (y : f64), is_finite y = true -> B2R y < 0 ->
   h rnd (B754_zero false) y = B754_infinity false) /\
  (forall rnd, h rnd (B754_zero false) (B754_infinity true) = B754_infinity false) /\
  (forall rnd, exists s, h rnd (B754_zero false) (B754_infinity false) = B754_zero s) /\
  (* [pow(x, ±0) = 1] for [x] +0 and +inf, and [pow(+1, ±inf) = 1] *)
  (forall rnd s,
   mpfr_round f64_format rnd 1 (with_val (h rnd (B754_zero false) (B754_zero s)))) /\
  (forall rnd s,
   mpfr_round f64_format rnd 1 (with_val (h rnd (B754_infinity false) (B754_zero s)))) /\
  (forall rnd (x : f64) s, is_finite x = true -> B2R x = 1 ->
   mpfr_round f64_format rnd 1 (with_val (h rnd x (B754_infinity s)))) /\
  (* [pow(x, -inf)] is +inf for [0 < x < 1] and a zero for [x > 1], and
     [pow(x, +inf)] is a zero for [0 < x < 1] and +inf for [x > 1] *)
  (forall rnd (x : f64), is_finite x = true -> 0 < B2R x < 1 ->
   h rnd x (B754_infinity true) = B754_infinity false) /\
  (forall rnd (x : f64), is_finite x = true -> 1 < B2R x ->
   exists s, h rnd x (B754_infinity true) = B754_zero s) /\
  (forall rnd (x : f64), is_finite x = true -> 0 < B2R x < 1 ->
   exists s, h rnd x (B754_infinity false) = B754_zero s) /\
  (forall rnd (x : f64), is_finite x = true -> 1 < B2R x ->
   h rnd x (B754_infinity false) = B754_infinity false) /\
  (* [pow(+inf, y)] is a zero for [y < 0] and +inf for [y > 0], infinities
     included *)
  (forall rnd (y : f64), is_finite y = true -> B2R y < 0 ->
   exists s, h rnd (B754_infinity false) y = B754_zero s) /\
  (forall rnd, exists s, h rnd (B754_infinity false) (B754_infinity true) = B754_zero s) /\
  (forall rnd (y : f64), is_finite y = true -> 0 < B2R y ->
   h rnd (B754_infinity false) y = B754_infinity false) /\
  (forall rnd, h rnd (B754_infinity false) (B754_infinity false) = B754_infinity false).

(** [pow_si(x, n)] at the points that [pown_ok] in [Mpfr.v] describes. *)
Definition pown_c (h : mpfr_rnd -> f64 -> Z -> f64) : Prop :=
  (forall rnd (x : f64) n, is_i32 n -> is_finite x = true -> pown_dom n (B2R x) ->
   mpfr_round f64_format rnd (powerRZ (B2R x) n) (with_val (h rnd x n))) /\
  (* [pow_si(±0, n)] for [n < 0]: +inf for an even [n], and the infinity
     with the sign of the zero for an odd one *)
  (forall rnd s n, is_i32 n -> (n < 0)%Z -> Z.even n = true ->
   h rnd (B754_zero s) n = B754_infinity false) /\
  (forall rnd s n, is_i32 n -> (n < 0)%Z -> Z.odd n = true ->
   h rnd (B754_zero s) n = B754_infinity s) /\
  (* [pow_si(+inf, n)] is a zero for [n < 0], 1 for [n = 0] and +inf for
     [n > 0], and [pow_si(-inf, n)] is a zero for an odd [n < 0] and -inf
     for an odd [n > 0] *)
  (forall rnd n, is_i32 n -> (n < 0)%Z ->
   exists s, h rnd (B754_infinity false) n = B754_zero s) /\
  (forall rnd, mpfr_round f64_format rnd 1 (with_val (h rnd (B754_infinity false) 0%Z))) /\
  (forall rnd n, is_i32 n -> (0 < n)%Z -> h rnd (B754_infinity false) n = B754_infinity false) /\
  (forall rnd n, is_i32 n -> (n < 0)%Z -> Z.odd n = true ->
   exists s, h rnd (B754_infinity true) n = B754_zero s) /\
  (forall rnd n, is_i32 n -> (0 < n)%Z -> Z.odd n = true ->
   h rnd (B754_infinity true) n = B754_infinity true).

Definition sin_c (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_correct real_dom sin h.

(** [sinh(-inf) = -inf] and [sinh(+inf) = +inf] *)
Definition sinh_c (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_correct real_dom sinh h /\
  h RNDD (B754_infinity true) = B754_infinity true /\
  h RNDU (B754_infinity false) = B754_infinity false.

Definition tan_c (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_correct tan_dom tan h.

(** [tanh(-inf) = -1] and [tanh(+inf) = 1] *)
Definition tanh_c (h : mpfr_rnd -> f64 -> f64) : Prop :=
  point_correct real_dom tanh h /\
  mpfr_round f64_format RNDD (-1) (with_val (h RNDD (B754_infinity true))) /\
  mpfr_round f64_format RNDU 1 (with_val (h RNDU (B754_infinity false))).
