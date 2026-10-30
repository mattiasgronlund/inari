(** * What the theorems assume of MPFR

    [Model.v] leaves the MPFR functions that [src/elementary.rs] calls
    abstract, as the fields of a record [m : mpfr]. This file states what
    the theorems assume of them: what the MPFR manual documents. Like
    [Model.v] and [Ieee1788.v], it has to be checked by reading, against
    the MPFR manual: its sections on rounding, on the exponent range, on
    special values and exceptions, the entry of [mpfr_get_d], and those of
    the functions. It assumes as little as the proofs use: the rounding of
    each function for finite arguments in its domain, and only the special
    values that the Rust code passes.

    MPFR's exponent range, [emin] and [emax], is global state that the
    Rust code does not set. The theorems hold for every range that
    contains that of [f64] ([range_ok]), as MPFR's default range does. *)

From Stdlib Require Import ZArith Reals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary.

Open Scope R_scope.

(** The reals that an MPFR number of 53 bits holds with the exponent range
    [emin], [emax]: 0, and those with 53 bits of significand and an
    exponent [e] with [emin <= e <= emax], where MPFR writes a number as
    [m * 2^e] with [1/2 <= |m| < 1]. MPFR has no subnormal numbers. *)
Definition mpfr_format (emin emax : Z) (y : R) : Prop :=
  y = 0 \/
  (generic_format radix2 (FLX_exp 53) y /\
   bpow radix2 (emin - 1) <= Rabs y < bpow radix2 emax).

(** The reals that a finite [f64] holds. *)
Definition f64_format (y : R) : Prop :=
  exists w : f64, is_finite w = true /\ B2R w = y.

(** [v] is the real [r] rounded in the direction [rnd] to an element of
    [F], where [F] is [mpfr_format] or [f64_format]: toward -inf, the
    largest element of [F] at or below [r], or -inf if there is none; and
    toward +inf, the least one at or above [r], or +inf. A result of 0 is a
    zero of either sign, and any other result is an [MNum]. This is
    rounding with overflow toward -inf and +inf, as MPFR and IEEE 754 do it:
    a positive real above the largest element of [F] rounds down to that
    element and up to +inf. *)
Definition mpfr_round (F : R -> Prop) (rnd : mpfr_rnd) (r : R) (v : mpfr_t) :
    Prop :=
  match rnd, v with
  | RNDD, MNum y => y <> 0 /\ Rnd_DN_pt F r y
  | RNDD, MZero _ => Rnd_DN_pt F r 0
  | RNDD, MInf true => forall g, F g -> r < g
  | RNDU, MNum y => y <> 0 /\ Rnd_UP_pt F r y
  | RNDU, MZero _ => Rnd_UP_pt F r 0
  | RNDU, MInf false => forall g, F g -> g < r
  | _, _ => False
  end.

(** MPFR's exponent range contains that of [f64], so every finite [f64] is
    an MPFR number of 53 bits. *)
Definition range_ok (emin emax : Z) : Prop :=
  (emin <= -1073)%Z /\ (1024 <= emax)%Z.

(** [mpfr_get_d]: an MPFR number of 53 bits other than 0 converts to the
    [f64] that rounds it in the direction [rnd], a zero to a zero, and an
    infinity to the infinity of the same sign. *)
Definition get_d_ok (emin emax : Z) (m : mpfr) : Prop :=
  (forall rnd y, y <> 0 -> mpfr_format emin emax y ->
   mpfr_round f64_format rnd y (with_val (mpfr_get_d m rnd (MNum y)))) /\
  (forall rnd s, exists s', mpfr_get_d m rnd (MZero s) = B754_zero s') /\
  (forall rnd s, mpfr_get_d m rnd (MInf s) = B754_infinity s).

(** The MPFR function [g] computes [f] on the domain [D]: for a finite
    [f64] [x] in [D], [g rnd x] is [f x] rounded in the direction [rnd] to
    an MPFR number of 53 bits. *)
Definition mpfr_correct (emin emax : Z) (D : R -> Prop) (f : R -> R)
    (g : mpfr_rnd -> mpfr_t -> mpfr_t) : Prop :=
  forall rnd (x : f64), is_finite x = true -> D (B2R x) ->
  mpfr_round (mpfr_format emin emax) rnd (f (B2R x)) (g rnd (with_val x)).

(** ** The functions

    For each function, [mpfr_correct] and the special values that
    [src/elementary.rs] passes it. *)

Definition acos_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax acos_dom acos (mpfr_acos m).

(** [acosh(+inf) = +inf] *)
Definition acosh_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax acosh_dom Racosh (mpfr_acosh m) /\
  mpfr_acosh m RNDU (MInf false) = MInf false.

Definition asin_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax asin_dom asin (mpfr_asin m).

(** [asinh(-inf) = -inf] and [asinh(+inf) = +inf] *)
Definition asinh_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax real_dom arcsinh (mpfr_asinh m) /\
  mpfr_asinh m RNDD (MInf true) = MInf true /\
  mpfr_asinh m RNDU (MInf false) = MInf false.

(** [atan(-inf)] and [atan(+inf)] are [-PI/2] and [PI/2], rounded. *)
Definition atan_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax real_dom atan (mpfr_atan m) /\
  mpfr_round (mpfr_format emin emax) RNDD (- (PI / 2)) (mpfr_atan m RNDD (MInf true)) /\
  mpfr_round (mpfr_format emin emax) RNDU (PI / 2) (mpfr_atan m RNDU (MInf false)).

(** [atanh(-1) = -inf] and [atanh(1) = +inf] *)
Definition atanh_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax atanh_dom Ratanh (mpfr_atanh m) /\
  mpfr_atanh m RNDD (MNum (-1)) = MInf true /\
  mpfr_atanh m RNDU (MNum 1) = MInf false.

(** [Interval::cos], [Interval::sin] and [Interval::tan] call [cos],
    [sin] and [tan] only at finite arguments, so no special value is
    assumed of them. *)
Definition cos_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax real_dom cos (mpfr_cos m).

(** [cosh(-inf) = cosh(+inf) = +inf] *)
Definition cosh_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax real_dom cosh (mpfr_cosh m) /\
  forall s, mpfr_cosh m RNDU (MInf s) = MInf false.

(** [exp(-inf) = +0] and [exp(+inf) = +inf], and the same for [exp10] and
    [exp2]. *)
Definition exp_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax real_dom exp (mpfr_exp m) /\
  mpfr_exp m RNDD (MInf true) = MZero false /\
  mpfr_exp m RNDU (MInf false) = MInf false.

Definition exp10_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax real_dom Rexp10 (mpfr_exp10 m) /\
  mpfr_exp10 m RNDD (MInf true) = MZero false /\
  mpfr_exp10 m RNDU (MInf false) = MInf false.

Definition exp2_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax real_dom Rexp2 (mpfr_exp2 m) /\
  mpfr_exp2 m RNDD (MInf true) = MZero false /\
  mpfr_exp2 m RNDU (MInf false) = MInf false.

(** [log(+0) = log(-0) = -inf] and [log(+inf) = +inf], and the same for
    [log10] and [log2]. *)
Definition ln_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax log_dom ln (mpfr_log m) /\
  (forall s, mpfr_log m RNDD (MZero s) = MInf true) /\
  mpfr_log m RNDU (MInf false) = MInf false.

Definition log10_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax log_dom Rlog10 (mpfr_log10 m) /\
  (forall s, mpfr_log10 m RNDD (MZero s) = MInf true) /\
  mpfr_log10 m RNDU (MInf false) = MInf false.

Definition log2_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax log_dom Rlog2 (mpfr_log2 m) /\
  (forall s, mpfr_log2 m RNDD (MZero s) = MInf true) /\
  mpfr_log2 m RNDU (MInf false) = MInf false.

Definition sin_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax real_dom sin (mpfr_sin m).

(** [sinh(-inf) = -inf] and [sinh(+inf) = +inf] *)
Definition sinh_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax real_dom sinh (mpfr_sinh m) /\
  mpfr_sinh m RNDD (MInf true) = MInf true /\
  mpfr_sinh m RNDU (MInf false) = MInf false.

Definition tan_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax tan_dom tan (mpfr_tan m).

(** [tanh(-inf) = -1] and [tanh(+inf) = 1] *)
Definition tanh_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax real_dom tanh (mpfr_tanh m) /\
  mpfr_tanh m RNDD (MInf true) = MNum (-1) /\
  mpfr_tanh m RNDU (MInf false) = MNum 1.
