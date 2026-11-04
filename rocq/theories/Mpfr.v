(** * What the theorems assume of MPFR

    [Model.v] leaves abstract, as the fields of a record [m : mpfr], the
    MPFR functions with which [src/mpfr_calls/mpfr.rs] rounds the bounds
    of the elementary functions. In [Model.v], the elementary functions
    take a record [point] of the functions that round their bounds to
    [f64]s, and the theorems about them, all but the one of
    [PointTheorems.v] below, are stated for [mpfr_point m], the record
    [point] that [src/mpfr_calls/mpfr.rs] makes of [m]. This file states
    what the theorems assume of [m]: what the MPFR manual documents. Like
    [Model.v] and [Ieee1788.v], it has to be checked by reading, against
    the MPFR manual: its sections on rounding, on the exponent range, on
    special values and exceptions, the entry of [mpfr_get_d], and those of
    the functions. It assumes as little as the proofs use: the rounding of
    each function for finite arguments in its domain, and only the special
    values that the Rust code passes. The rounding and the special values
    of the fields of [m], all but [mpfr_get_d], which converts their
    results, are stated only at the MPFR numbers that [with_val] makes of
    [f64]s, as the code passes them.
    A special value at a finite argument other than 0, such as
    [atan2(y, -inf)] for [y > 0], is thus assumed only where that argument
    is the real of a finite [f64], not at every real. A special value that
    is a zero is assumed only to be a zero, of either sign: the code passes
    the result of each function with special values here only to
    [mpfr_get_d], and [get_d_ok] says only that it converts a zero to a
    zero, so the theorems cannot use the sign.

    Neither [src/elementary.rs] nor the functions of
    [src/mpfr_calls/mpfr.rs] that it calls set MPFR's exponent range,
    [emin] and [emax]. The theorems about the functions of
    [src/elementary.rs] hold for every range that contains that of [f64]
    ([range_ok]), as MPFR's default range does.

    [mpfr_ok_consistent] in [MpfrConsistent.v] shows that the hypotheses
    on [m] that the theorems take can all hold at once: at every range with
    [range_ok], the ideal MPFR of [MpfrIdeal.v] satisfies all of them. It
    does not show that the MPFR that the Rust code links satisfies them.

    [Contract.v] states what each field of a record [point] must do, at
    the level of [f64]s. [MpfrPoint.v] shows that each field of
    [mpfr_point m] does it where [m] satisfies, at a range with
    [range_ok], [get_d_ok] and the hypothesis of the MPFR function that
    the field calls, such as [exp_ok] for [p_exp]. [PointTheorems.v]
    restates [exp_correct] as [exp_correct_point], for every record
    [point] whose [p_exp] does what [Contract.v] asks of it. All the
    others about the elementary functions, [exp_correct] among them,
    assume of [m] only what this file states. *)

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

(** The same for an MPFR function [g] of two numbers, which computes [f]
    on the domain [D] of points of R². *)
Definition mpfr_correct2 (emin emax : Z) (D : R -> R -> Prop) (f : R -> R -> R)
    (g : mpfr_rnd -> mpfr_t -> mpfr_t -> mpfr_t) : Prop :=
  forall rnd (x y : f64), is_finite x = true -> is_finite y = true ->
  D (B2R x) (B2R y) ->
  mpfr_round (mpfr_format emin emax) rnd (f (B2R x) (B2R y))
    (g rnd (with_val x) (with_val y)).

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

(** [Interval::atan2] calls [atan2(y, x)], with [y] a bound of [self] and
    [x] one of [rhs], at points where [y] is not a zero or [x] is above 0
    or +inf, and never at two infinities. For finite [y] and [x],
    [mpfr_correct2] covers those points: MPFR's [atan2] of a zero [y] and
    [x < 0] is [PI] or [-PI] by the sign of the zero, which no real
    function gives, and that of two zeros is a zero or [±PI] by both
    signs, at [(0, 0)], which is not in [atan2_dom], so the domain stated
    leaves out [y = 0, x <= 0]. The
    special values below are those of the [mpfr_atan2] entry of the MPFR
    manual at the points that the code passes, one infinity and a finite
    [f64], except that [atan2(y, +inf)] is only assumed to be a zero, of
    either sign (see the header). For a finite [y > 0] the entry gives +0
    there, and -0 for a finite [y < 0]. For [y] = ±0, it gives ±0 by its
    [atan2(±0, x) = ±0] for [x > 0] if that [x] can be +inf. If it cannot,
    no bullet of the entry names that point, and the rule of §4.5
    "Floating-Point Values on Special Numbers" for a point outside the
    domain but in its closure gives the limit, 0. The wording favours the
    first reading: the bullets with one infinite argument say "for finite
    x", "for finite y > 0" or "for finite y < 0", and those of
    [atan2(±0, x) = ±0] say only "for x > 0". The entry cites the ISO C99
    and IEEE 754 standards for its special values. MPFR's [src/atan2.c]
    lists them in a comment (l.66-79 in MPFR 4.2.2) that names no source,
    with a marker [313)], as of a footnote, at the end of its first
    bullet. Its bullets for these points,
    [atan2(±0, x) returns ±0, for x > 0] and
    [atan2(±y, +oo) returns ±0, for finite y > 0], give the same two
    readings and the same contrast. The zeros are exact, so they are
    stated for both directions, and [PI] and [PI / 2] are rounded. *)
Definition atan2_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct2 emin emax (fun y x => y <> 0 \/ 0 < x) Ratan2 (mpfr_atan2 m) /\
  (* [atan2(y, +inf)] is a zero for a finite [y > 0], for a finite [y < 0]
     and for [y] = ±0 *)
  (forall rnd (y : f64), is_finite y = true -> 0 < B2R y ->
   exists s', mpfr_atan2 m rnd (with_val y) (MInf false) = MZero s') /\
  (forall rnd (y : f64), is_finite y = true -> B2R y < 0 ->
   exists s', mpfr_atan2 m rnd (with_val y) (MInf false) = MZero s') /\
  (forall rnd s, exists s', mpfr_atan2 m rnd (MZero s) (MInf false) = MZero s') /\
  (* [atan2(y, -inf)] is [PI] for a finite [y > 0] and [-PI] for a finite
     [y < 0] *)
  (forall rnd (y : f64), is_finite y = true -> 0 < B2R y ->
   mpfr_round (mpfr_format emin emax) rnd PI
     (mpfr_atan2 m rnd (with_val y) (MInf true))) /\
  (forall rnd (y : f64), is_finite y = true -> B2R y < 0 ->
   mpfr_round (mpfr_format emin emax) rnd (- PI)
     (mpfr_atan2 m rnd (with_val y) (MInf true))) /\
  (* [atan2(+inf, x)] is [PI / 2] and [atan2(-inf, x)] is [- (PI / 2)] for
     a finite [x] *)
  (forall rnd (x : f64), is_finite x = true ->
   mpfr_round (mpfr_format emin emax) rnd (PI / 2)
     (mpfr_atan2 m rnd (MInf false) (with_val x))) /\
  (forall rnd (x : f64), is_finite x = true ->
   mpfr_round (mpfr_format emin emax) rnd (- (PI / 2))
     (mpfr_atan2 m rnd (MInf true) (with_val x))).

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

(** [exp(-inf)] is a zero and [exp(+inf) = +inf], and the same for [exp10]
    and [exp2]. The rules of §4.5 give +0 at -inf, of which only a zero is
    assumed (see the header). *)
Definition exp_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax real_dom exp (mpfr_exp m) /\
  (exists s, mpfr_exp m RNDD (MInf true) = MZero s) /\
  mpfr_exp m RNDU (MInf false) = MInf false.

Definition exp10_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax real_dom Rexp10 (mpfr_exp10 m) /\
  (exists s, mpfr_exp10 m RNDD (MInf true) = MZero s) /\
  mpfr_exp10 m RNDU (MInf false) = MInf false.

Definition exp2_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct emin emax real_dom Rexp2 (mpfr_exp2 m) /\
  (exists s, mpfr_exp2 m RNDD (MInf true) = MZero s) /\
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

(** [Interval::pow] calls [pow] at points [(x, y)] where [x] is +0, a
    real above 0 or +inf, or -0 for a [y] above 0, which [mpfr_correct2]
    covers. The special values below are those of the [mpfr_pow] entry of
    the MPFR manual at the points that the code passes: [x] +0, 1 or +inf,
    or [y] a zero or an infinity, outside the domain or not finite. MPFR
    returns them exactly, so they are stated for both directions. Where
    the entry gives +0, only a zero is assumed (see the header). *)
Definition pow_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct2 emin emax pow_dom Rpow (mpfr_pow m) /\
  (* [pow(+0, y) = +inf] for [y < 0], [-inf] included, as [y] is then not
     an odd integer or [+0] is the zero; [pow(+0, +inf)] is a zero *)
  (forall rnd (y : f64), is_finite y = true -> B2R y < 0 ->
   mpfr_pow m rnd (MZero false) (with_val y) = MInf false) /\
  (forall rnd, mpfr_pow m rnd (MZero false) (MInf true) = MInf false) /\
  (forall rnd, exists s, mpfr_pow m rnd (MZero false) (MInf false) = MZero s) /\
  (* [pow(x, ±0) = 1] for [x] +0 and +inf, and [pow(+1, ±inf) = 1] *)
  (forall rnd s, mpfr_pow m rnd (MZero false) (MZero s) = MNum 1) /\
  (forall rnd s, mpfr_pow m rnd (MInf false) (MZero s) = MNum 1) /\
  (forall rnd s, mpfr_pow m rnd (MNum 1) (MInf s) = MNum 1) /\
  (* [pow(x, -inf)] is +inf for [0 < x < 1] and a zero for [x > 1], and
     [pow(x, +inf)] is a zero for [0 < x < 1] and +inf for [x > 1] *)
  (forall rnd (x : f64), is_finite x = true -> 0 < B2R x < 1 ->
   mpfr_pow m rnd (with_val x) (MInf true) = MInf false) /\
  (forall rnd (x : f64), is_finite x = true -> 1 < B2R x ->
   exists s, mpfr_pow m rnd (with_val x) (MInf true) = MZero s) /\
  (forall rnd (x : f64), is_finite x = true -> 0 < B2R x < 1 ->
   exists s, mpfr_pow m rnd (with_val x) (MInf false) = MZero s) /\
  (forall rnd (x : f64), is_finite x = true -> 1 < B2R x ->
   mpfr_pow m rnd (with_val x) (MInf false) = MInf false) /\
  (* [pow(+inf, y)] is a zero for [y < 0] and +inf for [y > 0], infinities
     included *)
  (forall rnd (y : f64), is_finite y = true -> B2R y < 0 ->
   exists s, mpfr_pow m rnd (MInf false) (with_val y) = MZero s) /\
  (forall rnd, exists s, mpfr_pow m rnd (MInf false) (MInf true) = MZero s) /\
  (forall rnd (y : f64), is_finite y = true -> 0 < B2R y ->
   mpfr_pow m rnd (MInf false) (with_val y) = MInf false) /\
  (forall rnd, mpfr_pow m rnd (MInf false) (MInf false) = MInf false).

(** [Interval::powi] calls [pow_si] with an [i32] [n]. It computes
    [powerRZ] on its domain for finite [x], and the special values below
    are those of the [mpfr_pow] entry of the MPFR manual, which covers
    [mpfr_pow_si], at the points that the code passes: a zero for [n < 0],
    and an infinity. MPFR returns them exactly, so they are stated for both
    directions. Where the entry gives +0 or -0, only a zero is assumed (see
    the header). *)
Definition pown_ok (emin emax : Z) (m : mpfr) : Prop :=
  (forall rnd (x : f64) n, is_i32 n -> is_finite x = true -> pown_dom n (B2R x) ->
   mpfr_round (mpfr_format emin emax) rnd (powerRZ (B2R x) n)
     (mpfr_pow_si m rnd (with_val x) n)) /\
  (* [pow_si(±0, n)] for [n < 0]: +inf for an even [n], and the infinity
     with the sign of the zero for an odd one *)
  (forall rnd s n, is_i32 n -> (n < 0)%Z -> Z.even n = true ->
   mpfr_pow_si m rnd (MZero s) n = MInf false) /\
  (forall rnd s n, is_i32 n -> (n < 0)%Z -> Z.odd n = true ->
   mpfr_pow_si m rnd (MZero s) n = MInf s) /\
  (* [pow_si(+inf, n)] is a zero for [n < 0], 1 for [n = 0] and +inf for
     [n > 0], and [pow_si(-inf, n)] is a zero for an odd [n < 0] and -inf
     for an odd [n > 0] *)
  (forall rnd n, is_i32 n -> (n < 0)%Z ->
   exists s, mpfr_pow_si m rnd (MInf false) n = MZero s) /\
  (forall rnd, mpfr_pow_si m rnd (MInf false) 0 = MNum 1) /\
  (forall rnd n, is_i32 n -> (0 < n)%Z -> mpfr_pow_si m rnd (MInf false) n = MInf false) /\
  (forall rnd n, is_i32 n -> (n < 0)%Z -> Z.odd n = true ->
   exists s, mpfr_pow_si m rnd (MInf true) n = MZero s) /\
  (forall rnd n, is_i32 n -> (0 < n)%Z -> Z.odd n = true ->
   mpfr_pow_si m rnd (MInf true) n = MInf true).

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
