(** * What the theorems assume of MPFR

    [Model.v] leaves the MPFR functions that [src/elementary.rs] and
    [src/parse.rs] call abstract, as the fields of a record [m : mpfr].
    This file states what
    the theorems assume of them: what the MPFR manual documents. Like
    [Model.v] and [Ieee1788.v], it has to be checked by reading, against
    the MPFR manual: its sections on rounding, on the exponent range, on
    special values and exceptions, the entry of [mpfr_get_d], and those of
    the functions. It assumes as little as the proofs use: the rounding of
    each function for finite arguments in its domain, and only the special
    values that the Rust code passes.

    MPFR's exponent range, [emin] and [emax], is global state that
    [src/elementary.rs] does not set. The theorems about its functions
    hold for every range that contains that of [f64] ([range_ok]), as
    MPFR's default range does. [rational_to_f64] in [src/parse.rs] sets the
    range around its calls, and the hypotheses about them, in the last
    section, are stated at the range that it sets. *)

From Stdlib Require Import ZArith Reals Qreals.
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
    number. [atan2(±0, +inf) = ±0] is its [atan2(±0, x) = ±0] for
    [x > 0]. The zeros are exact, so they are stated for both directions,
    and [PI] and [PI / 2] are rounded. *)
Definition atan2_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct2 emin emax (fun y x => y <> 0 \/ 0 < x) Ratan2 (mpfr_atan2 m) /\
  (* [atan2(y, +inf)] is +0 for [y > 0] and -0 for [y < 0], and
     [atan2(±0, +inf) = ±0] *)
  (forall rnd y, 0 < y -> mpfr_atan2 m rnd (MNum y) (MInf false) = MZero false) /\
  (forall rnd y, y < 0 -> mpfr_atan2 m rnd (MNum y) (MInf false) = MZero true) /\
  (forall rnd s, mpfr_atan2 m rnd (MZero s) (MInf false) = MZero s) /\
  (* [atan2(y, -inf)] is [PI] for [y > 0] and [-PI] for [y < 0] *)
  (forall rnd y, 0 < y ->
   mpfr_round (mpfr_format emin emax) rnd PI (mpfr_atan2 m rnd (MNum y) (MInf true))) /\
  (forall rnd y, y < 0 ->
   mpfr_round (mpfr_format emin emax) rnd (- PI) (mpfr_atan2 m rnd (MNum y) (MInf true))) /\
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

(** [Interval::pow] calls [pow] at points [(x, y)] where [x] is +0, a
    real above 0 or +inf, or -0 for a [y] above 0, which [mpfr_correct2]
    covers. The special values below are those of the [mpfr_pow] entry of
    the MPFR manual at the points that the code passes: [x] +0, 1 or +inf,
    or [y] a zero or an infinity, outside the domain or not finite. MPFR
    returns them exactly, so they are stated for both directions. *)
Definition pow_ok (emin emax : Z) (m : mpfr) : Prop :=
  mpfr_correct2 emin emax pow_dom Rpow (mpfr_pow m) /\
  (* [pow(+0, y) = +inf] for [y < 0], [-inf] included, as [y] is then not
     an odd integer or [+0] is the zero; [pow(+0, +inf) = +0] *)
  (forall rnd y, y < 0 -> mpfr_pow m rnd (MZero false) (MNum y) = MInf false) /\
  (forall rnd, mpfr_pow m rnd (MZero false) (MInf true) = MInf false) /\
  (forall rnd, mpfr_pow m rnd (MZero false) (MInf false) = MZero false) /\
  (* [pow(x, ±0) = 1] for [x] +0 and +inf, and [pow(+1, ±inf) = 1] *)
  (forall rnd s, mpfr_pow m rnd (MZero false) (MZero s) = MNum 1) /\
  (forall rnd s, mpfr_pow m rnd (MInf false) (MZero s) = MNum 1) /\
  (forall rnd s, mpfr_pow m rnd (MNum 1) (MInf s) = MNum 1) /\
  (* [pow(x, -inf)] is +inf for [0 < x < 1] and +0 for [x > 1], and
     [pow(x, +inf)] is +0 for [0 < x < 1] and +inf for [x > 1] *)
  (forall rnd y, 0 < y < 1 -> mpfr_pow m rnd (MNum y) (MInf true) = MInf false) /\
  (forall rnd y, 1 < y -> mpfr_pow m rnd (MNum y) (MInf true) = MZero false) /\
  (forall rnd y, 0 < y < 1 -> mpfr_pow m rnd (MNum y) (MInf false) = MZero false) /\
  (forall rnd y, 1 < y -> mpfr_pow m rnd (MNum y) (MInf false) = MInf false) /\
  (* [pow(+inf, y)] is +0 for [y < 0] and +inf for [y > 0], infinities
     included *)
  (forall rnd y, y < 0 -> mpfr_pow m rnd (MInf false) (MNum y) = MZero false) /\
  (forall rnd, mpfr_pow m rnd (MInf false) (MInf true) = MZero false) /\
  (forall rnd y, 0 < y -> mpfr_pow m rnd (MInf false) (MNum y) = MInf false) /\
  (forall rnd, mpfr_pow m rnd (MInf false) (MInf false) = MInf false).

(** [Interval::powi] calls [pow_si] with an [i32] [n]. It computes
    [powerRZ] on its domain for finite [x], and the special values below
    are those of the [mpfr_pow] entry of the MPFR manual, which covers
    [mpfr_pow_si], at the points that the code passes: a zero for [n < 0],
    and an infinity. MPFR returns them exactly, so they are stated for both
    directions. *)
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
  (* [pow_si(+inf, n)] is +0 for [n < 0], 1 for [n = 0] and +inf for
     [n > 0], and [pow_si(-inf, n)] is -0 for an odd [n < 0] and -inf for
     an odd [n > 0] *)
  (forall rnd n, is_i32 n -> (n < 0)%Z -> mpfr_pow_si m rnd (MInf false) n = MZero false) /\
  (forall rnd, mpfr_pow_si m rnd (MInf false) 0 = MNum 1) /\
  (forall rnd n, is_i32 n -> (0 < n)%Z -> mpfr_pow_si m rnd (MInf false) n = MInf false) /\
  (forall rnd n, is_i32 n -> (n < 0)%Z -> Z.odd n = true ->
   mpfr_pow_si m rnd (MInf true) n = MZero true) /\
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

(** ** The conversions of [src/parse.rs]

    [rational_to_f64] sets MPFR's exponent range to [emin = -1073] and
    [emax = 1024] around its calls to [mpfr_set_q], [mpfr_subnormalize]
    and [mpfr_get_d], the range of the example in §5.13 of the MPFR
    manual, after the entry of [mpfr_subnormalize], of how to emulate
    IEEE 754 binary64 arithmetic with MPFR. *)

(** The ternary value [t] of an MPFR result [v] for the exact result [r]
    (§4.4 "Rounding"): 0 if [v] is [r], positive if [v] is above [r], and
    negative if below. An infinity is above or below every real, so its
    ternary value is not 0 here, as for an infinity that a function
    returns by overflow, and no NaN is the result for a real. *)
Definition ternary_ok (r : R) (v : mpfr_t) (t : Z) : Prop :=
  match v with
  | MNaN => False
  | MInf s => if s then (t < 0)%Z else (0 < t)%Z
  | MZero _ => ((t < 0)%Z <-> 0 < r) /\ (t = 0%Z <-> r = 0)
  | MNum y => ((t < 0)%Z <-> y < r) /\ (t = 0%Z <-> y = r)
  end.

(** [mpfr_set_q] (§5.2 "Assignment Functions"): the rational [q] rounded
    in the direction [rnd] to an MPFR number of 53 bits, and its ternary
    value. The entry says that [mpfr_set_q] might fail if the numerator or
    the denominator of [q] cannot be represented as an [mpfr_t], which this
    leaves out: it assumes the rounding for every [q]. *)
Definition set_q_ok (emin emax : Z) (m : mpfr) : Prop :=
  forall rnd q,
  mpfr_round (mpfr_format emin emax) rnd (Q2R q) (fst (mpfr_set_q m emin emax rnd q)) /\
  ternary_ok (Q2R q) (fst (mpfr_set_q m emin emax rnd q))
    (snd (mpfr_set_q m emin emax rnd q)).

(** The reals that [mpfr_subnormalize] rounds to: the MPFR numbers of 53
    bits that are integer multiples of [2^(emin - 1)]. That is all of
    those whose MPFR exponent [e] is at least [emin + 52], and below that,
    in what the manual calls the subnormal exponent range, those with
    [e - emin + 1] bits. *)
Definition sub_format (emin emax : Z) (y : R) : Prop :=
  mpfr_format emin emax y /\ generic_format radix2 (FLT_exp (emin - 1) 53) y.

(** [mpfr_subnormalize] (§5.13 "Exception Related Functions"): if [x] is
    the real [r] rounded in the direction [rnd] to an MPFR number of 53
    bits, with the ternary value [t], it rounds [r] in the direction [rnd]
    to [sub_format], and returns the ternary value of that against [r],
    not against [x], as the manual says. *)
Definition subnormalize_ok (emin emax : Z) (m : mpfr) : Prop :=
  forall rnd r x t,
  mpfr_round (mpfr_format emin emax) rnd r x -> ternary_ok r x t ->
  mpfr_round (sub_format emin emax) rnd r (fst (mpfr_subnormalize m emin emax rnd x t)) /\
  ternary_ok r (fst (mpfr_subnormalize m emin emax rnd x t))
    (snd (mpfr_subnormalize m emin emax rnd x t)).

(** What the theorems about [rational_to_f64] assume of MPFR: [set_q_ok],
    [subnormalize_ok] and [get_d_ok] at the exponent range that it sets. *)
Definition parse_ok (m : mpfr) : Prop :=
  set_q_ok (-1073) 1024 m /\ subnormalize_ok (-1073) 1024 m /\ get_d_ok (-1073) 1024 m.
