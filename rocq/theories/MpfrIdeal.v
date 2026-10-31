(** * An ideal MPFR

    [ideal emin emax] is a record of type [mpfr] whose functions round the
    real function in the direction asked to an MPFR number of 53 bits with
    the exponent range [emin], [emax], as [mpfr_round] with [mpfr_format]
    says, overflow and underflow included, and return at the special
    arguments the values that [Mpfr.v] states. Its [mpfr_get_d] rounds
    every real to an [f64] in the direction asked, with Flocq's
    [binary_normalize]. Its [mpfr_set_q] and [mpfr_subnormalize] take the
    range as their first two arguments, as the fields do. [MpfrConsistent.v]
    shows that, at every range with [range_ok], it satisfies every
    hypothesis on MPFR that the theorems take, so they can all hold at
    once.

    It is a witness, not a model of the MPFR that the Rust code links: it
    has to agree with what [Mpfr.v] states, and nothing else. At the
    arguments where [Mpfr.v] says nothing, such as those outside the domain
    of a function, or a special argument in a direction that [Mpfr.v] does
    not state, it returns whatever its definition gives, such as NaN or the
    rounding of the point function there, which need not be what MPFR
    returns: its [pow(-2, -inf)] is +inf, where MPFR's is +0. Everything is
    defined with Stdlib's decisions on reals and Flocq's [round], without a
    choice operator, and [Assumptions.v] shows that the theorems about
    [ideal] depend only on the four axioms of the other proofs. *)

From Stdlib Require Import ZArith Reals Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Mpfr.

Open Scope R_scope.

(** ** Rounding to an MPFR number of 53 bits *)

(** The largest MPFR number of 53 bits with the exponent range
    [emin], [emax]: [(2^53 - 1) * 2^(emax - 53)], just below [2^emax]. *)
Definition mpfr_max (emax : Z) : R := F2R (Float radix2 (2 ^ 53 - 1) (emax - 53)).

(** The real of an MPFR number: [y] for [MNum y], and 0 for the zeros and
    for NaN and the infinities, which the ideal functions do not use. *)
Definition mval (v : mpfr_t) : R := match v with MNum y => y | _ => 0 end.

(** The negation of an MPFR number, which flips the sign of a zero and of
    an infinity. *)
Definition mneg (v : mpfr_t) : mpfr_t :=
  match v with
  | MNaN => MNaN
  | MInf s => MInf (negb s)
  | MZero s => MZero (negb s)
  | MNum y => MNum (- y)
  end.

(** [r] rounded toward -inf to [mpfr_format emin emax]: -inf below the
    least MPFR number, the largest one at or above [2^emax], and otherwise
    the rounding to 53 bits if [|r|] is at least the least positive MPFR
    number [2^(emin - 1)], and below that, as MPFR has no subnormals, +0 if
    [r] is at least 0 and [-2^(emin - 1)] if it is below. *)
Definition round_dn (emin emax : Z) (r : R) : mpfr_t :=
  if Rlt_dec r (- mpfr_max emax) then MInf true
  else if Rle_dec (bpow radix2 emax) r then MNum (mpfr_max emax)
  else if Rle_dec (bpow radix2 (emin - 1)) (Rabs r)
  then MNum (round radix2 (FLX_exp 53) Zfloor r)
  else if Rle_dec 0 r then MZero false
  else MNum (- bpow radix2 (emin - 1)).

(** [r] rounded in the direction [rnd] to [mpfr_format emin emax]. Toward
    +inf it is the negation of [-r] rounded toward -inf, as [mpfr_format]
    is symmetric. *)
Definition round_mpfr (emin emax : Z) (rnd : mpfr_rnd) (r : R) : mpfr_t :=
  match rnd with
  | RNDD => round_dn emin emax r
  | RNDU => mneg (round_dn emin emax (- r))
  end.

(** ** [mpfr_get_d] *)

(** The rounding mode of Flocq for [rnd]. *)
Definition f64_mode (rnd : mpfr_rnd) : mode :=
  match rnd with RNDD => mode_DN | RNDU => mode_UP end.

(** [y] rounded in the direction [rnd] to an [f64]: its rounding to the
    format of the finite [f64]s, unbounded above, which [binary_normalize]
    keeps if it is below [2^1024] in magnitude, and otherwise replaces by
    the overflow of the direction, an infinity or the largest finite
    [f64]. *)
Definition round_f64 (rnd : mpfr_rnd) (y : R) : f64 :=
  binary_normalize 53 1024 prec_gt_0_53 prec_lt_emax_53_1024 (f64_mode rnd)
    (round_mode (f64_mode rnd) (scaled_mantissa radix2 (SpecFloat.fexp 53 1024) y))
    (cexp radix2 (SpecFloat.fexp 53 1024) y) false.

Definition ideal_get_d (rnd : mpfr_rnd) (v : mpfr_t) : f64 :=
  match v with
  | MNaN => B754_nan
  | MInf s => B754_infinity s
  | MZero s => B754_zero s
  | MNum y => round_f64 rnd y
  end.

(** ** The functions of one argument

    [ideal_fn num zero inf] is [num rnd y] at [MNum y], [zero rnd s] at the
    zero of sign [s], and [inf rnd s] at the infinity of sign [s]. For most
    functions, [num] and [zero] round the point function at [y] and at 0
    ([rnd_fn], [rnd_zero]). *)
Definition ideal_fn (num : mpfr_rnd -> R -> mpfr_t) (zero inf : mpfr_rnd -> bool -> mpfr_t)
    (rnd : mpfr_rnd) (v : mpfr_t) : mpfr_t :=
  match v with
  | MNaN => MNaN
  | MInf s => inf rnd s
  | MZero s => zero rnd s
  | MNum y => num rnd y
  end.

Definition rnd_fn (emin emax : Z) (f : R -> R) (rnd : mpfr_rnd) (y : R) : mpfr_t :=
  round_mpfr emin emax rnd (f y).

Definition rnd_zero (emin emax : Z) (f : R -> R) (rnd : mpfr_rnd) (_ : bool) : mpfr_t :=
  round_mpfr emin emax rnd (f 0).

(** NaN at both infinities, for the functions whose special values
    [Mpfr.v] does not state. *)
Definition no_inf (_ : mpfr_rnd) (_ : bool) : mpfr_t := MNaN.

(** [atanh] is -inf at -1 and +inf at 1, as [Mpfr.v] states, and
    [Ratanh] rounded elsewhere. *)
Definition rnd_atanh (emin emax : Z) (rnd : mpfr_rnd) (y : R) : mpfr_t :=
  if Req_dec_T y (-1) then MInf true
  else if Req_dec_T y 1 then MInf false
  else round_mpfr emin emax rnd (Ratanh y).

(** The infinities of [atan]: [-PI/2] and [PI/2] rounded. *)
Definition atan_inf (emin emax : Z) (rnd : mpfr_rnd) (s : bool) : mpfr_t :=
  round_mpfr emin emax rnd (if s then - (PI / 2) else PI / 2).

(** The infinities of [exp], [exp10] and [exp2]: +0 and +inf. *)
Definition exp_inf (_ : mpfr_rnd) (s : bool) : mpfr_t :=
  if s then MZero false else MInf false.

(** The zeros and infinities of the logarithms: -inf at either zero, NaN at
    -inf and +inf at +inf. *)
Definition log_zero (_ : mpfr_rnd) (_ : bool) : mpfr_t := MInf true.

Definition log_inf (_ : mpfr_rnd) (s : bool) : mpfr_t :=
  if s then MNaN else MInf false.

(** The infinities of [acosh]: NaN at -inf and +inf at +inf. *)
Definition acosh_inf (_ : mpfr_rnd) (s : bool) : mpfr_t :=
  if s then MNaN else MInf false.

(** The infinities of [sinh] and [asinh]: themselves. *)
Definition odd_inf (_ : mpfr_rnd) (s : bool) : mpfr_t := MInf s.

(** The infinities of [cosh]: +inf. *)
Definition cosh_inf (_ : mpfr_rnd) (_ : bool) : mpfr_t := MInf false.

(** The infinities of [tanh]: -1 and 1. *)
Definition tanh_inf (_ : mpfr_rnd) (s : bool) : mpfr_t :=
  if s then MNum (-1) else MNum 1.

(** ** The functions of two arguments *)

(** [atan2(y, x)]: at two finite numbers, [Ratan2] rounded, and at one
    infinity, the special values that [atan2_ok] states: [atan2(y, +inf)]
    is +0 for [y > 0], -0 for [y < 0] and the zero [y] itself for a zero
    [y], [atan2(y, -inf)] is [PI] rounded for [y > 0] and [-PI] rounded for
    [y < 0], and [atan2(+inf, x)] and [atan2(-inf, x)] are [PI/2] and
    [-PI/2] rounded. NaN elsewhere. *)
Definition ideal_atan2 (emin emax : Z) (rnd : mpfr_rnd) (y x : mpfr_t) : mpfr_t :=
  match y, x with
  | MZero s, MInf false => MZero s
  | MNum r, MInf false => if Rlt_dec 0 r then MZero false else MZero true
  | MNum r, MInf true => round_mpfr emin emax rnd (if Rlt_dec 0 r then PI else - PI)
  | MInf s, (MZero _ | MNum _) =>
      round_mpfr emin emax rnd (if s then - (PI / 2) else PI / 2)
  | (MZero _ | MNum _), (MZero _ | MNum _) =>
      round_mpfr emin emax rnd (Ratan2 (mval y) (mval x))
  | _, _ => MNaN
  end.

(** [pow(x, y)]: at two finite numbers, [Rpow] rounded, except +inf at a
    zero [x] and [y < 0], and at the other points, the special values that
    [pow_ok] states: [pow(+0, -inf) = +inf], [pow(+0, +inf) = +0],
    [pow(+0, ±0) = pow(+inf, ±0) = 1], [pow(x, ±inf)] 1 for [x = 1], +inf
    or +0 for [x < 1] by the sign of the infinity, and +0 or +inf for
    [x > 1], and [pow(+inf, y)] +0 for [y] below 0 or -inf and +inf for
    [y] above 0 or +inf. NaN elsewhere. *)
Definition ideal_pow (emin emax : Z) (rnd : mpfr_rnd) (x y : mpfr_t) : mpfr_t :=
  match x, y with
  | MZero false, MInf true => MInf false
  | MZero false, MInf false => MZero false
  | MZero false, MZero _ => MNum 1
  | MInf false, MZero _ => MNum 1
  | MNum r, MInf s =>
      if Req_dec_T r 1 then MNum 1
      else if Rlt_dec r 1 then (if s then MInf false else MZero false)
      else (if s then MZero false else MInf false)
  | MInf false, MInf s => if s then MZero false else MInf false
  | MInf false, MNum t => if Rlt_dec t 0 then MZero false else MInf false
  | MZero _, MNum t =>
      if Rlt_dec t 0 then MInf false else round_mpfr emin emax rnd (Rpow 0 t)
  | MNum _, (MZero _ | MNum _) | MZero _, MZero _ =>
      round_mpfr emin emax rnd (Rpow (mval x) (mval y))
  | _, _ => MNaN
  end.

(** [pow_si(x, n)]: at a number other than 0, [powerRZ] rounded; at a zero,
    [powerRZ 0 n] rounded for [n >= 0], and for [n < 0], +inf for an even
    [n] and the infinity of the sign of the zero for an odd one; at an
    infinity, a zero for [n < 0], 1 for [n = 0] and an infinity for
    [n > 0], negative for -inf and an odd [n] and positive otherwise, as
    [pown_ok] states. *)
Definition ideal_pow_si (emin emax : Z) (rnd : mpfr_rnd) (x : mpfr_t) (n : Z) : mpfr_t :=
  match x with
  | MNaN => MNaN
  | MZero s =>
      if Z_lt_dec n 0 then (if Z.even n then MInf false else MInf s)
      else round_mpfr emin emax rnd (powerRZ 0 n)
  | MInf s =>
      if Z_lt_dec n 0 then MZero (s && Z.odd n)
      else if Z.eq_dec n 0 then MNum 1
      else MInf (s && Z.odd n)
  | MNum y => round_mpfr emin emax rnd (powerRZ y n)
  end.

(** ** The conversions of [src/parse.rs] *)

(** The ternary value of [v] for [r]: the sign of [v - r], -1 for -inf and
    1 for +inf. *)
Definition ternary (r : R) (v : mpfr_t) : Z :=
  match v with
  | MInf s => if s then (-1)%Z else 1%Z
  | _ => match Rcompare (mval v) r with Lt => (-1)%Z | Eq => 0%Z | Gt => 1%Z end
  end.

(** [mpfr_set_q]: [q] rounded as the functions round, and its ternary
    value. It never fails, unlike MPFR 4.2.2's, which aborts, in an
    assertion of [mpfr_init2], if the numerator or the denominator has more
    than [MPFR_PREC_MAX] bits, not counting its low zero limbs. *)
Definition ideal_set_q (emin emax : Z) (rnd : mpfr_rnd) (q : Q) : mpfr_t * Z :=
  let v := round_mpfr emin emax rnd (Q2R q) in (v, ternary (Q2R q) v).

(** [y] rounded in the direction [rnd] to the multiples of [2^(emin - 1)]
    with 53 bits, as Flocq's [FLT_exp (emin - 1) 53] has them. *)
Definition round_sub (emin : Z) (rnd : mpfr_rnd) (y : R) : R :=
  round radix2 (FLT_exp (emin - 1) 53) (round_mode (f64_mode rnd)) y.

(** [mpfr_subnormalize]: [x] rounded again, in the same direction, to
    [sub_format]. If that keeps [x], the ternary value [t] stays, and
    otherwise the result is on the side of [x] away from [r], so its
    ternary value is -1 toward -inf and 1 toward +inf. A zero or an
    infinity stays as it is. *)
Definition ideal_subnormalize (emin _ : Z) (rnd : mpfr_rnd) (x : mpfr_t) (t : Z) :
    mpfr_t * Z :=
  match x with
  | MNum y =>
      let z := round_sub emin rnd y in
      if Req_dec_T z y then (x, t)
      else (MNum z, match rnd with RNDD => (-1)%Z | RNDU => 1%Z end)
  | _ => (x, t)
  end.

(** ** The record *)

Definition ideal (emin emax : Z) : mpfr := {|
  mpfr_get_d := ideal_get_d;
  mpfr_acos := ideal_fn (rnd_fn emin emax acos) (rnd_zero emin emax acos) no_inf;
  mpfr_acosh := ideal_fn (rnd_fn emin emax Racosh) (rnd_zero emin emax Racosh) acosh_inf;
  mpfr_asin := ideal_fn (rnd_fn emin emax asin) (rnd_zero emin emax asin) no_inf;
  mpfr_asinh := ideal_fn (rnd_fn emin emax arcsinh) (rnd_zero emin emax arcsinh) odd_inf;
  mpfr_atan := ideal_fn (rnd_fn emin emax atan) (rnd_zero emin emax atan) (atan_inf emin emax);
  mpfr_atan2 := ideal_atan2 emin emax;
  mpfr_atanh := ideal_fn (rnd_atanh emin emax) (rnd_zero emin emax Ratanh) no_inf;
  mpfr_cos := ideal_fn (rnd_fn emin emax cos) (rnd_zero emin emax cos) no_inf;
  mpfr_cosh := ideal_fn (rnd_fn emin emax cosh) (rnd_zero emin emax cosh) cosh_inf;
  mpfr_exp := ideal_fn (rnd_fn emin emax exp) (rnd_zero emin emax exp) exp_inf;
  mpfr_exp10 := ideal_fn (rnd_fn emin emax Rexp10) (rnd_zero emin emax Rexp10) exp_inf;
  mpfr_exp2 := ideal_fn (rnd_fn emin emax Rexp2) (rnd_zero emin emax Rexp2) exp_inf;
  mpfr_log := ideal_fn (rnd_fn emin emax ln) log_zero log_inf;
  mpfr_log10 := ideal_fn (rnd_fn emin emax Rlog10) log_zero log_inf;
  mpfr_log2 := ideal_fn (rnd_fn emin emax Rlog2) log_zero log_inf;
  mpfr_pow := ideal_pow emin emax;
  mpfr_pow_si := ideal_pow_si emin emax;
  mpfr_sin := ideal_fn (rnd_fn emin emax sin) (rnd_zero emin emax sin) no_inf;
  mpfr_sinh := ideal_fn (rnd_fn emin emax sinh) (rnd_zero emin emax sinh) odd_inf;
  mpfr_tan := ideal_fn (rnd_fn emin emax tan) (rnd_zero emin emax tan) no_inf;
  mpfr_tanh := ideal_fn (rnd_fn emin emax tanh) (rnd_zero emin emax tanh) tanh_inf;
  mpfr_set_q := ideal_set_q;
  mpfr_subnormalize := ideal_subnormalize
|}.

(** ** Finite floats as MPFR numbers *)

(** [with_val] of a finite float is a zero, whose real is 0, or [MNum] of
    its real, which is then not 0. *)
Lemma with_val_finite_cases :
  forall w : f64, is_finite w = true ->
  (exists s, with_val w = MZero s /\ B2R w = 0) \/
  (with_val w = MNum (B2R w) /\ B2R w <> 0).
Proof.
intros [s|s| |s mw ew Hw] Fw; try discriminate Fw.
- left. exists s. split; reflexivity.
- right. split; [reflexivity|]. cbn [B2R].
  apply F2R_neq_0. destruct s; discriminate.
Qed.

Lemma mval_with_val : forall w : f64, is_finite w = true -> mval (with_val w) = B2R w.
Proof.
intros [s|s| |s mw ew Hw] Fw; try discriminate Fw; reflexivity.
Qed.
