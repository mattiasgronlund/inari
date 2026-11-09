(** * Rounding to the nearest [f64]

    The contract of the functions of the dyadic kernel rounded to
    nearest, checked by reading, as [Contract.v] is. [near_round r v]
    says that [v] is the real number [r] rounded to the nearest binary64
    number, ties to even, as IEEE 754 rounds it, and as MPFR's [RNDN] in
    the exponent range of binary64, with [mpfr_subnormalize], gives it:
    - from 2^1024 - 2^970 up in magnitude, which is [f64::MAX] and half
      of its ulp, where the tie goes to the even 2^1024, an infinity of
      the sign of [r];
    - below it, the finite [f64] whose value is [r] rounded to nearest,
      ties to even, in the format of 53 bits whose least exponent is
      -1074, and a zero that is the rounding of a nonzero [r] has the sign
      of [r]. At [r = 0], either zero, as [mpfr_round] allows either. *)

From Stdlib Require Import Reals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model.

Open Scope R_scope.

Definition near_round (r : R) (v : f64) : Prop :=
  if Rle_dec (bpow radix2 1024 - bpow radix2 970) (Rabs r) then v = B754_infinity (Rlt_bool r 0)
  else
    is_finite v = true /\
    B2R v = round radix2 (FLT_exp (-1074) 53) ZnearestE r /\
    (r <> 0 -> B2R v = 0 -> Bsign v = Rlt_bool r 0).
