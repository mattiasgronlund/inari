(** * The point functions of [src/elementary.rs]

    The real functions and their domains that the theorems in [Elem.v],
    [Atanh.v], [ClosedDom.v], [Cosh.v], [Cos.v], [Sin.v], [Tan.v],
    [Pow.v], [Powi.v] and [Atan2.v] are stated with. Like
    [Ieee1788.v], this file has to be checked by reading, against the
    elementary functions of IEEE Std 1788-2015, which its table of required
    forward elementary functions names [pown], [pow], [exp], [exp2],
    [exp10], [log], [log2], [log10], [sin], [cos], [tan], [sinh], [cosh],
    [tanh], [asinh], [acosh], [atanh], [asin], [acos], [atan] and
    [atan2], each with its domain.

    Stdlib has some of them: [powerRZ], which is [pown], [exp], [ln],
    which is [log], [sin], [cos], [tan], [sinh], [cosh], [tanh],
    [arcsinh], which is [asinh], [atan], [asin] and [acos]. The
    others are defined below by the usual formulas. As in [Ieee1788.v], a
    function defined only on a domain [D] is a function from R to R, or
    from R² to R for [pow] and [atan2], whose values outside [D] are never
    used:
    Stdlib's [ln], for example, returns 0 at 0 and below, and [asin]
    returns [-PI/2] below -1. *)

From Stdlib Require Import ZArith Reals.

Open Scope R_scope.

(** The point functions [exp2] and [exp10]: [Rpower b r] is
    [exp (r * ln b)], i.e. [b] to the power [r]. *)
Definition Rexp2 (r : R) : R := Rpower 2 r.
Definition Rexp10 (r : R) : R := Rpower 10 r.

(** The point functions [log2] and [log10]: [Rlog b r] is [ln r / ln b]. *)
Definition Rlog2 (r : R) : R := Rlog 2 r.
Definition Rlog10 (r : R) : R := Rlog 10 r.

(** The point functions [acosh] and [atanh]. *)
Definition Racosh (r : R) : R := ln (r + sqrt (r * r - 1)).
Definition Ratanh (r : R) : R := ln ((1 + r) / (1 - r)) / 2.

(** The domains. [real_dom], all of R, is that of [exp], [exp2], [exp10],
    [sin], [cos], [sinh], [cosh], [tanh], [asinh] and [atan], [log_dom]
    that of [log], [log2] and [log10], and the others those of the
    functions they are named after: [tan_dom] is R without the odd
    multiples of [PI / 2]. *)
Definition real_dom (r : R) : Prop := True.
Definition log_dom (r : R) : Prop := 0 < r.
Definition asin_dom (r : R) : Prop := -1 <= r <= 1.
Definition acos_dom (r : R) : Prop := -1 <= r <= 1.
Definition acosh_dom (r : R) : Prop := 1 <= r.
Definition atanh_dom (r : R) : Prop := -1 < r < 1.
Definition tan_dom (r : R) : Prop := forall k : Z, r <> (IZR k + / 2) * PI.

(** The point function [pow] of two reals, [x] to the power [y]: as the
    standard defines it, [exp (y * ln x)], which is Stdlib's [Rpower x y],
    for [x > 0], and 0 for [x = 0], where its domain [pow_dom] asks
    [y > 0]. It is continuous at each point of its domain, the positive
    [y] axis included. *)
Definition Rpow (r t : R) : R := if Rle_dec r 0 then 0 else Rpower r t.
Definition pow_dom (r t : R) : Prop := 0 < r \/ (r = 0 /\ 0 < t).

(** The point function [atan2(y, x)] of two reals, with [y] first, as in
    the standard and in [self.atan2(rhs)], where [self] is [y]: the
    principal value of the argument (polar angle) of the point [(x, y)] of
    the plane, as the standard defines it. It is given by the usual
    formula, which is also that of the [mpfr_atan2] entry of the MPFR
    manual: [atan (y / x)] for [x > 0]; for [x < 0], that plus [PI] if
    [y >= 0] and minus [PI] if [y < 0]; and for [x = 0], [PI / 2] or
    [- (PI / 2)] by the sign of [y]. Its domain [atan2_dom] is R² without
    [(0, 0)], where its value 0 is never used. [AtanReal.v] proves that it
    is the argument: [Ratan2_polar] and [Ratan2_polar_unique]. *)
Definition Ratan2 (y x : R) : R :=
  if Rlt_dec 0 x then atan (y / x)
  else if Rlt_dec x 0 then
    (if Rle_dec 0 y then atan (y / x) + PI else atan (y / x) - PI)
  else if Rlt_dec 0 y then PI / 2
  else if Rlt_dec y 0 then - (PI / 2)
  else 0.
Definition atan2_dom (y x : R) : Prop := y <> 0 \/ x <> 0.

(** The point functions [pown(x, p)] for an integer [p], each a function
    of one real, are Stdlib's [powerRZ x p]: [x] multiplied by itself [p]
    times for [p > 0], [1] for [p = 0], even at [x = 0], and the inverse of
    [x] to the power [-p] for [p < 0]. The domain of [pown(x, p)] is all of
    R for [p >= 0], and R without 0 for [p < 0], where Stdlib's [powerRZ]
    returns 0 at 0, a value that is never used. *)
Definition pown_dom (n : Z) (r : R) : Prop := (0 <= n)%Z \/ r <> 0.
