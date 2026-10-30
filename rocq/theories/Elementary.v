(** * The point functions of [src/elementary.rs]

    The real functions and their domains that the theorems in [Elem.v],
    [Atanh.v], [ClosedDom.v] and [Cosh.v] are stated with. Like
    [Ieee1788.v], this file has to be checked by reading, against the
    elementary functions of IEEE Std 1788-2015, which its table of required
    forward elementary functions names [exp], [exp2], [exp10], [log],
    [log2], [log10], [sinh], [cosh], [tanh], [asinh], [acosh], [atanh],
    [asin], [acos] and [atan], each with its domain.

    Stdlib has some of them: [exp], [ln], which is [log], [sinh], [cosh],
    [tanh], [arcsinh], which is [asinh], [atan], [asin] and [acos]. The
    others are defined below by the usual formulas. As in [Ieee1788.v], a
    function defined only on a domain [D] is a function from R to R whose
    values outside [D] are never used: Stdlib's [ln], for example, returns
    0 at 0 and below, and [asin] returns [-PI/2] below -1. *)

From Stdlib Require Import Reals.

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
    [sinh], [cosh], [tanh], [asinh] and [atan], [log_dom] that of [log],
    [log2] and [log10], and the others those of the functions they are
    named after. *)
Definition real_dom (r : R) : Prop := True.
Definition log_dom (r : R) : Prop := 0 < r.
Definition asin_dom (r : R) : Prop := -1 <= r <= 1.
Definition acos_dom (r : R) : Prop := -1 <= r <= 1.
Definition acosh_dom (r : R) : Prop := 1 <= r.
Definition atanh_dom (r : R) : Prop := -1 < r < 1.
