(** * [hypot] of the ideal MPFR

    [ideal_hypot_ok]: the [mpfr_hypot] of the ideal MPFR satisfies
    [hypot_ok]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Mpfr MpfrRound MpfrIdeal IdealRound.

Open Scope R_scope.

Theorem ideal_hypot_ok :
  forall emin emax, range_ok emin emax -> hypot_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold hypot_ok. cbn [mpfr_hypot ideal].
split; [|split].
- (* At two finite floats, zeros included, [ideal_hypot] is [Rhypot]
     rounded. *)
  intros rnd x y Fx Fy _.
  destruct (with_val_finite_cases x Fx) as [(s & Ex & Bx) | (Ex & Bx)];
    destruct (with_val_finite_cases y Fy) as [(s' & Ey & By) | (Ey & By)];
    rewrite Ex, Ey; cbn [ideal_hypot mval];
    try rewrite Bx; try rewrite By; apply round_mpfr_correct, Hr.
- intros y. reflexivity.
- intros x. destruct x; reflexivity.
Qed.
