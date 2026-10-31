(** * [atan2] of the ideal MPFR

    [ideal_atan2_ok]: the [mpfr_atan2] of the ideal MPFR satisfies
    [atan2_ok], with the sign of the zero [atan2(±0, +inf) = ±0]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Mpfr MpfrRound MpfrIdeal IdealRound.

Open Scope R_scope.

(** At two finite floats, zeros included, [ideal_atan2] is [Ratan2]
    rounded, so the domain is not needed. *)
Lemma ideal_atan2_correct2 :
  forall emin emax, range_ok emin emax ->
  mpfr_correct2 emin emax (fun y x => y <> 0 \/ 0 < x) Ratan2
    (mpfr_atan2 (ideal emin emax)).
Proof.
intros emin emax Hr rnd y x Fy Fx _.
destruct (with_val_finite_cases y Fy) as [(s & Ey & By) | (Ey & By)];
  destruct (with_val_finite_cases x Fx) as [(s' & Ex & Bx) | (Ex & Bx)];
  rewrite Ey, Ex; cbn [mpfr_atan2 ideal ideal_atan2 mval];
  try rewrite By; try rewrite Bx; apply round_mpfr_correct, Hr.
Qed.

Theorem ideal_atan2_ok :
  forall emin emax, range_ok emin emax -> atan2_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold atan2_ok. cbn [mpfr_atan2 ideal].
split; [exact (ideal_atan2_correct2 emin emax Hr)|].
(* [split] would also solve some equations by [eq_refl], which shifts the
   bullets, so only the conjunctions are split. *)
repeat match goal with |- _ /\ _ => split end.
- intros rnd y Hy. cbn [ideal_atan2].
  destruct (Rlt_dec 0 y); [reflexivity | (exfalso; lra)].
- intros rnd y Hy. cbn [ideal_atan2].
  destruct (Rlt_dec 0 y); [(exfalso; lra) | reflexivity].
- (* the zero [y] itself, with its sign *)
  intros rnd s. reflexivity.
- intros rnd y Hy. cbn [ideal_atan2].
  destruct (Rlt_dec 0 y); [|(exfalso; lra)]. apply round_mpfr_correct, Hr.
- intros rnd y Hy. cbn [ideal_atan2].
  destruct (Rlt_dec 0 y); [(exfalso; lra)|]. apply round_mpfr_correct, Hr.
- intros rnd x Fx.
  destruct (with_val_finite_cases x Fx) as [(s & Ex & _) | (Ex & _)];
    rewrite Ex; cbn [ideal_atan2]; apply round_mpfr_correct, Hr.
- intros rnd x Fx.
  destruct (with_val_finite_cases x Fx) as [(s & Ex & _) | (Ex & _)];
    rewrite Ex; cbn [ideal_atan2]; apply round_mpfr_correct, Hr.
Qed.
