(** * [atan2] of the ideal MPFR

    [ideal_atan2_ok]: the [mpfr_atan2] of the ideal MPFR satisfies
    [atan2_ok]. Its [atan2(y, +inf)] for a finite [y] is +0 for [y > 0],
    -0 for [y < 0] and the zero [y] itself for a zero [y], as MPFR's is.
    That is more than [atan2_ok] asks: only a zero, of either sign. *)

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
- intros rnd y Fy Hy. rewrite (with_val_finite y Fy) by lra.
  exists false. cbn [ideal_atan2].
  destruct (Rlt_dec 0 (B2R y)); [reflexivity | (exfalso; lra)].
- intros rnd y Fy Hy. rewrite (with_val_finite y Fy) by lra.
  exists true. cbn [ideal_atan2].
  destruct (Rlt_dec 0 (B2R y)); [(exfalso; lra) | reflexivity].
- (* the zero [y] itself, with its sign *)
  intros rnd s. exists s. reflexivity.
- intros rnd y Fy Hy. rewrite (with_val_finite y Fy) by lra. cbn [ideal_atan2].
  destruct (Rlt_dec 0 (B2R y)); [|(exfalso; lra)]. apply round_mpfr_correct, Hr.
- intros rnd y Fy Hy. rewrite (with_val_finite y Fy) by lra. cbn [ideal_atan2].
  destruct (Rlt_dec 0 (B2R y)); [(exfalso; lra)|]. apply round_mpfr_correct, Hr.
- intros rnd x Fx.
  destruct (with_val_finite_cases x Fx) as [(s & Ex & _) | (Ex & _)];
    rewrite Ex; cbn [ideal_atan2]; apply round_mpfr_correct, Hr.
- intros rnd x Fx.
  destruct (with_val_finite_cases x Fx) as [(s & Ex & _) | (Ex & _)];
    rewrite Ex; cbn [ideal_atan2]; apply round_mpfr_correct, Hr.
Qed.
