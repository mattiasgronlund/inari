(** * [pow] and [pow_si] of the ideal MPFR

    [ideal_pow_ok] and [ideal_pown_ok]: the [mpfr_pow] and [mpfr_pow_si]
    of the ideal MPFR satisfy [pow_ok] and [pown_ok]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Mpfr MpfrRound MpfrIdeal IdealRound.

Open Scope R_scope.

(** At two finite floats in [pow_dom], [ideal_pow] is [Rpow] rounded: a
    zero [x] comes with [y > 0], which is the [MZero _, MNum t] clause, and
    the other points fall in the last finite clause. Two zeros are not in
    [pow_dom]. *)
Lemma ideal_pow_correct2 :
  forall emin emax, range_ok emin emax ->
  mpfr_correct2 emin emax pow_dom Rpow (mpfr_pow (ideal emin emax)).
Proof.
intros emin emax Hr rnd x y Fx Fy D. unfold pow_dom in D.
destruct (with_val_finite_cases x Fx) as [(s & Ex & Bx) | (Ex & Bx)];
  destruct (with_val_finite_cases y Fy) as [(s' & Ey & By) | (Ey & By)];
  rewrite Ex, Ey; cbn [mpfr_pow ideal].
- exfalso. rewrite Bx, By in D. lra.
- assert (Hy : 0 < B2R y) by (rewrite Bx in D; lra).
  rewrite Bx.
  destruct s; cbn [ideal_pow]; (destruct (Rlt_dec (B2R y) 0); [exfalso; lra|]);
    apply round_mpfr_correct, Hr.
- cbn [ideal_pow mval]. rewrite By. apply round_mpfr_correct, Hr.
- cbn [ideal_pow mval]. apply round_mpfr_correct, Hr.
Qed.

Theorem ideal_pow_ok :
  forall emin emax, range_ok emin emax -> pow_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold pow_ok. cbn [mpfr_pow ideal].
split; [exact (ideal_pow_correct2 emin emax Hr)|].
(* The special values: each clause is a test on [Rlt_dec] or [Req_dec_T]
   that the hypothesis decides. *)
repeat match goal with |- _ /\ _ => split end; intros; cbn [ideal_pow];
  repeat match goal with
  | |- context [Rlt_dec ?a ?b] => destruct (Rlt_dec a b)
  | |- context [Req_dec_T ?a ?b] => destruct (Req_dec_T a b)
  end;
  try reflexivity; try congruence; exfalso; lra.
Qed.

Theorem ideal_pown_ok :
  forall emin emax, range_ok emin emax -> pown_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold pown_ok. cbn [mpfr_pow_si ideal].
(* [split] would also solve some equations by [eq_refl], which shifts the
   bullets, so only the conjunctions are split. *)
split; [|repeat match goal with |- _ /\ _ => split end].
- (* a finite [x]: a zero comes with [n >= 0], as [pown_dom] asks *)
  intros rnd x n _ Fx D. unfold pown_dom in D.
  destruct (with_val_finite_cases x Fx) as [(s & Ex & Bx) | (Ex & Bx)];
    rewrite Ex; cbn [ideal_pow_si].
  + rewrite Bx in D |- *. destruct (Z_lt_dec n 0) as [Hn|Hn].
    * exfalso. destruct D as [D|D]; [lia | now apply D].
    * apply round_mpfr_correct, Hr.
  + apply round_mpfr_correct, Hr.
- intros rnd s n _ Hn He. cbn [ideal_pow_si].
  destruct (Z_lt_dec n 0); [|lia]. rewrite He. reflexivity.
- (* an odd [n] is not even *)
  intros rnd s n _ Hn Ho. cbn [ideal_pow_si].
  destruct (Z_lt_dec n 0); [|lia]. rewrite <- Z.negb_odd, Ho. reflexivity.
- intros rnd n _ Hn. cbn [ideal_pow_si].
  destruct (Z_lt_dec n 0); [reflexivity | lia].
- intros rnd. cbn [ideal_pow_si].
  destruct (Z_lt_dec 0 0); [lia|]. destruct (Z.eq_dec 0 0); [reflexivity | lia].
- intros rnd n _ Hn. cbn [ideal_pow_si].
  destruct (Z_lt_dec n 0); [lia|]. destruct (Z.eq_dec n 0); [lia | reflexivity].
- intros rnd n _ Hn Ho. cbn [ideal_pow_si].
  destruct (Z_lt_dec n 0); [|lia]. rewrite Ho. reflexivity.
- intros rnd n _ Hn Ho. cbn [ideal_pow_si].
  destruct (Z_lt_dec n 0); [lia|]. destruct (Z.eq_dec n 0); [lia|].
  rewrite Ho. reflexivity.
Qed.
