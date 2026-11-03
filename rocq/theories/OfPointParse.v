(** * MPFR functions made of functions of [f64]s: the conversion of
    [src/parse.rs]

    The MPFR functions of [of_point p] that [rational_to_f64] calls
    satisfy [parse_ok] where [p_round_rational p] satisfies
    [round_rational_c]. *)

From Stdlib Require Import ZArith Reals Qreals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Mpfr MpfrRound MpfrIdeal IdealRound IdealGetD
  IdealParse MpfrConsistent ParseFormat ParseRound Contract OfPointCore OfPoint.

Open Scope R_scope.

(** [ternary_nz] is [ternary] where that is not 0. *)
Lemma ternary_nz_eq : forall r v, ternary r v <> 0%Z -> ternary_nz r v = ternary r v.
Proof.
intros r v H. unfold ternary_nz.
destruct (ternary r v); [contradiction | reflexivity | reflexivity].
Qed.

(** The pair that [of_point_set_q] returns when it does not return the
    result of the ideal MPFR, for a zero [f64] that rounds [r]: the zero
    is [r] rounded to an MPFR number too ([round_zero_mpfr]). If
    [inexact], [r] is not 0, so [ternary] of the zero is not 0 and
    [ternary_nz] is [ternary]. Otherwise [r] is an [f64] that rounds to
    0, so it is 0, and the ternary value 0 is right. *)
Lemma of_point_set_q_other :
  forall rnd r s inexact,
  mpfr_round f64_format rnd r (with_val (B754_zero s)) ->
  (inexact = false <-> f64_format r) ->
  mpfr_round (mpfr_format (-1073) 1024) rnd r (with_val (B754_zero s)) /\
  ternary_ok r (with_val (B754_zero s))
    (if inexact then ternary_nz r (with_val (B754_zero s)) else 0%Z).
Proof.
intros rnd r s inexact H Hinex. cbn [with_val] in H |- *.
split; [exact (round_zero_mpfr _ _ _ H)|].
assert (F0 : f64_format 0) by (exists (B754_zero false); split; reflexivity).
destruct inexact.
- assert (Hr : r <> 0).
  { intros ->. apply Hinex in F0. discriminate F0. }
  rewrite ternary_nz_eq.
  + exact (ternary_correct _ _ _ _ H).
  + cbn [ternary mval]. destruct (Rcompare_spec 0 r) as [Hc|Hc|Hc]; try discriminate.
    exfalso. apply Hr. symmetry. exact Hc.
- assert (Fr : f64_format r) by (apply Hinex; reflexivity).
  assert (Hr : 0 = r).
  { destruct rnd; cbn [mpfr_round] in H;
      [exact (Rnd_DN_pt_idempotent _ _ _ H Fr) | exact (Rnd_UP_pt_idempotent _ _ _ H Fr)]. }
  cbn [ternary_ok]. split; split; intros; first [lia | lra | exfalso; lia | exfalso; lra].
Qed.

(** [set_q_ok] of [of_point p]. Where [of_point_set_q] returns the result
    of the ideal MPFR, that is [ideal_set_q_ok]. Otherwise, the ideal
    MPFR, [ideal_subnormalize] and [ideal_get_d] round [q] to an [f64]
    ([get_d_round]) with a ternary value that is 0 exactly when [q] is an
    [f64] ([ternary_exact]), which is what [round_rational_c] says of the
    [f64] [w] of [p_round_rational p] and its flag [inexact]. So the
    flags agree, and the two [f64]s differ, which makes them zeros
    ([round_f64_unique]), and [of_point_set_q_other] applies. *)
Lemma of_point_set_q_ok :
  forall p, round_rational_c (p_round_rational p) -> set_q_ok (-1073) 1024 (of_point p).
Proof.
intros p Hc rnd q.
change (mpfr_set_q (of_point p)) with (of_point_set_q p). unfold of_point_set_q.
destruct (p_round_rational p rnd q) as [w inexact] eqn:Ew.
pose proof (Hc rnd q) as [Hw Hinex]. rewrite Ew in Hw, Hinex. cbn [fst snd] in Hw, Hinex.
pose proof (ideal_set_q_ok (-1073) 1024 0 0 range_ok_f64 rnd q) as [Rh Th].
change (mpfr_set_q (ideal 0 0)) with ideal_set_q in Rh, Th.
destruct (ideal_set_q (-1073) 1024 rnd q) as [x t] eqn:Eh.
cbn [fst snd] in Rh, Th |- *.
destruct (ideal_subnormalize (-1073) 1024 rnd x t) as [x' t'] eqn:Es.
(* The ideal pipeline: [x'] rounds [q] to [sub_format], and its [f64]
   rounds [q] to an [f64]. *)
pose proof (ideal_subnormalize_ok (-1073) 1024 0 0 range_ok_f64 rnd (Q2R q) x t Rh Th)
  as [Rx' Tx'].
change (mpfr_subnormalize (ideal 0 0)) with ideal_subnormalize in Rx', Tx'.
rewrite Es in Rx', Tx'. cbn [fst snd] in Rx', Tx'.
pose proof (get_d_round (ideal 0 0) rnd (Q2R q) x' (ideal_get_d_ok _ _ 0 0) Rx') as Hw'.
change (mpfr_get_d (ideal 0 0)) with ideal_get_d in Hw'.
assert (Ht' : t' = 0%Z <-> f64_format (Q2R q)).
{ apply (ternary_exact f64_format rnd (Q2R q) x' t'); [|exact Tx'].
  exact (mpfr_round_ext _ _ _ _ _ sub_format_f64 Rx'). }
assert (Hie : negb (t' =? 0)%Z = inexact).
{ destruct inexact; destruct (Z.eqb_spec t' 0) as [E|E]; cbn [negb]; try reflexivity; exfalso.
  - apply Ht' in E. apply Hinex in E. discriminate E.
  - apply E, Ht', Hinex. reflexivity. }
destruct (f64_eq_dec (ideal_get_d rnd x') w) as [Ed|Ed].
{ destruct (Bool.bool_dec (negb (t' =? 0)%Z) inexact) as [Eb|Eb]; [|contradiction].
  cbn [fst snd]. split; assumption. }
(* The two [f64]s differ, so they are zeros. *)
destruct (round_f64_unique rnd (Q2R q) w (ideal_get_d rnd x') Hw Hw') as [E|(s & s' & -> & _)].
{ symmetry in E. contradiction. }
cbn [fst snd]. exact (of_point_set_q_other rnd (Q2R q) s inexact Hw Hinex).
Qed.

Theorem of_point_parse_ok :
  forall p, round_rational_c (p_round_rational p) -> parse_ok (of_point p).
Proof.
intros p Hc. split; [|split].
- exact (of_point_set_q_ok p Hc).
- exact (ideal_subnormalize_ok (-1073) 1024 0 0 range_ok_f64).
- exact (of_point_get_d_ok p).
Qed.
