(** * Rounding in a direction and negation

    [ParseRound.mpfr_round_up_opp] says that the negation of [-v]
    rounded up is [v] rounded down. [mpfr_round_down_opp] says it the
    other way round, and [pown_rnd_opp] puts the two together: the
    negation of [-r] rounded in the direction [negb up] is [r] rounded
    in the direction [up]. [DyPown.v] uses it for the odd powers of an
    [x < 0], and [FastSign.v] for the fast paths' results of either
    sign. They are in a file of their own so that [FastSign.v] need not
    require [DyPown.v], which may then require files that require
    [FastSign.v]. *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr.
From Inari Require ParseRound.

Open Scope R_scope.

(** [ParseRound.mpfr_round_up_opp] the other way round: the negation of
    [-v] rounded down is [v] rounded up. *)
Lemma mpfr_round_down_opp :
  forall v w, mpfr_round f64_format RNDD (- v) (with_val w) ->
  mpfr_round f64_format RNDU v (with_val (opp w)).
Proof.
intros v w H.
destruct (is_finite w) eqn:Fw.
- assert (Fo : is_finite (opp w) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fw).
  assert (Ro : (B2R (opp w) = - B2R w)%R) by apply B2R_Bopp.
  destruct (Req_dec (B2R w) 0%R) as [E0|N0].
  + destruct (ParseRound.with_val_zero w Fw E0) as (s & Es). rewrite Es in H. cbn [mpfr_round] in H.
    assert (E0' : B2R (opp w) = 0%R) by (rewrite Ro, E0; apply Ropp_0).
    destruct (ParseRound.with_val_zero _ Fo E0') as (s' & ->). cbn [mpfr_round].
    pose proof (Rnd_UP_pt_opp _ ParseRound.f64_format_opp _ _ H) as H'.
    rewrite Ropp_involutive, Ropp_0 in H'. exact H'.
  + rewrite (ParseRound.with_val_finite w Fw N0) in H. cbn [mpfr_round] in H. destruct H as (_ & H).
    assert (N0' : B2R (opp w) <> 0%R) by (rewrite Ro; lra).
    rewrite (ParseRound.with_val_finite _ Fo N0'). cbn [mpfr_round]. split; [exact N0'|].
    rewrite Ro. pose proof (Rnd_UP_pt_opp _ ParseRound.f64_format_opp _ _ H) as H'.
    rewrite Ropp_involutive in H'. exact H'.
- destruct w as [s|[|]| |s m e B]; try discriminate Fw;
    cbn [opp Bopp with_val mpfr_round negb] in *; try contradiction.
  intros g Fg. pose proof (H _ (ParseRound.f64_format_opp _ Fg)). lra.
Qed.

(** The negation of [-r] rounded in the direction [negb up] is [r]
    rounded in the direction [up]. *)
Lemma pown_rnd_opp :
  forall (up : bool) r w,
  mpfr_round f64_format (if negb up then RNDU else RNDD) (- r) (with_val w) ->
  mpfr_round f64_format (if up then RNDU else RNDD) r (with_val (opp w)).
Proof.
intros [|] r w H; cbn [negb] in H.
- exact (mpfr_round_down_opp r w H).
- exact (ParseRound.mpfr_round_up_opp r w H).
Qed.
