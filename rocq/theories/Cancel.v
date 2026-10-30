(** * [cancel_minus] and [cancel_plus] of intervals are correct

    [Interval::cancel_minus] returns, as its doc comment states, the
    tightest interval [z] such that [rhs + z ⊇ self] if IEEE 1788's
    cancelMinus has a value, and [Interval::ENTIRE] otherwise
    ([cancel_result] in [Ieee1788.v]). The cases are those of the code:

    - [self] empty and [rhs] empty or common: the empty interval
      ([cancel_empty]).
    - [self] not common, or [rhs] empty or not common: cancelMinus has no
      value ([not_defined]), as an interval that is neither empty nor
      common is unbounded ([not_common_unbounded]).
    - Both common: [cancel_common_eq] gives the lanes of [sub_ru] if the
      width of [rhs] is at most that of [self], which [sub_lanes_tightest]
      shows to be the tightest interval that contains [[a - c, b - d]], and
      [Interval::ENTIRE] otherwise ([cancel_common]).

    [cancel_plus x y] is [cancel_minus x (-y)] in the model, and the reals
    of [-y] are the negations of those of [y] ([neg_mem]). The decorated
    versions return NaI if an argument is NaI, and otherwise the result of
    the bare version decorated [trv], which [set_dec] keeps, as IEEE 1788
    asks of a "trivial" decorated version. *)

From Stdlib Require Import Bool ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Ieee1788 Integer MaxMin DecBinary Neg CancelSpec
  CancelLanes CancelWidths CancelHull.

Open Scope R_scope.

(** The first two [return]s of [cancel_minus]. *)
Lemma cancel_minus_empty_eq :
  forall x y,
  Interval.is_empty x && (Interval.is_empty y || Interval.is_common_interval y) = true ->
  Interval.cancel_minus x y = Some Interval.EMPTY.
Proof.
intros x y H. unfold Interval.cancel_minus. rewrite H. reflexivity.
Qed.

Lemma cancel_minus_entire_eq :
  forall x y,
  Interval.is_empty x && (Interval.is_empty y || Interval.is_common_interval y) = false ->
  negb (Interval.is_common_interval x) || Interval.is_empty y
    || negb (Interval.is_common_interval y) = true ->
  Interval.cancel_minus x y = Some Interval.ENTIRE.
Proof.
intros x y H1 H2. unfold Interval.cancel_minus. rewrite H1, H2. reflexivity.
Qed.

Theorem cancel_minus_correct :
  forall x y, valid x -> valid y ->
  exists z, Interval.cancel_minus x y = Some z /\
    cancel_result (fun r => mem r x) (fun r => mem r y) z.
Proof.
intros x y Hx Hy.
destruct (Interval.is_empty x && (Interval.is_empty y || Interval.is_common_interval y))
  eqn:H1.
{ (* [x] is empty and [y] empty or common, so bounded. *)
  exists Interval.EMPTY. split; [exact (cancel_minus_empty_eq x y H1)|].
  apply andb_true_iff in H1 as (Ex & H1). apply cancel_empty; [exact (empty_no_mem x Hx Ex)|].
  apply orb_true_iff in H1 as [Ey|Cy]; [|exact (common_bounded y Hy Cy)].
  exists 0. intros r Hr. destruct (empty_no_mem y Hy Ey r Hr). }
destruct (negb (Interval.is_common_interval x) || Interval.is_empty y
            || negb (Interval.is_common_interval y)) eqn:H2.
{ (* cancelMinus has no value. *)
  exists Interval.ENTIRE. split; [exact (cancel_minus_entire_eq x y H1 H2)|].
  apply cancel_undefined, not_defined.
  destruct (Interval.is_empty x) eqn:Ex.
  - (* [x] is empty, so [y] is neither empty nor common: unbounded. *)
    cbn [andb] in H1. apply orb_false_iff in H1 as (Ey & Cy).
    right. split; [exact (empty_no_mem x Hx Ex)|exact (not_common_unbounded y Hy Ey Cy)].
  - left. split; [exact (proj1 (proj2 (proj2 (lanes_ok x Hx Ex))))|].
    destruct (Interval.is_common_interval x) eqn:Cx;
      [|left; exact (not_common_unbounded x Hx Ex Cx)].
    destruct (Interval.is_empty y) eqn:Ey; [right; right; exact (empty_no_mem y Hy Ey)|].
    destruct (Interval.is_common_interval y) eqn:Cy; [discriminate H2|].
    right; left; exact (not_common_unbounded y Hy Ey Cy). }
(* Both are common. *)
apply orb_false_iff in H2 as (H2 & Cy). apply orb_false_iff in H2 as (Cx & Ey).
apply negb_false_iff in Cx. apply negb_false_iff in Cy.
rewrite (cancel_common_eq x y Hx Hy Cx Cy).
destruct (common_lanes x Hx Cx) as (_ & _ & Hxo & HX).
destruct (common_lanes y Hy Cy) as (_ & _ & Hyo & HY).
destruct (cancel_common (fun r => mem r x) (fun r => mem r y) _ _ _ _ Hxo Hyo HX HY)
  as (Hle & Hlt).
destruct (Rle_dec (B2R (snd (rep y)) + B2R (fst (rep y)))
                  (B2R (snd (rep x)) + B2R (fst (rep x)))) as [L|L];
  (eexists; split; [reflexivity|]).
- (* [d - c <= b - a]: the lanes of [sub_ru] are the tightest interval
     that contains [[a - c, b - d]]. *)
  apply Hle; [lra|]. exact (sub_lanes_tightest x y Hx Hy Cx Cy L).
- apply Hlt. lra.
Qed.

Theorem cancel_plus_correct :
  forall x y, valid x -> valid y ->
  exists z, Interval.cancel_plus x y = Some z /\
    cancel_result (fun r => mem r x) (fun r => mem (- r) y) z.
Proof.
intros x y Hx Hy. unfold Interval.cancel_plus.
destruct (neg_mem y Hy) as (Hny & Hm).
destruct (cancel_minus_correct x (Interval.neg y) Hx Hny) as (z & Ez & Hz).
exists z. split; [exact Ez|].
exact (cancel_result_ext _ _ _ _ z (fun r => iff_refl _) Hm Hz).
Qed.

(** [set_dec u Trv] of a valid [u] keeps [u] and decorates it [trv]: an
    empty valid [u] is [Interval::EMPTY], the interval of
    [DecInterval::EMPTY]. *)
Lemma set_dec_Trv :
  forall u, valid u ->
  itv (DecInterval.set_dec u Trv) = u /\ dec (DecInterval.set_dec u Trv) = Trv.
Proof.
intros u Hu. unfold DecInterval.set_dec. cbn [dec_eqb discriminant Z.eqb Pos.eqb].
destruct (Interval.is_empty u) eqn:Eu.
- split; [exact (eq_sym (valid_empty_eq u Hu Eu))|reflexivity].
- split; reflexivity.
Qed.

Theorem dec_cancel_minus_correct :
  forall x y, valid (itv x) -> valid (itv y) ->
  exists z, DecInterval.cancel_minus x y = Some z /\
    if DecInterval.is_nai x || DecInterval.is_nai y then z = DecInterval.NAI
    else
      cancel_result (fun r => mem r (itv x)) (fun r => mem r (itv y)) (itv z) /\
      dec z = Trv.
Proof.
intros x y Hx Hy. unfold DecInterval.cancel_minus.
destruct (DecInterval.is_nai x || DecInterval.is_nai y).
- exists DecInterval.NAI. split; reflexivity.
- destruct (cancel_minus_correct _ _ Hx Hy) as (u & Eu & Hu). rewrite Eu.
  destruct (set_dec_Trv u (cancel_result_valid _ _ _ Hu)) as (Iu & Du).
  exists (DecInterval.set_dec u Trv). split; [reflexivity|].
  rewrite Iu. split; [exact Hu|exact Du].
Qed.

Theorem dec_cancel_plus_correct :
  forall x y, valid (itv x) -> valid (itv y) ->
  exists z, DecInterval.cancel_plus x y = Some z /\
    if DecInterval.is_nai x || DecInterval.is_nai y then z = DecInterval.NAI
    else
      cancel_result (fun r => mem r (itv x)) (fun r => mem (- r) (itv y)) (itv z) /\
      dec z = Trv.
Proof.
intros x y Hx Hy. unfold DecInterval.cancel_plus.
destruct (DecInterval.is_nai x || DecInterval.is_nai y).
- exists DecInterval.NAI. split; reflexivity.
- destruct (cancel_plus_correct _ _ Hx Hy) as (u & Eu & Hu). rewrite Eu.
  destruct (set_dec_Trv u (cancel_result_valid _ _ _ Hu)) as (Iu & Du).
  exists (DecInterval.set_dec u Trv). split; [reflexivity|].
  rewrite Iu. split; [exact Hu|exact Du].
Qed.
