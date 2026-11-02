(** * Decorations of operations on three intervals

    [set_dec_correct3] is the generic theorem about the decorations of a
    function [f] of three reals, defined on all of R³, as
    [elem2_set_dec_correct] in [DecBinary.v] is for two reals, and is
    proved the same way. [set_dec] of the tightest interval [w] that
    contains the image of the box [x × y × z] under [f], with the minimum
    of the decorations of [x], [y] and [z] and the decoration [e] that
    [dec_holds3] describes for [f] on the box, returns the tightest
    interval, decorated as IEEE 1788 asks, if a box of three [com]
    intervals is bounded when [e] is [com] and [w] is common.

    [DecInterval::mul_add] calls [set_dec] with the result [w] of
    [Interval::mul_add] on the bare intervals [x], [y] and [z] and the
    minimum of their decorations, unless an argument is NaI.
    [dec_mul_add_correct] in [MulAdd.v] applies [set_dec_correct3] with
    [e] [com] for a nonempty box, as [Rfma] is continuous, and [trv] for an
    empty one, for which [w] is empty and [set_dec] returns [EMPTY] for any
    decoration other than [ill]. *)

From Stdlib Require Import ZArith Reals Lra Lia Classical_Prop.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer Sign DecBinary.

Open Scope R_scope.

Lemma image3_mem :
  forall h x y z r t u, mem r x -> mem t y -> mem u z -> image3 h x y z (h r t u).
Proof.
intros h x y z r t u Hr Ht Hu. exists r, t, u.
split; [exact Hr|]. split; [exact Ht|]. split; [exact Hu | reflexivity].
Qed.

Lemma image3_empty :
  forall h x y z,
  (forall r, ~ mem r x) \/ (forall t, ~ mem t y) \/ (forall u, ~ mem u z) ->
  forall s, ~ image3 h x y z s.
Proof.
intros h x y z H s (r & t & u & Hr & Ht & Hu & _).
destruct H as [H|[H|H]]; [exact (H r Hr) | exact (H t Ht) | exact (H u Hu)].
Qed.

(** ** The strongest decoration on a box *)

Lemma strongest3_Dac :
  forall h x y z w, p3 Dac h x y z w -> ~ p3 Com h x y z w -> strongest3 Dac h x y z w.
Proof.
intros h x y z w Hd Hc. split; [exact Hd|].
intros [] He; cbn [discriminant]; try lia. exfalso. exact (Hc He).
Qed.

Lemma strongest3_Com :
  forall h x y z w, p3 Com h x y z w -> strongest3 Com h x y z w.
Proof.
intros h x y z w Hc. split; [exact Hc|].
intros [] _; cbn [discriminant]; lia.
Qed.

(** A function continuous at [(r, t, u)] is continuous there relative to
    any box. *)
Lemma d3_continuity3_pt_in :
  forall f (X Y Z : R -> Prop) r t u,
  continuity3_pt f r t u -> continue_in3 f X Y Z r t u.
Proof.
intros f X Y Z r t u Hc eps Heps. destruct (Hc eps Heps) as (delta & Hd & H).
exists delta. split; [exact Hd|].
intros r' t' u' _ _ _. exact (H r' t' u' I I I).
Qed.

(** [dec_holds3 f x y z w e] says what the decoration [e] claims for [f]
    on the box [x × y × z], as [dec_holds] in [DecBinary.v] does for two
    reals, with [f] defined on all of R³: [trv], that [def] does not hold;
    [def], that [def] holds and [dac] does not; [dac], that [dac] holds and
    [f] is not continuous at some point of the box; and [com], that [dac]
    holds and [f] is continuous at each point of the box. [p3] asks nothing
    of [w] below [com], so [dec_holds3] does not depend on it. *)
Definition dec_holds3 (f : R -> R -> R -> R) (x y z w : Interval) (e : Decoration) :
    Prop :=
  match e with
  | Ill => False
  | Trv => ~ p3 Def f x y z w
  | Def => p3 Def f x y z w /\ ~ p3 Dac f x y z w
  | Dac =>
      p3 Dac f x y z w /\
      ~ (forall r t u, mem r x -> mem t y -> mem u z -> continuity3_pt f r t u)
  | Com =>
      p3 Dac f x y z w /\
      (forall r t u, mem r x -> mem t y -> mem u z -> continuity3_pt f r t u)
  end.

(** [dec_min] is associative and commutative. *)
Lemma d3_dec_min_assoc :
  forall a b c e, dec_min a (dec_min b (dec_min c e)) = dec_min e (dec_min a (dec_min b c)).
Proof.
intros [] [] [] []; reflexivity.
Qed.

(** [set_dec] of the tightest interval [w] that contains the image of
    [x × y × z] under [f], with the minimum of the decorations of [x], [y],
    [z] and the decoration [e] that [dec_holds3] describes, if a box of
    three [com] intervals is bounded when [e] is [com] and [w] is common. *)
Theorem set_dec_correct3 :
  forall f x y z w e,
  valid (itv x) -> valid (itv y) -> valid (itv z) ->
  dec x <> Ill -> dec y <> Ill -> dec z <> Ill ->
  is_tightest (image3 f (itv x) (itv y) (itv z)) w ->
  dec_holds3 f (itv x) (itv y) (itv z) w e ->
  (e = Com -> dec x = Com -> dec y = Com -> dec z = Com ->
   Interval.is_common_interval w = true ->
   bounded (fun r => mem r (itv x)) /\ bounded (fun t => mem t (itv y)) /\
   bounded (fun u => mem u (itv z))) ->
  let v := DecInterval.set_dec w (dec_min (dec x) (dec_min (dec y) (dec_min (dec z) e))) in
  is_tightest (image3 f (itv x) (itv y) (itv z)) (itv v) /\
  exists d, strongest3 d f (itv x) (itv y) (itv z) (itv v) /\
    dec v = dec_min d (dec_min (dec x) (dec_min (dec y) (dec z))).
Proof.
intros f x y z w e Hx Hy Hz Hdx Hdy Hdz Ht Hh Hb. cbv zeta.
pose proof (proj1 Ht) as Hw.
assert (Hm4 :
  forall e', e' <> Ill -> dec_min (dec x) (dec_min (dec y) (dec_min (dec z) e')) <> Ill).
{ intros e' He'. apply dec_min_not_Ill; [exact Hdx|].
  apply dec_min_not_Ill; [exact Hdy|]. apply dec_min_not_Ill; assumption. }
assert (Hm : dec_min (dec x) (dec_min (dec y) (dec z)) <> Ill).
{ apply dec_min_not_Ill; [exact Hdx|]. apply dec_min_not_Ill; assumption. }
(* A nonempty box has a point whose image is in [w], so [w] is not
   empty. *)
assert (Hne : (exists r, mem r (itv x)) -> (exists t, mem t (itv y)) ->
              (exists u, mem u (itv z)) -> Interval.is_empty w = false).
{ intros (r & Hr) (t & Htm) (u & Hu).
  apply (mem_not_empty w (f r t u) Hw). apply (proj1 (proj2 Ht)).
  exact (image3_mem f _ _ _ r t u Hr Htm Hu). }
destruct e; cbn [dec_holds3] in Hh.
- destruct Hh.
- (* [e = trv]: not even [def] holds, and [set_dec] keeps [trv] for any
     [w]. *)
  assert (St : strongest3 Trv f (itv x) (itv y) (itv z) w).
  { split; [exact I|].
    (* Each decoration above [trv] asks for a nonempty box. *)
    intros [] He; cbn [discriminant]; try lia; exfalso; apply Hh; cbn [p3] in *.
    - exact He.
    - destruct He as (Hx' & Hy' & Hz' & _).
      split; [exact Hx'|]. split; [exact Hy' | exact Hz'].
    - destruct He as (Hx' & Hy' & Hz' & _).
      split; [exact Hx'|]. split; [exact Hy' | exact Hz']. }
  rewrite (dec_min_Trv_r _ Hdz), (dec_min_Trv_r _ Hdy), (dec_min_Trv_r _ Hdx).
  destruct (Interval.is_empty w) eqn:Ew0.
  + rewrite (set_dec_empty_any w Trv Ew0 ltac:(discriminate)).
    cbn [itv dec DecInterval.EMPTY]. rewrite <- (valid_empty_eq w Hw Ew0).
    split; [exact Ht|]. exists Trv. split; [exact St|].
    symmetry. apply dec_min_Trv_l. exact Hm.
  + assert (Hc0 : Trv = Com -> Interval.is_common_interval w = true)
      by (intros E; discriminate E).
    rewrite (set_dec_keep w Trv Ew0 ltac:(discriminate) Hc0).
    cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|]. exists Trv.
    split; [exact St|].
    symmetry. apply dec_min_Trv_l. exact Hm.
- (* [e = def]: [dac] does not hold, nor [com], which implies it, as
     continuity at a point implies continuity there relative to the box.
     The minimum is below [com], so [set_dec] keeps it. *)
  destruct Hh as (Hdef & Nd).
  destruct Hdef as (Nx & Ny & Nz).
  pose proof (Hne Nx Ny Nz) as Ew0.
  assert (N : dec_min (dec x) (dec_min (dec y) (dec_min (dec z) Def)) <> Com).
  { intros E. destruct (dec_min_Com _ _ E) as (_ & E1).
    destruct (dec_min_Com _ _ E1) as (_ & E2).
    destruct (dec_min_Com _ _ E2) as (_ & E3). discriminate E3. }
  rewrite (set_dec_keep w _ Ew0 (Hm4 Def ltac:(discriminate)) (fun E => False_ind _ (N E))).
  cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
  exists Def. split; [|apply d3_dec_min_assoc].
  split; [split; [exact Nx|]; split; [exact Ny | exact Nz]|].
  intros [] He; cbn [discriminant]; try lia; exfalso; apply Nd.
  + exact He.
  + destruct He as (Hx' & Hy' & Hz' & _ & _ & _ & Hc & _).
    split; [exact Hx'|]. split; [exact Hy'|]. split; [exact Hz'|].
    intros r t u Hr Htm Hu. exact (d3_continuity3_pt_in f _ _ _ r t u (Hc r t u Hr Htm Hu)).
- (* [e = dac]: [com] does not hold, and [set_dec] keeps the minimum,
     which is below [com]. *)
  destruct Hh as (Hdac & Nc).
  pose proof Hdac as (Nx & Ny & Nz & _).
  pose proof (Hne Nx Ny Nz) as Ew0.
  assert (N : dec_min (dec x) (dec_min (dec y) (dec_min (dec z) Dac)) <> Com).
  { intros E. destruct (dec_min_Com _ _ E) as (_ & E1).
    destruct (dec_min_Com _ _ E1) as (_ & E2).
    destruct (dec_min_Com _ _ E2) as (_ & E3). discriminate E3. }
  rewrite (set_dec_keep w _ Ew0 (Hm4 Dac ltac:(discriminate)) (fun E => False_ind _ (N E))).
  cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
  exists Dac. split; [|apply d3_dec_min_assoc].
  apply strongest3_Dac; [exact Hdac|].
  intros (_ & _ & _ & _ & _ & _ & Hc & _). exact (Nc Hc).
- (* [e = com]: [set_dec] gets the minimum [m] of the decorations of [x],
     [y] and [z]. *)
  destruct Hh as (Hdac & Hc).
  pose proof Hdac as (Nx & Ny & Nz & _).
  pose proof (Hne Nx Ny Nz) as Ew0.
  rewrite (d3_dec_min_assoc (dec x) (dec y) (dec z) Com), dec_min_Com_l.
  destruct (Interval.is_common_interval w) eqn:Cw.
  + (* [w] is common: [set_dec] keeps [m], and [d] is [com] if it holds,
       and otherwise [dac], which holds. [com] holds if [m] is [com], as
       the box is then bounded. *)
    rewrite (set_dec_keep w _ Ew0 Hm (fun _ => Cw)).
    cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
    destruct (classic (p3 Com f (itv x) (itv y) (itv z) w)) as [Pc|Pc].
    * exists Com.
      split; [apply strongest3_Com; exact Pc | symmetry; apply dec_min_Com_l].
    * exists Dac. split; [apply strongest3_Dac; [exact Hdac | exact Pc]|].
      symmetry. apply dec_min_Dac_l. intros E. apply Pc.
      destruct (dec_min_Com _ _ E) as (Edx & E1).
      destruct (dec_min_Com _ _ E1) as (Edy & Edz).
      destruct (Hb eq_refl Edx Edy Edz eq_refl) as (Bx & By & Bz).
      split; [exact Nx|]. split; [exact Ny|]. split; [exact Nz|].
      split; [exact Bx|]. split; [exact By|]. split; [exact Bz|].
      split; [exact Hc|]. exact (common_bounded w Cw).
  + (* [w] is not common, so it is unbounded and [com] does not hold, and
       [set_dec] lowers [m] to at most [dac]. *)
    rewrite (set_dec_lower w _ Ew0 Cw Hm).
    cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
    exists Dac. split; [|reflexivity].
    apply strongest3_Dac; [exact Hdac|].
    intros (_ & _ & _ & _ & _ & _ & _ & Bw).
    rewrite (bounded_common w Hw Ew0 Bw) in Cw. discriminate Cw.
Qed.

(** ** A continuous function of three reals *)

Section Ternary.

(** [h] is continuous at each point of R³. *)
Variable h : R -> R -> R -> R.

Hypothesis h_continuous : forall r t u, continuity3_pt h r t u.

(** The restriction of [h] to any box is continuous, as [h] is. *)
Lemma p3_Dac_continuous :
  forall x y z w, (exists r, mem r x) -> (exists t, mem t y) -> (exists u, mem u z) ->
  p3 Dac h x y z w.
Proof using h_continuous.
intros x y z w Hx Hy Hz. split; [exact Hx|]. split; [exact Hy|].
split; [exact Hz|].
intros r t u _ _ _ eps Heps.
destruct (h_continuous r t u eps Heps) as (delta & Hd & H).
exists delta. split; [exact Hd|].
intros r' t' u' _ _ _. exact (H r' t' u' I I I).
Qed.

End Ternary.
