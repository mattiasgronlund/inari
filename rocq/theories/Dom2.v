(** * Functions of two reals with any domain

    [Ieee1788.v] states what IEEE 1788 asks of a function of two reals
    defined on a set [D] of points of R² with [image2_set], [p2_set] and
    [strongest2_set]. This file shows that for a product [D1 × D2] they are
    [image2_dom], [p2_dom] and [strongest2_dom], and for all of R² [image2],
    [p2] and [strongest2] ([*_prod], [*_all]). It also proves once, for the
    decorated versions that [impl_dec2!] in [src/elementary.rs] defines
    ([DecInterval.elem_dec2_impl]), that the result is NaI for NaI, and
    otherwise the tightest interval, decorated as IEEE 1788 asks, from what
    the interval function returns ([elem_dec2_impl_correct]). The
    decoration that the interval function returns may be any of [trv],
    [def], [dac] and [com], if it is the one that [dec_holds] describes for
    the box, so the theorem gives [dec_pow_correct], for
    [Interval::pow_impl], which returns [trv] or [com], and
    [dec_atan2_correct], for [Interval::atan2_impl], which also returns
    [dac] and [def], as [atan2] is not continuous on all of its domain. *)

From Stdlib Require Import ZArith Reals Lra Lia Classical_Prop.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 DecBinary Sqrt ElemDec.

Open Scope R_scope.

(** ** The product and all of R² as domains *)

Lemma image2_set_prod :
  forall D1 D2 f x y s,
  image2_set (fun r t => D1 r /\ D2 t) f x y s <-> image2_dom D1 D2 f x y s.
Proof.
intros D1 D2 f x y s. unfold image2_set, image2_dom. split.
- intros (r & t & Hr & Ht & [H1 H2] & Hs).
  exists r, t. exact (conj Hr (conj Ht (conj H1 (conj H2 Hs)))).
- intros (r & t & Hr & Ht & H1 & H2 & Hs).
  exists r, t. exact (conj Hr (conj Ht (conj (conj H1 H2) Hs))).
Qed.

Lemma continue_in2_set_prod :
  forall f D1 D2 r t,
  continue_in2_set f (fun r t => D1 r /\ D2 t) r t <-> continue_in2 f D1 D2 r t.
Proof.
intros f D1 D2 r t. unfold continue_in2_set, continue_in2.
split; intros H eps Heps; destruct (H eps Heps) as (delta & Hd & H');
  exists delta; (split; [exact Hd|]).
- intros r' t' H1 H2. exact (H' r' t' (conj H1 H2)).
- intros r' t' [H1 H2]. exact (H' r' t' H1 H2).
Qed.

(** A nonempty box [X × Y] is a subset of [D1 × D2] if and only if [X] is
    a subset of [D1] and [Y] of [D2]: a real of [X] and one of [Y] make a
    point of the box. *)
Lemma d2_box_prod :
  forall (X Y D1 D2 : R -> Prop), (exists r, X r) -> (exists t, Y t) ->
  (forall r t, X r -> Y t -> D1 r /\ D2 t) <->
  (forall r, X r -> D1 r) /\ (forall t, Y t -> D2 t).
Proof.
intros X Y D1 D2 (r0 & Hr0) (t0 & Ht0). split.
- intros H. split.
  + intros r Hr. exact (proj1 (H r t0 Hr Ht0)).
  + intros t Ht. exact (proj2 (H r0 t Hr0 Ht)).
- intros [H1 H2] r t Hr Ht. exact (conj (H1 r Hr) (H2 t Ht)).
Qed.

Lemma p2_set_prod :
  forall D1 D2 d f x y z,
  p2_set (fun r t => D1 r /\ D2 t) d f x y z <-> p2_dom D1 D2 d f x y z.
Proof.
intros D1 D2 d f x y z. destruct d; cbn [p2_set p2_dom]; [tauto | tauto | | |].
- (* [def] *)
  split.
  + intros (Hx & Hy & HD). split; [exact Hx|]. split; [exact Hy|].
    exact (proj1 (d2_box_prod _ _ D1 D2 Hx Hy) HD).
  + intros (Hx & Hy & HD). split; [exact Hx|]. split; [exact Hy|].
    exact (proj2 (d2_box_prod _ _ D1 D2 Hx Hy) HD).
- (* [dac] *)
  split.
  + intros (Hx & Hy & HD & Hc). split; [exact Hx|]. split; [exact Hy|].
    destruct (proj1 (d2_box_prod _ _ D1 D2 Hx Hy) HD) as [H1 H2].
    split; [exact H1|]. split; [exact H2 | exact Hc].
  + intros (Hx & Hy & H1 & H2 & Hc). split; [exact Hx|]. split; [exact Hy|].
    split; [exact (proj2 (d2_box_prod _ _ D1 D2 Hx Hy) (conj H1 H2)) | exact Hc].
- (* [com], where the continuity relative to [D1 × D2] is that of
     [continue_in2]. *)
  split.
  + intros (Hx & Hy & HD & Bx & By & Hc & Bz). split; [exact Hx|].
    split; [exact Hy|].
    destruct (proj1 (d2_box_prod _ _ D1 D2 Hx Hy) HD) as [H1 H2].
    split; [exact H1|]. split; [exact H2|]. split; [exact Bx|].
    split; [exact By|]. split; [|exact Bz].
    intros r t Hr Ht. exact (proj1 (continue_in2_set_prod f D1 D2 r t) (Hc r t Hr Ht)).
  + intros (Hx & Hy & H1 & H2 & Bx & By & Hc & Bz). split; [exact Hx|].
    split; [exact Hy|].
    split; [exact (proj2 (d2_box_prod _ _ D1 D2 Hx Hy) (conj H1 H2))|].
    split; [exact Bx|]. split; [exact By|]. split; [|exact Bz].
    intros r t Hr Ht. exact (proj2 (continue_in2_set_prod f D1 D2 r t) (Hc r t Hr Ht)).
Qed.

Lemma strongest2_set_prod :
  forall D1 D2 d f x y z,
  strongest2_set (fun r t => D1 r /\ D2 t) d f x y z <-> strongest2_dom D1 D2 d f x y z.
Proof.
intros D1 D2 d f x y z. unfold strongest2_set, strongest2_dom. split.
- intros (Hp & Hm). split; [exact (proj1 (p2_set_prod D1 D2 d f x y z) Hp)|].
  intros e He. apply Hm. exact (proj2 (p2_set_prod D1 D2 e f x y z) He).
- intros (Hp & Hm). split; [exact (proj2 (p2_set_prod D1 D2 d f x y z) Hp)|].
  intros e He. apply Hm. exact (proj1 (p2_set_prod D1 D2 e f x y z) He).
Qed.

Lemma image2_set_all :
  forall f x y s, image2_set (fun _ _ => True) f x y s <-> image2 f x y s.
Proof.
intros f x y s. unfold image2_set, image2. split.
- intros (r & t & Hr & Ht & _ & Hs). exists r, t. exact (conj Hr (conj Ht Hs)).
- intros (r & t & Hr & Ht & Hs). exists r, t. exact (conj Hr (conj Ht (conj I Hs))).
Qed.

(** Continuity relative to all of R² is [continuity2_pt]. *)
Lemma d2_continue_in2_set_all :
  forall f r t, continue_in2_set f (fun _ _ => True) r t <-> continuity2_pt f r t.
Proof.
intros f r t. unfold continue_in2_set, continuity2_pt, continue_in2.
split; intros H eps Heps; destruct (H eps Heps) as (delta & Hd & H');
  exists delta; (split; [exact Hd|]).
- intros r' t' _ _. exact (H' r' t' I).
- intros r' t' _. exact (H' r' t' I I).
Qed.

Lemma p2_set_all :
  forall d f x y z, p2_set (fun _ _ => True) d f x y z <-> p2 d f x y z.
Proof.
intros d f x y z. destruct d; cbn [p2_set p2]; [tauto | tauto | | |].
- (* [def] *)
  split.
  + intros (Hx & Hy & _). exact (conj Hx Hy).
  + intros (Hx & Hy). split; [exact Hx|]. split; [exact Hy|]. intros; exact I.
- (* [dac] *)
  split.
  + intros (Hx & Hy & _ & Hc). split; [exact Hx|]. split; [exact Hy | exact Hc].
  + intros (Hx & Hy & Hc). split; [exact Hx|]. split; [exact Hy|].
    split; [intros; exact I | exact Hc].
- (* [com] *)
  split.
  + intros (Hx & Hy & _ & Bx & By & Hc & Bz). split; [exact Hx|].
    split; [exact Hy|]. split; [exact Bx|]. split; [exact By|].
    split; [|exact Bz].
    intros r t Hr Ht. exact (proj1 (d2_continue_in2_set_all f r t) (Hc r t Hr Ht)).
  + intros (Hx & Hy & Bx & By & Hc & Bz). split; [exact Hx|].
    split; [exact Hy|]. split; [intros; exact I|]. split; [exact Bx|].
    split; [exact By|]. split; [|exact Bz].
    intros r t Hr Ht. exact (proj2 (d2_continue_in2_set_all f r t) (Hc r t Hr Ht)).
Qed.

Lemma strongest2_set_all :
  forall d f x y z, strongest2_set (fun _ _ => True) d f x y z <-> strongest2 d f x y z.
Proof.
intros d f x y z. unfold strongest2_set, strongest2. split.
- intros (Hp & Hm). split; [exact (proj1 (p2_set_all d f x y z) Hp)|].
  intros e He. apply Hm. exact (proj2 (p2_set_all e f x y z) He).
- intros (Hp & Hm). split; [exact (proj2 (p2_set_all d f x y z) Hp)|].
  intros e He. apply Hm. exact (proj1 (p2_set_all e f x y z) He).
Qed.

(** ** The strongest decoration *)

Lemma strongest2_set_Trv :
  forall D f x y z, ~ p2_set D Def f x y z -> strongest2_set D Trv f x y z.
Proof.
intros D f x y z H. split; [exact I|].
(* Each decoration above [trv] asks for a nonempty box in the domain. *)
intros [] He; cbn [discriminant]; try lia; exfalso; apply H; cbn [p2_set] in *.
- exact He.
- destruct He as (Hx & Hy & HD & _).
  split; [exact Hx|]. split; [exact Hy | exact HD].
- destruct He as (Hx & Hy & HD & _).
  split; [exact Hx|]. split; [exact Hy | exact HD].
Qed.

Lemma strongest2_set_Dac :
  forall D f x y z, p2_set D Dac f x y z -> ~ p2_set D Com f x y z ->
  strongest2_set D Dac f x y z.
Proof.
intros D f x y z Hd Hc. split; [exact Hd|].
intros [] He; cbn [discriminant]; try lia. exfalso. exact (Hc He).
Qed.

Lemma strongest2_set_Com :
  forall D f x y z, p2_set D Com f x y z -> strongest2_set D Com f x y z.
Proof.
intros D f x y z Hc. split; [exact Hc|].
intros [] _; cbn [discriminant]; lia.
Qed.

(** A function continuous at [(r, t)] relative to [D] is continuous there
    relative to any box in [D], as the points of the box near [(r, t)] are
    points of [D] near it. *)
Lemma d2_continue_in2_sub :
  forall f (D : R -> R -> Prop) (X Y : R -> Prop) r t,
  continue_in2_set f D r t -> (forall r' t', X r' -> Y t' -> D r' t') ->
  continue_in2 f X Y r t.
Proof.
intros f D X Y r t Hc HXY eps Heps. destruct (Hc eps Heps) as (delta & Hd & H).
exists delta. split; [exact Hd|].
intros r' t' Hr Ht. exact (H r' t' (HXY r' t' Hr Ht)).
Qed.

(** [dec_holds D f x y z e] says what the decoration [e] that the interval
    function returns for the box [x × y] claims: [trv], that [def] does
    not hold; [def], that [def] holds and [dac] does not; [dac], that
    [dac] holds and [f] is not continuous relative to [D] at some point of
    the box; and [com], that [dac] holds and [f] is continuous relative to
    [D] at each point of the box. [com] then holds if the box and [z] are
    bounded too, which [elem2_set_dec_correct] leaves to [set_dec] and to
    its last hypothesis. [p2_set] asks nothing of [z] below [com], so
    [dec_holds] does not depend on it. *)
Definition dec_holds (D : R -> R -> Prop) (f : R -> R -> R) (x y z : Interval)
    (e : Decoration) : Prop :=
  match e with
  | Ill => False
  | Trv => ~ p2_set D Def f x y z
  | Def => p2_set D Def f x y z /\ ~ p2_set D Dac f x y z
  | Dac =>
      p2_set D Dac f x y z /\
      ~ (forall r t, mem r x -> mem t y -> continue_in2_set f D r t)
  | Com =>
      p2_set D Dac f x y z /\
      (forall r t, mem r x -> mem t y -> continue_in2_set f D r t)
  end.

(** [dec_min] is associative and commutative. *)
Lemma d2_dec_min_assoc :
  forall a b e, dec_min a (dec_min b e) = dec_min e (dec_min a b).
Proof.
intros [] [] []; reflexivity.
Qed.

(** [set_dec] of the tightest interval [z] with the decoration [e] that
    the interval function returns, if [e] is the one that [dec_holds]
    describes, and a box of two [com] intervals is bounded when [e] is
    [com] and [z] is common. *)
Theorem elem2_set_dec_correct :
  forall D f x y z e,
  valid (itv x) -> valid (itv y) -> dec x <> Ill -> dec y <> Ill ->
  is_tightest (image2_set D f (itv x) (itv y)) z ->
  dec_holds D f (itv x) (itv y) z e ->
  (e = Com -> dec x = Com -> dec y = Com -> Interval.is_common_interval z = true ->
   bounded (fun r => mem r (itv x)) /\ bounded (fun t => mem t (itv y))) ->
  let w := DecInterval.set_dec z (dec_min (dec x) (dec_min (dec y) e)) in
  is_tightest (image2_set D f (itv x) (itv y)) (itv w) /\
  exists d, strongest2_set D d f (itv x) (itv y) (itv w) /\
    dec w = dec_min d (dec_min (dec x) (dec y)).
Proof.
intros D f x y z e Hx Hy Hdx Hdy Ht Hh Hb. cbv zeta.
pose proof (proj1 Ht) as Hz.
assert (Hm3 : forall e', e' <> Ill -> dec_min (dec x) (dec_min (dec y) e') <> Ill).
{ intros e' He'. apply dec_min_not_Ill; [exact Hdx|]. apply dec_min_not_Ill; assumption. }
(* A nonempty box in [D] has a point whose image is in [z], so [z] is not
   empty. *)
assert (Hne : (exists r, mem r (itv x)) -> (exists t, mem t (itv y)) ->
              (forall r t, mem r (itv x) -> mem t (itv y) -> D r t) ->
              Interval.is_empty z = false).
{ intros (r & Hr) (t & Htm) HD.
  apply (mem_not_empty z (f r t) Hz). apply (proj1 (proj2 Ht)).
  exists r, t. split; [exact Hr|]. split; [exact Htm|].
  split; [exact (HD r t Hr Htm) | reflexivity]. }
destruct e; cbn [dec_holds] in Hh.
- destruct Hh.
- (* [e = trv]: not even [def] holds, and [set_dec] keeps [trv] for any
     [z]. *)
  assert (Hm : dec_min (dec x) (dec y) <> Ill) by (apply dec_min_not_Ill; assumption).
  rewrite (ed_dec_min_Trv_r _ Hdy), (ed_dec_min_Trv_r _ Hdx).
  destruct (Interval.is_empty z) eqn:Ez0.
  + rewrite (set_dec_empty_any z Trv Ez0 ltac:(discriminate)).
    cbn [itv dec DecInterval.EMPTY]. rewrite <- (valid_empty_eq z Hz Ez0).
    split; [exact Ht|]. exists Trv.
    split; [apply strongest2_set_Trv; exact Hh|].
    symmetry. apply dec_min_Trv_l. exact Hm.
  + assert (Hc0 : Trv = Com -> Interval.is_common_interval z = true)
      by (intros E; discriminate E).
    rewrite (set_dec_keep z Trv Ez0 ltac:(discriminate) Hc0).
    cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|]. exists Trv.
    split; [apply strongest2_set_Trv; exact Hh|].
    symmetry. apply dec_min_Trv_l. exact Hm.
- (* [e = def]: [dac] does not hold, nor [com], which implies it. The
     minimum is below [com], so [set_dec] keeps it. *)
  destruct Hh as (Hdef & Nd).
  destruct Hdef as (Nx & Ny & HD).
  pose proof (Hne Nx Ny HD) as Ez0.
  assert (N : dec_min (dec x) (dec_min (dec y) Def) <> Com).
  { intros E. destruct (dec_min_Com _ _ E) as (_ & E1).
    destruct (dec_min_Com _ _ E1) as (_ & E2). discriminate E2. }
  rewrite (set_dec_keep z _ Ez0 (Hm3 Def ltac:(discriminate)) (fun E => False_ind _ (N E))).
  cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
  exists Def. split; [|apply d2_dec_min_assoc].
  split; [split; [exact Nx|]; split; [exact Ny | exact HD]|].
  intros [] He; cbn [discriminant]; try lia; exfalso; apply Nd.
  + exact He.
  + destruct He as (Hx' & Hy' & HD' & _ & _ & Hc & _).
    split; [exact Hx'|]. split; [exact Hy'|]. split; [exact HD'|].
    intros r t Hr Htm. exact (d2_continue_in2_sub f D _ _ r t (Hc r t Hr Htm) HD').
- (* [e = dac]: [com] does not hold, and [set_dec] keeps the minimum,
     which is below [com]. *)
  destruct Hh as (Hdac & Nc).
  pose proof Hdac as (Nx & Ny & HD & _).
  pose proof (Hne Nx Ny HD) as Ez0.
  assert (N : dec_min (dec x) (dec_min (dec y) Dac) <> Com).
  { intros E. destruct (dec_min_Com _ _ E) as (_ & E1).
    destruct (dec_min_Com _ _ E1) as (_ & E2). discriminate E2. }
  rewrite (set_dec_keep z _ Ez0 (Hm3 Dac ltac:(discriminate)) (fun E => False_ind _ (N E))).
  cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
  exists Dac. split; [|apply d2_dec_min_assoc].
  apply strongest2_set_Dac; [exact Hdac|].
  intros (_ & _ & _ & _ & _ & Hc & _). exact (Nc Hc).
- (* [e = com]: [set_dec] gets the minimum [m] of the decorations of [x]
     and [y]. *)
  destruct Hh as (Hdac & Hc).
  pose proof Hdac as (Nx & Ny & HD & _).
  pose proof (Hne Nx Ny HD) as Ez0.
  rewrite (d2_dec_min_assoc (dec x) (dec y) Com), dec_min_Com_l.
  assert (Hm : dec_min (dec x) (dec y) <> Ill) by (apply dec_min_not_Ill; assumption).
  destruct (Interval.is_common_interval z) eqn:Cz.
  + (* [z] is common: [set_dec] keeps [m], and [d] is [com] if it holds,
       and otherwise [dac], which holds. [com] holds if [m] is [com], as
       the box is then bounded. *)
    rewrite (set_dec_keep z _ Ez0 Hm (fun _ => Cz)).
    cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
    destruct (classic (p2_set D Com f (itv x) (itv y) z)) as [Pc|Pc].
    * exists Com.
      split; [apply strongest2_set_Com; exact Pc | symmetry; apply dec_min_Com_l].
    * exists Dac. split; [apply strongest2_set_Dac; [exact Hdac | exact Pc]|].
      symmetry. apply dec_min_Dac_l. intros E. apply Pc.
      destruct (dec_min_Com _ _ E) as (Edx & Edy).
      destruct (Hb eq_refl Edx Edy eq_refl) as (Bx & By).
      split; [exact Nx|]. split; [exact Ny|]. split; [exact HD|].
      split; [exact Bx|]. split; [exact By|]. split; [exact Hc|].
      exact (common_bounded z Cz).
  + (* [z] is not common, so it is unbounded and [com] does not hold, and
       [set_dec] lowers [m] to at most [dac]. *)
    rewrite (set_dec_lower z _ Ez0 Cz Hm).
    cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
    exists Dac. split; [|reflexivity].
    apply strongest2_set_Dac; [exact Hdac|].
    intros (_ & _ & _ & _ & _ & _ & Bz).
    rewrite (bounded_common z Hz Ez0 Bz) in Cz. discriminate Cz.
Qed.

(** [impl_dec2!($f, $f_impl)] for an interval function [h] that returns
    the tightest interval and a decoration that [dec_holds] describes, if
    a box of two [com] intervals is bounded when that decoration is [com]
    and the interval is common, as [elem2_set_dec_correct] asks. *)
Theorem elem_dec2_impl_correct :
  forall D f h x y, valid (itv x) -> valid (itv y) ->
  is_tightest (image2_set D f (itv x) (itv y)) (fst (h (itv x) (itv y))) ->
  dec_holds D f (itv x) (itv y) (fst (h (itv x) (itv y))) (snd (h (itv x) (itv y))) ->
  (snd (h (itv x) (itv y)) = Com -> dec x = Com -> dec y = Com ->
   Interval.is_common_interval (fst (h (itv x) (itv y))) = true ->
   bounded (fun r => mem r (itv x)) /\ bounded (fun t => mem t (itv y))) ->
  let w := DecInterval.elem_dec2_impl h x y in
  if DecInterval.is_nai x || DecInterval.is_nai y then w = DecInterval.NAI
  else
    is_tightest (image2_set D f (itv x) (itv y)) (itv w) /\
    exists d, strongest2_set D d f (itv x) (itv y) (itv w) /\
      dec w = dec_min d (dec_min (dec x) (dec y)).
Proof.
intros D f h x y Hx Hy Ht Hh Hb. cbv zeta.
unfold DecInterval.elem_dec2_impl. revert Ht Hh Hb.
destruct (h (itv x) (itv y)) as [z e]. cbn [fst snd]. intros Ht Hh Hb.
destruct (DecInterval.is_nai x || DecInterval.is_nai y) eqn:Hn.
- (* NaI has the decoration [ill], the least, so the minimum is [ill],
     and [set_dec] returns NaI for it. *)
  assert (Hm : dec_min (dec x) (dec_min (dec y) e) = Ill).
  { unfold DecInterval.is_nai in Hn. apply Bool.orb_true_iff in Hn.
    destruct (dec x), (dec y), e; destruct Hn as [Hn|Hn];
      cbn in Hn; try discriminate Hn; reflexivity. }
  unfold DecInterval.set_dec. rewrite Hm. reflexivity.
- apply Bool.orb_false_iff in Hn. destruct Hn as [Hnx Hny].
  assert (Hdx : dec x <> Ill).
  { intros E. unfold DecInterval.is_nai in Hnx. now rewrite E in Hnx. }
  assert (Hdy : dec y <> Ill).
  { intros E. unfold DecInterval.is_nai in Hny. now rewrite E in Hny. }
  exact (elem2_set_dec_correct D f x y z e Hx Hy Hdx Hdy Ht Hh Hb).
Qed.
