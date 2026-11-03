(** * Functions of two reals with any domain

    [Ieee1788.v] states what IEEE 1788 asks of a function of two reals
    defined on a set [D] of points of R² with [image2_set], [p2_set] and
    [strongest2_set]. This file shows that for a product [D1 × D2] they are
    [image2_dom], [p2_dom] and [strongest2_dom] ([*_prod]), and
    [DecBinary.v] that for all of R² they are [image2], [p2] and
    [strongest2] ([*_all]). [dec_div_correct] in [Div.v] uses
    [image2_set_prod], [continue_in2_set_prod] and [strongest2_set_prod]
    to apply [elem2_set_dec_correct] to [/], whose domain is
    [div_dom1 × div_dom2]. This file also proves once, for the
    decorated versions that [impl_dec2!] in [src/elementary.rs] defines
    ([DecInterval.elem_dec2_impl]), that the result is NaI for NaI, and
    otherwise the tightest interval, decorated as IEEE 1788 asks, from what
    the interval function returns ([elem_dec2_impl_correct], by
    [elem2_set_dec_correct] in [DecBinary.v]). The
    decoration that the interval function returns may be any of [trv],
    [def], [dac] and [com], if it is the one that [dec_holds] describes for
    the box, so the theorem gives [dec_pow_correct], for
    [Interval::pow_impl], which returns [trv] or [com], and
    [dec_atan2_correct], for [Interval::atan2_impl], which also returns
    [dac] and [def], as [atan2] is not continuous on all of its domain. *)

From Stdlib Require Import ZArith Reals Lra Lia Classical_Prop.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 DecBinary.

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
