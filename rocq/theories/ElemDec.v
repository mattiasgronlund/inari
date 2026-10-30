(** * The decorated versions of the elementary functions

    [impl_dec!] in [src/elementary.rs] defines the decorated version of
    each elementary function. Its first arm, [DecInterval.elem_dec],
    returns [set_dec(self.x.f(), self.d)], and its second,
    [DecInterval.elem_dec_impl], for a function that also returns a
    decoration [e] for its domain, [set_dec(y, self.d.min(e))] for
    [(y, e) = self.x.f_impl()]. Neither tests for NaI: [set_dec] returns
    NaI for the decoration [ill]. This file proves once, for both, that the
    result is NaI for NaI, and otherwise the tightest interval, decorated
    as IEEE 1788 asks, from what the interval function returns. *)

From Stdlib Require Import ZArith Reals Lra Classical_Prop.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 DecBinary Sqrt.

Open Scope R_scope.

Lemma dec_min_Com_r : forall d, dec_min d Com = d.
Proof.
intros []; reflexivity.
Qed.

Lemma ed_dec_min_Trv_r : forall d, d <> Ill -> dec_min d Trv = Trv.
Proof.
intros [] Hd; first [reflexivity | now elim Hd].
Qed.

(** A function continuous at [r] relative to [D] is continuous there
    relative to any subset of [D], as the points of the subset near [r]
    are points of [D] near [r]. *)
Lemma ed_continue_in_sub :
  forall f (D X : R -> Prop) r, continue_in f D r ->
  (forall s, X s -> D s) -> continue_in f X r.
Proof.
intros f D X r Hc HXD eps Heps. destruct (Hc eps Heps) as (alp & Halp & H).
exists alp. split; [exact Halp|].
intros s [[Hs Hne] Hd]. apply H.
split; [split; [exact (HXD s Hs) | exact Hne] | exact Hd].
Qed.

Lemma elem_dec_nai :
  forall h x, DecInterval.is_nai x = true -> DecInterval.elem_dec h x = DecInterval.NAI.
Proof.
intros h [z []] H; try discriminate H. reflexivity.
Qed.

Lemma elem_dec_impl_nai :
  forall h x, DecInterval.is_nai x = true ->
  DecInterval.elem_dec_impl h x = DecInterval.NAI.
Proof.
intros h [z []] H; try discriminate H.
unfold DecInterval.elem_dec_impl. cbn [itv dec].
destruct (h z) as [y []]; reflexivity.
Qed.

(** [set_dec z (dec_min (dec x) e)] for the tightest interval [z] that
    contains the image of [x] under [f] on its domain [D], where [f] is
    continuous on [D] at each real of [x]. The decoration [e] is [trv] if
    [x] is empty or has a real outside [D], and [com] if [x] is a subset of
    [D]. If [x] is [com], it must be bounded when [z] is common: an
    unbounded [com] interval has a bounded result for [exp], and none for
    [sinh] or [ln]. *)
Theorem elem_set_dec_correct :
  forall D f x z e,
  valid (itv x) -> dec x <> Ill ->
  is_tightest (image_dom D f (itv x)) z ->
  (forall r, mem r (itv x) -> D r -> continue_in f D r) ->
  (e = Trv /\ ~ ((exists r, mem r (itv x)) /\ forall r, mem r (itv x) -> D r)) \/
  (e = Com /\ (forall r, mem r (itv x) -> D r) /\
   (dec x = Com -> Interval.is_common_interval z = true ->
    bounded (fun r => mem r (itv x)))) ->
  let y := DecInterval.set_dec z (dec_min (dec x) e) in
  is_tightest (image_dom D f (itv x)) (itv y) /\
  exists d, strongest_dom D d f (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros D f x z e Hx Hd Ht Hc He. cbv zeta.
pose proof (proj1 Ht) as Hz.
destruct He as [(Ee & Hnd) | (Ee & HD & Hb)]; subst e.
- (* [e = trv]: [x] is empty or has a real outside [D], so not even [def]
     holds, and [set_dec] keeps [trv] for any [z]. *)
  rewrite (ed_dec_min_Trv_r _ Hd).
  destruct (Interval.is_empty z) eqn:Ez0.
  + rewrite (set_dec_empty_any z Trv Ez0 ltac:(discriminate)).
    cbn [itv dec DecInterval.EMPTY]. rewrite <- (valid_empty_eq z Hz Ez0).
    split; [exact Ht|]. exists Trv.
    split; [apply strongest_dom_Trv; exact Hnd|].
    symmetry. now apply dec_min_Trv_l.
  + assert (Hc0 : Trv = Com -> Interval.is_common_interval z = true)
      by (intros E; discriminate E).
    rewrite (set_dec_keep z Trv Ez0 ltac:(discriminate) Hc0).
    cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|]. exists Trv.
    split; [apply strongest_dom_Trv; exact Hnd|].
    symmetry. now apply dec_min_Trv_l.
- (* [e = com]: [x] is a subset of [D], and [set_dec] gets [dec x]. *)
  rewrite dec_min_Com_r.
  destruct (Interval.is_empty z) eqn:Ez0.
  + (* [z] is empty, so [x] has no real, as [f] maps one into [z]. *)
    rewrite (set_dec_empty_any z (dec x) Ez0 Hd).
    cbn [itv dec DecInterval.EMPTY]. rewrite <- (valid_empty_eq z Hz Ez0).
    split; [exact Ht|]. exists Trv.
    split; [|symmetry; now apply dec_min_Trv_l].
    apply strongest_dom_Trv. intros ((r & Hr) & _).
    apply (mem_empty z (f r) Hz Ez0). apply (proj1 (proj2 Ht)).
    exists r. split; [exact Hr|]. split; [exact (HD r Hr) | reflexivity].
  + (* [z] is nonempty, so [x] is, as its image is, and [dac] holds: [f]
       is continuous relative to [D], so relative to [x]. *)
    assert (Nx : exists r, mem r (itv x)).
    { destruct (Interval.is_empty (itv x)) eqn:Ex;
        [|exact (nonempty_mem _ Hx Ex)].
      rewrite (no_mem_empty z Hz) in Ez0; [discriminate Ez0|].
      apply (tightest_no_mem _ _ Ht). intros u (r & Hr & _).
      exact (mem_empty _ r Hx Ex Hr). }
    assert (Hdac : p_dom D Dac f (itv x) z).
    { cbn [p_dom]. split; [exact Nx|]. split; [exact HD|].
      intros r Hr. exact (ed_continue_in_sub f D _ r (Hc r Hr (HD r Hr)) HD). }
    destruct (classic (dec x = Com)) as [Edx|Ndx].
    * (* [x] is [com]: [com] holds if [z] is common, as [x] is then
         bounded, and otherwise [z] is unbounded, and [set_dec] lowers
         [com] to [dac]. *)
      rewrite Edx. destruct (Interval.is_common_interval z) eqn:Cz.
      -- rewrite (set_dec_keep z Com Ez0 ltac:(discriminate) (fun _ => Cz)).
         cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
         exists Com. split; [|reflexivity].
         apply strongest_dom_Com. cbn [p_dom].
         split; [exact Nx|]. split; [exact HD|].
         split; [exact (Hb Edx eq_refl)|].
         split; [intros r Hr; exact (Hc r Hr (HD r Hr))|].
         exact (common_bounded z Cz).
      -- rewrite (set_dec_lower z Com Ez0 Cz ltac:(discriminate)).
         cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
         exists Dac. split; [|reflexivity].
         apply strongest_dom_Dac; [exact Hdac|].
         intros (_ & _ & _ & _ & Bz).
         rewrite (bounded_common z Hz Ez0 Bz) in Cz. discriminate Cz.
    * (* [x] is not [com]: [set_dec] keeps [dec x], which is
         [dec_min d (dec x)] for [d] either [com] or [dac], so [d] is
         whichever of the two holds and is the stronger. *)
      rewrite (set_dec_keep z (dec x) Ez0 Hd (fun E => False_ind _ (Ndx E))).
      cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
      destruct (classic (p_dom D Com f (itv x) z)) as [Pc|Pc].
      -- exists Com.
         split; [now apply strongest_dom_Com | symmetry; apply dec_min_Com_l].
      -- exists Dac.
         split; [now apply strongest_dom_Dac|].
         symmetry. now apply dec_min_Dac_l.
Qed.

(** The first arm of [impl_dec!], for [Interval::$f] as [h], where [x] is
    a subset of the domain [D]. *)
Theorem elem_dec_correct :
  forall D f h x, valid (itv x) ->
  is_tightest (image_dom D f (itv x)) (h (itv x)) ->
  (forall r, mem r (itv x) -> D r) ->
  (forall r, mem r (itv x) -> continue_in f D r) ->
  (dec x = Com -> Interval.is_common_interval (h (itv x)) = true ->
   bounded (fun r => mem r (itv x))) ->
  let y := DecInterval.elem_dec h x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom D f (itv x)) (itv y) /\
    exists d, strongest_dom D d f (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros D f h x Hx Ht HD Hc Hb. cbv zeta.
destruct (DecInterval.is_nai x) eqn:Hn; [now apply elem_dec_nai|].
assert (Hd : dec x <> Ill).
{ intros E. unfold DecInterval.is_nai in Hn. now rewrite E in Hn. }
pose proof (elem_set_dec_correct D f x (h (itv x)) Com Hx Hd Ht
  (fun r Hr _ => Hc r Hr) (or_intror (conj eq_refl (conj HD Hb)))) as H.
cbv zeta in H. rewrite dec_min_Com_r in H. exact H.
Qed.

(** The second arm of [impl_dec!], for [Interval::$f_impl] as [h], which
    returns the decoration [trv] or [com] as [elem_set_dec_correct] asks. *)
Theorem elem_dec_impl_correct :
  forall D f h x, valid (itv x) ->
  is_tightest (image_dom D f (itv x)) (fst (h (itv x))) ->
  (forall r, mem r (itv x) -> D r -> continue_in f D r) ->
  (snd (h (itv x)) = Trv /\
   ~ ((exists r, mem r (itv x)) /\ forall r, mem r (itv x) -> D r)) \/
  (snd (h (itv x)) = Com /\ (forall r, mem r (itv x) -> D r) /\
   (dec x = Com -> Interval.is_common_interval (fst (h (itv x))) = true ->
    bounded (fun r => mem r (itv x)))) ->
  let y := DecInterval.elem_dec_impl h x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom D f (itv x)) (itv y) /\
    exists d, strongest_dom D d f (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros D f h x Hx Ht Hc He. cbv zeta.
destruct (DecInterval.is_nai x) eqn:Hn; [now apply elem_dec_impl_nai|].
assert (Hd : dec x <> Ill).
{ intros E. unfold DecInterval.is_nai in Hn. now rewrite E in Hn. }
unfold DecInterval.elem_dec_impl. revert Ht He.
destruct (h (itv x)) as [z e]. cbn [fst snd]. intros Ht He.
exact (elem_set_dec_correct D f x z e Hx Hd Ht Hc He).
Qed.
