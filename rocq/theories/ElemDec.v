(** * The decorated versions of the elementary functions

    [impl_dec!] in [src/elementary.rs] defines the decorated version of
    each elementary function. Its first arm, [DecInterval.elem_dec],
    returns [set_dec(self.x().f(), self.d())], and its second,
    [DecInterval.elem_dec_impl], for a function that also returns a
    decoration [e] for its domain, [set_dec(y, self.d().min(e))] for
    [(y, e) = self.x().f_impl()]. Neither tests for NaI: [set_dec] returns
    NaI for the decoration [ill]. This file proves once, for both, that the
    result is NaI for NaI, and otherwise the tightest interval, decorated
    as IEEE 1788 asks, from what the interval function returns.

    [elem_set_dec_correct] is the generic theorem about the decorations of
    a function [f] of one real, defined on a set [D] of reals, as
    [elem2_set_dec_correct] in [DecBinary.v] is for two: [set_dec] of the
    tightest interval [z] that contains the image of [x] under [f] on [D],
    with the minimum of the decoration of [x] and the decoration [e] that
    [dec_holds_dom] describes, returns the tightest interval, decorated as
    IEEE 1788 asks, if a [com] [x] is bounded when [e] is [com] and [z] is
    common. [elem_set_dec_trv_com] applies it to the decoration [trv] or
    [com]. [elem_dec_correct] and [elem_dec_impl_correct] below apply
    that, as do [dec_powi_correct], [dec_cos_correct], [dec_sin_correct]
    and [dec_tan_correct] in [Powi.v], [Cos.v], [Sin.v] and [Tan.v]. *)

From Stdlib Require Import ZArith Reals Lra Lia Classical_Prop.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 DecBinary Sqrt.

Open Scope R_scope.

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

(** [dec_holds_dom D f x z e] says what the decoration [e] that the
    interval function returns for [x] claims, as [dec_holds] in
    [DecBinary.v] does for a box: [trv], that [def] does not hold; [def],
    that [def] holds and [dac] does not; [dac], that [dac] holds and [f]
    is not continuous relative to [D] at some real of [x]; and [com], that
    [dac] holds and [f] is continuous relative to [D] at each real of [x].
    [p_dom] asks nothing of [z] below [com], so [dec_holds_dom] does not
    depend on it. *)
Definition dec_holds_dom (D : R -> Prop) (f : R -> R) (x z : Interval)
    (e : Decoration) : Prop :=
  match e with
  | Ill => False
  | Trv => ~ p_dom D Def f x z
  | Def => p_dom D Def f x z /\ ~ p_dom D Dac f x z
  | Dac => p_dom D Dac f x z /\ ~ (forall r, mem r x -> continue_in f D r)
  | Com => p_dom D Dac f x z /\ (forall r, mem r x -> continue_in f D r)
  end.

(** [set_dec] of the tightest interval [z] with the decoration [e] that
    the interval function returns, if [e] is the one that [dec_holds_dom]
    describes, and a [com] [x] is bounded when [e] is [com] and [z] is
    common. *)
Theorem elem_set_dec_correct :
  forall D f x z e,
  valid (itv x) -> dec x <> Ill ->
  is_tightest (image_dom D f (itv x)) z ->
  dec_holds_dom D f (itv x) z e ->
  (e = Com -> dec x = Com -> Interval.is_common_interval z = true ->
   bounded (fun r => mem r (itv x))) ->
  let y := DecInterval.set_dec z (dec_min (dec x) e) in
  is_tightest (image_dom D f (itv x)) (itv y) /\
  exists d, strongest_dom D d f (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros D f x z e Hx Hd Ht Hh Hb. cbv zeta.
pose proof (proj1 Ht) as Hz.
(* A nonempty [x] in [D] has a real whose image is in [z], so [z] is not
   empty. *)
assert (Hne : (exists r, mem r (itv x)) -> (forall r, mem r (itv x) -> D r) ->
              Interval.is_empty z = false).
{ intros (r & Hr) HD.
  apply (mem_not_empty z (f r) Hz). apply (proj1 (proj2 Ht)).
  exists r. split; [exact Hr|]. split; [exact (HD r Hr) | reflexivity]. }
destruct e; cbn [dec_holds_dom] in Hh.
- destruct Hh.
- (* [e = trv]: not even [def] holds, and [set_dec] keeps [trv] for any
     [z]. *)
  rewrite (dec_min_Trv_r _ Hd).
  destruct (Interval.is_empty z) eqn:Ez0.
  + rewrite (set_dec_empty_any z Trv Ez0 ltac:(discriminate)).
    cbn [itv dec DecInterval.EMPTY]. rewrite <- (valid_empty_eq z Hz Ez0).
    split; [exact Ht|]. exists Trv.
    split; [apply strongest_dom_Trv; exact Hh|].
    symmetry. apply dec_min_Trv_l. exact Hd.
  + assert (Hc0 : Trv = Com -> Interval.is_common_interval z = true)
      by (intros E; discriminate E).
    rewrite (set_dec_keep z Trv Ez0 ltac:(discriminate) Hc0).
    cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|]. exists Trv.
    split; [apply strongest_dom_Trv; exact Hh|].
    symmetry. apply dec_min_Trv_l. exact Hd.
- (* [e = def]: [dac] does not hold, nor [com], which implies it. The
     minimum is below [com], so [set_dec] keeps it. *)
  destruct Hh as (Hdef & Nd).
  pose proof Hdef as (Nx & HD).
  pose proof (Hne Nx HD) as Ez0.
  assert (N : dec_min (dec x) Def <> Com).
  { intros E. destruct (dec_min_Com _ _ E) as (_ & E1). discriminate E1. }
  rewrite (set_dec_keep z _ Ez0 (dec_min_not_Ill (dec x) Def Hd ltac:(discriminate))
    (fun E => False_ind _ (N E))).
  cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
  exists Def. split; [|destruct (dec x); reflexivity].
  split; [exact Hdef|].
  intros [] He; cbn [discriminant]; try lia; exfalso; apply Nd.
  + exact He.
  + (* [com] asks for continuity relative to [D], which gives it relative
       to [x], a subset of [D]. *)
    destruct He as (Nx' & HD' & _ & Hc & _).
    split; [exact Nx'|]. split; [exact HD'|].
    intros r Hr. exact (ed_continue_in_sub f D _ r (Hc r Hr) HD').
- (* [e = dac]: [com] does not hold, and [set_dec] keeps the minimum,
     which is below [com]. *)
  destruct Hh as (Hdac & Nc).
  pose proof Hdac as (Nx & HD & _).
  pose proof (Hne Nx HD) as Ez0.
  assert (N : dec_min (dec x) Dac <> Com).
  { intros E. destruct (dec_min_Com _ _ E) as (_ & E1). discriminate E1. }
  rewrite (set_dec_keep z _ Ez0 (dec_min_not_Ill (dec x) Dac Hd ltac:(discriminate))
    (fun E => False_ind _ (N E))).
  cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
  exists Dac. split; [|destruct (dec x); reflexivity].
  apply strongest_dom_Dac; [exact Hdac|].
  intros (_ & _ & _ & Hc & _). exact (Nc Hc).
- (* [e = com]: [set_dec] gets [dec x]. *)
  destruct Hh as (Hdac & Hc).
  pose proof Hdac as (Nx & HD & _).
  pose proof (Hne Nx HD) as Ez0.
  rewrite dec_min_Com_r.
  destruct (classic (dec x = Com)) as [Edx|Ndx].
  + (* [x] is [com]: [com] holds if [z] is common, as [x] is then
       bounded, and otherwise [z] is unbounded, and [set_dec] lowers
       [com] to [dac]. *)
    rewrite Edx. destruct (Interval.is_common_interval z) eqn:Cz.
    * rewrite (set_dec_keep z Com Ez0 ltac:(discriminate) (fun _ => Cz)).
      cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
      exists Com. split; [|reflexivity].
      apply strongest_dom_Com. cbn [p_dom].
      split; [exact Nx|]. split; [exact HD|].
      split; [exact (Hb eq_refl Edx eq_refl)|].
      split; [exact Hc|].
      exact (common_bounded z Cz).
    * rewrite (set_dec_lower z Com Ez0 Cz ltac:(discriminate)).
      cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
      exists Dac. split; [|reflexivity].
      apply strongest_dom_Dac; [exact Hdac|].
      intros (_ & _ & _ & _ & Bz).
      rewrite (bounded_common z Hz Ez0 Bz) in Cz. discriminate Cz.
  + (* [x] is not [com]: [set_dec] keeps [dec x], which is
       [dec_min d (dec x)] for [d] either [com] or [dac], so [d] is
       whichever of the two holds and is the stronger. *)
    rewrite (set_dec_keep z (dec x) Ez0 Hd (fun E => False_ind _ (Ndx E))).
    cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
    destruct (classic (p_dom D Com f (itv x) z)) as [Pc|Pc].
    * exists Com.
      split; [apply strongest_dom_Com; exact Pc | symmetry; apply dec_min_Com_l].
    * exists Dac.
      split; [apply strongest_dom_Dac; [exact Hdac | exact Pc]|].
      symmetry. apply dec_min_Dac_l. exact Ndx.
Qed.

(** [set_dec z (dec_min (dec x) e)] for the tightest interval [z] that
    contains the image of [x] under [f] on its domain [D], where [f] is
    continuous on [D] at each real of [x]. The decoration [e] is [trv] only
    if [x] is empty or has a real outside [D], and [com] only if [x] is a
    subset of [D]. If [x] is [com], it must be bounded when [z] is common: an
    unbounded [com] interval has a bounded result for [exp], and none for
    [sinh] or [ln]. [e] is the decoration that [dec_holds_dom] describes,
    except for an empty [x], which [com] allows: [x] is a subset of [D],
    but [def] asks for a nonempty one. [z] is then empty, and [set_dec]
    returns [EMPTY] for [trv] and [com] alike. *)
Theorem elem_set_dec_trv_com :
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
- (* [e = trv]: [dec_holds_dom] asks that [def] not hold, which is the
     hypothesis, and nothing of [x]'s bounds. *)
  assert (Hb0 : Trv = Com -> dec x = Com -> Interval.is_common_interval z = true ->
                bounded (fun r => mem r (itv x))) by (intros E; discriminate E).
  pose proof (elem_set_dec_correct D f x z Trv Hx Hd Ht Hnd Hb0) as H.
  cbv zeta in H. exact H.
- destruct (Interval.is_empty (itv x)) eqn:Ex.
  + (* [x] is empty, so its image is, and so is [z]. [set_dec] then
       returns [EMPTY] for [com] as for [trv], and [trv] is the
       decoration that [dec_holds_dom] describes, as [def] asks for a
       nonempty [x]. *)
    assert (Ez : Interval.is_empty z = true).
    { apply (no_mem_empty z Hz). apply (tightest_no_mem _ _ Ht).
      intros u (r & Hr & _). exact (mem_empty _ r Hx Ex Hr). }
    assert (Hnd : dec_holds_dom D f (itv x) z Trv).
    { intros ((r & Hr) & _). exact (mem_empty _ r Hx Ex Hr). }
    assert (Hb0 : Trv = Com -> dec x = Com -> Interval.is_common_interval z = true ->
                  bounded (fun r => mem r (itv x))) by (intros E; discriminate E).
    pose proof (elem_set_dec_correct D f x z Trv Hx Hd Ht Hnd Hb0) as H.
    cbv zeta in H.
    rewrite (set_dec_empty_any z _ Ez (dec_min_not_Ill (dec x) Trv Hd ltac:(discriminate)))
      in H.
    rewrite (set_dec_empty_any z _ Ez (dec_min_not_Ill (dec x) Com Hd ltac:(discriminate))).
    exact H.
  + (* [x] is nonempty and in [D], so [dac] holds: [f] is continuous
       relative to [D] at each real of [x], so relative to [x]. *)
    assert (Hh : dec_holds_dom D f (itv x) z Com).
    { cbn [dec_holds_dom p_dom]. split.
      - split; [exact (nonempty_mem _ Hx Ex)|]. split; [exact HD|].
        intros r Hr. exact (ed_continue_in_sub f D _ r (Hc r Hr (HD r Hr)) HD).
      - intros r Hr. exact (Hc r Hr (HD r Hr)). }
    pose proof (elem_set_dec_correct D f x z Com Hx Hd Ht Hh (fun _ => Hb)) as H.
    cbv zeta in H. exact H.
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
pose proof (elem_set_dec_trv_com D f x (h (itv x)) Com Hx Hd Ht
  (fun r Hr _ => Hc r Hr) (or_intror (conj eq_refl (conj HD Hb)))) as H.
cbv zeta in H. rewrite dec_min_Com_r in H. exact H.
Qed.

(** The second arm of [impl_dec!], for [Interval::$f_impl] as [h], which
    returns the decoration [trv] or [com] as [elem_set_dec_trv_com] asks. *)
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
exact (elem_set_dec_trv_com D f x z e Hx Hd Ht Hc He).
Qed.
