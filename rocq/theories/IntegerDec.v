(** * The decorations of [floor], [ceil], [round], [round_ties_even] and [trunc]

    [impl_dec!] in [src/integer.rs] picks a decoration for the result
    [y = f x] of each of these functions, [trv] if [y] is empty, [def] if
    it is not a singleton, and otherwise [dac] or [com], as its test
    [is_not_com] says, and decorates [y] with the minimum of it and the
    decoration of the argument. Section [Round] in [Integer.v] proves
    once, for the five, that [y] is the hull of the image. Section
    [RoundDec] here proves, once too, that [impl_dec] decorates it
    correctly if, for a nonempty interval, the decoration that it picks is
    [D] of the bounds ([D_test]), and [D] of two bounds is the strongest
    decoration of the rounding on the reals between them ([D_strongest]).

    [impl_dec_correct] applies [elem_set_dec_correct] in [ElemDec.v] with
    all of R as the domain, as [dec_sign_correct] in [Sign.v] does. The
    strongest decoration of a function is the one that [dec_holds_dom]
    describes if, for [dac], the interval and the hull of the image are
    bounded ([strongest_holds]). [impl_dec] picks [dac] or [com] only for
    a singleton [y], whose bounds and those of [x] are then finite, so both
    are bounded ([round_dec_bounded]). That also gives the bound that
    [elem_set_dec_correct] asks of a [com] argument.

    These proofs are not in [Integer.v] because [DecBinary.v] and
    [ElemDec.v] import [Integer.v] for lemmas that precede its Section
    [Round], so [Integer.v] cannot import [ElemDec.v] unless those lemmas
    move to a file below it. [dec_floor_correct] and [dec_ceil_correct]
    apply [impl_dec_correct], so they are here too. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer DecBinary ElemDec.

Open Scope R_scope.

(** The strongest decoration [d] of a function [h] on [x] is the one that
    [dec_holds_dom] describes on all of R, with the hull [z] of the image,
    if [x] and [z] are bounded when [d] is [dac]: on all of R, [p_dom] is
    [p] ([p_dom_all]), and [dac] then fails to be [com] only because [h] is
    not continuous at some real of [x]. *)
Lemma strongest_holds :
  forall d h x z, is_hull (image h x) z -> strongest d h x ->
  (d = Dac -> bounded (fun r => mem r x) /\ bounded (fun r => mem r z)) ->
  dec_holds_dom (fun _ => True) h x z d.
Proof.
intros d h x z Hz [Hp Hm] Hb. destruct d; cbn [dec_holds_dom].
- (* No decoration is [ill]. *)
  exact Hp.
- (* [trv]: [def] does not hold, as it is stronger. *)
  intros Hdef. apply (p_dom_all Def h x z Hz), Hm in Hdef.
  cbn [discriminant] in Hdef. lia.
- split; [exact (proj2 (p_dom_all Def h x z Hz) Hp)|].
  intros Hdac. apply (p_dom_all Dac h x z Hz), Hm in Hdac.
  cbn [discriminant] in Hdac. lia.
- (* [dac]: with [x] and the image bounded, continuity at each real of [x]
     would give [com], which is stronger. *)
  split; [exact (proj2 (p_dom_all Dac h x z Hz) Hp)|].
  intros Hc. destruct (Hb eq_refl) as [Bx Bz].
  assert (Hcom : p Com h x).
  { split; [exact (proj1 Hp)|]. split; [exact Bx|].
    split; [exact Hc | exact (proj2 (is_hull_bounded _ _ Hz) Bz)]. }
  apply Hm in Hcom. cbn [discriminant] in Hcom. lia.
- split; [exact (proj2 (p_dom_all Dac h x z Hz) (p_Com_Dac h x Hp))|].
  exact (proj1 (proj2 (proj2 Hp))).
Qed.

Section RoundDec.

(** The variables and hypotheses of Section [Round] in [Integer.v], in the
    same order, so that [impl_dec_correct] takes them in the order that
    [round_is_hull] does. *)
Variable g : f64 -> f64.
Variable G : R -> R.
Variable f : Interval -> Interval.

Hypothesis g_finite : forall a, is_finite (g a) = is_finite a.
Hypothesis g_inf : forall s, g (B754_infinity s) = B754_infinity s.
Hypothesis g_nan : g B754_nan = B754_nan.
Hypothesis g_B2R : forall a, B2R (g a) = G (B2R a).
Hypothesis G_le : forall u v, u <= v -> G u <= G v.
Hypothesis G_near : forall t, t - 1 < G t < t + 1.
Hypothesis f_rep :
  forall x, rep (f x) = (opp (g (opp (fst (rep x)))), g (snd (rep x))).

(** [is_not_com] is the test of [impl_dec], and [D lo hi] the strongest
    decoration of [G] on the reals between [lo] and [hi]. *)
Variable is_not_com : Interval -> Interval -> bool.
Variable D : option R -> option R -> Decoration.

Hypothesis D_test :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  (if Interval.is_singleton (f x) then
     if is_not_com x (f x) then Dac else Com
   else Def) = D (bound (opp (fst (rep x)))) (bound (snd (rep x))).

Hypothesis D_strongest :
  forall x lo hi,
  (forall r, mem r x <-> in_bounds lo hi r) -> ordered lo hi ->
  strongest (D lo hi) G x.

(** If [f x] is a nonempty singleton, the bounds of [x] are finite
    ([round_singleton]), and so are those of [f x] ([round_common]), so
    both are common, hence bounded. *)
Lemma round_dec_bounded :
  forall x, valid x ->
  Interval.is_empty (f x) = false -> Interval.is_singleton (f x) = true ->
  bounded (fun r => mem r x) /\ bounded (fun r => mem r (f x)).
Proof.
intros x Hx He Hs. destruct (is_nan (fst (rep x))) eqn:Hn.
- (* An empty [x] gives an empty [f x]. *)
  destruct (round_empty g f g_nan f_rep x Hx Hn) as [_ E].
  unfold Interval.is_empty in He. rewrite E in He. discriminate He.
- rewrite (round_singleton g G f g_finite g_inf g_B2R f_rep x Hx Hn) in Hs.
  unfold bound in Hs.
  destruct (is_finite (opp (fst (rep x)))) eqn:Fa; [|discriminate Hs].
  destruct (is_finite (snd (rep x))) eqn:Fb; [|discriminate Hs].
  split; apply common_bounded.
  + now apply finite_common.
  + exact (round_common g f g_finite f_rep x Fa Fb).
Qed.

(** The decoration that [impl_dec] computes for [x] is the one that
    [dec_holds_dom] describes. *)
Lemma round_holds :
  forall x, valid x ->
  dec_holds_dom (fun _ => True) G x (f x)
    (if Interval.is_empty (f x) then Trv
     else if negb (Interval.is_singleton (f x)) then Def
     else if is_not_com x (f x) then Dac else Com).
Proof.
intros x Hx.
pose proof (round_is_hull g G f g_finite g_inf g_nan g_B2R G_le G_near f_rep x Hx)
  as Hz.
destruct (is_nan (fst (rep x))) eqn:Hn.
- (* [x] is empty, so no decoration above [trv] holds. *)
  destruct (round_empty g f g_nan f_rep x Hx Hn) as [Hx' E].
  assert (Hy : Interval.is_empty (f x) = true).
  { unfold Interval.is_empty. now rewrite E. }
  rewrite Hy. cbn [dec_holds_dom]. intros ((r & Hr) & _). exact (Hx' r Hr).
- (* [D_test]: the decoration is [D] of the bounds of [x], the strongest. *)
  destruct (round_nonempty g G f g_finite g_inf g_B2R G_le f_rep x Hx Hn)
    as (HX & Hord & _).
  pose proof (round_not_empty g f g_finite g_inf f_rep x Hx Hn) as He.
  rewrite He. cbv iota.
  apply strongest_holds; [exact Hz | |].
  + replace (if negb (Interval.is_singleton (f x)) then Def
             else if is_not_com x (f x) then Dac else Com)
      with (D (bound (opp (fst (rep x)))) (bound (snd (rep x)))).
    * exact (D_strongest x _ _ HX Hord).
    * rewrite <- D_test by assumption.
      now destruct (Interval.is_singleton (f x)).
  + intros Ed. destruct (Interval.is_singleton (f x)) eqn:Hs; [|discriminate Ed].
    exact (round_dec_bounded x Hx He Hs).
Qed.

Theorem impl_dec_correct :
  forall x, valid (itv x) ->
  if DecInterval.is_nai x then DecInterval.impl_dec f is_not_com x = x
  else
    is_hull (image G (itv x)) (itv (DecInterval.impl_dec f is_not_com x)) /\
    exists d, strongest d G (itv x) /\
      dec (DecInterval.impl_dec f is_not_com x) = dec_min d (dec x).
Proof.
intros x Hx. unfold DecInterval.impl_dec. cbv zeta.
destruct (DecInterval.is_nai x) eqn:Hnai; [reflexivity|].
assert (Hdx : dec x <> Ill).
{ intros E. unfold DecInterval.is_nai in Hnai. now rewrite E in Hnai. }
pose proof (round_is_hull g G f g_finite g_inf g_nan g_B2R G_le G_near f_rep
  (itv x) Hx) as Hz.
pose proof (round_holds (itv x) Hx) as Hh.
set (d := if Interval.is_empty (f (itv x)) then Trv
          else if negb (Interval.is_singleton (f (itv x))) then Def
          else if is_not_com (itv x) (f (itv x)) then Dac else Com) in *.
assert (Hd : d <> Ill).
{ unfold d. destruct (Interval.is_empty _); [discriminate|].
  destruct (negb _); [discriminate|]. destruct (is_not_com _ _); discriminate. }
(* [impl_dec] picks [com] only for a nonempty singleton [f x], so [x] is
   bounded. *)
assert (Hb : d = Com -> dec x = Com ->
             Interval.is_common_interval (f (itv x)) = true ->
             bounded (fun r => mem r (itv x))).
{ intros Ed _ _. unfold d in Ed.
  destruct (Interval.is_empty (f (itv x))) eqn:He; [discriminate Ed|].
  destruct (Interval.is_singleton (f (itv x))) eqn:Hs; [|discriminate Ed].
  exact (proj1 (round_dec_bounded (itv x) Hx He Hs)). }
replace (dec_min d (dec x)) with (dec_min (dec x) d)
  by (destruct d, (dec x); reflexivity).
pose proof (elem_set_dec_correct (fun _ => True) G x (f (itv x)) d Hx Hdx
  (hull_tightest_all _ _ _ Hz) Hh Hb) as H.
cbv zeta in H. destruct H as (_ & d' & Hd' & Edec).
rewrite (itv_set_dec _ _ (proj1 Hz) (dec_min_not_Ill _ _ Hdx Hd)) in Hd' |- *.
split; [exact Hz|]. exists d'.
split; [exact (proj1 (strongest_dom_all d' G (itv x) _ Hz) Hd') | exact Edec].
Qed.

End RoundDec.

(** ** [floor] *)

(** [DecInterval::floor] returns a NaI unchanged, and otherwise the result of
    [Interval::floor] with the minimum of the strongest decoration of
    [floor] on the interval and the decoration of its argument. *)
Theorem dec_floor_correct :
  forall x, valid (itv x) ->
  if DecInterval.is_nai x then DecInterval.floor x = x
  else
    is_hull (image Rfloor (itv x)) (itv (DecInterval.floor x)) /\
    exists d, strongest d Rfloor (itv x) /\
      dec (DecInterval.floor x) = dec_min d (dec x).
Proof.
exact (impl_dec_correct ffloor Rfloor Interval.floor ffloor_finite ffloor_inf
  ffloor_nan ffloor_B2R Rfloor_le Rfloor_near floor_rep _ floor_dec floor_test
  floor_strongest).
Qed.

(** ** [ceil] *)

(** [DecInterval::ceil] returns a NaI unchanged, and otherwise the result of
    [Interval::ceil] with the minimum of the strongest decoration of [ceil]
    on the interval and the decoration of its argument. *)
Theorem dec_ceil_correct :
  forall x, valid (itv x) ->
  if DecInterval.is_nai x then DecInterval.ceil x = x
  else
    is_hull (image Rceil (itv x)) (itv (DecInterval.ceil x)) /\
    exists d, strongest d Rceil (itv x) /\
      dec (DecInterval.ceil x) = dec_min d (dec x).
Proof.
exact (impl_dec_correct fceil Rceil Interval.ceil fceil_finite fceil_inf
  fceil_nan fceil_B2R Rceil_le Rceil_near ceil_rep _ ceil_dec ceil_test
  ceil_strongest).
Qed.
