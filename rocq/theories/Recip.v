(** * [recip] of intervals is tightest and decorated correctly

    [Interval::recip] returns the tightest interval that contains the image
    of its argument under the point function [recip], [Rinv] on its domain
    R ∖ {0} ([image_dom] and [recip_dom] in [Ieee1788.v]), for either value
    of [has_fma], and [DecInterval::recip] decorates it with the minimum of
    the strongest decoration that holds and the decoration of its argument,
    as IEEE 1788 asks of a tightest interval version of a function, if the
    argument is [com] only when its interval is common.

    [Interval::recip] dispatches on the class of its argument, and
    [Interval::classify] is defined on every valid interval
    ([classify_defined] in [Abs.v]): [recip_empty] and [recip_entire] in
    [DivZero.v] prove [E], [Z] and [M], and [recip_N0], [recip_N1],
    [recip_P0] and [recip_P1] in [DivCases.v] the other four.

    [Rinv] is continuous at each real other than 0 ([Rinv_continuous]).
    The strongest decoration of [recip] on [x], with the result [z], is:
    - [trv] if [z] is empty: the image is then empty, so [x] has no real
      in the domain, and [def] asks for a nonempty subset of the domain.
    - [trv] if 0 is in [x], as [def] asks for [x] to be a subset of the
      domain. That is when [x.contains(0.0)], the test of
      [DecInterval::recip], which then passes [trv] to [set_dec]
      ([contains_zero] in [DivZero.v]).
    - [com] if [x] and [z] are nonempty and bounded.
    - [dac] otherwise.

    [dec_recip_correct] picks [trv] when [x.contains(0.0)] and [com]
    otherwise, and leaves the rest of these cases to
    [elem_set_dec_trv_com] in [ElemDec.v]. With [com], that theorem also
    asks that a [com] [x] be bounded if [z] is common.
    [recip [1, +inf]] is [[0, 1]], which is common though [x] is not
    bounded, so if [x] were [com], [set_dec] would keep [com]. So, as
    [dec_mul_correct] in [Mul.v] does, [dec_recip_correct] assumes that
    [x] is [com] only if its interval is common ([com_common]), which
    [ComCommon.v] shows of every [DecInterval] that the library makes. A
    common interval is bounded, which gives the bound. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer Sign MaxMin ComCommon DecBinary
  AddSub Abs Sqrt DivZero DivCases ElemDec.

Open Scope R_scope.

(** ** [Interval::recip] *)

Theorem recip_correct :
  forall has_fma x, valid x ->
  exists z, Interval.recip has_fma x = Some z /\
    is_tightest (image_dom recip_dom Rinv x) z.
Proof.
intros has_fma x Hx.
destruct (classify_defined x Hx) as (c & Cx).
destruct c.
- exact (recip_empty has_fma x CE Hx Cx (or_introl eq_refl)).
- exact (recip_entire has_fma x Hx Cx).
- exact (recip_N0 has_fma x Hx Cx).
- exact (recip_N1 has_fma x Hx Cx).
- exact (recip_P0 has_fma x Hx Cx).
- exact (recip_P1 has_fma x Hx Cx).
- exact (recip_empty has_fma x CZ Hx Cx (or_intror eq_refl)).
Qed.

(** ** [DecInterval::recip] *)

(** [Rinv] is [/ id], and [id] is continuous, as it is derivable. *)
Lemma Rinv_continuous : forall r, r <> 0 -> continuity_pt Rinv r.
Proof.
intros r Hr.
assert (H : continuity_pt (/ id)%F r).
{ apply continuity_pt_inv; [|exact Hr].
  apply derivable_continuous_pt, derivable_pt_id. }
exact H.
Qed.

(** [DecInterval::recip] returns NaI for NaI, and otherwise the tightest
    interval, decorated with the decoration that IEEE 1788 asks for, if
    [x] is [com] only when its interval is common. *)
Theorem dec_recip_correct :
  forall has_fma x, valid (itv x) -> com_common x ->
  exists y, DecInterval.recip has_fma x = Some y /\
    if DecInterval.is_nai x then y = x
    else
      is_tightest (image_dom recip_dom Rinv (itv x)) (itv y) /\
      exists d, strongest_dom recip_dom d Rinv (itv x) (itv y) /\
        dec y = dec_min d (dec x).
Proof.
intros has_fma x Hx Hcc. unfold DecInterval.recip.
destruct (DecInterval.is_nai x) eqn:Hnai; [exists x; split; reflexivity|].
assert (Hdx : dec x <> Ill).
{ intros E. unfold DecInterval.is_nai in Hnai. rewrite E in Hnai.
  discriminate Hnai. }
destruct (recip_correct has_fma (itv x) Hx) as (z & Ez & Hz).
cbv zeta. rewrite Ez. cbv beta iota.
exists (DecInterval.set_dec z (if Interval.contains (itv x) zero then Trv else dec x)).
split; [reflexivity|].
(* [Rinv] is continuous at each real of the domain. *)
pose proof (fun r (_ : mem r (itv x)) (Hr : recip_dom r) =>
  continuity_pt_continue_in Rinv recip_dom r (Rinv_continuous r Hr)) as Hc.
destruct (Interval.contains (itv x) zero) eqn:Hc0.
- (* 0 is in [x], and outside the domain, so [x] is not a subset of it:
     [trv]. *)
  assert (Hnd : ~ ((exists r, mem r (itv x)) /\
                   forall r, mem r (itv x) -> recip_dom r)).
  { intros (_ & HD). exact (HD 0 (proj1 (contains_zero (itv x) Hx) Hc0) eq_refl). }
  pose proof (elem_set_dec_trv_com recip_dom Rinv x z Trv Hx Hdx Hz Hc
    (or_introl (conj eq_refl Hnd))) as H.
  cbv zeta in H. rewrite (dec_min_Trv_r _ Hdx) in H. exact H.
- (* 0 is not in [x], so [x] is a subset of the domain: [com]. A [com]
     [x] is common ([com_common]), so bounded. *)
  assert (HD : forall r, mem r (itv x) -> recip_dom r).
  { intros r Hr E. subst r.
    rewrite (proj2 (contains_zero (itv x) Hx) Hr) in Hc0. discriminate Hc0. }
  pose proof (elem_set_dec_trv_com recip_dom Rinv x z Com Hx Hdx Hz Hc
    (or_intror (conj eq_refl (conj HD (fun Edx _ => common_bounded _ (Hcc Edx))))))
    as H.
  cbv zeta in H. rewrite dec_min_Com_r in H. exact H.
Qed.
