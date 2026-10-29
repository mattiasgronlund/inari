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
    [recip [1, +inf]] is [[0, 1]], which is common though [x] is not
    bounded, so if [x] were [com], [set_dec] would keep [com]. So, as
    [dec_mul_correct] in [Mul.v] does, [dec_recip_correct] assumes that
    [x] is [com] only if its interval is common ([com_common]), which
    [ComCommon.v] shows of every [DecInterval] that the library makes. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer Sign MaxMin ComCommon DecBinary
  AddSub Abs Sqrt DivZero DivCases.

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
set (d := if Interval.contains (itv x) zero then Trv else dec x).
exists (DecInterval.set_dec z d). split; [reflexivity|].
assert (Hd : d <> Ill).
{ unfold d. destruct (Interval.contains (itv x) zero);
    [discriminate | exact Hdx]. }
destruct (Interval.is_empty z) eqn:Ez0.
- (* [z] is empty, so the image is, and [x] has no real in the domain. *)
  pose proof (valid_empty_eq z (proj1 Hz) Ez0) as Ez1.
  rewrite (set_dec_empty_any z d Ez0 Hd). cbn [itv dec DecInterval.EMPTY].
  rewrite <- Ez1. split; [exact Hz|]. exists Trv.
  split; [|symmetry; apply dec_min_Trv_l; exact Hdx].
  apply strongest_dom_Trv. intros Hdef. cbn [p_dom] in Hdef.
  destruct Hdef as ((r & Hr) & HD).
  apply (mem_empty z (Rinv r) (proj1 Hz) Ez0).
  apply (proj1 (proj2 Hz)). exists r.
  split; [exact Hr|]. split; [exact (HD r Hr) | reflexivity].
- (* [x] is nonempty, as its image is. *)
  assert (Nx : Interval.is_empty (itv x) = false).
  { destruct (Interval.is_empty (itv x)) eqn:Ex; [|reflexivity].
    rewrite (no_mem_empty z (proj1 Hz)) in Ez0; [discriminate Ez0|].
    apply (tightest_no_mem _ _ Hz). intros u (r & Hr & _).
    exact (mem_empty _ r Hx Ex Hr). }
  destruct (nonempty_mem _ Hx Nx) as (r0 & Hr0).
  unfold d. destruct (Interval.contains (itv x) zero) eqn:Hc0.
  + (* 0 is in [x], and outside the domain. *)
    assert (Hc : Trv = Com -> Interval.is_common_interval z = true)
      by (intros E; discriminate E).
    rewrite (set_dec_keep z Trv Ez0 ltac:(discriminate) Hc).
    cbn [itv dec DecInterval.new_unchecked]. split; [exact Hz|].
    exists Trv. split; [|symmetry; apply dec_min_Trv_l; exact Hdx].
    apply strongest_dom_Trv. intros Hdef. cbn [p_dom] in Hdef.
    destruct Hdef as (_ & HD).
    exact (HD 0 (proj1 (contains_zero (itv x) Hx) Hc0) eq_refl).
  + (* 0 is not in [x], so [x] is in the domain, where [Rinv] is
       continuous. *)
    assert (HD : forall r, mem r (itv x) -> recip_dom r).
    { intros r Hr E. subst r.
      rewrite (proj2 (contains_zero (itv x) Hx) Hr) in Hc0. discriminate Hc0. }
    assert (Hcont : forall D r, mem r (itv x) -> continue_in Rinv D r).
    { intros D r Hr. apply continuity_pt_continue_in, Rinv_continuous, HD, Hr. }
    assert (Hdac : p_dom recip_dom Dac Rinv (itv x) z).
    { cbn [p_dom]. split; [exists r0; exact Hr0|].
      split; [exact HD|]. intros r Hr. exact (Hcont _ r Hr). }
    destruct (Interval.is_common_interval z) eqn:Cz.
    * rewrite (set_dec_keep z (dec x) Ez0 Hdx (fun _ => Cz)).
      cbn [itv dec DecInterval.new_unchecked]. split; [exact Hz|].
      destruct (Interval.is_common_interval (itv x)) eqn:Cx.
      -- (* [x] and [z] are bounded. *)
         exists Com. split; [|symmetry; apply dec_min_Com_l].
         apply strongest_dom_Com. cbn [p_dom].
         split; [exists r0; exact Hr0|]. split; [exact HD|].
         split; [exact (common_bounded _ Cx)|].
         split; [intros r Hr; exact (Hcont _ r Hr) | exact (common_bounded z Cz)].
      -- (* [x] is not common, so not bounded, as it is nonempty, and
            [com_common] gives that [x] is not [com]. *)
         assert (Hnc : dec x <> Com).
         { intros E. rewrite (Hcc E) in Cx. discriminate Cx. }
         exists Dac. split; [|symmetry; apply dec_min_Dac_l; exact Hnc].
         apply strongest_dom_Dac; [exact Hdac|].
         intros Hcom. cbn [p_dom] in Hcom. destruct Hcom as (_ & _ & Bx & _).
         rewrite (bounded_common (itv x) Hx Nx Bx) in Cx. discriminate Cx.
    * (* [z] is not common, so not bounded, as it is nonempty. *)
      rewrite (set_dec_lower z (dec x) Ez0 Cz Hdx).
      cbn [itv dec DecInterval.new_unchecked]. split; [exact Hz|].
      exists Dac. split; [|reflexivity].
      apply strongest_dom_Dac; [exact Hdac|].
      intros Hcom. cbn [p_dom] in Hcom. destruct Hcom as (_ & _ & _ & _ & Bz).
      rewrite (bounded_common z (proj1 Hz) Ez0 Bz) in Cz. discriminate Cz.
Qed.
