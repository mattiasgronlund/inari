(** * [mul_add] of two intervals that both contain 0 in their interior

    For [x] and [y] in [M], [x.mul_add(y, z)] computes the same four lane
    products as [x * y] in [MulMM.v], each with the lane of [z] added
    before the single rounding up, and takes [max1] of the two in each
    lane. The largest product of [x × y] and its largest negation are
    those of [MulMM.v] ([tight_mult_mixed] in [MulTight.v]). Adding the
    bound of a lane of [z] to the larger of two products is adding it to
    both and taking the larger ([uplus_umax] in [MulAddLane.v]), so
    [fma_lane_pos] and [max_least_lane] give each lane, and
    [tightest_mul_add] the tightest interval. *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Spec Ieee1788 Integer Sign MaxMin AddRu
  DecBinary Neg AddSub Classify2 Classes MulAddRu MulLane MulTight MulAddLane.

Open Scope R_scope.

(** [x.mul_add(y, z)] of two [M] intervals and a nonempty [z] returns the
    tightest interval that contains the image of [x × y × z] under
    [Rfma]. *)
Lemma mul_add_MM :
  forall has_fma x y z, valid x -> valid y -> valid z ->
  Interval.is_empty z = false ->
  Interval.classify x = Some CM -> Interval.classify y = Some CM ->
  exists w, Interval.mul_add has_fma x y z = Some w /\ is_tightest (image3 Rfma x y z) w.
Proof.
intros has_fma x y z Hx Hy Hz Ez Cx Cy.
unfold Interval.mul_add. rewrite Ez, (classify2_pair x y CM CM Cx Cy).
cbv beta iota zeta.
rewrite !mul_add_ru_correct. cbv beta iota zeta.
eexists. split; [reflexivity|].
destruct (classify_lanes x CM Hx Cx) as [Px0 Px1].
destruct (classify_lanes y CM Hy Cy) as [Py0 Py1].
destruct (classify_mem x CM Hx Cx) as [(rn & Hrn & Hrn0) (rp & Hrp & Hrp0)].
destruct (classify_mem y CM Hy Cy) as [(tn & Htn & Htn0) (tp & Htp & Htp0)].
destruct (lanes_tight x Hx (not_nan_upper _ (pos_lane_upper _ Px0)))
  as (_ & _ & _ & Tx0 & Tx1).
destruct (lanes_tight y Hy (not_nan_upper _ (pos_lane_upper _ Py0)))
  as (_ & _ & _ & Ty0 & Ty1).
(* The lanes of a nonempty [z] are finite or +inf. *)
destruct (lanes_tight z Hz Ez) as (Uz0 & Uz1 & _).
apply (tightest_mul_add x y z _
  (umax (umult (bound (fst (rep x))) (bound (snd (rep y))))
        (umult (bound (snd (rep x))) (bound (fst (rep y)))))
  (umax (umult (bound (fst (rep x))) (bound (fst (rep y))))
        (umult (bound (snd (rep x))) (bound (snd (rep y)))))
  Hz Ez).
- exists (rp * tp). apply image2_mem; assumption.
- (* The negation [-(r * t)] of a product is [r * (-t)], a product of a
     real of [x] and one of [-y]. *)
  apply (tight_ext _ (fun u => exists r t, mem r x /\ mem (- t) y /\ u = r * t)).
  + intros u. split.
    * intros (r & t & Hr & Ht & ->). exists r, (- t).
      split; [exact Hr|]. split; [exact Ht | ring].
    * intros (r & t & Hr & Ht & E). exists r, (- t).
      rewrite Ropp_involutive. split; [exact Hr|]. split; [exact Ht|].
      rewrite <- (Ropp_involutive u), E. ring.
  + (* The largest element of [-y] is [-c], and its largest negation is
       [d]. *)
    apply (tight_mult_mixed (bound (snd (rep x))) (bound (fst (rep x)))
      (bound (fst (rep y))) (bound (snd (rep y)))
      (fun r => mem r x) (fun t => mem (- t) y));
      [exact Tx1 | exact Tx0 | exact Ty0 | | exists rn; split; assumption
      | exists rp; split; assumption | exists (- tp) | exists (- tn)].
    * apply (tight_ext _ (fun t => mem t y)); [|exact Ty1].
      intros t. cbv beta. rewrite Ropp_involutive. reflexivity.
    * (* [-tp] is below 0, and its negation [tp] is in [y]. *)
      rewrite Ropp_involutive. split; [exact Htp | lra].
    * rewrite Ropp_involutive. split; [exact Htn | lra].
- apply (tight_mult_mixed (bound (snd (rep x))) (bound (fst (rep x)))
    (bound (snd (rep y))) (bound (fst (rep y)))
    (fun r => mem r x) (fun t => mem t y));
    [exact Tx1 | exact Tx0 | exact Ty1 | exact Ty0 | exists rn; split; assumption
    | exists rp; split; assumption | exists tn; split; assumption
    | exists tp; split; assumption].
- (* [max1] of [RU(-a * d + z0)] and [RU(b * -c + z0)], where [z0] is the
     first lane of [z]: adding its bound to the larger product is adding
     it to both and taking the larger. *)
  cbn [rep fst snd Generic.max Generic.shuffle02 Generic.shuffle13 Generic.swap].
  rewrite uplus_umax. apply max_least_lane; apply fma_lane_pos; assumption.
- (* [max1] of [RU(-a * -c + z1)] and [RU(b * d + z1)]. *)
  cbn [rep fst snd Generic.max Generic.shuffle02 Generic.shuffle13 Generic.swap].
  rewrite uplus_umax. apply max_least_lane; apply fma_lane_pos; assumption.
Qed.
