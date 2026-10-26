(** * [x * y] of two intervals that both contain 0 in their interior

    If [x = [a, b]] and [y = [c, d]] with [a < 0 < b] and [c < 0 < d]
    (both of the class [M]), [x * y] multiplies [[-a; -a]] by the swapped
    [[d; -c]], and [[b; b]] by [[-c; d]], both rounded up, and takes [max1]
    of the products in each lane:
    [[max(RU(-a * d), RU(b * -c)); max(RU(-a * -c), RU(b * d))]].

    The image of [x × y] under [*] has reals of both signs. Its largest
    element is [max(a * c, b * d)] = [max(-a * -c, b * d)], the larger of
    the largest product of two negative reals and that of two positive
    reals ([tight_mult_mixed] in [MulTight.v], with [A = x] and [B = y]).
    Its largest negation [-(r * t)] is [r * (-t)], a product of a real of
    [x] and one of [-y], which also has reals of both signs. So it is
    [max(-a * d, b * -c)], by the same lemma with [B = -y], whose largest
    element is [-c] and whose largest negation is [d]. Either largest
    element is +inf ([None]) if one of its factors is ([umult]).

    The lanes of an [M] interval are above 0 ([classify_lanes]), so each
    product of two lanes rounded up is the least float or +inf at or above
    the product of their upper bounds ([mul_lane_pos] in [MulLane.v]), and
    [max1] of two such is the least at or above the larger of the two
    ([max_least_lane]). [tightest_lanes] in [AddSub.v] puts the two lanes
    together into the tightest interval. *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Spec Ieee1788 Integer Sign MaxMin AddRu
  DecBinary Neg AddSub Classify2 Classes MulRu MulLane MulTight.

Open Scope R_scope.

(** [x * y] of two [M] intervals returns the tightest interval that
    contains the image of [x × y] under [*]. *)
Lemma mul_MM :
  forall has_fma x y, valid x -> valid y ->
  Interval.classify x = Some CM -> Interval.classify y = Some CM ->
  exists z, Interval.mul has_fma x y = Some z /\ is_tightest (image2 Rmult x y) z.
Proof.
intros has_fma x y Hx Hy Cx Cy.
unfold Interval.mul. rewrite (classify2_pair x y CM CM Cx Cy). cbv beta iota zeta.
rewrite !mul_ru_correct. cbv beta iota zeta.
eexists. split; [reflexivity|].
destruct (classify_lanes x CM Hx Cx) as [Px0 Px1].
destruct (classify_lanes y CM Hy Cy) as [Py0 Py1].
destruct (classify_mem x CM Hx Cx) as [(rn & Hrn & Hrn0) (rp & Hrp & Hrp0)].
destruct (classify_mem y CM Hy Cy) as [(tn & Htn & Htn0) (tp & Htp & Htp0)].
destruct (lanes_tight x Hx (not_nan_upper _ (pos_lane_upper _ Px0)))
  as (_ & _ & _ & Tx0 & Tx1).
destruct (lanes_tight y Hy (not_nan_upper _ (pos_lane_upper _ Py0)))
  as (_ & _ & _ & Ty0 & Ty1).
apply (tightest_lanes _ _
  (umax (umult (bound (fst (rep x))) (bound (snd (rep y))))
        (umult (bound (snd (rep x))) (bound (fst (rep y)))))
  (umax (umult (bound (fst (rep x))) (bound (fst (rep y))))
        (umult (bound (snd (rep x))) (bound (snd (rep y)))))).
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
- (* [max1] of [RU(-a * d)] and [RU(b * -c)]. *)
  cbn [rep fst snd Generic.max Generic.shuffle02 Generic.shuffle13 Generic.swap].
  apply max_least_lane; apply mul_lane_pos; assumption.
- (* [max1] of [RU(-a * -c)] and [RU(b * d)]. *)
  cbn [rep fst snd Generic.max Generic.shuffle02 Generic.shuffle13 Generic.swap].
  apply max_least_lane; apply mul_lane_pos; assumption.
Qed.
