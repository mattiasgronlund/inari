(** * Two-output division with two components

    If [y = [a, b]] is in [N1] or [P1] and [x = [c, d]] in [M], i.e.
    [b < 0] or [0 < a], and [c < 0 < d], [mul_rev x y] has two components,
    on either side of 0. [x = [c, d]] is stored as [[-c; d]] and
    [y = [a, b]] as [[-a; b]].

    - [N1 × M]: the reals [z < 0] come from [t > 0], and are
      [k1 = quot (Up y) (Qp x)], i.e. [(-inf, b / d]], or [(-inf, 0)] if
      [d = +inf]; the reals [z > 0] come from [t < 0], and are
      [k2 = quot (Um y) (Qn x)], i.e. [[b / c, +inf)], or [(0, +inf)] if
      [c = -inf]. [Interval::mul_rev_to_pair] returns
      [[+inf; RU(b / d)]] and [[RU(b / (-c)); +inf]].
    - [P1 × M]: [k1 = quot (Um y) (Qn x)], i.e. [(-inf, a / c]], or
      [(-inf, 0)] if [c = -inf], and [k2 = quot (Up y) (Qp x)], i.e.
      [[a / d, +inf)], or [(0, +inf)] if [d = +inf], and it returns
      [[+inf; RU((-a) / (-c))]] and [[RU((-a) / d); +inf]].

    Each lane is one of the forms of [DivLane.v]: +inf by [div_lane_inf],
    as the numerators there, [Um y] for [N1] and [Up y] for [P1], are above
    0, and the denominators of an [x] in [M] come as close to 0 as asked
    ([yset_M]), and the others by [div_lane_nonpos], with the largest
    numerator, [b] for [N1] or [-a] for [P1], at most 0 and in a lane of
    [y], and the largest denominator, [d] or [-c] (or +inf), in a lane of
    [x]. *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer Sign MaxMin DecBinary AddSub
  Classify2 Classes MulTight DivRu DivTight DivLane DivSets MulRevSets.

Open Scope R_scope.

(** The denominators of an [x] in [M]: those above 0 come as close to 0 as
    asked and have the largest element [d], or +inf, in the second lane, and
    the negations of those below 0 the same with [-c] in the first lane. *)
Lemma yset_M :
  forall x, valid x -> Interval.classify x = Some CM ->
  den_near0 (Qp x) /\ den_sup (Qp x) (snd (rep x)) /\
  den_near0 (Qn x) /\ den_sup (Qn x) (fst (rep x)).
Proof.
intros x Hx Cx.
pose proof (classify_lanes x _ Hx Cx) as L.
pose proof (classify_mem x _ Hx Cx) as M. cbv beta iota in L, M.
destruct L as (P0 & P1), M as ((r1 & Hr1 & Hr1n) & (r0 & Hr0 & Hr0p)).
destruct (lanes_tight x Hx (not_nan_upper _ (pos_lane_upper _ P0)))
  as (_ & _ & _ & T0 & T1).
assert (Hr1' : mem (- - r1) x /\ 0 < - r1).
{ rewrite Ropp_involutive. split; [exact Hr1 | lra]. }
split; [|split; [|split]].
- split; [intros q [_ Hq]; exact Hq|].
  (* [min(eps, r0)] is above 0 and at most [r0], so it is in [x] with
     [r1 < 0] and [r0]. *)
  intros eps Heps. exists (Rmin eps r0).
  pose proof (Rmin_l eps r0) as Ml. pose proof (Rmin_r eps r0) as Mr.
  assert (Hm : 0 < Rmin eps r0) by (apply Rmin_glb_lt; lra).
  split; [|exact Ml]. split; [|exact Hm].
  apply (mem_between x r1 r0); [exact Hx | exact Hr1 | exact Hr0 | split; lra].
- split; [exact P1|]. split.
  + exact (tight_pos _ _ T1 (ex_intro _ r0 (conj Hr0 Hr0p))).
  + split; [exists r0; split; [exact Hr0 | exact Hr0p]|].
    intros q [_ Hq]. exact Hq.
- split; [intros q [_ Hq]; exact Hq|].
  (* [-min(eps, -r1)] is below 0 and at least [r1], so it is in [x] with
     [r1] and [r0 > 0]. *)
  intros eps Heps. exists (Rmin eps (- r1)).
  pose proof (Rmin_l eps (- r1)) as Ml. pose proof (Rmin_r eps (- r1)) as Mr.
  assert (Hm : 0 < Rmin eps (- r1)) by (apply Rmin_glb_lt; lra).
  split; [|exact Ml]. split; [|exact Hm].
  apply (mem_between x r1 r0); [exact Hx | exact Hr1 | exact Hr0 | split; lra].
- split; [exact P0|]. split.
  + exact (tight_pos _ _ T0 (ex_intro _ (- r1) Hr1')).
  + split; [exists (- r1); exact Hr1'|].
    intros q [_ Hq]. exact Hq.
Qed.

(** [mul_rev_to_pair] for [N1 × M] divides [[b; b]] by [[-c; d]]. *)
Lemma mul_rev_N1M_eq :
  forall has_fma x y,
  Interval.classify x = Some CM -> Interval.classify y = Some CN1 ->
  Interval.mul_rev_to_pair has_fma x y =
  Some ({| rep := (B754_infinity false, Bdiv mode_UP (snd (rep y)) (snd (rep x))) |},
        {| rep := (Bdiv mode_UP (snd (rep y)) (fst (rep x)), B754_infinity false) |}).
Proof.
intros has_fma x y Cx Cy. unfold Interval.mul_rev_to_pair.
rewrite (classify2_pair _ _ _ _ Cy Cx); cbv beta iota zeta.
rewrite div_ru_correct, infinity_eq. reflexivity.
Qed.

(** [mul_rev_to_pair] for [P1 × M] divides [[-a; -a]] by [[-c; d]]. *)
Lemma mul_rev_P1M_eq :
  forall has_fma x y,
  Interval.classify x = Some CM -> Interval.classify y = Some CP1 ->
  Interval.mul_rev_to_pair has_fma x y =
  Some ({| rep := (B754_infinity false, Bdiv mode_UP (fst (rep y)) (fst (rep x))) |},
        {| rep := (Bdiv mode_UP (fst (rep y)) (snd (rep x)), B754_infinity false) |}).
Proof.
intros has_fma x y Cx Cy. unfold Interval.mul_rev_to_pair.
rewrite (classify2_pair _ _ _ _ Cy Cx); cbv beta iota zeta.
rewrite div_ru_correct, infinity_eq. reflexivity.
Qed.

Lemma mul_rev_N1M :
  forall has_fma x y, valid x -> valid y ->
  Interval.classify x = Some CM -> Interval.classify y = Some CN1 ->
  exists u v, Interval.mul_rev_to_pair has_fma x y = Some (u, v) /\
    two_output (mul_rev x y) u v.
Proof.
intros has_fma x y Hx Hy Cx Cy.
rewrite (mul_rev_N1M_eq has_fma x y Cx Cy).
eexists _, _. split; [reflexivity|].
pose proof (classify_mem y _ Hy Cy) as My. cbv beta iota in My.
destruct My as (Neg & r & Hr).
destruct (xset_N y Hy (or_intror Cy)) as (NUp & (_ & _ & PUm)).
destruct (yset_M x Hx Cx) as (Np & Sp & Nn & Sn).
(* The quotients by [Qp x] and [Qn x] are nonempty, as [y] is, and so are
   [Qp x] and [Qn x] by [den_sup]. *)
assert (E1 : exists s, quot (Up y) (Qp x) s).
{ apply quot_nonempty; [exists r; exact Hr | exact (proj1 (proj2 (proj2 Sp)))]. }
assert (E2 : exists s, quot (Um y) (Qn x) s).
{ apply quot_nonempty; [|exact (proj1 (proj2 (proj2 Sn)))].
  exists (- r). unfold Um. rewrite Ropp_involutive. exact Hr. }
apply (two_output_two _ (quot (Up y) (Qp x)) (quot (Um y) (Qn x)) 0).
- (* [t = 0] gives nothing, as 0 is not in [y]. *)
  intros s. rewrite mul_rev_split. split.
  + intros [[_ H0]|H]; [pose proof (Neg 0 H0); lra | exact H].
  + intros H. right. exact H.
- exact E1.
- exact E2.
- apply quot_convex; [exact (Up_convex y Hy) | exact (Qp_convex x Hx)|].
  intros q [_ Hq]. exact Hq.
- apply quot_convex; [exact (Um_convex y Hy) | exact (Qn_convex x Hx)|].
  intros q [_ Hq]. exact Hq.
- apply mul_rev_no0. intros H0. pose proof (Neg 0 H0). lra.
- intros s. apply quot_neg; [exact Neg | intros q [_ Hq]; exact Hq].
- intros s. apply quot_pos; [|intros q [_ Hq]; exact Hq].
  intros u Hu. pose proof (Neg _ Hu). lra.
- (* The negations of [k1] are [quot (Um y) (Qp x)], which has no upper
     bound as [Qp x] comes as close to 0 as asked, and the largest element
     of [k1] is [b / d], or 0 if [d = +inf]. *)
  apply tightest_lanes_lub; [exact E1| |].
  + apply (lane_ok_ext (quot (Um y) (Qp x))).
    * intros s. symmetry. apply quot_Up_opp.
    * exact (div_lane_inf _ _ PUm Np).
  + exact (div_lane_nonpos _ _ _ _ NUp Sp).
- (* The negations of [k2] are [quot (Up y) (Qn x)], with the largest
     element [b / (-c)], or 0 if [c = -inf], and [k2] has no upper bound
     as [Qn x] comes as close to 0 as asked. *)
  apply tightest_lanes_lub; [exact E2| |].
  + apply (lane_ok_ext (quot (Up y) (Qn x))).
    * intros s. symmetry. apply quot_Um_opp.
    * exact (div_lane_nonpos _ _ _ _ NUp Sn).
  + exact (div_lane_inf _ _ PUm Nn).
Qed.

Lemma mul_rev_P1M :
  forall has_fma x y, valid x -> valid y ->
  Interval.classify x = Some CM -> Interval.classify y = Some CP1 ->
  exists u v, Interval.mul_rev_to_pair has_fma x y = Some (u, v) /\
    two_output (mul_rev x y) u v.
Proof.
intros has_fma x y Hx Hy Cx Cy.
rewrite (mul_rev_P1M_eq has_fma x y Cx Cy).
eexists _, _. split; [reflexivity|].
pose proof (classify_mem y _ Hy Cy) as My. cbv beta iota in My.
destruct My as (Pos & r & Hr).
destruct (xset_P y Hy (or_intror Cy)) as ((_ & _ & PUp) & NUm).
destruct (yset_M x Hx Cx) as (Np & Sp & Nn & Sn).
assert (E1 : exists s, quot (Um y) (Qn x) s).
{ apply quot_nonempty; [|exact (proj1 (proj2 (proj2 Sn)))].
  exists (- r). unfold Um. rewrite Ropp_involutive. exact Hr. }
assert (E2 : exists s, quot (Up y) (Qp x) s).
{ apply quot_nonempty; [exists r; exact Hr | exact (proj1 (proj2 (proj2 Sp)))]. }
apply (two_output_two _ (quot (Um y) (Qn x)) (quot (Up y) (Qp x)) 0).
- (* [t = 0] gives nothing, as 0 is not in [y]. *)
  intros s. rewrite mul_rev_split. split.
  + intros [[_ H0]|[H|H]]; [pose proof (Pos 0 H0); lra | right; exact H | left; exact H].
  + intros [H|H]; right; [right | left]; exact H.
- exact E1.
- exact E2.
- apply quot_convex; [exact (Um_convex y Hy) | exact (Qn_convex x Hx)|].
  intros q [_ Hq]. exact Hq.
- apply quot_convex; [exact (Up_convex y Hy) | exact (Qp_convex x Hx)|].
  intros q [_ Hq]. exact Hq.
- apply mul_rev_no0. intros H0. pose proof (Pos 0 H0). lra.
- intros s. apply quot_neg; [|intros q [_ Hq]; exact Hq].
  intros u Hu. pose proof (Pos _ Hu). lra.
- intros s. apply quot_pos; [exact Pos | intros q [_ Hq]; exact Hq].
- (* The negations of [k1] are [quot (Up y) (Qn x)], which has no upper
     bound as [Qn x] comes as close to 0 as asked, and the largest element
     of [k1] is [(-a) / (-c)], or 0 if [c = -inf]. *)
  apply tightest_lanes_lub; [exact E1| |].
  + apply (lane_ok_ext (quot (Up y) (Qn x))).
    * intros s. symmetry. apply quot_Um_opp.
    * exact (div_lane_inf _ _ PUp Nn).
  + exact (div_lane_nonpos _ _ _ _ NUm Sn).
- (* The negations of [k2] are [quot (Um y) (Qp x)], with the largest
     element [(-a) / d], or 0 if [d = +inf], and [k2] has no upper bound
     as [Qp x] comes as close to 0 as asked. *)
  apply tightest_lanes_lub; [exact E2| |].
  + apply (lane_ok_ext (quot (Um y) (Qp x))).
    * intros s. symmetry. apply quot_Up_opp.
    * exact (div_lane_nonpos _ _ _ _ NUm Sp).
  + exact (div_lane_inf _ _ PUp Np).
Qed.
