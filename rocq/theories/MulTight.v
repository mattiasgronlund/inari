(** * The largest product of two sets of reals

    [x * y] of intervals needs the largest product [r * t] of a real [r] of
    [x] and a real [t] of [y], and the largest negation of such a product,
    in terms of the lanes of [x] and [y]. As in [tight_sum] in [AddSub.v], a
    lane holds the largest element of a set of reals, or +inf ([None]) if
    the set has no upper bound ([tight]). This file is the real analysis
    behind that; the floats come later.

    [tight (Some m) A] says that [m] is in [A] and is its largest element
    ([tight_Some]): [m <= m], so some [r] of [A] is at least [m], and every
    [r] of [A] is at most [m], as [r <= r].

    If every [t] of [B] is at least 0, and [A] and [B] each have an element
    above 0, the largest product is the product [U * V] of the largest
    elements ([tight_mult_pos_r]). [U] is above 0, as it is at least an
    element above 0, so [r * t <= U * t <= U * V] for [t >= 0], and
    [U * V] is a product. If [U] is +inf, [r * t0] for a [t0] of [B] above
    0 exceeds any [s] once [r] is large enough, and if [V] is +inf,
    [r0 * t] for an [r0] of [A] above 0 does. [tight_mult_pos_l] is the
    same with the roles of [A] and [B] swapped, as [r * t = t * r].

    If [a] and [c] are the least elements of [A] and [B], and both are at
    least 0, then [a * c <= r * t], as [a <= r] and [c <= t], so the largest
    negated product is [-(a * c)] ([tight_mult_min]).

    If [A] and [B] each have elements below and above 0, a product of reals
    of opposite signs, or with a zero, is at most 0, and so below the
    product of an [r] and a [t] that are both above 0. So the largest
    product is the larger of the largest product of reals above 0, and the
    largest product of reals below 0 ([tight_mult_mixed], with [tight_union]
    and [tight_cofinal]). The parts of [A] and [B] above 0 still have the
    largest elements [U] and [V] ([tight_pos]), so the first is [U * V], by
    [tight_mult_pos_r]. As [r * t = (-r) * (-t)], the second is the largest
    product of the negations above 0, [U' * V'], with [U'] and [V'] the
    largest negations of reals of [A] and [B].

    The products of reals of two intervals, or their negations, are the
    products of reals or negated reals of the intervals, as
    [-(r * t) = (-r) * t = r * (-t)] and [r * t = (-r) * (-t)]
    ([image2_mult_opp_l], [image2_mult_opp_r], [image2_mult_opp_lr]). *)

From Stdlib Require Import Reals Lra.
From Inari Require Import Model Ieee1788 MaxMin AddSub.

Open Scope R_scope.

(** ** Largest elements *)

(** [m] is the largest element of [A]. *)
Lemma tight_Some :
  forall m A, tight (Some m) A <-> A m /\ forall r, A r -> r <= m.
Proof.
intros m A. split.
- intros H.
  (* Every [r] of [A] is below itself, so below [m]. *)
  assert (Hmax : forall r, A r -> r <= m).
  { intros r Hr. apply (proj2 (H r)). exists r. split; [exact Hr | apply Rle_refl]. }
  split; [|exact Hmax].
  (* [m] is below [m], so below some [r] of [A], which is then [m]. *)
  destruct (proj1 (H m) (Rle_refl m)) as (r & Hr & Hmr).
  specialize (Hmax r Hr).
  replace m with r by lra. exact Hr.
- intros [Hm Hmax] s. cbn [below]. split.
  + intros Hs. exists m. split; [exact Hm | exact Hs].
  + intros (r & Hr & Hs). specialize (Hmax r Hr). lra.
Qed.

(** [A] and [B] have the same largest element if [A] is part of [B], and
    every element of [B] is at most one of [A]: then the same reals are at
    most an element of [A] and at most one of [B]. *)
Lemma tight_cofinal :
  forall o A B, (forall r, A r -> B r) -> (forall t, B t -> exists r, A r /\ t <= r) ->
  tight o A <-> tight o B.
Proof.
intros o A B HAB HBA.
assert (H : forall s, (exists r, A r /\ s <= r) <-> (exists t, B t /\ s <= t)).
{ intros s. split.
  - intros (r & Hr & Hs). exists r. split; [apply HAB, Hr | exact Hs].
  - intros (t & Ht & Hs). destruct (HBA t Ht) as (r & Hr & Htr).
    exists r. split; [exact Hr | lra]. }
split; intros HT s; rewrite (HT s).
- apply H.
- symmetry. apply H.
Qed.

(** If [A] has an element above 0, its part above 0 has the same largest
    element. *)
Lemma tight_pos :
  forall o A, tight o A -> (exists r, A r /\ 0 < r) ->
  tight o (fun r => A r /\ 0 < r).
Proof.
intros o A HA (r0 & Hr0 & Hr0p).
refine (proj2 (tight_cofinal o (fun r => A r /\ 0 < r) A _ _) HA).
- intros r [Hr _]. exact Hr.
- (* An element of [A] that is not above 0 is below [r0]. *)
  intros t Ht. destruct (Rlt_or_le 0 t) as [Htp|Htn].
  + exists t. split; [split; assumption | apply Rle_refl].
  + exists r0. split; [split; assumption | lra].
Qed.

(** The largest element of a union is the larger of the largest elements
    of the parts. *)
Lemma tight_union :
  forall o1 o2 P Q, tight o1 P -> tight o2 Q ->
  tight (umax o1 o2) (fun s => P s \/ Q s).
Proof.
intros o1 o2 P Q HP HQ s. rewrite below_umax, (HP s), (HQ s). split.
- intros [(r & Hr & Hs)|(r & Hr & Hs)]; exists r; (split; [|exact Hs]);
    [left | right]; exact Hr.
- intros (r & [Hr|Hr] & Hs); [left | right]; exists r; split; assumption.
Qed.

(** ** Largest products *)

Lemma umult_comm : forall o1 o2, umult o1 o2 = umult o2 o1.
Proof.
intros [a|] [b|]; cbn [umult]; [rewrite Rmult_comm | | |]; reflexivity.
Qed.

(** If every element of [B] is at least 0, and [A] and [B] each have an
    element above 0, the largest product of an element of [A] and one of
    [B] is the product of their largest elements. *)
Lemma tight_mult_pos_r :
  forall U V A B, tight U A -> tight V B ->
  (forall t, B t -> 0 <= t) -> (exists r, A r /\ 0 < r) -> (exists t, B t /\ 0 < t) ->
  tight (umult U V) (fun s => exists r t, A r /\ B t /\ s = r * t).
Proof.
intros [a|] [b|] A B HA HB HB0 (r0 & Hr0 & Hr0p) (t0 & Ht0 & Ht0p).
- cbn [umult]. apply (proj2 (tight_Some _ _)).
  destruct (proj1 (tight_Some _ _) HA) as [Ha Hamax].
  destruct (proj1 (tight_Some _ _) HB) as [Hb Hbmax].
  (* [a] is above 0, as [r0 <= a]. *)
  assert (Ha0 : 0 < a) by (specialize (Hamax r0 Hr0); lra).
  split.
  + exists a, b. split; [exact Ha | split; [exact Hb | reflexivity]].
  + intros s (r & t & Hr & Ht & ->).
    specialize (Hamax r Hr). specialize (Hbmax t Ht). specialize (HB0 t Ht).
    (* [r * t <= a * t] as [t >= 0], and [a * t <= a * b] as [a >= 0]. *)
    apply Rle_trans with (a * t).
    * apply Rmult_le_compat_r; assumption.
    * apply Rmult_le_compat_l; lra.
- (* [B] has no upper bound, so [r0 * t] exceeds [s] for a large [t]. *)
  intros s. cbn [umult below]. split; [intros _ | intros _; exact I].
  destruct (proj1 (HB (s / r0)) I) as (t & Ht & Hst).
  exists (r0 * t).
  split; [exists r0, t; split; [exact Hr0 | split; [exact Ht | reflexivity]] |].
  (* [s = r0 * (s / r0) <= r0 * t] as [r0 > 0]. *)
  replace s with (r0 * (s / r0)) by (field; lra).
  apply Rmult_le_compat_l; lra.
- (* [A] has no upper bound, so [r * t0] exceeds [s] for a large [r]. *)
  intros s. cbn [umult below]. split; [intros _ | intros _; exact I].
  destruct (proj1 (HA (s / t0)) I) as (r & Hr & Hsr).
  exists (r * t0).
  split; [exists r, t0; split; [exact Hr | split; [exact Ht0 | reflexivity]] |].
  (* [s = (s / t0) * t0 <= r * t0] as [t0 > 0]. *)
  replace s with (s / t0 * t0) by (field; lra).
  apply Rmult_le_compat_r; lra.
- (* The same as when only [A] has no upper bound. *)
  intros s. cbn [umult below]. split; [intros _ | intros _; exact I].
  destruct (proj1 (HA (s / t0)) I) as (r & Hr & Hsr).
  exists (r * t0).
  split; [exists r, t0; split; [exact Hr | split; [exact Ht0 | reflexivity]] |].
  replace s with (s / t0 * t0) by (field; lra).
  apply Rmult_le_compat_r; lra.
Qed.

(** The same if every element of [A] is at least 0. *)
Lemma tight_mult_pos_l :
  forall U V A B, tight U A -> tight V B ->
  (forall r, A r -> 0 <= r) -> (exists r, A r /\ 0 < r) -> (exists t, B t /\ 0 < t) ->
  tight (umult U V) (fun s => exists r t, A r /\ B t /\ s = r * t).
Proof.
intros U V A B HA HB HA0 HAp HBp.
(* [tight_mult_pos_r] with [A] and [B] swapped, as [t * r = r * t]. *)
rewrite umult_comm.
apply (tight_ext _ (fun s => exists t r, B t /\ A r /\ s = t * r)).
- intros s. split.
  + intros (t & r & Ht & Hr & ->). exists r, t.
    split; [exact Hr | split; [exact Ht | apply Rmult_comm]].
  + intros (r & t & Hr & Ht & ->). exists t, r.
    split; [exact Ht | split; [exact Hr | apply Rmult_comm]].
- exact (tight_mult_pos_r V U B A HB HA HA0 HBp HAp).
Qed.

(** If [a] and [c] are the least elements of [A] and [B], and both are at
    least 0, the largest negated product is [-(a * c)]. *)
Lemma tight_mult_min :
  forall a c A B, A a -> B c -> (forall r, A r -> a <= r) -> (forall t, B t -> c <= t) ->
  0 <= a -> 0 <= c ->
  tight (Some (- (a * c))) (fun s => exists r t, A r /\ B t /\ s = - (r * t)).
Proof.
intros a c A B Ha Hc Hamin Hcmin Ha0 Hc0. apply (proj2 (tight_Some _ _)). split.
- exists a, c. split; [exact Ha | split; [exact Hc | reflexivity]].
- intros s (r & t & Hr & Ht & ->).
  specialize (Hamin r Hr). specialize (Hcmin t Ht).
  (* [a * c <= r * t] as [0 <= a <= r] and [0 <= c <= t]. *)
  apply Ropp_le_contravar, Rmult_le_compat; assumption.
Qed.

(** If [A] and [B] each have elements below and above 0, the largest
    product is the larger of the product of the largest negations and the
    product of the largest elements. *)
Lemma tight_mult_mixed :
  forall U U' V V' A B,
  tight U A -> tight U' (fun r => A (- r)) -> tight V B -> tight V' (fun t => B (- t)) ->
  (exists r, A r /\ r < 0) -> (exists r, A r /\ 0 < r) ->
  (exists t, B t /\ t < 0) -> (exists t, B t /\ 0 < t) ->
  tight (umax (umult U' V') (umult U V)) (fun s => exists r t, A r /\ B t /\ s = r * t).
Proof.
intros U U' V V' A B HA HA' HB HB' (rn & Hrn & Hrn0) (rp & Hrp & Hrp0)
  (tn & Htn & Htn0) (tp & Htp & Htp0).
(* [-rn] and [-tn] are negations above 0 of reals of [A] and [B]. *)
assert (Hrn' : A (- - rn) /\ 0 < - rn) by (rewrite Ropp_involutive; split; [exact Hrn | lra]).
assert (Htn' : B (- - tn) /\ 0 < - tn) by (rewrite Ropp_involutive; split; [exact Htn | lra]).
(* The largest product of reals of [A] and [B] above 0 is [U * V]. *)
assert (Hpos : tight (umult U V)
  (fun s => exists r t, (A r /\ 0 < r) /\ (B t /\ 0 < t) /\ s = r * t)).
{ apply (tight_mult_pos_r U V (fun r => A r /\ 0 < r) (fun t => B t /\ 0 < t)).
  - apply tight_pos; [exact HA | exists rp; split; assumption].
  - apply tight_pos; [exact HB | exists tp; split; assumption].
  - intros t [_ Ht]. lra.
  - exists rp. split; [split; assumption | exact Hrp0].
  - exists tp. split; [split; assumption | exact Htp0]. }
(* The largest product of negations above 0 of reals of [A] and [B] is
   [U' * V']. *)
assert (Hneg : tight (umult U' V')
  (fun s => exists r t, (A (- r) /\ 0 < r) /\ (B (- t) /\ 0 < t) /\ s = r * t)).
{ apply (tight_mult_pos_r U' V' (fun r => A (- r) /\ 0 < r) (fun t => B (- t) /\ 0 < t)).
  - apply (tight_pos U' (fun r => A (- r))); [exact HA' | exists (- rn); exact Hrn'].
  - apply (tight_pos V' (fun t => B (- t))); [exact HB' | exists (- tn); exact Htn'].
  - intros t [_ Ht]. lra.
  - exists (- rn). split; [exact Hrn' | exact (proj2 Hrn')].
  - exists (- tn). split; [exact Htn' | exact (proj2 Htn')]. }
refine (proj1 (tight_cofinal _ _ _ _ _) (tight_union _ _ _ _ Hneg Hpos)); cbv beta.
- (* Both kinds of products are products of reals of [A] and [B]. *)
  intros s [(r & t & [Hr _] & [Ht _] & ->)|(r & t & [Hr _] & [Ht _] & ->)].
  + exists (- r), (- t). split; [exact Hr | split; [exact Ht | ring]].
  + exists r, t. split; [exact Hr | split; [exact Ht | reflexivity]].
- intros s (r & t & Hr & Ht & ->).
  destruct (Rlt_or_le 0 (r * t)) as [Hrt|Hrt].
  + (* A product above 0 is of reals of the same sign, both nonzero. *)
    exists (r * t). split; [|apply Rle_refl].
    destruct (Rlt_or_le 0 r) as [Hr0|Hr0].
    * assert (Ht0 : 0 < t) by nra.
      right. exists r, t. split; [split; assumption | split; [split; assumption | reflexivity]].
    * (* [r] is not 0, as [r * t] is not. *)
      assert (Hr0' : r < 0).
      { destruct (Rlt_or_le r 0) as [H|H]; [exact H|].
        replace r with 0 in Hrt by lra. lra. }
      assert (Ht0 : t < 0) by nra.
      (* [r * t = (-r) * (-t)], with [-r] and [-t] above 0. *)
      left. exists (- r), (- t). rewrite !Ropp_involutive.
      split; [split; [exact Hr | lra] | split; [split; [exact Ht | lra] | ring]].
  + (* A product at most 0 is below [rp * tp], which is above 0. *)
    assert (0 < rp * tp) by (apply Rmult_lt_0_compat; assumption).
    exists (rp * tp). split; [|lra].
    right. exists rp, tp. split; [split; assumption | split; [split; assumption | reflexivity]].
Qed.

(** ** Products with negated factors *)

(** [-(r * t) = (-r) * t], so the negated products are the products of
    the negations of the reals of [x] and the reals of [y]. *)
Lemma image2_mult_opp_l :
  forall x y s, image2 Rmult x y (- s) <->
  exists r t, mem (- r) x /\ mem t y /\ s = r * t.
Proof.
intros x y s. split.
- intros (r & t & Hr & Ht & E). exists (- r), t. rewrite Ropp_involutive.
  split; [exact Hr | split; [exact Ht | lra]].
- intros (r & t & Hr & Ht & ->). exists (- r), t.
  split; [exact Hr | split; [exact Ht | ring]].
Qed.

(** [-(r * t) = r * (-t)]. *)
Lemma image2_mult_opp_r :
  forall x y s, image2 Rmult x y (- s) <->
  exists r t, mem r x /\ mem (- t) y /\ s = r * t.
Proof.
intros x y s. split.
- intros (r & t & Hr & Ht & E). exists r, (- t). rewrite Ropp_involutive.
  split; [exact Hr | split; [exact Ht | lra]].
- intros (r & t & Hr & Ht & ->). exists r, (- t).
  split; [exact Hr | split; [exact Ht | ring]].
Qed.

(** [r * t = (-r) * (-t)]. *)
Lemma image2_mult_opp_lr :
  forall x y s, image2 Rmult x y s <->
  exists r t, mem (- r) x /\ mem (- t) y /\ s = r * t.
Proof.
intros x y s. split.
- intros (r & t & Hr & Ht & ->). exists (- r), (- t). rewrite !Ropp_involutive.
  split; [exact Hr | split; [exact Ht | ring]].
- intros (r & t & Hr & Ht & ->). exists (- r), (- t).
  split; [exact Hr | split; [exact Ht | ring]].
Qed.
