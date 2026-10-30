(** * The base of [Interval::pow]

    [Interval::pow] first intersects its base [self] with
    [DOM = [0, +inf]], which is [dom_nonneg] of [Interior.v]. This file
    shows that the image of the box under [pow] is that of the box with
    the intersection [x] as its base ([pw_image_inter]), and that the lower
    bound of a nonempty [x] is +0 or a float above 0, never -0 ([pw_xok]),
    as [min1] of two zeros in [Model.v] is -0, so that the lower lane of [x]
    is -0 whenever [self] has a real at or below 0. It also says when the
    decorations that [Interval::pow] picks hold: [interior(DOM)] tests that
    every real of [self] is above 0, and [subset(DOM)] that none is
    below 0. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Integer Sign MaxMin AddSub
  ValidSetOp Interior.

Open Scope R_scope.

(** A nonempty [valid] interval whose lower bound is a finite float at or
    above 0, and +0 if it is 0. *)
Definition pw_xok (x : Interval) : Prop :=
  valid x /\ Interval.is_empty x = false /\
  is_finite (Interval.inf_raw x) = true /\ 0 <= B2R (Interval.inf_raw x) /\
  (B2R (Interval.inf_raw x) = 0 -> Interval.inf_raw x = B754_zero false).

Lemma pw_inter_valid :
  forall self, valid self -> valid (Interval.intersection self dom_nonneg).
Proof.
intros self Hs. exact (intersection_valid self dom_nonneg Hs dom_nonneg_valid).
Qed.

Lemma pw_inter_mem :
  forall self r, valid self ->
  mem r (Interval.intersection self dom_nonneg) <-> mem r self /\ 0 <= r.
Proof.
intros self r Hs.
rewrite (intersection_mem self dom_nonneg r Hs dom_nonneg_valid), dom_nonneg_mem.
reflexivity.
Qed.

(** A lower bound that is +0 or a finite float above 0 has the form that
    [pw_xok] asks. *)
Lemma pc_lane_pos :
  forall c : f64, c = B754_zero false \/ (is_finite c = true /\ 0 < B2R c) ->
  is_finite c = true /\ 0 <= B2R c /\ (B2R c = 0 -> c = B754_zero false).
Proof.
intros c [->|(Fc & Pc)].
- split; [reflexivity|]. cbn [B2R]. split; [lra | intros _; reflexivity].
- split; [exact Fc|]. split; [lra | intros H; lra].
Qed.

(** The lower lane of the intersection is [min1] of that of [self], whose
    negation is a finite float or -inf, and that of [dom_nonneg], -0. A zero
    gives -0 ([min1] of two zeros has the sign bits of both or-ed), as does
    a float above 0 or +inf; a float below 0 is kept. The negation is then
    +0 or a float above 0. *)
Lemma pc_min1_lane :
  forall a, lower_ok (opp a) ->
  is_finite (opp (Generic.min1 a (B754_zero true))) = true /\
  0 <= B2R (opp (Generic.min1 a (B754_zero true))) /\
  (B2R (opp (Generic.min1 a (B754_zero true))) = 0 ->
   opp (Generic.min1 a (B754_zero true)) = B754_zero false).
Proof.
intros a Ha. apply pc_lane_pos.
destruct a as [[|]|[|]| |[|] ma ea Hea].
- left. vm_compute. reflexivity.
- left. vm_compute. reflexivity.
- destruct Ha as [H|H]; discriminate H.
- left. vm_compute. reflexivity.
- destruct Ha as [H|H]; discriminate H.
- right. change (opp (Generic.min1 (B754_finite true ma ea Hea) (B754_zero true)))
    with (B754_finite false ma ea Hea : f64).
  split; [reflexivity|]. cbn [B2R]. apply F2R_gt_0. cbn. lia.
- left. reflexivity.
Qed.

Lemma pw_xok_inter :
  forall self, valid self ->
  Interval.is_empty (Interval.intersection self dom_nonneg) = false ->
  pw_xok (Interval.intersection self dom_nonneg).
Proof.
intros self Hs Hne. unfold pw_xok.
split; [exact (pw_inter_valid self Hs)|]. split; [exact Hne|].
(* [self] is not empty, and the intersection is not empty either, so its
   lanes are [min1] of those of [self] and [dom_nonneg]. *)
assert (N : is_nan (fst (rep self)) = false /\
            fst (rep (Interval.intersection self dom_nonneg)) =
            Generic.min1 (fst (rep self)) (B754_zero true)).
{ revert Hne. unfold Interval.intersection, Interval.either_empty, Interval.is_empty.
  change (is_nan (fst (rep dom_nonneg))) with false.
  destruct (is_nan (fst (rep self))) eqn:N; cbn [orb].
  - intros H. cbn in H. discriminate H.
  - match goal with |- context [if ?c then _ else _] => destruct c end.
    + intros H. cbn in H. discriminate H.
    + intros _. split; reflexivity. }
destruct N as (N & E).
unfold Interval.inf_raw. rewrite E.
exact (pc_min1_lane _ (proj1 (valid_nonempty self Hs N))).
Qed.

Lemma pw_image_inter :
  forall self y s, valid self ->
  image2_set pow_dom Rpow self y s <->
  image2_set pow_dom Rpow (Interval.intersection self dom_nonneg) y s.
Proof.
intros self y s Hs. unfold image2_set. split.
- intros (r & t & Hr & Ht & Hd & ->). exists r, t.
  split; [|split; [exact Ht | split; [exact Hd | reflexivity]]].
  apply (pw_inter_mem self r Hs). split; [exact Hr|].
  destruct Hd as [Hd|[Hd _]]; lra.
- intros (r & t & Hr & Ht & Hd & ->). exists r, t.
  split; [exact (proj1 (proj1 (pw_inter_mem self r Hs) Hr))|].
  split; [exact Ht | split; [exact Hd | reflexivity]].
Qed.

Lemma pw_interior :
  forall self, valid self ->
  Interval.interior self dom_nonneg = true <-> forall r, mem r self -> 0 < r.
Proof.
intros self Hs. rewrite (interior_mem self dom_nonneg Hs dom_nonneg_valid). split.
- (* [r - eps / 2] is in [dom_nonneg], so [r] is above 0. *)
  intros H r Hr. destruct (H r Hr) as (e & He & Ht).
  assert (Hd : Rabs (r - e / 2 - r) < e).
  { replace (r - e / 2 - r) with (- (e / 2)) by ring.
    rewrite Rabs_Ropp, Rabs_pos_eq by lra. lra. }
  apply Ht, dom_nonneg_mem in Hd. lra.
- (* A real [r] above 0 has the neighbourhood of radius [r]. *)
  intros H r Hr. exists r. split; [exact (H r Hr)|].
  intros t Ht. apply dom_nonneg_mem. apply Rabs_def2 in Ht. lra.
Qed.

Lemma pw_subset :
  forall self, valid self ->
  Interval.subset self dom_nonneg = true <-> forall r, mem r self -> 0 <= r.
Proof.
intros self Hs. rewrite (subset_mem self dom_nonneg Hs dom_nonneg_valid).
split; intros H r Hr.
- exact (proj1 (dom_nonneg_mem r) (H r Hr)).
- exact (proj2 (dom_nonneg_mem r) (H r Hr)).
Qed.
