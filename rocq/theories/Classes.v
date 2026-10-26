(** * What the classes of [Interval::classify] say

    [x * y] of intervals picks the products of the bounds that give the
    bounds of the result by the classes of its arguments. This file shows
    what each class says about the lanes of a valid interval
    ([classify_lanes]), and about its reals ([classify_mem]).

    An [Interval] stores [[a, b]] as [[-a; b]], and [Interval::classify]
    packs the comparisons of both lanes with [0.0] into the code of the
    class, as the header of [Abs.v] explains. Each comparison depends only
    on the constructor of the lane and its sign bit: a zero of either sign
    is both [>= 0] and [<= 0], +inf and a finite float with sign bit 0 are
    only [>= 0], and -inf and a finite float with sign bit 1 are only
    [<= 0]. So [classify_lanes] destructs both lanes into Flocq's
    constructors, and [classify] computes the code for each combination.
    [valid] rules out -inf in the first lane, as [a] is not +inf, and in
    the second, as [b] is not -inf. Every other combination either gives
    the class in the statement or a code that is no class, for which
    [transmute_class] returns [None]: the latter are a NaN in one lane
    only, and [-a <= 0] and [b <= 0] with at least one of them strict. In
    each class other than [E], a lane is then a zero, a finite float whose
    value has the sign of its sign bit, or +inf, and a finite float with
    sign bit 0 or +inf is a [pos_lane].

    [classify_mem] reads the reals of [x] off its lanes: [r] is in [x]
    exactly when [-r] is below the first lane and [r] below the second
    ([mem_lanes]). A lane that is a float at most 0 bounds the reals of
    [x] on one side, and a positive lane is above some positive real [t],
    so [-t] or [t] is in [x] if the other lane is at least 0. That leaves
    a real of [x] in [N1] and [P1], where one lane is below 0, and [x] has
    one as it is valid and not empty ([lanes_ok]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Ieee1788 Integer Sign MaxMin AddSub.

Open Scope R_scope.

(** ** The lanes *)

(** A finite float has the sign of its sign bit. *)
Lemma pos_finite :
  forall (m : positive) (e : Z) (H : SpecFloat.bounded 53 1024 m e = true),
  pos_lane (B754_finite false m e H).
Proof.
intros m e H. right. split; [reflexivity|].
cbn [B2R]. apply F2R_gt_0. cbn [Fnum SpecFloat.cond_Zopp]. lia.
Qed.

Lemma neg_finite :
  forall (m : positive) (e : Z) (H : SpecFloat.bounded 53 1024 m e = true),
  B2R (B754_finite true m e H : f64) < 0.
Proof.
intros m e H. cbn [B2R]. apply F2R_lt_0. cbn [Fnum SpecFloat.cond_Zopp]. lia.
Qed.

(** The lanes of a valid interval [[-a; b]] by its class. *)
Lemma classify_lanes :
  forall x c, valid x -> Interval.classify x = Some c ->
  match c with
  | CE => rep x = (B754_nan, B754_nan)
  | CM => pos_lane (fst (rep x)) /\ pos_lane (snd (rep x))
  | CN0 => pos_lane (fst (rep x)) /\
           is_finite (snd (rep x)) = true /\ B2R (snd (rep x)) = 0
  | CN1 => pos_lane (fst (rep x)) /\
           is_finite (snd (rep x)) = true /\ B2R (snd (rep x)) < 0
  | CP0 => is_finite (fst (rep x)) = true /\ B2R (fst (rep x)) = 0 /\
           pos_lane (snd (rep x))
  | CP1 => is_finite (fst (rep x)) = true /\ B2R (fst (rep x)) < 0 /\
           pos_lane (snd (rep x))
  | CZ => is_finite (fst (rep x)) = true /\ B2R (fst (rep x)) = 0 /\
          is_finite (snd (rep x)) = true /\ B2R (snd (rep x)) = 0
  end.
Proof.
intros [[x0 x1]] c [[N0 N1]|(_ & Ha & Hb)] Hc; cbn [rep fst snd] in *.
- (* Both lanes NaN: the code is 0, that of [E]. *)
  destruct x0, x1; try discriminate N0; try discriminate N1.
  vm_compute in Hc. injection Hc as <-. reflexivity.
- (* With the constructor and sign bit of each lane fixed, [classify]
     computes. A code that is no class gives [None = Some c]. *)
  destruct x0 as [[]|[]| |[] m0 e0 H0], x1 as [[]|[]| |[] m1 e1 H1];
    vm_compute in Hc; try discriminate Hc; injection Hc as <-; cbv beta iota;
    first
      [ (* -inf in the first lane, i.e. [a = +inf], or in the second. *)
        exfalso; apply Ha; reflexivity
      | exfalso; apply Hb; reflexivity
      | repeat split;
        first
          [ reflexivity
          | left; reflexivity
          | apply pos_finite
          | apply neg_finite ] ].
Qed.

(** ** The reals *)

Lemma pos_lane_upper : forall w, pos_lane w -> upper_ok w.
Proof.
intros w [->|[Fw _]]; [right; reflexivity | left; exact Fw].
Qed.

(** A positive lane is above some positive real. *)
Lemma pos_lane_below :
  forall w, pos_lane w -> exists t, 0 < t /\ below (bound w) t.
Proof.
intros w [->|[Fw Hw]].
- exists 1. split; [lra | exact I].
- exists (B2R w). rewrite (bound_finite w Fw).
  split; [exact Hw | exact (Rle_refl (B2R w))].
Qed.

Lemma below_le : forall o s t, below o s -> t <= s -> below o t.
Proof.
intros [b|] s t Hs Ht; cbn [below] in *; [lra | exact I].
Qed.

(** A real [r] is in a nonempty [x] exactly when [-r] is below its first
    lane and [r] below its second. *)
Lemma mem_lanes :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  forall r,
  mem r x <-> below (bound (fst (rep x))) (- r) /\ below (bound (snd (rep x))) r.
Proof.
intros x Hx Hn r. destruct (valid_nonempty x Hx Hn) as (Ha & Hb & _).
(* The first lane holds [-a], so [-r] is below it when [r] is above [a]. *)
rewrite (mem_bounds x r Ha Hb), in_bounds_iff, (bound_lane (fst (rep x))),
  below_oopp.
reflexivity.
Qed.

(** The reals of a valid interval by its class. *)
Lemma classify_mem :
  forall x c, valid x -> Interval.classify x = Some c ->
  match c with
  | CE => forall r, ~ mem r x
  | CM => (exists r, mem r x /\ r < 0) /\ (exists r, mem r x /\ 0 < r)
  | CN0 => (forall r, mem r x -> r <= 0) /\ mem 0 x /\ (exists r, mem r x /\ r < 0)
  | CN1 => (forall r, mem r x -> r < 0) /\ (exists r, mem r x)
  | CP0 => (forall r, mem r x -> 0 <= r) /\ mem 0 x /\ (exists r, mem r x /\ 0 < r)
  | CP1 => (forall r, mem r x -> 0 < r) /\ (exists r, mem r x)
  | CZ => forall r, mem r x <-> r = 0
  end.
Proof.
intros x c Hx Hc. pose proof (classify_lanes x c Hx Hc) as Hl.
destruct c.
- intros r. exact (mem_nan x r Hl).
- destruct Hl as [P0 P1].
  pose proof (mem_lanes x Hx (not_nan_upper _ (pos_lane_upper _ P0))) as M.
  destruct (pos_lane_below _ P0) as (t0 & T0 & B0).
  destruct (pos_lane_below _ P1) as (t1 & T1 & B1).
  (* [-t0] is in [x], as [t0] is below the first lane and [-t0 < t1] below
     the second, and so is [t1], as [-t1 < t0]. *)
  split.
  + exists (- t0). split; [|lra]. apply M. split.
    * rewrite Ropp_involutive. exact B0.
    * apply (below_le _ t1); [exact B1 | lra].
  + exists t1. split; [|exact T1]. apply M. split.
    * apply (below_le _ t0); [exact B0 | lra].
    * exact B1.
- destruct Hl as (P0 & F1 & E1).
  pose proof (mem_lanes x Hx (not_nan_upper _ (pos_lane_upper _ P0))) as M.
  rewrite (bound_finite _ F1), E1 in M.
  destruct (pos_lane_below _ P0) as (t0 & T0 & B0).
  split; [|split].
  + intros r Hr. destruct (proj1 (M r) Hr) as [_ H1]. exact H1.
  + apply M. split; [apply (below_le _ t0); [exact B0 | lra]|].
    exact (Rle_refl 0).
  + exists (- t0). split; [|lra]. apply M. split.
    * rewrite Ropp_involutive. exact B0.
    * change (- t0 <= 0). lra.
- destruct Hl as (P0 & F1 & N1).
  pose proof (not_nan_upper _ (pos_lane_upper _ P0)) as Hn.
  pose proof (mem_lanes x Hx Hn) as M. rewrite (bound_finite _ F1) in M.
  destruct (lanes_ok x Hx Hn) as (_ & _ & Nx & _ & _).
  split; [|exact Nx].
  intros r Hr. destruct (proj1 (M r) Hr) as [_ H1].
  change (r <= B2R (snd (rep x))) in H1. lra.
- destruct Hl as (F0 & E0 & P1).
  pose proof (mem_lanes x Hx (not_nan_upper _ (or_introl F0))) as M.
  rewrite (bound_finite _ F0), E0 in M.
  destruct (pos_lane_below _ P1) as (t1 & T1 & B1).
  split; [|split].
  + intros r Hr. destruct (proj1 (M r) Hr) as [H0 _].
    change (- r <= 0) in H0. lra.
  + apply M. split; [change (- 0 <= 0); lra|].
    apply (below_le _ t1); [exact B1 | lra].
  + exists t1. split; [|exact T1]. apply M. split; [|exact B1].
    change (- t1 <= 0). lra.
- destruct Hl as (F0 & N0 & P1).
  pose proof (not_nan_upper _ (or_introl F0)) as Hn.
  pose proof (mem_lanes x Hx Hn) as M. rewrite (bound_finite _ F0) in M.
  destruct (lanes_ok x Hx Hn) as (_ & _ & Nx & _ & _).
  split; [|exact Nx].
  intros r Hr. destruct (proj1 (M r) Hr) as [H0 _].
  change (- r <= B2R (fst (rep x))) in H0. lra.
- destruct Hl as (F0 & E0 & F1 & E1).
  pose proof (mem_lanes x Hx (not_nan_upper _ (or_introl F0))) as M.
  rewrite (bound_finite _ F0), (bound_finite _ F1), E0, E1 in M.
  (* [r] is in [x] exactly when [-r <= 0] and [r <= 0]. *)
  intros r. rewrite M. change (- r <= 0 /\ r <= 0 <-> r = 0).
  split; [intros [H0 H1]; lra | intros ->; split; lra].
Qed.
