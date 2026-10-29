(** * The largest quotient of two sets of reals

    [x / y] and [recip x] of intervals need the largest quotient [u / q] of
    an element [u] of a set [U] of reals and an element [q] of a set [Q] of
    reals above 0 ([quot]), in terms of the lanes of [x] and [y]. Unlike a
    product of reals of two intervals, such a quotient need not have a
    largest element: [1 / [-inf, -1]] is [[-1, 0)] and [[1, 2] / [1, +inf]]
    is [(0, 2]]. So a lane holds the least upper bound of a set ([lub]),
    which [tight] in [AddSub.v] strengthens to a largest element
    ([tight_lub]), and [lane_ok T w] says that the lane [w] is the least
    float or +inf at or above that bound. [tightest_lanes_lub] is
    [tightest_lanes] of [AddSub.v] with [lub] in place of [tight].

    Three kinds of lanes occur, with [Q] a set of reals above 0:
    - (a) [U] has an element above 0 and a largest element [M], or +inf,
      and [Q] a least element [n]: the largest quotient is [M / n], or
      +inf ([quot_tight_a]).
    - (b) [U] has an element [r] above 0, and [Q] has elements as close to
      0 as asked ([den_near0]): [r / q] exceeds any real
      ([quot_unbounded]).
    - (c) [U] has a largest element [M <= 0], and [Q] a largest element
      [V], or +inf: the least upper bound is [M / V], or 0 if [Q] has no
      upper bound, which is not attained if [M < 0] ([quot_lub_c]). *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer MaxMin DecBinary AddSub MulTight.

Open Scope R_scope.

(** ** Definitions *)

(** The quotients [u / q] of an element of [U] and one of [Q]. *)
Definition quot (U Q : R -> Prop) : R -> Prop :=
  fun s => exists u q, U u /\ Q q /\ s = u / q.

(** [o] is the least upper bound of [T], or [None] if [T] has no upper
    bound: a real is below [o] exactly when it is at most every upper bound
    of [T]. *)
Definition lub (o : option R) (T : R -> Prop) : Prop :=
  forall s, below o s <-> forall m, (forall r, T r -> r <= m) -> s <= m.

(** The lane [w] is the least float or +inf at or above the least upper
    bound of [T]. *)
Definition lane_ok (T : R -> Prop) (w : f64) : Prop :=
  exists o, lub o T /\ least_lane o w.

(** An upper bound divided by [n > 0], with [None] for +inf. *)
Definition udiv (o : option R) (n : R) : option R :=
  match o with Some a => Some (a / n) | None => None end.

(** [m <= 0] divided by an upper bound [o] above 0: [m / v], or 0 if [o] is
    +inf. *)
Definition uquot (m : R) (o : option R) : option R :=
  match o with Some v => Some (m / v) | None => Some 0 end.

(** A set of numerators with an element above 0, whose largest element, or
    +inf, the lane [w] above 0 holds. *)
Definition pos_set (U : R -> Prop) (w : f64) : Prop :=
  pos_lane w /\ tight (bound w) U /\ exists r, U r /\ 0 < r.

(** A set of numerators whose largest element is the finite lane [w], at
    most 0. *)
Definition nonpos_set (U : R -> Prop) (w : f64) : Prop :=
  is_finite w = true /\ U (B2R w) /\ (forall r, U r -> r <= B2R w) /\ B2R w <= 0.

(** A set of denominators with the least element [n > 0]. *)
Definition den_min (Q : R -> Prop) (n : R) : Prop :=
  Q n /\ 0 < n /\ forall q, Q q -> n <= q.

(** A nonempty set of denominators above 0 whose largest element, or +inf,
    the lane [w] above 0 holds. *)
Definition den_sup (Q : R -> Prop) (w : f64) : Prop :=
  pos_lane w /\ tight (bound w) Q /\ (exists q, Q q) /\ forall q, Q q -> 0 < q.

(** A set of denominators above 0 with elements as close to 0 as asked. *)
Definition den_near0 (Q : R -> Prop) : Prop :=
  (forall q, Q q -> 0 < q) /\ forall eps, 0 < eps -> exists q, Q q /\ q <= eps.

(** ** Least upper bounds *)

Lemma lub_ext : forall o A B, (forall r, A r <-> B r) -> lub o A -> lub o B.
Proof.
intros o A B HAB HA s. rewrite (HA s).
split; intros H m Hm; apply H; intros r Hr; apply Hm, HAB, Hr.
Qed.

Lemma lane_ok_ext :
  forall A B w, (forall r, A r <-> B r) -> lane_ok A w -> lane_ok B w.
Proof.
intros A B w HAB (o & Ho & Hw). exists o.
split; [exact (lub_ext o A B HAB Ho) | exact Hw].
Qed.

(** A largest element is a least upper bound. *)
Lemma tight_lub : forall o A, tight o A -> lub o A.
Proof.
intros [a|] A HA s.
- apply tight_Some in HA. destruct HA as [Ha Hmax]. cbn [below]. split.
  + intros Hs m Hm. specialize (Hm a Ha). lra.
  + intros H. exact (H a Hmax).
- (* Every real is below an element of [A], so below every upper bound. *)
  cbn [below]. split; [|intros _; exact I].
  intros _ m Hm. destruct (proj1 (HA s) I) as (r & Hr & Hs).
  specialize (Hm r Hr). lra.
Qed.

(** A set with no upper bound has the least upper bound [None]. *)
Lemma lub_none :
  forall A, (forall m, exists s, A s /\ m <= s) -> lub None A.
Proof.
intros A HA s. cbn [below]. split; [|intros _; exact I].
intros _ m Hm. destruct (HA s) as (r & Hr & Hs). specialize (Hm r Hr). lra.
Qed.

(** Such a set has the lane +inf. *)
Lemma lane_ok_inf :
  forall A, (forall m, exists s, A s /\ m <= s) -> lane_ok A (B754_infinity false).
Proof.
intros A HA. exists None. split; [exact (lub_none A HA) | exact least_lane_inf].
Qed.

Lemma quot_nonempty :
  forall U Q, (exists u, U u) -> (exists q, Q q) -> exists s, quot U Q s.
Proof.
intros U Q [u Hu] [q Hq]. exists (u / q), u, q.
split; [exact Hu|]. split; [exact Hq | reflexivity].
Qed.

(** An element of [T] is below its least upper bound. *)
Lemma lub_below : forall o T r, lub o T -> T r -> below o r.
Proof.
intros o T r HL Hr. apply HL. intros m Hm. exact (Hm r Hr).
Qed.

(** The least upper bound of [T] is at most every upper bound [o'] of
    [T]. *)
Lemma lub_ule :
  forall o T o', lub o T -> (forall r, T r -> below o' r) -> ule o o'.
Proof.
intros o T [b|] HL HT s Hs; [|exact I].
exact (proj1 (HL s) Hs b HT).
Qed.

(** ** The tightest interval *)

(** [tightest_lanes_lub] for an interval [z] with the lanes [fst (rep z)]
    and [snd (rep z)]. The proof is that of [tightest_lanes] in [AddSub.v]:
    every element of [S] is below the lane of [z'] that bounds it, so the
    least upper bound is at most that lane ([lub_ule]). *)
Lemma tightest_lanes_lub_rep :
  forall S z, (exists s, S s) ->
  lane_ok (fun s => S (- s)) (fst (rep z)) -> lane_ok S (snd (rep z)) ->
  is_tightest S z.
Proof.
intros S z [s0 Hs0] (lo & Llo & U0 & Le0 & Min0) (hi & Lhi & U1 & Le1 & Min1).
pose proof (lower_ok_lane _ U0) as Ha.
(* The lower bound of [z] is [-] its first lane. *)
assert (Lo : forall s, below (bound (fst (rep z))) (- s) <->
                       above (bound (opp (fst (rep z)))) s).
{ intros s. rewrite bound_lane. apply below_oopp. }
(* Each element of [S] is between the bounds. *)
assert (Hin : forall s, S s ->
              in_bounds (bound (opp (fst (rep z)))) (bound (snd (rep z))) s).
{ intros s Hs. apply in_bounds_iff. split.
  - apply Lo, Le0. apply (lub_below _ _ _ Llo). cbv beta.
    rewrite Ropp_involutive. exact Hs.
  - apply Le1. exact (lub_below _ _ _ Lhi Hs). }
split; [exact (valid_bounds z Ha U1 (in_bounds_ordered _ _ s0 (Hin s0 Hs0)))|].
split; [intros s Hs; exact (proj2 (mem_bounds z s Ha U1) (Hin s Hs))|].
intros z' Hz' Hs r Hr.
(* [z'] is nonempty, and its lanes are upper bounds of the sets, so above
   their least upper bounds, and so above the lanes of [z]. *)
pose proof (mem_not_empty z' s0 Hz' (Hs s0 Hs0)) as Ez'.
destruct (lanes_ok z' Hz' Ez') as (U0' & U1' & _ & L0' & L1').
assert (M0 : ule (bound (fst (rep z))) (bound (fst (rep z')))).
{ apply (Min0 _ U0'). apply (lub_ule _ _ _ Llo). intros u Hu.
  pose proof (proj2 (L0' (- u)) (ex_intro _ (- u) (conj (Hs _ Hu) (Rle_refl _))))
    as H.
  rewrite Ropp_involutive in H. exact H. }
assert (M1 : ule (bound (snd (rep z))) (bound (snd (rep z')))).
{ apply (Min1 _ U1'). apply (lub_ule _ _ _ Lhi). intros u Hu.
  apply L1'. exists u. split; [exact (Hs _ Hu) | apply Rle_refl]. }
(* [r] is between two reals of [z']. *)
apply (mem_bounds z r Ha U1), in_bounds_iff in Hr. destruct Hr as [Hr0 Hr1].
apply Lo, M0, L0' in Hr0. apply M1, L1' in Hr1.
destruct Hr0 as (r1 & Hr1' & H1), Hr1 as (r2 & Hr2 & H2).
exact (mem_between z' r1 r2 r Hz' Hr1' Hr2 (conj H1 H2)).
Qed.

(** [tightest_lanes] in [AddSub.v] with least upper bounds: the first lane
    is the least float or +inf at or above the least upper bound of the
    negations of the elements of [S], and the second lane at or above that
    of [S]. *)
Lemma tightest_lanes_lub :
  forall S w0 w1, (exists s, S s) ->
  lane_ok (fun s => S (- s)) w0 -> lane_ok S w1 ->
  is_tightest S {| rep := (w0, w1) |}.
Proof.
intros S w0 w1 Hne L0 L1.
exact (tightest_lanes_lub_rep S {| rep := (w0, w1) |} Hne L0 L1).
Qed.

(** ** Largest quotients *)

(** (a): the largest quotient is [M / n] for the largest element [M] of
    [U], or +inf if [U] has no upper bound, and the least element [n] of
    [Q]. *)
Lemma quot_tight_a :
  forall Uo U Q n, tight Uo U -> (exists r, U r /\ 0 < r) -> den_min Q n ->
  tight (udiv Uo n) (quot U Q).
Proof.
intros [M|] U Q n HU (r0 & Hr0 & Hr0p) (Hn & Hnp & Hmin); cbn [udiv].
- apply tight_Some in HU. destruct HU as [HM Hmax].
  pose proof (Hmax r0 Hr0) as HMp.
  apply tight_Some.
  split; [exists M, n; split; [exact HM | split; [exact Hn | reflexivity]]|].
  intros s (u & q & Hu & Hq & ->).
  pose proof (Hmin q Hq) as Hnq.
  (* [u / q <= M / q <= M / n], as [u <= M], [0 < n <= q] and [0 < M]. *)
  assert (Hinv : / q <= / n) by (apply Rinv_le_contravar; [exact Hnp | exact Hnq]).
  assert (Pq : 0 <= / q) by (apply Rlt_le, Rinv_0_lt_compat; lra).
  unfold Rdiv. apply Rle_trans with (M * / q).
  + apply Rmult_le_compat_r; [exact Pq | exact (Hmax u Hu)].
  + apply Rmult_le_compat_l; [lra | exact Hinv].
- intros s. cbn [below]. split; [intros _ | intros _; exact I].
  (* An element of [U] at or above [s * n], divided by [n]. *)
  destruct (proj1 (HU (s * n)) I) as (u & Hu & Hsu).
  exists (u / n).
  split; [exists u, n; split; [exact Hu | split; [exact Hn | reflexivity]]|].
  replace s with (s * n / n) by (field; lra).
  unfold Rdiv.
  apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; exact Hnp | exact Hsu].
Qed.

(** (b): the quotients have no upper bound. *)
Lemma quot_unbounded :
  forall U Q, (exists r, U r /\ 0 < r) -> den_near0 Q ->
  forall m, exists s, quot U Q s /\ m <= s.
Proof.
intros U Q (r & Hr & Hrp) (Hpos & Hnear) m.
(* A [q] of [Q] at most [r / (|m| + 1)] gives [r / q >= |m| + 1 > m]. *)
assert (Ha : 0 < Rabs m + 1) by (pose proof (Rabs_pos m); lra).
assert (He : 0 < r / (Rabs m + 1)).
{ unfold Rdiv. apply Rmult_lt_0_compat; [exact Hrp | apply Rinv_0_lt_compat; exact Ha]. }
destruct (Hnear _ He) as (q & Hq & Hqe).
pose proof (Hpos q Hq) as Hqp.
exists (r / q). split; [exists r, q; split; [exact Hr | split; [exact Hq | reflexivity]]|].
assert (Hinv : / (r / (Rabs m + 1)) <= / q).
{ apply Rinv_le_contravar; [exact Hqp | exact Hqe]. }
assert (E : r * / (r / (Rabs m + 1)) = Rabs m + 1) by (field; lra).
assert (L : r * / (r / (Rabs m + 1)) <= r * / q).
{ apply Rmult_le_compat_l; [lra | exact Hinv]. }
pose proof (Rle_abs m). unfold Rdiv. lra.
Qed.

(** (c): the least upper bound is [M / V] for the largest element [M <= 0]
    of [U] and the largest element [V] of [Q], or 0 if [Q] has no upper
    bound. *)
Lemma quot_lub_c :
  forall U Q M Vo, U M -> (forall r, U r -> r <= M) -> M <= 0 ->
  tight Vo Q -> (exists q, Q q) -> (forall q, Q q -> 0 < q) ->
  lub (uquot M Vo) (quot U Q).
Proof.
intros U Q M [V|] HM Hmax HM0 HQ _ Hpos; cbn [uquot].
- (* [M / V] is the largest quotient: [u / q <= M / q <= M / V], as
     [u <= M <= 0] and [0 < q <= V]. *)
  apply tight_Some in HQ. destruct HQ as [HV HVmax].
  apply tight_lub, tight_Some.
  split; [exists M, V; split; [exact HM | split; [exact HV | reflexivity]]|].
  intros s (u & q & Hu & Hq & ->).
  pose proof (Hpos q Hq) as Hqp.
  assert (Hinv : / V <= / q) by (apply Rinv_le_contravar; [exact Hqp | exact (HVmax q Hq)]).
  assert (Pq : 0 <= / q) by (apply Rlt_le, Rinv_0_lt_compat; exact Hqp).
  unfold Rdiv. apply Rle_trans with (M * / q).
  + apply Rmult_le_compat_r; [exact Pq | exact (Hmax u Hu)].
  + apply Rmult_le_compat_neg_l; [exact HM0 | exact Hinv].
- (* The quotients are at most 0, and [M / q] exceeds every [m < 0] once
     [q > M / m]. *)
  intros s. cbn [below]. split.
  + intros Hs m Hm. destruct (Rle_or_lt 0 m) as [Hm0|Hm0]; [lra|]. exfalso.
    destruct (proj1 (HQ (M / m + 1)) I) as (q & Hq & Hmq).
    pose proof (Hpos q Hq) as Hqp.
    assert (Hq' : quot U Q (M / q)).
    { exists M, q. split; [exact HM | split; [exact Hq | reflexivity]]. }
    specialize (Hm _ Hq').
    (* [M <= m * q <= m * (M / m + 1) = M + m < M]. *)
    assert (H1 : m * q <= m * (M / m + 1)) by (apply Rmult_le_compat_neg_l; lra).
    assert (E1 : m * (M / m + 1) = M + m) by (field; lra).
    assert (E2 : M / q * q = M) by (field; lra).
    assert (H2 : M / q * q <= m * q) by (apply Rmult_le_compat_r; lra).
    lra.
  + intros H. apply H. intros r (u & q & Hu & Hq & ->).
    pose proof (Hpos q Hq) as Hqp. pose proof (Hmax u Hu).
    assert (Pq : 0 <= / q) by (apply Rlt_le, Rinv_0_lt_compat; exact Hqp).
    pose proof (Rmult_le_compat_r (/ q) u 0 Pq ltac:(lra)) as Hle.
    rewrite Rmult_0_l in Hle. exact Hle.
Qed.
