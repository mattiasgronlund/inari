(** * What [cancel_result] says, in terms of reals

    For nonempty bounded [X = [a, b]] and [Y = [c, d]] with
    [d - c <= b - a], an interval [z] satisfies [Y + z ⊇ X] exactly when it
    contains [[a - c, b - d]] ([superset_iff]), so the tightest such [z] is
    the tightest interval that contains [[a - c, b - d]]. For an empty [X],
    every [z] satisfies it, so the tightest is the empty interval. The
    lemmas here turn [cancel_result] into these two forms and back, for the
    proofs in [Cancel.v], and [cancel_result_empty] and [cancel_result_hull]
    show that it is what IEEE 1788 asks of an interval version of
    cancelMinus. *)

From Stdlib Require Import Reals Lra Classical.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer DecBinary AddSub DivZero ValidMake.

Open Scope R_scope.

(** [bounded], [cancel_defined] and [sum_superset] depend only on the reals
    of their sets. *)
Lemma bounded_ext :
  forall Y Y', (forall r, Y r <-> Y' r) -> bounded Y -> bounded Y'.
Proof.
intros Y Y' H [m Hm]. exists m. intros r Hr. apply Hm, H, Hr.
Qed.

Lemma defined_ext :
  forall X X' Y Y', (forall r, X r <-> X' r) -> (forall r, Y r <-> Y' r) ->
  cancel_defined X Y -> cancel_defined X' Y'.
Proof.
intros X X' Y Y' HX HY [[HE HB]|(a & b & c & d & H1 & H2 & H3 & H4 & H5)].
- left. split.
  + intros r Hr. apply (HE r), HX, Hr.
  + exact (bounded_ext Y Y' HY HB).
- right. exists a, b, c, d. split; [exact H1|]. split; [exact H2|].
  split; [exact H3|]. split.
  + intros r. split; intros Hr; [apply H4, HX, Hr|apply HX, H4, Hr].
  + intros r. split; intros Hr; [apply H5, HY, Hr|apply HY, H5, Hr].
Qed.

Lemma superset_ext :
  forall Y Y' Z X X', (forall r, X r <-> X' r) -> (forall r, Y r <-> Y' r) ->
  sum_superset Y Z X -> sum_superset Y' Z X'.
Proof.
intros Y Y' Z X X' HX HY H r Hr.
destruct (H r (proj2 (HX r) Hr)) as (s & t & Hs & Ht & E).
exists s, t. split; [apply HY, Hs|]. split; assumption.
Qed.

(** [cancel_result] depends only on the reals of [X] and [Y]. *)
Lemma cancel_result_ext :
  forall X X' Y Y' z, (forall r, X r <-> X' r) -> (forall r, Y r <-> Y' r) ->
  cancel_result X Y z -> cancel_result X' Y' z.
Proof.
intros X X' Y Y' z HX HY [Hd Hn].
assert (HX' : forall r, X' r <-> X r) by (intros r; apply iff_sym, HX).
assert (HY' : forall r, Y' r <-> Y r) by (intros r; apply iff_sym, HY).
split.
- intros D. destruct (Hd (defined_ext X' X Y' Y HX' HY' D)) as (V & S & L).
  split; [exact V|]. split.
  + exact (superset_ext Y Y' _ X X' HX HY S).
  + intros z' V' S' r Hr. exact (L z' V' (superset_ext Y' Y _ X' X HX' HY' S') r Hr).
- intros ND. apply Hn. intros D. exact (ND (defined_ext X X' Y Y' HX HY D)).
Qed.

(** The bounds of a nonempty closed interval of reals are unique. *)
Lemma endpoints_unique :
  forall a b a' b', a <= b -> (forall r, a <= r <= b <-> a' <= r <= b') ->
  a = a' /\ b = b'.
Proof.
intros a b a' b' Hab H.
(* [a] and [b] are in [[a', b']], so [a'] and [b'] are in [[a, b]]. *)
assert (Ha : a' <= a <= b') by (apply H; lra).
assert (Hb : a' <= b <= b') by (apply H; lra).
assert (Ha' : a <= a' <= b) by (apply H; lra).
assert (Hb' : a <= b' <= b) by (apply H; lra).
split; lra.
Qed.

(** For [X = [a, b]] and [Y = [c, d]] with [d - c <= b - a], [Y + z ⊇ X]
    exactly when [z] contains [[a - c, b - d]]. *)
Lemma superset_iff :
  forall X Y z a b c d, valid z -> a <= b -> c <= d -> d - c <= b - a ->
  (forall r, X r <-> a <= r <= b) -> (forall r, Y r <-> c <= r <= d) ->
  (sum_superset Y (fun t => mem t z) X <-> forall r, a - c <= r <= b - d -> mem r z).
Proof.
intros X Y z a b c d V Hab Hcd Hw HX HY. split.
- (* [a = s1 + t1] and [b = s2 + t2] with [s1] and [s2] in [[c, d]] give
     reals [t1 <= a - c] and [t2 >= b - d] of [z], and [z] contains every
     real between them. *)
  intros S r Hr.
  destruct (S a (proj2 (HX a) (conj (Rle_refl a) Hab))) as (s1 & t1 & Hs1 & Ht1 & E1).
  destruct (S b (proj2 (HX b) (conj Hab (Rle_refl b)))) as (s2 & t2 & Hs2 & Ht2 & E2).
  apply HY in Hs1. apply HY in Hs2.
  apply (mem_between z t1 t2 r V Ht1 Ht2). lra.
- (* For [r] in [[a, b]], [t = max(a - c, r - d)] is in [[a - c, b - d]]
     and [s = r - t] in [[c, d]]. *)
  intros H r Hr. apply HX in Hr.
  destruct (Rle_lt_dec (a - c) (r - d)) as [L|L].
  + exists d, (r - d). split; [apply HY; lra|]. split; [apply H; lra|]. ring.
  + exists (r - (a - c)), (a - c). split; [apply HY; lra|]. split; [apply H; lra|].
    ring.
Qed.

(** An empty [X] and a bounded [Y] give the empty interval. *)
Lemma cancel_empty :
  forall X Y, (forall r, ~ X r) -> bounded Y -> cancel_result X Y Interval.EMPTY.
Proof.
intros X Y HX HB. split.
- intros _. split; [exact EMPTY_valid|]. split.
  + intros r Hr. destruct (HX r Hr).
  + intros z' _ _ r Hr. destruct (mem_nan Interval.EMPTY r eq_refl Hr).
- intros ND. exfalso. apply ND. left. split; assumption.
Qed.

(** Where cancelMinus has no value, [Interval::ENTIRE] is the result. *)
Lemma cancel_undefined :
  forall X Y, ~ cancel_defined X Y -> cancel_result X Y Interval.ENTIRE.
Proof.
intros X Y ND. split; [intros D; destruct (ND D)|intros _; reflexivity].
Qed.

(** A closed interval of reals is bounded. *)
Lemma interval_bounded :
  forall X a b, (forall r, X r <-> a <= r <= b) -> bounded X.
Proof.
intros X a b H. exists (Rabs a + Rabs b). intros r Hr. apply H in Hr.
apply Rabs_le.
pose proof (Rle_abs b). pose proof (Rle_abs (- a)). rewrite Rabs_Ropp in *.
pose proof (Rabs_pos a). pose proof (Rabs_pos b). lra.
Qed.

(** cancelMinus(X, Y) has no value if [X] is nonempty and either [X] or [Y]
    is unbounded or [Y] is empty, or if [X] is empty and [Y] unbounded. *)
Lemma not_defined :
  forall X Y,
  ((exists r, X r) /\ (~ bounded X \/ ~ bounded Y \/ forall r, ~ Y r)) \/
  ((forall r, ~ X r) /\ ~ bounded Y) ->
  ~ cancel_defined X Y.
Proof.
intros X Y H D.
destruct D as [[HE HB]|(a & b & c & d & H1 & H2 & H3 & HX & HY)].
- destruct H as [[[r Hr] _]|[_ HnB]].
  + exact (HE r Hr).
  + exact (HnB HB).
- destruct H as [[_ [HnB|[HnB|HnY]]]|[HE _]].
  + exact (HnB (interval_bounded X a b HX)).
  + exact (HnB (interval_bounded Y c d HY)).
  + apply (HnY c), HY. lra.
  + apply (HE a), HX. lra.
Qed.

(** For [X = [a, b]] and [Y = [c, d]]: if [d - c <= b - a], the tightest
    interval that contains [[a - c, b - d]] is the result, and otherwise
    [Interval::ENTIRE] is. *)
Lemma cancel_common :
  forall X Y a b c d, a <= b -> c <= d ->
  (forall r, X r <-> a <= r <= b) -> (forall r, Y r <-> c <= r <= d) ->
  (forall z, d - c <= b - a -> is_tightest (fun r => a - c <= r <= b - d) z ->
     cancel_result X Y z) /\
  (b - a < d - c -> cancel_result X Y Interval.ENTIRE).
Proof.
intros X Y a b c d Hab Hcd HX HY. split.
- intros z Hw (V & In & L). split.
  + intros _. split; [exact V|]. split.
    * exact (proj2 (superset_iff X Y z a b c d V Hab Hcd Hw HX HY) In).
    * intros z' V' S' r Hr. apply (L z' V'); [|exact Hr].
      exact (proj1 (superset_iff X Y z' a b c d V' Hab Hcd Hw HX HY) S').
  + intros ND. exfalso. apply ND. right. exists a, b, c, d.
    split; [exact Hab|]. split; [exact Hcd|]. split; [exact Hw|].
    split; [exact HX|exact HY].
- (* Any bounds [a'], [b'], [c'], [d'] that [cancel_defined] gives are [a],
     [b], [c], [d], and [d - c <= b - a] is false. *)
  intros Hw. apply cancel_undefined. intros D.
  destruct D as [[HE _]|(a' & b' & c' & d' & H1 & H2 & H3 & HX' & HY')].
  + apply (HE a), HX. lra.
  + assert (E1 : a = a' /\ b = b').
    { apply endpoints_unique; [exact Hab|]. intros r.
      split; intros Hr; [apply HX', HX, Hr|apply HX, HX', Hr]. }
    assert (E2 : c = c' /\ d = d').
    { apply endpoints_unique; [exact Hcd|]. intros r.
      split; intros Hr; [apply HY', HY, Hr|apply HY, HY', Hr]. }
    destruct E1 as [E1 E1']. destruct E2 as [E2 E2']. lra.
Qed.

(** A [valid] interval with no reals is the empty interval. *)
Lemma no_real_empty :
  forall z, valid z -> (forall r, ~ mem r z) -> z = Interval.EMPTY.
Proof.
intros z V H. destruct (is_nan (fst (rep z))) eqn:E.
- apply MaxMin.rep_eq. rewrite (empty_nan z V E). reflexivity.
- destruct (MaxMin.lanes_ok z V E) as (_ & _ & [r Hr] & _). destruct (H r Hr).
Qed.

(** IEEE 1788's first case: an empty [X] and a bounded [Y] give the empty
    interval. *)
Theorem cancel_result_empty :
  forall X Y z, cancel_result X Y z -> (forall r, ~ X r) -> bounded Y ->
  z = Interval.EMPTY.
Proof.
intros X Y z [Hd _] HX HB.
assert (D : cancel_defined X Y) by (left; split; assumption).
destruct (Hd D) as (V & _ & L).
(* [Interval::EMPTY] satisfies [Y + z ⊇ X] for the empty [X], so [z] is
   inside it and has no reals. *)
apply no_real_empty; [exact V|].
intros r Hr.
apply (mem_nan Interval.EMPTY r eq_refl).
apply (L Interval.EMPTY EMPTY_valid); [|exact Hr].
intros t Ht. destruct (HX t Ht).
Qed.

(** IEEE 1788's second case: for [X = [a, b]] and [Y = [c, d]] with
    [d - c <= b - a], the result is the tightest interval that contains
    [[a - c, b - d]]. *)
Theorem cancel_result_hull :
  forall X Y z a b c d, cancel_result X Y z -> a <= b -> c <= d -> d - c <= b - a ->
  (forall r, X r <-> a <= r <= b) -> (forall r, Y r <-> c <= r <= d) ->
  is_tightest (fun r => a - c <= r <= b - d) z.
Proof.
intros X Y z a b c d [Hd _] Hab Hcd Hw HX HY.
assert (D : cancel_defined X Y).
{ right. exists a, b, c, d. split; [exact Hab|]. split; [exact Hcd|].
  split; [exact Hw|]. split; [exact HX|exact HY]. }
destruct (Hd D) as (V & S & L).
split; [exact V|]. split.
- exact (proj1 (superset_iff X Y z a b c d V Hab Hcd Hw HX HY) S).
- intros z' V' In r Hr. apply (L z' V'); [|exact Hr].
  exact (proj2 (superset_iff X Y z' a b c d V' Hab Hcd Hw HX HY) In).
Qed.

(** A [cancel_result] is [valid]: the tightest interval if cancelMinus has
    a value, and [Interval::ENTIRE] otherwise. *)
Lemma cancel_result_valid : forall X Y z, cancel_result X Y z -> valid z.
Proof.
intros X Y z [Hd Hn].
destruct (classic (cancel_defined X Y)) as [D|D].
- exact (proj1 (Hd D)).
- rewrite (Hn D). exact ENTIRE_valid.
Qed.
