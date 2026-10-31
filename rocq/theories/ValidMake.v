(** * The constructors make [valid] intervals

    Each place that makes an [Interval] other than by an operation, and
    each place that makes a [DecInterval], gives a [valid] interval:
    [Interval::EMPTY], [const_interval!] (and so [Interval::ENTIRE] and the
    other constants), [Interval::zero], [TryFrom<(f64, f64)>],
    [try_from_be_bytes] and its siblings, [try_from_ninterval_exact], and
    for [DecInterval], [new], [set_dec], the constants, [def_com!],
    [const_dec_interval!], [TryFrom<(f64, f64)>], [try_from_be_bytes] and
    its siblings, and [From<DecNInterval>]. [Valid.v] puts them together
    with the operations. *)

From Stdlib Require Import ZArith.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Inari Require Import Model Integer.

(** ** [Interval] *)

(** Bounds [a] and [b] that pass the test of [TryFrom<(f64, f64)>],
    stored as [[-a; b]], make a [valid] interval. *)
Lemma opp_pair_valid :
  forall a b,
  le a b = true -> eq a (B754_infinity false) = false ->
  eq b (B754_infinity true) = false ->
  valid {| rep := (opp a, b) |}.
Proof.
intros a b Hab Ha Hb. unfold valid. cbn [rep]. right.
(* The first lane holds [-a], so [valid] speaks of [-(-a)], i.e. [a]. *)
unfold opp. rewrite (Bopp_involutive _ _ a).
split; [exact Hab|]. split.
- intros ->. discriminate Ha.
- intros ->. discriminate Hb.
Qed.

Theorem EMPTY_valid : valid Interval.EMPTY.
Proof.
unfold valid, Interval.EMPTY. cbn [rep]. left. split; reflexivity.
Qed.

(** [const_interval!(a, b)], for [a] and [b] that pass its assertion. *)
Theorem const_interval_valid :
  forall a b, Interval.const_interval_ok a b = true ->
  valid (Interval.const_interval a b).
Proof.
intros a b H. unfold Interval.const_interval_ok in H.
rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in H.
destruct H as [[Hab Ha] Hb].
exact (opp_pair_valid a b Hab Ha Hb).
Qed.

Theorem ENTIRE_valid : valid Interval.ENTIRE.
Proof.
apply const_interval_valid. reflexivity.
Qed.

Theorem zero_valid : valid Interval.zero.
Proof.
(* [[+0; +0]] is [[-0, +0]], and [-0 <= +0]. *)
unfold valid, Interval.zero. cbn [rep Generic.splat]. right.
split; [reflexivity|]. split; discriminate.
Qed.

(** [with_infsup_raw(a, b)], for [a] and [b] that [TryFrom<(f64, f64)>]
    accepts. *)
Theorem with_infsup_raw_valid :
  forall a b,
  le a b = true -> eq a (B754_infinity false) = false ->
  eq b (B754_infinity true) = false ->
  valid (Interval.with_infsup_raw a b).
Proof.
intros a b Hab Ha Hb. unfold Interval.with_infsup_raw, Generic.constant.
exact (opp_pair_valid a b Hab Ha Hb).
Qed.

Theorem try_from_valid :
  forall a b x, Interval.try_from a b = Some x -> valid x.
Proof.
intros a b x H. unfold Interval.try_from in H.
match type of H with
| (if ?g then _ else _) = _ => destruct g eqn:G; [|discriminate]
end.
injection H as <-.
rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in G.
destruct G as [[Hab Ha] Hb].
exact (with_infsup_raw_valid a b Hab Ha Hb).
Qed.

Theorem try_from_bytes_valid :
  forall a b x, Interval.try_from_bytes a b = Some x -> valid x.
Proof.
intros a b x H. unfold Interval.try_from_bytes in H.
match type of H with
| (if ?g then _ else _) = _ => destruct g eqn:G
end.
- (* The first three conjuncts are the test of [TryFrom<(f64, f64)>];
     the signs of zero bounds do not matter for [valid]. *)
  injection H as <-. rewrite !Bool.andb_true_iff in G.
  destruct G as [[[[Hab Ha] Hb] _] _].
  rewrite Bool.negb_true_iff in Ha, Hb.
  exact (with_infsup_raw_valid a b Hab Ha Hb).
- destruct (eq a (B754_infinity false) && eq b (B754_infinity true));
    [|discriminate].
  injection H as <-. exact EMPTY_valid.
Qed.

Theorem try_from_ninterval_exact_valid :
  forall m x y, Interval.try_from_ninterval_exact m x = Some y -> valid y.
Proof.
intros m x y H. unfold Interval.try_from_ninterval_exact in H.
cbv zeta in H.
destruct (f64_inexact (number_to_f64 m (ninf x) Inf) ||
          f64_inexact (number_to_f64 m (nsup x) Sup)); [discriminate|].
injection H as <-.
set (a := f64_f (number_to_f64 m (ninf x) Inf)).
set (b := f64_f (number_to_f64 m (nsup x) Sup)).
destruct (Interval.try_from a b) as [z|] eqn:E.
- exact (try_from_valid a b z E).
- exact EMPTY_valid.
Qed.

(** ** [DecInterval] *)

Theorem new_valid : forall x, valid x -> valid (itv (DecInterval.new x)).
Proof.
intros x Hx. unfold DecInterval.new. cbn [itv DecInterval.new_unchecked].
exact Hx.
Qed.

Theorem set_dec_valid :
  forall x d, valid x -> valid (itv (DecInterval.set_dec x d)).
Proof.
intros x d Hx. unfold DecInterval.set_dec.
(* [NAI] and [EMPTY] hold [Interval::EMPTY], and the other branches
   hold [x]. *)
destruct (dec_eqb d Ill); [exact EMPTY_valid|].
destruct (Interval.is_empty x); [exact EMPTY_valid|].
destruct (dec_eqb d Com && negb (Interval.is_common_interval x));
  cbn [itv DecInterval.new_unchecked]; exact Hx.
Qed.

Theorem dec_constants_valid :
  valid (itv DecInterval.EMPTY) /\ valid (itv DecInterval.NAI) /\
  valid (itv DecInterval.ENTIRE).
Proof.
split; [exact EMPTY_valid|]. split; [exact EMPTY_valid|].
exact ENTIRE_valid.
Qed.

Theorem def_com_valid :
  forall a b, Interval.const_interval_ok a b = true ->
  valid (itv (DecInterval.def_com a b)).
Proof.
intros a b H. exact (const_interval_valid a b H).
Qed.

Theorem const_dec_interval_valid :
  forall a b, Interval.const_interval_ok a b = true ->
  valid (itv (DecInterval.const_dec_interval a b)).
Proof.
intros a b H. exact (const_interval_valid a b H).
Qed.

Theorem dec_try_from_valid :
  forall a b z, DecInterval.try_from a b = Some z -> valid (itv z).
Proof.
intros a b z H. unfold DecInterval.try_from in H.
destruct (Interval.try_from a b) as [x|] eqn:E; [|discriminate].
injection H as <-. exact (new_valid x (try_from_valid a b x E)).
Qed.

Theorem dec_try_from_bytes_valid :
  forall a b c z, DecInterval.try_from_bytes a b c = Some z -> valid (itv z).
Proof.
intros a b c z H. unfold DecInterval.try_from_bytes in H.
match type of H with
| match ?o with Some _ => _ | None => _ end = _ =>
    destruct o as [d|]; [|discriminate]
end.
cbv beta iota in H.
match type of H with
| (if ?g then _ else _) = _ => destruct g eqn:G
end.
- (* As for [Interval]: the first three conjuncts are the test of
     [TryFrom<(f64, f64)>]. *)
  injection H as <-. cbn [itv DecInterval.new_unchecked].
  rewrite !Bool.andb_true_iff in G.
  destruct G as [[[[[Hab Ha] Hb] _] _] _].
  rewrite Bool.negb_true_iff in Ha, Hb.
  exact (with_infsup_raw_valid a b Hab Ha Hb).
- destruct (eq a (B754_infinity false) && eq b (B754_infinity true) &&
            dec_eqb d Trv).
  + injection H as <-. exact EMPTY_valid.
  + destruct (is_nan a && is_nan b && dec_eqb d Ill); [|discriminate].
    injection H as <-. exact EMPTY_valid.
Qed.

Theorem from_dec_ninterval_valid :
  forall m x, valid (itv (DecInterval.from_dec_ninterval m x)).
Proof.
intros m x. unfold DecInterval.from_dec_ninterval. cbv zeta.
apply set_dec_valid.
set (a := f64_f (number_to_f64 m (ninf (nx x)) Inf)).
set (b := f64_f (number_to_f64 m (nsup (nx x)) Sup)).
destruct (Interval.try_from a b) as [y|] eqn:E.
- exact (try_from_valid a b y E).
- exact EMPTY_valid.
Qed.
