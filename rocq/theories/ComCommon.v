(** * A [DecInterval] is [com] only if its interval is common

    [dec_sign_correct], [dec_max_correct], [dec_min_correct],
    [dec_mul_correct], [dec_recip_correct] and [dec_div_correct] assume
    [com_common] of each argument, and [dec_mul_add_correct] of its first
    two: the argument is [com] only if its interval is common, i.e.
    nonempty and bounded. This file shows that every [DecInterval] that the
    library makes has this property.

    Rust makes a value of a struct only with a struct expression or with
    [unsafe] code such as [transmute], and otherwise copies existing ones.
    The fields of [struct DecInterval] are private to its module,
    [src/interval/dec_interval.rs], which has no submodule, so the compiler
    rejects a struct expression of the type, under any name, and an
    assignment to a field outside that file. That file has one struct
    expression, the body of [new_unchecked], and neither assigns to a
    field nor takes a mutable reference to one, which code outside it
    could assign through. Its derived [Clone], [Copy] and [Debug] copy the
    value or read the fields. The only [transmute] into a [DecInterval] is
    the one in [const_dec_interval!]. So every [DecInterval] comes from
    [const_dec_interval!] or from one of the callers of [new_unchecked]:
    - [DecInterval::new] ([new_com_common]);
    - [DecInterval::set_dec] ([set_dec_com_common]), for any interval and
      decoration, so for every caller, such as [x * y];
    - the constants [EMPTY], [NAI] and [ENTIRE] ([constants_com_common]),
      and those that [def_com!] defines ([def_com_com_common], with
      [def_com_ok_bounds] for its hypotheses);
    - [convex_hull] and [intersection] ([set_op_com_common]);
    - [try_from_be_bytes], [try_from_le_bytes] and [try_from_ne_bytes]
      ([try_from_bytes_com_common]);
    and [const_dec_interval!] is [const_dec_interval_com_common].

    The theorems for [new], [set_dec], [convex_hull] and [intersection]
    hold for any arguments, not only [valid] ones. *)

From Stdlib Require Import ZArith.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Inari Require Import Model Integer.

(** [x] is [com] only if its interval is common. *)
Definition com_common (x : DecInterval) : Prop :=
  dec x = Com -> Interval.is_common_interval (itv x) = true.

(** A decoration other than [com] makes no claim on the interval. *)
Lemma new_unchecked_com_common :
  forall x d, d <> Com -> com_common (DecInterval.new_unchecked x d).
Proof.
intros x d Hd E. now elim Hd.
Qed.

(** [[a, b]] is common if [a <= b], which excludes a NaN bound, [a] is not
    -inf and [b] is not +inf: the bounds are then finite, as [a] = +inf
    would force [b] = +inf, and [b] = -inf would force [a] = -inf. *)
Lemma const_interval_common :
  forall a b, le a b = true ->
  eq a (B754_infinity true) = false -> eq b (B754_infinity false) = false ->
  Interval.is_common_interval (Interval.const_interval a b) = true.
Proof.
intros a b Hab Ha Hb.
rewrite is_common_interval_lt, infinity_eq. cbn [Interval.const_interval rep fst snd].
destruct a as [[|]|[|]| |sa ma ea Ea], b as [[|]|[|]| |sb mb eb Eb];
  try discriminate; reflexivity.
Qed.

(** [DecInterval::new] decorates an interval [com] only if it is
    common. *)
Theorem new_com_common : forall x, com_common (DecInterval.new x).
Proof.
intros x. unfold com_common, DecInterval.new. cbv zeta.
cbn [dec itv DecInterval.new_unchecked].
destruct (Interval.is_empty x); [discriminate|].
now destruct (Interval.is_common_interval x).
Qed.

(** [set_dec] keeps [com] only for a common interval, and lowers it to
    [dac] otherwise. *)
Theorem set_dec_com_common :
  forall x d, com_common (DecInterval.set_dec x d).
Proof.
intros x d. unfold com_common, DecInterval.set_dec.
destruct (dec_eqb d Ill); [discriminate|].
destruct (Interval.is_empty x); [discriminate|].
destruct (dec_eqb d Com && negb (Interval.is_common_interval x)) eqn:E;
  [discriminate|].
cbn [dec itv DecInterval.new_unchecked]. intros ->. cbn in E.
now destruct (Interval.is_common_interval x).
Qed.

(** [EMPTY], [NAI] and [ENTIRE] are [trv], [ill] and [dac]. *)
Theorem constants_com_common :
  com_common DecInterval.EMPTY /\ com_common DecInterval.NAI /\
  com_common DecInterval.ENTIRE.
Proof.
repeat split; apply new_unchecked_com_common; discriminate.
Qed.

(** A constant that [def_com!] decorates [com] is common if its bounds are
    finite, which they are, as the assertion in [def_com!] implies
    ([def_com_ok_bounds] below). *)
Theorem def_com_com_common :
  forall a b, is_finite a = true -> is_finite b = true ->
  com_common (DecInterval.def_com a b).
Proof.
intros a b Ha Hb _. unfold DecInterval.def_com. cbn [itv DecInterval.new_unchecked].
rewrite is_common_interval_lt, infinity_eq. cbn [Interval.const_interval rep fst snd].
destruct a as [[|]|[|]| |sa ma ea Ea], b as [[|]|[|]| |sb mb eb Eb];
  try discriminate; reflexivity.
Qed.

(** [def_com!(C)] compiles only if [Interval::C] passes its assertion
    [def_com_ok], and then [Interval::C] is [const_interval a b] for finite
    floats [a <= b], so that
    [new_unchecked(Interval::C, Decoration::Com)] is [def_com a b] with the
    hypotheses of [def_com_com_common] and of [dmade_def_com] in
    [Valid.v]. *)
Theorem def_com_ok_bounds :
  forall x, DecInterval.def_com_ok x = true ->
  exists a b, x = Interval.const_interval a b /\
    is_finite a = true /\ is_finite b = true /\
    Interval.const_interval_ok a b = true.
Proof.
intros [[na b]] H. unfold DecInterval.def_com_ok in H. cbn [rep] in H.
exists (opp na), b. split.
{ unfold Interval.const_interval, opp. now rewrite Bopp_involutive. }
generalize (opp na) H. clear na H. intros a H.
apply andb_prop in H as [H Hb]. apply andb_prop in H as [Ha Hab].
unfold Interval.const_interval_ok. rewrite Hab.
destruct a as [[|]|[|]| |sa ma ea Ea], b as [[|]|[|]| |sb mb eb Eb];
  try discriminate; repeat split; reflexivity.
Qed.

(** [convex_hull] and [intersection] of [DecInterval]s are [trv] or
    NaI. *)
Theorem set_op_com_common :
  forall f x y, com_common (DecInterval.set_op f x y).
Proof.
intros f x y. unfold DecInterval.set_op.
destruct (DecInterval.is_nai x || DecInterval.is_nai y);
  apply new_unchecked_com_common; discriminate.
Qed.

(** [try_from_be_bytes] and its siblings accept [com] only with bounds
    that make the interval common. *)
Theorem try_from_bytes_com_common :
  forall a b c z, DecInterval.try_from_bytes a b c = Some z -> com_common z.
Proof.
intros a b c z H. unfold DecInterval.try_from_bytes in H.
match type of H with
| match ?o with Some _ => _ | None => _ end = _ =>
    destruct o as [d|]; [|discriminate]
end.
destruct (le a b) eqn:Hab; cbv beta iota in H; cbn [andb] in H.
- match type of H with
  | (if ?g then _ else _) = _ => destruct g eqn:G
  end.
  + injection H as <-. intros Ed. cbn [dec DecInterval.new_unchecked] in Ed.
    subst d. cbn [itv DecInterval.new_unchecked].
    (* The last conjunct, with [dec = Com], says that [a] is not -inf
       and [b] is not +inf. *)
    rewrite !Bool.andb_true_iff in G. destruct G as (_ & G).
    change (dec_eqb Com Com) with true in G. cbn [negb orb] in G.
    rewrite Bool.andb_true_iff, !Bool.negb_true_iff in G. destruct G as [Ha Hb].
    exact (const_interval_common a b Hab Ha Hb).
  + destruct (eq a (B754_infinity false) && eq b (B754_infinity true) &&
              dec_eqb d Trv).
    * injection H as <-. apply (proj1 constants_com_common).
    * destruct (is_nan a && is_nan b && dec_eqb d Ill); [|discriminate].
      injection H as <-. apply (proj1 (proj2 constants_com_common)).
- destruct (eq a (B754_infinity false) && eq b (B754_infinity true) &&
            dec_eqb d Trv).
  + injection H as <-. apply (proj1 constants_com_common).
  + destruct (is_nan a && is_nan b && dec_eqb d Ill); [|discriminate].
    injection H as <-. apply (proj1 (proj2 constants_com_common)).
Qed.

(** [const_dec_interval!] gives [com] only to an interval without an
    infinite bound, which is common if [a <= b], as it is for every
    [const_dec_interval!(a, b)] that compiles. *)
Theorem const_dec_interval_com_common :
  forall a b, le a b = true -> com_common (DecInterval.const_dec_interval a b).
Proof.
intros a b Hab. unfold com_common, DecInterval.const_dec_interval.
cbn [dec itv].
destruct (eq a (B754_infinity true) || eq b (B754_infinity false)) eqn:E;
  [discriminate|].
intros _. apply Bool.orb_false_iff in E. destruct E as [Ha Hb].
exact (const_interval_common a b Hab Ha Hb).
Qed.
