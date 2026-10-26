(** * [classify2] of two intervals is the pair of their classes

    [Interval::classify2] shifts the discriminant of the class of [self]
    four bits to the left and ORs in that of the class of [rhs], and
    [transmute]s the result into an [IntervalClass2]. Every discriminant of
    an [IntervalClass] is below 16, so the shift drops no bits, the two
    discriminants end up in different nibbles, and [transmute_class2]
    decodes them back into the two classes. So [classify2] is defined
    whenever [classify] is defined on both arguments, which
    [classify_defined] in [Abs.v] shows for valid intervals, and it returns
    the pair of their classes. *)

From Stdlib Require Import ZArith.
From Inari Require Import Model.

Lemma classify2_pair :
  forall x y c1 c2, Interval.classify x = Some c1 -> Interval.classify y = Some c2 ->
  Interval.classify2 x y = Some (c1, c2).
Proof.
intros x y c1 c2 E1 E2. unfold Interval.classify2. rewrite E1, E2.
(* With both classes fixed, the shift, [Z.lor], [Z.div] and [Z.modulo]
   compute on the discriminants. *)
destruct c1, c2; reflexivity.
Qed.
