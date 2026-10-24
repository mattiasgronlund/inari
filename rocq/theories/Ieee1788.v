(** * What IEEE 1788 asks of an interval version of a function

    The theorems in [Integer.v] are stated with the definitions here and
    the ones in [Model.v]. Like [Model.v], this file has to be checked by
    reading: against the standard, IEEE Std 1788-2015, rather than against
    the Rust code. Continuity is that of Stdlib's [continuity_pt] and
    [continue_in]. *)

From Stdlib Require Import Reals.
From Flocq Require Import Core.Raux.
From Inari Require Import Model.

Open Scope R_scope.

(** The point functions [floor] and [ceil], from R to R. *)
Definition Rfloor (r : R) : R := IZR (Zfloor r).
Definition Rceil (r : R) : R := IZR (Zceil r).

(** The image of the interval [x] under [f], as a set of reals. *)
Definition image (f : R -> R) (x : Interval) : R -> Prop :=
  fun s => exists r, mem r x /\ s = f r.

(** [y] holds exactly the reals between two elements of [s]. It is then
    the smallest interval that contains [s], so it is the result of a
    tightest interval version of [f] if [s] is the image of its argument
    under [f]. *)
Definition is_hull (s : R -> Prop) (y : Interval) : Prop :=
  valid y /\ forall r, mem r y <-> exists u v, s u /\ s v /\ u <= r <= v.

Definition bounded (s : R -> Prop) : Prop :=
  exists m, forall r, s r -> Rabs r <= m.

(** The predicate [p_d(f, x)] that the decoration [d] asserts about [f] on
    [x], for a function [f] defined on all of R:

    - [com]: [x] is nonempty and bounded, [f] is continuous at each point
      of [x], and the image of [x] is bounded. The standard asks this of the
      computed interval instead. For a result that is the hull of the image,
      as the theorems show, the two are the same ([is_hull_bounded] in
      [Integer.v]).
    - [dac]: [x] is nonempty, and the restriction of [f] to [x] is
      continuous.
    - [def]: [x] is nonempty.
    - [trv]: always true.
    - [ill] is only for NaI, never the result of evaluating [f]. *)
Definition p (d : Decoration) (f : R -> R) (x : Interval) : Prop :=
  let X := fun r => mem r x in
  match d with
  | Ill => False
  | Trv => True
  | Def => exists r, X r
  | Dac => (exists r, X r) /\ forall r, X r -> continue_in f X r
  | Com =>
      (exists r, X r) /\ bounded X /\ (forall r, X r -> continuity_pt f r) /\
      bounded (image f x)
  end.

(** [d] is the strongest decoration that holds for [f] on [x]. The standard
    orders the decorations [com > dac > def > trv > ill], as their
    discriminants in Rust do, and an operation on a decorated interval
    returns the minimum of this decoration and that of its argument. *)
Definition strongest (d : Decoration) (f : R -> R) (x : Interval) : Prop :=
  p d f x /\ forall e, p e f x -> (discriminant e <= discriminant d)%Z.
