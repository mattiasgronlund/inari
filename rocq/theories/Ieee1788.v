(** * What IEEE 1788 asks of an interval version of a function

    The theorems in [Abs.v], [AddSub.v], [Cancel.v], [CancelSpec.v],
    [Div.v], [Integer.v], [MaxMin.v], [DecMaxMin.v], [Mul.v], [MulRev.v],
    [Neg.v], [Recip.v], [Round.v], [Sign.v], [Sqr.v], [Sqrt.v] and
    [Trunc.v] are stated with the definitions here and the ones in
    [Model.v]. Like [Model.v], this file has to be checked by reading:
    against the standard, IEEE Std 1788-2015, rather than against the Rust
    code, [two_output] against the doc comment of
    [Interval::mul_rev_to_pair], and [cancel_result] against that of
    [Interval::cancel_minus]. Continuity of a
    function of one real is that of
    Stdlib's [continuity_pt] and [continue_in], and of two reals that of
    [continuity2_pt] and [continue_in2] below. The point functions [abs],
    [max], [min], [neg], [add], [sub], [mul], [sqr], [sqrt], [recip] and
    [div] are Stdlib's [Rabs], [Rmax], [Rmin], [Ropp], [Rplus], [Rminus],
    [Rmult], [Rsqr], [sqrt], [Rinv] and [Rdiv], the last four with their
    domains [sqr_dom], which is all of R, [sqrt_dom], [recip_dom], and the
    product of [div_dom1] and [div_dom2]. *)

From Stdlib Require Import Reals.
From Flocq Require Import Core.Raux Core.Generic_fmt Core.Round_NE.
From Inari Require Import Model.

Open Scope R_scope.

(** The point functions [floor] and [ceil], from R to R. *)
Definition Rfloor (r : R) : R := IZR (Zfloor r).
Definition Rceil (r : R) : R := IZR (Zceil r).

(** The point functions [roundTiesToAway], [roundTiesToEven] and [trunc].
    Flocq's [Znearest choice r] is the integer nearest to [r], and for a
    tie between [Zfloor r] and [Zfloor r + 1], the latter if
    [choice (Zfloor r)]. [ZnearestA] chooses it if [0 <= Zfloor r], which
    is away from zero, and [ZnearestE] if [Zfloor r] is odd, which gives the
    even one. [Ztrunc] rounds toward zero. *)
Definition Rround (r : R) : R := IZR (ZnearestA r).
Definition Rround_ties_even (r : R) : R := IZR (ZnearestE r).
Definition Rtrunc (r : R) : R := IZR (Ztrunc r).

(** The point function [sign]: [-1] below 0, [0] at 0, and [1] above. *)
Definition Rsign (r : R) : R :=
  match Rcompare r 0 with Lt => -1 | Eq => 0 | Gt => 1 end.

(** The image of the interval [x] under [f], as a set of reals. *)
Definition image (f : R -> R) (x : Interval) : R -> Prop :=
  fun s => exists r, mem r x /\ s = f r.

(** [y] holds exactly the reals between two elements of [s]. It is then
    the smallest interval that contains [s], so it is the result of a
    tightest interval version of [f] if [s] is the image of its argument
    under [f]. *)
Definition is_hull (s : R -> Prop) (y : Interval) : Prop :=
  valid y /\ forall r, mem r y <-> exists u v, s u /\ s v /\ u <= r <= v.

(** [y] is the smallest of the intervals that [valid] describes, whose
    bounds are floats or infinities, that contain [s]: it contains [s], and
    every such interval that contains [s] contains [y]. It is the result of
    a tightest interval version of [f] if [s] is the image of its argument
    under [f], and the image need not have a hull of this form, as the
    bounds of a sum of floats need not be floats. *)
Definition is_tightest (s : R -> Prop) (y : Interval) : Prop :=
  valid y /\ (forall r, s r -> mem r y) /\
  forall z, valid z -> (forall r, s r -> mem r z) -> forall r, mem r y -> mem r z.

Definition bounded (s : R -> Prop) : Prop :=
  exists m, forall r, s r -> Rabs r <= m.

(** The predicate [p_d(f, x)] that the decoration [d] asserts about [f] on
    [x], for a function [f] defined on all of R:

    - [com]: [x] is nonempty and bounded, [f] is continuous at each point
      of [x], and the image of [x] is bounded. The standard asks this of the
      computed interval instead. For a result that is the hull of the image,
      as the theorems stated with [p] show, the two are the same
      ([is_hull_bounded] in [Integer.v]). [p2] below, for functions of two
      reals, asks it of the computed interval, as the standard does,
      because a sum can overflow:
      [[f64::MAX, f64::MAX] + [f64::MAX, f64::MAX]] is
      [[f64::MAX, +inf]], though the image is bounded. A square can
      overflow too, so [sqr] is stated with [p_dom] and [sqr_dom] below.
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

(** ** Functions of one real with a domain

    A point function of IEEE 1788 may be defined only on a set of reals,
    its domain [Dom(f)]. Here, such a function is a function [f] from R to
    R with a domain [D], and only the values of [f] on [D] matter to the
    definitions below. Stdlib's [sqrt], for example, returns 0 below 0,
    where the standard's [sqrt] is not defined, and those values are never
    used. *)

(** The domain of the point function [sqrt]. *)
Definition sqrt_dom (r : R) : Prop := 0 <= r.

(** The domain of the point function [sqr], all of R. [sqr] is stated
    with the definitions for a function with a domain because [p_dom],
    unlike [p], asks for [com] that the computed interval be bounded, as
    the standard does: [[f64::MAX, f64::MAX]] squared is
    [[f64::MAX, +inf]], though the image is bounded. *)
Definition sqr_dom (r : R) : Prop := True.

(** The domain of the point function [recip], all reals but 0. Stdlib's
    [Rinv] returns 0 at 0, and that value is never used. *)
Definition recip_dom (r : R) : Prop := r <> 0.

(** The image of the interval [x] under [f] defined on [D], which the
    standard writes [Rge(f | x)]: the values of [f] at the reals of [x]
    that are in [D]. The reals of [x] outside [D] are ignored, so the
    image of [[-1, 1]] under [sqrt] is [[0, 1]]. *)
Definition image_dom (D : R -> Prop) (f : R -> R) (x : Interval) :
    R -> Prop :=
  fun s => exists r, mem r x /\ D r /\ s = f r.

(** The predicate [p_d(f, x)] for a function [f] defined on [D], with the
    computed interval [z]:

    - [com]: [x] is a bounded, nonempty subset of [D], [f] is continuous
      at each point of [x], and [z] is bounded. [f] is continuous at a
      point of [D] if its restriction to [D] is, as for the standard,
      whose [sqrt] is continuous at each point of its domain, 0 included.
      As in [p2], and as the standard asks, [z] has to be bounded, rather
      than the image.
    - [dac]: [x] is a nonempty subset of [D], and the restriction of [f]
      to [x] is continuous.
    - [def]: [x] is a nonempty subset of [D].
    - [trv]: always true.
    - [ill] is only for NaI, never the result of evaluating [f]. *)
Definition p_dom (D : R -> Prop) (d : Decoration) (f : R -> R) (x z : Interval) :
    Prop :=
  let X := fun r => mem r x in
  match d with
  | Ill => False
  | Trv => True
  | Def => (exists r, X r) /\ (forall r, X r -> D r)
  | Dac =>
      (exists r, X r) /\ (forall r, X r -> D r) /\
      forall r, X r -> continue_in f X r
  | Com =>
      (exists r, X r) /\ (forall r, X r -> D r) /\ bounded X /\
      (forall r, X r -> continue_in f D r) /\ bounded (fun s => mem s z)
  end.

(** [strongest d f x] for a function [f] defined on [D], with the computed
    interval [z]. *)
Definition strongest_dom (D : R -> Prop) (d : Decoration) (f : R -> R)
    (x z : Interval) : Prop :=
  p_dom D d f x z /\
  forall e, p_dom D e f x z -> (discriminant e <= discriminant d)%Z.

(** ** Functions of two reals *)

(** The image of the box [x × y] under [f], as a set of reals. *)
Definition image2 (f : R -> R -> R) (x y : Interval) : R -> Prop :=
  fun s => exists r t, mem r x /\ mem t y /\ s = f r t.

(** The restriction of [f] to [X × Y] is continuous at [(r, t)], in the
    topology of R², which is that of the norm [max(|r|, |t|)]. This is
    Stdlib's [continue_in] with a pair of reals in place of a real. *)
Definition continue_in2 (f : R -> R -> R) (X Y : R -> Prop) (r t : R) : Prop :=
  forall eps, 0 < eps -> exists delta, 0 < delta /\
    forall r' t', X r' -> Y t' -> Rabs (r' - r) < delta -> Rabs (t' - t) < delta ->
    Rabs (f r' t' - f r t) < eps.

(** [f] is continuous at [(r, t)], like Stdlib's [continuity_pt]. *)
Definition continuity2_pt (f : R -> R -> R) (r t : R) : Prop :=
  continue_in2 f (fun _ => True) (fun _ => True) r t.

(** [p d f x] for a function [f] of two reals, defined on all of R², and
    the box [x × y] in place of [x]: the box is nonempty if [x] and [y]
    are, and bounded if they are. For [com], the computed interval [z],
    rather than the image, has to be bounded, as the standard asks. *)
Definition p2 (d : Decoration) (f : R -> R -> R) (x y z : Interval) : Prop :=
  let X := fun r => mem r x in
  let Y := fun t => mem t y in
  match d with
  | Ill => False
  | Trv => True
  | Def => (exists r, X r) /\ (exists t, Y t)
  | Dac =>
      (exists r, X r) /\ (exists t, Y t) /\
      forall r t, X r -> Y t -> continue_in2 f X Y r t
  | Com =>
      (exists r, X r) /\ (exists t, Y t) /\ bounded X /\ bounded Y /\
      (forall r t, X r -> Y t -> continuity2_pt f r t) /\
      bounded (fun s => mem s z)
  end.

(** [strongest d f x] for a function [f] of two reals, the box [x × y]
    and the computed interval [z]. An operation on two decorated intervals
    returns the minimum of this decoration and those of its arguments. *)
Definition strongest2 (d : Decoration) (f : R -> R -> R) (x y z : Interval) :
    Prop :=
  p2 d f x y z /\ forall e, p2 e f x y z -> (discriminant e <= discriminant d)%Z.

(** ** Functions of two reals with a domain

    A point function of two reals may be defined only on a subset of R².
    Here the domain is a product [D1 × D2] of two sets of reals, as that of
    [/], [R × (R ∖ {0})], is. A product suffices for [/], and it lets the
    restriction of [f] to the domain be stated with [continue_in2], as for
    a box. As for one real, only the values of [f] on the domain matter:
    Stdlib's [Rdiv] returns 0 for a divisor 0, and that value is never
    used. *)

(** The domain of the point function [/], [div_dom1 × div_dom2]. *)
Definition div_dom1 (r : R) : Prop := True.
Definition div_dom2 (t : R) : Prop := t <> 0.

(** The image of the box [x × y] under [f] defined on [D1 × D2]: the values
    of [f] at the points of the box that are in the domain. The image of
    [[1, 2] × [0, 1]] under [/] is [[1, +inf)]. *)
Definition image2_dom (D1 D2 : R -> Prop) (f : R -> R -> R) (x y : Interval) :
    R -> Prop :=
  fun s => exists r t, mem r x /\ mem t y /\ D1 r /\ D2 t /\ s = f r t.

(** [p_dom D d f x z] for a function [f] of two reals defined on
    [D1 × D2], and the box [x × y] in place of [x]: the box is a nonempty
    subset of the domain if [x] and [y] are nonempty subsets of [D1] and
    [D2], and bounded if they are bounded. For [com], [f] is continuous at
    each point of the box relative to the domain, as in [p_dom], and the
    computed interval [z] is bounded, as in [p2]. *)
Definition p2_dom (D1 D2 : R -> Prop) (d : Decoration) (f : R -> R -> R)
    (x y z : Interval) : Prop :=
  let X := fun r => mem r x in
  let Y := fun t => mem t y in
  match d with
  | Ill => False
  | Trv => True
  | Def =>
      (exists r, X r) /\ (exists t, Y t) /\
      (forall r, X r -> D1 r) /\ (forall t, Y t -> D2 t)
  | Dac =>
      (exists r, X r) /\ (exists t, Y t) /\
      (forall r, X r -> D1 r) /\ (forall t, Y t -> D2 t) /\
      forall r t, X r -> Y t -> continue_in2 f X Y r t
  | Com =>
      (exists r, X r) /\ (exists t, Y t) /\
      (forall r, X r -> D1 r) /\ (forall t, Y t -> D2 t) /\
      bounded X /\ bounded Y /\
      (forall r t, X r -> Y t -> continue_in2 f D1 D2 r t) /\
      bounded (fun s => mem s z)
  end.

(** [strongest2 d f x y z] for a function [f] of two reals defined on
    [D1 × D2]. *)
Definition strongest2_dom (D1 D2 : R -> Prop) (d : Decoration) (f : R -> R -> R)
    (x y z : Interval) : Prop :=
  p2_dom D1 D2 d f x y z /\
  forall e, p2_dom D1 D2 e f x y z -> (discriminant e <= discriminant d)%Z.

(** ** Two-output division

    The standard's [mulRevToPair(b, c)] is [b.mul_rev_to_pair(c)] in
    inari, whose doc comment writes its set [c ⊘′ b]: the reals [z] with
    [t * z] in [c] for some [t] in [b]. The doc comment says that the set
    is empty, or has one or two connected components, and that the two
    intervals enclose them. [two_output] states what it asks of them. *)

(** The reals [z] with [t * z] in [c] for some [t] in [b]. If [b] and [c]
    are [[0, 0]], it is all of R. *)
Definition mul_rev (b c : Interval) : R -> Prop :=
  fun z => exists t, mem t b /\ mem (t * z) c.

(** [s] holds every real between two of its elements. The connected
    subsets of R are the convex ones. *)
Definition convex (s : R -> Prop) : Prop :=
  forall u v r, s u -> s v -> u <= r <= v -> s r.

(** [k] is a connected component of [s]: a nonempty convex subset of [s]
    that every convex subset of [s] that contains it equals. *)
Definition component (s k : R -> Prop) : Prop :=
  (exists r, k r) /\ convex k /\ (forall r, k r -> s r) /\
  forall k', convex k' -> (forall r, k r -> k' r) -> (forall r, k' r -> s r) ->
    forall r, k' r -> k r.

(** What the doc comment of [Interval::mul_rev_to_pair] asks of its
    outputs [u] and [v] for the set [s]:
    - [s] is empty, and [u] and [v] are the empty interval;
    - [s] has one component [k], i.e. every component of [s] has the
      elements of [k], [u] is the tightest interval that contains [k],
      and [v] is the empty interval;
    - [s] has two components [k1] and [k2], every element of [k1] below
      every element of [k2], and [u] and [v] are the tightest intervals
      that contain [k1] and [k2].
    So [s] has at most two components. *)
Definition two_output (s : R -> Prop) (u v : Interval) : Prop :=
  ((forall r, ~ s r) /\ u = Interval.EMPTY /\ v = Interval.EMPTY) \/
  (exists k, component s k /\ (forall k', component s k' -> forall r, k' r <-> k r) /\
     is_tightest k u /\ v = Interval.EMPTY) \/
  (exists k1 k2, component s k1 /\ component s k2 /\
     (forall r t, k1 r -> k2 t -> r < t) /\
     (forall k', component s k' ->
        (forall r, k' r <-> k1 r) \/ (forall r, k' r <-> k2 r)) /\
     is_tightest k1 u /\ is_tightest k2 v).

(** ** Cancellative subtraction and addition

    IEEE 1788's cancelMinus(x, y) is the tightest interval [z] such that
    [y + z ⊇ x], where [+] is the sum of sets of reals, if there is such a
    [z]. There is for an empty [x] and a bounded [y], when it is empty, and
    for nonempty bounded [x = [a, b]] and [y = [c, d]] with
    [d - c <= b - a], when it is [[a - c, b - d]]. Otherwise it has no value,
    and an interval version returns Entire. cancelPlus(x, y) is
    cancelMinus(x, -y). The sets [X] and [Y] below are the reals of [x] and
    [y], so that cancelPlus is cancelMinus of [X] and the negations of the
    reals of [y]. *)

(** [Y + Z ⊇ X]: every real of [X] is a real of [Y] plus a real of [Z]. *)
Definition sum_superset (Y Z X : R -> Prop) : Prop :=
  forall r, X r -> exists s t, Y s /\ Z t /\ r = s + t.

(** cancelMinus(X, Y) has a value. *)
Definition cancel_defined (X Y : R -> Prop) : Prop :=
  ((forall r, ~ X r) /\ bounded Y) \/
  (exists a b c d, a <= b /\ c <= d /\ d - c <= b - a /\
     (forall r, X r <-> a <= r <= b) /\ (forall r, Y r <-> c <= r <= d)).

(** [z] is the result of cancelMinus(X, Y) as the doc comment of
    [Interval::cancel_minus] states it: if cancelMinus(X, Y) has a value,
    the tightest interval [z] such that [Y + z ⊇ X], i.e. the [valid] one
    that every other [valid] interval with this property contains, and
    [Interval::ENTIRE] otherwise. [cancel_result_empty] and
    [cancel_result_hull] in [CancelSpec.v] show that [z] is then the empty
    interval and the tightest interval that contains [[a - c, b - d]],
    which is what IEEE 1788 asks of an interval version. *)
Definition cancel_result (X Y : R -> Prop) (z : Interval) : Prop :=
  (cancel_defined X Y ->
     valid z /\ sum_superset Y (fun t => mem t z) X /\
     forall z', valid z' -> sum_superset Y (fun t => mem t z') X ->
       forall r, mem r z -> mem r z') /\
  (~ cancel_defined X Y -> z = Interval.ENTIRE).
