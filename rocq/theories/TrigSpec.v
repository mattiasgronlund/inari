(** * When [sin], [cos] and [tan] of intervals are tightest

    [Interval::cos] computes [q = floor(x / PI)] with interval [/] and
    [floor], and decides from its bounds which multiples of π lie in [x];
    [Interval::sin] and [Interval::tan] do the same with [FRAC_PI_2]. As
    [x / PI] only encloses the quotients [r / π] ([Interval::PI] is an
    enclosure of π, and the division rounds outward), [q] can be wider
    than the hull of [floor(r / π)] over [x] when a bound of [x] is close
    to a multiple of π, and the result is then only an enclosure, not
    always the tightest (see [Cos.v]). [trig_tight] says when the theorems claim
    the tightest result: when [x] holds at most one real, or two reals at
    least [w] apart, where [w] is [2 * PI] for [sin] and [cos] and [PI] for
    [tan], so that [x] contains a full period, or [q] is that hull. Like
    [Ieee1788.v], this file has to be checked by reading. *)

From Stdlib Require Import ZArith Reals.
From Inari Require Import Model Ieee1788.

Open Scope R_scope.

(** For [C] = [Interval::PI] and [c] = π, or [C] = [Interval::FRAC_PI_2]
    and [c] = π/2. *)
Definition trig_tight (has_fma : bool) (C : Interval) (c w : R) (x : Interval) :
    Prop :=
  (forall r t, mem r x -> mem t x -> r = t) \/
  (exists r t, mem r x /\ mem t x /\ w <= t - r) \/
  (forall z, Interval.div has_fma x C = Some z ->
   is_hull (image (fun r => Rfloor (r / c)) x) (Interval.floor z)).
