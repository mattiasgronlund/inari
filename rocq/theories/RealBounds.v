(** * Bounds of a real function on all of R

    The limits of a monotone function at -inf and +inf, which [mono_inc] of
    intervals returns for an unbounded argument, as the greatest lower
    bound and the least upper bound of its values, or no bound. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

(** [L] is the greatest lower bound of the values of [f]. *)
Definition glb_of (f : R -> R) (L : R) : Prop :=
  (forall r, L <= f r) /\ forall eps, 0 < eps -> exists r, f r < L + eps.

(** [U] is the least upper bound of the values of [f]. *)
Definition lub_of (f : R -> R) (U : R) : Prop :=
  (forall r, f r <= U) /\ forall eps, 0 < eps -> exists r, U - eps < f r.

(** The values of [f] have no lower bound, or no upper bound. *)
Definition unbounded_below (f : R -> R) : Prop := forall M, exists r, f r <= M.
Definition unbounded_above (f : R -> R) : Prop := forall M, exists r, M <= f r.
