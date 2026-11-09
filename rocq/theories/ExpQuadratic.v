(** * The hypothesis that e^r is not a root of a quadratic with integer coefficients

    [exp_not_quadratic] says that for every rational [r = p / q] other
    than 0, [e^r] is not a root of a polynomial [a t^2 + b t + c] with
    integer coefficients that are not all 0. It follows from the theorem
    of Hermite and Lindemann ([e^r] is transcendental for every algebraic
    [r] other than 0), which is not proved here. It is not an axiom: it is
    a premise of each theorem that uses it, [sinh_dir_exact_with],
    [cosh_dir_exact_with] ([DyExpExact.v]), [asinh_dir_exact_with] and
    [acosh_dir_exact_with] ([DyLogExact.v]) and their forms for the Rust,
    so that it is in the statements of those theorems, and
    [Print Assumptions] does not list it among their axioms. *)

From Stdlib Require Import ZArith Reals.

Open Scope R_scope.

Definition exp_not_quadratic : Prop :=
  forall p q : Z, (0 < q)%Z -> p <> 0%Z ->
  forall a b c : Z, (a <> 0 \/ b <> 0 \/ c <> 0)%Z ->
  IZR a * exp (IZR p / IZR q) ^ 2 + IZR b * exp (IZR p / IZR q) + IZR c <> 0.
