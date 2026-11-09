(** * Fields and intervals that are outward of others

    [outward rnd v w]: the bound [v] is [w] or beyond it in the direction
    [rnd]. [fld_out h h']: every value of the field [h] is outward of the
    value of [h'] at the same arguments. [wider y y']: the interval [y]
    is valid where [y'] is and contains every real that [y'] contains, so
    it encloses every set that [y'] encloses ([encloses_wider]).
    [SideMono.v] and [SideMonoB.v] show that the elementary functions of
    [Model.v] return wider intervals for a record whose fields are
    outward of another's, and [SideTheorems.v] uses that. *)

From Stdlib Require Import ZArith Reals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Mpfr.

Open Scope R_scope.

Definition outward (rnd : mpfr_rnd) (v w : f64) : Prop :=
  v = w \/ match rnd with RNDD => Model.le v w = true | RNDU => Model.le w v = true end.

Definition fld_out (h h' : mpfr_rnd -> f64 -> f64) : Prop :=
  forall rnd x, outward rnd (h rnd x) (h' rnd x).

Definition fld_out2 (h h' : mpfr_rnd -> f64 -> f64 -> f64) : Prop :=
  forall rnd x y, outward rnd (h rnd x y) (h' rnd x y).

Definition fld_out_z (h h' : mpfr_rnd -> f64 -> Z -> f64) : Prop :=
  forall rnd x n, outward rnd (h rnd x n) (h' rnd x n).

Definition wider (y y' : Interval) : Prop :=
  (valid y' -> valid y) /\ forall r, mem r y' -> mem r y.

Lemma wider_refl : forall y, wider y y.
Proof. intros y. split; auto. Qed.

Lemma encloses_wider : forall s y y', encloses s y' -> wider y y' -> encloses s y.
Proof.
intros s y y' [V M] [W N]. split.
- exact (W V).
- intros r Hr. exact (N r (M r Hr)).
Qed.
