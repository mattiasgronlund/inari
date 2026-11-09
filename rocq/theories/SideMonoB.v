(** * Outward fields give wider intervals: [pow], [powi], [atan2] and the trigonometric functions

    As [SideMono.v], for the interval functions that take the minimum or
    the maximum of fields ([pow]), that return an [option] ([powi],
    [atan2]), or that branch on the value of a field: [sin], [cos] and
    [tan] choose their case by [quadrants], which reads the signs of the
    fields of [sin] and [cos] through [quadrant]. For them the records
    must also give the same [quadrant] at every argument. *)

From Stdlib Require Import ZArith Reals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Mpfr SideDefs SideMono.

Open Scope R_scope.

(** The proofs follow the code: [split_shared p q] splits the goal on
    every [match] whose scrutinee reads neither record [p] nor [q], so
    that both sides take the same branch. Every branch of these
    functions is chosen from the arguments, and in [sin], [cos] and
    [tan] also from [quadrants], which the proofs first make the same for
    both records. A scrutinee that reads a record is the value of the
    whole function, which reduces once the branches inside it are split.
    The leaves are then intervals that do not read the record
    ([wider_refl]), or whose bounds are fields, [fmin]/[fmax] of fields,
    or constants ([wir_wider], [fmin_out], [fmax_out]). *)

Ltac reads_no p q c :=
  lazymatch c with
  | context [p] => fail
  | context [q] => fail
  | _ => idtac
  end.

Ltac split_shared p q :=
  repeat (cbv beta iota zeta delta [fst];
    match goal with
    | |- context [match ?c with Some _ => _ | None => _ end] =>
        reads_no p q c; destruct c
    | |- context [if ?c then _ else _] => reads_no p q c; destruct c
    | |- context [match ?c with (_, _) => _ end] => reads_no p q c; destruct c
    | |- context [match ?c with
                  | CE => _ | CM => _ | CN0 => _ | CN1 => _
                  | CP0 => _ | CP1 => _ | CZ => _ end] =>
        reads_no p q c; destruct c
    end).

(** A bound of the [p] side outward of the bound of the [q] side. *)
Ltac side_bound H :=
  lazymatch goal with
  | |- outward _ (fmin _ _ _) _ => apply fmin_out; apply H
  | |- outward _ (fmax _ _ _) _ => apply fmax_out; apply H
  | |- outward _ ?v ?v => left; reflexivity
  | |- _ => apply H
  end.

Ltac side_leaf H :=
  lazymatch goal with
  | |- wider ?y ?y => apply wider_refl
  | |- wider (Interval.with_infsup_raw _ _) (Interval.with_infsup_raw _ _) =>
      apply wir_wider; side_bound H
  end.

(** [injection] would compute the constant bounds, so that the two sides
    no longer match as terms. *)
Lemma some_inj : forall (A : Type) (a b : A), Some a = Some b -> a = b.
Proof. congruence. Qed.

(** A leaf of a function that returns an [option]: the [q] side returned
    [Some], and so did the [p] side, at the same branch. *)
Ltac opt_leaf H :=
  let E := fresh "E" in
  intro E;
  first
    [ discriminate E
    | apply some_inj in E; subst; eexists; split; [reflexivity | side_leaf H] ].

Lemma pow_wider :
  forall p q, fld_out2 (p_pow p) (p_pow q) ->
  forall first_min first_max x y,
  wider (Interval.pow p first_min first_max x y) (Interval.pow q first_min first_max x y).
Proof.
intros p q H first_min first_max x y. unfold fld_out2 in H.
unfold Interval.pow, Interval.pow_impl.
split_shared p q.
all: side_leaf H.
Qed.

Lemma pown_wider :
  forall p q, fld_out_z (p_pown p) (p_pown q) ->
  forall n x y, Interval.powi q n x = Some y ->
  exists y', Interval.powi p n x = Some y' /\ wider y' y.
Proof.
intros p q H n x y. unfold fld_out_z in H.
unfold Interval.powi, Interval.powi_impl.
split_shared p q.
all: opt_leaf H.
Qed.

Lemma atan2_wider :
  forall p q, fld_out2 (p_atan2 p) (p_atan2 q) ->
  forall y x z, Interval.atan2 q y x = Some z ->
  exists z', Interval.atan2 p y x = Some z' /\ wider z' z.
Proof.
intros p q H y x z. unfold fld_out2 in H.
unfold Interval.atan2, Interval.atan2_impl.
split_shared p q.
all: opt_leaf H.
Qed.

(** [quadrants] reads the record only through [quadrant]. *)
Lemma quadrants_same :
  forall p q, (forall z, quadrant p z = quadrant q z) ->
  forall a b, quadrants p a b = quadrants q a b.
Proof.
intros p q HQ a b. unfold quadrants. rewrite !HQ. reflexivity.
Qed.

Lemma sin_wider :
  forall p q, fld_out (p_sin p) (p_sin q) -> (forall z, quadrant p z = quadrant q z) ->
  forall has_fma first x y, Interval.sin q has_fma first x = Some y ->
  exists y', Interval.sin p has_fma first x = Some y' /\ wider y' y.
Proof.
intros p q H HQ has_fma first x y. unfold fld_out in H.
unfold Interval.sin. cbv zeta.
rewrite (quadrants_same p q HQ).
generalize (quadrants q (Interval.inf_raw x) (Interval.sup_raw x)) as qn.
intros qn.
split_shared p q.
all: opt_leaf H.
Qed.

Lemma cos_wider :
  forall p q, fld_out (p_cos p) (p_cos q) -> (forall z, quadrant p z = quadrant q z) ->
  forall has_fma first x y, Interval.cos q has_fma first x = Some y ->
  exists y', Interval.cos p has_fma first x = Some y' /\ wider y' y.
Proof.
intros p q H HQ has_fma first x y. unfold fld_out in H.
unfold Interval.cos. cbv zeta.
rewrite (quadrants_same p q HQ).
generalize (quadrants q (Interval.inf_raw x) (Interval.sup_raw x)) as qn.
intros qn.
split_shared p q.
all: opt_leaf H.
Qed.

Lemma tan_wider :
  forall p q, fld_out (p_tan p) (p_tan q) -> (forall z, quadrant p z = quadrant q z) ->
  forall has_fma x y, Interval.tan q has_fma x = Some y ->
  exists y', Interval.tan p has_fma x = Some y' /\ wider y' y.
Proof.
intros p q H HQ has_fma x y. unfold fld_out in H.
unfold Interval.tan, Interval.tan_impl. cbv zeta.
rewrite (quadrants_same p q HQ).
generalize (quadrants q (Interval.inf_raw x) (Interval.sup_raw x)) as qn.
intros qn.
split_shared p q.
all: opt_leaf H.
Qed.
