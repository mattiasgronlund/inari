(** * [max] and [min] of decorated intervals are decorated correctly

    [DecInterval::max] and [DecInterval::min] return a NaI first argument
    unchanged, and otherwise call [set_dec] with the result of
    [Interval::max] or [Interval::min] and the minimum of the decorations
    of the arguments. If the second argument is NaI, that minimum is [ill],
    and [set_dec] returns NaI. [MaxMin.v] proves that the bare result is the
    hull of the image of the box [x × y], and the proofs here use nothing
    else about it.

    Section [Binary] proves the rest once, for any function [h] of two
    reals that is continuous at each point of R² and any interval operation
    [F] whose result is the hull of the image under [h], with
    [set_dec_correct] in [DecBinary.v]. That theorem needs the minimum of
    the decorations to be [com] only if a nonempty box with a bounded image
    is bounded. For [max] and [min], the hull of the image of an unbounded
    box can be common: [max([-inf, 1], [0, 2]) = [0, 2]]. If both arguments
    were [com], [set_dec] would keep [com], where the strongest decoration
    is [dac], as [com] asks for a bounded box. As for [sign], the theorems
    take as hypotheses that each argument is [com] only if its interval is
    common, and so bounded ([com_common]), which [ComCommon.v] shows of
    every [DecInterval] that the library makes. The minimum is [com] only
    if both decorations are, and then both intervals are common, so the box
    is bounded.

    [max] and [min] are continuous, as they move by no more than their
    arguments do. *)

From Stdlib Require Import Reals Lra.
From Inari Require Import Model Ieee1788 Integer ComCommon MaxMin DecBinary.

Open Scope R_scope.

(** ** A continuous function of two reals and its hull *)

Section Binary.

(** [h] is continuous at each point of R², and [F] returns the hull of the
    image of a box under [h]. *)
Variable h : R -> R -> R.
Variable F : Interval -> Interval -> Interval.

Hypothesis h_continuous : forall r t, continuity2_pt h r t.
Hypothesis F_hull :
  forall x y, valid x -> valid y -> is_hull (image2 h x y) (F x y).

(** The decorated version of [F] in the form of [DecInterval::max] and
    [DecInterval::min]: a NaI first argument unchanged, and otherwise
    [set_dec] of the result of [F] and the minimum of the decorations. *)
Definition dec_binary (x y : DecInterval) : DecInterval :=
  if DecInterval.is_nai x then x
  else DecInterval.set_dec (F (itv x) (itv y)) (dec_min (dec x) (dec y)).

Theorem dec_binary_correct :
  forall x y, valid (itv x) -> valid (itv y) ->
  com_common x ->
  com_common y ->
  if DecInterval.is_nai x then dec_binary x y = x
  else if DecInterval.is_nai y then dec_binary x y = DecInterval.NAI
  else
    is_hull (image2 h (itv x) (itv y)) (itv (dec_binary x y)) /\
    exists d, strongest2 d h (itv x) (itv y) (itv (dec_binary x y)) /\
      dec (dec_binary x y) = dec_min d (dec_min (dec x) (dec y)).
Proof.
intros x y Hx Hy Hcx Hcy. unfold dec_binary.
destruct (DecInterval.is_nai x) eqn:Nx; [reflexivity|].
assert (Hdx : dec x <> Ill).
{ intros E. unfold DecInterval.is_nai in Nx. now rewrite E in Nx. }
destruct (DecInterval.is_nai y) eqn:Ny; cbv beta iota.
- (* [dec y] is [ill], and so is the minimum, so [set_dec] returns NaI. *)
  unfold DecInterval.is_nai, dec_eqb in Ny. unfold DecInterval.set_dec.
  destruct (dec x), (dec y); cbn in Ny;
    first [discriminate | now elim Hdx | reflexivity].
- assert (Hdy : dec y <> Ill).
  { intros E. unfold DecInterval.is_nai in Ny. now rewrite E in Ny. }
  pose proof (F_hull _ _ Hx Hy) as Hz.
  (* The minimum is [com] only if both decorations are, and then both
     intervals are common, so bounded. *)
  assert (Hc : dec_min (dec x) (dec y) = Com ->
               (exists r, mem r (itv x)) -> (exists t, mem t (itv y)) ->
               bounded (image2 h (itv x) (itv y)) ->
               bounded (fun r => mem r (itv x)) /\
               bounded (fun t => mem t (itv y))).
  { intros E _ _ _. apply dec_min_Com in E. destruct E as [Ex Ey].
    split; apply common_bounded; [now apply Hcx | now apply Hcy]. }
  destruct (set_dec_correct h h_continuous (itv x) (itv y) (F (itv x) (itv y))
    (dec_min (dec x) (dec y)) Hx Hy (dec_min_not_Ill _ _ Hdx Hdy)
    (hull_tightest _ _ Hz) Hc) as (E & d & Hd & Ed).
  rewrite E. split; [exact Hz|]. exists d. split; [exact Hd | exact Ed].
Qed.

End Binary.

(** ** [max] *)

(** [max] moves by no more than its arguments do. *)
Lemma Rmax_continuous : forall r t, continuity2_pt Rmax r t.
Proof.
intros r t eps Heps. exists eps. split; [exact Heps|].
intros r' t' _ _ Hr Ht. apply Rabs_def2 in Hr, Ht.
apply Rabs_def1; unfold Rmax; destruct (Rle_dec r' t'), (Rle_dec r t); lra.
Qed.

(** [DecInterval::max] returns the tightest interval, decorated with the
    decoration that IEEE 1788 asks for, if each argument is [com] only when
    its interval is common. *)
Theorem dec_max_correct :
  forall x y, valid (itv x) -> valid (itv y) ->
  com_common x ->
  com_common y ->
  if DecInterval.is_nai x then DecInterval.max x y = x
  else if DecInterval.is_nai y then DecInterval.max x y = DecInterval.NAI
  else
    is_hull (image2 Rmax (itv x) (itv y)) (itv (DecInterval.max x y)) /\
    exists d, strongest2 d Rmax (itv x) (itv y) (itv (DecInterval.max x y)) /\
      dec (DecInterval.max x y) = dec_min d (dec_min (dec x) (dec y)).
Proof.
exact (dec_binary_correct Rmax Interval.max Rmax_continuous max_correct).
Qed.

(** ** [min] *)

(** [min] moves by no more than its arguments do. *)
Lemma Rmin_continuous : forall r t, continuity2_pt Rmin r t.
Proof.
intros r t eps Heps. exists eps. split; [exact Heps|].
intros r' t' _ _ Hr Ht. apply Rabs_def2 in Hr, Ht.
apply Rabs_def1; unfold Rmin; destruct (Rle_dec r' t'), (Rle_dec r t); lra.
Qed.

(** [DecInterval::min] does the same for [min]. *)
Theorem dec_min_correct :
  forall x y, valid (itv x) -> valid (itv y) ->
  com_common x ->
  com_common y ->
  if DecInterval.is_nai x then DecInterval.min x y = x
  else if DecInterval.is_nai y then DecInterval.min x y = DecInterval.NAI
  else
    is_hull (image2 Rmin (itv x) (itv y)) (itv (DecInterval.min x y)) /\
    exists d, strongest2 d Rmin (itv x) (itv y) (itv (DecInterval.min x y)) /\
      dec (DecInterval.min x y) = dec_min d (dec_min (dec x) (dec y)).
Proof.
exact (dec_binary_correct Rmin Interval.min Rmin_continuous min_correct).
Qed.
