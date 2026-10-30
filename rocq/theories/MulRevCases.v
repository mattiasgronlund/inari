(** * Two-output division with at most one component

    [Interval::mul_rev_to_pair] matches on the classes of [y] and [x], in
    that order, as [numerator.classify2(self)] does. Apart from [N1 × M]
    and [P1 × M] ([MulRevTwo.v]):

    - [mul_rev_empty]: if [x] or [y] is empty, or [x] is [[0, 0]] and 0 is
      not in [y] ([y] in [N1] or [P1]), [mul_rev x y] is empty, and it
      returns [[EMPTY, EMPTY]].
    - [mul_rev_entire]: if 0 is in [x] and in [y] (classes [M], [N0], [P0]
      and [Z]), [t = 0] gives every real, and it returns
      [[ENTIRE, EMPTY]].
    - [mul_rev_nz]: if 0 is not in [x] ([N1] or [P1]) and [y] is not
      empty, or 0 is in [x] but not in [y] and the reals of [x] are all at
      most 0 or all at least 0 ([x] in [N0] or [P0], [y] in [N1] or [P1]),
      it returns
      [[y / x, EMPTY]] ([mul_rev_div_eq]), as [Interval::div] calls the
      same helper, or returns [Interval::zero()], for each such pair of
      classes. [mul_rev x y] is then the image of [y × x] under [/]
      ([mul_rev_div]), which [div_correct] encloses tightly, and it is
      convex ([mul_rev_convex]). *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer Sign MaxMin DecBinary AddSub
  Classify2 Classes DivTight DivSets DivZero MulZero Div MulRevSets.

Open Scope R_scope.

(** ** Zero and the classes *)

(** 0 is in an interval of class [M], [N0], [P0] or [Z]: for [M], it lies
    between a negative and a positive member. *)
Lemma classify_mem0 :
  forall x c, valid x -> Interval.classify x = Some c ->
  (c = CM \/ c = CN0 \/ c = CP0 \/ c = CZ) -> mem 0 x.
Proof.
intros x c Hx Cx H. pose proof (classify_mem x c Hx Cx) as M.
destruct H as [-> | [-> | [-> | ->]]]; cbv beta iota in M.
- destruct M as [(u & Hu & Hu0) (v & Hv & Hv0)].
  apply (mem_between x u v 0 Hx Hu Hv). lra.
- exact (proj1 (proj2 M)).
- exact (proj1 (proj2 M)).
- apply M. reflexivity.
Qed.

(** 0 is not in an interval of class [N1] or [P1]. *)
Lemma classify_not_mem0 :
  forall x c, valid x -> Interval.classify x = Some c ->
  (c = CN1 \/ c = CP1) -> ~ mem 0 x.
Proof.
intros x c Hx Cx H H0. pose proof (classify_mem x c Hx Cx) as M.
destruct H as [-> | ->]; cbv beta iota in M; destruct M as [M _];
  pose proof (M 0 H0); lra.
Qed.

(** An interval of class [N0], [N1], [P0] or [P1] holds a nonzero real. *)
Lemma classify_nonzero :
  forall x c, valid x -> Interval.classify x = Some c ->
  (c = CN0 \/ c = CN1 \/ c = CP0 \/ c = CP1) -> exists t, mem t x /\ t <> 0.
Proof.
intros x c Hx Cx H. pose proof (classify_mem x c Hx Cx) as M.
destruct H as [-> | [-> | [-> | ->]]]; cbv beta iota in M.
- destruct M as (_ & _ & t & Ht & Ht0). exists t. split; [exact Ht | lra].
- destruct M as [M (t & Ht)]. exists t. split; [exact Ht|].
  pose proof (M t Ht). lra.
- destruct M as (_ & _ & t & Ht & Ht0). exists t. split; [exact Ht | lra].
- destruct M as [M (t & Ht)]. exists t. split; [exact Ht|].
  pose proof (M t Ht). lra.
Qed.

Lemma mul_rev_empty :
  forall has_fma x y cx cy, valid x -> valid y ->
  Interval.classify x = Some cx -> Interval.classify y = Some cy ->
  (cx = CE \/ cy = CE \/ (cx = CZ /\ (cy = CN1 \/ cy = CP1))) ->
  Interval.mul_rev_to_pair has_fma x y = Some (Interval.EMPTY, Interval.EMPTY) /\
  forall z, ~ mul_rev x y z.
Proof.
intros has_fma x y cx cy Hx Hy Cx Cy H.
pose proof (classify_mem x cx Hx Cx) as Mx.
pose proof (classify_mem y cy Hy Cy) as My.
split.
- unfold Interval.mul_rev_to_pair. rewrite (classify2_pair _ _ _ _ Cy Cx).
  destruct H as [-> | [-> | [-> [-> | ->]]]];
    [destruct cy | destruct cx | |]; reflexivity.
- intros z (t & Ht & Htz).
  destruct H as [-> | [-> | [-> [-> | ->]]]]; cbv beta iota in Mx, My.
  + exact (Mx t Ht).
  + exact (My _ Htz).
  (* [x = [0, 0]] forces [t = 0], and [t * z = 0] is not in [y]. *)
  + apply Mx in Ht. subst t. rewrite Rmult_0_l in Htz.
    pose proof (proj1 My 0 Htz). lra.
  + apply Mx in Ht. subst t. rewrite Rmult_0_l in Htz.
    pose proof (proj1 My 0 Htz). lra.
Qed.

Lemma mul_rev_entire :
  forall has_fma x y cx cy, valid x -> valid y ->
  Interval.classify x = Some cx -> Interval.classify y = Some cy ->
  (cx = CM \/ cx = CN0 \/ cx = CP0 \/ cx = CZ) ->
  (cy = CM \/ cy = CN0 \/ cy = CP0 \/ cy = CZ) ->
  Interval.mul_rev_to_pair has_fma x y = Some (Interval.ENTIRE, Interval.EMPTY) /\
  forall z, mul_rev x y z.
Proof.
intros has_fma x y cx cy Hx Hy Cx Cy Hcx Hcy.
split.
- unfold Interval.mul_rev_to_pair. rewrite (classify2_pair _ _ _ _ Cy Cx).
  destruct Hcx as [-> | [-> | [-> | ->]]]; destruct Hcy as [-> | [-> | [-> | ->]]];
    reflexivity.
(* [t = 0] is in [x], and [0 * z = 0] is in [y]. *)
- intros z. exists 0. split.
  + exact (classify_mem0 x cx Hx Cx Hcx).
  + rewrite Rmult_0_l. exact (classify_mem0 y cy Hy Cy Hcy).
Qed.

(** If [x] is in [N1] or [P1] and [y] is not empty, or [x] is in [N0] or
    [P0] and [y] in [N1] or [P1], [mul_rev_to_pair] returns
    [[y / x, EMPTY]]. *)
Lemma mul_rev_div_eq :
  forall has_fma x y cx cy,
  Interval.classify x = Some cx -> Interval.classify y = Some cy ->
  ((cx = CN1 \/ cx = CP1) /\ cy <> CE) \/
  ((cx = CN0 \/ cx = CP0) /\ (cy = CN1 \/ cy = CP1)) ->
  Interval.mul_rev_to_pair has_fma x y =
  let* z := Interval.div has_fma y x in Some (z, Interval.EMPTY).
Proof.
intros has_fma x y cx cy Cx Cy H.
unfold Interval.mul_rev_to_pair, Interval.div.
rewrite (classify2_pair _ _ _ _ Cy Cx).
(* Each pair of classes takes the same helper in both, or [zero]. *)
destruct H as [[[-> | ->] Hy] | [[-> | ->] [-> | ->]]];
  try (destruct cy; try (exfalso; apply Hy; reflexivity)); cbv beta iota zeta;
  try reflexivity;
  match goal with
  | |- match ?e with _ => _ end = match ?e with _ => _ end => destruct e; reflexivity
  end.
Qed.

Lemma mul_rev_nz :
  forall has_fma x y cx cy, valid x -> valid y ->
  Interval.classify x = Some cx -> Interval.classify y = Some cy ->
  ((cx = CN1 \/ cx = CP1) /\ cy <> CE) \/
  ((cx = CN0 \/ cx = CP0) /\ (cy = CN1 \/ cy = CP1)) ->
  exists u, Interval.mul_rev_to_pair has_fma x y = Some (u, Interval.EMPTY) /\
    two_output (mul_rev x y) u Interval.EMPTY.
Proof.
intros has_fma x y cx cy Hx Hy Cx Cy H.
rewrite (mul_rev_div_eq has_fma x y cx cy Cx Cy H).
destruct (div_correct has_fma y x Hy Hx) as (z & Hz & Tz).
exists z. split; [rewrite Hz; reflexivity|].
apply two_output_one.
(* With [t <> 0] in [x] and [r] in [y], [r / t] is in the set, as
   [t * (r / t) = r]. *)
- assert (Hcx : cx = CN0 \/ cx = CN1 \/ cx = CP0 \/ cx = CP1)
    by (destruct H as [[[-> | ->] _] | [[-> | ->] _]]; auto).
  assert (Hcy : cy <> CE)
    by (destruct H as [[_ Hne] | [_ [-> | ->]]]; [exact Hne | discriminate | discriminate]).
  destruct (classify_nonzero x cx Hx Cx Hcx) as (t & Ht & Ht0).
  destruct (classify_nonempty y cy Hy Cy Hcy) as (r & Hr).
  exists (r / t). exists t. split; [exact Ht|].
  replace (t * (r / t)) with r by (field; exact Ht0). exact Hr.
(* The reals of [x] have one sign. *)
- apply mul_rev_convex; [exact Hx | exact Hy|].
  destruct H as [[[-> | ->] _] | [[-> | ->] _]].
  + right. apply (classify_nonpos x Hx). right. exact Cx.
  + left. apply (classify_nonneg x Hx). right. exact Cx.
  + right. apply (classify_nonpos x Hx). left. exact Cx.
  + left. apply (classify_nonneg x Hx). left. exact Cx.
(* 0 is not in [x] ([N1], [P1]) or not in [y] ([N1], [P1]), so the set is
   the image of [y × x] under [/]. *)
- apply (is_tightest_ext (image2_dom div_dom1 div_dom2 Rdiv y x)); [|exact Tz].
  intros r. symmetry. apply mul_rev_div.
  destruct H as [[Hcx _] | [_ Hcy]].
  + left. exact (classify_not_mem0 x cx Hx Cx Hcx).
  + right. exact (classify_not_mem0 y cy Hy Cy Hcy).
Qed.
