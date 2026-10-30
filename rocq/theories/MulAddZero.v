(** * [mul_add] of intervals with an empty argument or a factor [[0, 0]]

    [x.mul_add(y, z)] returns the empty interval if [z] is empty, before it
    classifies [x] and [y] ([mul_add_addend_empty]), and if [x] or [y] is
    empty ([mul_add_empty]): the image of a box with an empty side is empty.
    If [x] or [y] is [[0, 0]] and the other is nonempty, it returns [z]
    itself ([mul_add_zero]): every product is 0, so the image is the set of
    reals of [z], whose tightest interval is [z] ([tightest_self]). *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer DecBinary AddSub Classify2 Classes
  MulZero DecTernary.

Open Scope R_scope.

(** A [valid] interval is the tightest interval that contains its reals. *)
Lemma tightest_self : forall z, valid z -> is_tightest (fun s => mem s z) z.
Proof.
intros z Hz. split; [exact Hz|]. split.
- intros r Hr. exact Hr.
- intros w _ Hw r Hr. exact (Hw r Hr).
Qed.

(** An empty [z] gives the empty interval. *)
Lemma mul_add_addend_empty :
  forall has_fma x y z, valid z -> Interval.is_empty z = true ->
  exists w, Interval.mul_add has_fma x y z = Some w /\ is_tightest (image3 Rfma x y z) w.
Proof.
intros has_fma x y z Hz Ez. exists Interval.EMPTY. split.
- (* The test of [z] comes before the classification of [x] and [y]. *)
  unfold Interval.mul_add. rewrite Ez. reflexivity.
- apply tightest_empty, image3_empty. right; right.
  intros u. exact (mem_empty z u Hz Ez).
Qed.

(** An empty [x] or [y] gives the empty interval. *)
Lemma mul_add_empty :
  forall has_fma x y z cx cy, valid x -> valid y -> Interval.is_empty z = false ->
  Interval.classify x = Some cx -> Interval.classify y = Some cy ->
  cx = CE \/ cy = CE ->
  exists w, Interval.mul_add has_fma x y z = Some w /\ is_tightest (image3 Rfma x y z) w.
Proof.
intros has_fma x y z cx cy Hx Hy Ez Ecx Ecy Hc. exists Interval.EMPTY. split.
- (* Past the test of [z], every pair with [E] on either side returns
     [EMPTY], as in [x * y]. *)
  unfold Interval.mul_add. rewrite Ez, (classify2_pair x y cx cy Ecx Ecy).
  destruct Hc as [->| ->]; [destruct cy | destruct cx]; reflexivity.
- apply tightest_empty, image3_empty.
  destruct Hc as [->| ->]; [left | right; left];
    [exact (classify_mem x CE Hx Ecx) | exact (classify_mem y CE Hy Ecy)].
Qed.

(** [[0, 0]] and a nonempty interval, in either order, give [z]. *)
Lemma mul_add_zero :
  forall has_fma x y z cx cy, valid x -> valid y -> valid z ->
  Interval.is_empty z = false ->
  Interval.classify x = Some cx -> Interval.classify y = Some cy ->
  (cx = CZ /\ cy <> CE) \/ (cy = CZ /\ cx <> CE) ->
  exists w, Interval.mul_add has_fma x y z = Some w /\ is_tightest (image3 Rfma x y z) w.
Proof.
intros has_fma x y z cx cy Hx Hy Hz Ez Ecx Ecy Hc. exists z. split.
- (* Past the test of [z], every pair with [Z] on one side and not [E] on
     the other returns [addend]. *)
  unfold Interval.mul_add. rewrite Ez, (classify2_pair x y cx cy Ecx Ecy).
  destruct Hc as [[-> H]|[-> H]]; [destruct cy | destruct cx];
    solve [reflexivity | exfalso; apply H; reflexivity].
- apply (is_tightest_ext (fun s => mem s z)); [|exact (tightest_self z Hz)].
  (* The image is the set of reals of [z]: a factor is 0, so [r * t + u]
     is [u], and the other factor can be any real of the other side, which
     has one. *)
  intros s. destruct Hc as [[-> H]|[-> H]].
  + pose proof (classify_mem x CZ Hx Ecx) as Mx.
    destruct (classify_nonempty y cy Hy Ecy H) as (t & Ht). split.
    * intros Hs. exists 0, t, s.
      split; [apply Mx; reflexivity|]. split; [exact Ht|]. split; [exact Hs|].
      unfold Rfma. ring.
    * intros (r & t' & u & Hr & _ & Hu & ->). apply Mx in Hr. subst r.
      cbv beta. unfold Rfma. rewrite Rmult_0_l, Rplus_0_l. exact Hu.
  + pose proof (classify_mem y CZ Hy Ecy) as My.
    destruct (classify_nonempty x cx Hx Ecx H) as (r & Hr). split.
    * intros Hs. exists r, 0, s.
      split; [exact Hr|]. split; [apply My; reflexivity|]. split; [exact Hs|].
      unfold Rfma. ring.
    * intros (r' & t & u & _ & Ht & Hu & ->). apply My in Ht. subst t.
      cbv beta. unfold Rfma. rewrite Rmult_0_r, Rplus_0_l. exact Hu.
Qed.
