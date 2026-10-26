(** * [x * y] of intervals with an empty argument or [[0, 0]]

    [x * y] of [Interval]s dispatches on the pair of the classes of its
    arguments ([classify2_pair] in [Classify2.v]). The pairs with an empty
    class return [Interval::EMPTY] without computing, and the image of a
    box with an empty side is empty, so the empty interval is the tightest
    interval that contains it ([tightest_empty] in [AddSub.v]).

    The remaining pairs with the class [Z], that of [[0, 0]], return
    [Interval::zero()], which holds [[+0; +0]]. Its first lane is [+0], so
    its lower bound is [-0], and both bounds have the value 0, so it holds
    exactly the real 0. That makes it the tightest interval that contains
    [{0}] ([zero_tightest]): every interval that contains 0 contains it.
    The image of [[0, 0] × y] for a nonempty [y] is [{0}]: a product with a
    factor 0 is 0, and [0 * t] is in the image for a real [t] of [y]
    ([classify_nonempty]). The same holds for [x × [0, 0]]. *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 DecBinary AddSub Classes Classify2.

Open Scope R_scope.

(** ** The reals of the classes *)

(** A valid interval whose class is not [E] holds a real. *)
Lemma classify_nonempty :
  forall x c, valid x -> Interval.classify x = Some c -> c <> CE ->
  exists r, mem r x.
Proof.
intros x c Hx Hc Hne. pose proof (classify_mem x c Hx Hc) as M.
destruct c.
- exfalso. apply Hne. reflexivity.
- destruct M as [(r & Hr & _) _]. exists r. exact Hr.
- destruct M as (_ & H0 & _). exists 0. exact H0.
- destruct M as [_ Hr]. exact Hr.
- destruct M as (_ & H0 & _). exists 0. exact H0.
- destruct M as [_ Hr]. exact Hr.
- exists 0. apply M. reflexivity.
Qed.

(** ** [[0, 0]] *)

(** [Interval.zero] holds exactly the real 0: its first lane [+0] gives
    the lower bound [-0], and both bounds have the value 0. *)
Lemma mem_zero : forall r, mem r Interval.zero <-> r = 0.
Proof.
intros r. unfold mem.
cbn [Interval.zero Generic.splat zero rep fst snd opp Bopp B2R].
(* [mem] is now [0 <= r /\ r <= 0]. *)
split; [intros [H0 H1]; lra | intros ->; split; lra].
Qed.

(** [Interval.zero] is the tightest interval that contains [{0}]. *)
Lemma zero_tightest : is_tightest (fun s => s = 0) Interval.zero.
Proof.
(* It is valid: [Bleb (-0) (+0)] computes to [true], and neither [-0] nor
   [+0] is an infinity. *)
split; [right; split; [reflexivity | split; discriminate]|]. split.
- intros r ->. apply mem_zero. reflexivity.
- (* An interval that contains 0 contains every real of [Interval.zero],
     which is 0. *)
  intros z _ Hz r Hr. apply mem_zero in Hr. exact (Hz r Hr).
Qed.

(** ** The theorems *)

(** An empty argument gives the empty interval. *)
Lemma mul_empty :
  forall has_fma x y cx cy, valid x -> valid y ->
  Interval.classify x = Some cx -> Interval.classify y = Some cy ->
  cx = CE \/ cy = CE ->
  exists z, Interval.mul has_fma x y = Some z /\ is_tightest (image2 Rmult x y) z.
Proof.
intros has_fma x y cx cy Hx Hy Ecx Ecy Hc. exists Interval.EMPTY. split.
- (* Every pair with [E] on either side returns [EMPTY]. *)
  unfold Interval.mul. rewrite (classify2_pair x y cx cy Ecx Ecy).
  destruct Hc as [->| ->]; [destruct cy | destruct cx]; reflexivity.
- apply tightest_empty, image2_empty.
  destruct Hc as [->| ->]; [left | right];
    [exact (classify_mem x CE Hx Ecx) | exact (classify_mem y CE Hy Ecy)].
Qed.

(** [[0, 0]] times a nonempty interval, or a nonempty interval times
    [[0, 0]], gives [[0, 0]]. *)
Lemma mul_zero :
  forall has_fma x y cx cy, valid x -> valid y ->
  Interval.classify x = Some cx -> Interval.classify y = Some cy ->
  (cx = CZ /\ cy <> CE) \/ (cy = CZ /\ cx <> CE) ->
  exists z, Interval.mul has_fma x y = Some z /\ is_tightest (image2 Rmult x y) z.
Proof.
intros has_fma x y cx cy Hx Hy Ecx Ecy Hc. exists Interval.zero. split.
- (* Every pair with [Z] on one side and not [E] on the other returns
     [zero]. *)
  unfold Interval.mul. rewrite (classify2_pair x y cx cy Ecx Ecy).
  destruct Hc as [[-> H]|[-> H]]; [destruct cy | destruct cx];
    solve [reflexivity | exfalso; apply H; reflexivity].
- apply (is_tightest_ext (fun s => s = 0)); [|exact zero_tightest].
  (* The image is [{0}]: a factor is 0, and the other factor can be any
     real of the other side, which has one. *)
  intros s. destruct Hc as [[-> H]|[-> H]].
  + pose proof (classify_mem x CZ Hx Ecx) as Mx.
    destruct (classify_nonempty y cy Hy Ecy H) as (t & Ht). split.
    * intros ->. exists 0, t.
      split; [apply Mx; reflexivity|]. split; [exact Ht | ring].
    * intros (r & t' & Hr & _ & ->). apply Mx in Hr. subst r. ring.
  + pose proof (classify_mem y CZ Hy Ecy) as My.
    destruct (classify_nonempty x cx Hx Ecx H) as (r & Hr). split.
    * intros ->. exists r, 0.
      split; [exact Hr|]. split; [apply My; reflexivity | ring].
    * intros (r' & t & _ & Ht & ->). apply My in Ht. subst t. ring.
Qed.
