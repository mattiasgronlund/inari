(** * Decorations of operations on three intervals

    [DecInterval::mul_add] calls [set_dec] with the result [w] of
    [Interval::mul_add] on the bare intervals [x], [y] and [z] and the
    minimum [e] of their decorations, unless an argument is NaI.
    [set_dec_correct3] shows that this decorates [w] as IEEE 1788 asks, for
    any function [h] of three reals that is continuous at each point of R³,
    if [w] is the tightest interval that contains the image of the box
    [x × y × z] under [h], as [set_dec_correct] in [DecBinary.v] does for
    two reals, and with the same argument: the strongest decoration is
    [trv] if the box is empty, [com] if [x], [y], [z] and [w] are nonempty
    and bounded, and [dac] otherwise. It takes as a hypothesis that [e] is
    [com] only if a nonempty box whose image is bounded is bounded too. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer Sign DecBinary.

Open Scope R_scope.

Lemma image3_mem :
  forall h x y z r t u, mem r x -> mem t y -> mem u z -> image3 h x y z (h r t u).
Proof.
intros h x y z r t u Hr Ht Hu. exists r, t, u.
split; [exact Hr|]. split; [exact Ht|]. split; [exact Hu | reflexivity].
Qed.

Lemma image3_empty :
  forall h x y z,
  (forall r, ~ mem r x) \/ (forall t, ~ mem t y) \/ (forall u, ~ mem u z) ->
  forall s, ~ image3 h x y z s.
Proof.
intros h x y z H s (r & t & u & Hr & Ht & Hu & _).
destruct H as [H|[H|H]]; [exact (H r Hr) | exact (H t Ht) | exact (H u Hu)].
Qed.

(** ** The strongest decoration on a box *)

Lemma strongest3_Trv :
  forall h x y z w,
  (forall r, ~ mem r x) \/ (forall t, ~ mem t y) \/ (forall u, ~ mem u z) ->
  strongest3 Trv h x y z w.
Proof.
intros h x y z w H. split; [exact I|].
(* Each decoration above [trv] asks for a nonempty box. *)
assert (Hne :
  ~ ((exists r, mem r x) /\ (exists t, mem t y) /\ (exists u, mem u z))).
{ intros ((r & Hr) & (t & Ht) & (u & Hu)).
  destruct H as [H|[H|H]]; [exact (H r Hr) | exact (H t Ht) | exact (H u Hu)]. }
intros [] He; cbn [discriminant]; try lia; exfalso; apply Hne;
  cbn [p3] in He.
- exact He.
- destruct He as (Hx & Hy & Hz & _). split; [|split]; assumption.
- destruct He as (Hx & Hy & Hz & _). split; [|split]; assumption.
Qed.

Lemma strongest3_Dac :
  forall h x y z w, p3 Dac h x y z w -> ~ p3 Com h x y z w -> strongest3 Dac h x y z w.
Proof.
intros h x y z w Hd Hc. split; [exact Hd|].
intros [] He; cbn [discriminant]; try lia. exfalso. exact (Hc He).
Qed.

Lemma strongest3_Com :
  forall h x y z w, p3 Com h x y z w -> strongest3 Com h x y z w.
Proof.
intros h x y z w Hc. split; [exact Hc|].
intros [] _; cbn [discriminant]; lia.
Qed.

(** ** A continuous function of three reals *)

Section Ternary.

(** [h] is continuous at each point of R³. *)
Variable h : R -> R -> R -> R.

Hypothesis h_continuous : forall r t u, continuity3_pt h r t u.

(** The restriction of [h] to any box is continuous, as [h] is. *)
Lemma p3_Dac_continuous :
  forall x y z w, (exists r, mem r x) -> (exists t, mem t y) -> (exists u, mem u z) ->
  p3 Dac h x y z w.
Proof using h_continuous.
intros x y z w Hx Hy Hz. split; [exact Hx|]. split; [exact Hy|].
split; [exact Hz|].
intros r t u _ _ _ eps Heps.
destruct (h_continuous r t u eps Heps) as (delta & Hd & H).
exists delta. split; [exact Hd|].
intros r' t' u' _ _ _. exact (H r' t' u' I I I).
Qed.

(** [set_dec] keeps the tightest interval [w] that contains the image of
    [x × y × z], and decorates it as IEEE 1788 asks, if [e] is [com] only
    when a nonempty box with a bounded image is bounded. *)
Theorem set_dec_correct3 :
  forall x y z w e, valid x -> valid y -> valid z -> e <> Ill ->
  is_tightest (image3 h x y z) w ->
  (e = Com -> (exists r, mem r x) -> (exists t, mem t y) -> (exists u, mem u z) ->
   bounded (image3 h x y z) ->
   bounded (fun r => mem r x) /\ bounded (fun t => mem t y) /\
   bounded (fun u => mem u z)) ->
  itv (DecInterval.set_dec w e) = w /\
  exists d, strongest3 d h x y z w /\
    dec (DecInterval.set_dec w e) = dec_min d e.
Proof using h_continuous.
intros x y z w e Hx Hy Hz He Hw Hc.
destruct (Interval.is_empty x || Interval.is_empty y || Interval.is_empty z)
  eqn:Exyz.
- (* The image of an empty box is empty, and so is [w]. *)
  assert (N : (forall r, ~ mem r x) \/ (forall t, ~ mem t y) \/
              (forall u, ~ mem u z)).
  { apply Bool.orb_true_iff in Exyz. destruct Exyz as [Exy|E].
    - apply Bool.orb_true_iff in Exy.
      destruct Exy as [E|E]; [left | right; left]; intros r; now apply mem_empty.
    - right; right; intros r; now apply mem_empty. }
  pose proof (no_mem_empty w (proj1 Hw)
    (tightest_no_mem _ _ Hw (image3_empty h x y z N))) as Ew.
  rewrite (set_dec_empty_any w e Ew He). cbn [itv dec DecInterval.EMPTY].
  split; [symmetry; exact (valid_empty_eq w (proj1 Hw) Ew)|].
  exists Trv.
  split; [now apply strongest3_Trv | symmetry; now apply dec_min_Trv_l].
- apply Bool.orb_false_iff in Exyz. destruct Exyz as [Exy Ez].
  apply Bool.orb_false_iff in Exy. destruct Exy as [Ex Ey].
  destruct (nonempty_mem x Hx Ex) as (r & Hr).
  destruct (nonempty_mem y Hy Ey) as (t & Ht).
  destruct (nonempty_mem z Hz Ez) as (u & Hu).
  (* [h r t u] is in the image, and so in [w]. *)
  assert (Ew : Interval.is_empty w = false).
  { apply (mem_not_empty _ (h r t u) (proj1 Hw)).
    apply (proj1 (proj2 Hw)). now apply image3_mem. }
  assert (Hdac : p3 Dac h x y z w).
  { apply p3_Dac_continuous; [exists r | exists t | exists u]; assumption. }
  destruct (Interval.is_common_interval w) eqn:Cw.
  + rewrite (set_dec_keep w e Ew He (fun _ => Cw)).
    cbn [itv dec DecInterval.new_unchecked]. split; [reflexivity|].
    pose proof (common_bounded w Cw) as Bw.
    destruct (Interval.is_common_interval x && Interval.is_common_interval y &&
              Interval.is_common_interval z) eqn:C.
    * (* A bounded box and a bounded [w]. *)
      apply andb_prop in C. destruct C as [Cxy Cz].
      apply andb_prop in Cxy. destruct Cxy as [Cx Cy].
      exists Com. split; [|symmetry; apply dec_min_Com_l].
      apply strongest3_Com.
      split; [exists r; exact Hr|]. split; [exists t; exact Ht|].
      split; [exists u; exact Hu|].
      split; [now apply common_bounded|]. split; [now apply common_bounded|].
      split; [now apply common_bounded|].
      split; [intros r' t' u' _ _ _; apply h_continuous | exact Bw].
    * (* An unbounded box: [x], [y] or [z] is not common, so not bounded,
         as it is nonempty. The image is in [w], so it is bounded, and [e]
         is not [com]. *)
      assert (Hnb :
        ~ (bounded (fun r => mem r x) /\ bounded (fun t => mem t y) /\
           bounded (fun u => mem u z))).
      { intros (Bx & By & Bz).
        rewrite (bounded_common x Hx Ex Bx), (bounded_common y Hy Ey By),
          (bounded_common z Hz Ez Bz) in C.
        discriminate C. }
      assert (Hnc : e <> Com).
      { intros E. apply Hnb, Hc; [exact E | exists r; exact Hr |
          exists t; exact Ht | exists u; exact Hu |].
        destruct Bw as (m & Hm). exists m. intros s Hs.
        apply Hm, (proj1 (proj2 Hw)), Hs. }
      exists Dac. split; [|symmetry; now apply dec_min_Dac_l].
      apply strongest3_Dac; [exact Hdac|].
      intros (_ & _ & _ & Bx & By & Bz & _).
      exact (Hnb (conj Bx (conj By Bz))).
  + (* [w] is not common, so not bounded, as it is nonempty. *)
    rewrite (set_dec_lower w e Ew Cw He).
    cbn [itv dec DecInterval.new_unchecked]. split; [reflexivity|].
    exists Dac. split; [|reflexivity].
    apply strongest3_Dac; [exact Hdac|].
    intros (_ & _ & _ & _ & _ & _ & _ & Bw).
    rewrite (bounded_common w (proj1 Hw) Ew Bw) in Cw. discriminate Cw.
Qed.

End Ternary.
