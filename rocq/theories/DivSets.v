(** * The sets of numerators and denominators of [x / y] and [recip x]

    [x = [a, b]] is stored as [[-a; b]]. The image of [x × y] under [/] is
    the set of [r / t] for [r] in [x] and [t <> 0] in [y]. If every real of
    [y] is at least 0, these are the quotients [quot] of the reals of [x]
    ([Up]) and the reals of [y] above 0 ([Qp]), and the negated quotients
    are those of the negated reals of [x] ([Um]), as [-(r / t) = (-r) / t].
    If every real of [y] is at most 0, [r / t = (-r) / (-t)], so the
    quotients are those of [Um] and the negated reals of [y] above 0
    ([Qn]), and the negated ones those of [Up] and [Qn] ([div_image_P] and
    [div_image_N]). The image of [x] under [recip] is the same with the
    numerators [{1}] or [{-1}] ([recip_image_P] and [recip_image_N]).

    The lanes of [x] and [y] hold the bounds of these sets, by their
    classes ([classify_lanes], [classify_mem] and [lanes_tight]):
    - [x] in [M] ([a < 0 < b]): [Up] and [Um] each have an element above 0,
      and the largest elements [b] and [-a] (or +inf) in the second and the
      first lane ([xset_M]).
    - [x] in [N0] or [N1] ([a < 0], [b <= 0]): [Up] has the largest element
      [b <= 0], the second lane, and [Um] is as for [M] ([xset_N]).
    - [x] in [P0] or [P1] ([0 <= a], [0 < b]): [Um] has the largest
      element [-a <= 0], the first lane, and [Up] is as for [M]
      ([xset_P]).
    - [y] in [P1] ([0 < c]): [Qp] has the least element [c], the negated
      first lane, and the largest [d] (or +inf), the second lane
      ([yset_P1]).
    - [y] in [P0] ([c = 0]): [Qp] has elements as close to 0 as asked, and
      the largest [d] (or +inf) ([yset_P0]).
    - [y] in [N1] and [N0]: the same for [Qn], with [-d] and [-c]
      ([yset_N1] and [yset_N0]).

    [div_tightest_P], [div_tightest_N], [recip_tightest_P] and
    [recip_tightest_N] combine the image rewriting with
    [tightest_lanes_lub] in [DivTight.v]. *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer Sign MaxMin DecBinary AddSub
  Classes MulTight MulNP DivTight.

Open Scope R_scope.

(** ** The sets *)

(** The reals of [x] and their negations, as numerators. *)
Definition Up (x : Interval) : R -> Prop := fun u => mem u x.
Definition Um (x : Interval) : R -> Prop := fun u => mem (- u) x.

(** The reals of [y] above 0, and the negations of the reals of [y] below
    0, as denominators. *)
Definition Qp (y : Interval) : R -> Prop := fun q => mem q y /\ 0 < q.
Definition Qn (y : Interval) : R -> Prop := fun q => mem (- q) y /\ 0 < q.

(** ** The numerators by the class of [x] *)

Lemma xset_M :
  forall x, valid x -> Interval.classify x = Some CM ->
  pos_set (Up x) (snd (rep x)) /\ pos_set (Um x) (fst (rep x)).
Proof.
intros x Hx Cx.
pose proof (classify_lanes x _ Hx Cx) as L.
pose proof (classify_mem x _ Hx Cx) as M. cbv beta iota in L, M.
destruct L as (P0 & P1), M as ((rn & Hrn & Hrnn) & (rp & Hrp & Hrpp)).
destruct (lanes_tight x Hx (not_nan_upper _ (pos_lane_upper _ P0)))
  as (_ & _ & _ & T0 & T1).
split.
- split; [exact P1|]. split; [exact T1|].
  exists rp. split; [exact Hrp | exact Hrpp].
- split; [exact P0|]. split; [exact T0|].
  (* [-rn] is above 0, and its negation [rn] is in [x]. *)
  exists (- rn). unfold Um. rewrite Ropp_involutive. split; [exact Hrn | lra].
Qed.

Lemma xset_N :
  forall x, valid x ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  nonpos_set (Up x) (snd (rep x)) /\ pos_set (Um x) (fst (rep x)).
Proof.
intros x Hx Cx.
(* Both classes say that the first lane is above 0, that the second is a
   float at most 0, and that [x] has a real below 0. *)
assert (H : pos_lane (fst (rep x)) /\ is_finite (snd (rep x)) = true /\
            B2R (snd (rep x)) <= 0 /\ exists r, mem r x /\ r < 0).
{ destruct Cx as [Cx|Cx];
    pose proof (classify_lanes x _ Hx Cx) as L;
    pose proof (classify_mem x _ Hx Cx) as M; cbv beta iota in L, M.
  - destruct L as (P0 & F1 & E1), M as (_ & _ & N).
    split; [exact P0|]. split; [exact F1|]. split; [lra | exact N].
  - destruct L as (P0 & F1 & N1), M as (Neg & r & Hr).
    split; [exact P0|]. split; [exact F1|]. split; [lra|].
    exists r. split; [exact Hr | exact (Neg r Hr)]. }
destruct H as (P0 & F1 & N1 & r0 & Hr0 & Hr0n).
destruct (lanes_tight x Hx (not_nan_upper _ (pos_lane_upper _ P0)))
  as (_ & _ & _ & T0 & T1).
(* The second lane is finite, so it is the largest real [b] of [x]. *)
rewrite (bound_finite _ F1) in T1.
destruct (proj1 (tight_Some _ _) T1) as [Hb Hbmax].
split.
- split; [exact F1|]. split; [exact Hb|]. split; [exact Hbmax | exact N1].
- split; [exact P0|]. split; [exact T0|].
  exists (- r0). unfold Um. rewrite Ropp_involutive. split; [exact Hr0 | lra].
Qed.

Lemma xset_P :
  forall x, valid x ->
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  pos_set (Up x) (snd (rep x)) /\ nonpos_set (Um x) (fst (rep x)).
Proof.
intros x Hx Cx.
(* Both classes say that the first lane is a float at most 0, that the
   second is above 0, and that [x] has a real above 0. *)
assert (H : is_finite (fst (rep x)) = true /\ B2R (fst (rep x)) <= 0 /\
            pos_lane (snd (rep x)) /\ exists r, mem r x /\ 0 < r).
{ destruct Cx as [Cx|Cx];
    pose proof (classify_lanes x _ Hx Cx) as L;
    pose proof (classify_mem x _ Hx Cx) as M; cbv beta iota in L, M.
  - destruct L as (F0 & E0 & P1), M as (_ & _ & Pos).
    split; [exact F0|]. split; [lra|]. split; [exact P1 | exact Pos].
  - destruct L as (F0 & N0 & P1), M as (Pos & r & Hr).
    split; [exact F0|]. split; [lra|]. split; [exact P1|].
    exists r. split; [exact Hr | exact (Pos r Hr)]. }
destruct H as (F0 & N0 & P1 & r0 & Hr0 & Hr0p).
destruct (lanes_tight x Hx (not_nan_upper _ (or_introl F0)))
  as (_ & _ & _ & T0 & T1).
(* The first lane is finite, so it is the largest negation [-a] of a real
   of [x]. *)
rewrite (bound_finite _ F0) in T0.
destruct (proj1 (tight_Some _ _) T0) as [Ha Hamax].
split.
- split; [exact P1|]. split; [exact T1|].
  exists r0. split; [exact Hr0 | exact Hr0p].
- split; [exact F0|]. split; [exact Ha|]. split; [exact Hamax | exact N0].
Qed.

(** The numerators [{1}] and [{-1}] of [recip], where [Interval::recip]
    stores [-1.0] as [opp one]. *)
Lemma one_pos_set : pos_set (fun u => u = 1) one.
Proof.
destruct one_B2R as [F E].
split; [right; split; [exact F | lra]|].
split.
- (* The lane is finite, so it is the largest element 1 of [{1}]. *)
  rewrite (bound_finite _ F), E. apply (proj2 (tight_Some _ _)).
  split; [reflexivity | intros r Hr; lra].
- exists 1. split; [reflexivity | lra].
Qed.

Lemma one_nonpos_set : nonpos_set (fun u => u = -1) (opp one).
Proof.
destruct one_B2R as [F E].
assert (E' : B2R (opp one) = -1) by (rewrite B2R_opp; lra).
unfold nonpos_set. cbv beta.
split; [rewrite is_finite_opp; exact F|].
split; [exact E'|].
split; [intros r Hr; lra | lra].
Qed.

(** ** The denominators by the class of [y] *)

Lemma yset_P1 :
  forall y, valid y -> Interval.classify y = Some CP1 ->
  is_finite (fst (rep y)) = true /\ den_min (Qp y) (- B2R (fst (rep y))) /\
  den_sup (Qp y) (snd (rep y)).
Proof.
intros y Hy Cy.
pose proof (classify_lanes y _ Hy Cy) as L.
pose proof (classify_mem y _ Hy Cy) as M. cbv beta iota in L, M.
destruct L as (F0 & N0 & P1), M as (Pos & r0 & Hr0).
destruct (lanes_tight y Hy (not_nan_upper _ (or_introl F0)))
  as (_ & _ & _ & T0 & T1).
(* The first lane is finite, so it is the largest negation [-c] of a real
   of [y]. *)
rewrite (bound_finite _ F0) in T0.
destruct (proj1 (tight_Some _ _) T0) as [Hc Hcmax].
split; [exact F0|]. split.
- (* [c] is the least real of [y], and above 0. *)
  split; [split; [exact Hc | lra]|]. split; [lra|].
  intros q [Hq _].
  assert (Hq' : mem (- - q) y) by (rewrite Ropp_involutive; exact Hq).
  specialize (Hcmax _ Hq'). lra.
- (* Every real of [y] is above 0, so [Qp y] has the largest real [d] of
     [y], or +inf. *)
  split; [exact P1|]. split.
  + exact (tight_pos _ _ T1 (ex_intro _ r0 (conj Hr0 (Pos r0 Hr0)))).
  + split; [exists r0; split; [exact Hr0 | exact (Pos r0 Hr0)]|].
    intros q [_ Hq]. exact Hq.
Qed.

Lemma yset_P0 :
  forall y, valid y -> Interval.classify y = Some CP0 ->
  den_near0 (Qp y) /\ den_sup (Qp y) (snd (rep y)).
Proof.
intros y Hy Cy.
pose proof (classify_lanes y _ Hy Cy) as L.
pose proof (classify_mem y _ Hy Cy) as M. cbv beta iota in L, M.
destruct L as (F0 & _ & P1), M as (_ & H0 & r0 & Hr0 & Hr0p).
destruct (lanes_tight y Hy (not_nan_upper _ (or_introl F0)))
  as (_ & _ & _ & _ & T1).
split.
- split; [intros q [_ Hq]; exact Hq|].
  (* [min(eps, r0)] is above 0 and at most [r0], so it is in [y] with 0
     and [r0]. *)
  intros eps Heps. exists (Rmin eps r0).
  pose proof (Rmin_l eps r0) as Ml. pose proof (Rmin_r eps r0) as Mr.
  assert (Hm : 0 < Rmin eps r0) by (apply Rmin_glb_lt; lra).
  split; [|exact Ml]. split; [|exact Hm].
  apply (mem_between y 0 r0); [exact Hy | exact H0 | exact Hr0 | split; lra].
- split; [exact P1|]. split.
  + exact (tight_pos _ _ T1 (ex_intro _ r0 (conj Hr0 Hr0p))).
  + split; [exists r0; split; [exact Hr0 | exact Hr0p]|].
    intros q [_ Hq]. exact Hq.
Qed.

Lemma yset_N1 :
  forall y, valid y -> Interval.classify y = Some CN1 ->
  is_finite (snd (rep y)) = true /\ den_min (Qn y) (- B2R (snd (rep y))) /\
  den_sup (Qn y) (fst (rep y)).
Proof.
intros y Hy Cy.
pose proof (classify_lanes y _ Hy Cy) as L.
pose proof (classify_mem y _ Hy Cy) as M. cbv beta iota in L, M.
destruct L as (P0 & F1 & N1), M as (Neg & r0 & Hr0).
destruct (lanes_tight y Hy (not_nan_upper _ (pos_lane_upper _ P0)))
  as (_ & _ & _ & T0 & T1).
(* The second lane is finite, so it is the largest real [d] of [y]. *)
rewrite (bound_finite _ F1) in T1.
destruct (proj1 (tight_Some _ _) T1) as [Hd Hdmax].
(* [-r0] is above 0, and its negation is in [y]. *)
assert (Hr0' : mem (- - r0) y /\ 0 < - r0).
{ pose proof (Neg r0 Hr0). rewrite Ropp_involutive. split; [exact Hr0 | lra]. }
split; [exact F1|]. split.
- (* [-d] is the least negation of a real of [y], and above 0. *)
  split; [split; [rewrite Ropp_involutive; exact Hd | lra]|]. split; [lra|].
  intros q [Hq _]. specialize (Hdmax _ Hq). lra.
- split; [exact P0|]. split.
  + exact (tight_pos _ _ T0 (ex_intro _ (- r0) Hr0')).
  + split; [exists (- r0); exact Hr0'|].
    intros q [_ Hq]. exact Hq.
Qed.

Lemma yset_N0 :
  forall y, valid y -> Interval.classify y = Some CN0 ->
  den_near0 (Qn y) /\ den_sup (Qn y) (fst (rep y)).
Proof.
intros y Hy Cy.
pose proof (classify_lanes y _ Hy Cy) as L.
pose proof (classify_mem y _ Hy Cy) as M. cbv beta iota in L, M.
destruct L as (P0 & _ & _), M as (_ & H0 & r0 & Hr0 & Hr0n).
destruct (lanes_tight y Hy (not_nan_upper _ (pos_lane_upper _ P0)))
  as (_ & _ & _ & T0 & _).
assert (Hr0' : mem (- - r0) y /\ 0 < - r0).
{ rewrite Ropp_involutive. split; [exact Hr0 | lra]. }
split.
- split; [intros q [_ Hq]; exact Hq|].
  (* [-min(eps, -r0)] is below 0 and at least [r0], so it is in [y] with
     [r0] and 0. *)
  intros eps Heps. exists (Rmin eps (- r0)).
  pose proof (Rmin_l eps (- r0)) as Ml. pose proof (Rmin_r eps (- r0)) as Mr.
  assert (Hm : 0 < Rmin eps (- r0)) by (apply Rmin_glb_lt; lra).
  split; [|exact Ml]. split; [|exact Hm].
  apply (mem_between y r0 0); [exact Hy | exact Hr0 | exact H0 | split; lra].
- split; [exact P0|]. split.
  + exact (tight_pos _ _ T0 (ex_intro _ (- r0) Hr0')).
  + split; [exists (- r0); exact Hr0'|].
    intros q [_ Hq]. exact Hq.
Qed.

(** The reals of an interval in [P0] or [P1] are at least 0, and those of
    one in [N0] or [N1] at most 0. *)
Lemma classify_nonneg :
  forall y, valid y ->
  (Interval.classify y = Some CP0 \/ Interval.classify y = Some CP1) ->
  forall t, mem t y -> 0 <= t.
Proof.
intros y Hy [Cy|Cy] t Ht;
  pose proof (classify_mem y _ Hy Cy) as M; cbv beta iota in M.
- destruct M as (Nonneg & _). exact (Nonneg t Ht).
- destruct M as (Pos & _). pose proof (Pos t Ht). lra.
Qed.

Lemma classify_nonpos :
  forall y, valid y ->
  (Interval.classify y = Some CN0 \/ Interval.classify y = Some CN1) ->
  forall t, mem t y -> t <= 0.
Proof.
intros y Hy [Cy|Cy] t Ht;
  pose proof (classify_mem y _ Hy Cy) as M; cbv beta iota in M.
- destruct M as (Nonpos & _). exact (Nonpos t Ht).
- destruct M as (Neg & _). pose proof (Neg t Ht). lra.
Qed.

(** ** The images *)

(** A divisor of one sign that is not 0 has that sign strictly. *)
Lemma nonneg_nonzero : forall t, 0 <= t -> t <> 0 -> 0 < t.
Proof.
intros t H1 H2. destruct (Rle_lt_or_eq_dec 0 t H1) as [H|H]; [exact H|].
exfalso. apply H2. symmetry. exact H.
Qed.

Lemma nonpos_nonzero : forall t, t <= 0 -> t <> 0 -> t < 0.
Proof.
intros t H1 H2. destruct (Rle_lt_or_eq_dec t 0 H1) as [H|H]; [exact H|].
exfalso. apply H2. exact H.
Qed.

Lemma div_image_P :
  forall x y, (forall t, mem t y -> 0 <= t) ->
  (forall s, image2_dom div_dom1 div_dom2 Rdiv x y s <-> quot (Up x) (Qp y) s) /\
  (forall s, image2_dom div_dom1 div_dom2 Rdiv x y (- s) <-> quot (Um x) (Qp y) s).
Proof.
intros x y Hy. split; intros s; split.
- intros (r & t & Hr & Ht & _ & Ht0 & ->).
  exists r, t. split; [exact Hr|].
  split; [split; [exact Ht | exact (nonneg_nonzero t (Hy t Ht) Ht0)] | reflexivity].
- intros (u & q & Hu & [Hq Hqp] & ->).
  exists u, q. split; [exact Hu|]. split; [exact Hq|]. split; [exact I|].
  split; [intros E; lra | reflexivity].
- intros (r & t & Hr & Ht & _ & Ht0 & E).
  exists (- r), t. split; [unfold Um; rewrite Ropp_involutive; exact Hr|].
  split; [split; [exact Ht | exact (nonneg_nonzero t (Hy t Ht) Ht0)]|].
  (* [s = -(r / t) = (-r) / t]. *)
  assert (E' : - r / t = - (r / t)) by (unfold Rdiv; ring).
  lra.
- intros (u & q & Hu & [Hq Hqp] & ->).
  exists (- u), q. split; [exact Hu|]. split; [exact Hq|]. split; [exact I|].
  split; [intros E; lra|].
  unfold Rdiv; ring.
Qed.

Lemma div_image_N :
  forall x y, (forall t, mem t y -> t <= 0) ->
  (forall s, image2_dom div_dom1 div_dom2 Rdiv x y s <-> quot (Um x) (Qn y) s) /\
  (forall s, image2_dom div_dom1 div_dom2 Rdiv x y (- s) <-> quot (Up x) (Qn y) s).
Proof.
intros x y Hy. split; intros s; split.
- intros (r & t & Hr & Ht & _ & Ht0 & ->).
  pose proof (nonpos_nonzero t (Hy t Ht) Ht0) as Htn.
  exists (- r), (- t). split; [unfold Um; rewrite Ropp_involutive; exact Hr|].
  split; [split; [rewrite Ropp_involutive; exact Ht | lra]|].
  (* [r / t = (-r) / (-t)]. *)
  unfold Rdiv; rewrite Rinv_opp; ring.
- intros (u & q & Hu & [Hq Hqp] & ->).
  exists (- u), (- q). split; [exact Hu|]. split; [exact Hq|]. split; [exact I|].
  split; [intros E; lra|].
  unfold Rdiv; rewrite Rinv_opp; ring.
- intros (r & t & Hr & Ht & _ & Ht0 & E).
  pose proof (nonpos_nonzero t (Hy t Ht) Ht0) as Htn.
  exists r, (- t). split; [exact Hr|].
  split; [split; [rewrite Ropp_involutive; exact Ht | lra]|].
  (* [s = -(r / t) = r / (-t)]. *)
  assert (E' : r / - t = - (r / t)) by (unfold Rdiv; rewrite Rinv_opp; ring).
  lra.
- intros (u & q & Hu & [Hq Hqp] & ->).
  exists u, (- q). split; [exact Hu|]. split; [exact Hq|]. split; [exact I|].
  split; [intros E; lra|].
  unfold Rdiv; rewrite Rinv_opp; ring.
Qed.

Lemma recip_image_P :
  forall x, (forall r, mem r x -> 0 <= r) ->
  (forall s, image_dom recip_dom Rinv x s <-> quot (fun u => u = 1) (Qp x) s) /\
  (forall s, image_dom recip_dom Rinv x (- s) <-> quot (fun u => u = -1) (Qp x) s).
Proof.
intros x Hx. split; intros s; split.
- intros (r & Hr & Hr0 & ->).
  exists 1, r. split; [reflexivity|].
  split; [split; [exact Hr | exact (nonneg_nonzero r (Hx r Hr) Hr0)]|].
  unfold Rdiv; ring.
- intros (u & q & -> & [Hq Hqp] & ->).
  exists q. split; [exact Hq|]. split; [intros E; lra|].
  unfold Rdiv; ring.
- intros (r & Hr & Hr0 & E).
  exists (-1), r. split; [reflexivity|].
  split; [split; [exact Hr | exact (nonneg_nonzero r (Hx r Hr) Hr0)]|].
  (* [s = -(1 / r) = (-1) / r]. *)
  assert (E' : -1 / r = - / r) by (unfold Rdiv; ring).
  lra.
- intros (u & q & -> & [Hq Hqp] & ->).
  exists q. split; [exact Hq|]. split; [intros E; lra|].
  unfold Rdiv; ring.
Qed.

Lemma recip_image_N :
  forall x, (forall r, mem r x -> r <= 0) ->
  (forall s, image_dom recip_dom Rinv x s <-> quot (fun u => u = -1) (Qn x) s) /\
  (forall s, image_dom recip_dom Rinv x (- s) <-> quot (fun u => u = 1) (Qn x) s).
Proof.
intros x Hx. split; intros s; split.
- intros (r & Hr & Hr0 & ->).
  pose proof (nonpos_nonzero r (Hx r Hr) Hr0) as Hrn.
  exists (-1), (- r). split; [reflexivity|].
  split; [split; [rewrite Ropp_involutive; exact Hr | lra]|].
  (* [1 / r = (-1) / (-r)]. *)
  unfold Rdiv; rewrite Rinv_opp; ring.
- intros (u & q & -> & [Hq Hqp] & ->).
  exists (- q). split; [exact Hq|]. split; [intros E; lra|].
  unfold Rdiv; rewrite Rinv_opp; ring.
- intros (r & Hr & Hr0 & E).
  pose proof (nonpos_nonzero r (Hx r Hr) Hr0) as Hrn.
  exists 1, (- r). split; [reflexivity|].
  split; [split; [rewrite Ropp_involutive; exact Hr | lra]|].
  (* [s = -(1 / r) = 1 / (-r)]. *)
  assert (E' : 1 / - r = - / r) by (unfold Rdiv; rewrite Rinv_opp; ring).
  lra.
- intros (u & q & -> & [Hq Hqp] & ->).
  exists (- q). split; [exact Hq|]. split; [intros E; lra|].
  unfold Rdiv; rewrite Rinv_opp; ring.
Qed.

(** ** The tightest interval from two lanes *)

Lemma div_tightest_P :
  forall x y w0 w1, (forall t, mem t y -> 0 <= t) ->
  (exists r, mem r x) -> (exists q, Qp y q) ->
  lane_ok (quot (Um x) (Qp y)) w0 -> lane_ok (quot (Up x) (Qp y)) w1 ->
  is_tightest (image2_dom div_dom1 div_dom2 Rdiv x y) {| rep := (w0, w1) |}.
Proof.
intros x y w0 w1 Hy (r & Hr) (q & Hq) L0 L1.
destruct (div_image_P x y Hy) as [I1 I0].
apply tightest_lanes_lub.
- exists (r / q). apply I1. exists r, q.
  split; [exact Hr|]. split; [exact Hq | reflexivity].
- apply (lane_ok_ext (quot (Um x) (Qp y))); [|exact L0].
  intros s. symmetry. apply I0.
- apply (lane_ok_ext (quot (Up x) (Qp y))); [|exact L1].
  intros s. symmetry. apply I1.
Qed.

Lemma div_tightest_N :
  forall x y w0 w1, (forall t, mem t y -> t <= 0) ->
  (exists r, mem r x) -> (exists q, Qn y q) ->
  lane_ok (quot (Up x) (Qn y)) w0 -> lane_ok (quot (Um x) (Qn y)) w1 ->
  is_tightest (image2_dom div_dom1 div_dom2 Rdiv x y) {| rep := (w0, w1) |}.
Proof.
intros x y w0 w1 Hy (r & Hr) (q & Hq) L0 L1.
destruct (div_image_N x y Hy) as [I1 I0].
apply tightest_lanes_lub.
- (* [r / q] is a quotient of [Up x] and [Qn y], so its negation is in
     the image. *)
  exists (- (r / q)). apply I0. exists r, q.
  split; [exact Hr|]. split; [exact Hq | reflexivity].
- apply (lane_ok_ext (quot (Up x) (Qn y))); [|exact L0].
  intros s. symmetry. apply I0.
- apply (lane_ok_ext (quot (Um x) (Qn y))); [|exact L1].
  intros s. symmetry. apply I1.
Qed.

Lemma recip_tightest_P :
  forall x w0 w1, (forall r, mem r x -> 0 <= r) -> (exists q, Qp x q) ->
  lane_ok (quot (fun u => u = -1) (Qp x)) w0 ->
  lane_ok (quot (fun u => u = 1) (Qp x)) w1 ->
  is_tightest (image_dom recip_dom Rinv x) {| rep := (w0, w1) |}.
Proof.
intros x w0 w1 Hx (q & Hq) L0 L1.
destruct (recip_image_P x Hx) as [I1 I0].
apply tightest_lanes_lub.
- exists (1 / q). apply I1. exists 1, q.
  split; [reflexivity|]. split; [exact Hq | reflexivity].
- apply (lane_ok_ext (quot (fun u => u = -1) (Qp x))); [|exact L0].
  intros s. symmetry. apply I0.
- apply (lane_ok_ext (quot (fun u => u = 1) (Qp x))); [|exact L1].
  intros s. symmetry. apply I1.
Qed.

Lemma recip_tightest_N :
  forall x w0 w1, (forall r, mem r x -> r <= 0) -> (exists q, Qn x q) ->
  lane_ok (quot (fun u => u = 1) (Qn x)) w0 ->
  lane_ok (quot (fun u => u = -1) (Qn x)) w1 ->
  is_tightest (image_dom recip_dom Rinv x) {| rep := (w0, w1) |}.
Proof.
intros x w0 w1 Hx (q & Hq) L0 L1.
destruct (recip_image_N x Hx) as [I1 I0].
apply tightest_lanes_lub.
- (* [1 / q] is a quotient of [{1}] and [Qn x], so its negation is in the
     image. *)
  exists (- (1 / q)). apply I0. exists 1, q.
  split; [reflexivity|]. split; [exact Hq | reflexivity].
- apply (lane_ok_ext (quot (fun u => u = 1) (Qn x))); [|exact L0].
  intros s. symmetry. apply I0.
- apply (lane_ok_ext (quot (fun u => u = -1) (Qn x))); [|exact L1].
  intros s. symmetry. apply I1.
Qed.
