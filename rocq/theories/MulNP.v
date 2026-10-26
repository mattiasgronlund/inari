(** * [x * y] of intervals that do not contain 0 in their interior

    If [x = [a, b]] and [y = [c, d]] are each in [N0] or [N1] ([a < 0] and
    [b <= 0]) or in [P0] or [P1] ([0 <= a] and [0 < b]), [x * y] returns
    the tightest interval that contains the image of [x × y] under [*]
    ([is_tightest]): [mul_NN], [mul_NP], [mul_PN] and [mul_PP].

    The reals of [x] then all have one sign, and so do those of [y]. Let
    [A] be the reals of [x] if they are at least 0, and their negations
    otherwise, and [B] the same for [y]. Then [A] and [B] are sets of reals
    at least 0, each with an element above 0, and a product [r * t] of a
    real of [x] and one of [y] is [p * q] for [p] in [A] and [q] in [B] if
    [x] and [y] have the same sign, and its negation is if they differ
    ([image2_mult_opp_lr], [image2_mult_opp_l] and [image2_mult_opp_r] in
    [MulTight.v]). The largest element of [A], or +inf if there is none,
    is held by a lane above 0: [-a] for [N0] and [N1], and [b] for [P0]
    and [P1]. Its least element is the negation of
    the other lane, which is a float at most 0: [-b] (the second lane is
    [b]) and [a] (the first lane is [-a]). [nonneg_set] collects these
    facts, and [nonneg_set_N] and [nonneg_set_P] read them off the class.

    The largest product [p * q] is [U * V], the product of the largest
    elements of [A] and [B], or +inf if either is +inf
    ([tight_mult_pos_r] in [MulTight.v]), and [mul_lane_pos] in
    [MulLane.v] shows that [Bmult mode_UP] of the two lanes above 0 is the
    least float or +inf at or above it ([nonneg_lane_pos]). The least
    product [p * q] is [m * n], the product of the least elements, which
    are at least 0, so the largest [-(p * q)] is [-(m * n)]
    ([tight_mult_min]). [Interval::mul] negates one of the two lanes that
    hold [-m] and [-n] with [neg0], so that their product is [-(m * n)],
    and [mul_lane_finite] rounds it up ([nonneg_lane_fin]).

    So one lane of the result is the upper bound of the [p * q] and the
    other that of the [-(p * q)], with the first lane, [-inf(x * y)], the
    upper bound of the negated products [-(r * t)]:
    - [N × N]: [r * t = p * q], the first lane [RU((-b) * d)] is
      [RU(-(m * n))] with [m = -b] and [n = -d], and the second lane
      [RU((-a) * (-c))] is [RU(U * V)].
    - [N × P]: [r * t = -(p * q)], the first lane [RU((-a) * d)] is
      [RU(U * V)], and the second [RU(b * c)] is [RU(-(m * n))] with
      [m = -b] and [n = c].
    - [P × N]: [r * t = -(p * q)], the first lane [RU(b * (-c))] is
      [RU(U * V)], and the second [RU(a * d)] is [RU(-(m * n))] with
      [m = a] and [n = -d].
    - [P × P]: [r * t = p * q], the first lane [RU((-a) * c)] is
      [RU(-(m * n))] with [m = a] and [n = c], and the second
      [RU(b * d)] is [RU(U * V)].
    [mul_fin_pos] assembles the first and last, and [mul_pos_fin] the
    other two, with [tightest_lanes] in [AddSub.v].

    A bound that is 0 may be stored as +0 or -0. Both are finite with
    [B2R] 0, so they need no case of their own. *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer Sign MaxMin AddSub Classify2
  Classes MulRu MulLane MulTight.

Open Scope R_scope.

(** ** One-signed sets of reals *)

(** [A] is a set of reals at least 0 with an element above 0, whose
    largest element, or +inf if there is none, is held by the lane [w]
    above 0, and whose least element is [m]. *)
Definition nonneg_set (A : R -> Prop) (w : f64) (m : R) : Prop :=
  pos_lane w /\ tight (bound w) A /\ (exists r, A r /\ 0 < r) /\
  A m /\ (forall r, A r -> m <= r) /\ 0 <= m.

(** The negations of the reals of an [x] in [N0] or [N1], i.e. of
    [[a, b]] with [a < 0] and [b <= 0], have the largest element [-a]
    (+inf if there is none), which the first lane holds, and the least
    element [-b], the negation of the second lane. *)
Lemma nonneg_set_N :
  forall x, valid x ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  is_finite (snd (rep x)) = true /\
  nonneg_set (fun r => mem (- r) x) (fst (rep x)) (- B2R (snd (rep x))).
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
split; [exact F1|]. split; [exact P0|]. split; [exact T0|]. cbv beta.
split; [|split; [|split]].
- exists (- r0). rewrite Ropp_involutive. split; [exact Hr0 | lra].
- rewrite Ropp_involutive. exact Hb.
- intros r Hr. specialize (Hbmax _ Hr). lra.
- lra.
Qed.

(** The reals of an [x] in [P0] or [P1], i.e. [[a, b]] with [0 <= a] and
    [0 < b], have the largest element [b] (+inf if there is none), which
    the second lane holds, and the least element [a], the negation of the
    first lane. *)
Lemma nonneg_set_P :
  forall x, valid x ->
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  is_finite (fst (rep x)) = true /\
  nonneg_set (fun r => mem r x) (snd (rep x)) (- B2R (fst (rep x))).
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
split; [exact F0|]. split; [exact P1|]. split; [exact T1|].
split; [|split; [|split]].
- exists r0. split; [exact Hr0 | exact Hr0p].
- exact Ha.
- (* A real [r] of [x] has [-r <= -a]. *)
  intros r Hr.
  assert (Hr' : mem (- - r) x) by (rewrite Ropp_involutive; exact Hr).
  specialize (Hamax _ Hr'). lra.
- lra.
Qed.

(** ** Products of one-signed sets *)

(** The products of two such sets have the largest element [U * V], or
    +inf if either [U] or [V] is +inf, and [Bmult mode_UP] of the lanes
    that hold [U] and [V] is the least float or +inf at or above it. *)
Lemma nonneg_lane_pos :
  forall S A B u v m n, nonneg_set A u m -> nonneg_set B v n ->
  (forall s, S s <-> exists p q, A p /\ B q /\ s = p * q) ->
  tight (umult (bound u) (bound v)) S /\
  least_lane (umult (bound u) (bound v)) (Bmult mode_UP u v).
Proof.
intros S A B u v m n (Pu & Tu & Eu & _) (Pv & Tv & Ev & _ & Lv & Mv) HS.
split; [|exact (mul_lane_pos u v Pu Pv)].
apply (tight_ext _ (fun s => exists p q, A p /\ B q /\ s = p * q)).
- intros s. symmetry. apply HS.
- apply tight_mult_pos_r; [exact Tu | exact Tv | | exact Eu | exact Ev].
  (* Every element of [B] is at least [n], which is at least 0. *)
  intros q Hq. specialize (Lv q Hq). lra.
Qed.

(** The negated products of two such sets with the least elements [m] and
    [n] have the largest element [-(m * n)], and if two finite lanes have
    that product, [Bmult mode_UP] of them is the least float or +inf at or
    above it. *)
Lemma nonneg_lane_fin :
  forall S A B wA wB m n u v, nonneg_set A wA m -> nonneg_set B wB n ->
  is_finite u = true -> is_finite v = true -> B2R u * B2R v = - (m * n) ->
  (forall s, S s <-> exists p q, A p /\ B q /\ s = - (p * q)) ->
  tight (Some (B2R u * B2R v)) S /\
  least_lane (Some (B2R u * B2R v)) (Bmult mode_UP u v).
Proof.
intros S A B wA wB m n u v (_ & _ & _ & Hm & Lm & Mm) (_ & _ & _ & Hn & Ln & Mn)
  Fu Fv Euv HS.
split; [|exact (mul_lane_finite u v Fu Fv)].
rewrite Euv. apply (tight_ext _ (fun s => exists p q, A p /\ B q /\ s = - (p * q))).
- intros s. symmetry. apply HS.
- exact (tight_mult_min m n A B Hm Hn Lm Ln Mm Mn).
Qed.

(** If the products [r * t] are the products [p * q] of two such sets, the
    first lane is the negated product of the least elements, and the
    second the product of the largest. *)
Lemma mul_fin_pos :
  forall S A B wA wB m n u v, nonneg_set A wA m -> nonneg_set B wB n ->
  is_finite u = true -> is_finite v = true -> B2R u * B2R v = - (m * n) ->
  (forall s, S s <-> exists p q, A p /\ B q /\ s = p * q) ->
  is_tightest S {| rep := (Bmult mode_UP u v, Bmult mode_UP wA wB) |}.
Proof.
intros S A B wA wB m n u v HA HB Fu Fv Euv HS.
assert (Hne : exists s, S s).
{ destruct HA as (_ & _ & _ & Hm & _), HB as (_ & _ & _ & Hn & _).
  exists (m * n). apply HS. exists m, n.
  split; [exact Hm | split; [exact Hn | reflexivity]]. }
(* The negation of a product is a negated product. *)
assert (HS' : forall s, S (- s) <-> exists p q, A p /\ B q /\ s = - (p * q)).
{ intros s. rewrite HS.
  split; intros (p & q & Hp & Hq & E); exists p, q;
    (split; [exact Hp | split; [exact Hq | lra]]). }
destruct (nonneg_lane_fin (fun s => S (- s)) A B wA wB m n u v HA HB Fu Fv Euv HS')
  as (T0 & L0).
destruct (nonneg_lane_pos S A B wA wB m n HA HB HS) as (T1 & L1).
apply (tightest_lanes _ _ _ _ Hne T0 T1); [exact L0 | exact L1].
Qed.

(** If the negations of the products [r * t] are the products [p * q] of
    two such sets, the first lane is the product of the largest elements,
    and the second the negated product of the least. *)
Lemma mul_pos_fin :
  forall S A B wA wB m n u v, nonneg_set A wA m -> nonneg_set B wB n ->
  is_finite u = true -> is_finite v = true -> B2R u * B2R v = - (m * n) ->
  (forall s, S (- s) <-> exists p q, A p /\ B q /\ s = p * q) ->
  is_tightest S {| rep := (Bmult mode_UP wA wB, Bmult mode_UP u v) |}.
Proof.
intros S A B wA wB m n u v HA HB Fu Fv Euv HS.
(* A product whose negation is [p * q] is [-(p * q)]. *)
assert (HS' : forall s, S s <-> exists p q, A p /\ B q /\ s = - (p * q)).
{ intros s. pose proof (HS (- s)) as E. rewrite Ropp_involutive in E. rewrite E.
  split; intros (p & q & Hp & Hq & E'); exists p, q;
    (split; [exact Hp | split; [exact Hq | lra]]). }
assert (Hne : exists s, S s).
{ destruct HA as (_ & _ & _ & Hm & _), HB as (_ & _ & _ & Hn & _).
  exists (- (m * n)). apply HS'. exists m, n.
  split; [exact Hm | split; [exact Hn | reflexivity]]. }
destruct (nonneg_lane_pos (fun s => S (- s)) A B wA wB m n HA HB HS) as (T0 & L0).
destruct (nonneg_lane_fin S A B wA wB m n u v HA HB Fu Fv Euv HS') as (T1 & L1).
apply (tightest_lanes _ _ _ _ Hne T0 T1); [exact L0 | exact L1].
Qed.

(** ** What [Interval::mul] computes *)

(** [x * y] for [N × N] multiplies [[-b; -a]] and [[d; -c]], with the
    first lane negated by [neg0]. *)
Lemma mul_NN_eq :
  forall has_fma x y,
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  (Interval.classify y = Some CN0 \/ Interval.classify y = Some CN1) ->
  Interval.mul has_fma x y =
  Some {| rep := (Bmult mode_UP (opp (snd (rep x))) (snd (rep y)),
                  Bmult mode_UP (fst (rep x)) (fst (rep y))) |}.
Proof.
intros has_fma x y Cx Cy. unfold Interval.mul.
destruct Cx as [Cx|Cx], Cy as [Cy|Cy]; rewrite (classify2_pair _ _ _ _ Cx Cy);
  cbv beta iota zeta; rewrite mul_ru_correct; reflexivity.
Qed.

(** [x * y] for [N × P] multiplies [[-a; b]] and [[d; c]]. *)
Lemma mul_NP_eq :
  forall has_fma x y,
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  (Interval.classify y = Some CP0 \/ Interval.classify y = Some CP1) ->
  Interval.mul has_fma x y =
  Some {| rep := (Bmult mode_UP (fst (rep x)) (snd (rep y)),
                  Bmult mode_UP (snd (rep x)) (opp (fst (rep y)))) |}.
Proof.
intros has_fma x y Cx Cy. unfold Interval.mul.
destruct Cx as [Cx|Cx], Cy as [Cy|Cy]; rewrite (classify2_pair _ _ _ _ Cx Cy);
  cbv beta iota zeta; rewrite mul_ru_correct; reflexivity.
Qed.

(** [x * y] for [P × N] multiplies [[b; a]] and [[-c; d]]. *)
Lemma mul_PN_eq :
  forall has_fma x y,
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  (Interval.classify y = Some CN0 \/ Interval.classify y = Some CN1) ->
  Interval.mul has_fma x y =
  Some {| rep := (Bmult mode_UP (snd (rep x)) (fst (rep y)),
                  Bmult mode_UP (opp (fst (rep x))) (snd (rep y))) |}.
Proof.
intros has_fma x y Cx Cy. unfold Interval.mul.
destruct Cx as [Cx|Cx], Cy as [Cy|Cy]; rewrite (classify2_pair _ _ _ _ Cx Cy);
  cbv beta iota zeta; rewrite mul_ru_correct; reflexivity.
Qed.

(** [x * y] for [P × P] multiplies [[-a; b]] and [[c; d]]. *)
Lemma mul_PP_eq :
  forall has_fma x y,
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  (Interval.classify y = Some CP0 \/ Interval.classify y = Some CP1) ->
  Interval.mul has_fma x y =
  Some {| rep := (Bmult mode_UP (fst (rep x)) (opp (fst (rep y))),
                  Bmult mode_UP (snd (rep x)) (snd (rep y))) |}.
Proof.
intros has_fma x y Cx Cy. unfold Interval.mul.
destruct Cx as [Cx|Cx], Cy as [Cy|Cy]; rewrite (classify2_pair _ _ _ _ Cx Cy);
  cbv beta iota zeta; rewrite mul_ru_correct; reflexivity.
Qed.

(** ** The theorems *)

(** [x * y] for [x] and [y] in [N0] or [N1]. *)
Lemma mul_NN :
  forall has_fma x y, valid x -> valid y ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  (Interval.classify y = Some CN0 \/ Interval.classify y = Some CN1) ->
  exists z, Interval.mul has_fma x y = Some z /\ is_tightest (image2 Rmult x y) z.
Proof.
intros has_fma x y Hx Hy Cx Cy. rewrite (mul_NN_eq has_fma x y Cx Cy).
eexists. split; [reflexivity|].
destruct (nonneg_set_N x Hx Cx) as (Fb & HX), (nonneg_set_N y Hy Cy) as (Fd & HY).
(* The first lane is [RU((-b) * d)], and [(-b) * d = -((-b) * (-d))]. *)
apply (mul_fin_pos _ _ _ _ _ _ _ _ _ HX HY).
- rewrite is_finite_opp. exact Fb.
- exact Fd.
- rewrite B2R_opp. ring.
- apply image2_mult_opp_lr.
Qed.

(** [x * y] for [x] in [N0] or [N1] and [y] in [P0] or [P1]. *)
Lemma mul_NP :
  forall has_fma x y, valid x -> valid y ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  (Interval.classify y = Some CP0 \/ Interval.classify y = Some CP1) ->
  exists z, Interval.mul has_fma x y = Some z /\ is_tightest (image2 Rmult x y) z.
Proof.
intros has_fma x y Hx Hy Cx Cy. rewrite (mul_NP_eq has_fma x y Cx Cy).
eexists. split; [reflexivity|].
destruct (nonneg_set_N x Hx Cx) as (Fb & HX), (nonneg_set_P y Hy Cy) as (Fc & HY).
(* The second lane is [RU(b * c)], and [b * c = -((-b) * c)]. *)
apply (mul_pos_fin _ _ _ _ _ _ _ _ _ HX HY).
- exact Fb.
- rewrite is_finite_opp. exact Fc.
- rewrite B2R_opp. ring.
- apply image2_mult_opp_l.
Qed.

(** [x * y] for [x] in [P0] or [P1] and [y] in [N0] or [N1]. *)
Lemma mul_PN :
  forall has_fma x y, valid x -> valid y ->
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  (Interval.classify y = Some CN0 \/ Interval.classify y = Some CN1) ->
  exists z, Interval.mul has_fma x y = Some z /\ is_tightest (image2 Rmult x y) z.
Proof.
intros has_fma x y Hx Hy Cx Cy. rewrite (mul_PN_eq has_fma x y Cx Cy).
eexists. split; [reflexivity|].
destruct (nonneg_set_P x Hx Cx) as (Fa & HX), (nonneg_set_N y Hy Cy) as (Fd & HY).
(* The second lane is [RU(a * d)], and [a * d = -(a * (-d))]. *)
apply (mul_pos_fin _ _ _ _ _ _ _ _ _ HX HY).
- rewrite is_finite_opp. exact Fa.
- exact Fd.
- rewrite B2R_opp. ring.
- apply image2_mult_opp_r.
Qed.

(** [x * y] for [x] and [y] in [P0] or [P1]. *)
Lemma mul_PP :
  forall has_fma x y, valid x -> valid y ->
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  (Interval.classify y = Some CP0 \/ Interval.classify y = Some CP1) ->
  exists z, Interval.mul has_fma x y = Some z /\ is_tightest (image2 Rmult x y) z.
Proof.
intros has_fma x y Hx Hy Cx Cy. rewrite (mul_PP_eq has_fma x y Cx Cy).
eexists. split; [reflexivity|].
destruct (nonneg_set_P x Hx Cx) as (Fa & HX), (nonneg_set_P y Hy Cy) as (Fc & HY).
(* The first lane is [RU((-a) * c)], and [(-a) * c = -(a * c)]. *)
apply (mul_fin_pos _ _ _ _ _ _ _ _ _ HX HY).
- exact Fa.
- rewrite is_finite_opp. exact Fc.
- rewrite B2R_opp. ring.
- (* The products [r * t] are those of the reals of [x] and [y]. *)
  intros s. reflexivity.
Qed.
