(** * [sqr] of intervals is tightest and decorated correctly

    [Interval::sqr] returns the tightest interval that contains the image
    of its argument under the point function [sqr], [r * r] for every real
    [r] ([image_dom] and [sqr_dom] in [Ieee1788.v]), for either value of
    [has_fma], and [DecInterval::sqr] decorates it with the minimum of the
    strongest decoration that holds and the decoration of its argument, as
    IEEE 1788 asks of a tightest interval version of a function.

    [Interval::sqr] dispatches on the class of its argument, and
    [Interval::classify] is defined on every valid interval
    ([classify_defined] in [Abs.v]). [x = [a, b]] is stored as [[-a; b]],
    and [RU] is rounding up:
    - [E]: the image is empty, and [sqr] returns [EMPTY].
    - [Z]: [x] is [[0, 0]], its image is [{0}], and [sqr] returns
      [Interval::zero()] ([zero_tightest] in [MulZero.v]).
    - [N0] and [N1] ([a < 0] and [b <= 0]), and [P0] and [P1] ([0 <= a]
      and [0 < b]): let [A] be the negations of the reals of [x] for [N0]
      and [N1], and the reals of [x] for [P0] and [P1]. [A] is a set of
      reals at least 0 with an element above 0 ([nonneg_set_N] and
      [nonneg_set_P] in [MulNP.v]), and the squares of the reals of [x]
      are those of the elements of [A]. [A] holds every real between two
      of its elements, so these squares are the products [p * q] of two
      elements of [A] ([squares_products]). The lanes are
      [[RU(b * (-b)); RU((-a) * (-a))]] for [N0] and [N1], and
      [[RU((-a) * a); RU(b * b)]] for [P0] and [P1]: the negated square of
      the least element of [A], and the square of the largest. So
      [mul_fin_pos] in [MulNP.v], which proves the cases [N × N] and
      [P × P] of [x * y], shows them tightest with [A] as both sets.
    - [M] ([a < 0 < b]): 0 is in [x], so the least square is 0, which the
      first lane holds as +0. The squares are among the products [r * t]
      of two reals of [x], and each such product is at most [r * r] or
      [t * t], so both sets have the same upper bounds ([tight_cofinal] in
      [MulTight.v]). The largest product is [max(a * a, b * b)], or there
      is none if [a] or [b] is infinite ([tight_mult_mixed] in
      [MulTight.v], with [x] as both arguments). The second lane,
      [max1(RU((-a) * (-a)), RU(b * b))], is the least float or +inf at or
      above it ([max_least_lane] and [mul_lane_pos] in [MulLane.v]).

    [sqr] is continuous at each real ([Rsqr_continuous]). It is stated with
    the definitions for a function with a domain, [sqr_dom] being all of
    R, because their [com] asks, as the standard does, for the computed
    interval [z] to be bounded, rather than the image: [[f64::MAX,
    f64::MAX]] squared is [[f64::MAX, +inf]], which [set_dec] decorates
    [dac], though the image [{f64::MAX * f64::MAX}] is bounded. The
    strongest decoration of [sqr] on [x], with the result [z], is:

    - [trv] if [x] is empty, as [def] asks for a nonempty [x]. [z] is then
      empty, and [set_dec] returns [EMPTY], whose [trv] is the minimum of
      [trv] and the decoration of [x].
    - [com] if [x] is nonempty and [z] is common, i.e. bounded
      ([common_bounded] and [bounded_common] in [DecBinary.v]). [x] is
      then bounded too, as a real [r] of [x] with [r * r <= m] has
      [|r| <= 1 + m], and [set_dec] keeps the decoration of [x], which is
      its minimum with [com].
    - [dac] if [x] is nonempty and [z] is not common. [set_dec] then lowers
      [com] to [dac] and keeps any other decoration, which gives the
      minimum of [dac] and the decoration of [x].

    So, like [dec_sqrt_correct] in [Sqrt.v], [dec_sqr_correct] needs no
    hypothesis that [x] is [com] only if its interval is common. *)

From Stdlib Require Import Reals Lra Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer Sign MaxMin DecBinary AddSub
  Abs Classes MulRu MulLane MulTight MulNP MulZero Sqrt.

Open Scope R_scope.

(** ** The image *)

(** The image of [x] under [sqr] holds the squares of the reals of [x]. *)
Lemma sqr_image :
  forall x s, image_dom sqr_dom Rsqr x s <-> exists r, mem r x /\ s = r * r.
Proof.
intros x s. unfold image_dom, sqr_dom, Rsqr. split.
- intros (r & Hr & _ & ->). exists r. split; [exact Hr | reflexivity].
- intros (r & Hr & ->). exists r. split; [exact Hr | split; [exact I | reflexivity]].
Qed.

(** The squares of the elements of a set [A] of reals at least 0 that
    holds every real between two of its elements are the products of two
    of its elements: [r * t] is the square of [sqrt (r * t)], which is
    between [r] and [t], as [r * r <= r * t <= t * t] for [0 <= r <= t]. *)
Lemma squares_products :
  forall A, (forall r, A r -> 0 <= r) ->
  (forall r t u, A r -> A t -> r <= u <= t -> A u) ->
  forall s, (exists u, A u /\ s = u * u) <-> (exists r t, A r /\ A t /\ s = r * t).
Proof.
intros A H0 Hbetween s. split.
- intros (u & Hu & ->). exists u, u. split; [exact Hu | split; [exact Hu | reflexivity]].
- (* It is enough to take [r <= t], as [r * t = t * r]. *)
  assert (Hle : forall r t, A r -> A t -> r <= t -> exists u, A u /\ r * t = u * u).
  { intros r t Hr Ht Hrt. pose proof (H0 r Hr) as Pr.
    assert (Prt : 0 <= r * t) by nra.
    assert (L1 : r * r <= r * t) by nra.
    assert (L2 : r * t <= t * t) by nra.
    apply sqrt_le_1_alt in L1, L2.
    rewrite sqrt_square in L1 by exact Pr. rewrite sqrt_square in L2 by lra.
    exists (sqrt (r * t)). split.
    - apply (Hbetween r t); [exact Hr | exact Ht | split; assumption].
    - symmetry. apply sqrt_sqrt. exact Prt. }
  intros (r & t & Hr & Ht & ->).
  destruct (Rle_or_lt r t) as [Hrt|Htr].
  + exact (Hle r t Hr Ht Hrt).
  + rewrite Rmult_comm. exact (Hle t r Ht Hr (Rlt_le _ _ Htr)).
Qed.

(** ** What [Interval::sqr] computes *)

(** [E] gives [EMPTY], and [Z] gives [Interval::zero()]. *)
Lemma sqr_eq_E :
  forall has_fma x, Interval.classify x = Some CE ->
  Interval.sqr has_fma x = Some Interval.EMPTY.
Proof.
intros has_fma x Cx. unfold Interval.sqr. rewrite Cx. reflexivity.
Qed.

Lemma sqr_eq_Z :
  forall has_fma x, Interval.classify x = Some CZ ->
  Interval.sqr has_fma x = Some Interval.zero.
Proof.
intros has_fma x Cx. unfold Interval.sqr. rewrite Cx. reflexivity.
Qed.

(** [M] multiplies [[-a; b]] by itself, takes [max1] of the lanes, and
    puts +0 in the first lane. *)
Lemma sqr_eq_M :
  forall has_fma x, Interval.classify x = Some CM ->
  Interval.sqr has_fma x =
  Some {| rep := (zero, Generic.max1 (Bmult mode_UP (fst (rep x)) (fst (rep x)))
                                     (Bmult mode_UP (snd (rep x)) (snd (rep x)))) |}.
Proof.
intros has_fma x Cx. unfold Interval.sqr. rewrite Cx. cbv beta iota zeta.
rewrite mul_ru_correct. reflexivity.
Qed.

(** [N0] and [N1] multiply [[b; -a]] by [[-b; -a]]. *)
Lemma sqr_eq_N :
  forall has_fma x,
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  Interval.sqr has_fma x =
  Some {| rep := (Bmult mode_UP (snd (rep x)) (opp (snd (rep x))),
                  Bmult mode_UP (fst (rep x)) (fst (rep x))) |}.
Proof.
intros has_fma x [Cx|Cx]; unfold Interval.sqr; rewrite Cx; cbv beta iota zeta;
  rewrite mul_ru_correct; reflexivity.
Qed.

(** [P0] and [P1] multiply [[-a; b]] by [[a; b]]. *)
Lemma sqr_eq_P :
  forall has_fma x,
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  Interval.sqr has_fma x =
  Some {| rep := (Bmult mode_UP (fst (rep x)) (opp (fst (rep x))),
                  Bmult mode_UP (snd (rep x)) (snd (rep x))) |}.
Proof.
intros has_fma x [Cx|Cx]; unfold Interval.sqr; rewrite Cx; cbv beta iota zeta;
  rewrite mul_ru_correct; reflexivity.
Qed.

(** ** The tightest interval by class *)

(** For [N0] and [N1], [A] is the negations of the reals of [x], with the
    largest element [-a] held by the first lane and the least element
    [-b]. *)
Lemma sqr_N :
  forall x, valid x ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  is_tightest (image_dom sqr_dom Rsqr x)
    {| rep := (Bmult mode_UP (snd (rep x)) (opp (snd (rep x))),
               Bmult mode_UP (fst (rep x)) (fst (rep x))) |}.
Proof.
intros x Hx Cx. destruct (nonneg_set_N x Hx Cx) as (Fb & HA).
apply (mul_fin_pos _ _ _ _ _ _ _ _ _ HA HA).
- exact Fb.
- rewrite is_finite_opp. exact Fb.
- rewrite B2R_opp. ring.
- intros s. rewrite sqr_image.
  destruct HA as (_ & _ & _ & _ & Lm & Mm).
  rewrite <- (squares_products (fun p => mem (- p) x)).
  + (* [r * r = (-r) * (-r)]. *)
    split; intros (u & Hu & ->); exists (- u);
      [rewrite Ropp_involutive; split; [exact Hu | ring] | split; [exact Hu | ring]].
  + intros r Hr. specialize (Lm r Hr). lra.
  + intros r t u Hr Ht Hu. apply (mem_between x (- t) (- r)); [exact Hx | exact Ht | exact Hr | lra].
Qed.

(** For [P0] and [P1], [A] is the reals of [x], with the largest element
    [b] held by the second lane and the least element [a]. *)
Lemma sqr_P :
  forall x, valid x ->
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  is_tightest (image_dom sqr_dom Rsqr x)
    {| rep := (Bmult mode_UP (fst (rep x)) (opp (fst (rep x))),
               Bmult mode_UP (snd (rep x)) (snd (rep x))) |}.
Proof.
intros x Hx Cx. destruct (nonneg_set_P x Hx Cx) as (Fa & HA).
apply (mul_fin_pos _ _ _ _ _ _ _ _ _ HA HA).
- exact Fa.
- rewrite is_finite_opp. exact Fa.
- rewrite B2R_opp. ring.
- intros s. rewrite sqr_image.
  destruct HA as (_ & _ & _ & _ & Lm & Mm).
  apply (squares_products (fun r => mem r x)).
  + intros r Hr. specialize (Lm r Hr). lra.
  + intros r t u Hr Ht Hu. exact (mem_between x r t u Hx Hr Ht Hu).
Qed.

(** For [M], the least square is 0, and the largest is
    [max(a * a, b * b)], or there is none if [a] or [b] is infinite. *)
Lemma sqr_M :
  forall x, valid x -> Interval.classify x = Some CM ->
  is_tightest (image_dom sqr_dom Rsqr x)
    {| rep := (zero, Generic.max1 (Bmult mode_UP (fst (rep x)) (fst (rep x)))
                                  (Bmult mode_UP (snd (rep x)) (snd (rep x)))) |}.
Proof.
intros x Hx Cx.
destruct (classify_lanes x CM Hx Cx) as [P0 P1].
destruct (classify_mem x CM Hx Cx) as [(rn & Hrn & Hrn0) (rp & Hrp & Hrp0)].
destruct (lanes_tight x Hx (not_nan_upper _ (pos_lane_upper _ P0)))
  as (_ & _ & _ & T0 & T1).
(* 0 is between a real of [x] below 0 and one above. *)
assert (H0 : mem 0 x) by (apply (mem_between x rn rp 0 Hx Hrn Hrp); lra).
apply (tightest_lanes _ _ (Some 0)
  (umax (umult (bound (fst (rep x))) (bound (fst (rep x))))
        (umult (bound (snd (rep x))) (bound (snd (rep x)))))).
- exists 0. apply sqr_image. exists 0. split; [exact H0 | ring].
- (* The negated squares are at most 0, which is one of them. *)
  apply tight_Some. split.
  + apply sqr_image. exists 0. split; [exact H0 | ring].
  + intros u Hu. apply sqr_image in Hu. destruct Hu as (r & _ & E). nra.
- (* The squares are products of two reals of [x], and a product [r * t]
     is at most [r * r] or [t * t], as [2 * r * t <= r * r + t * t]. *)
  assert (HAB : forall s, image_dom sqr_dom Rsqr x s ->
    exists r t, mem r x /\ mem t x /\ s = r * t).
  { intros s Hs. apply sqr_image in Hs. destruct Hs as (r & Hr & ->).
    exists r, r. split; [exact Hr | split; [exact Hr | reflexivity]]. }
  assert (HBA : forall s, (exists r t, mem r x /\ mem t x /\ s = r * t) ->
    exists u, image_dom sqr_dom Rsqr x u /\ s <= u).
  { intros s (r & t & Hr & Ht & ->).
    destruct (Rle_or_lt (r * t) (r * r)) as [H|H].
    - exists (r * r). split; [apply sqr_image; exists r; split; [exact Hr | reflexivity] | exact H].
    - exists (t * t). split; [apply sqr_image; exists t; split; [exact Ht | reflexivity]|].
      pose proof (Rle_0_sqr (r - t)). unfold Rsqr in *. nra. }
  apply (proj2 (tight_cofinal _ _ _ HAB HBA)).
  apply (tight_mult_mixed (bound (snd (rep x))) (bound (fst (rep x)))
    (bound (snd (rep x))) (bound (fst (rep x))) (fun r => mem r x) (fun t => mem t x));
    [exact T1 | exact T0 | exact T1 | exact T0 | exists rn; split; assumption
    | exists rp; split; assumption | exists rn; split; assumption
    | exists rp; split; assumption].
- cbn [rep fst]. exact (least_lane_exact zero eq_refl).
- cbn [rep snd]. apply max_least_lane; apply mul_lane_pos; assumption.
Qed.

(** ** The theorem *)

(** [Interval::sqr] returns the tightest interval that contains the image
    of [x] under [sqr]. *)
Theorem sqr_correct :
  forall has_fma x, valid x ->
  exists y, Interval.sqr has_fma x = Some y /\
    is_tightest (image_dom sqr_dom Rsqr x) y.
Proof.
intros has_fma x Hx. destruct (classify_defined x Hx) as (c & Cx).
destruct c.
- (* An empty [x] has an empty image. *)
  rewrite (sqr_eq_E has_fma x Cx). eexists. split; [reflexivity|].
  apply tightest_empty. intros u Hu. apply sqr_image in Hu.
  destruct Hu as (r & Hr & _). exact (classify_mem x CE Hx Cx r Hr).
- rewrite (sqr_eq_M has_fma x Cx). eexists. split; [reflexivity|].
  exact (sqr_M x Hx Cx).
- rewrite (sqr_eq_N has_fma x (or_introl Cx)). eexists. split; [reflexivity|].
  exact (sqr_N x Hx (or_introl Cx)).
- rewrite (sqr_eq_N has_fma x (or_intror Cx)). eexists. split; [reflexivity|].
  exact (sqr_N x Hx (or_intror Cx)).
- rewrite (sqr_eq_P has_fma x (or_introl Cx)). eexists. split; [reflexivity|].
  exact (sqr_P x Hx (or_introl Cx)).
- rewrite (sqr_eq_P has_fma x (or_intror Cx)). eexists. split; [reflexivity|].
  exact (sqr_P x Hx (or_intror Cx)).
- (* [x] is [[0, 0]], whose image is [{0}]. *)
  rewrite (sqr_eq_Z has_fma x Cx). eexists. split; [reflexivity|].
  apply (is_tightest_ext (fun s => s = 0)); [|exact zero_tightest].
  pose proof (classify_mem x CZ Hx Cx) as M. cbv beta iota in M.
  intros s. rewrite sqr_image. split.
  + intros ->. exists 0. split; [apply M; reflexivity | ring].
  + intros (r & Hr & ->). apply M in Hr. subst r. ring.
Qed.

(** ** The decorated version *)

(** [sqr] is continuous at each real, as it is differentiable there. *)
Lemma Rsqr_continuous : forall r, continuity_pt Rsqr r.
Proof.
intros r. exact (derivable_continuous_pt Rsqr r (derivable_pt_Rsqr r)).
Qed.

(** [DecInterval::sqr] returns NaI for NaI, and otherwise the tightest
    interval, decorated with the decoration that IEEE 1788 asks for. *)
Theorem dec_sqr_correct :
  forall has_fma x, valid (itv x) ->
  exists y, DecInterval.sqr has_fma x = Some y /\
    if DecInterval.is_nai x then y = x
    else
      is_tightest (image_dom sqr_dom Rsqr (itv x)) (itv y) /\
      exists d, strongest_dom sqr_dom d Rsqr (itv x) (itv y) /\
        dec y = dec_min d (dec x).
Proof.
intros has_fma x Hx. unfold DecInterval.sqr.
destruct (DecInterval.is_nai x) eqn:Hnai; [exists x; split; reflexivity|].
assert (Hdx : dec x <> Ill).
{ intros E. unfold DecInterval.is_nai in Hnai. now rewrite E in Hnai. }
destruct (sqr_correct has_fma (itv x) Hx) as (z & Ez & Hz).
rewrite Ez. cbv beta iota.
exists (DecInterval.set_dec z (dec x)). split; [reflexivity|].
assert (Him : forall r, mem r (itv x) -> mem (r * r) z).
{ intros r Hr. apply (proj1 (proj2 Hz)), sqr_image. exists r. split; [exact Hr | reflexivity]. }
destruct (Interval.is_empty z) eqn:Ez0.
- (* [z] is empty, so [x] is. *)
  pose proof (valid_empty_eq z (proj1 Hz) Ez0) as Ez1.
  rewrite (set_dec_empty_any z (dec x) Ez0 Hdx). cbn [itv dec DecInterval.EMPTY].
  rewrite <- Ez1. split; [exact Hz|]. exists Trv.
  split; [|symmetry; now apply dec_min_Trv_l].
  apply strongest_dom_Trv. intros Hdef. cbn [p_dom] in Hdef.
  destruct Hdef as ((r & Hr) & _).
  exact (mem_empty z (r * r) (proj1 Hz) Ez0 (Him r Hr)).
- (* [x] is nonempty, as its image is, and [sqr] is continuous on it. *)
  assert (Nx : exists r, mem r (itv x)).
  { destruct (Interval.is_empty (itv x)) eqn:Ex; [|exact (nonempty_mem _ Hx Ex)].
    exfalso. rewrite (no_mem_empty z (proj1 Hz)) in Ez0; [discriminate Ez0|].
    apply (tightest_no_mem _ _ Hz). intros u Hu. apply sqr_image in Hu.
    destruct Hu as (r & Hr & _). exact (mem_empty _ r Hx Ex Hr). }
  destruct Nx as (r0 & Hr0).
  assert (Hcont : forall D r, continue_in Rsqr D r)
    by (intros D r; apply continuity_pt_continue_in, Rsqr_continuous).
  assert (Hdac : p_dom sqr_dom Dac Rsqr (itv x) z).
  { cbn [p_dom]. split; [exists r0; exact Hr0|].
    split; [intros r _; exact I | intros r _; apply Hcont]. }
  destruct (Interval.is_common_interval z) eqn:Cz.
  + (* [z] is bounded, so [x] is. *)
    rewrite (set_dec_keep z (dec x) Ez0 Hdx (fun _ => Cz)).
    cbn [itv dec DecInterval.new_unchecked]. split; [exact Hz|].
    exists Com. split; [|symmetry; apply dec_min_Com_l].
    apply strongest_dom_Com. cbn [p_dom].
    split; [exists r0; exact Hr0|]. split; [intros r _; exact I|]. split.
    * (* [r * r <= m] gives [|r| <= 1 + m]. *)
      destruct (common_bounded z Cz) as (m & Hm).
      exists (1 + m). intros r Hr.
      pose proof (Hm _ (Him r Hr)) as Hs.
      rewrite Rabs_pos_eq in Hs by nra.
      apply Rabs_le. split; nra.
    * split; [intros r _; apply Hcont | exact (common_bounded z Cz)].
  + (* [z] is not bounded, and [com] asks for a bounded [z]. *)
    rewrite (set_dec_lower z (dec x) Ez0 Cz Hdx).
    cbn [itv dec DecInterval.new_unchecked]. split; [exact Hz|].
    exists Dac. split; [|reflexivity].
    apply strongest_dom_Dac; [exact Hdac|].
    intros Hcom. cbn [p_dom] in Hcom. destruct Hcom as (_ & _ & _ & _ & Bz).
    rewrite (bounded_common z (proj1 Hz) Ez0 Bz) in Cz. discriminate Cz.
Qed.
