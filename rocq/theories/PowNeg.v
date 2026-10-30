(** * [Interval::pow] for exponents at most 0

    The branch [d <= 0.0] of [Interval::pow], for the base [x], the
    intersection of [self] with [[0, +inf]], with bounds [a] and [b], and
    the exponent [y] with bounds [c] and [d]. Every point of the domain in
    the box has [r > 0], so the image is empty if [b] is 0
    ([pw_neg_empty]). Otherwise, for [r > 0] and [t <= 0], [r^t] decreases
    in [r], and in [t] it decreases for [r <= 1] and increases for
    [r >= 1], so the bounds are at the corners that the three cases pick:
    [b < 1] ([pw_neg_lt1]), [a > 1] ([pw_neg_gt1]) and [a <= 1 <= b]
    ([pw_neg_mid]). A corner with [a = 0], [b = +inf] or [c = -inf] is a
    limit, which [pow_rd] and [pow_ru] give by the special values of
    [PowMpfr.v]. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Integer Sign MaxMin AddSub
  DecBinary DivTight MpfrRound MonoInc PowReal PowMpfr PowCases.

Open Scope R_scope.

(** ** The bounds as reals *)

(** A finite float with the value 0 is a zero. *)
Lemma pn_zero :
  forall w : f64, is_finite w = true -> B2R w = 0 -> exists s, w = B754_zero s.
Proof.
intros [s|s| |s mw ew H] F E; try discriminate.
- now exists s.
- exfalso. revert E. cbn [B2R]. apply F2R_neq_0. destruct s; discriminate.
Qed.

Lemma pn_lt_1 :
  forall b, is_finite b = true -> Model.lt b (of_u64 1) = Rlt_bool (B2R b) 1.
Proof.
intros b Fb. destruct Sign.one_B2R as [F1 E1].
unfold Model.lt. rewrite Bltb_correct by first [exact Fb | exact F1].
change (B2R (of_u64 1)) with (B2R Sign.one). rewrite E1. reflexivity.
Qed.

Lemma pn_gt_1 :
  forall a, is_finite a = true -> Model.gt a (of_u64 1) = Rlt_bool 1 (B2R a).
Proof.
intros a Fa. destruct Sign.one_B2R as [F1 E1].
unfold Model.gt. rewrite Bltb_correct by first [exact Fa | exact F1].
change (B2R (of_u64 1)) with (B2R Sign.one). rewrite E1. reflexivity.
Qed.

(** The reals of a base [x] whose lower bound is the real [A]: those of
    [[A, b]] for a finite upper bound [b] above 0, or of [[A, +inf)]. *)
Definition pn_xdesc (x : Interval) (A : R) (b : f64) : Prop :=
  (is_finite b = true /\ 0 < B2R b /\ A <= B2R b /\
   forall r, mem r x <-> A <= r <= B2R b) \/
  (b = B754_infinity false /\ forall r, mem r x <-> A <= r).

(** The reals of an exponent [y] whose upper bound is the real [D]: those
    of [[c, D]] for a finite lower bound [c], or of [(-inf, D]]. *)
Definition pn_ydesc (y : Interval) (c : f64) (D : R) : Prop :=
  (is_finite c = true /\ B2R c <= D /\ forall t, mem t y <-> B2R c <= t <= D) \/
  (c = B754_infinity true /\ forall t, mem t y <-> t <= D).

Lemma pn_x :
  forall x, pw_xok x -> Model.eq (Interval.sup_raw x) Model.zero = false ->
  is_finite (Interval.inf_raw x) = true /\ 0 <= B2R (Interval.inf_raw x) /\
  (B2R (Interval.inf_raw x) = 0 -> Interval.inf_raw x = B754_zero false) /\
  pn_xdesc x (B2R (Interval.inf_raw x)) (Interval.sup_raw x).
Proof.
intros x (Hv & He & Fa & HA0 & HAz) Hb0.
split; [exact Fa|]. split; [exact HA0|]. split; [exact HAz|].
destruct (valid_nonempty x Hv He) as (Hlo & Hup & Hord).
assert (Hm := fun r => mem_bounds x r Hlo Hup).
unfold Interval.inf_raw, Interval.sup_raw, pn_xdesc in *.
rewrite (bound_finite _ Fa) in Hm, Hord.
destruct Hup as [Fb | Eb].
- left. rewrite (bound_finite _ Fb) in Hm, Hord. unfold ordered in Hord; cbv beta iota in Hord.
  (* [b] is not 0, and [0 <= a <= b]. *)
  assert (Hb : B2R (snd (rep x)) <> 0).
  { unfold Model.eq in Hb0. rewrite Beqb_correct in Hb0 by first [exact Fb | reflexivity].
    change (B2R Model.zero) with 0 in Hb0.
    revert Hb0. case Req_bool_spec; [discriminate | intros H _; exact H]. }
  split; [exact Fb|]. split; [lra|]. split; [exact Hord|].
  intros r. rewrite Hm. unfold in_bounds; cbv beta iota. tauto.
- right. split; [exact Eb|]. rewrite Eb, bound_inf in Hm.
  intros r. rewrite Hm. unfold in_bounds; cbv beta iota. tauto.
Qed.

Lemma pn_y :
  forall y, valid y -> Interval.is_empty y = false ->
  Model.le (Interval.sup_raw y) Model.zero = true ->
  is_finite (Interval.sup_raw y) = true /\ B2R (Interval.sup_raw y) <= 0 /\
  pn_ydesc y (Interval.inf_raw y) (B2R (Interval.sup_raw y)).
Proof.
intros y Hv He Hd.
destruct (valid_nonempty y Hv He) as (Hlo & Hup & Hord).
assert (Hm := fun t => mem_bounds y t Hlo Hup).
unfold Interval.inf_raw, Interval.sup_raw, pn_ydesc in *.
(* [d <= 0] rules out [d = +inf]. *)
destruct Hup as [Fd | Ed]; [| rewrite Ed in Hd; vm_compute in Hd; discriminate Hd].
split; [exact Fd|].
rewrite (bound_finite _ Fd) in Hm, Hord.
split.
{ unfold Model.le in Hd. rewrite Bleb_correct in Hd by first [exact Fd | reflexivity].
  change (B2R Model.zero) with 0 in Hd.
  revert Hd. case Rle_bool_spec; [intros H _; exact H | discriminate]. }
destruct Hlo as [Fc | Ec].
- left. rewrite (bound_finite _ Fc) in Hm, Hord. unfold ordered in Hord; cbv beta iota in Hord.
  split; [exact Fc|]. split; [exact Hord|].
  intros t. rewrite Hm. unfold in_bounds; cbv beta iota. tauto.
- right. split; [exact Ec|]. rewrite Ec, bound_inf in Hm.
  intros t. rewrite Hm. unfold in_bounds; cbv beta iota. tauto.
Qed.

Lemma pn_xA :
  forall x A b, pn_xdesc x A b -> (forall r, mem r x -> A <= r) /\ mem A x.
Proof.
intros x A b [(Fb & HB0 & HAB & Hm) | (Eb & Hm)]; split.
- intros r Hr. apply Hm in Hr. lra.
- apply Hm. lra.
- intros r Hr. apply Hm in Hr. exact Hr.
- apply Hm. lra.
Qed.

Lemma pn_yD :
  forall y c D, pn_ydesc y c D -> (forall t, mem t y -> t <= D) /\ mem D y.
Proof.
intros y c D [(Fc & HCD & Hm) | (Ec & Hm)]; split.
- intros t Ht. apply Hm in Ht. lra.
- apply Hm. lra.
- intros t Ht. apply Hm in Ht. exact Ht.
- apply Hm. lra.
Qed.

(** ** The image *)

(** For exponents at most 0, the points of the domain are those with
    [r > 0]. *)
Lemma pn_img :
  forall x y s, (forall t, mem t y -> t <= 0) ->
  image2_set pow_dom Rpow x y s <->
  exists r t, mem r x /\ mem t y /\ 0 < r /\ s = Rpow r t.
Proof.
intros x y s Hy. split.
- intros (r & t & Hr & Ht & Hd & Hs). exists r, t.
  split; [exact Hr|]. split; [exact Ht|]. split; [|exact Hs].
  destruct Hd as [Hd | [_ Hd]]; [exact Hd|]. specialize (Hy t Ht). lra.
- intros (r & t & Hr & Ht & Hd & Hs). exists r, t.
  split; [exact Hr|]. split; [exact Ht|]. split; [left; exact Hd | exact Hs].
Qed.

(** ** Lanes *)

(** The lower lane from a least element [L] rounded down, and the upper
    lane from a largest element [U] rounded up. *)
Lemma pn_lo_at :
  forall (S : R -> Prop) L w, S L -> (forall s, S s -> L <= s) ->
  mpfr_round f64_format RNDD L (with_val w) -> lane_ok (fun s => S (- s)) (opp w).
Proof.
intros S L w HL Hlo Hw. apply (pl_lo S L w Hlo); [|exact Hw].
intros eps He. exists L. split; [exact HL | lra].
Qed.

Lemma pn_hi_at :
  forall (S : R -> Prop) U w, S U -> (forall s, S s -> s <= U) ->
  mpfr_round f64_format RNDU U (with_val w) -> lane_ok S w.
Proof.
intros S U w HU Hhi Hw. apply (pl_hi S U w Hhi); [|exact Hw].
intros eps He. exists U. split; [exact HU | lra].
Qed.

(** The lower lane from the greatest lower bound 0 rounded down. *)
Lemma pn_lo_0 :
  forall (S : R -> Prop) w, (forall s, S s -> 0 <= s) ->
  (forall eps, 0 < eps -> exists s, S s /\ s < eps) ->
  mpfr_round f64_format RNDD 0 (with_val w) -> lane_ok (fun s => S (- s)) (opp w).
Proof.
intros S w Hlo Happ Hw. apply (pl_lo S 0 w Hlo); [|exact Hw].
intros eps He. destruct (Happ eps He) as (s & Hs & Hse). exists s.
split; [exact Hs | lra].
Qed.

(** The lower lane [pow_rd(b, c)] for [b >= 1] or [b = +inf]: the
    greatest lower bound is at the corner [(b, c)], as [r^t] decreases in
    [r] and, for [r >= 1], increases in [t]. It is attained if [b] and [c]
    are finite. Otherwise it is 0 ([b > 1] or [b = +inf], with [c < 0] or
    [c = -inf]), or 1 ([b = 1] and [c = -inf]: every value is
    [r^t >= 1^t = 1]; [b = +inf] and [c = 0]: [y = {0}]). *)
Lemma pn_lo_bc :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall x y A b c D, 0 <= A -> pn_xdesc x A b -> (is_finite b = true -> 1 <= B2R b) ->
  D <= 0 -> pn_ydesc y c D ->
  lane_ok (fun s => image2_set pow_dom Rpow x y (- s)) (opp (pow_rd m b c)).
Proof.
intros emin emax m Hrg Hg Hp x y A b c D HA0 Hxb Hb1 HD0 Hyc.
destruct (pn_yD y c D Hyc) as (HyD & HDy).
assert (Hy0 : forall t, mem t y -> t <= 0) by (intros t Ht; specialize (HyD t Ht); lra).
assert (Hpos : forall s, image2_set pow_dom Rpow x y s -> 0 <= s).
{ intros s Hs. destruct (proj1 (pn_img x y s Hy0) Hs) as (r & t & _ & _ & Hr & ->).
  apply Rlt_le, Rpow_gt_0, Hr. }
unfold pow_rd.
destruct Hxb as [(Fb & HB0 & HAB & Hmx) | (Eb & Hmx)];
  [specialize (Hb1 Fb) |];
  destruct Hyc as [(Fc & HCD & Hmy) | (Ec & Hmy)].
- (* [b] and [c] finite: the least value is [b^c]. *)
  apply (pn_lo_at (image2_set pow_dom Rpow x y) (Rpow (B2R b) (B2R c))).
  + apply (proj2 (pn_img x y _ Hy0)). exists (B2R b), (B2R c).
    split; [apply Hmx; lra|]. split; [apply Hmy; lra|]. split; [lra | reflexivity].
  + intros s Hs. destruct (proj1 (pn_img x y s Hy0) Hs) as (r & t & Hr & Ht & Hr0 & ->).
    apply Hmx in Hr. apply Hmy in Ht.
    apply Rle_trans with (Rpow (B2R b) t).
    * apply Rpow_le_exp_ge1; lra.
    * apply Rpow_le_base_neg; lra.
  + apply (pow_fin emin emax m Hrg Hg Hp); [exact Fb | exact Fc | left; lra].
- rewrite Ec. destruct (Rle_lt_or_eq_dec 1 (B2R b) Hb1) as [HB1 | HB1].
  + (* [b > 1], [c = -inf]: [b^t] tends to 0 as [t] falls. *)
    apply pn_lo_0; [exact Hpos | |].
    * intros eps He. destruct (Rpow_exp_small_gt1 (B2R b) eps HB1 He) as (t0 & Ht0).
      exists (Rpow (B2R b) (Rmin t0 D)). split.
      -- apply (proj2 (pn_img x y _ Hy0)). exists (B2R b), (Rmin t0 D).
         split; [apply Hmx; lra|]. split; [apply Hmy, Rmin_r|]. split; [lra | reflexivity].
      -- apply Ht0, Rmin_l.
    * apply (pow_gt1_ninf emin emax m Hg Hp); [exact Fb | exact HB1].
  + (* [b = 1], [c = -inf]: every value is at least [1^t = 1]. *)
    apply (pn_lo_at (image2_set pow_dom Rpow x y) 1).
    * apply (proj2 (pn_img x y _ Hy0)). exists (B2R b), D.
      split; [apply Hmx; lra|]. split; [exact HDy|]. split; [lra|].
      rewrite <- HB1. symmetry. apply Rpow_1_l.
    * intros s Hs. destruct (proj1 (pn_img x y s Hy0) Hs) as (r & t & Hr & Ht & Hr0 & ->).
      apply Hmx in Hr. specialize (HyD t Ht).
      rewrite <- (Rpow_1_l t). apply Rpow_le_base_neg; lra.
    * apply (pow_one_inf emin emax m Hrg Hg Hp); [exact Fb | lra].
- rewrite Eb. assert (HC0' : B2R c <= 0) by lra.
  destruct (Rle_lt_or_eq_dec _ _ HC0') as [HC0 | HC0].
  + (* [b = +inf], [c < 0]: [r^c] tends to 0 as [r] grows. *)
    apply pn_lo_0; [exact Hpos | |].
    * intros eps He. destruct (Rpow_base_large_neg (B2R c) eps HC0 He) as (r0 & Hr0 & Hr0e).
      exists (Rpow (Rmax r0 A) (B2R c)).
      pose proof (Rmax_l r0 A). pose proof (Rmax_r r0 A). split.
      -- apply (proj2 (pn_img x y _ Hy0)). exists (Rmax r0 A), (B2R c).
         split; [apply Hmx; lra|]. split; [apply Hmy; lra|]. split; [lra | reflexivity].
      -- apply Hr0e, Rmax_l.
    * apply (pow_pinf_neg emin emax m Hg Hp). left. split; [exact Fc | exact HC0].
  + (* [b = +inf], [c = 0]: [y = {0}], and every value is [r^0 = 1]. *)
    destruct (pn_zero c Fc HC0) as (sc & Ec0). rewrite Ec0.
    apply (pn_lo_at (image2_set pow_dom Rpow x y) 1).
    * apply (proj2 (pn_img x y _ Hy0)). exists (A + 1), 0.
      split; [apply Hmx; lra|]. split; [apply Hmy; lra|]. split; [lra|].
      symmetry. apply Rpow_0_r. lra.
    * intros s Hs. destruct (proj1 (pn_img x y s Hy0) Hs) as (r & t & Hr & Ht & Hr0 & ->).
      apply Hmy in Ht. replace t with 0 by lra. rewrite (Rpow_0_r r Hr0). lra.
    * apply (pow_pinf_zero emin emax m Hrg Hg Hp).
- (* [b = +inf], [c = -inf]: [r^t] for a fixed [t < 0] in [y] tends to 0
     as [r] grows. *)
  rewrite Eb, Ec. apply pn_lo_0; [exact Hpos | |].
  + intros eps He. pose proof (Rmin_l D (-1)). pose proof (Rmin_r D (-1)).
    assert (Ht0 : Rmin D (-1) < 0) by lra.
    destruct (Rpow_base_large_neg (Rmin D (-1)) eps Ht0 He) as (r0 & Hr0 & Hr0e).
    exists (Rpow (Rmax r0 A) (Rmin D (-1))).
    pose proof (Rmax_l r0 A). pose proof (Rmax_r r0 A). split.
    * apply (proj2 (pn_img x y _ Hy0)). exists (Rmax r0 A), (Rmin D (-1)).
      split; [apply Hmx; lra|]. split; [apply Hmy; lra|]. split; [lra | reflexivity].
    * apply Hr0e, Rmax_l.
  + apply (pow_pinf_neg emin emax m Hg Hp). right. reflexivity.
Qed.

(** The upper lane [pow_ru(a, c)] for [0 <= a <= 1], where [x] holds the
    reals of [[a, R1]] for some [R1 > 0]: the least upper bound is at the
    corner [(a, c)], as [r^t] decreases in [r] and, for [r <= 1], in [t].
    It is attained if [a > 0] and [c] is finite. Otherwise the values have
    no upper bound ([a = 0] with [c < 0] or [c = -inf], as [r^t] for a
    fixed [t < 0] grows without bound as [r] tends to 0; [0 < a < 1] with
    [c = -inf]), or the bound is 1 ([a = 0] and [c = 0]: [y = {0}];
    [a = 1] and [c = -inf]: every value is [r^t <= 1^t = 1]). *)
Lemma pn_hi_ac :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall x y a R1 c D,
  is_finite a = true -> 0 <= B2R a <= 1 -> (B2R a = 0 -> a = B754_zero false) ->
  0 < R1 -> B2R a <= R1 ->
  (forall r, mem r x -> B2R a <= r) -> (forall r, B2R a <= r <= R1 -> mem r x) ->
  D <= 0 -> pn_ydesc y c D ->
  lane_ok (image2_set pow_dom Rpow x y) (pow_ru m a c).
Proof.
intros emin emax m Hrg Hg Hp x y a R1 c D Fa HA HAz HR1 HAR Hxa Hax HD0 Hyc.
destruct (pn_yD y c D Hyc) as (HyD & HDy).
assert (Hy0 : forall t, mem t y -> t <= 0) by (intros t Ht; specialize (HyD t Ht); lra).
unfold pow_ru.
destruct (Req_dec (B2R a) 0) as [HA0 | HA0].
- rewrite (HAz HA0).
  (* For [t < 0] in [y], the values [r^t] for [r] in [(0, R1]] have no
     upper bound. *)
  assert (Hunb : forall t, mem t y -> t < 0 ->
    lane_ok (image2_set pow_dom Rpow x y) (B754_infinity false)).
  { intros t Ht Ht0. apply lane_ok_inf. intros M.
    destruct (Rpow_base_small_neg t M Ht0) as (r0 & Hr0 & Hr0M).
    exists (Rpow (Rmin r0 R1) t).
    assert (Hm : 0 < Rmin r0 R1) by (apply Rmin_glb_lt; lra).
    pose proof (Rmin_l r0 R1). pose proof (Rmin_r r0 R1). split.
    - apply (proj2 (pn_img x y _ Hy0)). exists (Rmin r0 R1), t.
      split; [apply Hax; lra|]. split; [exact Ht|]. split; [lra | reflexivity].
    - apply Hr0M. lra. }
  destruct Hyc as [(Fc & HCD & Hmy) | (Ec & Hmy)].
  + assert (HC0' : B2R c <= 0) by lra.
    destruct (Rle_lt_or_eq_dec _ _ HC0') as [HC0 | HC0].
    * rewrite (pow_zero_neg emin emax m Hg Hp RNDU c (or_introl (conj Fc HC0))).
      apply (Hunb (B2R c)); [apply Hmy; lra | exact HC0].
    * (* [y = {0}], and every value is [r^0 = 1]. *)
      destruct (pn_zero c Fc HC0) as (sc & Ec0). rewrite Ec0.
      apply (pn_hi_at (image2_set pow_dom Rpow x y) 1).
      -- apply (proj2 (pn_img x y _ Hy0)). exists R1, 0.
         split; [apply Hax; lra|]. split; [apply Hmy; lra|]. split; [lra|].
         symmetry. apply Rpow_0_r, HR1.
      -- intros s Hs. destruct (proj1 (pn_img x y s Hy0) Hs) as (r & t & Hr & Ht & Hr0 & ->).
         apply Hmy in Ht. replace t with 0 by lra. rewrite (Rpow_0_r r Hr0). lra.
      -- apply (pow_zero_zero emin emax m Hrg Hg Hp).
  + rewrite Ec, (pow_zero_neg emin emax m Hg Hp RNDU _ (or_intror eq_refl)).
    pose proof (Rmin_l D (-1)). pose proof (Rmin_r D (-1)).
    apply (Hunb (Rmin D (-1))); [apply Hmy; lra | lra].
- destruct Hyc as [(Fc & HCD & Hmy) | (Ec & Hmy)].
  + (* [a > 0], [c] finite: the largest value is [a^c]. *)
    apply (pn_hi_at (image2_set pow_dom Rpow x y) (Rpow (B2R a) (B2R c))).
    * apply (proj2 (pn_img x y _ Hy0)). exists (B2R a), (B2R c).
      split; [apply Hax; lra|]. split; [apply Hmy; lra|]. split; [lra | reflexivity].
    * intros s Hs. destruct (proj1 (pn_img x y s Hy0) Hs) as (r & t & Hr & Ht & Hr0 & ->).
      apply Hxa in Hr. apply Hmy in Ht.
      apply Rle_trans with (Rpow (B2R a) t).
      -- apply Rpow_le_base_neg; lra.
      -- apply Rpow_le_exp_le1; lra.
    * apply (pow_fin emin emax m Hrg Hg Hp); [exact Fa | exact Fc | left; lra].
  + rewrite Ec. destruct (Rle_lt_or_eq_dec _ _ (proj2 HA)) as [HA1 | HA1].
    * (* [0 < a < 1], [c = -inf]: [a^t] grows without bound as [t]
         falls. *)
      assert (HA01 : 0 < B2R a < 1) by lra.
      rewrite (pow_lt1_ninf emin emax m Hg Hp RNDU a Fa HA01).
      apply lane_ok_inf. intros M.
      destruct (Rpow_exp_small_lt1 (B2R a) M HA01) as (t0 & Ht0).
      exists (Rpow (B2R a) (Rmin t0 D)). split.
      -- apply (proj2 (pn_img x y _ Hy0)). exists (B2R a), (Rmin t0 D).
         split; [apply Hax; lra|]. split; [apply Hmy, Rmin_r|]. split; [lra | reflexivity].
      -- apply Ht0, Rmin_l.
    * (* [a = 1], [c = -inf]: every value is at most [1^t = 1]. *)
      apply (pn_hi_at (image2_set pow_dom Rpow x y) 1).
      -- apply (proj2 (pn_img x y _ Hy0)). exists (B2R a), D.
         split; [apply Hax; lra|]. split; [exact HDy|]. split; [lra|].
         rewrite HA1. symmetry. apply Rpow_1_l.
      -- intros s Hs. destruct (proj1 (pn_img x y s Hy0) Hs) as (r & t & Hr & Ht & Hr0 & ->).
         apply Hxa in Hr. specialize (HyD t Ht).
         rewrite <- (Rpow_1_l t). apply Rpow_le_base_neg; lra.
      -- apply (pow_one_inf emin emax m Hrg Hg Hp); [exact Fa | exact HA1].
Qed.

(** ** The three cases *)

Lemma pw_neg_empty :
  forall x y, pw_xok x -> valid y -> Interval.is_empty y = false ->
  Model.le (Interval.sup_raw y) Model.zero = true ->
  Model.eq (Interval.sup_raw x) Model.zero = true ->
  forall s, ~ image2_set pow_dom Rpow x y s.
Proof.
intros x y Hx Hyv Hye Hd Hb0 s (r & t & Hr & Ht & Hdom & _).
destruct (pn_y y Hyv Hye Hd) as (_ & HD0 & Hyc).
destruct (pn_yD _ _ _ Hyc) as (HyD & _). specialize (HyD t Ht).
destruct Hx as (Hv & He & _).
destruct (valid_nonempty x Hv He) as (Hlo & Hup & _).
pose proof (proj1 (mem_bounds x r Hlo Hup) Hr) as (_ & Hrb).
unfold Interval.sup_raw in Hb0.
(* [b] is a zero, so [r <= 0], and [t <= 0]: [(r, t)] is not in the
   domain. *)
destruct Hup as [Fb | Eb]; [| rewrite Eb in Hb0; vm_compute in Hb0; discriminate Hb0].
unfold Model.eq in Hb0. rewrite Beqb_correct in Hb0 by first [exact Fb | reflexivity].
change (B2R Model.zero) with 0 in Hb0.
revert Hb0. case Req_bool_spec; [intros Hb _ | discriminate].
rewrite (bound_finite _ Fb) in Hrb. cbv beta iota in Hrb.
destruct Hdom as [Hdom | [_ Hdom]]; lra.
Qed.

Lemma pw_neg_lt1 :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall x y, pw_xok x -> valid y -> Interval.is_empty y = false ->
  Model.le (Interval.sup_raw y) Model.zero = true ->
  Model.eq (Interval.sup_raw x) Model.zero = false ->
  Model.lt (Interval.sup_raw x) (of_u64 1) = true ->
  is_tightest (image2_set pow_dom Rpow x y)
    (Interval.with_infsup_raw (pow_rd m (Interval.sup_raw x) (Interval.sup_raw y))
       (pow_ru m (Interval.inf_raw x) (Interval.inf_raw y))).
Proof.
intros emin emax m Hrg Hg Hp x y Hx Hyv Hye Hd Hb0 Hb1.
destruct (pn_x x Hx Hb0) as (Fa & HA0 & HAz & Hxb).
destruct (pn_y y Hyv Hye Hd) as (Fd & HD0 & Hyc).
destruct (pn_yD _ _ _ Hyc) as (HyD & HDy).
assert (Hy0 : forall t, mem t y -> t <= 0) by (intros t Ht; specialize (HyD t Ht); lra).
destruct Hxb as [(Fb & HB0 & HAB & Hmx) | (Eb & _)];
  [| rewrite Eb in Hb1; vm_compute in Hb1; discriminate Hb1].
rewrite pn_lt_1 in Hb1 by exact Fb.
revert Hb1. case Rlt_bool_spec; [intros HB1 _ | discriminate].
assert (HS : image2_set pow_dom Rpow x y
  (Rpow (B2R (Interval.sup_raw x)) (B2R (Interval.sup_raw y)))).
{ apply (proj2 (pn_img x y _ Hy0)).
  exists (B2R (Interval.sup_raw x)), (B2R (Interval.sup_raw y)).
  split; [apply Hmx; lra|]. split; [exact HDy|]. split; [lra | reflexivity]. }
unfold Interval.with_infsup_raw, Generic.constant. apply tightest_lanes_lub.
- exact (ex_intro _ _ HS).
- (* The least value is [b^d], as [r^t] decreases in [r] and, for
     [r <= 1], in [t]. *)
  unfold pow_rd.
  apply (pn_lo_at (image2_set pow_dom Rpow x y)
    (Rpow (B2R (Interval.sup_raw x)) (B2R (Interval.sup_raw y))) _ HS).
  + intros s Hs. destruct (proj1 (pn_img x y s Hy0) Hs) as (r & t & Hr & Ht & Hr0 & ->).
    apply Hmx in Hr. specialize (HyD t Ht).
    apply Rle_trans with (Rpow (B2R (Interval.sup_raw x)) t).
    * apply Rpow_le_exp_le1; lra.
    * apply Rpow_le_base_neg; lra.
  + apply (pow_fin emin emax m Hrg Hg Hp); [exact Fb | exact Fd | left; lra].
- apply (pn_hi_ac emin emax m Hrg Hg Hp x y (Interval.inf_raw x) (B2R (Interval.sup_raw x))
    (Interval.inf_raw y) (B2R (Interval.sup_raw y)) Fa);
    [lra | exact HAz | lra | lra | | | exact HD0 | exact Hyc].
  + intros r Hr. apply Hmx in Hr. lra.
  + intros r Hr. apply Hmx. lra.
Qed.

Lemma pw_neg_gt1 :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall x y, pw_xok x -> valid y -> Interval.is_empty y = false ->
  Model.le (Interval.sup_raw y) Model.zero = true ->
  Model.eq (Interval.sup_raw x) Model.zero = false ->
  Model.lt (Interval.sup_raw x) (of_u64 1) = false ->
  Model.gt (Interval.inf_raw x) (of_u64 1) = true ->
  is_tightest (image2_set pow_dom Rpow x y)
    (Interval.with_infsup_raw (pow_rd m (Interval.sup_raw x) (Interval.inf_raw y))
       (pow_ru m (Interval.inf_raw x) (Interval.sup_raw y))).
Proof.
intros emin emax m Hrg Hg Hp x y Hx Hyv Hye Hd Hb0 _ Ha1.
destruct (pn_x x Hx Hb0) as (Fa & HA0 & HAz & Hxb).
destruct (pn_y y Hyv Hye Hd) as (Fd & HD0 & Hyc).
destruct (pn_yD _ _ _ Hyc) as (HyD & HDy).
destruct (pn_xA _ _ _ Hxb) as (Hxa & HAx).
assert (Hy0 : forall t, mem t y -> t <= 0) by (intros t Ht; specialize (HyD t Ht); lra).
rewrite pn_gt_1 in Ha1 by exact Fa.
revert Ha1. case Rlt_bool_spec; [intros HA1 _ | discriminate].
assert (HS : image2_set pow_dom Rpow x y
  (Rpow (B2R (Interval.inf_raw x)) (B2R (Interval.sup_raw y)))).
{ apply (proj2 (pn_img x y _ Hy0)).
  exists (B2R (Interval.inf_raw x)), (B2R (Interval.sup_raw y)).
  split; [exact HAx|]. split; [exact HDy|]. split; [lra | reflexivity]. }
unfold Interval.with_infsup_raw, Generic.constant. apply tightest_lanes_lub.
- exact (ex_intro _ _ HS).
- apply (pn_lo_bc emin emax m Hrg Hg Hp x y (B2R (Interval.inf_raw x))
    (Interval.sup_raw x) (Interval.inf_raw y) (B2R (Interval.sup_raw y)));
    [lra | exact Hxb | | exact HD0 | exact Hyc].
  (* A finite [b] is at least [a > 1]. *)
  intros Fb. destruct Hxb as [(_ & _ & HAB & _) | (Eb & _)]; [lra|].
  rewrite Eb in Fb. discriminate Fb.
- (* The largest value is [a^d], as [r^t] decreases in [r] and, for
     [r >= 1], increases in [t]. *)
  unfold pow_ru.
  apply (pn_hi_at (image2_set pow_dom Rpow x y)
    (Rpow (B2R (Interval.inf_raw x)) (B2R (Interval.sup_raw y))) _ HS).
  + intros s Hs. destruct (proj1 (pn_img x y s Hy0) Hs) as (r & t & Hr & Ht & Hr0 & ->).
    apply Hxa in Hr. specialize (HyD t Ht).
    apply Rle_trans with (Rpow (B2R (Interval.inf_raw x)) t).
    * apply Rpow_le_base_neg; lra.
    * apply Rpow_le_exp_ge1; lra.
  + apply (pow_fin emin emax m Hrg Hg Hp); [exact Fa | exact Fd | left; lra].
Qed.

Lemma pw_neg_mid :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall x y, pw_xok x -> valid y -> Interval.is_empty y = false ->
  Model.le (Interval.sup_raw y) Model.zero = true ->
  Model.eq (Interval.sup_raw x) Model.zero = false ->
  Model.lt (Interval.sup_raw x) (of_u64 1) = false ->
  Model.gt (Interval.inf_raw x) (of_u64 1) = false ->
  is_tightest (image2_set pow_dom Rpow x y)
    (Interval.with_infsup_raw (pow_rd m (Interval.sup_raw x) (Interval.inf_raw y))
       (pow_ru m (Interval.inf_raw x) (Interval.inf_raw y))).
Proof.
intros emin emax m Hrg Hg Hp x y Hx Hyv Hye Hd Hb0 Hb1 Ha1.
destruct (pn_x x Hx Hb0) as (Fa & HA0 & HAz & Hxb).
destruct (pn_y y Hyv Hye Hd) as (Fd & HD0 & Hyc).
destruct (pn_yD _ _ _ Hyc) as (HyD & HDy).
destruct (pn_xA _ _ _ Hxb) as (Hxa & _).
assert (Hy0 : forall t, mem t y -> t <= 0) by (intros t Ht; specialize (HyD t Ht); lra).
rewrite pn_gt_1 in Ha1 by exact Fa.
revert Ha1. case Rlt_bool_spec; [discriminate | intros HA1 _].
assert (HbB : is_finite (Interval.sup_raw x) = true -> 1 <= B2R (Interval.sup_raw x)).
{ intros Fb. rewrite pn_lt_1 in Hb1 by exact Fb.
  revert Hb1. case Rlt_bool_spec; [discriminate | intros H _; exact H]. }
(* [a <= 1 <= b], so [x] holds the reals of [[a, 1]]. *)
assert (H1x : forall r, B2R (Interval.inf_raw x) <= r <= 1 -> mem r x).
{ intros r Hr. destruct Hxb as [(Fb & _ & _ & Hmx) | (_ & Hmx)]; apply Hmx.
  - specialize (HbB Fb). lra.
  - lra. }
unfold Interval.with_infsup_raw, Generic.constant. apply tightest_lanes_lub.
- exists (Rpow 1 (B2R (Interval.sup_raw y))).
  apply (proj2 (pn_img x y _ Hy0)). exists 1, (B2R (Interval.sup_raw y)).
  split; [apply H1x; lra|]. split; [exact HDy|]. split; [lra | reflexivity].
- apply (pn_lo_bc emin emax m Hrg Hg Hp x y (B2R (Interval.inf_raw x))
    (Interval.sup_raw x) (Interval.inf_raw y) (B2R (Interval.sup_raw y)));
    [lra | exact Hxb | exact HbB | exact HD0 | exact Hyc].
- apply (pn_hi_ac emin emax m Hrg Hg Hp x y (Interval.inf_raw x) 1
    (Interval.inf_raw y) (B2R (Interval.sup_raw y)) Fa);
    [lra | exact HAz | lra | lra | exact Hxa | exact H1x | exact HD0 | exact Hyc].
Qed.
