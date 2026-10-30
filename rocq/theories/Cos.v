(** * [cos] of intervals encloses the image, and when it is tightest

    [Interval::cos] of [x = [a, b]] computes [q = floor(x / PI)] with
    bounds [qa] and [qb] ([trig_reduce] in [TrigReduce.v]), and
    [n = qb - qa] (0 if [a == b]) and the parity of [qa]. On
    [[k * PI, (k + 1) * PI]], [cos] decreases for even [k] and increases
    for odd [k] ([TrigPieces.v]). Every real of [x] lies in
    [[qa * PI, (qb + 1) * PI)], so: for [n = 0] [x] is in one piece and
    the result is that of a monotone function; for [n = 1] it spans two
    pieces with the minimum -1 (even [qa]) or the maximum 1 (odd [qa])
    between them; otherwise the result is [[-1, 1]]. Each encloses the
    image ([cos_encloses]), for every [x].

    The result is the tightest ([cos_correct]) under [trig_tight]
    ([TrigSpec.v]): if [x] holds one real, as [n] is then 0; if it holds
    two reals [2 * PI] apart, as it then contains both a maximum and a
    minimum and [n >= 2]; or if [q] is the hull of [floor(r / PI)] over
    [x], as every branch then attains its bounds. It is not the tightest
    for every [x]: [[-134241567.2736211, -134241567.27362108]], just below
    [-42730418 * PI], gives [[0.9999999999999989, 1]], where the tightest
    interval is [[0.9999999999999989, 0.9999999999999999]], as [qb] is one
    too large there.

    [DecInterval::cos] keeps the decoration of [x]: [cos] is defined and
    continuous everywhere, and the result is always bounded. So it is the
    strongest decoration ([dec_cos_correct]) if [x] is [com] only when it
    is bounded ([com_common]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr ComCommon Integer
  PiBounds TrigPieces TrigSpec TrigReduce TrigBranch
  AddSub DecBinary MonoInc Sqrt ElemDec.

Open Scope R_scope.

(** ** Helpers *)

(** The tests of [n] and [q] that the branches make, at the constants
    they meet. *)
Lemma cs_eq_zero : Model.eq Model.zero Model.zero = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cs_eq_one : Model.eq (of_u64 1) Model.zero = false.
Proof. vm_compute. reflexivity. Qed.

Lemma cs_inf_eq : Model.eq (B754_infinity false) Model.zero = false.
Proof. vm_compute. reflexivity. Qed.

Lemma cs_inf_le : Model.le (B754_infinity false) (of_u64 1) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma cs_tight_encl : forall s y, is_tightest s y -> encloses s y.
Proof.
intros s y (Hy & Hs & _). split; assumption.
Qed.

Lemma cs_even_succ : forall k, Z.even (k + 1) = negb (Z.even k).
Proof.
intros k. rewrite Z.add_1_r, Z.even_succ, <- Z.negb_even. reflexivity.
Qed.

(** [cos] at the multiple of π after [k * PI]. *)
Lemma cs_cos_succ : forall k, cos ((IZR k + 1) * PI) = if Z.even k then -1 else 1.
Proof.
intros k. rewrite <- plus_IZR, cos_kPI, cs_even_succ. destruct (Z.even k); reflexivity.
Qed.

(** Intervals are convex. *)
Lemma cs_mem_between :
  forall x r t u, valid x -> mem r x -> mem t x -> r <= u <= t -> mem u x.
Proof.
intros x r t u Hx Hr Ht Hu.
destruct (Interval.is_empty x) eqn:Hn; [destruct (mem_empty x r Hx Hn Hr)|].
destruct (valid_nonempty x Hx Hn) as (Ha & Hb & _).
apply (proj2 (mem_bounds x u Ha Hb)).
apply (in_bounds_between _ _ r t u); [| |exact Hu].
- exact (proj1 (mem_bounds x r Ha Hb) Hr).
- exact (proj1 (mem_bounds x t Ha Hb) Ht).
Qed.

(** An unbounded nonempty [x] holds two reals [2 * PI] apart. *)
Lemma cs_unbounded :
  forall x, valid x -> Interval.is_empty x = false ->
  Interval.inf_raw x = B754_infinity true \/ Interval.sup_raw x = B754_infinity false ->
  exists r t, mem r x /\ mem t x /\ 2 * PI <= t - r.
Proof.
intros x Hx Hn Hinf. pose proof PI_RGT_0 as HPI.
destruct (nonempty_mem x Hx Hn) as (r0 & Hr0).
destruct Hinf as [Ea|Eb].
- exists (r0 - 2 * PI), r0. split; [|split; [exact Hr0 | lra]].
  apply (mono_mem_dn x r0); [exact Hr0 | exact Ea | lra].
- exists r0, (r0 + 2 * PI). split; [exact Hr0|]. split; [|lra].
  apply (mono_mem_up x r0); [exact Hr0 | exact Eb | lra].
Qed.

(** [n] is +inf when [qa] or [qb] is infinite. *)
Lemma cs_n_inf :
  forall qa qb, (qa = B754_infinity true \/ is_finite qa = true) ->
  (qb = B754_infinity false \/ is_finite qb = true) ->
  qa = B754_infinity true \/ qb = B754_infinity false ->
  Model.sub qb qa = B754_infinity false.
Proof.
intros qa qb Ha Hb Hinf. apply n_inf; [| | | |exact Hinf].
- destruct Ha as [->|F]; [reflexivity|]. destruct qa; try discriminate F; reflexivity.
- destruct Hb as [->|F]; [reflexivity|]. destruct qb; try discriminate F; reflexivity.
- destruct Ha as [->|F]; intros E; [discriminate E | rewrite E in F; discriminate F].
- destruct Hb as [->|F]; intros E; [discriminate E | rewrite E in F; discriminate F].
Qed.

(** ** [[-1, 1]] *)

Lemma cs_full_encl :
  forall x,
  encloses (image_dom real_dom cos x) (Interval.const_interval (opp (of_u64 1)) (of_u64 1)).
Proof.
intros x. apply br_full_encl. intros r _ _. apply COS_bound.
Qed.

(** [x] holds a maximum and a minimum of [cos] if it holds two reals
    [2 * PI] apart ([cos_wide]), or two consecutive multiples of π. *)
Lemma cs_full_tight :
  forall x r t, valid x -> mem r x -> mem t x -> 2 * PI <= t - r ->
  is_tightest (image_dom real_dom cos x) (Interval.const_interval (opp (of_u64 1)) (of_u64 1)).
Proof.
intros x r t Hx Hr Ht Hrt. apply br_full_tight; [intros u _ _; apply COS_bound|].
destruct (cos_wide r t ltac:(lra)) as (u & v & Hu & Hv & Cu & Cv).
exists u, v.
split; [exact (cs_mem_between x r t u Hx Hr Ht Hu)|]. split; [exact I|]. split; [exact Cu|].
split; [exact (cs_mem_between x r t v Hx Hr Ht Hv)|]. split; [exact I | exact Cv].
Qed.

Lemma cs_full_tight_k :
  forall x k, mem (IZR k * PI) x -> mem ((IZR k + 1) * PI) x ->
  is_tightest (image_dom real_dom cos x) (Interval.const_interval (opp (of_u64 1)) (of_u64 1)).
Proof.
intros x k H0 H1. apply br_full_tight; [intros r _ _; apply COS_bound|].
pose proof (cos_kPI k) as C0. pose proof (cs_cos_succ k) as C1.
destruct (Z.even k).
- exists (IZR k * PI), ((IZR k + 1) * PI).
  exact (conj H0 (conj I (conj C0 (conj H1 (conj I C1))))).
- exists ((IZR k + 1) * PI), (IZR k * PI).
  exact (conj H1 (conj I (conj C1 (conj H0 (conj I C0))))).
Qed.

(** ** The branches with MPFR *)

Section CsBranches.

Variables (emin emax : Z) (m : mpfr).

Hypothesis Hrange : range_ok emin emax.
Hypothesis Hget : get_d_ok emin emax m.
Hypothesis Hc : cos_ok emin emax m.

(** If [a == b], [x] holds the one real [a], and both monotone forms are
    [[cos_rd(a), cos_ru(a)]]. *)
Lemma cs_single :
  forall x, valid x -> Interval.is_empty x = false ->
  Model.eq (Interval.inf_raw x) (Interval.sup_raw x) = true ->
  is_tightest (image_dom real_dom cos x)
    (Interval.with_infsup_raw (cos_rd m (Interval.sup_raw x)) (cos_ru m (Interval.inf_raw x))) /\
  is_tightest (image_dom real_dom cos x)
    (Interval.with_infsup_raw (cos_rd m (Interval.inf_raw x)) (cos_ru m (Interval.sup_raw x))).
Proof using Hrange Hget Hc.
intros x Hx Hn Eab.
destruct (bounds_eq_finite x Hx Hn Eab) as (Fa & Fb & _).
pose proof (proj1 (bounds_eq x Hx Hn) Eab) as Hall.
assert (Hfin : finite_itv x) by exact (conj Hx (conj Hn (conj Fa Fb))).
split.
- apply (br_dec_tight emin emax m real_dom cos (mpfr_cos m) Hrange Hget Hc x Hfin).
  + intros r _. exact I.
  + intros r t Hr Ht _. rewrite (Hall r t Hr Ht). apply Rle_refl.
- apply (br_inc_tight emin emax m real_dom cos (mpfr_cos m) Hrange Hget Hc x Hfin).
  + intros r _. exact I.
  + intros r t Hr Ht _. rewrite (Hall r t Hr Ht). apply Rle_refl.
Qed.

(** [n = 0]: [x] lies in [[k * PI, (k + 1) * PI)], where [cos] is
    monotone. *)
Lemma cs_piece0 :
  forall x k, finite_itv x ->
  IZR k * PI <= B2R (Interval.inf_raw x) -> B2R (Interval.sup_raw x) < (IZR k + 1) * PI ->
  (Z.even k = true ->
   is_tightest (image_dom real_dom cos x)
     (Interval.with_infsup_raw (cos_rd m (Interval.sup_raw x))
        (cos_ru m (Interval.inf_raw x)))) /\
  (Z.even k = false ->
   is_tightest (image_dom real_dom cos x)
     (Interval.with_infsup_raw (cos_rd m (Interval.inf_raw x))
        (cos_ru m (Interval.sup_raw x)))).
Proof using Hrange Hget Hc.
intros x k Hfin Ha Hb.
assert (Hin : forall r, mem r x -> IZR k * PI <= r <= (IZR k + 1) * PI).
{ intros r Hr. apply (finite_itv_mem x r Hfin) in Hr. lra. }
split; intros Ev.
- apply (br_dec_tight emin emax m real_dom cos (mpfr_cos m) Hrange Hget Hc x Hfin).
  + intros r _. exact I.
  + intros r t Hr Ht Hrt.
    exact (cos_piece_dec k r t Ev (proj1 (Hin r Hr)) Hrt (proj2 (Hin t Ht))).
- apply (br_inc_tight emin emax m real_dom cos (mpfr_cos m) Hrange Hget Hc x Hfin).
  + intros r _. exact I.
  + intros r t Hr Ht Hrt.
    exact (cos_piece_inc k r t Ev (proj1 (Hin r Hr)) Hrt (proj2 (Hin t Ht))).
Qed.

(** [n = 1]: [x] lies in [[k * PI, (k + 2) * PI)]. For an even [k],
    [cos] decreases up to [(k + 1) * PI] and then increases, so it is at
    most [cos a] before and at most [cos b] after; it attains -1 there if
    [(k + 1) * PI] is in [x]. An odd [k] is the same upside down. *)
Lemma cs_piece1 :
  forall first x k, finite_itv x ->
  IZR k * PI <= B2R (Interval.inf_raw x) -> B2R (Interval.sup_raw x) < (IZR k + 2) * PI ->
  (Z.even k = true ->
   let y := Interval.with_infsup_raw (opp (of_u64 1))
     (fmax first (cos_ru m (Interval.inf_raw x)) (cos_ru m (Interval.sup_raw x))) in
   encloses (image_dom real_dom cos x) y /\
   (B2R (Interval.inf_raw x) <= (IZR k + 1) * PI <= B2R (Interval.sup_raw x) ->
    is_tightest (image_dom real_dom cos x) y)) /\
  (Z.even k = false ->
   let y := Interval.with_infsup_raw
     (fmin first (cos_rd m (Interval.inf_raw x)) (cos_rd m (Interval.sup_raw x))) (of_u64 1) in
   encloses (image_dom real_dom cos x) y /\
   (B2R (Interval.inf_raw x) <= (IZR k + 1) * PI <= B2R (Interval.sup_raw x) ->
    is_tightest (image_dom real_dom cos x) y)).
Proof using Hrange Hget Hc.
intros first x k Hfin Ha Hb.
assert (Hin : forall r, mem r x ->
  B2R (Interval.inf_raw x) <= r <= B2R (Interval.sup_raw x))
  by (intros r Hr; exact (proj1 (finite_itv_mem x r Hfin) Hr)).
assert (Hk1 : IZR (k + 1) * PI = (IZR k + 1) * PI) by (rewrite plus_IZR; reflexivity).
assert (Hk2 : (IZR (k + 1) + 1) * PI = (IZR k + 2) * PI) by (rewrite plus_IZR; ring).
split; intros Ev; cbv zeta.
- assert (Ev1 : Z.even (k + 1) = false) by (rewrite cs_even_succ, Ev; reflexivity).
  (* Before [(k + 1) * PI], [cos r <= cos a]; after it, [cos r <= cos b]. *)
  assert (Hub : forall r, mem r x -> real_dom r ->
    -1 <= cos r <= Rmax (cos (B2R (Interval.inf_raw x))) (cos (B2R (Interval.sup_raw x)))).
  { intros r Hr _. destruct (Hin r Hr) as [Har Hrb].
    split; [apply COS_bound|].
    destruct (Rle_or_lt r ((IZR k + 1) * PI)) as [H1|H1].
    - eapply Rle_trans; [|apply Rmax_l]. exact (cos_piece_dec k _ r Ev Ha Har H1).
    - eapply Rle_trans; [|apply Rmax_r]. apply (cos_piece_inc (k + 1) r _ Ev1).
      + rewrite Hk1. lra.
      + exact Hrb.
      + rewrite Hk2. lra. }
  split.
  + exact (br_min_encl emin emax m real_dom cos (mpfr_cos m) Hrange Hget Hc first x Hfin I I
      (fun r _ _ => COS_bound r) Hub).
  + intros Hcrit.
    apply (br_min_tight emin emax m real_dom cos (mpfr_cos m) Hrange Hget Hc first x Hfin).
    * intros r _. exact I.
    * intros r _. apply COS_bound.
    * intros r Hr. exact (Hub r Hr I).
    * exists ((IZR k + 1) * PI). split; [exact (proj2 (finite_itv_mem x _ Hfin) Hcrit)|].
      rewrite cs_cos_succ, Ev. reflexivity.
- assert (Ev1 : Z.even (k + 1) = true) by (rewrite cs_even_succ, Ev; reflexivity).
  (* Before [(k + 1) * PI], [cos a <= cos r]; after it, [cos b <= cos r]. *)
  assert (Hlb : forall r, mem r x -> real_dom r ->
    Rmin (cos (B2R (Interval.inf_raw x))) (cos (B2R (Interval.sup_raw x))) <= cos r <= 1).
  { intros r Hr _. destruct (Hin r Hr) as [Har Hrb].
    split; [|apply COS_bound].
    destruct (Rle_or_lt r ((IZR k + 1) * PI)) as [H1|H1].
    - eapply Rle_trans; [apply Rmin_l|]. exact (cos_piece_inc k _ r Ev Ha Har H1).
    - eapply Rle_trans; [apply Rmin_r|]. apply (cos_piece_dec (k + 1) r _ Ev1).
      + rewrite Hk1. lra.
      + exact Hrb.
      + rewrite Hk2. lra. }
  split.
  + exact (br_max_encl emin emax m real_dom cos (mpfr_cos m) Hrange Hget Hc first x Hfin I I
      (fun r _ _ => COS_bound r) Hlb).
  + intros Hcrit.
    apply (br_max_tight emin emax m real_dom cos (mpfr_cos m) Hrange Hget Hc first x Hfin).
    * intros r _. exact I.
    * intros r _. apply COS_bound.
    * intros r Hr. exact (Hlb r Hr I).
    * exists ((IZR k + 1) * PI). split; [exact (proj2 (finite_itv_mem x _ Hfin) Hcrit)|].
      rewrite cs_cos_succ, Ev. reflexivity.
Qed.

End CsBranches.

(** ** [Interval::cos] *)

(** Both theorems at once, as they share the case analysis: the result
    always encloses the image, and is the tightest under [trig_tight].
    Only the branches [n = 1] and [n >= 2] for finite bounds need
    [trig_tight]; the others are tightest for every [x]. *)
Lemma cs_main :
  forall emin emax m has_fma first x,
  range_ok emin emax -> get_d_ok emin emax m -> cos_ok emin emax m -> valid x ->
  exists y, Interval.cos m has_fma first x = Some y /\
    encloses (image_dom real_dom cos x) y /\
    (trig_tight has_fma Interval.PI PI (2 * PI) x -> is_tightest (image_dom real_dom cos x) y).
Proof.
intros emin emax m has_fma first x Hrange Hget Hc Hx.
pose proof PI_RGT_0 as HPI.
destruct (Interval.is_empty x) eqn:Hn.
{ (* An empty [x] is returned, and its image is empty. *)
  exists x. unfold Interval.cos. rewrite Hn. split; [reflexivity|].
  assert (Ht : is_tightest (image_dom real_dom cos x) x).
  { rewrite (valid_empty_eq x Hx Hn). apply tightest_empty. intros u (r & Hr & _).
    exact (mem_nan Interval.EMPTY r eq_refl Hr). }
  split; [exact (cs_tight_encl _ _ Ht) | intros _; exact Ht]. }
destruct (trig_reduce has_fma Interval.PI PI x PI_const Hx Hn) as (z & Hz & Hlo & Hhi).
unfold Interval.cos. rewrite Hn, Hz. cbv beta iota zeta.
destruct (Model.eq (Interval.inf_raw x) (Interval.sup_raw x)) eqn:Eab; cbv beta iota.
{ (* [a == b]: [n = 0], and either branch is the tightest. *)
  rewrite cs_eq_zero. cbv beta iota.
  destruct (cs_single emin emax m Hrange Hget Hc x Hx Hn Eab) as [T1 T2].
  destruct (Model.eq (rem_euclid_2 (Interval.inf_raw (Interval.floor z))) Model.zero);
    cbv beta iota.
  - eexists. split; [reflexivity|].
    split; [exact (cs_tight_encl _ _ T1) | intros _; exact T1].
  - eexists. split; [reflexivity|].
    split; [exact (cs_tight_encl _ _ T2) | intros _; exact T2]. }
assert (Hfull : forall x, Interval.inf_raw x = B754_infinity true \/
    Interval.sup_raw x = B754_infinity false ->
  valid x -> Interval.is_empty x = false ->
  encloses (image_dom real_dom cos x) (Interval.const_interval (opp (of_u64 1)) (of_u64 1)) /\
  (trig_tight has_fma Interval.PI PI (2 * PI) x ->
   is_tightest (image_dom real_dom cos x)
     (Interval.const_interval (opp (of_u64 1)) (of_u64 1)))).
{ (* An unbounded [x] gives [[-1, 1]], the tightest. *)
  intros x' Hinf Hx' Hn'. split; [apply cs_full_encl|]. intros _.
  destruct (cs_unbounded x' Hx' Hn' Hinf) as (r & t & Hr & Ht & Hrt).
  exact (cs_full_tight x' r t Hx' Hr Ht Hrt). }
destruct Hlo as [(Ea & Eqa) | (Fa & Fqa & ka & Hka & Hkpa & _)];
  destruct Hhi as [(Eb & Eqb) | (Fb & Fqb & kb & Hkb & Hkpb)].
- (* [a = -inf] and [b = +inf]: [n = +inf]. *)
  rewrite (cs_n_inf _ _ (or_introl Eqa) (or_introl Eqb) (or_introl Eqa)), cs_inf_eq, cs_inf_le.
  eexists. split; [reflexivity|]. exact (Hfull x (or_introl Ea) Hx Hn).
- rewrite (cs_n_inf _ _ (or_introl Eqa) (or_intror Fqb) (or_introl Eqa)), cs_inf_eq, cs_inf_le.
  eexists. split; [reflexivity|]. exact (Hfull x (or_introl Ea) Hx Hn).
- rewrite (cs_n_inf _ _ (or_intror Fqa) (or_introl Eqb) (or_intror Eqb)), cs_inf_eq, cs_inf_le.
  eexists. split; [reflexivity|]. exact (Hfull x (or_intror Eb) Hx Hn).
- (* Finite bounds: [ka * PI <= a <= b < (kb + 1) * PI], so [ka <= kb], and
     the tests of [n] decide [kb - ka]. *)
  assert (Hfin : finite_itv x) by exact (conj Hx (conj Hn (conj Fa Fb))).
  assert (Hin : forall r, mem r x ->
    B2R (Interval.inf_raw x) <= r <= B2R (Interval.sup_raw x))
    by (intros r Hr; exact (proj1 (finite_itv_mem x r Hfin) Hr)).
  destruct (nonempty_mem x Hx Hn) as (r0 & Hr0).
  pose proof (Hin r0 Hr0) as Hr0'.
  assert (Hk : (ka <= kb)%Z).
  { assert (H : IZR ka < IZR kb + 1).
    { apply (Rmult_lt_reg_r PI); [exact HPI | lra]. }
    rewrite <- plus_IZR in H. apply lt_IZR in H. lia. }
  pose proof (n_small _ _ ka kb Fqa Fqb Hka Hkb Hk) as Hns. cbv zeta in Hns.
  destruct Hns as (Hn0 & Hj).
  destruct (Hj 1%Z ltac:(lia)) as (_ & Hle1 & _).
  rewrite Hn0, Hle1, (rem_euclid_2_int _ ka Fqa Hka).
  (* Under [trig_tight], [x] holds two reals [2 * PI] apart, or [ka] and
     [kb] are the floors of [a / PI] and [b / PI]. *)
  assert (Htt : trig_tight has_fma Interval.PI PI (2 * PI) x ->
    (exists r t, mem r x /\ mem t x /\ 2 * PI <= t - r) \/
    (B2R (Interval.inf_raw x) < (IZR ka + 1) * PI /\
     IZR kb * PI <= B2R (Interval.sup_raw x))).
  { intros [Hs | [Hw | He]].
    - apply (bounds_eq x Hx Hn) in Hs. rewrite Hs in Eab. discriminate Eab.
    - left. exact Hw.
    - right.
      destruct (trig_reduce_exact has_fma Interval.PI PI x z PI_const Hx Hn Hz (He z Hz))
        as [Ea' Eb'].
      specialize (Ea' Fa). specialize (Eb' Fb).
      pose proof (floor_div_bounds PI (B2R (Interval.inf_raw x)) HPI) as Fa'.
      pose proof (floor_div_bounds PI (B2R (Interval.sup_raw x)) HPI) as Fb'.
      rewrite <- Ea', Hka in Fa'. rewrite <- Eb', Hkb in Fb'. lra. }
  destruct (Z.eq_dec (kb - ka) 0) as [D0|D0];
    [|destruct (Z.eq_dec (kb - ka) 1) as [D1|D1]].
  + (* [kb = ka]: one piece. *)
    rewrite (proj2 (Z.eqb_eq _ _) D0). cbv beta iota.
    assert (Ekb : kb = ka) by lia. rewrite Ekb in Hkpb.
    pose proof (cs_piece0 emin emax m Hrange Hget Hc x ka Hfin Hkpa Hkpb) as Hp.
    destruct (Z.even ka) eqn:Ev; cbv beta iota;
      [rewrite cs_eq_zero; pose proof (proj1 Hp eq_refl) as T
      | rewrite cs_eq_one; pose proof (proj2 Hp eq_refl) as T];
      cbv beta iota; (eexists; split; [reflexivity|]);
      (split; [exact (cs_tight_encl _ _ T) | intros _; exact T]).
  + (* [kb = ka + 1]: two pieces, with -1 or 1 between them. *)
    rewrite (proj2 (Z.eqb_neq _ _) D0), (proj2 (Z.leb_le (kb - ka) 1) ltac:(lia)). cbv beta iota.
    assert (Ekb : IZR kb = IZR ka + 1)
      by (replace kb with (ka + 1)%Z by lia; apply plus_IZR).
    rewrite Ekb in Hkpb.
    assert (Hb2 : B2R (Interval.sup_raw x) < (IZR ka + 2) * PI) by lra.
    (* No two reals of [x] are [2 * PI] apart, so [trig_tight] gives the
       exact floors, and [(ka + 1) * PI] is in [x]. *)
    assert (Hcrit : trig_tight has_fma Interval.PI PI (2 * PI) x ->
      B2R (Interval.inf_raw x) <= (IZR ka + 1) * PI <= B2R (Interval.sup_raw x)).
    { intros Ht. destruct (Htt Ht) as [(r & t & Hr & Ht' & Hrt) | [H1 H2]].
      - pose proof (Hin r Hr). pose proof (Hin t Ht'). lra.
      - rewrite Ekb in H2. lra. }
    pose proof (cs_piece1 emin emax m Hrange Hget Hc first x ka Hfin Hkpa Hb2) as Hp.
    destruct (Z.even ka) eqn:Ev; cbv beta iota;
      [rewrite cs_eq_zero; pose proof (proj1 Hp eq_refl) as T
      | rewrite cs_eq_one; pose proof (proj2 Hp eq_refl) as T];
      cbv beta iota; cbv zeta in T; destruct T as [T1 T2];
      (eexists; split; [reflexivity|]);
      (split; [exact T1 | intros Ht; exact (T2 (Hcrit Ht))]).
  + (* [kb >= ka + 2]: [[-1, 1]]. *)
    rewrite (proj2 (Z.eqb_neq _ _) D0), (proj2 (Z.leb_gt (kb - ka) 1) ltac:(lia)). cbv beta iota.
    eexists. split; [reflexivity|]. split; [apply cs_full_encl|].
    intros Ht. destruct (Htt Ht) as [(r & t & Hr & Ht' & Hrt) | [H1 H2]].
    * exact (cs_full_tight x r t Hx Hr Ht' Hrt).
    * (* [(ka + 1) * PI] and [(ka + 2) * PI] are in [x]. *)
      assert (Ekb : IZR ka + 2 <= IZR kb) by (rewrite <- plus_IZR; apply IZR_le; lia).
      assert (H3 : (IZR ka + 2) * PI <= IZR kb * PI)
        by (apply Rmult_le_compat_r; [lra | exact Ekb]).
      apply (cs_full_tight_k x (ka + 1)); rewrite plus_IZR;
        apply (proj2 (finite_itv_mem x _ Hfin)); lra.
Qed.

Theorem cos_encloses :
  forall emin emax m has_fma first x,
  range_ok emin emax -> get_d_ok emin emax m -> cos_ok emin emax m -> valid x ->
  exists y, Interval.cos m has_fma first x = Some y /\
    encloses (image_dom real_dom cos x) y.
Proof.
intros emin emax m has_fma first x Hrange Hget Hc Hx.
destruct (cs_main emin emax m has_fma first x Hrange Hget Hc Hx) as (y & Ey & He & _).
exists y. split; [exact Ey | exact He].
Qed.

Theorem cos_correct :
  forall emin emax m has_fma first x,
  range_ok emin emax -> get_d_ok emin emax m -> cos_ok emin emax m -> valid x ->
  trig_tight has_fma Interval.PI PI (2 * PI) x ->
  exists y, Interval.cos m has_fma first x = Some y /\
    is_tightest (image_dom real_dom cos x) y.
Proof.
intros emin emax m has_fma first x Hrange Hget Hc Hx Ht.
destruct (cs_main emin emax m has_fma first x Hrange Hget Hc Hx) as (y & Ey & _ & Hy).
exists y. split; [exact Ey | exact (Hy Ht)].
Qed.

(** ** [DecInterval::cos] *)

Theorem dec_cos_correct :
  forall emin emax m has_fma first x,
  range_ok emin emax -> get_d_ok emin emax m -> cos_ok emin emax m ->
  valid (itv x) -> com_common x ->
  exists y, DecInterval.cos m has_fma first x = Some y /\
    if DecInterval.is_nai x then y = DecInterval.NAI
    else
      encloses (image_dom real_dom cos (itv x)) (itv y) /\
      (trig_tight has_fma Interval.PI PI (2 * PI) (itv x) ->
       is_tightest (image_dom real_dom cos (itv x)) (itv y)) /\
      exists d, strongest_dom real_dom d cos (itv x) (itv y) /\
        dec y = dec_min d (dec x).
Proof.
intros emin emax m has_fma first x Hrange Hget Hc Hx Hcc.
destruct (cs_main emin emax m has_fma first (itv x) Hrange Hget Hc Hx) as (y & Ey & He & Ht).
unfold DecInterval.cos. rewrite Ey. cbv beta iota.
exists (DecInterval.set_dec y (dec x)). split; [reflexivity|].
destruct (DecInterval.is_nai x) eqn:Enai.
- (* NaI: [set_dec] of [ill] is NaI. *)
  unfold DecInterval.is_nai, dec_eqb in Enai. revert Enai.
  destruct (dec x); intros Enai; cbn in Enai; try discriminate Enai. reflexivity.
- assert (Hd : dec x <> Ill).
  { intros E. unfold DecInterval.is_nai in Enai. rewrite E in Enai.
    vm_compute in Enai. discriminate Enai. }
  (* An empty [x] is returned as it is. *)
  assert (Hempty : (forall r, ~ mem r (itv x)) -> Interval.is_empty y = true).
  { intros Hno. destruct (Interval.is_empty (itv x)) eqn:Ex.
    - unfold Interval.cos in Ey. rewrite Ex in Ey. cbv beta iota in Ey.
      injection Ey as E'. rewrite <- E'. exact Ex.
    - destruct (nonempty_mem _ Hx Ex) as (r & Hr). destruct (Hno r Hr). }
  (* [cos] is continuous and defined everywhere, so [e = com]; a [com]
     [x] is common ([com_common]), so bounded. *)
  pose proof (trig_set_dec_correct real_dom cos x y Com Hx Hd He Hempty
    (fun r _ _ => continuity_pt_continue_in cos real_dom r (continuity_cos r))
    (or_intror (conj eq_refl (conj (fun r _ => I)
      (fun Ed _ => common_bounded _ (Hcc Ed)))))) as T.
  cbv zeta in T. rewrite dec_min_Com_r in T.
  destruct T as (T1 & T2 & _ & T4).
  split; [exact T1|]. split.
  + intros Htt. exact (T2 (Ht Htt)).
  + apply T4. intros E. discriminate E.
Qed.
