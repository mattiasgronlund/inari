(** * [Interval::pow] and [DecInterval::pow]

    [pow_correct]: [Interval::pow] returns the tightest interval that
    contains the image of the box [x × y] under IEEE 1788's [pow], defined
    on [pow_dom], for every first argument that Rust's [f64::min] and
    [f64::max] may return for equal zeros. [dec_pow_correct]: its decorated
    version returns NaI for NaI, and otherwise the same interval with the
    strongest decoration ([strongest2_set]), lowered to those of the
    arguments. The decoration needs [com_common] for both arguments, as an
    unbounded argument can give a bounded result: the image of
    [[2, +inf] × [-1, -0.5]] is [(0, 2^-0.5]]. Both assume what [Mpfr.v]
    says of MPFR. *)

From Stdlib Require Import ZArith Reals Lra Classical_Prop.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Integer Sign MaxMin AddSub
  DecBinary DivTight MpfrRound Interior ComCommon Dom2 PowReal PowMpfr PowCases
  PowNeg PowPos PowMix.

Open Scope R_scope.

(** ** The image and the box *)

(** If [either_empty] holds, the image has no element. *)
Lemma pw_empty_img :
  forall x y, valid x -> valid y ->
  Interval.either_empty x y = true -> forall s, ~ image2_set pow_dom Rpow x y s.
Proof.
intros x y Hx Hy Ee s (r & t & Hr & Ht & _).
unfold Interval.either_empty in Ee. apply Bool.orb_true_iff in Ee.
destruct Ee as [E|E]; [exact (mem_empty x r Hx E Hr) | exact (mem_empty y t Hy E Ht)].
Qed.

(** The box is not in the domain if the image over the intersection of
    [x] with [[0, +inf]] is empty: a point of the domain in the box has
    [r >= 0], so it is in that intersection. *)
Lemma pw_trv_img :
  forall x y, valid x ->
  (forall s, ~ image2_set pow_dom Rpow (Interval.intersection x dom_nonneg) y s) ->
  ~ ((exists r, mem r x) /\ (exists t, mem t y) /\
     forall r t, mem r x -> mem t y -> pow_dom r t).
Proof.
intros x y Hx He ((r & Hr) & (t & Ht) & Hd).
apply (He (Rpow r t)), (pw_image_inter x y _ Hx).
exists r, t. exact (conj Hr (conj Ht (conj (Hd r t Hr Ht) eq_refl))).
Qed.

(** A point of the box outside the domain. *)
Lemma pw_trv_pt :
  forall x y r t, mem r x -> mem t y -> ~ pow_dom r t ->
  ~ ((exists r, mem r x) /\ (exists t, mem t y) /\
     forall r t, mem r x -> mem t y -> pow_dom r t).
Proof.
intros x y r t Hr Ht Hn (_ & _ & Hd). exact (Hn (Hd r t Hr Ht)).
Qed.

(** ** The bounds as reals *)

(** [y] has a real at most 0 if its lower bound [c] is not above 0: any
    real of [y] if it has no real above 0, and else 0, as [c <= 0] is
    below that real. *)
Lemma pw_y_le0 :
  forall y, valid y -> Interval.is_empty y = false ->
  Model.gt (Interval.inf_raw y) Model.zero = false -> exists t, mem t y /\ t <= 0.
Proof.
intros y Hv He Hc.
destruct (valid_nonempty y Hv He) as (Hlo & Hup & _).
assert (Hm := fun t => mem_bounds y t Hlo Hup).
destruct (nonempty_mem y Hv He) as (t0 & Ht0).
destruct (Rle_dec t0 0) as [H0|H0]; [exists t0; exact (conj Ht0 H0)|].
apply Rnot_le_lt in H0.
exists 0. split; [|lra]. apply Hm. apply Hm in Ht0.
unfold in_bounds in Ht0 |- *. destruct Ht0 as [_ Hd0]. split.
- unfold Interval.inf_raw in Hc. destruct Hlo as [Fc | Ec].
  + rewrite (bound_finite _ Fc). cbv beta iota.
    unfold Model.gt in Hc. rewrite Bltb_correct in Hc by first [reflexivity | exact Fc].
    change (B2R Model.zero) with 0 in Hc.
    revert Hc. case Rlt_bool_spec; [discriminate | intros H _; exact H].
  + rewrite Ec, bound_inf. exact I.
- destruct (bound (snd (rep y))); [lra | exact I].
Qed.

(** Every real of [y] is above 0 if its lower bound is. *)
Lemma pw_y_pos :
  forall y, valid y -> Interval.is_empty y = false ->
  Model.gt (Interval.inf_raw y) Model.zero = true -> forall t, mem t y -> 0 < t.
Proof.
intros y Hv He Hc t Ht.
destruct (valid_nonempty y Hv He) as (Hlo & Hup & _).
apply (mem_bounds y t Hlo Hup) in Ht. unfold in_bounds in Ht. destruct Ht as [Hct _].
unfold Interval.inf_raw in Hc.
(* [c = -inf] is not above 0. *)
destruct Hlo as [Fc | Ec]; [| rewrite Ec in Hc; vm_compute in Hc; discriminate Hc].
rewrite (bound_finite _ Fc) in Hct. cbv beta iota in Hct.
unfold Model.gt in Hc. rewrite Bltb_correct in Hc by first [reflexivity | exact Fc].
change (B2R Model.zero) with 0 in Hc.
revert Hc. case Rlt_bool_spec; [intros H _; lra | discriminate].
Qed.

(** Every real of [x] is at most 0 if its upper bound is a zero. *)
Lemma pw_sup_zero :
  forall x r, valid x -> Interval.is_empty x = false ->
  Model.eq (Interval.sup_raw x) Model.zero = true -> mem r x -> r <= 0.
Proof.
intros x r Hv He Hb Hr.
destruct (valid_nonempty x Hv He) as (Hlo & Hup & _).
apply (mem_bounds x r Hlo Hup) in Hr. unfold in_bounds in Hr. destruct Hr as [_ Hrb].
unfold Interval.sup_raw in Hb.
(* [b = +inf] is no zero. *)
destruct Hup as [Fb | Eb]; [| rewrite Eb in Hb; vm_compute in Hb; discriminate Hb].
rewrite (bound_finite _ Fb) in Hrb. cbv beta iota in Hrb.
unfold Model.eq in Hb. rewrite Beqb_correct in Hb by first [reflexivity | exact Fb].
change (B2R Model.zero) with 0 in Hb.
revert Hb. case Req_bool_spec; [intros E _; lra | discriminate].
Qed.

(** ** The decorations that [Interval::pow] picks *)

(** [interior(DOM)] gives [com] exactly when every real of [x] is above 0.
    Otherwise some real [r] of [x] is at most 0, and with a real [t] of [y]
    at most 0, [(r, t)] is not in the domain. *)
Lemma pw_dec_interior :
  forall x y, valid x -> (exists t, mem t y /\ t <= 0) ->
  ((if Interval.interior x dom_nonneg then Com else Trv) = Trv /\
   ~ ((exists r, mem r x) /\ (exists t, mem t y) /\
      forall r t, mem r x -> mem t y -> pow_dom r t)) \/
  ((if Interval.interior x dom_nonneg then Com else Trv) = Com /\
   (forall r t, mem r x -> mem t y -> pow_dom r t)).
Proof.
intros x y Hx (t & Ht & Ht0).
destruct (Interval.interior x dom_nonneg) eqn:Ei.
- right. split; [reflexivity|]. intros r u Hr _. left.
  exact (proj1 (pw_interior x Hx) Ei r Hr).
- left. split; [reflexivity|].
  destruct (classic (exists r, mem r x /\ r <= 0)) as [(r & Hr & Hr0) | N].
  + apply (pw_trv_pt x y r t Hr Ht). intros [H|[_ H]]; lra.
  + exfalso.
    assert (H : forall r, mem r x -> 0 < r).
    { intros r Hr. apply Rnot_le_lt. intros Hle. apply N. exists r. exact (conj Hr Hle). }
    apply (pw_interior x Hx) in H. rewrite Ei in H. discriminate H.
Qed.

(** For [y] above 0, [subset(DOM)] gives [com] exactly when no real of [x]
    is below 0: the domain then holds [(0, t)] too. Otherwise some real of
    [x] is below 0, and no point with it is in the domain. *)
Lemma pw_dec_subset :
  forall x y, valid x -> (forall t, mem t y -> 0 < t) ->
  ((if Interval.subset x dom_nonneg then Com else Trv) = Trv /\
   ~ ((exists r, mem r x) /\ (exists t, mem t y) /\
      forall r t, mem r x -> mem t y -> pow_dom r t)) \/
  ((if Interval.subset x dom_nonneg then Com else Trv) = Com /\
   (forall r t, mem r x -> mem t y -> pow_dom r t)).
Proof.
intros x y Hx Hy.
destruct (Interval.subset x dom_nonneg) eqn:Es.
- right. split; [reflexivity|]. intros r t Hr Ht.
  pose proof (proj1 (pw_subset x Hx) Es r Hr) as H0.
  destruct (Rle_lt_or_eq_dec 0 r H0) as [H|H]; [left; exact H|].
  right. split; [symmetry; exact H | exact (Hy t Ht)].
- left. split; [reflexivity|]. intros (_ & (t & Ht) & Hd).
  destruct (classic (exists r, mem r x /\ r < 0)) as [(r & Hr & Hr0) | N].
  + destruct (Hd r t Hr Ht) as [H|[H _]]; lra.
  + assert (H : forall r, mem r x -> 0 <= r).
    { intros r Hr. apply Rnot_lt_le. intros Hlt. apply N. exists r. exact (conj Hr Hlt). }
    apply (pw_subset x Hx) in H. rewrite Es in H. discriminate H.
Qed.

(** The decoration of [Interval::pow] is [trv] only if the box is not in
    the domain, and [com] only if it is, by the same case split as the
    interval. *)
Lemma pw_dec_cases :
  forall m first_min first_max x y, valid x -> valid y ->
  (snd (Interval.pow_impl m first_min first_max x y) = Trv /\
   ~ ((exists r, mem r x) /\ (exists t, mem t y) /\
      forall r t, mem r x -> mem t y -> pow_dom r t)) \/
  (snd (Interval.pow_impl m first_min first_max x y) = Com /\
   (forall r t, mem r x -> mem t y -> pow_dom r t)).
Proof.
intros m f1 f2 x y Hx Hy.
pose proof (pw_inter_valid x Hx) as Hx'.
unfold Interval.pow_impl; cbv zeta. fold dom_nonneg.
destruct (Interval.either_empty (Interval.intersection x dom_nonneg) y) eqn:Ee.
- left. split; [reflexivity|].
  exact (pw_trv_img x y Hx (pw_empty_img _ y Hx' Hy Ee)).
- unfold Interval.either_empty in Ee. apply Bool.orb_false_iff in Ee.
  destruct Ee as (Ex & Ey).
  pose proof (pw_xok_inter x Hx Ex) as Hxok.
  set (x' := Interval.intersection x dom_nonneg) in *.
  destruct (Model.le (Interval.sup_raw y) Model.zero) eqn:Ed.
  + destruct (Model.eq (Interval.sup_raw x') Model.zero) eqn:Eb.
    * (* No point of the domain: the image over [x'] is empty. *)
      left. split; [reflexivity|].
      exact (pw_trv_img x y Hx (pw_neg_empty x' y Hxok Hy Ey Ed Eb)).
    * (* Every real of [y] is at most [d <= 0]. *)
      assert (Hty : exists t, mem t y /\ t <= 0).
      { destruct (pn_y y Hy Ey Ed) as (_ & HD0 & Hyc).
        destruct (pn_yD _ _ _ Hyc) as (_ & HD).
        exists (B2R (Interval.sup_raw y)). exact (conj HD HD0). }
      pose proof (pw_dec_interior x y Hx Hty) as K.
      destruct (Model.lt (Interval.sup_raw x') (of_u64 1));
        [|destruct (Model.gt (Interval.inf_raw x') (of_u64 1))]; exact K.
  + destruct (Model.gt (Interval.inf_raw y) Model.zero) eqn:Ec.
    * pose proof (pw_dec_subset x y Hx (pw_y_pos y Hy Ey Ec)) as K.
      destruct (Model.lt (Interval.sup_raw x') (of_u64 1));
        [|destruct (Model.gt (Interval.inf_raw x') (of_u64 1))]; exact K.
    * destruct (Model.eq (Interval.sup_raw x') Model.zero) eqn:Eb.
      -- (* [x'] is [{0}], so 0 is in [x], and [y] has a real at most 0. *)
         left. split; [reflexivity|].
         destruct (nonempty_mem x' Hx' Ex) as (r & Hr).
         pose proof (pw_sup_zero x' r Hx' Ex Eb Hr) as Hr0.
         apply (pw_inter_mem x r Hx) in Hr. destruct Hr as (Hr & Hr1).
         destruct (pw_y_le0 y Hy Ey Ec) as (t & Ht & Ht0).
         apply (pw_trv_pt x y r t Hr Ht). intros [H|[_ H]]; lra.
      -- exact (pw_dec_interior x y Hx (pw_y_le0 y Hy Ey Ec)).
Qed.

(** ** The theorems *)

Theorem pow_correct :
  forall emin emax m first_min first_max x y,
  range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  valid x -> valid y ->
  is_tightest (image2_set pow_dom Rpow x y) (Interval.pow m first_min first_max x y).
Proof.
intros emin emax m f1 f2 x y Hrg Hg Hp Hx Hy.
pose proof (pw_inter_valid x Hx) as Hx'.
(* The image is that over the intersection [x'] of [x] with
   [DOM = [0, +inf]]. *)
apply (is_tightest_ext (image2_set pow_dom Rpow (Interval.intersection x dom_nonneg) y)).
{ intros s. symmetry. exact (pw_image_inter x y s Hx). }
unfold Interval.pow, Interval.pow_impl; cbv zeta. fold dom_nonneg.
destruct (Interval.either_empty (Interval.intersection x dom_nonneg) y) eqn:Ee.
- apply tightest_empty. exact (pw_empty_img _ y Hx' Hy Ee).
- unfold Interval.either_empty in Ee. apply Bool.orb_false_iff in Ee.
  destruct Ee as (Ex & Ey).
  pose proof (pw_xok_inter x Hx Ex) as Hxok.
  set (x' := Interval.intersection x dom_nonneg) in *.
  destruct (Model.le (Interval.sup_raw y) Model.zero) eqn:Ed.
  + (* [d <= 0] *)
    destruct (Model.eq (Interval.sup_raw x') Model.zero) eqn:Eb.
    * apply tightest_empty. exact (pw_neg_empty x' y Hxok Hy Ey Ed Eb).
    * destruct (Model.lt (Interval.sup_raw x') (of_u64 1)) eqn:Eb1;
        [exact (pw_neg_lt1 emin emax m Hrg Hg Hp x' y Hxok Hy Ey Ed Eb Eb1)|].
      destruct (Model.gt (Interval.inf_raw x') (of_u64 1)) eqn:Ea1.
      -- exact (pw_neg_gt1 emin emax m Hrg Hg Hp x' y Hxok Hy Ey Ed Eb Eb1 Ea1).
      -- exact (pw_neg_mid emin emax m Hrg Hg Hp x' y Hxok Hy Ey Ed Eb Eb1 Ea1).
  + destruct (Model.gt (Interval.inf_raw y) Model.zero) eqn:Ec.
    * (* [c > 0] *)
      destruct (Model.lt (Interval.sup_raw x') (of_u64 1)) eqn:Eb1;
        [exact (pw_pos_lt1 emin emax m Hrg Hg Hp x' y Hxok Hy Ey Ed Ec Eb1)|].
      destruct (Model.gt (Interval.inf_raw x') (of_u64 1)) eqn:Ea1.
      -- exact (pw_pos_gt1 emin emax m Hrg Hg Hp x' y Hxok Hy Ey Ed Ec Eb1 Ea1).
      -- exact (pw_pos_mid emin emax m Hrg Hg Hp x' y Hxok Hy Ey Ed Ec Eb1 Ea1).
    * (* [c <= 0 < d] *)
      destruct (Model.eq (Interval.sup_raw x') Model.zero) eqn:Eb.
      -- exact (pw_mix_zero x' y Hxok Hy Ey Ed Eb).
      -- exact (pw_mix emin emax m Hrg Hg Hp f1 f2 x' y Hxok Hy Ey Ed Ec Eb).
Qed.

Theorem dec_pow_correct :
  forall emin emax m first_min first_max x y,
  range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  valid (itv x) -> valid (itv y) -> com_common x -> com_common y ->
  let z := DecInterval.pow m first_min first_max x y in
  if DecInterval.is_nai x || DecInterval.is_nai y then z = DecInterval.NAI
  else
    is_tightest (image2_set pow_dom Rpow (itv x) (itv y)) (itv z) /\
    exists d, strongest2_set pow_dom d Rpow (itv x) (itv y) (itv z) /\
      dec z = dec_min d (dec_min (dec x) (dec y)).
Proof.
intros emin emax m f1 f2 x y Hrg Hg Hp Hx Hy Cx Cy.
unfold DecInterval.pow.
apply (elem_dec2_impl_correct pow_dom Rpow (Interval.pow_impl m f1 f2) x y Hx Hy).
- exact (pow_correct emin emax m f1 f2 (itv x) (itv y) Hrg Hg Hp Hx Hy).
- intros r t _ _ Hd. exact (Rpow_continuous r t Hd).
- destruct (pw_dec_cases m f1 f2 (itv x) (itv y) Hx Hy) as [K | (Kc & Kd)];
    [left; exact K|].
  (* [com] needs both arguments bounded if they are [com]. *)
  right. split; [exact Kc|]. split; [exact Kd|].
  intros Ex Ey _. split; apply common_bounded; [exact (Cx Ex) | exact (Cy Ey)].
Qed.
