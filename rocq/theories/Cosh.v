(** * [cosh] of intervals and decorated intervals

    [cosh] decreases on [(-inf, 0]] and increases on [[0, +inf)], so
    [Interval::cosh] of [[a, b]] is [[cosh_rd(b), cosh_ru(a)]] if [b < 0],
    [[cosh_rd(a), cosh_ru(b)]] if [a > 0], and otherwise
    [[1, cosh_ru(max(-a, b))]], as [cosh] is even and [cosh 0 = 1]. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr
  Integer Sign MaxMin AddSub MulTight DecBinary DivTight Sqrt MpfrRound ExpReal ElemDec
  MonoInc.

Open Scope R_scope.

(** ** Helpers *)

(** [lt] of two finite floats compares their reals. *)
Lemma ch_lt_fin :
  forall u v, is_finite u = true -> is_finite v = true ->
  (Model.lt u v = true -> B2R u < B2R v) /\ (Model.lt u v = false -> B2R v <= B2R u).
Proof.
intros u v Fu Fv. unfold Model.lt. rewrite Bltb_correct by assumption.
case Rlt_bool_spec; intros H; split; intros E; first [lra | discriminate E].
Qed.

(** The bounds of a nonempty interval are not NaN. *)
Lemma ch_lower_not_nan : forall w, lower_ok w -> is_nan w = false.
Proof.
intros w [Fw| ->]; [|reflexivity].
destruct w; try discriminate Fw; reflexivity.
Qed.

Lemma ch_upper_not_nan : forall w, upper_ok w -> is_nan w = false.
Proof.
intros w [Fw| ->]; [|reflexivity].
destruct w; try discriminate Fw; reflexivity.
Qed.

(** [fmax] of two finite floats is finite, with the larger real, whichever
    of two equal floats (+0 and -0) it returns. *)
Lemma ch_fmax_fin :
  forall first x y, is_finite x = true -> is_finite y = true ->
  is_finite (fmax first x y) = true /\ B2R (fmax first x y) = Rmax (B2R x) (B2R y).
Proof.
intros first x y Fx Fy.
destruct (ch_lt_fin x y Fx Fy) as [Hxy Hxy'].
destruct (ch_lt_fin y x Fy Fx) as [Hyx Hyx'].
unfold fmax.
destruct (Model.lt x y) eqn:Exy.
- split; [exact Fy|]. rewrite Rmax_right; [reflexivity|]. specialize (Hxy eq_refl). lra.
- specialize (Hxy' eq_refl).
  destruct (Model.lt y x) eqn:Eyx.
  + split; [exact Fx|]. rewrite Rmax_left; [reflexivity|]. lra.
  + (* Neither is less, so their reals are equal. *)
    specialize (Hyx' eq_refl).
    destruct first; (split; [assumption|]).
    * rewrite Rmax_left; [reflexivity|]. lra.
    * rewrite Rmax_right; [reflexivity|]. lra.
Qed.

(** [fmax] with +inf, and an argument that is not NaN, is +inf. *)
Lemma ch_fmax_inf_l :
  forall first y, is_nan y = false -> fmax first (B754_infinity false) y = B754_infinity false.
Proof.
intros first [s|[|]| |s my ey Hy] Hn; try discriminate Hn; destruct first; reflexivity.
Qed.

Lemma ch_fmax_inf_r :
  forall first x, is_nan x = false -> fmax first x (B754_infinity false) = B754_infinity false.
Proof.
intros first [s|[|]| |s mx ex Hx] Hn; try discriminate Hn; destruct first; reflexivity.
Qed.

(** MPFR's [cosh] of an infinity, rounded up, is +inf. *)
Lemma ch_ru_inf :
  forall emin emax m s, get_d_ok emin emax m -> cosh_ok emin emax m ->
  cosh_ru m (B754_infinity s) = B754_infinity false.
Proof.
intros emin emax m s Hget Hc.
exact (mpfr_fn_inf emin emax m (mpfr_cosh m) RNDU s false Hget (proj2 Hc s)).
Qed.

(** [cosh] is even and increasing on [[0, +inf)], so it is at most
    [cosh c] at every real [r] with [|r| <= c]. *)
Lemma ch_abs_le : forall r c, Rabs r <= c -> cosh r <= cosh c.
Proof.
intros r c H. destruct (Rle_or_lt 0 r) as [Hr|Hr].
- rewrite Rabs_pos_eq in H by exact Hr. exact (cosh_inc r c Hr H).
- rewrite Rabs_left in H by exact Hr. rewrite <- (cosh_even r).
  apply cosh_inc; lra.
Qed.

Lemma ch_opp_not_nan : forall w, is_nan w = false -> is_nan (opp w) = false.
Proof.
intros w H. unfold opp. rewrite is_nan_Bopp. exact H.
Qed.

(** A nonempty interval with no bound on the wrong side of 0 holds 0. *)
Lemma ch_mem_0 :
  forall x, valid x -> Interval.is_empty x = false ->
  (is_finite (opp (fst (rep x))) = true -> B2R (opp (fst (rep x))) <= 0) ->
  (is_finite (snd (rep x)) = true -> 0 <= B2R (snd (rep x))) ->
  mem 0 x.
Proof.
intros x Hx Hn Ha0 Hb0.
destruct (valid_nonempty x Hx Hn) as (Ha & Hb & _).
apply (mem_bounds x 0 Ha Hb). unfold in_bounds. split.
- destruct Ha as [Fa|Ea]; [rewrite (bound_finite _ Fa); exact (Ha0 Fa) | rewrite Ea; exact I].
- destruct Hb as [Fb|Eb]; [rewrite (bound_finite _ Fb); exact (Hb0 Fb) | rewrite Eb; exact I].
Qed.

(** ** The three branches of [Interval::cosh] *)

Section ChBranches.

Variables (emin emax : Z) (m : mpfr) (first : bool).

Hypothesis Hrange : range_ok emin emax.
Hypothesis Hget : get_d_ok emin emax m.
Hypothesis Hc : cosh_ok emin emax m.

(** If [b < 0], [cosh] decreases on [x], so its least value on [x] is
    [cosh b], and its largest [cosh a], or it has none if [a = -inf]. *)
Lemma ch_neg :
  forall x, valid x -> Interval.is_empty x = false ->
  is_finite (snd (rep x)) = true -> B2R (snd (rep x)) < 0 ->
  is_tightest (image_dom real_dom cosh x)
    (Interval.with_infsup_raw (cosh_rd m (snd (rep x))) (cosh_ru m (opp (fst (rep x))))).
Proof using Hrange Hget Hc.
intros x Hx Hn Fb Hb.
destruct (nonempty_mem x Hx Hn) as (r0 & Hr0).
unfold Interval.with_infsup_raw, Generic.constant.
apply tightest_lanes_lub.
- exists (cosh r0), r0. split; [exact Hr0 | split; [exact I | reflexivity]].
- (* [b] is in [x], and [cosh_rd b] is [cosh b] rounded down. *)
  exists (Some (- cosh (B2R (snd (rep x))))). split.
  + apply tight_lub, tight_Some. split.
    * exists (B2R (snd (rep x))).
      split; [exact (mono_mem_sup x Hx Hn Fb) | split; [exact I | apply Ropp_involutive]].
    * intros s (r & Hr & _ & Hs).
      pose proof (cosh_dec r _ (mono_mem_le_sup x r Hr Fb) (Rlt_le _ _ Hb)). lra.
  + apply round_dn_lane.
    exact (mpfr_fn_correct emin emax m real_dom cosh (mpfr_cosh m) Hrange Hget (proj1 Hc)
      RNDD _ Fb I).
- destruct (valid_nonempty x Hx Hn) as ([Fa|Ea] & _ & _).
  + (* A finite [a] is in [x], and [cosh_ru a] is [cosh a] rounded up. *)
    exists (Some (cosh (B2R (opp (fst (rep x)))))). split.
    * apply tight_lub, tight_Some. split.
      -- exists (B2R (opp (fst (rep x)))).
         split; [exact (mono_mem_inf x Hx Hn Fa) | split; [exact I | reflexivity]].
      -- intros s (r & Hr & _ & ->).
         apply cosh_dec; [exact (mono_inf_le_mem x r Hr Fa)|].
         pose proof (mono_mem_le_sup x r Hr Fb). lra.
    * apply round_up_lane.
      exact (mpfr_fn_correct emin emax m real_dom cosh (mpfr_cosh m) Hrange Hget (proj1 Hc)
        RNDU _ Fa I).
  + (* At [a = -inf], [x] holds every real below [r0], and [cosh] of
       [-r] is [cosh r], which rises without bound. *)
    rewrite Ea, (ch_ru_inf emin emax m true Hget Hc). apply lane_ok_inf. intros M.
    destruct (cosh_unbounded M) as (r & Hr & HM).
    exists (cosh (Rmin (- r) r0)). split.
    * exists (Rmin (- r) r0). split; [|split; [exact I | reflexivity]].
      exact (mono_mem_dn x r0 _ Hr0 Ea (Rmin_r _ _)).
    * assert (Hr' : - r <= 0) by lra.
      pose proof (cosh_dec _ _ (Rmin_l (- r) r0) Hr') as H1.
      rewrite cosh_even in H1. lra.
Qed.

(** If [a > 0], [cosh] increases on [x], so its least value on [x] is
    [cosh a], and its largest [cosh b], or it has none if [b = +inf]. *)
Lemma ch_pos :
  forall x, valid x -> Interval.is_empty x = false ->
  is_finite (opp (fst (rep x))) = true -> 0 < B2R (opp (fst (rep x))) ->
  is_tightest (image_dom real_dom cosh x)
    (Interval.with_infsup_raw (cosh_rd m (opp (fst (rep x)))) (cosh_ru m (snd (rep x)))).
Proof using Hrange Hget Hc.
intros x Hx Hn Fa Ha.
destruct (nonempty_mem x Hx Hn) as (r0 & Hr0).
unfold Interval.with_infsup_raw, Generic.constant.
apply tightest_lanes_lub.
- exists (cosh r0), r0. split; [exact Hr0 | split; [exact I | reflexivity]].
- (* [a] is in [x], and [cosh_rd a] is [cosh a] rounded down. *)
  exists (Some (- cosh (B2R (opp (fst (rep x)))))). split.
  + apply tight_lub, tight_Some. split.
    * exists (B2R (opp (fst (rep x)))).
      split; [exact (mono_mem_inf x Hx Hn Fa) | split; [exact I | apply Ropp_involutive]].
    * intros s (r & Hr & _ & Hs).
      pose proof (cosh_inc _ r (Rlt_le _ _ Ha) (mono_inf_le_mem x r Hr Fa)). lra.
  + apply round_dn_lane.
    exact (mpfr_fn_correct emin emax m real_dom cosh (mpfr_cosh m) Hrange Hget (proj1 Hc)
      RNDD _ Fa I).
- destruct (valid_nonempty x Hx Hn) as (_ & [Fb|Eb] & _).
  + (* A finite [b] is in [x], and [cosh_ru b] is [cosh b] rounded up. *)
    exists (Some (cosh (B2R (snd (rep x))))). split.
    * apply tight_lub, tight_Some. split.
      -- exists (B2R (snd (rep x))).
         split; [exact (mono_mem_sup x Hx Hn Fb) | split; [exact I | reflexivity]].
      -- intros s (r & Hr & _ & ->).
         apply cosh_inc; [|exact (mono_mem_le_sup x r Hr Fb)].
         pose proof (mono_inf_le_mem x r Hr Fa). lra.
    * apply round_up_lane.
      exact (mpfr_fn_correct emin emax m real_dom cosh (mpfr_cosh m) Hrange Hget (proj1 Hc)
        RNDU _ Fb I).
  + (* At [b = +inf], [x] holds every real above [r0], where [cosh] rises
       without bound. *)
    rewrite Eb, (ch_ru_inf emin emax m false Hget Hc). apply lane_ok_inf. intros M.
    destruct (cosh_unbounded M) as (r & Hr & HM).
    exists (cosh (Rmax r r0)). split.
    * exists (Rmax r r0). split; [|split; [exact I | reflexivity]].
      exact (mono_mem_up x r0 _ Hr0 Eb (Rmax_r _ _)).
    * pose proof (cosh_inc r (Rmax r r0) Hr (Rmax_l _ _)). lra.
Qed.

(** Otherwise [0] is in [x], so the least value of [cosh] on [x] is
    [cosh 0 = 1], which [of_u64 1] is exactly. As [cosh] is even and
    increases on [[0, +inf)], its largest value is [cosh (max(-a, b))], or
    it has none if [a = -inf] or [b = +inf]. *)
Lemma ch_zero :
  forall x, valid x -> Interval.is_empty x = false ->
  (is_finite (opp (fst (rep x))) = true -> B2R (opp (fst (rep x))) <= 0) ->
  (is_finite (snd (rep x)) = true -> 0 <= B2R (snd (rep x))) ->
  is_tightest (image_dom real_dom cosh x)
    (Interval.with_infsup_raw (of_u64 1)
       (cosh_ru m (fmax first (opp (opp (fst (rep x)))) (snd (rep x))))).
Proof using Hrange Hget Hc.
intros x Hx Hn Ha0 Hb0.
pose proof (ch_mem_0 x Hx Hn Ha0 Hb0) as H0.
destruct one_B2R as [F1 E1]. unfold one in F1, E1.
destruct (valid_nonempty x Hx Hn) as (Ha & Hb & _).
unfold Interval.with_infsup_raw, Generic.constant.
apply tightest_lanes_lub.
- exists (cosh 0), 0. split; [exact H0 | split; [exact I | reflexivity]].
- exists (Some (B2R (opp (of_u64 1)))). split.
  + apply tight_lub, tight_Some. rewrite B2R_opp, E1. split.
    * exists 0. split; [exact H0 | split; [exact I | rewrite cosh_0; lra]].
    * intros s (r & _ & _ & Hs). pose proof (cosh_ge_1 r). lra.
  + apply least_lane_exact. rewrite is_finite_opp. exact F1.
- destruct Ha as [Fa|Ea]; [destruct Hb as [Fb|Eb]|].
  + (* Both bounds are finite: [c = max(-a, b)] is [|a|] or [|b|], the
       largest [|r|] of a real [r] of [x]. *)
    assert (Fa' : is_finite (opp (opp (fst (rep x)))) = true)
      by (rewrite is_finite_opp; exact Fa).
    destruct (ch_fmax_fin first _ _ Fa' Fb) as [Fc Ec].
    rewrite B2R_opp in Ec.
    exists (Some (cosh (B2R (fmax first (opp (opp (fst (rep x)))) (snd (rep x)))))). split.
    * apply tight_lub, tight_Some. split.
      -- destruct (Rle_or_lt (- B2R (opp (fst (rep x)))) (B2R (snd (rep x)))) as [H|H].
         ++ exists (B2R (snd (rep x))). split; [exact (mono_mem_sup x Hx Hn Fb)|].
            split; [exact I|]. rewrite Ec, Rmax_right by exact H. reflexivity.
         ++ exists (B2R (opp (fst (rep x)))). split; [exact (mono_mem_inf x Hx Hn Fa)|].
            split; [exact I|]. rewrite Ec, Rmax_left by lra. apply cosh_even.
      -- intros s (r & Hr & _ & ->). apply ch_abs_le. rewrite Ec. apply Rabs_le.
         pose proof (mono_inf_le_mem x r Hr Fa). pose proof (mono_mem_le_sup x r Hr Fb).
         pose proof (Rmax_l (- B2R (opp (fst (rep x)))) (B2R (snd (rep x)))).
         pose proof (Rmax_r (- B2R (opp (fst (rep x)))) (B2R (snd (rep x)))). lra.
    * apply round_up_lane.
      exact (mpfr_fn_correct emin emax m real_dom cosh (mpfr_cosh m) Hrange Hget (proj1 Hc)
        RNDU _ Fc I).
  + (* [b = +inf]: [fmax] is +inf, and [x] holds every real above 0. *)
    rewrite Eb, ch_fmax_inf_r.
    * rewrite (ch_ru_inf emin emax m false Hget Hc). apply lane_ok_inf. intros M.
      destruct (cosh_unbounded M) as (r & Hr & HM).
      exists (cosh r). split; [|exact HM].
      exists r. split; [exact (mono_mem_up x 0 r H0 Eb Hr) | split; [exact I | reflexivity]].
    * apply ch_opp_not_nan, ch_lower_not_nan. left. exact Fa.
  + (* [a = -inf]: [fmax] is +inf, and [x] holds every real below 0. *)
    rewrite Ea. change (opp (B754_infinity true)) with (B754_infinity false : f64).
    rewrite ch_fmax_inf_l by exact (ch_upper_not_nan _ Hb).
    rewrite (ch_ru_inf emin emax m false Hget Hc). apply lane_ok_inf. intros M.
    destruct (cosh_unbounded M) as (r & Hr & HM).
    exists (cosh (- r)). split; [|rewrite cosh_even; exact HM].
    exists (- r). split; [|split; [exact I | reflexivity]].
    apply (mono_mem_dn x 0 (- r) H0 Ea). lra.
Qed.

End ChBranches.

(** [Interval::cosh] returns the tightest interval that contains the
    image, whichever zero [f64::max] returns. *)
Theorem cosh_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> cosh_ok emin emax m ->
  forall first x, valid x ->
  is_tightest (image_dom real_dom cosh x) (Interval.cosh m first x).
Proof.
intros emin emax m Hrange Hget Hc first x Hx. unfold Interval.cosh.
destruct (Interval.is_empty x) eqn:Hn.
- (* An empty interval has an empty image. *)
  rewrite (valid_empty_eq x Hx Hn). apply tightest_empty.
  intros u (r & Hr & _). exact (mem_nan Interval.EMPTY r eq_refl Hr).
- (* +inf is not below 0 and -inf is not above 0, so the first two
     branches have the finite bound that their lemmas need. *)
  cbv zeta. unfold Interval.inf_raw, Interval.sup_raw.
  destruct (valid_nonempty x Hx Hn) as (Ha & Hb & _).
  destruct (Model.lt (snd (rep x)) Model.zero) eqn:Hlt.
  + destruct Hb as [Fb|Eb]; [|rewrite Eb in Hlt; discriminate Hlt].
    apply (ch_neg emin emax m Hrange Hget Hc x Hx Hn Fb).
    exact (proj1 (ch_lt_fin _ Model.zero Fb eq_refl) Hlt).
  + destruct (Model.gt (opp (fst (rep x))) Model.zero) eqn:Hgt.
    * destruct Ha as [Fa|Ea]; [|rewrite Ea in Hgt; discriminate Hgt].
      apply (ch_pos emin emax m Hrange Hget Hc x Hx Hn Fa).
      exact (proj1 (ch_lt_fin Model.zero _ eq_refl Fa) Hgt).
    * apply (ch_zero emin emax m first Hrange Hget Hc x Hx Hn).
      -- intros Fa. exact (proj2 (ch_lt_fin Model.zero _ eq_refl Fa) Hgt).
      -- intros Fb. exact (proj2 (ch_lt_fin _ Model.zero Fb eq_refl) Hlt).
Qed.

(** An infinite bound of a nonempty [x] gives an upper bound of +inf: the
    branch taken calls [cosh_ru] of that infinity, or of [fmax] of it. *)
Lemma ch_hi_inf :
  forall emin emax m first x, get_d_ok emin emax m -> cosh_ok emin emax m ->
  valid x -> Interval.is_empty x = false ->
  opp (fst (rep x)) = B754_infinity true \/ snd (rep x) = B754_infinity false ->
  snd (rep (Interval.cosh m first x)) = B754_infinity false.
Proof.
intros emin emax m first x Hget Hc Hx Hn Hinf.
destruct (valid_nonempty x Hx Hn) as (Ha & Hb & _).
unfold Interval.cosh. rewrite Hn. cbv zeta.
unfold Interval.inf_raw, Interval.sup_raw, Interval.with_infsup_raw, Generic.constant.
destruct (Model.lt (snd (rep x)) Model.zero) eqn:Hlt;
  [|destruct (Model.gt (opp (fst (rep x))) Model.zero) eqn:Hgt]; cbn [rep snd].
- destruct Hinf as [Ea|Eb]; [|rewrite Eb in Hlt; discriminate Hlt].
  rewrite Ea. exact (ch_ru_inf emin emax m true Hget Hc).
- destruct Hinf as [Ea|Eb]; [rewrite Ea in Hgt; discriminate Hgt|].
  rewrite Eb. exact (ch_ru_inf emin emax m false Hget Hc).
- destruct Hinf as [Ea|Eb].
  + rewrite Ea. change (opp (B754_infinity true)) with (B754_infinity false : f64).
    rewrite ch_fmax_inf_l by exact (ch_upper_not_nan _ Hb).
    exact (ch_ru_inf emin emax m false Hget Hc).
  + rewrite Eb, ch_fmax_inf_r by exact (ch_opp_not_nan _ (ch_lower_not_nan _ Ha)).
    exact (ch_ru_inf emin emax m false Hget Hc).
Qed.

Lemma ch_not_common :
  forall emin emax m first x, get_d_ok emin emax m -> cosh_ok emin emax m ->
  valid x -> Interval.is_empty x = false ->
  opp (fst (rep x)) = B754_infinity true \/ snd (rep x) = B754_infinity false ->
  Interval.is_common_interval (Interval.cosh m first x) = false.
Proof.
intros emin emax m first x Hget Hc Hx Hn Hinf.
pose proof (ch_hi_inf emin emax m first x Hget Hc Hx Hn Hinf) as E.
revert E. destruct (Interval.cosh m first x) as [[w0 w1]]. cbn [rep snd]. intros ->.
apply mono_not_common_hi.
Qed.

(** [DecInterval::cosh] returns NaI for NaI, and otherwise the tightest
    interval, decorated as IEEE 1788 asks. An unbounded interval has an
    unbounded result, so no hypothesis on a [com] argument is needed. *)
Theorem dec_cosh_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> cosh_ok emin emax m ->
  forall first x, valid (itv x) ->
  let y := DecInterval.cosh m first x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom cosh (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d cosh (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros emin emax m Hrange Hget Hc first x Hx. unfold DecInterval.cosh.
apply (elem_dec_correct real_dom cosh (Interval.cosh m first) x Hx).
- exact (cosh_correct emin emax m Hrange Hget Hc first (itv x) Hx).
- intros r _. exact I.
- intros r _. exact (continuity_pt_continue_in cosh real_dom r (cosh_cont r)).
- (* A common result comes from a bounded interval, as an infinite bound
     gives an upper bound of +inf. *)
  intros _ Hz. destruct (Interval.is_empty (itv x)) eqn:Hn.
  + exists 0. intros r Hr. destruct (mem_empty (itv x) r Hx Hn Hr).
  + destruct (valid_nonempty (itv x) Hx Hn) as (Ha & Hb & _).
    destruct Ha as [Fa|Ea]; [destruct Hb as [Fb|Eb]|].
    * exact (common_bounded _ (finite_common _ Fa Fb)).
    * rewrite (ch_not_common emin emax m first (itv x) Hget Hc Hx Hn (or_intror Eb)) in Hz.
      discriminate Hz.
    * rewrite (ch_not_common emin emax m first (itv x) Hget Hc Hx Hn (or_introl Ea)) in Hz.
      discriminate Hz.
Qed.
