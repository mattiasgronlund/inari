(** * [impl_mono_inc!] of intervals and decorated intervals

    The functions that [impl_mono_inc!] defines, such as [exp], return
    [[f_rd(a), f_ru(b)]] for a nonempty [[a, b]], where [f_rd] and [f_ru]
    compute an increasing, continuous function [f] on all of R with MPFR,
    rounded down and up. At a finite bound, that is [f] of the bound
    rounded down or up. At -inf, MPFR returns the greatest lower bound of
    [f] rounded down, or -inf if [f] has none ([low_end]), and at +inf the
    least upper bound rounded up, or +inf ([high_end]). These bounds need
    not be values of [f]: [exp] of [[-inf, 0]] is [(0, 1]]. So the lanes
    are those of least upper bounds ([lane_ok] and [tightest_lanes_lub] in
    [DivTight.v]). *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr RealBounds ComCommon
  Integer Sign MaxMin AddSub MulTight DecBinary DivTight MpfrRound Sqrt ElemDec.

Open Scope R_scope.

(** What MPFR returns at -inf: the greatest lower bound of [f] rounded
    down, or -inf if [f] has no lower bound. *)
Definition low_end (emin emax : Z) (f : R -> R) (v : mpfr_t) : Prop :=
  (exists L, glb_of f L /\ mpfr_round (mpfr_format emin emax) RNDD L v) \/
  (unbounded_below f /\ v = MInf true).

(** What MPFR returns at +inf: the least upper bound of [f] rounded up, or
    +inf if [f] has no upper bound. *)
Definition high_end (emin emax : Z) (f : R -> R) (v : mpfr_t) : Prop :=
  (exists U, lub_of f U /\ mpfr_round (mpfr_format emin emax) RNDU U v) \/
  (unbounded_above f /\ v = MInf false).

(** ** Bounds of intervals and of their images *)

(** An upper bound [U] of [T] that elements of [T] come as close to as
    asked is its least upper bound: an upper bound [m < U] would be below
    an element above [U - (U - m)]. *)
Lemma mono_lub_approx :
  forall U (T : R -> Prop), (forall s, T s -> s <= U) ->
  (forall eps, 0 < eps -> exists s, T s /\ U - eps < s) -> lub (Some U) T.
Proof.
intros U T Hub Happ s. cbn [below]. split.
- intros Hs m Hm. destruct (Rle_or_lt U m) as [HUm|HmU]; [lra|].
  destruct (Happ (U - m)) as (t & Ht & Hlt); [lra|].
  specialize (Hm t Ht). lra.
- intros H. exact (H U Hub).
Qed.

(** The finite bounds of a nonempty interval [x] are reals of [x], and
    bound its reals. *)
Lemma mono_mem_sup :
  forall x, valid x -> Interval.is_empty x = false -> is_finite (snd (rep x)) = true ->
  mem (B2R (snd (rep x))) x.
Proof.
intros x Hx Hn Fb.
destruct (valid_nonempty x Hx Hn) as (Ha & Hb & Hord).
apply (mem_bounds x _ Ha Hb). rewrite (bound_finite _ Fb) in Hord |- *.
revert Hord. unfold in_bounds, ordered.
destruct (bound (opp (fst (rep x)))); intros Hord; split; first [exact I | lra].
Qed.

Lemma mono_mem_inf :
  forall x, valid x -> Interval.is_empty x = false -> is_finite (opp (fst (rep x))) = true ->
  mem (B2R (opp (fst (rep x)))) x.
Proof.
intros x Hx Hn Fa.
destruct (valid_nonempty x Hx Hn) as (Ha & Hb & Hord).
apply (mem_bounds x _ Ha Hb). rewrite (bound_finite _ Fa) in Hord |- *.
revert Hord. unfold in_bounds, ordered.
destruct (bound (snd (rep x))); intros Hord; split; first [exact I | lra].
Qed.

Lemma mono_mem_le_sup :
  forall x r, mem r x -> is_finite (snd (rep x)) = true -> r <= B2R (snd (rep x)).
Proof.
intros x r [_ H] Fb. revert H Fb.
destruct (snd (rep x)); intros H Fb; try discriminate Fb; exact H.
Qed.

Lemma mono_inf_le_mem :
  forall x r, mem r x -> is_finite (opp (fst (rep x))) = true -> B2R (opp (fst (rep x))) <= r.
Proof.
intros x r [H _] Fa. revert H Fa.
destruct (opp (fst (rep x))); intros H Fa; try discriminate Fa; exact H.
Qed.

(** If the upper bound of [x] is +inf, every real above a real of [x] is
    in [x], and if the lower bound is -inf, every real below one. *)
Lemma mono_mem_up :
  forall x t r, mem t x -> snd (rep x) = B754_infinity false -> t <= r -> mem r x.
Proof.
intros x t r [H0 _] Eb Htr. split.
- revert H0. destruct (opp (fst (rep x))); intros H0; try exact H0; lra.
- rewrite Eb. reflexivity.
Qed.

Lemma mono_mem_dn :
  forall x t r, mem t x -> opp (fst (rep x)) = B754_infinity true -> r <= t -> mem r x.
Proof.
intros x t r [_ H1] Ea Hrt. split.
- rewrite Ea. reflexivity.
- revert H1. destruct (snd (rep x)); intros H1; try exact H1; lra.
Qed.

(** An interval with a lower bound of -inf (a first lane of +inf), or an
    upper bound of +inf, is not a common interval. *)
Lemma mono_not_common_lo :
  forall w, Interval.is_common_interval {| rep := (opp (B754_infinity true), w) |} = false.
Proof.
intros w. rewrite is_common_interval_lt, infinity_eq. reflexivity.
Qed.

Lemma mono_not_common_hi :
  forall w, Interval.is_common_interval {| rep := (w, B754_infinity false) |} = false.
Proof.
intros w. rewrite is_common_interval_lt, infinity_eq.
change (lt w (B754_infinity false) && lt (B754_infinity false) (B754_infinity false) = false).
destruct (lt w (B754_infinity false)); reflexivity.
Qed.

Section MonoInc.

Variables (emin emax : Z) (m : mpfr) (f : R -> R) (g : mpfr_rnd -> mpfr_t -> mpfr_t).

Hypothesis Hrange : range_ok emin emax.
Hypothesis Hget : get_d_ok emin emax m.
Hypothesis Hg : mpfr_correct emin emax real_dom f g.
Hypothesis Hlo : low_end emin emax f (g RNDD (MInf true)).
Hypothesis Hhi : high_end emin emax f (g RNDU (MInf false)).
Hypothesis Hinc : forall r t, r <= t -> f r <= f t.
Hypothesis Hcont : forall r, continuity_pt f r.

(** The second lane of the result for a nonempty [x]: [f_ru] of the upper
    bound [b] of [x] is the least float or +inf at or above the least upper
    bound of the image. *)
Lemma mono_lane_up :
  forall x, valid x -> Interval.is_empty x = false ->
  lane_ok (image_dom real_dom f x) (mpfr_fn m g RNDU (snd (rep x))).
Proof using Hrange Hget Hg Hhi Hinc.
intros x Hx Hn.
destruct (nonempty_mem x Hx Hn) as (r0 & Hr0).
destruct (valid_nonempty x Hx Hn) as (_ & [Fb|Eb] & _).
- (* A finite [b] is in [x], so [f b] is the largest value, as [f] is
     increasing, and [f_ru b] is [f b] rounded up. *)
  exists (Some (f (B2R (snd (rep x))))). split.
  + apply tight_lub, tight_Some. split.
    * exists (B2R (snd (rep x))).
      split; [exact (mono_mem_sup x Hx Hn Fb) | split; [exact I | reflexivity]].
    * intros s (r & Hr & _ & ->). apply Hinc, (mono_mem_le_sup x r Hr Fb).
  + apply round_up_lane.
    exact (mpfr_fn_correct emin emax m real_dom f g Hrange Hget Hg RNDU _ Fb I).
- (* At +inf, MPFR returns the least upper bound [U] of [f] rounded up, or
     +inf if [f] has no upper bound. [x] holds every real above [r0], and
     [f] is increasing, so its values on [x] come as close to [U], or rise
     as high, as those on R. *)
  rewrite Eb. destruct Hhi as [(U & HU & Hv) | (Hu & Hv)].
  + exists (Some U). split.
    * apply mono_lub_approx.
      -- intros s (r & _ & _ & ->). exact (proj1 HU r).
      -- intros eps Heps. destruct (proj2 HU eps Heps) as (r & Hr).
         exists (f (Rmax r r0)). split.
         ++ exists (Rmax r r0). split; [|split; [exact I | reflexivity]].
            exact (mono_mem_up x r0 _ Hr0 Eb (Rmax_r r r0)).
         ++ pose proof (Hinc r (Rmax r r0) (Rmax_l r r0)). lra.
    * apply round_up_lane. exact (mpfr_fn_round emin emax m RNDU U _ Hrange Hget Hv).
  + rewrite (mpfr_fn_inf emin emax m g RNDU false false Hget Hv).
    apply lane_ok_inf. intros M. destruct (Hu M) as (r & Hr).
    exists (f (Rmax r r0)). split.
    * exists (Rmax r r0). split; [|split; [exact I | reflexivity]].
      exact (mono_mem_up x r0 _ Hr0 Eb (Rmax_r r r0)).
    * pose proof (Hinc r (Rmax r r0) (Rmax_l r r0)). lra.
Qed.

(** The first lane of the result for a nonempty [x]: the negation of
    [f_rd] of the lower bound [a] of [x] is the least float or +inf at or
    above the least upper bound of the negated image. *)
Lemma mono_lane_dn :
  forall x, valid x -> Interval.is_empty x = false ->
  lane_ok (fun s => image_dom real_dom f x (- s))
    (opp (mpfr_fn m g RNDD (opp (fst (rep x))))).
Proof using Hrange Hget Hg Hlo Hinc.
intros x Hx Hn.
destruct (nonempty_mem x Hx Hn) as (r0 & Hr0).
destruct (valid_nonempty x Hx Hn) as ([Fa|Ea] & _ & _).
- (* A finite [a] is in [x], so [f a] is the least value, and [f_rd a] is
     [f a] rounded down. *)
  exists (Some (- f (B2R (opp (fst (rep x)))))). split.
  + apply tight_lub, tight_Some. split.
    * exists (B2R (opp (fst (rep x)))).
      split; [exact (mono_mem_inf x Hx Hn Fa) | split; [exact I | apply Ropp_involutive]].
    * intros s (r & Hr & _ & Hs).
      pose proof (Hinc _ _ (mono_inf_le_mem x r Hr Fa)). lra.
  + apply round_dn_lane.
    exact (mpfr_fn_correct emin emax m real_dom f g Hrange Hget Hg RNDD _ Fa I).
- (* At -inf, MPFR returns the greatest lower bound [L] of [f] rounded
     down, or -inf if [f] has no lower bound. [x] holds every real below
     [r0], so the values of [f] on [x] come as close to [L], or fall as
     low, as those on R. *)
  rewrite Ea. destruct Hlo as [(L & HL & Hv) | (Hu & Hv)].
  + exists (Some (- L)). split.
    * apply mono_lub_approx.
      -- intros s (r & _ & _ & Hs). pose proof (proj1 HL r). lra.
      -- intros eps Heps. destruct (proj2 HL eps Heps) as (r & Hr).
         exists (- f (Rmin r r0)). split.
         ++ exists (Rmin r r0). split; [|split; [exact I | apply Ropp_involutive]].
            exact (mono_mem_dn x r0 _ Hr0 Ea (Rmin_r r r0)).
         ++ pose proof (Hinc (Rmin r r0) r (Rmin_l r r0)). lra.
    * apply round_dn_lane. exact (mpfr_fn_round emin emax m RNDD L _ Hrange Hget Hv).
  + rewrite (mpfr_fn_inf emin emax m g RNDD true true Hget Hv).
    apply lane_ok_inf. intros M. destruct (Hu (- M)) as (r & Hr).
    exists (- f (Rmin r r0)). split.
    * exists (Rmin r r0). split; [|split; [exact I | apply Ropp_involutive]].
      exact (mono_mem_dn x r0 _ Hr0 Ea (Rmin_r r r0)).
    * pose proof (Hinc (Rmin r r0) r (Rmin_l r r0)). lra.
Qed.

(** If [f] has no lower bound and no upper bound, a common result comes
    from a bounded [x]: an infinite bound of [x] gives MPFR's infinity. *)
Lemma mono_common_bounded :
  unbounded_below f -> unbounded_above f ->
  forall x, valid x ->
  Interval.is_common_interval
    (Interval.mono_inc (mpfr_fn m g RNDD) (mpfr_fn m g RNDU) x) = true ->
  bounded (fun r => mem r x).
Proof using Hget Hlo Hhi.
intros Hub Hua x Hx Hz.
destruct (Interval.is_empty x) eqn:Hn.
- exists 0. intros r Hr. destruct (mem_empty x r Hx Hn Hr).
- unfold Interval.mono_inc in Hz. rewrite Hn in Hz. cbv beta iota in Hz.
  unfold Interval.with_infsup_raw, Interval.inf_raw, Interval.sup_raw, Generic.constant
    in Hz.
  destruct (valid_nonempty x Hx Hn) as (Ha & Hb & _).
  apply common_bounded, finite_common.
  + destruct Ha as [Fa|Ea]; [exact Fa|exfalso].
    destruct Hlo as [(L & HL & _) | (_ & Hv)].
    * destruct (Hub (L - 1)) as (r & Hr). pose proof (proj1 HL r). lra.
    * rewrite Ea, (mpfr_fn_inf emin emax m g RNDD true true Hget Hv), mono_not_common_lo
        in Hz.
      discriminate Hz.
  + destruct Hb as [Fb|Eb]; [exact Fb|exfalso].
    destruct Hhi as [(U & HU & _) | (_ & Hv)].
    * destruct (Hua (U + 1)) as (r & Hr). pose proof (proj1 HU r). lra.
    * rewrite Eb, (mpfr_fn_inf emin emax m g RNDU false false Hget Hv), mono_not_common_hi
        in Hz.
      discriminate Hz.
Qed.

(** [mono_inc] returns the tightest interval that contains the image. *)
Theorem mono_inc_correct :
  forall x, valid x ->
  is_tightest (image_dom real_dom f x)
    (Interval.mono_inc (mpfr_fn m g RNDD) (mpfr_fn m g RNDU) x).
Proof using Hrange Hget Hg Hlo Hhi Hinc Hcont.
intros x Hx. unfold Interval.mono_inc.
destruct (Interval.is_empty x) eqn:Hn; cbv beta iota.
- (* An empty interval has an empty image. *)
  rewrite (valid_empty_eq x Hx Hn). apply tightest_empty.
  intros u (r & Hr & _). exact (mem_nan Interval.EMPTY r eq_refl Hr).
- (* [with_infsup_raw(a', b')] has the lanes [-a'] and [b']. *)
  destruct (nonempty_mem x Hx Hn) as (r0 & Hr0).
  unfold Interval.with_infsup_raw, Interval.inf_raw, Interval.sup_raw, Generic.constant.
  apply tightest_lanes_lub.
  + exists (f r0), r0. split; [exact Hr0 | split; [exact I | reflexivity]].
  + exact (mono_lane_dn x Hx Hn).
  + exact (mono_lane_up x Hx Hn).
Qed.

(** Its decorated version, [impl_dec!(f)], returns NaI for NaI, and
    otherwise the tightest interval, decorated as IEEE 1788 asks. If [x] is
    [com], its interval must be bounded ([com_common x]), as [exp] of
    [[-inf, 0]] is bounded, unless [f] has no bound at either end, as for
    [sinh], when the result of an unbounded interval is unbounded too. *)
Theorem dec_mono_inc_correct :
  forall x, valid (itv x) ->
  com_common x \/ (unbounded_below f /\ unbounded_above f) ->
  let y :=
    DecInterval.elem_dec (Interval.mono_inc (mpfr_fn m g RNDD) (mpfr_fn m g RNDU)) x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom f (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d f (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof using Hrange Hget Hg Hlo Hhi Hinc Hcont.
intros x Hx Hc.
apply (elem_dec_correct real_dom f
  (Interval.mono_inc (mpfr_fn m g RNDD) (mpfr_fn m g RNDU)) x Hx).
- exact (mono_inc_correct (itv x) Hx).
- intros r _. exact I.
- intros r _. exact (continuity_pt_continue_in f real_dom r (Hcont r)).
- (* A [com] interval is bounded, or its result is not common. *)
  intros Hd Hz. destruct Hc as [Hc|(Hub & Hua)].
  + exact (common_bounded _ (Hc Hd)).
  + exact (mono_common_bounded Hub Hua (itv x) Hx Hz).
Qed.

End MonoInc.
