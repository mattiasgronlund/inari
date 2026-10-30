(** * [Interval::pow] for exponents on both sides of 0

    The last branch of [Interval::pow], [c <= 0.0 < d], with [x], [a], [b],
    [y], [c] and [d] as in [PowNeg.v]. If [b] is 0, [x] is [[0, 0]], and
    the only points of the domain in the box are [(0, t)] for [t > 0], at
    which [pow] is 0 ([pw_mix_zero]). Otherwise the least value is at
    [(a, d)] for the reals at most 1 and at [(b, c)] for those at least 1,
    and the largest at [(a, c)] and at [(b, d)], so the bounds are
    [fmin first_min (pow_rd(a, d)) (pow_rd(b, c))] and
    [fmax first_max (pow_ru(a, c)) (pow_ru(b, d))] ([pw_mix]). If [a > 1],
    [x] has no real at most 1, and the other corner gives both bounds:
    [pow_rd(a, d)] is at least 1, so at least [pow_rd(b, c)], and
    [pow_ru(a, c)] at most 1, so at most [pow_ru(b, d)]. The same holds
    for [b < 1], the other way round. [PowMixLo.v] proves the lower lane
    and [PowMixHi.v] the upper one. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Integer Sign MaxMin AddSub
  DecBinary DivTight MpfrRound MonoInc PowReal PowMpfr PowCases PowNeg PowMixLo PowMixHi.

Open Scope R_scope.

(** ** The case [b = 0] *)

(** If [b] is 0, [x] is [[0, 0]], as [a] is at least 0. *)
Lemma px_x0 :
  forall x, pw_xok x -> Model.eq (Interval.sup_raw x) Model.zero = true ->
  forall r, mem r x <-> r = 0.
Proof.
intros x (Hv & He & Fa & HA0 & _) Hb0.
destruct (valid_nonempty x Hv He) as (Hlo & Hup & Hord).
assert (Hm := fun r => mem_bounds x r Hlo Hup).
unfold Interval.inf_raw, Interval.sup_raw in *.
rewrite (bound_finite _ Fa) in Hm, Hord.
(* [b = +inf] is not 0. *)
destruct Hup as [Fb | Eb]; [| rewrite Eb in Hb0; vm_compute in Hb0; discriminate Hb0].
rewrite (bound_finite _ Fb) in Hm, Hord. unfold ordered in Hord; cbv beta iota in Hord.
unfold Model.eq in Hb0. rewrite Beqb_correct in Hb0 by first [exact Fb | reflexivity].
change (B2R Model.zero) with 0 in Hb0.
revert Hb0. case Req_bool_spec; [intros Hb _ | discriminate].
intros r. rewrite Hm. unfold in_bounds; cbv beta iota.
split; [intros Hr; lra | intros ->; lra].
Qed.

(** An exponent [y] whose upper bound [d] is above 0, a finite float or
    +inf, has a real above 0: [d], or for [d = +inf] a real above 0 and
    above [c]. *)
Lemma px_ypos :
  forall y, valid y -> Interval.is_empty y = false ->
  Model.le (Interval.sup_raw y) Model.zero = false ->
  exists t, mem t y /\ 0 < t.
Proof.
intros y Hv He Hd.
destruct (valid_nonempty y Hv He) as (Hlo & Hup & Hord).
assert (Hm := fun t => mem_bounds y t Hlo Hup).
unfold Interval.sup_raw in Hd.
destruct Hup as [Fd | Ed].
- assert (HD : 0 < B2R (snd (rep y))).
  { unfold Model.le in Hd. rewrite Bleb_correct in Hd by first [exact Fd | reflexivity].
    change (B2R Model.zero) with 0 in Hd.
    revert Hd. case Rle_bool_spec; [discriminate | intros H _; exact H]. }
  exists (B2R (snd (rep y))). split; [| exact HD].
  apply Hm. rewrite (bound_finite _ Fd) in Hord |- *.
  destruct Hlo as [Fc | Ec].
  + rewrite (bound_finite _ Fc) in Hord |- *. unfold ordered in Hord; cbv beta iota in Hord.
    unfold in_bounds; cbv beta iota. lra.
  + rewrite Ec, bound_inf. unfold in_bounds; cbv beta iota. split; [exact I | lra].
- rewrite Ed, bound_inf in Hm.
  destruct Hlo as [Fc | Ec].
  + set (c := B2R (opp (fst (rep y)))).
    pose proof (Rle_abs c) as Hc. pose proof (Rabs_pos c) as Hc0.
    exists (1 + Rabs c). split; [| lra].
    apply Hm. rewrite (bound_finite _ Fc). unfold in_bounds; cbv beta iota.
    split; [fold c; lra | exact I].
  + exists 1. split; [| lra].
    apply Hm. rewrite Ec, bound_inf. unfold in_bounds; cbv beta iota. split; exact I.
Qed.

(** The set [{0}] has the lane +0. *)
Lemma px_lane0 : lane_ok (fun s => s = 0) Model.zero.
Proof.
exists (Some 0). split.
- intros s. cbn [below]. split.
  + intros Hs m Hm. specialize (Hm 0 eq_refl). lra.
  + intros H. apply H. intros r ->. lra.
- (* [least_lane_exact] of [Sqrt.v] for +0. *)
  change (Some 0) with (bound Model.zero).
  split; [left; reflexivity|]. split; [intros s Hs; exact Hs|].
  intros z _ Hz. exact Hz.
Qed.

Lemma pw_mix_zero :
  forall x y, pw_xok x -> valid y -> Interval.is_empty y = false ->
  Model.le (Interval.sup_raw y) Model.zero = false ->
  Model.eq (Interval.sup_raw x) Model.zero = true ->
  is_tightest (image2_set pow_dom Rpow x y) Interval.zero.
Proof.
intros x y Hx Hyv Hye Hd Hb0.
pose proof (px_x0 x Hx Hb0) as Hmx.
destruct (px_ypos y Hyv Hye Hd) as (t0 & Ht0 & Ht0p).
(* The only points of the domain in the box are [(0, t)] for [t > 0], and
   [Rpow 0 t] is 0. *)
assert (HS : forall s, image2_set pow_dom Rpow x y s <-> s = 0).
{ intros s. split.
  - intros (r & t & Hr & _ & _ & ->). apply Hmx in Hr. subst r. apply Rpow_0_l.
  - intros ->. exists 0, t0.
    exact (conj (proj2 (Hmx 0) eq_refl)
             (conj Ht0 (conj (or_intror (conj eq_refl Ht0p)) (eq_sym (Rpow_0_l t0))))). }
unfold Interval.zero, Generic.splat. apply tightest_lanes_lub.
- exists 0. apply HS. reflexivity.
- apply (lane_ok_ext (fun s => s = 0)); [| exact px_lane0].
  intros s. cbv beta. rewrite HS. split; intros H; lra.
- apply (lane_ok_ext (fun s => s = 0)); [| exact px_lane0].
  intros s. rewrite HS. tauto.
Qed.

Lemma pw_mix :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall first_min first_max x y, pw_xok x -> valid y -> Interval.is_empty y = false ->
  Model.le (Interval.sup_raw y) Model.zero = false ->
  Model.gt (Interval.inf_raw y) Model.zero = false ->
  Model.eq (Interval.sup_raw x) Model.zero = false ->
  is_tightest (image2_set pow_dom Rpow x y)
    (Interval.with_infsup_raw
       (fmin first_min (pow_rd m (Interval.inf_raw x) (Interval.sup_raw y))
          (pow_rd m (Interval.sup_raw x) (Interval.inf_raw y)))
       (fmax first_max (pow_ru m (Interval.inf_raw x) (Interval.inf_raw y))
          (pow_ru m (Interval.sup_raw x) (Interval.sup_raw y)))).
Proof.
intros emin emax m Hrg Hg Hp first_min first_max x y Hx Hyv Hye Hd Hc Hb0.
unfold Interval.with_infsup_raw, Generic.constant. apply tightest_lanes_lub.
- (* A real of [x] above 0, [b] or [a + 1], and any real of [y]. *)
  destruct (pn_x x Hx Hb0) as (_ & HA0 & _ & Hxb).
  destruct (nonempty_mem y Hyv Hye) as (t & Ht).
  assert (Hr : exists r, mem r x /\ 0 < r).
  { destruct Hxb as [(_ & HB0 & HAB & Hmx) | (_ & Hmx)].
    - exists (B2R (Interval.sup_raw x)). split; [apply Hmx; lra | exact HB0].
    - exists (B2R (Interval.inf_raw x) + 1). split; [apply Hmx; lra | lra]. }
  destruct Hr as (r & Hr & Hr0).
  exists (Rpow r t), r, t. exact (conj Hr (conj Ht (conj (or_introl Hr0) eq_refl))).
- exact (pw_mix_lo emin emax m Hrg Hg Hp first_min x y Hx Hyv Hye Hd Hc Hb0).
- exact (pw_mix_hi emin emax m Hrg Hg Hp first_max x y Hx Hyv Hye Hd Hc Hb0).
Qed.
