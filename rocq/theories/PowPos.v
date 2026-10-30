(** * [Interval::pow] for exponents above 0

    The branch [c > 0.0] of [Interval::pow], with [x], [a], [b], [y], [c]
    and [d] as in [PowNeg.v]. Every point of the box with [r >= 0] is in
    the domain, [r^t] increases in [r], and in [t] it decreases for
    [r <= 1] and increases for [r >= 1], so the bounds are at the corners
    that the three cases pick: [b < 1] ([pw_pos_lt1]), [a > 1]
    ([pw_pos_gt1]) and [a <= 1 <= b] ([pw_pos_mid]). [b] may be -0 here,
    if [self] is [[.., -0]]: [x] is then [[0, 0]], and [pow_ru(-0, c)] is
    a zero. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Integer Sign MaxMin AddSub
  DecBinary DivTight MpfrRound MonoInc PowReal PowMpfr PowCases PowNeg.

Open Scope R_scope.

(** ** The bounds as reals *)

(** The reals of a nonempty interval [z] whose lower bound is the real
    [A]: those of [[A, b]] for a finite upper bound [b], or of
    [[A, +inf)]. Unlike [pn_xdesc], a finite [b] may be 0. *)
Definition pp_desc (z : Interval) (A : R) (b : f64) : Prop :=
  (is_finite b = true /\ A <= B2R b /\ forall r, mem r z <-> A <= r <= B2R b) \/
  (b = B754_infinity false /\ forall r, mem r z <-> A <= r).

Lemma pp_desc_A :
  forall z A b, pp_desc z A b -> (forall r, mem r z -> A <= r) /\ mem A z.
Proof.
intros z A b [(Fb & HAB & Hm) | (Eb & Hm)]; split.
- intros r Hr. apply Hm in Hr. lra.
- apply Hm. lra.
- intros r Hr. apply Hm in Hr. exact Hr.
- apply Hm. lra.
Qed.

(** A nonempty [valid] interval with a finite lower bound. *)
Lemma pp_desc_of :
  forall z, valid z -> Interval.is_empty z = false -> is_finite (Interval.inf_raw z) = true ->
  pp_desc z (B2R (Interval.inf_raw z)) (Interval.sup_raw z).
Proof.
intros z Hv He Fa.
destruct (valid_nonempty z Hv He) as (Hlo & Hup & Hord).
assert (Hm := fun r => mem_bounds z r Hlo Hup).
unfold Interval.inf_raw, Interval.sup_raw, pp_desc in *.
rewrite (bound_finite _ Fa) in Hm, Hord.
destruct Hup as [Fb | Eb].
- left. rewrite (bound_finite _ Fb) in Hm, Hord. unfold ordered in Hord; cbv beta iota in Hord.
  split; [exact Fb|]. split; [exact Hord|].
  intros r. rewrite Hm. unfold in_bounds; cbv beta iota. tauto.
- right. split; [exact Eb|]. rewrite Eb, bound_inf in Hm.
  intros r. rewrite Hm. unfold in_bounds; cbv beta iota. tauto.
Qed.

Lemma pp_x :
  forall x, pw_xok x ->
  is_finite (Interval.inf_raw x) = true /\ 0 <= B2R (Interval.inf_raw x) /\
  (B2R (Interval.inf_raw x) = 0 -> Interval.inf_raw x = B754_zero false) /\
  pp_desc x (B2R (Interval.inf_raw x)) (Interval.sup_raw x).
Proof.
intros x Hx. pose proof Hx as (Hv & He & Fa & HA0 & HAz).
split; [exact Fa|]. split; [exact HA0|]. split; [exact HAz|].
exact (pp_desc_of x Hv He Fa).
Qed.

(** An exponent [y] with [c > 0]: [c] is finite, as [Model.gt] of -inf
    and 0 is false, and [y] holds the reals of [[c, d]] or [[c, +inf)]. *)
Lemma pp_y :
  forall y, valid y -> Interval.is_empty y = false ->
  Model.gt (Interval.inf_raw y) Model.zero = true ->
  is_finite (Interval.inf_raw y) = true /\ 0 < B2R (Interval.inf_raw y) /\
  pp_desc y (B2R (Interval.inf_raw y)) (Interval.sup_raw y).
Proof.
intros y Hv He Hc.
destruct (valid_nonempty y Hv He) as (Hlo & _ & _).
assert (Fc : is_finite (Interval.inf_raw y) = true).
{ unfold Interval.inf_raw in *. destruct Hlo as [Fc | Ec]; [exact Fc|].
  rewrite Ec in Hc. vm_compute in Hc. discriminate Hc. }
split; [exact Fc|]. split; [| exact (pp_desc_of y Hv He Fc)].
unfold Model.gt in Hc. rewrite Bltb_correct in Hc by first [exact Fc | reflexivity].
change (B2R Model.zero) with 0 in Hc.
revert Hc. case Rlt_bool_spec; [intros H _; exact H | discriminate].
Qed.

(** ** The image *)

(** For bases at least 0 and exponents above 0, every point of the box is
    in the domain. *)
Lemma pp_img :
  forall x y s, (forall r, mem r x -> 0 <= r) -> (forall t, mem t y -> 0 < t) ->
  image2_set pow_dom Rpow x y s <->
  exists r t, mem r x /\ mem t y /\ s = Rpow r t.
Proof.
intros x y s Hx Hy. split.
- intros (r & t & Hr & Ht & _ & Hs). exists r, t.
  split; [exact Hr|]. split; [exact Ht | exact Hs].
- intros (r & t & Hr & Ht & Hs). exists r, t.
  split; [exact Hr|]. split; [exact Ht|]. split; [|exact Hs].
  specialize (Hx r Hr). specialize (Hy t Ht).
  destruct (Rle_lt_or_eq_dec 0 r Hx) as [H | H]; [left; exact H | right; split; lra].
Qed.

(** ** Lanes *)

(** The lower lane [pow_rd(a, d)] for [0 <= a <= 1]: the greatest lower
    bound is at the corner [(a, d)], as [r^t] increases in [r] and, for
    [r <= 1], decreases in [t]. A finite [d] gives the least value [a^d]
    ([0^d = 0] for [a = 0]). For [d = +inf] the bound is 0, attained at
    [(0, c)] if [a = 0] and a limit if [0 < a < 1], or 1 if [a = 1]
    (every value is [r^t >= 1^t = 1]). *)
Lemma pp_lo_ad :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall x y (a c d : f64),
  is_finite a = true -> 0 <= B2R a <= 1 -> (B2R a = 0 -> a = B754_zero false) ->
  (forall r, mem r x -> B2R a <= r) -> mem (B2R a) x ->
  0 < B2R c -> pp_desc y (B2R c) d ->
  lane_ok (fun s => image2_set pow_dom Rpow x y (- s)) (opp (pow_rd m a d)).
Proof.
intros emin emax m Hrg Hg Hp x y a c d Fa HA HAz Hxa Hax HC0 Hyd.
destruct (pp_desc_A y _ _ Hyd) as (Hyc & Hcy).
assert (Hx0 : forall r, mem r x -> 0 <= r) by (intros r Hr; specialize (Hxa r Hr); lra).
assert (Hy0 : forall t, mem t y -> 0 < t) by (intros t Ht; specialize (Hyc t Ht); lra).
(* Every value is at least [a^t] for its [t]. *)
assert (Hlo : forall r t, mem r x -> mem t y -> Rpow (B2R a) t <= Rpow r t).
{ intros r t Hr Ht. specialize (Hxa r Hr). specialize (Hy0 t Ht).
  apply Rpow_le_base_pos; lra. }
assert (Hpos : forall s, image2_set pow_dom Rpow x y s -> 0 <= s).
{ intros s Hs. destruct (proj1 (pp_img x y s Hx0 Hy0) Hs) as (r & t & Hr & _ & ->).
  apply Rpow_ge_0, Hx0, Hr. }
unfold pow_rd.
destruct Hyd as [(Fd & HCD & Hmy) | (Ed & Hmy)].
- (* [d] finite: the least value is [a^d]. *)
  apply (pn_lo_at (image2_set pow_dom Rpow x y) (Rpow (B2R a) (B2R d))).
  + apply (proj2 (pp_img x y _ Hx0 Hy0)). exists (B2R a), (B2R d).
    split; [exact Hax|]. split; [apply Hmy; lra | reflexivity].
  + intros s Hs. destruct (proj1 (pp_img x y s Hx0 Hy0) Hs) as (r & t & Hr & Ht & ->).
    apply Rle_trans with (Rpow (B2R a) t); [| exact (Hlo r t Hr Ht)].
    apply Hmy in Ht.
    destruct (Req_dec (B2R a) 0) as [HA0 | HA0].
    * rewrite HA0, !Rpow_0_l. lra.
    * apply Rpow_le_exp_le1; lra.
  + apply (pow_fin emin emax m Hrg Hg Hp); [exact Fa | exact Fd |].
    destruct (Req_dec (B2R a) 0) as [HA0 | HA0]; [right; split; lra | left; lra].
- rewrite Ed. destruct (Req_dec (B2R a) 0) as [HA0 | HA0].
  + (* [a = 0], [d = +inf]: the least value is [0^c = 0]. *)
    rewrite (HAz HA0).
    apply (pn_lo_at (image2_set pow_dom Rpow x y) 0); [| exact Hpos |].
    * apply (proj2 (pp_img x y _ Hx0 Hy0)). exists (B2R a), (B2R c).
      split; [exact Hax|]. split; [exact Hcy|]. rewrite HA0, Rpow_0_l. reflexivity.
    * apply (pow_zero_pinf emin emax m Hg Hp).
  + destruct (Rle_lt_or_eq_dec _ _ (proj2 HA)) as [HA1 | HA1].
    * (* [0 < a < 1], [d = +inf]: [a^t] tends to 0 as [t] grows. *)
      assert (HA01 : 0 < B2R a < 1) by lra.
      apply pn_lo_0; [exact Hpos | |].
      -- intros eps He. destruct (Rpow_exp_large_lt1 (B2R a) eps HA01 He) as (t0 & Ht0).
         exists (Rpow (B2R a) (Rmax t0 (B2R c))). split.
         ++ apply (proj2 (pp_img x y _ Hx0 Hy0)). exists (B2R a), (Rmax t0 (B2R c)).
            split; [exact Hax|]. split; [apply Hmy, Rmax_r | reflexivity].
         ++ apply Ht0, Rmax_l.
      -- apply (pow_lt1_pinf emin emax m Hg Hp); [exact Fa | exact HA01].
    * (* [a = 1], [d = +inf]: every value is at least [1^t = 1]. *)
      apply (pn_lo_at (image2_set pow_dom Rpow x y) 1).
      -- apply (proj2 (pp_img x y _ Hx0 Hy0)). exists (B2R a), (B2R c).
         split; [exact Hax|]. split; [exact Hcy|]. rewrite HA1, Rpow_1_l. reflexivity.
      -- intros s Hs. destruct (proj1 (pp_img x y s Hx0 Hy0) Hs) as (r & t & Hr & Ht & ->).
         apply Rle_trans with (Rpow (B2R a) t); [| exact (Hlo r t Hr Ht)].
         rewrite HA1, Rpow_1_l. lra.
      -- apply (pow_one_inf emin emax m Hrg Hg Hp); [exact Fa | exact HA1].
Qed.

(** The upper lane [pow_ru(b, c)] for a finite [0 <= b <= 1]: the least
    upper bound is the value [b^c] at the corner [(b, c)], as [r^t]
    increases in [r] and, for [r <= 1], decreases in [t]. If [b] is a
    zero, [x = {0}] and every value is 0. *)
Lemma pp_hi_bc :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall x y (b c d : f64), is_finite b = true -> B2R b <= 1 ->
  (forall r, mem r x -> 0 <= r <= B2R b) -> mem (B2R b) x ->
  is_finite c = true -> 0 < B2R c -> pp_desc y (B2R c) d ->
  lane_ok (image2_set pow_dom Rpow x y) (pow_ru m b c).
Proof.
intros emin emax m Hrg Hg Hp x y b c d Fb HB1 Hxb Hbx Fc HC0 Hyd.
destruct (pp_desc_A y _ _ Hyd) as (Hyc & Hcy).
assert (Hx0 : forall r, mem r x -> 0 <= r) by (intros r Hr; specialize (Hxb r Hr); lra).
assert (Hy0 : forall t, mem t y -> 0 < t) by (intros t Ht; specialize (Hyc t Ht); lra).
assert (HB0 : 0 <= B2R b) by (specialize (Hxb _ Hbx); lra).
unfold pow_ru.
apply (pn_hi_at (image2_set pow_dom Rpow x y) (Rpow (B2R b) (B2R c))).
- apply (proj2 (pp_img x y _ Hx0 Hy0)). exists (B2R b), (B2R c).
  split; [exact Hbx|]. split; [exact Hcy | reflexivity].
- intros s Hs. destruct (proj1 (pp_img x y s Hx0 Hy0) Hs) as (r & t & Hr & Ht & ->).
  specialize (Hxb r Hr). specialize (Hyc t Ht).
  destruct (Rle_lt_or_eq_dec 0 (B2R b) HB0) as [HB | HB].
  + apply Rle_trans with (Rpow (B2R b) t).
    * apply Rpow_le_base_pos; lra.
    * apply Rpow_le_exp_le1; lra.
  + (* [b = 0]: [x = {0}], and every value is 0. *)
    replace r with 0 by lra. rewrite <- HB, !Rpow_0_l. lra.
- apply (pow_fin emin emax m Hrg Hg Hp); [exact Fb | exact Fc |].
  destruct (Rle_lt_or_eq_dec 0 (B2R b) HB0) as [HB | HB]; [left; exact HB | right; split; lra].
Qed.

(** The upper lane [pow_ru(b, d)] for [b >= 1] or [b = +inf]: the least
    upper bound is at the corner [(b, d)], as [r^t] increases in [r] and,
    for [r >= 1], in [t]. It is attained if [b] and [d] are finite. If
    [b = +inf] ([r^c] grows without bound as [r] grows) or [b > 1] and
    [d = +inf] ([b^t] grows without bound as [t] grows), the values have
    no upper bound; if [b = 1] and [d = +inf], the bound is 1 (every value
    is [r^t <= 1^t = 1]). *)
Lemma pp_hi_bd :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall x y A (b c d : f64), 0 <= A -> pp_desc x A b -> (is_finite b = true -> 1 <= B2R b) ->
  0 < B2R c -> pp_desc y (B2R c) d ->
  lane_ok (image2_set pow_dom Rpow x y) (pow_ru m b d).
Proof.
intros emin emax m Hrg Hg Hp x y A b c d HA0 Hxb Hb1 HC0 Hyd.
destruct (pp_desc_A x _ _ Hxb) as (Hxa & Hax).
destruct (pp_desc_A y _ _ Hyd) as (Hyc & Hcy).
assert (Hx0 : forall r, mem r x -> 0 <= r) by (intros r Hr; specialize (Hxa r Hr); lra).
assert (Hy0 : forall t, mem t y -> 0 < t) by (intros t Ht; specialize (Hyc t Ht); lra).
unfold pow_ru.
destruct Hxb as [(Fb & HAB & Hmx) | (Eb & Hmx)]; [specialize (Hb1 Fb) |].
- (* Every value is at most [b^t] for its [t]. *)
  assert (Hhi : forall r t, mem r x -> mem t y -> Rpow r t <= Rpow (B2R b) t).
  { intros r t Hr Ht. apply Hmx in Hr. specialize (Hy0 t Ht).
    apply Rpow_le_base_pos; lra. }
  destruct Hyd as [(Fd & HCD & Hmy) | (Ed & Hmy)].
  + (* [b] and [d] finite: the largest value is [b^d]. *)
    apply (pn_hi_at (image2_set pow_dom Rpow x y) (Rpow (B2R b) (B2R d))).
    * apply (proj2 (pp_img x y _ Hx0 Hy0)). exists (B2R b), (B2R d).
      split; [apply Hmx; lra|]. split; [apply Hmy; lra | reflexivity].
    * intros s Hs. destruct (proj1 (pp_img x y s Hx0 Hy0) Hs) as (r & t & Hr & Ht & ->).
      apply Rle_trans with (Rpow (B2R b) t); [exact (Hhi r t Hr Ht)|].
      apply Hmy in Ht. apply Rpow_le_exp_ge1; lra.
    * apply (pow_fin emin emax m Hrg Hg Hp); [exact Fb | exact Fd | left; lra].
  + rewrite Ed. destruct (Rle_lt_or_eq_dec 1 (B2R b) Hb1) as [HB1 | HB1].
    * (* [b > 1], [d = +inf]: [b^t] grows without bound as [t] grows. *)
      rewrite (pow_gt1_pinf emin emax m Hg Hp RNDU b Fb HB1).
      apply lane_ok_inf. intros M.
      destruct (Rpow_exp_large_gt1 (B2R b) M HB1) as (t0 & Ht0).
      exists (Rpow (B2R b) (Rmax t0 (B2R c))). split.
      -- apply (proj2 (pp_img x y _ Hx0 Hy0)). exists (B2R b), (Rmax t0 (B2R c)).
         split; [apply Hmx; lra|]. split; [apply Hmy, Rmax_r | reflexivity].
      -- apply Ht0, Rmax_l.
    * (* [b = 1], [d = +inf]: every value is at most [1^t = 1]. *)
      apply (pn_hi_at (image2_set pow_dom Rpow x y) 1).
      -- apply (proj2 (pp_img x y _ Hx0 Hy0)). exists (B2R b), (B2R c).
         split; [apply Hmx; lra|]. split; [exact Hcy|]. rewrite <- HB1, Rpow_1_l. reflexivity.
      -- intros s Hs. destruct (proj1 (pp_img x y s Hx0 Hy0) Hs) as (r & t & Hr & Ht & ->).
         apply Rle_trans with (Rpow (B2R b) t); [exact (Hhi r t Hr Ht)|].
         rewrite <- HB1, Rpow_1_l. lra.
      -- apply (pow_one_inf emin emax m Hrg Hg Hp); [exact Fb | lra].
- (* [b = +inf]: [r^c] grows without bound as [r] grows. *)
  assert (Hd : (is_finite d = true /\ 0 < B2R d) \/ d = B754_infinity false).
  { destruct Hyd as [(Fd & HCD & _) | (Ed & _)]; [left; split; [exact Fd | lra] | right; exact Ed]. }
  rewrite Eb, (pow_pinf_pos emin emax m Hg Hp RNDU d Hd).
  apply lane_ok_inf. intros M.
  destruct (Rpow_base_large_pos (B2R c) M HC0) as (r0 & Hr0 & Hr0M).
  exists (Rpow (Rmax r0 A) (B2R c)). split.
  + apply (proj2 (pp_img x y _ Hx0 Hy0)). exists (Rmax r0 A), (B2R c).
    split; [apply Hmx, Rmax_r|]. split; [exact Hcy | reflexivity].
  + apply Hr0M, Rmax_l.
Qed.

(** ** The three cases *)

Lemma pw_pos_lt1 :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall x y, pw_xok x -> valid y -> Interval.is_empty y = false ->
  Model.le (Interval.sup_raw y) Model.zero = false ->
  Model.gt (Interval.inf_raw y) Model.zero = true ->
  Model.lt (Interval.sup_raw x) (of_u64 1) = true ->
  is_tightest (image2_set pow_dom Rpow x y)
    (Interval.with_infsup_raw (pow_rd m (Interval.inf_raw x) (Interval.sup_raw y))
       (pow_ru m (Interval.sup_raw x) (Interval.inf_raw y))).
Proof.
intros emin emax m Hrg Hg Hp x y Hx Hyv Hye _ Hc Hb1.
destruct (pp_x x Hx) as (Fa & HA0 & HAz & Hxb).
destruct (pp_y y Hyv Hye Hc) as (Fc & HC0 & Hyd).
destruct (pp_desc_A _ _ _ Hxb) as (Hxa & Hax).
destruct (pp_desc_A _ _ _ Hyd) as (Hyc & Hcy).
assert (Hx0 : forall r, mem r x -> 0 <= r) by (intros r Hr; specialize (Hxa r Hr); lra).
assert (Hy0 : forall t, mem t y -> 0 < t) by (intros t Ht; specialize (Hyc t Ht); lra).
assert (HS : image2_set pow_dom Rpow x y
  (Rpow (B2R (Interval.inf_raw x)) (B2R (Interval.inf_raw y)))).
{ apply (proj2 (pp_img x y _ Hx0 Hy0)).
  exists (B2R (Interval.inf_raw x)), (B2R (Interval.inf_raw y)).
  split; [exact Hax|]. split; [exact Hcy | reflexivity]. }
(* [b < 1] rules out [b = +inf]. *)
destruct Hxb as [(Fb & HAB & Hmx) | (Eb & _)];
  [| rewrite Eb in Hb1; vm_compute in Hb1; discriminate Hb1].
rewrite pn_lt_1 in Hb1 by exact Fb.
revert Hb1. case Rlt_bool_spec; [intros HB1 _ | discriminate].
unfold Interval.with_infsup_raw, Generic.constant. apply tightest_lanes_lub.
- exact (ex_intro _ _ HS).
- apply (pp_lo_ad emin emax m Hrg Hg Hp x y (Interval.inf_raw x) (Interval.inf_raw y)
    (Interval.sup_raw y) Fa); [lra | exact HAz | exact Hxa | exact Hax | exact HC0 | exact Hyd].
- apply (pp_hi_bc emin emax m Hrg Hg Hp x y (Interval.sup_raw x) (Interval.inf_raw y)
    (Interval.sup_raw y) Fb); [lra | | apply Hmx; lra | exact Fc | exact HC0 | exact Hyd].
  intros r Hr. apply Hmx in Hr. lra.
Qed.

Lemma pw_pos_gt1 :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall x y, pw_xok x -> valid y -> Interval.is_empty y = false ->
  Model.le (Interval.sup_raw y) Model.zero = false ->
  Model.gt (Interval.inf_raw y) Model.zero = true ->
  Model.lt (Interval.sup_raw x) (of_u64 1) = false ->
  Model.gt (Interval.inf_raw x) (of_u64 1) = true ->
  is_tightest (image2_set pow_dom Rpow x y)
    (Interval.with_infsup_raw (pow_rd m (Interval.inf_raw x) (Interval.inf_raw y))
       (pow_ru m (Interval.sup_raw x) (Interval.sup_raw y))).
Proof.
intros emin emax m Hrg Hg Hp x y Hx Hyv Hye _ Hc _ Ha1.
destruct (pp_x x Hx) as (Fa & HA0 & HAz & Hxb).
destruct (pp_y y Hyv Hye Hc) as (Fc & HC0 & Hyd).
destruct (pp_desc_A _ _ _ Hxb) as (Hxa & Hax).
destruct (pp_desc_A _ _ _ Hyd) as (Hyc & Hcy).
assert (Hx0 : forall r, mem r x -> 0 <= r) by (intros r Hr; specialize (Hxa r Hr); lra).
assert (Hy0 : forall t, mem t y -> 0 < t) by (intros t Ht; specialize (Hyc t Ht); lra).
assert (HS : image2_set pow_dom Rpow x y
  (Rpow (B2R (Interval.inf_raw x)) (B2R (Interval.inf_raw y)))).
{ apply (proj2 (pp_img x y _ Hx0 Hy0)).
  exists (B2R (Interval.inf_raw x)), (B2R (Interval.inf_raw y)).
  split; [exact Hax|]. split; [exact Hcy | reflexivity]. }
rewrite pn_gt_1 in Ha1 by exact Fa.
revert Ha1. case Rlt_bool_spec; [intros HA1 _ | discriminate].
unfold Interval.with_infsup_raw, Generic.constant. apply tightest_lanes_lub.
- exact (ex_intro _ _ HS).
- (* The least value is [a^c], as [r^t] increases in [r] and, for
     [r >= 1], in [t]. *)
  unfold pow_rd.
  apply (pn_lo_at (image2_set pow_dom Rpow x y)
    (Rpow (B2R (Interval.inf_raw x)) (B2R (Interval.inf_raw y))) _ HS).
  + intros s Hs. destruct (proj1 (pp_img x y s Hx0 Hy0) Hs) as (r & t & Hr & Ht & ->).
    specialize (Hxa r Hr). specialize (Hyc t Ht).
    apply Rle_trans with (Rpow (B2R (Interval.inf_raw x)) t).
    * apply Rpow_le_exp_ge1; lra.
    * apply Rpow_le_base_pos; lra.
  + apply (pow_fin emin emax m Hrg Hg Hp); [exact Fa | exact Fc | left; lra].
- apply (pp_hi_bd emin emax m Hrg Hg Hp x y (B2R (Interval.inf_raw x))
    (Interval.sup_raw x) (Interval.inf_raw y) (Interval.sup_raw y));
    [exact HA0 | exact Hxb | | exact HC0 | exact Hyd].
  (* A finite [b] is at least [a > 1]. *)
  intros Fb. destruct Hxb as [(_ & HAB & _) | (Eb & _)]; [lra|].
  rewrite Eb in Fb. discriminate Fb.
Qed.

Lemma pw_pos_mid :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall x y, pw_xok x -> valid y -> Interval.is_empty y = false ->
  Model.le (Interval.sup_raw y) Model.zero = false ->
  Model.gt (Interval.inf_raw y) Model.zero = true ->
  Model.lt (Interval.sup_raw x) (of_u64 1) = false ->
  Model.gt (Interval.inf_raw x) (of_u64 1) = false ->
  is_tightest (image2_set pow_dom Rpow x y)
    (Interval.with_infsup_raw (pow_rd m (Interval.inf_raw x) (Interval.sup_raw y))
       (pow_ru m (Interval.sup_raw x) (Interval.sup_raw y))).
Proof.
intros emin emax m Hrg Hg Hp x y Hx Hyv Hye _ Hc Hb1 Ha1.
destruct (pp_x x Hx) as (Fa & HA0 & HAz & Hxb).
destruct (pp_y y Hyv Hye Hc) as (Fc & HC0 & Hyd).
destruct (pp_desc_A _ _ _ Hxb) as (Hxa & Hax).
destruct (pp_desc_A _ _ _ Hyd) as (Hyc & Hcy).
assert (Hx0 : forall r, mem r x -> 0 <= r) by (intros r Hr; specialize (Hxa r Hr); lra).
assert (Hy0 : forall t, mem t y -> 0 < t) by (intros t Ht; specialize (Hyc t Ht); lra).
assert (HS : image2_set pow_dom Rpow x y
  (Rpow (B2R (Interval.inf_raw x)) (B2R (Interval.inf_raw y)))).
{ apply (proj2 (pp_img x y _ Hx0 Hy0)).
  exists (B2R (Interval.inf_raw x)), (B2R (Interval.inf_raw y)).
  split; [exact Hax|]. split; [exact Hcy | reflexivity]. }
rewrite pn_gt_1 in Ha1 by exact Fa.
revert Ha1. case Rlt_bool_spec; [discriminate | intros HA1 _].
assert (HbB : is_finite (Interval.sup_raw x) = true -> 1 <= B2R (Interval.sup_raw x)).
{ intros Fb. rewrite pn_lt_1 in Hb1 by exact Fb.
  revert Hb1. case Rlt_bool_spec; [discriminate | intros H _; exact H]. }
unfold Interval.with_infsup_raw, Generic.constant. apply tightest_lanes_lub.
- exact (ex_intro _ _ HS).
- apply (pp_lo_ad emin emax m Hrg Hg Hp x y (Interval.inf_raw x) (Interval.inf_raw y)
    (Interval.sup_raw y) Fa); [lra | exact HAz | exact Hxa | exact Hax | exact HC0 | exact Hyd].
- apply (pp_hi_bd emin emax m Hrg Hg Hp x y (B2R (Interval.inf_raw x))
    (Interval.sup_raw x) (Interval.inf_raw y) (Interval.sup_raw y));
    [exact HA0 | exact Hxb | exact HbB | exact HC0 | exact Hyd].
Qed.
