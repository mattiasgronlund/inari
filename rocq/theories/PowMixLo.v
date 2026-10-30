(** * The lower bound of [Interval::pow] for exponents on both sides of 0

    The lower lane of the branch [c <= 0.0 < d] of [Interval::pow], with
    [x], [a], [b], [y], [c] and [d] as in [PowNeg.v], and [b] not 0. For
    [t] in [y], [r^t] increases in [t] for [r >= 1] and decreases for
    [r <= 1], and for [r > 0] it increases in [r] if [t > 0] and decreases
    if [t <= 0]. So the greatest lower bound is at [(a, d)] for the reals of
    [x] at most 1 ([pxl_lo_ad]) and at [(b, c)] for those at least 1
    ([pxl_lo_bc]), and the lower bound is
    [fmin first_min (pow_rd(a, d)) (pow_rd(b, c))] ([pw_mix_lo]). If
    [a > 1], [x] has no real at most 1, but [pow_rd(a, d)] is still the
    rounded value at a point of the box, or +inf for [d = +inf], so [fmin]
    with it gives a lower lane of the image ([pxl_corner_l]). The same holds
    for [b < 1], the other way round ([pxl_corner_r]). A corner with
    [a = 0], [b = +inf], [c = -inf] or [d = +inf] is a limit, which
    [pow_rd] gives by the special values of [PowMpfr.v]. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Integer Sign MaxMin AddSub
  DecBinary DivTight MpfrRound MonoInc PowReal PowMpfr PowCases PowNeg.

Open Scope R_scope.

(** ** The exponent *)

(** The reals of an exponent [y] with the upper bound [d], a finite float
    above 0 or +inf, and with the lower bound [c], a finite float at most 0
    or -inf. *)
Definition pxl_yd (y : Interval) (d : f64) : Prop :=
  (is_finite d = true /\ 0 < B2R d /\ mem (B2R d) y /\ forall t, mem t y -> t <= B2R d) \/
  (d = B754_infinity false /\ forall t, 0 <= t -> mem t y).

Definition pxl_yc (y : Interval) (c : f64) : Prop :=
  (is_finite c = true /\ B2R c <= 0 /\ mem (B2R c) y /\ forall t, mem t y -> B2R c <= t) \/
  (c = B754_infinity true /\ forall t, t <= 0 -> mem t y).

Lemma pxl_y :
  forall y, valid y -> Interval.is_empty y = false ->
  Model.le (Interval.sup_raw y) Model.zero = false ->
  Model.gt (Interval.inf_raw y) Model.zero = false ->
  pxl_yd y (Interval.sup_raw y) /\ pxl_yc y (Interval.inf_raw y).
Proof.
intros y Hv He Hd Hc.
destruct (valid_nonempty y Hv He) as (Hlo & Hup & _).
assert (Hm := fun t => mem_bounds y t Hlo Hup).
unfold Interval.inf_raw, Interval.sup_raw, pxl_yd, pxl_yc in *.
(* [d <= 0] is false, so a finite [d] is above 0. *)
assert (HD : is_finite (snd (rep y)) = true -> 0 < B2R (snd (rep y))).
{ intros Fd. unfold Model.le in Hd. rewrite Bleb_correct in Hd by first [exact Fd | reflexivity].
  change (B2R Model.zero) with 0 in Hd.
  revert Hd. case Rle_bool_spec; [discriminate | intros H _; exact H]. }
(* [c > 0] is false, so a finite [c] is at most 0. *)
assert (HC : is_finite (opp (fst (rep y))) = true -> B2R (opp (fst (rep y))) <= 0).
{ intros Fc. unfold Model.gt in Hc. rewrite Bltb_correct in Hc by first [exact Fc | reflexivity].
  change (B2R Model.zero) with 0 in Hc.
  revert Hc. case Rlt_bool_spec; [discriminate | intros H _; exact H]. }
destruct Hup as [Fd | Ed], Hlo as [Fc | Ec].
- specialize (HD Fd). specialize (HC Fc).
  rewrite (bound_finite _ Fd), (bound_finite _ Fc) in Hm. unfold in_bounds in Hm; cbv beta iota in Hm.
  split; left.
  + split; [exact Fd|]. split; [exact HD|].
    split; [apply Hm; lra | intros t Ht; apply Hm in Ht; lra].
  + split; [exact Fc|]. split; [exact HC|].
    split; [apply Hm; lra | intros t Ht; apply Hm in Ht; lra].
- specialize (HD Fd).
  rewrite (bound_finite _ Fd), Ec, bound_inf in Hm. unfold in_bounds in Hm; cbv beta iota in Hm.
  split; [left | right].
  + split; [exact Fd|]. split; [exact HD|].
    split; [apply Hm; split; [exact I | lra] | intros t Ht; apply Hm in Ht; exact (proj2 Ht)].
  + split; [exact Ec|]. intros t Ht. apply Hm. split; [exact I | lra].
- specialize (HC Fc).
  rewrite Ed, bound_inf, (bound_finite _ Fc) in Hm. unfold in_bounds in Hm; cbv beta iota in Hm.
  split; [right | left].
  + split; [exact Ed|]. intros t Ht. apply Hm. split; [lra | exact I].
  + split; [exact Fc|]. split; [exact HC|].
    split; [apply Hm; split; [lra | exact I] | intros t Ht; apply Hm in Ht; exact (proj1 Ht)].
- rewrite Ed, Ec, !bound_inf in Hm. unfold in_bounds in Hm; cbv beta iota in Hm.
  split; right.
  + split; [exact Ed|]. intros t _. apply Hm. split; exact I.
  + split; [exact Ec|]. intros t _. apply Hm. split; exact I.
Qed.

(** ** The image *)

(** The values at the points of the box with [r <= 1], and with
    [r >= 1]. *)
Definition pxl_le1 (x y : Interval) (s : R) : Prop :=
  exists r t, mem r x /\ r <= 1 /\ mem t y /\ pow_dom r t /\ s = Rpow r t.

Definition pxl_ge1 (x y : Interval) (s : R) : Prop :=
  exists r t, mem r x /\ 1 <= r /\ mem t y /\ pow_dom r t /\ s = Rpow r t.

Lemma pxl_split :
  forall x y s, image2_set pow_dom Rpow x y s <-> pxl_le1 x y s \/ pxl_ge1 x y s.
Proof.
intros x y s. split.
- intros (r & t & Hr & Ht & Hd & Hs). destruct (Rle_or_lt r 1) as [H1 | H1].
  + left. exists r, t. exact (conj Hr (conj H1 (conj Ht (conj Hd Hs)))).
  + right. exists r, t. refine (conj Hr (conj _ (conj Ht (conj Hd Hs)))). lra.
- intros [(r & t & Hr & _ & Ht & Hd & Hs) | (r & t & Hr & _ & Ht & Hd & Hs)];
    exists r, t; exact (conj Hr (conj Ht (conj Hd Hs))).
Qed.

(** ** The two corners *)

(** The lower lane [pow_rd(a, d)] of the values with [r <= 1], for
    [0 <= a <= 1]: for [0 < r <= 1], [r^t] decreases in [t] and, for
    [t = d > 0], increases in [r]; [r = 0] gives 0, and then [a = 0]. It is
    attained if [d] is finite. For [d = +inf], it is attained at [(0, 1)]
    if [a = 0], it is the limit 0 of [a^t] if [0 < a < 1], and it is 1 at
    [r = 1] if [a = 1]. *)
Lemma pxl_lo_ad :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall x y a d, is_finite a = true -> 0 <= B2R a -> B2R a <= 1 ->
  (B2R a = 0 -> a = B754_zero false) ->
  mem (B2R a) x -> (forall r, mem r x -> B2R a <= r) -> pxl_yd y d ->
  lane_ok (fun s => pxl_le1 x y (- s)) (opp (pow_rd m a d)).
Proof.
intros emin emax m Hrg Hg Hp x y a d Fa HA0 HA1 HAz HAx Hxa Hyd.
assert (Hpos : forall s, pxl_le1 x y s -> 0 <= s).
{ intros s (r & t & Hr & _ & _ & _ & ->). apply Rpow_ge_0. specialize (Hxa r Hr). lra. }
unfold pow_rd.
destruct Hyd as [(Fd & HD0 & HDy & HyD) | (Ed & Hy0)].
- (* [d] finite: the least value is [a^d]. *)
  assert (Had : pow_dom (B2R a) (B2R d)).
  { destruct (Req_dec (B2R a) 0) as [H0 | H0]; [right; split; [exact H0 | exact HD0] | left; lra]. }
  apply (pn_lo_at (pxl_le1 x y) (Rpow (B2R a) (B2R d))).
  + exists (B2R a), (B2R d). exact (conj HAx (conj HA1 (conj HDy (conj Had eq_refl)))).
  + intros s (r & t & Hr & Hr1 & Ht & _ & ->).
    specialize (Hxa r Hr). specialize (HyD t Ht).
    destruct (Rle_lt_or_eq_dec 0 r (Rle_trans _ _ _ HA0 Hxa)) as [Hr0 | Hr0].
    * apply Rle_trans with (Rpow r (B2R d)).
      -- apply Rpow_le_base_pos; lra.
      -- apply Rpow_le_exp_le1; lra.
    * (* [r = 0], so [a = 0], and both values are 0. *)
      subst r. replace (B2R a) with 0 by lra. rewrite !Rpow_0_l. lra.
  + apply (pow_fin emin emax m Hrg Hg Hp); [exact Fa | exact Fd | exact Had].
- rewrite Ed. destruct (Req_dec (B2R a) 0) as [H0 | H0].
  + (* [a = +0], [d = +inf]: the least value is 0, at [(0, 1)]. *)
    rewrite (HAz H0).
    apply (pn_lo_at (pxl_le1 x y) 0); [| exact Hpos |].
    * exists 0, 1. refine (conj _ (conj _ (conj _ (conj _ _)))).
      -- rewrite <- H0. exact HAx.
      -- lra.
      -- apply Hy0. lra.
      -- right. split; [reflexivity | lra].
      -- symmetry. apply Rpow_0_l.
    * apply (pow_zero_pinf emin emax m Hg Hp).
  + destruct (Rle_lt_or_eq_dec _ _ HA1) as [HA1' | HA1'].
    * (* [0 < a < 1], [d = +inf]: [a^t] tends to 0 as [t] grows. *)
      assert (HA01 : 0 < B2R a < 1) by lra.
      apply pn_lo_0; [exact Hpos | |].
      -- intros eps He. destruct (Rpow_exp_large_lt1 (B2R a) eps HA01 He) as (t0 & Ht0).
         exists (Rpow (B2R a) (Rabs t0)). split.
         ++ exists (B2R a), (Rabs t0).
            refine (conj HAx (conj HA1 (conj _ (conj _ eq_refl)))).
            ** apply Hy0, Rabs_pos.
            ** left. lra.
         ++ apply Ht0, Rle_abs.
      -- apply (pow_lt1_pinf emin emax m Hg Hp); [exact Fa | exact HA01].
    * (* [a = 1], [d = +inf]: every [r] is 1, and every value is 1. *)
      apply (pn_lo_at (pxl_le1 x y) 1).
      -- exists (B2R a), 0. refine (conj HAx (conj HA1 (conj _ (conj _ _)))).
         ++ apply Hy0. lra.
         ++ left. lra.
         ++ rewrite HA1'. symmetry. apply Rpow_1_l.
      -- intros s (r & t & Hr & Hr1 & _ & _ & ->). specialize (Hxa r Hr).
         replace r with 1 by lra. rewrite Rpow_1_l. lra.
      -- apply (pow_one_inf emin emax m Hrg Hg Hp); [exact Fa | exact HA1'].
Qed.

(** The lower lane [pow_rd(b, c)] of the values with [r >= 1], for
    [b >= 1] or [b = +inf], as [pn_lo_bc] for [y] in [(-inf, 0]]: for
    [r >= 1], [r^t] increases in [t] and, for [t = c <= 0], decreases in
    [r]. It is attained if [b] and [c] are finite. Otherwise it is 0
    ([b > 1] or [b = +inf], with [c < 0] or [c = -inf]), or 1 ([b = 1] and
    [c = -inf]: every [r] is 1; [b = +inf] and [c = 0]: every value is
    [r^t >= r^0 = 1]). *)
Lemma pxl_lo_bc :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall x y A b c, 0 <= A -> pn_xdesc x A b -> (is_finite b = true -> 1 <= B2R b) ->
  pxl_yc y c ->
  lane_ok (fun s => pxl_ge1 x y (- s)) (opp (pow_rd m b c)).
Proof.
intros emin emax m Hrg Hg Hp x y A b c HA0 Hxb Hb1 Hyc.
assert (Hpos : forall s, pxl_ge1 x y s -> 0 <= s).
{ intros s (r & t & _ & Hr1 & _ & _ & ->). apply Rpow_ge_0. lra. }
unfold pow_rd.
destruct Hxb as [(Fb & HB0 & HAB & Hmx) | (Eb & Hmx)];
  [specialize (Hb1 Fb) |];
  destruct Hyc as [(Fc & HC0 & HCy & HyC) | (Ec & Hy0)].
- (* [b] and [c] finite: the least value is [b^c]. *)
  apply (pn_lo_at (pxl_ge1 x y) (Rpow (B2R b) (B2R c))).
  + exists (B2R b), (B2R c). refine (conj _ (conj Hb1 (conj HCy (conj _ eq_refl)))).
    * apply Hmx. lra.
    * left. lra.
  + intros s (r & t & Hr & Hr1 & Ht & _ & ->). apply Hmx in Hr. specialize (HyC t Ht).
    apply Rle_trans with (Rpow r (B2R c)).
    * apply Rpow_le_base_neg; lra.
    * apply Rpow_le_exp_ge1; lra.
  + apply (pow_fin emin emax m Hrg Hg Hp); [exact Fb | exact Fc | left; lra].
- rewrite Ec. destruct (Rle_lt_or_eq_dec 1 (B2R b) Hb1) as [HB1 | HB1].
  + (* [b > 1], [c = -inf]: [b^t] tends to 0 as [t] falls. *)
    apply pn_lo_0; [exact Hpos | |].
    * intros eps He. destruct (Rpow_exp_small_gt1 (B2R b) eps HB1 He) as (t0 & Ht0).
      exists (Rpow (B2R b) (Rmin t0 0)). split.
      -- exists (B2R b), (Rmin t0 0). refine (conj _ (conj Hb1 (conj _ (conj _ eq_refl)))).
         ++ apply Hmx. lra.
         ++ apply Hy0, Rmin_r.
         ++ left. lra.
      -- apply Ht0, Rmin_l.
    * apply (pow_gt1_ninf emin emax m Hg Hp); [exact Fb | exact HB1].
  + (* [b = 1], [c = -inf]: every [r] is 1, and every value is 1. *)
    apply (pn_lo_at (pxl_ge1 x y) 1).
    * exists (B2R b), 0. refine (conj _ (conj Hb1 (conj _ (conj _ _)))).
      -- apply Hmx. lra.
      -- apply Hy0. lra.
      -- left. lra.
      -- rewrite <- HB1. symmetry. apply Rpow_1_l.
    * intros s (r & t & Hr & Hr1 & _ & _ & ->). apply Hmx in Hr.
      replace r with 1 by lra. rewrite Rpow_1_l. lra.
    * apply (pow_one_inf emin emax m Hrg Hg Hp); [exact Fb | lra].
- rewrite Eb. destruct (Rle_lt_or_eq_dec _ _ HC0) as [HC0' | HC0'].
  + (* [b = +inf], [c < 0]: [r^c] tends to 0 as [r] grows. *)
    apply pn_lo_0; [exact Hpos | |].
    * intros eps He. destruct (Rpow_base_large_neg (B2R c) eps HC0' He) as (r0 & Hr0 & Hr0e).
      exists (Rpow (r0 + A + 1) (B2R c)). split.
      -- exists (r0 + A + 1), (B2R c). refine (conj _ (conj _ (conj HCy (conj _ eq_refl)))).
         ++ apply Hmx. lra.
         ++ lra.
         ++ left. lra.
      -- apply Hr0e. lra.
    * apply (pow_pinf_neg emin emax m Hg Hp). left. split; [exact Fc | exact HC0'].
  + (* [b = +inf], [c] a zero: every value is [r^t >= r^0 = 1], and
       [(A + 1, 0)] gives 1. *)
    destruct (pn_zero c Fc HC0') as (sc & Ec0). rewrite Ec0.
    apply (pn_lo_at (pxl_ge1 x y) 1).
    * exists (A + 1), 0. refine (conj _ (conj _ (conj _ (conj _ _)))).
      -- apply Hmx. lra.
      -- lra.
      -- rewrite <- HC0'. exact HCy.
      -- left. lra.
      -- symmetry. apply Rpow_0_r. lra.
    * intros s (r & t & Hr & Hr1 & Ht & _ & ->). specialize (HyC t Ht).
      rewrite <- (Rpow_0_r r) by lra. apply Rpow_le_exp_ge1; lra.
    * apply (pow_pinf_zero emin emax m Hrg Hg Hp).
- (* [b = +inf], [c = -inf]: [r^(-1)] tends to 0 as [r] grows. *)
  rewrite Eb, Ec. apply pn_lo_0; [exact Hpos | |].
  + intros eps He. assert (Hm1 : -1 < 0) by lra.
    destruct (Rpow_base_large_neg (-1) eps Hm1 He) as (r0 & Hr0 & Hr0e).
    exists (Rpow (r0 + A + 1) (-1)). split.
    * exists (r0 + A + 1), (-1). refine (conj _ (conj _ (conj _ (conj _ eq_refl)))).
      -- apply Hmx. lra.
      -- lra.
      -- apply Hy0. lra.
      -- left. lra.
    * apply Hr0e. lra.
  + apply (pow_pinf_neg emin emax m Hg Hp). right. reflexivity.
Qed.

(** ** [fmin] *)

(** A lower lane is not the negation of NaN. *)
Lemma pxl_not_nan : forall (T : R -> Prop) w, lane_ok T (opp w) -> is_nan w = false.
Proof.
intros T w (o & _ & [Fw | Ew] & _).
- rewrite is_finite_opp in Fw. destruct w; try discriminate Fw; reflexivity.
- destruct w; try discriminate Ew; reflexivity.
Qed.

(** [fmin] with +inf, and an argument that is not NaN, is that
    argument. *)
Lemma pxl_fmin_inf_l :
  forall first w, is_nan w = false -> fmin first (B754_infinity false) w = w.
Proof.
intros first [s|[|]| |s mw ew Hw] Hn; try discriminate Hn; destruct first; reflexivity.
Qed.

Lemma pxl_fmin_inf_r :
  forall first w, is_nan w = false -> fmin first w (B754_infinity false) = w.
Proof.
intros first [s|[|]| |s mw ew Hw] Hn; try discriminate Hn; destruct first; reflexivity.
Qed.

(** If [v] is a value of [S] and [w1] is [v] rounded down, then [fmin] of
    [w1] and a lower lane [w2] of [S] is again a lower lane of [S], as
    [S] is [S] with [v] added. *)
Lemma pxl_corner_l :
  forall (S : R -> Prop) v w1 w2 first, S v ->
  mpfr_round f64_format RNDD v (with_val w1) ->
  lane_ok (fun s => S (- s)) (opp w2) ->
  lane_ok (fun s => S (- s)) (opp (fmin first w1 w2)).
Proof.
intros S v w1 w2 first Hv Hw1 H2.
assert (H1 : lane_ok (fun s => (fun u => u = v) (- s)) (opp w1)).
{ apply (pn_lo_at (fun u => u = v) v w1 eq_refl); [intros s Hs; cbv beta in Hs; lra | exact Hw1]. }
apply (lane_ok_ext (fun s => (fun u => u = v) (- s) \/ S (- s))).
- intros s. cbv beta.
  split; [intros [H | H]; [rewrite H; exact Hv | exact H] | intros H; right; exact H].
- exact (pl_lo_fmin (fun u => u = v) S w1 w2 first
    (pxl_not_nan _ _ H1) (pxl_not_nan _ _ H2) H1 H2).
Qed.

Lemma pxl_corner_r :
  forall (S : R -> Prop) v w1 w2 first, S v ->
  mpfr_round f64_format RNDD v (with_val w2) ->
  lane_ok (fun s => S (- s)) (opp w1) ->
  lane_ok (fun s => S (- s)) (opp (fmin first w1 w2)).
Proof.
intros S v w1 w2 first Hv Hw2 H1.
assert (H2 : lane_ok (fun s => (fun u => u = v) (- s)) (opp w2)).
{ apply (pn_lo_at (fun u => u = v) v w2 eq_refl); [intros s Hs; cbv beta in Hs; lra | exact Hw2]. }
apply (lane_ok_ext (fun s => S (- s) \/ (fun u => u = v) (- s))).
- intros s. cbv beta.
  split; [intros [H | H]; [exact H | rewrite H; exact Hv] | intros H; left; exact H].
- exact (pl_lo_fmin S (fun u => u = v) w1 w2 first
    (pxl_not_nan _ _ H1) (pxl_not_nan _ _ H2) H1 H2).
Qed.

(** ** The lower lane *)

Lemma pw_mix_lo :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall first_min x y, pw_xok x -> valid y -> Interval.is_empty y = false ->
  Model.le (Interval.sup_raw y) Model.zero = false ->
  Model.gt (Interval.inf_raw y) Model.zero = false ->
  Model.eq (Interval.sup_raw x) Model.zero = false ->
  lane_ok (fun s => image2_set pow_dom Rpow x y (- s))
    (opp (fmin first_min (pow_rd m (Interval.inf_raw x) (Interval.sup_raw y))
            (pow_rd m (Interval.sup_raw x) (Interval.inf_raw y)))).
Proof.
intros emin emax m Hrg Hg Hp first_min x y Hx Hyv Hye Hd Hc Hb0.
destruct (pn_x x Hx Hb0) as (Fa & HA0 & HAz & Hxb).
destruct (pn_xA _ _ _ Hxb) as (Hxa & HAx).
destruct (pxl_y y Hyv Hye Hd Hc) as (Hyd & Hyc).
destruct (Rle_or_lt (B2R (Interval.inf_raw x)) 1) as [HA1 | HA1].
- assert (Hlo1 := pxl_lo_ad emin emax m Hrg Hg Hp x y (Interval.inf_raw x) (Interval.sup_raw y)
    Fa HA0 HA1 HAz HAx Hxa Hyd).
  assert (Hcase : (is_finite (Interval.sup_raw x) = true /\ B2R (Interval.sup_raw x) < 1) \/
                  (is_finite (Interval.sup_raw x) = true -> 1 <= B2R (Interval.sup_raw x))).
  { destruct Hxb as [(Fb & _) | (Eb & _)].
    - destruct (Rlt_or_le (B2R (Interval.sup_raw x)) 1) as [H | H];
        [left; split; [exact Fb | exact H] | right; intros _; exact H].
    - right. rewrite Eb. intros F. discriminate F. }
  destruct Hcase as [(Fb & HB1) | HbB].
  + (* [b < 1]: every real of [x] is below 1, and the corner [(b, c)] is
       dominated. *)
    destruct Hxb as [(_ & HB0 & HAB & Hmx) | (Eb & _)]; [| rewrite Eb in Fb; discriminate Fb].
    assert (Himg : forall s, pxl_le1 x y s <-> image2_set pow_dom Rpow x y s).
    { intros s. rewrite pxl_split. split; [intros H; left; exact H|].
      intros [H | (r & t & Hr & Hr1 & _)]; [exact H | apply Hmx in Hr; lra]. }
    apply (lane_ok_ext _ _ _ (fun s => Himg (- s))) in Hlo1.
    destruct Hyc as [(Fc & HC0 & HCy & HyC) | (Ec & Hy0)].
    * apply (pxl_corner_r _ (Rpow (B2R (Interval.sup_raw x)) (B2R (Interval.inf_raw y))));
        [| | exact Hlo1].
      -- exists (B2R (Interval.sup_raw x)), (B2R (Interval.inf_raw y)).
         refine (conj _ (conj HCy (conj _ eq_refl))); [apply Hmx; lra | left; lra].
      -- apply (pow_fin emin emax m Hrg Hg Hp); [exact Fb | exact Fc | left; lra].
    * (* [c = -inf]: [pow_rd(b, -inf)] is +inf. *)
      rewrite Ec.
      assert (E : pow_rd m (Interval.sup_raw x) (B754_infinity true) = B754_infinity false)
        by exact (pow_lt1_ninf emin emax m Hg Hp RNDD _ Fb (conj HB0 HB1)).
      rewrite E, pxl_fmin_inf_r by exact (pxl_not_nan _ _ Hlo1). exact Hlo1.
  + (* [a <= 1 <= b]: the image is the union of the two parts. *)
    assert (Hlo2 := pxl_lo_bc emin emax m Hrg Hg Hp x y _ _ _ HA0 Hxb HbB Hyc).
    apply (lane_ok_ext (fun s => pxl_le1 x y (- s) \/ pxl_ge1 x y (- s))).
    * intros s. symmetry. apply pxl_split.
    * exact (pl_lo_fmin _ _ _ _ first_min (pxl_not_nan _ _ Hlo1) (pxl_not_nan _ _ Hlo2)
        Hlo1 Hlo2).
- (* [a > 1]: every real of [x] is above 1, and the corner [(a, d)] is
     dominated. *)
  assert (Hb1 : is_finite (Interval.sup_raw x) = true -> 1 <= B2R (Interval.sup_raw x)).
  { intros Fb. destruct Hxb as [(_ & _ & HAB & _) | (Eb & _)]; [lra|].
    rewrite Eb in Fb. discriminate Fb. }
  assert (Hlo2 := pxl_lo_bc emin emax m Hrg Hg Hp x y _ _ _ HA0 Hxb Hb1 Hyc).
  assert (Himg : forall s, pxl_ge1 x y s <-> image2_set pow_dom Rpow x y s).
  { intros s. rewrite pxl_split. split; [intros H; right; exact H|].
    intros [(r & t & Hr & Hr1 & _) | H]; [specialize (Hxa r Hr); lra | exact H]. }
  apply (lane_ok_ext _ _ _ (fun s => Himg (- s))) in Hlo2.
  destruct Hyd as [(Fd & HD0 & HDy & HyD) | (Ed & Hy0)].
  + apply (pxl_corner_l _ (Rpow (B2R (Interval.inf_raw x)) (B2R (Interval.sup_raw y))));
      [| | exact Hlo2].
    * exists (B2R (Interval.inf_raw x)), (B2R (Interval.sup_raw y)).
      refine (conj HAx (conj HDy (conj _ eq_refl))). left. lra.
    * apply (pow_fin emin emax m Hrg Hg Hp); [exact Fa | exact Fd | left; lra].
  + (* [d = +inf]: [pow_rd(a, +inf)] is +inf. *)
    rewrite Ed.
    assert (E : pow_rd m (Interval.inf_raw x) (B754_infinity false) = B754_infinity false)
      by exact (pow_gt1_pinf emin emax m Hg Hp RNDD _ Fa HA1).
    rewrite E, pxl_fmin_inf_l by exact (pxl_not_nan _ _ Hlo2). exact Hlo2.
Qed.
