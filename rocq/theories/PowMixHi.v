(** * The upper bound of [Interval::pow] for exponents on both sides of 0

    The upper lane of the branch [c <= 0.0 < d] of [Interval::pow], with
    [x], [a], [b], [y], [c] and [d] as in [PowNeg.v], and [b] not 0. For
    [t] in [y], [r^t] increases in [t] for [r >= 1] and decreases for
    [r <= 1], and for [r > 0] it increases in [r] if [t > 0] and decreases
    if [t <= 0]. So the least upper bound is at [(a, c)] for the reals of
    [x] at most 1 and at [(b, d)] for those at least 1, and the upper bound
    is [fmax first_max (pow_ru(a, c)) (pow_ru(b, d))] ([pw_mix_hi]). If
    [a > 1], [x] has no real at most 1, and [pow_ru(a, c)] is at most 1,
    so at most [pow_ru(b, d)], which [fmax] then picks, or one of the same
    value. The same holds for [b < 1], the other way round. A corner with
    [a = 0], [b = +inf], [c = -inf] or [d = +inf] is a limit, which
    [pow_ru] gives by the special values of [PowMpfr.v]. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Integer Sign MaxMin AddSub
  DecBinary DivTight MpfrRound MonoInc PowReal PowMpfr PowCases PowNeg.

Open Scope R_scope.

(** ** The exponent and the two parts of the image *)

(** The reals of an exponent [y] with [c <= 0 < d], seen from one bound:
    [y] holds [[c, 0]] and has no real below a finite [c], or holds
    [(-inf, 0]]; and it holds [[0, d]] and has no real above a finite [d],
    or holds [[0, +inf)]. *)
Definition pxh_cdesc (y : Interval) (c : f64) : Prop :=
  (is_finite c = true /\ B2R c <= 0 /\ (forall t, mem t y -> B2R c <= t) /\
   forall t, B2R c <= t <= 0 -> mem t y) \/
  (c = B754_infinity true /\ forall t, t <= 0 -> mem t y).

Definition pxh_ddesc (y : Interval) (d : f64) : Prop :=
  (is_finite d = true /\ 0 < B2R d /\ (forall t, mem t y -> t <= B2R d) /\
   forall t, 0 <= t <= B2R d -> mem t y) \/
  (d = B754_infinity false /\ forall t, 0 <= t -> mem t y).

Lemma pxh_y :
  forall y, valid y -> Interval.is_empty y = false ->
  Model.le (Interval.sup_raw y) Model.zero = false ->
  Model.gt (Interval.inf_raw y) Model.zero = false ->
  pxh_cdesc y (Interval.inf_raw y) /\ pxh_ddesc y (Interval.sup_raw y).
Proof.
intros y Hv He Hd Hc.
destruct (valid_nonempty y Hv He) as (Hlo & Hup & _).
assert (Hm := fun t => mem_bounds y t Hlo Hup).
unfold Interval.inf_raw, Interval.sup_raw, pxh_cdesc, pxh_ddesc in *.
(* [c <= 0] and [d > 0] as reals, when they are finite. *)
assert (HC : is_finite (opp (fst (rep y))) = true -> B2R (opp (fst (rep y))) <= 0).
{ intros Fc. unfold Model.gt in Hc. rewrite Bltb_correct in Hc by first [exact Fc | reflexivity].
  change (B2R Model.zero) with 0 in Hc.
  revert Hc. case Rlt_bool_spec; [discriminate | intros H _; exact H]. }
assert (HD : is_finite (snd (rep y)) = true -> 0 < B2R (snd (rep y))).
{ intros Fd. unfold Model.le in Hd. rewrite Bleb_correct in Hd by first [exact Fd | reflexivity].
  change (B2R Model.zero) with 0 in Hd.
  revert Hd. case Rle_bool_spec; [discriminate | intros H _; exact H]. }
(* A real at most 0 is below [d], and one at least 0 is above [c]. *)
assert (Hhi : forall t, t <= 0 ->
  match bound (snd (rep y)) with Some b => t <= b | None => True end).
{ intros t Ht. destruct Hup as [Fd | Ed].
  - rewrite (bound_finite _ Fd). cbv beta iota. specialize (HD Fd). lra.
  - rewrite Ed, bound_inf. exact I. }
assert (Hlo' : forall t, 0 <= t ->
  match bound (opp (fst (rep y))) with Some a => a <= t | None => True end).
{ intros t Ht. destruct Hlo as [Fc | Ec].
  - rewrite (bound_finite _ Fc). cbv beta iota. specialize (HC Fc). lra.
  - rewrite Ec, bound_inf. exact I. }
split.
- destruct Hlo as [Fc | Ec].
  + left. specialize (HC Fc). split; [exact Fc|]. split; [exact HC|]. split.
    * intros t Ht. apply Hm in Ht. unfold in_bounds in Ht.
      rewrite (bound_finite _ Fc) in Ht. exact (proj1 Ht).
    * intros t Ht. apply Hm. unfold in_bounds. split.
      -- rewrite (bound_finite _ Fc). cbv beta iota. lra.
      -- apply Hhi. lra.
  + right. split; [exact Ec|]. intros t Ht. apply Hm. unfold in_bounds. split.
    * rewrite Ec, bound_inf. exact I.
    * apply Hhi. lra.
- destruct Hup as [Fd | Ed].
  + left. specialize (HD Fd). split; [exact Fd|]. split; [exact HD|]. split.
    * intros t Ht. apply Hm in Ht. unfold in_bounds in Ht.
      rewrite (bound_finite _ Fd) in Ht. exact (proj2 Ht).
    * intros t Ht. apply Hm. unfold in_bounds. split.
      -- apply Hlo'. lra.
      -- rewrite (bound_finite _ Fd). cbv beta iota. lra.
  + right. split; [exact Ed|]. intros t Ht. apply Hm. unfold in_bounds. split.
    * apply Hlo'. lra.
    * rewrite Ed, bound_inf. exact I.
Qed.

(** The values at the points of the domain in the box with [r <= 1], and
    those with [r >= 1]. Together they are the image. *)
Definition pxh_S1 (x y : Interval) : R -> Prop :=
  fun s => exists r t, mem r x /\ r <= 1 /\ mem t y /\ pow_dom r t /\ s = Rpow r t.

Definition pxh_S2 (x y : Interval) : R -> Prop :=
  fun s => exists r t, mem r x /\ 1 <= r /\ mem t y /\ pow_dom r t /\ s = Rpow r t.

Lemma pxh_img_split :
  forall x y s, image2_set pow_dom Rpow x y s <-> pxh_S1 x y s \/ pxh_S2 x y s.
Proof.
intros x y s. split.
- intros (r & t & Hr & Ht & Hd & Hs).
  destruct (Rle_or_lt r 1) as [H1 | H1]; [left | right]; exists r, t;
    (split; [exact Hr|]); (split; [lra|]); (split; [exact Ht|]); (split; [exact Hd | exact Hs]).
- intros [(r & t & Hr & _ & Ht & Hd & Hs) | (r & t & Hr & _ & Ht & Hd & Hs)]; exists r, t;
    (split; [exact Hr|]); (split; [exact Ht|]); (split; [exact Hd | exact Hs]).
Qed.

(** ** Floats *)

(** A float rounded up from 0 is a zero. *)
Lemma pxh_round_0 :
  forall w : f64, mpfr_round f64_format RNDU 0 (with_val w) -> exists s, w = B754_zero s.
Proof.
assert (F0 : f64_format 0) by (exists (B754_zero false); split; reflexivity).
intros w H. destruct w as [s|[|]| |s mw ew Hw]; cbn [with_val mpfr_round] in H;
  try contradiction.
- exists s. reflexivity.
- (* +inf would need every [f64] below 0. *)
  specialize (H 0 F0). lra.
- (* A finite float other than 0 at or above 0 is above the [f64] 0. *)
  exfalso. destruct H as (H0 & _ & Hge & Hmin). apply H0.
  apply Rle_antisym; [apply Hmin; [exact F0 | apply Rle_refl] | exact Hge].
Qed.

(** A float above 0: +inf, or a finite one with a real above 0. *)
Definition pxh_pos (w : f64) : Prop :=
  w = B754_infinity false \/ (is_finite w = true /\ 0 < B2R w).

Lemma pxh_round_pos :
  forall r w, 0 < r -> mpfr_round f64_format RNDU r (with_val w) -> pxh_pos w.
Proof.
intros r w Hr H. destruct (round_up_lane r w H) as ([Fw | Ew] & Hle & _).
- right. split; [exact Fw|]. rewrite (bound_finite _ Fw) in Hle.
  specialize (Hle r (Rle_refl r)). cbn [below] in Hle. lra.
- left. exact Ew.
Qed.

(** The comparisons that [fmax] makes between a zero and a float above
    0. *)
Lemma pxh_lt_0_pos :
  forall s w, pxh_pos w -> Model.lt (B754_zero s) w = true.
Proof.
intros s w [-> | (Fw & Hw)].
- destruct s; reflexivity.
- unfold Model.lt. rewrite Bltb_correct by first [exact Fw | reflexivity].
  apply Rlt_bool_true. exact Hw.
Qed.

Lemma pxh_lt_pos_0 :
  forall s w, pxh_pos w -> Model.lt w (B754_zero s) = false.
Proof.
intros s w [-> | (Fw & Hw)].
- destruct s; reflexivity.
- unfold Model.lt. rewrite Bltb_correct by first [exact Fw | reflexivity].
  apply Rlt_bool_false. apply Rlt_le. exact Hw.
Qed.

(** A lane is not NaN, as [pl_hi_fmax] asks. *)
Lemma pxh_not_nan : forall S w, lane_ok S w -> is_nan w = false.
Proof.
intros S w (o & _ & [Fw | ->] & _); [|reflexivity].
destruct w; try discriminate Fw; reflexivity.
Qed.

(** [pow_ru(a, c)] for [0 <= a < 1] is above 0: +inf ([a = 0] with
    [c < 0] or [c = -inf], and [0 < a < 1] with [c = -inf]), 1 rounded up
    ([a = 0] and [c = 0]), or [a^c > 0] rounded up. *)
Lemma pxh_ac_pos :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall a c, is_finite a = true -> 0 <= B2R a < 1 -> (B2R a = 0 -> a = B754_zero false) ->
  (is_finite c = true /\ B2R c <= 0) \/ c = B754_infinity true ->
  pxh_pos (pow_ru m a c).
Proof.
intros emin emax m Hrg Hg Hp a c Fa HA HAz Hc. unfold pow_ru.
destruct (Req_dec (B2R a) 0) as [HAe | HAp].
- rewrite (HAz HAe). destruct Hc as [(Fc & HC0) | ->].
  + destruct (Rle_lt_or_eq_dec _ _ HC0) as [HC0' | HCe].
    * left. exact (pow_zero_neg emin emax m Hg Hp RNDU c (or_introl (conj Fc HC0'))).
    * destruct (pn_zero c Fc HCe) as (sc & ->).
      apply (pxh_round_pos 1); [lra|].
      exact (pow_zero_zero emin emax m Hrg Hg Hp RNDU sc).
  + left. exact (pow_zero_neg emin emax m Hg Hp RNDU _ (or_intror eq_refl)).
- assert (HA' : 0 < B2R a < 1) by lra.
  destruct Hc as [(Fc & HC0) | ->].
  + apply (pxh_round_pos (Rpow (B2R a) (B2R c))); [apply Rpow_gt_0; lra|].
    apply (pow_fin emin emax m Hrg Hg Hp); [exact Fa | exact Fc | left; lra].
  + left. exact (pow_lt1_ninf emin emax m Hg Hp RNDU a Fa HA').
Qed.

(** [pow_ru(b, d)] for [b > 1] or [b = +inf], and [d > 0] or [d = +inf],
    is above 0: +inf, or [b^d > 0] rounded up. *)
Lemma pxh_bd_pos :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall b d, (is_finite b = true /\ 1 < B2R b) \/ b = B754_infinity false ->
  (is_finite d = true /\ 0 < B2R d) \/ d = B754_infinity false ->
  pxh_pos (pow_ru m b d).
Proof.
intros emin emax m Hrg Hg Hp b d Hb Hd. unfold pow_ru.
destruct Hb as [(Fb & HB1) | ->].
- destruct Hd as [(Fd & HD0) | ->].
  + apply (pxh_round_pos (Rpow (B2R b) (B2R d))); [apply Rpow_gt_0; lra|].
    apply (pow_fin emin emax m Hrg Hg Hp); [exact Fb | exact Fd | left; lra].
  + left. exact (pow_gt1_pinf emin emax m Hg Hp RNDU b Fb HB1).
- left. exact (pow_pinf_pos emin emax m Hg Hp RNDU d Hd).
Qed.

(** ** The lanes of the two parts *)

(** The upper lane [pow_ru(a, c)] of the part [r <= 1], where [x] holds
    the reals of [[a, R1]] for some [0 < R1 <= 1]: for [0 < r <= 1],
    [r^t <= r^c <= a^c], as [r^t] decreases in [t] and, for [c <= 0], in
    [r]; and a point with [r = 0] has [t > 0] and the value 0. The bound is
    attained if [a > 0] and [c] is finite. Otherwise the values have no
    upper bound ([a = 0] with [c < 0] or [c = -inf], as [r^t] for a fixed
    [t < 0] grows without bound as [r] tends to 0; [0 < a < 1] with
    [c = -inf]), or the bound is 1 ([a = 0] and [c = 0]: every value is
    at most [r^0 = 1] or 0; [a = 1] and [c = -inf]: the part holds only
    [r = 1]). This is [pn_hi_ac] for an exponent that also has reals
    above 0. *)
Lemma pxh_hi_ac :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall x y a R1 c,
  is_finite a = true -> 0 <= B2R a -> (B2R a = 0 -> a = B754_zero false) ->
  0 < R1 -> R1 <= 1 -> B2R a <= R1 ->
  (forall r, mem r x -> B2R a <= r) -> (forall r, B2R a <= r <= R1 -> mem r x) ->
  pxh_cdesc y c ->
  lane_ok (pxh_S1 x y) (pow_ru m a c).
Proof.
intros emin emax m Hrg Hg Hp x y a R1 c Fa HA0 HAz HR0 HR1 HAR Hxa Hax Hyc.
unfold pow_ru.
destruct (Req_dec (B2R a) 0) as [HAe | HAp].
- rewrite (HAz HAe).
  (* For [t < 0] in [y], the values [r^t] for [r] in [(0, R1]] have no
     upper bound. *)
  assert (Hunb : forall t, mem t y -> t < 0 -> lane_ok (pxh_S1 x y) (B754_infinity false)).
  { intros t Ht Ht0. apply lane_ok_inf. intros M.
    destruct (Rpow_base_small_neg t M Ht0) as (r0 & Hr0 & Hr0M).
    exists (Rpow (Rmin r0 R1) t).
    assert (Hm : 0 < Rmin r0 R1) by (apply Rmin_glb_lt; lra).
    pose proof (Rmin_l r0 R1). pose proof (Rmin_r r0 R1). split.
    - exists (Rmin r0 R1), t.
      split; [apply Hax; lra|]. split; [lra|]. split; [exact Ht|].
      split; [left; exact Hm | reflexivity].
    - apply Hr0M. lra. }
  destruct Hyc as [(Fc & HC0 & Hyc1 & Hyc2) | (Ec & Hyc2)].
  + destruct (Rle_lt_or_eq_dec _ _ HC0) as [HC0' | HCe].
    * rewrite (pow_zero_neg emin emax m Hg Hp RNDU c (or_introl (conj Fc HC0'))).
      apply (Hunb (B2R c)); [apply Hyc2; lra | exact HC0'].
    * (* [c = 0]: every value is [r^t <= r^0 = 1] for [r > 0], or 0. *)
      destruct (pn_zero c Fc HCe) as (sc & Ec0). rewrite Ec0.
      apply (pn_hi_at (pxh_S1 x y) 1).
      -- exists R1, 0. split; [apply Hax; lra|]. split; [exact HR1|].
         split; [apply Hyc2; lra|]. split; [left; exact HR0|].
         symmetry. apply Rpow_0_r, HR0.
      -- intros s (r & t & Hr & Hr1 & Ht & _ & ->).
         apply Hyc1 in Ht. apply Hxa in Hr.
         destruct (Rle_lt_or_eq_dec 0 r) as [Hr0 | Hr0]; [lra | |].
         ++ rewrite <- (Rpow_0_r r Hr0). apply Rpow_le_exp_le1; lra.
         ++ rewrite <- Hr0, Rpow_0_l. lra.
      -- apply (pow_zero_zero emin emax m Hrg Hg Hp).
  + rewrite Ec, (pow_zero_neg emin emax m Hg Hp RNDU _ (or_intror eq_refl)).
    apply (Hunb (-1)); [apply Hyc2; lra | lra].
- assert (HA : 0 < B2R a) by lra.
  destruct Hyc as [(Fc & HC0 & Hyc1 & Hyc2) | (Ec & Hyc2)].
  + (* [a > 0], [c] finite: the largest value is [a^c]. *)
    apply (pn_hi_at (pxh_S1 x y) (Rpow (B2R a) (B2R c))).
    * exists (B2R a), (B2R c). split; [apply Hax; lra|]. split; [lra|].
      split; [apply Hyc2; lra|]. split; [left; exact HA | reflexivity].
    * intros s (r & t & Hr & Hr1 & Ht & _ & ->). apply Hxa in Hr. apply Hyc1 in Ht.
      apply Rle_trans with (Rpow r (B2R c)).
      -- apply Rpow_le_exp_le1; lra.
      -- apply Rpow_le_base_neg; lra.
    * apply (pow_fin emin emax m Hrg Hg Hp); [exact Fa | exact Fc | left; exact HA].
  + rewrite Ec. assert (HA1 : B2R a <= 1) by lra.
    destruct (Rle_lt_or_eq_dec _ _ HA1) as [HA1' | HAe1].
    * (* [0 < a < 1], [c = -inf]: [a^t] grows without bound as [t]
         falls. *)
      assert (HA01 : 0 < B2R a < 1) by lra.
      rewrite (pow_lt1_ninf emin emax m Hg Hp RNDU a Fa HA01).
      apply lane_ok_inf. intros M.
      destruct (Rpow_exp_small_lt1 (B2R a) M HA01) as (t0 & Ht0).
      exists (Rpow (B2R a) (Rmin t0 0)). split.
      -- exists (B2R a), (Rmin t0 0). split; [apply Hax; lra|]. split; [lra|].
         split; [apply Hyc2, Rmin_r|]. split; [left; exact HA | reflexivity].
      -- apply Ht0, Rmin_l.
    * (* [a = 1], [c = -inf]: the part holds only [r = 1], with the value
         1. *)
      apply (pn_hi_at (pxh_S1 x y) 1).
      -- exists (B2R a), 0. split; [apply Hax; lra|]. split; [lra|].
         split; [apply Hyc2; lra|]. split; [left; exact HA|].
         rewrite HAe1. symmetry. apply Rpow_1_l.
      -- intros s (r & t & Hr & Hr1 & _ & _ & ->). apply Hxa in Hr.
         replace r with 1 by lra. rewrite Rpow_1_l. lra.
      -- apply (pow_one_inf emin emax m Hrg Hg Hp); [exact Fa | exact HAe1].
Qed.

(** The upper lane [pow_ru(b, d)] of the part [r >= 1], where [x] holds
    the reals of [[R2, b]] for some [R2 >= 1] and none above [b]: for
    [1 <= r <= b], [r^t <= r^d <= b^d], as [r^t] increases in [t] and, for
    [d > 0], in [r]. The bound is attained if [b] and [d] are finite.
    Otherwise the values have no upper bound ([b = +inf], as [r^t] for a
    fixed [t > 0] grows without bound with [r]; [b > 1] with [d = +inf]),
    or the bound is 1 ([b = 1] and [d = +inf]: the part holds only
    [r = 1]). *)
Lemma pxh_hi_bd :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall x y b R2 d, 1 <= R2 ->
  (is_finite b = true /\ R2 <= B2R b /\ (forall r, mem r x -> r <= B2R b) /\
   (forall r, R2 <= r <= B2R b -> mem r x)) \/
  (b = B754_infinity false /\ forall r, R2 <= r -> mem r x) ->
  pxh_ddesc y d ->
  lane_ok (pxh_S2 x y) (pow_ru m b d).
Proof.
intros emin emax m Hrg Hg Hp x y b R2 d HR2 Hxb Hyd.
unfold pow_ru.
destruct Hxb as [(Fb & HRB & Hxb1 & Hxb2) | (Eb & Hxb2)].
- destruct Hyd as [(Fd & HD0 & Hyd1 & Hyd2) | (Ed & Hyd2)].
  + (* [b] and [d] finite: the largest value is [b^d]. *)
    apply (pn_hi_at (pxh_S2 x y) (Rpow (B2R b) (B2R d))).
    * exists (B2R b), (B2R d). split; [apply Hxb2; lra|]. split; [lra|].
      split; [apply Hyd2; lra|]. split; [left; lra | reflexivity].
    * intros s (r & t & Hr & Hr1 & Ht & _ & ->). apply Hxb1 in Hr. apply Hyd1 in Ht.
      apply Rle_trans with (Rpow r (B2R d)).
      -- apply Rpow_le_exp_ge1; lra.
      -- apply Rpow_le_base_pos; lra.
    * apply (pow_fin emin emax m Hrg Hg Hp); [exact Fb | exact Fd | left; lra].
  + rewrite Ed. assert (HB1 : 1 <= B2R b) by lra.
    destruct (Rle_lt_or_eq_dec _ _ HB1) as [HB1' | HBe].
    * (* [b > 1], [d = +inf]: [b^t] grows without bound with [t]. *)
      rewrite (pow_gt1_pinf emin emax m Hg Hp RNDU b Fb HB1').
      apply lane_ok_inf. intros M.
      destruct (Rpow_exp_large_gt1 (B2R b) M HB1') as (t0 & Ht0).
      exists (Rpow (B2R b) (Rmax t0 0)). split.
      -- exists (B2R b), (Rmax t0 0). split; [apply Hxb2; lra|]. split; [lra|].
         split; [apply Hyd2, Rmax_r|]. split; [left; lra | reflexivity].
      -- apply Ht0, Rmax_l.
    * (* [b = 1], [d = +inf]: the part holds only [r = 1], with the value
         1. *)
      apply (pn_hi_at (pxh_S2 x y) 1).
      -- exists (B2R b), 0. split; [apply Hxb2; lra|]. split; [lra|].
         split; [apply Hyd2; lra|]. split; [left; lra|].
         rewrite <- HBe. symmetry. apply Rpow_1_l.
      -- intros s (r & t & Hr & Hr1 & _ & _ & ->). apply Hxb1 in Hr.
         replace r with 1 by lra. rewrite Rpow_1_l. lra.
      -- apply (pow_one_inf emin emax m Hrg Hg Hp); [exact Fb | lra].
- (* [b = +inf]: [r^t] for a fixed [t > 0] in [y] grows without bound
     with [r]. *)
  rewrite Eb.
  assert (Hdpos : (is_finite d = true /\ 0 < B2R d) \/ d = B754_infinity false).
  { destruct Hyd as [(Fd & HD0 & _) | (Ed & _)];
      [left; split; [exact Fd | exact HD0] | right; exact Ed]. }
  rewrite (pow_pinf_pos emin emax m Hg Hp RNDU d Hdpos).
  assert (Ht : exists t, mem t y /\ 0 < t).
  { destruct Hyd as [(Fd & HD0 & _ & Hyd2) | (Ed & Hyd2)];
      [exists (B2R d) | exists 1]; (split; [apply Hyd2; lra | lra]). }
  destruct Ht as (t & Ht & Ht0).
  apply lane_ok_inf. intros M.
  destruct (Rpow_base_large_pos t M Ht0) as (r0 & Hr0 & Hr0M).
  exists (Rpow (Rmax r0 R2) t).
  pose proof (Rmax_l r0 R2). pose proof (Rmax_r r0 R2). split.
  + exists (Rmax r0 R2), t. split; [apply Hxb2; lra|]. split; [lra|].
    split; [exact Ht|]. split; [left; lra | reflexivity].
  + apply Hr0M, Rmax_l.
Qed.

(** ** The three cases *)

(** [a <= 1 <= b]: both parts hold [r = 1], and [fmax] of their lanes is
    the lane of the image. *)
Lemma pxh_mid :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall first x y a b c d,
  is_finite a = true -> 0 <= B2R a -> B2R a <= 1 -> (B2R a = 0 -> a = B754_zero false) ->
  (forall r, mem r x -> B2R a <= r) -> (forall r, B2R a <= r <= 1 -> mem r x) ->
  (is_finite b = true /\ 1 <= B2R b /\ (forall r, mem r x -> r <= B2R b) /\
   (forall r, 1 <= r <= B2R b -> mem r x)) \/
  (b = B754_infinity false /\ forall r, 1 <= r -> mem r x) ->
  pxh_cdesc y c -> pxh_ddesc y d ->
  lane_ok (image2_set pow_dom Rpow x y) (fmax first (pow_ru m a c) (pow_ru m b d)).
Proof.
intros emin emax m Hrg Hg Hp first x y a b c d Fa HA0 HA1 HAz Hxa Hax Hxb Hyc Hyd.
assert (H1 : lane_ok (pxh_S1 x y) (pow_ru m a c)).
{ apply (pxh_hi_ac emin emax m Hrg Hg Hp x y a 1 c Fa HA0 HAz);
    [lra | lra | exact HA1 | exact Hxa | exact Hax | exact Hyc]. }
assert (H2 : lane_ok (pxh_S2 x y) (pow_ru m b d))
  by exact (pxh_hi_bd emin emax m Hrg Hg Hp x y b 1 d (Rle_refl 1) Hxb Hyd).
apply (lane_ok_ext (fun s => pxh_S1 x y s \/ pxh_S2 x y s)).
- intros s. symmetry. apply pxh_img_split.
- apply (pl_hi_fmax (pxh_S1 x y) (pxh_S2 x y));
    [exact (pxh_not_nan _ _ H1) | exact (pxh_not_nan _ _ H2) | exact H1 | exact H2].
Qed.

(** The upper lane, with [x] as [pn_x] gives it and [y] as [pxh_y] does.
    If [a > 1], the image is the part [r >= 1]. The corner [(a, c)], for a
    finite [c], is then a point of the box in the domain, so adding its
    value [a^c] to the image changes nothing, and [pow_ru(a, c)] is the
    lane of [{a^c}]: [pl_hi_fmax] gives the lane without comparing the two
    values. For [c = -inf], [pow_ru(a, c)] is a zero and [pow_ru(b, d)] is
    above 0, so [fmax] returns the latter. The case [b < 1] is the same
    with the part [r <= 1] and the corner [(b, d)]. *)
Lemma pxh_main :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall first x y a b c d,
  is_finite a = true -> 0 <= B2R a -> (B2R a = 0 -> a = B754_zero false) ->
  pn_xdesc x (B2R a) b -> pxh_cdesc y c -> pxh_ddesc y d ->
  lane_ok (image2_set pow_dom Rpow x y) (fmax first (pow_ru m a c) (pow_ru m b d)).
Proof.
intros emin emax m Hrg Hg Hp first x y a b c d Fa HA0 HAz Hxb Hyc Hyd.
destruct (pn_xA _ _ _ Hxb) as (Hxa & HAx).
destruct (Rlt_le_dec 1 (B2R a)) as [HA1 | HA1].
- (* [a > 1]: every [r] in [x] is above 1. *)
  assert (Hxb' : (is_finite b = true /\ B2R a <= B2R b /\ (forall r, mem r x -> r <= B2R b) /\
     (forall r, B2R a <= r <= B2R b -> mem r x)) \/
    (b = B754_infinity false /\ forall r, B2R a <= r -> mem r x)).
  { destruct Hxb as [(Fb & HB0 & HAB & Hmx) | (Eb & Hmx)]; [left | right].
    - split; [exact Fb|]. split; [exact HAB|].
      split; intros r Hr; [apply Hmx in Hr; lra | apply Hmx; lra].
    - split; [exact Eb|]. intros r Hr. apply Hmx. exact Hr. }
  assert (H2 : lane_ok (image2_set pow_dom Rpow x y) (pow_ru m b d)).
  { apply (lane_ok_ext (pxh_S2 x y)).
    - intros s. split.
      + intros (r & t & Hr & _ & Ht & Hd & Hs). exists r, t.
        split; [exact Hr|]. split; [exact Ht|]. split; [exact Hd | exact Hs].
      + intros (r & t & Hr & Ht & Hd & Hs). exists r, t.
        split; [exact Hr|]. split; [specialize (Hxa r Hr); lra|].
        split; [exact Ht|]. split; [exact Hd | exact Hs].
    - apply (pxh_hi_bd emin emax m Hrg Hg Hp x y b (B2R a) d); [lra | exact Hxb' | exact Hyd]. }
  destruct Hyc as [(Fc & HC0 & Hyc1 & Hyc2) | (Ec & Hyc2)].
  + (* [c] finite: the corner [(a, c)] is a point of the box. *)
    assert (HS : image2_set pow_dom Rpow x y (Rpow (B2R a) (B2R c))).
    { exists (B2R a), (B2R c). split; [exact HAx|]. split; [apply Hyc2; lra|].
      split; [left; lra | reflexivity]. }
    assert (H1 : lane_ok (fun s => s = Rpow (B2R a) (B2R c)) (pow_ru m a c)).
    { apply (pn_hi_at _ (Rpow (B2R a) (B2R c))); [reflexivity | intros s ->; apply Rle_refl|].
      apply (pow_fin emin emax m Hrg Hg Hp); [exact Fa | exact Fc | left; lra]. }
    apply (lane_ok_ext (fun s => s = Rpow (B2R a) (B2R c) \/ image2_set pow_dom Rpow x y s)).
    * intros s. split; [intros [-> | H]; [exact HS | exact H] | intros H; right; exact H].
    * apply (pl_hi_fmax (fun s => s = Rpow (B2R a) (B2R c)) (image2_set pow_dom Rpow x y));
        [exact (pxh_not_nan _ _ H1) | exact (pxh_not_nan _ _ H2) | exact H1 | exact H2].
  + (* [c = -inf]: [pow_ru(a, c)] is a zero, below [pow_ru(b, d)]. *)
    assert (H0 : mpfr_round f64_format RNDU 0 (with_val (pow_ru m a c))).
    { rewrite Ec. exact (pow_gt1_ninf emin emax m Hg Hp RNDU a Fa HA1). }
    destruct (pxh_round_0 _ H0) as (s & Es). rewrite Es.
    assert (Hpos : pxh_pos (pow_ru m b d)).
    { apply (pxh_bd_pos emin emax m Hrg Hg Hp b d).
      - destruct Hxb' as [(Fb & HAB & _) | (Eb & _)];
          [left; split; [exact Fb | lra] | right; exact Eb].
      - destruct Hyd as [(Fd & HD0 & _) | (Ed & _)];
          [left; split; [exact Fd | exact HD0] | right; exact Ed]. }
    unfold fmax. rewrite (pxh_lt_0_pos s _ Hpos). exact H2.
- destruct Hxb as [(Fb & HB0 & HAB & Hmx) | (Eb & Hmx)].
  + destruct (Rlt_le_dec (B2R b) 1) as [HB1 | HB1].
    * (* [b < 1]: every [r] in [x] is below 1. *)
      assert (H1 : lane_ok (image2_set pow_dom Rpow x y) (pow_ru m a c)).
      { apply (lane_ok_ext (pxh_S1 x y)).
        - intros s. split.
          + intros (r & t & Hr & _ & Ht & Hd & Hs). exists r, t.
            split; [exact Hr|]. split; [exact Ht|]. split; [exact Hd | exact Hs].
          + intros (r & t & Hr & Ht & Hd & Hs). exists r, t.
            split; [exact Hr|]. split; [apply Hmx in Hr; lra|].
            split; [exact Ht|]. split; [exact Hd | exact Hs].
        - apply (pxh_hi_ac emin emax m Hrg Hg Hp x y a (B2R b) c Fa HA0 HAz);
            [exact HB0 | lra | exact HAB | exact Hxa | intros r Hr; apply Hmx; exact Hr
            | exact Hyc]. }
      destruct Hyd as [(Fd & HD0 & Hyd1 & Hyd2) | (Ed & Hyd2)].
      -- (* [d] finite: the corner [(b, d)] is a point of the box. *)
         assert (HS : image2_set pow_dom Rpow x y (Rpow (B2R b) (B2R d))).
         { exists (B2R b), (B2R d). split; [apply Hmx; lra|]. split; [apply Hyd2; lra|].
           split; [left; exact HB0 | reflexivity]. }
         assert (H2 : lane_ok (fun s => s = Rpow (B2R b) (B2R d)) (pow_ru m b d)).
         { apply (pn_hi_at _ (Rpow (B2R b) (B2R d)));
             [reflexivity | intros s ->; apply Rle_refl|].
           apply (pow_fin emin emax m Hrg Hg Hp); [exact Fb | exact Fd | left; exact HB0]. }
         apply (lane_ok_ext
           (fun s => image2_set pow_dom Rpow x y s \/ s = Rpow (B2R b) (B2R d))).
         ++ intros s. split; [intros [H | ->]; [exact H | exact HS] | intros H; left; exact H].
         ++ apply (pl_hi_fmax (image2_set pow_dom Rpow x y) (fun s => s = Rpow (B2R b) (B2R d)));
              [exact (pxh_not_nan _ _ H1) | exact (pxh_not_nan _ _ H2) | exact H1 | exact H2].
      -- (* [d = +inf]: [pow_ru(b, d)] is a zero, below [pow_ru(a, c)]. *)
         assert (H0 : mpfr_round f64_format RNDU 0 (with_val (pow_ru m b d))).
         { rewrite Ed. exact (pow_lt1_pinf emin emax m Hg Hp RNDU b Fb (conj HB0 HB1)). }
         destruct (pxh_round_0 _ H0) as (s & Es). rewrite Es.
         assert (Hpos : pxh_pos (pow_ru m a c)).
         { apply (pxh_ac_pos emin emax m Hrg Hg Hp a c Fa); [lra | exact HAz|].
           destruct Hyc as [(Fc & HC0 & _) | (Ec & _)];
             [left; split; [exact Fc | exact HC0] | right; exact Ec]. }
         unfold fmax. rewrite (pxh_lt_pos_0 s _ Hpos), (pxh_lt_0_pos s _ Hpos). exact H1.
    * (* [a <= 1 <= b]. *)
      apply (pxh_mid emin emax m Hrg Hg Hp first x y a b c d Fa HA0 HA1 HAz Hxa);
        [intros r Hr; apply Hmx; lra | left | exact Hyc | exact Hyd].
      split; [exact Fb|]. split; [exact HB1|].
      split; intros r Hr; [apply Hmx in Hr; lra | apply Hmx; lra].
  + (* [a <= 1] and [b = +inf]. *)
    apply (pxh_mid emin emax m Hrg Hg Hp first x y a b c d Fa HA0 HA1 HAz Hxa);
      [intros r Hr; apply Hmx; lra | right | exact Hyc | exact Hyd].
    split; [exact Eb|]. intros r Hr. apply Hmx. lra.
Qed.

(** ** The lemma *)

Lemma pw_mix_hi :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall first_max x y, pw_xok x -> valid y -> Interval.is_empty y = false ->
  Model.le (Interval.sup_raw y) Model.zero = false ->
  Model.gt (Interval.inf_raw y) Model.zero = false ->
  Model.eq (Interval.sup_raw x) Model.zero = false ->
  lane_ok (image2_set pow_dom Rpow x y)
    (fmax first_max (pow_ru m (Interval.inf_raw x) (Interval.inf_raw y))
       (pow_ru m (Interval.sup_raw x) (Interval.sup_raw y))).
Proof.
intros emin emax m Hrg Hg Hp first_max x y Hx Hyv Hye Hd Hc Hb0.
destruct (pn_x x Hx Hb0) as (Fa & HA0 & HAz & Hxb).
destruct (pxh_y y Hyv Hye Hd Hc) as (Hyc & Hyd).
exact (pxh_main emin emax m Hrg Hg Hp first_max x y _ _ _ _ Fa HA0 HAz Hxb Hyc Hyd).
Qed.
