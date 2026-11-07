(** * The series of sin and cos in the dyadic kernel

    [series n r odd] of [DyadicTrig] in [Model.v] evaluates by Horner's
    scheme in [z = r^2] the scaled remainders of the series of [sin] (if
    [odd]) or [cos] at [r] ([trig_horner] of [TrigSeries.v]), from the
    enclosure [[0, 1]] of the remainder after [terms n z] terms
    ([trig_tail_bounds]), and multiplies by [r] for [sin]. [sin_k n quad
    neg r] picks [sin] or [cos] of [r] and its sign by [quad mod 4], so
    that it encloses [sin (k π/2 ± ρ)] for every [k] with [k mod 4 = quad
    mod 4] ([sin_quad]). Each lemma is partial correctness: if the
    function returns, its enclosure holds the real number. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary LogReal AtanhSeries DyRound DyConv DyOps
  DyDriver DyGrow DyConst DyExpCore DyExp DyExpRules DyLogRules DyLogCore DyLogHyp TrigSeries.

Open Scope Z_scope.

(** ** Helpers *)

(** [terms n z] is [6 n + 5], or the smaller of [6 n + 5] and a quotient
    of positive numbers, so it lies in [[0, 6 * 64 + 5]]. *)
Lemma tc_terms : forall n z, level_ok n -> 0 <= DyadicTrig.terms n z <= 389.
Proof.
intros n z Hn. unfold level_ok in Hn. unfold DyadicTrig.terms. cbv zeta.
destruct (Z.leb_spec (- (64 * Z.of_nat n)) (Dyadic.dy_exp (Dyadic.en_hi z))); [lia|].
set (e := - (64 * Z.of_nat n) - Dyadic.dy_exp (Dyadic.en_hi z)).
assert (He : 0 < e) by (unfold e; lia).
assert (Hq : 0 <= (64 * Z.of_nat n + 3 + e) / e) by (apply Z.div_pos; lia).
revert Hq. generalize ((64 * Z.of_nat n + 3 + e) / e). intros q Hq. lia.
Qed.

(** ** The loop of [series]

    If [t] holds [T] with [T] times the term [i] of the series equal to
    the remainder after [i] terms, a step holds [1 - ρ^2 T / ((2 i - 1 +
    o) (2 i + o))], which satisfies the same for [i - 1] ([trig_horner]).
    For [i <= 389] the divisor lies in [(0, 2^64)]. Each step adds [Ez +
    2^15] at most to the bound of the exponents of [t] (a product by [z],
    a division by an integer and a difference). *)
Lemma tc_series_loop_correct :
  forall n one_e z odd rho Ez,
  level_ok n -> encl_ok n one_e -> encl_le (2 ^ 13) one_e -> encl_has one_e 1 ->
  encl_ok n z -> encl_le Ez z -> 0 <= Ez <= 2 ^ 40 -> encl_has z (rho * rho) ->
  forall i t Et t' T,
  Z.of_nat i <= 389 ->
  encl_ok n t -> encl_le Et t -> 0 <= Et -> Et + Z.of_nat i * (Ez + 2 ^ 15) <= 2 ^ 59 ->
  encl_has t T -> (T * trig_term odd rho i = trig_fn odd rho - trig_sum odd i rho)%R ->
  DyadicTrig.series_loop n one_e z (Z.b2z odd) i t = Some t' ->
  encl_ok n t' /\ encl_le (Et + Z.of_nat i * (Ez + 2 ^ 15)) t' /\
  exists T', encl_has t' T' /\ (T' * trig_term odd rho 0 = trig_fn odd rho)%R.
Proof.
intros n one_e z odd rho Ez Hn Ho HoE Ho1 Hz HzE HEz Hzv i.
induction i as [|k IH]; intros t Et t' T Hi Ht HtE HEt0 HEt HT HTr H.
- cbn [DyadicTrig.series_loop] in H. injection H as <-.
  split; [exact Ht|]. split; [rewrite Z.mul_0_l, Z.add_0_r; exact HtE|].
  exists T. split; [exact HT|]. cbn [trig_sum] in HTr. lra.
- cbn [DyadicTrig.series_loop] in H.
  set (d := (2 * Z.of_nat k + 1 + Z.b2z odd) * (2 * Z.of_nat k + 2 + Z.b2z odd)) in H.
  destruct (Dyadic.encl_mul n z t) as [p|] eqn:Ep; [|discriminate H].
  destruct (Dyadic.encl_div_u64 n p d) as [q|] eqn:Eq; [|discriminate H].
  destruct (Dyadic.encl_sub n one_e q) as [t1|] eqn:Et1; [|discriminate H].
  rewrite Nat2Z.inj_succ in Hi, HEt.
  assert (HEt' : Et <= 2 ^ 59) by nia.
  (* The divisor is at most [(2 * 388 + 2) (2 * 388 + 3)]. *)
  assert (Ho01 : 0 <= Z.b2z odd <= 1) by (destruct odd; cbn; lia).
  assert (Hd : 0 < d < 2 ^ 64).
  { unfold d. split; [apply Z.mul_pos_pos; lia|].
    apply (Z.le_lt_trans _ (780 * 780)); [apply Z.mul_le_mono_nonneg; lia | lia]. }
  assert (HE1 : 0 <= Ez <= 2 ^ 60) by lia.
  assert (HE2 : 0 <= Et <= 2 ^ 60) by lia.
  destruct (mul_step n z t p Ez Et Hn Hz Ht HzE HtE HE1 HE2 Ep) as (Hp & HpE & Hpv).
  assert (HE3 : 0 <= Ez + Et + 2 ^ 13 <= 2 ^ 60) by lia.
  destruct (div_u64_step n p d q _ Hn Hp HpE HE3 Hd Eq) as (Hq & HqE & Hqv).
  assert (HE4 : 0 <= (2 ^ 13 : Z) <= 2 ^ 60) by lia.
  assert (HE5 : 0 <= Ez + Et + 2 ^ 13 + 2 ^ 13 <= 2 ^ 60) by lia.
  destruct (sub_step n one_e q t1 _ _ Hn Ho Hq HoE HqE HE4 HE5 Et1) as (Ht1 & Ht1E & Ht1v).
  set (T1 := (1 - rho * rho * T / IZR d)%R).
  assert (HT1 : encl_has t1 T1).
  { apply Ht1v; [exact Ho1 | apply Hqv, Hpv; assumption]. }
  assert (HT1r : (T1 * trig_term odd rho k = trig_fn odd rho - trig_sum odd k rho)%R).
  { unfold T1, d. apply trig_horner. exact HTr. }
  assert (Ht1E' : encl_le (Et + (Ez + 2 ^ 15)) t1).
  { apply (encl_le_mono (Z.max (2 ^ 13) (Ez + Et + 2 ^ 13 + 2 ^ 13) + 2 ^ 13));
      [lia | exact Ht1E]. }
  assert (Hk : Z.of_nat k <= 389) by lia.
  assert (HEt1 : 0 <= Et + (Ez + 2 ^ 15)) by lia.
  assert (HEt2 : Et + (Ez + 2 ^ 15) + Z.of_nat k * (Ez + 2 ^ 15) <= 2 ^ 59) by nia.
  destruct (IH t1 (Et + (Ez + 2 ^ 15)) t' T1 Hk Ht1 Ht1E' HEt1 HEt2 HT1 HT1r H)
    as (A & B & C).
  split; [exact A|]. split; [| exact C].
  apply (encl_le_mono (Et + (Ez + 2 ^ 15) + Z.of_nat k * (Ez + 2 ^ 15))); [| exact B].
  rewrite Nat2Z.inj_succ. nia.
Qed.

(** ** [series]

    [z = ρ^2] has exponents of at most [E + E + 2^13] ([mul_step]); the
    start [t0 = [0, 1]] of at most [2^13]; each of the [terms n z <= 389]
    steps of the loop adds [E + E + 2^13 + 2^15] at most, and the product
    by [r] for [sin] adds [E + 2^13]. For [E <= 2^34] the sum is below
    [2^50]. *)
Lemma series_correct :
  forall n r odd c E rho,
  level_ok n -> encl_ok n r -> encl_le E r -> 0 <= E <= 2 ^ 34 -> encl_has r rho ->
  (-1 <= rho <= 1)%R ->
  DyadicTrig.series n r odd = Some c ->
  encl_ok n c /\ encl_le (2 ^ 50) c /\ encl_has c (trig_fn odd rho).
Proof.
intros n r odd c E rho Hn Hr HrE HE Hrh Hrho H. unfold DyadicTrig.series in H.
destruct (Dyadic.encl_point n DyadicExp.one) as [one_e|] eqn:E1; [|discriminate H].
destruct (Dyadic.encl_mul n r r) as [z|] eqn:Ez; [|discriminate H].
set (K := DyadicTrig.terms n z) in H.
assert (Hk : 0 <= K <= 389) by exact (tc_terms n z Hn).
clearbody K.
set (t0 := {| Dyadic.en_lo := Dyadic.dy_zero n; Dyadic.en_hi := Dyadic.en_hi one_e |}) in H.
destruct (DyadicTrig.series_loop n one_e z (Z.b2z odd) (Z.to_nat K) t0) as [t|] eqn:Et;
  [|discriminate H].
destruct (point_has n _ _ Hn E1) as (Ho & HoE & Ho1). rewrite dexp_one_R in Ho1.
assert (HE1 : 0 <= E <= 2 ^ 60) by lia.
destruct (mul_step n r r z _ _ Hn Hr Hr HrE HrE HE1 HE1 Ez) as (Hz & HzE & Hzv).
(* The start [t0] is [[0, 1]]: its upper bound is that of the point 1. *)
destruct (dy_zero_ok n) as (Oz & Vz & _).
assert (Hhi1 : Dyadic.dy_R (Dyadic.en_hi one_e) = 1%R).
{ destruct (point_step n _ _ Hn E1) as (_ & _ & _ & Hh & _).
  unfold hi_R in Hh. rewrite Hh. exact dexp_one_R. }
assert (Ht0 : encl_ok n t0).
{ destruct Ho as (_ & Ohi & _).
  unfold encl_ok, t0; cbn [Dyadic.en_lo Dyadic.en_hi].
  split; [exact Oz|]. split; [exact Ohi|]. rewrite Vz, Hhi1. lra. }
assert (Ht0E : encl_le (2 ^ 13) t0).
{ destruct HoE as (_ & Lhi).
  unfold encl_le, t0; cbn [Dyadic.en_lo Dyadic.en_hi Dyadic.dy_zero Dyadic.dy_exp].
  split; [lia | exact Lhi]. }
(* The remainder after [terms n z] terms is [T] times the next term, for
   some [T] in [[0, 1]]. *)
assert (Hrho1 : (Rabs rho <= 1)%R) by (apply Rabs_le; lra).
destruct (trig_tail_bounds odd (Z.to_nat K) rho Hrho1) as (T & HT01 & HT).
assert (HT0 : encl_has t0 T).
{ unfold encl_has, t0; cbn [Dyadic.en_lo Dyadic.en_hi]. rewrite Vz, Hhi1. lra. }
assert (HEz : 0 <= E + E + 2 ^ 13 <= 2 ^ 40) by lia.
assert (HE0 : 0 <= (2 ^ 13 : Z)) by lia.
assert (HKi : Z.of_nat (Z.to_nat K) <= 389) by lia.
assert (HEb : 2 ^ 13 + Z.of_nat (Z.to_nat K) * (E + E + 2 ^ 13 + 2 ^ 15) <= 2 ^ 59).
{ rewrite Z2Nat.id by lia. nia. }
destruct (tc_series_loop_correct n one_e z odd rho _ Hn Ho HoE Ho1 Hz HzE HEz
  (Hzv _ _ Hrh Hrh) _ t0 _ t T HKi Ht0 Ht0E HE0 HEb HT0 HT Et) as (Ht & HtE & T1 & HT1 & HT1r).
rewrite Z2Nat.id in HtE by lia.
rewrite trig_term_0 in HT1r.
destruct odd; cbv iota in HT1r.
- (* [sin ρ = ρ T_0]. *)
  assert (HE7 : 0 <= 2 ^ 13 + K * (E + E + 2 ^ 13 + 2 ^ 15) <= 2 ^ 60) by nia.
  destruct (mul_step n r t c _ _ Hn Hr Ht HrE HtE HE1 HE7 H) as (Hc & HcE & Hcv).
  split; [exact Hc|]. split.
  + apply (encl_le_mono (E + (2 ^ 13 + K * (E + E + 2 ^ 13 + 2 ^ 15)) + 2 ^ 13));
      [nia | exact HcE].
  + replace (trig_fn true rho) with (rho * T1)%R by (rewrite <- HT1r; ring).
    apply Hcv; [exact Hrh | exact HT1].
- (* [cos ρ = T_0]. *)
  cbv iota in H. injection H as <-.
  split; [exact Ht|]. split.
  + apply (encl_le_mono (2 ^ 13 + K * (E + E + 2 ^ 13 + 2 ^ 15))); [nia | exact HtE].
  + replace (trig_fn false rho) with T1 by (rewrite <- HT1r; ring). exact HT1.
Qed.

Lemma sin_k_correct :
  forall n quad neg r c E k rho,
  level_ok n -> encl_ok n r -> encl_le E r -> 0 <= E <= 2 ^ 34 -> encl_has r rho ->
  (-1 <= rho <= 1)%R -> k mod 4 = quad mod 4 ->
  DyadicTrig.sin_k n quad neg r = Some c ->
  encl_ok n c /\ encl_le (2 ^ 50) c /\
  encl_has c (sin (IZR k * (PI / 2) + (if neg then - rho else rho))%R).
Proof.
intros n quad neg r c E k rho Hn Hr HrE HE Hrh Hrho Hk H.
rewrite (sin_quad k quad neg rho Hk). unfold DyadicTrig.sin_k in H.
destruct (quad mod 2 =? 0).
- destruct (DyadicTrig.series n r true) as [v|] eqn:Ev; [|discriminate H].
  injection H as <-.
  destruct (series_correct n r true v E rho Hn Hr HrE HE Hrh Hrho Ev) as (Hv & HvE & Hvh).
  destruct (xorb neg (quad mod 4 =? 2)).
  + destruct (neg_step n v _ Hn Hv HvE) as (A & B & C).
    split; [exact A|]. split; [exact B|]. apply C. exact Hvh.
  + split; [exact Hv|]. split; [exact HvE|]. exact Hvh.
- destruct (DyadicTrig.series n r false) as [v|] eqn:Ev; [|discriminate H].
  injection H as <-.
  destruct (series_correct n r false v E rho Hn Hr HrE HE Hrh Hrho Ev) as (Hv & HvE & Hvh).
  destruct (quad mod 4 =? 3).
  + destruct (neg_step n v _ Hn Hv HvE) as (A & B & C).
    split; [exact A|]. split; [exact B|]. apply C. exact Hvh.
  + split; [exact Hv|]. split; [exact HvE|]. exact Hvh.
Qed.
