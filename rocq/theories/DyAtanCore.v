(** * atan and the parts of asin and acos in the dyadic kernel

    [series] of [DyadicAtan] in [Model.v] evaluates by Horner's scheme in
    [z = v^2] the scaled remainders of the series of [atan] at [v]
    ([atan_tail_bounds] and [atan_horner]), from the enclosure
    [[0, 1/(2 terms + 1)]] of the remainder after [terms n z] terms.
    [atan_series] is [series] at its argument [u] if the upper bound of
    [u] is at most [2^-8], and otherwise twice [series] at [u] halved
    once ([atan_halve] of [AtanSeries.v]). [atan_encl] encloses [atan]
    of every point of a nonnegative enclosure [w] with the series at
    [w], [(1 - w)/(1 + w)], [(w - 1)/(w + 1)] or [1/w], and π of
    [DyConstPi.v] ([AtanIdent.v]).
    [asin_parts] encloses [asin t] or [acos t] for [0 <= t <= 1] as
    [atan] of a quotient with [√((1 - t)(1 + t))]. Each lemma is partial
    correctness: if the function returns, its enclosure holds the real
    number. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary LogReal AtanhSeries DyRound DyConv DyOps
  DyDriver DyGrow DyConst DyExpCore DyExp DyExpRules DyLogRules DyLogCore DyLogHyp AtanSeries
  AtanIdent DyConstPi.

Open Scope Z_scope.

(** ** Helpers *)

Lemma ac_t2_R : B2R DyadicAtan.t2 = (309 / 128)%R.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicAtan.t2) with (SpecFloat.S754_finite false 5435985487724544 (-51))
  by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 5435985487724544) with (IZR (309 * Z.pow_pos 2 44)).
rewrite mult_IZR. change (IZR (Z.pow_pos 2 44)) with (bpow radix2 44).
rewrite Rmult_assoc, <- bpow_plus.
change (44 + -51) with (-7). change (bpow radix2 (-7)) with (/ 128)%R. field.
Qed.

Lemma ac_split_R : B2R DyadicAtan.asin_split = (3 / 4)%R.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicAtan.asin_split) with (SpecFloat.S754_finite false 6755399441055744 (-53))
  by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 6755399441055744) with (IZR (3 * Z.pow_pos 2 51)).
rewrite mult_IZR. change (IZR (Z.pow_pos 2 51)) with (bpow radix2 51).
rewrite Rmult_assoc, <- bpow_plus.
change (51 + -53) with (-2). change (bpow radix2 (-2)) with (/ 4)%R. field.
Qed.

Lemma ac_split_finite : is_finite DyadicAtan.asin_split = true.
Proof. vm_compute. reflexivity. Qed.

(** [le x y = false] means [y < x] for finite [x] and [y]. *)
Lemma ac_not_le :
  forall x y, is_finite x = true -> is_finite y = true -> Model.le x y = false ->
  (B2R y < B2R x)%R.
Proof.
intros x y Fx Fy H. unfold Model.le in H. rewrite Bleb_correct in H by assumption.
destruct (Rle_bool_spec (B2R x) (B2R y)); [discriminate H | assumption].
Qed.

(** [dy_gt n x y = true] means [y < x]. *)
Lemma ac_gt :
  forall n x y,
  level_ok n -> dy_ok n x -> dy_ok n y -> DyadicExp.dy_gt n x y = true ->
  (Dyadic.dy_R y < Dyadic.dy_R x)%R.
Proof.
intros n x y Hn Hx Hy H. unfold DyadicExp.dy_gt in H. rewrite (cmp_correct n _ _ Hn Hx Hy) in H.
destruct (Rcompare_spec (Dyadic.dy_R x) (Dyadic.dy_R y)); [discriminate H | discriminate H | lra].
Qed.

(** [terms n z] is 1, [14 n + 2], or the smaller of [14 n + 2] and a
    quotient of positive numbers, so it lies in [[0, 14 * 64 + 2]]. *)
Lemma ac_terms : forall n z, level_ok n -> 0 <= DyadicAtan.terms n z <= 898.
Proof.
intros n z Hn. unfold level_ok in Hn. unfold DyadicAtan.terms. cbv zeta.
destruct (Dyadic.is_zero n (Dyadic.en_hi z)); [lia|].
destruct (Z.leb_spec (- (64 * Z.of_nat n)) (Dyadic.dy_exp (Dyadic.en_hi z))); [lia|].
set (e := - (64 * Z.of_nat n) - Dyadic.dy_exp (Dyadic.en_hi z)).
assert (He : 0 < e) by (unfold e; lia).
assert (Hq : 0 <= (64 * Z.of_nat n + 3 + e) / e) by (apply Z.div_pos; lia).
revert Hq. generalize ((64 * Z.of_nat n + 3 + e) / e). intros q Hq. lia.
Qed.

(** ** The loop of [series]

    If [t] holds [T] with [T v^(2i+1) = (-1)^i (atan v - Σ_{l < i}
    (-1)^l v^(2l+1) / (2l+1))], a step holds [1 / (2i - 1) - v^2 T],
    which satisfies the same for [i - 1] ([atan_horner]). Each step adds
    [Ez + 2^15] at most to the bound of the exponents of [t] (a division
    of 1, a product by [z] and a difference). *)
Lemma ac_series_loop_correct :
  forall n one_e z vv Ez,
  level_ok n -> encl_ok n one_e -> encl_le (2 ^ 13) one_e -> encl_has one_e 1 ->
  encl_ok n z -> encl_le Ez z -> 0 <= Ez <= 2 ^ 40 -> encl_has z (vv * vv) ->
  forall i t Et t' T,
  encl_ok n t -> encl_le Et t -> 0 <= Et -> Et + Z.of_nat i * (Ez + 2 ^ 15) <= 2 ^ 59 ->
  encl_has t T -> (T * vv ^ (2 * i + 1) = (-1) ^ i * (atan vv - atan_sum i vv))%R ->
  DyadicAtan.series_loop n one_e z i t = Some t' ->
  encl_ok n t' /\ encl_le (Et + Z.of_nat i * (Ez + 2 ^ 15)) t' /\
  exists T', encl_has t' T' /\ (T' * vv = atan vv)%R.
Proof.
intros n one_e z vv Ez Hn Ho HoE Ho1 Hz HzE HEz Hzv i.
induction i as [|k IH]; intros t Et t' T Ht HtE HEt0 HEt HT HTr H.
- cbn [DyadicAtan.series_loop] in H. injection H as <-.
  split; [exact Ht|]. split; [rewrite Z.mul_0_l, Z.add_0_r; exact HtE|].
  exists T. split; [exact HT|]. cbn [atan_sum pow Nat.mul Nat.add] in HTr. lra.
- cbn [DyadicAtan.series_loop] in H.
  destruct (Dyadic.encl_div_u64 n one_e (2 * Z.of_nat k + 1)) as [q|] eqn:Eq; [|discriminate H].
  destruct (Dyadic.encl_mul n z t) as [p|] eqn:Ep; [|discriminate H].
  destruct (Dyadic.encl_sub n q p) as [t1|] eqn:Et1; [|discriminate H].
  rewrite Nat2Z.inj_succ in HEt.
  assert (HEt' : Et <= 2 ^ 59) by nia.
  assert (Hk : 0 < 2 * Z.of_nat k + 1 < 2 ^ 64) by nia.
  assert (HE13 : 0 <= 2 ^ 13 <= 2 ^ 60) by lia.
  destruct (div_u64_step n one_e (2 * Z.of_nat k + 1) q (2 ^ 13) Hn Ho HoE HE13 Hk Eq)
    as (Hq & HqE & Hqv).
  assert (HE1 : 0 <= Ez <= 2 ^ 60) by lia.
  assert (HE2 : 0 <= Et <= 2 ^ 60) by lia.
  destruct (mul_step n z t p Ez Et Hn Hz Ht HzE HtE HE1 HE2 Ep) as (Hp & HpE & Hpv).
  assert (HE3 : 0 <= 2 ^ 13 + 2 ^ 13 <= 2 ^ 60) by lia.
  assert (HE4 : 0 <= Ez + Et + 2 ^ 13 <= 2 ^ 60) by lia.
  destruct (sub_step n q p t1 _ _ Hn Hq Hp HqE HpE HE3 HE4 Et1) as (Ht1 & Ht1E & Ht1v).
  set (T1 := (1 / IZR (2 * Z.of_nat k + 1) - vv * vv * T)%R).
  assert (HT1 : encl_has t1 T1).
  { apply Ht1v; [apply Hqv, Ho1 | apply Hpv; assumption]. }
  assert (HT1r : (T1 * vv ^ (2 * k + 1) = (-1) ^ k * (atan vv - atan_sum k vv))%R).
  { unfold T1. apply atan_horner. exact HTr. }
  assert (Ht1E' : encl_le (Et + (Ez + 2 ^ 15)) t1).
  { apply (encl_le_mono (Z.max (2 ^ 13 + 2 ^ 13) (Ez + Et + 2 ^ 13) + 2 ^ 13)); [lia | exact Ht1E]. }
  assert (HEt1 : 0 <= Et + (Ez + 2 ^ 15)) by lia.
  assert (HEt2 : Et + (Ez + 2 ^ 15) + Z.of_nat k * (Ez + 2 ^ 15) <= 2 ^ 59) by nia.
  destruct (IH t1 (Et + (Ez + 2 ^ 15)) t' T1 Ht1 Ht1E' HEt1 HEt2 HT1 HT1r H) as (A & B & C).
  split; [exact A|]. split; [| exact C].
  apply (encl_le_mono (Et + (Ez + 2 ^ 15) + Z.of_nat k * (Ez + 2 ^ 15))); [| exact B].
  rewrite Nat2Z.inj_succ. nia.
Qed.

(** ** [series]

    [z = v^2] has exponents of at most [E + E + 2^13] ([mul_step]); the
    start [t0 = [0, 1/(2 terms + 1)]] of at most [2^14]; each of the
    [terms n z <= 898] steps of the loop adds [E + E + 2^13 + 2^15] at
    most, and the product by [v] adds [E + 2^13]. For [E <= 2^34] the
    sum is below [2^49]. *)
Lemma series_correct :
  forall n v c E vv,
  level_ok n -> encl_ok n v -> encl_le E v -> 0 <= E <= 2 ^ 34 -> encl_has v vv ->
  DyadicAtan.series n v = Some c ->
  encl_ok n c /\ encl_le (2 ^ 49) c /\ encl_has c (atan vv).
Proof.
intros n v c E vv Hn Hv HvE HE Hvh H. unfold DyadicAtan.series in H.
destruct (Dyadic.encl_point n DyadicExp.one) as [one_e|] eqn:E1; [|discriminate H].
destruct (Dyadic.encl_mul n v v) as [z|] eqn:Ez; [|discriminate H].
destruct (Dyadic.from_f64 n DyadicExp.one) as [one_d|] eqn:Eo; [|discriminate H].
set (K := DyadicAtan.terms n z) in H.
assert (Hk : 0 <= K <= 898) by exact (ac_terms n z Hn).
clearbody K.
destruct (Dyadic.div_u64 n one_d (2 * K + 1) true) as [hi|] eqn:Ehi; [|discriminate H].
set (t0 := {| Dyadic.en_lo := Dyadic.dy_zero n; Dyadic.en_hi := hi |}) in H.
destruct (DyadicAtan.series_loop n one_e z (Z.to_nat K) t0) as [t|] eqn:Et; [|discriminate H].
destruct (point_has n _ _ Hn E1) as (Ho & HoE & Ho1). rewrite dexp_one_R in Ho1.
assert (HE13 : 0 <= 2 ^ 13 <= 2 ^ 60) by lia.
assert (HE1 : 0 <= E <= 2 ^ 60) by lia.
destruct (mul_step n v v z _ _ Hn Hv Hv HvE HvE HE1 HE1 Ez) as (Hz & HzE & Hzv).
(* The upper bound [hi] of the start is [1 / (2 terms + 1)] rounded up:
   the upper bound of [encl_div_u64] of the point 1. *)
destruct (from_f64_step n _ _ Hn Eo) as (Od & Ld & Vd & _).
assert (Sd : exp_small one_d) by (unfold exp_small; lia).
assert (Hk64 : 0 < 2 * K + 1 < 2 ^ 64) by lia.
destruct (div_u64_correct n one_d _ false Hn Od Sd Hk64) as (lo & Elo & _ & _).
assert (Eoe : one_e = {| Dyadic.en_lo := one_d; Dyadic.en_hi := one_d |}).
{ unfold Dyadic.encl_point in E1. rewrite Eo in E1. injection E1 as <-. reflexivity. }
assert (Eq0 : Dyadic.encl_div_u64 n one_e (2 * K + 1) =
              Some {| Dyadic.en_lo := lo; Dyadic.en_hi := hi |}).
{ rewrite Eoe. unfold Dyadic.encl_div_u64. cbn [Dyadic.en_lo Dyadic.en_hi].
  rewrite Elo, Ehi. reflexivity. }
destruct (div_u64_step n one_e _ _ (2 ^ 13) Hn Ho HoE HE13 Hk64 Eq0) as (Oq & Lq & Vq).
pose proof (Vq _ Ho1) as Vq1. unfold encl_has in Vq1; cbn [Dyadic.en_lo Dyadic.en_hi] in Vq1.
destruct Oq as (_ & Ohi & _). cbn [Dyadic.en_lo Dyadic.en_hi] in Ohi.
destruct Lq as (_ & Lhi). cbn [Dyadic.en_lo Dyadic.en_hi] in Lhi.
destruct (dy_zero_ok n) as (Oz & Vz & _).
assert (Hkp : (0 < IZR (2 * K + 1))%R) by (apply IZR_lt; lia).
assert (Hkq : (0 < 1 / IZR (2 * K + 1))%R) by (apply Rdiv_lt_0_compat; [lra | exact Hkp]).
assert (Ht0 : encl_ok n t0).
{ unfold encl_ok, t0; cbn [Dyadic.en_lo Dyadic.en_hi].
  split; [exact Oz|]. split; [exact Ohi|]. rewrite Vz. lra. }
assert (Ht0E : encl_le (2 ^ 14) t0).
{ unfold encl_le, t0; cbn [Dyadic.en_lo Dyadic.en_hi Dyadic.dy_zero Dyadic.dy_exp]. lia. }
(* The remainder after [terms n z] terms, scaled, lies in [[0, 1/(2 terms + 1)]]. *)
destruct (atan_tail_bounds (Z.to_nat K) vv) as (T & HT01 & HT).
assert (HINR : INR (2 * Z.to_nat K + 1) = IZR (2 * K + 1)).
{ rewrite INR_IZR_INZ. f_equal. lia. }
rewrite HINR in HT01.
assert (HT0 : encl_has t0 T).
{ unfold encl_has, t0; cbn [Dyadic.en_lo Dyadic.en_hi]. rewrite Vz. lra. }
assert (HEz : 0 <= E + E + 2 ^ 13 <= 2 ^ 40) by lia.
assert (HE0 : 0 <= (2 ^ 14 : Z)) by lia.
assert (HEb : 2 ^ 14 + Z.of_nat (Z.to_nat K) * (E + E + 2 ^ 13 + 2 ^ 15) <= 2 ^ 59).
{ rewrite Z2Nat.id by lia. nia. }
destruct (ac_series_loop_correct n one_e z vv _ Hn Ho HoE Ho1 Hz HzE HEz
  (Hzv _ _ Hvh Hvh) _ t0 _ t T Ht0 Ht0E HE0 HEb HT0 HT Et) as (Ht & HtE & T1 & HT1 & HT1r).
rewrite Z2Nat.id in HtE by lia.
(* [v T_0 = atan v]. *)
assert (HE7 : 0 <= 2 ^ 14 + K * (E + E + 2 ^ 13 + 2 ^ 15) <= 2 ^ 60) by nia.
destruct (mul_step n v t c _ _ Hn Hv Ht HvE HtE HE1 HE7 H) as (Hc & HcE & Hcv).
split; [exact Hc|]. split.
- apply (encl_le_mono (E + (2 ^ 14 + K * (E + E + 2 ^ 13 + 2 ^ 15)) + 2 ^ 13));
    [nia | exact HcE].
- replace (atan vv) with (vv * T1)%R by (rewrite <- HT1r; ring).
  apply Hcv; [exact Hvh | exact HT1].
Qed.

(** ** [atan_series]

    The proof does not use the comparison with [2^-8]: each branch
    encloses [atan] of every point of [u]. At most [2^-8], [atan_series]
    is [series] at [u]. Above, the exponents grow by the steps of [DyGrow.v]: [u^2] by
    [E + 2^13], [1 + u^2] to [2E + 2^14], its square root by [2^13], the
    divisor [d] to [2E + 2^15] and the halved [v] to [3E + 2^16], below
    the [2^34] of [series_correct]; the doubling adds 1. *)
Lemma atan_series_correct :
  forall n u c E uv,
  level_ok n -> encl_ok n u -> encl_le E u -> 0 <= E <= 2 ^ 32 -> encl_has u uv ->
  DyadicAtan.atan_series n u = Some c ->
  encl_ok n c /\ encl_le (2 ^ 50) c /\ encl_has c (atan uv).
Proof.
intros n u c E uv Hn Hu HuE HE Huv H. unfold DyadicAtan.atan_series in H.
destruct (Dyadic.from_f64 n DyadicAtan.no_halve) as [h|] eqn:Eh; [|discriminate H].
destruct (negb (DyadicExp.dy_gt n (Dyadic.en_hi u) h)) eqn:B.
{ (* [u <= 2^-8]: the series at [u] *)
  assert (HE' : 0 <= E <= 2 ^ 34) by lia.
  destruct (series_correct n u c E uv Hn Hu HuE HE' Huv H) as (Hc & HcE & Hcv).
  split; [exact Hc|]. split; [apply (encl_le_mono (2 ^ 49)); [lia | exact HcE] | exact Hcv]. }
destruct (Dyadic.encl_point n DyadicExp.one) as [one_e|] eqn:E1; [|discriminate H].
destruct (Dyadic.encl_mul n u u) as [u2|] eqn:Eu2; [|discriminate H].
destruct (Dyadic.encl_add n one_e u2) as [c2|] eqn:Ec2; [|discriminate H].
destruct (Dyadic.encl_sqrt n c2) as [sq|] eqn:Esq; [|discriminate H].
destruct (Dyadic.encl_add n one_e sq) as [d|] eqn:Ed; [|discriminate H].
destruct (Dyadic.encl_div n u d) as [v|] eqn:Ev; [|discriminate H].
destruct (DyadicAtan.series n v) as [s|] eqn:Es; [|discriminate H].
destruct (point_has n _ _ Hn E1) as (Ho & HoE & Ho1). rewrite dexp_one_R in Ho1.
assert (HE13 : 0 <= 2 ^ 13 <= 2 ^ 60) by lia.
assert (HE1 : 0 <= E <= 2 ^ 60) by lia.
(* [1 + u^2], its square root, [d = 1 + √(1 + u^2)] and [v = u / d]. *)
destruct (mul_step n u u u2 E E Hn Hu Hu HuE HuE HE1 HE1 Eu2) as (Hu2 & Hu2E & Hu2v).
assert (HE2 : 0 <= E + E + 2 ^ 13 <= 2 ^ 60) by lia.
destruct (add_step n one_e u2 c2 _ _ Hn Ho Hu2 HoE Hu2E HE13 HE2 Ec2) as (Hc2 & Hc2E & Hc2v).
pose proof (Hc2v _ _ Ho1 (Hu2v _ _ Huv Huv)) as Hc2h.
assert (Hc2E' : encl_le (2 * E + 2 ^ 14) c2).
{ apply (encl_le_mono (Z.max (2 ^ 13) (E + E + 2 ^ 13) + 2 ^ 13)); [lia | exact Hc2E]. }
assert (HE3 : 0 <= 2 * E + 2 ^ 14 <= 2 ^ 60) by lia.
assert (Huu : (0 <= uv * uv)%R) by nra.
assert (Hc2p : (0 <= hi_R c2)%R) by (unfold hi_R; unfold encl_has in Hc2h; lra).
destruct (sqrt_step n c2 sq _ Hn Hc2 Hc2E' HE3 Hc2p Esq) as (Hsq & HsqE & Hsqv).
assert (Hsqh : encl_has sq (sqrt (1 + uv * uv))) by (apply Hsqv; [lra | exact Hc2h]).
assert (HE4 : 0 <= 2 * E + 2 ^ 14 + 2 ^ 13 <= 2 ^ 60) by lia.
destruct (add_step n one_e sq d _ _ Hn Ho Hsq HoE HsqE HE13 HE4 Ed) as (Hd & HdE & Hdv).
pose proof (Hdv _ _ Ho1 Hsqh) as Hdh.
assert (HdE' : encl_le (2 * E + 2 ^ 15) d).
{ apply (encl_le_mono (Z.max (2 ^ 13) (2 * E + 2 ^ 14 + 2 ^ 13) + 2 ^ 13)); [lia | exact HdE]. }
assert (HE5 : 0 <= 2 * E + 2 ^ 15 <= 2 ^ 60) by lia.
destruct (div_step n u d v _ _ Hn Hu Hd HuE HdE' HE1 HE5 Ev) as (Hv & HvE & Hvv).
set (vv := (uv / (1 + sqrt (1 + uv * uv)))%R).
assert (Hvh : encl_has v vv) by (apply Hvv; [exact Huv | exact Hdh]).
assert (HvE' : encl_le (3 * E + 2 ^ 16) v).
{ apply (encl_le_mono (E + (2 * E + 2 ^ 15) + 2 ^ 13)); [lia | exact HvE]. }
assert (HE6 : 0 <= 3 * E + 2 ^ 16 <= 2 ^ 34) by lia.
destruct (series_correct n v s _ vv Hn Hv HvE' HE6 Hvh Es) as (Hs & HsE & Hsv).
(* [s] holds [atan v], and doubling it gives [atan u] ([atan_halve]). *)
assert (HE7 : 0 <= 2 ^ 49 <= 2 ^ 60) by lia.
assert (Hk1 : - 2 ^ 20 <= 1 <= 2 ^ 20) by lia.
destruct (shl_step n s 1 c _ Hn Hs HsE HE7 Hk1 H) as (Hc & HcE & Hcv).
split; [exact Hc|]. split.
- apply (encl_le_mono (2 ^ 49 + Z.abs 1)); [lia | exact HcE].
- assert (Ha : atan uv = (atan vv * bpow radix2 1)%R).
  { rewrite (atan_halve uv). fold vv. change (bpow radix2 1) with 2%R. ring. }
  rewrite Ha. apply Hcv, Hsv.
Qed.

(** ** [atan_encl]

    The lower bound of [w] is not negative, so neither is [wv]. Each
    branch encloses [atan] of the reduced argument with [atan_series],
    whose argument has exponents of at most [2 (2^30 + 2^13) + 2^13];
    [π/4] and [π/2] are π shifted ([shl_step]). *)
Lemma atan_encl_correct :
  forall n w c E wv,
  level_ok n -> encl_ok n w -> encl_le E w -> 0 <= E <= 2 ^ 30 -> encl_has w wv ->
  DyadicAtan.atan_encl n w = Some c ->
  encl_ok n c /\ encl_le (2 ^ 51) c /\ encl_has c (atan wv).
Proof.
intros n w c E wv Hn Hw HwE HE Hwv H. unfold DyadicAtan.atan_encl in H.
destruct (Dyadic.dy_neg (Dyadic.en_lo w)) eqn:Ng; [discriminate H|].
destruct (Dyadic.encl_point n DyadicExp.one) as [one_e|] eqn:E1; [|discriminate H].
destruct (Dyadic.from_f64 n DyadicAtan.t1) as [t1_d|] eqn:Et1; [|discriminate H].
pose proof Hw as (Olo & Ohi & _).
assert (Hw0 : (0 <= wv)%R).
{ pose proof (dy_R_nonneg _ (proj1 Olo) Ng). unfold encl_has in Hwv. lra. }
destruct (point_has n _ _ Hn E1) as (Ho & HoE & Ho1). rewrite dexp_one_R in Ho1.
assert (HE1 : 0 <= E <= 2 ^ 60) by lia.
assert (HE13 : 0 <= 2 ^ 13 <= 2 ^ 60) by lia.
assert (HE15 : 0 <= 2 ^ 15 <= 2 ^ 60) by lia.
assert (HE50 : 0 <= 2 ^ 50 <= 2 ^ 60) by lia.
destruct (negb (DyadicExp.dy_gt n (Dyadic.en_hi w) t1_d)) eqn:B1.
{ (* [w <= t1]: the series at [w] *)
  assert (HE' : 0 <= E <= 2 ^ 32) by lia.
  destruct (atan_series_correct n w c E wv Hn Hw HwE HE' Hwv H) as (Hc & HcE & Hcv).
  split; [exact Hc|]. split; [apply (encl_le_mono (2 ^ 50)); [lia | exact HcE] | exact Hcv]. }
destruct (DyadicExp.dy_lt n (Dyadic.en_hi w) (Dyadic.en_hi one_e)) eqn:B2.
{ (* [w < 1]: [π/4 - atan((1 - w)/(1 + w))] *)
  destruct (Dyadic.encl_sub n one_e w) as [a|] eqn:Ea; [|discriminate H].
  destruct (Dyadic.encl_add n one_e w) as [b|] eqn:Eb; [|discriminate H].
  destruct (Dyadic.encl_div n a b) as [u|] eqn:Eu; [|discriminate H].
  destruct (DyadicConsts.pi n) as [p|] eqn:Ep; [|discriminate H].
  destruct (Dyadic.encl_shl n p (-2)) as [p4|] eqn:Ep4; [|discriminate H].
  destruct (DyadicAtan.atan_series n u) as [s|] eqn:Es; [|discriminate H].
  destruct (sub_step n one_e w a _ _ Hn Ho Hw HoE HwE HE13 HE1 Ea) as (Ha & HaE & Hav).
  destruct (add_step n one_e w b _ _ Hn Ho Hw HoE HwE HE13 HE1 Eb) as (Hb & HbE & Hbv).
  assert (HE2 : 0 <= Z.max (2 ^ 13) E + 2 ^ 13 <= 2 ^ 60) by lia.
  destruct (div_step n a b u _ _ Hn Ha Hb HaE HbE HE2 HE2 Eu) as (Hu & HuE & Huv).
  assert (HuE' : encl_le (2 ^ 32) u).
  { apply (encl_le_mono (Z.max (2 ^ 13) E + 2 ^ 13 + (Z.max (2 ^ 13) E + 2 ^ 13) + 2 ^ 13));
      [lia | exact HuE]. }
  assert (HE3 : 0 <= 2 ^ 32 <= 2 ^ 32) by lia.
  destruct (atan_series_correct n u s _ _ Hn Hu HuE' HE3
    (Huv _ _ (Hav _ _ Ho1 Hwv) (Hbv _ _ Ho1 Hwv)) Es) as (Hs & HsE & Hsv).
  destruct (pi_correct n p Hn Ep) as (Hp & HpE & Hpv).
  assert (Hk : - 2 ^ 20 <= -2 <= 2 ^ 20) by lia.
  destruct (shl_step n p (-2) p4 _ Hn Hp HpE HE15 Hk Ep4) as (Hp4 & Hp4E & Hp4v).
  assert (HE4 : 0 <= 2 ^ 15 + Z.abs (-2) <= 2 ^ 60) by lia.
  destruct (sub_step n p4 s c _ _ Hn Hp4 Hs Hp4E HsE HE4 HE50 H) as (Hc & HcE & Hcv).
  split; [exact Hc|]. split.
  - apply (encl_le_mono (Z.max (2 ^ 15 + Z.abs (-2)) (2 ^ 50) + 2 ^ 13)); [lia | exact HcE].
  - rewrite (atan_quarter_minus wv) by lra.
    replace (PI / 4)%R with (PI * bpow radix2 (-2))%R
      by (change (bpow radix2 (-2)) with (/ 4)%R; field).
    apply Hcv; [apply Hp4v, Hpv | exact Hsv]. }
destruct (Dyadic.from_f64 n DyadicAtan.t2) as [t2_d|] eqn:Et2; [|discriminate H].
destruct (negb (DyadicExp.dy_gt n (Dyadic.en_lo w) t2_d)) eqn:B3.
{ (* [1 <= w <= t2]: [π/4 + atan((w - 1)/(w + 1))] *)
  destruct (Dyadic.encl_sub n w one_e) as [a|] eqn:Ea; [|discriminate H].
  destruct (Dyadic.encl_add n w one_e) as [b|] eqn:Eb; [|discriminate H].
  destruct (Dyadic.encl_div n a b) as [u|] eqn:Eu; [|discriminate H].
  destruct (DyadicConsts.pi n) as [p|] eqn:Ep; [|discriminate H].
  destruct (Dyadic.encl_shl n p (-2)) as [p4|] eqn:Ep4; [|discriminate H].
  destruct (DyadicAtan.atan_series n u) as [s|] eqn:Es; [|discriminate H].
  destruct (sub_step n w one_e a _ _ Hn Hw Ho HwE HoE HE1 HE13 Ea) as (Ha & HaE & Hav).
  destruct (add_step n w one_e b _ _ Hn Hw Ho HwE HoE HE1 HE13 Eb) as (Hb & HbE & Hbv).
  assert (HE2 : 0 <= Z.max E (2 ^ 13) + 2 ^ 13 <= 2 ^ 60) by lia.
  destruct (div_step n a b u _ _ Hn Ha Hb HaE HbE HE2 HE2 Eu) as (Hu & HuE & Huv).
  assert (HuE' : encl_le (2 ^ 32) u).
  { apply (encl_le_mono (Z.max E (2 ^ 13) + 2 ^ 13 + (Z.max E (2 ^ 13) + 2 ^ 13) + 2 ^ 13));
      [lia | exact HuE]. }
  assert (HE3 : 0 <= 2 ^ 32 <= 2 ^ 32) by lia.
  destruct (atan_series_correct n u s _ _ Hn Hu HuE' HE3
    (Huv _ _ (Hav _ _ Hwv Ho1) (Hbv _ _ Hwv Ho1)) Es) as (Hs & HsE & Hsv).
  destruct (pi_correct n p Hn Ep) as (Hp & HpE & Hpv).
  assert (Hk : - 2 ^ 20 <= -2 <= 2 ^ 20) by lia.
  destruct (shl_step n p (-2) p4 _ Hn Hp HpE HE15 Hk Ep4) as (Hp4 & Hp4E & Hp4v).
  assert (HE4 : 0 <= 2 ^ 15 + Z.abs (-2) <= 2 ^ 60) by lia.
  destruct (add_step n p4 s c _ _ Hn Hp4 Hs Hp4E HsE HE4 HE50 H) as (Hc & HcE & Hcv).
  split; [exact Hc|]. split.
  - apply (encl_le_mono (Z.max (2 ^ 15 + Z.abs (-2)) (2 ^ 50) + 2 ^ 13)); [lia | exact HcE].
  - rewrite (atan_quarter_plus wv) by lra.
    replace (PI / 4)%R with (PI * bpow radix2 (-2))%R
      by (change (bpow radix2 (-2)) with (/ 4)%R; field).
    apply Hcv; [apply Hp4v, Hpv | exact Hsv]. }
(* [w > t2 > 0]: [π/2 - atan(1/w)] *)
destruct (DyadicConsts.pi n) as [p|] eqn:Ep; [|discriminate H].
destruct (Dyadic.encl_shl n p (-1)) as [p2|] eqn:Ep2; [|discriminate H].
destruct (Dyadic.encl_div n one_e w) as [u|] eqn:Eu; [|discriminate H].
destruct (DyadicAtan.atan_series n u) as [s|] eqn:Es; [|discriminate H].
assert (B3' : DyadicExp.dy_gt n (Dyadic.en_lo w) t2_d = true).
{ destruct (DyadicExp.dy_gt n (Dyadic.en_lo w) t2_d); [reflexivity | discriminate B3]. }
destruct (from_f64_step n _ _ Hn Et2) as (Ot2 & _ & Vt2 & _). rewrite ac_t2_R in Vt2.
pose proof (ac_gt n _ _ Hn Olo Ot2 B3') as Hlo. rewrite Vt2 in Hlo.
assert (Hwp : (0 < wv)%R) by (unfold encl_has in Hwv; lra).
destruct (div_step n one_e w u _ _ Hn Ho Hw HoE HwE HE13 HE1 Eu) as (Hu & HuE & Huv).
assert (HuE' : encl_le (2 ^ 32) u).
{ apply (encl_le_mono (2 ^ 13 + E + 2 ^ 13)); [lia | exact HuE]. }
assert (HE3 : 0 <= 2 ^ 32 <= 2 ^ 32) by lia.
destruct (atan_series_correct n u s _ _ Hn Hu HuE' HE3 (Huv _ _ Ho1 Hwv) Es) as (Hs & HsE & Hsv).
destruct (pi_correct n p Hn Ep) as (Hp & HpE & Hpv).
assert (Hk : - 2 ^ 20 <= -1 <= 2 ^ 20) by lia.
destruct (shl_step n p (-1) p2 _ Hn Hp HpE HE15 Hk Ep2) as (Hp2 & Hp2E & Hp2v).
assert (HE4 : 0 <= 2 ^ 15 + Z.abs (-1) <= 2 ^ 60) by lia.
destruct (sub_step n p2 s c _ _ Hn Hp2 Hs Hp2E HsE HE4 HE50 H) as (Hc & HcE & Hcv).
split; [exact Hc|]. split.
- apply (encl_le_mono (Z.max (2 ^ 15 + Z.abs (-1)) (2 ^ 50) + 2 ^ 13)); [lia | exact HcE].
- rewrite (atan_half_inv wv Hwp).
  replace (PI / 2)%R with (PI * bpow radix2 (-1))%R
    by (change (bpow radix2 (-1)) with (/ 2)%R; field).
  apply Hcv; [apply Hp2v, Hpv | exact Hsv].
Qed.

(** ** [asin_parts]

    [1 - t] and [1 + t] are points' differences and sums, their product
    holds [(1 - t)(1 + t) >= 0], and the quotients with its square root
    have exponents of at most [2^16], below the [2^30] of
    [atan_encl_correct]. *)
Lemma asin_parts_correct :
  forall n t s below,
  level_ok n -> is_finite t = true -> (0 <= B2R t <= 1)%R ->
  DyadicAtan.asin_parts n t = Some (s, below) ->
  encl_ok n s /\ encl_le (2 ^ 51) s /\
  encl_has s (if below then asin (B2R t) else acos (B2R t)).
Proof.
intros n t s below Hn Ft Ht01 H. unfold DyadicAtan.asin_parts in H.
destruct (Dyadic.encl_point n t) as [x|] eqn:Ex; [|discriminate H].
destruct (Dyadic.encl_point n DyadicExp.one) as [one_e|] eqn:E1; [|discriminate H].
destruct (Dyadic.encl_sub n one_e x) as [a|] eqn:Ea; [|discriminate H].
destruct (Dyadic.encl_add n one_e x) as [b|] eqn:Eb; [|discriminate H].
destruct (Dyadic.encl_mul n a b) as [p|] eqn:Ep; [|discriminate H].
destruct (Dyadic.encl_sqrt n p) as [r|] eqn:Er; [|discriminate H].
destruct (point_has n _ _ Hn Ex) as (Hx & HxE & Hxv).
destruct (point_has n _ _ Hn E1) as (Ho & HoE & Ho1). rewrite dexp_one_R in Ho1.
assert (HE13 : 0 <= 2 ^ 13 <= 2 ^ 60) by lia.
destruct (sub_step n one_e x a _ _ Hn Ho Hx HoE HxE HE13 HE13 Ea) as (Ha & HaE & Hav).
destruct (add_step n one_e x b _ _ Hn Ho Hx HoE HxE HE13 HE13 Eb) as (Hb & HbE & Hbv).
assert (HaE' : encl_le (2 ^ 14) a) by (apply (encl_le_mono (Z.max (2 ^ 13) (2 ^ 13) + 2 ^ 13));
  [lia | exact HaE]).
assert (HbE' : encl_le (2 ^ 14) b) by (apply (encl_le_mono (Z.max (2 ^ 13) (2 ^ 13) + 2 ^ 13));
  [lia | exact HbE]).
assert (HE14 : 0 <= 2 ^ 14 <= 2 ^ 60) by lia.
destruct (mul_step n a b p _ _ Hn Ha Hb HaE' HbE' HE14 HE14 Ep) as (Hp & HpE & Hpv).
pose proof (Hpv _ _ (Hav _ _ Ho1 Hxv) (Hbv _ _ Ho1 Hxv)) as Hph.
assert (Hpp : (0 <= (1 - B2R t) * (1 + B2R t))%R) by nra.
assert (Hp0 : (0 <= hi_R p)%R) by (unfold hi_R; unfold encl_has in Hph; lra).
assert (HE15 : 0 <= 2 ^ 14 + 2 ^ 14 + 2 ^ 13 <= 2 ^ 60) by lia.
destruct (sqrt_step n p r _ Hn Hp HpE HE15 Hp0 Er) as (Hr & HrE & Hrv).
assert (Hrh : encl_has r (sqrt ((1 - B2R t) * (1 + B2R t)))) by (apply Hrv; [exact Hpp | exact Hph]).
assert (HE16 : 0 <= 2 ^ 14 + 2 ^ 14 + 2 ^ 13 + 2 ^ 13 <= 2 ^ 60) by lia.
destruct (Model.le t DyadicAtan.asin_split) eqn:L.
- (* [t <= 3/4]: [asin t = atan(t / √((1 - t)(1 + t)))] *)
  destruct (Dyadic.encl_div n x r) as [q|] eqn:Eq; [|discriminate H].
  destruct (DyadicAtan.atan_encl n q) as [s'|] eqn:Es; [|discriminate H].
  injection H as <- <-.
  destruct (div_step n x r q _ _ Hn Hx Hr HxE HrE HE13 HE16 Eq) as (Hq & HqE & Hqv).
  assert (HE17 : 0 <= 2 ^ 13 + (2 ^ 14 + 2 ^ 14 + 2 ^ 13 + 2 ^ 13) + 2 ^ 13 <= 2 ^ 30) by lia.
  destruct (atan_encl_correct n q s' _ _ Hn Hq HqE HE17 (Hqv _ _ Hxv Hrh) Es) as (Hs & HsE & Hsv).
  split; [exact Hs|]. split; [exact HsE|].
  pose proof (le_R _ _ Ft ac_split_finite L) as Hl. rewrite ac_split_R in Hl.
  rewrite asin_as_atan by lra. exact Hsv.
- (* [t > 3/4]: [acos t = atan(√((1 - t)(1 + t)) / t)] *)
  destruct (Dyadic.encl_div n r x) as [q|] eqn:Eq; [|discriminate H].
  destruct (DyadicAtan.atan_encl n q) as [s'|] eqn:Es; [|discriminate H].
  injection H as <- <-.
  destruct (div_step n r x q _ _ Hn Hr Hx HrE HxE HE16 HE13 Eq) as (Hq & HqE & Hqv).
  assert (HE17 : 0 <= 2 ^ 14 + 2 ^ 14 + 2 ^ 13 + 2 ^ 13 + 2 ^ 13 + 2 ^ 13 <= 2 ^ 30) by lia.
  destruct (atan_encl_correct n q s' _ _ Hn Hq HqE HE17 (Hqv _ _ Hrh Hxv) Es) as (Hs & HsE & Hsv).
  split; [exact Hs|]. split; [exact HsE|].
  pose proof (ac_not_le _ _ Ft ac_split_finite L) as Hl. rewrite ac_split_R in Hl.
  rewrite acos_as_atan by lra. exact Hsv.
Qed.
