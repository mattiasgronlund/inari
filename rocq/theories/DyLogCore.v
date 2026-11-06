(** * atanh and ln in the dyadic kernel

    [atanh_series] of [DyadicLog] in [Model.v] evaluates by Horner's
    scheme in [z = u^2] the scaled remainders of the series of [atanh]
    ([atanh_tail] and [atanh_horner] of [DyLogRules.v]), from the
    enclosure [[0, 2]] of the remainder after [terms n] terms. [reduce]
    writes a positive dyadic number [d] exactly as [2^e m], with [m] in
    [[1/√2, √2)] up to [2^-64], and encloses [|ln m|] as
    [2 atanh(|m - 1| / (m + 1))]; [ln_dy] adds [e ln 2] with the
    enclosure of ln 2 of [DyConst.v]. [ln_encl] encloses [ln] of every
    point of a positive enclosure [[x, y]] by [[ln x, ln x + (y - x) / x]]
    ([ln_le_sub]). Each lemma is partial correctness: if the function
    returns, its enclosure holds the real number. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary LogReal AtanhSeries DyRound DyConv DyOps
  DyDriver DyGrow DyConst DyExpCore DyExp DyLogRules.

Open Scope Z_scope.

(** ** Helpers *)

Lemma lc_half_R : B2R DyadicLog.half = (1 / 2)%R.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicLog.half) with (SpecFloat.S754_finite false 4503599627370496 (-53))
  by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
change (52 + -53) with (-1). change (bpow radix2 (-1)) with (/ 2)%R. field.
Qed.

(** [dy_lt n x 0 = false] means [0 <= x], and [dy_gt n x y = false]
    means [x <= y]. *)
Lemma lc_not_lt :
  forall n x y,
  level_ok n -> dy_ok n x -> dy_ok n y -> DyadicExp.dy_lt n x y = false ->
  (Dyadic.dy_R y <= Dyadic.dy_R x)%R.
Proof.
intros n x y Hn Hx Hy H. unfold DyadicExp.dy_lt in H. rewrite (cmp_correct n _ _ Hn Hx Hy) in H.
destruct (Rcompare_spec (Dyadic.dy_R x) (Dyadic.dy_R y)); [discriminate H | lra | lra].
Qed.

Lemma lc_lt :
  forall n x y,
  level_ok n -> dy_ok n x -> dy_ok n y -> DyadicExp.dy_lt n x y = true ->
  (Dyadic.dy_R x < Dyadic.dy_R y)%R.
Proof.
intros n x y Hn Hx Hy H. unfold DyadicExp.dy_lt in H. rewrite (cmp_correct n _ _ Hn Hx Hy) in H.
destruct (Rcompare_spec (Dyadic.dy_R x) (Dyadic.dy_R y)); [lra | discriminate H | discriminate H].
Qed.

Lemma lc_not_gt :
  forall n x y,
  level_ok n -> dy_ok n x -> dy_ok n y -> DyadicExp.dy_gt n x y = false ->
  (Dyadic.dy_R x <= Dyadic.dy_R y)%R.
Proof.
intros n x y Hn Hx Hy H. unfold DyadicExp.dy_gt in H. rewrite (cmp_correct n _ _ Hn Hx Hy) in H.
destruct (Rcompare_spec (Dyadic.dy_R x) (Dyadic.dy_R y)); [lra | lra | discriminate H].
Qed.

Lemma lc_terms : forall n, level_ok n -> 0 <= DyadicLog.terms n <= 821.
Proof.
intros n Hn. unfold level_ok in Hn. unfold DyadicLog.terms.
split; [apply Z.div_pos; lia |].
assert ((64 * Z.of_nat n + 10) / 5 < 822) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(** ** The loop of [atanh_series]

    If [t] holds [T] with [T u^(2i+1) = atanh u - Σ_{l < i} u^(2l+1) /
    (2l+1)], a step holds [1 / (2i - 1) + u^2 T], which satisfies the
    same for [i - 1] ([atanh_horner]). Each step adds [Ez + 2^15] at
    most to the bound of the exponents of [t] (a division of 1, a
    product by [z] and a sum). *)
Lemma lc_series_loop_correct :
  forall n one_e z uv Ez,
  level_ok n -> encl_ok n one_e -> encl_le (2 ^ 13) one_e -> encl_has one_e 1 ->
  encl_ok n z -> encl_le Ez z -> 0 <= Ez <= 2 ^ 40 -> encl_has z (uv * uv) ->
  forall i t Et t' T,
  encl_ok n t -> encl_le Et t -> 0 <= Et -> Et + Z.of_nat i * (Ez + 2 ^ 15) <= 2 ^ 59 ->
  encl_has t T -> (T * uv ^ (2 * i + 1) = Ratanh uv - atanh_sum i uv)%R ->
  DyadicLog.series_loop n one_e z i t = Some t' ->
  encl_ok n t' /\ encl_le (Et + Z.of_nat i * (Ez + 2 ^ 15)) t' /\
  exists T', encl_has t' T' /\ (T' * uv = Ratanh uv)%R.
Proof.
intros n one_e z uv Ez Hn Ho HoE Ho1 Hz HzE HEz Hzv i.
induction i as [|k IH]; intros t Et t' T Ht HtE HEt0 HEt HT HTr H.
- cbn [DyadicLog.series_loop] in H. injection H as <-.
  split; [exact Ht|]. split; [rewrite Z.mul_0_l, Z.add_0_r; exact HtE|].
  exists T. split; [exact HT|]. cbn [atanh_sum pow Nat.mul Nat.add] in HTr. lra.
- cbn [DyadicLog.series_loop] in H.
  destruct (Dyadic.encl_div_u64 n one_e (2 * Z.of_nat k + 1)) as [q|] eqn:Eq; [|discriminate H].
  destruct (Dyadic.encl_mul n z t) as [p|] eqn:Ep; [|discriminate H].
  destruct (Dyadic.encl_add n q p) as [t1|] eqn:Et1; [|discriminate H].
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
  destruct (add_step n q p t1 _ _ Hn Hq Hp HqE HpE HE3 HE4 Et1) as (Ht1 & Ht1E & Ht1v).
  set (T1 := (1 / IZR (2 * Z.of_nat k + 1) + uv * uv * T)%R).
  assert (HT1 : encl_has t1 T1).
  { apply Ht1v; [apply Hqv, Ho1 | apply Hpv; assumption]. }
  assert (HT1r : (T1 * uv ^ (2 * k + 1) = Ratanh uv - atanh_sum k uv)%R).
  { unfold T1. apply atanh_horner. exact HTr. }
  assert (Ht1E' : encl_le (Et + (Ez + 2 ^ 15)) t1).
  { apply (encl_le_mono (Z.max (2 ^ 13 + 2 ^ 13) (Ez + Et + 2 ^ 13) + 2 ^ 13)); [lia | exact Ht1E]. }
  assert (HEt1 : 0 <= Et + (Ez + 2 ^ 15)) by lia.
  assert (HEt2 : Et + (Ez + 2 ^ 15) + Z.of_nat k * (Ez + 2 ^ 15) <= 2 ^ 59) by nia.
  destruct (IH t1 (Et + (Ez + 2 ^ 15)) t' T1 Ht1 Ht1E' HEt1 HEt2 HT1 HT1r H) as (A & B & C).
  split; [exact A|]. split; [| exact C].
  apply (encl_le_mono (Et + (Ez + 2 ^ 15) + Z.of_nat k * (Ez + 2 ^ 15))); [| exact B].
  rewrite Nat2Z.inj_succ. nia.
Qed.

(** ** [atanh_series] *)

Lemma atanh_series_correct :
  forall n u c E uv,
  level_ok n -> encl_ok n u -> encl_le E u -> 0 <= E <= 2 ^ 30 -> encl_has u uv ->
  DyadicLog.atanh_series n u = Some c ->
  encl_ok n c /\ encl_le (2 ^ 43) c /\ encl_has c (Ratanh uv).
Proof.
intros n u c E uv Hn Hu HuE HE Huv H. unfold DyadicLog.atanh_series in H.
destruct (Dyadic.from_f64 n DyadicLog.half) as [half_d|] eqn:Eh; [|discriminate H].
destruct (DyadicExp.dy_lt n (Dyadic.en_lo u) (Dyadic.dy_zero n)) eqn:L1;
  cbn [orb] in H; [discriminate H|].
destruct (DyadicExp.dy_gt n (Dyadic.en_hi u) half_d) eqn:L2; cbn [orb] in H; [discriminate H|].
destruct (Dyadic.encl_mul n u u) as [z|] eqn:Ez; [|discriminate H].
destruct (Dyadic.encl_point n DyadicExp.one) as [one_e|] eqn:E1; [|discriminate H].
destruct (Dyadic.from_f64 n DyadicExp.two) as [two_d|] eqn:E2; [|discriminate H].
set (t0 := {| Dyadic.en_lo := Dyadic.dy_zero n; Dyadic.en_hi := two_d |}) in H.
destruct (DyadicLog.series_loop n one_e z (Z.to_nat (DyadicLog.terms n)) t0) as [t1|] eqn:E3;
  [|discriminate H].
destruct (from_f64_step n _ _ Hn Eh) as (Oh & _ & Vh & _). rewrite lc_half_R in Vh.
destruct (dy_zero_ok n) as (Oz & Vz & _).
pose proof Hu as (Olo & Ohi & _).
(* The check: [0 <= lo] and [hi <= 1/2], so that [0 <= uv <= 1/2]. *)
pose proof (lc_not_lt n _ _ Hn Olo Oz L1) as Hlo. rewrite Vz in Hlo.
pose proof (lc_not_gt n _ _ Hn Ohi Oh L2) as Hhi. rewrite Vh in Hhi.
unfold encl_has in Huv.
assert (Huv01 : (0 <= uv <= 1 / 2)%R) by lra.
assert (HE1 : 0 <= E <= 2 ^ 60) by lia.
destruct (mul_step n u u z E E Hn Hu Hu HuE HuE HE1 HE1 Ez) as (Hz & HzE & Hzv).
destruct (point_has n _ _ Hn E1) as (Ho & HoE & Ho1). rewrite dexp_one_R in Ho1.
destruct (from_f64_step n _ _ Hn E2) as (Ht & HtE & HtR & _). rewrite dexp_two_R in HtR.
(* The scheme starts from [[0, 2]], which holds the scaled remainder. *)
assert (Ht0 : encl_ok n t0).
{ unfold encl_ok, t0; cbn [Dyadic.en_lo Dyadic.en_hi].
  split; [exact Oz|]. split; [exact Ht|]. rewrite Vz, HtR. lra. }
assert (Ht0E : encl_le (2 ^ 13) t0).
{ unfold encl_le, t0; cbn [Dyadic.en_lo Dyadic.en_hi Dyadic.dy_zero Dyadic.dy_exp]. lia. }
pose proof (lc_terms n Hn) as Hk.
destruct (atanh_tail (Z.to_nat (DyadicLog.terms n)) uv Huv01) as (T & HT02 & HT).
assert (HT0 : encl_has t0 T).
{ unfold encl_has, t0; cbn [Dyadic.en_lo Dyadic.en_hi]. rewrite Vz, HtR. lra. }
assert (HEz : 0 <= E + E + 2 ^ 13 <= 2 ^ 40) by lia.
assert (HE0 : 0 <= (2 ^ 13 : Z)) by lia.
assert (HEb : 2 ^ 13 + Z.of_nat (Z.to_nat (DyadicLog.terms n)) * (E + E + 2 ^ 13 + 2 ^ 15)
              <= 2 ^ 59).
{ rewrite Z2Nat.id by lia. nia. }
destruct (lc_series_loop_correct n one_e z uv _ Hn Ho HoE Ho1 Hz HzE HEz
  (Hzv _ _ Huv Huv) _ t0 _ t1 T Ht0 Ht0E HE0 HEb HT0 HT E3) as (Ht1 & Ht1E & T1 & HT1 & HT1r).
rewrite Z2Nat.id in Ht1E by lia.
assert (HE2 : 0 <= 2 ^ 13 + DyadicLog.terms n * (E + E + 2 ^ 13 + 2 ^ 15) <= 2 ^ 60) by nia.
destruct (mul_step n u t1 c E _ Hn Hu Ht1 HuE Ht1E HE1 HE2 H) as (Hc & HcE & Hcv).
split; [exact Hc|]. split.
- apply (encl_le_mono (E + (2 ^ 13 + DyadicLog.terms n * (E + E + 2 ^ 13 + 2 ^ 15)) + 2 ^ 13));
    [nia | exact HcE].
- rewrite <- HT1r, Rmult_comm. apply Hcv; [exact Huv | exact HT1].
Qed.

Lemma reduce_correct :
  forall n d e a less,
  level_ok n -> dy_ok n d -> exp_small d ->
  DyadicLog.reduce n d = Some (e, a, less) ->
  (0 < Dyadic.dy_R d)%R /\ - 2048 <= e <= 2048 /\ encl_ok n a /\ encl_le (2 ^ 44) a /\
  encl_has a
    (if less then (IZR e * ln 2 - ln (Dyadic.dy_R d))%R
     else (ln (Dyadic.dy_R d) - IZR e * ln 2)%R).
Proof.
intros n d e a less Hn Hd Hds H. unfold DyadicLog.reduce in H.
destruct (Dyadic.dy_neg d) eqn:Ng; [discriminate H|].
destruct (Dyadic.is_zero n d) eqn:Zd; cbn [orb] in H; [discriminate H|].
cbv zeta in H.
remember (if DyadicLog.sqrt_half <=? Limbs.limb (Dyadic.dy_m d) (n - 1)
          then Dyadic.dy_exp d + 64 * Z.of_nat n else Dyadic.dy_exp d + 64 * Z.of_nat n - 1)
  as e0 eqn:He0d.
assert (He0 : e0 = Dyadic.dy_exp d + 64 * Z.of_nat n \/
              e0 = Dyadic.dy_exp d + 64 * Z.of_nat n - 1).
{ rewrite He0d. destruct (_ <=? _); [left | right]; reflexivity. }
clear He0d.
destruct (2048 <? Z.abs e0) eqn:B; [discriminate H|]. apply Z.ltb_ge in B.
pose proof Hn as Hn'. unfold level_ok in Hn'. unfold exp_small in Hds.
(* [d] is positive: its sign bit is clear and it is not 0. *)
assert (Pd : (0 < Dyadic.dy_R d)%R).
{ destruct (dy_cases n d Hn Hd) as [(Z0 & _) | (_ & Hv & _)];
    [rewrite Zd in Z0; discriminate Z0|].
  pose proof (dprec_bounds n Hn) as Hp.
  assert (P : 0 < 2 ^ (dprec n - 1)) by (apply Z.pow_pos_nonneg; lia).
  unfold Dyadic.dy_R. rewrite Ng.
  apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0]. }
(* [m = d 2^-e] exactly, with the mantissa of [d] and the exponent [-64 n] or
   [-64 n + 1]. *)
destruct (shl_correct n d (- e0) Hn Hd ltac:(lia)) as (m & Em & Om & Vm).
assert (Xm : Dyadic.dy_exp m = Dyadic.dy_exp d - e0).
{ unfold Dyadic.shl in Em. rewrite Zd in Em. rewrite checked_i64 in Em by lia.
  injection Em as <-. cbn [Dyadic.dy_exp]. lia. }
rewrite Em in H.
assert (Pm : (0 < Dyadic.dy_R m)%R) by (rewrite Vm; apply Rmult_lt_0_compat; [exact Pd | apply bpow_gt_0]).
(* [ln d = ln m + e ln 2]. *)
assert (Lm : ln (Dyadic.dy_R m) = (ln (Dyadic.dy_R d) - IZR e0 * ln 2)%R).
{ rewrite Vm, ln_mult by (try exact Pd; apply bpow_gt_0).
  rewrite bpow_exp, ln_exp, opp_IZR. change (IZR (radix_val radix2)) with 2%R. ring. }
destruct (hh_correct n m (2 ^ 13) Om ltac:(lia)) as (Ome & Lme & Hme).
destruct (Dyadic.encl_point n DyadicExp.one) as [one_e|] eqn:E1; [|discriminate H].
destruct (point_step n _ _ Hn E1) as (Oo & Lo & Vlo & _ & _). rewrite dexp_one_R in Vlo.
destruct (point_has n _ _ Hn E1) as (_ & _ & Ho1). rewrite dexp_one_R in Ho1.
pose proof Oo as (Oolo & _ & _).
assert (HE13 : 0 <= 2 ^ 13 <= 2 ^ 60) by lia.
assert (HE14 : 0 <= Z.max (2 ^ 13) (2 ^ 13) + 2 ^ 13 <= 2 ^ 60) by lia.
destruct (Dyadic.encl_add n {| Dyadic.en_lo := m; Dyadic.en_hi := m |} one_e) as [den|] eqn:Ed.
2:{ destruct (DyadicExp.dy_lt n m (Dyadic.en_lo one_e));
    destruct (Dyadic.encl_sub _ _ _); discriminate H. }
destruct (add_step n _ _ den _ _ Hn Ome Oo Lme Lo HE13 HE13 Ed) as (Od & Ld & Hdv).
specialize (Hdv _ _ Hme Ho1).
destruct (DyadicExp.dy_lt n m (Dyadic.en_lo one_e)) eqn:Ls.
- (* [m < 1]: [num] holds [1 - m], and [2 atanh((1 - m) / (m + 1)) = - ln m]. *)
  destruct (Dyadic.encl_sub n one_e {| Dyadic.en_lo := m; Dyadic.en_hi := m |}) as [num|] eqn:En;
    [|discriminate H].
  destruct (Dyadic.encl_div n num den) as [s|] eqn:Es; [|discriminate H].
  destruct (DyadicLog.atanh_series n s) as [a1|] eqn:Ea; [|discriminate H].
  destruct (Dyadic.encl_shl n a1 1) as [a2|] eqn:Ea2; [|discriminate H].
  injection H as <- <- <-.
  destruct (sub_step n _ _ num _ _ Hn Oo Ome Lo Lme HE13 HE13 En) as (On & Ln & Hnv).
  specialize (Hnv _ _ Ho1 Hme).
  destruct (div_step n num den s _ _ Hn On Od Ln Ld HE14 HE14 Es) as (Os & Ls' & Hsv).
  specialize (Hsv _ _ Hnv Hdv).
  destruct (atanh_series_correct n s a1 _ _ Hn Os Ls' ltac:(lia) Hsv Ea) as (Oa & La & Ha).
  destruct (shl_step n a1 1 a2 (2 ^ 43) Hn Oa La ltac:(lia) ltac:(lia) Ea2) as (Oa2 & La2 & Ha2).
  split; [exact Pd|]. split; [lia|]. split; [exact Oa2|].
  split; [apply (encl_le_mono (2 ^ 43 + Z.abs 1)); [lia | exact La2]|].
  specialize (Ha2 _ Ha). change (bpow radix2 1) with 2%R in Ha2.
  rewrite Rmult_comm, <- ln_atanh_inv in Ha2 by exact Pm. rewrite Lm in Ha2.
  replace (IZR e0 * ln 2 - ln (Dyadic.dy_R d))%R
    with (- (ln (Dyadic.dy_R d) - IZR e0 * ln 2))%R by ring.
  exact Ha2.
- (* [m >= 1]: [num] holds [m - 1], and [2 atanh((m - 1) / (m + 1)) = ln m]. *)
  destruct (Dyadic.encl_sub n {| Dyadic.en_lo := m; Dyadic.en_hi := m |} one_e) as [num|] eqn:En;
    [|discriminate H].
  destruct (Dyadic.encl_div n num den) as [s|] eqn:Es; [|discriminate H].
  destruct (DyadicLog.atanh_series n s) as [a1|] eqn:Ea; [|discriminate H].
  destruct (Dyadic.encl_shl n a1 1) as [a2|] eqn:Ea2; [|discriminate H].
  injection H as <- <- <-.
  destruct (sub_step n _ _ num _ _ Hn Ome Oo Lme Lo HE13 HE13 En) as (On & Ln & Hnv).
  specialize (Hnv _ _ Hme Ho1).
  destruct (div_step n num den s _ _ Hn On Od Ln Ld HE14 HE14 Es) as (Os & Ls' & Hsv).
  specialize (Hsv _ _ Hnv Hdv).
  destruct (atanh_series_correct n s a1 _ _ Hn Os Ls' ltac:(lia) Hsv Ea) as (Oa & La & Ha).
  destruct (shl_step n a1 1 a2 (2 ^ 43) Hn Oa La ltac:(lia) ltac:(lia) Ea2) as (Oa2 & La2 & Ha2).
  split; [exact Pd|]. split; [lia|]. split; [exact Oa2|].
  split; [apply (encl_le_mono (2 ^ 43 + Z.abs 1)); [lia | exact La2]|].
  specialize (Ha2 _ Ha). change (bpow radix2 1) with 2%R in Ha2.
  rewrite Rmult_comm, <- ln_atanh in Ha2 by exact Pm. rewrite Lm in Ha2.
  exact Ha2.
Qed.

(** ** One-dyadic steps of [ln_encl]

    [sub], [div] and [add] of [DyOps.v] on single dyadic numbers, with the
    bounds on the exponents of their results, as [sub_step], [div_step]
    and [add_step] of [DyGrow.v] give them for enclosures. *)
Lemma lc_dsub :
  forall n x y up d E,
  level_ok n -> dy_ok n x -> dy_ok n y -> - E <= Dyadic.dy_exp x <= E ->
  - E <= Dyadic.dy_exp y <= E -> 0 <= E <= 2 ^ 60 -> Dyadic.sub n x y up = Some d ->
  dy_ok n d /\ - (E + 2 ^ 13) <= Dyadic.dy_exp d <= E + 2 ^ 13 /\
  Dyadic.dy_R d = dround n up (Dyadic.dy_R x - Dyadic.dy_R y).
Proof.
intros n x y up d E Hn Hx Hy Ex Ey HE H.
assert (Sx : exp_small x) by (unfold exp_small; lia).
assert (Sy : exp_small y) by (unfold exp_small; lia).
destruct (sub_correct n x y up Hn Hx Hy Sx Sy) as (d' & E' & Od & Vd).
rewrite H in E'. injection E' as <-.
split; [exact Od|]. split; [|exact Vd].
(* [x - y] is [x + (- y)], and [neg] keeps the exponent. *)
destruct (neg_correct n y Hn Hy) as (Ny & Wy & Xy).
assert (Ey' : - E <= Dyadic.dy_exp (Dyadic.neg n y) <= E) by (rewrite Xy; exact Ey).
pose proof (grow_sum_win n x (Dyadic.neg n y) E E Hn Hx Ny Ex Ey') as W.
rewrite Wy, Z.max_id in W. unfold Rminus in Vd.
apply (grow_exp_of_win n _ up _ (- E) (E + 4096 + 1) _ Hn Od Vd W); lia.
Qed.

Lemma lc_ddiv :
  forall n x y up d Ex Ey,
  level_ok n -> dy_ok n x -> dy_ok n y -> - Ex <= Dyadic.dy_exp x <= Ex ->
  - Ey <= Dyadic.dy_exp y <= Ey -> 0 <= Ex <= 2 ^ 60 -> 0 <= Ey <= 2 ^ 60 ->
  Dyadic.dy_R y <> 0%R -> Dyadic.div n x y up = Some d ->
  dy_ok n d /\ - (Ex + Ey + 2 ^ 13) <= Dyadic.dy_exp d <= Ex + Ey + 2 ^ 13 /\
  Dyadic.dy_R d = dround n up (Dyadic.dy_R x / Dyadic.dy_R y).
Proof.
intros n x y up d Ex Ey Hn Hx Hy Exx Eyy HEx HEy Hy0 H.
assert (Sx : exp_small x) by (unfold exp_small; lia).
assert (Sy : exp_small y) by (unfold exp_small; lia).
destruct (div_correct n x y up Hn Hx Hy Sx Sy Hy0) as (d' & E' & Od & Vd).
rewrite H in E'. injection E' as <-.
split; [exact Od|]. split; [|exact Vd].
pose proof (grow_mul_win _ _ _ _ _ _ (grow_dy_win n x Ex Hn Hx Exx)
  (grow_inv_win _ _ _ Hy0 (grow_dy_win n y Ey Hn Hy Eyy))) as W.
unfold Rdiv in Vd.
apply (grow_exp_of_win n _ up _ _ _ _ Hn Od Vd W); lia.
Qed.

Lemma lc_dadd :
  forall n x y up d Ex Ey,
  level_ok n -> dy_ok n x -> dy_ok n y -> - Ex <= Dyadic.dy_exp x <= Ex ->
  - Ey <= Dyadic.dy_exp y <= Ey -> 0 <= Ex <= 2 ^ 60 -> 0 <= Ey <= 2 ^ 60 ->
  Dyadic.add n x y up = Some d ->
  dy_ok n d /\ - (Z.max Ex Ey + 2 ^ 13) <= Dyadic.dy_exp d <= Z.max Ex Ey + 2 ^ 13 /\
  Dyadic.dy_R d = dround n up (Dyadic.dy_R x + Dyadic.dy_R y).
Proof.
intros n x y up d Ex Ey Hn Hx Hy Exx Eyy HEx HEy H.
assert (Sx : exp_small x) by (unfold exp_small; lia).
assert (Sy : exp_small y) by (unfold exp_small; lia).
destruct (add_correct n x y up Hn Hx Hy Sx Sy) as (d' & E' & Od & Vd).
rewrite H in E'. injection E' as <-.
split; [exact Od|]. split; [|exact Vd].
pose proof (grow_sum_win n x y Ex Ey Hn Hx Hy Exx Eyy) as W.
apply (grow_exp_of_win n _ up _ _ _ _ Hn Od Vd W); lia.
Qed.

Lemma ln_dy_correct :
  forall n d c,
  level_ok n -> dy_ok n d -> exp_small d -> DyadicLog.ln_dy n d = Some c ->
  (0 < Dyadic.dy_R d)%R /\ encl_ok n c /\ encl_le (2 ^ 45) c /\
  encl_has c (ln (Dyadic.dy_R d)).
Proof.
intros n d c Hn Hd Hds H. unfold DyadicLog.ln_dy in H.
destruct (DyadicLog.reduce n d) as [[[e a] less]|] eqn:Er; [|discriminate H].
destruct (DyadicConsts.ln2 n) as [[h l]|] eqn:El; [|discriminate H].
destruct (DyadicExp.mul_int n {| Dyadic.en_lo := h; Dyadic.en_hi := h |} e) as [k1|] eqn:Ek1;
  [|discriminate H].
destruct (DyadicExp.mul_int n l e) as [k2|] eqn:Ek2; [|discriminate H].
destruct (Dyadic.encl_add n k1 k2) as [k|] eqn:Ek; [|discriminate H].
destruct (reduce_correct n d e a less Hn Hd Hds Er) as (Pd & He & Oa & La & Ha).
destruct (ln2_correct n h l Hn El) as (Hh & Heh & Hl & HEl & Hhl).
destruct (hh_correct n h (2 ^ 13) Hh Heh) as (Ohh & Lhh & Hhh).
assert (HE13 : 0 <= 2 ^ 13 <= 2 ^ 60) by lia.
assert (HE14 : 0 <= 2 ^ 14 <= 2 ^ 60) by lia.
(* [e ln 2 = e h + e (ln 2 - h)], with [e h] exact. *)
destruct (mul_int_step n _ e k1 (2 ^ 13) Hn Ohh Lhh HE13 He Ek1) as (Ok1 & Lk1 & Hk1).
destruct (mul_int_step n l e k2 (2 ^ 14) Hn Hl HEl HE14 He Ek2) as (Ok2 & Lk2 & Hk2).
assert (HEk1 : 0 <= 2 ^ 13 + 2 ^ 13 <= 2 ^ 60) by lia.
assert (HEk2 : 0 <= 2 ^ 14 + 2 ^ 13 <= 2 ^ 60) by lia.
destruct (add_step n k1 k2 k _ _ Hn Ok1 Ok2 Lk1 Lk2 HEk1 HEk2 Ek) as (Ok & Lk & Hk).
specialize (Hk _ _ (Hk1 _ Hhh) (Hk2 _ Hhl)).
replace (Dyadic.dy_R h * IZR e + (ln 2 - Dyadic.dy_R h) * IZR e)%R
  with (IZR e * ln 2)%R in Hk by ring.
assert (HEk : 0 <= Z.max (2 ^ 13 + 2 ^ 13) (2 ^ 14 + 2 ^ 13) + 2 ^ 13 <= 2 ^ 60) by lia.
assert (HE44 : 0 <= 2 ^ 44 <= 2 ^ 60) by lia.
split; [exact Pd|].
destruct less.
- (* [a] holds [e ln 2 - ln d]. *)
  destruct (neg_step n a (2 ^ 44) Hn Oa La) as (On & Ln & Hna).
  destruct (add_step n k _ c _ _ Hn Ok On Lk Ln HEk HE44 H) as (Oc & Lc & Hc).
  split; [exact Oc|]. split; [eapply encl_le_mono; [| exact Lc]; lia|].
  specialize (Hc _ _ Hk (Hna _ Ha)).
  replace (ln (Dyadic.dy_R d))
    with (IZR e * ln 2 + - (IZR e * ln 2 - ln (Dyadic.dy_R d)))%R by ring.
  exact Hc.
- (* [a] holds [ln d - e ln 2]. *)
  destruct (add_step n k _ c _ _ Hn Ok Oa Lk La HEk HE44 H) as (Oc & Lc & Hc).
  split; [exact Oc|]. split; [eapply encl_le_mono; [| exact Lc]; lia|].
  specialize (Hc _ _ Hk Ha).
  replace (ln (Dyadic.dy_R d)) with (IZR e * ln 2 + (ln (Dyadic.dy_R d) - IZR e * ln 2))%R
    by ring.
  exact Hc.
Qed.

Lemma ln_encl_correct :
  forall n a c E y,
  level_ok n -> encl_ok n a -> encl_le E a -> 0 <= E <= 2 ^ 30 -> encl_has a y ->
  DyadicLog.ln_encl n a = Some c ->
  (0 < lo_R a)%R /\ encl_ok n c /\ encl_le (2 ^ 46) c /\ encl_has c (ln y).
Proof.
intros n a c E y Hn Ha HaE HE Hy H. unfold DyadicLog.ln_encl in H.
destruct (DyadicLog.ln_dy n (Dyadic.en_lo a)) as [l|] eqn:El; [|discriminate H].
destruct (Dyadic.sub n (Dyadic.en_hi a) (Dyadic.en_lo a) true) as [w1|] eqn:Ew1;
  [|discriminate H].
destruct (Dyadic.div n w1 (Dyadic.en_lo a) true) as [w|] eqn:Ew; [|discriminate H].
destruct (Dyadic.add n (Dyadic.en_hi l) w true) as [hi|] eqn:Ehi; [|discriminate H].
injection H as <-.
pose proof Ha as (Olo & Ohi & Hle). pose proof HaE as (Llo & Lhi).
assert (Slo : exp_small (Dyadic.en_lo a)) by (unfold exp_small; lia).
destruct (ln_dy_correct n _ l Hn Olo Slo El) as (Plo & Ol & Ll & Hl).
assert (HE' : 0 <= E <= 2 ^ 60) by lia.
(* [w1 = hi - lo], [w = w1 / lo] and [hi' = hi_l + w], each rounded up. *)
destruct (lc_dsub n _ _ true w1 E Hn Ohi Olo Lhi Llo HE' Ew1) as (Ow1 & Lw1 & Vw1).
assert (Plo' : Dyadic.dy_R (Dyadic.en_lo a) <> 0%R) by (unfold lo_R in Plo; lra).
assert (HE1 : 0 <= E + 2 ^ 13 <= 2 ^ 60) by lia.
destruct (lc_ddiv n w1 _ true w (E + 2 ^ 13) E Hn Ow1 Olo Lw1 Llo HE1 HE' Plo' Ew)
  as (Ow & Lw & Vw).
pose proof Ol as (Oll & Olh & Hlle). pose proof Ll as (Lll & Llh).
assert (HE45 : 0 <= 2 ^ 45 <= 2 ^ 60) by lia.
assert (HE2 : 0 <= E + 2 ^ 13 + E + 2 ^ 13 <= 2 ^ 60) by lia.
destruct (lc_dadd n _ w true hi (2 ^ 45) (E + 2 ^ 13 + E + 2 ^ 13) Hn Olh Ow Llh Lw
  HE45 HE2 Ehi) as (Ohi' & Lhi' & Vhi').
pose proof (dround_bounds n (Dyadic.dy_R (Dyadic.en_hi a) - Dyadic.dy_R (Dyadic.en_lo a)) Hn)
  as (_ & R1).
rewrite <- Vw1 in R1.
pose proof (dround_bounds n (Dyadic.dy_R w1 / Dyadic.dy_R (Dyadic.en_lo a)) Hn) as (_ & R2).
rewrite <- Vw in R2.
pose proof (dround_bounds n (Dyadic.dy_R (Dyadic.en_hi l) + Dyadic.dy_R w) Hn) as (_ & R3).
rewrite <- Vhi' in R3.
unfold encl_has, lo_R in *.
set (x0 := Dyadic.dy_R (Dyadic.en_lo a)) in *.
(* [w >= (y - x) / x >= 0], as [y - x <= w1]. *)
assert (W : ((y - x0) / x0 <= Dyadic.dy_R w)%R).
{ apply Rle_trans with (Dyadic.dy_R w1 / x0)%R; [| exact R2].
  unfold Rdiv. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra | lra]. }
assert (W0 : (0 <= (y - x0) / x0)%R).
{ unfold Rdiv. apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra]. }
(* [ln x <= ln y <= ln x + (y - x) / x]. *)
pose proof (ln_inc x0 y Plo (proj1 Hy)) as L1.
pose proof (ln_le_sub x0 y (conj Plo (proj1 Hy))) as L2.
set (q := ((y - x0) / x0)%R) in *.
split; [exact Plo|]. split.
- unfold encl_ok; cbn [Dyadic.en_lo Dyadic.en_hi].
  split; [exact Oll|]. split; [exact Ohi'|]. lra.
- split.
  + unfold encl_le; cbn [Dyadic.en_lo Dyadic.en_hi]. lia.
  + cbn [Dyadic.en_lo Dyadic.en_hi]. lra.
Qed.
