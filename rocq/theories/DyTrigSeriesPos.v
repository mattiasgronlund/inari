(** * The series of [sin] and [cos] in the dyadic kernel stay above 0

    For an enclosure [r] in [[0, 4/5]], Horner's scheme of [series]
    starts from [[0, 1]], and each step [1 - z t / d] with [z = r^2] in
    [[0, 1]] and [d >= 2] keeps the enclosure [t] in [[0, 1]], and above
    0 after the first step. [series] takes at least one step, so the
    enclosure of [cos] ([t]) lies above 0, and that of [sin] ([r t])
    lies above 0 if [r] does ([series_pos]) and below 1
    ([series_sin_lt1]). [DyTrigPos.v] uses these for the signs of
    [sin x] and [cos x] at every level. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary LogReal DyRound DyConv DyOps DyDriver DyGrow
  DyConst DyExpCore DyExpRules DyExp ExpReal DyHypRules DyLogRules DyLogCore DyLog DyLogHyp
  TrigSeries DyTrigTiny DyCosSmall DySinSmall DyTanSmall DyTrigReduce DyTrigCore MpfrRound DyTrig.

Open Scope Z_scope.

(** ** Helpers *)

(** [1] has [dprec n] bits. *)
Lemma sp_round_1 : forall n up, level_ok n -> dround n up 1 = 1%R.
Proof.
intros n up Hn. pose proof (dprec_gt_0 n Hn). apply dround_id; [exact Hn|].
apply generic_format_FLX_1; assumption.
Qed.

Lemma sp_rd_nonneg : forall n r, level_ok n -> (0 <= r)%R -> (0 <= dround n false r)%R.
Proof.
intros n r Hn Hr. rewrite <- (dround_0 n false Hn). apply dround_le; assumption.
Qed.

Lemma sp_ru_le1 : forall n r, level_ok n -> (r <= 1)%R -> (dround n true r <= 1)%R.
Proof.
intros n r Hn Hr. rewrite <- (sp_round_1 n true Hn). apply dround_le; assumption.
Qed.

(** The relative width of a rounding to [dprec n >= 64] bits,
    [2^(1 - dprec n)], is at most [2^-3]. *)
Lemma sp_eps : forall n, level_ok n -> (0 < bpow radix2 (1 - dprec n) <= / 8)%R.
Proof.
intros n Hn. pose proof (dprec_bounds n Hn). split; [apply bpow_gt_0|].
apply (Rle_trans _ (bpow radix2 (-3))); [apply bpow_le; lia|].
cbn [bpow radix_val radix2]. lra.
Qed.

(** Rounding to [dprec n] bits has no underflow: [RD r >= r (1 - 2^-3)]
    by [dround_width]. *)
Lemma sp_rd_pos : forall n r, level_ok n -> (0 < r)%R -> (0 < dround n false r)%R.
Proof.
intros n r Hn Hr. pose proof (dround_bounds n r Hn) as B. pose proof (dround_width n r Hn) as W.
pose proof (sp_eps n Hn) as Ep. rewrite (Rabs_pos_eq r) in W by lra.
assert (r * bpow radix2 (1 - dprec n) <= r / 8)%R by nra.
lra.
Qed.

(** [RU (4/5) <= 4/5 (1 + 2^-3) < 1]. *)
Lemma sp_ru_lt1 : forall n r, level_ok n -> (r <= 4 / 5)%R -> (dround n true r < 1)%R.
Proof.
intros n r Hn Hr. apply (Rle_lt_trans _ (dround n true (4 / 5))); [apply dround_le; assumption|].
pose proof (dround_bounds n (4 / 5) Hn) as B. pose proof (dround_width n (4 / 5) Hn) as W.
pose proof (sp_eps n Hn) as Ep. rewrite (Rabs_pos_eq (4 / 5)) in W by lra.
lra.
Qed.

(** A product of enclosures above 0 is the product of the lower ends
    rounded down and of the upper ends rounded up. *)
Lemma sp_mul_pos :
  forall n a b c,
  level_ok n -> encl_ok n a -> encl_ok n b -> encl_small a -> encl_small b ->
  (0 <= lo_R a)%R -> (0 <= lo_R b)%R -> Dyadic.encl_mul n a b = Some c ->
  encl_ok n c /\ lo_R c = dround n false (lo_R a * lo_R b) /\
  hi_R c = dround n true (hi_R a * hi_R b).
Proof.
intros n a b c Hn Ha Hb Sa Sb Pa Pb H.
destruct (encl_mul_correct n a b Hn Ha Hb Sa Sb) as (c' & E' & Okc & Vlo & Vhi & _).
rewrite H in E'. injection E' as <-.
assert (Ra : (lo_R a <= hi_R a)%R) by (destruct Ha as (_ & _ & X); exact X).
assert (Rb : (lo_R b <= hi_R b)%R) by (destruct Hb as (_ & _ & X); exact X).
split; [exact Okc|]. rewrite Vlo, Vhi. split; f_equal.
- apply Rle_antisym.
  + eapply Rle_trans; [apply Rmin_l|]. eapply Rle_trans; [apply Rmin_l|]. apply Rmin_l.
  + repeat apply Rmin_glb; nra.
- apply Rle_antisym.
  + repeat apply Rmax_lub; nra.
  + apply Rmax_r.
Qed.

(** [terms n z >= 1]: [6 n + 5], or the smaller of it and a quotient
    [(64 n + 3 + e) / e] with [e > 0]. *)
Lemma sp_terms : forall n z, level_ok n -> 1 <= DyadicTrig.terms n z.
Proof.
intros n z Hn. unfold level_ok in Hn. unfold DyadicTrig.terms. cbv zeta.
destruct (Z.leb_spec (- (64 * Z.of_nat n)) (Dyadic.dy_exp (Dyadic.en_hi z))); [lia|].
set (e := - (64 * Z.of_nat n) - Dyadic.dy_exp (Dyadic.en_hi z)).
assert (He : 0 < e) by (unfold e; lia).
assert (Hq : 1 <= (64 * Z.of_nat n + 3 + e) / e) by (apply Z.div_le_lower_bound; lia).
revert Hq. generalize ((64 * Z.of_nat n + 3 + e) / e). intros q Hq. lia.
Qed.

(** ** The loop of [series]

    The bookkeeping of [tc_series_loop_correct] ([DyTrigCore.v]), with
    bounds in place of the value: for [z] in [[0, 1]] and [t] in [[0, 1]],
    [p = z t] lies in [[0, 1]], [q = p / d] with [d >= 2] in [[0, 1/2]]
    rounded, so below 1 ([sp_ru_lt1]), and [1 - q] in [(0, 1]]. *)
Lemma sp_loop :
  forall n one_e z o Ez,
  level_ok n -> encl_ok n one_e -> encl_le (2 ^ 13) one_e ->
  lo_R one_e = 1%R -> hi_R one_e = 1%R ->
  encl_ok n z -> encl_le Ez z -> 0 <= Ez <= 2 ^ 40 -> (0 <= lo_R z)%R -> (hi_R z <= 1)%R ->
  0 <= o <= 1 ->
  forall i t Et t',
  Z.of_nat i <= 389 ->
  encl_ok n t -> encl_le Et t -> 0 <= Et -> Et + Z.of_nat i * (Ez + 2 ^ 15) <= 2 ^ 59 ->
  (0 <= lo_R t)%R -> (hi_R t <= 1)%R ->
  DyadicTrig.series_loop n one_e z o i t = Some t' ->
  encl_ok n t' /\ encl_le (Et + Z.of_nat i * (Ez + 2 ^ 15)) t' /\
  (0 <= lo_R t')%R /\ (hi_R t' <= 1)%R /\
  ((i <> 0)%nat \/ (0 < lo_R t)%R -> (0 < lo_R t')%R).
Proof.
intros n one_e z o Ez Hn Ho HoE Hol Hoh Hz HzE HEz Hz0 Hz1 Ho01 i.
induction i as [|k IH]; intros t Et t' Hi Ht HtE HEt0 HEt Htl0 Hth1 H.
- cbn [DyadicTrig.series_loop] in H. injection H as <-.
  split; [exact Ht|]. split; [rewrite Z.mul_0_l, Z.add_0_r; exact HtE|].
  split; [exact Htl0|]. split; [exact Hth1|].
  intros [K | K]; [exfalso; apply K; reflexivity | exact K].
- cbn [DyadicTrig.series_loop] in H.
  set (d := (2 * Z.of_nat k + 1 + o) * (2 * Z.of_nat k + 2 + o)) in H.
  destruct (Dyadic.encl_mul n z t) as [p|] eqn:Ep; [|discriminate H].
  destruct (Dyadic.encl_div_u64 n p d) as [q|] eqn:Eq; [|discriminate H].
  destruct (Dyadic.encl_sub n one_e q) as [t1|] eqn:Et1; [|discriminate H].
  rewrite Nat2Z.inj_succ in Hi, HEt.
  assert (HEt' : Et <= 2 ^ 59) by nia.
  (* The divisor is at least [1 * 2] and at most [(2 * 388 + 2) (2 * 388 + 3)]. *)
  assert (Hd2 : 2 <= d).
  { unfold d. apply (Z.le_trans _ (1 * 2)); [lia | apply Z.mul_le_mono_nonneg; lia]. }
  assert (Hd : 0 < d < 2 ^ 64).
  { split; [lia|]. unfold d.
    apply (Z.le_lt_trans _ (780 * 780)); [apply Z.mul_le_mono_nonneg; lia | lia]. }
  assert (HE1 : 0 <= Ez <= 2 ^ 60) by lia.
  assert (HE2 : 0 <= Et <= 2 ^ 60) by lia.
  destruct (mul_step n z t p Ez Et Hn Hz Ht HzE HtE HE1 HE2 Ep) as (Hp & HpE & _).
  assert (HE3 : 0 <= Ez + Et + 2 ^ 13 <= 2 ^ 60) by lia.
  destruct (div_u64_step n p d q _ Hn Hp HpE HE3 Hd Eq) as (Hq & HqE & _).
  assert (HE4 : 0 <= (2 ^ 13 : Z) <= 2 ^ 60) by lia.
  assert (HE5 : 0 <= Ez + Et + 2 ^ 13 + 2 ^ 13 <= 2 ^ 60) by lia.
  destruct (sub_step n one_e q t1 _ _ Hn Ho Hq HoE HqE HE4 HE5 Et1) as (Ht1 & Ht1E & _).
  (* The values of [p], [q] and [t1]. *)
  assert (Sz : encl_small z) by (apply (encl_le_small Ez); [lia | exact HzE]).
  assert (St : encl_small t) by (apply (encl_le_small Et); [lia | exact HtE]).
  assert (Sp : encl_small p) by (apply (encl_le_small (Ez + Et + 2 ^ 13)); [lia | exact HpE]).
  assert (Sq : encl_small q)
    by (apply (encl_le_small (Ez + Et + 2 ^ 13 + 2 ^ 13)); [lia | exact HqE]).
  assert (So : encl_small one_e) by (apply (encl_le_small (2 ^ 13)); [lia | exact HoE]).
  destruct (sp_mul_pos n z t p Hn Hz Ht Sz St Hz0 Htl0 Ep) as (_ & Vpl & Vph).
  destruct (encl_div_u64_correct n p d Hn Hp Sp Hd) as (q' & Eq' & _ & Vql & Vqh & _).
  rewrite Eq in Eq'. injection Eq' as <-.
  destruct (encl_sub_correct n one_e q Hn Ho Hq So Sq) as (t1' & Et1' & _ & Vtl & Vth & _).
  rewrite Et1 in Et1'. injection Et1' as <-.
  assert (Rz : (lo_R z <= hi_R z)%R) by (destruct Hz as (_ & _ & X); exact X).
  assert (Rt : (lo_R t <= hi_R t)%R) by (destruct Ht as (_ & _ & X); exact X).
  assert (Rp : (lo_R p <= hi_R p)%R) by (destruct Hp as (_ & _ & X); exact X).
  assert (Hp0 : (0 <= lo_R p)%R)
    by (rewrite Vpl; apply sp_rd_nonneg; [exact Hn | apply Rmult_le_pos; assumption]).
  assert (Hp1 : (hi_R p <= 1)%R) by (rewrite Vph; apply sp_ru_le1; [exact Hn | nra]).
  assert (Hiv : (0 < / IZR d <= / 2)%R).
  { assert (D : (2 <= IZR d)%R) by (apply IZR_le; exact Hd2).
    split; [apply Rinv_0_lt_compat; lra | apply Rinv_le_contravar; lra]. }
  unfold Rdiv in Vql, Vqh.
  assert (Hq0 : (0 <= lo_R q)%R) by (rewrite Vql; apply sp_rd_nonneg; [exact Hn | nra]).
  assert (Hq1 : (hi_R q < 1)%R) by (rewrite Vqh; apply sp_ru_lt1; [exact Hn | nra]).
  assert (Ht1p : (0 < lo_R t1)%R)
    by (rewrite Vtl, Hol; apply sp_rd_pos; [exact Hn | lra]).
  assert (Ht11 : (hi_R t1 <= 1)%R)
    by (rewrite Vth, Hoh; apply sp_ru_le1; [exact Hn | lra]).
  (* The rest of the loop. *)
  assert (Ht1E' : encl_le (Et + (Ez + 2 ^ 15)) t1).
  { apply (encl_le_mono (Z.max (2 ^ 13) (Ez + Et + 2 ^ 13 + 2 ^ 13) + 2 ^ 13));
      [lia | exact Ht1E]. }
  assert (Hk : Z.of_nat k <= 389) by lia.
  assert (HEt1 : 0 <= Et + (Ez + 2 ^ 15)) by lia.
  assert (HEt2 : Et + (Ez + 2 ^ 15) + Z.of_nat k * (Ez + 2 ^ 15) <= 2 ^ 59) by nia.
  destruct (IH t1 (Et + (Ez + 2 ^ 15)) t' Hk Ht1 Ht1E' HEt1 HEt2 (Rlt_le _ _ Ht1p) Ht11 H)
    as (A & B & C & D & F).
  split; [exact A|]. split.
  + apply (encl_le_mono (Et + (Ez + 2 ^ 15) + Z.of_nat k * (Ez + 2 ^ 15))); [| exact B].
    rewrite Nat2Z.inj_succ. nia.
  + split; [exact C|]. split; [exact D|]. intros _. apply F. right. exact Ht1p.
Qed.

(** ** [series]

    [z = r r] lies in [[0, 1]] for [r] in [[0, 4/5]], the loop starts
    from [[0, 1]] and runs [terms n z >= 1] steps, so [t] lies in
    [(0, 1]]. [cos] is [t]; [sin] is [r t], above 0 if [r] is, and at
    most [RU (4/5) < 1]. The bookkeeping of the exponents is that of
    [series_correct] ([DyTrigCore.v]). *)
Lemma sp_series :
  forall n r odd c E,
  level_ok n -> encl_ok n r -> encl_le E r -> 0 <= E <= 2 ^ 34 ->
  (0 <= lo_R r)%R -> (hi_R r <= 4 / 5)%R ->
  DyadicTrig.series n r odd = Some c ->
  (odd = false -> (0 < lo_R c)%R) /\ (odd = true -> (0 < lo_R r)%R -> (0 < lo_R c)%R) /\
  (odd = true -> (hi_R c < 1)%R).
Proof.
intros n r odd c E Hn Hr HrE HE Hr0 Hr1 H. unfold DyadicTrig.series in H.
destruct (Dyadic.encl_point n DyadicExp.one) as [one_e|] eqn:E1; [|discriminate H].
destruct (Dyadic.encl_mul n r r) as [z|] eqn:Ez; [|discriminate H].
set (K := DyadicTrig.terms n z) in H.
assert (Hk : 1 <= K <= 389).
{ split; [exact (sp_terms n z Hn) | exact (proj2 (tc_terms n z Hn))]. }
clearbody K.
set (t0 := {| Dyadic.en_lo := Dyadic.dy_zero n; Dyadic.en_hi := Dyadic.en_hi one_e |}) in H.
destruct (DyadicTrig.series_loop n one_e z (Z.b2z odd) (Z.to_nat K) t0) as [t|] eqn:Et;
  [|discriminate H].
destruct (point_step n _ _ Hn E1) as (Ho & HoE & Hol & Hoh & _).
rewrite dexp_one_R in Hol, Hoh.
assert (HE1 : 0 <= E <= 2 ^ 60) by lia.
destruct (mul_step n r r z _ _ Hn Hr Hr HrE HrE HE1 HE1 Ez) as (Hz & HzE & _).
assert (Sr : encl_small r) by (apply (encl_le_small E); [lia | exact HrE]).
destruct (sp_mul_pos n r r z Hn Hr Hr Sr Sr Hr0 Hr0 Ez) as (_ & Vzl & Vzh).
assert (Rr : (lo_R r <= hi_R r)%R) by (destruct Hr as (_ & _ & X); exact X).
assert (Hz0 : (0 <= lo_R z)%R)
  by (rewrite Vzl; apply sp_rd_nonneg; [exact Hn | apply Rmult_le_pos; assumption]).
assert (Hz1 : (hi_R z <= 1)%R) by (rewrite Vzh; apply sp_ru_le1; [exact Hn | nra]).
(* The start [t0] is [[0, 1]]: its upper bound is that of the point 1. *)
destruct (dy_zero_ok n) as (Oz & Vz & _).
assert (Ht0 : encl_ok n t0).
{ destruct Ho as (_ & Ohi & _). unfold hi_R in Hoh.
  unfold encl_ok, t0; cbn [Dyadic.en_lo Dyadic.en_hi].
  split; [exact Oz|]. split; [exact Ohi|]. rewrite Vz, Hoh. lra. }
assert (Ht0E : encl_le (2 ^ 13) t0).
{ destruct HoE as (_ & Lhi).
  unfold encl_le, t0; cbn [Dyadic.en_lo Dyadic.en_hi Dyadic.dy_zero Dyadic.dy_exp].
  split; [lia | exact Lhi]. }
assert (Ht00 : (0 <= lo_R t0)%R).
{ unfold lo_R, t0; cbn [Dyadic.en_lo]. rewrite Vz. lra. }
assert (Ht01 : (hi_R t0 <= 1)%R).
{ unfold hi_R in Hoh |- *. unfold t0; cbn [Dyadic.en_hi]. rewrite Hoh. lra. }
assert (HEz : 0 <= E + E + 2 ^ 13 <= 2 ^ 40) by lia.
assert (HE0 : 0 <= (2 ^ 13 : Z)) by lia.
assert (HKi : Z.of_nat (Z.to_nat K) <= 389) by lia.
assert (HEb : 2 ^ 13 + Z.of_nat (Z.to_nat K) * (E + E + 2 ^ 13 + 2 ^ 15) <= 2 ^ 59).
{ rewrite Z2Nat.id by lia. nia. }
assert (Ho01 : 0 <= Z.b2z odd <= 1) by (destruct odd; cbn; lia).
destruct (sp_loop n one_e z (Z.b2z odd) _ Hn Ho HoE Hol Hoh Hz HzE HEz Hz0 Hz1 Ho01
  _ t0 _ t HKi Ht0 Ht0E HE0 HEb Ht00 Ht01 Et) as (Ht & HtE & Htl & Hth & Htp).
assert (HK0 : (Z.to_nat K <> 0)%nat) by lia.
assert (HtP : (0 < lo_R t)%R) by (apply Htp; left; exact HK0).
rewrite Z2Nat.id in HtE by lia.
destruct odd; cbv iota in H.
- (* [sin] is [r t]. *)
  assert (St : encl_small t).
  { apply (encl_le_small (2 ^ 13 + K * (E + E + 2 ^ 13 + 2 ^ 15))); [nia | exact HtE]. }
  destruct (sp_mul_pos n r t c Hn Hr Ht Sr St Hr0 Htl H) as (_ & Vcl & Vch).
  assert (Rt : (lo_R t <= hi_R t)%R) by (destruct Ht as (_ & _ & X); exact X).
  split; [intros X; discriminate X|]. split.
  + intros _ Hrp. rewrite Vcl. apply sp_rd_pos; [exact Hn|].
    apply Rmult_lt_0_compat; assumption.
  + intros _. rewrite Vch. apply sp_ru_lt1; [exact Hn|]. nra.
- (* [cos] is [t]. *)
  injection H as <-.
  split; [intros _; exact HtP|]. split; intros X; discriminate X.
Qed.

Lemma series_pos :
  forall n r odd c E,
  level_ok n -> encl_ok n r -> encl_le E r -> 0 <= E <= 2 ^ 34 ->
  (0 <= lo_R r)%R -> (hi_R r <= 4 / 5)%R -> (odd = true -> (0 < lo_R r)%R) ->
  DyadicTrig.series n r odd = Some c -> (0 < lo_R c)%R.
Proof.
intros n r odd c E Hn Hr HrE HE Hr0 Hr1 Hodd H.
destruct (sp_series n r odd c E Hn Hr HrE HE Hr0 Hr1 H) as (A & B & _).
destruct odd.
- apply B; [reflexivity | apply Hodd; reflexivity].
- apply A; reflexivity.
Qed.

Lemma series_sin_lt1 :
  forall n r c E,
  level_ok n -> encl_ok n r -> encl_le E r -> 0 <= E <= 2 ^ 34 ->
  (0 <= lo_R r)%R -> (hi_R r <= 4 / 5)%R ->
  DyadicTrig.series n r true = Some c -> (hi_R c < 1)%R.
Proof.
intros n r c E Hn Hr HrE HE Hr0 Hr1 H.
destruct (sp_series n r true c E Hn Hr HrE HE Hr0 Hr1 H) as (_ & _ & C).
apply C. reflexivity.
Qed.
