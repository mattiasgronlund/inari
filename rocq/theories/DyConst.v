(** * ln 2 and ln 10 in the dyadic kernel

    The tables [LN2] and [LN10] of [DyadicConsts] in [Model.v] are
    [floor(ln 2 * 2^4224)] and [floor(ln 10 * 2^4222)]: [vm_compute] of the
    sums [zsum] of [AtanhSeries.v] at 4,288 bits bounds both constants
    tightly enough to show it. [split] then gives, at each level, a
    normalized [h] and an enclosure of the rest of the constant: at each
    of the 64 levels, [vm_compute] checks that [h] and the bounds are
    normalized and that the bounds, plus [h], enclose the interval
    [[T, T + 1] * 2^-4224] (or [2^-4222]) that holds the constant.

    The 4,288-bit numbers stay behind variables in every lemma that a
    tactic other than [vm_compute] works on, so that no tactic tries to
    reduce them: an earlier draft that rewrote and ran [lia] on goals
    holding them did not finish within 60 s. In the [Z] products that
    [vm_compute] evaluates, the power of two comes first, as [Z.mul]
    recurses on its first factor: the check of the 64 levels takes
    about 3 s this way and 100 s the other way round. *)

From Stdlib Require Import ZArith Reals Lra Lia List Bool.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary DyRound DyConv DyOps DyDriver DyGrow
  AtanhSeries.

Open Scope Z_scope.

(** ** The tables are the floors *)

(** What the tables [t2] and [t10] must satisfy against the sums [s3] of
    [2^4288 atanh(1/3)] (1,353 terms) and [s9] of [2^4288 atanh(1/9)]
    (676 terms): with [2^4288 ln 2] in [[2 s3, 2 s3 + 2 * 1353 + 9/4)] and
    [2^4288 ln 10 = 6 * 2^4288 atanh(1/3) + 2 * 2^4288 atanh(1/9)], the
    tables times [2^64] (resp. [2^66]) and the next integers bracket these
    bounds. *)
Definition dc_tables_okb (t2 t10 s3 s9 : Z) : bool :=
  (2 ^ 64 * t2 <=? 2 * s3) &&
  (2 * s3 + 2 * 1353 + 4 <? 2 ^ 64 * (t2 + 1)) &&
  (2 ^ 66 * t10 <=? 6 * s3 + 2 * s9) &&
  (6 * s3 + 2 * s9 + 6 * 1353 + 2 * 676 + 16 <? 2 ^ 66 * (t10 + 1)).

Lemma dc_tables_ok_true :
  dc_tables_okb (Limbs.val DyadicConsts.LN2) (Limbs.val DyadicConsts.LN10)
    (zsum (3 * 3) (2 ^ 4288 / 3) 0 1353) (zsum (9 * 9) (2 ^ 4288 / 9) 0 676) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma dc_tables_spec :
  forall t2 t10 s3 s9, dc_tables_okb t2 t10 s3 s9 = true ->
  2 ^ 64 * t2 <= 2 * s3 /\ 2 * s3 + 2 * 1353 + 4 < 2 ^ 64 * (t2 + 1) /\
  2 ^ 66 * t10 <= 6 * s3 + 2 * s9 /\
  6 * s3 + 2 * s9 + 6 * 1353 + 2 * 676 + 16 < 2 ^ 66 * (t10 + 1).
Proof.
intros t2 t10 s3 s9 H. unfold dc_tables_okb in H.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1, H3. apply Z.ltb_lt in H2, H4.
exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

(** [3^2707] and [9^1353] exceed [2^4288]. *)
Lemma dc_pow3 : 2 ^ 4288 < 3 ^ Z.of_nat (2 * 1353 + 1).
Proof. apply (proj1 (Z.ltb_lt _ _)). vm_cast_no_check (eq_refl true). Qed.

Lemma dc_pow9 : 2 ^ 4288 < 9 ^ Z.of_nat (2 * 676 + 1).
Proof. apply (proj1 (Z.ltb_lt _ _)). vm_cast_no_check (eq_refl true). Qed.

(** The tail of [zsum_bounds] is below [1 / (1 - q^-2)] once [q^(2n+1)]
    exceeds [2^P]. *)
Lemma dc_tail :
  forall q P n, 2 <= q -> 0 <= P -> 2 ^ P < q ^ Z.of_nat (2 * n + 1) ->
  (bpow radix2 P * (/ IZR q) ^ (2 * n + 1) / (1 - (/ IZR q) ^ 2) <
   / (1 - (/ IZR q) ^ 2))%R.
Proof.
intros q P n Hq HP H.
assert (Hq0 : (2 <= IZR q)%R) by (apply IZR_le; exact Hq).
assert (Hx : (0 < / IZR q < 1)%R).
{ split; [apply Rinv_0_lt_compat; lra |].
  rewrite <- Rinv_1. apply Rinv_lt_contravar; lra. }
assert (Hd : (0 < 1 - (/ IZR q) ^ 2)%R) by nra.
assert (HQ : 0 < q ^ Z.of_nat (2 * n + 1)) by (apply Z.pow_pos_nonneg; lia).
assert (Hb : (bpow radix2 P * (/ IZR q) ^ (2 * n + 1) < 1)%R).
{ assert (HP2 : bpow radix2 P = IZR (2 ^ P)) by (symmetry; exact (IZR_Zpower radix2 P HP)).
  rewrite HP2, pow_inv, pow_IZR.
  apply IZR_lt in H. apply IZR_lt in HQ.
  apply (Rmult_lt_reg_r (IZR (q ^ Z.of_nat (2 * n + 1)))); [exact HQ |].
  rewrite Rmult_assoc, Rinv_l by lra. lra. }
apply (Rmult_lt_compat_r (/ (1 - (/ IZR q) ^ 2))) in Hb;
  [| apply Rinv_0_lt_compat; exact Hd].
rewrite Rmult_1_l in Hb. exact Hb.
Qed.

(** [t / B <= L < (t + 1) / B] from [C t <= lo], [hi <= C (t + 1)] and
    [lo <= C B L < hi]: the floor of [B L] is [t]. *)
Lemma dc_floor :
  forall (t L B C lo hi : R),
  (0 < B -> 0 < C -> C * t <= lo -> hi <= C * (t + 1) -> lo <= C * (B * L) < hi ->
   t * / B <= L < (t + 1) * / B)%R.
Proof.
intros t L B C lo hi HB HC H1 H2 [H3 H4].
assert (E1 : (t <= B * L)%R) by (apply (Rmult_le_reg_l C); [exact HC | lra]).
assert (E2 : (B * L < t + 1)%R) by (apply (Rmult_lt_reg_l C); [exact HC | lra]).
assert (HB' : (0 < / B)%R) by (apply Rinv_0_lt_compat; exact HB).
replace L with (B * L * / B)%R by (field; lra).
split.
- apply Rmult_le_compat_r; lra.
- apply Rmult_lt_compat_r; lra.
Qed.

(** [2^-4224 ln 2] from the sum [s] of [2^4288 atanh(1/3)], with [t] for
    the table: [ln 2 = 2 atanh(1/3)], and [2^4288 = 2^64 2^4224]. *)
Lemma dc_ln2_gen :
  forall (t s : Z) (tl : R),
  2 ^ 64 * t <= 2 * s -> 2 * s + 2 * 1353 + 4 < 2 ^ 64 * (t + 1) ->
  (IZR s <= bpow radix2 4288 * Ratanh (/ IZR 3) <= IZR s + INR 1353 + tl)%R ->
  (tl < / (1 - (/ IZR 3) ^ 2))%R ->
  (IZR t * bpow radix2 (-4224) <= ln 2 < (IZR t + 1) * bpow radix2 (-4224))%R.
Proof.
intros t s tl H1 H2 Hz Ht.
assert (Hq : (/ (1 - (/ IZR 3) ^ 2) = 9 / 8)%R) by field.
assert (Hn : INR 1353 = 1353%R) by (rewrite INR_IZR_INZ; reflexivity).
rewrite Hq in Ht. rewrite Hn in Hz.
apply IZR_le in H1. apply IZR_lt in H2.
rewrite !mult_IZR, IZR_pow2 in H1 by lia.
rewrite !plus_IZR, !mult_IZR, !plus_IZR, IZR_pow2 in H2 by lia.
assert (HB : (bpow radix2 (-4224) = / bpow radix2 4224)%R) by exact (bpow_opp radix2 4224).
assert (HC : (bpow radix2 64 * bpow radix2 4224 = bpow radix2 4288)%R)
  by (rewrite <- bpow_plus; reflexivity).
rewrite HB.
apply (dc_floor (IZR t) (ln 2) (bpow radix2 4224) (bpow radix2 64)
         (2 * IZR s) (2 * IZR s + 2 * 1353 + 4)); [apply bpow_gt_0 | apply bpow_gt_0 | lra | lra |].
rewrite <- Rmult_assoc, HC, ln2_atanh.
replace (1 / 3)%R with (/ IZR 3)%R by (unfold Rdiv; ring).
lra.
Qed.

(** The same for [ln 10 = 3 ln 2 + 2 atanh(1/9) = 6 atanh(1/3) + 2 atanh(1/9)],
    with [2^4288 = 2^66 2^4222]. *)
Lemma dc_ln10_gen :
  forall (t s3 s9 : Z) (tl3 tl9 : R),
  2 ^ 66 * t <= 6 * s3 + 2 * s9 ->
  6 * s3 + 2 * s9 + 6 * 1353 + 2 * 676 + 16 < 2 ^ 66 * (t + 1) ->
  (IZR s3 <= bpow radix2 4288 * Ratanh (/ IZR 3) <= IZR s3 + INR 1353 + tl3)%R ->
  (IZR s9 <= bpow radix2 4288 * Ratanh (/ IZR 9) <= IZR s9 + INR 676 + tl9)%R ->
  (tl3 < / (1 - (/ IZR 3) ^ 2))%R -> (tl9 < / (1 - (/ IZR 9) ^ 2))%R ->
  (IZR t * bpow radix2 (-4222) <= ln 10 < (IZR t + 1) * bpow radix2 (-4222))%R.
Proof.
intros t s3 s9 tl3 tl9 H1 H2 Hz3 Hz9 Ht3 Ht9.
assert (Hq3 : (/ (1 - (/ IZR 3) ^ 2) = 9 / 8)%R) by field.
assert (Hq9 : (/ (1 - (/ IZR 9) ^ 2) = 81 / 80)%R) by field.
assert (Hn3 : INR 1353 = 1353%R) by (rewrite INR_IZR_INZ; reflexivity).
assert (Hn9 : INR 676 = 676%R) by (rewrite INR_IZR_INZ; reflexivity).
rewrite Hq3 in Ht3. rewrite Hq9 in Ht9. rewrite Hn3 in Hz3. rewrite Hn9 in Hz9.
apply IZR_le in H1. apply IZR_lt in H2.
rewrite !plus_IZR, !mult_IZR, IZR_pow2 in H1 by lia.
rewrite !plus_IZR, !mult_IZR, !plus_IZR, IZR_pow2 in H2 by lia.
assert (HB : (bpow radix2 (-4222) = / bpow radix2 4222)%R) by exact (bpow_opp radix2 4222).
assert (HC : (bpow radix2 66 * bpow radix2 4222 = bpow radix2 4288)%R)
  by (rewrite <- bpow_plus; reflexivity).
rewrite HB.
apply (dc_floor (IZR t) (ln 10) (bpow radix2 4222) (bpow radix2 66)
         (6 * IZR s3 + 2 * IZR s9) (6 * IZR s3 + 2 * IZR s9 + 6 * 1353 + 2 * 676 + 16));
  [apply bpow_gt_0 | apply bpow_gt_0 | lra | lra |].
rewrite <- Rmult_assoc, HC, ln10_atanh, ln2_atanh.
replace (1 / 3)%R with (/ IZR 3)%R by (unfold Rdiv; ring).
replace (1 / 9)%R with (/ IZR 9)%R by (unfold Rdiv; ring).
lra.
Qed.

Lemma LN2_bounds :
  (IZR (Limbs.val DyadicConsts.LN2) * bpow radix2 (-4224) <= ln 2 <
   (IZR (Limbs.val DyadicConsts.LN2) + 1) * bpow radix2 (-4224))%R.
Proof.
destruct (dc_tables_spec _ _ _ _ dc_tables_ok_true) as (H1 & H2 & _ & _).
exact (dc_ln2_gen _ _ _ H1 H2 (zsum_bounds 3 4288 1353 ltac:(lia) ltac:(lia))
         (dc_tail 3 4288 1353 ltac:(lia) ltac:(lia) dc_pow3)).
Qed.

Lemma LN10_bounds :
  (IZR (Limbs.val DyadicConsts.LN10) * bpow radix2 (-4222) <= ln 10 <
   (IZR (Limbs.val DyadicConsts.LN10) + 1) * bpow radix2 (-4222))%R.
Proof.
destruct (dc_tables_spec _ _ _ _ dc_tables_ok_true) as (_ & _ & H3 & H4).
exact (dc_ln10_gen _ _ _ _ _ H3 H4
         (zsum_bounds 3 4288 1353 ltac:(lia) ltac:(lia))
         (zsum_bounds 9 4288 676 ltac:(lia) ltac:(lia))
         (dc_tail 3 4288 1353 ltac:(lia) ltac:(lia) dc_pow3)
         (dc_tail 9 4288 676 ltac:(lia) ltac:(lia) dc_pow9)).
Qed.

(** ** [split] at each level *)

(** A unit below every bound of [split]: a nonzero bound rounded from
    [w 2^e] to [n] limbs has an exponent of at least
    [e + 1 - 64 n >= -4224 + 1 - 4096]. [dc_dy_okb] checks it. *)
Definition dc_K : Z := 8448.

(** [m 2^(exp + K)], the value of a nonnegative [d] times [2^K] *)
Definition dc_scaled (d : Dyadic.dyadic) : Z :=
  2 ^ (Dyadic.dy_exp d + dc_K) * Limbs.val (Dyadic.dy_m d).

(** A normalized, nonzero, nonnegative [d] with an exponent of at least [-K] *)
Definition dc_dy_okb (n : nat) (d : Dyadic.dyadic) : bool :=
  forallb (fun a => (0 <=? a) && (a <? 2 ^ 64)) (Dyadic.dy_m d) &&
  Nat.eqb (length (Dyadic.dy_m d)) n &&
  (- 2 ^ 63 <=? Dyadic.dy_exp d) && (Dyadic.dy_exp d <? 2 ^ 63) &&
  (2 ^ (dprec n - 1) <=? Limbs.val (Dyadic.dy_m d)) &&
  negb (Dyadic.dy_neg d) && (- dc_K <=? Dyadic.dy_exp d).

Lemma dc_dy_okb_correct :
  forall n d, dc_dy_okb n d = true ->
  dy_ok n d /\ Dyadic.dy_R d = (IZR (dc_scaled d) * bpow radix2 (- dc_K))%R.
Proof.
intros n [neg e m] H. unfold dc_dy_okb in H. cbn [Dyadic.dy_m Dyadic.dy_exp Dyadic.dy_neg] in H.
repeat rewrite andb_true_iff in H.
destruct H as [[[[[[H1 H2] H3] H4] H5] H6] H7].
apply Nat.eqb_eq in H2. apply Z.leb_le in H3, H5, H7. apply Z.ltb_lt in H4.
apply negb_true_iff in H6. subst neg.
split.
- unfold dy_ok; cbn [Dyadic.dy_m Dyadic.dy_exp Dyadic.dy_neg].
  split; [| split; [exact H2 | split; [lia | right; exact H5]]].
  unfold limbs_ok. apply Forall_forall. intros a Ha.
  rewrite forallb_forall in H1. specialize (H1 a Ha).
  apply andb_prop in H1 as [Ha1 Ha2].
  apply Z.leb_le in Ha1. apply Z.ltb_lt in Ha2. lia.
- unfold Dyadic.dy_R, dc_scaled; cbn [Dyadic.dy_m Dyadic.dy_exp Dyadic.dy_neg].
  rewrite mult_IZR, (IZR_pow2 (e + dc_K)) by lia.
  rewrite (Rmult_comm (bpow radix2 (e + dc_K))), Rmult_assoc, <- bpow_plus.
  f_equal. f_equal. ring.
Qed.

(** What [ln2_correct] and [ln10_correct] need of [split] at one level,
    for a constant in [[t, t + 1] * 2^-s]. *)
Definition dc_split_okb (n : nat) (t s : Z) (o : option (Dyadic.dyadic * Dyadic.encl)) : bool :=
  match o with
  | None => false
  | Some (h, l) =>
      let lo := Dyadic.en_lo l in
      let hi := Dyadic.en_hi l in
      dc_dy_okb n h && dc_dy_okb n lo && dc_dy_okb n hi &&
      (- 2 ^ 13 <=? Dyadic.dy_exp h) && (Dyadic.dy_exp h <=? 2 ^ 13) &&
      (- 2 ^ 14 <=? Dyadic.dy_exp lo) && (Dyadic.dy_exp lo <=? 2 ^ 14) &&
      (- 2 ^ 14 <=? Dyadic.dy_exp hi) && (Dyadic.dy_exp hi <=? 2 ^ 14) &&
      (dc_scaled lo + dc_scaled h <=? 2 ^ (dc_K - s) * t) &&
      (2 ^ (dc_K - s) * (t + 1) <=? dc_scaled hi + dc_scaled h)
  end.

Lemma dc_split_correct :
  forall n t s h l r,
  dc_split_okb n t s (Some (h, l)) = true -> 0 <= s <= dc_K ->
  (IZR t * bpow radix2 (- s) <= r < (IZR t + 1) * bpow radix2 (- s))%R ->
  dy_ok n h /\ - 2 ^ 13 <= Dyadic.dy_exp h <= 2 ^ 13 /\
  encl_ok n l /\ encl_le (2 ^ 14) l /\ encl_has l (r - Dyadic.dy_R h).
Proof.
intros n t s h l r H Hs Hr. unfold dc_split_okb in H. cbv beta iota zeta in H.
repeat rewrite andb_true_iff in H.
destruct H as [[[[[[[[[[Hh Hlo] Hhi] E1] E2] E3] E4] E5] E6] B1] B2].
apply Z.leb_le in E1, E2, E3, E4, E5, E6, B1, B2.
destruct (dc_dy_okb_correct n h Hh) as [Hh1 Hh2].
destruct (dc_dy_okb_correct n _ Hlo) as [Hlo1 Hlo2].
destruct (dc_dy_okb_correct n _ Hhi) as [Hhi1 Hhi2].
(* [t 2^-s] and [(t + 1) 2^-s] in units of [2^-K] *)
assert (HT : forall u, (IZR (2 ^ (dc_K - s) * u) * bpow radix2 (- dc_K) =
                       IZR u * bpow radix2 (- s))%R).
{ intros u. rewrite mult_IZR, (IZR_pow2 (dc_K - s)) by lia.
  rewrite (Rmult_comm (bpow radix2 (dc_K - s))), Rmult_assoc, <- bpow_plus.
  f_equal. f_equal. ring. }
assert (HB : (0 < bpow radix2 (- dc_K))%R) by apply bpow_gt_0.
assert (HBs : (0 < bpow radix2 (- s))%R) by apply bpow_gt_0.
assert (L1 : (Dyadic.dy_R (Dyadic.en_lo l) + Dyadic.dy_R h <= IZR t * bpow radix2 (- s))%R).
{ rewrite Hlo2, Hh2, <- (HT t), <- Rmult_plus_distr_r.
  apply Rmult_le_compat_r; [lra |]. rewrite <- plus_IZR. apply IZR_le. exact B1. }
assert (L2 : ((IZR t + 1) * bpow radix2 (- s) <=
              Dyadic.dy_R (Dyadic.en_hi l) + Dyadic.dy_R h)%R).
{ rewrite Hhi2, Hh2, <- Rmult_plus_distr_r.
  replace (IZR t + 1)%R with (IZR (t + 1)) by (rewrite plus_IZR; reflexivity).
  rewrite <- (HT (t + 1)).
  apply Rmult_le_compat_r; [lra |]. rewrite <- plus_IZR. apply IZR_le. exact B2. }
split; [exact Hh1 |]. split; [lia |]. split; [| split].
- unfold encl_ok. split; [exact Hlo1 |]. split; [exact Hhi1 |]. lra.
- unfold encl_le. lia.
- unfold encl_has. lra.
Qed.

(** All 64 levels of [ln2] and [ln10] *)
Definition dc_level_okb (n : nat) : bool :=
  dc_split_okb n (Limbs.val DyadicConsts.LN2) 4224 (DyadicConsts.ln2 n) &&
  dc_split_okb n (Limbs.val DyadicConsts.LN10) 4222 (DyadicConsts.ln10 n).

Lemma dc_levels_ok_true : forallb dc_level_okb (seq 1 64) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma dc_level :
  forall n, level_ok n ->
  dc_split_okb n (Limbs.val DyadicConsts.LN2) 4224 (DyadicConsts.ln2 n) = true /\
  dc_split_okb n (Limbs.val DyadicConsts.LN10) 4222 (DyadicConsts.ln10 n) = true.
Proof.
intros n Hn.
assert (Hin : In n (seq 1 64)) by (apply in_seq; unfold level_ok in Hn; lia).
pose proof (proj1 (forallb_forall dc_level_okb (seq 1 64)) dc_levels_ok_true n Hin) as H.
unfold dc_level_okb in H. exact (andb_prop _ _ H).
Qed.

Lemma ln2_correct :
  forall n h l,
  level_ok n -> DyadicConsts.ln2 n = Some (h, l) ->
  dy_ok n h /\ - 2 ^ 13 <= Dyadic.dy_exp h <= 2 ^ 13 /\
  encl_ok n l /\ encl_le (2 ^ 14) l /\ encl_has l (ln 2 - Dyadic.dy_R h).
Proof.
intros n h l Hn Heq. destruct (dc_level n Hn) as [H _]. rewrite Heq in H.
apply (dc_split_correct n _ 4224 h l (ln 2) H); [unfold dc_K; lia |].
exact LN2_bounds.
Qed.

Lemma ln10_correct :
  forall n h l,
  level_ok n -> DyadicConsts.ln10 n = Some (h, l) ->
  dy_ok n h /\ - 2 ^ 13 <= Dyadic.dy_exp h <= 2 ^ 13 /\
  encl_ok n l /\ encl_le (2 ^ 14) l /\ encl_has l (ln 10 - Dyadic.dy_R h).
Proof.
intros n h l Hn Heq. destruct (dc_level n Hn) as [_ H]. rewrite Heq in H.
apply (dc_split_correct n _ 4222 h l (ln 10) H); [unfold dc_K; lia |].
exact LN10_bounds.
Qed.
