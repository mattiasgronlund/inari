(** * The product of the two tables of the fast path of [exp]

    [DyadicExp.fast_exp] multiplies the entries [2^(i/4096)] and [2^(j/64)]
    of its two tables, each a pair of [f64]s, into [th + tl]: [th] is the
    product of the high parts rounded, and [tl] adds the error of that
    rounding, exact by [TwoProduct.v] [Dekker], to the two cross products
    ([fast_exp_tbl]). The product of the two powers of 2 is between 1 and
    [2 - 2^-12 + 2^-26] ([tbl_T_bounds]).

    [Dekker] T. J. Dekker, A floating-point technique for extending the
    available precision, Numer. Math. 18 (1971). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Relative.
From Inari Require Import Model Encoding Elementary TwoSum TwoProduct FastExpTables FastExpErr.
From Inari Require MulRuTiny ExpSeries.

Open Scope R_scope.

Local Ltac nums := cbn [bpow radix_val radix2 Z.opp].
Local Ltac nums_in H := cbn [bpow radix_val radix2 Z.opp] in H.

(** The largest exponent is [(63 + 64 * 63) / 4096 = 1 - 2^-12], and
    [2^(1 - 2^-12) = 2 e^(-ln 2 / 4096)]. *)
Lemma tbl_T_bounds :
  forall i j, (0 <= i < 64)%Z -> (0 <= j < 64)%Z ->
  1 <= Rexp2 (IZR i / 4096) * Rexp2 (IZR j / 64) <= 2 - bpow radix2 (-12) + bpow radix2 (-26).
Proof.
intros i j Hi Hj.
unfold Rexp2, Rpower. rewrite <- exp_plus.
pose proof ln_lt_2 as Hl2.
(* [ln 2 < 1] because [2 = 1 + 1 < e]. *)
assert (Hl1 : ln 2 < 1).
{ rewrite <- (ln_exp 1). apply ln_increasing; [lra |].
  pose proof (exp_ineq1 1 ltac:(lra)). lra. }
assert (Hi' : 0 <= IZR i <= 63) by (split; apply IZR_le; lia).
assert (Hj' : 0 <= IZR j <= 63) by (split; apply IZR_le; lia).
set (y := ln 2 / 4096).
set (n := IZR i + 64 * IZR j).
assert (Hy : / 8192 < y < 1) by (unfold y; lra).
assert (Hn : 0 <= n <= 4095) by (unfold n; lra).
replace (IZR i / 4096 * ln 2 + IZR j / 64 * ln 2) with (n * y) by (unfold n, y; field).
split.
- rewrite <- exp_0. apply exp_le. apply Rmult_le_pos; lra.
- (* The exponent is at most [4095 y = ln 2 - y], and [e^(ln 2 - y) = 2 e^-y]. *)
  apply Rle_trans with (exp (ln 2 + - y)).
  { apply exp_le. replace (ln 2 + - y) with (4095 * y) by (unfold y; field).
    apply Rmult_le_compat_r; lra. }
  rewrite exp_plus, exp_ln by lra.
  destruct (ExpSeries.exp_alt_bounds y 1 ltac:(lra)) as [_ Hu].
  replace (sum_f_R0 (tg_alt (ExpSeries.exp_tg y)) (2 * 1)) with (1 - y + y * y / 2) in Hu
    by (unfold tg_alt, ExpSeries.exp_tg; cbn; field).
  (* [2 (1 - y + y^2/2) <= 2 - 2/8192 + 1/8192^2] as [y] is between [1/8192] and [1]. *)
  assert (H : 0 <= (y - / 8192) * (2 - y - / 8192)) by (apply Rmult_le_pos; lra).
  cbn [bpow radix_val radix2 Z.opp]. lra.
Qed.

(** [th + tl] is [2^(i/4096) 2^(j/64)] within [2^-100], and the product
    [th] of the high parts is exact for [Generic.two_prod_err] with and
    without an FMA. *)
Lemma fast_exp_tbl :
  forall fma i j a1h a1l a2h a2l,
  (0 <= i < 64)%Z -> (0 <= j < 64)%Z ->
  DyadicExp.tbl DyadicExp.T1 i = (a1h, a1l) -> DyadicExp.tbl DyadicExp.T2 j = (a2h, a2l) ->
  let th := mul a1h a2h in
  let tl := add (Generic.two_prod_err fma a1h a2h th) (add (mul a1h a2l) (mul a1l a2h)) in
  is_finite th = true /\ is_finite tl = true /\ 1 <= B2R th < 2 /\
  Rabs (B2R tl) <= 3 * bpow radix2 (-52) /\
  Rabs (B2R th + B2R tl - Rexp2 (IZR i / 4096) * Rexp2 (IZR j / 64)) <= bpow radix2 (-100) /\
  (forall b, Generic.two_prod_is_exact b a1h a2h th = true).
Proof.
intros fma i j a1h a1l a2h a2l Hi Hj E1 E2. cbv zeta.
destruct (t1_correct i a1h a1l Hi E1) as (F1h & F1l & H1h & H1l & H1).
destruct (t2_correct j a2h a2l Hj E2) as (F2h & F2l & H2h & H2l & H2).
pose proof (tbl_T_bounds i j Hi Hj) as HT.
set (T1 := Rexp2 (IZR i / 4096)) in *.
set (T2 := Rexp2 (IZR j / 64)) in *.
nums_in H1l. nums_in H1. nums_in H2l. nums_in H2. nums_in HT.
apply Rabs_le_inv in H1l. apply Rabs_le_inv in H1.
apply Rabs_le_inv in H2l. apply Rabs_le_inv in H2.
(* [a1h a2h - T1 T2 = (a1h - T1) a2h + T1 (a2h - T2)], and [a1h], [a2h]
   are within [2^-53 + 2^-104] of [T1], [T2], so [a1h a2h < 2 - 2^-13]. *)
assert (Hd1 : Rabs ((B2R a1h - T1) * B2R a2h)
              <= (bpow radix2 (-53) + bpow radix2 (-104)) * 2)
  by (apply Rabs_mul_le; apply Rabs_le; nums; lra).
assert (Hd2 : Rabs (T1 * (B2R a2h - T2))
              <= (2 + bpow radix2 (-53) + bpow radix2 (-104))
                 * (bpow radix2 (-53) + bpow radix2 (-104)))
  by (apply Rabs_mul_le; apply Rabs_le; nums; lra).
apply Rabs_le_inv in Hd1. apply Rabs_le_inv in Hd2. nums_in Hd1. nums_in Hd2.
assert (HP1 : 1 * 1 <= B2R a1h * B2R a2h) by (apply Rmult_le_compat; lra).
assert (HP : Rabs (B2R a1h * B2R a2h) <= 2 - bpow radix2 (-13)) by (apply Rabs_le; nums; lra).
(* [th = RN (a1h a2h)] with [1 <= th < 2]. *)
destruct (mul_k a1h a2h _ F1h F2h HP ltac:(nums; lra)) as (Fth & Rth & Hth).
assert (Hth1 : 1 <= B2R (mul a1h a2h)).
{ rewrite Rth. apply round_ge_generic; [typeclasses eauto | typeclasses eauto | | lra].
  change 1 with (bpow radix2 0). apply generic_format_FLT_bpow; [easy | lia]. }
assert (Hth2 : B2R (mul a1h a2h) < 2).
{ apply Rabs_le_inv in Hth. revert Hth. nums. lra. }
(* The exponent of [th] is 0 and those of [a1h], [a2h] are at most 0, so
   [two_prod_is_exact] holds with and without an FMA. *)
assert (Xth : Generic.exponent (mul a1h a2h) = 0%Z).
{ assert (A : bpow radix2 0 <= Rabs (B2R (mul a1h a2h)))
    by (rewrite Rabs_pos_eq by lra; cbn [bpow radix_val radix2 Z.pow_pos]; lra).
  assert (B : Rabs (B2R (mul a1h a2h)) < bpow radix2 1)
    by (rewrite Rabs_pos_eq by lra; cbn [bpow radix_val radix2 Z.pow_pos]; lra).
  pose proof (MulRuTiny.exponent_ge _ 0 Fth A).
  pose proof (MulRuTiny.exponent_lt _ 1 Fth ltac:(lia) B).
  lia. }
assert (X1 : (Generic.exponent a1h < 1)%Z).
{ apply MulRuTiny.exponent_lt; [exact F1h | lia |].
  rewrite Rabs_pos_eq by lra. cbn [bpow radix_val radix2 Z.pow_pos]. lra. }
assert (X2 : (Generic.exponent a2h < 1)%Z).
{ apply MulRuTiny.exponent_lt; [exact F2h | lia |].
  rewrite Rabs_pos_eq by lra. cbn [bpow radix_val radix2 Z.pow_pos]. lra. }
assert (Hex : forall b, Generic.two_prod_is_exact b a1h a2h (mul a1h a2h) = true).
{ intros b. unfold Generic.two_prod_is_exact. cbv zeta.
  destruct b; rewrite ?andb_true_iff, ?Z.leb_le; lia. }
destruct (two_prod_err_correct fma a1h a2h F1h F2h (Hex fma)) as (_ & _ & _ & Ferr & Eerr).
set (th := mul a1h a2h) in *.
set (err := Generic.two_prod_err fma a1h a2h th) in *.
(* The cross products: [|a1h a2l|, |a1l a2h| <= 2^-52]. *)
assert (Hc1 : Rabs (B2R a1h * B2R a2l) <= bpow radix2 (-52)).
{ eapply Rle_trans; [apply (Rabs_mul_le _ _ 2 (bpow radix2 (-53))); apply Rabs_le; nums; lra |].
  nums. lra. }
assert (Hc2 : Rabs (B2R a1l * B2R a2h) <= bpow radix2 (-52)).
{ eapply Rle_trans; [apply (Rabs_mul_le _ _ (bpow radix2 (-53)) 2); apply Rabs_le; nums; lra |].
  nums. lra. }
destruct (mul_k a1h a2l _ F1h F2l Hc1 ltac:(nums; lra)) as (Fm1 & _ & Hm1).
destruct (mul_k a1l a2h _ F1l F2h Hc2 ltac:(nums; lra)) as (Fm2 & _ & Hm2).
set (m1 := mul a1h a2l) in *. set (m2 := mul a1l a2h) in *.
apply Rabs_le_inv in Hc1. apply Rabs_le_inv in Hc2.
apply Rabs_le_inv in Hm1. apply Rabs_le_inv in Hm2.
apply Rabs_le_inv in Hth.
nums. nums_in Hc1. nums_in Hc2. nums_in Hm1. nums_in Hm2. nums_in Hth.
assert (Hs1 : Rabs (B2R m1 + B2R m2) <= bpow radix2 (-51) + bpow radix2 (-103))
  by (apply Rabs_le; nums; lra).
destruct (add_k m1 m2 _ Fm1 Fm2 Hs1 ltac:(nums; lra)) as (Fs1 & _ & Hs).
set (s1 := add m1 m2) in *.
apply Rabs_le_inv in Hs. nums_in Hs.
(* [|err| <= 2^-53 (2 - 2^-13)] by the relative bound, so the sum is
   below [3 2^-52 - 2^-67]. *)
assert (Htl0 : Rabs (B2R err + B2R s1) <= 3 * bpow radix2 (-52) - bpow radix2 (-67))
  by (apply Rabs_le; nums; lra).
destruct (add_k err s1 _ Ferr Fs1 Htl0 ltac:(nums; lra)) as (Ftl & _ & Htl).
set (tl := add err s1) in *.
apply Rabs_le_inv in Htl. nums_in Htl.
(* The error: [A1 A2 - T1 T2 = (A1 - T1) A2 + T1 (A2 - T2)] with [Ak = akh + akl],
   then [A1 A2 - (th + tl) = a1l a2l] minus the four rounding errors. *)
assert (Hf1 : Rabs ((B2R a1h + B2R a1l - T1) * (B2R a2h + B2R a2l))
              <= bpow radix2 (-104) * (2 + bpow radix2 (-53)))
  by (apply Rabs_mul_le; apply Rabs_le; nums; lra).
assert (Hf2 : Rabs (T1 * (B2R a2h + B2R a2l - T2))
              <= (2 + bpow radix2 (-53) + bpow radix2 (-104)) * bpow radix2 (-104))
  by (apply Rabs_mul_le; apply Rabs_le; nums; lra).
assert (Hll : Rabs (B2R a1l * B2R a2l) <= bpow radix2 (-53) * bpow radix2 (-53))
  by (apply Rabs_mul_le; apply Rabs_le; nums; lra).
apply Rabs_le_inv in Hf1. apply Rabs_le_inv in Hf2. apply Rabs_le_inv in Hll.
nums_in Hf1. nums_in Hf2. nums_in Hll.
split; [exact Fth |]. split; [exact Ftl |]. split; [lra |]. split; [apply Rabs_le; lra |].
split; [apply Rabs_le; lra | exact Hex].
Qed.
