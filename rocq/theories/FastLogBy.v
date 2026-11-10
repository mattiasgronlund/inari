(** * The fast paths of [log2] and [log10] before the rounding

    [DyadicLog.fast_log_by] of [Model.v] computes [e d + (ah + al) c]
    from the core ([FastLogCore.v]), for [c = 1/ln 2] and [d = 1]
    ([log2]), or [c = 1/ln 10] and [d = log10(2)] ([log10])
    ([FastLogTables.v]), with [e dh] exact, and normalises the sum
    ([FastLogNorm.v]). [fast_log2_correct] and [fast_log10_correct] show
    that the result is within [2^-68] of [log2 x 2^-k] and [log10 x
    2^-k], with [1/2 < |h| < 2], as the rounding tests of [FastSign.v]
    need. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct FastRound FastLogTables
  FastLogCore FastLogNorm FastLogFin FastLogByProd FastExpErr.
From Inari Require DyExpRules.

Open Scope R_scope.

(** ** Helpers *)

(** A finite [f64] with value [0] is a zero, as in [FastLogPoly.v]. *)
Local Lemma fb_zero : forall x : f64, is_finite x = true -> B2R x = 0 -> exists s, x = B754_zero s.
Proof.
intros [s|s| |s m e Hb] F H; try discriminate F.
- exists s. reflexivity.
- exfalso. cbn [B2R] in H. apply eq_0_F2R in H. destruct s; simpl in H; discriminate H.
Qed.

(** [rn_err] of [FastExpErr.v] for a named result. *)
Local Lemma fb_rn :
  forall a v, a = RN v -> Rabs (a - v) <= / 9007199254740992 * Rabs v + bpow radix2 (-1075).
Proof.
intros a v ->. pose proof (rn_err v) as H.
assert (U : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
rewrite U in H. exact H.
Qed.

(** The triangle inequality for the seven terms of the error. *)
Local Lemma fb_tri7 :
  forall a1 a2 a3 a4 a5 a6 a7,
  Rabs (a1 + a2 + a3 + a4 - a5 - a6 - a7) <=
  Rabs a1 + Rabs a2 + Rabs a3 + Rabs a4 + Rabs a5 + Rabs a6 + Rabs a7.
Proof.
intros a1 a2 a3 a4 a5 a6 a7. unfold Rminus.
pose proof (Rabs_triang (a1 + a2 + a3 + a4 + - a5 + - a6) (- a7)).
pose proof (Rabs_triang (a1 + a2 + a3 + a4 + - a5) (- a6)).
pose proof (Rabs_triang (a1 + a2 + a3 + a4) (- a5)).
pose proof (Rabs_triang (a1 + a2 + a3) a4).
pose proof (Rabs_triang (a1 + a2) a3).
pose proof (Rabs_triang a1 a2).
rewrite !Rabs_Ropp in *. lra.
Qed.

(** [e d] is exact for [|e| <= 1074] and [d = D 2^p] with [|D| < 2^42],
    as [1074 2^42 < 2^53]. *)
Local Lemma fb_e_mul :
  forall e (d : f64) (Dm p : Z), (-1074 <= e <= 1074)%Z -> is_finite d = true ->
  B2R d = IZR Dm * bpow radix2 p -> (Z.abs Dm < 2 ^ 42)%Z -> (-1074 <= p)%Z ->
  Rabs (B2R d) <= 1 ->
  is_finite (mul (DyadicLog.of_i64 e) d) = true /\
  B2R (mul (DyadicLog.of_i64 e) d) = IZR e * B2R d.
Proof.
intros e d Dm p He Fd Ed HDm Hp Hd1.
assert (Ee : (Z.abs e < 2 ^ 53)%Z) by (change (2 ^ 53)%Z with 9007199254740992%Z; lia).
destruct (fl_of_i64 e Ee) as [Fef Vef].
pose proof fl_max as HM.
assert (Hea : Rabs (IZR e) <= 1074) by (rewrite <- abs_IZR; apply IZR_le; lia).
destruct (mul_below_max _ _ Fef Fd) as (FP & EP & _).
{ rewrite Vef, Rabs_mult.
  assert (Rabs (IZR e) * Rabs (B2R d) <= 1074 * 1)
    by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hea | exact Hd1]).
  lra. }
split; [exact FP|]. rewrite EP, Vef. apply round_generic; [typeclasses eauto|].
rewrite Ed.
replace (IZR e * (IZR Dm * bpow radix2 p)) with (F2R (Float radix2 (e * Dm) p))
  by (unfold F2R; cbn [Fnum Fexp]; rewrite mult_IZR; ring).
apply generic_format_FLT, (FLT_spec _ _ _ _ (Float radix2 (e * Dm) p));
  [reflexivity | | cbn [Fexp]; lia].
cbn [Fnum radix_val radix2]. rewrite Z.abs_mul.
change (2 ^ 42)%Z with 4398046511104%Z in HDm.
change (2 ^ 53)%Z with 9007199254740992%Z.
assert (Z.abs e <= 1074)%Z by lia.
nia.
Qed.

(** ** The generic step

    For a constant [c = ch + cl] within [2^-104] of [K] and [d = dh +
    dl] within [2^-100] of [K ln 2], the sum is [K ln x] within [4/5
    2^-69 |K ln x|]. With [D = ln x - e ln 2], [y - (s + w)] is [e (K ln
    2 - d) + K (D - a) + a (K - c) + (a c - p)] minus three roundings of
    the low sum. For [e = 0] it is the first four terms, the core's [3
    2^-71 K |D|] and less than [2^-99 |D|] from the rest, where [|y| = K
    |D|]. For [e <> 0], [|y| >= K (0.6931 |e| - 0.35)], and the rest is
    below [2^-90 |e|]. *)
Local Lemma fb_main :
  forall fma x (c d : Z * Z) (K : R) h l k,
  is_finite x = true -> 0 < B2R x ->
  is_finite (from_bits (fst c)) = true -> is_finite (from_bits (snd c)) = true ->
  is_finite (from_bits (fst d)) = true -> is_finite (from_bits (snd d)) = true ->
  Rabs (B2R (from_bits (fst c)) + B2R (from_bits (snd c)) - K) <= bpow radix2 (-104) ->
  Rabs (B2R (from_bits (fst d)) + B2R (from_bits (snd d)) - K * ln 2) <= bpow radix2 (-100) ->
  2 / 5 <= B2R (from_bits (fst c)) <= 1443 / 1000 ->
  B2R (from_bits (fst c)) <= 3 / 2 * B2R (from_bits (fst d)) ->
  1 / 4 <= B2R (from_bits (fst d)) <= 1 ->
  Rabs (B2R (from_bits (snd c))) <= bpow radix2 (-55) ->
  Rabs (B2R (from_bits (snd d))) <= bpow radix2 (-44) ->
  (forall e, (-1074 <= e <= 1074)%Z ->
     is_finite (mul (DyadicLog.of_i64 e) (from_bits (fst d))) = true /\
     B2R (mul (DyadicLog.of_i64 e) (from_bits (fst d))) = IZR e * B2R (from_bits (fst d))) ->
  (forall s,
     is_finite (Generic.two_prod_err fma (B754_zero s) (from_bits (fst c))
       (mul (B754_zero s) (from_bits (fst c)))) = true /\
     B2R (Generic.two_prod_err fma (B754_zero s) (from_bits (fst c))
       (mul (B754_zero s) (from_bits (fst c)))) = 0) ->
  DyadicLog.fast_log_by fma x c d = Some (h, l, k) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < Rabs (B2R h) < 2 /\ (-1021 <= k <= 1022)%Z /\
  Rabs (ln (B2R x) * K * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-68).
Proof.
intros fma x c d K h l k Fx Px Fch Fcl Fdh Fdl HK HG Hch Hcd Hdh Hcl Hdl Hed Hz E.
pose proof (ln_core_correct fma x Fx Px) as Hc.
pose proof (core_cases fma x Fx Px) as Hcc.
unfold DyadicLog.fast_log_by in E.
destruct (DyadicLog.ln_core fma x) as [[e ah] al].
destruct Hc as (Fah & Fal & Eah & He & HD & Hcore).
destruct Hcc as (HA & Hcc).
cbv beta iota zeta in E.
set (ch := from_bits (fst c)) in *.
set (cl := from_bits (snd c)) in *.
set (dh := from_bits (fst d)) in *.
set (dl := from_bits (snd d)) in *.
assert (He' : (-1074 <= e <= 1074)%Z) by lia.
destruct (Hed e He') as [FP VP].
clear Hed.
assert (Ee : (Z.abs e < 2 ^ 53)%Z) by (change (2 ^ 53)%Z with 9007199254740992%Z; lia).
destruct (fl_of_i64 e Ee) as [Fef Vef].
assert (Hah0 : B2R ah = 0 \/ bpow radix2 (-56) <= Rabs (B2R ah)).
{ destruct Hcc as [(_ & H0 & _) | (_ & H1)]; [left | right]; assumption. }
assert (Hch4 : / 4 <= B2R ch <= 2) by lra.
destruct (by_prod fma ah al ch cl Fah Fal Fch Fcl Eah Hah0 HA Hch4 Hcl Hz)
  as (Fph & Fpl & Eph & Hpl & Hprod).
clear Hah0 Hch4.
set (ef := DyadicLog.of_i64 e) in *.
set (P := mul ef dh) in *.
set (ph := mul ah ch) in *.
set (pl := add (Generic.two_prod_err fma ah ch ph) (add (mul ah cl) (mul al ch))) in *.
set (Q := mul ef dl) in *.
destruct (Fast.fast_two_sum P ph) as [s t] eqn:E1.
set (R := add pl Q) in *.
set (W := add t R) in *.
destruct (Fast.fast_two_sum s W) as [h0 l0] eqn:E2.
(* The numbers. *)
assert (B44 : bpow radix2 (-44) = / 17592186044416) by reflexivity.
assert (B50 : bpow radix2 (-50) = / 1125899906842624) by reflexivity.
assert (B54 : bpow radix2 (-54) = / 18014398509481984) by reflexivity.
assert (B55 : bpow radix2 (-55) = / 36028797018963968) by reflexivity.
assert (B56 : bpow radix2 (-56) = / 72057594037927936) by reflexivity.
assert (B69 : bpow radix2 (-69) = / 590295810358705651712) by reflexivity.
assert (B71 : bpow radix2 (-71) = / 2361183241434822606848) by reflexivity.
assert (B100 : bpow radix2 (-100) = / 1267650600228229401496703205376) by reflexivity.
assert (B104 : bpow radix2 (-104) = / 20282409603651670423947251286016) by reflexivity.
assert (B1070 : bpow radix2 (-1070) = 32 * bpow radix2 (-1075)).
{ replace (-1070)%Z with (5 + -1075)%Z by lia. rewrite bpow_plus. reflexivity. }
pose proof (bpow_gt_0 radix2 (-1075)) as T0.
assert (T1 : bpow radix2 (-1075) <=
  / 1606938044258990275541962092341162602522202993782792835301376).
{ assert (B200 : bpow radix2 (-200) =
    / 1606938044258990275541962092341162602522202993782792835301376) by reflexivity.
  rewrite <- B200. apply bpow_le. lia. }
rewrite B44 in Hdl. rewrite B50, B1070 in Hpl. rewrite B100, B1070 in Hprod.
rewrite B55 in Hcl. rewrite B104 in HK. rewrite B100 in HG. rewrite B71 in Hcore.
set (u := bpow radix2 (-1075)) in *.
apply Rabs_le_inv in HK. apply Rabs_le_inv in HG.
pose proof (Rabs_le_inv _ _ Hcl) as Hcl'.
assert (HK1 : 39 / 100 <= K <= 14431 / 10000) by lra.
pose proof DyExpRules.ln2_bounds as L2.
pose proof (fl_y0 x Fx Px) as Hy0.
set (D := ln (B2R x) - IZR e * ln 2) in *.
(* [|y| = K |ln x|], [|y| <= 1100], and [y = 0] or [|y| >= 2^-56]. *)
assert (HyZ : Rabs (ln (B2R x) * K) = Rabs (ln (B2R x)) * K)
  by (rewrite Rabs_mult, (Rabs_pos_eq K) by lra; reflexivity).
assert (Hea : Rabs (IZR e) <= 1074) by (rewrite <- abs_IZR; apply IZR_le; lia).
assert (HeL : Rabs (IZR e * ln 2) = Rabs (IZR e) * ln 2)
  by (rewrite Rabs_mult, (Rabs_pos_eq (ln 2)) by lra; reflexivity).
pose proof (fl_tri (ln (B2R x)) (IZR e * ln 2) D ltac:(unfold D; ring)) as TZ.
pose proof (fl_tri (IZR e * ln 2) (ln (B2R x)) (- D) ltac:(unfold D; ring)) as TZ2.
rewrite Rabs_Ropp in TZ2. rewrite HeL in TZ, TZ2.
assert (YL : Rabs (IZR e) * (6931 / 10000) <= Rabs (IZR e) * ln 2)
  by (apply Rmult_le_compat_l; [apply Rabs_pos | lra]).
assert (YL2 : Rabs (IZR e) * ln 2 <= 1074 * (6932 / 10000))
  by (apply Rmult_le_compat; [apply Rabs_pos | lra | exact Hea | lra]).
assert (Hy1100 : Rabs (ln (B2R x) * K) <= 1100).
{ rewrite HyZ.
  assert (Rabs (ln (B2R x)) * K <= (1074 * (6932 / 10000) + 7 / 20) * (14431 / 10000))
    by (apply Rmult_le_compat; [apply Rabs_pos | lra | lra | lra]).
  lra. }
assert (Hy56 : ln (B2R x) * K = 0 \/ bpow radix2 (-56) <= Rabs (ln (B2R x) * K)).
{ destruct Hy0 as [Y0 | Y0]; [left; rewrite Y0; ring | right].
  rewrite HyZ, B56. rewrite B54 in Y0.
  assert (/ 18014398509481984 * (39 / 100) <= Rabs (ln (B2R x)) * K)
    by (apply Rmult_le_compat; [lra | lra | exact Y0 | lra]).
  lra. }
(* The core: [|a_h + a_l| <= 1.0001 |D|] and [|a_h| <= 1.0001 |a_h + a_l| + u]. *)
pose proof (fl_tri (B2R ah + B2R al) D (- (D - (B2R ah + B2R al))) ltac:(ring)) as Ta.
rewrite Rabs_Ropp in Ta.
pose proof (fb_rn _ _ Eah) as Hal. change (bpow radix2 (-1075)) with u in Hal.
replace (B2R ah - (B2R ah + B2R al)) with (- B2R al) in Hal by ring.
rewrite Rabs_Ropp in Hal.
pose proof (fl_tri (B2R ah) (B2R ah + B2R al) (- B2R al) ltac:(ring)) as Tb.
rewrite Rabs_Ropp in Tb.
assert (HS : Rabs (B2R ah + B2R al) <= 10001 / 10000 * Rabs D) by lra.
assert (HSA : Rabs (B2R ah) <= 10001 / 10000 * Rabs (B2R ah + B2R al) + u).
{ pose proof (Rabs_pos (B2R ah + B2R al)). lra. }
clear Ta Tb Hal.
pose proof (fb_rn _ _ Eph) as Hph. change (bpow radix2 (-1075)) with u in Hph.
pose proof fl_max as HM.
destruct (Z.eq_dec e 0) as [E0 | En0].
- (* [e = 0]: [s + w = ph + pl] exactly, and [y = K D]. *)
  assert (Ie : IZR e = 0) by (rewrite E0; reflexivity).
  rewrite Ie, Rmult_0_l in VP.
  assert (Ly : ln (B2R x) = D) by (unfold D; rewrite Ie; ring).
  assert (Hpc : Rabs (B2R ah * B2R ch) <= 3 / 4).
  { rewrite Rabs_mult, (Rabs_pos_eq (B2R ch)) by lra.
    assert (Rabs (B2R ah) * B2R ch <= / 2 * B2R ch) by (apply Rmult_le_compat_r; lra).
    lra. }
  assert (Hph1 : Rabs (B2R ph) <= 1).
  { pose proof (fl_tri (B2R ph) (B2R ah * B2R ch) (B2R ph - B2R ah * B2R ch) ltac:(ring)).
    lra. }
  assert (Fz : Rabs (B2R ph) <= Rabs (B2R P) \/ B2R P = 0) by (right; exact VP).
  assert (Hs : Rabs (B2R P + B2R ph) <= 2048) by (rewrite VP, Rplus_0_l; lra).
  destruct (fts_exact P ph s t FP Fph Fz Hs E1) as (Fs & Ft & Es & Est).
  rewrite VP, Rplus_0_l in Es, Est.
  rewrite round_generic in Es by first [apply generic_format_B2R | typeclasses eauto].
  assert (Et : B2R t = 0) by lra.
  destruct (mul_below_max ef dl Fef Fdl) as (FQ & EQ & _).
  { rewrite Vef, Ie, Rmult_0_l, Rabs_R0. lra. }
  fold Q in FQ, EQ.
  rewrite Vef, Ie, Rmult_0_l, round_0 in EQ by typeclasses eauto.
  destruct (add_below_max pl Q Fpl FQ) as (FR & ER & _).
  { rewrite EQ, Rplus_0_r. lra. }
  fold R in FR, ER.
  rewrite EQ, Rplus_0_r, round_generic in ER
    by first [apply generic_format_B2R | typeclasses eauto].
  destruct (add_below_max t R Ft FR) as (FW & EW & _).
  { rewrite Et, ER, Rplus_0_l. lra. }
  fold W in FW, EW.
  rewrite Et, ER, Rplus_0_l, round_generic in EW
    by first [apply generic_format_B2R | typeclasses eauto].
  destruct Hcc as [(D0 & A0 & L0) | (HX & HA56)].
  + (* [x = 1]: [y = 0], and [ph = pl = 0]. *)
    assert (Hph0 : B2R ph = 0).
    { rewrite Eph, A0, Rmult_0_l. apply round_0. typeclasses eauto. }
    destruct (fb_zero ah Fah A0) as [sa Ea].
    destruct (Hz sa) as [FT ET]. rewrite <- Ea in FT, ET. fold ph in FT, ET.
    destruct (mul_below_max ah cl Fah Fcl) as (FM1 & EM1 & _).
    { rewrite A0, Rmult_0_l, Rabs_R0. lra. }
    rewrite A0, Rmult_0_l, round_0 in EM1 by typeclasses eauto.
    destruct (mul_below_max al ch Fal Fch) as (FM2 & EM2 & _).
    { rewrite L0, Rmult_0_l, Rabs_R0. lra. }
    rewrite L0, Rmult_0_l, round_0 in EM2 by typeclasses eauto.
    destruct (add_below_max _ _ FM1 FM2) as (FM3 & EM3 & _).
    { rewrite EM1, EM2, Rplus_0_l, Rabs_R0. lra. }
    rewrite EM1, EM2, Rplus_0_l, round_0 in EM3 by typeclasses eauto.
    destruct (add_below_max _ _ FT FM3) as (FM4 & EM4 & _).
    { rewrite ET, EM3, Rplus_0_l, Rabs_R0. lra. }
    rewrite ET, EM3, Rplus_0_l, round_0 in EM4 by typeclasses eauto.
    fold pl in EM4.
    assert (Y0 : ln (B2R x) * K = 0) by (rewrite Ly, D0; ring).
    apply (fl_finish s W h0 l0 h l k (ln (B2R x) * K) Fs FW);
      [ | exact Hy1100 | exact Hy56 | | exact E2 | exact E].
    * right. rewrite Es. exact Hph0.
    * rewrite Y0, Es, EW, Hph0, EM4.
      replace (0 - (0 + 0)) with 0 by ring. rewrite Rabs_R0, Rmult_0_r. lra.
  + (* [x <> 1]: [|D| >= 2^-54] and [|a_h| >= 2^-56]. *)
    rewrite B54 in HX. rewrite B56 in HA56.
    assert (HKX : 39 / 100 * Rabs D <= K * Rabs D)
      by (apply Rmult_le_compat_r; [apply Rabs_pos | lra]).
    apply (fl_finish s W h0 l0 h l k (ln (B2R x) * K) Fs FW);
      [ | exact Hy1100 | exact Hy56 | | exact E2 | exact E].
    * (* [|pl| <= |ph|]. *)
      left. rewrite Es, EW.
      assert (Hpc2 : 2 / 5 * Rabs (B2R ah) <= Rabs (B2R ah * B2R ch)).
      { rewrite Rabs_mult, (Rabs_pos_eq (B2R ch)) by lra.
        assert (Rabs (B2R ah) * (2 / 5) <= Rabs (B2R ah) * B2R ch)
          by (apply Rmult_le_compat_l; [apply Rabs_pos | lra]).
        lra. }
      pose proof (fl_tri (B2R ah * B2R ch) (B2R ph) (- (B2R ph - B2R ah * B2R ch))
        ltac:(ring)) as Tph.
      rewrite Rabs_Ropp in Tph.
      lra.
    * (* The error is the sum of three terms. *)
      rewrite Es, EW, B69, HyZ, Ly.
      assert (Id : D * K - (B2R ph + B2R pl) =
        K * (D - (B2R ah + B2R al)) + (B2R ah + B2R al) * (K - (B2R ch + B2R cl)) -
        (B2R ph + B2R pl - (B2R ah + B2R al) * (B2R ch + B2R cl))) by ring.
      rewrite Id.
      pose proof (fl_tri
        (K * (D - (B2R ah + B2R al)) + (B2R ah + B2R al) * (K - (B2R ch + B2R cl)) -
         (B2R ph + B2R pl - (B2R ah + B2R al) * (B2R ch + B2R cl)))
        (K * (D - (B2R ah + B2R al)) + (B2R ah + B2R al) * (K - (B2R ch + B2R cl)))
        (- (B2R ph + B2R pl - (B2R ah + B2R al) * (B2R ch + B2R cl))) ltac:(ring)) as S1.
      pose proof (fl_tri
        (K * (D - (B2R ah + B2R al)) + (B2R ah + B2R al) * (K - (B2R ch + B2R cl)))
        (K * (D - (B2R ah + B2R al))) ((B2R ah + B2R al) * (K - (B2R ch + B2R cl))) eq_refl)
        as S2.
      rewrite Rabs_Ropp in S1.
      assert (B2 : Rabs (K * (D - (B2R ah + B2R al))) <=
        K * (3 * / 2361183241434822606848 * Rabs D)).
      { rewrite Rabs_mult, (Rabs_pos_eq K) by lra.
        apply Rmult_le_compat_l; [lra | exact Hcore]. }
      assert (B3 : Rabs ((B2R ah + B2R al) * (K - (B2R ch + B2R cl))) <=
        Rabs (B2R ah + B2R al) * / 20282409603651670423947251286016).
      { rewrite Rabs_mult. apply Rmult_le_compat_l; [apply Rabs_pos |]. apply Rabs_le. lra. }
      lra.
- (* [e <> 0]: [|e dh| >= dh > |ph|]. *)
  assert (Y1 : 1 <= Rabs (IZR e)) by (rewrite <- abs_IZR; apply IZR_le; lia).
  assert (HP : Rabs (B2R P) = Rabs (IZR e) * B2R dh)
    by (rewrite VP, Rabs_mult, (Rabs_pos_eq (B2R dh)) by lra; reflexivity).
  assert (HP1 : 1 * B2R dh <= Rabs (IZR e) * B2R dh) by (apply Rmult_le_compat_r; lra).
  assert (HP2 : Rabs (IZR e) * B2R dh <= Rabs (IZR e) * 1)
    by (apply Rmult_le_compat_l; [apply Rabs_pos | lra]).
  assert (Hpc : Rabs (B2R ah * B2R ch) <= 3 / 4 * B2R dh).
  { rewrite Rabs_mult, (Rabs_pos_eq (B2R ch)) by lra.
    assert (Rabs (B2R ah) * B2R ch <= / 2 * B2R ch) by (apply Rmult_le_compat_r; lra).
    lra. }
  assert (Hph1 : Rabs (B2R ph) <= 77 / 100 * B2R dh).
  { pose proof (fl_tri (B2R ph) (B2R ah * B2R ch) (B2R ph - B2R ah * B2R ch) ltac:(ring)).
    lra. }
  assert (Fz : Rabs (B2R ph) <= Rabs (B2R P) \/ B2R P = 0) by (left; lra).
  pose proof (fl_tri (B2R P + B2R ph) (B2R P) (B2R ph) ltac:(ring)) as Tp.
  pose proof (fl_tri (B2R P) (B2R P + B2R ph) (- B2R ph) ltac:(ring)) as Tp2.
  rewrite Rabs_Ropp in Tp2.
  assert (Hs : Rabs (B2R P + B2R ph) <= 2048) by lra.
  destruct (fts_exact P ph s t FP Fph Fz Hs E1) as (Fs & Ft & Es & Est).
  (* [t = (P + ph) - RN(P + ph)]. *)
  pose proof (fb_rn _ _ Es) as Hst. change (bpow radix2 (-1075)) with u in Hst.
  replace (B2R s - (B2R P + B2R ph)) with (- B2R t) in Hst by lra.
  rewrite Rabs_Ropp in Hst.
  assert (Ht : Rabs (B2R t) <= / 4503599627370496 * Rabs (IZR e)) by lra.
  assert (Hs1 : / 20 <= Rabs (B2R s)).
  { pose proof (fl_tri (B2R P + B2R ph) (B2R s) (B2R t) ltac:(lra)). lra. }
  (* [Q = RN(e dl)]. *)
  assert (Hedl : Rabs (IZR e * B2R dl) <= Rabs (IZR e) * / 17592186044416)
    by (rewrite Rabs_mult; apply Rmult_le_compat_l; [apply Rabs_pos | exact Hdl]).
  destruct (mul_below_max ef dl Fef Fdl) as (FQ & EQ & _).
  { rewrite Vef. lra. }
  fold Q in FQ, EQ. rewrite Vef in EQ.
  pose proof (fb_rn _ _ EQ) as HQ. change (bpow radix2 (-1075)) with u in HQ.
  pose proof (fl_tri (B2R Q) (IZR e * B2R dl) (B2R Q - IZR e * B2R dl) ltac:(ring)) as TQ.
  assert (HQ1 : Rabs (B2R Q) <= / 8796093022208 * Rabs (IZR e)) by lra.
  (* [R = RN(pl + Q)]. *)
  pose proof (fl_tri (B2R pl + B2R Q) (B2R pl) (B2R Q) ltac:(ring)) as TpQ.
  assert (HpQ : Rabs (B2R pl + B2R Q) <= / 4398046511104 * Rabs (IZR e)) by lra.
  destruct (add_below_max pl Q Fpl FQ) as (FR & ER & _).
  { lra. }
  fold R in FR, ER.
  pose proof (fb_rn _ _ ER) as HR. change (bpow radix2 (-1075)) with u in HR.
  pose proof (fl_tri (B2R R) (B2R pl + B2R Q) (B2R R - (B2R pl + B2R Q)) ltac:(ring)) as TR.
  assert (HR1 : Rabs (B2R R) <= / 2199023255552 * Rabs (IZR e)) by lra.
  (* [W = RN(t + R)]. *)
  pose proof (fl_tri (B2R t + B2R R) (B2R t) (B2R R) ltac:(ring)) as TtR.
  assert (HtR : Rabs (B2R t + B2R R) <= / 1099511627776 * Rabs (IZR e)) by lra.
  destruct (add_below_max t R Ft FR) as (FW & EW & _).
  { lra. }
  fold W in FW, EW.
  pose proof (fb_rn _ _ EW) as HW. change (bpow radix2 (-1075)) with u in HW.
  pose proof (fl_tri (B2R W) (B2R t + B2R R) (B2R W - (B2R t + B2R R)) ltac:(ring)) as TW.
  apply (fl_finish s W h0 l0 h l k (ln (B2R x) * K) Fs FW);
    [ | exact Hy1100 | exact Hy56 | | exact E2 | exact E].
  + left. lra.
  + (* The error is the sum of seven terms. *)
    assert (Es' : B2R s = IZR e * B2R dh + B2R ph - B2R t) by (rewrite VP in Est; lra).
    assert (Id : ln (B2R x) * K - (B2R s + B2R W) =
      IZR e * (K * ln 2 - (B2R dh + B2R dl)) + K * (D - (B2R ah + B2R al)) +
      (B2R ah + B2R al) * (K - (B2R ch + B2R cl)) +
      ((B2R ah + B2R al) * (B2R ch + B2R cl) - (B2R ph + B2R pl)) -
      (B2R Q - IZR e * B2R dl) - (B2R R - (B2R pl + B2R Q)) - (B2R W - (B2R t + B2R R))).
    { rewrite Es'. unfold D. ring. }
    rewrite Id, B69, HyZ.
    eapply Rle_trans; [apply fb_tri7 |].
    assert (B1 : Rabs (IZR e * (K * ln 2 - (B2R dh + B2R dl))) <=
      Rabs (IZR e) * / 1267650600228229401496703205376).
    { rewrite Rabs_mult. apply Rmult_le_compat_l; [apply Rabs_pos |]. apply Rabs_le. lra. }
    assert (B2 : Rabs (K * (D - (B2R ah + B2R al))) <=
      K * (3 * / 2361183241434822606848 * Rabs D)).
    { rewrite Rabs_mult, (Rabs_pos_eq K) by lra.
      apply Rmult_le_compat_l; [lra | exact Hcore]. }
    assert (B3 : Rabs ((B2R ah + B2R al) * (K - (B2R ch + B2R cl))) <=
      Rabs (B2R ah + B2R al) * / 20282409603651670423947251286016).
    { rewrite Rabs_mult. apply Rmult_le_compat_l; [apply Rabs_pos |]. apply Rabs_le. lra. }
    assert (B4 : Rabs ((B2R ah + B2R al) * (B2R ch + B2R cl) - (B2R ph + B2R pl)) <=
      / 1267650600228229401496703205376 * Rabs (B2R ah) + 32 * u)
      by (rewrite Rabs_minus_sym; exact Hprod).
    (* The six terms other than the core's are below [2^-90 |e|]. *)
    assert (Hrest :
      Rabs (IZR e * (K * ln 2 - (B2R dh + B2R dl))) +
      Rabs ((B2R ah + B2R al) * (K - (B2R ch + B2R cl))) +
      Rabs ((B2R ah + B2R al) * (B2R ch + B2R cl) - (B2R ph + B2R pl)) +
      Rabs (B2R Q - IZR e * B2R dl) + Rabs (B2R R - (B2R pl + B2R Q)) +
      Rabs (B2R W - (B2R t + B2R R)) <= / 1237940039285380274899124224 * Rabs (IZR e)).
    { pose proof (Rabs_pos (B2R ah + B2R al)). lra. }
    (* [|y| >= K (0.6931 |e| - |D|)], [|D| <= 7/20] and [|e| >= 1]. *)
    assert (HKZ : K * (6931 / 10000 * Rabs (IZR e) - Rabs D) <= K * Rabs (ln (B2R x)))
      by (apply Rmult_le_compat_l; lra).
    assert (HKD : K * Rabs D <= K * (7 / 20)) by (apply Rmult_le_compat_l; lra).
    assert (HKY : K * 1 <= K * Rabs (IZR e)) by (apply Rmult_le_compat_l; lra).
    assert (HKY2 : 39 / 100 * Rabs (IZR e) <= K * Rabs (IZR e))
      by (apply Rmult_le_compat_r; [apply Rabs_pos | lra]).
    pose proof (Rabs_pos (IZR e)) as Y0.
    clear - B2 Hrest HKZ HKD HKY HKY2 Y0.
    lra.
Qed.

(** ** The constants *)

(** [B2R] of a constant from its [B2SF], as [FastLogLn.v] does for [LN2L]. *)
Local Lemma fb_val :
  forall b m e, B2SF (from_bits b) = SpecFloat.S754_finite false m e ->
  B2R (from_bits b) = IZR (Zpos m) * bpow radix2 e.
Proof. intros b m e H. rewrite <- (SF2R_B2SF _ _ (from_bits b)), H. reflexivity. Qed.

(** The error term of the product of a zero and [c_h] is a zero, by
    computation on the [f64]s only. *)
Local Ltac fb_zero_tpe :=
  lazymatch goal with
  | |- context [Generic.two_prod_err ?f ?a ?b ?c] =>
    let v := eval vm_compute in (Generic.two_prod_err f a b c) in
    replace (Generic.two_prod_err f a b c) with v by (vm_compute; reflexivity)
  end;
  split; reflexivity.

(** ** The theorems *)

Theorem fast_log2_correct :
  forall fma x h l k,
  is_finite x = true -> 0 < B2R x ->
  DyadicLog.fast_log_by fma x DyadicLog.C2 DyadicLog.ONE = Some (h, l, k) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < Rabs (B2R h) < 2 /\ (-1021 <= k <= 1022)%Z /\
  Rabs (Rlog2 (B2R x) * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-68).
Proof.
intros fma x h l k Fx Px E.
unfold Rlog2, Rlog, Rdiv.
pose proof DyExpRules.ln2_bounds as L2.
assert (B52 : bpow radix2 (-52) = / 4503599627370496) by reflexivity.
assert (B55 : bpow radix2 (-55) = / 36028797018963968) by reflexivity.
assert (B108 : bpow radix2 (-108) = / 324518553658426726783156020576256) by reflexivity.
pose proof (fb_val (fst DyadicLog.C2) 6497320848556798 (-52) ltac:(vm_compute; reflexivity))
  as Vch.
pose proof (fb_val (snd DyadicLog.C2) 6605663993728292 (-108) ltac:(vm_compute; reflexivity))
  as Vcl.
pose proof (fb_val (fst DyadicLog.ONE) 4503599627370496 (-52) ltac:(vm_compute; reflexivity))
  as Vdh.
assert (Vdl : B2R (from_bits (snd DyadicLog.ONE)) = 0).
{ replace (from_bits (snd DyadicLog.ONE)) with (@B754_zero 53 1024 false)
    by (vm_compute; reflexivity).
  reflexivity. }
rewrite B52 in Vch, Vdh. rewrite B108 in Vcl.
assert (Vdh1 : B2R (from_bits (fst DyadicLog.ONE)) = 1) by lra.
refine (fb_main fma x DyadicLog.C2 DyadicLog.ONE (/ ln 2) h l k Fx Px _ _ _ _ c2_correct
  _ _ _ _ _ _ _ _ E).
1-4: vm_compute; reflexivity.
- replace (B2R (from_bits (fst DyadicLog.ONE)) + B2R (from_bits (snd DyadicLog.ONE)) -
    / ln 2 * ln 2) with 0 by (rewrite Vdh1, Vdl; field; lra).
  rewrite Rabs_R0. apply bpow_ge_0.
- rewrite Vch. lra.
- rewrite Vch, Vdh1. lra.
- rewrite Vdh1. lra.
- rewrite Vcl, B55, Rabs_pos_eq by lra. lra.
- rewrite Vdl, Rabs_R0. apply bpow_ge_0.
- intros e He. apply (fb_e_mul e _ 1 0 He).
  + vm_compute. reflexivity.
  + rewrite Vdh1. change (bpow radix2 0) with 1. ring.
  + reflexivity.
  + lia.
  + rewrite Vdh1, Rabs_R1. lra.
- intros s. destruct fma, s; fb_zero_tpe.
Qed.

Theorem fast_log10_correct :
  forall fma x h l k,
  is_finite x = true -> 0 < B2R x ->
  DyadicLog.fast_log_by fma x DyadicLog.C10 DyadicLog.LG2 = Some (h, l, k) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < Rabs (B2R h) < 2 /\ (-1021 <= k <= 1022)%Z /\
  Rabs (Rlog10 (B2R x) * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-68).
Proof.
intros fma x h l k Fx Px E.
unfold Rlog10, Rlog, Rdiv.
assert (B43 : bpow radix2 (-43) = / 8796093022208) by reflexivity.
assert (B44 : bpow radix2 (-44) = / 17592186044416) by reflexivity.
assert (B54 : bpow radix2 (-54) = / 18014398509481984) by reflexivity.
assert (B55 : bpow radix2 (-55) = / 36028797018963968) by reflexivity.
assert (B98 : bpow radix2 (-98) = / 316912650057057350374175801344) by reflexivity.
assert (B109 : bpow radix2 (-109) = / 649037107316853453566312041152512) by reflexivity.
pose proof (fb_val (fst DyadicLog.C10) 7823553867474190 (-54) ltac:(vm_compute; reflexivity))
  as Vch.
pose proof (fb_val (snd DyadicLog.C10) 7128502086859475 (-109) ltac:(vm_compute; reflexivity))
  as Vcl.
pose proof lg2h_exact as Vdh.
pose proof (fb_val (snd DyadicLog.LG2) 8988718531785560 (-98) ltac:(vm_compute; reflexivity))
  as Vdl.
rewrite B54 in Vch. rewrite B109 in Vcl. rewrite B43 in Vdh. rewrite B98 in Vdl.
refine (fb_main fma x DyadicLog.C10 DyadicLog.LG2 (/ ln 10) h l k Fx Px _ _ _ _ c10_correct
  _ _ _ _ _ _ _ _ E).
1-4: vm_compute; reflexivity.
- replace (/ ln 10 * ln 2) with (ln 2 / ln 10) by (unfold Rdiv; ring).
  exact lg2_split_correct.
- rewrite Vch. lra.
- rewrite Vch, Vdh. lra.
- rewrite Vdh. lra.
- rewrite Vcl, B55, Rabs_pos_eq by lra. lra.
- rewrite Vdl, B44, Rabs_pos_eq by lra. lra.
- intros e He. apply (fb_e_mul e _ 2647887844335 (-43) He).
  + vm_compute. reflexivity.
  + exact lg2h_exact.
  + reflexivity.
  + lia.
  + rewrite Vdh, Rabs_pos_eq by lra. lra.
- intros s. destruct fma, s; fb_zero_tpe.
Qed.
