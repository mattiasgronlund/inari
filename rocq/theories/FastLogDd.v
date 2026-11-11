(** * ln of a double-double, before the rounding

    [DyadicLog.fast_ln_dd] of [Model.v] adds [e0 ln 2] and [xl / xh] to the
    core of [xh] ([FastLogCore.v]), since
    [ln(xh + xl) = ln xh + ln(1 + xl / xh)] and [ln(1 + d)] is [d] within
    [d^2 <= 2^-102] for [|d| <= 2^-51]. [fast_ln_dd_correct] shows that the
    result is within [2^-68] of [y 2^-k] for a [y] that the argument
    approximates, with [1/2 < |h| < 2], as the rounding tests of [FastSign.v]
    need.

    In [fast_ln_dd], [e + e0 <= 1025] follows from [xh 2^e0 <= 2^1025], so
    that [(e + e0) LN2H] is exact ([FastLogLn.fl_e_ln2h]). For [e + e0 = 0],
    [h + l] is [a_h + RN(a_l + RN(xl / xh))], and [|y| >= 2^-20] makes the
    absolute errors of [xl / xh] relative. For [e + e0 <> 0], [|y| >= ln 2 -
    7/20 - 2^-50 > 0.343], as in [FastLogLn.v], and the two new roundings
    (of [xl / xh] and of its sum with [(e + e0) LN2L]) are below [2^-85]
    each. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct FastRound FastLogTables
  FastLogTaylor FastLogPoly FastLogCore FastLogNorm FastLogFin FastExpErr.
From Inari Require FastLogLn FastDiv.

Open Scope R_scope.

(** ** Helpers *)

Local Lemma ld_tri5 :
  forall a1 a2 a3 a4 a5,
  Rabs (a1 + a2 + a3 + a4 + a5) <= Rabs a1 + Rabs a2 + Rabs a3 + Rabs a4 + Rabs a5.
Proof.
intros.
pose proof (Rabs_triang a1 a2).
pose proof (Rabs_triang (a1 + a2) a3).
pose proof (Rabs_triang (a1 + a2 + a3) a4).
pose proof (Rabs_triang (a1 + a2 + a3 + a4) a5).
lra.
Qed.

Local Lemma ld_tri9 :
  forall a1 a2 a3 a4 a5 a6 a7 a8 a9,
  Rabs (a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9) <=
  Rabs a1 + Rabs a2 + Rabs a3 + Rabs a4 + Rabs a5 + Rabs a6 + Rabs a7 + Rabs a8 + Rabs a9.
Proof.
intros.
pose proof (ld_tri5 a1 a2 a3 a4 a5).
pose proof (Rabs_triang (a1 + a2 + a3 + a4 + a5) a6).
pose proof (Rabs_triang (a1 + a2 + a3 + a4 + a5 + a6) a7).
pose proof (Rabs_triang (a1 + a2 + a3 + a4 + a5 + a6 + a7) a8).
pose proof (Rabs_triang (a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8) a9).
lra.
Qed.

(** [ln(1 + d)] is [d] within [d^2 / (2 (1 - |d|)) <= d^2]
    ([log1p_taylor] of degree 1). *)
Local Lemma ld_log1p :
  forall d, Rabs d <= bpow radix2 (-51) -> Rabs (ln (1 + d) - d) <= bpow radix2 (-102).
Proof.
intros d Hd.
assert (B51 : bpow radix2 (-51) = / 2251799813685248) by reflexivity.
assert (B102 : bpow radix2 (-102) = / 5070602400912917605986812821504) by reflexivity.
rewrite B51 in Hd. rewrite B102.
pose proof (Rabs_pos d) as D0.
pose proof (log1p_taylor 1 d ltac:(lra)) as HT.
replace (log1p_sum 1 d) with d in HT by (cbn [log1p_sum]; simpl; field).
replace (INR 2) with 2 in HT by (simpl; ring).
eapply Rle_trans; [exact HT|].
assert (Hq : Rabs d ^ 2 <= / 5070602400912917605986812821504) by nra.
apply Rle_trans with (Rabs d ^ 2); [|exact Hq].
unfold Rdiv. rewrite <- (Rmult_1_r (Rabs d ^ 2)) at 2.
apply Rmult_le_compat_l; [apply pow_le, D0 |].
rewrite <- Rinv_1. apply Rinv_le_contravar; lra.
Qed.

(** [ln 2^n = n ln 2]. *)
Local Lemma ld_ln_bpow : forall n, ln (bpow radix2 n) = IZR n * ln 2.
Proof. intros n. rewrite bpow_exp, ln_exp. reflexivity. Qed.

(** ** [fast_ln_dd] *)

Theorem fast_ln_dd_correct :
  forall fma xh xl e0 y h l k,
  is_finite xh = true -> is_finite xl = true -> 0 < B2R xh ->
  Rabs (B2R xl) <= bpow radix2 (-51) * B2R xh -> (0 <= e0 <= 64)%Z ->
  B2R xh * bpow radix2 e0 <= bpow radix2 1025 -> bpow radix2 (-20) <= Rabs y ->
  Rabs (y - (IZR e0 * ln 2 + ln (B2R xh + B2R xl))) <= bpow radix2 (-80) * Rabs y ->
  DyadicLog.fast_ln_dd fma xh xl e0 = Some (h, l, k) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < Rabs (B2R h) < 2 /\ (-1021 <= k <= 1022)%Z /\
  Rabs (y * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-68).
Proof.
intros fma xh xl e0 y h l k Fxh Fxl Pxh Hxl He0 Hmax Hy20 Hy E.
pose proof (ln_core_correct fma xh Fxh Pxh) as Hc.
unfold DyadicLog.fast_ln_dd in E.
destruct (DyadicLog.ln_core fma xh) as [[e ah] al].
destruct Hc as (Fah & Fal & Eah & He & HD & Hcore).
cbv beta iota zeta in E.
assert (FLL : is_finite (from_bits DyadicLog.LN2L) = true) by (vm_compute; reflexivity).
pose proof ln2h_exact as VH. pose proof FastLogLn.fl_ln2l as VL. pose proof ln2_split_correct as Hln2.
(* The numbers. *)
assert (U : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
assert (B20 : bpow radix2 (-20) = / 1048576) by reflexivity.
assert (B42 : bpow radix2 (-42) = / 4398046511104) by reflexivity.
assert (B51 : bpow radix2 (-51) = / 2251799813685248) by reflexivity.
assert (B56 : bpow radix2 (-56) = / 72057594037927936) by reflexivity.
assert (B69 : bpow radix2 (-69) = / 590295810358705651712) by reflexivity.
assert (B71 : bpow radix2 (-71) = / 2361183241434822606848) by reflexivity.
assert (B80 : bpow radix2 (-80) = / 1208925819614629174706176) by reflexivity.
assert (B97 : bpow radix2 (-97) = / 158456325028528675187087900672) by reflexivity.
assert (B100 : bpow radix2 (-100) = / 1267650600228229401496703205376) by reflexivity.
assert (B102 : bpow radix2 (-102) = / 5070602400912917605986812821504) by reflexivity.
pose proof (bpow_gt_0 radix2 (-1075)) as T0.
assert (T1 : bpow radix2 (-1075) <= bpow radix2 (-100)) by (apply bpow_le; lia).
rewrite B42 in VH. rewrite B97 in VL. rewrite B100 in Hln2, T1. rewrite B71 in Hcore.
apply Rabs_le_inv in Hln2.
pose proof fl_max as HM.
assert (L2 : 6931 / 10000 <= ln 2 <= 6932 / 10000) by lra.
(* [e + e0 <= 1025], from [ln xh + e0 ln 2 <= 1025 ln 2] and [|ln xh - e ln 2| <= 7/20]. *)
assert (Hln_max : ln (B2R xh) + IZR e0 * ln 2 <= 1025 * ln 2).
{ assert (P0 : 0 < B2R xh * bpow radix2 e0) by (apply Rmult_lt_0_compat; [lra | apply bpow_gt_0]).
  pose proof (FastLogCore.lc_ln_le _ _ P0 Hmax) as Lm.
  rewrite ln_mult, !ld_ln_bpow in Lm by (try lra; apply bpow_gt_0).
  exact Lm. }
assert (Hee : (e + e0 <= 1025)%Z).
{ destruct (Z_le_gt_dec (e + e0) 1025) as [H|H]; [exact H | exfalso].
  assert (I : 1026 <= IZR e + IZR e0) by (rewrite <- plus_IZR; apply IZR_le; lia).
  assert (M : 1026 * ln 2 <= IZR e * ln 2 + IZR e0 * ln 2).
  { rewrite <- Rmult_plus_distr_r. apply Rmult_le_compat_r; lra. }
  pose proof (Rabs_le_inv _ _ HD) as HD'. lra. }
assert (Hn : (-1074 <= e + e0 <= 1074)%Z) by lia.
destruct (FastLogLn.fl_e_ln2h (e + e0) Hn) as [FP VP].
assert (En : (Z.abs (e + e0) < 2 ^ 53)%Z) by (change (2 ^ 53)%Z with 9007199254740992%Z; lia).
destruct (fl_of_i64 (e + e0) En) as [Fef Vef].
assert (Hea : Rabs (IZR (e + e0)) <= 1074) by (rewrite <- abs_IZR; apply IZR_le; lia).
(* [d = xl / xh], [|d| <= 2^-51], and its rounding [dl]. *)
assert (Hd : Rabs (B2R xl / B2R xh) <= / 2251799813685248).
{ unfold Rdiv. rewrite Rabs_mult, Rabs_inv, (Rabs_pos_eq (B2R xh)) by lra.
  apply Rmult_le_reg_r with (B2R xh); [lra|].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. rewrite <- B51. exact Hxl. }
destruct (FastDiv.div_e xl xh Fxl Fxh (Rgt_not_eq _ _ Pxh) ltac:(lra)) as [Fdl Edl].
pose proof (rn_err (B2R xl / B2R xh)) as Hdl. rewrite <- Edl, U in Hdl.
assert (Hsplit : ln (B2R xh + B2R xl) = ln (B2R xh) + ln (1 + B2R xl / B2R xh)).
{ pose proof (Rabs_le_inv _ _ Hd).
  rewrite <- ln_mult by lra. f_equal. field. lra. }
rewrite Hsplit in Hy.
pose proof (ld_log1p (B2R xl / B2R xh) ltac:(rewrite B51; exact Hd)) as Hlog.
rewrite B102 in Hlog.
set (d := B2R xl / B2R xh) in *.
set (L1 := ln (1 + d)) in *.
set (D := ln (B2R xh) - IZR e * ln 2) in *.
set (Y := IZR e0 * ln 2 + (ln (B2R xh) + L1)) in *.
assert (EY : Y = IZR (e + e0) * ln 2 + D + L1) by (unfold Y, D; rewrite plus_IZR; ring).
clear Hsplit Hln_max Hee Hmax.
set (ef := DyadicLog.of_i64 (e + e0)) in *.
set (LH := from_bits DyadicLog.LN2H) in *.
set (LL := from_bits DyadicLog.LN2L) in *.
set (P := mul ef LH) in *.
set (Q := mul ef LL) in *.
set (dl := div xl xh) in *.
set (Q' := add Q dl) in *.
destruct (Fast.fast_two_sum P ah) as [s t] eqn:E1.
set (R := add al Q') in *.
set (W := add t R) in *.
destruct (Fast.fast_two_sum s W) as [h0 l0] eqn:E2.
rewrite B80 in Hy. rewrite B20 in Hy20.
(* The core: [|a_h + a_l| <= 0.351] and [|a_l| <= 2^-54]. *)
assert (Hc1 : 3 * / 2361183241434822606848 * Rabs D <= 3 * / 2361183241434822606848 * (7 / 20))
  by (apply Rmult_le_compat_l; [lra | exact HD]).
pose proof (fl_tri (B2R ah + B2R al) D (- (D - (B2R ah + B2R al))) ltac:(ring)) as Ta.
rewrite Rabs_Ropp in Ta.
pose proof (rn_err (B2R ah + B2R al)) as Hal. rewrite <- Eah, U in Hal.
replace (B2R ah - (B2R ah + B2R al)) with (- B2R al) in Hal by ring. rewrite Rabs_Ropp in Hal.
pose proof (fl_tri (B2R ah) (B2R ah + B2R al) (- B2R al) ltac:(ring)) as Tb.
rewrite Rabs_Ropp in Tb.
assert (Hah : Rabs (B2R ah) <= 3501 / 10000) by lra.
assert (Hal' : Rabs (B2R al) <= / 18014398509481984) by lra.
clear Ta Tb.
(* [|d| <= 2^-51], [|ln(1 + d)| <= 2^-51 + 2^-102], [|dl - d| <= 2^-104 + 2^-1075]. *)
pose proof (fl_tri L1 d (L1 - d) ltac:(ring)) as TL1.
assert (Hl1 : Rabs L1 <= / 2251799813685248 + / 5070602400912917605986812821504) by lra.
assert (Hdl' : Rabs (B2R dl - d) <= / 20282409603651670423947251286016 + / 1267650600228229401496703205376)
  by lra.
pose proof (fl_tri (B2R dl) d (B2R dl - d) ltac:(ring)) as Tdl.
assert (Hdb : Rabs (B2R dl) <= / 2251799813685240) by lra.
clear TL1 Tdl.
(* [|y| <= 746]. *)
assert (Hy746 : Rabs y <= 746).
{ assert (Ey : Rabs (IZR (e + e0) * ln 2) <= 1074 * ln 2).
  { rewrite Rabs_mult, (Rabs_pos_eq (ln 2)) by lra.
    apply Rmult_le_compat_r; [lra | exact Hea]. }
  pose proof (fl_tri Y (IZR (e + e0) * ln 2 + D) L1 EY) as Ty1.
  pose proof (fl_tri (IZR (e + e0) * ln 2 + D) (IZR (e + e0) * ln 2) D eq_refl) as Ty2.
  pose proof (fl_tri y Y (y - Y) ltac:(ring)) as Ty3.
  lra. }
pose proof (fl_tri Y y (- (y - Y)) ltac:(ring)) as TyY.
rewrite Rabs_Ropp in TyY.
assert (Hy56 : y = 0 \/ bpow radix2 (-56) <= Rabs y) by (right; rewrite B56; lra).
destruct (Z.eq_dec (e + e0) 0) as [E0 | En0].
- (* [e + e0 = 0]: [h + l = a_h + RN(a_l + RN(xl / xh))]. *)
  assert (Ie : IZR (e + e0) = 0) by (rewrite E0; reflexivity).
  rewrite Ie, Rmult_0_l in VP, EY. rewrite Rplus_0_l in EY.
  assert (Fz : Rabs (B2R ah) <= Rabs (B2R P) \/ B2R P = 0) by (right; exact VP).
  assert (Hs : Rabs (B2R P + B2R ah) <= 2048) by (rewrite VP, Rplus_0_l; lra).
  destruct (fts_exact P ah s t FP Fah Fz Hs E1) as (Fs & Ft & Es & Est).
  rewrite VP, Rplus_0_l in Es, Est.
  rewrite round_generic in Es by first [apply generic_format_B2R | typeclasses eauto].
  assert (Et : B2R t = 0) by lra.
  destruct (mul_below_max ef LL Fef FLL) as (FQ & EQ & _).
  { rewrite Vef, Ie, Rmult_0_l, Rabs_R0. lra. }
  fold Q in FQ, EQ.
  rewrite Vef, Ie, Rmult_0_l, round_0 in EQ by typeclasses eauto.
  destruct (add_below_max Q dl FQ Fdl) as (FQ' & EQ' & _).
  { rewrite EQ, Rplus_0_l. lra. }
  fold Q' in FQ', EQ'.
  rewrite EQ, Rplus_0_l, round_generic in EQ' by first [apply generic_format_B2R | typeclasses eauto].
  destruct (add_below_max al Q' Fal FQ') as (FR & ER & _).
  { rewrite EQ'. pose proof (fl_tri (B2R al + B2R dl) (B2R al) (B2R dl) eq_refl). lra. }
  fold R in FR, ER.
  pose proof (rn_err (B2R al + B2R Q')) as HR. rewrite <- ER, U, EQ' in HR.
  rewrite EQ' in ER.
  pose proof (fl_tri (B2R al + B2R dl) (B2R al) (B2R dl) eq_refl) as TaD.
  pose proof (fl_tri (B2R R) (B2R al + B2R dl) (B2R R - (B2R al + B2R dl)) ltac:(ring)) as TR.
  assert (HRb : Rabs (B2R R) <= / 562949953421312) by lra.
  destruct (add_below_max t R Ft FR) as (FW & EW & _).
  { rewrite Et, Rplus_0_l. lra. }
  fold W in FW, EW.
  rewrite Et, Rplus_0_l, round_generic in EW by first [apply generic_format_B2R | typeclasses eauto].
  (* [|D| >= |y| - 2^-80 |y| - |L1|], so [|a_h| >= 2^-21]. *)
  pose proof (fl_tri Y D L1 EY) as TY.
  pose proof (fl_tri D (B2R ah + B2R al) (D - (B2R ah + B2R al)) ltac:(ring)) as TD.
  pose proof (fl_tri (B2R ah + B2R al) (B2R ah) (B2R al) eq_refl) as Tah.
  assert (HDy : Rabs D <= Rabs y + / 1208925819614629174706176 * Rabs y +
    / 2251799813685248 + / 5070602400912917605986812821504).
  { pose proof (fl_tri D Y (- L1) ltac:(rewrite EY; ring)) as TD2.
    rewrite Rabs_Ropp in TD2. lra. }
  apply (fl_finish s W h0 l0 h l k y Fs FW); [| lra | exact Hy56 | | exact E2 | exact E].
  + left. rewrite Es, EW. pose proof (fl_tri y Y (y - Y) ltac:(ring)) as Tyy.
    clear - HRb Tyy Hy Hy20 TY TD Tah Hcore Hc1 Hal' Hl1. lra.
  + (* The error is the sum of five terms. *)
    assert (Id : y - (B2R s + B2R W) =
      (y - Y) + (D - (B2R ah + B2R al)) + (L1 - d) + (- (B2R dl - d)) +
      (- (B2R R - (B2R al + B2R dl)))) by lra.
    rewrite Id. eapply Rle_trans; [apply ld_tri5|]. rewrite !Rabs_Ropp.
    rewrite B69.
    assert (Cb : Rabs (D - (B2R ah + B2R al)) <=
      3 * / 2361183241434822606848 * (Rabs y + / 1208925819614629174706176 * Rabs y +
        / 2251799813685248 + / 5070602400912917605986812821504)).
    { apply Rle_trans with (1 := Hcore). apply Rmult_le_compat_l; [lra | exact HDy]. }
    clear - Hy Cb Hlog Hdl' HR TaD Hal' Hdb Hy20 T0 T1.
    lra.
- (* [e + e0 <> 0]: [|y| >= ln 2 - 7/20 - 2^-50]. *)
  assert (Hea1 : 1 <= Rabs (IZR (e + e0))).
  { rewrite <- abs_IZR. apply IZR_le. lia. }
  assert (HP : Rabs (B2R P) = Rabs (IZR (e + e0)) * (IZR 3048493539143 * / 4398046511104)).
  { rewrite VP, VH, Rabs_mult, (Rabs_pos_eq (IZR 3048493539143 * _)) by lra. reflexivity. }
  assert (Fz : Rabs (B2R ah) <= Rabs (B2R P) \/ B2R P = 0) by (left; rewrite HP; lra).
  pose proof (fl_tri (B2R P + B2R ah) (B2R P) (B2R ah) ltac:(ring)) as Tp.
  assert (Hs : Rabs (B2R P + B2R ah) <= 2048) by lra.
  destruct (fts_exact P ah s t FP Fah Fz Hs E1) as (Fs & Ft & Es & Est).
  (* [t = (P + a_h) - RN(P + a_h)]. *)
  pose proof (rn_err (B2R P + B2R ah)) as Hst. rewrite <- Es, U in Hst.
  replace (B2R s - (B2R P + B2R ah)) with (- B2R t) in Hst by lra.
  rewrite Rabs_Ropp in Hst.
  (* [Q = RN((e + e0) LN2L)]. *)
  assert (HeL : Rabs (IZR (e + e0) * B2R LL) <=
    1074 * (IZR 8711806768342832 * / 158456325028528675187087900672)).
  { rewrite VL, Rabs_mult, (Rabs_pos_eq (IZR 8711806768342832 * _)) by lra.
    apply Rmult_le_compat_r; [lra | exact Hea]. }
  destruct (mul_below_max ef LL Fef FLL) as (FQ & EQ & _).
  { rewrite Vef. lra. }
  fold Q in FQ, EQ.
  pose proof (rn_err (IZR (e + e0) * B2R LL)) as HQ. rewrite Vef in EQ. rewrite <- EQ, U in HQ.
  pose proof (fl_tri (B2R Q) (IZR (e + e0) * B2R LL) (B2R Q - IZR (e + e0) * B2R LL)
    ltac:(ring)) as TQ.
  (* [Q' = RN(Q + dl)]. *)
  pose proof (fl_tri (B2R Q + B2R dl) (B2R Q) (B2R dl) eq_refl) as TQd.
  destruct (add_below_max Q dl FQ Fdl) as (FQ' & EQ' & _).
  { lra. }
  fold Q' in FQ', EQ'.
  pose proof (rn_err (B2R Q + B2R dl)) as HQ'. rewrite <- EQ', U in HQ'.
  pose proof (fl_tri (B2R Q') (B2R Q + B2R dl) (B2R Q' - (B2R Q + B2R dl)) ltac:(ring)) as TQ'.
  (* [R = RN(a_l + Q')]. *)
  pose proof (fl_tri (B2R al + B2R Q') (B2R al) (B2R Q') eq_refl) as TaQ.
  destruct (add_below_max al Q' Fal FQ') as (FR & ER & _).
  { lra. }
  fold R in FR, ER.
  pose proof (rn_err (B2R al + B2R Q')) as HR. rewrite <- ER, U in HR.
  pose proof (fl_tri (B2R R) (B2R al + B2R Q') (B2R R - (B2R al + B2R Q')) ltac:(ring)) as TR.
  (* [W = RN(t + R)]. *)
  pose proof (fl_tri (B2R t + B2R R) (B2R t) (B2R R) eq_refl) as TtR.
  destruct (add_below_max t R Ft FR) as (FW & EW & _).
  { lra. }
  fold W in FW, EW.
  pose proof (rn_err (B2R t + B2R R)) as HW. rewrite <- EW, U in HW.
  pose proof (fl_tri (B2R W) (B2R t + B2R R) (B2R W - (B2R t + B2R R)) ltac:(ring)) as TW.
  (* [|(e + e0) (ln 2 - LN2H - LN2L)| <= 1074 2^-100]. *)
  assert (Hdd : Rabs (IZR (e + e0) * (ln 2 - (B2R LH + B2R LL))) <=
    1074 * / 1267650600228229401496703205376).
  { rewrite Rabs_mult. apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hea |].
    apply Rabs_le. lra. }
  apply (fl_finish s W h0 l0 h l k y Fs FW); [| lra | exact Hy56 | | exact E2 | exact E].
  + left. pose proof (fl_tri (B2R P + B2R ah) (B2R s) (B2R t) ltac:(lra)) as Ts.
    pose proof (fl_tri (B2R P) (B2R P + B2R ah) (- B2R ah) ltac:(ring)) as Tp2.
    rewrite Rabs_Ropp in Tp2. lra.
  + (* The error is the sum of nine terms. *)
    assert (Id : y - (B2R s + B2R W) =
      (y - Y) + (D - (B2R ah + B2R al)) + IZR (e + e0) * (ln 2 - (B2R LH + B2R LL)) +
      (L1 - d) + (- (B2R W - (B2R t + B2R R))) + (- (B2R R - (B2R al + B2R Q'))) +
      (- (B2R Q' - (B2R Q + B2R dl))) + (- (B2R Q - IZR (e + e0) * B2R LL)) +
      (- (B2R dl - d))).
    { rewrite VP in Est. rewrite EY. ring_simplify. lra. }
    rewrite Id. eapply Rle_trans; [apply ld_tri9|]. rewrite !Rabs_Ropp.
    (* [|y| >= |e + e0| ln 2 - 7/20 - |L1| - 2^-80 |y| >= 0.343]. *)
    assert (Ey : ln 2 <= Rabs (IZR (e + e0) * ln 2)).
    { rewrite Rabs_mult, (Rabs_pos_eq (ln 2)) by lra.
      apply Rle_trans with (1 * ln 2); [lra | apply Rmult_le_compat_r; lra]. }
    pose proof (fl_tri (IZR (e + e0) * ln 2) Y (- (D + L1)) ltac:(rewrite EY; ring)) as Ty.
    pose proof (fl_tri (D + L1) D L1 eq_refl) as Ty2.
    rewrite Rabs_Ropp in Ty.
    rewrite B69.
    assert (Ya : 343 / 1000 <= Rabs y) by lra.
    (* [|P| <= 745], [|t| <= 2^-43]. *)
    assert (Pb : Rabs (B2R P) <= 745) by lra.
    assert (tb : Rabs (B2R t) <= / 8796093022208) by lra.
    (* [|(e + e0) LN2L| < 5.905 10^-11], and the sums that hold it. *)
    assert (Qb : Rabs (B2R Q) <= 591 / 10000000000000) by lra.
    assert (Qdb : Rabs (B2R Q + B2R dl) <= 592 / 10000000000000) by lra.
    assert (Q'b : Rabs (B2R Q') <= 593 / 10000000000000) by lra.
    assert (aQb : Rabs (B2R al + B2R Q') <= 594 / 10000000000000) by lra.
    assert (Rb : Rabs (B2R R) <= 595 / 10000000000000) by lra.
    assert (tRb : Rabs (B2R t + B2R R) <= 597 / 10000000000000) by lra.
    (* The five roundings of the low sum, each below [2^-85]. *)
    assert (eQ : Rabs (B2R Q - IZR (e + e0) * B2R LL) <= / 38685626227668133590597632) by lra.
    assert (eQ' : Rabs (B2R Q' - (B2R Q + B2R dl)) <= / 38685626227668133590597632) by lra.
    assert (eR : Rabs (B2R R - (B2R al + B2R Q')) <= / 38685626227668133590597632) by lra.
    assert (eW : Rabs (B2R W - (B2R t + B2R R)) <= / 38685626227668133590597632) by lra.
    assert (ed : Rabs (B2R dl - d) <= / 38685626227668133590597632) by lra.
    (* The core: [3 2^-71 7/20 = 1.05 2^-71]. *)
    assert (Cb : Rabs (D - (B2R ah + B2R al)) <= 105 / 100 * / 2361183241434822606848) by lra.
    (* [2^-80 |y| + 1.05 2^-71 + 1074 2^-100 + 2^-102 + 5 2^-85 < 3.2 2^-71 |y|]. *)
    clear - Hy Cb Hdd Hlog eQ eQ' eR eW ed Ya.
    lra.
Qed.

Theorem fast_ln_dd_fma :
  forall xh xl e0,
  is_finite xh = true -> 0 < B2R xh ->
  DyadicLog.fast_ln_dd true xh xl e0 = DyadicLog.fast_ln_dd false xh xl e0.
Proof.
intros xh xl e0 Fxh Pxh.
unfold DyadicLog.fast_ln_dd.
rewrite (ln_core_fma xh Fxh Pxh). reflexivity.
Qed.
