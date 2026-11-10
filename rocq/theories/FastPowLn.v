(** * The logarithm of x^y: e ln 2 + ln m

    [DyadicLog.ln_acc] of [Model.v] adds [e ln 2] to the core
    ([FastPowCore.v]) in double-double, as [DyadicLog.fast_ln] does
    ([FastLogLn.v]), without its normalization: [ln_acc_correct] shows
    that [lh + ll] is within [17/16 2^-79 |ln x|] of ln x, with [lh =
    RN(lh + ll)]. For [e = 0], [lh + ll] is the core's [ah + al]. For [e
    <> 0], [|ln m| <= 7/20] and [|ln x| >= |e| (ln 2 - 7/20)], so that
    the bound of the core, relative to [|ln m|], is at most [1.0201]
    times that relative to [|ln x|], and [e (ln 2 - LN2H - LN2L)] with
    the roundings of [e LN2L] and of the two additions of the low part
    add less than [2^-93] relative to [|ln x|].

    [ln_acc_fma] shows that an FMA gives the same result. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct FastRound FastExpErr
  FastLogTables FastLogNorm FastLogFin FastPowCore.
From Inari Require FastLogLn.

Open Scope R_scope.

(** [|a - b - c - d| <= |a| + |b| + |c| + |d|]. *)
Local Lemma pl_tri4 :
  forall a b c d, Rabs (a - b - c - d) <= Rabs a + Rabs b + Rabs c + Rabs d.
Proof.
intros a b c d.
pose proof (fl_tri (a - b - c - d) (a - b - c) (- d) ltac:(ring)) as H1.
pose proof (fl_tri (a - b - c) (a - b) (- c) ltac:(ring)) as H2.
pose proof (fl_tri (a - b) a (- b) ltac:(ring)) as H3.
rewrite Rabs_Ropp in H1, H2, H3.
lra.
Qed.

(** For a finite [x > 0], [lh + ll] is within [17/16 2^-79 |ln x|] of
    ln x, with [lh = RN(lh + ll)] and [|lh| <= 745]. *)
Theorem ln_acc_correct :
  forall fma x, is_finite x = true -> 0 < B2R x ->
  let '(lh, ll) := DyadicLog.ln_acc fma x in
  is_finite lh = true /\ is_finite ll = true /\ B2R lh = RN (B2R lh + B2R ll) /\
  Rabs (B2R lh) <= 745 /\
  Rabs (ln (B2R x) - (B2R lh + B2R ll)) <= 17 / 16 * bpow radix2 (-79) * Rabs (ln (B2R x)).
Proof.
intros fma x Fx Px.
pose proof (ln_core_acc_correct fma x Fx Px) as Hc.
unfold DyadicLog.ln_acc.
destruct (DyadicLog.ln_core_acc fma x) as [[e ah] al].
destruct Hc as (Fah & Fal & Eah & He & HD & Hcore).
cbv beta iota zeta.
assert (He' : (-1074 <= e <= 1074)%Z) by lia.
destruct (FastLogLn.fl_e_ln2h e He') as [FP VP].
assert (Ee : (Z.abs e < 2 ^ 53)%Z) by (change (2 ^ 53)%Z with 9007199254740992%Z; lia).
destruct (fl_of_i64 e Ee) as [Fef Vef].
assert (FLL : is_finite (from_bits DyadicLog.LN2L) = true) by (vm_compute; reflexivity).
pose proof ln2h_exact as VH. pose proof FastLogLn.fl_ln2l as VL.
pose proof ln2_split_correct as Hln2.
set (y := ln (B2R x)) in *.
set (ef := DyadicLog.of_i64 e) in *.
set (LH := from_bits DyadicLog.LN2H) in *.
set (LL := from_bits DyadicLog.LN2L) in *.
set (P := mul ef LH) in *.
set (Q := mul ef LL) in *.
destruct (Fast.fast_two_sum P ah) as [s t] eqn:E1.
set (R := add al Q) in *.
set (W := add t R) in *.
destruct (Fast.fast_two_sum s W) as [lh ll] eqn:E2.
(* The numbers. *)
assert (U : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
assert (B42 : bpow radix2 (-42) = / 4398046511104) by reflexivity.
assert (B79 : bpow radix2 (-79) = / 604462909807314587353088) by reflexivity.
assert (B93 : bpow radix2 (-93) = / 9903520314283042199192993792) by reflexivity.
assert (B97 : bpow radix2 (-97) = / 158456325028528675187087900672) by reflexivity.
assert (B100 : bpow radix2 (-100) = / 1267650600228229401496703205376) by reflexivity.
assert (B110 : bpow radix2 (-110) = / 1298074214633706907132624082305024) by reflexivity.
pose proof (bpow_gt_0 radix2 (-1075)) as T0.
assert (T1 : bpow radix2 (-1075) <= / 1298074214633706907132624082305024)
  by (rewrite <- B110; apply bpow_le; lia).
rewrite B42 in VH. rewrite B97 in VL. rewrite B100 in Hln2. rewrite B79 in Hcore.
apply Rabs_le_inv in Hln2.
pose proof fl_max as HM.
assert (Hea : Rabs (IZR e) <= 1074) by (rewrite <- abs_IZR; apply IZR_le; lia).
assert (L2 : 69314 / 100000 <= ln 2 <= 69315 / 100000) by lra.
(* The core: [|a_h| <= 0.3501] and [|a_l| <= 2^-54]. *)
set (D := y - IZR e * ln 2) in *.
assert (Hc1 : / 604462909807314587353088 * Rabs D <= / 604462909807314587353088 * (7 / 20))
  by (apply Rmult_le_compat_l; [lra | exact HD]).
pose proof (fl_tri (B2R ah + B2R al) D (- (D - (B2R ah + B2R al))) ltac:(ring)) as Ta.
rewrite Rabs_Ropp in Ta.
pose proof (rn_err (B2R ah + B2R al)) as Hal. rewrite <- Eah, U in Hal.
replace (B2R ah - (B2R ah + B2R al)) with (- B2R al) in Hal by ring. rewrite Rabs_Ropp in Hal.
pose proof (fl_tri (B2R ah) (B2R ah + B2R al) (- B2R al) ltac:(ring)) as Tb.
rewrite Rabs_Ropp in Tb.
assert (Hah : Rabs (B2R ah) <= 3501 / 10000) by lra.
assert (Hal' : Rabs (B2R al) <= / 18014398509481984) by lra.
assert (Hsa : Rabs (B2R ah + B2R al) <= 3501 / 10000) by lra.
clear Ta Tb Hal.
destruct (Z.eq_dec e 0) as [E0 | En0].
- (* [e = 0]: [lh + ll = a_h + a_l] exactly. *)
  assert (Ie : IZR e = 0) by (rewrite E0; reflexivity).
  rewrite Ie, Rmult_0_l in VP.
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
  destruct (add_below_max al Q Fal FQ) as (FR & ER & _).
  { rewrite EQ, Rplus_0_r. lra. }
  fold R in FR, ER.
  rewrite EQ, Rplus_0_r, round_generic in ER by first [apply generic_format_B2R | typeclasses eauto].
  destruct (add_below_max t R Ft FR) as (FW & EW & _).
  { rewrite Et, ER, Rplus_0_l. lra. }
  fold W in FW, EW.
  rewrite Et, ER, Rplus_0_l, round_generic in EW by first [apply generic_format_B2R | typeclasses eauto].
  (* The second Fast2Sum adds [a_l] to [a_h]. *)
  assert (Fz2 : Rabs (B2R W) <= Rabs (B2R s) \/ B2R s = 0)
    by (rewrite Es, EW; exact (fl_low ah al Eah)).
  assert (Hs2 : Rabs (B2R s + B2R W) <= 2048) by (rewrite Es, EW; lra).
  destruct (fts_exact s W lh ll Fs FW Fz2 Hs2 E2) as (Flh & Fll & Elh & Esum).
  rewrite Es, EW, <- Eah in Elh. rewrite Es, EW in Esum.
  split; [exact Flh|]. split; [exact Fll|].
  split; [rewrite Esum, <- Eah; exact Elh|]. split.
  + rewrite Elh. lra.
  + rewrite Esum, B79.
    unfold D in Hcore. rewrite Ie, Rmult_0_l, Rminus_0_r in Hcore.
    pose proof (Rabs_pos y). lra.
- (* [e <> 0]: [|ln x| >= |e| (ln 2 - 7/20)]. *)
  assert (Hea1 : 1 <= Rabs (IZR e)).
  { rewrite <- abs_IZR. apply IZR_le. lia. }
  assert (HP : Rabs (B2R P) = Rabs (IZR e) * (IZR 3048493539143 * / 4398046511104)).
  { rewrite VP, VH, Rabs_mult, (Rabs_pos_eq (IZR 3048493539143 * _)) by lra. reflexivity. }
  assert (Fz : Rabs (B2R ah) <= Rabs (B2R P) \/ B2R P = 0) by (left; rewrite HP; lra).
  pose proof (fl_tri (B2R P + B2R ah) (B2R P) (B2R ah) ltac:(ring)) as Tp.
  assert (Hs : Rabs (B2R P + B2R ah) <= 2048) by lra.
  destruct (fts_exact P ah s t FP Fah Fz Hs E1) as (Fs & Ft & Es & Est).
  (* [t = (P + a_h) - RN(P + a_h)]. *)
  pose proof (rn_err (B2R P + B2R ah)) as Hst. rewrite <- Es, U in Hst.
  replace (B2R s - (B2R P + B2R ah)) with (- B2R t) in Hst by lra.
  rewrite Rabs_Ropp in Hst.
  (* [Q = RN(e LN2L)]. *)
  assert (HeL : Rabs (IZR e * B2R LL) =
    Rabs (IZR e) * (IZR 8711806768342832 * / 158456325028528675187087900672)).
  { rewrite VL, Rabs_mult, (Rabs_pos_eq (IZR 8711806768342832 * _)) by lra. reflexivity. }
  destruct (mul_below_max ef LL Fef FLL) as (FQ & EQ & _).
  { rewrite Vef. lra. }
  fold Q in FQ, EQ.
  pose proof (rn_err (IZR e * B2R LL)) as HQ. rewrite Vef in EQ. rewrite <- EQ, U in HQ.
  pose proof (fl_tri (B2R Q) (IZR e * B2R LL) (B2R Q - IZR e * B2R LL) ltac:(ring)) as TQ.
  (* [R = RN(a_l + Q)]. *)
  pose proof (fl_tri (B2R al + B2R Q) (B2R al) (B2R Q) ltac:(ring)) as TaQ.
  destruct (add_below_max al Q Fal FQ) as (FR & ER & _).
  { lra. }
  fold R in FR, ER.
  pose proof (rn_err (B2R al + B2R Q)) as HR. rewrite <- ER, U in HR.
  pose proof (fl_tri (B2R R) (B2R al + B2R Q) (B2R R - (B2R al + B2R Q)) ltac:(ring)) as TR.
  (* [W = RN(t + R)]. *)
  pose proof (fl_tri (B2R t + B2R R) (B2R t) (B2R R) ltac:(ring)) as TtR.
  destruct (add_below_max t R Ft FR) as (FW & EW & _).
  { lra. }
  fold W in FW, EW.
  pose proof (rn_err (B2R t + B2R R)) as HW. rewrite <- EW, U in HW.
  pose proof (fl_tri (B2R W) (B2R t + B2R R) (B2R W - (B2R t + B2R R)) ltac:(ring)) as TW.
  (* [|e (ln 2 - LN2H - LN2L)| <= |e| 2^-100]. *)
  assert (Hd : Rabs (IZR e * (ln 2 - (B2R LH + B2R LL))) <=
    Rabs (IZR e) * / 1267650600228229401496703205376).
  { rewrite Rabs_mult. apply Rmult_le_compat_l; [apply Rabs_pos|]. apply Rabs_le. lra. }
  (* [|ln x| >= |e| ln 2 - 7/20 >= 0.34314 |e|]. *)
  assert (Ey : Rabs (IZR e) * (69314 / 100000) <= Rabs (IZR e * ln 2)).
  { rewrite Rabs_mult, (Rabs_pos_eq (ln 2)) by lra.
    apply Rmult_le_compat_l; [apply Rabs_pos | lra]. }
  pose proof (fl_tri (IZR e * ln 2) y (- D) ltac:(unfold D; ring)) as Ty.
  rewrite Rabs_Ropp in Ty.
  assert (Ya : Rabs (IZR e) * (34314 / 100000) <= Rabs y) by lra.
  clear Ey Ty.
  (* Each term against [|e|], with [2^-100] as the unit of the low ones:
     [|t| <= 2^-53 (|e| LN2H + 0.3501) <= 2^-52 |e|], [|e| LN2L 2^-53 =
     7.74 |e| 2^-100], [|Q| <= 2^-44 |e|] and [|R| <= 1.001 2^-44 |e|]. *)
  assert (tb : Rabs (B2R t) <= Rabs (IZR e) * / 4503599627370496) by lra.
  assert (eQ : Rabs (B2R Q - IZR e * B2R LL) <=
    Rabs (IZR e) * (775 / 100 * / 1267650600228229401496703205376)) by lra.
  assert (Qb : Rabs (B2R Q) <= Rabs (IZR e) * / 17592186044416) by lra.
  assert (eR : Rabs (B2R R - (B2R al + B2R Q)) <=
    Rabs (IZR e) * (775 / 100 * / 1267650600228229401496703205376)) by lra.
  assert (Rb : Rabs (B2R R) <= Rabs (IZR e) * (1001 / 1000 * / 17592186044416)) by lra.
  assert (eW : Rabs (B2R W - (B2R t + B2R R)) <=
    Rabs (IZR e) * (805 / 100 * / 1267650600228229401496703205376)) by lra.
  assert (Wb : Rabs (B2R W) <= Rabs (IZR e) * / 8796093022208) by lra.
  (* The second Fast2Sum: [|s| >= |e| LN2H - 0.3501 - |t| > |W|]. *)
  pose proof (fl_tri (B2R P + B2R ah) (B2R s) (B2R t) ltac:(lra)) as Ts.
  pose proof (fl_tri (B2R P) (B2R P + B2R ah) (- B2R ah) ltac:(ring)) as Tp2.
  rewrite Rabs_Ropp in Tp2.
  assert (Fz2 : Rabs (B2R W) <= Rabs (B2R s) \/ B2R s = 0) by (left; lra).
  pose proof (fl_tri (B2R s) (B2R P + B2R ah) (- B2R t) ltac:(lra)) as Ts2.
  rewrite Rabs_Ropp in Ts2.
  assert (sb : Rabs (B2R s) <= 7448 / 10) by lra.
  pose proof (fl_tri (B2R s + B2R W) (B2R s) (B2R W) eq_refl) as TsW.
  assert (Hs2 : Rabs (B2R s + B2R W) <= 2048) by lra.
  destruct (fts_exact s W lh ll Fs FW Fz2 Hs2 E2) as (Flh & Fll & Elh & Esum).
  split; [exact Flh|]. split; [exact Fll|].
  split; [rewrite Esum; exact Elh|]. split.
  + (* [|s + W| <= 744.8], so [|lh| <= 744.8 (1 + 2^-53) + 2^-1075 < 745]. *)
    pose proof (rn_err (B2R s + B2R W)) as Hlh. rewrite <- Elh, U in Hlh.
    pose proof (fl_tri (B2R lh) (B2R s + B2R W) (B2R lh - (B2R s + B2R W)) ltac:(ring)) as Tlh.
    lra.
  + (* The error is the core's and four small terms. *)
    rewrite Esum, B79.
    assert (Ext : Rabs (IZR e * (ln 2 - (B2R LH + B2R LL)) - (B2R W - (B2R t + B2R R)) -
      (B2R R - (B2R al + B2R Q)) - (B2R Q - IZR e * B2R LL)) <= bpow radix2 (-93) * Rabs y).
    { pose proof (pl_tri4 (IZR e * (ln 2 - (B2R LH + B2R LL))) (B2R W - (B2R t + B2R R))
        (B2R R - (B2R al + B2R Q)) (B2R Q - IZR e * B2R LL)) as T4.
      rewrite B93. clear - T4 Hd eQ eR eW Ya Hea1. lra. }
    assert (Id : y - (B2R s + B2R W) =
      (D - (B2R ah + B2R al)) + (IZR e * (ln 2 - (B2R LH + B2R LL)) -
      (B2R W - (B2R t + B2R R)) - (B2R R - (B2R al + B2R Q)) - (B2R Q - IZR e * B2R LL))).
    { unfold D. rewrite VP in Est. lra. }
    pose proof (fl_tri (y - (B2R s + B2R W)) (D - (B2R ah + B2R al))
      (IZR e * (ln 2 - (B2R LH + B2R LL)) - (B2R W - (B2R t + B2R R)) -
      (B2R R - (B2R al + B2R Q)) - (B2R Q - IZR e * B2R LL)) Id) as S1.
    (* The core: [2^-79 7/20 <= 1.02 2^-79 |ln x|], as [|ln x| >= 0.34314]. *)
    rewrite B93 in Ext.
    clear - S1 Ext Hcore Hc1 Ya Hea1.
    lra.
Qed.

(** An FMA changes only the core, which [ln_core_acc_fma] shows gives
    the same result. *)
Theorem ln_acc_fma :
  forall x, is_finite x = true -> 0 < B2R x -> DyadicLog.ln_acc true x = DyadicLog.ln_acc false x.
Proof.
intros x Fx Px.
unfold DyadicLog.ln_acc.
rewrite (ln_core_acc_fma x Fx Px).
reflexivity.
Qed.
