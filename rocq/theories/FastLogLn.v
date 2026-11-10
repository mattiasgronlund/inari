(** * The fast path of [ln] before the rounding

    [DyadicLog.fast_ln] of [Model.v] adds [e ln 2] to the core
    ([FastLogCore.v]), with [ln 2] split as [LN2H + LN2L]
    ([FastLogTables.v]) and [e LN2H] exact, and normalises the sum
    ([FastLogNorm.v]). [fast_ln_correct] shows that the result is within
    [2^-68] of [ln x 2^-k], with [1/2 < |h| < 2], as the rounding tests of
    [FastSign.v] need.

    The sum [h + l] is [ln x] within [4/5 2^-69 |ln x|] (as [FastLogFin.fl_finish] takes). For
    [e = 0], [h + l] is the core's [a_h + a_l] exactly, within [3 2^-71
    |ln x|]. For [e <> 0], [|ln x| >= ln 2 - 7/20 > 0.343], and the core's
    [3 2^-71 7/20], [1074 2^-100] from [LN2H + LN2L] and the three
    roundings of the low sum, below [2^-82], stay below [1.051 2^-71].
    Then [h = RN(h + l)] is [ln x] within a factor [1 +- 2^-52], so the
    error is at most [2^-69 |h|], as [normalize_correct] needs. [x = 1]
    gives [h + l = 0] and [h = 0], where [normalize] returns [None]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct FastRound FastLogTables
  FastLogCore FastLogNorm FastLogFin FastExpErr.

Open Scope R_scope.

(** ** Helpers (the shared ones are in [FastLogFin.v]) *)

(** [LN2L] as [m 2^-97]. *)
Local Lemma fl_ln2l :
  B2R (from_bits DyadicLog.LN2L) = IZR 8711806768342832 * bpow radix2 (-97).
Proof.
rewrite <- (SF2R_B2SF _ _ (from_bits DyadicLog.LN2L)).
replace (B2SF (from_bits DyadicLog.LN2L)) with (SpecFloat.S754_finite false 8711806768342832 (-97))
  by (vm_compute; reflexivity).
reflexivity.
Qed.

(** [e LN2H] is exact for [|e| <= 1074], as [LN2H] has a significand
    of 42 bits and [1074 2^42 < 2^53]. *)
Local Lemma fl_e_ln2h :
  forall e, (-1074 <= e <= 1074)%Z ->
  is_finite (mul (DyadicLog.of_i64 e) (from_bits DyadicLog.LN2H)) = true /\
  B2R (mul (DyadicLog.of_i64 e) (from_bits DyadicLog.LN2H)) =
    IZR e * B2R (from_bits DyadicLog.LN2H).
Proof.
intros e He.
assert (Ee : (Z.abs e < 2 ^ 53)%Z) by (change (2 ^ 53)%Z with 9007199254740992%Z; lia).
destruct (fl_of_i64 e Ee) as [Fef Vef].
assert (FLH : is_finite (from_bits DyadicLog.LN2H) = true) by (vm_compute; reflexivity).
pose proof ln2h_exact as VH.
assert (B42 : bpow radix2 (-42) = / 4398046511104) by reflexivity.
pose proof fl_max as HM.
assert (Hea : Rabs (IZR e) <= 1074) by (rewrite <- abs_IZR; apply IZR_le; lia).
destruct (mul_below_max _ _ Fef FLH) as (FP & EP & _).
{ rewrite Vef, VH, B42, Rabs_mult, (Rabs_pos_eq (IZR 3048493539143 * _)) by lra. lra. }
split; [exact FP|]. rewrite EP, Vef. apply round_generic; [typeclasses eauto|].
rewrite VH.
replace (IZR e * (IZR 3048493539143 * bpow radix2 (-42)))
  with (F2R (Float radix2 (e * 3048493539143) (-42)))
  by (unfold F2R; cbn [Fnum Fexp]; rewrite mult_IZR; ring).
apply generic_format_FLT, (FLT_spec _ _ _ _ (Float radix2 (e * 3048493539143) (-42)));
  [reflexivity | | cbn [Fexp]; lia].
cbn [Fnum radix_val radix2]. change (2 ^ 53)%Z with 9007199254740992%Z. lia.
Qed.

(** ** The theorem *)

Theorem fast_ln_correct :
  forall fma x h l k,
  is_finite x = true -> 0 < B2R x -> DyadicLog.fast_ln fma x = Some (h, l, k) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < Rabs (B2R h) < 2 /\ (-1021 <= k <= 1022)%Z /\
  Rabs (ln (B2R x) * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-68).
Proof.
intros fma x h l k Fx Px E.
pose proof (ln_core_correct fma x Fx Px) as Hc.
unfold DyadicLog.fast_ln in E.
destruct (DyadicLog.ln_core fma x) as [[e ah] al].
destruct Hc as (Fah & Fal & Eah & He & HD & Hcore).
cbv beta iota zeta in E.
assert (He' : (-1074 <= e <= 1074)%Z) by lia.
destruct (fl_e_ln2h e He') as [FP VP].
assert (Ee : (Z.abs e < 2 ^ 53)%Z) by (change (2 ^ 53)%Z with 9007199254740992%Z; lia).
destruct (fl_of_i64 e Ee) as [Fef Vef].
assert (FLL : is_finite (from_bits DyadicLog.LN2L) = true) by (vm_compute; reflexivity).
pose proof ln2h_exact as VH. pose proof fl_ln2l as VL. pose proof ln2_split_correct as Hln2.
pose proof (fl_y0 x Fx Px) as Hy0.
(* [fl_finish] takes [y = 0] or [|y| >= 2^-56]. *)
assert (Hy56 : ln (B2R x) = 0 \/ bpow radix2 (-56) <= Rabs (ln (B2R x))).
{ destruct Hy0 as [Y | Y]; [left; exact Y | right].
  apply Rle_trans with (2 := Y). apply bpow_le. lia. }
set (y := ln (B2R x)) in *.
set (ef := DyadicLog.of_i64 e) in *.
set (LH := from_bits DyadicLog.LN2H) in *.
set (LL := from_bits DyadicLog.LN2L) in *.
set (P := mul ef LH) in *.
set (Q := mul ef LL) in *.
destruct (Fast.fast_two_sum P ah) as [s t] eqn:E1.
set (R := add al Q) in *.
set (W := add t R) in *.
destruct (Fast.fast_two_sum s W) as [h0 l0] eqn:E2.
(* The numbers. *)
assert (U : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
assert (B42 : bpow radix2 (-42) = / 4398046511104) by reflexivity.
assert (B69 : bpow radix2 (-69) = / 590295810358705651712) by reflexivity.
assert (B71 : bpow radix2 (-71) = / 2361183241434822606848) by reflexivity.
assert (B97 : bpow radix2 (-97) = / 158456325028528675187087900672) by reflexivity.
assert (B100 : bpow radix2 (-100) = / 1267650600228229401496703205376) by reflexivity.
pose proof (bpow_gt_0 radix2 (-1075)) as T0.
assert (T1 : bpow radix2 (-1075) <= bpow radix2 (-100)) by (apply bpow_le; lia).
rewrite B42 in VH. rewrite B97 in VL. rewrite B100 in Hln2, T1. rewrite B71 in Hcore.
apply Rabs_le_inv in Hln2.
pose proof fl_max as HM.
assert (Hea : Rabs (IZR e) <= 1074) by (rewrite <- abs_IZR; apply IZR_le; lia).
assert (L2 : 6931 / 10000 <= ln 2 <= 6932 / 10000) by lra.
(* The core: [|a_h + a_l| <= 0.351] and [|a_l| <= 2^-54]. *)
set (D := y - IZR e * ln 2) in *.
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
clear Ta Tb Hal.
(* [|y| <= 746]. *)
assert (Hy : Rabs y <= 746).
{ assert (Ey : Rabs (IZR e * ln 2) <= 1074 * ln 2).
  { rewrite Rabs_mult, (Rabs_pos_eq (ln 2)) by lra.
    apply Rmult_le_compat_r; [lra | exact Hea]. }
  pose proof (fl_tri y (IZR e * ln 2) D ltac:(unfold D; ring)) as T. lra. }
destruct (Z.eq_dec e 0) as [E0 | En0].
- (* [e = 0]: [h + l = a_h + a_l] exactly. *)
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
  apply (fl_finish s W h0 l0 h l k y Fs FW); [| lra | exact Hy56 | | exact E2 | exact E].
  + rewrite Es, EW. exact (fl_low ah al Eah).
  + rewrite Es, EW.
    unfold D in Hcore. rewrite Ie, Rmult_0_l, Rminus_0_r in Hcore.
    rewrite B69. pose proof (Rabs_pos y). lra.
- (* [e <> 0]: [|y| >= ln 2 - 7/20]. *)
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
  assert (HeL : Rabs (IZR e * B2R LL) <= 1074 * (IZR 8711806768342832 * / 158456325028528675187087900672)).
  { rewrite VL, Rabs_mult, (Rabs_pos_eq (IZR 8711806768342832 * _)) by lra.
    apply Rmult_le_compat_r; [lra | exact Hea]. }
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
  (* [|e (ln 2 - LN2H - LN2L)| <= 1074 2^-100]. *)
  assert (Hd : Rabs (IZR e * (ln 2 - (B2R LH + B2R LL))) <=
    1074 * / 1267650600228229401496703205376).
  { rewrite Rabs_mult. apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hea |].
    apply Rabs_le. lra. }
  apply (fl_finish s W h0 l0 h l k y Fs FW); [| lra | exact Hy56 | | exact E2 | exact E].
  + left. pose proof (fl_tri (B2R P + B2R ah) (B2R s) (B2R t) ltac:(lra)) as Ts.
    pose proof (fl_tri (B2R P) (B2R P + B2R ah) (- B2R ah) ltac:(ring)) as Tp2.
    rewrite Rabs_Ropp in Tp2. lra.
  + (* The error is the sum of five terms. *)
    assert (Id : y - (B2R s + B2R W) =
      (D - (B2R ah + B2R al)) + IZR e * (ln 2 - (B2R LH + B2R LL)) -
      (B2R W - (B2R t + B2R R)) - (B2R R - (B2R al + B2R Q)) - (B2R Q - IZR e * B2R LL)).
    { unfold D. rewrite VP in Est. lra. }
    pose proof (fl_tri (y - (B2R s + B2R W))
      ((D - (B2R ah + B2R al)) + IZR e * (ln 2 - (B2R LH + B2R LL)))
      (- (B2R W - (B2R t + B2R R)) - (B2R R - (B2R al + B2R Q)) - (B2R Q - IZR e * B2R LL))
      ltac:(rewrite Id; ring)) as S1.
    pose proof (fl_tri ((D - (B2R ah + B2R al)) + IZR e * (ln 2 - (B2R LH + B2R LL)))
      (D - (B2R ah + B2R al)) (IZR e * (ln 2 - (B2R LH + B2R LL))) eq_refl) as S2.
    pose proof (fl_tri
      (- (B2R W - (B2R t + B2R R)) - (B2R R - (B2R al + B2R Q)) - (B2R Q - IZR e * B2R LL))
      (- (B2R W - (B2R t + B2R R)) - (B2R R - (B2R al + B2R Q)))
      (- (B2R Q - IZR e * B2R LL)) ltac:(ring)) as S3.
    pose proof (fl_tri (- (B2R W - (B2R t + B2R R)) - (B2R R - (B2R al + B2R Q)))
      (- (B2R W - (B2R t + B2R R))) (- (B2R R - (B2R al + B2R Q))) ltac:(ring)) as S4.
    rewrite !Rabs_Ropp in S3, S4.
    (* [|y| >= |e| ln 2 - 7/20 >= ln 2 - 7/20]. *)
    assert (Ey : ln 2 <= Rabs (IZR e * ln 2)).
    { rewrite Rabs_mult, (Rabs_pos_eq (ln 2)) by lra. nra. }
    pose proof (fl_tri (IZR e * ln 2) y (- D) ltac:(unfold D; ring)) as Ty.
    rewrite Rabs_Ropp in Ty.
    (* [rewrite !Rabs_Ropp in S3, S4] leaves the second [Rabs (- _)] of [S4]. *)
    rewrite Rabs_Ropp in S4.
    rewrite B69.
    (* (a) [|y| >= ln 2 - 7/20 > 0.3431]. *)
    assert (Ya : 3431 / 10000 <= Rabs y) by lra.
    (* (b) [|P| = |e| LN2H <= 1074 LN2H < 745]. *)
    assert (Pb : Rabs (B2R P) <= 745) by lra.
    (* (c) [|t| <= 2^-53 |P + a_h| + 2^-1075 < 2^-43]. *)
    assert (tb : Rabs (B2R t) <= / 8796093022208) by lra.
    (* (d) [|e LN2L| <= 1074 LN2L < 5.905 10^-11], and the sums that hold it. *)
    assert (Qb : Rabs (B2R Q) <= 591 / 10000000000000) by lra.
    assert (aQb : Rabs (B2R al + B2R Q) <= 592 / 10000000000000) by lra.
    assert (Rb : Rabs (B2R R) <= 593 / 10000000000000) by lra.
    assert (tRb : Rabs (B2R t + B2R R) <= 595 / 10000000000000) by lra.
    (* (e) The three roundings of the low sum, each below [2^-85]. *)
    assert (eQ : Rabs (B2R Q - IZR e * B2R LL) <= / 38685626227668133590597632) by lra.
    assert (eR : Rabs (B2R R - (B2R al + B2R Q)) <= / 38685626227668133590597632) by lra.
    assert (eW : Rabs (B2R W - (B2R t + B2R R)) <= / 38685626227668133590597632) by lra.
    (* (f) The core: [3 2^-71 7/20 = 1.05 2^-71]. *)
    assert (Cb : Rabs (D - (B2R ah + B2R al)) <= 105 / 100 * / 2361183241434822606848) by lra.
    (* [1.05 2^-71 + 1074 2^-100 + 3 2^-85 < 3.2 2^-71 0.3431]. *)
    clear - S1 S2 S3 S4 Hd Cb eQ eR eW Ya.
    lra.
Qed.
