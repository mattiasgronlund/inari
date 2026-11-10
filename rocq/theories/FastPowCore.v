(** * The logarithm of x^y: the core

    [DyadicLog.ln_core_acc] of [Model.v] is [DyadicLog.ln_core] with
    [DyadicLog.log1p_poly_acc] for [DyadicLog.log1p_poly]: the same
    reduction ([FastLogReduce.v]) and table ([FastLogTables.v]), and the
    more accurate polynomial of [FastPowPoly.v]. [ln_core_acc_correct]
    shows that it returns, for a finite [x > 0], [e] and [ah + al] within
    [2^-79 |ln m|] of ln m, for [m = x 2^-e], with [ah = RN(ah + al)].
    Away from 1, [|ln m| >= 2^-9 (1 - 2^-9)] and the errors are absolute,
    at most about [2^-88.7]; on the two intervals around 1, [r = 1], [z =
    m - 1] exactly and the error is relative to [|z|], at most about
    [0.88 2^-79 |z|].

    [ln_core_acc_fma] shows that an FMA gives the same result.
    [FastPowLn.v] adds [e ln 2].

    The proofs follow [FastLogCore.v]'s, whose lemmas on reals, on
    Fast2Sum and on the table they use: the two sums of two [f64]s that
    [ln_core_acc] does not round are exact by Fast2Sum [Dekker], the
    first because [|th| >= 2^-9 > |ah|] away from 1, and [th = 0] on the
    two intervals around 1.

    [Dekker] T. J. Dekker, A floating-point technique for extending the
    available precision, Numer. Math. 18 (1971). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct CancelLanes ExpSeries FastRound
  FastExpErr FastLogTables FastLogTaylor FastLogReduce FastPowPoly.
From Inari Require FastLogCore.

Open Scope R_scope.

Theorem ln_core_acc_correct :
  forall fma x, is_finite x = true -> 0 < B2R x ->
  let '(e, ah, al) := DyadicLog.ln_core_acc fma x in
  is_finite ah = true /\ is_finite al = true /\ B2R ah = RN (B2R ah + B2R al) /\
  (-1074 <= e <= 1024)%Z /\ Rabs (ln (B2R x) - IZR e * ln 2) <= 7 / 20 /\
  Rabs (ln (B2R x) - IZR e * ln 2 - (B2R ah + B2R al)) <=
    bpow radix2 (-79) * Rabs (ln (B2R x) - IZR e * ln 2).
Proof.
intros fma x Fx Px.
pose proof (ln_split_correct x Fx Px) as Hs.
unfold DyadicLog.ln_core_acc.
revert Hs. destruct (DyadicLog.ln_split x) as [[e m] i]. cbv beta iota.
intros (Fm & Hi & He & Hx & Hm).
pose proof (ltbl_correct i Hi) as Ht.
revert Ht. destruct (DyadicLog.ltbl i) as [[r th] tl]. cbv beta iota zeta.
intros (Fr & Fth & Ftl & Hr & Htab & Htl & Hband).
assert (I1 : 362 <= IZR (362 + i)) by (apply IZR_le; lia).
assert (I2 : IZR (363 + i) <= 724) by (apply IZR_le; lia).
assert (Hm2 : / 2 <= B2R m <= 2) by lra.
pose proof (FastLogCore.lc_band i r th tl m Hi Hm Hband (proj1 Hr)) as HB. clear Hband.
assert (Hrm : Rabs (B2R r * B2R m - 1) <= / 256).
{ destruct HB as [(R1 & _ & _ & H) | (_ & H & _)];
    [rewrite R1, Rmult_1_l; apply Rabs_le; lra | lra]. }
pose proof (ln_z_exact fma r m Fr Fm Hr Hm2 Hrm) as Hz. cbv zeta in Hz.
revert Hz.
destruct (Fast.fast_two_sum (sub (mul r m) DyadicExp.one) (Generic.two_prod_err fma r m (mul r m)))
  as [z1 z2].
cbv beta iota.
intros (Fz1 & Fz2 & Ez & Hz2 & Hz1 & Hr1).
destruct (FastLogCore.lc_z r th tl m z1 z2 HB Ez Hz2 Hr1) as [HZ _].
assert (Hz1' : B2R z1 = 0 \/ bpow radix2 (-200) <= Rabs (B2R z1)).
{ destruct Hz1 as [H | H]; [left; exact H | right].
  apply Rle_trans with (bpow radix2 (-106)); [apply bpow_le; lia | exact H]. }
pose proof (log1p_poly_acc_correct fma z1 z2 Fz1 Fz2 HZ Hz1' Hz2) as Hp.
revert Hp. destruct (DyadicLog.log1p_poly_acc fma z1 z2) as [ah pl]. cbv beta iota.
intros (Fah & Fpl & Hah & Hpl & Hpoly).
destruct (Fast.fast_two_sum th ah) as [u v] eqn:Euv.
destruct (Fast.fast_two_sum u (add v (add tl pl))) as [a_h a_l] eqn:Ea.
cbv beta iota.
(* [ln x - e ln 2 = ln m = ln(1 + z) - ln r]. *)
assert (Lx : ln (B2R x) - IZR e * ln 2 = ln (B2R m)).
{ rewrite Hx, ln_mult by first [lra | apply bpow_gt_0].
  rewrite bpow_exp, ln_exp. change (IZR (radix_val radix2)) with 2. ring. }
rewrite Lx.
assert (Hsmall : Rabs (ln (B2R m)) <= 7 / 20) by (apply FastLogCore.lc_ln_small; lra).
assert (Lm : ln (B2R m) = ln (1 + (B2R z1 + B2R z2)) - ln (B2R r)).
{ rewrite Ez. replace (1 + (B2R r * B2R m - 1)) with (B2R r * B2R m) by ring.
  rewrite ln_mult by lra. ring. }
pose proof (Rabs_pos (B2R z1)) as HZ0.
assert (B9 : bpow radix2 (-9) = / 512) by (cbn [bpow radix_val radix2]; lra).
destruct HB as [(R1 & T0 & L0 & Hm') | (Hth & Hrm3 & Hfar)].
- (* Around 1: [r = 1], [th = tl = 0] and [z2 = 0], so [u = ah], [v = 0]
     and [add v (add tl pl) = pl]; the error is that of
     [log1p_poly_acc], at most [7/4 2^-53 |z1|^4 + 2^-100 |z1| <= (7/8 +
     2^-21) 2^-79 |z1|] as [|z1| <= 2^-9], against [|ln(1 + z1)| >= |z1|
     (1 - 2^-9)]. *)
  pose proof (Hr1 R1) as Z20.
  pose proof (FastLogCore.lc_ln1p_lower (B2R z1) HZ) as Hlow.
  rewrite Z20, Rplus_0_r in Lm, Hpoly. rewrite Rabs_R0 in Hpoly.
  rewrite R1, ln_1, Rminus_0_r in Lm.
  rewrite B9 in HZ, Hah, Hlow.
  assert (HZ4 : Rabs (B2R z1) ^ 4 <= / 134217728 * Rabs (B2R z1)).
  { assert (Q2 : Rabs (B2R z1) * Rabs (B2R z1) <= / 262144) by nra.
    assert (Q3 : Rabs (B2R z1) * Rabs (B2R z1) * Rabs (B2R z1) <= / 134217728) by nra.
    replace (Rabs (B2R z1) ^ 4)
      with (Rabs (B2R z1) * Rabs (B2R z1) * Rabs (B2R z1) * Rabs (B2R z1)) by ring.
    nra. }
  cbn [bpow radix_val radix2] in Hpl, Hpoly.
  assert (Huv16 : Rabs (B2R th + B2R ah) <= 16) by (rewrite T0, Rplus_0_l; lra).
  destruct (FastLogCore.lc_fts th ah u v Fth Fah (or_intror T0) Huv16 Euv) as (Fu & Fv & Eu & Suv).
  assert (Eu' : B2R u = B2R ah).
  { rewrite Eu, T0, Rplus_0_l. apply round_generic; [typeclasses eauto|].
    apply generic_format_B2R. }
  assert (Ev : B2R v = 0) by lra.
  (* [|pl| <= |z1|^4 / 2 + 2^-51 |z1| <= |ah|]. *)
  assert (Hpl' : Rabs (B2R pl) <= Rabs (B2R z1) * (1 - / 512)) by lra.
  assert (Htp : Rabs (B2R tl + B2R pl) <= 16) by (rewrite L0, Rplus_0_l; lra).
  destruct (add_e tl pl Ftl Fpl Htp) as (Fw0 & Ew0 & _).
  assert (Ew0' : B2R (add tl pl) = B2R pl).
  { rewrite Ew0, L0, Rplus_0_l. apply round_generic; [typeclasses eauto|].
    apply generic_format_B2R. }
  assert (Hvw : Rabs (B2R v + B2R (add tl pl)) <= 16) by (rewrite Ev, Ew0', Rplus_0_l; lra).
  destruct (add_e v (add tl pl) Fv Fw0 Hvw) as (Fw & Ew & _).
  assert (Ew' : B2R (add v (add tl pl)) = B2R pl).
  { rewrite Ew, Ev, Ew0', Rplus_0_l. apply round_generic; [typeclasses eauto|].
    apply generic_format_B2R. }
  assert (Hle : Rabs (B2R (add v (add tl pl))) <= Rabs (B2R u)) by (rewrite Ew', Eu'; lra).
  assert (Huw : Rabs (B2R u + B2R (add v (add tl pl))) <= 16).
  { rewrite Ew', Eu'. pose proof (Rabs_triang (B2R ah) (B2R pl)). lra. }
  destruct (FastLogCore.lc_fts u _ a_h a_l Fu Fw (or_introl Hle) Huw Ea) as (Fa & Fb & Ea' & Sab).
  split; [exact Fa|]. split; [exact Fb|]. split; [rewrite Sab; exact Ea'|].
  split; [exact He|]. split; [exact Hsmall|].
  rewrite Sab, Ew', Eu', Lm.
  cbn [bpow radix_val radix2].
  lra.
- (* Elsewhere: [|ah| < 2^-9 <= |th|], so [u + v = th + ah]; the error is
     that of [log1p_poly_acc] with [|z1| <= 1465 10^-6], so [|z1|^4 <=
     4607 10^-15], the [2^-104] of the table, and those of the two
     roundings of [add v (add tl pl)], about [2^-88.75] in all, against
     [|ln m| >= 2^-9 (1 - 2^-9)]. *)
  pose proof (FastLogCore.lc_ln_far (B2R m) ltac:(lra) Hfar) as Hfar'.
  rewrite B9 in Hfar', Hth, HZ, Hah.
  assert (Zb : Rabs (B2R z1) <= 1465 / 1000000).
  { pose proof (FastLogCore.lc_tri (B2R z1) (B2R z1 + B2R z2) (- B2R z2) ltac:(ring)) as T.
    rewrite Rabs_Ropp, Ez in T. cbn [bpow radix_val radix2] in Hz2. lra. }
  assert (HZ4 : Rabs (B2R z1) ^ 4 <= 4607 / 1000000000000000).
  { apply Rle_trans with ((1465 / 1000000) ^ 4); [apply pow_incr; lra | cbn [pow]; lra]. }
  assert (Hz2Z : 512 / 511 * Rabs (B2R z2) * Rabs (B2R z1) ^ 3 <=
                 512 / 511 * bpow radix2 (-53) * Rabs (B2R z1) ^ 4).
  { replace (512 / 511 * bpow radix2 (-53) * Rabs (B2R z1) ^ 4)
      with (512 / 511 * (bpow radix2 (-53) * Rabs (B2R z1)) * Rabs (B2R z1) ^ 3) by ring.
    apply Rmult_le_compat_r; [apply pow_le, Rabs_pos | lra]. }
  assert (Hah9 : Rabs (B2R ah) <= Rabs (B2R th)) by lra.
  pose proof (Rabs_triang (B2R th) (B2R ah)) as T2.
  assert (Huv16 : Rabs (B2R th + B2R ah) <= 16) by lra.
  destruct (FastLogCore.lc_fts th ah u v Fth Fah (or_introl Hah9) Huv16 Euv)
    as (Fu & Fv & Eu & Suv).
  assert (Hu : Rabs (B2R u - (B2R th + B2R ah)) <=
               bpow radix2 (-53) * Rabs (B2R th + B2R ah) + bpow radix2 (-1075))
    by (rewrite Eu; apply rn_err).
  pose proof (FastLogCore.lc_tri (B2R th) (B2R th + B2R ah) (- B2R ah) ltac:(ring)) as T1.
  rewrite Rabs_Ropp in T1.
  pose proof (FastLogCore.lc_tri (B2R th + B2R ah) (B2R u) (- (B2R u - (B2R th + B2R ah)))
    ltac:(ring)) as T3.
  rewrite Rabs_Ropp in T3.
  assert (Ev : Rabs (B2R v) = Rabs (B2R u - (B2R th + B2R ah)))
    by (rewrite <- Rabs_Ropp; f_equal; lra).
  assert (Htl' : Rabs (B2R tl) <= bpow radix2 (-53) * (3 / 8)).
  { apply Rle_trans with (1 := Htl). apply Rmult_le_compat_l; [apply bpow_ge_0 | lra]. }
  pose proof (Rabs_triang (B2R tl) (B2R pl)) as T5.
  cbn [bpow radix_val radix2] in Hpl, Htl', Hu, Hpoly, Hz2Z, Htab.
  assert (Htp : Rabs (B2R tl + B2R pl) <= 16) by lra.
  destruct (add_e tl pl Ftl Fpl Htp) as (Fw0 & _ & Hw0).
  set (w0 := add tl pl) in *.
  pose proof (FastLogCore.lc_tri (B2R w0) (B2R tl + B2R pl) (B2R w0 - (B2R tl + B2R pl))
    ltac:(ring)) as T6.
  pose proof (Rabs_triang (B2R v) (B2R w0)) as T7.
  cbn [bpow radix_val radix2] in Hw0.
  assert (Hvw : Rabs (B2R v + B2R w0) <= 16) by lra.
  destruct (add_e v w0 Fv Fw0 Hvw) as (Fw & _ & Hw).
  set (w := add v w0) in *.
  pose proof (FastLogCore.lc_tri (B2R w) (B2R v + B2R w0) (B2R w - (B2R v + B2R w0))
    ltac:(ring)) as T8.
  pose proof (Rabs_triang (B2R u) (B2R w)) as T9.
  cbn [bpow radix_val radix2] in Hw.
  assert (Hle : Rabs (B2R w) <= Rabs (B2R u)) by lra.
  pose proof (FastLogCore.lc_tri (B2R u) (B2R th + B2R ah) (B2R u - (B2R th + B2R ah))
    ltac:(ring)) as T4.
  assert (Huw : Rabs (B2R u + B2R w) <= 16) by lra.
  destruct (FastLogCore.lc_fts u w a_h a_l Fu Fw (or_introl Hle) Huw Ea) as (Fa & Fb & Ea' & Sab).
  split; [exact Fa|]. split; [exact Fb|]. split; [rewrite Sab; exact Ea'|].
  split; [exact He|]. split; [exact Hsmall|].
  rewrite Sab.
  (* [ln m - (u + w)] is [(ln(1 + z) - (ah + pl)) - (th + tl + ln r) -
     (w0 - (tl + pl)) - (w - (v + w0))], as [u + v = th + ah]. *)
  pose proof Hpoly as Hpoly'. pose proof Htab as Htab'.
  pose proof Hw0 as Hw0'. pose proof Hw as Hw'.
  apply Rabs_le_inv in Hpoly', Htab', Hw0', Hw'.
  cbn [bpow radix_val radix2].
  apply Rabs_le. split; lra.
Qed.

Theorem ln_core_acc_fma :
  forall x, is_finite x = true -> 0 < B2R x ->
  DyadicLog.ln_core_acc true x = DyadicLog.ln_core_acc false x.
Proof.
intros x Fx Px.
pose proof (ln_split_correct x Fx Px) as Hs.
unfold DyadicLog.ln_core_acc.
revert Hs. destruct (DyadicLog.ln_split x) as [[e m] i]. cbv beta iota.
intros (Fm & Hi & _ & _ & Hm).
pose proof (ltbl_correct i Hi) as Ht.
revert Ht. destruct (DyadicLog.ltbl i) as [[r th] tl]. cbv beta iota zeta.
intros (Fr & _ & _ & Hr & _ & _ & Hband).
assert (I1 : 362 <= IZR (362 + i)) by (apply IZR_le; lia).
assert (I2 : IZR (363 + i) <= 724) by (apply IZR_le; lia).
assert (Hm2 : / 2 <= B2R m <= 2) by lra.
pose proof (FastLogCore.lc_band i r th tl m Hi Hm Hband (proj1 Hr)) as HB. clear Hband.
assert (Hrm : Rabs (B2R r * B2R m - 1) <= / 256).
{ destruct HB as [(R1 & _ & _ & H) | (_ & H & _)];
    [rewrite R1, Rmult_1_l; apply Rabs_le; lra | lra]. }
rewrite (ln_z_fma r m Fr Fm Hr Hm2 Hrm).
pose proof (ln_z_exact false r m Fr Fm Hr Hm2 Hrm) as Hz. cbv zeta in Hz.
revert Hz.
destruct (Fast.fast_two_sum (sub (mul r m) DyadicExp.one) (Generic.two_prod_err false r m (mul r m)))
  as [z1 z2].
cbv beta iota.
intros (Fz1 & _ & Ez & Hz2 & Hz1 & Hr1).
destruct (FastLogCore.lc_z r th tl m z1 z2 HB Ez Hz2 Hr1) as [HZ _].
assert (Hz1' : B2R z1 = 0 \/ bpow radix2 (-200) <= Rabs (B2R z1)).
{ destruct Hz1 as [H | H]; [left; exact H | right].
  apply Rle_trans with (bpow radix2 (-106)); [apply bpow_le; lia | exact H]. }
rewrite (log1p_poly_acc_fma z1 z2 Fz1 HZ Hz1'). reflexivity.
Qed.
