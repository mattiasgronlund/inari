(** * The core of the fast path of the logarithms

    [DyadicLog.ln_core] of [Model.v] returns, for a finite [x > 0], [e]
    and [ah + al] within [3 2^-71 |ln m|] of ln m, for [m = x 2^-e] in
    [[0.707, 1.415)], with [ah = RN(ah + al)] ([ln_core_correct]): ln m
    = -ln r + ln(1 + z) for the [r] of the table ([FastLogTables.v]) and
    [z = r m - 1] ([FastLogReduce.v]), with ln(1 + z) by
    [DyadicLog.log1p_poly] ([FastLogPoly.v]). Away from 1, [|ln m| >=
    2^-9] and the errors are absolute, at most about [2^-78.8]; on the
    two intervals around 1, [r = 1], [z = m - 1] exactly and the error is
    relative to [|z|]. [ln_core_fma] shows that an FMA gives the same
    result.

    The two sums of two [f64]s that [ln_core] does not round are exact by
    Fast2Sum [Dekker]: the first because [|th| >= 2^-9 > |ah|] away from
    1, and [th = 0] on the two intervals around 1.

    [Dekker] T. J. Dekker, A floating-point technique for extending the
    available precision, Numer. Math. 18 (1971). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct CancelLanes ExpSeries FastRound
  FastExpErr FastLogTables FastLogTaylor FastLogPoly FastLogReduce.

Open Scope R_scope.

(** ** Facts on reals *)

Local Lemma lc_tri : forall a b c, a = b + c -> Rabs a <= Rabs b + Rabs c.
Proof. intros a b c ->. apply Rabs_triang. Qed.

Local Lemma lc_ln_le : forall a b, 0 < a -> a <= b -> ln a <= ln b.
Proof.
intros a b Ha [H | <-]; [apply Rlt_le, ln_increasing; assumption | apply Rle_refl].
Qed.

(** [e^-y] is at most the alternating sum of degree 4 for [0 <= y <= 1]
    ([exp_alt_bounds]). *)
Local Lemma lc_exp_neg :
  forall y, 0 <= y <= 1 -> exp (- y) <= 1 - y + y ^ 2 / 2 - y ^ 3 / 6 + y ^ 4 / 24.
Proof.
intros y Hy. destruct (exp_alt_bounds y 2 Hy) as [_ Hu].
replace (sum_f_R0 (tg_alt (exp_tg y)) (2 * 2)) with (1 - y + y ^ 2 / 2 - y ^ 3 / 6 + y ^ 4 / 24)
  in Hu by (unfold tg_alt, exp_tg; cbn; field).
exact Hu.
Qed.

(** [|ln m| <= 7/20] on [[362/512, 724/512]], as [e^-0.35 <= 0.7048]
    and [0.7048 * 724/512 < 1]. *)
Local Lemma lc_ln_small : forall m, 362 / 512 <= m <= 724 / 512 -> Rabs (ln m) <= 7 / 20.
Proof.
intros m Hm.
pose proof (lc_exp_neg (7 / 20) ltac:(lra)) as He.
assert (Hq : exp (- (7 / 20)) <= 7048 / 10000) by (eapply Rle_trans; [exact He | lra]).
pose proof (exp_pos (- (7 / 20))) as Hq0.
pose proof (exp_pos (7 / 20)) as Hp0.
assert (Ep : exp (7 / 20) * exp (- (7 / 20)) = 1)
  by (rewrite <- exp_plus; replace (7 / 20 + - (7 / 20)) with 0 by ring; apply exp_0).
apply Rabs_le; split.
- rewrite <- (ln_exp (- (7 / 20))). apply lc_ln_le; lra.
- rewrite <- (ln_exp (7 / 20)). apply lc_ln_le; [lra|].
  assert (Hmq : m * exp (- (7 / 20)) <= 1) by nra.
  assert (E : m = m * exp (- (7 / 20)) * exp (7 / 20))
    by (rewrite Rmult_assoc, (Rmult_comm (exp _)), Ep; ring).
  rewrite E. rewrite <- (Rmult_1_l (exp (7 / 20))) at 2.
  apply Rmult_le_compat_r; lra.
Qed.

(** [|ln(1 + z)| >= |z| (1 - 2^-9)] for [|z| <= 2^-9]: the Taylor
    polynomial of degree 1 is within [|z|^2 / (2 (1 - |z|)) <= 2^-9 |z|]
    ([log1p_taylor]). *)
Local Lemma lc_ln1p_lower :
  forall z, Rabs z <= bpow radix2 (-9) -> Rabs z * (1 - bpow radix2 (-9)) <= Rabs (ln (1 + z)).
Proof.
intros z Hz.
assert (Hb : bpow radix2 (-9) = / 512) by (cbn [bpow radix_val radix2]; lra).
rewrite Hb in Hz |- *.
pose proof (Rabs_pos z) as HZ0.
pose proof (log1p_taylor 1 z ltac:(lra)) as H.
replace (log1p_sum 1 z) with z in H by (cbn; field).
replace (INR (S 1)) with 2 in H by (cbn; ring).
assert (Hq : Rabs z ^ 2 / (2 * (1 - Rabs z)) <= Rabs z * / 512).
{ apply (Rmult_le_reg_r (2 * (1 - Rabs z))); [lra|].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra. }
pose proof (lc_tri z (ln (1 + z)) (z - ln (1 + z)) ltac:(ring)) as T.
rewrite Rabs_minus_sym in T.
lra.
Qed.

(** [|ln m| >= 2^-9 (1 - 2^-9)] for [m] outside [[511/512, 513/512)]. *)
Local Lemma lc_ln_far :
  forall m, 0 < m -> (m < 511 / 512 \/ 513 / 512 <= m) ->
  bpow radix2 (-9) * (1 - bpow radix2 (-9)) <= Rabs (ln m).
Proof.
intros m Hm0 Hm.
assert (Hb : bpow radix2 (-9) = / 512) by (cbn [bpow radix_val radix2]; lra).
destruct Hm as [Hm | Hm].
- assert (Hz : Rabs (- bpow radix2 (-9)) <= bpow radix2 (-9))
    by (rewrite Rabs_Ropp, Rabs_pos_eq by apply bpow_ge_0; apply Rle_refl).
  pose proof (lc_ln1p_lower _ Hz) as H.
  rewrite Rabs_Ropp, Rabs_pos_eq in H by apply bpow_ge_0.
  rewrite Hb in H |- *.
  assert (L1 : ln m <= ln (1 + - / 512)) by (apply lc_ln_le; lra).
  assert (L2 : ln (1 + - / 512) < 0) by (rewrite <- ln_1; apply ln_increasing; lra).
  rewrite Rabs_left in H by lra. rewrite Rabs_left by lra. lra.
- assert (Hz : Rabs (bpow radix2 (-9)) <= bpow radix2 (-9))
    by (rewrite Rabs_pos_eq by apply bpow_ge_0; apply Rle_refl).
  pose proof (lc_ln1p_lower _ Hz) as H.
  rewrite Rabs_pos_eq in H by apply bpow_ge_0.
  rewrite Hb in H |- *.
  assert (L1 : ln (1 + / 512) <= ln m) by (apply lc_ln_le; lra).
  assert (L2 : 0 < ln (1 + / 512)) by (rewrite <- ln_1; apply ln_increasing; lra).
  rewrite Rabs_pos_eq in H by lra. rewrite Rabs_pos_eq by lra. lra.
Qed.

(** ** Fast2Sum *)

(** [Fast.fast_two_sum a b] is exact when [|b| <= |a|] ([CancelLanes.fast_two_sum])
    or [a = 0], where it returns [(b, 0)]. *)
Local Lemma lc_fts :
  forall a b s t, is_finite a = true -> is_finite b = true ->
  (Rabs (B2R b) <= Rabs (B2R a) \/ B2R a = 0) -> Rabs (B2R a + B2R b) <= 16 ->
  Fast.fast_two_sum a b = (s, t) ->
  is_finite s = true /\ is_finite t = true /\ B2R s = RN (B2R a + B2R b) /\
  B2R s + B2R t = B2R a + B2R b.
Proof.
intros a b s t Fa Fb Hab H16 E.
unfold Fast.fast_two_sum in E. injection E as <- <-.
destruct (add_e a b Fa Fb H16) as (Fs & Es & _).
destruct Hab as [Hab | Ha0].
- destruct (fast_two_sum a b (add a b) Fa Fb Hab Fs Es) as [Ft Et].
  do 3 (split; [assumption|]). rewrite Et. ring.
- assert (Es' : B2R (add a b) = B2R b).
  { rewrite Es, Ha0, Rplus_0_l. apply round_generic; [typeclasses eauto|].
    apply generic_format_B2R. }
  assert (Hd16 : Rabs (B2R a - B2R (add a b)) <= 16)
    by (rewrite Es', Ha0, Rminus_0_l, Rabs_Ropp; rewrite Ha0, Rplus_0_l in H16; exact H16).
  destruct (sub_e a (add a b) Fa Fs Hd16) as (Fd & Ed & _).
  assert (Ed' : B2R (sub a (add a b)) = - B2R b).
  { rewrite Ed, Es', Ha0, Rminus_0_l. apply round_generic; [typeclasses eauto|].
    apply generic_format_opp, generic_format_B2R. }
  assert (Ht16 : Rabs (B2R b + B2R (sub a (add a b))) <= 16)
    by (rewrite Ed', Rplus_opp_r, Rabs_R0; lra).
  destruct (add_e b (sub a (add a b)) Fb Fd Ht16) as (Ft & Et & _).
  rewrite Ed', Rplus_opp_r, round_0 in Et by typeclasses eauto.
  do 3 (split; [assumption|]). rewrite Es', Et, Ha0. ring.
Qed.

(** ** The table *)

(** The two cases of an entry of the table: on the two intervals around
    1, [r = 1] and [th = tl = 0]; elsewhere [|th| >= 2^-9], [r m] is
    within [3/2048] of 1 and [m] is outside [[511/512, 513/512)]. *)
Local Definition lc_cases (r th tl m : R) : Prop :=
  (r = 1 /\ th = 0 /\ tl = 0 /\ 511 / 512 <= m < 513 / 512) \/
  (bpow radix2 (-9) <= Rabs th <= 3 / 8 /\ Rabs (r * m - 1) <= 3 / 2048 /\
   (m < 511 / 512 \/ 513 / 512 <= m)).

(** [ltbl_correct] for an [m] in the interval of entry [i]: [r m] lies
    between [r] times the ends of the interval, as [r > 0]. *)
Local Lemma lc_band :
  forall i (r th tl m : f64), (0 <= i < 362)%Z ->
  IZR (362 + i) / 512 <= B2R m < IZR (363 + i) / 512 ->
  (if (i =? 149)%Z || (i =? 150)%Z then B2R r = 1 /\ B2R th = 0 /\ B2R tl = 0
   else
     bpow radix2 (-9) <= Rabs (B2R th) <= 3 / 8 /\
     Rabs (B2R r * (IZR (362 + i) / 512) - 1) <= 3 / 2048 /\
     Rabs (B2R r * (IZR (363 + i) / 512) - 1) <= 3 / 2048) ->
  / 2 <= B2R r ->
  lc_cases (B2R r) (B2R th) (B2R tl) (B2R m).
Proof.
intros i r th tl m Hi Hm Hband Hr.
unfold lc_cases.
destruct ((i =? 149)%Z || (i =? 150)%Z) eqn:Band.
- left. destruct Hband as (R1 & T0 & L0). do 3 (split; [assumption|]).
  apply Bool.orb_true_iff in Band.
  assert (Hi' : i = 149%Z \/ i = 150%Z) by (destruct Band as [B|B]; apply Z.eqb_eq in B; lia).
  assert (J1 : 511 <= IZR (362 + i)) by (apply IZR_le; lia).
  assert (J2 : IZR (363 + i) <= 513) by (apply IZR_le; lia).
  lra.
- right. destruct Hband as (Hth & H1 & H2). split; [exact Hth|].
  apply Bool.orb_false_iff in Band. destruct Band as [B1 B2].
  apply Z.eqb_neq in B1, B2.
  split.
  + assert (Hlo : B2R r * (IZR (362 + i) / 512) <= B2R r * B2R m)
      by (apply Rmult_le_compat_l; lra).
    assert (Hhi : B2R r * B2R m <= B2R r * (IZR (363 + i) / 512))
      by (apply Rmult_le_compat_l; lra).
    apply Rabs_le_inv in H1, H2. apply Rabs_le. lra.
  + destruct (Z_lt_le_dec i 150) as [L | L].
    * left. assert (IZR (363 + i) <= 511) by (apply IZR_le; lia). lra.
    * right. assert (513 <= IZR (362 + i)) by (apply IZR_le; lia). lra.
Qed.

(** [|r m - 1| <= 2^-9] in both cases, so [|z1| <= 2^-9]: on the two
    intervals around 1, [z2 = 0] and [z1 = m - 1]; elsewhere [|z1| <= 3/2048
    + |z2|] with [|z2| <= 2^-53 |z1|]. *)
Local Lemma lc_z :
  forall r th tl m z1 z2 : f64,
  lc_cases (B2R r) (B2R th) (B2R tl) (B2R m) ->
  B2R z1 + B2R z2 = B2R r * B2R m - 1 ->
  Rabs (B2R z2) <= bpow radix2 (-53) * Rabs (B2R z1) -> (B2R r = 1 -> B2R z2 = 0) ->
  Rabs (B2R z1) <= bpow radix2 (-9) /\ Rabs (B2R r * B2R m - 1) <= / 256.
Proof.
intros r th tl m z1 z2 HB Ez Hz2 Hr1.
assert (Hb : bpow radix2 (-9) = / 512) by (cbn [bpow radix_val radix2]; lra).
rewrite Hb.
destruct HB as [(R1 & _ & _ & Hm) | (_ & H & _)].
- rewrite (Hr1 R1), Rplus_0_r, R1, Rmult_1_l in Ez. rewrite R1, Rmult_1_l, <- Ez.
  split; apply Rabs_le; lra.
- pose proof (lc_tri (B2R z1) (B2R z1 + B2R z2) (- B2R z2) ltac:(ring)) as T.
  rewrite Rabs_Ropp, Ez in T.
  cbn [bpow radix_val radix2] in Hz2. split; lra.
Qed.

(** ** The core *)

Theorem ln_core_correct :
  forall fma x, is_finite x = true -> 0 < B2R x ->
  let '(e, ah, al) := DyadicLog.ln_core fma x in
  is_finite ah = true /\ is_finite al = true /\ B2R ah = RN (B2R ah + B2R al) /\
  (-1074 <= e <= 1024)%Z /\ Rabs (ln (B2R x) - IZR e * ln 2) <= 7 / 20 /\
  Rabs (ln (B2R x) - IZR e * ln 2 - (B2R ah + B2R al)) <=
    3 * bpow radix2 (-71) * Rabs (ln (B2R x) - IZR e * ln 2).
Proof.
intros fma x Fx Px.
pose proof (ln_split_correct x Fx Px) as Hs.
unfold DyadicLog.ln_core.
revert Hs. destruct (DyadicLog.ln_split x) as [[e m] i]. cbv beta iota.
intros (Fm & Hi & He & Hx & Hm).
pose proof (ltbl_correct i Hi) as Ht.
revert Ht. destruct (DyadicLog.ltbl i) as [[r th] tl]. cbv beta iota zeta.
intros (Fr & Fth & Ftl & Hr & Htab & Htl & Hband).
assert (I1 : 362 <= IZR (362 + i)) by (apply IZR_le; lia).
assert (I2 : IZR (363 + i) <= 724) by (apply IZR_le; lia).
assert (Hm2 : / 2 <= B2R m <= 2) by lra.
pose proof (lc_band i r th tl m Hi Hm Hband (proj1 Hr)) as HB. clear Hband.
assert (Hrm : Rabs (B2R r * B2R m - 1) <= / 256).
{ destruct HB as [(R1 & _ & _ & H) | (_ & H & _)];
    [rewrite R1, Rmult_1_l; apply Rabs_le; lra | lra]. }
pose proof (ln_z_exact fma r m Fr Fm Hr Hm2 Hrm) as Hz. cbv zeta in Hz.
revert Hz.
destruct (Fast.fast_two_sum (sub (mul r m) DyadicExp.one) (Generic.two_prod_err fma r m (mul r m)))
  as [z1 z2].
cbv beta iota.
intros (Fz1 & Fz2 & Ez & Hz2 & Hz1 & Hr1).
destruct (lc_z r th tl m z1 z2 HB Ez Hz2 Hr1) as [HZ _].
assert (Hz1' : B2R z1 = 0 \/ bpow radix2 (-200) <= Rabs (B2R z1)).
{ destruct Hz1 as [H | H]; [left; exact H | right].
  apply Rle_trans with (bpow radix2 (-106)); [apply bpow_le; lia | exact H]. }
pose proof (log1p_poly_correct fma z1 z2 Fz1 Fz2 HZ Hz1' Hz2) as Hp.
revert Hp. destruct (DyadicLog.log1p_poly fma z1 z2) as [ah pl]. cbv beta iota.
intros (Fah & Fpl & Hah & Hpl & Hpoly).
destruct (Fast.fast_two_sum th ah) as [u v] eqn:Euv.
destruct (Fast.fast_two_sum u (add v (add tl pl))) as [a_h a_l] eqn:Ea.
cbv beta iota.
(* [ln x - e ln 2 = ln m = ln(1 + z) - ln r]. *)
assert (Lx : ln (B2R x) - IZR e * ln 2 = ln (B2R m)).
{ rewrite Hx, ln_mult by first [lra | apply bpow_gt_0].
  rewrite bpow_exp, ln_exp. change (IZR (radix_val radix2)) with 2. ring. }
rewrite Lx.
assert (Hsmall : Rabs (ln (B2R m)) <= 7 / 20) by (apply lc_ln_small; lra).
assert (Lm : ln (B2R m) = ln (1 + (B2R z1 + B2R z2)) - ln (B2R r)).
{ rewrite Ez. replace (1 + (B2R r * B2R m - 1)) with (B2R r * B2R m) by ring.
  rewrite ln_mult by lra. ring. }
pose proof (Rabs_pos (B2R z1)) as HZ0.
assert (B9 : bpow radix2 (-9) = / 512) by (cbn [bpow radix_val radix2]; lra).
destruct HB as [(R1 & T0 & L0 & Hm') | (Hth & Hrm3 & Hfar)].
- (* Around 1: [r = 1], [th = tl = 0] and [z2 = 0], so [u = ah], [v = 0]
     and [add v (add tl pl) = pl]; the error is that of [log1p_poly],
     relative to [|z1|]. *)
  pose proof (Hr1 R1) as Z20.
  pose proof (lc_ln1p_lower (B2R z1) HZ) as Hlow.
  rewrite Z20, Rplus_0_r in Lm, Hpoly. rewrite Rabs_R0 in Hpoly.
  rewrite R1, ln_1, Rminus_0_r in Lm.
  rewrite B9 in HZ, Hah, Hlow.
  assert (HZ3 : Rabs (B2R z1) ^ 3 <= / 262144 * Rabs (B2R z1)).
  { assert (Rabs (B2R z1) * Rabs (B2R z1) <= / 262144) by nra.
    replace (Rabs (B2R z1) ^ 3) with (Rabs (B2R z1) * Rabs (B2R z1) * Rabs (B2R z1)) by ring.
    nra. }
  cbn [bpow radix_val radix2] in Hpl, Hpoly.
  assert (Huv16 : Rabs (B2R th + B2R ah) <= 16) by (rewrite T0, Rplus_0_l; lra).
  destruct (lc_fts th ah u v Fth Fah (or_intror T0) Huv16 Euv) as (Fu & Fv & Eu & Suv).
  assert (Eu' : B2R u = B2R ah).
  { rewrite Eu, T0, Rplus_0_l. apply round_generic; [typeclasses eauto|].
    apply generic_format_B2R. }
  assert (Ev : B2R v = 0) by lra.
  (* [|pl| <= |z1|^3 / 2 + 2^-51 |z1| <= |ah|]. *)
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
  destruct (lc_fts u _ a_h a_l Fu Fw (or_introl Hle) Huw Ea) as (Fa & Fb & Ea' & Sab).
  split; [exact Fa|]. split; [exact Fb|]. split; [rewrite Sab; exact Ea'|].
  split; [exact He|]. split; [exact Hsmall|].
  rewrite Sab, Ew', Eu', Lm.
  cbn [bpow radix_val radix2].
  lra.
- (* Elsewhere: [|ah| < 2^-9 <= |th|], so [u + v = th + ah]; the error is
     that of [log1p_poly] with [|z1| <= 1465 10^-6], the [2^-104] of the
     table, and those of the two roundings of [add v (add tl pl)], against
     [|ln m| >= 2^-9 (1 - 2^-9)]. *)
  pose proof (lc_ln_far (B2R m) ltac:(lra) Hfar) as Hfar'.
  rewrite B9 in Hfar', Hth, HZ, Hah.
  assert (Zb : Rabs (B2R z1) <= 1465 / 1000000).
  { pose proof (lc_tri (B2R z1) (B2R z1 + B2R z2) (- B2R z2) ltac:(ring)) as T.
    rewrite Rabs_Ropp, Ez in T. cbn [bpow radix_val radix2] in Hz2. lra. }
  assert (HZ3 : Rabs (B2R z1) ^ 3 <= 315 / 100000000000).
  { apply Rle_trans with ((1465 / 1000000) ^ 3); [apply pow_incr; lra | cbn [pow]; lra]. }
  assert (Hz2Z : 2 * Rabs (B2R z2) * Rabs (B2R z1) ^ 2 <=
                 2 * bpow radix2 (-53) * Rabs (B2R z1) ^ 3).
  { replace (2 * bpow radix2 (-53) * Rabs (B2R z1) ^ 3)
      with (2 * (bpow radix2 (-53) * Rabs (B2R z1)) * Rabs (B2R z1) ^ 2) by ring.
    apply Rmult_le_compat_r; [apply pow_le, Rabs_pos | lra]. }
  assert (Hah9 : Rabs (B2R ah) <= Rabs (B2R th)) by lra.
  pose proof (Rabs_triang (B2R th) (B2R ah)) as T2.
  assert (Huv16 : Rabs (B2R th + B2R ah) <= 16) by lra.
  destruct (lc_fts th ah u v Fth Fah (or_introl Hah9) Huv16 Euv) as (Fu & Fv & Eu & Suv).
  assert (Hu : Rabs (B2R u - (B2R th + B2R ah)) <=
               bpow radix2 (-53) * Rabs (B2R th + B2R ah) + bpow radix2 (-1075))
    by (rewrite Eu; apply rn_err).
  pose proof (lc_tri (B2R th) (B2R th + B2R ah) (- B2R ah) ltac:(ring)) as T1.
  rewrite Rabs_Ropp in T1.
  pose proof (lc_tri (B2R th + B2R ah) (B2R u) (- (B2R u - (B2R th + B2R ah))) ltac:(ring)) as T3.
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
  pose proof (lc_tri (B2R w0) (B2R tl + B2R pl) (B2R w0 - (B2R tl + B2R pl)) ltac:(ring)) as T6.
  pose proof (Rabs_triang (B2R v) (B2R w0)) as T7.
  cbn [bpow radix_val radix2] in Hw0.
  assert (Hvw : Rabs (B2R v + B2R w0) <= 16) by lra.
  destruct (add_e v w0 Fv Fw0 Hvw) as (Fw & _ & Hw).
  set (w := add v w0) in *.
  pose proof (lc_tri (B2R w) (B2R v + B2R w0) (B2R w - (B2R v + B2R w0)) ltac:(ring)) as T8.
  pose proof (Rabs_triang (B2R u) (B2R w)) as T9.
  cbn [bpow radix_val radix2] in Hw.
  assert (Hle : Rabs (B2R w) <= Rabs (B2R u)) by lra.
  pose proof (lc_tri (B2R u) (B2R th + B2R ah) (B2R u - (B2R th + B2R ah)) ltac:(ring)) as T4.
  assert (Huw : Rabs (B2R u + B2R w) <= 16) by lra.
  destruct (lc_fts u w a_h a_l Fu Fw (or_introl Hle) Huw Ea) as (Fa & Fb & Ea' & Sab).
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

Theorem ln_core_fma :
  forall x, is_finite x = true -> 0 < B2R x -> DyadicLog.ln_core true x = DyadicLog.ln_core false x.
Proof.
intros x Fx Px.
pose proof (ln_split_correct x Fx Px) as Hs.
unfold DyadicLog.ln_core.
revert Hs. destruct (DyadicLog.ln_split x) as [[e m] i]. cbv beta iota.
intros (Fm & Hi & _ & _ & Hm).
pose proof (ltbl_correct i Hi) as Ht.
revert Ht. destruct (DyadicLog.ltbl i) as [[r th] tl]. cbv beta iota zeta.
intros (Fr & _ & _ & Hr & _ & _ & Hband).
assert (I1 : 362 <= IZR (362 + i)) by (apply IZR_le; lia).
assert (I2 : IZR (363 + i) <= 724) by (apply IZR_le; lia).
assert (Hm2 : / 2 <= B2R m <= 2) by lra.
pose proof (lc_band i r th tl m Hi Hm Hband (proj1 Hr)) as HB. clear Hband.
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
destruct (lc_z r th tl m z1 z2 HB Ez Hz2 Hr1) as [HZ _].
assert (Hz1' : B2R z1 = 0 \/ bpow radix2 (-200) <= Rabs (B2R z1)).
{ destruct Hz1 as [H | H]; [left; exact H | right].
  apply Rle_trans with (bpow radix2 (-106)); [apply bpow_le; lia | exact H]. }
rewrite (log1p_poly_fma z1 z2 Fz1 HZ Hz1'). reflexivity.
Qed.
