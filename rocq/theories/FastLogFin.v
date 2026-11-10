(** * Shared steps of the fast paths of [ln], [log2] and [log10]

    Moved from [FastLogLn.v] for [FastLogBy.v] (rule P2: both proofs
    need them). [fl_finish] takes [|y| <= 1100] and [y = 0] or [|y| >=
    2^-56], so that it covers [log2] (up to [1074]) and [log10] near 1
    (at least [2^-54 / ln 10] in absolute value) as well as [ln]: the last Fast2Sum is
    exact and [normalize_correct] of [FastLogNorm.v] applies. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct FastRound FastLogNorm
  FastExpErr.

Open Scope R_scope.

Lemma fl_tri : forall a b c, a = b + c -> Rabs a <= Rabs b + Rabs c.
Proof. intros a b c ->. apply Rabs_triang. Qed.

Lemma fl_max : 2048 <= MAX.
Proof.
assert (H1 : bpow radix2 971 <= bpow radix2 1023) by (apply bpow_le; lia).
assert (H2 : bpow radix2 11 <= bpow radix2 1023) by (apply bpow_le; lia).
assert (H3 : bpow radix2 1024 = 2 * bpow radix2 1023).
{ replace 1024%Z with (1 + 1023)%Z by lia. rewrite bpow_plus. reflexivity. }
assert (H4 : bpow radix2 11 = 2048) by reflexivity.
lra.
Qed.

(** [e as f64] is [e] for [|e| < 2^53], as [DyPowCore.of_i64_exact]
    shows for the same function of [DyadicPow], after this file. *)
Lemma fl_of_i64 :
  forall k, (Z.abs k < 2 ^ 53)%Z ->
  is_finite (DyadicLog.of_i64 k) = true /\ B2R (DyadicLog.of_i64 k) = IZR k.
Proof.
intros k Hk.
assert (Fk : generic_format radix2 (SpecFloat.fexp 53 1024) (IZR k)).
{ change (SpecFloat.fexp 53 1024) with (FLT_exp (-1074) 53).
  apply generic_format_FLT, (FLT_spec _ _ _ _ (Float radix2 k 0)).
  - unfold F2R; cbn [Fnum Fexp bpow]. ring.
  - cbn [Fnum radix_val radix2]. exact Hk.
  - cbn [Fexp]. lia. }
unfold DyadicLog.of_i64.
pose proof (binary_normalize_correct 53 1024 prec_gt_0_53 prec_lt_emax_53_1024
  mode_NE k 0 false) as H.
cbv zeta in H.
replace (F2R (Float radix2 k 0)) with (IZR k) in H by (unfold F2R; cbn [Fnum Fexp bpow]; ring).
rewrite (round_generic _ _ _ (IZR k) Fk) in H.
rewrite Rlt_bool_true in H.
2: { rewrite <- abs_IZR.
  apply Rlt_trans with (IZR (2 ^ 53)); [apply IZR_lt; exact Hk|].
  rewrite (IZR_Zpower radix2) by lia. apply bpow_lt. lia. }
destruct H as (HR & HF & _). split; [exact HF | exact HR].
Qed.

(** [|b| <= |a|] or [a = 0] where [a = RN(a + b)]: [|b| <= 2^-53 |a + b|
    + 2^-1075], and [|a| >= 2^-1074] if [a <> 0]. *)
Lemma fl_low :
  forall a b : f64, B2R a = RN (B2R a + B2R b) -> Rabs (B2R b) <= Rabs (B2R a) \/ B2R a = 0.
Proof.
intros a b E.
destruct (Req_dec (B2R a) 0) as [Z|Z]; [right; exact Z | left].
assert (Ha : bpow radix2 (-1074) <= Rabs (B2R a)).
{ apply generic_format_ge_bpow with (fexp := fexp64).
  - intros e'. unfold FLT_exp. lia.
  - apply Rabs_pos_lt, Z.
  - apply generic_format_abs, generic_format_B2R. }
pose proof (rn_err (B2R a + B2R b)) as H. rewrite <- E in H.
replace (B2R a - (B2R a + B2R b)) with (- B2R b) in H by ring. rewrite Rabs_Ropp in H.
pose proof (Rabs_triang (B2R a) (B2R b)) as T.
assert (B : bpow radix2 (-1074) = 2 * bpow radix2 (-1075)).
{ replace (-1074)%Z with (1 + -1075)%Z by lia. rewrite bpow_plus. reflexivity. }
assert (U : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
rewrite U in H.
pose proof (bpow_gt_0 radix2 (-1075)).
lra.
Qed.

(** [ln x] is [0] or at least [2^-54] in magnitude. *)
Lemma fl_y0 :
  forall x : f64, is_finite x = true -> 0 < B2R x ->
  ln (B2R x) = 0 \/ bpow radix2 (-54) <= Rabs (ln (B2R x)).
Proof.
intros x Fx Px.
destruct (Req_dec (B2R x) 1) as [X1|X1].
- left. rewrite X1. exact ln_1.
- right. exact (ln_f64_ne1 x Fx Px X1).
Qed.

(** [normalize h l] is [None] where [h] is a zero. *)
Lemma fl_norm_nz :
  forall h l r, is_finite h = true -> DyadicLog.normalize h l = Some r -> B2R h <> 0.
Proof.
intros h l r Fh E Z. unfold DyadicLog.normalize in E.
assert (Fz : is_finite Model.zero = true) by reflexivity.
assert (Q : Model.eq h Model.zero = true).
{ unfold Model.eq. rewrite Beqb_correct by assumption.
  destruct (Req_bool_spec (B2R h) (B2R Model.zero)) as [H | H]; [reflexivity|].
  change (B2R Model.zero) with 0 in H. contradiction. }
rewrite Q in E. discriminate E.
Qed.

(** ** The last Fast2Sum and the normalisation

    If [s + w] is [y] within [4/5 2^-69 |y|], with [y = 0] or [|y| >=
    2^-56], then [h = RN(s + w)] is [y] within a factor [1 +- 2^-52], and
    [normalize_correct] applies. *)
Lemma fl_finish :
  forall s w h0 l0 h l k y,
  is_finite s = true -> is_finite w = true ->
  (Rabs (B2R w) <= Rabs (B2R s) \/ B2R s = 0) ->
  Rabs y <= 1100 -> (y = 0 \/ bpow radix2 (-56) <= Rabs y) ->
  Rabs (y - (B2R s + B2R w)) <= 4 / 5 * bpow radix2 (-69) * Rabs y ->
  Fast.fast_two_sum s w = (h0, l0) -> DyadicLog.normalize h0 l0 = Some (h, l, k) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < Rabs (B2R h) < 2 /\ (-1021 <= k <= 1022)%Z /\
  Rabs (y * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-68).
Proof.
intros s w h0 l0 h l k y Fs Fw Hsw Hy Hy0 Herr E2 E.
assert (B69 : bpow radix2 (-69) = / 590295810358705651712) by reflexivity.
assert (B56 : bpow radix2 (-56) = / 72057594037927936) by reflexivity.
assert (B100 : bpow radix2 (-100) = / 1267650600228229401496703205376) by reflexivity.
assert (U : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
pose proof (bpow_gt_0 radix2 (-1075)) as T0.
assert (T1 : bpow radix2 (-1075) <= bpow radix2 (-100)) by (apply bpow_le; lia).
assert (T2 : bpow radix2 (-1021) <= bpow radix2 (-100)) by (apply bpow_le; lia).
rewrite B100 in T1, T2. rewrite B69 in Herr.
pose proof (Rabs_pos y) as Y0.
pose proof (fl_tri (B2R s + B2R w) y (- (y - (B2R s + B2R w))) ltac:(ring)) as T.
rewrite Rabs_Ropp in T.
assert (Hv : Rabs (B2R s + B2R w) <= 2048) by lra.
destruct (fts_exact s w h0 l0 Fs Fw Hsw Hv E2) as (Fh0 & Fl0 & Eh0 & Ehl).
rewrite <- Ehl in Herr, Eh0. clear T Hv.
pose proof (fl_norm_nz h0 l0 _ Fh0 E) as Nz.
assert (Hy1 : bpow radix2 (-56) <= Rabs y).
{ destruct Hy0 as [Y | Y]; [|exact Y]. exfalso. apply Nz.
  rewrite Y, Rabs_R0, Rmult_0_r in Herr.
  pose proof (Rle_abs (0 - (B2R h0 + B2R l0))) as A1.
  pose proof (Rle_abs (- (0 - (B2R h0 + B2R l0)))) as A2. rewrite Rabs_Ropp in A2.
  assert (V : B2R h0 + B2R l0 = 0) by lra.
  rewrite Eh0, V. apply round_0; typeclasses eauto. }
rewrite B56 in Hy1.
pose proof (rn_err (B2R h0 + B2R l0)) as Hr. rewrite <- Eh0, U in Hr.
pose proof (fl_tri (B2R h0 + B2R l0) y (- (y - (B2R h0 + B2R l0))) ltac:(ring)) as T3.
pose proof (fl_tri y (B2R h0 + B2R l0) (y - (B2R h0 + B2R l0)) ltac:(ring)) as T4.
pose proof (fl_tri (B2R h0) (B2R h0 + B2R l0) (B2R h0 - (B2R h0 + B2R l0)) ltac:(ring)) as T5.
pose proof (fl_tri (B2R h0 + B2R l0) (B2R h0) (- (B2R h0 - (B2R h0 + B2R l0))) ltac:(ring))
  as T6.
rewrite Rabs_Ropp in T3, T6.
apply (normalize_correct h0 l0 h l k y Fh0 Fl0 Eh0); [split | | exact E].
- lra.
- lra.
- rewrite B69. lra.
Qed.
