(** * The rules on [th] of the fast path of [pow]

    Where [DyadicExp.fast_exp] returns [None], [DyadicPow.fast_pow_wide_dir]
    and [DyadicPow.fast_pow_wide_near] of [Model.v] settle [x^y] from [th =
    RN(y lh)] of [DyadicPow.pow_t] alone. If [|RN(y lh)| >= 1], [y lh] is at
    least [2^-1022] in magnitude, so [lh <> 0] and [x <> 1], so [|ln x| >=
    2^-54] ([FastLogNorm.ln_f64_ne1]), and [lh] is [ln x] within [2^-52
    |lh|] ([FastPowLn.ln_acc_correct], as [lh = RN(lh + ll)]). A finite [th]
    with [|th| >= 1] is then [y ln x] within [2^-51 |th|], and an infinite
    one has [|RN(y lh)| >= 2^1024], so [|y ln x| >= 1024], with the sign of
    [th] ([th_cases]). [th >= T_OVER] (the [f64] nearest to 709.7828) then
    gives [y ln x >= T_OVER (1 - 2^-51) > 1024 ln 2 = 709.78271...], so that
    [x^y > 2^1024] ([fast_pow_overflow]), and [th <= T_UNDER = -746] gives
    [y ln x < -1075 ln 2 = -745.13...], so that [0 < x^y < 2^-1075]
    ([fast_pow_underflow]), with [ln 2] from [DyExpRules.ln2_bounds]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Relative.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct FastRound FastLogNorm
  FastPowLn.
From Inari Require DyExpRules.

Open Scope R_scope.

(** Rounding to nearest of an [x] of at least [2^-1022] in magnitude moves
    it by at most [2^-53 |x|] (a copy of the [Local] lemma of
    [FastPowMul.v]). *)
Local Lemma rn_rel :
  forall x, bpow radix2 (-1022) <= Rabs x -> Rabs (RN x - x) <= bpow radix2 (-53) * Rabs x.
Proof.
intros x Hx.
assert (H : Rabs (RN x - x) <= / 2 * bpow radix2 (- 53 + 1) * Rabs x)
  by exact (relative_error_N_FLT radix2 (-1074) 53 eq_refl (fun z => negb (Z.even z)) x Hx).
change (- 53 + 1)%Z with (-52)%Z in H.
assert (E : / 2 * bpow radix2 (-52) = bpow radix2 (-53))
  by (cbn [bpow radix_val radix2]; lra).
rewrite E in H. exact H.
Qed.

(** [B2R l] of an [f64] literal [l], as [m * 2^e] (a copy of the [Local]
    tactic of [FastPow.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** [T_OVER = 6243315534363256 * 2^-43 = 709.7828] and [T_UNDER = -746],
    exactly. *)
Local Lemma lit_over : B2R DyadicPow.t_over = 6243315534363256 / 8796093022208.
Proof. lit_B2R. change (bpow radix2 (-43)) with (/ 8796093022208). lra. Qed.

Local Lemma lit_under : B2R DyadicPow.t_under = -746.
Proof. lit_B2R. change (bpow radix2 (-43)) with (/ 8796093022208). lra. Qed.

(** What [th] of [pow_t] says about [y ln x]: a finite [th] of at least 1
    in magnitude is [y ln x] within [2^-51 |th|], and an infinite one has
    [|y ln x| >= 1024] with its sign. *)
Local Lemma th_cases :
  forall fma x y th tl,
  is_finite x = true -> 0 < B2R x -> is_finite y = true ->
  DyadicPow.pow_t fma x y = (th, tl) ->
  (is_finite th = true -> 1 <= Rabs (B2R th) ->
   Rabs (B2R y * ln (B2R x) - B2R th) <= / 2251799813685248 * Rabs (B2R th)) /\
  (th = B754_infinity false -> 1024 <= B2R y * ln (B2R x)) /\
  (th = B754_infinity true -> B2R y * ln (B2R x) <= -1024).
Proof.
intros fma x y th tl Fx Px Fy Ht.
unfold DyadicPow.pow_t in Ht.
pose proof (ln_acc_correct fma x Fx Px) as HA.
destruct (DyadicLog.ln_acc fma x) as [lh ll].
cbv beta iota zeta in HA, Ht.
injection Ht as Eth Etl. clear Etl. subst th.
destruct HA as (Flh & Fll & Elh & _ & Err).
set (L := ln (B2R x)) in *.
set (S := B2R lh + B2R ll) in *.
change (bpow radix2 (-79)) with (/ 604462909807314587353088) in Err.
(* If [|RN(y lh)| >= 1], then [|y lh| >= 2^-1022], so [lh <> 0] and [x <>
   1], and [y ln x] is [y lh] within [2^-52 |y lh|]. *)
assert (Key : 1 <= Rabs (RN (B2R y * B2R lh)) ->
              bpow radix2 (-1022) <= Rabs (B2R y * B2R lh) /\
              Rabs (B2R y * L - B2R y * B2R lh)
                <= / 4503599627370496 * Rabs (B2R y * B2R lh)).
{ intros H1.
  (* Below [2^-1022], [y lh] would round to at most [2^-1022 < 1]. *)
  assert (Hz : bpow radix2 (-1022) <= Rabs (B2R y * B2R lh)).
  { destruct (Rle_or_lt (bpow radix2 (-1022)) (Rabs (B2R y * B2R lh))) as [H|H]; [exact H|].
    exfalso.
    assert (H2 : Rabs (RN (B2R y * B2R lh)) <= bpow radix2 (-1022)).
    { apply abs_round_le_generic; [typeclasses eauto .. | | lra].
      apply generic_format_FLT_bpow; [typeclasses eauto .. | lia]. }
    assert (H3 : bpow radix2 (-1022) < 1) by (change 1 with (bpow radix2 0); apply bpow_lt; lia).
    lra. }
  assert (Hlh : B2R lh <> 0).
  { intros E. rewrite E, Rmult_0_r, Rabs_R0 in Hz.
    pose proof (bpow_gt_0 radix2 (-1022)). lra. }
  (* [ln 1 = 0], so [x = 1] would give [S = 0] and [lh = RN(0) = 0]. *)
  assert (X1 : B2R x <> 1).
  { intros E. apply Hlh.
    assert (L0 : L = 0) by (unfold L; rewrite E; exact ln_1).
    rewrite L0, Rabs_R0, Rmult_0_r in Err.
    assert (S0 : S = 0).
    { destruct (Rle_or_lt 0 (0 - S)) as [H|H];
        [rewrite (Rabs_pos_eq _ H) in Err | rewrite (Rabs_left _ H) in Err]; lra. }
    rewrite Elh, S0. apply round_0; typeclasses eauto. }
  pose proof (ln_f64_ne1 x Fx Px X1) as HL54.
  change (ln (B2R x)) with L in HL54.
  change (bpow radix2 (-54)) with (/ 18014398509481984) in HL54.
  (* As in [FastPowMul.fast_pow_mul]: [|S| >= (1 - 17/16 2^-79) |ln x|],
     and [ll] is the rounding error of [lh = RN(S)], at most [2^-53 |S|]. *)
  assert (HS : (1 - 17 / 16 / 604462909807314587353088) * Rabs L <= Rabs S).
  { pose proof (Rabs_triang_inv L S). lra. }
  assert (Hll : Rabs (B2R ll) <= / 9007199254740992 * Rabs S).
  { replace (B2R ll) with (- (RN S - S)) by (rewrite <- Elh; unfold S; ring).
    rewrite Rabs_Ropp.
    change (/ 9007199254740992) with (bpow radix2 (-53)).
    apply rn_rel.
    apply Rle_trans with (bpow radix2 (-55)); [apply bpow_le; lia|].
    change (bpow radix2 (-55)) with (/ 36028797018963968). lra. }
  (* [ln x - lh = (ln x - S) + ll], with [|ln x| <= |S| / (1 - 17/16
     2^-79)] and [|S| <= |lh| / (1 - 2^-53)], so [|ln x - lh| <= (17/16
     2^-79 / (1 - 17/16 2^-79) + 2^-53) / (1 - 2^-53) |lh| <= 2^-52 |lh|]. *)
  assert (HLh : Rabs (L - B2R lh) <= / 4503599627370496 * Rabs (B2R lh)).
  { replace (L - B2R lh) with ((L - S) + B2R ll) by (unfold S; ring).
    pose proof (Rabs_triang (L - S) (B2R ll)).
    pose proof (Rabs_triang (B2R lh) (B2R ll)) as T. fold S in T.
    pose proof (Rabs_pos L). lra. }
  split; [exact Hz|].
  replace (B2R y * L - B2R y * B2R lh) with (B2R y * (L - B2R lh)) by ring.
  rewrite !Rabs_mult.
  pose proof (Rabs_pos (B2R y)).
  replace (/ 4503599627370496 * (Rabs (B2R y) * Rabs (B2R lh)))
    with (Rabs (B2R y) * (/ 4503599627370496 * Rabs (B2R lh))) by ring.
  apply Rmult_le_compat_l; assumption. }
(* An infinite [th] is the overflow of [RN(y lh)], with the sign of [y
   lh]. *)
assert (Inf : forall s, mul y lh = B754_infinity s ->
              bpow radix2 1024 <= Rabs (RN (B2R y * B2R lh)) /\
              s = xorb (Bsign y) (Bsign lh)).
{ intros s Es.
  generalize (@Bmult_correct 53 1024 _ _ mode_NE y lh).
  change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE)) with RN.
  change (Bmult mode_NE y lh) with (mul y lh). rewrite Es.
  case Rlt_bool_spec; intros Hov HB.
  - destruct HB as (_ & HF & _). rewrite Fy, Flh in HF. discriminate HF.
  - split; [exact Hov|]. cbn in HB. injection HB as HB. exact HB. }
(* Facts for both infinities: [|y lh| (1 + 2^-53) >= 2^1024]. *)
assert (B1024 : 2048 <= bpow radix2 1024)
  by (change 2048 with (bpow radix2 11); apply bpow_le; lia).
assert (Big : forall s, mul y lh = B754_infinity s ->
              bpow radix2 1024 <= (1 + / 9007199254740992) * Rabs (B2R y * B2R lh) /\
              Rabs (B2R y * L - B2R y * B2R lh)
                <= / 4503599627370496 * Rabs (B2R y * B2R lh)).
{ intros s Es. destruct (Inf s Es) as (Hov & _).
  assert (H1 : 1 <= Rabs (RN (B2R y * B2R lh))) by lra.
  destruct (Key H1) as (Hz & Hd).
  pose proof (rn_rel _ Hz) as Hr.
  change (bpow radix2 (-53)) with (/ 9007199254740992) in Hr.
  pose proof (Rabs_triang_inv (RN (B2R y * B2R lh)) (B2R y * B2R lh)).
  split; [lra | exact Hd]. }
split; [|split].
- (* [|y ln x - th| <= |y ln x - y lh| + |y lh - th| <= (2^-52 + 2^-53)
     |y lh|], with [|y lh| <= |th| / (1 - 2^-53)]. *)
  intros Fth H1.
  rewrite (mul_B2R y lh Fy Flh Fth) in H1 |- *.
  destruct (Key H1) as (Hz & Hd).
  pose proof (rn_rel _ Hz) as Hr.
  change (bpow radix2 (-53)) with (/ 9007199254740992) in Hr.
  rewrite Rabs_minus_sym in Hr.
  replace (B2R y * L - RN (B2R y * B2R lh))
    with ((B2R y * L - B2R y * B2R lh) + (B2R y * B2R lh - RN (B2R y * B2R lh))) by ring.
  pose proof (Rabs_triang (B2R y * L - B2R y * B2R lh)
    (B2R y * B2R lh - RN (B2R y * B2R lh))).
  pose proof (Rabs_triang_inv (B2R y * B2R lh) (RN (B2R y * B2R lh))).
  lra.
- (* [+inf]: the signs of [y] and [lh] agree, so [y lh > 0]. *)
  intros Es. destruct (Inf false Es) as (_ & Sx). destruct (Big false Es) as (Hb & Hd).
  assert (Z0 : 0 <= B2R y * B2R lh).
  { destruct (Bsign y) eqn:Sy, (Bsign lh) eqn:Sl; cbn in Sx; try discriminate Sx.
    - pose proof (sign_le_0 y Fy Sy). pose proof (sign_le_0 lh Flh Sl). nra.
    - pose proof (sign_ge_0 y Fy Sy). pose proof (sign_ge_0 lh Flh Sl). nra. }
  rewrite (Rabs_pos_eq _ Z0) in Hb, Hd.
  pose proof (Rle_abs (B2R y * B2R lh - B2R y * L)) as A. rewrite Rabs_minus_sym in A.
  lra.
- (* [-inf]: the signs of [y] and [lh] differ, so [y lh < 0]. *)
  intros Es. destruct (Inf true Es) as (_ & Sx). destruct (Big true Es) as (Hb & Hd).
  assert (Z0 : B2R y * B2R lh <= 0).
  { destruct (Bsign y) eqn:Sy, (Bsign lh) eqn:Sl; cbn in Sx; try discriminate Sx.
    - pose proof (sign_le_0 y Fy Sy). pose proof (sign_ge_0 lh Flh Sl). nra.
    - pose proof (sign_ge_0 y Fy Sy). pose proof (sign_le_0 lh Flh Sl). nra. }
  rewrite (Rabs_left1 _ Z0) in Hb, Hd.
  pose proof (Rle_abs (B2R y * L - B2R y * B2R lh)) as A.
  lra.
Qed.

Theorem fast_pow_overflow :
  forall fma x y th tl,
  is_finite x = true -> 0 < B2R x -> is_finite y = true ->
  DyadicPow.pow_t fma x y = (th, tl) -> ge th DyadicPow.t_over = true ->
  bpow radix2 1024 < Rpower (B2R x) (B2R y).
Proof.
intros fma x y th tl Fx Px Fy Ht Hge.
destruct (th_cases fma x y th tl Fx Px Fy Ht) as (Hf & Hp & _).
destruct DyExpRules.ln2_bounds as [L1 L2].
assert (Fo : is_finite DyadicPow.t_over = true) by (vm_compute; reflexivity).
pose proof lit_over as Lo.
(* [y ln x >= th (1 - 2^-51) >= T_OVER (1 - 2^-51) > 1024 ln 2]. *)
assert (HL : 1024 * ln 2 < B2R y * ln (B2R x)).
{ assert (HF : is_finite th = true -> 1024 * ln 2 < B2R y * ln (B2R x)).
  { intros Ft. pose proof (DyExpRules.ge_R _ _ Ft Fo Hge) as H. rewrite Lo in H.
    assert (H1 : 1 <= Rabs (B2R th)) by (rewrite (Rabs_pos_eq (B2R th)); lra).
    specialize (Hf Ft H1). rewrite (Rabs_pos_eq (B2R th)) in Hf by lra.
    pose proof (Rle_abs (B2R th - B2R y * ln (B2R x))) as A. rewrite Rabs_minus_sym in A.
    lra. }
  destruct th as [s|s| |s m e Hb]; try (apply HF; reflexivity).
  - destruct s; [vm_compute in Hge; discriminate Hge|].
    specialize (Hp eq_refl). lra.
  - vm_compute in Hge. discriminate Hge. }
(* [x^y = exp (y ln x)] and [2^1024 = exp (1024 ln 2)]. *)
unfold Rpower. rewrite DyExpRules.bpow_exp2. apply exp_increasing. lra.
Qed.

Theorem fast_pow_underflow :
  forall fma x y th tl,
  is_finite x = true -> 0 < B2R x -> is_finite y = true ->
  DyadicPow.pow_t fma x y = (th, tl) -> le th DyadicPow.t_under = true ->
  0 < Rpower (B2R x) (B2R y) < bpow radix2 (-1075).
Proof.
intros fma x y th tl Fx Px Fy Ht Hle.
destruct (th_cases fma x y th tl Fx Px Fy Ht) as (Hf & _ & Hn).
destruct DyExpRules.ln2_bounds as [L1 L2].
assert (Fu : is_finite DyadicPow.t_under = true) by (vm_compute; reflexivity).
pose proof lit_under as Lu.
(* [y ln x <= th (1 - 2^-51) <= -746 (1 - 2^-51) < -1075 ln 2]. *)
assert (HL : B2R y * ln (B2R x) < -1075 * ln 2).
{ assert (HF : is_finite th = true -> B2R y * ln (B2R x) < -1075 * ln 2).
  { intros Ft. pose proof (DyExpRules.le_R _ _ Ft Fu Hle) as H. rewrite Lu in H.
    assert (H1 : 1 <= Rabs (B2R th)) by (rewrite (Rabs_left (B2R th)) by lra; lra).
    specialize (Hf Ft H1). rewrite (Rabs_left (B2R th)) in Hf by lra.
    pose proof (Rle_abs (B2R y * ln (B2R x) - B2R th)) as A.
    lra. }
  destruct th as [s|s| |s m e Hb]; try (apply HF; reflexivity).
  - destruct s; [|vm_compute in Hle; discriminate Hle].
    specialize (Hn eq_refl). lra.
  - vm_compute in Hle. discriminate Hle. }
(* [x^y = exp (y ln x)] and [2^-1075 = exp (-1075 ln 2)]. *)
unfold Rpower. split; [apply exp_pos|].
rewrite DyExpRules.bpow_exp2. apply exp_increasing. lra.
Qed.
