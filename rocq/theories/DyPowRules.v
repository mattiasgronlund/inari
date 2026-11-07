(** * The rules before Ziv's strategy for the dyadic [pow]

    [pow_dir] of [DyadicPow] in [Model.v] settles some finite arguments
    before the loop: some of those whose results overflow or underflow,
    and some of those with [|y ln x| < 2^-54], whose results are then
    within an ulp of 1. The tests of the rules take bounds on [|y ln x|]
    from the exponents of the [f64]s ([odd_parts_spec], [expo_spec] and
    [ln_expo_spec]; [DyPown.v] and [DyPowExact.v] use the first two too).
    Each rule below is one such branch: where its test is true, the [f64]
    that the branch returns is the result rounded in the direction [up],
    and no finite [f64] is the exact result ([pow_rule_not_exact]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Sterbenz.
From Inari Require Import Model Mpfr Elementary MpfrRound DyExpRules.
From Inari Require Import Encoding Decompose Spec ExpReal LogReal.

Open Scope Z_scope.

(** ** The exponents of an [f64] *)

(** [m & -m] is the lowest bit [2^t] of [m = o 2^t] with [o] odd, so
    [trailing_zeros] splits off the odd part of [m]. *)
Lemma land_opp_pos :
  forall p : positive, exists t o, 0 <= t /\ Z.odd o = true /\ 0 < o /\
  Zpos p = o * 2 ^ t /\ Z.land (Zpos p) (- Zpos p) = 2 ^ t.
Proof.
induction p as [q _ | q IH | ].
- exists 0, (Zpos q~1). split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [ring|].
  cbn. change (Pos.ldiff q q) with (N.ldiff (Npos q) (Npos q)). rewrite N.ldiff_diag. reflexivity.
- destruct IH as (t & o & Ht & Ho & Ho0 & Hq & Hl).
  exists (t + 1), o. split; [lia|]. split; [exact Ho|]. split; [exact Ho0|]. split.
  + rewrite Pos2Z.inj_xO, Hq, Z.pow_add_r by lia. ring.
  + replace (Zpos q~0) with (Z.shiftl (Zpos q) 1) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    replace (- Z.shiftl (Zpos q) 1) with (Z.shiftl (- Zpos q) 1)
      by (rewrite !Z.shiftl_mul_pow2 by lia; lia).
    rewrite <- Z.shiftl_land, Hl, Z.shiftl_mul_pow2, Z.pow_add_r by lia. ring.
- exists 0, 1. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; reflexivity.
Qed.

Lemma trailing_zeros_odd :
  forall m, 0 < m ->
  0 <= trailing_zeros 64 m /\ Z.odd (Z.shiftr m (trailing_zeros 64 m)) = true /\
  m = Z.shiftr m (trailing_zeros 64 m) * 2 ^ trailing_zeros 64 m.
Proof.
intros m Hm. destruct m as [|p|p]; try lia.
destruct (land_opp_pos p) as (t & o & Ht & Ho & Ho0 & Hp & Hl).
unfold trailing_zeros. change (Zpos p =? 0) with false. cbv iota.
rewrite Hl, Z.log2_pow2 by exact Ht.
rewrite Z.shiftr_div_pow2 by exact Ht. rewrite Hp, Z.div_mul by (apply Z.pow_nonzero; lia).
split; [exact Ht|]. split; [exact Ho|reflexivity].
Qed.

(** [odd_parts x] is the odd [m] and the [e] of [|x| = m 2^e]. *)
Lemma odd_parts_spec :
  forall x m e,
  is_finite x = true -> B2R x <> 0%R -> DyadicPow.odd_parts x = (m, e) ->
  Z.odd m = true /\ 0 < m < 2 ^ 53 /\ -1074 <= e /\
  Rabs (B2R x) = (IZR m * bpow radix2 e)%R.
Proof.
intros x m e Fx Hx0 Ho.
destruct (to_bits_finite x Fx) as (c & Hc & Hb).
destruct (from_bits_finite (Bsign x) c Hc) as (_ & _ & Hx).
rewrite <- Hb, from_to_bits in Hx.
assert (Hax : Rabs (B2R x) = magnitude c).
{ destruct (magnitude_bounds c (proj1 Hc)) as ((H0 & _) & _).
  rewrite Hx. destruct (Bsign x); [rewrite Rabs_Ropp|]; apply Rabs_pos_eq; exact H0. }
assert (Hme : exists m0 e0,
  (Z.shiftr m0 (trailing_zeros 64 m0), e0 + trailing_zeros 64 m0) = (m, e) /\
  0 <= m0 < 2 ^ 53 /\ -1074 <= e0 /\ magnitude c = (IZR m0 * bpow radix2 e0)%R).
{ unfold DyadicPow.odd_parts in Ho. rewrite Hb, biased_finite, frac_finite in Ho by exact Hc.
  unfold magnitude, mant, Encoding.expo, F2R. cbn [Fnum Fexp].
  destruct (Z.eqb_spec (c / 2^52) 0) as [HE0 | HE0]; cbv beta iota zeta in Ho.
  - exists (c mod 2^52), (-1074). split; [exact Ho|]. split; [zlia|]. split; [lia|].
    rewrite HE0. reflexivity.
  - rewrite lor_implicit in Ho by zlia.
    exists (c mod 2^52 + 2^52), (c / 2^52 - 1075). split; [exact Ho|]. split; [zlia|].
    split; [zlia|]. f_equal. f_equal. zlia. }
destruct Hme as (m0 & e0 & Ho0 & Hm0 & He0 & Hmag).
apply pair_equal_spec in Ho0 as [<- <-].
assert (Hm0p : 0 < m0).
{ destruct (Z.eq_dec m0 0) as [E|E]; [|lia].
  exfalso. apply (Rabs_no_R0 _ Hx0). rewrite Hax, Hmag, E. ring. }
destruct (trailing_zeros_odd m0 Hm0p) as (Hz & Hodd & Hsplit).
set (z := trailing_zeros 64 m0) in *. set (o := Z.shiftr m0 z) in *.
assert (Hp2 : 0 < 2 ^ z) by (apply Z.pow_pos_nonneg; lia).
assert (Ho0 : 0 < o).
{ destruct (Z.lt_ge_cases 0 o) as [H|H]; [exact H|].
  assert (o * 2 ^ z <= 0) by (apply Z.mul_nonpos_nonneg; lia). lia. }
assert (Hom : o <= m0) by (rewrite Hsplit; nia).
split; [exact Hodd|]. split; [lia|]. split; [lia|].
rewrite Hax, Hmag, Hsplit, mult_IZR, bpow_plus, <- (IZR_Zpower radix2 z Hz).
change (radix_val radix2) with 2. ring.
Qed.

(** [expo x] is the exponent [g] of [2^g <= |x| < 2^(g+1)]. *)
Lemma expo_spec :
  forall x,
  is_finite x = true -> B2R x <> 0%R ->
  (bpow radix2 (DyadicPow.expo x) <= Rabs (B2R x) < bpow radix2 (DyadicPow.expo x + 1))%R.
Proof.
intros x Fx Hx0.
destruct (DyadicPow.odd_parts x) as [m e] eqn:Ho.
destruct (odd_parts_spec x m e Fx Hx0 Ho) as (_ & Hm & _ & Hax).
unfold DyadicPow.expo. rewrite Ho.
rewrite leading_zeros_pos by lia.
replace (e + 63 - (64 - 1 - Z.log2 m)) with (Z.log2 m + e) by ring.
destruct (Z.log2_spec m) as [H1 H2]; [lia|].
pose proof (Z.log2_nonneg m) as H3.
rewrite Hax, bpow_plus. replace (Z.log2 m + e + 1) with (Z.succ (Z.log2 m) + e) by ring.
rewrite bpow_plus, <- (IZR_Zpower radix2 (Z.log2 m)),
  <- (IZR_Zpower radix2 (Z.succ (Z.log2 m))) by lia.
pose proof (bpow_gt_0 radix2 e).
split.
- apply Rmult_le_compat_r; [lra|]. apply IZR_le. exact H1.
- apply Rmult_lt_compat_r; [lra|]. apply IZR_lt. exact H2.
Qed.

(** The exponent of a finite nonzero [f64] lies in [[-1074, 1023]]. *)
Lemma expo_range :
  forall x, is_finite x = true -> B2R x <> 0%R -> -1074 <= DyadicPow.expo x <= 1023.
Proof.
intros x Fx Hx0.
destruct (DyadicPow.odd_parts x) as [m e] eqn:Ho.
destruct (odd_parts_spec x m e Fx Hx0 Ho) as (_ & Hm & He & _).
split.
- unfold DyadicPow.expo. rewrite Ho, leading_zeros_pos by lia.
  pose proof (Z.log2_nonneg m). lia.
- destruct (expo_spec x Fx Hx0) as [H _].
  pose proof (abs_B2R_lt_emax _ _ x) as Hm'.
  cut (DyadicPow.expo x < 1024); [lia|]. apply (lt_bpow radix2). lra.
Qed.

(** [ilog2 v] is [Z.log2 v] for [0 < v < 2^64]. *)
Lemma ilog2_pos : forall v, 0 < v < 2 ^ 64 -> DyadicPow.ilog2 v = Z.log2 v.
Proof.
intros v Hv. unfold DyadicPow.ilog2. rewrite Z.mod_small by lia.
rewrite leading_zeros_pos by lia. ring.
Qed.

(** [g ln 2 <= ln r < (g + 1) ln 2] for [2^g <= r < 2^(g+1)]. *)
Lemma ln_bpow_bracket :
  forall r g, (bpow radix2 g <= r < bpow radix2 (g + 1))%R ->
  (IZR g * ln 2 <= ln r < IZR (g + 1) * ln 2)%R.
Proof.
intros r g [H1 H2]. pose proof (bpow_gt_0 radix2 g). split.
- rewrite <- (ln_exp (IZR g * ln 2)), <- bpow_exp2. apply ln_inc; assumption.
- rewrite <- (ln_exp (IZR (g + 1) * ln 2)), <- bpow_exp2. apply ln_increasing; [lra | exact H2].
Qed.

(** For [L >= 0], [2^(L-1) = 2^L / 2] and [2^(L-1+3) = 4 2^L]. *)
Lemma bpow_log2_cases :
  forall L, 0 <= L ->
  bpow radix2 (L - 1) = (IZR (2 ^ L) / 2)%R /\ bpow radix2 (L - 1 + 3) = (4 * IZR (2 ^ L))%R.
Proof.
intros L HL.
assert (E : bpow radix2 L = IZR (2 ^ L)) by (rewrite <- (IZR_Zpower radix2 L HL); reflexivity).
split.
- replace (L - 1) with (L + -1) by ring.
  rewrite bpow_plus, E. change (bpow radix2 (-1)) with (/ 2)%R. lra.
- replace (L - 1 + 3) with (L + 2) by ring. rewrite bpow_plus, E.
  change (bpow radix2 2) with 4%R. lra.
Qed.

(** [|ln r|] for [2^g <= r < 2^(g+1)] with [g >= 1], or with [g <= -2]
    and [h = -g - 1]: [ln r] lies within [[c ln 2, (c + 1) ln 2]] where
    [c = g] or [c = h], and [2^L <= c < 2^(L+1)] for [L = log2 c] puts it
    within [[2^L / 2, 4 2^L)], as [1/2 < ln 2 < 1]. *)
Lemma ln_far_bounds :
  forall l c, 1 <= c ->
  (IZR c * ln 2 <= l <= IZR (c + 1) * ln 2)%R ->
  (bpow radix2 (Z.log2 c - 1) <= l < bpow radix2 (Z.log2 c - 1 + 3))%R.
Proof.
intros l c Hc Hl.
destruct (Z.log2_spec c) as [HL1 HL2]; [lia|].
pose proof (Z.log2_nonneg c) as HL0.
destruct (bpow_log2_cases (Z.log2 c) HL0) as [-> ->].
set (L := Z.log2 c) in *.
rewrite Z.pow_succ_r in HL2 by exact HL0.
assert (HP : (0 < IZR (2 ^ L))%R) by (apply IZR_lt, Z.pow_pos_nonneg; lia).
assert (HcP : (IZR (2 ^ L) <= IZR c)%R) by (apply IZR_le; lia).
assert (HcP2 : (IZR (c + 1) <= 2 * IZR (2 ^ L))%R)
  by (rewrite <- mult_IZR; apply IZR_le; lia).
pose proof ln2_bounds as Hln2.
assert (H1 : (IZR (2 ^ L) * ln 2 <= IZR c * ln 2)%R) by (apply Rmult_le_compat_r; lra).
assert (H2 : (IZR (c + 1) * ln 2 <= 2 * IZR (2 ^ L) * ln 2)%R)
  by (apply Rmult_le_compat_r; lra).
split; nra.
Qed.

(** [|ln x|] for [1/2 <= x < 2] and [x <> 1], from [1 - 1/x <= ln x <=
    x - 1]: [|x - 1| <= |ln x| <= 2 |x - 1|] if [x < 1], and [|x - 1| / 2
    <= |ln x| <= |x - 1|] if [x > 1]. *)
Lemma ln_near_bounds :
  forall r, (1 / 2 <= r < 2)%R -> r <> 1%R ->
  (Rabs (r - 1) / 2 <= Rabs (ln r) <= 2 * Rabs (r - 1))%R.
Proof.
intros r Hr Hr1.
assert (Hu : (/ r * r = 1)%R) by (apply Rinv_l; lra).
assert (Hu1 : (1 / 2 < / r <= 2)%R).
{ split.
  - apply (Rmult_lt_reg_r r); [lra|]. rewrite Hu. lra.
  - apply (Rmult_le_reg_r r); [lra|]. rewrite Hu. lra. }
(* [1 + ln r <= r] and [1 + ln (1/r) <= 1/r], with [ln (1/r) = - ln r]. *)
assert (Hl1 : (1 + ln r <= r)%R) by (rewrite <- (exp_ln r) at 2 by lra; apply exp_ineq1_le).
assert (Hl2 : (1 - ln r <= / r)%R).
{ rewrite <- (exp_ln (/ r)) by (apply Rinv_0_lt_compat; lra).
  rewrite ln_Rinv by lra. apply exp_ineq1_le. }
destruct (Rlt_or_le r 1) as [Hlt | Hge].
- assert (Hln : (ln r < 0)%R) by (rewrite <- ln_1; apply ln_increasing; lra).
  rewrite Rabs_left by lra. rewrite Rabs_left by lra.
  split; nra.
- assert (Hgt : (1 < r)%R) by lra.
  assert (Hln : (0 < ln r)%R) by (rewrite <- ln_1; apply ln_increasing; lra).
  rewrite Rabs_pos_eq by lra. rewrite Rabs_pos_eq by lra.
  split; nra.
Qed.

(** [ln_expo x] is an [A] of [2^A <= |ln x| < 2^(A+3)]. *)
Lemma ln_expo_spec :
  forall x,
  is_finite x = true -> (0 < B2R x)%R -> B2R x <> 1%R ->
  (bpow radix2 (DyadicPow.ln_expo x) <= Rabs (ln (B2R x)) <
   bpow radix2 (DyadicPow.ln_expo x + 3))%R.
Proof.
intros x Fx Hx Hx1.
assert (Hx0 : B2R x <> 0%R) by lra.
destruct (expo_spec x Fx Hx0) as [Hg1 Hg2].
destruct (expo_range x Fx Hx0) as [Hgl Hgu].
rewrite Rabs_pos_eq in Hg1, Hg2 by lra.
pose proof (ln_bpow_bracket _ _ (conj Hg1 Hg2)) as [Hl1 Hl2].
unfold DyadicPow.ln_expo.
set (g := DyadicPow.expo x) in *.
destruct (Z.leb_spec 1 g) as [Hg | Hg]; cbv iota.
- (* [x >= 2]: [g ln 2 <= ln x < (g + 1) ln 2]. *)
  rewrite ilog2_pos by lia.
  assert (Hln : (0 < ln (B2R x))%R).
  { assert (H1 : (1 <= IZR g)%R) by (apply IZR_le; lia).
    pose proof ln2_bounds. nra. }
  rewrite Rabs_pos_eq by lra.
  apply ln_far_bounds; [lia | lra].
- destruct (Z.leb_spec g (-2)) as [Hg' | Hg']; cbv iota.
  + (* [x < 1/2]: [h ln 2 < -ln x <= (h + 1) ln 2] for [h = -g - 1]. *)
    rewrite ilog2_pos by lia.
    assert (Hln : (ln (B2R x) < 0)%R).
    { assert (H1 : (IZR (g + 1) <= -1)%R) by (apply IZR_le; lia).
      pose proof ln2_bounds. nra. }
    rewrite Rabs_left by lra.
    apply ln_far_bounds; [lia|].
    replace (IZR (- g - 1)) with (- IZR (g + 1))%R
      by (rewrite <- opp_IZR; f_equal; ring).
    replace (IZR (- g - 1 + 1)) with (- IZR g)%R
      by (rewrite <- opp_IZR; f_equal; ring).
    lra.
  + (* [1/2 <= x < 2]: [x - 1] is exact by Sterbenz's lemma. *)
    assert (Hr : (1 / 2 <= B2R x < 2)%R).
    { assert (Hg0 : g = 0 \/ g = -1) by lia.
      destruct Hg0 as [E | E]; rewrite E in Hg1, Hg2.
      - change (bpow radix2 0) with 1%R in Hg1.
        change (bpow radix2 (0 + 1)) with 2%R in Hg2. lra.
      - change (bpow radix2 (-1)) with (/ 2)%R in Hg1.
        change (bpow radix2 (-1 + 1)) with 1%R in Hg2. lra. }
    assert (F1 : is_finite DyadicExp.one = true) by (vm_compute; reflexivity).
    assert (E1 : B2R DyadicExp.one = 1%R).
    { rewrite <- SF2R_B2SF.
      replace (B2SF DyadicExp.one) with (SpecFloat.S754_finite false 4503599627370496 (-52))
        by (vm_compute; reflexivity).
      cbn [SF2R cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
      change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity. }
    assert (Fd : generic_format radix2 (SpecFloat.fexp 53 1024) (B2R x - 1)).
    { apply sterbenz; [typeclasses eauto .. | apply generic_format_B2R | | lra].
      rewrite <- E1. apply generic_format_B2R. }
    pose proof (Bminus_correct 53 1024 _ _ mode_NE x DyadicExp.one Fx F1) as E.
    rewrite E1 in E. cbn [round_mode] in E.
    rewrite round_generic in E by first [exact Fd | typeclasses eauto].
    rewrite Rlt_bool_true in E.
    2:{ assert (B : (bpow radix2 1 <= bpow radix2 1024)%R) by (apply bpow_le; lia).
        change (bpow radix2 1) with 2%R in B. apply Rabs_lt. split; lra. }
    destruct E as (Ed & Fs & _).
    change (Bminus mode_NE x DyadicExp.one) with (sub x DyadicExp.one) in Ed, Fs.
    assert (Hd0 : B2R (sub x DyadicExp.one) <> 0%R) by (rewrite Ed; lra).
    destruct (expo_spec _ Fs Hd0) as [Hd1 Hd2]. rewrite Ed in Hd1, Hd2.
    set (g' := DyadicPow.expo (sub x DyadicExp.one)) in *.
    pose proof (ln_near_bounds _ Hr Hx1) as [Hn1 Hn2].
    assert (E2 : bpow radix2 (g' - 1 + 1) = (2 * bpow radix2 (g' - 1))%R).
    { rewrite bpow_plus. change (bpow radix2 1) with 2%R. ring. }
    replace (g' - 1 + 1) with g' in E2 by ring.
    assert (E3 : bpow radix2 (g' - 1 + 3) = (2 * bpow radix2 (g' + 1))%R).
    { replace (g' - 1 + 3) with (g' + 1 + 1) by ring. rewrite bpow_plus.
      change (bpow radix2 1) with 2%R. ring. }
    rewrite E3. split; lra.
Qed.

(** ** The rules of [pow_dir] at finite arguments

    [s = expo y + ln_expo x] gives [2^s <= |y ln x| < 2^(s+4)], and the
    sign of [y ln x] is that of [y] times that of [x - 1]. *)

Local Notation G := (generic_format radix2 (SpecFloat.fexp 53 1024)).

Lemma pw_one_R : B2R DyadicExp.one = 1%R.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicExp.one) with (SpecFloat.S754_finite false 4503599627370496 (-52))
  by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

Lemma pw_m_one_R : B2R DyadicExp.m_one = (-1)%R.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicExp.m_one) with (SpecFloat.S754_finite true 4503599627370496 (-52))
  by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]. unfold F2R; cbn [Fnum Fexp]. rewrite opp_IZR.
change (IZR 4503599627370496) with (bpow radix2 52).
rewrite <- Ropp_mult_distr_l, <- bpow_plus. change (bpow radix2 (52 + -52)) with 1%R. lra.
Qed.

(** The bounds and the sign of [y ln x] that the rules test. *)
Lemma pow_rule_bounds :
  forall x y,
  is_finite x = true -> (0 < B2R x)%R -> B2R x <> 1%R -> is_finite y = true -> B2R y <> 0%R ->
  (bpow radix2 (DyadicPow.expo y + DyadicPow.ln_expo x) <= Rabs (B2R y * ln (B2R x)) <
   bpow radix2 (DyadicPow.expo y + DyadicPow.ln_expo x + 4))%R /\
  (Bool.eqb (gt y zero) (gt x DyadicExp.one) = true -> 0 < B2R y * ln (B2R x))%R /\
  (Bool.eqb (gt y zero) (gt x DyadicExp.one) = false -> B2R y * ln (B2R x) < 0)%R.
Proof.
intros x y Fx Hx Hx1 Fy Hy0.
destruct (expo_spec y Fy Hy0) as [Hy1 Hy2].
destruct (ln_expo_spec x Fx Hx Hx1) as [Hl1 Hl2].
set (ey := DyadicPow.expo y) in *. set (a := DyadicPow.ln_expo x) in *.
pose proof (bpow_gt_0 radix2 ey) as Hey. pose proof (bpow_gt_0 radix2 a) as Ha.
split.
- rewrite Rabs_mult, bpow_plus.
  replace (ey + a + 4) with ((ey + 1) + (a + 3)) by ring. rewrite bpow_plus.
  split.
  + apply Rmult_le_compat; lra.
  + apply Rmult_le_0_lt_compat; [lra | lra | exact Hy2 | exact Hl2].
- assert (F1 : is_finite DyadicExp.one = true) by (vm_compute; reflexivity).
  unfold gt. rewrite !Bltb_correct by first [reflexivity | assumption].
  rewrite pw_one_R. change (B2R zero) with 0%R.
  destruct (Rlt_bool_spec 0 (B2R y)) as [Hy | Hy];
    destruct (Rlt_bool_spec 1 (B2R x)) as [Hx' | Hx']; cbn [Bool.eqb].
  + assert (Hln : (0 < ln (B2R x))%R) by (rewrite <- ln_1; apply ln_increasing; lra).
    split; intros H; [nra | discriminate H].
  + assert (Hln : (ln (B2R x) < 0)%R) by (rewrite <- ln_1; apply ln_increasing; lra).
    split; intros H; [discriminate H | nra].
  + assert (Hln : (0 < ln (B2R x))%R) by (rewrite <- ln_1; apply ln_increasing; lra).
    assert (Hy' : (B2R y < 0)%R) by lra.
    split; intros H; [discriminate H | nra].
  + assert (Hln : (ln (B2R x) < 0)%R) by (rewrite <- ln_1; apply ln_increasing; lra).
    assert (Hy' : (B2R y < 0)%R) by lra.
    split; intros H; [nra | discriminate H].
Qed.

Lemma pow_rule_overflow :
  forall x y (up : bool),
  is_finite x = true -> (0 < B2R x)%R -> B2R x <> 1%R -> is_finite y = true -> B2R y <> 0%R ->
  10 <= DyadicPow.expo y + DyadicPow.ln_expo x ->
  Bool.eqb (gt y zero) (gt x DyadicExp.one) = true ->
  mpfr_round f64_format (if up then RNDU else RNDD) (Rpower (B2R x) (B2R y))
    (with_val (DyadicExp.overflow up)).
Proof.
intros x y up Fx Hx Hx1 Fy Hy0 Hs Ha.
destruct (pow_rule_bounds x y Fx Hx Hx1 Fy Hy0) as ([Hb _] & Hp & _).
specialize (Hp Ha).
assert (H10 : (bpow radix2 10 <= bpow radix2 (DyadicPow.expo y + DyadicPow.ln_expo x))%R)
  by (apply bpow_le; exact Hs).
change (bpow radix2 10) with 1024%R in H10.
rewrite Rabs_pos_eq in Hb by lra.
unfold Rpower. apply rnd_overflow, exp_710. lra.
Qed.

Lemma pow_rule_underflow :
  forall x y (up : bool),
  is_finite x = true -> (0 < B2R x)%R -> B2R x <> 1%R -> is_finite y = true -> B2R y <> 0%R ->
  10 <= DyadicPow.expo y + DyadicPow.ln_expo x ->
  Bool.eqb (gt y zero) (gt x DyadicExp.one) = false ->
  mpfr_round f64_format (if up then RNDU else RNDD) (Rpower (B2R x) (B2R y))
    (with_val (DyadicExp.underflow up)).
Proof.
intros x y up Fx Hx Hx1 Fy Hy0 Hs Ha.
destruct (pow_rule_bounds x y Fx Hx Hx1 Fy Hy0) as ([Hb _] & _ & Hn).
specialize (Hn Ha).
assert (H10 : (bpow radix2 10 <= bpow radix2 (DyadicPow.expo y + DyadicPow.ln_expo x))%R)
  by (apply bpow_le; exact Hs).
change (bpow radix2 10) with 1024%R in H10.
rewrite Rabs_left in Hb by lra.
unfold Rpower. apply rnd_underflow, exp_m746. lra.
Qed.

Lemma pow_rule_near_one :
  forall x y (up : bool),
  is_finite x = true -> (0 < B2R x)%R -> B2R x <> 1%R -> is_finite y = true -> B2R y <> 0%R ->
  DyadicPow.expo y + DyadicPow.ln_expo x <= -58 ->
  mpfr_round f64_format (if up then RNDU else RNDD) (Rpower (B2R x) (B2R y))
    (with_val (DyadicExp.near_one
       (if Bool.eqb (gt y zero) (gt x DyadicExp.one) then DyadicExp.one else DyadicExp.m_one)
       up)).
Proof.
intros x y up Fx Hx Hx1 Fy Hy0 Hs.
destruct (pow_rule_bounds x y Fx Hx Hx1 Fy Hy0) as ([_ Hb] & Hp & Hn).
assert (H54 : (bpow radix2 (DyadicPow.expo y + DyadicPow.ln_expo x + 4) <=
               bpow radix2 (-54))%R)
  by (apply bpow_le; lia).
unfold Rpower.
destruct (Bool.eqb (gt y zero) (gt x DyadicExp.one)) eqn:Ha.
- specialize (Hp eq_refl).
  apply rnd_near_one_exp; [vm_compute; reflexivity | lra | rewrite pw_one_R; intros H; lra
    | intros _; exact Hp | rewrite pw_one_R; intros H; lra].
- specialize (Hn eq_refl).
  apply rnd_near_one_exp; [vm_compute; reflexivity | lra | rewrite pw_m_one_R; intros H; lra
    | rewrite pw_m_one_R; intros H; lra | intros _; exact Hn].
Qed.

Lemma pow_rule_not_exact :
  forall x y (v : f64),
  is_finite x = true -> (0 < B2R x)%R -> B2R x <> 1%R -> is_finite y = true -> B2R y <> 0%R ->
  is_finite v = true ->
  10 <= DyadicPow.expo y + DyadicPow.ln_expo x \/ DyadicPow.expo y + DyadicPow.ln_expo x <= -58 ->
  Rpower (B2R x) (B2R y) <> B2R v.
Proof.
intros x y v Fx Hx Hx1 Fy Hy0 Fv Hs Heq.
destruct (pow_rule_bounds x y Fx Hx Hx1 Fy Hy0) as ([Hb1 Hb2] & _ & _).
unfold Rpower in Heq.
set (t := (B2R y * ln (B2R x))%R) in *.
pose proof (bpow_gt_0 radix2 (DyadicPow.expo y + DyadicPow.ln_expo x)) as Hs0.
assert (Gv : G (B2R v)) by apply generic_format_B2R.
destruct Hs as [Hs | Hs].
- (* [|t| >= 1024]: [exp t] is above every finite [f64], or below the
     least positive one. *)
  assert (H10 : (bpow radix2 10 <= bpow radix2 (DyadicPow.expo y + DyadicPow.ln_expo x))%R)
    by (apply bpow_le; exact Hs).
  change (bpow radix2 10) with 1024%R in H10.
  destruct (Rle_or_lt 0 t) as [Ht | Ht].
  + rewrite Rabs_pos_eq in Hb1 by exact Ht.
    assert (He : (bpow radix2 1024 <= exp t)%R) by (apply exp_710; lra).
    pose proof (abs_B2R_lt_emax _ _ v) as Hv.
    rewrite <- Heq, Rabs_pos_eq in Hv by (apply Rlt_le, exp_pos). lra.
  + rewrite Rabs_left in Hb1 by exact Ht.
    destruct (exp_m746 t) as [He1 He2]; [lra|].
    rewrite Heq in He1, He2.
    assert (Hm : (succ radix2 (SpecFloat.fexp 53 1024) 0 <= B2R v)%R)
      by (apply succ_le_lt; [typeclasses eauto | apply generic_format_0 | exact Gv | exact He1]).
    rewrite succ_zero in Hm. lra.
- (* [0 < |t| < 2^-54]: [exp t] lies strictly between 1 and its
     neighbour [f64] on the side of the sign of [t]. *)
  assert (H54 : (bpow radix2 (DyadicPow.expo y + DyadicPow.ln_expo x + 4) <=
                 bpow radix2 (-54))%R)
    by (apply bpow_le; lia).
  assert (Ht : (Rabs t < bpow radix2 (-54))%R) by lra.
  destruct (exp_near_one t Ht) as (_ & Ep & En).
  assert (G1 : G 1) by (rewrite <- pw_one_R; apply generic_format_B2R).
  destruct (Rlt_or_le 0 t) as [Hp | Hn].
  + destruct (Ep Hp) as [E1 E2]. rewrite Heq in E1, E2.
    assert (Hm : (succ radix2 (SpecFloat.fexp 53 1024) 1 <= B2R v)%R)
      by (apply succ_le_lt; [typeclasses eauto | exact G1 | exact Gv | exact E1]).
    rewrite succ_one in Hm. lra.
  + assert (Ht0 : (t < 0)%R).
    { destruct (Req_dec t 0) as [E | E]; [|lra]. rewrite E, Rabs_R0 in Hb1. lra. }
    destruct (En Ht0) as [E1 E2]. rewrite Heq in E1, E2.
    assert (Hm : (B2R v <= pred radix2 (SpecFloat.fexp 53 1024) 1)%R)
      by (apply pred_ge_gt; [typeclasses eauto | exact Gv | exact G1 | exact E2]).
    rewrite pred_one in Hm. lra.
Qed.
