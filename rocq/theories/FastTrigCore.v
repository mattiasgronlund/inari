(** * The results of the fast paths of [sin], [cos] and [tan] before the rounding

    Where [DyadicTrig.fast_sin], [fast_cos] and [fast_tan] of [Model.v]
    return [(h, l)] at an [x] with [|x| >= 2^-27], [h + l] is sin x, cos x
    or tan x within a relative 2^-71, 2^-71 and [3 * 2^-71], with [h =
    RN(h + l)] and [2^-1000 <= |h| <= 2^1000] ([fast_sin_correct] and the
    others): with [n = 2048 q + i] from [DyadicTrig.fast_reduce_any]
    ([FastTrigReduce.v] below 2^16, [FastTrigBig.v] above), x = 2π k + q
    π/2 + i π/4096 + ρ for an integer [k], and sin x and cos x are [±]
    [fast_eval] at [j = i] and ρ, or at [j = 2048 - i] and [-ρ]. They
    return the same with and without an FMA ([fast_sin_fma] and the
    others). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr TwoSum FastRound FastTrigTables FastTrigReduce FastTrigSC
  FastTrigEval FastTrigDiv FastTrigBig.
From Inari Require Import TrigPieces TrigSeries FastExpErr.

Open Scope R_scope.

(** ** The integers of the reduction

    [n = 2048 q + i] with [q = n >> 11] and [i = n & 2047], and bit 11 of
    [n] is bit 0 of [q]. *)

Lemma land_2047 : forall n, Z.land n 2047 = (n mod 2048)%Z.
Proof. intros n. exact (Z.land_ones n 11 ltac:(lia)). Qed.

Lemma shiftr_11 : forall n, Z.shiftr n 11 = (n / 2048)%Z.
Proof. intros n. exact (Z.shiftr_div_pow2 n 11 ltac:(lia)). Qed.

Lemma split_n : forall n, IZR n = 2048 * IZR (Z.shiftr n 11) + IZR (Z.land n 2047).
Proof.
intros n. rewrite land_2047, shiftr_11.
rewrite <- mult_IZR, <- plus_IZR. f_equal. apply Z_div_mod_eq_full.
Qed.

Lemma land_2047_range : forall n, (0 <= Z.land n 2047 <= 2047)%Z.
Proof. intros n. rewrite land_2047. pose proof (Z.mod_pos_bound n 2048). lia. Qed.

Lemma land_2048 : forall n, Z.land n 2048 = Z.shiftl (Z.land (Z.shiftr n 11) 1) 11.
Proof.
intros n. apply Z.bits_inj'. intros k Hk.
rewrite Z.shiftl_spec by lia. rewrite !Z.land_spec.
change 2048%Z with (2 ^ 11)%Z. rewrite Z.pow2_bits_eqb by lia.
destruct (Z.lt_trichotomy k 11) as [H | [H | H]].
- replace (11 =? k)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite Bool.andb_false_r. rewrite (Z.testbit_neg_r (Z.shiftr n 11)) by lia. reflexivity.
- subst k. rewrite Z.shiftr_spec by lia. reflexivity.
- replace (11 =? k)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  change (Z.testbit 1 (k - 11)) with (Z.testbit (2 ^ 0) (k - 11)).
  rewrite (Z.pow2_bits_eqb 0) by lia.
  replace (0 =? k - 11)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite !Bool.andb_false_r. reflexivity.
Qed.

Lemma land_2048_eqb :
  forall n, (Z.land n 2048 =? 0)%Z = (Z.land (Z.shiftr n 11) 1 =? 0)%Z.
Proof.
intros n. rewrite land_2048, Z.shiftl_mul_pow2 by lia.
destruct (Z.eqb_spec (Z.land (Z.shiftr n 11) 1) 0) as [E | E].
- rewrite E. reflexivity.
- apply Z.eqb_neq. lia.
Qed.

(** ** Quadrants *)

(** [sin (q π/2 + y)] by the last two bits of [q]. *)
Lemma sin_quad :
  forall q y,
  sin (IZR q * (PI / 2) + y) =
  if (Z.land q 1 =? 0)%Z then (if (Z.land q 2 =? 0)%Z then sin y else - sin y)
  else (if (Z.land q 2 =? 0)%Z then cos y else - cos y).
Proof.
intros q y.
assert (M : (q mod 4)%Z = Z.land q 3) by (symmetry; exact (Z.land_ones q 2 ltac:(lia))).
assert (L1 : Z.land q 1 = Z.land (q mod 4) 1)
  by (rewrite M, <- Z.land_assoc; reflexivity).
assert (L2 : Z.land q 2 = Z.land (q mod 4) 2)
  by (rewrite M, <- Z.land_assoc; reflexivity).
destruct (quad_shift q (q mod 4) y eq_refl) as [Hs _].
rewrite Hs, L1, L2.
destruct (quad_cases (q mod 4) y (Z.mod_pos_bound q 4 ltac:(lia)))
  as [(Hm & Hs' & _) | [(Hm & Hs' & _) | [(Hm & Hs' & _) | (Hm & Hs' & _)]]];
  rewrite Hs', Hm; reflexivity.
Qed.

(** [tan (q π/2 + y)] by the last bit of [q], as tan has the period π. *)
Lemma tan_quad :
  forall q y, sin y <> 0 -> cos y <> 0 ->
  tan (IZR q * (PI / 2) + y) =
  if (Z.land q 1 =? 0)%Z then sin y / cos y else - (cos y / sin y).
Proof.
intros q y S C. unfold tan.
assert (M : (q mod 4)%Z = Z.land q 3) by (symmetry; exact (Z.land_ones q 2 ltac:(lia))).
assert (L1 : Z.land q 1 = Z.land (q mod 4) 1)
  by (rewrite M, <- Z.land_assoc; reflexivity).
destruct (quad_shift q (q mod 4) y eq_refl) as [Hs Hc].
rewrite Hs, Hc, L1.
destruct (quad_cases (q mod 4) y (Z.mod_pos_bound q 4 ltac:(lia)))
  as [(Hm & Hs' & Hc') | [(Hm & Hs' & Hc') | [(Hm & Hs' & Hc') | (Hm & Hs' & Hc')]]];
  rewrite Hs', Hc', Hm.
- reflexivity.
- transitivity (- (cos y / sin y)); [field; exact S | reflexivity].
- transitivity (sin y / cos y); [field; exact C | reflexivity].
- transitivity (- (cos y / sin y)); [field; exact S | reflexivity].
Qed.

(** ** Bounds of sin and cos *)

Lemma sin_c : forall c, 0 <= c <= 1 -> 5 / 6 * c <= sin c <= c.
Proof.
intros c Hc. pose proof PI2_1.
destruct (sin_bound c 0 ltac:(lra) ltac:(lra)) as [H1 H2].
assert (E1 : sin_approx c (2 * 0 + 1) = c - c * c * c / 6)
  by (unfold sin_approx, sin_term; simpl; field).
assert (E2 : sin_approx c (2 * (0 + 1)) = c - c * c * c / 6 + c * c * c * c * c / 120)
  by (unfold sin_approx, sin_term; simpl; field).
rewrite E1 in H1. rewrite E2 in H2.
assert (c * c <= 1) by nra. assert (0 <= c * c * c <= c) by nra.
assert (c * c * c * c * c <= c * c * c) by nra.
lra.
Qed.

Lemma cos_c : forall c, 0 <= c <= 1 -> 1 - c * c / 2 <= cos c <= 1 - c * c / 4.
Proof.
intros c Hc. pose proof PI2_1.
destruct (cos_bound c 0 ltac:(lra) ltac:(lra)) as [H1 H2].
assert (E1 : cos_approx c (2 * 0 + 1) = 1 - c * c / 2)
  by (unfold cos_approx, cos_term; simpl; field).
assert (E2 : cos_approx c (2 * (0 + 1)) = 1 - c * c / 2 + c * c * c * c / 24)
  by (unfold cos_approx, cos_term; simpl; field).
rewrite E1 in H1. rewrite E2 in H2.
assert (0 <= c * c <= 1) by nra. assert (c * c * c * c <= c * c) by nra.
lra.
Qed.

(** An angle at least [c] away from 0 and from π/2. *)
Lemma sin_mid :
  forall a c, 0 <= c <= 1 -> c <= a <= PI / 2 - c -> 5 / 6 * c <= sin a <= 1 - c * c / 4.
Proof.
intros a c Hc Ha. pose proof PI2_1. split.
- apply Rle_trans with (sin c); [apply sin_c; lra |].
  apply tp_sin_inc; lra.
- rewrite <- (cos_shift a). apply Rle_trans with (cos c); [| apply cos_c; lra].
  apply tp_cos_dec; lra.
Qed.

Lemma cos_mid :
  forall a c, 0 <= c <= 1 -> c <= a <= PI / 2 - c -> 5 / 6 * c <= cos a <= 1 - c * c / 4.
Proof. intros a c Hc Ha. rewrite <- (sin_shift a). apply sin_mid; lra. Qed.

(** The [sin] and [cos] of an [x] of [fast_sin0] and [fast_cos0]. *)
Lemma sin_small :
  forall x, bpow radix2 (-27) <= Rabs x <= / 1000 ->
  bpow radix2 (-28) <= Rabs (sin x) <= 1.
Proof.
intros x Hx.
assert (B : bpow radix2 (-28) = / 2 * bpow radix2 (-27)) by (cbn [bpow radix_val radix2]; lra).
rewrite B. pose proof (bpow_gt_0 radix2 (-27)).
destruct (Rle_or_lt 0 x) as [P | P].
- rewrite Rabs_pos_eq in Hx by lra.
  destruct (sin_c x ltac:(lra)) as [S1 S2].
  rewrite Rabs_pos_eq by lra. lra.
- rewrite Rabs_left in Hx by lra.
  destruct (sin_c (- x) ltac:(lra)) as [S1 S2]. rewrite sin_neg in S1, S2.
  rewrite Rabs_left by lra. lra.
Qed.

Lemma cos_small : forall x, Rabs x <= / 1000 -> / 2 <= cos x <= 1.
Proof.
intros x Hx. split; [| apply COS_bound].
assert (A : cos (Rabs x) = cos x).
{ unfold Rabs. destruct (Rcase_abs x); [apply cos_neg | reflexivity]. }
rewrite <- A. destruct (cos_c (Rabs x) ltac:(split; [apply Rabs_pos | lra])).
assert (Rabs x * Rabs x <= 1) by (pose proof (Rabs_pos x); nra). lra.
Qed.

(** ** Float helpers *)

(** [rh == 0.0] is false only for a nonzero finite [rh]. *)
Lemma eq_zero_false : forall x : f64, is_finite x = true -> eq x zero = false -> B2R x <> 0.
Proof.
intros x Fx E. unfold eq in E. rewrite Beqb_correct in E by (first [exact Fx | reflexivity]).
change (B2R zero) with 0 in E.
destruct (Req_bool_spec (B2R x) 0) as [H | H]; [discriminate E | exact H].
Qed.

(** The [rr = rh + rl] of the reduction, rounded, and its negation. *)
Lemma rr_rn :
  forall rh rl, is_finite rh = true -> is_finite rl = true -> is_finite (add rh rl) = true ->
  B2R (add rh rl) = RN (B2R rh + B2R rl).
Proof. exact add_B2R. Qed.

Lemma rr_rn_opp :
  forall rh rl rr, B2R rr = RN (B2R rh + B2R rl) ->
  B2R (opp rr) = RN (B2R (opp rh) + B2R (opp rl)).
Proof.
intros rh rl rr H. unfold opp. rewrite !B2R_Bopp, H, <- Ropp_plus_distr, round_NE_opp.
reflexivity.
Qed.

(** RN keeps a number on the same side of a power of 2. *)
Lemma rn_ge_bpow :
  forall e y, (-1073 <= e)%Z -> bpow radix2 e <= y -> bpow radix2 e <= RN y.
Proof.
intros e y He Hy. apply round_ge_generic; [typeclasses eauto | typeclasses eauto | | exact Hy].
apply generic_format_bpow. unfold FLT_exp. lia.
Qed.

Lemma rn_le_bpow :
  forall e y, (-1073 <= e)%Z -> y <= bpow radix2 e -> RN y <= bpow radix2 e.
Proof.
intros e y He Hy. apply round_le_generic; [typeclasses eauto | typeclasses eauto | | exact Hy].
apply generic_format_bpow. unfold FLT_exp. lia.
Qed.

(** A pair [h = RN(h + l)] within a relative 2^-69 of a [v] of at least
    2^-30 and at most 2^20 in magnitude has [2^-31 <= |h| <= 2^21]. *)
Lemma pair_abs_range :
  forall (h l : f64) v, B2R h = RN (B2R h + B2R l) ->
  Rabs (v - (B2R h + B2R l)) <= bpow radix2 (-69) * Rabs v ->
  bpow radix2 (-30) <= Rabs v <= bpow radix2 20 ->
  bpow radix2 (-31) <= Rabs (B2R h) <= bpow radix2 21.
Proof.
intros h l v Hrn Hy Hv. rewrite Hrn, <- (round_NE_abs radix2 (FLT_exp (-1074) 53)).
assert (C : bpow radix2 (-69) * Rabs v <= / 4 * Rabs v)
  by (apply Rmult_le_compat_r; [apply Rabs_pos | cbn [bpow radix_val radix2 Z.pow_pos]; lra]).
pose proof (Rabs_triang_inv v (B2R h + B2R l)) as T1.
pose proof (Rabs_triang_inv (B2R h + B2R l) v) as T2. rewrite Rabs_minus_sym in T2.
assert (B : bpow radix2 (-31) * 2 = bpow radix2 (-30) /\ bpow radix2 21 = bpow radix2 20 * 2)
  by (cbn [bpow radix_val radix2 Z.pow_pos]; lra).
split.
- apply rn_ge_bpow; [lia |]. lra.
- apply rn_le_bpow; [lia |]. lra.
Qed.

(** The same for a positive [v] between 2^-13 and 1 and a relative
    2^-71: [2^-14 <= h <= 2]. *)
Lemma pair_pos_range :
  forall (h l : f64) v, B2R h = RN (B2R h + B2R l) ->
  Rabs (B2R h + B2R l - v) <= bpow radix2 (-71) * v ->
  bpow radix2 (-13) <= v <= 1 ->
  bpow radix2 (-14) <= B2R h <= 2.
Proof.
intros h l v Hrn Hy Hv. rewrite Hrn. apply Rabs_le_inv in Hy. pose proof (bpow_gt_0 radix2 (-13)).
assert (C : bpow radix2 (-71) * v <= / 4 * v)
  by (apply Rmult_le_compat_r; [lra | cbn [bpow radix_val radix2 Z.pow_pos]; lra]).
assert (B : bpow radix2 (-14) * 2 = bpow radix2 (-13) /\ bpow radix2 1 = 2)
  by (cbn [bpow radix_val radix2 Z.pow_pos]; lra).
split; [apply rn_ge_bpow | rewrite <- (proj2 B); apply rn_le_bpow]; try lia; lra.
Qed.

(** The negated pair of a pair near [v] is near [-v]. *)
Lemma pair_opp :
  forall (h l : f64) v k,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  Rabs (B2R h + B2R l - v) <= k ->
  is_finite (opp h) = true /\ is_finite (opp l) = true /\
  B2R (opp h) = RN (B2R (opp h) + B2R (opp l)) /\
  Rabs (B2R (opp h) + B2R (opp l) - - v) <= k.
Proof.
intros h l v k Fh Fl Hrn Hy. unfold opp. rewrite !is_finite_Bopp, !B2R_Bopp.
split; [exact Fh |]. split; [exact Fl |]. split.
- rewrite <- Ropp_plus_distr, round_NE_opp, <- Hrn. reflexivity.
- replace (- B2R h + - B2R l - - v) with (- (B2R h + B2R l - v)) by ring.
  rewrite Rabs_Ropp. exact Hy.
Qed.

(** The conclusion of the three theorems below, from a pair within a
    relative [k <= 2^-69] of a [w] between 2^-30 and 2^20 in magnitude. *)
Lemma pair_out :
  forall (h l : f64) w k,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  0 <= k <= bpow radix2 (-69) ->
  Rabs (B2R h + B2R l - w) <= k * Rabs w ->
  bpow radix2 (-30) <= Rabs w <= bpow radix2 20 ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  bpow radix2 (-1000) <= Rabs (B2R h) <= bpow radix2 1000 /\
  Rabs (w - (B2R h + B2R l)) <= k * Rabs w.
Proof.
intros h l w k Fh Fl Hrn Hk Hy Hw. rewrite Rabs_minus_sym in Hy.
assert (Hy' : Rabs (w - (B2R h + B2R l)) <= bpow radix2 (-69) * Rabs w).
{ apply Rle_trans with (1 := Hy). apply Rmult_le_compat_r; [apply Rabs_pos | lra]. }
destruct (pair_abs_range h l w Hrn Hy' Hw) as [R1 R2].
assert (bpow radix2 (-1000) <= bpow radix2 (-31)) by (apply bpow_le; lia).
assert (bpow radix2 21 <= bpow radix2 1000) by (apply bpow_le; lia).
split; [exact Fh |]. split; [exact Fl |]. split; [exact Hrn |]. split; [lra | exact Hy].
Qed.

(** ** The tables and the two evaluations *)

(** The row of [fast_sc] at [i], with [sh] and [ch] between 2^-12 and 1. *)
Lemma sc_facts :
  forall i, (1 <= i <= 2047)%Z ->
  let '(sh, sl, ch, cl) := DyadicTrig.fast_sc false i in
  is_finite sh = true /\ is_finite sl = true /\ is_finite ch = true /\ is_finite cl = true /\
  Rabs (B2R sh + B2R sl - sin (IZR i * (PI / 4096))) <=
    bpow radix2 (-88) * sin (IZR i * (PI / 4096)) /\
  Rabs (B2R ch + B2R cl - cos (IZR i * (PI / 4096))) <=
    bpow radix2 (-88) * cos (IZR i * (PI / 4096)) /\
  Rabs (B2R sl) <= bpow radix2 (-53) * B2R sh /\
  Rabs (B2R cl) <= bpow radix2 (-53) * B2R ch /\
  bpow radix2 (-12) <= B2R sh <= 1 /\ bpow radix2 (-12) <= B2R ch <= 1.
Proof.
intros i Hi. pose proof (fast_sc_correct i Hi) as H.
destruct (DyadicTrig.fast_sc false i) as [[[sh sl] ch] cl].
destruct H as (Fsh & Fsl & Fch & Fcl & Es & Ec & Ls & Lc).
do 8 (split; [assumption |]).
pose proof PI2_1. pose proof PI_4.
pose proof (mid_range i Hi) as M.
destruct (sin_mid (IZR i * (PI / 4096)) (PI / 4096) ltac:(lra) M) as [S1 S2].
destruct (cos_mid (IZR i * (PI / 4096)) (PI / 4096) ltac:(lra) M) as [C1 C2].
assert (Q : / 16777216 <= PI / 4096 * (PI / 4096) / 4) by nra.
apply Rabs_le_inv in Es. apply Rabs_le_inv in Ec.
apply Rabs_le_inv in Ls. apply Rabs_le_inv in Lc.
cbn [bpow radix_val radix2 Z.pow_pos Z.opp] in *.
split; split; lra.
Qed.

(** [sin (q π/2 + y)] and [cos (q π/2 + y)] at [j = 2048 - i]. *)
Lemma swap_angle :
  forall i, IZR (2048 - i) * (PI / 4096) = PI / 2 - IZR i * (PI / 4096).
Proof. intros i. rewrite minus_IZR. field. Qed.

(** The two calls of [fast_eval] at the [i] of the reduction: the first
    gives sin y and the second, at [j = 2048 - i] and [-ρ], cos y, where y
    = i π/4096 + ρ, and both are between 2^-13 and 1. *)
Lemma eval_both :
  forall i rh rl rr rho, (1 <= i <= 2047)%Z ->
  is_finite rh = true -> is_finite rl = true -> is_finite rr = true ->
  B2R rr = RN (B2R rh + B2R rl) ->
  Rabs rho <= PI / 8192 * (1 + bpow radix2 (-24)) ->
  Rabs (rho - (B2R rh + B2R rl)) <= bpow radix2 (-90) ->
  Rabs (B2R rl) <= bpow radix2 (-37) ->
  bpow radix2 (-65) <= Rabs (B2R rh) ->
  let '(sh, sl, ch, cl) := DyadicTrig.fast_sc false i in
  bpow radix2 (-13) <= sin (IZR i * (PI / 4096) + rho) <= 1 /\
  bpow radix2 (-13) <= cos (IZR i * (PI / 4096) + rho) <= 1 /\
  (let '(h, l) := DyadicTrig.fast_eval false sh sl ch cl rh rl rr in
   is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
   Rabs (B2R h + B2R l - sin (IZR i * (PI / 4096) + rho)) <=
     bpow radix2 (-71) * sin (IZR i * (PI / 4096) + rho)) /\
  (let '(h, l) := DyadicTrig.fast_eval false ch cl sh sl (opp rh) (opp rl) (opp rr) in
   is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
   Rabs (B2R h + B2R l - cos (IZR i * (PI / 4096) + rho)) <=
     bpow radix2 (-71) * cos (IZR i * (PI / 4096) + rho)).
Proof.
intros i rh rl rr rho Hi Frh Frl Frr Hrr Hrho Err Hrl Hrh.
pose proof (sc_facts i Hi) as S.
destruct (DyadicTrig.fast_sc false i) as [[[sh sl] ch] cl].
destruct S as (Fsh & Fsl & Fch & Fcl & Es & Ec & Ls & Lc & _).
split; [| split; [| split]].
- (* the range of sin y *)
  pose proof PI2_1. pose proof PI_4. pose proof (mid_range i Hi) as M.
  pose proof (Rabs_le_inv _ _ Hrho) as R.
  assert (K : bpow radix2 (-24) = / 16777216) by (cbn [bpow radix_val radix2 Z.pow_pos]; lra).
  assert (B : bpow radix2 (-13) = / 8192) by (cbn [bpow radix_val radix2 Z.pow_pos]; lra).
  rewrite K in R. rewrite B.
  destruct (sin_mid (IZR i * (PI / 4096) + rho) (PI / 8192 * (1 - / 16777216)) ltac:(lra)
    ltac:(lra)) as [S1 _].
  pose proof (SIN_bound (IZR i * (PI / 4096) + rho)). lra.
- (* the range of cos y *)
  pose proof PI2_1. pose proof PI_4. pose proof (mid_range i Hi) as M.
  pose proof (Rabs_le_inv _ _ Hrho) as R.
  assert (K : bpow radix2 (-24) = / 16777216) by (cbn [bpow radix_val radix2 Z.pow_pos]; lra).
  assert (B : bpow radix2 (-13) = / 8192) by (cbn [bpow radix_val radix2 Z.pow_pos]; lra).
  rewrite K in R. rewrite B.
  destruct (cos_mid (IZR i * (PI / 4096) + rho) (PI / 8192 * (1 - / 16777216)) ltac:(lra)
    ltac:(lra)) as [C1 _].
  pose proof (COS_bound (IZR i * (PI / 4096) + rho)). lra.
- exact (fast_eval_correct i sh sl ch cl rh rl rr rho Hi Fsh Fsl Fch Fcl Frh Frl Frr Hrr
    Es Ec Ls Lc Hrho Err Hrl Hrh).
- (* the swapped call: sin ((2048 - i) π/4096 - ρ) = cos y *)
  destruct (opp_ok rh) as [Frh' Rrh]. destruct (opp_ok rl) as [Frl' Rrl].
  destruct (opp_ok rr) as [Frr' _].
  assert (Hj : (1 <= 2048 - i <= 2047)%Z) by lia.
  assert (Es' : Rabs (B2R ch + B2R cl - sin (IZR (2048 - i) * (PI / 4096))) <=
                bpow radix2 (-88) * sin (IZR (2048 - i) * (PI / 4096)))
    by (rewrite swap_angle, sin_shift; exact Ec).
  assert (Ec' : Rabs (B2R sh + B2R sl - cos (IZR (2048 - i) * (PI / 4096))) <=
                bpow radix2 (-88) * cos (IZR (2048 - i) * (PI / 4096)))
    by (rewrite swap_angle, cos_shift; exact Es).
  assert (Hrho' : Rabs (- rho) <= PI / 8192 * (1 + bpow radix2 (-24)))
    by (rewrite Rabs_Ropp; exact Hrho).
  assert (Err' : Rabs (- rho - (B2R (opp rh) + B2R (opp rl))) <= bpow radix2 (-90)).
  { rewrite Rrh, Rrl. replace (- rho - (- B2R rh + - B2R rl)) with (- (rho - (B2R rh + B2R rl)))
      by ring. rewrite Rabs_Ropp. exact Err. }
  assert (Hrl' : Rabs (B2R (opp rl)) <= bpow radix2 (-37)) by (rewrite Rrl, Rabs_Ropp; exact Hrl).
  assert (Hrh' : bpow radix2 (-65) <= Rabs (B2R (opp rh))) by (rewrite Rrh, Rabs_Ropp; exact Hrh).
  pose proof (fast_eval_correct (2048 - i) ch cl sh sl (opp rh) (opp rl) (opp rr) (- rho) Hj
    Fch Fcl Fsh Fsl (eq_trans Frh' Frh) (eq_trans Frl' Frl) (eq_trans Frr' Frr)
    (rr_rn_opp rh rl rr Hrr) Es' Ec' Lc Ls Hrho' Err' Hrl' Hrh') as E.
  replace (IZR (2048 - i) * (PI / 4096) + - rho) with (PI / 2 - (IZR i * (PI / 4096) + rho))
    in E by (rewrite minus_IZR; field).
  rewrite sin_shift in E. exact E.
Qed.

(** ** The quadrant *)

(** What [fast_reduce_any] gives where [fast_quad] and [fast_tan] go on:
    [n = 2048 q + i] with [1 <= i <= 2047], and the premises of
    [eval_both] at ρ = x - 2π j - n π/4096 for an integer [j].
    [fast_reduce_any_correct] gives an [N] equal to [n] modulo 8192 and the
    bounds at ρ = x - N π/4096; with [N - n = 8192 j], N π/4096 is 2π j +
    n π/4096. *)
Lemma quad_setup :
  forall x n rh rl rr, DyadicTrig.fast_reduce_any false x = Some (n, rh, rl, rr) ->
  (Z.land n 2047 =? 0)%Z = false -> eq rh zero = false ->
  (1 <= Z.land n 2047 <= 2047)%Z /\
  IZR n = 2048 * IZR (Z.shiftr n 11) + IZR (Z.land n 2047) /\
  is_finite rh = true /\ is_finite rl = true /\ is_finite rr = true /\
  B2R rr = RN (B2R rh + B2R rl) /\
  Rabs (B2R rl) <= bpow radix2 (-37) /\
  bpow radix2 (-65) <= Rabs (B2R rh) /\
  exists j : Z,
  Rabs (B2R x - IZR j * (2 * PI) - IZR n * (PI / 4096)) <=
    PI / 8192 * (1 + bpow radix2 (-24)) /\
  Rabs (B2R x - IZR j * (2 * PI) - IZR n * (PI / 4096) - (B2R rh + B2R rl)) <=
    bpow radix2 (-90).
Proof.
intros x n rh rl rr R Ei Ez.
destruct (fast_reduce_any_correct x n rh rl rr R)
  as (_ & _ & Frh & Frl & Frr & Err & Hrl & Erh & N & Nm & E90 & Erho).
apply Z.eqb_neq in Ei. pose proof (land_2047_range n).
assert (Nz : n <> 0%Z) by (intros ->; apply Ei; reflexivity).
pose proof (eq_zero_false rh Frh Ez) as Hz.
split; [lia |]. split; [apply split_n |].
do 3 (split; [assumption |]).
split; [subst rr; exact (rr_rn rh rl Frh Frl Frr) |].
split; [assumption |]. split; [exact (Erh Nz Hz) |].
(* N = 8192 j + n, so N π/4096 = 2π j + n π/4096. *)
pose proof (Z_div_mod_eq_full (N - n) 8192) as D. rewrite Nm in D.
exists ((N - n) / 8192)%Z.
assert (Ej : IZR N = 8192 * IZR ((N - n) / 8192) + IZR n)
  by (rewrite <- mult_IZR, <- plus_IZR; f_equal; lia).
replace (B2R x - IZR ((N - n) / 8192) * (2 * PI) - IZR n * (PI / 4096))
  with (B2R x - IZR N * (PI / 4096)) by (rewrite Ej; field).
split; assumption.
Qed.

(** A pair within a relative 2^-71 of a [v] between 2^-13 and 1 gives
    the conclusion of [fast_sin_correct] at [v], and its negation at [-v]. *)
Lemma pos_out :
  forall (h l : f64) v,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  Rabs (B2R h + B2R l - v) <= bpow radix2 (-71) * v ->
  bpow radix2 (-13) <= v <= 1 ->
  (is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
   bpow radix2 (-1000) <= Rabs (B2R h) <= bpow radix2 1000 /\
   Rabs (v - (B2R h + B2R l)) <= bpow radix2 (-71) * Rabs v) /\
  (is_finite (opp h) = true /\ is_finite (opp l) = true /\
   B2R (opp h) = RN (B2R (opp h) + B2R (opp l)) /\
   bpow radix2 (-1000) <= Rabs (B2R (opp h)) <= bpow radix2 1000 /\
   Rabs (- v - (B2R (opp h) + B2R (opp l))) <= bpow radix2 (-71) * Rabs (- v)).
Proof.
intros h l v Fh Fl Hrn Hy Hv.
pose proof (bpow_gt_0 radix2 (-13)).
assert (Hk : 0 <= bpow radix2 (-71) <= bpow radix2 (-69))
  by (split; [apply bpow_ge_0 | apply bpow_le; lia]).
assert (Hw : bpow radix2 (-30) <= Rabs v <= bpow radix2 20).
{ rewrite Rabs_pos_eq by lra.
  assert (bpow radix2 (-30) <= bpow radix2 (-13)) by (apply bpow_le; lia).
  assert (1 <= bpow radix2 20) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
  lra. }
assert (Hy' : Rabs (B2R h + B2R l - v) <= bpow radix2 (-71) * Rabs v)
  by (rewrite (Rabs_pos_eq v) by lra; exact Hy).
split; [exact (pair_out h l v _ Fh Fl Hrn Hk Hy' Hw) |].
destruct (pair_opp h l v _ Fh Fl Hrn Hy') as (Fh' & Fl' & Hrn' & Hy'').
rewrite <- (Rabs_Ropp v) in Hy'', Hw.
exact (pair_out (opp h) (opp l) (- v) _ Fh' Fl' Hrn' Hk Hy'' Hw).
Qed.

(** [fast_quad] at [s] gives sin (x + s π/2). *)
Lemma quad_correct :
  forall x n rh rl rr s h l,
  DyadicTrig.fast_reduce_any false x = Some (n, rh, rl, rr) ->
  DyadicTrig.fast_quad false n s rh rl rr = Some (h, l) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  bpow radix2 (-1000) <= Rabs (B2R h) <= bpow radix2 1000 /\
  Rabs (sin (B2R x + IZR s * (PI / 2)) - (B2R h + B2R l)) <=
    bpow radix2 (-71) * Rabs (sin (B2R x + IZR s * (PI / 2))).
Proof.
intros x n rh rl rr s h l R Q.
unfold DyadicTrig.fast_quad in Q. cbv zeta in Q.
destruct (Z.land n 2047 =? 0)%Z eqn:Ei; [discriminate Q |]. cbn [orb] in Q.
destruct (eq rh zero) eqn:Ez; [discriminate Q |].
destruct (quad_setup x n rh rl rr R Ei Ez)
  as (Hi & Sn & Frh & Frl & Frr & Hrr & Hrl & Hrh & j & Hrho & Err).
(* sin has period 2π, so x - 2π j stands for x. *)
rewrite (tp_sin_sub (B2R x + IZR s * (PI / 2)) j).
replace (B2R x + IZR s * (PI / 2) - 2 * IZR j * PI)
  with (B2R x - IZR j * (2 * PI) + IZR s * (PI / 2)) by ring.
set (z := B2R x - IZR j * (2 * PI)) in *.
pose proof (eval_both _ rh rl rr _ Hi Frh Frl Frr Hrr Hrho Err Hrl Hrh) as EB.
set (y := IZR (Z.land n 2047) * (PI / 4096) + (z - IZR n * (PI / 4096))) in EB.
assert (A : sin (z + IZR s * (PI / 2)) = sin (IZR (Z.shiftr n 11 + s) * (PI / 2) + y))
  by (unfold y; f_equal; rewrite plus_IZR, Sn; field).
rewrite A, sin_quad. clear A.
revert Q EB. destruct (DyadicTrig.fast_sc false (Z.land n 2047)) as [[[sh sl] ch] cl].
intros Q (Sy & Cy & E1 & E2).
revert Q. destruct (Z.land (Z.shiftr n 11 + s) 1 =? 0); intros Q.
- revert Q E1. destruct (DyadicTrig.fast_eval false sh sl ch cl rh rl rr) as [h0 l0].
  intros Q (Fh & Fl & Hrn & Er).
  destruct (pos_out h0 l0 _ Fh Fl Hrn Er Sy) as [P N].
  destruct (Z.land (Z.shiftr n 11 + s) 2 =? 0); injection Q as Eh El; subst; assumption.
- revert Q E2.
  destruct (DyadicTrig.fast_eval false ch cl sh sl (opp rh) (opp rl) (opp rr)) as [h0 l0].
  intros Q (Fh & Fl & Hrn & Er).
  destruct (pos_out h0 l0 _ Fh Fl Hrn Er Cy) as [P N].
  destruct (Z.land (Z.shiftr n 11 + s) 2 =? 0); injection Q as Eh El; subst; assumption.
Qed.

(** The constants of the theorems below. *)
Lemma k71 : 0 <= bpow radix2 (-71) <= bpow radix2 (-69).
Proof. split; [apply bpow_ge_0 | apply bpow_le; lia]. Qed.

Lemma small_range :
  forall w, bpow radix2 (-28) <= Rabs w <= 1 -> bpow radix2 (-30) <= Rabs w <= bpow radix2 20.
Proof.
intros w Hw.
assert (bpow radix2 (-30) <= bpow radix2 (-28)) by (apply bpow_le; lia).
assert (1 <= bpow radix2 20) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
lra.
Qed.

(** An [x] of the reduction at [n = 0] is at most π/8192 (1 + 2^-24) <
    1/1000 in magnitude. *)
Lemma n0_small :
  forall x, Rabs x <= PI / 8192 * (1 + bpow radix2 (-24)) -> Rabs x <= / 1000.
Proof.
intros x Hx. pose proof PI_4.
assert (bpow radix2 (-24) <= 1) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
assert (PI / 8192 * (1 + bpow radix2 (-24)) <= 4 / 8192 * 2).
{ apply Rmult_le_compat; [pose proof PI_RGT_0; lra | pose proof (bpow_ge_0 radix2 (-24)); lra
  | lra | lra]. }
lra.
Qed.

Theorem fast_sin_correct :
  forall x h l,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicTrig.fast_sin false x = Some (h, l) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  bpow radix2 (-1000) <= Rabs (B2R h) <= bpow radix2 1000 /\
  Rabs (sin (B2R x) - (B2R h + B2R l)) <= bpow radix2 (-71) * Rabs (sin (B2R x)).
Proof.
intros x h l Fx Hx F. unfold DyadicTrig.fast_sin in F.
destruct (DyadicTrig.fast_reduce_any false x) as [[[[n rh] rl] rr] |] eqn:R; [| discriminate F].
destruct (n =? 0)%Z eqn:N0.
- apply Z.eqb_eq in N0. subst n.
  pose proof (proj1 (fast_reduce_any_correct x 0 rh rl rr R) eq_refl) as R0.
  destruct (fast_reduce_correct x 0 rh rl rr R0) as (_ & _ & _ & _ & _ & _ & _ & _ & Erho & _).
  rewrite Rmult_0_l, Rminus_0_r in Erho.
  pose proof (fast_sin0_correct x Fx (conj Hx Erho)) as S0.
  revert F S0. destruct (DyadicTrig.fast_sin0 x) as [h0 l0]. intros F S0.
  injection F as Eh El. subst h0 l0.
  destruct S0 as (Fh & Fl & Hrn & Er).
  pose proof (sin_small (B2R x) (conj Hx (n0_small _ Erho))) as Hs.
  exact (pair_out h l _ _ Fh Fl Hrn k71 Er (small_range _ Hs)).
- pose proof (quad_correct x n rh rl rr 0 h l R F) as Qc.
  rewrite Rmult_0_l, Rplus_0_r in Qc. exact Qc.
Qed.

Theorem fast_cos_correct :
  forall t h l,
  is_finite t = true -> bpow radix2 (-27) <= Rabs (B2R t) ->
  DyadicTrig.fast_cos false t = Some (h, l) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  bpow radix2 (-1000) <= Rabs (B2R h) <= bpow radix2 1000 /\
  Rabs (cos (B2R t) - (B2R h + B2R l)) <= bpow radix2 (-71) * Rabs (cos (B2R t)).
Proof.
intros t h l Ft Ht F. unfold DyadicTrig.fast_cos in F.
destruct (DyadicTrig.fast_reduce_any false t) as [[[[n rh] rl] rr] |] eqn:R; [| discriminate F].
destruct (n =? 0)%Z eqn:N0.
- apply Z.eqb_eq in N0. subst n.
  pose proof (proj1 (fast_reduce_any_correct t 0 rh rl rr R) eq_refl) as R0.
  destruct (fast_reduce_correct t 0 rh rl rr R0) as (_ & _ & _ & _ & _ & _ & _ & _ & Erho & _).
  rewrite Rmult_0_l, Rminus_0_r in Erho.
  pose proof (fast_cos0_correct t Ft (conj Ht Erho)) as C0.
  revert F C0. destruct (DyadicTrig.fast_cos0 t) as [h0 l0]. intros F C0.
  injection F as Eh El. subst h0 l0.
  destruct C0 as (Fh & Fl & Hrn & Er).
  pose proof (cos_small (B2R t) (n0_small _ Erho)) as Hc.
  assert (Er2 : Rabs (B2R h + B2R l - cos (B2R t)) <= bpow radix2 (-71) * Rabs (cos (B2R t)))
    by (rewrite (Rabs_pos_eq (cos (B2R t))) by lra; exact Er).
  assert (Hc' : bpow radix2 (-28) <= Rabs (cos (B2R t)) <= 1).
  { rewrite Rabs_pos_eq by lra.
    assert (bpow radix2 (-28) <= / 2) by (cbn [bpow radix_val radix2 Z.pow_pos Z.opp]; lra).
    lra. }
  exact (pair_out h l _ _ Fh Fl Hrn k71 Er2 (small_range _ Hc')).
- pose proof (quad_correct t n rh rl rr 1 h l R F) as Qc.
  replace (sin (B2R t + 1 * (PI / 2))) with (cos (B2R t)) in Qc
    by (rewrite cos_sin; f_equal; ring).
  exact Qc.
Qed.

(** The constant of [fast_tan_correct], and the range of its quotients. *)
Lemma k3 : 0 <= 3 * bpow radix2 (-71) <= bpow radix2 (-69).
Proof.
assert (B : bpow radix2 (-69) = 4 * bpow radix2 (-71))
  by (cbn [bpow radix_val radix2 Z.pow_pos]; lra).
pose proof (bpow_ge_0 radix2 (-71)). lra.
Qed.

Lemma quot_range :
  forall a b, bpow radix2 (-28) <= Rabs a <= 1 -> bpow radix2 (-13) <= b <= 1 ->
  bpow radix2 (-30) <= Rabs (a / b) <= bpow radix2 20.
Proof.
intros a b Ha Hb. pose proof (bpow_gt_0 radix2 (-13)).
assert (Pb : 0 < / b) by (apply Rinv_0_lt_compat; lra).
unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ b)) by lra.
assert (I1 : 1 <= / b) by (rewrite <- Rinv_1; apply Rinv_le_contravar; lra).
assert (I2 : / b <= bpow radix2 13).
{ replace (bpow radix2 13) with (/ bpow radix2 (-13)) by (rewrite <- bpow_opp; reflexivity).
  apply Rinv_le_contravar; lra. }
assert (bpow radix2 (-30) <= bpow radix2 (-28)) by (apply bpow_le; lia).
assert (bpow radix2 13 <= bpow radix2 20) by (apply bpow_le; lia).
pose proof (Rabs_pos a).
split.
- apply Rle_trans with (Rabs a * 1); [lra |].
  apply Rmult_le_compat_l; lra.
- apply Rle_trans with (1 * bpow radix2 13); [| lra].
  apply Rmult_le_compat; lra.
Qed.

Theorem fast_tan_correct :
  forall x h l,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicTrig.fast_tan false x = Some (h, l) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  bpow radix2 (-1000) <= Rabs (B2R h) <= bpow radix2 1000 /\
  Rabs (tan (B2R x) - (B2R h + B2R l)) <= 3 * bpow radix2 (-71) * Rabs (tan (B2R x)).
Proof.
intros x h l Fx Hx F. unfold DyadicTrig.fast_tan in F.
destruct (DyadicTrig.fast_reduce_any false x) as [[[[n rh] rl] rr] |] eqn:R; [| discriminate F].
destruct (n =? 0)%Z eqn:N0.
- (* n = 0: tan x = sin x / cos x from fast_sin0 and fast_cos0 *)
  apply Z.eqb_eq in N0. subst n.
  pose proof (proj1 (fast_reduce_any_correct x 0 rh rl rr R) eq_refl) as R0.
  destruct (fast_reduce_correct x 0 rh rl rr R0) as (_ & _ & _ & _ & _ & _ & _ & _ & Erho & _).
  rewrite Rmult_0_l, Rminus_0_r in Erho.
  pose proof (fast_sin0_correct x Fx (conj Hx Erho)) as S0.
  pose proof (fast_cos0_correct x Fx (conj Hx Erho)) as C0.
  pose proof (sin_small (B2R x) (conj Hx (n0_small _ Erho))) as Hs.
  pose proof (cos_small (B2R x) (n0_small _ Erho)) as Hc.
  assert (Hc' : bpow radix2 (-13) <= cos (B2R x) <= 1).
  { assert (bpow radix2 (-13) <= / 2) by (cbn [bpow radix_val radix2 Z.pow_pos Z.opp]; lra).
    lra. }
  revert F S0 C0. destruct (DyadicTrig.fast_sin0 x) as [sh sl].
  destruct (DyadicTrig.fast_cos0 x) as [ch cl].
  intros F (Fsh & Fsl & Hsrn & Es) (Fch & Fcl & Hcrn & Ec).
  pose proof (fast_div_correct sh sl ch cl _ _ Fsh Fsl Fch Fcl Hsrn Hcrn Hs Hc' Es Ec) as D.
  revert F D. destruct (DyadicTrig.fast_div false sh sl ch cl) as [h0 l0].
  intros F (Fh & Fl & Hrn & Er). injection F as <- <-.
  unfold tan. exact (pair_out h0 l0 _ _ Fh Fl Hrn k3 Er (quot_range _ _ Hs Hc')).
- cbv zeta in F.
  destruct (Z.land n 2047 =? 0)%Z eqn:Ei; [discriminate F |]. cbn [orb] in F.
  destruct (eq rh zero) eqn:Ez; [discriminate F |].
  destruct (quad_setup x n rh rl rr R Ei Ez)
    as (Hi & Sn & Frh & Frl & Frr & Hrr & Hrl & Hrh & j & Hrho & Err).
  (* sin and cos have period 2π, so tan x = tan (x - 2π j). *)
  assert (T : tan (B2R x) = tan (B2R x - IZR j * (2 * PI))).
  { unfold tan. rewrite (tp_sin_sub (B2R x) j), (tp_cos_sub (B2R x) j).
    replace (2 * IZR j * PI) with (IZR j * (2 * PI)) by ring. reflexivity. }
  rewrite T. clear T.
  set (z := B2R x - IZR j * (2 * PI)) in *.
  pose proof (eval_both _ rh rl rr _ Hi Frh Frl Frr Hrr Hrho Err Hrl Hrh) as EB.
  set (y := IZR (Z.land n 2047) * (PI / 4096) + (z - IZR n * (PI / 4096))) in EB.
  assert (A : tan z = tan (IZR (Z.shiftr n 11) * (PI / 2) + y))
    by (unfold y; f_equal; rewrite Sn; field).
  rewrite A. clear A.
  revert F EB. destruct (DyadicTrig.fast_sc false (Z.land n 2047)) as [[[sh sl] ch] cl].
  intros F (Sy & Cy & E1 & E2).
  pose proof (bpow_gt_0 radix2 (-13)).
  rewrite tan_quad by lra.
  rewrite land_2048_eqb in F.
  assert (L : bpow radix2 (-28) <= bpow radix2 (-13)) by (apply bpow_le; lia).
  assert (Sy' : bpow radix2 (-28) <= Rabs (sin y) <= 1) by (rewrite Rabs_pos_eq; lra).
  assert (Cy' : bpow radix2 (-28) <= Rabs (cos y) <= 1) by (rewrite Rabs_pos_eq; lra).
  revert F E1 E2. destruct (DyadicTrig.fast_eval false sh sl ch cl rh rl rr) as [s0 s1].
  destruct (DyadicTrig.fast_eval false ch cl sh sl (opp rh) (opp rl) (opp rr)) as [c0 c1].
  intros F (Fs0 & Fs1 & Hs0 & Es) (Fc0 & Fc1 & Hc0 & Ec).
  assert (Es' : Rabs (B2R s0 + B2R s1 - sin y) <= bpow radix2 (-71) * Rabs (sin y))
    by (rewrite (Rabs_pos_eq (sin y)) by lra; exact Es).
  assert (Ec' : Rabs (B2R c0 + B2R c1 - cos y) <= bpow radix2 (-71) * Rabs (cos y))
    by (rewrite (Rabs_pos_eq (cos y)) by lra; exact Ec).
  revert F. destruct (Z.land (Z.shiftr n 11) 1 =? 0)%Z; intros F.
  + pose proof (fast_div_correct s0 s1 c0 c1 _ _ Fs0 Fs1 Fc0 Fc1 Hs0 Hc0 Sy' Cy Es' Ec) as D.
    revert F D. destruct (DyadicTrig.fast_div false s0 s1 c0 c1) as [h0 l0].
    intros F (Fh & Fl & Hrn & Er). injection F as <- <-.
    exact (pair_out h0 l0 _ _ Fh Fl Hrn k3 Er (quot_range _ _ Sy' Cy)).
  + pose proof (fast_div_correct c0 c1 s0 s1 _ _ Fc0 Fc1 Fs0 Fs1 Hc0 Hs0 Cy' Sy Ec' Es) as D.
    revert F D. destruct (DyadicTrig.fast_div false c0 c1 s0 s1) as [h0 l0].
    intros F (Fh & Fl & Hrn & Er). injection F as <- <-.
    destruct (pair_opp h0 l0 _ _ Fh Fl Hrn Er) as (Fh' & Fl' & Hrn' & Er').
    rewrite <- (Rabs_Ropp (cos y / sin y)) in Er'.
    pose proof (quot_range _ _ Cy' Sy) as Q. rewrite <- Rabs_Ropp in Q.
    exact (pair_out (opp h0) (opp l0) _ _ Fh' Fl' Hrn' k3 Er' Q).
Qed.

(** ** With and without an FMA *)

(** The [rh] of the reduction past the guards of [fast_quad] is between
    2^-65 and 1 in magnitude, as is its negation. *)
Lemma rh_range :
  forall x n rh rl rr, DyadicTrig.fast_reduce_any false x = Some (n, rh, rl, rr) ->
  (Z.land n 2047 =? 0)%Z = false -> eq rh zero = false ->
  bpow radix2 (-65) <= Rabs (B2R rh) <= 1 /\ bpow radix2 (-65) <= Rabs (B2R (opp rh)) <= 1.
Proof.
intros x n rh rl rr R Ei Ez.
destruct (quad_setup x n rh rl rr R Ei Ez)
  as (_ & _ & _ & _ & _ & _ & Hrl & Hrh & j & Hrho & Err).
set (rho := B2R x - IZR j * (2 * PI) - IZR n * (PI / 4096)) in *.
destruct (opp_ok rh) as [_ Rrh]. rewrite Rrh, Rabs_Ropp.
pose proof PI_4. pose proof PI_RGT_0.
assert (B : bpow radix2 (-24) <= 1 /\ bpow radix2 (-90) <= bpow radix2 (-10) /\
  bpow radix2 (-37) <= bpow radix2 (-10)).
{ split; [change 1 with (bpow radix2 0) |]; [| split]; apply bpow_le; lia. }
assert (B10 : bpow radix2 (-10) = / 1024) by (cbn [bpow radix_val radix2 Z.pow_pos]; lra).
assert (P : PI / 8192 * (1 + bpow radix2 (-24)) <= 4 / 8192 * 2).
{ apply Rmult_le_compat; [lra | pose proof (bpow_ge_0 radix2 (-24)); lra | lra | lra]. }
pose proof (Rabs_triang (rho - (B2R rh + B2R rl)) (B2R rl)) as T1.
pose proof (Rabs_triang rho (- (rho - (B2R rh + B2R rl) + B2R rl))) as T2.
rewrite Rabs_Ropp in T2.
replace (rho + - (rho - (B2R rh + B2R rl) + B2R rl)) with (B2R rh) in T2 by ring.
lra.
Qed.

(** [fast_quad] is the same with and without an FMA. *)
Lemma quad_fma :
  forall x n rh rl rr s, DyadicTrig.fast_reduce_any false x = Some (n, rh, rl, rr) ->
  DyadicTrig.fast_quad true n s rh rl rr = DyadicTrig.fast_quad false n s rh rl rr.
Proof.
intros x n rh rl rr s R.
unfold DyadicTrig.fast_quad. cbv zeta.
destruct (Z.land n 2047 =? 0)%Z eqn:Ei; [reflexivity |]. cbn [orb].
destruct (eq rh zero) eqn:Ez; [reflexivity |].
destruct (quad_setup x n rh rl rr R Ei Ez) as (Hi & _ & Frh & _).
destruct (rh_range x n rh rl rr R Ei Ez) as [Rh Rh'].
destruct (opp_ok rh) as [Frh' _].
rewrite (fast_sc_fma _ Hi).
pose proof (sc_facts _ Hi) as S.
destruct (DyadicTrig.fast_sc false (Z.land n 2047)) as [[[sh sl] ch] cl].
destruct S as (Fsh & _ & Fch & _ & _ & _ & _ & _ & Rs & Rc).
rewrite (fast_eval_fma sh sl ch cl rh rl rr Fch Frh Rc Rh).
rewrite (fast_eval_fma ch cl sh sl (opp rh) (opp rl) (opp rr) Fsh (eq_trans Frh' Frh) Rs Rh').
reflexivity.
Qed.

Theorem fast_sin_fma :
  forall x, bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicTrig.fast_sin true x = DyadicTrig.fast_sin false x.
Proof.
intros x _. unfold DyadicTrig.fast_sin. rewrite fast_reduce_any_fma.
destruct (DyadicTrig.fast_reduce_any false x) as [[[[n rh] rl] rr] |] eqn:R; [| reflexivity].
destruct (n =? 0)%Z; [reflexivity |].
exact (quad_fma x n rh rl rr 0 R).
Qed.

Theorem fast_cos_fma :
  forall t, bpow radix2 (-27) <= Rabs (B2R t) ->
  DyadicTrig.fast_cos true t = DyadicTrig.fast_cos false t.
Proof.
intros t _. unfold DyadicTrig.fast_cos. rewrite fast_reduce_any_fma.
destruct (DyadicTrig.fast_reduce_any false t) as [[[[n rh] rl] rr] |] eqn:R; [| reflexivity].
destruct (n =? 0)%Z; [reflexivity |].
exact (quad_fma t n rh rl rr 1 R).
Qed.

(** A pair within a relative 2^-71 of a [v] between 2^-28 and 1 in
    magnitude, as [fast_sin0] gives, has [2^-29 <= |h| <= 2]. *)
Lemma pair_small_range :
  forall (h l : f64) v, B2R h = RN (B2R h + B2R l) ->
  Rabs (B2R h + B2R l - v) <= bpow radix2 (-71) * Rabs v ->
  bpow radix2 (-28) <= Rabs v <= 1 ->
  bpow radix2 (-29) <= Rabs (B2R h) <= 2.
Proof.
intros h l v Hrn Hy Hv. rewrite Hrn, <- (round_NE_abs radix2 (FLT_exp (-1074) 53)).
assert (C : bpow radix2 (-71) * Rabs v <= / 4 * Rabs v)
  by (apply Rmult_le_compat_r; [apply Rabs_pos | cbn [bpow radix_val radix2 Z.pow_pos]; lra]).
pose proof (Rabs_triang_inv v (B2R h + B2R l)) as T1. rewrite Rabs_minus_sym in T1.
pose proof (Rabs_triang_inv (B2R h + B2R l) v) as T2.
assert (B : bpow radix2 (-29) * 2 = bpow radix2 (-28) /\ bpow radix2 1 = 2)
  by (cbn [bpow radix_val radix2 Z.pow_pos]; lra).
split.
- apply rn_ge_bpow; [lia |]. lra.
- rewrite <- (proj2 B). apply rn_le_bpow; [lia |]. lra.
Qed.

Theorem fast_tan_fma :
  forall x, bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicTrig.fast_tan true x = DyadicTrig.fast_tan false x.
Proof.
intros x Hx. unfold DyadicTrig.fast_tan. rewrite fast_reduce_any_fma.
destruct (DyadicTrig.fast_reduce_any false x) as [[[[n rh] rl] rr] |] eqn:R; [| reflexivity].
destruct (n =? 0)%Z eqn:N0.
- (* n = 0: the quotient of fast_sin0 and fast_cos0 *)
  apply Z.eqb_eq in N0. subst n.
  pose proof (proj1 (fast_reduce_any_correct x 0 rh rl rr R) eq_refl) as R0.
  destruct (fast_reduce_correct x 0 rh rl rr R0) as (Fx & _ & _ & _ & _ & _ & _ & _ & Erho & _).
  rewrite Rmult_0_l, Rminus_0_r in Erho.
  pose proof (fast_sin0_correct x Fx (conj Hx Erho)) as S0.
  pose proof (fast_cos0_correct x Fx (conj Hx Erho)) as C0.
  pose proof (sin_small (B2R x) (conj Hx (n0_small _ Erho))) as Hs.
  pose proof (cos_small (B2R x) (n0_small _ Erho)) as Hc.
  assert (Hc' : bpow radix2 (-13) <= cos (B2R x) <= 1).
  { assert (bpow radix2 (-13) <= / 2) by (cbn [bpow radix_val radix2 Z.pow_pos Z.opp]; lra).
    lra. }
  revert S0 C0. destruct (DyadicTrig.fast_sin0 x) as [sh sl].
  destruct (DyadicTrig.fast_cos0 x) as [ch cl].
  intros (Fsh & _ & Hsrn & Es) (Fch & _ & Hcrn & Ec).
  rewrite (fast_div_fma sh sl ch cl Fsh Fch (pair_small_range sh sl _ Hsrn Es Hs)
    (pair_pos_range ch cl _ Hcrn Ec Hc')).
  reflexivity.
- cbv zeta.
  destruct (Z.land n 2047 =? 0)%Z eqn:Ei; [reflexivity |]. cbn [orb].
  destruct (eq rh zero) eqn:Ez; [reflexivity |].
  destruct (quad_setup x n rh rl rr R Ei Ez)
    as (Hi & _ & Frh & Frl & Frr & Hrr & Hrl & Hrh & j & Hrho & Err).
  destruct (rh_range x n rh rl rr R Ei Ez) as [Rh Rh'].
  destruct (opp_ok rh) as [Frh' _].
  pose proof (eval_both _ rh rl rr _ Hi Frh Frl Frr Hrr Hrho Err Hrl Hrh) as EB.
  rewrite (fast_sc_fma _ Hi).
  pose proof (sc_facts _ Hi) as S.
  revert EB S. destruct (DyadicTrig.fast_sc false (Z.land n 2047)) as [[[sh sl] ch] cl].
  intros (Sy & Cy & E1 & E2) (Fsh & _ & Fch & _ & _ & _ & _ & _ & Rs & Rc).
  rewrite (fast_eval_fma sh sl ch cl rh rl rr Fch Frh Rc Rh).
  rewrite (fast_eval_fma ch cl sh sl (opp rh) (opp rl) (opp rr) Fsh (eq_trans Frh' Frh) Rs Rh').
  revert E1 E2. destruct (DyadicTrig.fast_eval false sh sl ch cl rh rl rr) as [s0 s1].
  destruct (DyadicTrig.fast_eval false ch cl sh sl (opp rh) (opp rl) (opp rr)) as [c0 c1].
  intros (Fs0 & _ & Hs0 & Es) (Fc0 & _ & Hc0 & Ec).
  pose proof (pair_pos_range s0 s1 _ Hs0 Es Sy) as Ps.
  pose proof (pair_pos_range c0 c1 _ Hc0 Ec Cy) as Pc.
  assert (L : bpow radix2 (-29) <= bpow radix2 (-14)) by (apply bpow_le; lia).
  assert (As : bpow radix2 (-29) <= Rabs (B2R s0) <= 2)
    by (rewrite Rabs_pos_eq by (pose proof (bpow_ge_0 radix2 (-14)); lra); lra).
  assert (Ac : bpow radix2 (-29) <= Rabs (B2R c0) <= 2)
    by (rewrite Rabs_pos_eq by (pose proof (bpow_ge_0 radix2 (-14)); lra); lra).
  rewrite (fast_div_fma s0 s1 c0 c1 Fs0 Fc0 As Pc).
  rewrite (fast_div_fma c0 c1 s0 s1 Fc0 Fs0 Ac Ps).
  reflexivity.
Qed.
