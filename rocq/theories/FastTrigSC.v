(** * sin and cos of i π/4096 from the two tables

    [DyadicTrig.fast_sc false i] of [Model.v], for [i] in [1, 2047], is sin
    and cos of i π/4096 in double-double within a relative 2^-88, from
    the rows of [i / 64] and [i mod 64] of the tables by the addition
    formulas, renormalized so that each low part is at most 2^-53 times
    its high part ([fast_sc_correct]). It is the same with an FMA
    ([fast_sc_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Flocq Require Import Relative.
From Inari Require Import Model Mpfr TwoSum TwoProduct FastRound FastExpErr FastTrigTables.
From Inari Require CancelLanes MulRuTiny.

Open Scope R_scope.

(** ** sin and cos away from 0 and π/2 *)

Lemma sin_ge_lin : forall y, 0 <= y <= 1 -> 5 / 6 * y <= sin y.
Proof.
intros y Hy.
pose proof PI2_1 as HP.
destruct (sin_bound y 0 ltac:(lra) ltac:(lra)) as [H _].
assert (E : sin_approx y (2 * 0 + 1) = y - y * (y * y) / 6)
  by (unfold sin_approx, sin_term; simpl; field).
rewrite E in H.
assert (y * y <= 1) by nra.
assert (y * (y * y) <= y) by nra.
lra.
Qed.

Lemma cos_ge_half : forall z, 0 <= z <= 1 -> / 2 <= cos z.
Proof.
intros z Hz.
pose proof PI2_1 as HP.
destruct (cos_bound z 0 ltac:(lra) ltac:(lra)) as [H _].
assert (E : cos_approx z (2 * 0 + 1) = 1 - z * z / 2)
  by (unfold cos_approx, cos_term; simpl; field).
rewrite E in H.
assert (z * z <= 1) by nra.
lra.
Qed.

(** Between π/4096 and π/2 - π/4096, sin and cos are at least 1/2500:
    below 1 by [sin_ge_lin] and [cos_ge_half], above 1 by the same on
    π/2 - y. *)
Lemma sin_mid : forall y, PI / 4096 <= y <= PI / 2 - PI / 4096 -> / 2500 <= sin y.
Proof.
intros y Hy.
pose proof PI2_1. pose proof PI_4.
destruct (Rle_or_lt y 1) as [H1|H1].
- pose proof (sin_ge_lin y ltac:(lra)). lra.
- rewrite <- cos_shift. pose proof (cos_ge_half (PI / 2 - y) ltac:(lra)). lra.
Qed.

Lemma cos_mid : forall y, PI / 4096 <= y <= PI / 2 - PI / 4096 -> / 2500 <= cos y.
Proof.
intros y Hy.
pose proof PI2_1. pose proof PI_4.
destruct (Rle_or_lt y 1) as [H1|H1].
- pose proof (cos_ge_half y ltac:(lra)). lra.
- rewrite <- sin_shift. pose proof (sin_ge_lin (PI / 2 - y) ltac:(lra)). lra.
Qed.

Lemma mid_range :
  forall j, (1 <= j <= 2047)%Z -> PI / 4096 <= IZR j * (PI / 4096) <= PI / 2 - PI / 4096.
Proof.
intros j Hj.
assert (1 <= IZR j <= 2047) by (split; apply IZR_le; lia).
pose proof PI2_1.
split; nra.
Qed.

(** ** The rows of the tables *)

(** A row's high part, of sin or cos of an angle between π/4096 and π/2
    - π/4096, is between 2^-13 and 1 + 2^-51. *)
Lemma row_bounds :
  forall h l v,
  Rabs (h + l - v) <= bpow radix2 (-104) -> Rabs l <= bpow radix2 (-53) * h ->
  / 2500 <= v <= 1 ->
  bpow radix2 (-13) <= h <= 1 + bpow radix2 (-51).
Proof.
intros h l v H1 H2 H3.
apply Rabs_le_inv in H1, H2.
cbn [bpow radix_val radix2 Z.opp] in *.
split; lra.
Qed.

(** ** The products of two rows *)

(** [x y] is exact in [two_prod_err] when [x] and [y] are between 2^-13
    and 2: its exponent is between -27 and 2, theirs at most 1. *)
Lemma prod_exact_sc :
  forall b x y, is_finite x = true -> is_finite y = true ->
  bpow radix2 (-13) <= B2R x <= 2 -> bpow radix2 (-13) <= B2R y <= 2 ->
  Generic.two_prod_is_exact b x y (mul x y) = true.
Proof.
intros b x y Fx Fy Hx Hy.
assert (Hxy : bpow radix2 (-13) * bpow radix2 (-13) <= B2R x * B2R y <= 2 * 2).
{ pose proof (bpow_gt_0 radix2 (-13)).
  split; apply Rmult_le_compat; lra. }
cbn [bpow radix_val radix2 Z.opp] in Hx, Hy, Hxy.
destruct (mul_k x y 4 Fx Fy) as (Fp & _ & Bp);
  [rewrite Rabs_pos_eq by lra; lra | lra |].
apply Rabs_le_inv in Bp.
cbn [bpow radix_val radix2 Z.opp] in Bp.
assert (E1 : (-27 <= Generic.exponent (mul x y))%Z).
{ apply MulRuTiny.exponent_ge; [exact Fp |].
  rewrite Rabs_pos_eq by lra. cbn [bpow radix_val radix2 Z.opp]. lra. }
assert (E2 : (Generic.exponent (mul x y) < 3)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fp | lia |].
  rewrite Rabs_pos_eq by lra. cbn [bpow radix_val radix2 Z.opp]. lra. }
assert (E3 : (Generic.exponent x < 2)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fx | lia |].
  rewrite Rabs_pos_eq by lra. cbn [bpow radix_val radix2 Z.opp]. lra. }
assert (E4 : (Generic.exponent y < 2)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fy | lia |].
  rewrite Rabs_pos_eq by lra. cbn [bpow radix_val radix2 Z.opp]. lra. }
unfold Generic.two_prod_is_exact. cbv zeta.
destruct b; rewrite ?andb_true_iff, ?Z.leb_le; lia.
Qed.

(** [fast_mul] of two rows [(ah, al)] and [(bh, bl)]: [p] is [ah bh]
    rounded, [ah bh - p] is exact [Dekker], and [p + e] is [(ah + al) (bh
    + bl)] within [9 2^-106]: the errors of [ah bl], [al bh], their sum
    and [e], [2^-106] each per unit of their size (1, 1, 2 and 3 units of
    [2^-53]), and [al bl], left out, at most [2^-106]. *)
Lemma fast_mul_err :
  forall fma ah al bh bl p e,
  is_finite ah = true -> is_finite al = true -> is_finite bh = true -> is_finite bl = true ->
  bpow radix2 (-13) <= B2R ah <= 1 + bpow radix2 (-51) ->
  Rabs (B2R al) <= bpow radix2 (-53) * B2R ah ->
  bpow radix2 (-13) <= B2R bh <= 1 + bpow radix2 (-51) ->
  Rabs (B2R bl) <= bpow radix2 (-53) * B2R bh ->
  DyadicTrig.fast_mul fma ah al bh bl = (p, e) ->
  is_finite p = true /\ is_finite e = true /\
  bpow radix2 (-27) <= B2R p <= 1 + bpow radix2 (-48) /\
  Rabs (B2R e) <= bpow radix2 (-51) /\
  Rabs (B2R p + B2R e - (B2R ah + B2R al) * (B2R bh + B2R bl)) <= 9 * bpow radix2 (-106).
Proof.
intros fma ah al bh bl p e Fah Fal Fbh Fbl Hah Hal Hbh Hbl M.
unfold DyadicTrig.fast_mul in M. cbv zeta in M.
injection M as Ep Ee. subst p e.
pose proof (bpow_gt_0 radix2 (-13)) as H13.
pose proof (bpow_gt_0 radix2 (-53)) as H53.
assert (H2 : 1 + bpow radix2 (-51) <= 2) by (cbn [bpow radix_val radix2 Z.opp]; lra).
pose proof (prod_exact_sc fma ah bh Fah Fbh ltac:(lra) ltac:(lra)) as Hex.
destruct (two_prod_err_correct fma ah bh Fah Fbh Hex) as (Fp & Ep & _ & Fe0 & Ee0).
set (p := mul ah bh) in *.
set (e0 := Generic.two_prod_err fma ah bh p) in *.
(* The exact product [P = ah bh] and the three small ones. *)
assert (HP : bpow radix2 (-13) * bpow radix2 (-13) <= B2R ah * B2R bh <=
             (1 + bpow radix2 (-51)) * (1 + bpow radix2 (-51)))
  by (split; apply Rmult_le_compat; lra).
assert (HP0 : 0 < B2R ah * B2R bh) by (apply Rmult_lt_0_compat; lra).
assert (Habl : Rabs (B2R ah * B2R bl) <= bpow radix2 (-53) * (B2R ah * B2R bh)).
{ rewrite Rabs_mult, (Rabs_pos_eq (B2R ah)) by lra.
  replace (bpow radix2 (-53) * (B2R ah * B2R bh))
    with (B2R ah * (bpow radix2 (-53) * B2R bh)) by ring.
  apply Rmult_le_compat_l; lra. }
assert (Halb : Rabs (B2R al * B2R bh) <= bpow radix2 (-53) * (B2R ah * B2R bh)).
{ rewrite Rabs_mult, (Rabs_pos_eq (B2R bh)) by lra.
  replace (bpow radix2 (-53) * (B2R ah * B2R bh))
    with ((bpow radix2 (-53) * B2R ah) * B2R bh) by ring.
  apply Rmult_le_compat_r; lra. }
assert (Hall : Rabs (B2R al * B2R bl) <=
               (bpow radix2 (-53) * B2R ah) * (bpow radix2 (-53) * B2R bh)).
{ rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; assumption. }
assert (Hall' : (bpow radix2 (-53) * B2R ah) * (bpow radix2 (-53) * B2R bh) =
                bpow radix2 (-53) * bpow radix2 (-53) * (B2R ah * B2R bh)) by ring.
rewrite Hall' in Hall. clear Hall'.
set (P := B2R ah * B2R bh) in *.
pose proof (rn_err P) as Bp. rewrite <- Ep in Bp.
rewrite (Rabs_pos_eq P) in Bp by lra.
apply Rabs_le_inv in Bp, Habl, Halb, Hall.
cbn [bpow radix_val radix2 Z.opp] in Bp, Habl, Halb, Hall, HP, Hah, Hbh.
(* [m1 = ah bl] and [m2 = al bh] rounded, [m3 = m1 + m2] rounded,
   [e = e0 + m3] rounded. *)
destruct (mul_k ah bl (bpow radix2 (-53) + bpow radix2 (-102)) Fah Fbl) as (Fm1 & _ & Bm1);
  [apply Rabs_le; cbn [bpow radix_val radix2 Z.opp]; lra |
   cbn [bpow radix_val radix2 Z.opp]; lra |].
destruct (mul_k al bh (bpow radix2 (-53) + bpow radix2 (-102)) Fal Fbh) as (Fm2 & _ & Bm2);
  [apply Rabs_le; cbn [bpow radix_val radix2 Z.opp]; lra |
   cbn [bpow radix_val radix2 Z.opp]; lra |].
set (m1 := mul ah bl) in *. set (m2 := mul al bh) in *.
apply Rabs_le_inv in Bm1, Bm2.
cbn [bpow radix_val radix2 Z.opp] in Bm1, Bm2.
destruct (add_k m1 m2 (bpow radix2 (-52) + bpow radix2 (-100)) Fm1 Fm2) as (Fm3 & _ & Bm3);
  [apply Rabs_le; cbn [bpow radix_val radix2 Z.opp]; lra |
   cbn [bpow radix_val radix2 Z.opp]; lra |].
set (m3 := add m1 m2) in *.
apply Rabs_le_inv in Bm3.
cbn [bpow radix_val radix2 Z.opp] in Bm3.
destruct (add_k e0 m3 (3 * bpow radix2 (-53) + bpow radix2 (-98)) Fe0 Fm3) as (Fe & _ & Be);
  [apply Rabs_le; cbn [bpow radix_val radix2 Z.opp]; lra |
   cbn [bpow radix_val radix2 Z.opp]; lra |].
set (e := add e0 m3) in *.
apply Rabs_le_inv in Be.
cbn [bpow radix_val radix2 Z.opp] in Be.
assert (HX : (B2R ah + B2R al) * (B2R bh + B2R bl) =
             P + B2R ah * B2R bl + B2R al * B2R bh + B2R al * B2R bl)
  by (unfold P; ring).
split; [exact Fp |]. split; [exact Fe |].
split; [cbn [bpow radix_val radix2 Z.opp]; lra |].
split; [apply Rabs_le; cbn [bpow radix_val radix2 Z.opp]; lra |].
rewrite HX. apply Rabs_le. cbn [bpow radix_val radix2 Z.opp]. lra.
Qed.

(** The same with an FMA: the error of [ah bh] is exact either way. *)
Lemma fast_mul_fma :
  forall ah al bh bl,
  is_finite ah = true -> is_finite bh = true ->
  bpow radix2 (-13) <= B2R ah <= 2 -> bpow radix2 (-13) <= B2R bh <= 2 ->
  DyadicTrig.fast_mul true ah al bh bl = DyadicTrig.fast_mul false ah al bh bl.
Proof.
intros ah al bh bl Fah Fbh Hah Hbh.
unfold DyadicTrig.fast_mul. cbv zeta.
rewrite (two_prod_err_fma_eq ah bh Fah Fbh (prod_exact_sc true ah bh Fah Fbh Hah Hbh)
  (prod_exact_sc false ah bh Fah Fbh Hah Hbh)).
reflexivity.
Qed.

(** [Fast.fast_two_sum a b] with [|b| <= |a|]: [s] is [a + b] rounded and
    [t] its exact error, by Fast2Sum [Dekker]. *)
Lemma fts :
  forall a b s t, is_finite a = true -> is_finite b = true ->
  Rabs (B2R a + B2R b) <= 16 -> Rabs (B2R b) <= Rabs (B2R a) ->
  Fast.fast_two_sum a b = (s, t) ->
  is_finite s = true /\ is_finite t = true /\ B2R s = RN (B2R a + B2R b) /\
  Rabs (B2R s - (B2R a + B2R b)) <=
    bpow radix2 (-53) * Rabs (B2R a + B2R b) + bpow radix2 (-1075) /\
  B2R t = B2R a + B2R b - B2R s.
Proof.
intros a b s t Fa Fb H Hle E.
unfold Fast.fast_two_sum in E. cbv zeta in E.
injection E as Es Et. subst s t.
destruct (add_e a b Fa Fb H) as (Fs & Es & Bs).
destruct (CancelLanes.fast_two_sum a b (add a b) Fa Fb Hle Fs Es) as (Ft & Et).
repeat split; assumption.
Qed.

(** The product of two values each within [2^-104] of a number of at most
    1 in magnitude is within [2^-103 + 2^-208] of their product. *)
Lemma tprod :
  forall X x Y y,
  Rabs (X - x) <= bpow radix2 (-104) -> Rabs (Y - y) <= bpow radix2 (-104) ->
  Rabs x <= 1 -> Rabs y <= 1 ->
  Rabs (X * Y - x * y) <= bpow radix2 (-103) + bpow radix2 (-208).
Proof.
intros X x Y y HX HY Hx Hy.
assert (E : X * Y - x * y = (X - x) * (Y - y) + (X - x) * y + x * (Y - y)) by ring.
pose proof (Rabs_mul_le _ _ _ _ HX HY) as H1.
pose proof (Rabs_mul_le _ _ _ _ HX Hy) as H2.
pose proof (Rabs_mul_le _ _ _ _ Hx HY) as H3.
apply Rabs_le_inv in H1, H2, H3.
rewrite E. apply Rabs_le.
cbn [bpow radix_val radix2 Z.opp] in *. lra.
Qed.

(** The rounding to nearest of a normal [x] is within [2^-53] of [x]
    relatively to the result. *)
Lemma rn_rel :
  forall x, bpow radix2 (-1022) <= Rabs x ->
  Rabs (RN x - x) <= bpow radix2 (-53) * Rabs (RN x).
Proof.
intros x Hx.
assert (H : Rabs (RN x - x) <= / 2 * bpow radix2 (-52) * Rabs (RN x))
  by exact (relative_error_N_FLT_round radix2 (-1074) 53 eq_refl
    (fun z => negb (Z.even z)) x Hx).
assert (E : / 2 * bpow radix2 (-52) = bpow radix2 (-53))
  by (cbn [bpow radix_val radix2]; lra).
rewrite E in H. exact H.
Qed.

(** ** The index *)

(** [i >> 6] and [i & 63] are the quotient and remainder of [i] by 64. *)
Lemma sc_index :
  forall i, (1 <= i <= 2047)%Z ->
  Z.shiftr i 6 = (i / 64)%Z /\ Z.land i 63 = (i mod 64)%Z /\ i = (64 * (i / 64) + i mod 64)%Z /\
  (0 <= i / 64 <= 31)%Z /\ (0 <= i mod 64 <= 63)%Z.
Proof.
intros i Hi.
assert (E1 : Z.shiftr i 6 = (i / 64)%Z) by exact (Z.shiftr_div_pow2 i 6 ltac:(lia)).
assert (E2 : Z.land i 63 = (i mod 64)%Z) by exact (Z.land_ones i 6 ltac:(lia)).
assert (Hd : i = (64 * (i / 64) + i mod 64)%Z) by (apply Z.div_mod; lia).
pose proof (Z.mod_pos_bound i 64 ltac:(lia)).
repeat split; try assumption; lia.
Qed.

(** sin and cos of [j] π/4096 for [j] in [1, 2047] are between 1/2500
    and 1. *)
Lemma angle_mid :
  forall j, (1 <= j <= 2047)%Z ->
  / 2500 <= sin (IZR j * (PI / 4096)) <= 1 /\ / 2500 <= cos (IZR j * (PI / 4096)) <= 1.
Proof.
intros j Hj.
pose proof (mid_range j Hj) as H.
pose proof (sin_mid _ H). pose proof (cos_mid _ H).
pose proof (SIN_bound (IZR j * (PI / 4096))). pose proof (COS_bound (IZR j * (PI / 4096))).
split; split; lra.
Qed.

Lemma opp_ok : forall x, is_finite (opp x) = is_finite x /\ B2R (opp x) = - B2R x.
Proof. intros x. unfold opp. split; [apply is_finite_Bopp | apply B2R_Bopp]. Qed.

(** A row's value within [2^-104] of a number of at least 1/2500 is
    within [2^-88] of it relatively. *)
Lemma row_rel :
  forall h l y, Rabs (h + l - y) <= bpow radix2 (-104) -> / 2500 <= y ->
  Rabs (h + l - y) <= bpow radix2 (-88) * y.
Proof. intros h l y H Hy. cbn [bpow radix_val radix2 Z.opp] in *. lra. Qed.

Theorem fast_sc_correct :
  forall i, (1 <= i <= 2047)%Z ->
  let '(sh, sl, ch, cl) := DyadicTrig.fast_sc false i in
  is_finite sh = true /\ is_finite sl = true /\ is_finite ch = true /\ is_finite cl = true /\
  Rabs (B2R sh + B2R sl - sin (IZR i * (PI / 4096))) <=
    bpow radix2 (-88) * sin (IZR i * (PI / 4096)) /\
  Rabs (B2R ch + B2R cl - cos (IZR i * (PI / 4096))) <=
    bpow radix2 (-88) * cos (IZR i * (PI / 4096)) /\
  Rabs (B2R sl) <= bpow radix2 (-53) * B2R sh /\
  Rabs (B2R cl) <= bpow radix2 (-53) * B2R ch.
Proof.
intros i Hi.
destruct (sc_index i Hi) as (E1 & E2 & Hd & Hi1 & Hi2).
unfold DyadicTrig.fast_sc. rewrite E1, E2.
set (i1 := (i / 64)%Z) in *. set (i2 := (i mod 64)%Z) in *.
clearbody i1 i2. subst i.
pose proof (sc1_correct i1 Hi1) as T1. pose proof (sc2_correct i2 ltac:(lia)) as T2.
revert T1 T2.
destruct (DyadicTrig.sc DyadicTrig.SC1 i1) as [[[s1h s1l] c1h] c1l].
destruct (DyadicTrig.sc DyadicTrig.SC2 i2) as [[[s2h s2l] c2h] c2l].
intros T1 T2. cbv beta iota in T1, T2 |- *.
destruct T1 as (Fs1h & Fs1l & Fc1h & Fc1l & Es1 & Ec1 & Ns1 & Nc1).
destruct T2 as (Fs2h & Fs2l & Fc2h & Fc2l & Es2 & Ec2 & Ns2 & Nc2).
destruct (angle_mid (64 * i1 + i2) Hi) as [Sab Cab].
destruct (Z.eqb_spec i2 0) as [Z2|Z2]; cbv beta iota.
{ (* [i mod 64 = 0]: the row [i / 64] of [SC1], within 2^-104. *)
  subst i2. rewrite Z.add_0_r in Sab, Cab |- *.
  assert (A1 : IZR (64 * i1) * (PI / 4096) = IZR i1 * (PI / 64))
    by (rewrite mult_IZR; field).
  rewrite A1 in Sab, Cab |- *.
  repeat split; try assumption; apply row_rel; (assumption || lra). }
destruct (Z.eqb_spec i1 0) as [Z1|Z1]; cbv beta iota.
{ (* [i / 64 = 0]: the row [i] of [SC2]. *)
  subst i1. rewrite Z.mul_0_r, Z.add_0_l in Sab, Cab |- *.
  repeat split; try assumption; apply row_rel; (assumption || lra). }
(* Otherwise [i] π/4096 is [a + b], with [a = (i / 64) π/64] and [b = (i
   mod 64) π/4096], and [a - b] and the four angles are between π/4096
   and π/2 - π/4096. *)
destruct (angle_mid (64 * i1) ltac:(lia)) as [Sa Ca].
destruct (angle_mid (64 * i1 - i2) ltac:(lia)) as [Samb _].
destruct (angle_mid i2 ltac:(lia)) as [Sb Cb].
assert (A1 : IZR (64 * i1) * (PI / 4096) = IZR i1 * (PI / 64))
  by (rewrite mult_IZR; field).
assert (A2 : IZR (64 * i1 - i2) * (PI / 4096) = IZR i1 * (PI / 64) - IZR i2 * (PI / 4096))
  by (rewrite minus_IZR, mult_IZR; field).
assert (A3 : IZR (64 * i1 + i2) * (PI / 4096) = IZR i1 * (PI / 64) + IZR i2 * (PI / 4096))
  by (rewrite plus_IZR, mult_IZR; field).
rewrite A1 in Sa, Ca. rewrite A2 in Samb. rewrite A3 in Sab, Cab |- *.
clear A1 A2 A3.
set (a := IZR i1 * (PI / 64)) in *. set (b := IZR i2 * (PI / 4096)) in *.
rewrite sin_minus in Samb. rewrite sin_plus in Sab |- *. rewrite cos_plus in Cab |- *.
pose proof (row_bounds _ _ _ Es1 Ns1 Sa) as Hs1.
pose proof (row_bounds _ _ _ Ec1 Nc1 Ca) as Hc1.
pose proof (row_bounds _ _ _ Es2 Ns2 Sb) as Hs2.
pose proof (row_bounds _ _ _ Ec2 Nc2 Cb) as Hc2.
(* The table values' products, within [2^-103 + 2^-208] of the exact
   ones. *)
pose proof (tprod _ _ _ _ Es1 Ec2 ltac:(apply Rabs_le; lra) ltac:(apply Rabs_le; lra)) as P1.
pose proof (tprod _ _ _ _ Ec1 Es2 ltac:(apply Rabs_le; lra) ltac:(apply Rabs_le; lra)) as P2.
pose proof (tprod _ _ _ _ Ec1 Ec2 ltac:(apply Rabs_le; lra) ltac:(apply Rabs_le; lra)) as P3.
pose proof (tprod _ _ _ _ Es1 Es2 ltac:(apply Rabs_le; lra) ltac:(apply Rabs_le; lra)) as P4.
(* The four products of [fast_mul], each within [9 2^-106]. *)
destruct (DyadicTrig.fast_mul false s1h s1l c2h c2l) as [ps es] eqn:M1.
destruct (fast_mul_err false s1h s1l c2h c2l ps es Fs1h Fs1l Fc2h Fc2l Hs1 Ns1 Hc2 Nc2 M1)
  as (Fps & Fes & Hps & Hes & Eps).
cbv beta iota.
destruct (DyadicTrig.fast_mul false c1h c1l s2h s2l) as [qs fs] eqn:M2.
destruct (fast_mul_err false c1h c1l s2h s2l qs fs Fc1h Fc1l Fs2h Fs2l Hc1 Nc1 Hs2 Ns2 M2)
  as (Fqs & Ffs & Hqs & Hfs & Eqs).
cbv beta iota.
destruct (Fast.fast_two_sum ps qs) as [sh0 t] eqn:F1.
cbv beta iota.
destruct (DyadicTrig.fast_mul false c1h c1l c2h c2l) as [pc ec] eqn:M3.
destruct (fast_mul_err false c1h c1l c2h c2l pc ec Fc1h Fc1l Fc2h Fc2l Hc1 Nc1 Hc2 Nc2 M3)
  as (Fpc & Fec & Hpc & Hec & Epc).
cbv beta iota.
destruct (DyadicTrig.fast_mul false s1h s1l s2h s2l) as [qc fc] eqn:M4.
destruct (fast_mul_err false s1h s1l s2h s2l qc fc Fs1h Fs1l Fs2h Fs2l Hs1 Ns1 Hs2 Ns2 M4)
  as (Fqc & Ffc & Hqc & Hfc & Eqc).
cbv beta iota.
destruct (Fast.fast_two_sum pc (opp qc)) as [ch0 w] eqn:F2.
cbv beta iota.
destruct (Fast.fast_two_sum sh0 (add t (add es fs))) as [sh sl] eqn:F3.
cbv beta iota.
destruct (Fast.fast_two_sum ch0 (add w (sub ec fc))) as [ch cl] eqn:F4.
cbv beta iota.
apply Rabs_le_inv in P1, P2, P3, P4, Eps, Eqs, Epc, Eqc, Hes, Hfs, Hec, Hfc.
cbn [bpow radix_val radix2 Z.opp] in *.
(* [sh0 + t = ps + qs], as [qs <= ps]: their difference is about sin (a
   - b). *)
destruct (fts ps qs sh0 t Fps Fqs) as (Fsh0 & Ft & _ & Bsh0 & Et);
  [apply Rabs_le; lra | rewrite (Rabs_pos_eq (B2R ps)), (Rabs_pos_eq (B2R qs)) by lra; lra
  | exact F1 |].
rewrite (Rabs_pos_eq (B2R ps + B2R qs)) in Bsh0 by lra.
apply Rabs_le_inv in Bsh0. cbn [bpow radix_val radix2 Z.opp] in Bsh0.
(* [ch0 + w = pc - qc], as [qc <= pc]: their difference is about cos (a
   + b). *)
destruct (opp_ok qc) as [Foq Eoq].
destruct (fts pc (opp qc) ch0 w Fpc) as (Fch0 & Fw & _ & Bch0 & Ew);
  [rewrite Foq; exact Fqc | rewrite Eoq; apply Rabs_le; lra
  | rewrite Eoq, Rabs_Ropp, (Rabs_pos_eq (B2R pc)), (Rabs_pos_eq (B2R qc)) by lra; lra
  | exact F2 |].
rewrite Eoq in Bch0, Ew.
rewrite (Rabs_pos_eq (B2R pc + - B2R qc)) in Bch0 by lra.
apply Rabs_le_inv in Bch0. cbn [bpow radix_val radix2 Z.opp] in Bch0.
(* The low parts: [u = es + fs] and [v = t + u] rounded, and the same
   for cos. *)
destruct (add_k es fs (bpow radix2 (-50)) Fes Ffs) as (Fu & _ & Bu);
  [apply Rabs_le; cbn [bpow radix_val radix2 Z.opp]; lra |
   cbn [bpow radix_val radix2 Z.opp]; lra |].
apply Rabs_le_inv in Bu. cbn [bpow radix_val radix2 Z.opp] in Bu.
destruct (add_k t (add es fs) (bpow radix2 (-49)) Ft Fu) as (Fv & _ & Bv);
  [apply Rabs_le; cbn [bpow radix_val radix2 Z.opp]; lra |
   cbn [bpow radix_val radix2 Z.opp]; lra |].
apply Rabs_le_inv in Bv. cbn [bpow radix_val radix2 Z.opp] in Bv.
destruct (sub_k ec fc (bpow radix2 (-50)) Fec Ffc) as (Fu' & _ & Bu');
  [apply Rabs_le; cbn [bpow radix_val radix2 Z.opp]; lra |
   cbn [bpow radix_val radix2 Z.opp]; lra |].
apply Rabs_le_inv in Bu'. cbn [bpow radix_val radix2 Z.opp] in Bu'.
destruct (add_k w (sub ec fc) (bpow radix2 (-49)) Fw Fu') as (Fv' & _ & Bv');
  [apply Rabs_le; cbn [bpow radix_val radix2 Z.opp]; lra |
   cbn [bpow radix_val radix2 Z.opp]; lra |].
apply Rabs_le_inv in Bv'. cbn [bpow radix_val radix2 Z.opp] in Bv'.
set (u := add es fs) in *. set (v := add t u) in *.
set (u' := sub ec fc) in *. set (v' := add w u') in *.
(* The final Fast2Sums: [sh + sl = sh0 + v] and [ch + cl = ch0 + v']. *)
destruct (fts sh0 v sh sl Fsh0 Fv) as (Fsh & Fsl & Esh & Bsh & Esl);
  [apply Rabs_le; lra | rewrite (Rabs_pos_eq (B2R sh0)) by lra; apply Rabs_le; lra
  | exact F3 |].
destruct (fts ch0 v' ch cl Fch0 Fv') as (Fch & Fcl & Ech & Bch & Ecl);
  [apply Rabs_le; lra | rewrite (Rabs_pos_eq (B2R ch0)) by lra; apply Rabs_le; lra
  | exact F4 |].
rewrite (Rabs_pos_eq (B2R sh0 + B2R v)) in Bsh by lra.
rewrite (Rabs_pos_eq (B2R ch0 + B2R v')) in Bch by lra.
apply Rabs_le_inv in Bsh, Bch. cbn [bpow radix_val radix2 Z.opp] in Bsh, Bch.
(* Each low part is at most 2^-53 times its high part. *)
pose proof (rn_rel (B2R sh0 + B2R v)) as Rsh.
pose proof (rn_rel (B2R ch0 + B2R v')) as Rch.
rewrite <- Esh in Rsh. rewrite <- Ech in Rch.
rewrite (Rabs_pos_eq (B2R sh0 + B2R v)), (Rabs_pos_eq (B2R sh)) in Rsh by lra.
rewrite (Rabs_pos_eq (B2R ch0 + B2R v')), (Rabs_pos_eq (B2R ch)) in Rch by lra.
cbn [bpow radix_val radix2 Z.opp] in Rsh, Rch.
assert (Rsh' : Rabs (B2R sh - (B2R sh0 + B2R v)) <= / IZR (Z.pow_pos 2 53) * B2R sh)
  by (apply Rsh; lra).
assert (Rch' : Rabs (B2R ch - (B2R ch0 + B2R v')) <= / IZR (Z.pow_pos 2 53) * B2R ch)
  by (apply Rch; lra).
apply Rabs_le_inv in Rsh', Rch'.
(* The errors add up to about [58 2^-106], below [2^-88 / 2500]. *)
split; [exact Fsh |]. split; [exact Fsl |]. split; [exact Fch |]. split; [exact Fcl |].
split; [apply Rabs_le; lra |].
split; [apply Rabs_le; lra |].
split; apply Rabs_le; lra.
Qed.

Theorem fast_sc_fma :
  forall i, (1 <= i <= 2047)%Z -> DyadicTrig.fast_sc true i = DyadicTrig.fast_sc false i.
Proof.
intros i Hi.
destruct (sc_index i Hi) as (E1 & E2 & Hd & Hi1 & Hi2).
unfold DyadicTrig.fast_sc. rewrite E1, E2.
set (i1 := (i / 64)%Z) in *. set (i2 := (i mod 64)%Z) in *.
clearbody i1 i2. subst i.
destruct (Z.eqb_spec i2 0) as [Z2|Z2]; [reflexivity |].
destruct (Z.eqb_spec i1 0) as [Z1|Z1]; [reflexivity |].
pose proof (sc1_correct i1 Hi1) as T1. pose proof (sc2_correct i2 ltac:(lia)) as T2.
revert T1 T2.
destruct (DyadicTrig.sc DyadicTrig.SC1 i1) as [[[s1h s1l] c1h] c1l].
destruct (DyadicTrig.sc DyadicTrig.SC2 i2) as [[[s2h s2l] c2h] c2l].
intros T1 T2. cbv beta iota in T1, T2 |- *.
destruct T1 as (Fs1h & _ & Fc1h & _ & Es1 & Ec1 & Ns1 & Nc1).
destruct T2 as (Fs2h & _ & Fc2h & _ & Es2 & Ec2 & Ns2 & Nc2).
(* Each row's high part is between 2^-13 and 2. *)
assert (A1 : IZR (64 * i1) * (PI / 4096) = IZR i1 * (PI / 64))
  by (rewrite mult_IZR; field).
destruct (angle_mid (64 * i1) ltac:(lia)) as [Sa Ca]. rewrite A1 in Sa, Ca.
destruct (angle_mid i2 ltac:(lia)) as [Sb Cb].
pose proof (row_bounds _ _ _ Es1 Ns1 Sa) as Hs1.
pose proof (row_bounds _ _ _ Ec1 Nc1 Ca) as Hc1.
pose proof (row_bounds _ _ _ Es2 Ns2 Sb) as Hs2.
pose proof (row_bounds _ _ _ Ec2 Nc2 Cb) as Hc2.
assert (H2 : 1 + bpow radix2 (-51) <= 2) by (cbn [bpow radix_val radix2 Z.opp]; lra).
rewrite (fast_mul_fma s1h s1l c2h c2l Fs1h Fc2h ltac:(lra) ltac:(lra)).
rewrite (fast_mul_fma c1h c1l s2h s2l Fc1h Fs2h ltac:(lra) ltac:(lra)).
rewrite (fast_mul_fma c1h c1l c2h c2l Fc1h Fc2h ltac:(lra) ltac:(lra)).
rewrite (fast_mul_fma s1h s1l s2h s2l Fs1h Fs2h ltac:(lra) ltac:(lra)).
reflexivity.
Qed.
