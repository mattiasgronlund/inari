(** * sin and cos of i π/4096 from the table

    [DyadicTrig.fast_sc false i] of [Model.v], for [i] in [1, 2047], is
    the row of [DyadicTrig.SC] at [i] for [i <= 1024] and, above, the row
    at [2048 - i] with its sin and cos swapped, as sin(π/2 - b) = cos b
    and cos(π/2 - b) = sin b. It reads the row at [i] up to 1024 and at
    [2048 - i] above it, and picks its halves by an index, 2 above 1024
    and 0 up to it, which [fast_sc_row] shows is that swap. The rows are
    within 2^-104 of sin and cos of their angles, with each low part at
    most 2^-53 times its high part ([sc_correct] of [FastTrigTables.v]),
    and sin and cos of i π/4096 are at least 1/2500 for these [i]
    ([angle_mid]), so [fast_sc] is sin and cos of i π/4096 in
    double-double within a relative 2^-88, with the low parts bounded as
    in the table ([fast_sc_correct]). It does not read its [fma]
    argument, so it is the same with an FMA ([fast_sc_fma], by
    [reflexivity]).

    This file does not use the lemmas of the section on [f64] steps:
    [FastTrigEval.v] uses [fts], [FastTrigCore.v] uses [opp_ok], a comment
    of [FastTrigEval.v] cites [prod_exact_sc] and one of [FastAhypAcosh.v]
    cites [rn_rel]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Flocq Require Import Relative.
From Inari Require Import Model TwoSum FastExpErr FastTrigTables.
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

(** ** Steps in [f64] *)

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

Lemma opp_ok : forall x, is_finite (opp x) = is_finite x /\ B2R (opp x) = - B2R x.
Proof. intros x. unfold opp. split; [apply is_finite_Bopp | apply B2R_Bopp]. Qed.

(** ** The lookup *)

(** A row's value within [2^-104] of a number of at least 1/2500 is
    within [2^-88] of it relatively. *)
Lemma row_rel :
  forall h l y, Rabs (h + l - y) <= bpow radix2 (-104) -> / 2500 <= y ->
  Rabs (h + l - y) <= bpow radix2 (-88) * y.
Proof. intros h l y H Hy. cbn [bpow radix_val radix2 Z.opp] in *. lra. Qed.

(** [fast_sc] reads the row at [i] up to 1024 and at [2048 - i] above it,
    and picks its halves by the index [k], 2 above 1024 and 0 up to it,
    which is the row at [i] up to 1024 and the row at [2048 - i] with its
    halves swapped above it. *)
Lemma fast_sc_row :
  forall fma i,
  DyadicTrig.fast_sc fma i =
  if (i <=? 1024)%Z then DyadicTrig.sc DyadicTrig.SC i
  else let '(sh, sl, ch, cl) := DyadicTrig.sc DyadicTrig.SC (2048 - i) in (ch, cl, sh, sl).
Proof.
intros fma i. unfold DyadicTrig.fast_sc.
destruct (Z.ltb_spec 1024 i); destruct (Z.leb_spec i 1024); try lia.
- destruct (DyadicTrig.sc DyadicTrig.SC (2048 - i)) as [[[sh sl] ch] cl]. reflexivity.
- destruct (DyadicTrig.sc DyadicTrig.SC i) as [[[sh sl] ch] cl]. reflexivity.
Qed.

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
rewrite fast_sc_row.
destruct (Z.leb_spec i 1024) as [Hle|Hgt].
- (* The row [i]. *)
  pose proof (sc_correct i ltac:(lia)) as T.
  destruct (angle_mid i Hi) as [[Sa _] [Ca _]].
  revert T. destruct (DyadicTrig.sc DyadicTrig.SC i) as [[[sh sl] ch] cl].
  intros (Fsh & Fsl & Fch & Fcl & Es & Ec & Ns & Nc).
  repeat split; try assumption; apply row_rel; assumption.
- (* The row [2048 - i] with its halves swapped, by sin(π/2 - b) = cos b
     and cos(π/2 - b) = sin b. *)
  pose proof (sc_correct (2048 - i) ltac:(lia)) as T.
  destruct (angle_mid (2048 - i) ltac:(lia)) as [[Sa _] [Ca _]].
  assert (E : IZR i * (PI / 4096) = PI / 2 - IZR (2048 - i) * (PI / 4096))
    by (rewrite minus_IZR; field).
  rewrite E, sin_shift, cos_shift.
  revert T. destruct (DyadicTrig.sc DyadicTrig.SC (2048 - i)) as [[[sh sl] ch] cl].
  intros (Fsh & Fsl & Fch & Fcl & Es & Ec & Ns & Nc).
  repeat split; try assumption; apply row_rel; assumption.
Qed.

Theorem fast_sc_fma :
  forall i, (1 <= i <= 2047)%Z -> DyadicTrig.fast_sc true i = DyadicTrig.fast_sc false i.
Proof. intros i _. reflexivity. Qed.
