(** * The evaluation of the fast paths of [sin], [cos] and [tan]

    [DyadicTrig.fast_eval false sh sl ch cl rh rl rr] of [Model.v] is
    sin(j π/4096 + ρ) = S cos ρ + C sin ρ within a relative 2^-71, for
    [S = sh + sl] and [C = ch + cl] within a relative 2^-88 of sin and cos
    of j π/4096, j in [1, 2047], and [rh + rl] within 2^-90 of ρ, |ρ| <=
    π/8192 (1 + 2^-24), with the Taylor polynomials of cos ρ - 1 to degree
    4 and of sin ρ - ρ to degree 5 ([fast_eval_correct]). [fast_sin0] and
    [fast_cos0] are sin x and cos x within a relative 2^-71 for 2^-27 <=
    |x| <= π/8192 (1 + 2^-24) ([fast_sin0_correct], [fast_cos0_correct]).
    [fast_eval] is the same with an FMA ([fast_eval_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr TwoSum TwoProduct FastRound FastExpErr FastExpTables
  TrigSeries.
From Inari Require CancelLanes MulRuTiny PiBounds TrigPieces FastTrigSC FastTrigGappa.

Open Scope R_scope.

(** ** Constants *)

(** Powers of 2 as numerals, for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp] in *.

Local Lemma half_F : is_finite half = true /\ B2R half = / 2.
Proof.
assert (H : fix_of 53 half = Some 4503599627370496%Z) by (vm_compute; reflexivity).
apply fix_of_correct in H as [F H]. split; [exact F|]. rewrite H. num. lra.
Qed.

Local Lemma one_F : is_finite Fast.one = true /\ B2R Fast.one = 1.
Proof. split; [vm_compute; reflexivity | exact one_R]. Qed.

(** [S3], [S5] and [C4] are 1/6, 1/120 and 1/24 rounded to nearest; [S3]
    and [C4] are the [P3] and [P4] of [exp]. *)
Local Lemma s3_F :
  is_finite (from_bits DyadicTrig.S3) = true /\
  Rabs (B2R (from_bits DyadicTrig.S3) - / 6) <= bpow radix2 (-56).
Proof. split; [vm_compute; reflexivity | exact p3_correct]. Qed.

Local Lemma c4_F :
  is_finite (from_bits DyadicTrig.C4) = true /\
  Rabs (B2R (from_bits DyadicTrig.C4) - / 24) <= bpow radix2 (-58).
Proof. split; [vm_compute; reflexivity | exact p4_correct]. Qed.

Local Lemma s5_F :
  is_finite (from_bits DyadicTrig.S5) = true /\
  Rabs (B2R (from_bits DyadicTrig.S5) - / 120) <= bpow radix2 (-62).
Proof.
assert (H : fix_of 59 (from_bits DyadicTrig.S5) = Some 4803839602528529%Z)
  by (vm_compute; reflexivity).
apply fix_of_correct in H as [F H]. split; [exact F|]. rewrite H. num.
apply Rabs_le. split; lra.
Qed.

(** π/8192 (1 + 2^-24) is below [M = 3835e-7], and π/8192 above
    [3834.9e-7]. *)
Local Lemma pi_M :
  3834.9e-7 <= PI / 8192 /\ PI / 8192 * (1 + bpow radix2 (-24)) <= 3835e-7.
Proof.
pose proof PiBounds.PI_Q as [H1 H2].
unfold Q2R, PiBounds.pi_lo, PiBounds.pi_hi in H1, H2. cbn [Qnum Qden] in H1, H2.
num. split; lra.
Qed.

(** ** Taylor polynomials of sin and cos *)

Local Ltac taylor odd k :=
  intros a Ha; destruct (trig_tail_bounds odd k a Ha) as (T & HT & E);
  exists T; split; [exact HT|];
  unfold trig_fn, trig_sum, trig_term in E; cbn [Nat.b2n Nat.mul Nat.add pow] in E;
  rewrite ?INR_IZR_INZ in E; cbn [fact Nat.mul Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in E;
  lra.

Local Lemma sin_t3 :
  forall a, Rabs a <= 1 -> exists T, 0 <= T <= 1 /\ sin a = a - a ^ 3 / 6 + T * (a ^ 5 / 120).
Proof. taylor true 2%nat. Qed.

Local Lemma sin_t5 :
  forall a, Rabs a <= 1 ->
  exists T, 0 <= T <= 1 /\ sin a = a - a ^ 3 / 6 + a ^ 5 / 120 - T * (a ^ 7 / 5040).
Proof. taylor true 3%nat. Qed.

Local Lemma cos_t2 :
  forall a, Rabs a <= 1 -> exists T, 0 <= T <= 1 /\ cos a = 1 - a ^ 2 / 2 + T * (a ^ 4 / 24).
Proof. taylor false 2%nat. Qed.

Local Lemma cos_t4 :
  forall a, Rabs a <= 1 ->
  exists T, 0 <= T <= 1 /\ cos a = 1 - a ^ 2 / 2 + a ^ 4 / 24 - T * (a ^ 6 / 720).
Proof. taylor false 3%nat. Qed.

(** ** The polynomials *)

(** [add_k], [sub_k] and [mul_k] for a named result [z], with the error
    as two inequalities for [lra] (as in [FastExpPoly.v]). *)
Local Lemma add_kz :
  forall x y z K, z = add x y -> is_finite x = true -> is_finite y = true ->
  Rabs (B2R x + B2R y) <= K -> K <= 16 ->
  is_finite z = true /\
  - (bpow radix2 (-53) * K + bpow radix2 (-1075)) <= B2R z - (B2R x + B2R y) <=
    bpow radix2 (-53) * K + bpow radix2 (-1075).
Proof.
intros x y z K -> Fx Fy H HK.
destruct (add_k x y K Fx Fy H HK) as (F & _ & B).
split; [exact F | apply Rabs_le_inv; exact B].
Qed.

Local Lemma sub_kz :
  forall x y z K, z = sub x y -> is_finite x = true -> is_finite y = true ->
  Rabs (B2R x - B2R y) <= K -> K <= 16 ->
  is_finite z = true /\
  - (bpow radix2 (-53) * K + bpow radix2 (-1075)) <= B2R z - (B2R x - B2R y) <=
    bpow radix2 (-53) * K + bpow radix2 (-1075).
Proof.
intros x y z K -> Fx Fy H HK.
destruct (sub_k x y K Fx Fy H HK) as (F & _ & B).
split; [exact F | apply Rabs_le_inv; exact B].
Qed.

Local Lemma mul_kz :
  forall x y z K, z = mul x y -> is_finite x = true -> is_finite y = true ->
  Rabs (B2R x * B2R y) <= K -> K <= 16 ->
  is_finite z = true /\
  - (bpow radix2 (-53) * K + bpow radix2 (-1075)) <= B2R z - B2R x * B2R y <=
    bpow radix2 (-53) * K + bpow radix2 (-1075).
Proof.
intros x y z K -> Fx Fy H HK.
destruct (mul_k x y K Fx Fy H HK) as (F & _ & B).
split; [exact F | apply Rabs_le_inv; exact B].
Qed.

(** [z = rr^2] rounded, for [|rr| <= X <= 2^-10]. *)
Local Lemma poly_z :
  forall rr X, is_finite rr = true -> Rabs (B2R rr) <= X -> X <= bpow radix2 (-10) ->
  is_finite (mul rr rr) = true /\
  Rabs (B2R (mul rr rr) - B2R rr * B2R rr) <= bpow radix2 (-53) * (X * X) + bpow radix2 (-1075) /\
  0 <= X /\ X * X <= bpow radix2 (-20) /\ X * X * X <= bpow radix2 (-30).
Proof.
intros rr X Frr HX HX10.
assert (X0 : 0 <= X) by (pose proof (Rabs_pos (B2R rr)); lra).
assert (XX : X * X <= bpow radix2 (-20)) by (num; nra).
assert (XXX : X * X * X <= bpow radix2 (-30)) by (num; nra).
assert (Hm : Rabs (B2R rr * B2R rr) <= X * X) by (apply Rabs_mul_le; assumption).
destruct (mul_kz rr rr (mul rr rr) _ eq_refl Frr Frr Hm ltac:(num; lra)) as (Fz & Bz).
repeat split; try assumption. apply Rabs_le. lra.
Qed.

(** [cm], the polynomial of cos [rr] - 1, within a relative [3/2 2^-53]
    of [X^2], for [|rr| <= X <= 2^-10]. *)
Local Lemma poly_cm :
  forall rr X, is_finite rr = true -> Rabs (B2R rr) <= X -> X <= bpow radix2 (-10) ->
  let z := mul rr rr in
  let cm := mul z (sub (mul z (from_bits DyadicTrig.C4)) half) in
  is_finite cm = true /\
  Rabs (B2R cm - B2R rr ^ 2 * (B2R rr ^ 2 / 24 - / 2)) <=
    bpow radix2 (-53) * X ^ 2 * (3 / 2 + bpow radix2 (-12)) + bpow radix2 (-1070).
Proof.
intros rr X Frr HX HX10. cbv zeta.
destruct (poly_z rr X Frr HX HX10) as (Fz & Bz & X0 & XX & XXX).
set (z := mul rr rr) in *.
set (w1 := mul z (from_bits DyadicTrig.C4)).
set (w2 := sub w1 half).
set (cm := mul z w2).
destruct half_F as (Fh & Eh). destruct c4_F as (F4 & H4).
set (C4 := from_bits DyadicTrig.C4) in *.
set (P := B2R rr) in *.
pose proof (Rabs_le_inv _ _ H4) as H4'.
pose proof (Rabs_le_inv _ _ HX) as HP.
pose proof (Rabs_le_inv _ _ Bz) as Bz'.
assert (PP : 0 <= P * P <= X * X) by (split; nra).
set (Zb := X * X * (1 + bpow radix2 (-53)) + bpow radix2 (-1075)).
assert (Wz : Rabs (B2R z) <= Zb) by (apply Rabs_le; unfold Zb; lra).
assert (Wz2 : Zb <= bpow radix2 (-19)) by (unfold Zb; num; lra).
(* [w1 = z C4] rounded, below [2^-23]. *)
assert (H14 : Rabs (B2R C4) <= / 16) by (apply Rabs_le; num; lra).
assert (Hm1 : Rabs (B2R z * B2R C4) <= bpow radix2 (-19) * / 16)
  by (apply Rabs_mul_le; [lra | exact H14]).
destruct (mul_kz z C4 w1 _ eq_refl Fz F4 Hm1 ltac:(num; lra)) as (Fw1 & B1).
assert (Hm1' := Rabs_le_inv _ _ Hm1).
(* [w2 = w1 - 1/2] rounded. *)
assert (Hs2 : Rabs (B2R w1 - B2R half) <= / 2 + bpow radix2 (-22))
  by (apply Rabs_le; rewrite Eh; num; lra).
destruct (sub_kz w1 half w2 _ eq_refl Fw1 Fh Hs2 ltac:(num; lra)) as (Fw2 & B2).
(* [w2] is [P^2/24 - 1/2] within [2^-54 + 2^-70]. *)
assert (Hd1 : Rabs ((B2R z - P * P) * B2R C4) <=
              (bpow radix2 (-53) * (X * X) + bpow radix2 (-1075)) * / 16)
  by (apply Rabs_mul_le; assumption).
assert (Hd2 : Rabs (P * P * (B2R C4 - / 24)) <= X * X * bpow radix2 (-58))
  by (apply Rabs_mul_le; [rewrite Rabs_pos_eq by lra; lra | exact H4]).
apply Rabs_le_inv in Hd1, Hd2.
assert (C2 : Rabs (B2R w2 - (P * P / 24 - / 2)) <= bpow radix2 (-54) + bpow radix2 (-70))
  by (apply Rabs_le; rewrite Eh in B2; num; lra).
assert (W2 : Rabs (B2R w2) <= / 2 + bpow radix2 (-20))
  by (apply Rabs_le; apply Rabs_le_inv in C2; num; lra).
(* [cm = z w2] rounded. *)
assert (Hm3 : Rabs (B2R z * B2R w2) <= Zb * (/ 2 + bpow radix2 (-20)))
  by (apply Rabs_mul_le; assumption).
destruct (mul_kz z w2 cm _ eq_refl Fz Fw2 Hm3 ltac:(num; lra)) as (Fcm & B3).
split; [exact Fcm|].
assert (Hq1 : Rabs ((B2R z - P * P) * B2R w2) <=
              (bpow radix2 (-53) * (X * X) + bpow radix2 (-1075)) * (/ 2 + bpow radix2 (-20)))
  by (apply Rabs_mul_le; assumption).
assert (Hq2 : Rabs (P * P * (B2R w2 - (P * P / 24 - / 2))) <=
              X * X * (bpow radix2 (-54) + bpow radix2 (-70)))
  by (apply Rabs_mul_le; [rewrite Rabs_pos_eq by lra; lra | exact C2]).
apply Rabs_le_inv in Hq1, Hq2.
replace (P ^ 2) with (P * P) by ring. replace (X ^ 2) with (X * X) by ring.
unfold Zb in B3.
clear - B3 Hq1 Hq2 XX X0.
apply Rabs_le. num. lra.
Qed.

(** [s3], the polynomial of sin [rr] - [rr], within [2^-53 X^3], for
    [|rr| <= X <= 2^-10]. *)
Local Lemma poly_s3 :
  forall rr X, is_finite rr = true -> Rabs (B2R rr) <= X -> X <= bpow radix2 (-10) ->
  let z := mul rr rr in
  let s3 := mul (mul rr z) (sub (mul z (from_bits DyadicTrig.S5)) (from_bits DyadicTrig.S3)) in
  is_finite s3 = true /\
  Rabs (B2R s3 - B2R rr ^ 3 * (B2R rr ^ 2 / 120 - / 6)) <=
    bpow radix2 (-53) * X ^ 3 + bpow radix2 (-1070).
Proof.
intros rr X Frr HX HX10. cbv zeta.
destruct (poly_z rr X Frr HX HX10) as (Fz & Bz & X0 & XX & XXX).
set (z := mul rr rr) in *.
set (v := mul rr z).
set (w3 := mul z (from_bits DyadicTrig.S5)).
set (w4 := sub w3 (from_bits DyadicTrig.S3)).
set (s3 := mul v w4).
destruct s3_F as (F3 & H3). destruct s5_F as (F5 & H5).
set (S3 := from_bits DyadicTrig.S3) in *.
set (S5 := from_bits DyadicTrig.S5) in *.
set (P := B2R rr) in *.
pose proof (Rabs_le_inv _ _ H3) as H3'.
pose proof (Rabs_le_inv _ _ H5) as H5'.
pose proof (Rabs_le_inv _ _ HX) as HP.
pose proof (Rabs_le_inv _ _ Bz) as Bz'.
assert (PP : 0 <= P * P <= X * X) by (split; nra).
set (Zb := X * X * (1 + bpow radix2 (-53)) + bpow radix2 (-1075)).
assert (Wz : Rabs (B2R z) <= Zb) by (apply Rabs_le; unfold Zb; lra).
assert (Wz2 : Zb <= bpow radix2 (-19)) by (unfold Zb; num; lra).
(* [v = rr z] rounded. *)
assert (Hmv : Rabs (P * B2R z) <= X * Zb) by (apply Rabs_mul_le; assumption).
destruct (mul_kz rr z v _ eq_refl Frr Fz Hmv ltac:(unfold Zb; num; lra)) as (Fv & Bv).
fold P in Bv.
set (Vb := X * Zb * (1 + bpow radix2 (-53)) + bpow radix2 (-1075)).
assert (Wv : Rabs (B2R v) <= Vb)
  by (apply Rabs_le; apply Rabs_le_inv in Hmv; unfold Vb; num; lra).
(* [w3 = z S5] rounded, below [2^-25]. *)
assert (H15 : Rabs (B2R S5) <= / 64) by (apply Rabs_le; num; lra).
assert (Hm3 : Rabs (B2R z * B2R S5) <= bpow radix2 (-19) * / 64)
  by (apply Rabs_mul_le; [lra | exact H15]).
destruct (mul_kz z S5 w3 _ eq_refl Fz F5 Hm3 ltac:(num; lra)) as (Fw3 & B3).
assert (Hm3' := Rabs_le_inv _ _ Hm3).
(* [w4 = w3 - S3] rounded. *)
assert (Hs4 : Rabs (B2R w3 - B2R S3) <= / 5) by (apply Rabs_le; num; lra).
destruct (sub_kz w3 S3 w4 _ eq_refl Fw3 F3 Hs4 ltac:(lra)) as (Fw4 & B4).
(* [w4] is [P^2/120 - 1/6] within [2^-53 / 3]. *)
assert (Hd1 : Rabs ((B2R z - P * P) * B2R S5) <=
              (bpow radix2 (-53) * (X * X) + bpow radix2 (-1075)) * / 64)
  by (apply Rabs_mul_le; assumption).
assert (Hd2 : Rabs (P * P * (B2R S5 - / 120)) <= X * X * bpow radix2 (-62))
  by (apply Rabs_mul_le; [rewrite Rabs_pos_eq by lra; lra | exact H5]).
apply Rabs_le_inv in Hd1, Hd2.
assert (C4 : Rabs (B2R w4 - (P * P / 120 - / 6)) <= bpow radix2 (-53) / 3)
  by (apply Rabs_le; num; lra).
assert (W4 : Rabs (B2R w4) <= / 5)
  by (apply Rabs_le; apply Rabs_le_inv in C4; num; lra).
(* [s3 = v w4] rounded. *)
assert (Hm5 : Rabs (B2R v * B2R w4) <= Vb * / 5) by (apply Rabs_mul_le; assumption).
destruct (mul_kz v w4 s3 _ eq_refl Fv Fw4 Hm5 ltac:(unfold Vb, Zb; num; lra)) as (Fs3 & B5).
split; [exact Fs3|].
assert (Hq1 : Rabs ((B2R v - P * B2R z) * B2R w4) <=
              (bpow radix2 (-53) * (X * Zb) + bpow radix2 (-1075)) * / 5)
  by (apply Rabs_mul_le; [apply Rabs_le; exact Bv | exact W4]).
assert (Hq2 : Rabs (P * (B2R z - P * P)) <=
              X * (bpow radix2 (-53) * (X * X) + bpow radix2 (-1075)))
  by (apply Rabs_mul_le; assumption).
assert (Hq3 : Rabs (P * (B2R z - P * P) * B2R w4) <=
              X * (bpow radix2 (-53) * (X * X) + bpow radix2 (-1075)) * / 5)
  by (apply Rabs_mul_le; assumption).
assert (PPP : Rabs (P * P * P) <= X * X * X)
  by (apply Rabs_mul_le; [apply Rabs_mul_le|]; assumption).
assert (Hq4 : Rabs (P * P * P * (B2R w4 - (P * P / 120 - / 6))) <=
              X * X * X * (bpow radix2 (-53) / 3))
  by (apply Rabs_mul_le; assumption).
apply Rabs_le_inv in Hq1, Hq3, Hq4.
replace (P ^ 3) with (P * P * P) by ring. replace (P ^ 2) with (P * P) by ring.
replace (X ^ 3) with (X * X * X) by ring.
unfold Vb, Zb in B5. unfold Zb in Hq1.
clear - B5 Hq1 Hq3 Hq4 XX XXX X0 HX10.
apply Rabs_le. num. lra.
Qed.

(** [ch rh] is an exact product for both values of the FMA flag: its
    rounded value has an exponent in [[-78, 1]], [ch] is at most 2 and
    [rh] at most 1 (as [FastTrigSC.prod_exact_sc]). *)
Local Lemma prod_exact_eval :
  forall b x y, is_finite x = true -> is_finite y = true ->
  bpow radix2 (-12) <= Rabs (B2R x) <= 2 -> bpow radix2 (-65) <= Rabs (B2R y) <= 1 ->
  Generic.two_prod_is_exact b x y (mul x y) = true.
Proof.
intros b x y Fx Fy Hx Hy.
assert (Hxy : bpow radix2 (-12) * bpow radix2 (-65) <= Rabs (B2R x * B2R y) <= 2 * 1).
{ rewrite Rabs_mult. pose proof (bpow_gt_0 radix2 (-12)). pose proof (bpow_gt_0 radix2 (-65)).
  split; apply Rmult_le_compat; lra. }
num.
destruct (mul_e x y Fx Fy ltac:(lra)) as (Fp & _ & Bp).
pose proof (Rabs_triang_inv (B2R x * B2R y) (B2R x * B2R y - B2R (mul x y))) as T1.
replace (B2R x * B2R y - (B2R x * B2R y - B2R (mul x y))) with (B2R (mul x y)) in T1 by ring.
rewrite Rabs_minus_sym in T1.
pose proof (Rabs_triang (B2R x * B2R y) (B2R (mul x y) - B2R x * B2R y)) as T2.
replace (B2R x * B2R y + (B2R (mul x y) - B2R x * B2R y)) with (B2R (mul x y)) in T2 by ring.
num.
assert (E1 : (-78 <= Generic.exponent (mul x y))%Z)
  by (apply MulRuTiny.exponent_ge; [exact Fp | num; lra]).
assert (E2 : (Generic.exponent (mul x y) < 2)%Z)
  by (apply MulRuTiny.exponent_lt; [exact Fp | lia | num; lra]).
assert (E3 : (Generic.exponent x < 2)%Z)
  by (apply MulRuTiny.exponent_lt; [exact Fx | lia | num; lra]).
assert (E4 : (Generic.exponent y < 1)%Z)
  by (apply MulRuTiny.exponent_lt; [exact Fy | lia | num; lra]).
unfold Generic.two_prod_is_exact. cbv zeta.
destruct b; rewrite ?andb_true_iff, ?Z.leb_le; lia.
Qed.

(** ** The magnitude of the result *)

(** [t cos t <= sin t] for [0 <= t <= 1], from the Taylor bounds of
    degree 3 of sin and 2 of cos. *)
Local Lemma tan_ge : forall t, 0 <= t <= 1 -> t * cos t <= sin t.
Proof.
intros t Ht.
assert (Ha : Rabs t <= 1) by (apply Rabs_le; lra).
destruct (sin_t3 t Ha) as (T1 & HT1 & Es).
destruct (cos_t2 t Ha) as (T2 & HT2 & Ec).
rewrite Es, Ec.
assert (P5 : 0 <= t ^ 5) by (apply pow_le; lra).
assert (P53 : t ^ 5 <= t ^ 3).
{ replace (t ^ 5) with (t ^ 3 * (t * t)) by ring.
  assert (0 <= t ^ 3) by (apply pow_le; lra).
  assert (t * t <= 1) by nra.
  pose proof (Rmult_le_compat_l (t ^ 3) (t * t) 1 ltac:(assumption) ltac:(assumption)). lra. }
assert (A1 : 0 <= T1 * t ^ 5) by (apply Rmult_le_pos; lra).
assert (A2 : T2 * t ^ 5 <= t ^ 5)
  by (pose proof (Rmult_le_compat_r (t ^ 5) T2 1 P5 (proj2 HT2)); lra).
replace (t * (1 - t ^ 2 / 2 + T2 * (t ^ 4 / 24))) with (t - t ^ 3 / 2 + T2 * t ^ 5 / 24)
  by field.
replace (T1 * (t ^ 5 / 120)) with (T1 * t ^ 5 / 120) by field.
lra.
Qed.

(** [cos t π/4096 <= sin t] between π/4096 and π/2 - π/4096: by
    [tan_ge] below 1, and as sin t >= 1/2 above 1. *)
Local Lemma cos_u_le :
  forall t, PI / 4096 <= t <= PI / 2 - PI / 4096 -> cos t * (PI / 4096) <= sin t.
Proof.
intros t Ht.
pose proof PI2_1 as HP. pose proof PI_4 as HP4.
assert (C0 : 0 <= cos t) by (apply cos_ge_0; lra).
destruct (Rle_or_lt t 1) as [H1|H1].
- pose proof (tan_ge t ltac:(lra)) as Ht'.
  assert (cos t * (PI / 4096) <= cos t * t) by (apply Rmult_le_compat_l; lra).
  lra.
- rewrite <- cos_shift. pose proof (FastTrigSC.cos_ge_half (PI / 2 - t) ltac:(lra)) as Hc.
  pose proof (COS_bound t) as [_ Cb].
  assert (cos t * (PI / 4096) <= 1 * (PI / 4096)) by (apply Rmult_le_compat_r; lra).
  lra.
Qed.

(** The result [E = sin (j π/4096 + ρ) = S cos ρ + C sin ρ] is at least
    about S/2, as [C |ρ| <= S/2 (1 + 2^-24)] by [cos_u_le], and at least
    sin of π/8192 (1 - 2^-24), as sin increases up to π/2. *)
Local Lemma eval_mag :
  forall j rho, (1 <= j <= 2047)%Z -> Rabs rho <= PI / 8192 * (1 + bpow radix2 (-24)) ->
  (/ 2 - bpow radix2 (-20)) * sin (IZR j * (PI / 4096)) <= sin (IZR j * (PI / 4096) + rho) /\
  3834e-7 <= sin (IZR j * (PI / 4096) + rho).
Proof.
intros j rho Hj Hr.
pose proof (FastTrigSC.mid_range j Hj) as Hm.
pose proof (FastTrigSC.angle_mid j Hj) as ((S0 & S1) & (C0 & C1)).
set (t := IZR j * (PI / 4096)) in *.
pose proof pi_M as [PL PM].
pose proof PI2_1 as HP. pose proof PI_4 as HP4.
pose proof (Rabs_le_inv _ _ Hr) as Hr'.
assert (RM : - 3835e-7 <= rho <= 3835e-7) by lra.
split.
- rewrite sin_plus.
  (* [cos ρ >= 1 - 10^-7]. *)
  assert (HR1 : Rabs rho <= 1) by (apply Rabs_le; lra).
  destruct (cos_t2 rho HR1) as (T & HT & Ec).
  assert (R2 : rho ^ 2 <= 2e-7) by (cbn [pow]; nra).
  assert (R4 : 0 <= rho ^ 4) by (replace (rho ^ 4) with ((rho * rho) * (rho * rho)) by ring;
    apply Rmult_le_pos; apply Rle_0_sqr).
  assert (A : 0 <= T * (rho ^ 4 / 24)) by (apply Rmult_le_pos; lra).
  assert (Co : 1 - 1e-7 <= cos rho) by (rewrite Ec; lra).
  (* [sin ρ >= - |ρ|]. *)
  assert (Si : - Rabs rho <= sin rho).
  { destruct (Rle_or_lt 0 rho) as [R0|R0].
    - pose proof (sin_ge_0 rho R0 ltac:(lra)). pose proof (Rabs_pos rho). lra.
    - rewrite Rabs_left by exact R0.
      pose proof (sin_lt_x (- rho) ltac:(lra)) as H. rewrite sin_neg in H. lra. }
  pose proof (cos_u_le t Hm) as Cu.
  assert (E1 : sin t * (1 - 1e-7) <= sin t * cos rho) by (apply Rmult_le_compat_l; lra).
  assert (E2 : cos t * (- Rabs rho) <= cos t * sin rho) by (apply Rmult_le_compat_l; lra).
  assert (E3 : cos t * Rabs rho <= cos t * (PI / 8192 * (1 + bpow radix2 (-24))))
    by (apply Rmult_le_compat_l; lra).
  assert (E4 : cos t * (PI / 4096) * (1 + bpow radix2 (-24)) <=
               sin t * (1 + bpow radix2 (-24)))
    by (apply Rmult_le_compat_r; [pose proof (bpow_gt_0 radix2 (-24)); lra | exact Cu]).
  replace (cos t * (PI / 8192 * (1 + bpow radix2 (-24))))
    with (cos t * (PI / 4096) * (1 + bpow radix2 (-24)) / 2) in E3 by field.
  num. lra.
- (* [c = π/8192 (1 - 2^-24) <= t + ρ <= π/2 - c], and sin increases. *)
  set (c := PI / 8192 * (1 - bpow radix2 (-24))).
  assert (Cc : 3834.8e-7 <= c <= 3835e-7) by (unfold c; num; lra).
  assert (Lo : c <= t + rho) by (unfold c; num; lra).
  assert (Hi : t + rho <= PI / 2) by (num; lra).
  pose proof (sin_incr_1 c (t + rho) ltac:(lra) ltac:(lra) ltac:(lra) Hi Lo) as Hs.
  assert (Hc1 : Rabs c <= 1) by (apply Rabs_le; lra).
  destruct (sin_t3 c Hc1) as (T & HT & Es).
  assert (P5 : 0 <= c ^ 5) by (apply pow_le; lra).
  assert (A : 0 <= T * (c ^ 5 / 120)) by (apply Rmult_le_pos; lra).
  assert (c * c <= 2e-7) by nra.
  assert (C3 : c ^ 3 <= 1e-10) by (replace (c ^ 3) with (c * (c * c)) by ring; nra).
  lra.
Qed.

(** ** The approximation, on the reals *)

(** The Taylor polynomials of degree 4 of cos and 5 of sin at [ρ], for
    [|ρ| <= 3835e-7], are within [3835e-7^6 / 720] and [3835e-7^7 /
    5040] of cos ρ and sin ρ. *)
Local Lemma taylor_rho :
  forall rho, Rabs rho <= 3835e-7 ->
  Rabs (cos rho - (1 + rho ^ 2 * (rho ^ 2 / 24 - / 2))) <= 443e-26 /\
  Rabs (sin rho - (rho + rho ^ 3 * (rho ^ 2 / 120 - / 6))) <= 243e-30.
Proof.
intros rho Hr.
assert (HR1 : Rabs rho <= 1) by lra.
pose proof (Rabs_pos rho) as A0.
destruct (cos_t4 rho HR1) as (T & HT & Ec).
destruct (sin_t5 rho HR1) as (U & HU & Es).
assert (P6 : Rabs (rho ^ 6 / 720) <= 3835e-7 ^ 6 / 720).
{ unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ 720)) by lra. rewrite <- RPow_abs.
  apply Rmult_le_compat_r; [lra | apply pow_incr; lra]. }
assert (P7 : Rabs (rho ^ 7 / 5040) <= 3835e-7 ^ 7 / 5040).
{ unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ 5040)) by lra. rewrite <- RPow_abs.
  apply Rmult_le_compat_r; [lra | apply pow_incr; lra]. }
assert (HT1 : Rabs T <= 1) by (apply Rabs_le; lra).
assert (HU1 : Rabs U <= 1) by (apply Rabs_le; lra).
pose proof (Rabs_mul_le _ _ _ _ HT1 P6) as B6.
pose proof (Rabs_mul_le _ _ _ _ HU1 P7) as B7.
split.
- replace (cos rho - (1 + rho ^ 2 * (rho ^ 2 / 24 - / 2))) with (- (T * (rho ^ 6 / 720)))
    by (rewrite Ec; field).
  rewrite Rabs_Ropp. lra.
- replace (sin rho - (rho + rho ^ 3 * (rho ^ 2 / 120 - / 6))) with (- (U * (rho ^ 7 / 5040)))
    by (rewrite Es; field).
  rewrite Rabs_Ropp. lra.
Qed.

(** [a^2] is between 0 and [X^2] for [|a| <= X]. *)
Local Lemma sq_le : forall a X, Rabs a <= X -> 0 <= a ^ 2 <= X * X.
Proof.
intros a X Ha.
rewrite <- pow2_abs. pose proof (Rabs_pos a).
split; [apply pow_le; lra|].
replace (Rabs a ^ 2) with (Rabs a * Rabs a) by ring.
apply Rmult_le_compat; lra.
Qed.

(** The polynomials [a^2 (a^2/24 - 1/2)] of cos a - 1 and [a^3 (a^2/120 -
    1/6)] of sin a - a are at most [X^2/2] and [X^3/6] in magnitude for
    [|a| <= X <= 1]. *)
Local Lemma pc_mag :
  forall a X, Rabs a <= X -> X <= 1 -> Rabs (a ^ 2 * (a ^ 2 / 24 - / 2)) <= X * X / 2.
Proof.
intros a X Ha HX.
pose proof (sq_le a X Ha) as A2.
pose proof (Rabs_pos a).
assert (X * X <= 1) by nra.
assert (Q : Rabs (a ^ 2 / 24 - / 2) <= / 2) by (apply Rabs_le; lra).
assert (Ra : Rabs (a ^ 2) <= X * X) by (rewrite Rabs_pos_eq; lra).
pose proof (Rabs_mul_le _ _ _ _ Ra Q). lra.
Qed.

Local Lemma ps_mag :
  forall a X, Rabs a <= X -> X <= 1 -> Rabs (a ^ 3 * (a ^ 2 / 120 - / 6)) <= X * X * X / 6.
Proof.
intros a X Ha HX.
pose proof (sq_le a X Ha) as A2.
pose proof (Rabs_pos a).
assert (X * X <= 1) by nra.
assert (Q : Rabs (a ^ 2 / 120 - / 6) <= / 6) by (apply Rabs_le; lra).
assert (Ra : Rabs (a ^ 3) <= X * X * X).
{ rewrite <- RPow_abs. replace (X * X * X) with (X ^ 3) by ring. apply pow_incr; lra. }
pose proof (Rabs_mul_le _ _ _ _ Ra Q). lra.
Qed.

(** The same polynomials are [X] and [X^2] Lipschitz on [[-X, X]], for
    [X <= 1], by the factorizations [(a - b) (a + b) ((a^2 + b^2)/24 -
    1/2)] and [(a - b) ((a^2 + a b + b^2) (a^2/120 - 1/6) + b^3 (a +
    b)/120)]. *)
Local Lemma pc_diff :
  forall a b X D, Rabs a <= X -> Rabs b <= X -> X <= 1 -> Rabs (a - b) <= D ->
  Rabs (a ^ 2 * (a ^ 2 / 24 - / 2) - b ^ 2 * (b ^ 2 / 24 - / 2)) <= X * D.
Proof.
intros a b X D Ha Hb HX Hd.
replace (a ^ 2 * (a ^ 2 / 24 - / 2) - b ^ 2 * (b ^ 2 / 24 - / 2))
  with ((a - b) * ((a + b) * ((a ^ 2 + b ^ 2) / 24 - / 2))) by field.
pose proof (sq_le a X Ha). pose proof (sq_le b X Hb).
pose proof (Rabs_pos a).
assert (X * X <= 1) by nra.
assert (Q : Rabs ((a ^ 2 + b ^ 2) / 24 - / 2) <= / 2) by (apply Rabs_le; lra).
assert (Hab : Rabs (a + b) <= 2 * X)
  by (pose proof (Rabs_triang a b); lra).
pose proof (Rabs_mul_le _ _ _ _ Hab Q) as M1.
pose proof (Rabs_mul_le _ _ _ _ Hd M1) as M2.
lra.
Qed.

Local Lemma ps_diff :
  forall a b X D, Rabs a <= X -> Rabs b <= X -> X <= 1 -> Rabs (a - b) <= D ->
  Rabs (a ^ 3 * (a ^ 2 / 120 - / 6) - b ^ 3 * (b ^ 2 / 120 - / 6)) <= X * X * D.
Proof.
intros a b X D Ha Hb HX Hd.
replace (a ^ 3 * (a ^ 2 / 120 - / 6) - b ^ 3 * (b ^ 2 / 120 - / 6))
  with ((a - b) * ((a * a + a * b + b * b) * (a * a / 120 - / 6) + b * b * b * (a + b) / 120))
  by field.
pose proof (sq_le a X Ha) as Sa. pose proof (sq_le b X Hb) as Sb.
replace (a ^ 2) with (a * a) in Sa by ring. replace (b ^ 2) with (b * b) in Sb by ring.
pose proof (Rabs_pos a).
assert (X0 : 0 <= X) by lra.
assert (XX : X * X <= 1) by nra.
assert (Hab : Rabs (a * b) <= X * X) by (apply Rabs_mul_le; assumption).
apply Rabs_le_inv in Hab.
assert (Q1 : Rabs (a * a + a * b + b * b) <= 3 * (X * X)) by (apply Rabs_le; lra).
assert (Q2 : Rabs (a * a / 120 - / 6) <= / 6) by (apply Rabs_le; lra).
pose proof (Rabs_mul_le _ _ _ _ Q1 Q2) as H1.
assert (Hbbb : Rabs (b * b * b) <= X * X * X)
  by (apply Rabs_mul_le; [apply Rabs_mul_le|]; assumption).
assert (Hs : Rabs (a + b) <= 2 * X) by (pose proof (Rabs_triang a b); lra).
pose proof (Rabs_mul_le _ _ _ _ Hbbb Hs) as H2.
assert (X4 : X * X * X * (2 * X) <= 2 * (X * X)).
{ replace (X * X * X * (2 * X)) with (2 * (X * X) * (X * X)) by ring.
  assert (0 <= 2 * (X * X)) by nra.
  pose proof (Rmult_le_compat_l (2 * (X * X)) (X * X) 1 ltac:(assumption) XX). lra. }
assert (H3 : Rabs (b * b * b * (a + b) / 120) <= 2 * (X * X) / 120).
{ unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ 120)) by lra.
  apply Rmult_le_compat_r; lra. }
assert (H4 : Rabs ((a * a + a * b + b * b) * (a * a / 120 - / 6) + b * b * b * (a + b) / 120)
             <= X * X)
  by (pose proof (Rabs_triang ((a * a + a * b + b * b) * (a * a / 120 - / 6))
        (b * b * b * (a + b) / 120)); lra).
pose proof (Rabs_mul_le _ _ _ _ Hd H4). lra.
Qed.

(** The value that [fast_eval] rounds, [sh + sl + ch w + cl rr + sh cm +
    ch s3] for [w = rh + rl], [rr] its rounding and [cm], [s3] the
    rounded polynomials at [rr], is [S cos ρ + C sin ρ] within [55e-24 S
    + 16e-27], by the split [(sh + sl - S) + (ch + cl - C) w + C (w - ρ)
    + cl (rr - w) + (sh - S) cm + S (cm - cos ρ + 1) + (ch - C) s3 + C
    (s3 - sin ρ + ρ)]. *)
Local Lemma eval_approx :
  forall sh sl ch cl w rr cm s3 rho S C,
  0 < S <= 1 -> 0 < C <= 1 ->
  Rabs (sh + sl - S) <= bpow radix2 (-88) * S ->
  Rabs (ch + cl - C) <= bpow radix2 (-88) * C ->
  Rabs sl <= bpow radix2 (-53) * sh -> Rabs cl <= bpow radix2 (-53) * ch ->
  Rabs rho <= 3835e-7 -> Rabs w <= 3836e-7 -> Rabs rr <= 3836e-7 ->
  Rabs (rho - w) <= bpow radix2 (-90) ->
  Rabs (rr - w) <= bpow radix2 (-53) * 3836e-7 + bpow radix2 (-1075) ->
  Rabs (cm - rr ^ 2 * (rr ^ 2 / 24 - / 2)) <=
    bpow radix2 (-53) * 3836e-7 ^ 2 * (3 / 2 + bpow radix2 (-12)) + bpow radix2 (-1070) ->
  Rabs (s3 - rr ^ 3 * (rr ^ 2 / 120 - / 6)) <=
    bpow radix2 (-53) * 3836e-7 ^ 3 + bpow radix2 (-1070) ->
  Rabs (sh + sl + ch * w + cl * rr + sh * cm + ch * s3 - (S * cos rho + C * sin rho)) <=
    55e-24 * S + 16e-27.
Proof.
intros sh sl ch cl w rr cm s3 rho S C HS HC ES EC Lsl Lcl Hrho Hw Hrr Hrw Hrrw Hcm Hs3.
pose proof (Rabs_le_inv _ _ ES) as ES'.
pose proof (Rabs_le_inv _ _ EC) as EC'.
pose proof (Rabs_le_inv _ _ Lsl) as Lsl'.
pose proof (Rabs_le_inv _ _ Lcl) as Lcl'.
(* [rr] is within [D] of [ρ]. *)
assert (Hwr : Rabs (w - rho) <= bpow radix2 (-90)) by (rewrite Rabs_minus_sym; exact Hrw).
assert (Hrr_rho : Rabs (rr - rho) <=
                  bpow radix2 (-53) * 3836e-7 + bpow radix2 (-1075) + bpow radix2 (-90)).
{ pose proof (Rabs_triang (rr - w) (w - rho)) as T.
  replace (rr - w + (w - rho)) with (rr - rho) in T by ring. lra. }
assert (X1 : 3836e-7 <= 1) by lra.
assert (Hrho' : Rabs rho <= 3836e-7) by lra.
destruct (taylor_rho rho Hrho) as [Tc Ts].
pose proof (pc_mag rr _ Hrr X1) as Mc.
pose proof (ps_mag rr _ Hrr X1) as Ms.
pose proof (pc_diff rr rho _ _ Hrr Hrho' X1 Hrr_rho) as Dc.
pose proof (ps_diff rr rho _ _ Hrr Hrho' X1 Hrr_rho) as Ds.
(* [cm] and [s3] in magnitude. *)
assert (Kcm : Rabs cm <= 3836e-7 * 3836e-7 / 2 +
  (bpow radix2 (-53) * 3836e-7 ^ 2 * (3 / 2 + bpow radix2 (-12)) + bpow radix2 (-1070))).
{ pose proof (Rabs_triang (cm - rr ^ 2 * (rr ^ 2 / 24 - / 2)) (rr ^ 2 * (rr ^ 2 / 24 - / 2)))
    as T.
  replace (cm - rr ^ 2 * (rr ^ 2 / 24 - / 2) + rr ^ 2 * (rr ^ 2 / 24 - / 2)) with cm in T
    by ring.
  lra. }
assert (Ks3 : Rabs s3 <= 3836e-7 * 3836e-7 * 3836e-7 / 6 +
  (bpow radix2 (-53) * 3836e-7 ^ 3 + bpow radix2 (-1070))).
{ pose proof (Rabs_triang (s3 - rr ^ 3 * (rr ^ 2 / 120 - / 6)) (rr ^ 3 * (rr ^ 2 / 120 - / 6)))
    as T.
  replace (s3 - rr ^ 3 * (rr ^ 2 / 120 - / 6) + rr ^ 3 * (rr ^ 2 / 120 - / 6)) with s3 in T
    by ring.
  lra. }
(* The eight terms. *)
assert (Eq : sh + sl + ch * w + cl * rr + sh * cm + ch * s3 - (S * cos rho + C * sin rho) =
  (sh + sl - S) + (ch + cl - C) * w + C * (w - rho) + cl * (rr - w) + (sh - S) * cm
  + S * (cm - cos rho + 1) + (ch - C) * s3 + C * (s3 - sin rho + rho)) by ring.
rewrite Eq.
assert (C1 : Rabs C <= 1) by (rewrite Rabs_pos_eq; lra).
assert (S1 : Rabs S <= S) by (rewrite Rabs_pos_eq; lra).
assert (EC1 : Rabs (ch + cl - C) <= bpow radix2 (-88)) by (apply Rabs_le; num; lra).
pose proof (Rabs_mul_le _ _ _ _ EC1 Hw) as B2.
pose proof (Rabs_mul_le _ _ _ _ C1 Hwr) as B3.
assert (Hcl : Rabs cl <= 1.1103e-16) by (apply Rabs_le; num; lra).
pose proof (Rabs_mul_le _ _ _ _ Hcl Hrrw) as B4.
assert (DS : Rabs (sh - S) <= 1.1103e-16 * S) by (apply Rabs_le; num; lra).
pose proof (Rabs_mul_le _ _ _ _ DS Kcm) as B5.
assert (Y6 : Rabs (cm - cos rho + 1) <=
  (bpow radix2 (-53) * 3836e-7 ^ 2 * (3 / 2 + bpow radix2 (-12)) + bpow radix2 (-1070)) +
  3836e-7 * (bpow radix2 (-53) * 3836e-7 + bpow radix2 (-1075) + bpow radix2 (-90)) + 443e-26).
{ apply Rabs_le. apply Rabs_le_inv in Hcm, Dc, Tc. lra. }
pose proof (Rabs_mul_le _ _ _ _ S1 Y6) as B6.
assert (DC : Rabs (ch - C) <= 1.1103e-16) by (apply Rabs_le; num; lra).
pose proof (Rabs_mul_le _ _ _ _ DC Ks3) as B7.
assert (Y8 : Rabs (s3 - sin rho + rho) <=
  (bpow radix2 (-53) * 3836e-7 ^ 3 + bpow radix2 (-1070)) +
  3836e-7 * 3836e-7 * (bpow radix2 (-53) * 3836e-7 + bpow radix2 (-1075) + bpow radix2 (-90)) +
  243e-30).
{ apply Rabs_le. apply Rabs_le_inv in Hs3, Ds, Ts. lra. }
pose proof (Rabs_mul_le _ _ _ _ C1 Y8) as B8.
apply Rabs_le_inv in B2, B3, B4, B5, B6, B7, B8.
clear - ES' B2 B3 B4 B5 B6 B7 B8 HS.
apply Rabs_le. num. lra.
Qed.

(** The bound of [fast_eval_correct] from those of the approximation
    ([eval_approx]) and of the roundings, as [E] is at least about [S/2]
    and at least [3834e-7] ([eval_mag]). *)
Local Lemma eval_final :
  forall V HL S E, 0 < S ->
  (/ 2 - bpow radix2 (-20)) * S <= E -> 3834e-7 <= E ->
  Rabs (V - E) <= 55e-24 * S + 16e-27 ->
  Rabs (HL - V) <= 34e-24 * S + 11e-27 ->
  Rabs (HL - E) <= bpow radix2 (-71) * E.
Proof.
intros V HL S E HS H1 H2 A B.
apply Rabs_le_inv in A, B.
apply Rabs_le. num. lra.
Qed.

(** ** The roundings *)

(** [a + ae], for [a = ch rh] rounded and [ae] its exact error plus [ch
    rl + cl rr] rounded, is [ch (rh + rl) + cl rr] within [2^-88]: the
    product [ch rh] is exact as a TwoProduct, and the three roundings of
    [ae] add about [3 2^-90]. *)
Local Lemma eval_ae :
  forall ch cl rh rl rr,
  is_finite ch = true -> is_finite cl = true -> is_finite rh = true -> is_finite rl = true ->
  is_finite rr = true ->
  bpow radix2 (-12) <= Rabs (B2R ch) <= 1 + bpow radix2 (-52) ->
  Rabs (B2R cl) <= bpow radix2 (-53) * (1 + bpow radix2 (-52)) ->
  bpow radix2 (-65) <= Rabs (B2R rh) <= 3836e-7 ->
  Rabs (B2R rl) <= bpow radix2 (-37) -> Rabs (B2R rr) <= 3836e-7 ->
  let a := mul ch rh in
  let ae := add (Generic.two_prod_err false ch rh a) (add (mul ch rl) (mul cl rr)) in
  is_finite a = true /\ is_finite ae = true /\ Rabs (B2R a) <= 3837e-7 /\
  Rabs (B2R ae) <= bpow radix2 (-37) * (1 + bpow radix2 (-24)) /\
  Rabs (B2R a + B2R ae - (B2R ch * (B2R rh + B2R rl) + B2R cl * B2R rr)) <= bpow radix2 (-88).
Proof.
intros ch cl rh rl rr Fch Fcl Frh Frl Frr Hch Hcl Hrh Hrl Hrr. cbv zeta.
assert (Hch2 : bpow radix2 (-12) <= Rabs (B2R ch) <= 2) by (num; lra).
assert (Hrh1 : bpow radix2 (-65) <= Rabs (B2R rh) <= 1) by lra.
pose proof (prod_exact_eval false ch rh Fch Frh Hch2 Hrh1) as Hex.
destruct (two_prod_err_correct false ch rh Fch Frh Hex) as (Fa & Ea & _ & Fe0 & Ee0).
set (a := mul ch rh) in *.
set (e0 := Generic.two_prod_err false ch rh a) in *.
(* [a] is [ch rh] rounded, and [e0] its exact error. *)
assert (Pa : Rabs (B2R ch * B2R rh) <= (1 + bpow radix2 (-52)) * 3836e-7)
  by (apply Rabs_mul_le; lra).
pose proof (rn_err (B2R ch * B2R rh)) as Ba. rewrite <- Ea in Ba.
pose proof (Rabs_le_inv _ _ Pa) as Pa'.
assert (Ba' : Rabs (B2R a - B2R ch * B2R rh) <=
              bpow radix2 (-53) * ((1 + bpow radix2 (-52)) * 3836e-7) + bpow radix2 (-1075))
  by (num; lra).
apply Rabs_le_inv in Ba'.
(* [p1 = ch rl] and [p2 = cl rr] rounded, and their sum [q1]. *)
set (p1 := mul ch rl). set (p2 := mul cl rr). set (q1 := add p1 p2).
set (ae := add e0 q1).
assert (M1 : Rabs (B2R ch * B2R rl) <= (1 + bpow radix2 (-52)) * bpow radix2 (-37))
  by (apply Rabs_mul_le; lra).
destruct (mul_kz ch rl p1 _ eq_refl Fch Frl M1 ltac:(num; lra)) as (Fp1 & B1).
assert (M2 : Rabs (B2R cl * B2R rr) <= bpow radix2 (-53) * (1 + bpow radix2 (-52)) * 3836e-7)
  by (apply Rabs_mul_le; lra).
destruct (mul_kz cl rr p2 _ eq_refl Fcl Frr M2 ltac:(num; lra)) as (Fp2 & B2).
apply Rabs_le_inv in M1, M2.
assert (A1 : Rabs (B2R p1 + B2R p2) <= bpow radix2 (-37) * (1 + bpow radix2 (-26)))
  by (apply Rabs_le; num; lra).
destruct (add_kz p1 p2 q1 _ eq_refl Fp1 Fp2 A1 ltac:(num; lra)) as (Fq1 & B3).
apply Rabs_le_inv in A1.
(* [ae = e0 + q1] rounded. *)
assert (A2 : Rabs (B2R e0 + B2R q1) <= bpow radix2 (-37) * (1 + bpow radix2 (-25)))
  by (apply Rabs_le; rewrite Ee0; num; lra).
destruct (add_kz e0 q1 ae _ eq_refl Fe0 Fq1 A2 ltac:(num; lra)) as (Fae & B4).
apply Rabs_le_inv in A2.
split; [exact Fa|]. split; [exact Fae|]. split; [|split].
- apply Rabs_le. num. lra.
- apply Rabs_le. num. lra.
- rewrite Ee0 in B4. apply Rabs_le. num. lra.
Qed.

(** The low part [l = t + (((sl + ae) + sh cm) + ch s3)], summed in
    [f64], is at most about [74e-9 S] and within [33e-24 S + 7e-27] of
    the exact sum: six roundings of sums below [740e-10 S + 2^-37]. *)
Local Lemma eval_tail :
  forall S t sl ae sh cm ch s3,
  is_finite t = true -> is_finite sl = true -> is_finite ae = true -> is_finite sh = true ->
  is_finite cm = true -> is_finite ch = true -> is_finite s3 = true ->
  0 < S <= 1 ->
  Rabs (B2R t) <= bpow radix2 (-51) * S ->
  Rabs (B2R sl) <= bpow radix2 (-53) * (1 + bpow radix2 (-52)) * S ->
  Rabs (B2R ae) <= bpow radix2 (-37) * (1 + bpow radix2 (-24)) ->
  Rabs (B2R sh) <= (1 + bpow radix2 (-52)) * S ->
  Rabs (B2R cm) <= 736e-10 -> Rabs (B2R ch) <= 1 + bpow radix2 (-52) ->
  Rabs (B2R s3) <= 941e-14 ->
  let l := add t (add (add (add sl ae) (mul sh cm)) (mul ch s3)) in
  is_finite l = true /\ Rabs (B2R l) <= 74e-9 * S + 18e-12 /\
  Rabs (B2R l - (B2R t + B2R sl + B2R ae + B2R sh * B2R cm + B2R ch * B2R s3)) <=
    33e-24 * S + 7e-27.
Proof.
intros S t sl ae sh cm ch s3 Ft Fsl Fae Fsh Fcm Fch Fs3 HS Ht Hsl Hae Hsh Hcm Hch Hs3.
cbv zeta.
set (g1 := add sl ae). set (m1 := mul sh cm). set (g2 := add g1 m1).
set (m2 := mul ch s3). set (g3 := add g2 m2). set (l := add t g3).
apply Rabs_le_inv in Ht, Hsl, Hae.
(* [g1 = sl + ae] rounded. *)
assert (A1 : Rabs (B2R sl + B2R ae) <=
             bpow radix2 (-53) * (1 + bpow radix2 (-52)) * S +
             bpow radix2 (-37) * (1 + bpow radix2 (-24)))
  by (apply Rabs_le; lra).
destruct (add_kz sl ae g1 _ eq_refl Fsl Fae A1 ltac:(num; lra)) as (Fg1 & B1).
apply Rabs_le_inv in A1.
(* [m1 = sh cm] rounded. *)
assert (M1 : Rabs (B2R sh * B2R cm) <= (1 + bpow radix2 (-52)) * S * 736e-10)
  by (apply Rabs_mul_le; assumption).
destruct (mul_kz sh cm m1 _ eq_refl Fsh Fcm M1 ltac:(num; lra)) as (Fm1 & B2).
apply Rabs_le_inv in M1.
(* [g2 = g1 + m1] rounded. *)
assert (A2 : Rabs (B2R g1 + B2R m1) <= 738e-10 * S + bpow radix2 (-37) * (1 + bpow radix2 (-23)))
  by (apply Rabs_le; num; lra).
destruct (add_kz g1 m1 g2 _ eq_refl Fg1 Fm1 A2 ltac:(num; lra)) as (Fg2 & B3).
apply Rabs_le_inv in A2.
(* [m2 = ch s3] rounded. *)
assert (M2 : Rabs (B2R ch * B2R s3) <= (1 + bpow radix2 (-52)) * 941e-14)
  by (apply Rabs_mul_le; assumption).
destruct (mul_kz ch s3 m2 _ eq_refl Fch Fs3 M2 ltac:(num; lra)) as (Fm2 & B4).
apply Rabs_le_inv in M2.
(* [g3 = g2 + m2] rounded. *)
assert (A3 : Rabs (B2R g2 + B2R m2) <= 739e-10 * S + 17e-12)
  by (apply Rabs_le; num; lra).
destruct (add_kz g2 m2 g3 _ eq_refl Fg2 Fm2 A3 ltac:(num; lra)) as (Fg3 & B5).
apply Rabs_le_inv in A3.
(* [l = t + g3] rounded. *)
assert (A4 : Rabs (B2R t + B2R g3) <= 740e-10 * S + 171e-13)
  by (apply Rabs_le; num; lra).
destruct (add_kz t g3 l _ eq_refl Ft Fg3 A4 ltac:(num; lra)) as (Fl & B6).
apply Rabs_le_inv in A4.
split; [exact Fl|]. split.
- apply Rabs_le. num. lra.
- apply Rabs_le. num. lra.
Qed.

Theorem fast_eval_correct :
  forall j sh sl ch cl rh rl rr rho,
  (1 <= j <= 2047)%Z ->
  is_finite sh = true -> is_finite sl = true -> is_finite ch = true -> is_finite cl = true ->
  is_finite rh = true -> is_finite rl = true -> is_finite rr = true ->
  B2R rr = RN (B2R rh + B2R rl) ->
  Rabs (B2R sh + B2R sl - sin (IZR j * (PI / 4096))) <=
    bpow radix2 (-88) * sin (IZR j * (PI / 4096)) ->
  Rabs (B2R ch + B2R cl - cos (IZR j * (PI / 4096))) <=
    bpow radix2 (-88) * cos (IZR j * (PI / 4096)) ->
  Rabs (B2R sl) <= bpow radix2 (-53) * B2R sh ->
  Rabs (B2R cl) <= bpow radix2 (-53) * B2R ch ->
  Rabs rho <= PI / 8192 * (1 + bpow radix2 (-24)) ->
  Rabs (rho - (B2R rh + B2R rl)) <= bpow radix2 (-90) ->
  Rabs (B2R rl) <= bpow radix2 (-37) ->
  bpow radix2 (-65) <= Rabs (B2R rh) ->
  let '(h, l) := DyadicTrig.fast_eval false sh sl ch cl rh rl rr in
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  Rabs (B2R h + B2R l - sin (IZR j * (PI / 4096) + rho)) <=
    bpow radix2 (-71) * sin (IZR j * (PI / 4096) + rho).
Proof.
intros j sh sl ch cl rh rl rr rho Hj Fsh Fsl Fch Fcl Frh Frl Frr Err ES EC Lsl Lcl Hrho Hw Hrl
  Hrh.
unfold DyadicTrig.fast_eval. cbv zeta.
destruct (eval_mag j rho Hj Hrho) as (Mg1 & Mg2).
assert (Esp : sin (IZR j * (PI / 4096) + rho) =
              sin (IZR j * (PI / 4096)) * cos rho + cos (IZR j * (PI / 4096)) * sin rho)
  by apply sin_plus.
pose proof (FastTrigSC.angle_mid j Hj) as ((S0 & S1) & (C0 & C1)).
set (S := sin (IZR j * (PI / 4096))) in *.
set (C := cos (IZR j * (PI / 4096))) in *.
assert (HS : 0 < S <= 1) by lra.
assert (HC : 0 < C <= 1) by lra.
(* [sh] and [ch] are within a relative [2^-52] of [S] and [C]. *)
pose proof (Rabs_le_inv _ _ ES) as ES'. pose proof (Rabs_le_inv _ _ EC) as EC'.
pose proof (Rabs_le_inv _ _ Lsl) as Lsl'. pose proof (Rabs_le_inv _ _ Lcl) as Lcl'.
assert (Hsh : S * (1 - bpow radix2 (-52)) <= B2R sh <= S * (1 + bpow radix2 (-52)))
  by (num; split; lra).
assert (Hch : C * (1 - bpow radix2 (-52)) <= B2R ch <= C * (1 + bpow radix2 (-52)))
  by (num; split; lra).
assert (Hch12 : bpow radix2 (-12) <= Rabs (B2R ch) <= 1 + bpow radix2 (-52))
  by (rewrite Rabs_pos_eq by (num; lra); num; split; lra).
assert (Hcl : Rabs (B2R cl) <= bpow radix2 (-53) * (1 + bpow radix2 (-52))) by (num; lra).
assert (Hsl : Rabs (B2R sl) <= bpow radix2 (-53) * (1 + bpow radix2 (-52)) * S) by (num; lra).
assert (Hsh1 : Rabs (B2R sh) <= (1 + bpow radix2 (-52)) * S)
  by (rewrite Rabs_pos_eq by (num; lra); lra).
(* [ρ], [w = rh + rl], [rh] and [rr] are at most [3836e-7]. *)
pose proof pi_M as [PL PM].
assert (Hrho' : Rabs rho <= 3835e-7) by lra.
pose proof (Rabs_le_inv _ _ Hrho') as Hrho''.
pose proof (Rabs_le_inv _ _ Hw) as Hw'.
pose proof (Rabs_le_inv _ _ Hrl) as Hrl'.
assert (Hw36 : Rabs (B2R rh + B2R rl) <= 3836e-7) by (apply Rabs_le; num; lra).
assert (Hrh36 : Rabs (B2R rh) <= 3836e-7) by (apply Rabs_le; num; lra).
pose proof (rn_err (B2R rh + B2R rl)) as Brr. rewrite <- Err in Brr.
assert (Hrrw : Rabs (B2R rr - (B2R rh + B2R rl)) <=
               bpow radix2 (-53) * 3836e-7 + bpow radix2 (-1075)) by (num; lra).
assert (Hrr : Rabs (B2R rr) <= 3836e-7)
  by (apply Rabs_le; apply Rabs_le_inv in Hrrw; num; lra).
(* The polynomials at [rr], with the round-off bounds of [FastTrigGappa]. *)
destruct (FastTrigGappa.poly_cm_gappa rr Frr Hrr) as [Fcm Bcm]. cbv zeta in Fcm, Bcm.
destruct (FastTrigGappa.poly_s3_gappa rr Frr Hrr) as [Fs3 Bs3]. cbv zeta in Fs3, Bs3.
set (cm := mul (mul rr rr) (sub (mul (mul rr rr) (from_bits DyadicTrig.C4)) half)) in *.
set (s3 := mul (mul rr (mul rr rr))
             (sub (mul (mul rr rr) (from_bits DyadicTrig.S5)) (from_bits DyadicTrig.S3))) in *.
pose proof (pc_mag (B2R rr) 3836e-7 Hrr ltac:(lra)) as Mc.
pose proof (ps_mag (B2R rr) 3836e-7 Hrr ltac:(lra)) as Ms.
assert (Kcm : Rabs (B2R cm) <= 736e-10)
  by (apply Rabs_le; apply Rabs_le_inv in Bcm, Mc; num; lra).
assert (Ks3 : Rabs (B2R s3) <= 941e-14)
  by (apply Rabs_le; apply Rabs_le_inv in Bs3, Ms; num; lra).
(* [a + ae] is [ch w + cl rr] within [2^-88]. *)
destruct (eval_ae ch cl rh rl rr Fch Fcl Frh Frl Frr Hch12 Hcl (conj Hrh Hrh36) Hrl Hrr)
  as (Fa & Fae & Ka & Kae & Eae).
set (a := mul ch rh) in *.
set (ae := add (Generic.two_prod_err false ch rh a) (add (mul ch rl) (mul cl rr))) in *.
(* [h + t = sh + a] by Fast2Sum, as [|a| <= 3837e-7 < sh]. *)
pose proof (Rabs_le_inv _ _ Ka) as Ka'.
assert (Hle1 : Rabs (B2R a) <= Rabs (B2R sh)) by (rewrite (Rabs_pos_eq (B2R sh)); num; lra).
assert (Hsa : Rabs (B2R sh + B2R a) <= (1 + bpow radix2 (-52)) * S + 3837e-7)
  by (apply Rabs_le; num; lra).
destruct (Fast.fast_two_sum sh a) as [h t] eqn:E1. cbv beta iota.
destruct (FastTrigSC.fts sh a h t Fsh Fa ltac:(num; lra) Hle1 E1) as (Fh & Ft & _ & Bh & Et).
assert (Ht : Rabs (B2R t) <= bpow radix2 (-51) * S)
  by (rewrite Et; apply Rabs_le; apply Rabs_le_inv in Bh; num; lra).
assert (Hh : 15e-6 <= B2R h <= 2) by (apply Rabs_le_inv in Bh; num; lra).
(* The low part [l]. *)
destruct (eval_tail S t sl ae sh cm ch s3 Ft Fsl Fae Fsh Fcm Fch Fs3 HS Ht Hsl Kae Hsh1 Kcm
  ltac:(lra) Ks3) as (Fl & Kl & El).
set (l := add t (add (add (add sl ae) (mul sh cm)) (mul ch s3))) in *.
pose proof (Rabs_le_inv _ _ Kl) as Kl'.
(* [H + L = h + l] by Fast2Sum, as [|l| <= 75e-9 < h]. *)
assert (Hle2 : Rabs (B2R l) <= Rabs (B2R h)) by (rewrite (Rabs_pos_eq (B2R h)); lra).
destruct (Fast.fast_two_sum h l) as [H L] eqn:E2. cbv beta iota.
destruct (FastTrigSC.fts h l H L Fh Fl ltac:(apply Rabs_le; lra) Hle2 E2)
  as (FH & FL & EH & _ & EL).
assert (HL : B2R H + B2R L = B2R h + B2R l) by (rewrite EL; ring).
split; [exact FH|]. split; [exact FL|]. split; [rewrite HL; exact EH|].
rewrite HL.
(* The approximation and the roundings. *)
pose proof (eval_approx (B2R sh) (B2R sl) (B2R ch) (B2R cl) (B2R rh + B2R rl) (B2R rr) (B2R cm)
  (B2R s3) rho S C HS HC ES EC Lsl Lcl Hrho' Hw36 Hrr Hw Hrrw Bcm Bs3) as Ap.
rewrite <- Esp in Ap.
assert (Er : Rabs (B2R h + B2R l -
                   (B2R sh + B2R sl + B2R ch * (B2R rh + B2R rl) + B2R cl * B2R rr +
                    B2R sh * B2R cm + B2R ch * B2R s3)) <= 34e-24 * S + 11e-27)
  by (apply Rabs_le; apply Rabs_le_inv in El, Eae; num; lra).
exact (eval_final _ _ S _ (proj1 HS) Mg1 Mg2 Ap Er).
Qed.

Theorem fast_eval_fma :
  forall sh sl ch cl rh rl rr,
  is_finite ch = true -> is_finite rh = true ->
  bpow radix2 (-12) <= B2R ch <= 1 -> bpow radix2 (-65) <= Rabs (B2R rh) <= 1 ->
  DyadicTrig.fast_eval true sh sl ch cl rh rl rr = DyadicTrig.fast_eval false sh sl ch cl rh rl rr.
Proof.
intros sh sl ch cl rh rl rr Fch Frh Hch Hrh.
assert (Hch' : bpow radix2 (-12) <= Rabs (B2R ch) <= 2)
  by (rewrite Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 (-12)); lra); lra).
unfold DyadicTrig.fast_eval. cbv zeta.
rewrite (two_prod_err_fma_eq ch rh Fch Frh (prod_exact_eval true ch rh Fch Frh Hch' Hrh)
  (prod_exact_eval false ch rh Fch Frh Hch' Hrh)).
reflexivity.
Qed.

Theorem fast_sin0_correct :
  forall x,
  is_finite x = true ->
  bpow radix2 (-27) <= Rabs (B2R x) <= PI / 8192 * (1 + bpow radix2 (-24)) ->
  let '(h, l) := DyadicTrig.fast_sin0 x in
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  Rabs (B2R h + B2R l - sin (B2R x)) <= bpow radix2 (-71) * Rabs (sin (B2R x)).
Proof.
intros x Fx Hx.
unfold DyadicTrig.fast_sin0, Fast.fast_two_sum. cbv beta iota zeta.
pose proof pi_M as [_ PM].
set (X := Rabs (B2R x)) in *.
assert (HX10 : X <= bpow radix2 (-10)) by (num; lra).
destruct (poly_s3 x X Fx (Rle_refl _) HX10) as [Fs3 Bs3]. cbv zeta in Fs3, Bs3.
set (s3 := mul (mul x (mul x x))
             (sub (mul (mul x x) (from_bits DyadicTrig.S5)) (from_bits DyadicTrig.S3))) in *.
set (P := B2R x) in *.
assert (X0 : 0 <= X) by apply Rabs_pos.
assert (Y : X * X <= 15e-8) by (num; nra).
assert (Y0 : 0 <= X * X) by nra.
assert (X3 : X ^ 3 <= 15e-8 * X) by (replace (X ^ 3) with (X * (X * X)) by ring; nra).
assert (Y3 : X * X * (X * X) * (X * X) <= 1e-20).
{ assert (X * X * (X * X) <= 15e-8 * 15e-8) by nra. nra. }
assert (X7 : X ^ 7 <= 1e-20 * X)
  by (replace (X ^ 7) with (X * (X * X * (X * X) * (X * X))) by ring; nra).
(* The Taylor polynomial of degree 5 of sin, within [|x|^7 / 5040]. *)
assert (HP1 : Rabs P <= 1) by (unfold X in *; num; lra).
destruct (sin_t5 P HP1) as (T & HT & Es).
assert (B7 : Rabs (T * (P ^ 7 / 5040)) <= X ^ 7 / 5040).
{ unfold Rdiv. rewrite Rabs_mult, Rabs_mult, <- RPow_abs. fold X.
  rewrite (Rabs_pos_eq T), (Rabs_pos_eq (/ 5040)) by lra.
  assert (0 <= X ^ 7) by (apply pow_le; exact X0). nra. }
assert (B3 : Rabs (P ^ 3 * (P ^ 2 / 120 - / 6)) <= X ^ 3 / 5).
{ rewrite Rabs_mult, <- RPow_abs. fold X.
  assert (Q : Rabs (P ^ 2 / 120 - / 6) <= / 5).
  { rewrite <- pow2_abs. fold X. apply Rabs_le. cbn [pow]. split; nra. }
  assert (0 <= X ^ 3) by (apply pow_le; exact X0). nra. }
apply Rabs_le_inv in Bs3, B7, B3.
(* [|sin x| >= 0.99 |x|]. *)
assert (Hs : 99 / 100 * X <= Rabs (sin P)).
{ pose proof (Rabs_triang_inv P (P - sin P)) as Ht.
  replace (P - (P - sin P)) with (sin P) in Ht by ring. fold X in Ht.
  assert (Rabs (P - sin P) <= X / 100) by (apply Rabs_le; rewrite Es; lra). lra. }
(* [x + s3] is a float sum within [16], and [|s3| <= |x|]. *)
assert (S16 : Rabs (P + B2R s3) <= 16).
{ apply Rabs_le. unfold X in *. apply Rabs_le_inv in HP1. num. lra. }
destruct (add_e x s3 Fx Fs3 S16) as (Fh & Eh & _).
assert (Hle : Rabs (B2R s3) <= Rabs P).
{ apply Rabs_le. fold X. num. lra. }
destruct (CancelLanes.fast_two_sum x s3 (add x s3) Fx Fs3 Hle Fh Eh) as (Fl & El).
fold P in El.
split; [exact Fh|]. split; [exact Fl|].
rewrite El. replace (B2R (add x s3) + (P + B2R s3 - B2R (add x s3))) with (P + B2R s3) by ring.
split; [exact Eh|].
apply Rabs_le. rewrite Es in Hs |- *. num. split; lra.
Qed.

Theorem fast_cos0_correct :
  forall x,
  is_finite x = true ->
  bpow radix2 (-27) <= Rabs (B2R x) <= PI / 8192 * (1 + bpow radix2 (-24)) ->
  let '(h, l) := DyadicTrig.fast_cos0 x in
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  Rabs (B2R h + B2R l - cos (B2R x)) <= bpow radix2 (-71) * cos (B2R x).
Proof.
intros x Fx Hx.
unfold DyadicTrig.fast_cos0, Fast.fast_two_sum. cbv beta iota zeta.
pose proof pi_M as [_ PM].
set (X := Rabs (B2R x)) in *.
assert (HX10 : X <= bpow radix2 (-10)) by (num; lra).
destruct (poly_cm x X Fx (Rle_refl _) HX10) as [Fcm Bcm]. cbv zeta in Fcm, Bcm.
set (cm := mul (mul x x) (sub (mul (mul x x) (from_bits DyadicTrig.C4)) half)) in *.
set (P := B2R x) in *.
assert (X0 : 0 <= X) by apply Rabs_pos.
assert (Y : X * X <= 15e-8) by (num; nra).
assert (Y0 : 0 <= X * X) by nra.
assert (X2 : X ^ 2 <= 15e-8) by (replace (X ^ 2) with (X * X) by ring; exact Y).
assert (Y3 : X * X * (X * X) * (X * X) <= 1e-20).
{ assert (X * X * (X * X) <= 15e-8 * 15e-8) by nra. nra. }
assert (X6 : X ^ 6 <= 1e-20)
  by (replace (X ^ 6) with (X * X * (X * X) * (X * X)) by ring; exact Y3).
(* The Taylor polynomial of degree 4 of cos, within [|x|^6 / 720]. *)
assert (HP1 : Rabs P <= 1) by (unfold X in *; num; lra).
destruct (cos_t4 P HP1) as (T & HT & Ec).
assert (B6 : Rabs (T * (P ^ 6 / 720)) <= X ^ 6 / 720).
{ unfold Rdiv. rewrite Rabs_mult, Rabs_mult, <- RPow_abs. fold X.
  rewrite (Rabs_pos_eq T), (Rabs_pos_eq (/ 720)) by lra.
  assert (0 <= X ^ 6) by (apply pow_le; exact X0). nra. }
assert (B4 : Rabs (P ^ 2 * (P ^ 2 / 24 - / 2)) <= X ^ 2 / 2).
{ rewrite <- pow2_abs. fold X. rewrite Rabs_mult, (Rabs_pos_eq (X ^ 2)) by (apply pow_le; lra).
  assert (Q : Rabs (X ^ 2 / 24 - / 2) <= / 2).
  { apply Rabs_le. assert (0 <= X ^ 2) by (apply pow_le; lra). split; lra. }
  assert (0 <= X ^ 2) by (apply pow_le; exact X0). nra. }
apply Rabs_le_inv in Bcm, B6, B4.
destruct one_F as (F1 & E1).
(* [1 + cm] is a float sum within [16], and [|cm| <= 1]. *)
assert (S16 : Rabs (B2R Fast.one + B2R cm) <= 16) by (apply Rabs_le; rewrite E1; num; lra).
destruct (add_e Fast.one cm F1 Fcm S16) as (Fh & Eh & _).
assert (Hle : Rabs (B2R cm) <= Rabs (B2R Fast.one))
  by (rewrite E1, Rabs_R1; apply Rabs_le; num; lra).
destruct (CancelLanes.fast_two_sum Fast.one cm (add Fast.one cm) F1 Fcm Hle Fh Eh)
  as (Fl & El).
split; [exact Fh|]. split; [exact Fl|].
rewrite El.
replace (B2R (add Fast.one cm) + (B2R Fast.one + B2R cm - B2R (add Fast.one cm)))
  with (B2R Fast.one + B2R cm) by ring.
split; [exact Eh|].
rewrite E1. apply Rabs_le. rewrite Ec. num. split; lra.
Qed.
