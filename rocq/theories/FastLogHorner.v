(** * The terms of degree 3 to 8 of the fast path of the logarithms

    [DyadicLog.log1p_poly] of [Model.v] computes the terms of degree 3
    to 8 of the Taylor polynomial of ln(1 + z) at [z1] as [q], the
    product of [z1^3] and [log1p_tail z1] by Horner's scheme, all in
    [f64]. [log1p_horner z1] is that [q], and [log1p_horner_correct]
    bounds its error for [|z1| <= 2^-9], relative to [|z1|^3].

    With [u = 2^-53]: each inner step of Horner's scheme is within
    [2^-54] of its exact value; the last one, [v1 = Q3 + m1] rounded,
    is within half an ulp, [2^-55], since [Q3 + m1] is below [1/2]; with
    [Q3 = 1/3 - u/6] that puts [v1] within [0.4182 u] of [log1p_tail
    z1], and [|v1| <= 0.334]. [c = z1 RN(z1^2)] is within [(2 + u) u
    |z1|^3] of [z1^3], and [q = RN(c v1)]: with [|c| <= (1 + u)^2
    |z1|^3], [q] is within [0.334 ((1 + u)^2 + 2 + u) u |z1|^3 + 0.4182
    u |z1|^3 <= 1.421 u |z1|^3] of [z1^3 log1p_tail z1], plus the terms
    [2^-1075] of the roundings near the underflow threshold, fewer than
    four of them in all. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding TwoSum FastExpErr.

Open Scope R_scope.

(** The terms of degree 3 to 8 of the Taylor polynomial of ln(1 + z),
    divided by [z^3]: 1/3 - z/4 + z^2/5 - z^3/6 + z^4/7 - z^5/8. *)
Definition log1p_tail (z : R) : R :=
  / 3 + z * (- / 4 + z * (/ 5 + z * (- / 6 + z * (/ 7 + z * (- / 8))))).

(** [q] of [DyadicLog.log1p_poly]. *)
Definition log1p_horner (z1 : f64) : f64 :=
  mul (mul z1 (mul z1 z1))
    (add (from_bits DyadicLog.Q3)
       (mul z1 (add DyadicLog.neg_quarter
          (mul z1 (add (from_bits DyadicLog.Q5)
             (mul z1 (add (from_bits DyadicLog.Q6)
                (mul z1 (add (from_bits DyadicLog.Q7) (mul z1 DyadicLog.neg_eighth)))))))))).

(** [B2R l] of an [f64] literal [l], as [m * 2^e] (as in [FastExp.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** Powers of 2 as numerals, for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp] in *.

(** [add_k] and [mul_k] of [FastExpErr.v] for a named result [z], with
    the error as two inequalities for [lra] (as in [FastExpPoly.v]). *)
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

(** [mul_e] of [FastExpErr.v] for a named result [z]: the error is
    relative to [|x y|]. *)
Local Lemma mul_ez :
  forall x y z, z = mul x y -> is_finite x = true -> is_finite y = true ->
  Rabs (B2R x * B2R y) <= 16 ->
  is_finite z = true /\
  Rabs (B2R z - B2R x * B2R y) <=
    bpow radix2 (-53) * Rabs (B2R x * B2R y) + bpow radix2 (-1075).
Proof.
intros x y z -> Fx Fy H.
destruct (mul_e x y Fx Fy H) as (F & _ & B).
split; assumption.
Qed.

(** [x + y] of finite [f64]s, named [z], is [x + y] rounded to nearest. *)
Local Lemma add_rn :
  forall x y z, z = add x y -> is_finite x = true -> is_finite y = true ->
  Rabs (B2R x + B2R y) <= 16 ->
  is_finite z = true /\ B2R z = RN (B2R x + B2R y).
Proof.
intros x y z -> Fx Fy H.
destruct (add_e x y Fx Fy H) as (F & E & _).
split; assumption.
Qed.

(** Below [1/2], the ulp is at most [2^-54], so rounding to nearest moves
    [x] by at most [2^-55]. *)
Local Lemma rn_half :
  forall x, Rabs x < bpow radix2 (-1) -> Rabs (RN x - x) <= bpow radix2 (-55).
Proof.
intros x Hx.
destruct (Req_dec x 0) as [->|Hx0].
- rewrite round_0 by typeclasses eauto. rewrite Rminus_0_r, Rabs_R0. apply bpow_ge_0.
- assert (H : Rabs (RN x - x) <= / 2 * ulp radix2 fexp64 x)
    by (apply error_le_half_ulp; typeclasses eauto).
  assert (Hm : (mag radix2 x <= -1)%Z) by (apply mag_le_bpow; assumption).
  assert (Hu : ulp radix2 fexp64 x <= bpow radix2 (-54)).
  { rewrite ulp_neq_0 by exact Hx0. unfold cexp. apply bpow_le. unfold FLT_exp. lia. }
  assert (E : / 2 * bpow radix2 (-54) = bpow radix2 (-55))
    by (cbn [bpow radix_val radix2]; lra).
  lra.
Qed.

(** For [|z1| <= 2^-9], [q] is within [1.421 2^-53 |z1|^3 + 2^-1073] of
    [z1^3 log1p_tail z1]. *)
Theorem log1p_horner_correct :
  forall z1, is_finite z1 = true -> Rabs (B2R z1) <= bpow radix2 (-9) ->
  is_finite (log1p_horner z1) = true /\
  Rabs (B2R (log1p_horner z1) - B2R z1 ^ 3 * log1p_tail (B2R z1)) <=
    1421 / 1000 * bpow radix2 (-53) * Rabs (B2R z1) ^ 3 + bpow radix2 (-1073).
Proof.
intros z1 F Hz.
pose proof (Rabs_le_inv _ _ Hz) as Hz2.
pose proof (Rabs_pos (B2R z1)) as HZ0.
(* The constants: [Q3 = 1/3 - 2^-54/3], [Q5 = 1/5 + 2^-54/5],
   [Q6 = -1/6 + 2^-55/3], [Q7 = 1/7 - 2^-54/7], and -1/4 and -1/8
   exactly. *)
assert (F3 : is_finite (from_bits DyadicLog.Q3) = true) by (vm_compute; reflexivity).
assert (F5 : is_finite (from_bits DyadicLog.Q5) = true) by (vm_compute; reflexivity).
assert (F6 : is_finite (from_bits DyadicLog.Q6) = true) by (vm_compute; reflexivity).
assert (F7 : is_finite (from_bits DyadicLog.Q7) = true) by (vm_compute; reflexivity).
assert (Fq : is_finite DyadicLog.neg_quarter = true) by (vm_compute; reflexivity).
assert (Fe : is_finite DyadicLog.neg_eighth = true) by (vm_compute; reflexivity).
assert (E3 : B2R (from_bits DyadicLog.Q3) = / 3 - bpow radix2 (-54) / 3)
  by (lit_B2R; num; lra).
assert (E5 : B2R (from_bits DyadicLog.Q5) = / 5 + bpow radix2 (-54) / 5)
  by (lit_B2R; num; lra).
assert (E6 : B2R (from_bits DyadicLog.Q6) = - / 6 + bpow radix2 (-55) / 3)
  by (lit_B2R; num; lra).
assert (E7 : B2R (from_bits DyadicLog.Q7) = / 7 - bpow radix2 (-54) / 7)
  by (lit_B2R; num; lra).
assert (Eq : B2R DyadicLog.neg_quarter = - / 4) by (lit_B2R; num; lra).
assert (Ee : B2R DyadicLog.neg_eighth = - / 8) by (lit_B2R; num; lra).
(* The exact values of Horner's scheme: [T = log1p_tail z1 = 1/3 + z1 R2],
   [R2 = -1/4 + z1 R3], and so on. *)
pose (R5 := / 7 + B2R z1 * (- / 8)).
pose (R4 := - / 6 + B2R z1 * R5).
pose (R3 := / 5 + B2R z1 * R4).
pose (R2 := - / 4 + B2R z1 * R3).
pose (T := / 3 + B2R z1 * R2).
assert (ET : log1p_tail (B2R z1) = T) by reflexivity.
assert (ER5 : R5 = / 7 + B2R z1 * (- / 8)) by reflexivity.
assert (ER4 : R4 = - / 6 + B2R z1 * R5) by reflexivity.
assert (ER3 : R3 = / 5 + B2R z1 * R4) by reflexivity.
assert (ER2 : R2 = - / 4 + B2R z1 * R3) by reflexivity.
assert (ERT : T = / 3 + B2R z1 * R2) by reflexivity.
clearbody T R2 R3 R4 R5.
rewrite ET.
unfold log1p_horner.
set (m5 := mul z1 DyadicLog.neg_eighth).
set (v5 := add (from_bits DyadicLog.Q7) m5).
set (m4 := mul z1 v5).
set (v4 := add (from_bits DyadicLog.Q6) m4).
set (m3 := mul z1 v4).
set (v3 := add (from_bits DyadicLog.Q5) m3).
set (m2 := mul z1 v3).
set (v2 := add DyadicLog.neg_quarter m2).
set (m1 := mul z1 v2).
set (v1 := add (from_bits DyadicLog.Q3) m1).
set (sh := mul z1 z1).
set (c := mul z1 sh).
set (q := mul c v1).
(* [m5 = -z1/8] rounded. *)
assert (Hm5 : Rabs (B2R z1 * B2R DyadicLog.neg_eighth) <= bpow radix2 (-12))
  by (rewrite Ee; apply Rabs_le; num; lra).
destruct (mul_kz z1 _ m5 _ eq_refl F Fe Hm5 ltac:(num; lra)) as (Fm5 & B5).
rewrite Ee in B5.
(* [v5 = Q7 + m5] rounded is [R5] within [2^-54]. *)
assert (Hs5 : Rabs (B2R (from_bits DyadicLog.Q7) + B2R m5) <= 3 / 20)
  by (rewrite E7; apply Rabs_le; num; lra).
destruct (add_kz _ _ v5 _ eq_refl F7 Fm5 Hs5 ltac:(lra)) as (Fv5 & A5).
rewrite E7 in A5.
assert (C5 : - bpow radix2 (-54) <= B2R v5 - R5 <= bpow radix2 (-54)) by (num; lra).
assert (W5 : Rabs (B2R v5) <= 3 / 20) by (apply Rabs_le; num; lra).
(* [m4 = z1 v5] rounded, and [v4 = Q6 + m4] rounded is [R4] within [2^-54]. *)
assert (Hm4 : Rabs (B2R z1 * B2R v5) <= bpow radix2 (-9) * (3 / 20))
  by (apply Rabs_mul_le; assumption).
destruct (mul_kz z1 v5 m4 _ eq_refl F Fv5 Hm4 ltac:(num; lra)) as (Fm4 & B4).
assert (D4 : Rabs (B2R z1 * (B2R v5 - R5)) <= bpow radix2 (-9) * bpow radix2 (-54))
  by (apply Rabs_mul_le; [exact Hz | apply Rabs_le; exact C5]).
rewrite Rmult_minus_distr_l in D4. apply Rabs_le_inv in D4, Hm4.
assert (Hs4 : Rabs (B2R (from_bits DyadicLog.Q6) + B2R m4) <= 17 / 100)
  by (rewrite E6; apply Rabs_le; num; lra).
destruct (add_kz _ _ v4 _ eq_refl F6 Fm4 Hs4 ltac:(lra)) as (Fv4 & A4).
rewrite E6 in A4.
assert (C4 : - bpow radix2 (-54) <= B2R v4 - R4 <= bpow radix2 (-54)) by (num; lra).
assert (W4 : Rabs (B2R v4) <= 17 / 100) by (apply Rabs_le; num; lra).
(* [m3 = z1 v4] rounded, and [v3 = Q5 + m3] rounded is [R3] within [2^-54]. *)
assert (Hm3 : Rabs (B2R z1 * B2R v4) <= bpow radix2 (-9) * (17 / 100))
  by (apply Rabs_mul_le; assumption).
destruct (mul_kz z1 v4 m3 _ eq_refl F Fv4 Hm3 ltac:(num; lra)) as (Fm3 & B3).
assert (D3 : Rabs (B2R z1 * (B2R v4 - R4)) <= bpow radix2 (-9) * bpow radix2 (-54))
  by (apply Rabs_mul_le; [exact Hz | apply Rabs_le; exact C4]).
rewrite Rmult_minus_distr_l in D3. apply Rabs_le_inv in D3, Hm3.
assert (Hs3 : Rabs (B2R (from_bits DyadicLog.Q5) + B2R m3) <= 21 / 100)
  by (rewrite E5; apply Rabs_le; num; lra).
destruct (add_kz _ _ v3 _ eq_refl F5 Fm3 Hs3 ltac:(lra)) as (Fv3 & A3).
rewrite E5 in A3.
assert (C3 : - bpow radix2 (-54) <= B2R v3 - R3 <= bpow radix2 (-54)) by (num; lra).
assert (W3 : Rabs (B2R v3) <= 21 / 100) by (apply Rabs_le; num; lra).
(* [m2 = z1 v3] rounded, and [v2 = -1/4 + m2] rounded is [R2] within [2^-54]. *)
assert (Hm2 : Rabs (B2R z1 * B2R v3) <= bpow radix2 (-9) * (21 / 100))
  by (apply Rabs_mul_le; assumption).
destruct (mul_kz z1 v3 m2 _ eq_refl F Fv3 Hm2 ltac:(num; lra)) as (Fm2 & B2).
assert (D2 : Rabs (B2R z1 * (B2R v3 - R3)) <= bpow radix2 (-9) * bpow radix2 (-54))
  by (apply Rabs_mul_le; [exact Hz | apply Rabs_le; exact C3]).
rewrite Rmult_minus_distr_l in D2. apply Rabs_le_inv in D2, Hm2.
assert (Hs2 : Rabs (B2R DyadicLog.neg_quarter + B2R m2) <= 26 / 100)
  by (rewrite Eq; apply Rabs_le; num; lra).
destruct (add_kz _ _ v2 _ eq_refl Fq Fm2 Hs2 ltac:(lra)) as (Fv2 & A2).
rewrite Eq in A2.
assert (C2 : - bpow radix2 (-54) <= B2R v2 - R2 <= bpow radix2 (-54)) by (num; lra).
assert (W2 : Rabs (B2R v2) <= 26 / 100) by (apply Rabs_le; num; lra).
(* [m1 = z1 v2] rounded, and [v1 = Q3 + m1] rounded to nearest: [Q3 + m1]
   is below [1/2], so [v1] moves by half an ulp, [2^-55], at most. With
   [Q3 = 1/3 - u/6], [v1] is [T] within [0.4182 u]. *)
assert (Hm1 : Rabs (B2R z1 * B2R v2) <= bpow radix2 (-9) * (26 / 100))
  by (apply Rabs_mul_le; assumption).
destruct (mul_kz z1 v2 m1 _ eq_refl F Fv2 Hm1 ltac:(num; lra)) as (Fm1 & B1).
assert (D1 : Rabs (B2R z1 * (B2R v2 - R2)) <= bpow radix2 (-9) * bpow radix2 (-54))
  by (apply Rabs_mul_le; [exact Hz | apply Rabs_le; exact C2]).
rewrite Rmult_minus_distr_l in D1. apply Rabs_le_inv in D1, Hm1.
assert (Hs1 : Rabs (B2R (from_bits DyadicLog.Q3) + B2R m1) < bpow radix2 (-1))
  by (rewrite E3; apply Rabs_lt; num; lra).
destruct (add_rn _ _ v1 eq_refl F3 Fm1 ltac:(num; lra)) as (Fv1 & Ev1).
pose proof (rn_half _ Hs1) as A1. rewrite <- Ev1, E3 in A1. apply Rabs_le_inv in A1.
assert (C1 : - (4182 / 10000 * bpow radix2 (-53)) <= B2R v1 - T <=
             4182 / 10000 * bpow radix2 (-53))
  by (num; lra).
assert (W1 : Rabs (B2R v1) <= 334 / 1000) by (apply Rabs_le; num; lra).
(* [sh = z1^2] rounded and [c = z1 sh] rounded: [c] is [z1^3] within
   [(2 + u) u |z1|^3 + 2 * 2^-1075]. *)
assert (HZ2 : Rabs (B2R z1 * B2R z1) = Rabs (B2R z1) * Rabs (B2R z1)) by apply Rabs_mult.
assert (HZ3 : Rabs (B2R z1 * (B2R z1 * B2R z1)) = Rabs (B2R z1) ^ 3)
  by (rewrite !Rabs_mult; ring).
assert (HZ3p : 0 <= Rabs (B2R z1) ^ 3) by (apply pow_le; exact HZ0).
assert (HZZ : Rabs (B2R z1) * Rabs (B2R z1) <= bpow radix2 (-9) * bpow radix2 (-9))
  by (apply Rmult_le_compat; assumption).
assert (HZ3u : Rabs (B2R z1) ^ 3 <= bpow radix2 (-9) * (bpow radix2 (-9) * bpow radix2 (-9)))
  by (rewrite <- HZ3; apply Rabs_mul_le; [exact Hz | rewrite HZ2; exact HZZ]).
destruct (mul_ez z1 z1 sh eq_refl F F ltac:(rewrite HZ2; num; lra)) as (Fsh & Bsh).
rewrite HZ2 in Bsh. apply Rabs_le_inv in Bsh.
assert (Hzz : - (Rabs (B2R z1) * Rabs (B2R z1)) <= B2R z1 * B2R z1 <=
              Rabs (B2R z1) * Rabs (B2R z1))
  by (rewrite <- HZ2; apply Rabs_le_inv, Rle_refl).
assert (Wsh : Rabs (B2R sh) <=
              (1 + bpow radix2 (-53)) * (Rabs (B2R z1) * Rabs (B2R z1)) + bpow radix2 (-1075))
  by (apply Rabs_le; num; lra).
assert (Wsh1 : Rabs (B2R sh) <= 1) by (num; lra).
assert (Hzs : Rabs (B2R z1 * B2R sh) <= bpow radix2 (-9) * 1)
  by (apply Rabs_mul_le; assumption).
pose proof (Rabs_le_inv _ _ Hzs) as Hzs1.
destruct (mul_ez z1 sh c eq_refl F Fsh ltac:(num; lra)) as (Fc & Bc).
assert (Hzs2 : Rabs (B2R z1 * B2R sh) <= Rabs (B2R z1) *
         ((1 + bpow radix2 (-53)) * (Rabs (B2R z1) * Rabs (B2R z1)) + bpow radix2 (-1075)))
  by (apply Rabs_mul_le; [apply Rle_refl | exact Wsh]).
assert (Dsh : Rabs (B2R z1 * (B2R sh - B2R z1 * B2R z1)) <=
              Rabs (B2R z1) * (bpow radix2 (-53) * (Rabs (B2R z1) * Rabs (B2R z1))
                               + bpow radix2 (-1075)))
  by (apply Rabs_mul_le; [apply Rle_refl | apply Rabs_le; exact Bsh]).
rewrite Rmult_minus_distr_l in Dsh.
apply Rabs_le_inv in Bc, Dsh.
assert (Cc : Rabs (B2R c - B2R z1 * (B2R z1 * B2R z1)) <=
             bpow radix2 (-53) * (2 + bpow radix2 (-53)) * Rabs (B2R z1) ^ 3
             + 2 * bpow radix2 (-1075))
  by (apply Rabs_le; num; lra).
pose proof (Rabs_le_inv _ _ Cc) as Cc2.
assert (Hzzz : - Rabs (B2R z1) ^ 3 <= B2R z1 * (B2R z1 * B2R z1) <= Rabs (B2R z1) ^ 3)
  by (rewrite <- HZ3; apply Rabs_le_inv, Rle_refl).
assert (Wc : Rabs (B2R c) <=
             (1 + bpow radix2 (-53)) ^ 2 * Rabs (B2R z1) ^ 3 + 2 * bpow radix2 (-1075))
  by (apply Rabs_le; num; lra).
assert (Wc1 : Rabs (B2R c) <= 1) by (num; lra).
(* [q = c v1] rounded is [z1^3 T] within [1.421 u |z1|^3 + 2^-1073]. *)
assert (Hcv : Rabs (B2R c * B2R v1) <=
              ((1 + bpow radix2 (-53)) ^ 2 * Rabs (B2R z1) ^ 3 + 2 * bpow radix2 (-1075))
              * (334 / 1000))
  by (apply Rabs_mul_le; assumption).
assert (Hcv1 : Rabs (B2R c * B2R v1) <= 1 * (334 / 1000)) by (apply Rabs_mul_le; assumption).
destruct (mul_ez c v1 q eq_refl Fc Fv1 ltac:(lra)) as (Fqq & Bq).
split; [exact Fqq|].
assert (Dv : Rabs ((B2R c - B2R z1 * (B2R z1 * B2R z1)) * B2R v1) <=
             (bpow radix2 (-53) * (2 + bpow radix2 (-53)) * Rabs (B2R z1) ^ 3
              + 2 * bpow radix2 (-1075)) * (334 / 1000))
  by (apply Rabs_mul_le; assumption).
assert (Dt : Rabs (B2R z1 * (B2R z1 * B2R z1) * (B2R v1 - T)) <=
             Rabs (B2R z1) ^ 3 * (4182 / 10000 * bpow radix2 (-53)))
  by (apply Rabs_mul_le; [rewrite HZ3; apply Rle_refl | apply Rabs_le; exact C1]).
rewrite Rmult_minus_distr_r in Dv. rewrite Rmult_minus_distr_l in Dt.
apply Rabs_le_inv in Bq, Dv, Dt.
replace (B2R z1 ^ 3) with (B2R z1 * (B2R z1 * B2R z1)) by ring.
apply Rabs_le. num. lra.
Qed.
