(** * Rounding errors and the exponential near 0, for the fast path of [exp]

    The bounds that [FastExpPoly.v], [FastExpTbl.v], [FastExpProd.v] and
    [FastExpCore.v] share: the error of one rounding to nearest
    ([rn_err]), the sums and products of two [f64]s that stay far below
    the overflow threshold ([add_e], [sub_e], [mul_e], and their forms
    [add_k], [sub_k], [mul_k] with a bound of the exact result), and the
    Taylor polynomial of degree 4 of [e^r] ([exp_taylor4]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Relative.
From Inari Require Import Model Encoding Elementary TwoSum TwoProduct ExpSeries.

Open Scope R_scope.

(** ** Roundings *)

(** Rounding to nearest moves [x] by at most [2^-53 |x| + 2^-1075]. *)
Lemma rn_err :
  forall x, Rabs (RN x - x) <= bpow radix2 (-53) * Rabs x + bpow radix2 (-1075).
Proof.
intros x.
pose proof (bpow_gt_0 radix2 (-1075)) as H0.
pose proof (Rabs_pos x) as Hx0.
destruct (Rle_or_lt (bpow radix2 (-1022)) (Rabs x)) as [Hx|Hx].
- assert (H : Rabs (RN x - x) <= / 2 * bpow radix2 (- 53 + 1) * Rabs x)
    by exact (relative_error_N_FLT radix2 (-1074) 53 eq_refl (fun z => negb (Z.even z)) x Hx).
  change (- 53 + 1)%Z with (-52)%Z in H.
  assert (E : / 2 * bpow radix2 (-52) = bpow radix2 (-53))
    by (cbn [bpow radix_val radix2]; lra).
  rewrite E in H. lra.
- assert (H : Rabs (RN x - x) <= / 2 * ulp radix2 fexp64 x)
    by (apply error_le_half_ulp; typeclasses eauto).
  rewrite (ulp_FLT_small radix2 (-1074) 53 x) in H
    by (eapply Rlt_le_trans; [exact Hx | apply bpow_le; lia]).
  assert (E : / 2 * bpow radix2 (-1074) = bpow radix2 (-1075))
    by (cbn [bpow radix_val radix2]; lra).
  rewrite E in H.
  assert (0 <= bpow radix2 (-53) * Rabs x) by (apply Rmult_le_pos; [apply bpow_ge_0 | lra]).
  lra.
Qed.

Lemma small_le_max : forall z, Rabs z <= 16 -> Rabs z <= MAX.
Proof. intros z H. cbn [bpow radix_val radix2]. lra. Qed.

(** [x + y], [x - y] and [x * y] of finite [f64]s with an exact result of
    at most 16 in magnitude: finite, rounded to nearest, and within
    [2^-53] of the exact result relatively, plus [2^-1075]. *)
Lemma add_e :
  forall x y, is_finite x = true -> is_finite y = true -> Rabs (B2R x + B2R y) <= 16 ->
  is_finite (add x y) = true /\ B2R (add x y) = RN (B2R x + B2R y) /\
  Rabs (B2R (add x y) - (B2R x + B2R y)) <=
    bpow radix2 (-53) * Rabs (B2R x + B2R y) + bpow radix2 (-1075).
Proof.
intros x y Fx Fy H.
destruct (add_below_max x y Fx Fy (small_le_max _ H)) as (F & E & _).
split; [exact F | split; [exact E |]]. rewrite E. apply rn_err.
Qed.

Lemma sub_e :
  forall x y, is_finite x = true -> is_finite y = true -> Rabs (B2R x - B2R y) <= 16 ->
  is_finite (sub x y) = true /\ B2R (sub x y) = RN (B2R x - B2R y) /\
  Rabs (B2R (sub x y) - (B2R x - B2R y)) <=
    bpow radix2 (-53) * Rabs (B2R x - B2R y) + bpow radix2 (-1075).
Proof.
intros x y Fx Fy H.
destruct (sub_below_max x y Fx Fy (small_le_max _ H)) as (F & E & _).
split; [exact F | split; [exact E |]]. rewrite E. apply rn_err.
Qed.

Lemma mul_e :
  forall x y, is_finite x = true -> is_finite y = true -> Rabs (B2R x * B2R y) <= 16 ->
  is_finite (mul x y) = true /\ B2R (mul x y) = RN (B2R x * B2R y) /\
  Rabs (B2R (mul x y) - B2R x * B2R y) <=
    bpow radix2 (-53) * Rabs (B2R x * B2R y) + bpow radix2 (-1075).
Proof.
intros x y Fx Fy H.
destruct (mul_below_max x y Fx Fy (small_le_max _ H)) as (F & E & _).
split; [exact F | split; [exact E |]]. rewrite E. apply rn_err.
Qed.

Lemma Rabs_mul_le :
  forall x y X Y, Rabs x <= X -> Rabs y <= Y -> Rabs (x * y) <= X * Y.
Proof.
intros x y X Y Hx Hy. rewrite Rabs_mult.
apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hx | exact Hy].
Qed.

(** ** The exponential near 0 *)

Lemma exp_le : forall x y, x <= y -> exp x <= exp y.
Proof.
intros x y [H | ->]; [apply Rlt_le, exp_increasing; exact H | apply Rle_refl].
Qed.

(** [e^-y <= 1 - y/2] for [0 <= y <= 1] ([exp_alt_bounds]). *)
Lemma exp_neg_le : forall y, 0 <= y <= 1 -> exp (- y) <= 1 - y / 2.
Proof.
intros y Hy.
destruct (exp_alt_bounds y 1 Hy) as [_ Hu].
replace (sum_f_R0 (tg_alt (exp_tg y)) (2 * 1)) with (1 - y + y^2/2) in Hu
  by (unfold tg_alt, exp_tg; cbn; field).
assert (y ^ 2 <= y) by (cbn; nra).
lra.
Qed.

(** The Taylor polynomial of degree 4 of [e^r] is within [|r|^5 / 100]
    for [|r| <= 1/1024]: below 0 by [exp_alt_bounds], and above 0 because
    [e^r] is at least that sum of positive terms and [e^r = 1 / e^-r]
    with [e^-r] at least the alternating sum of degree 5. *)
Lemma exp_taylor4 :
  forall r, Rabs r <= / 1024 ->
  Rabs (exp r - (1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24)) <= Rabs r ^ 5 / 100.
Proof.
intros r Hr.
destruct (Rle_or_lt 0 r) as [Hp|Hn].
- rewrite (Rabs_pos_eq r) in Hr |- * by exact Hp.
  assert (Hr1 : 0 <= r <= 1) by lra.
  set (e := exp r). set (f := exp (- r)).
  assert (Hef : e * f = 1) by (unfold e, f; rewrite <- exp_plus, Rplus_opp_r; exact exp_0).
  assert (He0 : 0 < e) by apply exp_pos.
  destruct (exp_alt_bounds r 2 Hr1) as [Hfl _]. fold f in Hfl.
  replace (sum_f_R0 (tg_alt (exp_tg r)) (S (2 * 2)))
    with (1 - r + r^2/2 - r^3/6 + r^4/24 - r^5/120) in Hfl
    by (unfold tg_alt, exp_tg; cbn; field).
  assert (Hel : sum_f_R0 (fun i => / INR (fact i) * r ^ i) 4 <= e).
  { apply sum_incr.
    - exact (proj2_sig (exist_exp r)).
    - intros n. apply Rmult_le_pos;
        [left; apply Rinv_0_lt_compat, INR_fact_lt_0 | apply pow_le; lra]. }
  replace (sum_f_R0 (fun i => / INR (fact i) * r ^ i) 4)
    with (1 + r + r^2/2 + r^3/6 + r^4/24) in Hel by (cbn; field).
  assert (H2 : 0 <= r ^ 2 <= r) by (cbn; nra).
  assert (H3 : 0 <= r ^ 3 <= r) by (cbn; nra).
  assert (H4 : 0 <= r ^ 4 <= r) by (cbn; nra).
  assert (H5 : 0 <= r ^ 5 <= r) by (cbn; nra).
  (* [(P4(r) + r^5/100) P5(-r) - 1 = r^5 G] with [G >= 0]. *)
  set (G := r / 72 + r ^ 3 / 576 - (1 + r + r^2/2 + r^3/6 + r^4/24) / 120
            + (1 - r + r^2/2 - r^3/6 + r^4/24 - r^5/120) / 100).
  assert (HG : 0 <= G) by (unfold G; lra).
  assert (Hid : (1 + r + r^2/2 + r^3/6 + r^4/24 + r^5/100)
                * (1 - r + r^2/2 - r^3/6 + r^4/24 - r^5/120) - 1 = r ^ 5 * G)
    by (unfold G; field).
  assert (Hpos : 0 <= r ^ 5 * G) by (apply Rmult_le_pos; lra).
  set (L := 1 - r + r^2/2 - r^3/6 + r^4/24 - r^5/120) in *.
  assert (HL : 0 < L) by (unfold L; lra).
  (* [e L <= e f = 1 <= (P4 + r^5/100) L]. *)
  assert (Hu : e * L <= (1 + r + r^2/2 + r^3/6 + r^4/24 + r^5/100) * L).
  { apply Rle_trans with 1; [|lra].
    rewrite <- Hef. apply Rmult_le_compat_l; lra. }
  apply Rmult_le_reg_r in Hu; [|exact HL].
  rewrite Rabs_pos_eq by lra. lra.
- set (x := - r).
  assert (Hx : 0 <= x <= 1) by (unfold x; rewrite Rabs_left in Hr by exact Hn; lra).
  rewrite (Rabs_left r) by exact Hn. fold x.
  replace r with (- x) by (unfold x; ring).
  destruct (exp_alt_bounds x 2 Hx) as [Hl Hu].
  replace (sum_f_R0 (tg_alt (exp_tg x)) (S (2 * 2)))
    with (1 - x + x^2/2 - x^3/6 + x^4/24 - x^5/120) in Hl
    by (unfold tg_alt, exp_tg; cbn; field).
  replace (sum_f_R0 (tg_alt (exp_tg x)) (2 * 2))
    with (1 - x + x^2/2 - x^3/6 + x^4/24) in Hu
    by (unfold tg_alt, exp_tg; cbn; field).
  assert (H5 : 0 <= x ^ 5) by (apply pow_le; lra).
  replace (1 + - x + (- x) ^ 2 / 2 + (- x) ^ 3 / 6 + (- x) ^ 4 / 24)
    with (1 - x + x^2/2 - x^3/6 + x^4/24) by field.
  apply Rabs_le. lra.
Qed.

(** ** With a bound of the exact result *)

(** [add_e], [sub_e] and [mul_e] with the exact result bounded by [K]. *)
Lemma add_k :
  forall x y K, is_finite x = true -> is_finite y = true ->
  Rabs (B2R x + B2R y) <= K -> K <= 16 ->
  is_finite (add x y) = true /\ B2R (add x y) = RN (B2R x + B2R y) /\
  Rabs (B2R (add x y) - (B2R x + B2R y)) <= bpow radix2 (-53) * K + bpow radix2 (-1075).
Proof.
intros x y K Fx Fy H HK.
destruct (add_e x y Fx Fy ltac:(lra)) as (F & E & B).
split; [exact F | split; [exact E |]].
eapply Rle_trans; [exact B |].
apply Rplus_le_compat_r, Rmult_le_compat_l; [apply bpow_ge_0 | exact H].
Qed.

Lemma sub_k :
  forall x y K, is_finite x = true -> is_finite y = true ->
  Rabs (B2R x - B2R y) <= K -> K <= 16 ->
  is_finite (sub x y) = true /\ B2R (sub x y) = RN (B2R x - B2R y) /\
  Rabs (B2R (sub x y) - (B2R x - B2R y)) <= bpow radix2 (-53) * K + bpow radix2 (-1075).
Proof.
intros x y K Fx Fy H HK.
destruct (sub_e x y Fx Fy ltac:(lra)) as (F & E & B).
split; [exact F | split; [exact E |]].
eapply Rle_trans; [exact B |].
apply Rplus_le_compat_r, Rmult_le_compat_l; [apply bpow_ge_0 | exact H].
Qed.

Lemma mul_k :
  forall x y K, is_finite x = true -> is_finite y = true ->
  Rabs (B2R x * B2R y) <= K -> K <= 16 ->
  is_finite (mul x y) = true /\ B2R (mul x y) = RN (B2R x * B2R y) /\
  Rabs (B2R (mul x y) - B2R x * B2R y) <= bpow radix2 (-53) * K + bpow radix2 (-1075).
Proof.
intros x y K Fx Fy H HK.
destruct (mul_e x y Fx Fy ltac:(lra)) as (F & E & B).
split; [exact F | split; [exact E |]].
eapply Rle_trans; [exact B |].
apply Rplus_le_compat_r, Rmult_le_compat_l; [apply bpow_ge_0 | exact H].
Qed.
