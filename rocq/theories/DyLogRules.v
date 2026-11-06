(** * Real identities and rules before Ziv's strategy for the dyadic logarithms

    The functions of [DyadicLog] in [Model.v] compute [ln] of a positive
    number from [2 atanh((m - 1) / (m + 1))] for its mantissa [m], and
    [asinh], [acosh] and [atanh] from [atanh] or [ln] of an expression in
    their argument. This file proves those identities for the reals, the
    scaled remainders of the series of [atanh] that the Horner scheme of
    [series_loop] evaluates, and the rules for the exact powers of 10 of
    [log10_dir] and for the special values of [log_rules]. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Decompose Elementary LogReal AtanhSeries MpfrRound DyExpRules
  DyExp.

Open Scope R_scope.

Local Notation rnd_of up := (if up then RNDU else RNDD).

(** ** The series of atanh

    [T * x^(2k+1) = Ratanh x - atanh_sum k x]: [T] is the remainder of
    the series after [k] terms, scaled by [x^(2k+1)]. For [0 <= x <= 1/2]
    such a [T] exists in [[0, 2]] ([atanh_sum_bounds] gives at most
    [1 / (1 - x^2) <= 4/3]; for [x = 0] any [T] will do), and a step of
    Horner's scheme from [T] for [k + 1] gives one for [k]. *)
Lemma atanh_tail :
  forall n x, 0 <= x <= 1 / 2 ->
  exists T, 0 <= T <= 2 /\ T * x ^ (2 * n + 1) = Ratanh x - atanh_sum n x.
Proof.
intros n x Hx.
destruct (atanh_sum_bounds n x ltac:(lra)) as [B1 B2].
destruct (Req_dec x 0) as [-> | Hx0].
- (* At 0 the remainder is 0. *)
  exists 0. rewrite !pow_i in B2 by lia. unfold Rdiv in B2. rewrite Rmult_0_l in B2.
  split; [lra |]. rewrite Rmult_0_l. lra.
- set (p := x ^ (2 * n + 1)) in *.
  assert (Hp : 0 < p) by (apply pow_lt; lra).
  (* [1 / (1 - x^2) <= 2], as [x^2 <= 1/4]. *)
  assert (D : Ratanh x - atanh_sum n x <= 2 * p).
  { apply Rle_trans with (1 := B2).
    assert (Hq : 3 / 4 <= 1 - x ^ 2) by nra.
    apply (Rmult_le_reg_r (1 - x ^ 2)); [lra |].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
    assert (0 <= p * (1 - 2 * x ^ 2)) by (apply Rmult_le_pos; nra).
    lra. }
  exists ((Ratanh x - atanh_sum n x) / p).
  split; [split |].
  + unfold Rdiv. apply Rmult_le_pos; [lra |]. apply Rlt_le, Rinv_0_lt_compat. exact Hp.
  + apply (Rmult_le_reg_r p); [exact Hp |].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. lra.
  + field. lra.
Qed.

Lemma atanh_horner :
  forall k x T,
  T * x ^ (2 * S k + 1) = Ratanh x - atanh_sum (S k) x ->
  (1 / IZR (2 * Z.of_nat k + 1) + x * x * T) * x ^ (2 * k + 1) = Ratanh x - atanh_sum k x.
Proof.
intros k x T H. cbn [atanh_sum] in H.
replace (2 * S k + 1)%nat with (2 * k + 1 + 2)%nat in H by lia.
rewrite pow_add in H.
rewrite INR_IZR_INZ in H.
replace (Z.of_nat (2 * k + 1)) with (2 * Z.of_nat k + 1)%Z in H by lia.
assert (Hz : IZR (2 * Z.of_nat k + 1) <> 0) by (apply not_0_IZR; lia).
set (p := x ^ (2 * k + 1)) in *. set (z := IZR (2 * Z.of_nat k + 1)) in *.
assert (E : Ratanh x - atanh_sum k x = T * (p * x ^ 2) + p / z) by lra.
rewrite E. field. exact Hz.
Qed.

(** ** Identities *)

(** [m = (1 + s) / (1 - s)] for [s = (m - 1) / (m + 1)]. *)
Lemma ln_atanh : forall m, 0 < m -> ln m = 2 * Ratanh ((m - 1) / (m + 1)).
Proof.
intros m Hm. unfold Ratanh.
replace ((1 + (m - 1) / (m + 1)) / (1 - (m - 1) / (m + 1))) with m
  by (field; repeat split; lra).
field.
Qed.

Lemma ln_atanh_inv : forall m, 0 < m -> - ln m = 2 * Ratanh ((1 - m) / (m + 1)).
Proof.
intros m Hm. unfold Ratanh.
replace ((1 + (1 - m) / (m + 1)) / (1 - (1 - m) / (m + 1))) with (/ m)
  by (field; repeat split; lra).
rewrite ln_Rinv by exact Hm. field.
Qed.

Lemma Ratanh_odd : forall x, -1 < x < 1 -> Ratanh (- x) = - Ratanh x.
Proof.
intros x Hx. unfold Ratanh.
replace ((1 + - x) / (1 - - x)) with (/ ((1 + x) / (1 - x))) by (field; repeat split; lra).
rewrite ln_Rinv by (apply atanh_arg_pos; exact Hx). field.
Qed.

Lemma arcsinh_odd : forall x, arcsinh (- x) = - arcsinh x.
Proof.
intros x.
assert (S : forall y, sinh (- y) = - sinh y)
  by (intros y; unfold sinh; rewrite Ropp_involutive; field).
rewrite <- (sinh_arcsinh x) at 1.
rewrite <- S, arcsinh_sinh. reflexivity.
Qed.

Lemma arcsinh_ln : forall t, arcsinh t = ln (t + sqrt (1 + t * t)).
Proof.
intros t. unfold arcsinh. replace (t ^ 2 + 1) with (1 + t * t) by ring. reflexivity.
Qed.

(** For [c = sqrt (1 + t^2)] and [u = t / c], [(1 + u) / (1 - u)] is
    [(c + t)^2]. *)
Lemma arcsinh_atanh : forall t, 0 <= t -> arcsinh t = Ratanh (t / sqrt (1 + t * t)).
Proof.
intros t Ht. unfold arcsinh, Ratanh.
replace (t ^ 2 + 1) with (1 + t * t) by ring.
set (c := sqrt (1 + t * t)).
assert (Hc : c * c = 1 + t * t) by (unfold c; apply sqrt_sqrt; nra).
assert (Hc0 : 0 <= c) by apply sqrt_pos.
assert (Hct : t < c) by nra.
(* [(c + t) (c - t) = 1]. *)
assert (Q : (1 + t / c) / (1 - t / c) = (t + c) * (t + c)).
{ replace ((1 + t / c) / (1 - t / c)) with ((c + t) / (c - t)) by (field; repeat split; lra).
  apply (Rmult_eq_reg_r (c - t)); [| lra].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
  replace ((t + c) * (t + c) * (c - t)) with ((t + c) * (c * c - t * t)) by ring.
  rewrite Hc. ring. }
rewrite Q, ln_mult by lra. field.
Qed.

Lemma acosh_ln : forall x, Racosh x = ln (x + sqrt ((x - 1) * (x + 1))).
Proof.
intros x. unfold Racosh. replace (x * x - 1) with ((x - 1) * (x + 1)) by ring. reflexivity.
Qed.

(** For [r = sqrt (x^2 - 1)] and [u = r / x], [(1 + u) / (1 - u)] is
    [(x + r)^2]. *)
Lemma acosh_atanh : forall x, 1 <= x -> Racosh x = Ratanh (sqrt ((x - 1) * (x + 1)) / x).
Proof.
intros x Hx. unfold Racosh, Ratanh.
replace (x * x - 1) with ((x - 1) * (x + 1)) by ring.
set (r := sqrt ((x - 1) * (x + 1))).
assert (Hr : r * r = x * x - 1) by (unfold r; rewrite sqrt_sqrt by nra; ring).
assert (Hr0 : 0 <= r) by apply sqrt_pos.
assert (Hrx : r < x) by nra.
(* [(x + r) (x - r) = 1]. *)
assert (Q : (1 + r / x) / (1 - r / x) = (x + r) * (x + r)).
{ replace ((1 + r / x) / (1 - r / x)) with ((x + r) / (x - r)) by (field; repeat split; lra).
  apply (Rmult_eq_reg_r (x - r)); [| lra].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
  replace ((x + r) * (x + r) * (x - r)) with ((x + r) * (x * x - r * r)) by ring.
  rewrite Hr. ring. }
rewrite Q, ln_mult by lra. field.
Qed.

(** [encl_shl l (-1)] multiplies by [bpow radix2 (-1)]. *)
Lemma atanh_ln : forall t, Ratanh t = ln ((1 + t) / (1 - t)) * bpow radix2 (-1).
Proof.
intros t. unfold Ratanh.
assert (B : bpow radix2 (-1) = / 2) by reflexivity.
rewrite B. reflexivity.
Qed.

(** [ln t <= t - 1] at [t = y / x]. *)
Lemma ln_le_sub : forall x y, 0 < x <= y -> ln y <= ln x + (y - x) / x.
Proof.
intros x y [Hx Hxy].
assert (Hq : 0 < y / x) by (apply Rdiv_lt_0_compat; lra).
(* [1 + ln t <= exp (ln t) = t]. *)
pose proof (exp_ineq1_le (ln (y / x))) as H. rewrite exp_ln in H by exact Hq.
assert (Ey : y = x * (y / x)) by (field; lra).
rewrite Ey at 1. rewrite ln_mult by lra.
replace ((y - x) / x) with (y / x - 1) by (field; lra).
lra.
Qed.

(** ** The rules *)

(** [log10_dir] returns [k] for the [f64] [10^k], [0 <= k <= 22]. *)
Lemma log10_pow10_rule :
  forall x (up : bool) k,
  is_finite x = true ->
  List.find (fun k => eq (DyadicExp.pow10 (Z.of_nat k)) x) (List.seq 0 23) = Some k ->
  mpfr_round f64_format (rnd_of up) (Rlog10 (B2R x)) (with_val (of_u64 (Z.of_nat k))).
Proof.
intros x up k Fx Hf.
apply find_some in Hf. destruct Hf as [Hin Heq].
apply in_seq in Hin.
(* [pow10 k] is the [f64] [10^k]: [of_u64 1] for [k = 0]. *)
assert (P : is_finite (DyadicExp.pow10 (Z.of_nat k)) = true /\
            B2R (DyadicExp.pow10 (Z.of_nat k)) = 10 ^ k).
{ destruct k as [| k'].
  - change (DyadicExp.pow10 (Z.of_nat 0)) with (of_u64 1).
    destruct (of_u64_exact 1) as (F1 & _ & E1); [lia |].
    split; [exact F1 |]. rewrite E1. reflexivity.
  - assert (Hk : (1 <= Z.of_nat (S k') <= 22)%Z) by lia.
    destruct (pow10_exact (Z.of_nat (S k')) Hk) as [F E].
    split; [exact F |]. rewrite E, <- pow_IZR. reflexivity. }
destruct P as [Fp Ep].
unfold eq in Heq. rewrite Beqb_correct in Heq by assumption.
destruct (Req_bool_spec (B2R (DyadicExp.pow10 (Z.of_nat k))) (B2R x)) as [Ex | Ex];
  [| discriminate].
assert (Hk : (0 <= Z.of_nat k <= 2 ^ 53)%Z) by lia.
destruct (of_u64_exact (Z.of_nat k) Hk) as (Fk & _ & Ek).
apply rnd_exact; [exact Fk |].
rewrite <- Ex, Ep, Ek. unfold Rlog10.
rewrite Rlog_pow by lra. symmetry. apply INR_IZR_INZ.
Qed.

(** No rule of [log_rules] applies to a finite [x > 0]. *)
Lemma log_rules_finite_pos :
  forall x, is_finite x = true -> 0 < B2R x -> DyadicLog.log_rules x = None.
Proof.
intros x Fx Hx. unfold DyadicLog.log_rules.
rewrite (fin_not_nan x Fx), (fin_neq_inf x Fx). cbn [orb].
assert (Fz : is_finite Model.zero = true) by reflexivity.
assert (Ez : eq x Model.zero = false).
{ unfold eq. rewrite Beqb_correct by assumption.
  destruct (Req_bool_spec (B2R x) (B2R Model.zero)) as [H | H]; [| reflexivity].
  change (B2R Model.zero) with 0 in H. lra. }
assert (Lz : lt x Model.zero = false).
{ unfold lt. rewrite Bltb_correct by assumption.
  destruct (Rlt_bool_spec (B2R x) (B2R Model.zero)) as [H | H]; [| reflexivity].
  change (B2R Model.zero) with 0 in H. lra. }
rewrite Ez, Lz. reflexivity.
Qed.
