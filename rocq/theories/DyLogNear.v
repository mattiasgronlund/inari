(** * The logarithms and inverse hyperbolic functions of the dyadic kernel rounded to nearest

    [ln_near_with ziv_near_strict] and the others of [DyadicLog] return,
    where they return, their function at a finite [x] of its domain
    rounded to nearest as [near_round] says: the loop by
    [ziv_near_strict_correct] and the enclosures of [DyLog.v] and
    [DyLogHyp.v], and the rules before it by the cells of [NearCells.v]
    and the bounds of [DyLogRules.v] and [DyLogTiny.v]. Where they return
    with [ziv_near_strict], they return the same with [Dyadic.ziv_near]
    ([ln_near_strict] and the others). *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary LogReal DyRound DyConv DyOps DyDriver
  DyGrow DyConst DyExpCore DyExpRules DyExp ExpReal DyHyp DyLogRules DyLogTiny DyLogCore DyLog
  DyLogHyp NearF64 NearCells DyDriverNear FastLog FastAhyp.
From Inari Require AtanhSeries DySinhTiny Decompose.

Open Scope Z_scope.

(** ** Helpers *)

Local Open Scope R_scope.

(** [TINY_NEAR] is 2^-27: [B2SF] computes its significand 2^52 and
    exponent -79, as [hyp_lit_tiny] of [DyHypRules.v] does for 2^-26. *)
Local Lemma lit_tiny_near : B2R DyadicExp.tiny_near = bpow radix2 (-27).
Proof.
rewrite <- (SF2R_B2SF _ _ DyadicExp.tiny_near).
let s := eval vm_compute in (B2SF DyadicExp.tiny_near) in
replace (B2SF DyadicExp.tiny_near) with s by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]. unfold F2R. cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
reflexivity.
Qed.

(** For [0 < y < 2^-27], [y - y^3/2 <= asinh y <= y], so [asinh y] is
    within [y 2^-54] of [y], as [y^2 < 2^-54]. Above, [y < sinh y]
    ([sinh_tiny_real]). Below, [asinh y = atanh u] with [u = y / c] and
    [c = sqrt (1 + y^2)] ([arcsinh_atanh]), [atanh u >= u] (the series of
    [atanh] to one term, [atanh_sum_bounds]), and [y = u c <= u (1 + y^2/2)]
    with [u <= y], as [1 <= c <= 1 + y^2/2]. *)
Local Lemma asinh_tiny_near_pos :
  forall y, 0 < y < bpow radix2 (-27) -> Rabs (arcsinh y - y) <= y * bpow radix2 (-54).
Proof.
intros y Hy.
assert (Hb : bpow radix2 (-27) = 1 / 134217728 /\ bpow radix2 (-26) = 1 / 67108864 /\
             bpow radix2 (-54) = 1 / 18014398509481984)
  by (cbn [bpow radix_val radix2]; repeat split; lra).
destruct Hb as (Hb27 & Hb26 & Hb54).
assert (Hy26 : 0 < y < bpow radix2 (-26)) by lra.
destruct (DySinhTiny.sinh_tiny_real y Hy26) as [S1 _].
assert (U : arcsinh y <= y).
{ pose proof (asinh_inc y (sinh y) (Rlt_le _ _ S1)) as A. rewrite arcsinh_sinh in A. exact A. }
rewrite Hb27 in Hy. rewrite Hb54.
assert (Hyy : y * y < 1 / 18014398509481984).
{ replace (1 / 18014398509481984) with (1 / 134217728 * (1 / 134217728)) by field.
  apply Rmult_le_0_lt_compat; lra. }
assert (H3 : y * (y * y) < y * (1 / 18014398509481984)) by (apply Rmult_lt_compat_l; lra).
set (c := sqrt (1 + y * y)).
assert (Hc : c * c = 1 + y * y) by (unfold c; apply sqrt_sqrt; nra).
assert (Hc0 : 0 <= c) by apply sqrt_pos.
assert (Hc1 : 1 <= c) by nra.
assert (Hc2 : c <= 1 + y * y / 2).
{ unfold c. rewrite <- (sqrt_square (1 + y * y / 2)) by nra.
  apply sqrt_le_1_alt.
  assert (0 <= (y * y) * (y * y)) by (apply Rmult_le_pos; nra).
  nra. }
set (u := y / c).
assert (Hyu : y = u * c) by (unfold u; field; lra).
assert (Hu0 : 0 <= u) by (unfold u, Rdiv; apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra]).
assert (Huy : u <= y) by nra.
assert (Hu1 : u < 1) by lra.
assert (Hu2 : y <= u + u * (y * y) / 2) by nra.
assert (Hu3 : u * (y * y) <= y * (y * y)) by (apply Rmult_le_compat_r; [nra | exact Huy]).
destruct (AtanhSeries.atanh_sum_bounds 1 u (conj Hu0 Hu1)) as [L _].
replace (AtanhSeries.atanh_sum 1 u) with u in L by (cbn; field).
assert (E : arcsinh y = Ratanh u) by (unfold u, c; apply arcsinh_atanh; lra).
rewrite Rabs_left1 by lra.
lra.
Qed.

(** [asinh] is odd ([arcsinh_odd]). *)
Local Lemma asinh_tiny_near :
  forall y, y <> 0 -> Rabs y < bpow radix2 (-27) ->
  Rabs (arcsinh y - y) <= Rabs y * bpow radix2 (-54).
Proof.
intros y Hy0 Hy.
destruct (Rlt_or_le 0 y) as [P|N].
- rewrite (Rabs_pos_eq y) in Hy |- * by lra. apply asinh_tiny_near_pos. lra.
- rewrite (Rabs_left y) in Hy |- * by lra.
  replace (arcsinh y - y) with (- (arcsinh (- y) - - y)) by (rewrite arcsinh_odd; ring).
  rewrite Rabs_Ropp. apply asinh_tiny_near_pos. lra.
Qed.

(** For [0 < y < 2^-27], [y < atanh y <= y + y^3/3 + y^5 / (1 - y^2)]
    (the series of [atanh] to two terms, [atanh_sum_bounds], as
    [atanh_tiny_real] of [DyLogTiny.v] does at 2^-26), and
    [y^3/3 + y^5 / (1 - y^2) <= y^3/3 + 2 y^5] is below [y 2^-54], as
    [y^2 < 2^-54]. *)
Local Lemma atanh_tiny_near_pos :
  forall y, 0 < y < bpow radix2 (-27) -> Rabs (Ratanh y - y) <= y * bpow radix2 (-54).
Proof.
intros y Hy.
assert (Hb : bpow radix2 (-27) = 1 / 134217728 /\ bpow radix2 (-54) = 1 / 18014398509481984)
  by (cbn [bpow radix_val radix2]; split; lra).
destruct Hb as [Hb27 Hb54]. rewrite Hb27 in Hy. rewrite Hb54.
assert (Hyy : y * y < 1 / 18014398509481984).
{ replace (1 / 18014398509481984) with (1 / 134217728 * (1 / 134217728)) by field.
  apply Rmult_le_0_lt_compat; lra. }
assert (E2 : y ^ 2 = y * y) by ring.
assert (Hy2 : 1 / 2 <= 1 - y ^ 2) by lra.
destruct (AtanhSeries.atanh_sum_bounds 2 y ltac:(lra)) as [L U].
replace (AtanhSeries.atanh_sum 2 y) with (y + y ^ 3 / 3) in L, U by (cbn; field).
change (2 * 2 + 1)%nat with 5%nat in U.
(* [y^5 / (1 - y^2) <= 2 y^5], as [1 - y^2 >= 1/2]. *)
assert (Hq : y ^ 5 / (1 - y ^ 2) <= 2 * y ^ 5).
{ unfold Rdiv. rewrite Rmult_comm. apply Rmult_le_compat_r; [apply pow_le; lra|].
  replace 2 with (/ (1 / 2)) by field. apply Rinv_le_contravar; lra. }
assert (H3 : y ^ 3 < y * (1 / 18014398509481984)).
{ replace (y ^ 3) with (y * (y * y)) by ring. apply Rmult_lt_compat_l; lra. }
assert (H5 : y ^ 5 < y ^ 3 * (1 / 18014398509481984)).
{ replace (y ^ 5) with (y ^ 3 * (y * y)) by ring.
  apply Rmult_lt_compat_l; [apply pow_lt; lra | exact Hyy]. }
assert (P3 : 0 < y ^ 3) by (apply pow_lt; lra).
rewrite Rabs_pos_eq by lra.
lra.
Qed.

(** [atanh] is odd ([Ratanh_odd]). *)
Local Lemma atanh_tiny_near :
  forall y, y <> 0 -> Rabs y < bpow radix2 (-27) ->
  Rabs (Ratanh y - y) <= Rabs y * bpow radix2 (-54).
Proof.
intros y Hy0 Hy.
assert (Hb : bpow radix2 (-27) < 1) by (cbn [bpow radix_val radix2]; lra).
destruct (Rlt_or_le 0 y) as [P|N].
- rewrite (Rabs_pos_eq y) in Hy |- * by lra. apply atanh_tiny_near_pos. lra.
- rewrite (Rabs_left y) in Hy |- * by lra.
  replace (Ratanh y - y) with (- (Ratanh (- y) - - y)) by (rewrite Ratanh_odd by lra; ring).
  rewrite Rabs_Ropp. apply atanh_tiny_near_pos. lra.
Qed.

(** The rules [|x| < 2^-27] of [asinh_near_with] and [atanh_near_with]
    return [x]: at 0 its value, and otherwise within [|x| 2^-54] of the
    value ([near_x]). *)
Local Lemma asinh_tiny_near_rule :
  forall x, is_finite x = true -> lt (fabs x) DyadicExp.tiny_near = true ->
  near_round (arcsinh (B2R x)) x.
Proof.
intros x Fx G.
assert (Fth : is_finite DyadicExp.tiny_near = true) by (vm_compute; reflexivity).
pose proof (fabs_lt_R x _ Fx Fth G) as Hy. rewrite lit_tiny_near in Hy.
destruct (Req_dec (B2R x) 0) as [H0|H0].
- replace (arcsinh (B2R x)) with (B2R x) by (rewrite H0, arcsinh_0; reflexivity).
  exact (near_exact x Fx).
- apply near_x; [exact Fx | exact H0 |]. exact (asinh_tiny_near (B2R x) H0 Hy).
Qed.

Local Lemma atanh_tiny_near_rule :
  forall x, is_finite x = true -> lt (fabs x) DyadicExp.tiny_near = true ->
  near_round (Ratanh (B2R x)) x.
Proof.
intros x Fx G.
assert (Fth : is_finite DyadicExp.tiny_near = true) by (vm_compute; reflexivity).
pose proof (fabs_lt_R x _ Fx Fth G) as Hy. rewrite lit_tiny_near in Hy.
destruct (Req_dec (B2R x) 0) as [H0|H0].
- assert (E : Ratanh (B2R x) = B2R x).
  { rewrite H0. unfold Ratanh. replace ((1 + 0) / (1 - 0)) with 1 by field.
    rewrite ln_1. field. }
  rewrite E. exact (near_exact x Fx).
- apply near_x; [exact Fx | exact H0 |]. exact (atanh_tiny_near (B2R x) H0 Hy).
Qed.

(** The exact powers of 10 of [log10_near_with]: [log10 (10^k) = k], the
    [f64] [of_u64 k], as in [log10_pow10_rule] of [DyLogRules.v]. *)
Local Lemma log10_pow10_near :
  forall x k,
  is_finite x = true ->
  List.find (fun k => eq (DyadicExp.pow10 (Z.of_nat k)) x) (List.seq 0 23) = Some k ->
  near_round (Rlog10 (B2R x)) (of_u64 (Z.of_nat k)).
Proof.
intros x k Fx Hf.
apply find_some in Hf. destruct Hf as [Hin Heq].
apply in_seq in Hin.
(* [pow10 k] is the [f64] [10^k]: [of_u64 1] for [k = 0]. *)
assert (P : is_finite (DyadicExp.pow10 (Z.of_nat k)) = true /\
            B2R (DyadicExp.pow10 (Z.of_nat k)) = 10 ^ k).
{ destruct k as [| k'].
  - change (DyadicExp.pow10 (Z.of_nat 0)) with (of_u64 1).
    destruct (Decompose.of_u64_exact 1) as (F1 & _ & E1); [lia |].
    split; [exact F1 |]. rewrite E1. reflexivity.
  - assert (Hk : (1 <= Z.of_nat (S k') <= 22)%Z) by lia.
    destruct (pow10_exact (Z.of_nat (S k')) Hk) as [F E].
    split; [exact F |]. rewrite E, <- pow_IZR. reflexivity. }
destruct P as [Fp Ep].
unfold eq in Heq. rewrite Beqb_correct in Heq by assumption.
destruct (Req_bool_spec (B2R (DyadicExp.pow10 (Z.of_nat k))) (B2R x)) as [Ex | Ex];
  [| discriminate].
assert (Hk : (0 <= Z.of_nat k <= 2 ^ 53)%Z) by lia.
destruct (Decompose.of_u64_exact (Z.of_nat k) Hk) as (Fk & _ & Ek).
replace (Rlog10 (B2R x)) with (B2R (of_u64 (Z.of_nat k))); [exact (near_exact _ Fk)|].
rewrite <- Ex, Ep, Ek. unfold Rlog10.
rewrite Rlog_pow by lra. symmetry. apply INR_IZR_INZ.
Qed.

(** Where the rule [|x| < 2^-27] fails, [|x| >= 2^-27], as the fast paths
    of [asinh] and [atanh] take. *)
Local Lemma fast_not_tiny_near :
  forall x, is_finite x = true -> lt (fabs x) DyadicExp.tiny_near = false ->
  bpow radix2 (-27) <= Rabs (B2R x).
Proof.
intros x Fx G. unfold lt in G.
rewrite Bltb_correct in G by (first [unfold fabs; rewrite is_finite_Babs; exact Fx | reflexivity]).
rewrite hyp_fabs, lit_tiny_near in G.
destruct (Rlt_bool_spec (Rabs (B2R x)) (bpow radix2 (-27))) as [_|L]; [discriminate G | exact L].
Qed.

Local Close Scope R_scope.

(** Where [ziv_near_strict] returns, [Dyadic.ziv_near] returns the same:
    the goal [<body with ziv_near_strict> = Some v -> <body with
    Dyadic.ziv_near> = Some v] of a function of this file, split at its
    guards, which name neither driver, as [dir_strict] of [DyExp.v]. *)
Local Ltac near_strict :=
  repeat match goal with
  | |- (if ?c then _ else _) = Some _ -> _ => destruct c; [exact (fun h => h)|]
  | |- (match ?c with Some _ => _ | None => _ end) = Some _ -> _ =>
      destruct c; [exact (fun h => h)|]
  end;
  apply ziv_near_strict_ziv.

(** ** The functions rounded to nearest *)

Theorem ln_near_correct :
  forall x v,
  is_finite x = true -> log_dom (B2R x) -> DyadicLog.ln_near_with ziv_near_strict x = Some v ->
  near_round (ln (B2R x)) v.
Proof.
intros x v Fx Dx H. unfold DyadicLog.ln_near_with in H.
rewrite (log_rules_finite_pos x Fx Dx) in H.
destruct (DyadicLog.fast_ln_near false x) eqn:F; cbv iota in H.
{ injection H as <-. exact (fast_ln_near_correct false x _ Fx Dx F). }
apply (ziv_near_strict_correct (DyadicLog.ev_ln x) 1%nat _ v); [|exact H].
intros n a Hn Ha. exact (ev_ln_correct x n a Hn Ha).
Qed.

Theorem log2_near_correct :
  forall x v,
  is_finite x = true -> log_dom (B2R x) -> DyadicLog.log2_near_with ziv_near_strict x = Some v ->
  near_round (Rlog2 (B2R x)) v.
Proof.
intros x v Fx Dx H. unfold DyadicLog.log2_near_with in H.
rewrite (log_rules_finite_pos x Fx Dx) in H.
destruct (DyadicLog.fast_log2_near false x) eqn:F; cbv iota in H.
{ injection H as <-. exact (fast_log2_near_correct false x _ Fx Dx F). }
apply (ziv_near_strict_correct (DyadicLog.ev_log2 x) 1%nat _ v); [|exact H].
intros n a Hn Ha. exact (ev_log2_correct x n a Hn Ha).
Qed.

Theorem log10_near_correct :
  forall x v,
  is_finite x = true -> log_dom (B2R x) -> DyadicLog.log10_near_with ziv_near_strict x = Some v ->
  near_round (Rlog10 (B2R x)) v.
Proof.
intros x v Fx Dx H. unfold DyadicLog.log10_near_with in H.
rewrite (log_rules_finite_pos x Fx Dx) in H.
destruct (DyadicLog.fast_log10_near false x) eqn:F; cbv iota in H.
{ injection H as <-. exact (fast_log10_near_correct false x _ Fx Dx F). }
destruct (List.find (fun k => eq (DyadicExp.pow10 (Z.of_nat k)) x) (List.seq 0 23))
  as [k|] eqn:Ef.
- injection H as <-. exact (log10_pow10_near x k Fx Ef).
- apply (ziv_near_strict_correct (DyadicLog.ev_log10 x) 1%nat _ v); [|exact H].
  intros n a Hn Ha. exact (ev_log10_correct x n a Hn Ha).
Qed.

Theorem asinh_near_correct :
  forall x v,
  is_finite x = true -> DyadicLog.asinh_near_with ziv_near_strict x = Some v ->
  near_round (arcsinh (B2R x)) v.
Proof.
intros x v Fx H. unfold DyadicLog.asinh_near_with in H.
rewrite (fin_not_nan x Fx), (fin_neq_inf x Fx), (fin_neq_ninf x Fx) in H. cbn [orb] in H.
destruct (lt (fabs x) DyadicExp.tiny_near) eqn:G; cbv iota in H.
{ injection H as <-. exact (asinh_tiny_near_rule x Fx G). }
destruct (DyadicLog.fast_asinh_near false x) eqn:F; cbv iota in H.
{ injection H as <-. exact (fast_asinh_near_correct false x _ Fx (fast_not_tiny_near x Fx G) F). }
apply (ziv_near_strict_correct (DyadicLog.ev_asinh x) 1%nat _ v); [|exact H].
intros n a Hn Ha. exact (ev_asinh_correct x n a Hn Ha).
Qed.

(** [x < 1.0] is false on [acosh_dom], so only the loop remains, at
    [x = 1] too. *)
Theorem acosh_near_correct :
  forall x v,
  is_finite x = true -> acosh_dom (B2R x) -> DyadicLog.acosh_near_with ziv_near_strict x = Some v ->
  near_round (Racosh (B2R x)) v.
Proof.
intros x v Fx Dx H. unfold DyadicLog.acosh_near_with in H.
rewrite (fin_not_nan x Fx), (fin_neq_inf x Fx) in H. cbn [orb] in H.
destruct (lt x DyadicExp.one) eqn:G; cbv iota in H.
{ exfalso. apply lt_R in G; [|exact Fx|reflexivity].
  rewrite dexp_one_R in G. unfold acosh_dom in Dx. lra. }
destruct (DyadicLog.fast_acosh_near false x) eqn:F; cbv iota in H.
{ injection H as <-. exact (fast_acosh_near_correct false x _ Fx Dx F). }
apply (ziv_near_strict_correct (DyadicLog.ev_acosh x) 1%nat _ v); [|exact H].
intros n a Hn Ha. exact (ev_acosh_correct x n a Fx Dx Hn Ha).
Qed.

(** [|x| > 1.0] and [|x| == 1.0] are false on [atanh_dom]. *)
Theorem atanh_near_correct :
  forall x v,
  is_finite x = true -> atanh_dom (B2R x) -> DyadicLog.atanh_near_with ziv_near_strict x = Some v ->
  near_round (Ratanh (B2R x)) v.
Proof.
intros x v Fx Dx H. unfold DyadicLog.atanh_near_with in H. cbv zeta in H.
assert (Ft : is_finite (fabs x) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fx).
assert (A : (Rabs (B2R x) < 1)%R) by (unfold atanh_dom in Dx; apply Rabs_def1; lra).
rewrite (fin_not_nan x Fx) in H. cbv iota in H.
destruct (gt (fabs x) DyadicExp.one) eqn:G1; cbv iota in H.
{ exfalso. assert (G1' : lt DyadicExp.one (fabs x) = true) by exact G1.
  apply lt_R in G1'; [|reflexivity|exact Ft].
  rewrite dexp_one_R, hyp_fabs in G1'. lra. }
destruct (eq (fabs x) DyadicExp.one) eqn:G2; cbv iota in H.
{ exfalso. unfold eq in G2.
  rewrite Beqb_correct in G2 by (first [exact Ft | reflexivity]).
  rewrite dexp_one_R, hyp_fabs in G2.
  destruct (Req_bool_spec (Rabs (B2R x)) 1); [lra | discriminate G2]. }
destruct (lt (fabs x) DyadicExp.tiny_near) eqn:G3; cbv iota in H.
{ injection H as <-. exact (atanh_tiny_near_rule x Fx G3). }
destruct (DyadicLog.fast_atanh_near false x) eqn:F; cbv iota in H.
{ injection H as <-.
  exact (fast_atanh_near_correct false x _ Fx (conj (fast_not_tiny_near x Fx G3) A) F). }
apply (ziv_near_strict_correct (DyadicLog.ev_atanh x) 1%nat _ v); [|exact H].
intros n a Hn Ha. exact (ev_atanh_correct x n a Fx Dx Hn Ha).
Qed.

Theorem ln_near_strict :
  forall x v, DyadicLog.ln_near_with ziv_near_strict x = Some v -> DyadicLog.ln_near x = Some v.
Proof.
intros x v. unfold DyadicLog.ln_near, DyadicLog.ln_near_with.
destruct (DyadicLog.log_rules x); [exact (fun h => h)|].
destruct (DyadicLog.fast_ln_near false x); [exact (fun h => h)|apply ziv_near_strict_ziv].
Qed.

Theorem log2_near_strict :
  forall x v, DyadicLog.log2_near_with ziv_near_strict x = Some v -> DyadicLog.log2_near x = Some v.
Proof.
intros x v. unfold DyadicLog.log2_near, DyadicLog.log2_near_with.
destruct (DyadicLog.log_rules x); [exact (fun h => h)|].
destruct (DyadicLog.fast_log2_near false x); [exact (fun h => h)|apply ziv_near_strict_ziv].
Qed.

Theorem log10_near_strict :
  forall x v,
  DyadicLog.log10_near_with ziv_near_strict x = Some v -> DyadicLog.log10_near x = Some v.
Proof.
intros x v. unfold DyadicLog.log10_near, DyadicLog.log10_near_with.
destruct (DyadicLog.log_rules x); [exact (fun h => h)|].
destruct (DyadicLog.fast_log10_near false x); [exact (fun h => h)|].
destruct (List.find (fun k => eq (DyadicExp.pow10 (Z.of_nat k)) x) (List.seq 0 23));
  [exact (fun h => h)|apply ziv_near_strict_ziv].
Qed.

Theorem asinh_near_strict :
  forall x v,
  DyadicLog.asinh_near_with ziv_near_strict x = Some v -> DyadicLog.asinh_near x = Some v.
Proof.
intros x v. unfold DyadicLog.asinh_near, DyadicLog.asinh_near_with. near_strict.
Qed.

Theorem acosh_near_strict :
  forall x v,
  DyadicLog.acosh_near_with ziv_near_strict x = Some v -> DyadicLog.acosh_near x = Some v.
Proof.
intros x v. unfold DyadicLog.acosh_near, DyadicLog.acosh_near_with. near_strict.
Qed.

Theorem atanh_near_strict :
  forall x v,
  DyadicLog.atanh_near_with ziv_near_strict x = Some v -> DyadicLog.atanh_near x = Some v.
Proof.
intros x v. unfold DyadicLog.atanh_near, DyadicLog.atanh_near_with. cbv zeta. near_strict.
Qed.
