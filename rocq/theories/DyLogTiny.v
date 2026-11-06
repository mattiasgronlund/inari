(** * The rules before Ziv's strategy for [asinh] and [atanh] of tiny arguments

    The branches of [asinh_dir] and [atanh_dir] of [DyadicLog] in
    [Model.v] for [|x| < 2^-26]: [asinh x] and [atanh x] are [x] if [x] is
    0. Otherwise [asinh x] lies strictly between [x] and the next [f64]
    toward zero, which [toward_zero x up] returns when [up] rounds toward
    zero, as [tanh x] does in [DyTanhTiny.v], and [atanh x] lies strictly
    between [x] and the next [f64] away from zero, which [away x up]
    returns when [up] rounds away from zero, as [sinh x] does in
    [DySinhTiny.v]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Elementary ExpReal ConstLn Encoding IdealGetD OfPointCore
  MpfrRound MpfrIdeal ExpSeries AtanhSeries DyExpRules DyHypRules DySinhTiny DyTanhTiny
  DyLogRules.

Open Scope R_scope.

Local Notation rnd_of up := (if up then RNDU else RNDD).

(** The format of the finite [f64]s without the bound above, as in
    [DyTanhTiny.v]. *)
Local Notation G := (generic_format radix2 (SpecFloat.fexp 53 1024)).
Local Notation succ64 := (succ radix2 (SpecFloat.fexp 53 1024)).

(** If [w = succ p] with [0 <= p] and [w < 2^-26], [asinh w] lies strictly
    between [p] and [w]. [asinh] is the increasing inverse of [sinh], and
    [sinh_tiny_succ] gives [w < sinh w] and, for [p > 0],
    [sinh p < succ p = w]. *)
Lemma asinh_tiny_between :
  forall p, 0 <= p -> succ64 p < bpow radix2 (-26) -> p < arcsinh (succ64 p) < succ64 p.
Proof.
intros p Hp Hw.
assert (P53 : Prec_gt_0 53) by (unfold Prec_gt_0; lia).
pose proof (ulp_FLT_gt radix2 (-1074) 53 p) as Hu.
change (Rabs p * bpow radix2 (-53) < ulp radix2 (SpecFloat.fexp 53 1024) p) in Hu.
rewrite Rabs_pos_eq in Hu by exact Hp.
assert (Hs : succ64 p = p + ulp radix2 (SpecFloat.fexp 53 1024) p)
  by (apply succ_eq_pos; exact Hp).
assert (He : 0 < bpow radix2 (-53)) by apply bpow_gt_0.
assert (Hpw : p < succ64 p) by nra.
set (w := succ64 p) in *.
split.
- destruct Hp as [Hp | <-].
  + (* [sinh p < succ p = w], and [p = asinh (sinh p)]. *)
    destruct (sinh_tiny_succ p ltac:(lra)) as [_ H].
    rewrite <- (arcsinh_sinh p) at 1. apply arcsinh_lt. exact H.
  + rewrite <- arcsinh_0 at 1. apply arcsinh_lt. exact Hpw.
- (* [w < sinh w], and [w = asinh (sinh w)]. *)
  destruct (sinh_tiny_succ w ltac:(lra)) as [H _].
  rewrite <- (arcsinh_sinh w) at 2. apply arcsinh_lt. exact H.
Qed.

Lemma asinh_tiny_rule :
  forall x (up : bool), is_finite x = true -> lt (fabs x) DyadicExp.tiny_hyp = true ->
  mpfr_round f64_format (rnd_of up) (arcsinh (B2R x)) (with_val (DyadicExp.toward_zero x up)).
Proof.
intros x up Fx Ht.
assert (Fth : is_finite DyadicExp.tiny_hyp = true) by (vm_compute; reflexivity).
pose proof (fabs_lt_R x _ Fx Fth Ht) as Hy. rewrite hyp_lit_tiny in Hy.
assert (Fz : is_finite zero = true) by reflexivity.
unfold DyadicExp.toward_zero, eq, gt.
rewrite Beqb_correct by assumption. rewrite Bltb_correct by assumption.
assert (Ez : B2R zero = 0) by reflexivity. rewrite Ez.
destruct (Req_bool_spec (B2R x) 0) as [Hx|Hx]; cbn [orb].
{ (* [asinh 0 = 0]. *)
  apply rnd_exact; [exact Fx|]. rewrite Hx, arcsinh_0. reflexivity. }
destruct (toward_zero_bits x Fx Hx) as (p & Hp & Gp & Fb & Ex & Eb).
set (b := from_bits (to_bits x - 1)) in *.
assert (Hsp : 0 <= succ64 p) by (eapply Rle_trans; [exact Hp | apply succ_ge_id]).
revert Ex Eb. destruct (Bsign x); intros Ex Eb.
- (* [x = - succ p < 0]: [x] is below [asinh x], and [b = -p] is the next
     [f64] above [x]. *)
  assert (Hw : succ64 p < bpow radix2 (-26))
    by (rewrite Ex, Rabs_Ropp, Rabs_pos_eq in Hy by exact Hsp; exact Hy).
  destruct (asinh_tiny_between p Hp Hw) as [H1 H2].
  rewrite (Rlt_bool_false 0 (B2R x)) by (rewrite Ex; lra).
  destruct up; cbn [Bool.eqb].
  + apply (rnd_bracket x b true); [exact Fx | exact Fb | |].
    * rewrite Eb, Ex, succ_opp, pred_succ by first [exact Gp | typeclasses eauto]; reflexivity.
    * rewrite Eb, Ex, arcsinh_odd. lra.
  + apply (rnd_bracket x b false); [exact Fx | exact Fb | |].
    * rewrite Eb, Ex, succ_opp, pred_succ by first [exact Gp | typeclasses eauto]; reflexivity.
    * rewrite Eb, Ex, arcsinh_odd. lra.
- (* [x = succ p > 0]: [asinh x] is below [x], and [b = p] is the [f64]
     before [x]. *)
  assert (Hw : succ64 p < bpow radix2 (-26))
    by (rewrite Ex, Rabs_pos_eq in Hy by exact Hsp; exact Hy).
  destruct (asinh_tiny_between p Hp Hw) as [H1 H2].
  assert (Hpos : 0 < B2R x) by (rewrite Ex; lra).
  rewrite (Rlt_bool_true 0 (B2R x)) by exact Hpos.
  destruct up; cbn [Bool.eqb].
  + apply (rnd_bracket b x true); [exact Fb | exact Fx | |].
    * rewrite Eb, Ex; reflexivity.
    * rewrite Eb, Ex. lra.
  + apply (rnd_bracket b x false); [exact Fb | exact Fx | |].
    * rewrite Eb, Ex; reflexivity.
    * rewrite Eb, Ex. lra.
Qed.

(** For [0 < y < 2^-26], [y < atanh y < y + y 2^-53]: the series of
    [atanh] to two terms ([atanh_sum_bounds]) puts [atanh y] between
    [y + y^3/3] and [y + y^3/3 + y^5 / (1 - y^2)], and [y^2 < 2^-52] makes
    [y^3/3 + y^5 / (1 - y^2) <= y^3/3 + 2 y^5] less than [y 2^-53]. *)
Lemma atanh_tiny_real :
  forall y, 0 < y < bpow radix2 (-26) -> y < Ratanh y < y + y * bpow radix2 (-53).
Proof.
intros y Hy.
assert (Hb : bpow radix2 (-26) = 1 / 67108864 /\ bpow radix2 (-53) = 1 / 9007199254740992)
  by (cbn [bpow radix_val radix2]; split; lra).
destruct Hb as [Hb26 Hb53]. rewrite Hb26 in Hy. rewrite Hb53.
assert (Hyy : y * y < 1 / 4503599627370496).
{ replace (1 / 4503599627370496) with (1 / 67108864 * (1 / 67108864)) by field.
  apply Rmult_le_0_lt_compat; lra. }
assert (E2 : y ^ 2 = y * y) by ring.
assert (Hy2 : 1 / 2 <= 1 - y ^ 2) by lra.
destruct (atanh_sum_bounds 2 y ltac:(lra)) as [L U].
replace (atanh_sum 2 y) with (y + y ^ 3 / 3) in L, U by (cbn; field).
change (2 * 2 + 1)%nat with 5%nat in U.
(* [y^5 / (1 - y^2) <= 2 y^5], as [1 - y^2 >= 1/2]. *)
assert (Hq : y ^ 5 / (1 - y ^ 2) <= 2 * y ^ 5).
{ unfold Rdiv. rewrite Rmult_comm. apply Rmult_le_compat_r; [apply pow_le; lra|].
  replace 2 with (/ (1 / 2)) by field. apply Rinv_le_contravar; lra. }
assert (H3 : y ^ 3 < y * (1 / 4503599627370496)).
{ replace (y ^ 3) with (y * (y * y)) by ring. apply Rmult_lt_compat_l; lra. }
assert (H5 : y ^ 5 < y ^ 3 * (1 / 4503599627370496)).
{ replace (y ^ 5) with (y ^ 3 * (y * y)) by ring.
  apply Rmult_lt_compat_l; [apply pow_lt; lra | exact Hyy]. }
assert (P3 : 0 < y ^ 3) by (apply pow_lt; lra).
split; lra.
Qed.

(** [y < atanh y < succ y] for [0 < y < 2^-26], as [y 2^-53 < ulp y]. *)
Lemma atanh_tiny_succ :
  forall y, 0 < y < bpow radix2 (-26) -> y < Ratanh y < succ64 y.
Proof.
intros y Hy. destruct (atanh_tiny_real y Hy) as [H1 H2]. split; [exact H1|].
rewrite succ_eq_pos by lra.
change (SpecFloat.fexp 53 1024) with (FLT_exp (-1074) 53).
assert (P : Prec_gt_0 53) by (unfold Prec_gt_0; lia).
pose proof (ulp_FLT_gt radix2 (-1074) 53 y) as H.
change (Z.opp 53) with (-53)%Z in H.
rewrite Rabs_pos_eq in H by lra. lra.
Qed.

Lemma atanh_tiny_rule :
  forall x (up : bool), is_finite x = true -> lt (fabs x) DyadicExp.tiny_hyp = true ->
  mpfr_round f64_format (rnd_of up) (Ratanh (B2R x)) (with_val (DyadicExp.away x up)).
Proof.
intros x up Fx Hx.
assert (Ft : is_finite DyadicExp.tiny_hyp = true) by (vm_compute; reflexivity).
apply fabs_lt_R in Hx; [| exact Fx | exact Ft]. rewrite hyp_lit_tiny in Hx.
assert (Ht : bpow radix2 (-26) < 1)
  by (change 1 with (bpow radix2 0); apply bpow_lt; lia).
assert (Hx1 : Rabs (B2R x) < 1) by lra.
destruct (away_bits x Fx Hx1) as (Fb & Ep & En).
assert (Gx : G (B2R x)) by exact (generic_format_B2R 53 1024 x).
assert (Fz : is_finite zero = true) by reflexivity.
unfold DyadicExp.away, eq, gt.
rewrite Beqb_correct by assumption. rewrite Bltb_correct by assumption.
change (B2R zero) with 0.
set (b := from_bits (to_bits x + 1)%Z) in *.
apply Rabs_def2 in Hx as [Hx2 Hx3].
destruct (Req_bool_spec (B2R x) 0) as [H0|H0].
{ (* [atanh 0 = 0]. *)
  cbn [orb]. apply rnd_exact; [exact Fx|]. rewrite H0. unfold Ratanh.
  replace ((1 + 0) / (1 - 0)) with 1 by field. rewrite ln_1. field. }
cbn [orb].
destruct (Rlt_bool_spec 0 (B2R x)) as [Hp|Hn].
- (* [x > 0]: [atanh x] lies between [x] and [succ x], the pattern after [x]. *)
  specialize (Ep Hp).
  destruct (atanh_tiny_succ (B2R x) ltac:(lra)) as [H1 H2].
  assert (R : forall u : bool,
    mpfr_round f64_format (rnd_of u) (Ratanh (B2R x)) (with_val (if u then b else x)))
    by (intros u; apply rnd_bracket; [exact Fx | exact Fb | exact Ep | lra]).
  destruct up; [exact (R true) | exact (R false)].
- (* [x < 0]: [atanh x = - atanh (- x)] lies between [- succ (- x) = pred x],
     the pattern after [x], and [x = succ (pred x)]. *)
  assert (Hneg : B2R x < 0) by lra.
  specialize (En Hneg).
  destruct (atanh_tiny_succ (- B2R x) ltac:(lra)) as [H1 H2].
  assert (Hs : Ratanh (B2R x) = - Ratanh (- B2R x)).
  { rewrite (Ratanh_odd (B2R x)) by lra. ring. }
  assert (Ex : B2R x = succ64 (B2R b)).
  { rewrite En, <- pred_opp, Ropp_involutive. symmetry.
    apply succ_pred; [typeclasses eauto | exact Gx]. }
  assert (R : forall u : bool,
    mpfr_round f64_format (rnd_of u) (Ratanh (B2R x)) (with_val (if u then x else b)))
    by (intros u; apply rnd_bracket; [exact Fb | exact Fx | exact Ex | lra]).
  destruct up; [exact (R true) | exact (R false)].
Qed.
