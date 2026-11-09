(** * MPFR meets the contract

    The record [mpfr_point m] that [src/mpfr_calls/mpfr.rs] makes of the
    MPFR functions [m] satisfies each part of [Contract.v]: each [<f>_c]
    holds where [m] satisfies [get_d_ok] and the hypothesis [<f>_ok] of
    [Mpfr.v], at an exponent range with [range_ok]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Mpfr MpfrRound PowMpfr Atan2Mpfr Contract.

Open Scope R_scope.

Theorem mpfr_acos_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> acos_ok emin emax m ->
  acos_c (p_acos (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_acos mpfr_point].
unfold acos_ok in Hok. unfold acos_c, point_correct.
exact (mpfr_fn_correct emin emax m _ _ _ Hr Hget Hok).
Qed.

Theorem mpfr_acosh_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> acosh_ok emin emax m ->
  acosh_c (p_acosh (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_acosh mpfr_point].
destruct Hok as (Hc & H1). unfold acosh_c, point_correct. split.
- exact (mpfr_fn_correct emin emax m _ _ _ Hr Hget Hc).
- exact (mpfr_fn_inf emin emax m _ _ _ _ Hget H1).
Qed.

Theorem mpfr_asin_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> asin_ok emin emax m ->
  asin_c (p_asin (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_asin mpfr_point].
unfold asin_ok in Hok. unfold asin_c, point_correct.
exact (mpfr_fn_correct emin emax m _ _ _ Hr Hget Hok).
Qed.

Theorem mpfr_asinh_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> asinh_ok emin emax m ->
  asinh_c (p_asinh (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_asinh mpfr_point].
destruct Hok as (Hc & H1 & H2). unfold asinh_c, point_correct. split; [|split].
- exact (mpfr_fn_correct emin emax m _ _ _ Hr Hget Hc).
- exact (mpfr_fn_inf emin emax m _ _ _ _ Hget H1).
- exact (mpfr_fn_inf emin emax m _ _ _ _ Hget H2).
Qed.

Theorem mpfr_atan_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> atan_ok emin emax m ->
  atan_c (p_atan (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_atan mpfr_point].
destruct Hok as (Hc & H1 & H2). unfold atan_c, point_correct. split; [|split].
- exact (mpfr_fn_correct emin emax m _ _ _ Hr Hget Hc).
- (* [-PI/2] rounded down to an MPFR number, and then to an [f64]. *)
  exact (mpfr_fn_round emin emax m RNDD _ _ Hr Hget H1).
- exact (mpfr_fn_round emin emax m RNDU _ _ Hr Hget H2).
Qed.

Theorem mpfr_atan2_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  atan2_c (p_atan2 (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_atan2 mpfr_point].
destruct Hok as (Hc & H1 & H2 & H3 & H4 & H5 & H6 & H7).
pose proof Hget as (_ & Hzero & _).
unfold atan2_c, point_correct2.
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- intros rnd y x Fy Fx Hd. unfold mpfr_fn2.
  exact (mpfr_fn_round emin emax m rnd _ _ Hr Hget (Hc rnd y x Fy Fx Hd)).
- intros rnd y Fy Hy. unfold mpfr_fn2. cbn [with_val].
  destruct (H1 rnd y Fy Hy) as (s & ->). exact (Hzero rnd s).
- intros rnd y Fy Hy. unfold mpfr_fn2. cbn [with_val].
  destruct (H2 rnd y Fy Hy) as (s & ->). exact (Hzero rnd s).
- intros rnd s. unfold mpfr_fn2. cbn [with_val].
  destruct (H3 rnd s) as (s' & ->). exact (Hzero rnd s').
- intros rnd y Fy Hy. unfold mpfr_fn2.
  exact (mpfr_fn_round emin emax m rnd _ _ Hr Hget (H4 rnd y Fy Hy)).
- intros rnd y Fy Hy. unfold mpfr_fn2.
  exact (mpfr_fn_round emin emax m rnd _ _ Hr Hget (H5 rnd y Fy Hy)).
- intros rnd x Fx. unfold mpfr_fn2.
  exact (mpfr_fn_round emin emax m rnd _ _ Hr Hget (H6 rnd x Fx)).
- intros rnd x Fx. unfold mpfr_fn2.
  exact (mpfr_fn_round emin emax m rnd _ _ Hr Hget (H7 rnd x Fx)).
Qed.

Theorem mpfr_atanh_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> atanh_ok emin emax m ->
  atanh_c (p_atanh (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_atanh mpfr_point].
destruct Hok as (Hc & H1 & H2). destruct Hget as (Hnum & Hzero & Hinf).
unfold atanh_c, point_correct. split; [|split].
- exact (mpfr_fn_correct emin emax m _ _ _ Hr (conj Hnum (conj Hzero Hinf)) Hc).
- (* A finite [f64] whose real is [-1] is the MPFR number [-1]. *)
  intros x Fx Ex. unfold mpfr_fn.
  rewrite (with_val_finite x Fx) by lra. rewrite Ex, H1. apply Hinf.
- intros x Fx Ex. unfold mpfr_fn.
  rewrite (with_val_finite x Fx) by lra. rewrite Ex, H2. apply Hinf.
Qed.

Theorem mpfr_cbrt_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> cbrt_ok emin emax m ->
  cbrt_c (p_cbrt (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_cbrt mpfr_point].
destruct Hok as (Hc & H1 & H2). unfold cbrt_c, point_correct. split; [|split].
- exact (mpfr_fn_correct emin emax m _ _ _ Hr Hget Hc).
- exact (mpfr_fn_inf emin emax m _ _ _ _ Hget H1).
- exact (mpfr_fn_inf emin emax m _ _ _ _ Hget H2).
Qed.

Theorem mpfr_cos_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> cos_ok emin emax m ->
  cos_c (p_cos (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_cos mpfr_point].
unfold cos_ok in Hok. unfold cos_c, point_correct.
exact (mpfr_fn_correct emin emax m _ _ _ Hr Hget Hok).
Qed.

Theorem mpfr_cosh_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> cosh_ok emin emax m ->
  cosh_c (p_cosh (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_cosh mpfr_point].
destruct Hok as (Hc & H1). unfold cosh_c, point_correct. split.
- exact (mpfr_fn_correct emin emax m _ _ _ Hr Hget Hc).
- intros s. exact (mpfr_fn_inf emin emax m _ _ _ _ Hget (H1 s)).
Qed.

Theorem mpfr_exp_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> exp_ok emin emax m ->
  exp_c (p_exp (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_exp mpfr_point].
destruct Hok as (Hc & (s & H1) & H2). pose proof Hget as (_ & Hzero & _).
unfold exp_c, point_correct. split; [|split].
- exact (mpfr_fn_correct emin emax m _ _ _ Hr Hget Hc).
- (* MPFR's zero converts to a zero. *)
  unfold mpfr_fn. cbn [with_val]. rewrite H1. exact (Hzero RNDD s).
- exact (mpfr_fn_inf emin emax m _ _ _ _ Hget H2).
Qed.

Theorem mpfr_exp10_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> exp10_ok emin emax m ->
  exp10_c (p_exp10 (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_exp10 mpfr_point].
destruct Hok as (Hc & (s & H1) & H2). pose proof Hget as (_ & Hzero & _).
unfold exp10_c, point_correct. split; [|split].
- exact (mpfr_fn_correct emin emax m _ _ _ Hr Hget Hc).
- (* MPFR's zero converts to a zero. *)
  unfold mpfr_fn. cbn [with_val]. rewrite H1. exact (Hzero RNDD s).
- exact (mpfr_fn_inf emin emax m _ _ _ _ Hget H2).
Qed.

Theorem mpfr_exp2_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> exp2_ok emin emax m ->
  exp2_c (p_exp2 (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_exp2 mpfr_point].
destruct Hok as (Hc & (s & H1) & H2). pose proof Hget as (_ & Hzero & _).
unfold exp2_c, point_correct. split; [|split].
- exact (mpfr_fn_correct emin emax m _ _ _ Hr Hget Hc).
- (* MPFR's zero converts to a zero. *)
  unfold mpfr_fn. cbn [with_val]. rewrite H1. exact (Hzero RNDD s).
- exact (mpfr_fn_inf emin emax m _ _ _ _ Hget H2).
Qed.

Theorem mpfr_hypot_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> hypot_ok emin emax m ->
  hypot_c (p_hypot (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_hypot mpfr_point].
destruct Hok as (Hc & H1 & H2). pose proof Hget as (_ & _ & Hinf).
unfold hypot_c, point_correct2. split; [|split].
- intros rnd x y Fx Fy Hd. unfold mpfr_fn2.
  exact (mpfr_fn_round emin emax m rnd _ _ Hr Hget (Hc rnd x y Fx Fy Hd)).
- (* An infinity is MPFR's infinity, of the same sign. *)
  intros y. unfold mpfr_fn2. cbn [with_val]. rewrite H1. apply Hinf.
- intros x. unfold mpfr_fn2. cbn [with_val]. rewrite H2. apply Hinf.
Qed.

Theorem mpfr_ln_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> ln_ok emin emax m ->
  ln_c (p_ln (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_ln mpfr_point].
destruct Hok as (Hc & H1 & H2). pose proof Hget as (_ & _ & Hinf).
unfold ln_c, point_correct. split; [|split].
- exact (mpfr_fn_correct emin emax m _ _ _ Hr Hget Hc).
- (* A zero is MPFR's zero, of the same sign. *)
  intros s. unfold mpfr_fn. cbn [with_val]. rewrite H1. apply Hinf.
- exact (mpfr_fn_inf emin emax m _ _ _ _ Hget H2).
Qed.

Theorem mpfr_log10_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> log10_ok emin emax m ->
  log10_c (p_log10 (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_log10 mpfr_point].
destruct Hok as (Hc & H1 & H2). pose proof Hget as (_ & _ & Hinf).
unfold log10_c, point_correct. split; [|split].
- exact (mpfr_fn_correct emin emax m _ _ _ Hr Hget Hc).
- (* A zero is MPFR's zero, of the same sign. *)
  intros s. unfold mpfr_fn. cbn [with_val]. rewrite H1. apply Hinf.
- exact (mpfr_fn_inf emin emax m _ _ _ _ Hget H2).
Qed.

Theorem mpfr_log2_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> log2_ok emin emax m ->
  log2_c (p_log2 (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_log2 mpfr_point].
destruct Hok as (Hc & H1 & H2). pose proof Hget as (_ & _ & Hinf).
unfold log2_c, point_correct. split; [|split].
- exact (mpfr_fn_correct emin emax m _ _ _ Hr Hget Hc).
- (* A zero is MPFR's zero, of the same sign. *)
  intros s. unfold mpfr_fn. cbn [with_val]. rewrite H1. apply Hinf.
- exact (mpfr_fn_inf emin emax m _ _ _ _ Hget H2).
Qed.

Theorem mpfr_pow_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  pow_c (p_pow (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_pow mpfr_point].
pose proof Hok as
  (Hc & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14).
pose proof Hget as (_ & Hzero & Hinf).
unfold pow_c, point_correct2.
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split;
  [|split; [|split; [|split; [|split]]]]]]]]]]]]].
- exact (pow_fin emin emax m Hr Hget Hok).
- intros rnd y Fy Hy. exact (pow_zero_neg emin emax m Hget Hok rnd y (or_introl (conj Fy Hy))).
- intros rnd. exact (pow_zero_neg emin emax m Hget Hok rnd _ (or_intror eq_refl)).
- (* MPFR's zero converts to a zero, here and below. *)
  intros rnd. unfold mpfr_fn2. cbn [with_val].
  destruct (H3 rnd) as (s & ->). exact (Hzero rnd s).
- exact (pow_zero_zero emin emax m Hr Hget Hok).
- exact (pow_pinf_zero emin emax m Hr Hget Hok).
- exact (pow_one_inf emin emax m Hr Hget Hok).
- exact (pow_lt1_ninf emin emax m Hget Hok).
- intros rnd x Fx Hx. unfold mpfr_fn2. cbn [with_val].
  destruct (H8 rnd x Fx Hx) as (s & ->). exact (Hzero rnd s).
- intros rnd x Fx Hx. unfold mpfr_fn2. cbn [with_val].
  destruct (H9 rnd x Fx Hx) as (s & ->). exact (Hzero rnd s).
- exact (pow_gt1_pinf emin emax m Hget Hok).
- intros rnd y Fy Hy. unfold mpfr_fn2. cbn [with_val].
  destruct (H11 rnd y Fy Hy) as (s & ->). exact (Hzero rnd s).
- intros rnd. unfold mpfr_fn2. cbn [with_val].
  destruct (H12 rnd) as (s & ->). exact (Hzero rnd s).
- intros rnd y Fy Hy. exact (pow_pinf_pos emin emax m Hget Hok rnd y (or_introl (conj Fy Hy))).
- intros rnd. exact (pow_pinf_pos emin emax m Hget Hok rnd _ (or_intror eq_refl)).
Qed.

Theorem mpfr_pown_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pown_ok emin emax m ->
  pown_c (p_pown (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_pown mpfr_point].
pose proof Hok as (Pc & P1 & P2 & P3 & P4 & P5 & P6 & P7).
pose proof Hget as (_ & Hzero & _).
unfold pown_c.
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- exact (pown_fin emin emax m Hr Hget Hok).
- exact (pown_zero_neg_even emin emax m Hget Hok).
- exact (pown_zero_neg_odd emin emax m Hget Hok).
- (* MPFR's zero converts to a zero, here and below. *)
  intros rnd n Hn Hneg. unfold mpfr_fn_si. cbn [with_val].
  destruct (P3 rnd n Hn Hneg) as (s & ->). exact (Hzero rnd s).
- exact (pown_pinf_0 emin emax m Hr Hget Hok).
- exact (pown_pinf_pos emin emax m Hget Hok).
- intros rnd n Hn Hneg Ho. unfold mpfr_fn_si. cbn [with_val].
  destruct (P6 rnd n Hn Hneg Ho) as (s & ->). exact (Hzero rnd s).
- exact (pown_ninf_pos_odd emin emax m Hget Hok).
Qed.

Theorem mpfr_sin_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> sin_ok emin emax m ->
  sin_c (p_sin (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_sin mpfr_point].
unfold sin_ok in Hok. unfold sin_c, point_correct.
exact (mpfr_fn_correct emin emax m _ _ _ Hr Hget Hok).
Qed.

Theorem mpfr_sinh_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> sinh_ok emin emax m ->
  sinh_c (p_sinh (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_sinh mpfr_point].
destruct Hok as (Hc & H1 & H2). unfold sinh_c, point_correct. split; [|split].
- exact (mpfr_fn_correct emin emax m _ _ _ Hr Hget Hc).
- exact (mpfr_fn_inf emin emax m _ _ _ _ Hget H1).
- exact (mpfr_fn_inf emin emax m _ _ _ _ Hget H2).
Qed.

Theorem mpfr_tan_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> tan_ok emin emax m ->
  tan_c (p_tan (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_tan mpfr_point].
unfold tan_ok in Hok. unfold tan_c, point_correct.
exact (mpfr_fn_correct emin emax m _ _ _ Hr Hget Hok).
Qed.

Theorem mpfr_tanh_c :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> tanh_ok emin emax m ->
  tanh_c (p_tanh (mpfr_point m)).
Proof.
intros emin emax m Hr Hget Hok. cbn [p_tanh mpfr_point].
destruct Hok as (Hc & H1 & H2). unfold tanh_c, point_correct.
destruct (mpfr_format_1 emin emax Hr) as (F1 & Fm1).
split; [|split].
- exact (mpfr_fn_correct emin emax m _ _ _ Hr Hget Hc).
- (* [-1] is an MPFR number, which [mpfr_get_d] rounds to [-1]. *)
  unfold mpfr_fn. cbn [with_val]. rewrite H1.
  apply (mpfr_fn_round emin emax m RNDD _ _ Hr Hget).
  apply mpfr_round_exact; [lra | exact Fm1].
- unfold mpfr_fn. cbn [with_val]. rewrite H2.
  apply (mpfr_fn_round emin emax m RNDU _ _ Hr Hget).
  apply mpfr_round_exact; [lra | exact F1].
Qed.
