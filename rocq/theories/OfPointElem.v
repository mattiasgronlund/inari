(** * MPFR functions made of functions of [f64]s: one argument

    Each MPFR function of one number of [of_point p] satisfies the
    hypothesis of [Mpfr.v] at the exponent range of [f64] where the field
    of [p] satisfies its counterpart in [Contract.v]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Mpfr MpfrRound MpfrIdeal IdealRound IdealGetD
  Contract OfPointCore OfPoint.

Open Scope R_scope.

(** [fin f] gives [f] at every finite [f64]. *)
Lemma fin_finite :
  forall f (x : f64), is_finite x = true -> fin f x = Some (f (B2R x)).
Proof. intros f x Hx. unfold fin. rewrite Hx. reflexivity. Qed.

(** [lift1 F h], of a function [h] of [f64]s that computes [f] on [D] and
    an [F] that gives [f] at every finite [f64], is an MPFR function that
    computes [f] on [D] at the exponent range of [f64]. *)
Lemma lift1_correct :
  forall (F : f64 -> option R) D f (h : mpfr_rnd -> f64 -> f64),
  (forall x, is_finite x = true -> F x = Some (f (B2R x))) ->
  point_correct D f h -> mpfr_correct (-1073) 1024 D f (lift1 F h).
Proof.
intros F D f h HF Hh rnd x Hx HD. cbv beta zeta delta [lift1].
rewrite ideal_get_d_with_val, (HF x Hx).
apply lift_val_correct. exact (Hh rnd x Hx HD).
Qed.

(** The main clause of each [<f>_ok] for [lift1 (fin f) h]. *)
Lemma lift1_fin_correct :
  forall D f (h : mpfr_rnd -> f64 -> f64),
  point_correct D f h -> mpfr_correct (-1073) 1024 D f (lift1 (fin f) h).
Proof. intros D f h Hh. apply lift1_correct; [apply fin_finite | exact Hh]. Qed.

(** At an infinity, which [fin f] leaves out, [lift1 (fin f) h] is the
    result of [h] as an MPFR number. *)
Lemma lift1_fin_inf :
  forall f (h : mpfr_rnd -> f64 -> f64) rnd s,
  lift1 (fin f) h rnd (MInf s) = with_val (h rnd (B754_infinity s)).
Proof. intros f h rnd s. reflexivity. Qed.

(** At a finite [f64] [x] where [h] gives an infinity, [lift1 (fin f) h]
    is that infinity, whatever [f] is at [x]. *)
Lemma lift1_fin_to_inf :
  forall f (h : mpfr_rnd -> f64 -> f64) rnd v s,
  is_finite (ideal_get_d RNDD v) = true ->
  h rnd (ideal_get_d RNDD v) = B754_infinity s ->
  lift1 (fin f) h rnd v = MInf s.
Proof.
intros f h rnd v s Hx Hh. cbv beta zeta delta [lift1].
rewrite (fin_finite f _ Hx), Hh, lift_val_exact; [reflexivity|].
left. reflexivity.
Qed.

Theorem of_point_acos_ok :
  forall p, acos_c (p_acos p) -> acos_ok (-1073) 1024 (of_point p).
Proof. intros p Hc. exact (lift1_fin_correct _ _ _ Hc). Qed.

Theorem of_point_acosh_ok :
  forall p, acosh_c (p_acosh p) -> acosh_ok (-1073) 1024 (of_point p).
Proof.
intros p [Hc Hu]. split.
- exact (lift1_fin_correct _ _ _ Hc).
- cbn [mpfr_acosh of_point]. rewrite lift1_fin_inf, Hu. reflexivity.
Qed.

Theorem of_point_asin_ok :
  forall p, asin_c (p_asin p) -> asin_ok (-1073) 1024 (of_point p).
Proof. intros p Hc. exact (lift1_fin_correct _ _ _ Hc). Qed.

Theorem of_point_asinh_ok :
  forall p, asinh_c (p_asinh p) -> asinh_ok (-1073) 1024 (of_point p).
Proof.
intros p (Hc & Hd & Hu). split; [|split].
- exact (lift1_fin_correct _ _ _ Hc).
- cbn [mpfr_asinh of_point]. rewrite lift1_fin_inf, Hd. reflexivity.
- cbn [mpfr_asinh of_point]. rewrite lift1_fin_inf, Hu. reflexivity.
Qed.

(** [atan_val] gives [PI / 2] and [- (PI / 2)] at the infinities, so
    [lift_val] makes MPFR roundings of them of the roundings to [f64]s
    that [atan_c] assumes. *)
Theorem of_point_atan_ok :
  forall p, atan_c (p_atan p) -> atan_ok (-1073) 1024 (of_point p).
Proof.
intros p (Hc & Hd & Hu). split; [|split].
- apply lift1_correct; [|exact Hc].
  intros x Hx. destruct x as [s|s| |s m e B]; try discriminate; reflexivity.
- cbn [mpfr_atan of_point]. cbv beta zeta delta [lift1]. cbn [ideal_get_d atan_val].
  apply lift_val_correct. exact Hd.
- cbn [mpfr_atan of_point]. cbv beta zeta delta [lift1]. cbn [ideal_get_d atan_val].
  apply lift_val_correct. exact Hu.
Qed.

(** [MNum (-1)] and [MNum 1] convert to finite [f64]s, where [atanh_c]
    gives the infinities. *)
Theorem of_point_atanh_ok :
  forall p, atanh_c (p_atanh p) -> atanh_ok (-1073) 1024 (of_point p).
Proof.
intros p (Hc & Hd & Hu). split; [|split].
- exact (lift1_fin_correct _ _ _ Hc).
- cbn [mpfr_atanh of_point].
  destruct (ideal_get_d_m_one RNDD) as [Hf Hr].
  apply lift1_fin_to_inf; [exact Hf|]. exact (Hd _ Hf Hr).
- cbn [mpfr_atanh of_point].
  destruct (ideal_get_d_one RNDD) as [Hf Hr].
  apply lift1_fin_to_inf; [exact Hf|]. exact (Hu _ Hf Hr).
Qed.

Theorem of_point_cbrt_ok :
  forall p, cbrt_c (p_cbrt p) -> cbrt_ok (-1073) 1024 (of_point p).
Proof.
intros p (Hc & Hd & Hu). split; [|split].
- exact (lift1_fin_correct _ _ _ Hc).
- cbn [mpfr_cbrt of_point]. rewrite lift1_fin_inf, Hd. reflexivity.
- cbn [mpfr_cbrt of_point]. rewrite lift1_fin_inf, Hu. reflexivity.
Qed.

Theorem of_point_cos_ok :
  forall p, cos_c (p_cos p) -> cos_ok (-1073) 1024 (of_point p).
Proof. intros p Hc. exact (lift1_fin_correct _ _ _ Hc). Qed.

Theorem of_point_cosh_ok :
  forall p, cosh_c (p_cosh p) -> cosh_ok (-1073) 1024 (of_point p).
Proof.
intros p [Hc Hu]. split.
- exact (lift1_fin_correct _ _ _ Hc).
- intros s. cbn [mpfr_cosh of_point]. rewrite lift1_fin_inf, Hu. reflexivity.
Qed.

Theorem of_point_exp_ok :
  forall p, exp_c (p_exp p) -> exp_ok (-1073) 1024 (of_point p).
Proof.
intros p (Hc & [s Hd] & Hu). split; [|split].
- exact (lift1_fin_correct _ _ _ Hc).
- exists s. cbn [mpfr_exp of_point]. rewrite lift1_fin_inf, Hd. reflexivity.
- cbn [mpfr_exp of_point]. rewrite lift1_fin_inf, Hu. reflexivity.
Qed.

Theorem of_point_exp10_ok :
  forall p, exp10_c (p_exp10 p) -> exp10_ok (-1073) 1024 (of_point p).
Proof.
intros p (Hc & [s Hd] & Hu). split; [|split].
- exact (lift1_fin_correct _ _ _ Hc).
- exists s. cbn [mpfr_exp10 of_point]. rewrite lift1_fin_inf, Hd. reflexivity.
- cbn [mpfr_exp10 of_point]. rewrite lift1_fin_inf, Hu. reflexivity.
Qed.

Theorem of_point_exp2_ok :
  forall p, exp2_c (p_exp2 p) -> exp2_ok (-1073) 1024 (of_point p).
Proof.
intros p (Hc & [s Hd] & Hu). split; [|split].
- exact (lift1_fin_correct _ _ _ Hc).
- exists s. cbn [mpfr_exp2 of_point]. rewrite lift1_fin_inf, Hd. reflexivity.
- cbn [mpfr_exp2 of_point]. rewrite lift1_fin_inf, Hu. reflexivity.
Qed.

(** A zero converts to a zero, which is finite, so [lift_val] gets the
    infinity that [ln_c] gives there and keeps it ([lift_val_exact]); the
    same for [log10] and [log2]. *)
Theorem of_point_ln_ok :
  forall p, ln_c (p_ln p) -> ln_ok (-1073) 1024 (of_point p).
Proof.
intros p (Hc & Hd & Hu). split; [|split].
- exact (lift1_fin_correct _ _ _ Hc).
- intros s. cbn [mpfr_log of_point].
  apply lift1_fin_to_inf; [reflexivity|]. exact (Hd s).
- cbn [mpfr_log of_point]. rewrite lift1_fin_inf, Hu. reflexivity.
Qed.

Theorem of_point_log10_ok :
  forall p, log10_c (p_log10 p) -> log10_ok (-1073) 1024 (of_point p).
Proof.
intros p (Hc & Hd & Hu). split; [|split].
- exact (lift1_fin_correct _ _ _ Hc).
- intros s. cbn [mpfr_log10 of_point].
  apply lift1_fin_to_inf; [reflexivity|]. exact (Hd s).
- cbn [mpfr_log10 of_point]. rewrite lift1_fin_inf, Hu. reflexivity.
Qed.

Theorem of_point_log2_ok :
  forall p, log2_c (p_log2 p) -> log2_ok (-1073) 1024 (of_point p).
Proof.
intros p (Hc & Hd & Hu). split; [|split].
- exact (lift1_fin_correct _ _ _ Hc).
- intros s. cbn [mpfr_log2 of_point].
  apply lift1_fin_to_inf; [reflexivity|]. exact (Hd s).
- cbn [mpfr_log2 of_point]. rewrite lift1_fin_inf, Hu. reflexivity.
Qed.

Theorem of_point_sin_ok :
  forall p, sin_c (p_sin p) -> sin_ok (-1073) 1024 (of_point p).
Proof. intros p Hc. exact (lift1_fin_correct _ _ _ Hc). Qed.

Theorem of_point_sinh_ok :
  forall p, sinh_c (p_sinh p) -> sinh_ok (-1073) 1024 (of_point p).
Proof.
intros p (Hc & Hd & Hu). split; [|split].
- exact (lift1_fin_correct _ _ _ Hc).
- cbn [mpfr_sinh of_point]. rewrite lift1_fin_inf, Hd. reflexivity.
- cbn [mpfr_sinh of_point]. rewrite lift1_fin_inf, Hu. reflexivity.
Qed.

Theorem of_point_tan_ok :
  forall p, tan_c (p_tan p) -> tan_ok (-1073) 1024 (of_point p).
Proof. intros p Hc. exact (lift1_fin_correct _ _ _ Hc). Qed.

(** The roundings of -1 and 1 to [f64]s that [tanh_c] gives at the
    infinities are the [f64]s -1 and 1 ([with_val_round_one]). *)
Theorem of_point_tanh_ok :
  forall p, tanh_c (p_tanh p) -> tanh_ok (-1073) 1024 (of_point p).
Proof.
intros p (Hc & Hd & Hu). split; [|split].
- exact (lift1_fin_correct _ _ _ Hc).
- cbn [mpfr_tanh of_point]. rewrite lift1_fin_inf.
  exact (with_val_round_one _ _ _ (or_intror eq_refl) Hd).
- cbn [mpfr_tanh of_point]. rewrite lift1_fin_inf.
  exact (with_val_round_one _ _ _ (or_introl eq_refl) Hu).
Qed.
