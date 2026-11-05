(** * A record [point] whose exponential family is the dyadic kernel's

    The fields of [point] are total functions, and the functions of
    [DyadicExp] in [Model.v] return [None] where the Rust panics: at the
    cap of Ziv's strategy, at an [assert!], or at a panic of an operation
    of the kernel. [k_exp] and the others are the kernel's result where it
    returns, and the result rounded by definition ([round_f64] of
    [MpfrIdeal.v]) where the Rust panics, so the theorems below say
    nothing about the calls that panic: they cover the calls that return.
    That the loop ends before its cap is not proved. [kernel_point p] is
    [p] with these six fields. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr MpfrRound MpfrIdeal IdealGetD Elem Cosh
  Contract OfPointCore OfPoint OfPointElem PointTheorems DyExp DyHyp.

Open Scope R_scope.

Definition up_of (rnd : mpfr_rnd) : bool := match rnd with RNDD => false | RNDU => true end.

(** The field of the function [dir] of [DyadicExp] for the real function [f]. *)
Definition kernel_field (dir : f64 -> bool -> option f64) (f : R -> R) (rnd : mpfr_rnd) (x : f64)
  : f64 :=
  match dir x (up_of rnd) with Some v => v | None => round_f64 rnd (f (B2R x)) end.

Definition k_exp := kernel_field DyadicExp.exp_dir exp.
Definition k_exp2 := kernel_field DyadicExp.exp2_dir Rexp2.
Definition k_exp10 := kernel_field DyadicExp.exp10_dir Rexp10.
Definition k_sinh := kernel_field DyadicExp.sinh_dir sinh.
Definition k_cosh := kernel_field DyadicExp.cosh_dir cosh.
Definition k_tanh := kernel_field DyadicExp.tanh_dir tanh.

Definition kernel_point (p : point) : point := {|
  p_acos := p_acos p;
  p_acosh := p_acosh p;
  p_asin := p_asin p;
  p_asinh := p_asinh p;
  p_atan := p_atan p;
  p_atan2 := p_atan2 p;
  p_atanh := p_atanh p;
  p_cos := p_cos p;
  p_cosh := k_cosh;
  p_exp := k_exp;
  p_exp10 := k_exp10;
  p_exp2 := k_exp2;
  p_ln := p_ln p;
  p_log10 := p_log10 p;
  p_log2 := p_log2 p;
  p_pow := p_pow p;
  p_pown := p_pown p;
  p_sin := p_sin p;
  p_sinh := k_sinh;
  p_tan := p_tan p;
  p_tanh := k_tanh
|}.

(** ** The fields at finite arguments

    Where [dir] returns, its theorem gives the rounding in the direction
    [up_of rnd]; where it does not, [round_f64_correct] does. *)
Lemma kernel_field_correct :
  forall (dir : f64 -> bool -> option f64) (f : R -> R),
  (forall x up v, is_finite x = true -> dir x up = Some v ->
   mpfr_round f64_format (if up then RNDU else RNDD) (f (B2R x)) (with_val v)) ->
  point_correct real_dom f (kernel_field dir f).
Proof.
intros dir f Hd rnd x Fx _. unfold kernel_field.
destruct (dir x (up_of rnd)) as [v|] eqn:E.
- pose proof (Hd x (up_of rnd) v Fx E) as H. destruct rnd; exact H.
- apply round_f64_correct.
Qed.

(** The [f64]s 1 and -1 of [DyadicExp] are the reals 1 and -1, so they
    round 1 and -1 to themselves. *)
Lemma one_round : forall rnd, mpfr_round f64_format rnd 1 (with_val DyadicExp.one).
Proof.
intros rnd.
assert (H1 : B2R DyadicExp.one = 1).
{ rewrite <- SF2R_B2SF.
  replace (B2SF DyadicExp.one) with (SpecFloat.S754_finite false 4503599627370496 (-52))
    by (vm_compute; reflexivity).
  cbn [SF2R cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
  change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity. }
rewrite with_val_finite by (try (rewrite H1; lra); vm_compute; reflexivity). rewrite H1.
assert (He : (-1074 <= 0 < 1024)%Z) by lia.
apply mpfr_round_exact; [lra | exact (proj1 (f64_format_bpow 0 He))].
Qed.

Lemma m_one_round : forall rnd, mpfr_round f64_format rnd (-1) (with_val DyadicExp.m_one).
Proof.
intros rnd.
assert (H1 : B2R DyadicExp.m_one = -1).
{ rewrite <- SF2R_B2SF.
  replace (B2SF DyadicExp.m_one) with (SpecFloat.S754_finite true 4503599627370496 (-52))
    by (vm_compute; reflexivity).
  cbn [SF2R cond_Zopp]. unfold F2R; cbn [Fnum Fexp]. rewrite opp_IZR.
  change (IZR 4503599627370496) with (bpow radix2 52).
  rewrite <- Ropp_mult_distr_l, <- bpow_plus. reflexivity. }
rewrite with_val_finite by (try (rewrite H1; lra); vm_compute; reflexivity). rewrite H1.
assert (He : (-1074 <= 0 < 1024)%Z) by lia.
apply mpfr_round_exact; [lra | exact (proj2 (f64_format_bpow 0 He))].
Qed.

(** ** The contracts *)

Theorem k_exp_c : exp_c k_exp.
Proof.
split; [exact (kernel_field_correct _ _ exp_dir_correct) | split].
- exists false. unfold k_exp, kernel_field. cbn [up_of].
  replace (DyadicExp.exp_dir (B754_infinity true) false) with (Some (B754_zero false : f64))
    by (vm_compute; reflexivity).
  reflexivity.
- unfold k_exp, kernel_field. cbn [up_of].
  replace (DyadicExp.exp_dir (B754_infinity false) true) with (Some (B754_infinity false : f64))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Theorem k_exp2_c : exp2_c k_exp2.
Proof.
split; [exact (kernel_field_correct _ _ exp2_dir_correct) | split].
- exists false. unfold k_exp2, kernel_field. cbn [up_of].
  replace (DyadicExp.exp2_dir (B754_infinity true) false) with (Some (B754_zero false : f64))
    by (vm_compute; reflexivity).
  reflexivity.
- unfold k_exp2, kernel_field. cbn [up_of].
  replace (DyadicExp.exp2_dir (B754_infinity false) true) with (Some (B754_infinity false : f64))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Theorem k_exp10_c : exp10_c k_exp10.
Proof.
split; [exact (kernel_field_correct _ _ exp10_dir_correct) | split].
- exists false. unfold k_exp10, kernel_field. cbn [up_of].
  replace (DyadicExp.exp10_dir (B754_infinity true) false) with (Some (B754_zero false : f64))
    by (vm_compute; reflexivity).
  reflexivity.
- unfold k_exp10, kernel_field. cbn [up_of].
  replace (DyadicExp.exp10_dir (B754_infinity false) true) with (Some (B754_infinity false : f64))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Theorem k_sinh_c : sinh_c k_sinh.
Proof.
split; [exact (kernel_field_correct _ _ sinh_dir_correct) | split].
- unfold k_sinh, kernel_field. cbn [up_of].
  replace (DyadicExp.sinh_dir (B754_infinity true) false) with (Some (B754_infinity true : f64))
    by (vm_compute; reflexivity).
  reflexivity.
- unfold k_sinh, kernel_field. cbn [up_of].
  replace (DyadicExp.sinh_dir (B754_infinity false) true) with (Some (B754_infinity false : f64))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Theorem k_cosh_c : cosh_c k_cosh.
Proof.
split; [exact (kernel_field_correct _ _ cosh_dir_correct) |].
intros s. unfold k_cosh, kernel_field. cbn [up_of].
replace (DyadicExp.cosh_dir (B754_infinity s) true) with (Some (B754_infinity false : f64))
  by (destruct s; vm_compute; reflexivity).
reflexivity.
Qed.

Theorem k_tanh_c : tanh_c k_tanh.
Proof.
split; [exact (kernel_field_correct _ _ tanh_dir_correct) | split].
- unfold k_tanh, kernel_field. cbn [up_of].
  replace (DyadicExp.tanh_dir (B754_infinity true) false) with (Some DyadicExp.m_one)
    by (vm_compute; reflexivity).
  apply m_one_round.
- unfold k_tanh, kernel_field. cbn [up_of].
  replace (DyadicExp.tanh_dir (B754_infinity false) true) with (Some DyadicExp.one)
    by (vm_compute; reflexivity).
  apply one_round.
Qed.

Theorem kernel_exp_correct :
  forall p x, valid x -> is_tightest (image_dom real_dom exp x) (Interval.exp (kernel_point p) x).
Proof.
intros p x Hx. exact (exp_correct_point (kernel_point p) k_exp_c x Hx).
Qed.

Theorem kernel_exp2_correct :
  forall p x, valid x ->
  is_tightest (image_dom real_dom Rexp2 x) (Interval.exp2 (kernel_point p) x).
Proof.
intros p x Hx. exact (exp2_correct_point (kernel_point p) k_exp2_c x Hx).
Qed.

Theorem kernel_exp10_correct :
  forall p x, valid x ->
  is_tightest (image_dom real_dom Rexp10 x) (Interval.exp10 (kernel_point p) x).
Proof.
intros p x Hx. exact (exp10_correct_point (kernel_point p) k_exp10_c x Hx).
Qed.

Theorem kernel_sinh_correct :
  forall p x, valid x ->
  is_tightest (image_dom real_dom sinh x) (Interval.sinh (kernel_point p) x).
Proof.
intros p x Hx. exact (sinh_correct_point (kernel_point p) k_sinh_c x Hx).
Qed.

Theorem kernel_cosh_correct :
  forall p first x, valid x ->
  is_tightest (image_dom real_dom cosh x) (Interval.cosh (kernel_point p) first x).
Proof.
intros p first x Hx. exact (cosh_correct_point (kernel_point p) k_cosh_c first x Hx).
Qed.

Theorem kernel_tanh_correct :
  forall p x, valid x ->
  is_tightest (image_dom real_dom tanh x) (Interval.tanh (kernel_point p) x).
Proof.
intros p x Hx. exact (tanh_correct_point (kernel_point p) k_tanh_c x Hx).
Qed.
