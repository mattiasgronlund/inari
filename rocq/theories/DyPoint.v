(** * A record [point] whose exponentials and logarithms are the dyadic kernel's

    The fields of [point] are total functions, and the functions of
    [DyadicExp] and [DyadicLog] in [Model.v] return [None] where the Rust
    panics: at the cap of Ziv's strategy, at an [assert!], or at a panic
    of an operation of the kernel. [k_exp], [k_ln] and the others are the
    kernel's result where it returns, and the result rounded by definition
    ([round_f64] of [MpfrIdeal.v]) where the Rust panics, so the theorems
    below say nothing about the calls that panic: they cover the calls
    that return. That the loop ends before its cap is not proved.
    [kernel_point p] is [p] with these twelve fields. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr MpfrRound MpfrIdeal IdealGetD Elem Cosh
  Atanh Contract OfPointCore OfPoint OfPointElem PointTheorems DyExp DyHyp DyLog DyLogHyp.

Open Scope R_scope.

Definition up_of (rnd : mpfr_rnd) : bool := match rnd with RNDD => false | RNDU => true end.

(** The field of the function [dir] of [DyadicExp] or [DyadicLog] for the
    real function [f]. *)
Definition kernel_field (dir : f64 -> bool -> option f64) (f : R -> R) (rnd : mpfr_rnd) (x : f64)
  : f64 :=
  match dir x (up_of rnd) with Some v => v | None => round_f64 rnd (f (B2R x)) end.

Definition k_exp := kernel_field DyadicExp.exp_dir exp.
Definition k_exp2 := kernel_field DyadicExp.exp2_dir Rexp2.
Definition k_exp10 := kernel_field DyadicExp.exp10_dir Rexp10.
Definition k_sinh := kernel_field DyadicExp.sinh_dir sinh.
Definition k_cosh := kernel_field DyadicExp.cosh_dir cosh.
Definition k_tanh := kernel_field DyadicExp.tanh_dir tanh.
Definition k_ln := kernel_field DyadicLog.ln_dir ln.
Definition k_log2 := kernel_field DyadicLog.log2_dir Rlog2.
Definition k_log10 := kernel_field DyadicLog.log10_dir Rlog10.
Definition k_asinh := kernel_field DyadicLog.asinh_dir arcsinh.
Definition k_acosh := kernel_field DyadicLog.acosh_dir Racosh.
Definition k_atanh := kernel_field DyadicLog.atanh_dir Ratanh.

Definition kernel_point (p : point) : point := {|
  p_acos := p_acos p;
  p_acosh := k_acosh;
  p_asin := p_asin p;
  p_asinh := k_asinh;
  p_atan := p_atan p;
  p_atan2 := p_atan2 p;
  p_atanh := k_atanh;
  p_cos := p_cos p;
  p_cosh := k_cosh;
  p_exp := k_exp;
  p_exp10 := k_exp10;
  p_exp2 := k_exp2;
  p_ln := k_ln;
  p_log10 := k_log10;
  p_log2 := k_log2;
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

(** The same for a function [f] of domain [D], whose [dir] is proved for
    the finite arguments in [D]. *)
Lemma kernel_field_correct_dom :
  forall (D : R -> Prop) (dir : f64 -> bool -> option f64) (f : R -> R),
  (forall x up v, is_finite x = true -> D (B2R x) -> dir x up = Some v ->
   mpfr_round f64_format (if up then RNDU else RNDD) (f (B2R x)) (with_val v)) ->
  point_correct D f (kernel_field dir f).
Proof.
intros D dir f Hd rnd x Fx Dx. unfold kernel_field.
destruct (dir x (up_of rnd)) as [v|] eqn:E.
- pose proof (Hd x (up_of rnd) v Fx Dx E) as H. destruct rnd; exact H.
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

Theorem k_ln_c : ln_c k_ln.
Proof.
split; [exact (kernel_field_correct_dom _ _ _ ln_dir_correct) | split].
- intros s. unfold k_ln, kernel_field. cbn [up_of].
  replace (DyadicLog.ln_dir (B754_zero s) false) with (Some (B754_infinity true : f64))
    by (destruct s; vm_compute; reflexivity).
  reflexivity.
- unfold k_ln, kernel_field. cbn [up_of].
  replace (DyadicLog.ln_dir (B754_infinity false) true) with (Some (B754_infinity false : f64))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Theorem k_log2_c : log2_c k_log2.
Proof.
split; [exact (kernel_field_correct_dom _ _ _ log2_dir_correct) | split].
- intros s. unfold k_log2, kernel_field. cbn [up_of].
  replace (DyadicLog.log2_dir (B754_zero s) false) with (Some (B754_infinity true : f64))
    by (destruct s; vm_compute; reflexivity).
  reflexivity.
- unfold k_log2, kernel_field. cbn [up_of].
  replace (DyadicLog.log2_dir (B754_infinity false) true) with (Some (B754_infinity false : f64))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Theorem k_log10_c : log10_c k_log10.
Proof.
split; [exact (kernel_field_correct_dom _ _ _ log10_dir_correct) | split].
- intros s. unfold k_log10, kernel_field. cbn [up_of].
  replace (DyadicLog.log10_dir (B754_zero s) false) with (Some (B754_infinity true : f64))
    by (destruct s; vm_compute; reflexivity).
  reflexivity.
- unfold k_log10, kernel_field. cbn [up_of].
  replace (DyadicLog.log10_dir (B754_infinity false) true) with (Some (B754_infinity false : f64))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Theorem k_asinh_c : asinh_c k_asinh.
Proof.
split; [exact (kernel_field_correct _ _ asinh_dir_correct) | split].
- unfold k_asinh, kernel_field. cbn [up_of].
  replace (DyadicLog.asinh_dir (B754_infinity true) false) with (Some (B754_infinity true : f64))
    by (vm_compute; reflexivity).
  reflexivity.
- unfold k_asinh, kernel_field. cbn [up_of].
  replace (DyadicLog.asinh_dir (B754_infinity false) true) with (Some (B754_infinity false : f64))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Theorem k_acosh_c : acosh_c k_acosh.
Proof.
split; [exact (kernel_field_correct_dom _ _ _ acosh_dir_correct) |].
unfold k_acosh, kernel_field. cbn [up_of].
replace (DyadicLog.acosh_dir (B754_infinity false) true) with (Some (B754_infinity false : f64))
  by (vm_compute; reflexivity).
reflexivity.
Qed.

(** A finite [f64] of value -1 or 1 is [DyadicExp.m_one] or
    [DyadicExp.one]: it is not a zero, and [B2R] is injective on the
    nonzero finite [f64]s. *)
Lemma f64_of_value :
  forall (x y : f64) r,
  is_finite x = true -> is_finite_strict y = true -> B2R y = r -> r <> 0 -> B2R x = r -> x = y.
Proof.
intros x y r Fx Fy Hy Hr Hx. apply B2R_inj; [| exact Fy | congruence].
destruct x as [s|s| |s m e H]; try discriminate Fx; [| reflexivity].
cbn [B2R] in Hx. congruence.
Qed.

Theorem k_atanh_c : atanh_c k_atanh.
Proof.
split; [exact (kernel_field_correct_dom _ _ _ atanh_dir_correct) | split].
- intros x Fx Hx.
  rewrite (f64_of_value x DyadicExp.m_one (-1) Fx ltac:(vm_compute; reflexivity)
    DyHypRules.hyp_lit_m_one ltac:(lra) Hx).
  unfold k_atanh, kernel_field. cbn [up_of].
  replace (DyadicLog.atanh_dir DyadicExp.m_one false) with (Some (B754_infinity true : f64))
    by (vm_compute; reflexivity).
  reflexivity.
- intros x Fx Hx.
  rewrite (f64_of_value x DyadicExp.one 1 Fx ltac:(vm_compute; reflexivity)
    (proj2 one_B2R) ltac:(lra) Hx).
  unfold k_atanh, kernel_field. cbn [up_of].
  replace (DyadicLog.atanh_dir DyadicExp.one true) with (Some (B754_infinity false : f64))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Theorem kernel_ln_correct :
  forall p x, valid x -> is_tightest (image_dom log_dom ln x) (Interval.ln (kernel_point p) x).
Proof.
intros p x Hx. exact (ln_correct_point (kernel_point p) k_ln_c x Hx).
Qed.

Theorem kernel_log2_correct :
  forall p x, valid x ->
  is_tightest (image_dom log_dom Rlog2 x) (Interval.log2 (kernel_point p) x).
Proof.
intros p x Hx. exact (log2_correct_point (kernel_point p) k_log2_c x Hx).
Qed.

Theorem kernel_log10_correct :
  forall p x, valid x ->
  is_tightest (image_dom log_dom Rlog10 x) (Interval.log10 (kernel_point p) x).
Proof.
intros p x Hx. exact (log10_correct_point (kernel_point p) k_log10_c x Hx).
Qed.

Theorem kernel_asinh_correct :
  forall p x, valid x ->
  is_tightest (image_dom real_dom arcsinh x) (Interval.asinh (kernel_point p) x).
Proof.
intros p x Hx. exact (asinh_correct_point (kernel_point p) k_asinh_c x Hx).
Qed.

Theorem kernel_acosh_correct :
  forall p x, valid x ->
  is_tightest (image_dom acosh_dom Racosh x) (Interval.acosh (kernel_point p) x).
Proof.
intros p x Hx. exact (acosh_correct_point (kernel_point p) k_acosh_c x Hx).
Qed.

Theorem kernel_atanh_correct :
  forall p x, valid x ->
  is_tightest (image_dom atanh_dom Ratanh x) (Interval.atanh (kernel_point p) x).
Proof.
intros p x Hx. exact (atanh_correct_point (kernel_point p) k_atanh_c x Hx).
Qed.
