(** * MPFR functions made of functions of [f64]s

    [of_point p] is a record [mpfr] made of the record [point] [p], with
    [mpfr_point (of_point p) = p] ([mpfr_point_of_point]). Its
    [mpfr_get_d] is that of the ideal MPFR of [MpfrIdeal.v], so it
    satisfies [get_d_ok] at the exponent range of [f64]. Its other
    functions, of MPFR numbers, convert those to [f64]s, apply the field
    of [p], and make an MPFR number of the result with [lift_val] or
    [with_val]. [OfPointElem.v] and [OfPointPow.v] show that each
    satisfies the hypothesis of [Mpfr.v] at that range wherever the field
    satisfies its counterpart in [Contract.v].

    So a theorem whose hypotheses on MPFR functions [m] and their
    exponent range are those of [Mpfr.v] ([range_ok], [get_d_ok] and
    [<f>_ok]) and whose conclusion uses [m] only through the record
    [mpfr_point m], a coercion in [Model.v], holds for every record [p]
    that satisfies the counterparts in [Contract.v] of its [<f>_ok]: apply
    it at [of_point p] and the range of [f64], and rewrite with
    [mpfr_point_of_point]. [PointTheorems.v] does that for the theorems
    that its header lists, such as [exp_correct]; the others are stated
    only for MPFR functions [m]. *)

From Stdlib Require Import ZArith Reals Lra Lia FunctionalExtensionality.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Mpfr MpfrRound MpfrIdeal IdealRound IdealGetD
  Contract OfPointCore.

Open Scope R_scope.

(** The exact results that [lift_val] is given; at other arguments
    these give nothing. [atan_val] gives [atan] at a finite [f64],
    [- (PI / 2)] at -inf and [PI / 2] at +inf. [atan2_val y x] gives
    [Ratan2] at finite [y] and [x]; [PI / 2] at [y = +inf] and
    [- (PI / 2)] at [y = -inf] for a finite [x]; and, at [x = -inf], [PI]
    for a finite [y > 0] and [- PI] for a finite [y <= 0]. [atan2_c] and
    [atan2_ok] say nothing at [y = ±0] and an [x] that is -inf or a
    finite [x <= 0], so any value does there. [hypot_val], [pow_val] and
    [pown_val] give [Rhypot], [Rpow] and [powerRZ] at finite [f64]s. *)
Definition atan_val (x : f64) : option R :=
  match x with
  | B754_infinity s => Some (if s then - (PI / 2) else PI / 2)
  | _ => fin atan x
  end.

Definition atan2_val (y x : f64) : option R :=
  if is_finite y && is_finite x then Some (Ratan2 (B2R y) (B2R x)) else
  match y, x with
  | B754_infinity s, _ => if is_finite x then Some (if s then - (PI / 2) else PI / 2) else None
  | _, B754_infinity true =>
      if is_finite y then Some (if Rlt_dec 0 (B2R y) then PI else - PI) else None
  | _, _ => None
  end.

Definition hypot_val (x y : f64) : option R :=
  if is_finite x && is_finite y then Some (Rhypot (B2R x) (B2R y)) else None.

Definition pow_val (x y : f64) : option R :=
  if is_finite x && is_finite y then Some (Rpow (B2R x) (B2R y)) else None.

Definition pown_val (x : f64) (n : Z) : option R :=
  if is_finite x then Some (powerRZ (B2R x) n) else None.

Definition of_point (p : point) : mpfr := {|
  mpfr_get_d := ideal_get_d;
  mpfr_acos := lift1 (fin acos) (p_acos p);
  mpfr_acosh := lift1 (fin Racosh) (p_acosh p);
  mpfr_asin := lift1 (fin asin) (p_asin p);
  mpfr_asinh := lift1 (fin arcsinh) (p_asinh p);
  mpfr_atan := lift1 atan_val (p_atan p);
  mpfr_atan2 := lift2 atan2_val (p_atan2 p);
  mpfr_atanh := lift1 (fin Ratanh) (p_atanh p);
  mpfr_cbrt := lift1 (fin Rcbrt) (p_cbrt p);
  mpfr_cos := lift1 (fin cos) (p_cos p);
  mpfr_cosh := lift1 (fin cosh) (p_cosh p);
  mpfr_exp := lift1 (fin exp) (p_exp p);
  mpfr_exp10 := lift1 (fin Rexp10) (p_exp10 p);
  mpfr_exp2 := lift1 (fin Rexp2) (p_exp2 p);
  mpfr_hypot := lift2 hypot_val (p_hypot p);
  mpfr_log := lift1 (fin ln) (p_ln p);
  mpfr_log10 := lift1 (fin Rlog10) (p_log10 p);
  mpfr_log2 := lift1 (fin Rlog2) (p_log2 p);
  mpfr_pow := lift2 pow_val (p_pow p);
  mpfr_pow_si := lift_si pown_val (p_pown p);
  mpfr_sin := lift1 (fin sin) (p_sin p);
  mpfr_sinh := lift1 (fin sinh) (p_sinh p);
  mpfr_tan := lift1 (fin tan) (p_tan p);
  mpfr_tanh := lift1 (fin tanh) (p_tanh p)
|}.

(** [mpfr_fn] of [lift1 F h], where [mpfr_get_d] is [ideal_get_d], is
    [h]: the argument [with_val x] converts back to [x], and the MPFR
    number that [lift1] makes of [h rnd x] converts back to [h rnd x]. *)
Lemma mpfr_fn_lift1 :
  forall m F h, mpfr_get_d m = ideal_get_d -> mpfr_fn m (lift1 F h) = h.
Proof.
intros m F h Hm.
apply functional_extensionality; intros rnd.
apply functional_extensionality; intros x.
unfold mpfr_fn, lift1. cbv beta zeta. rewrite Hm, ideal_get_d_with_val.
destruct (F x); [apply ideal_get_d_lift_val | apply ideal_get_d_with_val].
Qed.

(** The same for two numbers. *)
Lemma mpfr_fn2_lift2 :
  forall m F h, mpfr_get_d m = ideal_get_d -> mpfr_fn2 m (lift2 F h) = h.
Proof.
intros m F h Hm.
apply functional_extensionality; intros rnd.
apply functional_extensionality; intros x.
apply functional_extensionality; intros y.
unfold mpfr_fn2, lift2. cbv beta zeta. rewrite Hm, !ideal_get_d_with_val.
destruct (F x y); [apply ideal_get_d_lift_val | apply ideal_get_d_with_val].
Qed.

(** The same for a number and an integer. *)
Lemma mpfr_fn_si_lift_si :
  forall m F h, mpfr_get_d m = ideal_get_d -> mpfr_fn_si m (lift_si F h) = h.
Proof.
intros m F h Hm.
apply functional_extensionality; intros rnd.
apply functional_extensionality; intros x.
apply functional_extensionality; intros n.
unfold mpfr_fn_si, lift_si. cbv beta zeta. rewrite Hm, ideal_get_d_with_val.
destruct (F x n); [apply ideal_get_d_lift_val | apply ideal_get_d_with_val].
Qed.

(** Each field of [mpfr_point (of_point p)] is [mpfr_fn], [mpfr_fn2] or
    [mpfr_fn_si] of a field of [of_point p] made by [lift1], [lift2] or
    [lift_si] of the same field of [p], which gives that field back
    ([mpfr_fn_lift1], [mpfr_fn2_lift2] and [mpfr_fn_si_lift_si]). The
    proof rewrites with these instead of using [f_equal], which did not
    finish here. *)
Theorem mpfr_point_of_point : forall p, mpfr_point (of_point p) = p.
Proof.
intros [h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23].
unfold mpfr_point.
cbn [of_point mpfr_get_d mpfr_acos mpfr_acosh mpfr_asin mpfr_asinh mpfr_atan mpfr_atan2
  mpfr_atanh mpfr_cbrt mpfr_cos mpfr_cosh mpfr_exp mpfr_exp10 mpfr_exp2 mpfr_hypot mpfr_log
  mpfr_log10 mpfr_log2 mpfr_pow mpfr_pow_si mpfr_sin mpfr_sinh mpfr_tan mpfr_tanh
  p_acos p_acosh p_asin p_asinh p_atan p_atan2 p_atanh p_cbrt p_cos p_cosh p_exp p_exp10 p_exp2
  p_hypot p_ln p_log10 p_log2 p_pow p_pown p_sin p_sinh p_tan p_tanh].
rewrite !mpfr_fn_lift1, !mpfr_fn2_lift2, mpfr_fn_si_lift_si by reflexivity.
reflexivity.
Qed.

Theorem of_point_get_d_ok : forall p, get_d_ok (-1073) 1024 (of_point p).
Proof. intros p. exact (ideal_get_d_ok (-1073) 1024 0 0). Qed.
