(** * MPFR functions made of functions of [f64]s

    [of_point p] is a record [mpfr] made of the record [point] [p], with
    [mpfr_point (of_point p) = p] ([mpfr_point_of_point]). Its
    [mpfr_get_d] and [mpfr_subnormalize] are those of the ideal MPFR of
    [MpfrIdeal.v], so they satisfy [get_d_ok] and [subnormalize_ok] at
    the exponent range of [f64]. Its other functions of MPFR numbers
    convert those to [f64]s, apply the field of [p], and make an MPFR
    number of the result with [lift_val] or [with_val]. Its
    [mpfr_set_q], of a rational, is [of_point_set_q] below.
    [OfPointElem.v], [OfPointPow.v] and [OfPointParse.v] show that each
    satisfies the hypothesis of [Mpfr.v] at that range wherever the field
    satisfies its counterpart in [Contract.v].

    So a theorem whose hypotheses on MPFR functions [m] and their
    exponent range are those of [Mpfr.v] ([range_ok], [get_d_ok],
    [<f>_ok] and [parse_ok]) and whose conclusion uses [m] only through
    the record [mpfr_point m], a coercion in [Model.v], holds for every
    record [p] that satisfies the counterparts in [Contract.v] of its
    [<f>_ok] and [parse_ok]: apply it at [of_point p] and the range of
    [f64], and rewrite with [mpfr_point_of_point]. [PointTheorems.v] does
    that for two such theorems, [exp_correct] and
    [from_ninterval_correct]; the others are stated only for MPFR
    functions [m]. *)

From Stdlib Require Import ZArith Reals Qreals Lra Lia FunctionalExtensionality.
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
    finite [x <= 0], so any value does there. [pow_val] and [pown_val]
    give [Rpow] and [powerRZ] at finite [f64]s. *)
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

Definition pow_val (x y : f64) : option R :=
  if is_finite x && is_finite y then Some (Rpow (B2R x) (B2R y)) else None.

Definition pown_val (x : f64) (n : Z) : option R :=
  if is_finite x then Some (powerRZ (B2R x) n) else None.

(** A ternary value of [v] for [r] that is not 0: [ternary r v], or 1 if
    that is 0. *)
Definition ternary_nz (r : R) (v : mpfr_t) : Z :=
  match ternary r v with 0%Z => 1%Z | t => t end.

(** [mpfr_set_q] made of [p_round_rational p]: the result of the ideal
    MPFR if [mpfr_subnormalize] and [mpfr_get_d], as [ideal_subnormalize]
    and [ideal_get_d] model them, turn it into what [p_round_rational p]
    gives, and otherwise the [f64] of [p_round_rational p] as an MPFR
    number, with a ternary value that is 0 exactly when
    [p_round_rational p] says that it is exact. *)
Definition of_point_set_q (p : point) (emin emax : Z) (rnd : mpfr_rnd) (q : Q) :
    mpfr_t * Z :=
  let '(w, inexact) := p_round_rational p rnd q in
  let h := ideal_set_q emin emax rnd q in
  let '(x', t') := ideal_subnormalize emin emax rnd (fst h) (snd h) in
  let other := (with_val w, if inexact then ternary_nz (Q2R q) (with_val w) else 0%Z) in
  if f64_eq_dec (ideal_get_d rnd x') w then
    if Bool.bool_dec (negb (t' =? 0)%Z) inexact then h else other
  else other.

Definition of_point (p : point) : mpfr := {|
  mpfr_get_d := ideal_get_d;
  mpfr_acos := lift1 (fin acos) (p_acos p);
  mpfr_acosh := lift1 (fin Racosh) (p_acosh p);
  mpfr_asin := lift1 (fin asin) (p_asin p);
  mpfr_asinh := lift1 (fin arcsinh) (p_asinh p);
  mpfr_atan := lift1 atan_val (p_atan p);
  mpfr_atan2 := lift2 atan2_val (p_atan2 p);
  mpfr_atanh := lift1 (fin Ratanh) (p_atanh p);
  mpfr_cos := lift1 (fin cos) (p_cos p);
  mpfr_cosh := lift1 (fin cosh) (p_cosh p);
  mpfr_exp := lift1 (fin exp) (p_exp p);
  mpfr_exp10 := lift1 (fin Rexp10) (p_exp10 p);
  mpfr_exp2 := lift1 (fin Rexp2) (p_exp2 p);
  mpfr_log := lift1 (fin ln) (p_ln p);
  mpfr_log10 := lift1 (fin Rlog10) (p_log10 p);
  mpfr_log2 := lift1 (fin Rlog2) (p_log2 p);
  mpfr_pow := lift2 pow_val (p_pow p);
  mpfr_pow_si := lift_si pown_val (p_pown p);
  mpfr_sin := lift1 (fin sin) (p_sin p);
  mpfr_sinh := lift1 (fin sinh) (p_sinh p);
  mpfr_tan := lift1 (fin tan) (p_tan p);
  mpfr_tanh := lift1 (fin tanh) (p_tanh p);
  mpfr_set_q := of_point_set_q p;
  mpfr_subnormalize := ideal_subnormalize
|}.

(** [ideal_subnormalize] keeps an [f64], which is a multiple of
    [2^-1074]. *)
Lemma ideal_subnormalize_with_val :
  forall rnd w t, ideal_subnormalize (-1073) 1024 rnd (with_val w) t = (with_val w, t).
Proof.
intros rnd [s|s| |s mw ew Hw] t; try reflexivity.
cbn [with_val ideal_subnormalize].
destruct (Req_dec_T _ _) as [E|E]; [reflexivity|].
exfalso. apply E. unfold round_sub.
(* [FLT_exp (-1073 - 1) 53] is the format of the finite [f64]s, which
   rounding keeps. *)
apply round_generic; [apply valid_rnd_round_mode|].
exact (generic_format_B2R 53 1024 (B754_finite s mw ew Hw)).
Qed.

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

(** [ternary_nz] is never 0. *)
Lemma ternary_nz_neq_0 : forall r v, ternary_nz r v <> 0%Z.
Proof. intros r v. unfold ternary_nz. destruct (ternary r v); discriminate. Qed.

(** [p_round_rational] of [mpfr_point (of_point p)] is that of [p]. If
    [of_point_set_q] returns the result of the ideal MPFR, the two tests
    say that [ideal_subnormalize] and [ideal_get_d] turn it into what
    [p_round_rational p] gives. Otherwise it returns [with_val w] for the
    [f64] [w] of [p_round_rational p], which [ideal_subnormalize] keeps
    ([ideal_subnormalize_with_val]) and [ideal_get_d] converts back to
    [w], with a ternary value that is 0 exactly when [p_round_rational p]
    says that [w] is exact. *)
Lemma of_point_round_rational :
  forall p rnd q,
  (let '(f, t) := of_point_set_q p (-1073) 1024 rnd q in
   let '(f, t) := ideal_subnormalize (-1073) 1024 rnd f t in
   (ideal_get_d rnd f, negb (t =? 0)%Z)) = p_round_rational p rnd q.
Proof.
intros p rnd q. unfold of_point_set_q.
destruct (p_round_rational p rnd q) as [w inexact].
destruct (ideal_set_q (-1073) 1024 rnd q) as [x t]. cbn [fst snd].
destruct (ideal_subnormalize (-1073) 1024 rnd x t) as [x' t'] eqn:Es.
assert (Hother :
  (let '(f, t) := (with_val w, if inexact then ternary_nz (Q2R q) (with_val w) else 0%Z) in
   let '(f, t) := ideal_subnormalize (-1073) 1024 rnd f t in
   (ideal_get_d rnd f, negb (t =? 0)%Z)) = (w, inexact)).
{ rewrite ideal_subnormalize_with_val, ideal_get_d_with_val. f_equal.
  destruct inexact; [|reflexivity].
  apply Bool.negb_true_iff, Z.eqb_neq, ternary_nz_neq_0. }
destruct (f64_eq_dec (ideal_get_d rnd x') w) as [Ed|Ed]; [|exact Hother].
destruct (Bool.bool_dec (negb (t' =? 0)%Z) inexact) as [Eb|Eb]; [|exact Hother].
rewrite Es, Ed, Eb. reflexivity.
Qed.

(** Each field of [mpfr_point (of_point p)] but [p_round_rational] is
    [mpfr_fn], [mpfr_fn2] or [mpfr_fn_si] of a field of [of_point p] made
    by [lift1], [lift2] or [lift_si] of the same field of [p], which gives
    that field back ([mpfr_fn_lift1], [mpfr_fn2_lift2] and
    [mpfr_fn_si_lift_si]), and [p_round_rational] is that of [p]
    ([of_point_round_rational]). The proof rewrites with these instead of
    using [f_equal], which did not finish here. *)
Theorem mpfr_point_of_point : forall p, mpfr_point (of_point p) = p.
Proof.
intros [h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 rr].
unfold mpfr_point.
cbn [of_point mpfr_get_d mpfr_acos mpfr_acosh mpfr_asin mpfr_asinh mpfr_atan mpfr_atan2
  mpfr_atanh mpfr_cos mpfr_cosh mpfr_exp mpfr_exp10 mpfr_exp2 mpfr_log mpfr_log10 mpfr_log2
  mpfr_pow mpfr_pow_si mpfr_sin mpfr_sinh mpfr_tan mpfr_tanh mpfr_set_q mpfr_subnormalize
  p_acos p_acosh p_asin p_asinh p_atan p_atan2 p_atanh p_cos p_cosh p_exp p_exp10 p_exp2
  p_ln p_log10 p_log2 p_pow p_pown p_sin p_sinh p_tan p_tanh].
rewrite !mpfr_fn_lift1, !mpfr_fn2_lift2, mpfr_fn_si_lift_si by reflexivity.
match goal with
| |- Build_point _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?X = _ =>
    replace X with rr; [reflexivity|]
end.
apply functional_extensionality; intros rnd.
apply functional_extensionality; intros q.
symmetry. exact (of_point_round_rational _ rnd q).
Qed.

Theorem of_point_get_d_ok : forall p, get_d_ok (-1073) 1024 (of_point p).
Proof. intros p. exact (ideal_get_d_ok (-1073) 1024 0 0). Qed.
