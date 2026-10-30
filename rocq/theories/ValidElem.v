(** * The elementary functions return [valid] intervals

    For [Valid.v]: each elementary function proved here returns a [valid]
    interval for a [valid] argument, as its theorem's [is_tightest] says,
    and so does its decorated version, whose result is [set_dec] of one or
    NaI. Each assumes what [Mpfr.v] says of MPFR. *)

From Stdlib Require Import ZArith Reals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr ValidMake ValidDecOps
  Elem Atanh Cosh ClosedDom.

(** [DecInterval::$f] of [impl_dec!($f)] is [set_dec] of [Interval::$f],
    so it is [valid] whenever [Interval::$f] is. *)
Lemma ve_elem_dec_valid :
  forall f x, valid (f (itv x)) -> valid (itv (DecInterval.elem_dec f x)).
Proof.
intros f x Hy. exact (set_dec_valid _ _ Hy).
Qed.

(** The same for [impl_dec!($f, $f_impl)], whose interval is the first
    component of [Interval::$f_impl], that is, [Interval::$f]. *)
Lemma ve_elem_dec_impl_valid :
  forall f x, valid (fst (f (itv x))) ->
  valid (itv (DecInterval.elem_dec_impl f x)).
Proof.
intros f x Hy. unfold DecInterval.elem_dec_impl.
destruct (f (itv x)) as [y d]. exact (set_dec_valid _ _ Hy).
Qed.

(** [<f>_valid]: [is_tightest S y] starts with [valid y]. *)
Ltac ve_plain thm :=
  intros emin emax m x Hr Hget Hok Hx;
  exact (proj1 (thm emin emax m Hr Hget Hok x Hx)).

(** [dec_<f>_valid] from [<f>_valid], by [set_dec_valid] rather than by
    [dec_<f>_correct], some of which assume [com_common x]. *)
Ltac ve_dec lem thm :=
  intros emin emax m x Hr Hget Hok Hx;
  exact (lem _ x (thm emin emax m (itv x) Hr Hget Hok Hx)).

Theorem acos_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> acos_ok emin emax m ->
  valid x -> valid (Interval.acos m x).
Proof.
ve_plain acos_correct.
Qed.

Theorem dec_acos_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> acos_ok emin emax m ->
  valid (itv x) -> valid (itv (DecInterval.acos m x)).
Proof.
ve_dec ve_elem_dec_impl_valid acos_valid.
Qed.

Theorem acosh_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> acosh_ok emin emax m ->
  valid x -> valid (Interval.acosh m x).
Proof.
ve_plain acosh_correct.
Qed.

Theorem dec_acosh_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> acosh_ok emin emax m ->
  valid (itv x) -> valid (itv (DecInterval.acosh m x)).
Proof.
ve_dec ve_elem_dec_impl_valid acosh_valid.
Qed.

Theorem asin_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> asin_ok emin emax m ->
  valid x -> valid (Interval.asin m x).
Proof.
ve_plain asin_correct.
Qed.

Theorem dec_asin_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> asin_ok emin emax m ->
  valid (itv x) -> valid (itv (DecInterval.asin m x)).
Proof.
ve_dec ve_elem_dec_impl_valid asin_valid.
Qed.

Theorem asinh_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> asinh_ok emin emax m ->
  valid x -> valid (Interval.asinh m x).
Proof.
ve_plain asinh_correct.
Qed.

Theorem dec_asinh_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> asinh_ok emin emax m ->
  valid (itv x) -> valid (itv (DecInterval.asinh m x)).
Proof.
ve_dec ve_elem_dec_valid asinh_valid.
Qed.

Theorem atan_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> atan_ok emin emax m ->
  valid x -> valid (Interval.atan m x).
Proof.
ve_plain atan_correct.
Qed.

Theorem dec_atan_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> atan_ok emin emax m ->
  valid (itv x) -> valid (itv (DecInterval.atan m x)).
Proof.
ve_dec ve_elem_dec_valid atan_valid.
Qed.

Theorem atanh_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> atanh_ok emin emax m ->
  valid x -> valid (Interval.atanh m x).
Proof.
ve_plain atanh_correct.
Qed.

Theorem dec_atanh_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> atanh_ok emin emax m ->
  valid (itv x) -> valid (itv (DecInterval.atanh m x)).
Proof.
ve_dec ve_elem_dec_impl_valid atanh_valid.
Qed.

Theorem cosh_valid :
  forall emin emax m first x, range_ok emin emax -> get_d_ok emin emax m -> cosh_ok emin emax m ->
  valid x -> valid (Interval.cosh m first x).
Proof.
intros emin emax m first x Hr Hget Hok Hx.
exact (proj1 (cosh_correct emin emax m Hr Hget Hok first x Hx)).
Qed.

Theorem dec_cosh_valid :
  forall emin emax m first x, range_ok emin emax -> get_d_ok emin emax m -> cosh_ok emin emax m ->
  valid (itv x) -> valid (itv (DecInterval.cosh m first x)).
Proof.
intros emin emax m first x Hr Hget Hok Hx.
exact (ve_elem_dec_valid _ x (cosh_valid emin emax m first (itv x) Hr Hget Hok Hx)).
Qed.

Theorem exp_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> exp_ok emin emax m ->
  valid x -> valid (Interval.exp m x).
Proof.
ve_plain exp_correct.
Qed.

Theorem dec_exp_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> exp_ok emin emax m ->
  valid (itv x) -> valid (itv (DecInterval.exp m x)).
Proof.
ve_dec ve_elem_dec_valid exp_valid.
Qed.

Theorem exp10_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> exp10_ok emin emax m ->
  valid x -> valid (Interval.exp10 m x).
Proof.
ve_plain exp10_correct.
Qed.

Theorem dec_exp10_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> exp10_ok emin emax m ->
  valid (itv x) -> valid (itv (DecInterval.exp10 m x)).
Proof.
ve_dec ve_elem_dec_valid exp10_valid.
Qed.

Theorem exp2_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> exp2_ok emin emax m ->
  valid x -> valid (Interval.exp2 m x).
Proof.
ve_plain exp2_correct.
Qed.

Theorem dec_exp2_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> exp2_ok emin emax m ->
  valid (itv x) -> valid (itv (DecInterval.exp2 m x)).
Proof.
ve_dec ve_elem_dec_valid exp2_valid.
Qed.

Theorem ln_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> ln_ok emin emax m ->
  valid x -> valid (Interval.ln m x).
Proof.
ve_plain ln_correct.
Qed.

Theorem dec_ln_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> ln_ok emin emax m ->
  valid (itv x) -> valid (itv (DecInterval.ln m x)).
Proof.
ve_dec ve_elem_dec_impl_valid ln_valid.
Qed.

Theorem log10_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> log10_ok emin emax m ->
  valid x -> valid (Interval.log10 m x).
Proof.
ve_plain log10_correct.
Qed.

Theorem dec_log10_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> log10_ok emin emax m ->
  valid (itv x) -> valid (itv (DecInterval.log10 m x)).
Proof.
ve_dec ve_elem_dec_impl_valid log10_valid.
Qed.

Theorem log2_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> log2_ok emin emax m ->
  valid x -> valid (Interval.log2 m x).
Proof.
ve_plain log2_correct.
Qed.

Theorem dec_log2_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> log2_ok emin emax m ->
  valid (itv x) -> valid (itv (DecInterval.log2 m x)).
Proof.
ve_dec ve_elem_dec_impl_valid log2_valid.
Qed.

Theorem sinh_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> sinh_ok emin emax m ->
  valid x -> valid (Interval.sinh m x).
Proof.
ve_plain sinh_correct.
Qed.

Theorem dec_sinh_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> sinh_ok emin emax m ->
  valid (itv x) -> valid (itv (DecInterval.sinh m x)).
Proof.
ve_dec ve_elem_dec_valid sinh_valid.
Qed.

Theorem tanh_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> tanh_ok emin emax m ->
  valid x -> valid (Interval.tanh m x).
Proof.
ve_plain tanh_correct.
Qed.

Theorem dec_tanh_valid :
  forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m -> tanh_ok emin emax m ->
  valid (itv x) -> valid (itv (DecInterval.tanh m x)).
Proof.
ve_dec ve_elem_dec_valid tanh_valid.
Qed.
