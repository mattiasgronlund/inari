(** * The functions of one argument of the ideal MPFR

    [ideal_fn_correct]: [ideal_fn] computes [f] on [D], as [mpfr_correct]
    says, if it rounds [f] at the numbers in [D] other than 0, and at the
    zeros if 0 is in [D]. [ideal_<f>_ok]: with it, and the special values
    that [ideal] gives, the ideal MPFR satisfies [<f>_ok] for the 18
    functions of one argument. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Mpfr MpfrRound MpfrIdeal IdealRound.

Open Scope R_scope.

Lemma ideal_fn_correct :
  forall emin emax (D : R -> Prop) f num zero inf, range_ok emin emax ->
  (forall rnd y, y <> 0 -> D y -> num rnd y = round_mpfr emin emax rnd (f y)) ->
  (forall rnd s, D 0 -> zero rnd s = round_mpfr emin emax rnd (f 0)) ->
  mpfr_correct emin emax D f (ideal_fn num zero inf).
Proof.
intros emin emax D f num zero inf Hr Hn Hz rnd x Fx Dx.
destruct (with_val_finite_cases x Fx) as [(s & E & B) | (E & B)];
  rewrite E; cbn [ideal_fn].
- rewrite B in Dx |- *. rewrite (Hz rnd s Dx). exact (round_mpfr_correct _ _ _ _ Hr).
- rewrite (Hn rnd _ B Dx). exact (round_mpfr_correct _ _ _ _ Hr).
Qed.

(** [mpfr_correct] for a field [ideal_fn (rnd_fn ..) (rnd_zero ..) _] of
    [ideal]: both side conditions hold by definition. *)
Ltac ie_correct Hr :=
  apply ideal_fn_correct; [exact Hr | intros; reflexivity | intros; reflexivity].

(** The same for the logarithms, whose domain leaves out 0. *)
Ltac ie_correct_log Hr :=
  apply ideal_fn_correct;
  [exact Hr | intros; reflexivity | intros ? ? H0; unfold log_dom in H0; lra].

Theorem ideal_acos_ok :
  forall emin emax, range_ok emin emax -> acos_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold acos_ok. cbn [ideal mpfr_acos]. ie_correct Hr.
Qed.

Theorem ideal_acosh_ok :
  forall emin emax, range_ok emin emax -> acosh_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold acosh_ok. cbn [ideal mpfr_acosh]. split.
- ie_correct Hr.
- reflexivity.
Qed.

Theorem ideal_asin_ok :
  forall emin emax, range_ok emin emax -> asin_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold asin_ok. cbn [ideal mpfr_asin]. ie_correct Hr.
Qed.

Theorem ideal_asinh_ok :
  forall emin emax, range_ok emin emax -> asinh_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold asinh_ok. cbn [ideal mpfr_asinh]. split; [|split].
- ie_correct Hr.
- reflexivity.
- reflexivity.
Qed.

Theorem ideal_atan_ok :
  forall emin emax, range_ok emin emax -> atan_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold atan_ok. cbn [ideal mpfr_atan]. split; [|split].
- ie_correct Hr.
- exact (round_mpfr_correct _ _ _ _ Hr).
- exact (round_mpfr_correct _ _ _ _ Hr).
Qed.

Theorem ideal_atanh_ok :
  forall emin emax, range_ok emin emax -> atanh_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold atanh_ok. cbn [ideal mpfr_atanh ideal_fn]. split; [|split].
- apply ideal_fn_correct; [exact Hr | | intros; reflexivity].
  (* On [atanh_dom], [y] is neither -1 nor 1, so [rnd_atanh] rounds. *)
  intros rnd y _ [H1 H2]. unfold rnd_atanh.
  destruct (Req_dec_T y (-1)) as [E|_]; [lra|].
  destruct (Req_dec_T y 1) as [E|_]; [lra|].
  reflexivity.
- unfold rnd_atanh. destruct (Req_dec_T (-1) (-1)) as [_|N]; [reflexivity|lra].
- unfold rnd_atanh. destruct (Req_dec_T 1 (-1)) as [E|_]; [lra|].
  destruct (Req_dec_T 1 1) as [_|N]; [reflexivity|lra].
Qed.

Theorem ideal_cos_ok :
  forall emin emax, range_ok emin emax -> cos_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold cos_ok. cbn [ideal mpfr_cos]. ie_correct Hr.
Qed.

Theorem ideal_cosh_ok :
  forall emin emax, range_ok emin emax -> cosh_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold cosh_ok. cbn [ideal mpfr_cosh]. split.
- ie_correct Hr.
- intros s. reflexivity.
Qed.

Theorem ideal_exp_ok :
  forall emin emax, range_ok emin emax -> exp_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold exp_ok. cbn [ideal mpfr_exp]. split; [|split].
- ie_correct Hr.
- reflexivity.
- reflexivity.
Qed.

Theorem ideal_exp10_ok :
  forall emin emax, range_ok emin emax -> exp10_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold exp10_ok. cbn [ideal mpfr_exp10]. split; [|split].
- ie_correct Hr.
- reflexivity.
- reflexivity.
Qed.

Theorem ideal_exp2_ok :
  forall emin emax, range_ok emin emax -> exp2_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold exp2_ok. cbn [ideal mpfr_exp2]. split; [|split].
- ie_correct Hr.
- reflexivity.
- reflexivity.
Qed.

Theorem ideal_ln_ok :
  forall emin emax, range_ok emin emax -> ln_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold ln_ok. cbn [ideal mpfr_log]. split; [|split].
- ie_correct_log Hr.
- intros s. reflexivity.
- reflexivity.
Qed.

Theorem ideal_log10_ok :
  forall emin emax, range_ok emin emax -> log10_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold log10_ok. cbn [ideal mpfr_log10]. split; [|split].
- ie_correct_log Hr.
- intros s. reflexivity.
- reflexivity.
Qed.

Theorem ideal_log2_ok :
  forall emin emax, range_ok emin emax -> log2_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold log2_ok. cbn [ideal mpfr_log2]. split; [|split].
- ie_correct_log Hr.
- intros s. reflexivity.
- reflexivity.
Qed.

Theorem ideal_sin_ok :
  forall emin emax, range_ok emin emax -> sin_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold sin_ok. cbn [ideal mpfr_sin]. ie_correct Hr.
Qed.

Theorem ideal_sinh_ok :
  forall emin emax, range_ok emin emax -> sinh_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold sinh_ok. cbn [ideal mpfr_sinh]. split; [|split].
- ie_correct Hr.
- reflexivity.
- reflexivity.
Qed.

Theorem ideal_tan_ok :
  forall emin emax, range_ok emin emax -> tan_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold tan_ok. cbn [ideal mpfr_tan]. ie_correct Hr.
Qed.

Theorem ideal_tanh_ok :
  forall emin emax, range_ok emin emax -> tanh_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr. unfold tanh_ok. cbn [ideal mpfr_tanh]. split; [|split].
- ie_correct Hr.
- reflexivity.
- reflexivity.
Qed.
