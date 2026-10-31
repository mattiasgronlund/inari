(** * The hypotheses of [Mpfr.v] can all hold at once

    [mpfr_ok emin emax m] is the conjunction of every hypothesis on [m]
    that the theorems take, besides [range_ok emin emax]: [get_d_ok], the
    21 [<f>_ok] of the functions of [src/elementary.rs], and [parse_ok] for
    [src/parse.rs]. No theorem takes [mpfr_ok] itself: they keep their own
    hypotheses on [m], all of them among these. The generic theorems from
    which those about the functions are proved, such as [mono_inc_correct],
    also take hypotheses on an MPFR function [g], such as
    [mpfr_correct], which those proofs derive from the [<f>_ok] for the
    field of [m]. [mpfr_ok_consistent] shows that for
    every exponent range with [range_ok], some [m] satisfies [mpfr_ok]: the
    ideal MPFR of [MpfrIdeal.v]. So the hypotheses do not contradict one
    another, and [mpfr_ok_default] gives such a range and [m] at MPFR's
    default exponent range. *)

From Stdlib Require Import ZArith Reals Lia.
From Inari Require Import Model Elementary Mpfr MpfrIdeal IdealRound IdealGetD IdealParse
  IdealElem IdealPow IdealAtan2.

Definition mpfr_ok (emin emax : Z) (m : mpfr) : Prop :=
  get_d_ok emin emax m /\
  acos_ok emin emax m /\
  acosh_ok emin emax m /\
  asin_ok emin emax m /\
  asinh_ok emin emax m /\
  atan_ok emin emax m /\
  atan2_ok emin emax m /\
  atanh_ok emin emax m /\
  cos_ok emin emax m /\
  cosh_ok emin emax m /\
  exp_ok emin emax m /\
  exp10_ok emin emax m /\
  exp2_ok emin emax m /\
  ln_ok emin emax m /\
  log10_ok emin emax m /\
  log2_ok emin emax m /\
  pow_ok emin emax m /\
  pown_ok emin emax m /\
  sin_ok emin emax m /\
  sinh_ok emin emax m /\
  tan_ok emin emax m /\
  tanh_ok emin emax m /\
  parse_ok m.

Theorem ideal_parse_ok : forall a b, parse_ok (ideal a b).
Proof.
intros a b.
assert (Hr : range_ok (-1073) 1024) by (split; lia).
split; [|split].
- exact (ideal_set_q_ok _ _ a b Hr).
- exact (ideal_subnormalize_ok _ _ a b Hr).
- exact (ideal_get_d_ok _ _ a b).
Qed.

Theorem ideal_mpfr_ok :
  forall emin emax, range_ok emin emax -> mpfr_ok emin emax (ideal emin emax).
Proof.
intros emin emax Hr.
unfold mpfr_ok.
split; [exact (ideal_get_d_ok emin emax emin emax)|].
split; [exact (ideal_acos_ok emin emax Hr)|].
split; [exact (ideal_acosh_ok emin emax Hr)|].
split; [exact (ideal_asin_ok emin emax Hr)|].
split; [exact (ideal_asinh_ok emin emax Hr)|].
split; [exact (ideal_atan_ok emin emax Hr)|].
split; [exact (ideal_atan2_ok emin emax Hr)|].
split; [exact (ideal_atanh_ok emin emax Hr)|].
split; [exact (ideal_cos_ok emin emax Hr)|].
split; [exact (ideal_cosh_ok emin emax Hr)|].
split; [exact (ideal_exp_ok emin emax Hr)|].
split; [exact (ideal_exp10_ok emin emax Hr)|].
split; [exact (ideal_exp2_ok emin emax Hr)|].
split; [exact (ideal_ln_ok emin emax Hr)|].
split; [exact (ideal_log10_ok emin emax Hr)|].
split; [exact (ideal_log2_ok emin emax Hr)|].
split; [exact (ideal_pow_ok emin emax Hr)|].
split; [exact (ideal_pown_ok emin emax Hr)|].
split; [exact (ideal_sin_ok emin emax Hr)|].
split; [exact (ideal_sinh_ok emin emax Hr)|].
split; [exact (ideal_tan_ok emin emax Hr)|].
split; [exact (ideal_tanh_ok emin emax Hr)|].
exact (ideal_parse_ok emin emax).
Qed.

Theorem mpfr_ok_consistent :
  forall emin emax, range_ok emin emax -> exists m, mpfr_ok emin emax m.
Proof.
intros emin emax Hr. exists (ideal emin emax). exact (ideal_mpfr_ok emin emax Hr).
Qed.

(** MPFR's default exponent range, [MPFR_EMIN_DEFAULT] and
    [MPFR_EMAX_DEFAULT] in [mpfr.h], satisfies [range_ok], and some [m]
    satisfies [mpfr_ok] at it. *)
Corollary mpfr_ok_default :
  range_ok (1 - 2 ^ 30) (2 ^ 30 - 1) /\ exists m, mpfr_ok (1 - 2 ^ 30) (2 ^ 30 - 1) m.
Proof.
assert (Hr : range_ok (1 - 2 ^ 30) (2 ^ 30 - 1)) by (split; cbn; lia).
split; [exact Hr | exact (mpfr_ok_consistent _ _ Hr)].
Qed.
