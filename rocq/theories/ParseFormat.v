(** * The reals that [mpfr_subnormalize] rounds to are the finite [f64]s

    At the exponent range that [rational_to_f64] in [src/parse.rs] sets,
    [emin = -1073] and [emax = 1024], [sub_format] of [Mpfr.v] is
    [f64_format]: 0, and the multiples of [2^-1074] with at most 53 bits of
    significand below [2^1024] in absolute value. *)

From Stdlib Require Import ZArith Reals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr MpfrRound.

Open Scope R_scope.

Lemma sub_format_f64 : forall y, sub_format (-1073) 1024 y <-> f64_format y.
Proof.
intros y. split.
- intros [[H0 | [_ Hb]] HG].
  + (* 0 is the zero [f64]. *)
    exists (B754_zero false). split; [reflexivity | now subst y].
  + (* [y] is a float of [FLT_exp (-1074) 53], the format of the finite
       [f64]s, below [2^1024] in absolute value, so [binary_normalize]
       rounds it to itself without overflowing. *)
    change (-1073 - 1)%Z with (SpecFloat.emin 53 1024) in HG.
    unfold generic_format in HG.
    set (mx := Ztrunc _) in HG. set (ex := cexp _ _ _) in HG.
    pose proof (binary_normalize_correct 53 1024 _ _ mode_NE mx ex false)
      as Hn.
    cbv zeta in Hn. rewrite <- HG in Hn.
    rewrite round_generic in Hn.
    2: { apply valid_rnd_round_mode. }
    2: { unfold generic_format. fold mx ex. exact HG. }
    rewrite Rlt_bool_true in Hn by apply Hb.
    destruct Hn as (Hv & Hf & _).
    eexists. split; [exact Hf | exact Hv].
- intros (w & Fw & <-). split.
  + apply f64_mpfr_format; [split; apply Z.le_refl | exists w; auto].
  + (* The finite [f64]s are the floats of [FLT_exp (3 - 1024 - 53) 53],
       and [3 - 1024 - 53 = -1073 - 1]. *)
    exact (generic_format_B2R 53 1024 w).
Qed.
