(** * Each theorem that assumes MPFR, applied to the ideal MPFR

    For each theorem that [Assumptions.v] prints, and each constructor of
    [made] and [dmade] in [Valid.v], that quantifies over an MPFR [m], this
    file applies it to [ideal emin emax] of [MpfrIdeal.v], for every
    exponent range with [range_ok], and proves from [range_ok] and
    [ideal_mpfr_ok] alone each of its hypotheses that is
    [range_ok emin emax] or a conjunct of [mpfr_ok emin emax m]. It walks
    the binders of the theorem up to the first type that is not a product,
    such as a [let], an [exists] or a conjunction, and fails on any other
    hypothesis there (a binder whose type is a [Prop]) whose predicate is
    [range_ok] or that of a conjunct, or that mentions no variable but
    [emin], [emax] and [m]. So each such hypothesis of these theorems that
    is about [emin], [emax] and [m] alone is [range_ok] or a conjunct of
    [mpfr_ok], and [mpfr_ok_consistent] shows that these can all hold at
    once. The other hypotheses, such as [valid x], or
    [Interval.cos m has_fma first x = Some y] in [cos_valid], stay
    hypotheses of the [Example], as the other binders, such as [x], stay
    binders of it. This misses a hypothesis on [m] whose predicate is
    neither [range_ok] nor that of a conjunct and that also mentions
    another variable, such as [x], a hypothesis in the first type that is
    not a product, such as in the body of a definition, and a binder on [m]
    whose type is not a [Prop]. [make] checks that every such theorem and
    constructor has an [Example] here (see the [Makefile]). *)

From Stdlib Require Import ZArith.
From Inari Require Import Model Mpfr MpfrIdeal MpfrConsistent MpfrRound ClosedDom Elem
  Atanh Cosh TrigQuad TrigCount Cos Sin Tan Pow Powi Atan2 ParseRound ParseHull ParseExact
  ParseDec ValidMake ValidElem Valid MpfrPoint.

(** [app_head t] is the function of the application [t], or [t] if [t] is
    not an application. *)
Ltac app_head t := lazymatch t with ?f _ => app_head f | _ => t end.

(** [mpfr_pred emin emax P] succeeds if [P] is [range_ok] or the predicate
    of a conjunct of [mpfr_ok emin emax (ideal emin emax)], such as
    [get_d_ok] or [parse_ok]. *)
Ltac mpfr_pred emin emax P :=
  let T := eval cbv delta [mpfr_ok] beta in
    (range_ok emin emax /\ mpfr_ok emin emax (ideal emin emax)) in
  let rec go T :=
    lazymatch T with
    | ?B /\ ?C => first [go B | go C]
    | _ => let h := app_head T in constr_eq h P
    end in
  go T.

(** [keep_ok emin emax A] succeeds if [mpfr_walk] may keep the hypothesis
    [A]: if its predicate is neither [range_ok] nor that of a conjunct of
    [mpfr_ok], and it mentions a variable of the context other than [emin]
    and [emax], i.e. one that the theorem binds before [A]. *)
Ltac keep_ok emin emax A :=
  tryif (let P := app_head A in mpfr_pred emin emax P) then fail else
  match A with
  | context [?v] =>
      is_var v;
      tryif constr_eq v emin then fail else tryif constr_eq v emax then fail else idtac
  end.

(** [mpfr_walk emin emax Hr H] proves the goal, whose type is an evar, from
    [H], a theorem applied to [emin], [emax] and [ideal emin emax], or to
    [ideal emin emax] alone. It walks the binders of [H] in order, up to its
    conclusion, the first type that is not a product. It proves a
    hypothesis [range_ok emin emax] by [Hr], and a conjunct of
    [mpfr_ok emin emax (ideal emin emax)] from [ideal_mpfr_ok]. It keeps
    every other binder as a binder of the goal, but fails on a hypothesis
    (a binder whose type is a [Prop]) for which [keep_ok] fails, as one
    that mentions no variable that the theorem binds before it can only be
    about [emin], [emax] and the MPFR. *)
Ltac mpfr_walk emin emax Hr H :=
  lazymatch type of H with
  | forall y : ?A, _ =>
    lazymatch type of A with
    | Prop =>
      lazymatch A with
      | range_ok emin emax => specialize (H Hr); mpfr_walk emin emax Hr H
      | _ =>
        let T := eval cbv delta [mpfr_ok] beta in (mpfr_ok emin emax (ideal emin emax)) in
        lazymatch T with
        | context [A] =>
          let HA := fresh in
          assert (HA : A) by (
            pose proof (ideal_mpfr_ok emin emax Hr) as HB; cbv delta [mpfr_ok] beta in HB;
            decompose [and] HB; assumption);
          specialize (H HA); clear HA; mpfr_walk emin emax Hr H
        | _ =>
          let R := constr:(range_ok emin emax) in
          let M := constr:(mpfr_ok emin emax (ideal emin emax)) in
          first [ keep_ok emin emax A
                | fail 1 "The hypothesis" A "is neither" R "nor a conjunct of" M ];
          let n := fresh y in refine (fun n : A => _); specialize (H n);
          mpfr_walk emin emax Hr H
        end
      end
    | _ =>
      let n := fresh y in refine (fun n : A => _); specialize (H n);
      mpfr_walk emin emax Hr H
    end
  | _ => exact H
  end.

(** [mpfr_example t], for a theorem [t] that binds [emin emax m] or [m]
    first, makes [fun emin emax (Hr : range_ok emin emax) => ...]: [t]
    applied to [ideal emin emax], with its hypotheses on it proved as in
    [mpfr_walk]. *)
Ltac mpfr_example t :=
  let emin := fresh "emin" in
  let emax := fresh "emax" in
  let Hr := fresh "Hr" in
  refine (fun (emin emax : Z) (Hr : range_ok emin emax) => _);
  let H := fresh "H" in
  lazymatch type of t with
  | forall (_ _ : Z) (_ : mpfr), _ => pose proof (t emin emax (ideal emin emax)) as H
  | forall _ : mpfr, _ => pose proof (t (ideal emin emax)) as H
  | _ => fail "mpfr_example: the theorem binds neither emin emax m nor m first"
  end;
  mpfr_walk emin emax Hr H.

(** The theorems that [Assumptions.v] prints and that quantify over an
    MPFR, in its order. *)
Example mpfr_fn_round_ideal := ltac:(mpfr_example mpfr_fn_round).
Example asinh_correct_ideal := ltac:(mpfr_example asinh_correct).
Example dec_asinh_correct_ideal := ltac:(mpfr_example dec_asinh_correct).
Example atan_correct_ideal := ltac:(mpfr_example atan_correct).
Example dec_atan_correct_ideal := ltac:(mpfr_example dec_atan_correct).
Example exp_correct_ideal := ltac:(mpfr_example exp_correct).
Example dec_exp_correct_ideal := ltac:(mpfr_example dec_exp_correct).
Example exp10_correct_ideal := ltac:(mpfr_example exp10_correct).
Example dec_exp10_correct_ideal := ltac:(mpfr_example dec_exp10_correct).
Example exp2_correct_ideal := ltac:(mpfr_example exp2_correct).
Example dec_exp2_correct_ideal := ltac:(mpfr_example dec_exp2_correct).
Example sinh_correct_ideal := ltac:(mpfr_example sinh_correct).
Example dec_sinh_correct_ideal := ltac:(mpfr_example dec_sinh_correct).
Example tanh_correct_ideal := ltac:(mpfr_example tanh_correct).
Example dec_tanh_correct_ideal := ltac:(mpfr_example dec_tanh_correct).
Example ln_correct_ideal := ltac:(mpfr_example ln_correct).
Example dec_ln_correct_ideal := ltac:(mpfr_example dec_ln_correct).
Example log10_correct_ideal := ltac:(mpfr_example log10_correct).
Example dec_log10_correct_ideal := ltac:(mpfr_example dec_log10_correct).
Example log2_correct_ideal := ltac:(mpfr_example log2_correct).
Example dec_log2_correct_ideal := ltac:(mpfr_example dec_log2_correct).
Example asin_correct_ideal := ltac:(mpfr_example asin_correct).
Example dec_asin_correct_ideal := ltac:(mpfr_example dec_asin_correct).
Example acosh_correct_ideal := ltac:(mpfr_example acosh_correct).
Example dec_acosh_correct_ideal := ltac:(mpfr_example dec_acosh_correct).
Example acos_correct_ideal := ltac:(mpfr_example acos_correct).
Example dec_acos_correct_ideal := ltac:(mpfr_example dec_acos_correct).
Example atanh_correct_ideal := ltac:(mpfr_example atanh_correct).
Example dec_atanh_correct_ideal := ltac:(mpfr_example dec_atanh_correct).
Example cosh_correct_ideal := ltac:(mpfr_example cosh_correct).
Example dec_cosh_correct_ideal := ltac:(mpfr_example dec_cosh_correct).
Example quadrant_correct_ideal := ltac:(mpfr_example quadrant_correct).
Example quadrants_correct_ideal := ltac:(mpfr_example quadrants_correct).
Example cos_encloses_ideal := ltac:(mpfr_example cos_encloses).
Example cos_correct_ideal := ltac:(mpfr_example cos_correct).
Example dec_cos_correct_ideal := ltac:(mpfr_example dec_cos_correct).
Example sin_encloses_ideal := ltac:(mpfr_example sin_encloses).
Example sin_correct_ideal := ltac:(mpfr_example sin_correct).
Example dec_sin_correct_ideal := ltac:(mpfr_example dec_sin_correct).
Example tan_encloses_ideal := ltac:(mpfr_example tan_encloses).
Example tan_correct_ideal := ltac:(mpfr_example tan_correct).
Example dec_tan_correct_ideal := ltac:(mpfr_example dec_tan_correct).
Example pow_correct_ideal := ltac:(mpfr_example pow_correct).
Example dec_pow_correct_ideal := ltac:(mpfr_example dec_pow_correct).
Example powi_correct_ideal := ltac:(mpfr_example powi_correct).
Example dec_powi_correct_ideal := ltac:(mpfr_example dec_powi_correct).
Example atan2_correct_ideal := ltac:(mpfr_example atan2_correct).
Example dec_atan2_correct_ideal := ltac:(mpfr_example dec_atan2_correct).
Example rational_to_f64_correct_ideal := ltac:(mpfr_example rational_to_f64_correct).
Example number_to_f64_correct_ideal := ltac:(mpfr_example number_to_f64_correct).
Example bounds_tightest_ideal := ltac:(mpfr_example bounds_tightest).
Example try_from_ninterval_exact_correct_ideal := ltac:(mpfr_example try_from_ninterval_exact_correct).
Example from_dec_ninterval_correct_ideal := ltac:(mpfr_example from_dec_ninterval_correct).
Example from_ninterval_correct_ideal := ltac:(mpfr_example from_ninterval_correct).
Example from_ninterval_new_ideal := ltac:(mpfr_example from_ninterval_new).
Example try_from_ninterval_exact_valid_ideal := ltac:(mpfr_example try_from_ninterval_exact_valid).
Example from_dec_ninterval_valid_ideal := ltac:(mpfr_example from_dec_ninterval_valid).
Example acos_valid_ideal := ltac:(mpfr_example acos_valid).
Example acosh_valid_ideal := ltac:(mpfr_example acosh_valid).
Example asin_valid_ideal := ltac:(mpfr_example asin_valid).
Example asinh_valid_ideal := ltac:(mpfr_example asinh_valid).
Example atan_valid_ideal := ltac:(mpfr_example atan_valid).
Example atan2_valid_ideal := ltac:(mpfr_example atan2_valid).
Example atanh_valid_ideal := ltac:(mpfr_example atanh_valid).
Example cos_valid_ideal := ltac:(mpfr_example cos_valid).
Example cosh_valid_ideal := ltac:(mpfr_example cosh_valid).
Example exp_valid_ideal := ltac:(mpfr_example exp_valid).
Example exp10_valid_ideal := ltac:(mpfr_example exp10_valid).
Example exp2_valid_ideal := ltac:(mpfr_example exp2_valid).
Example ln_valid_ideal := ltac:(mpfr_example ln_valid).
Example log10_valid_ideal := ltac:(mpfr_example log10_valid).
Example log2_valid_ideal := ltac:(mpfr_example log2_valid).
Example pow_valid_ideal := ltac:(mpfr_example pow_valid).
Example powi_valid_ideal := ltac:(mpfr_example powi_valid).
Example sin_valid_ideal := ltac:(mpfr_example sin_valid).
Example sinh_valid_ideal := ltac:(mpfr_example sinh_valid).
Example tan_valid_ideal := ltac:(mpfr_example tan_valid).
Example tanh_valid_ideal := ltac:(mpfr_example tanh_valid).
Example dec_acos_valid_ideal := ltac:(mpfr_example dec_acos_valid).
Example dec_acosh_valid_ideal := ltac:(mpfr_example dec_acosh_valid).
Example dec_asin_valid_ideal := ltac:(mpfr_example dec_asin_valid).
Example dec_asinh_valid_ideal := ltac:(mpfr_example dec_asinh_valid).
Example dec_atan_valid_ideal := ltac:(mpfr_example dec_atan_valid).
Example dec_atan2_valid_ideal := ltac:(mpfr_example dec_atan2_valid).
Example dec_atanh_valid_ideal := ltac:(mpfr_example dec_atanh_valid).
Example dec_cos_valid_ideal := ltac:(mpfr_example dec_cos_valid).
Example dec_cosh_valid_ideal := ltac:(mpfr_example dec_cosh_valid).
Example dec_exp_valid_ideal := ltac:(mpfr_example dec_exp_valid).
Example dec_exp10_valid_ideal := ltac:(mpfr_example dec_exp10_valid).
Example dec_exp2_valid_ideal := ltac:(mpfr_example dec_exp2_valid).
Example dec_ln_valid_ideal := ltac:(mpfr_example dec_ln_valid).
Example dec_log10_valid_ideal := ltac:(mpfr_example dec_log10_valid).
Example dec_log2_valid_ideal := ltac:(mpfr_example dec_log2_valid).
Example dec_pow_valid_ideal := ltac:(mpfr_example dec_pow_valid).
Example dec_powi_valid_ideal := ltac:(mpfr_example dec_powi_valid).
Example dec_sin_valid_ideal := ltac:(mpfr_example dec_sin_valid).
Example dec_sinh_valid_ideal := ltac:(mpfr_example dec_sinh_valid).
Example dec_tan_valid_ideal := ltac:(mpfr_example dec_tan_valid).
Example dec_tanh_valid_ideal := ltac:(mpfr_example dec_tanh_valid).
Example mpfr_acos_c_ideal := ltac:(mpfr_example mpfr_acos_c).
Example mpfr_acosh_c_ideal := ltac:(mpfr_example mpfr_acosh_c).
Example mpfr_asin_c_ideal := ltac:(mpfr_example mpfr_asin_c).
Example mpfr_asinh_c_ideal := ltac:(mpfr_example mpfr_asinh_c).
Example mpfr_atan_c_ideal := ltac:(mpfr_example mpfr_atan_c).
Example mpfr_atan2_c_ideal := ltac:(mpfr_example mpfr_atan2_c).
Example mpfr_atanh_c_ideal := ltac:(mpfr_example mpfr_atanh_c).
Example mpfr_cos_c_ideal := ltac:(mpfr_example mpfr_cos_c).
Example mpfr_cosh_c_ideal := ltac:(mpfr_example mpfr_cosh_c).
Example mpfr_exp_c_ideal := ltac:(mpfr_example mpfr_exp_c).
Example mpfr_exp10_c_ideal := ltac:(mpfr_example mpfr_exp10_c).
Example mpfr_exp2_c_ideal := ltac:(mpfr_example mpfr_exp2_c).
Example mpfr_ln_c_ideal := ltac:(mpfr_example mpfr_ln_c).
Example mpfr_log10_c_ideal := ltac:(mpfr_example mpfr_log10_c).
Example mpfr_log2_c_ideal := ltac:(mpfr_example mpfr_log2_c).
Example mpfr_pow_c_ideal := ltac:(mpfr_example mpfr_pow_c).
Example mpfr_pown_c_ideal := ltac:(mpfr_example mpfr_pown_c).
Example mpfr_sin_c_ideal := ltac:(mpfr_example mpfr_sin_c).
Example mpfr_sinh_c_ideal := ltac:(mpfr_example mpfr_sinh_c).
Example mpfr_tan_c_ideal := ltac:(mpfr_example mpfr_tan_c).
Example mpfr_tanh_c_ideal := ltac:(mpfr_example mpfr_tanh_c).
Example mpfr_round_rational_c_ideal := ltac:(mpfr_example mpfr_round_rational_c).

(** The constructors of [made] and [dmade] in [Valid.v] that quantify over
    an MPFR, in their order. *)
Example made_try_from_ninterval_exact_ideal := ltac:(mpfr_example made_try_from_ninterval_exact).
Example made_acos_ideal := ltac:(mpfr_example made_acos).
Example made_acosh_ideal := ltac:(mpfr_example made_acosh).
Example made_asin_ideal := ltac:(mpfr_example made_asin).
Example made_asinh_ideal := ltac:(mpfr_example made_asinh).
Example made_atan_ideal := ltac:(mpfr_example made_atan).
Example made_atan2_ideal := ltac:(mpfr_example made_atan2).
Example made_atanh_ideal := ltac:(mpfr_example made_atanh).
Example made_cos_ideal := ltac:(mpfr_example made_cos).
Example made_cosh_ideal := ltac:(mpfr_example made_cosh).
Example made_exp_ideal := ltac:(mpfr_example made_exp).
Example made_exp10_ideal := ltac:(mpfr_example made_exp10).
Example made_exp2_ideal := ltac:(mpfr_example made_exp2).
Example made_ln_ideal := ltac:(mpfr_example made_ln).
Example made_log10_ideal := ltac:(mpfr_example made_log10).
Example made_log2_ideal := ltac:(mpfr_example made_log2).
Example made_pow_ideal := ltac:(mpfr_example made_pow).
Example made_powi_ideal := ltac:(mpfr_example made_powi).
Example made_sin_ideal := ltac:(mpfr_example made_sin).
Example made_sinh_ideal := ltac:(mpfr_example made_sinh).
Example made_tan_ideal := ltac:(mpfr_example made_tan).
Example made_tanh_ideal := ltac:(mpfr_example made_tanh).
Example dmade_from_dec_ninterval_ideal := ltac:(mpfr_example dmade_from_dec_ninterval).
Example dmade_acos_ideal := ltac:(mpfr_example dmade_acos).
Example dmade_acosh_ideal := ltac:(mpfr_example dmade_acosh).
Example dmade_asin_ideal := ltac:(mpfr_example dmade_asin).
Example dmade_asinh_ideal := ltac:(mpfr_example dmade_asinh).
Example dmade_atan_ideal := ltac:(mpfr_example dmade_atan).
Example dmade_atan2_ideal := ltac:(mpfr_example dmade_atan2).
Example dmade_atanh_ideal := ltac:(mpfr_example dmade_atanh).
Example dmade_cos_ideal := ltac:(mpfr_example dmade_cos).
Example dmade_cosh_ideal := ltac:(mpfr_example dmade_cosh).
Example dmade_exp_ideal := ltac:(mpfr_example dmade_exp).
Example dmade_exp10_ideal := ltac:(mpfr_example dmade_exp10).
Example dmade_exp2_ideal := ltac:(mpfr_example dmade_exp2).
Example dmade_ln_ideal := ltac:(mpfr_example dmade_ln).
Example dmade_log10_ideal := ltac:(mpfr_example dmade_log10).
Example dmade_log2_ideal := ltac:(mpfr_example dmade_log2).
Example dmade_pow_ideal := ltac:(mpfr_example dmade_pow).
Example dmade_powi_ideal := ltac:(mpfr_example dmade_powi).
Example dmade_sin_ideal := ltac:(mpfr_example dmade_sin).
Example dmade_sinh_ideal := ltac:(mpfr_example dmade_sinh).
Example dmade_tan_ideal := ltac:(mpfr_example dmade_tan).
Example dmade_tanh_ideal := ltac:(mpfr_example dmade_tanh).
