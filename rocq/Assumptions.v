(** The axioms that the theorems depend on. [make] fails if this prints
    any axiom that is not listed in [AXIOMS] in the [Makefile].

    The [Example]s of [MpfrExamples.v] are not printed: each one applies a
    theorem printed here, or a constructor of [made] or [dmade], of which
    [made_valid] is printed here, to [ideal emin emax] and to proofs that
    the tactic [mpfr_example] builds from [range_ok] and [ideal_mpfr_ok],
    which is printed here too. At the end, two [Search]es write the names
    from which [make] takes those that must have an [Example] there. *)

From Inari Require Import Encoding AddRu SubRu TwoProduct MulRu DivRu SqrtRdRu AddOdd
  EmulatedFma MulAddRuSlow MulAddRu Integer RoundTiesEven Trunc Round Sign Abs MaxMin
  DecBinary DecTernary DecMaxMin Neg AddSub Mul MulAdd Sqrt Sqr Recip Div ComCommon
  MulRevSets MulRev CancelSpec Cancel MpfrRound ElemDec ClosedDom Elem Atanh Cosh
  PiBounds PiIrrational TrigQuad TrigCount TrigCert Cos Sin Tan Dom2 Pow Powi AtanReal
  PiTight Atan2 ParseScale ParseRound ParseHull ParseExact ParseDec ConstTight
  ConstPi ConstInv ConstLn ConstLog ValidMake ValidSetOp ValidOps ValidDecOps
  ValidElem Valid MpfrIdeal IdealRound IdealGetD IdealElem IdealPow IdealAtan2
  MpfrConsistent Contract OfPointCore OfPoint OfPointElem OfPointPow MpfrPoint
  PointTheorems.

Print Assumptions add1_ru_fast_correct.
Print Assumptions add_ru_correct.
Print Assumptions sub1_ru_correct.
Print Assumptions sub_ru_correct.
Print Assumptions two_prod_err_correct.
Print Assumptions mul1_ru_fast_correct.
Print Assumptions mul1_ru_slow_correct.
Print Assumptions mul1_ru_tiny_correct.
Print Assumptions mul_ru_impl_correct.
Print Assumptions mul_ru_correct.
Print Assumptions div1_ru_fast_correct.
Print Assumptions div1_ru_slow_correct.
Print Assumptions div_ru_impl_correct.
Print Assumptions div_ru_correct.
Print Assumptions sqrt1_rd_impl_correct.
Print Assumptions sqrt1_ru_impl_correct.
Print Assumptions sqrt1_rd_correct.
Print Assumptions sqrt1_ru_correct.
Print Assumptions sqrt_rd_ru_correct.
Print Assumptions add_odd_correct.
Print Assumptions mul_add1_rn_emulated_correct.
Print Assumptions mul_add1_ru_fast_correct.
Print Assumptions mul_add1_ru_slow_correct.
Print Assumptions mul_add_ru_impl_correct.
Print Assumptions mul_add_ru_correct.
Print Assumptions step_up_no_wrap.
Print Assumptions floor_correct.
Print Assumptions dec_floor_correct.
Print Assumptions ceil_correct.
Print Assumptions dec_ceil_correct.
Print Assumptions round_ties_even1_correct.
Print Assumptions round_correct.
Print Assumptions dec_round_correct.
Print Assumptions round_ties_even_correct.
Print Assumptions dec_round_ties_even_correct.
Print Assumptions trunc_correct.
Print Assumptions dec_trunc_correct.
Print Assumptions sign_correct.
Print Assumptions dec_sign_correct.
Print Assumptions classify_defined.
Print Assumptions abs_correct.
Print Assumptions dec_abs_correct.
Print Assumptions max_correct.
Print Assumptions min_correct.
Print Assumptions dec_max_correct.
Print Assumptions dec_min_correct.
Print Assumptions set_dec_correct.
Print Assumptions neg_correct.
Print Assumptions dec_neg_correct.
Print Assumptions add_correct.
Print Assumptions sub_correct.
Print Assumptions dec_add_correct.
Print Assumptions dec_sub_correct.
Print Assumptions mul_correct.
Print Assumptions dec_mul_correct.
Print Assumptions mul_add_correct.
Print Assumptions dec_mul_add_correct.
Print Assumptions sqrt_correct.
Print Assumptions dec_sqrt_correct.
Print Assumptions sqr_correct.
Print Assumptions dec_sqr_correct.
Print Assumptions recip_correct.
Print Assumptions dec_recip_correct.
Print Assumptions div_correct.
Print Assumptions dec_div_correct.
Print Assumptions mul_rev_one_component.
Print Assumptions mul_rev_to_pair_correct.
Print Assumptions dec_mul_rev_to_pair_correct.
Print Assumptions cancel_result_empty.
Print Assumptions cancel_result_hull.
Print Assumptions cancel_minus_correct.
Print Assumptions cancel_plus_correct.
Print Assumptions dec_cancel_minus_correct.
Print Assumptions dec_cancel_plus_correct.
Print Assumptions mpfr_fn_round.
Print Assumptions asinh_correct.
Print Assumptions dec_asinh_correct.
Print Assumptions atan_correct.
Print Assumptions dec_atan_correct.
Print Assumptions exp_correct.
Print Assumptions dec_exp_correct.
Print Assumptions exp10_correct.
Print Assumptions dec_exp10_correct.
Print Assumptions exp2_correct.
Print Assumptions dec_exp2_correct.
Print Assumptions sinh_correct.
Print Assumptions dec_sinh_correct.
Print Assumptions tanh_correct.
Print Assumptions dec_tanh_correct.
Print Assumptions ln_correct.
Print Assumptions dec_ln_correct.
Print Assumptions log10_correct.
Print Assumptions dec_log10_correct.
Print Assumptions log2_correct.
Print Assumptions dec_log2_correct.
Print Assumptions asin_correct.
Print Assumptions dec_asin_correct.
Print Assumptions acosh_correct.
Print Assumptions dec_acosh_correct.
Print Assumptions acos_correct.
Print Assumptions dec_acos_correct.
Print Assumptions atanh_correct.
Print Assumptions dec_atanh_correct.
Print Assumptions cosh_correct.
Print Assumptions dec_cosh_correct.
Print Assumptions PI_bounds.
Print Assumptions pi_irrational.
Print Assumptions quadrant_correct.
Print Assumptions quadrants_correct.
Print Assumptions floors_exact_ok.
Print Assumptions trig_wide.
Print Assumptions cos_encloses.
Print Assumptions cos_correct.
Print Assumptions dec_cos_correct.
Print Assumptions sin_encloses.
Print Assumptions sin_correct.
Print Assumptions dec_sin_correct.
Print Assumptions tan_encloses.
Print Assumptions tan_correct.
Print Assumptions dec_tan_correct.
Print Assumptions image2_set_prod.
Print Assumptions continue_in2_set_prod.
Print Assumptions p2_set_prod.
Print Assumptions strongest2_set_prod.
Print Assumptions image2_set_all.
Print Assumptions p2_set_all.
Print Assumptions strongest2_set_all.
Print Assumptions elem2_set_dec_correct.
Print Assumptions elem_dec2_impl_correct.
Print Assumptions elem_set_dec_correct.
Print Assumptions set_dec_correct3.
Print Assumptions pow_correct.
Print Assumptions dec_pow_correct.
Print Assumptions powi_correct.
Print Assumptions dec_powi_correct.
Print Assumptions Ratan2_range.
Print Assumptions Ratan2_polar.
Print Assumptions Ratan2_polar_unique.
Print Assumptions PI_up.
Print Assumptions PI_dn.
Print Assumptions FRAC_PI_2_up.
Print Assumptions FRAC_PI_2_dn.
Print Assumptions atan2_correct.
Print Assumptions dec_atan2_correct.
Print Assumptions scale_correct.
Print Assumptions rational_to_f64_correct.
Print Assumptions number_to_f64_correct.
Print Assumptions number_neg_correct.
Print Assumptions ninterval_ok_set.
Print Assumptions bounds_tightest.
Print Assumptions try_from_ninterval_exact_correct.
Print Assumptions dn_new_ok.
Print Assumptions dn_NAI_ok.
Print Assumptions dn_set_dec_ok.
Print Assumptions dn_decorated_ok.
Print Assumptions from_dec_ninterval_correct.
Print Assumptions from_ninterval_correct.
Print Assumptions from_ninterval_new.
Print Assumptions E_tightest.
Print Assumptions FRAC_1_PI_tightest.
Print Assumptions FRAC_1_SQRT_2_tightest.
Print Assumptions FRAC_2_PI_tightest.
Print Assumptions FRAC_2_SQRT_PI_tightest.
Print Assumptions FRAC_PI_2_tightest.
Print Assumptions FRAC_PI_3_tightest.
Print Assumptions FRAC_PI_4_tightest.
Print Assumptions FRAC_PI_6_tightest.
Print Assumptions FRAC_PI_8_tightest.
Print Assumptions LN_10_tightest.
Print Assumptions LN_2_tightest.
Print Assumptions LOG10_2_tightest.
Print Assumptions LOG10_E_tightest.
Print Assumptions LOG2_10_tightest.
Print Assumptions LOG2_E_tightest.
Print Assumptions PI_tightest.
Print Assumptions SQRT_2_tightest.
Print Assumptions TAU_tightest.
Print Assumptions com_strongest0.
Print Assumptions ENTIRE_dec_correct.
Print Assumptions EMPTY_dec_correct.
Print Assumptions NAI_dec_correct.
Print Assumptions new_com_common.
Print Assumptions set_dec_com_common.
Print Assumptions constants_com_common.
Print Assumptions def_com_com_common.
Print Assumptions def_com_ok_bounds.
Print Assumptions set_op_com_common.
Print Assumptions try_from_bytes_com_common.
Print Assumptions const_dec_interval_com_common.
Print Assumptions EMPTY_valid.
Print Assumptions const_interval_valid.
Print Assumptions ENTIRE_valid.
Print Assumptions zero_valid.
Print Assumptions with_infsup_raw_valid.
Print Assumptions try_from_valid.
Print Assumptions try_from_bytes_valid.
Print Assumptions try_from_ninterval_exact_valid.
Print Assumptions new_valid.
Print Assumptions set_dec_valid.
Print Assumptions dec_constants_valid.
Print Assumptions def_com_valid.
Print Assumptions const_dec_interval_valid.
Print Assumptions dec_try_from_valid.
Print Assumptions dec_try_from_bytes_valid.
Print Assumptions from_dec_ninterval_valid.
Print Assumptions convex_hull_valid.
Print Assumptions intersection_valid.
Print Assumptions floor_valid.
Print Assumptions ceil_valid.
Print Assumptions round_valid.
Print Assumptions round_ties_even_valid.
Print Assumptions trunc_valid.
Print Assumptions sign_valid.
Print Assumptions neg_valid.
Print Assumptions abs_valid.
Print Assumptions max_valid.
Print Assumptions min_valid.
Print Assumptions add_valid.
Print Assumptions sub_valid.
Print Assumptions mul_valid.
Print Assumptions div_valid.
Print Assumptions sqr_valid.
Print Assumptions sqrt_valid.
Print Assumptions recip_valid.
Print Assumptions mul_rev_to_pair_valid.
Print Assumptions cancel_minus_valid.
Print Assumptions cancel_plus_valid.
Print Assumptions acos_valid.
Print Assumptions acosh_valid.
Print Assumptions asin_valid.
Print Assumptions asinh_valid.
Print Assumptions atan_valid.
Print Assumptions atan2_valid.
Print Assumptions atanh_valid.
Print Assumptions cos_valid.
Print Assumptions cosh_valid.
Print Assumptions exp_valid.
Print Assumptions exp10_valid.
Print Assumptions exp2_valid.
Print Assumptions ln_valid.
Print Assumptions log10_valid.
Print Assumptions log2_valid.
Print Assumptions pow_valid.
Print Assumptions powi_valid.
Print Assumptions sin_valid.
Print Assumptions sinh_valid.
Print Assumptions tan_valid.
Print Assumptions tanh_valid.
Print Assumptions dec_floor_valid.
Print Assumptions dec_ceil_valid.
Print Assumptions dec_round_valid.
Print Assumptions dec_round_ties_even_valid.
Print Assumptions dec_trunc_valid.
Print Assumptions dec_sign_valid.
Print Assumptions dec_neg_valid.
Print Assumptions dec_abs_valid.
Print Assumptions dec_max_valid.
Print Assumptions dec_min_valid.
Print Assumptions dec_add_valid.
Print Assumptions dec_sub_valid.
Print Assumptions dec_mul_valid.
Print Assumptions dec_div_valid.
Print Assumptions dec_sqr_valid.
Print Assumptions dec_sqrt_valid.
Print Assumptions dec_recip_valid.
Print Assumptions dec_mul_rev_to_pair_valid.
Print Assumptions dec_cancel_minus_valid.
Print Assumptions dec_cancel_plus_valid.
Print Assumptions dec_acos_valid.
Print Assumptions dec_acosh_valid.
Print Assumptions dec_asin_valid.
Print Assumptions dec_asinh_valid.
Print Assumptions dec_atan_valid.
Print Assumptions dec_atan2_valid.
Print Assumptions dec_atanh_valid.
Print Assumptions dec_cos_valid.
Print Assumptions dec_cosh_valid.
Print Assumptions dec_exp_valid.
Print Assumptions dec_exp10_valid.
Print Assumptions dec_exp2_valid.
Print Assumptions dec_ln_valid.
Print Assumptions dec_log10_valid.
Print Assumptions dec_log2_valid.
Print Assumptions dec_pow_valid.
Print Assumptions dec_powi_valid.
Print Assumptions dec_sin_valid.
Print Assumptions dec_sinh_valid.
Print Assumptions dec_tan_valid.
Print Assumptions dec_tanh_valid.
Print Assumptions dec_convex_hull_valid.
Print Assumptions dec_intersection_valid.
Print Assumptions made_valid.
Print Assumptions round_mpfr_correct.
Print Assumptions ideal_get_d_ok.
Print Assumptions ideal_acos_ok.
Print Assumptions ideal_acosh_ok.
Print Assumptions ideal_asin_ok.
Print Assumptions ideal_asinh_ok.
Print Assumptions ideal_atan_ok.
Print Assumptions ideal_atanh_ok.
Print Assumptions ideal_cos_ok.
Print Assumptions ideal_cosh_ok.
Print Assumptions ideal_exp_ok.
Print Assumptions ideal_exp10_ok.
Print Assumptions ideal_exp2_ok.
Print Assumptions ideal_ln_ok.
Print Assumptions ideal_log10_ok.
Print Assumptions ideal_log2_ok.
Print Assumptions ideal_sin_ok.
Print Assumptions ideal_sinh_ok.
Print Assumptions ideal_tan_ok.
Print Assumptions ideal_tanh_ok.
Print Assumptions ideal_pow_ok.
Print Assumptions ideal_pown_ok.
Print Assumptions ideal_atan2_ok.
Print Assumptions ideal_mpfr_ok.
Print Assumptions mpfr_ok_consistent.
Print Assumptions mpfr_ok_default.

(** The contract of [Contract.v]. [of_point p], the MPFR functions made
    of a record [point] [p], gives back [p] by [mpfr_point]. At the
    exponent range of [f64], it satisfies [get_d_ok] and each [<f>_ok] of
    [Mpfr.v] where the field of [p] satisfies [<f>_c]. [mpfr_point m]
    satisfies each [<f>_c] where [m] satisfies [get_d_ok] and [<f>_ok],
    at an exponent range with [range_ok]. Last, [exp_correct] stated for
    every record [point] whose fields satisfy the parts of [Contract.v]
    that it needs ([PointTheorems.v]). *)
Print Assumptions mpfr_point_of_point.
Print Assumptions of_point_get_d_ok.
Print Assumptions of_point_acos_ok.
Print Assumptions of_point_acosh_ok.
Print Assumptions of_point_asin_ok.
Print Assumptions of_point_asinh_ok.
Print Assumptions of_point_atan_ok.
Print Assumptions of_point_atanh_ok.
Print Assumptions of_point_cos_ok.
Print Assumptions of_point_cosh_ok.
Print Assumptions of_point_exp_ok.
Print Assumptions of_point_exp10_ok.
Print Assumptions of_point_exp2_ok.
Print Assumptions of_point_ln_ok.
Print Assumptions of_point_log10_ok.
Print Assumptions of_point_log2_ok.
Print Assumptions of_point_sin_ok.
Print Assumptions of_point_sinh_ok.
Print Assumptions of_point_tan_ok.
Print Assumptions of_point_tanh_ok.
Print Assumptions of_point_atan2_ok.
Print Assumptions of_point_pow_ok.
Print Assumptions of_point_pown_ok.
Print Assumptions mpfr_acos_c.
Print Assumptions mpfr_acosh_c.
Print Assumptions mpfr_asin_c.
Print Assumptions mpfr_asinh_c.
Print Assumptions mpfr_atan_c.
Print Assumptions mpfr_atan2_c.
Print Assumptions mpfr_atanh_c.
Print Assumptions mpfr_cos_c.
Print Assumptions mpfr_cosh_c.
Print Assumptions mpfr_exp_c.
Print Assumptions mpfr_exp10_c.
Print Assumptions mpfr_exp2_c.
Print Assumptions mpfr_ln_c.
Print Assumptions mpfr_log10_c.
Print Assumptions mpfr_log2_c.
Print Assumptions mpfr_pow_c.
Print Assumptions mpfr_pown_c.
Print Assumptions mpfr_sin_c.
Print Assumptions mpfr_sinh_c.
Print Assumptions mpfr_tan_c.
Print Assumptions mpfr_tanh_c.
Print Assumptions exp_correct_point.

(** The names whose types quantify over an MPFR anywhere, and those of
    them that [Valid.v] declares, for the check of [MpfrExamples.v] in the
    [Makefile]. They are searched here, as this file imports every module
    whose theorems it prints, so that [Search] gives their short names.
    By default, [Search] hides the names whose qualified name contains
    [Private_], [_subproof] or [_subterm], such as those of the lemmas
    that [abstract] makes. The first line below has it show them too. *)
Remove Search Blacklist "Private_" "_subproof" "_subterm".
Redirect "MpfrSearch" Search (forall _ : Model.mpfr, _).
Redirect "MpfrSearchValid" Search (forall _ : Model.mpfr, _) inside Valid.
