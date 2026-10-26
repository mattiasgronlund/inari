(** The axioms that the theorems depend on. [make] fails if this prints
    any axiom that is not listed in [AXIOMS] in the [Makefile]. *)

From Inari Require Import Encoding AddRu SubRu TwoProduct MulRu DivRu SqrtRdRu
  AddOdd EmulatedFma MulAddRuSlow MulAddRu Integer RoundTiesEven Trunc Round Sign
  Abs MaxMin DecBinary DecMaxMin Neg AddSub.

Print Assumptions add1_ru_fast_correct.
Print Assumptions add_ru_correct.
Print Assumptions sub1_ru_correct.
Print Assumptions sub_ru_correct.
Print Assumptions two_prod_err_correct.
Print Assumptions mul1_ru_fast_correct.
Print Assumptions mul1_ru_slow_correct.
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
