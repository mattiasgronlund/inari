(** The axioms that the theorems depend on. [make] fails if this prints
    any axiom that is not listed in [AXIOMS] in the [Makefile]. *)

From Inari Require Import Encoding AddRu SubRu TwoProduct MulRu DivRu SqrtRdRu
  AddOdd EmulatedFma MulAddRuSlow MulAddRu.

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
