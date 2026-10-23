(** The axioms that the theorems depend on. [make] fails if this prints
    any axiom that is not listed in [AXIOMS] in the [Makefile]. *)

From Inari Require Import Encoding AddRu.

Print Assumptions add1_ru_fast_correct.
Print Assumptions step_up_no_wrap.
