(** * The intervals that the proved code makes are [valid]

    The theorems about operations assume that their arguments are
    [valid]. This file shows that every [Interval], and the interval of
    every [DecInterval], that is made from the library's constructors by
    the operations proved here, any number of times, is [valid]. [made]
    and [dmade] say what that is: each constructor below is one place in
    the library that makes a value, or one proved operation. There is no
    constructor for an operation that is not modelled here, such as [pow],
    so [made_valid] does not show that its results, or the intervals
    computed from them, are [valid].

    The constructors of [made] are [Interval::EMPTY], [const_interval!],
    which [Interval::ENTIRE] and the other constants of [Interval] are,
    [Interval::zero], [TryFrom<(f64, f64)>], [try_from_be_bytes] and its
    siblings, [try_from_ninterval_exact], which [interval_exact!] calls,
    the interval of a [dmade] [DecInterval], which
    [DecInterval::interval] returns, and the operations [abs], [ceil],
    [floor], [max], [min], [round], [round_ties_even], [sign], [sqr],
    [sqrt], [trunc], [-x], [x + y], [x - y], [x * y], [mul_add], [recip],
    [x / y], both outputs of [mul_rev_to_pair], [cancel_minus], [cancel_plus],
    [convex_hull], [intersection], and the functions [acos], [acosh],
    [asin], [asinh], [atan], [atanh], [cos], [cosh], [exp], [exp10],
    [exp2], [ln], [log10], [log2], [sin], [sinh], [tan] and [tanh] of
    [src/elementary.rs].
    Those of [dmade] are the constants, [def_com!], [const_dec_interval!],
    [new], [set_dec], [TryFrom<(f64, f64)>], [try_from_be_bytes] and its
    siblings, [From<DecNInterval>], which [FromStr] calls, and the
    decorated versions of the same operations.

    The constructors of the functions of [src/elementary.rs] assume an
    MPFR [m] and an exponent range [emin], [emax] that satisfy the
    hypotheses of [Mpfr.v]: [range_ok], [get_d_ok], and the function's own
    hypothesis, such as [exp_ok]. Those of [tan] also assume that π is
    irrational ([pi_irrational] in [Elementary.v]). *)

From Inari Require Import Model Elementary Mpfr ValidMake ValidSetOp ValidOps
  ValidDecOps ValidElem.

Inductive made : Interval -> Prop :=
  | made_EMPTY : made Interval.EMPTY
  | made_const_interval :
      forall a b, Interval.const_interval_ok a b = true ->
      made (Interval.const_interval a b)
  | made_zero : made Interval.zero
  | made_try_from :
      forall a b x, Interval.try_from a b = Some x -> made x
  | made_try_from_bytes :
      forall a b x, Interval.try_from_bytes a b = Some x -> made x
  | made_try_from_ninterval_exact :
      forall a b i x, Interval.try_from_ninterval_exact a b i = Some x -> made x
  | made_itv : forall d, dmade d -> made (itv d)
  | made_abs : forall x y, made x -> Interval.abs x = Some y -> made y
  | made_ceil : forall x, made x -> made (Interval.ceil x)
  | made_floor : forall x, made x -> made (Interval.floor x)
  | made_max :
      forall has_maximum x y, made x -> made y ->
      made (Interval.max has_maximum x y)
  | made_min :
      forall has_maximum x y, made x -> made y ->
      made (Interval.min has_maximum x y)
  | made_round : forall x, made x -> made (Interval.round x)
  | made_round_ties_even : forall x, made x -> made (Interval.round_ties_even x)
  | made_sign : forall x, made x -> made (Interval.sign x)
  | made_sqr :
      forall has_fma x y, made x -> Interval.sqr has_fma x = Some y -> made y
  | made_sqrt :
      forall has_fma x y, made x -> Interval.sqrt has_fma x = Some y -> made y
  | made_trunc : forall x, made x -> made (Interval.trunc x)
  | made_neg : forall x, made x -> made (Interval.neg x)
  | made_add :
      forall x y z, made x -> made y -> Interval.add x y = Some z -> made z
  | made_sub :
      forall x y z, made x -> made y -> Interval.sub x y = Some z -> made z
  | made_mul :
      forall has_fma x y z, made x -> made y ->
      Interval.mul has_fma x y = Some z -> made z
  | made_mul_add :
      forall has_fma x y z w, made x -> made y -> made z ->
      Interval.mul_add has_fma x y z = Some w -> made w
  | made_recip :
      forall has_fma x y, made x -> Interval.recip has_fma x = Some y -> made y
  | made_div :
      forall has_fma x y z, made x -> made y ->
      Interval.div has_fma x y = Some z -> made z
  | made_mul_rev_to_pair1 :
      forall has_fma x y u v, made x -> made y ->
      Interval.mul_rev_to_pair has_fma x y = Some (u, v) -> made u
  | made_mul_rev_to_pair2 :
      forall has_fma x y u v, made x -> made y ->
      Interval.mul_rev_to_pair has_fma x y = Some (u, v) -> made v
  | made_cancel_minus :
      forall x y z, made x -> made y -> Interval.cancel_minus x y = Some z -> made z
  | made_cancel_plus :
      forall x y z, made x -> made y -> Interval.cancel_plus x y = Some z -> made z
  | made_convex_hull :
      forall x y, made x -> made y -> made (Interval.convex_hull x y)
  | made_intersection :
      forall x y, made x -> made y -> made (Interval.intersection x y)
  | made_acos :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      acos_ok emin emax m -> made x -> made (Interval.acos m x)
  | made_acosh :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      acosh_ok emin emax m -> made x -> made (Interval.acosh m x)
  | made_asin :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      asin_ok emin emax m -> made x -> made (Interval.asin m x)
  | made_asinh :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      asinh_ok emin emax m -> made x -> made (Interval.asinh m x)
  | made_atan :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      atan_ok emin emax m -> made x -> made (Interval.atan m x)
  | made_atanh :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      atanh_ok emin emax m -> made x -> made (Interval.atanh m x)
  | made_cos :
      forall emin emax m has_fma first x y, range_ok emin emax ->
      get_d_ok emin emax m -> cos_ok emin emax m -> made x ->
      Interval.cos m has_fma first x = Some y -> made y
  | made_cosh :
      forall emin emax m first x, range_ok emin emax -> get_d_ok emin emax m ->
      cosh_ok emin emax m -> made x -> made (Interval.cosh m first x)
  | made_exp :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      exp_ok emin emax m -> made x -> made (Interval.exp m x)
  | made_exp10 :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      exp10_ok emin emax m -> made x -> made (Interval.exp10 m x)
  | made_exp2 :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      exp2_ok emin emax m -> made x -> made (Interval.exp2 m x)
  | made_ln :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      ln_ok emin emax m -> made x -> made (Interval.ln m x)
  | made_log10 :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      log10_ok emin emax m -> made x -> made (Interval.log10 m x)
  | made_log2 :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      log2_ok emin emax m -> made x -> made (Interval.log2 m x)
  | made_sin :
      forall emin emax m has_fma first x y, range_ok emin emax ->
      get_d_ok emin emax m -> sin_ok emin emax m -> made x ->
      Interval.sin m has_fma first x = Some y -> made y
  | made_sinh :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      sinh_ok emin emax m -> made x -> made (Interval.sinh m x)
  | made_tan :
      forall emin emax m has_fma x y, range_ok emin emax -> get_d_ok emin emax m ->
      tan_ok emin emax m -> pi_irrational -> made x ->
      Interval.tan m has_fma x = Some y -> made y
  | made_tanh :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      tanh_ok emin emax m -> made x -> made (Interval.tanh m x)
with dmade : DecInterval -> Prop :=
  | dmade_EMPTY : dmade DecInterval.EMPTY
  | dmade_NAI : dmade DecInterval.NAI
  | dmade_ENTIRE : dmade DecInterval.ENTIRE
  | dmade_def_com :
      forall a b, Interval.const_interval_ok a b = true ->
      dmade (DecInterval.def_com a b)
  | dmade_const_dec_interval :
      forall a b, Interval.const_interval_ok a b = true ->
      dmade (DecInterval.const_dec_interval a b)
  | dmade_new : forall x, made x -> dmade (DecInterval.new x)
  | dmade_set_dec : forall x d, made x -> dmade (DecInterval.set_dec x d)
  | dmade_try_from :
      forall a b z, DecInterval.try_from a b = Some z -> dmade z
  | dmade_try_from_bytes :
      forall a b c z, DecInterval.try_from_bytes a b c = Some z -> dmade z
  | dmade_from_dec_ninterval :
      forall a b o d, dmade (DecInterval.from_dec_ninterval a b o d)
  | dmade_abs : forall x z, dmade x -> DecInterval.abs x = Some z -> dmade z
  | dmade_ceil : forall x, dmade x -> dmade (DecInterval.ceil x)
  | dmade_floor : forall x, dmade x -> dmade (DecInterval.floor x)
  | dmade_max :
      forall has_maximum x y, dmade x -> dmade y ->
      dmade (DecInterval.max has_maximum x y)
  | dmade_min :
      forall has_maximum x y, dmade x -> dmade y ->
      dmade (DecInterval.min has_maximum x y)
  | dmade_round : forall x, dmade x -> dmade (DecInterval.round x)
  | dmade_round_ties_even :
      forall x, dmade x -> dmade (DecInterval.round_ties_even x)
  | dmade_sign : forall x, dmade x -> dmade (DecInterval.sign x)
  | dmade_sqr :
      forall has_fma x z, dmade x -> DecInterval.sqr has_fma x = Some z ->
      dmade z
  | dmade_sqrt :
      forall has_fma x z, dmade x -> DecInterval.sqrt has_fma x = Some z ->
      dmade z
  | dmade_trunc : forall x, dmade x -> dmade (DecInterval.trunc x)
  | dmade_neg : forall x, dmade x -> dmade (DecInterval.neg x)
  | dmade_add :
      forall x y z, dmade x -> dmade y -> DecInterval.add x y = Some z ->
      dmade z
  | dmade_sub :
      forall x y z, dmade x -> dmade y -> DecInterval.sub x y = Some z ->
      dmade z
  | dmade_mul :
      forall has_fma x y z, dmade x -> dmade y ->
      DecInterval.mul has_fma x y = Some z -> dmade z
  | dmade_mul_add :
      forall has_fma x y z w, dmade x -> dmade y -> dmade z ->
      DecInterval.mul_add has_fma x y z = Some w -> dmade w
  | dmade_recip :
      forall has_fma x z, dmade x -> DecInterval.recip has_fma x = Some z ->
      dmade z
  | dmade_div :
      forall has_fma x y z, dmade x -> dmade y ->
      DecInterval.div has_fma x y = Some z -> dmade z
  | dmade_mul_rev_to_pair1 :
      forall has_fma x y u v, dmade x -> dmade y ->
      DecInterval.mul_rev_to_pair has_fma x y = Some (u, v) -> dmade u
  | dmade_mul_rev_to_pair2 :
      forall has_fma x y u v, dmade x -> dmade y ->
      DecInterval.mul_rev_to_pair has_fma x y = Some (u, v) -> dmade v
  | dmade_cancel_minus :
      forall x y z, dmade x -> dmade y -> DecInterval.cancel_minus x y = Some z ->
      dmade z
  | dmade_cancel_plus :
      forall x y z, dmade x -> dmade y -> DecInterval.cancel_plus x y = Some z ->
      dmade z
  | dmade_convex_hull :
      forall x y, dmade x -> dmade y -> dmade (DecInterval.convex_hull x y)
  | dmade_intersection :
      forall x y, dmade x -> dmade y -> dmade (DecInterval.intersection x y)
  | dmade_acos :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      acos_ok emin emax m -> dmade x -> dmade (DecInterval.acos m x)
  | dmade_acosh :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      acosh_ok emin emax m -> dmade x -> dmade (DecInterval.acosh m x)
  | dmade_asin :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      asin_ok emin emax m -> dmade x -> dmade (DecInterval.asin m x)
  | dmade_asinh :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      asinh_ok emin emax m -> dmade x -> dmade (DecInterval.asinh m x)
  | dmade_atan :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      atan_ok emin emax m -> dmade x -> dmade (DecInterval.atan m x)
  | dmade_atanh :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      atanh_ok emin emax m -> dmade x -> dmade (DecInterval.atanh m x)
  | dmade_cos :
      forall emin emax m has_fma first x y, range_ok emin emax ->
      get_d_ok emin emax m -> cos_ok emin emax m -> dmade x ->
      DecInterval.cos m has_fma first x = Some y -> dmade y
  | dmade_cosh :
      forall emin emax m first x, range_ok emin emax -> get_d_ok emin emax m ->
      cosh_ok emin emax m -> dmade x -> dmade (DecInterval.cosh m first x)
  | dmade_exp :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      exp_ok emin emax m -> dmade x -> dmade (DecInterval.exp m x)
  | dmade_exp10 :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      exp10_ok emin emax m -> dmade x -> dmade (DecInterval.exp10 m x)
  | dmade_exp2 :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      exp2_ok emin emax m -> dmade x -> dmade (DecInterval.exp2 m x)
  | dmade_ln :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      ln_ok emin emax m -> dmade x -> dmade (DecInterval.ln m x)
  | dmade_log10 :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      log10_ok emin emax m -> dmade x -> dmade (DecInterval.log10 m x)
  | dmade_log2 :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      log2_ok emin emax m -> dmade x -> dmade (DecInterval.log2 m x)
  | dmade_sin :
      forall emin emax m has_fma first x y, range_ok emin emax ->
      get_d_ok emin emax m -> sin_ok emin emax m -> dmade x ->
      DecInterval.sin m has_fma first x = Some y -> dmade y
  | dmade_sinh :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      sinh_ok emin emax m -> dmade x -> dmade (DecInterval.sinh m x)
  | dmade_tan :
      forall emin emax m has_fma x y, range_ok emin emax -> get_d_ok emin emax m ->
      tan_ok emin emax m -> pi_irrational -> dmade x ->
      DecInterval.tan m has_fma x = Some y -> dmade y
  | dmade_tanh :
      forall emin emax m x, range_ok emin emax -> get_d_ok emin emax m ->
      tanh_ok emin emax m -> dmade x -> dmade (DecInterval.tanh m x).

(** Induction on [made] and [dmade] together, for properties that do not
    depend on the derivation. *)
Scheme made_min_ind := Minimality for made Sort Prop
  with dmade_min_ind := Minimality for dmade Sort Prop.
Combined Scheme made_dmade_ind from made_min_ind, dmade_min_ind.

(** Every [made] interval, and the interval of every [dmade] decorated
    interval, is [valid]. *)
Theorem made_valid :
  (forall x, made x -> valid x) /\ (forall d, dmade d -> valid (itv d)).
Proof.
apply (made_dmade_ind (fun x => valid x) (fun d => valid (itv d))).
- exact EMPTY_valid.
- exact const_interval_valid.
- exact zero_valid.
- exact try_from_valid.
- exact try_from_bytes_valid.
- exact try_from_ninterval_exact_valid.
- intros d _ H. exact H.
- intros x y _ Hx. exact (abs_valid x y Hx).
- intros x _ Hx. exact (ceil_valid x Hx).
- intros x _ Hx. exact (floor_valid x Hx).
- intros m x y _ Hx _ Hy. exact (max_valid m x y Hx Hy).
- intros m x y _ Hx _ Hy. exact (min_valid m x y Hx Hy).
- intros x _ Hx. exact (round_valid x Hx).
- intros x _ Hx. exact (round_ties_even_valid x Hx).
- intros x _ Hx. exact (sign_valid x Hx).
- intros f x y _ Hx. exact (sqr_valid f x y Hx).
- intros f x y _ Hx. exact (sqrt_valid f x y Hx).
- intros x _ Hx. exact (trunc_valid x Hx).
- intros x _ Hx. exact (neg_valid x Hx).
- intros x y z _ Hx _ Hy. exact (add_valid x y z Hx Hy).
- intros x y z _ Hx _ Hy. exact (sub_valid x y z Hx Hy).
- intros f x y z _ Hx _ Hy. exact (mul_valid f x y z Hx Hy).
- intros f x y z w _ Hx _ Hy _ Hz. exact (mul_add_valid f x y z w Hx Hy Hz).
- intros f x y _ Hx. exact (recip_valid f x y Hx).
- intros f x y z _ Hx _ Hy. exact (div_valid f x y z Hx Hy).
- intros f x y u v _ Hx _ Hy E. exact (proj1 (mul_rev_to_pair_valid f x y u v Hx Hy E)).
- intros f x y u v _ Hx _ Hy E. exact (proj2 (mul_rev_to_pair_valid f x y u v Hx Hy E)).
- intros x y z _ Hx _ Hy. exact (cancel_minus_valid x y z Hx Hy).
- intros x y z _ Hx _ Hy. exact (cancel_plus_valid x y z Hx Hy).
- intros x y _ Hx _ Hy. exact (convex_hull_valid x y Hx Hy).
- intros x y _ Hx _ Hy. exact (intersection_valid x y Hx Hy).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (acos_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (acosh_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (asin_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (asinh_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (atan_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (atanh_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m f first x y Hr Hg Ho _ Hx E.
  exact (cos_valid emin emax m f first x y Hr Hg Ho Hx E).
- intros emin emax m first x Hr Hg Ho _ Hx.
  exact (cosh_valid emin emax m first x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (exp_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (exp10_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (exp2_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (ln_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (log10_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (log2_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m f first x y Hr Hg Ho _ Hx E.
  exact (sin_valid emin emax m f first x y Hr Hg Ho Hx E).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (sinh_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m f x y Hr Hg Ho Hpi _ Hx E.
  exact (tan_valid emin emax m f x y Hr Hg Ho Hpi Hx E).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (tanh_valid emin emax m x Hr Hg Ho Hx).
- exact (proj1 dec_constants_valid).
- exact (proj1 (proj2 dec_constants_valid)).
- exact (proj2 (proj2 dec_constants_valid)).
- exact def_com_valid.
- exact const_dec_interval_valid.
- intros x _ Hx. exact (new_valid x Hx).
- intros x d _ Hx. exact (set_dec_valid x d Hx).
- exact dec_try_from_valid.
- exact dec_try_from_bytes_valid.
- exact from_dec_ninterval_valid.
- intros x z _ Hx. exact (dec_abs_valid x z Hx).
- intros x _ Hx. exact (dec_ceil_valid x Hx).
- intros x _ Hx. exact (dec_floor_valid x Hx).
- intros m x y _ Hx _ Hy. exact (dec_max_valid m x y Hx Hy).
- intros m x y _ Hx _ Hy. exact (dec_min_valid m x y Hx Hy).
- intros x _ Hx. exact (dec_round_valid x Hx).
- intros x _ Hx. exact (dec_round_ties_even_valid x Hx).
- intros x _ Hx. exact (dec_sign_valid x Hx).
- intros f x z _ Hx. exact (dec_sqr_valid f x z Hx).
- intros f x z _ Hx. exact (dec_sqrt_valid f x z Hx).
- intros x _ Hx. exact (dec_trunc_valid x Hx).
- intros x _ Hx. exact (dec_neg_valid x Hx).
- intros x y z _ Hx _ Hy. exact (dec_add_valid x y z Hx Hy).
- intros x y z _ Hx _ Hy. exact (dec_sub_valid x y z Hx Hy).
- intros f x y z _ Hx _ Hy. exact (dec_mul_valid f x y z Hx Hy).
- intros f x y z w _ Hx _ Hy _ Hz. exact (dec_mul_add_valid f x y z w Hx Hy Hz).
- intros f x z _ Hx. exact (dec_recip_valid f x z Hx).
- intros f x y z _ Hx _ Hy. exact (dec_div_valid f x y z Hx Hy).
- intros f x y u v _ Hx _ Hy E.
  exact (proj1 (dec_mul_rev_to_pair_valid f x y u v Hx Hy E)).
- intros f x y u v _ Hx _ Hy E.
  exact (proj2 (dec_mul_rev_to_pair_valid f x y u v Hx Hy E)).
- intros x y z _ Hx _ Hy. exact (dec_cancel_minus_valid x y z Hx Hy).
- intros x y z _ Hx _ Hy. exact (dec_cancel_plus_valid x y z Hx Hy).
- intros x y _ Hx _ Hy. exact (dec_convex_hull_valid x y Hx Hy).
- intros x y _ Hx _ Hy. exact (dec_intersection_valid x y Hx Hy).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (dec_acos_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (dec_acosh_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (dec_asin_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (dec_asinh_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (dec_atan_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (dec_atanh_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m f first x y Hr Hg Ho _ Hx E.
  exact (dec_cos_valid emin emax m f first x y Hr Hg Ho Hx E).
- intros emin emax m first x Hr Hg Ho _ Hx.
  exact (dec_cosh_valid emin emax m first x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (dec_exp_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (dec_exp10_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (dec_exp2_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (dec_ln_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (dec_log10_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (dec_log2_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m f first x y Hr Hg Ho _ Hx E.
  exact (dec_sin_valid emin emax m f first x y Hr Hg Ho Hx E).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (dec_sinh_valid emin emax m x Hr Hg Ho Hx).
- intros emin emax m f x y Hr Hg Ho Hpi _ Hx E.
  exact (dec_tan_valid emin emax m f x y Hr Hg Ho Hpi Hx E).
- intros emin emax m x Hr Hg Ho _ Hx.
  exact (dec_tanh_valid emin emax m x Hr Hg Ho Hx).
Qed.
