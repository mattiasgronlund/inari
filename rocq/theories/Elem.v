(** * The elementary functions of intervals and decorated intervals

    The theorems for [asinh], [atan], [exp], [exp10], [exp2], [sinh] and
    [tanh], which [impl_mono_inc!] defines, from [MonoInc.v], for [ln],
    [log10] and [log2], which [impl_log!] defines, from [LogDom.v], and for
    [asin] and [acosh] from [ClosedDom.v], each with the facts about its
    point function from [ExpReal.v], [LogReal.v] and [TrigReal.v]. The
    theorems for [atanh], [cosh] and [acos] are in [Atanh.v], [Cosh.v] and
    [ClosedDom.v]. Each assumes what [Mpfr.v] says of MPFR. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr RealBounds ComCommon
  MpfrRound Interior ExpReal LogReal TrigReal MonoInc LogDom ClosedDom.

Open Scope R_scope.

(* Each proof rewrites the function, by its definition, into the form of
   the section theorem, applies that with [eapply], and proves each
   hypothesis that it leaves by its shape, so the proofs do not depend on
   how many of the section's hypotheses the theorem takes. *)

(** ** [impl_mono_inc!] *)

Theorem asinh_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> asinh_ok emin emax m ->
  forall x, valid x -> is_tightest (image_dom real_dom arcsinh x) (Interval.asinh m x).
Proof.
intros emin emax m Hr Hget [Hg [Hlo Hhi]] x Hx.
change (Interval.asinh m x) with
  (Interval.mono_inc (mpfr_fn m (mpfr_asinh m) RNDD) (mpfr_fn m (mpfr_asinh m) RNDU) x).
eapply mono_inc_correct;
  first
    [ eassumption | exact asinh_inc | exact asinh_cont
    | right; split; [exact asinh_unbounded_below | exact Hlo]
    | right; split; [exact asinh_unbounded_above | exact Hhi] ].
Qed.

Theorem dec_asinh_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> asinh_ok emin emax m ->
  forall x, valid (itv x) ->
  let y := DecInterval.asinh m x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom arcsinh (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d arcsinh (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros emin emax m Hr Hget [Hg [Hlo Hhi]] x Hx.
change (DecInterval.asinh m x) with
  (DecInterval.elem_dec
     (Interval.mono_inc (mpfr_fn m (mpfr_asinh m) RNDD) (mpfr_fn m (mpfr_asinh m) RNDU)) x).
eapply dec_mono_inc_correct;
  first
    [ eassumption | exact asinh_inc | exact asinh_cont
    | right; split; [exact asinh_unbounded_below | exact Hlo]
    | right; split; [exact asinh_unbounded_above | exact Hhi]
    | right; split; [exact asinh_unbounded_below | exact asinh_unbounded_above] ].
Qed.

Theorem atan_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> atan_ok emin emax m ->
  forall x, valid x -> is_tightest (image_dom real_dom atan x) (Interval.atan m x).
Proof.
intros emin emax m Hr Hget [Hg [Hlo Hhi]] x Hx.
change (Interval.atan m x) with
  (Interval.mono_inc (mpfr_fn m (mpfr_atan m) RNDD) (mpfr_fn m (mpfr_atan m) RNDU) x).
eapply mono_inc_correct;
  first
    [ eassumption | exact atan_inc | exact atan_cont
    | left; exists (- (PI / 2)); split; [exact atan_glb | exact Hlo]
    | left; exists (PI / 2); split; [exact atan_lub | exact Hhi] ].
Qed.

Theorem dec_atan_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> atan_ok emin emax m ->
  forall x, valid (itv x) -> com_common x ->
  let y := DecInterval.atan m x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom atan (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d atan (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros emin emax m Hr Hget [Hg [Hlo Hhi]] x Hx Hcc.
change (DecInterval.atan m x) with
  (DecInterval.elem_dec
     (Interval.mono_inc (mpfr_fn m (mpfr_atan m) RNDD) (mpfr_fn m (mpfr_atan m) RNDU)) x).
eapply dec_mono_inc_correct;
  first
    [ eassumption | exact atan_inc | exact atan_cont
    | left; exists (- (PI / 2)); split; [exact atan_glb | exact Hlo]
    | left; exists (PI / 2); split; [exact atan_lub | exact Hhi]
    | left; exact Hcc ].
Qed.

Theorem exp_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> exp_ok emin emax m ->
  forall x, valid x -> is_tightest (image_dom real_dom exp x) (Interval.exp m x).
Proof.
intros emin emax m Hr Hget [Hg [Hlo Hhi]] x Hx.
change (Interval.exp m x) with
  (Interval.mono_inc (mpfr_fn m (mpfr_exp m) RNDD) (mpfr_fn m (mpfr_exp m) RNDU) x).
eapply mono_inc_correct;
  first
    [ eassumption | exact exp_inc | exact exp_cont
    | left; exists 0; split;
      [exact exp_glb | rewrite Hlo; apply mpfr_round_zero, mpfr_format_0]
    | right; split; [exact exp_unbounded | exact Hhi] ].
Qed.

Theorem dec_exp_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> exp_ok emin emax m ->
  forall x, valid (itv x) -> com_common x ->
  let y := DecInterval.exp m x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom exp (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d exp (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros emin emax m Hr Hget [Hg [Hlo Hhi]] x Hx Hcc.
change (DecInterval.exp m x) with
  (DecInterval.elem_dec
     (Interval.mono_inc (mpfr_fn m (mpfr_exp m) RNDD) (mpfr_fn m (mpfr_exp m) RNDU)) x).
eapply dec_mono_inc_correct;
  first
    [ eassumption | exact exp_inc | exact exp_cont
    | left; exists 0; split;
      [exact exp_glb | rewrite Hlo; apply mpfr_round_zero, mpfr_format_0]
    | right; split; [exact exp_unbounded | exact Hhi]
    | left; exact Hcc ].
Qed.

Theorem exp10_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> exp10_ok emin emax m ->
  forall x, valid x -> is_tightest (image_dom real_dom Rexp10 x) (Interval.exp10 m x).
Proof.
intros emin emax m Hr Hget [Hg [Hlo Hhi]] x Hx.
change (Interval.exp10 m x) with
  (Interval.mono_inc (mpfr_fn m (mpfr_exp10 m) RNDD) (mpfr_fn m (mpfr_exp10 m) RNDU) x).
eapply mono_inc_correct;
  first
    [ eassumption | exact exp10_inc | exact exp10_cont
    | left; exists 0; split;
      [exact exp10_glb | rewrite Hlo; apply mpfr_round_zero, mpfr_format_0]
    | right; split; [exact exp10_unbounded | exact Hhi] ].
Qed.

Theorem dec_exp10_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> exp10_ok emin emax m ->
  forall x, valid (itv x) -> com_common x ->
  let y := DecInterval.exp10 m x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom Rexp10 (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d Rexp10 (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros emin emax m Hr Hget [Hg [Hlo Hhi]] x Hx Hcc.
change (DecInterval.exp10 m x) with
  (DecInterval.elem_dec
     (Interval.mono_inc (mpfr_fn m (mpfr_exp10 m) RNDD) (mpfr_fn m (mpfr_exp10 m) RNDU)) x).
eapply dec_mono_inc_correct;
  first
    [ eassumption | exact exp10_inc | exact exp10_cont
    | left; exists 0; split;
      [exact exp10_glb | rewrite Hlo; apply mpfr_round_zero, mpfr_format_0]
    | right; split; [exact exp10_unbounded | exact Hhi]
    | left; exact Hcc ].
Qed.

Theorem exp2_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> exp2_ok emin emax m ->
  forall x, valid x -> is_tightest (image_dom real_dom Rexp2 x) (Interval.exp2 m x).
Proof.
intros emin emax m Hr Hget [Hg [Hlo Hhi]] x Hx.
change (Interval.exp2 m x) with
  (Interval.mono_inc (mpfr_fn m (mpfr_exp2 m) RNDD) (mpfr_fn m (mpfr_exp2 m) RNDU) x).
eapply mono_inc_correct;
  first
    [ eassumption | exact exp2_inc | exact exp2_cont
    | left; exists 0; split;
      [exact exp2_glb | rewrite Hlo; apply mpfr_round_zero, mpfr_format_0]
    | right; split; [exact exp2_unbounded | exact Hhi] ].
Qed.

Theorem dec_exp2_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> exp2_ok emin emax m ->
  forall x, valid (itv x) -> com_common x ->
  let y := DecInterval.exp2 m x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom Rexp2 (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d Rexp2 (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros emin emax m Hr Hget [Hg [Hlo Hhi]] x Hx Hcc.
change (DecInterval.exp2 m x) with
  (DecInterval.elem_dec
     (Interval.mono_inc (mpfr_fn m (mpfr_exp2 m) RNDD) (mpfr_fn m (mpfr_exp2 m) RNDU)) x).
eapply dec_mono_inc_correct;
  first
    [ eassumption | exact exp2_inc | exact exp2_cont
    | left; exists 0; split;
      [exact exp2_glb | rewrite Hlo; apply mpfr_round_zero, mpfr_format_0]
    | right; split; [exact exp2_unbounded | exact Hhi]
    | left; exact Hcc ].
Qed.

Theorem sinh_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> sinh_ok emin emax m ->
  forall x, valid x -> is_tightest (image_dom real_dom sinh x) (Interval.sinh m x).
Proof.
intros emin emax m Hr Hget [Hg [Hlo Hhi]] x Hx.
change (Interval.sinh m x) with
  (Interval.mono_inc (mpfr_fn m (mpfr_sinh m) RNDD) (mpfr_fn m (mpfr_sinh m) RNDU) x).
eapply mono_inc_correct;
  first
    [ eassumption | exact sinh_inc | exact sinh_cont
    | right; split; [exact sinh_unbounded_below | exact Hlo]
    | right; split; [exact sinh_unbounded_above | exact Hhi] ].
Qed.

Theorem dec_sinh_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> sinh_ok emin emax m ->
  forall x, valid (itv x) ->
  let y := DecInterval.sinh m x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom sinh (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d sinh (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros emin emax m Hr Hget [Hg [Hlo Hhi]] x Hx.
change (DecInterval.sinh m x) with
  (DecInterval.elem_dec
     (Interval.mono_inc (mpfr_fn m (mpfr_sinh m) RNDD) (mpfr_fn m (mpfr_sinh m) RNDU)) x).
eapply dec_mono_inc_correct;
  first
    [ eassumption | exact sinh_inc | exact sinh_cont
    | right; split; [exact sinh_unbounded_below | exact Hlo]
    | right; split; [exact sinh_unbounded_above | exact Hhi]
    | right; split; [exact sinh_unbounded_below | exact sinh_unbounded_above] ].
Qed.

Theorem tanh_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> tanh_ok emin emax m ->
  forall x, valid x -> is_tightest (image_dom real_dom tanh x) (Interval.tanh m x).
Proof.
intros emin emax m Hr Hget [Hg [Hlo Hhi]] x Hx.
change (Interval.tanh m x) with
  (Interval.mono_inc (mpfr_fn m (mpfr_tanh m) RNDD) (mpfr_fn m (mpfr_tanh m) RNDU) x).
eapply mono_inc_correct;
  first
    [ eassumption | exact tanh_inc | exact tanh_cont
    | left; exists (-1); split;
      [ exact tanh_glb
      | rewrite Hlo; apply mpfr_round_exact;
        [lra | exact (proj2 (mpfr_format_1 _ _ Hr))] ]
    | left; exists 1; split;
      [ exact tanh_lub
      | rewrite Hhi; apply mpfr_round_exact;
        [lra | exact (proj1 (mpfr_format_1 _ _ Hr))] ] ].
Qed.

Theorem dec_tanh_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> tanh_ok emin emax m ->
  forall x, valid (itv x) -> com_common x ->
  let y := DecInterval.tanh m x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom real_dom tanh (itv x)) (itv y) /\
    exists d, strongest_dom real_dom d tanh (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros emin emax m Hr Hget [Hg [Hlo Hhi]] x Hx Hcc.
change (DecInterval.tanh m x) with
  (DecInterval.elem_dec
     (Interval.mono_inc (mpfr_fn m (mpfr_tanh m) RNDD) (mpfr_fn m (mpfr_tanh m) RNDU)) x).
eapply dec_mono_inc_correct;
  first
    [ eassumption | exact tanh_inc | exact tanh_cont
    | left; exists (-1); split;
      [ exact tanh_glb
      | rewrite Hlo; apply mpfr_round_exact;
        [lra | exact (proj2 (mpfr_format_1 _ _ Hr))] ]
    | left; exists 1; split;
      [ exact tanh_lub
      | rewrite Hhi; apply mpfr_round_exact;
        [lra | exact (proj1 (mpfr_format_1 _ _ Hr))] ]
    | left; exact Hcc ].
Qed.

(** ** [impl_log!] *)

Theorem ln_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> ln_ok emin emax m ->
  forall x, valid x -> is_tightest (image_dom log_dom ln x) (Interval.ln m x).
Proof.
intros emin emax m Hr Hget [Hg [H0 Hinf]] x Hx.
change (Interval.ln m x) with
  (fst (Interval.log_impl (mpfr_fn m (mpfr_log m) RNDD) (mpfr_fn m (mpfr_log m) RNDU) x)).
eapply log_correct;
  first [ eassumption | exact ln_inc | exact ln_cont | exact ln_near0 | exact ln_big ].
Qed.

Theorem dec_ln_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> ln_ok emin emax m ->
  forall x, valid (itv x) ->
  let y := DecInterval.ln m x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom log_dom ln (itv x)) (itv y) /\
    exists d, strongest_dom log_dom d ln (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros emin emax m Hr Hget [Hg [H0 Hinf]] x Hx.
change (DecInterval.ln m x) with
  (DecInterval.elem_dec_impl
     (Interval.log_impl (mpfr_fn m (mpfr_log m) RNDD) (mpfr_fn m (mpfr_log m) RNDU)) x).
eapply dec_log_correct;
  first [ eassumption | exact ln_inc | exact ln_cont | exact ln_near0 | exact ln_big ].
Qed.

Theorem log10_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> log10_ok emin emax m ->
  forall x, valid x -> is_tightest (image_dom log_dom Rlog10 x) (Interval.log10 m x).
Proof.
intros emin emax m Hr Hget [Hg [H0 Hinf]] x Hx.
change (Interval.log10 m x) with
  (fst (Interval.log_impl (mpfr_fn m (mpfr_log10 m) RNDD) (mpfr_fn m (mpfr_log10 m) RNDU) x)).
eapply log_correct;
  first [ eassumption | exact log10_inc | exact log10_cont | exact log10_near0 | exact log10_big ].
Qed.

Theorem dec_log10_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> log10_ok emin emax m ->
  forall x, valid (itv x) ->
  let y := DecInterval.log10 m x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom log_dom Rlog10 (itv x)) (itv y) /\
    exists d, strongest_dom log_dom d Rlog10 (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros emin emax m Hr Hget [Hg [H0 Hinf]] x Hx.
change (DecInterval.log10 m x) with
  (DecInterval.elem_dec_impl
     (Interval.log_impl (mpfr_fn m (mpfr_log10 m) RNDD) (mpfr_fn m (mpfr_log10 m) RNDU)) x).
eapply dec_log_correct;
  first [ eassumption | exact log10_inc | exact log10_cont | exact log10_near0 | exact log10_big ].
Qed.

Theorem log2_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> log2_ok emin emax m ->
  forall x, valid x -> is_tightest (image_dom log_dom Rlog2 x) (Interval.log2 m x).
Proof.
intros emin emax m Hr Hget [Hg [H0 Hinf]] x Hx.
change (Interval.log2 m x) with
  (fst (Interval.log_impl (mpfr_fn m (mpfr_log2 m) RNDD) (mpfr_fn m (mpfr_log2 m) RNDU) x)).
eapply log_correct;
  first [ eassumption | exact log2_inc | exact log2_cont | exact log2_near0 | exact log2_big ].
Qed.

Theorem dec_log2_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> log2_ok emin emax m ->
  forall x, valid (itv x) ->
  let y := DecInterval.log2 m x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom log_dom Rlog2 (itv x)) (itv y) /\
    exists d, strongest_dom log_dom d Rlog2 (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros emin emax m Hr Hget [Hg [H0 Hinf]] x Hx.
change (DecInterval.log2 m x) with
  (DecInterval.elem_dec_impl
     (Interval.log_impl (mpfr_fn m (mpfr_log2 m) RNDD) (mpfr_fn m (mpfr_log2 m) RNDU)) x).
eapply dec_log_correct;
  first [ eassumption | exact log2_inc | exact log2_cont | exact log2_near0 | exact log2_big ].
Qed.

(** ** [asin] and [acosh] *)

Theorem asin_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> asin_ok emin emax m ->
  forall x, valid x -> is_tightest (image_dom asin_dom asin x) (Interval.asin m x).
Proof.
intros emin emax m Hr Hget Hg x Hx.
change (Interval.asin m x) with
  (fst (closed_inc (Interval.const_interval (opp (of_u64 1)) (of_u64 1))
     (mpfr_fn m (mpfr_asin m) RNDD) (mpfr_fn m (mpfr_asin m) RNDU) x)).
eapply closed_inc_correct;
  match goal with
  | |- is_finite _ = true => vm_compute; reflexivity
  | |- valid (Interval.const_interval _ _) => exact dom_unit_valid
  | |- forall r, asin_dom r <-> _ => exact (fun r => iff_sym (dom_unit_mem r))
  | |- of_u64 1 = B754_infinity false -> _ =>
      let H := fresh in
      intros H; apply (f_equal is_finite) in H; vm_compute in H; discriminate H
  | |- forall r t, asin_dom r -> asin_dom t -> r <= t -> _ =>
      exact (fun r t Hr Ht Hrt => asin_inc r t (proj1 Hr) Hrt (proj2 Ht))
  | |- forall r, asin_dom r -> continue_in _ _ _ => exact asin_cont
  | |- _ => eassumption
  end.
Qed.

Theorem dec_asin_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> asin_ok emin emax m ->
  forall x, valid (itv x) ->
  let y := DecInterval.asin m x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom asin_dom asin (itv x)) (itv y) /\
    exists d, strongest_dom asin_dom d asin (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros emin emax m Hr Hget Hg x Hx.
change (DecInterval.asin m x) with
  (DecInterval.elem_dec_impl
     (closed_inc (Interval.const_interval (opp (of_u64 1)) (of_u64 1))
        (mpfr_fn m (mpfr_asin m) RNDD) (mpfr_fn m (mpfr_asin m) RNDU)) x).
eapply dec_closed_inc_correct;
  match goal with
  | |- is_finite _ = true => vm_compute; reflexivity
  | |- valid (Interval.const_interval _ _) => exact dom_unit_valid
  | |- forall r, asin_dom r <-> _ => exact (fun r => iff_sym (dom_unit_mem r))
  | |- of_u64 1 = B754_infinity false -> _ =>
      let H := fresh in
      intros H; apply (f_equal is_finite) in H; vm_compute in H; discriminate H
  | |- forall r t, asin_dom r -> asin_dom t -> r <= t -> _ =>
      exact (fun r t Hr Ht Hrt => asin_inc r t (proj1 Hr) Hrt (proj2 Ht))
  | |- forall r, asin_dom r -> continue_in _ _ _ => exact asin_cont
  | |- _ => eassumption
  end.
Qed.

Theorem acosh_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> acosh_ok emin emax m ->
  forall x, valid x -> is_tightest (image_dom acosh_dom Racosh x) (Interval.acosh m x).
Proof.
intros emin emax m Hr Hget [Hg Hinf] x Hx.
change (Interval.acosh m x) with
  (fst (closed_inc (Interval.const_interval (of_u64 1) (B754_infinity false))
     (mpfr_fn m (mpfr_acosh m) RNDD) (mpfr_fn m (mpfr_acosh m) RNDU) x)).
eapply closed_inc_correct;
  match goal with
  | |- is_finite _ = true => vm_compute; reflexivity
  | |- valid (Interval.const_interval _ _) => exact dom_ge1_valid
  | |- forall r, acosh_dom r <-> _ => exact (fun r => iff_sym (dom_ge1_mem r))
  | |- B754_infinity false = B754_infinity false -> _ =>
      intros _; split; [exact Hinf | exact acosh_big]
  | |- forall r t, acosh_dom r -> acosh_dom t -> r <= t -> _ =>
      exact (fun r t Hr _ Hrt => acosh_inc r t Hr Hrt)
  | |- forall r, acosh_dom r -> continue_in _ _ _ =>
      exact (fun r Hr => continuity_pt_continue_in_dom _ _ _ (acosh_cont r Hr))
  | |- _ => eassumption
  end.
Qed.

Theorem dec_acosh_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> acosh_ok emin emax m ->
  forall x, valid (itv x) ->
  let y := DecInterval.acosh m x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom acosh_dom Racosh (itv x)) (itv y) /\
    exists d, strongest_dom acosh_dom d Racosh (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros emin emax m Hr Hget [Hg Hinf] x Hx.
change (DecInterval.acosh m x) with
  (DecInterval.elem_dec_impl
     (closed_inc (Interval.const_interval (of_u64 1) (B754_infinity false))
        (mpfr_fn m (mpfr_acosh m) RNDD) (mpfr_fn m (mpfr_acosh m) RNDU)) x).
eapply dec_closed_inc_correct;
  match goal with
  | |- is_finite _ = true => vm_compute; reflexivity
  | |- valid (Interval.const_interval _ _) => exact dom_ge1_valid
  | |- forall r, acosh_dom r <-> _ => exact (fun r => iff_sym (dom_ge1_mem r))
  | |- B754_infinity false = B754_infinity false -> _ =>
      intros _; split; [exact Hinf | exact acosh_big]
  | |- forall r t, acosh_dom r -> acosh_dom t -> r <= t -> _ =>
      exact (fun r t Hr _ Hrt => acosh_inc r t Hr Hrt)
  | |- forall r, acosh_dom r -> continue_in _ _ _ =>
      exact (fun r Hr => continuity_pt_continue_in_dom _ _ _ (acosh_cont r Hr))
  | |- _ => eassumption
  end.
Qed.
