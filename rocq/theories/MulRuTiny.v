(** * Rounding a tiny product up through a scaled one

    For finite, nonzero [x] and [y], [mul1_ru_tiny] rounds [z = x * y]
    toward +inf where [|RN(z)| < 2^-968], which [mul1_ru_fast] rejects. If
    [RN(z) = 0], it picks the result by the sign of [RN(z)]
    ([zero_rule_rounds_up]). Otherwise it scales [x] by [2^128], rounds the
    scaled product up on the fast path, giving [rs = RU(z * 2^128)], and
    rounds [rs * 2^-128] up from
    [q = RN(rs * 2^-128)] by comparing [q * 2^128] with [rs]
    ([step_up_rounds_up_iff0], which unlike [step_up_rounds_up_iff] allows
    [q = 0]). That gives [RU z], as rounding up twice through the finer
    format of the scaled product is rounding up once ([RU_scaled]).

    The lemmas here are about reals and single floats. [MulRu.v] puts them
    together in [mul1_ru_tiny_correct]. *)

From Stdlib Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Spec TwoSum AddRu StepUp TwoProduct
  SqrtSlow.

Open Scope R_scope.

Local Notation format := (generic_format radix2 fexp64).

(** ** Rounding up twice *)

(** Rounding [z * 2^128] up, scaling the result back by [2^-128] and
    rounding that up gives [RU z]. [RU (z * 2^128) * 2^-128] is at or above
    [z], so its rounding is at or above [RU z]. Conversely, [RU z * 2^128]
    is a float ([format_scale_up]) at or above [z * 2^128], so it is at or
    above [RU (z * 2^128)], and [RU z] is a float at or above
    [RU (z * 2^128) * 2^-128]. *)
Lemma RU_scaled :
  forall z,
  RU (RU (z * bpow radix2 128) * bpow radix2 (-128)) = RU z.
Proof.
intros z.
set (f := RU (z * bpow radix2 128)).
pose proof (bpow_gt_0 radix2 (-128)) as Hm128.
assert (Hinv : forall v, v * bpow radix2 128 * bpow radix2 (-128) = v).
{ intros v. apply scale_back. reflexivity. }
assert (Hf : z * bpow radix2 128 <= f) by apply (round_UP_pt radix2 fexp64).
assert (Fg : format (RU z)) by (apply generic_format_round; typeclasses eauto).
assert (Hg : z <= RU z) by apply (round_UP_pt radix2 fexp64).
apply Rle_antisym.
- (* [RU z * 2^128] is a float at or above [z * 2^128], hence at or
     above [f], so [RU z] is a float at or above [f * 2^-128]. *)
  apply round_le_generic; [typeclasses eauto .. | exact Fg |].
  assert (H : f <= RU z * bpow radix2 128).
  { apply round_le_generic; [typeclasses eauto .. | |].
    - apply format_scale_up; [exact Fg | lia].
    - apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Hg]. }
  rewrite <- (Hinv (RU z)).
  apply Rmult_le_compat_r; lra.
- (* [f * 2^-128] is at or above [z]. *)
  apply round_le; [typeclasses eauto .. |].
  rewrite <- (Hinv z).
  apply Rmult_le_compat_r; lra.
Qed.

(** [rounds_up_to v r] depends on [v] only through [RU v] and the sign of
    [v]. *)
Lemma rounds_up_to_ext :
  forall v v' r,
  RU v = RU v' -> Rlt_bool v 0 = Rlt_bool v' 0 ->
  rounds_up_to v r -> rounds_up_to v' r.
Proof.
intros v v' r HU Hs H.
unfold rounds_up_to in *.
rewrite <- HU, <- Hs.
exact H.
Qed.

(** ** Stepping up a result that may be zero *)

(** [step_up_rounds_up_iff] for a nonzero [w] and a [q = RN(w)] that may
    be zero, provided that a zero [q] has the sign of [w]. If [q = 0 < w], [step_up] gives the
    least positive float [2^-1074], which is [RU w]; if [w < q = 0], [RU w]
    is a zero, and [q] has the sign of [w]. *)
Lemma step_up_rounds_up_iff0 :
  forall w (q : f64) (up : bool),
  w <> 0 -> is_finite q = true -> B2R q = RN w ->
  (B2R q = 0 -> Bsign q = Rlt_bool w 0) ->
  (up = true <-> B2R q < w) ->
  rounds_up_to w (if up then Generic.step_up q else q).
Proof.
intros w q up Hw Fq Hq Hs Hup.
destruct (Req_dec (B2R q) 0) as [H0|H0].
2: { now apply step_up_rounds_up_iff. }
(* [|w| < 2^-1074], as otherwise [|RN w| >= 2^-1074], a float. *)
assert (Hsmall : Rabs w < bpow radix2 (-1074)).
{ apply Rnot_le_lt. intros Hge.
  assert (H : bpow radix2 (-1074) <= Rabs (RN w)).
  { apply abs_round_ge_generic; [typeclasses eauto .. | | exact Hge].
    apply generic_format_FLT_bpow; [typeclasses eauto .. | lia]. }
  rewrite <- Hq, H0, Rabs_R0 in H.
  pose proof (bpow_gt_0 radix2 (-1074)). lra. }
(* A finite [q] with value 0 is a zero. *)
assert (Hst : is_finite_strict q = false).
{ destruct q as [s|s| |s m e Hb]; try discriminate Fq; [reflexivity|].
  exfalso. revert H0. cbn [B2R]. apply F2R_neq_0. cbn [Fnum].
  destruct s; discriminate. }
unfold rounds_up_to.
destruct up.
- (* [0 < w < 2^-1074]: rounding up gives [succ 0 = 2^-1074], which
     [step_up] gives for a zero. *)
  assert (Hpos : 0 < w) by (rewrite <- H0; now apply Hup).
  assert (Hs0 : succ radix2 fexp64 0 = bpow radix2 (-1074)).
  { rewrite succ_0. apply ulp_FLT_0; typeclasses eauto. }
  assert (HU : RU w = bpow radix2 (-1074)).
  { rewrite RU_RN_below by (rewrite <- Hq, H0; exact Hpos).
    rewrite <- Hq, H0. exact Hs0. }
  rewrite step_up_Bsucc by exact Fq.
  generalize (@Bsucc_correct 53 1024 _ _ q Fq).
  change (SpecFloat.fexp 53 1024) with fexp64.
  rewrite H0, Hs0.
  rewrite Rlt_bool_true by (apply bpow_lt; lia).
  intros (HR & HF & HS).
  rewrite HU, Rabs_pos_eq by apply bpow_ge_0.
  rewrite Rlt_bool_true by (apply bpow_lt; lia).
  split; [exact HR|]. split; [exact HF|].
  rewrite HS, Hst, Bool.andb_false_r.
  symmetry. apply Rlt_bool_false. lra.
- (* [w <= q = 0], so [q] is [w] rounded up. *)
  assert (Hle : w <= B2R q).
  { apply Rnot_lt_le. intros Hlt. apply Hup in Hlt. discriminate Hlt. }
  assert (HU : RU w = B2R q).
  { rewrite Hq. apply RU_RN_above. rewrite <- Hq. exact Hle. }
  rewrite HU, Rlt_bool_true by apply abs_B2R_lt_emax.
  split; [reflexivity|]. split; [exact Fq | exact (Hs H0)].
Qed.

(** The zero rule of [mul1_ru_tiny]: if [p = RN(z)] is a zero with the
    sign of [z], then [z] rounded up is [p] if [z < 0], and the least
    positive float, whose bit pattern is [1], if [z > 0]. *)
Lemma zero_rule_rounds_up :
  forall z (p : f64),
  z <> 0 -> is_finite p = true -> B2R p = RN z -> B2R p = 0 ->
  Bsign p = Rlt_bool z 0 ->
  rounds_up_to z (if Bsign p then p else from_bits 1).
Proof.
intros z p Hz Fp Hp Hp0 Hs.
(* [step_up] of a zero is [from_bits 1]. *)
assert (Hstep : Generic.step_up p = from_bits 1).
{ unfold Generic.step_up, gt, lt.
  rewrite 2!Bltb_correct by first [exact Fp | reflexivity].
  change (B2R zero) with 0.
  rewrite Hp0, Rlt_bool_false by apply Rle_refl.
  reflexivity. }
replace (if Bsign p then p else from_bits 1)
  with (if negb (Bsign p) then Generic.step_up p else p)
  by (rewrite Hstep; destruct (Bsign p); reflexivity).
apply step_up_rounds_up_iff0;
  [exact Hz | exact Fp | exact Hp | intros _; exact Hs |].
rewrite Hs, Hp0.
destruct (Rdichotomy _ _ Hz) as [Hn|Hn];
  [rewrite (Rlt_bool_true _ _ Hn) | rewrite (Rlt_bool_false _ _ (Rlt_le _ _ Hn))];
  cbn [negb]; split; intros H; first [reflexivity | lra | discriminate H].
Qed.

(** ** Magnitudes *)

(** A nonzero float is at least [2^-1074] in magnitude. *)
Lemma abs_B2R_ge_min :
  forall x : f64, is_finite x = true -> B2R x <> 0 ->
  bpow radix2 (-1074) <= Rabs (B2R x).
Proof.
intros x Fx Hx.
apply (generic_format_ge_bpow radix2 fexp64).
- intros e. unfold FLT_exp. lia.
- apply Rabs_pos_lt. exact Hx.
- apply generic_format_abs.
  generalize (generic_format_B2R 53 1024 x).
  change (SpecFloat.fexp 53 1024) with fexp64. easy.
Qed.

(** If [RN z] is nonzero, [|z| >= 2^-1075]: [RN z] is then at least
    [2^-1074] in magnitude, while for [|z| < 2^-1075] it would be at most
    [2^-1075] away from [z]. *)
Lemma RN_nonzero_ge :
  forall z, RN z <> 0 -> bpow radix2 (-1075) <= Rabs z.
Proof.
intros z Hz.
(* [RN z] is a nonzero float, so at least [2^-1074] in magnitude. *)
assert (Hge : bpow radix2 (-1074) <= Rabs (RN z)).
{ apply (generic_format_ge_bpow radix2 fexp64).
  - intros e. unfold FLT_exp. lia.
  - apply Rabs_pos_lt. exact Hz.
  - apply generic_format_abs, generic_format_round; typeclasses eauto. }
apply Rnot_lt_le. intros Hlt.
(* Below [2^-1075], the ulp is [2^-1074], so [RN z] is at most [2^-1075]
   away from [z]. *)
assert (Hu : ulp radix2 fexp64 z = bpow radix2 (-1074)).
{ apply ulp_FLT_small; [typeclasses eauto |].
  apply Rlt_trans with (1 := Hlt). apply bpow_lt. lia. }
pose proof (error_le_half_ulp radix2 fexp64 (fun t => negb (Z.even t)) z)
  as He.
rewrite Hu in He.
assert (HB : bpow radix2 (-1074) = 2 * bpow radix2 (-1075)).
{ change (-1074)%Z with (1 + -1075)%Z. rewrite bpow_plus. reflexivity. }
pose proof (Rabs_triang (RN z - z) z) as Ht.
replace (RN z - z + z) with (RN z) in Ht by ring.
lra.
Qed.

(** If [|RN z| < 2^e] for a float [2^e], then [|z| < 2^e]. *)
Lemma abs_lt_of_RN_lt :
  forall z e, (-1074 <= e <= 1023)%Z ->
  Rabs (RN z) < bpow radix2 e -> Rabs z < bpow radix2 e.
Proof.
intros z e He H.
apply Rnot_le_lt. intros Hge.
assert (Rabs (RN z) >= bpow radix2 e); [|lra].
apply Rle_ge, abs_round_ge_generic; [typeclasses eauto .. | | exact Hge].
apply generic_format_FLT_bpow; [typeclasses eauto .. | lia].
Qed.

(** [exponent] from bounds on the magnitude: [exponent(x) < n] if
    [|x| < 2^n] for [n >= -1022], and [n <= exponent(x)] if [2^n <= |x|]
    (see [abs_B2R_lt_exponent] and [bpow_exponent_le_abs_B2R]). *)
Lemma exponent_lt :
  forall x n, is_finite x = true -> (-1022 <= n)%Z ->
  Rabs (B2R x) < bpow radix2 n -> (Generic.exponent x < n)%Z.
Proof.
intros x n Fx Hn Hlt.
apply Z.nle_gt. intros Hge.
assert (bpow radix2 (Generic.exponent x) <= Rabs (B2R x))
  by (apply bpow_exponent_le_abs_B2R; [exact Fx | lia]).
assert (bpow radix2 n <= bpow radix2 (Generic.exponent x))
  by (apply bpow_le; exact Hge).
lra.
Qed.

Lemma exponent_ge :
  forall x n, is_finite x = true ->
  bpow radix2 n <= Rabs (B2R x) -> (n <= Generic.exponent x)%Z.
Proof.
intros x n Fx Hge.
pose proof (abs_B2R_lt_exponent x Fx) as Hlt.
assert (H : bpow radix2 n < bpow radix2 (Generic.exponent x + 1)) by lra.
apply lt_bpow in H. lia.
Qed.

(** ** Products that do not overflow *)

(** For finite [x] and [y] whose exact product is at most [2^1023] in
    magnitude, [x * y] and [x * y] rounded up are finite, are [RN(x * y)]
    and [RU(x * y)], and have the sign [xorb (Bsign x) (Bsign y)] even if
    they are zero ([Bmult_correct]). *)
Lemma mul_RN_spec :
  forall x y : f64, is_finite x = true -> is_finite y = true ->
  Rabs (B2R x * B2R y) <= bpow radix2 1023 ->
  is_finite (mul x y) = true /\ B2R (mul x y) = RN (B2R x * B2R y) /\
  Bsign (mul x y) = xorb (Bsign x) (Bsign y).
Proof.
intros x y Fx Fy H.
(* [|RN(x * y)| <= 2^1023], a float, so the product does not overflow. *)
assert (Hlt : Rabs (RN (B2R x * B2R y)) < bpow radix2 1024).
{ apply Rle_lt_trans with (bpow radix2 1023).
  - apply abs_round_le_generic; [typeclasses eauto .. | | exact H].
    apply generic_format_FLT_bpow; [typeclasses eauto .. | lia].
  - apply bpow_lt. lia. }
generalize (@Bmult_correct 53 1024 _ _ mode_NE x y).
change (SpecFloat.fexp 53 1024) with fexp64.
rewrite Rlt_bool_true by exact Hlt.
intros (HR & HF & HS). rewrite Fx, Fy in HF.
change (Bmult mode_NE x y) with (mul x y) in HR, HF, HS.
split; [exact HF|]. split; [exact HR|].
apply HS. revert HF. destruct (mul x y); easy.
Qed.

Lemma Bmult_UP_spec :
  forall x y : f64, is_finite x = true -> is_finite y = true ->
  Rabs (B2R x * B2R y) <= bpow radix2 1023 ->
  is_finite (Bmult mode_UP x y) = true /\
  B2R (Bmult mode_UP x y) = RU (B2R x * B2R y) /\
  Bsign (Bmult mode_UP x y) = xorb (Bsign x) (Bsign y).
Proof.
intros x y Fx Fy H.
(* [|RU(x * y)| <= 2^1023], a float, so the product does not overflow. *)
assert (Hlt : Rabs (RU (B2R x * B2R y)) < bpow radix2 1024).
{ apply Rle_lt_trans with (bpow radix2 1023).
  - apply abs_round_le_generic; [typeclasses eauto .. | | exact H].
    apply generic_format_FLT_bpow; [typeclasses eauto .. | lia].
  - apply bpow_lt. lia. }
generalize (@Bmult_correct 53 1024 _ _ mode_UP x y).
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_UP)) with RU.
rewrite Rlt_bool_true by exact Hlt.
intros (HR & HF & HS). rewrite Fx, Fy in HF.
split; [exact HF|]. split; [exact HR|].
apply HS. revert HF. destruct (Bmult mode_UP x y); easy.
Qed.

(** ** The constants *)

(** [TWO_POW_128] and [TWO_POW_M128] of [mul1_ru_tiny] are [2^128] and
    [2^-128], as in [sqrt1_slow]. *)
Lemma two_pow_128_spec :
  is_finite (mul (of_u64 (2^64)) (of_u64 (2^64))) = true /\
  Bsign (mul (of_u64 (2^64)) (of_u64 (2^64))) = false /\
  B2R (mul (of_u64 (2^64)) (of_u64 (2^64))) = bpow radix2 128.
Proof.
exact (B2SF_bpow _ 128 two_pow_128_B2SF).
Qed.

Lemma two_pow_m128_spec :
  is_finite (div (of_u64 1) (mul (of_u64 (2^64)) (of_u64 (2^64)))) = true /\
  Bsign (div (of_u64 1) (mul (of_u64 (2^64)) (of_u64 (2^64)))) = false /\
  B2R (div (of_u64 1) (mul (of_u64 (2^64)) (of_u64 (2^64)))) =
    bpow radix2 (-128).
Proof.
exact (B2SF_bpow _ (-128) two_pow_m128_B2SF).
Qed.
