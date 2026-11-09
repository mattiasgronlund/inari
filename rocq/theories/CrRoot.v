(** * The square roots of [src/cr.rs]

    [sqrt_rd] and [sqrt_ru] of [src/cr.rs] call the backend's [sqrt1_rd]
    and [sqrt1_ru], [Generic.sqrt1_rd] and [Generic.sqrt1_ru] for the
    portable one, with or without an FMA, and [sqrt_rn] calls
    [x.sqrt()], i.e. [fsqrt]. At every finite [x >= 0] they return
    [sqrt (B2R x)] rounded toward -inf, toward +inf
    ([cr_sqrt_dir_correct]) and to nearest ([cr_sqrt_rn_correct]), by
    [sqrt1_rd_correct] and [sqrt1_ru_correct] of [SqrtRdRu.v] and Flocq's
    [Bsqrt_correct]; and a zero at the same zero ([cr_sqrt_zero]), +inf at +inf
    ([cr_sqrt_inf]), and NaN below 0, at -inf and at NaN ([cr_sqrt_nan]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr NearF64 Encoding SqrtRdRu.

Open Scope R_scope.

(** A finite float whose value is [r] rounded toward -inf or +inf in
    binary64 is [r] rounded as [mpfr_round] says: it is the greatest
    (least) [f64] at or below (above) [r], as the finite [f64]s are the
    floats of [fexp64]; and a zero is [MZero] of its sign. *)
Local Lemma round_dir_mpfr :
  forall (up : bool) r (w : f64), is_finite w = true ->
  B2R w = round radix2 fexp64 (if up then Zceil else Zfloor) r ->
  mpfr_round f64_format (if up then RNDU else RNDD) r (with_val w).
Proof.
intros up r w Fw Hw.
assert (Fv : f64_format (B2R w)) by (exists w; split; [exact Fw | reflexivity]).
assert (Hpt : if up then Rnd_UP_pt f64_format r (B2R w) else Rnd_DN_pt f64_format r (B2R w)).
{ destruct up.
  - destruct (round_UP_pt radix2 fexp64 r) as (_ & Hge & Hmin).
    split; [exact Fv |]. rewrite Hw. split; [exact Hge |].
    intros g (z & Fz & <-) Hg. apply Hmin; [apply generic_format_B2R | exact Hg].
  - destruct (round_DN_pt radix2 fexp64 r) as (_ & Hle & Hmax).
    split; [exact Fv |]. rewrite Hw. split; [exact Hle |].
    intros g (z & Fz & <-) Hg. apply Hmax; [apply generic_format_B2R | exact Hg]. }
clear Fv Hw.
destruct w as [s|s| |s m e B]; try discriminate Fw.
- (* A zero: [with_val] is [MZero s] and its value is 0. *)
  cbn [with_val]. cbn [B2R] in Hpt. destruct up; exact Hpt.
- (* A nonzero finite float: [with_val] is the [MNum] of its value. *)
  assert (N0 : B2R (B754_finite s m e B) <> 0).
  { cbn [B2R]. apply F2R_neq_0. cbn [Fnum]. destruct s; discriminate. }
  change (with_val (B754_finite s m e B)) with (MNum (B2R (B754_finite s m e B))).
  destruct up; cbn [mpfr_round]; split; assumption.
Qed.

(** At a finite [x >= 0], [Bsqrt m x] is finite and is [sqrt x] rounded in
    binary64: [x] is a zero or positive, and Flocq's [Bsqrt_correct] says
    so. *)
Local Lemma Bsqrt_nonneg :
  forall m (x : f64), is_finite x = true -> 0 <= B2R x ->
  is_finite (Bsqrt m x) = true /\
  B2R (Bsqrt m x) = round radix2 fexp64 (round_mode m) (sqrt (B2R x)).
Proof.
intros m x Fx Hx.
destruct (@Bsqrt_correct 53 1024 _ _ m x) as (HR & HF & _).
change (SpecFloat.fexp 53 1024) with fexp64 in HR.
split; [| exact HR].
rewrite HF. clear HR HF.
destruct x as [s|s| |[|] mx ex Hex]; try discriminate Fx; try reflexivity.
(* A negative finite [x] has a negative value. *)
exfalso. revert Hx. cbn [B2R]. apply Rlt_not_le, F2R_lt_0. cbn [Fnum cond_Zopp]. lia.
Qed.

Theorem cr_sqrt_dir_correct :
  forall has_fma (x : f64) (up : bool),
  is_finite x = true -> 0 <= B2R x ->
  exists v : f64,
  (if up then Generic.sqrt1_ru has_fma x else Generic.sqrt1_rd has_fma x) = Some v /\
  mpfr_round f64_format (if up then RNDU else RNDD) (sqrt (B2R x)) (with_val v).
Proof.
intros has_fma x up Fx Hx.
destruct (Bsqrt_nonneg (if up then mode_UP else mode_DN) x Fx Hx) as (Fs & Rs).
exists (Bsqrt (if up then mode_UP else mode_DN) x). split.
- destruct up; [apply sqrt1_ru_correct | apply sqrt1_rd_correct].
- apply round_dir_mpfr; [exact Fs |]. rewrite Rs. destruct up; reflexivity.
Qed.

Theorem cr_sqrt_rn_correct :
  forall x,
  is_finite x = true -> 0 <= B2R x -> near_round (sqrt (B2R x)) (fsqrt x).
Proof.
intros x Fx Hx. unfold near_round, fsqrt.
(* [sqrt x < 2^512], as [x < 2^1024], far below the overflow threshold. *)
assert (Hs : 0 <= sqrt (B2R x) < bpow radix2 512).
{ split; [apply sqrt_pos |].
  pose proof (@abs_B2R_lt_emax 53 1024 x) as H1. rewrite Rabs_pos_eq in H1 by exact Hx.
  pose proof (bpow_gt_0 radix2 512) as H2.
  rewrite <- (sqrt_square (bpow radix2 512)) by lra.
  apply sqrt_lt_1_alt. split; [exact Hx |].
  rewrite <- bpow_plus. exact H1. }
destruct (Rle_dec (bpow radix2 1024 - bpow radix2 970) (Rabs (sqrt (B2R x)))) as [Hb | _].
{ exfalso. rewrite Rabs_pos_eq in Hb by apply sqrt_pos.
  assert (H : bpow radix2 512 < bpow radix2 1024 - bpow radix2 970)
    by (cbn [bpow radix_val radix2]; lra).
  lra. }
destruct (Bsqrt_nonneg mode_NE x Fx Hx) as (Fs & Rs).
split; [exact Fs |]. split; [exact Rs |].
(* A nonzero [sqrt x] needs [x > 0], and then [Bsqrt] is positive. *)
intros Hr0 _.
assert (Hp : 0 < B2R x).
{ destruct (Rle_lt_or_eq_dec _ _ Hx) as [Hp | H0]; [exact Hp |].
  rewrite <- H0, sqrt_0 in Hr0. contradiction. }
destruct (Bsqrt_pos_bound mode_NE x Fx Hp) as (_ & Sg & _).
rewrite Sg. symmetry. apply Rlt_bool_false. apply sqrt_pos.
Qed.

Theorem cr_sqrt_zero :
  forall has_fma s,
  Generic.sqrt1_rd has_fma (B754_zero s) = Some (B754_zero s) /\
  Generic.sqrt1_ru has_fma (B754_zero s) = Some (B754_zero s) /\
  fsqrt (B754_zero s) = B754_zero s.
Proof.
intros has_fma s.
rewrite sqrt1_rd_correct, sqrt1_ru_correct. unfold fsqrt.
split; [| split]; reflexivity.
Qed.

Theorem cr_sqrt_inf :
  forall has_fma,
  Generic.sqrt1_rd has_fma infinity = Some infinity /\
  Generic.sqrt1_ru has_fma infinity = Some infinity /\ fsqrt infinity = infinity.
Proof.
intros has_fma.
assert (Hi : infinity = B754_infinity false) by exact from_bits_2047.
rewrite sqrt1_rd_correct, sqrt1_ru_correct. unfold fsqrt. rewrite Hi.
split; [| split]; reflexivity.
Qed.

Theorem cr_sqrt_nan :
  forall has_fma x,
  x = B754_nan \/ x = B754_infinity true \/ (is_finite x = true /\ B2R x < 0) ->
  Generic.sqrt1_rd has_fma x = Some B754_nan /\
  Generic.sqrt1_ru has_fma x = Some B754_nan /\ fsqrt x = B754_nan.
Proof.
intros has_fma x Hx.
rewrite sqrt1_rd_correct, sqrt1_ru_correct. unfold fsqrt.
(* [Bsqrt] of NaN, of -inf and of a negative finite [x] is NaN; a zero
   or a positive finite [x] is not negative. *)
destruct Hx as [-> | [-> | (Fx & Hx)]]; [split; [| split]; reflexivity | split; [| split]; reflexivity |].
destruct x as [s|s| |[|] mx ex Hex]; try discriminate Fx.
- exfalso. cbn [B2R] in Hx. lra.
- split; [| split]; reflexivity.
- exfalso. revert Hx. cbn [B2R]. apply Rle_not_lt, Rlt_le, F2R_gt_0. cbn [Fnum cond_Zopp]. lia.
Qed.
