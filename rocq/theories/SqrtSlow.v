(** * [sqrt1_slow] scales into the range of the fast path

    [sqrt1_slow x f] handles the inputs that the fast path of [sqrt1_rd]
    and [sqrt1_ru] rejects. A positive finite [x] is scaled by [2^128]
    if [exponent(x) < 0] and by [2^-128] otherwise, which brings it into
    the range of the fast path, [-966 <= exponent <= 1021], and the square
    root [f] returns for the scaled input is scaled back by [2^-64] or
    [2^64]. Any other [x] is zero, negative, infinite or NaN, and its
    square root does not depend on the rounding mode.

    All the scalings are exact. Scaling [x] up by [2^128] may land on a
    subnormal, which still has all the bits of [x] ([format_scale_up]).
    Every other scaled value is normal, and rounding a normal value commutes
    with a scaling that keeps it normal ([round_scale]), as both roundings
    are then FLX roundings with 53 bits. Since [sqrt(x * 2^(2k)) =
    sqrt(x) * 2^k], the square root of the scaled input is the square root
    of [x] rounded in the same mode and scaled by [2^k], so [sqrt1_slow]
    returns [Bsqrt m x] in any mode [m] in which [f] is correct. *)

From Stdlib Require Import Bool ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Decompose TwoSum TwoProduct StepUp
  RoundUpExact.

Open Scope R_scope.

Local Notation format := (generic_format radix2 fexp64).

(** ** Scaling by powers of two *)

(** Rounding commutes with a scaling by [2^e] if the value is normal before
    and after it. *)
Lemma round_scale :
  forall rnd {Hr : Valid_rnd rnd} v e,
  bpow radix2 (-1022) <= Rabs v ->
  bpow radix2 (-1022) <= Rabs (v * bpow radix2 e) ->
  round radix2 fexp64 rnd (v * bpow radix2 e) =
  round radix2 fexp64 rnd v * bpow radix2 e.
Proof.
intros rnd Hr v e Hv Hve.
(* Above [2^-1022] binary64 rounds like FLX with 53 bits, whose canonical
   exponent [mag - 53] moves with the scaling. *)
rewrite (round_FLT_FLX radix2 (-1074) 53 rnd (v * bpow radix2 e) Hve).
rewrite (round_FLT_FLX radix2 (-1074) 53 rnd v Hv).
assert (Hv0 : v <> 0).
{ intros ->. rewrite Rabs_R0 in Hv. generalize (bpow_gt_0 radix2 (-1022)).
  lra. }
unfold round, scaled_mantissa, cexp, FLX_exp.
rewrite (mag_mult_bpow radix2 v e Hv0).
unfold F2R; cbn [Fnum Fexp].
(* The scaled mantissas are the same real. *)
replace (v * bpow radix2 e * bpow radix2 (- (mag radix2 v + e - 53)))
  with (v * bpow radix2 (- (mag radix2 v - 53))).
2: { rewrite Rmult_assoc, <- bpow_plus. do 2 f_equal. ring. }
rewrite Rmult_assoc, <- bpow_plus. do 2 f_equal. ring.
Qed.

(** Scaling a float up by [2^e] keeps it a float: its integral significand
    stays the same and its exponent only grows. *)
Lemma format_scale_up :
  forall x e, format x -> (0 <= e)%Z -> format (x * bpow radix2 e).
Proof.
intros x e Hx He.
destruct (FLT_format_generic radix2 (-1074) 53 x Hx) as [[mx ex] Hxf Hm He'].
cbn [Fnum Fexp] in Hm, He'.
apply generic_format_FLT.
apply (FLT_spec radix2 (-1074) 53 _ (Float radix2 mx (ex + e)));
  cbn [Fnum Fexp]; [|exact Hm|lia].
rewrite Hxf. unfold F2R; cbn [Fnum Fexp].
rewrite bpow_plus. ring.
Qed.

(** Scaling a normal float by [2^e] keeps it a float if the result is
    normal too. *)
Lemma format_scale :
  forall v e, format v ->
  bpow radix2 (-1022) <= Rabs v ->
  bpow radix2 (-1022) <= Rabs (v * bpow radix2 e) ->
  format (v * bpow radix2 e).
Proof.
intros v e Hf Hv Hve.
rewrite <- (round_generic radix2 fexp64 ZnearestE v Hf).
rewrite <- (round_scale ZnearestE v e Hv Hve).
apply generic_format_round; typeclasses eauto.
Qed.

(** Scaling by [2^e] and then by [2^-e] gives back the value. *)
Lemma scale_back :
  forall v e e', (e + e' = 0)%Z -> v * bpow radix2 e * bpow radix2 e' = v.
Proof.
intros v e e' He.
rewrite Rmult_assoc, <- bpow_plus, He.
apply Rmult_1_r.
Qed.

(** ** Floats *)

(** A product that is a float below [2^1024] is computed exactly. *)
Lemma mul_exact :
  forall x y : f64,
  is_finite x = true -> is_finite y = true ->
  format (B2R x * B2R y) -> Rabs (B2R x * B2R y) < bpow radix2 1024 ->
  is_finite (mul x y) = true /\ B2R (mul x y) = B2R x * B2R y /\
  Bsign (mul x y) = xorb (Bsign x) (Bsign y).
Proof.
intros x y Fx Fy Hf Hlt.
generalize (@Bmult_correct 53 1024 _ _ mode_NE x y).
change (SpecFloat.fexp 53 1024) with fexp64.
rewrite (round_generic radix2 fexp64 (round_mode mode_NE) _ Hf).
rewrite (Rlt_bool_true _ _ Hlt).
intros (HR & HF & HS).
rewrite Fx, Fy in HF.
unfold mul.
split; [exact HF|]. split; [exact HR|].
apply HS, finite_not_nan, HF.
Qed.

(** A float with the significand [2^52] and a sign bit [0] is a power of
    two. *)
Lemma B2SF_bpow :
  forall (x : f64) n,
  B2SF x = SpecFloat.S754_finite false (2^52) (n - 52) ->
  is_finite x = true /\ Bsign x = false /\ B2R x = bpow radix2 n.
Proof.
intros [s|s| |s mx ex Hx] n H; try discriminate H.
cbn [B2SF] in H. injection H as -> -> ->.
split; [reflexivity|]. split; [reflexivity|].
cbn [B2R]. unfold F2R; cbn [Fnum Fexp SpecFloat.cond_Zopp].
replace (bpow radix2 n) with (bpow radix2 (n - 52 + 52)) by (f_equal; ring).
rewrite bpow_plus, Rmult_comm.
(* [bpow radix2 52] is [IZR (2^52)] by definition. *)
f_equal.
Qed.

(** The constants of [sqrt1_slow] are the powers of two that their names
    say, all of them normal: [2^n] is [2^52 * 2^(n - 52)]. *)
Lemma two_pow_64_B2SF :
  B2SF (of_u64 (2^64)) = SpecFloat.S754_finite false (2^52) 12.
Proof. vm_compute. reflexivity. Qed.

Lemma two_pow_m64_B2SF :
  B2SF (div (of_u64 1) (of_u64 (2^64))) =
  SpecFloat.S754_finite false (2^52) (-116).
Proof. vm_compute. reflexivity. Qed.

Lemma two_pow_128_B2SF :
  B2SF (mul (of_u64 (2^64)) (of_u64 (2^64))) =
  SpecFloat.S754_finite false (2^52) 76.
Proof. vm_compute. reflexivity. Qed.

Lemma two_pow_m128_B2SF :
  B2SF (div (of_u64 1) (mul (of_u64 (2^64)) (of_u64 (2^64)))) =
  SpecFloat.S754_finite false (2^52) (-180).
Proof. vm_compute. reflexivity. Qed.

(** The square root of a positive float. *)
Lemma Bsqrt_pos :
  forall m (x : f64), is_finite x = true -> 0 < B2R x ->
  is_finite (Bsqrt m x) = true /\ Bsign (Bsqrt m x) = false /\
  B2R (Bsqrt m x) = round radix2 fexp64 (round_mode m) (sqrt (B2R x)).
Proof.
intros m x Fx Hx.
destruct (@Bsqrt_correct 53 1024 _ _ m x) as (HR & HF & HS).
assert (Hs : Bsign x = false).
{ rewrite (Bsign_B2R x Fx) by lra. apply Rlt_bool_false. lra. }
assert (HF' : is_finite (Bsqrt m x) = true).
{ rewrite HF.
  destruct x as [s|s| |[|] mx ex Hmx]; try discriminate Fx; try reflexivity.
  discriminate Hs. }
split; [exact HF'|]. split; [|exact HR].
rewrite HS by exact (finite_not_nan _ HF'). exact Hs.
Qed.

(** ** The fast-path test *)

(** The fast path accepts every finite [y] with [2^-966 <= |y| < 2^1022],
    with or without an FMA. *)
Lemma sqrt1_fast_accepts :
  forall fma (y : f64), is_finite y = true ->
  bpow radix2 (-966) <= Rabs (B2R y) < bpow radix2 1022 ->
  snd (Generic.sqrt1_fast fma y) = true.
Proof.
intros fma y Fy (Hlo & Hhi).
assert (He : (-966 <= Generic.exponent y <= 1021)%Z).
{ split.
  - (* [2^-966 <= |y| < 2^(exponent(y) + 1)] *)
    assert (H := abs_B2R_lt_exponent y Fy).
    assert (H' : bpow radix2 (-966) < bpow radix2 (Generic.exponent y + 1))
      by lra.
    apply lt_bpow in H'. lia.
  - (* A subnormal [y] has [exponent(y) = -1023]; a normal one has
       [2^exponent(y) <= |y| < 2^1022]. *)
    destruct (Z_lt_le_dec (Generic.exponent y) (-1022)) as [Hl|Hl]; [lia|].
    assert (H := bpow_exponent_le_abs_B2R y Fy Hl).
    assert (H' : bpow radix2 (Generic.exponent y) < bpow radix2 1022) by lra.
    apply lt_bpow in H'. lia. }
unfold Generic.sqrt1_fast; cbv zeta.
destruct fma; cbn [fst snd]; rewrite andb_true_iff, !Z.leb_le; lia.
Qed.

(** ** The slow path *)

(** [sqrt1_slow x f] is [Bsqrt m x] if [f] is [Bsqrt m] on the inputs that
    the fast path accepts, in any rounding mode [m]. *)
Theorem sqrt1_slow_correct :
  forall fma m (f : f64 -> option f64) x,
  (forall y, snd (Generic.sqrt1_fast fma y) = true -> f y = Some (Bsqrt m y)) ->
  Generic.sqrt1_slow x f = Some (Bsqrt m x).
Proof.
intros fma m f x Hf.
unfold Generic.sqrt1_slow; cbv zeta.
destruct (gt x zero && Generic.is_finite x) eqn:Hp.
2: {
  (* Zero, negative, infinite or NaN: [Bsqrt] does not round, and a
     positive finite [x] contradicts [Hp]. *)
  rewrite is_finite_eq in Hp. unfold fsqrt. f_equal.
  destruct x as [s|s| |[|] mx ex Hmx]; try reflexivity.
  unfold gt in Hp. rewrite Bltb_correct in Hp by reflexivity.
  rewrite Rlt_bool_true in Hp; [discriminate Hp|].
  cbn [B2R zero]. apply F2R_gt_0. reflexivity. }
apply andb_true_iff in Hp as (Hp & Fx).
rewrite is_finite_eq in Fx.
unfold gt in Hp. rewrite Bltb_correct in Hp by easy.
cbn [B2R zero] in Hp.
destruct (Rlt_bool_spec 0 (B2R x)) as [Hx0|]; [|discriminate Hp].
clear Hp.
destruct (Bsqrt_pos m x Fx Hx0) as (Fs & Ss & Rs).
assert (Hfmt := generic_format_B2R 53 1024 x).
assert (Hsx : 0 <= sqrt (B2R x)) by apply sqrt_pos.
destruct (B2SF_bpow _ 64 two_pow_64_B2SF) as (F64 & S64 & R64).
destruct (B2SF_bpow _ (-64) two_pow_m64_B2SF) as (Fm64 & Sm64 & Rm64).
destruct (B2SF_bpow _ 128 two_pow_128_B2SF) as (F128 & S128 & R128).
destruct (B2SF_bpow _ (-128) two_pow_m128_B2SF) as (Fm128 & Sm128 & Rm128).
set (c64 := of_u64 (2^64)) in *.
set (c128 := mul c64 c64) in *.
set (cm64 := div (of_u64 1) c64) in *.
set (cm128 := div (of_u64 1) c128) in *.
assert (Hb := abs_B2R_lt_emax 53 1024 x).
rewrite Rabs_pos_eq in Hb by lra.
destruct (Generic.exponent x <? 0)%Z eqn:He.
- (* [exponent(x) < 0], so [2^-1074 <= x < 1] and [x' = x * 2^128] is in
     [[2^-946, 2^128)]. It may be subnormal but it is a float. *)
  apply Z.ltb_lt in He.
  assert (Hx1 : B2R x < 1).
  { generalize (abs_B2R_lt_exponent x Fx). rewrite Rabs_pos_eq by lra.
    intros H. apply Rlt_le_trans with (1 := H).
    apply (bpow_le radix2 _ 0). lia. }
  assert (Hxm : bpow radix2 (-1074) <= B2R x).
  { apply generic_format_ge_bpow with (fexp := fexp64); [|exact Hx0|exact Hfmt].
    intros e. apply Z.le_max_r. }
  destruct (mul_exact x c128 Fx F128) as (Fx' & Rx' & _).
  { rewrite R128. apply format_scale_up; [exact Hfmt | lia]. }
  { rewrite R128, Rabs_pos_eq by (generalize (bpow_gt_0 radix2 128); nra).
    apply Rlt_le_trans with (1 * bpow radix2 1024).
    - apply Rlt_le_trans with (1 * bpow radix2 128).
      + apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact Hx1].
      + rewrite !Rmult_1_l. apply bpow_le. lia.
    - lra. }
  set (x' := mul x c128) in *.
  rewrite R128 in Rx'.
  (* [x'] is in the range of the fast path. *)
  rewrite Hf.
  2: { apply sqrt1_fast_accepts; [exact Fx'|]. rewrite Rx'.
       rewrite Rabs_pos_eq by (generalize (bpow_gt_0 radix2 128); nra).
       split.
       - apply Rle_trans with (bpow radix2 (-1074) * bpow radix2 128).
         + rewrite <- bpow_plus. apply bpow_le. lia.
         + apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Hxm].
       - apply Rlt_le_trans with (1 * bpow radix2 128).
         + apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact Hx1].
         + rewrite Rmult_1_l. apply bpow_le. lia. }
  cbv beta iota. f_equal.
  (* [sqrt(x * 2^128) = sqrt(x) * 2^64] *)
  assert (Hsq : sqrt (B2R x') = sqrt (B2R x) * bpow radix2 64).
  { rewrite Rx', sqrt_mult by (lra || apply bpow_ge_0).
    change 128%Z with (2 * 64)%Z. rewrite sqrt_bpow. reflexivity. }
  (* [sqrt(x) >= 2^-537], so the square root is normal before and after
     the scaling, and rounding it commutes with the scaling. *)
  assert (Hs537 : bpow radix2 (-537) <= sqrt (B2R x)).
  { change (-537)%Z with (Z.div (-1074) 2).
    apply Rle_trans with (1 := sqrt_bpow_ge radix2 (-1074)).
    apply sqrt_le_1_alt. exact Hxm. }
  destruct (Bsqrt_pos m x' Fx') as (Fs' & Ss' & Rs').
  { rewrite Rx'. generalize (bpow_gt_0 radix2 128). nra. }
  rewrite Hsq, round_scale in Rs'; [| typeclasses eauto | |].
  2: { rewrite Rabs_pos_eq by exact Hsx.
       apply Rle_trans with (2 := Hs537). apply bpow_le. lia. }
  2: { rewrite Rabs_pos_eq by (generalize (bpow_gt_0 radix2 64); nra).
       apply Rle_trans with (bpow radix2 (-537) * bpow radix2 64).
       - rewrite <- bpow_plus. apply bpow_le. lia.
       - apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Hs537]. }
  rewrite <- Rs in Rs'.
  (* Scaling back by [2^-64] gives [Bsqrt m x] exactly. *)
  assert (Hprod : B2R (Bsqrt m x') * B2R cm64 = B2R (Bsqrt m x)).
  { rewrite Rs', Rm64. apply scale_back. reflexivity. }
  destruct (mul_exact (Bsqrt m x') cm64 Fs' Fm64) as (Fr & Rr & Sr);
    [rewrite Hprod; apply generic_format_B2R
    | rewrite Hprod; apply abs_B2R_lt_emax |].
  apply B2R_Bsign_inj; [exact Fr | exact Fs | | ].
  + rewrite Rr. exact Hprod.
  + rewrite Sr, Ss', Sm64, Ss. reflexivity.
- (* [exponent(x) >= 0], so [1 <= x < 2^1024] and [x' = x * 2^-128] is a
     normal float in [[2^-128, 2^896)]. *)
  apply Z.ltb_ge in He.
  assert (Hx1 : 1 <= B2R x).
  { generalize (bpow_exponent_le_abs_B2R x Fx ltac:(lia)).
    rewrite Rabs_pos_eq by lra. apply Rle_trans.
    apply (bpow_le radix2 0). exact He. }
  assert (H1022 : bpow radix2 (-1022) <= 1).
  { apply (bpow_le radix2 _ 0). lia. }
  assert (Hlo : bpow radix2 (-128) <= B2R x * bpow radix2 (-128)).
  { rewrite <- (Rmult_1_l (bpow radix2 (-128))) at 1.
    apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Hx1]. }
  assert (Hlo' : bpow radix2 (-1022) <= Rabs (B2R x * bpow radix2 (-128))).
  { rewrite Rabs_pos_eq by (generalize (bpow_gt_0 radix2 (-128)); nra).
    apply Rle_trans with (2 := Hlo). apply bpow_le. lia. }
  assert (Hhi : B2R x * bpow radix2 (-128) < bpow radix2 896).
  { replace 896%Z with (1024 + -128)%Z by reflexivity. rewrite bpow_plus.
    apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact Hb]. }
  destruct (mul_exact x cm128 Fx Fm128) as (Fx' & Rx' & _).
  { rewrite Rm128. apply format_scale; [exact Hfmt | | exact Hlo'].
    rewrite Rabs_pos_eq by lra. lra. }
  { rewrite Rm128, Rabs_pos_eq by (generalize (bpow_gt_0 radix2 (-128)); nra).
    apply Rlt_le_trans with (1 := Hhi). apply bpow_le. lia. }
  set (x' := mul x cm128) in *.
  rewrite Rm128 in Rx'.
  (* [x'] is in the range of the fast path. *)
  rewrite Hf.
  2: { apply sqrt1_fast_accepts; [exact Fx'|]. rewrite Rx'.
       rewrite Rabs_pos_eq by (generalize (bpow_gt_0 radix2 (-128)); nra).
       split.
       - apply Rle_trans with (2 := Hlo). apply bpow_le. lia.
       - apply Rlt_le_trans with (1 := Hhi). apply bpow_le. lia. }
  cbv beta iota. f_equal.
  (* [sqrt(x * 2^-128) = sqrt(x) * 2^-64] *)
  assert (Hsq : sqrt (B2R x') = sqrt (B2R x) * bpow radix2 (-64)).
  { rewrite Rx', sqrt_mult by (lra || apply bpow_ge_0).
    change (-128)%Z with (2 * (-64))%Z. rewrite sqrt_bpow. reflexivity. }
  (* [sqrt(x) >= 1], so the square root is normal before and after the
     scaling, and rounding it commutes with the scaling. *)
  assert (Hs1 : 1 <= sqrt (B2R x)).
  { rewrite <- sqrt_1. apply sqrt_le_1_alt. exact Hx1. }
  destruct (Bsqrt_pos m x' Fx') as (Fs' & Ss' & Rs').
  { rewrite Rx'. generalize (bpow_gt_0 radix2 (-128)). nra. }
  rewrite Hsq, round_scale in Rs'; [| typeclasses eauto | |].
  2: { rewrite Rabs_pos_eq by exact Hsx. lra. }
  2: { rewrite Rabs_pos_eq by (generalize (bpow_gt_0 radix2 (-64)); nra).
       apply Rle_trans with (1 * bpow radix2 (-64)).
       - rewrite Rmult_1_l. apply bpow_le. lia.
       - apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Hs1]. }
  rewrite <- Rs in Rs'.
  (* Scaling back by [2^64] gives [Bsqrt m x] exactly. *)
  assert (Hprod : B2R (Bsqrt m x') * B2R c64 = B2R (Bsqrt m x)).
  { rewrite Rs', R64. apply scale_back. reflexivity. }
  destruct (mul_exact (Bsqrt m x') c64 Fs' F64) as (Fr & Rr & Sr);
    [rewrite Hprod; apply generic_format_B2R
    | rewrite Hprod; apply abs_B2R_lt_emax |].
  apply B2R_Bsign_inj; [exact Fr | exact Fs | | ].
  + rewrite Rr. exact Hprod.
  + rewrite Sr, Ss', S64, Ss. reflexivity.
Qed.
