(** * The remainder of a division is a float

    [div1_ru_fast] computes [q = RN(x / y)] and the remainder
    [r = x - q * y] with an FMA or with Dekker's TwoProduct, and steps [q]
    up if [r] has the sign of [y]. That needs [r] to be a float, which is
    [BD03] (S. Boldo, M. Daumas, Representable correcting terms for possibly
    underflowing floating point operations, ARITH 2003). Flocq proves it
    only without subnormals ([div_error_FLX]); here is the form for
    binary64, with the bounds of the fast path, [|q| >= 2^-1022] and
    [|x| >= 2^-967].

    The argument: [x], [q] and [y] are integer multiples of [2^cexp x],
    [2^cexp q] and [2^cexp y], so [r] is an integer multiple of
    [2^min(cexp x, cexp q + cexp y)], and it is a float if it is smaller
    than [2^53] such units and the unit is at least [2^-1074]
    ([format_sub_mult]). [q] is normal, so it is within [2^-53 |q|] of
    [x / y], [|r| = |y| |q - x / y| <= 2^-53 |q y|], and since
    [|q y| <= |x| + |r|], [|r| <= 2^-52 |x|]. That bounds [r] by [2^53]
    units of [x] and of [q y], and [|q y| >= (1 - 2^-52) |x| > 2^-968]
    keeps [cexp q + cexp y >= -1073]. *)

From Stdlib Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.Core Calc.Operations Relative.
From Inari Require Import Model Encoding TwoSum.

Open Scope R_scope.

Local Notation format := (generic_format radix2 fexp64).

(** [x - q * y] is a float if it is smaller than [2^53] units of both
    [x] and [q * y], and the unit of [q * y] is at least [2^-1074]. *)
Lemma format_sub_mult :
  forall x q y, format x -> format q -> format y ->
  (-1074 <= cexp radix2 fexp64 q + cexp radix2 fexp64 y)%Z ->
  Rabs (x - q * y) < bpow radix2 (53 + cexp radix2 fexp64 x) ->
  Rabs (x - q * y) <
    bpow radix2 (53 + (cexp radix2 fexp64 q + cexp radix2 fexp64 y)) ->
  format (x - q * y).
Proof.
intros x q y Fx Fq Fy Hc Hx Hqy.
destruct (Req_dec (x - q * y) 0) as [Z|Z].
{ rewrite Z. apply generic_format_0. }
unfold generic_format in Fx, Fq, Fy.
set (fx := Float radix2 (Ztrunc (scaled_mantissa radix2 fexp64 x))
  (cexp radix2 fexp64 x)) in Fx.
set (fq := Float radix2 (Ztrunc (scaled_mantissa radix2 fexp64 q))
  (cexp radix2 fexp64 q)) in Fq.
set (fy := Float radix2 (Ztrunc (scaled_mantissa radix2 fexp64 y))
  (cexp radix2 fexp64 y)) in Fy.
(* [x - q * y] is an integer times [2^min(cexp x, cexp q + cexp y)]. *)
assert (E : x - q * y = F2R (Fminus fx (Fmult fq fy))).
{ rewrite F2R_minus, F2R_mult, <- Fx, <- Fq, <- Fy. reflexivity. }
assert (Ee : Fexp (Fminus fx (Fmult fq fy)) =
  Z.min (cexp radix2 fexp64 x)
    (cexp radix2 fexp64 q + cexp radix2 fexp64 y)).
{ unfold Fminus. rewrite Fexp_Fplus. reflexivity. }
rewrite E in Z, Hx, Hqy |- *.
revert Ee Z Hx Hqy.
destruct (Fminus fx (Fmult fq fy)) as [m e].
cbn [Fexp]. intros -> Z Hx Hqy.
apply generic_format_F2R. intros _.
(* Both bounds put the magnitude of [r] at most [53] above that exponent,
   and the exponent is at least [-1074]. *)
pose proof (mag_le_bpow radix2 _ _ Z Hx) as H1.
pose proof (mag_le_bpow radix2 _ _ Z Hqy) as H2.
unfold cexp, FLT_exp in *. lia.
Qed.

(** [|b|] is within [|a - b|] of [|a|]. *)
Lemma Rabs_close :
  forall a b, Rabs a - Rabs (a - b) <= Rabs b <= Rabs a + Rabs (a - b).
Proof.
intros a b.
pose proof (Rabs_triang b (a - b)) as H1.
pose proof (Rabs_triang a (- (a - b))) as H2.
rewrite Rabs_Ropp in H2.
replace (b + (a - b)) with a in H1 by ring.
replace (a + - (a - b)) with b in H2 by ring.
lra.
Qed.

(** [BD03]: if [q = RN(x / y)] is normal and [|x| >= 2^-967], the
    remainder [x - q * y] is a float, and at most [2^-52 |x|]. *)
Theorem div_remainder :
  forall x y, format x -> format y -> y <> 0 ->
  bpow radix2 (-1022) <= Rabs (RN (x / y)) ->
  bpow radix2 (-967) <= Rabs x ->
  format (x - RN (x / y) * y) /\
  Rabs (x - RN (x / y) * y) <= bpow radix2 (-52) * Rabs x.
Proof.
intros x y Fx Fy Zy Hq Hx.
set (q := RN (x / y)) in Hq |- *.
assert (Fq : format q).
{ unfold q. apply generic_format_round; typeclasses eauto. }
(* [q] is normal, so its half ulp is at most [2^-53 |q|]
   ([relative_error_N_FLT_round] would need [x / y] to be normal). *)
assert (Hu : Rabs (q - x / y) <= bpow radix2 (-53) * Rabs q).
{ pose proof (ulp_FLT_le radix2 (-1074) 53 q Hq) as H.
  change (1 - 53)%Z with (-52)%Z in H.
  assert (HM : bpow radix2 (-53) = / 2 * bpow radix2 (-52))
    by (cbn [bpow radix_val radix2]; lra).
  apply Rle_trans with (/ 2 * ulp radix2 fexp64 q).
  - unfold q. apply error_le_half_ulp_round; typeclasses eauto.
  - rewrite HM. lra. }
(* [r = y (x / y - q)]. *)
assert (Er : Rabs (x - q * y) = Rabs y * Rabs (q - x / y)).
{ rewrite <- Rabs_mult.
  replace (y * (q - x / y)) with (- (x - q * y)) by (field; exact Zy).
  rewrite Rabs_Ropp. reflexivity. }
assert (Hr1 : Rabs (x - q * y) <= bpow radix2 (-53) * (Rabs q * Rabs y)).
{ rewrite Er.
  pose proof (Rmult_le_compat_l _ _ _ (Rabs_pos y) Hu) as H.
  lra. }
pose proof (Rabs_close x (q * y)) as [Hqy1 Hqy2].
rewrite Rabs_mult in Hqy1, Hqy2.
(* [|q y| <= |x| + |r|] turns the bound relative to [q y] into one
   relative to [x]. *)
assert (Hr2 : Rabs (x - q * y) <= bpow radix2 (-52) * Rabs x).
{ pose proof (Rabs_pos x). pose proof (Rabs_pos (x - q * y)).
  clear - Hr1 Hqy2 H H0. cbn [bpow radix_val radix2] in *. lra. }
split; [|exact Hr2].
(* [|q y| >= (1 - 2^-52) |x| > 2^-968], and [|q y| < 2^(mag q + mag y)],
   so [cexp q + cexp y >= mag q + mag y - 106 >= -1073]. *)
assert (Hm : Rabs q * Rabs y <
  bpow radix2 (mag radix2 q + mag radix2 y)).
{ rewrite bpow_plus.
  apply Rmult_le_0_lt_compat; try apply Rabs_pos; apply bpow_mag_gt. }
assert (Hlow : bpow radix2 (-968) < Rabs q * Rabs y).
{ pose proof (Rabs_pos x).
  clear - Hr2 Hqy1 Hx H. cbn [bpow radix_val radix2] in *. lra. }
assert (Hmag : (-968 < mag radix2 q + mag radix2 y)%Z).
{ apply (lt_bpow radix2). lra. }
apply format_sub_mult; [exact Fx | exact Fq | exact Fy | | |].
- unfold cexp, FLT_exp. lia.
- (* [|r| <= |x| < 2^mag x <= 2^(53 + cexp x)]. *)
  assert (Hrx : Rabs (x - q * y) <= Rabs x).
  { pose proof (Rabs_pos x).
    clear - Hr2 H. cbn [bpow radix_val radix2] in *. lra. }
  apply Rle_lt_trans with (1 := Hrx).
  apply Rlt_le_trans with (1 := bpow_mag_gt radix2 x).
  apply bpow_le. unfold cexp, FLT_exp. lia.
- (* [|r| <= 2^-53 |q y| < 2^(mag q + mag y - 53)
     <= 2^(53 + cexp q + cexp y)]. *)
  apply Rle_lt_trans with (1 := Hr1).
  apply Rlt_le_trans with
    (bpow radix2 (-53) * bpow radix2 (mag radix2 q + mag radix2 y)).
  + apply Rmult_lt_compat_l; [apply bpow_gt_0 | exact Hm].
  + rewrite <- bpow_plus. apply bpow_le. unfold cexp, FLT_exp. lia.
Qed.
