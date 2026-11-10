(** * The [f64]s of the rounding tests for subnormal results

    Helpers of [FastRoundSub.v]: the bits of [C = Fast.sub_unit e] and of
    the [f64]s of its binade, the [f64]s from 0 to [2^-1022] and rounding
    to nearest among them, the bounds that the tests compare with, which
    are [C] times [Fast.sub_err] or [Fast.sub_near] ([sub_consts]), and
    the rounding of a [y 2^e] between two multiples of [2^-1074]
    ([sub_bracket]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error.
From Flocq Require IEEE754.Binary IEEE754.Bits.
From Inari Require Import Model Mpfr Encoding TwoSum TwoProduct DyDriver NearF64 NearCells
  FastRound.
From Inari Require StepUp DyExpRules.

Open Scope R_scope.


Local Notation G := (generic_format radix2 fexp64).

(** ** The bits of the [f64]s that the tests use

    [Fast.sub_unit e] is [C = 2^(-1022 - e)] ([sub_unit_spec]). The
    [f64]s of the binade of [C], and [2C], are [C] plus a multiple [m] of
    [2^-52 C], with the bits of [C] plus [m] ([binade_bits],
    [bits_binade]). The [f64] whose bits are [k] in [[0, 2^52]] is [k
    2^-1074], a subnormal or [2^-1022] ([small_bits], [small_succ]).
    Below [2^-1021] the [f64]s are [2^-1074] apart, so rounding to
    nearest returns the multiple of [2^-1074] closer than half that
    ([rn_sub_grid]). *)

(** [to_bits] undoes [from_bits] on the bits of the finite [f64]s that
    are at least [+0]. *)
Lemma to_from_bits : forall k, (0 <= k < 2047 * 2^52)%Z -> to_bits (from_bits k) = k.
Proof.
intros k Hk.
destruct (from_bits_finite false k Hk) as (Fk & _ & _).
cbn [sign_bit] in Fk. rewrite Z.add_0_l in Fk.
unfold from_bits in Fk. unfold to_bits, from_bits.
(* [BSN2B] undoes [B2BSN] on a float that is not a NaN. *)
replace (Binary.BSN2B 53 1024 Bits.default_nan_pl64 (Binary.B2BSN 53 1024 (Bits.b64_of_bits k)))
  with (Bits.b64_of_bits k)
  by (destruct (Bits.b64_of_bits k); try (cbn in Fk; discriminate); reflexivity).
unfold Bits.bits_of_b64, Bits.b64_of_bits.
apply Bits.bits_of_binary_float_of_bits.
split; [lia|]. apply Z.lt_trans with (2047 * 2^52)%Z; [lia | reflexivity].
Qed.

(** The [f64] with bits [k] in [[0, 2^52]] is [k 2^-1074]. *)
Lemma small_bits :
  forall k, (0 <= k <= 2^52)%Z ->
  is_finite (from_bits k) = true /\ Bsign (from_bits k) = false /\
  B2R (from_bits k) = IZR k * bpow radix2 (-1074).
Proof.
intros k Hk.
destruct (from_bits_finite false k ltac:(lia)) as (F & S & R).
cbn [sign_bit] in F, S, R. rewrite Z.add_0_l in F, S, R.
split; [exact F|]. split; [exact S|]. rewrite R.
(* Below [2^52] the biased exponent is 0, at [2^52] it is 1: both have
   the scale [2^-1074] and the integral significand [k]. *)
assert (Hm : mant k = k /\ expo k = (-1074)%Z).
{ unfold mant, expo.
  destruct (Z.eq_dec k (2^52)) as [->|Hne].
  - split; reflexivity.
  - rewrite Z.div_small by lia. rewrite Z.mod_small by lia. split; reflexivity. }
unfold magnitude, F2R. cbn [Fnum Fexp]. rewrite (proj1 Hm), (proj2 Hm). reflexivity.
Qed.

(** Adding 1 to the bits [k < 2^52] gives the next [f64]. *)
Local Lemma small_succ :
  forall k, (0 <= k < 2^52)%Z ->
  B2R (from_bits (k + 1)) = succ radix2 fexp64 (B2R (from_bits k)).
Proof.
intros k Hk.
destruct (from_bits_finite false k ltac:(lia)) as (_ & _ & R0).
destruct (from_bits_finite false (k + 1) ltac:(lia)) as (_ & _ & R1).
cbn [sign_bit] in R0, R1. rewrite Z.add_0_l in R0, R1.
rewrite R0, R1. apply magnitude_succ. lia.
Qed.

(** The [f64] with biased exponent [E] and fraction [m] is [2^(E - 1023)
    + m 2^(E - 1075)], also for [m = 2^52], where it is [2^(E - 1022)]. *)
Local Lemma binade_bits :
  forall E m, (1 <= E <= 2045)%Z -> (0 <= m <= 2^52)%Z ->
  is_finite (from_bits (E * 2^52 + m)) = true /\ Bsign (from_bits (E * 2^52 + m)) = false /\
  B2R (from_bits (E * 2^52 + m)) = bpow radix2 (E - 1023) + IZR m * bpow radix2 (E - 1075).
Proof.
intros E m HE Hm.
destruct (from_bits_finite false (E * 2^52 + m) ltac:(lia)) as (F & S & R).
cbn [sign_bit] in F, S, R. rewrite Z.add_0_l in F, S, R.
split; [exact F|]. split; [exact S|]. rewrite R.
assert (H52 : IZR (2^52) = bpow radix2 52) by (apply (IZR_Zpower radix2); lia).
destruct (Z.eq_dec m (2^52)) as [->|Hne].
- (* [m = 2^52] carries into the biased exponent [E + 1]. *)
  replace (E * 2^52 + 2^52)%Z with ((E + 1) * 2^52 + 0)%Z by ring.
  rewrite magnitude_split by lia.
  rewrite (proj2 (Z.eqb_neq (E + 1) 0)) by lia.
  replace (Z.max (E + 1) 1 - 1075)%Z with (E - 1075 + 1)%Z by lia.
  unfold F2R; cbn [Fnum Fexp]. rewrite Z.add_0_l, H52, !bpow_plus.
  replace (E - 1023)%Z with (E - 1075 + 52)%Z by ring.
  rewrite bpow_plus. change (bpow radix2 1) with 2.
  replace (bpow radix2 52) with (2 * bpow radix2 51)
    by (change 2 with (bpow radix2 1); rewrite <- bpow_plus; reflexivity).
  ring.
- rewrite magnitude_split by lia.
  rewrite (proj2 (Z.eqb_neq E 0)) by lia.
  replace (Z.max E 1 - 1075)%Z with (E - 1075)%Z by lia.
  unfold F2R; cbn [Fnum Fexp]. rewrite plus_IZR, H52.
  replace (E - 1023)%Z with (52 + (E - 1075))%Z by ring.
  rewrite bpow_plus. ring.
Qed.

(** An [f64] in [[2^(E - 1023), 2^(E - 1022))] has the biased exponent
    [E], and its fraction is its distance to [2^(E - 1023)] in units of
    [2^(E - 1075)]. *)
Lemma bits_binade :
  forall (x : f64) (E : Z), is_finite x = true -> (1 <= E <= 2046)%Z ->
  bpow radix2 (E - 1023) <= B2R x < bpow radix2 (E - 1022) ->
  (E * 2^52 <= to_bits x < E * 2^52 + 2^52)%Z /\
  B2R x = bpow radix2 (E - 1023) + IZR (to_bits x - E * 2^52) * bpow radix2 (E - 1075).
Proof.
intros x E Fx HE Hx.
assert (Hp : 0 < B2R x) by (pose proof (bpow_gt_0 radix2 (E - 1023)); lra).
destruct (to_bits_finite x Fx) as (c & Hc & Hb).
assert (Sx : Bsign x = false).
{ rewrite StepUp.Bsign_B2R by (assumption || lra). apply Rlt_bool_false. lra. }
destruct (from_bits_finite (Bsign x) c Hc) as (_ & _ & Hm).
rewrite <- Hb, from_to_bits, Sx in Hm. cbv beta iota in Hm.
rewrite Hb, Sx. cbn [sign_bit]. rewrite Z.add_0_l.
destruct (magnitude_bounds c (proj1 Hc)) as ((_ & Hlt) & Hge).
(* The biased exponent [c / 2^52] is [E]: neither is below the other. *)
assert (HcE : (c / 2^52 = E)%Z).
{ assert (H1 : (E - 1023 < c / 2^52 - 1022)%Z) by (apply (lt_bpow radix2); lra).
  assert (H2 : (c / 2^52 - 1023 < E - 1022)%Z).
  { apply (lt_bpow radix2). specialize (Hge ltac:(lia)). lra. }
  lia. }
split; [zlia|].
rewrite Hm.
destruct (split_52 c (proj1 Hc)) as (Hcs & _ & HM).
rewrite HcE in Hcs.
set (M := (c mod 2^52)%Z) in *.
replace (c - E * 2^52)%Z with M by lia.
rewrite Hcs at 1.
rewrite magnitude_split by lia.
rewrite (proj2 (Z.eqb_neq E 0)) by lia.
replace (Z.max E 1 - 1075)%Z with (E - 1075)%Z by lia.
unfold F2R; cbn [Fnum Fexp]. rewrite plus_IZR, (IZR_Zpower radix2) by lia.
replace (E - 1023)%Z with (52 + (E - 1075))%Z by ring.
rewrite bpow_plus. ring.
Qed.

(** [Fast.sub_unit e] is [2^(-1022 - e)], with the biased exponent [1 -
    e]. *)
Lemma sub_unit_spec :
  forall e, (-1085 <= e <= -1022)%Z ->
  is_finite (Fast.sub_unit e) = true /\ to_bits (Fast.sub_unit e) = ((1 - e) * 2^52)%Z /\
  B2R (Fast.sub_unit e) = bpow radix2 (-1022 - e).
Proof.
intros e He.
assert (Hu : Fast.sub_unit e = from_bits ((1 - e) * 2^52 + 0)).
{ unfold Fast.sub_unit.
  rewrite (Z.mod_small (1 - e)) by (simpl Z.pow; lia).
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.mod_small by (simpl Z.pow; lia).
  rewrite Z.add_0_r. reflexivity. }
destruct (binade_bits (1 - e) 0 ltac:(lia) ltac:(lia)) as (F & _ & R).
rewrite Hu. split; [exact F|]. split.
- rewrite to_from_bits by lia. ring.
- rewrite R. replace (1 - e - 1023)%Z with (-1022 - e)%Z by ring. ring.
Qed.

(** A real in [(0, 2^-1021)] closer than [2^-1075] to [k 2^-1074] rounds
    to it to nearest. *)
Lemma rn_sub_grid :
  forall r k, 0 < r < bpow radix2 (-1021) ->
  Rabs (r - IZR k * bpow radix2 (-1074)) < bpow radix2 (-1075) ->
  RN r = IZR k * bpow radix2 (-1074).
Proof.
intros r k Hr Hk.
(* Below [2^-1021] the scale is [2^-1074]. *)
assert (Hc : cexp radix2 fexp64 r = (-1074)%Z).
{ unfold cexp.
  assert (Hm : (mag radix2 r <= -1021)%Z).
  { apply mag_le_bpow; [lra|]. rewrite Rabs_pos_eq; lra. }
  unfold FLT_exp. lia. }
unfold round, scaled_mantissa, F2R. cbn [Fnum Fexp]. rewrite Hc.
rewrite (Znearest_imp _ _ k); [reflexivity|].
replace (r * bpow radix2 (- -1074) - IZR k)
  with ((r - IZR k * bpow radix2 (-1074)) * bpow radix2 1074).
2: { change (- -1074)%Z with 1074%Z.
     rewrite Rmult_minus_distr_r, Rmult_assoc, <- bpow_plus.
     change (bpow radix2 (-1074 + 1074)) with 1. rewrite Rmult_1_r. reflexivity. }
rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0.
replace (/ 2) with (bpow radix2 (-1075) * bpow radix2 1074)
  by (rewrite <- bpow_plus; reflexivity).
apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact Hk].
Qed.

(** ** The bounds of the tests *)

(** [Fast.sub_err] is [2^-67]. *)
Local Lemma sub_err_R : B2R Fast.sub_err = bpow radix2 (-67).
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF Fast.sub_err) with (SpecFloat.S754_finite false 4503599627370496 (-119))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

(** [Fast.sub_near] is [2^-53 - 2^-67]. *)
Local Lemma sub_near_R : B2R Fast.sub_near = bpow radix2 (-53) - bpow radix2 (-67).
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF Fast.sub_near) with (SpecFloat.S754_finite false 9006649498927104 (-106))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
(* [(2^53 - 2^39) 2^-106] *)
replace (bpow radix2 (-53)) with (bpow radix2 53 * bpow radix2 (-106))
  by (rewrite <- bpow_plus; reflexivity).
replace (bpow radix2 (-67)) with (bpow radix2 39 * bpow radix2 (-106))
  by (rewrite <- bpow_plus; reflexivity).
change (bpow radix2 53) with (IZR 9007199254740992).
change (bpow radix2 39) with (IZR 549755813888).
lra.
Qed.

(** A copy of [FastRoundErr.two_R], which is local there. *)
Local Lemma two_R : B2R Fast.two = 2.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF Fast.two) with (SpecFloat.S754_finite false 4503599627370496 (-51))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

(** A product that is an [f64] below [2^1024] is exact. *)
Local Lemma mul_exact :
  forall x y : f64, is_finite x = true -> is_finite y = true ->
  G (B2R x * B2R y) -> Rabs (B2R x * B2R y) < bpow radix2 1024 ->
  is_finite (mul x y) = true /\ B2R (mul x y) = B2R x * B2R y.
Proof.
intros x y Fx Fy Fm Hm.
unfold mul.
generalize (@Bmult_correct 53 1024 _ _ mode_NE x y).
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE)) with RN.
rewrite (round_generic _ _ _ _ Fm).
rewrite Rlt_bool_true by exact Hm.
intros (HR & HF & _).
split; [rewrite HF, Fx, Fy; reflexivity | exact HR].
Qed.

(** [2C], [C 2^-67] and [C (2^-53 - 2^-67)] are exact, for [C = 2^(-1022 -
    e)]. In units of [g = 2^(-1074 - e)], the gap between the [f64]s of
    [[C, 2C]], [C 2^-67] is [g / 32768] and [C (2^-53 - 2^-67)] is [g / 2 -
    g / 32768]. *)
Lemma sub_consts :
  forall e, (-1085 <= e <= -1022)%Z ->
  is_finite (mul Fast.two (Fast.sub_unit e)) = true /\
  B2R (mul Fast.two (Fast.sub_unit e)) = 2 * bpow radix2 (-1022 - e) /\
  is_finite (mul (Fast.sub_unit e) Fast.sub_err) = true /\
  B2R (mul (Fast.sub_unit e) Fast.sub_err) = bpow radix2 (-1074 - e) / 32768 /\
  is_finite (mul (Fast.sub_unit e) Fast.sub_near) = true /\
  B2R (mul (Fast.sub_unit e) Fast.sub_near) =
    bpow radix2 (-1074 - e) / 2 - bpow radix2 (-1074 - e) / 32768.
Proof.
intros e He.
destruct (sub_unit_spec e He) as (Fc & _ & Rc).
assert (Ft : is_finite Fast.two = true) by (vm_compute; reflexivity).
assert (Fe : is_finite Fast.sub_err = true) by (vm_compute; reflexivity).
assert (Fn : is_finite Fast.sub_near = true) by (vm_compute; reflexivity).
(* Everything is a multiple of [X = 2^(-1089 - e)] = [C 2^-67]: [g] is
   [2^15 X] and [C 2^-53] is [2^14 X]. *)
set (X := bpow radix2 (-1089 - e)).
assert (HX1 : bpow radix2 (-1074 - e) = 32768 * X).
{ unfold X. replace (-1074 - e)%Z with (15 + (-1089 - e))%Z by ring.
  rewrite bpow_plus. change (bpow radix2 15) with 32768. reflexivity. }
assert (HX2 : bpow radix2 (-1022 - e) * bpow radix2 (-67) = X).
{ unfold X. rewrite <- bpow_plus. f_equal. ring. }
assert (HX3 : bpow radix2 (-1022 - e) * bpow radix2 (-53) = 16384 * X).
{ unfold X. rewrite <- bpow_plus.
  replace (-1022 - e + -53)%Z with (14 + (-1089 - e))%Z by ring.
  rewrite bpow_plus. change (bpow radix2 14) with 16384. reflexivity. }
assert (HX0 : 0 < X) by apply bpow_gt_0.
(* [2^15 X] is at most [2^11], far below [2^1024]. *)
assert (HXb : 32768 * X < bpow radix2 1024) by (rewrite <- HX1; apply bpow_lt; lia).
(* [2C = 2^(-1021 - e)] is a power of 2 in the range of the format. *)
assert (P1 : B2R Fast.two * B2R (Fast.sub_unit e) = bpow radix2 (-1021 - e)).
{ rewrite two_R, Rc. replace (-1021 - e)%Z with (1 + (-1022 - e))%Z by ring.
  rewrite bpow_plus. reflexivity. }
assert (G1 : G (B2R Fast.two * B2R (Fast.sub_unit e))).
{ rewrite P1. apply generic_format_bpow. unfold FLT_exp. lia. }
assert (B1 : Rabs (B2R Fast.two * B2R (Fast.sub_unit e)) < bpow radix2 1024).
{ rewrite P1, Rabs_pos_eq by apply bpow_ge_0. apply bpow_lt. lia. }
destruct (mul_exact _ _ Ft Fc G1 B1) as (F1 & R1).
(* [C 2^-67 = X] is a power of 2 at or above [2^-1074]. *)
assert (P2 : B2R (Fast.sub_unit e) * B2R Fast.sub_err = X) by (rewrite Rc, sub_err_R; exact HX2).
assert (G2 : G (B2R (Fast.sub_unit e) * B2R Fast.sub_err)).
{ rewrite P2. apply generic_format_bpow. unfold FLT_exp. lia. }
assert (B2 : Rabs (B2R (Fast.sub_unit e) * B2R Fast.sub_err) < bpow radix2 1024).
{ rewrite P2, Rabs_pos_eq by lra. lra. }
destruct (mul_exact _ _ Fc Fe G2 B2) as (F2 & R2).
(* [C (2^-53 - 2^-67) = 16383 X] has a 14-bit significand and the exponent
   [-1089 - e >= -4]. *)
assert (P3 : B2R (Fast.sub_unit e) * B2R Fast.sub_near = 16383 * X).
{ rewrite Rc, sub_near_R, Rmult_minus_distr_l, HX3, HX2. ring. }
assert (G3 : G (B2R (Fast.sub_unit e) * B2R Fast.sub_near)).
{ rewrite P3. apply generic_format_FLT. exists (Float radix2 16383 (-1089 - e)).
  - unfold F2R, X. cbn [Fnum Fexp]. reflexivity.
  - cbn [Fnum]. simpl. lia.
  - cbn [Fexp]. lia. }
assert (B3 : Rabs (B2R (Fast.sub_unit e) * B2R Fast.sub_near) < bpow radix2 1024).
{ rewrite P3, Rabs_pos_eq by lra. lra. }
destruct (mul_exact _ _ Fc Fn G3 B3) as (F3 & R3).
split; [exact F1|]. split.
{ rewrite R1, P1. replace (-1021 - e)%Z with (1 + (-1022 - e))%Z by ring.
  rewrite bpow_plus. reflexivity. }
split; [exact F2|]. split; [rewrite R2, P2, HX1; field|].
split; [exact F3|]. rewrite R3, P3, HX1. field.
Qed.

(** ** Rounding between two multiples of [2^-1074] *)

(** If [y] is between [K] and [K + 1] times [g = 2^(-1074 - e)], then [y
    2^e] is between [K 2^-1074] and [(K + 1) 2^-1074], the [f64]s whose
    bits are [K] and [K + 1], and rounds up to the second and down to the
    first. *)
Lemma sub_bracket :
  forall (e K : Z) (up : bool) (y : R), (0 <= K < 2^52)%Z ->
  IZR K * bpow radix2 (-1074 - e) < y < (IZR K + 1) * bpow radix2 (-1074 - e) ->
  rounds up (y * bpow radix2 e) (from_bits (if up then (K + 1)%Z else K)).
Proof.
intros e K up y HK Hy.
destruct (small_bits K ltac:(lia)) as (F0 & _ & R0).
destruct (small_bits (K + 1) ltac:(lia)) as (F1 & _ & R1).
assert (Hs : B2R (from_bits (K + 1)) = succ radix2 (SpecFloat.fexp 53 1024) (B2R (from_bits K)))
  by exact (small_succ K HK).
(* Scaling by [2^e] turns the multiples of [g = 2^(-1074 - e)] into those
   of [2^-1074]. *)
assert (He : 0 < bpow radix2 e) by apply bpow_gt_0.
assert (Hg : bpow radix2 (-1074 - e) * bpow radix2 e = bpow radix2 (-1074)).
{ rewrite <- bpow_plus. f_equal. ring. }
assert (Hb : B2R (from_bits K) < y * bpow radix2 e < B2R (from_bits (K + 1))).
{ rewrite R0, R1, plus_IZR, <- Hg. split.
  - rewrite <- Rmult_assoc. apply Rmult_lt_compat_r; [exact He | exact (proj1 Hy)].
  - rewrite <- Rmult_assoc. apply Rmult_lt_compat_r; [exact He | exact (proj2 Hy)]. }
destruct up; unfold rounds.
- exact (DyExpRules.rnd_bracket _ _ true _ F0 F1 Hs Hb).
- exact (DyExpRules.rnd_bracket _ _ false _ F0 F1 Hs Hb).
Qed.
