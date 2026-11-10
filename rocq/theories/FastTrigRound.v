(** * The rounding of the fast paths of [sin], [cos] and [tan]

    [DyadicTrig.fast_round_dir h l up] and [DyadicTrig.fast_round_near h l]
    of [Model.v] round a real [y] of either sign from [h + l] within a
    relative [3 * 2^-71] of it, with [h = RN(h + l)] and [2^-1000 <= |h| <=
    2^1000]: they scale [h] and [l] by the power of two that brings [|h|]
    into [1, 2), which turns the relative bound into an absolute [2^-68]
    ([unscale]), and call [Fast.round_dir_signed] or
    [Fast.round_near_signed], which take the sign and which [FastSign.v]
    proves. [fast_round_dir_correct] and [fast_round_near_correct] state
    the two roundings. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Mult_error.
From Inari Require Import Model Mpfr Encoding TwoSum TwoProduct DyDriver NearF64 NearCells FastRound.
From Inari Require MulRuTiny FastExpErr FastSign.

Open Scope R_scope.

Local Notation G := (generic_format radix2 fexp64).

(** Rounding to nearest commutes with scaling by [2^k] where [x] and [x
    2^k] are both normal: their exponents in the format then differ by [k]. *)
Lemma rn_scale :
  forall x k, x <> 0 -> (-1021 <= mag radix2 x)%Z -> (-1021 <= mag radix2 x + k)%Z ->
  RN (x * bpow radix2 k) = RN x * bpow radix2 k.
Proof.
intros x k Hx H1 H2.
unfold round, scaled_mantissa, cexp.
rewrite mag_mult_bpow by exact Hx.
unfold FLT_exp. rewrite !Z.max_l by lia.
unfold F2R; cbn [Fnum Fexp].
rewrite (Rmult_assoc x), <- bpow_plus.
replace (k + - (mag radix2 x + k - 53))%Z with (- (mag radix2 x - 53))%Z by ring.
rewrite Rmult_assoc, <- bpow_plus. f_equal. f_equal. ring.
Qed.

(** A real within [2^-55] of a float [x] with [1 <= |x| < 2] rounds to
    [x]: the neighbours of [|x|] are at least [2^-53] away, and rounding to
    nearest is odd. *)
Lemma rn_keep :
  forall x r, G x -> 1 <= Rabs x < 2 -> Rabs r <= bpow radix2 (-55) -> RN (x + r) = x.
Proof.
(* The case [x > 0] first. *)
assert (P : forall x r, G x -> 1 <= x < 2 -> Rabs r <= bpow radix2 (-55) -> RN (x + r) = x).
{ intros x r Gx Hx Hr.
  apply rn_between; [exact Gx | lra |].
  apply Rabs_le_inv in Hr.
  assert (HS : succ radix2 fexp64 x = x + bpow radix2 (-52)) by (apply succ_hi; lra).
  assert (HQ : pred radix2 fexp64 x <= x - bpow radix2 (-53)).
  { assert (bpow radix2 (-53) <= bpow radix2 (-52)) by (apply bpow_le; lia).
    destruct (Req_dec x 1) as [E0|E0].
    - rewrite (pred_lo _ Gx) by lra. lra.
    - rewrite (pred_hi _ Gx) by lra. lra. }
  assert (bpow radix2 (-55) * 2 = bpow radix2 (-54) /\
          bpow radix2 (-54) * 2 = bpow radix2 (-53) /\
          bpow radix2 (-53) * 2 = bpow radix2 (-52))
    by (cbn [bpow radix_val radix2]; repeat split; lra).
  pose proof (bpow_gt_0 radix2 (-55)).
  lra. }
intros x r Gx Hx Hr.
destruct (Rle_or_lt 0 x) as [S|S].
- rewrite Rabs_pos_eq in Hx by exact S. exact (P x r Gx Hx Hr).
- (* [x + r] is [-(-x + -r)], which rounds to [-(-x)]. *)
  rewrite Rabs_left in Hx by exact S.
  replace (x + r) with (- (- x + - r)) by ring.
  rewrite round_NE_opp, P; [ring | apply generic_format_opp; exact Gx | exact Hx |].
  rewrite Rabs_Ropp. exact Hr.
Qed.

(** The scaled pair: for [2^-1000 <= |a| <= 2^1000] with [a = RN(a + b)]
    and [E = exponent a], the exponent of [|a|], and [s = 2^-E], [a s]
    and [b s] are finite, [a s] is between [1/2] and [2] in magnitude and
    still [RN] of their sum, [E] is in [-1021, 1022], and, for a [y] of
    which [a + b] is within [3 2^-71 |y|], [y 2^-E] is within [2^-68] of
    [a s + b s]: what the tests of [FastSign.v] take. The proof shows
    that [a 2^-E] is exact and in [1, 2) in magnitude, and that [b 2^-E]
    rounds to an [l'] at most [2^-1021] away (exact unless [|b 2^-E| <
    2^-1022]). *)
Lemma unscale :
  forall a b y,
  is_finite a = true -> is_finite b = true -> B2R a = RN (B2R a + B2R b) ->
  bpow radix2 (-1000) <= Rabs (B2R a) <= bpow radix2 1000 ->
  Rabs (y - (B2R a + B2R b)) <= 3 * bpow radix2 (-71) * Rabs y ->
  let E := Generic.exponent a in
  let s := from_bits (Z.shiftl ((- E + 1023) mod 2^64) 52 mod 2^64) in
  is_finite (mul a s) = true /\ is_finite (mul b s) = true /\
  B2R (mul a s) = RN (B2R (mul a s) + B2R (mul b s)) /\
  / 2 < Rabs (B2R (mul a s)) < 2 /\ (-1021 <= E <= 1022)%Z /\
  Rabs (y * bpow radix2 (- E) - (B2R (mul a s) + B2R (mul b s))) <= bpow radix2 (-68).
Proof.
intros a b y Fa Fb Hrn Ha Hy E s.
assert (HP : 0 < bpow radix2 (-1000)) by apply bpow_gt_0.
assert (HM : 2 <= MAX) by (cbn [bpow radix_val radix2]; lra).
(* [E] is in [-1000, 1000] and [2^E <= |a| < 2^(E+1)]. *)
assert (E1 : (-1000 <= E)%Z) by (apply MulRuTiny.exponent_ge; [exact Fa | lra]).
assert (E2 : (E < 1001)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fa | lia |].
  apply Rle_lt_trans with (1 := proj2 Ha). apply bpow_lt. lia. }
assert (A1 : bpow radix2 E <= Rabs (B2R a))
  by (apply bpow_exponent_le_abs_B2R; [exact Fa | lia]).
assert (A2 : Rabs (B2R a) < bpow radix2 (E + 1)) by (apply abs_B2R_lt_exponent; exact Fa).
assert (Ma : mag radix2 (B2R a) = (E + 1)%Z :> Z).
{ apply mag_unique. replace (E + 1 - 1)%Z with E by ring. lra. }
(* [|b| <= 2^-52 |a|], from [a = RN(a + b)]. *)
assert (Hb : Rabs (B2R b) <= bpow radix2 (-52) * Rabs (B2R a)).
{ pose proof (FastExpErr.rn_err (B2R a + B2R b)) as R. rewrite <- Hrn in R.
  replace (B2R a - (B2R a + B2R b)) with (- B2R b) in R by ring. rewrite Rabs_Ropp in R.
  pose proof (Rabs_triang (B2R a) (B2R b)) as T.
  assert (R2 : Rabs (B2R b) <=
               bpow radix2 (-53) * (Rabs (B2R a) + Rabs (B2R b)) + bpow radix2 (-1075)).
  { apply Rle_trans with (1 := R). apply Rplus_le_compat_r.
    apply Rmult_le_compat_l; [apply bpow_ge_0 | exact T]. }
  clear -R2 Ha. cbn [bpow radix_val radix2] in *. lra. }
(* [|a + b| >= 2^(E-1)], so [mag (a + b) >= E]. *)
assert (Mab : (E <= mag radix2 (B2R a + B2R b))%Z).
{ apply mag_ge_bpow.
  replace (E - 1)%Z with (E + -1)%Z by ring. rewrite bpow_plus.
  change (bpow radix2 (-1)) with (/ 2).
  assert (Q : bpow radix2 (-52) * Rabs (B2R a) <= / 4 * Rabs (B2R a)).
  { apply Rmult_le_compat_r; [apply Rabs_pos | cbn [bpow radix_val radix2]; lra]. }
  pose proof (Rabs_triang_inv (B2R a) (- B2R b)) as T.
  rewrite Rabs_Ropp in T.
  replace (B2R a - - B2R b) with (B2R a + B2R b) in T by ring.
  lra. }
destruct (pow2_bits (- E) ltac:(lia)) as (Fs & Rs). fold s in Fs, Rs.
set (p := bpow radix2 (- E)) in Rs |- *.
assert (Pp : 0 < p) by apply bpow_gt_0.
assert (P1 : bpow radix2 E * p = 1).
{ unfold p. rewrite <- bpow_plus. replace (E + - E)%Z with 0%Z by ring. reflexivity. }
assert (P2 : bpow radix2 (E + 1) * p = 2).
{ unfold p. rewrite <- bpow_plus. replace (E + 1 + - E)%Z with 1%Z by ring. reflexivity. }
(* [h' = a 2^-E] is exact and in [1, 2) in magnitude. *)
assert (Ga : G (B2R a * p)).
{ apply mult_bpow_exact_FLT; [apply generic_format_B2R | rewrite Ma; lia]. }
assert (Hap : Rabs (B2R a * p) = Rabs (B2R a) * p)
  by (rewrite Rabs_mult, (Rabs_pos_eq p) by lra; reflexivity).
assert (Ha1 : 1 <= Rabs (B2R a) * p) by (rewrite <- P1; apply Rmult_le_compat_r; lra).
assert (Ha2 : Rabs (B2R a) * p < 2) by (rewrite <- P2; apply Rmult_lt_compat_r; lra).
destruct (mul_below_max a s Fa Fs) as (Fh & Rh & _).
{ rewrite Rs, Hap. lra. }
rewrite Rs, (round_generic _ _ _ _ Ga) in Rh.
(* [|b 2^-E| <= 2^-52 |a| 2^-E < 2^-51]. *)
assert (Hb1 : Rabs (B2R b * p) <= bpow radix2 (-52) * 2).
{ rewrite Rabs_mult, (Rabs_pos_eq p) by lra.
  apply Rle_trans with (bpow radix2 (-52) * Rabs (B2R a) * p).
  - apply Rmult_le_compat_r; lra.
  - rewrite Rmult_assoc. apply Rmult_le_compat_l; [apply bpow_ge_0 | lra]. }
destruct (mul_below_max b s Fb Fs) as (Fl & Rl & _).
{ rewrite Rs. apply Rle_trans with (1 := Hb1). cbn [bpow radix_val radix2]. lra. }
rewrite Rs in Rl.
(* The scaled error: [|y 2^-E - (a + b) 2^-E| <= 3 2^-71 |y 2^-E|]. *)
assert (Hy1 : Rabs (y * p - (B2R a * p + B2R b * p)) <= 3 * bpow radix2 (-71) * Rabs (y * p)).
{ replace (y * p - (B2R a * p + B2R b * p)) with ((y - (B2R a + B2R b)) * p) by ring.
  rewrite !Rabs_mult, (Rabs_pos_eq p) by lra.
  rewrite <- Rmult_assoc. apply Rmult_le_compat_r; lra. }
(* [|y 2^-E| <= 2 + 2^-50]. *)
assert (Hy2 : Rabs (y * p) <= 2 + bpow radix2 (-50)).
{ pose proof (Rabs_triang (y * p - (B2R a * p + B2R b * p)) (B2R a * p + B2R b * p)) as T.
  replace (y * p - (B2R a * p + B2R b * p) + (B2R a * p + B2R b * p)) with (y * p)
    in T by ring.
  pose proof (Rabs_triang (B2R a * p) (B2R b * p)) as T2.
  rewrite Hap in T2.
  clear -T T2 Hy1 Hb1 Ha2. cbn [bpow radix_val radix2] in *. lra. }
(* Either [b 2^-E] is exact, or it is below [2^-1022] and so is [l']. *)
assert (HL : Rabs (B2R (mul b s) - B2R b * p) <= bpow radix2 (-1021) /\
             B2R (mul a s) = RN (B2R (mul a s) + B2R (mul b s))).
{ destruct (Rlt_or_le (Rabs (B2R b * p)) (bpow radix2 (-1022))) as [Hs|Hs].
  - assert (Hl : Rabs (B2R (mul b s)) <= bpow radix2 (-1022)).
    { rewrite Rl. apply abs_round_le_generic; [typeclasses eauto .. | | lra].
      apply generic_format_FLT_bpow; [easy | lia]. }
    split.
    + apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp.
      assert (bpow radix2 (-1022) + bpow radix2 (-1022) = bpow radix2 (-1021))
        by (cbn [bpow radix_val radix2]; lra).
      lra.
    + (* [h' + l'] is within [2^-1022] of [h'], so it rounds to [h']. *)
      rewrite Rh. symmetry. apply rn_keep; [exact Ga | rewrite Hap; lra |].
      apply Rle_trans with (1 := Hl). apply bpow_le. lia.
  - (* [b 2^-E] is normal, so it is a float, and rounding the scaled sum is
       scaling the rounding of [a + b]. *)
    assert (B0 : B2R b <> 0).
    { intros B0. rewrite B0, Rmult_0_l, Rabs_R0 in Hs.
      pose proof (bpow_gt_0 radix2 (-1022)). lra. }
    assert (Mb : (-1021 <= mag radix2 (B2R b) + - E)%Z).
    { rewrite <- mag_mult_bpow by exact B0. apply mag_ge_bpow. exact Hs. }
    assert (Gb : G (B2R b * p)).
    { apply mult_bpow_exact_FLT; [apply generic_format_B2R | lia]. }
    rewrite (round_generic _ _ _ _ Gb) in Rl.
    split.
    + rewrite Rl, Rminus_diag, Rabs_R0. apply bpow_ge_0.
    + rewrite Rh, Rl, <- Rmult_plus_distr_r. unfold p.
      rewrite rn_scale, <- Hrn; [reflexivity | | lia | lia].
      intros Z0. rewrite Z0, (round_0 radix2 fexp64 ZnearestE) in Hrn.
      rewrite Hrn, Rabs_R0 in Ha. lra. }
destruct HL as (HL1 & HL2).
split; [exact Fh|]. split; [exact Fl|]. split; [exact HL2|].
split; [rewrite Rh, Hap; lra|]. split; [lia|].
(* [|y' - (h' + l')| <= 3 2^-71 (2 + 2^-50) + 2^-1021 <= 2^-68]. *)
rewrite Rh.
replace (y * p - (B2R a * p + B2R (mul b s)))
  with ((y * p - (B2R a * p + B2R b * p)) - (B2R (mul b s) - B2R b * p)) by ring.
apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp.
assert (Q : 3 * bpow radix2 (-71) * Rabs (y * p) <= 3 * bpow radix2 (-71) * (2 + bpow radix2 (-50))).
{ apply Rmult_le_compat_l; [pose proof (bpow_ge_0 radix2 (-71)); lra | exact Hy2]. }
clear -Hy1 Q HL1. cbn [bpow radix_val radix2] in *. lra.
Qed.

Theorem fast_round_dir_correct :
  forall h l up v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  bpow radix2 (-1000) <= Rabs (B2R h) <= bpow radix2 1000 ->
  Rabs (y - (B2R h + B2R l)) <= 3 * bpow radix2 (-71) * Rabs y ->
  DyadicTrig.fast_round_dir h l up = Some v ->
  rounds up y v.
Proof.
intros h l up v y Fh Fl Hrn Hh Hy Hv.
unfold DyadicTrig.fast_round_dir, DyadicTrig.fast_unscale in Hv.
cbv beta iota zeta in Hv.
(* The masked bits are [exponent h], for either sign, by conversion. *)
change (Z.land (Z.shiftr (to_bits h) 52) 2047 - 1023)%Z with (Generic.exponent h) in Hv.
replace (1023 - Generic.exponent h)%Z with (- Generic.exponent h + 1023)%Z in Hv by ring.
pose proof (unscale h l y Fh Fl Hrn Hh Hy) as U. cbv zeta in U.
destruct U as (F1 & F2 & R1 & H1 & HE & Herr).
pose proof (FastSign.round_dir_signed_correct _ _ _ _ _ _ F1 F2 R1 H1 HE Herr Hv) as H.
replace (y * bpow radix2 (- Generic.exponent h) * bpow radix2 (Generic.exponent h)) with y
  in H by (rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l; symmetry; apply Rmult_1_r).
exact H.
Qed.

Theorem fast_round_near_correct :
  forall h l v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  bpow radix2 (-1000) <= Rabs (B2R h) <= bpow radix2 1000 ->
  Rabs (y - (B2R h + B2R l)) <= 3 * bpow radix2 (-71) * Rabs y ->
  DyadicTrig.fast_round_near h l = Some v ->
  near_round y v.
Proof.
intros h l v y Fh Fl Hrn Hh Hy Hv.
unfold DyadicTrig.fast_round_near, DyadicTrig.fast_unscale in Hv.
cbv beta iota zeta in Hv.
change (Z.land (Z.shiftr (to_bits h) 52) 2047 - 1023)%Z with (Generic.exponent h) in Hv.
replace (1023 - Generic.exponent h)%Z with (- Generic.exponent h + 1023)%Z in Hv by ring.
pose proof (unscale h l y Fh Fl Hrn Hh Hy) as U. cbv zeta in U.
destruct U as (F1 & F2 & R1 & H1 & HE & Herr).
pose proof (FastSign.round_near_signed_correct _ _ _ _ _ F1 F2 R1 H1 HE Herr Hv) as H.
replace (y * bpow radix2 (- Generic.exponent h) * bpow radix2 (Generic.exponent h)) with y
  in H by (rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l; symmetry; apply Rmult_1_r).
exact H.
Qed.
