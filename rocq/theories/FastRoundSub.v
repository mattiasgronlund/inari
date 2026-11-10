(** * Rounding tests for subnormal results

    [Fast.round_dir_sub] and [Fast.round_near_sub] of [Model.v] are the
    tests of [FastRound.v] for an [e] in [-1085, -1022], where [y 2^e] is
    below [2^-1021] and can be subnormal, so that scaling a rounded [h] by
    [2^e] would round a second time. They round [C + y] once instead, for
    [C = 2^(-1022 - e) >= 1]: the [f64]s in [[C, 2C]] are [g = 2^-52 C]
    apart, which is [2^-1074] in units of [2^-e]. [s + t = C + h] exactly
    by Fast2Sum [Dekker], and the result [(r - C) 2^e] is the [f64] whose
    bits are those of [r] less those of [C]
    ([round_dir_sub_correct], [round_near_sub_correct]).

    [Dekker] T. J. Dekker, A floating-point technique for extending the
    available precision, Numer. Math. 18 (1971). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error.
From Inari Require Import Model Mpfr Encoding TwoSum TwoProduct DyDriver NearF64 NearCells
  FastRound FastRoundSubBits FastRoundSubCommon.
From Inari Require StepUp DyExpRules.

Open Scope R_scope.

Local Notation G := (generic_format radix2 fexp64).

(** The bits, constants and grid of [FastRoundSubBits.v], and the sum [C
    + h + l] of [FastRoundSubCommon.v], are the steps of both proofs. *)

Theorem round_dir_sub_correct :
  forall h l e up v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < B2R h < 2 -> (-1085 <= e <= -1022)%Z ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  Fast.round_dir_sub h l e up = Some v ->
  rounds up (y * bpow radix2 e) v.
Proof.
intros h l e up v y Fh Fl Hrn Hh He Hy Hv.
destruct (sub_unit_spec e He) as (Fc & Bc & _).
destruct (sub_consts e He) as (F2c & R2c & Fb & Rb & _ & _).
destruct (sub_common h l e y Fh Fl Hrn Hh He Hy) as (Fs & Hk).
unfold Fast.round_dir_sub, Fast.fast_two_sum in Hv; cbv beta iota zeta in Hv.
set (c := Fast.sub_unit e) in *.
set (s := add c h) in *.
set (u := add (add h (sub c s)) l) in *.
set (b := mul c Fast.sub_err) in *.
set (g := bpow radix2 (-1074 - e)) in *.
(* The guard [s < 2C] keeps [s] in the binade of [C], where [s = C + N g]. *)
destruct (ge s (mul Fast.two c)) eqn:G0; [discriminate Hv|].
pose proof (FastRound.ge_false _ _ Fs F2c G0) as Hs2. rewrite R2c in Hs2.
destruct (Hk Hs2) as (Fu & Hy0 & N & HN & Hbits & HD1 & HD2).
apply Rabs_def2 in HD1, HD2.
destruct (gt u b) eqn:G1.
- (* [u > b]: [y] is in [(N g, (N + 1) g)], whose ends are [s - C] and its
     successor, the bits of [s] and [s + 1] less those of [C]. *)
  pose proof (FastRound.gt_true _ _ Fu Fb G1) as Hub. rewrite Rb in Hub.
  injection Hv as <-.
  replace (to_bits (if up then from_bits (to_bits s + 1) else s) - to_bits c)%Z
    with (if up then (N + 1)%Z else N).
  2: { destruct up; [rewrite to_from_bits by lia|]; rewrite Hbits, Bc; ring. }
  apply (sub_bracket e N up y); [lia | fold g; lra].
- destruct (lt u (opp b)) eqn:G2; [|discriminate Hv].
  (* [u < -b]: [y] is in [((N - 1) g, N g)], the bits of [s - 1] and [s]
     less those of [C]; [N >= 1] as [y > 0]. *)
  assert (Fob : is_finite (opp b) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fb).
  pose proof (DyExpRules.lt_R _ _ Fu Fob G2) as Hub.
  unfold opp in Hub. rewrite B2R_Bopp, Rb in Hub.
  assert (Hg : 0 < g) by apply bpow_gt_0.
  assert (HN1 : (1 <= N)%Z).
  { destruct (Z_lt_le_dec 0 N) as [HN0|HN0]; [lia|]. exfalso.
    apply IZR_le in HN0. nra. }
  injection Hv as <-.
  replace (to_bits (if up then s else from_bits (to_bits s - 1)) - to_bits c)%Z
    with (if up then (N - 1 + 1)%Z else (N - 1)%Z).
  2: { destruct up; [|rewrite to_from_bits by lia]; rewrite Hbits, Bc; ring. }
  apply (sub_bracket e (N - 1) up y); [lia|]. fold g. rewrite minus_IZR. lra.
Qed.

Theorem round_near_sub_correct :
  forall h l e v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < B2R h < 2 -> (-1085 <= e <= -1022)%Z ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  Fast.round_near_sub h l e = Some v ->
  near_round (y * bpow radix2 e) v.
Proof.
intros h l e v y Fh Fl Hrn Hh He Hy Hv.
destruct (sub_unit_spec e He) as (Fc & Bc & _).
destruct (sub_consts e He) as (F2c & R2c & _ & _ & Fb & Rb).
destruct (sub_common h l e y Fh Fl Hrn Hh He Hy) as (Fs & Hk).
unfold Fast.round_near_sub, Fast.fast_two_sum in Hv; cbv beta iota zeta in Hv.
set (c := Fast.sub_unit e) in *.
set (s := add c h) in *.
set (u := add (add h (sub c s)) l) in *.
set (b := mul c Fast.sub_near) in *.
set (g := bpow radix2 (-1074 - e)) in *.
destruct (lt s (mul Fast.two c) && lt u b && gt u (opp b)) eqn:HC; [|discriminate Hv].
apply andb_prop in HC as (HC & G2). apply andb_prop in HC as (G0 & G1).
pose proof (DyExpRules.lt_R _ _ Fs F2c G0) as Hs2. rewrite R2c in Hs2.
destruct (Hk Hs2) as (Fu & Hy0 & N & HN & Hbits & HD1 & HD2).
apply Rabs_def2 in HD1, HD2.
assert (Fob : is_finite (opp b) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fb).
pose proof (DyExpRules.lt_R _ _ Fu Fb G1) as Hub.
pose proof (FastRound.gt_true _ _ Fu Fob G2) as Hlb.
unfold opp in Hlb. rewrite B2R_Bopp in Hlb. rewrite Rb in Hub, Hlb.
(* [|u| < g/2 - g/32768] puts [y] within [g/2] of [N g], and the result
   is the [f64] whose bits are those of [s] less those of [C], [N]. *)
injection Hv as <-.
replace (to_bits s - to_bits c)%Z with N by (rewrite Hbits, Bc; ring).
destruct (small_bits N ltac:(lia)) as (Fv & Sv & Rv).
(* In units of [2^e], [g] is [2^-1074] and [y < 2^52 g] is below [2^-1022]. *)
assert (Hge : g * bpow radix2 e = bpow radix2 (-1074)).
{ unfold g. rewrite <- bpow_plus. f_equal. ring. }
assert (He0 : 0 < bpow radix2 e) by apply bpow_gt_0.
assert (Hr0 : 0 < y * bpow radix2 e) by (apply Rmult_lt_0_compat; assumption).
assert (HN52 : IZR N + 1 <= 4503599627370496).
{ rewrite <- plus_IZR. apply IZR_le. change 4503599627370496%Z with (2^52)%Z. lia. }
assert (H1022 : bpow radix2 (-1022) = 4503599627370496 * bpow radix2 (-1074)).
{ change 4503599627370496 with (bpow radix2 52). rewrite <- bpow_plus. reflexivity. }
assert (H1021 : bpow radix2 (-1021) = 2 * bpow radix2 (-1022)).
{ change 2 with (bpow radix2 1). rewrite <- bpow_plus. reflexivity. }
assert (H1074 : bpow radix2 (-1074) = 2 * bpow radix2 (-1075)).
{ change 2 with (bpow radix2 1). rewrite <- bpow_plus. reflexivity. }
assert (Hr1 : y * bpow radix2 e < (IZR N + 1) * bpow radix2 (-1074)).
{ rewrite <- Hge, <- Rmult_assoc. apply Rmult_lt_compat_r; [exact He0 | lra]. }
assert (H1074p : 0 < bpow radix2 (-1074)) by apply bpow_gt_0.
assert (Hr2 : y * bpow radix2 e < bpow radix2 (-1021)) by nra.
unfold near_round.
destruct (Rle_dec (bpow radix2 1024 - bpow radix2 970) (Rabs (y * bpow radix2 e))) as [Ho|_].
- (* No overflow: [y 2^e < 2^-1021]. *)
  exfalso. rewrite Rabs_pos_eq in Ho by lra.
  assert (bpow radix2 971 <= bpow radix2 1024) by (apply bpow_le; lia).
  assert (bpow radix2 971 = 2 * bpow radix2 970).
  { change 2 with (bpow radix2 1). rewrite <- bpow_plus. reflexivity. }
  assert (bpow radix2 (-1021) < bpow radix2 970) by (apply bpow_lt; lia).
  lra.
- split; [exact Fv | split].
  + rewrite Rv. symmetry. apply rn_sub_grid; [lra|].
    replace (y * bpow radix2 e - IZR N * bpow radix2 (-1074))
      with ((y - IZR N * g) * bpow radix2 e)
      by (rewrite Rmult_minus_distr_r, Rmult_assoc, Hge; reflexivity).
    rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 e)) by lra.
    apply Rlt_le_trans with (g / 2 * bpow radix2 e).
    * apply Rmult_lt_compat_r; [exact He0|]. apply Rabs_def1; lra.
    * lra.
  + (* [y > 0], so the sign of a zero result is [+]. *)
    intros _ _. rewrite Sv, Rlt_bool_false; [reflexivity | lra].
Qed.
