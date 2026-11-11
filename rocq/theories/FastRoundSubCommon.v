(** * The sum [C + h + l] of the rounding tests for subnormal results

    Helper of [FastRoundSub.v]. For [C = Fast.sub_unit e = 2^(-1022 - e)]
    and an [h] in [(1/2, 2)], [Fast.fast_two_sum C h] is [(s, t)] with
    [s] rounded to nearest. When [s < 2C], also [h < C], so [s + t = C +
    h] exactly by Fast2Sum [Dekker], and [s] is [C] plus [N] times [g =
    2^(-1074 - e)], the gap between the [f64]s of [[C, 2C)] ([sub_sum]).
    [u = t + l] rounded to nearest is then [y - N g] within [g / 32768],
    and [y - N g] is below [g] ([sub_common]).

    [Dekker] T. J. Dekker, A floating-point technique for extending the
    available precision, Numer. Math. 18 (1971). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error.
From Inari Require Import Model Mpfr Encoding TwoSum TwoProduct DyDriver NearF64 NearCells
  FastRound FastRoundSubBits.
From Inari Require StepUp DyExpRules CancelLanes.

Open Scope R_scope.

Local Notation G := (generic_format radix2 fexp64).
Local Notation succ64 := (succ radix2 fexp64).
Local Notation pred64 := (pred radix2 fexp64).

(** A copy of [FastExp.fe_RN_err], which comes later in the build:
    rounding to nearest moves a real at most [2^k] by at most [2^(k -
    53)]. *)
Local Lemma fe_RN_err :
  forall z k, (-1021 <= k)%Z -> Rabs z <= bpow radix2 k -> Rabs (RN z - z) <= bpow radix2 (k - 53).
Proof.
intros z k Hk Hz.
apply Rle_trans with (/ 2 * ulp radix2 (FLT_exp (-1074) 53) z).
{ apply error_le_half_ulp; typeclasses eauto. }
apply Rle_trans with (/ 2 * ulp radix2 (FLT_exp (-1074) 53) (bpow radix2 k)).
{ apply Rmult_le_compat_l; [lra|]. apply ulp_le; [typeclasses eauto .. |].
  rewrite (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0. exact Hz. }
rewrite ulp_bpow.
replace (FLT_exp (-1074) 53 (k + 1)) with (1 + (k - 53))%Z by (unfold FLT_exp; lia).
rewrite bpow_plus. change (bpow radix2 1) with 2. lra.
Qed.

(** [h = RN (h + l)] puts [l] within half the gaps around [h]: at most
    [2^-53] for [h] in [(1/2, 2)], and at most [2^-54] below 1. *)
Local Lemma l_bound :
  forall h l : f64,
  is_finite h = true -> B2R h = RN (B2R h + B2R l) -> / 2 < B2R h < 2 ->
  Rabs (B2R l) <= bpow radix2 (-53) /\ (B2R h < 1 -> Rabs (B2R l) <= bpow radix2 (-54)).
Proof.
intros h l Fh Hrn Hh.
destruct (FastRound.low_bounds h l Fh Hrn Hh) as (Hu & Hd & _ & _).
pose proof (generic_format_B2R _ _ h) as Fx.
assert (HP : bpow radix2 (-52) = 2 * bpow radix2 (-53) /\
             bpow radix2 (-53) = 2 * bpow radix2 (-54))
  by (cbn [bpow radix_val radix2]; split; lra).
pose proof (bpow_gt_0 radix2 (-54)) as H54.
destruct (Rlt_or_le (B2R h) 1) as [H1 | H1].
- (* Below 1 the gaps on both sides of [h] are [2^-53]. *)
  rewrite FastRound.succ_lo in Hu by lra.
  rewrite FastRound.pred_lo in Hd by (exact Fx || lra).
  assert (Hl : Rabs (B2R l) <= bpow radix2 (-54)) by (apply Rabs_le; lra).
  split; [lra | intros _; exact Hl].
- (* From 1 on the gap above is [2^-52], and so is the gap below, except
     at [h = 1] where it is [2^-53]. *)
  rewrite FastRound.succ_hi in Hu by lra.
  assert (Hd' : B2R h - pred64 (B2R h) <= bpow radix2 (-52)).
  { destruct (Rle_lt_or_eq_dec 1 (B2R h) H1) as [H1' | H1'].
    - rewrite FastRound.pred_hi by (exact Fx || lra). lra.
    - rewrite FastRound.pred_lo by (exact Fx || lra). lra. }
  split; [apply Rabs_le; lra | intros H; lra].
Qed.

(** [C + h] rounded to nearest is finite. Below [2C], [h < C], the error
    [t] of the sum is exact (Fast2Sum) and at most [g / 2], and the sum is
    [C + N g] with bits [(1 - e) 2^52 + N]. *)
Local Lemma sub_sum :
  forall (h : f64) (e : Z),
  is_finite h = true -> / 2 < B2R h < 2 -> (-1085 <= e <= -1022)%Z ->
  is_finite (add (Fast.sub_unit e) h) = true /\
  (B2R (add (Fast.sub_unit e) h) < 2 * bpow radix2 (-1022 - e) ->
   B2R h < bpow radix2 (-1022 - e) /\
   is_finite (add h (sub (Fast.sub_unit e) (add (Fast.sub_unit e) h))) = true /\
   B2R (add h (sub (Fast.sub_unit e) (add (Fast.sub_unit e) h))) =
     bpow radix2 (-1022 - e) + B2R h - B2R (add (Fast.sub_unit e) h) /\
   Rabs (B2R (add h (sub (Fast.sub_unit e) (add (Fast.sub_unit e) h))))
     <= bpow radix2 (-1074 - e) / 2 /\
   exists N : Z, (0 <= N < 2^52)%Z /\
     to_bits (add (Fast.sub_unit e) h) = ((1 - e) * 2^52 + N)%Z /\
     B2R (add (Fast.sub_unit e) h) = bpow radix2 (-1022 - e) + IZR N * bpow radix2 (-1074 - e)).
Proof.
intros h e Fh Hh He.
destruct (sub_unit_spec e He) as (Fc & _ & Hc).
assert (H2C : 2 * bpow radix2 (-1022 - e) = bpow radix2 (-1021 - e)).
{ replace (-1021 - e)%Z with (1 + (-1022 - e))%Z by ring.
  rewrite bpow_plus. reflexivity. }
(* [C] is between [1] and [2^63], so [C + h] is far below the overflow
   threshold. *)
assert (HC : 1 <= bpow radix2 (-1022 - e) <= bpow radix2 63).
{ split.
  - change 1 with (bpow radix2 0). apply bpow_le. lia.
  - apply bpow_le. lia. }
assert (HM : bpow radix2 63 + 2 <= bpow radix2 1023)
  by (cbn [bpow radix_val radix2]; lra).
assert (Hsum : Rabs (B2R (Fast.sub_unit e) + B2R h) <= bpow radix2 1023 + bpow radix2 971).
{ rewrite Hc, Rabs_pos_eq by lra. pose proof (bpow_ge_0 radix2 971). lra. }
destruct (add_no_overflow (Fast.sub_unit e) h Fc Fh Hsum) as (Fs & Hs).
set (s := add (Fast.sub_unit e) h) in *.
rewrite Hc in Hs.
split; [exact Fs|].
intros Hlt.
(* [C] and [2C] are [f64]s and rounding is monotone: [s < 2C] forces
   [C + h < 2C], and [C <= C + h] gives [C <= s]. *)
assert (HhC : B2R h < bpow radix2 (-1022 - e)).
{ apply Rnot_le_lt. intros HCh.
  assert (H2 : bpow radix2 (-1021 - e) <= RN (bpow radix2 (-1022 - e) + B2R h)).
  { apply round_ge_generic; [typeclasses eauto .. | |].
    - apply generic_format_bpow. unfold FLT_exp. lia.
    - lra. }
  lra. }
assert (HCs : bpow radix2 (-1022 - e) <= B2R s).
{ rewrite Hs. apply round_ge_generic; [typeclasses eauto .. | |].
  - apply generic_format_bpow. unfold FLT_exp. lia.
  - lra. }
split; [exact HhC|].
(* Fast2Sum [Dekker] applies as [|h| <= C]. *)
assert (Hle : Rabs (B2R h) <= Rabs (B2R (Fast.sub_unit e))).
{ rewrite Hc, !Rabs_pos_eq; lra. }
rewrite <- Hc in Hs.
destruct (CancelLanes.fast_two_sum (Fast.sub_unit e) h s Fc Fh Hle Fs Hs) as (Ft & Ht).
rewrite Hc in Hs, Ht.
split; [exact Ft|].
split; [exact Ht|].
split.
- (* [t] is the rounding error of [s], at most half the gap [g] between
     the [f64]s of [[C, 2C)]. *)
  rewrite Ht, Hs.
  replace (bpow radix2 (-1022 - e) + B2R h - RN (bpow radix2 (-1022 - e) + B2R h))
    with (- (RN (bpow radix2 (-1022 - e) + B2R h) - (bpow radix2 (-1022 - e) + B2R h)))
    by ring.
  rewrite Rabs_Ropp.
  replace (bpow radix2 (-1074 - e) / 2)
    with (/ 2 * ulp radix2 fexp64 (bpow radix2 (-1022 - e) + B2R h)).
  { apply error_le_half_ulp; typeclasses eauto. }
  rewrite ulp_neq_0 by lra. unfold cexp.
  rewrite (mag_unique_pos radix2 _ (-1021 - e)).
  + replace (FLT_exp (-1074) 53 (-1021 - e)) with (-1074 - e)%Z by (unfold FLT_exp; lia).
    field.
  + replace (-1021 - e - 1)%Z with (-1022 - e)%Z by ring. lra.
- (* [s] is in the binade [[C, 2C)], whose biased exponent is [1 - e]. *)
  assert (HE : (1 <= 1 - e <= 2046)%Z) by lia.
  assert (Hb : bpow radix2 (1 - e - 1023) <= B2R s < bpow radix2 (1 - e - 1022)).
  { replace (1 - e - 1023)%Z with (-1022 - e)%Z by ring.
    replace (1 - e - 1022)%Z with (-1021 - e)%Z by ring. lra. }
  destruct (bits_binade s (1 - e) Fs HE Hb) as (HN1 & HN2).
  exists (to_bits s - (1 - e) * 2^52)%Z.
  split; [lia|].
  split; [ring|].
  replace (1 - e - 1023)%Z with (-1022 - e)%Z in HN2 by ring.
  replace (1 - e - 1075)%Z with (-1074 - e)%Z in HN2 by ring.
  exact HN2.
Qed.

(** What the tests of [FastRoundSub.v] compare: with [s] and [t] as in
    [sub_sum] and [u = t + l] rounded to nearest, [y - N g] is [u] within
    [g / 32768], and below [g]; and [y > 0]. *)
Lemma sub_common :
  forall (h l : f64) (e : Z) (y : R),
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < B2R h < 2 -> (-1085 <= e <= -1022)%Z ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  is_finite (add (Fast.sub_unit e) h) = true /\
  (B2R (add (Fast.sub_unit e) h) < 2 * bpow radix2 (-1022 - e) ->
   is_finite (add (add h (sub (Fast.sub_unit e) (add (Fast.sub_unit e) h))) l) = true /\
   0 < y /\
   exists N : Z, (0 <= N < 2^52)%Z /\
     to_bits (add (Fast.sub_unit e) h) = ((1 - e) * 2^52 + N)%Z /\
     Rabs (y - IZR N * bpow radix2 (-1074 - e)
           - B2R (add (add h (sub (Fast.sub_unit e) (add (Fast.sub_unit e) h))) l))
       < bpow radix2 (-1074 - e) / 32768 /\
     Rabs (y - IZR N * bpow radix2 (-1074 - e)) < bpow radix2 (-1074 - e)).
Proof.
intros h l e y Fh Fl Hrn Hh He Hy.
destruct (sub_sum h e Fh Hh He) as (Fs & Hsub).
split; [exact Fs|].
intros Hlt.
destruct (Hsub Hlt) as (HhC & Ft & Ht & Htg & N & HN & Hbits & HsN).
set (s := add (Fast.sub_unit e) h) in *.
set (t := add h (sub (Fast.sub_unit e) s)) in *.
destruct (l_bound h l Fh Hrn Hh) as (Hl53 & Hl54).
assert (HP : bpow radix2 (-52) = 2 * bpow radix2 (-53) /\
             bpow radix2 (-53) = 2 * bpow radix2 (-54) /\
             bpow radix2 (-52) = 65536 * bpow radix2 (-68) /\
             bpow radix2 (-53) <= / 65536 / 65536 /\
             bpow radix2 (-53) <= / 4 /\ bpow radix2 (-68) <= / 4)
  by (cbn [bpow radix_val radix2]; repeat split; lra).
(* [g = C 2^-52] with [C = 2^(-1022 - e) >= 1]. *)
assert (HgC : bpow radix2 (-1074 - e) = bpow radix2 (-1022 - e) * bpow radix2 (-52)).
{ rewrite <- bpow_plus. f_equal. ring. }
assert (HC : 1 <= bpow radix2 (-1022 - e)).
{ change 1 with (bpow radix2 0). apply bpow_le. lia. }
pose proof (bpow_gt_0 radix2 (-52)) as H52.
(* [|l| <= g / 4]: at [e = -1022], [C = 1 > h], so [|l| <= 2^-54 = g / 4];
   below, [C >= 2] and [|l| <= 2^-53 <= g / 4]. *)
assert (Hlg : Rabs (B2R l) <= bpow radix2 (-1074 - e) / 4).
{ destruct (Z.eq_dec e (-1022)) as [E | E].
  - assert (HC1 : bpow radix2 (-1022 - e) = 1) by (rewrite E; reflexivity).
    rewrite HC1 in HhC, HgC.
    specialize (Hl54 HhC). lra.
  - assert (HC2 : 2 <= bpow radix2 (-1022 - e)).
    { change 2 with (bpow radix2 1). apply bpow_le. lia. }
    assert (2 * bpow radix2 (-52) <= bpow radix2 (-1074 - e)).
    { rewrite HgC. apply Rmult_le_compat_r; lra. }
    lra. }
assert (Hg52 : bpow radix2 (-52) <= bpow radix2 (-1074 - e)) by (apply bpow_le; lia).
assert (Hg11 : bpow radix2 (-1074 - e) <= bpow radix2 1023) by (apply bpow_le; lia).
pose proof (bpow_ge_0 radix2 971) as H971.
apply Rabs_le_inv in Htg, Hlg, Hy.
assert (Htl : Rabs (B2R t + B2R l) <= bpow radix2 (-1074 - e)) by (apply Rabs_le; lra).
destruct (add_no_overflow t l Ft Fl ltac:(lra)) as (Fu & Hu).
set (u := add t l) in *.
split; [exact Fu|].
split; [apply Rabs_le_inv in Hl53; lra|].
exists N.
split; [exact HN|].
split; [exact Hbits|].
(* [u] is [t + l] within [2^-53 g]. *)
assert (Hk : (-1021 <= -1074 - e)%Z) by lia.
pose proof (fe_RN_err (B2R t + B2R l) (-1074 - e) Hk Htl) as Hue.
rewrite <- Hu in Hue.
replace (-1074 - e - 53)%Z with ((-1074 - e) + (-53))%Z in Hue by ring.
rewrite bpow_plus in Hue.
apply Rabs_le_inv in Hue.
assert (Hg53 : bpow radix2 (-1074 - e) * bpow radix2 (-53)
               <= bpow radix2 (-1074 - e) * (/ 65536 / 65536)).
{ apply Rmult_le_compat_l; [apply bpow_ge_0 | lra]. }
(* [t = C + h - s = h - N g], so [y - N g - u = (y - h - l) + (t + l - u)]
   and [y - N g = (y - h - l) + t + l]. *)
assert (Ht' : B2R t = B2R h - IZR N * bpow radix2 (-1074 - e)) by (rewrite Ht, HsN; ring).
split; apply Rabs_lt; lra.
Qed.

(** [sub_common] for a bound [2^-p] on [|y - (h + l)|], [p] from 55 to 105,
    in place of [2^-68], as [FastRoundWideErr.v] needs: [y - N g] is [u]
    within [2^-p + 2^-105 C <= 2 2^-p C], for [C = 2^(-1022 - e) >= 1]. *)
Lemma sub_common_err :
  forall (h l : f64) (e p : Z) (y : R),
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < B2R h < 2 -> (-1085 <= e <= -1022)%Z -> (55 <= p <= 105)%Z ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (- p) ->
  is_finite (add (Fast.sub_unit e) h) = true /\
  (B2R (add (Fast.sub_unit e) h) < 2 * bpow radix2 (-1022 - e) ->
   is_finite (add (add h (sub (Fast.sub_unit e) (add (Fast.sub_unit e) h))) l) = true /\
   0 < y /\
   exists N : Z, (0 <= N < 2^52)%Z /\
     to_bits (add (Fast.sub_unit e) h) = ((1 - e) * 2^52 + N)%Z /\
     Rabs (y - IZR N * bpow radix2 (-1074 - e)
           - B2R (add (add h (sub (Fast.sub_unit e) (add (Fast.sub_unit e) h))) l))
       <= 2 * bpow radix2 (- p) * bpow radix2 (-1022 - e) /\
     Rabs (y - IZR N * bpow radix2 (-1074 - e)) < bpow radix2 (-1074 - e)).
Proof.
intros h l e p y Fh Fl Hrn Hh He Hp Hy.
destruct (sub_sum h e Fh Hh He) as (Fs & Hsub).
split; [exact Fs|].
intros Hlt.
destruct (Hsub Hlt) as (HhC & Ft & Ht & Htg & N & HN & Hbits & HsN).
set (s := add (Fast.sub_unit e) h) in *.
set (t := add h (sub (Fast.sub_unit e) s)) in *.
destruct (l_bound h l Fh Hrn Hh) as (Hl53 & Hl54).
assert (HP : bpow radix2 (-52) = 2 * bpow radix2 (-53) /\
             bpow radix2 (-53) = 2 * bpow radix2 (-54) /\
             bpow radix2 (-52) = 8 * bpow radix2 (-55) /\
             bpow radix2 (-53) <= / 4 /\ bpow radix2 (-55) <= / 4)
  by (cbn [bpow radix_val radix2]; repeat split; lra).
(* [g = C 2^-52] with [C = 2^(-1022 - e) >= 1]. *)
assert (HgC : bpow radix2 (-1074 - e) = bpow radix2 (-1022 - e) * bpow radix2 (-52)).
{ rewrite <- bpow_plus. f_equal. ring. }
assert (HC : 1 <= bpow radix2 (-1022 - e)).
{ change 1 with (bpow radix2 0). apply bpow_le. lia. }
pose proof (bpow_gt_0 radix2 (-52)) as H52.
(* [2^-p <= 2^-55], and [2^-p <= 2^-p C] as [C >= 1]. *)
assert (Hp55 : bpow radix2 (- p) <= bpow radix2 (-55)) by (apply bpow_le; lia).
pose proof (Rmult_le_compat_l (bpow radix2 (- p)) 1 (bpow radix2 (-1022 - e))
              (bpow_ge_0 _ _) HC) as HpC.
rewrite Rmult_1_r in HpC.
(* [|l| <= g / 4]: at [e = -1022], [C = 1 > h], so [|l| <= 2^-54 = g / 4];
   below, [C >= 2] and [|l| <= 2^-53 <= g / 4]. *)
assert (Hlg : Rabs (B2R l) <= bpow radix2 (-1074 - e) / 4).
{ destruct (Z.eq_dec e (-1022)) as [E | E].
  - assert (HC1 : bpow radix2 (-1022 - e) = 1) by (rewrite E; reflexivity).
    rewrite HC1 in HhC, HgC.
    specialize (Hl54 HhC). lra.
  - assert (HC2 : 2 <= bpow radix2 (-1022 - e)).
    { change 2 with (bpow radix2 1). apply bpow_le. lia. }
    assert (2 * bpow radix2 (-52) <= bpow radix2 (-1074 - e)).
    { rewrite HgC. apply Rmult_le_compat_r; lra. }
    lra. }
assert (Hg52 : bpow radix2 (-52) <= bpow radix2 (-1074 - e)) by (apply bpow_le; lia).
assert (Hg11 : bpow radix2 (-1074 - e) <= bpow radix2 1023) by (apply bpow_le; lia).
pose proof (bpow_ge_0 radix2 971) as H971.
apply Rabs_le_inv in Htg, Hlg, Hy.
assert (Htl : Rabs (B2R t + B2R l) <= bpow radix2 (-1074 - e)) by (apply Rabs_le; lra).
destruct (add_no_overflow t l Ft Fl ltac:(lra)) as (Fu & Hu).
set (u := add t l) in *.
split; [exact Fu|].
split; [apply Rabs_le_inv in Hl53; lra|].
exists N.
split; [exact HN|].
split; [exact Hbits|].
(* [u] is [t + l] within [2^-53 g]. *)
assert (Hk : (-1021 <= -1074 - e)%Z) by lia.
pose proof (fe_RN_err (B2R t + B2R l) (-1074 - e) Hk Htl) as Hue.
rewrite <- Hu in Hue.
replace (-1074 - e - 53)%Z with ((-1074 - e) + (-53))%Z in Hue by ring.
rewrite bpow_plus in Hue.
apply Rabs_le_inv in Hue.
(* [2^-53 g = 2^-105 C <= 2^-p C], as [p <= 105]. *)
assert (H105 : bpow radix2 (-1074 - e) * bpow radix2 (-53)
               <= bpow radix2 (- p) * bpow radix2 (-1022 - e)).
{ rewrite <- (bpow_plus radix2 (-1074 - e) (-53)).
  replace (-1074 - e + -53)%Z with (-105 + (-1022 - e))%Z by ring.
  rewrite (bpow_plus radix2 (-105) (-1022 - e)).
  apply Rmult_le_compat_r; [apply bpow_ge_0 | apply bpow_le; lia]. }
(* [t = C + h - s = h - N g], so [y - N g - u = (y - h - l) + (t + l - u)]
   and [y - N g = (y - h - l) + t + l]. *)
assert (Ht' : B2R t = B2R h - IZR N * bpow radix2 (-1074 - e)) by (rewrite Ht, HsN; ring).
split; [apply Rabs_le | apply Rabs_lt]; lra.
Qed.
