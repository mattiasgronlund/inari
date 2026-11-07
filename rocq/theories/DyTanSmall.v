(** * The rule of [tan] for small arguments before Ziv's strategy

    [tan_small] of [DyadicTrig] in [Model.v], which [tan_dir] tries for
    [|x| >= 2^-26] before [ziv]. For [t = |x|] in [[2^-26, 2^-14)], with
    [g], [m] and [s] as in [DySinSmall.v], [t^3/3 = c g] with [c = m^3 /
    (3 2^(s + 64))]. [tan t] lies in [(t + c g, t + (c + w) g)] with [w =
    t^5 / (4 g)] ([tan_small_real], from the bounds of [sin] and [cos]
    of [DySinSmall.v] and [DyCosSmall.v]). Where [j], the floor of [c], is
    also the floor of [c + b], for a bound [b] above [w], [tan t] lies
    strictly between [t + j g] and [t + (j + 1) g] ([tan_small_bracket]).
    Where also [f + j < 2^52] for the stored significand [f] of [t], these
    are the [f64]s whose patterns are those of [t] plus [j] and that plus
    1. [tan] is odd, as [sin] is ([tan_small_rule]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Encoding Decompose MpfrRound DyExpRules DyTrigTiny
  DyTrigSmall DyCosSmall DySinSmall.

Open Scope R_scope.

Local Notation rnd_of up := (if up then RNDU else RNDD).

(** For [0 < a < 2^-14], [a + a^3/3 < tan a < a + a^3/3 + a^5/4], with
    [tan a = sin a / cos a] and [cos a > 1 - a^2/2 > 0]. Below, [(a +
    a^3/3) cos a <= (a + a^3/3) (1 - a^2/2 + a^4/24) = a - a^3/6 - a^5/8 +
    a^7/72] ([cos_small_real]) is less than [a - a^3/6 < sin a]
    ([sin_small_real]), as [a^2 < 9]. Above, [sin a <= a - a^3/6 +
    a^5/120] is less than [a - a^3/6 + a^5/12 - a^7/8 = (a + a^3/3 +
    a^5/4) (1 - a^2/2) < (a + a^3/3 + a^5/4) cos a], as [a^2 < 3/5]. *)
Lemma tan_small_real :
  forall a, 0 < a < bpow radix2 (-14) ->
  a + a ^ 3 / 3 < tan a < a + a ^ 3 / 3 + a ^ 5 / 4.
Proof.
intros a Ha.
assert (H13 : bpow radix2 (-14) < bpow radix2 (-13)) by (apply bpow_lt; lia).
destruct (cos_small_real a Ha) as [C1 C2].
destruct (sin_small_real a ltac:(lra)) as [S1 S2].
assert (Hb : bpow radix2 (-14) = 1 / 16384) by (cbn [bpow radix_val radix2]; lra).
rewrite Hb in Ha.
assert (Haa : a * a < 1 / 4).
{ apply Rlt_trans with (1 / 16384 * (1 / 16384)); [|lra].
  apply Rmult_le_0_lt_compat; lra. }
assert (E2 : a ^ 2 = a * a) by ring.
assert (P3 : 0 < a ^ 3) by (apply pow_lt; lra).
assert (P5 : 0 < a ^ 5) by (apply pow_lt; lra).
assert (Hc : 0 < cos a) by lra.
assert (Et : tan a * cos a = sin a) by (unfold tan; field; lra).
assert (H7 : a ^ 7 < a ^ 5 * (1 / 4)).
{ replace (a ^ 7) with (a ^ 5 * (a * a)) by ring. apply Rmult_lt_compat_l; lra. }
(* [(a + a^3/3) cos a <= a - a^3/6 - a^5/8 + a^7/72 < a - a^3/6 < sin a]. *)
assert (L1 : (a + a ^ 3 / 3) * cos a <= (a + a ^ 3 / 3) * (1 - a ^ 2 / 2 + a ^ 4 / 24))
  by (apply Rmult_le_compat_l; lra).
replace ((a + a ^ 3 / 3) * (1 - a ^ 2 / 2 + a ^ 4 / 24))
  with (a - a ^ 3 / 6 - a ^ 5 / 8 + a ^ 7 / 72) in L1 by field.
(* [sin a <= a - a^3/6 + a^5/120 < a - a^3/6 + a^5/12 - a^7/8
   < (a + a^3/3 + a^5/4) cos a]. *)
assert (U1 : (a + a ^ 3 / 3 + a ^ 5 / 4) * (1 - a ^ 2 / 2)
             < (a + a ^ 3 / 3 + a ^ 5 / 4) * cos a)
  by (apply Rmult_lt_compat_l; lra).
replace ((a + a ^ 3 / 3 + a ^ 5 / 4) * (1 - a ^ 2 / 2))
  with (a - a ^ 3 / 6 + a ^ 5 / 12 - a ^ 7 / 8) in U1 by field.
split.
- apply (Rmult_lt_reg_r (cos a)); [exact Hc|]. lra.
- apply (Rmult_lt_reg_r (cos a)); [exact Hc|]. lra.
Qed.

(** [2^n] as a real, as [IZR_pow2] of [RoundUpExact.v] gives it. *)
Lemma IZR_pow2_tan : forall n, (0 <= n)%Z -> IZR (2 ^ n) = bpow radix2 n.
Proof. intros n Hn. exact (IZR_Zpower radix2 n Hn). Qed.

(** The bracket of [tan_small] in reals. For [t = M g] with [g = 2^(E -
    1075)], [2^52 <= M < 2^53] and [E] in [[997, 1008]], [s = 2086 - 2 E]
    and [d = 2 E - 1949], [M^3 = h 2^64 + l] with [0 <= l < 2^64], and [j
    = h / 2^s / 3 = M^3 / D] (floor) for [D = 3 2^(s + 64)]. [j D <= M^3]
    puts [j g] at or below [M^3 g^3 / 3 = t^3/3], as [2^(s + 64) g^2 = 1].
    [(h + 2^d) / 2^s / 3 = j] gives [M^3 + 2^(d + 64) < (j + 1) D], which
    puts [t^3/3 + t^5/4] below [(j + 1) g], as [t < 2^(E - 1022)] makes
    [t^5] less than [2^(d + 64) g^3 = 2^(5 E - 5110)]. So [t + j g < tan
    t < t + (j + 1) g] ([tan_small_real]; [t < 2^-14]). *)
Lemma tan_small_bracket :
  forall E M h l, (997 <= E <= 1008)%Z -> (2 ^ 52 <= M < 2 ^ 53)%Z ->
  (h * 2 ^ 64 + l = M * M * M)%Z -> (0 <= l < 2 ^ 64)%Z -> (0 <= h)%Z ->
  ((h + 2 ^ (2 * E - 1949)) / 2 ^ (2086 - 2 * E) / 3 = h / 2 ^ (2086 - 2 * E) / 3)%Z ->
  IZR M * bpow radix2 (E - 1075)
    + IZR (h / 2 ^ (2086 - 2 * E) / 3) * bpow radix2 (E - 1075)
  < tan (IZR M * bpow radix2 (E - 1075))
  < IZR M * bpow radix2 (E - 1075)
    + (IZR (h / 2 ^ (2086 - 2 * E) / 3) + 1) * bpow radix2 (E - 1075).
Proof.
intros E M h l HE HM HN Hl Hh Hj.
set (s := (2086 - 2 * E)%Z) in *.
set (d := (2 * E - 1949)%Z) in *.
set (j := (h / 2 ^ s / 3)%Z) in *.
assert (Ps : (0 < 2 ^ s)%Z) by (apply Z.pow_pos_nonneg; unfold s; lia).
assert (Pd : (0 < 2 ^ d)%Z) by (apply Z.pow_pos_nonneg; unfold d; lia).
(* [j D <= M^3] and [M^3 + 2^(d + 64) < (j + 1) D], with [D = 2^s 3 2^64]. *)
assert (Z1 : (j * (2 ^ s * 3) <= h)%Z).
{ unfold j. rewrite Z.div_div by lia. rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
assert (Z2 : (h + 2 ^ d < (j + 1) * (2 ^ s * 3))%Z).
{ rewrite <- Hj, Z.div_div by lia.
  pose proof (Z.mul_succ_div_gt (h + 2 ^ d) (2 ^ s * 3) ltac:(lia)) as H. lia. }
assert (Z1' : (j * (2 ^ s * 3) * 2 ^ 64 <= M * M * M)%Z).
{ rewrite <- HN. assert (H64 : (0 < 2 ^ 64)%Z) by lia.
  pose proof (Z.mul_le_mono_nonneg_r _ _ (2 ^ 64) ltac:(lia) Z1). lia. }
assert (Z2' : (M * M * M + 2 ^ d * 2 ^ 64 < (j + 1) * (2 ^ s * 3) * 2 ^ 64)%Z).
{ rewrite <- HN. assert (H64 : (0 < 2 ^ 64)%Z) by lia.
  assert (Z3 : (h + 2 ^ d + 1 <= (j + 1) * (2 ^ s * 3))%Z) by lia.
  pose proof (Z.mul_le_mono_nonneg_r _ _ (2 ^ 64) ltac:(lia) Z3). lia. }
apply IZR_le in Z1'. apply IZR_lt in Z2'.
rewrite !mult_IZR, !IZR_pow2_tan in Z1' by (unfold s; lia).
rewrite !plus_IZR, !mult_IZR, !plus_IZR, !IZR_pow2_tan in Z2' by (unfold s, d; lia).
set (g := bpow radix2 (E - 1075)) in *.
set (P := bpow radix2 s) in *.
set (Q := bpow radix2 d) in *.
set (K := bpow radix2 64) in *.
assert (Hg : 0 < g) by apply bpow_gt_0.
assert (HK : 0 < K) by apply bpow_gt_0.
(* [2^(s + 64) g^2 = 1] and [2^(d + 64) g^3 = 2^(5 E - 5110)]. *)
assert (R3 : P * K * (g * g) = 1).
{ unfold P, K, g. rewrite <- !bpow_plus.
  replace (s + 64 + (E - 1075 + (E - 1075)))%Z with 0%Z by (unfold s; ring).
  reflexivity. }
assert (R4 : Q * K * (g * g * g) = bpow radix2 (E - 1022) ^ 5).
{ unfold Q, K, g. cbn [pow]. rewrite Rmult_1_r, <- !bpow_plus. f_equal. unfold d. ring. }
assert (HM0 : 0 < IZR M) by (apply IZR_lt; lia).
assert (Hu : IZR M * g < bpow radix2 (E - 1022)).
{ replace (E - 1022)%Z with (53 + (E - 1075))%Z by ring. rewrite bpow_plus.
  apply Rmult_lt_compat_r; [exact Hg|]. rewrite <- IZR_pow2_tan by lia.
  apply IZR_lt. lia. }
assert (Ht0 : 0 < IZR M * g) by (apply Rmult_lt_0_compat; assumption).
assert (Ht14 : IZR M * g < bpow radix2 (-14)).
{ eapply Rlt_le_trans; [exact Hu | apply bpow_le; lia]. }
destruct (tan_small_real (IZR M * g) (conj Ht0 Ht14)) as [T1 T2].
assert (H5 : (IZR M * g) ^ 5 <= Q * K * (g * g * g)).
{ rewrite R4. apply pow_incr. lra. }
assert (Pu : 0 < Q * K * (g * g * g)) by (rewrite R4; apply pow_lt, bpow_gt_0).
assert (Hg3 : 0 < g * g * g / 3).
{ apply Rmult_lt_0_compat; [|lra]. apply Rmult_lt_0_compat; [|exact Hg].
  apply Rmult_lt_0_compat; exact Hg. }
(* [j g <= t^3/3]. *)
assert (L : IZR j * g <= (IZR M * g) ^ 3 / 3).
{ apply (Rmult_le_compat_r _ _ _ (Rlt_le _ _ Hg3)) in Z1'.
  replace ((IZR M * g) ^ 3 / 3) with (IZR M * IZR M * IZR M * (g * g * g / 3)) by field.
  replace (IZR j * g) with (IZR j * (P * 3) * K * (g * g * g / 3)); [exact Z1'|].
  transitivity (IZR j * g * (P * K * (g * g))); [field | rewrite R3; ring]. }
(* [t^3/3 + t^5/4 < (j + 1) g]. *)
assert (U : (IZR M * g) ^ 3 / 3 + Q * K * (g * g * g) / 3 < (IZR j + 1) * g).
{ apply (Rmult_lt_compat_r _ _ _ Hg3) in Z2'.
  replace ((IZR M * g) ^ 3 / 3 + Q * K * (g * g * g) / 3)
    with ((IZR M * IZR M * IZR M + Q * K) * (g * g * g / 3)) by field.
  replace ((IZR j + 1) * g) with ((IZR j + 1) * (P * 3) * K * (g * g * g / 3)); [exact Z2'|].
  transitivity ((IZR j + 1) * g * (P * K * (g * g))); [field | rewrite R3; ring]. }
assert (P5 : 0 < (IZR M * g) ^ 5) by (apply pow_lt; exact Ht0).
split; lra.
Qed.

(** Where [tan_small x up] returns [v], [v] is [tan x] rounded in the
    direction [up]. *)
Lemma tan_small_rule :
  forall x (up : bool) v,
  is_finite x = true -> DyadicTrig.tan_small x up = Some v ->
  mpfr_round f64_format (rnd_of up) (tan (B2R x)) (with_val v).
Proof.
intros x up v Fx H.
destruct (small_bits x Fx) as (Hb & Et & Hsh & Hland).
unfold DyadicTrig.tan_small in H. cbv beta zeta in H.
rewrite Hsh, Hland in H.
set (b := to_bits (fabs x)) in *.
set (E := (b / 2 ^ 52)%Z) in *.
set (f := (b mod 2 ^ 52)%Z) in *.
match type of H with (if ?c then _ else _) = _ => destruct c eqn:HE end; [discriminate H|].
assert (HE' : (997 <= E <= 1008)%Z).
{ apply Bool.negb_false_iff, andb_prop in HE as [H1 H2].
  apply Z.leb_le in H1, H2. lia. }
clear HE.
assert (Hf : (0 <= f < 2 ^ 52)%Z) by (apply Z.mod_pos_bound; lia).
assert (Hbd : b = (E * 2 ^ 52 + f)%Z).
{ unfold E, f. rewrite Z.mul_comm. apply Z.div_mod. lia. }
rewrite (lor_implicit f Hf) in H.
set (M := (f + 2 ^ 52)%Z) in *.
destruct (DyadicTrig.cube M) as [h l] eqn:Hc.
destruct (cube_correct M ltac:(unfold M; lia)) as (HN & Hl & Hh).
rewrite Hc in HN, Hl, Hh. cbn [fst snd] in HN, Hl, Hh.
cbv beta iota in H.
rewrite !Z.shiftr_div_pow2 in H by lia.
rewrite !Z.shiftl_1_l in H.
match type of H with (if ?c then _ else _) = _ => destruct c eqn:HT end; [discriminate H|].
apply Bool.orb_false_iff in HT as [HT1 HT2].
apply Bool.negb_false_iff, Z.eqb_eq in HT1.
apply Z.leb_gt in HT2.
injection H as <-.
assert (HN' : (h * 2 ^ 64 + l = M * M * M)%Z) by (rewrite HN; ring).
pose proof (tan_small_bracket E M h l HE' ltac:(unfold M; lia) HN' Hl Hh HT1) as Hbr.
set (j := (h / 2 ^ (2086 - 2 * E) / 3)%Z) in *.
assert (Hj0 : (0 <= j)%Z).
{ unfold j. apply Z.div_pos; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] | lia]. }
(* [b + j] and [b + j + 1] are the patterns of [t + j g] and [t + (j + 1) g]. *)
assert (Mlo : magnitude (b + j)
  = IZR M * bpow radix2 (E - 1075) + IZR j * bpow radix2 (E - 1075)).
{ rewrite Hbd, <- Z.add_assoc, magnitude_normal by lia. unfold M. rewrite !plus_IZR. ring. }
assert (Mhi : magnitude (b + j + 1)
  = IZR M * bpow radix2 (E - 1075) + (IZR j + 1) * bpow radix2 (E - 1075)).
{ rewrite Hbd. replace (E * 2 ^ 52 + f + j + 1)%Z with (E * 2 ^ 52 + (f + j + 1))%Z by ring.
  rewrite magnitude_normal by lia. unfold M. rewrite !plus_IZR. ring. }
assert (Hc0 : (0 <= b + j)%Z) by lia.
assert (Hc1 : (b + j + 1 < 2047 * 2 ^ 52)%Z).
{ rewrite Hbd. change (2 ^ 52)%Z with 4503599627370496%Z in *. lia. }
assert (Ex : Rabs (B2R x) = IZR M * bpow radix2 (E - 1075)).
{ unfold fabs in Et. rewrite B2R_Babs in Et. rewrite Et, Hbd, magnitude_normal by lia.
  reflexivity. }
rewrite <- Mlo, <- Mhi in Hbr.
assert (Fz : is_finite zero = true) by reflexivity.
assert (Hlt : lt x zero = Rlt_bool (B2R x) 0).
{ unfold lt. rewrite Bltb_correct by assumption. reflexivity. }
rewrite Hlt.
destruct (Rlt_bool_spec (B2R x) 0) as [Hn|Hp].
- (* [x < 0]: [tan x = - tan |x|], rounded in the other direction. *)
  rewrite Bool.xorb_true_r.
  assert (Hx : B2R x = - Rabs (B2R x)) by (rewrite Rabs_left by exact Hn; ring).
  rewrite Hx, tan_neg, Ex.
  apply bits_bracket_opp; [exact Hc0 | exact Hc1 | exact Hbr].
- (* [x > 0]: [x = |x|]. *)
  rewrite Bool.xorb_false_r.
  assert (Hx : B2R x = Rabs (B2R x)) by (rewrite Rabs_right by lra; reflexivity).
  rewrite Hx, Ex.
  apply bits_bracket; [exact Hc0 | exact Hc1 | exact Hbr].
Qed.
