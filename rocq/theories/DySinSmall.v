(** * The rule of [sin] for small arguments before Ziv's strategy

    [sin_small] of [DyadicTrig] in [Model.v], which [sin_dir] tries for
    [|x| >= 2^-26] before [ziv]. For [t = |x|] in [[2^-26, 2^-13)], [t =
    m g] with [g = 2^(be - 1075)] the ulp of [t] and [m] in [[2^52,
    2^53)], [t^3/6 = c g] with [c = m^3 / (6 2^(s + 64))], for [s = 2086
    - 2 be]. [sin t] lies in [(t - c g, t - (c - w) g]] with [w = t^5 /
    (120 g)] ([sin_small_real]). [j], the greatest integer below [c], is
    computed from the floor of [(m^3 - 1) / 2^64]; where it is also the
    floor of [c - b], for a bound [b] above [w], and the stored
    significand [f] of [t] is above [j] ([sin_small_int] for the
    integers), [sin t] lies strictly between the [f64]s [t - (j + 1) g]
    and [t - j g], whose patterns are those of [t] minus [j + 1] and that
    plus 1. [sin] is odd, so for [x < 0] the rule rounds [sin t] in the
    other direction and negates it ([sin_small_rule]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Encoding Decompose MpfrRound DyExpRules DyTrigTiny
  DyTrigSmall.

Open Scope R_scope.

Local Notation rnd_of up := (if up then RNDU else RNDD).

(** For [0 < a < 2^-13], [a - a^3/6 < sin a <= a - a^3/6 + a^5/120]. The
    upper bound is [sin_bounds_3]. The lower one is strict, as the sum of
    the first four terms of the series ([sin_bound] with [n = 1]) is above
    the sum of the first two: [a^7/5040 < a^5/120] for [a^2 < 42]. *)
Lemma sin_small_real :
  forall a, 0 < a < bpow radix2 (-13) ->
  a - a ^ 3 / 6 < sin a <= a - a ^ 3 / 6 + a ^ 5 / 120.
Proof.
intros a Ha.
assert (Hb : bpow radix2 (-13) = 1 / 8192) by (cbn [bpow radix_val radix2]; lra).
rewrite Hb in Ha. pose proof PI2_1 as HP.
assert (H0 : 0 <= a) by lra.
assert (Hp : a <= PI) by lra.
destruct (sin_bounds_3 a H0 Hp) as [_ H2].
destruct (sin_bound a 1 H0 Hp) as [H1 _].
replace (sin_approx a (2 * 1 + 1)) with (a - a ^ 3 / 6 + a ^ 5 / 120 - a ^ 7 / 5040) in H1
  by (unfold sin_approx, sin_term; simpl; field).
assert (P5 : 0 < a ^ 5) by (apply pow_lt; lra).
assert (H7 : a ^ 7 < a ^ 5 * 42).
{ replace (a ^ 7) with (a ^ 5 * (a * a)) by ring. apply Rmult_lt_compat_l; nra. }
split; lra.
Qed.

(** [IZR (2^e)] is [bpow radix2 e], as in [FormatHex.v]. *)
Local Lemma IZR_pow2 : forall e, (0 <= e)%Z -> IZR (2 ^ e) = bpow radix2 e.
Proof. intros e He. exact (IZR_Zpower radix2 e He). Qed.

(** The integer part of [sin_small_rule]. With [N = m^3 = h 2^64 + l],
    [z = 1] exactly when [l = 0], [q = 2^s] and [D = 6 q 2^64], the floor
    [j] of [(h - z) / (6 q)] is that of [(N - 1) / D], so [N <= (j + 1) D].
    That [j] is also the floor of [(h - p) / (6 q)] gives [j D + p 2^64 <=
    N]. [N >= 2^156] makes [h >= 1], so [j] is not negative. *)
Lemma sin_small_int :
  forall m h l z q p j : Z,
  (0 < q)%Z -> (0 <= l < 2^64)%Z -> (h * 2^64 + l = m * m * m)%Z -> (2^156 <= m * m * m)%Z ->
  (z = 1 /\ l = 0 \/ z = 0 /\ l <> 0)%Z ->
  (j = (h - z) / (q * 6))%Z -> ((h - p) / (q * 6) = j)%Z ->
  (0 <= j /\ m * m * m <= (j + 1) * 6 * (q * 2^64) /\
   j * 6 * (q * 2^64) + p * 2^64 <= m * m * m)%Z.
Proof.
intros m h l z q p j Hq Hl HN H3 Hz Ej Ep.
assert (Q6 : (0 < q * 6)%Z) by lia.
pose proof (Z.mul_div_le (h - p) (q * 6) Q6) as A3. rewrite Ep in A3.
pose proof (Z.mul_succ_div_gt (h - z) (q * 6) Q6) as A2. rewrite <- Ej in A2.
assert (Hh : (1 <= h)%Z) by lia.
assert (Hj : (0 <= j)%Z) by (rewrite Ej; apply Z.div_pos; lia).
split; [exact Hj|]. split; lia.
Qed.

(** Where [sin_small x up] returns [v], [v] is [sin x] rounded in the
    direction [up]. With [t = |x| = m g], [g = 2^(be - 1075)] and the
    bounds of [sin_small_int], [t^3/6 <= (j + 1) g] and [j g < t^3/6 -
    t^5/120], as [t^5/120 < 2^265 g^5/120] is below the margin [p 2^64
    g^3/6 = 2^265 g^5/96]. So [sin_small_real] puts [sin t] strictly
    between [t - (j + 1) g] and [t - j g], the values of the patterns [b -
    (j + 1)] and [b - j] ([bits_bracket]), and [sin x = - sin t] for [x <
    0] ([bits_bracket_opp]). *)
Lemma sin_small_rule :
  forall x (up : bool) v,
  is_finite x = true -> DyadicTrig.sin_small x up = Some v ->
  mpfr_round f64_format (rnd_of up) (sin (B2R x)) (with_val v).
Proof.
intros x up v Fx.
destruct (small_bits x Fx) as (Hb & Et & Es & El).
unfold DyadicTrig.sin_small. cbv zeta.
set (b := to_bits (fabs x)) in *.
rewrite Es, El. clear Es El.
set (E := (b / 2^52)%Z) in *.
set (f := (b mod 2^52)%Z) in *.
destruct ((997 <=? E) && (E <=? 1009))%Z eqn:HE; cbn [negb];
  [|intros H; discriminate H].
apply Bool.andb_true_iff in HE. destruct HE as [HE1 HE2]. apply Z.leb_le in HE1, HE2.
assert (Hf : (0 <= f < 2^52)%Z) by (apply Z.mod_pos_bound; lia).
assert (Hbd : b = (E * 2^52 + f)%Z) by (pose proof (Z.div_mod b (2^52)); unfold E, f; lia).
rewrite (lor_implicit f Hf).
set (m := (f + 2^52)%Z) in *.
assert (Hm : (2^52 <= m < 2^53)%Z) by (unfold m; lia).
pose proof (cube_correct m ltac:(lia)) as HC.
destruct (DyadicTrig.cube m) as [h l] eqn:C. cbn [fst snd] in HC. destruct HC as (HN & Hl & Hh).
replace (m ^ 3)%Z with (m * m * m)%Z in HN by ring.
cbn beta iota.
set (s := (2086 - 2 * E)%Z).
set (d := (2 * E - 1953)%Z).
assert (Hs : (68 <= s <= 92)%Z) by (unfold s; lia).
assert (Hd : (41 <= d <= 65)%Z) by (unfold d; lia).
assert (Hq : (0 < 2 ^ s)%Z) by (apply Z.pow_pos_nonneg; lia).
set (z := Z.b2z (l =? 0)).
assert (Hz : (z = 1 /\ l = 0 \/ z = 0 /\ l <> 0)%Z)
  by (unfold z; destruct (Z.eqb_spec l 0); [left | right]; cbn; lia).
set (j := (Z.shiftr (h - z) s / 6)%Z).
assert (Ej : j = ((h - z) / (2 ^ s * 6))%Z)
  by (unfold j; rewrite Z.shiftr_div_pow2, Z.div_div by lia; reflexivity).
destruct (Z.shiftr (h - Z.shiftl 1 d) s / 6 =? j)%Z eqn:T1;
  destruct (f <=? j)%Z eqn:T2; cbn [negb orb]; try (intros H; discriminate H).
intros H. injection H as <-.
apply Z.eqb_eq in T1. apply Z.leb_gt in T2.
rewrite Z.shiftl_1_l, Z.shiftr_div_pow2, Z.div_div in T1 by lia.
assert (Hm3 : (2^156 <= m * m * m)%Z).
{ replace (m * m * m)%Z with (m ^ 3)%Z by ring. change (2^156)%Z with ((2^52)^3)%Z.
  apply Z.pow_le_mono_l. lia. }
destruct (sin_small_int m h l z (2 ^ s) (2 ^ d) j Hq Hl HN Hm3 Hz Ej T1) as (Hj0 & I1 & I2).
(* The values of the two patterns. *)
set (g := bpow radix2 (E - 1075)).
assert (Hg : 0 < g) by apply bpow_gt_0.
assert (Hc0 : magnitude (b - (j + 1)) = (IZR m - IZR j - 1) * g).
{ replace (b - (j + 1))%Z with (E * 2^52 + (f - j - 1))%Z by lia.
  rewrite magnitude_normal by lia.
  replace (f - j - 1 + 2^52)%Z with (m - j - 1)%Z by (unfold m; lia).
  rewrite !minus_IZR. reflexivity. }
assert (Hc1 : magnitude (b - (j + 1) + 1) = (IZR m - IZR j) * g).
{ replace (b - (j + 1) + 1)%Z with (E * 2^52 + (f - j))%Z by lia.
  rewrite magnitude_normal by lia.
  replace (f - j + 2^52)%Z with (m - j)%Z by (unfold m; lia).
  rewrite minus_IZR. reflexivity. }
(* [t = |x|]. *)
assert (Ht : B2R (fabs x) = IZR m * g).
{ rewrite Et, Hbd. rewrite magnitude_normal by lia. reflexivity. }
assert (Ht0 : 0 < IZR m * g) by (apply Rmult_lt_0_compat; [apply IZR_lt; lia | exact Hg]).
assert (Ht13 : IZR m * g < bpow radix2 (-13)).
{ assert (Hg66 : g <= bpow radix2 (-66)) by (apply bpow_le; lia).
  assert (HM53 : IZR m < bpow radix2 53) by (rewrite <- IZR_pow2 by lia; apply IZR_lt; lia).
  replace (bpow radix2 (-13)) with (bpow radix2 53 * bpow radix2 (-66))
    by (rewrite <- bpow_plus; reflexivity).
  apply Rle_lt_trans with (IZR m * bpow radix2 (-66)).
  - apply Rmult_le_compat_l; [apply IZR_le; lia | exact Hg66].
  - apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact HM53]. }
destruct (sin_small_real (IZR m * g) (conj Ht0 Ht13)) as [S1 S2].
(* The integer bounds in reals: [2^s 2^64 g^2 = 1] and [2^d 2^64 g^2 = 2^261 g^4]. *)
apply IZR_le in I1, I2.
rewrite !mult_IZR, plus_IZR, !IZR_pow2 in I1 by lia.
rewrite plus_IZR, !mult_IZR, !IZR_pow2 in I2 by lia.
assert (R1 : bpow radix2 s * bpow radix2 64 * (g * g) = 1).
{ unfold g. rewrite <- !bpow_plus. change 1 with (bpow radix2 0). f_equal. unfold s. lia. }
assert (R2 : bpow radix2 d * bpow radix2 64 * (g * g) * g * 16 = bpow radix2 265 * (g * g * g * g * g)).
{ replace 16 with (bpow radix2 4) by reflexivity.
  unfold g. rewrite <- !bpow_plus. f_equal. unfold d. lia. }
assert (M5 : IZR m * IZR m * IZR m * IZR m * IZR m < bpow radix2 265).
{ rewrite <- IZR_pow2 by lia. rewrite <- !mult_IZR. apply IZR_lt.
  replace (m * m * m * m * m)%Z with (m ^ 5)%Z by ring. change (2^265)%Z with ((2^53)^5)%Z.
  apply Z.pow_lt_mono_l; lia. }
assert (G3 : 0 < g * g * g) by ((repeat apply Rmult_lt_0_compat); exact Hg).
assert (G5 : 0 < g * g * g * g * g) by ((repeat apply Rmult_lt_0_compat); exact Hg).
assert (K5 : 0 < bpow radix2 265 * (g * g * g * g * g))
  by (apply Rmult_lt_0_compat; [apply bpow_gt_0 | exact G5]).
assert (L1 : (IZR m * g) ^ 3 / 6 <= (IZR j + 1) * g).
{ pose proof (Rmult_le_compat_r (g * g * g) _ _ (Rlt_le _ _ G3) I1) as X.
  assert (Y : (IZR j + 1) * 6 * (bpow radix2 s * bpow radix2 64) * (g * g * g) =
              (IZR j + 1) * 6 * g * (bpow radix2 s * bpow radix2 64 * (g * g))) by ring.
  rewrite R1 in Y. lra. }
assert (L2 : IZR j * g < (IZR m * g) ^ 3 / 6 - (IZR m * g) ^ 5 / 120).
{ pose proof (Rmult_le_compat_r (g * g * g) _ _ (Rlt_le _ _ G3) I2) as X.
  assert (Y : (IZR j * 6 * (bpow radix2 s * bpow radix2 64) + bpow radix2 d * bpow radix2 64) *
              (g * g * g) =
              IZR j * 6 * g * (bpow radix2 s * bpow radix2 64 * (g * g)) +
              bpow radix2 d * bpow radix2 64 * (g * g) * g) by ring.
  rewrite R1 in Y.
  pose proof (Rmult_lt_compat_r (g * g * g * g * g) _ _ G5 M5) as X5.
  lra. }
assert (Hj1 : (b - (j + 1) + 1 < 2047 * 2^52)%Z) by lia.
(* The sign of [x]. *)
unfold lt. rewrite Bltb_correct by first [exact Fx | reflexivity].
change (B2R zero) with 0.
assert (Ea : Rabs (B2R x) = IZR m * g) by (rewrite <- Ht; symmetry; apply B2R_Babs).
destruct (Rlt_bool_spec (B2R x) 0) as [Hn | Hp].
- (* [x = -t]: [sin x = - sin t], rounded in the other direction. *)
  rewrite Rabs_left in Ea by exact Hn.
  replace (B2R x) with (- (IZR m * g)) by lra.
  rewrite sin_neg, Bool.xorb_true_r.
  apply bits_bracket_opp; [lia | exact Hj1 |]. rewrite Hc0, Hc1. split; lra.
- (* [x = t]. *)
  rewrite Rabs_pos_eq in Ea by exact Hp. rewrite Ea, Bool.xorb_false_r.
  apply bits_bracket; [lia | exact Hj1 |]. rewrite Hc0, Hc1. split; lra.
Qed.
