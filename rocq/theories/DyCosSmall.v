(** * The rule of [cos] for small arguments before Ziv's strategy

    [cos_small] of [DyadicTrig] in [Model.v], which [cos_dir] tries for
    [|x| >= 2^-26] before [ziv]. For [t = |x|] in [[2^-26, 2^-14)], [t =
    m 2^(be - 1075)] with [m] in [[2^52, 2^53)], and [t^2/2 = (k + r
    2^-s) 2^-53] exactly, for [s = 2098 - 2 be], [k = m^2 / 2^s] and [r =
    m^2 mod 2^s]. [cos t] lies in [(1 - t^2/2, 1 - t^2/2 + t^4/24]]
    ([cos_small_real]). Where [r = 0], [1 - t^2/2] is the [f64] [1 - k
    2^-53], and [t^4/24] is below [2^-53]. Where [r >= 2^(157 - s)], the
    distance from [1 - t^2/2] up to the [f64] [1 - k 2^-53] is at least
    [2^(104 - 2 s)], which is above [t^4/24]. In both cases [cos t] lies
    strictly between the [f64]s [1 - j 2^-53] and [1 - (j - 1) 2^-53], for
    [j = k + (r <> 0)], whose patterns are those of 1 minus [j] and that
    plus 1 ([cos_small_rule]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Encoding Decompose MpfrRound DyExpRules DyTrigTiny
  DyTrigSmall.

Open Scope R_scope.

Local Notation rnd_of up := (if up then RNDU else RNDD).

(** For [0 < a < 2^-14], [1 - a^2/2 < cos a <= 1 - a^2/2 + a^4/24]. *)
Lemma cos_small_real :
  forall a, 0 < a < bpow radix2 (-14) ->
  1 - a ^ 2 / 2 < cos a <= 1 - a ^ 2 / 2 + a ^ 4 / 24.
Proof.
intros a Ha.
assert (Hb : bpow radix2 (-14) = 1 / 16384) by (cbn [bpow radix_val radix2]; lra).
rewrite Hb in Ha. pose proof PI2_1 as HP.
assert (R1 : - PI / 2 <= a) by lra.
assert (R2 : a <= PI / 2) by lra.
destruct (cos_bounds_3 a R1 R2) as [_ H2].
(* Below, the sum of the first four terms of the series ([cos_bound] with
   [n = 1]), which is more than [1 - a^2/2] as [a^6/720 < a^4/24]. *)
destruct (cos_bound a 1 R1 R2) as [H1 _].
replace (cos_approx a (2 * 1 + 1)) with (1 - a ^ 2 / 2 + a ^ 4 / 24 - a ^ 6 / 720) in H1
  by (unfold cos_approx, cos_term; simpl; field).
split; [| exact H2].
assert (P4 : 0 < a ^ 4) by (apply pow_lt; lra).
assert (Aa : a * a < 1) by nra.
replace (a ^ 6) with (a ^ 4 * (a * a)) in H1 by ring.
assert (H6 : a ^ 4 * (a * a) < a ^ 4 * 1) by (apply Rmult_lt_compat_l; lra).
lra.
Qed.

(** [Some] is injective. [cos_small_rule] uses this rather than
    [injection], which did not finish there in ten minutes. *)
Local Lemma some_eq : forall a b : f64, Some a = Some b -> a = b.
Proof. intros a b E. injection E. easy. Qed.

(** Where [cos_small |x| up] returns [v], [v] is [cos x] rounded in the
    direction [up]. *)
Lemma cos_small_rule :
  forall x (up : bool) v,
  is_finite x = true -> DyadicTrig.cos_small (fabs x) up = Some v ->
  mpfr_round f64_format (rnd_of up) (cos (B2R x)) (with_val v).
Proof.
intros x up v Fx H.
destruct (small_bits x Fx) as (Hb & Ev & Esh & Eland).
unfold DyadicTrig.cos_small in H. cbv zeta in H.
rewrite Esh, Eland in H.
set (b := to_bits (fabs x)) in *.
set (E := (b / 2^52)%Z) in *.
set (f := (b mod 2^52)%Z) in *.
assert (Hf : (0 <= f < 2^52)%Z) by (apply Z.mod_pos_bound; reflexivity).
assert (Eb : b = (E * 2^52 + f)%Z).
{ unfold E, f. rewrite Z.mul_comm. apply Z.div_mod. apply Z.pow_nonzero; lia. }
rewrite (lor_implicit f Hf) in H.
destruct ((997 <=? E) && (E <=? 1008))%Z eqn:HE; [| discriminate H].
apply andb_prop in HE. destruct HE as [HE1 HE2].
apply Z.leb_le in HE1. apply Z.leb_le in HE2.
set (m := (f + 2^52)%Z) in *.
set (s := (2098 - 2 * E)%Z) in *.
assert (Hs : (82 <= s <= 104)%Z) by (unfold s; lia).
rewrite (Z.shiftl_1_l s) in H.
replace (2^s - 1)%Z with (Z.ones s) in H by (rewrite Z.ones_equiv; lia).
rewrite Z.land_ones in H by lia.
rewrite (Z.shiftr_div_pow2 _ s) in H by lia.
rewrite (Z.shiftr_div_pow2 _ (157 - s)) in H by lia.
set (sq := (m * m)%Z) in *.
set (P := (2^s)%Z) in *.
set (k := (sq / P)%Z) in *.
set (r := (sq mod P)%Z) in *.
set (Q := (2^(157 - s))%Z) in *.
set (j := (k + Z.b2z (negb (r =? 0)))%Z) in *.
destruct (negb (r =? 0) && (r / Q =? 0))%Z eqn:HT; [discriminate H |].
(* Not [injection] (see [some_eq]). *)
apply some_eq in H. subst v.
(* The integers: [m^2 = k 2^s + r], [1 <= k < 2^24], and [r = 0] or [r >=
   2^(157 - s)], so [j = k + (r <> 0)] is in [[1, 2^24]]. *)
assert (Hm : (4503599627370496 <= m < 9007199254740992)%Z) by (unfold m; simpl Z.pow in Hf; lia).
assert (Hsq : (20282409603651670423947251286016 <= sq < 81129638414606681695789005144064)%Z)
  by (unfold sq; nia).
assert (HP0 : (0 < P)%Z) by (apply Z.pow_pos_nonneg; lia).
assert (HP1 : (4835703278458516698824704 <= P <= 20282409603651670423947251286016)%Z).
{ change 4835703278458516698824704%Z with (2^82)%Z.
  change 20282409603651670423947251286016%Z with (2^104)%Z.
  split; apply Z.pow_le_mono_r; lia. }
assert (Hkr : sq = (P * k + r)%Z) by (apply Z.div_mod; lia).
assert (Hr : (0 <= r < P)%Z) by (apply Z.mod_pos_bound; lia).
assert (Hk : (1 <= k < 16777216)%Z) by nia.
assert (HQ0 : (0 < Q)%Z) by (apply Z.pow_pos_nonneg; lia).
assert (HrQ : r <> 0%Z -> (Q <= r)%Z).
{ intros Hr0. destruct (Z.lt_ge_cases r Q) as [Hl|Hl]; [| exact Hl].
  rewrite (Z.div_small r Q) in HT by lia.
  apply Z.eqb_neq in Hr0. rewrite Hr0 in HT. discriminate HT. }
assert (Hj : (r = 0 /\ j = k \/ r <> 0 /\ j = k + 1)%Z).
{ unfold j. destruct (Z.eqb_spec r 0) as [Hr0|Hr0]; [left | right]; split; auto;
    cbn [negb Z.b2z]; ring. }
assert (Hj1 : (1 <= j <= 16777216)%Z) by lia.
(* The value of [|x|], [t = m 2^(E - 1075)], and [t^2/2 = k 2^-53 + r
   2^(2E - 2151)]. *)
set (g := bpow radix2 (E - 1075)).
assert (Hg : 0 < g) by apply bpow_gt_0.
assert (Hg67 : g <= bpow radix2 (-67)) by (apply bpow_le; lia).
assert (Et : B2R (fabs x) = IZR m * g) by (rewrite Ev, Eb; apply magnitude_normal; lia).
assert (Ec : cos (B2R x) = cos (IZR m * g)).
{ rewrite <- Et. unfold fabs. rewrite B2R_Babs.
  destruct (Rcase_abs (B2R x)) as [Hn|Hn].
  - rewrite (Rabs_left _ Hn), cos_neg. reflexivity.
  - rewrite (Rabs_right _ Hn). reflexivity. }
assert (I1 : IZR P * (g * g) = bpow radix2 (-52)).
{ unfold P, g. rewrite (IZR_Zpower radix2) by lia. rewrite <- !bpow_plus. f_equal.
  unfold s. ring. }
assert (I2 : IZR Q = bpow radix2 209 * (g * g)).
{ unfold Q, g. rewrite (IZR_Zpower radix2) by lia. rewrite <- !bpow_plus. f_equal.
  unfold s. ring. }
assert (C52 : bpow radix2 (-52) = 1 / 4503599627370496) by (cbn [bpow radix_val radix2]; lra).
assert (C53 : bpow radix2 (-53) = 1 / 9007199254740992) by (cbn [bpow radix_val radix2]; lra).
assert (C67 : bpow radix2 (-67) = 1 / 147573952589676412928)
  by (cbn [bpow radix_val radix2]; lra).
assert (C14 : bpow radix2 (-14) = 1 / 16384) by (cbn [bpow radix_val radix2]; lra).
assert (C209 : bpow radix2 209 =
  822752278660603021077484591278675252491367932816789931674304512)
  by (cbn [bpow radix_val radix2]; lra).
assert (Rm : 4503599627370496 <= IZR m < 9007199254740992)
  by (split; [apply IZR_le | apply IZR_lt]; lia).
assert (Rsq : IZR sq = IZR m * IZR m) by (unfold sq; apply mult_IZR).
assert (Rsq1 : IZR sq < 81129638414606681695789005144064) by (apply IZR_lt; lia).
assert (Rsq0 : 0 <= IZR sq) by (apply IZR_le; lia).
assert (Rkr : IZR sq = IZR P * IZR k + IZR r) by (rewrite Hkr, plus_IZR, mult_IZR; reflexivity).
assert (Rr : 0 <= IZR r < IZR P) by (split; [apply IZR_le | apply IZR_lt]; lia).
set (t := IZR m * g) in *.
assert (Ht : 0 < t < bpow radix2 (-14)).
{ unfold t. split; [apply Rmult_lt_0_compat; lra |].
  apply Rlt_le_trans with (9007199254740992 * g); [apply Rmult_lt_compat_r; lra |].
  rewrite C14. rewrite C67 in Hg67. lra. }
assert (HA : t ^ 2 / 2 = IZR k * bpow radix2 (-53) + IZR r * (g * g) / 2).
{ replace (t ^ 2 / 2) with (IZR sq * (g * g) / 2) by (rewrite Rsq; unfold t; field).
  rewrite Rkr.
  replace ((IZR P * IZR k + IZR r) * (g * g) / 2)
    with (IZR k * (IZR P * (g * g)) / 2 + IZR r * (g * g) / 2) by field.
  rewrite I1, C52, C53. field. }
assert (Hgg : 0 < g * g) by (apply Rmult_lt_0_compat; lra).
(* [r 2^(2E - 2151) < 2^-53], as [r < 2^s]. *)
assert (HR : IZR r * (g * g) / 2 < bpow radix2 (-53)).
{ assert (IZR r * (g * g) < IZR P * (g * g)) by (apply Rmult_lt_compat_r; lra).
  rewrite C53. rewrite I1, C52 in *. lra. }
assert (HR0 : 0 <= IZR r * (g * g)) by (apply Rmult_le_pos; lra).
(* [t^4/24 < 2^-56/24 < 2^-53]. *)
assert (HD : t ^ 4 / 24 < bpow radix2 (-53)).
{ rewrite C14 in Ht. rewrite C53.
  assert (H2 : t * t < 1 / 16384 * (1 / 16384)) by (apply Rmult_le_0_lt_compat; lra).
  assert (H4 : t * t * (t * t) < 1 / 16384 * (1 / 16384) * (1 / 16384 * (1 / 16384)))
    by (apply Rmult_le_0_lt_compat; nra).
  replace (t ^ 4) with (t * t * (t * t)) by ring. lra. }
(* If [r <> 0], [t^4/24 < 2^212 2^(4E - 4300)/24], which is less than
   [2^(157 - s) 2^(2E - 2151) = 2^209 2^(4E - 4300)/2], at most [r
   2^(2E - 2151)]. *)
assert (HDR : r <> 0%Z -> t ^ 4 / 24 < IZR r * (g * g) / 2).
{ intros Hr0. specialize (HrQ Hr0).
  assert (RQ : IZR Q <= IZR r) by (apply IZR_le; exact HrQ).
  rewrite I2, C209 in RQ.
  replace (t ^ 4) with (IZR sq * IZR sq * ((g * g) * (g * g))) by (rewrite Rsq; unfold t; ring).
  assert (H1 : IZR sq * IZR sq <
    81129638414606681695789005144064 * 81129638414606681695789005144064)
    by (apply Rmult_le_0_lt_compat; lra).
  assert (H2 : IZR sq * IZR sq * ((g * g) * (g * g)) <
    81129638414606681695789005144064 * 81129638414606681695789005144064 *
      ((g * g) * (g * g)))
    by (apply Rmult_lt_compat_r; [apply Rmult_lt_0_compat |]; lra).
  assert (H3 : 822752278660603021077484591278675252491367932816789931674304512 * (g * g) * (g * g)
    <= IZR r * (g * g)) by (apply Rmult_le_compat_r; lra).
  assert (H4 : 0 < (g * g) * (g * g)) by (apply Rmult_lt_0_compat; lra).
  lra. }
destruct (cos_small_real t Ht) as [L U].
rewrite Ec.
assert (Hc : (0x3ff0000000000000 - j = 1022 * 2^52 + (2^52 - j))%Z) by (simpl Z.pow; lia).
apply bits_bracket.
- lia.
- simpl Z.pow. lia.
- rewrite Hc, (magnitude_normal 1022 (2^52 - j)) by (simpl Z.pow; lia).
  replace (1022 * 2^52 + (2^52 - j) + 1)%Z with (1022 * 2^52 + (2^52 - j + 1))%Z by ring.
  rewrite (magnitude_normal 1022 (2^52 - j + 1)) by (simpl Z.pow; lia).
  change (1022 - 1075)%Z with (-53)%Z.
  rewrite !plus_IZR, !minus_IZR. change (IZR (2^52)) with 4503599627370496.
  rewrite C53 in *.
  destruct Hj as [[Hr0 Ej] | [Hr0 Ej]]; rewrite Ej; [| rewrite plus_IZR].
  + (* [r = 0]: [cos t] is in [(1 - k 2^-53, 1 - k 2^-53 + t^4/24]]. *)
    assert (IZR r = 0) by (rewrite Hr0; reflexivity).
    split; nra.
  + (* [r <> 0]: [1 - (k + 1) 2^-53 < 1 - t^2/2 < cos t <= 1 - t^2/2 +
       t^4/24 < 1 - k 2^-53]. *)
    specialize (HDR Hr0). split; lra.
Qed.
