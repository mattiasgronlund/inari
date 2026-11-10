(** * The last steps of the fast paths of the logarithms

    [DyadicLog.normalize] of [Model.v] scales [h + l] by the exponent [k]
    of [h] to [1 <= |h| < 2] ([normalize_correct] shows [1/2 < |h| < 2]), so that the rounding
    tests of [FastSign.v] apply. [ln_f64_ne1] bounds [|ln x|] from below
    for an [f64] [x <> 1], so that [h] is not too small, and [fts_exact]
    is Fast2Sum [Dekker] for the sums of [FastLogLn.v] and
    [FastLogBy.v], which reach [|e| ln 2] with [|e| <= 1074].

    [Dekker] T. J. Dekker, A floating-point technique for extending the
    available precision, Numer. Math. 18 (1971). *)

From Stdlib Require Import ZArith Reals Lra Lia Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Mult_error.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct CancelLanes FastRound.
From Inari Require MulRuTiny FastExpErr.

Open Scope R_scope.

Local Notation G := (generic_format radix2 fexp64).
Local Notation succ64 := (succ radix2 fexp64).
Local Notation pred64 := (pred radix2 fexp64).

(** ** Fast2Sum *)

Local Lemma max_ge : 2048 <= MAX.
Proof.
assert (H1 : bpow radix2 971 <= bpow radix2 1023) by (apply bpow_le; lia).
assert (H2 : bpow radix2 11 <= bpow radix2 1023) by (apply bpow_le; lia).
assert (H3 : bpow radix2 1024 = 2 * bpow radix2 1023).
{ replace 1024%Z with (1 + 1023)%Z by lia. rewrite bpow_plus. reflexivity. }
assert (H4 : bpow radix2 11 = 2048) by reflexivity.
lra.
Qed.

(** [Fast.fast_two_sum a b] is exact when [|b| <= |a|]
    ([CancelLanes.fast_two_sum]) or [a = 0], where it returns [(b, 0)],
    as [FastLogCore.lc_fts] but for [|a + b| <= 2048]. *)
Lemma fts_exact :
  forall a b s t, is_finite a = true -> is_finite b = true ->
  (Rabs (B2R b) <= Rabs (B2R a) \/ B2R a = 0) -> Rabs (B2R a + B2R b) <= 2048 ->
  Fast.fast_two_sum a b = (s, t) ->
  is_finite s = true /\ is_finite t = true /\ B2R s = RN (B2R a + B2R b) /\
  B2R s + B2R t = B2R a + B2R b.
Proof.
intros a b s t Fa Fb Hab Hab2 E.
pose proof max_ge as HM.
unfold Fast.fast_two_sum in E. injection E as <- <-.
destruct (add_below_max a b Fa Fb ltac:(lra)) as (Fs & Es & _).
destruct Hab as [Hab | Ha0].
- destruct (fast_two_sum a b (add a b) Fa Fb Hab Fs Es) as [Ft Et].
  do 3 (split; [assumption|]). rewrite Et. ring.
- assert (Es' : B2R (add a b) = B2R b).
  { rewrite Es, Ha0, Rplus_0_l. apply round_generic; [typeclasses eauto|].
    apply generic_format_B2R. }
  assert (Hd : Rabs (B2R a - B2R (add a b)) <= MAX).
  { rewrite Es', Ha0, Rminus_0_l, Rabs_Ropp. rewrite Ha0, Rplus_0_l in Hab2. lra. }
  destruct (sub_below_max a (add a b) Fa Fs Hd) as (Fd & Ed & _).
  assert (Ed' : B2R (sub a (add a b)) = - B2R b).
  { rewrite Ed, Es', Ha0, Rminus_0_l. apply round_generic; [typeclasses eauto|].
    apply generic_format_opp, generic_format_B2R. }
  assert (Ht : Rabs (B2R b + B2R (sub a (add a b))) <= MAX)
    by (rewrite Ed', Rplus_opp_r, Rabs_R0; lra).
  destruct (add_below_max b (sub a (add a b)) Fb Fd Ht) as (Ft & Et & _).
  rewrite Ed', Rplus_opp_r, round_0 in Et by typeclasses eauto.
  do 3 (split; [assumption|]). rewrite Es', Et, Ha0. ring.
Qed.

(** ** The normalisation *)

(** Rounding to nearest commutes with scaling by [2^e] while neither [x]
    nor [x 2^e] is below [2^-1022] in magnitude: both then round at 53
    bits, and the scaled mantissa is the same. *)
Local Lemma rn_scale :
  forall x e, bpow radix2 (-1022) <= Rabs x -> bpow radix2 (-1022) <= Rabs (x * bpow radix2 e) ->
  RN (x * bpow radix2 e) = RN x * bpow radix2 e.
Proof.
intros x e Hx Hxe.
assert (Hx0 : x <> 0).
{ intros ->. rewrite Rabs_R0 in Hx. pose proof (bpow_gt_0 radix2 (-1022)). lra. }
assert (M1 : (-1021 <= mag radix2 x)%Z) by (apply mag_ge_bpow; exact Hx).
assert (M2 : (-1021 <= mag radix2 (x * bpow radix2 e))%Z) by (apply mag_ge_bpow; exact Hxe).
rewrite (mag_mult_bpow radix2 x e Hx0) in M2.
unfold round, scaled_mantissa, cexp, F2R. cbn [Fnum Fexp].
rewrite (mag_mult_bpow radix2 x e Hx0).
assert (E : FLT_exp (-1074) 53 (mag radix2 x + e) = (FLT_exp (-1074) 53 (mag radix2 x) + e)%Z)
  by (unfold FLT_exp; lia).
rewrite E.
set (f := FLT_exp (-1074) 53 (mag radix2 x)).
replace (x * bpow radix2 e * bpow radix2 (- (f + e))) with (x * bpow radix2 (- f)).
2: { rewrite Rmult_assoc, <- bpow_plus. f_equal. f_equal. lia. }
rewrite bpow_plus. ring.
Qed.

(** A real within [2^-55] of a float [a] in [[1, 2)] rounds to [a]: the
    neighbours of [a] are at least [2^-53] away. *)
Local Lemma rn_keep :
  forall a r, G a -> 1 <= a < 2 -> Rabs r <= bpow radix2 (-55) -> RN (a + r) = a.
Proof.
intros a r Fa Ha Hr.
assert (E2 : bpow radix2 (-53) = 4 * bpow radix2 (-55)).
{ replace (-53)%Z with (2 + -55)%Z by lia. rewrite bpow_plus. reflexivity. }
assert (E3 : bpow radix2 (-52) = 8 * bpow radix2 (-55)).
{ replace (-52)%Z with (3 + -55)%Z by lia. rewrite bpow_plus. reflexivity. }
pose proof (bpow_gt_0 radix2 (-55)).
assert (Hp : pred64 a <= a - bpow radix2 (-53)).
{ destruct (Rle_lt_or_eq_dec 1 a (proj1 Ha)) as [H1|H1].
  - rewrite pred_hi by (assumption || lra). lra.
  - subst a. rewrite pred_lo by (assumption || lra). lra. }
assert (Hs : succ64 a = a + bpow radix2 (-52)) by (apply succ_hi; lra).
apply rn_between; [exact Fa | lra |].
apply Rabs_le_inv in Hr. lra.
Qed.

(** A float below 2 in magnitude is at most [2 - 2^-52] in magnitude. *)
Local Lemma abs_le_pred2 :
  forall a, G a -> Rabs a < 2 -> Rabs a <= 2 - bpow radix2 (-52).
Proof.
intros a Fa Ha.
assert (H : Rabs a <= pred64 (bpow radix2 1)).
{ apply (pred_ge_gt radix2 fexp64); [apply generic_format_abs; exact Fa | exact format_two | exact Ha]. }
rewrite pred_bpow in H. exact H.
Qed.

Theorem normalize_correct :
  forall h l h' l' k y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  bpow radix2 (-1021) <= Rabs (B2R h) <= 2048 ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (-69) * Rabs (B2R h) ->
  DyadicLog.normalize h l = Some (h', l', k) ->
  is_finite h' = true /\ is_finite l' = true /\ B2R h' = RN (B2R h' + B2R l') /\
  / 2 < Rabs (B2R h') < 2 /\ (-1021 <= k <= 1022)%Z /\
  Rabs (y * bpow radix2 (- k) - (B2R h' + B2R l')) <= bpow radix2 (-68).
Proof.
intros h l h' l' k y Fh Fl Hrn Hh Hy E.
pose proof max_ge as HM.
unfold DyadicLog.normalize in E.
destruct (eq h zero); [discriminate|].
cbv zeta in E.
change (Z.land (Z.shiftr (to_bits h) 52) 2047 - 1023)%Z with (Generic.exponent h) in E.
(* The exponent [ek] of the normal [h]: [2^ek <= |h| < 2^(ek + 1)]. *)
assert (Hk1 : (-1021 <= Generic.exponent h)%Z) by (apply MulRuTiny.exponent_ge; [exact Fh | lra]).
assert (Hk2 : (Generic.exponent h < 12)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fh | lia |].
  change (bpow radix2 12) with 4096. lra. }
assert (Hlo : bpow radix2 (Generic.exponent h) <= Rabs (B2R h))
  by (apply bpow_exponent_le_abs_B2R; [exact Fh | lia]).
assert (Hhi : Rabs (B2R h) < bpow radix2 (Generic.exponent h + 1))
  by (apply abs_B2R_lt_exponent; exact Fh).
set (ek := Generic.exponent h) in *.
(* [s] is [2^-ek]. *)
replace (1023 - ek)%Z with (- ek + 1023)%Z in E by ring.
destruct (pow2_bits (- ek) ltac:(lia)) as (Fs & Rs).
set (s := from_bits _) in E, Fs, Rs.
injection E as Eh El Ek. subst h' l' k.
set (B := bpow radix2 (- ek)) in Rs |- *.
assert (HB0 : 0 < B) by apply bpow_gt_0.
assert (HB1 : bpow radix2 ek * B = 1).
{ unfold B. rewrite <- bpow_plus, Z.add_opp_diag_r. reflexivity. }
assert (HB2 : bpow radix2 (ek + 1) * B = 2).
{ unfold B. rewrite <- bpow_plus. replace (ek + 1 + - ek)%Z with 1%Z by ring. reflexivity. }
assert (Hh1 : 1 <= Rabs (B2R h) * B).
{ rewrite <- HB1. apply Rmult_le_compat_r; lra. }
assert (Hh2 : Rabs (B2R h) * B < 2).
{ rewrite <- HB2. apply Rmult_lt_compat_r; lra. }
(* [|l| <= |h| / 2], from the relative error of [h = RN(h + l)]. *)
assert (Hl : Rabs (B2R l) <= Rabs (B2R h) / 2).
{ pose proof (FastExpErr.rn_err (B2R h + B2R l)) as Re.
  rewrite <- Hrn in Re.
  replace (B2R h - (B2R h + B2R l)) with (- B2R l) in Re by ring.
  rewrite Rabs_Ropp in Re.
  pose proof (Rabs_triang (B2R h) (B2R l)) as T.
  assert (Hu : bpow radix2 (-53) <= / 8).
  { apply Rle_trans with (bpow radix2 (-3)); [apply bpow_le; lia|].
    change (bpow radix2 (-3)) with (/ 8). lra. }
  assert (P : bpow radix2 (-53) * Rabs (B2R h + B2R l) <= / 8 * Rabs (B2R h + B2R l))
    by (apply Rmult_le_compat_r; [apply Rabs_pos | exact Hu]).
  assert (Hm : bpow radix2 (-1075) <= bpow radix2 (-1021) / 8).
  { replace (-1021)%Z with (3 + -1024)%Z by lia. rewrite bpow_plus.
    change (bpow radix2 3) with 8.
    assert (bpow radix2 (-1075) <= bpow radix2 (-1024)) by (apply bpow_le; lia). lra. }
  pose proof (Rabs_pos (B2R h)). lra. }
(* [h' = h 2^-ek] exactly. *)
assert (Gh : G (B2R h * B)).
{ unfold B. apply mult_bpow_exact_FLT; [apply generic_format_B2R|].
  assert (Hm : (ek + 1 <= mag radix2 (B2R h))%Z)
    by (apply mag_ge_bpow; replace (ek + 1 - 1)%Z with ek by ring; exact Hlo).
  lia. }
assert (Hmh : Rabs (B2R h * B2R s) <= MAX).
{ rewrite Rs, Rabs_mult, (Rabs_pos_eq B) by lra. lra. }
destruct (mul_below_max h s Fh Fs Hmh) as (Fh' & Rh' & _).
rewrite Rs, (round_generic _ _ _ _ Gh) in Rh'.
assert (Habs : Rabs (B2R (mul h s)) = Rabs (B2R h) * B)
  by (rewrite Rh', Rabs_mult, (Rabs_pos_eq B) by lra; reflexivity).
assert (Hp2 : Rabs (B2R (mul h s)) <= 2 - bpow radix2 (-52))
  by (apply abs_le_pred2; [apply generic_format_B2R | lra]).
assert (Hml : Rabs (B2R l * B2R s) <= MAX).
{ rewrite Rs, Rabs_mult, (Rabs_pos_eq B) by lra.
  assert (Rabs (B2R l) * B <= Rabs (B2R h) / 2 * B) by (apply Rmult_le_compat_r; lra). lra. }
destruct (mul_below_max l s Fl Fs Hml) as (Fl' & Rl' & _).
rewrite Rs in Rl'.
(* The error before [l 2^-ek] is rounded, and the slack for that rounding:
   [2^-69 |h'| + 2^-1075 <= 2^-68] as [|h'| <= 2 - 2^-52]. *)
assert (Hy' : Rabs (y * B - (B2R h + B2R l) * B) <= bpow radix2 (-69) * Rabs (B2R (mul h s))).
{ replace (y * B - (B2R h + B2R l) * B) with ((y - (B2R h + B2R l)) * B) by ring.
  rewrite Rabs_mult, (Rabs_pos_eq B), Habs by lra.
  replace (bpow radix2 (-69) * (Rabs (B2R h) * B)) with (bpow radix2 (-69) * Rabs (B2R h) * B)
    by ring.
  apply Rmult_le_compat_r; lra. }
assert (Hfin : bpow radix2 (-69) * Rabs (B2R (mul h s)) + bpow radix2 (-1075) <= bpow radix2 (-68)).
{ assert (E68 : bpow radix2 (-68) = 2 * bpow radix2 (-69)).
  { replace (-68)%Z with (1 + -69)%Z by lia. rewrite bpow_plus. reflexivity. }
  assert (E121 : bpow radix2 (-1075) <= bpow radix2 (-69) * bpow radix2 (-52)).
  { rewrite <- bpow_plus. apply bpow_le. lia. }
  assert (P : bpow radix2 (-69) * Rabs (B2R (mul h s)) <= bpow radix2 (-69) * (2 - bpow radix2 (-52)))
    by (apply Rmult_le_compat_l; [apply bpow_ge_0 | exact Hp2]).
  lra. }
pose proof (bpow_gt_0 radix2 (-1075)) as H1075.
do 2 (split; [assumption|]).
destruct (Rle_or_lt (bpow radix2 (-1022)) (Rabs (B2R l * B))) as [HL|HL].
- (* [l 2^-ek] is a float: [h' + l'] is [(h + l) 2^-ek], and [RN]
     commutes with the scaling. *)
  assert (Gl : G (B2R l * B)).
  { assert (Hl0 : B2R l <> 0).
    { intros H0. rewrite H0, Rmult_0_l, Rabs_R0 in HL. pose proof (bpow_gt_0 radix2 (-1022)). lra. }
    unfold B. apply mult_bpow_exact_FLT; [apply generic_format_B2R|].
    assert (Hm : (-1021 <= mag radix2 (B2R l * B))%Z) by (apply mag_ge_bpow; exact HL).
    unfold B in Hm. rewrite (mag_mult_bpow radix2 _ _ Hl0) in Hm. lia. }
  rewrite (round_generic _ _ _ _ Gl) in Rl'.
  split; [|split; [lra | split; [lia|]]].
  + rewrite Rl', Rh'. replace (B2R h * B + B2R l * B) with ((B2R h + B2R l) * B) by ring.
    assert (Hhl : Rabs (B2R h) / 2 <= Rabs (B2R h + B2R l)).
    { pose proof (Rabs_triang_inv (B2R h) (- B2R l)) as T. rewrite Rabs_Ropp in T.
      replace (B2R h - - B2R l) with (B2R h + B2R l) in T by ring. lra. }
    assert (E1021 : bpow radix2 (-1021) = 2 * bpow radix2 (-1022)).
    { replace (-1021)%Z with (1 + -1022)%Z by lia. rewrite bpow_plus. reflexivity. }
    assert (Hhalf : bpow radix2 (-1022) <= / 2).
    { apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia|].
      change (bpow radix2 (-1)) with (/ 2). lra. }
    assert (Hsc : Rabs (B2R h) / 2 * B <= Rabs (B2R h + B2R l) * B)
      by (apply Rmult_le_compat_r; lra).
    unfold B. rewrite rn_scale.
    * rewrite <- Hrn. reflexivity.
    * lra.
    * rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (- ek))) by apply bpow_ge_0. fold B. lra.
  + rewrite Rl', Rh'. replace (B2R h * B + B2R l * B) with ((B2R h + B2R l) * B) by ring.
    lra.
- (* [|l'| <= 2^-1022], so [h' + l'] is between the midpoints around [h'],
     and [l'] is [l 2^-ek] within [2^-1075]. *)
  assert (Hd : Rabs (RN (B2R l * B) - B2R l * B) <= bpow radix2 (-1075)).
  { assert (H : Rabs (RN (B2R l * B) - B2R l * B) <= / 2 * ulp radix2 fexp64 (B2R l * B))
      by (apply error_le_half_ulp; typeclasses eauto).
    rewrite (ulp_FLT_small radix2 (-1074) 53 (B2R l * B)) in H
      by (eapply Rlt_le_trans; [exact HL | apply bpow_le; lia]).
    replace (bpow radix2 (-1074)) with (2 * bpow radix2 (-1075)) in H
      by (replace (-1074)%Z with (1 + -1075)%Z by lia; rewrite bpow_plus; reflexivity).
    lra. }
  assert (Hl' : Rabs (B2R (mul l s)) <= bpow radix2 (-55)).
  { rewrite Rl'. apply Rle_trans with (bpow radix2 (-1022)); [|apply bpow_le; lia].
    apply abs_round_le_generic; [typeclasses eauto .. | apply generic_format_FLT_bpow; [easy | lia] | lra]. }
  split; [|split; [lra | split; [lia|]]].
  + assert (Ga : G (Rabs (B2R (mul h s)))) by (apply generic_format_abs, generic_format_B2R).
    destruct (Rle_or_lt 0 (B2R (mul h s))) as [H0|H0].
    * rewrite Rabs_pos_eq in Ga, Habs by exact H0.
      symmetry. apply rn_keep; [exact Ga | lra | exact Hl'].
    * rewrite Rabs_left in Ga, Habs by exact H0.
      replace (B2R (mul h s) + B2R (mul l s))
        with (- (- B2R (mul h s) + - B2R (mul l s))) by ring.
      rewrite round_NE_opp.
      rewrite rn_keep; [ring | exact Ga | lra | rewrite Rabs_Ropp; exact Hl'].
  + rewrite Rl', Rh'.
    replace (y * B - (B2R h * B + RN (B2R l * B)))
      with ((y * B - (B2R h + B2R l) * B) + - (RN (B2R l * B) - B2R l * B)) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_Ropp. lra.
Qed.

(** [ln x <= x - 1], from [1 + t <= e^t]. *)
Local Lemma ln_le_sub1 : forall x, 0 < x -> ln x <= x - 1.
Proof.
intros x Hx.
rewrite <- (ln_exp (x - 1)).
pose proof (exp_ineq1_le (x - 1)) as H.
destruct (Rle_lt_or_eq_dec x (exp (x - 1)) ltac:(lra)) as [Hlt | <-].
- apply Rlt_le, ln_increasing; assumption.
- apply Rle_refl.
Qed.

(** The logarithm of an [f64] other than 1 is at least [2^-54] in
    magnitude, as [1 - 2^-53] and [1 + 2^-52] are the [f64]s nearest to
    1. *)
Theorem ln_f64_ne1 :
  forall x : f64,
  is_finite x = true -> 0 < B2R x -> B2R x <> 1 -> bpow radix2 (-54) <= Rabs (ln (B2R x)).
Proof.
intros x Fx Hx H1.
assert (Gx : G (B2R x)) by apply generic_format_B2R.
assert (E53 : bpow radix2 (-53) = 2 * bpow radix2 (-54)).
{ replace (-53)%Z with (1 + -54)%Z by lia. rewrite bpow_plus. reflexivity. }
assert (E52 : bpow radix2 (-52) = 4 * bpow radix2 (-54)).
{ replace (-52)%Z with (2 + -54)%Z by lia. rewrite bpow_plus. reflexivity. }
assert (Ht : bpow radix2 (-54) <= / 4).
{ apply Rle_trans with (bpow radix2 (-2)); [apply bpow_le; lia|].
  change (bpow radix2 (-2)) with (/ 4). lra. }
pose proof (bpow_gt_0 radix2 (-54)) as Ht0.
destruct (Rlt_or_le (B2R x) 1) as [Hlt | Hge].
- (* [x <= pred 1 = 1 - 2^-53], and [ln x <= x - 1]. *)
  assert (Hp : B2R x <= pred64 1)
    by (apply (pred_ge_gt radix2 fexp64); [exact Gx | exact format_one | exact Hlt]).
  rewrite pred_lo in Hp by (exact format_one || lra).
  pose proof (ln_le_sub1 (B2R x) Hx) as L.
  rewrite Rabs_left by lra. lra.
- (* [x >= succ 1 = 1 + 2^-52], and [ln x = - ln (1/x) >= 1 - 1/x]. *)
  assert (Hgt : 1 < B2R x) by (destruct Hge; [assumption | congruence]).
  assert (Hs : succ64 1 <= B2R x)
    by (apply (succ_le_lt radix2 fexp64); [exact format_one | exact Gx | exact Hgt]).
  rewrite succ_hi in Hs by lra.
  assert (Hi : / B2R x <= 1 - bpow radix2 (-54)).
  { apply (Rmult_le_reg_l (B2R x)); [lra|]. rewrite Rinv_r by lra. nra. }
  pose proof (ln_le_sub1 (/ B2R x) (Rinv_0_lt_compat _ Hx)) as L.
  rewrite ln_Rinv in L by exact Hx.
  rewrite Rabs_pos_eq by lra. lra.
Qed.
