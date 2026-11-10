(** * Rounding tests with the error bound as an argument

    [Fast.round_dir_err] and [Fast.round_near_err] of [Model.v] are
    [Fast.round_dir] and [Fast.round_near] of [FastRound.v] with the
    bound [|y - (h + l)| <= 2^-68] replaced by [|y - (h + l)| <= err] for
    an [err = 2^-p] with [55 <= p <= 105], which the fast paths of [sinh],
    [cosh] and [tanh] need, as they combine two exponentials or divide
    ([round_dir_err_correct], [round_near_err_correct]). They check [1/2 <
    h < 2] themselves. [two_sum_correct] is TwoSum [Knuth] of [Fast.two_sum]
    from [TwoSum.v], and [normalize_correct] shows that [Fast.normalize]
    scales [h + l] by a power of 2 into [1 <= h < 2] exactly. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error.
From Inari Require Import Model Mpfr Encoding TwoSum TwoProduct DyDriver NearF64 NearCells
  FastRound.
From Inari Require StepUp DyExpRules.

Open Scope R_scope.

Local Notation G := (generic_format radix2 fexp64).
Local Notation succ64 := (succ radix2 fexp64).
Local Notation pred64 := (pred radix2 fexp64).

(** [Fast.two_sum a b] is [(a + b, e)] with [a + b] rounded to nearest
    and [e] the exact error of that sum. *)
Theorem two_sum_correct :
  forall a b,
  is_finite a = true -> is_finite b = true ->
  Rabs (B2R a) < bpow radix2 1023 -> Rabs (B2R b) < bpow radix2 1023 ->
  is_finite (add a b) = true ->
  let '(s, t) := Fast.two_sum a b in
  s = add a b /\ is_finite t = true /\ B2R t = B2R a + B2R b - B2R s.
Proof.
intros a b Fa Fb Ha Hb Fs.
(* [Fast.two_sum] is the sum and [Generic.two_sum_err] of it. *)
change (Fast.two_sum a b) with (add a b, Generic.two_sum_err a b (add a b)).
cbv beta iota.
destruct (two_sum_err_correct a b Fa Fb Ha Hb Fs) as (Ft & Rt).
split; [reflexivity | split; assumption].
Qed.

(** ** Scaling up by a power of two *)

(** [RN] commutes with scaling by [2^e], [e >= 0], from [2^-1022] on: the
    exponent of the last bit moves by [e] with the value. *)
Local Lemma RN_shift :
  forall x e, bpow radix2 (-1022) <= Rabs x -> (0 <= e)%Z ->
  RN (x * bpow radix2 e) = RN x * bpow radix2 e.
Proof.
intros x e Hx He.
assert (Nx : x <> 0).
{ intros ->. rewrite Rabs_R0 in Hx. pose proof (bpow_gt_0 radix2 (-1022)). lra. }
assert (Hm : (-1021 <= mag radix2 x)%Z).
{ apply mag_ge_bpow. change (-1021 - 1)%Z with (-1022)%Z. exact Hx. }
unfold round, scaled_mantissa, cexp.
rewrite (mag_mult_bpow radix2 x e Nx).
assert (Hf : FLT_exp (-1074) 53 (mag radix2 x + e) = (FLT_exp (-1074) 53 (mag radix2 x) + e)%Z)
  by (unfold FLT_exp; lia).
rewrite Hf.
set (f := FLT_exp (-1074) 53 (mag radix2 x)).
replace (x * bpow radix2 e * bpow radix2 (- (f + e))) with (x * bpow radix2 (- f)).
2: { rewrite Rmult_assoc, <- bpow_plus. replace (e + - (f + e))%Z with (- f)%Z by ring.
     reflexivity. }
unfold F2R; cbn [Fnum Fexp]. rewrite bpow_plus. ring.
Qed.

(** [scale r e] is [r 2^e] exactly for [0 <= e <= 1023], while [|r| 2^e <
    2^1024]. *)
Local Lemma scale_up :
  forall r e, is_finite r = true -> (0 <= e <= 1023)%Z ->
  Rabs (B2R r) * bpow radix2 e < bpow radix2 1024 ->
  is_finite (Fast.scale r e) = true /\ B2R (Fast.scale r e) = B2R r * bpow radix2 e.
Proof.
intros r e Fr He Hr.
destruct (pow2_bits e ltac:(lia)) as (Fp & Rp).
assert (Fm : G (B2R r * bpow radix2 e)).
{ apply mult_bpow_pos_exact_FLT; [apply generic_format_B2R | lia]. }
unfold Fast.scale, mul.
set (p := from_bits _) in *.
generalize (@Bmult_correct 53 1024 _ _ mode_NE r p).
rewrite Rp.
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE)) with RN.
rewrite (round_generic _ _ _ _ Fm).
rewrite Rlt_bool_true.
2: { rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 e)) by apply bpow_ge_0. exact Hr. }
intros (HR & HF & _).
split; [rewrite HF, Fr, Fp; reflexivity | exact HR].
Qed.

(** [Fast.normalize h l] scales [h] and [l] by [2^-k] exactly, where [2^k
    <= h < 2^(k+1)], so that the scaled [h] is in [[1, 2)] and still the
    rounding of the scaled sum to nearest. *)
Theorem normalize_correct :
  forall h l,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  bpow radix2 (-1021) <= B2R h < 2 ->
  let '(h', l', k) := Fast.normalize h l in
  is_finite h' = true /\ is_finite l' = true /\ (-1021 <= k <= 0)%Z /\
  B2R h' = B2R h * bpow radix2 (- k) /\ B2R l' = B2R l * bpow radix2 (- k) /\
  bpow radix2 k <= B2R h < bpow radix2 (k + 1) /\ B2R h' = RN (B2R h' + B2R l').
Proof.
intros h l Fh Fl Hrn Hh.
assert (H0 : 0 < bpow radix2 (-1021)) by apply bpow_gt_0.
(* For [h > 0], [to_bits h >> 52] is the biased exponent of [h]. *)
destruct (to_bits_finite h Fh) as (c & Hc & Hb).
assert (Sh : Bsign h = false).
{ rewrite StepUp.Bsign_B2R by (assumption || lra). apply Rlt_bool_false. lra. }
pose proof (exponent_finite h c Hc Hb) as Ex.
assert (Hk : (Z.shiftr (to_bits h) 52 - 1023)%Z = Generic.exponent h).
{ rewrite Ex, Hb, Sh. cbn [sign_bit]. rewrite Z.add_0_l, Z.shiftr_div_pow2 by lia.
  reflexivity. }
pose proof (abs_B2R_lt_exponent h Fh) as K1. rewrite Rabs_pos_eq in K1 by lra.
assert (Kl : (-1021 <= Generic.exponent h)%Z).
{ assert (L : (-1021 < Generic.exponent h + 1)%Z) by (apply (lt_bpow radix2); lra). lia. }
pose proof (bpow_exponent_le_abs_B2R h Fh ltac:(lia)) as K0.
rewrite Rabs_pos_eq in K0 by lra.
assert (Ku : (Generic.exponent h <= 0)%Z).
{ assert (L : (Generic.exponent h < 1)%Z).
  { apply (lt_bpow radix2). change (bpow radix2 1) with 2. lra. }
  lia. }
unfold Fast.normalize. cbv beta iota zeta. rewrite Hk.
set (k := Generic.exponent h) in *.
(* [h = RN(h + l)] with [h > 0] keeps [|l|] below [h/2]: [0] and [2h]
   are floats no closer to [h + l] than [h]. *)
assert (HL : Rabs (B2R l) <= B2R h / 2).
{ pose proof (round_N_pt radix2 fexp64 (fun z => negb (Z.even z)) (B2R h + B2R l)) as HN.
  rewrite <- Hrn in HN. destruct HN as (_ & HN).
  assert (F2 : G (B2R h * bpow radix2 1)).
  { apply mult_bpow_pos_exact_FLT; [apply generic_format_B2R | lia]. }
  change (bpow radix2 1) with 2 in F2.
  assert (F0 : G 0) by apply generic_format_0.
  pose proof (HN _ F0) as N1. pose proof (HN _ F2) as N2.
  revert N1 N2. unfold Rabs. repeat destruct (Rcase_abs _); intros; lra. }
assert (HKK : bpow radix2 k * bpow radix2 (- k) = 1).
{ rewrite <- bpow_plus, Z.add_opp_diag_r. reflexivity. }
assert (HK1 : bpow radix2 (k + 1) = 2 * bpow radix2 k).
{ rewrite bpow_plus. change (bpow radix2 1) with 2. ring. }
assert (Hh2 : B2R h * bpow radix2 (- k) < 2).
{ replace 2 with (2 * bpow radix2 k * bpow radix2 (- k)) by (rewrite Rmult_assoc, HKK; ring).
  apply Rmult_lt_compat_r; [apply bpow_gt_0 | lra]. }
assert (Hl2 : Rabs (B2R l) * bpow radix2 (- k) < 2).
{ apply Rle_lt_trans with (B2R h * bpow radix2 (- k)); [|exact Hh2].
  apply Rmult_le_compat_r; [apply bpow_ge_0 | lra]. }
assert (H2 : 2 < bpow radix2 1024) by (cbn [bpow radix_val radix2]; lra).
destruct (scale_up h (- k) Fh ltac:(lia) ltac:(rewrite Rabs_pos_eq by lra; lra))
  as (Fh' & Rh').
destruct (scale_up l (- k) Fl ltac:(lia) ltac:(lra)) as (Fl' & Rl').
split; [exact Fh'|]. split; [exact Fl'|]. split; [lia|].
split; [exact Rh'|]. split; [exact Rl'|]. split; [lra|].
(* [h + l >= h/2 >= 2^-1022] is in the normal range, where scaling by
   [2^-k] commutes with [RN]. *)
assert (HB : bpow radix2 (-1021) = 2 * bpow radix2 (-1022)) by (cbn [bpow radix_val radix2]; lra).
rewrite Rh', Rl', <- Rmult_plus_distr_r.
rewrite RN_shift by (lia || (apply Rabs_le_inv in HL; rewrite Rabs_pos_eq; lra)).
rewrite <- Hrn. reflexivity.
Qed.

(** ** The literals of [round_dir_err] and [round_near_err] *)

Local Lemma half_R : B2R Model.half = / 2.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF Model.half) with (SpecFloat.S754_finite false 4503599627370496 (-53))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

Local Lemma two_R : B2R Fast.two = 2.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF Fast.two) with (SpecFloat.S754_finite false 4503599627370496 (-51))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

Local Lemma gap1_R : B2R Fast.gap1 = bpow radix2 (-53).
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF Fast.gap1) with (SpecFloat.S754_finite false 4503599627370496 (-105))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

Local Lemma gap0_R : B2R Fast.gap0 = bpow radix2 (-54).
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF Fast.gap0) with (SpecFloat.S754_finite false 4503599627370496 (-106))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

(** A float with a positive value is finite. *)
Local Lemma finite_of_pos : forall x : f64, 0 < B2R x -> is_finite x = true.
Proof. intros [s|s| |s m e' H] Hx; try reflexivity; cbn [B2R] in Hx; lra. Qed.

(** [2^-q - 2^-p] is the float [(2^(p-q) - 1) 2^-p] for [q < p <= q + 53],
    so [sub] computes it exactly. *)
Local Lemma sub_pow2 :
  forall g x q p, is_finite g = true -> is_finite x = true ->
  B2R g = bpow radix2 (- q) -> B2R x = bpow radix2 (- p) ->
  (0 <= q < p)%Z -> (p <= q + 53)%Z -> (p <= 1074)%Z ->
  is_finite (sub g x) = true /\ B2R (sub g x) = bpow radix2 (- q) - bpow radix2 (- p).
Proof.
intros g x q p Fg Fx Rg Rx Hq Hp Hp'.
assert (E : bpow radix2 (- q) - bpow radix2 (- p) =
            F2R (Float radix2 (2 ^ (p - q) - 1) (- p))).
{ unfold F2R; cbn [Fnum Fexp]. rewrite minus_IZR, (IZR_Zpower radix2) by lia.
  rewrite Rmult_minus_distr_r, <- bpow_plus. replace (p - q + - p)%Z with (- q)%Z by ring.
  ring. }
assert (P1 : (2 ^ 0 <= 2 ^ (p - q) <= 2 ^ 53)%Z) by (split; apply Z.pow_le_mono_r; lia).
change (2 ^ 0)%Z with 1%Z in P1.
assert (Ff : G (bpow radix2 (- q) - bpow radix2 (- p))).
{ rewrite E. apply generic_format_FLT.
  apply (FLT_spec _ _ _ _ (Float radix2 (2 ^ (p - q) - 1) (- p))); [reflexivity | |].
  - cbn [Fnum]. rewrite Z.abs_eq by lia. change (Zpower radix2 53) with (2 ^ 53)%Z. lia.
  - cbn [Fexp]. lia. }
assert (B1 : bpow radix2 (- p) <= bpow radix2 (- q)) by (apply bpow_le; lia).
assert (B2 : bpow radix2 (- q) <= bpow radix2 0) by (apply bpow_le; lia).
assert (B3 : bpow radix2 0 < bpow radix2 1024) by (apply bpow_lt; lia).
pose proof (bpow_gt_0 radix2 (- p)) as B4.
unfold sub.
generalize (@Bminus_correct 53 1024 _ _ mode_NE g x Fg Fx).
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE)) with RN.
rewrite Rg, Rx, (round_generic _ _ _ _ Ff).
rewrite Rlt_bool_true by (rewrite Rabs_pos_eq; lra).
intros (HR & HF & _).
split; [exact HF | exact HR].
Qed.

(** If [|y - (h + l)| <= 2^-p = err] for [55 <= p <= 105], with [h] the
    rounding of [h + l] to nearest, then where [round_dir_err] returns, it
    returns [y 2^e] rounded toward +inf if [up] and toward -inf
    otherwise. *)
Theorem round_dir_err_correct :
  forall h l e err p up v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  (-1021 <= e <= 1022)%Z -> (55 <= p <= 105)%Z -> B2R err = bpow radix2 (- p) ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (- p) ->
  Fast.round_dir_err h l e err up = Some v ->
  rounds up (y * bpow radix2 e) v.
Proof.
intros h l e err p up v y Fh Fl Hrn He Hp Herr Hy Hv.
unfold Fast.round_dir_err in Hv.
destruct (gt h Model.half && lt h Fast.two) eqn:HC; cbn [negb] in Hv; [|discriminate].
(* The function's own check gives [1/2 < h < 2]. *)
apply andb_prop in HC as [C1 C2].
pose proof (gt_true h Model.half Fh eq_refl C1) as H1. rewrite half_R in H1.
pose proof (DyExpRules.lt_R h Fast.two Fh eq_refl C2) as H2. rewrite two_R in H2.
assert (Hh : / 2 < B2R h < 2) by lra.
destruct (low_bounds h l Fh Hrn Hh) as (U1 & U2 & Gs & Gp).
assert (Fx : G (B2R h)) by apply generic_format_B2R.
(* [err = 2^-p <= 2^-55] is below half of each gap around [h]. *)
assert (HM : bpow radix2 (- p) < bpow radix2 (-53) / 2).
{ apply Rle_lt_trans with (bpow radix2 (-55)); [apply bpow_le; lia|].
  cbn [bpow radix_val radix2]; lra. }
assert (HE : 0 < bpow radix2 e) by apply bpow_gt_0.
apply Rabs_le_inv in Hy.
assert (Fe : is_finite err = true) by (apply finite_of_pos; rewrite Herr; apply bpow_gt_0).
assert (Fo : is_finite (opp err) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fe).
destruct (gt l err) eqn:G1.
- (* [l > 2^-p]: [h < y < succ h]. *)
  pose proof (gt_true l err Fl Fe G1) as L1. rewrite Herr in L1.
  injection Hv as Hv. subst v.
  pose proof (succ_le_2 (B2R h) Fx (proj2 Hh)) as S2.
  pose proof (succ_gt_id radix2 fexp64 (B2R h) ltac:(lra)) as S1.
  destruct (bits_succ h Fh ltac:(lra)) as (Fs & Rs).
  destruct (scale_correct h e Fh ltac:(lra) He) as (Flo & Rlo).
  destruct (scale_correct _ e Fs ltac:(rewrite Rs; lra) He) as (Fhi & Rhi).
  assert (Hs : B2R (Fast.scale (from_bits (to_bits h + 1)) e) =
               succ radix2 (SpecFloat.fexp 53 1024) (B2R (Fast.scale h e))).
  { change (SpecFloat.fexp 53 1024) with fexp64.
    rewrite Rhi, Rlo, Rs, succ_shift by (lra || lia). reflexivity. }
  assert (Hb : B2R (Fast.scale h e) < y * bpow radix2 e <
               B2R (Fast.scale (from_bits (to_bits h + 1)) e)).
  { rewrite Rlo, Rhi, Rs. split; apply Rmult_lt_compat_r; lra. }
  destruct up;
    [exact (DyExpRules.rnd_bracket _ _ true _ Flo Fhi Hs Hb)
    |exact (DyExpRules.rnd_bracket _ _ false _ Flo Fhi Hs Hb)].
- destruct (lt l (opp err)) eqn:G2; [|discriminate].
  (* [l < -2^-p]: [pred h < y < h]. *)
  pose proof (DyExpRules.lt_R l (opp err) Fl Fo G2) as L1.
  unfold opp in L1. rewrite B2R_Bopp, Herr in L1.
  injection Hv as Hv. subst v.
  pose proof (pred_ge_half (B2R h) Fx (proj1 Hh)) as P2.
  pose proof (pred_lt_id radix2 fexp64 (B2R h) ltac:(lra)) as P1.
  destruct (bits_pred h Fh ltac:(lra)) as (Fp & Rp).
  destruct (scale_correct _ e Fp ltac:(rewrite Rp; lra) He) as (Flo & Rlo).
  destruct (scale_correct h e Fh ltac:(lra) He) as (Fhi & Rhi).
  assert (Hs : B2R (Fast.scale h e) =
               succ radix2 (SpecFloat.fexp 53 1024)
                 (B2R (Fast.scale (from_bits (to_bits h - 1)) e))).
  { change (SpecFloat.fexp 53 1024) with fexp64.
    rewrite Rhi, Rlo, Rp, succ_shift by (lra || lia).
    rewrite (succ_pred radix2 fexp64) by exact Fx. reflexivity. }
  assert (Hb : B2R (Fast.scale (from_bits (to_bits h - 1)) e) < y * bpow radix2 e <
               B2R (Fast.scale h e)).
  { rewrite Rlo, Rhi, Rp. split; apply Rmult_lt_compat_r; lra. }
  destruct up;
    [exact (DyExpRules.rnd_bracket _ _ true _ Flo Fhi Hs Hb)
    |exact (DyExpRules.rnd_bracket _ _ false _ Flo Fhi Hs Hb)].
Qed.

(** The same rounded to nearest, ties to even, as [near_round] says. *)
Theorem round_near_err_correct :
  forall h l e err p v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  (-1021 <= e <= 1022)%Z -> (55 <= p <= 105)%Z -> B2R err = bpow radix2 (- p) ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (- p) ->
  Fast.round_near_err h l e err = Some v ->
  near_round (y * bpow radix2 e) v.
Proof.
intros h l e err p v y Fh Fl Hrn He Hp Herr Hy Hv.
assert (Fx : G (B2R h)) by apply generic_format_B2R.
assert (Fo : is_finite Fast.one = true) by reflexivity.
assert (Fe : is_finite err = true) by (apply finite_of_pos; rewrite Herr; apply bpow_gt_0).
(* The bounds [2^-53 - 2^-p] and [2^-54 - 2^-p] are exact. *)
destruct (sub_pow2 Fast.gap1 err 53 p eq_refl Fe gap1_R Herr ltac:(lia) ltac:(lia) ltac:(lia))
  as (F1 & R1).
destruct (sub_pow2 Fast.gap0 err 54 p eq_refl Fe gap0_R Herr ltac:(lia) ltac:(lia) ltac:(lia))
  as (F0 & R0).
change (- (53))%Z with (-53)%Z in R1. change (- (54))%Z with (-54)%Z in R0.
assert (HP : bpow radix2 (-52) = 2 * bpow radix2 (-53) /\
             bpow radix2 (-53) = 2 * bpow radix2 (-54))
  by (cbn [bpow radix_val radix2]; split; lra).
apply Rabs_le_inv in Hy.
unfold Fast.round_near_err in Hv. cbv zeta in Hv.
destruct (gt h Model.half && lt h Fast.two && lt l _ && gt l _) eqn:HC; [|discriminate].
injection Hv as Hv. subst v.
apply andb_prop in HC as [HC C2].
apply andb_prop in HC as [HC C1].
apply andb_prop in HC as [C3 C4].
(* The function's own check gives [1/2 < h < 2]. *)
pose proof (gt_true h Model.half Fh eq_refl C3) as H3. rewrite half_R in H3.
pose proof (DyExpRules.lt_R h Fast.two Fh eq_refl C4) as H4. rewrite two_R in H4.
assert (Hh : / 2 < B2R h < 2) by lra.
(* Above: from 1 on, the gap to [succ h] is [2^-52] and [l < 2^-53 -
   2^-p]; below 1, it is [2^-53] and [l < 2^-54 - 2^-p]. *)
assert (HA : y < (B2R h + succ64 (B2R h)) / 2).
{ destruct (ge h Fast.one) eqn:G1.
  - pose proof (DyExpRules.lt_R l _ Fl F1 C1) as L1. rewrite R1 in L1.
    pose proof (ge_true h Fast.one Fh Fo G1) as H1. rewrite one_R in H1.
    rewrite succ_hi by lra. lra.
  - pose proof (DyExpRules.lt_R l _ Fl F0 C1) as L1. rewrite R0 in L1.
    pose proof (ge_false h Fast.one Fh Fo G1) as H1. rewrite one_R in H1.
    rewrite succ_lo by lra. lra. }
(* Below: above 1, the gap to [pred h] is [2^-52] and [l > -(2^-53 -
   2^-p)]; from 1 down, it is [2^-53] and [l > -(2^-54 - 2^-p)]. *)
assert (HB : (pred64 (B2R h) + B2R h) / 2 < y).
{ destruct (gt h Fast.one) eqn:G2.
  - assert (Fn : is_finite (opp (sub Fast.gap1 err)) = true)
      by (unfold opp; rewrite is_finite_Bopp; exact F1).
    pose proof (gt_true l _ Fl Fn C2) as L1.
    unfold opp in L1. rewrite B2R_Bopp, R1 in L1.
    pose proof (gt_true h Fast.one Fh Fo G2) as H1. rewrite one_R in H1.
    rewrite pred_hi by (assumption || lra). lra.
  - assert (Fn : is_finite (opp (sub Fast.gap0 err)) = true)
      by (unfold opp; rewrite is_finite_Bopp; exact F0).
    pose proof (gt_true l _ Fl Fn C2) as L1.
    unfold opp in L1. rewrite B2R_Bopp, R0 in L1.
    pose proof (gt_false h Fast.one Fh Fo G2) as H1. rewrite one_R in H1.
    rewrite pred_lo by (assumption || lra). lra. }
destruct (scale_correct h e Fh ltac:(lra) He) as (Fv & Rv).
pose proof (succ_le_2 (B2R h) Fx (proj2 Hh)) as S2.
pose proof (pred_ge_half (B2R h) Fx (proj1 Hh)) as P2.
assert (HE : 0 < bpow radix2 e) by apply bpow_gt_0.
assert (HE2 : bpow radix2 e <= bpow radix2 1022) by (apply bpow_le; lia).
assert (HT : 2 * bpow radix2 1022 < bpow radix2 1024 - bpow radix2 970)
  by (cbn [bpow radix_val radix2]; lra).
assert (Hy0 : 0 < y * bpow radix2 e) by (apply Rmult_lt_0_compat; lra).
unfold near_round.
destruct (Rle_dec _ _) as [HO|_].
{ (* [y 2^e < 2 * 2^1022] is below the overflow threshold. *)
  exfalso. rewrite Rabs_pos_eq in HO by lra.
  assert (y * bpow radix2 e <= 2 * bpow radix2 1022) by (apply Rmult_le_compat; lra).
  lra. }
split; [exact Fv|]. split.
- rewrite Rv. symmetry. apply rn_between.
  + apply format_shift; [exact Fx | rewrite Rabs_pos_eq; lra | lia].
  + apply Rmult_lt_0_compat; lra.
  + (* The midpoints around [h 2^e] are those around [h], times [2^e]. *)
    rewrite succ_shift, pred_shift by (assumption || lra || lia).
    split.
    * replace ((pred64 (B2R h) * bpow radix2 e + B2R h * bpow radix2 e) / 2)
        with ((pred64 (B2R h) + B2R h) / 2 * bpow radix2 e) by field.
      apply Rmult_lt_compat_r; lra.
    * replace ((B2R h * bpow radix2 e + succ64 (B2R h) * bpow radix2 e) / 2)
        with ((B2R h + succ64 (B2R h)) / 2 * bpow radix2 e) by field.
      apply Rmult_lt_compat_r; lra.
- intros _ H0. rewrite Rv in H0.
  assert (0 < B2R h * bpow radix2 e) by (apply Rmult_lt_0_compat; lra). lra.
Qed.
