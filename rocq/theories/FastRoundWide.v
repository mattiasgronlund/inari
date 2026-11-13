(** * Rounding tests for an exponent from -1085 to 1023

    [Fast.round_dir_wide] and [Fast.round_near_wide] of [Model.v] send
    [y 2^e] with [e < -1022], or [e = -1022] and [h <= 1], to the tests of
    [FastRoundSub.v] and the rest to those of [FastRound.v], which are
    also right at [e = -1022] with [h > 1], where the [f64]s next to [h]
    are in [[1, 2]] and their scaling is exact, and at [e = 1023], where
    the scaling of [2] is +inf, the rounding up of a [y 2^1023] above the
    largest [f64]
    ([round_dir_wide_correct], [round_near_wide_correct]). The tests of
    [FastRoundErr.v] are right at [e = 1023] too
    ([round_dir_err_wide_correct], [round_near_err_wide_correct]), and at
    [e = -1022] with [h > 1] ([round_dir_err_normal_correct],
    [round_near_err_normal_correct]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Mult_error.
From Inari Require Import Model Mpfr Encoding TwoSum TwoProduct DyDriver NearF64 NearCells
  FastRound FastRoundErr FastRoundSub.
From Inari Require StepUp DyExpRules IdealGetD MpfrRound MpfrIdeal.

Open Scope R_scope.

Local Notation G := (generic_format radix2 fexp64).
Local Notation succ64 := (succ radix2 fexp64).
Local Notation pred64 := (pred radix2 fexp64).

(** ** Scaling by [2^e] for [e] from -1022 to 1023 *)

(** [x 2^e] is normal for [x >= 1/2] from [e = -1021] on, and for [x >= 1]
    at [e = -1022]: the condition on [mag x + e] that Flocq's shift lemmas
    take. *)
Local Lemma mag_wide :
  forall (x : R) (e : Z), / 2 <= x -> (-1022 <= e)%Z -> ((e = -1022)%Z -> 1 <= x) ->
  (-1021 <= mag radix2 x + e)%Z.
Proof.
intros x e Hx He H1.
destruct (Z.eq_dec e (-1022)) as [Ee|Ee].
- assert (M : (1 <= mag radix2 x)%Z).
  { apply mag_ge_bpow. change (bpow radix2 (1 - 1)) with 1.
    rewrite Rabs_pos_eq by lra. exact (H1 Ee). }
  lia.
- pose proof (mag_ge_0 x ltac:(rewrite Rabs_pos_eq; lra)). lia.
Qed.

Local Lemma format_wide :
  forall (x : R) (e : Z), G x -> / 2 <= x -> (-1022 <= e)%Z -> ((e = -1022)%Z -> 1 <= x) ->
  G (x * bpow radix2 e).
Proof.
intros x e Fx Hx He H1.
apply mult_bpow_exact_FLT; [exact Fx|].
pose proof (mag_wide x e Hx He H1). lia.
Qed.

Local Lemma succ_wide :
  forall (x : R) (e : Z), / 2 <= x -> (-1022 <= e)%Z -> ((e = -1022)%Z -> 1 <= x) ->
  succ64 (x * bpow radix2 e) = succ64 x * bpow radix2 e.
Proof.
intros x e Hx He H1.
pose proof (mag_wide x e Hx He H1).
pose proof (mag_ge_0 x ltac:(rewrite Rabs_pos_eq; lra)).
apply succ_FLT_exact_shift_pos; [lra | lia | lia].
Qed.

(** As in [FastRound.pred_shift], [pred] goes through [succ] of [pred x],
    which is at least 1 at [e = -1022] as [x > 1] there. *)
Local Lemma pred_wide :
  forall (x : R) (e : Z), G x -> / 2 < x -> (-1022 <= e)%Z -> ((e = -1022)%Z -> 1 < x) ->
  pred64 (x * bpow radix2 e) = pred64 x * bpow radix2 e.
Proof.
intros x e Fx Hx He H1.
pose proof (pred_ge_half x Fx Hx) as P1.
assert (P2 : (e = -1022)%Z -> 1 <= pred64 x).
{ intros Ee. apply (pred_ge_gt radix2 fexp64); [exact format_one | exact Fx | exact (H1 Ee)]. }
assert (Fp : G (pred64 x)) by (apply (generic_format_pred radix2 fexp64); exact Fx).
rewrite <- (succ_pred radix2 fexp64 x Fx) at 1.
rewrite <- (succ_wide (pred64 x) e P1 He P2).
apply (pred_succ radix2 fexp64).
exact (format_wide (pred64 x) e Fp P1 He P2).
Qed.

(** [scale r e] is [r 2^e] exactly where that is below [2^1024], for [r
    >= 1/2], and [r >= 1] at [e = -1022]. *)
Local Lemma scale_wide :
  forall (r : f64) (e : Z), is_finite r = true -> / 2 <= B2R r -> (-1022 <= e <= 1023)%Z ->
  ((e = -1022)%Z -> 1 <= B2R r) -> B2R r * bpow radix2 e < bpow radix2 1024 ->
  is_finite (Fast.scale r e) = true /\ B2R (Fast.scale r e) = B2R r * bpow radix2 e.
Proof.
intros r e Fr Hr He H1 HT.
destruct (pow2_bits e He) as (Fp & Rp).
assert (Fm : G (B2R r * bpow radix2 e)).
{ apply format_wide; [apply generic_format_B2R | exact Hr | lia | exact H1]. }
assert (HE : 0 < bpow radix2 e) by apply bpow_gt_0.
unfold Fast.scale, mul.
set (p := from_bits _) in *.
generalize (@Bmult_correct 53 1024 _ _ mode_NE r p).
rewrite Rp.
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE)) with RN.
rewrite (round_generic _ _ _ _ Fm).
rewrite Rlt_bool_true.
2: { rewrite Rabs_pos_eq by (apply Rmult_le_pos; lra). exact HT. }
intros (HR & HF & _).
split; [rewrite HF, Fr, Fp; reflexivity | exact HR].
Qed.

Local Lemma two_R : B2R Fast.two = 2.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF Fast.two) with (SpecFloat.S754_finite false 4503599627370496 (-51))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

(** [2 * 2^1023] overflows to +inf. *)
Local Lemma scale_two_top :
  forall b : f64, is_finite b = true -> B2R b = 2 -> Fast.scale b 1023 = B754_infinity false.
Proof.
intros b Fb Rb.
assert (Eb : b = Fast.two).
{ apply B2R_Bsign_inj; [exact Fb | reflexivity | rewrite Rb, two_R; reflexivity |].
  rewrite (StepUp.Bsign_B2R b Fb) by lra. rewrite Rb, Rlt_bool_false by lra.
  vm_compute. reflexivity. }
subst b. vm_compute. reflexivity.
Qed.

Local Lemma pred_two : pred64 2 = 2 - bpow radix2 (-52).
Proof. change 2 with (bpow radix2 1) at 1. rewrite pred_bpow. reflexivity. Qed.

(** A real between [f64::MAX = 2^1024 - 2^971] and [2^1024] rounds up to
    +inf and down to [f64::MAX], as in [DyExpRules.rnd_overflow]. *)
Local Lemma rnd_top :
  forall (m : f64) (up : bool) (r : R),
  is_finite m = true -> B2R m = bpow radix2 1024 - bpow radix2 971 ->
  B2R m < r < bpow radix2 1024 ->
  rounds up r (if up then B754_infinity false else m).
Proof.
intros m up r Fm Em Hr. unfold rounds. destruct up; cbv beta iota.
- cbn [with_val mpfr_round]. intros g Fg.
  destruct (IdealGetD.f64_format_G g Fg) as [Gg Hg]. apply Rabs_def2 in Hg as [Hg _].
  pose proof (IdealGetD.G_le_max g Gg Hg). lra.
- assert (H971 : 0 < bpow radix2 971 < bpow radix2 1024)
    by (split; [apply bpow_gt_0 | apply bpow_lt; lia]).
  destruct (MpfrIdeal.with_val_finite_cases _ Fm) as [(s & _ & H0) | (-> & H0)]; [lra|].
  cbn [mpfr_round]. split; [exact H0|].
  split; [exact (MpfrRound.f64_format_B2R _ Fm)|]. split; [lra|].
  intros g Fg Hg. destruct (IdealGetD.f64_format_G g Fg) as [Gg Hg'].
  apply Rabs_def2 in Hg' as [Hg' _].
  rewrite Em. apply IdealGetD.G_le_max; [exact Gg | exact Hg'].
Qed.

(** If [a < y < b] for [f64]s [a] and [b = succ a] in [[1/2, 2]], then
    [y 2^e] rounds toward +inf to [b 2^e] and toward -inf to [a 2^e], as
    [Fast.scale] computes them, for [e] from -1022 (where [a >= 1]) to
    1023. *)
Local Lemma bracket_wide :
  forall (a b : f64) (e : Z) (up : bool) (y : R),
  is_finite a = true -> is_finite b = true -> B2R b = succ64 (B2R a) ->
  / 2 <= B2R a -> B2R b <= 2 -> (-1022 <= e <= 1023)%Z -> ((e = -1022)%Z -> 1 <= B2R a) ->
  B2R a < y < B2R b ->
  rounds up (y * bpow radix2 e) (Fast.scale (if up then b else a) e).
Proof.
intros a b e up y Fa Fb Hs Ha Hb He H1 Hy.
assert (Ga : G (B2R a)) by apply generic_format_B2R.
assert (HE : 0 < bpow radix2 e) by apply bpow_gt_0.
pose proof (succ_gt_id radix2 fexp64 (B2R a) ltac:(lra)) as S1.
destruct (Rlt_le_dec (B2R b * bpow radix2 e) (bpow radix2 1024)) as [HT|HT].
- (* [b 2^e < 2^1024]: both scalings are exact, as in [FastRound]. *)
  assert (Ta : B2R a * bpow radix2 e < bpow radix2 1024).
  { apply Rlt_trans with (2 := HT). apply Rmult_lt_compat_r; lra. }
  destruct (scale_wide a e Fa Ha He H1 Ta) as (Flo & Rlo).
  destruct (scale_wide b e Fb ltac:(lra) He ltac:(intros Ee; specialize (H1 Ee); lra) HT)
    as (Fhi & Rhi).
  assert (Hs' : B2R (Fast.scale b e) =
                succ radix2 (SpecFloat.fexp 53 1024) (B2R (Fast.scale a e))).
  { change (SpecFloat.fexp 53 1024) with fexp64.
    rewrite Rhi, Rlo, Hs, succ_wide by (lra || lia || assumption). reflexivity. }
  assert (Hb' : B2R (Fast.scale a e) < y * bpow radix2 e < B2R (Fast.scale b e)).
  { rewrite Rlo, Rhi. split; apply Rmult_lt_compat_r; lra. }
  destruct up;
    [exact (DyExpRules.rnd_bracket _ _ true _ Flo Fhi Hs' Hb')
    |exact (DyExpRules.rnd_bracket _ _ false _ Flo Fhi Hs' Hb')].
- (* [b 2^e >= 2^1024] only for [b = 2] and [e = 1023]: then [a] is
     [f64::MAX / 2^1023], and [Fast.scale b 1023] is +inf. *)
  assert (T2 : 2 * bpow radix2 1023 = bpow radix2 1024).
  { change 2 with (bpow radix2 1). rewrite <- bpow_plus. reflexivity. }
  assert (Ee : e = 1023%Z).
  { destruct (Z.eq_dec e 1023) as [Ee|Ne]; [exact Ee|]. exfalso.
    assert (Le : bpow radix2 e <= bpow radix2 1022) by (apply bpow_le; lia).
    assert (L2 : 2 * bpow radix2 1022 < bpow radix2 1024)
      by (cbn [bpow radix_val radix2]; lra).
    assert (B2R b * bpow radix2 e <= 2 * bpow radix2 1022) by (apply Rmult_le_compat; lra).
    lra. }
  subst e.
  assert (Hb2 : B2R b = 2).
  { apply Rle_antisym; [exact Hb|].
    apply Rmult_le_reg_r with (bpow radix2 1023); [apply bpow_gt_0|]. lra. }
  assert (Ra : B2R a = 2 - bpow radix2 (-52)).
  { rewrite <- pred_two, <- Hb2, Hs. symmetry. apply (pred_succ radix2 fexp64). exact Ga. }
  assert (TM : B2R a * bpow radix2 1023 = bpow radix2 1024 - bpow radix2 971).
  { rewrite Ra, <- T2.
    replace (bpow radix2 971) with (bpow radix2 (-52) * bpow radix2 1023)
      by (rewrite <- bpow_plus; reflexivity).
    ring. }
  assert (H971 : 0 < bpow radix2 971) by apply bpow_gt_0.
  destruct (scale_wide a 1023 Fa Ha ltac:(lia) ltac:(intros Hc; exfalso; lia)
              ltac:(rewrite TM; lra)) as (Flo & Rlo).
  assert (Hr : B2R (Fast.scale a 1023) < y * bpow radix2 1023 < bpow radix2 1024).
  { rewrite Rlo, <- T2. split; apply Rmult_lt_compat_r; (apply bpow_gt_0 || lra). }
  assert (Rm : B2R (Fast.scale a 1023) = bpow radix2 1024 - bpow radix2 971)
    by (rewrite Rlo; exact TM).
  destruct up.
  + change (rounds true (y * bpow radix2 1023) (Fast.scale b 1023)).
    rewrite (scale_two_top b Fb Hb2).
    exact (rnd_top (Fast.scale a 1023) true _ Flo Rm Hr).
  + exact (rnd_top (Fast.scale a 1023) false _ Flo Rm Hr).
Qed.

(** If [y] is strictly between the midpoints around an [f64] [h] in [(1/2,
    2)], then [y 2^e] rounds to nearest to [h 2^e], as [Fast.scale]
    computes it, for [e] from -1022 (where [h > 1]) to 1023. *)
Local Lemma near_wide :
  forall (h : f64) (e : Z) (y : R),
  is_finite h = true -> / 2 < B2R h < 2 -> (-1022 <= e <= 1023)%Z ->
  ((e = -1022)%Z -> 1 < B2R h) ->
  (pred64 (B2R h) + B2R h) / 2 < y < (B2R h + succ64 (B2R h)) / 2 ->
  near_round (y * bpow radix2 e) (Fast.scale h e).
Proof.
intros h e y Fh Hh He H1 Hy.
assert (Fx : G (B2R h)) by apply generic_format_B2R.
pose proof (succ_le_2 (B2R h) Fx (proj2 Hh)) as S2.
pose proof (pred_ge_half (B2R h) Fx (proj1 Hh)) as P2.
pose proof (succ_gt_id radix2 fexp64 (B2R h) ltac:(lra)) as S1.
pose proof (pred_lt_id radix2 fexp64 (B2R h) ltac:(lra)) as P1.
assert (H1' : (e = -1022)%Z -> 1 <= B2R h) by (intros Ee; specialize (H1 Ee); lra).
assert (HE : 0 < bpow radix2 e) by apply bpow_gt_0.
assert (HE2 : bpow radix2 e <= bpow radix2 1023) by (apply bpow_le; lia).
assert (T2 : 2 * bpow radix2 1023 = bpow radix2 1024).
{ change 2 with (bpow radix2 1). rewrite <- bpow_plus. reflexivity. }
(* [y < 2 - 2^-53]: from 1 on, [succ h = h + 2^-52 <= 2]; below 1,
   [succ h <= 1]. *)
assert (HY : y < 2 - bpow radix2 (-53)).
{ assert (HP : bpow radix2 (-52) = 2 * bpow radix2 (-53)) by (cbn [bpow radix_val radix2]; lra).
  assert (H53 : bpow radix2 (-53) <= bpow radix2 0) by (apply bpow_le; lia).
  change (bpow radix2 0) with 1 in H53.
  destruct (Rle_lt_dec 1 (B2R h)) as [L|L].
  - rewrite succ_hi in S2, Hy by lra. lra.
  - assert (succ64 (B2R h) <= 1)
      by (apply (succ_le_lt radix2 fexp64); [exact Fx | exact format_one | exact L]).
    lra. }
(* So [y 2^e < (2 - 2^-53) 2^1023 = 2^1024 - 2^970], below the overflow
   threshold of [near_round]. *)
assert (HT : (2 - bpow radix2 (-53)) * bpow radix2 1023 = bpow radix2 1024 - bpow radix2 970).
{ rewrite <- T2.
  replace (bpow radix2 970) with (bpow radix2 (-53) * bpow radix2 1023)
    by (rewrite <- bpow_plus; reflexivity).
  ring. }
assert (Hy0 : 0 < y) by lra.
assert (Hy1 : y * bpow radix2 e < bpow radix2 1024 - bpow radix2 970).
{ rewrite <- HT. apply Rle_lt_trans with (y * bpow radix2 1023).
  - apply Rmult_le_compat_l; lra.
  - apply Rmult_lt_compat_r; [apply bpow_gt_0 | lra]. }
assert (Th : B2R h * bpow radix2 e < bpow radix2 1024).
{ rewrite <- T2. apply Rle_lt_trans with (B2R h * bpow radix2 1023).
  - apply Rmult_le_compat_l; lra.
  - apply Rmult_lt_compat_r; [apply bpow_gt_0 | lra]. }
destruct (scale_wide h e Fh ltac:(lra) He H1' Th) as (Fv & Rv).
unfold near_round.
destruct (Rle_dec _ _) as [HO|_].
{ exfalso. rewrite Rabs_pos_eq in HO by (apply Rmult_le_pos; lra). lra. }
split; [exact Fv|]. split.
- rewrite Rv. symmetry. apply rn_between.
  + apply format_wide; [exact Fx | lra | lia | exact H1'].
  + apply Rmult_lt_0_compat; lra.
  + (* The midpoints around [h 2^e] are those around [h], times [2^e]. *)
    rewrite succ_wide, pred_wide by (assumption || lra || lia).
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

(** ** The literals of [round_dir_err] and [round_near_err]

    Copies of the local lemmas of [FastRoundErr.v]. *)

Local Lemma half_R : B2R Model.half = / 2.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF Model.half) with (SpecFloat.S754_finite false 4503599627370496 (-53))
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

(** ** The directed test with a bound [err] below [2^-54] *)

(** The comparisons of [Fast.round_dir] and [Fast.round_dir_err], for an
    [err] that bounds [|y - (h + l)|] and is below half of each gap
    around [h], as [FastRound.round_dir_correct] and
    [FastRoundErr.round_dir_err_correct] prove them, with [bracket_wide]
    in place of [scale_correct] for [e] from -1022 (where [h > 1]) to
    1023. *)
Local Lemma dir_test :
  forall (h l err : f64) (e : Z) (up : bool) (v : f64) (y : R),
  is_finite h = true -> is_finite l = true -> is_finite err = true ->
  B2R h = RN (B2R h + B2R l) -> / 2 < B2R h < 2 ->
  (-1022 <= e <= 1023)%Z -> ((e = -1022)%Z -> 1 < B2R h) ->
  B2R err < bpow radix2 (-53) / 2 -> Rabs (y - (B2R h + B2R l)) <= B2R err ->
  (if gt l err then Some (Fast.scale (if up then from_bits (to_bits h + 1) else h) e)
   else if lt l (opp err) then Some (Fast.scale (if up then h else from_bits (to_bits h - 1)) e)
   else None) = Some v ->
  rounds up (y * bpow radix2 e) v.
Proof.
intros h l err e up v y Fh Fl Fe Hrn Hh He H1 HM Hy Hv.
destruct (low_bounds h l Fh Hrn Hh) as (U1 & U2 & Gs & Gp).
assert (Fx : G (B2R h)) by apply generic_format_B2R.
apply Rabs_le_inv in Hy.
assert (Fo : is_finite (opp err) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fe).
destruct (gt l err) eqn:G1.
- (* [l > err]: [h < y < succ h]. *)
  pose proof (gt_true l err Fl Fe G1) as L1.
  injection Hv as Hv. subst v.
  pose proof (succ_le_2 (B2R h) Fx (proj2 Hh)) as S2.
  destruct (bits_succ h Fh ltac:(lra)) as (Fs & Rs).
  apply bracket_wide;
    [exact Fh | exact Fs | exact Rs | lra | rewrite Rs; exact S2 | exact He
    | intros Ee; specialize (H1 Ee); lra | rewrite Rs; lra].
- destruct (lt l (opp err)) eqn:G2; [|discriminate].
  (* [l < -err]: [pred h < y < h]. *)
  pose proof (DyExpRules.lt_R l (opp err) Fl Fo G2) as L1.
  unfold opp in L1. rewrite B2R_Bopp in L1.
  injection Hv as Hv. subst v.
  pose proof (pred_ge_half (B2R h) Fx (proj1 Hh)) as P2.
  destruct (bits_pred h Fh ltac:(lra)) as (Fp & Rp).
  apply bracket_wide;
    [exact Fp | exact Fh | rewrite Rp, (succ_pred radix2 fexp64 _ Fx); reflexivity
    | rewrite Rp; exact P2 | lra | exact He | | rewrite Rp; lra].
  (* At [e = -1022], [h > 1], so [pred h >= 1]. *)
  intros Ee. rewrite Rp.
  apply (pred_ge_gt radix2 fexp64); [exact format_one | exact Fx | exact (H1 Ee)].
Qed.

(** ** The theorems *)

Theorem round_dir_wide_correct :
  forall h l e up v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < B2R h < 2 -> (-1085 <= e)%Z ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  Fast.round_dir_wide h l e up = Some v ->
  rounds up (y * bpow radix2 e) v.
Proof.
intros h l e up v y Fh Fl Hrn Hh He Hy Hv.
unfold Fast.round_dir_wide in Hv.
destruct (1023 <? e)%Z eqn:K1; [discriminate|].
apply Z.ltb_ge in K1.
destruct ((e <? -1022)%Z || ((e =? -1022)%Z && le h Fast.one)) eqn:K2.
- (* [e < -1022], or [e = -1022] with [h <= 1]: the subnormal test. *)
  apply (FastRoundSub.round_dir_sub_correct h l e up v y Fh Fl Hrn Hh); [|exact Hy|exact Hv].
  apply Bool.orb_true_iff in K2 as [K2|K2].
  + apply Z.ltb_lt in K2. lia.
  + apply Bool.andb_true_iff in K2 as [K2 _]. apply Z.eqb_eq in K2. lia.
- (* Otherwise [e >= -1022], and [h > 1] at [e = -1022]. *)
  apply Bool.orb_false_iff in K2 as [K2 K3].
  apply Z.ltb_ge in K2.
  assert (H1 : (e = -1022)%Z -> 1 < B2R h).
  { intros Ee. subst e. rewrite Z.eqb_refl in K3. cbn [andb] in K3.
    (* [le h one] is [ge one h]. *)
    pose proof (ge_false Fast.one h eq_refl Fh K3) as L. rewrite one_R in L. exact L. }
  assert (HP : bpow radix2 (-53) = 2 * bpow radix2 (-54))
    by (cbn [bpow radix_val radix2]; lra).
  pose proof (bpow_lt radix2 (-68) (-54) ltac:(lia)) as HL.
  rewrite round_dir_eq in Hv.
  apply (dir_test h l Fast.err e up v y Fh Fl ltac:(reflexivity) Hrn Hh ltac:(lia) H1);
    [rewrite err_R; lra | rewrite err_R; exact Hy | exact Hv].
Qed.

Theorem round_near_wide_correct :
  forall h l e v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < B2R h < 2 -> (-1085 <= e)%Z ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  Fast.round_near_wide h l e = Some v ->
  near_round (y * bpow radix2 e) v.
Proof.
intros h l e v y Fh Fl Hrn Hh He Hy Hv.
unfold Fast.round_near_wide in Hv.
destruct (1023 <? e)%Z eqn:K1; [discriminate|].
apply Z.ltb_ge in K1.
destruct ((e <? -1022)%Z || ((e =? -1022)%Z && le h Fast.one)) eqn:K2.
{ (* [e < -1022], or [e = -1022] with [h <= 1]: the subnormal test. *)
  apply (FastRoundSub.round_near_sub_correct h l e v y Fh Fl Hrn Hh); [|exact Hy|exact Hv].
  apply Bool.orb_true_iff in K2 as [K2|K2].
  - apply Z.ltb_lt in K2. lia.
  - apply Bool.andb_true_iff in K2 as [K2 _]. apply Z.eqb_eq in K2. lia. }
(* Otherwise [e >= -1022], and [h > 1] at [e = -1022]. *)
apply Bool.orb_false_iff in K2 as [K2 K3].
apply Z.ltb_ge in K2.
assert (Hb : (e = -1022)%Z -> 1 < B2R h).
{ intros Ee. subst e. rewrite Z.eqb_refl in K3. cbn [andb] in K3.
  (* [le h one] is [ge one h]. *)
  pose proof (ge_false Fast.one h eq_refl Fh K3) as L. rewrite one_R in L. exact L. }
(* The rest is [FastRound.round_near_correct]'s proof, up to the scaling. *)
assert (Fx : G (B2R h)) by apply generic_format_B2R.
assert (Fo : is_finite Fast.one = true) by reflexivity.
assert (HP : bpow radix2 (-52) = 2 * bpow radix2 (-53) /\
             bpow radix2 (-53) = 2 * bpow radix2 (-54))
  by (cbn [bpow radix_val radix2]; split; lra).
apply Rabs_le_inv in Hy.
unfold Fast.round_near in Hv. cbv zeta in Hv.
destruct (lt l _ && gt l _) eqn:HC; [|discriminate].
injection Hv as Hv. subst v.
apply andb_prop in HC as [C1 C2].
(* Above: from 1 on, the gap to [succ h] is [2^-52] and [l < 2^-53 -
   2^-68]; below 1, it is [2^-53] and [l < 2^-54 - 2^-68]. *)
assert (HA : y < (B2R h + succ64 (B2R h)) / 2).
{ destruct (ge h Fast.one) eqn:G1.
  - pose proof (DyExpRules.lt_R l Fast.near1 Fl eq_refl C1) as L1. rewrite near1_R in L1.
    pose proof (ge_true h Fast.one Fh Fo G1) as H1. rewrite one_R in H1.
    rewrite succ_hi by lra. lra.
  - pose proof (DyExpRules.lt_R l Fast.near0 Fl eq_refl C1) as L1. rewrite near0_R in L1.
    pose proof (ge_false h Fast.one Fh Fo G1) as H1. rewrite one_R in H1.
    rewrite succ_lo by lra. lra. }
(* Below: above 1, the gap to [pred h] is [2^-52] and [l > -(2^-53 -
   2^-68)]; from 1 down, it is [2^-53] and [l > -(2^-54 - 2^-68)]. *)
assert (HB : (pred64 (B2R h) + B2R h) / 2 < y).
{ destruct (gt h Fast.one) eqn:G2.
  - pose proof (gt_true l (opp Fast.near1) Fl eq_refl C2) as L1.
    unfold opp in L1. rewrite B2R_Bopp, near1_R in L1.
    pose proof (gt_true h Fast.one Fh Fo G2) as H1. rewrite one_R in H1.
    rewrite pred_hi by (assumption || lra). lra.
  - pose proof (gt_true l (opp Fast.near0) Fl eq_refl C2) as L1.
    unfold opp in L1. rewrite B2R_Bopp, near0_R in L1.
    pose proof (gt_false h Fast.one Fh Fo G2) as H1. rewrite one_R in H1.
    rewrite pred_lo by (assumption || lra). lra. }
exact (near_wide h e y Fh Hh ltac:(lia) Hb (conj HB HA)).
Qed.

Theorem round_dir_err_wide_correct :
  forall h l e err p up v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  (-1021 <= e <= 1023)%Z -> (55 <= p <= 105)%Z -> B2R err = bpow radix2 (- p) ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (- p) ->
  Fast.round_dir_err h l e err up = Some v ->
  rounds up (y * bpow radix2 e) v.
Proof.
intros h l e err p up v y Fh Fl Hrn He Hp Herr Hy Hv.
assert (Fe : is_finite err = true) by (apply finite_of_pos; rewrite Herr; apply bpow_gt_0).
rewrite (round_dir_err_eq h l e err up Fe ltac:(rewrite Herr; apply bpow_ge_0)) in Hv.
destruct (gt h Model.half && lt h Fast.two) eqn:HC; [|discriminate].
apply andb_prop in HC as [C3 C4].
(* The function's own check gives [1/2 < h < 2]. *)
pose proof (gt_true h Model.half Fh eq_refl C3) as H3. rewrite half_R in H3.
pose proof (DyExpRules.lt_R h Fast.two Fh eq_refl C4) as H4. rewrite two_R in H4.
(* [err = 2^-p <= 2^-55], below half of [2^-53]. *)
assert (HP : bpow radix2 (-53) = 2 * bpow radix2 (-54))
  by (cbn [bpow radix_val radix2]; lra).
pose proof (bpow_le radix2 (- p) (-55) ltac:(lia)) as HL.
pose proof (bpow_lt radix2 (-55) (-54) ltac:(lia)) as HL'.
apply (dir_test h l err e up v y Fh Fl Fe Hrn ltac:(lra) ltac:(lia)
         ltac:(intros; exfalso; lia));
  [rewrite Herr; lra | rewrite Herr; exact Hy | exact Hv].
Qed.

Theorem round_near_err_wide_correct :
  forall h l e err p v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  (-1021 <= e <= 1023)%Z -> (55 <= p <= 105)%Z -> B2R err = bpow radix2 (- p) ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (- p) ->
  Fast.round_near_err h l e err = Some v ->
  near_round (y * bpow radix2 e) v.
Proof.
intros h l e err p v y Fh Fl Hrn He Hp Herr Hy Hv.
(* [FastRoundErr.round_near_err_correct]'s proof, up to the scaling. *)
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
(* [e >= -1021], so the premise for [e = -1022] is vacuous. *)
exact (near_wide h e y Fh Hh ltac:(lia) ltac:(intros; exfalso; lia) (conj HB HA)).
Qed.

(** The same tests from [e = -1022], where [h > 1], as [Fast.round_dir_wide_err]
    and [Fast.round_near_wide_err] call them ([FastRoundWideErr.v]). *)

Theorem round_dir_err_normal_correct :
  forall h l e err p up v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  (-1022 <= e <= 1023)%Z -> ((e = -1022)%Z -> 1 < B2R h) ->
  (55 <= p <= 105)%Z -> B2R err = bpow radix2 (- p) ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (- p) ->
  Fast.round_dir_err h l e err up = Some v ->
  rounds up (y * bpow radix2 e) v.
Proof.
intros h l e err p up v y Fh Fl Hrn He H1 Hp Herr Hy Hv.
assert (Fe : is_finite err = true) by (apply finite_of_pos; rewrite Herr; apply bpow_gt_0).
rewrite (round_dir_err_eq h l e err up Fe ltac:(rewrite Herr; apply bpow_ge_0)) in Hv.
destruct (gt h Model.half && lt h Fast.two) eqn:HC; [|discriminate].
apply andb_prop in HC as [C3 C4].
(* The function's own check gives [1/2 < h < 2]. *)
pose proof (gt_true h Model.half Fh eq_refl C3) as H3. rewrite half_R in H3.
pose proof (DyExpRules.lt_R h Fast.two Fh eq_refl C4) as H4. rewrite two_R in H4.
(* [err = 2^-p <= 2^-55], below half of [2^-53]. *)
assert (HP : bpow radix2 (-53) = 2 * bpow radix2 (-54))
  by (cbn [bpow radix_val radix2]; lra).
pose proof (bpow_le radix2 (- p) (-55) ltac:(lia)) as HL.
pose proof (bpow_lt radix2 (-55) (-54) ltac:(lia)) as HL'.
apply (dir_test h l err e up v y Fh Fl Fe Hrn ltac:(lra) ltac:(lia) H1);
  [rewrite Herr; lra | rewrite Herr; exact Hy | exact Hv].
Qed.

Theorem round_near_err_normal_correct :
  forall h l e err p v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  (-1022 <= e <= 1023)%Z -> ((e = -1022)%Z -> 1 < B2R h) ->
  (55 <= p <= 105)%Z -> B2R err = bpow radix2 (- p) ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (- p) ->
  Fast.round_near_err h l e err = Some v ->
  near_round (y * bpow radix2 e) v.
Proof.
intros h l e err p v y Fh Fl Hrn He Hl1 Hp Herr Hy Hv.
(* [FastRoundErr.round_near_err_correct]'s proof, up to the scaling. *)
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
exact (near_wide h e y Fh Hh ltac:(lia) Hl1 (conj HB HA)).
Qed.
