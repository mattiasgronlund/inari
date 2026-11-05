(** * [rational_to_f64] and [number_to_f64] round a bound correctly

    [rational_to_f64 x infsup] is the [Rat] [x] rounded toward -inf for
    [Inf] and toward +inf for [Sup] to an [f64], as [mpfr_round] with
    [f64_format] says, with [inexact] false exactly when [x] is a finite
    [f64], and [overflow] true exactly when the result is infinite. It
    rounds up a nonzero [x] by [round_up_scaled] of [scale x]
    ([ParseScale.v]), which is [round_up_exact] for [Mid] ([RoundUpExact.v]),
    and rounds down [x] as the negation of [-x] rounded up.
    [number_to_f64] does the same for a [Rational], and returns the
    infinity itself, never inexact nor overflowed, for [NegInfinity] and
    [Infinity]. [number_neg_correct] shows that [-x] of a [Number] negates
    the reals that it bounds. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Ieee1788 Mpfr Spec RoundUpExact ParseScale.

Open Scope R_scope.

(** A bound [n] is exact: it is an infinity, or a rational that a finite
    [f64] holds. *)
Definition number_exact (n : Number) : Prop :=
  match n with Rational q => f64_format (rat_R q) | _ => True end.

(** [w] is the bound [n] rounded in the direction of [infsup]: an infinity
    is itself, and a rational is rounded as [mpfr_round] says. *)
Definition number_round (infsup : InfSup) (n : Number) (w : f64) : Prop :=
  match n with
  | NegInfinity => w = B754_infinity true
  | Rational q => mpfr_round f64_format (as_rnd_t infsup) (rat_R q) (with_val w)
  | Infinity => w = B754_infinity false
  end.

(** Rounding to [F] is rounding to any [G] with the same elements. *)
Lemma mpfr_round_ext :
  forall (F G : R -> Prop) rnd r v, (forall y, F y <-> G y) ->
  mpfr_round F rnd r v -> mpfr_round G rnd r v.
Proof.
intros F G [|] r [|[|]|s|y] HFG H; cbn [mpfr_round] in *; try contradiction.
- intros g Gg. apply H, HFG, Gg.
- destruct H as (F0 & H0 & Hmax). split; [apply HFG, F0|]. split; [exact H0|].
  intros g Gg. apply Hmax, HFG, Gg.
- destruct H as (Hy & Fy & Hyr & Hmax). split; [exact Hy|]. split; [apply HFG, Fy|].
  split; [exact Hyr|]. intros g Gg. apply Hmax, HFG, Gg.
- intros g Gg. apply H, HFG, Gg.
- destruct H as (F0 & H0 & Hmin). split; [apply HFG, F0|]. split; [exact H0|].
  intros g Gg. apply Hmin, HFG, Gg.
- destruct H as (Hy & Fy & Hyr & Hmin). split; [exact Hy|]. split; [apply HFG, Fy|].
  split; [exact Hyr|]. intros g Gg. apply Hmin, HFG, Gg.
Qed.

(** A rounding is never NaN, so a rounded float is infinite exactly when
    it is not finite. *)
Lemma round_overflow :
  forall F rnd r w, mpfr_round F rnd r (with_val w) ->
  f64_is_infinite w = negb (is_finite w).
Proof.
intros F rnd r [s|s| |s mw ew Hw] H; try reflexivity.
destruct rnd; contradiction.
Qed.

(** [-x] of a [Rat], as [number_neg] makes it, has the opposite value. *)
Lemma rat_R_neg :
  forall x,
  rat_R {| rat_neg := negb (rat_neg x); rat_num := rat_num x; rat_den := rat_den x;
           rat_e2 := rat_e2 x; rat_e5 := rat_e5 x |} = - rat_R x.
Proof.
intros x. unfold rat_R. cbn [rat_neg rat_num rat_den rat_e2 rat_e5]. cbv zeta.
destruct (rat_neg x); cbn [negb]; ring.
Qed.

(** A nonzero [Rat] is negative if [rat_neg] and positive otherwise, as
    [num], [den] and the powers of 2 and 5 are positive. *)
Lemma rat_R_cases :
  forall x, rat_ok x -> rat_num x <> 0%Z ->
  (rat_neg x = true /\ rat_R x < 0) \/ (rat_neg x = false /\ 0 < rat_R x).
Proof.
(* The bounds [< 2^2^63] are dropped: [lia] would compute them. *)
intros x ((Hn & _) & (Hd & _) & _) H0.
assert (Hp : 0 < IZR (rat_num x) * bpow radix2 (rat_e2 x) * bpow radix5 (rat_e5 x)
                 / IZR (rat_den x)).
{ apply Rdiv_lt_0_compat; [|apply IZR_lt; lia].
  apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; [apply IZR_lt; lia | ..];
    apply bpow_gt_0. }
unfold rat_R. cbv zeta.
destruct (rat_neg x); [left | right]; split; [reflexivity | lra | reflexivity | lra].
Qed.

(** The sign of a nonzero [Rat] is [rat_neg]. *)
Lemma rat_R_sign :
  forall x, rat_ok x -> rat_num x <> 0%Z -> Rlt_bool (rat_R x) 0 = rat_neg x.
Proof.
intros x Hx H0.
destruct (rat_R_cases x Hx H0) as [(-> & H) | (-> & H)];
  [apply Rlt_bool_true | apply Rlt_bool_false]; lra.
Qed.

(** ** Constants *)

(** [f64::MIN] is [-(2^1024 - 2^971)], the least finite [f64]. *)
Lemma min_f64_val :
  is_finite min_f64 = true /\
  B2R min_f64 = - (bpow radix2 1024 - bpow radix2 (1024 - 53)).
Proof.
split; [vm_compute; reflexivity|].
rewrite <- SF2R_B2SF.
replace (B2SF min_f64) with (SpecFloat.S754_finite true 9007199254740991 971)
  by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]. unfold F2R. cbn [Fnum Fexp].
change (1024 - 53)%Z with 971%Z.
replace (bpow radix2 1024) with (bpow radix2 53 * bpow radix2 971)
  by (rewrite <- bpow_plus; reflexivity).
change (bpow radix2 53) with (IZR 9007199254740992). rewrite opp_IZR.
lra.
Qed.

(** [f64::from_bits(1)] is [2^-1074], the least positive [f64]. *)
Lemma from_bits_1_val :
  is_finite (from_bits 1) = true /\ B2R (from_bits 1) = bpow radix2 (-1074) /\
  Bsign (from_bits 1) = false.
Proof.
split; [vm_compute; reflexivity|]. split; [|vm_compute; reflexivity].
rewrite <- SF2R_B2SF.
replace (B2SF (from_bits 1)) with (SpecFloat.S754_finite false 1 (-1074))
  by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]. apply F2R_bpow.
Qed.

(** ** Rounding up as [rounds_up_to] says *)

(** [with_val] of a finite [f64] is a zero or the [MNum] of its value. *)
Lemma with_val_finite :
  forall w : f64, is_finite w = true -> B2R w <> 0 -> with_val w = MNum (B2R w).
Proof.
intros [s|s| |s m e B] Fw Hw; try discriminate Fw; [|reflexivity].
cbn [B2R] in Hw. contradiction.
Qed.

Lemma with_val_zero :
  forall w : f64, is_finite w = true -> B2R w = 0 -> exists s, with_val w = MZero s.
Proof.
intros [s|s| |s m e B] Fw Hw; try discriminate Fw; [exists s; reflexivity|].
exfalso. revert Hw. cbn [B2R]. apply F2R_neq_0. cbn [Fnum]. destruct s; discriminate.
Qed.

(** The negation of an [f64] is one. *)
Lemma f64_format_opp : forall y, f64_format y -> f64_format (- y).
Proof.
intros y (w & Fw & <-). exists (opp w). unfold opp.
rewrite is_finite_Bopp, B2R_Bopp. split; [exact Fw | reflexivity].
Qed.

(** What [rounds_up_to v r] makes [r]: [RU v] below [2^1024] in
    magnitude; +inf if [RU v >= 2^1024], which needs [v > 0]; or [-MAX] if
    [RU v <= -2^1024], so [v <= -2^1024] as [v <= RU v]. *)
Lemma rounds_up_to_cases :
  forall v r, v <> 0 -> rounds_up_to v r ->
  (is_finite r = true /\ B2R r = RU v /\ Rabs (RU v) < bpow radix2 1024) \/
  (bpow radix2 1024 <= RU v /\ r = B754_infinity false) \/
  (v <= - bpow radix2 1024 /\ r = min_f64).
Proof.
intros v r Hv H. unfold rounds_up_to in H.
destruct (Rlt_bool_spec (Rabs (RU v)) (bpow radix2 1024)) as [Hl|Hl].
- left. destruct H as (Rr & Fr & _). split; [exact Fr|]. split; [exact Rr | exact Hl].
- right.
  (* [RU] is monotone and [RU 0 = 0], so [RU v] has the sign of [v] or
     is 0. *)
  destruct (round_UP_pt radix2 fexp64 v) as (_ & Hge & _).
  destruct (Rdichotomy _ _ Hv) as [Hn|Hp].
  + right. rewrite (Rlt_bool_true _ _ Hn), <- (B2SF_overflow true) in H.
    assert (HU : RU v <= 0).
    { rewrite <- (round_0 radix2 fexp64 Zceil). apply round_le; [typeclasses eauto .. | lra]. }
    rewrite Rabs_left1 in Hl by exact HU.
    split; [lra | exact (B2SF_inj _ _ _ _ H)].
  + left. rewrite (Rlt_bool_false _ _ (Rlt_le _ _ Hp)), <- (B2SF_overflow false) in H.
    assert (HU : 0 <= RU v).
    { rewrite <- (round_0 radix2 fexp64 Zceil). apply round_le; [typeclasses eauto .. | lra]. }
    rewrite Rabs_pos_eq in Hl by exact HU.
    split; [exact Hl|]. apply B2SF_inj. rewrite H. vm_compute. reflexivity.
Qed.

(** [round_up_scaled] rounds up the nonzero real whose sign it is given and
    whose magnitude the [Scaled] describes. *)
Lemma round_up_scaled_correct :
  forall s v, v <> 0 -> scaled_ok s (Rabs v) ->
  exists r, round_up_scaled (Rlt_bool v 0) s = Some r /\ rounds_up_to v r.
Proof.
intros [| |q e sticky] v Hv Hs; cbn [round_up_scaled scaled_ok] in *.
- (* [|v| > 2^1024]: [|RU v| >= 2^1024], so it overflows. For [v < 0],
     [-2^1024] is a float at or above [v], so at or above [RU v]. *)
  eexists. split; [reflexivity|]. unfold rounds_up_to.
  destruct (round_UP_pt radix2 fexp64 v) as (_ & Hge & Hmin).
  pose proof (bpow_gt_0 radix2 1024) as Hb.
  rewrite Rlt_bool_false; [apply B2SF_overflow|].
  destruct (Rdichotomy _ _ Hv) as [Hn|Hp].
  + rewrite Rabs_left in Hs by exact Hn.
    assert (G : generic_format radix2 fexp64 (- bpow radix2 1024)).
    { apply generic_format_opp, generic_format_bpow. unfold FLT_exp. lia. }
    assert (Hle : v <= - bpow radix2 1024) by lra.
    pose proof (Hmin _ G Hle).
    rewrite Rabs_left1 by lra. lra.
  + rewrite Rabs_pos_eq in Hs by lra. rewrite Rabs_pos_eq by lra. lra.
- (* [0 < |v| < 2^-1074]: [v] is in the first binade of subnormals,
     [2^(ex - 1) <= |v| < 2^ex] with [ex <= -1074], where [RU] gives
     [2^-1074] above 0 and 0 below it, as [RD] of [-v] gives 0. *)
  destruct Hs as [H0 H1].
  destruct (mag radix2 v) as (ex, Hex). specialize (Hex Hv).
  assert (Hle : (ex <= -1074)%Z).
  { assert (Hlt : bpow radix2 (ex - 1) < bpow radix2 (-1074)) by lra.
    apply lt_bpow in Hlt. lia. }
  assert (Hf : (ex <= fexp64 ex)%Z) by (unfold FLT_exp; lia).
  destruct (Rdichotomy _ _ Hv) as [Hn|Hp].
  + rewrite (Rlt_bool_true _ _ Hn). eexists. split; [reflexivity|].
    assert (HU : RU v = 0).
    { rewrite Rabs_left in Hex by exact Hn.
      rewrite <- (Ropp_involutive v), round_UP_opp.
      rewrite (round_DN_small_pos radix2 fexp64 (- v) ex Hex Hf). apply Ropp_0. }
    unfold rounds_up_to.
    rewrite HU, Rabs_R0, Rlt_bool_true by apply bpow_gt_0.
    rewrite (Rlt_bool_true _ _ Hn). split; [reflexivity|]. split; reflexivity.
  + rewrite (Rlt_bool_false _ _ (Rlt_le _ _ Hp)). eexists. split; [reflexivity|].
    destruct from_bits_1_val as (F1 & R1 & S1).
    assert (HU : RU v = bpow radix2 (-1074)).
    { rewrite Rabs_pos_eq in Hex by lra.
      rewrite (round_UP_small_pos radix2 fexp64 v ex Hex Hf).
      f_equal. unfold FLT_exp. lia. }
    unfold rounds_up_to.
    rewrite HU, Rabs_pos_eq by apply bpow_ge_0.
    rewrite Rlt_bool_true by (apply bpow_lt; lia).
    rewrite (Rlt_bool_false _ _ (Rlt_le _ _ Hp)).
    split; [exact R1|]. split; [exact F1 | exact S1].
- (* [Mid] is what [round_up_exact] asks for. *)
  destruct Hs as (Hq & He & Hl).
  apply round_up_exact_correct.
  split; [lia|]. split; [exact He|]. split; [intros _; lia|].
  split; [reflexivity | exact Hl].
Qed.

(** [rounds_up_to] is the rounding toward +inf that [mpfr_round] says. *)
Lemma rounds_up_to_mpfr_round :
  forall v r, v <> 0 -> rounds_up_to v r -> mpfr_round f64_format RNDU v (with_val r).
Proof.
intros v r Hv H.
destruct (round_UP_pt radix2 fexp64 v) as (_ & Hge & Hmin).
destruct (rounds_up_to_cases v r Hv H) as [(Fr & Rr & _) | [(Hb & ->) | (Hb & ->)]].
- (* [RU v] is the least float at or above [v], and the [f64]s are
     floats. *)
  assert (Hup : Rnd_UP_pt f64_format v (B2R r)).
  { split; [exists r; split; [exact Fr | reflexivity]|]. rewrite Rr. split; [exact Hge|].
    intros g (w & Fw & <-) Hg. apply Hmin; [apply generic_format_B2R | exact Hg]. }
  destruct (Req_dec (B2R r) 0) as [E0|N0].
  + destruct (with_val_zero r Fr E0) as (s & ->). cbn [mpfr_round].
    rewrite <- E0. exact Hup.
  + rewrite (with_val_finite r Fr N0). cbn [mpfr_round]. split; [exact N0 | exact Hup].
- (* Every [f64] is below [2^1024 <= RU v], so below [v]. *)
  cbn [with_val mpfr_round]. intros g (w & Fw & <-).
  pose proof (abs_B2R_lt_emax _ _ w) as Hw. apply Rabs_lt_inv in Hw.
  apply Rnot_le_lt. intros Hle.
  pose proof (Hmin _ (generic_format_B2R _ _ w) Hle). lra.
- (* [-MAX] is at or above [v <= -2^1024], and is the least [f64]. *)
  destruct min_f64_val as (Fm & Rm).
  pose proof (bpow_gt_0 radix2 (1024 - 53)) as H0.
  assert (H1 : bpow radix2 (1024 - 53) < bpow radix2 1024) by (apply bpow_lt; lia).
  assert (Nm : B2R min_f64 <> 0) by (rewrite Rm; lra).
  rewrite (with_val_finite min_f64 Fm Nm). cbn [mpfr_round].
  split; [exact Nm|]. split; [exists min_f64; split; [exact Fm | reflexivity]|].
  split; [rewrite Rm; lra|].
  intros g (w & Fw & <-) _.
  pose proof (abs_B2R_le_emax_minus_prec _ _ _ w) as Hw. apply Rabs_le_inv in Hw.
  rewrite Rm. lra.
Qed.

(** [-w] is [v] rounded down if [w] is [-v] rounded up, as the [f64]s
    are symmetric. *)
Lemma mpfr_round_up_opp :
  forall v w, mpfr_round f64_format RNDU (- v) (with_val w) ->
  mpfr_round f64_format RNDD v (with_val (opp w)).
Proof.
intros v w H.
destruct (is_finite w) eqn:Fw.
- assert (Fo : is_finite (opp w) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fw).
  assert (Ro : B2R (opp w) = - B2R w) by apply B2R_Bopp.
  destruct (Req_dec (B2R w) 0) as [E0|N0].
  + destruct (with_val_zero w Fw E0) as (s & Es). rewrite Es in H. cbn [mpfr_round] in H.
    assert (E0' : B2R (opp w) = 0) by (rewrite Ro, E0; apply Ropp_0).
    destruct (with_val_zero _ Fo E0') as (s' & ->). cbn [mpfr_round].
    pose proof (Rnd_DN_pt_opp _ f64_format_opp _ _ H) as H'.
    rewrite Ropp_involutive, Ropp_0 in H'. exact H'.
  + rewrite (with_val_finite w Fw N0) in H. cbn [mpfr_round] in H. destruct H as (_ & H).
    assert (N0' : B2R (opp w) <> 0) by (rewrite Ro; lra).
    rewrite (with_val_finite _ Fo N0'). cbn [mpfr_round]. split; [exact N0'|].
    rewrite Ro. pose proof (Rnd_DN_pt_opp _ f64_format_opp _ _ H) as H'.
    rewrite Ropp_involutive in H'. exact H'.
- destruct w as [s|[|]| |s m e B]; try discriminate Fw;
    cbn [opp Bopp with_val mpfr_round negb] in *; try contradiction.
  intros g Fg. pose proof (H _ (f64_format_opp _ Fg)). lra.
Qed.

(** The negation of [-v] rounded up is [v] rounded down. *)
Lemma rounds_up_to_opp :
  forall v r, v <> 0 -> rounds_up_to (- v) r -> mpfr_round f64_format RNDD v (with_val (opp r)).
Proof.
intros v r Hv H. apply mpfr_round_up_opp.
apply rounds_up_to_mpfr_round; [lra | exact H].
Qed.

(** [x == y] is false for an infinity and a finite [f64]. *)
Lemma eq_inf_finite :
  forall s w, is_finite w = true ->
  eq (B754_infinity s) w = false /\ eq w (B754_infinity s) = false.
Proof.
intros [|] [t|t| |t m e B] Fw; try discriminate Fw; split; reflexivity.
Qed.

(** [v] rounded up and rounded down are equal exactly when [v] is a finite
    [f64]. *)
Lemma rounds_up_to_eq :
  forall v u d, v <> 0 -> rounds_up_to v u -> rounds_up_to (- v) d ->
  (eq u (opp d) = true <-> f64_format v).
Proof.
intros v u d Hv Hu Hd.
assert (Hv' : - v <> 0) by lra.
destruct (round_UP_pt radix2 fexp64 v) as (_ & Hge & _).
destruct (round_UP_pt radix2 fexp64 (- v)) as (_ & Hge' & _).
destruct min_f64_val as (Fm & _).
assert (Fom : is_finite (opp min_f64) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fm).
pose proof (bpow_gt_0 radix2 1024) as Hb.
split.
- intros H.
  destruct (rounds_up_to_cases v u Hv Hu) as [(Fu & Ru & Bu) | [(Bu & ->) | (Bu & ->)]];
    destruct (rounds_up_to_cases (- v) d Hv' Hd) as [(Fd & Rd & Bd) | [(Bd & ->) | (Bd & ->)]];
    try apply Rabs_lt_inv in Bu; try apply Rabs_lt_inv in Bd.
  + (* Both finite: [RU v = -RU (-v)], and [-RU (-v) <= v <= RU v], so [v]
       is [RU v], the value of [u]. *)
    assert (Fo : is_finite (opp d) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fd).
    unfold eq in H. rewrite Beqb_correct in H by assumption.
    unfold opp in H. rewrite B2R_Bopp, Ru, Rd in H.
    destruct (Req_bool_spec (RU v) (- RU (- v))) as [E|E]; [|discriminate H].
    exists u. split; [exact Fu|]. rewrite Ru. lra.
  + cbn [opp Bopp negb] in H. rewrite (proj2 (eq_inf_finite true u Fu)) in H. discriminate H.
  + lra.
  + assert (Fo : is_finite (opp d) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fd).
    rewrite (proj1 (eq_inf_finite false _ Fo)) in H. discriminate H.
  + discriminate H.
  + rewrite (proj1 (eq_inf_finite false _ Fom)) in H. discriminate H.
  + lra.
  + cbn [opp Bopp negb] in H. rewrite (proj2 (eq_inf_finite true _ Fm)) in H. discriminate H.
  + lra.
- (* A finite [f64] [v] is its own [RU], and so is [-v]. *)
  intros (w & Fw & Ew).
  pose proof (abs_B2R_lt_emax _ _ w) as Hw. rewrite Ew in Hw. apply Rabs_lt_inv in Hw.
  assert (Gv : generic_format radix2 fexp64 v) by (rewrite <- Ew; apply generic_format_B2R).
  assert (U : RU v = v) by (apply round_generic; [typeclasses eauto | exact Gv]).
  assert (U' : RU (- v) = - v)
    by (apply round_generic; [typeclasses eauto | apply generic_format_opp; exact Gv]).
  destruct (rounds_up_to_cases v u Hv Hu) as [(Fu & Ru & _) | [(Bu & _) | (Bu & _)]];
    [|lra..].
  destruct (rounds_up_to_cases (- v) d Hv' Hd) as [(Fd & Rd & _) | [(Bd & _) | (Bd & _)]];
    [|lra..].
  assert (Fo : is_finite (opp d) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fd).
  unfold eq. rewrite Beqb_correct by assumption.
  unfold opp. rewrite B2R_Bopp, Ru, Rd, U, U', Ropp_involutive.
  apply Req_bool_true. reflexivity.
Qed.

Theorem rational_to_f64_correct :
  forall x infsup, rat_ok x ->
  exists F, rational_to_f64 x infsup = Some F /\
  mpfr_round f64_format (as_rnd_t infsup) (rat_R x) (with_val (f64_f F)) /\
  (f64_inexact F = false <-> f64_format (rat_R x)) /\
  f64_overflow F = negb (is_finite (f64_f F)).
Proof.
intros x infsup Hx. unfold rational_to_f64.
rewrite NatOps.is_zero_z_correct by exact (proj1 (proj1 Hx)).
destruct (Z.eqb_spec (rat_num x) 0) as [E0|N0].
- (* A zero numerator gives the exact +0. *)
  eexists. split; [reflexivity|]. cbn [f64_f f64_inexact f64_overflow].
  assert (R0 : rat_R x = 0).
  { unfold rat_R. cbv zeta. rewrite E0. unfold Rdiv. rewrite !Rmult_0_l.
    destruct (rat_neg x); [apply Ropp_0 | reflexivity]. }
  rewrite R0.
  assert (F0 : f64_format 0) by (exists zero; split; reflexivity).
  split; [|split; [split; intros; [exact F0 | reflexivity] | reflexivity]].
  destruct infsup; cbn [as_rnd_t with_val zero mpfr_round];
    [apply Rnd_DN_pt_refl | apply Rnd_UP_pt_refl]; exact F0.
- (* [up] is [x] rounded up, and [down] is [-(-x)] rounded up, i.e. [x]
     rounded down. *)
  destruct (scale_correct x Hx N0) as (s & Hs & Hok).
  rewrite Hs. cbv beta iota zeta.
  pose proof (rat_R_sign x Hx N0) as Hsg.
  assert (Hv : rat_R x <> 0)
    by (destruct (rat_R_cases x Hx N0) as [(_ & H) | (_ & H)]; lra).
  set (v := rat_R x) in *.
  destruct (round_up_scaled_correct s v Hv Hok) as (u & Hu & Ru).
  rewrite Hsg in Hu. rewrite Hu.
  assert (Hv' : - v <> 0) by lra.
  assert (Hok' : scaled_ok s (Rabs (- v))) by (rewrite Rabs_Ropp; exact Hok).
  assert (Hsg' : Rlt_bool (- v) 0 = negb (rat_neg x)).
  { rewrite <- Hsg. destruct (Rdichotomy _ _ Hv) as [Hn|Hp].
    - rewrite (Rlt_bool_true _ _ Hn). apply Rlt_bool_false. lra.
    - rewrite (Rlt_bool_false v 0) by lra. apply Rlt_bool_true. lra. }
  destruct (round_up_scaled_correct s (- v) Hv' Hok') as (d & Hd & Rd).
  rewrite Hsg' in Hd. rewrite Hd.
  eexists. split; [reflexivity|]. cbn [f64_f f64_inexact f64_overflow].
  assert (R : mpfr_round f64_format (as_rnd_t infsup) v
                (with_val (match infsup with Inf => opp d | Sup => u end))).
  { destruct infsup; cbn [as_rnd_t].
    - exact (rounds_up_to_opp v d Hv Rd).
    - exact (rounds_up_to_mpfr_round v u Hv Ru). }
  split; [exact R|]. split.
  + rewrite Bool.negb_false_iff. exact (rounds_up_to_eq v u d Hv Ru Rd).
  + exact (round_overflow _ _ _ _ R).
Qed.

Theorem number_to_f64_correct :
  forall n infsup, number_ok n ->
  exists F, number_to_f64 n infsup = Some F /\
  number_round infsup n (f64_f F) /\
  (f64_inexact F = false <-> number_exact n) /\
  (f64_overflow F = true <-> (exists q, n = Rational q) /\ is_finite (f64_f F) = false).
Proof.
intros [|q|] infsup Hn; cbn [number_to_f64 number_round number_exact number_ok] in *.
- eexists. split; [reflexivity|]. cbn [f64_f f64_inexact f64_overflow].
  split; [reflexivity|]. split; [split; intros; [exact I | reflexivity]|].
  split; [discriminate | intros ((q & Hq) & _); discriminate Hq].
- destruct (rational_to_f64_correct q infsup Hn) as (F & E & R & I & O).
  exists F. rewrite E. split; [reflexivity|]. split; [exact R|]. split; [exact I|].
  rewrite O. destruct (is_finite (f64_f F)); cbn [negb].
  + split; [discriminate | intros (_ & H); discriminate H].
  + split; [intros _; split; [exists q; reflexivity | reflexivity] | intros _; reflexivity].
- eexists. split; [reflexivity|]. cbn [f64_f f64_inexact f64_overflow].
  split; [reflexivity|]. split; [split; intros; [exact I | reflexivity]|].
  split; [discriminate | intros ((q & Hq) & _); discriminate Hq].
Qed.

Theorem number_neg_correct :
  forall n r,
  (above_num (number_neg n) r <-> below_num n (- r)) /\
  (below_num (number_neg n) r <-> above_num n (- r)).
Proof.
intros [|q|] r; cbn [number_neg above_num below_num].
- split; split; intros H; first [exact I | contradiction].
- rewrite rat_R_neg. split; split; intros H; lra.
- split; split; intros H; first [exact I | contradiction].
Qed.
