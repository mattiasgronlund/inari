(** * The rounding tests of the fast paths for results of either sign

    [Fast.round_dir_signed] and [Fast.round_near_signed] of [Model.v]
    take an [h] of either sign with [1/2 < |h| < 2]: for [h < 0] they
    round [-y 2^e] from [-h] and [-l] with [Fast.round_dir] in the other
    direction, or [Fast.round_near], and negate the result. That is the
    rounding of [y 2^e], as rounding toward -inf is the negation of
    rounding toward +inf of the negation, and rounding to nearest is odd
    ([round_dir_signed_correct], [round_near_signed_correct]). The fast
    paths of [ln], [log2] and [log10] use both. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Encoding TwoSum DyDriver NearF64 NearCells FastRound.
From Inari Require RoundOpp.

Open Scope R_scope.

(** [lt h zero] as a comparison of reals, for a finite [h]. *)
Lemma lt_zero_R :
  forall h, is_finite h = true -> if lt h zero then B2R h < 0 else 0 <= B2R h.
Proof.
intros h Fh. unfold lt. rewrite Bltb_correct by easy.
change (B2R zero) with 0.
destruct (Rlt_bool_spec (B2R h) 0) as [H | H]; exact H.
Qed.

(** For [h < 0], [-h], [-l] and [-y] satisfy the hypotheses of
    [round_dir_correct] and [round_near_correct], as rounding to nearest
    is odd. *)
Lemma opp_pair :
  forall h l y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < Rabs (B2R h) < 2 -> B2R h < 0 ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  is_finite (opp h) = true /\ is_finite (opp l) = true /\
  B2R (opp h) = RN (B2R (opp h) + B2R (opp l)) /\ / 2 < B2R (opp h) < 2 /\
  Rabs (- y - (B2R (opp h) + B2R (opp l))) <= bpow radix2 (-68).
Proof.
intros h l y Fh Fl Hrn Hh Hn Hy. unfold opp.
rewrite !is_finite_Bopp, !B2R_Bopp.
rewrite Rabs_left in Hh by exact Hn.
split; [exact Fh |]. split; [exact Fl |].
split; [rewrite <- Ropp_plus_distr, round_NE_opp, <- Hrn; reflexivity |].
split; [lra |].
replace (- y - (- B2R h + - B2R l)) with (- (y - (B2R h + B2R l))) by ring.
rewrite Rabs_Ropp. exact Hy.
Qed.

(** If [|y - (h + l)| <= 2^-68], with [h] the rounding of [h + l] to
    nearest and [1/2 < |h| < 2], then where [round_dir_signed] returns,
    it returns [y 2^e] rounded toward +inf if [up] and toward -inf
    otherwise. *)
Theorem round_dir_signed_correct :
  forall h l e up v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < Rabs (B2R h) < 2 -> (-1021 <= e <= 1022)%Z ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  Fast.round_dir_signed h l e up = Some v ->
  rounds up (y * bpow radix2 e) v.
Proof.
intros h l e up v y Fh Fl Hrn Hh He Hy Hv.
unfold Fast.round_dir_signed in Hv.
pose proof (lt_zero_R h Fh) as Hs.
destruct (lt h zero).
- (* [h < 0]: [w] is [-y 2^e] rounded the other way, and [-w] is [y 2^e]
     rounded in the direction [up]. *)
  destruct (Fast.round_dir (opp h) (opp l) e (negb up)) as [w |] eqn:Hw; [| discriminate].
  injection Hv as <-.
  destruct (opp_pair h l y Fh Fl Hrn Hh Hs Hy) as (Fh' & Fl' & Hrn' & Hh' & Hy').
  pose proof (round_dir_correct _ _ e (negb up) w (- y) Fh' Fl' Hrn' Hh' He Hy' Hw) as R.
  unfold rounds in R |- *. apply RoundOpp.pown_rnd_opp.
  replace (- (y * bpow radix2 e)) with (- y * bpow radix2 e) by ring. exact R.
- rewrite Rabs_pos_eq in Hh by exact Hs.
  exact (round_dir_correct h l e up v y Fh Fl Hrn Hh He Hy Hv).
Qed.

(** The same for [round_near_signed] and rounding to nearest. *)
Theorem round_near_signed_correct :
  forall h l e v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < Rabs (B2R h) < 2 -> (-1021 <= e <= 1022)%Z ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  Fast.round_near_signed h l e = Some v ->
  near_round (y * bpow radix2 e) v.
Proof.
intros h l e v y Fh Fl Hrn Hh He Hy Hv.
unfold Fast.round_near_signed in Hv.
pose proof (lt_zero_R h Fh) as Hs.
destruct (lt h zero).
- (* [h < 0]: [w] is [-y 2^e] rounded to nearest, and [-w] is [y 2^e]
     rounded to nearest. *)
  destruct (Fast.round_near (opp h) (opp l) e) as [w |] eqn:Hw; [| discriminate].
  injection Hv as <-.
  destruct (opp_pair h l y Fh Fl Hrn Hh Hs Hy) as (Fh' & Fl' & Hrn' & Hh' & Hy').
  pose proof (round_near_correct _ _ e w (- y) Fh' Fl' Hrn' Hh' He Hy' Hw) as R.
  apply NearCells.near_opp in R.
  replace (- (- y * bpow radix2 e)) with (y * bpow radix2 e) in R by ring. exact R.
- rewrite Rabs_pos_eq in Hh by exact Hs.
  exact (round_near_correct h l e v y Fh Fl Hrn Hh He Hy Hv).
Qed.
