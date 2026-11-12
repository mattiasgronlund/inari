(** * The multiples of π that atan and atan2 return from constants

    [pi_times] and [pi_times_near] of [DyadicAtan] in [Model.v] take
    [c π] for [|c|] = 1/4, 1/2, 3/4 and 1 from the bit patterns that
    [pi_bounds] gives. [pi_bounds_correct] shows that each pair is two
    adjacent positive [f64]s with [k π] strictly between them, closer to
    the first: [vm_compute] decodes the bits and checks that the second
    is [Bsucc] of the first, and [PiBounds.PI_Q] bounds π. So the pair
    with the sign of [c] is [c π] rounded toward -∞ and +∞
    ([pi_const_rounds], with [PiTight.pt_succ_le] for the gap and
    [DyDriver.finite_mpfr_round]), and the first with the sign of [c] is
    [c π] rounded to nearest ([pi_const_near], by [NearCells.near_x]). *)

From Stdlib Require Import ZArith Reals Lra Lia QArith.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr MpfrRound DyDriver NearF64 NearCells.
From Inari Require PiBounds PiTight.

Open Scope Z_scope.

(** ** Helpers *)

(** A float whose [B2SF] is a positive finite [m 2^e] has the real
    [m 2^e]. *)
Local Lemma pc_bits :
  forall (x : f64) m e, B2SF x = SpecFloat.S754_finite false m e ->
  B2R x = (IZR (Zpos m) * bpow radix2 e)%R.
Proof.
intros x m e H. rewrite <- SF2R_B2SF, H. reflexivity.
Qed.

(** [eq] of two finite floats is the equality of their reals
    ([Beqb_correct]). *)
Local Lemma pc_eq :
  forall k x : f64, is_finite k = true -> is_finite x = true -> eq k x = true -> B2R k = B2R x.
Proof.
intros k x Fk Fx E. unfold eq in E. rewrite Beqb_correct in E by assumption.
destruct (Req_bool_spec (B2R k) (B2R x)) as [H|H]; [exact H | discriminate E].
Qed.

(** The sign bit of a float bounds its real, as [DyAtan.atn_sign_true]
    and [DyAtan.atn_sign_false] have it ([DyAtan.v] imports this file). *)
Local Lemma pc_sign_true : forall x : f64, Bsign x = true -> (B2R x <= 0)%R.
Proof.
intros [s|s| |s m e H] Hs; cbn [B2R]; try apply Rle_refl.
cbn [Bsign] in Hs. subst s.
apply F2R_le_0. cbn [Fnum SpecFloat.cond_Zopp]. lia.
Qed.

Local Lemma pc_sign_false : forall x : f64, Bsign x = false -> (0 <= B2R x)%R.
Proof.
intros [s|s| |s m e H] Hs; cbn [B2R]; try apply Rle_refl.
cbn [Bsign] in Hs. subst s.
apply F2R_ge_0. cbn [Fnum SpecFloat.cond_Zopp]. lia.
Qed.

(** One pair of [pi_bounds_correct], from its decoded bits: [lo] and
    [hi] are [mlo 2^e] and [mhi 2^e], and the bounds on [q π] are stated
    on these reals. *)
Local Lemma pc_case :
  forall (k : f64) (lo hi : Z) (q : R) (mlo mhi : positive) (e : Z),
  B2R k = q ->
  is_finite (from_bits lo) = true -> is_finite (from_bits hi) = true ->
  Bsign (from_bits lo) = false -> Bsign (from_bits hi) = false ->
  Bsucc (from_bits lo) = from_bits hi ->
  B2SF (from_bits lo) = SpecFloat.S754_finite false mlo e ->
  B2SF (from_bits hi) = SpecFloat.S754_finite false mhi e ->
  (IZR (Zpos mlo) * bpow radix2 e < q * PI < IZR (Zpos mhi) * bpow radix2 e)%R ->
  (q * PI - IZR (Zpos mlo) * bpow radix2 e
     <= IZR (Zpos mlo) * bpow radix2 e * bpow radix2 (-54))%R ->
  is_finite (from_bits lo) = true /\ is_finite (from_bits hi) = true /\
  Bsign (from_bits lo) = false /\ Bsign (from_bits hi) = false /\
  Bsucc (from_bits lo) = from_bits hi /\
  (B2R (from_bits lo) < B2R k * PI < B2R (from_bits hi))%R /\
  (B2R k * PI - B2R (from_bits lo) <= B2R (from_bits lo) * bpow radix2 (-54))%R.
Proof.
intros k lo hi q mlo mhi e Hk F1 F2 S1 S2 Hs Dlo Dhi Hb He.
rewrite Hk, (pc_bits _ _ _ Dlo), (pc_bits _ _ _ Dhi).
exact (conj F1 (conj F2 (conj S1 (conj S2 (conj Hs (conj Hb He)))))).
Qed.

(** The arithmetic goals of [pc_case]: π to 18 decimals ([PI_Q]), and
    [cbn] turns each [bpow radix2 n] into a fraction that [lra]
    evaluates. *)
Local Ltac pc_arith :=
  destruct PiBounds.PI_Q as [P1 P2];
  unfold Q2R, PiBounds.pi_lo, PiBounds.pi_hi in P1, P2;
  cbn [QArith_base.Qnum QArith_base.Qden] in P1, P2;
  cbn [bpow radix_val radix2];
  lra.

(** The goals of [pc_case] that [vm_compute] decides: finiteness, signs,
    [Bsucc] (compared through [B2SF], as [PiTight.pt_PI_facts] does) and
    the decoded bits. *)
Local Ltac pc_bits_goals :=
  first [ apply B2SF_inj; vm_compute; reflexivity | vm_compute; reflexivity ].

(** ** The constants *)

(** [pi_bounds k], for a finite [k], gives two adjacent positive [f64]s
    with [k π] strictly between them, within [lo 2^-54] of the first. *)
Lemma pi_bounds_correct :
  forall k lo hi, is_finite k = true -> DyadicAtan.pi_bounds k = Some (lo, hi) ->
  is_finite (from_bits lo) = true /\ is_finite (from_bits hi) = true /\
  Bsign (from_bits lo) = false /\ Bsign (from_bits hi) = false /\
  Bsucc (from_bits lo) = from_bits hi /\
  (B2R (from_bits lo) < B2R k * PI < B2R (from_bits hi))%R /\
  (B2R k * PI - B2R (from_bits lo) <= B2R (from_bits lo) * bpow radix2 (-54))%R.
Proof.
intros k lo hi Fk.
unfold DyadicAtan.pi_bounds.
(* Each test [eq k x] that passes makes [B2R k] the real of the literal
   [x] ([pc_eq]), which [pc_bits] decodes. *)
destruct (eq k DyadicAtan.quarter) eqn:E1; intros H.
{ unfold DyadicAtan.PI_QUARTER in H. injection H as <- <-.
  assert (Hk : B2R k = (1 / 4)%R).
  { rewrite (pc_eq k DyadicAtan.quarter Fk ltac:(vm_compute; reflexivity) E1).
    rewrite (pc_bits _ 4503599627370496 (-54)) by (vm_compute; reflexivity).
    cbn [bpow radix_val radix2]. lra. }
  (* π/4 is [7074237752028440 2^-53] plus 0.276 of an ulp. *)
  apply (pc_case k _ _ (1 / 4) 7074237752028440 7074237752028441 (-53) Hk);
    [pc_bits_goals .. | pc_arith | pc_arith]. }
revert H.
destruct (eq k DyadicLog.half) eqn:E2; intros H.
{ unfold DyadicAtan.PI_HALF in H. injection H as <- <-.
  assert (Hk : B2R k = (1 / 2)%R).
  { rewrite (pc_eq k DyadicLog.half Fk ltac:(vm_compute; reflexivity) E2).
    rewrite (pc_bits _ 4503599627370496 (-53)) by (vm_compute; reflexivity).
    cbn [bpow radix_val radix2]. lra. }
  (* π/2 is [7074237752028440 2^-52] plus 0.276 of an ulp. *)
  apply (pc_case k _ _ (1 / 2) 7074237752028440 7074237752028441 (-52) Hk);
    [pc_bits_goals .. | pc_arith | pc_arith]. }
revert H.
destruct (eq k DyadicAtan.three_quarters) eqn:E3; intros H.
{ unfold DyadicAtan.PI_THREE_QUARTERS in H. injection H as <- <-.
  assert (Hk : B2R k = (3 / 4)%R).
  { rewrite (pc_eq k DyadicAtan.three_quarters Fk ltac:(vm_compute; reflexivity) E3).
    rewrite (pc_bits _ 6755399441055744 (-53)) by (vm_compute; reflexivity).
    cbn [bpow radix_val radix2]. lra. }
  (* 3π/4 is [5305678314021330 2^-51] plus 0.207 of an ulp. *)
  apply (pc_case k _ _ (3 / 4) 5305678314021330 5305678314021331 (-51) Hk);
    [pc_bits_goals .. | pc_arith | pc_arith]. }
revert H.
destruct (eq k DyadicExp.one) eqn:E4; intros H; [|discriminate H].
unfold DyadicAtan.PI_ONE in H. injection H as <- <-.
assert (Hk : B2R k = 1%R).
{ rewrite (pc_eq k DyadicExp.one Fk ltac:(vm_compute; reflexivity) E4).
  rewrite (pc_bits _ 4503599627370496 (-52)) by (vm_compute; reflexivity).
  cbn [bpow radix_val radix2]. lra. }
(* π is [7074237752028440 2^-51] plus 0.276 of an ulp. *)
apply (pc_case k _ _ 1 7074237752028440 7074237752028441 (-51) Hk);
  [pc_bits_goals .. | pc_arith | pc_arith].
Qed.

(** No [f64] lies strictly between [lo] and its successor [hi], nor
    between their negations, as [DyAtan.atn_pi2_gap] has it for
    [FRAC_PI_2]. *)
Local Lemma pc_gap :
  forall lo hi : f64, is_finite lo = true -> is_finite hi = true -> Bsucc lo = hi ->
  forall g, f64_format g ->
  (g <= B2R lo \/ B2R hi <= g)%R /\ (g <= - B2R hi \/ - B2R lo <= g)%R.
Proof.
intros lo hi Flo Fhi Hs g (w & Fw & <-). rewrite <- Hs in Fhi |- *.
split.
- destruct (Rle_or_lt (B2R w) (B2R lo)) as [L|L]; [left; exact L|].
  right. exact (PiTight.pt_succ_le _ w Flo Fhi L).
- destruct (Rle_or_lt (B2R (Bopp w)) (B2R lo)) as [L|L].
  + right. rewrite B2R_Bopp in L. lra.
  + left. pose proof (PiTight.pt_succ_le _ (Bopp w) Flo Fhi L) as P.
    rewrite B2R_Bopp in P. lra.
Qed.

(** The constant that [pi_times_with] returns for [c] is [c π] rounded
    toward +∞ if [up] and toward -∞ if not. *)
Lemma pi_const_rounds :
  forall c up lo hi, is_finite c = true -> DyadicAtan.pi_bounds (fabs c) = Some (lo, hi) ->
  rounds up (B2R c * PI)%R
    (copysign (from_bits (if Bool.eqb up (negb (Bsign c)) then hi else lo)) c).
Proof.
intros c up lo hi Fc Hb.
assert (Fk : is_finite (fabs c) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fc).
destruct (pi_bounds_correct _ _ _ Fk Hb) as (Flo & Fhi & Slo & Shi & Hs & (H1 & H2) & _).
unfold fabs in H1, H2. rewrite B2R_Babs in H1, H2.
pose proof (pc_gap _ _ Flo Fhi Hs) as G.
assert (Fol : is_finite (opp (from_bits lo)) = true)
  by (unfold opp; rewrite is_finite_Bopp; exact Flo).
assert (Foh : is_finite (opp (from_bits hi)) = true)
  by (unfold opp; rewrite is_finite_Bopp; exact Fhi).
unfold rounds, copysign.
(* For [c >= 0], [c π] lies between [lo] and [hi]; for [c <= 0], between
   [-hi] and [-lo]. Each direction takes the bound on its side, and
   [pc_gap] shows that no float lies between it and [c π]. *)
destruct (Bsign c) eqn:Sc.
- pose proof (pc_sign_true c Sc) as Cn. rewrite Rabs_left1 in H1, H2 by exact Cn.
  destruct up; cbn [Bool.eqb negb]; rewrite ?Slo, ?Shi; cbn [Bool.eqb]; unfold opp in *;
    apply finite_mpfr_round; try assumption; cbn [MpfrRound.rnd_pt].
  + split; [exact (f64_format_B2R _ Fol)|]. rewrite B2R_Bopp. split; [lra|].
    intros g Fg Hg. destruct (proj2 (G g Fg)); lra.
  + split; [exact (f64_format_B2R _ Foh)|]. rewrite B2R_Bopp. split; [lra|].
    intros g Fg Hg. destruct (proj2 (G g Fg)); lra.
- pose proof (pc_sign_false c Sc) as Cp. rewrite Rabs_pos_eq in H1, H2 by exact Cp.
  destruct up; cbn [Bool.eqb negb]; rewrite ?Slo, ?Shi; cbn [Bool.eqb];
    apply finite_mpfr_round; try assumption; cbn [MpfrRound.rnd_pt].
  + split; [exact (f64_format_B2R _ Fhi)|]. split; [lra|].
    intros g Fg Hg. destruct (proj1 (G g Fg)); lra.
  + split; [exact (f64_format_B2R _ Flo)|]. split; [lra|].
    intros g Fg Hg. destruct (proj1 (G g Fg)); lra.
Qed.

(** The constant that [pi_times_near_with] returns for [c] is [c π]
    rounded to nearest. *)
Lemma pi_const_near :
  forall c lo hi, is_finite c = true -> DyadicAtan.pi_bounds (fabs c) = Some (lo, hi) ->
  near_round (B2R c * PI)%R (copysign (from_bits lo) c).
Proof.
intros c lo hi Fc Hb.
assert (Fk : is_finite (fabs c) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fc).
destruct (pi_bounds_correct _ _ _ Fk Hb) as (Flo & _ & Slo & _ & _ & (H1 & _) & H3).
unfold fabs in H1, H3. rewrite B2R_Babs in H1, H3.
assert (E : bpow radix2 (-54) = (1 / 18014398509481984)%R)
  by (cbn [bpow radix_val radix2]; lra).
rewrite E in H3.
(* [lo] is positive, as [lo < |c| π <= lo (1 + 2^-54)]. *)
assert (Lp : (0 < B2R (from_bits lo))%R) by lra.
unfold copysign. rewrite Slo.
(* [near_x]: [c π] is within [|c π - ±lo| <= lo 2^-54] of [±lo]. *)
destruct (Bsign c) eqn:Sc; cbn [Bool.eqb].
- pose proof (pc_sign_true c Sc) as Cn. rewrite Rabs_left1 in H1, H3 by exact Cn.
  unfold opp. apply near_x.
  + rewrite is_finite_Bopp. exact Flo.
  + rewrite B2R_Bopp. lra.
  + rewrite B2R_Bopp, Rabs_Ropp, (Rabs_pos_eq (B2R (from_bits lo))) by lra.
    rewrite E. apply Rabs_le. lra.
- pose proof (pc_sign_false c Sc) as Cq. rewrite Rabs_pos_eq in H1, H3 by exact Cq.
  apply near_x.
  + exact Flo.
  + lra.
  + rewrite (Rabs_pos_eq (B2R (from_bits lo))) by lra.
    rewrite E. apply Rabs_le. lra.
Qed.
