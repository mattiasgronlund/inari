(** * [rational_to_f64] and [number_to_f64] round a bound correctly

    Given [parse_ok], [rational_to_f64 m q infsup] is the rational [q]
    rounded toward -inf for [Inf] and toward +inf for [Sup] to an [f64],
    as [mpfr_round] with [f64_format] says, with [inexact] false exactly
    when [q] is a finite [f64], and [overflow] true exactly when the result
    is infinite. [number_to_f64] does the same for a [Rational], and
    returns the infinity itself, never inexact nor overflowed, for
    [NegInfinity] and [Infinity]. [number_neg_correct] shows that [-x] of a
    [Number] negates the reals that it bounds. *)

From Stdlib Require Import ZArith Reals Qreals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Mpfr MpfrRound ParseFormat.

Open Scope R_scope.

(** A bound [n] is exact: it is an infinity, or a rational that a finite
    [f64] holds. *)
Definition number_exact (n : Number) : Prop :=
  match n with Rational q => f64_format (Q2R q) | _ => True end.

(** [w] is the bound [n] rounded in the direction of [infsup]: an infinity
    is itself, and a rational is rounded as [mpfr_round] says. *)
Definition number_round (infsup : InfSup) (n : Number) (w : f64) : Prop :=
  match n with
  | NegInfinity => w = B754_infinity true
  | Rational q => mpfr_round f64_format (as_rnd_t infsup) (Q2R q) (with_val w)
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

(** [mpfr_get_d] of [r] rounded to [sub_format] at the range that
    [rational_to_f64] sets is [r] rounded to an [f64]: [sub_format] is
    [f64_format] there, a number other than 0 converts to [r] rounded as
    it is already an [f64], and a zero or an infinity converts to one. *)
Lemma get_d_round :
  forall m rnd r v, get_d_ok (-1073) 1024 m ->
  mpfr_round (sub_format (-1073) 1024) rnd r v ->
  mpfr_round f64_format rnd r (with_val (mpfr_get_d m rnd v)).
Proof.
intros m rnd r v (Hnum & Hzero & Hinf) Hv.
pose proof (mpfr_round_ext _ _ _ _ _ sub_format_f64 Hv) as Hf.
destruct v as [|s|s|y].
- destruct rnd; contradiction.
- rewrite Hinf. exact Hf.
- destruct (Hzero rnd s) as (s' & ->). destruct rnd; exact Hf.
- (* [y] is [r] rounded to an [f64], and an MPFR number of 53 bits, which
     [mpfr_get_d] rounds to an [f64] in the same direction. *)
  assert (Hy : y <> 0 /\ rnd_pt f64_format rnd r y) by (destruct rnd; exact Hf).
  assert (Sy : sub_format (-1073) 1024 y) by (destruct rnd; exact (proj1 (proj2 Hv))).
  destruct Hy as (Hy0 & Hy).
  apply (round_compose _ f64_format rnd r y _ (fun g Fg => Fg) Hy).
  apply Hnum; [exact Hy0 | exact (proj1 Sy)].
Qed.

(** The ternary value of a rounding [v] of [r] to [F] is 0 exactly when
    [r] is in [F]: a rounding of an element of [F] is that element, and
    an infinity means that no element of [F] is on its side of [r]. *)
Lemma ternary_exact :
  forall F rnd r v t, mpfr_round F rnd r v -> ternary_ok r v t -> (t = 0%Z <-> F r).
Proof.
intros F rnd r [|s|s|y] t H T.
- contradiction.
- split.
  + intros ->. destruct s; cbn in T; lia.
  + intros Fr. destruct rnd, s; cbn [mpfr_round] in H; try contradiction;
      specialize (H r Fr); lra.
- apply (iff_trans (proj2 T)). split.
  + intros ->. destruct rnd; exact (proj1 H).
  + intros Fr. symmetry. destruct rnd;
      [exact (Rnd_DN_pt_idempotent _ _ _ H Fr) | exact (Rnd_UP_pt_idempotent _ _ _ H Fr)].
- apply (iff_trans (proj2 T)). split.
  + intros <-. destruct rnd; exact (proj1 (proj2 H)).
  + intros Fr. destruct rnd;
      [exact (Rnd_DN_pt_idempotent _ _ _ (proj2 H) Fr)
      | exact (Rnd_UP_pt_idempotent _ _ _ (proj2 H) Fr)].
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

Theorem rational_to_f64_correct :
  forall m q infsup, parse_ok m ->
  mpfr_round f64_format (as_rnd_t infsup) (Q2R q)
    (with_val (f64_f (rational_to_f64 m q infsup))) /\
  (f64_inexact (rational_to_f64 m q infsup) = false <-> f64_format (Q2R q)) /\
  f64_overflow (rational_to_f64 m q infsup) =
    negb (is_finite (f64_f (rational_to_f64 m q infsup))).
Proof.
intros m q infsup (Hq & Hs & Hg).
unfold rational_to_f64. cbv zeta.
generalize (as_rnd_t infsup) as rnd. intros rnd.
(* [set_q] rounds [q] to an MPFR number, and [subnormalize] then rounds
   [q] itself to [sub_format], with the ternary value against [q]. *)
destruct (mpfr_set_q m (-1073)%Z 1024%Z rnd q) as [x t] eqn:E1.
pose proof (Hq rnd q) as [Rx Tx]. rewrite E1 in Rx, Tx. cbn [fst snd] in Rx, Tx.
destruct (mpfr_subnormalize m (-1073)%Z 1024%Z rnd x t) as [x' t'] eqn:E2.
pose proof (Hs rnd (Q2R q) x t Rx Tx) as [Rx' Tx'].
rewrite E2 in Rx', Tx'. cbn [fst snd] in Rx', Tx'.
cbn [f64_f f64_inexact f64_overflow].
pose proof (get_d_round m rnd (Q2R q) x' Hg Rx') as R1.
split; [exact R1|]. split.
- rewrite Bool.negb_false_iff, Z.eqb_eq.
  apply (ternary_exact f64_format rnd (Q2R q) x' t'); [|exact Tx'].
  exact (mpfr_round_ext _ _ _ _ _ sub_format_f64 Rx').
- exact (round_overflow _ _ _ _ R1).
Qed.

Theorem number_to_f64_correct :
  forall m n infsup, parse_ok m ->
  number_round infsup n (f64_f (number_to_f64 m n infsup)) /\
  (f64_inexact (number_to_f64 m n infsup) = false <-> number_exact n) /\
  (f64_overflow (number_to_f64 m n infsup) = true <->
   (exists q, n = Rational q) /\ is_finite (f64_f (number_to_f64 m n infsup)) = false).
Proof.
intros m [|q|] infsup Hm;
  cbn [number_to_f64 number_round number_exact f64_f f64_inexact f64_overflow].
- split; [reflexivity|]. split; [split; intros; [exact I | reflexivity]|].
  split; [discriminate | intros ((q & Hq) & _); discriminate Hq].
- destruct (rational_to_f64_correct m q infsup Hm) as (R & I & O).
  split; [exact R|]. split; [exact I|].
  rewrite O. destruct (is_finite (f64_f (rational_to_f64 m q infsup))); cbn [negb].
  + split; [discriminate | intros (_ & H); discriminate H].
  + split; [intros _; split; [exists q; reflexivity | reflexivity] | intros _; reflexivity].
- split; [reflexivity|]. split; [split; intros; [exact I | reflexivity]|].
  split; [discriminate | intros ((q & Hq) & _); discriminate Hq].
Qed.

Theorem number_neg_correct :
  forall n r,
  (above_num (number_neg n) r <-> below_num n (- r)) /\
  (below_num (number_neg n) r <-> above_num n (- r)).
Proof.
intros [|q|] r; cbn [number_neg above_num below_num].
- split; split; intros H; first [exact I | contradiction].
- rewrite Q2R_opp. split; split; intros H; lra.
- split; split; intros H; first [exact I | contradiction].
Qed.
