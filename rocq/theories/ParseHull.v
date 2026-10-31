(** * The bounds that [number_to_f64] computes make the tightest interval

    For an [NInterval] [x] that the grammar can return ([ninterval_ok]),
    [Interval::try_from] of the bounds of [x] rounded down and up, or the
    empty interval where it fails, is the tightest interval that contains
    the reals that [x] denotes.

    [NInterval::EMPTY] has the lower bound [Infinity], which converts to
    +inf, so [try_from] fails and gives the empty interval, which is the
    tightest as [x] denotes no real. Otherwise the reals of [x] are those
    between its bounds, and there is one ([ninterval_ok_set]). A lower bound
    [NegInfinity] converts to -inf, whose negation +inf is the least lane
    above the negations of the reals of [x], as they have no upper bound,
    and a [Rational] lower bound [q] is the least real of [x], so [-q] is
    the largest negation, and the negation of [q] rounded down is the least
    float or +inf at or above it ([round_dn_lane]). The upper bound is the
    same without the negations ([round_up_lane]). So [[-a; b]] for the
    converted bounds [a] and [b] is the tightest interval
    ([tightest_lanes_lub]), and in particular [valid], which, as [b] is
    not NaN, is the test of [try_from] on [a] and [b]. *)

From Stdlib Require Import ZArith Reals Qreals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Mpfr MpfrRound ParseRound AddSub MulTight DivTight.

Open Scope R_scope.

(** The bounds of an [NInterval] that the grammar can return, other than
    [NInterval::EMPTY]. *)
Lemma ninterval_ok_bounds :
  forall x, ninterval_ok x -> nis_empty x = false ->
  number_le (ninf x) (nsup x) /\ ninf x <> Infinity /\ nsup x <> NegInfinity.
Proof.
intros x [He|H] Hne; [rewrite He in Hne; discriminate Hne | exact H].
Qed.

Lemma ninterval_ok_set :
  forall x, ninterval_ok x -> nis_empty x = false -> exists r, ninterval_set x r.
Proof.
intros x Hx Hne. destruct (ninterval_ok_bounds x Hx Hne) as (Hle & Ha & Hb).
unfold ninterval_set.
(* The lower bound if it is a [Rational], else the upper bound if it is
   one, else 0. *)
destruct (ninf x) as [|p|]; destruct (nsup x) as [|q|];
  cbn [number_le] in Hle; try contradiction; try congruence;
  cbn [above_num below_num].
- exists (Q2R q). split; [exact I | apply Rle_refl].
- exists 0. split; exact I.
- exists (Q2R p). split; [apply Rle_refl | apply Qle_Rle, Hle].
- exists (Q2R p). split; [apply Rle_refl | exact I].
Qed.

(** The lane of the lower bound: the negation of the lower bound rounded
    down is the least float or +inf at or above the least upper bound of
    the negations of the reals of [x]. *)
Lemma lower_lane :
  forall x a, ninterval_ok x -> nis_empty x = false ->
  number_round Inf (ninf x) a -> lane_ok (fun s => ninterval_set x (- s)) (opp a).
Proof.
intros x a Hx Hne Ha. destruct (ninterval_ok_bounds x Hx Hne) as (Hle & Hi & Hs).
unfold ninterval_set.
destruct (ninf x) as [|p|]; cbn [number_round as_rnd_t] in Ha; [| |congruence].
- (* -inf, whose negation is +inf: the negations of the reals of [x] are
     all the reals at or above that of the upper bound. *)
  subst a. change (opp (B754_infinity true)) with (B754_infinity false : f64).
  apply lane_ok_inf. intros t.
  destruct (nsup x) as [|q|]; [congruence| |].
  + exists (Rmax t (- Q2R q)). cbn [above_num below_num].
    pose proof (Rmax_r t (- Q2R q)).
    split; [split; [exact I | lra] | apply Rmax_l].
  + exists t. split; [split; exact I | apply Rle_refl].
- (* [-p] is the largest negation, as [p] is in [x]. *)
  exists (Some (- Q2R p)). split; [|exact (round_dn_lane _ _ Ha)].
  apply tight_lub, tight_Some. cbv beta. rewrite Ropp_involutive. split.
  + split; [cbn [above_num]; apply Rle_refl|].
    destruct (nsup x) as [|q|]; cbn [number_le below_num] in *;
      [congruence | apply Qle_Rle, Hle | exact I].
  + intros r [Hr _]. cbn [above_num] in Hr. lra.
Qed.

(** The lane of the upper bound: the upper bound rounded up is the least
    float or +inf at or above the least upper bound of the reals of
    [x]. *)
Lemma upper_lane :
  forall x b, ninterval_ok x -> nis_empty x = false ->
  number_round Sup (nsup x) b -> lane_ok (ninterval_set x) b.
Proof.
intros x b Hx Hne Hb. destruct (ninterval_ok_bounds x Hx Hne) as (Hle & Hi & Hs).
unfold ninterval_set.
destruct (nsup x) as [|q|]; cbn [number_round as_rnd_t] in Hb; [congruence| |].
- (* [q] is the largest real of [x]. *)
  exists (Some (Q2R q)). split; [|exact (round_up_lane _ _ Hb)].
  apply tight_lub, tight_Some. cbv beta. split.
  + split; [|cbn [below_num]; apply Rle_refl].
    destruct (ninf x) as [|p|]; cbn [number_le above_num] in *;
      [exact I | apply Qle_Rle, Hle | congruence].
  + intros r [_ Hr]. exact Hr.
- (* +inf: the reals of [x] are all the reals at or above the lower
     bound. *)
  subst b. apply lane_ok_inf. intros t.
  destruct (ninf x) as [|p|]; [| |congruence].
  + exists t. split; [split; exact I | apply Rle_refl].
  + exists (Rmax t (Q2R p)). cbn [above_num below_num].
    split; [split; [apply Rmax_r | exact I] | apply Rmax_l].
Qed.

(** A bound converts to a float that is not NaN: an infinity, or a
    rounding, which [mpfr_round] never makes NaN. *)
Lemma number_round_not_nan :
  forall infsup n w, number_round infsup n w -> is_nan w = false.
Proof.
intros infsup [|q|] w H; cbn [number_round] in H; try (subst w; reflexivity).
destruct w; try reflexivity.
destruct infsup; cbn [with_val as_rnd_t mpfr_round] in H; contradiction.
Qed.

(** [w == inf] is false for a float [w] other than that infinity. *)
Lemma eq_inf_false :
  forall (w : f64) s, w <> B754_infinity s -> eq w (B754_infinity s) = false.
Proof.
intros [sw|sw| |sw mw ew Hw] s H; destruct s; try destruct sw; try reflexivity;
  exfalso; apply H; reflexivity.
Qed.

Theorem bounds_tightest :
  forall m x, parse_ok m -> ninterval_ok x ->
  is_tightest (ninterval_set x)
    (match Interval.try_from (f64_f (number_to_f64 m (ninf x) Inf))
                             (f64_f (number_to_f64 m (nsup x) Sup)) with
     | Some y => y
     | None => Interval.EMPTY
     end).
Proof.
intros m x Hm Hx.
destruct (nis_empty x) eqn:He.
- (* [NInterval::EMPTY]: the lower bound +inf makes [try_from] fail, and
     no real is in [x]. *)
  destruct x as [[|p|] [|q|]|a]; cbn [nis_empty] in He; try discriminate He.
  cbn [ninf nsup number_to_f64 f64_f].
  assert (E : Interval.try_from (B754_infinity false) (B754_infinity true) = None)
    by reflexivity.
  rewrite E. apply tightest_empty. intros u [Hu _]. exact Hu.
- pose proof (proj1 (number_to_f64_correct m (ninf x) Inf Hm)) as Ra.
  pose proof (proj1 (number_to_f64_correct m (nsup x) Sup Hm)) as Rb.
  set (a := f64_f (number_to_f64 m (ninf x) Inf)) in *.
  set (b := f64_f (number_to_f64 m (nsup x) Sup)) in *.
  clearbody a b.
  assert (T : is_tightest (ninterval_set x) {| rep := (opp a, b) |}).
  { apply tightest_lanes_lub.
    - exact (ninterval_ok_set x Hx He).
    - exact (lower_lane x a Hx He Ra).
    - exact (upper_lane x b Hx He Rb). }
  (* [try_from] accepts [a] and [b]: its test is that [[-a; b]] is
     [valid], with [b] not NaN. *)
  assert (E : Interval.try_from a b = Some {| rep := (opp a, b) |}).
  { destruct T as [V _]. cbn [valid rep] in V.
    unfold opp in V. rewrite Bopp_involutive in V.
    destruct V as [[_ Nb] | (Hab & Ha & Hb)].
    { rewrite (number_round_not_nan _ _ _ Rb) in Nb. discriminate Nb. }
    unfold Interval.try_from, le.
    rewrite Hab, (eq_inf_false a false Ha), (eq_inf_false b true Hb).
    reflexivity. }
  rewrite E. exact T.
Qed.
