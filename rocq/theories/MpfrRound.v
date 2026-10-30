(** * Two roundings in the same direction are one

    [mpfr_fn] rounds [f x] to an MPFR number of 53 bits and then that to an
    [f64], both in the same direction. Every finite [f64] is an MPFR number
    of 53 bits ([f64_mpfr_format]), so the result is [f x] rounded once to
    an [f64] in that direction ([mpfr_fn_round]): toward -inf, every finite
    [f64] at or below [f x] is an MPFR number at or below it, so at or below
    the first rounding, and so at or below the second. The lanes of an
    interval that such roundings give are then the least floats or +inf
    above the bounds ([round_up_lane], [round_dn_lane]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Mpfr Integer MaxMin AddSub Sign.

Open Scope R_scope.

(** Every finite [f64] is an MPFR number of 53 bits. *)
Lemma f64_mpfr_format :
  forall emin emax y, range_ok emin emax -> f64_format y -> mpfr_format emin emax y.
Proof.
intros emin emax y [Hmin Hmax] (w & Fw & <-).
destruct w as [s|s| |s mw ew Hw]; try discriminate Fw; [left; reflexivity|].
right. split.
- (* A float of [f64] has 53 bits of significand, whatever its exponent. *)
  apply generic_format_FLX_FLT with (emin := (-1074)%Z).
  exact (generic_format_B2R 53 1024 (B754_finite s mw ew Hw)).
- split.
  + (* A nonzero [f64] is at least [2^-1074] in magnitude, the least
       positive subnormal, and MPFR's [emin - 1] is at most [-1074]. *)
    apply Rle_trans with (bpow radix2 (-1074)).
    * apply bpow_le. lia.
    * exact (abs_B2R_ge_emin _ _ (B754_finite s mw ew Hw) eq_refl).
  + apply Rlt_le_trans with (bpow radix2 1024).
    * exact (abs_B2R_lt_emax _ _ _).
    * apply bpow_le. exact Hmax.
Qed.

(** Rounding in the direction [rnd] to [F], as a predicate on the
    result. *)
Definition rnd_pt (F : R -> Prop) (rnd : mpfr_rnd) (r y : R) : Prop :=
  match rnd with RNDD => Rnd_DN_pt F r y | RNDU => Rnd_UP_pt F r y end.

(** If [G] contains [F], and [y] is [r] rounded to [G], then [y] rounded
    to [F] in the same direction is [r] rounded to [F]: an element of [F]
    on the far side of [r] is an element of [G] there, so on the far side
    of [y] too. *)
Lemma round_compose :
  forall (F G : R -> Prop) rnd r y v, (forall g, F g -> G g) ->
  rnd_pt G rnd r y -> mpfr_round F rnd y v -> mpfr_round F rnd r v.
Proof.
intros F G [|] r y v HFG (Gy & Hy & Hmin) Hv;
  destruct v as [|[|]|s|z]; cbn [mpfr_round] in *; try contradiction.
- intros g Fg. apply Rnot_le_lt. intros Hg.
  pose proof (Hmin g (HFG g Fg) Hg). pose proof (Hv g Fg). lra.
- destruct Hv as (F0 & H0 & Hmin0).
  split; [exact F0|]. split; [lra|].
  intros g Fg Hg. apply Hmin0; [exact Fg|]. exact (Hmin g (HFG g Fg) Hg).
- destruct Hv as (Hz & Fz & Hzy & Hminz). split; [exact Hz|].
  split; [exact Fz|]. split; [lra|].
  intros g Fg Hg. apply Hminz; [exact Fg|]. exact (Hmin g (HFG g Fg) Hg).
- intros g Fg. apply Rnot_le_lt. intros Hg.
  pose proof (Hmin g (HFG g Fg) Hg). pose proof (Hv g Fg). lra.
- destruct Hv as (F0 & H0 & Hmin0).
  split; [exact F0|]. split; [lra|].
  intros g Fg Hg. apply Hmin0; [exact Fg|]. exact (Hmin g (HFG g Fg) Hg).
- destruct Hv as (Hz & Fz & Hzy & Hminz). split; [exact Hz|].
  split; [exact Fz|]. split; [lra|].
  intros g Fg Hg. apply Hminz; [exact Fg|]. exact (Hmin g (HFG g Fg) Hg).
Qed.

(** Rounding to a set [G] that contains [F]: an infinite result means
    that no element of [G], and so none of [F], is on the far side of
    [r]. *)
Lemma round_inf_sub :
  forall (F G : R -> Prop) rnd r s, (forall g, F g -> G g) ->
  mpfr_round G rnd r (MInf s) -> mpfr_round F rnd r (MInf s).
Proof.
intros F G [|] r [|] HFG H; cbn [mpfr_round] in *; try contradiction;
  intros g Fg; exact (H g (HFG g Fg)).
Qed.

(** Exact results: a zero, or an MPFR number other than 0. *)
Lemma mpfr_round_zero :
  forall F rnd s, F 0 -> mpfr_round F rnd 0 (MZero s).
Proof.
intros F [|] s F0; cbn [mpfr_round];
  (split; [exact F0|]; split; [apply Rle_refl | intros g _ Hg; exact Hg]).
Qed.

Lemma mpfr_round_exact :
  forall F rnd y, y <> 0 -> F y -> mpfr_round F rnd y (MNum y).
Proof.
intros F [|] y Hy Fy; cbn [mpfr_round]; (split; [exact Hy|]);
  (split; [exact Fy|]; split; [apply Rle_refl | intros g _ Hg; exact Hg]).
Qed.

(** Rounding to an MPFR number of 53 bits and then to an [f64], in the
    same direction, is rounding to an [f64] in that direction. *)
Lemma mpfr_fn_round :
  forall emin emax m rnd r v, range_ok emin emax -> get_d_ok emin emax m ->
  mpfr_round (mpfr_format emin emax) rnd r v ->
  mpfr_round f64_format rnd r (with_val (mpfr_get_d m rnd v)).
Proof.
intros emin emax m rnd r v Hr (Hnum & Hzero & Hinf) Hv.
assert (HFG : forall g, f64_format g -> mpfr_format emin emax g)
  by (intros g; apply f64_mpfr_format, Hr).
destruct v as [|s|s|y].
- destruct rnd; contradiction.
- (* An infinity converts to itself, and no finite [f64] is on the far
     side of [r] as no MPFR number is. *)
  rewrite Hinf. cbn [with_val]. exact (round_inf_sub _ _ _ _ _ HFG Hv).
- (* A zero converts to a zero, which is [r] rounded as [0] is an [f64]. *)
  destruct (Hzero rnd s) as (s' & ->). cbn [with_val].
  apply (round_compose _ _ rnd r 0 _ HFG).
  + destruct rnd; exact Hv.
  + apply mpfr_round_zero. exists zero. split; reflexivity.
- (* [y] is [r] rounded to an MPFR number, and [mpfr_get_d] rounds it to an
     [f64] in the same direction. *)
  assert (Hy : y <> 0 /\ rnd_pt (mpfr_format emin emax) rnd r y)
    by (destruct rnd; exact Hv).
  destruct Hy as (Hy0 & Hy).
  apply (round_compose _ _ rnd r y _ HFG Hy).
  apply Hnum; [exact Hy0|].
  destruct rnd; exact (proj1 Hy).
Qed.

(** [mpfr_fn] of a function that MPFR computes correctly rounds once. *)
Lemma mpfr_fn_correct :
  forall emin emax m D f g, range_ok emin emax -> get_d_ok emin emax m ->
  mpfr_correct emin emax D f g ->
  forall rnd x, is_finite x = true -> D (B2R x) ->
  mpfr_round f64_format rnd (f (B2R x)) (with_val (mpfr_fn m g rnd x)).
Proof.
intros emin emax m D f g Hr Hget Hg rnd x Fx Dx.
unfold mpfr_fn. apply (mpfr_fn_round emin emax); [exact Hr | exact Hget|].
exact (Hg rnd x Fx Dx).
Qed.

(** An infinity converts to itself. *)
Lemma mpfr_fn_inf :
  forall emin emax m g rnd s t, get_d_ok emin emax m -> g rnd (MInf s) = MInf t ->
  mpfr_fn m g rnd (B754_infinity s) = B754_infinity t.
Proof.
intros emin emax m g rnd s t (_ & _ & Hinf) Hg.
unfold mpfr_fn. cbn [with_val]. rewrite Hg. apply Hinf.
Qed.

(** A finite float [w] that is [r] rounded is so as a real. *)
Lemma round_finite_pt :
  forall F rnd r (w : f64), is_finite w = true ->
  mpfr_round F rnd r (with_val w) -> rnd_pt F rnd r (B2R w).
Proof.
intros F rnd r [s|s| |s mw ew Hw] Fw H; try discriminate Fw;
  destruct rnd; cbn [with_val mpfr_round rnd_pt] in *; first [exact H | exact (proj2 H)].
Qed.

(** The reals of finite floats are [f64_format]. *)
Lemma f64_format_B2R : forall z : f64, is_finite z = true -> f64_format (B2R z).
Proof.
intros z Fz. exists z. split; [exact Fz | reflexivity].
Qed.

(** A float rounded up from [r] is the least float or +inf at or above
    [r]. *)
Lemma round_up_lane :
  forall r w, mpfr_round f64_format RNDU r (with_val w) -> least_lane (Some r) w.
Proof.
intros r w H.
destruct (is_finite w) eqn:Fw.
- (* As in [least_lane_RU]: a finite [z] at or above [r] is an [f64] at or
     above [r], so at or above [r] rounded up. *)
  destruct (round_finite_pt _ _ _ _ Fw H) as (_ & Hge & Hmin).
  split; [left; exact Fw|]. rewrite (bound_finite _ Fw). split.
  + intros s Hs. cbn [below] in *. lra.
  + intros z [Fz| ->] Hz; [|intros s _; exact I].
    rewrite (bound_finite _ Fz) in *.
    assert (Hle : r <= B2R z) by exact (Hz _ (Rle_refl _)).
    pose proof (Hmin _ (f64_format_B2R z Fz) Hle).
    intros s Hs. cbn [below] in *. lra.
- (* +inf: no finite [f64] is at or above [r]. *)
  destruct w as [s|[|]| |s mw ew Hw]; try discriminate Fw;
    cbn [with_val mpfr_round] in H; try contradiction.
  split; [right; reflexivity|]. split; [intros s _; exact I|].
  intros z [Fz| ->] Hz; [|intros s _; exact I].
  rewrite (bound_finite _ Fz) in Hz.
  assert (Hle : r <= B2R z) by exact (Hz _ (Rle_refl _)).
  pose proof (H _ (f64_format_B2R z Fz)). lra.
Qed.

(** The negation of a float rounded down from [r] is the least float or
    +inf at or above [-r]. *)
Lemma round_dn_lane :
  forall r w, mpfr_round f64_format RNDD r (with_val w) ->
  least_lane (Some (- r)) (opp w).
Proof.
intros r w H.
destruct (is_finite w) eqn:Fw.
- (* As in [least_lane_RD]: [-z] for a finite [z] at or above [-r] is an
     [f64] at or below [r], so at or below [r] rounded down. *)
  destruct (round_finite_pt _ _ _ _ Fw H) as (_ & Hle & Hmax).
  assert (Fw' : is_finite (opp w) = true) by (rewrite is_finite_opp; exact Fw).
  split; [left; exact Fw'|]. rewrite (bound_finite _ Fw'), B2R_opp. split.
  + intros s Hs. cbn [below] in *. lra.
  + intros z [Fz| ->] Hz; [|intros s _; exact I].
    rewrite (bound_finite _ Fz) in *.
    assert (Hle' : - r <= B2R z) by exact (Hz _ (Rle_refl _)).
    assert (Hf : f64_format (- B2R z)).
    { exists (opp z). rewrite is_finite_opp, B2R_opp. split; [exact Fz | reflexivity]. }
    assert (Hzr : - B2R z <= r) by lra.
    pose proof (Hmax _ Hf Hzr).
    intros s Hs. cbn [below] in *. lra.
- (* -inf, whose negation is +inf: no finite [f64] is at or below [r]. *)
  destruct w as [s|[|]| |s mw ew Hw]; try discriminate Fw;
    cbn [with_val mpfr_round] in H; try contradiction.
  split; [right; reflexivity|]. split; [intros s _; exact I|].
  intros z [Fz| ->] Hz; [|intros s _; exact I].
  rewrite (bound_finite _ Fz) in Hz.
  assert (Hle : - r <= B2R z) by exact (Hz _ (Rle_refl _)).
  assert (Hf : f64_format (- B2R z)).
  { exists (opp z). rewrite is_finite_opp, B2R_opp. split; [exact Fz | reflexivity]. }
  pose proof (H _ Hf). lra.
Qed.

(** A float rounded down is never +inf, and one rounded up is never
    -inf. *)
Lemma round_dn_not_pinf :
  forall r w, mpfr_round f64_format RNDD r (with_val w) -> w <> B754_infinity false.
Proof.
intros r w H ->. exact H.
Qed.

Lemma round_up_not_ninf :
  forall r w, mpfr_round f64_format RNDU r (with_val w) -> w <> B754_infinity true.
Proof.
intros r w H ->. exact H.
Qed.

(** 0, 1 and -1 are MPFR numbers of 53 bits. *)
Lemma mpfr_format_0 : forall emin emax, mpfr_format emin emax 0.
Proof.
intros emin emax. left. reflexivity.
Qed.

Lemma mpfr_format_1 :
  forall emin emax, range_ok emin emax ->
  mpfr_format emin emax 1 /\ mpfr_format emin emax (-1).
Proof.
intros emin emax Hr. destruct one_B2R as [F1 E1].
split; apply (f64_mpfr_format _ _ _ Hr).
- exists one. split; [exact F1 | exact E1].
- exists (opp one). rewrite is_finite_opp, B2R_opp, E1. split; [exact F1 | reflexivity].
Qed.

(** [with_val] of a finite float other than 0 is its real. *)
Lemma with_val_finite :
  forall w, is_finite w = true -> B2R w <> 0 -> with_val w = MNum (B2R w).
Proof.
intros [s|s| |s mw ew Hw] Fw H0; try discriminate Fw; [|reflexivity].
destruct (H0 eq_refl).
Qed.

(** [with_val] of the float [1.0] and of [-1.0]. *)
Lemma with_val_one : with_val (of_u64 1) = MNum 1.
Proof.
destruct one_B2R as [F1 E1]. unfold one in F1, E1.
rewrite (with_val_finite _ F1) by lra. rewrite E1. reflexivity.
Qed.

Lemma with_val_m_one : with_val (opp (of_u64 1)) = MNum (-1).
Proof.
destruct one_B2R as [F1 E1]. unfold one in F1, E1.
assert (F1' : is_finite (opp (of_u64 1)) = true) by (rewrite is_finite_opp; exact F1).
rewrite (with_val_finite _ F1') by (rewrite B2R_opp; lra).
rewrite B2R_opp, E1. reflexivity.
Qed.
