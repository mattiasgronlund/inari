(** * One lane of [x * y] of intervals, rounded up

    Outside the classes [E] and [Z], each lane of [x * y] is the product of
    two lanes rounded up, or [max1] of two such products. These lemmas show
    that each gives the least float or +inf at or above the upper bound
    that the lane stands for ([least_lane]), for [Mul.v] to combine.

    [mul_lane_finite] follows [add_lane] in [AddSub.v], with
    [Bmult_correct] in place of [Bplus_correct]. If the product rounded up
    does not overflow, [Bmult mode_UP] gives it, and a float at or above
    the product is at or above it rounded up. If it overflows, [Bmult]
    gives [binary_overflow] with the sign [xorb] of the signs of the lanes,
    and the signs of the lanes give that of the product: it is at most 0
    if the signs differ, and at least 0 if they agree. So a product that
    overflows below is at or below [-2^1024], and the result [-f64::MAX] is
    at or below every float, and one that overflows above rounds up to at
    least [2^1024]. A float at or above the product would be at or above it
    rounded up, so no float is, and the result is +inf.

    [mul_lane_pos] is the same for two lanes above 0, where the product of
    the upper bounds is [None] if either lane is +inf ([umult]). Two finite
    lanes are [mul_lane_finite], and +inf times +inf or a positive float
    is +inf, the least float or +inf at or above [None].

    [max_least_lane] needs no float reasoning: [max1] of two lanes has the
    bound [umax] of their bounds ([max1_bound]), and a real is below
    [umax] of two bounds exactly when it is below one of them
    ([below_umax]). So the result is at or above both upper bounds, and
    any float or +inf at or above both is at or above both lanes, so at or
    above their [max1]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Spec Ieee1788 Integer Sign MaxMin AddRu
  DecBinary Neg AddSub.

Open Scope R_scope.

(** ** The sign of a product *)

(** Lanes of different signs have a product at most 0. *)
Lemma mult_xorb_true :
  forall u v : f64, xorb (Bsign u) (Bsign v) = true -> B2R u * B2R v <= 0.
Proof.
intros u v Sx.
destruct (Bsign u) eqn:Su, (Bsign v) eqn:Sv; try discriminate Sx.
- pose proof (B2R_Bsign_true u Su). pose proof (B2R_Bsign_false v Sv).
  (* [u <= 0 <= v], so [-u * v] is a product of two reals at least 0. *)
  assert (0 <= - B2R u * B2R v) by (apply Rmult_le_pos; lra). lra.
- pose proof (B2R_Bsign_false u Su). pose proof (B2R_Bsign_true v Sv).
  assert (0 <= B2R u * - B2R v) by (apply Rmult_le_pos; lra). lra.
Qed.

(** Lanes of the same sign have a product at least 0. *)
Lemma mult_xorb_false :
  forall u v : f64, xorb (Bsign u) (Bsign v) = false -> 0 <= B2R u * B2R v.
Proof.
intros u v Sx.
destruct (Bsign u) eqn:Su, (Bsign v) eqn:Sv; try discriminate Sx.
- pose proof (B2R_Bsign_true u Su). pose proof (B2R_Bsign_true v Sv).
  (* [u, v <= 0], and [u * v = -u * -v]. *)
  replace (B2R u * B2R v) with (- B2R u * - B2R v) by ring.
  apply Rmult_le_pos; lra.
- apply Rmult_le_pos; apply B2R_Bsign_false; assumption.
Qed.

(** ** The lemmas *)

(** [Bmult mode_UP] of two finite lanes is the least float or +inf at or
    above their product. *)
Lemma mul_lane_finite :
  forall u v, is_finite u = true -> is_finite v = true ->
  least_lane (Some (B2R u * B2R v)) (Bmult mode_UP u v).
Proof.
intros u v Fu Fv.
destruct (round_UP_pt radix2 fexp64 (B2R u * B2R v)) as (_ & Hge & Hmin).
generalize (@Bmult_correct 53 1024 _ _ mode_UP u v).
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_UP)) with RU.
case Rlt_bool_spec; intros Hov HB.
- (* No overflow: the product rounded up. *)
  destruct HB as (HR & HF & _). rewrite Fu, Fv in HF. cbn [andb] in HF.
  split; [left; exact HF|]. rewrite (bound_finite _ HF), HR. split.
  + intros s Hs. cbn [below] in *. lra.
  + intros z [Fz| ->] Hz; [|intros s _; exact I].
    rewrite (bound_finite _ Fz) in *.
    (* [z] is a float at or above the product, so at or above it rounded
       up. *)
    assert (Hle : B2R u * B2R v <= B2R z) by exact (Hz _ (Rle_refl _)).
    pose proof (Hmin _ (generic_format_B2R _ _ z) Hle).
    intros s Hs. cbn [below] in *. lra.
- destruct (xorb (Bsign u) (Bsign v)) eqn:Sx.
  + (* The signs differ, so the product is at most 0, hence at or below
       -2^1024, and the result is [-f64::MAX]. *)
    pose proof (mult_xorb_true u v Sx).
    assert (Hneg : RU (B2R u * B2R v) <= 0).
    { apply Hmin; [apply generic_format_0 | lra]. }
    rewrite Rabs_left1 in Hov by exact Hneg.
    destruct (neg_overflow _ HB) as (Fw & Rw).
    split; [left; exact Fw|]. rewrite (bound_finite _ Fw), Rw. split.
    * intros s Hs'. cbn [below] in *. pose proof (bpow_gt_0 radix2 971). lra.
    * intros z Hz _ s Hs'. destruct Hz as [Fz| ->]; [|exact I].
      rewrite (bound_finite _ Fz). cbn [below] in *. pose proof (neg_max_le z).
      lra.
  + (* The signs agree, so the product rounded up is at least 0, hence at
       or above 2^1024, and so would be any float at or above the product.
       No float is, and the result is +inf. *)
    assert (Ew : Bmult mode_UP u v = B754_infinity false).
    { apply B2SF_inj. rewrite HB. reflexivity. }
    rewrite Ew. split; [right; reflexivity|]. split; [intros s _; exact I|].
    intros z [Fz| ->] Hz; [|intros s _; exact I].
    exfalso. rewrite (bound_finite _ Fz) in Hz.
    assert (Hle : B2R u * B2R v <= B2R z) by exact (Hz _ (Rle_refl _)).
    pose proof (Hmin _ (generic_format_B2R _ _ z) Hle).
    pose proof (mult_xorb_false u v Sx).
    rewrite Rabs_pos_eq in Hov by lra.
    pose proof (abs_B2R_lt_emax _ _ z). pose proof (Rle_abs (B2R z)). lra.
Qed.

(** A lane above 0 that is finite has the sign bit [false]. *)
Lemma pos_finite_sign :
  forall w : f64, 0 < B2R w -> Bsign w = false.
Proof.
intros w Pw. destruct (Bsign w) eqn:Sw; [|reflexivity].
pose proof (B2R_Bsign_true w Sw). lra.
Qed.

(** The same for two lanes above 0, where the product of the bounds is
    [None], i.e. +inf, if either lane is +inf ([umult]). *)
Lemma mul_lane_pos :
  forall u v, pos_lane u -> pos_lane v ->
  least_lane (umult (bound u) (bound v)) (Bmult mode_UP u v).
Proof.
intros u v [-> | (Fu & Pu)] [-> | (Fv & Pv)].
- (* +inf times +inf is +inf. *)
  exact least_lane_inf.
- (* +inf times a float above 0 is +inf. *)
  pose proof (pos_finite_sign v Pv) as Sv.
  destruct v as [sv|sv| |sv mv ev Hv]; try discriminate Fv; cbn [Bsign] in Sv;
    subst sv; [cbn [B2R] in Pv; lra | exact least_lane_inf].
- pose proof (pos_finite_sign u Pu) as Su.
  destruct u as [su|su| |su mu eu Hu]; try discriminate Fu; cbn [Bsign] in Su;
    subst su; [cbn [B2R] in Pu; lra | exact least_lane_inf].
- rewrite (bound_finite _ Fu), (bound_finite _ Fv). cbn [umult].
  exact (mul_lane_finite u v Fu Fv).
Qed.

(** If two lanes are the least floats or +inf at or above two upper
    bounds, their [max1] is the least at or above the larger bound. *)
Lemma max_least_lane :
  forall o1 o2 w1 w2, least_lane o1 w1 -> least_lane o2 w2 ->
  least_lane (umax o1 o2) (Generic.max1 w1 w2).
Proof.
intros o1 o2 w1 w2 (U1 & Le1 & Min1) (U2 & Le2 & Min2).
destruct (max1_bound _ _ U1 U2) as (U & B).
split; [exact U|]. rewrite B. split.
- (* Below one upper bound, so below that lane. *)
  intros s. rewrite !below_umax.
  intros [H|H]; [left; exact (Le1 s H) | right; exact (Le2 s H)].
- (* [z] is at or above both upper bounds, so at or above both lanes. *)
  intros z Uz Hz.
  assert (H1 : ule o1 (bound z))
    by (intros t Ht; apply Hz, below_umax; left; exact Ht).
  assert (H2 : ule o2 (bound z))
    by (intros t Ht; apply Hz, below_umax; right; exact Ht).
  intros s. rewrite below_umax.
  intros [H|H]; [exact (Min1 z Uz H1 s H) | exact (Min2 z Uz H2 s H)].
Qed.
