(** * One lane of [mul_add] of intervals, rounded up

    For a nonempty [z], and [x] and [y] outside the classes [E] and [Z],
    each lane of [x.mul_add(y, z)] is [Bfma mode_UP] of the two lanes that
    [x * y] multiplies and the lane of [z], or [max1] of two such. [fma_lane_finite] and [fma_lane_pos] show
    that each gives the least float or +inf at or above the sum of the
    product and the upper bound that the lane of [z] stands for
    ([least_lane]), as [mul_lane_finite] and [mul_lane_pos] in [MulLane.v]
    do for the product alone. [tightest_mul_add] puts two such lanes
    together into the tightest interval that contains the image of
    [x × y × z] under [Rfma], given the largest product and the largest
    negated product of [x × y], as [tightest_lanes] in [AddSub.v] does.

    [fma_lane_finite] follows [add_lane] in [AddSub.v], with
    [Bfma_correct] in place of [Bplus_correct]. If [u * v + w] rounded up
    does not overflow, [Bfma mode_UP] gives it. If it overflows, [Bfma]
    gives [binary_overflow] with the sign of [u * v + w]: below 0 it is at
    or below [-2^1024], and the result [-f64::MAX] is at or below every
    float; at or above 0 no float is at or above it, and the result is
    +inf. A third lane that is +inf gives +inf, as Flocq's [Bfma] returns
    an infinite third lane if the first two are finite. In
    [fma_lane_pos], a lane that is +inf times one above 0 is +inf, and
    adding a float or +inf to it keeps +inf. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Spec Ieee1788 Integer Sign MaxMin AddRu
  DecBinary Neg AddSub MulLane.

Open Scope R_scope.

(** [Bfma mode_UP] of two finite lanes and a lane that is finite or +inf
    is the least float or +inf at or above their product plus the bound of
    the third lane. *)
Lemma fma_lane_finite :
  forall u v w, is_finite u = true -> is_finite v = true -> upper_ok w ->
  least_lane (uplus (Some (B2R u * B2R v)) (bound w)) (Bfma mode_UP u v w).
Proof.
intros u v w Fu Fv [Fw| ->].
2: { (* The product of two finite lanes is finite, and [Bfma] returns the
        third lane if it is infinite. *)
     destruct u; try discriminate Fu; destruct v; try discriminate Fv;
       exact least_lane_inf. }
rewrite (bound_finite _ Fw). cbn [uplus].
destruct (round_UP_pt radix2 fexp64 (B2R u * B2R v + B2R w)) as (_ & Hge & Hmin).
generalize (@Bfma_correct 53 1024 _ _ mode_UP u v w Fu Fv Fw). cbv zeta.
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_UP)) with RU.
destruct (Rlt_bool_spec (Rabs (RU (B2R u * B2R v + B2R w))) (bpow radix2 1024))
  as [Hov|Hov]; intros HB.
- (* No overflow: the sum rounded up. *)
  destruct HB as (HR & HF & _).
  split; [left; exact HF|]. rewrite (bound_finite _ HF), HR. split.
  + intros s Hs. cbn [below] in *. lra.
  + intros z [Fz| ->] Hz; [|intros s _; exact I].
    rewrite (bound_finite _ Fz) in *.
    (* [z] is a float at or above the sum, so at or above it rounded up. *)
    assert (Hle : B2R u * B2R v + B2R w <= B2R z) by exact (Hz _ (Rle_refl _)).
    pose proof (Hmin _ (generic_format_B2R _ _ z) Hle).
    intros s Hs. cbn [below] in *. lra.
- (* The overflow takes the sign of the exact sum. *)
  revert HB. case Rlt_bool_spec; intros Hs HB.
  + (* The sum is below 0, so at or below -2^1024, and the result is
       [-f64::MAX]. *)
    assert (Hneg : RU (B2R u * B2R v + B2R w) <= 0).
    { apply Hmin; [apply generic_format_0 | lra]. }
    rewrite Rabs_left1 in Hov by exact Hneg.
    destruct (neg_overflow _ HB) as (Fr & Rr).
    split; [left; exact Fr|]. rewrite (bound_finite _ Fr), Rr. split.
    * intros s Hs'. cbn [below] in *. pose proof (bpow_gt_0 radix2 971). lra.
    * intros z Hz _ s Hs'. destruct Hz as [Fz| ->]; [|exact I].
      rewrite (bound_finite _ Fz). cbn [below] in *. pose proof (neg_max_le z).
      lra.
  + (* The sum is at least 0, so it rounds up to at least 2^1024, and so
       would any float at or above it. No float is, and the result is
       +inf. *)
    assert (Ew : Bfma mode_UP u v w = B754_infinity false).
    { apply B2SF_inj. rewrite HB. reflexivity. }
    rewrite Ew. split; [right; reflexivity|]. split; [intros s _; exact I|].
    intros z [Fz| ->] Hz; [|intros s _; exact I].
    exfalso. rewrite (bound_finite _ Fz) in Hz.
    assert (Hle : B2R u * B2R v + B2R w <= B2R z) by exact (Hz _ (Rle_refl _)).
    pose proof (Hmin _ (generic_format_B2R _ _ z) Hle).
    rewrite Rabs_pos_eq in Hov by lra.
    pose proof (abs_B2R_lt_emax _ _ z). pose proof (Rle_abs (B2R z)). lra.
Qed.

(** The same for two lanes above 0, where the product of the bounds is
    [None], i.e. +inf, if either lane is +inf ([umult]). *)
Lemma fma_lane_pos :
  forall u v w, pos_lane u -> pos_lane v -> upper_ok w ->
  least_lane (uplus (umult (bound u) (bound v)) (bound w)) (Bfma mode_UP u v w).
Proof.
intros u v w [-> | (Fu & Pu)] [-> | (Fv & Pv)] Uw.
- (* +inf times +inf is +inf, and adding a float or +inf to it gives
     +inf. *)
  destruct Uw as [Fw| ->]; [destruct w; try discriminate Fw|]; exact least_lane_inf.
- (* +inf times a float above 0 is +inf, as its sign bit is [false]. *)
  pose proof (pos_finite_sign v Pv) as Sv.
  destruct v as [sv|sv| |sv mv ev Hv]; try discriminate Fv; cbn [Bsign] in Sv;
    subst sv; [cbn [B2R] in Pv; lra|].
  destruct Uw as [Fw| ->]; [destruct w; try discriminate Fw|]; exact least_lane_inf.
- pose proof (pos_finite_sign u Pu) as Su.
  destruct u as [su|su| |su mu eu Hu]; try discriminate Fu; cbn [Bsign] in Su;
    subst su; [cbn [B2R] in Pu; lra|].
  destruct Uw as [Fw| ->]; [destruct w; try discriminate Fw|]; exact least_lane_inf.
- rewrite (bound_finite _ Fu), (bound_finite _ Fv). cbn [umult].
  exact (fma_lane_finite u v w Fu Fv Uw).
Qed.

(** Adding an upper bound to the larger of two is adding it to both and
    taking the larger. *)
Lemma uplus_umax :
  forall o1 o2 o3, uplus (umax o1 o2) o3 = umax (uplus o1 o3) (uplus o2 o3).
Proof.
intros [a|] [b|] [c|]; cbn [uplus umax]; try reflexivity.
f_equal. unfold Rmax. destruct (Rle_dec a b), (Rle_dec (a + c) (b + c)); lra.
Qed.

(** The image of [x × y × z] under [Rfma] holds the sums of a product of
    [x × y] and a real of [z]. *)
Lemma image3_fma :
  forall x y z s,
  image3 Rfma x y z s <-> exists p u, image2 Rmult x y p /\ mem u z /\ s = p + u.
Proof.
intros x y z s. unfold image3, image2, Rfma. split.
- intros (r & t & u & Hr & Ht & Hu & ->). exists (r * t), u.
  split; [exists r, t; split; [exact Hr | split; [exact Ht | reflexivity]]|].
  split; [exact Hu | reflexivity].
- intros (p & u & (r & t & Hr & Ht & ->) & Hu & ->). exists r, t, u.
  split; [exact Hr|]. split; [exact Ht|]. split; [exact Hu | reflexivity].
Qed.

(** [w] is the tightest interval that contains the image of [x × y × z]
    under [Rfma] if the products of [x × y] have the largest element [hi]
    and the largest negation [lo], and the lanes of [w] are the least
    floats or +inf at or above [lo] and [hi] plus the bounds of the lanes
    of a nonempty [z]. *)
Lemma tightest_mul_add :
  forall x y z w lo hi, valid z -> Interval.is_empty z = false ->
  (exists s, image2 Rmult x y s) ->
  tight lo (fun s => image2 Rmult x y (- s)) -> tight hi (image2 Rmult x y) ->
  least_lane (uplus lo (bound (fst (rep z)))) (fst (rep w)) ->
  least_lane (uplus hi (bound (snd (rep z)))) (snd (rep w)) ->
  is_tightest (image3 Rfma x y z) w.
Proof.
intros x y z w lo hi Hz Ez [p0 Hp0] Tlo Thi L0 L1.
(* [is_empty] is [is_nan] of the first lane, so [lanes_tight] applies. *)
destruct (lanes_tight z Hz Ez) as (_ & _ & [u0 Hu0] & Tz0 & Tz1).
apply (tightest_lanes _ w (uplus lo (bound (fst (rep z))))
                          (uplus hi (bound (snd (rep z))))).
- exists (p0 + u0). apply image3_fma. exists p0, u0.
  split; [exact Hp0|]. split; [exact Hu0 | reflexivity].
- (* The largest negated sum is the largest negated product plus the
     largest negated real of [z], as [-(p + u) = (-p) + (-u)]. *)
  apply (tight_ext _ (fun s => exists r t, image2 Rmult x y (- r) /\
                                           mem (- t) z /\ s = r + t)).
  + intros s. cbv beta. rewrite image3_fma. split.
    * intros (r & t & Hr & Ht & ->). exists (- r), (- t).
      split; [exact Hr|]. split; [exact Ht | ring].
    * intros (p & u & Hp & Hu & Hs). exists (- p), (- u).
      rewrite !Ropp_involutive. split; [exact Hp|]. split; [exact Hu | lra].
  + apply tight_sum; [exact Tlo | exact Tz0 | exists (- p0) | exists (- u0)];
      cbv beta; rewrite Ropp_involutive; assumption.
- (* The largest sum is the largest product plus the largest real of
     [z]. *)
  apply (tight_ext _ (fun s => exists r t, image2 Rmult x y r /\
                                           mem t z /\ s = r + t)).
  + intros s. cbv beta. rewrite image3_fma. reflexivity.
  + apply tight_sum; [exact Thi | exact Tz1 | exists p0; exact Hp0 | exists u0; exact Hu0].
- exact L0.
- exact L1.
Qed.
