(** * One lane of [x / y] and [recip x] of intervals, rounded up

    Outside the pairs of classes that give [EMPTY], [[0, 0]] or [ENTIRE],
    each lane of [x / y] and [recip x] is a quotient of two lanes rounded
    up ([Bdiv mode_UP]), or +inf. These lemmas show that each is the least
    float or +inf at or above the least upper bound of the set of quotients
    that the lane stands for ([lane_ok] in [DivTight.v]), in the three
    forms of [DivTight.v]:
    - (a) [div_lane_pos]: [Bdiv mode_UP u v] with [u] above 0 and [v] a
      float above 0; +inf / [v] is +inf.
    - (a') [div_lane_neg]: [Bdiv mode_UP (-u) v] with [u] above 0 and [v]
      a float below 0, which is [u / (-v)]; -inf / [v] is +inf.
    - (b) [div_lane_inf]: the lane +inf, for quotients with no upper
      bound.
    - (c) [div_lane_nonpos]: [Bdiv mode_UP u v] with [u] a float at most 0
      and [v] above 0; [u] / +inf is a zero, whose value 0 is the least
      upper bound.

    [div_lane_finite] follows [mul_lane_finite] in [MulLane.v], with
    [Bdiv_correct] in place of [Bmult_correct]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Spec Ieee1788 Integer Sign MaxMin AddRu
  DecBinary AddSub MulLane DivTight.

Open Scope R_scope.

(** ** The sign of a quotient *)

(** Lanes of different signs have a quotient at most 0. *)
Lemma div_xorb_true :
  forall u v : f64, B2R v <> 0 -> xorb (Bsign u) (Bsign v) = true ->
  B2R u / B2R v <= 0.
Proof.
intros u v Nv Sx. unfold Rdiv.
(* [v] is not 0, so its sign makes it below or above 0. *)
destruct (Rdichotomy _ _ Nv) as [Dv|Dv];
  destruct (Bsign u) eqn:Su, (Bsign v) eqn:Sv; try discriminate Sx;
  [ pose proof (B2R_Bsign_false v Sv); lra | | | pose proof (B2R_Bsign_true v Sv); lra ].
- (* [v < 0 <= u], so [u * -/v] is a product of two reals at least 0. *)
  pose proof (B2R_Bsign_false u Su).
  assert (/ B2R v < 0) by (apply Rinv_lt_0_compat; exact Dv).
  assert (0 <= B2R u * - / B2R v) by (apply Rmult_le_pos; lra). lra.
- (* [u <= 0 < v], so [-u * /v] is a product of two reals at least 0. *)
  pose proof (B2R_Bsign_true u Su).
  assert (0 < / B2R v) by (apply Rinv_0_lt_compat; exact Dv).
  assert (0 <= - B2R u * / B2R v) by (apply Rmult_le_pos; lra). lra.
Qed.

(** Lanes of the same sign have a quotient at least 0. *)
Lemma div_xorb_false :
  forall u v : f64, B2R v <> 0 -> xorb (Bsign u) (Bsign v) = false ->
  0 <= B2R u / B2R v.
Proof.
intros u v Nv Sx. unfold Rdiv.
destruct (Rdichotomy _ _ Nv) as [Dv|Dv];
  destruct (Bsign u) eqn:Su, (Bsign v) eqn:Sv; try discriminate Sx;
  [ | pose proof (B2R_Bsign_false v Sv); lra
    | pose proof (B2R_Bsign_true v Sv); lra | ].
- (* [u <= 0] and [v < 0], and [u * /v = -u * -/v]. *)
  pose proof (B2R_Bsign_true u Su).
  assert (/ B2R v < 0) by (apply Rinv_lt_0_compat; exact Dv).
  replace (B2R u * / B2R v) with (- B2R u * - / B2R v) by ring.
  apply Rmult_le_pos; lra.
- pose proof (B2R_Bsign_false u Su).
  assert (0 < / B2R v) by (apply Rinv_0_lt_compat; exact Dv).
  apply Rmult_le_pos; lra.
Qed.

(** ** The lemmas *)

(** [Bdiv mode_UP] of two finite lanes is the least float or +inf at or
    above their quotient. *)
Lemma div_lane_finite :
  forall u v, is_finite u = true -> is_finite v = true -> B2R v <> 0 ->
  least_lane (Some (B2R u / B2R v)) (Bdiv mode_UP u v).
Proof.
intros u v Fu Fv Nv.
destruct (round_UP_pt radix2 fexp64 (B2R u / B2R v)) as (_ & Hge & Hmin).
generalize (@Bdiv_correct 53 1024 _ _ mode_UP u v Nv).
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_UP)) with RU.
case Rlt_bool_spec; intros Hov HB.
- (* No overflow: the quotient rounded up. *)
  destruct HB as (HR & HF & _). rewrite Fu in HF.
  split; [left; exact HF|]. rewrite (bound_finite _ HF), HR. split.
  + intros s Hs. cbn [below] in *. lra.
  + intros z [Fz| ->] Hz; [|intros s _; exact I].
    rewrite (bound_finite _ Fz) in *.
    (* [z] is a float at or above the quotient, so at or above it rounded
       up. *)
    assert (Hle : B2R u / B2R v <= B2R z) by exact (Hz _ (Rle_refl _)).
    pose proof (Hmin _ (generic_format_B2R _ _ z) Hle).
    intros s Hs. cbn [below] in *. lra.
- destruct (xorb (Bsign u) (Bsign v)) eqn:Sx.
  + (* The signs differ, so the quotient is at most 0, hence at or below
       -2^1024, and the result is [-f64::MAX]. *)
    pose proof (div_xorb_true u v Nv Sx).
    assert (Hneg : RU (B2R u / B2R v) <= 0).
    { apply Hmin; [apply generic_format_0 | lra]. }
    rewrite Rabs_left1 in Hov by exact Hneg.
    destruct (neg_overflow _ HB) as (Fw & Rw).
    split; [left; exact Fw|]. rewrite (bound_finite _ Fw), Rw. split.
    * intros s Hs'. cbn [below] in *. pose proof (bpow_gt_0 radix2 971). lra.
    * intros z Hz _ s Hs'. destruct Hz as [Fz| ->]; [|exact I].
      rewrite (bound_finite _ Fz). cbn [below] in *. pose proof (neg_max_le z).
      lra.
  + (* The signs agree, so the quotient rounded up is at least 0, hence at
       or above 2^1024, and so would be any float at or above the quotient.
       No float is, and the result is +inf. *)
    assert (Ew : Bdiv mode_UP u v = B754_infinity false).
    { apply B2SF_inj. rewrite HB. reflexivity. }
    rewrite Ew. split; [right; reflexivity|]. split; [intros s _; exact I|].
    intros z [Fz| ->] Hz; [|intros s _; exact I].
    exfalso. rewrite (bound_finite _ Fz) in Hz.
    assert (Hle : B2R u / B2R v <= B2R z) by exact (Hz _ (Rle_refl _)).
    pose proof (Hmin _ (generic_format_B2R _ _ z) Hle).
    pose proof (div_xorb_false u v Nv Sx).
    rewrite Rabs_pos_eq in Hov by lra.
    pose proof (abs_B2R_lt_emax _ _ z). pose proof (Rle_abs (B2R z)). lra.
Qed.

(** [u / +inf] for a finite [u] is a zero, the least float at or above
    the upper bound 0. *)
Lemma least_lane_zero : forall s, least_lane (Some 0) (B754_zero s).
Proof.
intros s. split; [left; reflexivity|]. split.
- intros t Ht. exact Ht.
- intros z _ Hz. exact Hz.
Qed.

(** (a) *)
Lemma div_lane_pos :
  forall U Q u v, pos_set U u -> den_min Q (B2R v) -> is_finite v = true ->
  lane_ok (quot U Q) (Bdiv mode_UP u v).
Proof.
intros U Q u v (Pu & Tu & Hr) Hq Fv.
exists (udiv (bound u) (B2R v)).
split; [exact (tight_lub _ _ (quot_tight_a _ _ _ _ Tu Hr Hq))|].
destruct Hq as (_ & Pv & _).
destruct Pu as [-> | (Fu & _)].
- (* +inf over a float above 0, which has the sign bit [false], is +inf. *)
  pose proof (pos_finite_sign v Pv) as Sv.
  destruct v as [sv|sv| |sv mv ev Hv]; try discriminate Fv; cbn [Bsign] in Sv;
    subst sv; [cbn [B2R] in Pv; lra | exact least_lane_inf].
- rewrite (bound_finite _ Fu). cbn [udiv].
  apply div_lane_finite; [exact Fu | exact Fv | apply Rgt_not_eq; exact Pv].
Qed.

(** (a') *)
Lemma div_lane_neg :
  forall U Q u v, pos_set U u -> den_min Q (- B2R v) -> is_finite v = true ->
  lane_ok (quot U Q) (Bdiv mode_UP (opp u) v).
Proof.
intros U Q u v (Pu & Tu & Hr) Hq Fv.
exists (udiv (bound u) (- B2R v)).
split; [exact (tight_lub _ _ (quot_tight_a _ _ _ _ Tu Hr Hq))|].
destruct Hq as (_ & Pv & _).
destruct Pu as [-> | (Fu & _)].
- (* -inf over a float below 0, which has the sign bit [true], is +inf. *)
  assert (Sv : Bsign v = true).
  { destruct (Bsign v) eqn:E; [reflexivity|].
    pose proof (B2R_Bsign_false v E). lra. }
  destruct v as [sv|sv| |sv mv ev Hv]; try discriminate Fv; cbn [Bsign] in Sv;
    subst sv; [cbn [B2R] in Pv; lra | exact least_lane_inf].
- (* [-u / v = u / (-v)]. *)
  rewrite (bound_finite _ Fu). cbn [udiv].
  assert (Nv : B2R v <> 0) by (apply Rlt_not_eq; lra).
  replace (B2R u / - B2R v) with (B2R (opp u) / B2R v)
    by (rewrite B2R_opp; field; exact Nv).
  apply div_lane_finite; [rewrite is_finite_opp; exact Fu | exact Fv | exact Nv].
Qed.

(** (b) *)
Lemma div_lane_inf :
  forall U Q, (exists r, U r /\ 0 < r) -> den_near0 Q ->
  lane_ok (quot U Q) (B754_infinity false).
Proof.
intros U Q Hr Hq. apply lane_ok_inf. exact (quot_unbounded U Q Hr Hq).
Qed.

(** (c) *)
Lemma div_lane_nonpos :
  forall U Q u v, nonpos_set U u -> den_sup Q v ->
  lane_ok (quot U Q) (Bdiv mode_UP u v).
Proof.
intros U Q u v (Fu & Uu & Mu & Nu) (Pv & Tv & Qn & Qp).
exists (uquot (B2R u) (bound v)).
split; [exact (quot_lub_c U Q (B2R u) (bound v) Uu Mu Nu Tv Qn Qp)|].
destruct Pv as [-> | (Fv & Pv)].
- (* A finite [u] over +inf is a zero, and the upper bound is 0. *)
  destruct u as [su|su| |su mu eu Hu]; try discriminate Fu;
    exact (least_lane_zero _).
- rewrite (bound_finite _ Fv). cbn [uquot].
  apply div_lane_finite; [exact Fu | exact Fv | apply Rgt_not_eq; exact Pv].
Qed.
