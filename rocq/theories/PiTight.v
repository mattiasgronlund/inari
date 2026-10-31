(** * The bounds of [Interval::PI] and [Interval::FRAC_PI_2] are the floats next to π and π/2

    [PiBounds.v] shows [lo < c < hi] for the bounds [lo] and [hi] of each
    constant. Their bit patterns differ by one, so [hi] is the float after
    [lo] (Flocq's [Bsucc]), and no float lies strictly between them. So
    [hi] is the least float at or above [c], and [lo] the largest at or
    below it, which the tightest results of [Interval::atan2] need. Each
    lemma states it for a lane of an interval, as [least_lane] in
    [AddSub.v]: the upper bound [hi], or the negated lower bound [-lo]. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Integer Sign MaxMin AddSub PiBounds.

Open Scope R_scope.

(** ** A constant between two consecutive floats *)

(** A float above the finite float [lo] is at least the float [Bsucc lo]
    after it: [Bsucc_correct] makes that the successor [succ] of [lo] in
    the format, and [succ_le_lt] bounds every element of the format above
    [lo] by it. *)
Lemma pt_succ_le :
  forall lo z : f64, is_finite lo = true -> is_finite (Bsucc lo) = true ->
  B2R lo < B2R z -> B2R (Bsucc lo) <= B2R z.
Proof.
intros lo z Flo Fs Hz.
pose proof (Bsucc_correct 53 1024 _ _ lo Flo) as H.
revert H. case Rlt_bool_spec; intros _ H.
- destruct H as [H _]. rewrite H.
  apply succ_le_lt; [typeclasses eauto | apply generic_format_B2R |
    apply generic_format_B2R | exact Hz].
- (* [Bsucc lo] would be +inf. *)
  destruct (Bsucc lo); discriminate.
Qed.

(** If [hi = Bsucc lo] and [lo < c < hi], then [hi] is the least float or
    +inf at or above [c]. *)
Lemma pt_up :
  forall (lo hi : f64) c, is_finite lo = true -> is_finite hi = true ->
  Bsucc lo = hi -> B2R lo < c < B2R hi -> least_lane (Some c) hi.
Proof.
intros lo hi c Flo Fhi Hs Hc.
split; [left; exact Fhi|]. rewrite (bound_finite _ Fhi).
split; [intros s Hs'; cbn [below] in *; lra|].
intros z [Fz| ->] Hz.
- rewrite (bound_finite _ Fz) in Hz |- *.
  assert (Hcz : c <= B2R z) by exact (Hz c (Rle_refl c)).
  rewrite <- Hs in Fhi.
  pose proof (pt_succ_le lo z Flo Fhi ltac:(lra)) as H. rewrite Hs in H.
  intros s Hs'. cbn [below] in *. lra.
- intros s _. exact I.
Qed.

(** And [-lo] is the least float or +inf at or above [-c]: a float [z]
    with [-c <= z < -lo] would make [-z] a float in [(lo, c]], below
    [hi]. *)
Lemma pt_dn :
  forall (lo hi : f64) c, is_finite lo = true -> is_finite hi = true ->
  Bsucc lo = hi -> B2R lo < c < B2R hi -> least_lane (Some (- c)) (opp lo).
Proof.
intros lo hi c Flo Fhi Hs Hc.
assert (Fo : is_finite (opp lo) = true) by (rewrite is_finite_opp; exact Flo).
split; [left; exact Fo|]. rewrite (bound_finite _ Fo), B2R_opp.
split; [intros s Hs'; cbn [below] in *; lra|].
intros z [Fz| ->] Hz.
- rewrite (bound_finite _ Fz) in Hz |- *.
  assert (Hcz : - c <= B2R z) by exact (Hz (- c) (Rle_refl (- c))).
  destruct (Rle_or_lt (- B2R lo) (B2R z)) as [Hle|Hlt].
  + intros s Hs'. cbn [below] in *. lra.
  + exfalso.
    assert (Fz' : is_finite (opp z) = true) by (rewrite is_finite_opp; exact Fz).
    rewrite <- Hs in Fhi.
    pose proof (pt_succ_le lo (opp z) Flo Fhi) as H.
    rewrite B2R_opp, Hs in H. specialize (H ltac:(lra)). lra.
- intros s _. exact I.
Qed.

(** The bounds of [Interval::PI] and [Interval::FRAC_PI_2], decoded. *)
Lemma pt_PI_facts :
  is_finite (Interval.inf_raw Interval.PI) = true /\
  is_finite (Interval.sup_raw Interval.PI) = true /\
  Bsucc (Interval.inf_raw Interval.PI) = Interval.sup_raw Interval.PI.
Proof.
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
apply B2SF_inj. vm_compute. reflexivity.
Qed.

Lemma pt_FRAC_PI_2_facts :
  is_finite (Interval.inf_raw Interval.FRAC_PI_2) = true /\
  is_finite (Interval.sup_raw Interval.FRAC_PI_2) = true /\
  Bsucc (Interval.inf_raw Interval.FRAC_PI_2) = Interval.sup_raw Interval.FRAC_PI_2.
Proof.
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
apply B2SF_inj. vm_compute. reflexivity.
Qed.

(** ** The lanes *)

Lemma PI_up : least_lane (Some PI) (Interval.sup_raw Interval.PI).
Proof.
destruct pt_PI_facts as (F0 & F1 & Hs).
exact (pt_up _ _ PI F0 F1 Hs PI_bounds).
Qed.

Lemma PI_dn : least_lane (Some (- PI)) (opp (Interval.inf_raw Interval.PI)).
Proof.
destruct pt_PI_facts as (F0 & F1 & Hs).
exact (pt_dn _ _ PI F0 F1 Hs PI_bounds).
Qed.

Lemma FRAC_PI_2_up : least_lane (Some (PI / 2)) (Interval.sup_raw Interval.FRAC_PI_2).
Proof.
destruct pt_FRAC_PI_2_facts as (F0 & F1 & Hs).
apply (pt_up _ _ (PI / 2) F0 F1 Hs).
rewrite pb_frac_lo, pb_frac_hi. pose proof PI_bounds. lra.
Qed.

Lemma FRAC_PI_2_dn :
  least_lane (Some (- (PI / 2))) (opp (Interval.inf_raw Interval.FRAC_PI_2)).
Proof.
destruct pt_FRAC_PI_2_facts as (F0 & F1 & Hs).
apply (pt_dn _ _ (PI / 2) F0 F1 Hs).
rewrite pb_frac_lo, pb_frac_hi. pose proof PI_bounds. lra.
Qed.
