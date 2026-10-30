(** * The results that [sin], [cos] and [tan] of intervals return

    Each branch of [Interval::cos], [Interval::sin] and [Interval::tan]
    returns one of six forms, for [x = [a, b]] and [f_rd], [f_ru] computed
    with MPFR: [[f_rd(a), f_ru(b)]] (on a piece where [f] increases),
    [[f_rd(b), f_ru(a)]] (where it decreases), [[min(f_rd(a), f_rd(b)), 1]]
    (around a maximum), [[-1, max(f_ru(a), f_ru(b))]] (around a minimum),
    [[-1, 1]] and [[-inf, +inf]]. This file proves, once for every [f],
    when each form encloses the image of [x] ([br_*_encl]) and when it is
    the tightest interval that does ([br_*_tight]); the forms around a
    maximum or a minimum are for [sin] and [cos], so they assume that [f]
    is in [[-1, 1]]. And, in
    [trig_set_dec_correct], what [set_dec] makes of an enclosure, as
    [elem_set_dec_correct] in [ElemDec.v] does of a tightest interval. *)

From Stdlib Require Import ZArith Reals Lra Classical_Prop.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Integer DecBinary
  MpfrRound ElemDec.
From Inari Require Import Sign MaxMin AddSub MulTight DivTight Sqrt MonoInc Cosh.

Open Scope R_scope.

(** A nonempty interval with finite bounds. *)
Definition finite_itv (x : Interval) : Prop :=
  valid x /\ Interval.is_empty x = false /\
  is_finite (Interval.inf_raw x) = true /\ is_finite (Interval.sup_raw x) = true.

Lemma finite_itv_mem :
  forall x r, finite_itv x ->
  mem r x <-> B2R (Interval.inf_raw x) <= r <= B2R (Interval.sup_raw x).
Proof.
intros x r (_ & _ & Fa & Fb).
rewrite (mem_bounds x r (or_introl Fa) (or_introl Fb)).
unfold Interval.inf_raw, Interval.sup_raw in *.
rewrite (bound_finite _ Fa), (bound_finite _ Fb). unfold in_bounds. tauto.
Qed.

(** ** Helpers *)

Lemma tb_mem_inf : forall x, finite_itv x -> mem (B2R (Interval.inf_raw x)) x.
Proof.
intros x (Hx & Hn & Fa & _). exact (mono_mem_inf x Hx Hn Fa).
Qed.

Lemma tb_mem_sup : forall x, finite_itv x -> mem (B2R (Interval.sup_raw x)) x.
Proof.
intros x (Hx & Hn & _ & Fb). exact (mono_mem_sup x Hx Hn Fb).
Qed.

Lemma tb_ule_Some : forall a b, ule (Some a) (Some b) <-> a <= b.
Proof.
intros a b. split.
- intros H. exact (H a (Rle_refl a)).
- intros H s Hs. cbn [below] in *. lra.
Qed.

(** An interval whose first lane is at or above [lo] and whose second lane
    is at or above [hi] is valid if [-lo <= hi], and holds every real
    between [-lo] and [hi]. This is the start of the proof of
    [tightest_lanes_lub_rep] in [DivTight.v], without the minimality. *)
Lemma tb_encl_lanes :
  forall S w0 w1 lo hi, least_lane (Some lo) w0 -> least_lane (Some hi) w1 ->
  - lo <= hi -> (forall s, S s -> - lo <= s <= hi) ->
  encloses S {| rep := (w0, w1) |}.
Proof.
intros S w0 w1 lo hi (U0 & Le0 & _) (U1 & Le1 & _) Hlh HS.
pose proof (lower_ok_lane _ U0) as Ha.
assert (Hin : forall s, - lo <= s <= hi -> in_bounds (bound (opp w0)) (bound w1) s).
{ intros s Hs. apply in_bounds_iff. split.
  - apply below_oopp. rewrite <- bound_lane. apply Le0. cbn [below]. lra.
  - apply Le1. cbn [below]. lra. }
split.
- apply (valid_bounds {| rep := (w0, w1) |}); cbn [rep fst snd]; [exact Ha | exact U1|].
  apply (in_bounds_ordered _ _ hi). apply Hin. lra.
- intros s Hs. apply (proj2 (mem_bounds {| rep := (w0, w1) |} s Ha U1)).
  exact (Hin s (HS s Hs)).
Qed.

(** [1.0] is the least float at or above 1, and so is [-(-1.0)]. *)
Lemma tb_lane_one : least_lane (Some 1) (of_u64 1).
Proof.
destruct one_B2R as [F1 E1]. unfold one in F1, E1.
pose proof (least_lane_exact _ F1) as H. rewrite E1 in H. exact H.
Qed.

Lemma tb_lane_m_one : least_lane (Some 1) (opp (opp (of_u64 1))).
Proof.
unfold opp. rewrite Bopp_involutive. exact tb_lane_one.
Qed.

Lemma tb_f64_1 : f64_format 1 /\ f64_format (-1).
Proof.
destruct one_B2R as [F1 E1]. split.
- exists one. split; [exact F1 | exact E1].
- exists (opp one). rewrite is_finite_opp, B2R_opp, E1. split; [exact F1 | reflexivity].
Qed.

(** A value of at least -1 rounded down, or of at most 1 rounded up, is a
    finite float, as -1 and 1 are floats. *)
Lemma tb_rd_finite :
  forall r w, mpfr_round f64_format RNDD r (with_val w) -> -1 <= r -> is_finite w = true.
Proof.
intros r w H Hr. destruct w as [s|[|]| |s mw ew Hw]; cbn [with_val mpfr_round] in H;
  try reflexivity; try contradiction.
pose proof (H _ (proj2 tb_f64_1)). exfalso. lra.
Qed.

Lemma tb_ru_finite :
  forall r w, mpfr_round f64_format RNDU r (with_val w) -> r <= 1 -> is_finite w = true.
Proof.
intros r w H Hr. destruct w as [s|[|]| |s mw ew Hw]; cbn [with_val mpfr_round] in H;
  try reflexivity; try contradiction.
pose proof (H _ (proj1 tb_f64_1)). exfalso. lra.
Qed.

(** [fmin] of two finite floats is finite, with the smaller real, as
    [ch_fmax_fin] in [Cosh.v] for [fmax]. *)
Lemma tb_fmin_fin :
  forall first x y, is_finite x = true -> is_finite y = true ->
  is_finite (fmin first x y) = true /\ B2R (fmin first x y) = Rmin (B2R x) (B2R y).
Proof.
intros first x y Fx Fy.
destruct (ch_lt_fin x y Fx Fy) as [Hxy Hxy'].
destruct (ch_lt_fin y x Fy Fx) as [Hyx Hyx'].
unfold fmin.
destruct (Model.lt x y) eqn:Exy.
- split; [exact Fx|]. rewrite Rmin_left; [reflexivity|]. specialize (Hxy eq_refl). lra.
- specialize (Hxy' eq_refl).
  destruct (Model.lt y x) eqn:Eyx.
  + split; [exact Fy|]. rewrite Rmin_right; [reflexivity|]. lra.
  + (* Neither is less, so their reals are equal. *)
    specialize (Hyx' eq_refl).
    destruct first; (split; [assumption|]).
    * rewrite Rmin_left; [reflexivity|]. lra.
    * rewrite Rmin_right; [reflexivity|]. lra.
Qed.

(** Rounding is monotone, so the larger of two values rounded up is the
    larger of the two rounded up: [fmax] of the least lanes at or above
    [u] and [v] is the least lane at or above [max(u, v)]. *)
Lemma tb_lane_max :
  forall first u v w w', least_lane (Some u) w -> least_lane (Some v) w' ->
  is_finite w = true -> is_finite w' = true ->
  least_lane (Some (Rmax u v)) (fmax first w w').
Proof.
intros first u v w w' (_ & Le & Min) (_ & Le' & Min') Fw Fw'.
destruct (ch_fmax_fin first w w' Fw Fw') as [Fm Em].
rewrite (bound_finite _ Fw), tb_ule_Some in Le.
rewrite (bound_finite _ Fw'), tb_ule_Some in Le'.
pose proof (Rmax_l (B2R w) (B2R w')). pose proof (Rmax_r (B2R w) (B2R w')).
split; [left; exact Fm|]. rewrite (bound_finite _ Fm), Em. split.
- apply tb_ule_Some, Rmax_le_iff. lra.
- intros z [Fz| ->] Hz; [|intros s _; exact I].
  pose proof (Min z (or_introl Fz)) as M1. pose proof (Min' z (or_introl Fz)) as M2.
  rewrite (bound_finite _ Fz), (bound_finite _ Fw), !tb_ule_Some in M1.
  rewrite (bound_finite _ Fz), (bound_finite _ Fw'), !tb_ule_Some in M2.
  rewrite (bound_finite _ Fz), tb_ule_Some in Hz |- *.
  pose proof (Rmax_l u v). pose proof (Rmax_r u v).
  apply Rmax_le_iff. split; [apply M1 | apply M2]; lra.
Qed.

(** The same for the negated lanes of values rounded down and [fmin]. *)
Lemma tb_lane_min :
  forall first u v w w', least_lane (Some (- u)) (opp w) -> least_lane (Some (- v)) (opp w') ->
  is_finite w = true -> is_finite w' = true ->
  least_lane (Some (- Rmin u v)) (opp (fmin first w w')).
Proof.
intros first u v w w' (_ & Le & Min) (_ & Le' & Min') Fw Fw'.
destruct (tb_fmin_fin first w w' Fw Fw') as [Fm Em].
assert (Fo : forall a, is_finite a = true -> bound (opp a) = Some (- B2R a)).
{ intros a Fa. rewrite bound_finite by (rewrite is_finite_opp; exact Fa).
  rewrite B2R_opp. reflexivity. }
rewrite (Fo _ Fw), tb_ule_Some in Le. rewrite (Fo _ Fw'), tb_ule_Some in Le'.
pose proof (Rmin_l (B2R w) (B2R w')). pose proof (Rmin_r (B2R w) (B2R w')).
pose proof (Rmin_l u v). pose proof (Rmin_r u v).
split; [left; rewrite is_finite_opp; exact Fm|]. rewrite (Fo _ Fm), Em. split.
- apply tb_ule_Some.
  assert (Rmin (B2R w) (B2R w') <= Rmin u v) by (apply le_Rmin_iff; lra). lra.
- intros z [Fz| ->] Hz; [|intros s _; exact I].
  pose proof (Min z (or_introl Fz)) as M1. pose proof (Min' z (or_introl Fz)) as M2.
  rewrite (bound_finite _ Fz), (Fo _ Fw), !tb_ule_Some in M1.
  rewrite (bound_finite _ Fz), (Fo _ Fw'), !tb_ule_Some in M2.
  rewrite (bound_finite _ Fz), tb_ule_Some in Hz |- *.
  assert (- B2R z <= Rmin (B2R w) (B2R w')).
  { apply le_Rmin_iff. split; [pose proof (M1 ltac:(lra)) | pose proof (M2 ltac:(lra))]; lra. }
  lra.
Qed.

(** [itv (set_dec z d)] is [z] for a decoration other than [ill]: [z]
    itself, or [EMPTY] when [z] is empty, which then is [z]. *)
Lemma tb_set_dec_itv :
  forall z d, valid z -> d <> Ill -> itv (DecInterval.set_dec z d) = z.
Proof.
intros z d Hz Hd. destruct (Interval.is_empty z) eqn:E.
- rewrite (set_dec_empty_any z d E Hd). cbn [itv DecInterval.EMPTY].
  symmetry. exact (valid_empty_eq z Hz E).
- unfold DecInterval.set_dec. rewrite E.
  destruct d; try congruence; cbn [dec_eqb discriminant Z.eqb negb andb];
    try reflexivity.
  destruct (Interval.is_common_interval z); reflexivity.
Qed.

(** ** Forms that need no MPFR *)

Lemma br_full_encl :
  forall D f x, (forall r, mem r x -> D r -> -1 <= f r <= 1) ->
  encloses (image_dom D f x) (Interval.const_interval (opp (of_u64 1)) (of_u64 1)).
Proof.
intros D f x H. unfold Interval.const_interval.
apply (tb_encl_lanes _ _ _ 1 1 tb_lane_m_one tb_lane_one); [lra|].
intros s (r & Hr & Dr & ->). pose proof (H r Hr Dr). lra.
Qed.

Lemma br_full_tight :
  forall D f x, (forall r, mem r x -> D r -> -1 <= f r <= 1) ->
  (exists r t, mem r x /\ D r /\ f r = 1 /\ mem t x /\ D t /\ f t = -1) ->
  is_tightest (image_dom D f x) (Interval.const_interval (opp (of_u64 1)) (of_u64 1)).
Proof.
intros D f x H (r & t & Hr & Dr & Er & Ht & Dt & Et). unfold Interval.const_interval.
apply tightest_lanes_lub.
- exists (f r), r. split; [exact Hr | split; [exact Dr | reflexivity]].
- (* -1 is attained at [t], and is the least value. *)
  exists (Some 1). split; [|exact tb_lane_m_one].
  apply tight_lub, tight_Some. split.
  + exists t. split; [exact Ht | split; [exact Dt | lra]].
  + intros s (u & Hu & Du & Hs). pose proof (H u Hu Du). lra.
- exists (Some 1). split; [|exact tb_lane_one].
  apply tight_lub, tight_Some. split.
  + exists r. split; [exact Hr | split; [exact Dr | lra]].
  + intros s (u & Hu & Du & ->). pose proof (H u Hu Du). lra.
Qed.

Lemma br_entire_encl : forall D f x, encloses (image_dom D f x) Interval.ENTIRE.
Proof.
intros D f x. unfold Interval.ENTIRE, Interval.const_interval.
change (opp (B754_infinity true)) with (B754_infinity false : f64).
split.
- unfold valid. cbn. right. split; [reflexivity | split; discriminate].
- intros s _. unfold mem. cbn. split; reflexivity.
Qed.

Lemma br_entire_tight :
  forall D f x,
  (forall M, exists r, mem r x /\ D r /\ M <= f r) ->
  (forall M, exists r, mem r x /\ D r /\ f r <= - M) ->
  is_tightest (image_dom D f x) Interval.ENTIRE.
Proof.
intros D f x Hup Hdn. unfold Interval.ENTIRE, Interval.const_interval.
change (opp (B754_infinity true)) with (B754_infinity false : f64).
apply tightest_lanes_lub.
- destruct (Hup 0) as (r & Hr & Dr & _).
  exists (f r), r. split; [exact Hr | split; [exact Dr | reflexivity]].
- apply lane_ok_inf. intros M. destruct (Hdn M) as (r & Hr & Dr & HM).
  exists (- f r). split; [|lra].
  exists r. split; [exact Hr | split; [exact Dr | apply Ropp_involutive]].
- apply lane_ok_inf. intros M. destruct (Hup M) as (r & Hr & Dr & HM).
  exists (f r). split; [|exact HM].
  exists r. split; [exact Hr | split; [exact Dr | reflexivity]].
Qed.

(** ** Forms with MPFR *)

Section Branch.

Variables (emin emax : Z) (m : mpfr) (D : R -> Prop) (f : R -> R)
  (g : mpfr_rnd -> mpfr_t -> mpfr_t).

Hypothesis Hrange : range_ok emin emax.
Hypothesis Hget : get_d_ok emin emax m.
Hypothesis Hg : mpfr_correct emin emax D f g.

Lemma br_inc_encl :
  forall x, finite_itv x ->
  D (B2R (Interval.inf_raw x)) -> D (B2R (Interval.sup_raw x)) ->
  (forall r, mem r x -> D r ->
   f (B2R (Interval.inf_raw x)) <= f r <= f (B2R (Interval.sup_raw x))) ->
  encloses (image_dom D f x)
    (Interval.with_infsup_raw (mpfr_fn m g RNDD (Interval.inf_raw x))
       (mpfr_fn m g RNDU (Interval.sup_raw x))).
Proof using Hrange Hget Hg.
intros x Hfx Da Db Hf.
pose proof (tb_mem_inf x Hfx) as Ma.
destruct Hfx as (_ & _ & Fa & Fb).
unfold Interval.with_infsup_raw, Generic.constant.
apply (tb_encl_lanes _ _ _ (- f (B2R (Interval.inf_raw x))) (f (B2R (Interval.sup_raw x)))).
- apply round_dn_lane. exact (mpfr_fn_correct emin emax m D f g Hrange Hget Hg RNDD _ Fa Da).
- apply round_up_lane. exact (mpfr_fn_correct emin emax m D f g Hrange Hget Hg RNDU _ Fb Db).
- pose proof (Hf _ Ma Da). lra.
- intros s (r & Hr & Dr & ->). pose proof (Hf r Hr Dr). lra.
Qed.

Lemma br_dec_encl :
  forall x, finite_itv x ->
  D (B2R (Interval.inf_raw x)) -> D (B2R (Interval.sup_raw x)) ->
  (forall r, mem r x -> D r ->
   f (B2R (Interval.sup_raw x)) <= f r <= f (B2R (Interval.inf_raw x))) ->
  encloses (image_dom D f x)
    (Interval.with_infsup_raw (mpfr_fn m g RNDD (Interval.sup_raw x))
       (mpfr_fn m g RNDU (Interval.inf_raw x))).
Proof using Hrange Hget Hg.
intros x Hfx Da Db Hf.
pose proof (tb_mem_inf x Hfx) as Ma.
destruct Hfx as (_ & _ & Fa & Fb).
unfold Interval.with_infsup_raw, Generic.constant.
apply (tb_encl_lanes _ _ _ (- f (B2R (Interval.sup_raw x))) (f (B2R (Interval.inf_raw x)))).
- apply round_dn_lane. exact (mpfr_fn_correct emin emax m D f g Hrange Hget Hg RNDD _ Fb Db).
- apply round_up_lane. exact (mpfr_fn_correct emin emax m D f g Hrange Hget Hg RNDU _ Fa Da).
- pose proof (Hf _ Ma Da). lra.
- intros s (r & Hr & Dr & ->). pose proof (Hf r Hr Dr). lra.
Qed.

Lemma br_max_encl :
  forall first x, finite_itv x ->
  D (B2R (Interval.inf_raw x)) -> D (B2R (Interval.sup_raw x)) ->
  (forall r, mem r x -> D r -> -1 <= f r <= 1) ->
  (forall r, mem r x -> D r ->
   Rmin (f (B2R (Interval.inf_raw x))) (f (B2R (Interval.sup_raw x))) <= f r <= 1) ->
  encloses (image_dom D f x)
    (Interval.with_infsup_raw
       (fmin first (mpfr_fn m g RNDD (Interval.inf_raw x))
          (mpfr_fn m g RNDD (Interval.sup_raw x)))
       (of_u64 1)).
Proof using Hrange Hget Hg.
intros first x Hfx Da Db H1 Hf.
pose proof (tb_mem_inf x Hfx) as Ma. pose proof (tb_mem_sup x Hfx) as Mb.
destruct Hfx as (_ & _ & Fa & Fb).
pose proof (mpfr_fn_correct emin emax m D f g Hrange Hget Hg RNDD _ Fa Da) as Ra.
pose proof (mpfr_fn_correct emin emax m D f g Hrange Hget Hg RNDD _ Fb Db) as Rb.
unfold Interval.with_infsup_raw, Generic.constant.
apply (tb_encl_lanes _ _ _
  (- Rmin (f (B2R (Interval.inf_raw x))) (f (B2R (Interval.sup_raw x)))) 1).
- (* [f a] and [f b] are at least -1, so their roundings are finite. *)
  apply tb_lane_min.
  + exact (round_dn_lane _ _ Ra).
  + exact (round_dn_lane _ _ Rb).
  + exact (tb_rd_finite _ _ Ra (proj1 (H1 _ Ma Da))).
  + exact (tb_rd_finite _ _ Rb (proj1 (H1 _ Mb Db))).
- exact tb_lane_one.
- pose proof (H1 _ Ma Da).
  pose proof (Rmin_l (f (B2R (Interval.inf_raw x))) (f (B2R (Interval.sup_raw x)))). lra.
- intros s (r & Hr & Dr & ->). pose proof (Hf r Hr Dr). lra.
Qed.

Lemma br_min_encl :
  forall first x, finite_itv x ->
  D (B2R (Interval.inf_raw x)) -> D (B2R (Interval.sup_raw x)) ->
  (forall r, mem r x -> D r -> -1 <= f r <= 1) ->
  (forall r, mem r x -> D r ->
   -1 <= f r <= Rmax (f (B2R (Interval.inf_raw x))) (f (B2R (Interval.sup_raw x)))) ->
  encloses (image_dom D f x)
    (Interval.with_infsup_raw (opp (of_u64 1))
       (fmax first (mpfr_fn m g RNDU (Interval.inf_raw x))
          (mpfr_fn m g RNDU (Interval.sup_raw x)))).
Proof using Hrange Hget Hg.
intros first x Hfx Da Db H1 Hf.
pose proof (tb_mem_inf x Hfx) as Ma. pose proof (tb_mem_sup x Hfx) as Mb.
destruct Hfx as (_ & _ & Fa & Fb).
pose proof (mpfr_fn_correct emin emax m D f g Hrange Hget Hg RNDU _ Fa Da) as Ra.
pose proof (mpfr_fn_correct emin emax m D f g Hrange Hget Hg RNDU _ Fb Db) as Rb.
unfold Interval.with_infsup_raw, Generic.constant.
apply (tb_encl_lanes _ _ _ 1
  (Rmax (f (B2R (Interval.inf_raw x))) (f (B2R (Interval.sup_raw x))))).
- exact tb_lane_m_one.
- (* [f a] and [f b] are at most 1, so their roundings are finite. *)
  apply tb_lane_max.
  + exact (round_up_lane _ _ Ra).
  + exact (round_up_lane _ _ Rb).
  + exact (tb_ru_finite _ _ Ra (proj2 (H1 _ Ma Da))).
  + exact (tb_ru_finite _ _ Rb (proj2 (H1 _ Mb Db))).
- pose proof (H1 _ Ma Da).
  pose proof (Rmax_l (f (B2R (Interval.inf_raw x))) (f (B2R (Interval.sup_raw x)))). lra.
- intros s (r & Hr & Dr & ->). pose proof (Hf r Hr Dr). lra.
Qed.

Lemma br_inc_tight :
  forall x, finite_itv x -> (forall r, mem r x -> D r) ->
  (forall r t, mem r x -> mem t x -> r <= t -> f r <= f t) ->
  is_tightest (image_dom D f x)
    (Interval.with_infsup_raw (mpfr_fn m g RNDD (Interval.inf_raw x))
       (mpfr_fn m g RNDU (Interval.sup_raw x))).
Proof using Hrange Hget Hg.
intros x Hfx HD Hmono.
pose proof (tb_mem_inf x Hfx) as Ma. pose proof (tb_mem_sup x Hfx) as Mb.
pose proof (fun r => proj1 (finite_itv_mem x r Hfx)) as Hab.
destruct Hfx as (_ & _ & Fa & Fb).
unfold Interval.with_infsup_raw, Generic.constant.
apply tightest_lanes_lub.
- exists (f (B2R (Interval.inf_raw x))), (B2R (Interval.inf_raw x)).
  split; [exact Ma | split; [exact (HD _ Ma) | reflexivity]].
- (* [f a] is the least value, and [f_rd a] is it rounded down, which
     [round_dn_lane] turns into a lane also when it overflows. *)
  exists (Some (- f (B2R (Interval.inf_raw x)))). split.
  + apply tight_lub, tight_Some. split.
    * exists (B2R (Interval.inf_raw x)).
      split; [exact Ma | split; [exact (HD _ Ma) | apply Ropp_involutive]].
    * intros s (r & Hr & _ & Hs).
      pose proof (Hmono _ r Ma Hr (proj1 (Hab r Hr))). lra.
  + apply round_dn_lane.
    exact (mpfr_fn_correct emin emax m D f g Hrange Hget Hg RNDD _ Fa (HD _ Ma)).
- (* [f b] is the largest value, and [f_ru b] is it rounded up. *)
  exists (Some (f (B2R (Interval.sup_raw x)))). split.
  + apply tight_lub, tight_Some. split.
    * exists (B2R (Interval.sup_raw x)).
      split; [exact Mb | split; [exact (HD _ Mb) | reflexivity]].
    * intros s (r & Hr & _ & ->). exact (Hmono r _ Hr Mb (proj2 (Hab r Hr))).
  + apply round_up_lane.
    exact (mpfr_fn_correct emin emax m D f g Hrange Hget Hg RNDU _ Fb (HD _ Mb)).
Qed.

Lemma br_dec_tight :
  forall x, finite_itv x -> (forall r, mem r x -> D r) ->
  (forall r t, mem r x -> mem t x -> r <= t -> f t <= f r) ->
  is_tightest (image_dom D f x)
    (Interval.with_infsup_raw (mpfr_fn m g RNDD (Interval.sup_raw x))
       (mpfr_fn m g RNDU (Interval.inf_raw x))).
Proof using Hrange Hget Hg.
intros x Hfx HD Hmono.
pose proof (tb_mem_inf x Hfx) as Ma. pose proof (tb_mem_sup x Hfx) as Mb.
pose proof (fun r => proj1 (finite_itv_mem x r Hfx)) as Hab.
destruct Hfx as (_ & _ & Fa & Fb).
unfold Interval.with_infsup_raw, Generic.constant.
apply tightest_lanes_lub.
- exists (f (B2R (Interval.inf_raw x))), (B2R (Interval.inf_raw x)).
  split; [exact Ma | split; [exact (HD _ Ma) | reflexivity]].
- (* [f b] is the least value, and [f_rd b] is it rounded down. *)
  exists (Some (- f (B2R (Interval.sup_raw x)))). split.
  + apply tight_lub, tight_Some. split.
    * exists (B2R (Interval.sup_raw x)).
      split; [exact Mb | split; [exact (HD _ Mb) | apply Ropp_involutive]].
    * intros s (r & Hr & _ & Hs).
      pose proof (Hmono r _ Hr Mb (proj2 (Hab r Hr))). lra.
  + apply round_dn_lane.
    exact (mpfr_fn_correct emin emax m D f g Hrange Hget Hg RNDD _ Fb (HD _ Mb)).
- (* [f a] is the largest value, and [f_ru a] is it rounded up. *)
  exists (Some (f (B2R (Interval.inf_raw x)))). split.
  + apply tight_lub, tight_Some. split.
    * exists (B2R (Interval.inf_raw x)).
      split; [exact Ma | split; [exact (HD _ Ma) | reflexivity]].
    * intros s (r & Hr & _ & ->). exact (Hmono _ r Ma Hr (proj1 (Hab r Hr))).
  + apply round_up_lane.
    exact (mpfr_fn_correct emin emax m D f g Hrange Hget Hg RNDU _ Fa (HD _ Ma)).
Qed.

Lemma br_max_tight :
  forall first x, finite_itv x -> (forall r, mem r x -> D r) ->
  (forall r, mem r x -> -1 <= f r <= 1) ->
  (forall r, mem r x ->
   Rmin (f (B2R (Interval.inf_raw x))) (f (B2R (Interval.sup_raw x))) <= f r <= 1) ->
  (exists t, mem t x /\ f t = 1) ->
  is_tightest (image_dom D f x)
    (Interval.with_infsup_raw
       (fmin first (mpfr_fn m g RNDD (Interval.inf_raw x))
          (mpfr_fn m g RNDD (Interval.sup_raw x)))
       (of_u64 1)).
Proof using Hrange Hget Hg.
intros first x Hfx HD H1 Hf (t & Ht & Et).
pose proof (tb_mem_inf x Hfx) as Ma. pose proof (tb_mem_sup x Hfx) as Mb.
destruct Hfx as (_ & _ & Fa & Fb).
pose proof (mpfr_fn_correct emin emax m D f g Hrange Hget Hg RNDD _ Fa (HD _ Ma)) as Ra.
pose proof (mpfr_fn_correct emin emax m D f g Hrange Hget Hg RNDD _ Fb (HD _ Mb)) as Rb.
unfold Interval.with_infsup_raw, Generic.constant.
apply tightest_lanes_lub.
- exists (f t), t. split; [exact Ht | split; [exact (HD _ Ht) | reflexivity]].
- (* The least value is the smaller of [f a] and [f b]. *)
  exists (Some (- Rmin (f (B2R (Interval.inf_raw x))) (f (B2R (Interval.sup_raw x))))).
  split.
  + apply tight_lub, tight_Some. split.
    * rewrite Ropp_involutive.
      destruct (Rle_or_lt (f (B2R (Interval.inf_raw x))) (f (B2R (Interval.sup_raw x))))
        as [Hle|Hlt].
      -- rewrite Rmin_left by exact Hle.
         exists (B2R (Interval.inf_raw x)).
         split; [exact Ma | split; [exact (HD _ Ma) | reflexivity]].
      -- rewrite Rmin_right by lra.
         exists (B2R (Interval.sup_raw x)).
         split; [exact Mb | split; [exact (HD _ Mb) | reflexivity]].
    * intros s (r & Hr & _ & Hs). pose proof (Hf r Hr). lra.
  + apply tb_lane_min.
    * exact (round_dn_lane _ _ Ra).
    * exact (round_dn_lane _ _ Rb).
    * exact (tb_rd_finite _ _ Ra (proj1 (H1 _ Ma))).
    * exact (tb_rd_finite _ _ Rb (proj1 (H1 _ Mb))).
- (* The largest value is 1, at [t]. *)
  exists (Some 1). split; [|exact tb_lane_one].
  apply tight_lub, tight_Some. split.
  + exists t. split; [exact Ht | split; [exact (HD _ Ht) | lra]].
  + intros s (r & Hr & _ & ->). exact (proj2 (H1 r Hr)).
Qed.

Lemma br_min_tight :
  forall first x, finite_itv x -> (forall r, mem r x -> D r) ->
  (forall r, mem r x -> -1 <= f r <= 1) ->
  (forall r, mem r x ->
   -1 <= f r <= Rmax (f (B2R (Interval.inf_raw x))) (f (B2R (Interval.sup_raw x)))) ->
  (exists t, mem t x /\ f t = -1) ->
  is_tightest (image_dom D f x)
    (Interval.with_infsup_raw (opp (of_u64 1))
       (fmax first (mpfr_fn m g RNDU (Interval.inf_raw x))
          (mpfr_fn m g RNDU (Interval.sup_raw x)))).
Proof using Hrange Hget Hg.
intros first x Hfx HD H1 Hf (t & Ht & Et).
pose proof (tb_mem_inf x Hfx) as Ma. pose proof (tb_mem_sup x Hfx) as Mb.
destruct Hfx as (_ & _ & Fa & Fb).
pose proof (mpfr_fn_correct emin emax m D f g Hrange Hget Hg RNDU _ Fa (HD _ Ma)) as Ra.
pose proof (mpfr_fn_correct emin emax m D f g Hrange Hget Hg RNDU _ Fb (HD _ Mb)) as Rb.
unfold Interval.with_infsup_raw, Generic.constant.
apply tightest_lanes_lub.
- exists (f t), t. split; [exact Ht | split; [exact (HD _ Ht) | reflexivity]].
- (* The least value is -1, at [t]. *)
  exists (Some 1). split; [|exact tb_lane_m_one].
  apply tight_lub, tight_Some. split.
  + exists t. split; [exact Ht | split; [exact (HD _ Ht) | lra]].
  + intros s (r & Hr & _ & Hs). pose proof (H1 r Hr). lra.
- (* The largest value is the larger of [f a] and [f b]. *)
  exists (Some (Rmax (f (B2R (Interval.inf_raw x))) (f (B2R (Interval.sup_raw x))))).
  split.
  + apply tight_lub, tight_Some. split.
    * destruct (Rle_or_lt (f (B2R (Interval.inf_raw x))) (f (B2R (Interval.sup_raw x))))
        as [Hle|Hlt].
      -- rewrite Rmax_right by exact Hle.
         exists (B2R (Interval.sup_raw x)).
         split; [exact Mb | split; [exact (HD _ Mb) | reflexivity]].
      -- rewrite Rmax_left by lra.
         exists (B2R (Interval.inf_raw x)).
         split; [exact Ma | split; [exact (HD _ Ma) | reflexivity]].
    * intros s (r & Hr & _ & ->). exact (proj2 (Hf r Hr)).
  + apply tb_lane_max.
    * exact (round_up_lane _ _ Ra).
    * exact (round_up_lane _ _ Rb).
    * exact (tb_ru_finite _ _ Ra (proj2 (H1 _ Ma))).
    * exact (tb_ru_finite _ _ Rb (proj2 (H1 _ Mb))).
Qed.

End Branch.

(** ** Decorations

    [set_dec z (dec_min (dec x) e)] for an enclosure [z] and a decoration
    [e] that is [trv], or [com] for an [x] in the domain: the result
    encloses the image, is tightest if [z] is, and its decoration holds;
    it is the strongest unless [e] is [trv] for a nonempty [x] in the
    domain, which [tan] returns when its reduction is not exact. *)
Theorem trig_set_dec_correct :
  forall D f x z e,
  valid (itv x) -> dec x <> Ill ->
  encloses (image_dom D f (itv x)) z ->
  ((forall r, ~ mem r (itv x)) -> Interval.is_empty z = true) ->
  (forall r, mem r (itv x) -> D r -> continue_in f D r) ->
  e = Trv \/
  (e = Com /\ (forall r, mem r (itv x) -> D r) /\
   (dec x = Com -> Interval.is_common_interval z = true ->
    bounded (fun r => mem r (itv x)))) ->
  let y := DecInterval.set_dec z (dec_min (dec x) e) in
  encloses (image_dom D f (itv x)) (itv y) /\
  (is_tightest (image_dom D f (itv x)) z -> is_tightest (image_dom D f (itv x)) (itv y)) /\
  (exists d, p_dom D d f (itv x) (itv y) /\ dec y = dec_min d (dec x)) /\
  ((e = Trv -> ~ ((exists r, mem r (itv x)) /\ forall r, mem r (itv x) -> D r)) ->
   exists d, strongest_dom D d f (itv x) (itv y) /\ dec y = dec_min d (dec x)).
Proof.
intros D f x z e Hx Hd He Hemp Hc He'. cbv zeta.
pose proof (proj1 He) as Hz.
assert (Hde : dec_min (dec x) e <> Ill).
{ apply dec_min_not_Ill; [exact Hd|]. destruct He' as [-> | (-> & _)]; discriminate. }
(* [set_dec] keeps the interval [z], so enclosure and tightness carry
   over. *)
rewrite (tb_set_dec_itv z _ Hz Hde).
split; [exact He|]. split; [intros Ht; exact Ht|].
destruct He' as [Ee | (Ee & HD & Hb)]; subst e.
- (* [e = trv]: [set_dec] keeps [trv] for any [z], which always holds, and
     is the strongest if not even [def] holds. *)
  rewrite (ed_dec_min_Trv_r _ Hd).
  assert (Edy : dec (DecInterval.set_dec z Trv) = Trv).
  { destruct (Interval.is_empty z) eqn:Ez0.
    - rewrite (set_dec_empty_any z Trv Ez0 ltac:(discriminate)). reflexivity.
    - rewrite (set_dec_keep z Trv Ez0 ltac:(discriminate) ltac:(intros E; discriminate E)).
      reflexivity. }
  rewrite Edy.
  assert (E1 : Trv = dec_min Trv (dec x)) by (symmetry; now apply dec_min_Trv_l).
  split.
  + exists Trv. split; [exact I | exact E1].
  + intros Hnd. exists Trv. split; [apply strongest_dom_Trv; exact (Hnd eq_refl) | exact E1].
- (* [e = com]: [x] is a subset of [D], and [set_dec] gets [dec x]. The
     strongest decoration is found as in [elem_set_dec_correct]. *)
  rewrite dec_min_Com_r.
  assert (Hs : exists d, strongest_dom D d f (itv x) z /\
                 dec (DecInterval.set_dec z (dec x)) = dec_min d (dec x)).
  { destruct (Interval.is_empty z) eqn:Ez0.
    - (* [z] is empty, so [x] has no real, as [f] maps one into [z]. *)
      rewrite (set_dec_empty_any z (dec x) Ez0 Hd). cbn [dec DecInterval.EMPTY].
      exists Trv. split; [|symmetry; now apply dec_min_Trv_l].
      apply strongest_dom_Trv. intros ((r & Hr) & _).
      apply (mem_empty z (f r) Hz Ez0). apply (proj2 He).
      exists r. split; [exact Hr|]. split; [exact (HD r Hr) | reflexivity].
    - (* [z] is nonempty, so [x] is, and [dac] holds: [f] is continuous
         relative to [D], so relative to [x]. *)
      assert (Nx : exists r, mem r (itv x)).
      { destruct (Interval.is_empty (itv x)) eqn:Ex;
          [|exact (nonempty_mem _ Hx Ex)].
        (* [destruct] has replaced [Interval.is_empty z] by [false] in
           [Hemp]. *)
        discriminate (Hemp (fun r Hr => mem_empty _ r Hx Ex Hr)). }
      assert (Hdac : p_dom D Dac f (itv x) z).
      { cbn [p_dom]. split; [exact Nx|]. split; [exact HD|].
        intros r Hr. exact (ed_continue_in_sub f D _ r (Hc r Hr (HD r Hr)) HD). }
      destruct (classic (dec x = Com)) as [Edx|Ndx].
      + (* [x] is [com]: [com] holds if [z] is common, as [x] is then
           bounded, and otherwise [z] is unbounded, and [set_dec] lowers
           [com] to [dac]. *)
        rewrite Edx. destruct (Interval.is_common_interval z) eqn:Cz.
        * rewrite (set_dec_keep z Com Ez0 ltac:(discriminate) (fun _ => Cz)).
          cbn [dec DecInterval.new_unchecked].
          exists Com. split; [|reflexivity].
          apply strongest_dom_Com. cbn [p_dom].
          split; [exact Nx|]. split; [exact HD|].
          split; [exact (Hb Edx eq_refl)|].
          split; [intros r Hr; exact (Hc r Hr (HD r Hr))|].
          exact (common_bounded z Cz).
        * rewrite (set_dec_lower z Com Ez0 Cz ltac:(discriminate)).
          cbn [dec DecInterval.new_unchecked].
          exists Dac. split; [|reflexivity].
          apply strongest_dom_Dac; [exact Hdac|].
          intros (_ & _ & _ & _ & Bz).
          rewrite (bounded_common z Hz Ez0 Bz) in Cz. discriminate Cz.
      + (* [x] is not [com]: [set_dec] keeps [dec x], which is
           [dec_min d (dec x)] for [d] either [com] or [dac]. *)
        rewrite (set_dec_keep z (dec x) Ez0 Hd (fun E => False_ind _ (Ndx E))).
        cbn [dec DecInterval.new_unchecked].
        destruct (classic (p_dom D Com f (itv x) z)) as [Pc|Pc].
        * exists Com.
          split; [now apply strongest_dom_Com | symmetry; apply dec_min_Com_l].
        * exists Dac.
          split; [now apply strongest_dom_Dac|].
          symmetry. now apply dec_min_Dac_l. }
  destruct Hs as (d & Hsd & Ed).
  split; [exists d; split; [exact (proj1 Hsd) | exact Ed]|].
  intros _. exists d. split; [exact Hsd | exact Ed].
Qed.
