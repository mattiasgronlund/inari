(** * [asin], [acosh] and [acos] of intervals and decorated intervals

    [Interval::asin] and [Interval::acosh] have the same form: they
    intersect their argument with a closed domain [DOM] = [[c, d]], which
    is [[-1, 1]] and [[1, +inf]], and return [[f_rd(a), f_ru(b)]] for the
    intersection [[a, b]] if it is nonempty, where [f] is increasing and
    continuous on the domain. The decoration is [com] if the argument is a
    subset of [DOM], and [trv] otherwise. [closed_inc] is that form, and
    [closed_inc_correct] and [dec_closed_inc_correct] are proved for it
    once. [Interval::acos] has the same form with [f] decreasing, which
    returns [[f_rd(b), f_ru(a)]]. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Integer Sign MaxMin AddSub
  ValidSetOp DecBinary MpfrRound Interior ElemDec TrigReal.

Open Scope R_scope.

(** The form of [Interval.asin_impl] and [Interval.acosh_impl], for the
    domain [DOM] and the functions [f_rd] and [f_ru]: [Interval.asin_impl m]
    is [closed_inc] of [[-1, 1]], [asin_rd m] and [asin_ru m] by
    definition, and [Interval.acosh_impl m] that of [[1, +inf]],
    [acosh_rd m] and [acosh_ru m]. *)
Definition closed_inc (DOM : Interval) (f_rd f_ru : f64 -> f64) (self : Interval) :
    Interval * Decoration :=
  let x := Interval.intersection self DOM in
  if Interval.is_empty x then (x, Trv)
  else
    let y :=
      Interval.with_infsup_raw (f_rd (Interval.inf_raw x)) (f_ru (Interval.sup_raw x)) in
    let d := if Interval.subset self DOM then Com else Trv in
    (y, d).

(** ** The form of [closed_inc] and [Interval.acos_impl] *)

(** [closed_inc] and [Interval.acos_impl] differ only in how they compute
    the result from the intersection [x] of the argument with [DOM]: that
    is [h x] here. *)
Definition closed_gen (DOM : Interval) (h : Interval -> Interval) (self : Interval) :
    Interval * Decoration :=
  let x := Interval.intersection self DOM in
  if Interval.is_empty x then (x, Trv)
  else (h x, if Interval.subset self DOM then Com else Trv).

Lemma cl_closed_inc_eq :
  forall DOM f_rd f_ru,
  closed_inc DOM f_rd f_ru =
  closed_gen DOM
    (fun x => Interval.with_infsup_raw (f_rd (Interval.inf_raw x)) (f_ru (Interval.sup_raw x))).
Proof.
reflexivity.
Qed.

Lemma cl_acos_eq :
  forall m,
  Interval.acos_impl m =
  closed_gen dom_unit
    (fun x =>
       Interval.with_infsup_raw (acos_rd m (Interval.sup_raw x)) (acos_ru m (Interval.inf_raw x))).
Proof.
reflexivity.
Qed.

(** ** The bounds of a nonempty interval *)

Lemma cl_ub_cases :
  forall x, valid x -> Interval.is_empty x = false ->
  is_finite (Interval.sup_raw x) = true \/ Interval.sup_raw x = B754_infinity false.
Proof.
intros x Hx E. exact (proj1 (proj2 (valid_nonempty x Hx E))).
Qed.

Lemma cl_mem_iff :
  forall x r, valid x -> Interval.is_empty x = false ->
  mem r x <-> in_bounds (bound (Interval.inf_raw x)) (bound (Interval.sup_raw x)) r.
Proof.
intros x r Hx E. destruct (valid_nonempty x Hx E) as (La & Ub & _).
exact (mem_bounds x r La Ub).
Qed.

(** A nonempty interval whose reals are at least [lo] has a finite lower
    bound: otherwise [min(lo - 1, b)] would be in it. *)
Lemma cl_inf_finite :
  forall x lo, valid x -> Interval.is_empty x = false ->
  (forall r, mem r x -> lo <= r) -> is_finite (Interval.inf_raw x) = true.
Proof.
intros x lo Hx E Hlo.
destruct (valid_nonempty x Hx E) as ([Fa|Ea] & _ & _); [exact Fa|]. exfalso.
set (t := match bound (Interval.sup_raw x) with
          | Some b => Rmin (lo - 1) b | None => lo - 1 end).
assert (Ht : mem t x).
{ apply (cl_mem_iff x t Hx E). unfold Interval.inf_raw. rewrite Ea.
  split; [exact I|]. unfold t.
  destruct (bound (Interval.sup_raw x)); [apply Rmin_r | exact I]. }
apply Hlo in Ht. revert Ht. unfold t.
destruct (bound (Interval.sup_raw x)) as [b|]; intros Ht;
  [pose proof (Rmin_l (lo - 1) b)|]; lra.
Qed.

(** The same for the upper bound, with [max(hi + 1, a)]. *)
Lemma cl_sup_finite :
  forall x hi, valid x -> Interval.is_empty x = false ->
  (forall r, mem r x -> r <= hi) -> is_finite (Interval.sup_raw x) = true.
Proof.
intros x hi Hx E Hhi.
destruct (valid_nonempty x Hx E) as (_ & [Fb|Eb] & _); [exact Fb|]. exfalso.
set (t := match bound (Interval.inf_raw x) with
          | Some a => Rmax (hi + 1) a | None => hi + 1 end).
assert (Ht : mem t x).
{ apply (cl_mem_iff x t Hx E). unfold Interval.sup_raw. rewrite Eb.
  split; [|exact I]. unfold t.
  destruct (bound (Interval.inf_raw x)); [apply Rmax_r | exact I]. }
apply Hhi in Ht. revert Ht. unfold t.
destruct (bound (Interval.inf_raw x)) as [a|]; intros Ht;
  [pose proof (Rmax_l (hi + 1) a)|]; lra.
Qed.

Lemma cl_inf_mem :
  forall x, valid x -> Interval.is_empty x = false ->
  is_finite (Interval.inf_raw x) = true -> mem (B2R (Interval.inf_raw x)) x.
Proof.
intros x Hx E Fa. destruct (valid_nonempty x Hx E) as (_ & Ub & O).
apply (cl_mem_iff x _ Hx E).
change (opp (fst (rep x))) with (Interval.inf_raw x) in O.
change (snd (rep x)) with (Interval.sup_raw x) in O, Ub.
rewrite (bound_finite _ Fa) in *. split; [apply Rle_refl|].
destruct Ub as [Fb|Eb].
- rewrite (bound_finite _ Fb) in *. exact O.
- rewrite Eb. exact I.
Qed.

Lemma cl_sup_mem :
  forall x, valid x -> Interval.is_empty x = false ->
  is_finite (Interval.sup_raw x) = true -> mem (B2R (Interval.sup_raw x)) x.
Proof.
intros x Hx E Fb. destruct (valid_nonempty x Hx E) as (La & _ & O).
apply (cl_mem_iff x _ Hx E).
change (opp (fst (rep x))) with (Interval.inf_raw x) in O, La.
change (snd (rep x)) with (Interval.sup_raw x) in O.
rewrite (bound_finite _ Fb) in *. split; [|apply Rle_refl].
destruct La as [Fa|Ea].
- rewrite (bound_finite _ Fa) in *. exact O.
- rewrite Ea. exact I.
Qed.

Lemma cl_mem_inf :
  forall x r, valid x -> Interval.is_empty x = false ->
  is_finite (Interval.inf_raw x) = true -> mem r x -> B2R (Interval.inf_raw x) <= r.
Proof.
intros x r Hx E Fa Hr. apply (cl_mem_iff x r Hx E) in Hr.
rewrite (bound_finite _ Fa) in Hr. exact (proj1 Hr).
Qed.

Lemma cl_mem_sup :
  forall x r, valid x -> Interval.is_empty x = false ->
  is_finite (Interval.sup_raw x) = true -> mem r x -> r <= B2R (Interval.sup_raw x).
Proof.
intros x r Hx E Fb Hr. apply (cl_mem_iff x r Hx E) in Hr.
rewrite (bound_finite _ Fb) in Hr. exact (proj2 Hr).
Qed.

(** An interval [[a, +inf]] holds every real at or above [a]. *)
Lemma cl_sup_inf_mem :
  forall x t, valid x -> Interval.is_empty x = false ->
  is_finite (Interval.inf_raw x) = true -> Interval.sup_raw x = B754_infinity false ->
  B2R (Interval.inf_raw x) <= t -> mem t x.
Proof.
intros x t Hx E Fa Eb Ht. apply (cl_mem_iff x t Hx E).
rewrite (bound_finite _ Fa), Eb. split; [exact Ht | exact I].
Qed.

(** ** The domain [[c, d]] *)

Lemma cl_dom_lower :
  forall c d r, is_finite c = true -> mem r (Interval.const_interval c d) -> B2R c <= r.
Proof.
intros c d r Fc [H _]. cbn [Interval.const_interval rep fst] in H.
unfold opp in H. rewrite Bopp_involutive in H.
destruct c; try discriminate; exact H.
Qed.

Lemma cl_dom_upper :
  forall c d r, is_finite d = true -> mem r (Interval.const_interval c d) -> r <= B2R d.
Proof.
intros c d r Fd [_ H]. cbn [Interval.const_interval rep snd] in H.
destruct d; try discriminate; exact H.
Qed.

Lemma cl_dom_upper_ok :
  forall c d, is_finite c = true -> valid (Interval.const_interval c d) ->
  is_finite d = true \/ d = B754_infinity false.
Proof.
intros c d Fc H.
assert (E : Interval.is_empty (Interval.const_interval c d) = false).
{ unfold Interval.is_empty. cbn [Interval.const_interval rep fst]. unfold opp.
  destruct c; try discriminate; reflexivity. }
exact (cl_ub_cases _ H E).
Qed.

(** ** Tightest intervals from the extreme values of a set *)

(** [v] is the largest element of [S]. *)
Lemma cl_tight_max :
  forall (S : R -> Prop) v, S v -> (forall s, S s -> s <= v) -> tight (Some v) S.
Proof.
intros S v Hv Hmax s. cbn [below]. split.
- intros Hs. exists v. split; assumption.
- intros (t & Ht & Hs). specialize (Hmax t Ht). lra.
Qed.

(** [u] is the least element of [S], so [-u] is the largest negation of
    one. *)
Lemma cl_tight_min :
  forall (S : R -> Prop) u, S u -> (forall s, S s -> u <= s) ->
  tight (Some (- u)) (fun t => S (- t)).
Proof.
intros S u Hu Hmin. apply cl_tight_max.
- cbv beta. rewrite Ropp_involutive. exact Hu.
- intros s Hs. specialize (Hmin _ Hs). lra.
Qed.

(** [S] has no upper bound. *)
Lemma cl_tight_none :
  forall S : R -> Prop, (forall M, exists s, S s /\ M <= s) -> tight None S.
Proof.
intros S H s. cbn [below]. split; [intros _; apply H | intros _; exact I].
Qed.

(** [with_infsup_raw w0 w1] is stored as [[-w0; w1]]. *)
Lemma cl_tightest :
  forall S lo hi w0 w1, (exists s, S s) ->
  tight lo (fun u => S (- u)) -> tight hi S ->
  least_lane lo (opp w0) -> least_lane hi w1 ->
  is_tightest S (Interval.with_infsup_raw w0 w1).
Proof.
intros S lo hi w0 w1 Hne Hlo Hhi H0 H1.
exact (tightest_lanes S (Interval.with_infsup_raw w0 w1) lo hi Hne Hlo Hhi H0 H1).
Qed.

(** ** [closed_gen] *)

(** The image of [x] under [f] on [D] is that of the intersection of [x]
    with [DOM]. *)
Lemma closed_gen_image :
  forall DOM D f x, valid x -> valid DOM -> (forall r, D r <-> mem r DOM) ->
  forall s,
  image_dom D f x s <-> exists r, mem r (Interval.intersection x DOM) /\ s = f r.
Proof.
intros DOM D f x Hx HDOM HD s. split.
- intros (r & Hr & Dr & ->). exists r. split; [|reflexivity].
  apply (intersection_mem _ _ r Hx HDOM). split; [exact Hr|]. apply HD. exact Dr.
- intros (r & Hr & ->). apply (intersection_mem _ _ r Hx HDOM) in Hr.
  exists r. split; [exact (proj1 Hr)|]. split; [apply HD; exact (proj2 Hr) | reflexivity].
Qed.

(** If [h] returns the tightest interval that contains the image of a
    nonempty subset of [D], [closed_gen] returns the tightest interval that
    contains the image of its argument: for an empty intersection, the
    image is empty. *)
Lemma closed_gen_correct :
  forall DOM D f h, valid DOM -> (forall r, D r <-> mem r DOM) ->
  (forall x, valid x -> Interval.is_empty x = false -> (forall r, mem r x -> D r) ->
   is_tightest (fun s => exists r, mem r x /\ s = f r) (h x)) ->
  forall x, valid x -> is_tightest (image_dom D f x) (fst (closed_gen DOM h x)).
Proof.
intros DOM D f h HDOM HD Hh x Hx.
assert (HX : valid (Interval.intersection x DOM)) by now apply intersection_valid.
apply (is_tightest_ext (fun s => exists r, mem r (Interval.intersection x DOM) /\ s = f r)).
{ intros s. apply iff_sym. exact (closed_gen_image DOM D f x Hx HDOM HD s). }
cbv beta zeta delta [closed_gen].
destruct (Interval.is_empty (Interval.intersection x DOM)) eqn:E; cbn [fst].
- rewrite (valid_empty_eq _ HX E). apply tightest_empty.
  intros u (r & Hr & _). exact (mem_nan Interval.EMPTY r eq_refl Hr).
- apply Hh; [exact HX | exact E |]. intros r Hr.
  apply (intersection_mem _ _ r Hx HDOM) in Hr. apply HD. exact (proj2 Hr).
Qed.

(** The decorated version: [closed_gen] returns [trv] for an empty
    intersection, and otherwise [com] exactly when the argument is a
    subset of [DOM]. Then the argument is the intersection, which is
    bounded if the result is common, as [h] must ensure. *)
Lemma dec_closed_gen_correct :
  forall DOM D f h, valid DOM -> (forall r, D r <-> mem r DOM) ->
  (forall x, valid x -> Interval.is_empty x = false -> (forall r, mem r x -> D r) ->
   is_tightest (fun s => exists r, mem r x /\ s = f r) (h x)) ->
  (forall x, valid x -> Interval.is_empty x = false -> (forall r, mem r x -> D r) ->
   Interval.is_common_interval (h x) = true -> bounded (fun r => mem r x)) ->
  (forall r, D r -> continue_in f D r) ->
  forall x, valid (itv x) ->
  let y := DecInterval.elem_dec_impl (closed_gen DOM h) x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom D f (itv x)) (itv y) /\
    exists e, strongest_dom D e f (itv x) (itv y) /\ dec y = dec_min e (dec x).
Proof.
intros DOM D f h HDOM HD Ht Hb Hc x Hx.
apply elem_dec_impl_correct.
- exact Hx.
- exact (closed_gen_correct DOM D f h HDOM HD Ht (itv x) Hx).
- intros r _ Dr. exact (Hc r Dr).
- cbv beta zeta delta [closed_gen].
  assert (HX : valid (Interval.intersection (itv x) DOM)) by now apply intersection_valid.
  assert (HmX : forall r,
    mem r (Interval.intersection (itv x) DOM) <-> mem r (itv x) /\ D r).
  { intros r. split.
    - intros Hr. apply (intersection_mem _ _ r Hx HDOM) in Hr. destruct Hr as [H1 H2].
      split; [exact H1|]. apply HD. exact H2.
    - intros [H1 H2]. apply (intersection_mem _ _ r Hx HDOM).
      split; [exact H1|]. apply HD. exact H2. }
  destruct (Interval.is_empty (Interval.intersection (itv x) DOM)) eqn:E; cbn [fst snd].
  + (* An empty intersection: [x] has no real in [D]. *)
    left. split; [reflexivity|]. intros [[r Hr] Hsub].
    assert (HrX : mem r (Interval.intersection (itv x) DOM)).
    { apply HmX. split; [exact Hr | exact (Hsub r Hr)]. }
    rewrite (valid_empty_eq _ HX E) in HrX. exact (mem_nan Interval.EMPTY r eq_refl HrX).
  + destruct (Interval.subset (itv x) DOM) eqn:Es.
    * right. assert (Hsub : forall r, mem r (itv x) -> D r).
      { intros r Hr. apply HD. exact (proj1 (subset_mem (itv x) DOM Hx HDOM) Es r Hr). }
      split; [reflexivity|]. split; [exact Hsub|]. intros _ Hcom.
      destruct (Hb _ HX E (fun r Hr => proj2 (proj1 (HmX r) Hr)) Hcom) as [M HM].
      exists M. intros r Hr. apply HM. apply HmX. split; [exact Hr | exact (Hsub r Hr)].
    * left. split; [reflexivity|]. intros [_ Hsub].
      assert (Es' : Interval.subset (itv x) DOM = true).
      { apply (subset_mem (itv x) DOM Hx HDOM). intros r Hr. apply HD. exact (Hsub r Hr). }
      rewrite Es' in Es. discriminate Es.
Qed.

Section ClosedInc.

Variables (emin emax : Z) (m : mpfr) (D : R -> Prop) (f : R -> R)
  (g : mpfr_rnd -> mpfr_t -> mpfr_t) (c d : f64).

Hypothesis Hrange : range_ok emin emax.
Hypothesis Hget : get_d_ok emin emax m.
Hypothesis Hg : mpfr_correct emin emax D f g.
(** The domain is [[c, d]], with [c] finite. *)
Hypothesis Hc : is_finite c = true.
Hypothesis HDOM : valid (Interval.const_interval c d).
Hypothesis HD : forall r, D r <-> mem r (Interval.const_interval c d).
(** If [d] is +inf, MPFR returns +inf there, and [f] has no upper bound. *)
Hypothesis Hd :
  d = B754_infinity false ->
  g RNDU (MInf false) = MInf false /\ forall M, exists r, D r /\ M <= f r.
Hypothesis Hinc : forall r t, D r -> D t -> r <= t -> f r <= f t.
Hypothesis Hcont : forall r, D r -> continue_in f D r.

Lemma cl_D_lower : forall r, D r -> B2R c <= r.
Proof using Hc HD.
intros r Dr. apply (cl_dom_lower c d r Hc). apply HD. exact Dr.
Qed.

(** A nonempty subset [x] of [D] has a finite lower bound in [D]. *)
Lemma cl_inf_D :
  forall x, valid x -> Interval.is_empty x = false -> (forall r, mem r x -> D r) ->
  is_finite (Interval.inf_raw x) = true.
Proof using Hc HD.
intros x Hx E HxD. apply (cl_inf_finite x (B2R c) Hx E).
intros r Hr. apply cl_D_lower. exact (HxD r Hr).
Qed.

(** If a nonempty subset [x] of [D] has no upper bound, [d] is +inf:
    otherwise [max(a, d + 1)] would be in [x] but not in [D]. *)
Lemma cl_sup_inf_d :
  forall x, valid x -> Interval.is_empty x = false -> (forall r, mem r x -> D r) ->
  Interval.sup_raw x = B754_infinity false -> d = B754_infinity false.
Proof using Hc HDOM HD.
intros x Hx E HxD Eb.
destruct (cl_dom_upper_ok c d Hc HDOM) as [Fd|Ed]; [|exact Ed]. exfalso.
pose proof (cl_inf_D x Hx E HxD) as Fa.
set (t := Rmax (B2R (Interval.inf_raw x)) (B2R d + 1)).
assert (Ht : mem t x).
{ apply (cl_sup_inf_mem x t Hx E Fa Eb). apply Rmax_l. }
apply HxD in Ht. apply HD in Ht. apply (cl_dom_upper c d t Fd) in Ht.
pose proof (Rmax_r (B2R (Interval.inf_raw x)) (B2R d + 1)). unfold t in Ht. lra.
Qed.

(** For a nonempty subset [x] = [[a, b]] of [D], [[f_rd(a), f_ru(b)]] is
    the tightest interval that contains the image of [x], as [f] is
    increasing: [f(a)] is the least value. [f(b)] is the largest, or if
    [b] is +inf, the values have no upper bound and [f_ru(+inf)] is +inf. *)
Lemma cl_inc_tight :
  forall x, valid x -> Interval.is_empty x = false -> (forall r, mem r x -> D r) ->
  is_tightest (fun s => exists r, mem r x /\ s = f r)
    (Interval.with_infsup_raw (mpfr_fn m g RNDD (Interval.inf_raw x))
       (mpfr_fn m g RNDU (Interval.sup_raw x))).
Proof using Hrange Hget Hg Hc HDOM HD Hd Hinc.
intros x Hx E HxD.
pose proof (cl_inf_D x Hx E HxD) as Fa.
pose proof (cl_inf_mem x Hx E Fa) as Ma.
assert (Hne : exists s, exists r, mem r x /\ s = f r).
{ exists (f (B2R (Interval.inf_raw x))), (B2R (Interval.inf_raw x)).
  split; [exact Ma | reflexivity]. }
assert (Tlo : tight (Some (- f (B2R (Interval.inf_raw x))))
                (fun u => exists r, mem r x /\ - u = f r)).
{ apply (cl_tight_min (fun s => exists r, mem r x /\ s = f r)).
  - exists (B2R (Interval.inf_raw x)). split; [exact Ma | reflexivity].
  - intros s (r & Hr & ->). apply Hinc.
    + exact (HxD _ Ma).
    + exact (HxD r Hr).
    + exact (cl_mem_inf x r Hx E Fa Hr). }
assert (Llo : least_lane (Some (- f (B2R (Interval.inf_raw x))))
                (opp (mpfr_fn m g RNDD (Interval.inf_raw x)))).
{ apply round_dn_lane.
  exact (mpfr_fn_correct emin emax m D f g Hrange Hget Hg RNDD _ Fa (HxD _ Ma)). }
destruct (cl_ub_cases x Hx E) as [Fb|Eb].
- pose proof (cl_sup_mem x Hx E Fb) as Mb.
  apply (cl_tightest _ _ (Some (f (B2R (Interval.sup_raw x)))) _ _ Hne Tlo).
  + apply cl_tight_max.
    * exists (B2R (Interval.sup_raw x)). split; [exact Mb | reflexivity].
    * intros s (r & Hr & ->). apply Hinc.
      -- exact (HxD r Hr).
      -- exact (HxD _ Mb).
      -- exact (cl_mem_sup x r Hx E Fb Hr).
  + exact Llo.
  + apply round_up_lane.
    exact (mpfr_fn_correct emin emax m D f g Hrange Hget Hg RNDU _ Fb (HxD _ Mb)).
- destruct (Hd (cl_sup_inf_d x Hx E HxD Eb)) as [Hinf Hunb].
  rewrite Eb, (mpfr_fn_inf emin emax m g RNDU false false Hget Hinf).
  apply (cl_tightest _ _ None _ _ Hne Tlo).
  + apply cl_tight_none. intros M. destruct (Hunb M) as (r & Dr & Hr).
    (* [f(r) >= M] for some [r] in [D], and [max(r, a)] is in [x]. *)
    set (t := Rmax r (B2R (Interval.inf_raw x))).
    assert (Mt : mem t x).
    { apply (cl_sup_inf_mem x t Hx E Fa Eb). apply Rmax_r. }
    exists (f t). split; [exists t; split; [exact Mt | reflexivity]|].
    apply Rle_trans with (f r); [exact Hr|].
    apply Hinc; [exact Dr | exact (HxD t Mt) | apply Rmax_l].
  + exact Llo.
  + exact least_lane_inf.
Qed.

(** The result for a nonempty subset [x] of [D] is common only if [x] is
    bounded: an unbounded [x] has [b] = +inf, as [a] is finite, and then
    [f_ru(+inf)] is +inf. *)
Lemma cl_inc_bounded :
  forall x, valid x -> Interval.is_empty x = false -> (forall r, mem r x -> D r) ->
  Interval.is_common_interval
    (Interval.with_infsup_raw (mpfr_fn m g RNDD (Interval.inf_raw x))
       (mpfr_fn m g RNDU (Interval.sup_raw x))) = true ->
  bounded (fun r => mem r x).
Proof using Hget Hc HDOM HD Hd.
intros x Hx E HxD Hcom.
pose proof (cl_inf_D x Hx E HxD) as Fa.
destruct (cl_ub_cases x Hx E) as [Fb|Eb].
- exists (Rabs (B2R (Interval.inf_raw x)) + Rabs (B2R (Interval.sup_raw x))).
  intros r Hr. apply Rabs_between.
  split; [exact (cl_mem_inf x r Hx E Fa Hr) | exact (cl_mem_sup x r Hx E Fb Hr)].
- exfalso. destruct (Hd (cl_sup_inf_d x Hx E HxD Eb)) as [Hinf _].
  rewrite Eb, (mpfr_fn_inf emin emax m g RNDU false false Hget Hinf) in Hcom.
  rewrite is_common_interval_lt, infinity_eq in Hcom.
  apply andb_prop in Hcom. destruct Hcom as [_ H]. vm_compute in H. discriminate H.
Qed.

Theorem closed_inc_correct :
  forall x, valid x ->
  is_tightest (image_dom D f x)
    (fst (closed_inc (Interval.const_interval c d) (mpfr_fn m g RNDD) (mpfr_fn m g RNDU) x)).
Proof using Hrange Hget Hg Hc HDOM HD Hd Hinc Hcont.
intros x Hx. rewrite cl_closed_inc_eq.
apply (closed_gen_correct _ D f _ HDOM HD); [|exact Hx].
exact cl_inc_tight.
Qed.

Theorem dec_closed_inc_correct :
  forall x, valid (itv x) ->
  let y :=
    DecInterval.elem_dec_impl
      (closed_inc (Interval.const_interval c d) (mpfr_fn m g RNDD) (mpfr_fn m g RNDU)) x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom D f (itv x)) (itv y) /\
    exists e, strongest_dom D e f (itv x) (itv y) /\ dec y = dec_min e (dec x).
Proof using Hrange Hget Hg Hc HDOM HD Hd Hinc Hcont.
intros x Hx. rewrite cl_closed_inc_eq.
apply (dec_closed_gen_correct _ D f _ HDOM HD).
- exact cl_inc_tight.
- exact cl_inc_bounded.
- exact Hcont.
- exact Hx.
Qed.

End ClosedInc.

(** For a nonempty subset [x] = [[a, b]] of [[-1, 1]],
    [[acos_rd(b), acos_ru(a)]] is the tightest interval that contains the
    image of [x], as [acos] is decreasing: [acos(b)] is the least value
    and [acos(a)] the largest. *)
Lemma cl_acos_tight :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> acos_ok emin emax m ->
  forall x, valid x -> Interval.is_empty x = false -> (forall r, mem r x -> acos_dom r) ->
  is_tightest (fun s => exists r, mem r x /\ s = acos r)
    (Interval.with_infsup_raw (acos_rd m (Interval.sup_raw x)) (acos_ru m (Interval.inf_raw x))).
Proof.
intros emin emax m Hrange Hget Hacos x Hx E HxD.
assert (Fa : is_finite (Interval.inf_raw x) = true).
{ apply (cl_inf_finite x (-1) Hx E). intros r Hr. exact (proj1 (HxD r Hr)). }
assert (Fb : is_finite (Interval.sup_raw x) = true).
{ apply (cl_sup_finite x 1 Hx E). intros r Hr. exact (proj2 (HxD r Hr)). }
pose proof (cl_inf_mem x Hx E Fa) as Ma.
pose proof (cl_sup_mem x Hx E Fb) as Mb.
apply (cl_tightest _ (Some (- acos (B2R (Interval.sup_raw x))))
         (Some (acos (B2R (Interval.inf_raw x))))).
- exists (acos (B2R (Interval.inf_raw x))), (B2R (Interval.inf_raw x)).
  split; [exact Ma | reflexivity].
- apply (cl_tight_min (fun s => exists r, mem r x /\ s = acos r)).
  + exists (B2R (Interval.sup_raw x)). split; [exact Mb | reflexivity].
  + intros s (r & Hr & ->). apply acos_dec.
    * exact (proj1 (HxD r Hr)).
    * exact (cl_mem_sup x r Hx E Fb Hr).
    * exact (proj2 (HxD _ Mb)).
- apply cl_tight_max.
  + exists (B2R (Interval.inf_raw x)). split; [exact Ma | reflexivity].
  + intros s (r & Hr & ->). apply acos_dec.
    * exact (proj1 (HxD _ Ma)).
    * exact (cl_mem_inf x r Hx E Fa Hr).
    * exact (proj2 (HxD r Hr)).
- apply round_dn_lane. unfold acos_rd.
  exact (mpfr_fn_correct emin emax m acos_dom acos (mpfr_acos m) Hrange Hget Hacos RNDD _ Fb
           (HxD _ Mb)).
- apply round_up_lane. unfold acos_ru.
  exact (mpfr_fn_correct emin emax m acos_dom acos (mpfr_acos m) Hrange Hget Hacos RNDU _ Fa
           (HxD _ Ma)).
Qed.

Lemma cl_acos_dom : forall r, acos_dom r <-> mem r dom_unit.
Proof.
intros r. unfold acos_dom. apply iff_sym. apply dom_unit_mem.
Qed.

(** [Interval::acos] returns the tightest interval that contains the
    image. *)
Theorem acos_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> acos_ok emin emax m ->
  forall x, valid x -> is_tightest (image_dom acos_dom acos x) (Interval.acos m x).
Proof.
intros emin emax m Hrange Hget Hacos x Hx. unfold Interval.acos. rewrite cl_acos_eq.
apply (closed_gen_correct _ acos_dom acos _ dom_unit_valid cl_acos_dom); [|exact Hx].
exact (cl_acos_tight emin emax m Hrange Hget Hacos).
Qed.

(** [DecInterval::acos] returns NaI for NaI, and otherwise the tightest
    interval, decorated as IEEE 1788 asks. *)
Theorem dec_acos_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> acos_ok emin emax m ->
  forall x, valid (itv x) ->
  let y := DecInterval.acos m x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom acos_dom acos (itv x)) (itv y) /\
    exists d, strongest_dom acos_dom d acos (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof.
intros emin emax m Hrange Hget Hacos x Hx. unfold DecInterval.acos. rewrite cl_acos_eq.
apply (dec_closed_gen_correct _ acos_dom acos _ dom_unit_valid cl_acos_dom).
- exact (cl_acos_tight emin emax m Hrange Hget Hacos).
- (* A subset of [[-1, 1]] is bounded. *)
  intros y _ _ HyD _. exists 1. intros r Hr. destruct (HyD r Hr) as [H1 H2].
  apply Rabs_le. split; lra.
- exact acos_cont.
- exact Hx.
Qed.
