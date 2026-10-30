(** * [intersection], [interior] and [subset] on the reals of intervals

    The elementary functions with a domain intersect their argument with
    the domain, and decorate the result by [interior] or [subset] of their
    argument and the domain. This file says what these are on the reals
    of [valid] intervals, and what the domains [[0, +inf]], [[-1, 1]] and
    [[1, +inf]] of [src/elementary.rs] hold.

    A nonempty interval [[a, b]] is stored as [[-a; b]], and both lanes
    have the form of an upper bound, finite or +inf. A real [r] is in it
    exactly when [-r] is below the first lane and [r] below the second
    ([intr_mem_upper]). So the lanes compare as upper bounds: [Bleb] of two
    lanes says that every real below the first is below the second
    ([intr_le_ule]), which is [subset] lane by lane. [interior] asks, lane
    by lane, for the lane of [x] to be strictly below that of [y], or that
    of [y] to be +inf ([intr_ust]). A real of [x] then has a neighbourhood
    below the lane of [y], the gap between the lanes. Otherwise the lane
    of [y] is a finite [d] at or below that of [x], so [x] has a real at
    least [d] (from [lanes_ok]), and the reals just above it are not
    below [d]. *)

From Stdlib Require Import Bool ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Integer MaxMin ValidSetOp Sign.

Open Scope R_scope.

(** ** Lanes as upper bounds *)

(** The reals of an interval whose lanes have the form of upper bounds. *)
Lemma intr_mem_upper :
  forall u v r, upper_ok u -> upper_ok v ->
  mem r {| rep := (u, v) |} <-> below (bound u) (- r) /\ below (bound v) r.
Proof.
intros u v r Hu Hv.
rewrite (mem_bounds {| rep := (u, v) |} r (lower_ok_lane _ Hu) Hv).
cbn [rep fst snd]. rewrite in_bounds_iff, (bound_lane u), below_oopp.
reflexivity.
Qed.

(** [Bleb] of two lanes: every real below the first is below the second. *)
Lemma intr_le_ule :
  forall u w, upper_ok u -> upper_ok w ->
  le u w = true <-> forall s, below (bound u) s -> below (bound w) s.
Proof.
intros u w [Fu| ->] [Fw| ->]; unfold le.
- rewrite Bleb_correct by assumption. rewrite !bound_finite by assumption.
  cbn [below]. split.
  + case Rle_bool_spec; [intros H _ s Hs; lra | discriminate].
  + intros H. apply Rle_bool_true. apply H, Rle_refl.
- rewrite (bound_finite u Fu), bound_inf. cbn [below].
  split; [intros _ s _; exact I|].
  intros _. destruct u as [su|su| |su mu eu Hu]; try discriminate Fu;
    reflexivity.
- (* No real is below every real, so +inf is not below a finite [w]. *)
  rewrite bound_inf, (bound_finite w Fw). cbn [below]. split.
  + destruct w as [sw|sw| |sw mw ew Hw]; try discriminate Fw; discriminate.
  + intros H. specialize (H (B2R w + 1) I). lra.
- rewrite bound_inf. split; [intros _ s _; exact I | intros _; reflexivity].
Qed.

(** The upper bound [o1] is strictly below [o2], or [o2] is +inf. *)
Definition intr_ust (o1 o2 : option R) : Prop :=
  match o1, o2 with
  | _, None => True
  | Some b, Some d => b < d
  | None, Some _ => False
  end.

(** What a lane of [interior] tests, [lt] of the lanes or both +inf. *)
Lemma intr_lt_ust :
  forall u w, upper_ok u -> upper_ok w ->
  (lt u w || (eq u infinity && eq w infinity)) = true <->
  intr_ust (bound u) (bound w).
Proof.
intros u w [Fu| ->] [Fw| ->]; rewrite infinity_eq; unfold lt.
- assert (Eu : eq u (B754_infinity false) = false)
    by (destruct u as [su|su| |su mu eu Hu]; try discriminate Fu; reflexivity).
  rewrite Eu, orb_false_r, Bltb_correct by assumption.
  rewrite !bound_finite by assumption. cbn [intr_ust].
  case Rlt_bool_spec; intros H; split; intros H'; first [lra | reflexivity | discriminate].
- rewrite (bound_finite u Fu), bound_inf. cbn [intr_ust]. split; [intros _; exact I|].
  intros _. destruct u as [su|su| |su mu eu Hu]; try discriminate Fu;
    reflexivity.
- rewrite bound_inf, (bound_finite w Fw). cbn [intr_ust]. split; [|contradiction].
  destruct w as [sw|sw| |sw mw ew Hw]; try discriminate Fw; discriminate.
- rewrite bound_inf. cbn [intr_ust]. split; [intros _; exact I | intros _; reflexivity].
Qed.

(** On lanes, [lt] of the negations is [lt] the other way. *)
Lemma intr_lt_opp :
  forall u w, upper_ok u -> upper_ok w -> lt (opp w) (opp u) = lt u w.
Proof.
intros u w [Fu| ->] [Fw| ->]; unfold lt.
- rewrite !Bltb_correct by first [assumption | rewrite is_finite_opp; assumption].
  rewrite !B2R_opp.
  case Rlt_bool_spec; case Rlt_bool_spec; intros; first [reflexivity | lra].
- destruct u as [su|su| |su mu eu Hu]; try discriminate Fu; reflexivity.
- destruct w as [sw|sw| |sw mw ew Hw]; try discriminate Fw; reflexivity.
- reflexivity.
Qed.

(** A real below [o1] has a neighbourhood above it below [o2]: the gap
    [d - b] between the bounds, or any if [o2] is +inf. *)
Lemma intr_ust_nbhd :
  forall o1 o2, intr_ust o1 o2 ->
  exists e, 0 < e /\ forall r t, below o1 r -> t < r + e -> below o2 t.
Proof.
intros [b|] [d|] H; cbn [intr_ust] in H; try contradiction.
- exists (d - b). split; [lra|]. intros r t Hr Ht. cbn [below] in *. lra.
- exists 1. split; [lra|]. intros r t _ _. exact I.
- exists 1. split; [lra|]. intros r t _ _. exact I.
Qed.

(** Conversely, if every element of [A] has reals just above it below
    [o2], and [o1] is the largest element of [A], then [intr_ust o1 o2]:
    otherwise [o2] is a finite [d] at or below [o1], [A] has an element
    at least [d], and the reals just above it are above [d]. *)
Lemma intr_ust_of_nbhd :
  forall o1 o2 (A : R -> Prop),
  (forall s, below o1 s -> exists r, A r /\ s <= r) ->
  (forall r, A r -> exists e, 0 < e /\ forall t, r <= t -> t < r + e -> below o2 t) ->
  intr_ust o1 o2.
Proof.
intros o1 o2 A HA HN. destruct o2 as [d|]; [|destruct o1; exact I].
assert (Hd : ~ below o1 d).
{ intros Hb. destruct (HA d Hb) as (r & Ar & Hdr).
  destruct (HN r Ar) as (e & He & Ht).
  assert (H : r + e / 2 <= d) by (apply (Ht (r + e / 2)); lra).
  lra. }
destruct o1 as [b|]; cbn [intr_ust below] in *.
- apply Rnot_le_lt. exact Hd.
- exact (Hd I).
Qed.

(** [Generic.all] of a mask is [&&] of its lanes. *)
Lemma intr_all_mask :
  forall p q, Generic.all (Generic.mask p, Generic.mask q) = p && q.
Proof.
intros [|] [|]; reflexivity.
Qed.

(** The lanes of [intersection] pass the test [gt] only if no real is
    below both. *)
Lemma intr_gt_mem :
  forall u v r, upper_ok u -> upper_ok v -> Bltb v (opp u) = true ->
  below (bound u) (- r) -> below (bound v) r -> False.
Proof.
intros u v r [Fu| ->] [Fv| ->] G Hu Hv.
- rewrite Bltb_correct in G by first [assumption | rewrite is_finite_opp; assumption].
  rewrite B2R_opp in G. rewrite bound_finite in Hu, Hv by assumption.
  cbn [below] in Hu, Hv. revert G. case Rlt_bool_spec; [intros; lra | discriminate].
- destruct u as [su|su| |su mu eu H]; try discriminate Fu; destruct su; discriminate G.
- destruct v as [sv|sv| |sv mv ev H]; try discriminate Fv; destruct sv; discriminate G.
- discriminate G.
Qed.

(** ** The theorems *)

(** The reals of [intersection x y] are those of both. *)
Lemma intersection_mem :
  forall x y r, valid x -> valid y ->
  mem r (Interval.intersection x y) <-> mem r x /\ mem r y.
Proof.
intros [[x0 x1]] [[y0 y1]] r Hx Hy.
unfold Interval.intersection, Interval.either_empty, Interval.is_empty.
cbn [rep fst snd].
destruct (is_nan x0) eqn:Nx; cbn [orb].
{ split; [intros H; destruct (mem_nan Interval.EMPTY r eq_refl H)|].
  intros [H _]. destruct (mem_nan _ r (empty_nan _ Hx Nx) H). }
destruct (is_nan y0) eqn:Ny; cbn [orb].
{ split; [intros H; destruct (mem_nan Interval.EMPTY r eq_refl H)|].
  intros [_ H]. destruct (mem_nan _ r (empty_nan _ Hy Ny) H). }
destruct (valid_nonempty _ Hx Nx) as (Lx & Ux & _).
destruct (valid_nonempty _ Hy Ny) as (Ly & Uy & _).
cbn [rep fst snd] in Lx, Ux, Ly, Uy.
apply upper_ok_lane in Lx, Ly.
destruct (min1_bound _ _ Lx Ly) as [U0 B0].
destruct (min1_bound _ _ Ux Uy) as [U1 B1].
(* The lanes of [i] are [min1] of those of [x] and [y], i.e. [umin] of
   the upper bounds, so a real is below them exactly when it is below
   those of both. *)
assert (K : mem r {| rep := (Generic.min1 x0 y0, Generic.min1 x1 y1) |} <->
            mem r {| rep := (x0, x1) |} /\ mem r {| rep := (y0, y1) |}).
{ rewrite (intr_mem_upper _ _ r U0 U1), (intr_mem_upper _ _ r Lx Ux),
    (intr_mem_upper _ _ r Ly Uy), B0, B1, !below_umin.
  tauto. }
unfold Interval.inf_raw, Interval.sup_raw, Model.gt, Generic.min.
cbn [rep fst snd].
destruct (Bltb (Generic.min1 x1 y1) (opp (Generic.min1 x0 y0))) eqn:G; [|exact K].
split; [intros H; destruct (mem_nan Interval.EMPTY r eq_refl H)|].
intros Hxy. apply K in Hxy. apply (intr_mem_upper _ _ r U0 U1) in Hxy.
destruct Hxy as [H0 H1]. destruct (intr_gt_mem _ _ r U0 U1 G H0 H1).
Qed.

(** [interior x y]: every real of [x] has a neighbourhood in [y]. *)
Lemma interior_mem :
  forall x y, valid x -> valid y ->
  Interval.interior x y = true <->
  forall r, mem r x -> exists eps, 0 < eps /\ forall t, Rabs (t - r) < eps -> mem t y.
Proof.
intros [[x0 x1]] [[y0 y1]] Hx Hy.
unfold Interval.interior, Interval.is_empty, Interval.sup_raw, Interval.inf_raw,
  Generic.eq, Generic.shuffle13, Generic.shuffle02, Generic.splat.
cbn [rep fst snd].
rewrite !intr_all_mask.
destruct (is_nan x0) eqn:Nx; cbn [orb andb].
{ split; [|reflexivity]. intros _ r H. destruct (mem_nan _ r (empty_nan _ Hx Nx) H). }
destruct (lanes_ok _ Hx Nx) as (U0x & U1x & [r0 Hr0] & L0x & L1x).
cbn [rep fst snd] in U0x, U1x, L0x, L1x.
destruct (is_nan y0) eqn:Ny.
{ (* [y] is empty: its lanes are NaN, so the test fails, and the reals
     of [x] have no neighbourhood in [y]. *)
  pose proof (empty_nan _ Hy Ny) as Ey. split.
  - cbn [rep] in Ey. injection Ey as -> ->. rewrite infinity_eq.
    intros H. apply andb_prop in H. destruct H as [H _]. revert H.
    destruct x1 as [s|[]| |s m e Hm]; intros H; cbn in H; discriminate H.
  - intros H. destruct (H r0 Hr0) as (e & He & Ht).
    specialize (Ht r0). replace (r0 - r0) with 0 in Ht by ring.
    rewrite Rabs_R0 in Ht. destruct (mem_nan _ r0 Ey (Ht He)). }
destruct (lanes_ok _ Hy Ny) as (U0y & U1y & _ & L0y & L1y).
cbn [rep fst snd] in U0y, U1y, L0y, L1y.
rewrite (intr_lt_opp _ _ U0x U0y), andb_true_iff, (intr_lt_ust _ _ U1x U1y),
  (intr_lt_ust _ _ U0x U0y).
split.
- (* The smaller gap between the lanes is a neighbourhood. *)
  intros [H1 H0] r Hr. apply (intr_mem_upper _ _ r U0x U1x) in Hr.
  destruct Hr as [Hr0' Hr1].
  destruct (intr_ust_nbhd _ _ H0) as (e0 & He0 & N0).
  destruct (intr_ust_nbhd _ _ H1) as (e1 & He1 & N1).
  exists (Rmin e0 e1). split; [apply Rmin_glb_lt; assumption|].
  intros t Ht. apply Rabs_def2 in Ht. pose proof (Rmin_l e0 e1). pose proof (Rmin_r e0 e1).
  apply (intr_mem_upper _ _ t U0y U1y). split.
  + apply (N0 (- r)); [exact Hr0' | lra].
  + apply (N1 r); [exact Hr1 | lra].
- intros H. split.
  + (* The upper lanes: the reals of [x] are the set whose largest
       element is the second lane of [x]. *)
    apply (intr_ust_of_nbhd _ _ (fun r => mem r {| rep := (x0, x1) |})).
    * intros s Hs. apply L1x, Hs.
    * intros r Hr. destruct (H r Hr) as (e & He & Ht). exists e. split; [exact He|].
      intros t Ht1 Ht2.
      assert (Ht' : Rabs (t - r) < e) by (apply Rabs_def1; lra).
      apply (intr_mem_upper _ _ t U0y U1y), Ht, Ht'.
  + (* The lower lanes: the negations of the reals of [x] are the set
       whose largest element is the first lane of [x]. *)
    apply (intr_ust_of_nbhd _ _ (fun r => mem (- r) {| rep := (x0, x1) |})).
    * intros s Hs. rewrite <- (Ropp_involutive s) in Hs.
      apply L0x in Hs. destruct Hs as (r & Hr & Hrs).
      exists (- r). rewrite Ropp_involutive. split; [exact Hr | lra].
    * intros r Hr. destruct (H (- r) Hr) as (e & He & Ht). exists e.
      split; [exact He|]. intros t Ht1 Ht2.
      assert (Ht' : Rabs (- t - - r) < e) by (apply Rabs_def1; lra).
      apply Ht, (intr_mem_upper _ _ (- t) U0y U1y) in Ht'.
      rewrite Ropp_involutive in Ht'. apply Ht'.
Qed.

(** [subset x y]: every real of [x] is in [y]. *)
Lemma subset_mem :
  forall x y, valid x -> valid y ->
  Interval.subset x y = true <-> forall r, mem r x -> mem r y.
Proof.
intros [[x0 x1]] [[y0 y1]] Hx Hy.
unfold Interval.subset, Interval.is_empty, Generic.le. cbn [rep fst snd].
rewrite intr_all_mask.
destruct (is_nan x0) eqn:Nx; cbn [orb].
{ split; [|reflexivity]. intros _ r H. destruct (mem_nan _ r (empty_nan _ Hx Nx) H). }
destruct (lanes_ok _ Hx Nx) as (U0x & U1x & [r0 Hr0] & L0x & L1x).
cbn [rep fst snd] in U0x, U1x, L0x, L1x.
destruct (is_nan y0) eqn:Ny.
{ (* [y] is empty, and [x] has a real. *)
  pose proof (empty_nan _ Hy Ny) as Ey. split.
  - cbn [rep] in Ey. injection Ey as -> ->.
    assert (E : le x0 B754_nan = false) by (destruct x0; reflexivity).
    rewrite E. discriminate.
  - intros H. destruct (mem_nan _ r0 Ey (H r0 Hr0)). }
destruct (lanes_ok _ Hy Ny) as (U0y & U1y & _ & L0y & L1y).
cbn [rep fst snd] in U0y, U1y, L0y, L1y.
rewrite andb_true_iff, (intr_le_ule _ _ U0x U0y), (intr_le_ule _ _ U1x U1y).
split.
- intros [H0 H1] r Hr. apply (intr_mem_upper _ _ r U0x U1x) in Hr.
  apply (intr_mem_upper _ _ r U0y U1y).
  destruct Hr as [Hr0' Hr1]. split; [apply H0, Hr0' | apply H1, Hr1].
- (* A real below a lane of [x] is below that lane of a real of [x],
     which is in [y]. *)
  intros H. split.
  + intros s Hs. rewrite <- (Ropp_involutive s) in Hs |- *.
    apply L0x in Hs. destruct Hs as (r & Hr & Hrs).
    apply L0y. exists r. split; [apply H, Hr | exact Hrs].
  + intros s Hs. apply L1x in Hs. destruct Hs as (r & Hr & Hsr).
    apply L1y. exists r. split; [apply H, Hr | exact Hsr].
Qed.

(** The domains in [src/elementary.rs], with [0.0] as +0, [1.0] as
    [of_u64 1] and [-1.0] as its negation. *)
Definition dom_nonneg : Interval :=
  Interval.const_interval zero (B754_infinity false).
Definition dom_unit : Interval :=
  Interval.const_interval (opp (of_u64 1)) (of_u64 1).
Definition dom_ge1 : Interval :=
  Interval.const_interval (of_u64 1) (B754_infinity false).

(** A finite float is no infinity. *)
Lemma intr_finite_ne_inf :
  forall (a : f64) s, is_finite a = true -> a <> B754_infinity s.
Proof.
intros a s F ->. discriminate F.
Qed.

Lemma dom_nonneg_valid : valid dom_nonneg.
Proof.
unfold valid, dom_nonneg, Interval.const_interval. cbn [rep]. right.
split; [reflexivity|].
split; [apply intr_finite_ne_inf; reflexivity | discriminate].
Qed.

Lemma dom_unit_valid : valid dom_unit.
Proof.
unfold valid, dom_unit, Interval.const_interval. cbn [rep]. right.
split; [vm_compute; reflexivity|].
split; apply intr_finite_ne_inf; vm_compute; reflexivity.
Qed.

Lemma dom_ge1_valid : valid dom_ge1.
Proof.
unfold valid, dom_ge1, Interval.const_interval. cbn [rep]. right.
split; [vm_compute; reflexivity|].
split; [apply intr_finite_ne_inf; vm_compute; reflexivity | discriminate].
Qed.

Lemma dom_nonneg_mem : forall r, mem r dom_nonneg <-> 0 <= r.
Proof.
intros r. unfold mem, dom_nonneg, Interval.const_interval. cbn.
split; [intros [H _]; exact H | intros H; split; [exact H | reflexivity]].
Qed.

Lemma dom_unit_mem : forall r, mem r dom_unit <-> -1 <= r <= 1.
Proof.
intros r. destruct one_B2R as [F1 E1]. unfold one in F1, E1.
unfold dom_unit.
rewrite mem_bounds by (left; unfold Interval.const_interval; cbn [rep fst snd];
  rewrite ?is_finite_opp; exact F1).
unfold Interval.const_interval. cbn [rep fst snd].
rewrite !bound_finite by (rewrite ?is_finite_opp; exact F1).
unfold in_bounds. rewrite !B2R_opp, E1. split; intros; lra.
Qed.

Lemma dom_ge1_mem : forall r, mem r dom_ge1 <-> 1 <= r.
Proof.
intros r. destruct one_B2R as [F1 E1]. unfold one in F1, E1.
unfold dom_ge1.
rewrite mem_bounds by first
  [ left; unfold Interval.const_interval; cbn [rep fst snd];
    rewrite ?is_finite_opp; exact F1
  | right; reflexivity ].
unfold Interval.const_interval. cbn [rep fst snd].
rewrite bound_finite by (rewrite !is_finite_opp; exact F1).
rewrite bound_inf. unfold in_bounds. rewrite !B2R_opp, E1.
split; [intros [H _]; lra | intros H; split; [lra | exact I]].
Qed.
