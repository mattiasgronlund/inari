(** * [x + y] and [x - y] of intervals are tightest and decorated correctly

    [x + y] of [Interval]s returns the tightest interval that contains the
    image of the box [x × y] under [+], and [x + y] of [DecInterval]s
    decorates it with the minimum of the strongest decoration that holds
    and the decorations of [x] and [y], as IEEE 1788 asks of a tightest
    interval version of a function. The same holds for [x - y].

    [x + y] adds [[-a; b]] and [[-c; d]] with [add_ru], which gives
    [[RU(-a - c); RU(b + d)]], i.e. [[RD(a + c), RU(b + d)]]. The image of
    [[a, b] × [c, d]] holds the reals between [a + c] and [b + d], which
    need not be floats, so the result is not its hull, but the tightest
    interval with bounds that are floats or infinities that contains it
    ([is_tightest]). The second lane of [[-a; b]] is the largest real of
    [x], or +inf if there is none ([tight]), and the first lane is the
    largest negation of a real of [x]. The largest sum [r + t] is the sum
    of the largest [r] and the largest [t], or +inf if either is.
    [add_lane] shows that [Bplus mode_UP] gives the least float or +inf at
    or above that sum ([least_lane]): the sum rounded up if it does not
    overflow, +inf if it overflows above, and [-f64::MAX] if it overflows
    below, as every float is at least that. A lane that is +inf gives +inf.
    An empty argument gives NaN in both lanes, the empty interval.

    [x - y] adds [[-a; b]] and the swapped [[d; -c]], so it is [x + (-y)],
    and the image of [x × y] under [-] is that of [x × (-y)] under [+].

    [+] and [-] are continuous on R². If a nonempty box has a bounded image
    under [+], the box is bounded, as [|r| <= |r + t| + |t|] for a [t] in
    [y], and the same holds for [-]. So [set_dec_correct] in [DecBinary.v]
    applies without a hypothesis on the decorations of the arguments. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Spec Ieee1788 Integer Sign MaxMin AddRu
  DecBinary Neg.

Open Scope R_scope.

(** ** Upper bounds

    As in [below], [None] is +inf for an upper bound. *)

(** The upper bound [o1] is at most [o2]. *)
Definition ule (o1 o2 : option R) : Prop := forall s, below o1 s -> below o2 s.

(** The sum of two upper bounds. *)
Definition uplus (o1 o2 : option R) : option R :=
  match o1, o2 with Some a, Some b => Some (a + b) | _, _ => None end.

(** The product of two upper bounds above 0, for [x * y] in [Mul.v]. *)
Definition umult (o1 o2 : option R) : option R :=
  match o1, o2 with Some a, Some b => Some (a * b) | _, _ => None end.

(** [o] is the largest element of [A], or [None] if [A] has no upper
    bound: a real is below [o] exactly when it is below an element of
    [A]. *)
Definition tight (o : option R) (A : R -> Prop) : Prop :=
  forall s, below o s <-> exists r, A r /\ s <= r.

Lemma tight_ext :
  forall o A B, (forall r, A r <-> B r) -> tight o A -> tight o B.
Proof.
intros o A B HAB HA s. rewrite (HA s).
split; intros (r & Hr & Hs); exists r; (split; [apply HAB, Hr | exact Hs]).
Qed.

(** The largest sum of an element of [A] and one of [B] is the sum of
    their largest elements. *)
Lemma tight_sum :
  forall U V A B, tight U A -> tight V B -> (exists r, A r) -> (exists t, B t) ->
  tight (uplus U V) (fun s => exists r t, A r /\ B t /\ s = r + t).
Proof.
intros [a|] [b|] A B HA HB [r0 Hr0] [t0 Ht0] s; cbn [uplus below].
- split.
  + intros Hs.
    destruct (proj1 (HA a) (Rle_refl a)) as (r & Hr & Har).
    destruct (proj1 (HB b) (Rle_refl b)) as (t & Ht & Hbt).
    exists (r + t). split; [exists r, t; split; [exact Hr | split; [exact Ht | reflexivity]] | lra].
  + intros (u & (r & t & Hr & Ht & ->) & Hs).
    assert (r <= a) by (apply (proj2 (HA r)); exists r; split; [exact Hr | apply Rle_refl]).
    assert (t <= b) by (apply (proj2 (HB t)); exists t; split; [exact Ht | apply Rle_refl]).
    lra.
- (* [B] has no upper bound, so neither do the sums with [r0]. *)
  split; [|intros _; exact I]. intros _.
  destruct (proj1 (HB (s - r0)) I) as (t & Ht & Hs).
  exists (r0 + t). split; [exists r0, t; split; [exact Hr0 | split; [exact Ht | reflexivity]] | lra].
- split; [|intros _; exact I]. intros _.
  destruct (proj1 (HA (s - t0)) I) as (r & Hr & Hs).
  exists (r + t0). split; [exists r, t0; split; [exact Hr | split; [exact Ht0 | reflexivity]] | lra].
- split; [|intros _; exact I]. intros _.
  destruct (proj1 (HA (s - t0)) I) as (r & Hr & Hs).
  exists (r + t0). split; [exists r, t0; split; [exact Hr | split; [exact Ht0 | reflexivity]] | lra].
Qed.

(** What the lanes of a nonempty interval [x] say: the first holds the
    largest negation of a real of [x], and the second the largest real of
    [x]. *)
Lemma lanes_tight :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  upper_ok (fst (rep x)) /\ upper_ok (snd (rep x)) /\ (exists r, mem r x) /\
  tight (bound (fst (rep x))) (fun r => mem (- r) x) /\
  tight (bound (snd (rep x))) (fun r => mem r x).
Proof.
intros x Hx Hn. destruct (lanes_ok x Hx Hn) as (U0 & U1 & Nx & L0 & L1).
split; [exact U0|]. split; [exact U1|]. split; [exact Nx|]. split; [|exact L1].
intros s. pose proof (L0 (- s)) as H. rewrite Ropp_involutive in H. rewrite H.
split; intros (r & Hr & Hs); exists (- r).
- rewrite Ropp_involutive. split; [exact Hr | lra].
- split; [exact Hr | lra].
Qed.

(** ** Rounding a sum up *)

(** [w] is the least float or +inf at or above the upper bound [o]. *)
Definition least_lane (o : option R) (w : f64) : Prop :=
  upper_ok w /\ ule o (bound w) /\
  forall z, upper_ok z -> ule o (bound z) -> ule (bound w) (bound z).

(** [w] is above 0: a positive float or +inf. *)
Definition pos_lane (w : f64) : Prop :=
  w = B754_infinity false \/ (is_finite w = true /\ 0 < B2R w).

Lemma least_lane_inf : least_lane None (B754_infinity false).
Proof.
split; [right; reflexivity|]. split; [intros s _; exact I|].
intros z _ Hz s _. exact (Hz s I).
Qed.

Lemma B2R_Bsign_false : forall x : f64, Bsign x = false -> 0 <= B2R x.
Proof.
intros [s|s| |s m e H] Hs; cbn [B2R]; try apply Rle_refl.
cbn [Bsign] in Hs. subst s.
apply F2R_ge_0. cbn [Fnum SpecFloat.cond_Zopp]. lia.
Qed.

(** [Bplus mode_UP] returns [-f64::MAX] on a negative overflow, and every
    float is at least that. *)
Lemma neg_overflow :
  forall w : f64, B2SF w = binary_overflow 53 1024 mode_UP true ->
  is_finite w = true /\ B2R w = bpow radix2 971 - bpow radix2 1024.
Proof.
intros [sw|sw| |sw mw ew Hw] HO; cbn in HO; try discriminate HO.
injection HO as -> -> ->. split; [reflexivity|].
cbn [B2R]. unfold F2R. cbn [Fnum Fexp SpecFloat.cond_Zopp bpow radix_val radix2].
rewrite <- mult_IZR, <- minus_IZR. reflexivity.
Qed.

Lemma neg_max_le : forall z : f64, bpow radix2 971 - bpow radix2 1024 <= B2R z.
Proof.
intros z.
assert (H : Rabs (B2R z) <= bpow radix2 1024 - bpow radix2 971).
{ pose proof (bpow_lt radix2 971 1024 ltac:(lia)).
  destruct z as [s|s| |s m e Hb]; cbn [B2R]; try (rewrite Rabs_R0; lra).
  rewrite <- F2R_Zabs, abs_cond_Zopp.
  change (Z.abs (Z.pos m)) with (Z.pos m).
  change (bpow radix2 971) with (bpow radix2 (1024 - 53)).
  exact (bounded_le_emax_minus_prec 53 1024 _ m e Hb). }
apply Rabs_le_inv in H. lra.
Qed.

(** [Bplus mode_UP] of two lanes is the least float or +inf at or above
    their sum. *)
Lemma add_lane :
  forall u v, upper_ok u -> upper_ok v ->
  least_lane (uplus (bound u) (bound v)) (Bplus mode_UP u v).
Proof.
intros u v [Fu| ->] [Fv| ->];
  [| destruct u; try discriminate Fu; exact least_lane_inf
   | destruct v; try discriminate Fv; exact least_lane_inf
   | exact least_lane_inf].
rewrite (bound_finite _ Fu), (bound_finite _ Fv). cbn [uplus].
destruct (round_UP_pt radix2 fexp64 (B2R u + B2R v)) as (_ & Hge & Hmin).
generalize (@Bplus_correct 53 1024 _ _ mode_UP u v Fu Fv).
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_UP)) with RU.
case Rlt_bool_spec; intros Hov HB.
- (* No overflow: the sum rounded up. *)
  destruct HB as (HR & HF & _).
  split; [left; exact HF|]. rewrite (bound_finite _ HF), HR. split.
  + intros s Hs. cbn [below] in *. lra.
  + intros z [Fz| ->] Hz; [|intros s _; exact I].
    rewrite (bound_finite _ Fz) in *.
    (* [z] is a float at or above the sum, so at or above it rounded up. *)
    assert (Hle : B2R u + B2R v <= B2R z) by exact (Hz _ (Rle_refl _)).
    pose proof (Hmin _ (generic_format_B2R _ _ z) Hle).
    intros s Hs. cbn [below] in *. lra.
- destruct HB as (HO & Hs).
  destruct (Bsign u) eqn:Su.
  + (* Both lanes are at most 0, so the sum is at or below -2^1024, and
       the result is [-f64::MAX]. *)
    pose proof (B2R_Bsign_true u Su). pose proof (B2R_Bsign_true v (eq_sym Hs)).
    assert (Hneg : RU (B2R u + B2R v) <= 0).
    { apply Hmin; [apply generic_format_0 | lra]. }
    rewrite Rabs_left1 in Hov by exact Hneg.
    destruct (neg_overflow _ HO) as (Fw & Rw).
    split; [left; exact Fw|]. rewrite (bound_finite _ Fw), Rw. split.
    * intros s Hs'. cbn [below] in *. pose proof (bpow_gt_0 radix2 971). lra.
    * intros z Hz _ s Hs'. destruct Hz as [Fz| ->]; [|exact I].
      rewrite (bound_finite _ Fz). cbn [below] in *. pose proof (neg_max_le z).
      lra.
  + (* Both lanes are at least 0, so the sum is at or above 2^1024, which
       no float is, and the result is +inf. *)
    assert (Ew : Bplus mode_UP u v = B754_infinity false).
    { apply B2SF_inj. rewrite HO. reflexivity. }
    rewrite Ew. split; [right; reflexivity|]. split; [intros s _; exact I|].
    intros z [Fz| ->] Hz; [|intros s _; exact I].
    exfalso. rewrite (bound_finite _ Fz) in Hz.
    assert (Hle : B2R u + B2R v <= B2R z) by exact (Hz _ (Rle_refl _)).
    pose proof (Hmin _ (generic_format_B2R _ _ z) Hle).
    pose proof (B2R_Bsign_false u Su). pose proof (B2R_Bsign_false v (eq_sym Hs)).
    rewrite Rabs_pos_eq in Hov by lra.
    pose proof (abs_B2R_lt_emax _ _ z). pose proof (Rle_abs (B2R z)). lra.
Qed.

(** ** The tightest interval *)

Lemma is_tightest_ext :
  forall s1 s2 y, (forall r, s1 r <-> s2 r) -> is_tightest s1 y -> is_tightest s2 y.
Proof.
intros s1 s2 y H (Hy & Hin & Hmin). split; [exact Hy|]. split.
- intros r Hr. apply Hin, H, Hr.
- intros z Hz Hs. apply (Hmin z Hz). intros r Hr. apply Hs, H, Hr.
Qed.

Lemma tightest_empty :
  forall s, (forall u, ~ s u) -> is_tightest s Interval.EMPTY.
Proof.
intros s Hs. split; [left; split; reflexivity|]. split.
- intros u Hu. destruct (Hs u Hu).
- intros z _ _ r Hr. destruct (mem_nan Interval.EMPTY r eq_refl Hr).
Qed.

(** [z] is the tightest interval that contains [S] if its first lane is the
    least float or +inf at or above the largest negation of an element of
    [S], and its second lane the least at or above the largest element. *)
Lemma tightest_lanes :
  forall S z lo hi, (exists s, S s) ->
  tight lo (fun u => S (- u)) -> tight hi S ->
  least_lane lo (fst (rep z)) -> least_lane hi (snd (rep z)) ->
  is_tightest S z.
Proof.
intros S z lo hi [s0 Hs0] Tlo Thi (U0 & Le0 & Min0) (U1 & Le1 & Min1).
pose proof (lower_ok_lane _ U0) as Ha.
(* The lower bound of [z] is [-] its first lane. *)
assert (Lo : forall s, below (bound (fst (rep z))) (- s) <->
                       above (bound (opp (fst (rep z)))) s).
{ intros s. rewrite bound_lane. apply below_oopp. }
(* Each element of [S] is between the bounds. *)
assert (Hin : forall s, S s ->
              in_bounds (bound (opp (fst (rep z)))) (bound (snd (rep z))) s).
{ intros s Hs. apply in_bounds_iff. split.
  - apply Lo, Le0, Tlo. exists (- s). rewrite Ropp_involutive.
    split; [exact Hs | apply Rle_refl].
  - apply Le1, Thi. exists s. split; [exact Hs | apply Rle_refl]. }
split; [exact (valid_bounds z Ha U1 (in_bounds_ordered _ _ s0 (Hin s0 Hs0)))|].
split; [intros s Hs; exact (proj2 (mem_bounds z s Ha U1) (Hin s Hs))|].
intros z' Hz' Hs r Hr.
(* [z'] is nonempty, and its lanes are upper bounds above those of [S],
   so above those of [z]. *)
pose proof (mem_not_empty z' s0 Hz' (Hs s0 Hs0)) as Ez'.
destruct (lanes_ok z' Hz' Ez') as (U0' & U1' & _ & L0' & L1').
assert (M0 : ule (bound (fst (rep z))) (bound (fst (rep z')))).
{ apply (Min0 _ U0'). intros s Hlo.
  destruct (proj1 (Tlo s) Hlo) as (u & Hu & Hsu).
  pose proof (L0' (- s)) as H. rewrite Ropp_involutive in H. apply H.
  exists (- u). split; [exact (Hs _ Hu) | lra]. }
assert (M1 : ule (bound (snd (rep z))) (bound (snd (rep z')))).
{ apply (Min1 _ U1'). intros s Hhi.
  destruct (proj1 (Thi s) Hhi) as (u & Hu & Hsu).
  apply L1'. exists u. split; [exact (Hs _ Hu) | exact Hsu]. }
(* [r] is between two reals of [z']. *)
apply (mem_bounds z r Ha U1), in_bounds_iff in Hr. destruct Hr as [Hr0 Hr1].
apply Lo, M0, L0' in Hr0. apply M1, L1' in Hr1.
destruct Hr0 as (r1 & Hr1' & H1), Hr1 as (r2 & Hr2 & H2).
exact (mem_between z' r1 r2 r Hz' Hr1' Hr2 (conj H1 H2)).
Qed.

(** ** The theorems *)

(** [x + y] of [Interval]s returns the tightest interval that contains the
    image of [x × y] under [+]. *)
Theorem add_correct :
  forall x y, valid x -> valid y ->
  exists z, Interval.add x y = Some z /\ is_tightest (image2 Rplus x y) z.
Proof.
intros x y Hx Hy. unfold Interval.add. cbv zeta. rewrite add_ru_correct.
eexists. split; [reflexivity|].
destruct (is_nan (fst (rep x)) || is_nan (fst (rep y))) eqn:Hn.
- (* An empty argument gives NaN in both lanes, the empty interval. *)
  apply Bool.orb_true_iff in Hn.
  assert (N : rep x = (B754_nan, B754_nan) \/ rep y = (B754_nan, B754_nan)).
  { destruct Hn as [Hn|Hn]; [left | right]; now apply empty_nan. }
  replace (Bplus mode_UP (fst (rep x)) (fst (rep y)),
           Bplus mode_UP (snd (rep x)) (snd (rep y)))
    with (@B754_nan 53 1024, @B754_nan 53 1024)
    by (destruct N as [E|E]; rewrite E; cbn [fst snd];
        [reflexivity | destruct (fst (rep x)), (snd (rep x)); reflexivity]).
  apply tightest_empty, image2_empty.
  destruct N as [E|E]; [left | right]; intros r; exact (mem_nan _ r E).
- apply Bool.orb_false_iff in Hn. destruct Hn as [Hnx Hny].
  destruct (lanes_tight x Hx Hnx) as (Ux0 & Ux1 & [r0 Hr0] & Tx0 & Tx1).
  destruct (lanes_tight y Hy Hny) as (Uy0 & Uy1 & [t0 Ht0] & Ty0 & Ty1).
  apply (tightest_lanes _ _
    (uplus (bound (fst (rep x))) (bound (fst (rep y))))
    (uplus (bound (snd (rep x))) (bound (snd (rep y))))).
  + exists (r0 + t0). now apply image2_mem.
  + (* The largest negation of a sum is the sum of the largest negations. *)
    apply (tight_ext _ (fun s => exists r t, mem (- r) x /\ mem (- t) y /\ s = r + t)).
    * intros s. split.
      -- intros (r & t & Hr & Ht & ->). exists (- r), (- t).
         split; [exact Hr|]. split; [exact Ht | ring].
      -- intros (r & t & Hr & Ht & E). exists (- r), (- t).
         rewrite !Ropp_involutive. split; [exact Hr|]. split; [exact Ht | lra].
    * apply (tight_sum _ _ (fun r => mem (- r) x) (fun t => mem (- t) y));
        [exact Tx0 | exact Ty0 | exists (- r0) | exists (- t0)];
        now rewrite Ropp_involutive.
  + apply (tight_sum _ _ (fun r => mem r x) (fun t => mem t y));
      [exact Tx1 | exact Ty1 | exists r0; exact Hr0 | exists t0; exact Ht0].
  + apply add_lane; assumption.
  + apply add_lane; assumption.
Qed.

(** [x - y] of [Interval]s is [x + (-y)], and [r - t] is [r + (-t)]. *)
Theorem sub_correct :
  forall x y, valid x -> valid y ->
  exists z, Interval.sub x y = Some z /\ is_tightest (image2 Rminus x y) z.
Proof.
intros x y Hx Hy. destruct (neg_mem y Hy) as (Hv & Hm).
destruct (add_correct x (Interval.neg y) Hx Hv) as (z & E & Hz).
exists z. split; [exact E|].
apply (is_tightest_ext (image2 Rplus x (Interval.neg y)) _ z); [|exact Hz]. intros s. split.
- intros (r & t & Hr & Ht & ->). exists r, (- t).
  split; [exact Hr|]. split; [apply Hm, Ht | ring].
- intros (r & t & Hr & Ht & ->). exists r, (- t).
  split; [exact Hr|]. split; [apply Hm; now rewrite Ropp_involutive | ring].
Qed.

(** ** The decorated versions *)

Lemma Rplus_continuous : forall r t, continuity2_pt Rplus r t.
Proof.
intros r t eps Heps. exists (eps / 2). split; [lra|].
intros r' t' _ _ Hr Ht. apply Rabs_def2 in Hr, Ht.
apply Rabs_def1; lra.
Qed.

Lemma Rminus_continuous : forall r t, continuity2_pt Rminus r t.
Proof.
intros r t eps Heps. exists (eps / 2). split; [lra|].
intros r' t' _ _ Hr Ht. apply Rabs_def2 in Hr, Ht.
apply Rabs_def1; lra.
Qed.

(** A nonempty box whose image under [+] is bounded is bounded:
    [|r| <= |r + t0| + |t0|] for a [t0] in [y], and
    [|t| <= |r0 + t| + |r0|] for an [r0] in [x]. *)
Lemma plus_box_bounded :
  forall x y, (exists r, mem r x) -> (exists t, mem t y) ->
  bounded (image2 Rplus x y) ->
  bounded (fun r => mem r x) /\ bounded (fun t => mem t y).
Proof.
intros x y [r0 Hr0] [t0 Ht0] (m & Hm). split.
- exists (m + Rabs t0). intros r Hr.
  pose proof (Hm _ (image2_mem Rplus x y r t0 Hr Ht0)) as H.
  pose proof (Rabs_triang (r + t0) (- t0)) as T. rewrite Rabs_Ropp in T.
  replace (r + t0 + - t0) with r in T by ring. lra.
- exists (m + Rabs r0). intros t Ht.
  pose proof (Hm _ (image2_mem Rplus x y r0 t Hr0 Ht)) as H.
  pose proof (Rabs_triang (r0 + t) (- r0)) as T. rewrite Rabs_Ropp in T.
  replace (r0 + t + - r0) with t in T by ring. lra.
Qed.

(** The same for [-]: [|r| <= |r - t0| + |t0|] and
    [|t| <= |r0 - t| + |r0|]. *)
Lemma minus_box_bounded :
  forall x y, (exists r, mem r x) -> (exists t, mem t y) ->
  bounded (image2 Rminus x y) ->
  bounded (fun r => mem r x) /\ bounded (fun t => mem t y).
Proof.
intros x y [r0 Hr0] [t0 Ht0] (m & Hm). split.
- exists (m + Rabs t0). intros r Hr.
  pose proof (Hm _ (image2_mem Rminus x y r t0 Hr Ht0)) as H.
  pose proof (Rabs_triang (r - t0) t0) as T.
  replace (r - t0 + t0) with r in T by ring. lra.
- exists (m + Rabs r0). intros t Ht.
  pose proof (Hm _ (image2_mem Rminus x y r0 t Hr0 Ht)) as H.
  pose proof (Rabs_triang (- (r0 - t)) r0) as T. rewrite Rabs_Ropp in T.
  replace (- (r0 - t) + r0) with t in T by ring. lra.
Qed.

(** [x + y] of [DecInterval]s returns NaI if either argument is NaI, and
    otherwise the tightest interval, decorated with the decoration that
    IEEE 1788 asks for. *)
Theorem dec_add_correct :
  forall x y, valid (itv x) -> valid (itv y) ->
  exists z, DecInterval.add x y = Some z /\
    if DecInterval.is_nai x || DecInterval.is_nai y then z = DecInterval.NAI
    else
      is_tightest (image2 Rplus (itv x) (itv y)) (itv z) /\
      exists d, strongest2 d Rplus (itv x) (itv y) (itv z) /\
        dec z = dec_min d (dec_min (dec x) (dec y)).
Proof.
intros x y Hx Hy. unfold DecInterval.add.
destruct (DecInterval.is_nai x || DecInterval.is_nai y) eqn:N;
  [exists DecInterval.NAI; split; reflexivity|].
apply Bool.orb_false_iff in N. destruct N as [Nx Ny].
unfold DecInterval.is_nai in Nx, Ny.
assert (He : dec_min (dec x) (dec y) <> Ill).
{ apply dec_min_not_Ill; intros E; [rewrite E in Nx | rewrite E in Ny];
    discriminate. }
destruct (add_correct _ _ Hx Hy) as (z & -> & Hz). cbv beta iota.
exists (DecInterval.set_dec z (dec_min (dec x) (dec y))). split; [reflexivity|].
destruct (set_dec_correct Rplus Rplus_continuous _ _ z _ Hx Hy He Hz
  (fun _ => plus_box_bounded (itv x) (itv y))) as (E & d & Hd & Ed).
rewrite E. split; [exact Hz|]. exists d. split; [exact Hd | exact Ed].
Qed.

(** [x - y] of [DecInterval]s does the same for [-]. *)
Theorem dec_sub_correct :
  forall x y, valid (itv x) -> valid (itv y) ->
  exists z, DecInterval.sub x y = Some z /\
    if DecInterval.is_nai x || DecInterval.is_nai y then z = DecInterval.NAI
    else
      is_tightest (image2 Rminus (itv x) (itv y)) (itv z) /\
      exists d, strongest2 d Rminus (itv x) (itv y) (itv z) /\
        dec z = dec_min d (dec_min (dec x) (dec y)).
Proof.
intros x y Hx Hy. unfold DecInterval.sub.
destruct (DecInterval.is_nai x || DecInterval.is_nai y) eqn:N;
  [exists DecInterval.NAI; split; reflexivity|].
apply Bool.orb_false_iff in N. destruct N as [Nx Ny].
unfold DecInterval.is_nai in Nx, Ny.
assert (He : dec_min (dec x) (dec y) <> Ill).
{ apply dec_min_not_Ill; intros E; [rewrite E in Nx | rewrite E in Ny];
    discriminate. }
destruct (sub_correct _ _ Hx Hy) as (z & -> & Hz). cbv beta iota.
exists (DecInterval.set_dec z (dec_min (dec x) (dec y))). split; [reflexivity|].
destruct (set_dec_correct Rminus Rminus_continuous _ _ z _ Hx Hy He Hz
  (fun _ => minus_box_bounded (itv x) (itv y))) as (E & d & Hd & Ed).
rewrite E. split; [exact Hz|]. exists d. split; [exact Hd | exact Ed].
Qed.
