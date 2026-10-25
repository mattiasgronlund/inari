(** * [sign] of intervals is tightest and decorated correctly

    [Interval::sign] returns the hull of the image of its argument, and
    [DecInterval::sign] decorates it with the minimum of the strongest
    decoration that holds and the decoration of its argument, as IEEE 1788
    asks of a tightest interval version of a function, if the argument is
    [com] only when its interval is common (see below).

    An [Interval] stores [[a, b]] as [[-a; b]], and [Interval::sign]
    compares both lanes with [0.0]. The masks of the comparisons keep [1.0] in the lanes above 0
    and [-1.0] in the lanes below it, and [or] combines the two, which
    leaves [0.0] in a lane that is neither. So each lane holds its own sign,
    the first lane [sign (-a) = -sign a] and the second [sign b], and the
    result is [[sign a, sign b]]. As [sign] is nondecreasing, that is the
    hull of the image. An infinite bound gives [-1] or [1], which [sign]
    takes on the reals far enough out.

    [sign] is continuous except at 0. If [sign a = sign b], the restriction
    of [sign] to [[a, b]] is constant, and [sign] is continuous at each
    point of [[a, b]] unless 0 is in it. With [sign a = sign b], that is only
    [[0, 0]], which is when [a = 0], the test [x.inf_raw() == 0.0] in
    [impl_dec!(sign, ...)]. Otherwise [[a, b]] contains 0 and a nonzero
    real, so the restriction of [sign] jumps at 0.

    An unbounded interval on which [sign] is constant, such as [[1, +inf]],
    maps to a singleton, [[1, 1]], for which [impl_dec] computes [com],
    where the strongest decoration is [dac], as [com] asks for a bounded
    argument. The result is still right if the decoration of the argument
    is not [com], as the minimum with it is then the same for [com] and
    [dac]. [DecInterval::new], [set_dec] and the other constructors of the
    library make a [DecInterval] [com] only if its interval is common, but
    nothing here proves it, so [dec_sign_correct] takes it as a
    hypothesis. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Ieee1788 Integer.

Open Scope R_scope.

(** ** [sign] of a real *)

Lemma Rsign_neg : forall r, r < 0 -> Rsign r = -1.
Proof.
intros r H. unfold Rsign. now rewrite Rcompare_Lt.
Qed.

Lemma Rsign_pos : forall r, 0 < r -> Rsign r = 1.
Proof.
intros r H. unfold Rsign. now rewrite Rcompare_Gt.
Qed.

Lemma Rsign_0 : Rsign 0 = 0.
Proof.
unfold Rsign. now rewrite Rcompare_Eq.
Qed.

Lemma Rsign_le : forall u v, u <= v -> Rsign u <= Rsign v.
Proof.
intros u v H. unfold Rsign.
case (Rcompare_spec u 0); case (Rcompare_spec v 0); intros Hv Hu; cbv iota;
  lra.
Qed.

Lemma Rsign_bounds : forall r, -1 <= Rsign r <= 1.
Proof.
intros r. unfold Rsign. case (Rcompare_spec r 0); intros H; cbv iota; lra.
Qed.

Lemma Rsign_opp : forall r, Rsign (- r) = - Rsign r.
Proof.
intros r. unfold Rsign.
case (Rcompare_spec (- r) 0); case (Rcompare_spec r 0); intros H1 H2; cbv iota;
  lra.
Qed.

Lemma Rsign_zero : forall r, Rsign r = 0 -> r = 0.
Proof.
intros r. unfold Rsign. case (Rcompare_spec r 0); intros H E; cbv iota in E;
  lra.
Qed.

(** ** [sign] of a float *)

Lemma is_finite_opp : forall a, is_finite (opp a) = is_finite a.
Proof.
intros a. apply is_finite_Bopp.
Qed.

Lemma B2R_opp : forall a, B2R (opp a) = - B2R a.
Proof.
intros a. apply B2R_Bopp.
Qed.

Lemma bound_finite : forall a, is_finite a = true -> bound a = Some (B2R a).
Proof.
intros a Fa. unfold bound. now rewrite Fa.
Qed.

Lemma bound_inf : forall s, bound (B754_infinity s) = None.
Proof.
reflexivity.
Qed.

(** [1.0]. *)
Definition one : f64 := of_u64 1.

Lemma one_B2R : is_finite one = true /\ B2R one = 1.
Proof.
split; [vm_compute; reflexivity|].
rewrite <- SF2R_B2SF.
replace (B2SF one) with (SpecFloat.S754_finite false 4503599627370496 (-52))
  by (vm_compute; reflexivity).
unfold SF2R, F2R. cbn [Fnum Fexp SpecFloat.cond_Zopp].
change (bpow radix2 (-52)) with (/ 4503599627370496).
lra.
Qed.

(** What [Interval::sign] computes in a lane [v], and its value. *)
Definition fsign (v : f64) : f64 :=
  if gt v zero then one else if lt v zero then opp one else zero.
Definition vsign (v : f64) : R :=
  if gt v zero then 1 else if lt v zero then -1 else 0.

Lemma gt_lt_zero : forall v, gt v zero = true -> lt v zero = false.
Proof.
intros [s|s| |s m e H]; try destruct s; easy.
Qed.

Lemma fsign_finite : forall v, is_finite (fsign v) = true.
Proof.
intros v. unfold fsign.
destruct (gt v zero); [|destruct (lt v zero)]; vm_compute; reflexivity.
Qed.

Lemma fsign_not_nan : forall v, is_nan (fsign v) = false.
Proof.
intros v. unfold fsign.
destruct (gt v zero); [|destruct (lt v zero)]; vm_compute; reflexivity.
Qed.

Lemma fsign_B2R : forall v, B2R (fsign v) = vsign v.
Proof.
intros v. unfold fsign, vsign.
destruct (gt v zero); [exact (proj2 one_B2R)|].
destruct (lt v zero); [|reflexivity].
rewrite B2R_opp, (proj2 one_B2R). lra.
Qed.

Lemma vsign_finite : forall v, is_finite v = true -> vsign v = Rsign (B2R v).
Proof.
intros v Fv. unfold vsign, gt, lt, Rsign.
rewrite !Bltb_correct by first [exact Fv | reflexivity].
change (B2R zero) with 0.
case (Rlt_bool_spec 0 (B2R v)); intros H1;
  case (Rlt_bool_spec (B2R v) 0); intros H2;
  case (Rcompare_spec (B2R v) 0); intros H3; cbv iota; lra.
Qed.

(** One lane of [Interval::sign], with the masks as their bit patterns. *)
Lemma sign_lane :
  forall v,
  from_bits
    (Z.lor
       (to_bits (from_bits (Z.land (to_bits (of_u64 1)) (Generic.mask (gt v zero)))))
       (to_bits (from_bits
          (Z.land (to_bits (opp (of_u64 1))) (Generic.mask (lt v zero)))))) =
  fsign v.
Proof.
intros v. unfold fsign.
destruct (gt v zero) eqn:G; [rewrite (gt_lt_zero v G) | destruct (lt v zero)];
  apply B2SF_inj; vm_compute; reflexivity.
Qed.

Lemma sign_rep :
  forall x, Interval.is_empty x = false ->
  rep (Interval.sign x) = (fsign (fst (rep x)), fsign (snd (rep x))).
Proof.
intros x Hx. unfold Interval.sign. rewrite Hx. cbv beta iota zeta.
unfold Generic.or, Generic.and, Generic.gt, Generic.lt, Generic.splat.
cbn [rep fst snd].
f_equal; apply sign_lane.
Qed.

Lemma sign_empty :
  forall x, Interval.is_empty x = true -> Interval.sign x = Interval.EMPTY.
Proof.
intros x Hx. unfold Interval.sign. now rewrite Hx.
Qed.

Lemma sign_not_empty :
  forall x, Interval.is_empty x = false -> Interval.is_empty (Interval.sign x) = false.
Proof.
intros x Hx. unfold Interval.is_empty at 1. rewrite (sign_rep x Hx).
exact (fsign_not_nan _).
Qed.

(** ** The bounds of the result *)

(** [sign] of the bounds [lo] and [hi] of [in_bounds], where [None] is
    -inf for [lo] and +inf for [hi]. *)
Definition lsign (lo : option R) : R :=
  match lo with Some a => Rsign a | None => -1 end.
Definition usign (hi : option R) : R :=
  match hi with Some b => Rsign b | None => 1 end.

(** The first lane holds [-a], and [sign (-a) = -sign a]. *)
Lemma lower_sign :
  forall a, lower_ok (opp a) -> - vsign a = lsign (bound (opp a)).
Proof.
intros a [Fa|Ea].
- rewrite (bound_finite _ Fa). cbn [lsign].
  rewrite is_finite_opp in Fa.
  now rewrite B2R_opp, Rsign_opp, (vsign_finite a Fa).
- assert (E : a = B754_infinity false).
  { rewrite <- (Bopp_involutive _ _ a). unfold opp in Ea. now rewrite Ea. }
  rewrite Ea, bound_inf, E. cbn [lsign].
  assert (V : vsign (B754_infinity false) = 1) by reflexivity.
  rewrite V. lra.
Qed.

Lemma upper_sign : forall b, upper_ok b -> vsign b = usign (bound b).
Proof.
intros b [Fb| ->].
- rewrite (bound_finite _ Fb). cbn [usign]. exact (vsign_finite b Fb).
- reflexivity.
Qed.

Lemma lsign_le_usign : forall lo hi, ordered lo hi -> lsign lo <= usign hi.
Proof.
intros [a|] [b|] H; cbn [lsign usign ordered] in *.
- now apply Rsign_le.
- exact (proj2 (Rsign_bounds a)).
- exact (proj1 (Rsign_bounds b)).
- lra.
Qed.

(** Both bounds of the result are finite, and they are [sign] of those of
    the argument. *)
Lemma sign_bounds :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  is_finite (opp (fst (rep (Interval.sign x)))) = true /\
  is_finite (snd (rep (Interval.sign x))) = true /\
  B2R (opp (fst (rep (Interval.sign x)))) = lsign (bound (opp (fst (rep x)))) /\
  B2R (snd (rep (Interval.sign x))) = usign (bound (snd (rep x))).
Proof.
intros x Hx Hn. destruct (valid_nonempty x Hx Hn) as (Ha & Hb & _).
rewrite (sign_rep x Hn). cbn [fst snd].
rewrite is_finite_opp, B2R_opp, !fsign_B2R.
split; [apply fsign_finite|]. split; [apply fsign_finite|].
split; [now apply lower_sign | now apply upper_sign].
Qed.

(** ** The hull *)

(** The hull of the image of the reals between [lo] and [hi] under
    [sign]. *)
Lemma sign_hull :
  forall (X : R -> Prop) lo hi,
  (forall r, X r <-> in_bounds lo hi r) -> ordered lo hi ->
  forall r,
  lsign lo <= r <= usign hi <->
  exists u v, (exists t, X t /\ u = Rsign t) /\ (exists t, X t /\ v = Rsign t) /\
    u <= r <= v.
Proof.
intros X lo hi HX Hord r. split.
- intros [Hlo Hhi].
  assert (Hu : exists t, X t /\ Rsign t <= r).
  { destruct lo as [a|].
    - exists a. split; [|exact Hlo]. apply HX. split; [apply Rle_refl|].
      destruct hi; [exact Hord | exact I].
    - (* A real below both [-1] and [hi]. *)
      set (t := match hi with Some b => Rmin (-1) b | None => -1 end).
      assert (Ht : t <= -1).
      { unfold t. destruct hi; [apply Rmin_l | apply Rle_refl]. }
      exists t. split.
      + apply HX. split; [exact I|].
        unfold t. destruct hi; [apply Rmin_r | exact I].
      + rewrite Rsign_neg by lra. exact Hlo. }
  assert (Hv : exists t, X t /\ r <= Rsign t).
  { destruct hi as [b|].
    - exists b. split; [|exact Hhi]. apply HX. split; [|apply Rle_refl].
      destruct lo; [exact Hord | exact I].
    - (* A real above both [1] and [lo]. *)
      set (t := match lo with Some a => Rmax 1 a | None => 1 end).
      assert (Ht : 1 <= t).
      { unfold t. destruct lo; [apply Rmax_l | apply Rle_refl]. }
      exists t. split.
      + apply HX. split; [|exact I].
        unfold t. destruct lo; [apply Rmax_r | exact I].
      + rewrite Rsign_pos by lra. exact Hhi. }
  destruct Hu as (t1 & Ht1 & Hu), Hv as (t2 & Ht2 & Hv).
  exists (Rsign t1), (Rsign t2).
  split; [exists t1; split; [exact Ht1 | reflexivity]|].
  split; [exists t2; split; [exact Ht2 | reflexivity]|].
  split; [exact Hu | exact Hv].
- intros (u & v & (t1 & Ht1 & ->) & (t2 & Ht2 & ->) & Hr).
  apply HX in Ht1, Ht2.
  destruct Ht1 as [Ht1 _], Ht2 as [_ Ht2]. split.
  + apply Rle_trans with (Rsign t1); [|apply Hr].
    destruct lo as [a|]; cbn [lsign];
      [now apply Rsign_le | exact (proj1 (Rsign_bounds t1))].
  + apply Rle_trans with (Rsign t2); [apply Hr|].
    destruct hi as [b|]; cbn [usign];
      [now apply Rsign_le | exact (proj2 (Rsign_bounds t2))].
Qed.

(** [Interval::sign] returns the tightest interval that contains the image
    of its argument under [sign]. *)
Theorem sign_correct :
  forall x, valid x -> is_hull (image Rsign x) (Interval.sign x).
Proof.
intros x Hx.
destruct (is_nan (fst (rep x))) eqn:Hn.
- rewrite (sign_empty x Hn). apply is_hull_empty.
  intros u (r & Hr & _). exact (mem_nan x r (empty_nan x Hx Hn) Hr).
- destruct (valid_nonempty x Hx Hn) as (Ha & Hb & Hord).
  destruct (sign_bounds x Hx Hn) as (Fa & Fb & Ea & Eb).
  assert (HX : forall r, mem r x <->
                 in_bounds (bound (opp (fst (rep x)))) (bound (snd (rep x))) r).
  { intros r. now apply mem_bounds. }
  split.
  + apply valid_bounds; [left; exact Fa | left; exact Fb|].
    rewrite (bound_finite _ Fa), (bound_finite _ Fb), Ea, Eb.
    exact (lsign_le_usign _ _ Hord).
  + intros r. rewrite mem_bounds by (left; assumption).
    rewrite (bound_finite _ Fa), (bound_finite _ Fb), Ea, Eb.
    exact (sign_hull (fun r => mem r x) _ _ HX Hord r).
Qed.

(** ** Continuity *)

(** [sign] jumps by 1 at 0 on either side, so its restriction to [X] is not
    continuous at 0 if [X] has nonzero reals arbitrarily close to it. *)
Lemma sign_discontinuous :
  forall (X : R -> Prop),
  (forall d, 0 < d -> exists s, X s /\ s <> 0 /\ Rabs s < d) ->
  ~ continue_in Rsign X 0.
Proof.
intros X HX Hc.
assert (H1 : 1 > 0) by lra.
destruct (Hc 1 H1) as (alp & Halp & H).
destruct (HX alp Halp) as (s & Hs & Hs0 & Hsa).
assert (Hlt : Rabs (Rsign s - Rsign 0) < 1).
{ apply H. split.
  - split; [exact Hs | intros Heq; apply Hs0; symmetry; exact Heq].
  - change (Rabs (s - 0) < alp). now rewrite Rminus_0_r. }
rewrite Rsign_0 in Hlt.
destruct (Rdichotomy s 0 Hs0) as [Hneg|Hpos].
- rewrite Rsign_neg, Rabs_left in Hlt by lra. lra.
- rewrite Rsign_pos, Rabs_pos_eq in Hlt by lra. lra.
Qed.

(** [sign] is constant on each side of 0. *)
Lemma sign_continuous : forall r, r <> 0 -> continuity_pt Rsign r.
Proof.
intros r Hr eps Heps.
exists (Rabs r). split; [now apply Rabs_pos_lt|].
intros s [_ Hs]. change (Rabs (s - r) < Rabs r) in Hs.
change (Rabs (Rsign s - Rsign r) < eps).
assert (E : Rsign s = Rsign r).
{ apply Rabs_def2 in Hs. destruct (Rdichotomy r 0 Hr) as [Hneg|Hpos].
  - rewrite (Rabs_left r) in Hs by exact Hneg.
    rewrite !Rsign_neg by lra. reflexivity.
  - rewrite (Rabs_pos_eq r) in Hs by lra.
    rewrite !Rsign_pos by lra. reflexivity. }
rewrite E. unfold Rminus. rewrite Rplus_opp_r, Rabs_R0. exact Heps.
Qed.

(** If [x] contains 0 and a nonzero real, the restriction of [sign] to [x]
    is not continuous at 0. *)
Lemma sign_jump :
  forall x lo hi t,
  (forall r, mem r x <-> in_bounds lo hi r) ->
  in_bounds lo hi 0 -> in_bounds lo hi t -> t <> 0 ->
  ~ p Dac Rsign x.
Proof.
intros x lo hi t HX H0 Ht Ht0 [_ Hc].
apply (sign_discontinuous (fun r => mem r x)).
- intros d Hd. destruct (Rdichotomy t 0 Ht0) as [Hneg|Hpos].
  + assert (Hm : Rmax t (- d / 2) < 0) by (apply Rmax_lub_lt; lra).
    exists (Rmax t (- d / 2)). split; [|split].
    * apply HX. apply (in_bounds_between lo hi t 0); [exact Ht | exact H0 |].
      split; [apply Rmax_l | lra].
    * now apply Rlt_not_eq.
    * rewrite Rabs_left by exact Hm. generalize (Rmax_r t (- d / 2)). lra.
  + assert (Hm : 0 < Rmin t (d / 2)) by (apply Rmin_glb_lt; lra).
    exists (Rmin t (d / 2)). split; [|split].
    * apply HX. apply (in_bounds_between lo hi 0 t); [exact H0 | exact Ht |].
      split; [lra | apply Rmin_l].
    * now apply Rgt_not_eq.
    * rewrite Rabs_pos_eq by lra. generalize (Rmin_r t (d / 2)). lra.
- apply Hc, HX, H0.
Qed.

(** An interval with an infinite bound is not bounded. *)
Lemma unbounded_lo :
  forall x hi,
  (forall r, mem r x <-> in_bounds None hi r) -> ~ bounded (fun r => mem r x).
Proof.
intros x hi HX (m & Hm).
set (t := match hi with Some b => Rmin (- Rabs m - 1) b | None => - Rabs m - 1 end).
assert (Ht : t <= - Rabs m - 1).
{ unfold t. destruct hi; [apply Rmin_l | apply Rle_refl]. }
assert (Hx : mem t x).
{ apply HX. split; [exact I|]. unfold t. destruct hi; [apply Rmin_r | exact I]. }
specialize (Hm t Hx). generalize (Rabs_pos m) (RRle_abs m). intros H1 H2.
rewrite Rabs_left in Hm by lra. lra.
Qed.

Lemma unbounded_hi :
  forall x lo,
  (forall r, mem r x <-> in_bounds lo None r) -> ~ bounded (fun r => mem r x).
Proof.
intros x lo HX (m & Hm).
set (t := match lo with Some a => Rmax (Rabs m + 1) a | None => Rabs m + 1 end).
assert (Ht : Rabs m + 1 <= t).
{ unfold t. destruct lo; [apply Rmax_l | apply Rle_refl]. }
assert (Hx : mem t x).
{ apply HX. split; [|exact I]. unfold t. destruct lo; [apply Rmax_r | exact I]. }
specialize (Hm t Hx). generalize (Rabs_pos m) (RRle_abs m). intros H1 H2.
rewrite Rabs_pos_eq in Hm by lra. lra.
Qed.

(** If [sign] differs on the bounds, the reals between them contain 0 and
    a nonzero real. *)
Lemma sign_differs :
  forall lo hi, ordered lo hi -> lsign lo <> usign hi ->
  in_bounds lo hi 0 /\ exists t, in_bounds lo hi t /\ t <> 0.
Proof.
intros [a|] [b|] Hord Hs; cbn [lsign usign ordered in_bounds] in *.
- assert (H0 : a <= 0 <= b).
  { split.
    - destruct (Rle_or_lt a 0) as [H|H]; [exact H|].
      elim Hs. rewrite !Rsign_pos by lra. reflexivity.
    - destruct (Rle_or_lt 0 b) as [H|H]; [exact H|].
      elim Hs. rewrite !Rsign_neg by lra. reflexivity. }
  split; [exact H0|].
  destruct (Req_dec a 0) as [Ha|Ha].
  + exists b. split; [split; [lra | apply Rle_refl]|].
    intros Hb. elim Hs. now rewrite Ha, Hb.
  + exists a. split; [split; [apply Rle_refl | exact Hord] | exact Ha].
- destruct (Rle_or_lt a 0) as [H|H]; [|elim Hs; now apply Rsign_pos].
  split; [split; [exact H | exact I]|].
  exists 1. split; [split; [lra | exact I] | apply Rgt_not_eq; lra].
- destruct (Rle_or_lt 0 b) as [H|H]; [|elim Hs; symmetry; now apply Rsign_neg].
  split; [split; [exact I | exact H]|].
  exists (-1). split; [split; [exact I | lra] | apply Rlt_not_eq; lra].
- split; [split; exact I|].
  exists 1. split; [split; exact I | apply Rgt_not_eq; lra].
Qed.

(** ** The strongest decoration *)

(** The strongest decoration of [sign] on the reals between [lo] and [hi].
    Unlike [floor_dec], it is [dac] for an unbounded interval on which
    [sign] is constant, such as [[1, +inf]]. *)
Definition sign_dec (lo hi : option R) : Decoration :=
  if Req_bool (lsign lo) (usign hi) then
    match lo, hi with
    | Some a, Some _ => if Req_bool a 0 then Dac else Com
    | _, _ => Dac
    end
  else Def.

Lemma sign_strongest :
  forall x lo hi,
  (forall r, mem r x <-> in_bounds lo hi r) -> ordered lo hi ->
  strongest (sign_dec lo hi) Rsign x.
Proof.
intros x lo hi HX Hord.
assert (Hne : exists r, mem r x).
{ destruct (in_bounds_nonempty lo hi Hord) as (r & Hr). exists r. now apply HX. }
assert (Hcon : forall r, mem r x -> lsign lo <= Rsign r <= usign hi).
{ intros r Hr. apply HX in Hr. destruct Hr as [Hr1 Hr2]. split.
  - destruct lo as [a|]; cbn [lsign];
      [now apply Rsign_le | exact (proj1 (Rsign_bounds r))].
  - destruct hi as [b|]; cbn [usign];
      [now apply Rsign_le | exact (proj2 (Rsign_bounds r))]. }
unfold sign_dec. case (Req_bool_spec (lsign lo) (usign hi)); intros Hs.
- (* [sign] is constant on [x]. *)
  assert (Hdac : p Dac Rsign x).
  { split; [exact Hne|]. intros r Hr.
    apply continue_in_const with (c := lsign lo); [|exact Hr].
    intros s Hs'. generalize (Hcon s Hs'). lra. }
  destruct lo as [a|], hi as [b|]; cbv beta iota;
    cbn [lsign usign] in Hs, Hcon.
  + case (Req_bool_spec a 0); intros Ha.
    * (* [x] is [[0, 0]], and [sign] jumps at 0. *)
      apply strongest_Dac; [exact Hdac|].
      intros (_ & _ & Hc & _).
      apply (sign_discontinuous no_cond).
      -- intros d Hd. exists (d / 2). split; [exact I|].
         split; [apply Rgt_not_eq; lra | rewrite Rabs_pos_eq; lra].
      -- change (continuity_pt Rsign 0). apply Hc, HX.
         rewrite <- Ha. split; [apply Rle_refl | exact Hord].
    * (* [x] is bounded, and 0 is not in it. *)
      apply strongest_Com. split; [exact Hne|]. split; [|split].
      -- exists (Rabs a + Rabs b). intros r Hr. apply HX in Hr.
         now apply Rabs_between.
      -- intros r Hr. apply sign_continuous. intros Hr0.
         apply Ha, Rsign_zero. generalize (Hcon r Hr). rewrite Hr0, Rsign_0.
         lra.
      -- exists 1. intros s (r & _ & ->).
         generalize (Rsign_bounds r). intros H. apply Rabs_le. lra.
  + (* [x] is unbounded. *)
    apply strongest_Dac; [exact Hdac|].
    intros (_ & Hb & _). exact (unbounded_hi x (Some a) HX Hb).
  + apply strongest_Dac; [exact Hdac|].
    intros (_ & Hb & _). exact (unbounded_lo x (Some b) HX Hb).
  + apply strongest_Dac; [exact Hdac|].
    intros (_ & Hb & _). exact (unbounded_lo x None HX Hb).
- apply strongest_Def; [exact Hne|].
  destruct (sign_differs lo hi Hord Hs) as (H0 & t & Ht & Ht0).
  exact (sign_jump x lo hi t HX H0 Ht Ht0).
Qed.

(** ** What [impl_dec] tests *)

Lemma sign_singleton :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  Interval.is_singleton (Interval.sign x) =
    Req_bool (lsign (bound (opp (fst (rep x))))) (usign (bound (snd (rep x)))).
Proof.
intros x Hx Hn. destruct (sign_bounds x Hx Hn) as (Fa & Fb & Ea & Eb).
unfold Interval.is_singleton, Interval.inf_raw, Interval.sup_raw, eq.
rewrite Beqb_correct by assumption. now rewrite Ea, Eb.
Qed.

Lemma inf_zero_test :
  forall a, lower_ok a ->
  eq a zero = match bound a with Some r => Req_bool r 0 | None => false end.
Proof.
intros a [Fa| ->].
- rewrite (bound_finite _ Fa). unfold eq.
  rewrite Beqb_correct by first [exact Fa | reflexivity]. reflexivity.
- reflexivity.
Qed.

(** [impl_dec] computes [com] where [sign_dec] is [dac] on an unbounded
    interval, and both give the same decoration once the minimum with that
    of the argument is taken, which is not [com] then. *)
Lemma sign_test :
  forall x e, valid x -> is_nan (fst (rep x)) = false ->
  (e = Com -> Interval.is_common_interval x = true) ->
  dec_min (if Interval.is_singleton (Interval.sign x) then
             if eq (Interval.inf_raw x) zero then Dac else Com
           else Def) e =
  dec_min (sign_dec (bound (opp (fst (rep x)))) (bound (snd (rep x)))) e.
Proof.
intros x e Hx Hn He.
destruct (valid_nonempty x Hx Hn) as (Ha & Hb & _).
rewrite (sign_singleton x Hx Hn). unfold Interval.inf_raw.
rewrite (inf_zero_test _ Ha). unfold sign_dec.
destruct Ha as [Fa|Ea].
- destruct Hb as [Fb|Eb].
  + rewrite (bound_finite _ Fa), (bound_finite _ Fb). reflexivity.
  + (* [b = +inf] *)
    assert (Hnc : e <> Com).
    { intros E. specialize (He E).
      rewrite is_common_interval_lt, infinity_eq, Eb in He.
      apply Bool.andb_true_iff in He. destruct He as [_ He]. discriminate He. }
    rewrite Eb, bound_inf, (bound_finite _ Fa). cbv beta iota.
    case (Req_bool_spec (lsign (Some (B2R (opp (fst (rep x)))))) (usign None));
      intros _; [|reflexivity].
    case (Req_bool_spec (B2R (opp (fst (rep x)))) 0); intros _;
      destruct e; first [reflexivity | now elim Hnc].
- (* [a = -inf] *)
  assert (E0 : fst (rep x) = B754_infinity false).
  { rewrite <- (Bopp_involutive _ _ (fst (rep x))). unfold opp in Ea.
    now rewrite Ea. }
  assert (Hnc : e <> Com).
  { intros E. specialize (He E).
    rewrite is_common_interval_lt, infinity_eq, E0 in He. discriminate He. }
  rewrite Ea, bound_inf. cbv beta iota.
  case (Req_bool_spec (lsign None) (usign (bound (snd (rep x))))); intros _;
    [|reflexivity].
  destruct (bound (snd (rep x))); cbv beta iota;
    destruct e; first [reflexivity | now elim Hnc].
Qed.

(** ** The decorated version *)

(** [DecInterval::sign] returns a NaI unchanged, and otherwise the result of
    [Interval::sign] with the minimum of the strongest decoration of [sign]
    on the interval and the decoration of its argument, if the argument is
    [com] only when its interval is common. *)
Theorem dec_sign_correct :
  forall x, valid (itv x) ->
  (dec x = Com -> Interval.is_common_interval (itv x) = true) ->
  if DecInterval.is_nai x then DecInterval.sign x = x
  else
    is_hull (image Rsign (itv x)) (itv (DecInterval.sign x)) /\
    exists d, strongest d Rsign (itv x) /\
      dec (DecInterval.sign x) = dec_min d (dec x).
Proof.
intros x Hx Hcx. unfold DecInterval.sign, DecInterval.impl_dec. cbv zeta.
destruct (DecInterval.is_nai x) eqn:Hnai; [reflexivity|].
assert (Hdx : dec x <> Ill).
{ intros E. unfold DecInterval.is_nai in Hnai. now rewrite E in Hnai. }
destruct (is_nan (fst (rep (itv x)))) eqn:Hn.
- assert (Hx' : forall r, ~ mem r (itv x)).
  { intros r. exact (mem_nan _ r (empty_nan _ Hx Hn)). }
  assert (Hy : Interval.is_empty (Interval.sign (itv x)) = true).
  { rewrite (sign_empty (itv x) Hn). reflexivity. }
  rewrite Hy, set_dec_empty by assumption. split.
  + apply is_hull_empty. intros u (r & Hr & _). exact (Hx' r Hr).
  + exists Trv. split; [now apply strongest_Trv|].
    cbn. destruct (dec x); first [reflexivity | congruence].
- destruct (valid_nonempty (itv x) Hx Hn) as (_ & _ & Hord).
  assert (HX : forall r, mem r (itv x) <->
                 in_bounds (bound (opp (fst (rep (itv x)))))
                   (bound (snd (rep (itv x)))) r).
  { intros r. destruct (valid_nonempty (itv x) Hx Hn) as (Ha & Hb & _).
    now apply mem_bounds. }
  rewrite (sign_not_empty (itv x) Hn).
  set (d := if Interval.is_singleton (Interval.sign (itv x)) then
              if eq (Interval.inf_raw (itv x)) zero then Dac else Com
            else Def).
  assert (Ed : (if negb (Interval.is_singleton (Interval.sign (itv x))) then Def
                else if eq (Interval.inf_raw (itv x)) zero then Dac else Com) = d).
  { unfold d. now destruct (Interval.is_singleton (Interval.sign (itv x))). }
  rewrite Ed.
  assert (Hd : d <> Ill).
  { unfold d. destruct (Interval.is_singleton _), (eq _ _); discriminate. }
  rewrite set_dec_nonempty.
  + split; [now apply sign_correct|].
    exists (sign_dec (bound (opp (fst (rep (itv x))))) (bound (snd (rep (itv x))))).
    split; [now apply sign_strongest|].
    cbn [dec DecInterval.new_unchecked]. unfold d.
    apply sign_test; assumption.
  + now apply sign_not_empty.
  + exact Hd.
  + exact Hdx.
  + intros _. destruct (sign_bounds (itv x) Hx Hn) as (Fa & Fb & _).
    now apply finite_common.
Qed.
