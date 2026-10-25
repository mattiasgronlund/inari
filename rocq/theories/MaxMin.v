(** * [max] and [min] of intervals are tightest

    [Interval::max] and [Interval::min] return the hull of the image of
    their arguments, as IEEE 1788 asks of a tightest interval version of a
    function of two reals.

    An [Interval] stores [[a, b]] as [[-a; b]], and an empty one as
    [[NaN; NaN]]. With [HAS_MAXIMUM], [Interval::max] of [[a, b]] and
    [[c, d]] takes [minimum] of the first lanes and [maximum] of the
    second, [[min(-a, -c); max(b, d)]], which is [[-max(a, c); max(b, d)]],
    and [Interval::min] takes [[max(-a, -c); min(b, d)]], which is
    [[-min(a, c); min(b, d)]]. [maximum] and [minimum] give NaN in a lane
    if either argument is NaN there, so an empty argument gives an empty
    result, the hull of the image of an empty box.

    Both lanes of a nonempty interval have the form of an upper bound,
    finite or +inf, as [-a] is +inf when [a] is -inf. On such floats,
    [max1] and [min1] are [Rmax] and [Rmin] of the values, with +inf as the
    largest value (Section [max1] and [min1] on lanes). Two zeros give a
    zero of one sign or the other, whose value is 0 either way. So the
    first lane of [Interval::max] is [min1] of the first lanes, and the
    second lane of [Interval::min] is [min1] of the second lanes, and one
    lemma serves both, as another serves for [max1].

    The hull follows from the extreme points of the image. A real [s] is
    above the lower bound of the result exactly when some point of the
    image is at most [s], and below its upper bound exactly when some
    point of the image is at least [s] ([hull_lanes]). For [max],
    [max(r, t) <= s] exactly when [r <= s] and [t <= s], and
    [s <= max(r, t)] exactly when [s <= r] or [s <= t], and dually for
    [min]. Some real in [[a, b]] is at most [s] exactly when [a <= s], and
    at least [s] exactly when [s <= b], so [max(r, t) <= s] for some [r]
    in [[a, b]] and [t] in [[c, d]] exactly when [max(a, c) <= s], and
    [min(r, t) <= s] for some such [r] and [t] exactly when
    [min(a, c) <= s], and likewise for the upper bounds. Neither needs the
    cases of infinite bounds apart: they are the bounds [None] of
    [in_bounds], above or below every real. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Ieee1788 Integer Sign.

Open Scope R_scope.

(* The lane functions of the backend, without importing [Generic], whose
   [gt] and [lt] on [F64X2] would hide those on [f64]. *)
Local Notation max1 := Generic.max1.
Local Notation min1 := Generic.min1.
Local Notation maximum1 := Generic.maximum1.
Local Notation minimum1 := Generic.minimum1.

(** ** [max] and [min] of reals *)

Lemma Rmax_le_iff : forall r t s, Rmax r t <= s <-> r <= s /\ t <= s.
Proof.
intros r t s. unfold Rmax. destruct (Rle_dec r t); split; intros; lra.
Qed.

Lemma le_Rmax_iff : forall r t s, s <= Rmax r t <-> s <= r \/ s <= t.
Proof.
intros r t s. unfold Rmax. destruct (Rle_dec r t); split; intros; lra.
Qed.

Lemma Rmin_le_iff : forall r t s, Rmin r t <= s <-> r <= s \/ t <= s.
Proof.
intros r t s. unfold Rmin. destruct (Rle_dec r t); split; intros; lra.
Qed.

Lemma le_Rmin_iff : forall r t s, s <= Rmin r t <-> s <= r /\ s <= t.
Proof.
intros r t s. unfold Rmin. destruct (Rle_dec r t); split; intros; lra.
Qed.

(** Some [f r t] with [r] in [X] and [t] in [Y] has the property [P]
    exactly when some [r] has it and some [t] has it, if [P (f r t)] is
    [P r /\ P t]. *)
Lemma exists2_and :
  forall (X Y P : R -> Prop) (f : R -> R -> R),
  (forall r t, P (f r t) <-> P r /\ P t) ->
  (exists r t, X r /\ Y t /\ P (f r t)) <->
  (exists r, X r /\ P r) /\ (exists t, Y t /\ P t).
Proof.
intros X Y P f Hf. split.
- intros (r & t & Hr & Ht & H). apply Hf in H. destruct H as [H1 H2].
  split; [exists r | exists t]; split; assumption.
- intros [(r & Hr & H1) (t & Ht & H2)]. exists r, t.
  split; [exact Hr|]. split; [exact Ht|]. apply Hf. split; assumption.
Qed.

(** The same, with [P r \/ P t], if [X] and [Y] are nonempty. *)
Lemma exists2_or :
  forall (X Y P : R -> Prop) (f : R -> R -> R),
  (exists r, X r) -> (exists t, Y t) ->
  (forall r t, P (f r t) <-> P r \/ P t) ->
  (exists r t, X r /\ Y t /\ P (f r t)) <->
  (exists r, X r /\ P r) \/ (exists t, Y t /\ P t).
Proof.
intros X Y P f [r0 Hr0] [t0 Ht0] Hf. split.
- intros (r & t & Hr & Ht & H). apply Hf in H.
  destruct H as [H|H]; [left; exists r | right; exists t]; split; assumption.
- (* Pair the real that has [P] with any real of the other set. *)
  intros [(r & Hr & H)|(t & Ht & H)]; [exists r, t0 | exists r0, t];
    (split; [assumption|]); (split; [assumption|]); apply Hf;
    [left | right]; exact H.
Qed.

(** ** Bounds as option reals

    As in [in_bounds], [None] is -inf for a lower bound and +inf for an
    upper bound. *)

(** [s] is above the lower bound [lo], or below the upper bound [hi]. *)
Definition above (lo : option R) (s : R) : Prop :=
  match lo with Some a => a <= s | None => True end.
Definition below (hi : option R) (s : R) : Prop :=
  match hi with Some b => s <= b | None => True end.

Lemma in_bounds_iff :
  forall lo hi s, in_bounds lo hi s <-> above lo s /\ below hi s.
Proof.
intros lo hi s. exact (iff_refl _).
Qed.

Lemma in_bounds_ordered : forall lo hi s, in_bounds lo hi s -> ordered lo hi.
Proof.
intros [a|] [b|] s [H1 H2]; cbn in *; trivial; lra.
Qed.

(** [-o]: [None] stays [None], as -inf and +inf trade places. *)
Definition oopp (o : option R) : option R := option_map Ropp o.

(** [max] and [min] of upper bounds, where [None] is +inf. *)
Definition umax (o1 o2 : option R) : option R :=
  match o1, o2 with Some a, Some b => Some (Rmax a b) | _, _ => None end.
Definition umin (o1 o2 : option R) : option R :=
  match o1, o2 with
  | Some a, Some b => Some (Rmin a b)
  | Some a, None => Some a
  | None, _ => o2
  end.

Lemma below_oopp : forall o s, below (oopp o) (- s) <-> above o s.
Proof.
intros [a|] s; cbn [oopp option_map below above]; [split; intros; lra | tauto].
Qed.

Lemma below_umax :
  forall o1 o2 s, below (umax o1 o2) s <-> below o1 s \/ below o2 s.
Proof.
intros [a|] [b|] s; cbn [umax below]; [apply le_Rmax_iff | tauto | tauto | tauto].
Qed.

Lemma below_umin :
  forall o1 o2 s, below (umin o1 o2) s <-> below o1 s /\ below o2 s.
Proof.
intros [a|] [b|] s; cbn [umin below]; [apply le_Rmin_iff | tauto | tauto | tauto].
Qed.

(** Some real between [lo] and [hi] is at most [s] exactly when [s] is
    above [lo]. *)
Lemma above_points :
  forall lo hi s, ordered lo hi ->
  above lo s <-> exists r, in_bounds lo hi r /\ r <= s.
Proof.
intros lo hi s Hord. split.
- intros Hs. destruct lo as [a|].
  + exists a. split; [|exact Hs]. split; [apply Rle_refl|].
    destruct hi; [exact Hord | exact I].
  + (* A real below both [s] and [hi]. *)
    destruct hi as [b|].
    * exists (Rmin s b). split; [split; [exact I | apply Rmin_r] | apply Rmin_l].
    * exists s. split; [split; exact I | apply Rle_refl].
- intros (r & [Hr _] & Hs). destruct lo as [a|]; cbn [above] in *; [lra | exact I].
Qed.

(** Some real between [lo] and [hi] is at least [s] exactly when [s] is
    below [hi]. *)
Lemma below_points :
  forall lo hi s, ordered lo hi ->
  below hi s <-> exists r, in_bounds lo hi r /\ s <= r.
Proof.
intros lo hi s Hord. split.
- intros Hs. destruct hi as [b|].
  + exists b. split; [|exact Hs]. split; [|apply Rle_refl].
    destruct lo; [exact Hord | exact I].
  + (* A real above both [s] and [lo]. *)
    destruct lo as [a|].
    * exists (Rmax s a). split; [split; [apply Rmax_r | exact I] | apply Rmax_l].
    * exists s. split; [split; exact I | apply Rle_refl].
- intros (r & [_ Hr] & Hs). destruct hi as [b|]; cbn [below] in *; [lra | exact I].
Qed.

(** ** The lanes of an interval *)

(** Both lanes of a nonempty interval have the form of an upper bound:
    the first holds [-a], which is +inf when [a] is -inf. *)
Lemma upper_ok_lane : forall w, lower_ok (opp w) -> upper_ok w.
Proof.
intros w [Fw|Ew].
- left. rewrite is_finite_opp in Fw. exact Fw.
- right. rewrite <- (Bopp_involutive _ _ w). unfold opp in Ew. rewrite Ew.
  reflexivity.
Qed.

Lemma lower_ok_lane : forall w, upper_ok w -> lower_ok (opp w).
Proof.
intros w [Fw| ->]; [left | right; reflexivity].
rewrite is_finite_opp. exact Fw.
Qed.

Lemma not_nan_upper : forall w, upper_ok w -> is_nan w = false.
Proof.
intros w [Fw| ->]; [|reflexivity].
destruct w; first [reflexivity | discriminate Fw].
Qed.

(** The first lane holds [-a], so its bound is [-] that of [a]. *)
Lemma bound_lane : forall w, bound w = oopp (bound (opp w)).
Proof.
intros w. unfold bound. rewrite is_finite_opp, B2R_opp.
destruct (is_finite w); cbn [oopp option_map]; [|reflexivity].
rewrite Ropp_involutive. reflexivity.
Qed.

(** What the lanes of a nonempty interval [x] say: both have the form of
    an upper bound, [x] has a real, and its lanes tell which reals are at
    least, and at most, a real of [x]. *)
Lemma lanes_ok :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  upper_ok (fst (rep x)) /\ upper_ok (snd (rep x)) /\ (exists r, mem r x) /\
  (forall s, below (bound (fst (rep x))) (- s) <-> exists r, mem r x /\ r <= s) /\
  (forall s, below (bound (snd (rep x))) s <-> exists r, mem r x /\ s <= r).
Proof.
intros x Hx Hn. destruct (valid_nonempty x Hx Hn) as (Ha & Hb & Hord).
assert (HX : forall r, mem r x <->
               in_bounds (bound (opp (fst (rep x)))) (bound (snd (rep x))) r).
{ intros r. exact (mem_bounds x r Ha Hb). }
split; [exact (upper_ok_lane _ Ha)|]. split; [exact Hb|]. split; [|split].
- destruct (in_bounds_nonempty _ _ Hord) as (r & Hr). exists r. apply HX, Hr.
- intros s. rewrite bound_lane, below_oopp, (above_points _ _ s Hord).
  setoid_rewrite HX. reflexivity.
- intros s. rewrite (below_points _ _ s Hord). setoid_rewrite HX. reflexivity.
Qed.

(** ** [max1] and [min1] on lanes

    On floats of the form of an upper bound, [max1] and [min1] are [Rmax]
    and [Rmin] of the values, with +inf as the largest. *)

(** [and] of the bit patterns of two zeros is a zero, negative if both
    are, and [or] is a zero, negative if either is. *)
Lemma zero_bits :
  forall su sv,
  from_bits (Z.land (to_bits (B754_zero su)) (to_bits (B754_zero sv))) =
    B754_zero (su && sv) /\
  from_bits (Z.lor (to_bits (B754_zero su)) (to_bits (B754_zero sv))) =
    B754_zero (su || sv).
Proof.
intros [|] [|]; split; apply B2SF_inj; vm_compute; reflexivity.
Qed.

(** A finite float equal to [0.0] is a zero. *)
Lemma eq_zero_inv :
  forall u, is_finite u = true -> eq u zero = true -> u = B754_zero (Bsign u).
Proof.
intros u Fu Hu. unfold eq in Hu.
rewrite Beqb_correct in Hu by first [exact Fu | reflexivity].
revert Hu. case Req_bool_spec; [intros H _ | discriminate].
apply B2R_Bsign_inj; [exact Fu | reflexivity | exact H | reflexivity].
Qed.

Lemma max1_finite :
  forall u v, is_finite u = true -> is_finite v = true ->
  is_finite (max1 u v) = true /\ B2R (max1 u v) = Rmax (B2R u) (B2R v).
Proof.
intros u v Fu Fv. unfold max1.
rewrite (not_nan_upper u (or_introl Fu)), (not_nan_upper v (or_introl Fv)).
destruct (eq u zero && eq v zero) eqn:Z; cbv iota.
- (* Two zeros give a zero. *)
  destruct (andb_prop _ _ Z) as [Zu Zv].
  rewrite (eq_zero_inv u Fu Zu), (eq_zero_inv v Fv Zv), (proj1 (zero_bits _ _)).
  split; [reflexivity|]. cbn [B2R].
  rewrite Rmax_left; [reflexivity | apply Rle_refl].
- unfold gt. rewrite Bltb_correct by assumption.
  case Rlt_bool_spec; intros H; cbv iota; (split; [assumption|]).
  + rewrite Rmax_left by lra. reflexivity.
  + rewrite Rmax_right by lra. reflexivity.
Qed.

Lemma min1_finite :
  forall u v, is_finite u = true -> is_finite v = true ->
  is_finite (min1 u v) = true /\ B2R (min1 u v) = Rmin (B2R u) (B2R v).
Proof.
intros u v Fu Fv. unfold min1.
rewrite (not_nan_upper u (or_introl Fu)), (not_nan_upper v (or_introl Fv)).
destruct (eq u zero && eq v zero) eqn:Z; cbv iota.
- (* Two zeros give a zero. *)
  destruct (andb_prop _ _ Z) as [Zu Zv].
  rewrite (eq_zero_inv u Fu Zu), (eq_zero_inv v Fv Zv), (proj2 (zero_bits _ _)).
  split; [reflexivity|]. cbn [B2R].
  rewrite Rmin_left; [reflexivity | apply Rle_refl].
- unfold lt. rewrite Bltb_correct by assumption.
  case Rlt_bool_spec; intros H; cbv iota; (split; [assumption|]).
  + rewrite Rmin_left by lra. reflexivity.
  + rewrite Rmin_right by lra. reflexivity.
Qed.

(** +inf is the largest value. *)
Lemma max1_inf :
  forall w, upper_ok w ->
  max1 w (B754_infinity false) = B754_infinity false /\
  max1 (B754_infinity false) w = B754_infinity false.
Proof.
intros w [Fw| ->]; [destruct w as [[]|[]| |[] m e Hm]; try discriminate Fw|];
  split; reflexivity.
Qed.

Lemma min1_inf :
  forall w, upper_ok w ->
  min1 w (B754_infinity false) = w /\ min1 (B754_infinity false) w = w.
Proof.
intros w [Fw| ->]; [destruct w as [[]|[]| |[] m e Hm]; try discriminate Fw|];
  split; reflexivity.
Qed.

(** [max1] of upper bounds is [umax] of the bounds. *)
Lemma max1_bound :
  forall u v, upper_ok u -> upper_ok v ->
  upper_ok (max1 u v) /\ bound (max1 u v) = umax (bound u) (bound v).
Proof.
intros u v Hu Hv. destruct Hu as [Fu| ->]; [destruct Hv as [Fv| ->]|].
- destruct (max1_finite u v Fu Fv) as [F E].
  split; [left; exact F|].
  rewrite !bound_finite by assumption. rewrite E. reflexivity.
- rewrite (proj1 (max1_inf u (or_introl Fu))).
  split; [right; reflexivity|]. rewrite (bound_finite u Fu). reflexivity.
- rewrite (proj2 (max1_inf v Hv)). split; [right; reflexivity | reflexivity].
Qed.

(** [min1] of upper bounds is [umin] of the bounds. *)
Lemma min1_bound :
  forall u v, upper_ok u -> upper_ok v ->
  upper_ok (min1 u v) /\ bound (min1 u v) = umin (bound u) (bound v).
Proof.
intros u v Hu Hv. destruct Hu as [Fu| ->]; [destruct Hv as [Fv| ->]|].
- destruct (min1_finite u v Fu Fv) as [F E].
  split; [left; exact F|].
  rewrite !bound_finite by assumption. rewrite E. reflexivity.
- rewrite (proj1 (min1_inf u (or_introl Fu))).
  split; [left; exact Fu|]. rewrite (bound_finite u Fu). reflexivity.
- rewrite (proj2 (min1_inf v Hv)). split; [exact Hv | reflexivity].
Qed.

(** Neither lane is NaN, so [maximum1] and [minimum1] are [max1] and
    [min1]. *)
Lemma maximum1_minimum1 :
  forall u v, upper_ok u -> upper_ok v ->
  maximum1 u v = max1 u v /\ minimum1 u v = min1 u v.
Proof.
intros u v Hu Hv. unfold maximum1, minimum1.
rewrite (not_nan_upper u Hu), (not_nan_upper v Hv). split; reflexivity.
Qed.

(** ** The result *)

(** [Interval::max] and [Interval::min] with [HAS_MAXIMUM]. *)
Lemma max_rep :
  forall x y,
  rep (Interval.max x y) =
    (minimum1 (fst (rep x)) (fst (rep y)), maximum1 (snd (rep x)) (snd (rep y))).
Proof.
intros x y. reflexivity.
Qed.

Lemma min_rep :
  forall x y,
  rep (Interval.min x y) =
    (maximum1 (fst (rep x)) (fst (rep y)), minimum1 (snd (rep x)) (snd (rep y))).
Proof.
intros x y. reflexivity.
Qed.

(** If either argument is empty, both lanes of the result are NaN. *)
Lemma nan_rep :
  forall x y, valid x -> valid y ->
  is_nan (fst (rep x)) = true \/ is_nan (fst (rep y)) = true ->
  rep (Interval.max x y) = (B754_nan, B754_nan) /\
  rep (Interval.min x y) = (B754_nan, B754_nan).
Proof.
intros x y Hx Hy [Hn|Hn]; rewrite max_rep, min_rep.
- rewrite (empty_nan x Hx Hn). split; reflexivity.
- (* [maximum1] and [minimum1] give NaN whatever the lanes of [x]. *)
  rewrite (empty_nan y Hy Hn). destruct (rep x) as [x0 x1]. cbn [fst snd].
  destruct x0, x1; split; reflexivity.
Qed.

(** The empty interval is the hull of the image of an empty box. *)
Lemma hull_nan :
  forall f x y z, valid x -> valid y ->
  is_nan (fst (rep x)) = true \/ is_nan (fst (rep y)) = true ->
  rep z = (B754_nan, B754_nan) -> is_hull (image2 f x y) z.
Proof.
intros f x y [rz] Hx Hy Hn Ez. cbn [rep] in Ez. subst rz.
apply is_hull_empty. intros u (r & t & Hr & Ht & _).
destruct Hn as [Hn|Hn];
  [exact (mem_nan x r (empty_nan x Hx Hn) Hr) |
   exact (mem_nan y t (empty_nan y Hy Hn) Ht)].
Qed.

(** [z] is the hull of the image of [x × y] under [f] if its lanes have
    the form of upper bounds, and they tell which reals are at least, and
    at most, some [f r t] with [r] in [x] and [t] in [y]. *)
Lemma hull_lanes :
  forall f x y z,
  (exists r, mem r x) -> (exists t, mem t y) ->
  upper_ok (fst (rep z)) -> upper_ok (snd (rep z)) ->
  (forall s, below (bound (fst (rep z))) (- s) <->
     exists r t, mem r x /\ mem t y /\ f r t <= s) ->
  (forall s, below (bound (snd (rep z))) s <->
     exists r t, mem r x /\ mem t y /\ s <= f r t) ->
  is_hull (image2 f x y) z.
Proof.
intros f x y z [r0 Hr0] [t0 Ht0] Hz0 Hz1 Hlo Hhi.
assert (Ha := lower_ok_lane _ Hz0).
(* The lower bound of [z] is [-] its first lane. *)
assert (Lo : forall s, above (bound (opp (fst (rep z)))) s <->
               exists r t, mem r x /\ mem t y /\ f r t <= s).
{ intros s. rewrite <- below_oopp, <- bound_lane. exact (Hlo s). }
split.
- apply valid_bounds; [exact Ha | exact Hz1 |].
  (* [f r0 t0] is between the bounds. *)
  apply (in_bounds_ordered _ _ (f r0 t0)), in_bounds_iff.
  split; [apply Lo | apply Hhi]; exists r0, t0;
    (split; [exact Hr0 | split; [exact Ht0 | apply Rle_refl]]).
- intros s. rewrite (mem_bounds z s Ha Hz1), in_bounds_iff. split.
  + intros [H1 H2]. apply Lo in H1. apply Hhi in H2.
    destruct H1 as (r1 & t1 & Hr1 & Ht1 & H1),
      H2 as (r2 & t2 & Hr2 & Ht2 & H2).
    exists (f r1 t1), (f r2 t2).
    split; [exists r1, t1; split; [exact Hr1 | split; [exact Ht1 | reflexivity]]|].
    split; [exists r2, t2; split; [exact Hr2 | split; [exact Ht2 | reflexivity]]|].
    split; [exact H1 | exact H2].
  + intros (u & v & (r1 & t1 & Hr1 & Ht1 & ->) & (r2 & t2 & Hr2 & Ht2 & ->) & H1
              & H2).
    split; [apply Lo; exists r1, t1 | apply Hhi; exists r2, t2];
      (split; [assumption | split; assumption]).
Qed.

(** ** The theorems *)

(** [Interval::max] returns the tightest interval that contains the image
    of its arguments under [max]. *)
Theorem max_correct :
  forall x y, valid x -> valid y ->
  is_hull (image2 Rmax x y) (Interval.max x y).
Proof.
intros x y Hx Hy.
destruct (is_nan (fst (rep x)) || is_nan (fst (rep y))) eqn:Hn.
- apply Bool.orb_true_iff in Hn.
  exact (hull_nan Rmax x y _ Hx Hy Hn (proj1 (nan_rep x y Hx Hy Hn))).
- apply Bool.orb_false_iff in Hn. destruct Hn as [Hnx Hny].
  destruct (lanes_ok x Hx Hnx) as (Ux0 & Ux1 & Nx & Lx & Hx1).
  destruct (lanes_ok y Hy Hny) as (Uy0 & Uy1 & Ny & Ly & Hy1).
  destruct (min1_bound _ _ Ux0 Uy0) as (U0 & B0).
  destruct (max1_bound _ _ Ux1 Uy1) as (U1 & B1).
  assert (E : rep (Interval.max x y) =
                (min1 (fst (rep x)) (fst (rep y)),
                 max1 (snd (rep x)) (snd (rep y)))).
  { rewrite max_rep, (proj2 (maximum1_minimum1 _ _ Ux0 Uy0)),
      (proj1 (maximum1_minimum1 _ _ Ux1 Uy1)).
    reflexivity. }
  apply hull_lanes;
    [exact Nx | exact Ny | rewrite E; exact U0 | rewrite E; exact U1 | |].
  + (* [max(r, t) <= s] exactly when [r <= s] and [t <= s]. *)
    intros s. rewrite E. cbn [fst]. rewrite B0, below_umin, Lx, Ly. symmetry.
    exact (exists2_and (fun r => mem r x) (fun t => mem t y) (fun u => u <= s)
             Rmax (fun r t => Rmax_le_iff r t s)).
  + (* [s <= max(r, t)] exactly when [s <= r] or [s <= t]. *)
    intros s. rewrite E. cbn [snd]. rewrite B1, below_umax, Hx1, Hy1. symmetry.
    exact (exists2_or (fun r => mem r x) (fun t => mem t y) (fun u => s <= u)
             Rmax Nx Ny (fun r t => le_Rmax_iff r t s)).
Qed.

(** [Interval::min] does the same for [min]. *)
Theorem min_correct :
  forall x y, valid x -> valid y ->
  is_hull (image2 Rmin x y) (Interval.min x y).
Proof.
intros x y Hx Hy.
destruct (is_nan (fst (rep x)) || is_nan (fst (rep y))) eqn:Hn.
- apply Bool.orb_true_iff in Hn.
  exact (hull_nan Rmin x y _ Hx Hy Hn (proj2 (nan_rep x y Hx Hy Hn))).
- apply Bool.orb_false_iff in Hn. destruct Hn as [Hnx Hny].
  destruct (lanes_ok x Hx Hnx) as (Ux0 & Ux1 & Nx & Lx & Hx1).
  destruct (lanes_ok y Hy Hny) as (Uy0 & Uy1 & Ny & Ly & Hy1).
  destruct (max1_bound _ _ Ux0 Uy0) as (U0 & B0).
  destruct (min1_bound _ _ Ux1 Uy1) as (U1 & B1).
  assert (E : rep (Interval.min x y) =
                (max1 (fst (rep x)) (fst (rep y)),
                 min1 (snd (rep x)) (snd (rep y)))).
  { rewrite min_rep, (proj1 (maximum1_minimum1 _ _ Ux0 Uy0)),
      (proj2 (maximum1_minimum1 _ _ Ux1 Uy1)).
    reflexivity. }
  apply hull_lanes;
    [exact Nx | exact Ny | rewrite E; exact U0 | rewrite E; exact U1 | |].
  + (* [min(r, t) <= s] exactly when [r <= s] or [t <= s]. *)
    intros s. rewrite E. cbn [fst]. rewrite B0, below_umax, Lx, Ly. symmetry.
    exact (exists2_or (fun r => mem r x) (fun t => mem t y) (fun u => u <= s)
             Rmin Nx Ny (fun r t => Rmin_le_iff r t s)).
  + (* [s <= min(r, t)] exactly when [s <= r] and [s <= t]. *)
    intros s. rewrite E. cbn [snd]. rewrite B1, below_umin, Hx1, Hy1. symmetry.
    exact (exists2_and (fun r => mem r x) (fun t => mem t y) (fun u => s <= u)
             Rmin (fun r t => le_Rmin_iff r t s)).
Qed.
