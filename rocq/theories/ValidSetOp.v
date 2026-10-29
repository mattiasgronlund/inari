(** * [convex_hull] and [intersection] of [valid] intervals are [valid]

    An [Interval] stores [[a, b]] as [[-a; b]], and an empty one as
    [[NaN; NaN]]. If the first lane of an argument is NaN,
    [Interval::convex_hull] returns the other argument, which is [valid] by
    hypothesis, and [Interval::intersection] returns [Interval::EMPTY],
    which is [[NaN; NaN]] and so [valid].

    Otherwise both arguments are nonempty, and both lanes of each have the
    form of an upper bound, finite or +inf, as [-a] is +inf when [a] is
    -inf. On such floats, [max1] and [min1] are [Rmax] and [Rmin] of the
    values, with +inf as the largest value, and give a float of the same
    form ([max1_bound] and [min1_bound] in [MaxMin.v]). So both lanes of
    the result have that form too: its lower bound is finite or -inf and
    its upper bound is finite or +inf. What remains to show is that the
    lower bound is at most the upper one. An infinite bound, -inf below or
    +inf above, is ordered with any other, so only finite bounds need it.

    [convex_hull] of [[a, b]] and [[c, d]] takes [max1] of both lanes,
    [[max(-a, -c); max(b, d)]], which is [[-min(a, c); max(b, d)]], and
    [min(a, c) <= a <= b <= max(b, d)]. [intersection] takes [min1] of both
    lanes, [[min(-a, -c); min(b, d)]], which is [[-max(a, c); min(b, d)]],
    whose bounds need not be ordered. It returns [Interval::EMPTY] if the
    lower bound is above the upper one ([gt], i.e. [Bltb] of the upper
    bound and the lower one), and the interval of these lanes otherwise.
    Where both bounds are finite, [Bltb] is [<] of their values, so bounds
    that pass the test are ordered. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Integer MaxMin.

Open Scope R_scope.

(** The bound of [-w] is [-] that of [w]. *)
Lemma bound_opp_lane : forall w, bound (opp w) = oopp (bound w).
Proof.
intros w. rewrite (bound_lane (opp w)). unfold opp. rewrite Bopp_involutive.
reflexivity.
Qed.

Theorem convex_hull_valid :
  forall x y, valid x -> valid y -> valid (Interval.convex_hull x y).
Proof.
intros [[x0 x1]] [[y0 y1]] Hx Hy.
unfold Interval.convex_hull, Interval.is_empty. cbn [rep fst snd].
destruct (is_nan x0) eqn:Nx; [exact Hy|].
destruct (is_nan y0) eqn:Ny; [exact Hx|].
destruct (valid_nonempty _ Hx Nx) as (Lx & Ux & Ox).
destruct (valid_nonempty _ Hy Ny) as (Ly & Uy & Oy).
cbn [rep fst snd] in Lx, Ux, Ox, Ly, Uy, Oy.
apply upper_ok_lane in Lx, Ly.
destruct (max1_bound _ _ Lx Ly) as [U0 B0].
destruct (max1_bound _ _ Ux Uy) as [U1 B1].
apply valid_bounds; cbn [rep Generic.max fst snd].
- apply lower_ok_lane. exact U0.
- exact U1.
- rewrite bound_opp_lane, B0, B1.
  rewrite bound_opp_lane in Ox, Oy. revert Ox Oy.
  (* [-max(p, q) <= -p <= r <= max(r, s)], where [p] and [q] are the
     first lanes, [r] and [s] the second ones, and an infinite bound
     ([None]) is ordered with any other. *)
  destruct (bound x0) as [p|], (bound y0) as [q|], (bound x1) as [r|],
    (bound y1) as [s|]; cbn [oopp option_map umax ordered]; intros Ox Oy;
    try exact I.
  pose proof (Rmax_l p q). pose proof (Rmax_l r s). lra.
Qed.

Theorem intersection_valid :
  forall x y, valid x -> valid y -> valid (Interval.intersection x y).
Proof.
intros [[x0 x1]] [[y0 y1]] Hx Hy.
assert (VE : valid Interval.EMPTY) by (left; split; reflexivity).
unfold Interval.intersection, Interval.either_empty, Interval.is_empty.
cbn [rep fst snd].
destruct (is_nan x0) eqn:Nx; [exact VE|].
destruct (is_nan y0) eqn:Ny; [exact VE|].
destruct (valid_nonempty _ Hx Nx) as (Lx & Ux & _).
destruct (valid_nonempty _ Hy Ny) as (Ly & Uy & _).
cbn [rep fst snd] in Lx, Ux, Ly, Uy.
apply upper_ok_lane in Lx, Ly.
destruct (min1_bound _ _ Lx Ly) as [U0 _].
destruct (min1_bound _ _ Ux Uy) as [U1 _].
unfold Interval.inf_raw, Interval.sup_raw, Model.gt, Generic.min.
cbn [orb rep fst snd].
set (u := Generic.min1 x0 y0) in *. set (v := Generic.min1 x1 y1) in *.
destruct (Bltb v (opp u)) eqn:G; [exact VE|].
apply valid_bounds; cbn [rep fst snd].
- apply lower_ok_lane. exact U0.
- exact U1.
- (* An infinite bound ([None]) is ordered with any other. Where both are
     finite, [Bltb v (opp u) = false] says that [-u <= v]. *)
  unfold ordered, bound.
  destruct (is_finite (opp u)) eqn:Fu; [|exact I].
  destruct (is_finite v) eqn:Fv; [|exact I].
  rewrite Bltb_correct in G by assumption.
  revert G. case Rlt_bool_spec; [intros _ G; discriminate G | intros H _; exact H].
Qed.
