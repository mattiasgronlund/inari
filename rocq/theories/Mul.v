(** * [x * y] of intervals is tightest and decorated correctly

    [x * y] of [Interval]s returns the tightest interval that contains the
    image of the box [x × y] under [*], for either value of [has_fma], and
    [x * y] of [DecInterval]s decorates it with the minimum of the
    strongest decoration that holds and the decorations of [x] and [y], as
    IEEE 1788 asks of a tightest interval version of a function, if each of
    [x] and [y] is [com] only when its interval is common.

    [Interval::mul] dispatches on the pair of the classes of its arguments
    ([classify2_pair] in [Classify2.v]), and [Interval::classify] is
    defined on every valid interval ([classify_defined] in [Abs.v]). So
    [mul_correct] goes through the 49 pairs of classes, and a lemma in
    another file proves each:
    - [mul_empty] in [MulZero.v]: the 13 pairs with [E] on either side,
      which give the empty interval;
    - [mul_zero] in [MulZero.v]: the 11 pairs with [Z] on one side and not
      [E] on the other, which give [[0, 0]];
    - [mul_MM] in [MulMM.v]: [M × M], where each lane of the result is
      [max1] of two products rounded up;
    - [mul_MN], [mul_MP], [mul_NM] and [mul_PM] in [MulMRow.v]: the 8 pairs
      with [M] on one side and [N0], [N1], [P0] or [P1] on the other;
    - [mul_NN], [mul_NP], [mul_PN] and [mul_PP] in [MulNP.v]: the 16 pairs
      with [N0], [N1], [P0] or [P1] on both sides.
    That is each pair once: 13 + 11 + 1 + 8 + 16 = 49. The lemmas of
    [MulMRow.v] and [MulNP.v] take [N0] or [N1] as one hypothesis, as both
    take the same branch of [Interval::mul], and likewise [P0] or [P1].

    [DecInterval::mul] returns NaI if either argument is NaI, and otherwise
    calls [set_dec] with the result of [Interval::mul] and the minimum of
    the decorations, as [DecInterval::add] does. [set_dec_correct] in
    [DecBinary.v] shows that this decorates the result as IEEE 1788 asks,
    for a function that is continuous at each point of R², which [*] is
    ([Rmult_continuous]). It also needs the minimum of the decorations to
    be [com] only if a nonempty box whose image is bounded is bounded.
    That holds for [+] and [-], but not for [*]: the image of
    [[0, 0] × [1, +inf]] is [{0}], which is bounded, but the box is not.
    The strongest decoration there is [dac], as [com] asks for a bounded
    box, but if both arguments were [com], [set_dec] would keep [com] for
    the common result [[0, 0]]. So, as [dec_max_correct] in [DecMaxMin.v]
    does, [dec_mul_correct] takes as hypotheses that each argument is [com]
    only if its interval is common, and so bounded ([common_bounded] in
    [DecBinary.v]). The minimum is [com] only if both decorations are, and
    then the box is bounded. *)

From Stdlib Require Import Reals Lra.
From Inari Require Import Model Ieee1788 DecBinary Abs MulMM MulMRow MulNP
  MulZero.

Open Scope R_scope.

(** ** [Interval::mul] *)

(** [x * y] of [Interval]s returns the tightest interval that contains the
    image of [x × y] under [*]. *)
Theorem mul_correct :
  forall has_fma x y, valid x -> valid y ->
  exists z, Interval.mul has_fma x y = Some z /\ is_tightest (image2 Rmult x y) z.
Proof.
intros has_fma x y Hx Hy.
destruct (classify_defined x Hx) as (cx & Cx).
destruct (classify_defined y Hy) as (cy & Cy).
(* Each of the 49 pairs is a case of exactly one lemma. [auto] proves the
   class hypotheses, picking the side of a disjunction such as
   [Interval.classify y = Some CN0 \/ Interval.classify y = Some CN1], and
   [discriminate] proves that a class other than [E] is not [E]. *)
destruct cx, cy;
  first
    [ solve [apply (mul_empty has_fma x y _ _ Hx Hy Cx Cy); auto]
    | solve [apply (mul_zero has_fma x y _ _ Hx Hy Cx Cy);
             solve [left; split; [reflexivity | discriminate]
                   | right; split; [reflexivity | discriminate]]]
    | solve [apply mul_MM; auto]
    | solve [apply mul_MN; auto]
    | solve [apply mul_MP; auto]
    | solve [apply mul_NM; auto]
    | solve [apply mul_PM; auto]
    | solve [apply mul_NN; auto]
    | solve [apply mul_NP; auto]
    | solve [apply mul_PN; auto]
    | solve [apply mul_PP; auto] ].
Qed.

(** ** [DecInterval::mul] *)

(** [*] is continuous at each point [(r, t)] of R², as
    [r' * t' - r * t = (r' - r) * (t' - t) + r * (t' - t) + t * (r' - r)].
    If [r'] and [t'] are within [delta] of [r] and [t], its absolute value
    is below [delta * delta + (|r| + |t|) * delta], which is at most
    [delta * (|r| + |t| + 1)] for [delta <= 1], and at most [eps] for
    [delta <= eps / (|r| + |t| + 1)]. *)
Lemma Rmult_continuous : forall r t, continuity2_pt Rmult r t.
Proof.
intros r t eps Heps.
pose proof (Rabs_pos r) as Pr. pose proof (Rabs_pos t) as Pt.
set (k := Rabs r + Rabs t + 1).
assert (Hk : 0 < k) by (unfold k; lra).
assert (D0 : 0 < Rmin 1 (eps / k)).
{ apply Rmin_pos; [lra | apply Rdiv_lt_0_compat; assumption]. }
exists (Rmin 1 (eps / k)). split; [exact D0|].
intros r' t' _ _ Hr Ht.
set (delta := Rmin 1 (eps / k)) in *.
assert (D1 : delta <= 1) by apply Rmin_l.
(* [delta <= eps / k], so [delta * k <= eps]. *)
assert (D2 : delta * k <= eps).
{ apply (Rmult_le_reg_r (/ k)); [apply Rinv_0_lt_compat, Hk|].
  rewrite Rmult_assoc, Rinv_r by lra. rewrite Rmult_1_r. apply Rmin_r. }
unfold k in D2.
replace (r' * t' - r * t)
  with ((r' - r) * (t' - t) + r * (t' - t) + t * (r' - r)) by ring.
pose proof (Rabs_triang ((r' - r) * (t' - t) + r * (t' - t)) (t * (r' - r))) as T1.
pose proof (Rabs_triang ((r' - r) * (t' - t)) (r * (t' - t))) as T2.
rewrite Rabs_mult in T1. rewrite 2!Rabs_mult in T2.
pose proof (Rabs_pos (r' - r)) as Pa. pose proof (Rabs_pos (t' - t)) as Pb.
(* Each term is bounded by its factors' bounds. *)
assert (B1 : Rabs (r' - r) * Rabs (t' - t) <= Rabs (r' - r) * delta)
  by (apply Rmult_le_compat_l; lra).
assert (B2 : Rabs (r' - r) * delta < delta * delta)
  by (apply Rmult_lt_compat_r; [exact D0 | exact Hr]).
assert (B3 : Rabs r * Rabs (t' - t) <= Rabs r * delta)
  by (apply Rmult_le_compat_l; lra).
assert (B4 : Rabs t * Rabs (r' - r) <= Rabs t * delta)
  by (apply Rmult_le_compat_l; lra).
(* [delta <= 1], so [delta * delta <= delta]. *)
assert (B5 : delta * delta <= delta * 1) by (apply Rmult_le_compat_l; lra).
lra.
Qed.

(** [x * y] of [DecInterval]s returns NaI if either argument is NaI, and
    otherwise the tightest interval, decorated with the decoration that
    IEEE 1788 asks for, if each argument is [com] only when its interval is
    common. *)
Theorem dec_mul_correct :
  forall has_fma x y, valid (itv x) -> valid (itv y) ->
  (dec x = Com -> Interval.is_common_interval (itv x) = true) ->
  (dec y = Com -> Interval.is_common_interval (itv y) = true) ->
  exists z, DecInterval.mul has_fma x y = Some z /\
    if DecInterval.is_nai x || DecInterval.is_nai y then z = DecInterval.NAI
    else
      is_tightest (image2 Rmult (itv x) (itv y)) (itv z) /\
      exists d, strongest2 d Rmult (itv x) (itv y) (itv z) /\
        dec z = dec_min d (dec_min (dec x) (dec y)).
Proof.
intros has_fma x y Hx Hy Hcx Hcy. unfold DecInterval.mul.
destruct (DecInterval.is_nai x || DecInterval.is_nai y) eqn:N;
  [exists DecInterval.NAI; split; reflexivity|].
apply Bool.orb_false_iff in N. destruct N as [Nx Ny].
unfold DecInterval.is_nai in Nx, Ny.
assert (He : dec_min (dec x) (dec y) <> Ill).
{ apply dec_min_not_Ill; intros E; [rewrite E in Nx | rewrite E in Ny];
    discriminate. }
destruct (mul_correct has_fma _ _ Hx Hy) as (z & -> & Hz). cbv beta iota.
exists (DecInterval.set_dec z (dec_min (dec x) (dec y))). split; [reflexivity|].
(* The minimum is [com] only if both decorations are, and then both
   intervals are common, so bounded. *)
assert (Hc : dec_min (dec x) (dec y) = Com ->
             (exists r, mem r (itv x)) -> (exists t, mem t (itv y)) ->
             bounded (image2 Rmult (itv x) (itv y)) ->
             bounded (fun r => mem r (itv x)) /\
             bounded (fun t => mem t (itv y))).
{ intros E _ _ _. apply dec_min_Com in E. destruct E as [Ex Ey].
  split; apply common_bounded; [now apply Hcx | now apply Hcy]. }
destruct (set_dec_correct Rmult Rmult_continuous _ _ z _ Hx Hy He Hz Hc)
  as (E & d & Hd & Ed).
rewrite E. split; [exact Hz|]. exists d. split; [exact Hd | exact Ed].
Qed.
