(** * [mul_add] of intervals is tightest and decorated correctly

    [x.mul_add(y, z)] of [Interval]s returns the tightest interval that
    contains the image of the box [x × y × z] under [Rfma], [r * t + u],
    for either value of [has_fma], and [x.mul_add(y, z)] of [DecInterval]s
    decorates it with the minimum of the strongest decoration that holds
    and the decorations of [x], [y] and [z], as IEEE 1788 asks of a
    tightest interval version of a function, if each of [x] and [y] is
    [com] only when its interval is common.

    [Interval::mul_add] returns the empty interval for an empty [z]
    ([mul_add_addend_empty] in [MulAddZero.v]), and otherwise dispatches
    on the pair of the classes of [x] and [y] as [Interval::mul] does
    ([Mul.v]), with a lemma for each group of pairs: [mul_add_empty] and
    [mul_add_zero] in [MulAddZero.v], [mul_add_MM] in [MulAddMM.v],
    [mul_add_MN], [mul_add_MP], [mul_add_NM] and [mul_add_PM] in
    [MulAddMRow.v], and [mul_add_NN], [mul_add_NP], [mul_add_PN] and
    [mul_add_PP] in [MulAddNP.v].

    [Rfma] is continuous on R³ ([Rfma_continuous]), so
    [set_dec_correct3] in [DecTernary.v] gives the decorations, if [e] is
    [com] only when a nonempty box with a bounded image is bounded. As for
    [*], [[0, 0] × [1, +inf] × [1, 2]] has the bounded image [[1, 2]], so
    [dec_mul_add_correct] assumes [com_common] of [x] and [y], which
    [ComCommon.v] shows of every [DecInterval] that the library makes. It
    needs nothing of [z]: for [r] in [x] and [t] in [y], every [u] in [z]
    has [|u| <= |r * t + u| + |r * t|], so [z] is bounded if the image is
    ([fma_addend_bounded]). *)

From Stdlib Require Import Reals Lra.
From Inari Require Import Model Ieee1788 ComCommon DecBinary DecTernary Abs Mul
  MulAddZero MulAddMM MulAddMRow MulAddNP.

Open Scope R_scope.

(** ** [Interval::mul_add] *)

(** [x.mul_add(y, z)] of [Interval]s returns the tightest interval that
    contains the image of [x × y × z] under [Rfma]. *)
Theorem mul_add_correct :
  forall has_fma x y z, valid x -> valid y -> valid z ->
  exists w, Interval.mul_add has_fma x y z = Some w /\ is_tightest (image3 Rfma x y z) w.
Proof.
intros has_fma x y z Hx Hy Hz.
(* An empty [z] gives [EMPTY] before [x] and [y] are classified. *)
destruct (Interval.is_empty z) eqn:Ez;
  [exact (mul_add_addend_empty has_fma x y z Hz Ez)|].
destruct (classify_defined x Hx) as (cx & Cx).
destruct (classify_defined y Hy) as (cy & Cy).
(* Each of the 49 pairs is a case of exactly one lemma, as in [mul_correct]
   in [Mul.v]. [auto] proves the class hypotheses, picking the side of a
   disjunction such as
   [Interval.classify y = Some CN0 \/ Interval.classify y = Some CN1], and
   [discriminate] proves that a class other than [E] is not [E]. *)
destruct cx, cy;
  first
    [ solve [apply (mul_add_empty has_fma x y z _ _ Hx Hy Ez Cx Cy); auto]
    | solve [apply (mul_add_zero has_fma x y z _ _ Hx Hy Hz Ez Cx Cy);
             solve [left; split; [reflexivity | discriminate]
                   | right; split; [reflexivity | discriminate]]]
    | solve [apply mul_add_MM; auto]
    | solve [apply mul_add_MN; auto]
    | solve [apply mul_add_MP; auto]
    | solve [apply mul_add_NM; auto]
    | solve [apply mul_add_PM; auto]
    | solve [apply mul_add_NN; auto]
    | solve [apply mul_add_NP; auto]
    | solve [apply mul_add_PN; auto]
    | solve [apply mul_add_PP; auto] ].
Qed.

(** ** [DecInterval::mul_add] *)

(** [Rfma] is continuous at each point of R³, as [*] is
    ([Rmult_continuous] in [Mul.v]) and [+] is. *)
Lemma Rfma_continuous : forall r t u, continuity3_pt Rfma r t u.
Proof.
intros r t u eps Heps.
assert (He2 : 0 < eps / 2) by lra.
(* [r' * t'] is within [eps / 2] of [r * t] for [r'] and [t'] within [d]
   of [r] and [t]. *)
destruct (Rmult_continuous r t (eps / 2) He2) as (d & Hd & H).
exists (Rmin d (eps / 2)). split; [now apply Rmin_pos|].
intros r' t' u' _ _ _ Hr Ht Hu.
pose proof (Rmin_l d (eps / 2)) as M1. pose proof (Rmin_r d (eps / 2)) as M2.
assert (Hr' : Rabs (r' - r) < d) by lra.
assert (Ht' : Rabs (t' - t) < d) by lra.
pose proof (H r' t' I I Hr' Ht') as Hm.
(* [r' * t' + u' - (r * t + u) = (r' * t' - r * t) + (u' - u)], and
   [|u' - u| < eps / 2]. *)
unfold Rfma.
replace (r' * t' + u' - (r * t + u)) with ((r' * t' - r * t) + (u' - u))
  by ring.
pose proof (Rabs_triang (r' * t' - r * t) (u' - u)) as T.
lra.
Qed.

(** If [x] and [y] are nonempty and the image of [x × y × z] under [Rfma]
    is bounded, so is [z]. *)
Lemma fma_addend_bounded :
  forall x y z, (exists r, mem r x) -> (exists t, mem t y) ->
  bounded (image3 Rfma x y z) -> bounded (fun u => mem u z).
Proof.
intros x y z (r & Hr) (t & Ht) (m & Hm).
(* With [r] and [t] fixed, [|u| <= |r * t + u| + |r * t|], and
   [r * t + u] is in the image. *)
exists (m + Rabs (r * t)). intros u Hu.
pose proof (Hm (Rfma r t u) (image3_mem Rfma x y z r t u Hr Ht Hu)) as H.
unfold Rfma in H.
pose proof (Rabs_triang (r * t + u) (- (r * t))) as T.
rewrite Rabs_Ropp in T.
replace (r * t + u + - (r * t)) with u in T by ring.
lra.
Qed.

(** [x.mul_add(y, z)] of [DecInterval]s returns NaI if an argument is NaI,
    and otherwise the tightest interval, decorated with the decoration that
    IEEE 1788 asks for, if each of [x] and [y] is [com] only when its
    interval is common. *)
Theorem dec_mul_add_correct :
  forall has_fma x y z, valid (itv x) -> valid (itv y) -> valid (itv z) ->
  com_common x ->
  com_common y ->
  exists w, DecInterval.mul_add has_fma x y z = Some w /\
    if DecInterval.is_nai x || DecInterval.is_nai y || DecInterval.is_nai z
    then w = DecInterval.NAI
    else
      is_tightest (image3 Rfma (itv x) (itv y) (itv z)) (itv w) /\
      exists d, strongest3 d Rfma (itv x) (itv y) (itv z) (itv w) /\
        dec w = dec_min d (dec_min (dec x) (dec_min (dec y) (dec z))).
Proof.
intros has_fma x y z Hx Hy Hz Hcx Hcy. unfold DecInterval.mul_add.
destruct (DecInterval.is_nai x || DecInterval.is_nai y || DecInterval.is_nai z)
  eqn:N; [exists DecInterval.NAI; split; reflexivity|].
apply Bool.orb_false_iff in N. destruct N as [Nxy Nz].
apply Bool.orb_false_iff in Nxy. destruct Nxy as [Nx Ny].
unfold DecInterval.is_nai in Nx, Ny, Nz.
assert (He : dec_min (dec x) (dec_min (dec y) (dec z)) <> Ill).
{ apply dec_min_not_Ill; [|apply dec_min_not_Ill]; intros E;
    [rewrite E in Nx | rewrite E in Ny | rewrite E in Nz]; discriminate. }
destruct (mul_add_correct has_fma _ _ _ Hx Hy Hz) as (w & -> & Hw).
cbv beta iota.
exists (DecInterval.set_dec w (dec_min (dec x) (dec_min (dec y) (dec z)))).
split; [reflexivity|].
(* The minimum is [com] only if all three decorations are, and then [x]
   and [y] are common, so bounded, and [z] is bounded as the image is. *)
assert (Hc : dec_min (dec x) (dec_min (dec y) (dec z)) = Com ->
             (exists r, mem r (itv x)) -> (exists t, mem t (itv y)) ->
             (exists u, mem u (itv z)) ->
             bounded (image3 Rfma (itv x) (itv y) (itv z)) ->
             bounded (fun r => mem r (itv x)) /\
             bounded (fun t => mem t (itv y)) /\
             bounded (fun u => mem u (itv z))).
{ intros E Ex Ey _ B. apply dec_min_Com in E. destruct E as [Cx E].
  apply dec_min_Com in E. destruct E as [Cy _].
  split; [apply common_bounded, Hcx; exact Cx|].
  split; [apply common_bounded, Hcy; exact Cy|].
  exact (fma_addend_bounded _ _ _ Ex Ey B). }
destruct (set_dec_correct3 Rfma Rfma_continuous _ _ _ w _ Hx Hy Hz He Hw Hc)
  as (E & d & Hd & Ed).
rewrite E. split; [exact Hw|]. exists d. split; [exact Hd | exact Ed].
Qed.
