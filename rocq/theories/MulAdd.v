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

    [Rfma] is continuous on R³ ([Rfma_continuous]), so the decoration that
    [dec_holds3] describes is [com] for a nonempty box, and [trv] for an
    empty one, and [set_dec_correct3] in [DecTernary.v] gives the
    decorations, if a box of three [com] intervals is bounded when the
    result is common. As for [*], [[0, 0] × [1, +inf] × [1, 2]] has the
    bounded image [[1, 2]], so [dec_mul_add_correct] assumes [com_common]
    of [x] and [y], which [ComCommon.v] shows of every [DecInterval] that
    the library makes. It needs nothing of [z]: for [r] in [x] and [t] in
    [y], every [u] in [z] has [|u| <= |r * t + u| + |r * t|], so [z] is
    bounded if the image is ([fma_addend_bounded]). *)

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
assert (Hdx : dec x <> Ill) by (intros E; rewrite E in Nx; discriminate).
assert (Hdy : dec y <> Ill) by (intros E; rewrite E in Ny; discriminate).
assert (Hdz : dec z <> Ill) by (intros E; rewrite E in Nz; discriminate).
assert (He : dec_min (dec x) (dec_min (dec y) (dec z)) <> Ill).
{ apply dec_min_not_Ill; [exact Hdx|]. apply dec_min_not_Ill; assumption. }
destruct (mul_add_correct has_fma _ _ _ Hx Hy Hz) as (w & -> & Hw).
cbv beta iota.
exists (DecInterval.set_dec w (dec_min (dec x) (dec_min (dec y) (dec z)))).
split; [reflexivity|].
(* [set_dec_correct3] applies with the decoration [e] that [dec_holds3]
   describes: [trv] for an empty box, and otherwise [com], as [Rfma] is
   continuous. Either way, [set_dec] gets the same interval as with the
   minimum of the decorations of [x], [y] and [z]. *)
assert (Hdec :
  exists e, dec_holds3 Rfma (itv x) (itv y) (itv z) w e /\
    (e = Com -> dec x = Com -> dec y = Com -> dec z = Com ->
     Interval.is_common_interval w = true ->
     bounded (fun r => mem r (itv x)) /\ bounded (fun t => mem t (itv y)) /\
     bounded (fun u => mem u (itv z))) /\
    DecInterval.set_dec w (dec_min (dec x) (dec_min (dec y) (dec_min (dec z) e))) =
    DecInterval.set_dec w (dec_min (dec x) (dec_min (dec y) (dec z)))).
{ destruct (Interval.is_empty (itv x) || Interval.is_empty (itv y) ||
            Interval.is_empty (itv z)) eqn:Ee.
  - (* An empty box: [def] does not hold, and the image and so [w] are
       empty, which [set_dec] makes [EMPTY] for any decoration. *)
    assert (Hn : (forall r, ~ mem r (itv x)) \/ (forall t, ~ mem t (itv y)) \/
                 (forall u, ~ mem u (itv z))).
    { apply Bool.orb_true_iff in Ee. destruct Ee as [Exy|Ez].
      - apply Bool.orb_true_iff in Exy. destruct Exy as [Ex|Ey].
        + left. intros r. exact (mem_empty _ r Hx Ex).
        + right; left. intros t. exact (mem_empty _ t Hy Ey).
      - right; right. intros u. exact (mem_empty _ u Hz Ez). }
    assert (Ew : Interval.is_empty w = true).
    { apply (no_mem_empty w (proj1 Hw)).
      exact (tightest_no_mem _ w Hw (image3_empty Rfma _ _ _ Hn)). }
    exists Trv. split; [|split].
    + cbn [dec_holds3]. intros ((r & Hr) & (t & Ht) & (u & Hu)).
      destruct Hn as [Hn|[Hn|Hn]]; [exact (Hn r Hr) | exact (Hn t Ht) | exact (Hn u Hu)].
    + intros E. discriminate E.
    + rewrite (dec_min_Trv_r _ Hdz), (dec_min_Trv_r _ Hdy), (dec_min_Trv_r _ Hdx).
      rewrite (set_dec_empty_any w Trv Ew ltac:(discriminate)).
      rewrite (set_dec_empty_any w _ Ew He). reflexivity.
  - (* A nonempty box: [dac] holds and [Rfma] is continuous, so the
       decoration is [com]. The minimum is [com] only if all three
       decorations are, and then [x] and [y] are common, so bounded, and
       [z] is bounded as the image, which is in the common [w], is. *)
    apply Bool.orb_false_iff in Ee. destruct Ee as [Exy Ez].
    apply Bool.orb_false_iff in Exy. destruct Exy as [Ex Ey].
    pose proof (nonempty_mem _ Hx Ex) as Mx.
    pose proof (nonempty_mem _ Hy Ey) as My.
    pose proof (nonempty_mem _ Hz Ez) as Mz.
    exists Com. split; [|split].
    + cbn [dec_holds3].
      split; [exact (p3_Dac_continuous Rfma Rfma_continuous _ _ _ w Mx My Mz)|].
      intros r t u _ _ _. exact (Rfma_continuous r t u).
    + intros _ Cx Cy _ Cw.
      split; [apply common_bounded, Hcx; exact Cx|].
      split; [apply common_bounded, Hcy; exact Cy|].
      apply (fma_addend_bounded _ _ _ Mx My).
      destruct (common_bounded w Cw) as (m & Hm).
      exists m. intros s Hs. exact (Hm s (proj1 (proj2 Hw) s Hs)).
    + rewrite (dec_min_Com_r (dec z)). reflexivity. }
destruct Hdec as (e & Hh & Hb & E).
pose proof (set_dec_correct3 Rfma x y z w e Hx Hy Hz Hdx Hdy Hdz Hw Hh Hb) as H.
cbv zeta in H. rewrite E in H. exact H.
Qed.
