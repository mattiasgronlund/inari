(** * [Interval::atan2] and [DecInterval::atan2]

    [atan2_correct]: [Interval::atan2] returns the tightest interval that
    contains the image of the box [y × x] under IEEE 1788's [atan2],
    defined on [atan2_dom], where [y] is [self] and [x] is [rhs].
    [dec_atan2_correct]: its decorated version returns NaI for NaI, and
    otherwise the same interval with the strongest decoration
    ([strongest2_set]), lowered to those of the arguments. The decoration
    needs [com_common] for both arguments, as an unbounded argument can
    give a bounded result: the image of [[1, 2] × [1, +inf]] is in
    [(0, PI/2)]. Both assume what [Mpfr.v] says of MPFR.

    [Interval::atan2_impl] picks the result by the classes of [x] and [y].
    Each of the 49 pairs is a case of one lemma of [Atan2Const.v] (empty
    boxes and constant results), [Atan2Right.v], [Atan2Lower.v] and
    [Atan2Left.v] (bounds that [atan2_rd] and [atan2_ru] compute at
    corners), and its decoration a case of one of [Atan2Dec.v]
    ([at2_impl_dec]). *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Integer Abs Classify2 Classes
  DecBinary ComCommon AtanReal Dec2Set Atan2Dec Atan2Const Atan2Right Atan2Lower
  Atan2Left.

Open Scope R_scope.

Theorem atan2_correct :
  forall emin emax m y x,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  valid y -> valid x ->
  exists z, Interval.atan2 m y x = Some z /\
    is_tightest (image2_set atan2_dom Ratan2 y x) z.
Proof.
intros emin emax m y x Hr Hg Ho Hy Hx.
destruct (classify_defined x Hx) as (cx & Cx).
destruct (classify_defined y Hy) as (cy & Cy).
unfold Interval.atan2, Interval.atan2_impl. cbv zeta.
rewrite (classify2_pair x y cx cy Cx Cy).
(* Each of the 49 pairs, [x]'s class first in the order [E], [M], [N0],
   [N1], [P0], [P1], [Z], is a case of one lemma. *)
destruct cx, cy; cbv beta iota; eexists; (split; [reflexivity|]); cbn [fst].
(* E_E, E_M, E_N0, E_N1, E_P0, E_P1, E_Z *)
1-7: apply (at2_empty y x _ _ Hy Hx Cx Cy); left; reflexivity.
(* M_E, M_M, M_N0, M_N1, M_P0, M_P1, M_Z *)
- apply (at2_empty y x _ _ Hy Hx Cx Cy); right; left; reflexivity.
- apply (at2_full y x _ _ Hy Hx Cx Cy); left; reflexivity.
- apply (at2_full y x _ _ Hy Hx Cx Cy); [left | right]; reflexivity.
- apply (at2_mn1 emin emax m); assumption.
- apply at2_mp0; auto.
- apply (at2_mp1 emin emax m); assumption.
- apply at2_mp0; auto.
(* N0_E, N0_M, N0_N0, N0_N1, N0_P0, N0_P1, N0_Z *)
- apply (at2_empty y x _ _ Hy Hx Cx Cy); right; left; reflexivity.
- apply (at2_full y x _ _ Hy Hx Cx Cy); [right; left | left]; reflexivity.
- apply (at2_full y x _ _ Hy Hx Cx Cy); [right; left | right]; reflexivity.
- apply (at2_q3 emin emax m); auto.
- apply at2_n0p0; assumption.
- apply (at2_q2 emin emax m); auto.
- apply at2_pi; auto.
(* N1_E, N1_M, N1_N0, N1_N1, N1_P0, N1_P1, N1_Z *)
- apply (at2_empty y x _ _ Hy Hx Cx Cy); right; left; reflexivity.
- apply (at2_full y x _ _ Hy Hx Cx Cy); [right; right | left]; reflexivity.
- apply (at2_full y x _ _ Hy Hx Cx Cy); [right; right | right]; reflexivity.
- apply (at2_q3 emin emax m); auto.
- apply (at2_n1p0 emin emax m); assumption.
- apply (at2_q2 emin emax m); auto.
- apply at2_pi; auto.
(* P0_E, P0_M, P0_N0, P0_N1, P0_P0, P0_P1, P0_Z *)
- apply (at2_empty y x _ _ Hy Hx Cx Cy); right; left; reflexivity.
- apply at2_p0m; auto.
- apply at2_p0n0; assumption.
- apply (at2_q4 emin emax m y x _ _ Hr Hg Ho Hy Hx Cx Cy); left; split; reflexivity.
- apply at2_p0p0; assumption.
- apply (at2_q1 emin emax m y x _ _ Hr Hg Ho Hy Hx Cx Cy); left; split; reflexivity.
- apply at2_zero; assumption.
(* P1_E, P1_M, P1_N0, P1_N1, P1_P0, P1_P1, P1_Z *)
- apply (at2_empty y x _ _ Hy Hx Cx Cy); right; left; reflexivity.
- apply (at2_p1m emin emax m); assumption.
- apply (at2_q4 emin emax m y x _ _ Hr Hg Ho Hy Hx Cx Cy).
  right; left; split; [reflexivity | left; reflexivity].
- apply (at2_q4 emin emax m y x _ _ Hr Hg Ho Hy Hx Cx Cy).
  right; left; split; [reflexivity | right; reflexivity].
- apply (at2_q1 emin emax m y x _ _ Hr Hg Ho Hy Hx Cx Cy).
  right; left; split; [reflexivity | left; reflexivity].
- apply (at2_q1 emin emax m y x _ _ Hr Hg Ho Hy Hx Cx Cy).
  right; left; split; [reflexivity | right; left; reflexivity].
- apply (at2_q1 emin emax m y x _ _ Hr Hg Ho Hy Hx Cx Cy).
  right; left; split; [reflexivity | right; right; reflexivity].
(* Z_E, Z_M, Z_N0, Z_N1, Z_P0, Z_P1, Z_Z *)
- apply (at2_empty y x _ _ Hy Hx Cx Cy); right; left; reflexivity.
- apply at2_p0m; auto.
- apply at2_neg_half_pi; assumption.
- apply (at2_q4 emin emax m y x _ _ Hr Hg Ho Hy Hx Cx Cy); right; right; split; reflexivity.
- apply at2_half_pi; assumption.
- apply (at2_q1 emin emax m y x _ _ Hr Hg Ho Hy Hx Cx Cy); right; right; split; reflexivity.
- apply (at2_empty y x _ _ Hy Hx Cx Cy); right; right; split; reflexivity.
Qed.

(** The facts of [classify_mem] that the lemmas of [Atan2Dec.v] ask for:
    [0] is in an interval of class [N0], [P0] or [Z], and in one of class
    [M], between a real below 0 and one above; an interval of class [N1]
    or [P1] has a real, and one of class [M], [N0], [P0] or [Z] too; and a
    box with [y] of class [N1] or [P1], or [x] of class [P1], has no point
    with [y = 0] and [x <= 0]. *)
Ltac at2_zero_in M H :=
  first
    [ exact (proj1 (proj2 M))
    | exact (proj2 (M 0) eq_refl)
    | let u := fresh "u" in let v := fresh "v" in
      let Hu := fresh "Hu" in let Hv := fresh "Hv" in
      let Lu := fresh "Lu" in let Lv := fresh "Lv" in
      destruct M as ((u & Hu & Lu) & (v & Hv & Lv));
      exact (mem_between _ u v 0 H Hu Hv (conj (Rlt_le _ _ Lu) (Rlt_le _ _ Lv))) ].

Ltac at2_nonempty M :=
  first
    [ exact (proj2 M)
    | exists 0; exact (proj1 (proj2 M))
    | exists 0; exact (proj2 (M 0) eq_refl)
    | let u := fresh "u" in let Hu := fresh "Hu" in
      destruct (proj1 M) as (u & Hu & _); exists u; exact Hu ].

Ltac at2_avoid My Mx :=
  let r := fresh "r" in let t := fresh "t" in
  let Hr := fresh "Hr" in let Ht := fresh "Ht" in let E := fresh "E" in
  intros r t Hr Ht;
  first
    [ left; intros E; pose proof (proj1 My r Hr); lra
    | right; pose proof (proj1 Mx t Ht); lra ].

(** The decoration that [Interval::atan2_impl] returns is the one that
    [dec_holds] describes: [trv] for an empty box or one with [(0, 0)],
    [com] for one off the closed half-line [y = 0], [x <= 0], [dac] for
    [N1_P0] and [N1_Z], and [def] for [N1_M] and [N1_N0]. *)
Lemma at2_impl_dec :
  forall m y x, valid y -> valid x ->
  exists p, Interval.atan2_impl m y x = Some p /\
    dec_holds atan2_dom Ratan2 y x (fst p) (snd p).
Proof.
intros m y x Hy Hx.
destruct (classify_defined x Hx) as (cx & Cx).
destruct (classify_defined y Hy) as (cy & Cy).
pose proof (classify_mem x cx Hx Cx) as Mx.
pose proof (classify_mem y cy Hy Cy) as My.
unfold Interval.atan2_impl. cbv zeta.
rewrite (classify2_pair x y cx cy Cx Cy).
destruct cx, cy; cbv beta iota in Mx, My |- *; eexists; (split; [reflexivity|]);
  cbn [fst snd];
  lazymatch goal with
  | |- dec_holds _ _ _ _ _ Trv =>
      first
        [ apply ad_empty; first [left; exact My | right; exact Mx]
        | apply ad_trv; [at2_zero_in My Hy | at2_zero_in Mx Hx] ]
  | |- dec_holds _ _ _ _ _ Com =>
      apply ad_com; [at2_nonempty My | at2_nonempty Mx | at2_avoid My Mx]
  | |- dec_holds _ _ _ _ _ Dac =>
      apply ad_dac;
        [ at2_zero_in My Hy
        | first [exact (proj1 My) | intros ? Hr; pose proof (proj1 (My _) Hr); lra]
        | at2_nonempty Mx
        | exact (proj1 Mx) ]
  | |- dec_holds _ _ _ _ _ Def =>
      apply ad_def;
        [ at2_zero_in My Hy
        | first [exact (proj1 My) | exact (proj2 (proj2 My))]
        | at2_nonempty Mx
        | exact (proj1 Mx) ]
  end.
Qed.

Theorem dec_atan2_correct :
  forall emin emax m y x,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  valid (itv y) -> valid (itv x) -> com_common y -> com_common x ->
  exists w, DecInterval.atan2 m y x = Some w /\
    if DecInterval.is_nai y || DecInterval.is_nai x then w = DecInterval.NAI
    else
      is_tightest (image2_set atan2_dom Ratan2 (itv y) (itv x)) (itv w) /\
      exists d, strongest2_set atan2_dom d Ratan2 (itv y) (itv x) (itv w) /\
        dec w = dec_min d (dec_min (dec y) (dec x)).
Proof.
intros emin emax m y x Hr Hg Ho Hy Hx Cy Cx.
destruct (atan2_correct emin emax m (itv y) (itv x) Hr Hg Ho Hy Hx) as (z & Ez & Ht).
destruct (at2_impl_dec m (itv y) (itv x) Hy Hx) as (p & Ep & Hd).
(* [Interval::atan2] is the first component of [atan2_impl]. *)
assert (Hz : fst p = z).
{ unfold Interval.atan2 in Ez. rewrite Ep in Ez. injection Ez as E. exact E. }
subst z.
exists (DecInterval.set_dec (fst p) (dec_min (dec y) (dec_min (dec x) (snd p)))).
split; [unfold DecInterval.atan2; rewrite Ep; reflexivity|].
destruct (DecInterval.is_nai y || DecInterval.is_nai x) eqn:N.
- (* NaI has the decoration [ill], the least, so the minimum is [ill],
     and [set_dec] returns NaI for it. *)
  assert (Hm : dec_min (dec y) (dec_min (dec x) (snd p)) = Ill).
  { unfold DecInterval.is_nai in N. apply Bool.orb_true_iff in N.
    destruct (dec y), (dec x), (snd p); destruct N as [N|N];
      cbn in N; try discriminate N; reflexivity. }
  unfold DecInterval.set_dec. rewrite Hm. reflexivity.
- apply Bool.orb_false_iff in N. destruct N as [Ny Nx].
  assert (Dy : dec y <> Ill).
  { intros E. unfold DecInterval.is_nai in Ny. now rewrite E in Ny. }
  assert (Dx : dec x <> Ill).
  { intros E. unfold DecInterval.is_nai in Nx. now rewrite E in Nx. }
  apply (elem2_set_dec_strongest atan2_dom Ratan2 y x (fst p) (snd p) Hy Hx Dy Dx Ht).
  + (* The image is in [(-PI, PI]], so [fst p] is common if it is not
       empty. *)
    apply (tightest_common _ _ Ht). intros s (r & t & _ & _ & Hd' & ->).
    pose proof (Ratan2_range r t Hd'). pose proof PI_4. lra.
  + exact Hd.
  + (* A [com] argument is bounded, as it is common. *)
    intros _ Ey Ex.
    split; apply common_bounded; [exact (Cy Ey) | exact (Cx Ex)].
Qed.
