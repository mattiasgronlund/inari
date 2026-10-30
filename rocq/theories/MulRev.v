(** * Two-output division of intervals and decorated intervals

    [Interval::mul_rev_to_pair] returns what [two_output] in [Ieee1788.v]
    asks for the set [mul_rev x y] of reals [z] with [t * z] in [y] for
    some [t] in [x], for [x] [self] and [y] [numerator]. The proof splits
    on the classes of [x] and [y]: [mul_rev_empty], [mul_rev_entire] and
    [mul_rev_nz] in [MulRevCases.v], and [mul_rev_N1M] and [mul_rev_P1M] in
    [MulRevTwo.v].

    [DecInterval::mul_rev_to_pair] returns [[NAI, NAI]] if an argument is
    NaI. Otherwise its intervals are those of [Interval::mul_rev_to_pair],
    the second is decorated [trv], and the first is [numerator / self] if
    [x] and [y] are nonempty and 0 is not in [x], and is decorated [trv]
    otherwise. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer Sign MaxMin DecBinary AddSub
  Classify2 Classes Abs DivZero Div MulRevSets MulRevTwo MulRevCases.

Open Scope R_scope.

(** ** [Interval::mul_rev_to_pair] *)

(** The cases of [MulRevCases.v] in the form of [mul_rev_to_pair_correct].
    With every real in the set, the set is convex and has no bound. *)
Lemma mul_rev_empty_two :
  forall has_fma x y cx cy, valid x -> valid y ->
  Interval.classify x = Some cx -> Interval.classify y = Some cy ->
  (cx = CE \/ cy = CE \/ (cx = CZ /\ (cy = CN1 \/ cy = CP1))) ->
  exists u v, Interval.mul_rev_to_pair has_fma x y = Some (u, v) /\
    two_output (mul_rev x y) u v.
Proof.
intros has_fma x y cx cy Hx Hy Cx Cy H.
destruct (mul_rev_empty has_fma x y cx cy Hx Hy Cx Cy H) as (E & Hs).
exists Interval.EMPTY, Interval.EMPTY.
split; [exact E | exact (two_output_empty _ Hs)].
Qed.

Lemma mul_rev_entire_two :
  forall has_fma x y cx cy, valid x -> valid y ->
  Interval.classify x = Some cx -> Interval.classify y = Some cy ->
  (cx = CM \/ cx = CN0 \/ cx = CP0 \/ cx = CZ) ->
  (cy = CM \/ cy = CN0 \/ cy = CP0 \/ cy = CZ) ->
  exists u v, Interval.mul_rev_to_pair has_fma x y = Some (u, v) /\
    two_output (mul_rev x y) u v.
Proof.
intros has_fma x y cx cy Hx Hy Cx Cy H1 H2.
destruct (mul_rev_entire has_fma x y cx cy Hx Hy Cx Cy H1 H2) as (E & Hs).
exists Interval.ENTIRE, Interval.EMPTY. split; [exact E|].
apply two_output_one.
- exists 0. apply Hs.
- intros u v r _ _ _. apply Hs.
- apply tightest_entire; intros m; exists m; (split; [apply Hs | lra]).
Qed.

Lemma mul_rev_nz_two :
  forall has_fma x y cx cy, valid x -> valid y ->
  Interval.classify x = Some cx -> Interval.classify y = Some cy ->
  ((cx = CN1 \/ cx = CP1) /\ cy <> CE) \/
  ((cx = CN0 \/ cx = CP0) /\ (cy = CN1 \/ cy = CP1)) ->
  exists u v, Interval.mul_rev_to_pair has_fma x y = Some (u, v) /\
    two_output (mul_rev x y) u v.
Proof.
intros has_fma x y cx cy Hx Hy Cx Cy H.
destruct (mul_rev_nz has_fma x y cx cy Hx Hy Cx Cy H) as (u & E & Ht).
exists u, Interval.EMPTY. split; [exact E | exact Ht].
Qed.

Theorem mul_rev_to_pair_correct :
  forall has_fma x y, valid x -> valid y ->
  exists u v, Interval.mul_rev_to_pair has_fma x y = Some (u, v) /\
    two_output (mul_rev x y) u v.
Proof.
intros has_fma x y Hx Hy.
destruct (classify_defined x Hx) as (cx & Cx).
destruct (classify_defined y Hy) as (cy & Cy).
(* Each of the 49 pairs is a case of exactly one lemma: 15 with an empty
   set, 16 with every real, 16 with [y / x] and the two with two
   components. [auto] proves the class hypotheses, picking the side of a
   disjunction, and [discriminate] proves that two different classes
   differ. *)
destruct cx, cy;
  first
    [ solve [apply (mul_rev_empty_two has_fma x y _ _ Hx Hy Cx Cy); auto 6]
    | solve [apply (mul_rev_entire_two has_fma x y _ _ Hx Hy Cx Cy); auto]
    | solve [apply (mul_rev_nz_two has_fma x y _ _ Hx Hy Cx Cy);
             solve [left; split; [auto | discriminate] | right; split; auto]]
    | exact (mul_rev_N1M has_fma x y Hx Hy Cx Cy)
    | exact (mul_rev_P1M has_fma x y Hx Hy Cx Cy) ].
Qed.

(** ** [DecInterval::mul_rev_to_pair] *)

(** [d.min(e)] does not depend on the order of [d] and [e], as the
    discriminant tells the decorations apart. *)
Lemma dec_min_comm : forall d e, dec_min d e = dec_min e d.
Proof.
intros [] []; reflexivity.
Qed.

(** The outputs of [two_output] are valid: each is [EMPTY] or the tightest
    interval of a set. *)
Lemma two_output_valid :
  forall s u v, two_output s u v -> valid u /\ valid v.
Proof.
assert (VE : valid Interval.EMPTY) by (left; split; reflexivity).
intros s u v
  [(_ & -> & ->) | [(k & _ & _ & Hu & ->) | (k1 & k2 & _ & _ & _ & _ & Hu & Hv)]];
  split; first [exact VE | exact (proj1 Hu) | exact (proj1 Hv)].
Qed.

(** For an empty set, the first output of [two_output] is [EMPTY], as each
    of the other two forms has a component, which has an element. *)
Lemma two_output_empty_fst :
  forall s u v, two_output s u v -> (forall r, ~ s r) -> u = Interval.EMPTY.
Proof.
intros s u v
  [(_ & Eu & _) | [(k & Hk & _) | (k & _ & Hk & _)]] Hs; [exact Eu | |];
  destruct Hk as ((r & Hr) & _ & Hks & _); destruct (Hs r (Hks r Hr)).
Qed.

(** [set_dec] keeps a valid interval if the decoration is not [ill], as an
    empty valid interval is [EMPTY]. *)
Lemma itv_set_dec :
  forall w e, valid w -> e <> Ill -> itv (DecInterval.set_dec w e) = w.
Proof.
intros w e Hw He. unfold DecInterval.set_dec.
destruct (dec_eqb e Ill) eqn:E; [destruct e; [now elim He | discriminate E ..]|].
destruct (Interval.is_empty w) eqn:Ew; [exact (eq_sym (valid_empty_eq w Hw Ew))|].
destruct (dec_eqb e Com && negb (Interval.is_common_interval w)); reflexivity.
Qed.

Lemma dec_set_dec_Trv : forall w, dec (DecInterval.set_dec w Trv) = Trv.
Proof.
intros w. unfold DecInterval.set_dec. destruct (Interval.is_empty w); reflexivity.
Qed.

(** A nonempty interval without 0 is in [N1] or [P1]: one in [M] holds 0,
    which is between its elements of both signs. *)
Lemma classify_no0 :
  forall x c, valid x -> Interval.classify x = Some c ->
  (exists r, mem r x) -> ~ mem 0 x -> c = CN1 \/ c = CP1.
Proof.
intros x c Hx Cx (r & Hr) H0. pose proof (classify_mem x c Hx Cx) as M.
destruct c; [| | | left; reflexivity | | right; reflexivity |]; exfalso.
- exact (M r Hr).
- destruct M as ((a & Ha & Ha0) & (b & Hb & Hb0)).
  apply H0, (mem_between x a b 0 Hx Ha Hb). lra.
- exact (H0 (proj1 (proj2 M))).
- exact (H0 (proj1 (proj2 M))).
- exact (H0 (proj2 (M 0) eq_refl)).
Qed.

Theorem dec_mul_rev_to_pair_correct :
  forall has_fma x y, valid (itv x) -> valid (itv y) ->
  exists u v, DecInterval.mul_rev_to_pair has_fma x y = Some (u, v) /\
    if DecInterval.is_nai x || DecInterval.is_nai y then
      u = DecInterval.NAI /\ v = DecInterval.NAI
    else
      two_output (mul_rev (itv x) (itv y)) (itv u) (itv v) /\ dec v = Trv /\
      ((exists r, mem r (itv x)) -> (exists r, mem r (itv y)) -> ~ mem 0 (itv x) ->
         DecInterval.div has_fma y x = Some u) /\
      ((forall r, ~ mem r (itv x)) \/ (forall r, ~ mem r (itv y)) \/ mem 0 (itv x) ->
         dec u = Trv).
Proof.
intros has_fma x y Hx Hy. unfold DecInterval.mul_rev_to_pair.
destruct (DecInterval.is_nai x || DecInterval.is_nai y) eqn:N;
  [exists DecInterval.NAI, DecInterval.NAI;
   split; [reflexivity | split; reflexivity]|].
apply Bool.orb_false_iff in N. destruct N as [Nx Ny].
assert (Hdx : dec x <> Ill).
{ intros E. unfold DecInterval.is_nai in Nx. rewrite E in Nx. discriminate. }
assert (Hdy : dec y <> Ill).
{ intros E. unfold DecInterval.is_nai in Ny. rewrite E in Ny. discriminate. }
destruct (mul_rev_to_pair_correct has_fma _ _ Hx Hy) as (u & v & E & Ht).
rewrite E. cbv beta iota zeta.
set (d := if Interval.contains (itv x) zero then Trv else dec_min (dec x) (dec y)).
assert (Hd : d <> Ill).
{ unfold d. destruct (Interval.contains (itv x) zero);
    [discriminate | exact (dec_min_not_Ill _ _ Hdx Hdy)]. }
exists (DecInterval.set_dec u d), (DecInterval.set_dec v Trv). split; [reflexivity|].
destruct (two_output_valid _ _ _ Ht) as (Hu & Hv).
rewrite (itv_set_dec u d Hu Hd), (itv_set_dec v Trv Hv ltac:(discriminate)).
split; [exact Ht|]. split; [apply dec_set_dec_Trv|]. split.
- (* [x] is in [N1] or [P1] and [y] is nonempty, so [mul_rev_to_pair]
     returns [[y / x, EMPTY]], and both decorate [y / x] with the
     smaller decoration of [x] and [y]. *)
  intros Ex (t & Ht') H0.
  destruct (classify_defined (itv x) Hx) as (cx & Cx).
  destruct (classify_defined (itv y) Hy) as (cy & Cy).
  assert (Hc : (cx = CN1 \/ cx = CP1) /\ cy <> CE).
  { split; [exact (classify_no0 _ _ Hx Cx Ex H0)|].
    intros ->. exact (classify_mem _ _ Hy Cy t Ht'). }
  pose proof (mul_rev_div_eq has_fma _ _ _ _ Cx Cy (or_introl Hc)) as Em.
  destruct (div_correct has_fma (itv y) (itv x) Hy Hx) as (z & Ez & _).
  rewrite E, Ez in Em. cbv beta iota in Em. injection Em as -> _.
  unfold DecInterval.div, DecInterval.is_nai.
  unfold DecInterval.is_nai in Nx, Ny. rewrite Nx, Ny. cbn [orb].
  rewrite Ez. cbv beta iota zeta. unfold d. rewrite (dec_min_comm (dec y)).
  reflexivity.
- intros H.
  (* For an empty set the first output is [EMPTY], which [set_dec]
     decorates [trv]. *)
  assert (Hs : (forall r, ~ mul_rev (itv x) (itv y) r) ->
               dec (DecInterval.set_dec u d) = Trv).
  { intros Hs. rewrite (two_output_empty_fst _ _ _ Ht Hs).
    exact (f_equal dec (set_dec_empty_any Interval.EMPTY d eq_refl Hd)). }
  destruct H as [Nx0 | [Ny0 | H0]].
  + (* No [t] is in [x]. *)
    apply Hs. intros r (t & Ht' & _). exact (Nx0 t Ht').
  + (* No [t * r] is in [y]. *)
    apply Hs. intros r (t & _ & Ht'). exact (Ny0 (t * r) Ht').
  + (* [x] contains 0, so [d] is [trv]. *)
    unfold d. rewrite (proj2 (contains_zero _ Hx) H0). apply dec_set_dec_Trv.
Qed.
