(** * [x / y] of intervals is tightest and decorated correctly

    [x / y] of [Interval]s returns the tightest interval that contains the
    image of the box [x × y] under [/] on its domain R × (R ∖ {0})
    ([image2_dom], [div_dom1] and [div_dom2] in [Ieee1788.v]), for either
    value of [has_fma], and [x / y] of [DecInterval]s decorates it with the
    minimum of the strongest decoration that holds and the decorations of
    [x] and [y], as IEEE 1788 asks of a tightest interval version of a
    function, if each of [x] and [y] is [com] only when its interval is
    common.

    [Interval::div] dispatches on the pair of the classes of its arguments
    ([classify2_pair] in [Classify2.v]), and [Interval::classify] is
    defined on every valid interval ([classify_defined] in [Abs.v]). So
    [div_correct] goes through the 49 pairs, and a lemma in another file
    proves each:
    - [div_empty] in [DivZero.v]: the 19 pairs with [E] on either side or
      [Z] on the right;
    - [div_zero] in [DivZero.v]: the 5 pairs with [Z] on the left only;
    - [div_entire] in [DivZero.v]: the 7 pairs that give [ENTIRE];
    - the 10 lemmas of [DivCases.v]: the other 18 pairs.
    That is 19 + 5 + 7 + 18 = 49.

    [/] is continuous at each point [(r, t)] with [t <> 0]
    ([Rdiv_continuous]). The strongest decoration of [/] on [x × y], with
    the result [z], is:
    - [trv] if [z] is empty: the image is then empty, and [def] asks for a
      nonempty box in the domain.
    - [trv] if 0 is in [y], as [def] asks for the box to be a subset of the
      domain. That is when [y.contains(0.0)], the test of
      [DecInterval::div] ([contains_zero] in [DivZero.v]).
    - [com] if [x], [y] and [z] are nonempty and bounded.
    - [dac] otherwise.
    [[1, 2] / [1, +inf]] is [[0, 2]], which is common though the box is not
    bounded, so, as [dec_mul_correct] in [Mul.v] does, [dec_div_correct]
    assumes that each argument is [com] only if its interval is common
    ([com_common]), which [ComCommon.v] shows of every [DecInterval] that
    the library makes. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer Sign MaxMin ComCommon DecBinary
  AddSub Abs Mul DivZero DivCases Recip.

Open Scope R_scope.

(** ** [Interval::div] *)

Theorem div_correct :
  forall has_fma x y, valid x -> valid y ->
  exists z, Interval.div has_fma x y = Some z /\
    is_tightest (image2_dom div_dom1 div_dom2 Rdiv x y) z.
Proof.
intros has_fma x y Hx Hy.
destruct (classify_defined x Hx) as (cx & Cx).
destruct (classify_defined y Hy) as (cy & Cy).
(* Each of the 49 pairs is a case of exactly one lemma. [auto] proves the
   class hypotheses, picking the side of a disjunction such as
   [cx = CE \/ cy = CE \/ cy = CZ], and [discriminate] proves that two
   different classes differ. *)
destruct cx, cy;
  first
    [ solve [apply (div_empty has_fma x y _ _ Hx Hy Cx Cy); auto]
    | solve [apply (div_zero has_fma x y _ Hx Hy Cx Cy); discriminate]
    | solve [apply (div_entire has_fma x y _ _ Hx Hy Cx Cy);
             solve [left; split; [reflexivity | auto]
                   | right; split; [reflexivity | split; discriminate]]]
    | solve [apply div_MN1; auto]
    | solve [apply div_MP1; auto]
    | solve [apply div_NN0; auto]
    | solve [apply div_NN1; auto]
    | solve [apply div_NP0; auto]
    | solve [apply div_NP1; auto]
    | solve [apply div_PN0; auto]
    | solve [apply div_PN1; auto]
    | solve [apply div_PP0; auto]
    | solve [apply div_PP1; auto] ].
Qed.

(** ** The strongest decoration on a box in a domain *)

Lemma strongest2_dom_Trv :
  forall D1 D2 f x y z, ~ p2_dom D1 D2 Def f x y z ->
  strongest2_dom D1 D2 Trv f x y z.
Proof.
intros D1 D2 f x y z H. split; [exact I|].
(* Each decoration above [trv] asks for a nonempty box in the domain. *)
intros [] He; cbn [discriminant]; try lia; exfalso; apply H; cbn [p2_dom] in *.
- exact He.
- destruct He as (Hx & Hy & HD1 & HD2 & _).
  split; [exact Hx|]. split; [exact Hy|]. split; assumption.
- destruct He as (Hx & Hy & HD1 & HD2 & _).
  split; [exact Hx|]. split; [exact Hy|]. split; assumption.
Qed.

Lemma strongest2_dom_Dac :
  forall D1 D2 f x y z, p2_dom D1 D2 Dac f x y z -> ~ p2_dom D1 D2 Com f x y z ->
  strongest2_dom D1 D2 Dac f x y z.
Proof.
intros D1 D2 f x y z Hd Hc. split; [exact Hd|].
intros [] He; cbn [discriminant]; try lia. exfalso. exact (Hc He).
Qed.

Lemma strongest2_dom_Com :
  forall D1 D2 f x y z, p2_dom D1 D2 Com f x y z -> strongest2_dom D1 D2 Com f x y z.
Proof.
intros D1 D2 f x y z Hc. split; [exact Hc|].
intros [] _; cbn [discriminant]; lia.
Qed.

(** ** [DecInterval::div] *)

(** A function of two reals that is continuous at a point is continuous
    there relative to any box. *)
Lemma continuity2_pt_continue_in2 :
  forall f X Y r t, continuity2_pt f r t -> continue_in2 f X Y r t.
Proof.
intros f X Y r t Hc eps Heps. destruct (Hc eps Heps) as (delta & Hd & H).
exists delta. split; [exact Hd|].
intros r' t' _ _. exact (H r' t' I I).
Qed.

(** [r / t] is [r * / t]: [*] is continuous at [(r, / t)] ([Rmult_continuous]
    in [Mul.v]), so [r' * s'] is within [eps] of [r / t] for [r'] and [s']
    within [d1] of [r] and [/ t]. [/] is continuous at [t <> 0]
    ([Rinv_continuous] in [Recip.v]), so [/ t'] is within [d1] of [/ t] for
    [t'] within [alp] of [t], and [min d1 alp] does for both. *)
Lemma Rdiv_continuous : forall r t, t <> 0 -> continuity2_pt Rdiv r t.
Proof.
intros r t Ht eps Heps.
destruct (Rmult_continuous r (/ t) eps Heps) as (d1 & Hd1 & H1).
destruct (Rinv_continuous t Ht d1 Hd1) as (alp & Halp & H2).
assert (H3 : forall t', Rabs (t' - t) < alp -> Rabs (/ t' - / t) < d1).
{ intros t' Ht'. destruct (Req_dec t' t) as [E|E].
  - rewrite E. replace (/ t - / t) with 0 by ring. rewrite Rabs_R0. exact Hd1.
  - exact (H2 t' (conj (conj I (fun E' => E (eq_sym E'))) Ht')). }
exists (Rmin d1 alp). split; [apply Rmin_pos; assumption|].
intros r' t' _ _ Hr Ht'.
pose proof (Rmin_l d1 alp) as M1. pose proof (Rmin_r d1 alp) as M2.
unfold Rdiv. apply (H1 r' (/ t') I I); [lra|].
apply H3. lra.
Qed.

(** [x / y] of [DecInterval]s returns NaI if either argument is NaI, and
    otherwise the tightest interval, decorated with the decoration that
    IEEE 1788 asks for, if each argument is [com] only when its interval is
    common. *)
Theorem dec_div_correct :
  forall has_fma x y, valid (itv x) -> valid (itv y) ->
  com_common x ->
  com_common y ->
  exists z, DecInterval.div has_fma x y = Some z /\
    if DecInterval.is_nai x || DecInterval.is_nai y then z = DecInterval.NAI
    else
      is_tightest (image2_dom div_dom1 div_dom2 Rdiv (itv x) (itv y)) (itv z) /\
      exists d, strongest2_dom div_dom1 div_dom2 d Rdiv (itv x) (itv y) (itv z) /\
        dec z = dec_min d (dec_min (dec x) (dec y)).
Proof.
intros has_fma x y Hx Hy Hcx Hcy. unfold DecInterval.div.
destruct (DecInterval.is_nai x || DecInterval.is_nai y) eqn:N;
  [exists DecInterval.NAI; split; reflexivity|].
apply Bool.orb_false_iff in N. destruct N as [Nx Ny].
unfold DecInterval.is_nai in Nx, Ny.
assert (He : dec_min (dec x) (dec y) <> Ill).
{ apply dec_min_not_Ill; intros E; [rewrite E in Nx | rewrite E in Ny];
    discriminate. }
destruct (div_correct has_fma _ _ Hx Hy) as (z & Ez & Hz).
cbv zeta. rewrite Ez. cbv beta iota.
set (d := if Interval.contains (itv y) zero then Trv
          else dec_min (dec x) (dec y)).
assert (Hd : d <> Ill).
{ unfold d. destruct (Interval.contains (itv y) zero); [discriminate | exact He]. }
exists (DecInterval.set_dec z d). split; [reflexivity|].
destruct (Interval.is_empty z) eqn:Ez0.
- (* [z] is empty, so the image is, and the box has no point in the
     domain. *)
  pose proof (valid_empty_eq z (proj1 Hz) Ez0) as Ez1.
  rewrite (set_dec_empty_any z d Ez0 Hd). cbn [itv dec DecInterval.EMPTY].
  rewrite <- Ez1. split; [exact Hz|]. exists Trv.
  split; [|symmetry; exact (dec_min_Trv_l _ He)].
  apply strongest2_dom_Trv. intros Hdef. cbn [p2_dom] in Hdef.
  destruct Hdef as ((r & Hr) & (t & Ht) & _ & HD2).
  apply (mem_empty z (Rdiv r t) (proj1 Hz) Ez0).
  apply (proj1 (proj2 Hz)). exists r, t.
  split; [exact Hr|]. split; [exact Ht|]. split; [exact I|].
  split; [exact (HD2 t Ht) | reflexivity].
- (* [x] and [y] are nonempty, as the image is. *)
  assert (Ex : Interval.is_empty (itv x) = false).
  { destruct (Interval.is_empty (itv x)) eqn:Ex; [|reflexivity].
    rewrite (no_mem_empty z (proj1 Hz)) in Ez0; [discriminate Ez0|].
    apply (tightest_no_mem _ _ Hz). intros u (r & t & Hr & _).
    exact (mem_empty _ r Hx Ex Hr). }
  assert (Ey : Interval.is_empty (itv y) = false).
  { destruct (Interval.is_empty (itv y)) eqn:Ey; [|reflexivity].
    rewrite (no_mem_empty z (proj1 Hz)) in Ez0; [discriminate Ez0|].
    apply (tightest_no_mem _ _ Hz). intros u (r & t & _ & Ht & _).
    exact (mem_empty _ t Hy Ey Ht). }
  destruct (nonempty_mem _ Hx Ex) as (r0 & Hr0).
  destruct (nonempty_mem _ Hy Ey) as (t0 & Ht0).
  unfold d. destruct (Interval.contains (itv y) zero) eqn:C0.
  + (* 0 is in [y], so the box is not a subset of the domain. *)
    assert (Hc : Trv = Com -> Interval.is_common_interval z = true)
      by (intros E; discriminate E).
    rewrite (set_dec_keep z Trv Ez0 ltac:(discriminate) Hc).
    cbn [itv dec DecInterval.new_unchecked]. split; [exact Hz|].
    exists Trv. split; [|symmetry; exact (dec_min_Trv_l _ He)].
    apply strongest2_dom_Trv. intros Hdef. cbn [p2_dom] in Hdef.
    destruct Hdef as (_ & _ & _ & HD2).
    exact (HD2 0 (proj1 (contains_zero (itv y) Hy) C0) eq_refl).
  + (* 0 is not in [y], so the box is in the domain, where [/] is
       continuous. *)
    assert (HD2 : forall t, mem t (itv y) -> div_dom2 t).
    { intros t Ht. unfold div_dom2. intros E. rewrite E in Ht.
      rewrite (proj2 (contains_zero (itv y) Hy) Ht) in C0. discriminate C0. }
    assert (Hcont : forall X Y r t, mem t (itv y) -> continue_in2 Rdiv X Y r t).
    { intros X Y r t Ht. apply continuity2_pt_continue_in2, Rdiv_continuous.
      exact (HD2 t Ht). }
    assert (Hdac : p2_dom div_dom1 div_dom2 Dac Rdiv (itv x) (itv y) z).
    { cbn [p2_dom]. split; [exists r0; exact Hr0|].
      split; [exists t0; exact Ht0|].
      split; [intros r _; exact I|]. split; [exact HD2|].
      intros r t _ Ht. exact (Hcont _ _ r t Ht). }
    destruct (Interval.is_common_interval z) eqn:Cz.
    * rewrite (set_dec_keep z _ Ez0 He (fun _ => Cz)).
      cbn [itv dec DecInterval.new_unchecked]. split; [exact Hz|].
      pose proof (common_bounded z Cz) as Bz.
      destruct (Interval.is_common_interval (itv x) &&
                Interval.is_common_interval (itv y)) eqn:C.
      -- (* A bounded box and a bounded [z]. *)
         apply andb_prop in C. destruct C as [Cx Cy].
         exists Com. split; [|symmetry; apply dec_min_Com_l].
         apply strongest2_dom_Com. cbn [p2_dom].
         split; [exists r0; exact Hr0|]. split; [exists t0; exact Ht0|].
         split; [intros r _; exact I|]. split; [exact HD2|].
         split; [exact (common_bounded _ Cx)|].
         split; [exact (common_bounded _ Cy)|].
         split; [intros r t _ Ht; exact (Hcont _ _ r t Ht) | exact Bz].
      -- (* An unbounded box: [x] or [y] is not common, so not bounded, as
            it is nonempty, and by [com_common] not [com], so neither is
            the minimum of their decorations. *)
         assert (Hnb : ~ (bounded (fun r => mem r (itv x)) /\
                          bounded (fun t => mem t (itv y)))).
         { intros [Bx By].
           rewrite (bounded_common _ Hx Ex Bx), (bounded_common _ Hy Ey By) in C.
           discriminate C. }
         assert (Hnc : dec_min (dec x) (dec y) <> Com).
         { intros E. apply dec_min_Com in E. destruct E as [Ex' Ey'].
           apply Hnb. split; apply common_bounded; [exact (Hcx Ex') | exact (Hcy Ey')]. }
         exists Dac. split; [|symmetry; exact (dec_min_Dac_l _ Hnc)].
         apply strongest2_dom_Dac; [exact Hdac|].
         intros Hcom. cbn [p2_dom] in Hcom.
         destruct Hcom as (_ & _ & _ & _ & Bx & By & _). exact (Hnb (conj Bx By)).
    * (* [z] is not common, so not bounded, as it is nonempty. *)
      rewrite (set_dec_lower z _ Ez0 Cz He).
      cbn [itv dec DecInterval.new_unchecked]. split; [exact Hz|].
      exists Dac. split; [|reflexivity].
      apply strongest2_dom_Dac; [exact Hdac|].
      intros Hcom. cbn [p2_dom] in Hcom.
      destruct Hcom as (_ & _ & _ & _ & _ & _ & _ & Bz).
      rewrite (bounded_common z (proj1 Hz) Ez0 Bz) in Cz. discriminate Cz.
Qed.
