(** * Decorations of operations on two intervals

    [elem2_set_dec_correct] is the generic theorem about the decorations
    of a function [f] of two reals, defined on a set [D] of points of R². Let
    [z] be the tightest interval that contains the image of the box
    [x × y] under [f] on [D], and [e] the decoration that [dec_holds]
    describes for [f] on the box. Then [set_dec] of [z] with the minimum
    of [e] and the decorations of [x] and [y] returns the tightest
    interval, decorated with the minimum of the strongest decoration and
    those of [x] and [y], as IEEE 1788 asks, if a box of two [com]
    intervals is bounded when [e] is [com] and [z] is common. [set_dec]
    keeps a minimum below [com]. It lowers [com] to [dac] if [z] is not
    common, so unbounded, as [com] asks for a bounded [z], and keeps it if
    [z] is common, where [com] holds, as [x] and [y] are then [com] and so
    the box is bounded.
    [elem_dec2_impl_correct] in [Dom2.v] applies it to the decorated
    versions of [pow] and [atan2], [dec_div_correct] in [Div.v] to [/],
    with the [*_prod] lemmas of [Dom2.v], and [set_dec_correct] below to
    [max], [min], [+], [-] and [*].

    [DecInterval::max], [DecInterval::min], [DecInterval::add],
    [DecInterval::sub] and [DecInterval::mul] call [set_dec] with the
    result [z] of the operation
    on the bare intervals [x] and [y] and the minimum [e] of their
    decorations, unless an argument is NaI. [set_dec_correct] shows that
    this decorates [z] as IEEE 1788 asks, for any function [h] of two reals
    that is continuous at each point of R², if [z] is the tightest interval
    that contains the image of the box [x × y] under [h]. The proofs about
    each operation show that [z] is, and use nothing else about it. On all
    of R², the decoration that [dec_holds] describes for [h] is [com] for a
    nonempty box, as [h] is continuous, and [trv] for an empty one, whose
    image, and so [z], is empty. [set_dec] returns [EMPTY] for an empty
    [z] and any decoration other than [ill], so in both cases [set_dec] of
    [z] with [e] is what [elem2_set_dec_correct] gives for [x] decorated
    [e] and [y] decorated [com].

    [set_dec_correct] takes as a hypothesis that [e] is [com]
    only if a nonempty box whose image is bounded is bounded too. This
    holds for [+] and [-] of intervals, where [|r| <= |r + t| + |t|], but
    not for [max], [min] and [*]: [max([-inf, 1], [0, 2]) = [0, 2]], and
    [[0, 0] × [1, +inf]] has the image [{0}]. For those, [DecMaxMin.v] and
    [Mul.v] assume that each argument is [com] only if its interval is
    common, which [ComCommon.v] shows of every [DecInterval] that the
    library makes.

    [p2] asks for [com] that [z] be bounded, as the standard does, rather
    than the image: [[f64::MAX, f64::MAX] + [f64::MAX, f64::MAX]] is
    [[f64::MAX, +inf]], which the standard decorates [dac], though the
    image is bounded. *)

From Stdlib Require Import ZArith Reals Lra Lia Classical_Prop.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer Sign.

Open Scope R_scope.

(** ** Intervals and their members *)

(** A common interval is bounded. Both lanes of [[-a; b]] are below +inf,
    so [a] is not -inf and [b] is not +inf, and a NaN or the other
    infinity as a bound leaves no member. *)
Lemma common_bounded :
  forall x, Interval.is_common_interval x = true -> bounded (fun r => mem r x).
Proof.
intros x Hc. rewrite is_common_interval_lt, infinity_eq in Hc.
apply andb_prop in Hc. destruct Hc as [H0 H1].
exists (Rabs (B2R (opp (fst (rep x)))) + Rabs (B2R (snd (rep x)))).
intros r [Ha Hb]. apply Rabs_between. split.
- destruct (opp (fst (rep x))) as [s|s| |s m e He] eqn:E; try exact Ha.
  + (* [a = -inf], so the first lane is +inf. *)
    exfalso. subst s.
    assert (E0 : fst (rep x) = B754_infinity false).
    { rewrite <- (Bopp_involutive _ _ (fst (rep x))). unfold opp in E.
      now rewrite E. }
    rewrite E0 in H0. discriminate H0.
  + destruct Ha.
- destruct (snd (rep x)) as [s|s| |s m e He] eqn:E; try exact Hb.
  + (* [b = +inf] *)
    exfalso. subst s. discriminate H1.
  + destruct Hb.
Qed.

(** A nonempty bounded interval is common: an infinite bound would give it
    members of any magnitude. *)
Lemma bounded_common :
  forall z, valid z -> Interval.is_empty z = false ->
  bounded (fun r => mem r z) -> Interval.is_common_interval z = true.
Proof.
intros z Hz Hn Hb.
destruct (valid_nonempty z Hz Hn) as (Ha & Hb' & _).
assert (HX : forall r, mem r z <->
               in_bounds (bound (opp (fst (rep z)))) (bound (snd (rep z))) r).
{ intros r. now apply mem_bounds. }
apply finite_common.
- destruct Ha as [Fa|Ea]; [exact Fa|]. exfalso.
  rewrite Ea, bound_inf in HX. exact (unbounded_lo z _ HX Hb).
- destruct Hb' as [Fb|Eb]; [exact Fb|]. exfalso.
  rewrite Eb, bound_inf in HX. exact (unbounded_hi z _ HX Hb).
Qed.

Lemma nonempty_mem :
  forall z, valid z -> Interval.is_empty z = false -> exists r, mem r z.
Proof.
intros z Hz Hn. destruct (valid_nonempty z Hz Hn) as (Ha & Hb & Hord).
destruct (in_bounds_nonempty _ _ Hord) as (r & Hr).
exists r. exact (proj2 (mem_bounds z r Ha Hb) Hr).
Qed.

Lemma mem_empty :
  forall z r, valid z -> Interval.is_empty z = true -> ~ mem r z.
Proof.
intros z r Hz Hn. exact (mem_nan z r (empty_nan z Hz Hn)).
Qed.

Lemma mem_not_empty :
  forall z r, valid z -> mem r z -> Interval.is_empty z = false.
Proof.
intros z r Hz Hr. destruct (Interval.is_empty z) eqn:E; [|reflexivity].
destruct (mem_empty z r Hz E Hr).
Qed.

Lemma no_mem_empty :
  forall z, valid z -> (forall r, ~ mem r z) -> Interval.is_empty z = true.
Proof.
intros z Hz N. destruct (Interval.is_empty z) eqn:E; [reflexivity|].
destruct (nonempty_mem z Hz E) as (r & Hr). destruct (N r Hr).
Qed.

(** The empty interval has only one representation, [[NaN; NaN]]. *)
Lemma valid_empty_eq :
  forall z, valid z -> Interval.is_empty z = true -> z = Interval.EMPTY.
Proof.
intros [rz] Hz Hn. pose proof (empty_nan _ Hz Hn) as E. cbn [rep] in E.
now subst rz.
Qed.

(** An interval holds every real between two of its members. *)
Lemma mem_between :
  forall z u v r, valid z -> mem u z -> mem v z -> u <= r <= v -> mem r z.
Proof.
intros z u v r Hz Hu Hv Hr.
destruct (valid_nonempty z Hz (mem_not_empty z u Hz Hu)) as (Ha & Hb & _).
apply (mem_bounds z r Ha Hb).
apply (in_bounds_between _ _ u v); [apply (mem_bounds z u Ha Hb), Hu |
  apply (mem_bounds z v Ha Hb), Hv | exact Hr].
Qed.

(** A hull contains its set. *)
Lemma hull_mem : forall s z u, is_hull s z -> s u -> mem u z.
Proof.
intros s z u [_ Hz] Hu. apply Hz. exists u, u.
split; [exact Hu|]. split; [exact Hu|]. split; apply Rle_refl.
Qed.

(** The hull is the tightest interval, as every interval that contains two
    reals contains those between them. *)
Lemma hull_tightest : forall s y, is_hull s y -> is_tightest s y.
Proof.
intros s y Hy. split; [exact (proj1 Hy)|]. split.
- intros u Hu. exact (hull_mem s y u Hy Hu).
- intros z Hz Hs r Hr. apply (proj2 Hy) in Hr.
  destruct Hr as (u & v & Hu & Hv & Hr).
  exact (mem_between z u v r Hz (Hs u Hu) (Hs v Hv) Hr).
Qed.

(** The tightest interval that contains an empty set is empty, as [EMPTY]
    contains that set. *)
Lemma tightest_no_mem :
  forall s z, is_tightest s z -> (forall u, ~ s u) -> forall r, ~ mem r z.
Proof.
intros s z (_ & _ & Hz) Hs r Hr.
assert (He : valid Interval.EMPTY) by (left; split; reflexivity).
apply (mem_nan Interval.EMPTY r eq_refl).
apply (Hz Interval.EMPTY He); [|exact Hr].
intros u Hu. destruct (Hs u Hu).
Qed.

Lemma image2_mem :
  forall h x y r t, mem r x -> mem t y -> image2 h x y (h r t).
Proof.
intros h x y r t Hr Ht. exists r, t.
split; [exact Hr|]. split; [exact Ht | reflexivity].
Qed.

Lemma image2_empty :
  forall h x y, (forall r, ~ mem r x) \/ (forall t, ~ mem t y) ->
  forall u, ~ image2 h x y u.
Proof.
intros h x y H u (r & t & Hr & Ht & _).
destruct H as [H|H]; [exact (H r Hr) | exact (H t Ht)].
Qed.

(** ** Decorations *)

Lemma dec_min_not_Ill :
  forall d e, d <> Ill -> e <> Ill -> dec_min d e <> Ill.
Proof.
intros [] [] Hd He; cbn; try discriminate; congruence.
Qed.

(** [dec_min d e] is [com] only if both are. *)
Lemma dec_min_Com :
  forall d e, dec_min d e = Com -> d = Com /\ e = Com.
Proof.
intros [] [] H; cbn in H; first [split; reflexivity | discriminate H].
Qed.

Lemma dec_min_Trv_l : forall e, e <> Ill -> dec_min Trv e = Trv.
Proof.
intros [] He; first [reflexivity | now elim He].
Qed.

Lemma dec_min_Dac_l : forall e, e <> Com -> dec_min Dac e = e.
Proof.
intros [] He; first [reflexivity | now elim He].
Qed.

Lemma dec_min_Com_l : forall e, dec_min Com e = e.
Proof.
intros []; reflexivity.
Qed.

Lemma dec_min_Com_r : forall d, dec_min d Com = d.
Proof.
intros []; reflexivity.
Qed.

Lemma dec_min_Trv_r : forall d, d <> Ill -> dec_min d Trv = Trv.
Proof.
intros [] Hd; first [reflexivity | now elim Hd].
Qed.

(** [set_dec] with a decoration that is not [ill]: [EMPTY] for an empty
    interval, and otherwise the decoration unchanged if it is [com] only
    for a common interval, and lowered to [dac] if the interval is not
    common. *)
Lemma set_dec_empty_any :
  forall z e, Interval.is_empty z = true -> e <> Ill ->
  DecInterval.set_dec z e = DecInterval.EMPTY.
Proof.
intros z e Hz He. unfold DecInterval.set_dec. rewrite Hz.
destruct e; first [reflexivity | congruence].
Qed.

Lemma set_dec_keep :
  forall z e,
  Interval.is_empty z = false -> e <> Ill ->
  (e = Com -> Interval.is_common_interval z = true) ->
  DecInterval.set_dec z e = DecInterval.new_unchecked z e.
Proof.
intros z e Hz He Hc. unfold DecInterval.set_dec. rewrite Hz.
destruct e; try congruence; try reflexivity.
cbn. now rewrite Hc.
Qed.

Lemma set_dec_lower :
  forall z e,
  Interval.is_empty z = false -> Interval.is_common_interval z = false ->
  e <> Ill ->
  DecInterval.set_dec z e = DecInterval.new_unchecked z (dec_min Dac e).
Proof.
intros z e Hz Hc He. unfold DecInterval.set_dec. rewrite Hz, Hc.
destruct e; first [reflexivity | congruence].
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

(** ** Functions of two reals with any domain *)

Lemma image2_set_all :
  forall f x y s, image2_set (fun _ _ => True) f x y s <-> image2 f x y s.
Proof.
intros f x y s. unfold image2_set, image2. split.
- intros (r & t & Hr & Ht & _ & Hs). exists r, t. exact (conj Hr (conj Ht Hs)).
- intros (r & t & Hr & Ht & Hs). exists r, t. exact (conj Hr (conj Ht (conj I Hs))).
Qed.

(** Continuity relative to all of R² is [continuity2_pt]. *)
Lemma d2_continue_in2_set_all :
  forall f r t, continue_in2_set f (fun _ _ => True) r t <-> continuity2_pt f r t.
Proof.
intros f r t. unfold continue_in2_set, continuity2_pt, continue_in2.
split; intros H eps Heps; destruct (H eps Heps) as (delta & Hd & H');
  exists delta; (split; [exact Hd|]).
- intros r' t' _ _. exact (H' r' t' I).
- intros r' t' _. exact (H' r' t' I I).
Qed.

Lemma p2_set_all :
  forall d f x y z, p2_set (fun _ _ => True) d f x y z <-> p2 d f x y z.
Proof.
intros d f x y z. destruct d; cbn [p2_set p2]; [tauto | tauto | | |].
- (* [def] *)
  split.
  + intros (Hx & Hy & _). exact (conj Hx Hy).
  + intros (Hx & Hy). split; [exact Hx|]. split; [exact Hy|]. intros; exact I.
- (* [dac] *)
  split.
  + intros (Hx & Hy & _ & Hc). split; [exact Hx|]. split; [exact Hy | exact Hc].
  + intros (Hx & Hy & Hc). split; [exact Hx|]. split; [exact Hy|].
    split; [intros; exact I | exact Hc].
- (* [com] *)
  split.
  + intros (Hx & Hy & _ & Bx & By & Hc & Bz). split; [exact Hx|].
    split; [exact Hy|]. split; [exact Bx|]. split; [exact By|].
    split; [|exact Bz].
    intros r t Hr Ht. exact (proj1 (d2_continue_in2_set_all f r t) (Hc r t Hr Ht)).
  + intros (Hx & Hy & Bx & By & Hc & Bz). split; [exact Hx|].
    split; [exact Hy|]. split; [intros; exact I|]. split; [exact Bx|].
    split; [exact By|]. split; [|exact Bz].
    intros r t Hr Ht. exact (proj2 (d2_continue_in2_set_all f r t) (Hc r t Hr Ht)).
Qed.

Lemma strongest2_set_all :
  forall d f x y z, strongest2_set (fun _ _ => True) d f x y z <-> strongest2 d f x y z.
Proof.
intros d f x y z. unfold strongest2_set, strongest2. split.
- intros (Hp & Hm). split; [exact (proj1 (p2_set_all d f x y z) Hp)|].
  intros e He. apply Hm. exact (proj2 (p2_set_all e f x y z) He).
- intros (Hp & Hm). split; [exact (proj2 (p2_set_all d f x y z) Hp)|].
  intros e He. apply Hm. exact (proj1 (p2_set_all e f x y z) He).
Qed.

(** ** The strongest decoration *)

Lemma strongest2_set_Trv :
  forall D f x y z, ~ p2_set D Def f x y z -> strongest2_set D Trv f x y z.
Proof.
intros D f x y z H. split; [exact I|].
(* Each decoration above [trv] asks for a nonempty box in the domain. *)
intros [] He; cbn [discriminant]; try lia; exfalso; apply H; cbn [p2_set] in *.
- exact He.
- destruct He as (Hx & Hy & HD & _).
  split; [exact Hx|]. split; [exact Hy | exact HD].
- destruct He as (Hx & Hy & HD & _).
  split; [exact Hx|]. split; [exact Hy | exact HD].
Qed.

Lemma strongest2_set_Dac :
  forall D f x y z, p2_set D Dac f x y z -> ~ p2_set D Com f x y z ->
  strongest2_set D Dac f x y z.
Proof.
intros D f x y z Hd Hc. split; [exact Hd|].
intros [] He; cbn [discriminant]; try lia. exfalso. exact (Hc He).
Qed.

Lemma strongest2_set_Com :
  forall D f x y z, p2_set D Com f x y z -> strongest2_set D Com f x y z.
Proof.
intros D f x y z Hc. split; [exact Hc|].
intros [] _; cbn [discriminant]; lia.
Qed.

(** A function continuous at [(r, t)] relative to [D] is continuous there
    relative to any box in [D], as the points of the box near [(r, t)] are
    points of [D] near it. *)
Lemma d2_continue_in2_sub :
  forall f (D : R -> R -> Prop) (X Y : R -> Prop) r t,
  continue_in2_set f D r t -> (forall r' t', X r' -> Y t' -> D r' t') ->
  continue_in2 f X Y r t.
Proof.
intros f D X Y r t Hc HXY eps Heps. destruct (Hc eps Heps) as (delta & Hd & H).
exists delta. split; [exact Hd|].
intros r' t' Hr Ht. exact (H r' t' (HXY r' t' Hr Ht)).
Qed.

(** [dec_holds D f x y z e] says what the decoration [e] that the interval
    function returns for the box [x × y] claims: [trv], that [def] does
    not hold; [def], that [def] holds and [dac] does not; [dac], that
    [dac] holds and [f] is not continuous relative to [D] at some point of
    the box; and [com], that [dac] holds and [f] is continuous relative to
    [D] at each point of the box. [com] then holds if the box and [z] are
    bounded too, which [elem2_set_dec_correct] leaves to [set_dec] and to
    its last hypothesis. [p2_set] asks nothing of [z] below [com], so
    [dec_holds] does not depend on it. *)
Definition dec_holds (D : R -> R -> Prop) (f : R -> R -> R) (x y z : Interval)
    (e : Decoration) : Prop :=
  match e with
  | Ill => False
  | Trv => ~ p2_set D Def f x y z
  | Def => p2_set D Def f x y z /\ ~ p2_set D Dac f x y z
  | Dac =>
      p2_set D Dac f x y z /\
      ~ (forall r t, mem r x -> mem t y -> continue_in2_set f D r t)
  | Com =>
      p2_set D Dac f x y z /\
      (forall r t, mem r x -> mem t y -> continue_in2_set f D r t)
  end.

(** [dec_min] is associative and commutative. *)
Lemma d2_dec_min_assoc :
  forall a b e, dec_min a (dec_min b e) = dec_min e (dec_min a b).
Proof.
intros [] [] []; reflexivity.
Qed.

(** [set_dec] of the tightest interval [z] with the decoration [e] that
    the interval function returns, if [e] is the one that [dec_holds]
    describes, and a box of two [com] intervals is bounded when [e] is
    [com] and [z] is common. *)
Theorem elem2_set_dec_correct :
  forall D f x y z e,
  valid (itv x) -> valid (itv y) -> dec x <> Ill -> dec y <> Ill ->
  is_tightest (image2_set D f (itv x) (itv y)) z ->
  dec_holds D f (itv x) (itv y) z e ->
  (e = Com -> dec x = Com -> dec y = Com -> Interval.is_common_interval z = true ->
   bounded (fun r => mem r (itv x)) /\ bounded (fun t => mem t (itv y))) ->
  let w := DecInterval.set_dec z (dec_min (dec x) (dec_min (dec y) e)) in
  is_tightest (image2_set D f (itv x) (itv y)) (itv w) /\
  exists d, strongest2_set D d f (itv x) (itv y) (itv w) /\
    dec w = dec_min d (dec_min (dec x) (dec y)).
Proof.
intros D f x y z e Hx Hy Hdx Hdy Ht Hh Hb. cbv zeta.
pose proof (proj1 Ht) as Hz.
assert (Hm3 : forall e', e' <> Ill -> dec_min (dec x) (dec_min (dec y) e') <> Ill).
{ intros e' He'. apply dec_min_not_Ill; [exact Hdx|]. apply dec_min_not_Ill; assumption. }
(* A nonempty box in [D] has a point whose image is in [z], so [z] is not
   empty. *)
assert (Hne : (exists r, mem r (itv x)) -> (exists t, mem t (itv y)) ->
              (forall r t, mem r (itv x) -> mem t (itv y) -> D r t) ->
              Interval.is_empty z = false).
{ intros (r & Hr) (t & Htm) HD.
  apply (mem_not_empty z (f r t) Hz). apply (proj1 (proj2 Ht)).
  exists r, t. split; [exact Hr|]. split; [exact Htm|].
  split; [exact (HD r t Hr Htm) | reflexivity]. }
destruct e; cbn [dec_holds] in Hh.
- destruct Hh.
- (* [e = trv]: not even [def] holds, and [set_dec] keeps [trv] for any
     [z]. *)
  assert (Hm : dec_min (dec x) (dec y) <> Ill) by (apply dec_min_not_Ill; assumption).
  rewrite (dec_min_Trv_r _ Hdy), (dec_min_Trv_r _ Hdx).
  destruct (Interval.is_empty z) eqn:Ez0.
  + rewrite (set_dec_empty_any z Trv Ez0 ltac:(discriminate)).
    cbn [itv dec DecInterval.EMPTY]. rewrite <- (valid_empty_eq z Hz Ez0).
    split; [exact Ht|]. exists Trv.
    split; [apply strongest2_set_Trv; exact Hh|].
    symmetry. apply dec_min_Trv_l. exact Hm.
  + assert (Hc0 : Trv = Com -> Interval.is_common_interval z = true)
      by (intros E; discriminate E).
    rewrite (set_dec_keep z Trv Ez0 ltac:(discriminate) Hc0).
    cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|]. exists Trv.
    split; [apply strongest2_set_Trv; exact Hh|].
    symmetry. apply dec_min_Trv_l. exact Hm.
- (* [e = def]: [dac] does not hold, nor [com], which implies it. The
     minimum is below [com], so [set_dec] keeps it. *)
  destruct Hh as (Hdef & Nd).
  destruct Hdef as (Nx & Ny & HD).
  pose proof (Hne Nx Ny HD) as Ez0.
  assert (N : dec_min (dec x) (dec_min (dec y) Def) <> Com).
  { intros E. destruct (dec_min_Com _ _ E) as (_ & E1).
    destruct (dec_min_Com _ _ E1) as (_ & E2). discriminate E2. }
  rewrite (set_dec_keep z _ Ez0 (Hm3 Def ltac:(discriminate)) (fun E => False_ind _ (N E))).
  cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
  exists Def. split; [|apply d2_dec_min_assoc].
  split; [split; [exact Nx|]; split; [exact Ny | exact HD]|].
  intros [] He; cbn [discriminant]; try lia; exfalso; apply Nd.
  + exact He.
  + destruct He as (Hx' & Hy' & HD' & _ & _ & Hc & _).
    split; [exact Hx'|]. split; [exact Hy'|]. split; [exact HD'|].
    intros r t Hr Htm. exact (d2_continue_in2_sub f D _ _ r t (Hc r t Hr Htm) HD').
- (* [e = dac]: [com] does not hold, and [set_dec] keeps the minimum,
     which is below [com]. *)
  destruct Hh as (Hdac & Nc).
  pose proof Hdac as (Nx & Ny & HD & _).
  pose proof (Hne Nx Ny HD) as Ez0.
  assert (N : dec_min (dec x) (dec_min (dec y) Dac) <> Com).
  { intros E. destruct (dec_min_Com _ _ E) as (_ & E1).
    destruct (dec_min_Com _ _ E1) as (_ & E2). discriminate E2. }
  rewrite (set_dec_keep z _ Ez0 (Hm3 Dac ltac:(discriminate)) (fun E => False_ind _ (N E))).
  cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
  exists Dac. split; [|apply d2_dec_min_assoc].
  apply strongest2_set_Dac; [exact Hdac|].
  intros (_ & _ & _ & _ & _ & Hc & _). exact (Nc Hc).
- (* [e = com]: [set_dec] gets the minimum [m] of the decorations of [x]
     and [y]. *)
  destruct Hh as (Hdac & Hc).
  pose proof Hdac as (Nx & Ny & HD & _).
  pose proof (Hne Nx Ny HD) as Ez0.
  rewrite (d2_dec_min_assoc (dec x) (dec y) Com), dec_min_Com_l.
  assert (Hm : dec_min (dec x) (dec y) <> Ill) by (apply dec_min_not_Ill; assumption).
  destruct (Interval.is_common_interval z) eqn:Cz.
  + (* [z] is common: [set_dec] keeps [m], and [d] is [com] if it holds,
       and otherwise [dac], which holds. [com] holds if [m] is [com], as
       the box is then bounded. *)
    rewrite (set_dec_keep z _ Ez0 Hm (fun _ => Cz)).
    cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
    destruct (classic (p2_set D Com f (itv x) (itv y) z)) as [Pc|Pc].
    * exists Com.
      split; [apply strongest2_set_Com; exact Pc | symmetry; apply dec_min_Com_l].
    * exists Dac. split; [apply strongest2_set_Dac; [exact Hdac | exact Pc]|].
      symmetry. apply dec_min_Dac_l. intros E. apply Pc.
      destruct (dec_min_Com _ _ E) as (Edx & Edy).
      destruct (Hb eq_refl Edx Edy eq_refl) as (Bx & By).
      split; [exact Nx|]. split; [exact Ny|]. split; [exact HD|].
      split; [exact Bx|]. split; [exact By|]. split; [exact Hc|].
      exact (common_bounded z Cz).
  + (* [z] is not common, so it is unbounded and [com] does not hold, and
       [set_dec] lowers [m] to at most [dac]. *)
    rewrite (set_dec_lower z _ Ez0 Cz Hm).
    cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
    exists Dac. split; [|reflexivity].
    apply strongest2_set_Dac; [exact Hdac|].
    intros (_ & _ & _ & _ & _ & _ & Bz).
    rewrite (bounded_common z Hz Ez0 Bz) in Cz. discriminate Cz.
Qed.

(** ** A continuous function of two reals *)

Section Binary.

(** [h] is continuous at each point of R². *)
Variable h : R -> R -> R.

Hypothesis h_continuous : forall r t, continuity2_pt h r t.

(** The restriction of [h] to any box is continuous, as [h] is. *)
Lemma p2_Dac_continuous :
  forall x y z, (exists r, mem r x) -> (exists t, mem t y) -> p2 Dac h x y z.
Proof.
intros x y z Hx Hy. split; [exact Hx|]. split; [exact Hy|].
intros r t _ _ eps Heps.
destruct (h_continuous r t eps Heps) as (delta & Hd & H).
exists delta. split; [exact Hd|].
intros r' t' _ _. exact (H r' t' I I).
Qed.

(** [set_dec] keeps the tightest interval [z] that contains the image of
    [x × y], and decorates it as IEEE 1788 asks, if [e] is [com] only when
    a nonempty box with a bounded image is bounded. *)
Theorem set_dec_correct :
  forall x y z e, valid x -> valid y -> e <> Ill ->
  is_tightest (image2 h x y) z ->
  (e = Com -> (exists r, mem r x) -> (exists t, mem t y) ->
   bounded (image2 h x y) ->
   bounded (fun r => mem r x) /\ bounded (fun t => mem t y)) ->
  itv (DecInterval.set_dec z e) = z /\
  exists d, strongest2 d h x y z /\
    dec (DecInterval.set_dec z e) = dec_min d e.
Proof.
intros x y z e Hx Hy He Ht Hb.
(* [image2] is [image2_set] on all of R², so [z] is the tightest interval
   that contains that image too. *)
assert (Ht' : is_tightest (image2_set (fun _ _ => True) h x y) z).
{ destruct Ht as (Hz & Hin & Hmin). split; [exact Hz|]. split.
  - intros s Hs. apply Hin. exact (proj1 (image2_set_all h x y s) Hs).
  - intros w Hw Hs. apply (Hmin w Hw). intros s Hs'. apply Hs.
    exact (proj2 (image2_set_all h x y s) Hs'). }
(* The decoration [e'] that [dec_holds] describes for [h] on all of R² is
   [com] for a nonempty box, as [h] is continuous, and [trv] for an empty
   one. [set_dec] of [z] with the minimum of [e] and [e'] is that of [z]
   with [e]: for a nonempty box, [e'] is [com]; for an empty one, the image
   is empty, so [z] is empty, and [set_dec] returns [EMPTY] for both. *)
assert (He' : exists e', dec_holds (fun _ _ => True) h x y z e' /\
  (e' = Com -> e = Com -> Com = Com -> Interval.is_common_interval z = true ->
   bounded (fun r => mem r x) /\ bounded (fun t => mem t y)) /\
  DecInterval.set_dec z (dec_min e e') = DecInterval.set_dec z e).
{ destruct (classic ((exists r, mem r x) /\ (exists t, mem t y))) as [Hne|Hne].
  - exists Com. split; [|split].
    + cbn [dec_holds]. split.
      * exact (proj2 (p2_set_all Dac h x y z)
                 (p2_Dac_continuous x y z (proj1 Hne) (proj2 Hne))).
      * intros r t _ _. exact (proj2 (d2_continue_in2_set_all h r t) (h_continuous r t)).
    + (* A common [z] is bounded, and it contains the image. *)
      intros _ Ee _ Cz. apply (Hb Ee (proj1 Hne) (proj2 Hne)).
      destruct (common_bounded z Cz) as (m & Hm). exists m.
      intros s Hs. apply Hm. exact (proj1 (proj2 Ht) s Hs).
    + rewrite dec_min_Com_r. reflexivity.
  - exists Trv. split; [|split].
    + cbn [dec_holds p2_set]. intros (Nx & Ny & _). exact (Hne (conj Nx Ny)).
    + intros E. discriminate E.
    + assert (Ez : Interval.is_empty z = true).
      { apply (no_mem_empty z (proj1 Ht)). apply (tightest_no_mem _ z Ht).
        intros u (r & t & Hr & Htm & _).
        exact (Hne (conj (ex_intro _ r Hr) (ex_intro _ t Htm))). }
      rewrite (dec_min_Trv_r e He).
      rewrite (set_dec_empty_any z Trv Ez ltac:(discriminate)).
      rewrite (set_dec_empty_any z e Ez He). reflexivity. }
destruct He' as (e' & Hh & Hb' & Es).
assert (Hc : Com <> Ill) by discriminate.
(* [x] with the decoration [e] and [y] with [com] give [set_dec] the
   minimum of [e] and [e']. *)
pose proof (elem2_set_dec_correct (fun _ _ => True) h
  (DecInterval.new_unchecked x e) (DecInterval.new_unchecked y Com) z e'
  Hx Hy He Hc Ht' Hh Hb') as H.
cbv zeta in H. cbn [itv dec DecInterval.new_unchecked] in H.
rewrite (dec_min_Com_l e'), Es, (dec_min_Com_r e) in H.
destruct H as (_ & d & Hd & Hdw).
rewrite (itv_set_dec z e (proj1 Ht) He) in Hd.
split; [exact (itv_set_dec z e (proj1 Ht) He)|].
exists d. split; [exact (proj1 (strongest2_set_all d h x y z) Hd) | exact Hdw].
Qed.

End Binary.
