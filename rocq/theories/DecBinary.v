(** * Decorations of operations on two intervals

    [DecInterval::max], [DecInterval::min], [DecInterval::add],
    [DecInterval::sub] and [DecInterval::mul] call [set_dec] with the
    result [z] of the operation
    on the bare intervals [x] and [y] and the minimum [e] of their
    decorations, unless an argument is NaI. [set_dec_correct] shows that
    this decorates [z] as IEEE 1788 asks, for any function [h] of two reals
    that is continuous at each point of R², if [z] is the tightest interval
    that contains the image of the box [x × y] under [h]. The proofs about
    each operation show that [z] is, and use nothing else about it.

    The strongest decoration of [h] on [x × y], with the result [z], is:

    - [trv] if [x] or [y] is empty, as [def] asks for a nonempty box. The
      image is then empty, so the tightest interval [z] is empty, for which
      [set_dec] returns [EMPTY], whose [trv] is the minimum of [trv] and
      [e].
    - [com] if [x], [y] and [z] are nonempty and bounded. [z] is then
      common, and [set_dec] keeps [e], which is also its minimum with
      [com].
    - [dac] otherwise: [h] is continuous at each point of the box, so its
      restriction to the box is too, but [com] asks for a bounded box and a
      bounded [z]. If [z] is not common, it is unbounded, and [set_dec]
      lowers a [com] [e] to [dac] and keeps any other, which gives the
      minimum of [e] and [dac]. If [z] is common, [set_dec] keeps [e], so
      [e] must not be [com].

    [set_dec_correct] therefore takes as a hypothesis that [e] is [com]
    only if a nonempty box whose image is bounded is bounded too. This
    holds for [+] and [-] of intervals, where [|r| <= |r + t| + |t|], but
    not for [max], [min] and [*]: [max([-inf, 1], [0, 2]) = [0, 2]], and
    [[0, 0] × [1, +inf]] has the image [{0}]. For those, [DecMaxMin.v] and
    [Mul.v] assume that each argument is [com] only if its interval is
    common.

    [p2] asks for [com] that [z] be bounded, as the standard does, rather
    than the image: [[f64::MAX, f64::MAX] + [f64::MAX, f64::MAX]] is
    [[f64::MAX, +inf]], which the standard decorates [dac], though the
    image is bounded. *)

From Stdlib Require Import ZArith Reals Lra Lia.
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

(** ** The strongest decoration on a box *)

Lemma strongest2_Trv :
  forall h x y z, (forall r, ~ mem r x) \/ (forall t, ~ mem t y) ->
  strongest2 Trv h x y z.
Proof.
intros h x y z H. split; [exact I|].
(* Each decoration above [trv] asks for a nonempty box. *)
assert (Hne : ~ ((exists r, mem r x) /\ (exists t, mem t y))).
{ intros ((r & Hr) & (t & Ht)).
  destruct H as [H|H]; [exact (H r Hr) | exact (H t Ht)]. }
intros [] He; cbn [discriminant]; try lia; exfalso; apply Hne;
  cbn [p2] in He.
- exact He.
- destruct He as (Hx & Hy & _). split; assumption.
- destruct He as (Hx & Hy & _). split; assumption.
Qed.

Lemma strongest2_Dac :
  forall h x y z, p2 Dac h x y z -> ~ p2 Com h x y z -> strongest2 Dac h x y z.
Proof.
intros h x y z Hd Hc. split; [exact Hd|].
intros [] He; cbn [discriminant]; try lia. exfalso. exact (Hc He).
Qed.

Lemma strongest2_Com :
  forall h x y z, p2 Com h x y z -> strongest2 Com h x y z.
Proof.
intros h x y z Hc. split; [exact Hc|].
intros [] _; cbn [discriminant]; lia.
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
intros x y z e Hx Hy He Hz Hc.
destruct (Interval.is_empty x || Interval.is_empty y) eqn:Exy.
- (* The image of an empty box is empty, and so is [z]. *)
  assert (N : (forall r, ~ mem r x) \/ (forall t, ~ mem t y)).
  { apply Bool.orb_true_iff in Exy.
    destruct Exy as [E|E]; [left | right]; intros r; now apply mem_empty. }
  pose proof (no_mem_empty z (proj1 Hz)
    (tightest_no_mem _ _ Hz (image2_empty h x y N))) as Ez.
  rewrite (set_dec_empty_any z e Ez He). cbn [itv dec DecInterval.EMPTY].
  split; [symmetry; exact (valid_empty_eq z (proj1 Hz) Ez)|].
  exists Trv.
  split; [now apply strongest2_Trv | symmetry; now apply dec_min_Trv_l].
- apply Bool.orb_false_iff in Exy. destruct Exy as [Ex Ey].
  destruct (nonempty_mem x Hx Ex) as (r & Hr).
  destruct (nonempty_mem y Hy Ey) as (t & Ht).
  (* [h r t] is in the image, and so in [z]. *)
  assert (Ez : Interval.is_empty z = false).
  { apply (mem_not_empty _ (h r t) (proj1 Hz)).
    apply (proj1 (proj2 Hz)). now apply image2_mem. }
  assert (Hdac : p2 Dac h x y z).
  { apply p2_Dac_continuous; [exists r | exists t]; assumption. }
  destruct (Interval.is_common_interval z) eqn:Cz.
  + rewrite (set_dec_keep z e Ez He (fun _ => Cz)).
    cbn [itv dec DecInterval.new_unchecked]. split; [reflexivity|].
    pose proof (common_bounded z Cz) as Bz.
    destruct (Interval.is_common_interval x && Interval.is_common_interval y)
      eqn:C.
    * (* A bounded box and a bounded [z]. *)
      apply andb_prop in C. destruct C as [Cx Cy].
      exists Com. split; [|symmetry; apply dec_min_Com_l].
      apply strongest2_Com.
      split; [exists r; exact Hr|]. split; [exists t; exact Ht|].
      split; [now apply common_bounded|]. split; [now apply common_bounded|].
      split; [intros r' t' _ _; apply h_continuous | exact Bz].
    * (* An unbounded box: [x] or [y] is not common, so not bounded, as it
         is nonempty. The image is in [z], so it is bounded, and [e] is not
         [com]. *)
      assert (Hnb :
        ~ (bounded (fun r => mem r x) /\ bounded (fun t => mem t y))).
      { intros [Bx By].
        rewrite (bounded_common x Hx Ex Bx), (bounded_common y Hy Ey By) in C.
        discriminate C. }
      assert (Hnc : e <> Com).
      { intros E. apply Hnb, Hc; [exact E | exists r; exact Hr |
          exists t; exact Ht |].
        destruct Bz as (m & Hm). exists m. intros s Hs.
        apply Hm, (proj1 (proj2 Hz)), Hs. }
      exists Dac. split; [|symmetry; now apply dec_min_Dac_l].
      apply strongest2_Dac; [exact Hdac|].
      intros (_ & _ & Bx & By & _). exact (Hnb (conj Bx By)).
  + (* [z] is not common, so not bounded, as it is nonempty. *)
    rewrite (set_dec_lower z e Ez Cz He).
    cbn [itv dec DecInterval.new_unchecked]. split; [reflexivity|].
    exists Dac. split; [|reflexivity].
    apply strongest2_Dac; [exact Hdac|].
    intros (_ & _ & _ & _ & _ & Bz).
    rewrite (bounded_common z (proj1 Hz) Ez Bz) in Cz. discriminate Cz.
Qed.

End Binary.
