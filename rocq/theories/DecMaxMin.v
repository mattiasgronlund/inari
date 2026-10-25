(** * [max] and [min] of decorated intervals are decorated correctly

    [DecInterval::max] and [DecInterval::min] return a NaI first argument
    unchanged, and otherwise call [set_dec] with the result of
    [Interval::max] or [Interval::min] and the minimum of the decorations
    of the arguments. If the second argument is NaI, that minimum is [ill],
    and [set_dec] returns NaI. [MaxMin.v] proves that the bare result is the
    hull of the image of the box [x × y], and the proofs here use nothing
    else about it.

    Section [Binary] proves the rest once, for any function [h] of two
    reals that is continuous at each point of R² and bounded on bounded
    boxes, and any interval operation [F] whose result is the hull of the
    image under [h]. [set_dec_hull_correct] is the part that does not depend
    on how an operation treats NaI arguments, for other operations to
    reuse. The strongest decoration of [h] on [x × y] is:

    - [trv] if [x] or [y] is empty, as [def] asks for a nonempty box. The
      image is then empty, and so is its hull, for which [set_dec] returns
      [EMPTY], whose [trv] is the minimum of [trv] and the decorations of
      the arguments, as neither is [ill].
    - [com] if [x] and [y] are nonempty and bounded. The image is then
      bounded, and so is its hull, which therefore has finite bounds and is
      common. [set_dec] keeps the minimum of the decorations of the
      arguments, which is also its minimum with [com].
    - [dac] otherwise: [h] is continuous at each point of the box, so its
      restriction to the box is too, but [com] asks for a bounded box. The
      unbounded argument is not [com], see below, so neither is the
      minimum, which [set_dec] then keeps, and which is also its minimum
      with [dac].

    The hull of the image of an unbounded box can be common:
    [max([-inf, 1], [0, 2]) = [0, 2]]. If both arguments were [com],
    [set_dec] would keep [com], where the strongest decoration is [dac]. As
    for [sign], [DecInterval::new], [set_dec] and the other constructors of
    the library make a [DecInterval] [com] only if its interval is common,
    and so bounded, but nothing here proves it, so the theorems take it as a
    hypothesis.

    [max] and [min] are continuous, as they move by no more than their
    arguments do, and bounded on a bounded box by the bound of the box, as
    [max r t] and [min r t] are [r] or [t]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Ieee1788 Integer Sign MaxMin.

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

(** A hull contains its set, and is empty with it. *)
Lemma hull_mem : forall s z u, is_hull s z -> s u -> mem u z.
Proof.
intros s z u [_ Hz] Hu. apply Hz. exists u, u.
split; [exact Hu|]. split; [exact Hu|]. split; apply Rle_refl.
Qed.

Lemma hull_no_mem :
  forall s z, is_hull s z -> (forall u, ~ s u) -> forall r, ~ mem r z.
Proof.
intros s z [_ Hz] Hs r Hr. apply Hz in Hr.
destruct Hr as (u & _ & Hu & _). exact (Hs u Hu).
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
    interval, and otherwise the decoration unchanged, if it is [com] only
    for a common interval. *)
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

(** ** The strongest decoration on a box *)

Lemma strongest2_Trv :
  forall h x y, (forall r, ~ mem r x) \/ (forall t, ~ mem t y) ->
  strongest2 Trv h x y.
Proof.
intros h x y H. split; [exact I|].
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
  forall h x y, p2 Dac h x y -> ~ p2 Com h x y -> strongest2 Dac h x y.
Proof.
intros h x y Hd Hc. split; [exact Hd|].
intros [] He; cbn [discriminant]; try lia. exfalso. exact (Hc He).
Qed.

Lemma strongest2_Com : forall h x y, p2 Com h x y -> strongest2 Com h x y.
Proof.
intros h x y Hc. split; [exact Hc|].
intros [] _; cbn [discriminant]; lia.
Qed.

(** ** A continuous function of two reals *)

Section Binary.

(** [h] is continuous at each point of R² and bounded on each bounded box,
    and [F] returns the hull of the image of a box under [h]. *)
Variable h : R -> R -> R.
Variable F : Interval -> Interval -> Interval.

Hypothesis h_continuous : forall r t, continuity2_pt h r t.
Hypothesis h_bounded :
  forall m, exists k,
  forall r t, Rabs r <= m -> Rabs t <= m -> Rabs (h r t) <= k.
Hypothesis F_hull :
  forall x y, valid x -> valid y -> is_hull (image2 h x y) (F x y).

Lemma image2_bounded :
  forall x y, bounded (fun r => mem r x) -> bounded (fun t => mem t y) ->
  bounded (image2 h x y).
Proof.
intros x y (mx & Hmx) (my & Hmy).
(* [(r, t)] lies in the square of half-side [max(mx, my)]. *)
destruct (h_bounded (Rmax mx my)) as (k & Hk). exists k.
intros s (r & t & Hr & Ht & ->). apply Hk.
- apply Rle_trans with mx; [now apply Hmx | apply Rmax_l].
- apply Rle_trans with my; [now apply Hmy | apply Rmax_r].
Qed.

(** The restriction of [h] to any box is continuous, as [h] is. *)
Lemma p2_Dac_continuous :
  forall x y, (exists r, mem r x) -> (exists t, mem t y) -> p2 Dac h x y.
Proof.
intros x y Hx Hy. split; [exact Hx|]. split; [exact Hy|].
intros r t _ _ eps Heps.
destruct (h_continuous r t eps Heps) as (delta & Hd & H).
exists delta. split; [exact Hd|].
intros r' t' _ _. exact (H r' t' I I).
Qed.

(** If [x] or [y] is empty, so is the hull, which [set_dec] makes
    [EMPTY], decorated [trv]. *)
Lemma hull_empty_correct :
  forall x y e, valid x -> valid y -> e <> Ill ->
  (forall r, ~ mem r x) \/ (forall t, ~ mem t y) ->
  is_hull (image2 h x y) (itv (DecInterval.set_dec (F x y) e)) /\
  exists d, strongest2 d h x y /\
    dec (DecInterval.set_dec (F x y) e) = dec_min d e.
Proof.
intros x y e Hx Hy He N.
pose proof (F_hull x y Hx Hy) as Hz.
pose proof (image2_empty h x y N) as Ns.
rewrite (set_dec_empty_any _ _
  (no_mem_empty _ (proj1 Hz) (hull_no_mem _ _ Hz Ns)) He).
cbn [itv dec DecInterval.EMPTY]. split; [now apply is_hull_empty|].
exists Trv. split; [now apply strongest2_Trv | symmetry; now apply dec_min_Trv_l].
Qed.

(** If [x] and [y] are nonempty, [set_dec] keeps [e], which is its minimum
    with [com] on a bounded box, and with [dac] on an unbounded one, if [e]
    is [com] only when [x] and [y] are common. *)
Lemma hull_nonempty_correct :
  forall x y e, valid x -> valid y -> e <> Ill ->
  (exists r, mem r x) -> (exists t, mem t y) ->
  (e = Com ->
   Interval.is_common_interval x = true /\ Interval.is_common_interval y = true) ->
  is_hull (image2 h x y) (itv (DecInterval.set_dec (F x y) e)) /\
  exists d, strongest2 d h x y /\
    dec (DecInterval.set_dec (F x y) e) = dec_min d e.
Proof.
intros x y e Hx Hy He [r Hr] [t Ht] Hc.
pose proof (F_hull x y Hx Hy) as Hz.
(* [h r t] is in the image, and so in [F x y]. *)
assert (Ez : Interval.is_empty (F x y) = false).
{ apply (mem_not_empty _ (h r t) (proj1 Hz)).
  apply (hull_mem _ _ _ Hz). now apply image2_mem. }
destruct (Interval.is_common_interval x && Interval.is_common_interval y)
  eqn:C.
- (* A bounded box, whose image is bounded, so its hull is common. *)
  apply andb_prop in C. destruct C as [Cx Cy].
  pose proof (common_bounded x Cx) as Bx.
  pose proof (common_bounded y Cy) as By.
  assert (Cz : Interval.is_common_interval (F x y) = true).
  { apply bounded_common; [exact (proj1 Hz) | exact Ez |].
    apply (is_hull_bounded _ _ Hz). now apply image2_bounded. }
  rewrite (set_dec_keep _ _ Ez He (fun _ => Cz)).
  cbn [itv dec DecInterval.new_unchecked].
  split; [exact Hz|]. exists Com.
  split; [|symmetry; apply dec_min_Com_l].
  apply strongest2_Com.
  split; [exists r; exact Hr|]. split; [exists t; exact Ht|].
  split; [exact Bx|]. split; [exact By|].
  split; [intros r' t' _ _; apply h_continuous|].
  now apply image2_bounded.
- (* An unbounded box: [x] or [y] is not common, so not bounded, as it is
     nonempty, and not [com], so neither is [e]. *)
  assert (Hnc : e <> Com).
  { intros E. destruct (Hc E) as [Cx Cy]. rewrite Cx, Cy in C.
    discriminate C. }
  assert (Hnb : ~ (bounded (fun r => mem r x) /\ bounded (fun t => mem t y))).
  { intros [Bx By].
    rewrite (bounded_common x Hx (mem_not_empty x r Hx Hr) Bx),
      (bounded_common y Hy (mem_not_empty y t Hy Ht) By) in C.
    discriminate C. }
  rewrite (set_dec_keep _ _ Ez He (fun E => False_ind _ (Hnc E))).
  cbn [itv dec DecInterval.new_unchecked].
  split; [exact Hz|]. exists Dac.
  split; [|symmetry; now apply dec_min_Dac_l].
  apply strongest2_Dac.
  + apply p2_Dac_continuous; [exists r | exists t]; assumption.
  + intros (_ & _ & Bx & By & _). exact (Hnb (conj Bx By)).
Qed.

(** [set_dec] of the hull and the minimum of the decorations of [x] and
    [y], neither of which is NaI, is decorated as IEEE 1788 asks, if each
    is [com] only when its interval is common. *)
Theorem set_dec_hull_correct :
  forall x y, valid (itv x) -> valid (itv y) ->
  (dec x = Com -> Interval.is_common_interval (itv x) = true) ->
  (dec y = Com -> Interval.is_common_interval (itv y) = true) ->
  dec x <> Ill -> dec y <> Ill ->
  is_hull (image2 h (itv x) (itv y))
    (itv (DecInterval.set_dec (F (itv x) (itv y)) (dec_min (dec x) (dec y)))) /\
  exists d, strongest2 d h (itv x) (itv y) /\
    dec (DecInterval.set_dec (F (itv x) (itv y)) (dec_min (dec x) (dec y))) =
      dec_min d (dec_min (dec x) (dec y)).
Proof.
intros x y Hx Hy Hcx Hcy Hdx Hdy.
assert (He : dec_min (dec x) (dec y) <> Ill) by now apply dec_min_not_Ill.
destruct (Interval.is_empty (itv x)) eqn:Ex.
- apply hull_empty_correct; try assumption.
  left. intros r. now apply mem_empty.
- destruct (Interval.is_empty (itv y)) eqn:Ey.
  + apply hull_empty_correct; try assumption.
    right. intros t. now apply mem_empty.
  + apply hull_nonempty_correct; try assumption;
      [now apply nonempty_mem | now apply nonempty_mem |].
    intros E. apply dec_min_Com in E. destruct E as [E1 E2].
    split; [now apply Hcx | now apply Hcy].
Qed.

(** The decorated version of [F] in the form of [DecInterval::max] and
    [DecInterval::min]: a NaI first argument unchanged, and otherwise
    [set_dec] of the result of [F] and the minimum of the decorations. *)
Definition dec_binary (x y : DecInterval) : DecInterval :=
  if DecInterval.is_nai x then x
  else DecInterval.set_dec (F (itv x) (itv y)) (dec_min (dec x) (dec y)).

Theorem dec_binary_correct :
  forall x y, valid (itv x) -> valid (itv y) ->
  (dec x = Com -> Interval.is_common_interval (itv x) = true) ->
  (dec y = Com -> Interval.is_common_interval (itv y) = true) ->
  if DecInterval.is_nai x then dec_binary x y = x
  else if DecInterval.is_nai y then dec_binary x y = DecInterval.NAI
  else
    is_hull (image2 h (itv x) (itv y)) (itv (dec_binary x y)) /\
    exists d, strongest2 d h (itv x) (itv y) /\
      dec (dec_binary x y) = dec_min d (dec_min (dec x) (dec y)).
Proof.
intros x y Hx Hy Hcx Hcy. unfold dec_binary.
destruct (DecInterval.is_nai x) eqn:Nx; [reflexivity|].
assert (Hdx : dec x <> Ill).
{ intros E. unfold DecInterval.is_nai in Nx. now rewrite E in Nx. }
destruct (DecInterval.is_nai y) eqn:Ny; cbv beta iota.
- (* [dec y] is [ill], and so is the minimum, so [set_dec] returns NaI. *)
  unfold DecInterval.is_nai, dec_eqb in Ny. unfold DecInterval.set_dec.
  destruct (dec x), (dec y); cbn in Ny;
    first [discriminate | now elim Hdx | reflexivity].
- apply set_dec_hull_correct; try assumption.
  intros E. unfold DecInterval.is_nai in Ny. now rewrite E in Ny.
Qed.

End Binary.

(** ** [max] *)

(** [max] moves by no more than its arguments do. *)
Lemma Rmax_continuous : forall r t, continuity2_pt Rmax r t.
Proof.
intros r t eps Heps. exists eps. split; [exact Heps|].
intros r' t' _ _ Hr Ht. apply Rabs_def2 in Hr, Ht.
apply Rabs_def1; unfold Rmax; destruct (Rle_dec r' t'), (Rle_dec r t); lra.
Qed.

(** [max r t] is [r] or [t]. *)
Lemma Rmax_bounded :
  forall m, exists k,
  forall r t, Rabs r <= m -> Rabs t <= m -> Rabs (Rmax r t) <= k.
Proof.
intros m. exists m. intros r t Hr Ht.
unfold Rmax. destruct (Rle_dec r t); assumption.
Qed.

(** [DecInterval::max] returns the tightest interval, decorated with the
    decoration that IEEE 1788 asks for, if each argument is [com] only when
    its interval is common. *)
Theorem dec_max_correct :
  forall x y, valid (itv x) -> valid (itv y) ->
  (dec x = Com -> Interval.is_common_interval (itv x) = true) ->
  (dec y = Com -> Interval.is_common_interval (itv y) = true) ->
  if DecInterval.is_nai x then DecInterval.max x y = x
  else if DecInterval.is_nai y then DecInterval.max x y = DecInterval.NAI
  else
    is_hull (image2 Rmax (itv x) (itv y)) (itv (DecInterval.max x y)) /\
    exists d, strongest2 d Rmax (itv x) (itv y) /\
      dec (DecInterval.max x y) = dec_min d (dec_min (dec x) (dec y)).
Proof.
exact (dec_binary_correct Rmax Interval.max Rmax_continuous Rmax_bounded
  max_correct).
Qed.

(** ** [min] *)

(** [min] moves by no more than its arguments do. *)
Lemma Rmin_continuous : forall r t, continuity2_pt Rmin r t.
Proof.
intros r t eps Heps. exists eps. split; [exact Heps|].
intros r' t' _ _ Hr Ht. apply Rabs_def2 in Hr, Ht.
apply Rabs_def1; unfold Rmin; destruct (Rle_dec r' t'), (Rle_dec r t); lra.
Qed.

(** [min r t] is [r] or [t]. *)
Lemma Rmin_bounded :
  forall m, exists k,
  forall r t, Rabs r <= m -> Rabs t <= m -> Rabs (Rmin r t) <= k.
Proof.
intros m. exists m. intros r t Hr Ht.
unfold Rmin. destruct (Rle_dec r t); assumption.
Qed.

(** [DecInterval::min] does the same for [min]. *)
Theorem dec_min_correct :
  forall x y, valid (itv x) -> valid (itv y) ->
  (dec x = Com -> Interval.is_common_interval (itv x) = true) ->
  (dec y = Com -> Interval.is_common_interval (itv y) = true) ->
  if DecInterval.is_nai x then DecInterval.min x y = x
  else if DecInterval.is_nai y then DecInterval.min x y = DecInterval.NAI
  else
    is_hull (image2 Rmin (itv x) (itv y)) (itv (DecInterval.min x y)) /\
    exists d, strongest2 d Rmin (itv x) (itv y) /\
      dec (DecInterval.min x y) = dec_min d (dec_min (dec x) (dec y)).
Proof.
exact (dec_binary_correct Rmin Interval.min Rmin_continuous Rmin_bounded
  min_correct).
Qed.
