(** * [-x] of intervals is tightest and decorated correctly

    [-x] of an [Interval] returns the hull of the image of [x] under
    negation, and [-x] of a [DecInterval] decorates it with the minimum of
    the strongest decoration that holds and the decoration of [x], as
    IEEE 1788 asks of a tightest interval version of a function.

    [-x] swaps the lanes of [[-a; b]] into [[b; -a]], which stores
    [[-b, -a]], the image of [[a, b]]. An infinite bound, which only
    [a = -inf] or [b = +inf] can be, gives the bound +inf or -inf on the
    other side, and the empty interval [[NaN; NaN]] stays empty. No lane
    is computed, so no rounding is involved.

    Negation is continuous, and its result is bounded exactly when its
    argument is. As for [abs], the strongest decoration is then [trv] for
    the empty interval, [com] for a nonempty bounded one and [dac] for an
    unbounded one. [DecInterval::neg] returns a NaI unchanged, and
    otherwise calls [set_dec] with the result and the decoration of [x],
    which gives the minimum of the strongest decoration and that of [x] in
    each case. *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer Abs MaxMin DecBinary.

Open Scope R_scope.

(** ** The interval *)

Lemma in_bounds_opp :
  forall lo hi r,
  in_bounds (option_map Ropp hi) (option_map Ropp lo) r <-> in_bounds lo hi (- r).
Proof.
intros [a|] [b|] r; unfold in_bounds; cbn [option_map];
  split; intros [H1 H2]; split; trivial; lra.
Qed.

Lemma ordered_opp :
  forall lo hi, ordered lo hi -> ordered (option_map Ropp hi) (option_map Ropp lo).
Proof.
intros [a|] [b|] H; cbn in *; trivial; lra.
Qed.

(** [-x] is valid, and a real is in it exactly when its negation is in
    [x]. *)
Lemma neg_mem :
  forall x, valid x ->
  valid (Interval.neg x) /\ forall r, mem r (Interval.neg x) <-> mem (- r) x.
Proof.
intros x Hx.
destruct (is_nan (fst (rep x))) eqn:Hn.
- pose proof (empty_nan x Hx Hn) as E.
  assert (E' : rep (Interval.neg x) = (B754_nan, B754_nan)).
  { unfold Interval.neg, Generic.swap. cbn [rep]. now rewrite E. }
  split; [unfold valid; rewrite E'; left; split; reflexivity|].
  intros r. split; intros H;
    [destruct (mem_nan _ r E' H) | destruct (mem_nan _ (- r) E H)].
- destruct (valid_nonempty x Hx Hn) as (Ha & Hb & Hord).
  (* The lower bound of [-x] is [-b], and its upper bound is the first
     lane of [x], [-a]. *)
  assert (Ha' : lower_ok (opp (fst (rep (Interval.neg x))))).
  { exact (lower_ok_lane _ Hb). }
  assert (Hb' : upper_ok (snd (rep (Interval.neg x)))).
  { exact (upper_ok_lane _ Ha). }
  assert (B : bound (opp (fst (rep (Interval.neg x)))) =
                option_map Ropp (bound (snd (rep x))) /\
              bound (snd (rep (Interval.neg x))) =
                option_map Ropp (bound (opp (fst (rep x))))).
  { split; [apply bound_opp | apply bound_opp_opp]. }
  split.
  + apply valid_bounds; [exact Ha' | exact Hb' |].
    rewrite (proj1 B), (proj2 B). now apply ordered_opp.
  + intros r.
    rewrite (mem_bounds _ r Ha' Hb'), (proj1 B), (proj2 B), in_bounds_opp.
    symmetry. exact (mem_bounds x (- r) Ha Hb).
Qed.

(** [-x] returns the tightest interval that contains the image of [x]
    under negation. *)
Theorem neg_correct :
  forall x, valid x -> is_hull (image Ropp x) (Interval.neg x).
Proof.
intros x Hx. destruct (neg_mem x Hx) as (Hv & Hm).
split; [exact Hv|]. intros r. rewrite Hm. split.
- intros Hr.
  assert (Hi : image Ropp x r).
  { exists (- r). split; [exact Hr | now rewrite Ropp_involutive]. }
  exists r, r. split; [exact Hi|]. split; [exact Hi|]. split; apply Rle_refl.
- (* [-r] is between two reals of [x]. *)
  intros (u & v & (u' & Hu & ->) & (v' & Hv' & ->) & Hr).
  apply (mem_between x v' u' (- r) Hx Hv' Hu). lra.
Qed.

(** ** The decorated version *)

(** Negation moves by as much as its argument does. *)
Lemma Ropp_continue_in : forall X r, continue_in Ropp X r.
Proof.
intros X r eps Heps. exists eps. split; [exact Heps|].
intros s [_ Hs]. change (Rabs (s - r) < eps) in Hs.
change (Rabs (- s - - r) < eps).
replace (- s - - r) with (- (s - r)) by ring. now rewrite Rabs_Ropp.
Qed.

(** [-x] of a [DecInterval] decorates it with the decoration that
    IEEE 1788 asks for. *)
Theorem dec_neg_correct :
  forall x, valid (itv x) ->
  if DecInterval.is_nai x then DecInterval.neg x = x
  else
    is_hull (image Ropp (itv x)) (itv (DecInterval.neg x)) /\
    exists d, strongest d Ropp (itv x) /\
      dec (DecInterval.neg x) = dec_min d (dec x).
Proof.
intros x Hx. unfold DecInterval.neg.
destruct (DecInterval.is_nai x) eqn:Hnai; [reflexivity|].
assert (Hdx : dec x <> Ill).
{ intros E. unfold DecInterval.is_nai in Hnai. now rewrite E in Hnai. }
pose proof (neg_correct _ Hx) as Hz.
destruct (neg_mem _ Hx) as (Hv & Hm).
destruct (Interval.is_empty (itv x)) eqn:Ex.
- (* The image of an empty [x] is empty, and so is [-x], for which
     [set_dec] returns [EMPTY]. *)
  assert (N : forall r, ~ mem r (itv x)) by (intros r; now apply mem_empty).
  assert (Ez : Interval.is_empty (Interval.neg (itv x)) = true).
  { apply (no_mem_empty _ Hv). intros r Hr. apply Hm in Hr. exact (N _ Hr). }
  rewrite (set_dec_empty_any _ _ Ez Hdx). cbn [itv dec DecInterval.EMPTY].
  split; [apply is_hull_empty; intros u (r & Hr & _); exact (N r Hr)|].
  exists Trv.
  split; [now apply strongest_Trv | symmetry; now apply dec_min_Trv_l].
- destruct (nonempty_mem _ Hx Ex) as (r & Hr).
  assert (Ez : Interval.is_empty (Interval.neg (itv x)) = false).
  { apply (mem_not_empty _ (- r) Hv). apply Hm. now rewrite Ropp_involutive. }
  assert (Hdac : p Dac Ropp (itv x)).
  { split; [exists r; exact Hr|]. intros s _. apply Ropp_continue_in. }
  destruct (Interval.is_common_interval (Interval.neg (itv x))) eqn:C.
  + (* [-x] is bounded, so the image is, and so is [x]. *)
    rewrite (set_dec_keep _ _ Ez Hdx (fun _ => C)).
    cbn [itv dec DecInterval.new_unchecked].
    split; [exact Hz|]. exists Com. split; [|symmetry; apply dec_min_Com_l].
    destruct (proj2 (is_hull_bounded _ _ Hz) (common_bounded _ C)) as (m & Hb).
    apply strongest_Com. split; [exists r; exact Hr|]. split; [|split].
    * exists m. intros s Hs. rewrite <- Rabs_Ropp. apply Hb.
      exists s. split; [exact Hs | reflexivity].
    * intros s _. exact (Ropp_continue_in no_cond s).
    * exists m. exact Hb.
  + (* [-x] is not common, so not bounded, and neither is the image. *)
    rewrite (set_dec_lower _ _ Ez C Hdx).
    cbn [itv dec DecInterval.new_unchecked].
    split; [exact Hz|]. exists Dac. split; [|reflexivity].
    apply strongest_Dac; [exact Hdac|].
    intros (_ & _ & _ & Bi). apply (is_hull_bounded _ _ Hz) in Bi.
    rewrite (bounded_common _ Hv Ez Bi) in C. discriminate C.
Qed.
