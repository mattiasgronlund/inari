(** * [round] and [round_ties_even] of intervals are tightest and decorated
    correctly

    [Interval::round] and [Interval::round_ties_even] return the hull of
    the image of their argument, and [DecInterval::round] and
    [DecInterval::round_ties_even] decorate it with the minimum of the
    strongest decoration that holds and the decoration of their argument,
    as IEEE 1788 asks of a tightest interval version of a function.

    Both store [[a, b]] as [[-a; b]] and, unlike [floor] and [ceil], round
    both lanes as they are, without [neg0]. This is right because rounding
    to the nearest integer, with ties away from zero or to even, is odd:
    [round (-a) = -round a]. Flocq proves it for the reals, and it carries
    over to the floats, signed zeros included, as a float rounded to an
    integer keeps the sign of its argument ([Bnearbyint_odd]). The first
    lane then holds [-round a], and the result is [[round a, round b]], as
    if the first lane had been negated, rounded and negated back. Both
    roundings are nondecreasing and move a real by less than 1, so Section
    [Round] of [Integer.v] proves the hull, as it does for [floor] and
    [ceil]. [round_ties_even1], which [round_ties_even] uses on each lane,
    rounds as Flocq's [Bnearbyint mode_NE] does ([RoundTiesEven.v]).

    Both are constant on [(n - 1/2, n + 1/2)] for each integer [n], and
    jump at its ends, the reals halfway between two integers. If
    [round a = round b], the restriction to [[a, b]] is constant, and
    [[a, b]] holds no halfway real other than perhaps [a] or [b], so the
    function is continuous at each point of [[a, b]] unless [a] or [b] is
    halfway. That is the test in [impl_dec!(round, ...)] and
    [impl_dec!(round_ties_even, ...)], and as it computes [|a| - trunc |a|]
    exactly, it is right for every finite bound ([Nearest.v]). Otherwise the
    restriction takes two values on [[a, b]], so it jumps. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Ieee1788 Integer RoundTiesEven Nearest.

Open Scope R_scope.

(** ** Rounding to the nearest integer is odd *)

Lemma is_finite_not_nan : forall a : f64, is_finite a = true -> is_nan a = false.
Proof.
intros [s|s| |s m e H] Ha; try reflexivity. discriminate.
Qed.

(** [Bnearbyint md] is odd if rounding the reals with [md] is: a NaN, a
    zero or an infinity is its own result, and a finite result has the
    sign of its argument. *)
Lemma Bnearbyint_odd :
  forall md,
  (forall v, round radix2 (FIX_exp 0) (round_mode md) (- v) =
     - round radix2 (FIX_exp 0) (round_mode md) v) ->
  forall a : f64, Bnearbyint md (opp a) = opp (Bnearbyint md a).
Proof.
intros md Hmd [s|s| |s m e H]; try reflexivity.
set (a := B754_finite s m e H). unfold opp.
destruct (Bnearbyint_correct 53 1024 _ md a) as (Ra & Fa & Sa).
destruct (Bnearbyint_correct 53 1024 _ md (Bopp a)) as (Ra' & Fa' & Sa').
assert (Fb : is_finite (Bnearbyint md a) = true) by now rewrite Fa.
assert (Fb' : is_finite (Bnearbyint md (Bopp a)) = true)
  by now rewrite Fa', is_finite_Bopp.
apply B2R_Bsign_inj.
- exact Fb'.
- now rewrite is_finite_Bopp.
- rewrite Ra', !B2R_Bopp, Ra. apply Hmd.
- rewrite Sa' by now apply is_finite_not_nan.
  rewrite (Bsign_Bopp _ _ (Bnearbyint md a)), Sa
    by now apply is_finite_not_nan.
  reflexivity.
Qed.

(** ** [round] *)

Lemma fround_finite : forall a, is_finite (fround a) = is_finite a.
Proof.
intros a. exact (proj1 (proj2 (Bnearbyint_correct 53 1024 _ mode_NA a))).
Qed.

Lemma fround_inf : forall s, fround (B754_infinity s) = B754_infinity s.
Proof.
reflexivity.
Qed.

Lemma fround_nan : fround B754_nan = B754_nan.
Proof.
reflexivity.
Qed.

Lemma fround_B2R : forall a, B2R (fround a) = Rround (B2R a).
Proof.
intros a. unfold fround. rewrite (proj1 (Bnearbyint_correct 53 1024 _ mode_NA a)).
apply round_FIX_0.
Qed.

Lemma fround_odd : forall a, fround (opp a) = opp (fround a).
Proof.
exact (Bnearbyint_odd mode_NA (round_NA_opp radix2 (FIX_exp 0))).
Qed.

(** [round] rounds the first lane [-a] to [-round a]. *)
Lemma round_rep :
  forall x,
  rep (Interval.round x) =
    (opp (fround (opp (fst (rep x)))), fround (snd (rep x))).
Proof.
intros x. rewrite fround_odd. unfold opp. rewrite Bopp_involutive.
reflexivity.
Qed.

Lemma round_test :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  (if Interval.is_singleton (Interval.round x) then
     if eq (sub (fabs (Interval.inf_raw x)) (ftrunc (fabs (Interval.inf_raw x))))
          half ||
        eq (sub (fabs (Interval.sup_raw x)) (ftrunc (fabs (Interval.sup_raw x))))
          half
     then Dac else Com
   else Def) =
  nearest_dec (Z.leb 0) (bound (opp (fst (rep x)))) (bound (snd (rep x))).
Proof.
intros x Hx Hn.
rewrite (round_singleton fround Rround Interval.round fround_finite fround_inf
  fround_B2R round_rep x Hx Hn).
unfold nearest_dec, bound.
destruct (is_finite (opp (fst (rep x)))) eqn:Fa; cbv beta iota; [|reflexivity].
destruct (is_finite (snd (rep x))) eqn:Fb; cbv beta iota; [|reflexivity].
unfold Interval.inf_raw, Interval.sup_raw.
rewrite !is_half_test by assumption.
reflexivity.
Qed.

(** [Interval::round] returns the tightest interval that contains the image
    of its argument under [roundTiesToAway]. *)
Theorem round_correct :
  forall x, valid x -> is_hull (image Rround x) (Interval.round x).
Proof.
exact (round_is_hull fround Rround Interval.round fround_finite fround_inf
  fround_nan fround_B2R (Rnearest_le (Z.leb 0)) (Rnearest_near (Z.leb 0))
  round_rep).
Qed.

(** [DecInterval::round] returns a NaI unchanged, and otherwise the result of
    [Interval::round] with the minimum of the strongest decoration of
    [roundTiesToAway] on the interval and the decoration of its argument. *)
Theorem dec_round_correct :
  forall x, valid (itv x) ->
  if DecInterval.is_nai x then DecInterval.round x = x
  else
    is_hull (image Rround (itv x)) (itv (DecInterval.round x)) /\
    exists d, strongest d Rround (itv x) /\
      dec (DecInterval.round x) = dec_min d (dec x).
Proof.
exact (impl_dec_correct fround Rround Interval.round fround_finite fround_inf
  fround_nan fround_B2R (Rnearest_le (Z.leb 0)) (Rnearest_near (Z.leb 0))
  round_rep _ (nearest_dec (Z.leb 0)) round_test
  (nearest_strongest (Z.leb 0))).
Qed.

(** ** [round_ties_even] *)

Lemma round_ties_even1_finite :
  forall a, is_finite (Generic.round_ties_even1 a) = is_finite a.
Proof.
intros a. rewrite round_ties_even1_correct.
exact (proj1 (proj2 (Bnearbyint_correct 53 1024 _ mode_NE a))).
Qed.

Lemma round_ties_even1_inf :
  forall s, Generic.round_ties_even1 (B754_infinity s) = B754_infinity s.
Proof.
intros s. now rewrite round_ties_even1_correct.
Qed.

Lemma round_ties_even1_nan : Generic.round_ties_even1 B754_nan = B754_nan.
Proof.
now rewrite round_ties_even1_correct.
Qed.

Lemma round_ties_even1_B2R :
  forall a, B2R (Generic.round_ties_even1 a) = Rround_ties_even (B2R a).
Proof.
intros a. rewrite round_ties_even1_correct.
rewrite (proj1 (Bnearbyint_correct 53 1024 _ mode_NE a)).
apply round_FIX_0.
Qed.

Lemma round_ties_even1_odd :
  forall a,
  Generic.round_ties_even1 (opp a) = opp (Generic.round_ties_even1 a).
Proof.
intros a. rewrite !round_ties_even1_correct.
exact (Bnearbyint_odd mode_NE (round_NE_opp radix2 (FIX_exp 0)) a).
Qed.

(** [round_ties_even] rounds the first lane [-a] to [-round_ties_even a]. *)
Lemma round_ties_even_rep :
  forall x,
  rep (Interval.round_ties_even x) =
    (opp (Generic.round_ties_even1 (opp (fst (rep x)))),
     Generic.round_ties_even1 (snd (rep x))).
Proof.
intros x. rewrite round_ties_even1_odd. unfold opp. rewrite Bopp_involutive.
reflexivity.
Qed.

Lemma round_ties_even_test :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  (if Interval.is_singleton (Interval.round_ties_even x) then
     if eq (sub (fabs (Interval.inf_raw x)) (ftrunc (fabs (Interval.inf_raw x))))
          half ||
        eq (sub (fabs (Interval.sup_raw x)) (ftrunc (fabs (Interval.sup_raw x))))
          half
     then Dac else Com
   else Def) =
  nearest_dec (fun z => negb (Z.even z))
    (bound (opp (fst (rep x)))) (bound (snd (rep x))).
Proof.
intros x Hx Hn.
rewrite (round_singleton Generic.round_ties_even1 Rround_ties_even
  Interval.round_ties_even round_ties_even1_finite round_ties_even1_inf
  round_ties_even1_B2R round_ties_even_rep x Hx Hn).
unfold nearest_dec, bound.
destruct (is_finite (opp (fst (rep x)))) eqn:Fa; cbv beta iota; [|reflexivity].
destruct (is_finite (snd (rep x))) eqn:Fb; cbv beta iota; [|reflexivity].
unfold Interval.inf_raw, Interval.sup_raw.
rewrite !is_half_test by assumption.
reflexivity.
Qed.

(** [Interval::round_ties_even] returns the tightest interval that contains
    the image of its argument under [roundTiesToEven]. *)
Theorem round_ties_even_correct :
  forall x, valid x ->
  is_hull (image Rround_ties_even x) (Interval.round_ties_even x).
Proof.
exact (round_is_hull Generic.round_ties_even1 Rround_ties_even
  Interval.round_ties_even round_ties_even1_finite round_ties_even1_inf
  round_ties_even1_nan round_ties_even1_B2R
  (Rnearest_le (fun z => negb (Z.even z)))
  (Rnearest_near (fun z => negb (Z.even z))) round_ties_even_rep).
Qed.

(** [DecInterval::round_ties_even] returns a NaI unchanged, and otherwise the
    result of [Interval::round_ties_even] with the minimum of the strongest
    decoration of [roundTiesToEven] on the interval and the decoration of
    its argument. *)
Theorem dec_round_ties_even_correct :
  forall x, valid (itv x) ->
  if DecInterval.is_nai x then DecInterval.round_ties_even x = x
  else
    is_hull (image Rround_ties_even (itv x))
      (itv (DecInterval.round_ties_even x)) /\
    exists d, strongest d Rround_ties_even (itv x) /\
      dec (DecInterval.round_ties_even x) = dec_min d (dec x).
Proof.
exact (impl_dec_correct Generic.round_ties_even1 Rround_ties_even
  Interval.round_ties_even round_ties_even1_finite round_ties_even1_inf
  round_ties_even1_nan round_ties_even1_B2R
  (Rnearest_le (fun z => negb (Z.even z)))
  (Rnearest_near (fun z => negb (Z.even z))) round_ties_even_rep _
  (nearest_dec (fun z => negb (Z.even z))) round_ties_even_test
  (nearest_strongest (fun z => negb (Z.even z)))).
Qed.
