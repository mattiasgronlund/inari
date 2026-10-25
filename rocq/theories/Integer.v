(** * [floor] and [ceil] of intervals are tightest and decorated correctly

    [Interval::floor] and [Interval::ceil] return the hull of the image of
    their argument, and [DecInterval::floor] and [DecInterval::ceil]
    decorate it with the minimum of the strongest decoration that holds and
    the decoration of their argument, as IEEE 1788 asks of a tightest
    interval version of a function.

    Both store [[a, b]] as [[-a; b]], negate the first lane to get
    [[a; b]], round both lanes in the same direction, and negate the first
    lane back. As [floor] and [ceil] are nondecreasing, this gives
    [[floor a, floor b]] and [[ceil a, ceil b]], which hold exactly the
    integers in the image, and every real between them. Section [Round]
    proves this once for both, and [Round.v] and [Trunc.v] use it for
    [round], [round_ties_even] and [trunc].

    [floor] is continuous except at the integers, where it jumps from
    below. If [floor a = floor b = n], the restriction of [floor] to
    [[a, b]] is the constant [n], and [floor] is continuous at each point
    of [[a, b]] unless [n] is in it, which is when [a = n]. That is the
    test [x.inf_raw() == y.inf_raw()] in [impl_dec!(floor, ...)].
    Otherwise [[a, b]] contains an integer [n] and a real below it, so the
    restriction of [floor] jumps at [n]. [ceil] jumps from above, so its
    test is on [b] instead. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Ieee1788.

Open Scope R_scope.

(** ** Reals between two bounds *)

(** The reals between [lo] and [hi], where [None] is -inf for [lo] and
    +inf for [hi]. *)
Definition in_bounds (lo hi : option R) (r : R) : Prop :=
  match lo with Some a => a <= r | None => True end /\
  match hi with Some b => r <= b | None => True end.

Definition ordered (lo hi : option R) : Prop :=
  match lo, hi with Some a, Some b => a <= b | _, _ => True end.

Lemma in_bounds_between :
  forall lo hi t u s,
  in_bounds lo hi t -> in_bounds lo hi u -> t <= s <= u -> in_bounds lo hi s.
Proof.
intros [a|] [b|] t u s [Ht1 Ht2] [Hu1 Hu2] Hs; split; cbn in *; trivial; lra.
Qed.

Lemma in_bounds_nonempty :
  forall lo hi, ordered lo hi -> exists r, in_bounds lo hi r.
Proof.
intros [a|] [b|] H.
- exists a. split; [apply Rle_refl | exact H].
- exists a. split; [apply Rle_refl | exact I].
- exists b. split; [exact I | apply Rle_refl].
- exists 0. split; exact I.
Qed.

(** [r] between [a] and [b] is no larger in magnitude than both together. *)
Lemma Rabs_between :
  forall a b r, a <= r <= b -> Rabs r <= Rabs a + Rabs b.
Proof.
intros a b r Hr.
unfold Rabs. destruct (Rcase_abs r), (Rcase_abs a), (Rcase_abs b); lra.
Qed.

(** ** The bounds of an interval *)

(** A float as a bound: [None] if it is infinite. *)
Definition bound (a : f64) : option R :=
  if is_finite a then Some (B2R a) else None.

(** The forms that the bounds [a] and [b] of a nonempty interval take. *)
Definition lower_ok (a : f64) : Prop :=
  is_finite a = true \/ a = B754_infinity true.
Definition upper_ok (b : f64) : Prop :=
  is_finite b = true \/ b = B754_infinity false.

Lemma lower_upper_ok :
  forall a b,
  Bleb a b = true -> a <> B754_infinity false -> b <> B754_infinity true ->
  lower_ok a /\ upper_ok b /\ ordered (bound a) (bound b).
Proof.
intros a b H Ha Hb.
assert (Fab : is_finite a = true -> is_finite b = true -> B2R a <= B2R b).
{ intros Fa Fb. rewrite Bleb_correct in H by assumption.
  revert H. case Rle_bool_spec; [easy | discriminate]. }
unfold lower_ok, upper_ok, ordered, bound.
destruct a as [sa|[|]| |sa ma ea Hea], b as [sb|[|]| |sb mb eb Heb];
  try discriminate; try congruence; try destruct sa; try destruct sb;
  try discriminate; cbn; auto.
Qed.

Lemma Bleb_bounds :
  forall a b,
  lower_ok a -> upper_ok b -> ordered (bound a) (bound b) -> Bleb a b = true.
Proof.
intros a b [Fa| ->] [Fb| ->] H.
- unfold ordered, bound in H. rewrite Fa, Fb in H.
  rewrite Bleb_correct by assumption. now apply Rle_bool_true.
- destruct a as [sa|sa| |sa ma ea Hea]; try discriminate; destruct sa; reflexivity.
- destruct b as [sb|sb| |sb mb eb Heb]; try discriminate; destruct sb; reflexivity.
- reflexivity.
Qed.

(** The lower bound [a] of [x] is [opp (fst (rep x))], the upper bound [b]
    is [snd (rep x)]. *)
Lemma valid_nonempty :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  lower_ok (opp (fst (rep x))) /\ upper_ok (snd (rep x)) /\
  ordered (bound (opp (fst (rep x)))) (bound (snd (rep x))).
Proof.
intros [[x0 x1]] [[Hn _]|(Hle & Ha & Hb)] Hn'; cbn in *; [congruence|].
now apply lower_upper_ok.
Qed.

Lemma valid_bounds :
  forall x,
  lower_ok (opp (fst (rep x))) -> upper_ok (snd (rep x)) ->
  ordered (bound (opp (fst (rep x)))) (bound (snd (rep x))) -> valid x.
Proof.
intros [[x0 x1]] Ha Hb Hab. cbn in *. right.
split; [now apply Bleb_bounds|].
split; intros E; rewrite E in *; destruct Ha as [Ha|Ha], Hb as [Hb|Hb];
  discriminate.
Qed.

Lemma mem_bounds :
  forall x r,
  lower_ok (opp (fst (rep x))) -> upper_ok (snd (rep x)) ->
  (mem r x <-> in_bounds (bound (opp (fst (rep x)))) (bound (snd (rep x))) r).
Proof.
intros x r Ha Hb. unfold mem, in_bounds, bound.
destruct Ha as [Ha| ->], Hb as [Hb| ->]; rewrite ?Ha, ?Hb; cbn;
  [destruct (opp (fst (rep x))), (snd (rep x)) |
   destruct (opp (fst (rep x))) |
   destruct (snd (rep x)) | ];
  try discriminate; tauto.
Qed.

Lemma empty_nan :
  forall x, valid x -> is_nan (fst (rep x)) = true ->
  rep x = (B754_nan, B754_nan).
Proof.
intros [[x0 x1]] [[H0 H1]|(Hle & _)] Hn; cbn in *.
- destruct x0, x1; try discriminate. reflexivity.
- destruct x0; discriminate.
Qed.

Lemma mem_nan :
  forall x r, rep x = (B754_nan, B754_nan) -> ~ mem r x.
Proof.
intros x r E. unfold mem. rewrite E. cbn. tauto.
Qed.

Lemma is_hull_empty :
  forall s, (forall u, ~ s u) -> is_hull s Interval.EMPTY.
Proof.
intros s Hs. split.
- left. split; reflexivity.
- intros r. split.
  + intros [[] _].
  + intros (u & _ & Hu & _). destruct (Hs u Hu).
Qed.

(** IEEE 1788 asks for the computed interval to be bounded for [com], and
    [p] asks it of the image. For a hull, the two are the same. *)
Lemma is_hull_bounded :
  forall s y, is_hull s y -> (bounded s <-> bounded (fun r => mem r y)).
Proof.
intros s y [_ Hy]. split.
- intros (m & Hm). exists (m + m). intros r Hr.
  apply Hy in Hr. destruct Hr as (u & v & Hu & Hv & Huv).
  apply Rle_trans with (Rabs u + Rabs v); [now apply Rabs_between|].
  apply Rplus_le_compat; [apply Hm, Hu | apply Hm, Hv].
- intros (m & Hm). exists m. intros r Hr. apply Hm, Hy.
  exists r, r. split; [exact Hr|]. split; [exact Hr|].
  split; apply Rle_refl.
Qed.

Lemma infinity_eq : infinity = B754_infinity false.
Proof.
exact from_bits_2047.
Qed.

(** [all] of the mask from [lt] is true exactly when both comparisons
    hold. *)
Lemma is_common_interval_lt :
  forall x,
  Interval.is_common_interval x =
    lt (fst (rep x)) infinity && lt (snd (rep x)) infinity.
Proof.
intros x.
unfold Interval.is_common_interval, Generic.all, Generic.bitmask, Generic.lt,
  Generic.splat.
cbn [fst snd].
destruct (lt (fst (rep x)) infinity), (lt (snd (rep x)) infinity); reflexivity.
Qed.

(** An interval with finite bounds is a common interval. *)
Lemma finite_common :
  forall y,
  is_finite (opp (fst (rep y))) = true -> is_finite (snd (rep y)) = true ->
  Interval.is_common_interval y = true.
Proof.
intros y Ha Hb.
rewrite is_common_interval_lt, infinity_eq. unfold lt.
assert (Fa : is_finite (fst (rep y)) = true).
{ unfold opp in Ha. now rewrite is_finite_Bopp in Ha. }
destruct (fst (rep y)) as [s|s| |s m e H]; try discriminate; destruct s;
  (destruct (snd (rep y)) as [s'|s'| |s' m' e' H'];
   try discriminate; destruct s'; reflexivity).
Qed.

(** ** Rounding an interval in one direction *)

(** [round radix2 (FIX_exp 0) rnd] rounds to an integer. *)
Lemma round_FIX_0 :
  forall rnd v, round radix2 (FIX_exp 0) rnd v = IZR (rnd v).
Proof.
intros rnd v. unfold round, F2R, scaled_mantissa, cexp, FIX_exp.
cbn [Fnum Fexp bpow Z.opp]. now rewrite !Rmult_1_r.
Qed.

Section Round.

(** [g] rounds a float to an integer, as [G] rounds a real, and [f]
    rounds both bounds of an interval with [g]. [G] is nondecreasing and
    moves a real by less than 1. *)
Variable g : f64 -> f64.
Variable G : R -> R.
Variable f : Interval -> Interval.

Hypothesis g_finite : forall a, is_finite (g a) = is_finite a.
Hypothesis g_inf : forall s, g (B754_infinity s) = B754_infinity s.
Hypothesis g_nan : g B754_nan = B754_nan.
Hypothesis g_B2R : forall a, B2R (g a) = G (B2R a).
Hypothesis G_le : forall u v, u <= v -> G u <= G v.
Hypothesis G_near : forall t, t - 1 < G t < t + 1.
Hypothesis f_rep :
  forall x, rep (f x) = (opp (g (opp (fst (rep x)))), g (snd (rep x))).

Lemma bound_g : forall a, bound (g a) = option_map G (bound a).
Proof.
intros a. unfold bound. rewrite g_finite.
destruct (is_finite a); [|reflexivity]. cbn. now rewrite g_B2R.
Qed.

Lemma lower_ok_g : forall a, lower_ok a -> lower_ok (g a).
Proof.
intros a [Ha| ->]; [left; now rewrite g_finite | right; apply g_inf].
Qed.

Lemma upper_ok_g : forall b, upper_ok b -> upper_ok (g b).
Proof.
intros b [Hb| ->]; [left; now rewrite g_finite | right; apply g_inf].
Qed.

Lemma lower_f : forall x, opp (fst (rep (f x))) = g (opp (fst (rep x))).
Proof.
intros x. rewrite f_rep. apply Bopp_involutive.
Qed.

Lemma upper_f : forall x, snd (rep (f x)) = g (snd (rep x)).
Proof.
intros x. now rewrite f_rep.
Qed.

Lemma ordered_G :
  forall lo hi, ordered lo hi -> ordered (option_map G lo) (option_map G hi).
Proof.
intros [a|] [b|] H; cbn in *; trivial. now apply G_le.
Qed.

(** The hull of the image of the reals between [lo] and [hi] under [G]. *)
Lemma round_hull :
  forall (X : R -> Prop) lo hi,
  (forall r, X r <-> in_bounds lo hi r) -> ordered lo hi ->
  forall r,
  in_bounds (option_map G lo) (option_map G hi) r <->
  exists u v, (exists t, X t /\ u = G t) /\ (exists t, X t /\ v = G t) /\
    u <= r <= v.
Proof.
intros X lo hi HX Hord r. split.
- intros [Hlo Hhi].
  assert (Hu : exists u, (exists t, X t /\ u = G t) /\ u <= r).
  { destruct lo as [a|].
    - exists (G a). split; [|exact Hlo]. exists a. split; [|reflexivity].
      apply HX. split; [apply Rle_refl|]. destruct hi; [exact Hord | exact I].
    - (* A real below both [r - 1] and [hi]. *)
      set (t := match hi with Some b => Rmin (r - 1) b | None => r - 1 end).
      assert (Ht : t <= r - 1).
      { unfold t. destruct hi; [apply Rmin_l | apply Rle_refl]. }
      exists (G t). split.
      + exists t. split; [|reflexivity]. apply HX. split; [exact I|].
        unfold t. destruct hi; [apply Rmin_r | exact I].
      + generalize (G_near t). lra. }
  assert (Hv : exists v, (exists t, X t /\ v = G t) /\ r <= v).
  { destruct hi as [b|].
    - exists (G b). split; [|exact Hhi]. exists b. split; [|reflexivity].
      apply HX. split; [|apply Rle_refl]. destruct lo; [exact Hord | exact I].
    - (* A real above both [r + 1] and [lo]. *)
      set (t := match lo with Some a => Rmax (r + 1) a | None => r + 1 end).
      assert (Ht : r + 1 <= t).
      { unfold t. destruct lo; [apply Rmax_l | apply Rle_refl]. }
      exists (G t). split.
      + exists t. split; [|reflexivity]. apply HX. split; [|exact I].
        unfold t. destruct lo; [apply Rmax_r | exact I].
      + generalize (G_near t). lra. }
  destruct Hu as (u & Hu & Hur), Hv as (v & Hv & Hrv).
  exists u, v. auto.
- intros (u & v & (t1 & Ht1 & ->) & (t2 & Ht2 & ->) & Hr).
  apply HX in Ht1, Ht2.
  destruct Ht1 as [Ht1 _], Ht2 as [_ Ht2]. split.
  + destruct lo as [a|]; [|exact I]. cbn.
    apply Rle_trans with (G t1); [now apply G_le | apply Hr].
  + destruct hi as [b|]; [|exact I]. cbn.
    apply Rle_trans with (G t2); [apply Hr | now apply G_le].
Qed.

Lemma round_empty :
  forall x, valid x -> is_nan (fst (rep x)) = true ->
  (forall r, ~ mem r x) /\ rep (f x) = (B754_nan, B754_nan).
Proof.
intros x Hx Hn. pose proof (empty_nan x Hx Hn) as E. split.
- intros r. now apply mem_nan.
- rewrite f_rep, E. cbn. now rewrite g_nan.
Qed.

Lemma round_nonempty :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  let lo := bound (opp (fst (rep x))) in
  let hi := bound (snd (rep x)) in
  (forall r, mem r x <-> in_bounds lo hi r) /\ ordered lo hi /\
  valid (f x) /\
  (forall r, mem r (f x) <-> in_bounds (option_map G lo) (option_map G hi) r).
Proof.
intros x Hx Hn lo hi.
destruct (valid_nonempty x Hx Hn) as (Ha & Hb & Hab).
assert (Ha' : lower_ok (opp (fst (rep (f x))))).
{ rewrite lower_f. now apply lower_ok_g. }
assert (Hb' : upper_ok (snd (rep (f x)))).
{ rewrite upper_f. now apply upper_ok_g. }
assert (E : bound (opp (fst (rep (f x)))) = option_map G lo /\
            bound (snd (rep (f x))) = option_map G hi).
{ now rewrite lower_f, upper_f, !bound_g. }
split; [intros r; now apply mem_bounds|].
split; [exact Hab|].
split.
- apply valid_bounds; [exact Ha' | exact Hb'|].
  destruct E as [-> ->]. now apply ordered_G.
- intros r. rewrite mem_bounds by assumption. now destruct E as [-> ->].
Qed.

Theorem round_is_hull :
  forall x, valid x -> is_hull (image G x) (f x).
Proof.
intros x Hx.
destruct (is_nan (fst (rep x))) eqn:Hn.
- destruct (round_empty x Hx Hn) as [Hx' E].
  replace (f x) with Interval.EMPTY by (destruct (f x); cbn in E; now rewrite E).
  apply is_hull_empty. intros u (r & Hr & _). exact (Hx' r Hr).
- destruct (round_nonempty x Hx Hn) as (HX & Hord & Hy & HY).
  split; [exact Hy|].
  intros r. rewrite HY. exact (round_hull (fun r => mem r x) _ _ HX Hord r).
Qed.

(** What [impl_dec] tests on [y = f x]. *)

Lemma round_not_empty :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  Interval.is_empty (f x) = false.
Proof.
intros x Hx Hn. destruct (valid_nonempty x Hx Hn) as ([Ha|Ha] & _).
- unfold Interval.is_empty. rewrite f_rep. cbn [fst]. rewrite is_nan_Bopp.
  destruct (g (opp (fst (rep x)))) eqn:E; try reflexivity.
  rewrite <- g_finite, E in Ha. discriminate.
- unfold Interval.is_empty. rewrite f_rep, Ha, g_inf. reflexivity.
Qed.

Lemma round_singleton :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  Interval.is_singleton (f x) =
    match bound (opp (fst (rep x))), bound (snd (rep x)) with
    | Some a, Some b => Req_bool (G a) (G b)
    | _, _ => false
    end.
Proof.
intros x Hx Hn. destruct (valid_nonempty x Hx Hn) as (Ha & Hb & _).
unfold Interval.is_singleton, Interval.inf_raw, Interval.sup_raw, eq.
rewrite lower_f, upper_f. unfold bound.
destruct Ha as [Ha|Ha], Hb as [Hb|Hb].
- rewrite Ha, Hb, Beqb_correct, !g_B2R by now rewrite g_finite. reflexivity.
- rewrite Ha, Hb, g_inf. cbn.
  rewrite <- g_finite in Ha.
  destruct (g (opp (fst (rep x)))) as [s|s| |s m e H];
    try discriminate; destruct s; reflexivity.
- rewrite Ha, g_inf. cbn.
  rewrite <- g_finite in Hb.
  destruct (g (snd (rep x))) as [s|s| |s m e H];
    try discriminate; destruct s; reflexivity.
- rewrite Ha, Hb, !g_inf. reflexivity.
Qed.

Lemma round_common :
  forall x,
  is_finite (opp (fst (rep x))) = true -> is_finite (snd (rep x)) = true ->
  Interval.is_common_interval (f x) = true.
Proof.
intros x Ha Hb. apply finite_common.
- rewrite lower_f. now rewrite g_finite.
- rewrite upper_f. now rewrite g_finite.
Qed.

(** ** The decorated version *)

Lemma set_dec_empty :
  forall y e, Interval.is_empty y = true -> e <> Ill ->
  DecInterval.set_dec y (dec_min Trv e) = DecInterval.EMPTY.
Proof.
intros y e Hy He. unfold DecInterval.set_dec. rewrite Hy.
destruct e; first [reflexivity | congruence].
Qed.

Lemma set_dec_nonempty :
  forall y d e,
  Interval.is_empty y = false -> d <> Ill -> e <> Ill ->
  (d = Com -> Interval.is_common_interval y = true) ->
  DecInterval.set_dec y (dec_min d e) = DecInterval.new_unchecked y (dec_min d e).
Proof.
intros y d e Hy Hd He Hc. unfold DecInterval.set_dec. rewrite Hy.
destruct d, e; try congruence; try reflexivity.
cbn. now rewrite Hc.
Qed.

Lemma p_Com_Dac : forall h x, p Com h x -> p Dac h x.
Proof.
intros h x (Hne & _ & Hc & _). split; [exact Hne|].
intros r Hr. specialize (Hc r Hr).
intros eps Heps. destruct (Hc eps Heps) as (alp & Halp & H).
exists alp. split; [exact Halp|].
intros s [[_ Hs] Hd]. apply H. split; [split; [exact I | exact Hs] | exact Hd].
Qed.

Lemma strongest_Trv : forall h x, (forall r, ~ mem r x) -> strongest Trv h x.
Proof.
intros h x H. split; [exact I|].
intros [] He; cbn [discriminant]; try lia; exfalso; cbn [p] in He.
- destruct He as (r & Hr). exact (H r Hr).
- destruct He as ((r & Hr) & _). exact (H r Hr).
- destruct He as ((r & Hr) & _). exact (H r Hr).
Qed.

Lemma strongest_Def :
  forall h x, (exists r, mem r x) -> ~ p Dac h x -> strongest Def h x.
Proof.
intros h x Hne Hd. split; [exact Hne|].
intros [] He; cbn [discriminant]; try lia; exfalso.
- now apply Hd.
- now apply Hd, p_Com_Dac.
Qed.

Lemma strongest_Dac :
  forall h x, p Dac h x -> ~ p Com h x -> strongest Dac h x.
Proof.
intros h x Hd Hc. split; [exact Hd|].
intros [] He; cbn [discriminant]; try lia; exfalso. now apply Hc.
Qed.

Lemma strongest_Com : forall h x, p Com h x -> strongest Com h x.
Proof.
intros h x Hc. split; [exact Hc|].
intros [] _; cbn [discriminant]; lia.
Qed.

(** [is_not_com] is the test of [impl_dec], and [D lo hi] the strongest
    decoration of [G] on the reals between [lo] and [hi]. *)
Variable is_not_com : Interval -> Interval -> bool.
Variable D : option R -> option R -> Decoration.

Hypothesis D_test :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  (if Interval.is_singleton (f x) then
     if is_not_com x (f x) then Dac else Com
   else Def) = D (bound (opp (fst (rep x)))) (bound (snd (rep x))).

Hypothesis D_strongest :
  forall x lo hi,
  (forall r, mem r x <-> in_bounds lo hi r) -> ordered lo hi ->
  strongest (D lo hi) G x.

Theorem impl_dec_correct :
  forall x, valid (itv x) ->
  if DecInterval.is_nai x then DecInterval.impl_dec f is_not_com x = x
  else
    is_hull (image G (itv x)) (itv (DecInterval.impl_dec f is_not_com x)) /\
    exists d, strongest d G (itv x) /\
      dec (DecInterval.impl_dec f is_not_com x) = dec_min d (dec x).
Proof.
intros x Hx. unfold DecInterval.impl_dec. cbv zeta.
destruct (DecInterval.is_nai x) eqn:Hnai; [reflexivity|].
assert (Hdx : dec x <> Ill).
{ intros E. unfold DecInterval.is_nai in Hnai. now rewrite E in Hnai. }
destruct (is_nan (fst (rep (itv x)))) eqn:Hn.
- destruct (round_empty (itv x) Hx Hn) as [Hx' E].
  assert (Hy : Interval.is_empty (f (itv x)) = true).
  { unfold Interval.is_empty. now rewrite E. }
  rewrite Hy, set_dec_empty by assumption. split.
  + apply is_hull_empty. intros u (r & Hr & _). exact (Hx' r Hr).
  + exists Trv. split; [now apply strongest_Trv|].
    cbn. destruct (dec x); first [reflexivity | congruence].
- destruct (round_nonempty (itv x) Hx Hn) as (HX & Hord & _).
  rewrite (round_not_empty (itv x) Hx Hn).
  set (d := if Interval.is_singleton (f (itv x)) then
              if is_not_com (itv x) (f (itv x)) then Dac else Com
            else Def).
  assert (Ed : (if negb (Interval.is_singleton (f (itv x))) then Def
                else if is_not_com (itv x) (f (itv x)) then Dac else Com) = d).
  { unfold d. now destruct (Interval.is_singleton (f (itv x))). }
  rewrite Ed.
  assert (Hd : d <> Ill).
  { unfold d. destruct (Interval.is_singleton _), (is_not_com _ _); discriminate. }
  rewrite set_dec_nonempty.
  + split; [now apply round_is_hull|].
    exists d. split; [|reflexivity].
    unfold d. rewrite D_test by assumption. now apply D_strongest.
  + now apply round_not_empty.
  + exact Hd.
  + exact Hdx.
  + intros Hc. unfold d in Hc.
    destruct (Interval.is_singleton (f (itv x))) eqn:Hs; [|discriminate].
    rewrite round_singleton in Hs by assumption.
    destruct (valid_nonempty (itv x) Hx Hn) as (Ha & Hb & _).
    unfold bound in Hs.
    destruct (is_finite (opp (fst (rep (itv x))))) eqn:Fa; [|discriminate].
    destruct (is_finite (snd (rep (itv x)))) eqn:Fb; [|discriminate].
    now apply round_common.
Qed.

End Round.

(** ** Continuity *)

Lemma continue_in_const :
  forall h (X : R -> Prop) c r,
  (forall s, X s -> h s = c) -> X r -> continue_in h X r.
Proof.
intros h X c r Hc Hr eps Heps. exists 1. split; [lra|].
intros s [[Hs _] _]. change (Rabs (h s - h r) < eps).
rewrite (Hc s Hs), (Hc r Hr). replace (c - c) with 0 by ring.
rewrite Rabs_R0. exact Heps.
Qed.

(** ** [floor] *)

Lemma ffloor_finite : forall a, is_finite (ffloor a) = is_finite a.
Proof.
intros a. exact (proj1 (proj2 (Bnearbyint_correct 53 1024 _ mode_DN a))).
Qed.

Lemma ffloor_inf : forall s, ffloor (B754_infinity s) = B754_infinity s.
Proof.
reflexivity.
Qed.

Lemma ffloor_nan : ffloor B754_nan = B754_nan.
Proof.
reflexivity.
Qed.

Lemma ffloor_B2R : forall a, B2R (ffloor a) = Rfloor (B2R a).
Proof.
intros a. unfold ffloor. rewrite (proj1 (Bnearbyint_correct 53 1024 _ mode_DN a)).
apply round_FIX_0.
Qed.

Lemma floor_rep :
  forall x,
  rep (Interval.floor x) =
    (opp (ffloor (opp (fst (rep x)))), ffloor (snd (rep x))).
Proof.
reflexivity.
Qed.

Lemma Rfloor_le : forall u v, u <= v -> Rfloor u <= Rfloor v.
Proof.
intros u v H. apply IZR_le, Zfloor_le, H.
Qed.

Lemma Rfloor_lb : forall u, Rfloor u <= u.
Proof.
intros u. apply Zfloor_lb.
Qed.

Lemma Rfloor_near : forall t, t - 1 < Rfloor t < t + 1.
Proof.
intros t. generalize (Zfloor_lb t) (Zfloor_ub t). unfold Rfloor. lra.
Qed.

Lemma Rfloor_IZR : forall n, Rfloor (IZR n) = IZR n.
Proof.
intros n. unfold Rfloor. now rewrite Zfloor_IZR.
Qed.

Lemma Rfloor_imp : forall n u, IZR n <= u < IZR n + 1 -> Rfloor u = IZR n.
Proof.
intros n u H. unfold Rfloor. rewrite (Zfloor_imp n u); [reflexivity|].
rewrite plus_IZR. exact H.
Qed.

(** [floor] jumps by 1 at the integer [n], so its restriction to [X] is not
    continuous at [n] if [X] has reals arbitrarily close below [n]. *)
Lemma floor_discontinuous :
  forall (X : R -> Prop) n,
  (forall d, 0 < d -> exists s, X s /\ IZR n - d < s < IZR n) ->
  ~ continue_in Rfloor X (IZR n).
Proof.
intros X n HX Hc.
assert (H1 : 1 > 0) by lra.
destruct (Hc 1 H1) as (alp & Halp & H).
assert (Hd : 0 < Rmin alp 1) by (apply Rmin_glb_lt; lra).
destruct (HX (Rmin alp 1) Hd) as (s & Hs & Hs1 & Hs2).
generalize (Rmin_l alp 1) (Rmin_r alp 1). intros Hm1 Hm2.
assert (E : Rfloor s = IZR n - 1).
{ rewrite (Rfloor_imp (n - 1)); rewrite minus_IZR; [reflexivity | lra]. }
assert (Hlt : Rabs (Rfloor s - Rfloor (IZR n)) < 1).
{ apply H. split.
  - split; [exact Hs | intros Heq; lra].
  - change (Rabs (s - IZR n) < alp). rewrite Rabs_left; lra. }
rewrite E, Rfloor_IZR, Rabs_left in Hlt by lra. lra.
Qed.

(** [floor] is constant between two consecutive integers. *)
Lemma floor_continuous :
  forall n r, IZR n < r < IZR n + 1 -> continuity_pt Rfloor r.
Proof.
intros n r Hr eps Heps.
exists (Rmin (r - IZR n) (IZR n + 1 - r)). split.
{ apply Rmin_glb_lt; lra. }
intros s [_ Hs]. change (Rabs (s - r) < Rmin (r - IZR n) (IZR n + 1 - r)) in Hs.
change (Rabs (Rfloor s - Rfloor r) < eps).
generalize (Rmin_l (r - IZR n) (IZR n + 1 - r))
  (Rmin_r (r - IZR n) (IZR n + 1 - r)). intros H1 H2.
apply Rabs_def2 in Hs.
rewrite (Rfloor_imp n s), (Rfloor_imp n r) by lra.
replace (IZR n - IZR n) with 0 by ring. rewrite Rabs_R0. exact Heps.
Qed.

(** The strongest decoration of [floor] on the reals between [lo] and
    [hi], as [impl_dec!(floor, ...)] computes it. *)
Definition floor_dec (lo hi : option R) : Decoration :=
  match lo, hi with
  | Some a, Some b =>
      if Req_bool (Rfloor a) (Rfloor b) then
        if Req_bool a (Rfloor a) then Dac else Com
      else Def
  | _, _ => Def
  end.

(** If [x] contains the integer [n] and a real below it, the restriction of
    [floor] to [x] is not continuous at [n]. *)
Lemma floor_jump :
  forall x lo hi n t,
  (forall r, mem r x <-> in_bounds lo hi r) ->
  in_bounds lo hi t -> in_bounds lo hi (IZR n) -> t < IZR n ->
  ~ p Dac Rfloor x.
Proof.
intros x lo hi n t HX Ht Hn Htn [_ Hc].
apply (floor_discontinuous (fun r => mem r x) n).
- intros d Hd. exists (Rmax t (IZR n - d / 2)). split.
  + apply HX. apply (in_bounds_between lo hi t (IZR n)); [exact Ht | exact Hn |].
    split; [apply Rmax_l | apply Rmax_lub; lra].
  + split.
    * generalize (Rmax_r t (IZR n - d / 2)). lra.
    * apply Rmax_lub_lt; lra.
- apply Hc, HX, Hn.
Qed.

Lemma floor_strongest :
  forall x lo hi,
  (forall r, mem r x <-> in_bounds lo hi r) -> ordered lo hi ->
  strongest (floor_dec lo hi) Rfloor x.
Proof.
intros x lo hi HX Hord.
assert (Hne : exists r, mem r x).
{ destruct (in_bounds_nonempty lo hi Hord) as (r & Hr). exists r. now apply HX. }
unfold floor_dec. destruct lo as [a|], hi as [b|].
- assert (Hfab : Rfloor a <= Rfloor b) by now apply Rfloor_le.
  assert (Hcon : forall r, mem r x -> Rfloor a <= Rfloor r <= Rfloor b).
  { intros r Hr. apply HX in Hr. destruct Hr as [Hr1 Hr2].
    split; now apply Rfloor_le. }
  case Req_bool_spec; intros Hab.
  + case Req_bool_spec; intros Ha.
    * (* [floor] is constant on [x], but jumps at [a = floor a]. *)
      apply strongest_Dac.
      -- split; [exact Hne|]. intros r Hr.
         apply continue_in_const with (c := Rfloor a); [|exact Hr].
         intros s Hs. generalize (Hcon s Hs). lra.
      -- intros (_ & _ & Hc & _).
         apply (floor_discontinuous no_cond (Zfloor a)).
         ++ intros d Hd. exists (IZR (Zfloor a) - d / 2). split; [exact I | lra].
         ++ change (continuity_pt Rfloor (Rfloor a)). rewrite <- Ha.
            apply Hc, HX. split; [apply Rle_refl | exact Hord].
    * (* [floor a < a <= r <= b < floor b + 1 = floor a + 1]. *)
      assert (Ha' : Rfloor a < a).
      { destruct (Rle_lt_or_eq_dec _ _ (Rfloor_lb a)) as [H|H];
          [exact H | now elim Ha]. }
      apply strongest_Com. split; [exact Hne|]. split; [|split].
      -- exists (Rabs a + Rabs b). intros r Hr. apply HX in Hr.
         now apply Rabs_between.
      -- intros r Hr. apply (floor_continuous (Zfloor a)).
         change (IZR (Zfloor a)) with (Rfloor a).
         apply HX in Hr. destruct Hr as [Hr1 Hr2].
         generalize (Rfloor_near b). lra.
      -- exists (Rabs (Rfloor a)). intros s (r & Hr & ->).
         generalize (Hcon r Hr). intros Hr'.
         replace (Rfloor r) with (Rfloor a) by lra. apply Rle_refl.
  + (* [x] contains [floor b] and [a < floor b]. *)
    apply strongest_Def; [exact Hne|].
    assert (Hlt : Rfloor a + 1 <= Rfloor b).
    { unfold Rfloor in *. rewrite <- plus_IZR. apply IZR_le.
      apply le_IZR in Hfab.
      assert (Zfloor a <> Zfloor b) by (intros E; apply Hab; now rewrite E).
      lia. }
    generalize (Rfloor_near a). intros Ha.
    apply (floor_jump x (Some a) (Some b) (Zfloor b) a HX).
    * split; [apply Rle_refl | exact Hord].
    * change (IZR (Zfloor b)) with (Rfloor b).
      split; [lra | apply Rfloor_lb].
    * change (IZR (Zfloor b)) with (Rfloor b). lra.
- (* [x] contains [floor a + 1] and [a < floor a + 1]. *)
  apply strongest_Def; [exact Hne|].
  generalize (Rfloor_near a). intros Ha.
  apply (floor_jump x (Some a) None (Zfloor a + 1) a HX).
  + split; [apply Rle_refl | exact I].
  + split; [|exact I]. rewrite plus_IZR. change (IZR (Zfloor a)) with (Rfloor a).
    lra.
  + rewrite plus_IZR. change (IZR (Zfloor a)) with (Rfloor a). lra.
- (* [x] contains [floor b] and [floor b - 1]. *)
  apply strongest_Def; [exact Hne|].
  generalize (Rfloor_lb b). intros Hb.
  apply (floor_jump x None (Some b) (Zfloor b) (Rfloor b - 1) HX).
  + split; [exact I | lra].
  + split; [exact I | exact Hb].
  + change (IZR (Zfloor b)) with (Rfloor b). lra.
- (* [x] contains [0] and [-1]. *)
  apply strongest_Def; [exact Hne|].
  apply (floor_jump x None None 0 (-1) HX); [split; exact I .. | lra].
Qed.

Lemma floor_test :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  (if Interval.is_singleton (Interval.floor x) then
     if eq (Interval.inf_raw x) (Interval.inf_raw (Interval.floor x))
     then Dac else Com
   else Def) = floor_dec (bound (opp (fst (rep x)))) (bound (snd (rep x))).
Proof.
intros x Hx Hn.
rewrite (round_singleton ffloor Rfloor Interval.floor ffloor_finite ffloor_inf
  ffloor_B2R floor_rep x Hx Hn).
unfold floor_dec, bound.
destruct (is_finite (opp (fst (rep x)))) eqn:Fa; cbv beta iota; [|reflexivity].
destruct (is_finite (snd (rep x))) eqn:Fb; cbv beta iota; [|reflexivity].
destruct (Req_bool (Rfloor (B2R (opp (fst (rep x)))))
  (Rfloor (B2R (snd (rep x))))); [|reflexivity].
unfold Interval.inf_raw, eq.
rewrite (lower_f ffloor Interval.floor floor_rep), Beqb_correct, ffloor_B2R;
  [reflexivity | exact Fa | now rewrite ffloor_finite].
Qed.

(** [Interval::floor] returns the tightest interval that contains the image
    of its argument under [floor]. *)
Theorem floor_correct :
  forall x, valid x -> is_hull (image Rfloor x) (Interval.floor x).
Proof.
exact (round_is_hull ffloor Rfloor Interval.floor ffloor_finite ffloor_inf
  ffloor_nan ffloor_B2R Rfloor_le Rfloor_near floor_rep).
Qed.

(** [DecInterval::floor] returns a NaI unchanged, and otherwise the result of
    [Interval::floor] with the minimum of the strongest decoration of
    [floor] on the interval and the decoration of its argument. *)
Theorem dec_floor_correct :
  forall x, valid (itv x) ->
  if DecInterval.is_nai x then DecInterval.floor x = x
  else
    is_hull (image Rfloor (itv x)) (itv (DecInterval.floor x)) /\
    exists d, strongest d Rfloor (itv x) /\
      dec (DecInterval.floor x) = dec_min d (dec x).
Proof.
exact (impl_dec_correct ffloor Rfloor Interval.floor ffloor_finite ffloor_inf
  ffloor_nan ffloor_B2R Rfloor_le Rfloor_near floor_rep _ floor_dec floor_test
  floor_strongest).
Qed.

(** ** [ceil] *)

Lemma fceil_finite : forall a, is_finite (fceil a) = is_finite a.
Proof.
intros a. exact (proj1 (proj2 (Bnearbyint_correct 53 1024 _ mode_UP a))).
Qed.

Lemma fceil_inf : forall s, fceil (B754_infinity s) = B754_infinity s.
Proof.
reflexivity.
Qed.

Lemma fceil_nan : fceil B754_nan = B754_nan.
Proof.
reflexivity.
Qed.

Lemma fceil_B2R : forall a, B2R (fceil a) = Rceil (B2R a).
Proof.
intros a. unfold fceil. rewrite (proj1 (Bnearbyint_correct 53 1024 _ mode_UP a)).
apply round_FIX_0.
Qed.

Lemma ceil_rep :
  forall x,
  rep (Interval.ceil x) =
    (opp (fceil (opp (fst (rep x)))), fceil (snd (rep x))).
Proof.
reflexivity.
Qed.

Lemma Rceil_le : forall u v, u <= v -> Rceil u <= Rceil v.
Proof.
intros u v H. apply IZR_le, Zceil_le, H.
Qed.

Lemma Rceil_ub : forall u, u <= Rceil u.
Proof.
intros u. apply Zceil_ub.
Qed.

Lemma Rceil_near : forall t, t - 1 < Rceil t < t + 1.
Proof.
intros t. generalize (Zceil_ub t) (Zceil_lb t). unfold Rceil. lra.
Qed.

Lemma Rceil_IZR : forall n, Rceil (IZR n) = IZR n.
Proof.
intros n. unfold Rceil. now rewrite Zceil_IZR.
Qed.

Lemma Rceil_imp : forall n u, IZR n - 1 < u <= IZR n -> Rceil u = IZR n.
Proof.
intros n u H. unfold Rceil. rewrite (Zceil_imp n u); [reflexivity|].
rewrite minus_IZR. exact H.
Qed.

(** [ceil] jumps by 1 at the integer [n], so its restriction to [X] is not
    continuous at [n] if [X] has reals arbitrarily close above [n]. *)
Lemma ceil_discontinuous :
  forall (X : R -> Prop) n,
  (forall d, 0 < d -> exists s, X s /\ IZR n < s < IZR n + d) ->
  ~ continue_in Rceil X (IZR n).
Proof.
intros X n HX Hc.
assert (H1 : 1 > 0) by lra.
destruct (Hc 1 H1) as (alp & Halp & H).
assert (Hd : 0 < Rmin alp 1) by (apply Rmin_glb_lt; lra).
destruct (HX (Rmin alp 1) Hd) as (s & Hs & Hs1 & Hs2).
generalize (Rmin_l alp 1) (Rmin_r alp 1). intros Hm1 Hm2.
assert (E : Rceil s = IZR n + 1).
{ rewrite (Rceil_imp (n + 1)); rewrite plus_IZR; [reflexivity | lra]. }
assert (Hlt : Rabs (Rceil s - Rceil (IZR n)) < 1).
{ apply H. split.
  - split; [exact Hs | intros Heq; lra].
  - change (Rabs (s - IZR n) < alp). rewrite Rabs_pos_eq; lra. }
rewrite E, Rceil_IZR, Rabs_pos_eq in Hlt by lra. lra.
Qed.

(** [ceil] is constant between two consecutive integers. *)
Lemma ceil_continuous :
  forall n r, IZR n - 1 < r < IZR n -> continuity_pt Rceil r.
Proof.
intros n r Hr eps Heps.
exists (Rmin (r - (IZR n - 1)) (IZR n - r)). split.
{ apply Rmin_glb_lt; lra. }
intros s [_ Hs].
change (Rabs (s - r) < Rmin (r - (IZR n - 1)) (IZR n - r)) in Hs.
change (Rabs (Rceil s - Rceil r) < eps).
generalize (Rmin_l (r - (IZR n - 1)) (IZR n - r))
  (Rmin_r (r - (IZR n - 1)) (IZR n - r)). intros H1 H2.
apply Rabs_def2 in Hs.
rewrite (Rceil_imp n s), (Rceil_imp n r) by lra.
replace (IZR n - IZR n) with 0 by ring. rewrite Rabs_R0. exact Heps.
Qed.

(** The strongest decoration of [ceil] on the reals between [lo] and [hi],
    as [impl_dec!(ceil, ...)] computes it. *)
Definition ceil_dec (lo hi : option R) : Decoration :=
  match lo, hi with
  | Some a, Some b =>
      if Req_bool (Rceil a) (Rceil b) then
        if Req_bool b (Rceil b) then Dac else Com
      else Def
  | _, _ => Def
  end.

(** If [x] contains the integer [n] and a real above it, the restriction of
    [ceil] to [x] is not continuous at [n]. *)
Lemma ceil_jump :
  forall x lo hi n t,
  (forall r, mem r x <-> in_bounds lo hi r) ->
  in_bounds lo hi t -> in_bounds lo hi (IZR n) -> IZR n < t ->
  ~ p Dac Rceil x.
Proof.
intros x lo hi n t HX Ht Hn Hnt [_ Hc].
apply (ceil_discontinuous (fun r => mem r x) n).
- intros d Hd. exists (Rmin t (IZR n + d / 2)). split.
  + apply HX. apply (in_bounds_between lo hi (IZR n) t); [exact Hn | exact Ht |].
    split; [apply Rmin_glb; lra | apply Rmin_l].
  + split.
    * apply Rmin_glb_lt; lra.
    * generalize (Rmin_r t (IZR n + d / 2)). lra.
- apply Hc, HX, Hn.
Qed.

Lemma ceil_strongest :
  forall x lo hi,
  (forall r, mem r x <-> in_bounds lo hi r) -> ordered lo hi ->
  strongest (ceil_dec lo hi) Rceil x.
Proof.
intros x lo hi HX Hord.
assert (Hne : exists r, mem r x).
{ destruct (in_bounds_nonempty lo hi Hord) as (r & Hr). exists r. now apply HX. }
unfold ceil_dec. destruct lo as [a|], hi as [b|].
- assert (Hcab : Rceil a <= Rceil b) by now apply Rceil_le.
  assert (Hcon : forall r, mem r x -> Rceil a <= Rceil r <= Rceil b).
  { intros r Hr. apply HX in Hr. destruct Hr as [Hr1 Hr2].
    split; now apply Rceil_le. }
  case Req_bool_spec; intros Hab.
  + case Req_bool_spec; intros Hb.
    * (* [ceil] is constant on [x], but jumps at [b = ceil b]. *)
      apply strongest_Dac.
      -- split; [exact Hne|]. intros r Hr.
         apply continue_in_const with (c := Rceil a); [|exact Hr].
         intros s Hs. generalize (Hcon s Hs). lra.
      -- intros (_ & _ & Hc & _).
         apply (ceil_discontinuous no_cond (Zceil b)).
         ++ intros d Hd. exists (IZR (Zceil b) + d / 2). split; [exact I | lra].
         ++ change (continuity_pt Rceil (Rceil b)). rewrite <- Hb.
            apply Hc, HX. split; [exact Hord | apply Rle_refl].
    * (* [ceil a - 1 = ceil b - 1 < a <= r <= b < ceil b]. *)
      assert (Hb' : b < Rceil b).
      { destruct (Rle_lt_or_eq_dec _ _ (Rceil_ub b)) as [H|H];
          [exact H | now elim Hb]. }
      apply strongest_Com. split; [exact Hne|]. split; [|split].
      -- exists (Rabs a + Rabs b). intros r Hr. apply HX in Hr.
         now apply Rabs_between.
      -- intros r Hr. apply (ceil_continuous (Zceil b)).
         change (IZR (Zceil b)) with (Rceil b).
         apply HX in Hr. destruct Hr as [Hr1 Hr2].
         generalize (Rceil_near a). lra.
      -- exists (Rabs (Rceil a)). intros s (r & Hr & ->).
         generalize (Hcon r Hr). intros Hr'.
         replace (Rceil r) with (Rceil a) by lra. apply Rle_refl.
  + (* [x] contains [ceil a] and [ceil a < b]. *)
    apply strongest_Def; [exact Hne|].
    assert (Hlt : Rceil a + 1 <= Rceil b).
    { unfold Rceil in *. rewrite <- plus_IZR. apply IZR_le.
      apply le_IZR in Hcab.
      assert (Zceil a <> Zceil b) by (intros E; apply Hab; now rewrite E).
      lia. }
    generalize (Rceil_near b). intros Hb.
    apply (ceil_jump x (Some a) (Some b) (Zceil a) b HX).
    * split; [exact Hord | apply Rle_refl].
    * change (IZR (Zceil a)) with (Rceil a).
      split; [apply Rceil_ub | lra].
    * change (IZR (Zceil a)) with (Rceil a). lra.
- (* [x] contains [ceil a] and [ceil a + 1]. *)
  apply strongest_Def; [exact Hne|].
  generalize (Rceil_ub a). intros Ha.
  apply (ceil_jump x (Some a) None (Zceil a) (Rceil a + 1) HX).
  + split; [lra | exact I].
  + split; [exact Ha | exact I].
  + change (IZR (Zceil a)) with (Rceil a). lra.
- (* [x] contains [ceil b - 1] and [b]. *)
  apply strongest_Def; [exact Hne|].
  generalize (Rceil_near b). intros Hb.
  apply (ceil_jump x None (Some b) (Zceil b - 1) b HX).
  + split; [exact I | apply Rle_refl].
  + split; [exact I|]. rewrite minus_IZR.
    change (IZR (Zceil b)) with (Rceil b). lra.
  + rewrite minus_IZR. change (IZR (Zceil b)) with (Rceil b). lra.
- (* [x] contains [0] and [1]. *)
  apply strongest_Def; [exact Hne|].
  apply (ceil_jump x None None 0 1 HX); [split; exact I .. | lra].
Qed.

Lemma ceil_test :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  (if Interval.is_singleton (Interval.ceil x) then
     if eq (Interval.sup_raw x) (Interval.sup_raw (Interval.ceil x))
     then Dac else Com
   else Def) = ceil_dec (bound (opp (fst (rep x)))) (bound (snd (rep x))).
Proof.
intros x Hx Hn.
rewrite (round_singleton fceil Rceil Interval.ceil fceil_finite fceil_inf
  fceil_B2R ceil_rep x Hx Hn).
unfold ceil_dec, bound.
destruct (is_finite (opp (fst (rep x)))) eqn:Fa; cbv beta iota; [|reflexivity].
destruct (is_finite (snd (rep x))) eqn:Fb; cbv beta iota; [|reflexivity].
destruct (Req_bool (Rceil (B2R (opp (fst (rep x)))))
  (Rceil (B2R (snd (rep x))))); [|reflexivity].
unfold Interval.sup_raw, eq.
rewrite (upper_f fceil Interval.ceil ceil_rep), Beqb_correct, fceil_B2R;
  [reflexivity | exact Fb | now rewrite fceil_finite].
Qed.

(** [Interval::ceil] returns the tightest interval that contains the image
    of its argument under [ceil]. *)
Theorem ceil_correct :
  forall x, valid x -> is_hull (image Rceil x) (Interval.ceil x).
Proof.
exact (round_is_hull fceil Rceil Interval.ceil fceil_finite fceil_inf
  fceil_nan fceil_B2R Rceil_le Rceil_near ceil_rep).
Qed.

(** [DecInterval::ceil] returns a NaI unchanged, and otherwise the result of
    [Interval::ceil] with the minimum of the strongest decoration of [ceil]
    on the interval and the decoration of its argument. *)
Theorem dec_ceil_correct :
  forall x, valid (itv x) ->
  if DecInterval.is_nai x then DecInterval.ceil x = x
  else
    is_hull (image Rceil (itv x)) (itv (DecInterval.ceil x)) /\
    exists d, strongest d Rceil (itv x) /\
      dec (DecInterval.ceil x) = dec_min d (dec x).
Proof.
exact (impl_dec_correct fceil Rceil Interval.ceil fceil_finite fceil_inf
  fceil_nan fceil_B2R Rceil_le Rceil_near ceil_rep _ ceil_dec ceil_test
  ceil_strongest).
Qed.
