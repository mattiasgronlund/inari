(** * [abs] of intervals is tightest and decorated correctly

    [Interval::classify] is defined on every valid interval,
    [Interval::abs] returns the hull of the image of its argument, and
    [DecInterval::abs] decorates it with the minimum of the strongest
    decoration that holds and the decoration of its argument, as IEEE 1788
    asks of a tightest interval version of a function.

    An [Interval] stores [[a, b]] as [[-a; b]]. [Interval::classify]
    compares both lanes with [0.0] and packs the results into a code whose
    bit 0 is [-a >= 0], bit 1 is [b >= 0], bit 2 is [-a <= 0] and bit 3 is
    [b <= 0]. Every comparison with NaN is false, so the empty interval
    gives 0, the code of [E]. Otherwise each lane is above, below or equal
    to 0, which sets one or both of its bits, and the comparisons depend
    only on the signs of the lanes. Of the nine combinations, six are the
    codes of [M], [N0], [N1], [P0], [P1] and [Z], and the other three have
    [-a <= 0] and [b <= 0] with at least one of them strict, i.e. [a > b],
    which [valid] rules out. So the code is always that of a variant.

    [abs] returns [[a, b]] itself if [0 <= a] ([P0], [P1] and [Z]), as
    [abs] is the identity there; the lanes swapped, [[b; -a]], i.e.
    [[-b, -a]], if [a < 0] and [b <= 0] ([N0] and [N1]), as [abs r = -r]
    there; and [[0.0; max1(-a, b)]], i.e. [[-0, max(-a, b)]], if
    [a < 0 < b] ([M]). In the last case neither lane is NaN or 0, so
    [max1] returns the larger one. Each of the three is the image of
    [[a, b]], and an infinite bound of [x], which only [a = -inf] or
    [b = +inf] can be, gives the upper bound +inf in each case.

    [abs] is continuous, so its restriction to a nonempty [x] is
    continuous, and its image of a bounded [x] is bounded. The strongest
    decoration of a nonempty [x] is then [com] if both bounds of [x] are
    finite, and [dac] otherwise, as [com] asks for a bounded argument. The
    result has finite bounds exactly when [x] does, so [set_dec] keeps the
    decoration of the argument for a bounded [x], and lowers [com] to [dac]
    for an unbounded one. For the empty interval, the strongest decoration
    is [trv], and [set_dec] returns [EMPTY]. In each case, that is the
    minimum of the strongest decoration and that of the argument. Unlike
    [dec_sign_correct], [dec_abs_correct] needs no hypothesis on the
    decoration of the argument. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Ieee1788 Integer Sign.

Open Scope R_scope.

(** ** The classes *)

Lemma classify_empty :
  forall x, rep x = (B754_nan, B754_nan) -> Interval.classify x = Some CE.
Proof.
intros [r] E. cbn [rep] in E. subst r. reflexivity.
Qed.

(** The class of a nonempty interval by the signs of its lanes: [P0], [P1]
    or [Z] if [-a <= 0], [N0] or [N1] if [-a > 0] and [b <= 0], and [M] if
    [-a > 0] and [b > 0]. *)
Lemma classify_signs :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  (le (fst (rep x)) zero = true /\
   (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1 \/
    Interval.classify x = Some CZ)) \/
  (le (fst (rep x)) zero = false /\ le (snd (rep x)) zero = true /\
   (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1)) \/
  (le (fst (rep x)) zero = false /\ le (snd (rep x)) zero = false /\
   Interval.classify x = Some CM).
Proof.
intros [[x0 x1]] [[Hn0 _]|(Hle & _ & _)] Hn; cbn [rep fst snd] in *;
  [congruence|].
(* With the sign of each lane fixed, the comparisons with 0 compute, and
   so do [classify] and [Hle]. The codes that are no class have [-x0 > x1],
   for which [Hle] computes to [false = true]. *)
destruct x0 as [[]|[]| |[] m0 e0 H0], x1 as [[]|[]| |[] m1 e1 H1];
  try discriminate Hn;
  first
    [ left; split; [reflexivity|];
      first [left; reflexivity | right; left; reflexivity |
             right; right; reflexivity]
    | right; left; split; [reflexivity|]; split; [reflexivity|];
      first [left; reflexivity | right; reflexivity]
    | right; right; split; [reflexivity|]; split; reflexivity
    | vm_compute in Hle; discriminate Hle ].
Qed.

(** [Interval::classify] is defined on every valid interval: the code that
    it transmutes is the discriminant of a variant. *)
Theorem classify_defined :
  forall x, valid x -> exists c, Interval.classify x = Some c.
Proof.
intros x Hx. destruct (is_nan (fst (rep x))) eqn:Hn.
- exists CE. exact (classify_empty x (empty_nan x Hx Hn)).
- destruct (classify_signs x Hx Hn)
    as [(_ & [E|[E|E]]) | [(_ & _ & [E|E]) | (_ & _ & E)]];
    eexists; exact E.
Qed.

(** ** The lanes *)

Lemma opp_inf :
  forall v, opp v = B754_infinity true -> v = B754_infinity false.
Proof.
intros v E. rewrite <- (Bopp_involutive _ _ v). unfold opp in E. now rewrite E.
Qed.

Lemma bound_opp : forall v, bound (opp v) = option_map Ropp (bound v).
Proof.
intros v. unfold bound. rewrite is_finite_opp.
destruct (is_finite v); [cbn [option_map]; now rewrite B2R_opp | reflexivity].
Qed.

Lemma bound_opp_opp : forall v, bound v = option_map Ropp (bound (opp v)).
Proof.
intros v. rewrite bound_opp.
destruct (bound v) as [r|];
  [cbn [option_map]; now rewrite Ropp_involutive | reflexivity].
Qed.

(** The lanes of [[b; -a]] are bounds of the right form. *)
Lemma lower_ok_opp : forall v, upper_ok v -> lower_ok (opp v).
Proof.
intros v [Fv| ->]; [left; now rewrite is_finite_opp | right; reflexivity].
Qed.

Lemma upper_ok_opp : forall v, lower_ok (opp v) -> upper_ok v.
Proof.
intros v [Fv|Ev]; [left; now rewrite is_finite_opp in Fv | right; now apply opp_inf].
Qed.

Lemma lower_ok_not_nan : forall v, lower_ok (opp v) -> is_nan v = false.
Proof.
intros v [Fv|Ev].
- rewrite is_finite_opp in Fv. destruct v; first [reflexivity | discriminate Fv].
- now rewrite (opp_inf v Ev).
Qed.

Lemma upper_ok_not_nan : forall v, upper_ok v -> is_nan v = false.
Proof.
intros v [Fv| ->]; [destruct v; first [reflexivity | discriminate Fv] | reflexivity].
Qed.

(** What [le v zero], bit 2 of the code for the first lane and bit 3 for
    the second, says about the bounds. The first lane holds [-a], so
    [-a <= 0] is [0 <= a]. *)
Lemma lower_le_true :
  forall v, lower_ok (opp v) -> le v zero = true ->
  exists a, bound (opp v) = Some a /\ 0 <= a.
Proof.
intros v [Fa|Ea] H.
- exists (B2R (opp v)). split; [now apply bound_finite|].
  rewrite is_finite_opp in Fa. unfold le in H.
  rewrite Bleb_correct in H by first [exact Fa | reflexivity].
  change (B2R zero) with 0 in H. rewrite B2R_opp.
  revert H. case Rle_bool_spec; [intros Hv _; lra | discriminate].
- (* [-a = +inf] is above 0. *)
  rewrite (opp_inf v Ea) in H. vm_compute in H. discriminate H.
Qed.

Lemma lower_le_false :
  forall v, lower_ok (opp v) -> le v zero = false ->
  match bound (opp v) with Some a => a < 0 | None => True end.
Proof.
intros v [Fa|Ea] H.
- rewrite (bound_finite _ Fa), B2R_opp. cbv beta iota.
  rewrite is_finite_opp in Fa. unfold le in H.
  rewrite Bleb_correct in H by first [exact Fa | reflexivity].
  change (B2R zero) with 0 in H.
  revert H. case Rle_bool_spec; [discriminate | intros Hv _; lra].
- rewrite Ea, bound_inf. exact I.
Qed.

Lemma upper_le_true :
  forall v, upper_ok v -> le v zero = true ->
  exists b, bound v = Some b /\ b <= 0.
Proof.
intros v [Fb| ->] H.
- exists (B2R v). split; [now apply bound_finite|].
  unfold le in H. rewrite Bleb_correct in H by first [exact Fb | reflexivity].
  change (B2R zero) with 0 in H.
  revert H. case Rle_bool_spec; [intros Hv _; exact Hv | discriminate].
- (* [b = +inf] is above 0. *)
  vm_compute in H. discriminate H.
Qed.

Lemma upper_le_false :
  forall v, upper_ok v -> le v zero = false ->
  match bound v with Some b => 0 < b | None => True end.
Proof.
intros v [Fb| ->] H.
- rewrite (bound_finite _ Fb). cbv beta iota.
  unfold le in H. rewrite Bleb_correct in H by first [exact Fb | reflexivity].
  change (B2R zero) with 0 in H.
  revert H. case Rle_bool_spec; [discriminate | intros Hv _; exact Hv].
- exact I.
Qed.

(** A lane above 0 is no zero, so [max1] skips its case for two zeros and
    returns the larger lane. *)
Lemma max1_nonzero :
  forall v w, is_nan v = false -> is_nan w = false -> le v zero = false ->
  Generic.max1 v w = if gt v w then v else w.
Proof.
intros v w Nv Nw Hv.
assert (Ev : eq v zero = false).
{ destruct v as [[]|[]| |[] m e H]; first [reflexivity | discriminate Hv]. }
unfold Generic.max1. rewrite Nv, Nw, Ev. reflexivity.
Qed.

(** The bound [max(-a, b)], which is +inf if [a = -inf] or [b = +inf]. *)
Definition max_bound (lo hi : option R) : option R :=
  match lo, hi with Some a, Some b => Some (Rmax (- a) b) | _, _ => None end.

(** The larger of the lanes [-a] and [b] is the upper bound [max(-a, b)]. *)
Lemma max_lane :
  forall v w, lower_ok (opp v) -> upper_ok w ->
  upper_ok (if gt v w then v else w) /\
  bound (if gt v w then v else w) = max_bound (bound (opp v)) (bound w).
Proof.
intros v w [Fa|Ea] [Fb|Eb].
- rewrite (bound_finite _ Fa), (bound_finite _ Fb). cbn [max_bound].
  rewrite B2R_opp, Ropp_involutive. rewrite is_finite_opp in Fa.
  unfold gt. rewrite Bltb_correct by assumption.
  case Rlt_bool_spec; intros H.
  + split; [now left|]. rewrite (bound_finite _ Fa). f_equal.
    symmetry. apply Rmax_left. lra.
  + split; [now left|]. rewrite (bound_finite _ Fb). f_equal.
    symmetry. apply Rmax_right. exact H.
- (* [b = +inf] is the larger lane. *)
  rewrite (bound_finite _ Fa), Eb. rewrite is_finite_opp in Fa.
  assert (G : gt v (B754_infinity false) = false).
  { destruct v; first [discriminate Fa | reflexivity]. }
  rewrite G. split; [now right | reflexivity].
- (* [-a = +inf] is the larger lane. *)
  rewrite Ea, bound_inf, (opp_inf v Ea). cbn [max_bound].
  assert (G : gt (B754_infinity false) w = true).
  { destruct w; first [discriminate Fb | reflexivity]. }
  rewrite G. split; [now right | reflexivity].
- rewrite Ea, bound_inf, (opp_inf v Ea), Eb. split; [now right | reflexivity].
Qed.

(** ** The image *)

(** A set that holds exactly the reals between two bounds holds the reals
    between any two of its elements. *)
Lemma hull_bounds :
  forall (S : R -> Prop) lo hi,
  (forall t, S t <-> in_bounds lo hi t) ->
  forall r, in_bounds lo hi r <-> exists u v, S u /\ S v /\ u <= r <= v.
Proof.
intros S lo hi HS r. split.
- intros Hr. exists r, r. split; [now apply HS|]. split; [now apply HS|].
  split; apply Rle_refl.
- intros (u & v & Hu & Hv & Hr). apply HS in Hu, Hv.
  exact (in_bounds_between lo hi u v r Hu Hv Hr).
Qed.

(** [abs] is the identity on [[a, b]] for [0 <= a]. *)
Lemma image_nonneg :
  forall (X : R -> Prop) a hi,
  (forall r, X r <-> in_bounds (Some a) hi r) -> 0 <= a ->
  forall t, (exists r, X r /\ t = Rabs r) <-> in_bounds (Some a) hi t.
Proof.
intros X a hi HX Ha t. split.
- intros (r & Hr & ->). apply HX in Hr.
  rewrite Rabs_pos_eq; [exact Hr|].
  apply Rle_trans with a; [exact Ha | exact (proj1 Hr)].
- intros Ht. exists t. split; [now apply HX|].
  symmetry. apply Rabs_pos_eq.
  apply Rle_trans with a; [exact Ha | exact (proj1 Ht)].
Qed.

(** [abs r = -r] on [[a, b]] for [b <= 0], whose image is [[-b, -a]]. *)
Lemma image_nonpos :
  forall (X : R -> Prop) lo b,
  (forall r, X r <-> in_bounds lo (Some b) r) -> b <= 0 ->
  forall t,
  (exists r, X r /\ t = Rabs r) <-> in_bounds (Some (- b)) (option_map Ropp lo) t.
Proof.
intros X lo b HX Hb t. split.
- intros (r & Hr & ->). apply HX in Hr. destruct Hr as [Hr1 Hr2].
  assert (Hr : r <= b) by exact Hr2.
  rewrite Rabs_left1 by lra. split; [cbv beta iota; lra|].
  destruct lo as [a|]; [|exact I].
  cbn [option_map]. cbv beta iota in Hr1 |- *. lra.
- intros [Ht1 Ht2]. assert (Ht : - b <= t) by exact Ht1.
  exists (- t). split.
  + apply HX. split; [|cbv beta iota; lra].
    destruct lo as [a|]; [|exact I].
    cbn [option_map] in Ht2. cbv beta iota in Ht2 |- *. lra.
  + rewrite Rabs_Ropp, Rabs_pos_eq by lra. reflexivity.
Qed.

(** The image of [[a, b]] for [a < 0 < b] is [[0, max(-a, b)]]. *)
Lemma image_mixed :
  forall (X : R -> Prop) lo hi,
  (forall r, X r <-> in_bounds lo hi r) ->
  match lo with Some a => a < 0 | None => True end ->
  match hi with Some b => 0 < b | None => True end ->
  forall t,
  (exists r, X r /\ t = Rabs r) <-> in_bounds (Some 0) (max_bound lo hi) t.
Proof.
intros X lo hi HX Hlo Hhi t. split.
- intros (r & Hr & ->). apply HX in Hr. split; [apply Rabs_pos|].
  destruct lo as [a|], hi as [b|]; cbn [max_bound]; [|exact I..].
  cbn [in_bounds] in Hr. destruct Hr as [Hr1 Hr2].
  generalize (Rmax_l (- a) b) (Rmax_r (- a) b). intros H1 H2.
  unfold Rabs. destruct (Rcase_abs r); lra.
- intros Ht. assert (Ht0 : 0 <= t) by exact (proj1 Ht).
  (* [t] itself is in [x] unless it is above [b], and then [-t] is. *)
  assert (Hpos : X t \/ X (- t)).
  { destruct hi as [b|].
    - destruct (Rle_or_lt t b) as [Htb|Htb].
      + left. apply HX. split; [|exact Htb].
        destruct lo as [a|]; [cbv beta iota in Hlo |- *; lra | exact I].
      + right. apply HX. split; [|cbv beta iota in Hhi |- *; lra].
        destruct lo as [a|]; [|exact I].
        destruct Ht as [_ Ht]. cbn [max_bound] in Ht.
        cbv beta iota in Ht |- *. revert Ht.
        (* [t <= max(-a, b)] and [b < t], so [t <= -a]. *)
        unfold Rmax. destruct (Rle_dec (- a) b); lra.
    - left. apply HX. split; [|exact I].
      destruct lo as [a|]; [cbv beta iota in Hlo |- *; lra | exact I]. }
  destruct Hpos as [Hx|Hx]; [exists t | exists (- t)]; split; try exact Hx.
  + symmetry. now apply Rabs_pos_eq.
  + rewrite Rabs_Ropp. symmetry. now apply Rabs_pos_eq.
Qed.

(** ** The result *)

(** Both bounds are finite. *)
Definition both (lo hi : option R) : bool :=
  match lo, hi with Some _, Some _ => true | _, _ => false end.

(** What each class shows of the result [y] of [abs x]: its bounds are of
    the right form and ordered, they are finite exactly when those of [x]
    are, and the reals between them are the image of [x]. *)
Definition abs_ok (x y : Interval) : Prop :=
  lower_ok (opp (fst (rep y))) /\ upper_ok (snd (rep y)) /\
  ordered (bound (opp (fst (rep y)))) (bound (snd (rep y))) /\
  both (bound (opp (fst (rep y)))) (bound (snd (rep y))) =
    both (bound (opp (fst (rep x)))) (bound (snd (rep x))) /\
  forall t,
  image Rabs x t <-> in_bounds (bound (opp (fst (rep y)))) (bound (snd (rep y))) t.

(** [P0], [P1] and [Z]: [0 <= a], and the result is [x]. *)
Lemma abs_ok_nonneg :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  le (fst (rep x)) zero = true -> abs_ok x x.
Proof.
intros x Hx Hn Hl.
destruct (valid_nonempty x Hx Hn) as (Ha & Hb & Hord).
destruct (lower_le_true _ Ha Hl) as (a & Ea & Ha0).
split; [exact Ha|]. split; [exact Hb|]. split; [exact Hord|].
split; [reflexivity|].
assert (HX : forall r, mem r x <-> in_bounds (Some a) (bound (snd (rep x))) r).
{ intros r. rewrite <- Ea. now apply mem_bounds. }
intros t. rewrite Ea. exact (image_nonneg (fun r => mem r x) a _ HX Ha0 t).
Qed.

Lemma swap_bounds :
  forall lo b,
  ordered lo (Some b) ->
  ordered (Some (- b)) (option_map Ropp lo) /\
  both (Some (- b)) (option_map Ropp lo) = both lo (Some b).
Proof.
intros [a|] b H; cbn [ordered option_map both] in *; [|split; trivial].
split; [lra | reflexivity].
Qed.

(** [N0] and [N1]: [a < 0] and [b <= 0], and the result swaps the lanes
    into [[b; -a]], i.e. [[-b, -a]]. Only [b <= 0] matters here. *)
Lemma abs_ok_nonpos :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  le (snd (rep x)) zero = true ->
  abs_ok x {| rep := Generic.swap (rep x) |}.
Proof.
intros x Hx Hn Hl.
destruct (valid_nonempty x Hx Hn) as (Ha & Hb & Hord).
destruct (upper_le_true _ Hb Hl) as (b & Eb & Hb0).
assert (HX : forall r,
          mem r x <-> in_bounds (bound (opp (fst (rep x)))) (Some b) r).
{ intros r. rewrite <- Eb. now apply mem_bounds. }
rewrite Eb in Hord.
destruct (swap_bounds _ _ Hord) as [Hord' Hboth].
unfold abs_ok, Generic.swap. cbn [rep fst snd].
rewrite (bound_opp (snd (rep x))), Eb, (bound_opp_opp (fst (rep x))).
cbn [option_map].
split; [now apply lower_ok_opp|]. split; [now apply upper_ok_opp|].
split; [exact Hord'|]. split; [exact Hboth|].
intros t. exact (image_nonpos (fun r => mem r x) _ b HX Hb0 t).
Qed.

Lemma mixed_bounds :
  forall lo hi,
  match hi with Some b => 0 < b | None => True end ->
  ordered (Some 0) (max_bound lo hi) /\
  both (Some 0) (max_bound lo hi) = both lo hi.
Proof.
intros [a|] [b|] Hb; cbn [ordered max_bound both] in *; split; trivial.
generalize (Rmax_r (- a) b). lra.
Qed.

(** [M]: [a < 0 < b], and the result is [[0.0; max1(-a, b)]], i.e.
    [[-0, max(-a, b)]]. *)
Lemma abs_ok_mixed :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  le (fst (rep x)) zero = false -> le (snd (rep x)) zero = false ->
  abs_ok x
    {| rep := (zero,
               if gt (fst (rep x)) (snd (rep x)) then fst (rep x)
               else snd (rep x)) |}.
Proof.
intros x Hx Hn Hl0 Hl1.
destruct (valid_nonempty x Hx Hn) as (Ha & Hb & Hord).
destruct (max_lane _ _ Ha Hb) as (Hm & Em).
pose proof (lower_le_false _ Ha Hl0) as Hlo.
pose proof (upper_le_false _ Hb Hl1) as Hhi.
destruct (mixed_bounds (bound (opp (fst (rep x)))) _ Hhi) as [Hord' Hboth].
assert (HX : forall r,
          mem r x <->
          in_bounds (bound (opp (fst (rep x)))) (bound (snd (rep x))) r).
{ intros r. now apply mem_bounds. }
unfold abs_ok. cbn [rep fst snd]. rewrite Em.
(* The lower bound of the result is [-0.0], whose value is 0. *)
replace (bound (opp zero)) with (Some 0) by reflexivity.
split; [left; reflexivity|]. split; [exact Hm|].
split; [exact Hord'|]. split; [exact Hboth|].
intros t. exact (image_mixed (fun r => mem r x) _ _ HX Hlo Hhi t).
Qed.

Lemma abs_empty :
  forall x, rep x = (B754_nan, B754_nan) -> Interval.abs x = Some x.
Proof.
intros x E. unfold Interval.abs. now rewrite (classify_empty x E).
Qed.

Lemma abs_nonempty :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  exists y, Interval.abs x = Some y /\ abs_ok x y.
Proof.
intros x Hx Hn. destruct (valid_nonempty x Hx Hn) as (Ha & Hb & _).
destruct (classify_signs x Hx Hn)
  as [(Hl0 & Hc) | [(Hl0 & Hl1 & Hc) | (Hl0 & Hl1 & Hc)]].
- exists x. split; [|now apply abs_ok_nonneg].
  unfold Interval.abs. destruct Hc as [E|[E|E]]; now rewrite E.
- exists {| rep := Generic.swap (rep x) |}. split; [|now apply abs_ok_nonpos].
  unfold Interval.abs. destruct Hc as [E|E]; now rewrite E.
- exists {| rep := (zero,
                    if gt (fst (rep x)) (snd (rep x)) then fst (rep x)
                    else snd (rep x)) |}.
  split; [|now apply abs_ok_mixed].
  unfold Interval.abs. rewrite Hc.
  rewrite <- (max1_nonzero _ _ Hn (upper_ok_not_nan _ Hb) Hl0).
  reflexivity.
Qed.

Lemma abs_hull : forall x y, abs_ok x y -> is_hull (image Rabs x) y.
Proof.
intros x y (Ha & Hb & Hord & _ & Him). split; [now apply valid_bounds|].
intros r. rewrite mem_bounds by assumption. exact (hull_bounds _ _ _ Him r).
Qed.

(** [Interval::abs] returns the tightest interval that contains the image
    of its argument under [abs]. *)
Theorem abs_correct :
  forall x, valid x ->
  exists y, Interval.abs x = Some y /\ is_hull (image Rabs x) y.
Proof.
intros x Hx. destruct (is_nan (fst (rep x))) eqn:Hn.
- (* [E]: [abs] returns the empty interval. *)
  pose proof (empty_nan x Hx Hn) as E.
  exists x. split; [now apply abs_empty|]. split; [exact Hx|].
  intros r. split.
  + intros Hr. destruct (mem_nan x r E Hr).
  + intros (u & v & (t & Ht & _) & _). destruct (mem_nan x t E Ht).
- destruct (abs_nonempty x Hx Hn) as (y & Ey & Hy).
  exists y. split; [exact Ey | now apply abs_hull].
Qed.

(** ** The strongest decoration *)

Lemma Rabs_continue_in : forall X r, continue_in Rabs X r.
Proof.
intros X r eps Heps. destruct (Rcontinuity_abs r eps Heps) as (alp & Halp & H).
exists alp. split; [exact Halp|].
intros s [[_ Hs] Hd]. apply H. split; [split; [exact I | exact Hs] | exact Hd].
Qed.

(** The strongest decoration of [abs] on the reals between [lo] and [hi]. *)
Definition abs_dec (lo hi : option R) : Decoration :=
  if both lo hi then Com else Dac.

Lemma abs_strongest :
  forall x lo hi,
  (forall r, mem r x <-> in_bounds lo hi r) -> ordered lo hi ->
  strongest (abs_dec lo hi) Rabs x.
Proof.
intros x lo hi HX Hord.
assert (Hne : exists r, mem r x).
{ destruct (in_bounds_nonempty lo hi Hord) as (r & Hr). exists r. now apply HX. }
assert (Hdac : p Dac Rabs x).
{ split; [exact Hne|]. intros r _. apply Rabs_continue_in. }
unfold abs_dec. destruct lo as [a|], hi as [b|]; cbn [both].
- (* [x] is bounded, and so is its image. *)
  apply strongest_Com. split; [exact Hne|]. split; [|split].
  + exists (Rabs a + Rabs b). intros r Hr. apply HX in Hr.
    now apply Rabs_between.
  + intros r _. apply Rcontinuity_abs.
  + exists (Rabs a + Rabs b). intros s (r & Hr & ->). rewrite Rabs_Rabsolu.
    apply HX in Hr. now apply Rabs_between.
- apply strongest_Dac; [exact Hdac|].
  intros (_ & Hb & _). exact (unbounded_hi x (Some a) HX Hb).
- apply strongest_Dac; [exact Hdac|].
  intros (_ & Hb & _). exact (unbounded_lo x (Some b) HX Hb).
- apply strongest_Dac; [exact Hdac|].
  intros (_ & Hb & _). exact (unbounded_lo x None HX Hb).
Qed.

(** ** The decorated version *)

(** An interval is common exactly when both of its bounds are finite. *)
Lemma common_bounds :
  forall y, lower_ok (opp (fst (rep y))) -> upper_ok (snd (rep y)) ->
  Interval.is_common_interval y =
    both (bound (opp (fst (rep y)))) (bound (snd (rep y))).
Proof.
intros y [Fa|Ea] Hb; [destruct Hb as [Fb|Eb]|].
- rewrite (finite_common y Fa Fb), (bound_finite _ Fa), (bound_finite _ Fb).
  reflexivity.
- rewrite is_common_interval_lt, infinity_eq, Eb, bound_inf, (bound_finite _ Fa).
  cbn [both]. destruct (lt (fst (rep y)) (B754_infinity false)); reflexivity.
- rewrite Ea, bound_inf, is_common_interval_lt, infinity_eq, (opp_inf _ Ea).
  reflexivity.
Qed.

(** [DecInterval::abs] decorates it with the decoration that IEEE 1788 asks
    for. *)
Theorem dec_abs_correct :
  forall x, valid (itv x) ->
  exists y, DecInterval.abs x = Some y /\
    if DecInterval.is_nai x then y = x
    else
      is_hull (image Rabs (itv x)) (itv y) /\
      exists d, strongest d Rabs (itv x) /\ dec y = dec_min d (dec x).
Proof.
intros x Hx. unfold DecInterval.abs.
destruct (DecInterval.is_nai x) eqn:Hnai; [exists x; split; reflexivity|].
unfold DecInterval.is_nai in Hnai.
destruct (is_nan (fst (rep (itv x)))) eqn:Hn.
- (* [x] is empty, so [abs] returns its interval, and [set_dec] [EMPTY]. *)
  pose proof (empty_nan _ Hx Hn) as E.
  rewrite (abs_empty _ E). cbv beta iota.
  exists DecInterval.EMPTY. split; [|split].
  + f_equal. unfold DecInterval.set_dec, Interval.is_empty.
    now rewrite Hnai, Hn.
  + apply is_hull_empty. intros u (r & Hr & _). exact (mem_nan _ r E Hr).
  + exists Trv. split; [apply strongest_Trv; intros r; exact (mem_nan _ r E)|].
    cbn [dec DecInterval.EMPTY].
    destruct (dec x); first [reflexivity | discriminate Hnai].
- destruct (valid_nonempty (itv x) Hx Hn) as (_ & _ & Hord).
  destruct (abs_nonempty (itv x) Hx Hn) as (y & Ey & Hy).
  rewrite Ey. cbv beta iota.
  set (d := abs_dec (bound (opp (fst (rep (itv x))))) (bound (snd (rep (itv x))))).
  exists (DecInterval.new_unchecked y (dec_min d (dec x))). split; [|split].
  + (* [y] is common exactly when [d] is [com]. *)
    f_equal. pose proof Hy as (Hya & Hyb & _ & Hboth & _).
    unfold DecInterval.set_dec, Interval.is_empty.
    rewrite Hnai, (lower_ok_not_nan _ Hya), (common_bounds y Hya Hyb), Hboth.
    unfold d, abs_dec.
    destruct (both (bound (opp (fst (rep (itv x))))) (bound (snd (rep (itv x))))),
      (dec x); reflexivity.
  + exact (abs_hull _ _ Hy).
  + exists d. split; [|reflexivity].
    apply abs_strongest; [|exact Hord].
    intros r. destruct (valid_nonempty (itv x) Hx Hn) as (Ha & Hb & _).
    now apply mem_bounds.
Qed.
