(** * Rounding to the nearest integer: where it jumps, and the test for it

    [round] and [round_ties_even] both round to the nearest integer and
    differ only in where a tie goes. Flocq's [Znearest choice] sends a tie
    up or down as [choice] says, so Section [Nearest] proves what both need
    once, for any [choice].

    [Rnearest] is nondecreasing and constant on each [(n - 1/2, n + 1/2)],
    so it is continuous except at the half-integers [n + 1/2]. It jumps at
    each of them, whichever way the tie goes: the value there is [n] or
    [n + 1], while the reals just below round to [n] and those just above
    to [n + 1]. If [Rnearest a = Rnearest b], [Rnearest] is constant on
    [[a, b]], so its restriction is continuous, no half-integer lies
    strictly between [a] and [b], and [Rnearest] is continuous at each point
    of [[a, b]] unless [a] or [b] is a half-integer. That is the test in
    [impl_dec!(round, ...)] and [impl_dec!(round_ties_even, ...)].
    Otherwise [h = Rnearest a + 1/2] lies in [[a, b]], and so do the reals
    next to [h] on the side that [h] does not round to, so the restriction
    jumps at [h]. An unbounded interval holds a half-integer and reals on
    both sides of it.

    The Rust code tests [r] for a half-integer with
    [abs_a - abs_a.trunc() == 0.5], where [abs_a = |r|]. The subtraction
    is exact, so the test computes [is_half] ([is_half_test]): if [|r| < 1]
    then [trunc |r| = 0], and otherwise [|r| / 2 <= trunc |r| <= |r|] and
    Sterbenz's lemma (P. H. Sterbenz, Floating-point computation, 1974)
    applies. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Sterbenz.
From Inari Require Import Model Encoding Ieee1788 Integer.

Open Scope R_scope.

(** [r] is halfway between two integers: [|r| - trunc |r| = 1/2]. *)
Definition is_half (r : R) : bool :=
  Req_bool (Rabs r - IZR (Ztrunc (Rabs r))) (/ 2).

Lemma is_half_spec : forall r, is_half r = true <-> exists n, r = IZR n + / 2.
Proof.
intros r. unfold is_half. rewrite Ztrunc_floor by apply Rabs_pos. split.
- case Req_bool_spec; [intros H _ | discriminate].
  destruct (Rle_or_lt 0 r) as [Hr|Hr].
  + rewrite Rabs_pos_eq in H by exact Hr. exists (Zfloor r). lra.
  + (* [r = -(k + 1/2) = (-k - 1) + 1/2] with [k = floor (-r)]. *)
    rewrite Rabs_left in H by exact Hr. exists (- Zfloor (- r) - 1)%Z.
    rewrite minus_IZR, opp_IZR. lra.
- intros (n & ->). apply Req_bool_true.
  destruct (Z_lt_le_dec n 0) as [Hn|Hn].
  + assert (Hn' : IZR n <= -1) by (apply IZR_le; lia).
    rewrite Rabs_left by lra.
    rewrite (Zfloor_imp (- n - 1)).
    * rewrite minus_IZR, opp_IZR. lra.
    * rewrite plus_IZR, minus_IZR, opp_IZR. lra.
  + assert (Hn' : 0 <= IZR n) by (apply IZR_le; exact Hn).
    rewrite Rabs_pos_eq by lra.
    rewrite (Zfloor_imp n); [lra|]. rewrite plus_IZR. lra.
Qed.

Lemma half_B2R : is_finite half = true /\ B2R half = / 2.
Proof.
split; [vm_compute; reflexivity|].
rewrite <- SF2R_B2SF.
replace (B2SF half) with (SpecFloat.S754_finite false 4503599627370496 (-53))
  by (vm_compute; reflexivity).
unfold SF2R, F2R. cbn [Fnum Fexp SpecFloat.cond_Zopp].
change (bpow radix2 (-53)) with (/ 9007199254740992).
lra.
Qed.

(** The test in [impl_dec!(round, ...)] computes [is_half] exactly. *)
Lemma is_half_test :
  forall a, is_finite a = true ->
  eq (sub (fabs a) (ftrunc (fabs a))) half = is_half (B2R a).
Proof.
intros a Fa.
assert (FA : is_finite (fabs a) = true)
  by (unfold fabs; rewrite is_finite_Babs; exact Fa).
assert (RA : B2R (fabs a) = Rabs (B2R a)) by apply B2R_Babs.
assert (FT : is_finite (ftrunc (fabs a)) = true).
{ unfold ftrunc.
  rewrite (proj1 (proj2 (Bnearbyint_correct 53 1024 _ mode_ZR (fabs a)))).
  exact FA. }
assert (RT : B2R (ftrunc (fabs a)) = IZR (Ztrunc (Rabs (B2R a)))).
{ unfold ftrunc. rewrite (proj1 (Bnearbyint_correct 53 1024 _ mode_ZR (fabs a))).
  rewrite round_FIX_0, RA. reflexivity. }
assert (Ht : IZR (Ztrunc (Rabs (B2R a))) <= Rabs (B2R a) <
             IZR (Ztrunc (Rabs (B2R a))) + 1).
{ rewrite Ztrunc_floor by apply Rabs_pos. split; [apply Zfloor_lb | apply Zfloor_ub]. }
(* [|a| - trunc |a|] is a float. *)
assert (Fd : generic_format radix2 fexp64 (B2R (fabs a) - B2R (ftrunc (fabs a)))).
{ destruct (Rlt_or_le (Rabs (B2R a)) 1) as [H1|H1].
  - (* [trunc |a| = 0] *)
    assert (Z0 : Ztrunc (Rabs (B2R a)) = 0%Z).
    { rewrite Ztrunc_floor by apply Rabs_pos. apply Zfloor_imp.
      rewrite plus_IZR. generalize (Rabs_pos (B2R a)). lra. }
    rewrite RT, Z0. replace (B2R (fabs a) - IZR 0) with (B2R (fabs a)) by ring.
    apply generic_format_B2R.
  - (* [1 <= trunc |a| <= |a| < trunc |a| + 1], so Sterbenz's lemma applies. *)
    assert (H1' : 1 <= IZR (Ztrunc (Rabs (B2R a)))).
    { apply (IZR_le 1). rewrite Ztrunc_floor by apply Rabs_pos.
      rewrite <- (Zfloor_IZR 1). apply Zfloor_le. exact H1. }
    apply sterbenz; [typeclasses eauto .. | apply generic_format_B2R
      | apply generic_format_B2R | rewrite RA, RT; lra]. }
generalize (@Bminus_correct 53 1024 _ _ mode_NE (fabs a) (ftrunc (fabs a)) FA FT).
change (SpecFloat.fexp 53 1024) with fexp64.
rewrite (round_generic radix2 fexp64 (round_mode mode_NE) _ Fd).
rewrite Rlt_bool_true.
2: { rewrite RA, RT, Rabs_pos_eq by lra.
     apply Rlt_le_trans with 1; [lra|].
     change 1 with (bpow radix2 0). apply bpow_le. lia. }
intros (Hs & Fs & _).
destruct half_B2R as (Fh & Hh).
unfold eq, sub. rewrite Beqb_correct by assumption.
rewrite Hs, Hh, RA, RT. reflexivity.
Qed.

(** A function that takes the value [c] at reals of [X] arbitrarily close
    to [h], and differs from [c] by at least 1 at [h], is not continuous at
    [h] on [X]. *)
Lemma jump_discontinuous :
  forall (f : R -> R) (X : R -> Prop) h c,
  1 <= Rabs (c - f h) ->
  (forall d, 0 < d -> exists s, X s /\ s <> h /\ Rabs (s - h) < d /\ f s = c) ->
  ~ continue_in f X h.
Proof.
intros f X h c Hc Hs Hcont.
assert (H1 : 1 > 0) by lra.
destruct (Hcont 1 H1) as (alp & Halp & H).
destruct (Hs alp Halp) as (s & HXs & Hsh & Hd & Ef).
assert (Hlt : Rabs (f s - f h) < 1).
{ apply H. split; [split; [exact HXs | intros E; apply Hsh; now rewrite E] |].
  exact Hd. }
rewrite Ef in Hlt. lra.
Qed.

Section Nearest.

(** [Rround] is [Rnearest (Zle_bool 0)] and [Rround_ties_even] is
    [Rnearest (fun z => negb (Z.even z))]. *)
Variable choice : Z -> bool.

Definition Rnearest (r : R) : R := IZR (Znearest choice r).

Lemma Rnearest_le : forall u v, u <= v -> Rnearest u <= Rnearest v.
Proof.
intros u v H. apply IZR_le. exact (@Zrnd_le _ (valid_rnd_N choice) u v H).
Qed.

Lemma Rnearest_half : forall t, Rnearest t - / 2 <= t <= Rnearest t + / 2.
Proof.
intros t. generalize (Znearest_half choice t). unfold Rnearest. intros H.
apply Rabs_le_inv in H. lra.
Qed.

Lemma Rnearest_near : forall t, t - 1 < Rnearest t < t + 1.
Proof.
intros t. generalize (Rnearest_half t). lra.
Qed.

Lemma Rnearest_imp :
  forall n u, IZR n - / 2 < u < IZR n + / 2 -> Rnearest u = IZR n.
Proof.
intros n u Hu. unfold Rnearest. rewrite (Znearest_imp choice u n); [reflexivity|].
apply Rabs_def1; lra.
Qed.

(** A tie goes to one of the two integers next to it. *)
Lemma Rnearest_at_half :
  forall n, Rnearest (IZR n + / 2) = IZR n \/ Rnearest (IZR n + / 2) = IZR n + 1.
Proof.
intros n. generalize (Rnearest_half (IZR n + / 2)). unfold Rnearest. intros H.
assert (H1 : (n <= Znearest choice (IZR n + / 2))%Z) by (apply le_IZR; lra).
assert (H2 : (Znearest choice (IZR n + / 2) <= n + 1)%Z)
  by (apply le_IZR; rewrite plus_IZR; lra).
destruct (Z.eq_dec (Znearest choice (IZR n + / 2)) n) as [E|E].
- left. now rewrite E.
- right. rewrite <- plus_IZR. f_equal. lia.
Qed.

(** The reals just above [n + 1/2] round to [n + 1]. *)
Lemma near_half_right :
  forall n t d, IZR n + / 2 < t -> 0 < d ->
  exists s, IZR n + / 2 < s <= t /\ s - (IZR n + / 2) < d /\
    Rnearest s = IZR n + 1.
Proof.
intros n t d Ht Hd.
assert (He : 0 < Rmin d (/ 2)) by (apply Rmin_glb_lt; lra).
generalize (Rmin_l d (/ 2)) (Rmin_r d (/ 2)).
set (e := Rmin d (/ 2)) in *. intros He1 He2.
exists (Rmin t (IZR n + / 2 + e / 2)).
generalize (Rmin_l t (IZR n + / 2 + e / 2)) (Rmin_r t (IZR n + / 2 + e / 2)).
intros H1 H2.
assert (H3 : IZR n + / 2 < Rmin t (IZR n + / 2 + e / 2))
  by (apply Rmin_glb_lt; lra).
split; [lra|]. split; [lra|].
rewrite <- plus_IZR. apply Rnearest_imp. rewrite plus_IZR. lra.
Qed.

(** The reals just below [n + 1/2] round to [n]. *)
Lemma near_half_left :
  forall n t d, t < IZR n + / 2 -> 0 < d ->
  exists s, t <= s < IZR n + / 2 /\ IZR n + / 2 - s < d /\ Rnearest s = IZR n.
Proof.
intros n t d Ht Hd.
assert (He : 0 < Rmin d (/ 2)) by (apply Rmin_glb_lt; lra).
generalize (Rmin_l d (/ 2)) (Rmin_r d (/ 2)).
set (e := Rmin d (/ 2)) in *. intros He1 He2.
exists (Rmax t (IZR n + / 2 - e / 2)).
generalize (Rmax_l t (IZR n + / 2 - e / 2)) (Rmax_r t (IZR n + / 2 - e / 2)).
intros H1 H2.
assert (H3 : Rmax t (IZR n + / 2 - e / 2) < IZR n + / 2)
  by (apply Rmax_lub_lt; lra).
split; [lra|]. split; [lra|].
apply Rnearest_imp. lra.
Qed.

(** Away from the half-integers, [Rnearest] moves a real by less than 1/2. *)
Lemma nearest_strict :
  forall r, is_half r = false -> Rnearest r - / 2 < r < Rnearest r + / 2.
Proof.
intros r Hr. destruct (Rnearest_half r) as [H1 H2]. split.
- destruct (Rle_lt_or_eq_dec _ _ H1) as [H|H]; [exact H|].
  assert (E : is_half r = true).
  { apply is_half_spec. exists (Znearest choice r - 1)%Z.
    rewrite minus_IZR. unfold Rnearest in H. lra. }
  congruence.
- destruct (Rle_lt_or_eq_dec _ _ H2) as [H|H]; [exact H|].
  assert (E : is_half r = true).
  { apply is_half_spec. exists (Znearest choice r).
    unfold Rnearest in H. lra. }
  congruence.
Qed.

(** [Rnearest] is constant around a real that is not a half-integer. *)
Lemma nearest_continuous :
  forall r, is_half r = false -> continuity_pt Rnearest r.
Proof.
intros r Hr eps Heps. destruct (nearest_strict r Hr) as [H1 H2].
exists (Rmin (r - (Rnearest r - / 2)) (Rnearest r + / 2 - r)). split.
{ apply Rmin_glb_lt; lra. }
intros s [_ Hs].
change (Rabs (s - r) < Rmin (r - (Rnearest r - / 2)) (Rnearest r + / 2 - r)) in Hs.
change (Rabs (Rnearest s - Rnearest r) < eps).
generalize (Rmin_l (r - (Rnearest r - / 2)) (Rnearest r + / 2 - r))
  (Rmin_r (r - (Rnearest r - / 2)) (Rnearest r + / 2 - r)). intros H3 H4.
apply Rabs_def2 in Hs.
rewrite (Rnearest_imp (Znearest choice r) s) by (unfold Rnearest in *; lra).
change (IZR (Znearest choice r)) with (Rnearest r).
replace (Rnearest r - Rnearest r) with 0 by ring. rewrite Rabs_R0. exact Heps.
Qed.

(** [Rnearest] jumps at each half-integer, whichever way the tie goes. *)
Lemma nearest_discontinuous :
  forall r, is_half r = true -> ~ continuity_pt Rnearest r.
Proof.
intros r Hr. apply is_half_spec in Hr. destruct Hr as (n & ->).
destruct (Rnearest_at_half n) as [E|E].
- apply (jump_discontinuous Rnearest no_cond _ (IZR n + 1)).
  + rewrite E, Rabs_pos_eq by lra. lra.
  + intros d Hd.
    assert (Ht : IZR n + / 2 < IZR n + / 2 + 1) by lra.
    destruct (near_half_right n _ d Ht Hd) as (s & Hs & Hds & Es).
    exists s. split; [exact I|]. split; [intros Es'; lra|].
    split; [rewrite Rabs_pos_eq; lra | exact Es].
- apply (jump_discontinuous Rnearest no_cond _ (IZR n)).
  + rewrite E, Rabs_left by lra. lra.
  + intros d Hd.
    assert (Ht : IZR n + / 2 - 1 < IZR n + / 2) by lra.
    destruct (near_half_left n _ d Ht Hd) as (s & Hs & Hds & Es).
    exists s. split; [exact I|]. split; [intros Es'; lra|].
    split; [rewrite Rabs_left; lra | exact Es].
Qed.

(** No half-integer lies strictly between two reals that round to the same
    integer. *)
Lemma nearest_inside :
  forall a b r, a < r < b -> Rnearest a = Rnearest b -> is_half r = false.
Proof.
intros a b r Hr Hab.
destruct (is_half r) eqn:H; [exfalso | reflexivity].
apply is_half_spec in H. destruct H as (n & ->).
assert (H1 : 0 < 1) by lra.
assert (Ha : a < IZR n + / 2) by lra.
assert (Hb : IZR n + / 2 < b) by lra.
destruct (near_half_left n a 1 Ha H1) as (s & Hs & _ & Es).
destruct (near_half_right n b 1 Hb H1) as (s' & Hs' & _ & Es').
generalize (Rnearest_le a s (proj1 Hs)) (Rnearest_le s' b (proj2 Hs')). lra.
Qed.

(** The strongest decoration of [Rnearest] on the reals between [lo] and
    [hi], as [impl_dec!(round, ...)] computes it. *)
Definition nearest_dec (lo hi : option R) : Decoration :=
  match lo, hi with
  | Some a, Some b =>
      if Req_bool (Rnearest a) (Rnearest b) then
        if is_half a || is_half b then Dac else Com
      else Def
  | _, _ => Def
  end.

(** If [x] contains the half-integer [h = n + 1/2] and a real on the side of
    [h] that [h] does not round to, the restriction of [Rnearest] to [x] is
    not continuous at [h]. *)
Lemma nearest_jump :
  forall x lo hi n,
  (forall r, mem r x <-> in_bounds lo hi r) ->
  in_bounds lo hi (IZR n + / 2) ->
  (Rnearest (IZR n + / 2) = IZR n ->
   exists t, in_bounds lo hi t /\ IZR n + / 2 < t) ->
  (Rnearest (IZR n + / 2) = IZR n + 1 ->
   exists t, in_bounds lo hi t /\ t < IZR n + / 2) ->
  ~ p Dac Rnearest x.
Proof.
intros x lo hi n HX Hh Hr Hl [_ Hc].
assert (Hch : continue_in Rnearest (fun r => mem r x) (IZR n + / 2))
  by apply Hc, HX, Hh.
destruct (Rnearest_at_half n) as [E|E].
- destruct (Hr E) as (t & Ht & Hht).
  apply (jump_discontinuous Rnearest (fun r => mem r x) (IZR n + / 2) (IZR n + 1));
    [| | exact Hch].
  + rewrite E, Rabs_pos_eq by lra. lra.
  + intros d Hd. destruct (near_half_right n t d Hht Hd) as (s & Hs & Hds & Es).
    exists s. split.
    * apply HX. apply (in_bounds_between lo hi (IZR n + / 2) t);
        [exact Hh | exact Ht | lra].
    * split; [intros Es'; lra|].
      split; [rewrite Rabs_pos_eq; lra | exact Es].
- destruct (Hl E) as (t & Ht & Hht).
  apply (jump_discontinuous Rnearest (fun r => mem r x) (IZR n + / 2) (IZR n));
    [| | exact Hch].
  + rewrite E, Rabs_left by lra. lra.
  + intros d Hd. destruct (near_half_left n t d Hht Hd) as (s & Hs & Hds & Es).
    exists s. split.
    * apply HX. apply (in_bounds_between lo hi t (IZR n + / 2));
        [exact Ht | exact Hh | lra].
    * split; [intros Es'; lra|].
      split; [rewrite Rabs_left; lra | exact Es].
Qed.

Lemma nearest_strongest :
  forall x lo hi,
  (forall r, mem r x <-> in_bounds lo hi r) -> ordered lo hi ->
  strongest (nearest_dec lo hi) Rnearest x.
Proof.
intros x lo hi HX Hord.
assert (Hne : exists r, mem r x).
{ destruct (in_bounds_nonempty lo hi Hord) as (r & Hr). exists r. now apply HX. }
unfold nearest_dec. destruct lo as [a|], hi as [b|].
- assert (Hfab : Rnearest a <= Rnearest b) by now apply Rnearest_le.
  case Req_bool_spec; intros Hab.
  + assert (Hcon : forall r, mem r x -> Rnearest r = Rnearest a).
    { intros r Hr. apply HX in Hr. destruct Hr as [Hr1 Hr2].
      generalize (Rnearest_le a r Hr1) (Rnearest_le r b Hr2). lra. }
    destruct (is_half a || is_half b) eqn:Hh.
    * (* [Rnearest] is constant on [x], but jumps at [a] or [b]. *)
      apply strongest_Dac.
      -- split; [exact Hne|]. intros r Hr.
         apply continue_in_const with (c := Rnearest a); [exact Hcon | exact Hr].
      -- intros (_ & _ & Hc & _). apply Bool.orb_true_iff in Hh.
         destruct Hh as [Hh|Hh].
         ++ apply (nearest_discontinuous a Hh), Hc, HX.
            split; [apply Rle_refl | exact Hord].
         ++ apply (nearest_discontinuous b Hh), Hc, HX.
            split; [exact Hord | apply Rle_refl].
    * (* No half-integer is in [[a, b]]. *)
      apply Bool.orb_false_iff in Hh. destruct Hh as [Ha Hb].
      apply strongest_Com. split; [exact Hne|]. split; [|split].
      -- exists (Rabs a + Rabs b). intros r Hr. apply HX in Hr.
         now apply Rabs_between.
      -- intros r Hr. apply nearest_continuous.
         apply HX in Hr. destruct Hr as [Hr1 Hr2].
         destruct (Rle_lt_or_eq_dec _ _ Hr1) as [Har| <-]; [|exact Ha].
         destruct (Rle_lt_or_eq_dec _ _ Hr2) as [Hrb| ->]; [|exact Hb].
         apply (nearest_inside a b); [split; assumption | exact Hab].
      -- exists (Rabs (Rnearest a)). intros s (r & Hr & ->).
         rewrite (Hcon r Hr). apply Rle_refl.
  + (* [x] contains [h = Rnearest a + 1/2] and reals on either side of it
       up to [a] and [b]. *)
    apply strongest_Def; [exact Hne|].
    assert (Hlt : Rnearest a + 1 <= Rnearest b).
    { unfold Rnearest in *. rewrite <- plus_IZR. apply IZR_le.
      apply le_IZR in Hfab.
      assert (Znearest choice a <> Znearest choice b)
        by (intros E; apply Hab; now rewrite E).
      lia. }
    generalize (Rnearest_half a) (Rnearest_half b). intros Ha Hb.
    apply (nearest_jump x (Some a) (Some b) (Znearest choice a) HX);
      change (IZR (Znearest choice a)) with (Rnearest a).
    * split; lra.
    * intros E. exists b. split; [split; [exact Hord | apply Rle_refl]|].
      assert (Hhb : Rnearest a + / 2 <= b) by lra.
      destruct (Rle_lt_or_eq_dec _ _ Hhb) as [H|H]; [exact H|].
      rewrite <- H in Hlt. lra.
    * intros E. exists a. split; [split; [apply Rle_refl | exact Hord]|].
      assert (Hah : a <= Rnearest a + / 2) by lra.
      destruct (Rle_lt_or_eq_dec _ _ Hah) as [H|H]; [exact H|].
      rewrite <- H in E. lra.
- (* [x] contains [h = Rnearest a + 1/2], the reals above it, and [a < h]
     if [h] rounds up. *)
  apply strongest_Def; [exact Hne|].
  generalize (Rnearest_half a). intros Ha.
  apply (nearest_jump x (Some a) None (Znearest choice a) HX);
    change (IZR (Znearest choice a)) with (Rnearest a).
  + split; [lra | exact I].
  + intros _. exists (Rnearest a + / 2 + 1). split; [split; [lra | exact I] | lra].
  + intros E. exists a. split; [split; [apply Rle_refl | exact I]|].
    assert (Hah : a <= Rnearest a + / 2) by lra.
    destruct (Rle_lt_or_eq_dec _ _ Hah) as [H|H]; [exact H|].
    rewrite <- H in E. lra.
- (* [x] contains [h = Rnearest b - 1/2], the reals below it, and [b > h]
     if [h] rounds down. *)
  apply strongest_Def; [exact Hne|].
  generalize (Rnearest_half b). intros Hb.
  apply (nearest_jump x None (Some b) (Znearest choice b - 1) HX);
    rewrite minus_IZR; change (IZR (Znearest choice b)) with (Rnearest b).
  + split; [exact I | lra].
  + intros E. exists b. split; [split; [exact I | apply Rle_refl]|].
    assert (Hhb : Rnearest b - 1 + / 2 <= b) by lra.
    destruct (Rle_lt_or_eq_dec _ _ Hhb) as [H|H]; [exact H|].
    rewrite H in E. lra.
  + intros _. exists (Rnearest b - 1 + / 2 - 1).
    split; [split; [exact I | lra] | lra].
- (* [x] contains [1/2] and the reals on both sides of it. *)
  apply strongest_Def; [exact Hne|].
  apply (nearest_jump x None None 0 HX).
  + split; exact I.
  + intros _. exists 1. split; [split; exact I | lra].
  + intros _. exists 0. split; [split; exact I | lra].
Qed.

End Nearest.
