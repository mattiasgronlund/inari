(** * [trunc] of intervals is tightest and decorated correctly

    [Interval::trunc] returns the hull of the image of its argument, and
    [DecInterval::trunc] decorates it with the minimum of the strongest
    decoration that holds and the decoration of its argument, as IEEE 1788
    asks of a tightest interval version of a function.

    [Interval::trunc] stores [[a, b]] as [[-a; b]] and truncates both lanes
    as they are, with no [neg0]. Truncation is odd, [trunc (-a) =
    -trunc a], also on signed zeros and infinities, so the first lane holds
    [-trunc a]. The result is then the [[trunc a, trunc b]] of Section
    [Round] in [Integer.v], which proves the hull once [trunc] is known to
    be nondecreasing and to move a real by less than 1.

    [trunc] is continuous except at the nonzero integers: at [n > 0] it
    jumps from below, at [n < 0] from above, and it is [0] for
    [-1 < r < 1], [n] for [n <= r < n + 1] if [n > 0], and [n] for
    [n - 1 < r <= n] if [n < 0]. If [trunc a = trunc b = n], the
    restriction of [trunc] to [[a, b]] is the constant [n], and [trunc] is
    continuous at each point of [[a, b]] unless a nonzero integer is in
    it. Such an integer is [n], so it is [a] if [n > 0] and [b] if
    [n < 0], and there is none if [n = 0]. This is when [a] or [b] is a
    nonzero integer, the test
    [(x.inf_raw() != 0.0 && x.inf_raw() == y.inf_raw()) ||
    (x.sup_raw() != 0.0 && x.sup_raw() == y.sup_raw())] in
    [impl_dec!(trunc, ...)], where [y.inf_raw()] is [trunc a] and
    [y.sup_raw()] is [trunc b]. Otherwise [[a, b]] contains a positive
    integer and a real below it, or a negative integer and a real above
    it, so the restriction of [trunc] jumps there. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Ieee1788 Integer.

Open Scope R_scope.

(** ** [trunc] of a float *)

Lemma ftrunc_finite : forall a, is_finite (ftrunc a) = is_finite a.
Proof.
intros a. exact (proj1 (proj2 (Bnearbyint_correct 53 1024 _ mode_ZR a))).
Qed.

Lemma ftrunc_inf : forall s, ftrunc (B754_infinity s) = B754_infinity s.
Proof.
reflexivity.
Qed.

Lemma ftrunc_nan : ftrunc B754_nan = B754_nan.
Proof.
reflexivity.
Qed.

Lemma ftrunc_B2R : forall a, B2R (ftrunc a) = Rtrunc (B2R a).
Proof.
intros a. unfold ftrunc. rewrite (proj1 (Bnearbyint_correct 53 1024 _ mode_ZR a)).
apply round_FIX_0.
Qed.

Lemma ftrunc_sign : forall a, is_finite a = true -> Bsign (ftrunc a) = Bsign a.
Proof.
intros a Fa. apply (proj2 (proj2 (Bnearbyint_correct 53 1024 _ mode_ZR a))).
change (is_nan (ftrunc a) = false).
rewrite <- ftrunc_finite in Fa.
destruct (ftrunc a); first [reflexivity | discriminate].
Qed.

(** [trunc] is odd, also on signed zeros and infinities. *)
Lemma ftrunc_opp : forall a, ftrunc (opp a) = opp (ftrunc a).
Proof.
intros a. unfold opp.
destruct (is_finite a) eqn:Fa.
- assert (Fa' : is_nan a = false) by (destruct a; easy).
  assert (Fta : is_nan (ftrunc a) = false).
  { rewrite <- ftrunc_finite in Fa. destruct (ftrunc a); easy. }
  apply B2R_Bsign_inj.
  + now rewrite ftrunc_finite, is_finite_Bopp.
  + now rewrite is_finite_Bopp, ftrunc_finite.
  + rewrite B2R_Bopp, !ftrunc_B2R, B2R_Bopp. unfold Rtrunc.
    now rewrite Ztrunc_opp, opp_IZR.
  + rewrite ftrunc_sign by now rewrite is_finite_Bopp.
    rewrite !Bsign_Bopp by assumption. now rewrite ftrunc_sign.
- destruct a as [s|s| |s m e H]; [discriminate | reflexivity | reflexivity |
    discriminate].
Qed.

(** [Interval::trunc] has the shape of Section [Round]'s [f]. *)
Lemma trunc_rep :
  forall x,
  rep (Interval.trunc x) =
    (opp (ftrunc (opp (fst (rep x)))), ftrunc (snd (rep x))).
Proof.
intros x. change (rep (Interval.trunc x)) with
  (ftrunc (fst (rep x)), ftrunc (snd (rep x))).
rewrite ftrunc_opp. unfold opp. now rewrite Bopp_involutive.
Qed.

(** ** [trunc] of a real *)

Lemma Rtrunc_le : forall u v, u <= v -> Rtrunc u <= Rtrunc v.
Proof.
intros u v H. apply IZR_le, Ztrunc_le, H.
Qed.

Lemma Rtrunc_IZR : forall n, Rtrunc (IZR n) = IZR n.
Proof.
intros n. unfold Rtrunc. now rewrite Ztrunc_IZR.
Qed.

(** [trunc r] is [0] on [(-1, 1)], [floor r] for [r >= 1] and [ceil r]
    for [r <= -1]. *)
Lemma Rtrunc_cases :
  forall r,
  (Rtrunc r = 0 /\ -1 < r < 1) \/
  (0 < Rtrunc r /\ Rtrunc r <= r < Rtrunc r + 1) \/
  (Rtrunc r < 0 /\ Rtrunc r - 1 < r <= Rtrunc r).
Proof.
intros r. unfold Rtrunc. destruct (Rle_or_lt 0 r) as [Hr|Hr].
- rewrite Ztrunc_floor by exact Hr.
  generalize (Zfloor_lb r) (Zfloor_ub r) (Zfloor_lub 0 r Hr). intros H1 H2 H3.
  destruct (Z.eq_dec (Zfloor r) 0) as [E|E].
  + left. rewrite E in *. split; [reflexivity | lra].
  + right; left. assert (H4 : (0 < Zfloor r)%Z) by lia.
    apply (IZR_lt 0) in H4. split; lra.
- rewrite Ztrunc_ceil by lra.
  assert (Hr' : r <= IZR 0) by lra.
  generalize (Zceil_ub r) (Zceil_lb r) (Zceil_glb 0 r Hr'). intros H1 H2 H3.
  destruct (Z.eq_dec (Zceil r) 0) as [E|E].
  + left. rewrite E in *. split; [reflexivity | lra].
  + right; right. assert (H4 : (Zceil r < 0)%Z) by lia.
    apply (IZR_lt _ 0) in H4. split; lra.
Qed.

Lemma Rtrunc_near : forall t, t - 1 < Rtrunc t < t + 1.
Proof.
intros t. destruct (Rtrunc_cases t) as [H|[H|H]]; lra.
Qed.

Lemma Rtrunc_imp_pos :
  forall n u, (0 <= n)%Z -> IZR n <= u < IZR n + 1 -> Rtrunc u = IZR n.
Proof.
intros n u Hn H. apply (IZR_le 0) in Hn. unfold Rtrunc.
rewrite Ztrunc_floor by lra.
rewrite (Zfloor_imp n u); [reflexivity|]. rewrite plus_IZR. exact H.
Qed.

Lemma Rtrunc_imp_neg :
  forall n u, (n <= 0)%Z -> IZR n - 1 < u <= IZR n -> Rtrunc u = IZR n.
Proof.
intros n u Hn H. apply (IZR_le _ 0) in Hn. unfold Rtrunc.
rewrite Ztrunc_ceil by lra.
rewrite (Zceil_imp n u); [reflexivity|]. rewrite minus_IZR. exact H.
Qed.

Lemma Rtrunc_small : forall u, -1 < u < 1 -> Rtrunc u = 0.
Proof.
intros u H. destruct (Rle_or_lt 0 u).
- apply (Rtrunc_imp_pos 0); [lia | cbn; lra].
- apply (Rtrunc_imp_neg 0); [lia | cbn; lra].
Qed.

(** ** Continuity of [trunc] *)

(** A function constant on an open interval is continuous in it. *)
Lemma continuous_const_between :
  forall h l u c r,
  l < r < u -> (forall s, l < s < u -> h s = c) -> continuity_pt h r.
Proof.
intros h l u c r Hr Hc eps Heps.
exists (Rmin (r - l) (u - r)). split.
{ apply Rmin_glb_lt; lra. }
intros s [_ Hs]. change (Rabs (s - r) < Rmin (r - l) (u - r)) in Hs.
change (Rabs (h s - h r) < eps).
generalize (Rmin_l (r - l) (u - r)) (Rmin_r (r - l) (u - r)). intros H1 H2.
apply Rabs_def2 in Hs.
rewrite (Hc s), (Hc r) by lra.
replace (c - c) with 0 by ring. rewrite Rabs_R0. exact Heps.
Qed.

(** [trunc] is continuous except at the nonzero integers. *)
Lemma trunc_continuous :
  forall r, (r <> 0 -> r <> Rtrunc r) -> continuity_pt Rtrunc r.
Proof.
intros r Hr.
destruct (Rtrunc_cases r) as [(E & H)|[(Hn & H)|(Hn & H)]].
- apply (continuous_const_between Rtrunc (-1) 1 0 r H Rtrunc_small).
- assert (Hr' : Rtrunc r < r).
  { destruct (Rle_lt_or_eq_dec _ _ (proj1 H)) as [H'|H']; [exact H'|].
    elim Hr; lra. }
  apply (continuous_const_between Rtrunc (Rtrunc r) (Rtrunc r + 1) (Rtrunc r));
    [lra|].
  intros s Hs. change (Rtrunc r) with (IZR (Ztrunc r)) in *.
  apply Rtrunc_imp_pos; [|lra]. apply le_IZR. lra.
- assert (Hr' : r < Rtrunc r).
  { destruct (Rle_lt_or_eq_dec _ _ (proj2 H)) as [H'|H']; [exact H'|].
    elim Hr; lra. }
  apply (continuous_const_between Rtrunc (Rtrunc r - 1) (Rtrunc r) (Rtrunc r));
    [lra|].
  intros s Hs. change (Rtrunc r) with (IZR (Ztrunc r)) in *.
  apply Rtrunc_imp_neg; [|lra]. apply le_IZR. lra.
Qed.

(** [trunc] jumps by 1 at the positive integer [n], so its restriction to
    [X] is not continuous at [n] if [X] has reals arbitrarily close below
    [n]. *)
Lemma trunc_discontinuous_below :
  forall (X : R -> Prop) n, (0 < n)%Z ->
  (forall d, 0 < d -> exists s, X s /\ IZR n - d < s < IZR n) ->
  ~ continue_in Rtrunc X (IZR n).
Proof.
intros X n Hn HX Hc.
assert (H1 : 1 > 0) by lra.
destruct (Hc 1 H1) as (alp & Halp & H).
assert (Hd : 0 < Rmin alp 1) by (apply Rmin_glb_lt; lra).
destruct (HX (Rmin alp 1) Hd) as (s & Hs & Hs1 & Hs2).
generalize (Rmin_l alp 1) (Rmin_r alp 1). intros Hm1 Hm2.
assert (E : Rtrunc s = IZR n - 1).
{ rewrite (Rtrunc_imp_pos (n - 1)); rewrite ?minus_IZR; [reflexivity | lia | lra]. }
assert (Hlt : Rabs (Rtrunc s - Rtrunc (IZR n)) < 1).
{ apply H. split.
  - split; [exact Hs | intros Heq; lra].
  - change (Rabs (s - IZR n) < alp). rewrite Rabs_left; lra. }
rewrite E, Rtrunc_IZR, Rabs_left in Hlt by lra. lra.
Qed.

(** [trunc] jumps by 1 at the negative integer [n], so its restriction to
    [X] is not continuous at [n] if [X] has reals arbitrarily close above
    [n]. *)
Lemma trunc_discontinuous_above :
  forall (X : R -> Prop) n, (n < 0)%Z ->
  (forall d, 0 < d -> exists s, X s /\ IZR n < s < IZR n + d) ->
  ~ continue_in Rtrunc X (IZR n).
Proof.
intros X n Hn HX Hc.
assert (H1 : 1 > 0) by lra.
destruct (Hc 1 H1) as (alp & Halp & H).
assert (Hd : 0 < Rmin alp 1) by (apply Rmin_glb_lt; lra).
destruct (HX (Rmin alp 1) Hd) as (s & Hs & Hs1 & Hs2).
generalize (Rmin_l alp 1) (Rmin_r alp 1). intros Hm1 Hm2.
assert (E : Rtrunc s = IZR n + 1).
{ rewrite (Rtrunc_imp_neg (n + 1)); rewrite ?plus_IZR; [reflexivity | lia | lra]. }
assert (Hlt : Rabs (Rtrunc s - Rtrunc (IZR n)) < 1).
{ apply H. split.
  - split; [exact Hs | intros Heq; lra].
  - change (Rabs (s - IZR n) < alp). rewrite Rabs_pos_eq; lra. }
rewrite E, Rtrunc_IZR, Rabs_pos_eq in Hlt by lra. lra.
Qed.

(** [trunc] is not continuous at a nonzero integer. *)
Lemma trunc_discontinuous :
  forall c, c <> 0 -> c = Rtrunc c -> ~ continuity_pt Rtrunc c.
Proof.
intros c Hc0 Hc. unfold Rtrunc in Hc. rewrite Hc.
destruct (Z.lt_total (Ztrunc c) 0) as [Hn|[Hn|Hn]].
- apply (trunc_discontinuous_above no_cond _ Hn).
  intros d Hd. exists (IZR (Ztrunc c) + d / 2). split; [exact I | lra].
- rewrite Hn in Hc. now elim Hc0.
- apply (trunc_discontinuous_below no_cond _ Hn).
  intros d Hd. exists (IZR (Ztrunc c) - d / 2). split; [exact I | lra].
Qed.

(** ** The strongest decoration *)

(** The strongest decoration of [trunc] on the reals between [lo] and
    [hi], as [impl_dec!(trunc, ...)] computes it. *)
Definition trunc_dec (lo hi : option R) : Decoration :=
  match lo, hi with
  | Some a, Some b =>
      if Req_bool (Rtrunc a) (Rtrunc b) then
        if (negb (Req_bool a 0) && Req_bool a (Rtrunc a)) ||
           (negb (Req_bool b 0) && Req_bool b (Rtrunc b)) then Dac else Com
      else Def
  | _, _ => Def
  end.

(** The test of [trunc_dec] on one bound: it is a nonzero integer. *)
Lemma nonzero_int_spec :
  forall c,
  negb (Req_bool c 0) && Req_bool c (Rtrunc c) = true <->
  c <> 0 /\ c = Rtrunc c.
Proof.
intros c.
case Req_bool_spec; intros H0; [|case Req_bool_spec; intros H1]; cbn;
  split; intros H; first [discriminate H | tauto | reflexivity].
Qed.

(** If [x] contains the positive integer [n] and a real below it, the
    restriction of [trunc] to [x] is not continuous at [n]. *)
Lemma trunc_jump_below :
  forall x lo hi n t, (0 < n)%Z ->
  (forall r, mem r x <-> in_bounds lo hi r) ->
  in_bounds lo hi t -> in_bounds lo hi (IZR n) -> t < IZR n ->
  ~ p Dac Rtrunc x.
Proof.
intros x lo hi n t Hn0 HX Ht Hn Htn [_ Hc].
apply (trunc_discontinuous_below (fun r => mem r x) n Hn0).
- intros d Hd. exists (Rmax t (IZR n - d / 2)). split.
  + apply HX. apply (in_bounds_between lo hi t (IZR n)); [exact Ht | exact Hn |].
    split; [apply Rmax_l | apply Rmax_lub; lra].
  + split.
    * generalize (Rmax_r t (IZR n - d / 2)). lra.
    * apply Rmax_lub_lt; lra.
- apply Hc, HX, Hn.
Qed.

(** If [x] contains the negative integer [n] and a real above it, the
    restriction of [trunc] to [x] is not continuous at [n]. *)
Lemma trunc_jump_above :
  forall x lo hi n t, (n < 0)%Z ->
  (forall r, mem r x <-> in_bounds lo hi r) ->
  in_bounds lo hi t -> in_bounds lo hi (IZR n) -> IZR n < t ->
  ~ p Dac Rtrunc x.
Proof.
intros x lo hi n t Hn0 HX Ht Hn Hnt [_ Hc].
apply (trunc_discontinuous_above (fun r => mem r x) n Hn0).
- intros d Hd. exists (Rmin t (IZR n + d / 2)). split.
  + apply HX. apply (in_bounds_between lo hi (IZR n) t); [exact Hn | exact Ht |].
    split; [apply Rmin_glb; lra | apply Rmin_l].
  + split.
    * apply Rmin_glb_lt; lra.
    * generalize (Rmin_r t (IZR n + d / 2)). lra.
- apply Hc, HX, Hn.
Qed.

Lemma trunc_strongest :
  forall x lo hi,
  (forall r, mem r x <-> in_bounds lo hi r) -> ordered lo hi ->
  strongest (trunc_dec lo hi) Rtrunc x.
Proof.
intros x lo hi HX Hord.
assert (Hne : exists r, mem r x).
{ destruct (in_bounds_nonempty lo hi Hord) as (r & Hr). exists r. now apply HX. }
unfold trunc_dec. destruct lo as [a|], hi as [b|].
- assert (Htab : Rtrunc a <= Rtrunc b) by now apply Rtrunc_le.
  assert (Hcon : forall r, mem r x -> Rtrunc a <= Rtrunc r <= Rtrunc b).
  { intros r Hr. apply HX in Hr. destruct Hr as [Hr1 Hr2].
    split; now apply Rtrunc_le. }
  case Req_bool_spec; intros Hab.
  + destruct ((negb (Req_bool a 0) && Req_bool a (Rtrunc a)) ||
              (negb (Req_bool b 0) && Req_bool b (Rtrunc b))) eqn:Ht.
    * (* [trunc] is constant on [x], but jumps at the nonzero integer [a]
         or [b]. *)
      apply strongest_Dac.
      -- split; [exact Hne|]. intros r Hr.
         apply continue_in_const with (c := Rtrunc a); [|exact Hr].
         intros s Hs. generalize (Hcon s Hs). lra.
      -- intros (_ & _ & Hc & _).
         apply Bool.orb_true_iff in Ht. rewrite !nonzero_int_spec in Ht.
         destruct Ht as [[Ha0 Ha]|[Hb0 Hb]].
         ++ apply (trunc_discontinuous a Ha0 Ha), Hc, HX.
            split; [apply Rle_refl | exact Hord].
         ++ apply (trunc_discontinuous b Hb0 Hb), Hc, HX.
            split; [exact Hord | apply Rle_refl].
    * (* A nonzero integer [r] in [x] would be [trunc a = trunc b], so [a]
         if it is positive and [b] if it is negative. *)
      apply Bool.orb_false_iff in Ht. destruct Ht as [Ha Hb].
      assert (Ha' : ~ (a <> 0 /\ a = Rtrunc a)).
      { intros H. apply nonzero_int_spec in H. congruence. }
      assert (Hb' : ~ (b <> 0 /\ b = Rtrunc b)).
      { intros H. apply nonzero_int_spec in H. congruence. }
      apply strongest_Com. split; [exact Hne|]. split; [|split].
      -- exists (Rabs a + Rabs b). intros r Hr. apply HX in Hr.
         now apply Rabs_between.
      -- intros r Hr. apply trunc_continuous. intros Hr0 Hrt.
         generalize (Hcon r Hr). apply HX in Hr. destruct Hr as [Hr1 Hr2].
         intros Hr'.
         destruct (Rtrunc_cases r) as [Hr|[Hr|Hr]],
           (Rtrunc_cases a) as [Ha2|[Ha2|Ha2]],
           (Rtrunc_cases b) as [Hb2|[Hb2|Hb2]];
           first [lra | apply Ha'; split; [intros ?|]; lra |
                  apply Hb'; split; [intros ?|]; lra].
      -- exists (Rabs (Rtrunc a)). intros s (r & Hr & ->).
         generalize (Hcon r Hr). intros Hr'.
         replace (Rtrunc r) with (Rtrunc a) by lra. apply Rle_refl.
  + apply strongest_Def; [exact Hne|].
    assert (Hlt : Rtrunc a + 1 <= Rtrunc b).
    { unfold Rtrunc in *. rewrite <- plus_IZR. apply IZR_le.
      apply le_IZR in Htab.
      assert (Ztrunc a <> Ztrunc b) by (intros E; apply Hab; now rewrite E).
      lia. }
    generalize (Rtrunc_near a) (Rtrunc_near b). intros Ha Hb.
    destruct (Z_lt_le_dec 0 (Ztrunc b)) as [Hn|Hn].
    * (* [x] contains [trunc b > 0] and [a < trunc b]. *)
      assert (Hb' : Rtrunc b <= b).
      { apply (IZR_lt 0) in Hn. change (IZR (Ztrunc b)) with (Rtrunc b) in Hn.
        destruct (Rtrunc_cases b) as [H|[H|H]]; lra. }
      apply (trunc_jump_below x (Some a) (Some b) (Ztrunc b) a Hn HX).
      -- split; [apply Rle_refl | exact Hord].
      -- change (IZR (Ztrunc b)) with (Rtrunc b). split; lra.
      -- change (IZR (Ztrunc b)) with (Rtrunc b). lra.
    * (* [x] contains [trunc a < 0] and [trunc a < b]. *)
      assert (Hn' : (Ztrunc a < 0)%Z).
      { apply lt_IZR. apply (IZR_le _ 0) in Hn.
        change (IZR (Ztrunc a)) with (Rtrunc a).
        change (IZR (Ztrunc b)) with (Rtrunc b) in Hn. lra. }
      assert (Ha' : a <= Rtrunc a).
      { apply (IZR_lt _ 0) in Hn'. change (IZR (Ztrunc a)) with (Rtrunc a) in Hn'.
        destruct (Rtrunc_cases a) as [H|[H|H]]; lra. }
      apply (trunc_jump_above x (Some a) (Some b) (Ztrunc a) b Hn' HX).
      -- split; [exact Hord | apply Rle_refl].
      -- change (IZR (Ztrunc a)) with (Rtrunc a). split; lra.
      -- change (IZR (Ztrunc a)) with (Rtrunc a). lra.
- (* [x] contains a positive integer above [a]. *)
  apply strongest_Def; [exact Hne|].
  generalize (Rtrunc_near a). intros Ha.
  assert (Hn : (0 < Z.abs (Ztrunc a) + 1)%Z) by lia.
  assert (Ha' : Rtrunc a + 1 <= IZR (Z.abs (Ztrunc a) + 1)).
  { unfold Rtrunc. rewrite <- plus_IZR. apply IZR_le. lia. }
  apply (trunc_jump_below x (Some a) None _ a Hn HX).
  + split; [apply Rle_refl | exact I].
  + split; [lra | exact I].
  + lra.
- (* [x] contains a negative integer below [b]. *)
  apply strongest_Def; [exact Hne|].
  generalize (Rtrunc_near b). intros Hb.
  assert (Hn : (- Z.abs (Ztrunc b) - 1 < 0)%Z) by lia.
  assert (Hb' : IZR (- Z.abs (Ztrunc b) - 1) <= Rtrunc b - 1).
  { unfold Rtrunc. rewrite <- minus_IZR. apply IZR_le. lia. }
  apply (trunc_jump_above x None (Some b) _ b Hn HX).
  + split; [exact I | apply Rle_refl].
  + split; [exact I | lra].
  + lra.
- (* [x] contains [1] and [0]. *)
  apply strongest_Def; [exact Hne|].
  assert (Hn : (0 < 1)%Z) by lia.
  apply (trunc_jump_below x None None 1 0 Hn HX); [split; exact I .. | lra].
Qed.

Lemma trunc_test :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  (if Interval.is_singleton (Interval.trunc x) then
     if (negb (eq (Interval.inf_raw x) zero) &&
         eq (Interval.inf_raw x) (Interval.inf_raw (Interval.trunc x))) ||
        (negb (eq (Interval.sup_raw x) zero) &&
         eq (Interval.sup_raw x) (Interval.sup_raw (Interval.trunc x)))
     then Dac else Com
   else Def) = trunc_dec (bound (opp (fst (rep x)))) (bound (snd (rep x))).
Proof.
intros x Hx Hn.
rewrite (round_singleton ftrunc Rtrunc Interval.trunc ftrunc_finite ftrunc_inf
  ftrunc_B2R trunc_rep x Hx Hn).
unfold trunc_dec, bound.
destruct (is_finite (opp (fst (rep x)))) eqn:Fa; cbv beta iota; [|reflexivity].
destruct (is_finite (snd (rep x))) eqn:Fb; cbv beta iota; [|reflexivity].
destruct (Req_bool (Rtrunc (B2R (opp (fst (rep x)))))
  (Rtrunc (B2R (snd (rep x))))); [|reflexivity].
unfold Interval.inf_raw, Interval.sup_raw, eq.
rewrite (lower_f ftrunc Interval.trunc trunc_rep),
  (upper_f ftrunc Interval.trunc trunc_rep).
rewrite !Beqb_correct, !ftrunc_B2R
  by first [exact Fa | exact Fb | reflexivity | now rewrite ftrunc_finite].
reflexivity.
Qed.

(** ** The theorems *)

(** [Interval::trunc] returns the tightest interval that contains the image
    of its argument under [trunc]. *)
Theorem trunc_correct :
  forall x, valid x -> is_hull (image Rtrunc x) (Interval.trunc x).
Proof.
exact (round_is_hull ftrunc Rtrunc Interval.trunc ftrunc_finite ftrunc_inf
  ftrunc_nan ftrunc_B2R Rtrunc_le Rtrunc_near trunc_rep).
Qed.

(** [DecInterval::trunc] returns a NaI unchanged, and otherwise the result of
    [Interval::trunc] with the minimum of the strongest decoration of
    [trunc] on the interval and the decoration of its argument. *)
Theorem dec_trunc_correct :
  forall x, valid (itv x) ->
  if DecInterval.is_nai x then DecInterval.trunc x = x
  else
    is_hull (image Rtrunc (itv x)) (itv (DecInterval.trunc x)) /\
    exists d, strongest d Rtrunc (itv x) /\
      dec (DecInterval.trunc x) = dec_min d (dec x).
Proof.
exact (impl_dec_correct ftrunc Rtrunc Interval.trunc ftrunc_finite ftrunc_inf
  ftrunc_nan ftrunc_B2R Rtrunc_le Rtrunc_near trunc_rep _ trunc_dec trunc_test
  trunc_strongest).
Qed.
