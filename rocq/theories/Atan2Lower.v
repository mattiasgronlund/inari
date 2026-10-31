(** * [Interval::atan2] in the fourth quadrant and below the [x] axis

    As in [Atan2Right.v]: [y] is [self] with bounds [c] and [d], [x] is
    [rhs] with bounds [a] and [b], and the class of [x] comes first.
    - [at2_q4], [P0_N1], [P1_N0], [P1_N1] and [Z_N1]: the closed fourth
      quadrant without [(0, 0)], where [atan2] increases in [x] and in
      [y]: least at [(c, a)], greatest at [(d, b)];
    - [at2_mn1], [M_N1]: [y < 0], where it increases in [x]; in [y] it
      decreases for [x = a < 0] and increases for [x = b > 0]: least at
      [(d, a)], greatest at [(d, b)].
    A corner at an infinity gives a limit, which [at_val] is. *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Integer Sign MaxMin AddSub DivTight
  MpfrRound MonoInc Classes ClosedDom AtanReal Atan2Mpfr.

Open Scope R_scope.

(** ** The bounds *)

Lemma alo_fin_nan : forall w : f64, is_finite w = true -> is_nan w = false.
Proof.
intros [s|s| |s m e H] F; try reflexivity. discriminate F.
Qed.

Lemma alo_pos_nan : forall w, pos_lane w -> is_nan w = false.
Proof.
intros w [-> | [F _]]; [reflexivity | exact (alo_fin_nan w F)].
Qed.

(** The lower bound [opp w] of a positive first lane [w]: -inf, or finite
    below 0. *)
Lemma alo_neg_lo :
  forall w, pos_lane w ->
  opp w = B754_infinity true \/ (is_finite (opp w) = true /\ B2R (opp w) < 0).
Proof.
intros w [-> | [F H]]; [left; reflexivity | right].
rewrite is_finite_opp, B2R_opp. split; [exact F | lra].
Qed.

Lemma alo_lo_nan :
  forall w : f64, w = B754_infinity true \/ (is_finite w = true /\ B2R w < 0) -> is_nan w = false.
Proof.
intros w [-> | [F _]]; [reflexivity | exact (alo_fin_nan w F)].
Qed.

(** The reals of a nonempty interval, with each bound a condition only if
    it is finite. *)
Lemma alo_mem :
  forall z r, valid z -> Interval.is_empty z = false ->
  mem r z <->
  (is_finite (Interval.inf_raw z) = true -> B2R (Interval.inf_raw z) <= r) /\
  (is_finite (Interval.sup_raw z) = true -> r <= B2R (Interval.sup_raw z)).
Proof.
intros z r Hz E. rewrite (cl_mem_iff z r Hz E). unfold in_bounds, bound.
destruct (is_finite (Interval.inf_raw z)), (is_finite (Interval.sup_raw z));
  cbv beta iota; split; intros [H1 H2]; split; intros; try discriminate; auto.
Qed.

Lemma alo_ord :
  forall z, valid z -> Interval.is_empty z = false ->
  is_finite (Interval.inf_raw z) = true -> is_finite (Interval.sup_raw z) = true ->
  B2R (Interval.inf_raw z) <= B2R (Interval.sup_raw z).
Proof.
intros z Hz E Fa Fb. exact (cl_mem_sup z _ Hz E Fb (cl_inf_mem z Hz E Fa)).
Qed.

(** ** The fourth quadrant *)

(** [x] holds the reals of [[a, b]] with [a >= 0] finite, and [y] those of
    [[c, d]] with [c < 0] or [c = -inf], and [d <= 0] finite; [d = 0] only
    if [a > 0], so that the box misses [(0, 0)]. *)
Lemma alo_q4_core :
  forall emin emax m y x (a b c d : f64),
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  (forall t, mem t x <->
     (is_finite a = true -> B2R a <= t) /\ (is_finite b = true -> t <= B2R b)) ->
  (forall r, mem r y <->
     (is_finite c = true -> B2R c <= r) /\ (is_finite d = true -> r <= B2R d)) ->
  is_finite a = true -> 0 <= B2R a ->
  is_finite b = true \/ b = B754_infinity false -> (is_finite b = true -> B2R a <= B2R b) ->
  c = B754_infinity true \/ (is_finite c = true /\ B2R c < 0) ->
  is_finite d = true -> B2R d <= 0 -> (B2R d = 0 -> 0 < B2R a) ->
  (is_finite c = true -> B2R c <= B2R d) ->
  is_tightest (image2_set atan2_dom Ratan2 y x)
    (Interval.with_infsup_raw (atan2_rd m c a) (atan2_ru m d b)).
Proof.
intros emin emax m y x a b c d Hrg Hg Hat Mx My Fa Ha0 Ub Oab Lc Fd Hd0 Hda Ocd.
assert (Ma : mem (B2R a) x).
{ apply Mx. split; [intros _; apply Rle_refl | exact Oab]. }
assert (Md : mem (B2R d) y).
{ apply My. split; [exact Ocd | intros _; apply Rle_refl]. }
(* Every point of the box has [r <= d <= 0] and [t >= a >= 0]. *)
assert (Hbox : forall r t, mem r y -> mem t x -> r <= B2R d /\ B2R a <= t).
{ intros r t Hr Ht. apply My in Hr. apply Mx in Ht.
  split; [exact (proj2 Hr Fd) | exact (proj1 Ht Fa)]. }
unfold Interval.with_infsup_raw, Generic.constant. apply tightest_lanes_lub.
- (* [(d, a)] is in the domain: [d < 0], or [d = 0] and [a > 0]. *)
  exists (Ratan2 (B2R d) (B2R a)), (B2R d), (B2R a).
  split; [exact Md|]. split; [exact Ma|]. split; [|reflexivity].
  destruct (Req_dec (B2R d) 0) as [E|E].
  + right. specialize (Hda E). intros E0. lra.
  + left. exact E.
- (* The lower lane, at [(c, a)]: [c] is not 0, and [a] is finite. *)
  assert (Aca : at_args c a).
  { split; [exact (alo_lo_nan c Lc)|]. split; [exact (alo_fin_nan a Fa)|].
    split; [right; exact Fa|]. intros Fc Hc.
    destruct Lc as [-> | [_ Hc0]]; [discriminate Fc | lra]. }
  apply (at_lo_lane emin emax m _ c a Hrg Hg Hat Aca).
  + intros s (r & t & Hr & Ht & Hdom & ->).
    destruct (Hbox r t Hr Ht) as [Hrd Hta].
    destruct Lc as [-> | [Fc Hc0]].
    * (* [c = -inf]: the limit [-PI/2], below the whole quadrant. *)
      rewrite at_val_y_ninf. apply Ratan2_q4; [lra | lra | exact Hdom].
    * rewrite (at_val_fin c a Fc Fa). pose proof (proj1 (proj1 (My r) Hr) Fc) as Hcr.
      destruct (Rle_lt_or_eq_dec 0 (B2R a) Ha0) as [Ha | Ha].
      -- (* [a > 0]: up in [y] from [c] to [r], then in [x] from [a] to [t]. *)
         apply Rle_trans with (Ratan2 r (B2R a)); [apply Ratan2_inc_y; lra|].
         assert (Hr0' : r <= 0) by lra.
         destruct (Rle_lt_or_eq_dec r 0 Hr0') as [Hr0 | ->]; [apply Ratan2_inc_x; lra|].
         (* On the positive [x] axis, both are 0. *)
         rewrite !Ratan2_zero_y_pos by lra. lra.
      -- (* [a = 0]: the corner is on the negative [y] axis, at [-PI/2]. *)
         rewrite <- Ha, (Ratan2_zero_x_neg _ Hc0). apply Ratan2_q4; [lra | lra | exact Hdom].
  + intros eps He. destruct Lc as [-> | [Fc Hc0]].
    * (* [c = -inf]: [(r, a)] for some [r <= d] far down. *)
      rewrite at_val_y_ninf.
      destruct (Ratan2_y_ninf (B2R a) eps (B2R d) He) as (r & Hrd & Hr0 & Hre).
      exists (Ratan2 r (B2R a)). split; [|lra].
      exists r, (B2R a).
      split; [apply My; split; [intros F; discriminate F | intros _; exact Hrd]|].
      split; [exact Ma|]. split; [left; intros E; lra | reflexivity].
    * (* The corner itself. *)
      rewrite (at_val_fin c a Fc Fa). exists (Ratan2 (B2R c) (B2R a)). split; [|lra].
      exists (B2R c), (B2R a).
      split; [apply My; split; [intros _; apply Rle_refl | intros _; exact (Ocd Fc)]|].
      split; [exact Ma|]. split; [left; intros E; lra | reflexivity].
- (* The upper lane, at [(d, b)]: [d] is finite, and [d = 0] only with
     [b >= a > 0]. *)
  assert (Adb : at_args d b).
  { split; [exact (alo_fin_nan d Fd)|].
    split; [destruct Ub as [Fb | ->]; [exact (alo_fin_nan b Fb) | reflexivity]|].
    split; [left; exact Fd|]. intros _ Hd. specialize (Hda Hd).
    destruct Ub as [Fb | ->].
    - right. split; [exact Fb|]. specialize (Oab Fb). lra.
    - left. reflexivity. }
  apply (at_hi_lane emin emax m _ d b Hrg Hg Hat Adb).
  + intros s (r & t & Hr & Ht & Hdom & ->).
    destruct (Hbox r t Hr Ht) as [Hrd Hta].
    destruct Ub as [Fb | ->].
    * rewrite (at_val_fin d b Fd Fb). pose proof (proj2 (proj1 (Mx t) Ht) Fb) as Htb.
      specialize (Oab Fb).
      destruct (Rle_lt_or_eq_dec 0 (B2R b)) as [Hb | Hb]; [lra | |].
      -- (* [b > 0]: up in [x] from [t] to [b], then in [y] from [r] to [d]. *)
         apply Rle_trans with (Ratan2 r (B2R b)); [|apply Ratan2_inc_y; lra].
         assert (Hr0' : r <= 0) by lra.
         destruct (Rle_lt_or_eq_dec r 0 Hr0') as [Hr0 | ->]; [apply Ratan2_inc_x; lra|].
         (* On the positive [x] axis, both are 0: [t <> 0] by the domain. *)
         assert (Ht0 : 0 < t).
         { destruct Hdom as [H0 | H0]; [exfalso; apply H0; reflexivity|].
           destruct (Rle_lt_or_eq_dec 0 t) as [H1 | H1]; [lra | exact H1 |].
           exfalso. apply H0. symmetry. exact H1. }
         rewrite !Ratan2_zero_y_pos by lra. lra.
      -- (* [b = 0]: then [a = 0], [t = 0], and [r <= d < 0]: both are
            [-PI/2]. *)
         assert (Et : t = 0) by lra. subst t.
         assert (Hr0 : r < 0).
         { destruct Hdom as [H0 | H0]; [|exfalso; apply H0; reflexivity].
           destruct (Rle_lt_or_eq_dec r 0) as [H1 | H1]; [lra | exact H1 |].
           exfalso. apply H0. exact H1. }
         assert (Hd1 : B2R d < 0).
         { destruct (Rle_lt_or_eq_dec (B2R d) 0 Hd0) as [H1 | H1]; [exact H1|].
           specialize (Hda H1). lra. }
         rewrite <- Hb, (Ratan2_zero_x_neg _ Hr0), (Ratan2_zero_x_neg _ Hd1). lra.
    * (* [b = +inf]: the limit 0, above the whole quadrant. *)
      rewrite (at_val_x_pinf d Fd). apply Ratan2_q4; [lra | lra | exact Hdom].
  + intros eps He. destruct Ub as [Fb | ->].
    * (* The corner itself. *)
      rewrite (at_val_fin d b Fd Fb). specialize (Oab Fb).
      exists (Ratan2 (B2R d) (B2R b)). split; [|lra].
      exists (B2R d), (B2R b). split; [exact Md|].
      split; [apply Mx; split; [intros _; exact Oab | intros _; apply Rle_refl]|].
      split; [|reflexivity].
      destruct (Req_dec (B2R d) 0) as [E|E].
      -- right. specialize (Hda E). intros E0. lra.
      -- left. exact E.
    * (* [b = +inf]: [(d, t)] for some [t >= a] far right. *)
      rewrite (at_val_x_pinf d Fd).
      destruct (Ratan2_x_pinf (B2R d) eps (B2R a) He) as (t & Hat' & Ht0 & Hte).
      exists (Ratan2 (B2R d) t). split.
      -- exists (B2R d), t. split; [exact Md|].
         split; [apply Mx; split; [intros _; exact Hat' | intros F; discriminate F]|].
         split; [right; intros E; lra | reflexivity].
      -- apply Rabs_def2 in Hte. lra.
Qed.

(** The facts of [alo_q4_core] from the lanes: the first lane of [x] is
    finite and at most 0 ([a >= 0]), and that of [y] is positive
    ([c < 0] or [c = -inf]); the second lane of [y] is finite and at most
    0, and 0 only if [a > 0]. *)
Lemma alo_q4_box :
  forall emin emax m y x,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  valid y -> valid x ->
  is_finite (fst (rep x)) = true -> B2R (fst (rep x)) <= 0 ->
  pos_lane (fst (rep y)) -> is_finite (snd (rep y)) = true -> B2R (snd (rep y)) <= 0 ->
  (B2R (snd (rep y)) = 0 -> B2R (fst (rep x)) < 0) ->
  is_tightest (image2_set atan2_dom Ratan2 y x)
    (Interval.with_infsup_raw (atan2_rd m (Interval.inf_raw y) (Interval.inf_raw x))
       (atan2_ru m (Interval.sup_raw y) (Interval.sup_raw x))).
Proof.
intros emin emax m y x Hrg Hg Hat Hy Hx F0 H0 P1 F1 H1 H10.
assert (Ex : Interval.is_empty x = false) by exact (alo_fin_nan _ F0).
assert (Ey : Interval.is_empty y = false) by exact (alo_pos_nan _ P1).
assert (Fa : is_finite (Interval.inf_raw x) = true).
{ unfold Interval.inf_raw. rewrite is_finite_opp. exact F0. }
assert (Ha : B2R (Interval.inf_raw x) = - B2R (fst (rep x))).
{ unfold Interval.inf_raw. apply B2R_opp. }
assert (Ha0 : 0 <= B2R (Interval.inf_raw x)) by lra.
assert (Hda : B2R (Interval.sup_raw y) = 0 -> 0 < B2R (Interval.inf_raw x)).
{ intros E. specialize (H10 E). lra. }
exact (alo_q4_core emin emax m y x
  (Interval.inf_raw x) (Interval.sup_raw x) (Interval.inf_raw y) (Interval.sup_raw y)
  Hrg Hg Hat (fun t => alo_mem x t Hx Ex) (fun r => alo_mem y r Hy Ey) Fa Ha0
  (cl_ub_cases x Hx Ex) (alo_ord x Hx Ex Fa) (alo_neg_lo _ P1) F1 H1 Hda
  (fun Fc => alo_ord y Hy Ey Fc F1)).
Qed.

Lemma at2_q4 :
  forall emin emax m y x cx cy,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  valid y -> valid x ->
  Interval.classify x = Some cx -> Interval.classify y = Some cy ->
  (cx = CP0 /\ cy = CN1) \/ (cx = CP1 /\ (cy = CN0 \/ cy = CN1)) \/
  (cx = CZ /\ cy = CN1) ->
  is_tightest (image2_set atan2_dom Ratan2 y x)
    (Interval.with_infsup_raw (atan2_rd m (Interval.inf_raw y) (Interval.inf_raw x))
       (atan2_ru m (Interval.sup_raw y) (Interval.sup_raw x))).
Proof.
intros emin emax m y x cx cy Hrg Hg Hat Hy Hx Hcx Hcy Hc.
destruct Hc as [[-> ->] | [[-> [-> | ->]] | [-> ->]]].
- pose proof (classify_lanes x CP0 Hx Hcx) as (F0 & H0 & _).
  pose proof (classify_lanes y CN1 Hy Hcy) as (P1 & F1 & H1).
  apply (alo_q4_box emin emax m y x Hrg Hg Hat Hy Hx F0);
    [lra | exact P1 | exact F1 | lra | intros E; lra].
- pose proof (classify_lanes x CP1 Hx Hcx) as (F0 & H0 & _).
  pose proof (classify_lanes y CN0 Hy Hcy) as (P1 & F1 & H1).
  apply (alo_q4_box emin emax m y x Hrg Hg Hat Hy Hx F0);
    [lra | exact P1 | exact F1 | lra | intros E; lra].
- pose proof (classify_lanes x CP1 Hx Hcx) as (F0 & H0 & _).
  pose proof (classify_lanes y CN1 Hy Hcy) as (P1 & F1 & H1).
  apply (alo_q4_box emin emax m y x Hrg Hg Hat Hy Hx F0);
    [lra | exact P1 | exact F1 | lra | intros E; lra].
- pose proof (classify_lanes x CZ Hx Hcx) as (F0 & H0 & _).
  pose proof (classify_lanes y CN1 Hy Hcy) as (P1 & F1 & H1).
  apply (alo_q4_box emin emax m y x Hrg Hg Hat Hy Hx F0);
    [lra | exact P1 | exact F1 | lra | intros E; lra].
Qed.

(** ** Below the [x] axis, [x] across 0 *)

(** [x] holds the reals of [[a, b]] with [a < 0] or [a = -inf], and
    [b > 0] or [b = +inf]; [y] those of [[c, d]] with [d < 0] finite. *)
Lemma alo_mn1_core :
  forall emin emax m y x (a b c d : f64),
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  (forall t, mem t x <->
     (is_finite a = true -> B2R a <= t) /\ (is_finite b = true -> t <= B2R b)) ->
  (forall r, mem r y <->
     (is_finite c = true -> B2R c <= r) /\ (is_finite d = true -> r <= B2R d)) ->
  a = B754_infinity true \/ (is_finite a = true /\ B2R a < 0) ->
  b = B754_infinity false \/ (is_finite b = true /\ 0 < B2R b) ->
  is_finite d = true -> B2R d < 0 -> (is_finite c = true -> B2R c <= B2R d) ->
  is_tightest (image2_set atan2_dom Ratan2 y x)
    (Interval.with_infsup_raw (atan2_rd m d a) (atan2_ru m d b)).
Proof.
intros emin emax m y x a b c d Hrg Hg Hat Mx My La Ub Fd Hd0 Ocd.
assert (Md : mem (B2R d) y).
{ apply My. split; [exact Ocd | intros _; apply Rle_refl]. }
assert (Ha : is_finite a = true -> B2R a < 0).
{ destruct La as [-> | [_ H]]; [intros F; discriminate F | intros _; exact H]. }
assert (Hb : is_finite b = true -> 0 < B2R b).
{ destruct Ub as [-> | [_ H]]; [intros F; discriminate F | intros _; exact H]. }
(* Every point of the box is below the [x] axis, with [r <= d]. *)
assert (Hbox : forall r t, mem r y -> mem t x ->
  r <= B2R d /\ (is_finite a = true -> B2R a <= t) /\ (is_finite b = true -> t <= B2R b)).
{ intros r t Hr Ht. apply My in Hr. apply Mx in Ht. split; [exact (proj2 Hr Fd) | exact Ht]. }
unfold Interval.with_infsup_raw, Generic.constant. apply tightest_lanes_lub.
- (* [(d, 0)], with [d < 0]. *)
  exists (Ratan2 (B2R d) 0), (B2R d), 0. split; [exact Md|].
  split; [apply Mx; split; [intros F; specialize (Ha F); lra | intros F; specialize (Hb F); lra]|].
  split; [left; intros E; lra | reflexivity].
- (* The lower lane, at [(d, a)]. *)
  assert (Ada : at_args d a).
  { split; [exact (alo_fin_nan d Fd)|]. split; [exact (alo_lo_nan a La)|].
    split; [left; exact Fd|]. intros _ E. lra. }
  apply (at_lo_lane emin emax m _ d a Hrg Hg Hat Ada).
  + intros s (r & t & Hr & Ht & _ & ->). destruct (Hbox r t Hr Ht) as (Hrd & Hta & _).
    destruct La as [-> | [Fa Ha0]].
    * (* [a = -inf]: the limit [-PI], below the lower half-plane. *)
      rewrite (at_val_x_ninf_neg d Fd Hd0). assert (Hr0 : r < 0) by lra.
      pose proof (Ratan2_lower r t Hr0). lra.
    * (* Down in [y] from [r] to [d] at [x = a < 0], then up in [x] from [a]
         to [t]. *)
      rewrite (at_val_fin d a Fd Fa). specialize (Hta Fa).
      apply Rle_trans with (Ratan2 r (B2R a));
        [apply Ratan2_dec_y_lt; lra | apply Ratan2_inc_x; lra].
  + intros eps He. destruct La as [-> | [Fa Ha0]].
    * (* [a = -inf]: [(d, t)] for some [t < 0] far left. *)
      rewrite (at_val_x_ninf_neg d Fd Hd0).
      destruct (Ratan2_x_ninf_neg (B2R d) eps 0 Hd0 He) as (t & Ht0 & Ht1 & Hte).
      exists (Ratan2 (B2R d) t). split; [|lra].
      exists (B2R d), t. split; [exact Md|].
      split; [apply Mx; split; [intros F; discriminate F | intros F; specialize (Hb F); lra]|].
      split; [left; intros E; lra | reflexivity].
    * (* The corner itself. *)
      rewrite (at_val_fin d a Fd Fa). exists (Ratan2 (B2R d) (B2R a)). split; [|lra].
      exists (B2R d), (B2R a). split; [exact Md|].
      split; [apply Mx; split; [intros _; apply Rle_refl | intros F; specialize (Hb F); lra]|].
      split; [left; intros E; lra | reflexivity].
- (* The upper lane, at [(d, b)]. *)
  assert (Adb : at_args d b).
  { split; [exact (alo_fin_nan d Fd)|].
    split; [destruct Ub as [-> | [Fb _]]; [reflexivity | exact (alo_fin_nan b Fb)]|].
    split; [left; exact Fd|]. intros _ E. lra. }
  apply (at_hi_lane emin emax m _ d b Hrg Hg Hat Adb).
  + intros s (r & t & Hr & Ht & _ & ->). destruct (Hbox r t Hr Ht) as (Hrd & _ & Htb).
    destruct Ub as [-> | [Fb Hb0]].
    * (* [b = +inf]: the limit 0, above the lower half-plane. *)
      rewrite (at_val_x_pinf d Fd). assert (Hr0 : r < 0) by lra.
      pose proof (Ratan2_lower r t Hr0). lra.
    * (* Up in [x] from [t] to [b], then in [y] from [r] to [d] at
         [x = b > 0]. *)
      rewrite (at_val_fin d b Fd Fb). specialize (Htb Fb).
      apply Rle_trans with (Ratan2 r (B2R b));
        [apply Ratan2_inc_x; lra | apply Ratan2_inc_y; lra].
  + intros eps He. destruct Ub as [-> | [Fb Hb0]].
    * (* [b = +inf]: [(d, t)] for some [t > 0] far right. *)
      rewrite (at_val_x_pinf d Fd).
      destruct (Ratan2_x_pinf (B2R d) eps 0 He) as (t & Ht0 & Ht1 & Hte).
      exists (Ratan2 (B2R d) t). split.
      -- exists (B2R d), t. split; [exact Md|].
         split; [apply Mx; split; [intros F; specialize (Ha F); lra | intros F; discriminate F]|].
         split; [left; intros E; lra | reflexivity].
      -- apply Rabs_def2 in Hte. lra.
    * (* The corner itself. *)
      rewrite (at_val_fin d b Fd Fb). exists (Ratan2 (B2R d) (B2R b)). split; [|lra].
      exists (B2R d), (B2R b). split; [exact Md|].
      split; [apply Mx; split; [intros F; specialize (Ha F); lra | intros _; apply Rle_refl]|].
      split; [left; intros E; lra | reflexivity].
Qed.

Lemma at2_mn1 :
  forall emin emax m y x,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  valid y -> valid x ->
  Interval.classify x = Some CM -> Interval.classify y = Some CN1 ->
  is_tightest (image2_set atan2_dom Ratan2 y x)
    (Interval.with_infsup_raw (atan2_rd m (Interval.sup_raw y) (Interval.inf_raw x))
       (atan2_ru m (Interval.sup_raw y) (Interval.sup_raw x))).
Proof.
intros emin emax m y x Hrg Hg Hat Hy Hx Hcx Hcy.
pose proof (classify_lanes x CM Hx Hcx) as (P0 & P1).
pose proof (classify_lanes y CN1 Hy Hcy) as (Q0 & F1 & H1).
assert (Ex : Interval.is_empty x = false) by exact (alo_pos_nan _ P0).
assert (Ey : Interval.is_empty y = false) by exact (alo_pos_nan _ Q0).
exact (alo_mn1_core emin emax m y x
  (Interval.inf_raw x) (Interval.sup_raw x) (Interval.inf_raw y) (Interval.sup_raw y)
  Hrg Hg Hat (fun t => alo_mem x t Hx Ex) (fun r => alo_mem y r Hy Ey)
  (alo_neg_lo _ P0) P1 F1 H1 (fun Fc => alo_ord y Hy Ey Fc F1)).
Qed.
