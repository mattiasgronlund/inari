(** * [Interval::atan2] in the first quadrant, above the [x] axis and right of the [y] axis

    [y] is [self] with bounds [c] and [d], the [y] coordinates, and [x] is
    [rhs] with bounds [a] and [b], the [x] coordinates; the class of [x]
    comes first, as in [x.classify2(y)]. Each case picks the corner of the
    box where [atan2] is least, and the one where it is greatest, by the
    monotonicity of [AtanReal.v]:
    - [at2_q1], [P0_P1], [P1_P0], [P1_P1], [P1_Z] and [Z_P1]: the closed
      first quadrant without [(0, 0)], where [atan2] decreases in [x] and
      increases in [y]: least at [(c, b)], greatest at [(d, a)];
    - [at2_mp1], [M_P1]: [y > 0], where it decreases in [x]; in [y] it
      increases for [x = b > 0] and decreases for [x = a < 0]: least at
      [(c, b)], greatest at [(c, a)];
    - [at2_p1m], [P1_M]: [x > 0], where it increases in [y]; in [x] it
      decreases for [y = d > 0] and increases for [y = c < 0]: least at
      [(c, a)], greatest at [(d, a)].
    A corner at an infinity gives a limit, which [at_val] is. *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Integer Sign MaxMin AddSub DivTight
  MpfrRound MonoInc Classes ClosedDom AtanReal Atan2Mpfr.

Open Scope R_scope.

(** ** The bounds by class *)

Lemma arr_fin_nan : forall w : f64, is_finite w = true -> is_nan w = false.
Proof.
intros [s|s| |s mw ew Hw] F; try discriminate F; reflexivity.
Qed.

Lemma arr_pos_nan : forall w : f64, pos_lane w -> is_nan w = false.
Proof.
intros w [-> | [F _]]; [reflexivity | exact (arr_fin_nan w F)].
Qed.

(** [classify_lanes] for the bounds [inf_raw z = opp (fst (rep z))] and
    [sup_raw z = snd (rep z)], in the classes that these cases meet. *)
Lemma arr_cls :
  forall z c, valid z -> Interval.classify z = Some c ->
  match c with
  | CM =>
      Interval.is_empty z = false /\
      (Interval.inf_raw z = B754_infinity true \/
       (is_finite (Interval.inf_raw z) = true /\ B2R (Interval.inf_raw z) < 0)) /\
      pos_lane (Interval.sup_raw z)
  | CP0 =>
      Interval.is_empty z = false /\ is_finite (Interval.inf_raw z) = true /\
      B2R (Interval.inf_raw z) = 0 /\ pos_lane (Interval.sup_raw z)
  | CP1 =>
      Interval.is_empty z = false /\ is_finite (Interval.inf_raw z) = true /\
      0 < B2R (Interval.inf_raw z) /\ pos_lane (Interval.sup_raw z)
  | CZ =>
      Interval.is_empty z = false /\ is_finite (Interval.inf_raw z) = true /\
      B2R (Interval.inf_raw z) = 0 /\ is_finite (Interval.sup_raw z) = true /\
      B2R (Interval.sup_raw z) = 0
  | _ => True
  end.
Proof.
intros z c Hz Hc. pose proof (classify_lanes z c Hz Hc) as Hl.
unfold Interval.is_empty, Interval.inf_raw, Interval.sup_raw.
destruct c.
- exact I.
- (* The first lane +inf is the lower bound -inf. *)
  destruct Hl as [[E0 | (F0 & H0)] P1].
  + rewrite E0. split; [reflexivity|]. split; [left; reflexivity | exact P1].
  + split; [exact (arr_fin_nan _ F0)|]. split; [|exact P1].
    right. rewrite is_finite_opp, B2R_opp. split; [exact F0 | lra].
- exact I.
- exact I.
- destruct Hl as (F0 & H0 & P1).
  split; [exact (arr_fin_nan _ F0)|]. rewrite is_finite_opp, B2R_opp.
  split; [exact F0|]. split; [lra | exact P1].
- destruct Hl as (F0 & H0 & P1).
  split; [exact (arr_fin_nan _ F0)|]. rewrite is_finite_opp, B2R_opp.
  split; [exact F0|]. split; [lra | exact P1].
- destruct Hl as (F0 & H0 & F1 & H1).
  split; [exact (arr_fin_nan _ F0)|]. rewrite is_finite_opp, B2R_opp.
  split; [exact F0|]. split; [lra|]. split; [exact F1 | exact H1].
Qed.

(** ** Reals of the intervals *)

Lemma arr_ex :
  forall z, valid z -> Interval.is_empty z = false -> exists r, mem r z.
Proof.
intros z Hz E. destruct (valid_nonempty z Hz E) as (_ & _ & O).
destruct (in_bounds_nonempty _ _ O) as (r & Hr).
exists r. exact (proj2 (cl_mem_iff z r Hz E) Hr).
Qed.

(** An interval with the upper bound +inf holds every real above one of
    its reals, and one with the lower bound -inf every real below one. *)
Lemma arr_mem_up :
  forall z r0 r, valid z -> Interval.is_empty z = false ->
  Interval.sup_raw z = B754_infinity false -> mem r0 z -> r0 <= r -> mem r z.
Proof.
intros z r0 r Hz E Eb H0 Hr. apply (cl_mem_iff z r Hz E).
apply (cl_mem_iff z r0 Hz E) in H0. rewrite Eb in *. destruct H0 as [H0 _].
split; [|exact I].
destruct (bound (Interval.inf_raw z)); [lra | exact I].
Qed.

Lemma arr_mem_down :
  forall z r0 r, valid z -> Interval.is_empty z = false ->
  Interval.inf_raw z = B754_infinity true -> mem r0 z -> r <= r0 -> mem r z.
Proof.
intros z r0 r Hz E Ea H0 Hr. apply (cl_mem_iff z r Hz E).
apply (cl_mem_iff z r0 Hz E) in H0. rewrite Ea in *. destruct H0 as [_ H0].
split; [exact I|].
destruct (bound (Interval.sup_raw z)); [lra | exact I].
Qed.

(** A box with a point [(r, t)] of [atan2_dom], i.e. [r > 0] or [t > 0]
    here, has a value. *)
Lemma arr_nonempty :
  forall y x r t, mem r y -> mem t x -> 0 < r \/ 0 < t ->
  exists s, image2_set atan2_dom Ratan2 y x s.
Proof.
intros y x r t Hr Ht H. exists (Ratan2 r t), r, t.
split; [exact Hr|]. split; [exact Ht|]. split; [|reflexivity].
destruct H as [H | H]; [left | right]; intros E; lra.
Qed.

(** ** Bounds of [Ratan2] *)

(** On [r >= 0], [Ratan2] is at least 0: in [(0, PI)] for [r > 0], and 0
    or [PI] on the [x] axis. *)
Lemma arr_nonneg : forall r t, 0 <= r -> atan2_dom r t -> 0 <= Ratan2 r t.
Proof.
intros r t Hr Hd. unfold atan2_dom in Hd. pose proof PI_RGT_0.
destruct (Rle_lt_or_eq_dec 0 r Hr) as [Hr0 | Hr0].
- pose proof (Ratan2_upper r t Hr0). lra.
- subst r. destruct Hd as [Hd | Hd]; [exfalso; apply Hd; reflexivity|].
  destruct (Rtotal_order t 0) as [Ht | [Ht | Ht]].
  + rewrite (Ratan2_zero_y_neg t Ht). lra.
  + contradiction.
  + rewrite (Ratan2_zero_y_pos t Ht). lra.
Qed.

(** On [t >= 0], [Ratan2] is at most [PI / 2]: below it for [t > 0], and
    [PI / 2] or [- (PI / 2)] on the [y] axis. *)
Lemma arr_le_half : forall r t, 0 <= t -> atan2_dom r t -> Ratan2 r t <= PI / 2.
Proof.
intros r t Ht Hd. unfold atan2_dom in Hd. pose proof PI_RGT_0.
destruct (Rle_lt_or_eq_dec 0 t Ht) as [Ht0 | Ht0].
- pose proof (Ratan2_right r t Ht0). lra.
- subst t. destruct Hd as [Hd | Hd]; [|exfalso; apply Hd; reflexivity].
  destruct (Rtotal_order r 0) as [Hr | [Hr | Hr]].
  + rewrite (Ratan2_zero_x_neg r Hr). lra.
  + contradiction.
  + rewrite (Ratan2_zero_x_pos r Hr). lra.
Qed.

(** ** The lanes at the corners *)

(** The lower lane at [(c, b)] for [c >= 0] and [b > 0] or +inf, or [b = 0]
    with [c > 0]. For a finite [b], every value is at least [Ratan2 c b],
    which is attained: [Ratan2 c b <= Ratan2 r b] as [atan2] increases in
    [y] for [x = b > 0], and [Ratan2 r b <= Ratan2 r t] as it decreases in
    [x] for [r > 0] (for [r = 0], [Ratan2 0 b = 0]); for [b = 0], both are
    at least [Ratan2 r 0 = PI / 2]. For [b = +inf], every value is at
    least 0, the limit at [(c, +inf)]. *)
Lemma arr_lo_cb :
  forall emin emax m y x,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  valid y -> valid x -> Interval.is_empty y = false -> Interval.is_empty x = false ->
  is_finite (Interval.inf_raw y) = true -> 0 <= B2R (Interval.inf_raw y) ->
  pos_lane (Interval.sup_raw x) \/
  (is_finite (Interval.sup_raw x) = true /\ B2R (Interval.sup_raw x) = 0 /\
   0 < B2R (Interval.inf_raw y)) ->
  lane_ok (fun s => image2_set atan2_dom Ratan2 y x (- s))
    (opp (atan2_rd m (Interval.inf_raw y) (Interval.sup_raw x))).
Proof.
intros emin emax m y x Hrg Hg Hok Vy Vx Ey Ex Fc Hc Hb.
assert (Ly : forall r, mem r y -> B2R (Interval.inf_raw y) <= r)
  by (intros r Hr; exact (cl_mem_inf y r Vy Ey Fc Hr)).
pose proof (cl_inf_mem y Vy Ey Fc) as My.
destruct Hb as [[Eb | (Fb & Hb)] | (Fb & Hb0 & Hc0)].
- (* [b = +inf]. *)
  apply (at_lo_lane emin emax m (image2_set atan2_dom Ratan2 y x) _ _ Hrg Hg Hok).
  + rewrite Eb. unfold at_args. split; [exact (arr_fin_nan _ Fc)|].
    split; [reflexivity|]. split; [left; exact Fc|].
    intros _ _. left; reflexivity.
  + rewrite Eb, (at_val_x_pinf _ Fc). intros s (r & t & Hr & Ht & Hd & ->).
    apply arr_nonneg; [specialize (Ly r Hr); lra | exact Hd].
  + rewrite Eb, (at_val_x_pinf _ Fc). intros eps He.
    destruct (arr_ex x Vx Ex) as (t0 & Ht0).
    destruct (Ratan2_x_pinf (B2R (Interval.inf_raw y)) eps t0 He)
      as (t & Htt & Ht & Hlt).
    exists (Ratan2 (B2R (Interval.inf_raw y)) t). split.
    * exists (B2R (Interval.inf_raw y)), t.
      split; [exact My|]. split; [exact (arr_mem_up x t0 t Vx Ex Eb Ht0 Htt)|].
      split; [right; intros E; lra | reflexivity].
    * apply Rabs_def2 in Hlt. lra.
- (* [b > 0] finite. *)
  apply (at_lo_lane emin emax m (image2_set atan2_dom Ratan2 y x) _ _ Hrg Hg Hok).
  + unfold at_args. split; [exact (arr_fin_nan _ Fc)|].
    split; [exact (arr_fin_nan _ Fb)|]. split; [left; exact Fc|].
    intros _ _. right; split; [exact Fb | exact Hb].
  + rewrite (at_val_fin _ _ Fc Fb). intros s (r & t & Hr & Ht & Hd & ->).
    pose proof (Ly r Hr) as Hcr. pose proof (cl_mem_sup x t Vx Ex Fb Ht) as Htb.
    apply Rle_trans with (Ratan2 r (B2R (Interval.sup_raw x))).
    * exact (Ratan2_inc_y _ _ _ Hb Hcr).
    * assert (Hr' : 0 <= r) by lra.
      destruct (Rle_lt_or_eq_dec 0 r Hr') as [Hr0 | Hr0].
      -- exact (Ratan2_dec_x _ _ _ Hr0 Htb).
      -- subst r. rewrite (Ratan2_zero_y_pos _ Hb).
         apply arr_nonneg; [lra | exact Hd].
  + rewrite (at_val_fin _ _ Fc Fb). intros eps He.
    exists (Ratan2 (B2R (Interval.inf_raw y)) (B2R (Interval.sup_raw x))).
    split; [|lra].
    exists (B2R (Interval.inf_raw y)), (B2R (Interval.sup_raw x)).
    split; [exact My|]. split; [exact (cl_sup_mem x Vx Ex Fb)|].
    split; [right; intros E; lra | reflexivity].
- (* [b = 0], [c > 0]: [x <= 0], and every value is at least
     [Ratan2 r 0 = PI / 2 = Ratan2 c 0]. *)
  apply (at_lo_lane emin emax m (image2_set atan2_dom Ratan2 y x) _ _ Hrg Hg Hok).
  + unfold at_args. split; [exact (arr_fin_nan _ Fc)|].
    split; [exact (arr_fin_nan _ Fb)|]. split; [left; exact Fc|].
    intros _ H0. lra.
  + rewrite (at_val_fin _ _ Fc Fb), Hb0, (Ratan2_zero_x_pos _ Hc0).
    intros s (r & t & Hr & Ht & Hd & ->).
    pose proof (Ly r Hr) as Hcr. pose proof (cl_mem_sup x t Vx Ex Fb Ht) as Htb.
    rewrite <- (Ratan2_zero_x_pos r) by lra. apply Ratan2_dec_x; lra.
  + rewrite (at_val_fin _ _ Fc Fb). intros eps He.
    exists (Ratan2 (B2R (Interval.inf_raw y)) (B2R (Interval.sup_raw x))).
    split; [|lra].
    exists (B2R (Interval.inf_raw y)), (B2R (Interval.sup_raw x)).
    split; [exact My|]. split; [exact (cl_sup_mem x Vx Ex Fb)|].
    split; [left; intros E; lra | reflexivity].
Qed.

(** The upper lane at [(d, a)] for [a >= 0] and [d > 0] or +inf, or [d = 0]
    with [a > 0]. For a finite [d], every value is at most [Ratan2 d a],
    which is attained: for [t > 0], [Ratan2 r t <= Ratan2 d t] as [atan2]
    increases in [y], and [Ratan2 d t <= Ratan2 d a] as it decreases in [x]
    for [d > 0] (for [d = 0], both are 0); for [t = 0], [a = 0] and the
    value is at most [PI / 2 = Ratan2 d 0]. For [d = +inf], every value is
    at most [PI / 2], the limit at [(+inf, a)]. *)
Lemma arr_hi_da :
  forall emin emax m y x,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  valid y -> valid x -> Interval.is_empty y = false -> Interval.is_empty x = false ->
  is_finite (Interval.inf_raw x) = true -> 0 <= B2R (Interval.inf_raw x) ->
  pos_lane (Interval.sup_raw y) \/
  (is_finite (Interval.sup_raw y) = true /\ B2R (Interval.sup_raw y) = 0 /\
   0 < B2R (Interval.inf_raw x)) ->
  lane_ok (image2_set atan2_dom Ratan2 y x)
    (atan2_ru m (Interval.sup_raw y) (Interval.inf_raw x)).
Proof.
intros emin emax m y x Hrg Hg Hok Vy Vx Ey Ex Fa Ha Hd.
assert (Lx : forall t, mem t x -> B2R (Interval.inf_raw x) <= t)
  by (intros t Ht; exact (cl_mem_inf x t Vx Ex Fa Ht)).
pose proof (cl_inf_mem x Vx Ex Fa) as Mx.
destruct Hd as [[Ed | (Fd & Hd)] | (Fd & Hd0 & Ha0)].
- (* [d = +inf]. *)
  apply (at_hi_lane emin emax m (image2_set atan2_dom Ratan2 y x) _ _ Hrg Hg Hok).
  + rewrite Ed. unfold at_args. split; [reflexivity|].
    split; [exact (arr_fin_nan _ Fa)|]. split; [right; exact Fa|].
    intros F _. discriminate F.
  + rewrite Ed, at_val_y_pinf. intros s (r & t & Hr & Ht & Hdm & ->).
    apply arr_le_half; [specialize (Lx t Ht); lra | exact Hdm].
  + rewrite Ed, at_val_y_pinf. intros eps He.
    destruct (arr_ex y Vy Ey) as (r0 & Hr0).
    destruct (Ratan2_y_pinf (B2R (Interval.inf_raw x)) eps r0 He)
      as (r & Hrr & Hr & Hlt).
    exists (Ratan2 r (B2R (Interval.inf_raw x))). split; [|exact Hlt].
    exists r, (B2R (Interval.inf_raw x)).
    split; [exact (arr_mem_up y r0 r Vy Ey Ed Hr0 Hrr)|]. split; [exact Mx|].
    split; [left; intros E; lra | reflexivity].
- (* [d > 0] finite. *)
  apply (at_hi_lane emin emax m (image2_set atan2_dom Ratan2 y x) _ _ Hrg Hg Hok).
  + unfold at_args. split; [exact (arr_fin_nan _ Fd)|].
    split; [exact (arr_fin_nan _ Fa)|]. split; [left; exact Fd|].
    intros _ H0. lra.
  + rewrite (at_val_fin _ _ Fd Fa). intros s (r & t & Hr & Ht & Hdm & ->).
    pose proof (cl_mem_sup y r Vy Ey Fd Hr) as Hrd. pose proof (Lx t Ht) as Hat.
    assert (Ht0 : 0 <= t) by lra.
    destruct (Rle_lt_or_eq_dec 0 t Ht0) as [Ht1 | Ht1].
    * apply Rle_trans with (Ratan2 (B2R (Interval.sup_raw y)) t).
      -- exact (Ratan2_inc_y _ _ _ Ht1 Hrd).
      -- exact (Ratan2_dec_x _ _ _ Hd Hat).
    * subst t. assert (HA0 : B2R (Interval.inf_raw x) = 0) by lra.
      rewrite HA0, (Ratan2_zero_x_pos _ Hd). apply arr_le_half; [lra | exact Hdm].
  + rewrite (at_val_fin _ _ Fd Fa). intros eps He.
    exists (Ratan2 (B2R (Interval.sup_raw y)) (B2R (Interval.inf_raw x))).
    split; [|lra].
    exists (B2R (Interval.sup_raw y)), (B2R (Interval.inf_raw x)).
    split; [exact (cl_sup_mem y Vy Ey Fd)|]. split; [exact Mx|].
    split; [left; intros E; lra | reflexivity].
- (* [d = 0], [a > 0]: [y <= 0], and every value is at most
     [Ratan2 0 t = 0 = Ratan2 0 a]. *)
  apply (at_hi_lane emin emax m (image2_set atan2_dom Ratan2 y x) _ _ Hrg Hg Hok).
  + unfold at_args. split; [exact (arr_fin_nan _ Fd)|].
    split; [exact (arr_fin_nan _ Fa)|]. split; [left; exact Fd|].
    intros _ _. right; split; [exact Fa | exact Ha0].
  + rewrite (at_val_fin _ _ Fd Fa), Hd0, (Ratan2_zero_y_pos _ Ha0).
    intros s (r & t & Hr & Ht & Hdm & ->).
    pose proof (cl_mem_sup y r Vy Ey Fd Hr) as Hrd. pose proof (Lx t Ht) as Hat.
    rewrite <- (Ratan2_zero_y_pos t) by lra. apply Ratan2_inc_y; lra.
  + rewrite (at_val_fin _ _ Fd Fa). intros eps He.
    exists (Ratan2 (B2R (Interval.sup_raw y)) (B2R (Interval.inf_raw x))).
    split; [|lra].
    exists (B2R (Interval.sup_raw y)), (B2R (Interval.inf_raw x)).
    split; [exact (cl_sup_mem y Vy Ey Fd)|]. split; [exact Mx|].
    split; [right; intros E; lra | reflexivity].
Qed.

(** The lower lane at [(c, a)] for [a > 0] and [c < 0] or -inf. For a
    finite [c], every value is at least [Ratan2 c a], which is attained:
    [Ratan2 c a <= Ratan2 c t] as [atan2] increases in [x] for [c < 0],
    and [Ratan2 c t <= Ratan2 r t] as it increases in [y] for [t > 0]. For
    [c = -inf], every value is above [- (PI / 2)], the limit at
    [(-inf, a)]. *)
Lemma arr_lo_ca :
  forall emin emax m y x,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  valid y -> valid x -> Interval.is_empty y = false -> Interval.is_empty x = false ->
  is_finite (Interval.inf_raw x) = true -> 0 < B2R (Interval.inf_raw x) ->
  Interval.inf_raw y = B754_infinity true \/
  (is_finite (Interval.inf_raw y) = true /\ B2R (Interval.inf_raw y) < 0) ->
  lane_ok (fun s => image2_set atan2_dom Ratan2 y x (- s))
    (opp (atan2_rd m (Interval.inf_raw y) (Interval.inf_raw x))).
Proof.
intros emin emax m y x Hrg Hg Hok Vy Vx Ey Ex Fa Ha Hc.
assert (Lx : forall t, mem t x -> B2R (Interval.inf_raw x) <= t)
  by (intros t Ht; exact (cl_mem_inf x t Vx Ex Fa Ht)).
pose proof (cl_inf_mem x Vx Ex Fa) as Mx.
destruct Hc as [Ec | (Fc & Hc)].
- (* [c = -inf]. *)
  apply (at_lo_lane emin emax m (image2_set atan2_dom Ratan2 y x) _ _ Hrg Hg Hok).
  + rewrite Ec. unfold at_args. split; [reflexivity|].
    split; [exact (arr_fin_nan _ Fa)|]. split; [right; exact Fa|].
    intros F _. discriminate F.
  + rewrite Ec, at_val_y_ninf. intros s (r & t & Hr & Ht & Hdm & ->).
    assert (Ht0 : 0 < t) by (specialize (Lx t Ht); lra).
    pose proof (Ratan2_right r t Ht0). lra.
  + rewrite Ec, at_val_y_ninf. intros eps He.
    destruct (arr_ex y Vy Ey) as (r0 & Hr0).
    destruct (Ratan2_y_ninf (B2R (Interval.inf_raw x)) eps r0 He)
      as (r & Hrr & Hr & Hlt).
    exists (Ratan2 r (B2R (Interval.inf_raw x))). split; [|exact Hlt].
    exists r, (B2R (Interval.inf_raw x)).
    split; [exact (arr_mem_down y r0 r Vy Ey Ec Hr0 Hrr)|]. split; [exact Mx|].
    split; [left; intros E; lra | reflexivity].
- (* [c < 0] finite. *)
  apply (at_lo_lane emin emax m (image2_set atan2_dom Ratan2 y x) _ _ Hrg Hg Hok).
  + unfold at_args. split; [exact (arr_fin_nan _ Fc)|].
    split; [exact (arr_fin_nan _ Fa)|]. split; [left; exact Fc|].
    intros _ H0. lra.
  + rewrite (at_val_fin _ _ Fc Fa). intros s (r & t & Hr & Ht & Hdm & ->).
    pose proof (cl_mem_inf y r Vy Ey Fc Hr) as Hcr. pose proof (Lx t Ht) as Hat.
    apply Rle_trans with (Ratan2 (B2R (Interval.inf_raw y)) t).
    * exact (Ratan2_inc_x _ _ _ Hc Hat).
    * apply Ratan2_inc_y; lra.
  + rewrite (at_val_fin _ _ Fc Fa). intros eps He.
    exists (Ratan2 (B2R (Interval.inf_raw y)) (B2R (Interval.inf_raw x))).
    split; [|lra].
    exists (B2R (Interval.inf_raw y)), (B2R (Interval.inf_raw x)).
    split; [exact (cl_inf_mem y Vy Ey Fc)|]. split; [exact Mx|].
    split; [left; intros E; lra | reflexivity].
Qed.

(** The upper lane at [(c, a)] for [c > 0] and [a < 0] or -inf. For a
    finite [a], every value is at most [Ratan2 c a], which is attained:
    [Ratan2 r t <= Ratan2 r a] as [atan2] decreases in [x] for [r > 0],
    and [Ratan2 r a <= Ratan2 c a] as it decreases in [y >= 0] for
    [x = a < 0]. For [a = -inf], every value is below [PI], the limit at
    [(c, -inf)]. *)
Lemma arr_hi_ca :
  forall emin emax m y x,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  valid y -> valid x -> Interval.is_empty y = false -> Interval.is_empty x = false ->
  is_finite (Interval.inf_raw y) = true -> 0 < B2R (Interval.inf_raw y) ->
  Interval.inf_raw x = B754_infinity true \/
  (is_finite (Interval.inf_raw x) = true /\ B2R (Interval.inf_raw x) < 0) ->
  lane_ok (image2_set atan2_dom Ratan2 y x)
    (atan2_ru m (Interval.inf_raw y) (Interval.inf_raw x)).
Proof.
intros emin emax m y x Hrg Hg Hok Vy Vx Ey Ex Fc Hc Ha.
assert (Ly : forall r, mem r y -> B2R (Interval.inf_raw y) <= r)
  by (intros r Hr; exact (cl_mem_inf y r Vy Ey Fc Hr)).
pose proof (cl_inf_mem y Vy Ey Fc) as My.
destruct Ha as [Ea | (Fa & Ha)].
- (* [a = -inf]. *)
  apply (at_hi_lane emin emax m (image2_set atan2_dom Ratan2 y x) _ _ Hrg Hg Hok).
  + rewrite Ea. unfold at_args. split; [exact (arr_fin_nan _ Fc)|].
    split; [reflexivity|]. split; [left; exact Fc|].
    intros _ H0. lra.
  + rewrite Ea, (at_val_x_ninf_pos _ Fc Hc). intros s (r & t & Hr & Ht & Hdm & ->).
    assert (Hr0 : 0 < r) by (specialize (Ly r Hr); lra).
    pose proof (Ratan2_upper r t Hr0). lra.
  + rewrite Ea, (at_val_x_ninf_pos _ Fc Hc). intros eps He.
    destruct (arr_ex x Vx Ex) as (t0 & Ht0).
    destruct (Ratan2_x_ninf_pos (B2R (Interval.inf_raw y)) eps t0 Hc He)
      as (t & Htt & Ht & Hlt).
    exists (Ratan2 (B2R (Interval.inf_raw y)) t). split; [|exact Hlt].
    exists (B2R (Interval.inf_raw y)), t.
    split; [exact My|]. split; [exact (arr_mem_down x t0 t Vx Ex Ea Ht0 Htt)|].
    split; [left; intros E; lra | reflexivity].
- (* [a < 0] finite. *)
  apply (at_hi_lane emin emax m (image2_set atan2_dom Ratan2 y x) _ _ Hrg Hg Hok).
  + unfold at_args. split; [exact (arr_fin_nan _ Fc)|].
    split; [exact (arr_fin_nan _ Fa)|]. split; [left; exact Fc|].
    intros _ H0. lra.
  + rewrite (at_val_fin _ _ Fc Fa). intros s (r & t & Hr & Ht & Hdm & ->).
    pose proof (Ly r Hr) as Hcr. pose proof (cl_mem_inf x t Vx Ex Fa Ht) as Hat.
    apply Rle_trans with (Ratan2 r (B2R (Interval.inf_raw x))).
    * apply Ratan2_dec_x; lra.
    * apply Ratan2_dec_y_ge; lra.
  + rewrite (at_val_fin _ _ Fc Fa). intros eps He.
    exists (Ratan2 (B2R (Interval.inf_raw y)) (B2R (Interval.inf_raw x))).
    split; [|lra].
    exists (B2R (Interval.inf_raw y)), (B2R (Interval.inf_raw x)).
    split; [exact My|]. split; [exact (cl_inf_mem x Vx Ex Fa)|].
    split; [left; intros E; lra | reflexivity].
Qed.

(** ** The cases *)

(** [at2_q1] from the bounds: [c, a >= 0], not both 0, an upper bound [b]
    above 0 or +inf, or 0 only if [c > 0], and [d] likewise with [a]. *)
Lemma arr_q1 :
  forall emin emax m y x,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  valid y -> valid x -> Interval.is_empty y = false -> Interval.is_empty x = false ->
  is_finite (Interval.inf_raw y) = true -> 0 <= B2R (Interval.inf_raw y) ->
  is_finite (Interval.inf_raw x) = true -> 0 <= B2R (Interval.inf_raw x) ->
  0 < B2R (Interval.inf_raw y) \/ 0 < B2R (Interval.inf_raw x) ->
  pos_lane (Interval.sup_raw x) \/
  (is_finite (Interval.sup_raw x) = true /\ B2R (Interval.sup_raw x) = 0 /\
   0 < B2R (Interval.inf_raw y)) ->
  pos_lane (Interval.sup_raw y) \/
  (is_finite (Interval.sup_raw y) = true /\ B2R (Interval.sup_raw y) = 0 /\
   0 < B2R (Interval.inf_raw x)) ->
  is_tightest (image2_set atan2_dom Ratan2 y x)
    (Interval.with_infsup_raw (atan2_rd m (Interval.inf_raw y) (Interval.sup_raw x))
       (atan2_ru m (Interval.sup_raw y) (Interval.inf_raw x))).
Proof.
intros emin emax m y x Hrg Hg Hok Vy Vx Ey Ex Fc Hc Fa Ha Hca Hb Hd.
unfold Interval.with_infsup_raw, Generic.constant. apply tightest_lanes_lub.
- exact (arr_nonempty y x _ _ (cl_inf_mem y Vy Ey Fc) (cl_inf_mem x Vx Ex Fa) Hca).
- exact (arr_lo_cb emin emax m y x Hrg Hg Hok Vy Vx Ey Ex Fc Hc Hb).
- exact (arr_hi_da emin emax m y x Hrg Hg Hok Vy Vx Ey Ex Fa Ha Hd).
Qed.

Lemma at2_q1 :
  forall emin emax m y x cx cy,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  valid y -> valid x ->
  Interval.classify x = Some cx -> Interval.classify y = Some cy ->
  (cx = CP0 /\ cy = CP1) \/ (cx = CP1 /\ (cy = CP0 \/ cy = CP1 \/ cy = CZ)) \/
  (cx = CZ /\ cy = CP1) ->
  is_tightest (image2_set atan2_dom Ratan2 y x)
    (Interval.with_infsup_raw (atan2_rd m (Interval.inf_raw y) (Interval.sup_raw x))
       (atan2_ru m (Interval.sup_raw y) (Interval.inf_raw x))).
Proof.
intros emin emax m y x cx cy Hrg Hg Hok Vy Vx Cx Cy Hcl.
destruct Hcl as [[-> ->] | [[-> [-> | [-> | ->]]] | [-> ->]]].
- (* [P0_P1]: [y > 0]. *)
  destruct (arr_cls x CP0 Vx Cx) as (Ex & Fa & Ha & Pb).
  destruct (arr_cls y CP1 Vy Cy) as (Ey & Fc & Hc & Pd).
  apply (arr_q1 emin emax m y x Hrg Hg Hok Vy Vx Ey Ex Fc);
    [lra | exact Fa | lra | left; exact Hc | left; exact Pb | left; exact Pd].
- (* [P1_P0]: [x > 0]. *)
  destruct (arr_cls x CP1 Vx Cx) as (Ex & Fa & Ha & Pb).
  destruct (arr_cls y CP0 Vy Cy) as (Ey & Fc & Hc & Pd).
  apply (arr_q1 emin emax m y x Hrg Hg Hok Vy Vx Ey Ex Fc);
    [lra | exact Fa | lra | right; exact Ha | left; exact Pb | left; exact Pd].
- (* [P1_P1]. *)
  destruct (arr_cls x CP1 Vx Cx) as (Ex & Fa & Ha & Pb).
  destruct (arr_cls y CP1 Vy Cy) as (Ey & Fc & Hc & Pd).
  apply (arr_q1 emin emax m y x Hrg Hg Hok Vy Vx Ey Ex Fc);
    [lra | exact Fa | lra | right; exact Ha | left; exact Pb | left; exact Pd].
- (* [P1_Z]: [x > 0], [y = {0}], [d = 0]. *)
  destruct (arr_cls x CP1 Vx Cx) as (Ex & Fa & Ha & Pb).
  destruct (arr_cls y CZ Vy Cy) as (Ey & Fc & Hc & Fd & Hd).
  apply (arr_q1 emin emax m y x Hrg Hg Hok Vy Vx Ey Ex Fc);
    [lra | exact Fa | lra | right; exact Ha | left; exact Pb |
     right; split; [exact Fd | split; [exact Hd | exact Ha]]].
- (* [Z_P1]: [x = {0}], [b = 0], [y > 0]. *)
  destruct (arr_cls x CZ Vx Cx) as (Ex & Fa & Ha & Fb & Hb).
  destruct (arr_cls y CP1 Vy Cy) as (Ey & Fc & Hc & Pd).
  apply (arr_q1 emin emax m y x Hrg Hg Hok Vy Vx Ey Ex Fc);
    [lra | exact Fa | lra | left; exact Hc |
     right; split; [exact Fb | split; [exact Hb | exact Hc]] | left; exact Pd].
Qed.

Lemma at2_mp1 :
  forall emin emax m y x,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  valid y -> valid x ->
  Interval.classify x = Some CM -> Interval.classify y = Some CP1 ->
  is_tightest (image2_set atan2_dom Ratan2 y x)
    (Interval.with_infsup_raw (atan2_rd m (Interval.inf_raw y) (Interval.sup_raw x))
       (atan2_ru m (Interval.inf_raw y) (Interval.inf_raw x))).
Proof.
intros emin emax m y x Hrg Hg Hok Vy Vx Cx Cy.
destruct (arr_cls x CM Vx Cx) as (Ex & Ha & Pb).
destruct (arr_cls y CP1 Vy Cy) as (Ey & Fc & Hc & Pd).
destruct (arr_ex x Vx Ex) as (t0 & Ht0).
unfold Interval.with_infsup_raw, Generic.constant. apply tightest_lanes_lub.
- exact (arr_nonempty y x _ _ (cl_inf_mem y Vy Ey Fc) Ht0 (or_introl Hc)).
- apply (arr_lo_cb emin emax m y x Hrg Hg Hok Vy Vx Ey Ex Fc); [lra | left; exact Pb].
- exact (arr_hi_ca emin emax m y x Hrg Hg Hok Vy Vx Ey Ex Fc Hc Ha).
Qed.

Lemma at2_p1m :
  forall emin emax m y x,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  valid y -> valid x ->
  Interval.classify x = Some CP1 -> Interval.classify y = Some CM ->
  is_tightest (image2_set atan2_dom Ratan2 y x)
    (Interval.with_infsup_raw (atan2_rd m (Interval.inf_raw y) (Interval.inf_raw x))
       (atan2_ru m (Interval.sup_raw y) (Interval.inf_raw x))).
Proof.
intros emin emax m y x Hrg Hg Hok Vy Vx Cx Cy.
destruct (arr_cls x CP1 Vx Cx) as (Ex & Fa & Ha & Pb).
destruct (arr_cls y CM Vy Cy) as (Ey & Hc & Pd).
destruct (arr_ex y Vy Ey) as (r0 & Hr0).
unfold Interval.with_infsup_raw, Generic.constant. apply tightest_lanes_lub.
- exact (arr_nonempty y x _ _ Hr0 (cl_inf_mem x Vx Ex Fa) (or_intror Ha)).
- exact (arr_lo_ca emin emax m y x Hrg Hg Hok Vy Vx Ey Ex Fa Ha Hc).
- apply (arr_hi_da emin emax m y x Hrg Hg Hok Vy Vx Ey Ex Fa); [lra | left; exact Pd].
Qed.
