(** * [Interval::atan2] left of the [y] axis

    As in [Atan2Right.v]: [y] is [self] with bounds [c] and [d], [x] is
    [rhs] with bounds [a] and [b], and the class of [x] comes first.
    - [at2_q2], [N0_P1] and [N1_P1]: [x <= 0], [y > 0], where [atan2]
      decreases in [x], and in [y] for [x < 0] (it is [PI/2] for [x = 0]):
      least at [(d, b)], greatest at [(c, a)];
    - [at2_q3], [N0_N1] and [N1_N1]: [x <= 0], [y < 0], where it increases
      in [x] and decreases in [y] for [x < 0]: least at [(d, a)], greatest
      at [(c, b)];
    - [at2_n1p0], [N1_P0]: [x < 0], [y >= 0] with [0] in [y]: least at
      [(d, b)] as in [at2_q2], and greatest [PI], at [(0, t)].
    A corner at an infinity gives a limit, which [at_val] is. Each case is
    proved for a box given by four floats ([alf_box]), and the lemmas
    [alf_lo_db], [alf_hi_ca], [alf_lo_da], [alf_hi_cb] and [alf_hi_pi]
    give one lane each. *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Integer Sign MaxMin AddSub DivTight
  MpfrRound MonoInc Classes ClosedDom AtanReal PiTight Atan2Mpfr.

Open Scope R_scope.

(** ** The box *)

(** The reals [r] between [c] and [d], and [t] between [a] and [b], where
    an infinite bound bounds nothing. *)
Definition alf_box (a b c d : f64) (r t : R) : Prop :=
  (is_finite c = true -> B2R c <= r) /\ (is_finite d = true -> r <= B2R d) /\
  (is_finite a = true -> B2R a <= t) /\ (is_finite b = true -> t <= B2R b).

Lemma alf_mem :
  forall z r, valid z -> Interval.is_empty z = false ->
  mem r z <->
  (is_finite (Interval.inf_raw z) = true -> B2R (Interval.inf_raw z) <= r) /\
  (is_finite (Interval.sup_raw z) = true -> r <= B2R (Interval.sup_raw z)).
Proof.
intros z r Hz E. rewrite (cl_mem_iff z r Hz E). unfold in_bounds, bound.
destruct (is_finite (Interval.inf_raw z)), (is_finite (Interval.sup_raw z));
  cbv beta iota; split; intros [H0 H1]; split;
  first
    [ exact I | intros _; assumption | intros H; discriminate H
    | apply H0; reflexivity | apply H1; reflexivity ].
Qed.

(** The finite bounds of a nonempty interval are ordered. *)
Lemma alf_ord :
  forall z, valid z -> Interval.is_empty z = false ->
  is_finite (Interval.inf_raw z) = true -> is_finite (Interval.sup_raw z) = true ->
  B2R (Interval.inf_raw z) <= B2R (Interval.sup_raw z).
Proof.
intros z Hz E Fa Fb. destruct (valid_nonempty z Hz E) as (_ & _ & O).
change (opp (fst (rep z))) with (Interval.inf_raw z) in O.
change (snd (rep z)) with (Interval.sup_raw z) in O.
rewrite (bound_finite _ Fa), (bound_finite _ Fb) in O. exact O.
Qed.

Lemma alf_img_out :
  forall y x, valid y -> valid x ->
  Interval.is_empty y = false -> Interval.is_empty x = false ->
  forall s, image2_set atan2_dom Ratan2 y x s ->
  exists r t,
    alf_box (Interval.inf_raw x) (Interval.sup_raw x) (Interval.inf_raw y)
      (Interval.sup_raw y) r t /\
    atan2_dom r t /\ s = Ratan2 r t.
Proof.
intros y x Vy Vx Ey Ex s (r & t & Hr & Ht & D & ->). exists r, t.
apply (alf_mem y r Vy Ey) in Hr. apply (alf_mem x t Vx Ex) in Ht.
destruct Hr as [Hr0 Hr1], Ht as [Ht0 Ht1].
exact (conj (conj Hr0 (conj Hr1 (conj Ht0 Ht1))) (conj D eq_refl)).
Qed.

Lemma alf_img_in :
  forall y x, valid y -> valid x ->
  Interval.is_empty y = false -> Interval.is_empty x = false ->
  forall r t,
  alf_box (Interval.inf_raw x) (Interval.sup_raw x) (Interval.inf_raw y)
    (Interval.sup_raw y) r t ->
  atan2_dom r t -> image2_set atan2_dom Ratan2 y x (Ratan2 r t).
Proof.
intros y x Vy Vx Ey Ex r t (B0 & B1 & B2 & B3) D. exists r, t.
split; [apply (alf_mem y r Vy Ey); exact (conj B0 B1)|].
split; [apply (alf_mem x t Vx Ex); exact (conj B2 B3)|].
exact (conj D eq_refl).
Qed.

(** A lower bound held by a [pos_lane], i.e. [-a > 0] or [+inf], is -inf
    or a finite float below 0. *)
Lemma alf_inf_pos :
  forall z, pos_lane (fst (rep z)) ->
  Interval.inf_raw z = B754_infinity true \/
  (is_finite (Interval.inf_raw z) = true /\ B2R (Interval.inf_raw z) < 0).
Proof.
intros z [E|[F P]]; unfold Interval.inf_raw.
- left. rewrite E. reflexivity.
- right. rewrite is_finite_opp, B2R_opp. split; [exact F | lra].
Qed.

(** ** Real facts *)

Lemma alf_lt0 : forall t, t <= 0 -> t <> 0 -> t < 0.
Proof.
intros t H1 H2. destruct (Rle_lt_or_eq_dec t 0 H1); [assumption | contradiction].
Qed.

Lemma alf_gt0 : forall r, 0 <= r -> r <> 0 -> 0 < r.
Proof.
intros r H1 H2. destruct (Rle_lt_or_eq_dec 0 r H1) as [H|H]; [exact H|].
symmetry in H. contradiction.
Qed.

(** Left of the [y] axis, [Ratan2] is its value at the mirror point [-t]
    reflected about [PI / 2] above the [x] axis, and about [- (PI / 2)]
    below it: [atan (r / t) ± PI] and [atan (r / - t) = - atan (r / t)].
    This turns the limits as [r] goes to +inf or -inf right of the [y] axis
    into those left of it, from the other side. *)
Lemma alf_refl_ge : forall r t, t < 0 -> 0 <= r -> Ratan2 r t = PI - Ratan2 r (- t).
Proof.
intros r t Ht Hr. rewrite (Ratan2_neg_x_ge r t Ht Hr), (Ratan2_pos_x r (- t)) by lra.
replace (r / - t) with (- (r / t)) by (field; lra). rewrite atan_opp. ring.
Qed.

Lemma alf_refl_lt : forall r t, t < 0 -> r < 0 -> Ratan2 r t = - PI - Ratan2 r (- t).
Proof.
intros r t Ht Hr. rewrite (Ratan2_neg_x_lt r t Ht Hr), (Ratan2_pos_x r (- t)) by lra.
replace (r / - t) with (- (r / t)) by (field; lra). rewrite atan_opp. ring.
Qed.

(** ** The lanes for a box *)

(** The lower lane at [(d, b)] for [r >= c >= 0] and [t <= b <= 0], and
    [c > 0] if [b = 0]: [r = 0] gives [PI], the largest value, and [r > 0]
    decreases in [t] and then in [r] (it is [PI / 2] if [b = 0]). For
    [d = +inf] the values are at least [PI / 2] (the second quadrant), and
    come as close to it as asked at [(r, b)] for a large [r], or at
    [(c, 0)]. *)
Lemma alf_lo_db :
  forall emin emax m (S : R -> Prop) a b c d,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  (forall s, S s -> exists r t, alf_box a b c d r t /\ atan2_dom r t /\ s = Ratan2 r t) ->
  (forall r t, alf_box a b c d r t -> atan2_dom r t -> S (Ratan2 r t)) ->
  (is_finite a = true -> B2R a <= B2R b) ->
  (is_finite d = true -> B2R c <= B2R d) ->
  is_finite c = true -> 0 <= B2R c ->
  d = B754_infinity false \/ (is_finite d = true /\ 0 < B2R d) ->
  is_finite b = true -> B2R b <= 0 -> (B2R b = 0 -> 0 < B2R c) ->
  lane_ok (fun s => S (- s)) (opp (atan2_rd m d b)).
Proof.
intros emin emax m S a b c d Hr Hg Ha HS1 HS2 Oab Ocd Fc Pc Hd Fb Nb Hb0.
destruct Hd as [-> | (Fd & Pd)].
- apply (at_lo_lane emin emax m S (B754_infinity false) b Hr Hg Ha).
  + split; [reflexivity|]. split; [exact (not_nan_upper _ (or_introl Fb))|].
    split; [right; exact Fb|]. intros F. discriminate F.
  + rewrite at_val_y_pinf. intros s Hs.
    destruct (HS1 s Hs) as (r & t & (B0 & _ & _ & B3) & D & ->).
    specialize (B0 Fc). specialize (B3 Fb).
    assert (Q : PI / 2 <= Ratan2 r t <= PI) by (apply Ratan2_q2; [lra | lra | exact D]).
    lra.
  + rewrite at_val_y_pinf. intros eps He.
    destruct (Rlt_or_le (B2R b) 0) as [Lb|Lb].
    * (* [Ratan2 r b = PI - Ratan2 r (-b)], and the latter tends to
         [PI / 2] from below as [r] goes to +inf. *)
      destruct (Ratan2_y_pinf (- B2R b) eps (B2R c) He) as (r & R1 & R2 & R3).
      exists (Ratan2 r (B2R b)). split.
      -- apply HS2; [|left; lra].
         refine (conj _ (conj _ (conj _ _))).
         ++ intros _. exact R1.
         ++ intros F. discriminate F.
         ++ exact Oab.
         ++ intros _. apply Rle_refl.
      -- rewrite (alf_refl_ge r (B2R b)) by lra. lra.
    * (* [b = 0]: the value [PI / 2] at [(c, 0)]. *)
      assert (Eb : B2R b = 0) by lra. specialize (Hb0 Eb).
      exists (Ratan2 (B2R c) (B2R b)). split.
      -- apply HS2; [|left; lra].
         refine (conj _ (conj _ (conj _ _))).
         ++ intros _. apply Rle_refl.
         ++ intros F. discriminate F.
         ++ exact Oab.
         ++ intros _. apply Rle_refl.
      -- rewrite Eb, Ratan2_zero_x_pos by exact Hb0. lra.
- apply (at_lo_lane emin emax m S d b Hr Hg Ha).
  + split; [exact (not_nan_upper _ (or_introl Fd))|].
    split; [exact (not_nan_upper _ (or_introl Fb))|].
    split; [left; exact Fd|]. intros _ E. lra.
  + rewrite (at_val_fin d b Fd Fb). intros s Hs.
    destruct (HS1 s Hs) as (r & t & (B0 & B1 & _ & B3) & D & ->).
    specialize (B0 Fc). specialize (B1 Fd). specialize (B3 Fb).
    assert (Rg := Ratan2_range (B2R d) (B2R b) (or_introl (Rgt_not_eq _ _ Pd))).
    destruct (Req_dec r 0) as [-> | Nr].
    * (* [(0, t)] with [t < 0]: the value [PI]. *)
      destruct D as [D|D]; [exfalso; apply D; reflexivity|].
      rewrite (Ratan2_zero_y_neg t) by (apply alf_lt0; [lra | exact D]). lra.
    * assert (Pr : 0 < r) by (apply alf_gt0; [lra | exact Nr]).
      assert (H1 : Ratan2 r (B2R b) <= Ratan2 r t) by (apply Ratan2_dec_x; lra).
      assert (H2 : Ratan2 (B2R d) (B2R b) <= Ratan2 r (B2R b)).
      { destruct (Rlt_or_le (B2R b) 0) as [Lb|Lb].
        - apply Ratan2_dec_y_ge; lra.
        - replace (B2R b) with 0 by lra.
          rewrite (Ratan2_zero_x_pos (B2R d) Pd), (Ratan2_zero_x_pos r Pr). lra. }
      lra.
  + rewrite (at_val_fin d b Fd Fb). intros eps He.
    exists (Ratan2 (B2R d) (B2R b)). split; [|lra].
    apply HS2; [|left; lra].
    refine (conj _ (conj _ (conj _ _))).
    * intros _. exact (Ocd Fd).
    * intros _. apply Rle_refl.
    * exact Oab.
    * intros _. apply Rle_refl.
Qed.

(** The upper lane at [(c, a)] for [r >= c > 0] and [t >= a], [a < 0]: the
    values decrease in [t] and then in [r]. For [a = -inf] they are below
    [PI] (the upper half-plane), and come as close to it as asked at
    [(c, t)] for a small [t]. *)
Lemma alf_hi_ca :
  forall emin emax m (S : R -> Prop) a b c d,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  (forall s, S s -> exists r t, alf_box a b c d r t /\ atan2_dom r t /\ s = Ratan2 r t) ->
  (forall r t, alf_box a b c d r t -> atan2_dom r t -> S (Ratan2 r t)) ->
  (is_finite a = true -> B2R a <= B2R b) ->
  (is_finite d = true -> B2R c <= B2R d) ->
  is_finite c = true -> 0 < B2R c ->
  a = B754_infinity true \/ (is_finite a = true /\ B2R a < 0) ->
  is_finite b = true ->
  lane_ok S (atan2_ru m c a).
Proof.
intros emin emax m S a b c d Hr Hg Ha HS1 HS2 Oab Ocd Fc Pc Hao Fb.
destruct Hao as [-> | (Fa & Na)].
- apply (at_hi_lane emin emax m S c (B754_infinity true) Hr Hg Ha).
  + split; [exact (not_nan_upper _ (or_introl Fc))|]. split; [reflexivity|].
    split; [left; exact Fc|]. intros _ E. lra.
  + rewrite (at_val_x_ninf_pos c Fc Pc). intros s Hs.
    destruct (HS1 s Hs) as (r & t & (B0 & _ & _ & _) & _ & ->). specialize (B0 Fc).
    assert (U : 0 < Ratan2 r t < PI) by (apply Ratan2_upper; lra). lra.
  + rewrite (at_val_x_ninf_pos c Fc Pc). intros eps He.
    destruct (Ratan2_x_ninf_pos (B2R c) eps (B2R b) Pc He) as (t & T1 & T2 & T3).
    exists (Ratan2 (B2R c) t). split; [|lra].
    apply HS2; [|left; lra].
    refine (conj _ (conj _ (conj _ _))).
    * intros _. apply Rle_refl.
    * exact Ocd.
    * intros F. discriminate F.
    * intros _. exact T1.
- apply (at_hi_lane emin emax m S c a Hr Hg Ha).
  + split; [exact (not_nan_upper _ (or_introl Fc))|].
    split; [exact (not_nan_upper _ (or_introl Fa))|].
    split; [left; exact Fc|]. intros _ E. lra.
  + rewrite (at_val_fin c a Fc Fa). intros s Hs.
    destruct (HS1 s Hs) as (r & t & (B0 & _ & B2 & _) & _ & ->).
    specialize (B0 Fc). specialize (B2 Fa).
    assert (H1 : Ratan2 r t <= Ratan2 r (B2R a)) by (apply Ratan2_dec_x; lra).
    assert (H2 : Ratan2 r (B2R a) <= Ratan2 (B2R c) (B2R a))
      by (apply Ratan2_dec_y_ge; lra).
    lra.
  + rewrite (at_val_fin c a Fc Fa). intros eps He.
    exists (Ratan2 (B2R c) (B2R a)). split; [|lra].
    apply HS2; [|left; lra].
    refine (conj _ (conj _ (conj _ _))).
    * intros _. apply Rle_refl.
    * exact Ocd.
    * intros _. apply Rle_refl.
    * intros _. exact (Oab Fa).
Qed.

(** The lower lane at [(d, a)] for [r <= d < 0] and [t >= a], [a < 0]:
    the values increase in [t] and decrease in [r]. For [a = -inf] they
    are above [-PI] (the lower half-plane), and come as close to it as
    asked at [(d, t)] for a small [t]. *)
Lemma alf_lo_da :
  forall emin emax m (S : R -> Prop) a b c d,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  (forall s, S s -> exists r t, alf_box a b c d r t /\ atan2_dom r t /\ s = Ratan2 r t) ->
  (forall r t, alf_box a b c d r t -> atan2_dom r t -> S (Ratan2 r t)) ->
  (is_finite a = true -> B2R a <= B2R b) ->
  (is_finite c = true -> B2R c <= B2R d) ->
  is_finite d = true -> B2R d < 0 ->
  a = B754_infinity true \/ (is_finite a = true /\ B2R a < 0) ->
  is_finite b = true ->
  lane_ok (fun s => S (- s)) (opp (atan2_rd m d a)).
Proof.
intros emin emax m S a b c d Hr Hg Ha HS1 HS2 Oab Ocd Fd Nd Hao Fb.
destruct Hao as [-> | (Fa & Na)].
- apply (at_lo_lane emin emax m S d (B754_infinity true) Hr Hg Ha).
  + split; [exact (not_nan_upper _ (or_introl Fd))|]. split; [reflexivity|].
    split; [left; exact Fd|]. intros _ E. lra.
  + rewrite (at_val_x_ninf_neg d Fd Nd). intros s Hs.
    destruct (HS1 s Hs) as (r & t & (_ & B1 & _ & _) & _ & ->). specialize (B1 Fd).
    assert (L : - PI < Ratan2 r t < 0) by (apply Ratan2_lower; lra). lra.
  + rewrite (at_val_x_ninf_neg d Fd Nd). intros eps He.
    destruct (Ratan2_x_ninf_neg (B2R d) eps (B2R b) Nd He) as (t & T1 & T2 & T3).
    exists (Ratan2 (B2R d) t). split; [|lra].
    apply HS2; [|left; lra].
    refine (conj _ (conj _ (conj _ _))).
    * exact Ocd.
    * intros _. apply Rle_refl.
    * intros F. discriminate F.
    * intros _. exact T1.
- apply (at_lo_lane emin emax m S d a Hr Hg Ha).
  + split; [exact (not_nan_upper _ (or_introl Fd))|].
    split; [exact (not_nan_upper _ (or_introl Fa))|].
    split; [left; exact Fd|]. intros _ E. lra.
  + rewrite (at_val_fin d a Fd Fa). intros s Hs.
    destruct (HS1 s Hs) as (r & t & (_ & B1 & B2 & _) & _ & ->).
    specialize (B1 Fd). specialize (B2 Fa).
    assert (H1 : Ratan2 r (B2R a) <= Ratan2 r t) by (apply Ratan2_inc_x; lra).
    assert (H2 : Ratan2 (B2R d) (B2R a) <= Ratan2 r (B2R a))
      by (apply Ratan2_dec_y_lt; lra).
    lra.
  + rewrite (at_val_fin d a Fd Fa). intros eps He.
    exists (Ratan2 (B2R d) (B2R a)). split; [|lra].
    apply HS2; [|left; lra].
    refine (conj _ (conj _ (conj _ _))).
    * exact Ocd.
    * intros _. apply Rle_refl.
    * intros _. apply Rle_refl.
    * intros _. exact (Oab Fa).
Qed.

(** The upper lane at [(c, b)] for [r <= d < 0] and [t <= b <= 0]: the
    values increase in [t] and decrease in [r] (they are [- (PI / 2)] if
    [b = 0]). For [c = -inf] they are at most [- (PI / 2)] (the third
    quadrant), and come as close to it as asked at [(r, b)] for a small
    [r], or at [(d, 0)]. *)
Lemma alf_hi_cb :
  forall emin emax m (S : R -> Prop) a b c d,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  (forall s, S s -> exists r t, alf_box a b c d r t /\ atan2_dom r t /\ s = Ratan2 r t) ->
  (forall r t, alf_box a b c d r t -> atan2_dom r t -> S (Ratan2 r t)) ->
  (is_finite a = true -> B2R a <= B2R b) ->
  (is_finite c = true -> B2R c <= B2R d) ->
  is_finite d = true -> B2R d < 0 ->
  c = B754_infinity true \/ (is_finite c = true /\ B2R c < 0) ->
  is_finite b = true -> B2R b <= 0 ->
  lane_ok S (atan2_ru m c b).
Proof.
intros emin emax m S a b c d Hr Hg Ha HS1 HS2 Oab Ocd Fd Nd Hco Fb Nb.
destruct Hco as [-> | (Fc & Nc)].
- apply (at_hi_lane emin emax m S (B754_infinity true) b Hr Hg Ha).
  + split; [reflexivity|]. split; [exact (not_nan_upper _ (or_introl Fb))|].
    split; [right; exact Fb|]. intros F. discriminate F.
  + rewrite at_val_y_ninf. intros s Hs.
    destruct (HS1 s Hs) as (r & t & (_ & B1 & _ & B3) & _ & ->).
    specialize (B1 Fd). specialize (B3 Fb).
    assert (Q : - PI < Ratan2 r t <= - (PI / 2)) by (apply Ratan2_q3; lra). lra.
  + rewrite at_val_y_ninf. intros eps He.
    destruct (Rlt_or_le (B2R b) 0) as [Lb|Lb].
    * (* [Ratan2 r b = - PI - Ratan2 r (-b)], and the latter tends to
         [- (PI / 2)] from above as [r] goes to -inf. *)
      destruct (Ratan2_y_ninf (- B2R b) eps (B2R d) He) as (r & R1 & R2 & R3).
      exists (Ratan2 r (B2R b)). split.
      -- apply HS2; [|left; lra].
         refine (conj _ (conj _ (conj _ _))).
         ++ intros F. discriminate F.
         ++ intros _. exact R1.
         ++ exact Oab.
         ++ intros _. apply Rle_refl.
      -- rewrite (alf_refl_lt r (B2R b)) by lra. lra.
    * (* [b = 0]: the value [- (PI / 2)] at [(d, 0)]. *)
      assert (Eb : B2R b = 0) by lra.
      exists (Ratan2 (B2R d) (B2R b)). split.
      -- apply HS2; [|left; lra].
         refine (conj _ (conj _ (conj _ _))).
         ++ intros F. discriminate F.
         ++ intros _. apply Rle_refl.
         ++ exact Oab.
         ++ intros _. apply Rle_refl.
      -- rewrite Eb, Ratan2_zero_x_neg by exact Nd. lra.
- apply (at_hi_lane emin emax m S c b Hr Hg Ha).
  + split; [exact (not_nan_upper _ (or_introl Fc))|].
    split; [exact (not_nan_upper _ (or_introl Fb))|].
    split; [left; exact Fc|]. intros _ E. lra.
  + rewrite (at_val_fin c b Fc Fb). intros s Hs.
    destruct (HS1 s Hs) as (r & t & (B0 & B1 & _ & B3) & _ & ->).
    specialize (B0 Fc). specialize (B1 Fd). specialize (B3 Fb).
    assert (H1 : Ratan2 r t <= Ratan2 r (B2R b)) by (apply Ratan2_inc_x; lra).
    assert (H2 : Ratan2 r (B2R b) <= Ratan2 (B2R c) (B2R b)).
    { destruct (Rlt_or_le (B2R b) 0) as [Lb|Lb].
      - apply Ratan2_dec_y_lt; lra.
      - replace (B2R b) with 0 by lra.
        rewrite (Ratan2_zero_x_neg (B2R c) Nc), (Ratan2_zero_x_neg r) by lra. lra. }
    lra.
  + rewrite (at_val_fin c b Fc Fb). intros eps He.
    exists (Ratan2 (B2R c) (B2R b)). split; [|lra].
    apply HS2; [|left; lra].
    refine (conj _ (conj _ (conj _ _))).
    * intros _. apply Rle_refl.
    * intros _. exact (Ocd Fc).
    * exact Oab.
    * intros _. apply Rle_refl.
Qed.

(** The upper lane [PI] for [r >= c = 0] and [t <= b < 0]: [PI] is the
    largest value of [Ratan2], and that at [(0, b)]. *)
Lemma alf_hi_pi :
  forall (S : R -> Prop) a b c d,
  (forall s, S s -> exists r t, alf_box a b c d r t /\ atan2_dom r t /\ s = Ratan2 r t) ->
  (forall r t, alf_box a b c d r t -> atan2_dom r t -> S (Ratan2 r t)) ->
  (is_finite a = true -> B2R a <= B2R b) ->
  (is_finite d = true -> B2R c <= B2R d) ->
  is_finite c = true -> B2R c = 0 ->
  is_finite b = true -> B2R b < 0 ->
  lane_ok S (Interval.sup_raw Interval.PI).
Proof.
intros S a b c d HS1 HS2 Oab Ocd Fc Ec Fb Nb.
exists (Some PI). split; [|exact PI_up].
apply mono_lub_approx.
- intros s Hs. destruct (HS1 s Hs) as (r & t & _ & D & ->).
  exact (proj2 (Ratan2_range r t D)).
- intros eps He. exists (Ratan2 (B2R c) (B2R b)). split.
  + apply HS2; [|right; lra].
    refine (conj _ (conj _ (conj _ _))).
    * intros _. apply Rle_refl.
    * exact Ocd.
    * exact Oab.
    * intros _. apply Rle_refl.
  + rewrite Ec, Ratan2_zero_y_neg by exact Nb. lra.
Qed.

(** ** The cases *)

(** The bounds [a] and [b] of [x] in [N0] or [N1]: [b <= 0], and [a] is
    -inf or below 0. *)
Lemma alf_x_left :
  forall x, valid x ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  pos_lane (fst (rep x)) /\ is_finite (Interval.sup_raw x) = true /\
  B2R (Interval.sup_raw x) <= 0.
Proof.
intros x Vx [Cx|Cx].
- destruct (classify_lanes x CN0 Vx Cx) as (P & F & E).
  split; [exact P|]. split; [exact F|]. change (B2R (snd (rep x)) <= 0). lra.
- destruct (classify_lanes x CN1 Vx Cx) as (P & F & N).
  split; [exact P|]. split; [exact F|]. change (B2R (snd (rep x)) <= 0). lra.
Qed.

Lemma at2_q2 :
  forall emin emax m y x,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  valid y -> valid x ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  Interval.classify y = Some CP1 ->
  is_tightest (image2_set atan2_dom Ratan2 y x)
    (Interval.with_infsup_raw (atan2_rd m (Interval.sup_raw y) (Interval.sup_raw x))
       (atan2_ru m (Interval.inf_raw y) (Interval.inf_raw x))).
Proof.
intros emin emax m y x Hr Hg Ha Vy Vx Cx Cy.
destruct (classify_lanes y CP1 Vy Cy) as (Fy0 & Ny0 & Py1).
destruct (alf_x_left x Vx Cx) as (Px0 & Fb & Nb).
assert (Ey : Interval.is_empty y = false) by exact (not_nan_upper _ (or_introl Fy0)).
assert (Ex : Interval.is_empty x = false)
  by exact (not_nan_upper _ (pos_lane_upper _ Px0)).
assert (Fc : is_finite (Interval.inf_raw y) = true)
  by (unfold Interval.inf_raw; rewrite is_finite_opp; exact Fy0).
assert (Pc : 0 < B2R (Interval.inf_raw y)) by (unfold Interval.inf_raw; rewrite B2R_opp; lra).
assert (Oab := alf_ord x Vx Ex).
assert (Ocd := alf_ord y Vy Ey Fc).
pose proof (alf_img_out y x Vy Vx Ey Ex) as HS1.
pose proof (alf_img_in y x Vy Vx Ey Ex) as HS2.
unfold Interval.with_infsup_raw, Generic.constant. apply tightest_lanes_lub.
- (* [(c, b)] is in the box. *)
  exists (Ratan2 (B2R (Interval.inf_raw y)) (B2R (Interval.sup_raw x))).
  apply HS2; [|left; lra].
  refine (conj _ (conj _ (conj _ _))).
  + intros _. apply Rle_refl.
  + exact Ocd.
  + intros Fa. exact (Oab Fa Fb).
  + intros _. apply Rle_refl.
- apply (alf_lo_db emin emax m _ (Interval.inf_raw x) (Interval.sup_raw x)
    (Interval.inf_raw y) (Interval.sup_raw y) Hr Hg Ha HS1 HS2).
  + intros Fa. exact (Oab Fa Fb).
  + exact Ocd.
  + exact Fc.
  + lra.
  + exact Py1.
  + exact Fb.
  + exact Nb.
  + intros _. exact Pc.
- apply (alf_hi_ca emin emax m _ (Interval.inf_raw x) (Interval.sup_raw x)
    (Interval.inf_raw y) (Interval.sup_raw y) Hr Hg Ha HS1 HS2).
  + intros Fa. exact (Oab Fa Fb).
  + exact Ocd.
  + exact Fc.
  + exact Pc.
  + exact (alf_inf_pos x Px0).
  + exact Fb.
Qed.

Lemma at2_q3 :
  forall emin emax m y x,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  valid y -> valid x ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  Interval.classify y = Some CN1 ->
  is_tightest (image2_set atan2_dom Ratan2 y x)
    (Interval.with_infsup_raw (atan2_rd m (Interval.sup_raw y) (Interval.inf_raw x))
       (atan2_ru m (Interval.inf_raw y) (Interval.sup_raw x))).
Proof.
intros emin emax m y x Hr Hg Ha Vy Vx Cx Cy.
destruct (classify_lanes y CN1 Vy Cy) as (Py0 & Fd & Nd).
change (snd (rep y)) with (Interval.sup_raw y) in Fd, Nd.
destruct (alf_x_left x Vx Cx) as (Px0 & Fb & Nb).
assert (Ey : Interval.is_empty y = false)
  by exact (not_nan_upper _ (pos_lane_upper _ Py0)).
assert (Ex : Interval.is_empty x = false)
  by exact (not_nan_upper _ (pos_lane_upper _ Px0)).
assert (Oab := alf_ord x Vx Ex).
assert (Ocd : is_finite (Interval.inf_raw y) = true ->
              B2R (Interval.inf_raw y) <= B2R (Interval.sup_raw y))
  by (intros Fc; exact (alf_ord y Vy Ey Fc Fd)).
pose proof (alf_img_out y x Vy Vx Ey Ex) as HS1.
pose proof (alf_img_in y x Vy Vx Ey Ex) as HS2.
unfold Interval.with_infsup_raw, Generic.constant. apply tightest_lanes_lub.
- (* [(d, b)] is in the box. *)
  exists (Ratan2 (B2R (Interval.sup_raw y)) (B2R (Interval.sup_raw x))).
  apply HS2; [|left; lra].
  refine (conj _ (conj _ (conj _ _))).
  + exact Ocd.
  + intros _. apply Rle_refl.
  + intros Fa. exact (Oab Fa Fb).
  + intros _. apply Rle_refl.
- apply (alf_lo_da emin emax m _ (Interval.inf_raw x) (Interval.sup_raw x)
    (Interval.inf_raw y) (Interval.sup_raw y) Hr Hg Ha HS1 HS2).
  + intros Fa. exact (Oab Fa Fb).
  + exact Ocd.
  + exact Fd.
  + exact Nd.
  + exact (alf_inf_pos x Px0).
  + exact Fb.
- apply (alf_hi_cb emin emax m _ (Interval.inf_raw x) (Interval.sup_raw x)
    (Interval.inf_raw y) (Interval.sup_raw y) Hr Hg Ha HS1 HS2).
  + intros Fa. exact (Oab Fa Fb).
  + exact Ocd.
  + exact Fd.
  + exact Nd.
  + exact (alf_inf_pos y Py0).
  + exact Fb.
  + exact Nb.
Qed.

Lemma at2_n1p0 :
  forall emin emax m y x,
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  valid y -> valid x ->
  Interval.classify x = Some CN1 -> Interval.classify y = Some CP0 ->
  is_tightest (image2_set atan2_dom Ratan2 y x)
    (Interval.with_infsup_raw (atan2_rd m (Interval.sup_raw y) (Interval.sup_raw x))
       (Interval.sup_raw Interval.PI)).
Proof.
intros emin emax m y x Hr Hg Ha Vy Vx Cx Cy.
destruct (classify_lanes y CP0 Vy Cy) as (Fy0 & Ey0 & Py1).
destruct (classify_lanes x CN1 Vx Cx) as (Px0 & Fb & Nb).
change (snd (rep x)) with (Interval.sup_raw x) in Fb, Nb.
assert (Ey : Interval.is_empty y = false) by exact (not_nan_upper _ (or_introl Fy0)).
assert (Ex : Interval.is_empty x = false)
  by exact (not_nan_upper _ (pos_lane_upper _ Px0)).
assert (Fc : is_finite (Interval.inf_raw y) = true)
  by (unfold Interval.inf_raw; rewrite is_finite_opp; exact Fy0).
assert (Ec : B2R (Interval.inf_raw y) = 0) by (unfold Interval.inf_raw; rewrite B2R_opp; lra).
assert (Oab := alf_ord x Vx Ex).
assert (Ocd := alf_ord y Vy Ey Fc).
pose proof (alf_img_out y x Vy Vx Ey Ex) as HS1.
pose proof (alf_img_in y x Vy Vx Ey Ex) as HS2.
unfold Interval.with_infsup_raw, Generic.constant. apply tightest_lanes_lub.
- (* [(c, b)] = [(0, b)] is in the box. *)
  exists (Ratan2 (B2R (Interval.inf_raw y)) (B2R (Interval.sup_raw x))).
  apply HS2; [|right; lra].
  refine (conj _ (conj _ (conj _ _))).
  + intros _. apply Rle_refl.
  + exact Ocd.
  + intros Fa. exact (Oab Fa Fb).
  + intros _. apply Rle_refl.
- apply (alf_lo_db emin emax m _ (Interval.inf_raw x) (Interval.sup_raw x)
    (Interval.inf_raw y) (Interval.sup_raw y) Hr Hg Ha HS1 HS2).
  + intros Fa. exact (Oab Fa Fb).
  + exact Ocd.
  + exact Fc.
  + lra.
  + exact Py1.
  + exact Fb.
  + lra.
  + intros E. lra.
- apply (alf_hi_pi _ (Interval.inf_raw x) (Interval.sup_raw x)
    (Interval.inf_raw y) (Interval.sup_raw y) HS1 HS2).
  + intros Fa. exact (Oab Fa Fb).
  + exact Ocd.
  + exact Fc.
  + exact Ec.
  + exact Fb.
  + exact Nb.
Qed.
