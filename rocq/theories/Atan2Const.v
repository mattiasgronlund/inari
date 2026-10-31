(** * The cases of [Interval::atan2] whose result is a constant

    [y] is [self], the interval of [y] coordinates, and [x] is [rhs], the
    interval of [x] coordinates, whose class comes first in
    [x.classify2(y)]. In each case below the box is empty, contains
    [(0, 0)], or has [x < 0] and meets the half-line [y = 0], [x < 0]
    ([N1_M], [N1_N0] and [N1_Z]). The image is empty for an empty box and
    for [Z_Z], and otherwise its bounds are among 0, [±PI/2], [PI] and
    [-PI], each the value at a point of the box, or for [-PI] a limit just
    below that half-line.
    [PiTight.v] shows that the bounds of [Interval::PI] and
    [Interval::FRAC_PI_2] round them. *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Integer Sign MaxMin AddSub DivTight
  DecBinary MonoInc Classes AtanReal PiTight.

Open Scope R_scope.

(** ** Helpers *)

(** A point of the box in the domain puts its value in the image. *)
Lemma ac_pt :
  forall y x r t s, mem r y -> mem t x -> atan2_dom r t -> Ratan2 r t = s ->
  image2_set atan2_dom Ratan2 y x s.
Proof.
intros y x r t s Hr Ht Hd Hs. exists r, t.
exact (conj Hr (conj Ht (conj Hd (eq_sym Hs)))).
Qed.

(** A largest element [U] of [T] is its least upper bound, so the least
    float or +inf at or above [U] is the lane of [T]. *)
Lemma ac_lane :
  forall (T : R -> Prop) U w, T U -> (forall s, T s -> s <= U) ->
  least_lane (Some U) w -> lane_ok T w.
Proof.
intros T U w HU Hub Hw. exists (Some U). split; [|exact Hw].
apply mono_lub_approx; [exact Hub|].
intros eps He. exists U. split; [exact HU | lra].
Qed.

(** [least_lane_exact] of [Sqrt.v], for a float of value [c]. *)
Lemma ac_least_lane_val :
  forall w c, is_finite w = true -> B2R w = c -> least_lane (Some c) w.
Proof.
intros w c Fw <-. split; [left; exact Fw|]. rewrite (bound_finite _ Fw).
split; [intros s Hs; exact Hs|].
intros z _ Hz. exact Hz.
Qed.

(** [+0] and [-0] are the least floats at or above 0. *)
Lemma ac_zero_up : least_lane (Some 0) Model.zero.
Proof. apply ac_least_lane_val; reflexivity. Qed.

Lemma ac_zero_dn : least_lane (Some 0) (opp Model.zero).
Proof. apply ac_least_lane_val; reflexivity. Qed.

Lemma ac_opp_opp : forall w : f64, opp (opp w) = w.
Proof. intros w. unfold opp. apply Bopp_involutive. Qed.

(** The first lanes of [Interval::PI] and [Interval::FRAC_PI_2] are the
    negated lower bounds of [PiTight.v]. *)
Lemma ac_PI_dn_rep : least_lane (Some (- PI)) (fst (rep Interval.PI)).
Proof.
pose proof PI_dn as H. unfold Interval.inf_raw in H. rewrite ac_opp_opp in H.
exact H.
Qed.

Lemma ac_FRAC_PI_2_dn_rep :
  least_lane (Some (- (PI / 2))) (fst (rep Interval.FRAC_PI_2)).
Proof.
pose proof FRAC_PI_2_dn as H. unfold Interval.inf_raw in H. rewrite ac_opp_opp in H.
exact H.
Qed.

(** An interval of class [M] holds 0. *)
Lemma ac_cm_zero :
  forall y, valid y -> Interval.classify y = Some CM -> mem 0 y.
Proof.
intros y Hy Hc.
pose proof (classify_mem y CM Hy Hc) as ((u & Hu & Hu0) & (v & Hv & Hv0)).
apply (mem_between y u v 0 Hy Hu Hv). lra.
Qed.

(** A nonzero real on one side of 0 is strictly on that side. *)
Lemma ac_neg_of : forall t, t <= 0 -> t <> 0 -> t < 0.
Proof.
intros t H1 H2. destruct (Rle_lt_or_eq_dec t 0 H1) as [H|H]; [exact H | contradiction].
Qed.

Lemma ac_pos_of : forall t, 0 <= t -> t <> 0 -> 0 < t.
Proof.
intros t H1 H2. destruct (Rle_lt_or_eq_dec 0 t H1) as [H|H]; [exact H|].
symmetry in H. contradiction.
Qed.

(** [Ratan2] on the closed upper and right half-planes. *)
Lemma ac_upper_half :
  forall r t, 0 <= r -> atan2_dom r t -> 0 <= Ratan2 r t <= PI.
Proof.
intros r t Hr Hd. pose proof PI_RGT_0.
destruct (Rle_or_lt 0 t) as [Ht|Ht].
- pose proof (Ratan2_q1 r t Hr Ht Hd). lra.
- pose proof (Ratan2_q2 r t Hr (Rlt_le _ _ Ht) Hd). lra.
Qed.

Lemma ac_right_half :
  forall r t, 0 <= t -> atan2_dom r t -> - (PI / 2) <= Ratan2 r t <= PI / 2.
Proof.
intros r t Ht Hd. pose proof PI_RGT_0.
destruct (Rle_or_lt 0 r) as [Hr|Hr].
- pose proof (Ratan2_q1 r t Hr Ht Hd). lra.
- pose proof (Ratan2_q4 r t (Rlt_le _ _ Hr) Ht Hd). lra.
Qed.

(** A set with a least element [lo] and a largest element [hi] has the
    tightest interval [[a, b]] if [-a] is the least float or +inf at or
    above [-lo], and [b] that at or above [hi]. *)
Lemma ac_range :
  forall (S : R -> Prop) lo hi a b, S lo -> S hi -> (forall s, S s -> lo <= s <= hi) ->
  least_lane (Some (- lo)) (opp a) -> least_lane (Some hi) b ->
  is_tightest S (Interval.with_infsup_raw a b).
Proof.
intros S lo hi a b Hlo Hhi Hb La Lb.
unfold Interval.with_infsup_raw, Generic.constant. apply tightest_lanes_lub.
- exists lo. exact Hlo.
- apply (ac_lane _ (- lo)); [cbv beta; rewrite Ropp_involutive; exact Hlo | | exact La].
  intros s Hs. specialize (Hb _ Hs). lra.
- apply (ac_lane _ hi); [exact Hhi | | exact Lb].
  intros s Hs. specialize (Hb _ Hs). lra.
Qed.

(** A set with the one element [c] has the tightest interval [z] if its
    first lane is the least float or +inf at or above [-c], and its second
    lane that at or above [c]. *)
Lemma ac_single :
  forall (S : R -> Prop) c z, S c -> (forall s, S s -> s = c) ->
  least_lane (Some (- c)) (fst (rep z)) -> least_lane (Some c) (snd (rep z)) ->
  is_tightest S z.
Proof.
intros S c z Hc Hall L0 L1. apply tightest_lanes_lub_rep.
- exists c. exact Hc.
- apply (ac_lane _ (- c)); [cbv beta; rewrite Ropp_involutive; exact Hc | | exact L0].
  intros s Hs. specialize (Hall _ Hs). lra.
- apply (ac_lane _ c); [exact Hc | | exact L1].
  intros s Hs. specialize (Hall _ Hs). lra.
Qed.

(** No point of the domain: [x] or [y] is empty, or both are [{0}]. *)
Lemma at2_empty :
  forall y x cx cy, valid y -> valid x ->
  Interval.classify x = Some cx -> Interval.classify y = Some cy ->
  cx = CE \/ cy = CE \/ (cx = CZ /\ cy = CZ) ->
  is_tightest (image2_set atan2_dom Ratan2 y x) Interval.EMPTY.
Proof.
intros y x cx cy Hy Hx Hcx Hcy Hc. apply tightest_empty.
intros u (r & t & Hr & Ht & Hd & _).
pose proof (classify_mem x cx Hx Hcx) as Mx.
pose proof (classify_mem y cy Hy Hcy) as My.
destruct Hc as [-> | [-> | [-> ->]]].
- exact (Mx t Ht).
- exact (My r Hr).
- (* The only point of the box is [(0, 0)]. *)
  apply (proj1 (Mx t)) in Ht. apply (proj1 (My r)) in Hr. subst r t.
  destruct Hd as [H|H]; apply H; reflexivity.
Qed.

(** [M_M], [M_N0], [N0_M], [N0_N0], [N1_M] and [N1_N0]: [x] has a real
    below 0, and [y] has 0 and a real below it, so the image has [PI],
    at [(0, t)] for [t < 0], and values as close to [-PI] as asked. *)
Lemma at2_full :
  forall y x cx cy, valid y -> valid x ->
  Interval.classify x = Some cx -> Interval.classify y = Some cy ->
  (cx = CM \/ cx = CN0 \/ cx = CN1) -> (cy = CM \/ cy = CN0) ->
  is_tightest (image2_set atan2_dom Ratan2 y x)
    (Interval.with_infsup_raw (opp (Interval.sup_raw Interval.PI))
       (Interval.sup_raw Interval.PI)).
Proof.
intros y x cx cy Hy Hx Hcx Hcy Hcx' Hcy'.
(* [x] has a real [t < 0], and [y] has 0 and a real [u < 0]. *)
assert (Tx : exists t, mem t x /\ t < 0).
{ pose proof (classify_mem x cx Hx Hcx) as Mx.
  destruct Hcx' as [-> | [-> | ->]].
  - exact (proj1 Mx).
  - exact (proj2 (proj2 Mx)).
  - destruct Mx as [Hn (t & Ht)]. exists t. exact (conj Ht (Hn t Ht)). }
assert (Uy : mem 0 y /\ exists u, mem u y /\ u < 0).
{ destruct Hcy' as [-> | ->].
  - split; [exact (ac_cm_zero y Hy Hcy)|].
    exact (proj1 (classify_mem y CM Hy Hcy)).
  - pose proof (classify_mem y CN0 Hy Hcy) as (_ & Z & U). exact (conj Z U). }
destruct Tx as (t & Ht & Ht0). destruct Uy as (Zy & u & Hu & Hu0).
assert (Hpi : image2_set atan2_dom Ratan2 y x PI).
{ apply (ac_pt y x 0 t); [exact Zy | exact Ht | right; intros E; lra |].
  apply Ratan2_zero_y_neg. exact Ht0. }
unfold Interval.with_infsup_raw, Generic.constant. apply tightest_lanes_lub.
- exists PI. exact Hpi.
- (* The values come as close to [-PI] as asked just below the half-line
     [y = 0], [x < 0], at [(r, t)] for [r] in [[max(r0, u), 0)]. *)
  exists (Some PI). split; [|rewrite ac_opp_opp; exact PI_up].
  apply mono_lub_approx.
  + intros s (r & t' & Hr & Ht' & Hd & Hs). pose proof (Ratan2_range r t' Hd). lra.
  + intros eps He. destruct (Ratan2_y_0neg t eps Ht0 He) as (r0 & Hr0 & Happ).
    pose proof (Rmax_l r0 u) as Hm1. pose proof (Rmax_r r0 u) as Hm2.
    pose proof (Rmax_lub_lt r0 u 0 Hr0 Hu0) as Hm3.
    specialize (Happ (Rmax r0 u) Hm1 Hm3).
    exists (- Ratan2 (Rmax r0 u) t). split; [|lra].
    apply (ac_pt y x (Rmax r0 u) t).
    * apply (mem_between y u 0 (Rmax r0 u) Hy Hu Zy). lra.
    * exact Ht.
    * left. intros E. lra.
    * ring.
- apply (ac_lane _ PI); [exact Hpi | | exact PI_up].
  intros s (r & t' & Hr & Ht' & Hd & ->). pose proof (Ratan2_range r t' Hd). lra.
Qed.

(** [P0_P0]: the closed first quadrant, [[0, PI/2]]. *)
Lemma at2_p0p0 :
  forall y x, valid y -> valid x ->
  Interval.classify x = Some CP0 -> Interval.classify y = Some CP0 ->
  is_tightest (image2_set atan2_dom Ratan2 y x)
    (Interval.with_infsup_raw Model.zero (Interval.sup_raw Interval.FRAC_PI_2)).
Proof.
intros y x Hy Hx Hcx Hcy.
pose proof (classify_mem x CP0 Hx Hcx) as (Px & Zx & b & Hb & Hb0).
pose proof (classify_mem y CP0 Hy Hcy) as (Py & Zy & d & Hd & Hd0).
apply (ac_range _ 0 (PI / 2)).
- apply (ac_pt y x 0 b); [exact Zy | exact Hb | right; intros E; lra |].
  apply Ratan2_zero_y_pos. exact Hb0.
- apply (ac_pt y x d 0); [exact Hd | exact Zx | left; intros E; lra |].
  apply Ratan2_zero_x_pos. exact Hd0.
- intros s (r & t & Hr & Ht & Hdom & ->). exact (Ratan2_q1 r t (Py r Hr) (Px t Ht) Hdom).
- rewrite Ropp_0. exact ac_zero_dn.
- exact FRAC_PI_2_up.
Qed.

(** [M_P0] and [M_Z]: [x] has reals on both sides of 0, and [y] has 0
    and none below, [[0, PI]]. *)
Lemma at2_mp0 :
  forall y x, valid y -> valid x ->
  Interval.classify x = Some CM ->
  (Interval.classify y = Some CP0 \/ Interval.classify y = Some CZ) ->
  is_tightest (image2_set atan2_dom Ratan2 y x)
    (Interval.with_infsup_raw Model.zero (Interval.sup_raw Interval.PI)).
Proof.
intros y x Hy Hx Hcx Hcy.
pose proof (classify_mem x CM Hx Hcx) as ((a & Ha & Ha0) & (b & Hb & Hb0)).
assert (Py : forall r, mem r y -> 0 <= r).
{ destruct Hcy as [Hc|Hc].
  - exact (proj1 (classify_mem y CP0 Hy Hc)).
  - intros r Hr. apply (proj1 (classify_mem y CZ Hy Hc r)) in Hr. lra. }
assert (Zy : mem 0 y).
{ destruct Hcy as [Hc|Hc].
  - exact (proj1 (proj2 (classify_mem y CP0 Hy Hc))).
  - exact (proj2 (classify_mem y CZ Hy Hc 0) eq_refl). }
apply (ac_range _ 0 PI).
- apply (ac_pt y x 0 b); [exact Zy | exact Hb | right; intros E; lra |].
  apply Ratan2_zero_y_pos. exact Hb0.
- apply (ac_pt y x 0 a); [exact Zy | exact Ha | right; intros E; lra |].
  apply Ratan2_zero_y_neg. exact Ha0.
- intros s (r & t & Hr & Ht & Hdom & ->). exact (ac_upper_half r t (Py r Hr) Hdom).
- rewrite Ropp_0. exact ac_zero_dn.
- exact PI_up.
Qed.

(** [N0_P0]: the closed second quadrant, [[PI/2, PI]]. *)
Lemma at2_n0p0 :
  forall y x, valid y -> valid x ->
  Interval.classify x = Some CN0 -> Interval.classify y = Some CP0 ->
  is_tightest (image2_set atan2_dom Ratan2 y x)
    (Interval.with_infsup_raw (Interval.inf_raw Interval.FRAC_PI_2)
       (Interval.sup_raw Interval.PI)).
Proof.
intros y x Hy Hx Hcx Hcy.
pose proof (classify_mem x CN0 Hx Hcx) as (Nx & Zx & a & Ha & Ha0).
pose proof (classify_mem y CP0 Hy Hcy) as (Py & Zy & d & Hd & Hd0).
apply (ac_range _ (PI / 2) PI).
- apply (ac_pt y x d 0); [exact Hd | exact Zx | left; intros E; lra |].
  apply Ratan2_zero_x_pos. exact Hd0.
- apply (ac_pt y x 0 a); [exact Zy | exact Ha | right; intros E; lra |].
  apply Ratan2_zero_y_neg. exact Ha0.
- intros s (r & t & Hr & Ht & Hdom & ->). exact (Ratan2_q2 r t (Py r Hr) (Nx t Ht) Hdom).
- exact FRAC_PI_2_dn.
- exact PI_up.
Qed.

(** [P0_N0]: the closed fourth quadrant, [[-PI/2, 0]]. *)
Lemma at2_p0n0 :
  forall y x, valid y -> valid x ->
  Interval.classify x = Some CP0 -> Interval.classify y = Some CN0 ->
  is_tightest (image2_set atan2_dom Ratan2 y x)
    (Interval.with_infsup_raw (opp (Interval.sup_raw Interval.FRAC_PI_2)) Model.zero).
Proof.
intros y x Hy Hx Hcx Hcy.
pose proof (classify_mem x CP0 Hx Hcx) as (Px & Zx & b & Hb & Hb0).
pose proof (classify_mem y CN0 Hy Hcy) as (Ny & Zy & c & Hc & Hc0).
apply (ac_range _ (- (PI / 2)) 0).
- apply (ac_pt y x c 0); [exact Hc | exact Zx | left; intros E; lra |].
  apply Ratan2_zero_x_neg. exact Hc0.
- apply (ac_pt y x 0 b); [exact Zy | exact Hb | right; intros E; lra |].
  apply Ratan2_zero_y_pos. exact Hb0.
- intros s (r & t & Hr & Ht & Hdom & ->). exact (Ratan2_q4 r t (Ny r Hr) (Px t Ht) Hdom).
- rewrite Ropp_involutive, ac_opp_opp. exact FRAC_PI_2_up.
- exact ac_zero_up.
Qed.

(** [P0_M] and [Z_M]: [x] has 0 and none below, and [y] has reals on
    both sides of 0, [[-PI/2, PI/2]]. *)
Lemma at2_p0m :
  forall y x, valid y -> valid x ->
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CZ) ->
  Interval.classify y = Some CM ->
  is_tightest (image2_set atan2_dom Ratan2 y x)
    (Interval.with_infsup_raw (opp (Interval.sup_raw Interval.FRAC_PI_2))
       (Interval.sup_raw Interval.FRAC_PI_2)).
Proof.
intros y x Hy Hx Hcx Hcy.
assert (Px : forall t, mem t x -> 0 <= t).
{ destruct Hcx as [Hc|Hc].
  - exact (proj1 (classify_mem x CP0 Hx Hc)).
  - intros t Ht. apply (proj1 (classify_mem x CZ Hx Hc t)) in Ht. lra. }
assert (Zx : mem 0 x).
{ destruct Hcx as [Hc|Hc].
  - exact (proj1 (proj2 (classify_mem x CP0 Hx Hc))).
  - exact (proj2 (classify_mem x CZ Hx Hc 0) eq_refl). }
pose proof (classify_mem y CM Hy Hcy) as ((c & Hc & Hc0) & (d & Hd & Hd0)).
apply (ac_range _ (- (PI / 2)) (PI / 2)).
- apply (ac_pt y x c 0); [exact Hc | exact Zx | left; intros E; lra |].
  apply Ratan2_zero_x_neg. exact Hc0.
- apply (ac_pt y x d 0); [exact Hd | exact Zx | left; intros E; lra |].
  apply Ratan2_zero_x_pos. exact Hd0.
- intros s (r & t & Hr & Ht & Hdom & ->). exact (ac_right_half r t (Px t Ht) Hdom).
- rewrite Ropp_involutive, ac_opp_opp. exact FRAC_PI_2_up.
- exact FRAC_PI_2_up.
Qed.

(** [N0_Z] and [N1_Z]: the image is [{PI}]. *)
Lemma at2_pi :
  forall y x, valid y -> valid x ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  Interval.classify y = Some CZ ->
  is_tightest (image2_set atan2_dom Ratan2 y x) Interval.PI.
Proof.
intros y x Hy Hx Hcx Hcy.
(* [x] has only reals at most 0, one of them [a < 0], and [y] is [{0}]. *)
assert (Nx : (forall t, mem t x -> t <= 0) /\ exists a, mem a x /\ a < 0).
{ destruct Hcx as [Hc|Hc].
  - pose proof (classify_mem x CN0 Hx Hc) as (N & _ & A). exact (conj N A).
  - pose proof (classify_mem x CN1 Hx Hc) as (N & a & Ha).
    split; [intros t Ht; exact (Rlt_le _ _ (N t Ht))|].
    exists a. exact (conj Ha (N a Ha)). }
destruct Nx as (Nx & a & Ha & Ha0).
pose proof (classify_mem y CZ Hy Hcy) as My.
apply (ac_single _ PI).
- apply (ac_pt y x 0 a); [exact (proj2 (My 0) eq_refl) | exact Ha | right; intros E; lra |].
  apply Ratan2_zero_y_neg. exact Ha0.
- intros s (r & t & Hr & Ht & Hdom & ->).
  apply (proj1 (My r)) in Hr. subst r.
  destruct Hdom as [H|H]; [exfalso; apply H; reflexivity|].
  apply Ratan2_zero_y_neg. exact (ac_neg_of t (Nx t Ht) H).
- exact ac_PI_dn_rep.
- exact PI_up.
Qed.

(** [P0_Z]: the image is [{0}]. *)
Lemma at2_zero :
  forall y x, valid y -> valid x ->
  Interval.classify x = Some CP0 -> Interval.classify y = Some CZ ->
  is_tightest (image2_set atan2_dom Ratan2 y x) Interval.zero.
Proof.
intros y x Hy Hx Hcx Hcy.
pose proof (classify_mem x CP0 Hx Hcx) as (Px & Zx & b & Hb & Hb0).
pose proof (classify_mem y CZ Hy Hcy) as My.
apply (ac_single _ 0).
- apply (ac_pt y x 0 b); [exact (proj2 (My 0) eq_refl) | exact Hb | right; intros E; lra |].
  apply Ratan2_zero_y_pos. exact Hb0.
- intros s (r & t & Hr & Ht & Hdom & ->).
  apply (proj1 (My r)) in Hr. subst r.
  destruct Hdom as [H|H]; [exfalso; apply H; reflexivity|].
  apply Ratan2_zero_y_pos. exact (ac_pos_of t (Px t Ht) H).
- rewrite Ropp_0. exact ac_zero_up.
- exact ac_zero_up.
Qed.

(** [Z_N0]: the image is [{-PI/2}]. *)
Lemma at2_neg_half_pi :
  forall y x, valid y -> valid x ->
  Interval.classify x = Some CZ -> Interval.classify y = Some CN0 ->
  is_tightest (image2_set atan2_dom Ratan2 y x) (Interval.neg Interval.FRAC_PI_2).
Proof.
intros y x Hy Hx Hcx Hcy.
pose proof (classify_mem x CZ Hx Hcx) as Mx.
pose proof (classify_mem y CN0 Hy Hcy) as (Ny & Zy & c & Hc & Hc0).
apply (ac_single _ (- (PI / 2))).
- apply (ac_pt y x c 0); [exact Hc | exact (proj2 (Mx 0) eq_refl) | left; intros E; lra |].
  apply Ratan2_zero_x_neg. exact Hc0.
- intros s (r & t & Hr & Ht & Hdom & ->).
  apply (proj1 (Mx t)) in Ht. subst t.
  destruct Hdom as [H|H]; [|exfalso; apply H; reflexivity].
  apply Ratan2_zero_x_neg. exact (ac_neg_of r (Ny r Hr) H).
- (* The lanes of [-FRAC_PI_2] are those of [FRAC_PI_2] swapped. *)
  rewrite Ropp_involutive. exact FRAC_PI_2_up.
- exact ac_FRAC_PI_2_dn_rep.
Qed.

(** [Z_P0]: the image is [{PI/2}]. *)
Lemma at2_half_pi :
  forall y x, valid y -> valid x ->
  Interval.classify x = Some CZ -> Interval.classify y = Some CP0 ->
  is_tightest (image2_set atan2_dom Ratan2 y x) Interval.FRAC_PI_2.
Proof.
intros y x Hy Hx Hcx Hcy.
pose proof (classify_mem x CZ Hx Hcx) as Mx.
pose proof (classify_mem y CP0 Hy Hcy) as (Py & Zy & d & Hd & Hd0).
apply (ac_single _ (PI / 2)).
- apply (ac_pt y x d 0); [exact Hd | exact (proj2 (Mx 0) eq_refl) | left; intros E; lra |].
  apply Ratan2_zero_x_pos. exact Hd0.
- intros s (r & t & Hr & Ht & Hdom & ->).
  apply (proj1 (Mx t)) in Ht. subst t.
  destruct Hdom as [H|H]; [|exfalso; apply H; reflexivity].
  apply Ratan2_zero_x_pos. exact (ac_pos_of r (Py r Hr) H).
- exact ac_FRAC_PI_2_dn_rep.
- exact FRAC_PI_2_up.
Qed.
