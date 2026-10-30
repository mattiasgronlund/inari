(** * [mul_add] of intervals where one factor has 0 in its interior

    The cases [M × N], [M × P], [N × M] and [P × M] of
    [x.mul_add(y, z)] compute the same lane products as [x * y] in
    [MulMRow.v], each with the lane of [z] added before the single rounding
    up. The largest products and largest negated products of [x × y] are
    those of [MulMRow.v] ([mul_M_lanes], [mul_N_lanes], [mul_P_lanes],
    [tight_mult_pos_r], [tight_mult_pos_l] and [image2_mult_opp_l],
    [image2_mult_opp_r], [image2_mult_opp_lr]). [fma_lane_pos] in
    [MulAddLane.v] gives each lane, and [tightest_mul_add] the tightest
    interval ([tightest_mul_add_pos]). *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer MaxMin DecBinary AddSub MulAddRu
  Classify2 Classes MulLane MulTight MulMRow MulAddLane.

Open Scope R_scope.

(** As [tightest_mul_pos] in [MulMRow.v], with the lanes of a nonempty
    [z] added: if the lanes [u0], [v0], [u1] and [v1] are above 0, and the
    negated products and the products of reals of [x] and [y] have the
    largest elements [umult (bound u0) (bound v0)] and
    [umult (bound u1) (bound v1)], then [Bfma mode_UP] of them and the
    lanes of [z] give the tightest interval. *)
Lemma tightest_mul_add_pos :
  forall x y z u0 v0 u1 v1 A0 B0 A1 B1,
  valid z -> Interval.is_empty z = false ->
  pos_lane u0 -> pos_lane v0 -> pos_lane u1 -> pos_lane v1 ->
  (exists r, mem r x) -> (exists t, mem t y) ->
  (forall s, image2 Rmult x y (- s) <-> exists r t, A0 r /\ B0 t /\ s = r * t) ->
  (forall s, image2 Rmult x y s <-> exists r t, A1 r /\ B1 t /\ s = r * t) ->
  tight (umult (bound u0) (bound v0)) (fun s => exists r t, A0 r /\ B0 t /\ s = r * t) ->
  tight (umult (bound u1) (bound v1)) (fun s => exists r t, A1 r /\ B1 t /\ s = r * t) ->
  is_tightest (image3 Rfma x y z)
    {| rep := (Bfma mode_UP u0 v0 (fst (rep z)), Bfma mode_UP u1 v1 (snd (rep z))) |}.
Proof.
intros x y z u0 v0 u1 v1 A0 B0 A1 B1 Hz Ez P0 Q0 P1 Q1 [r0 Hr0] [t0 Ht0] E0 E1 T0 T1.
(* The lanes of [z] are [upper_ok], which [fma_lane_pos] needs. *)
destruct (lanes_tight z Hz Ez) as (Uz0 & Uz1 & _).
apply (tightest_mul_add x y z _ (umult (bound u0) (bound v0)) (umult (bound u1) (bound v1))
  Hz Ez).
- exists (r0 * t0). exact (image2_mem Rmult x y r0 t0 Hr0 Ht0).
- exact (tight_ext _ _ _ (fun s => iff_sym (E0 s)) T0).
- exact (tight_ext _ _ _ (fun s => iff_sym (E1 s)) T1).
- exact (fma_lane_pos u0 v0 _ P0 Q0 Uz0).
- exact (fma_lane_pos u1 v1 _ P1 Q1 Uz1).
Qed.

(** [M × N]: the first lane is [RU(b * (-c) + (-e))] and the second
    [RU((-a) * (-c) + f)], for [z = [e, f]]. *)
Lemma mul_add_MN :
  forall has_fma x y z, valid x -> valid y -> valid z ->
  Interval.is_empty z = false ->
  Interval.classify x = Some CM ->
  (Interval.classify y = Some CN0 \/ Interval.classify y = Some CN1) ->
  exists w, Interval.mul_add has_fma x y z = Some w /\ is_tightest (image3 Rfma x y z) w.
Proof.
intros has_fma x y z Hx Hy Hz Ez Cx Cy.
destruct (mul_M_lanes x Hx Cx) as (Px0 & Px1 & Ex & Tx0 & Tx1 & Nx & Px).
destruct (mul_N_lanes y Hy Cy) as (Py0 & Ey & Ty0 & Gy & Ny).
exists {| rep := (Bfma mode_UP (snd (rep x)) (fst (rep y)) (fst (rep z)),
                  Bfma mode_UP (fst (rep x)) (fst (rep y)) (snd (rep z))) |}.
split.
- (* [N0] and [N1] take the same branch: [x] swapped times [-c] twice. *)
  unfold Interval.mul_add. rewrite Ez.
  destruct Cy as [Cy|Cy]; rewrite (classify2_pair _ _ _ _ Cx Cy); cbv beta iota zeta;
    rewrite mul_add_ru_correct; reflexivity.
- apply (tightest_mul_add_pos x y z _ _ _ _
    (fun r => mem r x) (fun t => mem (- t) y) (fun r => mem (- r) x) (fun t => mem (- t) y)
    Hz Ez Px1 Py0 Px0 Py0 Ex Ey (image2_mult_opp_r x y) (image2_mult_opp_lr x y)).
  + exact (tight_mult_pos_r _ _ _ _ Tx1 Ty0 Gy Px Ny).
  + exact (tight_mult_pos_r _ _ _ _ Tx0 Ty0 Gy Nx Ny).
Qed.

(** [M × P]: the first lane is [RU((-a) * d + (-e))] and the second
    [RU(b * d + f)]. *)
Lemma mul_add_MP :
  forall has_fma x y z, valid x -> valid y -> valid z ->
  Interval.is_empty z = false ->
  Interval.classify x = Some CM ->
  (Interval.classify y = Some CP0 \/ Interval.classify y = Some CP1) ->
  exists w, Interval.mul_add has_fma x y z = Some w /\ is_tightest (image3 Rfma x y z) w.
Proof.
intros has_fma x y z Hx Hy Hz Ez Cx Cy.
destruct (mul_M_lanes x Hx Cx) as (Px0 & Px1 & Ex & Tx0 & Tx1 & Nx & Px).
destruct (mul_P_lanes y Hy Cy) as (Py1 & Ey & Ty1 & Gy & Py).
exists {| rep := (Bfma mode_UP (fst (rep x)) (snd (rep y)) (fst (rep z)),
                  Bfma mode_UP (snd (rep x)) (snd (rep y)) (snd (rep z))) |}.
split.
- (* [P0] and [P1] take the same branch: [x] times [d] twice. *)
  unfold Interval.mul_add. rewrite Ez.
  destruct Cy as [Cy|Cy]; rewrite (classify2_pair _ _ _ _ Cx Cy); cbv beta iota zeta;
    rewrite mul_add_ru_correct; reflexivity.
- apply (tightest_mul_add_pos x y z _ _ _ _
    (fun r => mem (- r) x) (fun t => mem t y) (fun r => mem r x) (fun t => mem t y)
    Hz Ez Px0 Py1 Px1 Py1 Ex Ey (image2_mult_opp_l x y) (fun s => iff_refl _)).
  + exact (tight_mult_pos_r _ _ _ _ Tx0 Ty1 Gy Nx Py).
  + exact (tight_mult_pos_r _ _ _ _ Tx1 Ty1 Gy Px Py).
Qed.

(** [N × M]: the first lane is [RU((-a) * d + (-e))] and the second
    [RU((-a) * (-c) + f)]. *)
Lemma mul_add_NM :
  forall has_fma x y z, valid x -> valid y -> valid z ->
  Interval.is_empty z = false ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  Interval.classify y = Some CM ->
  exists w, Interval.mul_add has_fma x y z = Some w /\ is_tightest (image3 Rfma x y z) w.
Proof.
intros has_fma x y z Hx Hy Hz Ez Cx Cy.
destruct (mul_N_lanes x Hx Cx) as (Px0 & Ex & Tx0 & Gx & Nx).
destruct (mul_M_lanes y Hy Cy) as (Py0 & Py1 & Ey & Ty0 & Ty1 & Ny & Py).
exists {| rep := (Bfma mode_UP (fst (rep x)) (snd (rep y)) (fst (rep z)),
                  Bfma mode_UP (fst (rep x)) (fst (rep y)) (snd (rep z))) |}.
split.
- (* [N0] and [N1] take the same branch: [-a] twice times [y] swapped. *)
  unfold Interval.mul_add. rewrite Ez.
  destruct Cx as [Cx|Cx]; rewrite (classify2_pair _ _ _ _ Cx Cy); cbv beta iota zeta;
    rewrite mul_add_ru_correct; reflexivity.
- apply (tightest_mul_add_pos x y z _ _ _ _
    (fun r => mem (- r) x) (fun t => mem t y) (fun r => mem (- r) x) (fun t => mem (- t) y)
    Hz Ez Px0 Py1 Px0 Py0 Ex Ey (image2_mult_opp_l x y) (image2_mult_opp_lr x y)).
  + exact (tight_mult_pos_l _ _ _ _ Tx0 Ty1 Gx Nx Py).
  + exact (tight_mult_pos_l _ _ _ _ Tx0 Ty0 Gx Nx Ny).
Qed.

(** [P × M]: the first lane is [RU(b * (-c) + (-e))] and the second
    [RU(b * d + f)]. *)
Lemma mul_add_PM :
  forall has_fma x y z, valid x -> valid y -> valid z ->
  Interval.is_empty z = false ->
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  Interval.classify y = Some CM ->
  exists w, Interval.mul_add has_fma x y z = Some w /\ is_tightest (image3 Rfma x y z) w.
Proof.
intros has_fma x y z Hx Hy Hz Ez Cx Cy.
destruct (mul_P_lanes x Hx Cx) as (Px1 & Ex & Tx1 & Gx & Px).
destruct (mul_M_lanes y Hy Cy) as (Py0 & Py1 & Ey & Ty0 & Ty1 & Ny & Py).
exists {| rep := (Bfma mode_UP (snd (rep x)) (fst (rep y)) (fst (rep z)),
                  Bfma mode_UP (snd (rep x)) (snd (rep y)) (snd (rep z))) |}.
split.
- (* [P0] and [P1] take the same branch: [b] twice times [y]. *)
  unfold Interval.mul_add. rewrite Ez.
  destruct Cx as [Cx|Cx]; rewrite (classify2_pair _ _ _ _ Cx Cy); cbv beta iota zeta;
    rewrite mul_add_ru_correct; reflexivity.
- apply (tightest_mul_add_pos x y z _ _ _ _
    (fun r => mem r x) (fun t => mem (- t) y) (fun r => mem r x) (fun t => mem t y)
    Hz Ez Px1 Py0 Px1 Py1 Ex Ey (image2_mult_opp_r x y) (fun s => iff_refl _)).
  + exact (tight_mult_pos_l _ _ _ _ Tx1 Ty0 Gx Px Ny).
  + exact (tight_mult_pos_l _ _ _ _ Tx1 Ty1 Gx Px Py).
Qed.
