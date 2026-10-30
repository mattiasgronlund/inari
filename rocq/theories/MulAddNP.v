(** * [mul_add] of intervals that do not contain 0 in their interior

    The cases [N × N], [N × P], [P × N] and [P × P] of [x.mul_add(y, z)]
    compute the same lane products as [x * y] in [MulNP.v], each with the
    lane of [z] added before the single rounding up. The largest product
    and the largest negated product of [x × y] are those of [MulNP.v]
    ([nonneg_set_N], [nonneg_set_P], and the [tight] halves of
    [nonneg_lane_pos] and [nonneg_lane_fin]). [fma_lane_pos] and
    [fma_lane_finite] in [MulAddLane.v] give the lanes, and
    [tightest_mul_add] the tightest interval ([mul_add_fin_pos],
    [mul_add_pos_fin]). *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer Sign MaxMin AddSub Classify2
  Classes MulAddRu MulLane MulTight MulNP MulAddLane.

Open Scope R_scope.

(** ** The tightest interval *)

(** As [mul_fin_pos] in [MulNP.v], with the lanes of a nonempty [z]
    added: the products of [x × y] are the products [p * q] of two
    one-signed sets, the first lane adds the first lane of [z] to the
    negated product of their least elements, and the second adds the
    second lane of [z] to the product of their largest. *)
Lemma mul_add_fin_pos :
  forall x y z A B wA wB m n u v, valid z -> Interval.is_empty z = false ->
  nonneg_set A wA m -> nonneg_set B wB n ->
  is_finite u = true -> is_finite v = true -> B2R u * B2R v = - (m * n) ->
  (forall s, image2 Rmult x y s <-> exists p q, A p /\ B q /\ s = p * q) ->
  is_tightest (image3 Rfma x y z)
    {| rep := (Bfma mode_UP u v (fst (rep z)), Bfma mode_UP wA wB (snd (rep z))) |}.
Proof.
intros x y z A B wA wB m n u v Hz Ez HA HB Fu Fv Euv HS.
(* The lanes of the nonempty [z] are floats or +inf. *)
destruct (lanes_tight z Hz Ez) as (U0 & U1 & _).
assert (Hne : exists s, image2 Rmult x y s).
{ destruct HA as (_ & _ & _ & Hm & _), HB as (_ & _ & _ & Hn & _).
  exists (m * n). apply HS. exists m, n.
  split; [exact Hm | split; [exact Hn | reflexivity]]. }
(* The negation of a product is a negated product. *)
assert (HS' : forall s, image2 Rmult x y (- s) <->
                        exists p q, A p /\ B q /\ s = - (p * q)).
{ intros s. rewrite HS.
  split; intros (p & q & Hp & Hq & E); exists p, q;
    (split; [exact Hp | split; [exact Hq | lra]]). }
pose proof (proj1 (nonneg_lane_fin _ A B wA wB m n u v HA HB Fu Fv Euv HS')) as T0.
pose proof (proj1 (nonneg_lane_pos _ A B wA wB m n HA HB HS)) as T1.
apply (tightest_mul_add x y z _ _ _ Hz Ez Hne T0 T1); cbn [rep fst snd].
- apply fma_lane_finite; [exact Fu | exact Fv | exact U0].
- apply fma_lane_pos; [exact (proj1 HA) | exact (proj1 HB) | exact U1].
Qed.

(** As [mul_pos_fin] in [MulNP.v], with the lanes of a nonempty [z]
    added: the negated products of [x × y] are the products [p * q]. *)
Lemma mul_add_pos_fin :
  forall x y z A B wA wB m n u v, valid z -> Interval.is_empty z = false ->
  nonneg_set A wA m -> nonneg_set B wB n ->
  is_finite u = true -> is_finite v = true -> B2R u * B2R v = - (m * n) ->
  (forall s, image2 Rmult x y (- s) <-> exists p q, A p /\ B q /\ s = p * q) ->
  is_tightest (image3 Rfma x y z)
    {| rep := (Bfma mode_UP wA wB (fst (rep z)), Bfma mode_UP u v (snd (rep z))) |}.
Proof.
intros x y z A B wA wB m n u v Hz Ez HA HB Fu Fv Euv HS.
(* The lanes of the nonempty [z] are floats or +inf. *)
destruct (lanes_tight z Hz Ez) as (U0 & U1 & _).
(* A product whose negation is [p * q] is [-(p * q)]. *)
assert (HS' : forall s, image2 Rmult x y s <->
                        exists p q, A p /\ B q /\ s = - (p * q)).
{ intros s. pose proof (HS (- s)) as E. rewrite Ropp_involutive in E. rewrite E.
  split; intros (p & q & Hp & Hq & E'); exists p, q;
    (split; [exact Hp | split; [exact Hq | lra]]). }
assert (Hne : exists s, image2 Rmult x y s).
{ destruct HA as (_ & _ & _ & Hm & _), HB as (_ & _ & _ & Hn & _).
  exists (- (m * n)). apply HS'. exists m, n.
  split; [exact Hm | split; [exact Hn | reflexivity]]. }
pose proof (proj1 (nonneg_lane_pos _ A B wA wB m n HA HB HS)) as T0.
pose proof (proj1 (nonneg_lane_fin _ A B wA wB m n u v HA HB Fu Fv Euv HS')) as T1.
apply (tightest_mul_add x y z _ _ _ Hz Ez Hne T0 T1); cbn [rep fst snd].
- apply fma_lane_pos; [exact (proj1 HA) | exact (proj1 HB) | exact U0].
- apply fma_lane_finite; [exact Fu | exact Fv | exact U1].
Qed.

(** ** What [Interval::mul_add] computes *)

(** [N × N] multiplies [[-b; -a]] and [[d; -c]], as [mul_NN_eq]. *)
Lemma mul_add_NN_eq :
  forall has_fma x y z, Interval.is_empty z = false ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  (Interval.classify y = Some CN0 \/ Interval.classify y = Some CN1) ->
  Interval.mul_add has_fma x y z =
  Some {| rep := (Bfma mode_UP (opp (snd (rep x))) (snd (rep y)) (fst (rep z)),
                  Bfma mode_UP (fst (rep x)) (fst (rep y)) (snd (rep z))) |}.
Proof.
intros has_fma x y z Ez Cx Cy. unfold Interval.mul_add. rewrite Ez.
destruct Cx as [Cx|Cx], Cy as [Cy|Cy]; rewrite (classify2_pair _ _ _ _ Cx Cy);
  cbv beta iota zeta; rewrite !mul_add_ru_correct; reflexivity.
Qed.

(** [N × P] multiplies [[-a; b]] and [[d; c]], as [mul_NP_eq]. *)
Lemma mul_add_NP_eq :
  forall has_fma x y z, Interval.is_empty z = false ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  (Interval.classify y = Some CP0 \/ Interval.classify y = Some CP1) ->
  Interval.mul_add has_fma x y z =
  Some {| rep := (Bfma mode_UP (fst (rep x)) (snd (rep y)) (fst (rep z)),
                  Bfma mode_UP (snd (rep x)) (opp (fst (rep y))) (snd (rep z))) |}.
Proof.
intros has_fma x y z Ez Cx Cy. unfold Interval.mul_add. rewrite Ez.
destruct Cx as [Cx|Cx], Cy as [Cy|Cy]; rewrite (classify2_pair _ _ _ _ Cx Cy);
  cbv beta iota zeta; rewrite !mul_add_ru_correct; reflexivity.
Qed.

(** [P × N] multiplies [[b; a]] and [[-c; d]], as [mul_PN_eq]. *)
Lemma mul_add_PN_eq :
  forall has_fma x y z, Interval.is_empty z = false ->
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  (Interval.classify y = Some CN0 \/ Interval.classify y = Some CN1) ->
  Interval.mul_add has_fma x y z =
  Some {| rep := (Bfma mode_UP (snd (rep x)) (fst (rep y)) (fst (rep z)),
                  Bfma mode_UP (opp (fst (rep x))) (snd (rep y)) (snd (rep z))) |}.
Proof.
intros has_fma x y z Ez Cx Cy. unfold Interval.mul_add. rewrite Ez.
destruct Cx as [Cx|Cx], Cy as [Cy|Cy]; rewrite (classify2_pair _ _ _ _ Cx Cy);
  cbv beta iota zeta; rewrite !mul_add_ru_correct; reflexivity.
Qed.

(** [P × P] multiplies [[-a; b]] and [[c; d]], as [mul_PP_eq]. *)
Lemma mul_add_PP_eq :
  forall has_fma x y z, Interval.is_empty z = false ->
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  (Interval.classify y = Some CP0 \/ Interval.classify y = Some CP1) ->
  Interval.mul_add has_fma x y z =
  Some {| rep := (Bfma mode_UP (fst (rep x)) (opp (fst (rep y))) (fst (rep z)),
                  Bfma mode_UP (snd (rep x)) (snd (rep y)) (snd (rep z))) |}.
Proof.
intros has_fma x y z Ez Cx Cy. unfold Interval.mul_add. rewrite Ez.
destruct Cx as [Cx|Cx], Cy as [Cy|Cy]; rewrite (classify2_pair _ _ _ _ Cx Cy);
  cbv beta iota zeta; rewrite !mul_add_ru_correct; reflexivity.
Qed.

(** ** The theorems *)

Lemma mul_add_NN :
  forall has_fma x y z, valid x -> valid y -> valid z ->
  Interval.is_empty z = false ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  (Interval.classify y = Some CN0 \/ Interval.classify y = Some CN1) ->
  exists w, Interval.mul_add has_fma x y z = Some w /\ is_tightest (image3 Rfma x y z) w.
Proof.
intros has_fma x y z Hx Hy Hz Ez Cx Cy. rewrite (mul_add_NN_eq has_fma x y z Ez Cx Cy).
eexists. split; [reflexivity|].
destruct (nonneg_set_N x Hx Cx) as (Fb & HX), (nonneg_set_N y Hy Cy) as (Fd & HY).
(* The first product is [(-b) * d], and [(-b) * d = -((-b) * (-d))]. *)
apply (mul_add_fin_pos _ _ _ _ _ _ _ _ _ _ _ Hz Ez HX HY).
- rewrite is_finite_opp. exact Fb.
- exact Fd.
- rewrite B2R_opp. ring.
- apply image2_mult_opp_lr.
Qed.

Lemma mul_add_NP :
  forall has_fma x y z, valid x -> valid y -> valid z ->
  Interval.is_empty z = false ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  (Interval.classify y = Some CP0 \/ Interval.classify y = Some CP1) ->
  exists w, Interval.mul_add has_fma x y z = Some w /\ is_tightest (image3 Rfma x y z) w.
Proof.
intros has_fma x y z Hx Hy Hz Ez Cx Cy. rewrite (mul_add_NP_eq has_fma x y z Ez Cx Cy).
eexists. split; [reflexivity|].
destruct (nonneg_set_N x Hx Cx) as (Fb & HX), (nonneg_set_P y Hy Cy) as (Fc & HY).
(* The second product is [b * c], and [b * c = -((-b) * c)]. *)
apply (mul_add_pos_fin _ _ _ _ _ _ _ _ _ _ _ Hz Ez HX HY).
- exact Fb.
- rewrite is_finite_opp. exact Fc.
- rewrite B2R_opp. ring.
- apply image2_mult_opp_l.
Qed.

Lemma mul_add_PN :
  forall has_fma x y z, valid x -> valid y -> valid z ->
  Interval.is_empty z = false ->
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  (Interval.classify y = Some CN0 \/ Interval.classify y = Some CN1) ->
  exists w, Interval.mul_add has_fma x y z = Some w /\ is_tightest (image3 Rfma x y z) w.
Proof.
intros has_fma x y z Hx Hy Hz Ez Cx Cy. rewrite (mul_add_PN_eq has_fma x y z Ez Cx Cy).
eexists. split; [reflexivity|].
destruct (nonneg_set_P x Hx Cx) as (Fa & HX), (nonneg_set_N y Hy Cy) as (Fd & HY).
(* The second product is [a * d], and [a * d = -(a * (-d))]. *)
apply (mul_add_pos_fin _ _ _ _ _ _ _ _ _ _ _ Hz Ez HX HY).
- rewrite is_finite_opp. exact Fa.
- exact Fd.
- rewrite B2R_opp. ring.
- apply image2_mult_opp_r.
Qed.

Lemma mul_add_PP :
  forall has_fma x y z, valid x -> valid y -> valid z ->
  Interval.is_empty z = false ->
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  (Interval.classify y = Some CP0 \/ Interval.classify y = Some CP1) ->
  exists w, Interval.mul_add has_fma x y z = Some w /\ is_tightest (image3 Rfma x y z) w.
Proof.
intros has_fma x y z Hx Hy Hz Ez Cx Cy. rewrite (mul_add_PP_eq has_fma x y z Ez Cx Cy).
eexists. split; [reflexivity|].
destruct (nonneg_set_P x Hx Cx) as (Fa & HX), (nonneg_set_P y Hy Cy) as (Fc & HY).
(* The first product is [(-a) * c], and [(-a) * c = -(a * c)]. *)
apply (mul_add_fin_pos _ _ _ _ _ _ _ _ _ _ _ Hz Ez HX HY).
- exact Fa.
- rewrite is_finite_opp. exact Fc.
- rewrite B2R_opp. ring.
- (* The products [r * t] are those of the reals of [x] and [y]. *)
  intros s. reflexivity.
Qed.
