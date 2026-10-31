(** * The point function [atan2] of two reals

    Facts about [Ratan2] of [Elementary.v], with [r] the [y] coordinate and
    [t] the [x] coordinate, as in [Ratan2 r t]: its values on the axes and
    by the formula, that it is the argument of the point [(t, r)]
    ([Ratan2_polar], [Ratan2_polar_unique]), its range on each half-plane
    and quadrant, its monotonicity in each argument, its limits at the
    infinities, and where it is continuous: everywhere on its domain but
    on the half-line [r = 0], [t < 0], where it jumps from near [-PI] below
    the line to [PI] on it. All of it follows from Stdlib's [atan]:
    [atan_bound], [atan_opp], [atan_inv], [atan_0], [sin_atan] and
    [cos_atan] in [Ratan.v], and [atan_increasing], [atan_tan] and
    [derivable_pt_atan] there through [atan_inc], [atan_glb], [atan_lub]
    and [atan_cont] of [TrigReal.v]. *)

From Stdlib Require Import Reals Lra.
From Inari Require Import Model Ieee1788 Elementary RealBounds TrigReal.

Open Scope R_scope.

(** ** Values *)

Lemma Ratan2_pos_x : forall r t, 0 < t -> Ratan2 r t = atan (r / t).
Proof.
intros r t Ht. unfold Ratan2.
destruct (Rlt_dec 0 t) as [_|H]; [reflexivity | lra].
Qed.

Lemma Ratan2_neg_x_ge : forall r t, t < 0 -> 0 <= r -> Ratan2 r t = atan (r / t) + PI.
Proof.
intros r t Ht Hr. unfold Ratan2.
destruct (Rlt_dec 0 t) as [H|_]; [lra|].
destruct (Rlt_dec t 0) as [_|H]; [|lra].
destruct (Rle_dec 0 r) as [_|H]; [reflexivity | lra].
Qed.

Lemma Ratan2_neg_x_lt : forall r t, t < 0 -> r < 0 -> Ratan2 r t = atan (r / t) - PI.
Proof.
intros r t Ht Hr. unfold Ratan2.
destruct (Rlt_dec 0 t) as [H|_]; [lra|].
destruct (Rlt_dec t 0) as [_|H]; [|lra].
destruct (Rle_dec 0 r) as [H|_]; [lra | reflexivity].
Qed.

Lemma Ratan2_zero_x_pos : forall r, 0 < r -> Ratan2 r 0 = PI / 2.
Proof.
intros r Hr. unfold Ratan2.
(* Both tests on the [x] coordinate are [Rlt_dec 0 0]. *)
destruct (Rlt_dec 0 0) as [H|_]; [lra|].
destruct (Rlt_dec 0 r) as [_|H]; [reflexivity | lra].
Qed.

Lemma Ratan2_zero_x_neg : forall r, r < 0 -> Ratan2 r 0 = - (PI / 2).
Proof.
intros r Hr. unfold Ratan2.
destruct (Rlt_dec 0 0) as [H|_]; [lra|].
destruct (Rlt_dec 0 r) as [H|_]; [lra|].
destruct (Rlt_dec r 0) as [_|H]; [reflexivity | lra].
Qed.

Lemma Ratan2_zero_y_pos : forall t, 0 < t -> Ratan2 0 t = 0.
Proof.
intros t Ht. rewrite Ratan2_pos_x by exact Ht.
unfold Rdiv. rewrite Rmult_0_l. exact atan_0.
Qed.

Lemma Ratan2_zero_y_neg : forall t, t < 0 -> Ratan2 0 t = PI.
Proof.
intros t Ht. rewrite Ratan2_neg_x_ge by lra.
unfold Rdiv. rewrite Rmult_0_l, atan_0. ring.
Qed.

(** ** Helpers *)

Lemma ar_atan_nonneg : forall u, 0 <= u -> 0 <= atan u.
Proof. intros u Hu. rewrite <- atan_0. apply atan_inc, Hu. Qed.

Lemma ar_atan_nonpos : forall u, u <= 0 -> atan u <= 0.
Proof. intros u Hu. rewrite <- atan_0. apply atan_inc, Hu. Qed.

(** The signs of quotients and the monotonicity of division. *)

Lemma ar_div_le_pos : forall a b c, 0 < c -> a <= b -> a / c <= b / c.
Proof.
intros a b c Hc Hab. assert (0 < / c) by (apply Rinv_0_lt_compat, Hc).
unfold Rdiv. nra.
Qed.

Lemma ar_div_le_neg : forall a b c, c < 0 -> a <= b -> b / c <= a / c.
Proof.
intros a b c Hc Hab. assert (/ c < 0) by (apply Rinv_lt_0_compat, Hc).
unfold Rdiv. nra.
Qed.

Lemma ar_div_nonneg_pos : forall a c, 0 <= a -> 0 < c -> 0 <= a / c.
Proof.
intros a c Ha Hc. assert (0 < / c) by (apply Rinv_0_lt_compat, Hc).
unfold Rdiv. nra.
Qed.

Lemma ar_div_nonpos_pos : forall a c, a <= 0 -> 0 < c -> a / c <= 0.
Proof.
intros a c Ha Hc. assert (0 < / c) by (apply Rinv_0_lt_compat, Hc).
unfold Rdiv. nra.
Qed.

Lemma ar_div_nonneg_neg : forall a c, 0 <= a -> c < 0 -> a / c <= 0.
Proof.
intros a c Ha Hc. assert (/ c < 0) by (apply Rinv_lt_0_compat, Hc).
unfold Rdiv. nra.
Qed.

Lemma ar_div_nonpos_neg : forall a c, a <= 0 -> c < 0 -> 0 <= a / c.
Proof.
intros a c Ha Hc. assert (/ c < 0) by (apply Rinv_lt_0_compat, Hc).
unfold Rdiv. nra.
Qed.

Lemma ar_div_lt_np : forall a c, a < 0 -> 0 < c -> a / c < 0.
Proof.
intros a c Ha Hc. assert (0 < / c) by (apply Rinv_0_lt_compat, Hc).
unfold Rdiv. nra.
Qed.

Lemma ar_div_lt_pn : forall a c, 0 < a -> c < 0 -> a / c < 0.
Proof.
intros a c Ha Hc. assert (/ c < 0) by (apply Rinv_lt_0_compat, Hc).
unfold Rdiv. nra.
Qed.

Lemma ar_div_lt_nn : forall a c, a < 0 -> c < 0 -> 0 < a / c.
Proof.
intros a c Ha Hc. assert (/ c < 0) by (apply Rinv_lt_0_compat, Hc).
unfold Rdiv. nra.
Qed.

Lemma ar_div_inv : forall a c, a <> 0 -> c <> 0 -> a / c = / (c / a).
Proof. intros a c Ha Hc. field. tauto. Qed.

(** [atan_inv] for a negative argument: [/ u = - / (- u)], and [atan] is
    odd ([atan_opp]). *)
Lemma ar_atan_inv_neg : forall u, u < 0 -> atan (/ u) = - (PI / 2) - atan u.
Proof.
intros u Hu.
replace (/ u) with (- / (- u)) by (field; lra).
rewrite atan_opp, atan_inv by lra.
rewrite atan_opp. ring.
Qed.

(** Above the [x] axis, [Ratan2 r t = PI / 2 - atan (t / r)] for every [t]:
    for [t > 0] by [atan_inv], as [r / t = / (t / r)]; for [t < 0] by
    [ar_atan_inv_neg] and the [+ PI] of the definition; for [t = 0] as
    [atan 0 = 0]. *)
Lemma ar_up : forall r t, 0 < r -> Ratan2 r t = PI / 2 - atan (t / r).
Proof.
intros r t Hr. unfold Ratan2.
destruct (Rlt_dec 0 t) as [Ht|Ht].
- rewrite (ar_div_inv r t) by lra. apply atan_inv, Rdiv_lt_0_compat; assumption.
- destruct (Rlt_dec t 0) as [Ht'|Ht'].
  + destruct (Rle_dec 0 r) as [_|Hr']; [|lra].
    rewrite (ar_div_inv r t) by lra.
    rewrite ar_atan_inv_neg by (apply ar_div_lt_np; assumption). lra.
  + destruct (Rlt_dec 0 r) as [_|Hr']; [|lra].
    assert (Ht0 : t = 0) by lra. subst t.
    unfold Rdiv. rewrite Rmult_0_l, atan_0. ring.
Qed.

(** Below the [x] axis, [Ratan2 r t = - (PI / 2) - atan (t / r)] for every
    [t], in the same way. *)
Lemma ar_lo : forall r t, r < 0 -> Ratan2 r t = - (PI / 2) - atan (t / r).
Proof.
intros r t Hr. unfold Ratan2.
destruct (Rlt_dec 0 t) as [Ht|Ht].
- rewrite (ar_div_inv r t) by lra. apply ar_atan_inv_neg, ar_div_lt_pn; assumption.
- destruct (Rlt_dec t 0) as [Ht'|Ht'].
  + destruct (Rle_dec 0 r) as [Hr'|_]; [lra|].
    rewrite (ar_div_inv r t) by lra.
    rewrite atan_inv by (apply ar_div_lt_nn; assumption). lra.
  + destruct (Rlt_dec 0 r) as [Hr'|_]; [lra|].
    destruct (Rlt_dec r 0) as [_|Hr']; [|lra].
    assert (Ht0 : t = 0) by lra. subst t.
    unfold Rdiv. rewrite Rmult_0_l, atan_0. ring.
Qed.

(** ** The argument

    [Ratan2 r t] is the principal value of the argument of [(t, r)]: the
    angle [u] in [(-PI, PI]] with [t = ρ cos u] and [r = ρ sin u] for
    [ρ = sqrt (r² + t²)], which is the definition of IEEE 1788 (Table 9.1,
    footnote f, of the drafts P1788/D9.5 and 1788.1/D9.8). *)

Lemma Ratan2_range : forall r t, atan2_dom r t -> - PI < Ratan2 r t <= PI.
Proof.
intros r t Hd. pose proof PI_RGT_0 as HPI.
destruct (Rtotal_order r 0) as [Hr|[Hr|Hr]].
- rewrite ar_lo by exact Hr. pose proof (atan_bound (t / r)). lra.
- subst r. unfold atan2_dom in Hd.
  destruct Hd as [Hd|Hd]; [exfalso; apply Hd; reflexivity|].
  destruct (Rtotal_order t 0) as [Ht|[Ht|Ht]].
  + rewrite Ratan2_zero_y_neg by exact Ht. lra.
  + contradiction.
  + rewrite Ratan2_zero_y_pos by exact Ht. lra.
- rewrite ar_up by exact Hr. pose proof (atan_bound (t / r)). lra.
Qed.

(** For [t <> 0], [ρ = |t| sqrt (1 + (r / t)²)], as
    [r² + t² = t² (1 + (r / t)²)]. *)
Lemma ar_radius : forall r t, t <> 0 ->
  sqrt (r * r + t * t) = Rabs t * sqrt (1 + Rsqr (r / t)).
Proof.
intros r t Ht.
replace (r * r + t * t) with (Rsqr t * (1 + Rsqr (r / t)))
  by (unfold Rsqr; field; exact Ht).
pose proof (Rle_0_sqr (r / t)) as H.
rewrite sqrt_mult; [| apply Rle_0_sqr | lra].
rewrite sqrt_Rsqr_abs. reflexivity.
Qed.

(** Hence, by [cos_atan] and [sin_atan], [ρ cos (atan (r / t)) = |t|] and
    [ρ sin (atan (r / t)) = |t| (r / t)]. *)
Lemma ar_polar_atan : forall r t, t <> 0 ->
  sqrt (r * r + t * t) * cos (atan (r / t)) = Rabs t /\
  sqrt (r * r + t * t) * sin (atan (r / t)) = Rabs t * (r / t).
Proof.
intros r t Ht. rewrite ar_radius by exact Ht. rewrite cos_atan, sin_atan.
assert (Hs : 0 < sqrt (1 + Rsqr (r / t))).
{ apply sqrt_lt_R0. pose proof (Rle_0_sqr (r / t)). lra. }
split; field; lra.
Qed.

Lemma Ratan2_polar :
  forall r t, atan2_dom r t ->
  t = sqrt (r * r + t * t) * cos (Ratan2 r t) /\
  r = sqrt (r * r + t * t) * sin (Ratan2 r t).
Proof.
intros r t Hd.
destruct (Rtotal_order t 0) as [Ht|[Ht|Ht]].
- destruct (ar_polar_atan r t (Rlt_not_eq _ _ Ht)) as [Hc Hs].
  rewrite Rabs_left in Hc, Hs by exact Ht.
  assert (Hq : - t * (r / t) = - r) by (field; lra).
  destruct (Rle_dec 0 r) as [Hr|Hr].
  + rewrite Ratan2_neg_x_ge by assumption. rewrite neg_cos, neg_sin. lra.
  + rewrite Ratan2_neg_x_lt by lra.
    (* [cos (u - PI) = - cos u] and [sin (u - PI) = - sin u], by [neg_cos]
       and [neg_sin] at [u - PI]. *)
    pose proof (neg_cos (atan (r / t) - PI)) as Ec.
    pose proof (neg_sin (atan (r / t) - PI)) as Es.
    replace (atan (r / t) - PI + PI) with (atan (r / t)) in Ec, Es by ring.
    assert (Ec' : cos (atan (r / t) - PI) = - cos (atan (r / t))) by lra.
    assert (Es' : sin (atan (r / t) - PI) = - sin (atan (r / t))) by lra.
    rewrite Ec', Es'. lra.
- subst t. unfold atan2_dom in Hd.
  destruct Hd as [Hr|Hr]; [|exfalso; apply Hr; reflexivity].
  replace (r * r + 0 * 0) with (r * r) by ring.
  destruct (Rtotal_order r 0) as [Hr'|[Hr'|Hr']]; [| contradiction |].
  + rewrite Ratan2_zero_x_neg by exact Hr'.
    rewrite cos_neg, sin_neg, cos_PI2, sin_PI2.
    replace (r * r) with ((- r) * (- r)) by ring.
    rewrite sqrt_square by lra. split; ring.
  + rewrite Ratan2_zero_x_pos by exact Hr'. rewrite cos_PI2, sin_PI2.
    rewrite sqrt_square by lra. split; ring.
- destruct (ar_polar_atan r t (Rgt_not_eq _ _ Ht)) as [Hc Hs].
  rewrite Rabs_pos_eq in Hc, Hs by lra.
  assert (Hq : t * (r / t) = r) by (field; lra).
  rewrite Ratan2_pos_x by exact Ht. lra.
Qed.

(** [cos] and [sin] of [u] are those of [Ratan2 r t], as [ρ > 0]. If
    [sin u >= 0], both are in [[0, PI]] ([sin_lt_0_var] excludes
    [(-PI, 0)]), and [cos_inj] applies; otherwise both are in [(-PI, 0)]
    ([sin_ge_0] excludes [[0, PI]]), and [cos_inj] applies to their
    opposites. *)
Lemma Ratan2_polar_unique :
  forall r t u, atan2_dom r t -> - PI < u <= PI ->
  t = sqrt (r * r + t * t) * cos u -> r = sqrt (r * r + t * t) * sin u ->
  u = Ratan2 r t.
Proof.
intros r t u Hd Hu Ht Hr.
destruct (Ratan2_polar r t Hd) as [Ht' Hr'].
pose proof (Ratan2_range r t Hd) as Hth.
pose proof PI_RGT_0 as HPI.
assert (Hrho : 0 < sqrt (r * r + t * t)).
{ apply sqrt_lt_R0. pose proof (Rle_0_sqr r). pose proof (Rle_0_sqr t).
  unfold atan2_dom in Hd. destruct Hd as [Hz|Hz].
  - pose proof (Rsqr_pos_lt r Hz). unfold Rsqr in *. lra.
  - pose proof (Rsqr_pos_lt t Hz). unfold Rsqr in *. lra. }
set (th := Ratan2 r t) in *.
set (rho := sqrt (r * r + t * t)) in *.
assert (Hc : cos u = cos th) by (apply (Rmult_eq_reg_l rho); lra).
assert (Hs : sin u = sin th) by (apply (Rmult_eq_reg_l rho); lra).
destruct (Rle_dec 0 u) as [Hu0|Hu0].
- assert (Hth0 : 0 <= th).
  { destruct (Rle_dec 0 th) as [H|H]; [exact H|].
    assert (Hn : th < 0) by lra.
    pose proof (sin_lt_0_var th (proj1 Hth) Hn).
    pose proof (sin_ge_0 u Hu0 (proj2 Hu)). lra. }
  apply cos_inj; [split; lra | split; lra | exact Hc].
- assert (Hn : u < 0) by lra.
  assert (Hth0 : th < 0).
  { destruct (Rlt_dec th 0) as [H|H]; [exact H|].
    assert (Hp : 0 <= th) by lra.
    pose proof (sin_lt_0_var u (proj1 Hu) Hn).
    pose proof (sin_ge_0 th Hp (proj2 Hth)). lra. }
  assert (E : - u = - th).
  { apply cos_inj; [split; lra | split; lra |]. rewrite 2!cos_neg. exact Hc. }
  lra.
Qed.

(** ** Ranges on the half-planes and the closed quadrants *)

Lemma Ratan2_upper : forall r t, 0 < r -> 0 < Ratan2 r t < PI.
Proof.
intros r t Hr. rewrite ar_up by exact Hr. pose proof (atan_bound (t / r)). lra.
Qed.

Lemma Ratan2_lower : forall r t, r < 0 -> - PI < Ratan2 r t < 0.
Proof.
intros r t Hr. rewrite ar_lo by exact Hr. pose proof (atan_bound (t / r)). lra.
Qed.

Lemma Ratan2_right : forall r t, 0 < t -> - (PI / 2) < Ratan2 r t < PI / 2.
Proof.
intros r t Ht. rewrite Ratan2_pos_x by exact Ht. pose proof (atan_bound (r / t)). lra.
Qed.

Lemma Ratan2_q1 :
  forall r t, 0 <= r -> 0 <= t -> atan2_dom r t -> 0 <= Ratan2 r t <= PI / 2.
Proof.
intros r t Hr Ht Hd. pose proof PI_RGT_0.
destruct (Rle_lt_or_eq_dec 0 r Hr) as [Hr'|<-].
- rewrite ar_up by exact Hr'. pose proof (atan_bound (t / r)).
  pose proof (ar_atan_nonneg (t / r) (ar_div_nonneg_pos t r Ht Hr')). lra.
- unfold atan2_dom in Hd. destruct Hd as [Hd|Hd]; [exfalso; apply Hd; reflexivity|].
  rewrite Ratan2_zero_y_pos by lra. lra.
Qed.

Lemma Ratan2_q2 :
  forall r t, 0 <= r -> t <= 0 -> atan2_dom r t -> PI / 2 <= Ratan2 r t <= PI.
Proof.
intros r t Hr Ht Hd. pose proof PI_RGT_0.
destruct (Rle_lt_or_eq_dec 0 r Hr) as [Hr'|<-].
- rewrite ar_up by exact Hr'. pose proof (atan_bound (t / r)).
  pose proof (ar_atan_nonpos (t / r) (ar_div_nonpos_pos t r Ht Hr')). lra.
- unfold atan2_dom in Hd. destruct Hd as [Hd|Hd]; [exfalso; apply Hd; reflexivity|].
  rewrite Ratan2_zero_y_neg by lra. lra.
Qed.

Lemma Ratan2_q3 : forall r t, r < 0 -> t <= 0 -> - PI < Ratan2 r t <= - (PI / 2).
Proof.
intros r t Hr Ht. rewrite ar_lo by exact Hr. pose proof (atan_bound (t / r)).
pose proof (ar_atan_nonneg (t / r) (ar_div_nonpos_neg t r Ht Hr)). lra.
Qed.

Lemma Ratan2_q4 :
  forall r t, r <= 0 -> 0 <= t -> atan2_dom r t -> - (PI / 2) <= Ratan2 r t <= 0.
Proof.
intros r t Hr Ht Hd. pose proof PI_RGT_0.
destruct (Rle_lt_or_eq_dec r 0 Hr) as [Hr' | ->].
- rewrite ar_lo by exact Hr'. pose proof (atan_bound (t / r)).
  pose proof (ar_atan_nonpos (t / r) (ar_div_nonneg_neg t r Ht Hr')). lra.
- unfold atan2_dom in Hd. destruct Hd as [Hd|Hd]; [exfalso; apply Hd; reflexivity|].
  rewrite Ratan2_zero_y_pos by lra. lra.
Qed.

(** ** Monotonicity

    Above the [x] axis, [Ratan2] decreases in [t]; below it, it increases
    in [t]; right of the [y] axis, it increases in [r]; and left of it, it
    decreases in [r] on [r >= 0] and on [r < 0], with the jump between
    them. *)

Lemma Ratan2_dec_x : forall r t t', 0 < r -> t <= t' -> Ratan2 r t' <= Ratan2 r t.
Proof.
intros r t t' Hr Htt. rewrite 2!ar_up by exact Hr.
pose proof (atan_inc _ _ (ar_div_le_pos t t' r Hr Htt)). lra.
Qed.

Lemma Ratan2_inc_x : forall r t t', r < 0 -> t <= t' -> Ratan2 r t <= Ratan2 r t'.
Proof.
intros r t t' Hr Htt. rewrite 2!ar_lo by exact Hr.
pose proof (atan_inc _ _ (ar_div_le_neg t t' r Hr Htt)). lra.
Qed.

Lemma Ratan2_inc_y : forall r r' t, 0 < t -> r <= r' -> Ratan2 r t <= Ratan2 r' t.
Proof.
intros r r' t Ht Hrr. rewrite 2!Ratan2_pos_x by exact Ht.
apply atan_inc, ar_div_le_pos; assumption.
Qed.

Lemma Ratan2_dec_y_ge :
  forall r r' t, t < 0 -> 0 <= r -> r <= r' -> Ratan2 r' t <= Ratan2 r t.
Proof.
intros r r' t Ht Hr Hrr.
rewrite (Ratan2_neg_x_ge r' t), (Ratan2_neg_x_ge r t) by lra.
pose proof (atan_inc _ _ (ar_div_le_neg r r' t Ht Hrr)). lra.
Qed.

Lemma Ratan2_dec_y_lt :
  forall r r' t, t < 0 -> r <= r' -> r' < 0 -> Ratan2 r' t <= Ratan2 r t.
Proof.
intros r r' t Ht Hrr Hr'.
rewrite (Ratan2_neg_x_lt r' t), (Ratan2_neg_x_lt r t) by lra.
pose proof (atan_inc _ _ (ar_div_le_neg r r' t Ht Hrr)). lra.
Qed.

(** ** Limits

    Each lemma gives a point beyond any bound [M] where [Ratan2] is within
    [eps] of its limit: 0 as [t] goes to +inf, [PI] or [-PI] as [t] goes
    to -inf above or below the [x] axis, [PI / 2] or [- (PI / 2)] as [r]
    goes to +inf or -inf, and [-PI] as [r] goes to 0 from below, left of
    the [y] axis. *)

(** [atan_cont] as epsilon-delta, without the [x <> u] of [continue_in]. *)
Lemma ar_atan_cont_eps : forall u eps, 0 < eps -> exists delta, 0 < delta /\
  forall x, Rabs (x - u) < delta -> Rabs (atan x - atan u) < eps.
Proof.
intros u eps Heps.
destruct (continue_in_elim atan no_cond u (atan_cont u) eps Heps) as (d & Hd & H).
exists d. split; [exact Hd|]. intros x Hx.
destruct (Req_dec u x) as [<-|Hne].
- replace (atan u - atan u) with 0 by ring. rewrite Rabs_R0. exact Heps.
- apply H; [exact I | exact Hne | exact Hx].
Qed.

(** A point [s >= M], [s > 0], with [|a / s| < delta]: any
    [s >= (|a| + 1) / delta]. *)
Lemma ar_small_quot : forall a delta M, 0 < delta ->
  exists s, M <= s /\ 0 < s /\ Rabs (a / s) < delta.
Proof.
intros a d M Hd.
exists (Rmax 1 (Rmax M ((Rabs a + 1) / d))).
pose proof (Rmax_l 1 (Rmax M ((Rabs a + 1) / d))) as S1.
pose proof (Rmax_r 1 (Rmax M ((Rabs a + 1) / d))) as S2.
pose proof (Rmax_l M ((Rabs a + 1) / d)) as S3.
pose proof (Rmax_r M ((Rabs a + 1) / d)) as S4.
set (s := Rmax 1 (Rmax M ((Rabs a + 1) / d))) in *.
assert (Hq : (Rabs a + 1) / d * d = Rabs a + 1) by (field; lra).
set (q := (Rabs a + 1) / d) in *.
assert (Hs : 0 < s) by lra.
split; [lra|]. split; [exact Hs|].
unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ s)) by (left; apply Rinv_0_lt_compat, Hs).
apply (Rmult_lt_reg_r s); [exact Hs|].
rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r.
(* [|a| < d * s], as [d * s >= d * q = |a| + 1]. *)
assert (d * q <= d * s) by (apply Rmult_le_compat_l; lra).
lra.
Qed.

Lemma Ratan2_x_pinf :
  forall r eps M, 0 < eps -> exists t, M <= t /\ 0 < t /\ Rabs (Ratan2 r t) < eps.
Proof.
intros r eps M Heps.
destruct (ar_atan_cont_eps 0 eps Heps) as (d & Hd & H).
destruct (ar_small_quot r d M Hd) as (t & Ht1 & Ht2 & Ht3).
exists t. split; [exact Ht1|]. split; [exact Ht2|].
rewrite Ratan2_pos_x by exact Ht2.
specialize (H (r / t)). rewrite atan_0, !Rminus_0_r in H. apply H, Ht3.
Qed.

(** For [r > 0], [atan_glb] gives [u] with [atan u < - (PI / 2) + eps];
    then [t = r w] for [w = min u (M / r) (-1)]. *)
Lemma Ratan2_x_ninf_pos :
  forall r eps M, 0 < r -> 0 < eps -> exists t, t <= M /\ t < 0 /\ PI - eps < Ratan2 r t.
Proof.
intros r eps M Hr Heps.
destruct atan_glb as [_ Hg]. destruct (Hg eps Heps) as (u & Hu).
pose proof (Rmin_l u (Rmin (M / r) (-1))) as W1.
pose proof (Rmin_r u (Rmin (M / r) (-1))) as W2.
pose proof (Rmin_l (M / r) (-1)) as W3.
pose proof (Rmin_r (M / r) (-1)) as W4.
set (w := Rmin u (Rmin (M / r) (-1))) in *.
exists (r * w).
assert (E : r * (M / r) = M) by (field; lra).
assert (B1 : r * w <= r * (M / r)) by (apply Rmult_le_compat_l; lra).
assert (B2 : r * w <= r * (-1)) by (apply Rmult_le_compat_l; lra).
split; [lra|]. split; [lra|].
rewrite ar_up by exact Hr.
replace (r * w / r) with w by (field; lra).
pose proof (atan_inc w u W1). lra.
Qed.

(** For [r < 0], [atan_lub] gives [u] with [PI / 2 - eps < atan u]; then
    [t = r w] for [w = max u (M / r) 1]. *)
Lemma Ratan2_x_ninf_neg :
  forall r eps M, r < 0 -> 0 < eps ->
  exists t, t <= M /\ t < 0 /\ Ratan2 r t < - PI + eps.
Proof.
intros r eps M Hr Heps.
destruct atan_lub as [_ Hg]. destruct (Hg eps Heps) as (u & Hu).
pose proof (Rmax_l u (Rmax (M / r) 1)) as W1.
pose proof (Rmax_r u (Rmax (M / r) 1)) as W2.
pose proof (Rmax_l (M / r) 1) as W3.
pose proof (Rmax_r (M / r) 1) as W4.
set (w := Rmax u (Rmax (M / r) 1)) in *.
exists (r * w).
assert (E : r * (M / r) = M) by (field; lra).
assert (B1 : r * w <= r * (M / r)) by (apply Rmult_le_compat_neg_l; lra).
assert (B2 : r * w <= r * 1) by (apply Rmult_le_compat_neg_l; lra).
split; [lra|]. split; [lra|].
rewrite ar_lo by exact Hr.
replace (r * w / r) with w by (field; lra).
pose proof (atan_inc u w W1). lra.
Qed.

Lemma Ratan2_y_pinf :
  forall t eps M, 0 < eps -> exists r, M <= r /\ 0 < r /\ PI / 2 - eps < Ratan2 r t.
Proof.
intros t eps M Heps.
destruct (ar_atan_cont_eps 0 eps Heps) as (d & Hd & H).
destruct (ar_small_quot t d M Hd) as (r & Hr1 & Hr2 & Hr3).
exists r. split; [exact Hr1|]. split; [exact Hr2|].
rewrite ar_up by exact Hr2.
specialize (H (t / r)). rewrite atan_0, !Rminus_0_r in H.
pose proof (H Hr3) as H'. apply Rabs_def2 in H'. lra.
Qed.

Lemma Ratan2_y_ninf :
  forall t eps M, 0 < eps ->
  exists r, r <= M /\ r < 0 /\ Ratan2 r t < - (PI / 2) + eps.
Proof.
intros t eps M Heps.
destruct (ar_atan_cont_eps 0 eps Heps) as (d & Hd & H).
destruct (ar_small_quot t d (- M) Hd) as (s & Hs1 & Hs2 & Hs3).
exists (- s). split; [lra|]. split; [lra|].
rewrite ar_lo by lra.
replace (t / - s) with (- (t / s)) by (field; lra).
rewrite atan_opp.
specialize (H (t / s)). rewrite atan_0, !Rminus_0_r in H.
pose proof (H Hs3) as H'. apply Rabs_def2 in H'. lra.
Qed.

(** For [t < 0] and [r0 = delta t / 2 <= r < 0], [0 <= r / t <= delta / 2],
    so [atan (r / t)] is within [eps] of [atan 0 = 0]. *)
Lemma Ratan2_y_0neg :
  forall t eps, t < 0 -> 0 < eps ->
  exists r0, r0 < 0 /\ forall r, r0 <= r -> r < 0 -> Ratan2 r t < - PI + eps.
Proof.
intros t eps Ht Heps.
destruct (ar_atan_cont_eps 0 eps Heps) as (d & Hd & H).
exists (d * t / 2). split.
- assert (d * t < 0) by nra. lra.
- intros r Hr0 Hr.
  rewrite Ratan2_neg_x_lt by assumption.
  assert (Hq0 : 0 <= r / t) by (apply ar_div_nonpos_neg; lra).
  assert (Hq1 : r / t <= d * t / 2 / t) by (apply ar_div_le_neg; assumption).
  replace (d * t / 2 / t) with (d / 2) in Hq1 by (field; lra).
  specialize (H (r / t)). rewrite atan_0, !Rminus_0_r in H.
  assert (Hq : Rabs (r / t) < d) by (rewrite Rabs_pos_eq by exact Hq0; lra).
  pose proof (H Hq) as H'. apply Rabs_def2 in H'. lra.
Qed.

(** ** Continuity *)

(** The quotient [a' / c'] is within [e] of [a / c], [c <> 0], for
    [(a', c')] within [delta] of [(a, c)], where [c'] has the sign of [c]:
    for [|c' - c| < |c| / 2], [c c' > c² / 2]; and
    [(a' / c' - a / c) (c c') = (a' - a) c - a (c' - c)], whose absolute
    value is below [delta (|a| + |c|)], which is at most [e c² / 2] for
    [delta <= e c² / (2 (|a| + |c|))]. *)
Lemma ar_div_cont : forall a c e, c <> 0 -> 0 < e ->
  exists delta, 0 < delta /\ forall a' c',
  Rabs (a' - a) < delta -> Rabs (c' - c) < delta ->
  0 < c * c' /\ Rabs (a' / c' - a / c) < e.
Proof.
intros a c e Hc He.
assert (Pc : 0 < Rabs c) by (apply Rabs_pos_lt, Hc).
pose proof (Rabs_pos a) as Pa.
assert (Hc2 : 0 < c * c) by (pose proof (Rsqr_pos_lt c Hc); unfold Rsqr in *; lra).
assert (Hcc : Rabs c * Rabs c = c * c) by (rewrite <- Rabs_mult; apply Rabs_pos_eq; lra).
set (k := Rabs a + Rabs c).
assert (Hk : 0 < k) by (unfold k; lra).
set (delta := Rmin (Rabs c / 2) (e * (c * c) / (2 * k))).
assert (D0 : 0 < delta).
{ apply Rmin_pos; [lra|]. apply Rdiv_lt_0_compat; [|lra].
  apply Rmult_lt_0_compat; assumption. }
assert (D1 : delta <= Rabs c / 2) by apply Rmin_l.
assert (D2 : delta * k <= e * (c * c) / 2).
{ assert (D2' : delta <= e * (c * c) / (2 * k)) by apply Rmin_r.
  assert (D3 : delta * k <= e * (c * c) / (2 * k) * k) by (apply Rmult_le_compat_r; lra).
  replace (e * (c * c) / (2 * k) * k) with (e * (c * c) / 2) in D3 by (field; lra).
  exact D3. }
exists delta. split; [exact D0|].
intros a' c' Ha Hc'.
assert (Hcc' : c * c / 2 < c * c').
{ pose proof (Rle_abs (- (c * (c' - c)))) as R1.
  rewrite Rabs_Ropp, Rabs_mult in R1.
  assert (R2 : Rabs c * Rabs (c' - c) < Rabs c * (Rabs c / 2))
    by (apply Rmult_lt_compat_l; lra).
  lra. }
split; [lra|].
assert (Hc'0 : c' <> 0) by (intro E; rewrite E, Rmult_0_r in Hcc'; lra).
assert (Hn : Rabs ((a' - a) * c + - (a * (c' - c))) < delta * k).
{ pose proof (Rabs_triang ((a' - a) * c) (- (a * (c' - c)))) as T.
  rewrite Rabs_Ropp, 2!Rabs_mult in T.
  assert (B1 : Rabs (a' - a) * Rabs c < delta * Rabs c)
    by (apply Rmult_lt_compat_r; lra).
  assert (B2 : Rabs a * Rabs (c' - c) <= Rabs a * delta)
    by (apply Rmult_le_compat_l; lra).
  unfold k. lra. }
assert (Hx : (a' / c' - a / c) * (c * c') = (a' - a) * c + - (a * (c' - c)))
  by (field; tauto).
assert (Hn' : Rabs (a' / c' - a / c) * (c * c') < delta * k).
{ rewrite <- (Rabs_pos_eq (c * c')) by lra. rewrite <- Rabs_mult, Hx. exact Hn. }
assert (E1 : e * (c * c / 2) < e * (c * c')) by (apply Rmult_lt_compat_l; assumption).
apply (Rmult_lt_reg_r (c * c')); [lra|]. lra.
Qed.

(** Hence [atan (a' / c')] is continuous at [(a, c)] for [c <> 0], by
    [atan_cont] at [a / c]. *)
Lemma ar_atan_quot_cont : forall a c eps, c <> 0 -> 0 < eps ->
  exists delta, 0 < delta /\ forall a' c',
  Rabs (a' - a) < delta -> Rabs (c' - c) < delta ->
  0 < c * c' /\ Rabs (atan (a' / c') - atan (a / c)) < eps.
Proof.
intros a c eps Hc Heps.
destruct (ar_atan_cont_eps (a / c) eps Heps) as (d1 & Hd1 & H1).
destruct (ar_div_cont a c d1 Hc Hd1) as (d & Hd & H).
exists d. split; [exact Hd|]. intros a' c' Ha Hc'.
destruct (H a' c' Ha Hc') as [Hs Hq]. split; [exact Hs|]. apply H1, Hq.
Qed.

(** [Ratan2] is continuous at each point off the closed half-line
    [r = 0], [t <= 0]. *)
Lemma Ratan2_cont : forall r t, r <> 0 \/ 0 < t -> continuity2_pt Ratan2 r t.
Proof.
intros r t Hd. unfold continuity2_pt, continue_in2. intros eps Heps.
destruct (Rlt_dec 0 t) as [Ht|Ht].
- (* Near [(r, t)], [t' > 0] and [Ratan2 r' t' = atan (r' / t')]. *)
  destruct (ar_atan_quot_cont r t eps (Rgt_not_eq _ _ Ht) Heps) as (d & Hd' & H).
  exists d. split; [exact Hd'|]. intros r' t' _ _ Hr Ht2.
  destruct (H r' t' Hr Ht2) as [Hs Hq].
  assert (Ht' : 0 < t') by nra.
  rewrite 2!Ratan2_pos_x by assumption. exact Hq.
- destruct Hd as [Hr|Hr]; [|contradiction].
  destruct (Rtotal_order r 0) as [Hr0|[Hr0|Hr0]]; [| contradiction |].
  + (* Near [(r, t)], [r' < 0] and [Ratan2 r' t' = - (PI / 2) - atan (t' / r')]. *)
    destruct (ar_atan_quot_cont t r eps Hr Heps) as (d & Hd' & H).
    exists d. split; [exact Hd'|]. intros r' t' _ _ Hr2 Ht2.
    destruct (H t' r' Ht2 Hr2) as [Hs Hq].
    assert (Hr' : r' < 0) by nra.
    rewrite (ar_lo r' t' Hr'), (ar_lo r t Hr0).
    replace (- (PI / 2) - atan (t' / r') - (- (PI / 2) - atan (t / r)))
      with (- (atan (t' / r') - atan (t / r))) by ring.
    rewrite Rabs_Ropp. exact Hq.
  + (* Near [(r, t)], [r' > 0] and [Ratan2 r' t' = PI / 2 - atan (t' / r')]. *)
    destruct (ar_atan_quot_cont t r eps Hr Heps) as (d & Hd' & H).
    exists d. split; [exact Hd'|]. intros r' t' _ _ Hr2 Ht2.
    destruct (H t' r' Ht2 Hr2) as [Hs Hq].
    assert (Hr' : 0 < r') by nra.
    rewrite (ar_up r' t' Hr'), (ar_up r t Hr0).
    replace (PI / 2 - atan (t' / r') - (PI / 2 - atan (t / r)))
      with (- (atan (t' / r') - atan (t / r))) by ring.
    rewrite Rabs_Ropp. exact Hq.
Qed.

(** Its restriction to [r >= 0], [t < 0] is continuous, as it is
    [atan (r / t) + PI] there. *)
Lemma Ratan2_cont_upper :
  forall r t, 0 <= r -> t < 0 ->
  continue_in2 Ratan2 (fun r' => 0 <= r') (fun t' => t' < 0) r t.
Proof.
intros r t Hr Ht. unfold continue_in2. intros eps Heps.
destruct (ar_atan_quot_cont r t eps (Rlt_not_eq _ _ Ht) Heps) as (d & Hd & H).
exists d. split; [exact Hd|]. intros r' t' Hr' Ht' Hr2 Ht2.
cbv beta in Hr', Ht'.
destruct (H r' t' Hr2 Ht2) as [_ Hq].
rewrite (Ratan2_neg_x_ge r' t' Ht' Hr'), (Ratan2_neg_x_ge r t Ht Hr).
replace (atan (r' / t') + PI - (atan (r / t) + PI))
  with (atan (r' / t') - atan (r / t)) by ring.
exact Hq.
Qed.

(** It is not continuous relative to its domain at a point [(0, t)] with
    [t < 0], where it is [PI], as it is near [-PI] just below. *)
Lemma Ratan2_not_cont : forall t, t < 0 -> ~ continue_in2_set Ratan2 atan2_dom 0 t.
Proof.
intros t Ht H. pose proof PI_RGT_0 as HPI.
unfold continue_in2_set in H.
destruct (H PI HPI) as (d & Hd & Hc).
assert (Hr : - (d / 2) < 0) by lra.
assert (Hdom : atan2_dom (- (d / 2)) t) by (left; lra).
assert (H1 : Rabs (- (d / 2) - 0) < d).
{ rewrite Rminus_0_r, Rabs_Ropp, Rabs_pos_eq by lra. lra. }
assert (H2 : Rabs (t - t) < d).
{ replace (t - t) with 0 by ring. rewrite Rabs_R0. exact Hd. }
specialize (Hc _ _ Hdom H1 H2).
rewrite Ratan2_zero_y_neg in Hc by exact Ht.
pose proof (Ratan2_lower (- (d / 2)) t Hr).
apply Rabs_def2 in Hc. lra.
Qed.

(** Nor relative to a box with points just below such a point. *)
Lemma Ratan2_not_cont_in2 :
  forall (Y X : R -> Prop) t, t < 0 -> X t ->
  (forall eps, 0 < eps -> exists r, Y r /\ - eps < r < 0) ->
  ~ continue_in2 Ratan2 Y X 0 t.
Proof.
intros Y X t Ht HXt HY H. pose proof PI_RGT_0 as HPI.
unfold continue_in2 in H.
destruct (H PI HPI) as (d & Hd & Hc).
destruct (HY d Hd) as (r & HYr & Hr1 & Hr2).
assert (H1 : Rabs (r - 0) < d).
{ rewrite Rminus_0_r, Rabs_left by exact Hr2. lra. }
assert (H2 : Rabs (t - t) < d).
{ replace (t - t) with 0 by ring. rewrite Rabs_R0. exact Hd. }
specialize (Hc r t HYr HXt H1 H2).
rewrite Ratan2_zero_y_neg in Hc by exact Ht.
pose proof (Ratan2_lower r t Hr2).
apply Rabs_def2 in Hc. lra.
Qed.
