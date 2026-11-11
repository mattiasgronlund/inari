(** * The odd series of [asinh] and [atanh] near 0

    [DyadicLog.odd_series] of [Model.v] computes [t + t^3 P(t^2)] for a
    [t] in [[2^-27, 2^-8)], where [P] is a polynomial of degree 3 with
    [f64] coefficients: [t^2] rounded to nearest, Horner's scheme for [P]
    in it, [c = (t u) p] with each product rounded, then [t + c] as a
    double-double by Fast2Sum (exact, as [|c| < t]), scaled by
    [Fast.normalize] into [[1, 2)]. [odd_series_err] bounds it for any
    coefficients with [1/8 <= |c0| <= 1/2] and [|c1|, |c2|, |c3| <= 1/4]:
    [c] is within [(4 * 2^-53 |c0| + 2^-60) t^3] of [t^3 P(t^2)], and the
    scaled [t] stays below [2 (1 + 2^-14)], so that a function within [E t^3]
    of [t + t^3 P(t^2)] is within [2^-67] of the scaled double-double where
    [(1 + 2^-14) (E + 4 * 2^-53 |c0| + 2^-60) <= 2^-52].
    - [asinh_odd_correct]: with [ASINH_ODD] (RN(-1/6), RN(3/40),
      RN(-5/112), RN(35/1152)), from the Taylor bound [asinh_taylor9] of
      [AsinhTaylor.v].
    - [atanh_odd_correct]: with [ATANH_ODD] (RN(1/3), RN(1/5), RN(1/7),
      RN(1/9)), from the series bound [atanh_sum_bounds] of
      [AtanhSeries.v]. *)

From Stdlib Require Import ZArith Reals Lra Lia Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Relative.
From Inari Require Import Model Elementary Encoding TwoSum FastExpErr FastRoundErr
  CancelLanes AtanhSeries AsinhTaylor.

Open Scope R_scope.

(** ** Helpers *)

(** Powers of 2 as numerals, for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp].

(** [B2R l] of an [f64] literal [l] in the goal, as [m * 2^e] (as
    [lit_R] of [FastSinhHorner.v]). *)
Local Ltac lit_R l :=
  rewrite <- (SF2R_B2SF _ _ l);
  let s := eval vm_compute in (B2SF l) in
  replace (B2SF l) with s by (vm_compute; reflexivity);
  cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR.

(** Rounding to nearest of an [x] of at least [2^-1022] in magnitude moves
    it by at most [2^-53 |x|] (as [rn_rel] of [FastSinhHorner.v]). *)
Local Lemma od_rel :
  forall x, bpow radix2 (-1022) <= Rabs x -> Rabs (RN x - x) <= bpow radix2 (-53) * Rabs x.
Proof.
intros x Hx.
assert (H : Rabs (RN x - x) <= / 2 * bpow radix2 (- 53 + 1) * Rabs x)
  by exact (relative_error_N_FLT radix2 (-1074) 53 eq_refl (fun z => negb (Z.even z)) x Hx).
change (- 53 + 1)%Z with (-52)%Z in H.
assert (E : / 2 * bpow radix2 (-52) = bpow radix2 (-53))
  by (cbn [bpow radix_val radix2]; lra).
rewrite E in H. exact H.
Qed.

(** ** Horner's scheme

    A step [x q] or [c + q] of the scheme (as [mul_step] and [add_step]
    of [FastSinhHorner.v], with [|x|, |v| <= U] in place of [1/16]), with
    [x] within [dl] of [v], [q] within [D] of [y] and [c] within [G] of
    [g], is within [D'] of [v y] or [g + y]: the rounding of an exact
    result of at most [K] adds [2^-53 K + 2^-1075]. *)

Local Lemma od_mul :
  forall x q v y U Y D dl D',
  is_finite x = true -> is_finite q = true ->
  Rabs (B2R x) <= U -> Rabs v <= U -> Rabs (B2R x - v) <= dl ->
  Rabs (B2R q - y) <= D -> Rabs y <= Y -> U * (Y + D) <= 16 ->
  bpow radix2 (-53) * (U * (Y + D)) + bpow radix2 (-1075) + U * D + dl * Y <= D' ->
  is_finite (mul x q) = true /\ Rabs (B2R (mul x q) - v * y) <= D' /\
  Rabs (v * y) <= U * Y.
Proof.
intros x q v y U Y D dl D' Fx Fq Hx Hv Hd Hq Hy HYD HD.
assert (Aq : Rabs (B2R q) <= Y + D).
{ apply Rabs_le_inv in Hq. apply Rabs_le_inv in Hy. apply Rabs_le. lra. }
assert (Hm : Rabs (B2R x * B2R q) <= U * (Y + D)) by (apply Rabs_mul_le; assumption).
destruct (mul_k x q (U * (Y + D)) Fx Fq Hm HYD) as (F & _ & B).
(* [x q - v y = x (q - y) + (x - v) y]. *)
assert (H1 : Rabs (B2R x * (B2R q - y)) <= U * D) by (apply Rabs_mul_le; assumption).
assert (H2 : Rabs ((B2R x - v) * y) <= dl * Y) by (apply Rabs_mul_le; assumption).
assert (H3 : Rabs (v * y) <= U * Y) by (apply Rabs_mul_le; assumption).
apply Rabs_le_inv in B, H1, H2.
split; [exact F | split; [apply Rabs_le; lra | exact H3]].
Qed.

Local Lemma od_add :
  forall c q g y K G D D',
  is_finite c = true -> is_finite q = true ->
  Rabs (B2R c - g) <= G -> Rabs (B2R q - y) <= D -> Rabs (g + y) <= K -> K + G + D <= 16 ->
  bpow radix2 (-53) * (K + G + D) + bpow radix2 (-1075) + G + D <= D' ->
  is_finite (add c q) = true /\ Rabs (B2R (add c q) - (g + y)) <= D'.
Proof.
intros c q g y K G D D' Fc Fq Hc Hq Hs HK HD.
apply Rabs_le_inv in Hc, Hq, Hs.
assert (Hm : Rabs (B2R c + B2R q) <= K + G + D) by (apply Rabs_le; lra).
destruct (add_k c q (K + G + D) Fc Fq Hm HK) as (F & _ & B).
apply Rabs_le_inv in B.
split; [exact F | apply Rabs_le; lra].
Qed.

(** [|a + b| <= A + B] from [|a| <= A] and [|b| <= B]. *)
Local Lemma od_sum :
  forall a b A B, Rabs a <= A -> Rabs b <= B -> Rabs (a + b) <= A + B.
Proof.
intros a b A B Ha Hb. apply Rabs_le_inv in Ha, Hb. apply Rabs_le. lra.
Qed.

(** Horner's scheme [p] of [P(v) = x0 + v (x1 + v (x2 + v x3))] in an [u]
    within [2^-69] of [v], both at most [2^-15]: [p] is within [2^-53 |x0|
    + 2^-67] of [P(v)], since only its last sum is not scaled by [v]. *)
Local Lemma odd_horner :
  forall u v x0 x1 x2 x3,
  is_finite u = true -> is_finite x0 = true -> is_finite x1 = true ->
  is_finite x2 = true -> is_finite x3 = true ->
  0 <= B2R u <= bpow radix2 (-15) -> 0 <= v <= bpow radix2 (-15) ->
  Rabs (B2R u - v) <= bpow radix2 (-69) ->
  Rabs (B2R x0) <= / 2 -> Rabs (B2R x1) <= / 4 -> Rabs (B2R x2) <= / 4 ->
  Rabs (B2R x3) <= / 4 ->
  is_finite (add x0 (mul u (add x1 (mul u (add x2 (mul u x3)))))) = true /\
  Rabs (B2R (add x0 (mul u (add x1 (mul u (add x2 (mul u x3)))))) -
    (B2R x0 + v * (B2R x1 + v * (B2R x2 + v * B2R x3))))
    <= bpow radix2 (-53) * Rabs (B2R x0) + bpow radix2 (-67) /\
  Rabs (v * (B2R x1 + v * (B2R x2 + v * B2R x3))) <= bpow radix2 (-16).
Proof.
intros u v x0 x1 x2 x3 Fu F0 F1 F2 F3 Hu Hv Hd H0 H1 H2 H3.
assert (Au : Rabs (B2R u) <= bpow radix2 (-15)) by (rewrite Rabs_pos_eq; lra).
assert (Av : Rabs v <= bpow radix2 (-15)) by (rewrite Rabs_pos_eq; lra).
assert (Z : forall z, Rabs (z - z) <= 0)
  by (intros z; replace (z - z) with 0 by ring; rewrite Rabs_R0; lra).
(* Innermost first: each step's error bound and the bound of its exact
   value. *)
destruct (od_mul u x3 v (B2R x3) (bpow radix2 (-15)) (/ 4) 0 (bpow radix2 (-69))
  (bpow radix2 (-69)) Fu F3 Au Av Hd (Z _) H3 ltac:(num; lra) ltac:(num; lra))
  as (Fm3 & Em3 & Wm3).
pose proof (od_sum _ _ _ _ H2 Wm3) as S2.
destruct (od_add x2 (mul u x3) (B2R x2) (v * B2R x3) _ 0 (bpow radix2 (-69))
  (bpow radix2 (-54)) F2 Fm3 (Z _) Em3 S2 ltac:(num; lra) ltac:(num; lra))
  as (Fa2 & Ea2).
destruct (od_mul u _ v _ (bpow radix2 (-15)) _ (bpow radix2 (-54)) (bpow radix2 (-69))
  (bpow radix2 (-68)) Fu Fa2 Au Av Hd Ea2 S2 ltac:(num; lra) ltac:(num; lra))
  as (Fm2 & Em2 & Wm2).
pose proof (od_sum _ _ _ _ H1 Wm2) as S1.
destruct (od_add x1 _ (B2R x1) _ _ 0 (bpow radix2 (-68)) (bpow radix2 (-54)) F1 Fm2 (Z _)
  Em2 S1 ltac:(num; lra) ltac:(num; lra)) as (Fa1 & Ea1).
destruct (od_mul u _ v _ (bpow radix2 (-15)) _ (bpow radix2 (-54)) (bpow radix2 (-69))
  (bpow radix2 (-68)) Fu Fa1 Au Av Hd Ea1 S1 ltac:(num; lra) ltac:(num; lra))
  as (Fm1 & Em1 & Wm1).
pose proof (od_sum _ _ _ _ (Rle_refl (Rabs (B2R x0))) Wm1) as S0.
destruct (od_add x0 _ (B2R x0) _ _ 0 (bpow radix2 (-68))
  (bpow radix2 (-53) * Rabs (B2R x0) + bpow radix2 (-67)) F0 Fm1 (Z _) Em1 S0
  ltac:(num; lra) ltac:(num; lra)) as (Fp & Ep).
split; [exact Fp | split; [exact Ep |]].
eapply Rle_trans; [exact Wm1 | num; lra].
Qed.

(** ** The products and the sum *)

(** [2^-53] in the form [num] gives it, which [lra] reads as a constant. *)
Local Notation eps53 := (/ IZR (Z.pow_pos 2 53)) (only parsing).

(** With [u] within [2^-53 v] of [v], [w] within [2^-53 |t u|] of [t u],
    [c] within [2^-53 |w p|] of [w p], and [p] within [2^-53 a + 2^-67] of
    [P], [c] is within [(4 * 2^-53 a + 2^-60) t v] of [t v P]: [c - t v P
    = (c - w p) + (w - t u) p + t (u - v) p + t v (p - P)], and each
    of the first three is at most [2^-53 (1 + 2^-53)^2 t v |p|]. *)
Local Lemma odd_prod :
  forall T v U W C p P a,
  0 <= T -> 0 <= v -> Rabs (U - v) <= bpow radix2 (-53) * v ->
  Rabs (W - T * U) <= bpow radix2 (-53) * Rabs (T * U) ->
  Rabs (C - W * p) <= bpow radix2 (-53) * Rabs (W * p) ->
  Rabs (p - P) <= bpow radix2 (-53) * a + bpow radix2 (-67) ->
  Rabs P <= a + bpow radix2 (-16) -> 0 <= a <= / 2 ->
  Rabs (C - T * v * P) <= T * v * (4 * bpow radix2 (-53) * a + bpow radix2 (-60)).
Proof.
intros T v U W C p P a HT Hv HU HW HC Hp HP Ha.
rewrite Rabs_mult in HC.
cbn [bpow radix_val radix2 Z.opp] in HU, HW, HC, Hp, HP |- *.
apply Rabs_le_inv in HU.
(* [0 <= u <= (1 + e) v], so [0 <= t u <= (1 + e) t v], with [e = 2^-53]
   a constant (as [eps53]), so that the bounds below stay linear for
   [lra]. *)
assert (TU0 : 0 <= T * U) by (apply Rmult_le_pos; lra).
assert (TU1 : T * U <= T * (v * (1 + eps53))) by (apply Rmult_le_compat_l; lra).
rewrite (Rabs_pos_eq (T * U)) in HW by exact TU0.
apply Rabs_le_inv in HW.
assert (TV : 0 <= T * v) by (apply Rmult_le_pos; lra).
(* [|w| <= (1 + e)^2 t v] and [|p| <= q = (1 + e) a + 2^-16 + 2^-67]. *)
assert (AW : Rabs W <= T * v * ((1 + eps53) * (1 + eps53))) by (apply Rabs_le; lra).
set (q := (1 + eps53) * a + / IZR (Z.pow_pos 2 16) + / IZR (Z.pow_pos 2 67)).
assert (Ap : Rabs p <= q).
{ apply Rabs_le_inv in Hp, HP. apply Rabs_le. unfold q. lra. }
assert (P1 : Rabs W * Rabs p <= T * v * ((1 + eps53) * (1 + eps53)) * q)
  by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact AW | exact Ap]).
assert (P2 : Rabs ((W - T * U) * p) <= eps53 * (T * v * (1 + eps53)) * q).
{ rewrite Rabs_mult. apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | | exact Ap].
  apply Rabs_le. lra. }
assert (P3 : Rabs (T * (U - v) * p) <= T * (eps53 * v) * q).
{ rewrite Rabs_mult. apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | | exact Ap].
  rewrite Rabs_mult, (Rabs_pos_eq T) by exact HT. apply Rmult_le_compat_l; [exact HT |].
  apply Rabs_le. lra. }
assert (P4 : Rabs (T * v * (p - P)) <= T * v * (eps53 * a + / IZR (Z.pow_pos 2 67))).
{ rewrite Rabs_mult, (Rabs_pos_eq (T * v)) by exact TV.
  apply Rmult_le_compat_l; [exact TV | exact Hp]. }
assert (A0 : 0 <= T * v * a <= T * v * / 2).
{ split; [apply Rmult_le_pos; lra | apply Rmult_le_compat_l; lra]. }
apply Rabs_le_inv in HC, P2, P3, P4.
unfold q in *.
apply Rabs_le. lra.
Qed.

(** ** The generic series *)

(** [odd_series] with coefficients [1/8 <= |c0| <= 1/2] and [|c1|, |c2|,
    |c3| <= 1/4], for a [t] in [[2^-27, 2^-8)] and a [y] within [E t^3] of
    [t + t^3 P(t^2)]: [h + l] is [(t + c) 2^-k] for a [c] within
    [(4 * 2^-53 |c0| + 2^-60) t^3] of [t^3 P(t^2)] ([odd_prod]), and
    [t (1 - 2^-15) <= h0 < 2^(k+1)] for the [h0] before scaling, so [2^-k
    t <= 2 (1 + 2^-14)]. *)
Local Lemma odd_series_err :
  forall t c0 c1 c2 c3 h l k y E,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < bpow radix2 (-8) ->
  is_finite (from_bits c0) = true -> is_finite (from_bits c1) = true ->
  is_finite (from_bits c2) = true -> is_finite (from_bits c3) = true ->
  / 8 <= Rabs (B2R (from_bits c0)) <= / 2 -> Rabs (B2R (from_bits c1)) <= / 4 ->
  Rabs (B2R (from_bits c2)) <= / 4 -> Rabs (B2R (from_bits c3)) <= / 4 ->
  Rabs (y - (B2R t + B2R t ^ 3 * (B2R (from_bits c0) + B2R t ^ 2 * (B2R (from_bits c1) +
    B2R t ^ 2 * (B2R (from_bits c2) + B2R t ^ 2 * B2R (from_bits c3))))))
    <= E * B2R t ^ 3 ->
  0 <= E ->
  (1 + bpow radix2 (-14)) *
    (E + 4 * bpow radix2 (-53) * Rabs (B2R (from_bits c0)) + bpow radix2 (-60))
    <= bpow radix2 (-52) ->
  DyadicLog.odd_series t (c0, c1, c2, c3) = (h, l, k) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= k <= 1022)%Z /\
  Rabs (y * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-67).
Proof.
intros t c0 c1 c2 c3 h l k y E Ft Ht F0 F1 F2 F3 H0 H1 H2 H3 Hy HE0 HE H.
unfold DyadicLog.odd_series in H. cbv beta iota zeta in H.
set (x0 := from_bits c0) in *. set (x1 := from_bits c1) in *.
set (x2 := from_bits c2) in *. set (x3 := from_bits c3) in *.
set (u := mul t t) in *.
set (p := add x0 (mul u (add x1 (mul u (add x2 (mul u x3)))))) in *.
set (w := mul t u) in *. set (c := mul w p) in *.
destruct (Fast.fast_two_sum t c) as (s & l0) eqn:Ef.
set (T := B2R t) in *.
set (a := Rabs (B2R x0)) in *.
assert (HT : 0 < T) by (pose proof (bpow_gt_0 radix2 (-27)); lra).
(* [2^-54 <= t^2 <= 2^-16]. *)
assert (Hv : bpow radix2 (-54) <= T * T <= bpow radix2 (-16)).
{ replace (bpow radix2 (-54)) with (bpow radix2 (-27) * bpow radix2 (-27))
    by (rewrite <- bpow_plus; reflexivity).
  replace (bpow radix2 (-16)) with (bpow radix2 (-8) * bpow radix2 (-8))
    by (rewrite <- bpow_plus; reflexivity).
  pose proof (bpow_gt_0 radix2 (-27)) as B27.
  split; apply Rmult_le_compat; lra. }
(* [u = RN(t^2)] is within [2^-53 t^2] of [t^2]. *)
assert (Mu : Rabs (T * T) <= bpow radix2 (-16)) by (rewrite Rabs_pos_eq; nra).
destruct (mul_k t t _ Ft Ft Mu ltac:(num; lra)) as (Fu & Eu & _).
fold u in Fu, Eu.
assert (Ru : Rabs (B2R u - T * T) <= bpow radix2 (-53) * (T * T)).
{ rewrite Eu. rewrite <- (Rabs_pos_eq (T * T)) at 2 by nra.
  apply od_rel. rewrite Rabs_pos_eq by nra.
  eapply Rle_trans; [| exact (proj1 Hv)]. apply bpow_le. lia. }
assert (Bu : bpow radix2 (-55) <= B2R u <= bpow radix2 (-15)).
{ apply Rabs_le_inv in Ru. revert Ru Hv. num. lra. }
assert (Du : Rabs (B2R u - T * T) <= bpow radix2 (-69)).
{ eapply Rle_trans; [exact Ru |]. revert Hv. num. lra. }
(* Horner's scheme. *)
destruct (odd_horner u (T * T) x0 x1 x2 x3 Fu F0 F1 F2 F3
  ltac:(split; [pose proof (bpow_gt_0 radix2 (-55)); lra | lra])
  ltac:(revert Hv; num; lra) Du (proj2 H0) H1 H2 H3) as (Fp & Ep & Wq).
fold p in Fp, Ep.
set (Q := B2R x1 + T * T * (B2R x2 + T * T * B2R x3)) in *.
set (P := B2R x0 + T * T * Q) in *.
assert (AP : Rabs P <= a + bpow radix2 (-16)) by (apply od_sum; [apply Rle_refl | exact Wq]).
assert (Bp : bpow radix2 (-4) <= Rabs (B2R p) <= 1).
{ apply Rabs_le_inv in Wq. apply Rabs_le_inv in Ep.
  unfold P, a in *. revert H0 Wq Ep. num.
  unfold Rabs. destruct (Rcase_abs (B2R x0)), (Rcase_abs (B2R p)); lra. }
(* [w = RN(t u)] and [c = RN(w p)], both normal. *)
assert (TU : bpow radix2 (-82) <= T * B2R u <= bpow radix2 (-23)).
{ replace (bpow radix2 (-82)) with (bpow radix2 (-27) * bpow radix2 (-55))
    by (rewrite <- bpow_plus; reflexivity).
  replace (bpow radix2 (-23)) with (bpow radix2 (-8) * bpow radix2 (-15))
    by (rewrite <- bpow_plus; reflexivity).
  pose proof (bpow_gt_0 radix2 (-27)) as B27. pose proof (bpow_gt_0 radix2 (-55)) as B55.
  split; apply Rmult_le_compat; lra. }
pose proof (bpow_gt_0 radix2 (-82)) as B82.
assert (Mw : Rabs (T * B2R u) <= bpow radix2 (-23)) by (rewrite Rabs_pos_eq; lra).
destruct (mul_k t u _ Ft Fu Mw ltac:(num; lra)) as (Fw & Ew & _).
fold w in Fw, Ew.
assert (Rw : Rabs (B2R w - T * B2R u) <= bpow radix2 (-53) * Rabs (T * B2R u)).
{ rewrite Ew. apply od_rel. rewrite Rabs_pos_eq by lra.
  eapply Rle_trans; [| exact (proj1 TU)]. apply bpow_le. lia. }
assert (Bw : bpow radix2 (-83) <= Rabs (B2R w) <= bpow radix2 (-22)).
{ rewrite (Rabs_pos_eq (T * B2R u)) in Rw by lra. apply Rabs_le_inv in Rw.
  revert Rw TU. num. intros Rw TU. rewrite Rabs_pos_eq; lra. }
assert (Bwp : bpow radix2 (-87) <= Rabs (B2R w * B2R p) <= bpow radix2 (-22)).
{ rewrite Rabs_mult.
  replace (bpow radix2 (-87)) with (bpow radix2 (-83) * bpow radix2 (-4))
    by (rewrite <- bpow_plus; reflexivity).
  pose proof (bpow_gt_0 radix2 (-83)) as B83. pose proof (bpow_gt_0 radix2 (-4)) as B4.
  split; [apply Rmult_le_compat; lra |].
  rewrite <- (Rmult_1_r (bpow radix2 (-22))).
  apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | lra | lra]. }
destruct (mul_k w p _ Fw Fp (proj2 Bwp) ltac:(num; lra)) as (Fc & Ec & _).
fold c in Fc, Ec.
assert (Rc : Rabs (B2R c - B2R w * B2R p) <= bpow radix2 (-53) * Rabs (B2R w * B2R p)).
{ rewrite Ec. apply od_rel.
  eapply Rle_trans; [| exact (proj1 Bwp)]. apply bpow_le. lia. }
(* [c] is within [(4 * 2^-53 a + 2^-60) t^3] of [t^3 P(t^2)]. *)
pose proof (odd_prod T (T * T) (B2R u) (B2R w) (B2R c) (B2R p) P a ltac:(lra)
  ltac:(nra) Ru Rw Rc Ep AP ltac:(lra)) as Rp.
(* So [|c| <= t^3 <= 2^-16 t]: Fast2Sum is exact. *)
assert (T3 : 0 <= T * (T * T) <= bpow radix2 (-16) * T).
{ split; [apply Rmult_le_pos; nra |].
  rewrite Rmult_comm. apply Rmult_le_compat_r; lra. }
assert (Ac : Rabs (B2R c) <= bpow radix2 (-16) * T).
{ apply Rabs_le_inv in Rp. apply Rabs_le_inv in AP.
  assert (X : T * (T * T) * a <= T * (T * T) * / 2) by (apply Rmult_le_compat_l; lra).
  assert (X' : 0 <= T * (T * T) * a) by (apply Rmult_le_pos; [lra | apply Rabs_pos]).
  assert (Y1 : T * (T * T) * P <= T * (T * T) * (a + bpow radix2 (-16)))
    by (apply Rmult_le_compat_l; lra).
  assert (Y2 : - (T * (T * T) * (a + bpow radix2 (-16))) <= T * (T * T) * P).
  { rewrite Ropp_mult_distr_r. apply Rmult_le_compat_l; lra. }
  revert Rp X X' Y1 Y2 T3. num. intros. apply Rabs_le. nra. }
unfold Fast.fast_two_sum in Ef. injection Ef as Es El. subst s l0.
assert (Mts : Rabs (T + B2R c) <= 16).
{ apply Rabs_le_inv in Ac. rewrite Rabs_pos_eq; revert Ac Ht; num; lra. }
destruct (add_e t c Ft Fc Mts) as (Fs & Es & _).
destruct (fast_two_sum t c (add t c) Ft Fc
  ltac:(fold T; rewrite (Rabs_pos_eq T) by lra; eapply Rle_trans; [exact Ac | num; lra])
  Fs Es) as (Fl & El).
set (s := add t c) in *. set (l0 := add c (sub t s)) in *.
(* [t (1 - 2^-15) <= s <= 2^-7]. *)
assert (Bs : T * (1 - bpow radix2 (-15)) <= B2R s <= bpow radix2 (-7)).
{ assert (Pts : bpow radix2 (-1022) <= Rabs (T + B2R c)).
  { apply Rabs_le_inv in Ac. rewrite Rabs_pos_eq; revert Ac Ht; num; lra. }
  pose proof (od_rel _ Pts) as R. fold T in Es. rewrite <- Es in R.
  apply Rabs_le_inv in Ac. rewrite (Rabs_pos_eq (T + B2R c)) in R by (revert Ac Ht; num; lra).
  apply Rabs_le_inv in R. revert R Ac Ht. num. lra. }
assert (Rs : B2R s = RN (B2R s + B2R l0))
  by (rewrite El; replace (B2R s + (B2R t + B2R c - B2R s)) with (B2R t + B2R c) by ring; exact Es).
assert (Hs : bpow radix2 (-1021) <= B2R s < 2) by (revert Bs Ht; num; lra).
pose proof (normalize_correct s l0 Fs Fl Rs Hs) as N.
rewrite H in N. cbv beta iota in N.
destruct N as (Fh & Fl' & Hk & Eh & El' & Bk & Rh).
do 3 (split; [assumption|]). split; [lia |].
(* [2^-k t <= 2 (1 + 2^-14)]. *)
set (B := bpow radix2 (- k)).
assert (PB : 0 < B) by apply bpow_gt_0.
assert (EB : B * bpow radix2 (k + 1) = 2)
  by (unfold B; rewrite <- bpow_plus; replace (- k + (k + 1))%Z with 1%Z by ring; reflexivity).
assert (BT : B * T <= 2 * (1 + bpow radix2 (-14))).
{ assert (L : B * (T * (1 - bpow radix2 (-15))) < B * bpow radix2 (k + 1))
    by (apply Rmult_lt_compat_l; lra).
  revert L EB. num. intros. lra. }
(* So the error is at most [2 (1 + 2^-14) 2^-16 (E + 4 * 2^-53 a + 2^-60)]. *)
assert (Ey : Rabs (y - (T + B2R c)) <= T * (T * T) *
  (E + 4 * bpow radix2 (-53) * a + bpow radix2 (-60))).
{ apply Rabs_le_inv in Hy, Rp. apply Rabs_le. unfold P, Q in Rp. lra. }
replace (y * B - (B2R h + B2R l)) with ((y - (T + B2R c)) * B)
  by (rewrite Eh, El', El; fold B; unfold T; ring).
rewrite Rabs_mult, (Rabs_pos_eq B) by lra.
set (M := E + 4 * bpow radix2 (-53) * a + bpow radix2 (-60)) in *.
assert (PM : 0 <= M).
{ unfold M. num. lra. }
apply Rle_trans with (T * (T * T) * M * B).
{ apply Rmult_le_compat_r; lra. }
replace (T * (T * T) * M * B) with ((B * T) * (T * T * M)) by ring.
apply Rle_trans with (2 * (1 + bpow radix2 (-14)) * (bpow radix2 (-16) * M)).
{ apply Rmult_le_compat; [nra | apply Rmult_le_pos; nra | exact BT |].
  apply Rmult_le_compat_r; lra. }
revert HE. fold a. fold M. num. lra.
Qed.

(** ** The two series *)

(** [t^(n+2) <= 2^-16 t^n] for [0 <= t <= 2^-8]. *)
Local Lemma pow_step :
  forall t n, 0 <= t <= bpow radix2 (-8) -> 0 <= t ^ (n + 2) <= bpow radix2 (-16) * t ^ n.
Proof.
intros t n Ht.
assert (Pn : 0 <= t ^ n) by (apply pow_le; lra).
assert (T2 : t ^ 2 <= bpow radix2 (-16)).
{ replace (bpow radix2 (-16)) with (bpow radix2 (-8) * bpow radix2 (-8))
    by (rewrite <- bpow_plus; reflexivity).
  cbn [pow]. rewrite Rmult_1_r. apply Rmult_le_compat; lra. }
rewrite pow_add. split; [apply Rmult_le_pos; [exact Pn | apply pow2_ge_0] |].
rewrite Rmult_comm. apply Rmult_le_compat_r; [exact Pn | exact T2].
Qed.

(** The magnitude bounds of [odd_series_err] for a coefficient in the
    goal. *)
Local Ltac coef_abs c :=
  lit_R (from_bits c); num; unfold Rabs; destruct (Rcase_abs _); lra.

Theorem asinh_odd_correct :
  forall t h l k,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < bpow radix2 (-8) ->
  DyadicLog.odd_series t DyadicLog.ASINH_ODD = (h, l, k) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= k <= 1022)%Z /\
  Rabs (arcsinh (B2R t) * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-67).
Proof.
intros t h l k Ft Ht H.
set (T := B2R t) in *.
assert (HT : 0 <= T <= bpow radix2 (-8)) by (pose proof (bpow_gt_0 radix2 (-27)); lra).
destruct (pow_step T 3 HT) as (P5a & P5). destruct (pow_step T 5 HT) as (P7a & P7).
destruct (pow_step T 7 HT) as (P9a & P9). destruct (pow_step T 9 HT) as (P11a & P11).
assert (P3 : 0 <= T ^ 3) by (apply pow_le; lra).
cbn [Nat.add] in P5a, P5, P7a, P7, P9a, P9, P11a, P11.
(* The Taylor bound: [|asinh t - (t - t^3/6 + ... + 35 t^9/1152)| <= t^11/40]. *)
pose proof (asinh_taylor9 T ltac:(revert HT; num; lra)) as Tay.
apply (odd_series_err t DyadicLog.Q6 DyadicLog.A5 DyadicLog.A7 DyadicLog.A9 h l k
  (arcsinh T) (bpow radix2 (-55) / 3 + bpow radix2 (-68)) Ft Ht);
  [vm_compute; reflexivity .. | | | | | | | | exact H].
- split; coef_abs DyadicLog.Q6.
- coef_abs DyadicLog.A5.
- coef_abs DyadicLog.A7.
- coef_abs DyadicLog.A9.
- fold T. lit_R (from_bits DyadicLog.Q6). lit_R (from_bits DyadicLog.A5).
  lit_R (from_bits DyadicLog.A7). lit_R (from_bits DyadicLog.A9).
  apply Rabs_le_inv in Tay. apply Rabs_le. revert Tay P3 P5 P7 P9 P11 P5a P7a P9a P11a.
  num. intros. lra.
- num. lra.
- lit_R (from_bits DyadicLog.Q6). num. unfold Rabs. destruct (Rcase_abs _); lra.
Qed.

Theorem atanh_odd_correct :
  forall t h l k,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < bpow radix2 (-8) ->
  DyadicLog.odd_series t DyadicLog.ATANH_ODD = (h, l, k) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= k <= 1022)%Z /\
  Rabs (Ratanh (B2R t) * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-67).
Proof.
intros t h l k Ft Ht H.
set (T := B2R t) in *.
assert (HT : 0 <= T <= bpow radix2 (-8)) by (pose proof (bpow_gt_0 radix2 (-27)); lra).
destruct (pow_step T 1 HT) as (P3a & P3). destruct (pow_step T 3 HT) as (P5a & P5).
destruct (pow_step T 5 HT) as (P7a & P7). destruct (pow_step T 7 HT) as (P9a & P9).
destruct (pow_step T 9 HT) as (P11a & P11).
cbn [Nat.add] in P3a, P3, P5a, P5, P7a, P7, P9a, P9, P11a, P11.
(* The series: [0 <= atanh t - (t + t^3/3 + ... + t^9/9) <= t^11 / (1 - t^2)],
   and [t^11 / (1 - t^2) <= 2 t^11]. *)
pose proof (atanh_sum_bounds 5 T ltac:(revert HT; num; lra)) as Ser.
replace (atanh_sum 5 T) with (T + T ^ 3 / 3 + T ^ 5 / 5 + T ^ 7 / 7 + T ^ 9 / 9) in Ser
  by (cbn [atanh_sum Nat.mul Nat.add]; simpl INR; field).
replace (2 * 5 + 1)%nat with 11%nat in Ser by reflexivity.
assert (D : T ^ 11 / (1 - T ^ 2) <= 2 * T ^ 11).
{ assert (T2 : T ^ 2 <= / 2) by (replace (T ^ 2) with (T ^ (0 + 2)) by reflexivity;
    revert P3; cbn [pow Nat.add]; num; nra).
  unfold Rdiv. rewrite Rmult_comm. apply Rmult_le_compat_r; [lra |].
  replace 2 with (/ / 2) by (rewrite Rinv_inv; reflexivity).
  apply Rinv_le_contravar; lra. }
apply (odd_series_err t DyadicLog.Q3 DyadicLog.Q5 DyadicLog.Q7 DyadicLog.Q9 h l k
  (Ratanh T) (bpow radix2 (-54) / 3 + bpow radix2 (-62)) Ft Ht);
  [vm_compute; reflexivity .. | | | | | | | | exact H].
- split; coef_abs DyadicLog.Q3.
- coef_abs DyadicLog.Q5.
- coef_abs DyadicLog.Q7.
- coef_abs DyadicLog.Q9.
- fold T. lit_R (from_bits DyadicLog.Q3). lit_R (from_bits DyadicLog.Q5).
  lit_R (from_bits DyadicLog.Q7). lit_R (from_bits DyadicLog.Q9).
  apply Rabs_le. revert Ser D P3a P3 P5 P7 P9 P11 P5a P7a P9a P11a.
  num. intros. lra.
- num. lra.
- lit_R (from_bits DyadicLog.Q3). num. unfold Rabs. destruct (Rcase_abs _); lra.
Qed.
