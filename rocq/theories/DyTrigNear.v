(** * The trigonometric functions of the dyadic kernel rounded to nearest

    [sin_near_with ziv_near_strict] and the others of [DyadicTrig] return,
    where they return, their function at a finite [x] rounded to nearest
    as [near_round] says: the loop by [ziv_near_strict_correct] and the
    enclosures of [DyTrig.v], and the rules before it by the cells of
    [NearCells.v] and the bounds of [DyTrigTiny.v]. Where they return
    with [ziv_near_strict], they return the same with [Dyadic.ziv_near]
    ([sin_near_strict] and the others). *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary LogReal DyRound DyConv DyOps DyDriver DyGrow
  DyConst DyExpCore DyExpRules DyExp ExpReal DyHypRules DyLogRules DyLogCore DyLog DyLogHyp
  TrigSeries DyTrigTiny DyCosSmall DySinSmall DyTanSmall DyTrigReduce DyTrigCore DyTrig MpfrRound
  NearF64 NearCells DyDriverNear.

Open Scope Z_scope.

(** ** Helpers *)

(** [tiny_near] is [2^-27]: [B2SF] of the literal computes to its sign,
    significand and exponent, as [asin_lit_tiny] of [DyAtanTiny.v] has it. *)
Local Lemma tn_lit_tiny : B2R DyadicExp.tiny_near = bpow radix2 (-27).
Proof.
rewrite <- (SF2R_B2SF _ _ DyadicExp.tiny_near).
let s := eval vm_compute in (B2SF DyadicExp.tiny_near) in
replace (B2SF DyadicExp.tiny_near) with s by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]; unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
reflexivity.
Qed.

(** [lt (fabs x) tiny_near] is [|x| < 2^-27]. *)
Local Lemma tn_tiny :
  forall x, is_finite x = true -> lt (fabs x) DyadicExp.tiny_near = true ->
  (Rabs (B2R x) < bpow radix2 (-27))%R.
Proof.
intros x Fx G. rewrite <- tn_lit_tiny.
apply fabs_lt_R; [exact Fx | vm_compute; reflexivity | exact G].
Qed.

(** For [0 < w < 2^-27], [w^3 < w 2^-54], as [w^2 < 2^-54]. *)
Local Lemma tn_cube :
  forall w, (0 < w < bpow radix2 (-27))%R -> (w ^ 3 < w * bpow radix2 (-54))%R.
Proof.
intros w Hw.
assert (E : bpow radix2 (-54) = (bpow radix2 (-27) * bpow radix2 (-27))%R)
  by (rewrite <- bpow_plus; reflexivity).
assert (Hww : (w * w < bpow radix2 (-54))%R) by (rewrite E; apply Rmult_le_0_lt_compat; lra).
replace (w ^ 3)%R with (w * (w * w))%R by ring.
apply Rmult_lt_compat_l; lra.
Qed.

(** An odd [f] within [w 2^-54] of [w] for [0 < w < 2^-27] rounds to
    nearest to [x] at a finite [x] with [|x| < 2^-27]: by [near_exact] at
    [x = 0], where [f 0 = 0], and otherwise by [near_x], as
    [f x - x = - (f (-x) - (-x))]. *)
Local Lemma tn_odd :
  forall (f : R -> R) x,
  (forall w, f (- w) = - f w)%R ->
  (forall w, 0 < w < bpow radix2 (-27) -> Rabs (f w - w) <= w * bpow radix2 (-54))%R ->
  is_finite x = true -> (Rabs (B2R x) < bpow radix2 (-27))%R ->
  near_round (f (B2R x)) x.
Proof.
intros f x Fo Fb Fx Hx.
destruct (Req_dec (B2R x) 0) as [X0|X0].
- assert (F0 : f 0%R = 0%R) by (pose proof (Fo 0%R) as E; rewrite Ropp_0 in E; lra).
  rewrite X0, F0, <- X0. exact (near_exact x Fx).
- apply (near_x x _ Fx X0).
  destruct (Rlt_or_le 0 (B2R x)) as [P|N].
  + rewrite (Rabs_pos_eq (B2R x)) in Hx |- * by lra. apply Fb. lra.
  + assert (N' : (B2R x < 0)%R)
      by (destruct (Rle_lt_or_eq_dec _ _ N); [assumption | contradiction]).
    rewrite (Rabs_left1 (B2R x)) in Hx |- * by lra.
    replace (f (B2R x) - B2R x)%R with (- (f (- B2R x) - - B2R x))%R by (rewrite Fo; ring).
    rewrite Rabs_Ropp. apply Fb. lra.
Qed.

(** For [0 < w < 2^-27], [w - w^3/6 <= sin w <= w - w^3/6 + w^5/120]
    ([sin_bounds_3]), where [w^5/120 < w^3/6] and [w^3 < w 2^-54]. *)
Local Lemma tn_sin :
  forall w, (0 < w < bpow radix2 (-27))%R -> (Rabs (sin w - w) <= w * bpow radix2 (-54))%R.
Proof.
intros w Hw.
pose proof (tn_cube w Hw) as H3.
assert (B : (bpow radix2 (-27) < bpow radix2 (-26))%R) by (apply bpow_lt; lia).
destruct (tiny_range w ltac:(lra)) as (R0 & RP & _ & _ & Hww).
destruct (sin_bounds_3 w R0 RP) as [S1 S2].
assert (P3 : (0 < w ^ 3)%R) by (apply pow_lt; lra).
assert (H5 : (w ^ 3 * (w * w) < w ^ 3 * 1)%R) by (apply Rmult_lt_compat_l; lra).
replace (w ^ 3 * (w * w))%R with (w ^ 5)%R in H5 by ring.
apply Rabs_le. lra.
Qed.

(** For [0 <= t < 2^-27], [1 - 2^-54 < 1 - t^2/2 <= cos t <= 1]
    ([cos_bounds_3], [COS_bound]), as [t^2 < 2^-54]. *)
Local Lemma tn_cos :
  forall t, (0 <= t < bpow radix2 (-27))%R ->
  (1 - bpow radix2 (-54) <= cos t <= 1 + bpow radix2 (-53))%R.
Proof.
intros t Ht.
pose proof (COS_bound t) as [_ C1].
pose proof (bpow_gt_0 radix2 (-53)) as P53.
pose proof (bpow_gt_0 radix2 (-54)) as P54.
split; [|lra].
destruct (Rle_lt_or_eq_dec 0 t (proj1 Ht)) as [Tp|T0].
2: { rewrite <- T0, cos_0. lra. }
assert (B : (bpow radix2 (-27) < bpow radix2 (-26))%R) by (apply bpow_lt; lia).
destruct (tiny_range t ltac:(lra)) as (_ & _ & R1 & R2 & _).
destruct (cos_bounds_3 t R1 R2) as [C2 _].
assert (E : bpow radix2 (-54) = (bpow radix2 (-27) * bpow radix2 (-27))%R)
  by (rewrite <- bpow_plus; reflexivity).
assert (Htt : (t * t < bpow radix2 (-54))%R) by (rewrite E; apply Rmult_le_0_lt_compat; lra).
replace (t ^ 2)%R with (t * t)%R in C2 by ring.
lra.
Qed.

(** [cos] is even. *)
Local Lemma tn_cos_abs : forall r, cos r = cos (Rabs r).
Proof. intros r. unfold Rabs. destruct (Rcase_abs r); [rewrite cos_neg|]; reflexivity. Qed.

(** For [0 < w < 2^-27], [w < tan w <= w + w^3/2] ([tan_tiny_real]), and
    [w^3 < w 2^-54]. *)
Local Lemma tn_tan :
  forall w, (0 < w < bpow radix2 (-27))%R -> (Rabs (tan w - w) <= w * bpow radix2 (-54))%R.
Proof.
intros w Hw.
pose proof (tn_cube w Hw) as H3.
assert (B : (bpow radix2 (-27) < bpow radix2 (-26))%R) by (apply bpow_lt; lia).
destruct (tan_tiny_real w ltac:(lra)) as [T1 T2].
assert (P3 : (0 < w ^ 3)%R) by (apply pow_lt; lra).
apply Rabs_le. lra.
Qed.

(** Where [ziv_near_strict] returns, [Dyadic.ziv_near] returns the same:
    the goal [<body with ziv_near_strict> = Some v -> <body with
    Dyadic.ziv_near> = Some v] of a function of this file, split at its
    guards, which name neither driver, as [dir_strict] of [DyExp.v]. *)
Local Ltac near_strict :=
  repeat match goal with
  | |- (if ?c then _ else _) = Some _ -> _ => destruct c; [exact (fun h => h)|]
  end;
  apply ziv_near_strict_ziv.

(** ** The functions *)


Theorem sin_near_correct :
  forall x v,
  is_finite x = true -> DyadicTrig.sin_near_with ziv_near_strict x = Some v ->
  near_round (sin (B2R x)) v.
Proof.
intros x v Fx H. unfold DyadicTrig.sin_near_with in H.
rewrite Fx in H. cbv [negb] in H.
destruct (lt (fabs x) DyadicExp.tiny_near) eqn:G; cbv iota in H.
{ injection H as <-. exact (tn_odd sin x sin_neg tn_sin Fx (tn_tiny x Fx G)). }
apply (ziv_near_strict_correct (DyadicTrig.ev_sin x) 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_sin_correct x n a Hn Fx Ha).
Qed.

Theorem cos_near_correct :
  forall x v,
  is_finite x = true -> DyadicTrig.cos_near_with ziv_near_strict x = Some v ->
  near_round (cos (B2R x)) v.
Proof.
intros x v Fx H. unfold DyadicTrig.cos_near_with in H. cbv zeta in H.
rewrite (trg_fabs_finite x Fx) in H. cbv [negb] in H.
destruct (lt (fabs x) DyadicExp.tiny_near) eqn:G; cbv iota in H.
{ (* [cos x = cos |x|] with [|x| < 2^-27] is within [2^-54] of 1. *)
  injection H as <-. rewrite tn_cos_abs. apply near_one, tn_cos.
  split; [apply Rabs_pos | exact (tn_tiny x Fx G)]. }
apply (ziv_near_strict_correct (DyadicTrig.ev_cos (fabs x)) 1%nat); [|exact H].
intros n a Hn Ha.
destruct (ev_cos_correct (fabs x) n a Hn (trg_fabs_finite x Fx) (trg_fabs_pos x) Ha)
  as (Oa & Ha').
split; [exact Oa|].
rewrite trg_fabs_R, <- tn_cos_abs in Ha'. exact Ha'.
Qed.

Theorem tan_near_correct :
  forall x v,
  is_finite x = true -> DyadicTrig.tan_near_with ziv_near_strict x = Some v ->
  near_round (tan (B2R x)) v.
Proof.
intros x v Fx H. unfold DyadicTrig.tan_near_with in H.
rewrite Fx in H. cbv [negb] in H.
destruct (lt (fabs x) DyadicExp.tiny_near) eqn:G; cbv iota in H.
{ injection H as <-. exact (tn_odd tan x tan_neg tn_tan Fx (tn_tiny x Fx G)). }
apply (ziv_near_strict_correct (DyadicTrig.ev_tan x) 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_tan_correct x n a Hn Fx Ha).
Qed.

Theorem sin_near_strict :
  forall x v, DyadicTrig.sin_near_with ziv_near_strict x = Some v -> DyadicTrig.sin_near x = Some v.
Proof. intros x v. unfold DyadicTrig.sin_near, DyadicTrig.sin_near_with. near_strict. Qed.

Theorem cos_near_strict :
  forall x v, DyadicTrig.cos_near_with ziv_near_strict x = Some v -> DyadicTrig.cos_near x = Some v.
Proof. intros x v. unfold DyadicTrig.cos_near, DyadicTrig.cos_near_with. cbv zeta. near_strict. Qed.

Theorem tan_near_strict :
  forall x v, DyadicTrig.tan_near_with ziv_near_strict x = Some v -> DyadicTrig.tan_near x = Some v.
Proof. intros x v. unfold DyadicTrig.tan_near, DyadicTrig.tan_near_with. near_strict. Qed.
