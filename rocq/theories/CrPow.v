(** * The signs of [pow] in [src/cr.rs]

    [Cr.pow_dir_with] and [Cr.pow_near_signed_with] return, at a finite
    [x < 0] and a finite integer [y = k], [x^k] rounded as the kernel's
    function it calls ([cr_pow_dir_neg], [cr_pow_near_neg]), and the
    kernel's [pow] elsewhere in its domain ([cr_pow_dir_dom],
    [cr_pow_near_dom]), by the theorems of [DyPow.v], [DyPown.v] and
    [DyPowNear.v]. Where they return with [ziv_strict] and
    [ziv_near_strict], they return the same with [Dyadic.ziv] and
    [Dyadic.ziv_near] ([cr_pow_dir_strict], [cr_pow_near_strict]). *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr MpfrRound Limbs Elementary DyRound DyConv DyOps DyDriver
  DyGrow DyConst DyExpCore DyExpRules DyExp DyLogRules DyLogCore DyPowArith DyPowRules
  DyPowExact DyPowCore NearF64 NearCells DyDriverNear DyPowNear.
From Inari Require DyPown DyPow Integer.

Open Scope Z_scope.

(** ** The branches of [Cr.pow_dir_with] *)

(** [2^e] is even for [e > 0]. *)
Local Lemma pow2_even : forall e, 0 < e -> Z.odd (Zpower radix2 e) = false.
Proof.
intros e He. replace e with (e - 1 + 1) by ring.
rewrite (Zpower_plus radix2) by lia. rewrite Z.odd_mul.
change (Z.odd (Zpower radix2 1)) with false. apply Bool.andb_false_r.
Qed.

(** At a finite [y = k], [is_odd_integer y] is whether [k] is odd: [k = 0]
    is [eq y zero], and otherwise [|k| = m 2^e] with an odd [m]
    ([odd_parts_spec]), so [k] is odd at [e = 0], even at [e > 0], and
    [e < 0] would make [m = |k| 2^-e] even. *)
Lemma is_odd_integer_IZR :
  forall (y : f64) k, is_finite y = true -> B2R y = IZR k -> DyadicPow.is_odd_integer y = Z.odd k.
Proof.
intros y k Fy Hy. unfold DyadicPow.is_odd_integer.
assert (Fz : is_finite zero = true) by reflexivity.
assert (Rz : B2R zero = 0%R) by reflexivity.
destruct (Z.eq_dec k 0) as [K0 | K0].
- subst k. rewrite (proj2 (DyPow.eq_fin y zero Fy Fz)) by (rewrite Hy, Rz; reflexivity).
  reflexivity.
- assert (Ny : B2R y <> 0%R) by (rewrite Hy; intros H; apply K0, eq_IZR_R0, H).
  rewrite (DyPow.eq_false_of y zero Fy Fz) by (rewrite Rz; exact Ny). cbn [negb andb].
  destruct (DyadicPow.odd_parts y) as [m e] eqn:O. cbn [snd].
  destruct (odd_parts_spec y m e Fy Ny O) as (Om & _ & _ & Ha).
  rewrite Hy, <- abs_IZR in Ha.
  assert (Ok : Z.odd k = Z.odd (Z.abs k)).
  { destruct (Z_le_gt_dec 0 k);
      [rewrite Z.abs_eq by lia | rewrite Z.abs_neq, Z.odd_opp by lia]; reflexivity. }
  rewrite Ok. destruct (Z.compare_spec e 0) as [E0 | Elt | Egt].
  + subst e. change (bpow radix2 0) with 1%R in Ha. rewrite Rmult_1_r in Ha.
    apply eq_IZR in Ha. rewrite Ha. symmetry. exact Om.
  + exfalso.
    assert (Hm : IZR m = IZR (Z.abs k * Zpower radix2 (- e))).
    { rewrite mult_IZR, (IZR_Zpower radix2) by lia.
      rewrite Ha, Rmult_assoc, <- bpow_plus, Z.add_opp_diag_r.
      change (bpow radix2 0) with 1%R. ring. }
    apply eq_IZR in Hm. rewrite Hm, Z.odd_mul, pow2_even, Bool.andb_false_r in Om by lia.
    discriminate Om.
  + rewrite (proj2 (Z.eqb_neq e 0)) by lia.
    rewrite <- (IZR_Zpower radix2), <- mult_IZR in Ha by lia. apply eq_IZR in Ha.
    rewrite Ha, Z.odd_mul, pow2_even, Bool.andb_false_r by lia. reflexivity.
Qed.

(** A finite integer [y] is its own floor. *)
Local Lemma ffloor_int :
  forall (y : f64) k, is_finite y = true -> B2R y = IZR k -> eq y (ffloor y) = true.
Proof.
intros y k Fy Hy.
assert (Ff : is_finite (ffloor y) = true) by (rewrite Integer.ffloor_finite; exact Fy).
apply (proj2 (DyPow.eq_fin y (ffloor y) Fy Ff)).
rewrite Integer.ffloor_B2R, Hy, Integer.Rfloor_IZR. reflexivity.
Qed.

(** The guard of the negative branch holds at a finite [x < 0] and a
    finite [y]. *)
Local Lemma neg_guard :
  forall x y : f64, is_finite x = true -> (B2R x < 0)%R -> is_finite y = true ->
  lt x zero && negb (is_nan y) = true.
Proof.
intros x y Fx Hx Fy. rewrite (proj2 (DyPow.lt_fin x zero Fx eq_refl)) by exact Hx.
destruct y; try discriminate Fy; reflexivity.
Qed.

(** The guard of the negative branch fails in [pow_dom], where [x >= 0]. *)
Local Lemma dom_guard :
  forall x y : f64, is_finite x = true -> pow_dom (B2R x) (B2R y) ->
  lt x zero && negb (is_nan y) = false.
Proof.
intros x y Fx Hd. assert (Rz : B2R zero = 0%R) by reflexivity.
rewrite (DyPow.lt_false_of x zero Fx eq_refl) by (rewrite Rz; destruct Hd as [H | [H _]]; lra).
reflexivity.
Qed.

(** For [r < 0], [(-r)^k] is [Rpow (-r) k] ([powerRZ_Rpower]), which is
    [-r^k] at an odd [k] and [r^k] at an even one. *)
Local Lemma Rpow_opp_int :
  forall r k, (r < 0)%R ->
  Rpow (- r) (IZR k) = (if Z.odd k then - powerRZ r k else powerRZ r k)%R.
Proof.
intros r k Hr. unfold Rpow. destruct (Rle_dec (- r) 0) as [H | _]; [lra |].
rewrite <- powerRZ_Rpower by lra. apply DyPown.pown_powerRZ_opp.
Qed.

(** [opp x] is finite, of value [-x], and in [pow_dom] at a finite
    [x < 0]. *)
Local Lemma opp_neg :
  forall x y : f64, is_finite x = true -> (B2R x < 0)%R ->
  is_finite (opp x) = true /\ B2R (opp x) = (- B2R x)%R /\ pow_dom (B2R (opp x)) (B2R y).
Proof.
intros x y Fx Hx. unfold opp. rewrite is_finite_Bopp, B2R_Bopp.
split; [exact Fx |]. split; [reflexivity |]. left. lra.
Qed.

(** ** The theorems *)

Theorem cr_pow_dir_neg :
  forall x y k (up : bool) v,
  is_finite x = true -> (B2R x < 0)%R -> is_finite y = true -> B2R y = IZR k ->
  Cr.pow_dir_with ziv_strict x y up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (powerRZ (B2R x) k) (with_val v).
Proof.
intros x y k up v Fx Hx Fy Hy E. unfold Cr.pow_dir_with in E.
rewrite (neg_guard x y Fx Hx Fy), (is_odd_integer_IZR y k Fy Hy) in E.
destruct (opp_neg x y Fx Hx) as (Fo & Ro & Do).
pose proof (Rpow_opp_int (B2R x) k Hx) as Rk. rewrite <- Ro, <- Hy in Rk.
destruct (Z.odd k).
- (* [x^k = -(-x)^k], rounded in the other direction and negated. *)
  destruct (DyadicPow.pow_dir_with ziv_strict (opp x) y (negb up)) as [w|] eqn:P;
    [| discriminate E].
  injection E as Ev. subst v. apply DyPown.pown_rnd_opp.
  pose proof (DyPow.pow_dir_correct _ _ _ _ Fo Fy Do P) as H. rewrite Rk in H. exact H.
- (* [x^k = (-x)^k], and [y] is its own floor. *)
  rewrite (ffloor_int y k Fy Hy) in E. cbn [orb] in E.
  pose proof (DyPow.pow_dir_correct _ _ _ _ Fo Fy Do E) as H. rewrite Rk in H. exact H.
Qed.

Theorem cr_pow_dir_dom :
  forall x y (up : bool) v,
  is_finite x = true -> is_finite y = true -> pow_dom (B2R x) (B2R y) ->
  Cr.pow_dir_with ziv_strict x y up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (Rpow (B2R x) (B2R y)) (with_val v).
Proof.
intros x y up v Fx Fy Hd E. unfold Cr.pow_dir_with in E.
rewrite (dom_guard x y Fx Hd) in E.
exact (DyPow.pow_dir_correct x y up v Fx Fy Hd E).
Qed.

Theorem cr_pow_near_neg :
  forall x y k v,
  is_finite x = true -> (B2R x < 0)%R -> is_finite y = true -> B2R y = IZR k ->
  Cr.pow_near_signed_with ziv_near_strict x y = Some v ->
  near_round (powerRZ (B2R x) k) v.
Proof.
intros x y k v Fx Hx Fy Hy E. unfold Cr.pow_near_signed_with in E.
rewrite (neg_guard x y Fx Hx Fy), (is_odd_integer_IZR y k Fy Hy) in E.
destruct (opp_neg x y Fx Hx) as (Fo & Ro & Do).
pose proof (Rpow_opp_int (B2R x) k Hx) as Rk. rewrite <- Ro, <- Hy in Rk.
destruct (Z.odd k).
- (* [x^k = -(-x)^k], and rounding to nearest commutes with negation. *)
  destruct (DyadicPow.pow_near_with ziv_near_strict (opp x) y) as [w|] eqn:P;
    [| discriminate E].
  injection E as Ev. subst v.
  pose proof (pow_near_correct _ _ _ Fo Fy Do P) as H. rewrite Rk in H.
  pose proof (near_opp _ _ H) as H'. rewrite Ropp_involutive in H'. exact H'.
- (* [x^k = (-x)^k], and [y] is its own floor. *)
  rewrite (ffloor_int y k Fy Hy) in E. cbn [orb] in E.
  pose proof (pow_near_correct _ _ _ Fo Fy Do E) as H. rewrite Rk in H. exact H.
Qed.

Theorem cr_pow_near_dom :
  forall x y v,
  is_finite x = true -> is_finite y = true -> pow_dom (B2R x) (B2R y) ->
  Cr.pow_near_signed_with ziv_near_strict x y = Some v ->
  near_round (Rpow (B2R x) (B2R y)) v.
Proof.
intros x y v Fx Fy Hd E. unfold Cr.pow_near_signed_with in E.
rewrite (dom_guard x y Fx Hd) in E.
exact (pow_near_correct x y v Fx Fy Hd E).
Qed.

Theorem cr_pow_dir_strict :
  forall x y up v, Cr.pow_dir_with ziv_strict x y up = Some v -> Cr.pow_dir x y up = Some v.
Proof.
intros x y up v. unfold Cr.pow_dir, Cr.pow_dir_with.
destruct (lt x zero && negb (is_nan y)); [| apply DyPow.pow_dir_strict].
destruct (DyadicPow.is_odd_integer y).
- destruct (DyadicPow.pow_dir_with ziv_strict (opp x) y (negb up)) as [w|] eqn:P;
    [| intros H; discriminate H].
  pose proof (DyPow.pow_dir_strict _ _ _ _ P) as Q. unfold DyadicPow.pow_dir in Q.
  rewrite Q. exact (fun h => h).
- destruct (eq y (ffloor y) || eq x DyadicExp.neg_infinity);
    [apply DyPow.pow_dir_strict | exact (fun h => h)].
Qed.

Theorem cr_pow_near_strict :
  forall x y v,
  Cr.pow_near_signed_with ziv_near_strict x y = Some v -> Cr.pow_near_signed x y = Some v.
Proof.
intros x y v. unfold Cr.pow_near_signed, Cr.pow_near_signed_with.
destruct (lt x zero && negb (is_nan y)); [| apply pow_near_strict].
destruct (DyadicPow.is_odd_integer y).
- destruct (DyadicPow.pow_near_with ziv_near_strict (opp x) y) as [w|] eqn:P;
    [| intros H; discriminate H].
  pose proof (pow_near_strict _ _ _ P) as Q. unfold DyadicPow.pow_near in Q.
  rewrite Q. exact (fun h => h).
- destruct (eq y (ffloor y) || eq x DyadicExp.neg_infinity);
    [apply pow_near_strict | exact (fun h => h)].
Qed.
