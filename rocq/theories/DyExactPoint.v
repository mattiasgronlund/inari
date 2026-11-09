(** * Point enclosures through the operations of the kernel

    [encl_pt n a r] says that [a] is a valid enclosure at level [n] both
    of whose bounds are [r]. The operations of [Dyadic] map points to
    points wherever the exact result is in the format of the level, as
    they round each bound of the exact result outward ([encl_add_correct]
    and the others of [DyDriver.v]) and rounding is the identity on that
    format ([dround_id]). The point 0 times a valid [encl_small]
    enclosure, or divided by one that excludes 0, is the point 0, as the
    divisions of the kernel need a divisor that excludes 0. A bound of
    value 0 has exponent 0
    ([dy_cases]), and the exponent of a nonzero bound is fixed by its
    magnitude ([grow_exp_win]), so that enclosures of moderate magnitudes
    are [encl_small], as the operations need of their operands. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs DyRound DyConv DyOps DyDriver DyGrow.

Open Scope R_scope.

(** The format of the bounds at level [n]. *)
Local Notation fmt n := (generic_format radix2 (FLX_exp (dprec n))).

(** [a] encloses [r] by the point [r] at level [n]. *)
Definition encl_pt (n : nat) (a : Dyadic.encl) (r : R) : Prop :=
  encl_ok n a /\ lo_R a = r /\ hi_R a = r.

Local Lemma pt_min_id : forall x, Rmin x x = x.
Proof. intros x. apply Rmin_left, Rle_refl. Qed.

Local Lemma pt_max_id : forall x, Rmax x x = x.
Proof. intros x. apply Rmax_left, Rle_refl. Qed.

(** ** Exponents from values *)

(** A valid bound of value 0 has exponent 0. *)
Lemma pt_exp0 :
  forall n d, level_ok n -> dy_ok n d -> Dyadic.dy_R d = 0 -> Dyadic.dy_exp d = 0%Z.
Proof.
intros n d Hn Hd H.
destruct (dy_cases n d Hn Hd) as [(_ & _ & _ & E & _) | (_ & _ & B & _)]; [exact E |].
rewrite H, Rabs_R0 in B. pose proof (bpow_gt_0 radix2 (Dyadic.dy_exp d + dprec n - 1)). lra.
Qed.

(** Bounds that are 0 or of magnitudes from [2^-4096] to [2^4096] are
    small. *)
Lemma pt_small_win :
  forall n a,
  level_ok n -> encl_ok n a ->
  grow_win (-4096) 4096 (lo_R a) -> grow_win (-4096) 4096 (hi_R a) -> encl_small a.
Proof.
intros n a Hn (Ol & Oh & _) Wl Wh. unfold encl_small, exp_small.
destruct (grow_exp_win n _ _ _ Hn Ol Wl); destruct (grow_exp_win n _ _ _ Hn Oh Wh); lia.
Qed.

Lemma pt_small :
  forall n a r, level_ok n -> encl_pt n a r -> grow_win (-4096) 4096 r -> encl_small a.
Proof.
intros n a r Hn (Oa & L & H) W. apply (pt_small_win n a Hn Oa); [rewrite L | rewrite H]; exact W.
Qed.

Lemma pt_win_int :
  forall m, (Z.abs m < 2 ^ 64)%Z -> grow_win (-4096) 4096 (IZR m).
Proof.
intros m Hm.
destruct (grow_int_win (Z.abs m)) as [Z | B]; [lia | |].
- left. apply eq_IZR in Z. rewrite (proj1 (Z.abs_0_iff m) Z). reflexivity.
- right. rewrite <- abs_IZR. rewrite Rabs_pos_eq in B by (apply IZR_le; lia).
  destruct B as (B1 & B2). split.
  + apply Rle_trans with (2 := B1). apply bpow_le. lia.
  + apply Rle_trans with (1 := B2). apply bpow_le. lia.
Qed.

Lemma pt_win_bpow :
  forall e, (-4096 <= e <= 4096)%Z -> grow_win (-4096) 4096 (bpow radix2 e).
Proof.
intros e He. right. rewrite Rabs_pos_eq by apply bpow_ge_0.
split; apply bpow_le; lia.
Qed.

(** ** Values in the format *)

Lemma pt_format_int :
  forall n m, level_ok n -> (Z.abs m < 2 ^ 64)%Z -> fmt n (IZR m).
Proof.
intros n m Hn Hm. pose proof (dprec_bounds n Hn).
assert (P : (2 ^ 64 <= 2 ^ dprec n)%Z) by (apply Z.pow_le_mono_r; lia).
pose proof (format_int n false m 0 Hn ltac:(lia)) as F. cbv iota in F.
change (bpow radix2 0) with 1 in F. rewrite Rmult_1_r in F. exact F.
Qed.

Lemma pt_format_bpow : forall n e, level_ok n -> fmt n (bpow radix2 e).
Proof.
intros n e Hn. pose proof (dprec_bounds n Hn).
assert (P : (2 ^ 1 <= 2 ^ dprec n)%Z) by (apply Z.pow_le_mono_r; lia).
pose proof (format_int n false 1 e Hn ltac:(cbn in P |- *; lia)) as F. cbv iota in F.
rewrite Rmult_1_l in F. exact F.
Qed.

(** ** Comparisons *)

Lemma pt_dy_lt :
  forall n x y,
  level_ok n -> dy_ok n x -> dy_ok n y ->
  DyadicExp.dy_lt n x y = true <-> Dyadic.dy_R x < Dyadic.dy_R y.
Proof.
intros n x y Hn Hx Hy. unfold DyadicExp.dy_lt. rewrite (cmp_correct n _ _ Hn Hx Hy).
destruct (Rcompare_spec (Dyadic.dy_R x) (Dyadic.dy_R y));
  split; intro; try lra; try reflexivity; discriminate.
Qed.

Lemma pt_dy_gt :
  forall n x y,
  level_ok n -> dy_ok n x -> dy_ok n y ->
  DyadicExp.dy_gt n x y = true <-> Dyadic.dy_R y < Dyadic.dy_R x.
Proof.
intros n x y Hn Hx Hy. unfold DyadicExp.dy_gt. rewrite (cmp_correct n _ _ Hn Hx Hy).
destruct (Rcompare_spec (Dyadic.dy_R x) (Dyadic.dy_R y));
  split; intro; try lra; try reflexivity; discriminate.
Qed.

(** ** Operations on points *)

Lemma pt_point :
  forall n x,
  level_ok n -> is_finite x = true ->
  exists c, Dyadic.encl_point n x = Some c /\ encl_pt n c (B2R x) /\ encl_small c.
Proof.
intros n x Hn Hx.
destruct (encl_point_correct n x Hn Hx) as (c & E & Oc & Sc & L & H).
exists c. split; [exact E |]. split; [split; [exact Oc | split; assumption] | exact Sc].
Qed.

Lemma pt_add :
  forall n a b r s,
  level_ok n -> encl_pt n a r -> encl_pt n b s -> encl_small a -> encl_small b ->
  fmt n (r + s) ->
  exists c, Dyadic.encl_add n a b = Some c /\ encl_pt n c (r + s).
Proof.
intros n a b r s Hn (Oa & La & Ha) (Ob & Lb & Hb) Sa Sb F.
destruct (encl_add_correct n a b Hn Oa Ob Sa Sb) as (c & E & Oc & L & H & _).
exists c. split; [exact E |]. split; [exact Oc |].
rewrite L, H, La, Ha, Lb, Hb, !dround_id by assumption. split; reflexivity.
Qed.

Lemma pt_sub :
  forall n a b r s,
  level_ok n -> encl_pt n a r -> encl_pt n b s -> encl_small a -> encl_small b ->
  fmt n (r - s) ->
  exists c, Dyadic.encl_sub n a b = Some c /\ encl_pt n c (r - s).
Proof.
intros n a b r s Hn (Oa & La & Ha) (Ob & Lb & Hb) Sa Sb F.
destruct (encl_sub_correct n a b Hn Oa Ob Sa Sb) as (c & E & Oc & L & H & _).
exists c. split; [exact E |]. split; [exact Oc |].
rewrite L, H, La, Ha, Lb, Hb, !dround_id by assumption. split; reflexivity.
Qed.

Lemma pt_mul :
  forall n a b r s,
  level_ok n -> encl_pt n a r -> encl_pt n b s -> encl_small a -> encl_small b ->
  fmt n (r * s) ->
  exists c, Dyadic.encl_mul n a b = Some c /\ encl_pt n c (r * s).
Proof.
intros n a b r s Hn (Oa & La & Ha) (Ob & Lb & Hb) Sa Sb F.
destruct (encl_mul_correct n a b Hn Oa Ob Sa Sb) as (c & E & Oc & L & H & _).
exists c. split; [exact E |]. split; [exact Oc |].
rewrite L, H, La, Ha, Lb, Hb, !pt_min_id, !pt_max_id, !dround_id by assumption.
split; reflexivity.
Qed.

Lemma pt_div_u64 :
  forall n a r k,
  level_ok n -> encl_pt n a r -> encl_small a -> (0 < k < 2 ^ 64)%Z -> fmt n (r / IZR k) ->
  exists c, Dyadic.encl_div_u64 n a k = Some c /\ encl_pt n c (r / IZR k).
Proof.
intros n a r k Hn (Oa & La & Ha) Sa Hk F.
destruct (encl_div_u64_correct n a k Hn Oa Sa Hk) as (c & E & Oc & L & H & _).
exists c. split; [exact E |]. split; [exact Oc |].
rewrite L, H, La, Ha, !dround_id by assumption. split; reflexivity.
Qed.

Lemma pt_shl :
  forall n a r k,
  level_ok n -> encl_pt n a r -> encl_small a -> (- 2 ^ 62 <= k <= 2 ^ 62)%Z ->
  exists c, Dyadic.encl_shl n a k = Some c /\ encl_pt n c (r * bpow radix2 k).
Proof.
intros n a r k Hn (Oa & La & Ha) Sa Hk.
destruct (encl_shl_correct n a k Hn Oa Sa Hk) as (c & E & Oc & L & H & _).
exists c. split; [exact E |]. split; [exact Oc |].
rewrite L, H, La, Ha. split; reflexivity.
Qed.

Lemma pt_sqrt :
  forall n a r,
  level_ok n -> encl_pt n a r -> encl_small a -> 0 <= r -> fmt n (sqrt r) ->
  exists c, Dyadic.encl_sqrt n a = Some c /\ encl_pt n c (sqrt r).
Proof.
intros n a r Hn (Oa & La & Ha) Sa Hr F.
destruct (encl_sqrt_correct n a Hn Oa Sa ltac:(rewrite Ha; exact Hr)) as (c & E & Oc & L & H & _).
exists c. split; [exact E |]. split; [exact Oc |].
rewrite L, H, La, Ha, (Rmax_left r 0 Hr), !dround_id by assumption. split; reflexivity.
Qed.

(** [mul_int] negates the product by [|k|] for [k < 0], which needs that
    product small, hence the window. *)
Lemma pt_mul_int :
  forall n a r k,
  level_ok n -> encl_pt n a r -> encl_small a -> (Z.abs k < 2 ^ 64)%Z ->
  fmt n (r * IZR k) -> grow_win (-4096) 4096 (r * IZR k) ->
  exists c, DyadicExp.mul_int n a k = Some c /\ encl_pt n c (r * IZR k).
Proof.
intros n a r k Hn (Oa & La & Ha) Sa Hk F W.
(* The product by [|k|] is that by [k] up to its sign, so it is in the
   format and the window too. *)
assert (Ek : r * IZR (Z.abs k) = r * IZR k \/ r * IZR (Z.abs k) = - (r * IZR k)).
{ destruct (Z.abs_spec k) as [(_ & ->) | (_ & ->)]; [left | right]; rewrite ?opp_IZR; ring. }
assert (F' : fmt n (r * IZR (Z.abs k))).
{ destruct Ek as [-> | ->]; [exact F | apply generic_format_opp; exact F]. }
assert (W' : grow_win (-4096) 4096 (r * IZR (Z.abs k))).
{ destruct W as [Z | B]; [left | right]; destruct Ek as [-> | ->]; rewrite ?Rabs_Ropp; try lra.
  all: exact B. }
destruct (encl_mul_u64_correct n a (Z.abs k) Hn Oa Sa ltac:(lia)) as (p & E & Op & L & H & _).
rewrite La in L. rewrite Ha in H. rewrite dround_id in L, H by assumption.
unfold DyadicExp.mul_int. rewrite E. cbv beta iota.
destruct (Z.ltb_spec k 0) as [K | K].
- assert (Pp : encl_pt n p (r * IZR (Z.abs k))) by (split; [exact Op | split; assumption]).
  pose proof (pt_small n p _ Hn Pp W') as Sp.
  destruct (encl_neg_correct n p Hn Op Sp) as (On & _ & Ln & Hn' & _).
  rewrite Z.abs_neq in L, H by lia. rewrite opp_IZR in L, H.
  eexists. split; [reflexivity |]. split; [exact On |].
  rewrite Ln, Hn', L, H. split; ring.
- rewrite Z.abs_eq in L, H by lia.
  eexists. split; [reflexivity |]. split; [exact Op | split; assumption].
Qed.

(** ** The point 0 against any enclosure *)

Lemma pt_mul_int_0 :
  forall n a,
  level_ok n -> encl_ok n a -> encl_small a ->
  exists c, DyadicExp.mul_int n a 0 = Some c /\ encl_pt n c 0.
Proof.
intros n a Hn Oa Sa.
destruct (encl_mul_u64_correct n a 0 Hn Oa Sa ltac:(lia)) as (p & E & Op & L & H & _).
unfold DyadicExp.mul_int. cbn [Z.abs]. rewrite E. cbv beta iota. cbn [Z.ltb Z.compare].
exists p. split; [reflexivity |]. split; [exact Op |].
rewrite L, H, !Rmult_0_r, !dround_0 by exact Hn. split; reflexivity.
Qed.

Lemma pt_mul_0_l :
  forall n a b,
  level_ok n -> encl_pt n a 0 -> encl_ok n b -> encl_small b ->
  exists c, Dyadic.encl_mul n a b = Some c /\ encl_pt n c 0.
Proof.
intros n a b Hn (Oa & La & Ha) Ob Sb.
pose proof (pt_small n a 0 Hn (conj Oa (conj La Ha)) (or_introl eq_refl)) as Sa.
destruct (encl_mul_correct n a b Hn Oa Ob Sa Sb) as (c & E & Oc & L & H & _).
exists c. split; [exact E |]. split; [exact Oc |].
rewrite L, H, La, Ha, !Rmult_0_l, !pt_min_id, !pt_max_id, !dround_0 by exact Hn.
split; reflexivity.
Qed.

Lemma pt_div_0_l :
  forall n a b,
  level_ok n -> encl_pt n a 0 -> encl_ok n b -> encl_small b -> (0 < lo_R b \/ hi_R b < 0) ->
  exists c, Dyadic.encl_div n a b = Some c /\ encl_pt n c 0.
Proof.
intros n a b Hn (Oa & La & Ha) Ob Sb Sg.
pose proof (pt_small n a 0 Hn (conj Oa (conj La Ha)) (or_introl eq_refl)) as Sa.
destruct (encl_div_correct n a b Hn Oa Ob Sa Sb Sg) as (c & E & Oc & L & H & _).
exists c. split; [exact E |]. split; [exact Oc |].
rewrite L, H, La, Ha. unfold Rdiv. rewrite !Rmult_0_l, !pt_min_id, !pt_max_id, !dround_0 by exact Hn.
split; reflexivity.
Qed.
