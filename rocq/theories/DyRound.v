(** * Rounding in the dyadic kernel

    [Dyadic.round] of [Model.v] is Flocq's rounding toward +inf or -inf at
    the precision [64 n] of [n] limbs ([dround]) of the number that its
    limbs and sticky bit stand for. The other lemmas are the facts about
    normalized dyadic numbers ([dy_ok]) that [DyConv.v], [DyIsqrt.v],
    [DyOps.v] and [DyDriver.v] use. Every lemma is for [1 <= n <= 64]
    ([level_ok]), the precisions of Ziv's strategy. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Spec RoundUpExact ParseRound.

Open Scope Z_scope.

Definition dprec (n : nat) : Z := 64 * Z.of_nat n.

Definition level_ok (n : nat) : Prop := (1 <= n <= 64)%nat.

(** [r] rounded toward +inf if [up], and toward -inf otherwise, to [dprec n] bits. *)
Definition dround (n : nat) (up : bool) (r : R) : R :=
  if up then round radix2 (FLX_exp (dprec n)) Zceil r
  else round radix2 (FLX_exp (dprec n)) Zfloor r.

(** A normalized [Dyadic<N>], as the header of [src/dyadic.rs] says. *)
Definition dy_ok (n : nat) (x : Dyadic.dyadic) : Prop :=
  limbs_ok (Dyadic.dy_m x) /\ length (Dyadic.dy_m x) = n /\
  - 2 ^ 63 <= Dyadic.dy_exp x < 2 ^ 63 /\
  ((Limbs.val (Dyadic.dy_m x) = 0 /\ Dyadic.dy_neg x = false /\ Dyadic.dy_exp x = 0) \/
   2 ^ (dprec n - 1) <= Limbs.val (Dyadic.dy_m x)).

(** An exponent far enough from the ends of [i64] that no operation of
    [DyOps.v] on it overflows. *)
Definition exp_small (x : Dyadic.dyadic) : Prop := - 2 ^ 61 <= Dyadic.dy_exp x <= 2 ^ 61.

(** ** [dround] *)

Lemma dprec_bounds : forall n, level_ok n -> 64 <= dprec n <= 4096.
Proof. intros n Hn. unfold level_ok, dprec in *. lia. Qed.

Lemma dprec_gt_0 : forall n, level_ok n -> Prec_gt_0 (dprec n).
Proof. intros n Hn. unfold Prec_gt_0. pose proof (dprec_bounds n Hn). lia. Qed.

Lemma dround_le :
  forall n up r1 r2, level_ok n -> (r1 <= r2)%R -> (dround n up r1 <= dround n up r2)%R.
Proof.
intros n up r1 r2 Hn Hr. pose proof (dprec_gt_0 n Hn).
unfold dround. destruct up; apply round_le; auto with typeclass_instances.
Qed.

Lemma dround_bounds : forall n r, level_ok n -> (dround n false r <= r <= dround n true r)%R.
Proof.
intros n r Hn. pose proof (dprec_gt_0 n Hn). unfold dround.
destruct (round_DN_pt radix2 (FLX_exp (dprec n)) r) as (_ & H1 & _).
destruct (round_UP_pt radix2 (FLX_exp (dprec n)) r) as (_ & H2 & _).
lra.
Qed.

Lemma dround_id :
  forall n up r,
  level_ok n -> generic_format radix2 (FLX_exp (dprec n)) r -> dround n up r = r.
Proof.
intros n up r Hn Hf. pose proof (dprec_gt_0 n Hn). unfold dround.
destruct up; apply round_generic; auto with typeclass_instances.
Qed.

Lemma dround_opp : forall n up r, level_ok n -> dround n up (- r) = (- dround n (negb up) r)%R.
Proof.
intros n up r Hn. pose proof (dprec_gt_0 n Hn). unfold dround.
destruct up; simpl.
- apply round_UP_opp.
- apply round_DN_opp.
Qed.

(** The width lemma of one rounding: at most [|r| * 2^(1 - p)], and 0 for
    an [r] of [p] bits (by [dround_id]). *)
Lemma dround_width :
  forall n r,
  level_ok n -> (dround n true r - dround n false r <= Rabs r * bpow radix2 (1 - dprec n))%R.
Proof.
intros n r Hn. pose proof (dprec_gt_0 n Hn).
assert (Hb : (0 <= Rabs r * bpow radix2 (1 - dprec n))%R).
{ apply Rmult_le_pos; [apply Rabs_pos | apply bpow_ge_0]. }
destruct (generic_format_EM radix2 (FLX_exp (dprec n)) r) as [Hf | Hf].
- rewrite !dround_id by assumption. lra.
- unfold dround. rewrite round_UP_DN_ulp by assumption.
  pose proof (ulp_FLX_le radix2 (dprec n) r). lra.
Qed.

(** The width of an enclosure [[el, eh]] rounded outward. *)
Lemma encl_round_width :
  forall n el eh,
  level_ok n -> (el <= eh)%R ->
  (dround n true eh - dround n false el <=
   (eh - el) + (Rabs el + Rabs eh) * bpow radix2 (1 - dprec n))%R.
Proof.
intros n el eh Hn _.
pose proof (dround_bounds n el Hn). pose proof (dround_bounds n eh Hn).
pose proof (dround_width n el Hn). pose proof (dround_width n eh Hn).
rewrite Rmult_plus_distr_r. lra.
Qed.

(** ** Normalized numbers *)

Lemma checked_i64 : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> checked_i 64 z = Some z.
Proof. intros z Hz. apply checked_i_ok. exact Hz. Qed.

(** [2^(p - 1) = 2^63 * 2^(p - 64)] and [2^p = 2^64 * 2^(p - 64)] *)
Lemma dprec_split :
  forall n,
  level_ok n ->
  2 ^ (dprec n - 1) = 2 ^ 63 * 2 ^ (64 * Z.of_nat (n - 1)) /\
  2 ^ dprec n = 2 ^ 64 * 2 ^ (64 * Z.of_nat (n - 1)).
Proof.
intros n Hn. pose proof (dprec_bounds n Hn).
replace (64 * Z.of_nat (n - 1)) with (dprec n - 64) by (unfold level_ok, dprec in *; lia).
rewrite <- !Z.pow_add_r by lia.
split; f_equal; lia.
Qed.

(** The top limb of a normalized mantissa has its top bit set. *)
Lemma top_limb :
  forall n m,
  level_ok n -> limbs_ok m -> length m = n -> 2 ^ (dprec n - 1) <= Limbs.val m ->
  2 ^ 63 <= Limbs.limb m (n - 1) < 2 ^ 64.
Proof.
intros n m Hn Hm Hl Hv.
destruct (dprec_split n Hn) as [H1 H2].
pose proof (val_bounds m Hm) as Hb. rewrite Hl in Hb. fold (dprec n) in Hb.
rewrite limb_val by exact Hm.
remember (2 ^ (64 * Z.of_nat (n - 1))) as P eqn:HP.
assert (HP0 : 0 < P) by (rewrite HP; apply pow64_pos).
assert (Hq1 : 2 ^ 63 <= Limbs.val m / P).
{ apply Z.div_le_lower_bound; lia. }
assert (Hq2 : Limbs.val m / P < 2 ^ 64).
{ apply Z.div_lt_upper_bound; lia. }
rewrite Z.mod_small by lia. lia.
Qed.

Lemma val_nonneg : forall m, limbs_ok m -> 0 <= Limbs.val m.
Proof. intros m Hm. apply (val_bounds m Hm). Qed.

(** [dy_R] without its sign. *)
Lemma dy_abs :
  forall x,
  limbs_ok (Dyadic.dy_m x) ->
  Rabs (Dyadic.dy_R x) = (IZR (Limbs.val (Dyadic.dy_m x)) * bpow radix2 (Dyadic.dy_exp x))%R.
Proof.
intros x Hm. unfold Dyadic.dy_R.
assert (H : (0 <= IZR (Limbs.val (Dyadic.dy_m x)) * bpow radix2 (Dyadic.dy_exp x))%R).
{ apply Rmult_le_pos; [apply IZR_le, val_nonneg, Hm | apply bpow_ge_0]. }
destruct (Dyadic.dy_neg x); [rewrite Rabs_Ropp |]; apply Rabs_pos_eq; exact H.
Qed.

(** A normalized number is zero, with [neg = false] and [exp = 0], or
    has a mantissa of [p] bits. *)
Lemma dy_cases :
  forall n x,
  level_ok n -> dy_ok n x ->
  (Dyadic.is_zero n x = true /\ Limbs.val (Dyadic.dy_m x) = 0 /\ Dyadic.dy_neg x = false /\
   Dyadic.dy_exp x = 0 /\ Dyadic.dy_R x = 0%R) \/
  (Dyadic.is_zero n x = false /\
   2 ^ (dprec n - 1) <= Limbs.val (Dyadic.dy_m x) < 2 ^ dprec n /\
   (bpow radix2 (Dyadic.dy_exp x + dprec n - 1) <= Rabs (Dyadic.dy_R x) <
    bpow radix2 (Dyadic.dy_exp x + dprec n))%R).
Proof.
intros n x Hn (Hm & Hl & He & [(Hv & Hneg & Hx) | Hv]).
- left. unfold Dyadic.is_zero. rewrite limb_val by exact Hm. rewrite Hv.
  rewrite Z.div_0_l by (apply Z.pow_nonzero; lia). rewrite Z.mod_0_l by lia.
  repeat split; try assumption.
  unfold Dyadic.dy_R. rewrite Hv, Hneg. simpl. ring.
- right. pose proof (top_limb n _ Hn Hm Hl Hv) as Ht.
  pose proof (val_bounds _ Hm) as Hb. rewrite Hl in Hb. fold (dprec n) in Hb.
  pose proof (dprec_bounds n Hn).
  split; [unfold Dyadic.is_zero; apply Z.eqb_neq; lia |].
  split; [lia |].
  rewrite dy_abs by exact Hm.
  replace (Dyadic.dy_exp x + dprec n - 1) with ((dprec n - 1) + Dyadic.dy_exp x) by ring.
  replace (Dyadic.dy_exp x + dprec n) with (dprec n + Dyadic.dy_exp x) by ring.
  rewrite !bpow_plus.
  rewrite <- (IZR_Zpower radix2 (dprec n - 1)), <- (IZR_Zpower radix2 (dprec n)) by lia.
  pose proof (bpow_gt_0 radix2 (Dyadic.dy_exp x)).
  split; [apply Rmult_le_compat_r | apply Rmult_lt_compat_r]; try lra.
  + apply IZR_le. simpl. lia.
  + apply IZR_lt. simpl. lia.
Qed.

(** An integer of [p] bits times a power of 2 has [p] bits. *)
Lemma format_int :
  forall n (s : bool) m e,
  level_ok n -> Z.abs m < 2 ^ dprec n ->
  generic_format radix2 (FLX_exp (dprec n))
    (if s then (- (IZR m * bpow radix2 e))%R else (IZR m * bpow radix2 e)%R).
Proof.
intros n s m e Hn Hm. pose proof (dprec_gt_0 n Hn).
apply generic_format_FLX.
exists (Float radix2 (if s then - m else m) e).
- unfold F2R; simpl. destruct s; [rewrite opp_IZR; ring | reflexivity].
- simpl. destruct s; [rewrite Z.abs_opp |]; exact Hm.
Qed.

Lemma dy_zero_ok :
  forall n,
  dy_ok n (Dyadic.dy_zero n) /\ Dyadic.dy_R (Dyadic.dy_zero n) = 0%R /\
  exp_small (Dyadic.dy_zero n).
Proof.
intros n. unfold dy_ok, exp_small, Dyadic.dy_zero, Dyadic.dy_R; simpl.
rewrite val_repeat0. split; [| split].
- split; [apply limbs_ok_repeat0 |]. split; [apply repeat_length |].
  split; [lia |]. left; repeat split.
- simpl. ring.
- lia.
Qed.

Lemma dy_format :
  forall n x,
  level_ok n -> dy_ok n x -> generic_format radix2 (FLX_exp (dprec n)) (Dyadic.dy_R x).
Proof.
intros n x Hn Hx.
destruct Hx as (Hm & Hl & _). pose proof (val_bounds _ Hm) as Hb.
rewrite Hl in Hb. fold (dprec n) in Hb.
unfold Dyadic.dy_R. apply format_int; [exact Hn | rewrite Z.abs_eq; lia].
Qed.

(** The exponent of a nonzero number follows from its value, so bounds on
    values bound exponents. *)
Lemma exp_of_value :
  forall n d,
  level_ok n -> dy_ok n d -> Dyadic.dy_R d <> 0%R ->
  Dyadic.dy_exp d = mag radix2 (Dyadic.dy_R d) - dprec n.
Proof.
intros n d Hn Hd Hz.
destruct (dy_cases n d Hn Hd) as [(_ & _ & _ & _ & H) | (_ & _ & H)]; [contradiction |].
rewrite (mag_unique radix2 (Dyadic.dy_R d) (Dyadic.dy_exp d + dprec n) H). ring.
Qed.

Lemma is_zero_correct :
  forall n x, level_ok n -> dy_ok n x -> (Dyadic.is_zero n x = true <-> Dyadic.dy_R x = 0%R).
Proof.
intros n x Hn Hx.
destruct (dy_cases n x Hn Hx) as [(Hz & _ & _ & _ & H) | (Hz & _ & H)];
  rewrite Hz; split; intros; try easy.
exfalso. pose proof (bpow_gt_0 radix2 (Dyadic.dy_exp x + dprec n - 1)).
rewrite H0, Rabs_R0 in H. lra.
Qed.

Lemma neg_correct :
  forall n x,
  level_ok n -> dy_ok n x ->
  dy_ok n (Dyadic.neg n x) /\ Dyadic.dy_R (Dyadic.neg n x) = (- Dyadic.dy_R x)%R /\
  Dyadic.dy_exp (Dyadic.neg n x) = Dyadic.dy_exp x.
Proof.
intros n x Hn Hx. unfold Dyadic.neg.
destruct (dy_cases n x Hn Hx) as [(Hz & _ & _ & _ & H) | (Hz & Hv & _)]; rewrite Hz.
- rewrite H. split; [exact Hx |]. split; [ring | reflexivity].
- destruct Hx as (Hm & Hl & He & _).
  split; [| split; [| reflexivity]].
  + unfold dy_ok; simpl. split; [exact Hm |]. split; [exact Hl |].
    split; [exact He |]. right; lia.
  + unfold Dyadic.dy_R; simpl. destruct (Dyadic.dy_neg x); simpl; ring.
Qed.

Lemma shl_correct :
  forall n x k,
  level_ok n -> dy_ok n x -> - 2 ^ 63 <= Dyadic.dy_exp x + k < 2 ^ 63 ->
  exists d,
  Dyadic.shl n x k = Some d /\ dy_ok n d /\
  Dyadic.dy_R d = (Dyadic.dy_R x * bpow radix2 k)%R.
Proof.
intros n x k Hn Hx Hk. unfold Dyadic.shl.
destruct (dy_cases n x Hn Hx) as [(Hz & _ & _ & _ & H) | (Hz & Hv & _)]; rewrite Hz.
- exists x. split; [reflexivity |]. split; [exact Hx |]. rewrite H. ring.
- rewrite checked_i64 by exact Hk. eexists. split; [reflexivity |].
  destruct Hx as (Hm & Hl & He & _). split.
  + unfold dy_ok; simpl. split; [exact Hm |]. split; [exact Hl |].
    split; [lia |]. right; lia.
  + unfold Dyadic.dy_R; simpl. rewrite bpow_plus.
    destruct (Dyadic.dy_neg x); ring.
Qed.

Lemma cmp_abs_correct :
  forall n x y,
  level_ok n -> dy_ok n x -> dy_ok n y ->
  Dyadic.cmp_abs n x y = Rcompare (Rabs (Dyadic.dy_R x)) (Rabs (Dyadic.dy_R y)).
Proof.
intros n x y Hn Hx Hy. unfold Dyadic.cmp_abs.
destruct (dy_cases n x Hn Hx) as [(Hzx & _ & _ & _ & Rx) | (Hzx & Hvx & Rx)];
destruct (dy_cases n y Hn Hy) as [(Hzy & _ & _ & _ & Ry) | (Hzy & Hvy & Ry)];
  rewrite Hzx, Hzy.
- rewrite Rx, Ry. symmetry. apply Rcompare_Eq. reflexivity.
- rewrite Rx, Rabs_R0. symmetry. apply Rcompare_Lt.
  pose proof (bpow_gt_0 radix2 (Dyadic.dy_exp y + dprec n - 1)). lra.
- rewrite Ry, Rabs_R0. symmetry. apply Rcompare_Gt.
  pose proof (bpow_gt_0 radix2 (Dyadic.dy_exp x + dprec n - 1)). lra.
- destruct (Z.compare_spec (Dyadic.dy_exp x) (Dyadic.dy_exp y)) as [He | He | He].
  + rewrite (Limbs.cmp_correct _ _ (proj1 Hx) (proj1 Hy)).
    rewrite !dy_abs by (apply Hx || apply Hy). rewrite He.
    rewrite Rcompare_mult_r by apply bpow_gt_0.
    symmetry. apply Rcompare_IZR.
  + symmetry. apply Rcompare_Lt.
    assert (Hb : (bpow radix2 (Dyadic.dy_exp x + dprec n) <=
                  bpow radix2 (Dyadic.dy_exp y + dprec n - 1))%R) by (apply bpow_le; lia).
    lra.
  + symmetry. apply Rcompare_Gt.
    assert (Hb : (bpow radix2 (Dyadic.dy_exp y + dprec n) <=
                  bpow radix2 (Dyadic.dy_exp x + dprec n - 1))%R) by (apply bpow_le; lia).
    lra.
Qed.

Lemma dy_R_sign :
  forall x,
  limbs_ok (Dyadic.dy_m x) ->
  Dyadic.dy_R x = (if Dyadic.dy_neg x then - Rabs (Dyadic.dy_R x) else Rabs (Dyadic.dy_R x))%R.
Proof.
intros x Hm. rewrite dy_abs by exact Hm.
unfold Dyadic.dy_R. destruct (Dyadic.dy_neg x); reflexivity.
Qed.

(** The sign of a normalized number, as [Dyadic.sign] reads it. *)
Lemma dy_sign_cases :
  forall n x,
  level_ok n -> dy_ok n x ->
  (Dyadic.sign n x = 0 /\ Dyadic.dy_neg x = false /\ Dyadic.dy_R x = 0%R) \/
  exists A,
  (0 < A)%R /\ Rabs (Dyadic.dy_R x) = A /\ Dyadic.is_zero n x = false /\
  Dyadic.sign n x = (if Dyadic.dy_neg x then -1 else 1) /\
  Dyadic.dy_R x = (if Dyadic.dy_neg x then - A else A)%R.
Proof.
intros n x Hn Hx. unfold Dyadic.sign.
destruct (dy_cases n x Hn Hx) as [(Hz & _ & Hneg & _ & H) | (Hz & _ & H)]; rewrite Hz.
- left. split; [reflexivity |]. split; assumption.
- right. exists (Rabs (Dyadic.dy_R x)).
  pose proof (bpow_gt_0 radix2 (Dyadic.dy_exp x + dprec n - 1)).
  split; [lra |]. split; [reflexivity |]. split; [reflexivity |].
  split; [reflexivity |]. apply dy_R_sign, Hx.
Qed.

Lemma cmp_correct :
  forall n x y,
  level_ok n -> dy_ok n x -> dy_ok n y ->
  Dyadic.cmp n x y = Rcompare (Dyadic.dy_R x) (Dyadic.dy_R y).
Proof.
intros n x y Hn Hx Hy. unfold Dyadic.cmp.
rewrite (cmp_abs_correct n x y Hn Hx Hy), (cmp_abs_correct n y x Hn Hy Hx).
destruct (dy_sign_cases n x Hn Hx) as [(Sx & Nx & Rx) | (A & HA & Ax & _ & Sx & Rx)];
destruct (dy_sign_cases n y Hn Hy) as [(Sy & Ny & Ry) | (B & HB & By & _ & Sy & Ry)];
  rewrite Sx, Sy; try rewrite Ax; try rewrite By; rewrite Rx, Ry; try rewrite Nx;
  try rewrite Ny; rewrite ?Rabs_R0;
  try destruct (Dyadic.dy_neg x); try destruct (Dyadic.dy_neg y); simpl;
  first
    [ reflexivity
    | rewrite Rcompare_opp; reflexivity
    | symmetry; apply Rcompare_Lt; lra
    | symmetry; apply Rcompare_Gt; lra ].
Qed.

Lemma dmin_correct :
  forall n x y,
  level_ok n -> dy_ok n x -> dy_ok n y ->
  (Dyadic.dmin n x y = x \/ Dyadic.dmin n x y = y) /\
  Dyadic.dy_R (Dyadic.dmin n x y) = Rmin (Dyadic.dy_R x) (Dyadic.dy_R y).
Proof.
intros n x y Hn Hx Hy. unfold Dyadic.dmin. rewrite (cmp_correct n x y Hn Hx Hy).
destruct (Rcompare_spec (Dyadic.dy_R x) (Dyadic.dy_R y)) as [H | H | H].
- split; [left; reflexivity |]. symmetry. apply Rmin_left. lra.
- split; [left; reflexivity |]. symmetry. apply Rmin_left. lra.
- split; [right; reflexivity |]. symmetry. apply Rmin_right. lra.
Qed.

Lemma dmax_correct :
  forall n x y,
  level_ok n -> dy_ok n x -> dy_ok n y ->
  (Dyadic.dmax n x y = x \/ Dyadic.dmax n x y = y) /\
  Dyadic.dy_R (Dyadic.dmax n x y) = Rmax (Dyadic.dy_R x) (Dyadic.dy_R y).
Proof.
intros n x y Hn Hx Hy. unfold Dyadic.dmax. rewrite (cmp_correct n x y Hn Hx Hy).
destruct (Rcompare_spec (Dyadic.dy_R x) (Dyadic.dy_R y)) as [H | H | H].
- split; [right; reflexivity |]. symmetry. apply Rmax_right. lra.
- split; [right; reflexivity |]. symmetry. apply Rmax_right. lra.
- split; [left; reflexivity |]. symmetry. apply Rmax_left. lra.
Qed.

(** ** [round], [from_f64] and [to_f64] *)

Lemma existsb_nonzero :
  forall y,
  limbs_ok y -> (existsb (fun l => negb (l =? 0)) y = true <-> Limbs.val y <> 0).
Proof.
induction y as [| a y IH]; intros Hy.
- simpl. split; [discriminate | intros H; exfalso; apply H; reflexivity].
- apply limbs_ok_cons in Hy. destruct Hy as [Ha Hy].
  specialize (IH Hy). pose proof (val_nonneg y Hy).
  change (existsb (fun l => negb (l =? 0)) (a :: y))
    with (negb (a =? 0) || existsb (fun l => negb (l =? 0)) y).
  change (Limbs.val (a :: y)) with (a + 2 ^ 64 * Limbs.val y).
  rewrite Bool.orb_true_iff, IH, Bool.negb_true_iff, Z.eqb_neq. lia.
Qed.

(** [a mod (P * C) = a mod P + P * (a / P mod C)] is zero exactly when
    both of its parts are. *)
Lemma mod_split_zero :
  forall a P C,
  0 <= a -> 0 < P -> 0 < C ->
  (a mod P <> 0 \/ a / P mod C <> 0 <-> a mod (P * C) <> 0).
Proof.
intros a P C Ha HP HC. rewrite Z.rem_mul_r by lia.
pose proof (Z.mod_pos_bound a P HP). pose proof (Z.mod_pos_bound (a / P) C HC).
remember (a mod P) as A. remember (a / P mod C) as B.
split; intros Hh; nia.
Qed.

Lemma low_bits_nonzero_correct :
  forall x k,
  limbs_ok x -> 0 <= k ->
  (Dyadic.low_bits_nonzero x k = true <-> Limbs.val x mod 2 ^ k <> 0).
Proof.
intros x k Hx Hk. unfold Dyadic.low_bits_nonzero.
pose proof (Z.div_mod k 64 ltac:(lia)) as Hks.
pose proof (Z.mod_pos_bound k 64 ltac:(lia)) as Hs.
pose proof (Z.div_pos k 64 Hk ltac:(lia)) as Hj.
remember (k / 64) as j. remember (k mod 64) as s.
rewrite Bool.orb_true_iff, existsb_nonzero by (apply limbs_ok_firstn, Hx).
rewrite val_firstn by exact Hx.
rewrite Bool.negb_true_iff, Z.eqb_neq.
assert (Hones : Z.shiftl 1 s - 1 = Z.ones s) by (unfold Z.ones; lia).
rewrite Hones, Z.land_ones by lia.
rewrite limb_val by exact Hx.
rewrite Z2Nat.id by lia.
pose proof (val_nonneg x Hx).
assert (H64 : 2 ^ 64 = 2 ^ s * 2 ^ (64 - s)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite H64, Z.rem_mul_r by lia.
rewrite (Z.mul_comm (2 ^ s)), Z.mod_add, Z.mod_mod by lia.
rewrite Hks, Z.pow_add_r by lia.
apply mod_split_zero; lia.
Qed.

Lemma dround_cond_opp :
  forall n up neg r,
  level_ok n -> dround n up (cond_Ropp neg r) = cond_Ropp neg (dround n (xorb neg up) r).
Proof.
intros n up neg r Hn. destruct neg; simpl; [| reflexivity].
rewrite dround_opp by exact Hn. reflexivity.
Qed.

(** The rounding of a positive [v] in [[M 2^E, (M + 1) 2^E)] for an [M]
    of [p] bits. *)
Lemma dround_mag :
  forall n up M E v (inexact : bool),
  level_ok n -> 2 ^ (dprec n - 1) <= M < 2 ^ dprec n ->
  (IZR M * bpow radix2 E <= v < IZR (M + 1) * bpow radix2 E)%R ->
  (inexact = false <-> v = (IZR M * bpow radix2 E)%R) ->
  dround n up v = (IZR (if inexact && up then M + 1 else M) * bpow radix2 E)%R.
Proof.
intros n up M E v inexact Hn HM Hv Hi.
pose proof (dprec_bounds n Hn) as Hp. pose proof (dprec_gt_0 n Hn).
pose proof (bpow_gt_0 radix2 E) as HB.
pose proof (bpow_gt_0 radix2 (dprec n - 1)) as HB1.
assert (HE : (bpow radix2 E * bpow radix2 (- E) = 1)%R).
{ rewrite <- bpow_plus, Z.add_opp_diag_r. reflexivity. }
assert (HM1 : (bpow radix2 (dprec n - 1) <= IZR M)%R).
{ rewrite <- IZR_Zpower by lia. apply IZR_le. simpl. lia. }
assert (HM2 : (IZR (M + 1) <= bpow radix2 (dprec n))%R).
{ rewrite <- IZR_Zpower by lia. apply IZR_le. simpl. lia. }
assert (HMB : (0 <= IZR M * bpow radix2 E)%R) by (apply Rmult_le_pos; lra).
assert (Hmag : mag radix2 v = E + dprec n :> Z).
{ apply mag_unique. rewrite Rabs_pos_eq by lra.
  replace (E + dprec n - 1) with ((dprec n - 1) + E) by ring.
  replace (E + dprec n) with (dprec n + E) by ring.
  rewrite !bpow_plus. split.
  - apply Rle_trans with (IZR M * bpow radix2 E)%R; [| lra].
    apply Rmult_le_compat_r; lra.
  - apply Rlt_le_trans with (IZR (M + 1) * bpow radix2 E)%R; [lra |].
    apply Rmult_le_compat_r; lra. }
assert (Hz1 : (IZR M <= v * bpow radix2 (- E))%R).
{ replace (IZR M) with (IZR M * bpow radix2 E * bpow radix2 (- E))%R
    by (rewrite Rmult_assoc, HE; ring).
  apply Rmult_le_compat_r; [apply bpow_ge_0 | lra]. }
assert (Hz2 : (v * bpow radix2 (- E) < IZR (M + 1))%R).
{ replace (IZR (M + 1)) with (IZR (M + 1) * bpow radix2 E * bpow radix2 (- E))%R
    by (rewrite Rmult_assoc, HE; ring).
  apply Rmult_lt_compat_r; [apply bpow_gt_0 | lra]. }
(* [round] is [rnd (v 2^-E) * 2^E], as the exponent of [v] is [E + p]. *)
assert (Hr : forall rnd : R -> Z,
           round radix2 (FLX_exp (dprec n)) rnd v =
           (IZR (rnd (v * bpow radix2 (- E))%R) * bpow radix2 E)%R).
{ intros rnd. unfold round, F2R, scaled_mantissa, cexp, FLX_exp. rewrite Hmag.
  replace (E + dprec n - dprec n) with E by ring. reflexivity. }
unfold dround. destruct inexact, up; cbn [andb]; rewrite Hr.
- (* inexact and up: [M < v 2^-E], so the ceiling is [M + 1]. *)
  rewrite (Zceil_imp (M + 1)); [reflexivity |]. split; [| lra].
  replace (M + 1 - 1) with M by ring.
  destruct (Rle_lt_or_eq_dec _ _ Hz1) as [Hlt | Heq]; [exact Hlt |].
  exfalso. assert (Hd : true = false); [| discriminate]. apply Hi.
  apply (Rmult_eq_reg_r (bpow radix2 (- E))); [| apply Rgt_not_eq, bpow_gt_0].
  rewrite Rmult_assoc, HE, Rmult_1_r. symmetry. exact Heq.
- rewrite (Zfloor_imp M); [reflexivity | lra].
- (* exact: [v 2^-E = M]. *)
  rewrite (proj1 Hi eq_refl), Rmult_assoc, HE, Rmult_1_r, Zceil_IZR. reflexivity.
- rewrite (Zfloor_imp M); [reflexivity | lra].
Qed.

(** The end of [Dyadic.round], from its [let* exp]: [m] holds the [p]
    bits [M] of a positive [v] in [[M 2^E, (M + 1) 2^E)], and [dropped]
    says whether [v] is not [M 2^E]. *)
Lemma round_tail :
  forall n neg up m M E v (dropped : bool),
  level_ok n -> limbs_ok m -> length m = n -> Limbs.val m = M ->
  2 ^ (dprec n - 1) <= M < 2 ^ dprec n -> - 2 ^ 63 <= E < 2 ^ 63 - 1 ->
  (IZR M * bpow radix2 E <= v < IZR (M + 1) * bpow radix2 E)%R ->
  (dropped = false <-> v = (IZR M * bpow radix2 E)%R) ->
  exists d,
  (if dropped && negb (Bool.eqb up neg) then
     let (m', c) := Limbs.add_assign m (1 :: nil) in
     if c then
       let* exp' := checked_i 64 (E + 1) in
       Some {| Dyadic.dy_neg := neg; Dyadic.dy_exp := exp';
               Dyadic.dy_m := Limbs.update m' (n - 1) (2 ^ 63 :: nil) |}
     else Some {| Dyadic.dy_neg := neg; Dyadic.dy_exp := E; Dyadic.dy_m := m' |}
   else Some {| Dyadic.dy_neg := neg; Dyadic.dy_exp := E; Dyadic.dy_m := m |}) = Some d /\
  dy_ok n d /\ Dyadic.dy_R d = dround n up (cond_Ropp neg v).
Proof.
intros n neg up m M E v dropped Hn Hm Hl HvM HM HE Hv Hd.
pose proof (dprec_bounds n Hn) as Hp.
rewrite dround_cond_opp by exact Hn.
rewrite (dround_mag n (xorb neg up) M E v dropped Hn HM Hv Hd).
(* The model's [negb (Bool.eqb up neg)] is [xorb neg up]: the rounding
   is away from zero exactly when it is up for a positive number or down
   for a negative one. *)
replace (negb (Bool.eqb up neg)) with (xorb neg up) by (destruct up, neg; reflexivity).
destruct (dropped && xorb neg up) eqn:Hdu.
- destruct (Limbs.add_assign m (1 :: nil)) as [m' c] eqn:Ha.
  assert (H1 : limbs_ok (1 :: nil)) by (apply limbs_ok_cons; split; [lia | constructor]).
  assert (Hl1 : (length (1 :: nil) <= length m)%nat)
    by (rewrite Hl; unfold level_ok in Hn; cbn [length]; lia).
  destruct (add_assign_correct m (1 :: nil) m' c Hm H1 Hl1 Ha) as (Hm' & Hl' & Hv').
  cbn [Limbs.val] in Hv'. rewrite Hl in Hv', Hl'.
  change (64 * Z.of_nat n) with (dprec n) in Hv'.
  pose proof (val_bounds m' Hm') as Hb'. rewrite Hl' in Hb'.
  change (64 * Z.of_nat n) with (dprec n) in Hb'.
  destruct c; cbn [Z.b2z] in Hv'.
  + (* The carry out: [M + 1 = 2^p], so [m'] is zero and the result is
       [2^(p - 1) 2^(E + 1)]. *)
    assert (Hm0 : Limbs.val m' = 0) by lia.
    assert (HM1 : M + 1 = 2 ^ dprec n) by lia.
    rewrite checked_i64 by lia.
    eexists. split; [reflexivity |].
    assert (Hlu : (n - 1 + length (2 ^ 63 :: nil) <= length m')%nat)
      by (rewrite Hl'; unfold level_ok in Hn; cbn [length]; lia).
    assert (Hup : Limbs.val (Limbs.update m' (n - 1) (2 ^ 63 :: nil)) = 2 ^ (dprec n - 1)).
    { rewrite val_update by assumption. cbn [length].
      rewrite val_firstn by (apply limbs_ok_skipn; exact Hm').
      rewrite val_skipn by exact Hm'. rewrite Hm0, Z.div_0_l by (apply Z.pow_nonzero; lia).
      rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
      cbn [Limbs.val]. destruct (dprec_split n Hn) as [Hs _]. rewrite Hs. ring. }
    split.
    * unfold dy_ok; cbn [Dyadic.dy_m Dyadic.dy_exp Dyadic.dy_neg].
      split; [apply limbs_ok_update; [exact Hm' | apply limbs_ok_cons; split; [lia | constructor]] |].
      split; [rewrite update_length by exact Hlu; lia |].
      split; [lia |]. right. lia.
    * unfold Dyadic.dy_R, cond_Ropp; cbn [Dyadic.dy_m Dyadic.dy_exp Dyadic.dy_neg].
      rewrite Hup, HM1.
      assert (Hval : (IZR (2 ^ (dprec n - 1)) * bpow radix2 (E + 1) =
                      IZR (2 ^ dprec n) * bpow radix2 E)%R).
      { assert (Hp1 : 0 <= dprec n - 1) by lia. assert (Hp0 : 0 <= dprec n) by lia.
        rewrite (IZR_pow2 _ Hp1), (IZR_pow2 _ Hp0).
        rewrite <- !bpow_plus. f_equal. ring. }
      rewrite Hval. reflexivity.
  + (* No carry: [m'] holds [M + 1 < 2^p]. *)
    rewrite Z.add_0_r in Hv'.
    eexists. split; [reflexivity |]. split.
    * unfold dy_ok; cbn [Dyadic.dy_m Dyadic.dy_exp Dyadic.dy_neg].
      split; [exact Hm' |]. split; [exact Hl' |]. split; [lia |]. right. lia.
    * unfold Dyadic.dy_R, cond_Ropp; cbn [Dyadic.dy_m Dyadic.dy_exp Dyadic.dy_neg].
      rewrite Hv', HvM. reflexivity.
- eexists. split; [reflexivity |]. split.
  + unfold dy_ok; cbn [Dyadic.dy_m Dyadic.dy_exp Dyadic.dy_neg].
    split; [exact Hm |]. split; [exact Hl |]. split; [lia |]. right. lia.
  + unfold Dyadic.dy_R, cond_Ropp; cbn [Dyadic.dy_m Dyadic.dy_exp Dyadic.dy_neg].
    rewrite HvM. reflexivity.
Qed.

(** The one rounding of every operation: [(-1)^neg * (x + t) * 2^e] for a
    [t] in [(0, 1)] if [sticky] and [t = 0] otherwise, where a sticky [x]
    has at least [p] bits, and the exponent of the result fits an [i64]. *)
Lemma round_correct :
  forall (n : nat) (neg : bool) (x : list Z) (e : Z) (sticky up : bool) (t : R),
  level_ok n -> limbs_ok x ->
  (if sticky then (0 < t < 1)%R /\ 2 ^ (dprec n - 1) <= Limbs.val x else t = 0%R) ->
  (Limbs.val x = 0 \/ - 2 ^ 63 <= e + nat_bits (Limbs.val x) - dprec n < 2 ^ 63 - 1) ->
  exists d,
  Dyadic.round n neg x e sticky up = Some d /\ dy_ok n d /\
  Dyadic.dy_R d = dround n up (cond_Ropp neg ((IZR (Limbs.val x) + t) * bpow radix2 e)).
Proof.
intros n neg x e sticky up t Hn Hx Ht He.
pose proof (dprec_bounds n Hn) as Hp.
pose proof (Z.pow_pos_nonneg 2 (dprec n - 1) ltac:(lia) ltac:(lia)) as Hp1.
unfold Dyadic.round. cbv zeta.
rewrite bit_len_correct by exact Hx.
change (64 * Z.of_nat n) with (dprec n).
pose proof (val_nonneg x Hx) as HX0.
remember (Limbs.val x) as X eqn:HX.
destruct (Z.eq_dec X 0) as [H0 | H0].
- (* Zero: [t] is zero too, as a sticky [x] is not. *)
  assert (Ht0 : t = 0%R).
  { destruct sticky; [destruct Ht as [_ Ht]; lia | exact Ht]. }
  rewrite H0. exists (Dyadic.dy_zero n). split; [reflexivity |].
  destruct (dy_zero_ok n) as (Hz1 & Hz2 & _). split; [exact Hz1 |].
  rewrite Hz2, Ht0.
  replace (cond_Ropp neg ((IZR 0 + 0) * bpow radix2 e)) with 0%R
    by (destruct neg; simpl; ring).
  pose proof (dprec_gt_0 n Hn).
  unfold dround. destruct up; symmetry; apply round_0; auto with typeclass_instances.
- assert (HXpos : 0 < X) by lia.
  pose proof (Z.log2_nonneg X) as Hlog.
  destruct (Z.log2_spec X HXpos) as [HlX1 HlX2].
  change (Z.succ (Z.log2 X)) with (Z.log2 X + 1) in HlX2.
  assert (Hnb : nat_bits X = Z.log2 X + 1)
    by (unfold nat_bits; rewrite (proj2 (Z.eqb_neq X 0) H0); reflexivity).
  rewrite Hnb in He |- *.
  destruct He as [He | He]; [lia |].
  assert (Hl1 : 2 ^ (Z.log2 X + 1 - 1) <= X)
    by (replace (Z.log2 X + 1 - 1) with (Z.log2 X) by ring; exact HlX1).
  remember (Z.log2 X + 1) as l eqn:Hl.
  rewrite (proj2 (Z.eqb_neq l 0)) by lia. cbv beta iota.
  remember (l - dprec n) as sh eqn:Hsh.
  rewrite (checked_i64 (e + sh)) by lia. cbv beta iota.
  (* [t] is in [[0, 1)] *)
  assert (Ht01 : (0 <= t < 1)%R).
  { destruct sticky; [destruct Ht as [Ht _]; lra | rewrite Ht; lra]. }
  destruct (Z.leb_spec 0 sh) as [Hsh0 | Hsh0].
  + (* [x] has at least [p] bits: [M] is its top [p] bits, and [R] the
       [sh] bits below them. *)
    pose proof (Z.pow_pos_nonneg 2 sh ltac:(lia) Hsh0) as HS0.
    destruct (shr_into_correct n x sh Hx Hsh0) as (Hm & Hml & Hmv).
    rewrite <- HX in Hmv. change (64 * Z.of_nat n) with (dprec n) in Hmv.
    assert (HM : 2 ^ (dprec n - 1) <= X / 2 ^ sh < 2 ^ dprec n).
    { split.
      - apply Z.div_le_lower_bound; [lia |].
        rewrite <- Z.pow_add_r by lia. replace (sh + (dprec n - 1)) with (l - 1) by lia. lia.
      - apply Z.div_lt_upper_bound; [lia |].
        rewrite <- Z.pow_add_r by lia. replace (sh + dprec n) with l by lia. lia. }
    rewrite Z.mod_small in Hmv by lia.
    pose proof (Z.div_mod X (2 ^ sh) ltac:(lia)) as HXd.
    pose proof (Z.mod_pos_bound X (2 ^ sh) HS0) as HRb.
    remember (X / 2 ^ sh) as M eqn:HMd. remember (X mod 2 ^ sh) as R0 eqn:HR0.
    assert (HS : IZR (2 ^ sh) = bpow radix2 sh) by exact (IZR_pow2 sh Hsh0).
    assert (HXr : IZR X = (bpow radix2 sh * IZR M + IZR R0)%R)
      by (rewrite HXd at 1; rewrite plus_IZR, mult_IZR, HS; reflexivity).
    assert (HR : (0 <= IZR R0 /\ IZR R0 + 1 <= bpow radix2 sh)%R).
    { split; [apply IZR_le; lia |]. rewrite <- HS, <- plus_IZR. apply IZR_le. lia. }
    pose proof (bpow_gt_0 radix2 e) as HB.
    (* The low bits of [x] are nonzero exactly when [R] is. *)
    assert (Hlow : ((0 <? sh) && Dyadic.low_bits_nonzero x sh) = false <-> R0 = 0).
    { destruct (Z.ltb_spec 0 sh) as [Hs | Hs]; cbn [andb].
      - pose proof (low_bits_nonzero_correct x sh Hx Hsh0) as Hb.
        rewrite <- HX, <- HR0 in Hb.
        destruct (Dyadic.low_bits_nonzero x sh).
        + split; [discriminate | intros HR00; exfalso; exact (proj1 Hb eq_refl HR00)].
        + split; [| reflexivity]. intros _.
          destruct (Z.eq_dec R0 0) as [HR00 | HR00]; [exact HR00 |].
          discriminate (proj2 Hb HR00).
      - replace sh with 0 in HR0 by lia. rewrite Z.pow_0_r, Z.mod_1_r in HR0.
        split; [intros _; exact HR0 | reflexivity]. }
    (* [v] is [M 2^E] exactly when [R] and [t] are zero. *)
    assert (Hv_eq : ((IZR X + t) * bpow radix2 e = IZR M * bpow radix2 (e + sh))%R <->
                    R0 = 0 /\ t = 0%R).
    { rewrite bpow_plus, HXr. split.
      - intros Heq.
        assert (H1 : ((IZR R0 + t) * bpow radix2 e = 0)%R).
        { replace ((IZR R0 + t) * bpow radix2 e)%R
            with ((bpow radix2 sh * IZR M + IZR R0 + t) * bpow radix2 e
                  - IZR M * (bpow radix2 e * bpow radix2 sh))%R by ring.
          rewrite Heq. ring. }
        destruct (Rmult_integral _ _ H1) as [H2 | H2]; [| lra].
        split; [| lra]. apply eq_IZR. change (IZR 0) with 0%R. lra.
      - intros [HR00 Ht0]. rewrite HR00, Ht0. change (IZR 0) with 0%R. ring. }
    apply (round_tail n neg up (Limbs.shr_into n x sh) M (e + sh)
             ((IZR X + t) * bpow radix2 e)%R).
    * exact Hn.
    * exact Hm.
    * exact Hml.
    * exact Hmv.
    * exact HM.
    * lia.
    * rewrite bpow_plus, HXr. split.
      -- replace (IZR M * (bpow radix2 e * bpow radix2 sh))%R
           with ((bpow radix2 sh * IZR M) * bpow radix2 e)%R by ring.
         apply Rmult_le_compat_r; lra.
      -- replace (IZR (M + 1) * (bpow radix2 e * bpow radix2 sh))%R
           with ((bpow radix2 sh * IZR M + bpow radix2 sh) * bpow radix2 e)%R
           by (rewrite plus_IZR; ring).
         apply Rmult_lt_compat_r; lra.
    * rewrite Hv_eq. destruct sticky; cbn [orb].
      -- split; [discriminate | intros [_ Ht0]; lra].
      -- rewrite Hlow. split; [intros HR00; split; [exact HR00 | exact Ht] | intros [HR00 _]; exact HR00].
  + (* [x] has fewer than [p] bits, so it is not sticky and the shift is
       exact. *)
    assert (Hs0 : sticky = false).
    { destruct sticky; [| reflexivity]. destruct Ht as [_ HXp]. exfalso.
      assert (Hlp : dprec n <= l).
      { destruct (Z.le_gt_cases (dprec n) l) as [H | H]; [exact H |].
        assert (Hle : l <= dprec n - 1) by lia.
        pose proof (Z.pow_le_mono_r 2 l (dprec n - 1) ltac:(lia) Hle). lia. }
      lia. }
    subst sticky. subst t.
    assert (Hnsh : 0 <= - sh) by lia.
    pose proof (Z.pow_pos_nonneg 2 (- sh) ltac:(lia) Hnsh) as HS0.
    destruct (shl_into_correct n x (- sh) Hx Hnsh) as (Hm & Hml & Hmv).
    rewrite <- HX in Hmv. change (64 * Z.of_nat n) with (dprec n) in Hmv.
    assert (HM1 : 2 ^ (dprec n - 1) <= X * 2 ^ (- sh)).
    { replace (dprec n - 1) with ((l - 1) + - sh) by lia.
      rewrite Z.pow_add_r by lia. apply Z.mul_le_mono_nonneg_r; lia. }
    assert (HM2 : X * 2 ^ (- sh) < 2 ^ dprec n).
    { replace (dprec n) with (l + - sh) by lia.
      rewrite Z.pow_add_r by lia. apply Z.mul_lt_mono_pos_r; lia. }
    rewrite Z.mod_small in Hmv by lia.
    rewrite (proj2 (Z.ltb_ge 0 sh)) by lia.
    assert (HS : IZR (2 ^ (- sh)) = bpow radix2 (- sh)) by exact (IZR_pow2 (- sh) Hnsh).
    assert (Hv0 : (IZR (X * 2 ^ (- sh)) * bpow radix2 (e + sh) =
                   (IZR X + 0) * bpow radix2 e)%R).
    { rewrite mult_IZR, HS, bpow_plus.
      assert (Hinv : (bpow radix2 (- sh) * bpow radix2 sh = 1)%R)
        by (rewrite <- bpow_plus, Z.add_opp_diag_l; reflexivity).
      replace (IZR X * bpow radix2 (- sh) * (bpow radix2 e * bpow radix2 sh))%R
        with (IZR X * bpow radix2 e * (bpow radix2 (- sh) * bpow radix2 sh))%R by ring.
      rewrite Hinv. ring. }
    pose proof (bpow_gt_0 radix2 (e + sh)) as HB.
    apply (round_tail n neg up (Limbs.shl_into n x (- sh)) (X * 2 ^ (- sh)) (e + sh)
             ((IZR X + 0) * bpow radix2 e)%R).
    * exact Hn.
    * exact Hm.
    * exact Hml.
    * exact Hmv.
    * lia.
    * lia.
    * rewrite <- Hv0. split; [lra |].
      rewrite plus_IZR, Rmult_plus_distr_r. lra.
    * rewrite Hv0. split; [intros _; reflexivity | intros _; reflexivity].
Qed.
