(** * Bounds on the exponents of enclosures, step by step

    The lemmas of [DyDriver.v] about the operations on enclosures assume
    [encl_small] of their operands. A chain of operations keeps it if each
    step bounds the exponents of its result by those of its operands
    ([encl_le]): the value of a nonzero normalized dyadic number fixes its
    exponent ([exp_of_value]), and the exact result of each operation, if
    it is not 0, has a magnitude within a few bits of those of its
    operands. The step lemmas below are those of [DyDriver.v] for an
    operation that returned: from [op = Some c], the enclosure [c] is
    valid, bounded, and holds every result of the operation on points of
    its operands. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs DyRound DyConv DyOps DyDriver.

Open Scope Z_scope.

(** Both bounds of [a] have exponents in [[-E, E]]. *)
Definition encl_le (E : Z) (a : Dyadic.encl) : Prop :=
  - E <= Dyadic.dy_exp (Dyadic.en_lo a) <= E /\ - E <= Dyadic.dy_exp (Dyadic.en_hi a) <= E.

Lemma encl_le_small : forall E a, E <= 2 ^ 61 -> encl_le E a -> encl_small a.
Proof. intros E a HE (H1 & H2). unfold encl_small, exp_small. lia. Qed.

Lemma encl_le_mono : forall E E' a, E <= E' -> encl_le E a -> encl_le E' a.
Proof. intros E E' a HE (H1 & H2). unfold encl_le. lia. Qed.

(** ** Windows of magnitudes

    [grow_win L U r]: [r] is 0, or its magnitude lies in [[2^L, 2^U]].
    A normalized number of exponent [e] in [[-E, E]] lies in the window
    [[-E + 63, E + 4096]] ([grow_dy_win]); the windows of the operands
    give one of the exact result ([grow_add_win], [grow_mul_win],
    [grow_inv_win]); rounding keeps it, since powers of 2 are in the
    format ([grow_dround_win]); and the window of a normalized number
    bounds its exponent ([grow_exp_win]). *)

Definition grow_win (L U : Z) (r : R) : Prop :=
  r = 0%R \/ (bpow radix2 L <= Rabs r <= bpow radix2 U)%R.

Lemma grow_win_abs : forall L U r, grow_win L U r -> (Rabs r <= bpow radix2 U)%R.
Proof.
  intros L U r [H | H]; [rewrite H, Rabs_R0; apply bpow_ge_0 | apply H].
Qed.

Lemma grow_win_mono :
  forall L U L' U' r, L' <= L -> U <= U' -> grow_win L U r -> grow_win L' U' r.
Proof.
  intros L U L' U' r HL HU [H | [H1 H2]]; [left; exact H | right; split].
  - apply Rle_trans with (2 := H1). apply bpow_le. exact HL.
  - apply Rle_trans with (1 := H2). apply bpow_le. exact HU.
Qed.

Lemma grow_dy_win :
  forall n d E,
  level_ok n -> dy_ok n d -> - E <= Dyadic.dy_exp d <= E ->
  grow_win (- E + 63) (E + 4096) (Dyadic.dy_R d).
Proof.
  intros n d E Hn Hd He. pose proof (dprec_bounds n Hn) as Hp.
  destruct (dy_cases n d Hn Hd) as [(_ & _ & _ & _ & H) | (_ & _ & H1 & H2)].
  - left. exact H.
  - right. split.
    + apply Rle_trans with (2 := H1). apply bpow_le. lia.
    + apply Rlt_le, Rlt_le_trans with (1 := H2). apply bpow_le. lia.
Qed.

(** The magnitude of a nonzero normalized number is in
    [[2^(e + p - 1), 2^(e + p))] for its exponent [e] and the precision
    [p] in [[64, 4096]]. *)
Lemma grow_exp_win :
  forall n d L U,
  level_ok n -> dy_ok n d -> grow_win L U (Dyadic.dy_R d) ->
  Dyadic.dy_exp d = 0 \/ (L - 4096 < Dyadic.dy_exp d /\ Dyadic.dy_exp d <= U - 63).
Proof.
  intros n d L U Hn Hd Hw. pose proof (dprec_bounds n Hn) as Hp.
  destruct (dy_cases n d Hn Hd) as [(_ & _ & _ & He & _) | (_ & _ & H1 & H2)].
  - left. exact He.
  - right. pose proof (bpow_gt_0 radix2 (Dyadic.dy_exp d + dprec n - 1)) as B0.
    destruct Hw as [H0 | [W1 W2]].
    + rewrite H0, Rabs_R0 in H1. lra.
    + assert (A : L < Dyadic.dy_exp d + dprec n) by (apply (lt_bpow radix2); lra).
      assert (B : Dyadic.dy_exp d + dprec n - 1 <= U) by (apply (le_bpow radix2); lra).
      lia.
Qed.

Lemma grow_bpow_format :
  forall n e, level_ok n -> generic_format radix2 (FLX_exp (dprec n)) (bpow radix2 e).
Proof.
  intros n e Hn. pose proof (dprec_bounds n Hn) as Hp.
  pose proof (format_int n false 1 e Hn) as H. cbv iota in H. rewrite Rmult_1_l in H.
  apply H. assert (2 ^ 1 <= 2 ^ dprec n) by (apply Z.pow_le_mono_r; lia).
  rewrite Z.pow_1_r in *. lia.
Qed.

Lemma grow_dround_win :
  forall n up r L U, level_ok n -> grow_win L U r -> grow_win L U (dround n up r).
Proof.
  intros n up r L U Hn [H | [H1 H2]].
  - left. rewrite H. apply dround_0, Hn.
  - right.
    pose proof (grow_bpow_format n L Hn) as FL. pose proof (grow_bpow_format n U Hn) as FU.
    assert (FL' : generic_format radix2 (FLX_exp (dprec n)) (- bpow radix2 L))
      by (apply generic_format_opp; exact FL).
    assert (FU' : generic_format radix2 (FLX_exp (dprec n)) (- bpow radix2 U))
      by (apply generic_format_opp; exact FU).
    pose proof (bpow_gt_0 radix2 L).
    destruct (Rle_or_lt 0 r) as [P | P].
    + rewrite Rabs_pos_eq in H1, H2 by exact P.
      pose proof (dround_le n up _ _ Hn H1) as A. pose proof (dround_le n up _ _ Hn H2) as B.
      rewrite (dround_id n up _ Hn FL) in A. rewrite (dround_id n up _ Hn FU) in B.
      rewrite Rabs_pos_eq by lra. lra.
    + rewrite Rabs_left in H1, H2 by exact P.
      assert (C : (- bpow radix2 U <= r)%R) by lra.
      assert (D : (r <= - bpow radix2 L)%R) by lra.
      pose proof (dround_le n up _ _ Hn C) as A. pose proof (dround_le n up _ _ Hn D) as B.
      rewrite (dround_id n up _ Hn FU') in A. rewrite (dround_id n up _ Hn FL') in B.
      rewrite Rabs_left by lra. lra.
Qed.

(** A bound on the exponent of [d] from the window of the exact value
    that it rounds. *)
Lemma grow_exp_of_win :
  forall n d up r L U E,
  level_ok n -> dy_ok n d -> Dyadic.dy_R d = dround n up r -> grow_win L U r ->
  - E <= L - 4096 -> U - 63 <= E -> 0 <= E -> - E <= Dyadic.dy_exp d <= E.
Proof.
  intros n d up r L U E Hn Hd Hv Hw HL HU HE.
  assert (W : grow_win L U (Dyadic.dy_R d)) by (rewrite Hv; apply grow_dround_win; assumption).
  destruct (grow_exp_win n d L U Hn Hd W); lia.
Qed.

(** A dyadic number of exponent at least [m] is an integer times [2^m]. *)
Lemma grow_int_mult :
  forall d m, m <= Dyadic.dy_exp d -> exists k, Dyadic.dy_R d = (IZR k * bpow radix2 m)%R.
Proof.
  intros d m He. rewrite dy_R_eq.
  assert (B : bpow radix2 (Dyadic.dy_exp d) =
              (IZR (2 ^ (Dyadic.dy_exp d - m)) * bpow radix2 m)%R).
  { rewrite IZR_pow2 by lia. rewrite <- bpow_plus. f_equal. ring. }
  rewrite B.
  destruct (Dyadic.dy_neg d); cbn [cond_Ropp].
  - exists (- (Limbs.val (Dyadic.dy_m d) * 2 ^ (Dyadic.dy_exp d - m))).
    rewrite opp_IZR, mult_IZR. ring.
  - exists (Limbs.val (Dyadic.dy_m d) * 2 ^ (Dyadic.dy_exp d - m)).
    rewrite mult_IZR. ring.
Qed.

(** A nonzero sum of integers times [2^-m] is at least [2^-m] in
    magnitude. *)
Lemma grow_add_win :
  forall m U ku kv u v,
  u = (IZR ku * bpow radix2 (- m))%R -> v = (IZR kv * bpow radix2 (- m))%R ->
  (Rabs u <= bpow radix2 U)%R -> (Rabs v <= bpow radix2 U)%R ->
  grow_win (- m) (U + 1) (u + v).
Proof.
  intros m U ku kv u v Hu Hv Au Av.
  assert (S : (u + v = IZR (ku + kv) * bpow radix2 (- m))%R)
    by (rewrite Hu, Hv, plus_IZR; ring).
  destruct (Z.eq_dec (ku + kv) 0) as [Z0 | Z0].
  - left. rewrite S, Z0. ring.
  - right. split.
    + rewrite S, Rabs_mult, Rabs_Zabs, (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0.
      assert (K : (1 <= IZR (Z.abs (ku + kv)))%R) by (apply IZR_le; lia).
      pose proof (bpow_gt_0 radix2 (- m)). nra.
    + rewrite bpow_plus. change (bpow radix2 1) with 2%R.
      pose proof (Rabs_triang u v). lra.
Qed.

Lemma grow_sum_win :
  forall n u v Eu Ev,
  level_ok n -> dy_ok n u -> dy_ok n v ->
  - Eu <= Dyadic.dy_exp u <= Eu -> - Ev <= Dyadic.dy_exp v <= Ev ->
  grow_win (- Z.max Eu Ev) (Z.max Eu Ev + 4096 + 1) (Dyadic.dy_R u + Dyadic.dy_R v).
Proof.
  intros n u v Eu Ev Hn Hu Hv Hu' Hv'.
  destruct (grow_int_mult u (- Z.max Eu Ev)) as (ku & Ku); [lia |].
  destruct (grow_int_mult v (- Z.max Eu Ev)) as (kv & Kv); [lia |].
  apply (grow_add_win (Z.max Eu Ev) (Z.max Eu Ev + 4096) ku kv); [exact Ku | exact Kv | |].
  - apply (grow_win_abs (- Eu + 63)).
    apply (grow_win_mono (- Eu + 63) (Eu + 4096)); [lia | lia |].
    exact (grow_dy_win n u Eu Hn Hu Hu').
  - apply (grow_win_abs (- Ev + 63)).
    apply (grow_win_mono (- Ev + 63) (Ev + 4096)); [lia | lia |].
    exact (grow_dy_win n v Ev Hn Hv Hv').
Qed.

Lemma grow_mul_win :
  forall La Ua Lb Ub u v,
  grow_win La Ua u -> grow_win Lb Ub v -> grow_win (La + Lb) (Ua + Ub) (u * v).
Proof.
  intros La Ua Lb Ub u v [Hu | [U1 U2]] [Hv | [V1 V2]].
  - left. rewrite Hu. ring.
  - left. rewrite Hu. ring.
  - left. rewrite Hv. ring.
  - right. rewrite Rabs_mult, !bpow_plus.
    pose proof (bpow_gt_0 radix2 La). pose proof (bpow_gt_0 radix2 Lb).
    split; apply Rmult_le_compat; lra.
Qed.

Lemma grow_inv_win :
  forall L U v, v <> 0%R -> grow_win L U v -> grow_win (- U) (- L) (/ v).
Proof.
  intros L U v Hv [H | [H1 H2]]; [contradiction |].
  right. rewrite Rabs_inv, !bpow_opp.
  pose proof (bpow_gt_0 radix2 L).
  split; apply Rinv_le_contravar; lra.
Qed.

Lemma grow_min_win :
  forall L U x y, grow_win L U x -> grow_win L U y -> grow_win L U (Rmin x y).
Proof. intros L U x y Hx Hy. unfold Rmin. destruct (Rle_dec x y); assumption. Qed.

Lemma grow_max_win :
  forall L U x y, grow_win L U x -> grow_win L U y -> grow_win L U (Rmax x y).
Proof. intros L U x y Hx Hy. unfold Rmax. destruct (Rle_dec x y); assumption. Qed.

Lemma grow_int_win : forall k, 0 <= k < 2 ^ 64 -> grow_win 0 64 (IZR k).
Proof.
  intros k Hk. destruct (Z.eq_dec k 0) as [-> | K]; [left; reflexivity | right].
  rewrite Rabs_pos_eq by (apply IZR_le; lia).
  rewrite <- (IZR_pow2 64) by lia. change (bpow radix2 0) with 1%R.
  split; apply IZR_le; lia.
Qed.

(** A finite [f64] is 0 or at least [2^-1074] and below [2^1024] in
    magnitude. *)
Lemma grow_f64_win : forall x : f64, grow_win (-1074) 1024 (B2R x).
Proof.
  intros x. destruct (Req_dec (B2R x) 0) as [H | H]; [left; exact H | right].
  split; [| apply Rlt_le, abs_B2R_lt_emax].
  assert (S : is_finite_strict x = true)
    by (destruct x; try reflexivity; exfalso; apply H; reflexivity).
  exact (abs_B2R_ge_emin _ _ x S).
Qed.

Lemma grow_checked_i : forall w z e, checked_i w z = Some e -> e = z.
Proof.
  intros w z e H. unfold checked_i in H.
  destruct ((- 2 ^ (w - 1) <=? z) && (z <? 2 ^ (w - 1)))%bool; [| discriminate].
  injection H as <-. reflexivity.
Qed.

(** [shl] keeps 0 and adds [k] to the exponent of any other number. *)
Lemma grow_shl_exp :
  forall n x k d,
  Dyadic.shl n x k = Some d ->
  Dyadic.dy_exp d = Dyadic.dy_exp x \/ Dyadic.dy_exp d = Dyadic.dy_exp x + k.
Proof.
  intros n x k d H. unfold Dyadic.shl in H.
  destruct (Dyadic.is_zero n x).
  - injection H as <-. left. reflexivity.
  - destruct (checked_i 64 (Dyadic.dy_exp x + k)) as [e |] eqn:C; [| discriminate].
    apply grow_checked_i in C. injection H as <-. right. exact C.
Qed.

(** ** The steps *)

Lemma from_f64_step :
  forall n x d,
  level_ok n -> Dyadic.from_f64 n x = Some d ->
  dy_ok n d /\ - 2 ^ 13 <= Dyadic.dy_exp d <= 2 ^ 13 /\ Dyadic.dy_R d = B2R x /\
  is_finite x = true.
Proof.
  intros n x d Hn H.
  assert (F : is_finite x = true).
  { destruct (is_finite x) eqn:F; [reflexivity |].
    unfold Dyadic.from_f64 in H. rewrite F in H. cbn [negb] in H. discriminate. }
  destruct (from_f64_correct n x Hn F) as (d' & E & Ok & _ & V).
  rewrite H in E. injection E as <-.
  split; [exact Ok |]. split; [| split; [exact V | exact F]].
  pose proof (grow_exp_win n d (-1074) 1024 Hn Ok) as W.
  rewrite V in W. specialize (W (grow_f64_win x)). lia.
Qed.

Lemma point_step :
  forall n x c,
  level_ok n -> Dyadic.encl_point n x = Some c ->
  encl_ok n c /\ encl_le (2 ^ 13) c /\ lo_R c = B2R x /\ hi_R c = B2R x /\
  is_finite x = true.
Proof.
  intros n x c Hn H. unfold Dyadic.encl_point in H.
  destruct (Dyadic.from_f64 n x) as [d |] eqn:E; [| discriminate].
  injection H as <-.
  destruct (from_f64_step n x d Hn E) as (Ok & He & V & F).
  unfold encl_ok, encl_le, lo_R, hi_R; cbn [Dyadic.en_lo Dyadic.en_hi].
  split; [split; [exact Ok | split; [exact Ok | apply Rle_refl]] |].
  split; [split; exact He |].
  split; [exact V | split; [exact V | exact F]].
Qed.

Lemma neg_step :
  forall n a E,
  level_ok n -> encl_ok n a -> encl_le E a ->
  encl_ok n (Dyadic.encl_neg n a) /\ encl_le E (Dyadic.encl_neg n a) /\
  forall x, encl_has a x -> encl_has (Dyadic.encl_neg n a) (- x).
Proof.
  intros n a E Hn (Hla & Hha & Ha) (La & Lh).
  destruct (neg_correct n (Dyadic.en_lo a) Hn Hla) as (Oklo & Vlo & Xlo).
  destruct (neg_correct n (Dyadic.en_hi a) Hn Hha) as (Okhi & Vhi & Xhi).
  unfold Dyadic.encl_neg, encl_ok, encl_le, encl_has; cbn [Dyadic.en_lo Dyadic.en_hi].
  rewrite Vlo, Vhi, Xlo, Xhi.
  split; [split; [exact Okhi | split; [exact Oklo | lra]] |].
  split; [split; assumption |].
  intros x Hx. lra.
Qed.

Lemma add_step :
  forall n a b c Ea Eb,
  level_ok n -> encl_ok n a -> encl_ok n b -> encl_le Ea a -> encl_le Eb b ->
  0 <= Ea <= 2 ^ 60 -> 0 <= Eb <= 2 ^ 60 ->
  Dyadic.encl_add n a b = Some c ->
  encl_ok n c /\ encl_le (Z.max Ea Eb + 2 ^ 13) c /\
  forall x y, encl_has a x -> encl_has b y -> encl_has c (x + y).
Proof.
  intros n a b c Ea Eb Hn Ha Hb La Lb HEa HEb E.
  assert (Sa : encl_small a) by (apply (encl_le_small Ea); [lia | exact La]).
  assert (Sb : encl_small b) by (apply (encl_le_small Eb); [lia | exact Lb]).
  destruct (encl_add_correct n a b Hn Ha Hb Sa Sb) as (c' & E' & Okc & Vlo & Vhi & Hc).
  rewrite E in E'. injection E' as <-.
  split; [exact Okc |]. split; [| exact Hc].
  destruct Ha as (Hla & Hha & _). destruct Hb as (Hlb & Hhb & _).
  destruct Okc as (Hlc & Hhc & _). destruct La as (La1 & La2). destruct Lb as (Lb1 & Lb2).
  unfold lo_R, hi_R in Vlo, Vhi. split.
  - apply (grow_exp_of_win n _ false _ (- Z.max Ea Eb) (Z.max Ea Eb + 4096 + 1) _ Hn Hlc Vlo);
      [apply (grow_sum_win n); assumption | lia | lia | lia].
  - apply (grow_exp_of_win n _ true _ (- Z.max Ea Eb) (Z.max Ea Eb + 4096 + 1) _ Hn Hhc Vhi);
      [apply (grow_sum_win n); assumption | lia | lia | lia].
Qed.

Lemma sub_step :
  forall n a b c Ea Eb,
  level_ok n -> encl_ok n a -> encl_ok n b -> encl_le Ea a -> encl_le Eb b ->
  0 <= Ea <= 2 ^ 60 -> 0 <= Eb <= 2 ^ 60 ->
  Dyadic.encl_sub n a b = Some c ->
  encl_ok n c /\ encl_le (Z.max Ea Eb + 2 ^ 13) c /\
  forall x y, encl_has a x -> encl_has b y -> encl_has c (x - y).
Proof.
  intros n a b c Ea Eb Hn Ha Hb La Lb HEa HEb E.
  assert (Sa : encl_small a) by (apply (encl_le_small Ea); [lia | exact La]).
  assert (Sb : encl_small b) by (apply (encl_le_small Eb); [lia | exact Lb]).
  destruct (encl_sub_correct n a b Hn Ha Hb Sa Sb) as (c' & E' & Okc & Vlo & Vhi & Hc).
  rewrite E in E'. injection E' as <-.
  split; [exact Okc |]. split; [| exact Hc].
  destruct Ha as (Hla & Hha & _). destruct Hb as (Hlb & Hhb & _).
  destruct Okc as (Hlc & Hhc & _). destruct La as (La1 & La2). destruct Lb as (Lb1 & Lb2).
  (* [x - y] is [x + (- y)], and [neg] keeps the exponent. *)
  destruct (neg_correct n (Dyadic.en_lo b) Hn Hlb) as (Nlo & Wlo & Xlo).
  destruct (neg_correct n (Dyadic.en_hi b) Hn Hhb) as (Nhi & Whi & Xhi).
  unfold lo_R, hi_R in Vlo, Vhi. unfold Rminus in Vlo, Vhi.
  rewrite <- Wlo in Vhi. rewrite <- Whi in Vlo. split.
  - apply (grow_exp_of_win n _ false _ (- Z.max Ea Eb) (Z.max Ea Eb + 4096 + 1) _ Hn Hlc Vlo);
      [apply (grow_sum_win n); try assumption; rewrite Xhi; assumption | lia | lia | lia].
  - apply (grow_exp_of_win n _ true _ (- Z.max Ea Eb) (Z.max Ea Eb + 4096 + 1) _ Hn Hhc Vhi);
      [apply (grow_sum_win n); try assumption; rewrite Xlo; assumption | lia | lia | lia].
Qed.

Lemma mul_step :
  forall n a b c Ea Eb,
  level_ok n -> encl_ok n a -> encl_ok n b -> encl_le Ea a -> encl_le Eb b ->
  0 <= Ea <= 2 ^ 60 -> 0 <= Eb <= 2 ^ 60 ->
  Dyadic.encl_mul n a b = Some c ->
  encl_ok n c /\ encl_le (Ea + Eb + 2 ^ 13) c /\
  forall x y, encl_has a x -> encl_has b y -> encl_has c (x * y).
Proof.
  intros n a b c Ea Eb Hn Ha Hb La Lb HEa HEb E.
  assert (Sa : encl_small a) by (apply (encl_le_small Ea); [lia | exact La]).
  assert (Sb : encl_small b) by (apply (encl_le_small Eb); [lia | exact Lb]).
  destruct (encl_mul_correct n a b Hn Ha Hb Sa Sb) as (c' & E' & Okc & Vlo & Vhi & Hc).
  rewrite E in E'. injection E' as <-.
  split; [exact Okc |]. split; [| exact Hc].
  destruct Ha as (Hla & Hha & _). destruct Hb as (Hlb & Hhb & _).
  destruct Okc as (Hlc & Hhc & _). destruct La as (La1 & La2). destruct Lb as (Lb1 & Lb2).
  pose proof (grow_dy_win n _ Ea Hn Hla La1) as Wla.
  pose proof (grow_dy_win n _ Ea Hn Hha La2) as Wha.
  pose proof (grow_dy_win n _ Eb Hn Hlb Lb1) as Wlb.
  pose proof (grow_dy_win n _ Eb Hn Hhb Lb2) as Whb.
  pose proof (grow_mul_win _ _ _ _ _ _ Wla Wlb) as W1.
  pose proof (grow_mul_win _ _ _ _ _ _ Wla Whb) as W2.
  pose proof (grow_mul_win _ _ _ _ _ _ Wha Wlb) as W3.
  pose proof (grow_mul_win _ _ _ _ _ _ Wha Whb) as W4.
  unfold lo_R, hi_R in Vlo, Vhi. split.
  - apply (grow_exp_of_win n _ false _ (- Ea + 63 + (- Eb + 63)) (Ea + 4096 + (Eb + 4096)) _
             Hn Hlc Vlo);
      [repeat apply grow_min_win; assumption | lia | lia | lia].
  - apply (grow_exp_of_win n _ true _ (- Ea + 63 + (- Eb + 63)) (Ea + 4096 + (Eb + 4096)) _
             Hn Hhc Vhi);
      [repeat apply grow_max_win; assumption | lia | lia | lia].
Qed.

Lemma div_step :
  forall n a b c Ea Eb,
  level_ok n -> encl_ok n a -> encl_ok n b -> encl_le Ea a -> encl_le Eb b ->
  0 <= Ea <= 2 ^ 60 -> 0 <= Eb <= 2 ^ 60 ->
  Dyadic.encl_div n a b = Some c ->
  encl_ok n c /\ encl_le (Ea + Eb + 2 ^ 13) c /\
  forall x y, encl_has a x -> encl_has b y -> encl_has c (x / y).
Proof.
  intros n a b c Ea Eb Hn Ha Hb La Lb HEa HEb E.
  assert (Sa : encl_small a) by (apply (encl_le_small Ea); [lia | exact La]).
  assert (Sb : encl_small b) by (apply (encl_le_small Eb); [lia | exact Lb]).
  (* The [assert!] passed, so [b] does not hold 0. *)
  assert (H0 : (0 < lo_R b \/ hi_R b < 0)%R).
  { destruct (Rlt_or_le 0 (lo_R b)) as [P | P]; [left; exact P |].
    destruct (Rlt_or_le (hi_R b) 0) as [Q | Q]; [right; exact Q |].
    rewrite (encl_div_zero n a b Hn Hb (conj P Q)) in E. discriminate. }
  destruct (encl_div_correct n a b Hn Ha Hb Sa Sb H0) as (c' & E' & Okc & Vlo & Vhi & Hc).
  rewrite E in E'. injection E' as <-.
  split; [exact Okc |]. split; [| exact Hc].
  destruct Ha as (Hla & Hha & _). destruct Hb as (Hlb & Hhb & Hb).
  destruct Okc as (Hlc & Hhc & _). destruct La as (La1 & La2). destruct Lb as (Lb1 & Lb2).
  unfold lo_R, hi_R in H0.
  assert (Nl : Dyadic.dy_R (Dyadic.en_lo b) <> 0%R) by lra.
  assert (Nh : Dyadic.dy_R (Dyadic.en_hi b) <> 0%R) by lra.
  pose proof (grow_dy_win n _ Ea Hn Hla La1) as Wla.
  pose proof (grow_dy_win n _ Ea Hn Hha La2) as Wha.
  pose proof (grow_inv_win _ _ _ Nl (grow_dy_win n _ Eb Hn Hlb Lb1)) as Wlb.
  pose proof (grow_inv_win _ _ _ Nh (grow_dy_win n _ Eb Hn Hhb Lb2)) as Whb.
  pose proof (grow_mul_win _ _ _ _ _ _ Wla Wlb) as W1.
  pose proof (grow_mul_win _ _ _ _ _ _ Wla Whb) as W2.
  pose proof (grow_mul_win _ _ _ _ _ _ Wha Wlb) as W3.
  pose proof (grow_mul_win _ _ _ _ _ _ Wha Whb) as W4.
  unfold lo_R, hi_R in Vlo, Vhi. unfold Rdiv in Vlo, Vhi. split.
  - apply (grow_exp_of_win n _ false _ (- Ea + 63 + - (Eb + 4096)) (Ea + 4096 + - (- Eb + 63)) _
             Hn Hlc Vlo);
      [repeat apply grow_min_win; assumption | lia | lia | lia].
  - apply (grow_exp_of_win n _ true _ (- Ea + 63 + - (Eb + 4096)) (Ea + 4096 + - (- Eb + 63)) _
             Hn Hhc Vhi);
      [repeat apply grow_max_win; assumption | lia | lia | lia].
Qed.

Lemma mul_u64_step :
  forall n a k c E,
  level_ok n -> encl_ok n a -> encl_le E a -> 0 <= E <= 2 ^ 60 -> 0 <= k < 2 ^ 64 ->
  Dyadic.encl_mul_u64 n a k = Some c ->
  encl_ok n c /\ encl_le (E + 2 ^ 13) c /\
  forall x, encl_has a x -> encl_has c (x * IZR k).
Proof.
  intros n a k c E Hn Ha La HE Hk H.
  assert (Sa : encl_small a) by (apply (encl_le_small E); [lia | exact La]).
  destruct (encl_mul_u64_correct n a k Hn Ha Sa Hk) as (c' & E' & Okc & Vlo & Vhi & Hc).
  rewrite H in E'. injection E' as <-.
  split; [exact Okc |]. split; [| exact Hc].
  destruct Ha as (Hla & Hha & _). destruct Okc as (Hlc & Hhc & _). destruct La as (La1 & La2).
  pose proof (grow_int_win k Hk) as Wk.
  pose proof (grow_mul_win _ _ _ _ _ _ (grow_dy_win n _ E Hn Hla La1) Wk) as W1.
  pose proof (grow_mul_win _ _ _ _ _ _ (grow_dy_win n _ E Hn Hha La2) Wk) as W2.
  unfold lo_R, hi_R in Vlo, Vhi. split.
  - apply (grow_exp_of_win n _ false _ _ _ _ Hn Hlc Vlo W1); lia.
  - apply (grow_exp_of_win n _ true _ _ _ _ Hn Hhc Vhi W2); lia.
Qed.

Lemma div_u64_step :
  forall n a k c E,
  level_ok n -> encl_ok n a -> encl_le E a -> 0 <= E <= 2 ^ 60 -> 0 < k < 2 ^ 64 ->
  Dyadic.encl_div_u64 n a k = Some c ->
  encl_ok n c /\ encl_le (E + 2 ^ 13) c /\
  forall x, encl_has a x -> encl_has c (x / IZR k).
Proof.
  intros n a k c E Hn Ha La HE Hk H.
  assert (Sa : encl_small a) by (apply (encl_le_small E); [lia | exact La]).
  destruct (encl_div_u64_correct n a k Hn Ha Sa Hk) as (c' & E' & Okc & Vlo & Vhi & Hc).
  rewrite H in E'. injection E' as <-.
  split; [exact Okc |]. split; [| exact Hc].
  destruct Ha as (Hla & Hha & _). destruct Okc as (Hlc & Hhc & _). destruct La as (La1 & La2).
  assert (Hk' : 0 <= k < 2 ^ 64) by lia.
  assert (Nk : IZR k <> 0%R) by (apply not_0_IZR; lia).
  pose proof (grow_inv_win _ _ _ Nk (grow_int_win k Hk')) as Wk.
  pose proof (grow_mul_win _ _ _ _ _ _ (grow_dy_win n _ E Hn Hla La1) Wk) as W1.
  pose proof (grow_mul_win _ _ _ _ _ _ (grow_dy_win n _ E Hn Hha La2) Wk) as W2.
  unfold lo_R, hi_R in Vlo, Vhi. unfold Rdiv in Vlo, Vhi. split.
  - apply (grow_exp_of_win n _ false _ _ _ _ Hn Hlc Vlo W1); lia.
  - apply (grow_exp_of_win n _ true _ _ _ _ Hn Hhc Vhi W2); lia.
Qed.

Lemma shl_step :
  forall n a k c E,
  level_ok n -> encl_ok n a -> encl_le E a -> 0 <= E <= 2 ^ 60 -> - 2 ^ 20 <= k <= 2 ^ 20 ->
  Dyadic.encl_shl n a k = Some c ->
  encl_ok n c /\ encl_le (E + Z.abs k) c /\
  forall x, encl_has a x -> encl_has c (x * bpow radix2 k).
Proof.
  intros n a k c E Hn Ha La HE Hk H.
  assert (Sa : encl_small a) by (apply (encl_le_small E); [lia | exact La]).
  assert (Hk' : - 2 ^ 62 <= k <= 2 ^ 62) by lia.
  destruct (encl_shl_correct n a k Hn Ha Sa Hk') as (c' & E' & Okc & _ & _ & Hc).
  rewrite H in E'. injection E' as <-.
  split; [exact Okc |]. split; [| exact Hc].
  unfold Dyadic.encl_shl in H.
  destruct (Dyadic.shl n (Dyadic.en_lo a) k) as [lo |] eqn:Elo; [| discriminate].
  destruct (Dyadic.shl n (Dyadic.en_hi a) k) as [hi |] eqn:Ehi; [| discriminate].
  injection H as <-.
  pose proof (grow_shl_exp n _ k lo Elo). pose proof (grow_shl_exp n _ k hi Ehi).
  unfold encl_le in *; cbn [Dyadic.en_lo Dyadic.en_hi]. lia.
Qed.
