(** * The operations of the dyadic kernel are correctly rounded

    Each operation of [Dyadic] in [Model.v] returns the exact result
    rounded toward +inf if [up] and toward -inf otherwise at [64 n] bits
    ([dround]), and never panics for normalized operands with exponents
    of [exp_small], except where its Rust function says it panics: a
    division by zero and the square root of a negative number. Each
    proof shows that the window of limbs that the function passes to
    [round] holds the exact result, and applies [round_correct]. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core.
From Inari Require Import Model Limbs Knuth DyRound DyIsqrt.

Open Scope Z_scope.
Open Scope list_scope.

(** ** Helpers *)

Lemma IZR_pow2 : forall k, 0 <= k -> IZR (2 ^ k) = bpow radix2 k.
Proof. intros k Hk. rewrite <- IZR_Zpower by exact Hk. reflexivity. Qed.

Lemma pow2_add : forall a b, 0 <= a -> 0 <= b -> 2 ^ (a + b) = 2 ^ a * 2 ^ b.
Proof. intros a b Ha Hb. apply Z.pow_add_r; lia. Qed.

Lemma pow2_pos : forall a, 0 <= a -> 0 < 2 ^ a.
Proof. intros a Ha. apply Z.pow_pos_nonneg; lia. Qed.

Lemma dy_R_eq :
  forall x,
  Dyadic.dy_R x =
  cond_Ropp (Dyadic.dy_neg x) (IZR (Limbs.val (Dyadic.dy_m x)) * bpow radix2 (Dyadic.dy_exp x)).
Proof. intros x. unfold Dyadic.dy_R, cond_Ropp. destruct (Dyadic.dy_neg x); reflexivity. Qed.

Lemma checked_i64 : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> checked_i 64 z = Some z.
Proof.
  intros z Hz. unfold checked_i.
  replace (64 - 1) with 63 by reflexivity.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  reflexivity.
Qed.

Lemma dround_0 : forall n up, level_ok n -> dround n up 0 = 0%R.
Proof. intros n up Hn. apply dround_id; [exact Hn | apply generic_format_0]. Qed.

Lemma nat_bits_bounds : forall v k, 0 <= k -> 0 <= v < 2 ^ k -> 0 <= nat_bits v <= k.
Proof.
  intros v k Hk Hv. unfold nat_bits.
  destruct (Z.eqb_spec v 0) as [H0 | H0]; [lia |].
  assert (Hl : Z.log2 v < k) by (apply Z.log2_lt_pow2; lia).
  pose proof (Z.log2_nonneg v). lia.
Qed.

Lemma existsb_nonzero :
  forall r, limbs_ok r -> existsb (fun l => negb (l =? 0)) r = negb (Limbs.val r =? 0).
Proof.
  induction r as [| a r IH]; intros Hr; [reflexivity |].
  apply Forall_cons_iff in Hr. destruct Hr as (Ha & Hr).
  cbn [existsb Limbs.val]. rewrite (IH Hr).
  pose proof (val_bounds r Hr) as Hb.
  destruct (Z.eqb_spec a 0) as [Ha0 | Ha0];
    destruct (Z.eqb_spec (Limbs.val r) 0) as [Hr0 | Hr0];
    destruct (Z.eqb_spec (a + 2 ^ 64 * Limbs.val r) 0) as [Hs | Hs];
    cbn [negb orb]; try reflexivity; lia.
Qed.

(** [low_bits_nonzero x k] tests the bits of [x] below bit [k]. *)
Lemma low_bits_nonzero_correct :
  forall x k,
  limbs_ok x -> 0 <= k ->
  Dyadic.low_bits_nonzero x k = negb (Limbs.val x mod 2 ^ k =? 0).
Proof.
  intros x k Hx Hk. unfold Dyadic.low_bits_nonzero.
  set (q := k / 64). set (r := k mod 64).
  assert (Hq : 0 <= q) by (apply Z.div_pos; lia).
  assert (Hr : 0 <= r < 64) by (apply Z.mod_pos_bound; lia).
  assert (Hkqr : k = 64 * q + r) by (apply Z.div_mod; lia).
  assert (Hqn : Z.of_nat (Z.to_nat q) = q) by (apply Z2Nat.id; exact Hq).
  rewrite (existsb_nonzero _ (limbs_ok_firstn _ _ Hx)), (val_firstn _ _ Hx), Hqn.
  rewrite Z.shiftl_1_l.
  replace (2 ^ r - 1) with (Z.ones r) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia.
  rewrite (limb_val _ _ Hx), Hqn.
  set (V := Limbs.val x).
  assert (HV : 0 <= V) by (apply (val_bounds x Hx)).
  assert (HQ : 0 < 2 ^ (64 * q)) by (apply pow2_pos; lia).
  assert (HR : 0 < 2 ^ r) by (apply pow2_pos; lia).
  (* [V mod 2^k] is [V mod 2^(64 q)] plus [2^(64 q)] times the bits [64 q .. k] *)
  assert (Hsplit : V mod 2 ^ k = V mod 2 ^ (64 * q) + 2 ^ (64 * q) * ((V / 2 ^ (64 * q)) mod 2 ^ r)).
  { rewrite Hkqr, pow2_add by lia. apply Z.rem_mul_r; lia. }
  assert (Hlimb : V / 2 ^ (64 * q) mod 2 ^ 64 mod 2 ^ r = V / 2 ^ (64 * q) mod 2 ^ r).
  { symmetry. apply Znumtheory.Zmod_div_mod; [lia | lia |].
    exists (2 ^ (64 - r)). rewrite <- pow2_add by lia. f_equal. lia. }
  rewrite Hlimb, Hsplit.
  pose proof (Z.mod_pos_bound V (2 ^ (64 * q)) HQ).
  pose proof (Z.mod_pos_bound (V / 2 ^ (64 * q)) (2 ^ r) HR).
  destruct (Z.eqb_spec (V mod 2 ^ (64 * q)) 0);
    destruct (Z.eqb_spec (V / 2 ^ (64 * q) mod 2 ^ r) 0);
    destruct (Z.eqb_spec (V mod 2 ^ (64 * q) + 2 ^ (64 * q) * (V / 2 ^ (64 * q) mod 2 ^ r)) 0);
    cbn [negb orb]; try reflexivity; nia.
Qed.

(** The facts about a nonzero normalized number. *)
Lemma dy_ok_nz :
  forall n x,
  level_ok n -> dy_ok n x -> Dyadic.is_zero n x = false ->
  limbs_ok (Dyadic.dy_m x) /\ length (Dyadic.dy_m x) = n /\
  - 2 ^ 63 <= Dyadic.dy_exp x < 2 ^ 63 /\
  2 ^ (dprec n - 1) <= Limbs.val (Dyadic.dy_m x) < 2 ^ (dprec n).
Proof.
  intros n x Hn Hx Hz.
  pose proof Hx as (H1 & H2 & H3 & H4).
  pose proof (val_bounds _ H1) as Hb. rewrite H2 in Hb.
  destruct H4 as [(H4 & H5 & H6) | H4].
  - exfalso. assert (HR : Dyadic.dy_R x = 0%R).
    { rewrite dy_R_eq, H4, Rmult_0_l. destruct (Dyadic.dy_neg x); cbn [cond_Ropp]; lra. }
    apply (is_zero_correct n x Hn Hx) in HR. congruence.
  - unfold dprec in *. split; [exact H1 | lia].
Qed.

Lemma is_zero_R : forall n x, level_ok n -> dy_ok n x -> Dyadic.is_zero n x = true -> Dyadic.dy_R x = 0%R.
Proof. intros n x Hn Hx Hz. apply (is_zero_correct n x Hn Hx). exact Hz. Qed.

Lemma dy_zero_result :
  forall n up r,
  level_ok n -> r = 0%R ->
  exists d,
  Some (Dyadic.dy_zero n) = Some d /\ dy_ok n d /\ Dyadic.dy_R d = dround n up r.
Proof.
  intros n up r Hn Hr. exists (Dyadic.dy_zero n).
  destruct (dy_zero_ok n) as (H1 & H2 & _).
  split; [reflexivity | split; [exact H1 |]].
  rewrite H2, Hr, dround_0 by exact Hn. reflexivity.
Qed.

Lemma IZR_div_lt_1 : forall a b, 0 <= a < b -> (IZR a / IZR b < 1)%R.
Proof.
  intros a b Hab.
  assert (Hb : (0 < IZR b)%R) by (apply IZR_lt; lia).
  assert (Hlt : (IZR a < IZR b)%R) by (apply IZR_lt; lia).
  apply Rmult_lt_reg_r with (IZR b); [exact Hb |].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l by lra. exact Hlt.
Qed.

(** [round_correct] for the windows of the operations, which have at most
    [2 n + 2] limbs, and exponents [e] far from the ends of [i64]. *)
Lemma round_apply :
  forall (n : nat) (neg : bool) (x : list Z) (e : Z) (sticky up : bool) (t r : R),
  level_ok n -> limbs_ok x -> (length x <= 2 * n + 2)%nat ->
  (if sticky then (0 < t < 1)%R /\ 2 ^ (dprec n - 1) <= Limbs.val x else t = 0%R) ->
  - 2 ^ 63 + 2 ^ 20 <= e <= 2 ^ 63 - 2 ^ 20 ->
  r = cond_Ropp neg ((IZR (Limbs.val x) + t) * bpow radix2 e) ->
  exists d,
  Dyadic.round n neg x e sticky up = Some d /\ dy_ok n d /\ Dyadic.dy_R d = dround n up r.
Proof.
  intros n neg x e sticky up t r Hn Hx Hl Hs He Hr. subst r.
  apply round_correct; [exact Hn | exact Hx | exact Hs |].
  right. pose proof Hn as Hn'. unfold level_ok in Hn'. unfold dprec.
  pose proof (val_bounds x Hx) as Hb.
  assert (Hk : 0 <= 64 * Z.of_nat (length x)) by lia.
  pose proof (nat_bits_bounds (Limbs.val x) _ Hk Hb) as Hnb.
  lia.
Qed.

(** ** Multiplications *)

Lemma mul_correct :
  forall n a b up,
  level_ok n -> dy_ok n a -> dy_ok n b -> exp_small a -> exp_small b ->
  exists d,
  Dyadic.mul n a b up = Some d /\ dy_ok n d /\
  Dyadic.dy_R d = dround n up (Dyadic.dy_R a * Dyadic.dy_R b).
Proof.
  intros n a b up Hn Ha Hb Hea Heb.
  unfold Dyadic.mul.
  destruct (Dyadic.is_zero n a) eqn:Za; cbn [orb].
  { apply dy_zero_result; [exact Hn |]. rewrite (is_zero_R n a Hn Ha Za). ring. }
  destruct (Dyadic.is_zero n b) eqn:Zb.
  { apply dy_zero_result; [exact Hn |]. rewrite (is_zero_R n b Hn Hb Zb). ring. }
  destruct (dy_ok_nz n a Hn Ha Za) as (Ha1 & Ha2 & Ha3 & Ha4).
  destruct (dy_ok_nz n b Hn Hb Zb) as (Hb1 & Hb2 & Hb3 & Hb4).
  unfold exp_small in Hea, Heb. pose proof Hn as Hn'. unfold level_ok in Hn'.
  rewrite (checked_i64 (Dyadic.dy_exp a + Dyadic.dy_exp b)) by lia.
  destruct (mul_into_correct (Dyadic.dy_m a) (Dyadic.dy_m b) Ha1 Hb1) as (w & Hw1 & Hw2 & Hw3 & Hw4).
  replace (2 * n)%nat with (length (Dyadic.dy_m a) + length (Dyadic.dy_m b))%nat by lia.
  rewrite Hw1.
  apply round_apply with (t := 0%R); [exact Hn | exact Hw2 | lia | reflexivity | lia |].
  rewrite !dy_R_eq, Hw4, mult_IZR, bpow_plus.
  destruct (Dyadic.dy_neg a), (Dyadic.dy_neg b); cbn [negb Bool.eqb cond_Ropp]; ring.
Qed.

Lemma mul_u64_correct :
  forall n a k up,
  level_ok n -> dy_ok n a -> exp_small a -> 0 <= k < 2 ^ 64 ->
  exists d,
  Dyadic.mul_u64 n a k up = Some d /\ dy_ok n d /\
  Dyadic.dy_R d = dround n up (Dyadic.dy_R a * IZR k).
Proof.
  intros n a k up Hn Ha Hea Hk.
  unfold Dyadic.mul_u64.
  destruct (Dyadic.is_zero n a) eqn:Za; cbn [orb].
  { apply dy_zero_result; [exact Hn |]. rewrite (is_zero_R n a Hn Ha Za). ring. }
  destruct (Z.eqb_spec k 0) as [Hk0 | Hk0].
  { apply dy_zero_result; [exact Hn |]. rewrite Hk0. ring. }
  destruct (dy_ok_nz n a Hn Ha Za) as (Ha1 & Ha2 & Ha3 & Ha4).
  unfold exp_small in Hea. pose proof Hn as Hn'. unfold level_ok in Hn'.
  assert (H0 : 0 <= 0 < 2 ^ 64) by lia.
  destruct (mul_add_limb_correct (Dyadic.dy_m a) k 0 Ha1 Hk H0)
    as (s & c & Hs1 & Hs2 & Hs3 & Hc & Hs4).
  rewrite Hs1.
  assert (Hw : limbs_ok (s ++ c :: nil)).
  { apply limbs_ok_app; [exact Hs2 | constructor; [lia | constructor]]. }
  assert (Hv : Limbs.val (s ++ c :: nil) = Limbs.val (Dyadic.dy_m a) * k).
  { rewrite val_app, Hs3. cbn [Limbs.val]. nia. }
  apply round_apply with (t := 0%R);
    [exact Hn | exact Hw | rewrite length_app; cbn [length]; lia | reflexivity | lia |].
  rewrite dy_R_eq, Hv, mult_IZR.
  destruct (Dyadic.dy_neg a); cbn [cond_Ropp]; ring.
Qed.

(** ** Divisions *)

Lemma div_u64_correct :
  forall n a k up,
  level_ok n -> dy_ok n a -> exp_small a -> 0 < k < 2 ^ 64 ->
  exists d,
  Dyadic.div_u64 n a k up = Some d /\ dy_ok n d /\
  Dyadic.dy_R d = dround n up (Dyadic.dy_R a / IZR k).
Proof.
    intros n a k up Hn Ha Hea Hk.
  unfold Dyadic.div_u64.
  rewrite (proj2 (Z.eqb_neq k 0)) by lia.
  destruct (Dyadic.is_zero n a) eqn:Za.
  { apply dy_zero_result; [exact Hn |]. rewrite (is_zero_R n a Hn Ha Za). unfold Rdiv. ring. }
  destruct (dy_ok_nz n a Hn Ha Za) as (Ha1 & Ha2 & Ha3 & Ha4).
  unfold exp_small in Hea. pose proof Hn as Hn'. unfold level_ok in Hn'.
  rewrite (checked_i64 (Dyadic.dy_exp a - 64)) by lia.
  assert (Hx : limbs_ok (0 :: Dyadic.dy_m a)) by (constructor; [lia | exact Ha1]).
  destruct (div_rem_limb_correct (0 :: Dyadic.dy_m a) k Hx Hk) as (q & r & Hq1 & Hq2 & Hq3 & Hq4 & Hr).
  rewrite Hq1.
  cbn [Limbs.val length] in Hq3, Hq4, Hr.
  set (ma := Limbs.val (Dyadic.dy_m a)) in *.
  set (X := 0 + 2 ^ 64 * ma) in *.
  assert (HXd : X = k * Limbs.val q + r) by (rewrite Hq4, Hr; apply Z.div_mod; lia).
  assert (Hr0 : 0 <= r < k) by (rewrite Hr; apply Z.mod_pos_bound; lia).
  assert (HkR : IZR k <> 0%R) by (apply not_0_IZR; lia).
  apply round_apply with (t := (IZR r / IZR k)%R);
    [exact Hn | exact Hq2 | lia | | lia |].
  - destruct (Z.eqb_spec r 0) as [Hr1 | Hr1]; cbn [negb].
    + rewrite Hr1. unfold Rdiv. ring.
    + split.
      * split.
        -- apply Rdiv_lt_0_compat; apply IZR_lt; lia.
        -- apply IZR_div_lt_1. lia.
      * (* [q = X / k >= ma] as [k <= 2^64] *)
        unfold dprec in *. rewrite Hq4. apply Z.le_trans with ma; [lia |].
        apply Z.div_le_lower_bound; [lia |]. unfold X. nia.
  - assert (HXR : (IZR k * IZR (Limbs.val q) + IZR r = bpow radix2 64 * IZR ma)%R).
    { rewrite <- mult_IZR, <- plus_IZR, <- HXd. unfold X. rewrite Z.add_0_l, mult_IZR, IZR_pow2 by lia.
      reflexivity. }
    assert (E : (IZR (Limbs.val q) + IZR r / IZR k = (IZR k * IZR (Limbs.val q) + IZR r) / IZR k)%R)
      by (field; exact HkR).
    rewrite E, HXR, dy_R_eq.
    fold ma.
    replace (Dyadic.dy_exp a - 64) with (Dyadic.dy_exp a + - 64) by ring.
    (* [- 64] is the literal [Zneg 64], which [bpow_opp] does not match *)
    rewrite bpow_plus.
    replace (bpow radix2 (-64)) with (/ bpow radix2 64)%R by (symmetry; exact (bpow_opp radix2 64)).
    assert (H64 : bpow radix2 64 <> 0%R) by (apply Rgt_not_eq, bpow_gt_0).
    destruct (Dyadic.dy_neg a); cbn [cond_Ropp]; field; split; assumption.
Qed.

(** [assert!(k != 0, "division by zero")] *)
Lemma div_u64_zero : forall n a up, Dyadic.div_u64 n a 0 up = None.
Proof. intros n a up. reflexivity. Qed.

Lemma div_correct :
  forall n a b up,
  level_ok n -> dy_ok n a -> dy_ok n b -> exp_small a -> exp_small b ->
  Dyadic.dy_R b <> 0%R ->
  exists d,
  Dyadic.div n a b up = Some d /\ dy_ok n d /\
  Dyadic.dy_R d = dround n up (Dyadic.dy_R a / Dyadic.dy_R b).
Proof.
    intros n a b up Hn Ha Hb Hea Heb HbR.
  unfold Dyadic.div.
  destruct (Dyadic.is_zero n b) eqn:Zb.
  { exfalso. exact (HbR (is_zero_R n b Hn Hb Zb)). }
  destruct (Dyadic.is_zero n a) eqn:Za.
  { apply dy_zero_result; [exact Hn |]. rewrite (is_zero_R n a Hn Ha Za). unfold Rdiv. ring. }
  destruct (dy_ok_nz n a Hn Ha Za) as (Ha1 & Ha2 & Ha3 & Ha4).
  destruct (dy_ok_nz n b Hn Hb Zb) as (Hb1 & Hb2 & Hb3 & Hb4).
  unfold exp_small in Hea, Heb. pose proof Hn as Hn'. unfold level_ok in Hn'.
  unfold dprec in Ha4, Hb4.
  rewrite (checked_i64 (Dyadic.dy_exp a - Dyadic.dy_exp b)) by lia.
  rewrite (checked_i64 (Dyadic.dy_exp a - Dyadic.dy_exp b - 64 * Z.of_nat n)) by lia.
  assert (Hx : limbs_ok (repeat 0 n ++ Dyadic.dy_m a))
    by (apply limbs_ok_app; [apply limbs_ok_repeat0 | exact Ha1]).
  set (ma := Limbs.val (Dyadic.dy_m a)) in *.
  set (mb := Limbs.val (Dyadic.dy_m b)) in *.
  assert (HP : 0 < 2 ^ (64 * Z.of_nat n)) by (apply pow2_pos; lia).
  assert (HP1 : 2 ^ (64 * Z.of_nat n) = 2 * 2 ^ (64 * Z.of_nat n - 1)).
  { rewrite <- (Z.pow_1_r 2) at 2. rewrite <- pow2_add by lia. f_equal. lia. }
  assert (Hmb0 : mb <> 0) by lia.
  destruct (div_rem_correct (repeat 0 n ++ Dyadic.dy_m a) (Dyadic.dy_m b) Hx Hb1 Hmb0)
    as (q & r & Hq1 & Hq2 & Hr2 & Hq3 & Hr3 & Hq4 & Hr4).
  rewrite Hq1.
  rewrite (existsb_nonzero r Hr2).
  rewrite val_app, val_repeat0, repeat_length in Hq4, Hr4.
  fold ma in Hq4, Hr4.
  set (X := 0 + 2 ^ (64 * Z.of_nat n) * ma) in *.
  assert (HXd : X = mb * Limbs.val q + Limbs.val r) by (rewrite Hq4, Hr4; apply Z.div_mod; lia).
  assert (Hr0 : 0 <= Limbs.val r < mb) by (rewrite Hr4; apply Z.mod_pos_bound; lia).
  assert (HmbR : IZR mb <> 0%R) by (apply not_0_IZR; lia).
  rewrite length_app, repeat_length, Ha2 in Hq3.
  apply round_apply with (t := (IZR (Limbs.val r) / IZR mb)%R);
    [exact Hn | exact Hq2 | lia | | lia |].
  - destruct (Z.eqb_spec (Limbs.val r) 0) as [Hr1 | Hr1]; cbn [negb].
    + rewrite Hr1. unfold Rdiv. ring.
    + split.
      * split.
        -- apply Rdiv_lt_0_compat; apply IZR_lt; lia.
        -- apply IZR_div_lt_1. lia.
      * (* [q = ma * 2^p / mb >= ma] as [mb < 2^p] *)
        unfold dprec. rewrite Hq4. apply Z.le_trans with ma; [lia |].
        apply Z.div_le_lower_bound; [lia |]. unfold X. nia.
  - assert (HXR : (IZR mb * IZR (Limbs.val q) + IZR (Limbs.val r) =
                   bpow radix2 (64 * Z.of_nat n) * IZR ma)%R).
    { rewrite <- mult_IZR, <- plus_IZR, <- HXd. unfold X.
      rewrite Z.add_0_l, mult_IZR, IZR_pow2 by lia. reflexivity. }
    assert (E : (IZR (Limbs.val q) + IZR (Limbs.val r) / IZR mb =
                 (IZR mb * IZR (Limbs.val q) + IZR (Limbs.val r)) / IZR mb)%R)
      by (field; exact HmbR).
    rewrite E, HXR, !dy_R_eq.
    fold ma mb.
    replace (Dyadic.dy_exp a - Dyadic.dy_exp b - 64 * Z.of_nat n)
      with (Dyadic.dy_exp a + - Dyadic.dy_exp b + - (64 * Z.of_nat n)) by ring.
    rewrite !bpow_plus, !bpow_opp.
    assert (H1 : bpow radix2 (64 * Z.of_nat n) <> 0%R) by (apply Rgt_not_eq, bpow_gt_0).
    assert (H2 : bpow radix2 (Dyadic.dy_exp b) <> 0%R) by (apply Rgt_not_eq, bpow_gt_0).
    destruct (Dyadic.dy_neg a), (Dyadic.dy_neg b); cbn [negb Bool.eqb cond_Ropp];
      field; repeat split; assumption.
Qed.

(** [assert!(!other.is_zero(), "division by zero")] *)
Lemma div_zero :
  forall n a b up, level_ok n -> dy_ok n b -> Dyadic.dy_R b = 0%R -> Dyadic.div n a b up = None.
Proof.
  intros n a b up Hn Hb HbR. unfold Dyadic.div.
  rewrite (proj2 (is_zero_correct n b Hn Hb) HbR). reflexivity.
Qed.

(** ** Additions *)

(** The window of [y] in [add], for [d = x.exp - y.exp], and the body of
    [add] after the swap that makes [|x| >= |y|]: [Dyadic.add] unfolds to
    them. *)
Definition add_window (n : nat) (m : list Z) (d : Z) : list Z * bool :=
  if d <=? 64 then (Limbs.shl_into (S n) m (64 - d), false)
  else (Limbs.shr_into (S n) m (d - 64), Dyadic.low_bits_nonzero m (d - 64)).

Definition add_body (n : nat) (x y : Dyadic.dyadic) (up : bool) : option Dyadic.dyadic :=
  let d := (Dyadic.dy_exp x - Dyadic.dy_exp y) mod 2 ^ 64 in
  let* e := checked_i 64 (Dyadic.dy_exp x - 64) in
  let w := 0 :: Dyadic.dy_m x ++ 0 :: nil in
  let '(wy, sticky) := add_window n (Dyadic.dy_m y) d in
  let w' :=
    if Bool.eqb (Dyadic.dy_neg x) (Dyadic.dy_neg y) then fst (Limbs.add_assign w wy)
    else fst (Limbs.sub_assign w wy sticky) in
  Dyadic.round n (Dyadic.dy_neg x) w' e sticky up.

Lemma add_eq :
  forall n a b up,
  Dyadic.add n a b up =
  if Dyadic.is_zero n b then Some a else
  if Dyadic.is_zero n a then Some b else
  match Dyadic.cmp_abs n a b with Lt => add_body n b a up | _ => add_body n a b up end.
Proof. intros n a b up. unfold Dyadic.add. destruct (Dyadic.cmp_abs n a b); reflexivity. Qed.

(** In units of [2^(ex - 64)], [|y| = m * 2^ey] is the window [wy] plus a
    [t] in [[0, 1)], which is 0 unless [sticky]. *)
Lemma add_window_correct :
  forall n m ey ex wy sticky,
  limbs_ok m -> length m = n -> ey <= ex ->
  add_window n m (ex - ey) = (wy, sticky) ->
  limbs_ok wy /\ length wy = S n /\
  exists t, (0 <= t < 1)%R /\
  (if sticky then (0 < t)%R /\ 2 * Limbs.val wy <= Limbs.val m else t = 0%R) /\
  (IZR (Limbs.val m) * bpow radix2 ey = (IZR (Limbs.val wy) + t) * bpow radix2 (ex - 64))%R.
Proof.
  intros n m ey ex wy sticky Hm Hl Hle Hw. unfold add_window in Hw.
  pose proof (val_bounds m Hm) as Hb. rewrite Hl in Hb.
  assert (HS : 2 ^ (64 * Z.of_nat (S n)) = 2 ^ 64 * 2 ^ (64 * Z.of_nat n))
    by (rewrite Nat2Z.inj_succ, <- pow2_add by lia; f_equal; lia).
  destruct (Z.leb_spec (ex - ey) 64) as [Hd | Hd].
  - apply pair_equal_spec in Hw. destruct Hw as (Hwy & Hst). subst wy sticky.
    assert (Hd0 : 0 <= 64 - (ex - ey)) by lia.
    destruct (shl_into_correct (S n) m (64 - (ex - ey)) Hm Hd0) as (W1 & W2 & W3).
    split; [exact W1 |]. split; [exact W2 |].
    exists 0%R. split; [lra |]. split; [reflexivity |].
    assert (HP : 0 < 2 ^ (64 - (ex - ey)) <= 2 ^ 64).
    { split; [apply pow2_pos; lia | apply Z.pow_le_mono_r; lia]. }
    rewrite W3, Z.mod_small by nia.
    rewrite Rplus_0_r, mult_IZR, IZR_pow2 by lia.
    rewrite Rmult_assoc, <- bpow_plus. do 2 f_equal. ring.
  - set (k := ex - ey - 64) in *.
    assert (Hk : 1 <= k) by (unfold k; lia).
    assert (Hk0 : 0 <= k) by lia.
    apply pair_equal_spec in Hw. destruct Hw as (Hwy & Hst). subst wy sticky.
    destruct (shr_into_correct (S n) m k Hm Hk0) as (W1 & W2 & W3).
    rewrite (low_bits_nonzero_correct m k Hm Hk0).
    split; [exact W1 |]. split; [exact W2 |].
    assert (HK : 2 <= 2 ^ k).
    { replace k with (1 + (k - 1)) by ring. rewrite pow2_add by lia.
      assert (H : 0 < 2 ^ (k - 1)) by (apply pow2_pos; lia). lia. }
    assert (HK0 : 0 < 2 ^ k) by lia.
    pose proof (Z.mod_pos_bound (Limbs.val m) (2 ^ k) HK0) as Hr.
    assert (Hq : 0 <= Limbs.val m / 2 ^ k) by (apply Z.div_pos; lia).
    assert (Hdm : Limbs.val m = 2 ^ k * (Limbs.val m / 2 ^ k) + Limbs.val m mod 2 ^ k)
      by (apply Z.div_mod; lia).
    assert (Hqle : Limbs.val m / 2 ^ k <= Limbs.val m) by (apply Z.div_le_upper_bound; nia).
    assert (HPn : 0 < 2 ^ (64 * Z.of_nat n)) by (apply pow2_pos; lia).
    rewrite W3. rewrite (Z.mod_small (Limbs.val m / 2 ^ k)) by nia.
    remember (Limbs.val m / 2 ^ k) as q eqn:Eq in *.
    remember (Limbs.val m mod 2 ^ k) as r eqn:Er in *.
    assert (HkR : IZR (2 ^ k) <> 0%R) by (apply not_0_IZR; lia).
    exists (IZR r / IZR (2 ^ k))%R.
    split.
    { split.
      - unfold Rdiv. apply Rmult_le_pos; [apply IZR_le; lia |].
        apply Rlt_le, Rinv_0_lt_compat, IZR_lt. lia.
      - apply IZR_div_lt_1. lia. }
    split.
    { destruct (Z.eqb_spec r 0) as [Hr0 | Hr0]; cbn [negb].
      - rewrite Hr0. unfold Rdiv. ring.
      - split; [apply Rdiv_lt_0_compat; apply IZR_lt; lia | nia]. }
    replace (ex - 64) with (ey + k) by (unfold k; ring).
    rewrite bpow_plus, <- (IZR_pow2 k) by lia.
    rewrite Hdm at 1. rewrite plus_IZR, mult_IZR. field. exact HkR.
Qed.

(** [add] after the swap: [|y| <= |x|], both nonzero. *)
Lemma add_body_correct :
  forall n x y up,
  level_ok n -> dy_ok n x -> dy_ok n y -> exp_small x -> exp_small y ->
  Dyadic.is_zero n x = false -> Dyadic.is_zero n y = false ->
  (Rabs (Dyadic.dy_R y) <= Rabs (Dyadic.dy_R x))%R ->
  exists d,
  add_body n x y up = Some d /\ dy_ok n d /\
  Dyadic.dy_R d = dround n up (Dyadic.dy_R x + Dyadic.dy_R y).
Proof.
  intros n x y up Hn Hx Hy Hex Hey Zx Zy Hxy.
  destruct (dy_ok_nz n x Hn Hx Zx) as (Hx1 & Hx2 & Hx3 & Hx4).
  destruct (dy_ok_nz n y Hn Hy Zy) as (Hy1 & Hy2 & Hy3 & Hy4).
  assert (HxR : Dyadic.dy_R x <> 0%R).
  { intros H. apply (is_zero_correct n x Hn Hx) in H. congruence. }
  assert (HyR : Dyadic.dy_R y <> 0%R).
  { intros H. apply (is_zero_correct n y Hn Hy) in H. congruence. }
  (* [|x| >= |y|] makes [x.exp >= y.exp], as the exponents follow from the values *)
  assert (Hle : Dyadic.dy_exp y <= Dyadic.dy_exp x).
  { rewrite (exp_of_value n x Hn Hx HxR), (exp_of_value n y Hn Hy HyR).
    apply Z.sub_le_mono_r. apply mag_le_abs; assumption. }
  rewrite (dy_R_eq x), (dy_R_eq y) in Hxy |- *. rewrite !abs_cond_Ropp in Hxy.
  unfold exp_small in Hex, Hey. pose proof Hn as Hn'. unfold level_ok in Hn'.
  unfold dprec in Hx4, Hy4.
  unfold add_body.
  rewrite (Z.mod_small (Dyadic.dy_exp x - Dyadic.dy_exp y) (2 ^ 64)) by lia.
  rewrite (checked_i64 (Dyadic.dy_exp x - 64)) by lia.
  cbv beta iota zeta.
  destruct (add_window n (Dyadic.dy_m y) (Dyadic.dy_exp x - Dyadic.dy_exp y)) as [wy sticky] eqn:Hw.
  destruct (add_window_correct n (Dyadic.dy_m y) (Dyadic.dy_exp y) (Dyadic.dy_exp x) wy sticky
              Hy1 Hy2 Hle Hw) as (W1 & W2 & t & Ht & Hst & HyW).
  pose proof (val_bounds wy W1) as Hwb. rewrite W2 in Hwb.
  assert (HxW : (IZR (Limbs.val (Dyadic.dy_m x)) * bpow radix2 (Dyadic.dy_exp x) =
                 IZR (2 ^ 64 * Limbs.val (Dyadic.dy_m x)) * bpow radix2 (Dyadic.dy_exp x - 64))%R).
  { rewrite mult_IZR, IZR_pow2 by lia.
    rewrite (Rmult_comm (bpow radix2 64)), Rmult_assoc, <- bpow_plus. do 2 f_equal. ring. }
  assert (Hu : (0 < bpow radix2 (Dyadic.dy_exp x - 64))%R) by apply bpow_gt_0.
  assert (HS : 2 ^ (64 * Z.of_nat (S n)) = 2 ^ 64 * 2 ^ (64 * Z.of_nat n))
    by (rewrite Nat2Z.inj_succ, <- pow2_add by lia; f_equal; lia).
  assert (HSS : 2 ^ (64 * Z.of_nat (S (S n))) = 2 ^ 64 * 2 ^ (64 * Z.of_nat (S n)))
    by (rewrite (Nat2Z.inj_succ (S n)), <- pow2_add by lia; f_equal; lia).
  assert (HP : 2 ^ (64 * Z.of_nat n) = 2 * 2 ^ (64 * Z.of_nat n - 1)).
  { rewrite <- (Z.pow_1_r 2) at 2. rewrite <- pow2_add by lia. f_equal. lia. }
  assert (HP1 : 0 < 2 ^ (64 * Z.of_nat n - 1)) by (apply pow2_pos; lia).
  set (mx := Limbs.val (Dyadic.dy_m x)) in *.
  set (my := Limbs.val (Dyadic.dy_m y)) in *.
  set (wv := Limbs.val wy) in *.
  set (P := 2 ^ (64 * Z.of_nat n)) in *.
  set (P1 := 2 ^ (64 * Z.of_nat n - 1)) in *.
  (* [|y| <= |x|] in units of [2^(ex - 64)] *)
  assert (Hmag : (IZR wv + t <= IZR (2 ^ 64 * mx))%R).
  { assert (HxP : (0 <= IZR (2 ^ 64 * mx) * bpow radix2 (Dyadic.dy_exp x - 64))%R)
      by (apply Rmult_le_pos; [apply IZR_le; lia | lra]).
    assert (HyP : (0 <= (IZR wv + t) * bpow radix2 (Dyadic.dy_exp x - 64))%R).
    { apply Rmult_le_pos; [| lra]. apply Rplus_le_le_0_compat; [apply IZR_le; lia | lra]. }
    rewrite HyW, HxW, (Rabs_pos_eq _ HxP), (Rabs_pos_eq _ HyP) in Hxy.
    apply Rmult_le_reg_r with (bpow radix2 (Dyadic.dy_exp x - 64)); assumption. }
  assert (Hint : wv + Z.b2z sticky <= 2 ^ 64 * mx).
  { destruct sticky; cbn [Z.b2z].
    - destruct Hst as (Ht0 & _).
      assert (H : (IZR wv < IZR (2 ^ 64 * mx))%R) by lra.
      apply lt_IZR in H. lia.
    - rewrite Hst, Rplus_0_r in Hmag. apply le_IZR in Hmag. lia. }
  pose proof (b2z_bounds sticky) as Hb2z.
  set (w := 0 :: Dyadic.dy_m x ++ 0 :: nil).
  assert (Hw1 : limbs_ok w).
  { constructor; [lia |]. apply limbs_ok_app; [exact Hx1 | constructor; [lia | constructor]]. }
  assert (Hw2 : length w = S (S n)) by (unfold w; cbn [length]; rewrite length_app, Hx2; cbn; lia).
  assert (Hw3 : Limbs.val w = 2 ^ 64 * mx).
  { unfold w. cbn [Limbs.val]. rewrite val_app. cbn [Limbs.val]. fold mx. ring. }
  assert (Hlen : (length wy <= length w)%nat) by lia.
  assert (He : - 2 ^ 63 + 2 ^ 20 <= Dyadic.dy_exp x - 64 <= 2 ^ 63 - 2 ^ 20) by lia.
  destruct (Bool.eqb (Dyadic.dy_neg x) (Dyadic.dy_neg y)) eqn:Es.
  - (* same signs: a sum, which has no carry out of the top limb *)
    destruct (Limbs.add_assign w wy) as [s c] eqn:Ea. cbn [fst].
    destruct (add_assign_correct w wy s c Hw1 W1 Hlen Ea) as (S1 & S2 & S3).
    rewrite Hw2, Hw3 in S3. fold wv in S3.
    pose proof (val_bounds s S1) as Hsb.
    assert (Hc : c = false).
    { destruct c; [exfalso | reflexivity]. cbn [Z.b2z] in S3. rewrite HSS, HS in S3. lia. }
    subst c. cbn [Z.b2z] in S3. rewrite Z.mul_0_l, Z.add_0_r in S3.
    apply round_apply with (t := t);
      [exact Hn | exact S1 | lia | | exact He |].
    + destruct sticky; [| exact Hst].
      destruct Hst as (Ht0 & _). split; [lra |]. unfold dprec. fold P1. lia.
    + rewrite HyW, HxW, S3, plus_IZR.
      apply Bool.eqb_prop in Es. rewrite <- Es.
      destruct (Dyadic.dy_neg x); cbn [cond_Ropp]; ring.
  - (* opposite signs: a difference, which is nonnegative as [|x| >= |y|] *)
    destruct (Limbs.sub_assign w wy sticky) as [s c] eqn:Ea. cbn [fst].
    destruct (sub_assign_correct w wy sticky s c Hw1 W1 Hlen Ea) as (S1 & S2 & S3).
    rewrite Hw2, Hw3 in S3. fold wv in S3.
    pose proof (val_bounds s S1) as Hsb. rewrite S2, Hw2 in Hsb.
    assert (Hc : c = false).
    { destruct c; [exfalso | reflexivity]. cbn [Z.b2z] in S3. lia. }
    subst c. cbn [Z.b2z] in S3. rewrite Z.mul_0_l, Z.sub_0_r in S3.
    apply round_apply with (t := if sticky then (1 - t)%R else 0%R);
      [exact Hn | exact S1 | lia | | exact He |].
    + destruct sticky; [| reflexivity].
      destruct Hst as (Ht0 & Hwv). cbn [Z.b2z] in S3. cbv beta iota. split; [lra |].
      unfold dprec. fold P1. lia.
    + assert (Hny : Dyadic.dy_neg y = negb (Dyadic.dy_neg x)).
      { destruct (Dyadic.dy_neg x), (Dyadic.dy_neg y); cbn in Es |- *; congruence. }
      rewrite HyW, HxW, Hny.
      assert (Hs : (IZR (Limbs.val s) = IZR (2 ^ 64 * mx) - IZR wv - IZR (Z.b2z sticky))%R)
        by (rewrite <- !minus_IZR; f_equal; lia).
      rewrite Hs.
      destruct sticky; cbn [Z.b2z].
      * destruct (Dyadic.dy_neg x); cbn [negb cond_Ropp]; ring.
      * rewrite Hst. destruct (Dyadic.dy_neg x); cbn [negb cond_Ropp]; ring.
Qed.

Lemma add_correct :
  forall n a b up,
  level_ok n -> dy_ok n a -> dy_ok n b -> exp_small a -> exp_small b ->
  exists d,
  Dyadic.add n a b up = Some d /\ dy_ok n d /\
  Dyadic.dy_R d = dround n up (Dyadic.dy_R a + Dyadic.dy_R b).
Proof.
  intros n a b up Hn Ha Hb Hea Heb.
  rewrite add_eq.
  destruct (Dyadic.is_zero n b) eqn:Zb.
  { exists a. split; [reflexivity |]. split; [exact Ha |].
    rewrite (is_zero_R n b Hn Hb Zb), Rplus_0_r.
    symmetry. apply dround_id; [exact Hn | apply dy_format; assumption]. }
  destruct (Dyadic.is_zero n a) eqn:Za.
  { exists b. split; [reflexivity |]. split; [exact Hb |].
    rewrite (is_zero_R n a Hn Ha Za), Rplus_0_l.
    symmetry. apply dround_id; [exact Hn | apply dy_format; assumption]. }
  pose proof (cmp_abs_correct n a b Hn Ha Hb) as Hc.
  destruct (Dyadic.cmp_abs n a b); symmetry in Hc.
  - apply add_body_correct; try assumption.
    apply Rcompare_Eq_inv in Hc. rewrite Hc. apply Rle_refl.
  - rewrite Rplus_comm. apply add_body_correct; try assumption.
    apply Rcompare_Lt_inv in Hc. lra.
  - apply add_body_correct; try assumption.
    apply Rcompare_Gt_inv in Hc. lra.
Qed.

Lemma sub_correct :
  forall n a b up,
  level_ok n -> dy_ok n a -> dy_ok n b -> exp_small a -> exp_small b ->
  exists d,
  Dyadic.sub n a b up = Some d /\ dy_ok n d /\
  Dyadic.dy_R d = dround n up (Dyadic.dy_R a - Dyadic.dy_R b).
Proof.
  intros n a b up Hn Ha Hb Hea Heb.
  destruct (neg_correct n b Hn Hb) as (N1 & N2 & N3).
  assert (Hen : exp_small (Dyadic.neg n b)) by (unfold exp_small in *; rewrite N3; exact Heb).
  destruct (add_correct n a (Dyadic.neg n b) up Hn Ha N1 Hea Hen) as (d & D1 & D2 & D3).
  exists d. split; [exact D1 | split; [exact D2 |]].
  rewrite D3, N2. reflexivity.
Qed.

(** ** Square roots *)

(** A number with [neg = false] is not negative. *)
Lemma dy_R_nonneg :
  forall x, limbs_ok (Dyadic.dy_m x) -> Dyadic.dy_neg x = false -> (0 <= Dyadic.dy_R x)%R.
Proof.
  intros x Hm Hneg. rewrite dy_R_eq, Hneg. cbn [cond_Ropp].
  apply Rmult_le_pos; [apply IZR_le, val_nonneg, Hm | apply bpow_ge_0].
Qed.

(** [sqrt x = s + t] with [t] in [(0, 1)] if [s] is [Z.sqrt x] and [s * s <> x]. *)
Lemma sqrt_frac :
  forall x s,
  0 <= s -> s * s < x < (s + 1) * (s + 1) ->
  (0 < sqrt (IZR x) - IZR s < 1)%R.
Proof.
  intros x s Hs Hx.
  assert (HS : (0 <= IZR s)%R) by (apply IZR_le; exact Hs).
  assert (H1 : (IZR s * IZR s < IZR x)%R) by (rewrite <- mult_IZR; apply IZR_lt; lia).
  assert (H2 : (IZR x < (IZR s + 1) * (IZR s + 1))%R).
  { rewrite <- (plus_IZR s 1), <- mult_IZR. apply IZR_lt. lia. }
  assert (Hx0 : (0 <= IZR x)%R) by (apply IZR_le; nia).
  pose proof (sqrt_pos (IZR x)) as Hr.
  pose proof (sqrt_sqrt (IZR x) Hx0) as Hrr.
  set (r := sqrt (IZR x)) in *.
  split; nra.
Qed.

Lemma sqrt_correct :
  forall n a up,
  level_ok n -> dy_ok n a -> exp_small a -> (0 <= Dyadic.dy_R a)%R ->
  exists d,
  Dyadic.sqrt n a up = Some d /\ dy_ok n d /\
  Dyadic.dy_R d = dround n up (sqrt (Dyadic.dy_R a)).
Proof.
  intros n a up Hn Ha Hea Hge.
  unfold Dyadic.sqrt.
  destruct (Dyadic.is_zero n a) eqn:Za.
  { apply dy_zero_result; [exact Hn |]. rewrite (is_zero_R n a Hn Ha Za). exact sqrt_0. }
  destruct (dy_ok_nz n a Hn Ha Za) as (Ha1 & Ha2 & Ha3 & Ha4).
  pose proof Hn as Hn'. unfold level_ok in Hn'. unfold dprec in Ha4.
  assert (HPh : 0 < 2 ^ (64 * Z.of_nat n - 1)) by (apply pow2_pos; lia).
  destruct (Dyadic.dy_neg a) eqn:Ng.
  { (* [neg] and a nonzero mantissa make [dy_R a] negative *)
    exfalso. rewrite dy_R_eq, Ng in Hge. cbn [cond_Ropp] in Hge.
    assert (HM : (0 < IZR (Limbs.val (Dyadic.dy_m a)))%R) by (apply IZR_lt; lia).
    pose proof (bpow_gt_0 radix2 (Dyadic.dy_exp a)) as HB.
    pose proof (Rmult_lt_0_compat _ _ HM HB). lra. }
  unfold exp_small in Hea.
  remember (Dyadic.dy_exp a) as E eqn:HeqE in *.
  remember (Limbs.val (Dyadic.dy_m a)) as M eqn:HeqM in *.
  (* [E = 2 h + m] with [m = E mod 2] in [{0, 1}] *)
  assert (H2 : 2 <> 0) by lia.
  assert (H2' : 0 < 2) by lia.
  pose proof (Z.div_mod E 2 H2) as HEd.
  pose proof (Z.mod_pos_bound E 2 H2') as HEm.
  remember (E / 2) as h eqn:Heqh in *.
  remember (E mod 2) as m eqn:Heqm in *.
  remember (h - 32 * Z.of_nat n) as e eqn:Heqe.
  rewrite (checked_i64 e) by lia.
  cbv beta iota zeta.
  (* [x = M 2^(64 n + m)], which fits [2 n + 1] limbs *)
  assert (Hsh : 0 <= 64 * Z.of_nat n + m) by lia.
  destruct (shl_into_correct (2 * n + 1) (Dyadic.dy_m a) (64 * Z.of_nat n + m) Ha1 Hsh)
    as (Hx1 & Hx2 & Hx3).
  remember (Limbs.shl_into (2 * n + 1) (Dyadic.dy_m a) (64 * Z.of_nat n + m)) as x eqn:Heqx in *.
  rewrite <- HeqM in Hx3.
  remember (2 ^ (64 * Z.of_nat n - 1)) as Q eqn:HeqQ in *.
  assert (HP : 2 ^ (64 * Z.of_nat n + m) = 2 ^ (64 * Z.of_nat n) * 2 ^ m) by (apply pow2_add; lia).
  assert (HPn : 2 ^ (64 * Z.of_nat n) = 2 * Q).
  { rewrite HeqQ. rewrite <- (Z.pow_1_r 2) at 2. rewrite <- pow2_add by lia. f_equal. lia. }
  rewrite HPn in Ha4.
  assert (HPm : 1 <= 2 ^ m <= 2).
  { assert (Hm01 : m = 0 \/ m = 1) by lia.
    destruct Hm01 as [Hm0 | Hm0]; rewrite Hm0; cbn; lia. }
  assert (HQQ : 2 ^ (128 * Z.of_nat n - 1) = 2 * Q * Q).
  { rewrite HeqQ.
    replace (128 * Z.of_nat n - 1) with (1 + (64 * Z.of_nat n - 1) + (64 * Z.of_nat n - 1)) by lia.
    rewrite !pow2_add by lia. rewrite Z.pow_1_r. reflexivity. }
  assert (HQQ1 : 2 ^ (128 * Z.of_nat n + 1) = 8 * Q * Q).
  { rewrite HeqQ.
    replace (128 * Z.of_nat n + 1) with (3 + (64 * Z.of_nat n - 1) + (64 * Z.of_nat n - 1)) by lia.
    rewrite !pow2_add by lia. reflexivity. }
  assert (H2n : 2 ^ (64 * Z.of_nat (2 * n + 1)) = 2 ^ 64 * (2 * Q) * (2 * Q)).
  { rewrite <- HPn, <- !pow2_add by lia. f_equal. lia. }
  (* [K = M 2^m] in [[Q, 4 Q)], so that [nia] sees products of two atoms *)
  assert (HK : Q <= M * 2 ^ m < 4 * Q) by nia.
  assert (HMm : M * 2 ^ (64 * Z.of_nat n + m) = M * 2 ^ m * (2 * Q)) by (rewrite HP, HPn; ring).
  remember (M * 2 ^ m) as K eqn:HeqK in *.
  assert (HX : Limbs.val x = M * 2 ^ (64 * Z.of_nat n + m)).
  { rewrite Hx3. apply Z.mod_small. rewrite HMm, H2n. split; nia. }
  assert (HXb : 2 ^ (128 * Z.of_nat n - 1) <= Limbs.val x < 2 ^ (128 * Z.of_nat n + 1)).
  { rewrite HQQ, HQQ1, HX, HMm. nia. }
  assert (HX0 : 0 <= Limbs.val x) by (apply val_nonneg; exact Hx1).
  destruct (isqrt_correct n x Hn Hx1 Hx2 HXb) as (s & Hs1 & Hs2 & Hs3 & Hs4).
  rewrite Hs1. cbv beta iota zeta.
  destruct (mul_into_correct s s Hs2 Hs2) as (sq & Hq1 & Hq2 & Hq3 & Hq4).
  replace (2 * n + 2)%nat with (length s + length s)%nat by lia.
  rewrite Hq1. cbv beta iota zeta.
  rewrite (Limbs.cmp_correct sq x Hq2 Hx1), Hq4.
  remember (Limbs.val x) as X eqn:HeqX in *.
  remember (Limbs.val s) as Sv eqn:HeqSv in *.
  pose proof (Z.sqrt_spec X HX0) as HS. cbv zeta in HS. rewrite <- Hs4 in HS.
  rewrite <- Z.add_1_r in HS.
  assert (HS0 : 0 <= Sv) by (rewrite Hs4; apply Z.sqrt_nonneg).
  (* [Sv >= 2^(64 n - 1)] as [X >= 2^(128 n - 1) >= Q^2] *)
  assert (HQ0 : 0 <= Q) by lia.
  assert (HSQ : Q <= Sv).
  { rewrite Hs4. apply (proj1 (Z.sqrt_le_square X Q HX0 HQ0)). nia. }
  apply round_apply with (t := (sqrt (IZR X) - IZR Sv)%R);
    [exact Hn | exact Hs2 | lia | | lia |].
  - rewrite <- HeqSv.
    destruct (Z.compare_spec (Sv * Sv) X) as [Heq | Hlt | Hgt].
    + rewrite <- Heq, mult_IZR, sqrt_square by (apply IZR_le; exact HS0). ring.
    + split; [apply sqrt_frac; lia | unfold dprec; rewrite <- HeqQ; exact HSQ].
    + exfalso. lia.
  - (* [sqrt (M 2^E) = sqrt (X 2^(2 e)) = sqrt X 2^e] *)
    rewrite <- HeqSv, dy_R_eq, Ng, <- HeqE, <- HeqM. cbn [cond_Ropp].
    assert (HE : (IZR M * bpow radix2 E = IZR X * (bpow radix2 e * bpow radix2 e))%R).
    { rewrite HX, mult_IZR, IZR_pow2 by lia. rewrite Rmult_assoc, <- !bpow_plus.
      f_equal. f_equal. lia. }
    assert (HXR : (0 <= IZR X)%R) by (apply IZR_le; exact HX0).
    rewrite HE, sqrt_mult_alt by exact HXR.
    rewrite sqrt_square by apply bpow_ge_0. ring.
Qed.

(** [assert!(!self.neg, "square root of a negative number")] *)
Lemma sqrt_neg :
  forall n a up, level_ok n -> dy_ok n a -> (Dyadic.dy_R a < 0)%R -> Dyadic.sqrt n a up = None.
Proof.
  intros n a up Hn Ha Hlt. unfold Dyadic.sqrt.
  destruct (Dyadic.is_zero n a) eqn:Za.
  { exfalso. rewrite (is_zero_R n a Hn Ha Za) in Hlt. lra. }
  destruct (Dyadic.dy_neg a) eqn:Ng; [reflexivity |].
  exfalso. pose proof (dy_R_nonneg a (proj1 Ha) Ng). lra.
Qed.
