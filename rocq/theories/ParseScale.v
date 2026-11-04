(** * [scale] of a nonzero [Rat] describes its magnitude

    [scale x] returns [Huge] for [|x| > 2^1024], [Tiny] for
    [0 < |x| < 2^-1074], and otherwise [Mid q e sticky] with
    [2^55 <= q < 2^57] and [|x| = (q + f) * 2^e] for a [0 <= f < 1] that is
    0 exactly when [sticky] is false ([scale_correct]). It never panics for
    such a [Rat] with [rat_ok].

    The proof follows the comments of [fn scale] in [src/parse.rs]. A
    positive integer of [k] bits lies in [[2^(k - 1), 2^k)]
    ([nat_bits_spec]), so [2^(t - 1) < n / d < 2^(t + 1)] for the
    difference [t] of the bit lengths of [n] and [d] ([ratio_bounds]).
    With [4^k <= 5^k <= 8^k] ([pow5_bounds_nonneg], [pow5_bounds_neg]),
    this bounds [|x|] by [e2], [e5] and the bit lengths of [num] and [den]
    before [5^|e5|] is computed ([coarse_bounds]), and [scale] returns
    [Huge] or [Tiny] when these bounds imply it. Otherwise [5^|e5|] is
    multiplied into the numerator or the denominator, so that
    [|x| = n / d * 2^e2]; [scale] bounds [|x|] the same way with the bit
    lengths of [n] and [d], and either returns [Huge] or [Tiny] or picks
    [e] with [|x| / 2^e] in [(2^55, 2^57)]. The integer division then
    gives [q] and the sticky bit ([mid_ok]). Every [i128], [u64] and [i32]
    operation stays in range, as [num] and [den] have at most [2^63] bits
    and [n] and [d] at most [2^64] ([nat_bits_le], [nat_bits_mul_pow5]). *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model.

Open Scope R_scope.

(** The [Scaled] [s] describes the real [a > 0]. For [Mid], the bounds on
    [q] and [e] imply those that [round_up_exact_pre] in [Spec.v] asks
    for. *)
Definition scaled_ok (s : Scaled) (a : R) : Prop :=
  match s with
  | Huge => bpow radix2 1024 < a
  | Tiny => 0 < a < bpow radix2 (-1074)
  | Mid q e sticky =>
      (2^55 <= q < 2^57)%Z /\ (-2^20 <= e <= 2^20)%Z /\
      if sticky then F2R (Float radix2 q e) < a < F2R (Float radix2 (q + 1) e)
      else a = F2R (Float radix2 q e)
  end.

(** ** Checked integer operations that cannot overflow *)

Lemma checked_i_128 : forall z, (- 2^100 <= z <= 2^100)%Z -> checked_i 128 z = Some z.
Proof.
  intros z Hz. unfold checked_i.
  replace ((- 2^(128 - 1) <=? z) && (z <? 2^(128 - 1)))%Z with true; [reflexivity|].
  symmetry. apply Bool.andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(** [z as i32] and [z as u64] keep a [z] that fits. *)
Lemma as_i32_small : forall z, (- 2^20 <= z <= 2^20)%Z -> ((z + 2^31) mod 2^32 - 2^31)%Z = z.
Proof. intros z Hz. rewrite Z.mod_small by lia. ring. Qed.

Lemma as_u64_small : forall z, (0 <= z <= 2^40)%Z -> (z mod 2^64)%Z = z.
Proof. intros z Hz. apply Z.mod_small. lia. Qed.

Lemma div_u_some : forall a b, (b <> 0)%Z -> div_u a b = Some (a / b)%Z.
Proof. intros a b Hb. unfold div_u. now rewrite (proj2 (Z.eqb_neq b 0) Hb). Qed.

Lemma rem_u_some : forall a b, (b <> 0)%Z -> rem_u a b = Some (a mod b)%Z.
Proof. intros a b Hb. unfold rem_u. now rewrite (proj2 (Z.eqb_neq b 0) Hb). Qed.

(** ** Bit lengths *)

(** A positive [n] lies in [[2^(nat_bits n - 1), 2^nat_bits n)]. *)
Lemma nat_bits_spec : forall n, (0 < n)%Z ->
  (1 <= nat_bits n)%Z /\ (2 ^ (nat_bits n - 1) <= n < 2 ^ nat_bits n)%Z.
Proof.
  intros n Hn. unfold nat_bits.
  destruct (Z.eqb_spec n 0) as [->|_]; [lia|].
  pose proof (Z.log2_spec n Hn) as [H1 H2]. pose proof (Z.log2_nonneg n).
  unfold Z.succ in H2. replace (Z.log2 n + 1 - 1)%Z with (Z.log2 n) by lia.
  split; [lia | split; assumption].
Qed.

(** A positive [n < 2^k] has at most [k] bits. *)
Lemma nat_bits_le : forall n k, (0 < n)%Z -> (n < 2 ^ k)%Z -> (nat_bits n <= k)%Z.
Proof.
  intros n k Hn Hk. unfold nat_bits.
  destruct (Z.eqb_spec n 0) as [->|_]; [lia|].
  apply (Z.log2_lt_pow2 n k Hn) in Hk. lia.
Qed.

(** [5^k <= 8^k = 2^(3 k)]. *)
Lemma pow5_le_pow2 : forall k, (0 <= k)%Z -> (5 ^ k <= 2 ^ (3 * k))%Z.
Proof.
  intros k Hk. rewrite Z.pow_mul_r by lia.
  apply Z.pow_le_mono_l. lia.
Qed.

(** [m * 5^k] has at most [3 k] bits more than [m]. *)
Lemma nat_bits_mul_pow5 : forall m k, (0 < m)%Z -> (0 <= k)%Z ->
  (0 < m * 5 ^ k)%Z /\ (nat_bits (m * 5 ^ k) <= nat_bits m + 3 * k)%Z.
Proof.
  intros m k Hm Hk.
  pose proof (Z.pow_pos_nonneg 5 k ltac:(lia) Hk) as H5.
  destruct (nat_bits_spec m Hm) as [Hb [_ Hm2]].
  split; [lia|]. apply nat_bits_le; [lia|].
  rewrite Z.pow_add_r by lia.
  apply Z.lt_le_trans with (2 ^ nat_bits m * 5 ^ k)%Z.
  - apply Z.mul_lt_mono_pos_r; assumption.
  - apply Z.mul_le_mono_nonneg_l; [apply Z.pow_nonneg; lia | apply pow5_le_pow2; lia].
Qed.

(** ** Powers as reals *)

Lemma IZR_pow2 : forall e, (0 <= e)%Z -> IZR (2 ^ e) = bpow radix2 e.
Proof. intros e He. exact (IZR_Zpower radix2 e He). Qed.

Lemma IZR_pow5 : forall e, (0 <= e)%Z -> IZR (5 ^ e) = bpow radix5 e.
Proof. intros e He. exact (IZR_Zpower radix5 e He). Qed.

(** [4^k <= 5^k <= 8^k], the [lo5] and [hi5] of [scale] for [e5 >= 0]. *)
Lemma pow5_bounds_nonneg : forall k, (0 <= k)%Z ->
  bpow radix2 (2 * k) <= bpow radix5 k <= bpow radix2 (3 * k).
Proof.
  intros k Hk.
  rewrite <- IZR_pow2, <- IZR_pow2, <- IZR_pow5 by lia.
  split; apply IZR_le.
  - rewrite Z.pow_mul_r by lia. apply Z.pow_le_mono_l. lia.
  - apply pow5_le_pow2. exact Hk.
Qed.

(** The same for [e5 < 0], where [lo5] and [hi5] swap. *)
Lemma pow5_bounds_neg : forall k, (k < 0)%Z ->
  bpow radix2 (3 * k) <= bpow radix5 k <= bpow radix2 (2 * k).
Proof.
  intros k Hk.
  destruct (pow5_bounds_nonneg (- k) ltac:(lia)) as [H1 H2].
  replace (3 * k)%Z with (- (3 * - k))%Z by lia.
  replace (2 * k)%Z with (- (2 * - k))%Z by lia.
  rewrite (bpow_opp radix2 (3 * - k)), (bpow_opp radix2 (2 * - k)).
  replace (bpow radix5 k) with (/ bpow radix5 (- k))
    by (rewrite <- bpow_opp, Z.opp_involutive; reflexivity).
  split; apply Rinv_le_contravar; try assumption; apply bpow_gt_0.
Qed.

(** ** Real bounds from bit lengths *)

Lemma Rdiv_nonneg : forall a b, 0 <= a -> 0 < b -> 0 <= a / b.
Proof.
  intros a b Ha Hb. unfold Rdiv.
  apply Rmult_le_pos; [exact Ha | apply Rlt_le, Rinv_0_lt_compat, Hb].
Qed.

(** [2^(t - 1) < n / d < 2^(t + 1)] for [t = nat_bits n - nat_bits d]. *)
Lemma ratio_bounds : forall n d, (0 < n)%Z -> (0 < d)%Z ->
  bpow radix2 (nat_bits n - nat_bits d - 1) < IZR n / IZR d <
  bpow radix2 (nat_bits n - nat_bits d + 1).
Proof.
  intros n d Hn Hd.
  destruct (nat_bits_spec n Hn) as [Hbn [Hn1 Hn2]].
  destruct (nat_bits_spec d Hd) as [Hbd [Hd1 Hd2]].
  apply IZR_le in Hn1. apply IZR_lt in Hn2. apply IZR_le in Hd1. apply IZR_lt in Hd2.
  rewrite IZR_pow2 in Hn1, Hn2, Hd1, Hd2 by lia.
  pose proof (bpow_gt_0 radix2 (nat_bits n - 1)) as Pn1.
  pose proof (bpow_gt_0 radix2 (nat_bits d - 1)) as Pd1.
  pose proof (bpow_gt_0 radix2 (nat_bits d)) as Pd2.
  assert (Pd : 0 < IZR d) by (apply IZR_lt; lia).
  (* [1/2^bd < 1/d <= 1/2^(bd - 1)]. *)
  assert (Id1 : / IZR d <= / bpow radix2 (nat_bits d - 1)).
  { apply Rinv_le_contravar; assumption. }
  assert (Id2 : / bpow radix2 (nat_bits d) < / IZR d).
  { apply Rinv_lt_contravar; [apply Rmult_lt_0_compat|]; assumption. }
  pose proof (Rinv_0_lt_compat _ Pd2) as Qd2.
  unfold Rdiv. split.
  - replace (nat_bits n - nat_bits d - 1)%Z with ((nat_bits n - 1) + - nat_bits d)%Z by ring.
    rewrite bpow_plus, bpow_opp. nra.
  - replace (nat_bits n - nat_bits d + 1)%Z with (nat_bits n + - (nat_bits d - 1))%Z by ring.
    rewrite bpow_plus, bpow_opp. nra.
Qed.

(** [|x|] with its factors in the order of the bounds below. *)
Lemma rat_R_abs : forall x, (0 <= rat_num x)%Z -> (0 < rat_den x)%Z ->
  Rabs (rat_R x) =
  IZR (rat_num x) / IZR (rat_den x) * bpow radix2 (rat_e2 x) * bpow radix5 (rat_e5 x).
Proof.
  intros x Hn Hd.
  assert (H : 0 <= IZR (rat_num x) / IZR (rat_den x) * bpow radix2 (rat_e2 x) *
                   bpow radix5 (rat_e5 x)).
  { apply Rmult_le_pos; [apply Rmult_le_pos|]; [|apply bpow_ge_0..].
    apply Rdiv_nonneg; [apply IZR_le | apply IZR_lt]; lia. }
  unfold rat_R.
  destruct (rat_neg x); [rewrite Rabs_Ropp|]; rewrite Rabs_pos_eq;
    (unfold Rdiv in *; first [ring | lra]).
Qed.

(** The coarse bound of [scale], before [5^e5] is computed:
    [2^(b0 + lo5 - 1) < |x| < 2^(b0 + hi5 + 1)]. *)
Lemma coarse_bounds : forall num den e2 e5 lo5 hi5,
  (0 < num)%Z -> (0 < den)%Z ->
  bpow radix2 lo5 <= bpow radix5 e5 <= bpow radix2 hi5 ->
  bpow radix2 (nat_bits num - nat_bits den + e2 + lo5 - 1) <
  IZR num / IZR den * bpow radix2 e2 * bpow radix5 e5 <
  bpow radix2 (nat_bits num - nat_bits den + e2 + hi5 + 1).
Proof.
  intros num den e2 e5 lo5 hi5 Hn Hd [H5l H5h].
  destruct (ratio_bounds num den Hn Hd) as [Hl Hh].
  set (t := (nat_bits num - nat_bits den)%Z) in *.
  set (r := IZR num / IZR den) in *.
  pose proof (bpow_gt_0 radix2 e2) as P2.
  pose proof (bpow_gt_0 radix2 lo5) as Pl.
  pose proof (bpow_gt_0 radix2 (t - 1)) as Pt.
  replace (t + e2 + lo5 - 1)%Z with (t - 1 + e2 + lo5)%Z by ring.
  replace (t + e2 + hi5 + 1)%Z with (t + 1 + e2 + hi5)%Z by ring.
  rewrite (bpow_plus radix2 (t - 1 + e2)), (bpow_plus radix2 (t - 1)).
  rewrite (bpow_plus radix2 (t + 1 + e2)), (bpow_plus radix2 (t + 1)).
  split.
  - apply Rlt_le_trans with (r * bpow radix2 e2 * bpow radix2 lo5).
    + apply Rmult_lt_compat_r; [exact Pl|]. apply Rmult_lt_compat_r; assumption.
    + apply Rmult_le_compat_l; [|exact H5l].
      apply Rmult_le_pos; lra.
  - apply Rle_lt_trans with (r * bpow radix2 e2 * bpow radix2 hi5).
    + apply Rmult_le_compat_l; [|exact H5h].
      apply Rmult_le_pos; lra.
    + apply Rmult_lt_compat_r; [apply bpow_gt_0|]. apply Rmult_lt_compat_r; assumption.
Qed.

(** ** The division *)

(** If [a = N / D * 2^e] and [2^(e + 55) < a < 2^(e + 57)], the quotient
    and remainder of [N / D] describe [a] as [scale]'s [Mid] says. *)
Lemma mid_ok : forall N D e a,
  (0 <= N)%Z -> (0 < D)%Z -> (- 2^20 <= e <= 2^20)%Z ->
  a = IZR N / IZR D * bpow radix2 e ->
  bpow radix2 (e + 55) < a < bpow radix2 (e + 57) ->
  scaled_ok (Mid ((N / D) mod 2^128) e (negb (N mod D =? 0))) a.
Proof.
  intros N D e a HN HD He Ha [Hlo Hhi].
  pose proof (Z.div_mod N D ltac:(lia)) as HNqr.
  pose proof (Z.mod_pos_bound N D HD) as Hr.
  remember (N / D)%Z as q eqn:Hq. remember (N mod D)%Z as r eqn:Hr'.
  pose proof (bpow_gt_0 radix2 e) as Pe.
  assert (PD : 0 < IZR D) by (apply IZR_lt; lia).
  (* [N / D = q + rho] with [0 <= rho = r / D < 1]. *)
  set (rho := IZR r / IZR D).
  assert (Hrho : 0 <= rho < 1).
  { unfold rho. split.
    - apply Rdiv_nonneg; [apply IZR_le; lia | exact PD].
    - apply Rmult_lt_reg_r with (IZR D); [exact PD|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l by lra.
      apply IZR_lt. lia. }
  assert (Ha' : a = (IZR q + rho) * bpow radix2 e).
  { rewrite Ha, HNqr, plus_IZR, mult_IZR. unfold rho. field. lra. }
  rewrite (bpow_plus radix2 e 55), <- (IZR_pow2 55) in Hlo by lia.
  rewrite (bpow_plus radix2 e 57), <- (IZR_pow2 57) in Hhi by lia.
  (* [2^55 < q + rho < 2^57], so [2^55 <= q < 2^57]. *)
  assert (Hv : IZR (2 ^ 55) < IZR q + rho < IZR (2 ^ 57)).
  { split.
    - apply Rmult_lt_reg_r with (bpow radix2 e); [exact Pe|]. lra.
    - apply Rmult_lt_reg_r with (bpow radix2 e); [exact Pe|]. lra. }
  assert (Hq57 : (q < 2 ^ 57)%Z) by (apply lt_IZR; lra).
  assert (Hq55 : (2 ^ 55 < q + 1)%Z) by (apply lt_IZR; rewrite plus_IZR; lra).
  unfold scaled_ok.
  rewrite Z.mod_small by lia.
  split; [lia | split; [lia|]].
  unfold F2R; cbn [Fnum Fexp]. rewrite plus_IZR.
  destruct (Z.eqb_spec r 0) as [Hr0|Hr0]; cbn [negb].
  - rewrite Ha'. unfold rho. rewrite Hr0. unfold Rdiv. ring.
  - assert (Prho : 0 < rho).
    { unfold rho. apply Rdiv_lt_0_compat; [apply IZR_lt; lia | exact PD]. }
    assert (P1 : 0 < rho * bpow radix2 e) by (apply Rmult_lt_0_compat; lra).
    assert (P2 : 0 < (1 - rho) * bpow radix2 e) by (apply Rmult_lt_0_compat; lra).
    rewrite Ha'. split; lra.
Qed.

(** ** [scale] *)

Theorem scale_correct :
  forall x, rat_ok x -> rat_num x <> 0%Z ->
  exists s, scale x = Some s /\ scaled_ok s (Rabs (rat_R x)).
Proof.
  intros x Hok Hnz.
  destruct Hok as [[Hn0 HnK] [[Hd0 HdK] [He2 He5]]].
  rewrite rat_R_abs by assumption.
  destruct x as [neg num den e2 e5].
  cbn [rat_num rat_den rat_e2 rat_e5] in *.
  (* [num] and [den] have at most [2^63] bits. [lia] must not see
     [2 ^ 2 ^ 63], which it would compute. *)
  assert (Hn : (0 < num)%Z) by (clear - Hn0 Hnz; lia).
  pose proof (nat_bits_le num (2^63) Hn HnK) as Hbn.
  pose proof (nat_bits_le den (2^63) Hd0 HdK) as Hbd.
  clear HnK HdK.
  pose proof (proj1 (nat_bits_spec num Hn)) as Hbn1.
  pose proof (proj1 (nat_bits_spec den Hd0)) as Hbd1.
  remember (IZR num / IZR den * bpow radix2 e2 * bpow radix5 e5) as A eqn:HA0.
  assert (PA : 0 < A).
  { rewrite HA0. apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; [|apply bpow_gt_0..].
    apply Rdiv_lt_0_compat; apply IZR_lt; lia. }
  unfold scale. cbn [rat_num rat_den rat_e2 rat_e5].
  rewrite (checked_i_128 (nat_bits num - nat_bits den)) by lia. cbv beta iota zeta.
  rewrite (checked_i_128 (nat_bits num - nat_bits den + e2)) by lia. cbv beta iota zeta.
  remember (nat_bits num - nat_bits den + e2)%Z as b0 eqn:Hb0.
  (* The coarse bound decides the [Huge] and [Tiny] that the exponents imply. *)
  remember (if 0 <=? e5 then
      let* lo5 := checked_i 128 (2 * e5) in
      let* hi5 := checked_i 128 (3 * e5) in
      Some (lo5, hi5)
    else
      let* lo5 := checked_i 128 (3 * e5) in
      let* hi5 := checked_i 128 (2 * e5) in
      Some (lo5, hi5))%Z as lohi eqn:Hlohi.
  assert (Hlh : exists lo5 hi5, lohi = Some (lo5, hi5) /\
    (- 2^33 <= lo5 <= 2^33)%Z /\ (- 2^33 <= hi5 <= 2^33)%Z /\
    bpow radix2 lo5 <= bpow radix5 e5 <= bpow radix2 hi5).
  { subst lohi. destruct (Z.leb_spec 0 e5) as [Hs|Hs].
    - rewrite !checked_i_128 by lia. cbv beta iota.
      exists (2 * e5)%Z, (3 * e5)%Z. split; [reflexivity|].
      split; [lia | split; [lia | apply pow5_bounds_nonneg; exact Hs]].
    - rewrite !checked_i_128 by lia. cbv beta iota.
      exists (3 * e5)%Z, (2 * e5)%Z. split; [reflexivity|].
      split; [lia | split; [lia | apply pow5_bounds_neg; exact Hs]]. }
  destruct Hlh as [lo5 [hi5 [Hlh [Hlo5 [Hhi5 H5]]]]].
  rewrite Hlh. clear Hlohi Hlh lohi. cbv beta iota.
  destruct (coarse_bounds num den e2 e5 lo5 hi5 Hn Hd0 H5) as [Cl Ch].
  rewrite <- Hb0, <- HA0 in Cl, Ch.
  rewrite (checked_i_128 (b0 + lo5)) by lia. cbv beta iota.
  destruct (Z.leb_spec 1025 (b0 + lo5)) as [Hu|Hu].
  { exists Huge. split; [reflexivity|]. cbn [scaled_ok].
    apply Rle_lt_trans with (2 := Cl). apply bpow_le. lia. }
  rewrite (checked_i_128 (b0 + hi5)) by lia. cbv beta iota.
  destruct (Z.leb_spec (b0 + hi5) (-1075)) as [Hv|Hv].
  { exists Tiny. split; [reflexivity|]. cbn [scaled_ok].
    split; [exact PA|]. apply Rlt_le_trans with (1 := Ch). apply bpow_le. lia. }
  (* [|x| = n / d * 2^e2]. *)
  remember (if 0 <=? e5 then (num * 5 ^ Z.abs e5, den) else (num, den * 5 ^ Z.abs e5))%Z
    as nd eqn:Hnd.
  destruct nd as [n d].
  assert (Hnd' : (0 < n)%Z /\ (0 < d)%Z /\
    (nat_bits n <= 2^64)%Z /\ (nat_bits d <= 2^64)%Z /\
    A = IZR n / IZR d * bpow radix2 e2).
  { rewrite HA0. destruct (Z.leb_spec 0 e5) as [Hs|Hs]; injection Hnd as -> ->.
    - rewrite Z.abs_eq by exact Hs.
      destruct (nat_bits_mul_pow5 num e5 Hn Hs) as [Pn Bn].
      split; [exact Pn | split; [exact Hd0 | split; [lia | split; [lia|]]]].
      rewrite mult_IZR, IZR_pow5 by exact Hs. unfold Rdiv. ring.
    - rewrite Z.abs_neq by lia.
      destruct (nat_bits_mul_pow5 den (- e5) Hd0 ltac:(lia)) as [Pd Bd].
      split; [exact Hn | split; [exact Pd | split; [lia | split; [lia|]]]].
      rewrite mult_IZR, IZR_pow5 by lia.
      replace (bpow radix5 e5) with (/ bpow radix5 (- e5))
        by (rewrite <- bpow_opp, Z.opp_involutive; reflexivity).
      unfold Rdiv. rewrite Rinv_mult. ring. }
  clear Hnd.
  destruct Hnd' as [Pn [Pd [Bn [Bd HA]]]].
  pose proof (proj1 (nat_bits_spec n Pn)) as Bn1.
  pose proof (proj1 (nat_bits_spec d Pd)) as Bd1.
  cbv beta iota.
  (* The fine bound [2^(b - 1) < |x| < 2^(b + 1)]. *)
  rewrite (checked_i_128 (nat_bits n - nat_bits d)) by lia. cbv beta iota zeta.
  rewrite (checked_i_128 (nat_bits n - nat_bits d + e2)) by lia. cbv beta iota zeta.
  remember (nat_bits n - nat_bits d + e2)%Z as b eqn:Hb.
  assert (Fb : bpow radix2 (b - 1) < A < bpow radix2 (b + 1)).
  { destruct (ratio_bounds n d Pn Pd) as [Rl Rh].
    pose proof (bpow_gt_0 radix2 e2) as P2.
    rewrite HA, Hb.
    replace (nat_bits n - nat_bits d + e2 - 1)%Z with (nat_bits n - nat_bits d - 1 + e2)%Z
      by ring.
    replace (nat_bits n - nat_bits d + e2 + 1)%Z with (nat_bits n - nat_bits d + 1 + e2)%Z
      by ring.
    rewrite (bpow_plus radix2 (nat_bits n - nat_bits d - 1)).
    rewrite (bpow_plus radix2 (nat_bits n - nat_bits d + 1)).
    split; apply Rmult_lt_compat_r; assumption. }
  destruct (Z.leb_spec 1025 b) as [Hbh|Hbh].
  { exists Huge. split; [reflexivity|]. cbn [scaled_ok].
    apply Rle_lt_trans with (2 := proj1 Fb). apply bpow_le. lia. }
  destruct (Z.leb_spec b (-1075)) as [Hbt|Hbt].
  { exists Tiny. split; [reflexivity|]. cbn [scaled_ok].
    split; [exact PA|]. apply Rlt_le_trans with (1 := proj2 Fb). apply bpow_le. lia. }
  (* [e = b - 56], so [2^(e + 55) < |x| < 2^(e + 57)]. *)
  rewrite (checked_i_128 (b - 56)) by lia. cbv beta iota.
  rewrite (checked_i_128 (e2 - (b - 56))) by lia. cbv beta iota.
  assert (Fe : bpow radix2 (b - 56 + 55) < A < bpow radix2 (b - 56 + 57)).
  { replace (b - 56 + 55)%Z with (b - 1)%Z by ring.
    replace (b - 56 + 57)%Z with (b + 1)%Z by ring. exact Fb. }
  destruct (Z.leb_spec 0 (e2 - (b - 56))) as [Hsh|Hsh].
  - (* [sh >= 0]: [q = floor(n * 2^sh / d)]. *)
    rewrite (as_u64_small (e2 - (b - 56))) by lia. cbv beta iota zeta.
    rewrite Z.shiftl_mul_pow2 by exact Hsh.
    rewrite div_u_some, rem_u_some by lia. cbv beta iota zeta.
    rewrite (as_i32_small (b - 56)) by lia.
    eexists. split; [reflexivity|].
    apply mid_ok; [| exact Pd | lia | | exact Fe].
    { apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]. }
    assert (E : bpow radix2 e2 = bpow radix2 (e2 - (b - 56)) * bpow radix2 (b - 56)).
    { rewrite <- bpow_plus. f_equal. ring. }
    rewrite HA, E, mult_IZR, IZR_pow2 by exact Hsh. unfold Rdiv. ring.
  - (* [sh < 0]: [q = floor(n / (d * 2^(-sh)))]. *)
    rewrite (checked_i_128 (- (e2 - (b - 56)))) by lia. cbv beta iota.
    rewrite (as_u64_small (- (e2 - (b - 56)))) by lia. cbv beta iota zeta.
    rewrite Z.shiftl_mul_pow2 by lia.
    assert (PD : (0 < d * 2 ^ (- (e2 - (b - 56))))%Z).
    { apply Z.mul_pos_pos; [exact Pd | apply Z.pow_pos_nonneg; lia]. }
    rewrite div_u_some, rem_u_some by lia. cbv beta iota zeta.
    rewrite (as_i32_small (b - 56)) by lia.
    eexists. split; [reflexivity|].
    apply mid_ok; [lia | exact PD | lia | | exact Fe].
    assert (E : bpow radix2 e2 = / bpow radix2 (- (e2 - (b - 56))) * bpow radix2 (b - 56)).
    { rewrite <- bpow_opp, <- bpow_plus. f_equal. ring. }
    rewrite HA, E, mult_IZR, IZR_pow2 by lia. unfold Rdiv. rewrite Rinv_mult. ring.
Qed.
