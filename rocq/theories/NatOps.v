(** * The operations of [Nat] on the integers that [Nat]s hold

    Each [Nat] that [Model.v] reads as a [Z] has the limbs [to_limbs] of
    that [Z], the only list of limbs with no zero limb at the top
    ([nat_ok]) that holds it. Each operation of [NatLimbs] returns such
    limbs, so the reading holds of its result too, and the wrapper [_z] of
    each one computes the operation on [Z] that its comment gives. *)

From Stdlib Require Import ZArith Lia List.
From Flocq Require Import Core.Core.
From Inari Require Import Model Limbs Knuth.

Open Scope Z_scope.

(** The limbs of a [Nat]: [u64]s, with no zero limb at the top. *)
Definition nat_ok (x : list Z) : Prop :=
  limbs_ok x /\ (x = nil \/ Limbs.limb x (length x - 1) <> 0).

(** ** Lists of limbs with no zero limb at the top *)

Lemma checked_u_some : forall w z, 0 <= z < 2 ^ w -> checked_u w z = Some z.
Proof.
intros w z Hz. unfold checked_u.
replace ((0 <=? z) && (z <? 2 ^ w)) with true; [reflexivity|].
symmetry. apply Bool.andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma nat_ok_nil : nat_ok nil.
Proof. split; [constructor | now left]. Qed.

Lemma val_nonneg : forall x, limbs_ok x -> 0 <= Limbs.val x.
Proof. intros x H. exact (proj1 (val_bounds x H)). Qed.

Lemma nat_ok_cons :
  forall a x, nat_ok (a :: x) <-> 0 <= a < 2 ^ 64 /\ nat_ok x /\ (x = nil -> a <> 0).
Proof.
intros a x. unfold nat_ok, limbs_ok, Limbs.limb. rewrite Forall_cons_iff.
destruct x as [|b x].
- cbn. split.
  + intros [[Ha _] H]. split; [exact Ha|]. split; [split; [constructor | now left]|].
    intros _. destruct H as [H|H]; [discriminate | exact H].
  + intros [Ha [_ H]]. split; [split; [exact Ha | constructor]|]. right. now apply H.
- cbn [length]. replace (S (S (length x)) - 1)%nat with (S (length x)) by lia.
  replace (S (length x) - 1)%nat with (length x) by lia. cbn [nth].
  split.
  + intros [[Ha Hf] [H|H]]; [discriminate|].
    split; [exact Ha|]. split; [split; [exact Hf | now right]|]. discriminate.
  + intros [Ha [[Hf [H|H]] _]]; [discriminate|].
    split; [split; [exact Ha | exact Hf]|]. now right.
Qed.

(** A nonempty list of limbs has no zero limb at the top exactly when it
    holds at least [2^(64 (n - 1))] for its length [n]. *)
Lemma nat_ok_iff_val :
  forall x, limbs_ok x -> x <> nil ->
  (nat_ok x <-> 2 ^ (64 * Z.of_nat (length x - 1)) <= Limbs.val x).
Proof.
intros x Hx Hn.
pose proof (val_last x Hn) as E.
assert (Hf : limbs_ok (firstn (length x - 1) x)) by now apply limbs_ok_firstn.
pose proof (val_bounds _ Hf) as Bf.
rewrite length_firstn, Nat.min_l in Bf by lia.
pose proof (limb_bound x (length x - 1) Hx) as Bl.
pose proof (Z.pow_pos_nonneg 2 (64 * Z.of_nat (length x - 1)) ltac:(lia) ltac:(lia)) as P.
split.
- intros [_ [H|H]]; [contradiction|]. rewrite E.
  assert (1 <= Limbs.limb x (length x - 1)) by lia. nia.
- intros H. split; [exact Hx|]. right. intros H0. rewrite H0 in E. lia.
Qed.

Lemma nat_ok_val0 : forall x, nat_ok x -> Limbs.val x = 0 -> x = nil.
Proof.
induction x as [|a x IH]; intros H E; [reflexivity|].
apply nat_ok_cons in H. destruct H as [Ha [Hx Hz]].
cbn [Limbs.val] in E. pose proof (val_nonneg x (proj1 Hx)).
assert (Ex : Limbs.val x = 0) by lia.
specialize (IH Hx Ex). exfalso. apply (Hz IH). lia.
Qed.

(** Each value has at most one list of limbs with no zero limb at the top. *)
Lemma nat_ok_unique :
  forall x y, nat_ok x -> nat_ok y -> Limbs.val x = Limbs.val y -> x = y.
Proof.
induction x as [|a x IH]; intros y Hx Hy E.
- symmetry. apply nat_ok_val0; [exact Hy|]. cbn [Limbs.val] in E. lia.
- destruct y as [|b y].
  + apply nat_ok_val0; [exact Hx | exact E].
  + apply nat_ok_cons in Hx. apply nat_ok_cons in Hy.
    destruct Hx as [Ha [Hx _]], Hy as [Hb [Hy _]].
    cbn [Limbs.val] in E.
    assert (Eab : a = b /\ Limbs.val x = Limbs.val y) by lia.
    destruct Eab as [-> Exy]. now rewrite (IH y Hx Hy Exy).
Qed.

(** ** [to_limbs] and [from_limbs] *)

Lemma to_limbs_fuel_correct :
  forall f z, 0 <= z < 2 ^ Z.of_nat f ->
  nat_ok (NatLimbs.to_limbs_fuel f z) /\ Limbs.val (NatLimbs.to_limbs_fuel f z) = z.
Proof.
induction f as [|f IH]; intros z Hz.
- cbn in Hz. replace z with 0 by lia. split; [exact nat_ok_nil | reflexivity].
- cbn [NatLimbs.to_limbs_fuel].
  destruct (Z.eqb_spec z 0) as [->|Hz0]; [split; [exact nat_ok_nil | reflexivity]|].
  pose proof (Z.pow_pos_nonneg 2 (Z.of_nat f) ltac:(lia) ltac:(lia)) as P.
  assert (Hq : 0 <= z / 2 ^ 64 < 2 ^ Z.of_nat f).
  { split; [apply Z.div_pos; lia|].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hz by lia.
    apply Z.div_lt_upper_bound; [lia | nia]. }
  destruct (IH _ Hq) as [Hok Hv].
  (* [z = 2^64 (z / 2^64) + z mod 2^64]. *)
  pose proof (Z.div_mod z (2 ^ 64) ltac:(lia)) as D.
  split.
  + apply nat_ok_cons. split; [apply Z.mod_pos_bound; lia|]. split; [exact Hok|].
    intros Hn Hm. rewrite Hn in Hv. cbn [Limbs.val] in Hv.
    rewrite <- Hv, Hm in D. lia.
  + cbn [Limbs.val]. rewrite Hv. lia.
Qed.

Lemma to_limbs_correct :
  forall z, 0 <= z -> nat_ok (NatLimbs.to_limbs z) /\ Limbs.val (NatLimbs.to_limbs z) = z.
Proof.
intros z Hz. unfold NatLimbs.to_limbs. apply to_limbs_fuel_correct.
rewrite Z2Nat.id by (pose proof (Z.log2_nonneg z); lia).
split; [exact Hz|].
destruct (Z.eq_dec z 0) as [->|Hz0]; [reflexivity|].
exact (proj2 (Z.log2_spec z ltac:(lia))).
Qed.

Lemma to_limbs_val : forall x, nat_ok x -> NatLimbs.to_limbs (Limbs.val x) = x.
Proof.
intros x Hx. pose proof (val_nonneg x (proj1 Hx)) as H.
destruct (to_limbs_correct _ H) as [Hok Hv].
now apply nat_ok_unique.
Qed.

Lemma from_limbs_correct :
  forall v,
  limbs_ok v ->
  nat_ok (NatLimbs.from_limbs v) /\ Limbs.val (NatLimbs.from_limbs v) = Limbs.val v.
Proof.
induction v as [|a v IH]; intros Hv; [split; [exact nat_ok_nil | reflexivity]|].
unfold limbs_ok in Hv. apply Forall_cons_iff in Hv. destruct Hv as [Ha Hv].
destruct (IH Hv) as [Hok Hval].
cbn [NatLimbs.from_limbs]. revert Hok Hval.
destruct (NatLimbs.from_limbs v) as [|b t]; intros Hok Hval.
- cbn [Limbs.val] in Hval |- *.
  destruct (Z.eqb_spec a 0) as [->|Ha0]; [split; [exact nat_ok_nil | cbn [Limbs.val]; lia]|].
  split; [|cbn [Limbs.val]; lia].
  apply nat_ok_cons. split; [exact Ha|]. split; [exact nat_ok_nil|]. intros _; exact Ha0.
- split.
  + apply nat_ok_cons. split; [exact Ha|]. split; [exact Hok | discriminate].
  + cbn [Limbs.val] in Hval |- *. lia.
Qed.

Lemma to_limbs_nil : forall a, 0 <= a -> (NatLimbs.to_limbs a = nil <-> a = 0).
Proof.
intros a Ha. destruct (to_limbs_correct a Ha) as [Hok Hv]. split.
- intros E. rewrite E in Hv. cbn [Limbs.val] in Hv. lia.
- intros ->. reflexivity.
Qed.

(** ** The operations on lists of limbs *)

Lemma nat_mul_correct :
  forall x y, nat_ok x -> nat_ok y ->
  exists z, NatLimbs.mul x y = Some z /\ nat_ok z /\ Limbs.val z = Limbs.val x * Limbs.val y.
Proof.
intros x y Hx Hy. unfold NatLimbs.mul.
destruct (mul_into_correct x y (proj1 Hx) (proj1 Hy)) as (out & E & Hout & _ & Hv).
rewrite E. destruct (from_limbs_correct out Hout) as [Hok Hval].
exists (NatLimbs.from_limbs out). split; [reflexivity|]. split; [exact Hok | lia].
Qed.

Lemma nat_shl_correct :
  forall x k, nat_ok x -> 0 <= k ->
  nat_ok (NatLimbs.shl x k) /\ Limbs.val (NatLimbs.shl x k) = Limbs.val x * 2 ^ k.
Proof.
intros x k Hx Hk. unfold NatLimbs.shl.
destruct x as [|a x0].
{ cbn [NatLimbs.is_zero Limbs.val]. split; [exact nat_ok_nil | ring]. }
cbn [NatLimbs.is_zero]. remember (a :: x0) as x eqn:Ex.
set (n := (Z.to_nat (k / 64) + length x + 1)%nat).
destruct (shl_into_correct n x k (proj1 Hx) Hk) as (Hl & _ & Hv).
destruct (from_limbs_correct _ Hl) as [Hok Hval].
split; [exact Hok|]. rewrite Hval, Hv. apply Z.mod_small.
pose proof (val_bounds x (proj1 Hx)) as [B0 B1].
pose proof (Z.pow_nonneg 2 k ltac:(lia)) as P.
split; [nia|].
assert (Hk64 : 0 <= k / 64 /\ k < 64 * (k / 64) + 64).
{ pose proof (Z.mod_pos_bound k 64 ltac:(lia)). pose proof (Z.div_mod k 64 ltac:(lia)).
  split; [apply Z.div_pos|]; lia. }
assert (Hk' : 2 ^ k < 2 ^ (64 * (k / 64) + 64)) by (apply Z.pow_lt_mono_r; lia).
unfold n. rewrite !Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia).
replace (64 * (k / 64 + Z.of_nat (length x) + Z.of_nat 1))
  with (64 * Z.of_nat (length x) + (64 * (k / 64) + 64)) by (cbn [Z.of_nat]; ring).
rewrite Z.pow_add_r by lia.
apply Z.mul_lt_mono_nonneg; lia.
Qed.

(** [mul_add_u64] keeps the top limb nonzero for [m > 0]: the carry is
    pushed exactly when it is nonzero. *)
Lemma mul_add_u64_correct :
  forall n m a, nat_ok n -> 0 < m < 2 ^ 64 -> 0 <= a < 2 ^ 64 ->
  exists n', NatLimbs.mul_add_u64 n m a = Some n' /\ nat_ok n' /\
  Limbs.val n' = Limbs.val n * m + a.
Proof.
intros n m a Hn Hm Ha. unfold NatLimbs.mul_add_u64.
destruct (mul_add_limb_correct n m a (proj1 Hn) ltac:(lia) Ha)
  as (s & c & E & Hs & Hlen & Hc & Hv).
rewrite E. eexists; split; [reflexivity|].
destruct (Z.eqb_spec c 0) as [->|Hc0].
- rewrite Z.mul_0_l, Z.add_0_r in Hv. split; [|exact Hv].
  destruct s as [|b s']; [exact nat_ok_nil|].
  apply nat_ok_iff_val; [exact Hs | discriminate|].
  rewrite Hlen, Hv.
  destruct n as [|n0 n']; [discriminate Hlen|].
  pose proof (proj1 (nat_ok_iff_val (n0 :: n') (proj1 Hn) ltac:(discriminate)) Hn) as Hlow.
  pose proof (val_nonneg _ (proj1 Hn)). nia.
- split.
  + split; [apply limbs_ok_app; [exact Hs | constructor; [lia | constructor]]|].
    right. rewrite length_app. cbn [length].
    replace (length s + 1 - 1)%nat with (length s) by lia.
    unfold Limbs.limb. now rewrite nth_middle.
  + rewrite val_app. cbn [Limbs.val]. rewrite Hlen. lia.
Qed.

Lemma pow5_loop_correct :
  forall i p, nat_ok p ->
  exists p', NatLimbs.pow5_loop i p = Some p' /\ nat_ok p' /\
  Limbs.val p' = Limbs.val p * (5 ^ 27) ^ Z.of_nat i.
Proof.
induction i as [|i IH]; intros p Hp.
- exists p. split; [reflexivity|]. split; [exact Hp|].
  cbn [Z.of_nat]. rewrite Z.pow_0_r. ring.
- cbn [NatLimbs.pow5_loop].
  destruct (mul_add_u64_correct p (5 ^ 27) 0 Hp ltac:(lia) ltac:(lia)) as (p1 & E & Hp1 & Hv1).
  rewrite E. destruct (IH p1 Hp1) as (p' & E' & Hp' & Hv').
  exists p'. split; [exact E'|]. split; [exact Hp'|].
  rewrite Hv', Hv1, Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma nat_pow5_correct :
  forall k, 0 <= k ->
  exists p, NatLimbs.pow5 k = Some p /\ nat_ok p /\ Limbs.val p = 5 ^ k.
Proof.
intros k Hk. unfold NatLimbs.pow5.
assert (Hr : 0 <= k mod 27 < 27) by (apply Z.mod_pos_bound; lia).
assert (H0 : nat_ok (5 ^ (k mod 27) :: nil)).
{ apply nat_ok_cons. split; [|split; [exact nat_ok_nil|]].
  - split; [apply Z.pow_nonneg; lia|].
    apply Z.le_lt_trans with (5 ^ 26); [apply Z.pow_le_mono_r; lia | lia].
  - intros _. pose proof (Z.pow_pos_nonneg 5 (k mod 27) ltac:(lia) ltac:(lia)). lia. }
destruct (pow5_loop_correct (Z.to_nat (k / 27)) _ H0) as (p & E & Hp & Hv).
exists p. split; [exact E|]. split; [exact Hp|].
rewrite Hv. cbn [Limbs.val]. rewrite Z2Nat.id by (apply Z.div_pos; lia).
assert (Hq : 0 <= k / 27) by (apply Z.div_pos; lia).
rewrite Z.mul_0_r, Z.add_0_r, <- Z.pow_mul_r, <- Z.pow_add_r by lia.
f_equal. pose proof (Z.div_mod k 27 ltac:(lia)). lia.
Qed.

Lemma nat_div_rem_correct :
  forall x d, nat_ok x -> nat_ok d -> d <> nil ->
  exists q r, NatLimbs.div_rem x d = Some (q, r) /\ nat_ok q /\ nat_ok r /\
  Limbs.val q = Limbs.val x / Limbs.val d /\ Limbs.val r = Limbs.val x mod Limbs.val d.
Proof.
intros x d Hx Hd Hn. unfold NatLimbs.div_rem.
replace (NatLimbs.is_zero d) with false by (destruct d; [contradiction | reflexivity]).
assert (Hd0 : Limbs.val d <> 0) by (intros H; exact (Hn (nat_ok_val0 d Hd H))).
destruct (div_rem_correct x d (proj1 Hx) (proj1 Hd) Hd0)
  as (q & r & E & Hq & Hr & _ & _ & Vq & Vr).
rewrite E.
destruct (from_limbs_correct q Hq) as [Oq Eq], (from_limbs_correct r Hr) as [Or Er].
exists (NatLimbs.from_limbs q), (NatLimbs.from_limbs r).
split; [reflexivity|]. split; [exact Oq|]. split; [exact Or|]. split; lia.
Qed.

(** [Z.lor] of the low limb and the high limb shifted by 64 bits is their
    sum, as their bits are apart. *)
Lemma lor_low_high :
  forall lo hi, 0 <= lo < 2 ^ 64 -> Z.lor lo (hi * 2 ^ 64) = lo + hi * 2 ^ 64.
Proof.
intros lo hi Hlo.
assert (H0 : Z.land lo (hi * 2 ^ 64) = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n 64) as [Hn64|Hn64].
  - rewrite <- Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_spec_low by lia.
    apply Bool.andb_false_r.
  - rewrite <- (Z.mod_small lo (2 ^ 64)) by lia.
    rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
rewrite <- Z.lxor_lor by exact H0. symmetry. now apply Z.add_nocarry_lxor.
Qed.

Lemma pow10_correct :
  forall k, 0 <= k < 2 ^ 32 ->
  exists p, NatLimbs.pow10 k = Some p /\ nat_ok p /\ Limbs.val p = 10 ^ k.
Proof.
intros k Hk. unfold NatLimbs.pow10.
rewrite checked_u_some by lia.
destruct (nat_pow5_correct k ltac:(lia)) as (p & E & Hp & Hv). rewrite E.
destruct (nat_shl_correct p k Hp ltac:(lia)) as [Hok Hval].
exists (NatLimbs.shl p k). split; [reflexivity|]. split; [exact Hok|].
rewrite Hval, Hv, <- Z.pow_mul_l. reflexivity.
Qed.

Lemma pow10_lt_inv : forall d D, 0 <= D -> 10 ^ d < 10 ^ D -> d < D.
Proof. intros d D HD H. apply (Z.pow_lt_mono_r_iff 10); lia. Qed.

(** The loop of [digits10] from a [d] with [10^d <= n < 10^D]: each step
    raises [d] by one until [n < 10^(d + 1)], which is at [d = D - 1]. *)
Lemma digits10_loop_correct :
  forall n D, nat_ok n -> Limbs.val n < 10 ^ D -> 10 ^ (D - 1) <= Limbs.val n -> D < 2 ^ 32 ->
  forall fuel d, 0 <= d -> 10 ^ d <= Limbs.val n -> D - d <= Z.of_nat fuel ->
  NatLimbs.digits10_loop fuel n d = Some (D - 1).
Proof.
intros n D Hn Ha Hd HD.
assert (HD0 : 0 <= D).
{ destruct (Z.lt_ge_cases D 0) as [H|H]; [|exact H].
  rewrite (Z.pow_neg_r 10 D H) in Ha. pose proof (val_nonneg n (proj1 Hn)). lia. }
induction fuel as [|f IH]; intros d Hd0 Hdn Hf.
- exfalso. assert (d < D) by (apply pow10_lt_inv; lia). cbn [Z.of_nat] in Hf. lia.
- assert (HdD : d < D) by (apply pow10_lt_inv; lia).
  cbn [NatLimbs.digits10_loop]. rewrite checked_u_some by lia.
  destruct (pow10_correct (d + 1) ltac:(lia)) as (p & E & Hp & Hv). rewrite E.
  rewrite cmp_correct by first [exact (proj1 Hn) | exact (proj1 Hp)]. rewrite Hv.
  rewrite Nat2Z.inj_succ in Hf.
  destruct (Z.compare_spec (Limbs.val n) (10 ^ (d + 1))) as [H|H|H].
  + apply IH; lia.
  + assert (D - 1 < d + 1) by (apply pow10_lt_inv; lia). f_equal. lia.
  + apply IH; lia.
Qed.

(** [10^d0 <= 2^l] for [d0 = l * 1233 / 4096], as [10^1233 < 2^4096]. *)
Lemma pow10_le_pow2 : forall l, 0 <= l -> 10 ^ (l * 1233 / 4096) <= 2 ^ l.
Proof.
intros l Hl. set (d0 := l * 1233 / 4096).
assert (Hd0 : 0 <= d0) by (apply Z.div_pos; lia).
apply (proj2 (Z.pow_le_mono_l_iff (10 ^ d0) (2 ^ l) 1233
  ltac:(apply Z.pow_nonneg; lia) ltac:(apply Z.pow_nonneg; lia) ltac:(lia))).
rewrite <- !Z.pow_mul_r by lia.
apply Z.le_trans with (2 ^ (4096 * d0)).
- replace (d0 * 1233) with (1233 * d0) by ring. rewrite !Z.pow_mul_r by lia.
  apply Z.pow_le_mono_l. split; [apply Z.pow_nonneg; lia|].
  apply Z.lt_le_incl. vm_compute. reflexivity.
- apply Z.pow_le_mono_r; [lia|]. unfold d0.
  pose proof (Z.mul_div_le (l * 1233) 4096 ltac:(lia)). lia.
Qed.

Lemma nat_digits10_correct :
  forall n, nat_ok n -> Zdigits radix10 (Limbs.val n) < 2 ^ 32 ->
  NatLimbs.digits10 n = Some (Zdigits radix10 (Limbs.val n)).
Proof.
intros n Hn HD. unfold NatLimbs.digits10, NatLimbs.bits.
rewrite bit_len_correct by exact (proj1 Hn).
pose proof (val_nonneg n (proj1 Hn)) as Ha0.
pose proof (digits10_loop_correct n (Zdigits radix10 (Limbs.val n)) Hn) as Hloop.
revert Hloop HD Ha0. generalize (Limbs.val n) as a. intros a Hloop HD Ha0.
destruct (Z.eq_dec a 0) as [->|Ha]; [reflexivity|].
assert (Ha1 : 0 < a) by lia.
pose proof (Zdigits_correct radix10 a) as [D1 D2].
pose proof (Zdigits_gt_0 radix10 a Ha) as HD0.
rewrite Z.abs_eq in D1, D2 by lia.
change (radix_val radix10) with 10 in D1, D2.
revert Hloop HD D1 D2 HD0. generalize (Zdigits radix10 a) as D.
intros D Hloop HD D1 D2 HD0.
pose proof (Z.log2_spec a Ha1) as [L1 L2].
pose proof (Z.log2_nonneg a) as L0.
(* [a < 10^D <= 16^D = 2^(4 D)], so [log2 a < 4 D]. *)
assert (HL : Z.log2 a < 4 * D).
{ apply (proj1 (Z.log2_lt_pow2 a (4 * D) Ha1)).
  apply Z.lt_le_trans with (10 ^ D); [exact D2|].
  rewrite Z.pow_mul_r by lia. apply Z.pow_le_mono_l. change (2 ^ 4) with 16. lia. }
(* [2^(D - 1) <= 10^(D - 1) <= a < 2^(log2 a + 1)], so [D <= log2 a + 1]. *)
assert (HDL : D <= Z.log2 a + 1).
{ assert (H2 : 2 ^ (D - 1) < 2 ^ Z.succ (Z.log2 a)).
  { apply Z.le_lt_trans with (10 ^ (D - 1)); [apply Z.pow_le_mono_l; lia | lia]. }
  assert (H3 : 0 <= Z.succ (Z.log2 a)) by lia.
  pose proof (proj2 (Z.pow_lt_mono_r_iff 2 (D - 1) _ ltac:(lia) H3) H2). lia. }
unfold nat_bits. replace (a =? 0) with false by (symmetry; now apply Z.eqb_neq).
cbv beta iota zeta.
replace (Z.log2 a + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (Z.log2 a + 1 - 1) with (Z.log2 a) by ring.
rewrite (checked_u_some 64 (Z.log2 a)) by lia. cbv beta iota.
rewrite (checked_u_some 128 (Z.log2 a * 1233)) by lia. cbv beta iota.
(* The first guess [d0 = log2 a * 1233 / 4096]. *)
assert (Hd0 : 0 <= Z.log2 a * 1233 / 4096) by (apply Z.div_pos; lia).
pose proof (Z.mul_div_le (Z.log2 a * 1233) 4096 ltac:(lia)) as Hd1.
rewrite (checked_u_some 64 (Z.log2 a * 1233 / 4096)) by lia. cbv beta iota.
assert (Hdn : 10 ^ (Z.log2 a * 1233 / 4096) <= a).
{ pose proof (pow10_le_pow2 (Z.log2 a) L0). lia. }
assert (Hf : D - Z.log2 a * 1233 / 4096 <= Z.of_nat (S (Z.to_nat (Z.log2 a + 1)))).
{ rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia. }
rewrite (Hloop D2 D1 HD _ _ Hd0 Hdn Hf).
replace (D - 1 + 1) with D by ring. apply checked_u_some. lia.
Qed.

(** ** The operations on the [Z]s that [Nat]s hold *)

Lemma mul_z_correct : forall a b, 0 <= a -> 0 <= b -> NatLimbs.mul_z a b = Some (a * b).
Proof.
intros a b Ha Hb. unfold NatLimbs.mul_z.
destruct (to_limbs_correct a Ha) as [Oa Va], (to_limbs_correct b Hb) as [Ob Vb].
destruct (nat_mul_correct _ _ Oa Ob) as (z & E & _ & Vz).
rewrite E, Vz, Va, Vb. reflexivity.
Qed.

Lemma shl_z_correct : forall a s, 0 <= a -> 0 <= s < 2 ^ 64 -> NatLimbs.shl_z a s = Z.shiftl a s.
Proof.
intros a s Ha Hs. unfold NatLimbs.shl_z.
destruct (to_limbs_correct a Ha) as [Oa Va].
destruct (nat_shl_correct _ s Oa ltac:(lia)) as [_ V].
rewrite V, Va, Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma div_rem_z_correct :
  forall a b, 0 <= a -> 0 < b -> NatLimbs.div_rem_z a b = Some (a / b, a mod b).
Proof.
intros a b Ha Hb. unfold NatLimbs.div_rem_z.
destruct (to_limbs_correct a Ha) as [Oa Va], (to_limbs_correct b ltac:(lia)) as [Ob Vb].
assert (Hn : NatLimbs.to_limbs b <> nil) by (rewrite to_limbs_nil; lia).
destruct (nat_div_rem_correct _ _ Oa Ob Hn) as (q & r & E & _ & _ & Vq & Vr).
rewrite E, Vq, Vr, Va, Vb. reflexivity.
Qed.

(** [assert!(!d.is_zero(), "division by zero")] *)
Lemma div_rem_z_zero : forall a, NatLimbs.div_rem_z a 0 = None.
Proof.
intros a. unfold NatLimbs.div_rem_z, NatLimbs.div_rem.
replace (NatLimbs.to_limbs 0) with (@nil Z) by reflexivity. reflexivity.
Qed.

Lemma bits_z_correct : forall a, 0 <= a -> NatLimbs.bits_z a = nat_bits a.
Proof.
intros a Ha. unfold NatLimbs.bits_z, NatLimbs.bits.
destruct (to_limbs_correct a Ha) as [Oa Va].
rewrite bit_len_correct by exact (proj1 Oa). now rewrite Va.
Qed.

Lemma is_zero_z_correct : forall a, 0 <= a -> NatLimbs.is_zero_z a = (a =? 0).
Proof.
intros a Ha. unfold NatLimbs.is_zero_z. pose proof (to_limbs_nil a Ha) as H.
destruct (NatLimbs.to_limbs a) as [|b l]; cbn [NatLimbs.is_zero].
- symmetry. apply Z.eqb_eq. now apply H.
- symmetry. apply Z.eqb_neq. intros E. apply H in E. discriminate.
Qed.

Lemma low_u128_z_correct : forall a, 0 <= a -> NatLimbs.low_u128_z a = a mod 2 ^ 128.
Proof.
intros a Ha. unfold NatLimbs.low_u128_z, NatLimbs.low_u128.
destruct (to_limbs_correct a Ha) as [Oa Va].
rewrite !limb_val by exact (proj1 Oa). rewrite Va.
change (2 ^ (64 * Z.of_nat 0)) with 1. change (2 ^ (64 * Z.of_nat 1)) with (2 ^ 64).
rewrite Z.div_1_r, Z.shiftl_mul_pow2 by lia.
pose proof (Z.mod_pos_bound (a / 2 ^ 64) (2 ^ 64) ltac:(lia)) as B.
rewrite (Z.mod_small ((a / 2 ^ 64) mod 2 ^ 64 * 2 ^ 64)) by lia.
rewrite lor_low_high by (apply Z.mod_pos_bound; lia).
change (2 ^ 128) with (2 ^ 64 * 2 ^ 64).
rewrite Z.rem_mul_r by lia. ring.
Qed.

Lemma pow5_z_correct : forall k, 0 <= k < 2 ^ 32 -> NatLimbs.pow5_z k = Some (5 ^ k).
Proof.
intros k Hk. unfold NatLimbs.pow5_z.
destruct (nat_pow5_correct k ltac:(lia)) as (p & E & _ & V).
rewrite E, V. reflexivity.
Qed.

Lemma add_z_correct : forall a b, 0 <= a -> 0 <= b -> NatLimbs.add_z a b = a + b.
Proof.
intros a b Ha Hb. unfold NatLimbs.add_z, NatLimbs.add.
destruct (to_limbs_correct a Ha) as [Oa Va], (to_limbs_correct b Hb) as [Ob Vb].
(* The sum of [x] and [y], with [y] no longer than [x], fits the limbs of
   [x] and one limb more, so that no carry leaves it. *)
assert (Hadd : forall x y, nat_ok x -> nat_ok y -> (length y <= length x)%nat ->
  Limbs.val (NatLimbs.from_limbs (fst (Limbs.add_assign (x ++ 0 :: nil) y))) =
  Limbs.val x + Limbs.val y).
{ intros x y Hx Hy Hl.
  assert (Hx0 : limbs_ok (x ++ 0 :: nil))
    by (apply limbs_ok_app; [exact (proj1 Hx) | constructor; [lia | constructor]]).
  destruct (Limbs.add_assign (x ++ 0 :: nil) y) as [s c] eqn:E.
  destruct (add_assign_correct _ _ s c Hx0 (proj1 Hy) ltac:(rewrite length_app; cbn; lia) E)
    as (Hs & _ & Hv).
  cbn [fst]. destruct (from_limbs_correct s Hs) as [_ ->].
  rewrite val_app in Hv. cbn [Limbs.val] in Hv. rewrite length_app in Hv. cbn [length] in Hv.
  pose proof (val_bounds x (proj1 Hx)) as [X0 X1].
  pose proof (val_bounds y (proj1 Hy)) as [Y0 Y1].
  pose proof (val_nonneg s Hs) as S0.
  assert (Hyx : 2 ^ (64 * Z.of_nat (length y)) <= 2 ^ (64 * Z.of_nat (length x)))
    by (apply Z.pow_le_mono_r; lia).
  replace (64 * Z.of_nat (length x + 1)) with (64 * Z.of_nat (length x) + 64) in Hv by lia.
  rewrite Z.pow_add_r in Hv by lia.
  destruct c; cbn [Z.b2z] in Hv; [|lia].
  exfalso. nia. }
destruct (Nat.leb_spec (length (NatLimbs.to_limbs b)) (length (NatLimbs.to_limbs a))) as [H|H].
- rewrite Hadd, Va, Vb by first [assumption | lia]. reflexivity.
- rewrite Hadd, Va, Vb by first [assumption | lia]. ring.
Qed.

Lemma from_u64_z_correct : forall x, 0 <= x < 2 ^ 64 -> NatLimbs.from_u64_z x = x.
Proof.
intros x Hx. unfold NatLimbs.from_u64_z, NatLimbs.from_u64.
assert (H : limbs_ok (x :: nil)) by (constructor; [lia | constructor]).
destruct (from_limbs_correct _ H) as [_ ->]. cbn [Limbs.val]. ring.
Qed.

(** [digits10] tests [pow10(d + 1)] up to the number of digits, which
    [u32::try_from] needs below [2^32]. *)
Lemma digits10_z_correct :
  forall a,
  0 <= a -> Zdigits radix10 a < 2 ^ 32 -> NatLimbs.digits10_z a = Some (Zdigits radix10 a).
Proof.
intros a Ha HD. unfold NatLimbs.digits10_z.
destruct (to_limbs_correct a Ha) as [Oa Va].
rewrite nat_digits10_correct, Va; [reflexivity | exact Oa | now rewrite Va].
Qed.
