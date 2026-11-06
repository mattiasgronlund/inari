(** * π in the dyadic kernel

    The table [PI] of [DyadicConsts] in [Model.v] is [floor(π * 2^4222)].
    Machin's formula [π = 16 atan(1/5) - 4 atan(1/239)] (Stdlib's
    [Machin_4_5_239]) gives it: [azsum] sums the alternating series of
    [2^4288 atan(1/q)] in integers, each term a floor, so that 925 terms
    for [q = 5] and 272 for [q = 239] are each within 1 of the real terms,
    and the remainders of [atan_tail_bounds] of [AtanSeries.v] are below
    1. [vm_compute] of the two sums bounds [2^4288 π] within
    [16 * 926 + 4 * 273] of an integer, tightly enough to show that the
    table and the next integer bracket [2^4222 π] ([PI_bounds]). [pi n]
    is [[h, h] + l] with the split of [DyConst.v], checked at each of the
    64 levels by [vm_compute] as there ([pi_correct]).

    As in [DyConst.v], the 4,288-bit numbers stay behind variables in
    every lemma that a tactic other than [vm_compute] works on, and in the
    [Z] products that [vm_compute] evaluates, the power of two comes
    first. *)

From Stdlib Require Import ZArith Reals Machin Lra Lia List Bool.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary DyRound DyConv DyOps DyDriver DyGrow
  AtanhSeries DyConst DyLog AtanSeries.

Open Scope Z_scope.

(** ** The alternating sums in integer fixed point *)

(** [Σ_{i < n} (-1)^i floor(u_i / (2 (i0 + i) + 1))] for [u_0 = u] and
    [u_(i+1) = floor(u_i / q2)]: with [u = floor(2^P / q)] and [q2 = q^2],
    each term is [floor(2^P / (q^(2i+1) (2i+1)))], as in [zsum] of
    [AtanhSeries.v], with alternating signs. *)
Fixpoint azsum (q2 u i : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S m => u / (2 * i + 1) - azsum q2 (u / q2) (i + 1) m
  end.

(** [Σ_{i < n} (-1)^i x^(2 (i0 + i) + 1) / (2 (i0 + i) + 1)], recursive at
    the front as [azsum] is *)
Fixpoint at_tsum (i0 n : nat) (x : R) : R :=
  match n with
  | O => 0
  | S m => x ^ (2 * i0 + 1) / INR (2 * i0 + 1) - at_tsum (S i0) m x
  end.

Lemma at_tsum_last :
  forall n i0 x,
  at_tsum i0 (S n) x =
  (at_tsum i0 n x + (-1) ^ n * x ^ (2 * (i0 + n) + 1) / INR (2 * (i0 + n) + 1))%R.
Proof.
induction n as [| m IH]; intros i0 x.
- cbn [at_tsum]. rewrite Nat.add_0_r, pow_O. unfold Rdiv. ring.
- change (at_tsum i0 (S (S m)) x)
    with (x ^ (2 * i0 + 1) / INR (2 * i0 + 1) - at_tsum (S i0) (S m) x)%R.
  rewrite (IH (S i0)). cbn [at_tsum]. replace (S i0 + m)%nat with (i0 + S m)%nat by lia.
  replace ((-1) ^ S m)%R with (- (-1) ^ m)%R by (simpl; ring).
  (* [ring] does not see through [Rdiv] of a product here. *)
  unfold Rdiv. ring.
Qed.

Lemma at_tsum_atan_sum : forall n x, atan_sum n x = at_tsum 0 n x.
Proof.
induction n as [| m IH]; intros x; [reflexivity |].
rewrite at_tsum_last, <- IH. reflexivity.
Qed.

(** Each of the [n] floors is at most 1 below the real term, so the sum
    is within [n] of the real one, whatever the signs. *)
Lemma azsum_tsum :
  forall q P, 2 <= q -> 0 <= P ->
  forall n i0 u, u = 2 ^ P / q ^ Z.of_nat (2 * i0 + 1) ->
  (IZR (azsum (q * q) u (Z.of_nat i0) n) - INR n <= bpow radix2 P * at_tsum i0 n (/ IZR q) <=
   IZR (azsum (q * q) u (Z.of_nat i0) n) + INR n)%R.
Proof.
intros q P Hq HP n. induction n as [| m IH]; intros i0 u Hu.
- cbn [azsum at_tsum]. simpl INR. lra.
- cbn [azsum at_tsum].
  assert (HQ : 0 < q ^ Z.of_nat (2 * i0 + 1)) by (apply Z.pow_pos_nonneg; lia).
  (* The next [u] is [2^P / q^(2 i0 + 3)]. *)
  assert (Hu' : u / (q * q) = 2 ^ P / q ^ Z.of_nat (2 * S i0 + 1)).
  { rewrite Hu, Z.div_div by lia. f_equal.
    replace (Z.of_nat (2 * S i0 + 1)) with (Z.of_nat (2 * i0 + 1) + 2) by lia.
    rewrite Z.pow_add_r by lia. ring. }
  replace (Z.of_nat i0 + 1) with (Z.of_nat (S i0)) by lia.
  specialize (IH (S i0) _ Hu').
  pose proof (as_term_bounds q P (2 * i0 + 1) Hq HP ltac:(lia)) as Ht.
  replace (2 * Z.of_nat i0 + 1) with (Z.of_nat (2 * i0 + 1)) by lia.
  rewrite <- Hu in Ht.
  rewrite minus_IZR, S_INR, Rmult_minus_distr_l. lra.
Qed.

(** With [q^(2n+1)] above [2^P], the remainder after [n] terms, times
    [2^P], is below 1 in magnitude, so [2^P atan(1/q)] is within [n + 1]
    of the sum. *)
Lemma azsum_bounds :
  forall q P n,
  2 <= q -> 0 <= P -> 2 ^ P < q ^ Z.of_nat (2 * n + 1) ->
  (IZR (azsum (q * q) (2 ^ P / q) 0 n) - INR n - 1 < bpow radix2 P * atan (/ IZR q) <
   IZR (azsum (q * q) (2 ^ P / q) 0 n) + INR n + 1)%R.
Proof.
intros q P n Hq HP H.
pose proof (azsum_tsum q P Hq HP n 0 (2 ^ P / q)) as Hz.
change (Z.of_nat (2 * 0 + 1)) with 1 in Hz. rewrite Z.pow_1_r in Hz.
specialize (Hz eq_refl). change (Z.of_nat 0) with 0 in Hz.
rewrite <- at_tsum_atan_sum in Hz.
assert (Hq0 : (2 <= IZR q)%R) by (apply IZR_le; exact Hq).
assert (Hx : (0 < / IZR q)%R) by (apply Rinv_0_lt_compat; lra).
assert (HQ : 0 < q ^ Z.of_nat (2 * n + 1)) by (apply Z.pow_pos_nonneg; lia).
assert (HB : (0 < bpow radix2 P)%R) by apply bpow_gt_0.
(* [2^P q^-(2n+1) < 1], as in [dc_tail] *)
assert (Hb : (bpow radix2 P * (/ IZR q) ^ (2 * n + 1) < 1)%R).
{ assert (HP2 : bpow radix2 P = IZR (2 ^ P)) by (symmetry; exact (IZR_Zpower radix2 P HP)).
  rewrite HP2, pow_inv, pow_IZR.
  apply IZR_lt in H. apply IZR_lt in HQ.
  apply (Rmult_lt_reg_r (IZR (q ^ Z.of_nat (2 * n + 1)))); [exact HQ |].
  rewrite Rmult_assoc, Rinv_l by lra. lra. }
destruct (atan_tail_bounds n (/ IZR q)) as (T & [HT0 HT1] & HT).
assert (HT2 : (T <= 1)%R).
{ assert (Hk : (1 <= INR (2 * n + 1))%R)
    by (rewrite plus_INR, mult_INR; simpl INR; pose proof (pos_INR n); lra).
  assert (/ INR (2 * n + 1) <= 1)%R by (rewrite <- Rinv_1; apply Rinv_le_contravar; lra).
  unfold Rdiv in HT1. lra. }
assert (Hxn : (0 < (/ IZR q) ^ (2 * n + 1))%R) by (apply pow_lt; exact Hx).
(* The remainder [D] has magnitude [T q^-(2n+1)], as [(-1)^n] has 1. *)
set (D := (atan (/ IZR q) - atan_sum n (/ IZR q))%R) in HT |- *.
assert (HD : (Rabs D = T * (/ IZR q) ^ (2 * n + 1))%R).
{ replace (Rabs D) with (Rabs ((-1) ^ n * D)) by (rewrite Rabs_mult, pow_1_abs; ring).
  rewrite <- HT. apply Rabs_pos_eq. apply Rmult_le_pos; lra. }
assert (HTx : (bpow radix2 P * (T * (/ IZR q) ^ (2 * n + 1)) < 1)%R).
{ apply (Rle_lt_trans _ (bpow radix2 P * (/ IZR q) ^ (2 * n + 1))); [| exact Hb].
  apply Rmult_le_compat_l; [lra |].
  rewrite <- (Rmult_1_l ((/ IZR q) ^ (2 * n + 1))) at 2.
  apply Rmult_le_compat_r; lra. }
assert (H1 : (bpow radix2 P * D <= bpow radix2 P * Rabs D)%R)
  by (apply Rmult_le_compat_l; [lra | apply Rle_abs]).
assert (H2 : (bpow radix2 P * - D <= bpow radix2 P * Rabs D)%R).
{ apply Rmult_le_compat_l; [lra |]. rewrite <- Rabs_Ropp. apply Rle_abs. }
rewrite HD in H1, H2.
assert (E : (bpow radix2 P * atan (/ IZR q) =
             bpow radix2 P * atan_sum n (/ IZR q) + bpow radix2 P * D)%R)
  by (unfold D; ring).
rewrite E. lra.
Qed.

(** ** The table is the floor *)

(** What the table [t] must satisfy against the sums [s5] of
    [2^4288 atan(1/5)] (925 terms) and [s239] of [2^4288 atan(1/239)]
    (272 terms): with [2^4288 π = 16 * 2^4288 atan(1/5) - 4 * 2^4288 atan(1/239)]
    within [16 * 926 + 4 * 273] of [16 s5 - 4 s239], the table times
    [2^66] and the next integer bracket these bounds. *)
Definition dp_table_okb (t s5 s239 : Z) : bool :=
  (2 ^ 66 * t + (16 * 926 + 4 * 273) <=? 16 * s5 - 4 * s239) &&
  (16 * s5 - 4 * s239 + (16 * 926 + 4 * 273) <=? 2 ^ 66 * (t + 1)).

Lemma dp_table_ok_true :
  dp_table_okb (Limbs.val DyadicConsts.PI)
    (azsum (5 * 5) (2 ^ 4288 / 5) 0 925) (azsum (239 * 239) (2 ^ 4288 / 239) 0 272) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma dp_table_spec :
  forall t s5 s239, dp_table_okb t s5 s239 = true ->
  2 ^ 66 * t + (16 * 926 + 4 * 273) <= 16 * s5 - 4 * s239 /\
  16 * s5 - 4 * s239 + (16 * 926 + 4 * 273) <= 2 ^ 66 * (t + 1).
Proof.
intros t s5 s239 H. unfold dp_table_okb in H.
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2.
exact (conj H1 H2).
Qed.

(** [5^1851] and [239^545] exceed [2^4288]. *)
Lemma dp_pow5 : 2 ^ 4288 < 5 ^ Z.of_nat (2 * 925 + 1).
Proof. apply (proj1 (Z.ltb_lt _ _)). vm_cast_no_check (eq_refl true). Qed.

Lemma dp_pow239 : 2 ^ 4288 < 239 ^ Z.of_nat (2 * 272 + 1).
Proof. apply (proj1 (Z.ltb_lt _ _)). vm_cast_no_check (eq_refl true). Qed.

(** [2^-4222 π] from the sums [s5] and [s239], with [t] for the table:
    [π = 16 atan(1/5) - 4 atan(1/239)], and [2^4288 = 2^66 2^4222]. *)
Lemma dp_pi_gen :
  forall (t s5 s239 : Z),
  2 ^ 66 * t + (16 * 926 + 4 * 273) <= 16 * s5 - 4 * s239 ->
  16 * s5 - 4 * s239 + (16 * 926 + 4 * 273) <= 2 ^ 66 * (t + 1) ->
  (IZR s5 - INR 925 - 1 < bpow radix2 4288 * atan (/ IZR 5) < IZR s5 + INR 925 + 1)%R ->
  (IZR s239 - INR 272 - 1 < bpow radix2 4288 * atan (/ IZR 239) <
   IZR s239 + INR 272 + 1)%R ->
  (IZR t * bpow radix2 (-4222) <= PI < (IZR t + 1) * bpow radix2 (-4222))%R.
Proof.
intros t s5 s239 H1 H2 H5 H239.
assert (Hn5 : INR 925 = 925%R) by (rewrite INR_IZR_INZ; reflexivity).
assert (Hn239 : INR 272 = 272%R) by (rewrite INR_IZR_INZ; reflexivity).
rewrite Hn5 in H5. rewrite Hn239 in H239.
apply IZR_le in H1, H2.
rewrite !plus_IZR, !minus_IZR, !mult_IZR, IZR_pow2 in H1 by lia.
rewrite !plus_IZR, !minus_IZR, !mult_IZR, !plus_IZR, IZR_pow2 in H2 by lia.
assert (HB : (bpow radix2 (-4222) = / bpow radix2 4222)%R) by exact (bpow_opp radix2 4222).
assert (HC : (bpow radix2 66 * bpow radix2 4222 = bpow radix2 4288)%R)
  by (rewrite <- bpow_plus; reflexivity).
assert (HPI : (PI = 16 * atan (/ IZR 5) - 4 * atan (/ IZR 239))%R)
  by (pose proof Machin_4_5_239; lra).
rewrite HB.
apply (dc_floor (IZR t) PI (bpow radix2 4222) (bpow radix2 66)
         (16 * IZR s5 - 4 * IZR s239 - (16 * 926 + 4 * 273))
         (16 * IZR s5 - 4 * IZR s239 + (16 * 926 + 4 * 273)));
  [apply bpow_gt_0 | apply bpow_gt_0 | lra | lra |].
rewrite <- Rmult_assoc, HC, HPI.
replace (bpow radix2 4288 * (16 * atan (/ IZR 5) - 4 * atan (/ IZR 239)))%R
  with (16 * (bpow radix2 4288 * atan (/ IZR 5)) -
        4 * (bpow radix2 4288 * atan (/ IZR 239)))%R by ring.
lra.
Qed.

Lemma PI_bounds :
  (IZR (Limbs.val DyadicConsts.PI) * bpow radix2 (-4222) <= PI <
   (IZR (Limbs.val DyadicConsts.PI) + 1) * bpow radix2 (-4222))%R.
Proof.
destruct (dp_table_spec _ _ _ dp_table_ok_true) as [H1 H2].
exact (dp_pi_gen _ _ _ H1 H2 (azsum_bounds 5 4288 925 ltac:(lia) ltac:(lia) dp_pow5)
         (azsum_bounds 239 4288 272 ltac:(lia) ltac:(lia) dp_pow239)).
Qed.

(** ** [split] at each level *)

(** All 64 levels of [pi] *)
Definition dp_level_okb (n : nat) : bool :=
  dc_split_okb n (Limbs.val DyadicConsts.PI) 4222 (DyadicConsts.split n DyadicConsts.PI (-4222) 0).

Lemma dp_levels_ok_true : forallb dp_level_okb (seq 1 64) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma pi_correct :
  forall n p,
  level_ok n -> DyadicConsts.pi n = Some p ->
  encl_ok n p /\ encl_le (2 ^ 15) p /\ encl_has p PI.
Proof.
intros n p Hn Hp. unfold DyadicConsts.pi in Hp. revert Hp.
destruct (DyadicConsts.split n DyadicConsts.PI (-4222) 0) as [[h l] |] eqn:E;
  intros Hp; [| discriminate Hp].
assert (Hin : In n (seq 1 64)) by (apply in_seq; unfold level_ok in Hn; lia).
pose proof (proj1 (forallb_forall dp_level_okb (seq 1 64)) dp_levels_ok_true n Hin) as H.
unfold dp_level_okb in H. rewrite E in H.
destruct (dc_split_correct n _ 4222 h l PI H ltac:(unfold dc_K; lia) PI_bounds)
  as (Hh & Heh & Hl & HEl & Hhl).
exact (split_sum n h l p PI Hn Hh Heh Hl HEl Hhl Hp).
Qed.
