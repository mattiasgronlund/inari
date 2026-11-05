(** * The series of atanh, and ln 2 and ln 10 from it

    [atanh x = x + x^3 / 3 + x^5 / 5 + ...] for [0 <= x < 1], with the
    remainder after [n] terms between 0 and [x^(2n+1) / (1 - x^2)]
    ([atanh_sum_bounds]), by the mean value theorem on [atanh] minus the
    partial sum, whose derivative is [x^(2n) / (1 - x^2)]. With
    [ln 2 = 2 atanh(1/3)] and [ln 10 = 3 ln 2 + 2 atanh(1/9)], the sums
    in integer fixed point of [zsum] bound [ln 2] and [ln 10] at any
    precision, which [DyConst.v] computes with [vm_compute]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core.
From Inari Require Import Elementary.

Open Scope R_scope.

(** [Σ_{i < n} x^(2i+1) / (2i+1)] *)
Fixpoint atanh_sum (n : nat) (x : R) : R :=
  match n with
  | O => 0
  | S m => atanh_sum m x + x ^ (2 * m + 1) / INR (2 * m + 1)
  end.

(** ** The remainder of the series *)

(** [Σ_{i < n} x^(2i)], the derivative of [atanh_sum n] *)
Fixpoint as_geo_sum (n : nat) (x : R) : R :=
  match n with
  | O => 0
  | S m => as_geo_sum m x + x ^ (2 * m)
  end.

Lemma as_geo_sum_eq : forall n x, as_geo_sum n x * (1 - x ^ 2) = 1 - x ^ (2 * n).
Proof.
induction n as [| m IH]; intros x; cbn [as_geo_sum].
- simpl. ring.
- replace (2 * S m)%nat with (2 * m + 2)%nat by lia. rewrite pow_add.
  rewrite Rmult_plus_distr_r, IH. ring.
Qed.

Lemma as_derive_eq :
  forall f x l l', derivable_pt_lim f x l -> l = l' -> derivable_pt_lim f x l'.
Proof. intros f x l l' H <-. exact H. Qed.

Lemma as_sum_derive : forall n x, derivable_pt_lim (atanh_sum n) x (as_geo_sum n x).
Proof.
induction n as [| m IH]; intros x.
- apply (derivable_pt_lim_ext (fct_cte 0)); [intros z; reflexivity |].
  apply derivable_pt_lim_const.
- apply (derivable_pt_lim_ext
           (atanh_sum m + mult_real_fct (/ INR (2 * m + 1)) (fun y => y ^ (2 * m + 1)))%F).
  { intros z. unfold plus_fct, mult_real_fct. cbn [atanh_sum]. unfold Rdiv. ring. }
  eapply as_derive_eq.
  + apply derivable_pt_lim_plus; [apply IH |].
    apply derivable_pt_lim_scal. apply derivable_pt_lim_pow.
  + cbn [as_geo_sum]. replace (Init.Nat.pred (2 * m + 1)) with (2 * m)%nat by lia.
    field. apply not_0_INR. lia.
Qed.

(** The derivative of [atanh] is [1 / (1 - x^2)]. *)
Lemma as_atanh_derive : forall c, -1 < c < 1 -> derivable_pt_lim Ratanh c (/ (1 - c ^ 2)).
Proof.
intros c Hc.
assert (H1 : 0 < 1 - c) by lra. assert (H2 : 0 < 1 + c) by lra.
assert (H3 : 0 < 1 - c ^ 2) by nra.
apply (derivable_pt_lim_ext
         (mult_real_fct (/ 2) (comp ln ((fct_cte 1 + id) / (fct_cte 1 - id))%F))).
{ intros z. unfold mult_real_fct, comp, div_fct, plus_fct, minus_fct, fct_cte, id, Ratanh.
  unfold Rdiv. ring. }
eapply as_derive_eq.
- apply derivable_pt_lim_scal. apply derivable_pt_lim_comp.
  + apply derivable_pt_lim_div.
    * apply derivable_pt_lim_plus; [apply derivable_pt_lim_const | apply derivable_pt_lim_id].
    * apply derivable_pt_lim_minus; [apply derivable_pt_lim_const | apply derivable_pt_lim_id].
    * unfold minus_fct, fct_cte, id. lra.
  + apply derivable_pt_lim_ln. unfold div_fct, plus_fct, minus_fct, fct_cte, id.
    apply Rdiv_lt_0_compat; lra.
- unfold div_fct, plus_fct, minus_fct, fct_cte, id, Rsqr. field. lra.
Qed.

Lemma atanh_sum_bounds :
  forall n x, 0 <= x < 1 ->
  0 <= Ratanh x - atanh_sum n x <= x ^ (2 * n + 1) / (1 - x ^ 2).
Proof.
intros n x Hx.
assert (Hx2 : 0 < 1 - x ^ 2) by nra.
assert (Ha : Ratanh 0 = 0).
{ unfold Ratanh. replace ((1 + 0) / (1 - 0)) with 1 by field. rewrite ln_1. lra. }
assert (Hs : forall m, atanh_sum m 0 = 0).
{ induction m as [| m IH]; cbn [atanh_sum]; [reflexivity |].
  rewrite IH, pow_i by lia. unfold Rdiv. ring. }
destruct (Req_dec x 0) as [-> | Hx0].
- (* At 0 both sides are 0. *)
  rewrite Ha, Hs, pow_i by lia. unfold Rdiv. lra.
- (* The mean value theorem on [0, x]: the difference is [c^(2n) / (1 - c^2) * x]. *)
  assert (Hd : forall c, 0 <= c <= x ->
            derivable_pt_lim (fun r => Ratanh r - atanh_sum n r) c
              ((fun r => r ^ (2 * n) / (1 - r ^ 2)) c)).
  { intros c Hc. cbv beta.
    apply (derivable_pt_lim_ext (Ratanh - atanh_sum n)%F); [intros z; reflexivity |].
    eapply as_derive_eq.
    - apply derivable_pt_lim_minus; [apply as_atanh_derive; lra | apply as_sum_derive].
    - assert (Hq : 0 < 1 - c ^ 2) by nra.
      pose proof (as_geo_sum_eq n c) as Hg.
      replace (as_geo_sum n c) with ((1 - c ^ (2 * n)) / (1 - c ^ 2))
        by (rewrite <- Hg; field; lra).
      field. lra. }
  destruct (MVT_cor2 (fun r => Ratanh r - atanh_sum n r)
              (fun r => r ^ (2 * n) / (1 - r ^ 2)) 0 x ltac:(lra) Hd) as (c & Hc & Hc0).
  cbv beta in Hc.
  rewrite Ha, Hs in Hc. repeat rewrite Rminus_0_r in Hc. rewrite Hc.
  assert (Hc2 : 0 < 1 - c ^ 2) by nra.
  assert (Hp : 0 <= c ^ (2 * n)) by (apply pow_le; lra).
  assert (Hpx : c ^ (2 * n) <= x ^ (2 * n)) by (apply pow_incr; lra).
  assert (Hi : / (1 - c ^ 2) <= / (1 - x ^ 2)).
  { apply Rinv_le_contravar; [exact Hx2 |].
    assert (c ^ 2 <= x ^ 2) by (apply pow_incr; lra). lra. }
  assert (Hi0 : 0 < / (1 - c ^ 2)) by (apply Rinv_0_lt_compat; exact Hc2).
  assert (Hm : c ^ (2 * n) * / (1 - c ^ 2) <= x ^ (2 * n) * / (1 - x ^ 2))
    by (apply Rmult_le_compat; lra).
  assert (Hm0 : 0 <= c ^ (2 * n) * / (1 - c ^ 2)) by (apply Rmult_le_pos; lra).
  rewrite pow_add, pow_1. unfold Rdiv. split.
  + apply Rmult_le_pos; lra.
  + replace (x ^ (2 * n) * x * / (1 - x ^ 2)) with (x ^ (2 * n) * / (1 - x ^ 2) * x) by ring.
    apply Rmult_le_compat_r; lra.
Qed.

(** ** ln 2 and ln 10 *)

Lemma ln2_atanh : ln 2 = 2 * Ratanh (1 / 3).
Proof.
unfold Ratanh. replace ((1 + 1 / 3) / (1 - 1 / 3)) with 2 by field. field.
Qed.

Lemma ln10_atanh : ln 10 = 3 * ln 2 + 2 * Ratanh (1 / 9).
Proof.
unfold Ratanh. replace ((1 + 1 / 9) / (1 - 1 / 9)) with (5 / 4) by field.
replace 10 with (2 * 2 * 2 * (5 / 4)) by field.
rewrite !ln_mult by lra. field.
Qed.

(** ** The sums in integer fixed point *)

(** [Σ_{i < n} floor(u_i / (2 (i0 + i) + 1))] for [u_0 = u] and
    [u_(i+1) = floor(u_i / q2)]: with [u = floor(2^P / q)] and [q2 = q^2],
    each term is [floor(2^P / (q^(2i+1) (2i+1)))]. *)
Fixpoint zsum (q2 u i : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S m => (u / (2 * i + 1) + zsum q2 (u / q2) (i + 1) m)%Z
  end.

(** [Σ_{i < n} x^(2 (i0 + i) + 1) / (2 (i0 + i) + 1)], recursive at the
    front as [zsum] is *)
Fixpoint as_tsum (i0 n : nat) (x : R) : R :=
  match n with
  | O => 0
  | S m => x ^ (2 * i0 + 1) / INR (2 * i0 + 1) + as_tsum (S i0) m x
  end.

Lemma as_tsum_last :
  forall n i0 x,
  as_tsum i0 (S n) x = as_tsum i0 n x + x ^ (2 * (i0 + n) + 1) / INR (2 * (i0 + n) + 1).
Proof.
induction n as [| m IH]; intros i0 x.
- cbn [as_tsum]. rewrite Nat.add_0_r. ring.
- change (as_tsum i0 (S (S m)) x)
    with (x ^ (2 * i0 + 1) / INR (2 * i0 + 1) + as_tsum (S i0) (S m) x).
  rewrite IH. cbn [as_tsum]. replace (S i0 + m)%nat with (i0 + S m)%nat by lia. ring.
Qed.

Lemma as_tsum_atanh_sum : forall n x, atanh_sum n x = as_tsum 0 n x.
Proof.
induction n as [| m IH]; intros x; [reflexivity |].
rewrite as_tsum_last, <- IH. reflexivity.
Qed.

(** One term: [floor(floor(2^P / q^k) / k)] is the floor of the real
    [2^P x^k / k] for [x = 1 / q]. *)
Lemma as_term_bounds :
  forall q P k, (2 <= q)%Z -> (0 <= P)%Z -> (1 <= k)%nat ->
  IZR (2 ^ P / q ^ Z.of_nat k / Z.of_nat k) <= bpow radix2 P * ((/ IZR q) ^ k / INR k) <
  IZR (2 ^ P / q ^ Z.of_nat k / Z.of_nat k) + 1.
Proof.
intros q P k Hq HP Hk.
assert (HQ : (0 < q ^ Z.of_nat k)%Z) by (apply Z.pow_pos_nonneg; lia).
assert (HK : (0 < Z.of_nat k)%Z) by lia.
assert (HD : (0 < q ^ Z.of_nat k * Z.of_nat k)%Z) by lia.
rewrite Z.div_div by lia.
set (D := (q ^ Z.of_nat k * Z.of_nat k)%Z) in *.
set (f := (2 ^ P / D)%Z).
assert (Hf1 : (D * f <= 2 ^ P)%Z) by (apply Z.mul_div_le; lia).
assert (Hf2 : (2 ^ P < D * (f + 1))%Z) by (apply Z.mul_succ_div_gt; lia).
apply IZR_le in Hf1. apply IZR_lt in Hf2.
rewrite mult_IZR in Hf1. rewrite mult_IZR, plus_IZR in Hf2.
assert (HDR : 0 < IZR D) by (apply IZR_lt; lia).
(* The real term times [D] is [2^P]. *)
assert (Ht : bpow radix2 P * ((/ IZR q) ^ k / INR k) * IZR D = IZR (2 ^ P)).
{ assert (HP2 : bpow radix2 P = IZR (2 ^ P)) by (symmetry; exact (IZR_Zpower radix2 P HP)).
  rewrite HP2. unfold D. rewrite mult_IZR, <- pow_IZR, <- INR_IZR_INZ.
  assert (0 < IZR q) by (apply IZR_lt; lia).
  assert (0 < INR k) by (apply lt_0_INR; lia).
  rewrite pow_inv. field. split; (lra || (apply pow_nonzero; lra)). }
split.
- apply (Rmult_le_reg_r (IZR D)); [exact HDR |]. rewrite Ht. lra.
- apply (Rmult_lt_reg_r (IZR D)); [exact HDR |]. rewrite Ht. lra.
Qed.

Lemma as_zsum_tsum :
  forall q P, (2 <= q)%Z -> (0 <= P)%Z ->
  forall n i0 u, u = (2 ^ P / q ^ Z.of_nat (2 * i0 + 1))%Z ->
  IZR (zsum (q * q) u (Z.of_nat i0) n) <= bpow radix2 P * as_tsum i0 n (/ IZR q) <=
  IZR (zsum (q * q) u (Z.of_nat i0) n) + INR n.
Proof.
intros q P Hq HP n. induction n as [| m IH]; intros i0 u Hu.
- cbn [zsum as_tsum]. simpl INR. lra.
- cbn [zsum as_tsum].
  assert (HQ : (0 < q ^ Z.of_nat (2 * i0 + 1))%Z) by (apply Z.pow_pos_nonneg; lia).
  (* The next [u] is [2^P / q^(2 i0 + 3)]. *)
  assert (Hu' : (u / (q * q))%Z = (2 ^ P / q ^ Z.of_nat (2 * S i0 + 1))%Z).
  { rewrite Hu, Z.div_div by lia. f_equal.
    replace (Z.of_nat (2 * S i0 + 1)) with (Z.of_nat (2 * i0 + 1) + 2)%Z by lia.
    rewrite Z.pow_add_r by lia. ring. }
  replace (Z.of_nat i0 + 1)%Z with (Z.of_nat (S i0)) by lia.
  specialize (IH (S i0) _ Hu').
  pose proof (as_term_bounds q P (2 * i0 + 1) Hq HP ltac:(lia)) as Ht.
  replace (2 * Z.of_nat i0 + 1)%Z with (Z.of_nat (2 * i0 + 1)) by lia.
  rewrite <- Hu in Ht.
  rewrite plus_IZR, S_INR, Rmult_plus_distr_l. lra.
Qed.

(** Each of the [n] terms of [zsum] is at most 1 below the real term it
    floors, and the terms past [n] add at most [q^-(2n+1) / (1 - q^-2)]. *)
Lemma zsum_bounds :
  forall q P n,
  (2 <= q)%Z -> (0 <= P)%Z ->
  IZR (zsum (q * q) (2 ^ P / q) 0 n) <= bpow radix2 P * Ratanh (/ IZR q) <=
  IZR (zsum (q * q) (2 ^ P / q) 0 n) + INR n +
  bpow radix2 P * (/ IZR q) ^ (2 * n + 1) / (1 - (/ IZR q) ^ 2).
Proof.
intros q P n Hq HP.
assert (Hq0 : 2 <= IZR q) by (apply IZR_le; exact Hq).
assert (Hx : 0 <= / IZR q < 1).
{ split; [apply Rlt_le, Rinv_0_lt_compat; lra |].
  rewrite <- Rinv_1. apply Rinv_lt_contravar; lra. }
pose proof (as_zsum_tsum q P Hq HP n 0 (2 ^ P / q)%Z) as Hz.
change (Z.of_nat (2 * 0 + 1)) with 1%Z in Hz. rewrite Z.pow_1_r in Hz.
specialize (Hz eq_refl). change (Z.of_nat 0) with 0%Z in Hz.
rewrite <- as_tsum_atanh_sum in Hz.
destruct (atanh_sum_bounds n (/ IZR q) Hx) as [Hr1 Hr2].
assert (HB : 0 < bpow radix2 P) by apply bpow_gt_0.
assert (H1 : 0 <= bpow radix2 P * (Ratanh (/ IZR q) - atanh_sum n (/ IZR q)))
  by (apply Rmult_le_pos; lra).
assert (H2 : bpow radix2 P * (Ratanh (/ IZR q) - atanh_sum n (/ IZR q)) <=
             bpow radix2 P * ((/ IZR q) ^ (2 * n + 1) / (1 - (/ IZR q) ^ 2)))
  by (apply Rmult_le_compat_l; lra).
replace (bpow radix2 P * (/ IZR q) ^ (2 * n + 1) / (1 - (/ IZR q) ^ 2))
  with (bpow radix2 P * ((/ IZR q) ^ (2 * n + 1) / (1 - (/ IZR q) ^ 2)))
  by (unfold Rdiv; ring).
rewrite Rmult_minus_distr_l in H1, H2. lra.
Qed.
