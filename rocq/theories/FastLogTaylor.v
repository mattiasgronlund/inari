(** * The Taylor series of ln(1 + z)

    [log1p_taylor] bounds the remainder of the Taylor series of ln(1 + z)
    at 0, by the mean value theorem, as [AtanhSeries.atanh_sum_bounds]
    does for atanh, and [log1p_shift] the term of first order in [w] of
    ln(1 + z + w) for a small [w], which [FastLogPoly.v] needs for the
    low part [z2] of [z]. *)

From Stdlib Require Import Reals Lra Lia.
From Flocq Require Import Core.Core.

Open Scope R_scope.

(** z - z^2/2 + ... + (-1)^(d+1) z^d / d, the Taylor polynomial of degree
    [d] of ln(1 + z) at 0. *)
Fixpoint log1p_sum (d : nat) (z : R) : R :=
  match d with
  | O => 0
  | S k => log1p_sum k z + (-1) ^ k * z ^ S k / INR (S k)
  end.

(** ** Derivatives *)

(** [Σ_{k < d} (-1)^k t^k], the derivative of [log1p_sum d] *)
Fixpoint log1p_geo (d : nat) (t : R) : R :=
  match d with
  | O => 0
  | S k => log1p_geo k t + (-1) ^ k * t ^ k
  end.

Lemma log1p_geo_eq : forall d t, log1p_geo d t * (1 + t) = 1 - (-1) ^ d * t ^ d.
Proof.
induction d as [| k IH]; intros t; cbn [log1p_geo].
- simpl. ring.
- rewrite Rmult_plus_distr_r, IH. simpl. ring.
Qed.

Lemma log1p_derive_eq :
  forall f x l l', derivable_pt_lim f x l -> l = l' -> derivable_pt_lim f x l'.
Proof. intros f x l l' H <-. exact H. Qed.

Lemma log1p_sum_derive : forall d t, derivable_pt_lim (log1p_sum d) t (log1p_geo d t).
Proof.
induction d as [| k IH]; intros t.
- apply (derivable_pt_lim_ext (fct_cte 0)); [intros z; reflexivity |].
  apply derivable_pt_lim_const.
- apply (derivable_pt_lim_ext
           (log1p_sum k + mult_real_fct ((-1) ^ k / INR (S k)) (fun y => y ^ S k))%F).
  { intros z. unfold plus_fct, mult_real_fct. cbn [log1p_sum]. unfold Rdiv. ring. }
  eapply log1p_derive_eq.
  + apply derivable_pt_lim_plus; [apply IH |].
    apply derivable_pt_lim_scal. apply derivable_pt_lim_pow.
  + cbn [log1p_geo]. replace (Init.Nat.pred (S k)) with k by reflexivity.
    field. apply not_0_INR. lia.
Qed.

(** The derivative of ln(1 + z) minus its Taylor polynomial of degree [d]
    is [(-1)^d t^d / (1 + t)], since the derivative of the polynomial is a
    geometric sum. *)
Lemma log1p_rem_derive :
  forall d t, -1 < t ->
  derivable_pt_lim (fun r => ln (1 + r) - log1p_sum d r) t ((-1) ^ d * t ^ d / (1 + t)).
Proof.
intros d t Ht.
apply (derivable_pt_lim_ext (comp ln (fct_cte 1 + id) - log1p_sum d)%F);
  [intros z; reflexivity |].
eapply log1p_derive_eq.
- apply derivable_pt_lim_minus; [| apply log1p_sum_derive].
  apply derivable_pt_lim_comp.
  + apply derivable_pt_lim_plus; [apply derivable_pt_lim_const | apply derivable_pt_lim_id].
  + apply derivable_pt_lim_ln. unfold plus_fct, fct_cte, id. lra.
- unfold plus_fct, fct_cte, id.
  pose proof (log1p_geo_eq d t) as Hg.
  replace (log1p_geo d t) with ((1 - (-1) ^ d * t ^ d) / (1 + t))
    by (rewrite <- Hg; field; lra).
  field. lra.
Qed.

(** The derivative of the bound [s r^(d+1) / K] *)
Lemma log1p_bound_derive :
  forall s d K t,
  derivable_pt_lim (fun r => s * r ^ S d / K) t (s * (INR (S d) * t ^ d) / K).
Proof.
intros s d K t.
apply (derivable_pt_lim_ext (mult_real_fct (s / K) (fun y => y ^ S d)));
  [intros z; unfold mult_real_fct, Rdiv; ring |].
eapply log1p_derive_eq.
- apply derivable_pt_lim_scal. apply derivable_pt_lim_pow.
- replace (Init.Nat.pred (S d)) with d by reflexivity. unfold Rdiv. ring.
Qed.

(** ** The remainder *)

(** A function whose derivative is dominated by the derivative of [g]
    moves less than [g] does: the mean value theorem on [g - f] and [g + f]. *)
Lemma log1p_dominate :
  forall f f' g g' a b, a < b ->
  (forall c, a <= c <= b -> derivable_pt_lim f c (f' c)) ->
  (forall c, a <= c <= b -> derivable_pt_lim g c (g' c)) ->
  (forall c, a <= c <= b -> Rabs (f' c) <= g' c) ->
  Rabs (f b - f a) <= g b - g a.
Proof.
intros f f' g g' a b Hab Hf Hg Hd.
destruct (MVT_cor2 (fun r => g r - f r) (fun r => g' r - f' r) a b Hab) as (c & Hc & Hc0).
{ intros c Hc. apply (derivable_pt_lim_ext (g - f)%F); [intros z; reflexivity |].
  apply derivable_pt_lim_minus; [apply Hg | apply Hf]; exact Hc. }
destruct (MVT_cor2 (fun r => g r + f r) (fun r => g' r + f' r) a b Hab) as (e & He & He0).
{ intros e He. apply (derivable_pt_lim_ext (g + f)%F); [intros z; reflexivity |].
  apply derivable_pt_lim_plus; [apply Hg | apply Hf]; exact He. }
pose proof (Hd c ltac:(lra)) as H1. pose proof (Hd e ltac:(lra)) as H2.
apply Rabs_le_inv in H1. apply Rabs_le_inv in H2.
assert (P1 : 0 <= (g' c - f' c) * (b - a)) by (apply Rmult_le_pos; lra).
assert (P2 : 0 <= (g' e + f' e) * (b - a)) by (apply Rmult_le_pos; lra).
apply Rabs_le. lra.
Qed.

Lemma log1p_opp_pow : forall n x, (- x) ^ n = (-1) ^ n * x ^ n.
Proof. intros n x. rewrite <- Rpow_mult_distr. f_equal. ring. Qed.

Theorem log1p_taylor :
  forall d z, Rabs z <= / 2 ->
  Rabs (ln (1 + z) - log1p_sum d z) <= Rabs z ^ S d / (INR (S d) * (1 - Rabs z)).
Proof.
intros d z Hz.
set (f := fun r => ln (1 + r) - log1p_sum d r).
change (ln (1 + z) - log1p_sum d z) with (f z).
assert (Hs : forall k, log1p_sum k 0 = 0).
{ induction k as [| k IH]; cbn [log1p_sum]; [reflexivity |].
  rewrite IH, pow_i by lia. unfold Rdiv. ring. }
assert (Hf0 : f 0 = 0) by (unfold f; rewrite Hs, Rplus_0_r, ln_1; ring).
assert (HD : 0 < INR (S d)) by (apply lt_0_INR; lia).
assert (HZ : 0 < 1 - Rabs z) by lra.
set (K := INR (S d) * (1 - Rabs z)).
assert (HK : 0 < K) by (apply Rmult_lt_0_compat; lra).
(* The derivative of [s r^(d+1) / K] is [s r^d / (1 - |z|)], and it
   dominates [|r|^d / (1 + r)], the absolute value of [f'] at [r], where
   [s r^d = |r|^d] and [|r| <= |z|]. *)
assert (Hdom : forall s c, Rabs c <= Rabs z -> s * c ^ d = Rabs c ^ d ->
          Rabs ((-1) ^ d * c ^ d / (1 + c)) <= s * (INR (S d) * c ^ d) / K).
{ intros s c Hc Hsc.
  assert (Hc1 : 0 < 1 + c) by (apply Rabs_le_inv in Hc; lra).
  replace (s * (INR (S d) * c ^ d) / K) with (Rabs c ^ d / (1 - Rabs z))
    by (unfold K; rewrite <- Hsc; field; lra).
  unfold Rdiv. rewrite !Rabs_mult, pow_1_abs, <- RPow_abs, Rmult_1_l.
  rewrite (Rabs_pos_eq (/ (1 + c))) by (apply Rlt_le, Rinv_0_lt_compat; lra).
  apply Rmult_le_compat_l; [apply pow_le, Rabs_pos |].
  apply Rinv_le_contravar; [exact HZ |].
  apply Rabs_le_inv in Hc. lra. }
destruct (Rtotal_order z 0) as [Hn | [-> | Hp]].
- (* z < 0: on [z, 0] with [s = (-1)^d], so that [g 0 - g z = |z|^(d+1) / K]. *)
  pose proof (log1p_dominate f (fun r => (-1) ^ d * r ^ d / (1 + r))
                (fun r => (-1) ^ d * r ^ S d / K)
                (fun r => (-1) ^ d * (INR (S d) * r ^ d) / K) z 0 Hn) as H.
  rewrite Hf0, Rminus_0_l, Rabs_Ropp in H.
  rewrite (Rabs_left z Hn), log1p_opp_pow.
  replace ((-1) ^ S d * z ^ S d / K) with (0 - (-1) ^ d * z ^ S d / K)
    by (simpl; field; lra).
  replace 0 with ((-1) ^ d * 0 ^ S d / K) at 1 by (simpl; field; lra).
  apply H.
  + intros c Hc. apply log1p_rem_derive. apply Rabs_le_inv in Hz. lra.
  + intros c Hc. apply log1p_bound_derive.
  + intros c Hc. apply Hdom.
    * rewrite (Rabs_left z Hn). unfold Rabs. destruct (Rcase_abs c); lra.
    * rewrite <- log1p_opp_pow. f_equal. unfold Rabs. destruct (Rcase_abs c); lra.
- (* z = 0: both sides are 0. *)
  rewrite Hf0, Rabs_R0, pow_i by lia. unfold Rdiv. rewrite Rmult_0_l. lra.
- (* z > 0: on [0, z] with [s = 1]. *)
  pose proof (log1p_dominate f (fun r => (-1) ^ d * r ^ d / (1 + r))
                (fun r => 1 * r ^ S d / K)
                (fun r => 1 * (INR (S d) * r ^ d) / K) 0 z Hp) as H.
  rewrite Hf0, Rminus_0_r in H.
  rewrite (Rabs_pos_eq z) by lra.
  replace (z ^ S d / K) with (1 * z ^ S d / K - 1 * 0 ^ S d / K)
    by (rewrite pow_i by lia; field; lra).
  apply H.
  + intros c Hc. apply log1p_rem_derive. lra.
  + intros c Hc. apply log1p_bound_derive.
  + intros c Hc. apply Hdom.
    * rewrite (Rabs_pos_eq z), (Rabs_pos_eq c); lra.
    * rewrite (Rabs_pos_eq c) by lra. ring.
Qed.

(** For [|z| <= 2^-9] and [|w| <= 2^-53 |z|], ln(1 + z + w) is within
    [512/511 |w| z^2 + 2^-113 |z|] of ln(1 + z) + w (1 - z). *)
Theorem log1p_shift :
  forall z w, Rabs z <= bpow radix2 (-9) -> Rabs w <= bpow radix2 (-53) * Rabs z ->
  Rabs (ln (1 + (z + w)) - (ln (1 + z) + w * (1 - z))) <=
    512 / 511 * Rabs w * Rabs z ^ 2 + bpow radix2 (-113) * Rabs z.
Proof.
intros z w Hz Hw.
assert (B9 : bpow radix2 (-9) = / 512) by reflexivity.
assert (B53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
assert (B113 : bpow radix2 (-113) = / 10384593717069655257060992658440192)
  by reflexivity.
rewrite B9 in Hz. rewrite B53 in Hw. rewrite B113.
assert (HZ0 : 0 <= Rabs z) by apply Rabs_pos.
assert (HW0 : 0 <= Rabs w) by apply Rabs_pos.
pose proof (Rabs_le_inv z _ Hz) as Hz'.
assert (H1z : 0 < 1 + z) by lra.
(* [1 + z + w = (1 + z) (1 + t)] with [t = w / (1 + z)]. *)
assert (Hi : / (1 + z) <= 512 / 511).
{ replace (512 / 511) with (/ (1 - / 512)) by field. apply Rinv_le_contravar; lra. }
set (t := w / (1 + z)).
assert (Ht : Rabs t <= 512 / 511 * Rabs w).
{ unfold t, Rdiv. rewrite Rabs_mult, Rabs_inv, (Rabs_pos_eq (1 + z)) by lra.
  rewrite Rmult_comm. apply Rmult_le_compat_r; [exact HW0 | exact Hi]. }
assert (Ht2 : Rabs t <= / 2) by lra.
pose proof (Rabs_le_inv t _ Ht2) as Ht'.
assert (Hsplit : ln (1 + (z + w)) = ln (1 + z) + ln (1 + t)).
{ rewrite <- ln_mult by lra. f_equal. unfold t. field. lra. }
rewrite Hsplit.
replace (ln (1 + z) + ln (1 + t) - (ln (1 + z) + w * (1 - z)))
  with ((ln (1 + t) - t) + (t - w * (1 - z))) by ring.
eapply Rle_trans; [apply Rabs_triang |].
(* [ln (1 + t) - t]: the Taylor remainder of degree 1. *)
pose proof (log1p_taylor 1 t Ht2) as HT.
replace (log1p_sum 1 t) with t in HT by (cbn [log1p_sum]; simpl; field).
assert (HT' : Rabs (ln (1 + t) - t) <= / 10384593717069655257060992658440192 * Rabs z).
{ eapply Rle_trans; [exact HT |].
  replace (INR 2) with 2 by (simpl; ring).
  (* [|t|^2 / (2 (1 - |t|)) <= |t|^2 <= (512/511 2^-53)^2 2^-9 |z|] *)
  assert (Hta : Rabs t <= 512 / 511 * / 9007199254740992 * Rabs z) by lra.
  assert (Htb : Rabs t ^ 2 <= (512 / 511 * / 9007199254740992 * Rabs z) ^ 2)
    by (apply pow_incr; split; [apply Rabs_pos | exact Hta]).
  assert (Htc : 0 <= Rabs t ^ 2) by (apply pow_le, Rabs_pos).
  apply Rle_trans with (Rabs t ^ 2).
  { unfold Rdiv. rewrite <- (Rmult_1_r (Rabs t ^ 2)) at 2.
    apply Rmult_le_compat_l; [exact Htc |].
    rewrite <- Rinv_1. apply Rinv_le_contravar; lra. }
  apply Rle_trans with ((512 / 511 * / 9007199254740992 * Rabs z) ^ 2); [exact Htb |].
  nra. }
(* [t - w (1 - z) = w z^2 / (1 + z)]. *)
assert (HS : Rabs (t - w * (1 - z)) <= 512 / 511 * Rabs w * Rabs z ^ 2).
{ replace (t - w * (1 - z)) with (w * z ^ 2 * / (1 + z)) by (unfold t; field; lra).
  rewrite !Rabs_mult, Rabs_inv, (Rabs_pos_eq (1 + z)) by lra.
  rewrite <- RPow_abs.
  assert (0 <= Rabs w * Rabs z ^ 2) by (apply Rmult_le_pos; [lra | apply pow_le; lra]).
  nra. }
lra.
Qed.
