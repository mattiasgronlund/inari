(** * Facts of atan for its fast path

    The reduction of [FastAtanCore.v]: atan t = atan c + atan((t - c) / (1
    + t c)) for [t, c >= 0] ([atan_sub_table], from Stdlib's
    [Machin.atan_sub_correct]), and the bounds [|atan a - atan b| <= |a -
    b|] ([atan_lipschitz]), [q/2 <= atan q] for [0 <= q <= 2]
    ([atan_lower]) and [atan q <= q] for [q >= 0] ([atan_upper]) that turn
    absolute errors of an argument into relative errors of atan. *)

From Stdlib Require Import Reals Lra.
From Stdlib Require Import Machin.
From Inari Require Import Elementary AtanReal AtanIdent AtanSeries.

Open Scope R_scope.

Lemma atan_sub_table :
  forall t c, 0 <= t -> 0 <= c -> atan t = atan c + atan ((t - c) / (1 + t * c)).
Proof.
intros t c Ht Hc.
(* [atan t] and [atan c] lie in [[0, π/2)], so their difference lies in
   [(-π/2, π/2)], as [atan_sub_correct] needs; [1 + t c >= 1]. *)
pose proof (ar_atan_nonneg t Ht) as Ht'.
pose proof (ar_atan_nonneg c Hc) as Hc'.
pose proof (atan_bound t) as Hbt.
pose proof (atan_bound c) as Hbc.
assert (Htc : 0 <= t * c) by (apply Rmult_le_pos; assumption).
change ((t - c) / (1 + t * c)) with (atan_sub t c).
pose proof (atan_bound (atan_sub t c)) as Hbs.
apply atan_sub_correct; [apply Rgt_not_eq | |]; lra.
Qed.

Lemma atan_lipschitz : forall a b, Rabs (atan a - atan b) <= Rabs (a - b).
Proof.
(* For [x < y], the mean value theorem gives [atan y - atan x = (y - x) /
   (1 + c^2)] for some [c], and [0 < 1 / (1 + c^2) <= 1]. *)
assert (key : forall x y, x < y -> Rabs (atan x - atan y) <= Rabs (x - y)).
{ intros x y Hxy.
  destruct (MVT_cor2 atan (fun c => / (1 + c ^ 2)) x y Hxy) as [c [Hc _]].
  { intros c _. apply derivable_pt_lim_atan. }
  pose proof (pow2_ge_0 c) as Hc2.
  assert (Hk : 0 < / (1 + c ^ 2) <= 1).
  { split; [apply Rinv_0_lt_compat; lra |].
    rewrite <- Rinv_1. apply Rinv_le_contravar; lra. }
  rewrite (Rabs_minus_sym (atan x)), (Rabs_minus_sym x), Hc, Rabs_mult.
  rewrite (Rabs_pos_eq (/ (1 + c ^ 2))) by lra.
  pose proof (Rabs_pos (y - x)). nra. }
intros a b.
destruct (Rtotal_order a b) as [H | [H | H]].
- apply key, H.
- subst b. unfold Rminus. rewrite !Rplus_opp_r, Rabs_R0. lra.
- rewrite (Rabs_minus_sym (atan a)), (Rabs_minus_sym a). apply key, H.
Qed.

(* [atan_upper] comes first, as [atan_lower] uses it at [1 / q]. *)
Lemma atan_upper : forall q, 0 <= q -> atan q <= q.
Proof.
intros q Hq.
(* The series remainder at [n = 0]: [atan q = T q] with [0 <= T <= 1]. *)
destruct (atan_tail_bounds 0 q) as [T [[HT0 HT1] HT]].
cbn [atan_sum pow Nat.mul Nat.add INR] in HT, HT1.
assert (T * q <= q) by nra.
lra.
Qed.

Lemma atan_lower : forall q, 0 <= q <= 2 -> q / 2 <= atan q.
Proof.
intros q [Hq0 Hq2].
destruct (Rle_or_lt q 1) as [Hq1 | Hq1].
- (* The series remainder at [n = 1]: [atan q = q - T q^3] with [0 <= T <=
     1/3], and [q - q^3/3 >= q/2] as [q^2 <= 1]. *)
  destruct (atan_tail_bounds 1 q) as [T [[HT0 HT1] HT]].
  cbn [atan_sum pow Nat.mul Nat.add INR] in HT, HT1.
  assert (Hq3 : 0 <= q * (q * q) <= q) by (split; nra).
  assert (T * (q * (q * q)) <= q / 3) by nra.
  nra.
- (* [atan q = π/2 - atan (1/q) >= π/2 - 1/q > 3/2 - 1/q >= q/2], the last
     step as [(q - 1)(q - 2) <= 0]. *)
  assert (Hqp : 0 < q) by lra.
  pose proof (atan_inv q Hqp) as Hinv.
  pose proof (atan_upper (/ q) (Rlt_le _ _ (Rinv_0_lt_compat q Hqp))) as Hup.
  pose proof PI2_3_2 as Hpi.
  assert (Hq : q / 2 + / q <= 3 / 2).
  { apply (Rmult_le_reg_r q); [exact Hqp |].
    rewrite Rmult_plus_distr_r, Rinv_l by lra. nra. }
  lra.
Qed.

(** ** The errors of the fast paths of [FastAtan.v] and [FastAsin.v]

    Flocq's [bpow] and [π]'s bound in [FastAtanTables.v] are imported
    only here, after the proofs above. *)

From Flocq Require Import Core.Core.
From Inari Require FastAtanTables.

(** The core's [2^-74] relative error at [q'] near [q], as an absolute
    error at [q] ([atan_upper], [atan_lipschitz]). *)
Lemma atan_abs_err :
  forall q' q s,
  0 <= q' <= 3 / 2 -> Rabs (q' - q) <= bpow radix2 (-90) ->
  Rabs (s - atan q') <= bpow radix2 (-74) * atan q' ->
  Rabs (s - atan q) <= bpow radix2 (-73).
Proof.
intros q' q s Hq' Hd Hs.
(* [|s - atan q| <= |s - atan q'| + |atan q' - atan q| <= 2^-74 atan q' +
   |q' - q|], and [atan q' <= q' <= 3/2], so the sum is at most [3/2
   2^-74 + 2^-90 <= 2^-73]. *)
pose proof (atan_upper q' (proj1 Hq')) as Hu.
assert (Hl : Rabs (atan q' - atan q) <= bpow radix2 (-90)).
{ eapply Rle_trans; [apply atan_lipschitz | exact Hd]. }
assert (E73 : bpow radix2 (-73) = / 9444732965739290427392) by reflexivity.
assert (E74 : bpow radix2 (-74) = / 18889465931478580854784) by reflexivity.
assert (E90 : bpow radix2 (-90) = / 1237940039285380274899124224) by reflexivity.
rewrite E74 in Hs. rewrite E90 in Hl. rewrite E73.
apply Rabs_le_inv in Hs. apply Rabs_le_inv in Hl.
apply Rabs_le. split; lra.
Qed.

(** The same, as a relative error at [q] ([atan_lower]). *)
Lemma atan_rel_err :
  forall q' q s,
  0 < q <= 2 -> Rabs (q' - q) <= bpow radix2 (-96) * q ->
  Rabs (s - atan q') <= bpow radix2 (-74) * atan q' ->
  Rabs (s - atan q) <= bpow radix2 (-73) * atan q.
Proof.
intros q' q s Hq Hd Hs.
(* [|s - atan q| <= 2^-74 atan q' + |atan q' - atan q|], with [atan q' <=
   atan q + 2^-96 q] and [|atan q' - atan q| <= 2^-96 q]; then [q <= 2
   atan q] makes the sum at most [(2^-74 + 2^-169 + 2^-95) atan q <= 2^-73
   atan q]. *)
assert (Hlo : q / 2 <= atan q) by (apply atan_lower; lra).
assert (Hl : Rabs (atan q' - atan q) <= bpow radix2 (-96) * q).
{ eapply Rle_trans; [apply atan_lipschitz | exact Hd]. }
assert (E73 : bpow radix2 (-73) = / 9444732965739290427392) by reflexivity.
assert (E74 : bpow radix2 (-74) = / 18889465931478580854784) by reflexivity.
assert (E96 : bpow radix2 (-96) = / 79228162514264337593543950336) by reflexivity.
rewrite E74 in Hs. rewrite E96 in Hl. rewrite E73.
apply Rabs_le_inv in Hs. apply Rabs_le_inv in Hl.
apply Rabs_le. split; lra.
Qed.

(** [atan q] for [0 < q <= 1] is in [(0, π/4]], and [π < 16/5]
    ([FastAtanTables.fast_pio2_correct]). *)
Lemma atan_pos_le : forall q, 0 < q <= 1 -> 0 < atan q <= 4 / 5.
Proof.
intros q [Hq0 Hq1].
assert (Hlo : q / 2 <= atan q) by (apply atan_lower; lra).
(* [atan q <= atan 1 = π/4], as atan is increasing. *)
assert (Hup : atan q <= PI / 4).
{ rewrite <- atan_1.
  destruct (Rle_lt_or_eq_dec q 1 Hq1) as [H | ->].
  - apply Rlt_le, atan_increasing, H.
  - apply Rle_refl. }
(* [π/2 <= hi + |lo| + 2^-107 < 8/5], with [hi] and [lo] the two halves
   of [PIO2]. *)
destruct FastAtanTables.fast_pio2_correct as (_ & _ & Ehi & Hl & He).
rewrite Ehi in He.
assert (E53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
assert (E107 : bpow radix2 (-107) = / 162259276829213363391578010288128) by reflexivity.
rewrite E53 in Hl. rewrite E107 in He.
apply Rabs_le_inv in Hl. apply Rabs_le_inv in He.
split; lra.
Qed.

(** [atan q] is [q] within [q^3/3] for [q >= 0]
    ([AtanSeries.atan_tail_bounds]). *)
Lemma atan_cubic : forall q, 0 <= q -> 0 <= q - atan q <= q ^ 3 / 3.
Proof.
intros q Hq.
(* The series remainder at [n = 1]: [q - atan q = T q^3] with [0 <= T <=
   1/3], as in [DyAtanTiny.atan_tiny_real]. *)
destruct (atan_tail_bounds 1 q) as (T & B & E).
change (2 * 1 + 1)%nat with 3%nat in B, E.
replace (atan_sum 1 q) with q in E by (cbn; field).
replace (INR 3) with 3 in B by (cbn; ring).
replace ((-1) ^ 1) with (-1) in E by ring.
assert (P3 : 0 <= q ^ 3) by (apply pow_le; exact Hq).
assert (H0 : 0 <= T * q ^ 3) by (apply Rmult_le_pos; lra).
assert (H1 : T * q ^ 3 <= q ^ 3 / 3).
{ unfold Rdiv. rewrite (Rmult_comm (q ^ 3)). apply Rmult_le_compat_r; lra. }
split; lra.
Qed.
