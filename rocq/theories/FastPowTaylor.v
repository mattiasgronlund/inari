(** * The term of first order in a small shift of ln(1 + z), for x^y

    [log1p_shift2] bounds the error of ln(1 + z) + w (1 - z + z^2) as
    ln(1 + z + w), for [|z| <= 2^-9] and [|w| <= 2^-53 |z|], which
    [FastPowPoly.v] needs for the low part [z2] of [z]. It is
    [FastLogTaylor.log1p_shift] with one more term of [w / (1 + z)]:
    with [t = w / (1 + z)], ln(1 + z + w) = ln(1 + z) + ln(1 + t),
    ln(1 + t) is within [t^2] of [t] ([FastLogTaylor.log1p_taylor] at
    degree 1), and [t - w (1 - z + z^2) = - w z^3 / (1 + z)]. With
    [1 / (1 + z) <= 512/511], [t^2] is below [2^-113 |z|] and the last
    term below [512/511 |w| |z|^3]. *)

From Stdlib Require Import Reals Lra Lia.
From Flocq Require Import Core.Core.
From Inari Require Import FastLogTaylor.

Open Scope R_scope.

(** For [|z| <= 2^-9] and [|w| <= 2^-53 |z|], ln(1 + z + w) is within
    [512/511 |w| |z|^3 + 2^-113 |z|] of ln(1 + z) + w (1 - z + z^2). *)
Theorem log1p_shift2 :
  forall z w, Rabs z <= bpow radix2 (-9) -> Rabs w <= bpow radix2 (-53) * Rabs z ->
  Rabs (ln (1 + (z + w)) - (ln (1 + z) + w * (1 - z + z ^ 2))) <=
    512 / 511 * Rabs w * Rabs z ^ 3 + bpow radix2 (-113) * Rabs z.
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
replace (ln (1 + z) + ln (1 + t) - (ln (1 + z) + w * (1 - z + z ^ 2)))
  with ((ln (1 + t) - t) + (t - w * (1 - z + z ^ 2))) by ring.
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
(* [t - w (1 - z + z^2) = - w z^3 / (1 + z)], since
   [(1 + z) (1 - z + z^2) = 1 + z^3]. *)
assert (HS : Rabs (t - w * (1 - z + z ^ 2)) <= 512 / 511 * Rabs w * Rabs z ^ 3).
{ replace (t - w * (1 - z + z ^ 2)) with (- (w * z ^ 3 * / (1 + z)))
    by (unfold t; field; lra).
  rewrite Rabs_Ropp, !Rabs_mult, Rabs_inv, (Rabs_pos_eq (1 + z)) by lra.
  rewrite <- RPow_abs.
  assert (0 <= Rabs w * Rabs z ^ 3) by (apply Rmult_le_pos; [lra | apply pow_le; lra]).
  nra. }
lra.
Qed.
