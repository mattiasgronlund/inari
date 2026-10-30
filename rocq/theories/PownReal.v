(** * The point functions [pown] on the reals

    Facts about Stdlib's [powerRZ r n] that the proofs of [Powi.v] use: its
    value for [n = 0], its symmetry for an even or odd [n], its sign, its
    monotonicity above 0, its limits as [r] grows without bound or tends to
    0, and its continuity at each point of the domain [pown_dom n]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Inari Require Import Elementary.

Open Scope R_scope.

(** Helpers: the parity of [Z.pos p] and [Z.neg p] is the parity of
    [Pos.to_nat p], and the sign of [(- r) ^ k] follows the parity of
    [k]. *)
Lemma pnr_parity_nat :
  forall k, Z.even (Z.of_nat k) = Nat.even k /\ Z.odd (Z.of_nat k) = Nat.odd k.
Proof.
  intros k; induction k as [|k [He Ho]].
  - split; reflexivity.
  - rewrite Nat2Z.inj_succ, Z.even_succ, Z.odd_succ, Nat.even_succ, Nat.odd_succ.
    split; assumption.
Qed.

Lemma pnr_zeven_pos : forall p, Z.even (Z.pos p) = Nat.even (Pos.to_nat p).
Proof.
  intros p. rewrite <- positive_nat_Z. apply pnr_parity_nat.
Qed.

Lemma pnr_zodd_pos : forall p, Z.odd (Z.pos p) = Nat.odd (Pos.to_nat p).
Proof.
  intros p. rewrite <- positive_nat_Z. apply pnr_parity_nat.
Qed.

Lemma pnr_zeven_neg : forall p, Z.even (Z.neg p) = Z.even (Z.pos p).
Proof. intros p; destruct p; reflexivity. Qed.

Lemma pnr_zodd_neg : forall p, Z.odd (Z.neg p) = Z.odd (Z.pos p).
Proof. intros p; destruct p; reflexivity. Qed.

Lemma pnr_pow_opp :
  forall r k, (- r) ^ k = if Nat.even k then r ^ k else - (r ^ k).
Proof.
  intros r k; induction k as [|k IH].
  - reflexivity.
  - rewrite Nat.even_succ; unfold Nat.odd.
    change ((- r) ^ S k) with (- r * (- r) ^ k).
    change (r ^ S k) with (r * r ^ k).
    rewrite IH; destruct (Nat.even k); simpl; ring.
Qed.

Lemma pnr_pow_even : forall r k, Nat.even k = true -> (- r) ^ k = r ^ k.
Proof. intros r k H; rewrite pnr_pow_opp, H; reflexivity. Qed.

Lemma pnr_pow_odd : forall r k, Nat.odd k = true -> (- r) ^ k = - (r ^ k).
Proof.
  intros r k H; unfold Nat.odd in H; rewrite pnr_pow_opp.
  destruct (Nat.even k); [discriminate | reflexivity].
Qed.

(** For an odd [k], [pow] is increasing on all of R: compare the
    absolute values on the negative side. *)
Lemma pnr_pow_le_odd :
  forall r t k, Nat.odd k = true -> r <= t -> r ^ k <= t ^ k.
Proof.
  intros r t k Hk Hrt.
  assert (Hr : r ^ k = - ((- r) ^ k)) by (rewrite pnr_pow_odd by exact Hk; ring).
  assert (Ht : t ^ k = - ((- t) ^ k)) by (rewrite pnr_pow_odd by exact Hk; ring).
  destruct (Rle_or_lt 0 r) as [H0r | Hr0].
  - apply pow_incr; lra.
  - destruct (Rle_or_lt 0 t) as [H0t | Ht0].
    + rewrite Hr.
      assert (0 <= (- r) ^ k) by (apply pow_le; lra).
      assert (0 <= t ^ k) by (apply pow_le; lra).
      lra.
    + rewrite Hr, Ht.
      assert ((- t) ^ k <= (- r) ^ k) by (apply pow_incr; lra).
      lra.
Qed.

(** [r <= r ^ k] for [r >= 1] and [r ^ k <= r] for [0 <= r <= 1], when
    [k >= 1]. *)
Lemma pnr_pow_ge_self : forall r k, 1 <= r -> (1 <= k)%nat -> r <= r ^ k.
Proof.
  intros r k Hr Hk.
  rewrite <- (pow_1 r) at 1.
  apply Rle_pow; assumption.
Qed.

Lemma pnr_pow_le_self : forall r k, 0 <= r <= 1 -> (1 <= k)%nat -> r ^ k <= r.
Proof.
  intros r k Hr Hk.
  replace k with (S (k - 1)) by lia.
  change (r ^ S (k - 1)) with (r * r ^ (k - 1)).
  assert (r ^ (k - 1) <= 1) by (rewrite <- (pow1 (k - 1)); apply pow_incr; lra).
  assert (0 <= r ^ (k - 1)) by (apply pow_le; lra).
  nra.
Qed.

Lemma pnr_k_pos : forall p, (1 <= Pos.to_nat p)%nat.
Proof. intros p; pose proof (Pos2Nat.is_pos p); lia. Qed.

Lemma pown_0 : forall r, powerRZ r 0 = 1.
Proof.
  intros r; reflexivity.
Qed.

Lemma pown_even_opp : forall r n, Z.even n = true -> powerRZ (- r) n = powerRZ r n.
Proof.
  intros r n Hn; destruct n as [|p|p]; simpl.
  - reflexivity.
  - rewrite pnr_zeven_pos in Hn; rewrite pnr_pow_even by exact Hn; reflexivity.
  - rewrite pnr_zeven_neg, pnr_zeven_pos in Hn.
    rewrite pnr_pow_even by exact Hn; reflexivity.
Qed.

Lemma pown_odd_opp : forall r n, Z.odd n = true -> powerRZ (- r) n = - powerRZ r n.
Proof.
  intros r n Hn; destruct n as [|p|p]; simpl.
  - discriminate.
  - rewrite pnr_zodd_pos in Hn; rewrite pnr_pow_odd by exact Hn; reflexivity.
  - rewrite pnr_zodd_neg, pnr_zodd_pos in Hn.
    rewrite pnr_pow_odd by exact Hn; apply Rinv_opp.
Qed.

Lemma pown_even_abs : forall r n, Z.even n = true -> powerRZ r n = powerRZ (Rabs r) n.
Proof.
  intros r n Hn; unfold Rabs; destruct (Rcase_abs r).
  - symmetry; apply pown_even_opp; exact Hn.
  - reflexivity.
Qed.

Lemma pown_gt_0 : forall r n, 0 < r -> 0 < powerRZ r n.
Proof.
  intros r n Hr; apply powerRZ_lt; exact Hr.
Qed.

Lemma pown_ge_0 : forall r n, 0 <= r -> (0 <= n)%Z -> 0 <= powerRZ r n.
Proof.
  intros r n Hr Hn; destruct n as [|p|p]; simpl.
  - lra.
  - apply pow_le; exact Hr.
  - lia.
Qed.

(** ** Monotonicity *)

(** Increasing from 0 for [n >= 0], decreasing above 0 for [n < 0], and
    increasing on all of R for an odd [n > 0]. *)
Lemma pown_le_pos :
  forall r t n, (0 <= n)%Z -> 0 <= r <= t -> powerRZ r n <= powerRZ t n.
Proof.
  intros r t n Hn Hrt; destruct n as [|p|p]; simpl.
  - lra.
  - apply pow_incr; exact Hrt.
  - lia.
Qed.

Lemma pown_le_neg :
  forall r t n, (n < 0)%Z -> 0 < r <= t -> powerRZ t n <= powerRZ r n.
Proof.
  intros r t n Hn Hrt; destruct n as [|p|p]; simpl; try lia.
  apply Rinv_le_contravar.
  - apply pow_lt; lra.
  - apply pow_incr; lra.
Qed.

Lemma pown_le_odd :
  forall r t n, (0 < n)%Z -> Z.odd n = true -> r <= t -> powerRZ r n <= powerRZ t n.
Proof.
  intros r t n Hn Hodd Hrt; destruct n as [|p|p]; simpl; try lia.
  rewrite pnr_zodd_pos in Hodd.
  apply pnr_pow_le_odd; assumption.
Qed.

(** ** Limits *)

(** As [r] grows: without bound for [n > 0], and toward 0 for [n < 0]. *)
Lemma pown_large_pos :
  forall n M, (0 < n)%Z -> exists r0, 0 < r0 /\ forall r, r0 <= r -> M <= powerRZ r n.
Proof.
  intros n M Hn; destruct n as [|p|p]; try lia.
  exists (1 + Rabs M); split.
  - pose proof (Rabs_pos M); lra.
  - intros r Hr; simpl.
    pose proof (Rle_abs M); pose proof (Rabs_pos M).
    assert (r <= r ^ Pos.to_nat p) by (apply pnr_pow_ge_self; [lra | apply pnr_k_pos]).
    lra.
Qed.

Lemma pown_large_neg :
  forall n eps, (n < 0)%Z -> 0 < eps ->
  exists r0, 0 < r0 /\ forall r, r0 <= r -> powerRZ r n < eps.
Proof.
  intros n eps Hn Heps; destruct n as [|p|p]; try lia.
  pose proof (Rinv_pos eps Heps) as Hie.
  exists (1 + / eps); split; [lra |].
  intros r Hr; simpl.
  assert (r <= r ^ Pos.to_nat p) by (apply pnr_pow_ge_self; [lra | apply pnr_k_pos]).
  rewrite <- (Rinv_inv eps).
  apply Rinv_lt_contravar; [apply Rmult_lt_0_compat; lra | lra].
Qed.

(** As [r] tends to 0 from above, without bound for [n < 0]. *)
Lemma pown_small_neg :
  forall n M, (n < 0)%Z -> exists r0, 0 < r0 /\ forall r, 0 < r <= r0 -> M <= powerRZ r n.
Proof.
  intros n M Hn; destruct n as [|p|p]; try lia.
  pose proof (Rabs_pos M) as HaM; pose proof (Rle_abs M) as HlM.
  assert (H1 : 0 < 1 + Rabs M) by lra.
  pose proof (Rinv_pos _ H1) as Hi.
  assert (Hi1 : / (1 + Rabs M) <= 1).
  { rewrite <- Rinv_1; apply Rinv_le_contravar; lra. }
  exists (/ (1 + Rabs M)); split; [exact Hi |].
  intros r Hr; simpl.
  assert (Hk : r ^ Pos.to_nat p <= r) by (apply pnr_pow_le_self; [lra | apply pnr_k_pos]).
  assert (Hk0 : 0 < r ^ Pos.to_nat p) by (apply pow_lt; lra).
  assert (/ r <= / r ^ Pos.to_nat p) by (apply Rinv_le_contravar; lra).
  assert (/ / (1 + Rabs M) <= / r) by (apply Rinv_le_contravar; lra).
  rewrite Rinv_inv in *.
  lra.
Qed.

(** ** Continuity *)

Lemma pown_cont : forall n r, pown_dom n r -> continuity_pt (fun r => powerRZ r n) r.
Proof.
  intros n r Hd; destruct n as [|p|p].
  - apply continuity_pt_const; intros x y; reflexivity.
  - change (continuity_pt (fun y => y ^ Pos.to_nat p) r).
    apply derivable_continuous_pt, derivable_pt_pow.
  - assert (Hr : r <> 0) by (destruct Hd as [Hd | Hd]; [lia | exact Hd]).
    change (continuity_pt (inv_fct (fun y => y ^ Pos.to_nat p)) r).
    apply continuity_pt_inv.
    + apply derivable_continuous_pt, derivable_pt_pow.
    + apply pow_nonzero; exact Hr.
Qed.
