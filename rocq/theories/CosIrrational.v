(** * cos r is irrational for every rational r other than 0

    Niven's proof ("Irrational Numbers", 1956, ch. 2), with the integral
    replaced by the mean value theorem, as in [PiIrrational.v]. As [cos]
    is even, take [r = a / b > 0], and suppose [cos r = c / d] with
    [d > 0]. With Niven's polynomial [g] of [CosNiven.v] for an odd [p],
    [F] its alternating sum of even derivatives, and [G(x) = F'(x) sin x -
    F(x) cos x], [G' = g sin] ([ci_G_deriv]), and [G(r) - G(0) = F(0) -
    F(r) cos r] ([ci_G_ends], from [cn_F'r]). So [d (G(r) - G(0)) =
    d F(0) - c F(r)] is [(p-1)!] times the integer [d z0 - c p z1]
    ([cn_F0], [cn_Fr]). Niven takes a prime [p]; here [p = 2 a d K + 1]
    for an integer [K >= 1], which is odd and prime to [2 a] and to [d]
    (Bezout), so that [p] does not divide [d z0] and the integer is not 0.
    By the mean value theorem, [G(r) - G(0)] is [r g(x) sin x] for some
    [x] in [(0, r)], and [0 <= g(x) <= a^2 C^(p-1)] there with
    [C = 2 r a^3], which does not depend on [p]. So
    [(p-1)! <= d r a^2 C^(p-1)] ([ci_bound]), which fails for large [K]
    ([cv_speed_pow_fact]). *)

From Stdlib Require Import ZArith Reals Lra Lia Znumtheory.
From Inari Require Import NivenPoly NivenAlt CosNiven.

Open Scope R_scope.

Definition ci_G (a b : Z) (p : nat) (x : R) : R :=
  ch_alt (cn_d a b p) 1 (2 * p - 1) x * sin x - ch_alt (cn_d a b p) 0 (2 * p - 1) x * cos x.

(** [derivable_pt_lim] with its limit rewritten. *)
Lemma ci_lim_eq :
  forall f x l l', l = l' -> derivable_pt_lim f x l -> derivable_pt_lim f x l'.
Proof.
  intros f x l l' E H. rewrite <- E. exact H.
Qed.

Lemma ci_G_deriv :
  forall a b p x, (1 <= p)%nat ->
  derivable_pt_lim (ci_G a b p) x (zp_ev (cn_poly a b p) x * sin x).
Proof.
  intros a b p x Hp.
  pose proof (cn_d_chain a b p) as Hc.
  pose proof (derivable_pt_lim_mult _ _ x _ _
    (ch_alt_deriv _ Hc (2 * p - 1) 1 x) (derivable_pt_lim_sin x)) as H1.
  pose proof (derivable_pt_lim_mult _ _ x _ _
    (ch_alt_deriv _ Hc (2 * p - 1) 0 x) (derivable_pt_lim_cos x)) as H0.
  pose proof (derivable_pt_lim_minus _ _ x _ _ H1 H0) as H.
  (* [F'' + F = g]: the sum telescopes to [g] and a derivative of order
     [4 p], which vanishes as [g] has degree [4 p - 2]. *)
  pose proof (ch_alt_rec (cn_d a b p) (2 * p - 1) 0 x) as Hr.
  replace (0 + 2 * (2 * p - 1) + 2)%nat with (4 * p)%nat in Hr by lia.
  rewrite (cn_d_high a b p x Hp), Rmult_0_r, Rplus_0_r in Hr.
  change (zp_ev (cn_poly a b p) x) with (cn_d a b p O x).
  rewrite <- Hr.
  eapply ci_lim_eq; [| exact H].
  ring.
Qed.

Lemma ci_G_ends :
  forall a b p, (0 < b)%Z ->
  ci_G a b p (IZR a / IZR b) - ci_G a b p 0 =
  ch_alt (cn_d a b p) 0 (2 * p - 1) 0 -
  ch_alt (cn_d a b p) 0 (2 * p - 1) (IZR a / IZR b) * cos (IZR a / IZR b).
Proof.
  intros a b p Hb.
  unfold ci_G.
  rewrite (cn_F'r a b p Hb), sin_0, cos_0.
  ring.
Qed.

(** The bound of Niven's argument for [p = S n], in the names of
    [cos_irrational]: [r = p / q] and [cos r = a / b]. *)
Lemma ci_bound :
  forall p q a b n, (0 < q)%Z -> (0 < p)%Z -> (0 < b)%Z -> (1 <= n)%nat ->
  cos (IZR p / IZR q) = IZR a / IZR b ->
  Nat.Odd (S n) -> Z.gcd (Z.of_nat (S n)) (2 * p) = 1%Z ->
  Z.gcd (Z.of_nat (S n)) b = 1%Z ->
  INR (fact n) <=
  IZR b * (IZR p / IZR q) * IZR p ^ 2 * (IZR p / IZR q * IZR p ^ 2 * (2 * IZR p)) ^ n.
Proof.
  intros p q a b n Hq Hp Hb Hn E Ho Hg2p Hgb.
  assert (Hq' : 0 < IZR q) by (apply IZR_lt; exact Hq).
  assert (Hp' : 0 < IZR p) by (apply IZR_lt; exact Hp).
  assert (Hb' : 0 < IZR b) by (apply IZR_lt; exact Hb).
  assert (Hr : 0 < IZR p / IZR q) by (apply Rdiv_lt_0_compat; assumption).
  assert (HP1 : (1 <= S n)%nat) by lia.
  destruct (cn_F0 p q (S n) Ho Hg2p) as [z0 [Hz0 Hgz0]].
  destruct (cn_Fr p q (S n) Hq HP1) as [z1 Hz1].
  replace (S n - 1)%nat with n in Hz0 by lia.
  (* The integer [b z0 - a (S n) z1] is not 0: [S n] divides [a (S n) z1]
     but not [b z0], as it is prime to [b] and to [z0], and [S n > 1]. *)
  assert (HW : (b * z0 - a * Z.of_nat (S n) * z1 <> 0)%Z).
  { intro HW0.
    assert (Hd : (Z.of_nat (S n) | b * z0)%Z) by (exists (a * z1)%Z; lia).
    assert (Hrel : rel_prime (Z.of_nat (S n)) (b * z0))
      by (apply rel_prime_mult; apply Zgcd_1_rel_prime; assumption).
    destruct Hrel as [_ _ Hg].
    assert (H1 : (Z.of_nat (S n) | 1)%Z) by (apply Hg; [apply Z.divide_refl | exact Hd]).
    apply Z.divide_pos_le in H1; lia. }
  destruct (MVT_cor2 (ci_G p q (S n)) (fun x => zp_ev (cn_poly p q (S n)) x * sin x)
    0 (IZR p / IZR q) Hr (fun c _ => ci_G_deriv p q (S n) c HP1)) as [c [Hc [Hc0 Hcr]]].
  cbv beta in Hc.
  rewrite (ci_G_ends p q (S n) Hq), E, Hz0, Hz1, cn_poly_ev, Rminus_0_r in Hc.
  replace (S n - 1)%nat with n in Hc by lia.
  change (fact (S n)) with (S n * fact n)%nat in Hc.
  rewrite mult_INR, (INR_IZR_INZ (S n)) in Hc.
  set (g := c ^ n * (IZR p - IZR q * c) ^ (2 * S n) * (2 * IZR p - IZR q * c) ^ n) in Hc.
  (* [b (G(r) - G(0)) = n! W] with the integer [W] above. *)
  assert (HbW : INR (fact n) * IZR (b * z0 - a * Z.of_nat (S n) * z1) =
    IZR b * g * (IZR p / IZR q) * sin c).
  { rewrite minus_IZR, !mult_IZR.
    replace (IZR b * g * (IZR p / IZR q) * sin c) with (IZR b * (g * sin c * (IZR p / IZR q)))
      by ring.
    rewrite <- Hc.
    field. lra. }
  (* On [(0, r)], [0 < q c < p], so [0 <= c^n <= r^n],
     [0 <= (p - q c)^(2 S n) <= p^(2 S n)] and [0 <= (2 p - q c)^n <= (2 p)^n]. *)
  assert (Hqc : IZR q * c < IZR p).
  { apply (Rmult_lt_compat_l (IZR q)) in Hcr; [| exact Hq'].
    replace (IZR q * (IZR p / IZR q)) with (IZR p) in Hcr by (field; lra).
    exact Hcr. }
  assert (Hqc0 : 0 < IZR q * c) by (apply Rmult_lt_0_compat; assumption).
  assert (H1 : 0 <= c ^ n <= (IZR p / IZR q) ^ n)
    by (split; [apply pow_le | apply pow_incr]; lra).
  assert (H2 : 0 <= (IZR p - IZR q * c) ^ (2 * S n) <= IZR p ^ (2 * S n))
    by (split; [apply pow_le | apply pow_incr]; lra).
  assert (H3 : 0 <= (2 * IZR p - IZR q * c) ^ n <= (2 * IZR p) ^ n)
    by (split; [apply pow_le | apply pow_incr]; lra).
  assert (Hg0 : 0 <= g)
    by (unfold g; apply Rmult_le_pos; [apply Rmult_le_pos |]; tauto).
  assert (Hg1 : g <= (IZR p / IZR q) ^ n * IZR p ^ (2 * S n) * (2 * IZR p) ^ n).
  { unfold g.
    apply Rmult_le_compat; [apply Rmult_le_pos | | apply Rmult_le_compat |]; tauto. }
  assert (EC : (IZR p / IZR q) ^ n * IZR p ^ (2 * S n) * (2 * IZR p) ^ n =
    IZR p ^ 2 * (IZR p / IZR q * IZR p ^ 2 * (2 * IZR p)) ^ n).
  { rewrite pow_mult, !Rpow_mult_distr.
    change ((IZR p ^ 2) ^ S n) with (IZR p ^ 2 * (IZR p ^ 2) ^ n).
    ring. }
  rewrite EC in Hg1.
  assert (Hbgr : 0 <= IZR b * g * (IZR p / IZR q))
    by (apply Rmult_le_pos; [apply Rmult_le_pos |]; lra).
  pose proof (SIN_bound c) as [Hs0 Hs1].
  assert (HX1 : IZR b * g * (IZR p / IZR q) * sin c <= IZR b * g * (IZR p / IZR q) * 1)
    by (apply Rmult_le_compat_l; assumption).
  assert (HX0 : IZR b * g * (IZR p / IZR q) * -1 <= IZR b * g * (IZR p / IZR q) * sin c)
    by (apply Rmult_le_compat_l; assumption).
  (* [|W| >= 1], so [n! <= |b (G(r) - G(0))| <= b g(c) r]. *)
  assert (Hf : 0 < INR (fact n)) by apply INR_fact_lt_0.
  assert (Hfg : INR (fact n) <= IZR b * g * (IZR p / IZR q)).
  { destruct (Z_le_gt_dec 1 (b * z0 - a * Z.of_nat (S n) * z1)) as [HW1 | HW1].
    - apply IZR_le in HW1.
      assert (A : INR (fact n) * 1 <= INR (fact n) * IZR (b * z0 - a * Z.of_nat (S n) * z1))
        by (apply Rmult_le_compat_l; lra).
      lra.
    - assert (HW2 : (b * z0 - a * Z.of_nat (S n) * z1 <= -1)%Z) by lia.
      apply IZR_le in HW2.
      assert (A : INR (fact n) * IZR (b * z0 - a * Z.of_nat (S n) * z1) <= INR (fact n) * -1)
        by (apply Rmult_le_compat_l; lra).
      lra. }
  assert (Hbr : 0 <= IZR b * (IZR p / IZR q))
    by (apply Rmult_le_pos; lra).
  apply (Rmult_le_compat_l _ _ _ Hbr) in Hg1.
  lra.
Qed.

Theorem cos_irrational :
  forall p q a b : Z, (0 < q)%Z -> p <> 0%Z -> (0 < b)%Z ->
  cos (IZR p / IZR q) <> IZR a / IZR b.
Proof.
  intros p q a b Hq Hp0 Hb E.
  (* [cos] is even, so take [p > 0]. *)
  assert (Hpos : exists p', (0 < p')%Z /\ cos (IZR p' / IZR q) = IZR a / IZR b).
  { destruct (Z_lt_le_dec 0 p) as [Hp | Hp].
    - exists p. split; assumption.
    - exists (- p)%Z. split; [lia |].
      rewrite opp_IZR, Rdiv_opp_l, cos_neg. exact E. }
  clear p Hp0 E. destruct Hpos as [p [Hp E]].
  assert (Hq' : 0 < IZR q) by (apply IZR_lt; exact Hq).
  assert (Hp' : 0 < IZR p) by (apply IZR_lt; exact Hp).
  assert (Hb' : 0 < IZR b) by (apply IZR_lt; exact Hb).
  assert (Hr : 0 < IZR p / IZR q) by (apply Rdiv_lt_0_compat; assumption).
  set (C := IZR p / IZR q * IZR p ^ 2 * (2 * IZR p)).
  set (B := IZR b * (IZR p / IZR q) * IZR p ^ 2).
  assert (HB : 0 < B).
  { unfold B. apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat |]; [lra | lra |].
    apply pow_lt. exact Hp'. }
  (* [C^n / n! < 1 / B] for [n >= N]. *)
  destruct (cv_speed_pow_fact C (/ B) (Rinv_0_lt_compat _ HB)) as [N HN].
  (* [n = 2 p b K] with [K = S N], and the odd [S n] is prime to [2 p] and to [b]. *)
  assert (Hpb : (0 < p * b)%Z) by (apply Z.mul_pos_pos; assumption).
  set (t := Z.to_nat (p * b)).
  assert (Ht : Z.of_nat t = (p * b)%Z) by (apply Z2Nat.id; lia).
  assert (Ht1 : (1 <= t)%nat) by lia.
  set (n := (2 * (t * S N))%nat).
  assert (HnN : (N <= n)%nat) by (unfold n; nia).
  assert (Hn1 : (1 <= n)%nat) by (unfold n; nia).
  assert (En : Z.of_nat (S n) = (1 + 2 * (p * b * Z.of_nat (S N)))%Z).
  { unfold n. rewrite Nat2Z.inj_succ, !Nat2Z.inj_mul, Ht. lia. }
  assert (Ho : Nat.Odd (S n)) by (exists (t * S N)%nat; unfold n; lia).
  assert (Hg2p : Z.gcd (Z.of_nat (S n)) (2 * p) = 1%Z).
  { rewrite En, Z.gcd_comm.
    replace (1 + 2 * (p * b * Z.of_nat (S N)))%Z with (1 + b * Z.of_nat (S N) * (2 * p))%Z
      by ring.
    rewrite Z.gcd_add_mult_diag_r. apply Z.gcd_1_r. }
  assert (Hgb : Z.gcd (Z.of_nat (S n)) b = 1%Z).
  { rewrite En, Z.gcd_comm.
    replace (1 + 2 * (p * b * Z.of_nat (S N)))%Z with (1 + 2 * p * Z.of_nat (S N) * b)%Z
      by ring.
    rewrite Z.gcd_add_mult_diag_r. apply Z.gcd_1_r. }
  pose proof (ci_bound p q a b n Hq Hp Hb Hn1 E Ho Hg2p Hgb) as Hbd.
  change (INR (fact n) <= B * C ^ n) in Hbd.
  specialize (HN n HnN).
  unfold R_dist in HN.
  rewrite Rminus_0_r in HN.
  apply Rabs_def2 in HN.
  destruct HN as [HN _].
  (* [B C^n < n!], against [ci_bound]. *)
  pose proof (INR_fact_lt_0 n) as Hf.
  assert (HBf : 0 < B * INR (fact n)) by (apply Rmult_lt_0_compat; assumption).
  apply (Rmult_lt_compat_l (B * INR (fact n))) in HN; [| exact HBf].
  replace (B * INR (fact n) * (C ^ n / INR (fact n))) with (B * C ^ n) in HN
    by (field; lra).
  replace (B * INR (fact n) * / B) with (INR (fact n)) in HN by (field; lra).
  lra.
Qed.
