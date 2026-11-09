(** * e^r is irrational for every rational r other than 0

    Niven's method, as for [pi_irrational] ([PiIrrational.v]), with the
    integral replaced by the mean value theorem. For an integer [k > 0]
    with [e^k = a / b], let [f] be [x^n (1 - x)^n] ([nv_poly 1 1 n] of
    [NivenSym.v]), [F] the sum of [(-1)^j k^(2n-j) f^(j)] for [j] from 0
    to [2 n], so that [F' + k F = k^(2n+1) f], and [G(x) = e^(kx) F(x)],
    whose derivative is [k^(2n+1) e^(kx) f(x)]. [b (G(1) - G(0)) =
    a F(1) - b F(0)] is [n!] times an integer, as [f(1 - x) = f(x)], and
    by the mean value theorem it is [b k^(2n+1) e^(kc) f(c)] for some [c]
    in [(0, 1)], which is positive and at most [b k e^k (k^2)^n]. So
    [n! <= b k e^k (k^2)^n], which fails for large [n]. A rational [p / q]
    reduces to it: [(e^(p/q))^q = e^p], and [e^(-k) = 1 / e^k]. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Inari Require Import NivenPoly NivenAlt NivenSym.

Open Scope R_scope.

(** [derivable_pt_lim] with its limit rewritten. *)
Lemma ex_lim_eq :
  forall f x l l', l = l' -> derivable_pt_lim f x l -> derivable_pt_lim f x l'.
Proof.
  intros f x l l' E H. rewrite <- E. exact H.
Qed.

(** [x^n (1 - x)^n] is symmetric about [1 / 2], so its derivatives at 1
    are those at 0 up to the sign [(-1) ^ k]. The proof of [nv_d_sym]
    with [1] in place of [PI]. *)
Lemma nv_d_sym1 : forall n k, nv_d 1 1 n k 1 = (-1) ^ k * nv_d 1 1 n k 0.
Proof.
  intros n k.
  assert (H := ch_unique (nv_d 1 1 n) (fun k x => (-1) ^ k * nv_d 1 1 n k (1 - x))
    (nv_d_chain 1 1 n) (ch_reflect (nv_d 1 1 n) 1 (nv_d_chain 1 1 n))).
  assert (H0 : forall x, nv_d 1 1 n O x = (-1) ^ 0 * nv_d 1 1 n O (1 - x)).
  { intros x. unfold nv_d. cbn [zp_dn]. rewrite pow_O, Rmult_1_l, !nv_poly_ev.
    rewrite <- !Rpow_mult_distr. f_equal. ring. }
  specialize (H H0 k 1). cbv beta in H. rewrite H.
  replace (1 - 1) with 0 by ring. reflexivity.
Qed.

Lemma nv_d_int1 : forall n k, exists z, nv_d 1 1 n k 1 = INR (fact n) * IZR z.
Proof.
  intros n k. destruct (nv_d_int 1 1 n k) as [z Hz].
  exists ((-1) ^ Z.of_nat k * z)%Z.
  rewrite nv_d_sym1, Hz, mult_IZR, <- pow_IZR. ring.
Qed.

(** The derivative of order [2 n + 1], past the degree [2 n], is 0. *)
Lemma nv_d_odd : forall n x, nv_d 1 1 n (2 * n + 1) x = 0.
Proof.
  intros n x. unfold nv_d. apply zp_ev_dn_high.
  unfold nv_poly. rewrite length_app, repeat_length, zp_length_qpow. lia.
Qed.

(** [ep_S d k s m] is [d s k^m - d (s + 1) k^(m-1) + ... + (-1)^m d (s + m)],
    the sum of [(-1)^j k^(m-j) d (s + j)] for [j] from 0 to [m]. *)
Fixpoint ep_S (d : nat -> R -> R) (k : R) (s m : nat) (x : R) : R :=
  match m with
  | O => d s x
  | S m => k ^ S m * d s x - ep_S d k (S s) m x
  end.

Lemma ep_S_deriv :
  forall d k, ch_chain d ->
  forall m s x, derivable_pt_lim (ep_S d k s m) x (ep_S d k (S s) m x).
Proof.
  intros d k Hd m.
  induction m as [|m IHm]; intros s x; cbn [ep_S].
  - apply Hd.
  - apply derivable_pt_lim_minus.
    + apply (derivable_pt_lim_scal (d s)). apply Hd.
    + apply IHm.
Qed.

(** [k F + F'] telescopes to [k^(m+1) d s] and one last term. *)
Lemma ep_S_rec :
  forall d k m s x,
  k * ep_S d k s m x + ep_S d k (S s) m x
  = k ^ S m * d s x + (-1) ^ m * d (S (s + m)) x.
Proof.
  intros d k m.
  induction m as [|m IHm]; intros s x; cbn [ep_S].
  - rewrite Nat.add_0_r. simpl. ring.
  - specialize (IHm (S s) x).
    replace (S (s + S m)) with (S (S s + m)) by lia.
    replace (ep_S d k (S (S s)) m x)
      with (k ^ S m * d (S s) x + (-1) ^ m * d (S (S s + m)) x - k * ep_S d k (S s) m x)
      by lra.
    simpl. ring.
Qed.

(** If every [d j] is a multiple of [N] at [x0], so is every sum. *)
Lemma ep_S_mult :
  forall d k N x0, (forall j, exists z, d j x0 = N * IZR z) ->
  forall m s, exists z, ep_S d (IZR k) s m x0 = N * IZR z.
Proof.
  intros d k N x0 Hj m.
  induction m as [|m IHm]; intros s.
  - apply Hj.
  - destruct (Hj s) as [z1 H1]. destruct (IHm (S s)) as [z2 H2].
    exists (k ^ Z.of_nat (S m) * z1 - z2)%Z. cbn [ep_S].
    rewrite H1, H2, minus_IZR, mult_IZR, <- pow_IZR. ring.
Qed.

Definition ex_F (k : R) (n : nat) (x : R) : R := ep_S (nv_d 1 1 n) k 0 (2 * n) x.

Definition ex_G (k : R) (n : nat) (x : R) : R := exp (k * x) * ex_F k n x.

Lemma ex_G_deriv :
  forall k n x,
  derivable_pt_lim (ex_G k n) x (k ^ (2 * n + 1) * exp (k * x) * zp_ev (nv_poly 1 1 n) x).
Proof.
  intros k n x.
  assert (Hl : derivable_pt_lim (fun x => k * x) x k).
  { eapply ex_lim_eq; [| apply (derivable_pt_lim_scal id k x 1), derivable_pt_lim_id].
    ring. }
  assert (He : derivable_pt_lim (fun x => exp (k * x)) x (exp (k * x) * k)).
  { apply (derivable_pt_lim_comp (fun x => k * x) exp x k (exp (k * x)) Hl).
    apply derivable_pt_lim_exp. }
  pose proof (derivable_pt_lim_mult _ _ x _ _ He
    (ep_S_deriv (nv_d 1 1 n) k (nv_d_chain 1 1 n) (2 * n) 0 x)) as H.
  (* [k F + F' = k^(2n+1) f], as the last term is a derivative of order
     [2 n + 1], past the degree. *)
  pose proof (ep_S_rec (nv_d 1 1 n) k (2 * n) 0 x) as Hr.
  replace (S (0 + 2 * n)) with (2 * n + 1)%nat in Hr by lia.
  rewrite nv_d_odd, Rmult_0_r, Rplus_0_r in Hr.
  replace (S (2 * n)) with (2 * n + 1)%nat in Hr by lia.
  change (zp_ev (nv_poly 1 1 n) x) with (nv_d 1 1 n O x).
  eapply ex_lim_eq; [| exact H].
  transitivity (exp (k * x) * (k * ep_S (nv_d 1 1 n) k 0 (2 * n) x
    + ep_S (nv_d 1 1 n) k 1 (2 * n) x)); [| rewrite Hr; ring].
  unfold ex_F. ring.
Qed.

(** If [e^k = a / b], then [n! <= b e^k k^(2n+1)] for every [n]. *)
Lemma ex_bound :
  forall k a b n, (0 < k)%Z -> (0 < b)%Z -> exp (IZR k) = IZR a / IZR b ->
  INR (fact n) <= IZR b * exp (IZR k) * IZR k ^ (2 * n + 1).
Proof.
  intros k a b n Hk Hb E.
  assert (HK : 0 < IZR k) by (apply IZR_lt; exact Hk).
  assert (Hb' : 0 < IZR b) by (apply IZR_lt; exact Hb).
  assert (Ea : IZR a = exp (IZR k) * IZR b) by (rewrite E; field; lra).
  destruct (MVT_cor2 (ex_G (IZR k) n)
    (fun x => IZR k ^ (2 * n + 1) * exp (IZR k * x) * zp_ev (nv_poly 1 1 n) x) 0 1 Rlt_0_1
    (fun c _ => ex_G_deriv (IZR k) n c)) as [c [Hc [Hc0 Hc1]]].
  cbv beta in Hc.
  unfold ex_G, ex_F in Hc.
  rewrite Rmult_1_r, Rmult_0_r, exp_0, Rmult_1_l, Rminus_0_r, Rmult_1_r in Hc.
  destruct (ep_S_mult (nv_d 1 1 n) k (INR (fact n)) 1 (nv_d_int1 n) (2 * n) 0) as [z1 H1].
  destruct (ep_S_mult (nv_d 1 1 n) k (INR (fact n)) 0 (nv_d_int 1 1 n) (2 * n) 0) as [z0 H0].
  rewrite H1, H0, nv_poly_ev in Hc.
  (* Hc : e^k n! z1 - n! z0 = k^(2n+1) e^(kc) c^n (1 - c)^n. Times [b],
     the left side is [n!] times the integer [a z1 - b z0]. *)
  replace (c ^ n * (IZR 1 - IZR 1 * c) ^ n) with ((c * (1 - c)) ^ n) in Hc
    by (rewrite Rpow_mult_distr; f_equal; f_equal; ring).
  assert (HZ : INR (fact n) * IZR (a * z1 - b * z0)
    = IZR b * (IZR k ^ (2 * n + 1) * exp (IZR k * c) * (c * (1 - c)) ^ n)).
  { rewrite <- Hc, minus_IZR, !mult_IZR, Ea. ring. }
  assert (Hf0 : 0 < (c * (1 - c)) ^ n) by (apply pow_lt; nra).
  assert (Hf1 : (c * (1 - c)) ^ n <= 1)
    by (rewrite <- (pow1 n) at 2; apply pow_incr; split; nra).
  assert (He0 : 0 < exp (IZR k * c)) by apply exp_pos.
  assert (He1 : exp (IZR k * c) <= exp (IZR k))
    by (apply Rlt_le, exp_increasing; nra).
  assert (Hk0 : 0 < IZR k ^ (2 * n + 1)) by (apply pow_lt; exact HK).
  assert (Hn : 0 < INR (fact n)) by apply INR_fact_lt_0.
  assert (HR0 : 0 < IZR b * (IZR k ^ (2 * n + 1) * exp (IZR k * c) * (c * (1 - c)) ^ n)).
  { apply Rmult_lt_0_compat; [exact Hb' |].
    apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat |]; assumption. }
  (* The integer is positive, so at least 1. *)
  assert (Hz1 : 1 <= IZR (a * z1 - b * z0)).
  { assert (Hz0 : 0 < IZR (a * z1 - b * z0)).
    { apply (Rmult_lt_reg_l (INR (fact n))); [exact Hn |].
      rewrite Rmult_0_r, HZ. exact HR0. }
    apply IZR_le. apply lt_0_IZR in Hz0. lia. }
  assert (A : INR (fact n) <= INR (fact n) * IZR (a * z1 - b * z0)) by nra.
  assert (B : IZR k ^ (2 * n + 1) * exp (IZR k * c) * (c * (1 - c)) ^ n
    <= IZR k ^ (2 * n + 1) * exp (IZR k)).
  { rewrite <- (Rmult_1_r (IZR k ^ (2 * n + 1) * exp (IZR k))).
    apply Rmult_le_compat; [| lra | | exact Hf1].
    - apply Rmult_le_pos; lra.
    - apply Rmult_le_compat_l; lra. }
  assert (C : IZR b * (IZR k ^ (2 * n + 1) * exp (IZR k * c) * (c * (1 - c)) ^ n)
    <= IZR b * (IZR k ^ (2 * n + 1) * exp (IZR k)))
    by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

(** [e^k] is irrational for every integer [k > 0]. *)
Lemma exp_irrational_pos :
  forall k a b : Z, (0 < k)%Z -> (0 < b)%Z -> exp (IZR k) <> IZR a / IZR b.
Proof.
  intros k a b Hk Hb E.
  assert (HK : 0 < IZR k) by (apply IZR_lt; exact Hk).
  assert (Hb' : 0 < IZR b) by (apply IZR_lt; exact Hb).
  assert (HC : 0 < IZR b * exp (IZR k) * IZR k).
  { apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat |]; [exact Hb' | apply exp_pos | exact HK]. }
  destruct (cv_speed_pow_fact (IZR k ^ 2) (/ (IZR b * exp (IZR k) * IZR k))
    (Rinv_0_lt_compat _ HC)) as [N HN].
  specialize (HN N (Nat.le_refl N)).
  unfold R_dist in HN.
  cbv beta in HN.
  rewrite Rminus_0_r in HN.
  apply Rabs_def2 in HN.
  destruct HN as [HN _].
  pose proof (ex_bound k a b N Hk Hb E) as HB.
  rewrite pow_add, pow_mult, pow_1 in HB.
  pose proof (INR_fact_lt_0 N) as Hf.
  pose proof (exp_pos (IZR k)) as He.
  (* [(k^2)^N / N! < 1 / (b e^k k)], so [b e^k k (k^2)^N < N!], against
     [ex_bound]. *)
  assert (HX : IZR b * exp (IZR k) * IZR k * (IZR k ^ 2) ^ N < INR (fact N)).
  { apply (Rmult_lt_reg_r (/ INR (fact N) * / (IZR b * exp (IZR k) * IZR k))).
    - apply Rmult_lt_0_compat; apply Rinv_0_lt_compat; assumption.
    - replace (IZR b * exp (IZR k) * IZR k * (IZR k ^ 2) ^ N
        * (/ INR (fact N) * / (IZR b * exp (IZR k) * IZR k)))
        with ((IZR k ^ 2) ^ N / INR (fact N)) by (field; repeat split; lra).
      replace (INR (fact N) * (/ INR (fact N) * / (IZR b * exp (IZR k) * IZR k)))
        with (/ (IZR b * exp (IZR k) * IZR k)) by (field; repeat split; lra).
      exact HN. }
  lra.
Qed.

(** [e^(n r) = (e^r)^n]. *)
Lemma exp_mult_nat : forall n r, exp (INR n * r) = exp r ^ n.
Proof.
  induction n as [|n IHn]; intros r.
  - simpl. rewrite Rmult_0_l, exp_0. reflexivity.
  - rewrite S_INR, Rmult_plus_distr_r, Rmult_1_l, exp_plus, IHn. simpl. ring.
Qed.

Theorem exp_irrational :
  forall p q a b : Z, (0 < q)%Z -> p <> 0%Z -> (0 < b)%Z ->
  exp (IZR p / IZR q) <> IZR a / IZR b.
Proof.
  intros p q a b Hq Hp Hb E.
  assert (Hq' : 0 < IZR q) by (apply IZR_lt; exact Hq).
  assert (Hb' : 0 < IZR b) by (apply IZR_lt; exact Hb).
  assert (Hm : INR (Z.to_nat q) = IZR q)
    by (rewrite INR_IZR_INZ, Z2Nat.id by lia; reflexivity).
  (* [e^p = (a / b)^q = a^q / b^q]. *)
  assert (Ep : exp (IZR p)
    = IZR (a ^ Z.of_nat (Z.to_nat q)) / IZR (b ^ Z.of_nat (Z.to_nat q))).
  { replace (IZR p) with (INR (Z.to_nat q) * (IZR p / IZR q)) by (rewrite Hm; field; lra).
    rewrite exp_mult_nat, E, <- !pow_IZR.
    unfold Rdiv. rewrite Rpow_mult_distr, pow_inv. reflexivity. }
  assert (HB : (0 < b ^ Z.of_nat (Z.to_nat q))%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (HB' : 0 < IZR (b ^ Z.of_nat (Z.to_nat q))) by (apply IZR_lt; exact HB).
  (* [a^q > 0], as [e^p > 0]. *)
  assert (HA' : 0 < IZR (a ^ Z.of_nat (Z.to_nat q))).
  { replace (IZR (a ^ Z.of_nat (Z.to_nat q)))
      with (exp (IZR p) * IZR (b ^ Z.of_nat (Z.to_nat q))) by (rewrite Ep; field; lra).
    apply Rmult_lt_0_compat; [apply exp_pos | exact HB']. }
  assert (HA : (0 < a ^ Z.of_nat (Z.to_nat q))%Z) by (apply lt_IZR; exact HA').
  destruct (Z.lt_trichotomy p 0) as [Hn | [H0 | Hpos]].
  - (* [e^(-p) = b^q / a^q], with [-p > 0]. *)
    assert (Hn' : (0 < - p)%Z) by lia.
    apply (exp_irrational_pos (- p) (b ^ Z.of_nat (Z.to_nat q)) _ Hn' HA).
    rewrite opp_IZR, exp_Ropp, Ep. field. lra.
  - exact (Hp H0).
  - exact (exp_irrational_pos p _ _ Hpos HB Ep).
Qed.
