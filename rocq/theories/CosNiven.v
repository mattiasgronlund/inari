(** * The polynomial of the proof that cos r is irrational

    For [r = a / b] with [b > 0] and an odd [p], Niven's polynomial for
    [cos r] (Niven, "Irrational Numbers", 1956, ch. 2) is
    [g(x) = x^(p-1) (a - b x)^(2p) (2a - b x)^(p-1)] ([cn_poly], with
    integer coefficients, of degree [4p - 2]), and [cn_d a b p k] its
    derivative of order [k]. [F = ch_alt (cn_d a b p) 0 (2p - 1)] is
    [g - g'' + g'''' - ...]. As [g(2r - x) = g(x)], the derivatives of
    odd order vanish at [r], so [F'(r) = 0] ([cn_F'r]). At 0, the
    derivatives of order below [p - 1] vanish, that of order [p - 1] is
    [(p-1)! a^(2p) (2a)^(p-1)], and the others are multiples of [p!], so
    [F(0)] is [(p-1)!] times an integer prime to [p] where [p] is prime to
    [2 a] ([cn_F0]). At [r], [g(r + u) = b^(p+1) u^(2p) (a - b u)^(p-1)
    (a + b u)^(p-1)], so the derivatives of order below [2p] vanish and
    the others are multiples of [(2p)!], and [F(r)] is [p!] times an
    integer ([cn_Fr]). *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Stdlib Require Import Znumtheory Zpow_facts.
From Inari Require Import NivenPoly NivenAlt NivenSym.

Open Scope R_scope.

(** [zp_linpow c b n l] is the list of [(c - b x)^n l(x)]. *)
Fixpoint zp_linpow (c b : Z) (n : nat) (l : list Z) : list Z :=
  match n with
  | O => l
  | S n => zp_lin c b (zp_linpow c b n l)
  end.

Definition cn_poly (a b : Z) (p : nat) : list Z :=
  repeat 0%Z (p - 1) ++ zp_linpow (2 * a) b (p - 1) (zp_qpow a b (2 * p)).

Definition cn_d (a b : Z) (p k : nat) (x : R) : R := zp_ev (zp_dn k (cn_poly a b p)) x.

Lemma zp_ev_linpow :
  forall c b n l x, zp_ev (zp_linpow c b n l) x = (IZR c - IZR b * x) ^ n * zp_ev l x.
Proof.
  intros c b n l x. induction n as [| n IH].
  - cbn [zp_linpow pow]. ring.
  - cbn [zp_linpow pow]. rewrite zp_ev_lin, IH. ring.
Qed.

Lemma zp_length_lin : forall a b l, length (zp_lin a b l) = S (length l).
Proof.
  intros a b l. unfold zp_lin, zp_scale. rewrite zp_length_add. cbn [length].
  rewrite !length_map. lia.
Qed.

Lemma zp_length_linpow : forall c b n l, length (zp_linpow c b n l) = (n + length l)%nat.
Proof.
  intros c b n l. induction n as [| n IH].
  - reflexivity.
  - cbn [zp_linpow]. rewrite zp_length_lin, IH. reflexivity.
Qed.

(** The constant coefficient of [(a - b x) l(x)] is [a l_0]. *)
Lemma zp_nth0_lin : forall a b l, nth 0 (zp_lin a b l) 0%Z = (a * nth 0 l 0%Z)%Z.
Proof.
  intros a b [| c l]; unfold zp_lin, zp_scale; rewrite zp_nth_add; cbn [map nth]; ring.
Qed.

Lemma zp_nth0_linpow :
  forall c b n l, nth 0 (zp_linpow c b n l) 0%Z = (c ^ Z.of_nat n * nth 0 l 0%Z)%Z.
Proof.
  intros c b n l. induction n as [| n IH].
  - cbn [zp_linpow]. rewrite Z.pow_0_r. ring.
  - cbn [zp_linpow]. rewrite zp_nth0_lin, IH, Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma zp_nth0_qpow : forall a b n, nth 0 (zp_qpow a b n) 0%Z = (a ^ Z.of_nat n)%Z.
Proof.
  intros a b n. induction n as [| n IH].
  - reflexivity.
  - cbn [zp_qpow]. rewrite zp_nth0_lin, IH, Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma cn_poly_ev :
  forall a b p x,
  zp_ev (cn_poly a b p) x =
  x ^ (p - 1) * (IZR a - IZR b * x) ^ (2 * p) * (2 * IZR a - IZR b * x) ^ (p - 1).
Proof.
  intros a b p x. unfold cn_poly.
  rewrite zp_ev_shift, zp_ev_linpow, zp_ev_qpow, mult_IZR. ring.
Qed.

Lemma cn_d_chain : forall a b p, ch_chain (cn_d a b p).
Proof.
  intros a b p k x. unfold cn_d. apply zp_ev_dn.
Qed.

Lemma cn_length :
  forall a b p, (1 <= p)%nat -> length (cn_poly a b p) = (4 * p - 1)%nat.
Proof.
  intros a b p Hp. unfold cn_poly.
  rewrite length_app, repeat_length, zp_length_linpow, zp_length_qpow. lia.
Qed.

Lemma cn_d_high : forall a b p x, (1 <= p)%nat -> cn_d a b p (4 * p) x = 0.
Proof.
  intros a b p x Hp. unfold cn_d. apply zp_ev_dn_high.
  rewrite cn_length by exact Hp. lia.
Qed.

(** [g(x) = (x (2a - b x))^(p-1) ((a - b x)^2)^p], the form in which its
    symmetry about [a / b] shows. *)
Lemma cn_poly_ev2 :
  forall a b p x,
  zp_ev (cn_poly a b p) x =
  (x * (2 * IZR a - IZR b * x)) ^ (p - 1) * ((IZR a - IZR b * x) ^ 2) ^ p.
Proof.
  intros a b p x. rewrite cn_poly_ev, Rpow_mult_distr, <- pow_mult. ring.
Qed.

(** With [a = r b], [g(2r - x) = g(x)], so the chain of [g] is that of its
    reflection about [r]. *)
Lemma cn_d_reflect :
  forall a b p r, IZR a = r * IZR b ->
  forall k x, cn_d a b p k x = (-1) ^ k * cn_d a b p k (2 * r - x).
Proof.
  intros a b p r Ha k x.
  assert (H := ch_unique (cn_d a b p) (fun k x => (-1) ^ k * cn_d a b p k (2 * r - x))
    (cn_d_chain a b p) (ch_reflect (cn_d a b p) (2 * r) (cn_d_chain a b p))).
  assert (H0 : forall x, cn_d a b p O x = (-1) ^ 0 * cn_d a b p O (2 * r - x)).
  { intros y. unfold cn_d. cbn [zp_dn]. rewrite pow_O, Rmult_1_l, !cn_poly_ev2.
    (* [y (2a - b y) = b y (2r - y)] and [(a - b y)^2 = b^2 (r - y)^2]. *)
    f_equal; f_equal; rewrite Ha; ring. }
  exact (H H0 k x).
Qed.

Lemma cn_F'r :
  forall a b p, (0 < b)%Z ->
  ch_alt (cn_d a b p) 1 (2 * p - 1) (IZR a / IZR b) = 0.
Proof.
  intros a b p Hb.
  assert (Hb' : 0 < IZR b) by (apply IZR_lt; exact Hb).
  assert (Ha : IZR a = IZR a / IZR b * IZR b) by (field; lra).
  set (r := IZR a / IZR b) in *.
  (* The derivatives of odd order vanish at the centre [r] of the symmetry,
     so [F'(r)], their alternating sum, is its own opposite. *)
  assert (Hr : forall k, cn_d a b p k r = (-1) ^ k * cn_d a b p k r).
  { intro k. pose proof (cn_d_reflect a b p r Ha k r) as H.
    replace (2 * r - r) with r in H by ring. exact H. }
  pose proof (ch_alt_reflect (cn_d a b p) r r Hr (2 * p - 1) 1) as H.
  cbn [pow] in H. lra.
Qed.

(** [ch_alt_mult] for the terms from order [s0] on. *)
Lemma ch_alt_mult_ge :
  forall d N x0 s0, (forall k, (s0 <= k)%nat -> exists z, d k x0 = N * IZR z) ->
  forall m s, (s0 <= s)%nat -> exists z, ch_alt d s m x0 = N * IZR z.
Proof.
  intros d N x0 s0 Hk m.
  induction m as [| m IHm]; intros s Hs.
  - apply Hk, Hs.
  - destruct (Hk s Hs) as [z1 H1]. destruct (IHm (S (S s))) as [z2 H2]; [lia |].
    exists (z1 - z2)%Z. cbn [ch_alt]. rewrite H1, H2, minus_IZR. ring.
Qed.

(** If every term but the one of order [k0] is a multiple of [N P] at
    [x0], and that one is [N L], the alternating sum from [s] that reaches
    [k0 = s + 2 j] is [N] times [(-1)^j L] plus a multiple of [P]. *)
Lemma ch_alt_one :
  forall d N P L x0 k0,
  (forall k, k <> k0 -> exists z, d k x0 = N * (IZR P * IZR z)) ->
  d k0 x0 = N * IZR L ->
  forall m s j, k0 = (s + 2 * j)%nat -> (j <= m)%nat ->
  exists z, ch_alt d s m x0 = N * ((-1) ^ j * IZR L + IZR P * IZR z).
Proof.
  intros d N P L x0 k0 Hk HL m.
  induction m as [| m IHm]; intros s j Hs Hj.
  - assert (j = 0%nat) by lia. subst j. exists 0%Z. cbn [ch_alt].
    replace (d s x0) with (d k0 x0) by (f_equal; lia).
    rewrite HL. cbn [pow]. ring.
  - destruct j as [| j].
    + (* [s = k0]: the terms after it are multiples of [N P]. *)
      destruct (ch_alt_mult_ge d (N * IZR P) x0 (S k0)) with (m := m) (s := S (S s))
        as [z Hz].
      * intros k Hk'. destruct (Hk k) as [z Hz]; [lia |]. exists z. rewrite Hz. ring.
      * lia.
      * exists (- z)%Z. cbn [ch_alt]. rewrite Hz.
        replace (d s x0) with (d k0 x0) by (f_equal; lia).
        rewrite HL, opp_IZR. cbn [pow]. ring.
    + (* [s < k0]: the first term is a multiple of [N P]. *)
      destruct (Hk s) as [z1 H1]; [lia |].
      destruct (IHm (S (S s)) j) as [z2 H2]; [lia | lia |].
      exists (z1 - z2)%Z. cbn [ch_alt]. rewrite H1, H2, minus_IZR. cbn [pow]. ring.
Qed.

Lemma cn_d_0 :
  forall a b p k, cn_d a b p k 0 = IZR (Z.of_nat (fact k) * nth k (cn_poly a b p) 0%Z).
Proof.
  intros a b p k. unfold cn_d. apply zp_ev_dn_0.
Qed.

Lemma cn_fact_pred : forall p, (1 <= p)%nat -> fact p = (p * fact (p - 1))%nat.
Proof.
  intros [| p] Hp; [lia |].
  replace (S p - 1)%nat with p by lia. reflexivity.
Qed.

Lemma cn_F0 :
  forall a b p, Nat.Odd p -> Z.gcd (Z.of_nat p) (2 * a) = 1%Z ->
  exists z, ch_alt (cn_d a b p) 0 (2 * p - 1) 0 = INR (fact (p - 1)) * IZR z /\
    Z.gcd (Z.of_nat p) z = 1%Z.
Proof.
  intros a b p [n Hn] Hg.
  assert (Hp : (1 <= p)%nat) by lia.
  (* The term of order [p - 1] is [(p-1)! (2a)^(p-1) a^(2p)], the constant
     coefficient of [(2a - b x)^(p-1) (a - b x)^(2p)]. *)
  assert (HL : cn_d a b p (p - 1) 0 =
    INR (fact (p - 1)) * IZR ((2 * a) ^ Z.of_nat (p - 1) * a ^ Z.of_nat (2 * p))).
  { rewrite cn_d_0. unfold cn_poly.
    rewrite app_nth2 by (rewrite repeat_length; lia).
    rewrite repeat_length, Nat.sub_diag, zp_nth0_linpow, zp_nth0_qpow.
    rewrite mult_IZR, <- INR_IZR_INZ. reflexivity. }
  (* Below [p - 1] the coefficients are 0; above, [k!] is a multiple of
     [p! = p (p-1)!]. *)
  assert (Hk : forall k, k <> (p - 1)%nat -> exists z,
    cn_d a b p k 0 = INR (fact (p - 1)) * (IZR (Z.of_nat p) * IZR z)).
  { intros k Hk. rewrite cn_d_0.
    destruct (Nat.lt_ge_cases k (p - 1)) as [Hlt | Hge].
    - exists 0%Z. unfold cn_poly.
      rewrite app_nth1 by (rewrite repeat_length; exact Hlt).
      rewrite nth_repeat, Z.mul_0_r. ring.
    - destruct (nv_fact_mult p k) as [m Hm]; [lia |].
      exists (Z.of_nat m * nth k (cn_poly a b p) 0)%Z.
      rewrite Hm, cn_fact_pred by exact Hp.
      rewrite !Nat2Z.inj_mul, !mult_IZR, INR_IZR_INZ. ring. }
  destruct (ch_alt_one (cn_d a b p) (INR (fact (p - 1))) (Z.of_nat p)
    ((2 * a) ^ Z.of_nat (p - 1) * a ^ Z.of_nat (2 * p)) 0 (p - 1) Hk HL
    (2 * p - 1) 0 n) as [z Hz]; [lia | lia |].
  exists ((-1) ^ Z.of_nat n * ((2 * a) ^ Z.of_nat (p - 1) * a ^ Z.of_nat (2 * p))
    + Z.of_nat p * z)%Z.
  split.
  - rewrite Hz, plus_IZR, (mult_IZR ((-1) ^ Z.of_nat n)%Z), (mult_IZR (Z.of_nat p)),
      <- (pow_IZR (-1)). reflexivity.
  - (* [p] is prime to [2a], hence to [a], to their powers and to [(-1)^n],
       and so to the sum, whose other term is a multiple of [p]. *)
    rewrite (Z.mul_comm (Z.of_nat p) z), Z.gcd_add_mult_diag_r.
    apply Zgcd_1_rel_prime. apply Zgcd_1_rel_prime in Hg.
    assert (Ha : rel_prime (Z.of_nat p) a).
    { apply rel_prime_sym. apply (rel_prime_div (2 * a)).
      - apply rel_prime_sym. exact Hg.
      - apply Z.divide_factor_r. }
    assert (H1 : rel_prime (Z.of_nat p) (-1)).
    { apply rel_prime_sym. apply (rel_prime_div 1).
      - apply rel_prime_1.
      - exists (-1)%Z. reflexivity. }
    repeat apply rel_prime_mult; apply rel_prime_Zpower_r; try lia; assumption.
Qed.

(** The chain of [x => d k (c + x)] is that of [g(c + x)]. *)
Lemma cn_shift_chain : forall a b p c, ch_chain (fun k u => cn_d a b p k (c + u)).
Proof.
  intros a b p c k u. cbv beta.
  assert (H1 : derivable_pt_lim (fun u => c + u) u 1).
  { replace 1 with (0 + 1) by ring.
    apply (derivable_pt_lim_plus (fct_cte c) id).
    - apply derivable_pt_lim_const.
    - apply derivable_pt_lim_id. }
  replace (cn_d a b p (S k) (c + u)) with (cn_d a b p (S k) (c + u) * 1) by ring.
  apply (derivable_pt_lim_comp (fun u => c + u) (cn_d a b p k)).
  - exact H1.
  - apply cn_d_chain.
Qed.

Lemma cn_Fr :
  forall a b p, (0 < b)%Z -> (1 <= p)%nat ->
  exists z, ch_alt (cn_d a b p) 0 (2 * p - 1) (IZR a / IZR b) = INR (fact p) * IZR z.
Proof.
  intros a b p Hb Hp.
  assert (Hb' : 0 < IZR b) by (apply IZR_lt; exact Hb).
  assert (Ha : IZR a = IZR a / IZR b * IZR b) by (field; lra).
  set (r := IZR a / IZR b) in *. clearbody r.
  (* [g(r + u) = b^(p+1) u^(2p) (a - b u)^(p-1) (a + b u)^(p-1)], the
     polynomial [hl] with integer coefficients and [2p] leading zeros. *)
  set (hl := repeat 0%Z (2 * p) ++
    zp_scale (b ^ Z.of_nat (p + 1)) (zp_linpow a b (p - 1) (zp_qpow a (- b) (p - 1)))).
  assert (H := ch_unique (fun k u => cn_d a b p k (r + u)) (fun k => zp_ev (zp_dn k hl))
    (cn_shift_chain a b p r) (fun k u => zp_ev_dn k hl u)).
  assert (H0 : forall u, cn_d a b p O (r + u) = zp_ev (zp_dn O hl) u).
  { intro u. unfold cn_d, hl. cbn [zp_dn].
    rewrite cn_poly_ev, zp_ev_shift, zp_ev_scale, zp_ev_linpow, zp_ev_qpow, <- pow_IZR,
      opp_IZR.
    replace (IZR a - IZR b * (r + u)) with (- (IZR b * u)) by (rewrite Ha; ring).
    replace (2 * IZR a - IZR b * (r + u)) with (IZR a - IZR b * u) by (rewrite Ha; ring).
    replace (IZR a - - IZR b * u) with (IZR b * (r + u)) by (rewrite Ha; ring).
    assert (E : (- (IZR b * u)) ^ (2 * p) = IZR b ^ (p + 1) * IZR b ^ (p - 1) * u ^ (2 * p)).
    { rewrite <- pow_add. replace (p + 1 + (p - 1))%nat with (2 * p)%nat by lia.
      rewrite <- Rpow_mult_distr, !pow_mult. f_equal. ring. }
    rewrite E, Rpow_mult_distr. ring. }
  apply ch_alt_mult. intro k.
  specialize (H H0 k 0). cbv beta in H. rewrite Rplus_0_r, zp_ev_dn_0 in H. rewrite H.
  (* Below [2 p] the coefficients of [hl] are 0; from [p] on, [k!] is a
     multiple of [p!]. *)
  destruct (Nat.lt_ge_cases k p) as [Hlt | Hge].
  - exists 0%Z. unfold hl.
    rewrite app_nth1 by (rewrite repeat_length; lia).
    rewrite nth_repeat, Z.mul_0_r. ring.
  - destruct (nv_fact_mult p k Hge) as [m Hm].
    exists (Z.of_nat m * nth k hl 0)%Z.
    rewrite Hm, Nat2Z.inj_mul, !mult_IZR, INR_IZR_INZ. ring.
Qed.
