(** * Niven's polynomial and its derivatives at 0 and π

    For [PiIrrational.v]. If [PI = a / b], Niven's polynomial
    [x ^ n * (a - b x) ^ n / n!] (Niven, 1947, "A simple proof that π is
    irrational") is symmetric about [PI / 2]. [nv_poly a b n] is it times
    [n!], with integer coefficients, and [nv_d a b n k] its [k]-th
    derivative. At 0 each derivative is [k!] times a coefficient, which is
    0 for [k < n], so it is [n!] times an integer ([nv_d_int]); at [PI] it
    is the same up to the sign [(-1) ^ k] ([nv_d_sym]), by the symmetry.
    The derivative of order [2 n + 2], past the degree [2 n], is 0
    ([nv_d_high]). *)

From Stdlib Require Import ZArith Reals Lra Lia List.
Import ListNotations.
From Inari Require Import NivenPoly NivenAlt.

Open Scope R_scope.

Definition nv_poly (a b : Z) (n : nat) : list Z := repeat 0%Z n ++ zp_qpow a b n.

Definition nv_d (a b : Z) (n k : nat) (x : R) : R := zp_ev (zp_dn k (nv_poly a b n)) x.

Lemma nv_poly_ev :
  forall a b n x, zp_ev (nv_poly a b n) x = x ^ n * (IZR a - IZR b * x) ^ n.
Proof.
  intros a b n x. unfold nv_poly. rewrite zp_ev_shift, zp_ev_qpow. reflexivity.
Qed.

Lemma nv_d_chain : forall a b n, ch_chain (nv_d a b n).
Proof.
  intros a b n k x. unfold nv_d. apply zp_ev_dn.
Qed.

Lemma nv_d_sym :
  forall a b n k, (0 < b)%Z -> PI = IZR a / IZR b ->
  nv_d a b n k PI = (-1) ^ k * nv_d a b n k 0.
Proof.
  intros a b n k Hb Hpi.
  assert (Hb' : 0 < IZR b) by (apply IZR_lt; exact Hb).
  assert (Ha : IZR a = PI * IZR b) by (rewrite Hpi; field; lra).
  (* Both [nv_d a b n] and its reflection about [PI / 2] are chains of
     derivatives, and they start with the same polynomial, since
     [x (a - b x) = b x (PI - x)] is symmetric about [PI / 2]. *)
  assert (H := ch_unique (nv_d a b n) (fun k x => (-1) ^ k * nv_d a b n k (PI - x))
    (nv_d_chain a b n) (ch_reflect (nv_d a b n) PI (nv_d_chain a b n))).
  assert (H0 : forall x, nv_d a b n O x = (-1) ^ 0 * nv_d a b n O (PI - x)).
  { intros x. unfold nv_d. cbn [zp_dn]. rewrite pow_O, Rmult_1_l, !nv_poly_ev, Ha.
    rewrite <- !Rpow_mult_distr. f_equal. ring. }
  specialize (H H0 k PI). cbv beta in H. rewrite H.
  replace (PI - PI) with 0 by ring. reflexivity.
Qed.

(** [k!] is a multiple of [n!] once [n <= k]. *)
Lemma nv_fact_mult : forall n k, (n <= k)%nat -> exists m, fact k = (fact n * m)%nat.
Proof.
  intros n k Hk. induction Hk as [|k Hk [m Hm]].
  - exists 1%nat. lia.
  - exists (S k * m)%nat. cbn [fact]. rewrite Hm. ring.
Qed.

Lemma nv_d_int : forall a b n k, exists z, nv_d a b n k 0 = INR (fact n) * IZR z.
Proof.
  intros a b n k. unfold nv_d. rewrite zp_ev_dn_0.
  destruct (Nat.lt_ge_cases k n) as [Hk | Hk].
  - (* Below [n], the coefficient is one of the [n] leading zeros. *)
    exists 0%Z. unfold nv_poly.
    rewrite app_nth1 by (rewrite repeat_length; exact Hk).
    rewrite nth_repeat, Z.mul_0_r, Rmult_0_r. reflexivity.
  - destruct (nv_fact_mult n k Hk) as [m Hm].
    exists (Z.of_nat m * nth k (nv_poly a b n) 0)%Z.
    rewrite Hm, INR_IZR_INZ, <- mult_IZR, Nat2Z.inj_mul, Z.mul_assoc. reflexivity.
Qed.

Lemma nv_d_high : forall a b n x, nv_d a b n (2 * n + 2) x = 0.
Proof.
  intros a b n x. unfold nv_d. apply zp_ev_dn_high.
  unfold nv_poly. rewrite length_app, repeat_length, zp_length_qpow. lia.
Qed.
