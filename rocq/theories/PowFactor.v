(** * Rational powers of 2 and of 10

    [2^r] and [10^r], for a rational [r = p / q], are rational only where
    [r] is an integer ([pow2_rational] and [pow10_rational]): if
    [(2^(p/q))^q = 2^p] is [(a / b)^q], the factorization of [a^q] and
    [b^q] into primes, in which the exponent of 2 is a multiple of [q],
    makes [q] divide [p], and likewise for 10. Only the exponent of 2 is
    compared, for both: [2] and [10] are [2 o] with [o] odd, so that the
    exponent of 2 in [a^q = (2 o)^p b^q] is [q i = p + q j], where [2^i]
    and [2^j] are the powers of 2 in [a] and [b] ([pf_int]). *)

From Stdlib Require Import ZArith Reals Lra Lia Znumtheory.

Open Scope R_scope.

(** ** The exponent of 2 in an integer

    Every [a > 0] is [2^i m] with [m] odd, and [i] is unique. Only the
    exponent of 2 is needed: [2] and [10] are both [2 o] with [o] odd. *)

Lemma pf_odd_part :
  forall a : Z, (0 < a)%Z ->
  exists i m : Z, (0 <= i)%Z /\ Z.odd m = true /\ a = (2 ^ i * m)%Z.
Proof.
intros a Ha. destruct a as [| p | p]; try lia. clear Ha.
induction p as [p _ | p IH |].
- exists 0%Z, (Z.pos p~1). split; [lia | split; reflexivity].
- destruct IH as (i & m & Hi & Hm & E). exists (i + 1)%Z, m.
  split; [lia | split; [exact Hm |]].
  rewrite Z.pow_add_r, Z.pow_1_r by lia.
  change (Z.pos p~0) with (2 * Z.pos p)%Z. rewrite E. ring.
- exists 0%Z, 1%Z. split; [lia | split; reflexivity].
Qed.

Lemma pf_odd_unique_le :
  forall i j m n : Z, (0 <= i <= j)%Z -> Z.odd m = true -> Z.odd n = true ->
  (2 ^ i * m = 2 ^ j * n)%Z -> i = j.
Proof.
intros i j m n Hij Hm Hn E.
destruct (Z.eq_dec i j) as [| Ne]; [assumption | exfalso].
replace j with (i + (j - i))%Z in E by ring.
rewrite Z.pow_add_r in E by lia.
assert (E' : m = (2 ^ (j - i) * n)%Z).
{ apply (Z.mul_reg_l _ _ (2 ^ i)); [apply Z.pow_nonzero; lia |].
  rewrite E. ring. }
(* [j > i], so [m] would be even. *)
replace (j - i)%Z with (Z.succ (j - i - 1)) in E' by ring.
rewrite Z.pow_succ_r in E' by lia.
rewrite E', <- Z.mul_assoc, Z.odd_mul, Z.odd_2 in Hm. discriminate Hm.
Qed.

Lemma pf_odd_unique :
  forall i j m n : Z, (0 <= i)%Z -> (0 <= j)%Z -> Z.odd m = true -> Z.odd n = true ->
  (2 ^ i * m = 2 ^ j * n)%Z -> i = j.
Proof.
intros i j m n Hi Hj Hm Hn E.
destruct (Z.le_ge_cases i j).
- apply (pf_odd_unique_le i j m n); [lia | exact Hm | exact Hn | exact E].
- symmetry. apply (pf_odd_unique_le j i n m); [lia | exact Hn | exact Hm | auto].
Qed.

Lemma pf_odd_pow :
  forall m k : Z, Z.odd m = true -> (0 <= k)%Z -> Z.odd (m ^ k) = true.
Proof.
intros m k Hm Hk. destruct (Z.eq_dec k 0) as [-> | Nk]; [reflexivity |].
rewrite Z.odd_pow by lia. exact Hm.
Qed.

(** [a^q = (2 o)^p b^q] with [o] odd makes [q] divide [p]: the exponents
    of 2 are [q i] and [p + q j]. *)
Lemma pf_int :
  forall o c p q a b : Z, c = (2 * o)%Z -> Z.odd o = true ->
  (0 < q)%Z -> (0 < a)%Z -> (0 < b)%Z -> (0 <= p)%Z ->
  (a ^ q = c ^ p * b ^ q)%Z -> (q | p)%Z.
Proof.
intros o c p q a b -> Ho Hq Ha Hb Hp E.
destruct (pf_odd_part a Ha) as (i & m & Hi & Hm & ->).
destruct (pf_odd_part b Hb) as (j & n & Hj & Hn & ->).
rewrite !Z.pow_mul_l, <- !Z.pow_mul_r in E by lia.
assert (E' : (2 ^ (i * q) * m ^ q = 2 ^ (p + j * q) * (o ^ p * n ^ q))%Z).
{ rewrite E, Z.pow_add_r by nia. ring. }
apply pf_odd_unique in E'; [| nia | nia | apply pf_odd_pow; [exact Hm | lia] |].
- exists (i - j)%Z. nia.
- rewrite Z.odd_mul, (pf_odd_pow o p Ho), (pf_odd_pow n q Hn) by lia. reflexivity.
Qed.

(** [c^(p/q) = a / b] gives [a > 0] and the integer identity
    [a^q = c^p b^q], or [b^q = c^(-p) a^q] for [p < 0], by raising both
    sides to the [q]-th power. *)
Lemma pf_real :
  forall c p q a b : Z, (0 < c)%Z -> (0 < q)%Z -> (0 < b)%Z ->
  Rpower (IZR c) (IZR p / IZR q) = IZR a / IZR b ->
  (0 < a)%Z /\ ((0 <= p)%Z -> (a ^ q = c ^ p * b ^ q)%Z) /\
  ((p < 0)%Z -> (b ^ q = c ^ (- p) * a ^ q)%Z).
Proof.
intros c p q a b Hc Hq Hb H.
assert (Rc : 0 < IZR c) by (apply IZR_lt; exact Hc).
assert (Rq : 0 < IZR q) by (apply IZR_lt; exact Hq).
assert (Rb : 0 < IZR b) by (apply IZR_lt; exact Hb).
assert (Hab : 0 < IZR a / IZR b) by (rewrite <- H; unfold Rpower; apply exp_pos).
assert (Ra : 0 < IZR a).
{ replace (IZR a) with (IZR a / IZR b * IZR b) by (field; lra).
  apply Rmult_lt_0_compat; assumption. }
set (N := Z.to_nat q).
assert (HN : INR N = IZR q) by (unfold N; rewrite INR_IZR_INZ, Z2Nat.id by lia; reflexivity).
assert (HZ : Z.of_nat N = q) by (unfold N; apply Z2Nat.id; lia).
(* [(a / b)^N = c^(p/q * q) = c^p] *)
assert (P : (IZR a / IZR b) ^ N = Rpower (IZR c) (IZR p)).
{ rewrite <- (Rpower_pow N _ Hab), <- H, Rpower_mult, HN.
  f_equal. field. lra. }
assert (P' : IZR a ^ N = Rpower (IZR c) (IZR p) * IZR b ^ N).
{ rewrite <- P, <- Rpow_mult_distr. f_equal. field. lra. }
rewrite !pow_IZR, HZ in P'.
split; [apply lt_IZR; exact Ra | split].
- intros Hp.
  replace (IZR p) with (INR (Z.to_nat p)) in P'
    by (rewrite INR_IZR_INZ, Z2Nat.id by lia; reflexivity).
  rewrite (Rpower_pow _ _ Rc), pow_IZR, Z2Nat.id, <- mult_IZR in P' by lia.
  apply eq_IZR. exact P'.
- intros Hp.
  replace (IZR p) with (- INR (Z.to_nat (- p))) in P'
    by (rewrite INR_IZR_INZ, Z2Nat.id, opp_IZR by lia; ring).
  rewrite Rpower_Ropp, (Rpower_pow _ _ Rc), pow_IZR, Z2Nat.id in P' by lia.
  assert (Pc : 0 < IZR (c ^ (- p))) by (apply IZR_lt, Z.pow_pos_nonneg; lia).
  apply eq_IZR. rewrite mult_IZR, P'. field. lra.
Qed.

(** [(2 o)^(p/q)], with [o] odd, is rational only where [q] divides [p]. *)
Lemma pf_rational :
  forall o p q a b : Z, Z.odd o = true -> (0 < o)%Z -> (0 < q)%Z -> (0 < b)%Z ->
  Rpower (IZR (2 * o)) (IZR p / IZR q) = IZR a / IZR b -> (q | p)%Z.
Proof.
intros o p q a b Ho Hop Hq Hb H.
destruct (pf_real (2 * o) p q a b ltac:(lia) Hq Hb H) as (Ha & Hpos & Hneg).
destruct (Z.le_gt_cases 0 p) as [Hp | Hp].
- exact (pf_int o (2 * o) p q a b eq_refl Ho Hq Ha Hb Hp (Hpos Hp)).
- apply Z.divide_opp_r.
  exact (pf_int o (2 * o) (- p) q b a eq_refl Ho Hq Hb Ha ltac:(lia) (Hneg Hp)).
Qed.

Theorem pow2_rational :
  forall p q a b : Z, (0 < q)%Z -> (0 < b)%Z ->
  Rpower 2 (IZR p / IZR q) = IZR a / IZR b -> (q | p)%Z.
Proof.
intros p q a b Hq Hb H.
exact (pf_rational 1 p q a b eq_refl ltac:(lia) Hq Hb H).
Qed.

Theorem pow10_rational :
  forall p q a b : Z, (0 < q)%Z -> (0 < b)%Z ->
  Rpower 10 (IZR p / IZR q) = IZR a / IZR b -> (q | p)%Z.
Proof.
intros p q a b Hq Hb H.
exact (pf_rational 5 p q a b eq_refl ltac:(lia) Hq Hb H).
Qed.
