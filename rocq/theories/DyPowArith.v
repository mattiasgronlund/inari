(** * The arithmetic of the exact powers

    The facts about integers and reals that [DyPowExact.v] and [DyPown.v]
    use to show which [x^y] of [f64]s are [f64]s, with no function of
    [Model.v]: the odd part and the power of 2 of a dyadic are unique
    ([odd_pow2_inj]), an odd power of a positive integer that is a
    [2^k]-th power is the [2^k]-th power of an integer ([odd_pow_root]),
    and [x^(p/2^k)] of a dyadic [x] with an odd part [mx] is a dyadic only
    where [mx^p] is a [2^k]-th power ([pow_dyadic_eq], [pow_dyadic_neg]
    and [pow_dyadic_sound]), and then [x] is the [2^k]-th power of a
    dyadic whose [p]-th power is [x^(p/2^k)] ([pow_dyadic_root] and
    [pow_dyadic_complete]). *)

From Stdlib Require Import ZArith Znumtheory Reals Lia Lra.
From Flocq Require Import Core.Core.

Open Scope Z_scope.

(** An odd [m] times [2^e] determines [m] and [e]. *)
Lemma odd_pow2_inj :
  forall m1 e1 m2 e2,
  Z.odd m1 = true -> Z.odd m2 = true ->
  (IZR m1 * bpow radix2 e1 = IZR m2 * bpow radix2 e2)%R ->
  m1 = m2 /\ e1 = e2.
Proof.
  (* With [f1 <= f2], [a1 = a2 2^(f2 - f1)], which is even unless
     [f1 = f2]. *)
  assert (K : forall a1 f1 a2 f2,
    Z.odd a1 = true -> f1 <= f2 ->
    (IZR a1 * bpow radix2 f1 = IZR a2 * bpow radix2 f2)%R ->
    a1 = a2 /\ f1 = f2).
  { intros a1 f1 a2 f2 A1 Hf E.
    assert (HP : IZR (2 ^ (f2 - f1)) = bpow radix2 (f2 - f1))
      by (apply (IZR_Zpower radix2); lia).
    assert (E' : a1 = a2 * 2 ^ (f2 - f1)).
    { apply eq_IZR. rewrite mult_IZR, HP.
      apply Rmult_eq_reg_r with (bpow radix2 f1).
      2: apply Rgt_not_eq, bpow_gt_0.
      rewrite E, Rmult_assoc, <- bpow_plus.
      replace (f2 - f1 + f1) with f2 by ring. reflexivity. }
    destruct (Z.eq_dec f1 f2) as [<- | Hne].
    - split; [| reflexivity].
      rewrite Z.sub_diag, Z.pow_0_r, Z.mul_1_r in E'. exact E'.
    - exfalso.
      rewrite E', Z.odd_mul, Z.odd_pow in A1 by lia.
      destruct (Z.odd a2); discriminate A1. }
  intros m1 e1 m2 e2 H1 H2 H.
  destruct (Z.le_ge_cases e1 e2) as [He | He].
  - now apply K.
  - destruct (K m2 e2 m1 e1 H2 ltac:(lia) (eq_sym H)) as [-> ->].
    split; reflexivity.
Qed.

(** [n q^2 = r^2] of positive [q] and [r] makes [n] a square: with
    [g = gcd(q, r)], [q = q' g] and [r = r' g] of coprime [q'] and [r'],
    [n q'^2 = r'^2], so [q'] divides [r' r'] and then [r'] (Gauss's
    lemma), so [q' = 1] and [n = r'^2]. *)
Lemma square_of_mul_square :
  forall n q r,
  0 < q -> 0 < r -> n * q ^ 2 = r ^ 2 ->
  exists s, 0 < s /\ n = s ^ 2.
Proof.
  intros n q r Hq Hr E.
  remember (Z.gcd q r) as g eqn:Hg.
  assert (Hg0 : 0 < g).
  { assert (0 <= g) by (rewrite Hg; apply Z.gcd_nonneg).
    assert (g <> 0) by (intro H0; rewrite Hg in H0; apply Z.gcd_eq_0 in H0; lia).
    lia. }
  destruct (Z.gcd_divide_l q r) as [q' Hq'].
  destruct (Z.gcd_divide_r q r) as [r' Hr'].
  rewrite <- Hg in Hq', Hr'.
  assert (Hc : Z.gcd q' r' = 1).
  { assert (Hm : g = Z.gcd q' r' * g).
    { rewrite Hg at 1. rewrite Hq', Hr', Z.gcd_mul_mono_r, Z.abs_eq by lia.
      reflexivity. }
    apply (Z.mul_reg_r _ _ g); lia. }
  assert (Hq0 : 0 < q') by nia.
  assert (Hr0 : 0 < r') by nia.
  assert (E3 : n * q' ^ 2 = r' ^ 2).
  { apply (Z.mul_reg_r _ _ (g ^ 2)); [nia |].
    transitivity (n * (q' * g) ^ 2); [ring |].
    rewrite <- Hq', E, Hr'. ring. }
  assert (Hd : (q' | r' * r')).
  { exists (n * q'). transitivity (r' ^ 2); [ring |]. rewrite <- E3. ring. }
  apply Z.gauss in Hd; [| exact Hc].
  apply Z.divide_gcd_iff in Hd; [| lia].
  rewrite Hc in Hd. subst q'.
  exists r'. split; [exact Hr0 |]. rewrite <- E3. ring.
Qed.

(** [a^p = b^2] with an odd [p] makes [a] a square. *)
Lemma odd_pow_square :
  forall a b p,
  0 < a -> 0 < b -> Z.odd p = true -> 0 < p ->
  a ^ p = b ^ 2 ->
  exists s, 0 < s /\ a = s ^ 2.
Proof.
  intros a b p Ha Hb Hp Hp0 E.
  (* [a^(2j+1) = a (a^j)^2]. *)
  apply Z.odd_spec in Hp. destruct Hp as [j ->].
  apply (square_of_mul_square a (a ^ j) b).
  - apply Z.pow_pos_nonneg; lia.
  - exact Hb.
  - rewrite <- E, <- Z.pow_mul_r, Z.pow_add_r, Z.pow_1_r by lia.
    rewrite (Z.mul_comm j 2). ring.
Qed.

(** [a^p = b^(2^k)] with an odd [p] makes [a] a [2^k]-th power. *)
Lemma odd_pow_root :
  forall a b p k,
  0 < a -> 0 < b -> Z.odd p = true -> 0 < p -> 0 <= k ->
  a ^ p = b ^ (2 ^ k) ->
  exists r, 0 < r /\ a = r ^ (2 ^ k).
Proof.
  intros a b p k Ha Hb Hp Hp0 Hk. revert a b Ha Hb.
  pattern k. apply natlike_ind; [| | exact Hk]; clear k Hk.
  - intros a b Ha Hb E. exists a. split; [exact Ha |].
    now rewrite Z.pow_0_r, Z.pow_1_r.
  - (* [a^p = (b^(2^k))^2] makes [a = s^2], then [s^p = b^(2^k)] by
       injectivity of squaring, and [s = r^(2^k)] by induction. *)
    intros k Hk IH a b Ha Hb E.
    assert (H2k : 0 <= 2 ^ k) by (apply Z.pow_nonneg; lia).
    assert (E' : a ^ p = (b ^ (2 ^ k)) ^ 2).
    { rewrite E, <- Z.pow_mul_r by lia. f_equal.
      rewrite Z.pow_succ_r by lia. ring. }
    destruct (odd_pow_square a (b ^ (2 ^ k)) p Ha) as [s [Hs Has]];
      [apply Z.pow_pos_nonneg; lia | exact Hp | exact Hp0 | exact E' |].
    assert (Esp : s ^ p = b ^ (2 ^ k)).
    { apply (Z.pow_inj_l _ _ 2); [apply Z.pow_nonneg; lia | lia | lia |].
      rewrite <- E', Has, <- !Z.pow_mul_r by lia. f_equal. ring. }
    destruct (IH s b Hs Hb Esp) as [r [Hr Hsr]].
    exists r. split; [exact Hr |].
    rewrite Has, Hsr, <- Z.pow_mul_r by lia. f_equal.
    rewrite Z.pow_succ_r by lia. ring.
Qed.

(** [Rpower] of a positive integer at a non-negative integer. *)
Lemma Rpower_IZR_pow :
  forall m n, 0 < m -> 0 <= n -> Rpower (IZR m) (IZR n) = IZR (m ^ n).
Proof.
  intros m n Hm Hn.
  replace (IZR n) with (INR (Z.to_nat n))
    by (rewrite INR_IZR_INZ, Z2Nat.id by lia; reflexivity).
  rewrite Rpower_pow by (apply IZR_lt; lia).
  rewrite pow_IZR, Z2Nat.id by lia. reflexivity.
Qed.

(** [Rpower] of a power of 2 at an integer. *)
Lemma Rpower_bpow_IZR :
  forall e n, Rpower (bpow radix2 e) (IZR n) = bpow radix2 (e * n).
Proof.
  intros e n. unfold Rpower. rewrite !bpow_exp, ln_exp, mult_IZR.
  f_equal. ring.
Qed.

(** [(m 2^e)^n = m^n 2^(e n)] of a positive [m] and an [n >= 0]. *)
Lemma Rpower_dyadic_IZR :
  forall m e n, 0 < m -> 0 <= n ->
  Rpower (IZR m * bpow radix2 e) (IZR n) = (IZR (m ^ n) * bpow radix2 (e * n))%R.
Proof.
  intros m e n Hm Hn.
  rewrite <- Rpower_mult_distr
    by first [apply IZR_lt; exact Hm | apply bpow_gt_0].
  rewrite Rpower_IZR_pow by lia. now rewrite Rpower_bpow_IZR.
Qed.

(** Where [(mx 2^ex)^(p/2^k)] is the dyadic [mv 2^ev], of odd [mx] and
    [mv], [mx^p = mv^(2^k)] and [ex p = ev 2^k]. *)
Lemma pow_dyadic_eq :
  forall mx ex mv ev p k,
  Z.odd mx = true -> 0 < mx -> Z.odd mv = true -> 0 < mv -> 0 < p -> 0 <= k ->
  Rpower (IZR mx * bpow radix2 ex) (IZR p / IZR (2 ^ k)) = (IZR mv * bpow radix2 ev)%R ->
  mx ^ p = mv ^ (2 ^ k) /\ ex * p = ev * 2 ^ k.
Proof.
  intros mx ex mv ev p k Hmx Hmx0 Hmv Hmv0 Hp Hk E.
  assert (H2k : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  (* Raise both sides to [2^k]: [(x^(p/2^k))^(2^k) = x^p]. *)
  assert (E2 : Rpower (IZR mx * bpow radix2 ex) (IZR p) =
               Rpower (IZR mv * bpow radix2 ev) (IZR (2 ^ k))).
  { rewrite <- E, Rpower_mult. f_equal. field. apply not_0_IZR. lia. }
  rewrite (Rpower_dyadic_IZR mx ex p), (Rpower_dyadic_IZR mv ev (2 ^ k)) in E2
    by lia.
  apply odd_pow2_inj in E2; [exact E2 | |].
  - rewrite Z.odd_pow by lia. exact Hmx.
  - rewrite Z.odd_pow by lia. exact Hmv.
Qed.

(** Where [(mx 2^ex)^(-p/2^k)] is the dyadic [mv 2^ev], of odd [mx] and
    [mv], [mx = 1]. *)
Lemma pow_dyadic_neg :
  forall mx ex mv ev p k,
  Z.odd mx = true -> 0 < mx -> Z.odd mv = true -> 0 < mv -> 0 < p -> 0 <= k ->
  Rpower (IZR mx * bpow radix2 ex) (- (IZR p / IZR (2 ^ k))) = (IZR mv * bpow radix2 ev)%R ->
  mx = 1.
Proof.
  intros mx ex mv ev p k Hmx Hmx0 Hmv Hmv0 Hp Hk E.
  assert (H2k : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (HV : (0 < IZR mv * bpow radix2 ev)%R)
    by (apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0]).
  set (q := (IZR p / IZR (2 ^ k))%R) in E.
  rewrite Rpower_Ropp in E.
  assert (HR : (0 < Rpower (IZR mx * bpow radix2 ex) q)%R)
    by (unfold Rpower; apply exp_pos).
  (* [x^q mv 2^ev = 1], raised to [2^k]:
     [mx^p mv^(2^k) 2^(ex p + ev 2^k) = 1]. *)
  assert (E1 : (Rpower (IZR mx * bpow radix2 ex) q * (IZR mv * bpow radix2 ev) = 1)%R).
  { rewrite <- E. field. now apply Rgt_not_eq. }
  assert (E2 : (Rpower (IZR mx * bpow radix2 ex) (IZR p) *
                Rpower (IZR mv * bpow radix2 ev) (IZR (2 ^ k)) = 1)%R).
  { replace (IZR p) with (q * IZR (2 ^ k))%R
      by (unfold q; field; apply not_0_IZR; lia).
    rewrite <- Rpower_mult, Rpower_mult_distr by assumption.
    rewrite E1. unfold Rpower. rewrite ln_1, Rmult_0_r. apply exp_0. }
  rewrite (Rpower_dyadic_IZR mx ex p), (Rpower_dyadic_IZR mv ev (2 ^ k)) in E2
    by lia.
  assert (E3 : (IZR (mx ^ p * mv ^ (2 ^ k)) * bpow radix2 (ex * p + ev * 2 ^ k) =
                IZR 1 * bpow radix2 0)%R).
  { rewrite mult_IZR, bpow_plus. change (bpow radix2 0) with 1%R.
    rewrite Rmult_1_r, <- E2. ring. }
  assert (Ho : Z.odd (mx ^ p * mv ^ (2 ^ k)) = true)
    by (rewrite Z.odd_mul, !Z.odd_pow, Hmx, Hmv by lia; reflexivity).
  destruct (odd_pow2_inj _ _ _ _ Ho (eq_refl : Z.odd 1 = true) E3) as [E4 _].
  (* [mx^p mv^(2^k) = 1] of positive factors makes [mx^p = 1], so [mx = 1]. *)
  apply Z.mul_eq_1 in E4.
  destruct E4 as [E4 | E4]; [| pose proof (Z.pow_pos_nonneg mx p); lia].
  replace p with (Z.succ (p - 1)) in E4 by lia.
  rewrite Z.pow_succ_r in E4 by lia.
  apply Z.mul_eq_1 in E4. lia.
Qed.

(** [((mr 2^er)^(2^k))^(p/2^k) = mr^p 2^(er p)]. *)
Lemma pow_dyadic_sound :
  forall mr er p k,
  0 < mr -> 0 < p -> 0 <= k ->
  Rpower (IZR (mr ^ (2 ^ k)) * bpow radix2 (er * 2 ^ k)) (IZR p / IZR (2 ^ k)) =
  (IZR (mr ^ p) * bpow radix2 (er * p))%R.
Proof.
  intros mr er p k Hmr Hp Hk.
  assert (H2k : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  rewrite <- (Rpower_dyadic_IZR mr er (2 ^ k)), <- (Rpower_dyadic_IZR mr er p),
    Rpower_mult by lia.
  f_equal. field. apply not_0_IZR. lia.
Qed.

(** [mx^p = mv^(2^k)] and [ex p = ev 2^k], with [p] odd unless [k = 0],
    make [mx 2^ex] the [2^k]-th power of a dyadic [r 2^er] whose [p]-th
    power is [mv 2^ev]. *)
Lemma pow_dyadic_root :
  forall mx ex mv ev p k,
  0 < mx -> 0 < mv -> 0 < p -> 0 <= k -> (k = 0 \/ Z.odd p = true) ->
  mx ^ p = mv ^ (2 ^ k) -> ex * p = ev * 2 ^ k ->
  exists r er, 0 < r /\ mx = r ^ (2 ^ k) /\ ex = er * 2 ^ k /\ mv = r ^ p /\ ev = er * p.
Proof.
  intros mx ex mv ev p k Hmx Hmv Hp Hk Hpk E Ee.
  assert (H2k : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  destruct Hpk as [-> | Hpo].
  - (* [k = 0]: [r = mx] and [er = ex]. *)
    rewrite Z.pow_0_r, Z.pow_1_r in E. rewrite Z.pow_0_r, Z.mul_1_r in Ee.
    exists mx, ex. rewrite Z.pow_0_r, Z.pow_1_r, Z.mul_1_r.
    repeat split; auto.
  - (* [mx = r^(2^k)], and then [mv^(2^k) = (r^p)^(2^k)]. *)
    destruct (odd_pow_root mx mv p k Hmx Hmv Hpo Hp Hk E) as [r [Hr Hmr]].
    assert (Hv : mv = r ^ p).
    { apply (Z.pow_inj_l _ _ (2 ^ k));
        [lia | apply Z.pow_nonneg; lia | exact H2k |].
      rewrite <- E, Hmr, <- !Z.pow_mul_r by lia. f_equal. ring. }
    (* [2^k] divides [p ex] and is coprime to the odd [p], so it divides
       [ex] (Gauss's lemma). *)
    assert (Hd : (2 ^ k | ex)).
    { apply (Gauss _ p).
      - exists ev. rewrite <- Ee. ring.
      - apply rel_prime_sym, Zpow_facts.rel_prime_Zpower_r; [exact Hk |].
        apply rel_prime_sym, prime_rel_prime; [exact prime_2 |].
        intros [c Hc]. rewrite Hc, Z.odd_mul in Hpo.
        destruct (Z.odd c); discriminate Hpo. }
    destruct Hd as [er Her].
    exists r, er. repeat split; [exact Hr | exact Hmr | exact Her | exact Hv |].
    apply (Z.mul_reg_r _ _ (2 ^ k)); [lia |].
    rewrite <- Ee, Her. ring.
Qed.

(** Where [(mx 2^ex)^(± p/2^k)] is the dyadic [mv 2^ev], of odd [mx] and
    [mv], with [p] odd unless [k = 0], [mx 2^ex] is the [2^k]-th power of
    a dyadic [r 2^er], and [mv 2^ev] is [(r 2^er)^(± p)], with [r = 1] for
    the negative exponent. *)
Lemma pow_dyadic_complete :
  forall (neg : bool) mx ex mv ev p k,
  Z.odd mx = true -> 0 < mx -> Z.odd mv = true -> 0 < mv -> 0 < p -> 0 <= k ->
  (k = 0 \/ Z.odd p = true) ->
  Rpower (IZR mx * bpow radix2 ex)
    (if neg then - (IZR p / IZR (2 ^ k)) else IZR p / IZR (2 ^ k))%R =
  (IZR mv * bpow radix2 ev)%R ->
  exists r er, 0 < r /\ mx = r ^ (2 ^ k) /\ ex = er * 2 ^ k /\ mv = r ^ p /\
  (if neg then r = 1 /\ ev = - (er * p) else ev = er * p).
Proof.
  intros neg mx ex mv ev p k Hmx Hmx0 Hmv Hmv0 Hp Hk Hpk E.
  destruct neg.
  - pose proof (pow_dyadic_neg mx ex mv ev p k Hmx Hmx0 Hmv Hmv0 Hp Hk E) as H1.
    subst mx.
    (* [(2^ex)^(-q) = (2^(-ex))^q]. *)
    assert (E' : Rpower (IZR 1 * bpow radix2 (- ex)) (IZR p / IZR (2 ^ k)) =
                 (IZR mv * bpow radix2 ev)%R).
    { rewrite <- E. unfold Rpower. rewrite !Rmult_1_l, bpow_opp, ln_Rinv
        by apply bpow_gt_0.
      f_equal. ring. }
    destruct (pow_dyadic_eq 1 (- ex) mv ev p k eq_refl ltac:(lia) Hmv Hmv0 Hp Hk E')
      as [Ep Ee].
    destruct (pow_dyadic_root 1 (- ex) mv ev p k ltac:(lia) Hmv0 Hp Hk Hpk Ep Ee)
      as [r [er [Hr [Hr1 [Her [Hv Hev]]]]]].
    (* [1 = r^(2^k)] makes [r = 1]. *)
    assert (Hr1' : r = 1).
    { destruct (Z.eq_dec r 1) as [-> | Hne]; [reflexivity |].
      assert (H2k : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
      apply (Z.pow_gt_1 r (2 ^ k)) in H2k; lia. }
    subst r.
    exists 1, (- er).
    split; [lia |]. split; [exact Hr1 |].
    split; [rewrite Z.mul_opp_l; lia |]. split; [exact Hv |].
    split; [reflexivity | rewrite Z.mul_opp_l; lia].
  - destruct (pow_dyadic_eq mx ex mv ev p k Hmx Hmx0 Hmv Hmv0 Hp Hk E) as [Ep Ee].
    exact (pow_dyadic_root mx ex mv ev p k Hmx0 Hmv0 Hp Hk Hpk Ep Ee).
Qed.
