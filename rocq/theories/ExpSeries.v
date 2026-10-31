(** * Rational bounds of [exp] from the alternating series of [exp (- x)]

    For [0 <= x <= 1], the terms [x ^ n / n!] of the series of [exp x]
    decrease to 0, so the partial sums of the alternating series
    [Σ (-1)^n x^n / n!] of [exp (- x)] bound it below and above (Stdlib's
    [alternated_series_ineq] in [AltSeries.v], [exp_alt_bounds]). Their
    copies in [Q] ([es_sumQ]) keep the common denominator [d^n * n!] of a
    rational [x = p / d], so that [vm_compute] adds them without the
    [gcd]s of [Qred], and their reciprocals bound [exp x]
    ([exp_Q_bounds]). *)

From Stdlib Require Import ZArith Reals Lra QArith Qreals.

Open Scope R_scope.

(** The terms [x ^ n / n!] of the series of [exp x]. *)
Definition exp_tg (x : R) (n : nat) : R := x ^ n / INR (fact n).

(** The alternating terms are those of the series of [exp (- x)]:
    [(-1)^n * x^n = (-1 * x)^n]. *)
Lemma exp_tg_alt : forall x n, tg_alt (exp_tg x) n = (- x) ^ n / INR (fact n).
Proof.
  intros x n; unfold tg_alt, exp_tg.
  replace (- x) with (-1 * x) by ring.
  rewrite Rpow_mult_distr; unfold Rdiv; ring.
Qed.

(** [exp_tg x (S n) = exp_tg x n * (x / (n + 1))], and [x / (n + 1) <= 1]. *)
Lemma exp_tg_decreasing : forall x, 0 <= x <= 1 -> Un_decreasing (exp_tg x).
Proof.
  intros x Hx n; unfold exp_tg.
  rewrite fact_simpl, mult_INR, <- tech_pow_Rmult.
  pose proof (INR_fact_lt_0 n) as Hf.
  assert (HS : 1 <= INR (S n)) by (rewrite S_INR; pose proof (pos_INR n); lra).
  assert (Hp : 0 <= x ^ n / INR (fact n)).
  { unfold Rdiv; apply Rmult_le_pos; [apply pow_le; lra |].
    left; apply Rinv_0_lt_compat; exact Hf. }
  replace (x * x ^ n / (INR (S n) * INR (fact n)))
    with (x ^ n / INR (fact n) * (x / INR (S n))) by (field; lra).
  rewrite <- (Rmult_1_r (x ^ n / INR (fact n))) at 2.
  apply Rmult_le_compat_l; [exact Hp |].
  unfold Rdiv; apply (Rmult_le_reg_r (INR (S n))); [lra |].
  rewrite Rmult_assoc, Rinv_l by lra; lra.
Qed.

(** For [0 <= x <= 1], the partial sums of [Σ (-1)^n x^n / n!] with an
    even number of terms bound [exp (- x)] below, and those with an odd
    number above: [sum_f_R0 f n] adds the [n + 1] terms from [f 0] to
    [f n]. *)
Lemma exp_alt_bounds :
  forall x N, 0 <= x <= 1 ->
  sum_f_R0 (tg_alt (exp_tg x)) (S (2 * N)) <= exp (- x) <=
  sum_f_R0 (tg_alt (exp_tg x)) (2 * N).
Proof.
  intros x N Hx; apply alternated_series_ineq.
  - exact (exp_tg_decreasing x Hx).
  - exact (cv_speed_pow_fact x).
  - (* [exp (- x)] is the limit [exist_exp] picks for the series
       [Σ / i! * (- x)^i]; [infinite_sum] and [Un_cv] of the partial sums
       unfold to the same statement. *)
    pose proof (proj2_sig (exist_exp (- x))) as H.
    change (proj1_sig (exist_exp (- x))) with (exp (- x)) in H.
    unfold exp_in, infinite_sum in H.
    intros eps Heps; destruct (H eps Heps) as [N0 HN]; exists N0.
    intros n Hn; rewrite (sum_eq _ (fun i => / INR (fact i) * (- x) ^ i)).
    + exact (HN n Hn).
    + intros i _; rewrite exp_tg_alt; unfold Rdiv; ring.
Qed.

(** ** The partial sums in [Q]

    For [x = p / d], [es_AP p d n] is [(A, (-p)^n, d^n * n!)], where the
    partial sum [Σ_{i <= n} (-x)^i / i!] is [A / (d^n * n!)]. Each step
    multiplies by [d] and the next [k + 1] in [positive] and [Z], so no
    unary number larger than [n] is computed. *)
Fixpoint es_AP (p : Z) (d : positive) (n : nat) : Z * Z * positive :=
  match n with
  | O => (1%Z, 1%Z, 1%positive)
  | S k =>
      let '(a, pk, den) := es_AP p d k in
      let pk1 := (- p * pk)%Z in
      let m := Pos.of_succ_nat k in
      ((a * Zpos d * Zpos m + pk1)%Z, pk1, (den * d * m)%positive)
  end.

(** [sum_f_R0 (tg_alt (exp_tg q)) n] in [Q]. *)
Definition es_sumQ (q : Q) (n : nat) : Q :=
  let '(a, _, den) := es_AP (Qnum q) (Qden q) n in (a # den)%Q.

(** [Pos.of_succ_nat k] is [k + 1]. *)
Lemma es_succ_R : forall k, IZR (Zpos (Pos.of_succ_nat k)) = INR (S k).
Proof.
  intros k; rewrite INR_IZR_INZ, Zpos_P_of_succ_nat, Nat2Z.inj_succ; reflexivity.
Qed.

(** The invariant of [es_AP]: the second component is [(-p)^n], the third
    [d^n * n!], and the first divided by the third, [a / (d^n * n!)], is
    the partial sum of [Σ (- p / d)^i / i!] up to [i = n]. *)
Lemma es_AP_inv :
  forall p d n a pk den, es_AP p d n = (a, pk, den) ->
  IZR pk = (- IZR p) ^ n /\
  IZR (Zpos den) = IZR (Zpos d) ^ n * INR (fact n) /\
  IZR a / IZR (Zpos den) =
  sum_f_R0 (fun i => (- (IZR p / IZR (Zpos d))) ^ i / INR (fact i)) n.
Proof.
  intros p d n; induction n as [|k IH]; intros a pk den Hn.
  - cbn [es_AP] in Hn; injection Hn as <- <- <-.
    cbn [pow sum_f_R0 fact INR]; split; [|split]; [reflexivity | ring | field].
  - cbn [es_AP] in Hn.
    destruct (es_AP p d k) as [[a0 pk0] den0] eqn:E.
    destruct (IH a0 pk0 den0 eq_refl) as [H1 [H2 H3]]; clear IH E.
    cbn beta iota zeta in Hn; injection Hn as <- <- <-.
    assert (HD : IZR (Zpos d) <> 0) by (apply eq_IZR_contrapositive; discriminate).
    assert (HDk : IZR (Zpos d) ^ k <> 0) by (apply pow_nonzero; exact HD).
    assert (HM : INR (S k) <> 0) by (apply not_0_INR; discriminate).
    pose proof (INR_fact_neq_0 k) as HF.
    assert (Hpk : IZR (- p * pk0) = (- IZR p) ^ S k).
    { rewrite mult_IZR, opp_IZR, H1; reflexivity. }
    assert (Hden : IZR (Zpos (den0 * d * Pos.of_succ_nat k)) =
                   IZR (Zpos d) ^ S k * INR (fact (S k))).
    { rewrite !Pos2Z.inj_mul, !mult_IZR, H2, es_succ_R, fact_simpl, mult_INR,
        <- tech_pow_Rmult.
      ring. }
    split; [exact Hpk | split; [exact Hden |]].
    rewrite Hden, plus_IZR, Hpk, !mult_IZR, es_succ_R, tech5, <- H3, H2.
    (* [(- (p / d))^(k+1) = (-p)^(k+1) / d^(k+1)], and [d^(k+1) = d * d^k]. *)
    replace (- (IZR p / IZR (Zpos d))) with (- IZR p * / IZR (Zpos d))
      by (unfold Rdiv; ring).
    rewrite Rpow_mult_distr, pow_inv, <- (tech_pow_Rmult (IZR (Zpos d)) k),
      fact_simpl, mult_INR.
    field; repeat split; assumption.
Qed.

Lemma es_sumQ_R :
  forall q n, Q2R (es_sumQ q n) = sum_f_R0 (tg_alt (exp_tg (Q2R q))) n.
Proof.
  intros q n; unfold es_sumQ.
  destruct (es_AP (Qnum q) (Qden q) n) as [[a pk] den] eqn:E.
  destruct (es_AP_inv _ _ _ _ _ _ E) as [_ [_ H3]]; clear E.
  cbn beta iota zeta.
  (* [Q2R (a # den) = a / den] and [Q2R q = Qnum q / Qden q] by definition. *)
  change (Q2R (a # den)) with (IZR a / IZR (Zpos den)); rewrite H3.
  change (IZR (Qnum q) / IZR (Zpos (Qden q))) with (Q2R q).
  apply sum_eq; intros i _; rewrite exp_tg_alt; reflexivity.
Qed.

(** ** Bounds of [exp q] for a rational [0 <= q <= 1] *)

(** [exp q = / exp (- q)], so the reciprocals of the bounds of
    [exp (- q)] bound [exp q]. *)
Definition exp_loQ (q : Q) (N : nat) : Q := Qinv (es_sumQ q (2 * N)).
Definition exp_hiQ (q : Q) (N : nat) : Q := Qinv (es_sumQ q (S (2 * N))).

Lemma exp_Q_bounds :
  forall q N, (0 <= q)%Q -> (q <= 1)%Q -> (0 < es_sumQ q (S (2 * N)))%Q ->
  Q2R (exp_loQ q N) <= exp (Q2R q) <= Q2R (exp_hiQ q N).
Proof.
  intros q N H0 H1 Hpos.
  apply Qle_Rle in H0, H1; apply Qlt_Rlt in Hpos.
  replace (Q2R 0) with 0 in H0, Hpos by (unfold Q2R; simpl; lra).
  replace (Q2R 1) with 1 in H1 by (unfold Q2R; simpl; lra).
  destruct (exp_alt_bounds (Q2R q) N (conj H0 H1)) as [Hlo Hhi].
  rewrite <- !es_sumQ_R in Hlo, Hhi.
  pose proof (exp_pos (- Q2R q)) as He.
  (* A rational with a positive image is not [0]. *)
  assert (Hnz : forall s, 0 < Q2R s -> ~ (s == 0)%Q).
  { intros s Hs Hs0; apply Qeq_eqR in Hs0; rewrite Hs0 in Hs.
    unfold Q2R in Hs; simpl in Hs; lra. }
  unfold exp_loQ, exp_hiQ.
  rewrite !Q2R_inv by (apply Hnz; lra).
  (* [exp q = / exp (- q)], and [/] reverses the bounds of [exp (- q)]. *)
  rewrite <- (Rinv_inv (exp (Q2R q))), <- exp_Ropp.
  split; apply Rinv_le_contravar; lra.
Qed.
