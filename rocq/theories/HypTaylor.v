(** * The Taylor polynomials of [sinh] and [cosh]

    On [[0, 1]], the Taylor polynomial of [sinh] of degree 15 is below
    [sinh] by at most [3/2] times the next term, [y^17 / 17!]
    ([sinh_taylor]), and that of [cosh] of degree 12 below [cosh] by at
    most [3/2] times [y^14 / 14!] ([cosh_taylor]). The polynomials of
    [FastHypPoly.v] and [FastCoshPoly.v] approximate these two. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Inari Require Import ExpSeries.

Open Scope R_scope.

(** [n!] in [Z], so that the factorials of literals compute in binary,
    not in the unary [nat] of [fact]. *)
Local Fixpoint zfact (n : nat) : Z :=
  match n with O => 1%Z | S m => (Z.of_nat n * zfact m)%Z end.

Local Lemma fact_R : forall n, INR (fact n) = IZR (zfact n).
Proof.
induction n as [|n IH]; [reflexivity|].
rewrite fact_simpl, mult_INR, IH. cbn [zfact]. rewrite mult_IZR, <- INR_IZR_INZ. reflexivity.
Qed.

(** Replaces every [zfact n] of a literal [n] in the goal by its value. *)
Local Ltac zfact_lit :=
  repeat match goal with |- context [zfact ?n] =>
    let v := eval vm_compute in (zfact n) in change (zfact n) with v end.

(** [exp y] is at most its Taylor polynomial of degree [n] plus twice the
    next term on [[0, 1]], as each later term is at most half the one
    before it. *)
Local Lemma exp_le_taylor :
  forall n y, 0 <= y <= 1 ->
  exp y <= sum_f_R0 (fun i => / INR (fact i) * y ^ i) n + 2 * (/ INR (fact (S n)) * y ^ S n).
Proof.
intros n y Hy.
set (s := fun i => / INR (fact i) * y ^ i).
assert (Hs0 : forall i, 0 <= s i).
{ intros i. unfold s. cbv beta.
  apply Rmult_le_pos; [left; apply Rinv_0_lt_compat, INR_fact_lt_0 | apply pow_le; lra]. }
assert (Hs : forall i, (1 <= i)%nat -> s (S i) <= s i / 2).
{ intros i Hi.
  assert (Hc : 0 <= s i) by exact (Hs0 i).
  unfold s in Hc |- *. cbv beta in Hc |- *.
  rewrite fact_simpl, mult_INR, Rinv_mult. cbn [pow].
  assert (Hk : 2 <= INR (S i)) by (rewrite S_INR; apply le_INR in Hi; rewrite INR_1 in Hi; lra).
  assert (Hk' : 0 < / INR (S i) <= / 2)
    by (split; [apply Rinv_0_lt_compat; lra | apply Rinv_le_contravar; lra]).
  assert (Hy' : y * / INR (S i) <= / 2) by nra.
  replace (/ INR (S i) * / INR (fact i) * (y * y ^ i))
    with (y * / INR (S i) * (/ INR (fact i) * y ^ i)) by ring.
  nra. }
(* The partial sums from degree [n + 1] on, plus their next term, are at
   most the bound. *)
assert (Hk : forall k, sum_f_R0 s (S n + k)%nat + s (S n + k)%nat <= sum_f_R0 s n + 2 * s (S n)).
{ induction k as [|k IH].
  - rewrite Nat.add_0_r, tech5. lra.
  - rewrite Nat.add_succ_r, tech5. assert (H1 : (1 <= S n + k)%nat) by lia.
    pose proof (Hs _ H1). lra. }
(* So is their limit [exp y]. *)
pose proof (proj2_sig (exist_exp y)) as Hin. change (exp_in y (exp y)) in Hin.
fold s.
destruct (Rle_or_lt (exp y) (sum_f_R0 s n + 2 * s (S n))) as [H|H]; [exact H | exfalso].
destruct (Hin (exp y - (sum_f_R0 s n + 2 * s (S n)))) as [N HN]; [lra|].
assert (HNn : (S n + N >= N)%nat) by lia.
assert (Hd : R_dist (sum_f_R0 s (S n + N)%nat) (exp y) < exp y - (sum_f_R0 s n + 2 * s (S n)))
  by exact (HN _ HNn).
unfold R_dist in Hd. apply Rabs_def2 in Hd.
pose proof (Hk N). pose proof (Hs0 (S n + N)%nat). lra.
Qed.

(** [y + y^3/3! + ... + y^15/15!]. *)
Definition sinh_taylor15 (y : R) : R :=
  y + y ^ 3 / 6 + y ^ 5 / 120 + y ^ 7 / 5040 + y ^ 9 / 362880 + y ^ 11 / 39916800
  + y ^ 13 / 6227020800 + y ^ 15 / 1307674368000.

(** [1 + y^2/2! + ... + y^12/12!]. *)
Definition cosh_taylor12 (y : R) : R :=
  1 + y ^ 2 / 2 + y ^ 4 / 24 + y ^ 6 / 720 + y ^ 8 / 40320 + y ^ 10 / 3628800
  + y ^ 12 / 479001600.

(** [0 <= sinh y - sinh_taylor15 y <= 3/2 * y^17 / 17!] on [[0, 1]]: [exp y]
    lies between its Taylor polynomial [P] of degree 16 and [P] plus twice
    the next term ([exp_le_taylor]), and [exp (-y)] between the alternating
    sums of degree 17 and 16 ([exp_alt_bounds]). *)
Lemma sinh_taylor :
  forall y, 0 <= y <= 1 ->
  0 <= sinh y - sinh_taylor15 y <= 3 / 2 * (y ^ 17 / 355687428096000).
Proof.
intros y Hy.
assert (Hel : sum_f_R0 (fun i => / INR (fact i) * y ^ i) 16 <= exp y).
{ apply sum_incr; [exact (proj2_sig (exist_exp y)) |].
  intros n. apply Rmult_le_pos; [left; apply Rinv_0_lt_compat, INR_fact_lt_0 | apply pow_le; lra]. }
pose proof (exp_le_taylor 16 y Hy) as Heu.
destruct (exp_alt_bounds y 8 Hy) as [Hfl Hfu].
change (S (2 * 8)) with 17%nat in Hfl. change (2 * 8)%nat with 16%nat in Hfu.
rewrite tech5, exp_tg_alt in Hfl.
assert (E : sum_f_R0 (fun i => / INR (fact i) * y ^ i) 16 - sum_f_R0 (tg_alt (exp_tg y)) 16 =
            2 * sinh_taylor15 y).
{ unfold sinh_taylor15. cbn [sum_f_R0]. rewrite !exp_tg_alt, !fact_R. zfact_lit. field. }
assert (F17 : INR (fact 17) = 355687428096000)
  by (rewrite fact_R; apply f_equal; vm_compute; reflexivity).
assert (P17 : (- y) ^ 17 = - y ^ 17) by ring.
rewrite F17, P17 in Hfl. rewrite F17 in Heu.
unfold sinh. lra.
Qed.

(** [0 <= cosh y - cosh_taylor12 y <= 3/2 * y^14 / 14!] on [[0, 1]], as
    [sinh_taylor]. *)
Lemma cosh_taylor :
  forall y, 0 <= y <= 1 ->
  0 <= cosh y - cosh_taylor12 y <= 3 / 2 * (y ^ 14 / 87178291200).
Proof.
intros y Hy.
assert (Hel : sum_f_R0 (fun i => / INR (fact i) * y ^ i) 13 <= exp y).
{ apply sum_incr; [exact (proj2_sig (exist_exp y)) |].
  intros n. apply Rmult_le_pos; [left; apply Rinv_0_lt_compat, INR_fact_lt_0 | apply pow_le; lra]. }
pose proof (exp_le_taylor 13 y Hy) as Heu.
destruct (exp_alt_bounds y 6 Hy) as [Hfl _].
destruct (exp_alt_bounds y 7 Hy) as [_ Hfu].
change (S (2 * 6)) with 13%nat in Hfl. change (2 * 7)%nat with 14%nat in Hfu.
rewrite tech5, exp_tg_alt in Hfu.
assert (E : sum_f_R0 (fun i => / INR (fact i) * y ^ i) 13 + sum_f_R0 (tg_alt (exp_tg y)) 13 =
            2 * cosh_taylor12 y).
{ unfold cosh_taylor12. cbn [sum_f_R0]. rewrite !exp_tg_alt, !fact_R. zfact_lit. field. }
assert (F14 : INR (fact 14) = 87178291200)
  by (rewrite fact_R; apply f_equal; vm_compute; reflexivity).
assert (P14 : (- y) ^ 14 = y ^ 14) by ring.
rewrite F14, P14 in Hfu. rewrite F14 in Heu.
unfold cosh. lra.
Qed.
