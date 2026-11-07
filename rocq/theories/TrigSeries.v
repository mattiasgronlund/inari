(** * The series of sin and cos, and their quadrants

    What [DyTrigCore.v] and [DyTrig.v] need of the reals. [trig_term odd
    a i] is the term of degree [2 i + 1] of the series of [sin a] if
    [odd], and that of degree [2 i] of [cos a] otherwise; [trig_sum odd k
    a] is the sum of the first [k] terms. For [|a| <= 1], the remainder
    after [k] terms is [T] times the next term for some [T] in [[0, 1]]
    ([trig_tail_bounds], from [sin_bound] and [cos_bound] of Stdlib's
    [Rtrigo1.v], and below two terms from [0 <= sin a <= a] and
    [0 <= cos a <= 1]), and these factors satisfy the step of Horner's scheme in
    [a^2] ([trig_horner]). [cos_sqrt] gives [cos a] from [sin a] for
    [|a| <= 1], and [sin_quad] and [tan_quad] give [sin] and [tan] of [k
    π/2 + a] or [k π/2 - a] from [sin a] and [cos a] by [k mod 4]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Inari Require Import TrigPieces.

Open Scope R_scope.

Definition trig_term (odd : bool) (a : R) (i : nat) : R :=
  (-1) ^ i * a ^ (2 * i + Nat.b2n odd) / INR (fact (2 * i + Nat.b2n odd)).

Fixpoint trig_sum (odd : bool) (k : nat) (a : R) : R :=
  match k with O => 0 | S j => trig_sum odd j a + trig_term odd a j end.

Definition trig_fn (odd : bool) (a : R) : R := if odd then sin a else cos a.

Lemma trig_term_0 : forall odd a, trig_term odd a 0 = if odd then a else 1.
Proof. intros [|] a; unfold trig_term; simpl; field. Qed.

Lemma trig_sum_S : forall odd k a, trig_sum odd (S k) a = trig_sum odd k a + trig_term odd a k.
Proof. reflexivity. Qed.

(** Each term is [- a^2 / ((2 k + 1 + o) (2 k + 2 + o))] times the one
    before, as [fact (n + 2) = (n + 2) (n + 1) fact n]. *)
Lemma trig_term_S :
  forall odd a k,
  trig_term odd a (S k) =
  - (a * a) * trig_term odd a k /
    ((2 * INR k + 1 + IZR (Z.b2z odd)) * (2 * INR k + 2 + IZR (Z.b2z odd))).
Proof.
  intros odd a k.
  assert (Ek : 0 <= INR k) by apply pos_INR.
  assert (HB : 0 <= IZR (Z.b2z odd)) by (apply IZR_le; destruct odd; simpl; lia).
  assert (En : INR (2 * k + Nat.b2n odd) = 2 * INR k + IZR (Z.b2z odd))
    by (rewrite plus_INR, mult_INR; destruct odd; simpl; ring).
  unfold trig_term.
  replace (2 * S k + Nat.b2n odd)%nat with (S (S (2 * k + Nat.b2n odd))) by lia.
  set (n := (2 * k + Nat.b2n odd)%nat) in *.
  rewrite !fact_simpl, !mult_INR, !S_INR, En.
  cbn [pow].
  field.
  repeat split; first [apply INR_fact_neq_0 | intro; lra].
Qed.

(** The step of Horner's scheme: if [T] times the term [S k] is the
    remainder after [S k] terms, then [1 - a^2 T / ((2 k + 1 + o) (2 k + 2
    + o))] times the term [k] is the remainder after [k] terms, where [o]
    is 1 for [sin] and 0 for [cos]. *)
Lemma trig_horner :
  forall odd k a T,
  T * trig_term odd a (S k) = trig_fn odd a - trig_sum odd (S k) a ->
  (1 - a * a * T / IZR ((2 * Z.of_nat k + 1 + Z.b2z odd) * (2 * Z.of_nat k + 2 + Z.b2z odd))) *
    trig_term odd a k = trig_fn odd a - trig_sum odd k a.
Proof.
  intros odd k a T H.
  rewrite trig_sum_S in H.
  assert (Ek : 0 <= INR k) by apply pos_INR.
  assert (HB : 0 <= IZR (Z.b2z odd)) by (apply IZR_le; destruct odd; simpl; lia).
  assert (D : IZR ((2 * Z.of_nat k + 1 + Z.b2z odd) * (2 * Z.of_nat k + 2 + Z.b2z odd)) =
              (2 * INR k + 1 + IZR (Z.b2z odd)) * (2 * INR k + 2 + IZR (Z.b2z odd)))
    by (rewrite mult_IZR, !plus_IZR, !mult_IZR, <- INR_IZR_INZ; reflexivity).
  (* The left side is the term [k] plus [T] times the term [S k]. *)
  transitivity (trig_term odd a k + T * trig_term odd a (S k)).
  - rewrite D, trig_term_S.
    field.
    repeat split; intro; lra.
  - rewrite H; ring.
Qed.

(** [sin_approx] and [cos_approx] of Stdlib's [Rtrigo_alt.v] sum the
    terms [0] to [m], inclusive. *)
Lemma sum_f_R0_trig_sum :
  forall odd a f, (forall i, f i = trig_term odd a i) ->
  forall m, sum_f_R0 f m = trig_sum odd (S m) a.
Proof.
  intros odd a f Hf m; induction m as [|m IH].
  - change (sum_f_R0 f 0%nat) with (f 0%nat).
    change (trig_sum odd 1 a) with (0 + trig_term odd a 0).
    rewrite Hf; ring.
  - change (sum_f_R0 f (S m)) with (sum_f_R0 f m + f (S m)).
    rewrite trig_sum_S, IH, Hf; reflexivity.
Qed.

Lemma trig_approx :
  forall (odd : bool) a m,
  (if odd then sin_approx a m else cos_approx a m) = trig_sum odd (S m) a.
Proof.
  intros [|] a m; [unfold sin_approx | unfold cos_approx];
    apply sum_f_R0_trig_sum; intros i; unfold sin_term, cos_term, trig_term; cbn [Nat.b2n].
  - unfold Rdiv; ring.
  - rewrite Nat.add_0_r; unfold Rdiv; ring.
Qed.

(** For [0 <= a <= 1] the partial sums bracket the function: an even
    number of terms is below it and an odd number above. Two and more
    terms are [sin_bound] and [cos_bound]; none and one term are
    [0 <= sin a <= a] and [0 <= cos a <= 1]. These need [a <= PI / 2],
    which holds as [1 < PI / 2] ([PI2_1]). *)
Lemma trig_bounds_even :
  forall odd a j, 0 <= a <= 1 ->
  trig_sum odd (2 * j) a <= trig_fn odd a <= trig_sum odd (2 * j + 1) a.
Proof.
  intros odd a j Ha; pose proof PI2_1 as HPI.
  destruct j as [|n].
  - change (2 * 0 + 1)%nat with 1%nat; change (2 * 0)%nat with 0%nat.
    rewrite trig_sum_S; change (trig_sum odd 0 a) with 0.
    destruct odd; unfold trig_fn.
    + replace (trig_term true a 0) with a by (rewrite trig_term_0; reflexivity).
      split; [apply sin_ge_0; lra|].
      destruct (Req_dec a 0) as [->|Ha0]; [rewrite sin_0; lra|].
      assert (sin a < a) by (apply sin_lt_x; lra); lra.
    + replace (trig_term false a 0) with 1 by (rewrite trig_term_0; reflexivity).
      split; [apply cos_ge_0; lra|].
      pose proof (COS_bound a); lra.
  - pose proof (trig_approx odd a (2 * n + 1)) as E1.
    pose proof (trig_approx odd a (2 * (n + 1))) as E2.
    replace (S (2 * n + 1)) with (2 * S n)%nat in E1 by lia.
    replace (S (2 * (n + 1))) with (2 * S n + 1)%nat in E2 by lia.
    rewrite <- E1, <- E2.
    destruct odd; unfold trig_fn; [apply sin_bound | apply cos_bound]; lra.
Qed.

Lemma trig_bounds_odd :
  forall odd a j, 0 <= a <= 1 ->
  trig_sum odd (2 * j + 2) a <= trig_fn odd a <= trig_sum odd (2 * j + 1) a.
Proof.
  intros odd a j Ha.
  pose proof (trig_bounds_even odd a j Ha) as H0.
  pose proof (trig_bounds_even odd a (S j) Ha) as H1.
  replace (2 * S j)%nat with (2 * j + 2)%nat in H1 by lia.
  lra.
Qed.

(** A remainder between 0 and the next term is that term times some [T]
    in [[0, 1]]; if the term is 0, so is the remainder, and [T = 0]. *)
Lemma tail_of_bracket :
  forall t r, (0 <= r <= t \/ t <= r <= 0) -> exists T, 0 <= T <= 1 /\ T * t = r.
Proof.
  intros t r H.
  destruct (Req_dec t 0) as [Ht|Ht].
  - exists 0; split; [lra|]; subst t; lra.
  - exists (r / t).
    assert (E : r / t * t = r) by (field; exact Ht).
    split; [|exact E].
    set (T := r / t) in *.
    destruct H as [[H1 H2]|[H1 H2]]; split; nra.
Qed.

Lemma trig_tail_pos :
  forall odd k a, 0 <= a <= 1 ->
  exists T, 0 <= T <= 1 /\ T * trig_term odd a k = trig_fn odd a - trig_sum odd k a.
Proof.
  intros odd k a Ha; apply tail_of_bracket.
  pose proof (trig_sum_S odd k a) as E.
  destruct (Nat.Even_or_Odd k) as [[j ->]|[j ->]].
  - pose proof (trig_bounds_even odd a j Ha) as H.
    replace (2 * j + 1)%nat with (S (2 * j)) in H by lia.
    rewrite E in H; left; lra.
  - pose proof (trig_bounds_odd odd a j Ha) as H.
    replace (2 * j + 2)%nat with (S (2 * j + 1)) in H by lia.
    rewrite E in H; right; lra.
Qed.

(** The terms, sums and functions are odd in [a] for [sin] and even for
    [cos]. *)
Lemma trig_term_opp :
  forall odd a i, trig_term odd (- a) i = (if odd then -1 else 1) * trig_term odd a i.
Proof.
  intros [|] a i; unfold trig_term; cbn [Nat.b2n].
  - rewrite !pow_add, !pow_mult; replace ((- a) ^ 2) with (a ^ 2) by ring; unfold Rdiv; ring.
  - rewrite Nat.add_0_r, !pow_mult; replace ((- a) ^ 2) with (a ^ 2) by ring; unfold Rdiv; ring.
Qed.

Lemma trig_sum_opp :
  forall odd k a, trig_sum odd k (- a) = (if odd then -1 else 1) * trig_sum odd k a.
Proof.
  intros odd k a; induction k as [|k IH].
  - change (trig_sum odd 0 (- a)) with 0; change (trig_sum odd 0 a) with 0; ring.
  - rewrite !trig_sum_S, IH, trig_term_opp; ring.
Qed.

Lemma trig_fn_opp : forall odd a, trig_fn odd (- a) = (if odd then -1 else 1) * trig_fn odd a.
Proof. intros [|] a; unfold trig_fn; [rewrite sin_neg | rewrite cos_neg]; ring. Qed.

Lemma trig_tail_bounds :
  forall odd k a, Rabs a <= 1 ->
  exists T, 0 <= T <= 1 /\ T * trig_term odd a k = trig_fn odd a - trig_sum odd k a.
Proof.
  intros odd k a Ha.
  assert (Hab : -1 <= a <= 1) by (unfold Rabs in Ha; destruct (Rcase_abs a); lra).
  destruct (Rle_dec 0 a) as [Hp|Hn].
  - apply trig_tail_pos; lra.
  - (* For [a < 0], the factor of [- a] serves, as both sides change by
       the same sign. *)
    destruct (trig_tail_pos odd k (- a)) as [T [HT E]]; [lra|].
    exists T; split; [exact HT|].
    rewrite trig_term_opp, trig_fn_opp, trig_sum_opp in E.
    destruct odd; cbv beta iota in E; lra.
Qed.

Lemma cos_sqrt : forall a, Rabs a <= 1 -> cos a = sqrt ((1 - sin a) * (1 + sin a)).
Proof.
  intros a Ha.
  assert (Hab : -1 <= a <= 1) by (unfold Rabs in Ha; destruct (Rcase_abs a); lra).
  pose proof PI2_1 as HPI.
  assert (Hc : 0 <= cos a) by (apply cos_ge_0; lra).
  (* [(1 - sin a) (1 + sin a) = 1 - sin² a = cos² a], and [cos a >= 0]. *)
  replace ((1 - sin a) * (1 + sin a)) with (cos a * cos a)
    by (pose proof (sin2_cos2 a) as E; unfold Rsqr in E; lra).
  rewrite sqrt_square; [reflexivity | exact Hc].
Qed.

(** ** Quadrants *)

(** [k π/2 + y] is [y + m π/2] plus a multiple of [2 π] for [m = k mod 4]
    ([tp_mod4]). *)
Lemma quad_shift :
  forall k m y, (k mod 4 = m)%Z ->
  sin (IZR k * (PI / 2) + y) = sin (y + IZR m * (PI / 2)) /\
  cos (IZR k * (PI / 2) + y) = cos (y + IZR m * (PI / 2)).
Proof.
  intros k m y Hm; destruct (tp_mod4 k m Hm) as [j ->].
  replace ((4 * IZR j + IZR m) * (PI / 2) + y) with ((y + IZR m * (PI / 2)) + 2 * IZR j * PI)
    by field.
  split; [apply tp_sin_period | apply tp_cos_period].
Qed.

Lemma sin_cos_PI2 : forall y, sin (y + PI / 2) = cos y /\ cos (y + PI / 2) = - sin y.
Proof. intros y; rewrite sin_plus, cos_plus, sin_PI2, cos_PI2; split; ring. Qed.

(** [sin] and [cos] of [y + m π/2] for [m] in [0..3]. *)
Lemma quad_cases :
  forall m y, (0 <= m < 4)%Z ->
  (m = 0%Z /\ sin (y + IZR m * (PI / 2)) = sin y /\ cos (y + IZR m * (PI / 2)) = cos y) \/
  (m = 1%Z /\ sin (y + IZR m * (PI / 2)) = cos y /\ cos (y + IZR m * (PI / 2)) = - sin y) \/
  (m = 2%Z /\ sin (y + IZR m * (PI / 2)) = - sin y /\ cos (y + IZR m * (PI / 2)) = - cos y) \/
  (m = 3%Z /\ sin (y + IZR m * (PI / 2)) = - cos y /\ cos (y + IZR m * (PI / 2)) = sin y).
Proof.
  intros m y Hm.
  destruct (sin_cos_PI2 y) as [S1 C1].
  assert (Hc : (m = 0 \/ m = 1 \/ m = 2 \/ m = 3)%Z) by lia.
  destruct Hc as [-> | [-> | [-> | ->]]].
  - left; rewrite Rmult_0_l, Rplus_0_r; auto.
  - right; left; rewrite Rmult_1_l; auto.
  - right; right; left.
    replace (y + IZR 2 * (PI / 2)) with (y + PI) by field.
    rewrite neg_sin, neg_cos; auto.
  - right; right; right.
    replace (y + IZR 3 * (PI / 2)) with ((y + PI / 2) + PI) by field.
    rewrite neg_sin, neg_cos, S1, C1; split; [reflexivity|]; split; [reflexivity | ring].
Qed.

(** Replaces each [Z.eqb] of two literals in the goal by its value. *)
Local Ltac z_eqb_compute :=
  repeat match goal with
  | |- context [ Z.eqb ?a ?b ] =>
      let v := eval vm_compute in (Z.eqb a b) in
      lazymatch v with
      | true => change (Z.eqb a b) with true
      | false => change (Z.eqb a b) with false
      end
  end.

Lemma sin_quad :
  forall (k quad : Z) (neg : bool) (rho : R), (k mod 4 = quad mod 4)%Z ->
  sin (IZR k * (PI / 2) + (if neg then - rho else rho)) =
  if (quad mod 2 =? 0)%Z then (if xorb neg (quad mod 4 =? 2)%Z then - sin rho else sin rho)
  else (if (quad mod 4 =? 3)%Z then - cos rho else cos rho).
Proof.
  intros k quad neg rho Hk.
  rewrite <- (Z.mod_mod_divide quad 4 2) by (exists 2%Z; reflexivity).
  destruct (quad_shift k (quad mod 4) (if neg then - rho else rho) Hk) as [-> _].
  assert (Hm : (0 <= quad mod 4 < 4)%Z) by (apply Z.mod_pos_bound; lia).
  clear Hk; revert Hm; generalize (quad mod 4)%Z as m; intros m Hm.
  destruct (quad_cases m (if neg then - rho else rho) Hm)
    as [[-> [-> _]]|[[-> [-> _]]|[[-> [-> _]]|[-> [-> _]]]]];
    z_eqb_compute; destruct neg; cbn [xorb negb];
    rewrite ?sin_neg, ?cos_neg; ring.
Qed.

Lemma tan_quad :
  forall (k quad : Z) (neg : bool) (rho : R), (k mod 4 = quad mod 4)%Z ->
  tan (IZR k * (PI / 2) + (if neg then - rho else rho)) =
  (if xorb neg (quad mod 2 =? 1)%Z then -1 else 1) *
  (if (quad mod 2 =? 1)%Z then cos rho / sin rho else sin rho / cos rho).
Proof.
  intros k quad neg rho Hk.
  rewrite <- (Z.mod_mod_divide quad 4 2) by (exists 2%Z; reflexivity).
  unfold tan.
  destruct (quad_shift k (quad mod 4) (if neg then - rho else rho) Hk) as [-> ->].
  assert (Hm : (0 <= quad mod 4 < 4)%Z) by (apply Z.mod_pos_bound; lia).
  clear Hk; revert Hm; generalize (quad mod 4)%Z as m; intros m Hm.
  (* At the poles a divisor is 0 and [/ - 0 = - / 0] ([Rinv_opp]), so
     the signs move out of the divisors even there. *)
  destruct (quad_cases m (if neg then - rho else rho) Hm)
    as [[-> [-> ->]]|[[-> [-> ->]]|[[-> [-> ->]]|[-> [-> ->]]]]];
    z_eqb_compute; destruct neg; cbn [xorb negb];
    rewrite ?sin_neg, ?cos_neg; unfold Rdiv; rewrite ?Ropp_involutive, ?Rinv_opp; ring.
Qed.
