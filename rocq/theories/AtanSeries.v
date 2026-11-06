(** * The series of atan, and the halving of its argument

    [atan_sum n x] is the sum of the first [n] terms of the series of
    [atan x]. For every real [x], the remainder after [n] terms, times
    [(-1)^n], is [T x^(2n+1)] with [T] in [[0, 1/(2n+1)]]
    ([atan_tail_bounds]): it is the integral from 0 to [x] of
    [t^(2n) / (1 + t^2)]. [atan_horner] is one step of Horner's scheme in
    [x^2] on these scaled remainders, as [atanh_horner] of [DyLogRules.v]
    is for atanh. [atan_halve] halves the argument: [atan u] is
    [2 atan(u / (1 + √(1 + u^2)))]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core.
From Inari Require Import Elementary.

Open Scope R_scope.

(** [Σ_{i < n} (-1)^i x^(2i+1) / (2i+1)] *)
Fixpoint atan_sum (n : nat) (x : R) : R :=
  match n with
  | O => 0
  | S m => atan_sum m x + (-1) ^ m * x ^ (2 * m + 1) / INR (2 * m + 1)
  end.

(** ** The remainder of the series *)

(** [Σ_{i < n} (-1)^i x^(2i)], the derivative of [atan_sum n] *)
Fixpoint at_geo_sum (n : nat) (x : R) : R :=
  match n with
  | O => 0
  | S m => at_geo_sum m x + (-1) ^ m * x ^ (2 * m)
  end.

(** The geometric sum in [-x^2]. *)
Lemma at_geo_sum_eq :
  forall n x, at_geo_sum n x * (1 + x ^ 2) = 1 - (-1) ^ n * x ^ (2 * n).
Proof.
induction n as [| m IH]; intros x; cbn [at_geo_sum].
- simpl. ring.
- replace (2 * S m)%nat with (2 * m + 2)%nat by lia. rewrite pow_add.
  change ((-1) ^ S m) with (-1 * (-1) ^ m).
  rewrite Rmult_plus_distr_r, IH. ring.
Qed.

Lemma at_derive_eq :
  forall f x l l', derivable_pt_lim f x l -> l = l' -> derivable_pt_lim f x l'.
Proof. intros f x l l' H <-. exact H. Qed.

Lemma at_sum_derive : forall n x, derivable_pt_lim (atan_sum n) x (at_geo_sum n x).
Proof.
induction n as [| m IH]; intros x.
- apply (derivable_pt_lim_ext (fct_cte 0)); [intros z; reflexivity |].
  apply derivable_pt_lim_const.
- apply (derivable_pt_lim_ext
           (atan_sum m
            + mult_real_fct ((-1) ^ m / INR (2 * m + 1)) (fun y => y ^ (2 * m + 1)))%F).
  { intros z. unfold plus_fct, mult_real_fct. cbn [atan_sum]. unfold Rdiv. ring. }
  eapply at_derive_eq.
  + apply derivable_pt_lim_plus; [apply IH |].
    apply derivable_pt_lim_scal. apply derivable_pt_lim_pow.
  + cbn [at_geo_sum]. replace (Init.Nat.pred (2 * m + 1)) with (2 * m)%nat by lia.
    field. apply not_0_INR. lia.
Qed.

(** Stdlib 9.1 has [Rdiv_lt_0_compat] but no [<=] form. *)
Lemma at_div_nonneg : forall a b, 0 <= a -> 0 < b -> 0 <= a / b.
Proof.
intros a b Ha Hb. unfold Rdiv. apply Rmult_le_pos; [exact Ha |].
apply Rlt_le, Rinv_0_lt_compat. exact Hb.
Qed.

Lemma at_sign_sq : forall n, (-1) ^ n * (-1) ^ n = 1.
Proof.
intros n. rewrite <- Rpow_mult_distr. replace (-1 * -1) with 1 by ring. apply pow1.
Qed.

(** The derivative of the remainder times [(-1)^n] is [x^(2n) / (1 + x^2)]. *)
Lemma at_rem_derive :
  forall n c,
  derivable_pt_lim (fun r => (-1) ^ n * (atan r - atan_sum n r)) c
    (c ^ (2 * n) / (1 + c ^ 2)).
Proof.
intros n c.
apply (derivable_pt_lim_ext (mult_real_fct ((-1) ^ n) (atan - atan_sum n)%F));
  [intros z; reflexivity |].
eapply at_derive_eq.
- apply derivable_pt_lim_scal.
  apply derivable_pt_lim_minus; [apply derivable_pt_lim_atan | apply at_sum_derive].
- assert (Hq : 0 < 1 + c ^ 2) by nra.
  pose proof (at_geo_sum_eq n c) as Hg.
  replace (at_geo_sum n c) with ((1 - (-1) ^ n * c ^ (2 * n)) / (1 + c ^ 2))
    by (rewrite <- Hg; field; lra).
  (* [((-1)^n)^2 = 1] removes the sign. *)
  replace (c ^ (2 * n) / (1 + c ^ 2))
    with ((-1) ^ n * (-1) ^ n * (c ^ (2 * n) / (1 + c ^ 2)))
    by (rewrite at_sign_sq; ring).
  field. lra.
Qed.

(** The derivative of [x^(2n+1) / (2n+1)] minus that remainder is
    [x^(2n) - x^(2n) / (1 + x^2)]. *)
Lemma at_upper_derive :
  forall n c,
  derivable_pt_lim
    (fun r => r ^ (2 * n + 1) / INR (2 * n + 1) - (-1) ^ n * (atan r - atan_sum n r)) c
    (c ^ (2 * n) - c ^ (2 * n) / (1 + c ^ 2)).
Proof.
intros n c.
apply (derivable_pt_lim_ext
         (mult_real_fct (/ INR (2 * n + 1)) (fun y => y ^ (2 * n + 1))
          - (fun r => ((-1) ^ n * (atan r - atan_sum n r))%R))%F).
{ intros z. unfold minus_fct, mult_real_fct. unfold Rdiv. ring. }
eapply at_derive_eq.
- apply derivable_pt_lim_minus; [| apply at_rem_derive].
  apply derivable_pt_lim_scal. apply derivable_pt_lim_pow.
- replace (Init.Nat.pred (2 * n + 1)) with (2 * n)%nat by lia.
  assert (Hq : 0 < 1 + c ^ 2) by nra.
  field. split; [lra | apply not_0_INR; lia].
Qed.

Lemma at_sum_0 : forall n, atan_sum n 0 = 0.
Proof.
induction n as [| m IH]; cbn [atan_sum]; [reflexivity |].
rewrite IH, pow_i by lia. unfold Rdiv. ring.
Qed.

(** For [x > 0]: [0 <= (-1)^n (atan x - atan_sum n x) <= x^(2n+1) / (2n+1)], by
    the mean value theorem on [[0, x]] for the remainder and for its
    difference from [x^(2n+1) / (2n+1)], whose derivatives are nonnegative. *)
Lemma at_tail_pos :
  forall n x, 0 < x ->
  0 <= (-1) ^ n * (atan x - atan_sum n x) <= x ^ (2 * n + 1) / INR (2 * n + 1).
Proof.
intros n x Hx.
destruct (MVT_cor2 (fun r => (-1) ^ n * (atan r - atan_sum n r))
            (fun r => r ^ (2 * n) / (1 + r ^ 2)) 0 x Hx
            (fun c _ => at_rem_derive n c)) as (c & Hc & Hc0).
destruct (MVT_cor2
            (fun r => r ^ (2 * n + 1) / INR (2 * n + 1) - (-1) ^ n * (atan r - atan_sum n r))
            (fun r => r ^ (2 * n) - r ^ (2 * n) / (1 + r ^ 2)) 0 x Hx
            (fun c _ => at_upper_derive n c)) as (d & Hd & Hd0).
cbv beta in Hc, Hd.
rewrite atan_0, at_sum_0 in Hc, Hd. rewrite pow_i in Hd by lia.
replace (0 / INR (2 * n + 1)) with 0 in Hd by (unfold Rdiv; ring).
replace ((-1) ^ n * (0 - 0)) with 0 in Hc, Hd by ring.
rewrite Rminus_0_r in Hc, Hd.
assert (Hc2 : 0 < 1 + c ^ 2) by nra.
assert (Hd2 : 0 < 1 + d ^ 2) by nra.
assert (Hcn : 0 <= c ^ (2 * n)) by (apply pow_le; lra).
assert (Hdn : 0 <= d ^ (2 * n)) by (apply pow_le; lra).
(* Both derivatives are nonnegative at the points of the theorem. *)
assert (Pc : 0 <= c ^ (2 * n) / (1 + c ^ 2) * x).
{ apply Rmult_le_pos; [| lra]. apply at_div_nonneg; lra. }
assert (Pd : 0 <= (d ^ (2 * n) - d ^ (2 * n) / (1 + d ^ 2)) * x).
{ apply Rmult_le_pos; [| lra].
  replace (d ^ (2 * n) - d ^ (2 * n) / (1 + d ^ 2))
    with (d ^ (2 * n) * (d ^ 2 / (1 + d ^ 2))) by (field; lra).
  apply Rmult_le_pos; [exact Hdn |]. apply at_div_nonneg; [nra | lra]. }
lra.
Qed.

(** [atan] and [atan_sum n] are odd. *)
Lemma at_rem_opp :
  forall n x,
  (-1) ^ n * (atan (- x) - atan_sum n (- x)) = - ((-1) ^ n * (atan x - atan_sum n x)).
Proof.
intros n x.
assert (Hs : forall m, atan_sum m (- x) = - atan_sum m x).
{ induction m as [| m IH]; cbn [atan_sum]; [ring |].
  rewrite IH.
  replace (- x) with (-1 * x) by ring. rewrite Rpow_mult_distr.
  replace (2 * m + 1)%nat with (S (2 * m)) by lia. rewrite pow_1_odd.
  unfold Rdiv. ring. }
rewrite atan_opp, Hs. ring.
Qed.

Lemma at_pow_opp : forall n x, (- x) ^ (2 * n + 1) = - x ^ (2 * n + 1).
Proof.
intros n x.
replace (- x) with (-1 * x) by ring. rewrite Rpow_mult_distr.
replace (2 * n + 1)%nat with (S (2 * n)) by lia. rewrite pow_1_odd. ring.
Qed.

Lemma atan_tail_bounds :
  forall n x, exists T, 0 <= T <= 1 / INR (2 * n + 1) /\
  T * x ^ (2 * n + 1) = (-1) ^ n * (atan x - atan_sum n x).
Proof.
intros n x.
assert (Hi : 0 < INR (2 * n + 1)) by (apply lt_0_INR; lia).
destruct (Req_dec x 0) as [-> | Hx0].
- (* At 0 the remainder is 0. *)
  exists 0. split.
  + split; [lra |]. apply at_div_nonneg; lra.
  + rewrite atan_0, at_sum_0. ring.
- (* [T] is the remainder over [x^(2n+1)]; its bounds come from [|x|]. *)
  set (y := Rabs x).
  assert (Hy : 0 < y) by (apply Rabs_pos_lt; exact Hx0).
  assert (E : (-1) ^ n * (atan x - atan_sum n x) / x ^ (2 * n + 1) =
              (-1) ^ n * (atan y - atan_sum n y) / y ^ (2 * n + 1)).
  { unfold y. destruct (Rcase_abs x) as [Hn | Hn].
    - rewrite (Rabs_left x Hn), at_rem_opp, at_pow_opp. field.
      apply pow_nonzero. exact Hx0.
    - rewrite (Rabs_right x Hn). reflexivity. }
  assert (Hp : 0 < y ^ (2 * n + 1)) by (apply pow_lt; exact Hy).
  destruct (at_tail_pos n y Hy) as [B1 B2].
  exists ((-1) ^ n * (atan x - atan_sum n x) / x ^ (2 * n + 1)).
  split.
  + rewrite E. split.
    * apply at_div_nonneg; lra.
    * apply (Rmult_le_reg_r (y ^ (2 * n + 1))); [exact Hp |].
      replace ((-1) ^ n * (atan y - atan_sum n y) / y ^ (2 * n + 1) * y ^ (2 * n + 1))
        with ((-1) ^ n * (atan y - atan_sum n y)) by (field; lra).
      replace (1 / INR (2 * n + 1) * y ^ (2 * n + 1))
        with (y ^ (2 * n + 1) / INR (2 * n + 1)) by (field; lra).
      exact B2.
  + field. apply pow_nonzero. exact Hx0.
Qed.

(** One step of Horner's scheme, from [T] for [k + 1] terms to
    [1 / (2k+1) - x^2 T] for [k] terms. *)
Lemma atan_horner :
  forall k x T,
  T * x ^ (2 * S k + 1) = (-1) ^ S k * (atan x - atan_sum (S k) x) ->
  (1 / IZR (2 * Z.of_nat k + 1) - x * x * T) * x ^ (2 * k + 1) =
  (-1) ^ k * (atan x - atan_sum k x).
Proof.
intros k x T H. cbn [atan_sum] in H.
replace (2 * S k + 1)%nat with (2 * k + 1 + 2)%nat in H by lia.
rewrite pow_add in H.
rewrite INR_IZR_INZ in H.
replace (Z.of_nat (2 * k + 1)) with (2 * Z.of_nat k + 1)%Z in H by lia.
assert (Hz : IZR (2 * Z.of_nat k + 1) <> 0) by (apply not_0_IZR; lia).
change ((-1) ^ S k) with (-1 * (-1) ^ k) in H.
pose proof (at_sign_sq k) as Hs.
set (p := x ^ (2 * k + 1)) in *. set (z := IZR (2 * Z.of_nat k + 1)) in *.
set (s := (-1) ^ k) in *.
assert (E : T * (p * x ^ 2) = - s * (atan x - atan_sum k x) + s * s * (p / z))
  by (rewrite H; field; exact Hz).
rewrite Hs, Rmult_1_l in E.
transitivity (p / z - T * (p * x ^ 2)); [field; exact Hz |].
rewrite E. ring.
Qed.

(** ** Halving the argument *)

(** With [s = √(1 + u^2)] and [v = u / (1 + s)]: [|u| < s], so [|v| < 1] and
    [|2 atan v| < π/2], and [tan (2 atan v) = 2v / (1 - v^2) = u], as
    [1 - v^2 = 2 / (1 + s)]. *)
Lemma atan_halve : forall u, atan u = 2 * atan (u / (1 + sqrt (1 + u * u))).
Proof.
intros u.
assert (Hs0 : 0 <= 1 + u * u) by nra.
set (s := sqrt (1 + u * u)).
assert (Hss : s * s = 1 + u * u) by (apply sqrt_sqrt; exact Hs0).
assert (Hs : 0 <= s) by apply sqrt_pos.
assert (Hu1 : u < s) by nra.
assert (Hu2 : - s < u) by nra.
set (v := u / (1 + s)).
assert (Hvs : v * (1 + s) = u) by (unfold v; field; lra).
assert (Hv : -1 < v < 1) by (split; nra).
(* [Ropp 1], not the literal [-1] (which [- 1] also parses to), so that
   [atan_opp] applies. *)
assert (Ha1 : atan (Ropp 1) < atan v) by (apply atan_increasing; lra).
assert (Ha2 : atan v < atan 1) by (apply atan_increasing; lra).
rewrite atan_opp, atan_1 in Ha1. rewrite atan_1 in Ha2.
assert (Ha : - (PI / 2) < 2 * atan v < PI / 2) by lra.
assert (Hc1 : cos (atan v) <> 0).
{ destruct (atan_bound v). apply Rgt_not_eq, cos_gt_0; lra. }
assert (Hc2 : cos (2 * atan v) <> 0).
{ apply Rgt_not_eq, cos_gt_0; lra. }
assert (Htan : tan (2 * atan v) = u).
{ rewrite tan_2a; [| exact Hc1 | exact Hc2 | rewrite tan_atan; nra]. rewrite tan_atan.
  assert (E : 1 - v * v = 2 / (1 + s)).
  { unfold v. replace (u / (1 + s) * (u / (1 + s))) with (u * u / ((1 + s) * (1 + s)))
      by (field; lra).
    replace (u * u) with (s * s - 1) by lra. field. lra. }
  rewrite E. unfold v. field. lra. }
rewrite <- Htan at 1. apply atan_tan. exact Ha.
Qed.
