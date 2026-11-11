(** * Taylor truncations of [arcsinh] near 0

    [asinh_taylor9] and [asinh_taylor15] bound the remainders of the odd
    Taylor polynomials of degrees 9 and 15 of [arcsinh] on [[0, 1/16]],
    for the near-0 branch of [asinh] ([FastAhypOdd.v]) and the near-1
    branch of [acosh] ([FastAhypNear1.v]).

    Both go through [FastLogTaylor.log1p_dominate], the mean value theorem
    on the remainder and the bound: the derivative of [arcsinh] at [c] is
    [1/√(1 + v)] with [v = c^2], and the derivative of the Taylor polynomial
    is [B(v)], the binomial series of [(1 + v)^(-1/2)] truncated after
    [v^4] (resp. [v^7]). Squaring turns [|1/√(1 + v) - B(v)| <= C v^k] into
    two polynomial inequalities on [[0, 1/256]], which [lra] proves from
    [0 <= v^j] and [v^(j+1) <= v^j / 256], and [nra] for the last one of
    degree 15 ([binom7_bounds]). *)

From Stdlib Require Import Reals Lra Lia.
From Inari Require Import FastLogTaylor.

Open Scope R_scope.

(** ** Odd polynomials and their derivatives *)

(** [Σ_{k < n} a_k r^(2k+1)] *)
Fixpoint odd_poly (a : nat -> R) (n : nat) (r : R) : R :=
  match n with
  | O => 0
  | S k => odd_poly a k r + a k * r ^ (2 * k + 1)
  end.

(** [Σ_{k < n} (2k+1) a_k r^(2k)], the derivative of [odd_poly a n] *)
Fixpoint odd_poly_deriv (a : nat -> R) (n : nat) (r : R) : R :=
  match n with
  | O => 0
  | S k => odd_poly_deriv a k r + a k * INR (2 * k + 1) * r ^ (2 * k)
  end.

Lemma odd_poly_0 : forall a n, odd_poly a n 0 = 0.
Proof.
intros a n; induction n as [| k IH]; cbn [odd_poly]; [reflexivity |].
rewrite IH, pow_i by lia. ring.
Qed.

Lemma odd_poly_derive :
  forall a n r, derivable_pt_lim (odd_poly a n) r (odd_poly_deriv a n r).
Proof.
intros a n; induction n as [| k IH]; intros r.
- apply (derivable_pt_lim_ext (fct_cte 0)); [intros z; reflexivity |].
  apply derivable_pt_lim_const.
- apply (derivable_pt_lim_ext
           (odd_poly a k + mult_real_fct (a k) (fun y => y ^ (2 * k + 1)))%F);
    [intros z; reflexivity |].
  eapply log1p_derive_eq.
  + apply derivable_pt_lim_plus; [apply IH |].
    apply derivable_pt_lim_scal. apply derivable_pt_lim_pow.
  + cbn [odd_poly_deriv].
    replace (Init.Nat.pred (2 * k + 1)) with (2 * k)%nat by lia. ring.
Qed.

(** The Taylor coefficients of [arcsinh] at 0, [(-1)^k C(2k, k) / (4^k (2k + 1))],
    up to degree 15 *)
Definition asinh_coef (k : nat) : R :=
  match k with
  | 0%nat => 1
  | 1%nat => - / 6
  | 2%nat => 3 / 40
  | 3%nat => - 5 / 112
  | 4%nat => 35 / 1152
  | 5%nat => - 63 / 2816
  | 6%nat => 231 / 13312
  | 7%nat => - 143 / 10240
  | _ => 0
  end.

(** ** The remainder through the mean value theorem *)

(** If the derivative of the remainder is dominated by the derivative of
    [r^(d+1) / K] on [[0, 1/16]], so is the remainder by [t^(d+1) / K]. *)
Lemma asinh_taylor_gen :
  forall n d K t, 0 <= t <= / 16 ->
  (forall c, 0 <= c <= / 16 ->
     Rabs (/ sqrt (c ^ 2 + 1) - odd_poly_deriv asinh_coef n c) <= INR (S d) * c ^ d / K) ->
  Rabs (arcsinh t - odd_poly asinh_coef n t) <= t ^ S d / K.
Proof.
intros n d K t Ht Hd.
assert (E0 : arcsinh 0 - odd_poly asinh_coef n 0 = 0)
  by (rewrite arcsinh_0, odd_poly_0; ring).
assert (P0 : 0 ^ S d = 0) by (apply pow_i; lia).
destruct (Rle_lt_or_eq_dec 0 t (proj1 Ht)) as [Ht0 | <-].
2: { rewrite E0, P0, Rabs_R0. right. unfold Rdiv. ring. }
pose proof (log1p_dominate (fun r => arcsinh r - odd_poly asinh_coef n r)
  (fun c => / sqrt (c ^ 2 + 1) - odd_poly_deriv asinh_coef n c)
  (fun r => 1 * r ^ S d / K) (fun c => 1 * (INR (S d) * c ^ d) / K) 0 t Ht0) as H.
cbv beta in H. rewrite E0, P0, Rminus_0_r in H.
eapply Rle_trans; [apply H | right; unfold Rdiv; ring].
- intros c _. cbv beta.
  apply (derivable_pt_lim_ext (arcsinh - odd_poly asinh_coef n)%F);
    [intros z; reflexivity |].
  apply derivable_pt_lim_minus; [apply derivable_pt_lim_arcsinh | apply odd_poly_derive].
- intros c _. apply log1p_bound_derive.
- intros c Hc. cbv beta.
  replace (1 * (INR (S d) * c ^ d) / K) with (INR (S d) * c ^ d / K)
    by (unfold Rdiv; ring).
  apply Hd. lra.
Qed.

(** ** The derivative bound by squaring *)

(** [L <= 1/√(1 + v) <= U] follows from [L^2 (1 + v) <= 1 <= U^2 (1 + v)]
    and [U >= 0]: with [w = √(1 + v)], [(L w)^2 <= 1] gives [L w <= 1], and
    [(U w)^2 >= 1] with [U w >= 0] gives [U w >= 1]. *)
Lemma inv_sqrt_between :
  forall v L U, 0 <= v -> 0 <= U ->
  L ^ 2 * (1 + v) <= 1 -> 1 <= U ^ 2 * (1 + v) ->
  L <= / sqrt (v + 1) <= U.
Proof.
intros v L U Hv HU HL HU2.
assert (Hw : 0 < sqrt (v + 1)) by (apply sqrt_lt_R0; lra).
assert (Hw2 : sqrt (v + 1) * sqrt (v + 1) = v + 1) by (apply sqrt_sqrt; lra).
set (w := sqrt (v + 1)) in *.
assert (EL : (L * w) ^ 2 = L ^ 2 * (1 + v))
  by (replace ((L * w) ^ 2) with (L ^ 2 * (w * w)) by ring; rewrite Hw2; ring).
assert (EU : (U * w) ^ 2 = U ^ 2 * (1 + v))
  by (replace ((U * w) ^ 2) with (U ^ 2 * (w * w)) by ring; rewrite Hw2; ring).
rewrite <- EL in HL. rewrite <- EU in HU2.
assert (HUw : 0 <= U * w) by (apply Rmult_le_pos; lra).
assert (H1 : L * w <= 1) by nra.
assert (H2 : 1 <= U * w) by nra.
split; apply (Rmult_le_reg_r w); auto; rewrite Rinv_l by lra; lra.
Qed.

(** [0 <= v^k] and [v^(k+1) <= v^k / 256] on [[0, 1/256]]: with these as
    hypotheses, [lra] bounds a polynomial whose terms below [v^j] cancel by
    its [v^j] coefficient minus its negative higher ones, each scaled by a
    power of [1/256]. *)
Lemma pow_step : forall v k, 0 <= v <= / 256 -> 0 <= v ^ k /\ v ^ S k <= / 256 * v ^ k.
Proof.
intros v k Hv. split; [apply pow_le; lra |].
change (v ^ S k) with (v * v ^ k).
apply Rmult_le_compat_r; [apply pow_le |]; lra.
Qed.

Ltac pow_steps v Hv n :=
  match n with
  | O => idtac
  | S ?m => destruct (pow_step v m Hv); pow_steps v Hv m
  end.

(** [(1 + v)^(-1/2)] truncated after [v^4] *)
Definition binom4 (v : R) : R :=
  1 - v / 2 + 3 * v ^ 2 / 8 - 5 * v ^ 3 / 16 + 35 * v ^ 4 / 128.

(** [(1 + v)^(-1/2)] truncated after [v^7] *)
Definition binom7 (v : R) : R :=
  binom4 v - 63 * v ^ 5 / 256 + 231 * v ^ 6 / 1024 - 429 * v ^ 7 / 2048.

(** The next term of the series is [-63/256 v^5], so [binom4] is above
    [1/√(1 + v)] and less than [11/40 v^5] away: [binom4 v ^ 2 (1 + v) - 1]
    starts at [63/128 v^5], and [1 - (binom4 v - 11/40 v^5)^2 (1 + v)] at
    [(11/20 - 63/128) v^5 = 37/640 v^5]. *)
Lemma binom4_bounds :
  forall v, 0 <= v <= / 256 ->
  0 <= binom4 v /\ 1 <= binom4 v ^ 2 * (1 + v) /\
  (binom4 v - 11 / 40 * v ^ 5) ^ 2 * (1 + v) <= 1.
Proof.
intros v Hv. pow_steps v Hv 11%nat. unfold binom4. repeat split; lra.
Qed.

(** The next term of the series is [+6435/32768 v^8], so [binom7] is below
    [1/√(1 + v)] and less than [17/80 v^8] away: [1 - binom7 v ^ 2 (1 + v)]
    starts at [6435/16384 v^8], and [(binom7 v + 17/80 v^8)^2 (1 + v) - 1]
    at [(17/40 - 6435/16384) v^8 = 2641/81920 v^8]. *)
Lemma binom7_bounds :
  forall v, 0 <= v <= / 256 ->
  0 <= binom7 v /\ binom7 v ^ 2 * (1 + v) <= 1 /\
  1 <= (binom7 v + 17 / 80 * v ^ 8) ^ 2 * (1 + v).
Proof.
intros v Hv. pow_steps v Hv 17%nat. unfold binom7, binom4.
(* [lra] finds no certificate for the last one; [nra] does. *)
split; [lra | split; [lra | nra]].
Qed.

Lemma sq_range : forall c, 0 <= c <= / 16 -> 0 <= c ^ 2 <= / 256.
Proof. intros c Hc. split; nra. Qed.

(** ** The theorems *)

Theorem asinh_taylor9 :
  forall t, 0 <= t <= / 16 ->
  Rabs (arcsinh t - (t - t ^ 3 / 6 + 3 * t ^ 5 / 40 - 5 * t ^ 7 / 112 + 35 * t ^ 9 / 1152))
    <= t ^ 11 / 40.
Proof.
intros t Ht.
match goal with |- Rabs (arcsinh t - ?p) <= _ =>
  replace p with (odd_poly asinh_coef 5 t)
    by (cbn [odd_poly asinh_coef Nat.mul Nat.add]; field)
end.
apply (asinh_taylor_gen 5 10 40 t Ht).
intros c Hc.
(* The derivative of the polynomial is [binom4 (c^2)], and the bound's is
   [11/40 (c^2)^5]. *)
replace (odd_poly_deriv asinh_coef 5 c) with (binom4 (c ^ 2))
  by (cbn [odd_poly_deriv asinh_coef Nat.mul Nat.add INR]; unfold binom4; field).
replace (INR 11 * c ^ 10 / 40) with (11 / 40 * (c ^ 2) ^ 5) by (cbn [INR]; field).
pose proof (sq_range c Hc) as Hv.
set (v := c ^ 2) in *.
destruct (binom4_bounds v Hv) as (HB & HU & HL).
destruct (inv_sqrt_between v (binom4 v - 11 / 40 * v ^ 5) (binom4 v)) as [H1 H2];
  try lra.
assert (0 <= v ^ 5) by (apply pow_le; lra).
apply Rabs_le. lra.
Qed.

Theorem asinh_taylor15 :
  forall s, 0 <= s <= / 16 ->
  Rabs (arcsinh s - (s - s ^ 3 / 6 + 3 * s ^ 5 / 40 - 5 * s ^ 7 / 112 + 35 * s ^ 9 / 1152
    - 63 * s ^ 11 / 2816 + 231 * s ^ 13 / 13312 - 143 * s ^ 15 / 10240)) <= s ^ 17 / 80.
Proof.
intros s Hs.
match goal with |- Rabs (arcsinh s - ?p) <= _ =>
  replace p with (odd_poly asinh_coef 8 s)
    by (cbn [odd_poly asinh_coef Nat.mul Nat.add]; field)
end.
apply (asinh_taylor_gen 8 16 80 s Hs).
intros c Hc.
(* The derivative of the polynomial is [binom7 (c^2)], and the bound's is
   [17/80 (c^2)^8]. *)
replace (odd_poly_deriv asinh_coef 8 c) with (binom7 (c ^ 2))
  by (cbn [odd_poly_deriv asinh_coef Nat.mul Nat.add INR]; unfold binom7, binom4; field).
replace (INR 17 * c ^ 16 / 80) with (17 / 80 * (c ^ 2) ^ 8) by (cbn [INR]; field).
pose proof (sq_range c Hc) as Hv.
set (v := c ^ 2) in *.
destruct (binom7_bounds v Hv) as (HB & HL & HU).
assert (0 <= v ^ 8) by (apply pow_le; lra).
destruct (inv_sqrt_between v (binom7 v) (binom7 v + 17 / 80 * v ^ 8)) as [H1 H2];
  try lra.
apply Rabs_le. lra.
Qed.
