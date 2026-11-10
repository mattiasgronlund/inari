(** * The logarithms and inverse hyperbolic functions of the kernel at their exact results

    At a finite [x] in its domain whose exact result is an [f64] [v],
    each of [ln], [log2], [log10], [asinh], [acosh] and [atanh] of
    [DyadicLog] returns [v]: with any driver where a rule settles every
    such [x] ([log10], [asinh], [atanh]), and otherwise with a driver that
    returns exact points ([driver_exact] of [DyPown.v], and
    [driver_exact_zero] of [DyExactDriver.v] for the point 0). The only
    such arguments are these. [ln x = s] and [atanh x = s] give
    [e^s = x] and [e^(2s) = (1 + x) / (1 - x)], rationals, so [s = 0]
    ([exp_irrational]), at [x = 1] and [x = ±0]. [log2 x = s] and
    [log10 x = s] give [x = 2^s] and [x = 10^s], so [s] is an integer
    ([pow2_rational], [pow10_rational]) from -1074 to 1023 for [log2] and
    from 0 to 22 for [log10] ([f64_pow2], [f64_pow10]). [asinh x = s] and
    [acosh x = s] give [(e^s)^2 - 2 x e^s -+ 1 = 0], so [s = 0] under the
    hypothesis [exp_not_quadratic] of [ExpQuadratic.v], at [x = ±0] and
    [x = 1]. [ev_ln] and [ev_acosh] enclose 0 by the point 0 at [x = 1],
    and [ev_log2] encloses [k] by the point [k] at [x = 2^k]
    ([ev_ln_one], [ev_acosh_one], [ev_log2_exact] of [DyLogPoint.v]);
    [log10] returns [k] at [x = 10^k] by its rule, and [asinh] and
    [atanh] return [x] at [x = ±0]. Where the result is 0, [ln], [log2], [log10] and [acosh]
    return [zero], the [f64] [+0], and [asinh] and [atanh] return [x]. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary LogReal DyRound DyConv DyOps DyDriver
  DyGrow DyConst DyExpCore DyExpRules DyExp DyHyp DyLogRules DyLogTiny DyLogCore DyLog DyLogHyp
  DyPowExact DyPown DyExactDriver PowFactor ExpIrrational ExpQuadratic DyTrigExact DyLogPoint
  FastLog FastAhyp.

Open Scope R_scope.

(** ** Helpers *)

(** A finite [f64] of nonzero value is [B754_finite]. *)
Lemma dle_strict : forall x : f64, is_finite x = true -> B2R x <> 0 -> is_finite_strict x = true.
Proof.
intros x Fx N. destruct x as [s | s | | s m e B]; try discriminate Fx; [| reflexivity].
exfalso. apply N. reflexivity.
Qed.

(** [one] is the only finite [f64] of value 1. *)
Lemma dle_one : forall x : f64, is_finite x = true -> B2R x = 1 -> x = DyadicExp.one.
Proof.
intros x Fx X1.
apply B2R_inj; [apply dle_strict; [exact Fx | lra] | vm_compute; reflexivity |].
rewrite X1, (proj2 one_B2R). reflexivity.
Qed.

(** A finite [v] at which [e^(m v)], [m <> 0], is a rational is 0, as
    [B2R v] is a rational ([f64_rational], [exp_irrational]). *)
Lemma dle_exp_zero :
  forall (v : f64) (m a b : Z), is_finite v = true -> m <> 0%Z -> (0 < b)%Z ->
  exp (IZR m * B2R v) = IZR a / IZR b -> B2R v = 0.
Proof.
intros v m a b Fv Hm Hb H.
destruct (f64_rational v Fv) as (p & q & Hq & Ev).
destruct (Z.eq_dec p 0) as [-> | Np]; [rewrite Ev; unfold Rdiv; apply Rmult_0_l |].
exfalso.
assert (N : (m * p <> 0)%Z) by (apply Z.neq_mul_0; split; assumption).
apply (exp_irrational (m * p) q a b Hq N Hb).
rewrite <- H, Ev, mult_IZR. f_equal. unfold Rdiv. ring.
Qed.

(** A finite [v] at which [e^v] is a root of [t^2 - 2 x t + c], for a
    finite [x] and an integer [c], is 0 under [exp_not_quadratic]: with
    [x = a / b] and [v = p / q], [e^(p/q)] is a root of
    [b t^2 - 2 a t + b c], whose leading coefficient [b] is not 0. *)
Lemma dle_quad_zero :
  exp_not_quadratic ->
  forall (x v : f64) (c : Z), is_finite x = true -> is_finite v = true ->
  exp (B2R v) ^ 2 - 2 * B2R x * exp (B2R v) + IZR c = 0 -> B2R v = 0.
Proof.
intros HQ x v c Fx Fv H.
destruct (f64_rational v Fv) as (p & q & Hq & Ev).
destruct (f64_rational x Fx) as (a & b & Hb & Ex).
destruct (Z.eq_dec p 0) as [-> | Np]; [rewrite Ev; unfold Rdiv; apply Rmult_0_l |].
exfalso.
assert (Rb : IZR b <> 0) by (apply not_0_IZR; lia).
apply (HQ p q Hq Np b (- (2 * a))%Z (b * c)%Z); [left; lia |].
(* [b (e^v)^2 - 2 a e^v + b c = b ((e^v)^2 - 2 x e^v + c)] *)
assert (E2 : IZR b * exp (B2R v) ^ 2 + IZR (- (2 * a)) * exp (B2R v) + IZR (b * c)
             = IZR b * (exp (B2R v) ^ 2 - 2 * B2R x * exp (B2R v) + IZR c)).
{ rewrite Ex, opp_IZR, !mult_IZR. field. exact Rb. }
rewrite <- Ev, E2, H. ring.
Qed.

(** [y = log_c x], for [c > 1], gives [x = c^y]. *)
Lemma dle_rlog_rpower : forall c x y, 1 < c -> 0 < x -> Rlog c x = y -> x = Rpower c y.
Proof.
intros c x y Hc Hx H. unfold Rlog in H. unfold Rpower.
assert (L : 0 < ln c) by (rewrite <- ln_1; apply ln_increasing; lra).
rewrite <- H. replace (ln x / ln c * ln c) with (ln x) by (field; lra).
symmetry. apply exp_ln. exact Hx.
Qed.

(** A finite [x > 0] whose [log_c x] is a finite [f64] [v] is [c^k] for
    the integer [k = v], where [c^(p/q)] is rational only if [q] divides
    [p] ([pow2_rational], [pow10_rational]). *)
Lemma dle_log_int :
  forall c, 1 < c ->
  (forall p q a b : Z, (0 < q)%Z -> (0 < b)%Z ->
     Rpower c (IZR p / IZR q) = IZR a / IZR b -> (q | p)%Z) ->
  forall x v : f64, is_finite x = true -> is_finite v = true -> 0 < B2R x ->
  Rlog c (B2R x) = B2R v -> exists k, B2R v = IZR k /\ B2R x = powerRZ c k.
Proof.
intros c Hc Hr x v Fx Fv Hx H.
destruct (f64_rational v Fv) as (p & q & Hq & Ev).
destruct (f64_rational x Fx) as (a & b & Hb & Ex).
pose proof (dle_rlog_rpower c (B2R x) (B2R v) Hc Hx H) as E.
assert (D : (q | p)%Z).
{ apply (Hr p q a b Hq Hb). rewrite <- Ev, <- E. exact Ex. }
destruct D as (k & ->).
assert (Vk : B2R v = IZR k).
{ rewrite Ev, mult_IZR. field. apply not_0_IZR. lia. }
exists k. split; [exact Vk |].
rewrite powerRZ_Rpower by lra. rewrite <- Vk. exact E.
Qed.

(** The [f64] [pow10 k] is [10^k], for [0 <= k <= 22], as in
    [log10_pow10_rule] of [DyLogRules.v]. *)
Lemma dle_pow10 :
  forall k : nat, (k <= 22)%nat ->
  is_finite (DyadicExp.pow10 (Z.of_nat k)) = true /\ B2R (DyadicExp.pow10 (Z.of_nat k)) = 10 ^ k.
Proof.
intros k Hk. destruct k as [| k'].
- change (DyadicExp.pow10 (Z.of_nat 0)) with (of_u64 1).
  destruct (of_u64_exact 1) as (F1 & E1); [lia |].
  split; [exact F1 |]. rewrite E1. reflexivity.
- assert (Hk' : (1 <= Z.of_nat (S k') <= 22)%Z) by lia.
  destruct (pow10_exact (Z.of_nat (S k')) Hk') as [F E].
  split; [exact F |]. rewrite E, <- pow_IZR. reflexivity.
Qed.

Theorem ln_dir_exact_with :
  forall z, driver_exact_zero z ->
  forall x (v : f64) (up : bool),
  is_finite x = true -> log_dom (B2R x) -> is_finite v = true -> ln (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = zero) ->
  DyadicLog.ln_dir_with z x up = Some v.
Proof.
intros z Hz0 x v up Fx Dx Fv H Hz.
(* [e^v = x] is a rational, so [v = 0] ([dle_exp_zero]), and then
   [x = e^0 = 1]. *)
assert (E : exp (B2R v) = B2R x) by (rewrite <- H; apply exp_ln; exact Dx).
destruct (f64_rational x Fx) as (a & b & Hb & Ex).
assert (V0 : B2R v = 0).
{ apply (dle_exp_zero v 1 a b Fv ltac:(discriminate) Hb). rewrite Rmult_1_l, E. exact Ex. }
assert (X1 : B2R x = 1) by (rewrite <- E, V0; apply exp_0).
rewrite (dle_one x Fx X1) in Dx |- *.
destruct Hz as [Hz | ->]; [contradiction |].
(* No rule of [log_rules] applies to 1, so [ln] is the driver on
   [ev_ln 1], which encloses 0 by the point 0 at every level
   ([ev_ln_one]). *)
unfold DyadicLog.ln_dir_with.
rewrite (log_rules_finite_pos DyadicExp.one (proj1 one_B2R) Dx), fast_ln_one.
apply Hz0; [lia | exact ev_ln_one].
Qed.

Theorem ln_dir_exact :
  forall x (v : f64) (up : bool),
  is_finite x = true -> log_dom (B2R x) -> is_finite v = true -> ln (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = zero) ->
  DyadicLog.ln_dir x up = Some v.
Proof.
intros x v up. apply ln_dir_exact_with. exact ziv_exact_zero.
Qed.

(** Where the fast path of [log2] returns at an [x] whose [log2 x] is a
    nonzero [f64] [v], it returns [v]. *)
Lemma fast_log2_exact :
  forall x up (v r : f64),
  is_finite x = true -> 0 < B2R x -> is_finite v = true -> Rlog2 (B2R x) = B2R v ->
  B2R v <> 0 -> DyadicLog.fast_log2_dir false x up = Some r -> r = v.
Proof.
intros x up v r Fx Hx Fv H Nv F.
pose proof (fast_log2_dir_correct false x up r Fx Hx F) as R. unfold rounds in R. rewrite H in R.
pose proof (DyExpRules.rnd_exact v (if up then RNDU else RNDD) (B2R v) Fv eq_refl) as R'.
destruct (OfPointCore.round_f64_unique _ _ _ _ R R') as [E | (s & s' & _ & Ev)]; [exact E|].
(* Both zeros: impossible, as [v <> 0]. *)
exfalso. subst v. exact (Nv eq_refl).
Qed.

Theorem log2_dir_exact_with :
  forall z, driver_exact z -> driver_exact_zero z ->
  forall x (v : f64) (up : bool),
  is_finite x = true -> log_dom (B2R x) -> is_finite v = true -> Rlog2 (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = zero) ->
  DyadicLog.log2_dir_with z x up = Some v.
Proof.
intros z Hz1 Hz0 x v up Fx Dx Fv H Hz.
(* [x = 2^v], so [v] is an integer [k] ([dle_log_int]), and [x = 2^k]
   is an [f64] only for [-1074 <= k <= 1023] ([f64_pow2]). *)
destruct (dle_log_int 2 ltac:(lra) pow2_rational x v Fx Fv Dx H) as (k & Vk & Xk).
pose proof (f64_pow2 x k Fx Xk) as Rk.
(* No rule of [log_rules] applies, so [log2] is the driver on
   [ev_log2 x], which encloses [k] by the point [k] at every level
   ([ev_log2_exact]). *)
unfold DyadicLog.log2_dir_with. rewrite (log_rules_finite_pos x Fx Dx).
destruct (Z.eq_dec k 0) as [-> | Nk].
- destruct Hz as [Hz | ->]; [contradiction |].
  assert (F : DyadicLog.fast_log2_dir false x up = None).
  { rewrite (dle_one x Fx ltac:(rewrite Xk; reflexivity)). apply fast_log2_one. }
  rewrite F. cbv iota.
  apply Hz0; [lia |]. intros n Hn. exact (ev_log2_exact x 0 n Fx Xk Rk Hn).
- assert (Nv : B2R v <> 0) by (rewrite Vk; apply not_0_IZR; exact Nk).
  destruct (DyadicLog.fast_log2_dir false x up) eqn:F; cbv iota.
  { f_equal. exact (fast_log2_exact x up v _ Fx Dx Fv H Nv F). }
  apply Hz1; [exact Fv | exact Nv | lia |].
  intros n Hn. rewrite Vk. exact (ev_log2_exact x k n Fx Xk Rk Hn).
Qed.

Theorem log2_dir_exact :
  forall x (v : f64) (up : bool),
  is_finite x = true -> log_dom (B2R x) -> is_finite v = true -> Rlog2 (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = zero) ->
  DyadicLog.log2_dir x up = Some v.
Proof.
intros x v up. apply log2_dir_exact_with; [exact ziv_exact | exact ziv_exact_zero].
Qed.

Theorem log10_dir_exact_with :
  forall z x (v : f64) (up : bool),
  is_finite x = true -> log_dom (B2R x) -> is_finite v = true -> Rlog10 (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = zero) ->
  DyadicLog.log10_dir_with z x up = Some v.
Proof.
intros z x v up Fx Dx Fv H Hz.
(* [x = 10^v], so [v] is an integer [k] ([dle_log_int]), and [x = 10^k]
   is an [f64] only for [0 <= k <= 22] ([f64_pow10]). *)
destruct (dle_log_int 10 ltac:(lra) pow10_rational x v Fx Fv Dx H) as (k & Vk & Xk).
pose proof (f64_pow10 x k Fx Xk) as Rk.
unfold DyadicLog.log10_dir_with. rewrite (log_rules_finite_pos x Fx Dx).
destruct (List.find (fun k => Model.eq (DyadicExp.pow10 (Z.of_nat k)) x) (List.seq 0 23))
  as [j |] eqn:Ef.
- (* The rule finds [x = 10^j], so [v = log10 x = j], which [of_u64 j]
     is. *)
  apply find_some in Ef. destruct Ef as [Hin Heq]. apply in_seq in Hin.
  assert (Hj22 : (j <= 22)%nat) by lia.
  destruct (dle_pow10 j Hj22) as [Fp Ep].
  unfold Model.eq in Heq. rewrite Beqb_correct in Heq by assumption.
  destruct (Req_bool_spec (B2R (DyadicExp.pow10 (Z.of_nat j))) (B2R x)) as [Ex | Ex];
    [| discriminate].
  assert (Vj : B2R v = INR j).
  { rewrite <- H, <- Ex, Ep. unfold Rlog10. apply Rlog_pow; lra. }
  assert (Hj : (0 <= Z.of_nat j < 2 ^ 53)%Z) by lia.
  destruct (of_u64_exact (Z.of_nat j) Hj) as (Fj & Ej).
  destruct j as [| j'].
  + (* [j = 0]: [of_u64 0] is [zero]. *)
    destruct Hz as [Hz | ->]; [exfalso; apply Hz; exact Vj | vm_compute; reflexivity].
  + assert (Nj : IZR (Z.of_nat (S j')) <> 0) by (apply not_0_IZR; lia).
    f_equal. apply B2R_inj.
    * apply dle_strict; [exact Fj | rewrite Ej; exact Nj].
    * apply dle_strict; [exact Fv | rewrite Vj, INR_IZR_INZ; exact Nj].
    * rewrite Ej, Vj, INR_IZR_INZ. reflexivity.
- (* The rule finds [x = 10^k] in [0, ..., 22]. *)
  exfalso.
  assert (Hin : In (Z.to_nat k) (List.seq 0 23)) by (apply in_seq; lia).
  pose proof (find_none _ _ Ef _ Hin) as N. cbv beta in N.
  assert (Hk22 : (Z.to_nat k <= 22)%nat) by lia.
  destruct (dle_pow10 (Z.to_nat k) Hk22) as [Fp Ep].
  unfold Model.eq in N. rewrite Beqb_correct in N by assumption.
  destruct (Req_bool_spec (B2R (DyadicExp.pow10 (Z.of_nat (Z.to_nat k)))) (B2R x)) as [_ | Ne];
    [discriminate |].
  apply Ne. rewrite Ep, Xk, pow_powerRZ, Z2Nat.id by lia. reflexivity.
Qed.

Theorem log10_dir_exact :
  forall x (v : f64) (up : bool),
  is_finite x = true -> log_dom (B2R x) -> is_finite v = true -> Rlog10 (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = zero) ->
  DyadicLog.log10_dir x up = Some v.
Proof.
intros x v up. apply log10_dir_exact_with.
Qed.

Theorem asinh_dir_exact_with :
  exp_not_quadratic ->
  forall z x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> arcsinh (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = x) ->
  DyadicLog.asinh_dir_with z x up = Some v.
Proof.
intros HQ z x v up Fx Fv H Hz.
(* [x = sinh v] makes [e^v] a root of [t^2 - 2 x t - 1], so [v = 0]
   ([dle_quad_zero]), and then [x = sinh 0 = 0]. *)
assert (Sx : B2R x = sinh (B2R v)) by (rewrite <- H; symmetry; apply sinh_arcsinh).
assert (V0 : B2R v = 0).
{ apply (dle_quad_zero HQ x v (Z.opp 1) Fx Fv). rewrite opp_IZR.
  rewrite Sx. unfold sinh. rewrite exp_Ropp.
  pose proof (exp_pos (B2R v)). field. lra. }
assert (X0 : B2R x = 0).
{ rewrite Sx, V0. unfold sinh. rewrite Ropp_0, exp_0. field. }
destruct (dte_zero x Fx X0) as (s & ->).
destruct Hz as [Hz | ->]; [contradiction |].
(* [x = ±0]: the rule [toward_zero] returns [x]. *)
destruct s, up; vm_compute; reflexivity.
Qed.

Theorem asinh_dir_exact :
  exp_not_quadratic ->
  forall x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> arcsinh (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = x) ->
  DyadicLog.asinh_dir x up = Some v.
Proof.
intros H x v up. apply asinh_dir_exact_with. exact H.
Qed.

Theorem acosh_dir_exact_with :
  exp_not_quadratic ->
  forall z, driver_exact_zero z ->
  forall x (v : f64) (up : bool),
  is_finite x = true -> acosh_dom (B2R x) -> is_finite v = true -> Racosh (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = zero) ->
  DyadicLog.acosh_dir_with z x up = Some v.
Proof.
intros HQ z Hz0 x v up Fx Dx Fv H Hz.
(* [e^v = x + s] with [s = sqrt (x^2 - 1)] is a root of
   [t^2 - 2 x t + 1], so [v = 0] ([dle_quad_zero]), and then
   [x + s = 1] with [x >= 1] and [s >= 0] gives [x = 1]. *)
unfold acosh_dom in Dx.
set (s := sqrt (B2R x * B2R x - 1)).
assert (Hs : s * s = B2R x * B2R x - 1) by (apply sqrt_sqrt; nra).
assert (S0 : 0 <= s) by apply sqrt_pos.
assert (E : exp (B2R v) = B2R x + s).
{ rewrite <- H. unfold Racosh. fold s. apply exp_ln. lra. }
assert (V0 : B2R v = 0).
{ apply (dle_quad_zero HQ x v 1 Fx Fv). rewrite E. nra. }
assert (X1 : B2R x = 1) by (rewrite V0, exp_0 in E; lra).
rewrite (dle_one x Fx X1).
destruct Hz as [Hz | ->]; [contradiction |].
(* [1 < 1] is false, and the fast path returns [None] at 1
   ([fast_acosh_one]), so [acosh] is the driver on [ev_acosh 1], which
   encloses 0 by the point 0 at every level ([ev_acosh_one]). *)
unfold DyadicLog.acosh_dir_with.
replace (is_nan DyadicExp.one || Model.eq DyadicExp.one infinity) with false
  by (vm_compute; reflexivity).
replace (lt DyadicExp.one DyadicExp.one) with false by (vm_compute; reflexivity).
cbv iota. rewrite fast_acosh_one. cbv iota.
apply Hz0; [lia | exact ev_acosh_one].
Qed.

Theorem acosh_dir_exact :
  exp_not_quadratic ->
  forall x (v : f64) (up : bool),
  is_finite x = true -> acosh_dom (B2R x) -> is_finite v = true -> Racosh (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = zero) ->
  DyadicLog.acosh_dir x up = Some v.
Proof.
intros H x v up. apply acosh_dir_exact_with; [exact H | exact ziv_exact_zero].
Qed.

Theorem atanh_dir_exact_with :
  forall z x (v : f64) (up : bool),
  is_finite x = true -> atanh_dom (B2R x) -> is_finite v = true -> Ratanh (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = x) ->
  DyadicLog.atanh_dir_with z x up = Some v.
Proof.
intros z x v up Fx Dx Fv H Hz.
unfold atanh_dom in Dx.
(* [e^(2 v) = (1 + x) / (1 - x) = (b + a) / (b - a)] for [x = a / b] is
   a rational, so [v = 0] ([dle_exp_zero]), and then [(1 + x) / (1 - x)
   = 1] gives [x = 0]. *)
assert (L : ln ((1 + B2R x) / (1 - B2R x)) = 2 * B2R v) by (rewrite <- H; unfold Ratanh; field).
assert (P : 0 < (1 + B2R x) / (1 - B2R x)) by (apply Rdiv_lt_0_compat; lra).
destruct (f64_rational x Fx) as (a & b & Hb & Ex).
assert (Rb : 0 < IZR b) by (apply IZR_lt; exact Hb).
assert (Hab : (0 < b - a)%Z).
{ assert (Ea : IZR a = B2R x * IZR b) by (rewrite Ex; field; lra).
  apply lt_IZR. rewrite minus_IZR. nra. }
assert (Rab : 0 < IZR b - IZR a) by (rewrite <- minus_IZR; apply IZR_lt; exact Hab).
assert (V0 : B2R v = 0).
{ apply (dle_exp_zero v 2 (b + a) (b - a) Fv ltac:(discriminate) Hab).
  rewrite <- L, exp_ln by exact P.
  rewrite Ex, plus_IZR, minus_IZR. field. lra. }
assert (X0 : B2R x = 0).
{ rewrite V0, Rmult_0_r in L.
  assert (E1 : (1 + B2R x) / (1 - B2R x) = 1) by (rewrite <- (exp_ln _ P), L; apply exp_0).
  assert (M : 1 + B2R x = (1 + B2R x) / (1 - B2R x) * (1 - B2R x)) by (field; lra).
  rewrite E1 in M. lra. }
destruct (dte_zero x Fx X0) as (s & ->).
destruct Hz as [Hz | ->]; [contradiction |].
(* [x = ±0]: the rule [away] returns [x]. *)
destruct s, up; vm_compute; reflexivity.
Qed.

Theorem atanh_dir_exact :
  forall x (v : f64) (up : bool),
  is_finite x = true -> atanh_dom (B2R x) -> is_finite v = true -> Ratanh (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = x) ->
  DyadicLog.atanh_dir x up = Some v.
Proof.
intros x v up. apply atanh_dir_exact_with.
Qed.
