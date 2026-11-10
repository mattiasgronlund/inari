(** * The inverse trigonometric functions of the kernel at their exact results

    At a finite argument in its domain whose exact result is an [f64]
    [v], each of [atan], [asin], [acos] and [atan2] of [DyadicAtan]
    returns [v]: with any driver for [atan], [asin] and [atan2], whose
    such arguments a rule settles, and with a driver that returns the
    exact point 0 ([driver_exact_zero] of [DyExactDriver.v]) for [acos].
    The only such arguments are these. For a result [s], [cos (2 s)] is
    [(1 - x^2) / (1 + x^2)] for [atan x], [1 - 2 x^2] for [asin x], and
    [(x^2 - y^2) / (x^2 + y^2)] for [atan2(y, x)] ([Ratan2_polar]), and
    [cos s = x] for [acos x]: all rationals, so [s = 0]
    ([cos_irrational]). That is [x = ±0] for [atan] and [asin], which
    return [x], [x = 1] for [acos], where [ev_acos] encloses 0 by the
    point 0 ([ev_acos_one]) and [acos] returns [zero], the [f64] [+0], and
    [y = ±0] with [x > 0] for [atan2], which returns [y]. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary LogReal AtanReal DyRound DyConv DyOps
  DyDriver DyGrow DyConst DyExpCore DyExpRules DyExp ExpReal DyHyp DyHypRules DyLogRules
  DyLogCore DyLog DyLogHyp AtanSeries AtanIdent DyConstPi DyAtanTiny DyAtanCore DyAtan DyAsin
  DyPown DyExactDriver CosIrrational DyTrigExact.

Open Scope R_scope.

(** [ev_acos 1] at level [n] is an enclosure both of whose ends are 0. *)
Definition dae_acos_one_okb (n : nat) : bool :=
  match DyadicAtan.ev_acos DyadicExp.one n with
  | Some a => Dyadic.is_zero n (Dyadic.en_lo a) && Dyadic.is_zero n (Dyadic.en_hi a)
  | None => false
  end.

(** All 64 levels, by computation, as [dc_levels_ok_true] of [DyConst.v]. *)
Lemma dae_acos_one_true : forallb dae_acos_one_okb (seq 1 64) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** [ev_acos] encloses [acos 1 = 0] by the point 0 at every level. *)
Lemma ev_acos_one :
  forall n, level_ok n ->
  exists a, DyadicAtan.ev_acos DyadicExp.one n = Some a /\ encl_ok n a /\
    lo_R a = 0 /\ hi_R a = 0.
Proof.
intros n Hn.
assert (Hin : In n (seq 1 64)) by (apply in_seq; unfold level_ok in Hn; lia).
pose proof (proj1 (forallb_forall dae_acos_one_okb (seq 1 64)) dae_acos_one_true n Hin) as H.
unfold dae_acos_one_okb in H.
destruct (DyadicAtan.ev_acos DyadicExp.one n) as [a|] eqn:Ea; [|discriminate H].
apply andb_prop in H. destruct H as (Zl & Zh).
destruct one_B2R as (F1 & E1).
assert (D1 : -1 <= B2R DyadicExp.one <= 1) by (rewrite E1; lra).
(* [encl_ok] from [ev_acos_correct]; then both ends, being zero, are 0. *)
destruct (ev_acos_correct DyadicExp.one n a Hn F1 D1 Ea) as (Oa & _).
exists a. split; [reflexivity |]. split; [exact Oa |].
destruct Oa as (Ol & Oh & _). unfold lo_R, hi_R. split.
- exact (proj1 (is_zero_correct n _ Hn Ol) Zl).
- exact (proj1 (is_zero_correct n _ Hn Oh) Zh).
Qed.

Theorem atan_dir_exact_with :
  forall z x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> atan (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = x) ->
  DyadicAtan.atan_dir_with z x up = Some v.
Proof.
intros z x v up Fx Fv H Hz.
(* [tan v = x] is a rational, so [v = 0] ([dte_tan_zero]), and then
   [x = tan 0 = 0]. *)
assert (V0 : B2R v = 0).
{ apply (dte_tan_zero v x Fv Fx). rewrite <- H. apply tan_atan. }
assert (X0 : B2R x = 0) by (rewrite <- (tan_atan (B2R x)), H, V0; apply tan_0).
destruct (dte_zero x Fx X0) as (s & ->).
destruct Hz as [Hz | ->]; [contradiction |].
(* [x = ±0]: the rule [toward_zero] returns [x]. *)
destruct s, up; vm_compute; reflexivity.
Qed.

Theorem atan_dir_exact :
  forall x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> atan (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = x) ->
  DyadicAtan.atan_dir x up = Some v.
Proof.
intros x v up. apply atan_dir_exact_with.
Qed.

Theorem asin_dir_exact_with :
  forall z x (v : f64) (up : bool),
  is_finite x = true -> asin_dom (B2R x) -> is_finite v = true -> asin (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = x) ->
  DyadicAtan.asin_dir_with z x up = Some v.
Proof.
intros z x v up Fx Dx Fv H Hz.
(* [sin v = x] is a rational, so [v = 0] ([dte_sin_zero]), and then
   [x = sin 0 = 0]. *)
assert (V0 : B2R v = 0).
{ apply (dte_sin_zero v x Fv Fx). rewrite <- H. apply sin_asin. exact Dx. }
assert (X0 : B2R x = 0) by (rewrite <- (sin_asin (B2R x) Dx), H, V0; apply sin_0).
destruct (dte_zero x Fx X0) as (s & ->).
destruct Hz as [Hz | ->]; [contradiction |].
(* [x = ±0]: the rule [away] returns [x]. *)
destruct s, up; vm_compute; reflexivity.
Qed.

Theorem asin_dir_exact :
  forall x (v : f64) (up : bool),
  is_finite x = true -> asin_dom (B2R x) -> is_finite v = true -> asin (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = x) ->
  DyadicAtan.asin_dir x up = Some v.
Proof.
intros x v up. apply asin_dir_exact_with.
Qed.

Theorem acos_dir_exact_with :
  forall z, driver_exact_zero z ->
  forall x (v : f64) (up : bool),
  is_finite x = true -> acos_dom (B2R x) -> is_finite v = true -> acos (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = zero) ->
  DyadicAtan.acos_dir_with z x up = Some v.
Proof.
intros z Hz0 x v up Fx Dx Fv H Hz.
(* [cos v = x] is a rational, so [v = 0] ([dte_cos1]), and then
   [x = cos 0 = 1]. *)
destruct (f64_rational x Fx) as (a & b & Hb & Ex).
assert (V0 : B2R v = 0).
{ apply (dte_cos1 v a b Fv Hb). rewrite <- H, cos_acos by exact Dx. exact Ex. }
assert (X1 : B2R x = 1) by (rewrite <- (cos_acos (B2R x) Dx), H, V0; apply cos_0).
(* [x] is [one]: nonzero finite [f64]s are equal where their values are. *)
assert (Sx : is_finite_strict x = true).
{ destruct x as [s' | s' | | s' m e B]; try discriminate Fx; [cbn [B2R] in X1; lra | reflexivity]. }
assert (Xo : x = DyadicExp.one).
{ apply B2R_inj; [exact Sx | vm_compute; reflexivity |]. rewrite X1, (proj2 one_B2R). reflexivity. }
subst x.
destruct Hz as [Hz | ->]; [contradiction |].
(* [|1| > 1] is false, so [acos] is the driver on [ev_acos 1], which
   encloses 0 by the point 0 at every level ([ev_acos_one]). *)
unfold DyadicAtan.acos_dir_with.
replace (is_nan DyadicExp.one) with false by (vm_compute; reflexivity).
replace (gt (fabs DyadicExp.one) DyadicExp.one) with false by (vm_compute; reflexivity).
cbv iota.
replace (DyadicAtan.fast_acos_dir false DyadicExp.one up) with (@None f64)
  by (destruct up; vm_compute; reflexivity).
cbv iota.
apply Hz0; [lia | exact ev_acos_one].
Qed.

Theorem acos_dir_exact :
  forall x (v : f64) (up : bool),
  is_finite x = true -> acos_dom (B2R x) -> is_finite v = true -> acos (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = zero) ->
  DyadicAtan.acos_dir x up = Some v.
Proof.
intros x v up. apply acos_dir_exact_with. exact ziv_exact_zero.
Qed.

Theorem atan2_dir_exact_with :
  forall z y x (v : f64) (up : bool),
  is_finite y = true -> is_finite x = true -> atan2_dom (B2R y) (B2R x) ->
  is_finite v = true -> Ratan2 (B2R y) (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = y) ->
  DyadicAtan.atan2_dir_with z y x up = Some v.
Proof.
intros z y x v up Fy Fx D Fv H Hz.
destruct (f64_rational y Fy) as (a & b & Hb & Ey).
destruct (f64_rational x Fx) as (c & d & Hd & Ex).
(* [x = r cos v] and [y = r sin v] with [r = sqrt (y^2 + x^2) > 0]. *)
destruct (Ratan2_polar (B2R y) (B2R x) D) as (Px & Py).
rewrite H in Px, Py.
assert (Pd : 0 < B2R y * B2R y + B2R x * B2R x).
{ destruct D as [D | D]; pose proof (Rsqr_pos_lt _ D); unfold Rsqr in *; nra. }
(* [cos (2 v) = (x^2 - y^2) / (x^2 + y^2)] is a rational, so [v = 0]
   ([dte_cos2]). *)
assert (V0 : B2R v = 0).
{ assert (R2 : sqrt (B2R y * B2R y + B2R x * B2R x) * sqrt (B2R y * B2R y + B2R x * B2R x)
               = B2R y * B2R y + B2R x * B2R x) by (apply sqrt_sqrt; lra).
  revert Px Py R2.
  generalize (sqrt (B2R y * B2R y + B2R x * B2R x)) as r. intros r Px Py R2.
  assert (Nr : r <> 0) by (intro E; rewrite E in R2; lra).
  assert (Rb : 0 < IZR b) by (apply IZR_lt; exact Hb).
  assert (Rd : 0 < IZR d) by (apply IZR_lt; exact Hd).
  (* [c^2 b^2 + a^2 d^2 = (b d)^2 (y^2 + x^2) > 0] *)
  assert (Q : IZR (c * c * b * b + a * a * d * d)
              = (IZR b * IZR d) * (IZR b * IZR d) * (B2R y * B2R y + B2R x * B2R x)).
  { rewrite plus_IZR, !mult_IZR, Ey, Ex. field. lra. }
  assert (Hn : (0 < c * c * b * b + a * a * d * d)%Z).
  { apply lt_IZR. rewrite Q. apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; apply Rmult_lt_0_compat; lra | exact Pd]. }
  apply (dte_cos2 v (c * c * b * b - a * a * d * d) _ Fv Hn).
  rewrite Q, minus_IZR, !mult_IZR, cos_2a.
  replace (cos (B2R v) * cos (B2R v) - sin (B2R v) * sin (B2R v))
    with (((r * cos (B2R v)) * (r * cos (B2R v)) - (r * sin (B2R v)) * (r * sin (B2R v)))
          / (r * r)) by (field; exact Nr).
  rewrite <- Px, <- Py, R2.
  replace (IZR c * IZR c * IZR b * IZR b - IZR a * IZR a * IZR d * IZR d)
    with ((IZR b * IZR d) * (IZR b * IZR d) * (B2R x * B2R x - B2R y * B2R y))
    by (rewrite Ey, Ex; field; lra).
  field. repeat split; lra. }
(* So [y = r sin 0 = 0] and [x = r cos 0 = r > 0]. *)
rewrite V0, sin_0, Rmult_0_r in Py.
rewrite V0, cos_0, Rmult_1_r in Px.
assert (Xp : 0 < B2R x) by (rewrite Px; apply sqrt_lt_R0; exact Pd).
destruct (dte_zero y Fy Py) as (s & ->).
destruct Hz as [Hz | ->]; [contradiction |].
assert (Sx : Bsign x = false)
  by (destruct (Bsign x) eqn:S; [apply atn_sign_true in S; lra | reflexivity]).
(* [y = ±0] and [x > 0]: the rule for [y = 0] returns [y]. *)
unfold DyadicAtan.atan2_dir_with.
rewrite (fin_not_nan x Fx), Sx.
destruct s; vm_compute; reflexivity.
Qed.

Theorem atan2_dir_exact :
  forall y x (v : f64) (up : bool),
  is_finite y = true -> is_finite x = true -> atan2_dom (B2R y) (B2R x) ->
  is_finite v = true -> Ratan2 (B2R y) (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = y) ->
  DyadicAtan.atan2_dir y x up = Some v.
Proof.
intros y x v up. apply atan2_dir_exact_with.
Qed.
