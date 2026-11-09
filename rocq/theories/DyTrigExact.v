(** * The trigonometric functions of the kernel at their exact results

    At a finite [x] whose exact result is an [f64] [v], each of [sin],
    [cos] and [tan] of [DyadicTrig] returns [v], with any driver. The only
    such [x] is [±0]: [cos x], and [cos (2x)], which is [1 - 2 (sin x)^2]
    and [(1 - (tan x)^2) / (1 + (tan x)^2)], are not rationals at a
    rational [x] other than 0 ([cos_irrational]). There, [sin] and [tan]
    return [x], the zero of the same sign, by the rules [toward_zero] and
    [away], and [cos] returns 1 by the rule [near_one]. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary DyRound DyConv DyOps DyDriver DyGrow
  DyExpRules DyExp DyTrig DyExactDriver CosIrrational.

Open Scope R_scope.

(** ** Helpers *)

(** A finite [f64] of value 0 is a zero. *)
Lemma dte_zero : forall x : f64, is_finite x = true -> B2R x = 0 -> exists s, x = B754_zero s.
Proof.
intros x Fx H. destruct x as [s | s | | s m e B]; try discriminate Fx.
- exists s. reflexivity.
- exfalso. pose proof (abs_B2R_ge_emin 53 1024 (B754_finite s m e B) eq_refl) as L.
  rewrite H, Rabs_R0 in L. pose proof (bpow_gt_0 radix2 (SpecFloat.emin 53 1024)). lra.
Qed.

(** A finite [x] at which [cos x], or [cos (2 x)], is a rational is 0, as
    [B2R x] is a rational ([f64_rational], [cos_irrational]). *)
Lemma dte_cos1 :
  forall (x : f64) (a b : Z), is_finite x = true -> (0 < b)%Z ->
  cos (B2R x) = IZR a / IZR b -> B2R x = 0.
Proof.
intros x a b Fx Hb H.
destruct (f64_rational x Fx) as (p & q & Hq & Ex).
destruct (Z.eq_dec p 0) as [-> | Np]; [rewrite Ex; unfold Rdiv; apply Rmult_0_l |].
exfalso. apply (cos_irrational p q a b Hq Np Hb). rewrite <- H, Ex. reflexivity.
Qed.

Lemma dte_cos2 :
  forall (x : f64) (a b : Z), is_finite x = true -> (0 < b)%Z ->
  cos (2 * B2R x) = IZR a / IZR b -> B2R x = 0.
Proof.
intros x a b Fx Hb H.
destruct (f64_rational x Fx) as (p & q & Hq & Ex).
destruct (Z.eq_dec p 0) as [-> | Np]; [rewrite Ex; unfold Rdiv; apply Rmult_0_l |].
exfalso.
assert (N2 : (2 * p <> 0)%Z) by lia.
apply (cos_irrational (2 * p) q a b Hq N2 Hb).
rewrite <- H, Ex, mult_IZR. f_equal. unfold Rdiv. ring.
Qed.

(** [sin x] rational makes [cos (2 x) = 1 - 2 (sin x)^2] rational. *)
Lemma dte_sin_zero :
  forall x v : f64, is_finite x = true -> is_finite v = true -> sin (B2R x) = B2R v -> B2R x = 0.
Proof.
intros x v Fx Fv H.
destruct (f64_rational v Fv) as (a & b & Hb & Ev).
assert (Hbb : (0 < b * b)%Z) by nia.
assert (Rb : IZR b <> 0) by (apply not_0_IZR; lia).
apply (dte_cos2 x (b * b - 2 * a * a) (b * b) Fx Hbb).
rewrite cos_2a_sin, H, Ev, minus_IZR, !mult_IZR. field. exact Rb.
Qed.

(** [tan x = sin x / cos x] rational makes [cos x] zero, which [dte_cos1]
    excludes, or [cos (2 x) = (1 - (tan x)^2) / (1 + (tan x)^2)]
    rational. *)
Lemma dte_tan_zero :
  forall x v : f64, is_finite x = true -> is_finite v = true -> tan (B2R x) = B2R v -> B2R x = 0.
Proof.
intros x v Fx Fv H.
destruct (f64_rational v Fv) as (a & b & Hb & Ev).
rewrite Ev in H. set (X := B2R x) in H |- *.
destruct (Req_dec (cos X) 0) as [C0 | Nc].
{ apply (dte_cos1 x 0 1 Fx ltac:(lia)). fold X. rewrite C0. unfold Rdiv. ring. }
assert (Rb : 0 < IZR b) by (apply IZR_lt; exact Hb).
assert (Hd : (0 < b * b + a * a)%Z) by nia.
assert (Rd : 0 < IZR b * IZR b + IZR a * IZR a)
  by (rewrite <- !mult_IZR, <- plus_IZR; apply IZR_lt; exact Hd).
assert (Hs : sin X = IZR a / IZR b * cos X).
{ unfold tan in H. rewrite <- H. field. exact Nc. }
(* [(cos x)^2 (a^2 + b^2) = b^2], from [(sin x)^2 + (cos x)^2 = 1] *)
assert (PC : cos X * cos X * (IZR a * IZR a + IZR b * IZR b) = IZR b * IZR b).
{ pose proof (sin2_cos2 X) as P. rewrite Hs in P.
  replace (cos X * cos X * (IZR a * IZR a + IZR b * IZR b))
    with (IZR b * IZR b * (Rsqr (IZR a / IZR b * cos X) + Rsqr (cos X))) by (unfold Rsqr; field; lra).
  rewrite P. ring. }
apply (dte_cos2 x (b * b - a * a) (b * b + a * a) Fx Hd). fold X.
rewrite cos_2a, Hs, minus_IZR, plus_IZR, !mult_IZR.
replace (cos X * cos X - IZR a / IZR b * cos X * (IZR a / IZR b * cos X))
  with (cos X * cos X * (IZR a * IZR a + IZR b * IZR b) * (IZR b * IZR b - IZR a * IZR a)
        / (IZR b * IZR b * (IZR b * IZR b + IZR a * IZR a))) by (field; lra).
rewrite PC. field. lra.
Qed.

Theorem sin_dir_exact_with :
  forall z x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> sin (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = x) ->
  DyadicTrig.sin_dir_with z x up = Some v.
Proof.
intros z x v up Fx Fv H Hz.
destruct (dte_zero x Fx (dte_sin_zero x v Fx Fv H)) as (s & ->).
destruct Hz as [Hz | ->]; [exfalso; apply Hz; rewrite <- H; apply sin_0 |].
(* [x = ±0]: the rule [toward_zero] returns [x]. *)
destruct s, up; vm_compute; reflexivity.
Qed.

Theorem sin_dir_exact :
  forall x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> sin (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = x) ->
  DyadicTrig.sin_dir x up = Some v.
Proof.
intros x v up. apply sin_dir_exact_with.
Qed.

Theorem cos_dir_exact_with :
  forall z x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> cos (B2R x) = B2R v ->
  DyadicTrig.cos_dir_with z x up = Some v.
Proof.
intros z x v up Fx Fv H.
assert (X0 : B2R x = 0).
{ destruct (f64_rational v Fv) as (a & b & Hb & Ev).
  apply (dte_cos1 x a b Fx Hb). rewrite H. exact Ev. }
destruct (dte_zero x Fx X0) as (s & ->).
(* [v] is 1, which is [one]: nonzero finite [f64]s are equal where their
   values are. *)
assert (V1 : B2R v = 1) by (rewrite <- H; apply cos_0).
assert (Sv : is_finite_strict v = true).
{ destruct v as [s' | s' | | s' m e B]; try discriminate Fv; [cbn [B2R] in V1; lra | reflexivity]. }
assert (Vo : v = DyadicExp.one).
{ apply B2R_inj; [exact Sv | vm_compute; reflexivity |]. rewrite V1, (proj2 one_B2R). reflexivity. }
subst v.
(* [x = ±0]: the rule [near_one] returns [one]. *)
destruct s, up; vm_compute; reflexivity.
Qed.

Theorem cos_dir_exact :
  forall x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> cos (B2R x) = B2R v ->
  DyadicTrig.cos_dir x up = Some v.
Proof.
intros x v up. apply cos_dir_exact_with.
Qed.

Theorem tan_dir_exact_with :
  forall z x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> tan (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = x) ->
  DyadicTrig.tan_dir_with z x up = Some v.
Proof.
intros z x v up Fx Fv H Hz.
destruct (dte_zero x Fx (dte_tan_zero x v Fx Fv H)) as (s & ->).
destruct Hz as [Hz | ->]; [exfalso; apply Hz; rewrite <- H; apply tan_0 |].
(* [x = ±0]: the rule [away] returns [x]. *)
destruct s, up; vm_compute; reflexivity.
Qed.

Theorem tan_dir_exact :
  forall x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> tan (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = x) ->
  DyadicTrig.tan_dir x up = Some v.
Proof.
intros x v up. apply tan_dir_exact_with.
Qed.
