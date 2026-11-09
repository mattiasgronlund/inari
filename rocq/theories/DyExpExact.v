(** * The exponentials and hyperbolic functions of the kernel at their exact results

    At a finite [x] whose exact result is an [f64] [v], each of [exp],
    [exp2], [exp10], [sinh], [cosh] and [tanh] of [DyadicExp] returns [v],
    with any driver for those whose exact results are all settled by a
    rule, and with a driver that returns exact points ([driver_exact] of
    [DyPown.v]) for [exp2]. The only such arguments are these. [e^x] and
    [tanh x] are not rationals at a rational [x] other than 0
    ([exp_irrational]; [e^(2x) = (1 + t) / (1 - t)] for [t = tanh x]),
    nor are [sinh x] and [cosh x] under [exp_not_quadratic] (below), so
    [x] is [±0], which the rules [near_one], [away] and [toward_zero]
    settle. [2^x] and [10^x] are rationals only at an integer [x]
    ([pow2_rational], [pow10_rational]), [2^m] is an [f64] for
    [-1074 <= m <= 1023] and [10^m] for [0 <= m <= 22] ([f64_pow2],
    [f64_pow10]). At such an integer [m <> 0], [ev_exp2] encloses [2^m]
    by the point [2^m] at every level, as [(m - x) ln 2 = 0] there, and
    the driver returns it ([ev_exp2_exact] of [DyExpPoint.v]); [exp10]
    returns [10^m] by its rule for [1 <= m <= 22]. [sinh x] and [cosh x]
    at a rational [x] other than 0 are rationals only if [e^x] is a root
    of a quadratic with rational coefficients, [(e^x)^2 - 2 s e^x -+ 1 = 0]
    for [s = sinh x] or [cosh x], which the hypothesis [exp_not_quadratic]
    of [ExpQuadratic.v] excludes. Where the result is 0, which is only
    [sinh] and [tanh] at [x = ±0], they return [x], the zero of the same
    sign. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary ExpReal DyRound DyConv DyOps DyDriver
  DyGrow DyExpCore DyExpRules DyHypRules DyExp DyHyp DyPown DyExactDriver PowFactor
  ExpIrrational ExpQuadratic DyTrigExact DyExpPoint.

Open Scope R_scope.

(** ** Helpers *)

(** [B2R l] for a literal [l], as in [DyHypRules.v]: [B2SF l] computes to
    its sign, significand and exponent. *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** A finite [f64] of value 1 is [one]: nonzero finite [f64]s are equal
    where their values are. *)
Lemma dxe_one : forall v : f64, is_finite v = true -> B2R v = 1 -> v = DyadicExp.one.
Proof.
intros v Fv V1.
assert (Sv : is_finite_strict v = true).
{ destruct v as [s | s | | s m e B]; try discriminate Fv; [cbn [B2R] in V1; lra | reflexivity]. }
apply B2R_inj; [exact Sv | vm_compute; reflexivity |]. rewrite V1, (proj2 one_B2R). reflexivity.
Qed.

(** A finite [x] at which [e^(k x)], for an integer [k <> 0], is a
    rational is 0, as [B2R x] is a rational ([f64_rational],
    [exp_irrational]). *)
Lemma dxe_exp_zero :
  forall (x : f64) (k a b : Z), is_finite x = true -> k <> 0%Z -> (0 < b)%Z ->
  exp (IZR k * B2R x) = IZR a / IZR b -> B2R x = 0.
Proof.
intros x k a b Fx Nk Hb H.
destruct (f64_rational x Fx) as (p & q & Hq & Ex).
destruct (Z.eq_dec p 0) as [-> | Np]; [rewrite Ex; unfold Rdiv; apply Rmult_0_l |].
exfalso.
assert (Nkp : (k * p <> 0)%Z) by (intros E; apply Z.mul_eq_0 in E; lia).
apply (exp_irrational (k * p) q a b Hq Nkp Hb).
rewrite <- H, Ex, mult_IZR. f_equal. unfold Rdiv. ring.
Qed.

(** [sinh x] or [cosh x] rational, [a / b], makes [e = e^x] a root of
    [b t^2 - 2 a t -+ b], as [e^(-x) = 1 / e], which
    [exp_not_quadratic] excludes at a rational [x] other than 0. The
    lemma takes any integer [c] for the sign [-+]. *)
Lemma dxe_hyp_zero :
  exp_not_quadratic ->
  forall (x : f64) (c a b : Z), is_finite x = true -> (0 < b)%Z ->
  (exp (B2R x) + IZR c * exp (- B2R x)) / 2 = IZR a / IZR b -> B2R x = 0.
Proof.
intros HQ x c a b Fx Hb H.
destruct (f64_rational x Fx) as (p & q & Hq & Ex).
destruct (Z.eq_dec p 0) as [-> | Np]; [rewrite Ex; unfold Rdiv; apply Rmult_0_l |].
exfalso.
assert (N : (b <> 0 \/ - 2 * a <> 0 \/ c * b <> 0)%Z) by lia.
apply (HQ p q Hq Np b (- 2 * a)%Z (c * b)%Z N). rewrite <- Ex.
assert (Pe : 0 < exp (B2R x)) by apply exp_pos.
assert (Rb : 0 < IZR b) by (apply IZR_lt; exact Hb).
rewrite exp_Ropp in H. set (e := exp (B2R x)) in H, Pe |- *.
assert (Ea : IZR a = IZR b * ((e + IZR c * / e) / 2)) by (rewrite H; field; lra).
rewrite !mult_IZR, Ea. field. lra.
Qed.

Theorem exp_dir_exact_with :
  forall z x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> exp (B2R x) = B2R v ->
  DyadicExp.exp_dir_with z x up = Some v.
Proof.
intros z x v up Fx Fv H.
assert (X0 : B2R x = 0).
{ destruct (f64_rational v Fv) as (a & b & Hb & Ev).
  apply (dxe_exp_zero x 1 a b Fx ltac:(lia) Hb). rewrite Rmult_1_l, H. exact Ev. }
destruct (dte_zero x Fx X0) as (s & ->).
assert (Vo : v = DyadicExp.one) by (apply dxe_one; [exact Fv | rewrite <- H; apply exp_0]).
subst v.
(* [x = ±0]: the rule [near_one] returns [one]. *)
destruct s, up; vm_compute; reflexivity.
Qed.

Theorem exp_dir_exact :
  forall x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> exp (B2R x) = B2R v ->
  DyadicExp.exp_dir x up = Some v.
Proof.
intros x v up. apply exp_dir_exact_with.
Qed.

Theorem exp2_dir_exact_with :
  forall z, driver_exact z ->
  forall x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> Rexp2 (B2R x) = B2R v ->
  DyadicExp.exp2_dir_with z x up = Some v.
Proof.
intros z Hz x v up Fx Fv H. unfold driver_exact in Hz.
destruct (f64_rational v Fv) as (a & b & Hb & Ev).
destruct (f64_rational x Fx) as (p & q & Hq & Ex).
(* [x] is an integer [m] ([pow2_rational]), and [v = 2^m] *)
assert (Hd : (q | p)%Z).
{ apply (pow2_rational p q a b Hq Hb). rewrite <- Ex, <- Ev. exact H. }
destruct Hd as (m & ->).
assert (Rq : IZR q <> 0) by (apply not_0_IZR; lia).
assert (Xm : B2R x = IZR m) by (rewrite Ex, mult_IZR; field; exact Rq).
assert (Vm : B2R v = powerRZ 2 m).
{ rewrite <- H. unfold Rexp2. rewrite Xm, powerRZ_Rpower by lra. reflexivity. }
pose proof (f64_pow2 v m Fv Vm) as Hr.
destruct (Z.eq_dec m 0) as [-> | Nm].
{ (* [x = ±0]: the rule [near_one] returns [one]. *)
  destruct (dte_zero x Fx Xm) as (s & ->).
  assert (Vo : v = DyadicExp.one) by (apply dxe_one; [exact Fv | rewrite Vm; reflexivity]).
  subst v. destruct s, up; vm_compute; reflexivity. }
(* [1 <= |m|]: no rule applies, and [ev_exp2] encloses [2^m] by a point. *)
assert (Am : 1 <= Rabs (IZR m)) by (rewrite <- abs_IZR; apply IZR_le; lia).
unfold DyadicExp.exp2_dir_with.
rewrite (fin_not_nan x Fx), (fin_neq_inf x Fx), (fin_neq_ninf x Fx). cbn [orb].
assert (G1 : ge x (from_bits 0x4090000000000000) = false).
{ destruct (ge x _) eqn:G; [exfalso | reflexivity].
  apply ge_R in G; [| exact Fx | vm_compute; reflexivity].
  assert (L : B2R (from_bits 0x4090000000000000) = 1024)
    by (lit_B2R; cbn [bpow radix_val radix2]; lra).
  rewrite L, Xm in G. apply le_IZR in G. lia. }
assert (G2 : lt x (from_bits 0xc090cc0000000000) = false).
{ destruct (lt x _) eqn:G; [exfalso | reflexivity].
  apply lt_R in G; [| exact Fx | vm_compute; reflexivity].
  assert (L : B2R (from_bits 0xc090cc0000000000) = -1075)
    by (lit_B2R; cbn [bpow radix_val radix2]; lra).
  rewrite L, Xm in G. apply lt_IZR in G. lia. }
assert (G3 : lt (fabs x) DyadicExp.tiny_exp = false).
{ destruct (lt (fabs x) _) eqn:G; [exfalso | reflexivity].
  apply fabs_lt_R in G; [| exact Fx | vm_compute; reflexivity].
  assert (L : B2R DyadicExp.tiny_exp = bpow radix2 (-54)).
  { lit_B2R. change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
    reflexivity. }
  assert (L1 : bpow radix2 (-54) < 1) by (cbn [bpow radix_val radix2]; lra).
  rewrite Xm in G. lra. }
rewrite G1, G2, G3.
apply Hz; [exact Fv | rewrite Vm; apply powerRZ_NOR; lra | lia |].
intros n Hn. rewrite Vm. exact (ev_exp2_exact x m n Fx Xm Nm Hr Hn).
Qed.

Theorem exp2_dir_exact :
  forall x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> Rexp2 (B2R x) = B2R v ->
  DyadicExp.exp2_dir x up = Some v.
Proof.
intros x v up. apply exp2_dir_exact_with. exact ziv_exact.
Qed.

Theorem exp10_dir_exact_with :
  forall z x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> Rexp10 (B2R x) = B2R v ->
  DyadicExp.exp10_dir_with z x up = Some v.
Proof.
intros z x v up Fx Fv H.
destruct (f64_rational v Fv) as (a & b & Hb & Ev).
destruct (f64_rational x Fx) as (p & q & Hq & Ex).
(* [x] is an integer [m] ([pow10_rational]), and [v = 10^m] *)
assert (Hd : (q | p)%Z).
{ apply (pow10_rational p q a b Hq Hb). rewrite <- Ex, <- Ev. exact H. }
destruct Hd as (m & ->).
assert (Rq : IZR q <> 0) by (apply not_0_IZR; lia).
assert (Xm : B2R x = IZR m) by (rewrite Ex, mult_IZR; field; exact Rq).
assert (Vm : B2R v = powerRZ 10 m).
{ rewrite <- H. unfold Rexp10. rewrite Xm, powerRZ_Rpower by lra. reflexivity. }
pose proof (f64_pow10 v m Fv Vm) as Hr.
destruct (Z.eq_dec m 0) as [-> | Nm].
{ (* [x = ±0]: the rule [near_one] returns [one]. *)
  destruct (dte_zero x Fx Xm) as (s & ->).
  assert (Vo : v = DyadicExp.one) by (apply dxe_one; [exact Fv | rewrite Vm; reflexivity]).
  subst v. destruct s, up; vm_compute; reflexivity. }
(* [1 <= m <= 22]: the rule for the integers from 1 to 22 returns [10^m]. *)
assert (L22 : B2R (from_bits 0x4036000000000000) = 22)
  by (lit_B2R; cbn [bpow radix_val radix2]; lra).
unfold DyadicExp.exp10_dir_with.
rewrite (fin_not_nan x Fx), (fin_neq_inf x Fx), (fin_neq_ninf x Fx). cbn [orb].
assert (G1 : ge x (from_bits 0x4073500000000000) = false).
{ destruct (ge x _) eqn:G; [exfalso | reflexivity].
  apply ge_R in G; [| exact Fx | vm_compute; reflexivity].
  assert (L : B2R (from_bits 0x4073500000000000) = 309)
    by (lit_B2R; cbn [bpow radix_val radix2]; lra).
  rewrite L, Xm in G. apply le_IZR in G. lia. }
assert (G2 : le x (from_bits 0xc074400000000000) = false).
{ destruct (le x _) eqn:G; [exfalso | reflexivity].
  apply le_R in G; [| exact Fx | vm_compute; reflexivity].
  assert (L : B2R (from_bits 0xc074400000000000) = -324)
    by (lit_B2R; cbn [bpow radix_val radix2]; lra).
  rewrite L, Xm in G. apply le_IZR in G. lia. }
assert (G3 : lt (fabs x) DyadicExp.tiny_exp10 = false).
{ destruct (lt (fabs x) _) eqn:G; [exfalso | reflexivity].
  apply fabs_lt_R in G; [| exact Fx | vm_compute; reflexivity].
  assert (L : B2R DyadicExp.tiny_exp10 = bpow radix2 (-56)).
  { lit_B2R. change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
    reflexivity. }
  assert (L1 : bpow radix2 (-56) < 1) by (cbn [bpow radix_val radix2]; lra).
  assert (Am : 1 <= Rabs (IZR m)) by (rewrite <- abs_IZR; apply IZR_le; lia).
  rewrite Xm in G. lra. }
assert (G4 : le DyadicExp.one x && le x (from_bits 0x4036000000000000) && eq x (ffloor x) = true).
{ unfold le, eq, ffloor.
  destruct (Bnearbyint_correct 53 1024 _ mode_DN x) as (Ef & Ff & _).
  rewrite !Bleb_correct, Beqb_correct; try (exact Fx || (rewrite Ff; exact Fx) ||
    (vm_compute; reflexivity)).
  rewrite Ef, round_FIX_IZR, Xm, (proj2 one_B2R), L22.
  change (round_mode mode_DN) with Zfloor. rewrite Zfloor_IZR.
  rewrite Rle_bool_true, Rle_bool_true, Req_bool_true by (reflexivity || (apply IZR_le; lia)).
  reflexivity. }
rewrite G1, G2, G3, G4. f_equal.
(* [to_i64 x] is [m]: [Btrunc x] is [trunc m = m]. *)
assert (Ht : DyadicExp.to_i64 x = m).
{ assert (Et : IZR (Btrunc x) = IZR m)
    by (rewrite Btrunc_correct, round_FIX_IZR, Xm, Ztrunc_IZR; reflexivity).
  apply eq_IZR in Et.
  destruct x as [s|s| |s mx e B]; try discriminate Fx.
  - cbn [B2R] in Xm. apply eq_IZR in Xm. lia.
  - cbn [DyadicExp.to_i64]. rewrite Et. lia. }
rewrite Ht.
assert (Hm : (1 <= m <= 22)%Z) by lia.
destruct (pow10_exact m Hm) as [Fp Ep].
assert (Pm : powerRZ 10 m = IZR (10 ^ m)).
{ destruct m as [| mp | mp]; [lia | apply dxd_powerRZ_pos | lia]. }
assert (Pv : 0 < IZR (10 ^ m)) by (apply IZR_lt, Z.pow_pos_nonneg; lia).
apply B2R_inj.
- destruct (DyadicExp.pow10 m) as [s | s | | s mx e B]; try discriminate Fp;
    [cbn [B2R] in Ep; lra | reflexivity].
- destruct v as [s | s | | s mx e B]; try discriminate Fv;
    [cbn [B2R] in Vm; lra | reflexivity].
- rewrite Ep, Vm, Pm. reflexivity.
Qed.

Theorem exp10_dir_exact :
  forall x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> Rexp10 (B2R x) = B2R v ->
  DyadicExp.exp10_dir x up = Some v.
Proof.
intros x v up. apply exp10_dir_exact_with.
Qed.

Theorem sinh_dir_exact_with :
  exp_not_quadratic ->
  forall z x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> sinh (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = x) ->
  DyadicExp.sinh_dir_with z x up = Some v.
Proof.
intros HQ z x v up Fx Fv H Hz.
assert (X0 : B2R x = 0).
{ destruct (f64_rational v Fv) as (a & b & Hb & Ev).
  apply (dxe_hyp_zero HQ x (-1) a b Fx Hb). rewrite <- Ev, <- H. unfold sinh, Rdiv. ring. }
destruct (dte_zero x Fx X0) as (s & ->).
destruct Hz as [Hz | ->].
{ exfalso. apply Hz. rewrite <- H. cbn [B2R]. unfold sinh. rewrite Ropp_0, exp_0. field. }
(* [x = ±0]: the rule [away] returns [x]. *)
destruct s, up; vm_compute; reflexivity.
Qed.

Theorem sinh_dir_exact :
  exp_not_quadratic ->
  forall x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> sinh (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = x) ->
  DyadicExp.sinh_dir x up = Some v.
Proof.
intros H x v up. apply sinh_dir_exact_with. exact H.
Qed.

Theorem cosh_dir_exact_with :
  exp_not_quadratic ->
  forall z x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> cosh (B2R x) = B2R v ->
  DyadicExp.cosh_dir_with z x up = Some v.
Proof.
intros HQ z x v up Fx Fv H.
assert (X0 : B2R x = 0).
{ destruct (f64_rational v Fv) as (a & b & Hb & Ev).
  apply (dxe_hyp_zero HQ x 1 a b Fx Hb). rewrite <- Ev, <- H. unfold cosh, Rdiv. ring. }
destruct (dte_zero x Fx X0) as (s & ->).
assert (Vo : v = DyadicExp.one).
{ apply dxe_one; [exact Fv |]. rewrite <- H. cbn [B2R]. unfold cosh.
  rewrite Ropp_0, exp_0. field. }
subst v.
(* [x = ±0]: the rule [near_one] returns [one] at [|x| = +0]. *)
destruct s, up; vm_compute; reflexivity.
Qed.

Theorem cosh_dir_exact :
  exp_not_quadratic ->
  forall x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> cosh (B2R x) = B2R v ->
  DyadicExp.cosh_dir x up = Some v.
Proof.
intros H x v up. apply cosh_dir_exact_with. exact H.
Qed.

Theorem tanh_dir_exact_with :
  forall z x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> tanh (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = x) ->
  DyadicExp.tanh_dir_with z x up = Some v.
Proof.
intros z x v up Fx Fv H Hz.
assert (X0 : B2R x = 0).
{ destruct (f64_rational v Fv) as (a & b & Hb & Ev).
  set (X := B2R x) in H |- *.
  assert (Pe : 0 < exp X) by apply exp_pos.
  assert (Rb : 0 < IZR b) by (apply IZR_lt; exact Hb).
  assert (E2 : exp (IZR 2 * X) = exp X * exp X) by (rewrite <- exp_plus; f_equal; ring).
  (* [(b - a) e^(2x) = a + b], as [tanh x = (e^(2x) - 1) / (e^(2x) + 1)] *)
  assert (Q : (IZR b - IZR a) * (exp X * exp X) = IZR a + IZR b).
  { unfold tanh, sinh, cosh in H. rewrite exp_Ropp, Ev in H.
    assert (Ea : IZR a = IZR b * ((exp X - / exp X) / 2 / ((exp X + / exp X) / 2))).
    { rewrite H. field. lra. }
    rewrite Ea. field. split; [lra | nra]. }
  destruct (Z.lt_trichotomy (b - a) 0) as [Hn | [He | Hp]].
  - (* [e^(2x) = (- (a + b)) / (a - b)] *)
    apply (dxe_exp_zero x 2 (- (a + b)) (a - b) Fx ltac:(lia) ltac:(lia)).
    assert (Rd : 0 < IZR (a - b)) by (apply IZR_lt; lia).
    rewrite minus_IZR in Rd. fold X. rewrite E2, opp_IZR, plus_IZR, minus_IZR.
    apply (Rmult_eq_reg_l (IZR b - IZR a)); [| lra]. rewrite Q. field. lra.
  - (* [b = a] makes [a + b = 2 b = 0] *)
    exfalso. assert (Ea : IZR b = IZR a) by (apply IZR_eq; lia).
    rewrite Ea in Q. replace (IZR a - IZR a) with 0 in Q by ring. lra.
  - (* [e^(2x) = (a + b) / (b - a)] *)
    apply (dxe_exp_zero x 2 (a + b) (b - a) Fx ltac:(lia) Hp).
    assert (Rd : 0 < IZR (b - a)) by (apply IZR_lt; lia).
    rewrite minus_IZR in Rd. fold X. rewrite E2, plus_IZR, minus_IZR.
    apply (Rmult_eq_reg_l (IZR b - IZR a)); [| lra]. rewrite Q. field. lra. }
destruct (dte_zero x Fx X0) as (s & ->).
destruct Hz as [Hz | ->].
{ exfalso. apply Hz. rewrite <- H. cbn [B2R]. unfold tanh, sinh, cosh.
  rewrite Ropp_0, exp_0. field. }
(* [x = ±0]: the rule [toward_zero] returns [x]. *)
destruct s, up; vm_compute; reflexivity.
Qed.

Theorem tanh_dir_exact :
  forall x (v : f64) (up : bool),
  is_finite x = true -> is_finite v = true -> tanh (B2R x) = B2R v ->
  (B2R v <> 0 \/ v = x) ->
  DyadicExp.tanh_dir x up = Some v.
Proof.
intros x v up. apply tanh_dir_exact_with.
Qed.
