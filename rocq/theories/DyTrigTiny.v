(** * The rules before Ziv's strategy for [sin], [cos] and [tan] of tiny arguments

    The branches of [sin_dir], [cos_dir] and [tan_dir] of [DyadicTrig] in
    [Model.v] for [|x| < 2^-26]. [sin x] is [x] if [x] is 0, and
    otherwise lies strictly between [x] and the next [f64] toward zero,
    which [toward_zero x up] returns when [up] rounds toward zero, as
    [atan x] does in [DyAtanTiny.v]. [tan x] is [x] if [x] is 0, and
    otherwise lies strictly between [x] and the next [f64] away from zero,
    which [away x up] returns when [up] rounds away from zero, as [asin x]
    does there. [cos x] is 1 if [x] is 0, and otherwise lies strictly
    between [1 - 2^-53] and 1, which [near_one (-|x|) up] rounds, as
    [cosh_tiny_rule] of [DyHypRules.v] does on the other side of 1. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Elementary ExpReal ConstLn Encoding IdealGetD OfPointCore
  MpfrRound MpfrIdeal ExpSeries AtanhSeries DyExpRules DyHypRules DySinhTiny DyTanhTiny
  DyLogRules DyLogTiny AtanSeries DyAtanTiny DyRound DyOps DyConv.

Open Scope R_scope.

Local Notation rnd_of up := (if up then RNDU else RNDD).

(** The format of the finite [f64]s without the bound above, as in
    [DyTanhTiny.v]. *)
Local Notation G := (generic_format radix2 (SpecFloat.fexp 53 1024)).
Local Notation succ64 := (succ radix2 (SpecFloat.fexp 53 1024)).

(** ** The series bounds *)

(** For [0 <= a <= π], [a - a^3/6 <= sin a <= a - a^3/6 + a^5/120]: the
    sums of the first two and three terms of the series of [sin]
    ([sin_bound] with [n = 0]). *)
Lemma sin_bounds_3 :
  forall a, 0 <= a -> a <= PI -> a - a ^ 3 / 6 <= sin a <= a - a ^ 3 / 6 + a ^ 5 / 120.
Proof.
intros a H0 Hp. destruct (sin_bound a 0 H0 Hp) as [H1 H2].
replace (sin_approx a (2 * 0 + 1)) with (a - a ^ 3 / 6) in H1
  by (unfold sin_approx, sin_term; simpl; field).
replace (sin_approx a (2 * (0 + 1))) with (a - a ^ 3 / 6 + a ^ 5 / 120) in H2
  by (unfold sin_approx, sin_term; simpl; field).
split; assumption.
Qed.

(** For [|a| <= π/2], [1 - a^2/2 <= cos a <= 1 - a^2/2 + a^4/24]: the sums
    of the first two and three terms of the series of [cos] ([cos_bound]
    with [n = 0]). *)
Lemma cos_bounds_3 :
  forall a, - PI / 2 <= a -> a <= PI / 2 -> 1 - a ^ 2 / 2 <= cos a <= 1 - a ^ 2 / 2 + a ^ 4 / 24.
Proof.
intros a H0 Hp. destruct (cos_bound a 0 H0 Hp) as [H1 H2].
replace (cos_approx a (2 * 0 + 1)) with (1 - a ^ 2 / 2) in H1
  by (unfold cos_approx, cos_term; simpl; field).
replace (cos_approx a (2 * (0 + 1))) with (1 - a ^ 2 / 2 + a ^ 4 / 24) in H2
  by (unfold cos_approx, cos_term; simpl; field).
split; assumption.
Qed.

(** [0 < w < 2^-26] puts [w] in the range of [sin_bounds_3] and
    [cos_bounds_3], as [2^-26 < 1 < π/2] ([PI2_1]), and makes [w^2] less
    than [2^-52]. *)
Lemma tiny_range :
  forall w, 0 < w < bpow radix2 (-26) ->
  0 <= w /\ w <= PI /\ - PI / 2 <= w /\ w <= PI / 2 /\ w * w < 1 / 4503599627370496.
Proof.
intros w Hw.
assert (Hb : bpow radix2 (-26) = 1 / 67108864) by (cbn [bpow radix_val radix2]; lra).
rewrite Hb in Hw. pose proof PI2_1 as HP.
assert (Hww : w * w < 1 / 4503599627370496).
{ replace (1 / 4503599627370496) with (1 / 67108864 * (1 / 67108864)) by field.
  apply Rmult_le_0_lt_compat; lra. }
repeat split; lra.
Qed.

(** ** [sin] *)

(** If [w = succ p] with [0 <= p] and [w < 2^-26], [sin w] lies strictly
    between [p] and [w]: [sin w < w] ([sin_lt_x]), and [w - w^3/6 <=
    sin w] ([sin_bounds_3]) where [w^3/6 < w 2^-52 / 6] is less than
    [ulp p = w - p], which is more than [p 2^-53]. *)
Lemma sin_tiny_between :
  forall p, 0 <= p -> succ64 p < bpow radix2 (-26) -> p < sin (succ64 p) < succ64 p.
Proof.
intros p Hp Hw.
assert (P53 : Prec_gt_0 53) by (unfold Prec_gt_0; lia).
pose proof (ulp_FLT_gt radix2 (-1074) 53 p) as Hu.
change (Rabs p * bpow radix2 (-53) < ulp radix2 (SpecFloat.fexp 53 1024) p) in Hu.
rewrite Rabs_pos_eq in Hu by exact Hp.
assert (Hs : succ64 p = p + ulp radix2 (SpecFloat.fexp 53 1024) p)
  by (apply succ_eq_pos; exact Hp).
assert (He : 0 < bpow radix2 (-53)) by apply bpow_gt_0.
assert (Hpw : p < succ64 p) by nra.
set (w := succ64 p) in *.
set (u := ulp radix2 (SpecFloat.fexp 53 1024) p) in *.
assert (Hb53 : bpow radix2 (-53) = 1 / 9007199254740992) by (cbn [bpow radix_val radix2]; lra).
rewrite Hb53 in Hu.
destruct (tiny_range w ltac:(lra)) as (R0 & RP & _ & _ & Hww).
destruct (sin_bounds_3 w R0 RP) as [H1 _].
pose proof (sin_lt_x w ltac:(lra)) as H2.
assert (H3 : w ^ 3 < w * (1 / 4503599627370496)).
{ replace (w ^ 3) with (w * (w * w)) by ring. apply Rmult_lt_compat_l; lra. }
split; lra.
Qed.

Lemma sin_tiny_rule :
  forall x (up : bool),
  is_finite x = true -> lt (fabs x) DyadicExp.tiny_hyp = true ->
  mpfr_round f64_format (rnd_of up) (sin (B2R x)) (with_val (DyadicExp.toward_zero x up)).
Proof.
intros x up Fx Ht.
assert (Fth : is_finite DyadicExp.tiny_hyp = true) by (vm_compute; reflexivity).
pose proof (fabs_lt_R x _ Fx Fth Ht) as Hy. rewrite hyp_lit_tiny in Hy.
assert (Fz : is_finite zero = true) by reflexivity.
unfold DyadicExp.toward_zero, eq, gt.
rewrite Beqb_correct by assumption. rewrite Bltb_correct by assumption.
assert (Ez : B2R zero = 0) by reflexivity. rewrite Ez.
destruct (Req_bool_spec (B2R x) 0) as [Hx|Hx]; cbn [orb].
{ (* [sin 0 = 0]. *)
  apply rnd_exact; [exact Fx|]. rewrite Hx, sin_0. reflexivity. }
destruct (toward_zero_bits x Fx Hx) as (p & Hp & Gp & Fb & Ex & Eb).
set (b := from_bits (to_bits x - 1)) in *.
assert (Hsp : 0 <= succ64 p) by (eapply Rle_trans; [exact Hp | apply succ_ge_id]).
revert Ex Eb. destruct (Bsign x); intros Ex Eb.
- (* [x = - succ p < 0]: [x] is below [sin x], and [b = -p] is the next
     [f64] above [x]. *)
  assert (Hw : succ64 p < bpow radix2 (-26))
    by (rewrite Ex, Rabs_Ropp, Rabs_pos_eq in Hy by exact Hsp; exact Hy).
  destruct (sin_tiny_between p Hp Hw) as [H1 H2].
  rewrite (Rlt_bool_false 0 (B2R x)) by (rewrite Ex; lra).
  destruct up; cbn [Bool.eqb].
  + apply (rnd_bracket x b true); [exact Fx | exact Fb | |].
    * rewrite Eb, Ex, succ_opp, pred_succ by first [exact Gp | typeclasses eauto]; reflexivity.
    * rewrite Eb, Ex, sin_neg. lra.
  + apply (rnd_bracket x b false); [exact Fx | exact Fb | |].
    * rewrite Eb, Ex, succ_opp, pred_succ by first [exact Gp | typeclasses eauto]; reflexivity.
    * rewrite Eb, Ex, sin_neg. lra.
- (* [x = succ p > 0]: [sin x] is below [x], and [b = p] is the [f64]
     before [x]. *)
  assert (Hw : succ64 p < bpow radix2 (-26))
    by (rewrite Ex, Rabs_pos_eq in Hy by exact Hsp; exact Hy).
  destruct (sin_tiny_between p Hp Hw) as [H1 H2].
  assert (Hpos : 0 < B2R x) by (rewrite Ex; lra).
  rewrite (Rlt_bool_true 0 (B2R x)) by exact Hpos.
  destruct up; cbn [Bool.eqb].
  + apply (rnd_bracket b x true); [exact Fb | exact Fx | |].
    * rewrite Eb, Ex; reflexivity.
    * rewrite Eb, Ex. lra.
  + apply (rnd_bracket b x false); [exact Fb | exact Fx | |].
    * rewrite Eb, Ex; reflexivity.
    * rewrite Eb, Ex. lra.
Qed.

(** ** [cos] *)

(** For [0 < a < 2^-26], [1 - 2^-53 < cos a < 1]: [cos_bounds_3] puts
    [cos a] at or above [1 - a^2/2], where [a^2/2 < 2^-53], and at or below
    [1 - a^2/2 + a^4/24], which is less than 1 as [a^2 < 12]. *)
Lemma cos_tiny_real :
  forall a, 0 < a < bpow radix2 (-26) -> 1 - bpow radix2 (-53) < cos a < 1.
Proof.
intros a Ha.
destruct (tiny_range a Ha) as (_ & _ & R1 & R2 & Haa).
destruct (cos_bounds_3 a R1 R2) as [H1 H2].
assert (Hb53 : bpow radix2 (-53) = 1 / 9007199254740992) by (cbn [bpow radix_val radix2]; lra).
rewrite Hb53.
assert (P2 : 0 < a ^ 2) by (apply pow_lt; lra).
assert (E2 : a ^ 2 = a * a) by ring.
assert (H4 : a ^ 4 < a ^ 2 * (1 / 4503599627370496)).
{ replace (a ^ 4) with (a ^ 2 * (a * a)) by ring. apply Rmult_lt_compat_l; lra. }
split; lra.
Qed.

Lemma cos_tiny_rule :
  forall x (up : bool),
  is_finite x = true -> lt (fabs x) DyadicExp.tiny_hyp = true ->
  mpfr_round f64_format (rnd_of up) (cos (B2R x))
    (with_val (DyadicExp.near_one (opp (fabs x)) up)).
Proof.
intros x up Fx Hx.
assert (Ft : is_finite (opp (fabs x)) = true)
  by (unfold opp, fabs; rewrite is_finite_Bopp, is_finite_Babs; exact Fx).
assert (Et : B2R (opp (fabs x)) = - Rabs (B2R x))
  by (unfold opp, fabs; rewrite B2R_Bopp, B2R_Babs; reflexivity).
assert (Hy : Rabs (B2R x) < bpow radix2 (-26)).
{ rewrite <- hyp_lit_tiny. apply fabs_lt_R; [exact Fx | vm_compute; reflexivity | exact Hx]. }
(* [cos] is even, so [cos x = cos |x|]. *)
assert (Ec : cos (B2R x) = cos (Rabs (B2R x))).
{ destruct (Rcase_abs (B2R x)) as [Hn|Hn].
  - rewrite (Rabs_left _ Hn), cos_neg. reflexivity.
  - rewrite (Rabs_right _ Hn). reflexivity. }
pose proof (Rabs_pos (B2R x)) as Hp.
rewrite Ec. apply rnd_near_one; [exact Ft | intros H; rewrite Et in H ..].
- replace (Rabs (B2R x)) with 0 by lra. exact cos_0.
- lra.
- apply cos_tiny_real. lra.
Qed.

(** ** [tan] *)

(** For [0 < y < 2^-26], [y < tan y <= y + y^3/2], with [tan y = sin y /
    cos y] and [cos y >= 1 - y^2/2 > 0]. Below, [y cos y <= y - y^3/2 +
    y^5/24] ([cos_bounds_3]) is less than [y - y^3/6 <= sin y]
    ([sin_bounds_3]), as [y^2 < 8]. Above, [sin y <= y - y^3/6 + y^5/120]
    is at most [y - y^5/4 = (y + y^3/2) (1 - y^2/2) <= (y + y^3/2) cos y],
    as [y^2 (1/120 + 1/4) <= 1/6]. *)
Lemma tan_tiny_real :
  forall y, 0 < y < bpow radix2 (-26) -> y < tan y <= y + y ^ 3 / 2.
Proof.
intros y Hy.
destruct (tiny_range y Hy) as (R0 & RP & R1 & R2 & Hyy).
destruct (sin_bounds_3 y R0 RP) as [S1 S2].
destruct (cos_bounds_3 y R1 R2) as [C1 C2].
assert (P3 : 0 < y ^ 3) by (apply pow_lt; lra).
assert (E2 : y ^ 2 = y * y) by ring.
assert (Hc : 0 < cos y) by lra.
assert (Et : tan y * cos y = sin y) by (unfold tan; field; lra).
(* [y cos y <= y - y^3/2 + y^5/24 < y - y^3/6 <= sin y]. *)
assert (L1 : y * cos y <= y * (1 - y ^ 2 / 2 + y ^ 4 / 24))
  by (apply Rmult_le_compat_l; lra).
assert (H5 : y ^ 5 < y ^ 3 * (1 / 4503599627370496)).
{ replace (y ^ 5) with (y ^ 3 * (y * y)) by ring. apply Rmult_lt_compat_l; lra. }
replace (y * (1 - y ^ 2 / 2 + y ^ 4 / 24)) with (y - y ^ 3 / 2 + y ^ 5 / 24) in L1 by field.
(* [sin y <= y - y^3/6 + y^5/120 <= y - y^5/4 <= (y + y^3/2) cos y]. *)
assert (U1 : (y + y ^ 3 / 2) * (1 - y ^ 2 / 2) <= (y + y ^ 3 / 2) * cos y)
  by (apply Rmult_le_compat_l; lra).
replace ((y + y ^ 3 / 2) * (1 - y ^ 2 / 2)) with (y - y ^ 5 / 4) in U1 by field.
split.
- apply (Rmult_lt_reg_r (cos y)); [exact Hc|]. lra.
- apply (Rmult_le_reg_r (cos y)); [exact Hc|]. lra.
Qed.

(** [y < tan y < succ y] for [0 < y < 2^-26], as [y^3/2 < y 2^-53 < ulp y]. *)
Lemma tan_tiny_succ :
  forall y, 0 < y < bpow radix2 (-26) -> y < tan y < succ64 y.
Proof.
intros y Hy. destruct (tan_tiny_real y Hy) as [H1 H2]. split; [exact H1|].
destruct (tiny_range y Hy) as (_ & _ & _ & _ & Hyy).
rewrite succ_eq_pos by lra.
change (SpecFloat.fexp 53 1024) with (FLT_exp (-1074) 53).
assert (P : Prec_gt_0 53) by (unfold Prec_gt_0; lia).
pose proof (ulp_FLT_gt radix2 (-1074) 53 y) as H.
change (Z.opp 53) with (-53)%Z in H.
rewrite Rabs_pos_eq in H by lra.
assert (Hb53 : bpow radix2 (-53) = 1 / 9007199254740992) by (cbn [bpow radix_val radix2]; lra).
rewrite Hb53 in H.
assert (H3 : y ^ 3 < y * (1 / 4503599627370496)).
{ replace (y ^ 3) with (y * (y * y)) by ring. apply Rmult_lt_compat_l; lra. }
lra.
Qed.

Lemma tan_tiny_rule :
  forall x (up : bool),
  is_finite x = true -> lt (fabs x) DyadicExp.tiny_hyp = true ->
  mpfr_round f64_format (rnd_of up) (tan (B2R x)) (with_val (DyadicExp.away x up)).
Proof.
intros x up Fx Hx.
assert (Ft : is_finite DyadicExp.tiny_hyp = true) by (vm_compute; reflexivity).
apply fabs_lt_R in Hx; [| exact Fx | exact Ft]. rewrite hyp_lit_tiny in Hx.
assert (Ht : bpow radix2 (-26) < 1)
  by (change 1 with (bpow radix2 0); apply bpow_lt; lia).
assert (Hx1 : Rabs (B2R x) < 1) by lra.
destruct (away_bits x Fx Hx1) as (Fb & Ep & En).
assert (Gx : G (B2R x)) by exact (generic_format_B2R 53 1024 x).
assert (Fz : is_finite zero = true) by reflexivity.
unfold DyadicExp.away, eq, gt.
rewrite Beqb_correct by assumption. rewrite Bltb_correct by assumption.
change (B2R zero) with 0.
set (b := from_bits (to_bits x + 1)%Z) in *.
apply Rabs_def2 in Hx as [Hx2 Hx3].
destruct (Req_bool_spec (B2R x) 0) as [H0|H0].
{ (* [tan 0 = 0]. *)
  cbn [orb]. apply rnd_exact; [exact Fx|]. rewrite H0, tan_0. reflexivity. }
cbn [orb].
destruct (Rlt_bool_spec 0 (B2R x)) as [Hp|Hn].
- (* [x > 0]: [tan x] lies between [x] and [succ x], the pattern after [x]. *)
  specialize (Ep Hp).
  destruct (tan_tiny_succ (B2R x) ltac:(lra)) as [H1 H2].
  assert (R : forall u : bool,
    mpfr_round f64_format (rnd_of u) (tan (B2R x)) (with_val (if u then b else x)))
    by (intros u; apply rnd_bracket; [exact Fx | exact Fb | exact Ep | lra]).
  destruct up; [exact (R true) | exact (R false)].
- (* [x < 0]: [tan x = - tan (- x)] lies between [- succ (- x) = pred x],
     the pattern after [x], and [x = succ (pred x)]. *)
  assert (Hneg : B2R x < 0) by lra.
  specialize (En Hneg).
  destruct (tan_tiny_succ (- B2R x) ltac:(lra)) as [H1 H2].
  assert (Hs : tan (B2R x) = - tan (- B2R x))
    by (rewrite tan_neg, Ropp_involutive; reflexivity).
  assert (Ex : B2R x = succ64 (B2R b)).
  { rewrite En, <- pred_opp, Ropp_involutive. symmetry.
    apply succ_pred; [typeclasses eauto | exact Gx]. }
  assert (R : forall u : bool,
    mpfr_round f64_format (rnd_of u) (tan (B2R x)) (with_val (if u then x else b)))
    by (intros u; apply rnd_bracket; [exact Fb | exact Fx | exact Ex | lra]).
  destruct up; [exact (R true) | exact (R false)].
Qed.
