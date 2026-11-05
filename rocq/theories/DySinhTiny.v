(** * The rule before Ziv's strategy for [sinh] of tiny arguments

    The branch of [sinh_dir] of [DyadicExp] in [Model.v] for [|x| <
    2^-26]: [sinh x] is [x] if [x] is 0, and otherwise lies strictly
    between [x] and the next [f64] away from zero, which [away x up]
    returns when [up] rounds away from zero. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Elementary ExpReal ConstLn Encoding IdealGetD OfPointCore
  MpfrRound MpfrIdeal ExpSeries DyExpRules DyHypRules.

Open Scope R_scope.

Local Notation rnd_of up := (if up then RNDU else RNDD).

(** [from_bits (to_bits x + 1)], for a finite [x] with [|x| < 1], is the
    [f64] after [|x|] with the sign of [x]: [to_bits x] is the sign bit
    plus the pattern [c] of [|x|], [c + 1] is the pattern of [succ |x|]
    ([magnitude_succ]), and [|x| < 1] keeps [c + 1] below the infinities. *)
Lemma away_bits :
  forall x, is_finite x = true -> Rabs (B2R x) < 1 ->
  is_finite (from_bits (to_bits x + 1)%Z) = true /\
  (0 < B2R x ->
   B2R (from_bits (to_bits x + 1)%Z) = succ radix2 (SpecFloat.fexp 53 1024) (B2R x)) /\
  (B2R x < 0 ->
   B2R (from_bits (to_bits x + 1)%Z) = - succ radix2 (SpecFloat.fexp 53 1024) (- B2R x)).
Proof.
intros x Fx Hx.
destruct (to_bits_finite x Fx) as (c & Hc & Hb).
destruct (from_bits_finite (Bsign x) c Hc) as (_ & _ & Ex).
rewrite <- Hb, from_to_bits in Ex.
destruct (magnitude_bounds c (proj1 Hc)) as ((H0 & _) & Hge).
assert (Hm : magnitude c < 1).
{ rewrite Ex in Hx. destruct (Bsign x); [rewrite Rabs_Ropp in Hx|];
  rewrite Rabs_pos_eq in Hx by exact H0; exact Hx. }
(* [2^(E - 1023) <= magnitude c < 1] for a biased exponent [E > 0], so
   [E <= 1022] and [c + 1] is at most the pattern of [1]. *)
assert (Hc1 : (0 <= c + 1 < 2047 * 2^52)%Z).
{ destruct (Z.eq_dec (c / 2^52) 0) as [E0|E0]; [zlia|].
  specialize (Hge E0).
  assert (He : (c / 2^52 - 1023 < 0)%Z).
  { apply (lt_bpow radix2). change (bpow radix2 0) with 1. lra. }
  zlia. }
replace (to_bits x + 1)%Z with (sign_bit (Bsign x) + (c + 1))%Z by (rewrite Hb; ring).
destruct (from_bits_finite (Bsign x) (c + 1) Hc1) as (F1 & _ & E1).
rewrite magnitude_succ in E1 by lia.
change (SpecFloat.fexp 53 1024) with fexp64.
split; [exact F1|]. rewrite E1, Ex.
destruct (Bsign x); cbv beta iota; split; intros H.
- lra.
- rewrite Ropp_involutive. reflexivity.
- reflexivity.
- lra.
Qed.

(** For [0 < y < 2^-26], [y < sinh y < y + y 2^-53]. The series of [exp]
    bound [exp y] below by [1 + y + y^2/2 + y^3/6] (positive terms) and
    [exp (-y)] on both sides by [1 - y + y^2/2 - y^3/6] and [1 - y + y^2/2]
    (alternating terms, [exp_alt_bounds]), so [sinh y >= y + y^3/12]; and
    [exp y = 1 / exp (-y)] is at most [1 + y + y^2/2 + 5 y^3/6], as the
    product of that with [1 - y + y^2/2 - y^3/6] is [1 + y^3 (2/3 - ...)],
    so [sinh y <= y + y^3/2], below [y + y 2^-53] as [y^2 < 2^-52]. *)
Lemma sinh_tiny_real :
  forall y, 0 < y < bpow radix2 (-26) -> y < sinh y < y + y * bpow radix2 (-53).
Proof.
intros y Hy.
assert (Hb : bpow radix2 (-26) * bpow radix2 (-26) = 2 * bpow radix2 (-53) /\
             0 < bpow radix2 (-26) < 1 / 1000)
  by (cbn [bpow radix_val radix2]; lra).
assert (Hy1 : 0 <= y <= 1) by lra.
set (e := exp y). set (f := exp (- y)).
assert (Hef : e * f = 1) by (unfold e, f; rewrite <- exp_plus, Rplus_opp_r; exact exp_0).
assert (He0 : 0 < e) by apply exp_pos.
assert (Hf0 : 0 < f) by apply exp_pos.
destruct (exp_alt_bounds y 1 Hy1) as [Hfl Hfu]. fold f in Hfl, Hfu.
replace (sum_f_R0 (tg_alt (exp_tg y)) (S (2 * 1))) with (1 - y + y^2/2 - y^3/6) in Hfl
  by (unfold tg_alt, exp_tg; cbn; field).
replace (sum_f_R0 (tg_alt (exp_tg y)) (2 * 1)) with (1 - y + y^2/2) in Hfu
  by (unfold tg_alt, exp_tg; cbn; field).
assert (Hel : sum_f_R0 (fun i => / INR (fact i) * y ^ i) 3 <= e).
{ apply sum_incr.
  - exact (proj2_sig (exist_exp y)).
  - intros n. apply Rmult_le_pos;
      [left; apply Rinv_0_lt_compat, INR_fact_lt_0 | apply pow_le; lra]. }
replace (sum_f_R0 (fun i => / INR (fact i) * y ^ i) 3) with (1 + y + y^2/2 + y^3/6) in Hel
  by (cbn; field).
assert (Hy3 : 0 < y^3) by (apply pow_lt; lra).
assert (Hyy : y * y < 2 * bpow radix2 (-53)).
{ destruct Hb as [Hb _]. rewrite <- Hb. apply Rmult_le_0_lt_compat; lra. }
assert (Hyyy : y * (y * y) < y * (2 * bpow radix2 (-53)))
  by (apply Rmult_lt_compat_l; lra).
(* [exp y < 1 + y + y^2/2 + 5 y^3/6]. *)
assert (Hp : 0 < 2/3 - 3/4 * y + 1/3 * y^2 - 5/36 * y^3).
{ assert (0 <= y^2) by (apply pow_le; lra).
  assert (y^3 <= y) by (replace (y^3) with (y * y^2) by ring; nra).
  lra. }
assert (Hcb : 1 < (1 + y + y^2/2 + 5/6 * y^3) * (1 - y + y^2/2 - y^3/6)).
{ assert (0 < y^3 * (2/3 - 3/4 * y + 1/3 * y^2 - 5/36 * y^3))
    by (apply Rmult_lt_0_compat; assumption).
  replace ((1 + y + y^2/2 + 5/6 * y^3) * (1 - y + y^2/2 - y^3/6))
    with (1 + y^3 * (2/3 - 3/4 * y + 1/3 * y^2 - 5/36 * y^3)) by field.
  lra. }
assert (Heu : e < 1 + y + y^2/2 + 5/6 * y^3).
{ assert (Hb0 : 0 < 1 - y + y^2/2 - y^3/6) by lra.
  apply (Rmult_lt_reg_r (1 - y + y^2/2 - y^3/6)); [exact Hb0|].
  apply Rle_lt_trans with (e * f); [apply Rmult_le_compat_l; lra | lra]. }
unfold sinh. fold e f.
assert (E3 : y^3 = y * (y * y)) by ring.
split; lra.
Qed.

(** [y < sinh y < succ y] for [0 < y < 2^-26], as [y 2^-53 < ulp y]. *)
Lemma sinh_tiny_succ :
  forall y, 0 < y < bpow radix2 (-26) ->
  y < sinh y < succ radix2 (SpecFloat.fexp 53 1024) y.
Proof.
intros y Hy. destruct (sinh_tiny_real y Hy) as [H1 H2]. split; [exact H1|].
rewrite succ_eq_pos by lra.
change (SpecFloat.fexp 53 1024) with (FLT_exp (-1074) 53).
assert (P : Prec_gt_0 53) by (unfold Prec_gt_0; lia).
pose proof (ulp_FLT_gt radix2 (-1074) 53 y) as H.
change (Z.opp 53) with (-53)%Z in H.
rewrite Rabs_pos_eq in H by lra. lra.
Qed.

Lemma sinh_tiny_rule :
  forall x (up : bool), is_finite x = true -> lt (fabs x) DyadicExp.tiny_hyp = true ->
  mpfr_round f64_format (rnd_of up) (sinh (B2R x)) (with_val (DyadicExp.away x up)).
Proof.
intros x up Fx Hx.
assert (Ft : is_finite DyadicExp.tiny_hyp = true) by (vm_compute; reflexivity).
apply fabs_lt_R in Hx; [| exact Fx | exact Ft]. rewrite hyp_lit_tiny in Hx.
assert (Ht : bpow radix2 (-26) < 1)
  by (change 1 with (bpow radix2 0); apply bpow_lt; lia).
assert (Hx1 : Rabs (B2R x) < 1) by lra.
destruct (away_bits x Fx Hx1) as (Fb & Ep & En).
assert (Gx : generic_format radix2 (SpecFloat.fexp 53 1024) (B2R x))
  by exact (generic_format_B2R 53 1024 x).
assert (Fz : is_finite zero = true) by reflexivity.
unfold DyadicExp.away, eq, gt.
rewrite Beqb_correct by assumption. rewrite Bltb_correct by assumption.
change (B2R zero) with 0.
set (b := from_bits (to_bits x + 1)%Z) in *.
apply Rabs_def2 in Hx as [Hx2 Hx3].
destruct (Req_bool_spec (B2R x) 0) as [H0|H0].
{ cbn [orb]. apply rnd_exact; [exact Fx|]. rewrite H0, sinh_0. reflexivity. }
cbn [orb].
destruct (Rlt_bool_spec 0 (B2R x)) as [Hp|Hn].
- (* [x > 0]: [sinh x] lies between [x] and [succ x], the pattern after [x]. *)
  specialize (Ep Hp).
  destruct (sinh_tiny_succ (B2R x) ltac:(lra)) as [H1 H2].
  assert (R : forall u : bool,
    mpfr_round f64_format (rnd_of u) (sinh (B2R x)) (with_val (if u then b else x)))
    by (intros u; apply rnd_bracket; [exact Fx | exact Fb | exact Ep | lra]).
  destruct up; [exact (R true) | exact (R false)].
- (* [x < 0]: [sinh x = - sinh (- x)] lies between [- succ (- x) = pred x],
     the pattern after [x], and [x = succ (pred x)]. *)
  assert (Hneg : B2R x < 0) by lra.
  specialize (En Hneg).
  destruct (sinh_tiny_succ (- B2R x) ltac:(lra)) as [H1 H2].
  assert (Hs : sinh (B2R x) = - sinh (- B2R x))
    by (unfold sinh; rewrite Ropp_involutive; field).
  assert (Ex : B2R x = succ radix2 (SpecFloat.fexp 53 1024) (B2R b)).
  { rewrite En, <- pred_opp, Ropp_involutive. symmetry.
    apply succ_pred; [typeclasses eauto | exact Gx]. }
  assert (R : forall u : bool,
    mpfr_round f64_format (rnd_of u) (sinh (B2R x)) (with_val (if u then x else b)))
    by (intros u; apply rnd_bracket; [exact Fb | exact Fx | exact Ex | lra]).
  destruct up; [exact (R true) | exact (R false)].
Qed.
