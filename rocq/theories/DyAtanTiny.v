(** * The rules before Ziv's strategy for [atan], [asin] and [atan2] of tiny arguments

    The branches of [atan_dir], [asin_dir] and [atan2_dir] of
    [DyadicAtan] in [Model.v] for tiny arguments: [atan x] and [asin x]
    are [x] if [x] is 0. Otherwise [atan x] lies strictly between [x] and
    the next [f64] toward zero for [|x| < 2^-26], which [toward_zero x up]
    returns when [up] rounds toward zero, as [asinh x] does in
    [DyLogTiny.v], and [asin x] lies strictly between [x] and the next
    [f64] away from zero for [|x| < 2^-27], which [away x up] returns
    when [up] rounds away from zero, as [atanh x] does there.
    [tiny_quotient y x] returns an [f64] only if it is [y / x] exactly
    and of absolute value below [2^-26], so that the rule of [atan]
    applies to it. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Elementary ExpReal ConstLn Encoding IdealGetD OfPointCore
  MpfrRound MpfrIdeal ExpSeries AtanhSeries DyExpRules DyHypRules DySinhTiny DyTanhTiny
  DyLogRules DyLogTiny AtanSeries DyRound DyOps DyConv.

Open Scope R_scope.

Local Notation rnd_of up := (if up then RNDU else RNDD).

(** The format of the finite [f64]s without the bound above, as in
    [DyTanhTiny.v]. *)
Local Notation G := (generic_format radix2 (SpecFloat.fexp 53 1024)).
Local Notation succ64 := (succ radix2 (SpecFloat.fexp 53 1024)).

(** ** [atan] *)

(** For [0 < w < 2^-26], [w - w^3/3 <= atan w < w]: the remainders of the
    series of [atan] after one and two terms ([atan_tail_bounds]) put
    [atan w] between [w - w^3/3] and [w - w^3/3 + w^5/5], and [w^2 < 5/3]
    makes [w^5/5] less than [w^3/3]. *)
Lemma atan_tiny_real :
  forall w, 0 < w < bpow radix2 (-26) -> w - w ^ 3 / 3 <= atan w < w.
Proof.
intros w Hw.
assert (Hb : bpow radix2 (-26) = 1 / 67108864) by (cbn [bpow radix_val radix2]; lra).
rewrite Hb in Hw.
assert (Hww : w * w < 1 / 4503599627370496).
{ replace (1 / 4503599627370496) with (1 / 67108864 * (1 / 67108864)) by field.
  apply Rmult_le_0_lt_compat; lra. }
destruct (atan_tail_bounds 1 w) as (T1 & B1 & E1).
destruct (atan_tail_bounds 2 w) as (T2 & B2 & E2).
change (2 * 1 + 1)%nat with 3%nat in B1, E1.
change (2 * 2 + 1)%nat with 5%nat in B2, E2.
replace (atan_sum 1 w) with w in E1 by (cbn; field).
replace (atan_sum 2 w) with (w - w ^ 3 / 3) in E2 by (cbn; field).
replace (INR 3) with 3 in B1 by (cbn; ring).
replace (INR 5) with 5 in B2 by (cbn; ring).
replace ((-1) ^ 1) with (-1) in E1 by ring.
replace ((-1) ^ 2) with 1 in E2 by ring.
assert (P3 : 0 < w ^ 3) by (apply pow_lt; lra).
assert (P5 : 0 < w ^ 5) by (apply pow_lt; lra).
assert (H1 : T1 * w ^ 3 <= w ^ 3 / 3).
{ unfold Rdiv. rewrite (Rmult_comm (w ^ 3)). apply Rmult_le_compat_r; lra. }
assert (H2 : T2 * w ^ 5 <= w ^ 5 / 5).
{ unfold Rdiv. rewrite (Rmult_comm (w ^ 5)). apply Rmult_le_compat_r; lra. }
assert (H5 : w ^ 5 < w ^ 3 * (1 / 4503599627370496)).
{ replace (w ^ 5) with (w ^ 3 * (w * w)) by ring. apply Rmult_lt_compat_l; lra. }
split; lra.
Qed.

(** If [w = succ p] with [0 <= p] and [w < 2^-26], [atan w] lies strictly
    between [p] and [w]: [atan_tiny_real] puts it below [w] and at or above
    [w - w^3/3], and [w^3/3 < w 2^-52 / 3] is less than [ulp p = w - p],
    which is more than [p 2^-53]. *)
Lemma atan_tiny_between :
  forall p, 0 <= p -> succ64 p < bpow radix2 (-26) -> p < atan (succ64 p) < succ64 p.
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
assert (Hb : bpow radix2 (-26) = 1 / 67108864 /\ bpow radix2 (-53) = 1 / 9007199254740992)
  by (cbn [bpow radix_val radix2]; split; lra).
destruct Hb as [Hb26 Hb53]. rewrite Hb53 in Hu.
destruct (atan_tiny_real w ltac:(lra)) as [H1 H2].
rewrite Hb26 in Hw.
assert (Hww : w * w < 1 / 4503599627370496).
{ replace (1 / 4503599627370496) with (1 / 67108864 * (1 / 67108864)) by field.
  apply Rmult_le_0_lt_compat; lra. }
assert (H3 : w ^ 3 < w * (1 / 4503599627370496)).
{ replace (w ^ 3) with (w * (w * w)) by ring. apply Rmult_lt_compat_l; lra. }
split; lra.
Qed.

Lemma atan_tiny_rule :
  forall x (up : bool), is_finite x = true -> lt (fabs x) DyadicExp.tiny_hyp = true ->
  mpfr_round f64_format (rnd_of up) (atan (B2R x)) (with_val (DyadicExp.toward_zero x up)).
Proof.
intros x up Fx Ht.
assert (Fth : is_finite DyadicExp.tiny_hyp = true) by (vm_compute; reflexivity).
pose proof (fabs_lt_R x _ Fx Fth Ht) as Hy. rewrite hyp_lit_tiny in Hy.
assert (Fz : is_finite zero = true) by reflexivity.
unfold DyadicExp.toward_zero, eq, gt.
rewrite Beqb_correct by assumption. rewrite Bltb_correct by assumption.
assert (Ez : B2R zero = 0) by reflexivity. rewrite Ez.
destruct (Req_bool_spec (B2R x) 0) as [Hx|Hx]; cbn [orb].
{ (* [atan 0 = 0]. *)
  apply rnd_exact; [exact Fx|]. rewrite Hx, atan_0. reflexivity. }
destruct (toward_zero_bits x Fx Hx) as (p & Hp & Gp & Fb & Ex & Eb).
set (b := from_bits (to_bits x - 1)) in *.
assert (Hsp : 0 <= succ64 p) by (eapply Rle_trans; [exact Hp | apply succ_ge_id]).
revert Ex Eb. destruct (Bsign x); intros Ex Eb.
- (* [x = - succ p < 0]: [x] is below [atan x], and [b = -p] is the next
     [f64] above [x]. *)
  assert (Hw : succ64 p < bpow radix2 (-26))
    by (rewrite Ex, Rabs_Ropp, Rabs_pos_eq in Hy by exact Hsp; exact Hy).
  destruct (atan_tiny_between p Hp Hw) as [H1 H2].
  rewrite (Rlt_bool_false 0 (B2R x)) by (rewrite Ex; lra).
  destruct up; cbn [Bool.eqb].
  + apply (rnd_bracket x b true); [exact Fx | exact Fb | |].
    * rewrite Eb, Ex, succ_opp, pred_succ by first [exact Gp | typeclasses eauto]; reflexivity.
    * rewrite Eb, Ex, atan_opp. lra.
  + apply (rnd_bracket x b false); [exact Fx | exact Fb | |].
    * rewrite Eb, Ex, succ_opp, pred_succ by first [exact Gp | typeclasses eauto]; reflexivity.
    * rewrite Eb, Ex, atan_opp. lra.
- (* [x = succ p > 0]: [atan x] is below [x], and [b = p] is the [f64]
     before [x]. *)
  assert (Hw : succ64 p < bpow radix2 (-26))
    by (rewrite Ex, Rabs_pos_eq in Hy by exact Hsp; exact Hy).
  destruct (atan_tiny_between p Hp Hw) as [H1 H2].
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

(** ** [asin] *)

Lemma asin_lit_tiny : B2R DyadicAtan.tiny_asin = bpow radix2 (-27).
Proof.
(* [B2SF] of the literal computes to its sign, significand and exponent,
   as [lit_B2R] does in [DyHypRules.v]. *)
rewrite <- (SF2R_B2SF _ _ DyadicAtan.tiny_asin).
let s := eval vm_compute in (B2SF DyadicAtan.tiny_asin) in
replace (B2SF DyadicAtan.tiny_asin) with s by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]; unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
reflexivity.
Qed.

(** For [0 < y < 2^-27], [y < asin y <= y + y^3]. [asin y] is
    [atan (y / √(1 - y^2))] ([asin_atan]), positive, and
    [y = sin (asin y) < asin y] ([sin_lt_x]). Above, [atan z <= z] for
    [z >= 0] (the remainder of the series after no term,
    [atan_tail_bounds]), and [1 / √(1 - s) <= 1 + s] for [0 <= s <= 1/2],
    as [(1 - s) (1 + s)^2 = 1 + s (1 - s - s^2) >= 1]. *)
Lemma asin_tiny_real :
  forall y, 0 < y < bpow radix2 (-27) -> y < asin y <= y + y ^ 3.
Proof.
intros y Hy.
assert (Hb : bpow radix2 (-27) = 1 / 134217728) by (cbn [bpow radix_val radix2]; lra).
rewrite Hb in Hy.
assert (Hyy : y * y < 1 / 18014398509481984).
{ replace (1 / 18014398509481984) with (1 / 134217728 * (1 / 134217728)) by field.
  apply Rmult_le_0_lt_compat; lra. }
assert (Hy1 : -1 < y < 1) by lra.
assert (Hs : 0 < 1 - y²) by (unfold Rsqr; lra).
set (r := sqrt (1 - y²)).
assert (Hr : 0 < r) by (apply sqrt_lt_R0; exact Hs).
assert (Hrr : r * r = 1 - y²) by (apply sqrt_sqrt; lra).
unfold Rsqr in Hrr.
set (z := y / r).
assert (Hz : 0 < z) by (apply Rdiv_lt_0_compat; lra).
assert (Ea : asin y = atan z) by (apply asin_atan; exact Hy1).
split.
- (* [0 < asin y], so [sin (asin y) < asin y]. *)
  assert (Hp : 0 < asin y) by (rewrite Ea, <- atan_0; apply atan_increasing; exact Hz).
  pose proof (sin_lt_x (asin y) Hp) as H.
  rewrite sin_asin in H by lra. exact H.
- (* [atan z <= z <= y (1 + y^2)]. *)
  destruct (atan_tail_bounds 0 z) as (T & B & E).
  change (2 * 0 + 1)%nat with 1%nat in B, E.
  replace (atan_sum 0 z) with 0 in E by reflexivity.
  replace (INR 1) with 1 in B by reflexivity.
  replace ((-1) ^ 0) with 1 in E by ring.
  rewrite pow_1 in E.
  assert (Hza : atan z <= z).
  { assert (T * z <= 1 * z) by (apply Rmult_le_compat_r; lra). lra. }
  (* [(r (1 + y^2))^2 = (1 - y^2) (1 + y^2)^2 >= 1], and [r (1 + y^2) >= 0]. *)
  assert (Hr1 : 1 <= r * (1 + y * y)).
  { assert (Hsq : 1 <= (r * (1 + y * y)) * (r * (1 + y * y))).
    { replace ((r * (1 + y * y)) * (r * (1 + y * y))) with
        ((r * r) * ((1 + y * y) * (1 + y * y))) by ring.
      rewrite Hrr. nra. }
    nra. }
  assert (Hzy : z <= y * (1 + y * y)).
  { unfold z. apply (Rmult_le_reg_r r); [exact Hr|].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra. }
  rewrite Ea. replace (y + y ^ 3) with (y * (1 + y * y)) by ring. lra.
Qed.

(** [y < asin y < succ y] for [0 < y < 2^-27], as [y^3 < y 2^-54 < ulp y]. *)
Lemma asin_tiny_succ :
  forall y, 0 < y < bpow radix2 (-27) -> y < asin y < succ64 y.
Proof.
intros y Hy. destruct (asin_tiny_real y Hy) as [H1 H2]. split; [exact H1|].
rewrite succ_eq_pos by lra.
change (SpecFloat.fexp 53 1024) with (FLT_exp (-1074) 53).
assert (P : Prec_gt_0 53) by (unfold Prec_gt_0; lia).
pose proof (ulp_FLT_gt radix2 (-1074) 53 y) as H.
change (Z.opp 53) with (-53)%Z in H.
rewrite Rabs_pos_eq in H by lra.
assert (Hb : bpow radix2 (-27) = 1 / 134217728 /\ bpow radix2 (-53) = 1 / 9007199254740992)
  by (cbn [bpow radix_val radix2]; split; lra).
destruct Hb as [Hb27 Hb53]. rewrite Hb27 in Hy. rewrite Hb53 in H.
assert (Hyy : y * y < 1 / 18014398509481984).
{ replace (1 / 18014398509481984) with (1 / 134217728 * (1 / 134217728)) by field.
  apply Rmult_le_0_lt_compat; lra. }
assert (H3 : y ^ 3 < y * (1 / 18014398509481984)).
{ replace (y ^ 3) with (y * (y * y)) by ring. apply Rmult_lt_compat_l; lra. }
lra.
Qed.

Lemma asin_tiny_rule :
  forall x (up : bool), is_finite x = true -> lt (fabs x) DyadicAtan.tiny_asin = true ->
  mpfr_round f64_format (rnd_of up) (asin (B2R x)) (with_val (DyadicExp.away x up)).
Proof.
intros x up Fx Hx.
assert (Ft : is_finite DyadicAtan.tiny_asin = true) by (vm_compute; reflexivity).
apply fabs_lt_R in Hx; [| exact Fx | exact Ft]. rewrite asin_lit_tiny in Hx.
assert (Ht : bpow radix2 (-27) < 1)
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
{ (* [asin 0 = 0]. *)
  cbn [orb]. apply rnd_exact; [exact Fx|]. rewrite H0, asin_0. reflexivity. }
cbn [orb].
destruct (Rlt_bool_spec 0 (B2R x)) as [Hp|Hn].
- (* [x > 0]: [asin x] lies between [x] and [succ x], the pattern after [x]. *)
  specialize (Ep Hp).
  destruct (asin_tiny_succ (B2R x) ltac:(lra)) as [H1 H2].
  assert (R : forall u : bool,
    mpfr_round f64_format (rnd_of u) (asin (B2R x)) (with_val (if u then b else x)))
    by (intros u; apply rnd_bracket; [exact Fx | exact Fb | exact Ep | lra]).
  destruct up; [exact (R true) | exact (R false)].
- (* [x < 0]: [asin x = - asin (- x)] lies between [- succ (- x) = pred x],
     the pattern after [x], and [x = succ (pred x)]. *)
  assert (Hneg : B2R x < 0) by lra.
  specialize (En Hneg).
  destruct (asin_tiny_succ (- B2R x) ltac:(lra)) as [H1 H2].
  assert (Hs : asin (B2R x) = - asin (- B2R x))
    by (rewrite asin_opp, Ropp_involutive; reflexivity).
  assert (Ex : B2R x = succ64 (B2R b)).
  { rewrite En, <- pred_opp, Ropp_involutive. symmetry.
    apply succ_pred; [typeclasses eauto | exact Gx]. }
  assert (R : forall u : bool,
    mpfr_round f64_format (rnd_of u) (asin (B2R x)) (with_val (if u then x else b)))
    by (intros u; apply rnd_bracket; [exact Fb | exact Fx | exact Ex | lra]).
  destruct up; [exact (R true) | exact (R false)].
Qed.

(** ** [tiny_quotient] *)

(** [q <= lo <= y / x <= hi <= q'], from the directed divisions and
    conversions, and [eq q q'] makes [q] and [q'] the same real, so [q] is
    [y / x]. [lt (fabs q) tiny_hyp] rules out an infinity or a NaN [q], and
    [eq q q'] then rules them out for [q']. *)
Lemma tiny_quotient_correct :
  forall y x q,
  is_finite y = true -> is_finite x = true -> 0 < B2R x ->
  DyadicAtan.tiny_quotient y x = Some (Some q) ->
  is_finite q = true /\ B2R q = B2R y / B2R x /\ lt (fabs q) DyadicExp.tiny_hyp = true.
Proof.
intros y x q Fy Fx Hx H.
assert (Hn : level_ok 1) by (unfold level_ok; lia).
destruct (from_f64_correct 1 y Hn Fy) as (a & Ea & Oa & Sa & Va).
destruct (from_f64_correct 1 x Hn Fx) as (d & Ed & Od & Sd & Vd).
assert (Hd : Dyadic.dy_R d <> 0) by (rewrite Vd; lra).
destruct (div_correct 1 a d false Hn Oa Od Sa Sd Hd) as (lo & Elo & Olo & Vlo).
destruct (div_correct 1 a d true Hn Oa Od Sa Sd Hd) as (hi & Ehi & Ohi & Vhi).
destruct (to_f64_correct 1 lo false Hn Olo) as (q0 & Eq0 & Rq0).
destruct (to_f64_correct 1 hi true Hn Ohi) as (q1 & Eq1 & Rq1).
unfold DyadicAtan.tiny_quotient in H.
destruct (ge (mul (fabs y) DyadicAtan.two_25) x); [discriminate H|].
rewrite Ea, Ed in H. cbv beta iota in H.
rewrite Elo, Ehi, Eq0, Eq1 in H. cbv beta iota in H.
destruct (eq q0 q1 && lt (fabs q0) DyadicExp.tiny_hyp) eqn:C; [|discriminate H].
injection H as <-.
apply andb_prop in C as [Ce Cl].
assert (Fq0 : is_finite q0 = true).
{ destruct q0 as [s|s| |s m e Hm]; try reflexivity; vm_compute in Cl; discriminate Cl. }
assert (Fq1 : is_finite q1 = true).
{ destruct q1 as [s'|s'| |s' m' e' Hm']; try reflexivity;
    destruct q0 as [s|s| |s m e Hm]; try discriminate Fq0;
    try destruct s'; vm_compute in Ce; discriminate Ce. }
split; [exact Fq0|]. split; [|exact Cl].
unfold eq in Ce. rewrite Beqb_correct in Ce by assumption.
destruct (Req_bool_spec (B2R q0) (B2R q1)) as [E01|]; [|discriminate Ce].
apply round_finite_pt in Rq0; [|exact Fq0].
apply round_finite_pt in Rq1; [|exact Fq1].
cbn [rnd_pt] in Rq0, Rq1.
destruct Rq0 as (_ & L0 & _). destruct Rq1 as (_ & L1 & _).
rewrite Va, Vd in Vlo, Vhi.
destruct (dround_bounds 1 (B2R y / B2R x) Hn) as [D0 D1].
lra.
Qed.
