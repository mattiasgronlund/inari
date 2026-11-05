(** * The rule before Ziv's strategy for [tanh] of tiny arguments

    The branch of [tanh_dir] of [DyadicExp] in [Model.v] for [|x| <
    2^-26]: [tanh x] is [x] if [x] is 0, and otherwise lies strictly
    between [x] and the next [f64] toward zero, which [toward_zero x up]
    returns when [up] rounds toward zero. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Elementary ExpReal ConstLn Encoding IdealGetD OfPointCore
  MpfrRound MpfrIdeal ExpSeries DyExpRules DyHypRules.

Open Scope R_scope.

Local Notation rnd_of up := (if up then RNDU else RNDD).

(** The format of the finite [f64]s without the bound above, as in
    [DyExpRules.v]. *)
Local Notation G := (generic_format radix2 (SpecFloat.fexp 53 1024)).
Local Notation succ64 := (succ radix2 (SpecFloat.fexp 53 1024)).

(** Subtracting one from the pattern of a nonzero finite [x] steps to the
    next [f64] toward zero: if [|x|] is [succ p], the result is [p] with
    the sign of [x] ([-0] for [x = -2^-1074]). *)
Lemma toward_zero_bits :
  forall x, is_finite x = true -> B2R x <> 0 ->
  exists p, 0 <= p /\ G p /\
    is_finite (from_bits (to_bits x - 1)) = true /\
    B2R x = (if Bsign x then - succ64 p else succ64 p) /\
    B2R (from_bits (to_bits x - 1)) = (if Bsign x then - p else p).
Proof.
intros x Fx Hx0.
destruct (to_bits_finite x Fx) as (c & Hc & Hb).
destruct (from_bits_finite (Bsign x) c Hc) as (_ & _ & Hx).
rewrite <- Hb, from_to_bits in Hx.
(* [c = 0] is a zero, so [c - 1] is a pattern too. *)
assert (Hc0 : c <> 0%Z).
{ intros ->. rewrite magnitude_0 in Hx. apply Hx0. rewrite Hx.
  destruct (Bsign x); ring. }
rewrite Hb.
replace (sign_bit (Bsign x) + c - 1)%Z with (sign_bit (Bsign x) + (c - 1))%Z by ring.
assert (Hc1 : (0 <= c - 1 < 2047 * 2^52)%Z) by lia.
destruct (from_bits_finite (Bsign x) (c - 1) Hc1) as (F1 & _ & R1).
pose proof (magnitude_succ (c - 1) (proj1 Hc1)) as Hsucc.
replace (c - 1 + 1)%Z with c in Hsucc by ring.
destruct (magnitude_bounds (c - 1) (proj1 Hc1)) as ((Hm0 & _) & _).
assert (Gm : G (magnitude (c - 1))).
{ destruct (from_bits_finite false (c - 1) Hc1) as (_ & _ & R0).
  cbv beta iota in R0. rewrite <- R0. apply generic_format_B2R. }
exists (magnitude (c - 1)).
split; [exact Hm0|]. split; [exact Gm|]. split; [exact F1|]. split.
- rewrite Hx, Hsucc. reflexivity.
- exact R1.
Qed.

(** For [0 < y < 2^-26], [y - 2/5 y^3 <= tanh y < y]. With [v = exp (-2y)],
    [tanh y = (1 - v) / (1 + v)], and the alternating series of [exp (-2y)]
    ([exp_alt_bounds]) bounds [v] by its partial sums of 4 and 5 terms. *)
Lemma tanh_tiny_bounds :
  forall y, 0 < y < bpow radix2 (-26) -> y - 2 / 5 * y ^ 3 <= tanh y < y.
Proof.
intros y Hy.
assert (Hb : 0 < bpow radix2 (-26) < 1 / 1000) by (cbn [bpow radix_val radix2]; lra).
set (v := exp (- (2 * y))).
assert (Hv : 0 < v) by apply exp_pos.
assert (Ht : tanh y = (1 - v) / (1 + v)).
{ rewrite tanh_eq. unfold v. rewrite exp_Ropp.
  pose proof (exp_pos (2 * y)). field. lra. }
assert (Hz : 0 <= 2 * y <= 1) by lra.
destruct (exp_alt_bounds (2 * y) 1 Hz) as [Hl _].
destruct (exp_alt_bounds (2 * y) 2 Hz) as [_ Hu].
fold v in Hl, Hu.
assert (Hl' : 1 - 2 * y + 2 * y ^ 2 - 4 / 3 * y ^ 3 <= v).
{ eapply Rle_trans; [|exact Hl]. right. unfold tg_alt, exp_tg. simpl. field. }
assert (Hu' : v <= 1 - 2 * y + 2 * y ^ 2 - 4 / 3 * y ^ 3 + 2 / 3 * y ^ 4).
{ eapply Rle_trans; [exact Hu|]. right. unfold tg_alt, exp_tg. simpl. field. }
clear Hl Hu.
(* The powers of [y] shrink by at least 16 each, which is all [lra]
   needs of them. *)
assert (Pk : forall k, 0 < y ^ S k <= y ^ k / 16).
{ intros k. assert (0 < y ^ k) by (apply pow_lt; lra).
  split; [apply pow_lt; lra|]. rewrite <- tech_pow_Rmult. nra. }
pose proof (Pk 1%nat) as P2. pose proof (Pk 2%nat) as P3. pose proof (Pk 3%nat) as P4.
pose proof (Pk 4%nat) as P5. pose proof (Pk 5%nat) as P6. pose proof (Pk 6%nat) as P7.
assert (HT : tanh y * (1 + v) = 1 - v) by (rewrite Ht; field; lra).
clear Ht. split.
- (* [v (1 + t) <= 1 - t] for [t = y - 2/5 y^3], so [t <= tanh y]. *)
  assert (Hk : v * (1 + (y - 2 / 5 * y ^ 3)) <= 1 - (y - 2 / 5 * y ^ 3)).
  { eapply Rle_trans.
    { apply Rmult_le_compat_r; [lra | exact Hu']. }
    ring_simplify. lra. }
  set (t := y - 2 / 5 * y ^ 3) in *. set (T := tanh y) in *.
  clear - HT Hk Hv. nra.
- (* [1 - y < v (1 + y)], so [tanh y < y]. *)
  assert (Hk : 1 - y < v * (1 + y)).
  { eapply Rlt_le_trans; [|apply Rmult_le_compat_r; [lra | exact Hl']].
    ring_simplify. lra. }
  set (T := tanh y) in *.
  clear - HT Hk Hv. nra.
Qed.

(** If [w = succ p] with [0 <= p] and [w < 2^-26], [tanh w] lies strictly
    between [p] and [w]: [w - p = ulp p > p 2^-53] ([ulp_FLT_gt]) gives
    [p < w / (1 + 2^-53)], and [w^2 < 2^-52] gives [w - 2/5 w^3 >=
    w (1 - 4/5 2^-53) >= w / (1 + 2^-53)]. *)
Lemma tanh_tiny_between :
  forall p, 0 <= p -> succ64 p < bpow radix2 (-26) -> p < tanh (succ64 p) < succ64 p.
Proof.
intros p Hp Hw.
assert (P53 : Prec_gt_0 53) by (unfold Prec_gt_0; lia).
pose proof (ulp_FLT_gt radix2 (-1074) 53 p) as Hu.
change (Rabs p * bpow radix2 (-53) < ulp radix2 (SpecFloat.fexp 53 1024) p) in Hu.
rewrite Rabs_pos_eq in Hu by exact Hp.
assert (Hs : succ64 p = p + ulp radix2 (SpecFloat.fexp 53 1024) p)
  by (apply succ_eq_pos; exact Hp).
set (w := succ64 p) in *.
set (u := ulp radix2 (SpecFloat.fexp 53 1024) p) in *.
assert (He : bpow radix2 (-53) = 1 / 9007199254740992) by (cbn [bpow radix_val radix2]; lra).
rewrite He in Hu.
assert (Hw0 : 0 < w) by lra.
destruct (tanh_tiny_bounds w (conj Hw0 Hw)) as [Hl Hr].
split; [|exact Hr].
(* [w^2 < 2^-52], so [w^3 <= 2^-52 w]. *)
assert (H52 : bpow radix2 (-26) * bpow radix2 (-26) = 1 / 4503599627370496)
  by (cbn [bpow radix_val radix2]; lra).
assert (Hw2 : w * w < 1 / 4503599627370496).
{ rewrite <- H52. apply Rmult_le_0_lt_compat; lra. }
assert (Hw3 : w ^ 3 <= w / 4503599627370496).
{ replace (w ^ 3) with (w * (w * w)) by ring.
  replace (w / 4503599627370496) with (w * (1 / 4503599627370496)) by field.
  apply Rmult_le_compat_l; lra. }
lra.
Qed.

Lemma tanh_tiny_rule :
  forall x (up : bool), is_finite x = true -> lt (fabs x) DyadicExp.tiny_hyp = true ->
  mpfr_round f64_format (rnd_of up) (tanh (B2R x)) (with_val (DyadicExp.toward_zero x up)).
Proof.
intros x up Fx Ht.
assert (Fth : is_finite DyadicExp.tiny_hyp = true) by (vm_compute; reflexivity).
pose proof (fabs_lt_R x _ Fx Fth Ht) as Hy. rewrite hyp_lit_tiny in Hy.
assert (Fz : is_finite zero = true) by reflexivity.
unfold DyadicExp.toward_zero, eq, gt.
rewrite Beqb_correct by assumption. rewrite Bltb_correct by assumption.
assert (Ez : B2R zero = 0) by reflexivity. rewrite Ez.
destruct (Req_bool_spec (B2R x) 0) as [Hx|Hx]; cbn [orb].
{ (* [tanh 0 = 0]. *)
  apply rnd_exact; [exact Fx|]. rewrite Hx.
  unfold tanh, sinh, cosh. rewrite Ropp_0, exp_0. field. }
destruct (toward_zero_bits x Fx Hx) as (p & Hp & Gp & Fb & Ex & Eb).
set (b := from_bits (to_bits x - 1)) in *.
assert (Hsp : 0 <= succ64 p) by (eapply Rle_trans; [exact Hp | apply succ_ge_id]).
revert Ex Eb. destruct (Bsign x); intros Ex Eb.
- (* [x = - succ p < 0]: [x] is below [tanh x], and [b = -p] is the next
     [f64] above [x]. *)
  assert (Hw : succ64 p < bpow radix2 (-26))
    by (rewrite Ex, Rabs_Ropp, Rabs_pos_eq in Hy by exact Hsp; exact Hy).
  destruct (tanh_tiny_between p Hp Hw) as [H1 H2].
  rewrite (Rlt_bool_false 0 (B2R x)) by (rewrite Ex; lra).
  destruct up; cbn [Bool.eqb].
  + apply (rnd_bracket x b true); [exact Fx | exact Fb | |].
    * rewrite Eb, Ex, succ_opp, pred_succ by first [exact Gp | typeclasses eauto]; reflexivity.
    * rewrite Eb, Ex, tanh_odd. lra.
  + apply (rnd_bracket x b false); [exact Fx | exact Fb | |].
    * rewrite Eb, Ex, succ_opp, pred_succ by first [exact Gp | typeclasses eauto]; reflexivity.
    * rewrite Eb, Ex, tanh_odd. lra.
- (* [x = succ p > 0]: [tanh x] is below [x], and [b = p] is the [f64]
     before [x]. *)
  assert (Hw : succ64 p < bpow radix2 (-26))
    by (rewrite Ex, Rabs_pos_eq in Hy by exact Hsp; exact Hy).
  destruct (tanh_tiny_between p Hp Hw) as [H1 H2].
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
