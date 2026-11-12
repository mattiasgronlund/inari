(** * The polynomial of the first stage of the fast path of atan

    [DyadicAtan.fast_atan1] of [Model.v] evaluates atan x for [|x| <=
    2^-7] as [x - x^3 B] with [B = 1/3 - v (1/5 - v (1/7 - v / 9))] and
    [v = x^2], the odd Taylor polynomial of degree 9, in plain [f64]: at
    [x = th] where [i = 0], and at [x = uh] otherwise. [poly9 x] is the
    rounded [x^3 B], within [2^-52 |x|^3] of [x - atan x] ([poly9_err]).

    The steps, with [S = x^2] and [C = |x| S = |x|^3]: [v] rounds [S],
    Horner's scheme gives [b] within [0.84 2^-53] of [B(S)] (the steps
    [mul_step] and [sub_step] of [FastAtanPoly.v], with [A3] within
    [2^-54] of [1/3] and [A5], [A7], [A9] within [2^-56] of [1/5], [1/7],
    [1/9]), [w] rounds [x v] and [m] rounds [w b]. [p9_assemble] adds
    their errors, about [1.86 2^-53 C], to the truncation [|x|^11 / 11 <=
    2^-59.4 C] ([AtanSeries.atan_tail_bounds]) on the reals. *)

From Stdlib Require Import ZArith Reals Lra Lia QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error Sterbenz.
From Inari Require Import Model Mpfr Encoding Elementary TwoSum TwoProduct DyDriver NearF64
  FastRound FastRoundErr FastDiv CancelLanes FastHypPos FastAtanTables FastAtanIdent
  FastAtanPoly FastAtanCore AtanSeries.
From Inari Require FastExpErr FastExpReduce ConstTight.

Open Scope R_scope.

(** Powers of 2 as numerals, for [lra] (as in [FastAtanPoly.v]). *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp].

(** The plain degree-9 polynomial of [fast_atan1]: [x^3 B] for [B = 1/3 - v
    (1/5 - v (1/7 - v / 9))], [v = x^2], each step rounded to nearest. *)
Definition poly9 (x : f64) : f64 :=
  let v := mul x x in
  mul (mul x v) (sub (from_bits (fst DyadicAtan.A3))
    (mul v (sub (from_bits DyadicAtan.A5) (mul v (sub (from_bits DyadicAtan.A7)
      (mul v (from_bits DyadicAtan.A9))))))).

(** The error of [poly9] on the reals: with [v] within [2^-53 x^2] of
    [x^2], [w] within [2^-53 |x v|] of [x v], [b] within [0.84 2^-53] of
    [p] and [m] within [2^-53 |w b|] of [w b], [m] is within [1.86 2^-53
    |x|^3] of [x^3 p], and [x^3 p - m] plus the truncation [T x^11] of
    the series is at most [2^-52 |x|^3]. *)
Local Lemma p9_assemble :
  forall xr v w b m p T : R,
  bpow radix2 (-82) <= Rabs xr <= bpow radix2 (-7) ->
  Rabs (v - xr * xr) <= bpow radix2 (-53) * (xr * xr) ->
  Rabs (w - xr * v) <= bpow radix2 (-53) * Rabs (xr * v) ->
  Rabs (b - p) <= 84 / 100 * bpow radix2 (-53) -> Rabs b <= 34 / 100 ->
  Rabs (m - w * b) <= bpow radix2 (-53) * Rabs (w * b) ->
  0 <= T <= / 11 ->
  Rabs m <= bpow radix2 (-15) * Rabs xr /\
  Rabs (xr - m - (xr - xr * (xr * xr) * p - T * xr ^ 11)) <= bpow radix2 (-52) * Rabs xr ^ 3.
Proof.
intros xr v w b m p T Hx Hv Hw Hb Hb1 Hm HT.
pose proof (bpow_gt_0 radix2 (-53)) as P53.
(* [S = x^2 = X^2] is at most [2^-14], so [C = X S] is at most [2^-14 X]. *)
assert (ES : xr * xr = Rabs xr * Rabs xr).
{ rewrite <- Rabs_mult. symmetry. apply Rabs_pos_eq. pose proof (Rle_0_sqr xr) as H.
  unfold Rsqr in H. exact H. }
assert (HS : 0 <= xr * xr <= bpow radix2 (-14)).
{ rewrite ES. split; [apply Rmult_le_pos; apply Rabs_pos |].
  replace (bpow radix2 (-14)) with (bpow radix2 (-7) * bpow radix2 (-7))
    by (rewrite <- bpow_plus; reflexivity).
  apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | apply Hx | apply Hx]. }
assert (HC0 : 0 <= Rabs xr * (xr * xr)) by (apply Rmult_le_pos; [apply Rabs_pos | apply HS]).
assert (HC : Rabs xr * (xr * xr) <= bpow radix2 (-14) * Rabs xr).
{ rewrite (Rmult_comm (Rabs xr)). apply Rmult_le_compat_r; [apply Rabs_pos | apply HS]. }
assert (Hxs : Rabs (xr * (xr * xr)) = Rabs xr * (xr * xr)).
{ rewrite Rabs_mult, (Rabs_pos_eq (xr * xr)) by apply HS. reflexivity. }
(* [|v| <= (1 + 2^-53) S] and [|x v| <= (1 + 2^-53) C]. *)
pose proof Hv as Hv'. apply Rabs_le_inv in Hv'.
assert (Av : Rabs v <= (1 + bpow radix2 (-53)) * (xr * xr)).
{ rewrite Rabs_pos_eq; revert Hv' HS; num; intros; lra. }
assert (Axv : Rabs (xr * v) <= (1 + bpow radix2 (-53)) * (Rabs xr * (xr * xr))).
{ rewrite Rabs_mult.
  replace ((1 + bpow radix2 (-53)) * (Rabs xr * (xr * xr)))
    with (Rabs xr * ((1 + bpow radix2 (-53)) * (xr * xr))) by ring.
  apply Rmult_le_compat_l; [apply Rabs_pos | exact Av]. }
(* [|w| <= (1 + 2^-53) |x v|] and [|w b| <= 0.34 (1 + 2^-53)^2 C]. *)
assert (Aw : Rabs w <= (1 + bpow radix2 (-53)) * Rabs (xr * v)).
{ pose proof (Rabs_triang (xr * v) (w - xr * v)) as T2.
  replace (xr * v + (w - xr * v)) with w in T2 by ring. lra. }
assert (Awb : Rabs (w * b) <=
              (1 + bpow radix2 (-53)) * ((1 + bpow radix2 (-53)) * (Rabs xr * (xr * xr))) *
              (34 / 100)).
{ rewrite Rabs_mult. apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | | exact Hb1].
  apply Rle_trans with (1 := Aw). apply Rmult_le_compat_l; [lra | exact Axv]. }
(* [x^3 p - m = x^3 (p - b) + x b (S - v) + b (x v - w) + (w b - m)],
   one bound for each term. *)
assert (F1 : Rabs (xr * (xr * xr) * (p - b)) <=
             Rabs xr * (xr * xr) * (84 / 100 * bpow radix2 (-53))).
{ rewrite Rabs_mult, Hxs. apply Rmult_le_compat_l; [exact HC0 |].
  rewrite Rabs_minus_sym. exact Hb. }
assert (F2 : Rabs (xr * b * (xr * xr - v)) <=
             Rabs xr * (34 / 100) * (bpow radix2 (-53) * (xr * xr))).
{ rewrite !Rabs_mult.
  apply Rmult_le_compat; [apply Rmult_le_pos; apply Rabs_pos | apply Rabs_pos | |].
  - apply Rmult_le_compat_l; [apply Rabs_pos | exact Hb1].
  - rewrite Rabs_minus_sym. exact Hv. }
assert (F3 : Rabs (b * (xr * v - w)) <=
             34 / 100 * (bpow radix2 (-53) * ((1 + bpow radix2 (-53)) * (Rabs xr * (xr * xr))))).
{ rewrite Rabs_mult. apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hb1 |].
  rewrite Rabs_minus_sym. apply Rle_trans with (1 := Hw).
  apply Rmult_le_compat_l; [lra | exact Axv]. }
assert (F4 : Rabs (w * b - m) <=
             bpow radix2 (-53) *
             ((1 + bpow radix2 (-53)) * ((1 + bpow radix2 (-53)) * (Rabs xr * (xr * xr))) *
              (34 / 100))).
{ rewrite Rabs_minus_sym. apply Rle_trans with (1 := Hm).
  apply Rmult_le_compat_l; [lra | exact Awb]. }
(* The truncation: [|T x^11| <= C S^4 / 11 <= 2^-56 C / 11]. *)
assert (H8 : (xr * xr) ^ 4 <= bpow radix2 (-56)).
{ apply Rle_trans with (bpow radix2 (-14) ^ 4).
  - apply pow_incr. exact HS.
  - cbn [pow]. rewrite Rmult_1_r, <- !bpow_plus. apply bpow_le. lia. }
assert (F5 : Rabs (T * xr ^ 11) <= / 11 * (Rabs xr * (xr * xr) * bpow radix2 (-56))).
{ replace (xr ^ 11) with (xr * (xr * xr) * (xr * xr) ^ 4) by ring.
  rewrite Rabs_mult, (Rabs_pos_eq T) by lra.
  apply Rmult_le_compat; [lra | apply Rabs_pos | apply HT |].
  rewrite Rabs_mult, Hxs, (Rabs_pos_eq ((xr * xr) ^ 4)) by (apply pow_le; apply HS).
  apply Rmult_le_compat_l; [exact HC0 | exact H8]. }
replace (Rabs xr ^ 3) with (Rabs xr * (xr * xr)) by (rewrite ES; ring).
split.
- (* [|m| <= (1 + 2^-53) |w b| <= 0.35 C <= 2^-15 X]. *)
  pose proof (Rabs_triang (w * b) (m - w * b)) as T3.
  replace (w * b + (m - w * b)) with m in T3 by ring.
  revert T3 Hm Awb HC HC0. num. intros. lra.
- (* The sum of the five, [(0.84 + 3 0.34 + 2^-50) 2^-53 + 2^-56 / 11 <=
     1.88 2^-53] of [C]. *)
  apply Rabs_le_inv in F1, F2, F3, F4, F5.
  apply Rabs_le. revert F1 F2 F3 F4 F5 HC0. num. intros. split; lra.
Qed.

Lemma poly9_err :
  forall x, is_finite x = true -> bpow radix2 (-82) <= Rabs (B2R x) <= bpow radix2 (-7) ->
  is_finite (poly9 x) = true /\ Rabs (B2R (poly9 x)) <= bpow radix2 (-15) * Rabs (B2R x) /\
  Rabs (B2R x - B2R (poly9 x) - atan (B2R x)) <= bpow radix2 (-52) * Rabs (B2R x) ^ 3.
Proof.
intros x Fx Hx.
unfold poly9. cbv zeta.
pose proof (bpow_gt_0 radix2 (-82)) as P82.
pose proof (bpow_gt_0 radix2 (-1075)) as P0.
(* [S = x^2 = X^2] is in [[2^-164, 2^-14]]. *)
assert (ES : B2R x * B2R x = Rabs (B2R x) * Rabs (B2R x)).
{ rewrite <- Rabs_mult. symmetry. apply Rabs_pos_eq. pose proof (Rle_0_sqr (B2R x)) as H.
  unfold Rsqr in H. exact H. }
assert (HS : bpow radix2 (-164) <= B2R x * B2R x <= bpow radix2 (-14)).
{ rewrite ES. split.
  - replace (bpow radix2 (-164)) with (bpow radix2 (-82) * bpow radix2 (-82))
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; lra.
  - replace (bpow radix2 (-14)) with (bpow radix2 (-7) * bpow radix2 (-7))
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | lra | lra]. }
pose proof (bpow_gt_0 radix2 (-164)) as P164.
(* [v = RN(S)], within [2^-53 S] as [S] is normal, and at most [2^-14],
   a float, as rounding is monotone. *)
assert (Kv : Rabs (B2R x * B2R x) <= 1)
  by (rewrite Rabs_pos_eq by lra; revert HS; num; intros; lra).
destruct (FastExpErr.mul_k x x 1 Fx Fx Kv ltac:(lra)) as (Fv & Ev & _).
assert (Rv : Rabs (B2R (mul x x) - B2R x * B2R x) <= bpow radix2 (-53) * (B2R x * B2R x)).
{ assert (H := FastAtanPoly.rn_rel (B2R x * B2R x)).
  rewrite (Rabs_pos_eq (B2R x * B2R x)) in H by lra. rewrite Ev. apply H.
  eapply Rle_trans; [| apply HS]. apply bpow_le. lia. }
assert (Bv : 0 <= B2R (mul x x) <= bpow radix2 (-14)).
{ split.
  - pose proof Rv as R. apply Rabs_le_inv in R. revert R HS. num. intros. lra.
  - rewrite Ev. apply round_le_generic; [typeclasses eauto .. | | apply HS].
    apply generic_format_bpow. unfold FLT_exp. lia. }
set (v := mul x x) in *.
(* [B] in [v] by Horner's scheme, innermost first: [q1 = v A9] is within
   [2^-68] of [S/9], [q2 = A7 - q1] within [2^-54] of [1/7 - S/9], and so
   on, with the bound of each exact partial result from the step before;
   [b = A3 - q5] rounds a value near [1/3], adding [2^-53/3] to the
   [2^-54] of [A3]. *)
assert (Hd : Rabs (B2R v - B2R x * B2R x) <= bpow radix2 (-67)).
{ apply Rle_trans with (1 := Rv). revert HS. num. intros. lra. }
assert (Hu : 0 <= B2R x * B2R x <= bpow radix2 (-14)) by lra.
destruct FastAtanPoly.at9_b as (F9 & B9). destruct FastAtanPoly.at7_b as (F7 & B7).
destruct FastAtanPoly.at5_b as (F5 & B5).
destruct FastAtanPoly.at3_b as (F3h & _ & B3h & _ & _).
assert (G9 : Rabs (/ 9) <= / 9) by (rewrite Rabs_pos_eq; lra).
assert (G7 : 0 <= / 7) by lra. assert (G5 : 0 <= / 5) by lra. assert (G3 : 0 <= / 3) by lra.
assert (B3 : Rabs (B2R (from_bits (fst DyadicAtan.A3)) - / 3) <= bpow radix2 (-54))
  by (apply Rabs_le; lra).
destruct (FastAtanPoly.mul_step v _ (B2R x * B2R x) (/ 9) (bpow radix2 (-14))
  (bpow radix2 (-14)) (/ 9) (bpow radix2 (-56)) (bpow radix2 (-67)) (bpow radix2 (-68))
  Fv F9 Bv Hu Hd B9 G9 ltac:(num; lra) ltac:(num; lra)) as (Fq1 & E1 & W1).
set (q1 := mul v (from_bits DyadicAtan.A9)) in *.
destruct (FastAtanPoly.sub_step _ q1 (/ 7) _ _ (bpow radix2 (-56)) (bpow radix2 (-68))
  (bpow radix2 (-54)) F7 Fq1 B7 E1 G7 W1 ltac:(num; lra) ltac:(num; lra)) as (Fq2 & E2 & W2).
set (q2 := sub (from_bits DyadicAtan.A7) q1) in *.
destruct (FastAtanPoly.mul_step v q2 (B2R x * B2R x) _ (bpow radix2 (-14)) (bpow radix2 (-14))
  _ (bpow radix2 (-54)) (bpow radix2 (-67)) (bpow radix2 (-67)) Fv Fq2 Bv Hu Hd E2 W2
  ltac:(num; lra) ltac:(num; lra)) as (Fq3 & E3 & W3).
set (q3 := mul v q2) in *.
destruct (FastAtanPoly.sub_step _ q3 (/ 5) _ _ (bpow radix2 (-56)) (bpow radix2 (-67))
  (bpow radix2 (-54)) F5 Fq3 B5 E3 G5 W3 ltac:(num; lra) ltac:(num; lra)) as (Fq4 & E4 & W4).
set (q4 := sub (from_bits DyadicAtan.A5) q3) in *.
destruct (FastAtanPoly.mul_step v q4 (B2R x * B2R x) _ (bpow radix2 (-14)) (bpow radix2 (-14))
  _ (bpow radix2 (-54)) (bpow radix2 (-67)) (bpow radix2 (-67)) Fv Fq4 Bv Hu Hd E4 W4
  ltac:(num; lra) ltac:(num; lra)) as (Fq5 & E5 & W5).
set (q5 := mul v q4) in *.
destruct (FastAtanPoly.sub_step _ q5 (/ 3) _ _ (bpow radix2 (-54)) (bpow radix2 (-67))
  (84 / 100 * bpow radix2 (-53)) F3h Fq5 B3 E5 G3 W5 ltac:(num; lra) ltac:(num; lra))
  as (Fb & Eb & _).
set (b := sub (from_bits (fst DyadicAtan.A3)) q5) in *.
(* [b] is in [[0.32, 0.34]], as [S (1/5 - ...)] is at most [2^-14 / 4]. *)
pose proof Eb as Eb'. pose proof W5 as W5'. apply Rabs_le_inv in Eb', W5'.
assert (Ab0 : 32 / 100 <= B2R b <= 34 / 100) by (revert Eb' W5'; num; intros; lra).
assert (Ab : 32 / 100 <= Rabs (B2R b) <= 34 / 100) by (rewrite Rabs_pos_eq; lra).
(* [w = RN(x v)], within [2^-53 |x v|]: [|x v|] is in [[2^-247, 2^-21]]. *)
pose proof Rv as Rv'. apply Rabs_le_inv in Rv'.
assert (Av : bpow radix2 (-165) <= Rabs (B2R v) <= bpow radix2 (-14)).
{ rewrite Rabs_pos_eq by lra. split; [revert Rv' HS; num; intros; lra | apply Bv]. }
assert (Axv : bpow radix2 (-247) <= Rabs (B2R x * B2R v) <= bpow radix2 (-21)).
{ rewrite Rabs_mult. split.
  - replace (bpow radix2 (-247)) with (bpow radix2 (-82) * bpow radix2 (-165))
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; [lra | apply bpow_ge_0 | apply Hx | apply Av].
  - replace (bpow radix2 (-21)) with (bpow radix2 (-7) * bpow radix2 (-14))
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | apply Hx | apply Av]. }
destruct (FastExpErr.mul_k x v 1 Fx Fv ltac:(revert Axv; num; intros; lra) ltac:(lra))
  as (Fw & Ew & _).
assert (Rw : Rabs (B2R (mul x v) - B2R x * B2R v) <= bpow radix2 (-53) * Rabs (B2R x * B2R v)).
{ rewrite Ew. apply FastAtanPoly.rn_rel. eapply Rle_trans; [| apply Axv]. apply bpow_le. lia. }
set (w := mul x v) in *.
(* [m = RN(w b)], within [2^-53 |w b|]: [|w| >= 2^-248] and [b >= 0.32]. *)
assert (Aw : bpow radix2 (-248) <= Rabs (B2R w) <= bpow radix2 (-20)).
{ pose proof (Rabs_triang_inv (B2R x * B2R v) (B2R x * B2R v - B2R w)) as T1.
  replace (B2R x * B2R v - (B2R x * B2R v - B2R w)) with (B2R w) in T1 by ring.
  rewrite (Rabs_minus_sym (B2R x * B2R v)) in T1.
  pose proof (Rabs_triang (B2R x * B2R v) (B2R w - B2R x * B2R v)) as T2.
  replace (B2R x * B2R v + (B2R w - B2R x * B2R v)) with (B2R w) in T2 by ring.
  revert T1 T2 Rw Axv. num. intros. lra. }
assert (Awb : bpow radix2 (-1022) <= Rabs (B2R w * B2R b) <= 1).
{ rewrite Rabs_mult. split.
  - apply Rle_trans with (bpow radix2 (-248) * (32 / 100)); [num; lra |].
    apply Rmult_le_compat; [apply bpow_ge_0 | lra | apply Aw | apply Ab].
  - apply Rle_trans with (bpow radix2 (-20) * (34 / 100)); [| num; lra].
    apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | apply Aw | apply Ab]. }
destruct (FastExpErr.mul_k w b 1 Fw Fb ltac:(lra) ltac:(lra)) as (Fm & Em & _).
assert (Rm : Rabs (B2R (mul w b) - B2R w * B2R b) <= bpow radix2 (-53) * Rabs (B2R w * B2R b)).
{ rewrite Em. apply FastAtanPoly.rn_rel. apply Awb. }
set (m := mul w b) in *.
(* The Taylor polynomial of [atan] is [x - x^3 B(S)], within [|x|^11/11]
   ([AtanSeries.atan_tail_bounds]). *)
destruct (atan_tail_bounds 5 (B2R x)) as (T & HT & ET).
change (2 * 5 + 1)%nat with 11%nat in HT, ET.
replace (INR 11) with 11 in HT by (cbn [INR]; ring).
assert (HT' : 0 <= T <= / 11) by lra.
assert (Hsum : atan_sum 5 (B2R x) =
               B2R x - B2R x * (B2R x * B2R x) *
               (/ 3 - B2R x * B2R x * (/ 5 - B2R x * B2R x * (/ 7 - B2R x * B2R x * / 9))))
  by (cbn [atan_sum INR pow Nat.mul Nat.add]; field).
replace (atan (B2R x)) with
  (B2R x - B2R x * (B2R x * B2R x) *
   (/ 3 - B2R x * B2R x * (/ 5 - B2R x * B2R x * (/ 7 - B2R x * B2R x * / 9))) -
   T * B2R x ^ 11)
  by (rewrite <- Hsum, ET; ring).
destruct (p9_assemble (B2R x) (B2R v) (B2R w) (B2R b) (B2R m) _ T Hx Rv Rw Eb
  ltac:(lra) Rm HT') as (A1 & A2).
split; [exact Fm | split; [exact A1 | exact A2]].
Qed.
