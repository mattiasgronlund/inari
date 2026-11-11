(** * The correction of the series of [acosh] near 1

    [DyadicLog.fast_acosh_near1] of [Model.v] computes [acosh x] for
    [1 < x < 1 + 2^-8] as [2 asinh s] with [s = sqrt u] and
    [u = (x - 1)/2], and [asinh s] as [s (1 + W(u))], where
    [W(u) = -u/6 + 3u^2/40 - 5u^3/112 + 35u^4/1152 - 63u^5/2816 +
    231u^6/13312 - 143u^7/10240] holds the terms of degree 1 to 7 in [u]
    of the Taylor series of [asinh s / s - 1]. This file proves the steps
    that do not involve [s]:
    - [near1_u]: [u] is exact, as [x - 1] is (Sterbenz's lemma) and so is
      halving it, and [2^-53 <= u < 2^-9].
    - [near1_w]: [W(u)] as the double-double [wl - mh]. [mh = RN(u c3)],
      with [c3] the high part of [SH3] (about [1/6]), and [ml = u c3 - mh]
      exactly ([Generic.two_prod_err]: Dekker's product or an FMA,
      [two_prod_err_correct]). [wl = r - (ml + u c3l)], with [c3l] the low
      part of [SH3] and [r = RN(u^2) p] for [p] Horner's scheme of
      [W(u)/u^2 + 1/(6u)] with [f64] coefficients, so [wl - mh] is
      [r - u (c3 + c3l)] up to roundings. It is within [2^-71] of [W(u)].
    - [near1_ml_fma]: [ml] is the same [f64] with or without an FMA. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Sterbenz Mult_error.
From Inari Require Import Model Encoding TwoSum TwoProduct FastExpErr.
From Inari Require FastRound MulRuTiny.

Open Scope R_scope.

Local Notation format := (generic_format radix2 fexp64).

(** ** Literals *)

(** [B2R l] of an [f64] literal [l] in the goal, as [m * 2^e] (as
    [lit_R] of [FastSinhHorner.v]). *)
Local Ltac lit_R l :=
  rewrite <- (SF2R_B2SF _ _ l);
  let s := eval vm_compute in (B2SF l) in
  replace (B2SF l) with s by (vm_compute; reflexivity);
  cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR.

(** Powers of 2 as numerals, for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp].

Local Lemma one_F : is_finite DyadicExp.one = true /\ B2R DyadicExp.one = 1.
Proof.
split; [vm_compute; reflexivity|]. lit_R DyadicExp.one. num. lra.
Qed.

Local Lemma half_F : is_finite DyadicLog.half = true /\ B2R DyadicLog.half = / 2.
Proof.
split; [vm_compute; reflexivity|]. lit_R DyadicLog.half. num. lra.
Qed.

(** [SH3] is the double-double [1/3!] within [2^-110]: its high part is
    [1/6 - 2^-55/3], and its low part is at most [2^-56] (as [sh3_b] of
    [FastSinhHorner.v]). *)
Local Lemma sh3_b :
  is_finite (from_bits (fst DyadicExp.SH3)) = true /\
  is_finite (from_bits (snd DyadicExp.SH3)) = true /\
  / 6 - bpow radix2 (-54) <= B2R (from_bits (fst DyadicExp.SH3)) <= / 6 /\
  Rabs (B2R (from_bits (snd DyadicExp.SH3))) <= bpow radix2 (-56) /\
  Rabs (B2R (from_bits (fst DyadicExp.SH3)) + B2R (from_bits (snd DyadicExp.SH3)) - / 6)
    <= bpow radix2 (-110).
Proof.
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
lit_R (from_bits (fst DyadicExp.SH3)). lit_R (from_bits (snd DyadicExp.SH3)). num.
split; [lra|]. split; apply Rabs_le; lra.
Qed.

(** The coefficients [A5] to [A15] are [3/40], [-5/112], [35/1152],
    [-63/2816], [231/13312] and [-143/10240] within [2^-57]. *)
Local Ltac coef c :=
  split; [vm_compute; reflexivity|]; lit_R (from_bits c); num; apply Rabs_le; lra.

Local Lemma a5_b :
  is_finite (from_bits DyadicLog.A5) = true /\
  Rabs (B2R (from_bits DyadicLog.A5) - 3 / 40) <= bpow radix2 (-57).
Proof. coef DyadicLog.A5. Qed.

Local Lemma a7_b :
  is_finite (from_bits DyadicLog.A7) = true /\
  Rabs (B2R (from_bits DyadicLog.A7) - (- 5 / 112)) <= bpow radix2 (-57).
Proof. coef DyadicLog.A7. Qed.

Local Lemma a9_b :
  is_finite (from_bits DyadicLog.A9) = true /\
  Rabs (B2R (from_bits DyadicLog.A9) - 35 / 1152) <= bpow radix2 (-57).
Proof. coef DyadicLog.A9. Qed.

Local Lemma a11_b :
  is_finite (from_bits DyadicLog.A11) = true /\
  Rabs (B2R (from_bits DyadicLog.A11) - (- 63 / 2816)) <= bpow radix2 (-57).
Proof. coef DyadicLog.A11. Qed.

Local Lemma a13_b :
  is_finite (from_bits DyadicLog.A13) = true /\
  Rabs (B2R (from_bits DyadicLog.A13) - 231 / 13312) <= bpow radix2 (-57).
Proof. coef DyadicLog.A13. Qed.

Local Lemma a15_b :
  is_finite (from_bits DyadicLog.A15) = true /\
  Rabs (B2R (from_bits DyadicLog.A15) - (- 143 / 10240)) <= bpow radix2 (-57).
Proof. coef DyadicLog.A15. Qed.

(** ** Horner's scheme

    A step [x q] or [c + q] of the scheme (as [od_mul] and [od_add] of
    [FastAhypOdd.v]), with [x] within [dl] of [v], [q] within [D] of [y]
    and [c] within [G] of [g], is within [D'] of [v y] or [g + y]: the
    rounding of an exact result of at most [K] adds [2^-53 K + 2^-1075]. *)

Local Lemma n1_mul :
  forall x q v y U Y D dl D',
  is_finite x = true -> is_finite q = true ->
  Rabs (B2R x) <= U -> Rabs v <= U -> Rabs (B2R x - v) <= dl ->
  Rabs (B2R q - y) <= D -> Rabs y <= Y -> U * (Y + D) <= 16 ->
  bpow radix2 (-53) * (U * (Y + D)) + bpow radix2 (-1075) + U * D + dl * Y <= D' ->
  is_finite (mul x q) = true /\ Rabs (B2R (mul x q) - v * y) <= D' /\
  Rabs (v * y) <= U * Y.
Proof.
intros x q v y U Y D dl D' Fx Fq Hx Hv Hd Hq Hy HYD HD.
assert (Aq : Rabs (B2R q) <= Y + D).
{ apply Rabs_le_inv in Hq. apply Rabs_le_inv in Hy. apply Rabs_le. lra. }
assert (Hm : Rabs (B2R x * B2R q) <= U * (Y + D)) by (apply Rabs_mul_le; assumption).
destruct (mul_k x q (U * (Y + D)) Fx Fq Hm HYD) as (F & _ & B).
(* [x q - v y = x (q - y) + (x - v) y]. *)
assert (H1 : Rabs (B2R x * (B2R q - y)) <= U * D) by (apply Rabs_mul_le; assumption).
assert (H2 : Rabs ((B2R x - v) * y) <= dl * Y) by (apply Rabs_mul_le; assumption).
assert (H3 : Rabs (v * y) <= U * Y) by (apply Rabs_mul_le; assumption).
apply Rabs_le_inv in B, H1, H2.
split; [exact F | split; [apply Rabs_le; lra | exact H3]].
Qed.

Local Lemma n1_add :
  forall c q g y K G D D',
  is_finite c = true -> is_finite q = true ->
  Rabs (B2R c - g) <= G -> Rabs (B2R q - y) <= D -> Rabs (g + y) <= K -> K + G + D <= 16 ->
  bpow radix2 (-53) * (K + G + D) + bpow radix2 (-1075) + G + D <= D' ->
  is_finite (add c q) = true /\ Rabs (B2R (add c q) - (g + y)) <= D'.
Proof.
intros c q g y K G D D' Fc Fq Hc Hq Hs HK HD.
apply Rabs_le_inv in Hc, Hq, Hs.
assert (Hm : Rabs (B2R c + B2R q) <= K + G + D) by (apply Rabs_le; lra).
destruct (add_k c q (K + G + D) Fc Fq Hm HK) as (F & _ & B).
apply Rabs_le_inv in B.
split; [exact F | apply Rabs_le; lra].
Qed.

(** [|g + y| <= K] from [|y| <= Y] and [-K <= g - Y], [g + Y <= K]. *)
Local Lemma n1_sum :
  forall g y Y K, Rabs y <= Y -> - K <= g - Y -> g + Y <= K -> Rabs (g + y) <= K.
Proof.
intros g y Y K Hy H1 H2. apply Rabs_le_inv in Hy. apply Rabs_le. lra.
Qed.

(** The [f64] Horner scheme of [fast_acosh_near1] in [u]. *)
Local Definition n1_p (u : f64) : f64 :=
  add (from_bits DyadicLog.A5) (mul u (add (from_bits DyadicLog.A7)
    (mul u (add (from_bits DyadicLog.A9) (mul u (add (from_bits DyadicLog.A11)
    (mul u (add (from_bits DyadicLog.A13) (mul u (from_bits DyadicLog.A15)))))))))).

(** The polynomial it evaluates: [W(v) = -v/6 + v^2 n1_P(v)]. *)
Local Definition n1_P (v : R) : R :=
  3 / 40 + v * (- 5 / 112 + v * (35 / 1152 + v * (- 63 / 2816 + v * (231 / 13312 +
  v * (- 143 / 10240))))).

(** [p] is within [2^-55] of [n1_P(u)]: its last sum, about [3/40], adds
    [2^-53/13], [A5] adds [2^-57], and the other steps are scaled by
    [u <= 2^-9]. *)
Local Lemma n1_horner :
  forall u, is_finite u = true -> 0 <= B2R u <= bpow radix2 (-9) ->
  is_finite (n1_p u) = true /\ Rabs (B2R (n1_p u) - n1_P (B2R u)) <= bpow radix2 (-55) /\
  Rabs (n1_P (B2R u)) <= / 13.
Proof.
intros u Fu Hu.
destruct a5_b as (F5 & B5). destruct a7_b as (F7 & B7). destruct a9_b as (F9 & B9).
destruct a11_b as (F11 & B11). destruct a13_b as (F13 & B13). destruct a15_b as (F15 & B15).
assert (Au : Rabs (B2R u) <= bpow radix2 (-9)) by (rewrite Rabs_pos_eq; lra).
assert (Z : Rabs (B2R u - B2R u) <= 0)
  by (replace (B2R u - B2R u) with 0 by ring; rewrite Rabs_R0; lra).
(* Innermost first: each step's error bound and the bound of its exact
   value. *)
destruct (n1_mul u _ (B2R u) _ (bpow radix2 (-9)) (/ 64) (bpow radix2 (-57)) 0
  (bpow radix2 (-65)) Fu F15 Au Au Z B15 ltac:(apply Rabs_le; lra) ltac:(num; lra)
  ltac:(num; lra)) as (Fm1 & Em1 & Wm1).
pose proof (n1_sum (231 / 13312) _ _ (/ 32) Wm1 ltac:(num; lra) ltac:(num; lra)) as S2.
destruct (n1_add _ _ _ _ (/ 32) (bpow radix2 (-57)) (bpow radix2 (-65)) (bpow radix2 (-56))
  F13 Fm1 B13 Em1 S2 ltac:(num; lra) ltac:(num; lra)) as (Fa2 & Ea2).
destruct (n1_mul u _ (B2R u) _ (bpow radix2 (-9)) (/ 32) (bpow radix2 (-56)) 0
  (bpow radix2 (-64)) Fu Fa2 Au Au Z Ea2 S2 ltac:(num; lra) ltac:(num; lra))
  as (Fm3 & Em3 & Wm3).
pose proof (n1_sum (- 63 / 2816) _ _ (/ 32) Wm3 ltac:(num; lra) ltac:(num; lra)) as S4.
destruct (n1_add _ _ _ _ (/ 32) (bpow radix2 (-57)) (bpow radix2 (-64)) (bpow radix2 (-56))
  F11 Fm3 B11 Em3 S4 ltac:(num; lra) ltac:(num; lra)) as (Fa4 & Ea4).
destruct (n1_mul u _ (B2R u) _ (bpow radix2 (-9)) (/ 32) (bpow radix2 (-56)) 0
  (bpow radix2 (-64)) Fu Fa4 Au Au Z Ea4 S4 ltac:(num; lra) ltac:(num; lra))
  as (Fm5 & Em5 & Wm5).
pose proof (n1_sum (35 / 1152) _ _ (/ 32) Wm5 ltac:(num; lra) ltac:(num; lra)) as S6.
destruct (n1_add _ _ _ _ (/ 32) (bpow radix2 (-57)) (bpow radix2 (-64)) (bpow radix2 (-56))
  F9 Fm5 B9 Em5 S6 ltac:(num; lra) ltac:(num; lra)) as (Fa6 & Ea6).
destruct (n1_mul u _ (B2R u) _ (bpow radix2 (-9)) (/ 32) (bpow radix2 (-56)) 0
  (bpow radix2 (-64)) Fu Fa6 Au Au Z Ea6 S6 ltac:(num; lra) ltac:(num; lra))
  as (Fm7 & Em7 & Wm7).
pose proof (n1_sum (- 5 / 112) _ _ (/ 16) Wm7 ltac:(num; lra) ltac:(num; lra)) as S8.
destruct (n1_add _ _ _ _ (/ 16) (bpow radix2 (-57)) (bpow radix2 (-64)) (bpow radix2 (-55))
  F7 Fm7 B7 Em7 S8 ltac:(num; lra) ltac:(num; lra)) as (Fa8 & Ea8).
destruct (n1_mul u _ (B2R u) _ (bpow radix2 (-9)) (/ 16) (bpow radix2 (-55)) 0
  (bpow radix2 (-63)) Fu Fa8 Au Au Z Ea8 S8 ltac:(num; lra) ltac:(num; lra))
  as (Fm9 & Em9 & Wm9).
pose proof (n1_sum (3 / 40) _ _ (/ 13) Wm9 ltac:(num; lra) ltac:(num; lra)) as S10.
destruct (n1_add _ _ _ _ (/ 13) (bpow radix2 (-57)) (bpow radix2 (-63)) (bpow radix2 (-55))
  F5 Fm9 B5 Em9 S10 ltac:(num; lra) ltac:(num; lra)) as (Fp & Ep).
split; [exact Fp | split; [exact Ep | exact S10]].
Qed.

(** ** The product [u c3] *)

(** [mh = RN(u c3)] is between [2^-57] and [2^-11], within [2^-64] of
    [u c3]. *)
Local Lemma n1_mh :
  forall u, is_finite u = true -> bpow radix2 (-53) <= B2R u < bpow radix2 (-9) ->
  is_finite (mul u (from_bits (fst DyadicExp.SH3))) = true /\
  bpow radix2 (-57) <= B2R (mul u (from_bits (fst DyadicExp.SH3))) <= bpow radix2 (-11) /\
  Rabs (B2R (mul u (from_bits (fst DyadicExp.SH3))) -
    B2R u * B2R (from_bits (fst DyadicExp.SH3))) <= bpow radix2 (-64).
Proof.
intros u Fu Hu.
destruct sh3_b as (F3h & _ & B3h & _ & _).
pose proof (bpow_gt_0 radix2 (-53)) as P53.
assert (N : 0 <= / 6 - bpow radix2 (-54)) by (num; lra).
assert (L : bpow radix2 (-53) * (/ 6 - bpow radix2 (-54)) <=
  B2R u * B2R (from_bits (fst DyadicExp.SH3))) by (apply Rmult_le_compat; lra).
assert (U : B2R u * B2R (from_bits (fst DyadicExp.SH3)) <= bpow radix2 (-9) * / 6)
  by (apply Rmult_le_compat; lra).
assert (K : Rabs (B2R u * B2R (from_bits (fst DyadicExp.SH3))) <= bpow radix2 (-9) * / 6)
  by (rewrite Rabs_pos_eq by (apply Rmult_le_pos; lra); exact U).
destruct (mul_k _ _ _ Fu F3h K ltac:(num; lra)) as (F & _ & B).
split; [exact F|].
apply Rabs_le_inv in B. revert L U B. num. intros L U B.
split; [split; lra | apply Rabs_le; lra].
Qed.

(** Both variants of [two_prod_is_exact] hold for [u c3] (as
    [two_prod_is_exact_of] of [FastDdSqrt.v]). *)
Local Lemma n1_tpe :
  forall fma u, is_finite u = true -> bpow radix2 (-53) <= B2R u < bpow radix2 (-9) ->
  Generic.two_prod_is_exact fma u (from_bits (fst DyadicExp.SH3))
    (mul u (from_bits (fst DyadicExp.SH3))) = true.
Proof.
intros fma u Fu Hu.
destruct sh3_b as (F3h & _ & B3h & _ & _).
destruct (n1_mh u Fu Hu) as (Fmh & Hmh & _).
pose proof (bpow_gt_0 radix2 (-57)) as P57.
pose proof (bpow_gt_0 radix2 (-53)) as P53.
assert (Ep : (-968 <= Generic.exponent (mul u (from_bits (fst DyadicExp.SH3))) <= 1022)%Z).
{ split.
  - apply MulRuTiny.exponent_ge; [exact Fmh |].
    rewrite Rabs_pos_eq by lra.
    apply Rle_trans with (bpow radix2 (-57)); [apply bpow_le; lia | lra].
  - apply Z.lt_le_incl, MulRuTiny.exponent_lt; [exact Fmh | lia |].
    rewrite Rabs_pos_eq by lra.
    apply Rle_lt_trans with (bpow radix2 (-11)); [lra | apply bpow_lt; lia]. }
assert (Eu : (Generic.exponent u <= 995)%Z).
{ apply Z.lt_le_incl, MulRuTiny.exponent_lt; [exact Fu | lia |].
  rewrite Rabs_pos_eq by lra.
  apply Rlt_trans with (bpow radix2 (-9)); [lra | apply bpow_lt; lia]. }
assert (Ec : (Generic.exponent (from_bits (fst DyadicExp.SH3)) <= 995)%Z).
{ apply Z.lt_le_incl, MulRuTiny.exponent_lt; [exact F3h | lia |].
  rewrite Rabs_pos_eq by (revert B3h; num; intros; lra).
  apply Rle_lt_trans with (bpow radix2 0); [num; lra | apply bpow_lt; lia]. }
destruct fma; cbv beta iota zeta delta [Generic.two_prod_is_exact];
  repeat (apply andb_true_intro; split); apply Z.leb_le; lia.
Qed.

(** ** The theorems *)

Local Lemma format_bpow64 : forall e, (-1074 <= e)%Z -> format (bpow radix2 e).
Proof. intros e He. apply generic_format_bpow. unfold FLT_exp. lia. Qed.

(** [u = (x - 1)/2] is exact: [x - 1] by Sterbenz's lemma, and its half as
    [x - 1 >= 2^-52] is far from the subnormals. *)
Lemma near1_u : forall x, is_finite x = true -> 1 < B2R x < 1 + bpow radix2 (-8) ->
  is_finite (mul DyadicLog.half (sub x DyadicExp.one)) = true /\
  B2R (mul DyadicLog.half (sub x DyadicExp.one)) = (B2R x - 1) / 2 /\
  bpow radix2 (-53) <= B2R (mul DyadicLog.half (sub x DyadicExp.one)) < bpow radix2 (-9).
Proof.
intros x Fx Hx.
destruct one_F as (F1 & E1). destruct half_F as (Fh & Eh).
assert (B8 : bpow radix2 (-8) <= / 256) by (num; lra).
(* [x >= succ 1 = 1 + 2^-52] *)
assert (HX1 : 1 + bpow radix2 (-52) <= B2R x).
{ assert (S : succ radix2 fexp64 1 <= B2R x).
  { apply succ_le_lt; [typeclasses eauto | exact (format_bpow64 0 ltac:(lia)) |
      apply generic_format_B2R | lra]. }
  rewrite succ_eq_pos in S by lra.
  replace (ulp radix2 fexp64 1) with (bpow radix2 (-52)) in S; [lra |].
  change 1 with (bpow radix2 0). rewrite ulp_bpow. reflexivity. }
(* [x - 1] is exact (Sterbenz), as [1/2 <= x <= 2]. *)
assert (Gd : format (B2R x - 1)).
{ apply sterbenz; try typeclasses eauto.
  - apply generic_format_B2R.
  - exact (format_bpow64 0 ltac:(lia)).
  - lra. }
destruct (sub_below_max x DyadicExp.one Fx F1) as (Fd & Ed & _).
{ rewrite E1. apply small_le_max. apply Rabs_le. lra. }
rewrite E1, round_generic in Ed by (try typeclasses eauto; exact Gd).
set (d := sub x DyadicExp.one) in *.
assert (Hm : Rabs (B2R DyadicLog.half * B2R d) <= 1).
{ rewrite Eh, Ed, Rabs_pos_eq by lra. lra. }
destruct (mul_k DyadicLog.half d 1 Fh Fd Hm ltac:(lra)) as (Fm & Em & _).
(* Halving [x - 1 >= 2^-52] is exact. *)
assert (Ev : B2R (mul DyadicLog.half d) = (B2R x - 1) / 2).
{ rewrite Em, Eh, Ed.
  assert (G : format ((B2R x - 1) * bpow radix2 (-1))).
  { apply mult_bpow_exact_FLT; [exact Gd |].
    assert (M : (-51 <= mag radix2 (B2R x - 1))%Z).
    { apply mag_ge_bpow. rewrite Rabs_pos_eq by lra.
      change (-51 - 1)%Z with (-52)%Z. lra. }
    lia. }
  change (bpow radix2 (-1)) with (/ 2) in G.
  rewrite Rmult_comm. unfold Rdiv. apply round_generic; [typeclasses eauto | exact G]. }
split; [exact Fm|]. split; [exact Ev|]. rewrite Ev.
revert HX1 Hx. num. intros. lra.
Qed.

(** [W(u)] as the double-double [wl - mh]: [-mh + (r - ml - u c3l)] is
    [r - u (c3 + c3l)] up to the roundings of [u c3l], of its sum with
    [ml] and of [wl], where [c3 + c3l] is within [2^-110] of [1/6] and [r]
    within [2^-72] of [u^2 n1_P(u)]. *)
Lemma near1_w : forall fma u mh ml r wl,
  is_finite u = true -> bpow radix2 (-53) <= B2R u < bpow radix2 (-9) ->
  mh = mul u (from_bits (fst DyadicExp.SH3)) ->
  ml = Generic.two_prod_err fma u (from_bits (fst DyadicExp.SH3)) mh ->
  r = mul (mul u u) (add (from_bits DyadicLog.A5) (mul u (add (from_bits DyadicLog.A7)
        (mul u (add (from_bits DyadicLog.A9) (mul u (add (from_bits DyadicLog.A11)
        (mul u (add (from_bits DyadicLog.A13) (mul u (from_bits DyadicLog.A15))))))))))) ->
  wl = sub r (add ml (mul u (from_bits (snd DyadicExp.SH3)))) ->
  is_finite mh = true /\ is_finite wl = true /\
  bpow radix2 (-57) <= B2R mh <= bpow radix2 (-11) /\ Rabs (B2R wl) <= bpow radix2 (-21) /\
  Rabs (B2R wl - B2R mh - (- B2R u / 6 + 3 * B2R u ^ 2 / 40 - 5 * B2R u ^ 3 / 112
    + 35 * B2R u ^ 4 / 1152 - 63 * B2R u ^ 5 / 2816 + 231 * B2R u ^ 6 / 13312
    - 143 * B2R u ^ 7 / 10240)) <= bpow radix2 (-71).
Proof.
intros fma u mh ml r wl Fu Hu Emh Eml Er Ewl.
pose proof (bpow_gt_0 radix2 (-53)) as P53.
assert (Hu' : 0 <= B2R u <= bpow radix2 (-9)) by lra.
assert (Au : Rabs (B2R u) <= bpow radix2 (-9)) by (rewrite Rabs_pos_eq; lra).
destruct sh3_b as (F3h & F3l & B3h & B3l & B3).
(* [mh = RN(u c3)], and [ml = u c3 - mh] exactly. *)
destruct (n1_mh u Fu Hu) as (Fmh & Hmh & Bmh).
destruct (two_prod_err_correct fma u _ Fu F3h (n1_tpe fma u Fu Hu))
  as (_ & _ & _ & Fml & Eml').
rewrite <- Emh in Fmh, Hmh, Bmh, Fml, Eml'. rewrite <- Eml in Fml, Eml'.
set (c3 := from_bits (fst DyadicExp.SH3)) in *.
set (c3l := from_bits (snd DyadicExp.SH3)) in *.
(* [r = RN(RN(u^2) p)] is within [2^-72] of [u^2 n1_P(u)]. *)
destruct (n1_horner u Fu Hu') as (Fp & Ep & Wp).
assert (Er' : r = mul (mul u u) (n1_p u)) by exact Er.
clear Er.
set (p := n1_p u) in *.
assert (Huu : Rabs (B2R u * B2R u) <= bpow radix2 (-9) * bpow radix2 (-9))
  by (apply Rabs_mul_le; exact Au).
destruct (mul_k u u _ Fu Fu Huu ltac:(num; lra)) as (Fuu & _ & Buu).
set (uu := mul u u) in *.
assert (Ap : Rabs (B2R p) <= / 13 + bpow radix2 (-55)).
{ pose proof Ep as E'. pose proof Wp as W'. apply Rabs_le_inv in E', W'.
  apply Rabs_le. lra. }
assert (Auu : Rabs (B2R uu) <= bpow radix2 (-9) * bpow radix2 (-9) +
  (bpow radix2 (-53) * (bpow radix2 (-9) * bpow radix2 (-9)) + bpow radix2 (-1075))).
{ pose proof Buu as B'. pose proof Huu as H'. apply Rabs_le_inv in B', H'.
  apply Rabs_le. lra. }
assert (Hup : Rabs (B2R uu * B2R p) <= 5 * bpow radix2 (-24)).
{ eapply Rle_trans; [apply Rabs_mul_le; [exact Auu | exact Ap] |]. num. lra. }
destruct (mul_k uu p _ Fuu Fp Hup ltac:(num; lra)) as (Fr & _ & Br).
rewrite <- Er' in Fr, Br.
(* [q = RN(ml + RN(u c3l))], with [|ml| <= 2^-64] and [|u c3l| <= 2^-65]. *)
assert (Hqq : Rabs (B2R u * B2R c3l) <= bpow radix2 (-9) * bpow radix2 (-56))
  by (apply Rabs_mul_le; [exact Au | exact B3l]).
destruct (mul_k u c3l _ Fu F3l Hqq ltac:(num; lra)) as (Fqq & _ & Bqq).
set (qq := mul u c3l) in *.
assert (Hq : Rabs (B2R ml + B2R qq) <= bpow radix2 (-63)).
{ rewrite Eml'. pose proof Bmh as B1. pose proof Bqq as B2. pose proof Hqq as B4.
  apply Rabs_le_inv in B1, B2, B4. apply Rabs_le. revert B1 B2 B4. num. intros. lra. }
destruct (add_k ml qq _ Fml Fqq Hq ltac:(num; lra)) as (Fq & _ & Bq).
set (q := add ml qq) in *.
(* [wl = RN(r - q)]. *)
assert (Hw : Rabs (B2R r - B2R q) <= 5 * bpow radix2 (-24) + bpow radix2 (-62)).
{ pose proof Br as B1. pose proof Hup as B2. pose proof Bq as B5. pose proof Hq as B4.
  apply Rabs_le_inv in B1, B2, B5, B4. apply Rabs_le. revert B1 B2 B5 B4. num. intros.
  lra. }
destruct (sub_k r q _ Fr Fq Hw ltac:(num; lra)) as (Fw & _ & Bw).
rewrite <- Ewl in Fw, Bw.
split; [exact Fmh|]. split; [exact Fw|]. split; [exact Hmh|]. split.
{ pose proof Bw as B1. pose proof Hw as B2. apply Rabs_le_inv in B1, B2. apply Rabs_le.
  revert B1 B2. num. intros. lra. }
(* The products that the error terms leave. *)
assert (T1 : Rabs ((B2R uu - B2R u * B2R u) * B2R p) <=
  (bpow radix2 (-53) * (bpow radix2 (-9) * bpow radix2 (-9)) + bpow radix2 (-1075)) *
  (/ 13 + bpow radix2 (-55))) by (apply Rabs_mul_le; [exact Buu | exact Ap]).
assert (T2 : Rabs (B2R u * B2R u * (B2R p - n1_P (B2R u))) <=
  bpow radix2 (-9) * bpow radix2 (-9) * bpow radix2 (-55))
  by (apply Rabs_mul_le; [exact Huu | exact Ep]).
assert (T3 : Rabs (B2R u * (B2R c3 + B2R c3l - / 6)) <= bpow radix2 (-9) * bpow radix2 (-110))
  by (apply Rabs_mul_le; [exact Au | exact B3]).
match goal with
| |- Rabs ?E <= _ =>
  replace E with ((B2R wl - (B2R r - B2R q)) + (B2R r - B2R uu * B2R p)
    + (B2R uu - B2R u * B2R u) * B2R p + B2R u * B2R u * (B2R p - n1_P (B2R u))
    - (B2R q - (B2R ml + B2R qq)) - (B2R qq - B2R u * B2R c3l)
    - B2R u * (B2R c3 + B2R c3l - / 6)) by (rewrite Eml'; unfold n1_P; field)
end.
apply Rabs_le_inv in Bw, Br, T1, T2, Bq, Bqq, T3. apply Rabs_le.
revert Bw Br T1 T2 Bq Bqq T3. num. intros. lra.
Qed.

(** [ml] is the same [f64] whether [Generic.two_prod_err] uses an FMA or
    Dekker's product. *)
Lemma near1_ml_fma : forall u, is_finite u = true -> bpow radix2 (-53) <= B2R u < bpow radix2 (-9) ->
  Generic.two_prod_err true u (from_bits (fst DyadicExp.SH3)) (mul u (from_bits (fst DyadicExp.SH3))) =
  Generic.two_prod_err false u (from_bits (fst DyadicExp.SH3)) (mul u (from_bits (fst DyadicExp.SH3))).
Proof.
intros u Fu Hu.
destruct sh3_b as (F3h & _).
apply FastRound.two_prod_err_fma_eq;
  [exact Fu | exact F3h | exact (n1_tpe true u Fu Hu) | exact (n1_tpe false u Fu Hu)].
Qed.
