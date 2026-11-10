(** * The Horner part of the Taylor polynomial of [sinh]

    [DyadicExp.fast_sinh_poly] of [Model.v] writes the odd Taylor
    polynomial of [sinh t] as [t + t^3 (1/3! + u shA u)] with [u = t^2],
    where [shA u = 1/5! + u/7! + ... + u^5/15!]. Its [f64] Horner scheme [a]
    in [uh], the rounding of [t^2], is within [3 * 2^-61] of [shA u]
    ([sh_horner]), and the double-double [bh + bl] of [1/3! + uh a] is
    within [2^-62 + 2^-100] of [1/3! + u shA u] ([sh_b]). [dd_out] bounds
    the low part of a double-double result. [FastHypPoly.v] assembles
    them. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error Relative.
From Inari Require Import Model Mpfr Encoding Elementary TwoSum TwoProduct DyDriver NearF64
  FastRound FastExpErr CancelLanes MulRuTiny.

Open Scope R_scope.

(** ** Literals and rounding errors *)

(** [B2R l] of an [f64] literal [l] in the goal, as [m * 2^e] (as
    [lit_R] of [FastCoshPoly.v]). *)
Local Ltac lit_R l :=
  rewrite <- (SF2R_B2SF _ _ l);
  let s := eval vm_compute in (B2SF l) in
  replace (B2SF l) with s by (vm_compute; reflexivity);
  cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR.

(** Powers of 2 as numerals, for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp].

(** Rounding to nearest of an [x] of at least [2^-1022] in magnitude moves
    it by at most [2^-53 |x|] (the first case of [rn_err] of
    [FastExpErr.v]). *)
Local Lemma rn_rel :
  forall x, bpow radix2 (-1022) <= Rabs x -> Rabs (RN x - x) <= bpow radix2 (-53) * Rabs x.
Proof.
intros x Hx.
assert (H : Rabs (RN x - x) <= / 2 * bpow radix2 (- 53 + 1) * Rabs x)
  by exact (relative_error_N_FLT radix2 (-1074) 53 eq_refl (fun z => negb (Z.even z)) x Hx).
change (- 53 + 1)%Z with (-52)%Z in H.
assert (E : / 2 * bpow radix2 (-52) = bpow radix2 (-53))
  by (cbn [bpow radix_val radix2]; lra).
rewrite E in H. exact H.
Qed.

(** The part of the Taylor polynomial of [sinh] after [t^3/3!], divided by
    [t^5], in [u = t^2]. *)
Definition shA (u : R) : R :=
  / 120 + u * (/ 5040 + u * (/ 362880 + u * (/ 39916800 + u * (/ 6227020800 +
  u * / 1307674368000)))).

(** The coefficients [SH5] to [SH15] are [1/5!] to [1/15!] within
    [2^-62], [2^-72], [2^-72], [2^-79], [2^-85] and [2^-96]. *)
Local Ltac coef c :=
  split; [vm_compute; reflexivity|]; lit_R (from_bits c); num; apply Rabs_le; lra.

Local Lemma sh5_b :
  is_finite (from_bits DyadicExp.SH5) = true /\
  Rabs (B2R (from_bits DyadicExp.SH5) - / 120) <= bpow radix2 (-62).
Proof. coef DyadicExp.SH5. Qed.

Local Lemma sh7_b :
  is_finite (from_bits DyadicExp.SH7) = true /\
  Rabs (B2R (from_bits DyadicExp.SH7) - / 5040) <= bpow radix2 (-72).
Proof. coef DyadicExp.SH7. Qed.

Local Lemma sh9_b :
  is_finite (from_bits DyadicExp.SH9) = true /\
  Rabs (B2R (from_bits DyadicExp.SH9) - / 362880) <= bpow radix2 (-72).
Proof. coef DyadicExp.SH9. Qed.

Local Lemma sh11_b :
  is_finite (from_bits DyadicExp.SH11) = true /\
  Rabs (B2R (from_bits DyadicExp.SH11) - / 39916800) <= bpow radix2 (-79).
Proof. coef DyadicExp.SH11. Qed.

Local Lemma sh13_b :
  is_finite (from_bits DyadicExp.SH13) = true /\
  Rabs (B2R (from_bits DyadicExp.SH13) - / 6227020800) <= bpow radix2 (-85).
Proof. coef DyadicExp.SH13. Qed.

Local Lemma sh15_b :
  is_finite (from_bits DyadicExp.SH15) = true /\
  Rabs (B2R (from_bits DyadicExp.SH15) - / 1307674368000) <= bpow radix2 (-96).
Proof. coef DyadicExp.SH15. Qed.

(** [SH3] is the double-double [1/3!] within [2^-110]: its high part is
    [1/6 - 2^-55/3], and its low part is at most [2^-56]. *)
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

(** ** Horner's scheme

    A step [x q] or [c + q] of the scheme, with [x] within [dl] of [u], [q]
    within [D] of [y] and [c] within [G] of [g], is within [D'] of [u y] or
    [g + y]: the rounding of an exact result of at most [K] adds [2^-53 K +
    2^-1075]. *)

Local Lemma mul_step :
  forall x q u y Y D dl D',
  is_finite x = true -> is_finite q = true ->
  0 <= B2R x <= / 16 -> 0 <= u <= / 16 -> Rabs (B2R x - u) <= dl ->
  Rabs (B2R q - y) <= D -> Rabs y <= Y -> Y + D <= 16 ->
  bpow radix2 (-53) * ((Y + D) / 16) + bpow radix2 (-1075) + D / 16 + dl * Y <= D' ->
  is_finite (mul x q) = true /\ Rabs (B2R (mul x q) - u * y) <= D' /\
  Rabs (u * y) <= Y / 16.
Proof.
intros x q u y Y D dl D' Fx Fq Hx Hu Hd Hq Hy HYD HD.
assert (Ax : Rabs (B2R x) <= / 16) by (rewrite Rabs_pos_eq; lra).
assert (Au : Rabs u <= / 16) by (rewrite Rabs_pos_eq; lra).
assert (Aq : Rabs (B2R q) <= Y + D).
{ apply Rabs_le_inv in Hq. apply Rabs_le_inv in Hy. apply Rabs_le. lra. }
assert (Hm : Rabs (B2R x * B2R q) <= (Y + D) / 16).
{ eapply Rle_trans; [apply Rabs_mul_le; [exact Ax | exact Aq] | lra]. }
destruct (mul_k x q ((Y + D) / 16) Fx Fq Hm ltac:(lra)) as (F & _ & B).
(* [x q - u y = x (q - y) + (x - u) y]. *)
assert (H1 : Rabs (B2R x * (B2R q - y)) <= / 16 * D) by (apply Rabs_mul_le; assumption).
assert (H2 : Rabs ((B2R x - u) * y) <= dl * Y) by (apply Rabs_mul_le; assumption).
assert (H3 : Rabs (u * y) <= / 16 * Y) by (apply Rabs_mul_le; assumption).
apply Rabs_le_inv in B, H1, H2.
split; [exact F | split; [apply Rabs_le; lra | lra]].
Qed.

Local Lemma add_step :
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

(** [|g + y| <= K] from [|y| <= Y] and a positive [g]. *)
Local Lemma sum_le :
  forall g y Y K, 0 <= g -> Rabs y <= Y -> g + Y <= K -> Rabs (g + y) <= K.
Proof.
intros g y Y K Hg Hy HK. apply Rabs_le_inv in Hy. apply Rabs_le. lra.
Qed.

(** The Horner scheme of [fast_sinh_poly] in an [uh] within [2^-56] of
    [u]. *)
Lemma sh_horner :
  forall uh u,
  is_finite uh = true -> 0 <= B2R uh <= / 16 -> 0 <= u <= / 16 ->
  Rabs (B2R uh - u) <= bpow radix2 (-56) ->
  let a := add (from_bits DyadicExp.SH5) (mul uh (add (from_bits DyadicExp.SH7)
             (mul uh (add (from_bits DyadicExp.SH9) (mul uh (add (from_bits DyadicExp.SH11)
             (mul uh (add (from_bits DyadicExp.SH13) (mul uh (from_bits DyadicExp.SH15)))))))))) in
  is_finite a = true /\ Rabs (B2R a - shA u) <= 3 * bpow radix2 (-61) /\
  Rabs (shA u) <= / 119.
Proof.
intros uh u Fu Hu Hu0 Hd a.
destruct sh5_b as (F5 & B5). destruct sh7_b as (F7 & B7). destruct sh9_b as (F9 & B9).
destruct sh11_b as (F11 & B11). destruct sh13_b as (F13 & B13). destruct sh15_b as (F15 & B15).
assert (G13 : 0 <= / 6227020800) by lra. assert (G11 : 0 <= / 39916800) by lra.
assert (G9 : 0 <= / 362880) by lra. assert (G7 : 0 <= / 5040) by lra.
assert (G5 : 0 <= / 120) by lra.
(* Each step, innermost first: its error bound [D'] and the bound [K] of
   the exact partial sum. *)
destruct (mul_step uh _ u _ (bpow radix2 (-40)) _ _ (bpow radix2 (-95)) Fu F15 Hu Hu0 Hd B15
  ltac:(rewrite Rabs_pos_eq by lra; num; lra) ltac:(num; lra) ltac:(num; lra))
  as (Fq1 & E1 & W1).
pose proof (sum_le _ _ _ (bpow radix2 (-32)) G13 W1 ltac:(num; lra)) as S2.
destruct (add_step _ _ _ _ (bpow radix2 (-32)) _ _ (bpow radix2 (-83)) F13 Fq1 B13 E1 S2
  ltac:(num; lra) ltac:(num; lra)) as (Fq2 & E2).
destruct (mul_step uh _ u _ (bpow radix2 (-32)) _ _ (bpow radix2 (-86)) Fu Fq2 Hu Hu0 Hd E2 S2
  ltac:(num; lra) ltac:(num; lra)) as (Fq3 & E3 & W3).
pose proof (sum_le _ _ _ (bpow radix2 (-25)) G11 W3 ltac:(num; lra)) as S4.
destruct (add_step _ _ _ _ (bpow radix2 (-25)) _ _ (bpow radix2 (-77)) F11 Fq3 B11 E3 S4
  ltac:(num; lra) ltac:(num; lra)) as (Fq4 & E4).
destruct (mul_step uh _ u _ (bpow radix2 (-25)) _ _ (bpow radix2 (-79)) Fu Fq4 Hu Hu0 Hd E4 S4
  ltac:(num; lra) ltac:(num; lra)) as (Fq5 & E5 & W5).
pose proof (sum_le _ _ _ (bpow radix2 (-18)) G9 W5 ltac:(num; lra)) as S6.
destruct (add_step _ _ _ _ (bpow radix2 (-18)) _ _ (bpow radix2 (-70)) F9 Fq5 B9 E5 S6
  ltac:(num; lra) ltac:(num; lra)) as (Fq6 & E6).
destruct (mul_step uh _ u _ (bpow radix2 (-18)) _ _ (bpow radix2 (-72)) Fu Fq6 Hu Hu0 Hd E6 S6
  ltac:(num; lra) ltac:(num; lra)) as (Fq7 & E7 & W7).
pose proof (sum_le _ _ _ (bpow radix2 (-12)) G7 W7 ltac:(num; lra)) as S8.
destruct (add_step _ _ _ _ (bpow radix2 (-12)) _ _ (bpow radix2 (-64)) F7 Fq7 B7 E7 S8
  ltac:(num; lra) ltac:(num; lra)) as (Fq8 & E8).
destruct (mul_step uh _ u _ (bpow radix2 (-12)) _ _ (bpow radix2 (-66)) Fu Fq8 Hu Hu0 Hd E8 S8
  ltac:(num; lra) ltac:(num; lra)) as (Fq9 & E9 & W9).
pose proof (sum_le _ _ _ (/ 119) G5 W9 ltac:(num; lra)) as Sa.
destruct (add_step _ _ _ _ (/ 119) _ _ (3 * bpow radix2 (-61)) F5 Fq9 B5 E9 Sa
  ltac:(num; lra) ltac:(num; lra)) as (Fa & Ea).
split; [exact Fa | split; [exact Ea | exact Sa]].
Qed.

(** The double-double [bh + bl] of [1/3! + uh a] in [fast_sinh_poly]. *)
Lemma sh_b :
  forall uh u,
  is_finite uh = true -> 0 <= B2R uh <= / 16 -> 0 <= u <= / 16 ->
  Rabs (B2R uh - u) <= bpow radix2 (-57) ->
  let a := add (from_bits DyadicExp.SH5) (mul uh (add (from_bits DyadicExp.SH7)
             (mul uh (add (from_bits DyadicExp.SH9) (mul uh (add (from_bits DyadicExp.SH11)
             (mul uh (add (from_bits DyadicExp.SH13) (mul uh (from_bits DyadicExp.SH15)))))))))) in
  let '(bh, b0) := Fast.fast_two_sum (from_bits (fst DyadicExp.SH3)) (mul uh a) in
  let bl := add b0 (from_bits (snd DyadicExp.SH3)) in
  is_finite bh = true /\ is_finite bl = true /\ / 8 <= B2R bh <= / 4 /\
  Rabs (B2R bl) <= bpow radix2 (-53) /\
  Rabs (B2R bh + B2R bl - (/ 6 + u * shA u)) <= bpow radix2 (-62) + bpow radix2 (-100).
Proof.
intros uh u Fu Hu Hu0 Hd a.
pose proof (bpow_gt_0 radix2 (-1075)) as P0.
assert (Hd' : Rabs (B2R uh - u) <= bpow radix2 (-56))
  by (eapply Rle_trans; [exact Hd | apply bpow_le; lia]).
pose proof (sh_horner uh u Fu Hu Hu0 Hd') as Hh.
change (is_finite a = true /\ Rabs (B2R a - shA u) <= 3 * bpow radix2 (-61) /\
  Rabs (shA u) <= / 119) in Hh.
clearbody a. destruct Hh as (Fa & Ea & Wa).
destruct sh3_b as (F3h & F3l & B3h & B3l & B3).
(* [m = uh a] is within [2^-62] of [u shA u], which is at most [1/1904]. *)
destruct (mul_step uh a u (shA u) (/ 119) (3 * bpow radix2 (-61)) (bpow radix2 (-57))
  (bpow radix2 (-62)) Fu Fa Hu Hu0 Hd Ea Wa ltac:(num; lra) ltac:(num; lra))
  as (Fm & Em & Wm).
unfold Fast.fast_two_sum. cbv beta iota zeta.
set (h := from_bits (fst DyadicExp.SH3)) in *.
set (l := from_bits (snd DyadicExp.SH3)) in *.
set (m := mul uh a) in *.
assert (Am : Rabs (B2R m) <= / 1900).
{ pose proof Em as E'. pose proof Wm as W'. apply Rabs_le_inv in E', W'.
  apply Rabs_le. revert E' W'. num. intros. lra. }
(* [bh] rounds [h + m], which is about [1/6]. *)
assert (Hs : Rabs (B2R h + B2R m) <= / 5).
{ pose proof Am as A'. apply Rabs_le_inv in A'. apply Rabs_le. revert B3h A'. num. intros.
  lra. }
destruct (add_k h m (/ 5) F3h Fm Hs ltac:(lra)) as (Fbh & Ebh & Bbh).
set (bh := add h m) in *.
(* Fast2Sum applies, as [|m| <= 1/1900 <= h], so [b0] is the exact error
   [h + m - bh], at most [2^-53/5 + 2^-1075] (Dekker 1971). *)
assert (Hle : Rabs (B2R m) <= Rabs (B2R h)).
{ rewrite (Rabs_pos_eq (B2R h)) by (revert B3h; num; intros; lra).
  revert B3h Am. num. intros. lra. }
destruct (CancelLanes.fast_two_sum h m bh F3h Fm Hle Fbh Ebh) as (Fb0 & Eb0).
set (b0 := add m (sub h bh)) in *.
pose proof Bbh as Bbh'. apply Rabs_le_inv in Bbh'.
assert (Ab0 : Rabs (B2R b0) <= bpow radix2 (-55)).
{ rewrite Eb0. apply Rabs_le. revert Bbh'. num. intros. lra. }
(* [bl] rounds [b0 + l], at most [2^-55 + 2^-56]. *)
assert (Hs2 : Rabs (B2R b0 + B2R l) <= bpow radix2 (-54)).
{ pose proof Ab0 as A'. pose proof B3l as L'. apply Rabs_le_inv in A', L'. apply Rabs_le.
  revert A' L'. num. intros. lra. }
destruct (add_k b0 l (bpow radix2 (-54)) Fb0 F3l Hs2 ltac:(num; lra)) as (Fbl & _ & Bbl).
set (bl := add b0 l) in *.
split; [exact Fbh|]. split; [exact Fbl|].
pose proof Am as Am'. pose proof Hs2 as Hs2'. pose proof Em as Em'. pose proof B3 as B3'.
apply Rabs_le_inv in Am', Hs2', Em', B3', Bbl.
split; [revert B3h Am' Bbh'; num; intros; lra|].
split; [apply Rabs_le; revert Hs2' Bbl; num; intros; lra|].
(* [bh + bl - (1/6 + u shA u)] is [(h + l - 1/6) + (m - u shA u)] plus
   the rounding error of [bl]. *)
apply Rabs_le. revert Eb0 Em' B3' Bbl. num. intros. lra.
Qed.

(** A double-double [rh + rl] in [[2^-27, 1/2]], with [rh] the rounding of
    [rh + rl] to nearest: [rh] is in the same range and [rl] is at most
    [2^-52 rh]. *)
Lemma dd_out :
  forall rh rl : f64,
  is_finite rh = true -> is_finite rl = true -> B2R rh = RN (B2R rh + B2R rl) ->
  bpow radix2 (-27) <= B2R rh + B2R rl <= / 2 ->
  bpow radix2 (-27) <= B2R rh <= / 2 /\ Rabs (B2R rl) <= bpow radix2 (-52) * B2R rh.
Proof.
intros rh rl _ _ Eh Hx.
pose proof (bpow_gt_0 radix2 (-27)) as P27.
(* [2^-27] and [1/2] are [f64]s, so the rounding [rh] stays between them. *)
assert (L : bpow radix2 (-27) <= B2R rh).
{ rewrite Eh. apply round_ge_generic; [typeclasses eauto .. | | lra].
  apply generic_format_bpow. unfold FLT_exp. lia. }
assert (U : B2R rh <= / 2).
{ rewrite Eh. replace (/ 2) with (bpow radix2 (-1)) by (num; lra).
  apply round_le_generic; [typeclasses eauto .. | | num; lra].
  apply generic_format_bpow. unfold FLT_exp. lia. }
split; [lra|].
(* [rl] is the error of rounding [rh + rl], at most [2^-53 (rh + rl)]. *)
assert (R : Rabs (RN (B2R rh + B2R rl) - (B2R rh + B2R rl)) <=
            bpow radix2 (-53) * Rabs (B2R rh + B2R rl)).
{ apply rn_rel. rewrite Rabs_pos_eq by lra.
  eapply Rle_trans; [| exact (proj1 Hx)]. apply bpow_le. lia. }
rewrite <- Eh in R.
replace (B2R rh - (B2R rh + B2R rl)) with (- B2R rl) in R by ring.
rewrite Rabs_Ropp, (Rabs_pos_eq (B2R rh + B2R rl)) in R by lra.
(* So [|rl| <= 2^-53 (rh + |rl|)], and [|rl| <= 2^-52 rh]. *)
pose proof (Rle_abs (B2R rl)) as A.
revert R A L. num. intros. lra.
Qed.
