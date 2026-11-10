(** * The quotients of the fast paths of [atan] and [atan2]

    The inputs of the core of [FastAtanCore.v] that [FastAtan.v] builds
    from a quotient by [Fast.dd_div]: two significands in [[1, 2)] give a
    double-double within [2^-98] of their quotient, relatively, which is
    in [(1/2, 2)] ([quot_facts]), and which a power of 2 scales exactly
    into the core's range ([scaled_input]); for [1 < t < 2^54], [1 / t]
    is the core's input ([big_input]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Encoding Elementary AtanReal AtanIdent TwoSum DyDriver
  NearF64 NearCells FastRound FastRoundErr FastDiv FastHypPos FastAtanTables FastAtanIdent
  FastAtanCore FastAtanAsm.
From Inari Require DyExp DyPown FastExpErr FastLogReduce AtanSeries.

Open Scope R_scope.

Local Notation G := (generic_format radix2 fexp64).

(** A finite [f64] below 2 is at most [2 - 2^-52], the [f64] before 2. *)
Lemma below_two :
  forall x : f64, is_finite x = true -> B2R x < 2 -> B2R x <= 2 - bpow radix2 (-52).
Proof.
intros x Fx Hx.
assert (P : pred radix2 fexp64 (bpow radix2 1) = 2 - bpow radix2 (-52))
  by (rewrite pred_bpow; reflexivity).
rewrite <- P.
apply pred_ge_gt; [typeclasses eauto | apply generic_format_B2R | | exact Hx].
apply generic_format_bpow. unfold FLT_exp. lia.
Qed.

(** Below [2 - 2^-53], the midpoint of [2 - 2^-52] and 2, [RN] is at most
    [2 - 2^-52]. *)
Lemma rn_below_two :
  forall z, z < 2 - bpow radix2 (-53) -> RN z <= 2 - bpow radix2 (-52).
Proof.
intros z Hz.
assert (G2 : G (bpow radix2 1)) by (apply generic_format_bpow; unfold FLT_exp; lia).
assert (P : pred radix2 fexp64 (bpow radix2 1) = 2 - bpow radix2 (-52))
  by (rewrite pred_bpow; reflexivity).
rewrite <- P.
apply round_N_le_midp; [typeclasses eauto | apply generic_format_pred; [typeclasses eauto | exact G2] |].
rewrite succ_pred by first [exact G2 | typeclasses eauto]. rewrite P.
assert (B : bpow radix2 (-52) = / 4503599627370496 /\ bpow radix2 (-53) = / 9007199254740992)
  by (split; reflexivity).
destruct B as (B1 & B2). rewrite B1. rewrite B2 in Hz.
change (bpow radix2 1) with 2. lra.
Qed.

(** The low part of a rounded-to-nearest normal value is within [2^-53] of
    it relatively (as in [FastAtanCore.v]). *)
Local Lemma low_rel :
  forall x (h : f64), B2R h = RN x -> bpow radix2 (-1022) <= Rabs (B2R h) ->
  Rabs (x - B2R h) <= bpow radix2 (-53) * Rabs (B2R h).
Proof.
intros x h Hh Hb.
rewrite Hh in *.
rewrite <- Rabs_Ropp, Ropp_minus_distr.
apply Rle_trans with (/ 2 * ulp radix2 fexp64 (RN x)).
{ apply error_le_half_ulp_round; typeclasses eauto. }
assert (Hb' : bpow radix2 (-1074 + 53 - 1) <= Rabs (RN x)) by exact Hb.
pose proof (ulp_FLT_le radix2 (-1074) 53 (RN x) Hb') as U.
assert (B : bpow radix2 (1 - 53) = / 4503599627370496 /\ bpow radix2 (-53) = / 9007199254740992)
  by (split; reflexivity).
destruct B as (B1 & B2). rewrite B1 in U. rewrite B2. lra.
Qed.

(** The quotient [mn / md] of two significands in [[1, 2)] by
    [Fast.dd_div], within [2^-98] relatively ([dd_div_correct]), with [qh]
    in [[1/2, 2)] and its low part [ql] within [2^-53] of it. *)
Lemma quot_facts :
  forall fma mn md qh ql,
  is_finite mn = true -> is_finite md = true -> 1 <= B2R mn < 2 -> 1 <= B2R md < 2 ->
  Fast.dd_div fma mn zero md zero = (qh, ql) ->
  is_finite qh = true /\ is_finite ql = true /\ B2R qh = RN (B2R qh + B2R ql) /\
  Rabs (B2R qh + B2R ql - B2R mn / B2R md) <= bpow radix2 (-98) * (B2R mn / B2R md) /\
  / 2 <= B2R qh < 2 /\ Rabs (B2R ql) <= bpow radix2 (-53) * B2R qh /\
  / 2 < B2R mn / B2R md < 2.
Proof.
intros fma mn md qh ql Fmn Fmd Hmn Hmd E.
assert (Fz : is_finite zero = true) by reflexivity.
assert (Ez : B2R zero = 0) by reflexivity.
assert (H80 : bpow radix2 (-80) <= 1) by (apply (bpow_le radix2 (-80) 0); lia).
pose proof (bpow_gt_0 radix2 (-50)) as P50.
pose proof (bpow_gt_0 radix2 (-52)) as P52.
assert (HN : bpow radix2 (-80) <= B2R mn <= 4) by lra.
assert (HL : Rabs (B2R zero) <= bpow radix2 (-50) * B2R mn)
  by (rewrite Ez, Rabs_R0; apply Rmult_le_pos; lra).
assert (HD : / 2 <= B2R md <= 4) by lra.
assert (HE : Rabs (B2R zero) <= bpow radix2 (-52) * B2R md)
  by (rewrite Ez, Rabs_R0; apply Rmult_le_pos; lra).
pose proof (dd_div_correct fma mn zero md zero Fmn Fz Fmd Fz HN HL HD HE) as D.
rewrite E in D. destruct D as (Fq & Fl & Rq & Hq).
rewrite Ez, !Rplus_0_r in Hq.
set (r := B2R mn / B2R md) in *.
(* Both significands are at most [2 - 2^-52], so [r] is in
   [[1 / (2 - 2^-52), 2 - 2^-52]]. *)
pose proof (below_two mn Fmn (proj2 Hmn)) as Bn.
pose proof (below_two md Fmd (proj2 Hmd)) as Bd.
assert (B : bpow radix2 (-52) = / 4503599627370496 /\ bpow radix2 (-53) = / 9007199254740992 /\
  bpow radix2 (-98) = / 316912650057057350374175801344) by (repeat split; reflexivity).
destruct B as (B52 & B53 & B98).
assert (Er : r * B2R md = B2R mn) by (unfold r; field; lra).
assert (Hr0 : 0 < r) by (unfold r; apply Rdiv_lt_0_compat; lra).
assert (Hr1 : r <= B2R mn) by nra.
rewrite B52 in Bn, Bd.
assert (Hr2 : 1 <= r * (2 - / 4503599627370496)) by nra.
rewrite B98 in Hq.
apply Rabs_le_inv in Hq.
assert (Hlo : / 2 <= B2R qh + B2R ql) by lra.
assert (Hhi : B2R qh + B2R ql < 2 - / 9007199254740992) by lra.
assert (Hqh : / 2 <= B2R qh).
{ rewrite Rq. apply round_ge_generic; [typeclasses eauto .. | | exact Hlo].
  change (/ 2) with (bpow radix2 (-1)). apply generic_format_bpow. unfold FLT_exp. lia. }
assert (Hqh2 : B2R qh < 2).
{ rewrite Rq. apply Rle_lt_trans with (2 - bpow radix2 (-52)); [| rewrite B52; lra].
  apply rn_below_two. rewrite B53. exact Hhi. }
split; [exact Fq |]. split; [exact Fl |]. split; [exact Rq |].
split; [rewrite B98; apply Rabs_le; lra |].
split; [split; assumption |]. split; [| split; lra].
assert (Hb : bpow radix2 (-1022) <= Rabs (B2R qh)).
{ rewrite Rabs_pos_eq by lra. apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia |].
  change (bpow radix2 (-1)) with (/ 2). exact Hqh. }
pose proof (low_rel (B2R qh + B2R ql) qh Rq Hb) as L.
replace (B2R qh + B2R ql - B2R qh) with (B2R ql) in L by ring.
rewrite (Rabs_pos_eq (B2R qh)) in L by lra. exact L.
Qed.

(** [(qh + ql) 2^j], for [qh + ql] within [2^-98] of [r] and [r 2^j <= 1],
    is the core's input: [qh 2^j] is exact, and the error of [ql 2^j] is
    far below [2^-96 r 2^j]. *)
Lemma scaled_input :
  forall qh ql r j,
  is_finite qh = true -> is_finite ql = true ->
  Rabs (B2R qh + B2R ql - r) <= bpow radix2 (-98) * r ->
  / 2 <= B2R qh < 2 -> Rabs (B2R ql) <= bpow radix2 (-53) * B2R qh ->
  (-60 <= j <= 0)%Z -> r * bpow radix2 j <= 1 ->
  let th := mul qh (DyadicExp.two_pow j) in
  let tl := mul ql (DyadicExp.two_pow j) in
  is_finite th = true /\ is_finite tl = true /\
  bpow radix2 (-61) <= B2R th <= 129 / 128 /\ Rabs (B2R tl) <= bpow radix2 (-53) * B2R th /\
  Rabs (B2R th + B2R tl - r * bpow radix2 j) <= bpow radix2 (-96) * (r * bpow radix2 j).
Proof.
intros qh ql r j Fh Fl Hq Hh Hl Hj HrJ. cbv zeta.
assert (Hj' : (-1022 <= j <= 1023)%Z) by lia.
assert (Fp : is_finite (DyadicExp.two_pow j) = true /\ B2R (DyadicExp.two_pow j) = bpow radix2 j)
  by exact (pow2_bits j Hj').
destruct Fp as (Fp & Rp).
(* [qh 2^j] is exact ([scale] multiplies by the same power of 2). *)
change (mul qh (DyadicExp.two_pow j)) with (Fast.scale qh j).
destruct (scale_correct qh j Fh ltac:(lra) ltac:(lia)) as (Fth & Rth).
set (J := bpow radix2 j) in *.
assert (HJ0 : 0 < J) by apply bpow_gt_0.
assert (HJ1 : J <= 1) by (apply (bpow_le radix2 j 0); lia).
assert (HJ60 : bpow radix2 (-60) <= J) by (apply bpow_le; lia).
assert (B : bpow radix2 (-53) = / 9007199254740992 /\
  bpow radix2 (-61) = / 2305843009213693952 /\ bpow radix2 (-60) = / 1152921504606846976 /\
  bpow radix2 (-62) = / 4611686018427387904 /\
  bpow radix2 (-96) = / 79228162514264337593543950336 /\
  bpow radix2 (-98) = / 316912650057057350374175801344 /\
  bpow radix2 (-200) = / 1606938044258990275541962092341162602522202993782792835301376)
  by (repeat split; reflexivity).
destruct B as (B53 & B61 & B60 & B62 & B96 & B98 & B200).
(* [ql 2^j] is rounded to nearest, with an absolute error of [2^-1075]
   when it is subnormal. *)
assert (HQ : Rabs (B2R ql * B2R (DyadicExp.two_pow j)) <= 16).
{ rewrite Rp, Rabs_mult, (Rabs_pos_eq J) by lra.
  rewrite B53 in Hl. apply Rle_trans with (1 * 1); [| lra].
  apply Rmult_le_compat; [apply Rabs_pos | lra | lra | exact HJ1]. }
destruct (FastExpErr.mul_e ql (DyadicExp.two_pow j) Fl Fp HQ) as (Ftl & Etl & Htl).
rewrite Rp in Etl, Htl.
(* The error of [qh + ql] times [2^j]. *)
assert (T2 : Rabs (B2R qh * J + B2R ql * J - r * J) <= bpow radix2 (-98) * (r * J)).
{ replace (B2R qh * J + B2R ql * J - r * J) with ((B2R qh + B2R ql - r) * J) by ring.
  rewrite Rabs_mult, (Rabs_pos_eq J) by lra. rewrite <- Rmult_assoc.
  apply Rmult_le_compat_r; [lra | exact Hq]. }
assert (HQJ : Rabs (B2R ql * J) <= bpow radix2 (-53) * (B2R qh * J)).
{ rewrite Rabs_mult, (Rabs_pos_eq J) by lra. rewrite <- Rmult_assoc.
  apply Rmult_le_compat_r; [lra | exact Hl]. }
assert (HX : bpow radix2 (-61) <= B2R qh * J).
{ replace (bpow radix2 (-61)) with (/ 2 * bpow radix2 (-60))
    by (rewrite B61, B60; field).
  apply Rmult_le_compat; [lra | apply bpow_ge_0 | lra | exact HJ60]. }
(* [|tl| <= 2^-53 th]: [2^-53 th] is a float that bounds [|ql 2^j|], and
   rounding to nearest keeps the bound. *)
assert (TL : Rabs (B2R (mul ql (DyadicExp.two_pow j))) <= bpow radix2 (-53) * (B2R qh * J)).
{ rewrite Etl. apply abs_round_le_generic; [typeclasses eauto .. | | exact HQJ].
  replace (bpow radix2 (-53) * (B2R qh * J)) with (B2R qh * bpow radix2 (j + -53))
    by (rewrite bpow_plus; unfold J; ring).
  apply format_shift; [apply generic_format_B2R | rewrite Rabs_pos_eq; lra | lia]. }
split; [exact Fth |]. split; [exact Ftl |]. rewrite Rth.
set (X := B2R qh * J) in *. set (QJ := B2R ql * J) in *. set (RJ := r * J) in *.
clearbody X QJ RJ.
pose proof (Rabs_le_inv _ _ HQJ) as HQJ'. pose proof (Rabs_le_inv _ _ T2) as T2'.
apply Rabs_le_inv in Htl. pose proof (Rabs_pos QJ) as HQ0.
rewrite B53 in HQJ, HQJ', Htl, TL. rewrite B61 in HX. rewrite B98 in T2'.
rewrite B96, B53, B61.
assert (HXR : X * (1 - / 9007199254740992) <= RJ * (1 + / 316912650057057350374175801344))
  by lra.
(* [2^-1075] is far below [2^-200 RJ], as [RJ] is at least [2^-62]. *)
assert (HE : bpow radix2 (-1075) <=
  / 1606938044258990275541962092341162602522202993782792835301376 * RJ).
{ assert (R62 : bpow radix2 (-62) <= RJ) by (rewrite B62; lra).
  rewrite <- B200.
  apply Rle_trans with (bpow radix2 (-200) * bpow radix2 (-62));
    [rewrite <- bpow_plus; apply bpow_le; lia |].
  apply Rmult_le_compat_l; [apply bpow_ge_0 | exact R62]. }
split; [split; lra |]. split; [exact TL |].
apply Rabs_le. lra.
Qed.

(** For [1 < t < 2^54], the significand [m] of [t] and the input of the
    core at [1 / t = (1 / m) 2^-k]. *)
Lemma big_input :
  forall fma t m k qh ql,
  is_finite t = true -> 1 < B2R t < bpow radix2 54 ->
  DyadicAtan.split t = (m, k) -> Fast.dd_div fma DyadicExp.one zero m zero = (qh, ql) ->
  is_finite m = true /\ 1 <= B2R m < 2 /\
  let th := mul qh (DyadicExp.two_pow (- k)) in
  let tl := mul ql (DyadicExp.two_pow (- k)) in
  is_finite th = true /\ is_finite tl = true /\
  bpow radix2 (-61) <= B2R th <= 129 / 128 /\ Rabs (B2R tl) <= bpow radix2 (-53) * B2R th /\
  Rabs (B2R th + B2R tl - 1 / B2R t) <= bpow radix2 (-96) * (1 / B2R t).
Proof.
intros fma t m k qh ql Ft Ht Es Ed.
pose proof (FastAtanAsm.split_correct t Ft ltac:(lra)) as S.
rewrite Es in S. destruct S as (Fm & Hm & Etm & _).
pose proof (bpow_gt_0 radix2 k) as Pk.
(* [t = m 2^k] with [1 <= m < 2] and [1 < t < 2^54] gives [0 <= k <= 53]. *)
assert (Hk0 : (0 <= k)%Z).
{ destruct (Z_lt_le_dec k 0) as [Hlt | Hle]; [exfalso | exact Hle].
  assert (B : bpow radix2 k <= / 2)
    by (change (/ 2) with (bpow radix2 (-1)); apply bpow_le; lia).
  nra. }
assert (Hk53 : (k < 54)%Z).
{ apply (lt_bpow radix2). nra. }
destruct FastLogReduce.one_R as (F1 & E1).
destruct (quot_facts fma DyadicExp.one m qh ql F1 Fm ltac:(rewrite E1; lra) Hm Ed)
  as (Fq & Fl & Rq & Hq & Hqh & Hql & Hr).
rewrite E1 in Hq, Hr.
assert (Hinv : 1 / B2R m <= 1).
{ unfold Rdiv. rewrite Rmult_1_l.
  apply Rle_trans with (/ 1); [apply Rinv_le_contravar; lra | rewrite Rinv_1; lra]. }
assert (HJ : 1 / B2R m * bpow radix2 (- k) <= 1).
{ apply Rle_trans with (1 * 1); [| lra].
  apply Rmult_le_compat; [lra | apply bpow_ge_0 | exact Hinv |].
  apply (bpow_le radix2 (- k) 0). lia. }
pose proof (scaled_input qh ql (1 / B2R m) (- k) Fq Fl Hq Hqh Hql ltac:(lia) HJ) as S.
assert (Hr1 : 1 / B2R m * bpow radix2 (- k) = 1 / B2R t)
  by (rewrite Etm, bpow_opp; field; lra).
cbv zeta in S |- *. rewrite Hr1 in S.
split; [exact Fm |]. split; [exact Hm | exact S].
Qed.
