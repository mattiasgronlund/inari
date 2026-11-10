(** * The real-number steps of the fast paths of [asin] and [acos]

    Facts that [FastAsinSqrt.v], [FastAsinQuot.v] and [FastAsin.v] use: a
    float below 1 is at most [1 - 2^-53] ([below_one]), a normal [RN x]
    is within [2^-53 |RN x|] of [x] ([low_rel]), a quotient whose
    denominator errs by [k <= 1/2], or whose numerator errs by [k],
    relatively, errs by at most [2k] or [k] ([div_den], [div_num]), and a
    double-double within [2^-96 q] of a [q] in [[2^-27, 1.0003]] is an
    input of the core of [FastAtanCore.v] ([quot_tail]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Sterbenz.
From Inari Require Import Model Mpfr Elementary AtanReal AtanIdent TwoSum TwoProduct DyDriver
  NearF64 NearCells FastRound FastRoundErr FastDiv FastHypPos FastAtanTables FastAtanIdent
  FastAtanCore FastAtanAsm FastDdSqrt.
From Inari Require DyExp DyPown DyAtanTiny DyExpRules FastExpErr MulRuTiny FastLogNorm.

Open Scope R_scope.

(** A float below [1] is at most [pred 1 = 1 - 2^-53]. *)
Lemma below_one :
  forall t : f64, is_finite t = true -> B2R t < 1 -> B2R t <= 1 - bpow radix2 (-53).
Proof.
intros t _ Ht.
rewrite <- DyExpRules.pred_one.
apply pred_ge_gt; [typeclasses eauto | apply generic_format_B2R | exact format_one | lra].
Qed.

(** [low_rel] of [FastAtanCore.v]: a normal [RN x] is within [2^-53] of
    [x], relative to it. *)
Lemma low_rel :
  forall x (h : f64), B2R h = RN x -> bpow radix2 (-1022) <= Rabs (B2R h) ->
  Rabs (x - B2R h) <= bpow radix2 (-53) * Rabs (B2R h).
Proof.
intros x h Hh Hb.
rewrite Hh in *.
rewrite <- Rabs_Ropp, Ropp_minus_distr.
apply Rle_trans with (/ 2 * ulp radix2 (FLT_exp (-1074) 53) (RN x)).
{ apply error_le_half_ulp_round; typeclasses eauto. }
assert (Hb' : bpow radix2 (-1074 + 53 - 1) <= Rabs (RN x)) by exact Hb.
pose proof (ulp_FLT_le radix2 (-1074) 53 (RN x) Hb') as U.
assert (B : bpow radix2 (1 - 53) = / 4503599627370496 /\ bpow radix2 (-53) = / 9007199254740992)
  by (split; reflexivity).
destruct B as (B1 & B2). rewrite B1 in U. rewrite B2. lra.
Qed.

(** [a / B] for [B] within [k <= 1/2] of [b], relative to [b]. *)
Lemma div_den :
  forall a b B k, 0 <= a -> 0 < b -> 0 <= k <= / 2 -> Rabs (B - b) <= k * b ->
  Rabs (a / B - a / b) <= 2 * k * (a / b).
Proof.
intros a b B k Ha Hb Hk H.
(* [b - B <= k b <= b/2], so [B >= b/2 > 0]. *)
assert (HB : b <= 2 * B).
{ pose proof (Rle_abs (b - B)) as A. rewrite Rabs_minus_sym in A.
  assert (k * b <= / 2 * b) by (apply Rmult_le_compat_r; lra). lra. }
(* [a/B - a/b = (a/b) (b - B)/B], and [|b - B| <= k b <= 2 k B]. *)
replace (a / B - a / b) with (a / b * ((b - B) / B))
  by (field; split; apply Rgt_not_eq; lra).
assert (Hab : 0 <= a / b)
  by (unfold Rdiv; apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra]).
assert (Hq : Rabs ((b - B) / B) <= 2 * k).
{ unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ B)) by (left; apply Rinv_0_lt_compat; lra).
  rewrite Rabs_minus_sym.
  apply Rmult_le_reg_r with B; [lra |].
  rewrite Rmult_assoc, Rinv_l by (apply Rgt_not_eq; lra). rewrite Rmult_1_r.
  assert (0 <= k * (2 * B - b)) by (apply Rmult_le_pos; lra). lra. }
rewrite Rabs_mult, (Rabs_pos_eq (a / b)) by exact Hab.
rewrite (Rmult_comm (a / b)).
apply Rmult_le_compat_r; [exact Hab | exact Hq].
Qed.

(** [a / d] for [a] within [k] of [b], relative to [b / d]. *)
Lemma div_num :
  forall a b d k, 0 < d -> Rabs (a - b) <= k * b -> Rabs (a / d - b / d) <= k * (b / d).
Proof.
intros a b d k Hd H.
replace (a / d - b / d) with ((a - b) * / d) by (unfold Rdiv; ring).
rewrite Rabs_mult, (Rabs_pos_eq (/ d)) by (left; apply Rinv_0_lt_compat; exact Hd).
unfold Rdiv. rewrite <- Rmult_assoc.
apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact Hd | exact H].
Qed.

(** A double-double within [2^-96] of [q] is the input [fast_atan_core]
    takes. *)
Lemma quot_tail :
  forall (qh ql : f64) q,
  B2R qh = RN (B2R qh + B2R ql) -> bpow radix2 (-27) <= q <= 10003 / 10000 ->
  Rabs (B2R qh + B2R ql - q) <= bpow radix2 (-96) * q ->
  bpow radix2 (-61) <= B2R qh <= 129 / 128 /\ Rabs (B2R ql) <= bpow radix2 (-53) * B2R qh.
Proof.
intros qh ql q Hh [Hq0 Hq1] He.
assert (K27 : bpow radix2 (-27) = / 134217728) by reflexivity.
assert (K52 : bpow radix2 (-52) = / 4503599627370496) by reflexivity.
assert (K61 : bpow radix2 (-61) = / 2305843009213693952) by reflexivity.
assert (K96 : bpow radix2 (-96) = / 79228162514264337593543950336) by reflexivity.
pose proof (bpow_gt_0 radix2 (-61)) as P61.
rewrite K27 in Hq0. rewrite K96 in He.
apply Rabs_le_inv in He.
(* [qh + ql] is within [2^-96] of [q], so in [[2^-28, 1.0004]], and [qh =
   RN(qh + ql)] is at least the float [2^-61] and at most [qh + ql + 2^-52]. *)
assert (Hlo : bpow radix2 (-61) <= B2R qh).
{ rewrite Hh. apply round_ge_generic;
    [typeclasses eauto .. | apply generic_format_bpow; unfold FLT_exp; lia | rewrite K61; lra]. }
assert (Hhi : B2R qh <= 129 / 128).
{ assert (K1 : bpow radix2 (-52 + 53) = 2) by reflexivity.
  assert (A : Rabs (B2R qh + B2R ql) <= bpow radix2 (-52 + 53))
    by (rewrite K1, Rabs_pos_eq by lra; lra).
  pose proof (rn_err _ (-52) ltac:(lia) A) as R.
  rewrite <- Hh, K52 in R. apply Rabs_le_inv in R. lra. }
split; [split; assumption |].
(* [ql = (qh + ql) - RN(qh + ql)] ([low_rel]). *)
assert (Hb : bpow radix2 (-1022) <= Rabs (B2R qh)).
{ rewrite Rabs_pos_eq by lra.
  apply Rle_trans with (2 := Hlo). apply bpow_le. lia. }
pose proof (low_rel (B2R qh + B2R ql) qh Hh Hb) as L.
replace (B2R qh + B2R ql - B2R qh) with (B2R ql) in L by ring.
rewrite (Rabs_pos_eq (B2R qh)) in L by lra.
exact L.
Qed.
