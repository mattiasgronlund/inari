(** * The fast path of [asinh] before the rounding, for [t >= 2^-8]

    [DyadicLog.fast_asinh_pos] of [Model.v] computes [asinh t = ln(t + c)]
    with [c = sqrt(1 + t^2)] in double-double ([Fast.dd_sqrt],
    [FastDdSqrt.v]), where [1 + t^2] is exact up to one rounding of
    [2^-105 (1 + t^2)]: as [ln(t + c)] up to [2^26]
    ([fast_ln_dd_correct] with [e0 = 0]), and
    from [2^26] on as [ln 2 + ln(t + RN(1/(4t)))], since
    [0 <= (1 + s/2) - sqrt(1 + s) <= s^2/8] for [s = 1/t^2] puts
    [2 (t + 1/(4t))] within [2^-106] of [t + c], relatively.
    [fast_asinh_pos_correct] shows that the result is within [2^-68] of
    [asinh t 2^-k], with [1/2 < |h| < 2]. *)

From Stdlib Require Import ZArith Reals Lra Lia Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error Sterbenz.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct FastRound FastRoundErr
  FastDiv FastDdSqrt FastLogTables FastLogPoly FastLogCore FastLogNorm FastLogFin FastLogDd
  FastExpErr.
From Inari Require FastLogReduce FastHypPos CancelLanes DyLogRules.
From Flocq Require Import Relative.

Open Scope R_scope.

Local Notation format := (generic_format radix2 fexp64).

(** The value of a literal (as in [FastHypPos.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

Local Ltac lit_pow2 :=
  lit_B2R; change (IZR 4503599627370496) with (bpow radix2 52); rewrite <- bpow_plus;
  reflexivity.

Local Lemma lit_large : B2R DyadicLog.ahyp_large = bpow radix2 26.
Proof. lit_pow2. Qed.

Local Lemma lit_quarter : B2R DyadicLog.quarter = bpow radix2 (-2).
Proof. lit_pow2. Qed.

(** [ln x <= x - 1] (as in [FastLogNorm.v]), so [1 - 1/x <= ln x]. *)
Local Lemma ln_le_sub1 : forall x, 0 < x -> ln x <= x - 1.
Proof.
intros x Hx.
rewrite <- (ln_exp (x - 1)).
pose proof (exp_ineq1_le (x - 1)) as H.
destruct (Rle_lt_or_eq_dec x (exp (x - 1)) ltac:(lra)) as [Hlt | <-].
- apply Rlt_le, ln_increasing; assumption.
- apply Rle_refl.
Qed.

Local Lemma ln_ge : forall x, 0 < x -> 1 - / x <= ln x.
Proof.
intros x Hx.
pose proof (ln_le_sub1 (/ x) (Rinv_0_lt_compat x Hx)) as H.
rewrite ln_Rinv in H by exact Hx. lra.
Qed.

(** [ln] is [1/m]-Lipschitz above [m]. *)
Local Lemma ln_diff :
  forall a b m, 0 < m -> m <= a -> m <= b -> Rabs (ln a - ln b) <= Rabs (a - b) * / m.
Proof.
intros a b m Hm Ha Hb.
assert (K : forall x y, m <= x <= y -> 0 <= ln y - ln x <= (y - x) * / m).
{ intros x y Hxy.
  pose proof (DyLogRules.ln_le_sub x y ltac:(lra)) as H.
  assert (H0 : ln x <= ln y).
  { destruct (Req_dec x y) as [<-|Ne]; [lra|].
    apply Rlt_le, ln_increasing; lra. }
  assert (H1 : (y - x) / x <= (y - x) * / m).
  { unfold Rdiv. apply Rmult_le_compat_l; [lra|]. apply Rinv_le_contravar; lra. }
  lra. }
destruct (Rle_or_lt a b) as [L|L].
- destruct (K a b (conj Ha L)) as (K0 & K1).
  rewrite (Rabs_left1 (ln a - ln b)) by lra. rewrite (Rabs_left1 (a - b)) by lra. lra.
- destruct (K b a (conj Hb (Rlt_le _ _ L))) as (K0 & K1).
  rewrite (Rabs_pos_eq (ln a - ln b)) by lra. rewrite (Rabs_pos_eq (a - b)) by lra. lra.
Qed.

(** [x >= 2^26]: [y = ln(t + c)] with [c = sqrt(t^2 + 1)], and [D = t + i/2 - c]
    for [i = 1/t] has [D (t + i/2 + c) = i^2/4], so [0 <= D <= i^3/8]: [2 (t +
    RN(i/4))] is within [2^-78] of [t + c], and [ln] of it within [2^-104]. *)
Local Lemma asinh_large :
  forall t, is_finite t = true -> bpow radix2 26 <= B2R t ->
  is_finite (div DyadicLog.quarter t) = true /\
  Rabs (B2R (div DyadicLog.quarter t)) <= bpow radix2 (-51) * B2R t /\
  B2R t * bpow radix2 1 <= bpow radix2 1025 /\
  bpow radix2 (-20) <= Rabs (arcsinh (B2R t)) /\
  Rabs (arcsinh (B2R t) - (1 * ln 2 + ln (B2R t + B2R (div DyadicLog.quarter t))))
    <= bpow radix2 (-80) * Rabs (arcsinh (B2R t)).
Proof.
intros t Ft Ht.
pose proof (abs_B2R_lt_emax _ _ t) as Hxm.
assert (Fq : is_finite DyadicLog.quarter = true) by reflexivity.
pose proof lit_quarter as Eq.
pose proof (bpow_gt_0 radix2 26) as H26.
set (x := B2R t) in *.
assert (Hx0 : 0 < x) by lra.
rewrite Rabs_pos_eq in Hxm by lra.
set (i := / x).
assert (Hi0 : 0 < i) by (apply Rinv_0_lt_compat; lra).
assert (Hti : x * i = 1) by (apply Rinv_r; lra).
assert (Hi : i <= bpow radix2 (-26)).
{ replace (bpow radix2 (-26)) with (/ bpow radix2 26) by (rewrite <- bpow_opp; reflexivity).
  apply Rinv_le_contravar; lra. }
assert (Hz : B2R DyadicLog.quarter / x = bpow radix2 (-2) * i) by (rewrite Eq; reflexivity).
assert (Hd : Rabs (B2R DyadicLog.quarter / x) <= MAX).
{ apply small_le_max. rewrite Hz, Rabs_pos_eq.
  - cbn [bpow radix_val radix2] in *. lra.
  - pose proof (bpow_gt_0 radix2 (-2)). nra. }
destruct (FastDdSqrt.div_e DyadicLog.quarter t Fq Ft ltac:(fold x; lra) Hd) as (Fxl & Exl).
fold x in Exl. rewrite Hz in Exl.
set (xl := B2R (div DyadicLog.quarter t)) in *.
pose proof (FastExpErr.rn_err (bpow radix2 (-2) * i)) as Hxe.
rewrite <- Exl in Hxe.
assert (Hz0 : 0 < bpow radix2 (-2) * i) by (pose proof (bpow_gt_0 radix2 (-2)); nra).
rewrite (Rabs_pos_eq (bpow radix2 (-2) * i)) in Hxe by lra.
apply Rabs_le_inv in Hxe.
assert (Hxl : Rabs xl <= bpow radix2 (-51) * x).
{ apply Rabs_le. cbn [bpow radix_val radix2] in *. lra. }
split; [exact Fxl|]. split; [exact Hxl|].
split.
{ replace (bpow radix2 1025) with (bpow radix2 1024 * bpow radix2 1)
    by (rewrite <- bpow_plus; reflexivity).
  apply Rmult_le_compat_r; [apply bpow_ge_0 | lra]. }
unfold arcsinh.
replace (x ^ 2) with (x * x) by ring.
set (c := sqrt (x * x + 1)).
assert (Hc0 : 0 <= c) by apply sqrt_pos.
assert (Hcc : c * c = x * x + 1) by (apply sqrt_sqrt; nra).
assert (Hct : x <= c) by nra.
assert (Hy : / 2 < ln (x + c)).
{ pose proof ln_lt_2. assert (ln 2 < ln (x + c)).
  { apply ln_increasing; [lra|]. cbn [bpow radix_val radix2] in Ht. lra. }
  lra. }
rewrite Rabs_pos_eq by lra.
split; [cbn [bpow radix_val radix2]; lra|].
rewrite Rmult_1_l, <- ln_mult by (cbn [bpow radix_val radix2] in *; lra).
(* [D = x + i/2 - c], [D (x + i/2 + c) = i^2/4]. *)
set (D := x + i / 2 - c).
assert (Ed : D * (x + i / 2 + c) = i * i / 4).
{ unfold D. replace ((x + i / 2 - c) * (x + i / 2 + c))
    with ((x * x + 1 - c * c) + (x * i - 1) + i * i / 4) by field.
  rewrite Hcc, Hti. field. }
assert (HD0 : 0 <= D) by nra.
assert (HD1 : D * 2 <= i * i * i / 4).
{ assert (E : D * (2 * x) * i = D * 2).
  { replace (D * (2 * x) * i) with (2 * D * (x * i)) by ring. rewrite Hti. ring. }
  rewrite <- E. replace (i * i * i / 4) with (i * i / 4 * i) by field.
  apply Rmult_le_compat_r; nra. }
assert (Hii : i * i <= bpow radix2 (-26) * bpow radix2 (-26))
  by (apply Rmult_le_compat; lra).
assert (Hiii : i * i * i <= bpow radix2 (-26) * bpow radix2 (-26) * i)
  by (apply Rmult_le_compat_r; lra).
assert (HAB : Rabs (x + c - 2 * (x + xl)) <= bpow radix2 (-78)).
{ replace (x + c - 2 * (x + xl)) with (- D - 2 * (xl - bpow radix2 (-2) * i))
    by (unfold D; replace (bpow radix2 (-2)) with (/ 4) by (cbn [bpow radix_val radix2]; lra); field).
  apply Rabs_le. cbn [bpow radix_val radix2] in *. lra. }
pose proof (ln_diff (x + c) (2 * (x + xl)) x Hx0 ltac:(lra)
  ltac:(cbn [bpow radix_val radix2] in *; apply Rabs_le_inv in Hxl; lra)) as HL.
fold i in HL.
assert (HL2 : Rabs (x + c - 2 * (x + xl)) * i <= bpow radix2 (-78) * bpow radix2 (-26))
  by (apply Rmult_le_compat; [apply Rabs_pos | lra | exact HAB | exact Hi]).
cbn [bpow radix_val radix2] in *. lra.
Qed.

(** A rounding to nearest at or above [2^-1022] is within [2^-53] of the
    result. *)
Local Lemma rel_half_ulp :
  forall x, bpow radix2 (-1022) <= Rabs (RN x) ->
  Rabs (RN x - x) <= bpow radix2 (-53) * Rabs (RN x).
Proof.
intros x Hx.
pose proof (ulp_FLT_le radix2 (-1074) 53 (RN x) Hx) as H.
change (1 - 53)%Z with (-52)%Z in H.
assert (HM : bpow radix2 (-53) = / 2 * bpow radix2 (-52))
  by (cbn [bpow radix_val radix2]; lra).
apply Rle_trans with (/ 2 * ulp radix2 fexp64 (RN x)).
- apply error_le_half_ulp_round; typeclasses eauto.
- rewrite HM. lra.
Qed.

(** [ph = RN(t^2)] for [2^-27 <= t < 2^26]. *)
Local Lemma sq_facts :
  forall t, is_finite t = true -> bpow radix2 (-27) <= B2R t < bpow radix2 26 ->
  is_finite (mul t t) = true /\ B2R (mul t t) = RN (B2R t * B2R t) /\
  bpow radix2 (-56) <= B2R (mul t t) <= bpow radix2 52 + 1 /\
  bpow radix2 (-54) <= B2R t * B2R t < bpow radix2 52.
Proof.
intros t Ft Ht.
pose proof (bpow_gt_0 radix2 (-27)) as H27.
assert (Hx1 : bpow radix2 (-27) * bpow radix2 (-27) <= B2R t * B2R t)
  by (apply Rmult_le_compat; lra).
assert (Hx2 : B2R t * B2R t < bpow radix2 26 * bpow radix2 26)
  by (apply Rmult_le_0_lt_compat; lra).
rewrite <- bpow_plus in Hx1, Hx2.
change (-27 + -27)%Z with (-54)%Z in Hx1. change (26 + 26)%Z with 52%Z in Hx2.
destruct (mul_below_max t t Ft Ft) as (Fp & Ep & _).
{ rewrite Rabs_pos_eq by nra. cbn [bpow radix_val radix2] in *. lra. }
pose proof (FastExpErr.rn_err (B2R t * B2R t)) as Hpe. rewrite <- Ep in Hpe.
rewrite (Rabs_pos_eq (B2R t * B2R t)) in Hpe by nra. apply Rabs_le_inv in Hpe.
split; [exact Fp|]. split; [exact Ep|].
cbn [bpow radix_val radix2] in *. lra.
Qed.

(** Both variants of the product [t t] are exact. *)
Local Lemma asinh_exact :
  forall fma t, is_finite t = true -> bpow radix2 (-27) <= B2R t < bpow radix2 26 ->
  Generic.two_prod_is_exact fma t t (mul t t) = true.
Proof.
intros fma t Ft Ht.
destruct (sq_facts t Ft Ht) as (Fp & _ & Hp & _).
pose proof (bpow_gt_0 radix2 (-56)) as H56.
pose proof (bpow_gt_0 radix2 (-27)) as H27.
apply FastDdSqrt.two_prod_is_exact_of; [split | |].
- apply FastDdSqrt.exponent_ge; [exact Fp|].
  rewrite Rabs_pos_eq by lra. cbn [bpow radix_val radix2] in *. lra.
- assert (E : (Generic.exponent (mul t t) < 53)%Z).
  { apply FastDdSqrt.exponent_lt; [exact Fp | lia |].
    rewrite Rabs_pos_eq by lra. cbn [bpow radix_val radix2] in *. lra. }
  lia.
- assert (E : (Generic.exponent t < 26)%Z).
  { apply FastDdSqrt.exponent_lt; [exact Ft | lia |]. rewrite Rabs_pos_eq by lra. lra. }
  lia.
- assert (E : (Generic.exponent t < 26)%Z).
  { apply FastDdSqrt.exponent_lt; [exact Ft | lia |]. rewrite Rabs_pos_eq by lra. lra. }
  lia.
Qed.

(** [ah + a2] with [a2 = RN(al + pl)] is [1 + t^2] within [2^-104], as
    [|al|, |pl| <= ulp(ah)/2]. *)
Local Lemma asinh_sq :
  forall fma t ah al, is_finite t = true -> bpow radix2 (-27) <= B2R t < bpow radix2 26 ->
  Fast.two_sum DyadicExp.one (mul t t) = (ah, al) ->
  is_finite ah = true /\ is_finite (add al (Generic.two_prod_err fma t t (mul t t))) = true /\
  1 <= B2R ah <= bpow radix2 53 /\
  Rabs (B2R (add al (Generic.two_prod_err fma t t (mul t t)))) <= bpow radix2 (-52) * B2R ah /\
  Rabs (B2R ah + B2R (add al (Generic.two_prod_err fma t t (mul t t))) - (1 + B2R t * B2R t))
    <= bpow radix2 (-104) * (1 + B2R t * B2R t).
Proof.
intros fma t ah al Ft Ht Hts.
pose proof (asinh_exact fma t Ft Ht) as Hex.
destruct (two_prod_err_correct fma t t Ft Ft Hex) as (Fp & Ep & _ & Fpl & Epl).
destruct (sq_facts t Ft Ht) as (_ & _ & Hp & Hxx).
set (pl := Generic.two_prod_err fma t t (mul t t)) in *.
set (ph := mul t t) in *.
set (x := B2R t) in *.
destruct FastLogReduce.one_R as (F1 & E1).
pose proof (bpow_gt_0 radix2 (-56)) as H56.
destruct (add_below_max _ _ F1 Fp) as (Fa & Ea & _).
{ rewrite E1, Rabs_pos_eq by lra. cbn [bpow radix_val radix2] in *. lra. }
pose proof (FastRoundErr.two_sum_correct DyadicExp.one ph F1 Fp) as Hts2.
rewrite Hts in Hts2.
destruct Hts2 as (Eah & Fal & Eal).
{ rewrite E1, Rabs_pos_eq by lra. cbn [bpow radix_val radix2]. lra. }
{ rewrite Rabs_pos_eq by lra. cbn [bpow radix_val radix2] in *. lra. }
{ exact Fa. }
rewrite <- Eah in Fa, Ea. rewrite E1 in Ea, Eal.
assert (Hph : B2R ph <= B2R ah).
{ rewrite Ea. apply round_ge_generic; [typeclasses eauto .. | apply generic_format_B2R | lra]. }
assert (H1 : 1 <= B2R ah).
{ rewrite Ea, <- E1.
  apply round_ge_generic; [typeclasses eauto .. | apply generic_format_B2R | lra]. }
pose proof (FastExpErr.rn_err (1 + B2R ph)) as Hae. rewrite <- Ea in Hae.
rewrite (Rabs_pos_eq (1 + B2R ph)) in Hae by lra. apply Rabs_le_inv in Hae.
assert (Hal : Rabs (B2R al) <= / 2 * ulp radix2 fexp64 (B2R ah)).
{ rewrite Eal, Rabs_minus_sym, Ea. replace (1 + B2R ph) with (B2R DyadicExp.one + B2R ph) by (rewrite E1; reflexivity).
  apply error_le_half_ulp_round; typeclasses eauto. }
assert (Hpl : Rabs (B2R pl) <= / 2 * ulp radix2 fexp64 (B2R ph)).
{ rewrite Epl, Rabs_minus_sym, Ep. apply error_le_half_ulp_round; typeclasses eauto. }
assert (Hulp : ulp radix2 fexp64 (B2R ph) <= ulp radix2 fexp64 (B2R ah)).
{ apply (ulp_le radix2 fexp64). rewrite !Rabs_pos_eq by lra. exact Hph. }
assert (Hn : bpow radix2 (-1022) <= Rabs (B2R ah))
  by (rewrite Rabs_pos_eq by lra; cbn [bpow radix_val radix2]; lra).
pose proof (ulp_FLT_le radix2 (-1074) 53 (B2R ah) Hn) as Hu.
change (1 - 53)%Z with (-52)%Z in Hu. rewrite Rabs_pos_eq in Hu by lra.
assert (Hfu : format (ulp radix2 fexp64 (B2R ah)))
  by (apply generic_format_ulp; typeclasses eauto).
assert (Hs : Rabs (B2R al + B2R pl) <= ulp radix2 fexp64 (B2R ah)).
{ pose proof (Rabs_triang (B2R al) (B2R pl)). lra. }
destruct (add_e al pl Fal Fpl) as (Fa2 & Ea2 & Ha2e).
{ cbn [bpow radix_val radix2] in *. lra. }
set (a2 := add al pl) in *.
assert (Esum : B2R al + B2R pl = 1 + x * x - B2R ah) by (rewrite Eal, Epl; ring).
assert (Ha2 : Rabs (B2R a2) <= ulp radix2 fexp64 (B2R ah)).
{ rewrite Ea2. apply abs_round_le_generic; [typeclasses eauto .. | exact Hfu | exact Hs]. }
split; [exact Fa|]. split; [exact Fa2|].
split; [cbn [bpow radix_val radix2] in *; lra|].
split; [lra|].
rewrite Esum in Hs, Ha2e.
replace (B2R ah + B2R a2 - (1 + x * x)) with (B2R a2 - (1 + x * x - B2R ah)) by ring.
pose proof Hs as Hs2. apply Rabs_le_inv in Hs2.
pose proof (Rabs_pos (1 + x * x - B2R ah)).
cbn [bpow radix_val radix2] in *. lra.
Qed.

(** [sqrt(ah + a2)] is within [2^-104] of [c = sqrt(1 + s)], as [|p - q| (p
    + q) = |p^2 - q^2|], so [ch + cl] is within [(2^-100 + 2^-103) c]. *)
Local Lemma asinh_c :
  forall fma ah a2 ch cl s,
  is_finite ah = true -> is_finite a2 = true -> 0 <= s ->
  1 <= B2R ah <= bpow radix2 53 ->
  Rabs (B2R a2) <= bpow radix2 (-52) * B2R ah ->
  Rabs (B2R ah + B2R a2 - (1 + s)) <= bpow radix2 (-104) * (1 + s) ->
  Fast.dd_sqrt fma ah a2 = (ch, cl) ->
  is_finite ch = true /\ is_finite cl = true /\ B2R ch = RN (B2R ch + B2R cl) /\
  Rabs (B2R ch + B2R cl - sqrt (1 + s)) <=
    (bpow radix2 (-100) + bpow radix2 (-103)) * sqrt (1 + s).
Proof.
intros fma ah a2 ch cl s Fah Fa2 Hs Hah Ha2 He Hsq.
destruct (dd_sqrt_correct fma ah a2 ch cl Fah Fa2) as (Fch & Fcl & Ech & Hc).
{ split.
  - apply Rle_trans with 1; [cbn [bpow radix_val radix2]; lra | lra].
  - apply Rle_trans with (bpow radix2 53); [lra | apply bpow_le; lia]. }
{ exact Ha2. }
{ exact Hsq. }
split; [exact Fch|]. split; [exact Fcl|]. split; [exact Ech|].
set (A := B2R ah + B2R a2) in *.
assert (HA : 0 <= A).
{ apply Rabs_le_inv in Ha2. unfold A. cbn [bpow radix_val radix2] in *. lra. }
set (p := sqrt A) in *. set (q := sqrt (1 + s)) in *.
assert (Hp0 : 0 <= p) by apply sqrt_pos.
assert (Hq0 : 0 <= q) by apply sqrt_pos.
assert (Hpp : p * p = A) by (apply sqrt_sqrt; lra).
assert (Hqq : q * q = 1 + s) by (apply sqrt_sqrt; lra).
assert (Hq1 : 1 <= q) by nra.
assert (Hpq : Rabs (p - q) <= bpow radix2 (-104) * q).
{ set (e := bpow radix2 (-104)) in *. assert (He0 : 0 < e) by apply bpow_gt_0.
  rewrite <- Hpp, <- Hqq in He. apply Rabs_le_inv in He.
  assert (H0 : 0 <= e * q * p) by (apply Rmult_le_pos; [apply Rmult_le_pos|]; lra).
  assert (H1 : 0 < p + q) by lra.
  apply Rabs_le. split; nra. }
apply Rabs_le_inv in Hpq. apply Rabs_le_inv in Hc.
apply Rabs_le. cbn [bpow radix_val radix2] in *. lra.
Qed.

(** ** Helpers of the two branches below [2^26] (as in [FastAhypAcosh.v]) *)

(** Dekker's FastTwoSum (T. J. Dekker, A floating-point technique for
    extending the available precision, 1971): [s = RN(a + b)] and
    [s + t = a + b] exactly, up to [MAX]. *)
Local Lemma fts :
  forall a b s t, is_finite a = true -> is_finite b = true ->
  Rabs (B2R b) <= Rabs (B2R a) -> Rabs (B2R a + B2R b) <= MAX ->
  Fast.fast_two_sum a b = (s, t) ->
  is_finite s = true /\ is_finite t = true /\ B2R s = RN (B2R a + B2R b) /\
  B2R s + B2R t = B2R a + B2R b.
Proof.
intros a b s t Fa Fb Hab Hab2 E.
unfold Fast.fast_two_sum in E. injection E as <- <-.
destruct (add_below_max a b Fa Fb Hab2) as (Fs & Es & _).
destruct (CancelLanes.fast_two_sum a b (add a b) Fa Fb Hab Fs Es) as [Ft Et].
do 3 (split; [assumption|]). rewrite Et. ring.
Qed.

(** The rounding to nearest of a normal [x] is within [2^-53] of [x]
    relatively to the result. *)
Local Lemma rn_rel :
  forall x, bpow radix2 (-1022) <= Rabs x ->
  Rabs (RN x - x) <= bpow radix2 (-53) * Rabs (RN x).
Proof.
intros x Hx.
assert (H : Rabs (RN x - x) <= / 2 * bpow radix2 (-52) * Rabs (RN x))
  by exact (relative_error_N_FLT_round radix2 (-1074) 53 eq_refl
    (fun z => negb (Z.even z)) x Hx).
assert (E : / 2 * bpow radix2 (-52) = bpow radix2 (-53))
  by (cbn [bpow radix_val radix2]; lra).
rewrite E in H. exact H.
Qed.

(** Rounding to nearest is monotone, and leaves a [f64] in place. *)
Local Lemma rn_ge :
  forall a b, format a -> a <= b -> a <= RN b.
Proof.
intros a b Fa H.
rewrite <- (round_generic radix2 fexp64 ZnearestE a Fa) at 1.
apply round_le; [typeclasses eauto .. | exact H].
Qed.

Local Lemma le_of_sq : forall a b, 0 <= b -> a * a <= b * b -> a <= b.
Proof. intros a b Hb H. destruct (Rle_dec a 0) as [Ha | Ha]; [lra | nra]. Qed.

Local Lemma ln_le_mono : forall a b, 0 < a -> a <= b -> ln a <= ln b.
Proof.
intros a b Ha Hab.
destruct (Req_dec a b) as [<- | Hn]; [lra |].
apply Rlt_le, ln_increasing; lra.
Qed.

(** [u (1 - u) <= ln(1 + u)] for [u >= 0], from [1 - 1/(1 + u) <= ln(1 + u)]. *)
Local Lemma ln_lo : forall u, 0 <= u -> u * (1 - u) <= ln (1 + u).
Proof.
intros u Hu.
pose proof (ln_ge (1 + u) ltac:(lra)) as L.
set (v := / (1 + u)) in L.
assert (Iv : v * (1 + u) = 1) by (unfold v; field; lra).
assert (Iv2 : u * (v * (1 + u)) = u) by (rewrite Iv; ring).
assert (Hv0 : 0 < v) by (unfold v; apply Rinv_0_lt_compat; lra).
assert (H : 0 <= u * u * v) by (apply Rmult_le_pos; [nra | lra]).
assert (Hv : 1 - u <= v) by lra.
assert (H2 : u * (1 - u) <= u * v) by (apply Rmult_le_compat_l; lra).
lra.
Qed.

(** Two close positive reals have close logarithms: for [|B - A| <= e A]
    and [e <= 1/4], [|ln A - ln B| = |ln(B/A)| <= 2e]. *)
Local Lemma ln_close :
  forall A B e, 0 < A -> Rabs (B - A) <= e * A -> e <= / 4 ->
  Rabs (ln A - ln B) <= 2 * e.
Proof.
intros A B e HA H He.
apply Rabs_le_inv in H.
assert (He0 : 0 <= e) by nra.
set (q := B / A).
assert (Eq : B = A * q) by (unfold q; field; lra).
assert (Hq : 1 - e <= q <= 1 + e).
{ rewrite Eq in H. split; nra. }
assert (Hq0 : 0 < q) by lra.
rewrite Eq, ln_mult by assumption.
pose proof (ln_le_sub1 q Hq0) as L1.
pose proof (ln_ge q Hq0) as L2.
assert (I : / q * q = 1) by (field; lra).
assert (I0 : 0 < / q) by (apply Rinv_0_lt_compat; lra).
assert (I1 : / q * (1 - e) <= 1) by nra.
assert (I2 : / q <= 1 + 2 * e) by nra.
apply Rabs_le. lra.
Qed.

(** From [t = 2^-11] to [2^26]: [ln(t + c)] with [xh + xl = ch + t] exactly (Dekker's FastTwoSum, as [fts]),
    since [c - t = 1/(c + t) >= 2^-28] puts [ch] above [t]. [xh + RN(xl + cl)] is within [2^-98] of [t + c],
    so its [ln] is within [2^-97] absolutely, and [asinh t >= ln(1 + 2^-11) > 2^-12]. *)
Local Lemma asinh_mid :
  forall t ch cl xh xl,
  is_finite t = true -> bpow radix2 (-11) <= B2R t < bpow radix2 26 ->
  is_finite ch = true -> is_finite cl = true -> B2R ch = RN (B2R ch + B2R cl) ->
  Rabs (B2R ch + B2R cl - sqrt (1 + B2R t * B2R t)) <=
    (bpow radix2 (-100) + bpow radix2 (-103)) * sqrt (1 + B2R t * B2R t) ->
  Fast.fast_two_sum ch t = (xh, xl) ->
  is_finite xh = true /\ is_finite (add xl cl) = true /\ 0 < B2R xh /\
  Rabs (B2R (add xl cl)) <= bpow radix2 (-51) * B2R xh /\
  B2R xh * bpow radix2 0 <= bpow radix2 1025 /\
  bpow radix2 (-20) <= Rabs (arcsinh (B2R t)) /\
  Rabs (arcsinh (B2R t) - (IZR 0 * ln 2 + ln (B2R xh + B2R (add xl cl)))) <=
    bpow radix2 (-80) * Rabs (arcsinh (B2R t)).
Proof.
intros t ch cl xh xl Ft Ht Fch Fcl Ech Hc E.
assert (Bm1022 : bpow radix2 (-1022) <= / 1267650600228229401496703205376)
  by (apply (Rle_trans _ (bpow radix2 (-100))); [apply bpow_le; lia | right; reflexivity]).
assert (B1025 : 1 <= bpow radix2 1025) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
assert (Gx : format (B2R t)) by apply generic_format_B2R.
assert (Gch : format (B2R ch)) by apply generic_format_B2R.
cbn [bpow radix_val radix2 Z.opp] in Ht, Hc |- *.
set (X := B2R t) in *.
set (c := sqrt (1 + X * X)) in *.
assert (Hcc : c * c = 1 + X * X) by (unfold c; apply sqrt_sqrt; nra).
assert (Hc0 : 0 <= c) by apply sqrt_pos.
assert (Ec : c = sqrt (1 + X * X)) by reflexivity.
clearbody c.
(* [X <= c <= X + 1], and [c - X = 1/(c + X) >= 2^-28] *)
assert (Hc1 : 1 <= c) by (apply le_of_sq; [exact Hc0 | nra]).
assert (HcX : X <= c) by (apply le_of_sq; [exact Hc0 | nra]).
assert (HcX1 : c <= X + 1) by (apply le_of_sq; [lra | nra]).
assert (Hxc : (c - X) * (c + X) = 1)
  by (replace ((c - X) * (c + X)) with (c * c - X * X) by ring; lra).
assert (Hxc1 : (c - X) * (c + X) <= (c - X) * 268435456)
  by (apply Rmult_le_compat_l; lra).
(* [C = ch + cl] is above [X], and so is [ch] *)
set (C := B2R ch + B2R cl) in *.
assert (EC : C = B2R ch + B2R cl) by reflexivity.
apply Rabs_le_inv in Hc.
assert (HXch : X <= B2R ch).
{ rewrite Ech. apply rn_ge; [exact Gx | lra]. }
pose proof (rn_rel C ltac:(rewrite Rabs_pos_eq by lra; lra)) as Hch.
rewrite <- Ech in Hch.
rewrite (Rabs_pos_eq (B2R ch)) in Hch by lra.
cbn [bpow radix_val radix2 Z.opp] in Hch.
apply Rabs_le_inv in Hch.
(* the FastTwoSum *)
destruct (fts ch t xh xl Fch Ft) as (Fxh & Fxl & Exh & Exhl); try exact E.
{ fold X. rewrite !Rabs_pos_eq by lra. lra. }
{ fold X. rewrite Rabs_pos_eq by lra. cbn [bpow radix_val radix2 Z.opp]. lra. }
fold X in Exh, Exhl.
assert (Hxh0 : B2R ch <= B2R xh).
{ rewrite Exh. apply rn_ge; [exact Gch | lra]. }
pose proof (rn_rel (B2R ch + X) ltac:(rewrite Rabs_pos_eq by lra; lra)) as Hxh.
rewrite <- Exh in Hxh.
rewrite (Rabs_pos_eq (B2R xh)) in Hxh by lra.
cbn [bpow radix_val radix2 Z.opp] in Hxh.
apply Rabs_le_inv in Hxh.
(* [xl + cl] *)
assert (Hz : Rabs (B2R xl + B2R cl) <= / 4503599627370496 * B2R xh).
{ apply Rabs_le. split; lra. }
destruct (add_below_max xl cl Fxl Fcl) as (Fz & Ez & _).
{ apply (Rle_trans _ _ _ Hz). cbn [bpow radix_val radix2 Z.opp]. lra. }
pose proof (FastExpErr.rn_err (B2R xl + B2R cl)) as Hzr.
rewrite <- Ez in Hzr.
cbn [bpow radix_val radix2 Z.opp] in Hzr.
apply Rabs_le_inv in Hzr.
assert (Hz' := Hz). apply Rabs_le_inv in Hz'.
(* [B = xh + RN(xl + cl)] against [A = t + c] *)
set (B := B2R xh + B2R (add xl cl)).
assert (EB : B = B2R xh + B2R (add xl cl)) by reflexivity.
assert (HAB : Rabs (B - (X + c)) <= / 316912650057057350374175801344 * (X + c)).
{ apply Rabs_le. split; lra. }
assert (HA : 1 + / 2048 <= X + c) by lra.
pose proof (ln_lo (/ 2048) ltac:(lra)) as Hl0.
pose proof (ln_le_mono (1 + / 2048) (X + c) ltac:(lra) HA) as Hl1.
pose proof (ln_close (X + c) B (/ 316912650057057350374175801344)
  ltac:(lra) HAB ltac:(lra)) as Hcl.
(* the logarithms: [asinh t = ln(t + c)] *)
unfold arcsinh. replace (X ^ 2 + 1) with (1 + X * X) by ring.
rewrite <- Ec.
rewrite (Rabs_pos_eq (ln (X + c))) by lra.
replace (IZR 0 * ln 2 + ln B) with (ln B) by ring.
rewrite Rmult_1_r.
split; [exact Fxh |].
split; [exact Fz |].
split; [lra |].
split; [apply Rabs_le; lra |].
split; [lra |].
split; [lra |].
lra.
Qed.

Theorem fast_asinh_pos_correct :
  forall fma t h l k,
  is_finite t = true -> bpow radix2 (-8) <= B2R t ->
  DyadicLog.fast_asinh_pos fma t = Some (h, l, k) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < Rabs (B2R h) < 2 /\ (-1021 <= k <= 1022)%Z /\
  Rabs (arcsinh (B2R t) * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-68).
Proof.
intros fma t h l k Ft Ht8.
assert (FL : is_finite DyadicLog.ahyp_large = true) by reflexivity.
assert (HTS : bpow radix2 (-11) <= B2R t)
  by (apply (Rle_trans _ (bpow radix2 (-8))); [apply bpow_le; lia | exact Ht8]).
assert (Ht : bpow radix2 (-27) <= B2R t)
  by (apply (Rle_trans _ (bpow radix2 (-8))); [apply bpow_le; lia | exact Ht8]).
assert (Pt : 0 < B2R t) by (pose proof (bpow_gt_0 radix2 (-27)); lra).
unfold DyadicLog.fast_asinh_pos. cbv zeta.
destruct (Model.ge t DyadicLog.ahyp_large) eqn:Ege.
- (* From [2^26] on: [ln 2 + ln(t + RN(1/(4t)))]. *)
  pose proof (ge_true t _ Ft FL Ege) as HTL. rewrite lit_large in HTL.
  destruct (asinh_large t Ft HTL) as (Fq & Hq & Hm & Hy20 & Herr).
  intros E. exact (fast_ln_dd_correct fma t _ 1 _ h l k Ft Fq Pt Hq ltac:(lia) Hm Hy20 Herr E).
- (* Up to [2^26]: [ln(t + c)]. *)
  pose proof (ge_false t _ Ft FL Ege) as HTL. rewrite lit_large in HTL.
  destruct (Fast.two_sum DyadicExp.one (mul t t)) as [ah al] eqn:Ea. cbv beta iota.
  destruct (asinh_sq fma t ah al Ft (conj Ht HTL) Ea) as (Fah & Fa2 & Hah & Ha2 & He).
  destruct (Fast.dd_sqrt fma ah (add al (Generic.two_prod_err fma t t (mul t t)))) as [ch cl] eqn:Ec.
  cbv beta iota.
  destruct (asinh_c fma ah _ ch cl (B2R t * B2R t) Fah Fa2 ltac:(nra) Hah Ha2 He Ec)
    as (Fch & Fcl & Ech & Hc).
  destruct (Fast.fast_two_sum ch t) as [xh xl] eqn:Ex.
  destruct (asinh_mid t ch cl xh xl Ft (conj HTS HTL) Fch Fcl Ech Hc Ex)
    as (Fxh & Fxl & Pxh & Hxl & Hm & Hy20 & Herr).
  intros E. exact (fast_ln_dd_correct fma xh (add xl cl) 0 _ h l k Fxh Fxl Pxh Hxl ltac:(lia)
    Hm Hy20 Herr E).
Qed.

Theorem fast_asinh_pos_fma :
  forall t,
  is_finite t = true -> bpow radix2 (-8) <= B2R t ->
  DyadicLog.fast_asinh_pos true t = DyadicLog.fast_asinh_pos false t.
Proof.
intros t Ft Ht8.
assert (FL : is_finite DyadicLog.ahyp_large = true) by reflexivity.
assert (HTS : bpow radix2 (-11) <= B2R t)
  by (apply (Rle_trans _ (bpow radix2 (-8))); [apply bpow_le; lia | exact Ht8]).
assert (Ht : bpow radix2 (-27) <= B2R t)
  by (apply (Rle_trans _ (bpow radix2 (-8))); [apply bpow_le; lia | exact Ht8]).
assert (Pt : 0 < B2R t) by (pose proof (bpow_gt_0 radix2 (-27)); lra).
unfold DyadicLog.fast_asinh_pos. cbv zeta.
destruct (Model.ge t DyadicLog.ahyp_large) eqn:Ege.
- apply fast_ln_dd_fma; [exact Ft | exact Pt].
- pose proof (ge_false t _ Ft FL Ege) as HTL. rewrite lit_large in HTL.
  (* [t^2] is exact either way, so its error is the same [f64]. *)
  rewrite (two_prod_err_fma_eq t t Ft Ft (asinh_exact true t Ft (conj Ht HTL))
    (asinh_exact false t Ft (conj Ht HTL))).
  destruct (Fast.two_sum DyadicExp.one (mul t t)) as [ah al] eqn:Ea. cbv beta iota.
  destruct (asinh_sq false t ah al Ft (conj Ht HTL) Ea) as (Fah & Fa2 & Hah & Ha2 & He).
  assert (Hah' : bpow radix2 (-900) <= B2R ah <= bpow radix2 900).
  { split.
    - apply (Rle_trans _ (bpow radix2 0)); [apply bpow_le; lia | cbn [bpow]; lra].
    - apply (Rle_trans _ (bpow radix2 53)); [lra | apply bpow_le; lia]. }
  rewrite (dd_sqrt_fma ah _ Fah Fa2 Hah').
  destruct (Fast.dd_sqrt false ah (add al (Generic.two_prod_err false t t (mul t t))))
    as [ch cl] eqn:Ec.
  cbv beta iota.
  destruct (asinh_c false ah _ ch cl (B2R t * B2R t) Fah Fa2 ltac:(nra) Hah Ha2 He Ec)
    as (Fch & Fcl & Ech & Hc).
  destruct (Fast.fast_two_sum ch t) as [xh xl] eqn:Ex.
  destruct (asinh_mid t ch cl xh xl Ft (conj HTS HTL) Fch Fcl Ech Hc Ex)
    as (Fxh & _ & Pxh & _).
  apply fast_ln_dd_fma; assumption.
Qed.
