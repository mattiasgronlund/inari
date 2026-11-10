(** * The core's cases and the product of [fast_log_by]

    [DyadicLog.fast_log_by] of [Model.v] multiplies the core's [a_h +
    a_l] ([FastLogCore.v]) by the constant [c_h + c_l]. [core_cases]
    shows that [ln x - e ln 2] and [a_h] are both [0] or both away from
    [0], [by_prod] that [ph + pl] is the product within [2^-100 |a_h|]
    plus underflow, and [by_prod_fma] that an FMA gives the same error
    term of [ph] where [a_h] is not [0]. [FastLogBy.v] and [FastLog.v]
    use them. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct FastRound FastLogTables
  FastLogReduce FastLogCore FastLogNorm FastExpErr.
From Inari Require MulRuTiny.

Open Scope R_scope.

(** ** Helpers *)

Local Lemma bp_tri : forall a b c, a = b + c -> Rabs a <= Rabs b + Rabs c.
Proof. intros a b c ->. apply Rabs_triang. Qed.

(** Powers of 2 as numerals, for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp] in *.

(** A finite [f64] of value 0 is a zero (as in [FastLogPoly.v]). *)
Local Lemma zero_of_B2R : forall x : f64, is_finite x = true -> B2R x = 0 -> exists s, x = B754_zero s.
Proof.
intros [s|s| |s m e Hb] F H; try discriminate F.
- exists s. reflexivity.
- exfalso. cbn [B2R] in H. apply eq_0_F2R in H. destruct s; simpl in H; discriminate H.
Qed.

(** A product or a sum of exact value 0 is a finite 0. *)
Local Lemma mul_z :
  forall x y, is_finite x = true -> is_finite y = true -> B2R x * B2R y = 0 ->
  is_finite (mul x y) = true /\ B2R (mul x y) = 0.
Proof.
intros x y Fx Fy H.
destruct (mul_e x y Fx Fy ltac:(rewrite H, Rabs_R0; lra)) as (F & E & _).
split; [exact F |]. rewrite E, H. apply round_0; typeclasses eauto.
Qed.

Local Lemma add_z :
  forall x y, is_finite x = true -> is_finite y = true -> B2R x + B2R y = 0 ->
  is_finite (add x y) = true /\ B2R (add x y) = 0.
Proof.
intros x y Fx Fy H.
destruct (add_e x y Fx Fy ltac:(rewrite H, Rabs_R0; lra)) as (F & E & _).
split; [exact F |]. rewrite E, H. apply round_0; typeclasses eauto.
Qed.

(** The [e] of [ln_core] is that of [ln_split]. *)
Local Lemma core_e :
  forall fma x, fst (fst (DyadicLog.ln_core fma x)) = fst (fst (DyadicLog.ln_split x)).
Proof.
intros fma x. unfold DyadicLog.ln_core.
destruct (DyadicLog.ln_split x) as [[e m] i]. cbv beta iota.
destruct (DyadicLog.ltbl i) as [[r th] tl]. cbv beta iota zeta.
destruct (Fast.fast_two_sum (sub (mul r m) DyadicExp.one) (Generic.two_prod_err fma r m (mul r m)))
  as [z1 z2].
cbv beta iota.
destruct (DyadicLog.log1p_poly fma z1 z2) as [ah pl]. cbv beta iota.
destruct (Fast.fast_two_sum th ah) as [u v]. cbv beta iota.
destruct (Fast.fast_two_sum u (add v (add tl pl))) as [a_h a_l]. reflexivity.
Qed.

(** [a_h c_h] is exact as [ph + (a_h c_h - ph)] (TwoProduct,
    [TwoProduct.v]) for [2^-56 <= |a_h| <= 1/2] and [1/4 <= c_h <= 2]:
    [2^-59 <= |ph| < 4], and [a_h] and [c_h] are far below the range of
    Dekker's split. *)
Local Lemma prod_exact :
  forall fma ah ch, is_finite ah = true -> is_finite ch = true ->
  bpow radix2 (-56) <= Rabs (B2R ah) -> Rabs (B2R ah) <= / 2 -> / 4 <= B2R ch <= 2 ->
  Generic.two_prod_is_exact fma ah ch (mul ah ch) = true.
Proof.
intros fma ah ch Fah Fch Hlo Hhi Hch.
assert (B56 : bpow radix2 (-56) = / 72057594037927936) by reflexivity.
assert (U : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
assert (B59 : bpow radix2 (-59) = / 576460752303423488) by reflexivity.
assert (B100 : bpow radix2 (-100) = / 1267650600228229401496703205376) by reflexivity.
pose proof (bpow_gt_0 radix2 (-1075)) as T0.
assert (T1 : bpow radix2 (-1075) <= bpow radix2 (-100)) by (apply bpow_le; lia).
rewrite B56 in Hlo. rewrite B100 in T1.
assert (Ech : Rabs (B2R ch) = B2R ch) by (apply Rabs_pos_eq; lra).
assert (Lo : / 72057594037927936 * / 4 <= Rabs (B2R ah * B2R ch)).
{ rewrite Rabs_mult, Ech. apply Rmult_le_compat; lra. }
assert (Hi : Rabs (B2R ah * B2R ch) <= 1).
{ rewrite Rabs_mult, Ech. apply Rle_trans with (/ 2 * 2); [| lra].
  apply Rmult_le_compat; [apply Rabs_pos | lra | exact Hhi | lra]. }
destruct (mul_e ah ch Fah Fch ltac:(lra)) as (Fp & _ & Bp).
rewrite U in Bp.
pose proof (bp_tri (B2R ah * B2R ch) (B2R (mul ah ch)) (- (B2R (mul ah ch) - B2R ah * B2R ch))
  ltac:(ring)) as Ta.
pose proof (bp_tri (B2R (mul ah ch)) (B2R ah * B2R ch) (B2R (mul ah ch) - B2R ah * B2R ch)
  ltac:(ring)) as Tb.
rewrite Rabs_Ropp in Ta.
assert (Elo : (-59 <= Generic.exponent (mul ah ch))%Z).
{ apply MulRuTiny.exponent_ge; [exact Fp |]. rewrite B59. lra. }
assert (Ehi : (Generic.exponent (mul ah ch) < 2)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fp | lia |]. num. lra. }
assert (Ea : (Generic.exponent ah < 0)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fah | lia |]. num. lra. }
assert (Ec : (Generic.exponent ch < 2)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fch | lia |]. rewrite Ech. num. lra. }
unfold Generic.two_prod_is_exact. cbv zeta.
destruct fma; repeat (apply andb_true_intro; split); apply Z.leb_le; lia.
Qed.

(** ** The theorems *)

(** [ln x - e ln 2 = ln m] is [0] (then [x = 2^e] and [a_h = a_l = 0])
    or at least [2^-54] in magnitude (then [|a_h| >= 2^-56]). *)
Lemma core_cases :
  forall fma x, is_finite x = true -> 0 < B2R x ->
  let '(e, ah, al) := DyadicLog.ln_core fma x in
  Rabs (B2R ah) <= / 2 /\
  ((ln (B2R x) - IZR e * ln 2 = 0 /\ B2R ah = 0 /\ B2R al = 0) \/
   (bpow radix2 (-54) <= Rabs (ln (B2R x) - IZR e * ln 2) /\
    bpow radix2 (-56) <= Rabs (B2R ah))).
Proof.
intros fma x Fx Px.
pose proof (ln_core_correct fma x Fx Px) as Hc.
pose proof (ln_split_correct x Fx Px) as Hs.
pose proof (core_e fma x) as Ee.
revert Hc Hs Ee.
destruct (DyadicLog.ln_core fma x) as [[e ah] al].
destruct (DyadicLog.ln_split x) as [[e' m] i].
cbn [fst]. cbv beta iota.
intros (Fah & Fal & Eah & _ & HD & Hcore) (Fm & Hi & _ & Hx & Hm) <-.
assert (I1 : 362 <= IZR (362 + i)) by (apply IZR_le; lia).
assert (Pm : 0 < B2R m) by lra.
(* [ln x - e ln 2 = ln m], as in [FastLogCore.v]. *)
assert (Lx : ln (B2R x) - IZR e * ln 2 = ln (B2R m)).
{ rewrite Hx, ln_mult by first [lra | apply bpow_gt_0].
  rewrite bpow_exp, ln_exp. change (IZR (radix_val radix2)) with 2. ring. }
rewrite Lx in HD, Hcore |- *.
set (D := ln (B2R m)) in *.
assert (U : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
assert (B54 : bpow radix2 (-54) = / 18014398509481984) by reflexivity.
assert (B56 : bpow radix2 (-56) = / 72057594037927936) by reflexivity.
assert (B71 : bpow radix2 (-71) = / 2361183241434822606848) by reflexivity.
assert (B100 : bpow radix2 (-100) = / 1267650600228229401496703205376) by reflexivity.
pose proof (bpow_gt_0 radix2 (-1075)) as T0.
assert (T1 : bpow radix2 (-1075) <= bpow radix2 (-100)) by (apply bpow_le; lia).
rewrite B100 in T1. rewrite B71 in Hcore. rewrite B54, B56.
(* [a_h = RN(a_h + a_l)], so [|a_l| <= 2^-53 |a_h + a_l| + 2^-1075]. *)
pose proof (rn_err (B2R ah + B2R al)) as Hr. rewrite <- Eah, U in Hr.
replace (B2R ah - (B2R ah + B2R al)) with (- B2R al) in Hr by ring. rewrite Rabs_Ropp in Hr.
pose proof (bp_tri (B2R ah + B2R al) D (- (D - (B2R ah + B2R al))) ltac:(ring)) as Ta.
pose proof (bp_tri D (B2R ah + B2R al) (D - (B2R ah + B2R al)) ltac:(ring)) as Tb.
pose proof (bp_tri (B2R ah) (B2R ah + B2R al) (- B2R al) ltac:(ring)) as Tc.
pose proof (bp_tri (B2R ah + B2R al) (B2R ah) (B2R al) ltac:(ring)) as Td.
rewrite Rabs_Ropp in Ta, Tc.
pose proof (Rabs_pos D) as P0.
assert (Hah : Rabs (B2R ah) <= / 2) by lra.
split; [exact Hah |].
destruct (Req_dec (B2R m) 1) as [M1 | M1].
- (* [m = 1]: [ln m = 0], so the core is exact: [a_h + a_l = 0]. *)
  left.
  assert (D0 : D = 0) by (unfold D; rewrite M1; apply ln_1).
  rewrite D0, Rabs_R0 in Hcore.
  apply Rabs_le_inv in Hcore.
  assert (A0 : B2R ah + B2R al = 0) by lra.
  assert (H0 : B2R ah = 0).
  { rewrite Eah, A0. apply round_0; typeclasses eauto. }
  split; [exact D0 |]. split; [exact H0 | lra].
- (* [m <> 1]: [|ln m| >= 2^-54] ([FastLogNorm.v]), and [a_h + a_l] is
     within [3 2^-71] of it relatively. *)
  right. pose proof (ln_f64_ne1 m Fm Pm M1) as Hlo. fold D in Hlo. rewrite B54 in Hlo.
  split; [exact Hlo | lra].
Qed.

(** [ph + pl] is [(a_h + a_l) (c_h + c_l)] within [2^-100 |a_h| +
    2^-1070]. The error term of [ph] is exact ([TwoProduct.v]) where [a_h
    <> 0]; where [a_h = 0], the hypothesis on the zeros, which
    [FastLogBy.v] checks for each constant by computation, gives it. *)
Lemma by_prod :
  forall fma ah al ch cl,
  is_finite ah = true -> is_finite al = true -> is_finite ch = true -> is_finite cl = true ->
  B2R ah = RN (B2R ah + B2R al) ->
  (B2R ah = 0 \/ bpow radix2 (-56) <= Rabs (B2R ah)) -> Rabs (B2R ah) <= / 2 ->
  / 4 <= B2R ch <= 2 -> Rabs (B2R cl) <= bpow radix2 (-55) ->
  (forall s,
     is_finite (Generic.two_prod_err fma (B754_zero s) ch (mul (B754_zero s) ch)) = true /\
     B2R (Generic.two_prod_err fma (B754_zero s) ch (mul (B754_zero s) ch)) = 0) ->
  let ph := mul ah ch in
  let pl := add (Generic.two_prod_err fma ah ch ph) (add (mul ah cl) (mul al ch)) in
  is_finite ph = true /\ is_finite pl = true /\ B2R ph = RN (B2R ah * B2R ch) /\
  Rabs (B2R pl) <= bpow radix2 (-50) * Rabs (B2R ah) + bpow radix2 (-1070) /\
  Rabs (B2R ph + B2R pl - (B2R ah + B2R al) * (B2R ch + B2R cl)) <=
    bpow radix2 (-100) * Rabs (B2R ah) + bpow radix2 (-1070).
Proof.
intros fma ah al ch cl Fah Fal Fch Fcl Eah H0 Hhi Hch Hcl Hz.
cbv zeta.
assert (B1070 : bpow radix2 (-1070) = 32 * bpow radix2 (-1075)).
{ replace (-1070)%Z with (5 + -1075)%Z by lia. rewrite bpow_plus. reflexivity. }
rewrite B1070.
pose proof (bpow_gt_0 radix2 (-1075)) as T0.
destruct H0 as [A0 | Alo].
- (* [a_h = 0]: [a_l = RN(a_l) = 0], and every term is 0. *)
  assert (L0 : B2R al = 0).
  { rewrite A0, Rplus_0_l in Eah.
    rewrite (round_generic radix2 fexp64 ZnearestE (B2R al)) in Eah
      by apply generic_format_B2R.
    lra. }
  destruct (zero_of_B2R ah Fah A0) as [s ->].
  destruct (Hz s) as (Ft & Et).
  destruct (mul_z (B754_zero s) ch Fah Fch ltac:(rewrite A0; ring)) as (Fp & Ep).
  destruct (mul_z (B754_zero s) cl Fah Fcl ltac:(rewrite A0; ring)) as (F1 & E1).
  destruct (mul_z al ch Fal Fch ltac:(rewrite L0; ring)) as (F2 & E2).
  destruct (add_z _ _ F1 F2 ltac:(rewrite E1, E2; ring)) as (F3 & E3).
  destruct (add_z _ _ Ft F3 ltac:(rewrite Et, E3; ring)) as (F4 & E4).
  split; [exact Fp |]. split; [exact F4 |]. split.
  { rewrite Ep, A0, Rmult_0_l. symmetry. apply round_0; typeclasses eauto. }
  rewrite Ep, E4, A0, L0, Rabs_R0.
  split; [lra |].
  replace (0 + 0 - (0 + 0) * (B2R ch + B2R cl)) with 0 by ring. rewrite Rabs_R0. lra.
- (* [|a_h| >= 2^-56]: [ph + tp = a_h c_h] exactly, and four roundings. *)
  pose proof (prod_exact fma ah ch Fah Fch Alo Hhi Hch) as Ex.
  destruct (two_prod_err_correct fma ah ch Fah Fch Ex) as (Fp & Ep & _ & Ft & Et).
  set (ph := mul ah ch) in *.
  set (tp := Generic.two_prod_err fma ah ch ph) in *.
  assert (U : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
  assert (B50 : bpow radix2 (-50) = / 1125899906842624) by reflexivity.
  assert (B55 : bpow radix2 (-55) = / 36028797018963968) by reflexivity.
  assert (B100 : bpow radix2 (-100) = / 1267650600228229401496703205376) by reflexivity.
  assert (T1 : bpow radix2 (-1075) <= bpow radix2 (-100)) by (apply bpow_le; lia).
  rewrite B50, B100. rewrite B55 in Hcl. rewrite B100 in T1.
  set (A := Rabs (B2R ah)) in *.
  pose proof (Rabs_pos (B2R ah)) as A0. fold A in A0.
  (* [|a_l| <= 2^-52 |a_h| + 2 2^-1075], from [a_h = RN(a_h + a_l)]. *)
  pose proof (rn_err (B2R ah + B2R al)) as Hr. rewrite <- Eah, U in Hr.
  replace (B2R ah - (B2R ah + B2R al)) with (- B2R al) in Hr by ring. rewrite Rabs_Ropp in Hr.
  pose proof (bp_tri (B2R ah + B2R al) (B2R ah) (B2R al) eq_refl) as Ta. fold A in Ta.
  assert (Hal : Rabs (B2R al) <= / 4503599627370496 * A + 2 * bpow radix2 (-1075)) by lra.
  clear Hr Ta.
  (* The products, by hand, so that [lra] sees linear bounds. *)
  assert (Ech : Rabs (B2R ch) <= 2) by (apply Rabs_le; lra).
  pose proof (Rabs_mul_le (B2R ah) (B2R cl) A (/ 36028797018963968) (Rle_refl _) Hcl) as M1.
  pose proof (Rabs_mul_le (B2R al) (B2R ch) _ 2 Hal Ech) as M2.
  pose proof (Rabs_mul_le (B2R al) (B2R cl) _ _ Hal Hcl) as M3.
  pose proof (Rabs_mul_le (B2R ah) (B2R ch) A 2 (Rle_refl _) Ech) as M4.
  (* [tp = a_h c_h - RN(a_h c_h)]. *)
  pose proof (rn_err (B2R ah * B2R ch)) as Hp. rewrite <- Ep, U in Hp.
  assert (Htp : Rabs (B2R tp) <= / 4503599627370496 * A + bpow radix2 (-1075)).
  { rewrite Et, Rabs_minus_sym. lra. }
  clear Hp.
  (* [m1 = RN(a_h c_l)] and [m2 = RN(a_l c_h)]. *)
  destruct (mul_e ah cl Fah Fcl ltac:(lra)) as (F1 & _ & E1). rewrite U in E1.
  destruct (mul_e al ch Fal Fch ltac:(lra)) as (F2 & _ & E2). rewrite U in E2.
  set (m1 := mul ah cl) in *. set (m2 := mul al ch) in *.
  assert (E1' : Rabs (B2R m1 - B2R ah * B2R cl) <=
                / 324518553658426726783156020576256 * A + bpow radix2 (-1075)) by lra.
  assert (E2' : Rabs (B2R m2 - B2R al * B2R ch) <=
                / 20282409603651670423947251286016 * A + 2 * bpow radix2 (-1075)) by lra.
  clear E1 E2.
  (* The inner sum [i = RN(m1 + m2)]. *)
  pose proof (bp_tri (B2R m1 + B2R m2) (B2R ah * B2R cl + B2R al * B2R ch)
    ((B2R m1 - B2R ah * B2R cl) + (B2R m2 - B2R al * B2R ch)) ltac:(ring)) as S1.
  pose proof (Rabs_triang (B2R m1 - B2R ah * B2R cl) (B2R m2 - B2R al * B2R ch)) as S2.
  pose proof (Rabs_triang (B2R ah * B2R cl) (B2R al * B2R ch)) as S3.
  assert (Hs : Rabs (B2R m1 + B2R m2) <= 9 / 16 * / 1125899906842624 * A + 7 * bpow radix2 (-1075))
    by lra.
  clear S1 S2 S3.
  destruct (add_e m1 m2 F1 F2 ltac:(lra)) as (Fi & _ & Ei). rewrite U in Ei.
  set (i := add m1 m2) in *.
  assert (Ei' : Rabs (B2R i - (B2R m1 + B2R m2)) <=
                9 / 16 * / 10141204801825835211973625643008 * A + 2 * bpow radix2 (-1075)) by lra.
  clear Ei.
  (* The outer sum [pl = RN(tp + i)]. *)
  pose proof (bp_tri (B2R i) (B2R m1 + B2R m2) (B2R i - (B2R m1 + B2R m2)) ltac:(ring)) as S4.
  pose proof (Rabs_triang (B2R tp) (B2R i)) as S5.
  assert (Hti : Rabs (B2R tp + B2R i) <= 7 / 8 * / 1125899906842624 * A + 10 * bpow radix2 (-1075))
    by lra.
  clear S4 S5.
  destruct (add_e tp i Ft Fi ltac:(lra)) as (Fo & _ & Eo). rewrite U in Eo.
  set (pl := add tp i) in *.
  assert (Eo' : Rabs (B2R pl - (B2R tp + B2R i)) <=
                7 / 8 * / 10141204801825835211973625643008 * A + 2 * bpow radix2 (-1075)) by lra.
  clear Eo.
  split; [exact Fp |]. split; [exact Fo |]. split; [exact Ep |]. split.
  { pose proof (bp_tri (B2R pl) (B2R tp + B2R i) (B2R pl - (B2R tp + B2R i)) ltac:(ring)) as S6.
    lra. }
  (* The error: [ph + tp = a_h c_h] cancels, and five terms are left. *)
  assert (Ee : B2R ph + B2R pl - (B2R ah + B2R al) * (B2R ch + B2R cl) =
    (B2R pl - (B2R tp + B2R i)) + (B2R i - (B2R m1 + B2R m2)) +
    (B2R m1 - B2R ah * B2R cl) + (B2R m2 - B2R al * B2R ch) - B2R al * B2R cl).
  { rewrite Et. ring. }
  rewrite Ee.
  apply Rabs_le_inv in Eo', Ei', E1', E2', M3.
  apply Rabs_le. split; lra.
Qed.

(** With an FMA, the error term of [ph] is the same [f64] where [a_h <>
    0], as [FastRound.two_prod_err_fma_eq] shows for an exact product. *)
Lemma by_prod_fma :
  forall ah ch,
  is_finite ah = true -> is_finite ch = true ->
  bpow radix2 (-56) <= Rabs (B2R ah) -> Rabs (B2R ah) <= / 2 -> / 4 <= B2R ch <= 2 ->
  Generic.two_prod_err true ah ch (mul ah ch) = Generic.two_prod_err false ah ch (mul ah ch).
Proof.
intros ah ch Fah Fch Hlo Hhi Hch.
apply FastRound.two_prod_err_fma_eq; [exact Fah | exact Fch | |]; apply prod_exact; assumption.
Qed.
