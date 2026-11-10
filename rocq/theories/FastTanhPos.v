(** * The scaled result of the fast path of [tanh]

    [DyadicExp.fast_tanh_pos] of [Model.v] returns, for [t >= 0], an
    unevaluated sum [h + l] with [h] the rounding of [h + l] to nearest,
    an exponent [k] and a bound [err = 2^-p] with [|tanh t 2^-k - (h +
    l)| <= err], which the tests of [FastRoundErr.v] take
    ([fast_tanh_pos_correct]):
    - [t >= 1/8]: [(1 - w) / (1 + w)] for [w = e^-2t] from
      [fast_exp_correct] of [FastExpCore.v], by the double-double quotient
      of [FastDiv.v], scaled by [Fast.normalize], with [err = 2^(-67-k)]
      for the exponent [k] in [[-4, 0]] of the quotient;
    - [2^-27 <= t < 1/8]: the quotient of the polynomials of
      [FastHypPoly.v] and [FastCoshPoly.v], scaled by [Fast.normalize],
      with [err = 2^-63].
    It returns the same with and without an FMA ([fast_tanh_pos_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error.
From Inari Require Import Model Mpfr Encoding Elementary TwoSum TwoProduct MulRuTiny DyDriver
  NearF64 FastRound FastExpTables FastExpCore FastRoundErr FastDiv FastHypPoly FastCoshPoly FastExpErr
  FastExp.
From Inari Require CancelLanes ExpReal.

Open Scope R_scope.

Local Notation G := (generic_format radix2 fexp64).

(** ** Helpers *)

Lemma th_format_bpow : forall a, (-1074 <= a)%Z -> G (bpow radix2 a).
Proof.
intros a Ha. apply generic_format_FLT_bpow; [easy | lia].
Qed.

Lemma th_format_3_2 : G (3 / 2).
Proof.
apply generic_format_FLT. apply (FLT_spec _ _ _ _ (Float radix2 3 (-1))).
- unfold F2R. cbn [Fnum Fexp]. change (bpow radix2 (-1)) with (/ 2). lra.
- cbn. lia.
- cbn. lia.
Qed.

(** [-2.0], as in [DyHyp.v]. *)
Lemma th_m_two_R : B2R DyadicExp.m_two = -2.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicExp.m_two) with (SpecFloat.S754_finite true 4503599627370496 (-51))
  by (vm_compute; reflexivity).
unfold SF2R, F2R. cbn [Fnum Fexp SpecFloat.cond_Zopp].
change (bpow radix2 (-51)) with (/ 2251799813685248)%R.
rewrite opp_IZR. lra.
Qed.

(** A finite product of [-2.0] and [t] is exact, as [hyp_mul_two] of
    [DyHyp.v]. *)
Lemma th_mul_m_two :
  forall t : f64, is_finite (mul DyadicExp.m_two t) = true ->
  B2R (mul DyadicExp.m_two t) = -2 * B2R t.
Proof.
intros t F. rewrite <- th_m_two_R.
assert (G0 : generic_format radix2 (FLT_exp (-1074) 53) (B2R DyadicExp.m_two * B2R t)).
{ assert (G1 : generic_format radix2 (FLT_exp (-1074) 53) (B2R t * bpow radix2 1)).
  { apply mult_bpow_pos_exact_FLT; [apply generic_format_B2R | lia]. }
  rewrite th_m_two_R. change (bpow radix2 1) with 2 in G1.
  replace (-2 * B2R t) with (- (B2R t * 2)) by ring.
  apply generic_format_opp. exact G1. }
pose proof (Bmult_correct 53 1024 _ _ mode_NE DyadicExp.m_two t) as Hm.
change (SpecFloat.fexp 53 1024) with (FLT_exp (-1074) 53) in Hm.
cbn [round_mode] in Hm. rewrite (round_generic _ _ _ _ G0) in Hm.
destruct (Rlt_bool_spec (Rabs (B2R DyadicExp.m_two * B2R t)) (bpow radix2 1024)) as [L|L].
- destruct Hm as (Rm & _). exact Rm.
- unfold mul in F. rewrite <- is_finite_SF_B2SF, Hm in F. discriminate F.
Qed.

(** ** The scaling by [Fast.normalize]

    For [2^a <= qh + ql <= 3/2] with [qh] the rounding of [qh + ql],
    [Fast.normalize] returns [(h, l, k)] with [a <= k <= 0] and [h + l =
    (qh + ql) 2^-k < 2]. *)
Lemma th_tail :
  forall qh ql a,
  is_finite qh = true -> is_finite ql = true -> B2R qh = RN (B2R qh + B2R ql) ->
  (-1021 <= a <= 0)%Z -> bpow radix2 a <= B2R qh + B2R ql <= 3 / 2 ->
  let '(h, l, k) := Fast.normalize qh ql in
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (a <= k <= 0)%Z /\
  B2R h + B2R l = (B2R qh + B2R ql) * bpow radix2 (- k) /\ B2R h + B2R l < 2.
Proof.
intros qh ql a Fh Fl Hrn Ha HQ.
assert (H1 : bpow radix2 a <= B2R qh).
{ rewrite Hrn. apply round_ge_generic; [typeclasses eauto .. | apply th_format_bpow; lia | lra]. }
assert (H2 : B2R qh <= 3 / 2).
{ rewrite Hrn. apply round_le_generic; [typeclasses eauto .. | exact th_format_3_2 | lra]. }
assert (H3 : bpow radix2 (-1021) <= bpow radix2 a) by (apply bpow_le; lia).
pose proof (normalize_correct qh ql Fh Fl Hrn ltac:(lra)) as Hn.
destruct (Fast.normalize qh ql) as [[h l] k].
destruct Hn as (Fh' & Fl' & Hk & Eh & El & Hb & Hrn').
assert (Hak : (a <= k)%Z).
{ destruct (Z_le_gt_dec a k) as [L|L]; [exact L|].
  assert (bpow radix2 (k + 1) <= bpow radix2 a) by (apply bpow_le; lia). lra. }
assert (HQk : B2R qh + B2R ql < bpow radix2 (k + 1)).
{ destruct (Rlt_or_le (B2R qh + B2R ql) (bpow radix2 (k + 1))) as [L|L]; [exact L|].
  assert (bpow radix2 (k + 1) <= B2R qh).
  { rewrite Hrn. apply round_ge_generic; [typeclasses eauto .. | apply th_format_bpow; lia | lra]. }
  lra. }
assert (HS : B2R h + B2R l = (B2R qh + B2R ql) * bpow radix2 (- k)) by (rewrite Eh, El; ring).
split; [exact Fh'|]. split; [exact Fl'|]. split; [exact Hrn'|]. split; [lia|].
split; [exact HS|].
rewrite HS.
replace 2 with (bpow radix2 (k + 1) * bpow radix2 (- k))
  by (rewrite <- bpow_plus; replace (k + 1 + - k)%Z with 1%Z by ring; reflexivity).
apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact HQk].
Qed.

(** ** [2^-27 <= t < 1/8]: the quotient of the polynomials

    With [S = s (1 + a)], [C = c (1 + b)], [|a| <= 2^-65], [|b| <=
    2^-66] for [s = sinh t] and [c = cosh t], [S / C - s / c = (S c - s
    C) / (C c)] and [|S c - s C| <= 3 2^-66 s c], so [|S / C - tanh t| (1
    - 2^-66) <= 3 2^-66 tanh t], and [dd_div] adds [2^-98] of [S / C]. *)
Lemma th_small_core :
  forall fma t, is_finite t = true -> bpow radix2 (-27) <= B2R t < / 8 ->
  let '(sh, sl) := DyadicExp.fast_sinh_poly fma t in
  let '(ch, cl) := DyadicExp.fast_cosh_poly fma t in
  let '(qh, ql) := Fast.dd_div fma sh sl ch cl in
  is_finite qh = true /\ is_finite ql = true /\ B2R qh = RN (B2R qh + B2R ql) /\
  bpow radix2 (-30) <= B2R qh + B2R ql <= 3 / 2 /\
  Rabs (B2R qh + B2R ql - tanh (B2R t))
    <= (3 * bpow radix2 (-66) + bpow radix2 (-97)) * tanh (B2R t).
Proof.
intros fma t Ft Ht.
pose proof (sinh_poly_correct fma t Ft ltac:(lra)) as Hs.
pose proof (cosh_poly_correct fma t Ft Ht) as Hc.
destruct (DyadicExp.fast_sinh_poly fma t) as [sh sl].
destruct (DyadicExp.fast_cosh_poly fma t) as [ch cl].
destruct Hs as (Fsh & Fsl & _ & Hsh & Hsl & Es).
destruct Hc as (Fch & Fcl & Hch & Hcl & Ec).
assert (HM : bpow radix2 (-80) <= bpow radix2 (-27) /\ bpow radix2 (-52) <= bpow radix2 (-50))
  by (split; apply bpow_le; lia).
pose proof (bpow_gt_0 radix2 (-27)) as H27.
assert (Hsl' : Rabs (B2R sl) <= bpow radix2 (-50) * B2R sh).
{ apply Rle_trans with (1 := Hsl). apply Rmult_le_compat_r; lra. }
pose proof (dd_div_correct fma sh sl ch cl Fsh Fsl Fch Fcl ltac:(lra) Hsl' ltac:(lra) Hcl) as Hq.
destruct (Fast.dd_div fma sh sl ch cl) as [qh ql].
destruct Hq as (Fqh & Fql & Rq & Eq).
do 3 (split; [assumption|]).
set (S := B2R sh + B2R sl) in *. set (C := B2R ch + B2R cl) in *.
set (Q := B2R qh + B2R ql) in *.
set (s := sinh (B2R t)) in *. set (c := cosh (B2R t)) in *.
set (R := S / C) in *.
assert (HK : bpow radix2 (-52) = / 4503599627370496 /\ bpow radix2 (-27) = / 134217728 /\
  bpow radix2 (-30) = / 1073741824 /\ bpow radix2 (-65) = / 36893488147419103232 /\
  bpow radix2 (-66) = / 73786976294838206464 /\
  bpow radix2 (-97) = / 158456325028528675187087900672 /\
  bpow radix2 (-98) = / 316912650057057350374175801344)
  by (repeat split; reflexivity).
destruct HK as (K52 & K27 & K30 & K65 & K66 & K97 & K98).
rewrite K52 in Hsl, Hcl. rewrite K27 in Hsh. rewrite K65 in Es. rewrite K66 in Ec |- *.
rewrite K30, K97. rewrite K98 in Eq.
assert (Hsl0 := Rabs_le_inv _ _ Hsl). assert (Hcl0 := Rabs_le_inv _ _ Hcl).
assert (HS : / 134217728 * (1 - / 4503599627370496) <= S <= / 2 * (1 + / 4503599627370496))
  by (unfold S; nra).
assert (HC : 1 - / 4503599627370496 <= C <= 2 * (1 + / 4503599627370496)) by (unfold C; nra).
assert (HRC : R * C = S) by (unfold R; field; lra).
assert (HR0 : 0 <= R) by (unfold R; apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; lra]).
assert (HRlo : / 134217728 * (1 - / 4503599627370496) <= R * (2 * (1 + / 4503599627370496)))
  by (apply Rle_trans with (R * C); [lra | apply Rmult_le_compat_l; lra]).
assert (HRhi : R * (1 - / 4503599627370496) <= / 2 * (1 + / 4503599627370496))
  by (apply Rle_trans with (R * C); [apply Rmult_le_compat_l; lra | lra]).
assert (Eq0 := Rabs_le_inv _ _ Eq).
split; [lra|].
(* [c > 0] and [s >= 0] from the bounds of [C] and [S]. *)
assert (Ec0 := Rabs_le_inv _ _ Ec). assert (Es0 := Rabs_le_inv _ _ Es).
assert (Hc0 : 0 < c) by lra.
assert (Hs0 : 0 <= s) by lra.
assert (HT : tanh (B2R t) * c = s) by (unfold tanh; fold s c; field; lra).
set (T := tanh (B2R t)) in *.
assert (HT0 : 0 <= T).
{ destruct (Rle_or_lt 0 T) as [L|L]; [exact L|]. nra. }
set (d := R - T).
assert (Hd : d * C * c = (S - s) * c - s * (C - c)).
{ unfold d. replace ((R - T) * C * c) with ((R * C) * c - (T * c) * C) by ring.
  rewrite HRC, HT. ring. }
assert (Hd1 : Rabs d * C * c <= 3 * / 73786976294838206464 * s * c).
{ replace (Rabs d * C * c) with (Rabs (d * C * c))
    by (rewrite !Rabs_mult, (Rabs_pos_eq C), (Rabs_pos_eq c); lra).
  rewrite Hd. eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_Ropp, !Rabs_mult, (Rabs_pos_eq c), (Rabs_pos_eq s) by lra.
  replace (3 * / 73786976294838206464 * s * c)
    with (/ 36893488147419103232 * s * c + s * (/ 73786976294838206464 * c)) by field.
  apply Rplus_le_compat; [apply Rmult_le_compat_r; lra | apply Rmult_le_compat_l; lra]. }
assert (Hd2 : Rabs d * C <= 3 * / 73786976294838206464 * T * c).
{ apply Rmult_le_reg_r with c; [exact Hc0|].
  replace (3 * / 73786976294838206464 * T * c * c) with (3 * / 73786976294838206464 * (T * c) * c)
    by ring.
  rewrite HT. exact Hd1. }
assert (Hd3 : Rabs d * (1 - / 73786976294838206464) <= 3 * / 73786976294838206464 * T).
{ apply Rmult_le_reg_r with c; [exact Hc0|].
  apply Rle_trans with (Rabs d * C); [|lra].
  replace (Rabs d * (1 - / 73786976294838206464) * c)
    with (Rabs d * (c * (1 - / 73786976294838206464))) by ring.
  apply Rmult_le_compat_l; [apply Rabs_pos | lra]. }
assert (HQR : Rabs (Q - R) <= / 316912650057057350374175801344 * (T + Rabs d)).
{ apply Rle_trans with (1 := Eq). apply Rmult_le_compat_l; [lra|].
  unfold d. destruct (Rabs_le_inv _ _ (Rle_refl (Rabs (R - T)))).
  pose proof (Rle_abs (R - T)). lra. }
replace (Q - T) with ((Q - R) + d) by (unfold d; ring).
eapply Rle_trans; [apply Rabs_triang|].
pose proof (Rabs_pos d). lra.
Qed.

Lemma th_one : is_finite DyadicExp.one = true /\ B2R DyadicExp.one = 1.
Proof.
split; [reflexivity | exact one_R].
Qed.

(** ** [t >= 1/8]: [(1 - w) / (1 + w)] for [w = e^-2t]

    [fast_exp] returns [h + l] within [2^-68 - 2^-72] of [y 2^-e] for [y
    = e^-2t <= e^-1/4 <= 4/5], so [e <= 0] and [w = (h + l) 2^e] is [y]
    within about [2^-67 y]. The denominator [D = 1 + W + dd] and the
    numerator [N = 1 - W + dn] for [W = wh + wl] carry the rounding
    errors [dd] and [dn] of their low parts, and [tanh t (1 + y) = 1 -
    y] gives [(N / D - tanh t) D = (y - W) (1 + tanh t) + dn - tanh t
    dd], where [y (1 + tanh t) = 1 - tanh t <= 8/9]. *)
Lemma th_mid_core :
  forall fma t h l e, is_finite t = true -> / 8 <= B2R t ->
  DyadicExp.fast_exp fma (mul DyadicExp.m_two t) zero = Some (h, l, e) ->
  let wh := mul h (DyadicExp.two_pow e) in
  let wl := mul l (DyadicExp.two_pow e) in
  let dh := add DyadicExp.one wh in
  let nh := add DyadicExp.one (opp wh) in
  let dl := add (add wh (sub DyadicExp.one dh)) wl in
  let nl := sub (add (opp wh) (sub DyadicExp.one nh)) wl in
  is_finite nh = true /\ is_finite nl = true /\ is_finite dh = true /\ is_finite dl = true /\
  bpow radix2 (-80) <= B2R nh <= 4 /\ Rabs (B2R nl) <= bpow radix2 (-50) * B2R nh /\
  / 2 <= B2R dh <= 4 /\ Rabs (B2R dl) <= bpow radix2 (-52) * B2R dh /\
  / 9 <= tanh (B2R t) <= 1 /\
  Rabs ((B2R nh + B2R nl) / (B2R dh + B2R dl) - tanh (B2R t))
    <= bpow radix2 (-67) - bpow radix2 (-70).
Proof.
intros fma t h l e Ft Ht He wh wl dh nh dl nl.
destruct th_one as [F1 E1].
assert (K53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
assert (K50 : bpow radix2 (-50) = / 1125899906842624) by reflexivity.
assert (K52 : bpow radix2 (-52) = / 4503599627370496) by reflexivity.
assert (K67 : bpow radix2 (-67) = / 147573952589676412928) by reflexivity.
assert (K68 : bpow radix2 (-68) = / 295147905179352825856) by reflexivity.
assert (K70 : bpow radix2 (-70) = / 1180591620717411303424) by reflexivity.
assert (K72 : bpow radix2 (-72) = / 4722366482869645213696) by reflexivity.
assert (K80 : bpow radix2 (-80) = / 1208925819614629174706176) by reflexivity.
pose proof (bpow_gt_0 radix2 (-1075)) as Hu0.
assert (Hu1 : bpow radix2 (-1075) <= / 1267650600228229401496703205376).
{ change (/ 1267650600228229401496703205376) with (bpow radix2 (-100)). apply bpow_le. lia. }
destruct (fe_in _ _ _ _ He) as [Fz _].
pose proof (th_mul_m_two t Fz) as Ez.
assert (Hz0 : Rabs (B2R zero) <= bpow radix2 (-40))
  by (cbn [B2R zero]; rewrite Rabs_R0; apply bpow_ge_0).
destruct (fast_exp_correct fma _ zero h l e Fz eq_refl Hz0 He) as (Fh & Fl & Rh & Hh & Hee & Herr).
rewrite Ez in Herr. change (B2R zero) with 0 in Herr. rewrite Rplus_0_r, K68, K72 in Herr.
set (y := exp (-2 * B2R t)) in Herr.
assert (Hy0 : 0 < y) by apply exp_pos.
(* [y <= 4/5]: [e^2t >= 1 + 2t >= 5/4]. *)
assert (Hy : y <= 4 / 5).
{ assert (Hy1 : y * exp (2 * B2R t) = 1).
  { unfold y. rewrite <- exp_plus. replace (-2 * B2R t + 2 * B2R t) with 0 by ring. apply exp_0. }
  pose proof (exp_ineq1_le (2 * B2R t)) as Hx. nra. }
(* [tanh t (1 + y) = 1 - y], from [e^t e^-t = 1]. *)
assert (HT : tanh (B2R t) * (1 + y) = 1 - y).
{ unfold y, tanh, sinh, cosh.
  replace (-2 * B2R t) with (- B2R t + - B2R t) by ring. rewrite exp_plus.
  set (a := exp (B2R t)). set (b := exp (- B2R t)).
  assert (Ha : 0 < a) by apply exp_pos. assert (Hb : 0 < b) by apply exp_pos.
  assert (Hab : a * b = 1) by (unfold a, b; rewrite <- exp_plus, Rplus_opp_r; apply exp_0).
  assert (Habb : a * b * b = b) by (rewrite Hab; ring).
  apply Rmult_eq_reg_r with (a + b); [|lra].
  replace ((a - b) / 2 / ((a + b) / 2) * (1 + b * b) * (a + b)) with ((a - b) * (1 + b * b))
    by (field; lra).
  lra. }
set (T := tanh (B2R t)) in *.
assert (HT1 : / 9 <= T <= 1) by (split; nra).
(* [|l| <= 2^-53 |h + l| + 2^-1075], as [h] is the rounding of [h + l]. *)
pose proof (rn_err (B2R h + B2R l)) as Hl. rewrite <- Rh in Hl.
replace (B2R h - (B2R h + B2R l)) with (- B2R l) in Hl by ring.
rewrite Rabs_Ropp, K53 in Hl.
assert (Hl2 : Rabs (B2R h + B2R l) <= B2R h + Rabs (B2R l)).
{ eapply Rle_trans; [apply Rabs_triang|]. rewrite (Rabs_pos_eq (B2R h)) by lra. lra. }
assert (Hla := Rabs_le_inv (B2R l) _ (Rle_refl _)).
(* [e <= 0]: else [h + l <= y / 2 + 2^-68 < 1/2 - 2^-52]. *)
assert (He0 : (e <= 0)%Z).
{ destruct (Z_le_gt_dec e 0) as [L|L]; [exact L|]. exfalso.
  assert (Hb : bpow radix2 (- e) <= / 2)
    by (change (/ 2) with (bpow radix2 (-1)); apply bpow_le; lia).
  assert (Hb0 : 0 < bpow radix2 (- e)) by apply bpow_gt_0.
  assert (Hyb : y * bpow radix2 (- e) <= y * / 2) by (apply Rmult_le_compat_l; lra).
  apply Rabs_le_inv in Herr. lra. }
set (E := bpow radix2 e) in *.
assert (HE0 : 0 < E) by apply bpow_gt_0.
assert (HE1 : E <= 1) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
assert (HEi : E * bpow radix2 (- e) = 1)
  by (unfold E; rewrite <- bpow_plus, Z.add_opp_diag_r; reflexivity).
assert (Fp : is_finite (DyadicExp.two_pow e) = true /\ B2R (DyadicExp.two_pow e) = E)
  by exact (pow2_bits e ltac:(lia)).
destruct Fp as [Fp Ep].
(* [wh = h 2^e] exactly. *)
assert (Hwh : is_finite wh = true /\ B2R wh = B2R h * E)
  by exact (scale_correct h e Fh ltac:(lra) ltac:(lia)).
destruct Hwh as [Fwh Ewh].
set (WH := B2R wh) in *.
set (LE := B2R l * E).
assert (HWE : E / 2 <= WH <= 2 * E) by (rewrite Ewh; split; nra).
assert (Herr' : Rabs (y - (WH + LE))
  <= (/ 295147905179352825856 - / 4722366482869645213696) * E).
{ assert (Hid : (y * bpow radix2 (- e) - (B2R h + B2R l)) * E = y - (WH + LE)).
  { unfold LE. rewrite Ewh.
    replace ((y * bpow radix2 (- e) - (B2R h + B2R l)) * E)
      with (y * (E * bpow radix2 (- e)) - (B2R h * E + B2R l * E)) by ring.
    rewrite HEi. ring. }
  rewrite <- Hid, Rabs_mult, (Rabs_pos_eq E) by lra.
  apply Rmult_le_compat_r; lra. }
(* [|l 2^e| <= 2^-53 (wh + |l 2^e|) + 2^-1075]. *)
assert (HLE : Rabs LE * (1 - / 9007199254740992)
  <= / 9007199254740992 * WH + bpow radix2 (-1075)).
{ unfold LE. rewrite Rabs_mult, (Rabs_pos_eq E) by lra. rewrite Ewh.
  assert (Hl3 : Rabs (B2R l) * (1 - / 9007199254740992)
    <= / 9007199254740992 * B2R h + bpow radix2 (-1075)) by lra.
  apply Rle_trans with ((/ 9007199254740992 * B2R h + bpow radix2 (-1075)) * E).
  - replace (Rabs (B2R l) * E * (1 - / 9007199254740992))
      with (Rabs (B2R l) * (1 - / 9007199254740992) * E) by ring.
    apply Rmult_le_compat_r; lra.
  - assert (bpow radix2 (-1075) * E <= bpow radix2 (-1075)) by nra. lra. }
assert (Hlea := Rabs_le_inv LE _ (Rle_refl _)).
assert (Herr2 := Rabs_le_inv _ _ Herr').
assert (WH1 : 0 < WH <= 81 / 100) by lra.
(* [wl] *)
assert (HLE16 : Rabs (B2R l * B2R (DyadicExp.two_pow e)) <= 16).
{ rewrite Ep. fold LE. lra. }
destruct (mul_e l (DyadicExp.two_pow e) Fl Fp HLE16) as (Fwl & _ & Hwl).
change (mul l (DyadicExp.two_pow e)) with wl in Fwl, Hwl.
rewrite Ep in Hwl. fold LE in Hwl. rewrite K53 in Hwl.
apply Rabs_le_inv in Hwl.
(* [dh] and [d0 = 1 + wh - dh] *)
destruct (add_e DyadicExp.one wh F1 Fwh ltac:(rewrite E1; change (B2R wh) with WH; apply Rabs_le; lra))
  as (Fdh & Rdh & Hdh).
change (add DyadicExp.one wh) with dh in Fdh, Rdh, Hdh.
rewrite E1 in Rdh, Hdh. change (B2R wh) with WH in Rdh, Hdh.
rewrite (Rabs_pos_eq (1 + WH)), K53 in Hdh by lra.
apply Rabs_le_inv in Hdh.
destruct (CancelLanes.fast_two_sum DyadicExp.one wh dh F1 Fwh
  ltac:(rewrite E1, Rabs_R1; change (B2R wh) with WH; rewrite Rabs_pos_eq; lra)
  Fdh ltac:(rewrite E1; exact Rdh)) as [Fd0 Ed0].
rewrite E1 in Ed0. change (B2R wh) with WH in Ed0.
set (d0 := add wh (sub DyadicExp.one dh)) in *.
(* [nh] and [n0 = 1 - wh - nh] *)
assert (Fo : is_finite (opp wh) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fwh).
assert (Eo : B2R (opp wh) = - WH) by (unfold opp; apply B2R_Bopp).
destruct (add_e DyadicExp.one (opp wh) F1 Fo ltac:(rewrite E1, Eo; apply Rabs_le; lra))
  as (Fnh & Rnh & Hnh).
change (add DyadicExp.one (opp wh)) with nh in Fnh, Rnh, Hnh.
rewrite E1, Eo in Rnh, Hnh.
rewrite (Rabs_pos_eq (1 + - WH)), K53 in Hnh by lra.
apply Rabs_le_inv in Hnh.
destruct (CancelLanes.fast_two_sum DyadicExp.one (opp wh) nh F1 Fo
  ltac:(rewrite E1, Eo, Rabs_R1, Rabs_Ropp, Rabs_pos_eq; lra)
  Fnh ltac:(rewrite E1, Eo; exact Rnh)) as [Fn0 En0].
rewrite E1, Eo in En0.
set (n0 := add (opp wh) (sub DyadicExp.one nh)) in *.
(* The low parts [nl = RN(n0 - wl)] and [dl = RN(d0 + wl)]; the slack
   [2^-98] covers the three [2^-1075 <= 2^-100] of [nh], [wl] and [LE]. *)
assert (Hn0wl : Rabs (B2R n0 - B2R wl)
  <= / 9007199254740992 + / 316912650057057350374175801344) by (apply Rabs_le; lra).
assert (Hd0wl : Rabs (B2R d0 + B2R wl)
  <= / 9007199254740992 * (1 + 2 * WH) + / 316912650057057350374175801344)
  by (apply Rabs_le; lra).
destruct (sub_e n0 wl Fn0 Fwl ltac:(lra)) as (Fnl & _ & Hnl).
change (sub n0 wl) with nl in Fnl, Hnl. rewrite K53 in Hnl.
destruct (add_e d0 wl Fd0 Fwl ltac:(lra)) as (Fdl & _ & Hdl).
change (add d0 wl) with dl in Fdl, Hdl. rewrite K53 in Hdl.
set (dn := B2R nl - (B2R n0 - B2R wl)) in *.
set (dd := B2R dl - (B2R d0 + B2R wl)) in *.
assert (Hdn : Rabs dn <= / 9007199254740992 *
  (/ 9007199254740992 + / 316912650057057350374175801344) + bpow radix2 (-1075)).
{ eapply Rle_trans; [exact Hnl|]. apply Rplus_le_compat_r.
  apply Rmult_le_compat_l; [lra | exact Hn0wl]. }
assert (Hdd : Rabs dd <= / 9007199254740992 *
  (/ 9007199254740992 * (1 + 2 * WH) + / 316912650057057350374175801344) + bpow radix2 (-1075)).
{ eapply Rle_trans; [exact Hdl|]. apply Rplus_le_compat_r.
  apply Rmult_le_compat_l; [lra | exact Hd0wl]. }
assert (Hdn2 := Rabs_le_inv _ _ Hdn). assert (Hdd2 := Rabs_le_inv _ _ Hdd).
assert (Hn0wl2 := Rabs_le_inv _ _ Hn0wl). assert (Hd0wl2 := Rabs_le_inv _ _ Hd0wl).
do 4 (split; [assumption|]).
rewrite K80, K50, K52.
split; [lra|]. split; [apply Rabs_le; unfold dn in Hdn2; lra|].
split; [lra|]. split; [apply Rabs_le; unfold dd in Hdd2; lra|].
split; [exact HT1|].
(* The error of the quotient *)
set (W := WH + B2R wl).
set (N := B2R nh + B2R nl). set (D := B2R dh + B2R dl).
assert (HN : N = 1 - W + dn) by (unfold N, W, dn; lra).
assert (HD : D = 1 + W + dd) by (unfold D, W, dd; lra).
assert (HD1 : 1 - / 316912650057057350374175801344 <= D) by (rewrite HD; unfold W; lra).
assert (HRD : N / D * D = N) by (field; lra).
set (R := N / D) in *.
assert (Hid : (R - T) * D = (y - W) * (1 + T) + dn - T * dd).
{ replace ((R - T) * D) with (R * D - T * D) by ring. rewrite HRD, HN, HD. lra. }
assert (Hyw : Rabs (y - W) <= (15 / 2361183241434822606848 + / 1267650600228229401496703205376) * y
  + / 316912650057057350374175801344) by (apply Rabs_le; unfold W; split; lra).
assert (Hx : forall a b c : Rdefinitions.R, Rabs (a + b - c) <= Rabs a + Rabs b + Rabs c).
{ intros a b c. unfold Rminus. eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_Ropp. pose proof (Rabs_triang a b). lra. }
assert (H4 : Rabs (R - T) * D <= Rabs (y - W) * (1 + T) + Rabs dn + T * Rabs dd).
{ rewrite <- (Rabs_pos_eq D) by lra. rewrite <- Rabs_mult, Hid.
  eapply Rle_trans; [apply Hx|].
  rewrite !Rabs_mult, (Rabs_pos_eq (1 + T)), (Rabs_pos_eq T) by lra. lra. }
assert (H1 : Rabs (y - W) * (1 + T) <= ((15 / 2361183241434822606848
  + / 1267650600228229401496703205376) * y + / 316912650057057350374175801344) * (1 + T))
  by (apply Rmult_le_compat_r; lra).
assert (H2 : T * Rabs dd <= Rabs dd).
{ rewrite <- (Rmult_1_l (Rabs dd)) at 2. apply Rmult_le_compat_r; [apply Rabs_pos | lra]. }
assert (H3 : Rabs (R - T) * (1 - / 316912650057057350374175801344) <= Rabs (R - T) * D)
  by (apply Rmult_le_compat_l; [apply Rabs_pos | lra]).
rewrite K67, K70. lra.
Qed.

(** The literals of [fast_tanh_pos]: [2^-27], [0.125] and [2^-63]. *)
Lemma th_lits :
  (is_finite DyadicExp.tiny_near = true /\ B2R DyadicExp.tiny_near = bpow radix2 (-27)) /\
  (is_finite (from_bits 0x3fc0000000000000) = true /\
   B2R (from_bits 0x3fc0000000000000) = bpow radix2 (-3)) /\
  (is_finite DyadicExp.err63 = true /\ B2R DyadicExp.err63 = bpow radix2 (-63)).
Proof.
split; [|split].
- exact (pow2_bits (-27) ltac:(lia)).
- exact (pow2_bits (-3) ltac:(lia)).
- exact (pow2_bits (-63) ltac:(lia)).
Qed.

(** Where [fast_tanh_pos] returns [(h, l, e, err)], [h + l] is [tanh t
    2^-e] within [err = 2^-p], and [h] is the rounding of [h + l] to
    nearest. *)
Theorem fast_tanh_pos_correct :
  forall fma t h l e err,
  is_finite t = true -> 0 <= B2R t ->
  DyadicExp.fast_tanh_pos fma t = Some (h, l, e, err) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= e <= 1022)%Z /\
  exists p, (55 <= p <= 105)%Z /\ B2R err = bpow radix2 (- p) /\
    Rabs (tanh (B2R t) * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (- p).
Proof.
intros fma t h l e err Ft Ht H.
destruct th_lits as ((F27 & E27) & (F3 & E3) & (F63 & E63)).
assert (K3 : bpow radix2 (-3) = / 8) by reflexivity.
unfold DyadicExp.fast_tanh_pos in H.
destruct (lt t DyadicExp.tiny_near) eqn:L1; [discriminate H|].
pose proof (gt_false DyadicExp.tiny_near t F27 Ft L1) as H27. rewrite E27 in H27.
destruct (lt t (from_bits 0x3fc0000000000000)) eqn:L2.
- (* [2^-27 <= t < 1/8]: the quotient of the polynomials, within [2^-63]
     of [tanh t 2^-k] as [|X - Y| <= eps X] and [X (1 - eps) <= Y < 2]
     for [X = tanh t 2^-k] and [Y = h + l]. *)
  pose proof (gt_true (from_bits 0x3fc0000000000000) t F3 Ft L2) as H3.
  rewrite E3, K3 in H3.
  pose proof (th_small_core fma t Ft (conj H27 H3)) as Hc.
  destruct (DyadicExp.fast_sinh_poly fma t) as [sh sl].
  destruct (DyadicExp.fast_cosh_poly fma t) as [ch cl].
  destruct (Fast.dd_div fma sh sl ch cl) as [qh ql].
  destruct Hc as (Fqh & Fql & Rq & HQ & EQ).
  pose proof (th_tail qh ql (-30) Fqh Fql Rq ltac:(lia) HQ) as Hn.
  destruct (Fast.normalize qh ql) as [[h0 l0] k].
  injection H as E1 E2 E4 E5. subst h0 l0 k err.
  destruct Hn as (Fh & Fl & Rh & Hk & Ehl & Hlt).
  do 3 (split; [assumption|]). split; [lia|].
  exists 63%Z. split; [lia|]. split; [exact E63|].
  rewrite Ehl in Hlt |- *.
  set (B := bpow radix2 (- e)) in *.
  assert (HB : 0 < B) by apply bpow_gt_0.
  set (Q := B2R qh + B2R ql) in *. set (T := tanh (B2R t)) in *.
  replace (T * B - Q * B) with ((T - Q) * B) by ring.
  rewrite Rabs_mult, (Rabs_pos_eq B), Rabs_minus_sym by lra.
  assert (K : bpow radix2 (-66) = / 73786976294838206464 /\
    bpow radix2 (-97) = / 158456325028528675187087900672 /\
    bpow radix2 (-63) = / 9223372036854775808) by (repeat split; reflexivity).
  destruct K as (K66 & K97 & K63). rewrite K66, K97 in EQ.
  match goal with |- _ <= bpow radix2 ?z => change (bpow radix2 z) with (/ 9223372036854775808) end.
  assert (EQ0 := Rabs_le_inv _ _ EQ).
  assert (H1 : Rabs (Q - T) * B
    <= (3 * / 73786976294838206464 + / 158456325028528675187087900672) * T * B)
    by (apply Rmult_le_compat_r; lra).
  assert (H2 : (1 - (3 * / 73786976294838206464 + / 158456325028528675187087900672)) * T * B
    <= Q * B) by (apply Rmult_le_compat_r; lra).
  lra.
- (* [t >= 1/8]: [(1 - w) / (1 + w)], within [2^-67 - 2^-70] of [tanh t]
     by [th_mid_core], and [dd_div] adds [2^-98] of the quotient. *)
  pose proof (gt_false (from_bits 0x3fc0000000000000) t F3 Ft L2) as H3.
  rewrite E3, K3 in H3.
  destruct (DyadicExp.fast_exp fma (mul DyadicExp.m_two t) zero) as [[[h0 l0] e0]|] eqn:He;
    [|discriminate H].
  cbv beta iota zeta delta [Fast.fast_two_sum] in H.
  pose proof (th_mid_core fma t h0 l0 e0 Ft H3 He) as Hm. cbv zeta in Hm.
  destruct Hm as (Fnh & Fnl & Fdh & Fdl & Hnh & Hnl & Hdh & Hdl & HT & Hq).
  match goal with H : context [Fast.dd_div ?f ?a ?b ?c ?d] |- _ =>
    pose proof (dd_div_correct f a b c d Fnh Fnl Fdh Fdl Hnh Hnl Hdh Hdl) as Hd;
    destruct (Fast.dd_div f a b c d) as [qh ql] end.
  destruct Hd as (Fqh & Fql & Rq & Eq).
  match type of Eq with Rabs (_ - ?r) <= _ => set (R0 := r) in * end.
  assert (K : bpow radix2 (-98) = / 316912650057057350374175801344 /\
    bpow radix2 (-67) = / 147573952589676412928 /\
    bpow radix2 (-70) = / 1180591620717411303424 /\ bpow radix2 (-4) = / 16)
    by (repeat split; reflexivity).
  destruct K as (K98 & K67 & K70 & K4). rewrite K98 in Eq. rewrite K67, K70 in Hq.
  assert (Eq0 := Rabs_le_inv _ _ Eq). assert (Hq0 := Rabs_le_inv _ _ Hq).
  assert (HQ : bpow radix2 (-4) <= B2R qh + B2R ql <= 3 / 2) by (rewrite K4; lra).
  pose proof (th_tail qh ql (-4) Fqh Fql Rq ltac:(lia) HQ) as Hn.
  destruct (Fast.normalize qh ql) as [[h1 l1] k].
  injection H as E1 E2 E4 E5. subst h1 l1 k err.
  destruct Hn as (Fh & Fl & Rh & Hk & Ehl & Hlt).
  do 3 (split; [assumption|]). split; [lia|].
  exists (67 + e)%Z. split; [lia|].
  split.
  { etransitivity; [exact (proj2 (pow2_bits (-67 - e) ltac:(lia)))|].
    f_equal. lia. }
  rewrite Ehl.
  set (B := bpow radix2 (- e)) in *.
  assert (HB : 0 < B) by apply bpow_gt_0.
  assert (KB : bpow radix2 (- (67 + e)) = / 147573952589676412928 * B).
  { unfold B. rewrite <- K67, <- bpow_plus. f_equal. lia. }
  rewrite KB.
  set (Q := B2R qh + B2R ql) in *. set (T := tanh (B2R t)) in *.
  replace (T * B - Q * B) with ((T - Q) * B) by ring.
  rewrite Rabs_mult, (Rabs_pos_eq B) by lra.
  apply Rmult_le_compat_r; [lra|].
  apply Rabs_le. lra.
Qed.

(** [fast_tanh_pos] returns the same with and without an FMA. *)
Theorem fast_tanh_pos_fma :
  forall t,
  is_finite t = true -> 0 <= B2R t ->
  DyadicExp.fast_tanh_pos true t = DyadicExp.fast_tanh_pos false t.
Proof.
intros t Ft Ht.
destruct th_lits as ((F27 & E27) & (F3 & E3) & _).
assert (K3 : bpow radix2 (-3) = / 8) by reflexivity.
unfold DyadicExp.fast_tanh_pos.
destruct (lt t DyadicExp.tiny_near) eqn:L1; [reflexivity|].
pose proof (gt_false DyadicExp.tiny_near t F27 Ft L1) as H27. rewrite E27 in H27.
destruct (lt t (from_bits 0x3fc0000000000000)) eqn:L2.
- (* The polynomials and [dd_div] do not depend on [fma]. *)
  pose proof (gt_true (from_bits 0x3fc0000000000000) t F3 Ft L2) as H3.
  rewrite E3, K3 in H3.
  assert (Ht4 : bpow radix2 (-27) <= B2R t < / 4) by lra.
  rewrite (sinh_poly_fma t Ft Ht4), (cosh_poly_fma t Ft (conj H27 H3)).
  pose proof (sinh_poly_correct false t Ft Ht4) as Hs.
  pose proof (cosh_poly_correct false t Ft (conj H27 H3)) as Hc.
  destruct (DyadicExp.fast_sinh_poly false t) as [sh sl].
  destruct (DyadicExp.fast_cosh_poly false t) as [ch cl].
  destruct Hs as (Fsh & Fsl & _ & Hsh & Hsl & _).
  destruct Hc as (Fch & Fcl & Hch & Hcl & _).
  assert (HM : bpow radix2 (-80) <= bpow radix2 (-27) /\ bpow radix2 (-52) <= bpow radix2 (-50))
    by (split; apply bpow_le; lia).
  pose proof (bpow_gt_0 radix2 (-27)).
  assert (Hsl' : Rabs (B2R sl) <= bpow radix2 (-50) * B2R sh).
  { apply Rle_trans with (1 := Hsl). apply Rmult_le_compat_r; lra. }
  rewrite (dd_div_fma sh sl ch cl Fsh Fsl Fch Fcl ltac:(lra) Hsl' ltac:(lra) Hcl).
  reflexivity.
- (* [fast_exp] and [dd_div] do not depend on [fma]. *)
  pose proof (gt_false (from_bits 0x3fc0000000000000) t F3 Ft L2) as H3.
  rewrite E3, K3 in H3.
  rewrite fast_exp_fma.
  destruct (DyadicExp.fast_exp false (mul DyadicExp.m_two t) zero) as [[[h0 l0] e0]|] eqn:He;
    [|reflexivity].
  cbv beta iota zeta delta [Fast.fast_two_sum].
  pose proof (th_mid_core false t h0 l0 e0 Ft H3 He) as Hm. cbv zeta in Hm.
  destruct Hm as (Fnh & Fnl & Fdh & Fdl & Hnh & Hnl & Hdh & Hdl & _).
  rewrite (dd_div_fma _ _ _ _ Fnh Fnl Fdh Fdl Hnh Hnl Hdh Hdl).
  reflexivity.
Qed.
