(** * The double-double quotient of the fast paths

    [Fast.dd_div] of [Model.v] divides [nh + nl] by [dh + dl]: one
    division [qh = RN(nh / dh)], the remainder [nh - qh dh], which is an
    [f64] [Boldo-Daumas] and which [Sterbenz] and the exact product of
    [TwoProduct.v] compute exactly, and one correction [RN(r / dh)] added
    by Fast2Sum. The result is within [2^-98] of the quotient, relatively
    ([dd_div_correct]), and the same with and without an FMA
    ([dd_div_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error.
From Inari Require Import Model Mpfr Encoding TwoSum TwoProduct DyDriver NearF64 FastRound.
From Inari Require FastExpErr DivRemainder DivRuFast CancelLanes.

Open Scope R_scope.

Local Notation format := (generic_format radix2 fexp64).

(* Closes a linear goal whose constants are literal powers of two: [cbn]
   turns each [bpow radix2 n] into a rational constant for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2] in *; lra.

(** ** Helpers *)

(** [x / y] of finite [f64]s with an exact result of at most 16 in
    magnitude is finite and rounded to nearest, as [FastExpErr.add_e]. *)
Local Lemma div_e :
  forall x y, is_finite x = true -> is_finite y = true -> B2R y <> 0 ->
  Rabs (B2R x / B2R y) <= 16 ->
  is_finite (div x y) = true /\ B2R (div x y) = RN (B2R x / B2R y).
Proof.
intros x y Fx Fy Hy H.
destruct (RN_below_max _ (FastExpErr.small_le_max _ H)) as (Hlt & _).
generalize (@Bdiv_correct 53 1024 _ _ mode_NE x y Hy).
rewrite Rlt_bool_true by exact Hlt.
intros (HR & HF & _).
change (Bdiv mode_NE x y) with (div x y) in HR, HF.
rewrite Fx in HF. split; [exact HF | exact HR].
Qed.

(** The exponent of a finite [f64] below [2^k] is below [k], and that of
    one at least [2^k] at least [k]. *)
Local Lemma exponent_lt :
  forall x k, is_finite x = true -> (-1022 <= k)%Z ->
  Rabs (B2R x) < bpow radix2 k -> (Generic.exponent x < k)%Z.
Proof.
intros x k Fx Hk H.
destruct (Z_lt_le_dec (Generic.exponent x) (-1022)) as [L|L]; [lia|].
pose proof (bpow_exponent_le_abs_B2R x Fx L) as H0.
assert (H1 : bpow radix2 (Generic.exponent x) < bpow radix2 k) by lra.
apply lt_bpow in H1. exact H1.
Qed.

Local Lemma exponent_ge :
  forall x k, is_finite x = true -> bpow radix2 k <= Rabs (B2R x) ->
  (k <= Generic.exponent x)%Z.
Proof.
intros x k Fx H.
pose proof (abs_B2R_lt_exponent x Fx) as H0.
assert (H1 : bpow radix2 k < bpow radix2 (Generic.exponent x + 1)) by lra.
apply lt_bpow in H1. lia.
Qed.

Local Lemma exponent_small :
  forall x, is_finite x = true -> Rabs (B2R x) <= 8 -> (Generic.exponent x < 4)%Z.
Proof.
intros x Fx H.
apply exponent_lt; [exact Fx | lia |].
change (bpow radix2 4) with 16. lra.
Qed.

(** Both variants of [two_prod_is_exact] hold for operands and a product
    of moderate exponents. *)
Local Lemma two_prod_is_exact_of :
  forall fma x y,
  (-968 <= Generic.exponent (mul x y) <= 1022)%Z ->
  (Generic.exponent x <= 995)%Z -> (Generic.exponent y <= 995)%Z ->
  Generic.two_prod_is_exact fma x y (mul x y) = true.
Proof.
intros fma x y Ep Ex Ey.
destruct fma; cbv beta iota zeta delta [Generic.two_prod_is_exact];
  repeat (apply andb_true_intro; split); apply Z.leb_le; lia.
Qed.

(** An error of [x d] against [n] is one of [x] against [n / d]. *)
Local Lemma div_rel :
  forall X N D e, 0 < D -> 0 <= N ->
  Rabs (X * D - N) <= e * N -> Rabs (X - N / D) <= e * (N / D).
Proof.
intros X N D e HD HN H.
replace (X - N / D) with ((X * D - N) / D) by (field; lra).
unfold Rdiv. rewrite Rabs_mult, Rabs_inv, (Rabs_pos_eq D) by lra.
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; exact HD | exact H].
Qed.

(** The rounding error of [RN(r / d)], times [d]. *)
Local Lemma mul_div_err :
  forall S R D, 0 < D ->
  Rabs (S - R / D) <= bpow radix2 (-53) * Rabs (R / D) + bpow radix2 (-1075) ->
  Rabs (S * D - R) <= bpow radix2 (-53) * Rabs R + bpow radix2 (-1075) * D.
Proof.
intros S R D HD H.
replace (S * D - R) with ((S - R / D) * D) by (field; lra).
replace (Rabs R) with (Rabs (R / D) * D)
  by (unfold Rdiv; rewrite Rabs_mult, Rabs_inv, (Rabs_pos_eq D) by lra; field; lra).
rewrite Rabs_mult, (Rabs_pos_eq D) by lra.
apply Rle_trans with ((bpow radix2 (-53) * Rabs (R / D) + bpow radix2 (-1075)) * D).
- apply Rmult_le_compat_r; lra.
- right; ring.
Qed.

(** ** The leading quotient and its remainder *)

(** [qh = RN(nh / dh)] lies in [[2^-82, 8]], the remainder [nh - qh dh]
    is an [f64] of at most [2^-52 nh] ([DivRemainder.div_remainder]), and
    the product [qh dh] passes both checks of [two_prod_is_exact]. *)
Local Lemma quot :
  forall nh dh, is_finite nh = true -> is_finite dh = true ->
  bpow radix2 (-80) <= B2R nh <= 4 -> / 2 <= B2R dh <= 4 ->
  is_finite (div nh dh) = true /\ B2R (div nh dh) = RN (B2R nh / B2R dh) /\
  bpow radix2 (-82) <= B2R (div nh dh) <= 8 /\
  format (B2R nh - B2R (div nh dh) * B2R dh) /\
  Rabs (B2R nh - B2R (div nh dh) * B2R dh) <= bpow radix2 (-52) * Rabs (B2R nh) /\
  bpow radix2 (-967) <= Rabs (B2R nh) /\
  Generic.two_prod_is_exact true (div nh dh) dh (mul (div nh dh) dh) = true /\
  Generic.two_prod_is_exact false (div nh dh) dh (mul (div nh dh) dh) = true /\
  (Generic.exponent nh <= 1021)%Z /\ (Generic.exponent (div nh dh) <= 995)%Z /\
  (Generic.exponent dh <= 995)%Z.
Proof.
intros nh dh Fn Fd HN HD.
pose proof (bpow_gt_0 radix2 (-82)) as P82.
assert (Hd0 : B2R dh <> 0) by (intro; lra).
(* [nh / dh] lies in [[2^-80 / 4, 4 / (1/2)]]. *)
assert (Hz : bpow radix2 (-82) <= B2R nh / B2R dh <= 8).
{ split; apply Rmult_le_reg_r with (B2R dh); try lra; unfold Rdiv;
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra; num. }
assert (Hz16 : Rabs (B2R nh / B2R dh) <= 16) by (rewrite Rabs_pos_eq; lra).
destruct (div_e nh dh Fn Fd Hd0 Hz16) as (Fq & Rq).
(* Rounding is monotone and [2^-82] and [8] are [f64]s. *)
assert (HQ : bpow radix2 (-82) <= B2R (div nh dh) <= 8).
{ rewrite Rq. split.
  - apply round_ge_generic; [typeclasses eauto .. | | lra].
    apply generic_format_FLT_bpow; [typeclasses eauto | lia].
  - apply round_le_generic; [typeclasses eauto .. | | lra].
    change 8 with (bpow radix2 3).
    apply generic_format_FLT_bpow; [typeclasses eauto | lia]. }
assert (HN0 : bpow radix2 (-967) <= Rabs (B2R nh)).
{ rewrite Rabs_pos_eq by num. apply Rle_trans with (2 := proj1 HN). apply bpow_le. lia. }
assert (HQn : bpow radix2 (-1022) <= Rabs (RN (B2R nh / B2R dh))).
{ rewrite <- Rq, Rabs_pos_eq by lra.
  apply Rle_trans with (2 := proj1 HQ). apply bpow_le. lia. }
assert (Gn : format (B2R nh)) by apply generic_format_B2R.
assert (Gd : format (B2R dh)) by apply generic_format_B2R.
destruct (DivRemainder.div_remainder (B2R nh) (B2R dh) Gn Gd Hd0 HQn HN0) as (Fr0 & Hr0).
rewrite <- Rq in Fr0, Hr0.
(* [qh dh] is within [2^-52 nh] of [nh], so in [[nh / 2, 2 nh]]. *)
assert (HQD : B2R nh / 2 <= B2R (div nh dh) * B2R dh <= 2 * B2R nh).
{ pose proof Hr0 as H. rewrite (Rabs_pos_eq (B2R nh)) in H by num.
  apply Rabs_le_inv in H. num. }
assert (KQD : Rabs (B2R (div nh dh) * B2R dh) <= 16) by (rewrite Rabs_pos_eq; lra).
destruct (FastExpErr.mul_e (div nh dh) dh Fq Fd KQD) as (Fp & Rp & _).
assert (HP : bpow radix2 (-82) <= B2R (mul (div nh dh) dh) <= 8).
{ rewrite Rp. split.
  - apply round_ge_generic; [typeclasses eauto .. | | num].
    apply generic_format_FLT_bpow; [typeclasses eauto | lia].
  - apply round_le_generic; [typeclasses eauto .. | | lra].
    change 8 with (bpow radix2 3).
    apply generic_format_FLT_bpow; [typeclasses eauto | lia]. }
(* The exponents that [two_prod_is_exact] and [div_dekker_remainder]
   check. *)
assert (Ep1 : (-82 <= Generic.exponent (mul (div nh dh) dh))%Z).
{ apply exponent_ge; [exact Fp | rewrite Rabs_pos_eq; lra]. }
assert (Ep2 : (Generic.exponent (mul (div nh dh) dh) < 4)%Z).
{ apply exponent_small; [exact Fp | rewrite Rabs_pos_eq; lra]. }
assert (Eq : (Generic.exponent (div nh dh) < 4)%Z).
{ apply exponent_small; [exact Fq | rewrite Rabs_pos_eq; lra]. }
assert (Ed : (Generic.exponent dh < 4)%Z).
{ apply exponent_small; [exact Fd | rewrite Rabs_pos_eq; lra]. }
assert (En : (Generic.exponent nh < 4)%Z).
{ apply exponent_small; [exact Fn | rewrite Rabs_pos_eq; num]. }
split; [exact Fq |]. split; [exact Rq |]. split; [exact HQ |].
split; [exact Fr0 |]. split; [exact Hr0 |]. split; [exact HN0 |].
split; [apply two_prod_is_exact_of; lia |].
split; [apply two_prod_is_exact_of; lia |].
split; [lia |]. split; lia.
Qed.

(** ** The theorems *)

(** [Fast.dd_div fma nh nl dh dl] is [(nh + nl) / (dh + dl)] within
    [2^-98] relatively, as an unevaluated sum [qh + ql] with [qh] the
    rounding of [qh + ql] to nearest. *)
Theorem dd_div_correct :
  forall fma nh nl dh dl,
  is_finite nh = true -> is_finite nl = true -> is_finite dh = true -> is_finite dl = true ->
  bpow radix2 (-80) <= B2R nh <= 4 -> Rabs (B2R nl) <= bpow radix2 (-50) * B2R nh ->
  / 2 <= B2R dh <= 4 -> Rabs (B2R dl) <= bpow radix2 (-52) * B2R dh ->
  let '(qh, ql) := Fast.dd_div fma nh nl dh dl in
  is_finite qh = true /\ is_finite ql = true /\ B2R qh = RN (B2R qh + B2R ql) /\
  Rabs (B2R qh + B2R ql - (B2R nh + B2R nl) / (B2R dh + B2R dl))
    <= bpow radix2 (-98) * ((B2R nh + B2R nl) / (B2R dh + B2R dl)).
Proof.
intros fma nh nl dh dl Fnh Fnl Fdh Fdl HN HL HD HE.
destruct (quot nh dh Fnh Fdh HN HD)
  as (Fq & Rq & HQ & Fr0 & Hr0 & HN0 & T1 & T0 & En & Eq & Ed).
(* The remainder [(nh - p) - pe] is [nh - qh dh] exactly, and [pe] is the
   same with an FMA as with Dekker's product. *)
destruct (DivRuFast.div_dekker_remainder nh (div nh dh) dh Fnh Fq Fdh Fr0 Hr0 HN0 En Eq Ed)
  as (Fa & Ra).
assert (Epe : Generic.two_prod_err fma (div nh dh) dh (mul (div nh dh) dh) =
              Generic.two_prod_err false (div nh dh) dh (mul (div nh dh) dh)).
{ destruct fma; [exact (two_prod_err_fma_eq _ _ Fq Fdh T1 T0) | reflexivity]. }
cbv beta iota zeta delta [Fast.dd_div Fast.fast_two_sum].
rewrite Epe. clear Epe T1 T0 Fr0 HN0 En Eq Ed.
set (qh := div nh dh) in *.
set (a := sub (sub nh (mul qh dh)) (Generic.two_prod_err false qh dh (mul qh dh))) in *.
pose proof (bpow_gt_0 radix2 (-82)) as P82.
assert (HD0 : 0 < B2R dh) by lra.
rewrite (Rabs_pos_eq (B2R nh)) in Hr0 by num.
apply Rabs_le_inv in Hr0.
pose proof (Rabs_le_inv _ _ HL) as HL2.
pose proof (Rabs_le_inv _ _ HE) as HE2.
(* [b = RN(a + nl)], with [|a + nl| <= 5 * 2^-52 nh]. *)
assert (Kb : Rabs (B2R a + B2R nl) <= 5 * bpow radix2 (-52) * B2R nh)
  by (apply Rabs_le; num).
assert (Kb' : 5 * bpow radix2 (-52) * B2R nh <= 16) by num.
destruct (FastExpErr.add_k a nl _ Fa Fnl Kb Kb') as (Fb & _ & Eb).
clear Kb Kb'.
set (b := add a nl) in *.
apply Rabs_le_inv in Eb.
(* [c = RN(qh dl)], with [|qh dl| <= 2^-52 qh dh <= 2 * 2^-52 nh]. *)
assert (HQE : Rabs (B2R qh * B2R dl) <= bpow radix2 (-52) * (B2R qh * B2R dh)).
{ rewrite Rabs_mult, (Rabs_pos_eq (B2R qh)) by lra.
  replace (bpow radix2 (-52) * (B2R qh * B2R dh))
    with (B2R qh * (bpow radix2 (-52) * B2R dh)) by ring.
  apply Rmult_le_compat_l; [lra | exact HE]. }
assert (Kc : Rabs (B2R qh * B2R dl) <= 2 * bpow radix2 (-52) * B2R nh) by num.
assert (Kc' : 2 * bpow radix2 (-52) * B2R nh <= 16) by num.
destruct (FastExpErr.mul_k qh dl _ Fq Fdl Kc Kc') as (Fc & _ & Ec).
clear HQE Kc'.
set (c := mul qh dl) in *.
apply Rabs_le_inv in Ec. apply Rabs_le_inv in Kc.
(* [r = RN(b - c)], with [|b - c| <= 8 * 2^-52 nh]. *)
assert (Kr : Rabs (B2R b - B2R c) <= 8 * bpow radix2 (-52) * B2R nh)
  by (apply Rabs_le; num).
assert (Kr' : 8 * bpow radix2 (-52) * B2R nh <= 16) by num.
destruct (FastExpErr.sub_k b c _ Fb Fc Kr Kr') as (Fr & _ & Er).
clear Kr'.
set (r := sub b c) in *.
apply Rabs_le_inv in Er. apply Rabs_le_inv in Kr.
assert (HRv : Rabs (B2R r) <= 9 * bpow radix2 (-52) * B2R nh) by (apply Rabs_le; num).
pose proof (Rabs_le_inv _ _ HRv) as HRv2.
(* [sv = RN(r / dh)], and [|sv dh - r| <= 2^-53 |r| + 2^-1075 dh]. *)
assert (Hd0 : B2R dh <> 0) by lra.
assert (Ks : Rabs (B2R r / B2R dh) <= 16).
{ unfold Rdiv. rewrite Rabs_mult, Rabs_inv, (Rabs_pos_eq (B2R dh)) by lra.
  assert (Iv : / B2R dh <= 2).
  { apply Rmult_le_reg_r with (B2R dh); [lra |]. rewrite Rinv_l by lra. lra. }
  apply Rle_trans with (Rabs (B2R r) * 2).
  - apply Rmult_le_compat_l; [apply Rabs_pos | exact Iv].
  - num. }
destruct (div_e r dh Fr Fdh Hd0 Ks) as (Fs & Rs).
pose proof (FastExpErr.rn_err (B2R r / B2R dh)) as Es. rewrite <- Rs in Es.
pose proof (mul_div_err _ _ _ HD0 Es) as Esd.
clear Ks Es.
set (sv := div r dh) in *.
apply Rabs_le_inv in Esd.
assert (HSD : Rabs (B2R sv * B2R dh) <= 10 * bpow radix2 (-52) * B2R nh)
  by (apply Rabs_le; num).
(* Fast2Sum applies: [|sv| dh <= 10 * 2^-52 nh <= qh dh]. *)
assert (HS : Rabs (B2R sv) <= Rabs (B2R qh)).
{ rewrite (Rabs_pos_eq (B2R qh)) by lra.
  apply Rmult_le_reg_r with (B2R dh); [lra |].
  replace (Rabs (B2R sv) * B2R dh) with (Rabs (B2R sv * B2R dh))
    by (rewrite Rabs_mult, (Rabs_pos_eq (B2R dh)) by lra; reflexivity).
  num. }
assert (Kt : Rabs (B2R qh + B2R sv) <= 16).
{ eapply Rle_trans; [apply Rabs_triang |].
  rewrite (Rabs_pos_eq (B2R qh)) in HS |- * by lra. lra. }
assert (Kt' : (16 <= 16)%R) by lra.
destruct (FastExpErr.add_k qh sv 16 Fq Fs Kt Kt') as (Ft & Rt & _).
destruct (CancelLanes.fast_two_sum qh sv (add qh sv) Fq Fs HS Ft Rt) as (Fl & Rl).
rewrite Rl.
replace (B2R (add qh sv) + (B2R qh + B2R sv - B2R (add qh sv)))
  with (B2R qh + B2R sv) by ring.
split; [exact Ft |]. split; [exact Fl |]. split; [exact Rt |].
(* The error: [(qh + sv)(dh + dl) - (nh + nl)] is
   [(sv dh - r) + (r - (b - c)) + (b - (a + nl)) - (c - qh dl) + sv dl],
   at most [(9 + 8 + 5 + 2) 2^-105 nh + 10 * 2^-104 nh + 7 * 2^-1075],
   which is below [2^-98 (nh + nl)]. *)
assert (HSE : Rabs (B2R sv * B2R dl) <= bpow radix2 (-52) * Rabs (B2R sv * B2R dh)).
{ rewrite !Rabs_mult, (Rabs_pos_eq (B2R dh)) by lra.
  replace (bpow radix2 (-52) * (Rabs (B2R sv) * B2R dh))
    with (Rabs (B2R sv) * (bpow radix2 (-52) * B2R dh)) by ring.
  apply Rmult_le_compat_l; [apply Rabs_pos | exact HE]. }
apply Rabs_le_inv in HSE.
apply div_rel; [num | num |].
replace ((B2R qh + B2R sv) * (B2R dh + B2R dl) - (B2R nh + B2R nl))
  with (B2R qh * B2R dh + B2R qh * B2R dl + B2R sv * B2R dh + B2R sv * B2R dl
        - B2R nh - B2R nl) by ring.
apply Rabs_le. num.
Qed.

(** [Fast.dd_div] returns the same with and without an FMA. *)
Theorem dd_div_fma :
  forall nh nl dh dl,
  is_finite nh = true -> is_finite nl = true -> is_finite dh = true -> is_finite dl = true ->
  bpow radix2 (-80) <= B2R nh <= 4 -> Rabs (B2R nl) <= bpow radix2 (-50) * B2R nh ->
  / 2 <= B2R dh <= 4 -> Rabs (B2R dl) <= bpow radix2 (-52) * B2R dh ->
  Fast.dd_div true nh nl dh dl = Fast.dd_div false nh nl dh dl.
Proof.
intros nh nl dh dl Fnh Fnl Fdh Fdl HN HL HD HE.
destruct (quot nh dh Fnh Fdh HN HD) as (Fq & _ & _ & _ & _ & _ & T1 & T0 & _).
(* The product [qh dh] is exact, so its error is the same [f64] either
   way ([FastRound.two_prod_err_fma_eq]). *)
cbv beta iota zeta delta [Fast.dd_div].
rewrite (two_prod_err_fma_eq _ _ Fq Fdh T1 T0).
reflexivity.
Qed.
