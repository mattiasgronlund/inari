(** * The fast path of [pow] and [pown]

    [DyadicPow.fast_pow] of [Model.v] computes x^y = e^(y ln x) for a
    finite [x > 0]: ln x as [lh + ll] within [17/16 2^-79 |ln x|]
    ([FastPowLn.ln_acc_correct]), [t = y ln x] as [th + tl] with [th =
    RN(y lh)] and [tl] the error of that product ([TwoProduct.v]) plus
    [RN(y ll)], and [e^(th + tl)] by [DyadicExp.fast_exp]
    ([FastExpCore.fast_exp_correct]), which returns [None] unless [|th|
    <= 709]. Where it returns, [y lh] is exact as [th] plus its error,
    as [2^-61 <= |th| <= 709] and [|y| < 2^65], so that [th + tl] is
    within [3/4 2^-69] of [y ln x] ([FastPowMul.fast_pow_mul]). A change
    [d] of [z] moves [e^z 2^-e], which is below [2 + 2^-68] as [h =
    RN(h + l)] and [h < 2], by at most [(2 + 2^-68) d (1 + 2 d)]
    ([fp_compose]). So [fast_pow_correct] shows that [x^y 2^-e] is
    within [2^-67] of [h + l], with [1/2 < h < 2] and [h = RN(h + l)],
    where [|y ln x| >= 2^-60], which holds wherever [pow] and [pown]
    call it at [x <> 1], and also at [x = 1] for [|y| <= 2^900], where
    [lh = ll = th = tl = 0] ([FastPowMul.fast_pow_mul_one]).

    [fast_pow_dir_correct] and [fast_pow_near_correct] prove the fast
    paths of [pow] and [pown] in all three roundings, with the tests of
    [FastRoundErr.v] at [2^-67], and [fast_pow_dir_fma] and
    [fast_pow_near_fma] that an FMA gives the same results. At [x = 1],
    where the signs of the zeros passed to [fast_exp] may depend on the
    FMA, both directed paths return [None] and both paths to nearest
    return 1, for each sign, by computation. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Elementary Encoding TwoSum TwoProduct MulRuTiny DyDriver
  NearF64 FastRound FastExpErr FastExp FastExpCore FastRoundErr FastPowLn FastPowMul.

Open Scope R_scope.

(** ** Helpers *)

(** [B2R l] of an [f64] literal [l], as [m * 2^e] (as in [FastExp.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** A literal [2^k] with a mantissa of [2^52] (as in [FastHypPos.v]). *)
Local Ltac lit_pow2 :=
  lit_B2R; change (IZR 4503599627370496) with (bpow radix2 52); rewrite <- bpow_plus;
  reflexivity.

Local Lemma lit_err67 : B2R DyadicExp.err67 = bpow radix2 (-67).
Proof. lit_pow2. Qed.

(** The range test of [fast_exp], [-707.0 <= zh && zh <= 709.0], as in
    [FastExp.v]. *)
Local Notation in_range zh :=
  (Model.le (from_bits 0xc086180000000000) zh && Model.le zh (from_bits 0x4086280000000000)).

(** As in [FastHyp.v]. *)
Local Lemma scale_back : forall y e, y = y * bpow radix2 (- e) * bpow radix2 e.
Proof.
intros y e. rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l.
change (bpow radix2 0) with 1. ring.
Qed.

(** [|e^d - 1| <= |d| (1 + 2 |d|)], as [FastExpCore.v]'s [fc_exp_close]:
    [1 + d <= e^d] and [1 - d <= e^-d], so [e^d (1 - d) <= 1]. *)
Local Lemma fp_exp_close : forall d, Rabs d <= / 4 -> Rabs (exp d - 1) <= Rabs d * (1 + 2 * Rabs d).
Proof.
intros d Hd.
pose proof (exp_ineq1_le d) as H1. pose proof (exp_ineq1_le (- d)) as H2.
pose proof (exp_pos d) as P.
assert (E : exp d * exp (- d) = 1)
  by (rewrite <- exp_plus; replace (d + - d) with 0 by ring; apply exp_0).
assert (H3 : exp d * (1 - d) <= 1) by (rewrite <- E; apply Rmult_le_compat_l; lra).
apply Rabs_le_inv in Hd.
destruct (Rle_or_lt 0 d) as [Hp | Hn].
- rewrite (Rabs_pos_eq d Hp).
  assert (E2 : exp d <= 1 + 2 * d) by nra.
  apply Rabs_le; split; nra.
- rewrite (Rabs_left d Hn).
  assert (E1 : exp d <= 1) by nra.
  apply Rabs_le; split; nra.
Qed.

(** ** The composition *)

(** If [h + l] is [e^z A] within [2^-68 - 2^-72], with [h = RN(h + l)]
    and [1/2 < h < 2], then it is [e^t A] within [2^-67] for [|t - z| <=
    3/4 2^-69]: [e^z A < 2 + 2^-68], and [e^t A - e^z A = e^z A (e^(t -
    z) - 1)]. *)
Local Lemma fp_compose :
  forall t z A (h l : f64),
  B2R h = RN (B2R h + B2R l) -> / 2 < B2R h < 2 ->
  Rabs (exp z * A - (B2R h + B2R l)) <= bpow radix2 (-68) - bpow radix2 (-72) ->
  0 < A -> Rabs (t - z) <= 3 / 4 * bpow radix2 (-69) ->
  Rabs (exp t * A - (B2R h + B2R l)) <= bpow radix2 (-67).
Proof.
intros t z A h l Eh Hh Herr A0 Hu.
set (c := 3 / 4 * bpow radix2 (-69)) in Hu.
set (u := t - z) in Hu.
assert (HM : c <= / 4 /\ 0 <= c /\
             bpow radix2 (-68) - bpow radix2 (-72) + (2 + bpow radix2 (-68)) * (c * (1 + 2 * c))
               <= bpow radix2 (-67) /\ bpow radix2 1 = 2 /\ 0 < bpow radix2 (-72))
  by (unfold c; cbn [bpow radix_val radix2]; repeat split; lra).
destruct HM as (HM1 & HM2 & HM3 & HM4 & HM5).
(* [|h + l| < 2], as [|RN(h + l)| = h < 2]. *)
assert (Hhl : Rabs (B2R h + B2R l) < 2).
{ rewrite <- HM4. apply abs_lt_of_RN_lt; [lia|].
  rewrite <- Eh, HM4, Rabs_pos_eq by lra. lra. }
pose proof (fp_exp_close u ltac:(lra)) as Hc.
set (B := exp z * A) in *.
assert (B0 : 0 < B) by (apply Rmult_lt_0_compat; [apply exp_pos | exact A0]).
assert (EB : exp t * A = B + B * (exp u - 1)).
{ unfold B, u. replace t with (z + (t - z)) at 1 by ring. rewrite exp_plus. ring. }
pose proof Herr as Herr'. apply Rabs_le_inv in Herr'. apply Rabs_def2 in Hhl.
assert (B2 : B <= 2 + bpow radix2 (-68)) by lra.
assert (Hc2 : Rabs u * (1 + 2 * Rabs u) <= c * (1 + 2 * c))
  by (pose proof (Rabs_pos u); apply Rmult_le_compat; lra).
assert (HB : Rabs (B * (exp u - 1)) <= (2 + bpow radix2 (-68)) * (c * (1 + 2 * c))).
{ rewrite Rabs_mult, (Rabs_pos_eq B) by lra.
  apply Rmult_le_compat; [lra | apply Rabs_pos | exact B2 |].
  eapply Rle_trans; [exact Hc | exact Hc2]. }
rewrite EB. apply Rabs_le_inv in HB. apply Rabs_le. lra.
Qed.

Theorem fast_pow_correct :
  forall fma x y h l e,
  is_finite x = true -> 0 < B2R x -> is_finite y = true ->
  ((B2R x = 1 /\ Rabs (B2R y) <= bpow radix2 900) \/
   bpow radix2 (-60) <= Rabs (B2R y * ln (B2R x))) ->
  DyadicPow.fast_pow fma x y = Some (h, l, e) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < B2R h < 2 /\ (-1021 <= e <= 1022)%Z /\
  Rabs (Rpower (B2R x) (B2R y) * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (-67).
Proof.
intros fma x y h l e Fx Px Fy Hyp H.
destruct Hyp as [[X1 Hy] | Hb].
- (* [x = 1]: [fast_exp] of two zeros, and [y ln x = 0] exactly. *)
  destruct (fast_pow_mul_one fma x y Fx X1 Fy Hy) as (sh & sl & E).
  rewrite E in H.
  assert (Z0 : Rabs (B2R (B754_zero sl : f64)) <= bpow radix2 (-40))
    by (cbn [B2R]; rewrite Rabs_R0; apply bpow_ge_0).
  destruct (fast_exp_correct fma (B754_zero sh) (B754_zero sl) h l e eq_refl eq_refl Z0 H)
    as (Fh & Fl & Eh & Hh & He & Herr).
  do 5 (split; [assumption|]).
  unfold Rpower. eapply fp_compose; [exact Eh | exact Hh | exact Herr | apply bpow_gt_0 |].
  replace (B2R y * ln (B2R x) - (B2R (B754_zero sh : f64) + B2R (B754_zero sl : f64))) with 0.
  2: { rewrite X1, ln_1. cbn [B2R]. ring. }
  rewrite Rabs_R0. apply Rmult_le_pos; [lra | apply bpow_ge_0].
- (* [|y ln x| >= 2^-60]: [fast_pow_mul] bounds [th + tl - y ln x]. *)
  unfold DyadicPow.fast_pow in H.
  destruct (DyadicLog.ln_acc fma x) as [lh ll] eqn:Ln.
  pose proof (fast_pow_mul fma x y Fx Px Fy Hb) as M. rewrite Ln in M.
  cbv beta iota zeta in H, M.
  destruct (fe_in _ _ _ _ H) as [Fth Hth].
  destruct (M Fth Hth) as (Ftl & Htl & Hd & _).
  destruct (fast_exp_correct fma _ _ h l e Fth Ftl Htl H) as (Fh & Fl & Eh & Hh & He & Herr).
  do 5 (split; [assumption|]).
  unfold Rpower. eapply fp_compose; [exact Eh | exact Hh | exact Herr | apply bpow_gt_0 |].
  exact Hd.
Qed.

(** ** The three roundings *)

Theorem fast_pow_dir_correct :
  forall fma x y up v,
  is_finite x = true -> 0 < B2R x -> is_finite y = true ->
  ((B2R x = 1 /\ Rabs (B2R y) <= bpow radix2 900) \/
   bpow radix2 (-60) <= Rabs (B2R y * ln (B2R x))) ->
  DyadicPow.fast_pow_dir fma x y up = Some v ->
  rounds up (Rpower (B2R x) (B2R y)) v.
Proof.
intros fma x y up v Fx Px Fy Hyp H. unfold DyadicPow.fast_pow_dir in H.
destruct (DyadicPow.fast_pow fma x y) as [[[h l] e]|] eqn:E; [|discriminate H].
destruct (fast_pow_correct fma x y h l e Fx Px Fy Hyp E) as (Fh & Fl & Eh & Hh & He & Herr).
rewrite (scale_back (Rpower (B2R x) (B2R y)) e).
exact (round_dir_err_correct h l e DyadicExp.err67 67 up v _ Fh Fl Eh He ltac:(lia) lit_err67
  Herr H).
Qed.

Theorem fast_pow_near_correct :
  forall fma x y v,
  is_finite x = true -> 0 < B2R x -> is_finite y = true ->
  ((B2R x = 1 /\ Rabs (B2R y) <= bpow radix2 900) \/
   bpow radix2 (-60) <= Rabs (B2R y * ln (B2R x))) ->
  DyadicPow.fast_pow_near fma x y = Some v ->
  near_round (Rpower (B2R x) (B2R y)) v.
Proof.
intros fma x y v Fx Px Fy Hyp H. unfold DyadicPow.fast_pow_near in H.
destruct (DyadicPow.fast_pow fma x y) as [[[h l] e]|] eqn:E; [|discriminate H].
destruct (fast_pow_correct fma x y h l e Fx Px Fy Hyp E) as (Fh & Fl & Eh & Hh & He & Herr).
rewrite (scale_back (Rpower (B2R x) (B2R y)) e).
exact (round_near_err_correct h l e DyadicExp.err67 67 v _ Fh Fl Eh He ltac:(lia) lit_err67
  Herr H).
Qed.

(** ** An FMA gives the same results *)

(** At [x = 1], [fast_exp] of two zeros returns [h + l = 1], so the
    directed test fails and the test to nearest returns 1, whatever the
    signs of the zeros and the FMA. *)
Local Lemma fp_one_dir :
  forall fma x y up,
  is_finite x = true -> B2R x = 1 -> is_finite y = true -> Rabs (B2R y) <= bpow radix2 900 ->
  DyadicPow.fast_pow_dir fma x y up = None.
Proof.
intros fma x y up Fx X1 Fy Hy.
destruct (fast_pow_mul_one fma x y Fx X1 Fy Hy) as (sh & sl & E).
unfold DyadicPow.fast_pow_dir. rewrite E.
destruct fma, sh, sl, up; vm_compute; reflexivity.
Qed.

Local Lemma fp_one_near :
  forall fma x y,
  is_finite x = true -> B2R x = 1 -> is_finite y = true -> Rabs (B2R y) <= bpow radix2 900 ->
  option_map B2SF (DyadicPow.fast_pow_near fma x y) = Some (B2SF DyadicExp.one).
Proof.
intros fma x y Fx X1 Fy Hy.
destruct (fast_pow_mul_one fma x y Fx X1 Fy Hy) as (sh & sl & E).
unfold DyadicPow.fast_pow_near. rewrite E.
destruct fma, sh, sl; vm_compute; reflexivity.
Qed.

(** For [|y ln x| >= 2^-60], [ln_acc] and [fast_exp] do not depend on
    the FMA, and neither does the error of [y lh] where [fast_exp]
    reads it. *)
Local Lemma fp_fma :
  forall x y,
  is_finite x = true -> 0 < B2R x -> is_finite y = true ->
  bpow radix2 (-60) <= Rabs (B2R y * ln (B2R x)) ->
  DyadicPow.fast_pow true x y = DyadicPow.fast_pow false x y.
Proof.
intros x y Fx Px Fy Hb.
unfold DyadicPow.fast_pow. rewrite (ln_acc_fma x Fx Px).
destruct (DyadicLog.ln_acc false x) as [lh ll] eqn:Ln.
pose proof (fast_pow_mul false x y Fx Px Fy Hb) as M. rewrite Ln in M.
cbv beta iota zeta in M |- *.
rewrite fast_exp_fma.
destruct (in_range (mul y lh)) eqn:G; [| rewrite !fe_out by exact G; reflexivity].
destruct (fe_range _ G) as [Fth Hth].
destruct (M Fth Hth) as (_ & _ & _ & Ep).
rewrite Ep. reflexivity.
Qed.

Theorem fast_pow_dir_fma :
  forall x y up,
  is_finite x = true -> 0 < B2R x -> is_finite y = true ->
  ((B2R x = 1 /\ Rabs (B2R y) <= bpow radix2 900) \/
   bpow radix2 (-60) <= Rabs (B2R y * ln (B2R x))) ->
  DyadicPow.fast_pow_dir true x y up = DyadicPow.fast_pow_dir false x y up.
Proof.
intros x y up Fx Px Fy [[X1 Hy] | Hb].
- rewrite (fp_one_dir true x y up Fx X1 Fy Hy), (fp_one_dir false x y up Fx X1 Fy Hy).
  reflexivity.
- unfold DyadicPow.fast_pow_dir. rewrite (fp_fma x y Fx Px Fy Hb). reflexivity.
Qed.

Theorem fast_pow_near_fma :
  forall x y,
  is_finite x = true -> 0 < B2R x -> is_finite y = true ->
  ((B2R x = 1 /\ Rabs (B2R y) <= bpow radix2 900) \/
   bpow radix2 (-60) <= Rabs (B2R y * ln (B2R x))) ->
  DyadicPow.fast_pow_near true x y = DyadicPow.fast_pow_near false x y.
Proof.
intros x y Fx Px Fy [[X1 Hy] | Hb].
- pose proof (fp_one_near true x y Fx X1 Fy Hy) as O1.
  pose proof (fp_one_near false x y Fx X1 Fy Hy) as O2.
  destruct (DyadicPow.fast_pow_near true x y) as [v1|];
    destruct (DyadicPow.fast_pow_near false x y) as [v2|];
    cbn [option_map] in O1, O2; try discriminate.
  injection O1 as O1. injection O2 as O2.
  f_equal. apply B2SF_inj. rewrite O1, O2. reflexivity.
- unfold DyadicPow.fast_pow_near. rewrite (fp_fma x y Fx Px Fy Hb). reflexivity.
Qed.
