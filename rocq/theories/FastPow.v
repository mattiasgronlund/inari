(** * The fast path of [pow] and [pown]

    [DyadicPow.pow_t] of [Model.v] computes [t = y ln x] for a finite [x
    > 0] as [th + tl]: ln x as [lh + ll] within [17/16 2^-79 |ln x|]
    ([FastPowLn.ln_acc_correct]), [th = RN(y lh)] and [tl] the error of
    that product ([TwoProduct.v]) plus [RN(y ll)]. [DyadicPow.fast_pow_dir]
    and [DyadicPow.fast_pow_near] take [e^(th + tl)] from
    [DyadicExp.fast_exp] ([FastExpCore.fast_exp_correct]), which returns
    [None] unless [|th| <= 709]. Where it returns, [y lh] is exact as [th]
    plus its error, as [2^-61 <= |th| <= 709] and [|y| < 2^65], so that
    [th + tl] is within [3/4 2^-69] of [y ln x]
    ([FastPowMul.fast_pow_mul]). A change [d] of [z] moves [e^z 2^-e],
    which is below [2 + 2^-68] as [h = RN(h + l)] and [h < 2], by at most
    [(2 + 2^-68) d (1 + 2 d)] ([fp_compose]). So [fast_pow_correct] shows
    that [x^y 2^-e] is within [2^-67] of [h + l], with [1/2 < h < 2] and
    [h = RN(h + l)], where [|y ln x| >= 2^-60], which holds wherever [pow]
    and [pown] call it at [x <> 1], and also at [x = 1] for [|y| <=
    2^900], where [lh = ll = th = tl = 0] ([FastPowMul.fast_pow_mul_one]).

    Where [fast_exp] returns [None], [DyadicPow.fast_pow_wide_dir] and
    [DyadicPow.fast_pow_wide_near] return the overflow for [th >= T_OVER]
    and the underflow for [th <= T_UNDER] ([FastPowRules.v]), and between
    them, where [-746 < th < -707] or [709 < th < T_OVER], take [e^(th +
    tl)] from [DyadicExp.fast_exp_edge]
    ([FastExpEdge.fast_exp_edge_correct]): there [th + tl] is within
    [13/16 2^-69] of [y ln x] ([FastPowMul.fast_pow_mul_wide]), and [x^y
    2^-e] within [2^-67] of [h + l] ([fast_pow_edge_correct]), which the
    tests of [FastRoundWideErr.v] round, subnormal results included.

    [fast_pow_dir_correct] and [fast_pow_near_correct] prove the fast
    paths of [pow] and [pown] in all three roundings, and
    [fast_pow_dir_fma] and [fast_pow_near_fma] that an FMA gives the same
    results. At [x = 1], where the signs of the zeros passed to [fast_exp]
    may depend on the FMA, both directed paths return [None] and both
    paths to nearest return 1, for each sign, by computation. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Elementary Encoding TwoSum TwoProduct MulRuTiny DyDriver
  NearF64 FastRound FastExpErr FastExp FastExpCore FastRoundErr FastPowLn FastPowMul FastPowRules.
From Inari Require DyExpRules NearCells FastExpEdge FastRoundWide FastRoundWideErr.

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
  forall fma x y th tl h l e,
  is_finite x = true -> 0 < B2R x -> is_finite y = true ->
  ((B2R x = 1 /\ Rabs (B2R y) <= bpow radix2 900) \/
   bpow radix2 (-60) <= Rabs (B2R y * ln (B2R x))) ->
  DyadicPow.pow_t fma x y = (th, tl) ->
  DyadicExp.fast_exp fma th tl = Some (h, l, e) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < B2R h < 2 /\ (-1021 <= e <= 1022)%Z /\
  Rabs (Rpower (B2R x) (B2R y) * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (-67).
Proof.
intros fma x y th tl h l e Fx Px Fy Hyp Ht H.
destruct Hyp as [[X1 Hy] | Hb].
- (* [x = 1]: [fast_exp] of two zeros, and [y ln x = 0] exactly. *)
  destruct (fast_pow_mul_one fma x y Fx X1 Fy Hy) as (sh & sl & E).
  rewrite E in Ht. injection Ht as <- <-.
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
  unfold DyadicPow.pow_t in Ht.
  destruct (DyadicLog.ln_acc fma x) as [lh ll] eqn:Ln.
  pose proof (fast_pow_mul fma x y Fx Px Fy Hb) as M. rewrite Ln in M.
  cbv beta iota zeta in Ht, M. injection Ht as <- <-.
  destruct (fe_in _ _ _ _ H) as [Fth Hth].
  destruct (M Fth Hth) as (Ftl & Htl & Hd & _).
  destruct (fast_exp_correct fma _ _ h l e Fth Ftl Htl H) as (Fh & Fl & Eh & Hh & He & Herr).
  do 5 (split; [assumption|]).
  unfold Rpower. eapply fp_compose; [exact Eh | exact Hh | exact Herr | apply bpow_gt_0 |].
  exact Hd.
Qed.

(** ** Past the range of [fast_exp] *)

(** A copy of [fp_compose] with the bounds of the edge: [h + l] is [e^z
    A] within [2^-68 - 2^-73] ([FastExpEdge.fast_exp_edge_correct]), and
    [|t - z| <= 13/16 2^-69] ([FastPowMul.fast_pow_mul_wide]). *)
Local Lemma fp_compose_edge :
  forall t z A (h l : f64),
  B2R h = RN (B2R h + B2R l) -> / 2 < B2R h < 2 ->
  Rabs (exp z * A - (B2R h + B2R l)) <= bpow radix2 (-68) - bpow radix2 (-73) ->
  0 < A -> Rabs (t - z) <= 13 / 16 * bpow radix2 (-69) ->
  Rabs (exp t * A - (B2R h + B2R l)) <= bpow radix2 (-67).
Proof.
intros t z A h l Eh Hh Herr A0 Hu.
set (c := 13 / 16 * bpow radix2 (-69)) in Hu.
set (u := t - z) in Hu.
assert (HM : c <= / 4 /\ 0 <= c /\
             bpow radix2 (-68) - bpow radix2 (-73) + (2 + bpow radix2 (-68)) * (c * (1 + 2 * c))
               <= bpow radix2 (-67) /\ bpow radix2 1 = 2 /\ 0 < bpow radix2 (-73))
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

Theorem fast_pow_edge_correct :
  forall fma x y th tl h l e,
  is_finite x = true -> 0 < B2R x -> is_finite y = true ->
  bpow radix2 (-60) <= Rabs (B2R y * ln (B2R x)) ->
  DyadicPow.pow_t fma x y = (th, tl) ->
  is_finite th = true -> bpow radix2 9 <= Rabs (B2R th) <= 752 ->
  DyadicExp.fast_exp_edge fma th tl = Some (h, l, e) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < B2R h < 2 /\ (-1085 <= e <= 1026)%Z /\
  Rabs (Rpower (B2R x) (B2R y) * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (-67).
Proof.
intros fma x y th tl h l e Fx Px Fy Hb Ht Fth Hth H.
(* [fast_pow_mul_wide] bounds [th + tl - y ln x]. *)
unfold DyadicPow.pow_t in Ht.
destruct (DyadicLog.ln_acc fma x) as [lh ll] eqn:Ln.
pose proof (fast_pow_mul_wide fma x y Fx Px Fy Hb) as M. rewrite Ln in M.
cbv beta iota zeta in Ht, M. injection Ht as Eth Etl. rewrite Etl, Eth in M.
destruct (M Fth (proj2 Hth)) as (Ftl & Htl & Hd & _).
(* [fast_exp_edge_correct] at [a = th + tl] exactly. *)
assert (Z : Rabs (B2R th + B2R tl - (B2R th + B2R tl)) <= bpow radix2 (-92))
  by (rewrite Rminus_diag, Rabs_R0; apply bpow_ge_0).
destruct (FastExpEdge.fast_exp_edge_correct fma th tl _ h l e Fth Ftl (proj1 Hth) Htl Z H)
  as (Fh & Fl & Eh & Hh & He & Herr).
do 5 (split; [assumption|]).
unfold Rpower. eapply fp_compose_edge; [exact Eh | exact Hh | exact Herr | apply bpow_gt_0 |].
exact Hd.
Qed.

(** At [x = 1], [fast_exp] of the two zeros returns, so the fast path
    does not reach its [None] arm. *)
Local Lemma fp_one_some :
  forall fma x y th tl,
  is_finite x = true -> B2R x = 1 -> is_finite y = true -> Rabs (B2R y) <= bpow radix2 900 ->
  DyadicPow.pow_t fma x y = (th, tl) -> DyadicExp.fast_exp fma th tl = None -> False.
Proof.
intros fma x y th tl Fx X1 Fy Hy Ht E.
destruct (fast_pow_mul_one fma x y Fx X1 Fy Hy) as (sh & sl & E1).
rewrite E1 in Ht. injection Ht as <- <-.
(* Compute only whether [fast_exp] returns: reading back its [f64]s, with
   their proofs of boundedness, from [vm_compute in E] does not finish. *)
assert (S : option_map (fun _ => tt) (DyadicExp.fast_exp fma (B754_zero sh) (B754_zero sl)) =
            Some tt) by (destruct fma, sh, sl; vm_compute; reflexivity).
rewrite E in S. discriminate S.
Qed.

(** Below [T_OVER = 6243315534363256 2^-43] (about 709.7828) and above
    [T_UNDER = -746], [|th| <= 752]. *)
Local Lemma fp_wide_th :
  forall th, is_finite th = true ->
  Model.ge th DyadicPow.t_over = false -> Model.le th DyadicPow.t_under = false ->
  Rabs (B2R th) <= 752.
Proof.
intros th Fth G L.
assert (Fo : is_finite DyadicPow.t_over = true) by (vm_compute; reflexivity).
assert (Fu : is_finite DyadicPow.t_under = true) by (vm_compute; reflexivity).
pose proof (FastRound.ge_false th DyadicPow.t_over Fth Fo G) as G'.
assert (L' : B2R DyadicPow.t_under < B2R th).
{ unfold Model.le in L. rewrite Bleb_correct in L by assumption.
  destruct (Rle_bool_spec (B2R th) (B2R DyadicPow.t_under)); [discriminate L | assumption]. }
assert (To : B2R DyadicPow.t_over = 6243315534363256 * bpow radix2 (-43)) by (lit_B2R; ring).
assert (Tu : B2R DyadicPow.t_under = -746) by (lit_B2R; cbn [bpow radix_val radix2]; lra).
assert (B : 6243315534363256 * bpow radix2 (-43) <= 752) by (cbn [bpow radix_val radix2]; lra).
apply Rabs_le. lra.
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
destruct (DyadicPow.pow_t fma x y) as [th tl] eqn:Ht. cbv beta iota in H.
destruct (DyadicExp.fast_exp fma th tl) as [[[h l] e]|] eqn:E.
- destruct (fast_pow_correct fma x y th tl h l e Fx Px Fy Hyp Ht E)
    as (Fh & Fl & Eh & Hh & He & Herr).
  rewrite (scale_back (Rpower (B2R x) (B2R y)) e).
  exact (round_dir_err_correct h l e DyadicExp.err67 67 up v _ Fh Fl Eh He ltac:(lia) lit_err67
    Herr H).
- destruct Hyp as [[X1 Hy] | Hb]; [destruct (fp_one_some fma x y th tl Fx X1 Fy Hy Ht E)|].
  unfold DyadicPow.fast_pow_wide_dir in H.
  destruct (Model.ge th DyadicPow.t_over) eqn:G.
  { (* [x^y > 2^1024]. *)
    injection H as <-. unfold rounds. apply DyExpRules.rnd_overflow.
    pose proof (fast_pow_overflow fma x y th tl Fx Px Fy Ht G). lra. }
  destruct (Model.le th DyadicPow.t_under) eqn:L.
  { (* [0 < x^y < 2^-1075]. *)
    injection H as <-. unfold rounds. apply DyExpRules.rnd_underflow.
    pose proof (fast_pow_underflow fma x y th tl Fx Px Fy Ht L).
    assert (bpow radix2 (-1075) < bpow radix2 (-1074)) by (apply bpow_lt; lia). lra. }
  (* Between them, [2^9 <= |th| <= 752]. *)
  destruct (DyadicExp.fast_exp_edge fma th tl) as [[[h l] e]|] eqn:E2; [|discriminate H].
  destruct (FastExpEdge.fast_exp_edge_in _ _ _ _ E2) as [Fth _].
  pose proof (fp_wide_th th Fth G L) as Hw.
  pose proof (fe_none fma th tl Fth E) as H9.
  destruct (fast_pow_edge_correct fma x y th tl h l e Fx Px Fy Hb Ht Fth (conj H9 Hw) E2)
    as (Fh & Fl & Eh & Hh & He & Herr).
  rewrite (scale_back (Rpower (B2R x) (B2R y)) e).
  exact (FastRoundWideErr.round_dir_wide_err_correct h l e DyadicExp.err67 67 up v _ Fh Fl Eh Hh
    ltac:(lia) ltac:(lia) lit_err67 Herr H).
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
destruct (DyadicPow.pow_t fma x y) as [th tl] eqn:Ht. cbv beta iota in H.
destruct (DyadicExp.fast_exp fma th tl) as [[[h l] e]|] eqn:E.
- destruct (fast_pow_correct fma x y th tl h l e Fx Px Fy Hyp Ht E)
    as (Fh & Fl & Eh & Hh & He & Herr).
  rewrite (scale_back (Rpower (B2R x) (B2R y)) e).
  exact (round_near_err_correct h l e DyadicExp.err67 67 v _ Fh Fl Eh He ltac:(lia) lit_err67
    Herr H).
- destruct Hyp as [[X1 Hy] | Hb]; [destruct (fp_one_some fma x y th tl Fx X1 Fy Hy Ht E)|].
  unfold DyadicPow.fast_pow_wide_near in H.
  destruct (Model.ge th DyadicPow.t_over) eqn:G.
  { (* [x^y > 2^1024]. *)
    injection H as <-. apply NearCells.near_inf.
    pose proof (fast_pow_overflow fma x y th tl Fx Px Fy Ht G).
    pose proof (bpow_gt_0 radix2 970). lra. }
  destruct (Model.le th DyadicPow.t_under) eqn:L.
  { (* [0 < x^y < 2^-1075]. *)
    injection H as <-. apply NearCells.near_zero.
    pose proof (fast_pow_underflow fma x y th tl Fx Px Fy Ht L). lra. }
  (* Between them, [2^9 <= |th| <= 752]. *)
  destruct (DyadicExp.fast_exp_edge fma th tl) as [[[h l] e]|] eqn:E2; [|discriminate H].
  destruct (FastExpEdge.fast_exp_edge_in _ _ _ _ E2) as [Fth _].
  pose proof (fp_wide_th th Fth G L) as Hw.
  pose proof (fe_none fma th tl Fth E) as H9.
  destruct (fast_pow_edge_correct fma x y th tl h l e Fx Px Fy Hb Ht Fth (conj H9 Hw) E2)
    as (Fh & Fl & Eh & Hh & He & Herr).
  rewrite (scale_back (Rpower (B2R x) (B2R y)) e).
  exact (FastRoundWideErr.round_near_wide_err_correct h l e DyadicExp.err67 67 v _ Fh Fl Eh Hh
    ltac:(lia) ltac:(lia) lit_err67 Herr H).
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

(** [pow_t] once [ln_acc] has returned. *)
Local Lemma fp_pow_t :
  forall fma x y lh ll, DyadicLog.ln_acc fma x = (lh, ll) ->
  DyadicPow.pow_t fma x y = (mul y lh, add (Generic.two_prod_err fma y lh (mul y lh)) (mul y ll)).
Proof. intros fma x y lh ll Ln. unfold DyadicPow.pow_t. rewrite Ln. reflexivity. Qed.

(** For [|y ln x| >= 2^-60], [ln_acc] does not depend on the FMA, so
    neither does [th]. Nor does [tl] where [|th| <= 752], as the error
    of [y lh] does not ([FastPowMul.fast_pow_mul_wide]). Elsewhere [tl]
    is not read: [fast_exp] and [fast_exp_edge] return [None] where [th]
    is not finite, and [fast_exp] where [|th| > 709], and past 752 the
    rules on [T_OVER] or [T_UNDER] return before [fast_exp_edge]. *)
Local Lemma fp_fma :
  forall x y th1 tl1 th tl,
  is_finite x = true -> 0 < B2R x -> is_finite y = true ->
  bpow radix2 (-60) <= Rabs (B2R y * ln (B2R x)) ->
  DyadicPow.pow_t true x y = (th1, tl1) -> DyadicPow.pow_t false x y = (th, tl) ->
  th1 = th /\
  (tl1 = tl \/
   (forall fma t, DyadicExp.fast_exp fma th t = None) /\
   (Model.ge th DyadicPow.t_over = true \/ Model.le th DyadicPow.t_under = true \/
    forall fma t, DyadicExp.fast_exp_edge fma th t = None)).
Proof.
intros x y th1 tl1 th tl Fx Px Fy Hb E1 E2.
destruct (DyadicLog.ln_acc false x) as [lh ll] eqn:Ln.
pose proof (fast_pow_mul_wide false x y Fx Px Fy Hb) as M. rewrite Ln in M.
cbv beta iota zeta in M.
(* Split the pairs with [fp_pow_t] and [pair_equal_spec]: [injection]
   unfolds [mul y lh], and [cbv] with projections made [Qed] take 17 s. *)
rewrite (fp_pow_t true x y lh ll) in E1 by (rewrite (ln_acc_fma x Fx Px); exact Ln).
rewrite (fp_pow_t false x y lh ll Ln) in E2.
apply pair_equal_spec in E1 as [<- <-]. apply pair_equal_spec in E2 as [<- <-].
split; [reflexivity|].
destruct (Bool.bool_dec (is_finite (mul y lh)) true) as [Fth | Fth].
2: { right. split.
     - intros fma t. destruct (DyadicExp.fast_exp fma (mul y lh) t) eqn:E; [|reflexivity].
       destruct (fe_in _ _ _ _ E) as [F _]. exfalso. exact (Fth F).
     - right; right. intros fma t.
       destruct (DyadicExp.fast_exp_edge fma (mul y lh) t) eqn:E; [|reflexivity].
       destruct (FastExpEdge.fast_exp_edge_in _ _ _ _ E) as [F _]. exfalso. exact (Fth F). }
destruct (Rle_or_lt (Rabs (B2R (mul y lh))) 752) as [Hs | Hs].
- left. destruct (M Fth Hs) as (_ & _ & _ & Ep). rewrite Ep. reflexivity.
- right. split.
  + intros fma t. destruct (DyadicExp.fast_exp fma (mul y lh) t) eqn:E; [|reflexivity].
    destruct (fe_in _ _ _ _ E) as [_ B]. lra.
  + destruct (Model.ge (mul y lh) DyadicPow.t_over) eqn:G; [left; reflexivity|].
    destruct (Model.le (mul y lh) DyadicPow.t_under) eqn:L; [right; left; reflexivity|].
    pose proof (fp_wide_th _ Fth G L). lra.
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
- unfold DyadicPow.fast_pow_dir.
  destruct (DyadicPow.pow_t true x y) as [th1 tl1] eqn:E1.
  destruct (DyadicPow.pow_t false x y) as [th tl] eqn:E2.
  destruct (fp_fma x y th1 tl1 th tl Fx Px Fy Hb E1 E2) as [<- [<- | [N W]]];
    cbv beta iota; unfold DyadicPow.fast_pow_wide_dir.
  + rewrite fast_exp_fma, FastExpEdge.fast_exp_edge_fma. reflexivity.
  + rewrite !N.
    destruct (Model.ge th1 DyadicPow.t_over) eqn:G; [reflexivity|].
    destruct (Model.le th1 DyadicPow.t_under) eqn:L; [reflexivity|].
    (* The two [destruct]s also turned [W]'s first two cases into [false = true]. *)
    destruct W as [W | [W | N2]]; [discriminate W | discriminate W |].
    rewrite !N2. reflexivity.
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
- unfold DyadicPow.fast_pow_near.
  destruct (DyadicPow.pow_t true x y) as [th1 tl1] eqn:E1.
  destruct (DyadicPow.pow_t false x y) as [th tl] eqn:E2.
  destruct (fp_fma x y th1 tl1 th tl Fx Px Fy Hb E1 E2) as [<- [<- | [N W]]];
    cbv beta iota; unfold DyadicPow.fast_pow_wide_near.
  + rewrite fast_exp_fma, FastExpEdge.fast_exp_edge_fma. reflexivity.
  + rewrite !N.
    destruct (Model.ge th1 DyadicPow.t_over) eqn:G; [reflexivity|].
    destruct (Model.le th1 DyadicPow.t_under) eqn:L; [reflexivity|].
    (* The two [destruct]s also turned [W]'s first two cases into [false = true]. *)
    destruct W as [W | [W | N2]]; [discriminate W | discriminate W |].
    rewrite !N2. reflexivity.
Qed.
