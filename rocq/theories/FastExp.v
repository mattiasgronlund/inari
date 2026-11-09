(** * The fast paths of [exp], [exp2] and [exp10]

    Where [DyadicExp.fast_exp_dir] and the others of [Model.v] return,
    they return [e^x], [2^x] and [10^x] rounded toward +inf if [up] and
    toward -inf otherwise ([fast_exp_dir_correct] and the others), and
    rounded to nearest ([fast_exp_near_correct] and the others), from the
    bound of [FastExpCore.v] and the tests of [FastRound.v]. [2^x] and
    [10^x] are [e^(x c)] for [c] = ln 2 and ln 10 in double-double, with
    an exact product [x c_h] where [|x|] is at least the [TINY_EXP] or
    [TINY_EXP10] of the rules before them. They return the same with and
    without an FMA ([fast_exp_dir_fma] and the others). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Elementary TwoSum TwoProduct MulRuTiny DyDriver NearF64
  FastRound FastExpTables FastExpCore.

Open Scope R_scope.

(** ** The argument of [fast_exp] for [exp2] and [exp10]

    [fast_exp_by x c] passes [zh = RN(x c_h)] and [zl = RN((x c_h - zh) +
    RN(x c_l))] to [fast_exp], where [x c_h - zh] is exact by
    [TwoProduct.v] once [|x| >= 2^-56] and [|zh| <= 709]. Then [|x| <
    2^11], [|x c_h - zh| <= 2^-43], [|x c_l| <= 2^-41], [|zl| <= 2^-40],
    and [zh + zl] is [x c] within [2^-92] when [c_h + c_l] is [c] within
    [2^-105] ([fe_by_core]). That moves [e^(zh + zl) 2^-e], which is at
    most 5, by at most [10 * 2^-92 <= 2^-72], so the bound [2^-68 -
    2^-72] of [fast_exp_correct] becomes [2^-68] ([fe_by_correct]). *)

(** [B2R l] of an [f64] literal [l], as [m * 2^e]. *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** The same as a hypothesis [H]. *)
Local Ltac lit_hyp l H :=
  let s := eval vm_compute in (B2SF l) in
  assert (H : B2R l = SF2R radix2 s)
    by (rewrite <- (SF2R_B2SF _ _ l); replace (B2SF l) with s by (vm_compute; reflexivity);
        reflexivity);
  cbn [SF2R SpecFloat.cond_Zopp] in H; unfold F2R in H; cbn [Fnum Fexp] in H;
  rewrite ?opp_IZR in H.

(** The range test of [fast_exp], [-707.0 <= zh && zh <= 709.0]. *)
Local Notation in_range zh :=
  (Model.le (from_bits 0xc086180000000000) zh && Model.le zh (from_bits 0x4086280000000000)).

Lemma fe_le_R :
  forall x y, is_finite x = true -> is_finite y = true -> Model.le x y = true -> B2R x <= B2R y.
Proof.
intros x y Fx Fy H. unfold Model.le in H. rewrite Bleb_correct in H by assumption.
destruct (Rle_bool_spec (B2R x) (B2R y)); [assumption | discriminate].
Qed.

Lemma fe_out : forall fma zh zl, in_range zh = false -> DyadicExp.fast_exp fma zh zl = None.
Proof. intros fma zh zl G. unfold DyadicExp.fast_exp. rewrite G. reflexivity. Qed.

Lemma fe_range : forall zh, in_range zh = true -> is_finite zh = true /\ Rabs (B2R zh) <= 709.
Proof.
intros zh G. apply andb_prop in G as [G1 G2].
assert (Fz : is_finite zh = true).
{ destruct zh as [s|[|]| |s m e B]; try reflexivity; vm_compute in G1, G2; discriminate. }
split; [exact Fz|].
apply fe_le_R in G1; [| vm_compute; reflexivity | exact Fz].
apply fe_le_R in G2; [| exact Fz | vm_compute; reflexivity].
assert (L1 : B2R (from_bits 0xc086180000000000) = -707)
  by (lit_B2R; cbn [bpow radix_val radix2]; lra).
assert (L2 : B2R (from_bits 0x4086280000000000) = 709)
  by (lit_B2R; cbn [bpow radix_val radix2]; lra).
apply Rabs_le. lra.
Qed.

(** Where [fast_exp] returns, [zh] is in its range. *)
Lemma fe_in :
  forall fma zh zl r, DyadicExp.fast_exp fma zh zl = Some r ->
  is_finite zh = true /\ Rabs (B2R zh) <= 709.
Proof.
intros fma zh zl r H. destruct (in_range zh) eqn:G; [exact (fe_range zh G)|].
rewrite fe_out in H by exact G. discriminate H.
Qed.

Lemma fe_finite : forall x : f64, bpow radix2 (-56) <= Rabs (B2R x) -> is_finite x = true.
Proof.
intros [s|s| |s m e B] H; try reflexivity; cbn [B2R] in H; rewrite Rabs_R0 in H;
  pose proof (bpow_gt_0 radix2 (-56)); lra.
Qed.

(** Rounding to nearest moves a real of magnitude at most [2^k] by at
    most half its ulp, [2^(k - 53)], for [k >= -1021]. *)
Lemma fe_RN_err :
  forall z k, (-1021 <= k)%Z -> Rabs z <= bpow radix2 k -> Rabs (RN z - z) <= bpow radix2 (k - 53).
Proof.
intros z k Hk Hz.
apply Rle_trans with (/ 2 * ulp radix2 (FLT_exp (-1074) 53) z).
{ apply error_le_half_ulp; typeclasses eauto. }
apply Rle_trans with (/ 2 * ulp radix2 (FLT_exp (-1074) 53) (bpow radix2 k)).
{ apply Rmult_le_compat_l; [lra|]. apply ulp_le; [typeclasses eauto .. |].
  rewrite (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0. exact Hz. }
rewrite ulp_bpow.
replace (FLT_exp (-1074) 53 (k + 1)) with (1 + (k - 53))%Z by (unfold FLT_exp; lia).
rewrite bpow_plus. change (bpow radix2 1) with 2. lra.
Qed.

(** [|e^u - 1| <= 2 |u|] for [|u| <= 1/2]. *)
Lemma fe_exp_close : forall u, Rabs u <= / 2 -> Rabs (exp u - 1) <= 2 * Rabs u.
Proof.
intros u Hu.
pose proof (exp_ineq1_le u) as H1. pose proof (exp_ineq1_le (- u)) as H2.
pose proof (exp_pos u) as P.
assert (E : exp u * exp (- u) = 1)
  by (rewrite <- exp_plus; replace (u + - u) with 0 by ring; apply exp_0).
assert (H3 : exp u * (1 - u) <= 1) by (rewrite <- E; apply Rmult_le_compat_l; lra).
apply Rabs_le_inv in Hu.
destruct (Rle_or_lt 0 u) as [Hp | Hn].
- rewrite (Rabs_pos_eq u Hp). assert (E2 : exp u <= 2) by nra.
  apply Rabs_le; split; nra.
- rewrite (Rabs_left u Hn). apply Rabs_le; split; nra.
Qed.

Lemma fe_by_bounds :
  forall x ch, is_finite x = true -> is_finite ch = true -> / 2 <= B2R ch <= 4 ->
  is_finite (mul x ch) = true -> Rabs (B2R (mul x ch)) <= 709 ->
  Rabs (B2R x * B2R ch) < bpow radix2 10 /\ Rabs (B2R x) < bpow radix2 11.
Proof.
intros x ch Fx Fc Hc Fp Hp.
rewrite (mul_B2R x ch Fx Fc Fp) in Hp.
assert (H10 : Rabs (B2R x * B2R ch) < bpow radix2 10).
{ apply abs_lt_of_RN_lt; [lia|].
  assert (bpow radix2 10 = 1024) by (cbn [bpow radix_val radix2]; lra). lra. }
split; [exact H10|].
assert (E11 : bpow radix2 11 = 2 * bpow radix2 10)
  by (change 11%Z with (1 + 10)%Z; rewrite bpow_plus; reflexivity).
rewrite Rabs_mult, (Rabs_pos_eq (B2R ch)) in H10 by lra.
pose proof (Rabs_pos (B2R x)). nra.
Qed.

(** The product [x c_h] is exact by [Generic.two_prod_err], with and
    without an FMA. *)
Lemma fe_by_exact :
  forall fma x ch, is_finite x = true -> is_finite ch = true -> / 2 <= B2R ch <= 4 ->
  bpow radix2 (-56) <= Rabs (B2R x) ->
  is_finite (mul x ch) = true -> Rabs (B2R (mul x ch)) <= 709 ->
  Generic.two_prod_is_exact fma x ch (mul x ch) = true.
Proof.
intros fma x ch Fx Fc Hc Hx Fp Hp.
destruct (fe_by_bounds x ch Fx Fc Hc Fp Hp) as [H10 H11].
assert (E1 : (-57 <= Generic.exponent (mul x ch))%Z).
{ apply exponent_ge; [exact Fp|]. rewrite (mul_B2R x ch Fx Fc Fp).
  apply abs_round_ge_generic; [typeclasses eauto .. | |].
  - apply generic_format_FLT_bpow; [typeclasses eauto .. | lia].
  - rewrite Rabs_mult, (Rabs_pos_eq (B2R ch)) by lra.
    assert (bpow radix2 (-56) = 2 * bpow radix2 (-57))
      by (change (-56)%Z with (1 + -57)%Z; rewrite bpow_plus; reflexivity).
    pose proof (bpow_gt_0 radix2 (-57)). nra. }
assert (E2 : (Generic.exponent (mul x ch) < 10)%Z).
{ apply exponent_lt; [exact Fp | lia |].
  assert (bpow radix2 10 = 1024) by (cbn [bpow radix_val radix2]; lra). lra. }
assert (E3 : (Generic.exponent x < 11)%Z) by (apply exponent_lt; [exact Fx | lia | exact H11]).
assert (E4 : (Generic.exponent ch < 3)%Z).
{ apply exponent_lt; [exact Fc | lia |]. rewrite Rabs_pos_eq by lra.
  assert (bpow radix2 3 = 8) by (cbn [bpow radix_val radix2]; lra). lra. }
unfold Generic.two_prod_is_exact.
destruct fma; cbv beta iota zeta; repeat (apply andb_true_intro; split); apply Z.leb_le; lia.
Qed.

Lemma fe_by_core :
  forall fma x ch cl k,
  is_finite x = true -> is_finite ch = true -> is_finite cl = true ->
  / 2 <= B2R ch <= 4 -> Rabs (B2R cl) <= bpow radix2 (-52) ->
  Rabs (B2R ch + B2R cl - k) <= bpow radix2 (-105) ->
  bpow radix2 (-56) <= Rabs (B2R x) ->
  is_finite (mul x ch) = true -> Rabs (B2R (mul x ch)) <= 709 ->
  is_finite (add (Generic.two_prod_err fma x ch (mul x ch)) (mul x cl)) = true /\
  Rabs (B2R (add (Generic.two_prod_err fma x ch (mul x ch)) (mul x cl))) <= bpow radix2 (-40) /\
  Rabs (B2R (mul x ch) + B2R (add (Generic.two_prod_err fma x ch (mul x ch)) (mul x cl))
        - B2R x * k) <= bpow radix2 (-92).
Proof.
intros fma x ch cl k Fx Fc Fl Hc Hl Hk Hx Fp Hp.
destruct (fe_by_bounds x ch Fx Fc Hc Fp Hp) as [H10 H11].
pose proof (fe_by_exact fma x ch Fx Fc Hc Hx Fp Hp) as Ex.
destruct (two_prod_err_correct fma x ch Fx Fc Ex) as (_ & Ep & _ & Ft & Et).
set (t := Generic.two_prod_err fma x ch (mul x ch)) in *.
assert (Ht : Rabs (B2R t) <= bpow radix2 (-43)).
{ rewrite Et, Ep, <- Rabs_Ropp.
  replace (- (B2R x * B2R ch - RN (B2R x * B2R ch)))
    with (RN (B2R x * B2R ch) - B2R x * B2R ch) by ring.
  apply (fe_RN_err _ 10); [lia | lra]. }
assert (Hxl : Rabs (B2R x * B2R cl) <= bpow radix2 (-41)).
{ rewrite Rabs_mult.
  replace (bpow radix2 (-41)) with (bpow radix2 11 * bpow radix2 (-52))
    by (rewrite <- bpow_plus; reflexivity).
  apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | lra | exact Hl]. }
assert (Hb : Rabs (B2R x * B2R cl) <= bpow radix2 1023)
  by (eapply Rle_trans; [exact Hxl | apply bpow_le; lia]).
destruct (mul_RN_spec x cl Fx Fl Hb) as (Fm & Em & _).
set (m := mul x cl) in *.
assert (Hm : Rabs (B2R m - B2R x * B2R cl) <= bpow radix2 (-94))
  by (rewrite Em; apply (fe_RN_err _ (-41)); [lia | exact Hxl]).
assert (HM : bpow radix2 (-43) + bpow radix2 (-41) + bpow radix2 (-94) <= bpow radix2 (-40) /\
             bpow radix2 (-40) <= bpow radix2 1023 + bpow radix2 971 /\
             bpow radix2 11 * bpow radix2 (-105) = bpow radix2 (-94) /\
             bpow radix2 (-94) + bpow radix2 (-94) + bpow radix2 (-93) = bpow radix2 (-92))
  by (cbn [bpow radix_val radix2]; lra).
apply Rabs_le_inv in Ht, Hxl, Hm.
assert (Htm : Rabs (B2R t + B2R m) <= bpow radix2 (-40)) by (apply Rabs_le; lra).
destruct (add_no_overflow t m Ft Fm ltac:(lra)) as (Fz & Ez).
split; [exact Fz|]. split.
{ rewrite Ez. apply abs_round_le_generic; [typeclasses eauto .. | | exact Htm].
  apply generic_format_FLT_bpow; [typeclasses eauto .. | lia]. }
assert (Hz : Rabs (B2R (add t m) - (B2R t + B2R m)) <= bpow radix2 (-93))
  by (rewrite Ez; apply (fe_RN_err _ (-40)); [lia | exact Htm]).
assert (Hd : Rabs (B2R x * (B2R ch + B2R cl - k)) <= bpow radix2 (-94)).
{ rewrite Rabs_mult. destruct HM as (_ & _ & <- & _).
  apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | lra | exact Hk]. }
assert (Eq : B2R x * (B2R ch + B2R cl - k) = B2R x * B2R ch + B2R x * B2R cl - B2R x * k)
  by ring.
apply Rabs_le_inv in Hz, Hd. apply Rabs_le. lra.
Qed.

(** Where [fast_exp_by x c] returns, its [h + l] is [e^(x k) 2^-e]
    within [2^-68], for [c_h + c_l] within [2^-105] of [k]. *)
Lemma fe_by_correct :
  forall fma x c k h l e,
  is_finite (from_bits (fst c)) = true -> is_finite (from_bits (snd c)) = true ->
  / 2 <= B2R (from_bits (fst c)) <= 4 -> Rabs (B2R (from_bits (snd c))) <= bpow radix2 (-52) ->
  Rabs (B2R (from_bits (fst c)) + B2R (from_bits (snd c)) - k) <= bpow radix2 (-105) ->
  is_finite x = true -> bpow radix2 (-56) <= Rabs (B2R x) ->
  DyadicExp.fast_exp_by fma x c = Some (h, l, e) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < B2R h < 2 /\ (-1021 <= e <= 1022)%Z /\
  Rabs (exp (B2R x * k) * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (-68).
Proof.
intros fma x c k h l e Fc Fl Hc Hl Hk Fx Hx H.
unfold DyadicExp.fast_exp_by in H. cbv beta iota zeta in H.
set (ch := from_bits (fst c)) in *. set (cl := from_bits (snd c)) in *.
destruct (fe_in _ _ _ _ H) as [Fp Hp].
destruct (fe_by_core fma x ch cl k Fx Fc Fl Hc Hl Hk Hx Fp Hp) as (Fzl & Hzl & Hd).
destruct (fast_exp_correct fma _ _ h l e Fp Fzl Hzl H) as (Fh & Fl' & Eh & Hh & He & Herr).
do 5 (split; [assumption|]).
set (a := B2R (mul x ch) + B2R (add _ _)) in *.
set (u := B2R x * k - a).
assert (Hu : Rabs u <= bpow radix2 (-92))
  by (unfold u; rewrite <- Rabs_Ropp; replace (- (B2R x * k - a)) with (a - B2R x * k) by ring;
      exact Hd).
assert (HM : bpow radix2 (-92) <= / 2 /\ 10 * bpow radix2 (-92) <= bpow radix2 (-72) /\
             bpow radix2 2 = 4 /\ bpow radix2 (-68) <= 1)
  by (cbn [bpow radix_val radix2]; lra).
destruct HM as (HM1 & HM2 & HM3 & HM4).
pose proof (fe_exp_close u ltac:(lra)) as Hc'.
assert (Hhl : Rabs (B2R h + B2R l) < bpow radix2 2)
  by (apply abs_lt_of_RN_lt; [lia | rewrite <- Eh, Rabs_pos_eq by lra; lra]).
set (A := exp a * bpow radix2 (- e)) in *.
assert (A0 : 0 < A) by (apply Rmult_lt_0_compat; [apply exp_pos | apply bpow_gt_0]).
apply Rabs_def2 in Hhl. destruct Hhl as [Hhl1 Hhl2].
pose proof Herr as Herr'. apply Rabs_le_inv in Herr'.
pose proof (bpow_gt_0 radix2 (-72)).
assert (A5 : A <= 5) by lra.
assert (EA : exp (B2R x * k) * bpow radix2 (- e) = A + A * (exp u - 1)).
{ unfold A, u. replace (B2R x * k) with (a + (B2R x * k - a)) at 1 by ring.
  rewrite exp_plus. ring. }
assert (HA : Rabs (A * (exp u - 1)) <= 10 * bpow radix2 (-92)).
{ rewrite Rabs_mult, (Rabs_pos_eq A) by lra.
  replace (10 * bpow radix2 (-92)) with (5 * (2 * bpow radix2 (-92))) by ring.
  apply Rmult_le_compat; [lra | apply Rabs_pos | lra | lra]. }
rewrite EA. apply Rabs_le_inv in HA. apply Rabs_le.
pose proof (bpow_gt_0 radix2 (-72)). lra.
Qed.

(** [LN2] and [LN10] meet the hypotheses of [fe_by_correct]. *)
Lemma fe_ln2 :
  is_finite (from_bits (fst DyadicExp.LN2)) = true /\
  is_finite (from_bits (snd DyadicExp.LN2)) = true /\
  / 2 <= B2R (from_bits (fst DyadicExp.LN2)) <= 4 /\
  Rabs (B2R (from_bits (snd DyadicExp.LN2))) <= bpow radix2 (-52) /\
  Rabs (B2R (from_bits (fst DyadicExp.LN2)) + B2R (from_bits (snd DyadicExp.LN2)) - ln 2)
    <= bpow radix2 (-105).
Proof.
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
lit_hyp (from_bits (fst DyadicExp.LN2)) Eh. lit_hyp (from_bits (snd DyadicExp.LN2)) El.
split; [rewrite Eh; cbn [bpow radix_val radix2]; lra|].
split; [rewrite El; apply Rabs_le; cbn [bpow radix_val radix2]; lra|].
eapply Rle_trans; [apply ln2_dd_correct | apply bpow_le; lia].
Qed.

Lemma fe_ln10 :
  is_finite (from_bits (fst DyadicExp.LN10)) = true /\
  is_finite (from_bits (snd DyadicExp.LN10)) = true /\
  / 2 <= B2R (from_bits (fst DyadicExp.LN10)) <= 4 /\
  Rabs (B2R (from_bits (snd DyadicExp.LN10))) <= bpow radix2 (-52) /\
  Rabs (B2R (from_bits (fst DyadicExp.LN10)) + B2R (from_bits (snd DyadicExp.LN10)) - ln 10)
    <= bpow radix2 (-105).
Proof.
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
lit_hyp (from_bits (fst DyadicExp.LN10)) Eh. lit_hyp (from_bits (snd DyadicExp.LN10)) El.
split; [rewrite Eh; cbn [bpow radix_val radix2]; lra|].
split; [rewrite El; apply Rabs_le; cbn [bpow radix_val radix2]; lra|].
exact ln10_dd_correct.
Qed.

(** [fast_exp_by] is the same with and without an FMA. *)
Lemma fe_by_fma :
  forall x c, is_finite (from_bits (fst c)) = true -> / 2 <= B2R (from_bits (fst c)) <= 4 ->
  bpow radix2 (-56) <= Rabs (B2R x) ->
  DyadicExp.fast_exp_by true x c = DyadicExp.fast_exp_by false x c.
Proof.
intros x c Fc Hc Hx. pose proof (fe_finite x Hx) as Fx.
unfold DyadicExp.fast_exp_by. cbv beta iota zeta.
set (ch := from_bits (fst c)) in *.
rewrite fast_exp_fma.
destruct (in_range (mul x ch)) eqn:G; [| rewrite !fe_out by exact G; reflexivity].
destruct (fe_range _ G) as [Fp Hp].
rewrite (two_prod_err_fma_eq x ch Fx Fc (fe_by_exact true x ch Fx Fc Hc Hx Fp Hp)
  (fe_by_exact false x ch Fx Fc Hc Hx Fp Hp)).
reflexivity.
Qed.

(** The arguments that the rules of [exp2] and [exp10] leave. *)
Lemma tiny_exp_false :
  forall x, is_finite x = true -> lt (fabs x) DyadicExp.tiny_exp = false ->
  bpow radix2 (-54) <= Rabs (B2R x).
Proof.
intros x Fx H. unfold Model.lt in H.
rewrite Bltb_correct in H
  by (unfold fabs; rewrite ?is_finite_Babs; first [exact Fx | vm_compute; reflexivity]).
assert (L : B2R DyadicExp.tiny_exp = bpow radix2 (-54)).
{ lit_B2R. change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
  reflexivity. }
destruct (Rlt_bool_spec (B2R (fabs x)) (B2R DyadicExp.tiny_exp)); [discriminate H|].
unfold fabs in *. rewrite B2R_Babs in *. lra.
Qed.

Lemma tiny_exp10_false :
  forall x, is_finite x = true -> lt (fabs x) DyadicExp.tiny_exp10 = false ->
  bpow radix2 (-56) <= Rabs (B2R x).
Proof.
intros x Fx H. unfold Model.lt in H.
rewrite Bltb_correct in H
  by (unfold fabs; rewrite ?is_finite_Babs; first [exact Fx | vm_compute; reflexivity]).
assert (L : B2R DyadicExp.tiny_exp10 = bpow radix2 (-56)).
{ lit_B2R. change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
  reflexivity. }
destruct (Rlt_bool_spec (B2R (fabs x)) (B2R DyadicExp.tiny_exp10)); [discriminate H|].
unfold fabs in *. rewrite B2R_Babs in *. lra.
Qed.

(** ** Rounded toward -inf and +inf *)

Theorem fast_exp_dir_correct :
  forall fma x up v,
  is_finite x = true -> DyadicExp.fast_exp_dir fma x up = Some v ->
  rounds up (exp (B2R x)) v.
Proof.
intros fma x up v Fx H. unfold DyadicExp.fast_exp_dir in H.
destruct (DyadicExp.fast_exp fma x zero) as [[[h l] e]|] eqn:E; [|discriminate H].
assert (Z0 : Rabs (B2R zero) <= bpow radix2 (-40))
  by (change (B2R zero) with 0; rewrite Rabs_R0; apply bpow_ge_0).
destruct (fast_exp_correct fma x zero h l e Fx eq_refl Z0 E) as (Fh & Fl & Eh & Hh & He & Herr).
replace (exp (B2R x)) with (exp (B2R x + B2R zero) * bpow radix2 (- e) * bpow radix2 e).
2: { change (B2R zero) with 0. rewrite Rplus_0_r, Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l.
     change (bpow radix2 0) with 1. ring. }
apply (round_dir_correct h l e up v); try assumption.
pose proof (bpow_gt_0 radix2 (-72)). lra.
Qed.

Theorem fast_exp2_dir_correct :
  forall fma x up v,
  is_finite x = true -> bpow radix2 (-54) <= Rabs (B2R x) ->
  DyadicExp.fast_exp2_dir fma x up = Some v ->
  rounds up (Rexp2 (B2R x)) v.
Proof.
intros fma x up v Fx Hx H. unfold DyadicExp.fast_exp2_dir in H.
destruct (DyadicExp.fast_exp_by fma x DyadicExp.LN2) as [[[h l] e]|] eqn:E; [|discriminate H].
destruct fe_ln2 as (Fc & Fl & Hc & Hl & Hk).
assert (Hx' : bpow radix2 (-56) <= Rabs (B2R x))
  by (apply Rle_trans with (bpow radix2 (-54)); [apply bpow_le; lia | exact Hx]).
destruct (fe_by_correct fma x _ (ln 2) h l e Fc Fl Hc Hl Hk Fx Hx' E)
  as (Fh & Fl' & Eh & Hh & He & Herr).
replace (Rexp2 (B2R x)) with (exp (B2R x * ln 2) * bpow radix2 (- e) * bpow radix2 e).
2: { rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l. change (bpow radix2 0) with 1.
     rewrite Rmult_1_r. reflexivity. }
exact (round_dir_correct h l e up v _ Fh Fl' Eh Hh He Herr H).
Qed.

Theorem fast_exp10_dir_correct :
  forall fma x up v,
  is_finite x = true -> bpow radix2 (-56) <= Rabs (B2R x) ->
  DyadicExp.fast_exp10_dir fma x up = Some v ->
  rounds up (Rexp10 (B2R x)) v.
Proof.
intros fma x up v Fx Hx H. unfold DyadicExp.fast_exp10_dir in H.
destruct (DyadicExp.fast_exp_by fma x DyadicExp.LN10) as [[[h l] e]|] eqn:E; [|discriminate H].
destruct fe_ln10 as (Fc & Fl & Hc & Hl & Hk).
destruct (fe_by_correct fma x _ (ln 10) h l e Fc Fl Hc Hl Hk Fx Hx E)
  as (Fh & Fl' & Eh & Hh & He & Herr).
replace (Rexp10 (B2R x)) with (exp (B2R x * ln 10) * bpow radix2 (- e) * bpow radix2 e).
2: { rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l. change (bpow radix2 0) with 1.
     rewrite Rmult_1_r. reflexivity. }
exact (round_dir_correct h l e up v _ Fh Fl' Eh Hh He Herr H).
Qed.

(** ** Rounded to nearest *)

Theorem fast_exp_near_correct :
  forall fma x v,
  is_finite x = true -> DyadicExp.fast_exp_near fma x = Some v ->
  near_round (exp (B2R x)) v.
Proof.
intros fma x v Fx H. unfold DyadicExp.fast_exp_near in H.
destruct (DyadicExp.fast_exp fma x zero) as [[[h l] e]|] eqn:E; [|discriminate H].
assert (Z0 : Rabs (B2R zero) <= bpow radix2 (-40))
  by (change (B2R zero) with 0; rewrite Rabs_R0; apply bpow_ge_0).
destruct (fast_exp_correct fma x zero h l e Fx eq_refl Z0 E) as (Fh & Fl & Eh & Hh & He & Herr).
replace (exp (B2R x)) with (exp (B2R x + B2R zero) * bpow radix2 (- e) * bpow radix2 e).
2: { change (B2R zero) with 0. rewrite Rplus_0_r, Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l.
     change (bpow radix2 0) with 1. ring. }
apply (round_near_correct h l e v); try assumption.
pose proof (bpow_gt_0 radix2 (-72)). lra.
Qed.

Theorem fast_exp2_near_correct :
  forall fma x v,
  is_finite x = true -> bpow radix2 (-54) <= Rabs (B2R x) ->
  DyadicExp.fast_exp2_near fma x = Some v ->
  near_round (Rexp2 (B2R x)) v.
Proof.
intros fma x v Fx Hx H. unfold DyadicExp.fast_exp2_near in H.
destruct (DyadicExp.fast_exp_by fma x DyadicExp.LN2) as [[[h l] e]|] eqn:E; [|discriminate H].
destruct fe_ln2 as (Fc & Fl & Hc & Hl & Hk).
assert (Hx' : bpow radix2 (-56) <= Rabs (B2R x))
  by (apply Rle_trans with (bpow radix2 (-54)); [apply bpow_le; lia | exact Hx]).
destruct (fe_by_correct fma x _ (ln 2) h l e Fc Fl Hc Hl Hk Fx Hx' E)
  as (Fh & Fl' & Eh & Hh & He & Herr).
replace (Rexp2 (B2R x)) with (exp (B2R x * ln 2) * bpow radix2 (- e) * bpow radix2 e).
2: { rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l. change (bpow radix2 0) with 1.
     rewrite Rmult_1_r. reflexivity. }
exact (round_near_correct h l e v _ Fh Fl' Eh Hh He Herr H).
Qed.

Theorem fast_exp10_near_correct :
  forall fma x v,
  is_finite x = true -> bpow radix2 (-56) <= Rabs (B2R x) ->
  DyadicExp.fast_exp10_near fma x = Some v ->
  near_round (Rexp10 (B2R x)) v.
Proof.
intros fma x v Fx Hx H. unfold DyadicExp.fast_exp10_near in H.
destruct (DyadicExp.fast_exp_by fma x DyadicExp.LN10) as [[[h l] e]|] eqn:E; [|discriminate H].
destruct fe_ln10 as (Fc & Fl & Hc & Hl & Hk).
destruct (fe_by_correct fma x _ (ln 10) h l e Fc Fl Hc Hl Hk Fx Hx E)
  as (Fh & Fl' & Eh & Hh & He & Herr).
replace (Rexp10 (B2R x)) with (exp (B2R x * ln 10) * bpow radix2 (- e) * bpow radix2 e).
2: { rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l. change (bpow radix2 0) with 1.
     rewrite Rmult_1_r. reflexivity. }
exact (round_near_correct h l e v _ Fh Fl' Eh Hh He Herr H).
Qed.

(** ** With and without an FMA *)

Theorem fast_exp_dir_fma :
  forall x up, DyadicExp.fast_exp_dir true x up = DyadicExp.fast_exp_dir false x up.
Proof.
intros x up. unfold DyadicExp.fast_exp_dir. rewrite fast_exp_fma. reflexivity.
Qed.

Theorem fast_exp2_dir_fma :
  forall x up, bpow radix2 (-54) <= Rabs (B2R x) ->
  DyadicExp.fast_exp2_dir true x up = DyadicExp.fast_exp2_dir false x up.
Proof.
intros x up Hx. unfold DyadicExp.fast_exp2_dir.
destruct fe_ln2 as (Fc & _ & Hc & _).
rewrite (fe_by_fma x _ Fc Hc) by (apply Rle_trans with (bpow radix2 (-54)); [apply bpow_le; lia | exact Hx]).
reflexivity.
Qed.

Theorem fast_exp10_dir_fma :
  forall x up, bpow radix2 (-56) <= Rabs (B2R x) ->
  DyadicExp.fast_exp10_dir true x up = DyadicExp.fast_exp10_dir false x up.
Proof.
intros x up Hx. unfold DyadicExp.fast_exp10_dir.
destruct fe_ln10 as (Fc & _ & Hc & _).
rewrite (fe_by_fma x _ Fc Hc Hx). reflexivity.
Qed.

Theorem fast_exp_near_fma :
  forall x, DyadicExp.fast_exp_near true x = DyadicExp.fast_exp_near false x.
Proof.
intros x. unfold DyadicExp.fast_exp_near. rewrite fast_exp_fma. reflexivity.
Qed.

Theorem fast_exp2_near_fma :
  forall x, bpow radix2 (-54) <= Rabs (B2R x) ->
  DyadicExp.fast_exp2_near true x = DyadicExp.fast_exp2_near false x.
Proof.
intros x Hx. unfold DyadicExp.fast_exp2_near.
destruct fe_ln2 as (Fc & _ & Hc & _).
rewrite (fe_by_fma x _ Fc Hc) by (apply Rle_trans with (bpow radix2 (-54)); [apply bpow_le; lia | exact Hx]).
reflexivity.
Qed.

Theorem fast_exp10_near_fma :
  forall x, bpow radix2 (-56) <= Rabs (B2R x) ->
  DyadicExp.fast_exp10_near true x = DyadicExp.fast_exp10_near false x.
Proof.
intros x Hx. unfold DyadicExp.fast_exp10_near.
destruct fe_ln10 as (Fc & _ & Hc & _).
rewrite (fe_by_fma x _ Fc Hc Hx). reflexivity.
Qed.
