(** * The fast path of [exp] outside the range of [fast_exp]

    [DyadicExp.fast_exp_edge zh zl] of [Model.v] calls [fast_exp] on [z +
    64 ln 2] for [zh < 0] and on [z - 4 ln 2] otherwise, for [z = zh +
    zl], and returns its exponent less 64 or plus 4: [e^z = 2^-64 e^(z +
    64 ln 2) = 2^4 e^(z - 4 ln 2)]. [m ln 2] is [SH + SL] within [2^-98]
    for the [LN2_64] and [LN2_4] of [Model.v], with [SH] a multiple of
    [2^-43], so that [zh + SH] and [zh - SH] are exact where [|zh| >=
    2^9]. The shift then moves [z] by less than [2^-91] and the scaled
    result by less than [2^-87], so the bound [2^-68 - 2^-72] of
    [fast_exp_correct] becomes [2^-68 - 2^-73] ([fast_exp_edge_correct]).
    It returns the same with and without an FMA ([fast_exp_edge_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct MulRuTiny FastRound
  FastExpTables FastExpReduce FastExpCore.

Open Scope R_scope.

(** ** Helpers

    Copies of [FastExp.v]'s, which imports this file. *)

(** The same as [B2R l = m * 2^e] for an [f64] literal [l], as a
    hypothesis [H]. *)
Local Ltac lit_hyp l H :=
  let s := eval vm_compute in (B2SF l) in
  assert (H : B2R l = SF2R radix2 s)
    by (rewrite <- (SF2R_B2SF _ _ l); replace (B2SF l) with s by (vm_compute; reflexivity);
        reflexivity);
  cbn [SF2R SpecFloat.cond_Zopp] in H; unfold F2R in H; cbn [Fnum Fexp] in H;
  rewrite ?opp_IZR in H.

(** [B2R l] of an [f64] literal [l], as [m * 2^e]. *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** The range test of [fast_exp], [-707.0 <= zh && zh <= 709.0]. *)
Local Notation in_range zh :=
  (Model.le (from_bits 0xc086180000000000) zh && Model.le zh (from_bits 0x4086280000000000)).

Local Lemma ee_le_R :
  forall x y, is_finite x = true -> is_finite y = true -> Model.le x y = true -> B2R x <= B2R y.
Proof.
intros x y Fx Fy H. unfold Model.le in H. rewrite Bleb_correct in H by assumption.
destruct (Rle_bool_spec (B2R x) (B2R y)); [assumption | discriminate].
Qed.

Local Lemma ee_range : forall zh, in_range zh = true -> is_finite zh = true /\ Rabs (B2R zh) <= 709.
Proof.
intros zh G. apply andb_prop in G as [G1 G2].
assert (Fz : is_finite zh = true).
{ destruct zh as [s|[|]| |s m e B]; try reflexivity; vm_compute in G1, G2; discriminate. }
split; [exact Fz|].
apply ee_le_R in G1; [| vm_compute; reflexivity | exact Fz].
apply ee_le_R in G2; [| exact Fz | vm_compute; reflexivity].
assert (L1 : B2R (from_bits 0xc086180000000000) = -707)
  by (lit_B2R; cbn [bpow radix_val radix2]; lra).
assert (L2 : B2R (from_bits 0x4086280000000000) = 709)
  by (lit_B2R; cbn [bpow radix_val radix2]; lra).
apply Rabs_le. lra.
Qed.

(** Where [fast_exp] returns, [zh] is in its range. *)
Local Lemma ee_in :
  forall fma zh zl r, DyadicExp.fast_exp fma zh zl = Some r ->
  is_finite zh = true /\ Rabs (B2R zh) <= 709.
Proof.
intros fma zh zl r H. destruct (in_range zh) eqn:G; [exact (ee_range zh G)|].
unfold DyadicExp.fast_exp in H. rewrite G in H. discriminate H.
Qed.

(** Rounding to nearest moves a real of magnitude at most [2^k] by at
    most half its ulp, [2^(k - 53)], for [k >= -1021]. *)
Local Lemma ee_RN_err :
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
Local Lemma ee_exp_close : forall u, Rabs u <= / 2 -> Rabs (exp u - 1) <= 2 * Rabs u.
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

(** If [x - y] is finite, it is [RN(x - y)], as [TwoSum.add_B2R]. *)
Local Lemma ee_sub_B2R :
  forall x y, is_finite x = true -> is_finite y = true ->
  is_finite (sub x y) = true -> B2R (sub x y) = RN (B2R x - B2R y).
Proof.
intros x y Fx Fy Fs.
generalize (@Bminus_correct 53 1024 _ _ mode_NE x y Fx Fy).
destruct (Rlt_bool _ _).
- intros (HR & _). exact HR.
- intros (HO & _). exfalso.
  revert Fs HO. unfold sub.
  destruct (Bminus mode_NE x y); intros F HO; discriminate.
Qed.

(** ** The constants *)

Local Notation SH64 := (from_bits (fst DyadicExp.LN2_64)).
Local Notation SL64 := (from_bits (snd DyadicExp.LN2_64)).
Local Notation SH4 := (from_bits (fst DyadicExp.LN2_4)).
Local Notation SL4 := (from_bits (snd DyadicExp.LN2_4)).

(** [SH] is a multiple of [2^-43], [|SL| <= 2^-46], and [SH + SL] is [m ln
    2] within [2^-98]: within [2^-100] of [m (LN2[0] + LN2[1])], computed
    exactly, and [LN2] is ln 2 within [2^-106] ([ln2_dd_correct]). The
    shift for [zh >= 0] is [-SH4] and [-SL4]. *)
Local Lemma ee_consts :
  is_finite SH64 = true /\ is_finite SL64 = true /\
  is_finite SH4 = true /\ is_finite SL4 = true /\
  B2R SH64 = IZR 390207173010335 * bpow radix2 (-43) /\
  - B2R SH4 = IZR (-24387948313146) * bpow radix2 (-43) /\
  Rabs (B2R SL64) <= bpow radix2 (-46) /\ Rabs (- B2R SL4) <= bpow radix2 (-46) /\
  Rabs (B2R SH64) <= 45 /\ Rabs (- B2R SH4) <= 45 /\
  Rabs (B2R SH64 + B2R SL64 - IZR 64 * ln 2) <= bpow radix2 (-98) /\
  Rabs (- B2R SH4 + - B2R SL4 - IZR (-4) * ln 2) <= bpow radix2 (-98).
Proof.
lit_hyp (from_bits (fst DyadicExp.LN2_64)) Wa. lit_hyp (from_bits (snd DyadicExp.LN2_64)) Wb.
lit_hyp (from_bits (fst DyadicExp.LN2_4)) Wc. lit_hyp (from_bits (snd DyadicExp.LN2_4)) Wd.
lit_hyp (from_bits (fst DyadicExp.LN2)) We. lit_hyp (from_bits (snd DyadicExp.LN2)) Wf.
pose proof ln2_dd_correct as L. rewrite We, Wf in L. apply Rabs_le_inv in L.
rewrite Wa, Wb, Wc, Wd. cbn [bpow radix_val radix2] in L |- *.
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
split; [lra|]. split; [lra|].
repeat split; apply Rabs_le; lra.
Qed.

(** ** One shift

    [zh' = RN(zh + dh)] is exact: [zh] and [dh] are multiples of [2^-43]
    (as [|zh| >= 2^9]), and so is their sum, which is below [2^10] as
    [|zh'| <= 709]. [zl' = RN(zl + dl)] is within [2^-93] of [zl + dl],
    which is below [2^-40]. So [zh' + zl'] is [z + k ln 2] within [2^-92
    + 2^-98 + 2^-93 <= 2^-91] of [a + k ln 2], and [e^(a + k ln 2)
    2^-e0] is [A e^u] for [A = e^(zh' + zl') 2^-e0 <= 5] and [|u| <=
    2^-91], within [10 * 2^-91 <= 2^-87] of [A], which [fast_exp_correct]
    bounds. [e^a 2^-(e0 - k) = e^(a + k ln 2) 2^-e0]. *)
Local Lemma ee_shift :
  forall (fma : bool) (zh zl : f64) (a : R) (zh' zl' : f64) (dh dl : R) (n k : Z) (h l : f64)
    (e0 e : Z),
  is_finite zh = true -> is_finite zl = true ->
  bpow radix2 9 <= Rabs (B2R zh) -> Rabs (B2R zl) <= 3 * bpow radix2 (-42) ->
  Rabs (a - (B2R zh + B2R zl)) <= bpow radix2 (-92) ->
  dh = IZR n * bpow radix2 (-43) -> Rabs dl <= bpow radix2 (-46) ->
  Rabs (dh + dl - IZR k * ln 2) <= bpow radix2 (-98) -> (-4 <= k <= 64)%Z ->
  is_finite zh' = true -> B2R zh' = RN (B2R zh + dh) -> Rabs (B2R zh') <= 709 ->
  is_finite zl' = true -> B2R zl' = RN (B2R zl + dl) ->
  DyadicExp.fast_exp fma zh' zl' = Some (h, l, e0) -> e = (e0 - k)%Z ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < B2R h < 2 /\ (-1085 <= e <= 1026)%Z /\
  Rabs (exp a * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (-68) - bpow radix2 (-73).
Proof.
intros fma zh zl a zh' zl' dh dl n k h l e0 e Fzh Fzl Hzh Hzl Ha Edh Hdl Hk Hkr
  Fz' Ez' Hz' Fl' El' H Ee.
assert (HM : bpow radix2 10 = 1024 /\
             3 * bpow radix2 (-42) + bpow radix2 (-46) <= bpow radix2 (-40) /\
             bpow radix2 (-92) + bpow radix2 (-98) + bpow radix2 (-93) <= bpow radix2 (-91) /\
             bpow radix2 (-91) <= / 2 /\
             10 * bpow radix2 (-91) + (bpow radix2 (-68) - bpow radix2 (-72))
               <= bpow radix2 (-68) - bpow radix2 (-73) /\
             bpow radix2 2 = 4 /\ bpow radix2 (-68) <= 1)
  by (cbn [bpow radix_val radix2]; lra).
destruct HM as (HM1 & HM2 & HM3 & HM4 & HM5 & HM6 & HM7).
(* [zh + dh] is exact. *)
assert (Hs : Rabs (B2R zh + dh) < bpow radix2 10).
{ apply abs_lt_of_RN_lt; [lia|]. rewrite <- Ez'. lra. }
pose proof (generic_format_B2R _ _ zh) as G.
change (SpecFloat.fexp 53 1024) with fexp64 in G.
assert (Hce : (-43 <= cexp radix2 fexp64 (B2R zh))%Z).
{ change (-43)%Z with (FLT_exp (-1074) 53 10).
  apply (cexp_ge_bpow radix2 fexp64 (B2R zh) 10). exact Hzh. }
destruct (format_mult_inv _ _ G Hce) as (z & Hz).
assert (Ex : B2R zh + dh = IZR (z + n) * bpow radix2 (-43))
  by (rewrite Hz, Edh, plus_IZR; ring).
assert (Hzn : (Z.abs (z + n) < 2 ^ 53)%Z).
{ apply lt_IZR. rewrite abs_IZR.
  rewrite Ex, Rabs_mult, (Rabs_pos_eq (bpow radix2 (-43))) in Hs by apply bpow_ge_0.
  assert (B : bpow radix2 10 = IZR (2 ^ 53)%Z * bpow radix2 (-43)).
  { change (IZR (2 ^ 53)%Z) with (bpow radix2 53). rewrite <- bpow_plus. reflexivity. }
  rewrite B in Hs.
  apply Rmult_lt_reg_r with (bpow radix2 (-43)); [apply bpow_gt_0 | exact Hs]. }
assert (Ezh' : B2R zh' = B2R zh + dh).
{ rewrite Ez'. apply round_generic; [typeclasses eauto|].
  rewrite Ex. apply format_mult; [exact Hzn | lia]. }
(* [zl' = RN(zl + dl)] is below [2^-40] and within [2^-93] of [zl + dl]. *)
assert (Hzl1 : Rabs (B2R zl + dl) <= bpow radix2 (-40)).
{ pose proof Hzl as Hzl0. pose proof Hdl as Hdl0. apply Rabs_le_inv in Hzl0, Hdl0.
  apply Rabs_le. lra. }
assert (Hzl' : Rabs (B2R zl') <= bpow radix2 (-40)).
{ rewrite El'. apply abs_round_le_generic; [typeclasses eauto .. | | exact Hzl1].
  apply generic_format_FLT_bpow; [typeclasses eauto .. | lia]. }
assert (Hel : Rabs (B2R zl' - (B2R zl + dl)) <= bpow radix2 (-93))
  by (rewrite El'; apply (ee_RN_err _ (-40)); [lia | exact Hzl1]).
destruct (fast_exp_correct fma zh' zl' h l e0 Fz' Fl' Hzl' H) as (Fh & Fl & Eh & Hh & He0 & Herr).
do 4 (split; [assumption|]). split; [subst e; lia|].
subst e.
set (u := a + IZR k * ln 2 - (B2R zh' + B2R zl')).
assert (Hu : Rabs u <= bpow radix2 (-91)).
{ unfold u. rewrite Ezh'. apply Rabs_le_inv in Ha, Hk, Hel. apply Rabs_le. lra. }
pose proof (ee_exp_close u ltac:(lra)) as Hc.
assert (Hhl : Rabs (B2R h + B2R l) < bpow radix2 2)
  by (apply abs_lt_of_RN_lt; [lia | rewrite <- Eh, Rabs_pos_eq by lra; lra]).
set (A := exp (B2R zh' + B2R zl') * bpow radix2 (- e0)) in *.
assert (A0 : 0 < A) by (apply Rmult_lt_0_compat; [apply exp_pos | apply bpow_gt_0]).
apply Rabs_def2 in Hhl. destruct Hhl as [Hhl1 Hhl2].
pose proof Herr as Herr'. apply Rabs_le_inv in Herr'.
pose proof (bpow_gt_0 radix2 (-72)).
assert (A5 : A <= 5) by lra.
assert (E1 : exp a * exp (IZR k * ln 2) = exp (B2R zh' + B2R zl') * exp u).
{ rewrite <- !exp_plus. f_equal. unfold u. ring. }
assert (EA : exp a * bpow radix2 (- (e0 - k)) = A + A * (exp u - 1)).
{ replace (- (e0 - k))%Z with (k + - e0)%Z by ring.
  rewrite bpow_plus, (bpow_exp radix2 k). change (IZR (radix_val radix2)) with 2.
  transitivity (exp a * exp (IZR k * ln 2) * bpow radix2 (- e0)); [ring|].
  rewrite E1. unfold A. ring. }
assert (HA : Rabs (A * (exp u - 1)) <= 10 * bpow radix2 (-91)).
{ rewrite Rabs_mult, (Rabs_pos_eq A) by lra.
  replace (10 * bpow radix2 (-91)) with (5 * (2 * bpow radix2 (-91))) by ring.
  apply Rmult_le_compat; [lra | apply Rabs_pos | lra | lra]. }
rewrite EA. apply Rabs_le_inv in HA. apply Rabs_le. lra.
Qed.

(** Where the shift [zh + d] reaches the range of [fast_exp] and [|d| <=
    45], [|zh| <= 709 + 2^-43 + 45]. *)
Local Lemma ee_in_bound :
  forall (zh : f64) (d : R) (zh' : f64),
  Rabs (B2R zh') <= 709 -> B2R zh' = RN (B2R zh + d) -> Rabs d <= 45 ->
  Rabs (B2R zh) <= 760.
Proof.
intros zh d zh' Hz E Hd.
assert (HM : bpow radix2 10 = 1024 /\ bpow radix2 (-43) <= 1)
  by (cbn [bpow radix_val radix2]; lra).
assert (Hs : Rabs (B2R zh + d) < bpow radix2 10)
  by (apply abs_lt_of_RN_lt; [lia | rewrite <- E; lra]).
assert (He : Rabs (RN (B2R zh + d) - (B2R zh + d)) <= bpow radix2 (-43))
  by (apply (ee_RN_err _ 10); [lia | lra]).
rewrite <- E in He. apply Rabs_le_inv in Hz, He, Hd. apply Rabs_le. lra.
Qed.

(** Where [fast_exp_edge] returns, [zh] is finite and within [709] of the
    shift. *)
Lemma fast_exp_edge_in :
  forall fma zh zl r, DyadicExp.fast_exp_edge fma zh zl = Some r ->
  is_finite zh = true /\ Rabs (B2R zh) <= 760.
Proof.
intros fma zh zl r H.
destruct ee_consts as (F1 & _ & F3 & _ & _ & _ & _ & _ & B1 & B3 & _).
unfold DyadicExp.fast_exp_edge in H.
destruct (Model.lt zh Model.zero); cbv beta iota in H.
- lazymatch type of H with context [DyadicExp.fast_exp ?f ?x ?y] =>
    destruct (DyadicExp.fast_exp f x y) as [r0|] eqn:E; [|discriminate H] end.
  destruct (ee_in _ _ _ _ E) as [Fz Hz].
  assert (Fzh : is_finite zh = true).
  { clear - Fz. destruct zh as [s|[|]| |s m e B]; try reflexivity; vm_compute in Fz;
      discriminate Fz. }
  split; [exact Fzh|].
  exact (ee_in_bound zh _ _ Hz (add_B2R zh _ Fzh F1 Fz) B1).
- lazymatch type of H with context [DyadicExp.fast_exp ?f ?x ?y] =>
    destruct (DyadicExp.fast_exp f x y) as [r0|] eqn:E; [|discriminate H] end.
  destruct (ee_in _ _ _ _ E) as [Fz Hz].
  assert (Fzh : is_finite zh = true).
  { clear - Fz. destruct zh as [s|[|]| |s m e B]; try reflexivity; vm_compute in Fz;
      discriminate Fz. }
  split; [exact Fzh|].
  exact (ee_in_bound zh _ _ Hz (ee_sub_B2R zh _ Fzh F3 Fz) B3).
Qed.

Theorem fast_exp_edge_correct :
  forall fma zh zl a h l e,
  is_finite zh = true -> is_finite zl = true ->
  bpow radix2 9 <= Rabs (B2R zh) -> Rabs (B2R zl) <= 3 * bpow radix2 (-42) ->
  Rabs (a - (B2R zh + B2R zl)) <= bpow radix2 (-92) ->
  DyadicExp.fast_exp_edge fma zh zl = Some (h, l, e) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < B2R h < 2 /\ (-1085 <= e <= 1026)%Z /\
  Rabs (exp a * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (-68) - bpow radix2 (-73).
Proof.
intros fma zh zl a h l e Fzh Fzl Hzh Hzl Ha H.
destruct ee_consts as (F1 & F2 & F3 & F4 & E1 & E3 & L1 & L3 & _ & _ & K1 & K3).
assert (Hzl0 : Rabs (B2R zl) <= bpow radix2 1022).
{ eapply Rle_trans; [exact Hzl|].
  assert (bpow radix2 (-42) <= bpow radix2 1020) by (apply bpow_le; lia).
  pose proof (bpow_gt_0 radix2 (-42)).
  assert (bpow radix2 1022 = 4 * bpow radix2 1020)
    by (change 1022%Z with (2 + 1020)%Z; rewrite bpow_plus; reflexivity).
  lra. }
assert (HL : bpow radix2 (-46) <= bpow radix2 1022) by (apply bpow_le; lia).
assert (HB : bpow radix2 1022 + bpow radix2 1022 <= bpow radix2 1023 + bpow radix2 971).
{ assert (bpow radix2 1023 = 2 * bpow radix2 1022)
    by (change 1023%Z with (1 + 1022)%Z; rewrite bpow_plus; reflexivity).
  pose proof (bpow_gt_0 radix2 971). lra. }
unfold DyadicExp.fast_exp_edge in H.
destruct (Model.lt zh Model.zero); cbv beta iota in H.
- lazymatch type of H with context [DyadicExp.fast_exp ?f ?x ?y] =>
    destruct (DyadicExp.fast_exp f x y) as [[[h0 l0] e0]|] eqn:E; [|discriminate H] end.
  injection H as Eh El Ee. subst h0 l0.
  destruct (ee_in _ _ _ _ E) as [Fz Hz].
  destruct (add_no_overflow zl SL64 Fzl F2) as (Fl' & El').
  { apply Rabs_le_inv in Hzl0, L1. apply Rabs_le. lra. }
  exact (ee_shift fma zh zl a _ _ _ _ _ 64 h l e0 e Fzh Fzl Hzh Hzl Ha E1 L1 K1
           ltac:(lia) Fz (add_B2R zh _ Fzh F1 Fz) Hz Fl' El' E (eq_sym Ee)).
- lazymatch type of H with context [DyadicExp.fast_exp ?f ?x ?y] =>
    destruct (DyadicExp.fast_exp f x y) as [[[h0 l0] e0]|] eqn:E; [|discriminate H] end.
  injection H as Eh El Ee. subst h0 l0.
  destruct (ee_in _ _ _ _ E) as [Fz Hz].
  destruct (sub_no_overflow zl SL4 Fzl F4) as (Fl' & El').
  { rewrite Rabs_Ropp in L3. apply Rabs_le_inv in Hzl0, L3. apply Rabs_le. lra. }
  assert (Ee' : e = (e0 - -4)%Z) by lia.
  exact (ee_shift fma zh zl a _ _ _ _ _ (-4) h l e0 e Fzh Fzl Hzh Hzl Ha E3 L3 K3
           ltac:(lia) Fz (ee_sub_B2R zh _ Fzh F3 Fz) Hz Fl' El' E Ee').
Qed.

Theorem fast_exp_edge_fma :
  forall zh zl, DyadicExp.fast_exp_edge true zh zl = DyadicExp.fast_exp_edge false zh zl.
Proof.
intros zh zl. unfold DyadicExp.fast_exp_edge. rewrite !fast_exp_fma. reflexivity.
Qed.
