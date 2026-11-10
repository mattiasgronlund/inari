(** * The argument of [fast_exp_edge] for [exp2] and [exp10]

    [DyadicExp.fast_exp_by_edge x c] passes the [zh = RN(x c_h)] and [zl]
    of [fast_exp_by] to [fast_exp_edge], where [fast_exp_by] returns
    [None], so [|zh| > 707]. The bounds of [FastExp.v]'s [fe_by_core] hold
    there up to [|zh| <= 1000], with [|zl| <= 3 * 2^-42], and
    [fast_exp_edge_correct] of [FastExpEdge.v] gives [2^x] and [10^x]
    within [2^-68 - 2^-73] ([fe_by_edge_correct]), the same with and
    without an FMA ([fe_by_edge_fma]). This file cannot import
    [FastExp.v], which imports it, so it has its own copies of the bounds
    of [fe_by_core]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Elementary TwoSum TwoProduct MulRuTiny DyDriver NearF64
  FastRound FastExpTables FastExpCore FastExpEdge.

Open Scope R_scope.

(** [B2R l] of an [f64] literal [l], as [m * 2^e] (a copy of [FastExp.v]'s). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** The range test of [fast_exp], [-707.0 <= zh && zh <= 709.0]. *)
Local Notation in_range zh :=
  (Model.le (from_bits 0xc086180000000000) zh && Model.le zh (from_bits 0x4086280000000000)).

Local Lemma fe_out : forall fma zh zl, in_range zh = false -> DyadicExp.fast_exp fma zh zl = None.
Proof. intros fma zh zl G. unfold DyadicExp.fast_exp. rewrite G. reflexivity. Qed.

(** [fast_exp] returns [None] only where its range test fails. *)
Local Lemma fe_none : forall fma zh zl, DyadicExp.fast_exp fma zh zl = None -> in_range zh = false.
Proof.
intros fma zh zl H. destruct (in_range zh) eqn:G; [exfalso | reflexivity].
unfold DyadicExp.fast_exp in H. rewrite G in H. cbv beta iota zeta delta [negb] in H.
repeat match type of H with context [match ?p with pair _ _ => _ end] => destruct p end.
discriminate H.
Qed.

(** A finite [zh] outside the range of [fast_exp] is above [707] in
    magnitude. *)
Local Lemma fe_out_R :
  forall zh, is_finite zh = true -> in_range zh = false -> 707 < Rabs (B2R zh).
Proof.
intros zh Fz G.
assert (L1 : B2R (from_bits 0xc086180000000000) = -707)
  by (lit_B2R; cbn [bpow radix_val radix2]; lra).
assert (L2 : B2R (from_bits 0x4086280000000000) = 709)
  by (lit_B2R; cbn [bpow radix_val radix2]; lra).
unfold Model.le in G.
rewrite !Bleb_correct in G by first [exact Fz | vm_compute; reflexivity].
rewrite L1, L2 in G.
destruct (Rle_bool_spec (-707) (B2R zh)) as [A|A];
  destruct (Rle_bool_spec (B2R zh) 709) as [B|B]; cbn in G; try discriminate G;
  unfold Rabs; destruct (Rcase_abs (B2R zh)); lra.
Qed.

(** Whether [fast_exp_edge] returns depends only on [zh]. *)
Local Lemma fe_edge_none :
  forall fma zh zl zl', DyadicExp.fast_exp_edge fma zh zl = None ->
  DyadicExp.fast_exp_edge fma zh zl' = None.
Proof.
intros fma zh zl zl' H. unfold DyadicExp.fast_exp_edge in *.
revert H. destruct (lt zh zero); intro H;
  match type of H with context [DyadicExp.fast_exp fma ?a ?b] =>
    destruct (DyadicExp.fast_exp fma a b) as [[[h l] e]|] eqn:E;
    [cbv beta iota in H; discriminate H|];
    rewrite (fe_out fma a _ (fe_none fma a b E)); reflexivity end.
Qed.

Local Lemma fe_finite : forall x : f64, bpow radix2 (-56) <= Rabs (B2R x) -> is_finite x = true.
Proof.
intros [s|s| |s m e B] H; try reflexivity; cbn [B2R] in H; rewrite Rabs_R0 in H;
  pose proof (bpow_gt_0 radix2 (-56)); lra.
Qed.

(** Rounding to nearest moves a real of magnitude at most [2^k] by at
    most half its ulp, [2^(k - 53)], for [k >= -1021]. *)
Local Lemma fe_RN_err :
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

(** [FastExp.v]'s [fe_by_bounds] for [|zh| <= 1000]. *)
Local Lemma fe_by_bounds_wide :
  forall x ch, is_finite x = true -> is_finite ch = true -> / 2 <= B2R ch <= 4 ->
  is_finite (mul x ch) = true -> Rabs (B2R (mul x ch)) <= 1000 ->
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

(** [FastExp.v]'s [fe_by_exact] for [|zh| <= 1000]: the product [x c_h]
    is exact by [Generic.two_prod_err], with and without an FMA. *)
Local Lemma fe_by_exact_wide :
  forall fma x ch, is_finite x = true -> is_finite ch = true -> / 2 <= B2R ch <= 4 ->
  bpow radix2 (-56) <= Rabs (B2R x) ->
  is_finite (mul x ch) = true -> Rabs (B2R (mul x ch)) <= 1000 ->
  Generic.two_prod_is_exact fma x ch (mul x ch) = true.
Proof.
intros fma x ch Fx Fc Hc Hx Fp Hp.
destruct (fe_by_bounds_wide x ch Fx Fc Hc Fp Hp) as [H10 H11].
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

(** [FastExp.v]'s [fe_by_core] for [|zh| <= 1000]: [|x c_h - zh| <=
    2^-43] and [|x c_l| <= 2^11 2^-52 = 2^-41], so with the roundings
    [|zl| <= 3 * 2^-42], and [zh + zl] is still [x k] within [2^-92]. *)
Local Lemma fe_by_core_wide :
  forall fma x ch cl k,
  is_finite x = true -> is_finite ch = true -> is_finite cl = true ->
  / 2 <= B2R ch <= 4 -> Rabs (B2R cl) <= bpow radix2 (-52) ->
  Rabs (B2R ch + B2R cl - k) <= bpow radix2 (-105) ->
  bpow radix2 (-56) <= Rabs (B2R x) ->
  is_finite (mul x ch) = true -> Rabs (B2R (mul x ch)) <= 1000 ->
  is_finite (add (Generic.two_prod_err fma x ch (mul x ch)) (mul x cl)) = true /\
  Rabs (B2R (add (Generic.two_prod_err fma x ch (mul x ch)) (mul x cl)))
    <= 3 * bpow radix2 (-42) /\
  Rabs (B2R (mul x ch) + B2R (add (Generic.two_prod_err fma x ch (mul x ch)) (mul x cl))
        - B2R x * k) <= bpow radix2 (-92).
Proof.
intros fma x ch cl k Fx Fc Fl Hc Hl Hk Hx Fp Hp.
destruct (fe_by_bounds_wide x ch Fx Fc Hc Fp Hp) as [H10 H11].
pose proof (fe_by_exact_wide fma x ch Fx Fc Hc Hx Fp Hp) as Ex.
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
             bpow radix2 (-94) + bpow radix2 (-94) + bpow radix2 (-93) = bpow radix2 (-92) /\
             bpow radix2 (-43) + bpow radix2 (-41) + bpow radix2 (-94) + bpow radix2 (-93)
               <= 3 * bpow radix2 (-42))
  by (cbn [bpow radix_val radix2]; lra).
apply Rabs_le_inv in Ht, Hxl, Hm.
assert (Htm : Rabs (B2R t + B2R m) <= bpow radix2 (-40)) by (apply Rabs_le; lra).
destruct (add_no_overflow t m Ft Fm ltac:(lra)) as (Fz & Ez).
assert (Hz : Rabs (B2R (add t m) - (B2R t + B2R m)) <= bpow radix2 (-93))
  by (rewrite Ez; apply (fe_RN_err _ (-40)); [lia | exact Htm]).
split; [exact Fz|]. split.
{ (* [|t + m| <= 2^-43 + 2^-41 + 2^-94] and its rounding adds at most
     [2^-93]. *)
  pose proof Hz as Hz'. apply Rabs_le_inv in Hz'. apply Rabs_le. lra. }
assert (Hd : Rabs (B2R x * (B2R ch + B2R cl - k)) <= bpow radix2 (-94)).
{ rewrite Rabs_mult. destruct HM as (_ & _ & <- & _).
  apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | lra | exact Hk]. }
assert (Eq : B2R x * (B2R ch + B2R cl - k) = B2R x * B2R ch + B2R x * B2R cl - B2R x * k)
  by ring.
apply Rabs_le_inv in Hz, Hd. apply Rabs_le. lra.
Qed.

(** Where [fast_exp_by_edge x c] returns after [fast_exp_by x c] did not,
    its [h + l] is [e^(x k) 2^-e] within [2^-68 - 2^-73], for [c_h + c_l]
    within [2^-105] of [k]: [fast_exp_by]'s [None] puts [|zh|] above
    [707], and [fast_exp_edge]'s [Some] below [760]. *)
Lemma fe_by_edge_correct :
  forall fma x c k h l e,
  is_finite (from_bits (fst c)) = true -> is_finite (from_bits (snd c)) = true ->
  / 2 <= B2R (from_bits (fst c)) <= 4 -> Rabs (B2R (from_bits (snd c))) <= bpow radix2 (-52) ->
  Rabs (B2R (from_bits (fst c)) + B2R (from_bits (snd c)) - k) <= bpow radix2 (-105) ->
  is_finite x = true -> bpow radix2 (-56) <= Rabs (B2R x) ->
  DyadicExp.fast_exp_by fma x c = None ->
  DyadicExp.fast_exp_by_edge fma x c = Some (h, l, e) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < B2R h < 2 /\ (-1085 <= e <= 1026)%Z /\
  Rabs (exp (B2R x * k) * bpow radix2 (- e) - (B2R h + B2R l))
    <= bpow radix2 (-68) - bpow radix2 (-73).
Proof.
intros fma x c k h l e Fc Fl Hc Hl Hk Fx Hx N H.
unfold DyadicExp.fast_exp_by in N. unfold DyadicExp.fast_exp_by_edge in H.
cbv beta iota zeta in N, H.
set (ch := from_bits (fst c)) in *. set (cl := from_bits (snd c)) in *.
destruct (FastExpEdge.fast_exp_edge_in _ _ _ _ H) as [Fp Hp].
pose proof (fe_out_R _ Fp (fe_none _ _ _ N)) as Hlo.
assert (Hp' : Rabs (B2R (mul x ch)) <= 1000) by lra.
destruct (fe_by_core_wide fma x ch cl k Fx Fc Fl Hc Hl Hk Hx Fp Hp') as (Fzl & Hzl & Hd).
assert (H9 : bpow radix2 9 <= Rabs (B2R (mul x ch))) by (cbn [bpow radix_val radix2]; lra).
apply (FastExpEdge.fast_exp_edge_correct fma _ _ (B2R x * k) h l e Fp Fzl H9 Hzl); [|exact H].
rewrite Rabs_minus_sym. exact Hd.
Qed.

(** [fast_exp_by_edge] is the same with and without an FMA: where
    [fast_exp_edge] returns, [|zh| <= 760] and the product [x c_h] is
    exact, and whether it returns depends only on [zh]. *)
Lemma fe_by_edge_fma :
  forall x c, is_finite (from_bits (fst c)) = true -> / 2 <= B2R (from_bits (fst c)) <= 4 ->
  bpow radix2 (-56) <= Rabs (B2R x) ->
  DyadicExp.fast_exp_by_edge true x c = DyadicExp.fast_exp_by_edge false x c.
Proof.
intros x c Fc Hc Hx. pose proof (fe_finite x Hx) as Fx.
unfold DyadicExp.fast_exp_by_edge. cbv beta iota zeta.
set (ch := from_bits (fst c)) in *.
rewrite FastExpEdge.fast_exp_edge_fma.
match goal with |- ?L = _ => destruct L as [r|] eqn:E end.
- destruct (FastExpEdge.fast_exp_edge_in _ _ _ _ E) as [Fp Hp].
  assert (Hp' : Rabs (B2R (mul x ch)) <= 1000) by lra.
  rewrite (two_prod_err_fma_eq x ch Fx Fc (fe_by_exact_wide true x ch Fx Fc Hc Hx Fp Hp')
    (fe_by_exact_wide false x ch Fx Fc Hc Hx Fp Hp')) in E.
  symmetry. exact E.
- symmetry. exact (fe_edge_none _ _ _ _ E).
Qed.
