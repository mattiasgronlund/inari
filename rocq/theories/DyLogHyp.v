(** * asinh, acosh and atanh in the dyadic kernel

    [asinh_dir], [acosh_dir] and [atanh_dir] of [DyadicLog] in [Model.v]
    compute [arcsinh], [Racosh] and [Ratanh] of a finite [x] in their
    domains in the direction [up], as [DyLog.v] does for [ln]: by the
    rules of [DyLogTiny.v] for tiny arguments, and otherwise by the
    driver, with the enclosures of [ev_asinh_correct] and the others.
    [asinh_dir_post] and the others prove this for any driver [z] and
    property [post] that holds of every correct rounding ([rounds_post])
    and that [z] gives ([driver_post]). So with [ziv_strict] the kernel
    rounds correctly where it returns ([asinh_dir_correct] and the others,
    by [ziv_strict_correct] of [DyDriver.v]), the Rust returns the same
    value there ([asinh_dir_strict] and the others), and wherever the Rust
    returns, its result is at or above the exact value if [up], and at or
    below it otherwise ([asinh_dir_side] and the others, by [ziv_side]).
    For [t = |x|] or [x], each is [atanh] of an argument of at most 0.1748
    by [atanh_series], or [ln] of an enclosure by [ln_encl]
    ([DyLogCore.v]), with the identities of [DyLogRules.v], and the odd
    functions from [t = |x|]. That a rounding test passes by the cap
    is not proved. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary LogReal DyRound DyConv DyOps DyDriver
  DyGrow DyExpCore DyExpRules DyExp DyHyp DyLogRules DyLogTiny DyLogCore FastAhyp.
From Inari Require DyHypRules.

Open Scope Z_scope.

(** ** Helpers *)

(** [sqrt r] lies between [r] and 1, so it keeps a window that contains
    [2^0]. *)
Lemma lh_sqrt_win :
  forall L U r, (0 <= r)%R -> grow_win L U r -> grow_win (Z.min L 0) (Z.max U 0) (sqrt r).
Proof.
intros L U r P [H | [H1 H2]].
- left. rewrite H. apply sqrt_0.
- right. rewrite Rabs_pos_eq in H1, H2 by exact P.
  pose proof (sqrt_pos r) as S0. rewrite Rabs_pos_eq by exact S0.
  pose proof (sqrt_sqrt r P) as S2.
  assert (BL : (bpow radix2 (Z.min L 0) <= bpow radix2 L)%R) by (apply bpow_le; lia).
  assert (BL0 : (bpow radix2 (Z.min L 0) <= bpow radix2 0)%R) by (apply bpow_le; lia).
  assert (BU : (bpow radix2 U <= bpow radix2 (Z.max U 0))%R) by (apply bpow_le; lia).
  assert (BU0 : (bpow radix2 0 <= bpow radix2 (Z.max U 0))%R) by (apply bpow_le; lia).
  change (bpow radix2 0) with 1%R in BL0, BU0.
  destruct (Rle_or_lt 1 r) as [R1 | R1].
  + assert (Q : (1 <= sqrt r)%R) by (rewrite <- sqrt_1; apply sqrt_le_1_alt; exact R1).
    split; nra.
  + assert (Q : (sqrt r <= 1)%R) by (rewrite <- sqrt_1; apply sqrt_le_1_alt; lra).
    split; nra.
Qed.

Lemma lh_max0_win : forall L U r, grow_win L U r -> grow_win L U (Rmax r 0).
Proof.
intros L U r H. unfold Rmax. destruct (Rle_dec r 0); [left; reflexivity | exact H].
Qed.

(** The step of [DyGrow.v] for [Encl::sqrt], from [encl_sqrt_correct]. *)
Lemma sqrt_step :
  forall n a c E,
  level_ok n -> encl_ok n a -> encl_le E a -> 0 <= E <= 2 ^ 60 -> (0 <= hi_R a)%R ->
  Dyadic.encl_sqrt n a = Some c ->
  encl_ok n c /\ encl_le (E + 2 ^ 13) c /\
  forall x, (0 <= x)%R -> encl_has a x -> encl_has c (sqrt x).
Proof.
intros n a c E Hn Ha La HE H0 H.
assert (Sa : encl_small a) by (apply (encl_le_small E); [lia | exact La]).
destruct (encl_sqrt_correct n a Hn Ha Sa H0) as (c' & E' & Okc & Vlo & Vhi & Hc).
rewrite H in E'. injection E' as <-.
split; [exact Okc |]. split; [| exact Hc].
destruct Ha as (Hla & Hha & _). destruct Okc as (Hlc & Hhc & _). destruct La as (La1 & La2).
pose proof (grow_dy_win n _ E Hn Hla La1) as Wla.
pose proof (grow_dy_win n _ E Hn Hha La2) as Wha.
pose proof (lh_sqrt_win _ _ _ (Rmax_r _ _) (lh_max0_win _ _ _ Wla)) as W1.
pose proof (lh_sqrt_win _ _ _ H0 Wha) as W2.
unfold lo_R, hi_R in Vlo, Vhi. split.
- apply (grow_exp_of_win n _ false _ _ _ _ Hn Hlc Vlo W1); lia.
- apply (grow_exp_of_win n _ true _ _ _ _ Hn Hhc Vhi W2); lia.
Qed.

(** An enclosure of [f |x|] for an odd [f], negated if [x < 0.0], holds
    [f x]. *)
Lemma lh_odd :
  forall n x r E (f : R -> R),
  level_ok n -> encl_ok n r -> encl_le E r ->
  (B2R x <= 0 -> f (B2R x) = - f (- B2R x))%R ->
  encl_has r (f (Rabs (B2R x))) ->
  encl_ok n (if lt x zero then Dyadic.encl_neg n r else r) /\
  encl_has (if lt x zero then Dyadic.encl_neg n r else r) (f (B2R x)).
Proof.
intros n x r E f Hn Or Lr Hf Hr.
destruct (lt_zero_spec x) as (N1 & N2).
destruct (lt x zero) eqn:Lx.
- destruct (neg_step n r E Hn Or Lr) as (Oa & _ & Ha).
  split; [exact Oa|].
  specialize (Ha _ Hr). rewrite Rabs_left1 in Ha by (apply N1; reflexivity).
  rewrite Hf by (apply N1; reflexivity). exact Ha.
- split; [exact Or|].
  rewrite Rabs_pos_eq in Hr by (apply N2; reflexivity). exact Hr.
Qed.

(** ** The [Eval]s *)

(** [asinh t = atanh (t / sqrt (1 + t^2))] for [t <= SERIES_MAX], and
    [asinh t = ln (t + sqrt (1 + t^2))] otherwise; then
    [asinh (-t) = - asinh t]. *)
Lemma ev_asinh_correct :
  forall x n a,
  level_ok n -> DyadicLog.ev_asinh x n = Some a ->
  encl_ok n a /\ encl_has a (arcsinh (B2R x)).
Proof.
intros x n a Hn H. unfold DyadicLog.ev_asinh in H.
destruct (Dyadic.encl_point n (fabs x)) as [t|] eqn:Et; [|discriminate H].
destruct (Dyadic.encl_point n DyadicExp.one) as [one_e|] eqn:E1; [|discriminate H].
destruct (Dyadic.encl_mul n t t) as [t2|] eqn:Et2; [|discriminate H].
destruct (Dyadic.encl_add n one_e t2) as [c2|] eqn:Ec2; [|discriminate H].
destruct (Dyadic.encl_sqrt n c2) as [c|] eqn:Ec; [|discriminate H].
cbv beta iota in H.
destruct (point_has n _ t Hn Et) as (Ot & Lt & Ht).
rewrite hyp_fabs in Ht.
destruct (point_has n _ one_e Hn E1) as (O1 & L1 & H1).
rewrite dexp_one_R in H1.
destruct (mul_step n t t t2 _ _ Hn Ot Ot Lt Lt ltac:(lia) ltac:(lia) Et2) as (Ot2 & Lt2 & Ht2).
specialize (Ht2 _ _ Ht Ht).
destruct (add_step n one_e t2 c2 _ _ Hn O1 Ot2 L1 Lt2 ltac:(lia) ltac:(lia) Ec2)
  as (Oc2 & Lc2 & Hc2).
specialize (Hc2 _ _ H1 Ht2).
(* [1 + t^2 >= 0], so the upper bound of [c2] is too. *)
assert (P2 : (0 <= 1 + Rabs (B2R x) * Rabs (B2R x))%R)
  by (pose proof (Rabs_pos (B2R x)); nra).
assert (Hh : (0 <= hi_R c2)%R)
  by (pose proof Hc2 as Q; unfold encl_has in Q; unfold hi_R; lra).
destruct (sqrt_step n c2 c _ Hn Oc2 Lc2 ltac:(lia) Hh Ec) as (Oc & Lc & Hc).
specialize (Hc _ P2 Hc2).
destruct (if le (fabs x) DyadicLog.series_max then _ else _) as [r|] eqn:Er in H;
  [|discriminate H].
cbv beta iota in H. injection H as <-.
(* [r] holds [asinh |x|]. *)
assert (Hr : encl_ok n r /\ encl_le (2 ^ 46) r /\ encl_has r (arcsinh (Rabs (B2R x)))).
{ destruct (le (fabs x) DyadicLog.series_max).
  - destruct (Dyadic.encl_div n t c) as [u|] eqn:Eu; [|discriminate Er].
    cbv beta iota in Er.
    destruct (div_step n t c u _ _ Hn Ot Oc Lt Lc ltac:(lia) ltac:(lia) Eu) as (Ou & Lu & Hu).
    specialize (Hu _ _ Ht Hc).
    destruct (atanh_series_correct n u r _ _ Hn Ou Lu ltac:(lia) Hu Er) as (Or & Lr & Hr).
    split; [exact Or|]. split; [eapply encl_le_mono; [|exact Lr]; lia|].
    rewrite (arcsinh_atanh (Rabs (B2R x))) by apply Rabs_pos. exact Hr.
  - destruct (Dyadic.encl_add n t c) as [s|] eqn:Es; [|discriminate Er].
    cbv beta iota in Er.
    destruct (add_step n t c s _ _ Hn Ot Oc Lt Lc ltac:(lia) ltac:(lia) Es) as (Os & Ls & Hs).
    specialize (Hs _ _ Ht Hc).
    destruct (ln_encl_correct n s r _ _ Hn Os Ls ltac:(lia) Hs Er) as (_ & Or & Lr & Hr).
    split; [exact Or|]. split; [exact Lr|].
    rewrite (arcsinh_ln (Rabs (B2R x))). exact Hr. }
destruct Hr as (Or & Lr & Hr).
apply (lh_odd n x r (2 ^ 46) arcsinh Hn Or Lr); [|exact Hr].
intros _. rewrite <- arcsinh_odd, Ropp_involutive. reflexivity.
Qed.

(** [acosh x = atanh (sqrt ((x - 1) (x + 1)) / x)] for
    [x <= ACOSH_SERIES_MAX], and [acosh x = ln (x + sqrt ((x - 1) (x + 1)))]
    otherwise. *)
Lemma ev_acosh_correct :
  forall x n a,
  is_finite x = true -> acosh_dom (B2R x) ->
  level_ok n -> DyadicLog.ev_acosh x n = Some a ->
  encl_ok n a /\ encl_has a (Racosh (B2R x)).
Proof.
intros x n a Fx Dx Hn H. unfold acosh_dom in Dx. unfold DyadicLog.ev_acosh in H.
destruct (Dyadic.encl_point n x) as [px|] eqn:Ep; [|discriminate H].
destruct (Dyadic.encl_point n DyadicExp.one) as [one_e|] eqn:E1; [|discriminate H].
destruct (Dyadic.encl_sub n px one_e) as [xm|] eqn:Em; [|discriminate H].
destruct (Dyadic.encl_add n px one_e) as [xp|] eqn:Ex; [|discriminate H].
destruct (Dyadic.encl_mul n xm xp) as [p|] eqn:Epp; [|discriminate H].
destruct (Dyadic.encl_sqrt n p) as [r|] eqn:Er; [|discriminate H].
cbv beta iota in H.
destruct (point_has n _ px Hn Ep) as (Op & Lp & Hp).
destruct (point_has n _ one_e Hn E1) as (O1 & L1 & H1).
rewrite dexp_one_R in H1.
destruct (sub_step n px one_e xm _ _ Hn Op O1 Lp L1 ltac:(lia) ltac:(lia) Em) as (Om & Lm & Hm).
specialize (Hm _ _ Hp H1).
destruct (add_step n px one_e xp _ _ Hn Op O1 Lp L1 ltac:(lia) ltac:(lia) Ex) as (Ox & Lx & Hx).
specialize (Hx _ _ Hp H1).
destruct (mul_step n xm xp p _ _ Hn Om Ox Lm Lx ltac:(lia) ltac:(lia) Epp)
  as (Opp & Lpp & Hpp).
specialize (Hpp _ _ Hm Hx).
(* [(x - 1) (x + 1) >= 0] for [x >= 1], so the upper bound of [p] is too. *)
assert (P : (0 <= (B2R x - 1) * (B2R x + 1))%R) by nra.
assert (Hh : (0 <= hi_R p)%R)
  by (pose proof Hpp as Q; unfold encl_has in Q; unfold hi_R; lra).
destruct (sqrt_step n p r _ Hn Opp Lpp ltac:(lia) Hh Er) as (Or & Lr & Hr).
specialize (Hr _ P Hpp).
destruct (le x DyadicLog.acosh_series_max).
- destruct (Dyadic.encl_div n r px) as [u|] eqn:Eu; [|discriminate H].
  cbv beta iota in H.
  destruct (div_step n r px u _ _ Hn Or Op Lr Lp ltac:(lia) ltac:(lia) Eu) as (Ou & Lu & Hu).
  specialize (Hu _ _ Hr Hp).
  destruct (atanh_series_correct n u a _ _ Hn Ou Lu ltac:(lia) Hu H) as (Oa & _ & Ha).
  split; [exact Oa|]. rewrite (acosh_atanh (B2R x)) by exact Dx. exact Ha.
- destruct (Dyadic.encl_add n px r) as [s|] eqn:Es; [|discriminate H].
  cbv beta iota in H.
  destruct (add_step n px r s _ _ Hn Op Or Lp Lr ltac:(lia) ltac:(lia) Es) as (Os & Ls & Hs).
  specialize (Hs _ _ Hp Hr).
  destruct (ln_encl_correct n s a _ _ Hn Os Ls ltac:(lia) Hs H) as (_ & Oa & _ & Ha).
  split; [exact Oa|]. rewrite (acosh_ln (B2R x)). exact Ha.
Qed.

(** [atanh t] by the series for [t <= SERIES_MAX], and
    [atanh t = ln ((1 + t) / (1 - t)) / 2] otherwise; then
    [atanh (-t) = - atanh t]. *)
Lemma ev_atanh_correct :
  forall x n a,
  is_finite x = true -> atanh_dom (B2R x) ->
  level_ok n -> DyadicLog.ev_atanh x n = Some a ->
  encl_ok n a /\ encl_has a (Ratanh (B2R x)).
Proof.
intros x n a Fx Dx Hn H. unfold atanh_dom in Dx. unfold DyadicLog.ev_atanh in H.
destruct (Dyadic.encl_point n (fabs x)) as [t|] eqn:Et; [|discriminate H].
cbv beta iota in H.
destruct (point_has n _ t Hn Et) as (Ot & Lt & Ht).
rewrite hyp_fabs in Ht.
destruct (if le (fabs x) DyadicLog.series_max then _ else _) as [r|] eqn:Er in H;
  [|discriminate H].
cbv beta iota in H. injection H as <-.
(* [r] holds [atanh |x|]. *)
assert (Hr : encl_ok n r /\ encl_le (2 ^ 47) r /\ encl_has r (Ratanh (Rabs (B2R x)))).
{ destruct (le (fabs x) DyadicLog.series_max).
  - destruct (atanh_series_correct n t r _ _ Hn Ot Lt ltac:(lia) Ht Er) as (Or & Lr & Hr).
    split; [exact Or|]. split; [eapply encl_le_mono; [|exact Lr]; lia|]. exact Hr.
  - destruct (Dyadic.encl_point n DyadicExp.one) as [one_e|] eqn:E1; [|discriminate Er].
    destruct (Dyadic.encl_add n one_e t) as [a'|] eqn:Ea; [|discriminate Er].
    destruct (Dyadic.encl_sub n one_e t) as [b|] eqn:Eb; [|discriminate Er].
    destruct (Dyadic.encl_div n a' b) as [q|] eqn:Eq'; [|discriminate Er].
    destruct (DyadicLog.ln_encl n q) as [l|] eqn:El; [|discriminate Er].
    cbv beta iota in Er.
    destruct (point_has n _ one_e Hn E1) as (O1 & L1 & H1).
    rewrite dexp_one_R in H1.
    destruct (add_step n one_e t a' _ _ Hn O1 Ot L1 Lt ltac:(lia) ltac:(lia) Ea)
      as (Oa & La & Ha).
    specialize (Ha _ _ H1 Ht).
    destruct (sub_step n one_e t b _ _ Hn O1 Ot L1 Lt ltac:(lia) ltac:(lia) Eb)
      as (Ob & Lb & Hb).
    specialize (Hb _ _ H1 Ht).
    destruct (div_step n a' b q _ _ Hn Oa Ob La Lb ltac:(lia) ltac:(lia) Eq')
      as (Oq & Lq & Hq).
    specialize (Hq _ _ Ha Hb).
    destruct (ln_encl_correct n q l _ _ Hn Oq Lq ltac:(lia) Hq El) as (_ & Ol & Ll & Hl).
    destruct (shl_step n l (-1) r _ Hn Ol Ll ltac:(lia) ltac:(lia) Er) as (Or & Lr & Hr).
    split; [exact Or|]. split; [eapply encl_le_mono; [|exact Lr]; lia|].
    rewrite (atanh_ln (Rabs (B2R x))). exact (Hr _ Hl). }
destruct Hr as (Or & Lr & Hr).
apply (lh_odd n x r (2 ^ 47) Ratanh Hn Or Lr); [|exact Hr].
intros _. rewrite (Ratanh_odd (B2R x)) by lra. ring.
Qed.

(** ** The directed functions *)

(** Where the rule [|x| < 2^-26] fails, [|x| >= 2^-27], as the fast paths
    of [asinh] and [atanh] take. *)
Local Lemma fast_not_tiny :
  forall x, is_finite x = true -> lt (fabs x) DyadicExp.tiny_hyp = false ->
  (bpow radix2 (-27) <= Rabs (B2R x))%R.
Proof.
intros x Fx G. unfold lt in G.
rewrite Bltb_correct in G by (first [unfold fabs; rewrite is_finite_Babs; exact Fx | reflexivity]).
rewrite hyp_fabs, DyHypRules.hyp_lit_tiny in G.
destruct (Rlt_bool_spec (Rabs (B2R x)) (bpow radix2 (-26))) as [_|L]; [discriminate G|].
apply Rle_trans with (bpow radix2 (-26)); [apply bpow_le; lia | exact L].
Qed.

Lemma asinh_dir_post :
  forall z post, rounds_post post -> driver_post z post ->
  forall x up v,
  is_finite x = true -> DyadicLog.asinh_dir_with z x up = Some v ->
  post up (arcsinh (B2R x)) v.
Proof.
intros z post Hp Hz x up v Fx H. unfold DyadicLog.asinh_dir_with in H.
rewrite (fin_not_nan x Fx), (fin_neq_inf x Fx), (fin_neq_ninf x Fx) in H. cbn [orb] in H.
destruct (lt (fabs x) DyadicExp.tiny_hyp) eqn:G; cbv iota in H.
{ injection H as <-. apply Hp. exact (asinh_tiny_rule x up Fx G). }
destruct (DyadicLog.fast_asinh_dir false x up) eqn:F; cbv iota in H.
{ injection H as <-. apply Hp.
  exact (fast_asinh_dir_correct false x up _ Fx (fast_not_tiny x Fx G) F). }
apply (Hz (DyadicLog.ev_asinh x) up 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_asinh_correct x n a Hn Ha).
Qed.

Theorem asinh_dir_correct :
  forall x up v,
  is_finite x = true -> DyadicLog.asinh_dir_with ziv_strict x up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (arcsinh (B2R x)) (with_val v).
Proof. exact (asinh_dir_post ziv_strict rounds (fun _ _ _ H => H) ziv_strict_correct). Qed.

Theorem asinh_dir_side :
  forall x up v,
  is_finite x = true -> DyadicLog.asinh_dir x up = Some v ->
  f64_side up (arcsinh (B2R x)) v.
Proof. exact (asinh_dir_post Dyadic.ziv f64_side rounds_side ziv_side). Qed.

Theorem asinh_dir_strict :
  forall x up v,
  DyadicLog.asinh_dir_with ziv_strict x up = Some v -> DyadicLog.asinh_dir x up = Some v.
Proof.
intros x up v. unfold DyadicLog.asinh_dir, DyadicLog.asinh_dir_with.
destruct (is_nan x || (eq x infinity || eq x DyadicExp.neg_infinity));
  [exact (fun h => h)|].
destruct (lt (fabs x) DyadicExp.tiny_hyp); [exact (fun h => h)|].
destruct (DyadicLog.fast_asinh_dir false x up); [exact (fun h => h)|apply ziv_strict_ziv].
Qed.

(** [x < 1.0] is false on [acosh_dom]. *)
Lemma acosh_dir_post :
  forall z post, rounds_post post -> driver_post z post ->
  forall x up v,
  is_finite x = true -> acosh_dom (B2R x) -> DyadicLog.acosh_dir_with z x up = Some v ->
  post up (Racosh (B2R x)) v.
Proof.
intros z post Hp Hz x up v Fx Dx H. unfold DyadicLog.acosh_dir_with in H.
rewrite (fin_not_nan x Fx), (fin_neq_inf x Fx) in H. cbn [orb] in H.
destruct (lt x DyadicExp.one) eqn:G; cbv iota in H.
{ exfalso. apply lt_R in G; [|exact Fx|reflexivity].
  rewrite dexp_one_R in G. unfold acosh_dom in Dx. lra. }
destruct (DyadicLog.fast_acosh_dir false x up) eqn:F; cbv iota in H.
{ injection H as <-. apply Hp. exact (fast_acosh_dir_correct false x up _ Fx Dx F). }
apply (Hz (DyadicLog.ev_acosh x) up 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_acosh_correct x n a Fx Dx Hn Ha).
Qed.

Theorem acosh_dir_correct :
  forall x up v,
  is_finite x = true -> acosh_dom (B2R x) -> DyadicLog.acosh_dir_with ziv_strict x up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (Racosh (B2R x)) (with_val v).
Proof. exact (acosh_dir_post ziv_strict rounds (fun _ _ _ H => H) ziv_strict_correct). Qed.

Theorem acosh_dir_side :
  forall x up v,
  is_finite x = true -> acosh_dom (B2R x) -> DyadicLog.acosh_dir x up = Some v ->
  f64_side up (Racosh (B2R x)) v.
Proof. exact (acosh_dir_post Dyadic.ziv f64_side rounds_side ziv_side). Qed.

Theorem acosh_dir_strict :
  forall x up v,
  DyadicLog.acosh_dir_with ziv_strict x up = Some v -> DyadicLog.acosh_dir x up = Some v.
Proof.
intros x up v. unfold DyadicLog.acosh_dir, DyadicLog.acosh_dir_with.
destruct (is_nan x || eq x infinity); [exact (fun h => h)|].
destruct (lt x DyadicExp.one); [exact (fun h => h)|].
destruct (DyadicLog.fast_acosh_dir false x up); [exact (fun h => h)|apply ziv_strict_ziv].
Qed.

(** [|x| > 1.0] and [|x| == 1.0] are false on [atanh_dom]. *)
Lemma atanh_dir_post :
  forall z post, rounds_post post -> driver_post z post ->
  forall x up v,
  is_finite x = true -> atanh_dom (B2R x) -> DyadicLog.atanh_dir_with z x up = Some v ->
  post up (Ratanh (B2R x)) v.
Proof.
intros z post Hp Hz x up v Fx Dx H. unfold DyadicLog.atanh_dir_with in H. cbv zeta in H.
assert (Ft : is_finite (fabs x) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fx).
assert (A : (Rabs (B2R x) < 1)%R) by (unfold atanh_dom in Dx; apply Rabs_def1; lra).
rewrite (fin_not_nan x Fx) in H. cbv iota in H.
destruct (gt (fabs x) DyadicExp.one) eqn:G1; cbv iota in H.
{ exfalso. assert (G1' : lt DyadicExp.one (fabs x) = true) by exact G1.
  apply lt_R in G1'; [|reflexivity|exact Ft].
  rewrite dexp_one_R, hyp_fabs in G1'. lra. }
destruct (eq (fabs x) DyadicExp.one) eqn:G2; cbv iota in H.
{ exfalso. unfold eq in G2.
  rewrite Beqb_correct in G2 by (first [exact Ft | reflexivity]).
  rewrite dexp_one_R, hyp_fabs in G2.
  destruct (Req_bool_spec (Rabs (B2R x)) 1); [lra | discriminate G2]. }
destruct (lt (fabs x) DyadicExp.tiny_hyp) eqn:G3; cbv iota in H.
{ injection H as <-. apply Hp. exact (atanh_tiny_rule x up Fx G3). }
destruct (DyadicLog.fast_atanh_dir false x up) eqn:F; cbv iota in H.
{ injection H as <-. apply Hp.
  exact (fast_atanh_dir_correct false x up _ Fx (conj (fast_not_tiny x Fx G3) A) F). }
apply (Hz (DyadicLog.ev_atanh x) up 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_atanh_correct x n a Fx Dx Hn Ha).
Qed.

Theorem atanh_dir_correct :
  forall x up v,
  is_finite x = true -> atanh_dom (B2R x) -> DyadicLog.atanh_dir_with ziv_strict x up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (Ratanh (B2R x)) (with_val v).
Proof. exact (atanh_dir_post ziv_strict rounds (fun _ _ _ H => H) ziv_strict_correct). Qed.

Theorem atanh_dir_side :
  forall x up v,
  is_finite x = true -> atanh_dom (B2R x) -> DyadicLog.atanh_dir x up = Some v ->
  f64_side up (Ratanh (B2R x)) v.
Proof. exact (atanh_dir_post Dyadic.ziv f64_side rounds_side ziv_side). Qed.

Theorem atanh_dir_strict :
  forall x up v,
  DyadicLog.atanh_dir_with ziv_strict x up = Some v -> DyadicLog.atanh_dir x up = Some v.
Proof.
intros x up v. unfold DyadicLog.atanh_dir, DyadicLog.atanh_dir_with. cbv zeta.
destruct (is_nan x); [exact (fun h => h)|].
destruct (gt (fabs x) DyadicExp.one); [exact (fun h => h)|].
destruct (eq (fabs x) DyadicExp.one); [exact (fun h => h)|].
destruct (lt (fabs x) DyadicExp.tiny_hyp); [exact (fun h => h)|].
destruct (DyadicLog.fast_atanh_dir false x up); [exact (fun h => h)|apply ziv_strict_ziv].
Qed.
