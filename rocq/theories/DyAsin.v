(** * asin and acos in the dyadic kernel

    [asin_dir] and [acos_dir] of [DyadicAtan] in [Model.v] apply the rule
    of [DyAtanTiny.v] for a tiny [x] in [asin], and otherwise the driver
    [ziv] to the enclosures of [ev_asin_correct] and [ev_acos_correct],
    from [asin_parts] of [DyAtanCore.v] at [|x|], [asin t + acos t = π/2],
    and the symmetries [asin(-t) = -asin t] and [acos(-t) = π - acos t].
    [asin_dir_post] and [acos_dir_post] prove, for any driver [z] in place
    of [ziv] ([asin_dir_with z] and [acos_dir_with z]) and any property
    [post] that holds of every correct rounding ([rounds_post]) and that
    [z] gives ([driver_post] of [DyDriver.v]), that the result has [post]
    for [asin] and [acos] of a finite [x] in [[-1, 1]] and the direction
    [up]. So with [ziv_strict] the kernel rounds correctly where it
    returns ([asin_dir_correct] and [acos_dir_correct], by
    [ziv_strict_correct]), the Rust returns the same value there
    ([asin_dir_strict] and [acos_dir_strict]), and wherever the Rust
    returns, its result is on the side of [up] ([asin_dir_side] and
    [acos_dir_side], by [ziv_side]). That a rounding test passes by
    the cap is not proved. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
(* [DyHyp] for [hyp_fabs] and [hyp_half]. *)
From Inari Require Import Model Mpfr Limbs Elementary LogReal AtanReal DyRound DyConv DyOps
  DyDriver DyGrow DyConst DyExpCore DyExpRules DyExp ExpReal DyHyp DyHypRules DyLogRules
  DyLogCore DyLog DyLogHyp AtanSeries AtanIdent DyConstPi DyAtanTiny DyAtanCore DyAtan.

Open Scope Z_scope.

(** ** Helpers *)

(** [encl_sub (encl_shl π (-1)) s], with [π] from [DyadicConsts.pi],
    holds [π/2 - v] when [s] holds [v]. *)
Lemma as_half_pi_sub :
  forall n s p h c v,
  level_ok n -> encl_ok n s -> encl_le (2 ^ 51) s -> encl_has s v ->
  DyadicConsts.pi n = Some p -> Dyadic.encl_shl n p (-1) = Some h ->
  Dyadic.encl_sub n h s = Some c ->
  encl_ok n c /\ encl_le (2 ^ 52) c /\ encl_has c (PI / 2 - v).
Proof.
intros n s p h c v Hn Os Ls Hs Ep Eh Ec.
destruct (pi_correct n p Hn Ep) as (Op & Lp & Hp).
destruct (shl_step n p (-1) h _ Hn Op Lp ltac:(lia) ltac:(lia) Eh) as (Oh & Lh & Hh).
specialize (Hh _ Hp). rewrite hyp_half in Hh.
destruct (sub_step n h s c _ _ Hn Oh Os Lh Ls ltac:(lia) ltac:(lia) Ec) as (Oc & Lc & Hc).
specialize (Hc _ _ Hh Hs).
split; [exact Oc|]. split; [eapply encl_le_mono; [|exact Lc]; lia|]. exact Hc.
Qed.

(** [|x|] of an [x] in [[-1, 1]] is a finite [f64] in [[0, 1]], as
    [asin_parts_correct] takes it. *)
Lemma as_fabs :
  forall x, is_finite x = true -> (-1 <= B2R x <= 1)%R ->
  is_finite (fabs x) = true /\ (0 <= B2R (fabs x) <= 1)%R.
Proof.
intros x Fx Dx. split.
- unfold fabs. rewrite is_finite_Babs. exact Fx.
- rewrite hyp_fabs. split; [apply Rabs_pos | apply Rabs_le; lra].
Qed.

(** ** The [Eval]s *)

(** [asin |x|] from [asin_parts], or [π/2 - acos |x|]; then
    [asin (-t) = - asin t]. *)
Lemma ev_asin_correct :
  forall x n a,
  level_ok n -> is_finite x = true -> (-1 <= B2R x <= 1)%R -> DyadicAtan.ev_asin x n = Some a ->
  encl_ok n a /\ encl_has a (asin (B2R x)).
Proof.
intros x n a Hn Fx Dx H. unfold DyadicAtan.ev_asin in H.
destruct (DyadicAtan.asin_parts n (fabs x)) as [[s below]|] eqn:Ep; [|discriminate H].
cbv beta iota in H.
destruct (as_fabs x Fx Dx) as (Ft & Dt).
destruct (asin_parts_correct n (fabs x) s below Hn Ft Dt Ep) as (Os & Ls & Hs).
rewrite hyp_fabs in Hs.
destruct (if below then _ else _) as [r|] eqn:Er in H; [|discriminate H].
cbv beta iota in H. injection H as <-.
(* [r] holds [asin |x|]. *)
assert (Hr : encl_ok n r /\ encl_le (2 ^ 52) r /\ encl_has r (asin (Rabs (B2R x)))).
{ destruct below.
  - injection Er as <-. split; [exact Os|].
    split; [eapply encl_le_mono; [|exact Ls]; lia | exact Hs].
  - destruct (DyadicConsts.pi n) as [p|] eqn:Epi; [|discriminate Er].
    cbv beta iota in Er.
    destruct (Dyadic.encl_shl n p (-1)) as [h|] eqn:Eh; [|discriminate Er].
    cbv beta iota in Er.
    destruct (as_half_pi_sub n s p h r _ Hn Os Ls Hs Epi Eh Er) as (Or & Lr & Hr).
    split; [exact Or|]. split; [exact Lr|].
    (* [π/2 - acos t = asin t] on [[-1, 1]]. *)
    assert (D : (-1 <= Rabs (B2R x) <= 1)%R) by (rewrite <- hyp_fabs; lra).
    rewrite <- (asin_plus_acos _ D) in Hr.
    replace (asin (Rabs (B2R x)) + acos (Rabs (B2R x)) - acos (Rabs (B2R x)))%R
      with (asin (Rabs (B2R x))) in Hr by ring.
    exact Hr. }
destruct Hr as (Or & Lr & Hr).
apply (lh_odd n x r (2 ^ 52) asin Hn Or Lr); [|exact Hr].
intros _. rewrite asin_opp, Ropp_involutive. reflexivity.
Qed.

(** [acos |x|] from [asin_parts], or [π/2 - asin |x|]; then
    [acos (-t) = π - acos t]. *)
Lemma ev_acos_correct :
  forall x n a,
  level_ok n -> is_finite x = true -> (-1 <= B2R x <= 1)%R -> DyadicAtan.ev_acos x n = Some a ->
  encl_ok n a /\ encl_has a (acos (B2R x)).
Proof.
intros x n a Hn Fx Dx H. unfold DyadicAtan.ev_acos in H.
destruct (DyadicAtan.asin_parts n (fabs x)) as [[s below]|] eqn:Ep; [|discriminate H].
cbv beta iota in H.
destruct (as_fabs x Fx Dx) as (Ft & Dt).
destruct (asin_parts_correct n (fabs x) s below Hn Ft Dt Ep) as (Os & Ls & Hs).
rewrite hyp_fabs in Hs.
destruct (if below then _ else _) as [r|] eqn:Er in H; [|discriminate H].
cbv beta iota in H.
(* [r] holds [acos |x|]. *)
assert (Hr : encl_ok n r /\ encl_le (2 ^ 52) r /\ encl_has r (acos (Rabs (B2R x)))).
{ destruct below.
  - destruct (DyadicConsts.pi n) as [p|] eqn:Epi; [|discriminate Er].
    cbv beta iota in Er.
    destruct (Dyadic.encl_shl n p (-1)) as [h|] eqn:Eh; [|discriminate Er].
    cbv beta iota in Er.
    destruct (as_half_pi_sub n s p h r _ Hn Os Ls Hs Epi Eh Er) as (Or & Lr & Hr).
    split; [exact Or|]. split; [exact Lr|].
    (* [π/2 - asin t = acos t] on [[-1, 1]]. *)
    assert (D : (-1 <= Rabs (B2R x) <= 1)%R) by (rewrite <- hyp_fabs; lra).
    rewrite <- (asin_plus_acos _ D) in Hr.
    replace (asin (Rabs (B2R x)) + acos (Rabs (B2R x)) - asin (Rabs (B2R x)))%R
      with (acos (Rabs (B2R x))) in Hr by ring.
    exact Hr.
  - injection Er as <-. split; [exact Os|].
    split; [eapply encl_le_mono; [|exact Ls]; lia | exact Hs]. }
destruct Hr as (Or & Lr & Hr).
destruct (lt_zero_spec x) as (N1 & N2).
destruct (lt x zero) eqn:Lx.
- (* [x <= 0]: [acos x = π - acos (-x)]. *)
  destruct (DyadicConsts.pi n) as [p|] eqn:Epi; [|discriminate H].
  cbv beta iota in H.
  destruct (pi_correct n p Hn Epi) as (Op & Lp & Hp).
  destruct (sub_step n p r a _ _ Hn Op Or Lp Lr ltac:(lia) ltac:(lia) H) as (Oa & _ & Ha).
  specialize (Ha _ _ Hp Hr).
  split; [exact Oa|].
  rewrite Rabs_left1 in Ha by (apply N1; reflexivity).
  rewrite acos_opp in Ha.
  replace (PI - (PI - acos (B2R x)))%R with (acos (B2R x)) in Ha by ring.
  exact Ha.
- injection H as <-. split; [exact Or|].
  rewrite Rabs_pos_eq in Hr by (apply N2; reflexivity). exact Hr.
Qed.

(** ** The directed functions *)

(** [|x| > 1.0] is false on [asin_dom]. *)
Lemma asin_dir_post :
  forall z post, rounds_post post -> driver_post z post ->
  forall x up v,
  is_finite x = true -> asin_dom (B2R x) -> DyadicAtan.asin_dir_with z x up = Some v ->
  post up (asin (B2R x)) v.
Proof.
intros z post Hp Hz x up v Fx Dx H.
unfold asin_dom in Dx. unfold DyadicAtan.asin_dir_with in H.
destruct (as_fabs x Fx Dx) as (Ft & Dt).
rewrite (fin_not_nan x Fx) in H. cbv iota in H.
destruct (gt (fabs x) DyadicExp.one) eqn:G1; cbv iota in H.
{ exfalso. assert (G1' : lt DyadicExp.one (fabs x) = true) by exact G1.
  apply lt_R in G1'; [|reflexivity|exact Ft].
  rewrite dexp_one_R in G1'. lra. }
destruct (lt (fabs x) DyadicAtan.tiny_asin) eqn:G2; cbv iota in H.
{ injection H as <-. apply Hp. exact (asin_tiny_rule x up Fx G2). }
apply (Hz (DyadicAtan.ev_asin x) up 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_asin_correct x n a Hn Fx Dx Ha).
Qed.

Theorem asin_dir_correct :
  forall x up v,
  is_finite x = true -> asin_dom (B2R x) -> DyadicAtan.asin_dir_with ziv_strict x up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (asin (B2R x)) (with_val v).
Proof. exact (asin_dir_post ziv_strict rounds (fun _ _ _ H => H) ziv_strict_correct). Qed.

Theorem asin_dir_side :
  forall x up v,
  is_finite x = true -> asin_dom (B2R x) -> DyadicAtan.asin_dir x up = Some v ->
  f64_side up (asin (B2R x)) v.
Proof. exact (asin_dir_post Dyadic.ziv f64_side rounds_side ziv_side). Qed.

Theorem asin_dir_strict :
  forall x up v,
  DyadicAtan.asin_dir_with ziv_strict x up = Some v -> DyadicAtan.asin_dir x up = Some v.
Proof.
intros x up v. unfold DyadicAtan.asin_dir, DyadicAtan.asin_dir_with.
destruct (is_nan x); [exact (fun h => h)|].
destruct (gt (fabs x) DyadicExp.one); [exact (fun h => h)|].
destruct (lt (fabs x) DyadicAtan.tiny_asin); [exact (fun h => h)|].
apply ziv_strict_ziv.
Qed.

(** [|x| > 1.0] is false on [acos_dom]. *)
Lemma acos_dir_post :
  forall z post, rounds_post post -> driver_post z post ->
  forall x up v,
  is_finite x = true -> acos_dom (B2R x) -> DyadicAtan.acos_dir_with z x up = Some v ->
  post up (acos (B2R x)) v.
Proof.
intros z post Hp Hz x up v Fx Dx H.
unfold acos_dom in Dx. unfold DyadicAtan.acos_dir_with in H.
destruct (as_fabs x Fx Dx) as (Ft & Dt).
rewrite (fin_not_nan x Fx) in H. cbv iota in H.
destruct (gt (fabs x) DyadicExp.one) eqn:G1; cbv iota in H.
{ exfalso. assert (G1' : lt DyadicExp.one (fabs x) = true) by exact G1.
  apply lt_R in G1'; [|reflexivity|exact Ft].
  rewrite dexp_one_R in G1'. lra. }
apply (Hz (DyadicAtan.ev_acos x) up 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_acos_correct x n a Hn Fx Dx Ha).
Qed.

Theorem acos_dir_correct :
  forall x up v,
  is_finite x = true -> acos_dom (B2R x) -> DyadicAtan.acos_dir_with ziv_strict x up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (acos (B2R x)) (with_val v).
Proof. exact (acos_dir_post ziv_strict rounds (fun _ _ _ H => H) ziv_strict_correct). Qed.

Theorem acos_dir_side :
  forall x up v,
  is_finite x = true -> acos_dom (B2R x) -> DyadicAtan.acos_dir x up = Some v ->
  f64_side up (acos (B2R x)) v.
Proof. exact (acos_dir_post Dyadic.ziv f64_side rounds_side ziv_side). Qed.

Theorem acos_dir_strict :
  forall x up v,
  DyadicAtan.acos_dir_with ziv_strict x up = Some v -> DyadicAtan.acos_dir x up = Some v.
Proof.
intros x up v. unfold DyadicAtan.acos_dir, DyadicAtan.acos_dir_with.
destruct (is_nan x); [exact (fun h => h)|].
destruct (gt (fabs x) DyadicExp.one); [exact (fun h => h)|].
apply ziv_strict_ziv.
Qed.
