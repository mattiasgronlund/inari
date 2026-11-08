(** * sin, cos and tan in the dyadic kernel

    [sin_dir_post], [cos_dir_post] and [tan_dir_post] prove that, for a
    finite [x], the results of [sin_dir_with z], [cos_dir_with z] and
    [tan_dir_with z] of [DyadicTrig] in [Model.v] have the property
    [post] of [sin], [cos] and [tan] of [x], for any driver [z] and any
    property [post] that every correct rounding has ([rounds_post] of
    [DyDriver.v]) and that the results of [z] have ([driver_post]). They
    use the rules of [DyTrigTiny.v] for [|x| < 2^-26], those of
    [DyCosSmall.v], [DySinSmall.v] and [DyTanSmall.v] where they return,
    and otherwise the driver with the enclosures of [ev_sin_correct],
    [ev_cos_correct] and [ev_tan_correct]. Each [ev_] reduces [|x|] to
    [k π/2 ± ρ] ([reduce_correct] of [DyTrigReduce.v]), encloses [sin] or
    [cos] of [ρ] by the series ([DyTrigCore.v]), and picks the quadrant
    by [k mod 4] ([sin_quad] and [tan_quad] of [TrigSeries.v]). [ev_tan]
    encloses [cos ρ] as [√((1 - sin ρ)(1 + sin ρ))] ([cos_sqrt]) and
    returns only where the divisor of its quotient excludes 0, so the
    theorems on [tan] need no hypothesis on the domain of [tan]. So, for
    a finite [x]: with the driver [ziv_strict], the kernel rounds [sin],
    [cos] and [tan] of [x] in the direction [up] where it returns
    ([sin_dir_correct], [cos_dir_correct] and [tan_dir_correct]); the
    Rust ([sin_dir] and the others, with [Dyadic.ziv]) returns the same
    value there ([sin_dir_strict], [cos_dir_strict] and [tan_dir_strict]);
    and wherever the Rust returns, its result is at or above the exact
    value if [up] and at or below it otherwise ([sin_dir_side],
    [cos_dir_side] and [tan_dir_side]). That a rounding test passes
    by the cap is not proved. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary LogReal DyRound DyConv DyOps DyDriver DyGrow
  DyConst DyExpCore DyExpRules DyExp ExpReal DyHypRules DyLogRules DyLogCore DyLog DyLogHyp
  TrigSeries DyTrigTiny DyCosSmall DySinSmall DyTanSmall DyTrigReduce DyTrigCore MpfrRound.

Open Scope Z_scope.

(** ** Helpers *)

Lemma trg_fabs_finite : forall x : f64, is_finite x = true -> is_finite (fabs x) = true.
Proof. intros x F. unfold fabs. rewrite is_finite_Babs. exact F. Qed.

Lemma trg_fabs_R : forall x : f64, B2R (fabs x) = Rabs (B2R x).
Proof. intros x. unfold fabs. apply B2R_Babs. Qed.

Lemma trg_fabs_pos : forall x : f64, (0 <= B2R (fabs x))%R.
Proof. intros x. rewrite trg_fabs_R. apply Rabs_pos. Qed.

(** [quad] is [k mod 4], so [k] and [quad] agree mod 4. *)
Lemma trg_mod4 : forall k quad, k mod 4 = quad -> k mod 4 = quad mod 4.
Proof. intros k quad <-. rewrite Zmod_mod. reflexivity. Qed.

(** ** The [Eval]s *)

(** [sin |x|] by the reduction and [sin_k], then [sin (-t) = - sin t]. *)
Lemma ev_sin_correct :
  forall x n a,
  level_ok n -> is_finite x = true -> DyadicTrig.ev_sin x n = Some a ->
  encl_ok n a /\ encl_has a (sin (B2R x)).
Proof.
intros x n a Hn Fx H. unfold DyadicTrig.ev_sin in H.
destruct (DyadicTrig.reduce n (fabs x)) as [[[quad neg] r]|] eqn:Er; [|discriminate H].
cbv beta iota in H.
destruct (DyadicTrig.sin_k n quad neg r) as [v|] eqn:Ev; [|discriminate H].
cbv beta iota in H. injection H as <-.
destruct (reduce_correct n (fabs x) quad neg r Hn (trg_fabs_finite x Fx) (trg_fabs_pos x) Er)
  as (Or & Lr & k & rho & Hk & Hr & Hb & Ht).
destruct (sin_k_correct n quad neg r v (2 ^ 15) k rho Hn Or Lr ltac:(lia) Hr Hb
  (trg_mod4 k quad Hk) Ev) as (Ov & Lv & Hv).
rewrite <- Ht, trg_fabs_R in Hv.
apply (lh_odd n x v (2 ^ 50) sin Hn Ov Lv); [|exact Hv].
intros _. rewrite sin_neg, Ropp_involutive. reflexivity.
Qed.

(** For [t = k π/2 ± ρ], [cos t = sin (π/2 + t) = sin ((k + 1) π/2 ± ρ)],
    and [(k + 1) mod 4 = (quad + 1) mod 4]. *)
Lemma ev_cos_correct :
  forall t n a,
  level_ok n -> is_finite t = true -> (0 <= B2R t)%R -> DyadicTrig.ev_cos t n = Some a ->
  encl_ok n a /\ encl_has a (cos (B2R t)).
Proof.
intros t n a Hn Ft Pt H. unfold DyadicTrig.ev_cos in H.
destruct (DyadicTrig.reduce n t) as [[[quad neg] r]|] eqn:Er; [|discriminate H].
cbv beta iota in H.
destruct (reduce_correct n t quad neg r Hn Ft Pt Er) as (Or & Lr & k & rho & Hk & Hr & Hb & Ht).
assert (Hk1 : (k + 1) mod 4 = (quad + 1) mod 4).
{ subst quad. rewrite Z.add_mod_idemp_l by lia. reflexivity. }
destruct (sin_k_correct n (quad + 1) neg r a (2 ^ 15) (k + 1) rho Hn Or Lr ltac:(lia) Hr Hb
  Hk1 H) as (Oa & _ & Ha).
split; [exact Oa|].
replace (cos (B2R t)) with (sin (IZR (k + 1) * (PI / 2) + (if neg then - rho else rho)))%R;
  [exact Ha|].
rewrite Ht, cos_sin, plus_IZR. f_equal. ring.
Qed.

(** [tan |x|] by the reduction, as [sin ρ / cos ρ] or [cos ρ / sin ρ]
    with [cos ρ = √((1 - sin ρ)(1 + sin ρ))] and the sign of [tan_quad],
    then [tan (-t) = - tan t]. *)
Lemma ev_tan_correct :
  forall x n a,
  level_ok n -> is_finite x = true -> DyadicTrig.ev_tan x n = Some a ->
  encl_ok n a /\ encl_has a (tan (B2R x)).
Proof.
intros x n a Hn Fx H. unfold DyadicTrig.ev_tan in H.
destruct (DyadicTrig.reduce n (fabs x)) as [[[quad neg] r]|] eqn:Er; [|discriminate H].
cbv beta iota zeta in H.
destruct (Dyadic.encl_point n DyadicExp.one) as [one_e|] eqn:E1; [|discriminate H].
destruct (DyadicTrig.series n r true) as [s|] eqn:Es; [|discriminate H].
destruct (Dyadic.encl_sub n one_e s) as [ea|] eqn:Ea; [|discriminate H].
destruct (Dyadic.encl_add n one_e s) as [eb|] eqn:Eb; [|discriminate H].
destruct (Dyadic.encl_mul n ea eb) as [p|] eqn:Ep; [|discriminate H].
destruct (Dyadic.encl_sqrt n p) as [c|] eqn:Ec; [|discriminate H].
cbv beta iota zeta in H.
destruct (if (quad mod 2 =? 1) then _ else _) as [v|] eqn:Ev in H; [|discriminate H].
cbv beta iota in H. injection H as <-.
destruct (reduce_correct n (fabs x) quad neg r Hn (trg_fabs_finite x Fx) (trg_fabs_pos x) Er)
  as (Or & Lr & k & rho & Hk & Hr & Hb & Ht).
destruct (point_has n _ one_e Hn E1) as (O1 & L1 & H1).
rewrite dexp_one_R in H1.
destruct (series_correct n r true s (2 ^ 15) rho Hn Or Lr ltac:(lia) Hr Hb Es) as (Os & Ls & Hs).
cbn [trig_fn] in Hs.
pose proof (SIN_bound rho) as Sb.
(* [1 - sin ρ] and [1 + sin ρ], whose bounds of exponents are at most
   [2^50 + 2^13]. *)
destruct (sub_step n one_e s ea _ _ Hn O1 Os L1 Ls ltac:(lia) ltac:(lia) Ea) as (Oa & La & Ha).
specialize (Ha _ _ H1 Hs).
assert (La' : encl_le (2 ^ 51) ea) by (eapply encl_le_mono; [|exact La]; lia).
destruct (add_step n one_e s eb _ _ Hn O1 Os L1 Ls ltac:(lia) ltac:(lia) Eb) as (Ob & Lb & Hb').
specialize (Hb' _ _ H1 Hs).
assert (Lb' : encl_le (2 ^ 51) eb) by (eapply encl_le_mono; [|exact Lb]; lia).
destruct (mul_step n ea eb p _ _ Hn Oa Ob La' Lb' ltac:(lia) ltac:(lia) Ep) as (Op & Lp & Hp).
specialize (Hp _ _ Ha Hb').
assert (Lp' : encl_le (2 ^ 53) p) by (eapply encl_le_mono; [|exact Lp]; lia).
(* [(1 - sin ρ)(1 + sin ρ)] is not negative, so neither is the upper
   bound of [p]. *)
assert (P0 : (0 <= (1 - sin rho) * (1 + sin rho))%R) by (apply Rmult_le_pos; lra).
assert (Hh : (0 <= hi_R p)%R) by (unfold encl_has in Hp; unfold hi_R; lra).
destruct (sqrt_step n p c _ Hn Op Lp' ltac:(lia) Hh Ec) as (Oc & Lc & Hc).
specialize (Hc _ P0 Hp).
rewrite <- cos_sqrt in Hc by (apply Rabs_le; lra).
assert (Lc' : encl_le (2 ^ 54) c) by (eapply encl_le_mono; [|exact Lc]; lia).
(* [v] holds the quotient of [tan_quad]. *)
assert (Hv : encl_ok n v /\ encl_le (2 ^ 55) v /\
  encl_has v (if quad mod 2 =? 1 then (cos rho / sin rho)%R else (sin rho / cos rho)%R)).
{ destruct (quad mod 2 =? 1).
  - destruct (div_step n c s v _ _ Hn Oc Os Lc' Ls ltac:(lia) ltac:(lia) Ev) as (Ov & Lv & Hv).
    split; [exact Ov|]. split; [eapply encl_le_mono; [|exact Lv]; lia|]. exact (Hv _ _ Hc Hs).
  - destruct (div_step n s c v _ _ Hn Os Oc Ls Lc' ltac:(lia) ltac:(lia) Ev) as (Ov & Lv & Hv).
    split; [exact Ov|]. split; [eapply encl_le_mono; [|exact Lv]; lia|]. exact (Hv _ _ Hs Hc). }
clear Ev. destruct Hv as (Ov & Lv & Hv).
assert (T : tan (Rabs (B2R x)) =
  ((if xorb neg (quad mod 2 =? 1) then -1 else 1) *
   (if quad mod 2 =? 1 then cos rho / sin rho else sin rho / cos rho))%R).
{ rewrite <- trg_fabs_R, Ht. apply tan_quad. exact (trg_mod4 k quad Hk). }
revert Hv T.
generalize (if quad mod 2 =? 1 then (cos rho / sin rho)%R else (sin rho / cos rho)%R) as W.
intros W Hv T.
destruct (neg_step n v _ Hn Ov Lv) as (Onv & _ & Hnv).
specialize (Hnv _ Hv).
destruct (lt_zero_spec x) as (N1 & N2).
destruct (lt x zero) eqn:Lx.
- (* [x <= 0]: [tan x = - tan |x|]. *)
  assert (TX : tan (B2R x) = (- tan (Rabs (B2R x)))%R).
  { rewrite Rabs_left1 by (apply N1; reflexivity). rewrite tan_neg. ring. }
  rewrite TX, T.
  destruct (xorb neg (quad mod 2 =? 1)); cbn [xorb].
  + split; [exact Ov|]. replace (- (-1 * W))%R with W by ring. exact Hv.
  + split; [exact Onv|]. replace (- (1 * W))%R with (- W)%R by ring. exact Hnv.
- (* [0 <= x]: [tan x = tan |x|]. *)
  rewrite <- (Rabs_pos_eq (B2R x)) by (apply N2; reflexivity).
  rewrite T.
  destruct (xorb neg (quad mod 2 =? 1)); cbn [xorb].
  + split; [exact Onv|]. replace (-1 * W)%R with (- W)%R by ring. exact Hnv.
  + split; [exact Ov|]. replace (1 * W)%R with W by ring. exact Hv.
Qed.

(** ** The functions *)

Lemma sin_dir_post :
  forall z post, rounds_post post -> driver_post z post ->
  forall x up v,
  is_finite x = true -> DyadicTrig.sin_dir_with z x up = Some v ->
  post up (sin (B2R x)) v.
Proof.
intros z post Hp Hz x up v Fx H. unfold DyadicTrig.sin_dir_with in H.
rewrite Fx in H. cbv [negb] in H.
destruct (lt (fabs x) DyadicExp.tiny_hyp) eqn:G; cbv iota in H.
{ injection H as <-. apply Hp. exact (sin_tiny_rule x up Fx G). }
destruct (DyadicTrig.sin_small x up) as [w|] eqn:S; cbv iota in H.
{ injection H as <-. apply Hp. exact (sin_small_rule x up w Fx S). }
apply (Hz (DyadicTrig.ev_sin x) up 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_sin_correct x n a Hn Fx Ha).
Qed.

Theorem sin_dir_correct :
  forall x up v,
  is_finite x = true -> DyadicTrig.sin_dir_with ziv_strict x up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (sin (B2R x)) (with_val v).
Proof. exact (sin_dir_post ziv_strict rounds (fun _ _ _ H => H) ziv_strict_correct). Qed.

Theorem sin_dir_side :
  forall x up v,
  is_finite x = true -> DyadicTrig.sin_dir x up = Some v ->
  f64_side up (sin (B2R x)) v.
Proof. exact (sin_dir_post Dyadic.ziv f64_side rounds_side ziv_side). Qed.

Theorem sin_dir_strict :
  forall x up v,
  DyadicTrig.sin_dir_with ziv_strict x up = Some v -> DyadicTrig.sin_dir x up = Some v.
Proof.
intros x up v. unfold DyadicTrig.sin_dir, DyadicTrig.sin_dir_with.
destruct (negb (is_finite x)); [exact (fun h => h)|].
destruct (lt (fabs x) DyadicExp.tiny_hyp); [exact (fun h => h)|].
destruct (DyadicTrig.sin_small x up); [exact (fun h => h)|].
apply ziv_strict_ziv.
Qed.

(** [cos_dir] works on [t = |x|], and [cos |x| = cos x]. *)
Lemma cos_dir_post :
  forall z post, rounds_post post -> driver_post z post ->
  forall x up v,
  is_finite x = true -> DyadicTrig.cos_dir_with z x up = Some v ->
  post up (cos (B2R x)) v.
Proof.
intros z post Hp Hz x up v Fx H. unfold DyadicTrig.cos_dir_with in H. cbv zeta in H.
rewrite (trg_fabs_finite x Fx) in H. cbv [negb] in H.
destruct (lt (fabs x) DyadicExp.tiny_hyp) eqn:G; cbv iota in H.
{ injection H as <-. apply Hp. exact (cos_tiny_rule x up Fx G). }
destruct (DyadicTrig.cos_small (fabs x) up) as [w|] eqn:S; cbv iota in H.
{ injection H as <-. apply Hp. exact (cos_small_rule x up w Fx S). }
apply (Hz (DyadicTrig.ev_cos (fabs x)) up 1%nat); [|exact H].
intros n a Hn Ha.
destruct (ev_cos_correct (fabs x) n a Hn (trg_fabs_finite x Fx) (trg_fabs_pos x) Ha)
  as (Oa & Ha').
split; [exact Oa|].
rewrite trg_fabs_R in Ha'. unfold Rabs in Ha'.
destruct (Rcase_abs (B2R x)); [rewrite cos_neg in Ha'|]; exact Ha'.
Qed.

Theorem cos_dir_correct :
  forall x up v,
  is_finite x = true -> DyadicTrig.cos_dir_with ziv_strict x up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (cos (B2R x)) (with_val v).
Proof. exact (cos_dir_post ziv_strict rounds (fun _ _ _ H => H) ziv_strict_correct). Qed.

Theorem cos_dir_side :
  forall x up v,
  is_finite x = true -> DyadicTrig.cos_dir x up = Some v ->
  f64_side up (cos (B2R x)) v.
Proof. exact (cos_dir_post Dyadic.ziv f64_side rounds_side ziv_side). Qed.

Theorem cos_dir_strict :
  forall x up v,
  DyadicTrig.cos_dir_with ziv_strict x up = Some v -> DyadicTrig.cos_dir x up = Some v.
Proof.
intros x up v. unfold DyadicTrig.cos_dir, DyadicTrig.cos_dir_with. cbv zeta.
destruct (negb (is_finite (fabs x))); [exact (fun h => h)|].
destruct (lt (fabs x) DyadicExp.tiny_hyp); [exact (fun h => h)|].
destruct (DyadicTrig.cos_small (fabs x) up); [exact (fun h => h)|].
apply ziv_strict_ziv.
Qed.

Lemma tan_dir_post :
  forall z post, rounds_post post -> driver_post z post ->
  forall x up v,
  is_finite x = true -> DyadicTrig.tan_dir_with z x up = Some v ->
  post up (tan (B2R x)) v.
Proof.
intros z post Hp Hz x up v Fx H. unfold DyadicTrig.tan_dir_with in H.
rewrite Fx in H. cbv [negb] in H.
destruct (lt (fabs x) DyadicExp.tiny_hyp) eqn:G; cbv iota in H.
{ injection H as <-. apply Hp. exact (tan_tiny_rule x up Fx G). }
destruct (DyadicTrig.tan_small x up) as [w|] eqn:S; cbv iota in H.
{ injection H as <-. apply Hp. exact (tan_small_rule x up w Fx S). }
apply (Hz (DyadicTrig.ev_tan x) up 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_tan_correct x n a Hn Fx Ha).
Qed.

Theorem tan_dir_correct :
  forall x up v,
  is_finite x = true -> DyadicTrig.tan_dir_with ziv_strict x up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (tan (B2R x)) (with_val v).
Proof. exact (tan_dir_post ziv_strict rounds (fun _ _ _ H => H) ziv_strict_correct). Qed.

Theorem tan_dir_side :
  forall x up v,
  is_finite x = true -> DyadicTrig.tan_dir x up = Some v ->
  f64_side up (tan (B2R x)) v.
Proof. exact (tan_dir_post Dyadic.ziv f64_side rounds_side ziv_side). Qed.

Theorem tan_dir_strict :
  forall x up v,
  DyadicTrig.tan_dir_with ziv_strict x up = Some v -> DyadicTrig.tan_dir x up = Some v.
Proof.
intros x up v. unfold DyadicTrig.tan_dir, DyadicTrig.tan_dir_with.
destruct (negb (is_finite x)); [exact (fun h => h)|].
destruct (lt (fabs x) DyadicExp.tiny_hyp); [exact (fun h => h)|].
destruct (DyadicTrig.tan_small x up); [exact (fun h => h)|].
apply ziv_strict_ziv.
Qed.
