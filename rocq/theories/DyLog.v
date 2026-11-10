(** * ln, log2 and log10 in the dyadic kernel

    [ln_dir], [log2_dir] and [log10_dir] of [DyadicLog] in [Model.v]
    compute [ln], [Rlog2] and [Rlog10] of a finite [x > 0] in the
    direction [up]: by the rule for the exact powers of 10 of
    [DyLogRules.v] where it applies, and otherwise by the driver, with the
    enclosures of [ev_ln_correct] and the others. [ln_dir_post] and the
    others prove this for any driver [z] and property [post] that holds of
    every correct rounding ([rounds_post]) and that [z] gives
    ([driver_post]). So with [ziv_strict] the kernel rounds correctly where
    it returns ([ln_dir_correct] and the others, by [ziv_strict_correct]
    of [DyDriver.v]), the Rust returns the same value there
    ([ln_dir_strict] and the others), and wherever the Rust returns, its
    result is at or above the exact value if [up], and at or below it
    otherwise ([ln_dir_side] and the others, by [ziv_side]). [log2 x] is
    [e + (ln x - e ln 2) / ln 2] with [e] and the enclosure of [reduce],
    and [log10 x] is [ln x / ln 10], with the enclosures of ln 2 and ln 10
    of [DyConst.v]. That a rounding test passes by the cap is not
    proved. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary LogReal DyRound DyConv DyOps DyDriver
  DyGrow DyConst DyExpCore DyExpRules DyExp ExpReal DyLogRules DyLogCore FastLog.

Open Scope Z_scope.

(** ** Helpers *)

(** The enclosure [[h, h] + l] of ln 2 or ln 10, from the split of
    [DyConst.v]. *)
Lemma split_sum :
  forall n h l c r,
  level_ok n -> dy_ok n h -> - 2 ^ 13 <= Dyadic.dy_exp h <= 2 ^ 13 ->
  encl_ok n l -> encl_le (2 ^ 14) l -> encl_has l (r - Dyadic.dy_R h) ->
  Dyadic.encl_add n {| Dyadic.en_lo := h; Dyadic.en_hi := h |} l = Some c ->
  encl_ok n c /\ encl_le (2 ^ 15) c /\ encl_has c r.
Proof.
intros n h l c r Hn Hh Heh Hl HEl Hhl Ec.
destruct (hh_correct n h (2 ^ 13) Hh Heh) as (Ohh & Lhh & Hhh).
destruct (add_step n _ l c _ _ Hn Ohh Hl Lhh HEl ltac:(lia) ltac:(lia) Ec) as (Oc & Lc & Hc).
split; [exact Oc|].
split; [apply (encl_le_mono (Z.max (2 ^ 13) (2 ^ 14) + 2 ^ 13)); [lia | exact Lc]|].
specialize (Hc _ _ Hhh Hhl).
replace (Dyadic.dy_R h + (r - Dyadic.dy_R h))%R with r in Hc by ring. exact Hc.
Qed.

(** [from_f64] of [x] is a dyadic number of value [B2R x], with a small
    exponent. *)
Lemma from_f64_small :
  forall n x d,
  level_ok n -> Dyadic.from_f64 n x = Some d ->
  dy_ok n d /\ exp_small d /\ Dyadic.dy_R d = B2R x.
Proof.
intros n x d Hn Ed.
destruct (from_f64_step n x d Hn Ed) as (Od & He & Vd & _).
split; [exact Od|]. split; [unfold exp_small; lia | exact Vd].
Qed.

(** ** The [Eval]s *)

Lemma ev_ln_correct :
  forall x n a,
  level_ok n -> DyadicLog.ev_ln x n = Some a -> encl_ok n a /\ encl_has a (ln (B2R x)).
Proof.
intros x n a Hn H. unfold DyadicLog.ev_ln in H.
destruct (Dyadic.from_f64 n x) as [d|] eqn:Ed; [|discriminate H].
destruct (from_f64_small n x d Hn Ed) as (Od & Sd & Vd).
destruct (ln_dy_correct n d a Hn Od Sd H) as (_ & Oa & _ & Ha).
rewrite Vd in Ha. split; assumption.
Qed.

Lemma ev_log2_correct :
  forall x n a,
  level_ok n -> DyadicLog.ev_log2 x n = Some a -> encl_ok n a /\ encl_has a (Rlog2 (B2R x)).
Proof.
intros x n a Hn H. unfold DyadicLog.ev_log2 in H.
destruct (Dyadic.from_f64 n x) as [d|] eqn:Ed; [|discriminate H].
destruct (DyadicLog.reduce n d) as [[[e b] less]|] eqn:Er; [|discriminate H].
destruct (DyadicConsts.ln2 n) as [[h l]|] eqn:El; [|discriminate H].
destruct (Dyadic.encl_add n {| Dyadic.en_lo := h; Dyadic.en_hi := h |} l) as [c|] eqn:Ec;
  [|discriminate H].
destruct (Dyadic.encl_div n b c) as [r|] eqn:Erd; [|discriminate H].
destruct (Dyadic.encl_point n DyadicExp.one) as [p1|] eqn:Ep; [|discriminate H].
destruct (DyadicExp.mul_int n p1 e) as [k|] eqn:Ek; [|discriminate H].
destruct (from_f64_small n x d Hn Ed) as (Od & Sd & Vd).
destruct (reduce_correct n d e b less Hn Od Sd Er) as (Hpos & He & Ob & Lb & Hb).
destruct (ln2_correct n h l Hn El) as (Hh & Heh & Hl & HEl & Hhl).
destruct (split_sum n h l c (ln 2) Hn Hh Heh Hl HEl Hhl Ec) as (Oc & Lc & Hc).
destruct (div_step n b c r _ _ Hn Ob Oc Lb Lc ltac:(lia) ltac:(lia) Erd) as (Or & Lr & Hr).
specialize (Hr _ _ Hb Hc).
destruct (point_has n DyadicExp.one p1 Hn Ep) as (Op & Lp & Hp).
rewrite (proj2 one_B2R) in Hp.
destruct (mul_int_step n p1 e k _ Hn Op Lp ltac:(lia) He Ek) as (Ok & Lk & Hk).
specialize (Hk _ Hp).
rewrite Vd in Hr.
pose proof ln_2_pos as L2.
(* [log2 x = e + (ln x - e ln 2) / ln 2], with the sign of the second
   term outside the division. *)
destruct less.
- destruct (neg_step n r _ Hn Or Lr) as (On & Ln & Hn').
  specialize (Hn' _ Hr).
  destruct (add_step n k _ a _ _ Hn Ok On Lk Ln ltac:(lia) ltac:(lia) H) as (Oa & _ & Ha).
  split; [exact Oa|].
  replace (Rlog2 (B2R x))
    with (1 * IZR e + - ((IZR e * ln 2 - ln (B2R x)) / ln 2))%R; [exact (Ha _ _ Hk Hn')|].
  unfold Rlog2, Rlog. field. lra.
- destruct (add_step n k r a _ _ Hn Ok Or Lk Lr ltac:(lia) ltac:(lia) H) as (Oa & _ & Ha).
  split; [exact Oa|].
  replace (Rlog2 (B2R x))
    with (1 * IZR e + (ln (B2R x) - IZR e * ln 2) / ln 2)%R; [exact (Ha _ _ Hk Hr)|].
  unfold Rlog2, Rlog. field. lra.
Qed.

Lemma ev_log10_correct :
  forall x n a,
  level_ok n -> DyadicLog.ev_log10 x n = Some a -> encl_ok n a /\ encl_has a (Rlog10 (B2R x)).
Proof.
intros x n a Hn H. unfold DyadicLog.ev_log10 in H.
destruct (DyadicConsts.ln10 n) as [[h l]|] eqn:El; [|discriminate H].
destruct (Dyadic.from_f64 n x) as [d|] eqn:Ed; [|discriminate H].
destruct (DyadicLog.ln_dy n d) as [y|] eqn:Ey; [|discriminate H].
destruct (Dyadic.encl_add n {| Dyadic.en_lo := h; Dyadic.en_hi := h |} l) as [c|] eqn:Ec;
  [|discriminate H].
destruct (from_f64_small n x d Hn Ed) as (Od & Sd & Vd).
destruct (ln_dy_correct n d y Hn Od Sd Ey) as (_ & Oy & Ly & Hy).
destruct (ln10_correct n h l Hn El) as (Hh & Heh & Hl & HEl & Hhl).
destruct (split_sum n h l c (ln 10) Hn Hh Heh Hl HEl Hhl Ec) as (Oc & Lc & Hc).
destruct (div_step n y c a _ _ Hn Oy Oc Ly Lc ltac:(lia) ltac:(lia) H) as (Oa & _ & Ha).
split; [exact Oa|].
rewrite Vd in Hy. exact (Ha _ _ Hy Hc).
Qed.

(** ** The directed functions *)

Lemma ln_dir_post :
  forall z post, rounds_post post -> driver_post z post ->
  forall x up v,
  is_finite x = true -> log_dom (B2R x) -> DyadicLog.ln_dir_with z x up = Some v ->
  post up (ln (B2R x)) v.
Proof.
intros z post Hp Hz x up v Fx Dx H. unfold DyadicLog.ln_dir_with in H.
rewrite (log_rules_finite_pos x Fx Dx) in H.
destruct (DyadicLog.fast_ln_dir false x up) eqn:F; cbv iota in H.
{ injection H as <-. apply Hp. exact (fast_ln_dir_correct false x up _ Fx Dx F). }
apply (Hz (DyadicLog.ev_ln x) up 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_ln_correct x n a Hn Ha).
Qed.

Theorem ln_dir_correct :
  forall x up v,
  is_finite x = true -> log_dom (B2R x) -> DyadicLog.ln_dir_with ziv_strict x up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (ln (B2R x)) (with_val v).
Proof. exact (ln_dir_post ziv_strict rounds (fun _ _ _ H => H) ziv_strict_correct). Qed.

Theorem ln_dir_side :
  forall x up v,
  is_finite x = true -> log_dom (B2R x) -> DyadicLog.ln_dir x up = Some v ->
  f64_side up (ln (B2R x)) v.
Proof. exact (ln_dir_post Dyadic.ziv f64_side rounds_side ziv_side). Qed.

Theorem ln_dir_strict :
  forall x up v,
  DyadicLog.ln_dir_with ziv_strict x up = Some v -> DyadicLog.ln_dir x up = Some v.
Proof.
intros x up v. unfold DyadicLog.ln_dir, DyadicLog.ln_dir_with.
destruct (DyadicLog.log_rules x); [exact (fun h => h)|].
destruct (DyadicLog.fast_ln_dir false x up); [exact (fun h => h)|apply ziv_strict_ziv].
Qed.

Lemma log2_dir_post :
  forall z post, rounds_post post -> driver_post z post ->
  forall x up v,
  is_finite x = true -> log_dom (B2R x) -> DyadicLog.log2_dir_with z x up = Some v ->
  post up (Rlog2 (B2R x)) v.
Proof.
intros z post Hp Hz x up v Fx Dx H. unfold DyadicLog.log2_dir_with in H.
rewrite (log_rules_finite_pos x Fx Dx) in H.
destruct (DyadicLog.fast_log2_dir false x up) eqn:F; cbv iota in H.
{ injection H as <-. apply Hp. exact (fast_log2_dir_correct false x up _ Fx Dx F). }
apply (Hz (DyadicLog.ev_log2 x) up 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_log2_correct x n a Hn Ha).
Qed.

Theorem log2_dir_correct :
  forall x up v,
  is_finite x = true -> log_dom (B2R x) -> DyadicLog.log2_dir_with ziv_strict x up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (Rlog2 (B2R x)) (with_val v).
Proof. exact (log2_dir_post ziv_strict rounds (fun _ _ _ H => H) ziv_strict_correct). Qed.

Theorem log2_dir_side :
  forall x up v,
  is_finite x = true -> log_dom (B2R x) -> DyadicLog.log2_dir x up = Some v ->
  f64_side up (Rlog2 (B2R x)) v.
Proof. exact (log2_dir_post Dyadic.ziv f64_side rounds_side ziv_side). Qed.

Theorem log2_dir_strict :
  forall x up v,
  DyadicLog.log2_dir_with ziv_strict x up = Some v -> DyadicLog.log2_dir x up = Some v.
Proof.
intros x up v. unfold DyadicLog.log2_dir, DyadicLog.log2_dir_with.
destruct (DyadicLog.log_rules x); [exact (fun h => h)|].
destruct (DyadicLog.fast_log2_dir false x up); [exact (fun h => h)|apply ziv_strict_ziv].
Qed.

Lemma log10_dir_post :
  forall z post, rounds_post post -> driver_post z post ->
  forall x up v,
  is_finite x = true -> log_dom (B2R x) -> DyadicLog.log10_dir_with z x up = Some v ->
  post up (Rlog10 (B2R x)) v.
Proof.
intros z post Hp Hz x up v Fx Dx H. unfold DyadicLog.log10_dir_with in H.
rewrite (log_rules_finite_pos x Fx Dx) in H.
destruct (DyadicLog.fast_log10_dir false x up) eqn:F; cbv iota in H.
{ injection H as <-. apply Hp. exact (fast_log10_dir_correct false x up _ Fx Dx F). }
destruct (List.find (fun k => eq (DyadicExp.pow10 (Z.of_nat k)) x) (List.seq 0 23))
  as [k|] eqn:Ef.
- injection H as <-. apply Hp. exact (log10_pow10_rule x up k Fx Ef).
- apply (Hz (DyadicLog.ev_log10 x) up 1%nat); [|exact H].
  intros n a Hn Ha. exact (ev_log10_correct x n a Hn Ha).
Qed.

Theorem log10_dir_correct :
  forall x up v,
  is_finite x = true -> log_dom (B2R x) -> DyadicLog.log10_dir_with ziv_strict x up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (Rlog10 (B2R x)) (with_val v).
Proof. exact (log10_dir_post ziv_strict rounds (fun _ _ _ H => H) ziv_strict_correct). Qed.

Theorem log10_dir_side :
  forall x up v,
  is_finite x = true -> log_dom (B2R x) -> DyadicLog.log10_dir x up = Some v ->
  f64_side up (Rlog10 (B2R x)) v.
Proof. exact (log10_dir_post Dyadic.ziv f64_side rounds_side ziv_side). Qed.

Theorem log10_dir_strict :
  forall x up v,
  DyadicLog.log10_dir_with ziv_strict x up = Some v -> DyadicLog.log10_dir x up = Some v.
Proof.
intros x up v. unfold DyadicLog.log10_dir, DyadicLog.log10_dir_with.
destruct (DyadicLog.log_rules x); [exact (fun h => h)|].
destruct (DyadicLog.fast_log10_dir false x up); [exact (fun h => h)|].
destruct (List.find (fun k => eq (DyadicExp.pow10 (Z.of_nat k)) x) (List.seq 0 23));
  [exact (fun h => h)|apply ziv_strict_ziv].
Qed.
