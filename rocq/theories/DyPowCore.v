(** * The enclosure of [x^y] in the dyadic kernel

    [ev_pow x y] of [DyadicPow] in [Model.v] encloses [x^y] of a finite
    [x > 0] and a finite [y] ([ev_pow_correct]). It writes [ln x = e ln 2
    ± a] with [e] and the enclosure [a] of [reduce] ([reduce_correct] of
    [DyLogCore.v]), takes an integer [k] near [y log2 x] from an [f64]
    estimate, and returns [2^k e^-w] for [w = (k - y e) ln 2 ∓ y a] by
    [scaled] ([scaled_gen] of [DyExp.v]), with the enclosure of ln 2 of
    [DyConst.v]. Both signs give [w = k ln 2 - y ln x], and so [2^k e^-w
    = x^y] ([pow_w_value]). [k] need not be near [y log2 x] for the
    enclosure to hold: only [|k| <= 2^14], which [to_k] checks
    ([pow_to_k_bound]), and then [k as f64] is [k] ([of_i64_exact]). *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary DyRound DyConv DyOps DyDriver DyGrow
  DyConst DyExpCore DyExpRules DyExp DyLogRules DyLogCore DyLog.

Open Scope Z_scope.

(** [k as f64] is [k] for [|k| <= 2^53]. *)
Lemma of_i64_exact :
  forall k, Z.abs k <= 2 ^ 53 ->
  is_finite (DyadicPow.of_i64 k) = true /\ B2R (DyadicPow.of_i64 k) = IZR k.
Proof.
intros k Hk.
assert (Fk : generic_format radix2 (SpecFloat.fexp 53 1024) (IZR k)).
{ change (SpecFloat.fexp 53 1024) with (FLT_exp (-1074) 53).
  destruct (Z_lt_le_dec (Z.abs k) (2 ^ 53)) as [Hlt|Hge].
  - (* Below [2^53], [k] fits the significand. *)
    apply generic_format_FLT, (FLT_spec _ _ _ _ (Float radix2 k 0)).
    + unfold F2R; cbn [Fnum Fexp bpow]. ring.
    + cbn [Fnum radix_val radix2]. exact Hlt.
    + cbn [Fexp]. lia.
  - (* [k = ±2^53] is a power of two up to its sign. *)
    assert (E : k = 2 ^ 53 \/ k = - (2 ^ 53)) by lia.
    destruct E as [-> | ->]; [| rewrite opp_IZR; apply generic_format_opp];
      rewrite (IZR_Zpower radix2) by lia;
      apply generic_format_FLT_bpow; first [typeclasses eauto | lia]. }
unfold DyadicPow.of_i64.
pose proof (binary_normalize_correct 53 1024 prec_gt_0_53 prec_lt_emax_53_1024
  mode_NE k 0 false) as H.
cbv zeta in H.
replace (F2R (Float radix2 k 0)) with (IZR k) in H by (unfold F2R; cbn [Fnum Fexp bpow]; ring).
rewrite (round_generic _ _ _ (IZR k) Fk) in H.
rewrite Rlt_bool_true in H.
2: { (* [|k| <= 2^53 < 2^1024] *)
  rewrite <- abs_IZR.
  apply Rle_lt_trans with (IZR (2 ^ 53)); [apply IZR_le; exact Hk|].
  rewrite (IZR_Zpower radix2) by lia. apply bpow_lt. lia. }
destruct H as (HR & HF & _). split; [exact HF | exact HR].
Qed.

(** [to_k] of [DyadicPow] returns only [|k| <= 2^14]. *)
Lemma pow_to_k_bound : forall c k, DyadicPow.to_k c = Some k -> - 2 ^ 14 <= k <= 2 ^ 14.
Proof.
intros c k H. unfold DyadicPow.to_k in H.
destruct (Z.abs (DyadicExp.to_i64 c) <=? 2 ^ 14) eqn:B; [|discriminate H].
injection H as <-. apply Z.leb_le in B. lia.
Qed.

(** Both values of [less] give [w = k ln 2 - y ln x], where [A] is what
    the enclosure [a] of [reduce] holds, so that [2^k e^-w = x^y]. *)
Lemma pow_w_value :
  forall (less : bool) x y e k,
  let A := if less then (IZR e * ln 2 - ln x)%R else (ln x - IZR e * ln 2)%R in
  let z := ((IZR k - y * IZR e) * ln 2)%R in
  let w := if less then (z + y * A)%R else (z - y * A)%R in
  w = (IZR k * ln 2 - y * ln x)%R /\ (bpow radix2 k * exp (- w))%R = Rpower x y.
Proof.
intros less x y e k A z w.
assert (Hw : w = (IZR k * ln 2 - y * ln x)%R) by (unfold w, z, A; destruct less; ring).
split; [exact Hw|].
rewrite Hw, bpow_exp2, <- exp_plus. unfold Rpower. f_equal. ring.
Qed.

Lemma ev_pow_correct :
  forall n x y a,
  level_ok n -> is_finite x = true -> (0 < B2R x)%R -> is_finite y = true ->
  DyadicPow.ev_pow x y n = Some a ->
  encl_ok n a /\ encl_has a (Rpower (B2R x) (B2R y)).
Proof.
intros n x y c Hn Fx Hx Fy H. unfold DyadicPow.ev_pow in H.
destruct (Dyadic.from_f64 n x) as [d|] eqn:Ed; [|discriminate H].
destruct (DyadicLog.reduce n d) as [[[e a] less]|] eqn:Er; [|discriminate H].
destruct (Dyadic.to_f64 n (Dyadic.en_hi a) true) as [ah|] eqn:Eah; [|discriminate H].
cbv zeta in H.
destruct (DyadicPow.to_k _) as [k|] eqn:Ek; [|discriminate H].
destruct (DyadicConsts.ln2 n) as [[h l]|] eqn:El; [|discriminate H].
destruct (Dyadic.encl_point n (DyadicPow.of_i64 k)) as [pk|] eqn:Epk; [|discriminate H].
destruct (Dyadic.encl_point n y) as [py|] eqn:Epy; [|discriminate H].
destruct (DyadicExp.mul_int n py e) as [ye|] eqn:Eye; [|discriminate H].
destruct (Dyadic.encl_sub n pk ye) as [z|] eqn:Ez; [|discriminate H].
destruct (Dyadic.encl_add n {| Dyadic.en_lo := h; Dyadic.en_hi := h |} l) as [hl|] eqn:Ehl;
  [|discriminate H].
destruct (Dyadic.encl_mul n z hl) as [zl|] eqn:Ezl; [|discriminate H].
destruct (DyadicExp.mul_f64 n a y) as [ya|] eqn:Eya; [|discriminate H].
destruct (if less then Dyadic.encl_add n zl ya else Dyadic.encl_sub n zl ya) as [w|] eqn:Ew;
  [|discriminate H].
cbv beta iota in H.
destruct (from_f64_small n x d Hn Ed) as (Od & Sd & Vd).
destruct (reduce_correct n d e a less Hn Od Sd Er) as (_ & He & Oa & La & Ha).
rewrite Vd in Ha.
apply pow_to_k_bound in Ek.
destruct (ln2_correct n h l Hn El) as (Hh & Heh & Hl & HEl & Hhl).
destruct (of_i64_exact k ltac:(lia)) as (_ & Vk).
destruct (point_has n _ pk Hn Epk) as (Opk & Lpk & Hpk). rewrite Vk in Hpk.
destruct (point_has n y py Hn Epy) as (Opy & Lpy & Hpy).
destruct (mul_int_step n py e ye _ Hn Opy Lpy ltac:(lia) He Eye) as (Oye & Lye & Hye).
destruct (sub_step n pk ye z _ _ Hn Opk Oye Lpk Lye ltac:(lia) ltac:(lia) Ez) as (Oz & Lz & Hz).
destruct (split_sum n h l hl (ln 2) Hn Hh Heh Hl HEl Hhl Ehl) as (Ohl & Lhl & Hhl').
destruct (mul_step n z hl zl _ _ Hn Oz Ohl Lz Lhl ltac:(lia) ltac:(lia) Ezl) as (Ozl & Lzl & Hzl).
destruct (mul_f64_step n a y ya _ Hn Oa La ltac:(lia) Eya) as (Oya & Lya & Hya).
(* [zl] holds [(k - y e) ln 2] and [ya] holds [y A]. *)
specialize (Hzl _ _ (Hz _ _ Hpk (Hye _ Hpy)) Hhl'). specialize (Hya _ Ha).
pose proof (pow_w_value less (B2R x) (B2R y) e k) as V. cbv zeta in V.
destruct V as (_ & V).
(* [w] holds [zl + ya] or [zl - ya], by [less], with exponents within
   [2^29 + 2^14 + 2^13]. *)
assert (Hw : encl_ok n w /\ encl_le (2 ^ 29 + 2 ^ 19) w /\
  encl_has w (if less then
    ((IZR k - B2R y * IZR e) * ln 2 +
     B2R y * (if less then IZR e * ln 2 - ln (B2R x) else ln (B2R x) - IZR e * ln 2))%R
  else
    ((IZR k - B2R y * IZR e) * ln 2 -
     B2R y * (if less then IZR e * ln 2 - ln (B2R x) else ln (B2R x) - IZR e * ln 2))%R)).
{ destruct less.
  - destruct (add_step n zl ya w _ _ Hn Ozl Oya Lzl Lya ltac:(lia) ltac:(lia) Ew)
      as (Ow & Lw & Hw).
    split; [exact Ow|]. split; [eapply encl_le_mono; [| exact Lw]; lia|].
    exact (Hw _ _ Hzl Hya).
  - destruct (sub_step n zl ya w _ _ Hn Ozl Oya Lzl Lya ltac:(lia) ltac:(lia) Ew)
      as (Ow & Lw & Hw).
    split; [exact Ow|]. split; [eapply encl_le_mono; [| exact Lw]; lia|].
    exact (Hw _ _ Hzl Hya). }
destruct Hw as (Ow & Lw & Hw).
destruct (scaled_gen n w k h l c _ _ Hn Ow Lw ltac:(lia) Hh ltac:(lia) Hl HEl Hhl Ek Hw H)
  as (Oc & _ & Hc).
rewrite V in Hc. split; [exact Oc | exact Hc].
Qed.
