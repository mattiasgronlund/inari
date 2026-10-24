(** * The fast path of [mul_add_ru] rounds up

    [mul_add1_ru_fast fma a b c] computes [r1 = RN(a * b + c)] and the sign
    of its error [a * b + c - r1] with ErrFma (S. Boldo and J.-M. Muller,
    Exact and approximated error of the FMA, IEEE Trans. Computers 60(2),
    2011, Algorithm 4), [BM11] below:

    - [u1 + u2 = a * b] exactly, with [u1 = RN(a * b)] ([two_prod_err]);
    - [alpha1 + alpha2 = c + u2] exactly, with [alpha1 = RN(c + u2)]
      ([two_sum_err]);
    - [beta1 + beta2 = u1 + alpha1] exactly, with [beta1 = RN(u1 + alpha1)];
    - [gamma = RN(RN(beta1 - r1) + beta2)].

    [BM11, Theorem 2] ([Pff2Flocq.ErrFMA_correct]) shows that
    [a * b + c = r1 + gamma + alpha2] if none of [a * b], [alpha1], [beta1]
    and [r1] is tiny, which is what [ok] checks with [two_prod_is_exact] and
    [not_tiny]; the bounds on [exponent(u1)] and [exponent(c)] keep every
    operation from overflowing. Then [err = RN(gamma + alpha2)] has the sign
    of [a * b + c - r1], as [gamma + alpha2] is a sum of two floats, so
    stepping [r1] up if [err > 0] rounds [a * b + c] up
    ([step_up_rounds_up_iff]). If [r1 = 0], then [a * b + c = 0], and [r1]
    is the zero that [Bfma mode_UP] returns too.

    The caller shows that [r1] is [Bfma mode_NE a b c] both with an FMA and
    without one ([mul_add1_rn_emulated]); here it is a hypothesis. *)

From Stdlib Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error.
From Flocq Require Pff.Pff2Flocq.
From Inari Require Import Model Encoding Spec Decompose TwoSum StepUp
  TwoProduct.

Open Scope R_scope.

(** If [a * b + c = 0], [Bfma] returns a zero whose sign is the same when
    rounding to nearest and toward +inf: both modes give [-0] only if
    [a * b] and [c] are both [-0] or negative. *)
Lemma Bfma_NE_UP_zero :
  forall a b c : f64,
  is_finite a = true -> is_finite b = true -> is_finite c = true ->
  B2R a * B2R b + B2R c = 0 ->
  Bfma mode_NE a b c = Bfma mode_UP a b c.
Proof.
intros a b c Fa Fb Fc H0.
pose proof (@Bfma_correct 53 1024 _ _ mode_NE a b c Fa Fb Fc) as HN.
pose proof (@Bfma_correct 53 1024 _ _ mode_UP a b c Fa Fb Fc) as HU.
cbv zeta in HN, HU.
rewrite H0, round_0, Rabs_R0, Rlt_bool_true, Rcompare_Eq in HN, HU
  by first [apply bpow_gt_0 | reflexivity | typeclasses eauto].
destruct HN as (HRN & HFN & HSN), HU as (HRU & HFU & HSU).
apply B2R_Bsign_inj; [exact HFN | exact HFU | congruence |].
rewrite HSN, HSU. unfold Bfma_szero. reflexivity.
Qed.

(** What [not_tiny x e_min] checks: [x] is zero or at least [2^e_min] in
    magnitude. *)
Lemma not_tiny_B2R :
  forall x : f64, is_finite x = true -> forall e, (-1022 <= e)%Z ->
  eq x zero || (e <=? Generic.exponent x)%Z = true ->
  B2R x = 0 \/ bpow radix2 e <= Rabs (B2R x).
Proof.
intros x Fx e He H.
apply Bool.orb_true_iff in H as [H|H].
- left. apply eq_zero_iff in H as [s ->]. reflexivity.
- right. apply Z.leb_le in H.
  apply Rle_trans with (bpow radix2 (Generic.exponent x)).
  + now apply bpow_le.
  + apply bpow_exponent_le_abs_B2R; [exact Fx | lia].
Qed.

(** If [r1] is [Bfma mode_NE a b c], [special] is false (so [a], [b] and
    [c] are finite and [a] and [b] nonzero) and [ok] holds, then
    [mul_add1_ru_fast] returns [a * b + c] rounded up, or, if
    [a * b + c = 0], the zero that [Bfma mode_UP] returns. *)
Theorem mul_add1_ru_fast_rounds_up :
  forall (fma : bool) (a b c : f64),
  (if fma then mul_add a b c
   else Generic.mul_add1_rn_emulated (mul a b)
     (Generic.two_prod_err fma a b (mul a b)) c) = Bfma mode_NE a b c ->
  negb (Generic.is_finite a && Generic.is_finite b && Generic.is_finite c)
    || eq a zero || eq b zero = false ->
  snd (Generic.mul_add1_ru_fast fma a b c) = true ->
  (B2R a * B2R b + B2R c = 0 /\
   fst (Generic.mul_add1_ru_fast fma a b c) = Bfma mode_UP a b c) \/
  (B2R a * B2R b + B2R c <> 0 /\
   rounds_up_to (B2R a * B2R b + B2R c)
     (fst (Generic.mul_add1_ru_fast fma a b c))).
Proof.
intros fma a b c Hr1 Hsp Hok.
unfold Generic.mul_add1_ru_fast in Hok |- *. cbv beta zeta in Hok |- *.
rewrite Hsp in Hok |- *. rewrite Hr1 in Hok |- *. clear Hr1.
cbn [fst snd orb] in Hok |- *.
(* [a], [b] and [c] are finite. *)
apply Bool.orb_false_elim in Hsp as [Hsp _].
apply Bool.orb_false_elim in Hsp as [Hf _].
rewrite !is_finite_eq in Hf.
apply Bool.negb_false_iff, andb_prop in Hf as [Hf Fc].
apply andb_prop in Hf as [Fa Fb].
rewrite !Bool.andb_true_iff in Hok.
destruct Hok as ((((((Hex & Hu1e) & Hce) & _) & Tr1) & Ta1) & Tb1).
apply Z.leb_le in Hu1e, Hce.
(* [u1 = RN(a * b)], [u2 = a * b - u1] and [2^-969 <= |a * b| < 2^1022]. *)
assert (He : (-968 <= Generic.exponent (mul a b) <= 1023)%Z).
{ unfold Generic.two_prod_is_exact in Hex. cbv zeta in Hex.
  destruct fma; rewrite !Bool.andb_true_iff, !Z.leb_le in Hex; lia. }
destruct (two_prod_err_correct fma a b Fa Fb Hex)
  as (Fu1 & Hu1 & _ & Fu2 & Hu2).
destruct (mul_exponent_bounds a b Fa Fb He) as (_ & _ & _ & Hab1 & Hab2).
clear He Hex.
set (u1 := mul a b) in *.
set (u2 := Generic.two_prod_err fma a b u1) in *.
set (r1 := Bfma mode_NE a b c) in *.
set (alpha1 := add c u2) in *.
set (alpha2 := Generic.two_sum_err c u2 alpha1) in *.
set (beta1 := add u1 alpha1) in *.
set (beta2 := Generic.two_sum_err u1 alpha1 beta1) in *.
set (s := sub beta1 r1) in *.
set (gamma := add s beta2) in *.
set (err := add gamma alpha2) in *.
(* No operation overflows: [|a * b|], [|c|] and [|u1|] are below [2^1022],
   and every rounding error is at most [2^971]. *)
assert (HP : 0 < bpow radix2 971 /\ 64 * bpow radix2 971 <= bpow radix2 1022 /\
  bpow radix2 1023 = 2 * bpow radix2 1022 /\
  bpow radix2 1024 = 2 * bpow radix2 1023)
  by (cbn [bpow radix_val radix2]; lra).
destruct HP as (HP0 & HP1 & HP2 & HP3).
assert (Hab : Rabs (B2R a * B2R b) < bpow radix2 1022).
{ apply Rlt_le_trans with (1 := Hab2). apply bpow_le. lia. }
assert (Hc : Rabs (B2R c) < bpow radix2 1022).
{ apply Rlt_le_trans with (1 := abs_B2R_lt_exponent c Fc).
  apply bpow_le. lia. }
assert (Hu1b : Rabs (B2R u1) < bpow radix2 1022).
{ apply Rlt_le_trans with (1 := abs_B2R_lt_exponent u1 Fu1).
  apply bpow_le. lia. }
apply Rabs_lt_inv in Hab, Hc, Hu1b.
assert (E1 : Rabs (B2R u1 - B2R a * B2R b) <= bpow radix2 971).
{ rewrite Hu1. apply RN_error. apply Rabs_le. lra. }
apply Rabs_le_inv in E1.
(* [alpha1 = RN(c + u2)] and [alpha2 = c + u2 - alpha1] *)
assert (Ha1 : is_finite alpha1 = true /\ B2R alpha1 = RN (B2R c + B2R u2)).
{ apply add_no_overflow; [exact Fc | exact Fu2 |]. apply Rabs_le. lra. }
destruct Ha1 as (Fa1 & Ha1).
assert (E2 : Rabs (B2R alpha1 - (B2R c + B2R u2)) <= bpow radix2 971).
{ rewrite Ha1. apply RN_error. apply Rabs_le. lra. }
apply Rabs_le_inv in E2.
assert (Ha2 : is_finite alpha2 = true /\
  B2R alpha2 = B2R c + B2R u2 - B2R alpha1).
{ apply two_sum_err_correct;
    [exact Fc | exact Fu2 | apply Rabs_lt; lra .. | exact Fa1]. }
destruct Ha2 as (Fa2 & Ha2).
(* [beta1 = RN(u1 + alpha1)] and [beta2 = u1 + alpha1 - beta1], where
   [u1 + alpha1] is within [2^971] of [a * b + c]. *)
assert (Hb1 : is_finite beta1 = true /\
  B2R beta1 = RN (B2R u1 + B2R alpha1)).
{ apply add_no_overflow; [exact Fu1 | exact Fa1 |]. apply Rabs_le. lra. }
destruct Hb1 as (Fb1 & Hb1).
assert (E3 : Rabs (B2R beta1 - (B2R u1 + B2R alpha1)) <= bpow radix2 971).
{ rewrite Hb1. apply RN_error. apply Rabs_le. lra. }
apply Rabs_le_inv in E3.
assert (Hb2 : is_finite beta2 = true /\
  B2R beta2 = B2R u1 + B2R alpha1 - B2R beta1).
{ apply two_sum_err_correct;
    [exact Fu1 | exact Fa1 | apply Rabs_lt; lra .. | exact Fb1]. }
destruct Hb2 as (Fb2 & Hb2).
(* [r1 = RN(a * b + c)], as [|a * b + c| < 2^1023]. *)
assert (Habc : Rabs (B2R a * B2R b + B2R c) <=
  bpow radix2 1023 + bpow radix2 971).
{ apply Rabs_le. lra. }
assert (Hr : is_finite r1 = true /\ B2R r1 = RN (B2R a * B2R b + B2R c)).
{ pose proof (@Bfma_correct 53 1024 _ _ mode_NE a b c Fa Fb Fc) as H.
  cbv zeta in H.
  change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE))
    with RN in H.
  rewrite Rlt_bool_true in H by exact (RN_no_overflow _ Habc).
  destruct H as (HR & HF & _). split; [exact HF | exact HR]. }
destruct Hr as (Fr1 & Hr1).
assert (E4 : Rabs (B2R r1 - (B2R a * B2R b + B2R c)) <= bpow radix2 971).
{ rewrite Hr1. apply RN_error. apply Rabs_le. lra. }
apply Rabs_le_inv in E4.
(* [s = RN(beta1 - r1)], where [|beta1 - r1| <= 3 * 2^971], and
   [gamma = RN(s + beta2)] and [err = RN(gamma + alpha2)] are small too. *)
assert (Hs : is_finite s = true /\ B2R s = RN (B2R beta1 - B2R r1)).
{ apply sub_no_overflow; [exact Fb1 | exact Fr1 |]. apply Rabs_le. lra. }
destruct Hs as (Fs & Hs).
assert (E5 : Rabs (B2R s - (B2R beta1 - B2R r1)) <= bpow radix2 971).
{ rewrite Hs. apply RN_error. apply Rabs_le. lra. }
apply Rabs_le_inv in E5.
assert (Hg : is_finite gamma = true /\ B2R gamma = RN (B2R s + B2R beta2)).
{ apply add_no_overflow; [exact Fs | exact Fb2 |]. apply Rabs_le. lra. }
destruct Hg as (Fg & Hg).
assert (E6 : Rabs (B2R gamma - (B2R s + B2R beta2)) <= bpow radix2 971).
{ rewrite Hg. apply RN_error. apply Rabs_le. lra. }
apply Rabs_le_inv in E6.
assert (Herr : is_finite err = true /\
  B2R err = RN (B2R gamma + B2R alpha2)).
{ apply add_no_overflow; [exact Fg | exact Fa2 |]. apply Rabs_le. lra. }
destruct Herr as (Fe & Herr).
(* ErrFma [BM11, Theorem 2]: [a * b + c = r1 + gamma + alpha2], given what
   [not_tiny] checks. Flocq states it with every float expanded into the
   rounded sums that define it; fold them back. *)
assert (U2 := not_tiny_B2R alpha1 Fa1 (-1021) ltac:(lia) Ta1).
assert (U4 := not_tiny_B2R beta1 Fb1 (-1020) ltac:(lia) Tb1).
assert (U5 := not_tiny_B2R r1 Fr1 (-1022) ltac:(lia) Tr1).
assert (Hev : Pff.Even radix2) by (exists 1%Z; reflexivity).
pose proof (Pff2Flocq.ErrFMA_correct radix2 (-1074) 53 Hev ltac:(lia)
  (fun z => negb (Z.even z)) ltac:(lia) (B2R a) (B2R b) (B2R c)
  (generic_format_B2R _ _ a) (generic_format_B2R _ _ b)
  (generic_format_B2R _ _ c) (or_intror Hab1)) as HE.
rewrite <- Hu1, <- Hu2, <- Ha1, <- Hb1, <- Hr1, <- Hs, <- Hb2, <- Hg,
  <- Ha2, <- Herr in HE.
specialize (HE U2 U4 U5).
assert (HE' : B2R a * B2R b + B2R c = B2R r1 + (B2R gamma + B2R alpha2))
  by lra.
clear HE.
(* So [err > 0] if and only if [r1 < a * b + c]: [RN] is monotone, and
   [RN(gamma + alpha2)] is not zero unless [gamma + alpha2] is
   ([round_plus_neq_0]). *)
assert (Hup : gt err zero = true <-> B2R r1 < B2R a * B2R b + B2R c).
{ unfold gt. rewrite Bltb_correct by first [exact Fe | reflexivity].
  change (B2R zero) with 0. rewrite Herr.
  destruct (Rlt_bool_spec 0 (RN (B2R gamma + B2R alpha2))) as [Hpos|Hnpos];
    split; intros H; try (reflexivity || discriminate).
  - apply Rnot_le_lt. intros Hle.
    assert (Hle' : B2R gamma + B2R alpha2 <= 0) by lra.
    apply (round_le radix2 fexp64 ZnearestE) in Hle'; [|typeclasses eauto ..].
    rewrite round_0 in Hle' by typeclasses eauto. lra.
  - assert (Hd : 0 < B2R gamma + B2R alpha2) by lra.
    assert (Hd0 : RN (B2R gamma + B2R alpha2) <> 0).
    { apply round_plus_neq_0; try typeclasses eauto;
        first [apply generic_format_B2R | intros H0; lra]. }
    apply Rlt_le, (round_le radix2 fexp64 ZnearestE) in Hd;
      [|typeclasses eauto ..].
    rewrite round_0 in Hd by typeclasses eauto. lra. }
destruct (Req_dec (B2R r1) 0) as [Hr10|Hr10].
- (* [r1 = 0]: [gamma + alpha2 = a * b + c] rounds to 0, so it is 0, and
     [err = 0]. *)
  assert (Habc0 : B2R a * B2R b + B2R c = 0).
  { destruct (Req_dec (B2R a * B2R b + B2R c) 0) as [H0|H0]; [exact H0|].
    exfalso.
    assert (Hd0 : RN (B2R gamma + B2R alpha2) <> 0).
    { apply round_plus_neq_0; try typeclasses eauto;
        first [apply generic_format_B2R | intros H1; apply H0; lra]. }
    apply Hd0. replace (B2R gamma + B2R alpha2)
      with (B2R a * B2R b + B2R c) by lra.
    rewrite <- Hr1. exact Hr10. }
  left. split; [exact Habc0|].
  assert (Hg0 : gt err zero = false).
  { apply Bool.not_true_is_false. intros Hgt. apply Hup in Hgt. lra. }
  rewrite Hg0. exact (Bfma_NE_UP_zero a b c Fa Fb Fc Habc0).
- (* [r1 <> 0], so [a * b + c <> 0]. *)
  assert (Habc0 : B2R a * B2R b + B2R c <> 0).
  { intros H0. apply Hr10. rewrite Hr1, H0. apply round_0.
    typeclasses eauto. }
  right. split; [exact Habc0|].
  apply step_up_rounds_up_iff; [exact Fr1 | exact Hr1 | exact Hr10 | exact Hup].
Qed.
