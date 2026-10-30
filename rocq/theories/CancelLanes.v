(** * The float steps of [cancel_minus], one lane at a time

    - A common interval has finite lanes [-a] and [b], with [a <= b]
      ([common_lanes]).
    - A width [-a + b >= 0] rounded to nearest is either finite and the
      rounded width, or +inf, and then the width is at least
      [2^1024 - 2^970], the midpoint of [MAX] and [2^1024] ([width_lane]).
    - Halving a float of magnitude at least [2^970] is exact ([halve]).
    - Of two floats whose sum is at least 0, the larger has the larger
      magnitude ([max_min_lanes]), which is what Fast2Sum needs.
    - Fast2Sum (T. J. Dekker, A floating-point technique for extending the
      available precision, Numer. Math. 18, 1971) gives the exact error of
      a sum rounded to nearest, and none of its steps overflows
      ([fast_two_sum]). Flocq proves it without a largest exponent
      ([Pff2Flocq.Fast2Sum_correct]); binary64 has one, and what is left to
      prove is that no step overflows: [|hi - s| <= |hi|], and the error is
      at most [2^971].
    - [partial_cmp] of finite floats compares their values
      ([partial_cmp_finite]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Flocq Require Pff.Pff2Flocq.
From Inari Require Import Model Encoding Ieee1788 Integer MaxMin TwoSum.
From Inari Require Sign DecBinary Nearest TwoProduct SqrtSlow.

Open Scope R_scope.

(** The lanes of a common interval [[-a; b]] are finite, [a <= b], and the
    reals of the interval are those of [[a, b]]. *)
Lemma common_lanes :
  forall x, valid x -> Interval.is_common_interval x = true ->
  is_finite (fst (rep x)) = true /\ is_finite (snd (rep x)) = true /\
  - B2R (fst (rep x)) <= B2R (snd (rep x)) /\
  forall r, mem r x <-> - B2R (fst (rep x)) <= r <= B2R (snd (rep x)).
Proof.
intros x Hx Hc.
rewrite is_common_interval_lt, infinity_eq in Hc.
apply andb_prop in Hc. destruct Hc as [H0 H1].
(* Both lanes are below +inf, so neither is NaN or +inf. *)
assert (Hn : is_nan (fst (rep x)) = false).
{ revert H0. destruct (fst (rep x)); intros H0; first [reflexivity | discriminate H0]. }
destruct (valid_nonempty x Hx Hn) as (Ha & Hb & Hord).
assert (F0 : is_finite (fst (rep x)) = true).
{ destruct Ha as [Fa|Ea].
  - rewrite Sign.is_finite_opp in Fa. exact Fa.
  - (* [a = -inf], so the first lane is +inf. *)
    exfalso.
    assert (E0 : fst (rep x) = B754_infinity false).
    { rewrite <- (Bopp_involutive _ _ (fst (rep x))). unfold opp in Ea.
      now rewrite Ea. }
    rewrite E0 in H0. discriminate H0. }
assert (F1 : is_finite (snd (rep x)) = true).
{ destruct Hb as [Fb|Eb]; [exact Fb|]. rewrite Eb in H1. discriminate H1. }
assert (Fa : is_finite (opp (fst (rep x))) = true)
  by (rewrite Sign.is_finite_opp; exact F0).
rewrite (Sign.bound_finite _ Fa), (Sign.bound_finite _ F1) in Hord.
cbn [ordered] in Hord. rewrite Sign.B2R_opp in Hord.
split; [exact F0|]. split; [exact F1|]. split; [exact Hord|].
intros r. rewrite (mem_bounds x r Ha Hb).
rewrite (Sign.bound_finite _ Fa), (Sign.bound_finite _ F1), Sign.B2R_opp.
reflexivity.
Qed.

(** A valid interval that is neither empty nor common is unbounded. *)
Lemma not_common_unbounded :
  forall x, valid x -> Interval.is_empty x = false ->
  Interval.is_common_interval x = false -> ~ bounded (fun r => mem r x).
Proof.
intros x Hx Hn Hc Hb.
rewrite (DecBinary.bounded_common x Hx Hn Hb) in Hc. discriminate Hc.
Qed.

(** A valid empty interval has no reals, and an empty or common one is
    bounded. *)
Lemma empty_no_mem :
  forall x, valid x -> Interval.is_empty x = true -> forall r, ~ mem r x.
Proof.
intros x Hx He r.
apply mem_nan, empty_nan; [exact Hx | exact He].
Qed.

Lemma common_bounded :
  forall x, valid x -> Interval.is_common_interval x = true ->
  bounded (fun r => mem r x).
Proof.
intros x _ Hc. exact (DecBinary.common_bounded x Hc).
Qed.

(** A finite float with the sign bit set is at most 0. *)
Lemma Bsign_le_0 :
  forall u : f64, is_finite u = true -> Bsign u = true -> B2R u <= 0.
Proof.
intros [s|s| |s m e H] Fu Hs; try discriminate Fu.
- apply Rle_refl.
- cbn [Bsign] in Hs. subst s. cbn [B2R]. apply F2R_le_0. cbn. lia.
Qed.

(** [MAX] is the float below [2^1024], so [2^1024] is the float after it. *)
Lemma succ_MAX : succ radix2 fexp64 TwoProduct.MAX = bpow radix2 1024.
Proof.
assert (E : pred radix2 fexp64 (bpow radix2 1024) = TwoProduct.MAX).
{ rewrite pred_bpow. reflexivity. }
rewrite <- E. apply succ_pred; [typeclasses eauto|].
apply generic_format_bpow. cbn. lia.
Qed.

(** Rounding to nearest gives at most [MAX] below the midpoint
    [2^1024 - 2^970] of [MAX] and [2^1024]. *)
Lemma RN_le_MAX :
  forall z, z < bpow radix2 1024 - bpow radix2 970 -> RN z <= TwoProduct.MAX.
Proof.
intros z Hz.
apply round_N_le_midp; [typeclasses eauto | exact TwoProduct.format_MAX|].
rewrite succ_MAX.
assert (HM : bpow radix2 971 = 2 * bpow radix2 970).
{ change 2 with (bpow radix2 1). rewrite <- bpow_plus. reflexivity. }
lra.
Qed.

(** The width [u + v >= 0] of finite lanes, rounded to nearest. *)
Lemma width_lane :
  forall u v : f64, is_finite u = true -> is_finite v = true ->
  0 <= B2R u + B2R v ->
  (is_finite (add u v) = true /\ B2R (add u v) = RN (B2R u + B2R v)) \/
  (add u v = B754_infinity false /\
   bpow radix2 1024 - bpow radix2 970 <= B2R u + B2R v).
Proof.
intros u v Fu Fv Hp.
generalize (@Bplus_correct 53 1024 _ _ mode_NE u v Fu Fv).
change (SpecFloat.fexp 53 1024) with fexp64.
case Rlt_bool_spec; intros Hlt.
- intros (HR & HF & _). left. split; [exact HF | exact HR].
- intros (HO & Hs). right.
  (* An overflow means [|RN(u + v)| >= 2^1024 > MAX], which needs
     [u + v] at least at the midpoint of [MAX] and [2^1024]. *)
  assert (Hw : bpow radix2 1024 - bpow radix2 970 <= B2R u + B2R v).
  { destruct (Rlt_or_le (B2R u + B2R v) (bpow radix2 1024 - bpow radix2 970))
      as [Hl|Hl]; [|exact Hl].
    exfalso.
    assert (H0 : 0 <= RN (B2R u + B2R v)).
    { apply round_ge_generic; [typeclasses eauto .. | apply generic_format_0 | exact Hp]. }
    assert (H1 := RN_le_MAX _ Hl).
    change (round radix2 fexp64 (round_mode mode_NE)) with
      (round radix2 fexp64 ZnearestE) in Hlt.
    rewrite Rabs_pos_eq in Hlt by exact H0.
    pose proof (bpow_gt_0 radix2 971). lra. }
  split; [|exact Hw].
  (* The sum is positive, so [u] and [v], which have the same sign, are not
     both negative, and the infinity is +inf. *)
  assert (Su : Bsign u = false).
  { destruct (Bsign u) eqn:E; [|reflexivity]. exfalso.
    assert (Hu := Bsign_le_0 u Fu E).
    assert (Hv := Bsign_le_0 v Fv (eq_sym Hs)).
    assert (Hpos : 0 < bpow radix2 1024 - bpow radix2 970).
    { cbn [bpow radix_val radix2]. lra. }
    lra. }
  rewrite Su in HO. unfold add. apply B2SF_inj. rewrite HO. reflexivity.
Qed.

(** [0.5 * u] for a float of magnitude at least [2^970]. *)
Lemma halve :
  forall u : f64, is_finite u = true -> bpow radix2 970 <= Rabs (B2R u) ->
  is_finite (mul half u) = true /\ B2R (mul half u) = B2R u / 2.
Proof.
intros u Fu Hu.
destruct Nearest.half_B2R as (Fh & Hh).
assert (E : B2R half * B2R u = B2R u * bpow radix2 (-1)).
{ rewrite Hh. change (bpow radix2 (-1)) with (/ 2). ring. }
(* [u] is normal, and so is [u / 2], which is therefore a float. *)
assert (HN : bpow radix2 (-1022) <= bpow radix2 969).
{ apply bpow_le. lia. }
assert (H969 : bpow radix2 970 = 2 * bpow radix2 969).
{ change 2 with (bpow radix2 1). rewrite <- bpow_plus. reflexivity. }
pose proof (bpow_gt_0 radix2 969) as P969.
assert (Hf : generic_format radix2 fexp64 (B2R half * B2R u)).
{ rewrite E. apply SqrtSlow.format_scale.
  - apply generic_format_B2R.
  - lra.
  - rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0.
    change (bpow radix2 (-1)) with (/ 2). lra. }
assert (Hlt : Rabs (B2R half * B2R u) < bpow radix2 1024).
{ rewrite Rabs_mult, Hh, (Rabs_pos_eq (/ 2)) by lra.
  assert (H := abs_B2R_lt_emax _ _ u).
  pose proof (bpow_gt_0 radix2 1024). lra. }
destruct (SqrtSlow.mul_exact half u Fh Fu Hf Hlt) as (HF & HR & _).
split; [exact HF|]. rewrite HR, Hh. field.
Qed.

(** [max1] and [min1] of two finite floats whose sum is at least 0. *)
Lemma max_min_lanes :
  forall p q : f64, is_finite p = true -> is_finite q = true ->
  0 <= B2R p + B2R q ->
  is_finite (Generic.max1 p q) = true /\ is_finite (Generic.min1 p q) = true /\
  Rabs (B2R (Generic.min1 p q)) <= Rabs (B2R (Generic.max1 p q)) /\
  B2R (Generic.max1 p q) + B2R (Generic.min1 p q) = B2R p + B2R q.
Proof.
intros p q Fp Fq Hpq.
destruct (max1_finite p q Fp Fq) as (FM & HM).
destruct (min1_finite p q Fp Fq) as (Fm & Hm).
split; [exact FM|]. split; [exact Fm|]. rewrite HM, Hm.
(* The larger is at least 0, and at least minus the smaller. *)
unfold Rmax, Rmin. destruct (Rle_dec (B2R p) (B2R q)).
- split; [|ring]. unfold Rabs.
  destruct (Rcase_abs (B2R p)), (Rcase_abs (B2R q)); lra.
- split; [|ring]. unfold Rabs.
  destruct (Rcase_abs (B2R p)), (Rcase_abs (B2R q)); lra.
Qed.

(** Fast2Sum: for [|lo| <= |hi|] and a finite [s = RN(hi + lo)],
    [lo + (hi - s)], each step rounded to nearest, is finite and the exact
    error [hi + lo - s]. *)
Lemma fast_two_sum :
  forall hi lo s : f64, is_finite hi = true -> is_finite lo = true ->
  Rabs (B2R lo) <= Rabs (B2R hi) ->
  is_finite s = true -> B2R s = RN (B2R hi + B2R lo) ->
  is_finite (add lo (sub hi s)) = true /\
  B2R (add lo (sub hi s)) = B2R hi + B2R lo - B2R s.
Proof.
intros hi lo s Fhi Flo Hle Fs Hs.
(* [hi + lo] lies between 0 and [2 hi], and so does [s], as rounding is
   monotone and [0] and [2 hi] are floats. So [|hi - s| <= |hi|]. *)
assert (F2 : generic_format radix2 fexp64 (2 * B2R hi)).
{ replace (2 * B2R hi) with (B2R hi * bpow radix2 1)
    by (change (bpow radix2 1) with 2; ring).
  apply SqrtSlow.format_scale_up; [apply generic_format_B2R | lia]. }
assert (Hd : Rabs (B2R hi - B2R s) <= Rabs (B2R hi)).
{ rewrite Hs.
  destruct (Rle_or_lt 0 (B2R hi)) as [Hp|Hn].
  - rewrite (Rabs_pos_eq (B2R hi)) in Hle |- * by exact Hp.
    apply Rabs_le_inv in Hle.
    assert (L : 0 <= RN (B2R hi + B2R lo)).
    { apply round_ge_generic; [typeclasses eauto .. | apply generic_format_0 | lra]. }
    assert (U : RN (B2R hi + B2R lo) <= 2 * B2R hi).
    { apply round_le_generic; [typeclasses eauto .. | exact F2 | lra]. }
    apply Rabs_le. lra.
  - rewrite (Rabs_left (B2R hi)) in Hle |- * by exact Hn.
    apply Rabs_le_inv in Hle.
    assert (L : 2 * B2R hi <= RN (B2R hi + B2R lo)).
    { apply round_ge_generic; [typeclasses eauto .. | exact F2 | lra]. }
    assert (U : RN (B2R hi + B2R lo) <= 0).
    { apply round_le_generic; [typeclasses eauto .. | apply generic_format_0 | lra]. }
    apply Rabs_le. lra. }
(* So [hi - s] rounds to at most [|hi|], a float below [2^1024]. *)
assert (Ht : Rabs (RN (B2R hi - B2R s)) < bpow radix2 1024).
{ apply Rle_lt_trans with (Rabs (B2R hi)); [|apply abs_B2R_lt_emax].
  apply abs_round_le_generic;
    [typeclasses eauto .. | apply generic_format_abs, generic_format_B2R | exact Hd]. }
generalize (@Bminus_correct 53 1024 _ _ mode_NE hi s Fhi Fs).
rewrite Rlt_bool_true by exact Ht.
intros (HT & FT & _).
change (Bminus mode_NE hi s) with (sub hi s) in HT, FT.
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE)) with
  (round radix2 fexp64 ZnearestE) in HT.
(* Flocq's Fast2Sum, with its [x] our [hi] and its [y] our [lo]. Ties to
   even is symmetric, [RN(-z) = -RN(z)], as it requires. *)
assert (Hchoice : forall z, negb (Z.even z) = negb (negb (Z.even (- (z + 1))))).
{ intros z. rewrite Z.even_opp, Z.even_add. destruct (Z.even z); reflexivity. }
pose proof (Pff2Flocq.Fast2Sum_correct (-1074) 53 (fun z => negb (Z.even z))
  ltac:(lia) ltac:(lia) Hchoice (B2R hi) (B2R lo)
  (generic_format_B2R _ _ hi) (generic_format_B2R _ _ lo) Hle) as T.
rewrite <- Hs, <- HT in T.
assert (Hb : RN (B2R lo + B2R (sub hi s)) = B2R hi + B2R lo - B2R s) by lra.
(* The error [hi + lo - s] is at most [2^971]: [|hi + lo| <= 2^1024],
   as otherwise [s] would round to at least [2^1024] in magnitude. *)
assert (Hz : Rabs (B2R hi + B2R lo) <= bpow radix2 1024).
{ assert (Hsl := abs_B2R_lt_emax _ _ s).
  assert (Fb : generic_format radix2 fexp64 (bpow radix2 1024))
    by (apply generic_format_bpow; cbn; lia).
  apply Rabs_le.
  destruct (Rle_or_lt (- bpow radix2 1024) (B2R hi + B2R lo)) as [H1|H1];
    [split; [exact H1|]|].
  - destruct (Rle_or_lt (B2R hi + B2R lo) (bpow radix2 1024)) as [H2|H2];
      [exact H2|].
    exfalso.
    assert (G : bpow radix2 1024 <= RN (B2R hi + B2R lo)).
    { apply round_ge_generic; [typeclasses eauto .. | exact Fb | lra]. }
    rewrite <- Hs in G. apply Rabs_lt_inv in Hsl. lra.
  - exfalso.
    assert (G : RN (B2R hi + B2R lo) <= - bpow radix2 1024).
    { apply round_le_generic;
        [typeclasses eauto .. | apply generic_format_opp, Fb | lra]. }
    rewrite <- Hs in G. apply Rabs_lt_inv in Hsl. lra. }
assert (He : Rabs (B2R hi + B2R lo - B2R s) <= bpow radix2 971).
{ rewrite Hs, Rabs_minus_sym. apply RN_error. exact Hz. }
assert (Hlt : Rabs (RN (B2R lo + B2R (sub hi s))) < bpow radix2 1024).
{ rewrite Hb. apply Rle_lt_trans with (1 := He). apply bpow_lt. lia. }
generalize (@Bplus_correct 53 1024 _ _ mode_NE lo (sub hi s) Flo FT).
rewrite Rlt_bool_true by exact Hlt.
intros (HR & HF & _).
change (Bplus mode_NE lo (sub hi s)) with (add lo (sub hi s)) in HR, HF.
split; [exact HF|]. rewrite HR. exact Hb.
Qed.

(** [partial_cmp] of finite floats is the order of their values. *)
Lemma partial_cmp_finite :
  forall u v : f64, is_finite u = true -> is_finite v = true ->
  partial_cmp u v = Some (Rcompare (B2R u) (B2R v)).
Proof.
intros u v Fu Fv. unfold partial_cmp. apply Bcompare_correct; assumption.
Qed.
