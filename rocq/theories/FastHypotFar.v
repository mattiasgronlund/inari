(** * The rule of the fast path of [hypot] at a gap of 27 or more

    For finite [big >= small > 0] whose biased exponents differ by 27 or
    more, [big] is normal and
    [big < hypot(big, small) < big + small^2 / (2 big) < big + ulp(big) / 2],
    so [hypot(big, small)] rounds down and to nearest to [big]
    ([hypot_far_dir], [hypot_far_near]) and up to the [f64] after [big],
    which is +inf after the largest [f64]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr DyDriver NearF64 Encoding MpfrRound.
From Inari Require IdealGetD DyExpRules FastRound StepUp.

Open Scope R_scope.

Local Notation G := (generic_format radix2 fexp64).
Local Notation succ64 := (succ radix2 fexp64).

(** The bits of a positive finite [x] are a finite pattern [c] with the
    sign bit clear, and [x] is its [magnitude]. *)
Local Lemma pos_bits :
  forall x, is_finite x = true -> 0 < B2R x ->
  exists c, (0 <= c < 2047 * 2^52)%Z /\ to_bits x = c /\ B2R x = magnitude c.
Proof.
intros x Fx Hx.
destruct (to_bits_finite x Fx) as (c & Hc & Hb).
assert (Sx : Bsign x = false).
{ rewrite StepUp.Bsign_B2R by (assumption || lra). apply Rlt_bool_false. lra. }
destruct (from_bits_finite (Bsign x) c Hc) as (_ & _ & Rx).
rewrite <- Hb, from_to_bits, Sx in Rx. cbv beta iota in Rx.
rewrite Sx in Hb. cbn [sign_bit] in Hb. rewrite Z.add_0_l in Hb.
exists c. split; [exact Hc|]. split; [exact Hb | exact Rx].
Qed.

(** What both theorems use: with [u = ulp(big)], [succ big = big + u],
    [u <= 2^971], and [big < hypot(big, small) < big + u / 2]. *)
Local Lemma far_facts :
  forall big small,
  is_finite big = true -> is_finite small = true ->
  0 < B2R small <= B2R big ->
  (27 <= Z.shiftr (to_bits big) 52 - Z.shiftr (to_bits small) 52)%Z ->
  exists c u,
  (0 <= c < 2047 * 2^52)%Z /\ to_bits big = c /\ B2R big = magnitude c /\
  succ64 (B2R big) = B2R big + u /\ 0 < u <= bpow radix2 971 /\
  B2R big < sqrt (B2R big * B2R big + B2R small * B2R small) < B2R big + u / 2.
Proof.
intros big small Fb Fs Hs Hg.
destruct (pos_bits big Fb ltac:(lra)) as (cb & Hcb & Bb & Rb).
destruct (pos_bits small Fs ltac:(lra)) as (cs & Hcs & Bs & Rs).
(* For a positive [v], [to_bits v >> 52] is the biased exponent [c / 2^52]. *)
rewrite Bb, Bs, !Z.shiftr_div_pow2 in Hg by lia.
destruct (magnitude_bounds cb (proj1 Hcb)) as ((_ & _) & Hb2).
destruct (magnitude_bounds cs (proj1 Hcs)) as ((_ & Hs1) & _).
pose proof (ulp_magnitude cb (proj1 Hcb)) as Hu.
assert (HEs : (0 <= cs / 2^52)%Z) by (apply Z.div_pos; lia).
assert (HEb : (cb / 2^52 <= 2046)%Z) by (clear - Hcb; zlia).
(* The biased exponent of [big] is at least 27, so [big] is normal, with
   [2^(E - 1023) <= big] and [ulp(big) = 2^(E - 1075)]. *)
specialize (Hb2 ltac:(lia)).
unfold expo in Hu. rewrite Z.max_l in Hu by lia.
set (E := (cb / 2^52)%Z) in *.
(* [A] is half of [ulp(big)]. *)
set (A := bpow radix2 (E - 1076)).
assert (HA : 0 < A) by apply bpow_gt_0.
assert (U : bpow radix2 (E - 1075) = 2 * A).
{ unfold A. replace (E - 1075)%Z with (1 + (E - 1076))%Z by ring.
  rewrite bpow_plus. reflexivity. }
assert (B0 : A * bpow radix2 53 <= B2R big).
{ rewrite Rb. replace (A * bpow radix2 53) with (bpow radix2 (E - 1023)); [exact Hb2|].
  unfold A. rewrite <- bpow_plus. f_equal. ring. }
(* [small < 2^(Es - 1022) <= 2^(E - 1049)], as [Es <= E - 27]. *)
assert (S1 : B2R small < A * bpow radix2 27).
{ rewrite Rs. apply Rlt_le_trans with (1 := Hs1).
  unfold A. rewrite <- bpow_plus. apply bpow_le. lia. }
assert (K : bpow radix2 27 * bpow radix2 27 = 2 * bpow radix2 53).
{ rewrite <- bpow_plus. replace (27 + 27)%Z with (1 + 53)%Z by reflexivity.
  rewrite bpow_plus. reflexivity. }
(* [small^2 < 2^(2E - 2098) <= 2 big A]. *)
assert (Q : B2R small * B2R small < 2 * B2R big * A).
{ assert (P1 : B2R small * B2R small < (A * bpow radix2 27) * (A * bpow radix2 27))
    by (apply Rmult_le_0_lt_compat; lra).
  replace ((A * bpow radix2 27) * (A * bpow radix2 27))
    with (A * A * (bpow radix2 27 * bpow radix2 27)) in P1 by ring.
  rewrite K in P1.
  assert (P2 : A * (A * bpow radix2 53) <= A * B2R big)
    by (apply Rmult_le_compat_l; lra).
  lra. }
exists cb, (2 * A).
split; [exact Hcb|]. split; [exact Bb|]. split; [exact Rb|].
split.
{ rewrite Rb, succ_eq_pos by (rewrite <- Rb; lra). rewrite Hu, U. reflexivity. }
split.
{ split; [lra|]. rewrite <- U. apply bpow_le. lia. }
(* [r = sqrt(big^2 + small^2)] has [big^2 < r^2 < (big + A)^2]. *)
set (b := B2R big) in *. set (s := B2R small) in *.
assert (R0 : 0 <= sqrt (b * b + s * s)) by apply sqrt_pos.
assert (R2 : sqrt (b * b + s * s) * sqrt (b * b + s * s) = b * b + s * s)
  by (apply sqrt_sqrt; nra).
set (r := sqrt (b * b + s * s)) in *.
replace (2 * A / 2) with A by field.
split; nra.
Qed.

(** ** The theorems *)

Theorem hypot_far_dir :
  forall big small up,
  is_finite big = true -> is_finite small = true ->
  0 < B2R small <= B2R big ->
  (27 <= Z.shiftr (to_bits big) 52 - Z.shiftr (to_bits small) 52)%Z ->
  rounds up (sqrt (B2R big * B2R big + B2R small * B2R small))
    (if up then from_bits (to_bits big + 1) else big).
Proof.
intros big small up Fb Fs Hs Hg.
destruct (far_facts big small Fb Fs Hs Hg) as (c & u & Hc & Bb & Rb & Su & Hu & Hr).
set (r := sqrt (B2R big * B2R big + B2R small * B2R small)) in *.
assert (Gb : G (B2R big)) by apply generic_format_B2R.
(* A float above [big] is at least [succ big = big + u], so above [r]. *)
assert (Above : forall g, G g -> B2R big < g -> B2R big + u <= g).
{ intros g Gg Hlt. rewrite <- Su.
  apply (succ_le_lt radix2 fexp64); first [exact Gb | exact Gg | exact Hlt | typeclasses eauto]. }
destruct up.
- rewrite Bb.
  destruct (Z.eq_dec (c + 1) (2047 * 2^52)) as [HM|HM].
  + (* [big] is the largest [f64]: [succ big = 2^1024], and every [f64]
       is at most [big], so below [r]. *)
    assert (E : B2R big + u = bpow radix2 1024).
    { rewrite <- Su, Rb, <- magnitude_succ by lia. rewrite HM. apply magnitude_2047. }
    rewrite HM, from_bits_2047.
    unfold rounds. cbn [with_val mpfr_round].
    intros g Fg. destruct (IdealGetD.f64_format_G g Fg) as (Gg & Hg2).
    apply Rabs_def2 in Hg2 as [Hg2 _].
    destruct (Rle_or_lt g (B2R big)) as [Hle|Hlt]; [lra|].
    pose proof (Above g Gg Hlt). lra.
  + (* Otherwise the pattern after [big] is [succ big]. *)
    assert (Hc1 : (0 <= c + 1 < 2047 * 2^52)%Z) by lia.
    destruct (from_bits_finite false (c + 1) Hc1) as (F1 & _ & R1).
    cbn [sign_bit] in F1, R1. rewrite Z.add_0_l in F1, R1. cbv beta iota in R1.
    rewrite magnitude_succ in R1 by lia. rewrite <- Rb in R1.
    unfold rounds.
    apply (DyExpRules.rnd_bracket big (from_bits (c + 1)) true r Fb F1).
    * change (SpecFloat.fexp 53 1024) with fexp64. exact R1.
    * rewrite R1, Su. lra.
- unfold rounds. apply IdealGetD.finite_round_ok; [exact Fb|]. cbn [rnd_pt].
  split; [exact Gb|]. split; [lra|].
  intros g Gg Hle. destruct (Rle_or_lt g (B2R big)) as [H|H]; [exact H|].
  pose proof (Above g Gg H). lra.
Qed.

Theorem hypot_far_near :
  forall big small,
  is_finite big = true -> is_finite small = true ->
  0 < B2R small <= B2R big ->
  (27 <= Z.shiftr (to_bits big) 52 - Z.shiftr (to_bits small) 52)%Z ->
  near_round (sqrt (B2R big * B2R big + B2R small * B2R small)) big.
Proof.
intros big small Fb Fs Hs Hg.
destruct (far_facts big small Fb Fs Hs Hg) as (c & u & Hc & Bb & Rb & Su & Hu & Hr).
set (r := sqrt (B2R big * B2R big + B2R small * B2R small)) in *.
assert (Gb : G (B2R big)) by apply generic_format_B2R.
(* [big <= MAX = 2^1024 - 2^971] and [u <= 2^971], so [r < big + u / 2]
   is below [2^1024 - 2^970]. *)
assert (Mx : B2R big <= bpow radix2 1024 - bpow radix2 971).
{ apply IdealGetD.G_le_max; [exact Gb|].
  pose proof (abs_B2R_lt_emax 53 1024 big) as H. apply Rabs_def2 in H as [H _]. exact H. }
assert (H970 : bpow radix2 971 = 2 * bpow radix2 970).
{ replace 971%Z with (1 + 970)%Z by reflexivity. rewrite bpow_plus. reflexivity. }
unfold near_round.
destruct (Rle_dec _ _) as [Hle|_].
{ exfalso. rewrite Rabs_pos_eq in Hle by lra. lra. }
split; [exact Fb|]. split.
- (* [r] is between [big] and the midpoint [big + u / 2] to [succ big]. *)
  symmetry. apply FastRound.rn_between; [exact Gb | lra |].
  pose proof (pred_lt_id radix2 fexp64 (B2R big) ltac:(lra)). rewrite Su. lra.
- intros _ H0. exfalso. lra.
Qed.
