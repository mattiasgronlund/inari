(** * The angle of the fast paths of [asin] and [acos]

    With [r = √((1 - t)(1 + t))], [DyadicAtan.fast_asin_atan t] of
    [Model.v] takes the arctangent of [q = t / r] up to the split [181/256]
    and of [q = r / t] above it, which is [asin t] and [acos t]
    ([asin_q], from [AtanIdent.asin_as_atan] and [acos_as_atan]); [q] is
    in [[2^-27, 1.0003]] and its arctangent in [[2^-28, 4/5]]
    ([atan_q_bounds], [asin_atan_range]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Sterbenz.
From Inari Require Import Model Mpfr Elementary AtanReal AtanIdent TwoSum TwoProduct DyDriver
  NearF64 NearCells FastRound FastRoundErr FastDiv FastHypPos FastAtanTables FastAtanIdent
  FastAtanCore FastAtanAsm FastDdSqrt.
From Inari Require DyExp DyPown DyAtanTiny DyExpRules FastExpErr MulRuTiny FastLogNorm.
From Inari Require Import FastAsinReal.

Open Scope R_scope.

(** The quotient [q] that [fast_asin_atan] takes the arctangent of, with
    [r = √((1 - t)(1 + t))]: [t / r = tan(asin t)] up to the split and
    [r / t = tan(acos t)] above it ([asin_as_atan], [acos_as_atan]). As
    [181/256 < 1/√2], [r > 0.707] below the split and [r < 0.7072]
    above it, so [q <= 1.0003]. *)
Lemma asin_q :
  forall t, bpow radix2 (-27) <= t <= 1 - bpow radix2 (-53) ->
  bpow radix2 (-27) <= sqrt ((1 - t) * (1 + t)) <= 1 /\
  (t <= 181 / 256 -> 707 / 1000 <= sqrt ((1 - t) * (1 + t))) /\
  exists q, bpow radix2 (-27) <= q <= 10003 / 10000 /\
    q = (if Rle_bool t (181 / 256) then t / sqrt ((1 - t) * (1 + t))
         else sqrt ((1 - t) * (1 + t)) / t) /\
    (if Rle_bool t (181 / 256) then asin t else acos t) = atan q.
Proof.
intros t [Ht0 Ht1].
assert (K27 : bpow radix2 (-27) = / 134217728) by reflexivity.
assert (K53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
rewrite K27 in Ht0 |- *. rewrite K53 in Ht1.
assert (Hp : 0 <= (1 - t) * (1 + t)) by nra.
pose proof (sqrt_positivity _ Hp) as Hr0.
pose proof (sqrt_sqrt _ Hp) as Hrr.
set (r := sqrt ((1 - t) * (1 + t))) in *.
(* [r^2 = 1 - t^2 >= 1 - (1 - 2^-53)^2 > 2^-54]. *)
assert (Htt : t * t <= (1 - / 9007199254740992) * (1 - / 9007199254740992))
  by (apply Rmult_le_compat; lra).
assert (Hrlo : / 134217728 <= r).
{ destruct (Rle_or_lt (/ 134217728) r) as [H | H]; [exact H |].
  assert (r * r <= r * / 134217728) by (apply Rmult_le_compat_l; lra).
  assert (r * / 134217728 < / 134217728 * / 134217728) by (apply Rmult_lt_compat_r; lra).
  lra. }
assert (Hrhi : r <= 1) by nra.
(* Up to the split, [r^2 >= 1 - (181/256)^2 > 0.707^2]. *)
assert (Hr707 : t <= 181 / 256 -> 707 / 1000 <= r).
{ intros Hs.
  assert (Ts : t * t <= 181 / 256 * (181 / 256)) by (apply Rmult_le_compat; lra).
  destruct (Rle_or_lt (707 / 1000) r) as [H | H]; [exact H |].
  assert (r * r <= r * (707 / 1000)) by (apply Rmult_le_compat_l; lra).
  assert (r * (707 / 1000) < 707 / 1000 * (707 / 1000)) by (apply Rmult_lt_compat_r; lra).
  lra. }
split; [split; assumption |]. split; [exact Hr707 |].
destruct (Rle_bool_spec t (181 / 256)) as [Hs | Hs].
- (* [q = t / r] with [r] in [[0.707, 1]]: [t <= q <= 0.70704 / 0.707]. *)
  specialize (Hr707 Hs).
  set (q := t / r).
  assert (Eq : q * r = t) by (unfold q; field; apply Rgt_not_eq; lra).
  assert (Hq0 : 0 <= q)
    by (unfold q, Rdiv; apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra]).
  exists q. split; [split; nra |]. split; [reflexivity |].
  exact (asin_as_atan t ltac:(lra)).
- (* [q = r / t] with [r^2 <= 1 - (181/256)^2 < 0.7072^2] and [t > 181/256]:
     [r <= q <= 0.7072 / (181/256)]. *)
  assert (Ts : 181 / 256 * (181 / 256) <= t * t) by (apply Rmult_le_compat; lra).
  assert (Hr7072 : r <= 7072 / 10000).
  { destruct (Rle_or_lt r (7072 / 10000)) as [H | H]; [exact H |].
    assert (r * (7072 / 10000) <= r * r) by (apply Rmult_le_compat_l; lra).
    assert (7072 / 10000 * (7072 / 10000) < r * (7072 / 10000))
      by (apply Rmult_lt_compat_r; lra).
    lra. }
  set (q := r / t).
  assert (Eq : q * t = r) by (unfold q; field; apply Rgt_not_eq; lra).
  assert (Hq0 : 0 <= q)
    by (unfold q, Rdiv; apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra]).
  exists q. split; [split; nra |]. split; [reflexivity |].
  exact (acos_as_atan t ltac:(lra)).
Qed.

Lemma atan_q_bounds :
  forall q, bpow radix2 (-27) <= q <= 10003 / 10000 -> bpow radix2 (-28) <= atan q <= 4 / 5.
Proof.
intros q [Hq0 Hq1].
assert (P27 : bpow radix2 (-27) = / 134217728) by reflexivity.
assert (P28 : bpow radix2 (-28) = / 268435456) by reflexivity.
rewrite P27 in Hq0. rewrite P28.
assert (Hlo : q / 2 <= atan q) by (apply atan_lower; lra).
destruct (Rle_or_lt q 1) as [H1 | H1].
- destruct (atan_pos_le q) as [_ Hu]; [lra |]. split; lra.
- (* [atan q <= atan 1 + (q - 1) = π/4 + (q - 1)] ([atan_lipschitz]), and
     [π/2 <= hi + |lo| + 2^-107] with [hi] and [lo] the halves of [PIO2]. *)
  pose proof (atan_lipschitz q 1) as L.
  rewrite atan_1, (Rabs_pos_eq (q - 1)) in L by lra.
  apply Rabs_le_inv in L.
  destruct FastAtanTables.fast_pio2_correct as (_ & _ & Ehi & Hl & He).
  rewrite Ehi in He.
  assert (E53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
  assert (E107 : bpow radix2 (-107) = / 162259276829213363391578010288128) by reflexivity.
  rewrite E53 in Hl. rewrite E107 in He.
  apply Rabs_le_inv in Hl. apply Rabs_le_inv in He.
  split; lra.
Qed.

(** The value [fast_asin_atan] approximates is in [[2^-28, 4/5]]. *)
Lemma asin_atan_range :
  forall t : f64, is_finite t = true -> bpow radix2 (-27) <= B2R t < 1 ->
  bpow radix2 (-28)
    <= (if Rle_bool (B2R t) (181 / 256) then asin (B2R t) else acos (B2R t)) <= 4 / 5.
Proof.
intros t Ft [H0 H1].
pose proof (below_one t Ft H1) as Hb.
destruct (asin_q (B2R t) (conj H0 Hb)) as (_ & _ & q & Hq & _ & Eq).
rewrite Eq. apply atan_q_bounds. exact Hq.
Qed.
