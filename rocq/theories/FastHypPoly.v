(** * The Taylor polynomial of the fast path of [sinh]

    [DyadicExp.fast_sinh_poly] of [Model.v] evaluates the odd Taylor
    polynomial [t + t^3/3! + ... + t^15/15!] of [sinh t] on [2^-27 <= t <
    1/4], with [t^2], [t^3], [1/3!] and the sum of the first two terms in
    double-double and the rest in [f64], and is within [2^-65] of [sinh t]
    relatively ([sinh_poly_correct]). [tanh] divides it by the polynomial
    of [cosh] of [FastCoshPoly.v] on [t < 1/8]. It returns the same with
    and without an FMA ([sinh_poly_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error.
From Inari Require Import Model Mpfr Encoding Elementary TwoSum TwoProduct DyDriver NearF64
  FastRound FastExpErr CancelLanes MulRuTiny ExpSeries HypTaylor FastSinhHorner FastSinhSteps.

Open Scope R_scope.

(** Powers of 2 as numerals, for [lra] (as in [FastCoshPoly.v]). *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp].

(** The assembly of [sinh_poly_correct] on the reals: [S], which stands
    for [sinh T], is within [3/2 T^17/17!] above [T + T^3 B], and the
    double-double [rh + rl] is [T + (ch + cl)], [ch + cl] is the product
    of [t3h + t3l], near [T^3], and [bh + bl], near [B], each within the
    bounds of [FastSinhSteps.v] and [FastSinhHorner.v]. *)
Local Lemma sh_assemble :
  forall T B S rh rl ch cl t3h t3l bh bl : R,
  bpow radix2 (-27) <= T < / 4 ->
  T + T * (T * T) * B <= S <= T + T * (T * T) * B + 3 / 2 * (T ^ 17 / 355687428096000) ->
  Rabs (rh + rl - (T + ch + cl)) <= bpow radix2 (-101) * T ->
  Rabs (ch + cl - (t3h + t3l) * (bh + bl)) <=
    bpow radix2 (-101) * (T * (T * T)) + 8 * bpow radix2 (-1075) ->
  Rabs (t3h + t3l - T * (T * T)) <=
    bpow radix2 (-103) * (T * (T * T)) + 3 * bpow radix2 (-1075) ->
  / 8 <= bh <= / 4 -> Rabs bl <= bpow radix2 (-53) ->
  Rabs (bh + bl - B) <= bpow radix2 (-62) + bpow radix2 (-100) ->
  bpow radix2 (-27) <= rh + rl <= / 2 /\ Rabs (rh + rl - S) <= bpow radix2 (-65) * S.
Proof.
intros T B S rh rl ch cl t3h t3l bh bl HT HS Er Ec E3 Bbh Bbl Eb.
pose proof (bpow_gt_0 radix2 (-27)) as P27.
assert (HT0 : 0 <= T) by lra.
(* [T^2] is in [[2^-54, T/4]], and [v = T^3] in [[2^-54 T, T/16]]. *)
assert (HU : bpow radix2 (-54) <= T * T <= T * / 4).
{ split.
  - replace (bpow radix2 (-54)) with (bpow radix2 (-27) * bpow radix2 (-27)) by (num; lra).
    apply Rmult_le_compat; lra.
  - apply Rmult_le_compat_l; lra. }
assert (HV : bpow radix2 (-54) * T <= T * (T * T) <= T * (T * / 4)).
{ split.
  - rewrite (Rmult_comm (bpow radix2 (-54))). apply Rmult_le_compat_l; lra.
  - apply Rmult_le_compat_l; lra. }
assert (HV0 : 0 <= T * (T * T)) by (apply Rmult_le_pos; [lra | apply Rmult_le_pos; lra]).
(* [B] is within [2^-62 + 2^-100] of [bh + bl], so in [[1/8 - 2^-52, 1/4 + 2^-52]]. *)
assert (Bbl' := Rabs_le_inv _ _ Bbl).
assert (HB : / 8 - bpow radix2 (-52) <= B <= / 4 + bpow radix2 (-52)).
{ apply Rabs_le_inv in Eb. revert Bbh Bbl' Eb. num. intros. lra. }
assert (HVB : T * (T * T) * (/ 8 - bpow radix2 (-52)) <= T * (T * T) * B <=
              T * (T * T) * (/ 4 + bpow radix2 (-52)))
  by (split; apply Rmult_le_compat_l; lra).
(* The two products of the error. *)
assert (H3 : Rabs ((t3h + t3l - T * (T * T)) * (bh + bl)) <=
             (bpow radix2 (-103) * (T * (T * T)) + 3 * bpow radix2 (-1075)) *
             (/ 4 + bpow radix2 (-53))).
{ apply Rabs_mul_le; [exact E3 | apply Rabs_le; lra]. }
assert (H4 : Rabs (T * (T * T) * (bh + bl - B)) <=
             T * (T * T) * (bpow radix2 (-62) + bpow radix2 (-100))).
{ apply Rabs_mul_le; [rewrite Rabs_pos_eq by exact HV0; lra | exact Eb]. }
(* The truncation [3/2 T^17/17!], with [T^16 <= 2^-32]. *)
assert (H17 : T ^ 17 <= T * / 4294967296).
{ replace (T ^ 17) with (T * T ^ 16) by ring.
  apply Rmult_le_compat_l; [lra|].
  apply Rle_trans with ((/ 4) ^ 16); [apply pow_incr; lra | cbn [pow]; lra]. }
(* [rh + rl - S] is the sum of the five errors. *)
apply Rabs_le_inv in Er. apply Rabs_le_inv in Ec.
apply Rabs_le_inv in H3. apply Rabs_le_inv in H4.
clear Bbl Eb E3.
cbn [bpow radix_val radix2 Z.opp] in *.
split; [split | apply Rabs_le; split]; lra.
Qed.

(** The polynomial of [sinh] as a double-double [sh + sl], with [sh] the
    rounding of [sh + sl] to nearest, within [2^-65] of [sinh t]
    relatively. *)
Theorem sinh_poly_correct :
  forall fma t,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < / 4 ->
  let '(sh, sl) := DyadicExp.fast_sinh_poly fma t in
  is_finite sh = true /\ is_finite sl = true /\ B2R sh = RN (B2R sh + B2R sl) /\
  bpow radix2 (-27) <= B2R sh <= / 2 /\ Rabs (B2R sl) <= bpow radix2 (-52) * B2R sh /\
  Rabs (B2R sh + B2R sl - sinh (B2R t)) <= bpow radix2 (-65) * sinh (B2R t).
Proof.
intros fma t Ft Ht.
pose proof (bpow_gt_0 radix2 (-27)) as P27.
pose proof (bpow_gt_0 radix2 (-55)) as P55.
pose proof (bpow_gt_0 radix2 (-1075)) as Peps.
assert (HT0 : 0 <= B2R t) by lra.
(* [u = t^2] is at most [1/16], and [v = t^3] in [[2^-81, 1/64]] and at
   most [t/16]. *)
assert (HU : 0 <= B2R t * B2R t <= / 16).
{ split; [apply Rmult_le_pos; lra|].
  apply Rle_trans with (/ 4 * / 4); [apply Rmult_le_compat; lra | lra]. }
assert (HV : bpow radix2 (-81) <= B2R t * (B2R t * B2R t) <= / 64).
{ destruct Ht as (Ht0 & Ht1). split.
  - replace (bpow radix2 (-81)) with
      (bpow radix2 (-27) * (bpow radix2 (-27) * bpow radix2 (-27))) by (num; lra).
    apply Rmult_le_compat; [lra | apply Rmult_le_pos; lra | lra |].
    apply Rmult_le_compat; lra.
  - apply Rle_trans with (/ 4 * (/ 4 * / 4)); [| lra].
    apply Rmult_le_compat; [lra | apply Rmult_le_pos; lra | lra |].
    apply Rmult_le_compat; lra. }
assert (HVT : B2R t * (B2R t * B2R t) <= B2R t / 16).
{ apply Rle_trans with (B2R t * / 16); [apply Rmult_le_compat_l; lra | lra]. }
(* [t^2] as [uh + ul] and [t^3] as [t3h + t3l]. *)
pose proof (sh_t3 fma t Ft Ht) as H3. cbv zeta in H3.
destruct H3 as (Fu & F3h & F3l & _ & Bu & Eu & E3h & B3l & E3).
assert (Hd : Rabs (B2R (mul t t) - B2R t * B2R t) <= bpow radix2 (-57)).
{ apply Rle_trans with (1 := Eu). revert HU. num. intros. lra. }
assert (Bu0 : 0 <= B2R (mul t t) <= / 16) by lra.
unfold DyadicExp.fast_sinh_poly. cbv zeta.
(* [1/3! + t^2 shA (t^2)] as [bh + bl]. *)
destruct (Fast.fast_two_sum (from_bits (fst DyadicExp.SH3)) _) as [bh b0] eqn:Eb.
pose proof (sh_b (mul t t) (B2R t * B2R t) Fu Bu0 HU Hd) as Hb. cbv zeta in Hb.
rewrite Eb in Hb. cbv beta iota zeta in Hb. cbv beta iota.
destruct Hb as (Fbh & Fbl & Bbh & Bbl & Ebb).
(* [t^3 (1/3! + t^2 shA (t^2))] as [ch + cl]. *)
destruct (sh_c fma (mul t (mul t t)) _ bh _ _ F3h F3l Fbh Fbl HV E3h B3l Bbh Bbl)
  as (Fch & Fcl & _ & Bch & Bcl & Ec).
assert (Hch : Rabs (B2R (mul (mul t (mul t t)) bh)) <= B2R t / 16) by lra.
assert (Hcl : bpow radix2 (-50) * (B2R t * (B2R t * B2R t)) + 8 * bpow radix2 (-1075) <=
              bpow radix2 (-50) * B2R t).
{ generalize (proj1 Ht) HVT. num. intros. lra. }
apply (Rle_trans _ _ _ Bcl) in Hcl.
(* [t + (ch + cl)] as [rh + rl]. *)
pose proof (sh_final t _ _ Ft Fch Fcl Ht Hch Hcl) as Hf.
(* [destruct] abstracts the sums in [Hf] too. *)
destruct (Fast.fast_two_sum t _) as [sh s0]. cbv beta iota in Hf |- *.
destruct (Fast.fast_two_sum sh _) as [rh rl]. cbv beta iota in Hf |- *.
destruct Hf as (Frh & Frl & Rr & Ef).
(* The Taylor polynomial is [t + t^3 (1/3! + t^2 shA (t^2))]. *)
assert (Hs : 0 <= B2R t <= 1) by lra.
apply sinh_taylor in Hs.
assert (Hid : sinh_taylor15 (B2R t) = B2R t + B2R t * (B2R t * B2R t) *
                (/ 6 + B2R t * B2R t * shA (B2R t * B2R t)))
  by (unfold sinh_taylor15, shA; field).
rewrite Hid in Hs.
assert (HS : B2R t + B2R t * (B2R t * B2R t) * (/ 6 + B2R t * B2R t * shA (B2R t * B2R t)) <=
             sinh (B2R t) <=
             B2R t + B2R t * (B2R t * B2R t) * (/ 6 + B2R t * B2R t * shA (B2R t * B2R t)) +
             3 / 2 * (B2R t ^ 17 / 355687428096000)) by lra.
destruct (sh_assemble _ _ _ _ _ _ _ _ _ _ _ Ht HS Ef Ec E3 Bbh Bbl Ebb) as (Hr & Herr).
destruct (dd_out rh rl Frh Frl Rr Hr) as (Hrh & Hrl).
repeat split; assumption || lra.
Qed.

(** The polynomial of [sinh] is the same with and without an FMA. *)
Theorem sinh_poly_fma :
  forall t,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < / 4 ->
  DyadicExp.fast_sinh_poly true t = DyadicExp.fast_sinh_poly false t.
Proof.
intros t Ft Ht.
pose proof (bpow_gt_0 radix2 (-27)) as P27.
(* [uh], [t3h] and the exactness of their products, from [sh_t3]. *)
pose proof (sh_t3 true t Ft Ht) as H3. cbv zeta in H3.
destruct H3 as (Fu & F3h & F3l & X3 & Bu & Eu & E3h & B3l & _).
unfold DyadicExp.fast_sinh_poly. cbv zeta.
rewrite (two_prod_err_fma_eq t t Ft Ft (proj1 (X3 true)) (proj1 (X3 false))).
rewrite (two_prod_err_fma_eq t (mul t t) Ft Fu (proj2 (X3 true)) (proj2 (X3 false))).
(* [u = t^2] is at most [1/16], so [uh] is within [2^-57] of it. *)
assert (HT0 : 0 <= B2R t) by lra.
assert (HU : 0 <= B2R t * B2R t <= / 16).
{ split; [apply Rmult_le_pos; lra|].
  apply Rle_trans with (/ 4 * / 4); [apply Rmult_le_compat; lra | lra]. }
assert (Hd : Rabs (B2R (mul t t) - B2R t * B2R t) <= bpow radix2 (-57)).
{ apply Rle_trans with (1 := Eu). revert HU. num. intros. lra. }
destruct (Fast.fast_two_sum (from_bits (fst DyadicExp.SH3)) _) as [bh b0] eqn:Eb.
assert (Bu0 : 0 <= B2R (mul t t) <= / 16) by (pose proof (bpow_gt_0 radix2 (-55)); lra).
pose proof (sh_b (mul t t) (B2R t * B2R t) Fu Bu0 HU Hd) as Hb. cbv zeta in Hb.
rewrite Eb in Hb. cbv beta iota zeta in Hb.
destruct Hb as (Fbh & Fbl & Bbh & Bbl & _).
(* [v = t^3] is in [[2^-81, 1/64]]. *)
assert (HV : bpow radix2 (-81) <= B2R t * (B2R t * B2R t) <= / 64).
{ destruct Ht as (Ht0 & Ht1). split.
  - replace (bpow radix2 (-81)) with
      (bpow radix2 (-27) * (bpow radix2 (-27) * bpow radix2 (-27))) by (num; lra).
    apply Rmult_le_compat; [lra | apply Rmult_le_pos; lra | lra |].
    apply Rmult_le_compat; lra.
  - apply Rle_trans with (/ 4 * (/ 4 * / 4)); [| lra].
    apply Rmult_le_compat; [lra | apply Rmult_le_pos; lra | lra |].
    apply Rmult_le_compat; lra. }
destruct (sh_c true (mul t (mul t t)) _ bh _ _ F3h F3l Fbh Fbl HV E3h B3l Bbh Bbl)
  as (_ & _ & Xc & _).
cbv zeta in Xc.
rewrite (two_prod_err_fma_eq (mul t (mul t t)) bh F3h Fbh (Xc true) (Xc false)).
reflexivity.
Qed.
