(** * The double-double of the fast path of [hypot]

    [DyadicRoot.hypot_dd fma big small], for finite [big >= small > 0]
    whose biased exponents differ by less than 27, returns [None] or a
    double-double [(h, l)] with [h = RN (h + l)] within 2^-98 of
    [hypot(big, small) 2^-e], for [e] in [-1021, 1022]
    ([hypot_dd_correct]), and the same with and without an FMA
    ([hypot_dd_fma]). Scaled by 2^-e, [big] is in [1/2, 1) and [small] at
    least 2^-78, so the scaling is exact ([hypot_dd_scale]), the sum
    [x^2 + y^2] is within 2^-102 of [ah + al] ([FastHypotSum.v]), and
    [dd_sqrt_correct] of [FastDdSqrt.v] bounds the square root. *)

From Stdlib Require Import Bool ZArith Reals Lra Lia Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Mult_error.
From Inari Require Import Model Encoding TwoSum FastDdSqrt FastHypotSum.
From Inari Require FastLogReduce SqrtSlow.

Open Scope R_scope.

Local Notation format := (generic_format radix2 fexp64).

(** ** The scaling *)

(** The bits [k 2^52] are those of [2^(k - 1023)], for a biased exponent
    [k] of a normal number (a copy of [FastRound.pow2_bits] for the form
    that [hypot_dd] builds). *)
Local Lemma pow2_shift :
  forall k, (1 <= k <= 2046)%Z ->
  is_finite (from_bits (Z.shiftl k 52)) = true /\
  B2R (from_bits (Z.shiftl k 52)) = bpow radix2 (k - 1023).
Proof.
intros k Hk.
rewrite Z.shiftl_mul_pow2 by lia.
destruct (from_bits_finite false (k * 2^52)) as (Fp & _ & Rp);
  [simpl Z.pow; lia|].
cbn [sign_bit] in Fp, Rp. rewrite Z.add_0_l in Fp, Rp.
split; [exact Fp|]. rewrite Rp.
replace (k * 2^52)%Z with (k * 2^52 + 0)%Z by ring.
rewrite magnitude_split by (simpl Z.pow; lia).
rewrite (proj2 (Z.eqb_neq k 0)) by lia.
replace (Z.max k 1 - 1075)%Z with (k - 1023 - 52)%Z by lia.
unfold F2R; cbn [Fnum Fexp].
rewrite Z.add_0_l, (IZR_Zpower radix2) by easy.
rewrite <- bpow_plus. f_equal. ring.
Qed.

(** [v 2^e] is a float with [v] when it is at least 2^-1021. *)
Local Lemma scale_exact :
  forall v e, format v -> bpow radix2 (-1021) <= v * bpow radix2 e ->
  format (v * bpow radix2 e).
Proof.
intros v e Fv Hve.
pose proof (bpow_gt_0 radix2 (-1021)) as P.
assert (Hv : v <> 0) by (intros ->; lra).
assert (Hm : (-1020 <= mag radix2 (v * bpow radix2 e))%Z).
{ apply mag_ge_bpow. rewrite Rabs_pos_eq by lra. exact Hve. }
rewrite mag_mult_bpow in Hm by exact Hv.
apply mult_bpow_exact_FLT; [exact Fv | lia].
Qed.

(** With [eb] the biased exponent of [big], in [1, 2044], [s = 2^(1022 -
    eb)] scales [big] exactly into [1/2, 1) and [small] exactly into
    [2^-78, big s]: a normal [small] has a biased exponent above [eb -
    27], and a subnormal one forces [eb <= 26]. *)
Lemma hypot_dd_scale :
  forall big small,
  is_finite big = true -> is_finite small = true ->
  0 < B2R small <= B2R big ->
  (Z.shiftr (to_bits big) 52 - Z.shiftr (to_bits small) 52 < 27)%Z ->
  Z.shiftr (to_bits big) 52 <> 0%Z -> (Z.shiftr (to_bits big) 52 <= 2044)%Z ->
  forall eb sc, eb = Z.shiftr (to_bits big) 52 -> sc = from_bits (Z.shiftl (2045 - eb) 52) ->
  (1 <= eb <= 2044)%Z /\
  is_finite (mul big sc) = true /\ is_finite (mul small sc) = true /\
  B2R (mul big sc) = B2R big * bpow radix2 (1022 - eb) /\
  B2R (mul small sc) = B2R small * bpow radix2 (1022 - eb) /\
  / 2 <= B2R (mul big sc) < 1 /\
  bpow radix2 (-78) <= B2R (mul small sc) <= B2R (mul big sc).
Proof.
intros big small Fb Fs Hsb Hg Heb0 Heb1 eb sc -> ->.
destruct (FastLogReduce.pos_bits big Fb ltac:(lra)) as (cb & Hcb & Bb & Rb).
destruct (FastLogReduce.pos_bits small Fs ltac:(lra)) as (cs & Hcs & Bs & Rs).
assert (Eb : Z.shiftr cb 52 = (cb / 2 ^ 52)%Z) by (apply Z.shiftr_div_pow2; lia).
assert (Es : Z.shiftr cs 52 = (cs / 2 ^ 52)%Z) by (apply Z.shiftr_div_pow2; lia).
rewrite Bb, Eb in Hg, Heb0, Heb1 |- *. rewrite Bs, Es in Hg.
destruct (magnitude_bounds cb ltac:(lia)) as ((_ & Hblt) & Hbge).
destruct (magnitude_bounds cs ltac:(lia)) as (_ & Hsge).
rewrite <- Rb in Hblt, Hbge. rewrite <- Rs in Hsge.
specialize (Hbge Heb0).
assert (Hb0 : (0 <= cb / 2 ^ 52)%Z) by (apply Z.div_pos; [lia | reflexivity]).
assert (Hs0 : (0 <= cs / 2 ^ 52)%Z) by (apply Z.div_pos; [lia | reflexivity]).
set (eb := (cb / 2 ^ 52)%Z) in *. set (es := (cs / 2 ^ 52)%Z) in *.
destruct (pow2_shift (2045 - eb) ltac:(lia)) as (Fsc & Rsc).
replace (2045 - eb - 1023)%Z with (1022 - eb)%Z in Rsc by ring.
set (sc := from_bits (Z.shiftl (2045 - eb) 52)) in *.
pose proof (bpow_gt_0 radix2 (1022 - eb)) as PS.
pose proof (bpow_gt_0 radix2 (-78)) as P78.
assert (P1021 : bpow radix2 (-1021) <= bpow radix2 (-78)) by (apply bpow_le; lia).
assert (P1 : bpow radix2 (-78) <= / 2)
  by (change (/ 2) with (bpow radix2 (-1)); apply bpow_le; lia).
assert (P1024 : 1 <= bpow radix2 1024)
  by (change 1 with (bpow radix2 0); apply bpow_le; lia).
(* [big] is in [2^(eb - 1023), 2^(eb - 1022)). *)
assert (HX : / 2 <= B2R big * bpow radix2 (1022 - eb) < 1).
{ assert (E1 : bpow radix2 (eb - 1023) * bpow radix2 (1022 - eb) = / 2).
  { rewrite <- bpow_plus. replace (eb - 1023 + (1022 - eb))%Z with (-1)%Z by ring.
    reflexivity. }
  assert (E2 : bpow radix2 (eb - 1022) * bpow radix2 (1022 - eb) = 1).
  { rewrite <- bpow_plus. replace (eb - 1022 + (1022 - eb))%Z with 0%Z by ring.
    reflexivity. }
  split.
  - rewrite <- E1. apply Rmult_le_compat_r; lra.
  - rewrite <- E2. apply Rmult_lt_compat_r; lra. }
(* [small] is at least 2^-1074, and at least 2^(es - 1023) when normal. *)
assert (Hsk : exists k, (-78 <= k + (1022 - eb))%Z /\ bpow radix2 k <= B2R small).
{ destruct (Z.eq_dec es 0) as [E0|E0].
  - exists (-1074)%Z. split; [lia|].
    apply (generic_format_ge_bpow radix2 (FLT_exp (-1074) 53)).
    + intros e. unfold FLT_exp. lia.
    + lra.
    + apply generic_format_B2R.
  - exists (es - 1023)%Z. split; [lia|]. exact (Hsge E0). }
destruct Hsk as (k & Hk & Hsk).
assert (HY : bpow radix2 (-78) <= B2R small * bpow radix2 (1022 - eb)).
{ apply Rle_trans with (bpow radix2 k * bpow radix2 (1022 - eb)).
  - rewrite <- bpow_plus. apply bpow_le. exact Hk.
  - apply Rmult_le_compat_r; lra. }
assert (HYX : B2R small * bpow radix2 (1022 - eb) <= B2R big * bpow radix2 (1022 - eb))
  by (apply Rmult_le_compat_r; lra).
(* Both products are exact. *)
assert (Fx : format (B2R big * B2R sc)).
{ rewrite Rsc. apply scale_exact; [apply generic_format_B2R | lra]. }
assert (Ax : Rabs (B2R big * B2R sc) < bpow radix2 1024)
  by (rewrite Rsc, Rabs_pos_eq by lra; lra).
destruct (SqrtSlow.mul_exact big sc Fb Fsc Fx Ax) as (Fmx & Rmx & _).
assert (Fy : format (B2R small * B2R sc)).
{ rewrite Rsc. apply scale_exact; [apply generic_format_B2R | lra]. }
assert (Ay : Rabs (B2R small * B2R sc) < bpow radix2 1024)
  by (rewrite Rsc, Rabs_pos_eq by lra; lra).
destruct (SqrtSlow.mul_exact small sc Fs Fsc Fy Ay) as (Fmy & Rmy & _).
rewrite Rmx, Rmy, Rsc.
split; [lia|]. split; [exact Fmx|]. split; [exact Fmy|].
split; [reflexivity|]. split; [reflexivity|].
split; [exact HX|]. split; [exact HY | exact HYX].
Qed.

(** ** The theorems *)

Theorem hypot_dd_correct :
  forall fma big small h l e,
  is_finite big = true -> is_finite small = true ->
  0 < B2R small <= B2R big ->
  (Z.shiftr (to_bits big) 52 - Z.shiftr (to_bits small) 52 < 27)%Z ->
  DyadicRoot.hypot_dd fma big small = Some (h, l, e) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= e <= 1022)%Z /\
  Rabs (sqrt (B2R big * B2R big + B2R small * B2R small) * bpow radix2 (- e)
        - (B2R h + B2R l)) <= bpow radix2 (-98).
Proof.
intros fma big small h l e Fb Fs Hsb Hg Hdd.
unfold DyadicRoot.hypot_dd in Hdd. cbv zeta in Hdd.
match type of Hdd with context [if ?c then _ else _] => destruct c eqn:Heb end;
  [discriminate|].
apply Bool.orb_false_iff in Heb as (Heb0 & Heb1).
apply Z.eqb_neq in Heb0. apply Z.ltb_ge in Heb1.
set (eb := Z.shiftr (to_bits big) 52) in *.
set (sc := from_bits (Z.shiftl (2045 - eb) 52)) in *.
destruct (hypot_dd_scale big small Fb Fs Hsb Hg Heb0 Heb1 eb sc eq_refl eq_refl)
  as (Heb & Fx & Fy & Rx & Ry & HX & HY).
set (x := mul big sc) in *. set (y := mul small sc) in *.
destruct (Fast.fast_two_sum (mul x x) (mul y y)) as (r2, e2) eqn:E1.
match type of Hdd with context [Fast.fast_two_sum r2 ?t] =>
  destruct (Fast.fast_two_sum r2 t) as (ah, al) eqn:E2 end.
destruct (Fast.dd_sqrt fma ah al) as (sh, sl) eqn:E3.
(* [injection] stalls here, so take the pair apart by hand. *)
apply (f_equal (fun o => match o with Some p => p | None => (sh, sl, 0%Z) end)) in Hdd.
cbv beta iota in Hdd.
apply pair_equal_spec in Hdd as (Hdd & He). apply pair_equal_spec in Hdd as (Hh & Hl).
subst h l e.
destruct (hypot_sum_sq_correct fma x y r2 e2 ah al Fx Fy HX HY E1 E2)
  as (Fah & Fal & Hah & Hal & Hsum).
(* [ah] in [1/8, 4] is far inside the range of [dd_sqrt_correct]. *)
assert (Hah' : bpow radix2 (-900) <= B2R ah <= bpow radix2 900).
{ assert (B1 : bpow radix2 (-900) <= bpow radix2 (-3)) by (apply bpow_le; lia).
  assert (B2 : bpow radix2 2 <= bpow radix2 900) by (apply bpow_le; lia).
  change (bpow radix2 (-3)) with (/ 8) in B1. change (bpow radix2 2) with 4 in B2.
  lra. }
destruct (dd_sqrt_correct fma ah al sh sl Fah Fal Hah' Hal E3) as (Fsh & Fsl & Rsh & Herr).
split; [exact Fsh|]. split; [exact Fsl|]. split; [exact Rsh|]. split; [lia|].
replace (- (eb - 1022))%Z with (1022 - eb)%Z by ring.
(* [hypot(big, small) 2^(1022 - eb) = sqrt(x^2 + y^2)], as both are scaled
   exactly. *)
assert (HA : sqrt (B2R big * B2R big + B2R small * B2R small) * bpow radix2 (1022 - eb)
             = sqrt (B2R x * B2R x + B2R y * B2R y)).
{ rewrite Rx, Ry.
  pose proof (bpow_gt_0 radix2 (1022 - eb)) as PS.
  replace (B2R big * bpow radix2 (1022 - eb) * (B2R big * bpow radix2 (1022 - eb))
           + B2R small * bpow radix2 (1022 - eb) * (B2R small * bpow radix2 (1022 - eb)))
    with ((B2R big * B2R big + B2R small * B2R small)
          * (bpow radix2 (1022 - eb) * bpow radix2 (1022 - eb))) by ring.
  rewrite sqrt_mult_alt by nra.
  rewrite sqrt_square by lra. reflexivity. }
rewrite HA.
pose proof (bpow_gt_0 radix2 (-78)) as P78.
assert (Hxx : / 4 <= B2R x * B2R x < 1) by nra.
assert (Hyy : 0 <= B2R y * B2R y <= B2R x * B2R x)
  by (split; [nra | apply Rmult_le_compat; lra]).
assert (HQ : / 4 <= B2R x * B2R x + B2R y * B2R y <= 2) by lra.
(* The constants, with [eps = 2^-102]. *)
pose proof (bpow_gt_0 radix2 (-102)) as Pe.
assert (C100 : bpow radix2 (-100) = 4 * bpow radix2 (-102)).
{ change 4 with (bpow radix2 2). rewrite <- bpow_plus. reflexivity. }
assert (C98 : bpow radix2 (-98) = 16 * bpow radix2 (-102)).
{ change 16 with (bpow radix2 4). rewrite <- bpow_plus. reflexivity. }
assert (C8 : bpow radix2 (-102) <= / 8)
  by (change (/ 8) with (bpow radix2 (-3)); apply bpow_le; lia).
set (Q := B2R x * B2R x + B2R y * B2R y) in *.
set (Q' := B2R ah + B2R al) in *.
apply Rabs_le_inv in Hsum.
assert (HQ' : / 8 <= Q' <= 4) by lra.
assert (Hu : sqrt Q * sqrt Q = Q) by (apply sqrt_sqrt; lra).
assert (Hv : sqrt Q' * sqrt Q' = Q') by (apply sqrt_sqrt; lra).
pose proof (sqrt_pos Q) as Pu. pose proof (sqrt_pos Q') as Pv.
set (u := sqrt Q) in *. set (v := sqrt Q') in *.
assert (Hu2 : / 2 <= u) by nra.
assert (Hv2 : v <= 2) by nra.
(* [|u - v| = |Q - Q'| / (u + v) <= 2 eps], as [u >= 1/2]. *)
assert (Huv : Rabs (u - v) <= 2 * bpow radix2 (-102)).
{ assert (Hp : (u - v) * (u + v) = Q - Q') by (rewrite <- Hu, <- Hv; ring).
  assert (Hp2 : Rabs (u - v) * (u + v) <= bpow radix2 (-102)).
  { rewrite <- (Rabs_pos_eq (u + v)) by lra.
    rewrite <- Rabs_mult, Hp. apply Rabs_le. lra. }
  assert (Rabs (u - v) * / 2 <= Rabs (u - v) * (u + v))
    by (apply Rmult_le_compat_l; [apply Rabs_pos | lra]).
  lra. }
(* [|sh + sl - v| <= 2^-100 v <= 2^-99], so the total is at most
   [2 eps + 8 eps <= 16 eps]. *)
replace (u - (B2R sh + B2R sl)) with ((u - v) + (v - (B2R sh + B2R sl))) by ring.
eapply Rle_trans; [apply Rabs_triang|].
rewrite (Rabs_minus_sym v).
assert (Hv3 : bpow radix2 (-100) * v <= bpow radix2 (-100) * 2)
  by (apply Rmult_le_compat_l; [apply bpow_ge_0 | lra]).
lra.
Qed.

Theorem hypot_dd_fma :
  forall big small,
  is_finite big = true -> is_finite small = true ->
  0 < B2R small <= B2R big ->
  (Z.shiftr (to_bits big) 52 - Z.shiftr (to_bits small) 52 < 27)%Z ->
  DyadicRoot.hypot_dd true big small = DyadicRoot.hypot_dd false big small.
Proof.
intros big small Fb Fs Hsb Hg.
unfold DyadicRoot.hypot_dd. cbv zeta.
match goal with |- context [if ?c then _ else _] => destruct c eqn:Heb end;
  [reflexivity|].
apply Bool.orb_false_iff in Heb as (Heb0 & Heb1).
apply Z.eqb_neq in Heb0. apply Z.ltb_ge in Heb1.
set (eb := Z.shiftr (to_bits big) 52) in *.
set (sc := from_bits (Z.shiftl (2045 - eb) 52)) in *.
destruct (hypot_dd_scale big small Fb Fs Hsb Hg Heb0 Heb1 eb sc eq_refl eq_refl)
  as (_ & Fx & Fy & _ & _ & HX & HY).
set (x := mul big sc) in *. set (y := mul small sc) in *.
(* The squares' errors are the same [f64] with and without an FMA
   ([hypot_sum_sq_fma]), and so is the square root ([dd_sqrt_fma]). *)
destruct (hypot_sum_sq_fma x y Fx Fy HX HY) as (Ex & Ey).
rewrite Ex, Ey.
destruct (Fast.fast_two_sum (mul x x) (mul y y)) as (r2, e2) eqn:E1.
match goal with |- context [Fast.fast_two_sum r2 ?t] =>
  destruct (Fast.fast_two_sum r2 t) as (ah, al) eqn:E2 end.
destruct (hypot_sum_sq_correct false x y r2 e2 ah al Fx Fy HX HY E1 E2)
  as (Fah & Fal & Hah & _).
assert (Hah' : bpow radix2 (-900) <= B2R ah <= bpow radix2 900).
{ assert (B1 : bpow radix2 (-900) <= bpow radix2 (-3)) by (apply bpow_le; lia).
  assert (B2 : bpow radix2 2 <= bpow radix2 900) by (apply bpow_le; lia).
  change (bpow radix2 (-3)) with (/ 8) in B1. change (bpow radix2 2) with 4 in B2.
  lra. }
rewrite (dd_sqrt_fma ah al Fah Fal Hah').
reflexivity.
Qed.
