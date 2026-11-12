(** * The evaluation of the fast paths of [sin], [cos] and [tan] near the multiples of π/2

    For [rh + rl] within a relative 2^-74 of ρ, 2^-61 <= |ρ| <= π/8192
    (1 + 2^-24), [|rl| <= 2^-24 |rh|] and [rr = RN(rh + rl)] (what
    [FastTrigBandRed.v] and [FastTrigBandBig.v] give),
    [DyadicTrig.fast_band_sin rh rl rr] of [Model.v] is sin ρ within a
    relative 2^-71, with the Taylor polynomial of sin ρ - ρ to degree 5
    ([band_sin_correct]), [DyadicTrig.fast_cos0 rr] is cos ρ within a
    relative 2^-71 ([band_cos_correct]), [DyadicTrig.fast_band_eval q]
    is sin(q π/2 + ρ) within a relative 2^-71 ([band_eval_correct]), and
    [DyadicTrig.fast_band_tan false n] is tan(n π/4096 + ρ) for a multiple
    [n] of 2048 within a relative [3 * 2^-71] ([band_tan_correct]), with
    [h = RN(h + l)] and [2^-1000 <= |h| <= 2^1000], from the quotient of
    [FastTrigBandDiv.v]. The quotient is the same with an FMA
    ([band_tan_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr TwoSum TwoProduct FastRound FastExpErr FastExpTables
  TrigSeries FastTrigEval FastTrigDiv FastTrigBandDiv.
From Inari Require CancelLanes MulRuTiny PiBounds TrigPieces FastTrigSC.

Open Scope R_scope.

(** Powers of 2 as numerals, for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp] in *.

(** ** The premises *)

(** [rr], the rounding of [rh + rl], is within a relative [2^-52] of ρ,
    and both are below [3836e-7] in magnitude: the rounding errs by
    [2^-53 |rh + rl| + 2^-1075], and [2^-1075] is below [2^-1014 |ρ|]. *)
Local Lemma band_rr :
  forall (rh rl rr : f64) rho,
  B2R rr = RN (B2R rh + B2R rl) ->
  bpow radix2 (-61) <= Rabs rho <= PI / 8192 * (1 + bpow radix2 (-24)) ->
  Rabs (rho - (B2R rh + B2R rl)) <= bpow radix2 (-74) * Rabs rho ->
  Rabs (B2R rr - rho) <= bpow radix2 (-52) * Rabs rho /\
  Rabs (B2R rr) <= (1 + bpow radix2 (-52)) * Rabs rho /\
  Rabs (B2R rr) <= 3836e-7 /\ Rabs rho <= 3835e-7.
Proof.
intros rh rl rr rho Err Hr Hd.
pose proof (FastExpErr.rn_err (B2R rh + B2R rl)) as E. rewrite <- Err in E.
pose proof FastTrigEval.pi_M as [_ PM].
set (Y := B2R rh + B2R rl) in *. set (P := B2R rr) in *.
pose proof (Rabs_triang_inv Y rho) as T1. rewrite Rabs_minus_sym in T1.
pose proof (Rabs_triang (P - Y) (Y - rho)) as T2.
replace (P - Y + (Y - rho)) with (P - rho) in T2 by ring.
rewrite (Rabs_minus_sym Y rho) in T2.
pose proof (Rabs_triang_inv P rho) as T3.
num.
assert (D : Rabs (P - rho) <= / 4503599627370496 * Rabs rho) by lra.
split; [lra|]. split; [lra|]. split; lra.
Qed.

(** sin ρ is within a relative 1/100 of ρ, and cos ρ is between 0.999
    and 1, for |ρ| <= [3835e-7] (Taylor polynomials of degree 1 and 0). *)
Local Lemma band_mag :
  forall rho, Rabs rho <= 3835e-7 ->
  99 / 100 * Rabs rho <= Rabs (sin rho) <= 101 / 100 * Rabs rho /\
  999 / 1000 <= cos rho <= 1.
Proof.
intros rho H.
assert (H1 : Rabs rho <= 1) by lra.
destruct (FastTrigEval.sin_t3 rho H1) as (T & HT & Es).
destruct (FastTrigEval.cos_t2 rho H1) as (U & HU & Ec).
destruct (FastTrigEval.sq_le rho 3835e-7 H) as [A0 A1].
assert (A4 : 0 <= rho ^ 4 <= 3835e-7 * 3835e-7 * (3835e-7 * 3835e-7))
  by (replace (rho ^ 4) with (rho ^ 2 * rho ^ 2) by ring; split; nra).
assert (K : Rabs (- rho ^ 2 / 6 + T * (rho ^ 4 / 120)) <= / 100)
  by (apply Rabs_le; split; nra).
assert (D : Rabs (sin rho - rho) <= / 100 * Rabs rho).
{ replace (sin rho - rho) with (rho * (- rho ^ 2 / 6 + T * (rho ^ 4 / 120)))
    by (rewrite Es; field).
  rewrite Rabs_mult, Rmult_comm. apply Rmult_le_compat_r; [apply Rabs_pos | exact K]. }
pose proof (Rabs_triang_inv (sin rho) rho) as T1.
pose proof (Rabs_triang_inv rho (sin rho)) as T2. rewrite Rabs_minus_sym in T2.
pose proof (COS_bound rho) as [_ C1].
split; [split; lra |]. split; [| exact C1].
rewrite Ec. nra.
Qed.

(** A rounding [h = RN(y)] of a [y] within a relative [2^-60] of [v],
    for [a <= |v| <= b] and [2^-1070 <= a]: [|h|] lies in [[a / 2, 2 b]]. *)
Local Lemma pair_mag :
  forall h y v a b, bpow radix2 (-1070) <= a -> a <= Rabs v <= b ->
  h = RN y -> Rabs (y - v) <= bpow radix2 (-60) * Rabs v ->
  a / 2 <= Rabs h <= 2 * b.
Proof.
intros h y v a b Ha Hv Rh H.
pose proof (FastExpErr.rn_err y) as E. rewrite <- Rh in E.
pose proof (Rabs_triang_inv y v) as T1.
pose proof (Rabs_triang_inv v y) as T2. rewrite Rabs_minus_sym in T2.
pose proof (Rabs_triang_inv h y) as T3.
pose proof (Rabs_triang_inv y h) as T4. rewrite Rabs_minus_sym in T4.
num. split; lra.
Qed.

(** The negated pair of a pair near [v] is near [-v] (as [pair_opp] of
    [FastTrigCore.v], which imports this file). *)
Local Lemma band_opp :
  forall (h l : f64) v k,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  Rabs (B2R h + B2R l - v) <= k ->
  is_finite (opp h) = true /\ is_finite (opp l) = true /\
  B2R (opp h) = RN (B2R (opp h) + B2R (opp l)) /\ Rabs (B2R (opp h)) = Rabs (B2R h) /\
  Rabs (B2R (opp h) + B2R (opp l) - - v) <= k.
Proof.
intros h l v k Fh Fl Hrn Hy. unfold opp. rewrite !is_finite_Bopp, !B2R_Bopp.
split; [exact Fh |]. split; [exact Fl |]. split; [| split].
- rewrite <- Ropp_plus_distr, round_NE_opp, <- Hrn. reflexivity.
- apply Rabs_Ropp.
- replace (- B2R h + - B2R l - - v) with (- (B2R h + B2R l - v)) by ring.
  rewrite Rabs_Ropp. exact Hy.
Qed.

(** A pair near [v], or its negation by [b = false], is near [v] or [-v]
    (the last step of [fast_band_eval]). *)
Local Lemma band_out :
  forall (h l : f64) v (b : bool),
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  bpow radix2 (-1000) <= Rabs (B2R h) <= bpow radix2 1000 ->
  Rabs (B2R h + B2R l - v) <= bpow radix2 (-71) * Rabs v ->
  let w := if b then v else - v in
  let '(h', l') := if b then (h, l) else (opp h, opp l) in
  is_finite h' = true /\ is_finite l' = true /\ B2R h' = RN (B2R h' + B2R l') /\
  bpow radix2 (-1000) <= Rabs (B2R h') <= bpow radix2 1000 /\
  Rabs (w - (B2R h' + B2R l')) <= bpow radix2 (-71) * Rabs w.
Proof.
intros h l v b Fh Fl Rh Mh E. cbv zeta. destruct b.
- rewrite Rabs_minus_sym. tauto.
- destruct (band_opp h l v _ Fh Fl Rh E) as (Fh' & Fl' & Rh' & Ah & E').
  rewrite Rabs_minus_sym, Rabs_Ropp, Ah. tauto.
Qed.

(** ** sin ρ and cos ρ *)

Theorem band_sin_correct :
  forall (rh rl rr : f64) rho,
  is_finite rh = true -> is_finite rl = true -> is_finite rr = true ->
  B2R rr = RN (B2R rh + B2R rl) ->
  bpow radix2 (-61) <= Rabs rho <= PI / 8192 * (1 + bpow radix2 (-24)) ->
  Rabs (rho - (B2R rh + B2R rl)) <= bpow radix2 (-74) * Rabs rho ->
  Rabs (B2R rl) <= bpow radix2 (-24) * Rabs (B2R rh) ->
  let '(h, l) := DyadicTrig.fast_band_sin rh rl rr in
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  bpow radix2 (-1000) <= Rabs (B2R h) <= bpow radix2 1000 /\
  Rabs (B2R h + B2R l - sin rho) <= bpow radix2 (-71) * Rabs (sin rho).
Proof.
intros rh rl rr rho Frh Frl Frr Err Hr Hd Hrl.
destruct (band_rr rh rl rr rho Err Hr Hd) as (Dr & XR & Xr & Xrho).
destruct (band_mag rho Xrho) as ((S0 & S1) & _).
unfold DyadicTrig.fast_band_sin, Fast.fast_two_sum. cbv beta iota zeta.
set (X := Rabs (B2R rr)) in *.
assert (HX10 : X <= bpow radix2 (-10)) by (num; lra).
destruct (FastTrigEval.poly_s3 rr X Frr (Rle_refl _) HX10) as [Fs3 Bs3]. cbv zeta in Fs3, Bs3.
set (s3 := mul (mul rr (mul rr rr))
             (sub (mul (mul rr rr) (from_bits DyadicTrig.S5)) (from_bits DyadicTrig.S3))) in *.
pose proof (FastTrigEval.ps_mag (B2R rr) X (Rle_refl _) ltac:(num; lra)) as Pm.
assert (Xrho' : Rabs rho <= 3836e-7) by lra.
pose proof (FastTrigEval.ps_diff (B2R rr) rho 3836e-7 _ Xr Xrho' ltac:(lra) Dr) as Pd.
set (P := B2R rr) in *.
assert (X0 : 0 <= X) by apply Rabs_pos.
assert (X3 : X * X * X <= 15e-8 * X).
{ assert (X * X <= 15e-8) by nra. nra. }
replace (X ^ 3) with (X * X * X) in Bs3 by ring.
(* The Taylor polynomial of degree 5 of sin at ρ, within [|ρ|^7 / 5040]. *)
assert (HR1 : Rabs rho <= 1) by lra.
destruct (FastTrigEval.sin_t5 rho HR1) as (T & HT & Es).
destruct (FastTrigEval.sq_le rho 3835e-7 Xrho) as [A0 A1].
assert (B7 : Rabs (T * (rho ^ 7 / 5040)) <= 1e-24 * Rabs rho).
{ replace (T * (rho ^ 7 / 5040)) with (rho * (T * (rho ^ 2 * rho ^ 2 * rho ^ 2) / 5040))
    by field.
  rewrite Rabs_mult, Rmult_comm. apply Rmult_le_compat_r; [apply Rabs_pos |].
  assert (0 <= rho ^ 2 * rho ^ 2 <= 3835e-7 * 3835e-7 * (3835e-7 * 3835e-7)) by (split; nra).
  assert (0 <= rho ^ 2 * rho ^ 2 * rho ^ 2 <= 3835e-7 * 3835e-7 * (3835e-7 * 3835e-7) *
    (3835e-7 * 3835e-7)) by (split; nra).
  apply Rabs_le. split; nra. }
(* [|rh|] is within a relative [2^-23] of [|ρ|]. *)
set (Y := B2R rh + B2R rl) in *.
assert (EY : Y = B2R rh + B2R rl) by reflexivity.
pose proof (Rabs_triang_inv (B2R rh) (- B2R rl)) as T1. rewrite Rabs_Ropp in T1.
replace (B2R rh - - B2R rl) with Y in T1 by (unfold Y; ring).
pose proof (Rabs_triang (B2R rh) (B2R rl)) as T2. fold Y in T2.
pose proof (Rabs_triang_inv rho Y) as T3.
pose proof (Rabs_triang_inv Y rho) as T4. rewrite Rabs_minus_sym in T4.
assert (Hrh : Rabs (B2R rh) <= (1 + bpow radix2 (-23)) * Rabs rho) by (num; lra).
(* [s3] is at most [2^-25 |ρ|]: [|rr|^3 / 6 <= 2.5e-8 |rr|]. *)
pose proof (Rabs_triang_inv (B2R s3) (P ^ 3 * (P ^ 2 / 120 - / 6))) as T5.
assert (Hs3 : Rabs (B2R s3) <= bpow radix2 (-25) * Rabs rho) by (num; lra).
(* [rl + s3] is at most [2^-23 |ρ|]. *)
pose proof (Rabs_triang (B2R rl) (B2R s3)) as T6.
assert (Hls : Rabs (B2R rl + B2R s3) <= bpow radix2 (-23) * Rabs rho) by (num; lra).
assert (S16 : Rabs (B2R rl + B2R s3) <= 16) by (num; lra).
destruct (add_e rl s3 Frl Fs3 S16) as (Fl0 & El0 & Bl0).
set (l0 := add rl s3) in *.
(* [|l0| <= |rh|], for the fast two-sum. *)
pose proof (Rabs_triang_inv (B2R l0) (B2R rl + B2R s3)) as T7.
pose proof (Rabs_triang_inv (B2R rh) (- B2R rl)) as T1'. rewrite Rabs_Ropp in T1'.
assert (Hrh' : (1 - bpow radix2 (-23)) * Rabs rho <= Rabs (B2R rh)) by (num; lra).
assert (Hle : Rabs (B2R l0) <= Rabs (B2R rh)) by (num; lra).
pose proof (Rabs_triang (B2R rh) (B2R l0)) as T8.
assert (S16' : Rabs (B2R rh + B2R l0) <= 16) by (num; lra).
destruct (add_e rh l0 Frh Fl0 S16') as (Fh & Eh & _).
destruct (CancelLanes.fast_two_sum rh l0 (add rh l0) Frh Fl0 Hle Fh Eh) as (Fl & El).
split; [exact Fh|]. split; [exact Fl|].
rewrite El.
replace (B2R (add rh l0) + (B2R rh + B2R l0 - B2R (add rh l0))) with (B2R rh + B2R l0)
  by ring.
split; [exact Eh|].
(* [rh + l0 - sin ρ] is [(Y - ρ) + (l0 - (rl + s3)) + (s3 - ps(rr)) +
   (ps(rr) - ps(ρ))] plus the Taylor remainder, at most [2^-72.8 |ρ|]. *)
assert (Er : Rabs (B2R rh + B2R l0 - sin rho) <= bpow radix2 (-71) * Rabs (sin rho)).
{ apply Rabs_le_inv in Hd, Bl0, Bs3, Pd, B7. apply Rabs_le. num. split; lra. }
split; [| exact Er].
assert (Er' : Rabs (B2R rh + B2R l0 - sin rho) <= bpow radix2 (-60) * Rabs (sin rho))
  by (num; lra).
assert (Ha : bpow radix2 (-1070) <= 99 / 100 * bpow radix2 (-61)) by (num; lra).
assert (Hs : 99 / 100 * bpow radix2 (-61) <= Rabs (sin rho) <= 1) by (num; lra).
destruct (pair_mag _ _ _ _ 1 Ha Hs Eh Er') as [H0 H1].
num. split; lra.
Qed.

Theorem band_cos_correct :
  forall (rh rl rr : f64) rho,
  is_finite rh = true -> is_finite rl = true -> is_finite rr = true ->
  B2R rr = RN (B2R rh + B2R rl) ->
  bpow radix2 (-61) <= Rabs rho <= PI / 8192 * (1 + bpow radix2 (-24)) ->
  Rabs (rho - (B2R rh + B2R rl)) <= bpow radix2 (-74) * Rabs rho ->
  Rabs (B2R rl) <= bpow radix2 (-24) * Rabs (B2R rh) ->
  let '(h, l) := DyadicTrig.fast_cos0 rr in
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  bpow radix2 (-1000) <= Rabs (B2R h) <= bpow radix2 1000 /\
  Rabs (B2R h + B2R l - cos rho) <= bpow radix2 (-71) * Rabs (cos rho).
Proof.
intros rh rl rr rho Frh Frl Frr Err Hr Hd Hrl.
destruct (band_rr rh rl rr rho Err Hr Hd) as (Dr & _ & Xr & Xrho).
destruct (band_mag rho Xrho) as (_ & C0 & C1).
unfold DyadicTrig.fast_cos0, Fast.fast_two_sum. cbv beta iota zeta.
assert (HX10 : 3836e-7 <= bpow radix2 (-10)) by (num; lra).
destruct (FastTrigEval.poly_cm rr 3836e-7 Frr Xr HX10) as [Fcm Bcm]. cbv zeta in Fcm, Bcm.
set (cm := mul (mul rr rr) (sub (mul (mul rr rr) (from_bits DyadicTrig.C4)) half)) in *.
set (P := B2R rr) in *.
(* The Taylor polynomial of degree 4 of cos at ρ, within [ρ^6 / 720]. *)
assert (HR1 : Rabs rho <= 1) by lra.
destruct (FastTrigEval.cos_t4 rho HR1) as (T & HT & Ec).
destruct (FastTrigEval.sq_le rho 3835e-7 Xrho) as [A0 A1].
assert (B6 : 0 <= T * (rho ^ 6 / 720) <= 5e-24).
{ replace (T * (rho ^ 6 / 720)) with (T * (rho ^ 2 * rho ^ 2 * rho ^ 2) / 720) by field.
  assert (0 <= rho ^ 2 * rho ^ 2 <= 3835e-7 * 3835e-7 * (3835e-7 * 3835e-7)) by (split; nra).
  assert (0 <= rho ^ 2 * rho ^ 2 * rho ^ 2 <= 3835e-7 * 3835e-7 * (3835e-7 * 3835e-7) *
    (3835e-7 * 3835e-7)) by (split; nra).
  split; nra. }
(* The polynomial at [rr] against the one at ρ, with [|rr - ρ| <= 2^-52 |ρ|]. *)
assert (Xrho' : Rabs rho <= 3836e-7) by lra.
pose proof (FastTrigEval.pc_diff P rho 3836e-7 _ Xr Xrho' ltac:(lra) Dr) as Pd.
pose proof (FastTrigEval.pc_mag P 3836e-7 Xr ltac:(lra)) as Pm.
apply Rabs_le_inv in Bcm, Pd, Pm.
destruct FastTrigEval.one_F as (F1 & E1).
(* [1 + cm] is a float sum within [16], and [|cm| <= 1]. *)
assert (Cm : Rabs (B2R cm) <= / 1000) by (apply Rabs_le; num; lra).
assert (S16 : Rabs (B2R Fast.one + B2R cm) <= 16)
  by (rewrite E1; apply Rabs_le; apply Rabs_le_inv in Cm; lra).
destruct (add_e Fast.one cm F1 Fcm S16) as (Fh & Eh & Bh).
assert (Hle : Rabs (B2R cm) <= Rabs (B2R Fast.one)) by (rewrite E1, Rabs_R1; lra).
destruct (CancelLanes.fast_two_sum Fast.one cm (add Fast.one cm) F1 Fcm Hle Fh Eh)
  as (Fl & El).
split; [exact Fh|]. split; [exact Fl|].
rewrite El.
replace (B2R (add Fast.one cm) + (B2R Fast.one + B2R cm - B2R (add Fast.one cm)))
  with (B2R Fast.one + B2R cm) by ring.
split; [exact Eh|].
rewrite E1 in Bh |- *. rewrite (Rabs_pos_eq (cos rho)) by lra.
split.
- (* [h] is [1 + cm] within [2^-52], so near 1. *)
  apply Rabs_le_inv in Cm.
  rewrite (Rabs_pos_eq (1 + B2R cm)) in Bh by lra.
  apply Rabs_le_inv in Bh.
  rewrite Rabs_pos_eq by (num; lra).
  num. split; lra.
- (* [1 + cm - cos ρ] is [(cm - pc(rr)) + (pc(rr) - pc(ρ))] plus the
     Taylor remainder. *)
  apply Rabs_le. num. split; lra.
Qed.

(** ** sin(q π/2 + ρ), as [sin_quad] of [FastTrigCore.v] splits it *)

Theorem band_eval_correct :
  forall q (rh rl rr : f64) rho,
  is_finite rh = true -> is_finite rl = true -> is_finite rr = true ->
  B2R rr = RN (B2R rh + B2R rl) ->
  bpow radix2 (-61) <= Rabs rho <= PI / 8192 * (1 + bpow radix2 (-24)) ->
  Rabs (rho - (B2R rh + B2R rl)) <= bpow radix2 (-74) * Rabs rho ->
  Rabs (B2R rl) <= bpow radix2 (-24) * Rabs (B2R rh) ->
  let w := if (Z.land q 1 =? 0)%Z then (if (Z.land q 2 =? 0)%Z then sin rho else - sin rho)
           else (if (Z.land q 2 =? 0)%Z then cos rho else - cos rho) in
  let '(h, l) := DyadicTrig.fast_band_eval q rh rl rr in
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  bpow radix2 (-1000) <= Rabs (B2R h) <= bpow radix2 1000 /\
  Rabs (w - (B2R h + B2R l)) <= bpow radix2 (-71) * Rabs w.
Proof.
intros q rh rl rr rho Frh Frl Frr Err Hr Hd Hrl. cbv zeta.
unfold DyadicTrig.fast_band_eval.
destruct (Z.land q 1 =? 0)%Z.
- generalize (band_sin_correct rh rl rr rho Frh Frl Frr Err Hr Hd Hrl).
  destruct (DyadicTrig.fast_band_sin rh rl rr) as [h l].
  intros (Fh & Fl & Rh & Mh & E).
  exact (band_out h l (sin rho) (Z.land q 2 =? 0)%Z Fh Fl Rh Mh E).
- generalize (band_cos_correct rh rl rr rho Frh Frl Frr Err Hr Hd Hrl).
  destruct (DyadicTrig.fast_cos0 rr) as [h l].
  intros (Fh & Fl & Rh & Mh & E).
  exact (band_out h l (cos rho) (Z.land q 2 =? 0)%Z Fh Fl Rh Mh E).
Qed.

(** ** tan(q π/2 + ρ), as [tan_quad] of [FastTrigCore.v] splits it *)

(** The quotient of [FastTrigBandDiv.v], with [|n / d|] in
    [[2^-64, 2^64]], so its [h] lies in [[2^-65, 2^65]] by [pair_mag]. *)
Local Lemma band_quot :
  forall nh nl dh dl n d,
  is_finite nh = true -> is_finite nl = true -> is_finite dh = true -> is_finite dl = true ->
  B2R nh = RN (B2R nh + B2R nl) -> B2R dh = RN (B2R dh + B2R dl) ->
  bpow radix2 (-64) <= Rabs n <= 1 -> bpow radix2 (-64) <= Rabs d <= 1 ->
  Rabs (B2R nh + B2R nl - n) <= bpow radix2 (-71) * Rabs n ->
  Rabs (B2R dh + B2R dl - d) <= bpow radix2 (-71) * Rabs d ->
  let '(h, l) := DyadicTrig.fast_div false nh nl dh dl in
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  bpow radix2 (-1000) <= Rabs (B2R h) <= bpow radix2 1000 /\
  Rabs (B2R h + B2R l - n / d) <= 3 * bpow radix2 (-71) * Rabs (n / d).
Proof.
intros nh nl dh dl n d Fnh Fnl Fdh Fdl Rnh Rdh Hn Hd HN HD.
generalize (band_div_correct nh nl dh dl n d Fnh Fnl Fdh Fdl Rnh Rdh Hn Hd HN HD).
destruct (DyadicTrig.fast_div false nh nl dh dl) as [h l].
intros (Fh & Fl & Rh & E).
(* [|n / d| = |n| / |d|], with [1 <= 1 / |d| <= 2^64]. *)
assert (Q : bpow radix2 (-64) <= Rabs (n / d) <= bpow radix2 64).
{ pose proof (bpow_gt_0 radix2 (-64)) as P64.
  assert (D0 : 0 < Rabs d) by lra.
  unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
  pose proof (Rinv_r (Rabs d) ltac:(lra)) as Id.
  pose proof (Rinv_0_lt_compat (Rabs d) D0) as I0.
  set (i := / Rabs d) in *.
  assert (I1 : 1 <= i) by nra.
  assert (I2 : i <= bpow radix2 64) by (num; nra).
  split; nra. }
assert (E' : Rabs (B2R h + B2R l - n / d) <= bpow radix2 (-60) * Rabs (n / d)) by (num; lra).
assert (Ha : bpow radix2 (-1070) <= bpow radix2 (-64)) by (num; lra).
destruct (pair_mag (B2R h) _ (n / d) _ _ Ha Q Rh E') as [H0 H1].
split; [exact Fh |]. split; [exact Fl |]. split; [exact Rh |]. split; [| exact E].
num. split; lra.
Qed.

Theorem band_tan_correct :
  forall n (rh rl rr : f64) rho,
  is_finite rh = true -> is_finite rl = true -> is_finite rr = true ->
  B2R rr = RN (B2R rh + B2R rl) ->
  bpow radix2 (-61) <= Rabs rho <= PI / 8192 * (1 + bpow radix2 (-24)) ->
  Rabs (rho - (B2R rh + B2R rl)) <= bpow radix2 (-74) * Rabs rho ->
  Rabs (B2R rl) <= bpow radix2 (-24) * Rabs (B2R rh) ->
  let w := if (Z.land n 2048 =? 0)%Z then sin rho / cos rho else - (cos rho / sin rho) in
  let '(h, l) := DyadicTrig.fast_band_tan false n rh rl rr in
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  bpow radix2 (-1000) <= Rabs (B2R h) <= bpow radix2 1000 /\
  Rabs (w - (B2R h + B2R l)) <= 3 * bpow radix2 (-71) * Rabs w.
Proof.
intros n rh rl rr rho Frh Frl Frr Err Hr Hd Hrl. cbv zeta.
destruct (band_rr rh rl rr rho Err Hr Hd) as (_ & _ & _ & Xrho).
destruct (band_mag rho Xrho) as ((S0 & S1) & C0 & C1).
(* sin ρ and cos ρ lie in [[2^-64, 1]] in magnitude. *)
assert (Hs : bpow radix2 (-64) <= Rabs (sin rho) <= 1) by (num; lra).
assert (Hc : bpow radix2 (-64) <= Rabs (cos rho) <= 1)
  by (rewrite Rabs_pos_eq by lra; num; lra).
generalize (band_sin_correct rh rl rr rho Frh Frl Frr Err Hr Hd Hrl).
generalize (band_cos_correct rh rl rr rho Frh Frl Frr Err Hr Hd Hrl).
unfold DyadicTrig.fast_band_tan.
destruct (DyadicTrig.fast_band_sin rh rl rr) as [sh sl].
destruct (DyadicTrig.fast_cos0 rr) as [ch cl].
intros (Fch & Fcl & Rch & _ & Ec) (Fsh & Fsl & Rsh & _ & Es).
destruct (Z.land n 2048 =? 0)%Z.
- generalize (band_quot sh sl ch cl (sin rho) (cos rho) Fsh Fsl Fch Fcl Rsh Rch Hs Hc Es Ec).
  destruct (DyadicTrig.fast_div false sh sl ch cl) as [h l].
  intros (Fh & Fl & Rh & Mh & E).
  rewrite Rabs_minus_sym. tauto.
- generalize (band_quot ch cl sh sl (cos rho) (sin rho) Fch Fcl Fsh Fsl Rch Rsh Hc Hs Ec Es).
  destruct (DyadicTrig.fast_div false ch cl sh sl) as [h l].
  intros (Fh & Fl & Rh & Mh & E).
  destruct (band_opp h l (cos rho / sin rho) _ Fh Fl Rh E) as (Fh' & Fl' & Rh' & Ah & E').
  rewrite Rabs_minus_sym, Rabs_Ropp, Ah. tauto.
Qed.

Theorem band_tan_fma :
  forall n (rh rl rr : f64) rho,
  is_finite rh = true -> is_finite rl = true -> is_finite rr = true ->
  B2R rr = RN (B2R rh + B2R rl) ->
  bpow radix2 (-61) <= Rabs rho <= PI / 8192 * (1 + bpow radix2 (-24)) ->
  Rabs (rho - (B2R rh + B2R rl)) <= bpow radix2 (-74) * Rabs rho ->
  Rabs (B2R rl) <= bpow radix2 (-24) * Rabs (B2R rh) ->
  DyadicTrig.fast_band_tan true n rh rl rr = DyadicTrig.fast_band_tan false n rh rl rr.
Proof.
intros n rh rl rr rho Frh Frl Frr Err Hr Hd Hrl.
destruct (band_rr rh rl rr rho Err Hr Hd) as (_ & _ & _ & Xrho).
destruct (band_mag rho Xrho) as ((S0 & S1) & C0 & C1).
assert (Hs : bpow radix2 (-64) <= Rabs (sin rho) <= 1) by (num; lra).
assert (Hc : bpow radix2 (-64) <= Rabs (cos rho) <= 1)
  by (rewrite Rabs_pos_eq by lra; num; lra).
assert (Ha : bpow radix2 (-1070) <= bpow radix2 (-64)) by (num; lra).
generalize (band_sin_correct rh rl rr rho Frh Frl Frr Err Hr Hd Hrl).
generalize (band_cos_correct rh rl rr rho Frh Frl Frr Err Hr Hd Hrl).
unfold DyadicTrig.fast_band_tan.
destruct (DyadicTrig.fast_band_sin rh rl rr) as [sh sl].
destruct (DyadicTrig.fast_cos0 rr) as [ch cl].
intros (Fch & _ & Rch & _ & Ec) (Fsh & _ & Rsh & _ & Es).
(* The leading parts lie in [[2^-65, 2]] in magnitude, by [pair_mag]. *)
assert (Es' : Rabs (B2R sh + B2R sl - sin rho) <= bpow radix2 (-60) * Rabs (sin rho))
  by (num; lra).
assert (Ec' : Rabs (B2R ch + B2R cl - cos rho) <= bpow radix2 (-60) * Rabs (cos rho))
  by (num; lra).
destruct (pair_mag (B2R sh) _ (sin rho) _ _ Ha Hs Rsh Es') as [Ms0 Ms1].
destruct (pair_mag (B2R ch) _ (cos rho) _ _ Ha Hc Rch Ec') as [Mc0 Mc1].
assert (Ms : bpow radix2 (-65) <= Rabs (B2R sh) <= 2) by (num; lra).
assert (Mc : bpow radix2 (-65) <= Rabs (B2R ch) <= 2) by (num; lra).
destruct (Z.land n 2048 =? 0)%Z.
- exact (band_div_fma sh sl ch cl Fsh Fch Ms Mc).
- rewrite (band_div_fma ch cl sh sl Fch Fsh Mc Ms). reflexivity.
Qed.
