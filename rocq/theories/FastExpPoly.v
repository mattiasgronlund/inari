(** * The polynomial of the fast path of [exp]

    After the reduction of [FastExpReduce.v], [DyadicExp.fast_exp]
    evaluates [e^(rh + rl)] as [s + pl], where [(s, t)] is the Fast2Sum
    [Dekker] of [1] and [rh], and [pl] adds [t], [rl] and the Taylor
    polynomial [q] of degree 4 without its terms of degree 0 and 1, in
    Horner's scheme on [rr = rh + rl] rounded ([fast_exp_poly]).

    [Dekker] T. J. Dekker, A floating-point technique for extending the
    available precision, Numer. Math. 18 (1971). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Relative.
From Inari Require Import Model Encoding Elementary TwoSum TwoProduct CancelLanes ExpSeries
  FastExpTables FastExpErr.

Open Scope R_scope.

(** [B2R l] of an [f64] literal [l], as [m * 2^e] (as in [FastExp.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** Powers of 2 as numerals, for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp] in *.

Local Lemma one_F : is_finite DyadicExp.one = true /\ B2R DyadicExp.one = 1.
Proof.
split; [vm_compute; reflexivity|]. lit_B2R. cbn [bpow radix_val radix2]. lra.
Qed.

Local Lemma half_F : is_finite half = true /\ B2R half = / 2.
Proof.
split; [vm_compute; reflexivity|]. lit_B2R. cbn [bpow radix_val radix2]. lra.
Qed.

(** [s = 1 + rh] rounded and [1 + rh - s]: [s] within [2^-53 (1 +
    3 * 2^-15) + 2^-1075] of [1 + rh]. *)
Local Lemma s_err :
  forall rh,
  is_finite rh = true -> Rabs (B2R rh) <= 3 * bpow radix2 (-15) ->
  is_finite (add DyadicExp.one rh) = true /\
  B2R (add DyadicExp.one rh) = RN (1 + B2R rh) /\
  Rabs (B2R (add DyadicExp.one rh) - (1 + B2R rh)) <=
    bpow radix2 (-53) * (1 + 3 * bpow radix2 (-15)) + bpow radix2 (-1075).
Proof.
intros rh Frh Hrh.
destruct one_F as (F1 & E1).
assert (HK : Rabs (B2R DyadicExp.one + B2R rh) <= 1 + 3 * bpow radix2 (-15)).
{ rewrite E1. apply Rabs_le_inv in Hrh. apply Rabs_le. lra. }
assert (HK16 : 1 + 3 * bpow radix2 (-15) <= 16) by (num; lra).
destruct (add_k DyadicExp.one rh _ F1 Frh HK HK16) as (Fs & Es & Bs).
rewrite E1 in Es, Bs. auto.
Qed.

(** [s = 1 + rh] rounded is finite and within [2^-13] of 1. *)
Lemma fast_exp_s :
  forall rh,
  is_finite rh = true -> Rabs (B2R rh) <= 3 * bpow radix2 (-15) ->
  is_finite (add DyadicExp.one rh) = true /\
  Rabs (B2R (add DyadicExp.one rh) - 1) <= bpow radix2 (-13).
Proof.
intros rh Frh Hrh.
destruct (s_err rh Frh Hrh) as (Fs & _ & Bs).
split; [exact Fs|].
apply Rabs_le_inv in Bs, Hrh. apply Rabs_le. num. lra.
Qed.

(** [add_k] and [mul_k] for a named result [z], with the error as two
    inequalities for [lra]. *)
Local Lemma add_kz :
  forall x y z K, z = add x y -> is_finite x = true -> is_finite y = true ->
  Rabs (B2R x + B2R y) <= K -> K <= 16 ->
  is_finite z = true /\
  - (bpow radix2 (-53) * K + bpow radix2 (-1075)) <= B2R z - (B2R x + B2R y) <=
    bpow radix2 (-53) * K + bpow radix2 (-1075).
Proof.
intros x y z K -> Fx Fy H HK.
destruct (add_k x y K Fx Fy H HK) as (F & _ & B).
split; [exact F | apply Rabs_le_inv; exact B].
Qed.

Local Lemma mul_kz :
  forall x y z K, z = mul x y -> is_finite x = true -> is_finite y = true ->
  Rabs (B2R x * B2R y) <= K -> K <= 16 ->
  is_finite z = true /\
  - (bpow radix2 (-53) * K + bpow radix2 (-1075)) <= B2R z - B2R x * B2R y <=
    bpow radix2 (-53) * K + bpow radix2 (-1075).
Proof.
intros x y z K -> Fx Fy H HK.
destruct (mul_k x y K Fx Fy H HK) as (F & _ & B).
split; [exact F | apply Rabs_le_inv; exact B].
Qed.

(** [s + pl] is [e^(rh + rl)] within [2^-71]. *)
Lemma fast_exp_poly :
  forall rh rl,
  is_finite rh = true -> is_finite rl = true ->
  Rabs (B2R rh) <= 3 * bpow radix2 (-15) -> Rabs (B2R rl) <= bpow radix2 (-20) ->
  let rr := add rh rl in
  let q := mul (mul rr rr)
    (add half (mul rr (add (from_bits DyadicExp.P3) (mul rr (from_bits DyadicExp.P4))))) in
  let s := add DyadicExp.one rh in
  let t := add rh (sub DyadicExp.one s) in
  let pl := add (add t rl) q in
  is_finite s = true /\ is_finite pl = true /\
  Rabs (B2R s - 1) <= bpow radix2 (-13) /\
  Rabs (B2R pl) <= bpow radix2 (-20) + bpow radix2 (-25) /\
  Rabs (B2R s + B2R pl - 1) <= 25 * bpow radix2 (-18) /\
  Rabs (exp (B2R rh + B2R rl) - (B2R s + B2R pl)) <= bpow radix2 (-71).
Proof.
intros rh rl Frh Frl Hrh Hrl. cbv zeta.
set (rr := add rh rl).
set (v1 := mul rr (from_bits DyadicExp.P4)).
set (v2 := add (from_bits DyadicExp.P3) v1).
set (v3 := mul rr v2).
set (v4 := add half v3).
set (v5 := mul rr rr).
set (q := mul v5 v4).
set (s := add DyadicExp.one rh).
set (t := add rh (sub DyadicExp.one s)).
set (a := add t rl).
set (pl := add a q).
destruct one_F as (F1 & E1).
destruct half_F as (Fh & Eh).
assert (F3 : is_finite (from_bits DyadicExp.P3) = true) by (vm_compute; reflexivity).
assert (F4 : is_finite (from_bits DyadicExp.P4) = true) by (vm_compute; reflexivity).
pose proof (Rabs_le_inv _ _ p3_correct) as H3.
pose proof (Rabs_le_inv _ _ p4_correct) as H4.
pose proof (Rabs_le_inv _ _ Hrh) as Hy.
pose proof (Rabs_le_inv _ _ Hrl) as Hz.
(* [s = 1 + rh] rounded, and [t = 1 + rh - s] exactly (Fast2Sum [Dekker],
   as [|rh| <= 1]). *)
destruct (s_err rh Frh Hrh) as (Fs & Es & Bs).
change (add DyadicExp.one rh) with s in Fs, Es, Bs.
assert (Es1 : B2R s = RN (B2R DyadicExp.one + B2R rh)) by (rewrite E1; exact Es).
assert (Hle : Rabs (B2R rh) <= Rabs (B2R DyadicExp.one))
  by (rewrite E1, Rabs_R1; num; lra).
destruct (fast_two_sum DyadicExp.one rh s F1 Frh Hle Fs Es1) as (Ft & Et).
change (add rh (sub DyadicExp.one s)) with t in Ft, Et.
apply Rabs_le_inv in Bs.
(* [rr = rh + rl] rounded, [|rr| <= X = 25 * 2^-18]; [R = rh + rl]. *)
assert (HR : Rabs (B2R rh + B2R rl) <= 3 * bpow radix2 (-15) + bpow radix2 (-20))
  by (apply Rabs_le; lra).
destruct (add_kz rh rl rr _ eq_refl Frh Frl HR ltac:(num; lra)) as (Frr & Brr).
assert (Hx : Rabs (B2R rr) <= 25 * bpow radix2 (-18)) by (apply Rabs_le; num; lra).
pose proof (Rabs_le_inv _ _ Hx) as Hx2.
(* [v1 = rr P4] rounded is [rr / 24] within [2^-69]. *)
assert (H14 : Rabs (B2R (from_bits DyadicExp.P4)) <= / 16) by (apply Rabs_le; num; lra).
assert (Hm1 : Rabs (B2R rr * B2R (from_bits DyadicExp.P4)) <= 25 * bpow radix2 (-18) * / 16)
  by (apply Rabs_mul_le; assumption).
destruct (mul_kz rr (from_bits DyadicExp.P4) v1 _ eq_refl Frr F4 Hm1 ltac:(num; lra))
  as (Fv1 & B1).
assert (Hd1 : Rabs (B2R rr * (B2R (from_bits DyadicExp.P4) - / 24)) <=
              25 * bpow radix2 (-18) * bpow radix2 (-58))
  by (apply Rabs_mul_le; [exact Hx | exact p4_correct]).
apply Rabs_le_inv in Hd1.
assert (C1 : - bpow radix2 (-69) <= B2R v1 - B2R rr / 24 <= bpow radix2 (-69))
  by (num; lra).
assert (W1 : Rabs (B2R v1) <= bpow radix2 (-17)) by (apply Rabs_le; num; lra).
(* [v2 = P3 + v1] rounded is [1/6 + rr/24] within [2^-54]. *)
assert (H2s : Rabs (B2R (from_bits DyadicExp.P3) + B2R v1) <= / 5)
  by (apply Rabs_le; apply Rabs_le_inv in W1; num; lra).
destruct (add_kz (from_bits DyadicExp.P3) v1 v2 _ eq_refl F3 Fv1 H2s ltac:(lra))
  as (Fv2 & B2).
assert (C2 : - bpow radix2 (-54) <= B2R v2 - (/ 6 + B2R rr / 24) <= bpow radix2 (-54))
  by (num; lra).
assert (W2 : Rabs (B2R v2) <= / 5) by (apply Rabs_le; num; lra).
(* [v3 = rr v2] rounded is [rr/6 + rr^2/24] within [2^-66]. *)
assert (Hm3 : Rabs (B2R rr * B2R v2) <= 25 * bpow radix2 (-18) * / 5)
  by (apply Rabs_mul_le; assumption).
destruct (mul_kz rr v2 v3 _ eq_refl Frr Fv2 Hm3 ltac:(num; lra)) as (Fv3 & B3).
assert (Hd3 : Rabs (B2R rr * (B2R v2 - (/ 6 + B2R rr / 24))) <=
              25 * bpow radix2 (-18) * bpow radix2 (-54))
  by (apply Rabs_mul_le; [exact Hx | apply Rabs_le; exact C2]).
apply Rabs_le_inv in Hd3, Hm3.
assert (C3 : - bpow radix2 (-66) <= B2R v3 - (B2R rr / 6 + B2R rr * B2R rr / 24) <=
             bpow radix2 (-66))
  by (num; lra).
assert (W3 : Rabs (B2R v3) <= bpow radix2 (-15)) by (apply Rabs_le; num; lra).
(* [v4 = 1/2 + v3] rounded is [W = 1/2 + rr/6 + rr^2/24] within [2^-53]. *)
assert (H4s : Rabs (B2R half + B2R v3) <= / 2 + bpow radix2 (-15))
  by (apply Rabs_le; apply Rabs_le_inv in W3; lra).
destruct (add_kz half v3 v4 _ eq_refl Fh Fv3 H4s ltac:(num; lra)) as (Fv4 & B4).
assert (C4 : - bpow radix2 (-53) <= B2R v4 - (/ 2 + B2R rr / 6 + B2R rr * B2R rr / 24) <=
             bpow radix2 (-53))
  by (num; lra).
assert (W4 : Rabs (B2R v4) <= / 2 + bpow radix2 (-14)) by (apply Rabs_le; num; lra).
(* [v5 = rr^2] rounded. *)
assert (Hm5 : Rabs (B2R rr * B2R rr) <= 25 * bpow radix2 (-18) * (25 * bpow radix2 (-18)))
  by (apply Rabs_mul_le; assumption).
destruct (mul_kz rr rr v5 _ eq_refl Frr Frr Hm5 ltac:(num; lra)) as (Fv5 & B5).
pose proof (Rabs_le_inv _ _ Hm5) as Hm52.
assert (W5 : Rabs (B2R v5) <= bpow radix2 (-26)) by (apply Rabs_le; num; lra).
(* [q = v5 v4] rounded is [Q(rr) = rr^2 W] within [2^-77]. *)
assert (Hmq : Rabs (B2R v5 * B2R v4) <= bpow radix2 (-26) * (/ 2 + bpow radix2 (-14)))
  by (apply Rabs_mul_le; assumption).
destruct (mul_kz v5 v4 q _ eq_refl Fv5 Fv4 Hmq ltac:(num; lra)) as (Fq & Bq).
assert (Hq1 : Rabs ((B2R v5 - B2R rr * B2R rr) * B2R v4) <=
              (bpow radix2 (-53) * (25 * bpow radix2 (-18) * (25 * bpow radix2 (-18)))
               + bpow radix2 (-1075)) * (/ 2 + bpow radix2 (-14)))
  by (apply Rabs_mul_le; [apply Rabs_le; exact B5 | exact W4]).
assert (Hq2 : Rabs (B2R rr * B2R rr * (B2R v4 - (/ 2 + B2R rr / 6 + B2R rr * B2R rr / 24))) <=
              25 * bpow radix2 (-18) * (25 * bpow radix2 (-18)) * bpow radix2 (-53))
  by (apply Rabs_mul_le; [exact Hm5 | apply Rabs_le; exact C4]).
apply Rabs_le_inv in Hq1, Hq2, Hmq.
assert (CQ : - bpow radix2 (-77) <=
             B2R q - B2R rr * B2R rr * (/ 2 + B2R rr / 6 + B2R rr * B2R rr / 24) <=
             bpow radix2 (-77))
  by (num; lra).
assert (WQ : Rabs (B2R q) <= bpow radix2 (-26)) by (apply Rabs_le; num; lra).
(* [a = t + rl] rounded and [pl = a + q] rounded. *)
assert (HA : Rabs (B2R t + B2R rl) <= bpow radix2 (-20) + bpow radix2 (-52))
  by (apply Rabs_le; num; lra).
destruct (add_kz t rl a _ eq_refl Ft Frl HA ltac:(num; lra)) as (Fa & Ba).
assert (HP : Rabs (B2R a + B2R q) <=
             bpow radix2 (-20) + bpow radix2 (-26) + bpow radix2 (-51))
  by (apply Rabs_le; apply Rabs_le_inv in WQ; num; lra).
destruct (add_kz a q pl _ eq_refl Fa Fq HP ltac:(num; lra)) as (Fpl & Bpl).
split; [exact Fs|]. split; [exact Fpl|].
split; [apply Rabs_le; num; lra|].
split; [apply Rabs_le; num; lra|].
split; [apply Rabs_le; num; lra|].
(* [Q(rr) - Q(R) = (rr - R) M] with [|M| <= 2^-13]. *)
set (R := B2R rh + B2R rl) in *.
assert (ER : R = B2R rh + B2R rl) by reflexivity.
assert (HRX : Rabs R <= 25 * bpow radix2 (-18)) by (apply Rabs_le; apply Rabs_le_inv in HR; num; lra).
pose proof (Rabs_le_inv _ _ HRX) as HRX2.
assert (Hb : Rabs (B2R rr * R) <= 25 * bpow radix2 (-18) * (25 * bpow radix2 (-18)))
  by (apply Rabs_mul_le; assumption).
assert (Hc : Rabs (R * R) <= 25 * bpow radix2 (-18) * (25 * bpow radix2 (-18)))
  by (apply Rabs_mul_le; assumption).
apply Rabs_le_inv in Hb, Hc.
assert (Hd : Rabs ((B2R rr + R) * (B2R rr * B2R rr + R * R)) <=
             (2 * (25 * bpow radix2 (-18))) *
             (2 * (25 * bpow radix2 (-18) * (25 * bpow radix2 (-18)))))
  by (apply Rabs_mul_le; apply Rabs_le; lra).
apply Rabs_le_inv in Hd.
set (M := (B2R rr + R) / 2 + (B2R rr * B2R rr + B2R rr * R + R * R) / 6
          + (B2R rr + R) * (B2R rr * B2R rr + R * R) / 24).
assert (HM : Rabs M <= bpow radix2 (-13)) by (apply Rabs_le; unfold M; num; lra).
assert (HQM : Rabs ((B2R rr - R) * M) <=
              (bpow radix2 (-53) * (3 * bpow radix2 (-15) + bpow radix2 (-20))
               + bpow radix2 (-1075)) * bpow radix2 (-13))
  by (apply Rabs_mul_le; [apply Rabs_le; exact Brr | exact HM]).
apply Rabs_le_inv in HQM.
assert (EM : B2R rr * B2R rr * (/ 2 + B2R rr / 6 + B2R rr * B2R rr / 24)
             - R * R * (/ 2 + R / 6 + R * R / 24) = (B2R rr - R) * M)
  by (unfold M; field).
(* Taylor at [R]: within [|R|^5 / 100]. *)
assert (HR1 : Rabs R <= / 1024) by (eapply Rle_trans; [exact HR | num; lra]).
pose proof (exp_taylor4 R HR1) as HT.
assert (HT5 : Rabs R ^ 5 <= (3 * bpow radix2 (-15) + bpow radix2 (-20)) ^ 5)
  by (apply pow_incr; split; [apply Rabs_pos | exact HR]).
apply Rabs_le_inv in HT.
replace (1 + R + R ^ 2 / 2 + R ^ 3 / 6 + R ^ 4 / 24)
  with (1 + R + R * R * (/ 2 + R / 6 + R * R / 24)) in HT by field.
(* The sum: [e^R - (s + pl)] is the Taylor error, [Q(R) - Q(rr)],
   [Q(rr) - q], and the roundings of [a] and [pl]. With [u = 2^-74]
   they are at most 1.28u, 0.03u, 0.13u, 2u and 2.03u: 5.5u <= 8u. *)
clear - HT HT5 EM HQM CQ Et E1 Ba Bpl ER.
apply Rabs_le. num. lra.
Qed.
