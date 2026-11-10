(** * The scaled result of the fast path of [cosh]

    [DyadicExp.fast_cosh_pos] of [Model.v] returns, for [t >= 0], an
    unevaluated sum [h + l] with [h] the rounding of [h + l] to nearest,
    an exponent [e] and a bound [err = 2^-p] with [|cosh t 2^-e - (h +
    l)| <= err], which the tests of [FastRoundErr.v] take
    ([fast_cosh_pos_correct]):
    - [t >= 26]: [e^t / 2] from [fast_exp_correct] of [FastExpCore.v],
      where the term [e^-t / 2] it drops is below [2^-74] once scaled, and
      fits the room [2^-72] that [fast_exp_correct] leaves below [2^-68];
    - [t < 26]: [(E + 1/E) / 2] for [E = e^t] from [fast_exp_correct] and
      [1/E] from the double-double quotient of [FastDiv.v], with [err =
      2^-67].
    It returns the same with and without an FMA ([fast_cosh_pos_fma]).
    The lemmas it shares with [sinh] are in [FastHypPos.v]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error.
From Inari Require Import Model Mpfr Encoding Elementary TwoSum TwoProduct MulRuTiny DyDriver
  NearF64 FastRound FastExpTables FastExpCore FastRoundErr FastDiv FastHypPos.
From Inari Require DyExpRules CancelLanes SqrtSlow.

Open Scope R_scope.

Local Notation G := (generic_format radix2 fexp64).
Local Notation succ64 := (succ radix2 fexp64).
Local Notation pred64 := (pred radix2 fexp64).

(** ** The middle range [t < 26] *)

(** For [E = e^t], [P = 2^-e] and [y = h + l], the quotient [P P / y]
    that [dd_div] computes is [r E P] for [r = P / (E y)], and it misses
    [P / E] by [-(E P - y) r], where [r y E^2 = E P] bounds [r]. *)
Local Lemma cq_split :
  forall E P y, 0 < E -> 0 < P -> 0 < y ->
  exists r, 0 < r /\ r * y * (E * E) = E * P /\
    / E * P - P * P / y = - (E * P - y) * r /\ P * P / y = r * (E * P).
Proof.
intros E P y HE HP Hy.
assert (E0 : E <> 0) by (apply Rgt_not_eq; exact HE).
assert (Y0 : y <> 0) by (apply Rgt_not_eq; exact Hy).
exists (P / (E * y)).
split.
{ unfold Rdiv. apply Rmult_lt_0_compat; [exact HP|].
  apply Rinv_0_lt_compat, Rmult_lt_0_compat; assumption. }
split; [field; repeat split; assumption|].
split; field; repeat split; assumption.
Qed.

(** The values of the middle range before the halving: [h' + l'] is
    [cosh t 2^-(e - 1) = E P + P / E] within [2^-68], with [h' = RN(h' +
    l')]. The error is [(E P - y) (1 - r)] from [fast_exp] (with [0 < r <=
    2], as [E >= 1]), [2^-95] from the quotient and two roundings of the
    low parts below [2^-100]: [s0], [l] and [wl] are below [2^-49], and the
    sum [h'] of [s > 1/4] and the low part [a2] is exact by Fast2Sum
    ([CancelLanes.fast_two_sum]). *)
Local Lemma cosh_mid_core :
  forall fma (t h l : f64) e wh wl s s0 h' l',
  0 <= B2R t ->
  is_finite h = true -> is_finite l = true -> / 2 < B2R h < 2 ->
  Rabs (B2R l) <= bpow radix2 (-53) -> (-1 <= e <= 39)%Z ->
  Rabs (exp (B2R t) * bpow radix2 (- e) - (B2R h + B2R l))
    <= bpow radix2 (-68) - bpow radix2 (-72) ->
  Fast.dd_div fma (DyadicExp.two_pow (-2 * e)) zero h l = (wh, wl) ->
  Fast.two_sum h wh = (s, s0) ->
  Fast.fast_two_sum s (add (add s0 l) wl) = (h', l') ->
  is_finite h' = true /\ is_finite l' = true /\ B2R h' = RN (B2R h' + B2R l') /\
  Rabs (B2R l') <= bpow radix2 (-49) /\ Rabs (B2R h' + B2R l') <= 16 /\
  Rabs (cosh (B2R t) * bpow radix2 (- (e - 1)) - (B2R h' + B2R l')) <= bpow radix2 (-68).
Proof.
intros fma t h l e wh wl s s0 h' l' Ht Fh Fl Hh Hl He Herr Hdd Hts Hft.
assert (K : bpow radix2 (-53) <= / 64 /\ bpow radix2 (-68) <= / 64 /\ 0 < bpow radix2 (-72) /\
  bpow radix2 (-98) * 6 <= bpow radix2 (-95) /\ bpow radix2 3 = 8 /\ bpow radix2 4 = 16 /\
  bpow radix2 (-95) <= / 64 /\ bpow radix2 (-50) <= / 64 /\ bpow radix2 (-49) <= / 64 /\
  bpow radix2 (-49) + bpow radix2 (-53) <= bpow radix2 (-48) /\
  bpow radix2 (-48) + bpow radix2 (-101) + bpow radix2 (-50) <= bpow radix2 (-47) /\
  bpow radix2 (-47) + bpow radix2 (-100) <= / 4 /\
  bpow radix2 (-95) + bpow radix2 (-101) + bpow radix2 (-100) <= bpow radix2 (-72) /\
  16 <= bpow radix2 1023 /\ 0 < bpow radix2 971 /\ 0 < bpow radix2 (-101) /\
  0 < bpow radix2 (-100) /\ 0 < bpow radix2 (-48) /\ 0 < bpow radix2 (-47))
  by (cbn [bpow radix_val radix2]; repeat split; lra).
destruct K as (K53 & K68 & K72 & K98 & K3 & K4 & K95 & K50 & K49 & K48 & K47 & K46 & Kf &
  K1023 & K971 & P101 & P100 & P48 & P47).
(* The quotient [W = wh + wl] of [P P / y]. *)
destruct (tp_facts e He) as (Fn & Rn & Bn).
destruct (dd_hyps h l e Hh Hl He) as (D1 & D2 & D3).
assert (Fz : is_finite zero = true) by reflexivity.
pose proof (dd_div_correct fma _ _ h l Fn Fz Fh Fl Bn D1 D2 D3) as D.
rewrite Hdd in D. destruct D as (Fwh & Fwl & Ewh & Hw).
rewrite Rn in Hw. change (B2R zero) with 0 in Hw. rewrite Rplus_0_r in Hw.
assert (HE : 1 <= exp (B2R t)) by (rewrite <- exp_0; apply exp_le; exact Ht).
pose proof (bpow_gt_0 radix2 (- e)) as HP.
pose proof Herr as Herr'. apply Rabs_le_inv in Herr'.
pose proof Hl as Hl'. apply Rabs_le_inv in Hl'.
assert (Ypos : 0 < B2R h + B2R l) by lra.
assert (HE0 : 0 < exp (B2R t)) by lra.
destruct (cq_split (exp (B2R t)) (bpow radix2 (- e)) (B2R h + B2R l) HE0 HP Ypos)
  as (r & Hr & R1 & R2 & R3).
rewrite R3 in Hw, R2.
(* [r <= 2]: [r y <= r y E^2 = E P <= y + 2^-68]. *)
assert (E2 : 1 <= exp (B2R t) * exp (B2R t)) by nra.
assert (RY : r * (B2R h + B2R l) <= exp (B2R t) * bpow radix2 (- e)).
{ rewrite <- R1. apply Rle_trans with (r * (B2R h + B2R l) * 1); [lra|].
  apply Rmult_le_compat_l; [|exact E2]. apply Rmult_le_pos; lra. }
assert (Rle2 : r <= 2).
{ destruct (Rle_lt_dec r 2) as [|Hr2]; [assumption|exfalso].
  assert (2 * (B2R h + B2R l) < r * (B2R h + B2R l)) by (apply Rmult_lt_compat_r; lra).
  lra. }
assert (EP3 : exp (B2R t) * bpow radix2 (- e) <= 3) by lra.
assert (Q0 : 0 <= r * (exp (B2R t) * bpow radix2 (- e))) by (apply Rmult_le_pos; lra).
assert (Q6 : r * (exp (B2R t) * bpow radix2 (- e)) <= 6).
{ apply Rle_trans with (2 * 3); [apply Rmult_le_compat; lra | lra]. }
assert (WQ : Rabs (B2R wh + B2R wl - r * (exp (B2R t) * bpow radix2 (- e)))
             <= bpow radix2 (-95)).
{ apply Rle_trans with (1 := Hw). apply Rle_trans with (bpow radix2 (-98) * 6); [|exact K98].
  apply Rmult_le_compat_l; [apply bpow_ge_0 | exact Q6]. }
pose proof WQ as WQ'. apply Rabs_le_inv in WQ'.
(* [|wl| <= 2^-50], as [|W| <= 8]. *)
assert (Wl : Rabs (B2R wl) <= bpow radix2 (-50)).
{ assert (Z1 : Rabs (RN (B2R wh + B2R wl) - (B2R wh + B2R wl)) <= bpow radix2 (-50)).
  { apply rn_err; [lia|]. change (-50 + 53)%Z with 3%Z. apply Rabs_le. lra. }
  rewrite <- Ewh in Z1. replace (B2R wh - (B2R wh + B2R wl)) with (- B2R wl) in Z1 by ring.
  rewrite Rabs_Ropp in Z1. exact Z1. }
pose proof Wl as Wl'. apply Rabs_le_inv in Wl'.
(* [s + s0 = h + wh] exactly, with [|s0| <= 2^-49], as [|h + wh| <= 16]. *)
assert (HW : Rabs (B2R h + B2R wh) <= 16) by (apply Rabs_le; lra).
assert (HW' : Rabs (B2R h + B2R wh) <= bpow radix2 1023 + bpow radix2 971) by lra.
destruct (add_no_overflow h wh Fh Fwh HW') as (Fs & Rs).
assert (Hh1 : Rabs (B2R h) < bpow radix2 1023) by (apply Rabs_def1; lra).
assert (Hw1 : Rabs (B2R wh) < bpow radix2 1023) by (apply Rabs_def1; lra).
pose proof (two_sum_correct h wh Fh Fwh Hh1 Hw1 Fs) as T.
rewrite Hts in T. destruct T as (Es & Fs0 & Rs0).
rewrite <- Es in Fs, Rs.
assert (S0 : Rabs (B2R s0) <= bpow radix2 (-49)).
{ assert (Z1 : Rabs (RN (B2R h + B2R wh) - (B2R h + B2R wh)) <= bpow radix2 (-49)).
  { apply rn_err; [lia|]. change (-49 + 53)%Z with 4%Z. lra. }
  rewrite <- Rs in Z1. rewrite Rs0.
  replace (B2R h + B2R wh - B2R s) with (- (B2R s - (B2R h + B2R wh))) by ring.
  rewrite Rabs_Ropp. exact Z1. }
pose proof S0 as S0'. apply Rabs_le_inv in S0'.
(* The low part [a2 = RN(RN(s0 + l) + wl)], with two errors below [2^-100]. *)
assert (B1 : Rabs (B2R s0 + B2R l) <= bpow radix2 1023 + bpow radix2 971)
  by (apply Rabs_le; lra).
destruct (add_no_overflow s0 l Fs0 Fl B1) as (Fa1 & Ra1).
assert (A1 : Rabs (B2R (add s0 l) - (B2R s0 + B2R l)) <= bpow radix2 (-101)).
{ rewrite Ra1. apply rn_err; [lia|]. change (-101 + 53)%Z with (-48)%Z. apply Rabs_le. lra. }
pose proof A1 as A1'. apply Rabs_le_inv in A1'.
assert (B2 : Rabs (B2R (add s0 l) + B2R wl) <= bpow radix2 1023 + bpow radix2 971)
  by (apply Rabs_le; lra).
destruct (add_no_overflow (add s0 l) wl Fa1 Fwl B2) as (Fa2 & Ra2).
assert (A2 : Rabs (B2R (add (add s0 l) wl) - (B2R (add s0 l) + B2R wl)) <= bpow radix2 (-100)).
{ rewrite Ra2. apply rn_err; [lia|]. change (-100 + 53)%Z with (-47)%Z. apply Rabs_le. lra. }
pose proof A2 as A2'. apply Rabs_le_inv in A2'.
(* Fast2Sum of [s > 1/4] and [|a2| < 1/4]: [wh >= -2^-49], as [W >= 0]. *)
assert (Spos : / 4 < B2R s) by lra.
assert (Ha2 : Rabs (B2R (add (add s0 l) wl)) <= Rabs (B2R s)).
{ rewrite (Rabs_pos_eq (B2R s)) by lra. apply Rabs_le. lra. }
assert (Hsa : Rabs (B2R s + B2R (add (add s0 l) wl)) <= 16) by (apply Rabs_le; lra).
assert (B3 : Rabs (B2R s + B2R (add (add s0 l) wl)) <= bpow radix2 1023 + bpow radix2 971)
  by lra.
destruct (add_no_overflow s (add (add s0 l) wl) Fs Fa2 B3) as (Fh1 & Rh1).
destruct (CancelLanes.fast_two_sum s (add (add s0 l) wl) (add s (add (add s0 l) wl))
  Fs Fa2 Ha2 Fh1 Rh1) as (Fl1 & Rl1).
cbv beta zeta delta [Fast.fast_two_sum] in Hft.
apply pair_equal_spec in Hft. destruct Hft as (Eh' & El').
rewrite El' in Fl1, Rl1. rewrite Eh' in Fh1, Rh1, Rl1.
assert (Rsum : B2R h' + B2R l' = B2R s + B2R (add (add s0 l) wl)) by (rewrite Rl1; ring).
assert (L1 : Rabs (B2R l') <= bpow radix2 (-49)).
{ assert (Z1 : Rabs (RN (B2R s + B2R (add (add s0 l) wl)) - (B2R s + B2R (add (add s0 l) wl)))
               <= bpow radix2 (-49)).
  { apply rn_err; [lia|]. change (-49 + 53)%Z with 4%Z. lra. }
  rewrite <- Rh1 in Z1.
  replace (B2R l') with (- (B2R h' - (B2R s + B2R (add (add s0 l) wl)))) by (rewrite Rl1; ring).
  rewrite Rabs_Ropp. exact Z1. }
refine (conj Fh1 (conj Fl1 (conj _ (conj L1 (conj _ _))))).
- rewrite Rsum. exact Rh1.
- rewrite Rsum. exact Hsa.
- (* The error [(E P - y) (1 - r) + (r E P - W) - (a1 - (s0 + l)) - (a2 - (a1 + wl))]. *)
  rewrite cosh_scale, exp_Ropp, Rsum.
  assert (DR : Rabs ((exp (B2R t) * bpow radix2 (- e) - (B2R h + B2R l)) * (1 - r))
               <= bpow radix2 (-68) - bpow radix2 (-72)).
  { rewrite Rabs_mult. rewrite <- (Rmult_1_r (bpow radix2 (-68) - bpow radix2 (-72))).
    apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Herr | apply Rabs_le; lra]. }
  apply Rabs_le_inv in DR.
  apply Rabs_le. lra.
Qed.

(** The halving of the middle range when [h' >= 2]: [h' / 2] is exact,
    [l' / 2] is exact or below [2^-1022], and either way [h' / 2] is the
    rounding of their sum; the error halves, plus [2^-103] from [l' / 2]. *)
Local Lemma cosh_halve :
  forall (h l : f64) c,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  2 <= B2R h -> Rabs (B2R l) <= bpow radix2 (-49) -> Rabs (B2R h + B2R l) <= 16 ->
  Rabs (c * 2 - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  is_finite (mul h half) = true /\ is_finite (mul l half) = true /\
  B2R (mul h half) = RN (B2R (mul h half) + B2R (mul l half)) /\
  Rabs (c - (B2R (mul h half) + B2R (mul l half))) <= bpow radix2 (-67).
Proof.
intros h l c Fh Fl Eh Hh Hl Hs Hc.
assert (K : bpow radix2 (-49) <= / 64 /\ 16 <= bpow radix2 1023 /\ 0 < bpow radix2 971 /\
  bpow radix2 (-68) * / 2 + bpow radix2 (-103) <= bpow radix2 (-67) /\
  bpow radix2 (-49) * / 2 <= bpow radix2 (-50) /\ bpow radix2 (-1022) <= / 2 /\
  0 < bpow radix2 (-1021) /\ bpow radix2 (-1021) + bpow radix2 (-1074) < bpow radix2 (-54))
  by (cbn [bpow radix_val radix2]; repeat split; lra).
destruct K as (K49 & K1023 & K971 & K67 & K50 & K1022 & K1021 & K54).
assert (Fhalf : is_finite half = true) by (vm_compute; reflexivity).
pose proof Hl as Hl'. apply Rabs_le_inv in Hl'.
pose proof Hs as Hs'. apply Rabs_le_inv in Hs'.
assert (M1 : Rabs (B2R h * B2R half) <= bpow radix2 1023 + bpow radix2 971)
  by (rewrite lit_half; apply Rabs_le; lra).
destruct (mul_fin h half Fh Fhalf M1) as (Fmh & Rmh).
assert (M2 : Rabs (B2R l * B2R half) <= bpow radix2 1023 + bpow radix2 971)
  by (rewrite lit_half; apply Rabs_le; lra).
destruct (mul_fin l half Fl Fhalf M2) as (Fml & Rml).
rewrite lit_half in Rmh, Rml.
assert (Gh : G (B2R h * / 2)).
{ change (/ 2) with (bpow radix2 (-1)).
  apply format_shift; [apply generic_format_B2R | rewrite Rabs_pos_eq; lra | lia]. }
rewrite (round_generic _ _ _ _ Gh) in Rmh.
assert (Z1 : Rabs (RN (B2R l * / 2) - B2R l * / 2) <= bpow radix2 (-103)).
{ apply rn_err; [lia|]. change (-103 + 53)%Z with (-50)%Z. apply Rabs_le. lra. }
assert (Err : Rabs (c - (B2R (mul h half) + B2R (mul l half))) <= bpow radix2 (-67)).
{ rewrite Rmh, Rml. apply Rabs_le_inv in Z1. apply Rabs_le_inv in Hc. apply Rabs_le. lra. }
assert (Ern : B2R (mul h half) = RN (B2R (mul h half) + B2R (mul l half))).
{ rewrite Rmh, Rml.
  destruct (Rle_lt_dec (bpow radix2 (-1021)) (Rabs (B2R l))) as [Hbig|Hsmall].
  - (* [l / 2] is exact, and so is the scaling of [RN(h + l) = h]. *)
    assert (Gl : G (B2R l * / 2)).
    { change (/ 2) with (bpow radix2 (-1)). apply mult_bpow_exact_FLT; [apply generic_format_B2R|].
      assert (M : (-1020 <= mag radix2 (B2R l))%Z).
      { apply mag_ge_bpow. change (-1020 - 1)%Z with (-1021)%Z. exact Hbig. }
      lia. }
    rewrite (round_generic _ _ _ _ Gl).
    rewrite <- Rmult_plus_distr_r. change (/ 2) with (bpow radix2 (-1)).
    rewrite (SqrtSlow.round_scale ZnearestE (B2R h + B2R l) (-1)).
    + rewrite <- Eh. reflexivity.
    + rewrite Rabs_pos_eq by lra. lra.
    + change (bpow radix2 (-1)) with (/ 2). rewrite Rabs_pos_eq by lra. lra.
  - (* [RN(l / 2)] is below [2^-54], which [h / 2 >= 1] absorbs. *)
    assert (Z2 : Rabs (RN (B2R l * / 2) - B2R l * / 2) <= bpow radix2 (-1074)).
    { apply rn_err; [lia|]. change (-1074 + 53)%Z with (-1021)%Z.
      apply Rabs_lt_inv in Hsmall. apply Rabs_le. lra. }
    symmetry. apply rn_absorb; [exact Gh | lra |].
    apply Rabs_le_inv in Z2. apply Rabs_lt_inv in Hsmall. apply Rabs_def1; lra. }
exact (conj Fmh (conj Fml (conj Ern Err))).
Qed.

(** ** The theorems *)

(** Where [fast_cosh_pos] returns [(h, l, e, err)], [h + l] is [cosh t
    2^-e] within [err = 2^-p], and [h] is the rounding of [h + l] to
    nearest. *)
Theorem fast_cosh_pos_correct :
  forall fma t h l e err,
  is_finite t = true -> 0 <= B2R t ->
  DyadicExp.fast_cosh_pos fma t = Some (h, l, e, err) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= e <= 1022)%Z /\
  exists p, (55 <= p <= 105)%Z /\ B2R err = bpow radix2 (- p) /\
    Rabs (cosh (B2R t) * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (- p).
Proof.
intros fma t h l e err Ft Ht H.
unfold DyadicExp.fast_cosh_pos in H.
destruct (DyadicExp.fast_exp fma t zero) as [[[h0 l0] e0]|] eqn:Hfe; [|discriminate H].
cbv beta iota in H.
destruct (fe_facts fma t h0 l0 e0 Ft Ht Hfe) as (Fh0 & Fl0 & Eh0 & Hh0 & He0 & Hl0 & Herr0).
assert (F26 : is_finite (from_bits 0x403a000000000000) = true) by (vm_compute; reflexivity).
destruct (ge t (from_bits 0x403a000000000000)) eqn:Hge.
- (* [t >= 26]: [e^t / 2], and the dropped [e^-t / 2] fits the room [2^-72]. *)
  injection H as <- <- <- <-.
  pose proof (ge_true _ _ Ft F26 Hge) as Ht26. rewrite lit_26 in Ht26.
  refine (conj Fh0 (conj Fl0 (conj Eh0 (conj _ _)))); [lia|].
  exists 68%Z. split; [lia|]. split; [exact lit_err68|].
  rewrite cosh_scale. cbn [Z.opp].
  assert (K : bpow radix2 (-53) <= / 64 /\ bpow radix2 (-68) <= / 64 /\ 0 < bpow radix2 (-72))
    by (cbn [bpow radix_val radix2]; repeat split; lra).
  apply Rabs_le_inv in Herr0. apply Rabs_le_inv in Hl0.
  pose proof (bpow_gt_0 radix2 (- e0)) as HP.
  assert (EP : exp (B2R t) * bpow radix2 (- e0) <= 3) by lra.
  pose proof (tail_small (B2R t) (bpow radix2 (- e0)) Ht26 (Rlt_le _ _ HP) EP) as T.
  assert (T0 : 0 <= exp (- B2R t) * bpow radix2 (- e0))
    by (apply Rmult_le_pos; [apply Rlt_le, exp_pos | lra]).
  apply Rabs_le. lra.
- (* [t < 26]: [E P + P / E], halved when [h' >= 2]. *)
  pose proof (ge_false _ _ Ft F26 Hge) as Ht26. rewrite lit_26 in Ht26.
  pose proof (fe_mid t h0 l0 e0 Ht26 Hh0 Hl0 Herr0) as He39.
  assert (He : (-1 <= e0 <= 39)%Z) by lia.
  destruct (Fast.dd_div fma (DyadicExp.two_pow (-2 * e0)) zero h0 l0) as [wh wl] eqn:Hdd.
  cbv beta iota in H.
  destruct (Fast.two_sum h0 wh) as [s s0] eqn:Hts. cbv beta iota in H.
  destruct (Fast.fast_two_sum s (add (add s0 l0) wl)) as [h1 l1] eqn:Hft. cbv beta iota in H.
  destruct (cosh_mid_core fma t h0 l0 e0 wh wl s s0 h1 l1 Ht Fh0 Fl0 Hh0 Hl0 He Herr0 Hdd Hts Hft)
    as (Fh1 & Fl1 & Eh1 & Hl1 & Hs1 & Hb).
  assert (F2 : is_finite DyadicExp.two = true) by (vm_compute; reflexivity).
  destruct (ge h1 DyadicExp.two) eqn:Hg2.
  + injection H as <- <- <- <-.
    pose proof (ge_true _ _ Fh1 F2 Hg2) as H2. rewrite lit_two in H2.
    assert (Hc : Rabs (cosh (B2R t) * bpow radix2 (- e0) * 2 - (B2R h1 + B2R l1))
                 <= bpow radix2 (-68)).
    { replace (cosh (B2R t) * bpow radix2 (- e0) * 2)
        with (cosh (B2R t) * bpow radix2 (- (e0 - 1))); [exact Hb|].
      replace (- (e0 - 1))%Z with (1 + - e0)%Z by lia.
      rewrite bpow_plus. change (bpow radix2 1) with 2. ring. }
    destruct (cosh_halve h1 l1 _ Fh1 Fl1 Eh1 H2 Hl1 Hs1 Hc) as (F1 & F2' & R & B).
    refine (conj F1 (conj F2' (conj R (conj _ _)))); [lia|].
    exists 67%Z. split; [lia|]. split; [exact lit_err67 | exact B].
  + injection H as <- <- <- <-.
    refine (conj Fh1 (conj Fl1 (conj Eh1 (conj _ _)))); [lia|].
    exists 67%Z. split; [lia|]. split; [exact lit_err67|].
    apply Rle_trans with (1 := Hb). apply bpow_le. lia.
Qed.

(** [fast_cosh_pos] returns the same with and without an FMA. *)
Theorem fast_cosh_pos_fma :
  forall t,
  is_finite t = true -> 0 <= B2R t ->
  DyadicExp.fast_cosh_pos true t = DyadicExp.fast_cosh_pos false t.
Proof.
intros t Ft Ht.
unfold DyadicExp.fast_cosh_pos.
assert (F26 : is_finite (from_bits 0x403a000000000000) = true) by (vm_compute; reflexivity).
rewrite fast_exp_fma.
destruct (DyadicExp.fast_exp false t zero) as [[[h0 l0] e0]|] eqn:Hfe; [|reflexivity].
cbv beta iota.
destruct (ge t (from_bits 0x403a000000000000)) eqn:Hge; [reflexivity|].
pose proof (ge_false _ _ Ft F26 Hge) as T3. rewrite lit_26 in T3.
destruct (fe_facts false t h0 l0 e0 Ft Ht Hfe) as (Fh0 & Fl0 & _ & Hh0 & He0 & Hl0 & Herr).
pose proof (fe_mid t h0 l0 e0 T3 Hh0 Hl0 Herr) as He1.
assert (He : (-1 <= e0 <= 39)%Z) by lia.
destruct (tp_facts e0 He) as (Fn & _ & Bn).
destruct (dd_hyps h0 l0 e0 Hh0 Hl0 He) as (N1 & D1 & D2).
rewrite (dd_div_fma (DyadicExp.two_pow (-2 * e0)) zero h0 l0 Fn eq_refl Fh0 Fl0 Bn N1 D1 D2).
reflexivity.
Qed.
