(** * The assembly steps of the fast paths of atan, atan2, asin and acos

    [DyadicAtan.pio2_add f rh rl] of [Model.v] adds [f π/2], for [f = 1/2]
    or [1], to a double-double [rh + rl] with [|rh| <= f] and [|rl| <=
    2^-52], with [PIO2] of [FastAtanTables.v], within [2^-102]
    ([pio2_add_correct]).
    [DyadicAtan.split v] writes a positive finite [v] as [m 2^e] with [m]
    in [[1, 2)] exactly ([split_correct]), as [DyadicLog.ln_split].
    [DyadicAtan.octant swap neg rh rl] turns a double-double [rh + rl]
    near [v] in [(0, 4/5]] into [h + l] near [v], [π - v], [π/2 - v] or
    [π/2 + v] by [(swap, neg)], scaled by [2^-e] into the range of
    [Fast.round_dir_err] and [Fast.round_near_err], within [2^-70]
    ([octant_correct]). None of these sums cancels: each is at least
    [π/4], or is [v] itself. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error.
From Inari Require Import Model Mpfr Encoding Elementary TwoSum DyDriver NearF64
  FastRound FastRoundErr CancelLanes FastHypPos FastAtanTables.
From Inari Require FastExpErr FastLogReduce SqrtSlow Limbs MulRuTiny.

Open Scope R_scope.

(** Closes a linear goal over the reals: the bounds [Rabs x <= y] of the
    context become two inequalities, [2^-1075] stays an atom, and every
    other [bpow] of a constant exponent becomes a numeral. *)
Local Ltac close :=
  pose proof (bpow_gt_0 radix2 (-1075));
  assert (bpow radix2 (-1075) <= bpow radix2 (-200)) by (apply bpow_le; lia);
  repeat match goal with H : Rabs _ <= _ |- _ => apply Rabs_le_inv in H end;
  try apply Rabs_le;
  let w := fresh "w" in
  set (w := bpow radix2 (-1075)) in *; clearbody w;
  cbn [bpow radix_val radix2] in *; lra.

Lemma pio2_add_correct :
  forall f rh rl,
  is_finite f = true -> is_finite rh = true -> is_finite rl = true ->
  (B2R f = / 2 \/ B2R f = 1) ->
  Rabs (B2R rh) <= B2R f -> Rabs (B2R rl) <= bpow radix2 (-52) ->
  let '(h, l) := DyadicAtan.pio2_add f rh rl in
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  Rabs (B2R h + B2R l - (B2R f * (PI / 2) + (B2R rh + B2R rl))) <= bpow radix2 (-102).
Proof.
intros f rh rl Ff Frh Frl Hf Hrh Hrl.
destruct fast_pio2_correct as (FP & FPl & EP & HPl & HPi).
cbv beta iota zeta delta [DyadicAtan.pio2_add Fast.fast_two_sum].
set (P := from_bits (fst DyadicAtan.PIO2)) in *.
set (Pl := from_bits (snd DyadicAtan.PIO2)) in *.
assert (HF : / 2 <= B2R f <= 1) by (destruct Hf; lra).
pose proof (bpow_gt_0 radix2 (-1075)) as Hw0.
assert (Hw : bpow radix2 (-1075) <= bpow radix2 (-200)) by (apply bpow_le; lia).
(* [P f] is a float: [P] itself, or [P / 2]. *)
assert (Hm1 : is_finite (mul P f) = true /\ B2R (mul P f) = B2R P * B2R f).
{ destruct (SqrtSlow.mul_exact P f FP Ff) as (F & E & _); [| | split; assumption].
  - destruct Hf as [Ef | Ef]; rewrite Ef.
    + replace (/ 2) with (bpow radix2 (-1)) by (cbn [bpow radix_val radix2]; lra).
      apply SqrtSlow.format_scale; [apply generic_format_B2R | |].
      * rewrite EP, Rabs_pos_eq by lra. cbn [bpow radix_val radix2]. lra.
      * rewrite Rabs_mult, EP, (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0.
        rewrite Rabs_pos_eq by lra. cbn [bpow radix_val radix2]. lra.
    + rewrite Rmult_1_r. apply generic_format_B2R.
  - rewrite EP, Rabs_pos_eq by lra. cbn [bpow radix_val radix2]. lra. }
destruct Hm1 as (Fm1 & Em1).
set (m1 := mul P f) in *.
rewrite EP in Em1, HPi.
(* [s = RN(P f + rh)], with [P f + rh] in [[0.28, 2.6]]. *)
destruct (FastExpErr.add_k m1 rh (13 / 5) Fm1 Frh) as (Fs & Es & Hs); [rewrite Em1; close | lra |].
set (s := add m1 rh) in *.
destruct (CancelLanes.fast_two_sum m1 rh s Fm1 Frh) as (Fs0 & Es0); [| exact Fs | exact Es |].
{ apply Rle_trans with (B2R f); [exact Hrh |]. rewrite Em1, Rabs_pos_eq by lra. lra. }
set (s0 := add rh (sub m1 s)) in *.
(* [m2 = RN(Pl f)], with [|Pl f| <= 2^-53]. *)
assert (HPlf : Rabs (B2R Pl * B2R f) <= bpow radix2 (-53)).
{ rewrite <- (Rmult_1_r (bpow radix2 (-53))).
  apply FastExpErr.Rabs_mul_le; [exact HPl | rewrite Rabs_pos_eq; lra]. }
destruct (FastExpErr.mul_k Pl f (bpow radix2 (-53)) FPl Ff HPlf) as (Fm2 & _ & Hm2); [close |].
set (m2 := mul Pl f) in *.
(* The low parts: [a1 = RN(s0 + m2)] and [v = RN(a1 + rl)]. *)
destruct (FastExpErr.add_k s0 m2 (4 * bpow radix2 (-53)) Fs0 Fm2) as (Fa1 & _ & Ha1);
  [close | close |].
set (a1 := add s0 m2) in *.
destruct (FastExpErr.add_k a1 rl (7 * bpow radix2 (-53)) Fa1 Frl) as (Fv & _ & Hv);
  [close | close |].
set (v := add a1 rl) in *.
(* [h = RN(s + v)], and Fast2Sum is exact as [|v| <= 2^-50 <= s]. *)
destruct (FastExpErr.add_k s v 3 Fs Fv) as (Fh & Eh & _); [close | lra |].
set (h := add s v) in *.
destruct (CancelLanes.fast_two_sum s v h Fs Fv) as (Fl & El); [| exact Fh | exact Eh |].
{ rewrite (Rabs_pos_eq (B2R s)) by close. close. }
rewrite El.
split; [exact Fh |]. split; [exact Fl |].
split; [replace (B2R h + (B2R s + B2R v - B2R h)) with (B2R s + B2R v) by ring; exact Eh |].
(* The error is [f (P + Pl - pi/2)] plus the three roundings of the low
   parts: [2^-107 + (1 + 4 + 7) 2^-106 + 3 2^-1075 <= 2^-102]. *)
assert (HPiF : Rabs (B2R f * (884279719003555 / 562949953421312 + B2R Pl - PI / 2)) <=
  1 * bpow radix2 (-107)).
{ apply FastExpErr.Rabs_mul_le; [rewrite Rabs_pos_eq; lra | exact HPi]. }
clear Es Eh El.
close.
Qed.

(** The split of a normal pattern [c]: [m] is [1 + M 2^-52] for the
    stored significand [M], and [c] has the value [m 2^(E - 1023)] for its
    biased exponent [E], as [FastLogReduce.split_normal] without the
    table. *)
Local Lemma split_one :
  forall c, (2 ^ 52 <= c < 2047 * 2 ^ 52)%Z ->
  let m := from_bits (Z.lor (Z.land c DyadicLog.frac) 0x3ff0000000000000) in
  is_finite m = true /\ 1 <= B2R m < 2 /\
  (-1022 <= Z.shiftr c 52 - 1023 <= 1023)%Z /\
  magnitude c = B2R m * bpow radix2 (Z.shiftr c 52 - 1023).
Proof.
intros c Hc. cbv zeta.
assert (HcE : (c = c / 2 ^ 52 * 2 ^ 52 + c mod 2 ^ 52 /\ 1 <= c / 2 ^ 52 <= 2046 /\
  0 <= c mod 2 ^ 52 < 2 ^ 52)%Z) by zlia.
assert (Ef : Z.land c DyadicLog.frac = (c mod 2 ^ 52)%Z).
{ change DyadicLog.frac with (Z.ones 52). apply Z.land_ones. lia. }
assert (Es : Z.shiftr c 52 = (c / 2 ^ 52)%Z) by (apply Z.shiftr_div_pow2; lia).
rewrite Ef, Es.
set (E := (c / 2 ^ 52)%Z) in *. set (M := (c mod 2 ^ 52)%Z) in *.
destruct HcE as (HcE & HE & HM).
(* The value of [c]: [(M + 2^52) 2^(E - 1075)]. *)
assert (Hc' : magnitude c = F2R (Float radix2 (M + 2 ^ 52) (E - 1075))).
{ rewrite HcE. rewrite magnitude_split by lia.
  replace (E =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  replace (Z.max E 1) with E by lia. reflexivity. }
rewrite Hc'.
(* [m] is the pattern [1023 2^52 + M], of value [(M + 2^52) 2^-52]. *)
replace 0x3ff0000000000000%Z with (1023 * 2 ^ 52)%Z by reflexivity.
rewrite Z.lor_comm, Limbs.lor_low by lia.
destruct (from_bits_finite false (1023 * 2 ^ 52 + M)) as (Fm & _ & Em);
  [split; [lia | simpl Z.pow in *; lia] |].
unfold sign_bit in Fm, Em. rewrite Z.add_0_l in Fm, Em. cbv iota in Em.
rewrite Em, magnitude_split by lia.
change (1023 =? 0)%Z with false. cbv iota. change (Z.max 1023 1 - 1075)%Z with (-52)%Z.
split; [exact Fm |].
unfold F2R; cbn [Fnum Fexp].
assert (H52 : IZR (2 ^ 52) * bpow radix2 (-52) = 1).
{ change (2 ^ 52)%Z with (Zpower radix2 52). rewrite IZR_Zpower by lia.
  rewrite <- bpow_plus. reflexivity. }
assert (HM0 : 0 <= IZR M) by (apply IZR_le; lia).
assert (HM1 : IZR M < IZR (2 ^ 52)) by (apply IZR_lt; lia).
pose proof (bpow_gt_0 radix2 (-52)) as Hb.
rewrite plus_IZR.
split; [split; nra | split; [lia |]].
rewrite Rmult_assoc, <- bpow_plus. do 2 f_equal. ring.
Qed.

Lemma split_correct :
  forall v,
  is_finite v = true -> 0 < B2R v ->
  let '(m, e) := DyadicAtan.split v in
  is_finite m = true /\ 1 <= B2R m < 2 /\ B2R v = B2R m * bpow radix2 e /\
  (-1074 <= e <= 1023)%Z.
Proof.
intros v Fv Hv.
destruct (FastLogReduce.pos_bits v Fv Hv) as (c & Hc & Hb & Hval).
unfold DyadicAtan.split. rewrite Hb.
replace (DyadicExp.two_pow 52) with DyadicLog.two52 by (vm_compute; reflexivity).
destruct (Z.ltb_spec c (2 ^ 52)) as [Hs | Hs]; cbv beta iota zeta.
- (* A subnormal [v = c 2^-1074]: [v 2^52] is exact and normal. *)
  destruct FastLogReduce.two52_R as [F52 E52].
  assert (Hm0 : magnitude (0 * 2 ^ 52 + c) = IZR c * bpow radix2 (-1074)).
  { rewrite magnitude_split by lia. reflexivity. }
  rewrite Z.mul_0_l, Z.add_0_l in Hm0.
  destruct (magnitude_bounds c ltac:(lia)) as ((_ & Hlt) & _).
  replace (c / 2 ^ 52)%Z with 0%Z in Hlt by (symmetry; apply Z.div_small; lia).
  change (0 - 1022)%Z with (-1022)%Z in Hlt.
  assert (Hc1 : 1 <= IZR c) by (apply IZR_le; lia).
  pose proof (bpow_gt_0 radix2 (-1074)) as Hb0.
  assert (Hlo : bpow radix2 (-1074) <= B2R v) by (rewrite Hval, Hm0; nra).
  assert (Hhi : B2R v < bpow radix2 (-1022)) by (rewrite Hval; exact Hlt).
  assert (Hx2 : is_finite (mul v DyadicLog.two52) = true /\
    B2R (mul v DyadicLog.two52) = B2R v * bpow radix2 52).
  { destruct (MulRuTiny.mul_RN_spec v DyadicLog.two52 Fv F52) as (F & E & _).
    - rewrite E52, Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 52); nra).
      apply Rle_trans with (bpow radix2 (-1022) * bpow radix2 52).
      + apply Rmult_le_compat_r; [apply bpow_ge_0 | lra].
      + rewrite <- bpow_plus. apply bpow_le. lia.
    - split; [exact F |]. rewrite E, E52.
      apply round_generic; [typeclasses eauto |].
      apply SqrtSlow.format_scale_up; [apply generic_format_B2R | lia]. }
  destruct Hx2 as (Fx2 & Ex2).
  assert (Hx2lo : bpow radix2 (-1022) <= B2R (mul v DyadicLog.two52)).
  { rewrite Ex2. replace (-1022)%Z with (-1074 + 52)%Z by reflexivity.
    rewrite bpow_plus. apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Hlo]. }
  destruct (FastLogReduce.pos_bits (mul v DyadicLog.two52) Fx2
    ltac:(pose proof (bpow_gt_0 radix2 (-1022)); lra)) as (c2 & Hc2 & Hb2 & Hv2).
  rewrite Hb2.
  assert (Hn2 : (2 ^ 52 <= c2)%Z).
  { destruct (Z.lt_ge_cases c2 (2 ^ 52)) as [Hl | Hl]; [exfalso | exact Hl].
    destruct (magnitude_bounds c2 ltac:(lia)) as ((_ & Hlt2) & _).
    replace (c2 / 2 ^ 52)%Z with 0%Z in Hlt2 by (symmetry; apply Z.div_small; lia).
    change (0 - 1022)%Z with (-1022)%Z in Hlt2. lra. }
  pose proof (split_one c2 (conj Hn2 (proj2 Hc2))) as H. cbv zeta in H.
  destruct H as (Fm & Hm & He & Hmag).
  split; [exact Fm |]. split; [exact Hm |]. split; [| lia].
  rewrite bpow_plus.
  match goal with |- _ = ?m * (?a * ?b) => replace (m * (a * b)) with (a * (m * b)) by ring end.
  rewrite <- Hmag, <- Hv2, Ex2.
  rewrite Rmult_comm, Rmult_assoc, <- bpow_plus. rewrite Rmult_1_r. reflexivity.
- (* A normal [v]. *)
  pose proof (split_one c (conj Hs (proj2 Hc))) as H. cbv zeta in H.
  destruct H as (Fm & Hm & He & Hmag).
  split; [exact Fm |]. split; [exact Hm |]. split; [| lia].
  rewrite Z.add_0_l, Hval. exact Hmag.
Qed.

(** ** The octant *)

(** [B2R l] of an [f64] literal [l], as [m * 2^e] (as in [FastHypPos.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

Local Lemma lit_err70 :
  is_finite DyadicAtan.err70 = true /\ B2R DyadicAtan.err70 = bpow radix2 (-70).
Proof.
split; [vm_compute; reflexivity |].
lit_B2R. change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
reflexivity.
Qed.

Local Lemma lit_half : is_finite DyadicLog.half = true /\ B2R DyadicLog.half = / 2.
Proof. split; [vm_compute; reflexivity |]. lit_B2R. cbn [bpow radix_val radix2]. lra. Qed.

Local Lemma lit_neg_half :
  is_finite DyadicLog.neg_half = true /\ B2R DyadicLog.neg_half = - / 2.
Proof. split; [vm_compute; reflexivity |]. lit_B2R. cbn [bpow radix_val radix2]. lra. Qed.

(** [c x] for [c = 1/2] or [-1/2] and [|x| <= 1]: exact where it is
    normal, and within half an ulp of the subnormals, [2^-1075], below. *)
Local Lemma mul_half :
  forall c x, is_finite c = true -> is_finite x = true ->
  (B2R c = / 2 \/ B2R c = - / 2) -> Rabs (B2R x) <= 1 ->
  is_finite (mul c x) = true /\ Rabs (B2R (mul c x) - B2R c * B2R x) <= bpow radix2 (-1075).
Proof.
intros c x Fc Fx Hc Hx.
assert (B1 : bpow radix2 (-1) = / 2) by (cbn [bpow radix_val radix2]; lra).
assert (Hcx : Rabs (B2R c * B2R x) = / 2 * Rabs (B2R x)).
{ rewrite Rabs_mult.
  destruct Hc as [-> | ->]; [| rewrite Rabs_Ropp]; rewrite (Rabs_pos_eq (/ 2)) by lra;
    reflexivity. }
destruct (FastExpErr.mul_e c x Fc Fx ltac:(rewrite Hcx; lra)) as (F & E & _).
split; [exact F |]. rewrite E.
pose proof (bpow_gt_0 radix2 (-1075)) as H0.
destruct (Rle_or_lt (bpow radix2 (-1022)) (Rabs (B2R c * B2R x))) as [Hb | Hb].
- (* [c x = +-(x 2^-1)] is a float. *)
  assert (Hf : generic_format radix2 fexp64 (B2R x * bpow radix2 (-1))).
  { pose proof (bpow_gt_0 radix2 (-1022)).
    apply SqrtSlow.format_scale; [apply generic_format_B2R | lra |].
    rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0. rewrite B1. lra. }
  rewrite round_generic; [rewrite Rminus_diag, Rabs_R0; lra | typeclasses eauto |].
  destruct Hc as [Ec | Ec]; rewrite Ec, <- B1.
  + rewrite Rmult_comm. exact Hf.
  + replace (- bpow radix2 (-1) * B2R x) with (- (B2R x * bpow radix2 (-1))) by ring.
    apply generic_format_opp. exact Hf.
- (* Below [2^-1022], the error is at most half of [ulp = 2^-1074]. *)
  assert (H : Rabs (RN (B2R c * B2R x) - B2R c * B2R x) <=
    / 2 * ulp radix2 fexp64 (B2R c * B2R x))
    by (apply error_le_half_ulp; typeclasses eauto).
  rewrite (ulp_FLT_small radix2 (-1074) 53 _) in H
    by (eapply Rlt_le_trans; [exact Hb | apply bpow_le; lia]).
  assert (E' : / 2 * bpow radix2 (-1074) = bpow radix2 (-1075))
    by (cbn [bpow radix_val radix2]; lra).
  lra.
Qed.

(** The cases that add to [π/2]: [|rh + rl - v| <= d] with [v <= 4/5]
    and [d <= 2^-60] gives [|rl| <= 2^-53] and [|rh| <= 81/100]. *)
Local Lemma oct_low_d :
  forall (rh rl : f64) v d, B2R rh = RN (B2R rh + B2R rl) -> 0 < v <= 4 / 5 ->
  d <= bpow radix2 (-60) -> Rabs (B2R rh + B2R rl - v) <= d ->
  Rabs (B2R rl) <= bpow radix2 (-53) /\ Rabs (B2R rh) <= 81 / 100.
Proof.
intros rh rl v d Hrn Hv Hd Hz.
assert (Hz1 : Rabs (B2R rh + B2R rl) <= bpow radix2 (-53 + 53)).
{ change (-53 + 53)%Z with 0%Z. close. }
pose proof (FastHypPos.rn_err _ (-53) ltac:(lia) Hz1) as Hr.
rewrite <- Hrn in Hr.
replace (B2R rh - (B2R rh + B2R rl)) with (- B2R rl) in Hr by ring.
rewrite Rabs_Ropp in Hr.
split; [exact Hr | close].
Qed.

(** [oct_low_d] at [d = 2^-73]. *)
Local Lemma oct_low :
  forall (rh rl : f64) v, B2R rh = RN (B2R rh + B2R rl) -> 0 < v <= 4 / 5 ->
  Rabs (B2R rh + B2R rl - v) <= bpow radix2 (-73) ->
  Rabs (B2R rl) <= bpow radix2 (-53) /\ Rabs (B2R rh) <= 81 / 100.
Proof.
intros rh rl v Hrn Hv Hz.
assert (Hd : bpow radix2 (-73) <= bpow radix2 (-60)) by (apply bpow_le; lia).
exact (oct_low_d rh rl v _ Hrn Hv Hd Hz).
Qed.

(** For [(swap, neg)] = [(false, false)], [rh + rl] must be within
    [2^-73] of [v] relatively and [v >= 2^-1020], for [normalize]; for
    the others, within [2^-73] absolutely. *)
Lemma octant_correct :
  forall swap neg rh rl v h l e err,
  is_finite rh = true -> is_finite rl = true -> B2R rh = RN (B2R rh + B2R rl) ->
  0 < v <= 4 / 5 ->
  (if swap || neg then Rabs (B2R rh + B2R rl - v) <= bpow radix2 (-73)
   else bpow radix2 (-1020) <= v /\ Rabs (B2R rh + B2R rl - v) <= bpow radix2 (-73) * v) ->
  DyadicAtan.octant swap neg rh rl = (h, l, e, err) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= e <= 1)%Z /\ B2R err = bpow radix2 (-70) /\
  Rabs ((if swap then (if neg then PI / 2 + v else PI / 2 - v) else (if neg then PI - v else v))
        * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (-70).
Proof.
intros swap neg rh rl v h l e err Frh Frl Hrn Hv Hc E.
destruct lit_err70 as (_ & E70).
destruct FastLogReduce.one_R as (F1 & E1).
destruct swap, neg; cbv beta iota delta [orb] in Hc;
  cbv beta iota delta [DyadicAtan.octant] in E; cbv beta iota.
- (* [π/2 + v]: [π/4 + v/2] with [e = 1]. *)
  destruct (oct_low rh rl v Hrn Hv Hc) as (Hrl & Hrh).
  destruct lit_half as (Fc & Ec).
  destruct (mul_half _ rh Fc Frh (or_introl Ec) ltac:(lra)) as (Fa & Ha).
  destruct (mul_half _ rl Fc Frl (or_introl Ec) ltac:(close)) as (Fb & Hb).
  rewrite Ec in Ha, Hb.
  pose proof (pio2_add_correct _ _ _ Fc Fa Fb (or_introl Ec)
    ltac:(rewrite Ec; close) ltac:(close)) as H.
  revert E H.
  destruct (DyadicAtan.pio2_add DyadicLog.half (mul DyadicLog.half rh) (mul DyadicLog.half rl))
    as (h', l').
  cbv beta iota. intros E (Fh & Fl & Hrn' & Herr). injection E as <- <- <- <-.
  rewrite Ec in Herr.
  split; [exact Fh |]. split; [exact Fl |]. split; [exact Hrn' |]. split; [lia |].
  split; [exact E70 |].
  rewrite (bpow_opp radix2 1). change (bpow radix2 1) with 2.
  close.
- (* [π/2 - v] with [e = 0]. *)
  destruct (oct_low rh rl v Hrn Hv Hc) as (Hrl & Hrh).
  assert (Fa : is_finite (opp rh) = true) by (unfold opp; rewrite is_finite_Bopp; exact Frh).
  assert (Ea : B2R (opp rh) = - B2R rh) by (unfold opp; apply B2R_Bopp).
  assert (Fb : is_finite (opp rl) = true) by (unfold opp; rewrite is_finite_Bopp; exact Frl).
  assert (Eb : B2R (opp rl) = - B2R rl) by (unfold opp; apply B2R_Bopp).
  pose proof (pio2_add_correct _ _ _ F1 Fa Fb (or_intror E1)
    ltac:(rewrite Ea, Rabs_Ropp, E1; lra) ltac:(rewrite Eb, Rabs_Ropp; close)) as H.
  revert E H.
  destruct (DyadicAtan.pio2_add DyadicExp.one (opp rh) (opp rl)) as (h', l').
  cbv beta iota. intros E (Fh & Fl & Hrn' & Herr). injection E as <- <- <- <-.
  rewrite E1, Ea, Eb in Herr.
  split; [exact Fh |]. split; [exact Fl |]. split; [exact Hrn' |]. split; [lia |].
  split; [exact E70 |].
  change (bpow radix2 (- 0)) with 1.
  close.
- (* [π - v]: [π/2 - v/2] with [e = 1]. *)
  destruct (oct_low rh rl v Hrn Hv Hc) as (Hrl & Hrh).
  destruct lit_neg_half as (Fc & Ec).
  destruct (mul_half _ rh Fc Frh (or_intror Ec) ltac:(lra)) as (Fa & Ha).
  destruct (mul_half _ rl Fc Frl (or_intror Ec) ltac:(close)) as (Fb & Hb).
  rewrite Ec in Ha, Hb.
  pose proof (pio2_add_correct _ _ _ F1 Fa Fb (or_intror E1)
    ltac:(rewrite E1; close) ltac:(close)) as H.
  revert E H.
  destruct (DyadicAtan.pio2_add DyadicExp.one (mul DyadicLog.neg_half rh)
    (mul DyadicLog.neg_half rl)) as (h', l').
  cbv beta iota. intros E (Fh & Fl & Hrn' & Herr). injection E as <- <- <- <-.
  rewrite E1 in Herr.
  split; [exact Fh |]. split; [exact Fl |]. split; [exact Hrn' |]. split; [lia |].
  split; [exact E70 |].
  rewrite (bpow_opp radix2 1). change (bpow radix2 1) with 2.
  close.
- (* [v] itself, scaled into [[1, 2)] by [normalize]. *)
  destruct Hc as (Hv0 & Hz).
  set (z := B2R rh + B2R rl) in *.
  assert (HT : bpow radix2 (-73) * v <= v / 2).
  { apply Rle_trans with (/ 2 * v); [| lra].
    apply Rmult_le_compat_r; [lra | cbn [bpow radix_val radix2]; lra]. }
  assert (E1020 : bpow radix2 (-1020) = 2 * bpow radix2 (-1021)).
  { change (-1020)%Z with (1 + -1021)%Z. rewrite bpow_plus. reflexivity. }
  assert (Hz' := Hz). apply Rabs_le_inv in Hz'.
  (* [rh = RN(z)] is in [[2^-1021, 2)], as [z] is in [[v / 2, 3 v / 2]]. *)
  assert (Hrh : bpow radix2 (-1021) <= B2R rh < 2).
  { split.
    - rewrite Hrn. apply round_ge_generic;
        [typeclasses eauto .. | apply generic_format_bpow; unfold FLT_exp; lia | lra].
    - pose proof (FastExpErr.rn_err z) as Hr. rewrite <- Hrn in Hr.
      rewrite (Rabs_pos_eq z) in Hr by lra.
      close. }
  pose proof (normalize_correct rh rl Frh Frl Hrn Hrh) as N.
  revert E N.
  destruct (Fast.normalize rh rl) as ((h', l'), k).
  cbv beta iota. intros E (Fh & Fl & Hk & Eh & El & Hb & Hrn').
  injection E as <- <- <- <-.
  split; [exact Fh |]. split; [exact Fl |]. split; [exact Hrn' |]. split; [lia |].
  split; [exact E70 |].
  (* [z < 2^(k+1)], or [RN(z) >= 2^(k+1) > rh]; so [v < 2^(k+2)], and the
     error is at most [2^-73 2^(k+2) 2^-k = 2^-71]. *)
  assert (Hzk : z < bpow radix2 (k + 1)).
  { destruct (Rlt_or_le z (bpow radix2 (k + 1))) as [H | H]; [exact H | exfalso].
    assert (bpow radix2 (k + 1) <= B2R rh).
    { rewrite Hrn. apply round_ge_generic;
        [typeclasses eauto .. | apply generic_format_bpow; unfold FLT_exp; lia | exact H]. }
    lra. }
  assert (Ekk : bpow radix2 k * bpow radix2 (- k) = 1)
    by (rewrite <- bpow_plus, Z.add_opp_diag_r; reflexivity).
  assert (Hk1 : bpow radix2 (k + 1) = 2 * bpow radix2 k)
    by (rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
  assert (H4 : v <= 4 * bpow radix2 k) by lra.
  rewrite Eh, El.
  replace (v * bpow radix2 (- k) - (B2R rh * bpow radix2 (- k) + B2R rl * bpow radix2 (- k)))
    with ((v - z) * bpow radix2 (- k)) by (unfold z; ring).
  rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (- k))) by apply bpow_ge_0.
  rewrite Rabs_minus_sym.
  apply Rle_trans with (bpow radix2 (-73) * v * bpow radix2 (- k)).
  { apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Hz]. }
  apply Rle_trans with (bpow radix2 (-73) * (4 * bpow radix2 k) * bpow radix2 (- k)).
  { apply Rmult_le_compat_r; [apply bpow_ge_0 |].
    apply Rmult_le_compat_l; [apply bpow_ge_0 | exact H4]. }
  replace (bpow radix2 (-73) * (4 * bpow radix2 k) * bpow radix2 (- k))
    with (bpow radix2 (-73) * 4 * (bpow radix2 k * bpow radix2 (- k))) by ring.
  rewrite Ekk. cbn [bpow radix_val radix2]. lra.
Qed.

(** [octant_correct] for [rh + rl] within [d] of [v], for [2^-100 <= d <=
    2^-60], relatively for [(swap, neg)] = [(false, false)] and absolutely
    for the others: the result is within [3 d] of the octant's value. *)
Lemma octant_bound :
  forall swap neg rh rl v h l e err d,
  is_finite rh = true -> is_finite rl = true -> B2R rh = RN (B2R rh + B2R rl) ->
  0 < v <= 4 / 5 -> bpow radix2 (-100) <= d <= bpow radix2 (-60) ->
  (if swap || neg then Rabs (B2R rh + B2R rl - v) <= d
   else bpow radix2 (-1020) <= v /\ Rabs (B2R rh + B2R rl - v) <= d * v) ->
  DyadicAtan.octant swap neg rh rl = (h, l, e, err) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= e <= 1)%Z /\
  Rabs ((if swap then (if neg then PI / 2 + v else PI / 2 - v) else (if neg then PI - v else v))
        * bpow radix2 (- e) - (B2R h + B2R l)) <= 3 * d.
Proof.
intros swap neg rh rl v h l e err d Frh Frl Hrn Hv Hd Hc E.
destruct Hd as (Hd0 & Hd1).
destruct FastLogReduce.one_R as (F1 & E1).
destruct swap, neg; cbv beta iota delta [orb] in Hc;
  cbv beta iota delta [DyadicAtan.octant] in E; cbv beta iota.
- (* [π/2 + v]: [π/4 + v/2] with [e = 1]; the error is at most [2^-102 +
     2 2^-1075 + d / 2 <= 3 d], as [d >= 2^-100]. *)
  destruct (oct_low_d rh rl v d Hrn Hv Hd1 Hc) as (Hrl & Hrh).
  destruct lit_half as (Fc & Ec).
  destruct (mul_half _ rh Fc Frh (or_introl Ec) ltac:(lra)) as (Fa & Ha).
  destruct (mul_half _ rl Fc Frl (or_introl Ec) ltac:(close)) as (Fb & Hb).
  rewrite Ec in Ha, Hb.
  pose proof (pio2_add_correct _ _ _ Fc Fa Fb (or_introl Ec)
    ltac:(rewrite Ec; close) ltac:(close)) as H.
  revert E H.
  destruct (DyadicAtan.pio2_add DyadicLog.half (mul DyadicLog.half rh) (mul DyadicLog.half rl))
    as (h', l').
  cbv beta iota. intros E (Fh & Fl & Hrn' & Herr). injection E as <- <- <- <-.
  rewrite Ec in Herr.
  split; [exact Fh |]. split; [exact Fl |]. split; [exact Hrn' |]. split; [lia |].
  rewrite (bpow_opp radix2 1). change (bpow radix2 1) with 2.
  close.
- (* [π/2 - v] with [e = 0]: at most [2^-102 + d <= 3 d]. *)
  destruct (oct_low_d rh rl v d Hrn Hv Hd1 Hc) as (Hrl & Hrh).
  assert (Fa : is_finite (opp rh) = true) by (unfold opp; rewrite is_finite_Bopp; exact Frh).
  assert (Ea : B2R (opp rh) = - B2R rh) by (unfold opp; apply B2R_Bopp).
  assert (Fb : is_finite (opp rl) = true) by (unfold opp; rewrite is_finite_Bopp; exact Frl).
  assert (Eb : B2R (opp rl) = - B2R rl) by (unfold opp; apply B2R_Bopp).
  pose proof (pio2_add_correct _ _ _ F1 Fa Fb (or_intror E1)
    ltac:(rewrite Ea, Rabs_Ropp, E1; lra) ltac:(rewrite Eb, Rabs_Ropp; close)) as H.
  revert E H.
  destruct (DyadicAtan.pio2_add DyadicExp.one (opp rh) (opp rl)) as (h', l').
  cbv beta iota. intros E (Fh & Fl & Hrn' & Herr). injection E as <- <- <- <-.
  rewrite E1, Ea, Eb in Herr.
  split; [exact Fh |]. split; [exact Fl |]. split; [exact Hrn' |]. split; [lia |].
  change (bpow radix2 (- 0)) with 1.
  close.
- (* [π - v]: [π/2 - v/2] with [e = 1], as the first case. *)
  destruct (oct_low_d rh rl v d Hrn Hv Hd1 Hc) as (Hrl & Hrh).
  destruct lit_neg_half as (Fc & Ec).
  destruct (mul_half _ rh Fc Frh (or_intror Ec) ltac:(lra)) as (Fa & Ha).
  destruct (mul_half _ rl Fc Frl (or_intror Ec) ltac:(close)) as (Fb & Hb).
  rewrite Ec in Ha, Hb.
  pose proof (pio2_add_correct _ _ _ F1 Fa Fb (or_intror E1)
    ltac:(rewrite E1; close) ltac:(close)) as H.
  revert E H.
  destruct (DyadicAtan.pio2_add DyadicExp.one (mul DyadicLog.neg_half rh)
    (mul DyadicLog.neg_half rl)) as (h', l').
  cbv beta iota. intros E (Fh & Fl & Hrn' & Herr). injection E as <- <- <- <-.
  rewrite E1 in Herr.
  split; [exact Fh |]. split; [exact Fl |]. split; [exact Hrn' |]. split; [lia |].
  rewrite (bpow_opp radix2 1). change (bpow radix2 1) with 2.
  close.
- (* [v] itself, scaled into [[1, 2)] by [normalize]. *)
  destruct Hc as (Hv0 & Hz).
  set (z := B2R rh + B2R rl) in *.
  assert (Hd2 : d <= / 3).
  { apply Rle_trans with (1 := Hd1). cbn [bpow radix_val radix2]. lra. }
  assert (HT : d * v <= v / 3).
  { apply Rle_trans with (/ 3 * v); [| lra].
    apply Rmult_le_compat_r; lra. }
  assert (E1020 : bpow radix2 (-1020) = 2 * bpow radix2 (-1021)).
  { change (-1020)%Z with (1 + -1021)%Z. rewrite bpow_plus. reflexivity. }
  pose proof (bpow_gt_0 radix2 (-1021)) as P1021.
  assert (Hz' := Hz). apply Rabs_le_inv in Hz'.
  (* [rh = RN(z)] is in [[2^-1021, 2)], as [z] is in [[2 v / 3, 4 v / 3]]. *)
  assert (Hrh : bpow radix2 (-1021) <= B2R rh < 2).
  { split.
    - rewrite Hrn. apply round_ge_generic;
        [typeclasses eauto .. | apply generic_format_bpow; unfold FLT_exp; lia | lra].
    - pose proof (FastExpErr.rn_err z) as Hr. rewrite <- Hrn in Hr.
      rewrite (Rabs_pos_eq z) in Hr by lra.
      close. }
  pose proof (normalize_correct rh rl Frh Frl Hrn Hrh) as N.
  revert E N.
  destruct (Fast.normalize rh rl) as ((h', l'), k).
  cbv beta iota. intros E (Fh & Fl & Hk & Eh & El & Hb & Hrn').
  injection E as <- <- <- <-.
  split; [exact Fh |]. split; [exact Fl |]. split; [exact Hrn' |]. split; [lia |].
  (* [z < 2^(k+1)], or [RN(z) >= 2^(k+1) > rh]; with [z >= (1 - d) v >=
     2 v / 3], [v < 3 2^k], and the error is at most [d v 2^-k <= 3 d]. *)
  assert (Hzk : z < bpow radix2 (k + 1)).
  { destruct (Rlt_or_le z (bpow radix2 (k + 1))) as [H | H]; [exact H | exfalso].
    assert (bpow radix2 (k + 1) <= B2R rh).
    { rewrite Hrn. apply round_ge_generic;
        [typeclasses eauto .. | apply generic_format_bpow; unfold FLT_exp; lia | exact H]. }
    lra. }
  assert (Ekk : bpow radix2 k * bpow radix2 (- k) = 1)
    by (rewrite <- bpow_plus, Z.add_opp_diag_r; reflexivity).
  assert (Hk1 : bpow radix2 (k + 1) = 2 * bpow radix2 k)
    by (rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
  assert (H3 : v <= 3 * bpow radix2 k) by lra.
  rewrite Eh, El.
  replace (v * bpow radix2 (- k) - (B2R rh * bpow radix2 (- k) + B2R rl * bpow radix2 (- k)))
    with ((v - z) * bpow radix2 (- k)) by (unfold z; ring).
  rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (- k))) by apply bpow_ge_0.
  rewrite Rabs_minus_sym.
  apply Rle_trans with (d * v * bpow radix2 (- k)).
  { apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Hz]. }
  assert (Hd0' : 0 <= d) by (pose proof (bpow_gt_0 radix2 (-100)); lra).
  apply Rle_trans with (d * (3 * bpow radix2 k) * bpow radix2 (- k)).
  { apply Rmult_le_compat_r; [apply bpow_ge_0 |].
    apply Rmult_le_compat_l; [exact Hd0' | exact H3]. }
  replace (d * (3 * bpow radix2 k) * bpow radix2 (- k))
    with (3 * d * (bpow radix2 k * bpow radix2 (- k))) by ring.
  rewrite Ekk. lra.
Qed.
