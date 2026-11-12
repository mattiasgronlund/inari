(** * The product of the reduction of the fast paths of [sin], [cos] and [tan] near the multiples of π/2 above 2^16

    The floats [fh] and [fl] of [DyadicTrig.fast_reduce_band_big] of
    [Model.v] are their integers [zh] and [zl] times [2^(-53-s)] and
    [2^(-106-s)], not rounded, where [s] is the shift of the
    normalization ([band_fh], [band_fl]), as the bits [(970 - s) << 52]
    and [(917 - s) << 52] are those powers of 2 ([band_pow]). With [S =
    2^-s], where [S/8 <= |fh| <= S/2] and [|fl| <= 2^-53 S] (which hold
    for either sign of [fh] and [fl] where [2^51 - 1 <= |zh| <= 2^52] and
    [0 <= zl < 2^53], [band_f_bounds]), [DyadicTrig.fast_mul] of [fh +
    fl] by [(U1 + U2) + U3] is [(fh + fl) π/4096] within [2^-110 S], with
    [|rl| <= 2^-24 |rh|] ([band_mul_rel]), the same with and without an
    FMA ([band_mul_fma]), as [FastTrigBigDec.v] and [FastTrigBigMul.v]
    give them for [fast_reduce_big]'s absolute bound.
    [FastTrigBandBig.v] uses them. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Encoding TwoSum TwoProduct FastRound FastExpErr
  FastTrigTables FastTrigReduce FastTrigBigMul FastTrigBigDec.
From Inari Require MulRuTiny FastLogFin FastExpReduce.

Open Scope R_scope.

(** ** The scales *)

(** The bits [E << 52] for a biased exponent [1 <= E <= 2046] and a zero
    stored significand are the float [2^(E - 1023)] ([Encoding.v]). *)
Lemma band_pow :
  forall E, (1 <= E <= 2046)%Z ->
  is_finite (from_bits (Z.shiftl E 52)) = true /\
  B2R (from_bits (Z.shiftl E 52)) = bpow radix2 (E - 1023).
Proof.
intros E HE.
assert (Eb : Z.shiftl E 52 = (sign_bit false + (E * 2 ^ 52 + 0))%Z).
{ rewrite Z.shiftl_mul_pow2 by lia. unfold sign_bit. ring. }
rewrite Eb.
destruct (from_bits_finite false (E * 2 ^ 52 + 0)) as (F & _ & V); [lia |].
split; [exact F |]. rewrite V. cbv iota.
rewrite magnitude_split by lia.
replace (E =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
replace (Z.max E 1) with E by lia.
unfold F2R. cbn [Fnum Fexp].
change (IZR (0 + 2 ^ 52)) with (bpow radix2 52).
rewrite <- bpow_plus. f_equal. ring.
Qed.

(** [z as f64] is [z] for [|z| < 2^53], and [z 2^(E - 1023)] is a float,
    as it is an integer below [2^53] times a power of 2 above the
    subnormals. *)
Lemma band_scale :
  forall z E, (Z.abs z < 2 ^ 53)%Z -> (1 <= E <= 1023)%Z ->
  is_finite (mul (DyadicTrig.of_i64 z) (from_bits (Z.shiftl E 52))) = true /\
  B2R (mul (DyadicTrig.of_i64 z) (from_bits (Z.shiftl E 52))) =
    IZR z * bpow radix2 (E - 1023).
Proof.
intros z E Hz HE.
destruct (band_pow E) as (Fp & Ep); [lia |].
change (DyadicTrig.of_i64 z) with (DyadicLog.of_i64 z).
destruct (FastLogFin.fl_of_i64 z Hz) as (Fz & Ez).
assert (Hb : Rabs (IZR z * bpow radix2 (E - 1023)) < bpow radix2 (E - 1023 + 53)).
{ rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (E - 1023))) by apply bpow_ge_0.
  rewrite <- abs_IZR.
  replace (E - 1023 + 53)%Z with (53 + (E - 1023))%Z by ring.
  rewrite (bpow_plus radix2 53 (E - 1023)).
  apply Rmult_lt_compat_r; [apply bpow_gt_0 |].
  change (bpow radix2 53) with (IZR (2 ^ 53)). apply IZR_lt. exact Hz. }
assert (B : bpow radix2 (E - 1023 + 53) <= bpow radix2 53) by (apply bpow_le; lia).
cbn [bpow radix_val radix2 Z.pow_pos] in B.
destruct (mul_below_max _ _ Fz Fp) as (F & R & _).
{ rewrite Ez, Ep. apply FastExpReduce.le_MAX. lra. }
split; [exact F |].
rewrite R, Ez, Ep. apply round_generic; [typeclasses eauto |].
apply grid_format; [lia | exact Hb].
Qed.

(** ** The two parts of the normalized fraction *)

(** [fh = zh 2^(-53-s)] for [|zh| <= 2^52]: the biased exponent [970 -
    s] is [2^(-53-s)]. *)
Lemma band_fh :
  forall zh s, (0 <= s <= 50)%Z -> (- 2 ^ 52 <= zh <= 2 ^ 52)%Z ->
  is_finite (mul (DyadicTrig.of_i64 zh) (from_bits (Z.shiftl (970 - s) 52))) = true /\
  B2R (mul (DyadicTrig.of_i64 zh) (from_bits (Z.shiftl (970 - s) 52))) =
    IZR zh * bpow radix2 (-53 - s).
Proof.
intros zh s Hs Hz.
destruct (band_scale zh (970 - s)) as (F & E); [lia | lia |].
split; [exact F |]. rewrite E. f_equal. f_equal. ring.
Qed.

(** [fl = zl 2^(-106-s)] for [0 <= zl < 2^53]: the biased exponent [917
    - s] is [2^(-106-s)]. *)
Lemma band_fl :
  forall zl s, (0 <= s <= 50)%Z -> (0 <= zl < 2 ^ 53)%Z ->
  is_finite (mul (DyadicTrig.of_i64 zl) (from_bits (Z.shiftl (917 - s) 52))) = true /\
  B2R (mul (DyadicTrig.of_i64 zl) (from_bits (Z.shiftl (917 - s) 52))) =
    IZR zl * bpow radix2 (-106 - s).
Proof.
intros zl s Hs Hz.
destruct (band_scale zl (917 - s)) as (F & E); [lia | lia |].
split; [exact F |]. rewrite E. f_equal. f_equal. ring.
Qed.

(** ** The product by π/4096 *)

(** Where [S/8 <= |fh| <= S/2] for some [S] in [[2^-50, 1]], [rh =
    RN(fh uh)] is at least [2^-15 S] in magnitude, as [fh uh] is at least
    [2^-14 S] and its rounding error at most [2^-64 S], and so at least
    [2^-65]. *)
Lemma band_guard :
  forall S fh,
  bpow radix2 (-50) <= S <= 1 -> is_finite fh = true ->
  bpow radix2 (-3) * S <= Rabs (B2R fh) <= / 2 * S ->
  Rabs (B2R fh) <= / 2 /\
  bpow radix2 (-15) * S <=
    Rabs (B2R (mul fh (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)))) /\
  bpow radix2 (-65) <=
    Rabs (B2R (mul fh (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)))).
Proof.
intros S fh HS Ffh Hfh.
destruct big_uh as (Fuh & _).
destruct big_u_bounds as (_ & Buh & _).
set (uh := add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)) in *.
pose proof (bpow_ge_0 radix2 (-50)) as B50.
pose proof (bpow_ge_0 radix2 (-11)) as B11.
assert (Hh : Rabs (B2R fh) <= / 2) by lra.
assert (HP : Rabs (B2R fh * B2R uh) <= / 2 * S * bpow radix2 (-10)).
{ apply Rabs_mul_le; [lra |]. rewrite Rabs_pos_eq by lra. lra. }
destruct (mul_k fh uh _ Ffh Fuh HP) as (_ & _ & Bp);
  [cbn [bpow radix_val radix2 Z.opp] in *; lra |].
assert (HL : bpow radix2 (-3) * S * bpow radix2 (-11) <= Rabs (B2R fh * B2R uh)).
{ rewrite Rabs_mult, (Rabs_pos_eq (B2R uh)) by lra.
  apply Rmult_le_compat; [| exact B11 | lra | lra].
  apply Rmult_le_pos; [apply bpow_ge_0 | lra]. }
pose proof (Rabs_triang_inv (B2R fh * B2R uh) (B2R fh * B2R uh - B2R (mul fh uh))) as T.
replace (B2R fh * B2R uh - (B2R fh * B2R uh - B2R (mul fh uh))) with (B2R (mul fh uh))
  in T by ring.
rewrite Rabs_minus_sym in T.
split; [exact Hh |].
cbn [bpow radix_val radix2 Z.opp] in *.
split; lra.
Qed.

(** [fast_mul] of [(fh, fl)] and [(uh, U3)], as in [big_mul_correct] with
    every bound times [S]: [rh = RN(fh uh)], and [fh uh - rh] is exact
    ([big_exact], Dekker). Where [Us = uh + U3] is within 2^-119 of
    [π/4096] ([fast_trig_consts]), [(fh + fl) π/4096 - (rh + rl)] is [(fh
    + fl) (π/4096 - Us) + fl U3] (at most [2^-119 S] and [2^-117 S]) minus
    the errors of [fh U3], [fl uh], their sum and [rl] (at most about
    [2^-118 S], [2^-116 S], [2^-115 S] and [2^-114 S], plus [2^-1075]
    each): within [2^-110 S] in all, as [S >= 2^-50]. [rl] is at most
    [2^-61 S] and its rounding, and [rh] at least [2^-15 S]
    ([band_guard]), so [|rl| <= 2^-24 |rh|]. *)
Lemma band_mul_rel :
  forall S fh fl rh rl,
  bpow radix2 (-50) <= S <= 1 ->
  is_finite fh = true -> is_finite fl = true ->
  bpow radix2 (-3) * S <= Rabs (B2R fh) <= / 2 * S ->
  Rabs (B2R fl) <= bpow radix2 (-53) * S ->
  DyadicTrig.fast_mul false fh fl
    (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)) (from_bits DyadicTrig.U3) =
    (rh, rl) ->
  is_finite rh = true /\ is_finite rl = true /\ is_finite (add rh rl) = true /\
  Rabs ((B2R fh + B2R fl) * (PI / 4096) - (B2R rh + B2R rl)) <= bpow radix2 (-110) * S /\
  bpow radix2 (-15) * S <= Rabs (B2R rh) /\
  Rabs (B2R rl) <= bpow radix2 (-24) * Rabs (B2R rh).
Proof.
intros S fh fl rh rl HS Ffh Ffl Hfh Hfl M.
destruct (band_guard S fh HS Ffh Hfh) as (Hh & Hrh & Hrh65).
unfold DyadicTrig.fast_mul in M. cbv zeta in M.
apply pair_equal_spec in M as [Ep Erl]. subst rh rl.
pose proof (big_exact false fh Ffh Hh Hrh65) as Hex.
destruct big_uh as (Fuh & Euh).
destruct big_u_bounds as (Fu3 & Buh & Bu3).
destruct fast_trig_consts as (_ & HU).
rewrite <- Euh in HU.
set (uh := add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)) in *.
set (u3 := from_bits DyadicTrig.U3) in *.
set (u := PI / 4096) in *.
clearbody uh u3 u. clear Euh.
cbn [bpow radix_val radix2 Z.opp] in Buh, Bu3, HS.
assert (Hfu : Rabs (B2R fh) <= / 2 * S) by lra.
(* [p = RN(fh uh)] and [e0 = fh uh - p] exactly. *)
destruct (two_prod_err_correct false fh uh Ffh Fuh Hex) as (Fp & _ & _ & Fe0 & Ee0).
assert (HP : Rabs (B2R fh * B2R uh) <= / 2 * S * bpow radix2 (-10)).
{ apply Rabs_mul_le; [exact Hfu |]. rewrite Rabs_pos_eq by lra.
  cbn [bpow radix_val radix2 Z.opp]. lra. }
destruct (mul_k fh uh _ Ffh Fuh HP) as (_ & _ & Bp);
  [cbn [bpow radix_val radix2 Z.opp]; lra |].
set (p := mul fh uh) in *.
set (e0 := Generic.two_prod_err false fh uh p) in *.
clearbody p e0.
apply Rabs_le_inv in HP, Bp.
cbn [bpow radix_val radix2 Z.opp] in HP, Bp.
(* [m1 = RN(fh U3)], [m2 = RN(fl uh)], [m3 = RN(m1 + m2)], [e = RN(e0 + m3)]. *)
assert (H1b : Rabs (B2R fh * B2R u3) <= / 2 * S * bpow radix2 (-64)).
{ apply Rabs_mul_le; [exact Hfu |]. rewrite Rabs_pos_eq by lra.
  cbn [bpow radix_val radix2 Z.opp]. lra. }
destruct (mul_k fh u3 _ Ffh Fu3 H1b) as (Fm1 & _ & Bm1);
  [cbn [bpow radix_val radix2 Z.opp]; lra |].
assert (H2b : Rabs (B2R fl * B2R uh) <= bpow radix2 (-53) * S * bpow radix2 (-10)).
{ apply Rabs_mul_le; [exact Hfl |]. rewrite Rabs_pos_eq by lra.
  cbn [bpow radix_val radix2 Z.opp]. lra. }
destruct (mul_k fl uh _ Ffl Fuh H2b) as (Fm2 & _ & Bm2);
  [cbn [bpow radix_val radix2 Z.opp]; lra |].
set (m1 := mul fh u3) in *. set (m2 := mul fl uh) in *.
clearbody m1 m2.
apply Rabs_le_inv in H1b, H2b, Bm1, Bm2.
cbn [bpow radix_val radix2 Z.opp] in H1b, H2b, Bm1, Bm2.
destruct (add_k m1 m2 (bpow radix2 (-62) * S) Fm1 Fm2) as (Fm3 & _ & Bm3);
  [apply Rabs_le; cbn [bpow radix_val radix2 Z.opp]; lra |
   cbn [bpow radix_val radix2 Z.opp]; lra |].
set (m3 := add m1 m2) in *. clearbody m3.
apply Rabs_le_inv in Bm3.
cbn [bpow radix_val radix2 Z.opp] in Bm3.
destruct (add_k e0 m3 (bpow radix2 (-61) * S) Fe0 Fm3) as (Fe & _ & Be);
  [apply Rabs_le; cbn [bpow radix_val radix2 Z.opp]; lra |
   cbn [bpow radix_val radix2 Z.opp]; lra |].
set (e := add e0 m3) in *. clearbody e.
apply Rabs_le_inv in Be.
cbn [bpow radix_val radix2 Z.opp] in Be.
(* [rh + rl] is far from overflow. *)
destruct (add_k p e 1 Fp Fe) as (Fr & _ & _);
  [apply Rabs_le; lra | lra |].
(* The constants: [(fh + fl) (π/4096 - Us)] and [fl U3]. *)
pose proof Hfl as Hfl'.
apply Rabs_le_inv in Hfu, Hfl'. cbn [bpow radix_val radix2 Z.opp] in Hfl'.
assert (Hf : Rabs (B2R fh + B2R fl) <= S) by (apply Rabs_le; lra).
pose proof (Rabs_mul_le _ _ _ _ Hf HU) as HD.
assert (Hlu : Rabs (B2R fl * B2R u3) <= bpow radix2 (-53) * S * bpow radix2 (-64)).
{ apply Rabs_mul_le; [exact Hfl |]. rewrite Rabs_pos_eq by lra.
  cbn [bpow radix_val radix2 Z.opp]. lra. }
apply Rabs_le_inv in HD, Hlu.
cbn [bpow radix_val radix2 Z.opp] in HD, Hlu, Hrh.
split; [exact Fp |]. split; [exact Fe |]. split; [exact Fr |].
split; [| split; [exact Hrh |]].
- apply Rabs_le. cbn [bpow radix_val radix2 Z.opp]. split; lra.
- apply Rle_trans with (bpow radix2 (-39) * S).
  + apply Rabs_le. cbn [bpow radix_val radix2 Z.opp]. split; lra.
  + cbn [bpow radix_val radix2 Z.opp]. lra.
Qed.

(** The same with an FMA: [fh uh] is exact in [two_prod_err] either way
    ([big_mul_fma]), as [|fh| <= 1/2] and [|RN(fh uh)| >= 2^-65]
    ([band_guard]). *)
Lemma band_mul_fma :
  forall S fh fl,
  bpow radix2 (-50) <= S <= 1 -> is_finite fh = true ->
  bpow radix2 (-3) * S <= Rabs (B2R fh) <= / 2 * S ->
  DyadicTrig.fast_mul true fh fl
    (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)) (from_bits DyadicTrig.U3) =
  DyadicTrig.fast_mul false fh fl
    (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)) (from_bits DyadicTrig.U3).
Proof.
intros S fh fl HS Ffh Hfh.
destruct (band_guard S fh HS Ffh Hfh) as (Hh & _ & H65).
exact (big_mul_fma fh fl Ffh Hh H65).
Qed.

(** The premises of [band_mul_rel] and [band_mul_fma] from the integers,
    with [S = 2^-s]: [fh = ± zh 2^(-53-s)] for [2^51 - 1 <= |zh| <=
    2^52] is between [S/8] and [S/2] in magnitude, and [fl = ± zl
    2^(-106-s)] for [0 <= zl < 2^53] is below [2^-53 S]. *)
Lemma band_f_bounds :
  forall sg zh zl s (fh fl : f64),
  (sg = 1 \/ sg = - 1) -> (0 <= s <= 50)%Z ->
  (2 ^ 51 - 1 <= Z.abs zh <= 2 ^ 52)%Z -> (0 <= zl < 2 ^ 53)%Z ->
  B2R fh = sg * (IZR zh * bpow radix2 (-53 - s)) ->
  B2R fl = sg * (IZR zl * bpow radix2 (-106 - s)) ->
  bpow radix2 (-50) <= bpow radix2 (- s) <= 1 /\
  bpow radix2 (-3) * bpow radix2 (- s) <= Rabs (B2R fh) <= / 2 * bpow radix2 (- s) /\
  Rabs (B2R fl) <= bpow radix2 (-53) * bpow radix2 (- s).
Proof.
intros sg zh zl s fh fl Hsg Hs Hzh Hzl Efh Efl.
assert (Asg : Rabs sg = 1).
{ destruct Hsg as [-> | ->]; unfold Rabs; destruct (Rcase_abs _); lra. }
replace (-53 - s)%Z with (-53 + - s)%Z in Efh by ring.
replace (-106 - s)%Z with (-106 + - s)%Z in Efl by ring.
rewrite bpow_plus in Efh, Efl.
set (S := bpow radix2 (- s)) in *.
assert (HS : bpow radix2 (-50) <= S <= 1).
{ split; [apply bpow_le; lia |].
  change 1 with (bpow radix2 0). apply bpow_le. lia. }
assert (S0 : 0 <= S) by (pose proof (bpow_ge_0 radix2 (-50)); lra).
(* [|fh| = |zh| 2^-53 S] and [|fl| = zl 2^-106 S]. *)
assert (Rh : Rabs (B2R fh) = IZR (Z.abs zh) * S * bpow radix2 (-53)).
{ rewrite Efh, !Rabs_mult, Asg, abs_IZR, (Rabs_pos_eq S S0),
    (Rabs_pos_eq (bpow radix2 (-53))) by apply bpow_ge_0.
  ring. }
assert (Rl : Rabs (B2R fl) = IZR zl * S * bpow radix2 (-106)).
{ rewrite Efl, !Rabs_mult, Asg, (Rabs_pos_eq S S0),
    (Rabs_pos_eq (bpow radix2 (-106))) by apply bpow_ge_0.
  rewrite Rabs_pos_eq by (apply IZR_le; lia). ring. }
destruct Hzh as [Z1 Z2]. destruct Hzl as [Z3 Z4].
apply IZR_le in Z1, Z2. apply IZR_lt in Z4.
rewrite minus_IZR in Z1.
assert (P1 : IZR (2 ^ 51) * S - S <= IZR (Z.abs zh) * S).
{ replace (IZR (2 ^ 51) * S - S) with ((IZR (2 ^ 51) - 1) * S) by ring.
  apply Rmult_le_compat_r; [exact S0 | exact Z1]. }
assert (P2 : IZR (Z.abs zh) * S <= IZR (2 ^ 52) * S).
{ apply Rmult_le_compat_r; [exact S0 | exact Z2]. }
assert (P3 : IZR zl * S <= IZR (2 ^ 53) * S).
{ apply Rmult_le_compat_r; [exact S0 | lra]. }
rewrite Rh, Rl.
split; [exact HS |].
cbn [bpow radix_val radix2 Z.opp] in *.
split; [split |]; lra.
Qed.
