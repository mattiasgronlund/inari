(** * The reduction of the fast path of [exp]

    [DyadicExp.fast_exp zh zl] writes [z = zh + zl] as [k c + r] with [c =
    ln 2 / 4096], [k] an integer within 1/2 of [RN(zh INV)], and so
    within about 1/2 + 2^-30 of [zh / c], and [r = rh + rl] up to 2^-72,
    where [rh = zh - k C1] is exact and at most [3 * 2^-15] in magnitude
    ([fast_exp_reduce]).

    [k] comes from the usual trick of adding and subtracting [SHIFTER] =
    1.5 * 2^52 (as in CORE-MATH's [exp] and in pxfm): [t = RN(zh INV)] is
    below 2^22 in magnitude, so [t + SHIFTER] lies in [[2^52, 2^53)],
    where the floats are the integers, and rounding it gives an integer
    within 1/2 of it. Subtracting [SHIFTER] again is exact. [C1] has 31
    significant bits, so [k C1] is exact for [|k| < 2^22]. [zh - k C1] is
    exact too, but not by Sterbenz's lemma, which fails narrowly at [k =
    ±1]: for [k <> 0], [|zh| >= 2^-14], so [zh] and [k C1] are multiples
    of 2^-66, and so is their difference, which is below 2^-13 in
    magnitude. *)

From Stdlib Require Import ZArith Reals Lra Lia QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Sterbenz.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct FastExpTables.
From Inari Require ConstTight.

Open Scope R_scope.

(** ** Helpers *)

(** [lit w H] adds [H : B2R w = n * / d] for the literal [w], with [n] and
    [d] numerals that [lra] reads, as in [DyExpRules.v]. *)
Local Ltac lit w H :=
  let q := eval vm_compute in (ConstTight.B2Q w) in
  assert (H : B2R w = Q2R q)
    by (rewrite ConstTight.B2Q_correct; f_equal; vm_compute; reflexivity);
  unfold Q2R in H; cbn [Qnum Qden] in H.

(** Rounding a value of at most [2^e] in magnitude to nearest moves it by
    at most [2^(e - 53)], half an ulp of [2^e], if [2^e] is normal. *)
Lemma RN_err_le :
  forall z e e', (-1021 <= e)%Z -> e' = (e - 53)%Z -> Rabs z <= bpow radix2 e ->
  Rabs (RN z - z) <= bpow radix2 e'.
Proof.
intros z e e' He -> Hz.
apply Rle_trans with (/2 * ulp radix2 fexp64 z).
{ apply error_le_half_ulp; typeclasses eauto. }
apply Rle_trans with (/2 * ulp radix2 fexp64 (bpow radix2 e)).
{ apply Rmult_le_compat_l. lra.
  apply ulp_le; [typeclasses eauto .. |].
  rewrite (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0. exact Hz. }
rewrite ulp_bpow.
replace (FLT_exp (-1074) 53 (e + 1)) with (e - 53 + 1)%Z by (unfold FLT_exp; lia).
rewrite bpow_plus. change (bpow radix2 1) with 2. lra.
Qed.

(** An integer of at most 53 bits times [2^e] is a float. *)
Lemma format_mult :
  forall M e, (Z.abs M < 2 ^ 53)%Z -> (-1074 <= e)%Z ->
  generic_format radix2 fexp64 (IZR M * bpow radix2 e).
Proof.
intros M e HM He. apply generic_format_FLT.
apply FLT_spec with (Float radix2 M e); [reflexivity | exact HM | exact He].
Qed.

Lemma format_int : forall z, (Z.abs z < 2 ^ 53)%Z -> generic_format radix2 fexp64 (IZR z).
Proof.
intros z Hz. rewrite <- (Rmult_1_r (IZR z)). apply (format_mult z 0); [exact Hz | lia].
Qed.

(** A float whose canonical exponent is at least [e] is an integer times
    [2^e]. *)
Lemma format_mult_inv :
  forall x e, generic_format radix2 fexp64 x -> (e <= cexp radix2 fexp64 x)%Z ->
  exists a, x = IZR a * bpow radix2 e.
Proof.
intros x e Gx He.
exists (Ztrunc (scaled_mantissa radix2 fexp64 x) * 2 ^ (cexp radix2 fexp64 x - e))%Z.
transitivity (F2R (Float radix2 (Ztrunc (scaled_mantissa radix2 fexp64 x))
                                (cexp radix2 fexp64 x))); [exact Gx|].
rewrite (F2R_change_exp radix2 e _ _ He). reflexivity.
Qed.

(** In [[2^52, 2^53)] the floats are the integers, so rounding to nearest
    there is rounding to the nearest integer, ties to even. *)
Lemma RN_int :
  forall v, bpow radix2 52 <= v < bpow radix2 53 ->
  RN v = IZR (Znearest (fun x => negb (Z.even x)) v).
Proof.
intros v Hv.
unfold round, scaled_mantissa, cexp.
rewrite (mag_unique_pos radix2 v 53 Hv).
change (FLT_exp (-1074) 53 53) with 0%Z.
unfold F2R. cbn [Fnum Fexp].
change (bpow radix2 (- 0)) with 1. change (bpow radix2 0) with 1.
rewrite !Rmult_1_r. reflexivity.
Qed.

(** [c as i64] is [c] itself for a float [c] that is an integer below
    2^63 in magnitude. *)
Lemma to_i64_int :
  forall c z, is_finite c = true -> B2R c = IZR z -> (Z.abs z < 2 ^ 63)%Z ->
  DyadicExp.to_i64 c = z.
Proof.
intros c z Fc Hz Hb.
assert (T : Btrunc c = z).
{ apply eq_IZR. rewrite Btrunc_correct, Hz by reflexivity.
  unfold round, F2R, scaled_mantissa, cexp, FIX_exp.
  cbn [Fnum Fexp bpow Z.opp]. rewrite !Rmult_1_r. now rewrite Ztrunc_IZR. }
assert (M : DyadicExp.to_i64 c = Z.max (- 2 ^ 63) (Z.min (2 ^ 63 - 1) (Btrunc c)))
  by (destruct c; try discriminate Fc; reflexivity).
rewrite M, T. lia.
Qed.

(** [ks.to_bits() as i32 as i64] is the integer [ks - SHIFTER] where
    that difference rounds to an integer below 2^31 in magnitude. *)
Lemma shifter_bits :
  forall ks z, is_finite (sub ks DyadicExp.shifter) = true ->
  B2R (sub ks DyadicExp.shifter) = IZR z -> (Z.abs z < 2 ^ 31)%Z ->
  DyadicExp.low_i32 (to_bits ks) = z.
Proof.
intros ks z F Hz Hb.
(* A NaN or an infinite [ks] gives a NaN or an infinite difference. *)
assert (Fk : is_finite ks = true).
{ destruct ks as [s|s| |s m e H]; try reflexivity; exfalso;
    vm_compute in F; discriminate F. }
assert (FS : is_finite DyadicExp.shifter = true) by reflexivity.
lit DyadicExp.shifter HS.
set (S := DyadicExp.shifter) in *.
(* The difference is finite, so it did not overflow, and is [RN(ks - S)]. *)
assert (HR : B2R (sub ks S) = RN (B2R ks - B2R S)).
{ generalize (@Bminus_correct 53 1024 _ _ mode_NE ks S Fk FS).
  destruct (Rlt_bool _ _).
  - intros (HR & _). exact HR.
  - intros (HO & _). exfalso.
    revert F HO. unfold sub.
    destruct (Bminus mode_NE ks S); intros F HO; discriminate. }
rewrite HR in Hz.
assert (Hzb : IZR (-2147483648) < IZR z < IZR 2147483648)
  by (split; apply IZR_lt; lia).
(* [S / 2 <= ks <= 2 S]: otherwise [RN(ks - S)] is at least [S] or at most
   [-S / 2], as rounding is monotone and both bounds are floats. *)
assert (Hlo : B2R S / 2 <= B2R ks).
{ apply Rnot_lt_le. intros Hlt.
  assert (RN (B2R ks - B2R S) <= IZR (-3377699720527872)).
  { apply round_le_generic; [typeclasses eauto .. | apply format_int; lia |]. lra. }
  lra. }
assert (Hhi : B2R ks <= 2 * B2R S).
{ apply Rnot_lt_le. intros Hlt.
  assert (IZR 6755399441055744 <= RN (B2R ks - B2R S)).
  { apply round_ge_generic; [typeclasses eauto .. | apply format_int; lia |]. lra. }
  lra. }
(* So [ks - S] is exact (Sterbenz's lemma), and [ks = S + z] is an integer
   in [[2^52, 2^53)]. *)
assert (Ex : RN (B2R ks - B2R S) = B2R ks - B2R S).
{ apply round_generic; [typeclasses eauto|].
  apply sterbenz; [typeclasses eauto .. | apply generic_format_B2R | apply generic_format_B2R |].
  lra. }
rewrite Ex in Hz.
assert (Hks : B2R ks = IZR (6755399441055744 + z)) by (rewrite plus_IZR; lra).
(* The bits of [ks] are [c = E 2^52 + M] with the sign bit clear, where the
   biased exponent [E] is 1075, so that the value is [M + 2^52]. *)
destruct (to_bits_finite ks Fk) as (c & Hc & Hbits).
destruct (from_bits_finite (Bsign ks) c Hc) as (_ & _ & Hv).
rewrite <- Hbits, from_to_bits in Hv.
destruct (magnitude_bounds c (proj1 Hc)) as ((Hm0 & Hmlt) & Hmge).
assert (Hs : Bsign ks = false).
{ destruct (Bsign ks); [|reflexivity]. exfalso.
  assert (0 < B2R ks) by (rewrite Hks, plus_IZR; lra).
  lra. }
rewrite Hs in Hv, Hbits. cbv beta iota in Hv.
assert (B52 : bpow radix2 52 = 4503599627370496) by reflexivity.
assert (B53 : bpow radix2 53 = 9007199254740992) by reflexivity.
assert (HE : (c / 2 ^ 52 = 1075)%Z).
{ assert (H1 : (52 < c / 2 ^ 52 - 1022)%Z).
  { apply (lt_bpow radix2). apply Rle_lt_trans with (2 := Hmlt).
    rewrite B52, <- Hv, Hks, plus_IZR. lra. }
  assert (HE0 : (c / 2 ^ 52 <> 0)%Z) by lia.
  assert (H2 : (c / 2 ^ 52 - 1023 < 53)%Z).
  { apply (lt_bpow radix2). apply Rle_lt_trans with (1 := Hmge HE0).
    rewrite B53, <- Hv, Hks, plus_IZR. lra. }
  lia. }
destruct (split_52 c (proj1 Hc)) as (Hcs & _ & HM).
set (M := (c mod 2 ^ 52)%Z) in *.
rewrite Hcs, HE, magnitude_split in Hv by lia.
change (1075 =? 0)%Z with false in Hv. change (Z.max 1075 1 - 1075)%Z with 0%Z in Hv.
cbv iota in Hv. unfold F2R in Hv. cbn [Fnum Fexp] in Hv.
change (bpow radix2 0) with 1 in Hv. rewrite Rmult_1_r, Hks in Hv.
apply eq_IZR in Hv.
(* [to_bits ks = 1075 2^52 + 2^51 + z], which is [z] modulo 2^32. *)
assert (Hc2 : (to_bits ks = z + (1075 * 2 ^ 20 + 2 ^ 19) * 2 ^ 32)%Z).
{ rewrite Hbits. unfold sign_bit. cbv iota. lia. }
rewrite Hc2. unfold DyadicExp.low_i32. rewrite Z.mod_add by lia.
destruct (Z.ltb_spec (z mod 2 ^ 32) (2 ^ 31)); Z.div_mod_to_equations; lia.
Qed.

(** The operations below never come near [MAX]. *)
Lemma le_MAX : forall z, Rabs z <= 1000000000000000000000 -> Rabs z <= MAX.
Proof.
intros z Hz.
pose proof bpow_facts as (B0 & B1 & B2).
assert (B70 : bpow radix2 70 <= bpow radix2 1023) by (apply bpow_le; lia).
assert (B70' : 1000000000000000000000 <= bpow radix2 70)
  by (cbn [bpow radix_val radix2]; lra).
lra.
Qed.

(** ** The reduction *)

Theorem fast_exp_reduce :
  forall zh zl,
  is_finite zh = true -> is_finite zl = true -> Rabs (B2R zl) <= bpow radix2 (-40) ->
  -707 <= B2R zh <= 709 ->
  let kf := sub (add (mul zh (from_bits DyadicExp.INV)) DyadicExp.shifter) DyadicExp.shifter in
  let k := DyadicExp.to_i64 kf in
  let rh := sub zh (mul kf (from_bits DyadicExp.C1)) in
  let rl := sub zl (mul kf (from_bits DyadicExp.C2)) in
  is_finite kf = true /\ B2R kf = IZR k /\ (Z.abs k < 4194304)%Z /\
  (-1021 <= Z.shiftr k 12 <= 1022)%Z /\
  is_finite rh = true /\ is_finite rl = true /\
  B2R rh = B2R zh - IZR k * B2R (from_bits DyadicExp.C1) /\
  Rabs (B2R rh) <= 3 * bpow radix2 (-15) /\ Rabs (B2R rl) <= bpow radix2 (-20) /\
  Rabs (B2R zh + B2R zl - IZR k * (ln 2 / 4096) - (B2R rh + B2R rl)) <= bpow radix2 (-72).
Proof.
intros zh zl Fzh Fzl Hzl Hzh. cbv zeta.
(* The constants, as exact rationals. *)
assert (FI : is_finite (from_bits DyadicExp.INV) = true) by reflexivity.
assert (FS : is_finite DyadicExp.shifter = true) by reflexivity.
assert (F1 : is_finite (from_bits DyadicExp.C1) = true) by reflexivity.
assert (F2 : is_finite (from_bits DyadicExp.C2) = true) by reflexivity.
lit (from_bits DyadicExp.INV) HI.
lit DyadicExp.shifter HS.
lit (from_bits DyadicExp.C1) HC1r.
lit (from_bits DyadicExp.C2) HC2.
pose proof c1_exact as HC1.
pose proof c12_correct as HC12.
set (I := from_bits DyadicExp.INV) in *.
set (S := DyadicExp.shifter) in *.
set (c1 := from_bits DyadicExp.C1) in *.
set (c2 := from_bits DyadicExp.C2) in *.
assert (B : bpow radix2 (-14) = / 16384 /\ bpow radix2 (-15) = / 32768 /\
            bpow radix2 (-20) = / 1048576 /\ bpow radix2 (-21) = / 2097152 /\
            bpow radix2 (-31) = / 2147483648 /\ bpow radix2 (-40) = / 1099511627776 /\
            bpow radix2 (-72) = / 4722366482869645213696 /\
            bpow radix2 (-73) = / 9444732965739290427392 /\
            bpow radix2 (-74) = / 18889465931478580854784 /\
            bpow radix2 (-76) = / 75557863725914323419136 /\
            bpow radix2 22 = 4194304 /\ bpow radix2 52 = 4503599627370496 /\
            bpow radix2 53 = 9007199254740992)
  by (repeat split; reflexivity).
destruct B as (B14 & B15 & B20 & B21 & B31 & B40 & B72 & B73 & B74 & B76 & B22 & B52 & B53).
apply Rabs_le_inv in Hzl.
(* t = RN(zh INV) is within 2^-31 of zh INV, which is below 2^22 in
   magnitude. *)
assert (HzI : -4177861 <= B2R zh * B2R I <= 4189679) by (rewrite HI; lra).
destruct (mul_below_max zh I Fzh FI) as (FP & HP & _).
{ apply le_MAX, Rabs_le. lra. }
set (P := mul zh I) in *.
assert (EP : Rabs (B2R P - B2R zh * B2R I) <= bpow radix2 (-31)).
{ rewrite HP. apply (RN_err_le _ 22); [lia | reflexivity |]. apply Rabs_le. lra. }
rewrite HI in EP. apply Rabs_le_inv in EP.
(* t + SHIFTER is in [2^52, 2^53), so it rounds to an integer [m]. *)
destruct (add_below_max P S FP FS) as (FU & HU & _).
{ apply le_MAX, Rabs_le. rewrite HS. lra. }
set (U := add P S) in *.
assert (Hv : bpow radix2 52 <= B2R P + B2R S < bpow radix2 53) by (rewrite HS; lra).
rewrite (RN_int _ Hv) in HU.
pose proof (Znearest_half (fun x => negb (Z.even x)) (B2R P + B2R S)) as Hm.
set (m := Znearest (fun x => negb (Z.even x)) (B2R P + B2R S)) in *.
apply Rabs_le_inv in Hm.
(* [kf] is the integer [n = m - SHIFTER], within 1/2 of t. *)
set (n := (m - 6755399441055744)%Z).
assert (Hn : IZR n = B2R U - B2R S) by (unfold n; rewrite minus_IZR, HU, HS; lra).
assert (Hnr : -4177862 < IZR n < 4189681) by lra.
assert (Hn1 : (-4177862 < n < 4189681)%Z) by (split; apply lt_IZR; lra).
destruct (sub_below_max U S FU FS) as (Fkf & Hkf & _).
{ apply le_MAX, Rabs_le. rewrite <- Hn. lra. }
set (kf := sub U S) in *.
assert (Ekf : B2R kf = IZR n).
{ rewrite Hkf, <- Hn. apply round_generic; [typeclasses eauto|]. apply format_int. lia. }
assert (Ek : DyadicExp.to_i64 kf = n) by (apply to_i64_int; [exact Fkf | exact Ekf | lia]).
rewrite Ek.
(* [n = 0] unless [|zh| >= 2^-14]. *)
assert (Hsmall : n = 0%Z \/ bpow radix2 (-14) <= Rabs (B2R zh)).
{ destruct (Rlt_or_le (Rabs (B2R zh)) (bpow radix2 (-14))) as [H|H]; [left | right; exact H].
  apply Rabs_lt_inv in H.
  assert (H1 : (-1 < n < 1)%Z) by (split; apply lt_IZR; lra).
  lia. }
(* [kf C1] is exact: [C1] has 31 significant bits and [|n| < 2^22]. *)
destruct (mul_below_max kf c1 Fkf F1) as (FM1 & HM1 & _).
{ apply le_MAX, Rabs_le. rewrite Ekf, HC1r. lra. }
assert (EM1 : B2R (mul kf c1) = IZR n * B2R c1).
{ rewrite HM1, Ekf. apply round_generic; [typeclasses eauto|].
  rewrite HC1, <- Rmult_assoc, <- mult_IZR. apply format_mult; lia. }
(* zh - n C1 = zh (1 - INV C1) + (zh INV - t) C1 + (t - n) C1, at most
   709 * 6.2e-10 + 2^-31 C1 + C1 / 2 < 8.6e-5 in magnitude. *)
assert (Hrhb : -3 * bpow radix2 (-15) <= B2R zh - IZR n * B2R c1 <= 3 * bpow radix2 (-15))
  by (rewrite HC1r; lra).
destruct (sub_below_max zh (mul kf c1) Fzh FM1) as (Frh & Hrh & _).
{ apply le_MAX, Rabs_le. rewrite EM1. lra. }
set (rh := sub zh (mul kf c1)) in *.
assert (Erh : B2R rh = B2R zh - IZR n * B2R c1).
{ rewrite Hrh, EM1. apply round_generic; [typeclasses eauto|].
  pose proof (generic_format_B2R _ _ zh) as G.
  change (SpecFloat.fexp 53 1024) with fexp64 in G.
  destruct Hsmall as [Hn0 | Hz].
  - rewrite Hn0, Rmult_0_l, Rminus_0_r. exact G.
  - (* zh and n C1 are multiples of 2^-66, and so is their difference,
       which is below 2^-13 in magnitude. *)
    assert (Hce : (-66 <= cexp radix2 fexp64 (B2R zh))%Z).
    { change (-66)%Z with (FLT_exp (-1074) 53 (-13)).
      apply (cexp_ge_bpow radix2 fexp64 (B2R zh) (-13)). exact Hz. }
    destruct (format_mult_inv _ _ G Hce) as (a & Ha).
    assert (Hd : B2R zh - IZR n * B2R c1 =
                 IZR (a - n * 1488522235 * 8388608) * bpow radix2 (-66)).
    { rewrite Ha, HC1, minus_IZR, !mult_IZR.
      change (IZR 8388608) with (bpow radix2 23).
      replace (bpow radix2 (-43)) with (bpow radix2 23 * bpow radix2 (-66))
        by (rewrite <- bpow_plus; reflexivity).
      ring. }
    rewrite Hd. rewrite Hd in Hrhb.
    assert (B66 : bpow radix2 (-66) = / 73786976294838206464) by reflexivity.
    rewrite B66, B15 in Hrhb.
    apply format_mult; [|lia].
    set (M := (a - n * 1488522235 * 8388608)%Z) in *.
    assert (HM : (- 6755399441055744 <= M <= 6755399441055744)%Z)
      by (split; apply le_IZR; lra).
    lia. }
(* [RN(n C2)] is within 2^-74 of [n C2], which is below 4.34e-7 in
   magnitude. *)
assert (HnC2 : - 4334 / 10000000000 <= IZR n * B2R c2 <= 4334 / 10000000000)
  by (rewrite HC2; lra).
destruct (mul_below_max kf c2 Fkf F2) as (FM2 & HM2 & _).
{ apply le_MAX, Rabs_le. rewrite Ekf. lra. }
set (m2 := mul kf c2) in *.
assert (E1 : Rabs (B2R m2 - IZR n * B2R c2) <= bpow radix2 (-74)).
{ rewrite HM2, Ekf. apply (RN_err_le _ (-21)); [lia | reflexivity |]. apply Rabs_le. lra. }
apply Rabs_le_inv in E1.
(* [rl = RN(zl - RN(n C2))] is within 2^-73 of [zl - RN(n C2)], which is
   below 2^-20 in magnitude. *)
destruct (sub_below_max zl m2 Fzl FM2) as (Frl & Hrl & _).
{ apply le_MAX, Rabs_le. lra. }
set (rl := sub zl m2) in *.
assert (E2 : Rabs (B2R rl - (B2R zl - B2R m2)) <= bpow radix2 (-73)).
{ rewrite Hrl. apply (RN_err_le _ (-20)); [lia | reflexivity |]. apply Rabs_le. lra. }
apply Rabs_le_inv in E2.
(* |n (C1 + C2 - c)| <= 2^22 2^-98. *)
assert (E3 : Rabs (IZR n * (B2R c1 + B2R c2 - ln 2 / 4096)) <= bpow radix2 (-76)).
{ rewrite Rabs_mult.
  replace (bpow radix2 (-76)) with (bpow radix2 22 * bpow radix2 (-98))
    by (rewrite <- bpow_plus; reflexivity).
  apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | | exact HC12].
  rewrite <- abs_IZR. rewrite B22. apply IZR_le. lia. }
apply Rabs_le_inv in E3.
split; [exact Fkf|]. split; [exact Ekf|]. split; [lia|].
split.
{ rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12)%Z with 4096%Z.
  Z.div_mod_to_equations. lia. }
split; [exact Frh|]. split; [exact Frl|]. split; [exact Erh|].
split; [rewrite Erh; apply Rabs_le; lra|].
split; [apply Rabs_le; lra|].
(* zh + zl - n c - (rh + rl)
   = n (C1 + C2 - c) + (RN(n C2) - n C2) - (rl - (zl - RN(n C2))). *)
replace (B2R zh + B2R zl - IZR n * (ln 2 / 4096) - (B2R rh + B2R rl))
  with (IZR n * (B2R c1 + B2R c2 - ln 2 / 4096) + (B2R m2 - IZR n * B2R c2)
        - (B2R rl - (B2R zl - B2R m2)))
  by (rewrite Erh; ring).
apply Rabs_le. lra.
Qed.
