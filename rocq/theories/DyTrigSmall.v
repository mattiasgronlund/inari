(** * Helpers for the rules of [sin], [cos] and [tan] of small arguments

    [cos_small], [sin_small] and [tan_small] of [DyadicTrig] in [Model.v]
    read the bits of [|x|], compute with them in integers, and return an
    [f64] by its bits. These lemmas give the value of a bit pattern of a
    normal [f64] ([magnitude_normal]), the fields of the pattern of [|x|]
    ([small_bits]), the roundings of a real that lies strictly between the
    [f64]s of two consecutive patterns, or of its opposite ([bits_bracket]
    and [bits_bracket_opp]), and the cube of [cube] ([cube_correct]).
    [DyCosSmall.v], [DySinSmall.v] and [DyTanSmall.v] use them. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Encoding Decompose MpfrRound DyExpRules.

Open Scope R_scope.

Local Notation rnd_of up := (if up then RNDU else RNDD).

(** The value of the pattern with the biased exponent [be > 0] and the
    stored significand [M], for [M] up to [2^52]: [M = 2^52] is the
    pattern of [2^(be - 1022)], the first of the next binade. *)
Lemma magnitude_normal :
  forall be M, (1 <= be)%Z -> (0 <= M <= 2^52)%Z ->
  magnitude (be * 2^52 + M) = IZR (M + 2^52) * bpow radix2 (be - 1075).
Proof.
intros be M Hbe HM.
destruct (Z.eq_dec M (2^52)) as [HM52|HM52].
- (* The significand [2^52] carries into the exponent: the pattern is
     [(be + 1) 2^52 + 0], of value [2^52 2^(be + 1 - 1075)]. *)
  subst M.
  replace (be * 2^52 + 2^52)%Z with ((be + 1) * 2^52 + 0)%Z by ring.
  rewrite magnitude_split by (simpl Z.pow; lia).
  replace (be + 1 =? 0)%Z with false by lia.
  replace (Z.max (be + 1) 1 - 1075)%Z with (1 + (be - 1075))%Z by lia.
  unfold F2R; cbn [Fnum Fexp].
  rewrite bpow_plus. change (bpow radix2 1) with 2.
  rewrite Z.add_0_l, plus_IZR. ring.
- rewrite magnitude_split by lia.
  replace (be =? 0)%Z with false by lia.
  replace (Z.max be 1) with be by lia.
  reflexivity.
Qed.

(** The pattern of [|x|], for a finite [x], is that of a finite [f64]
    with the sign bit clear, its value is [|x|], and the shift and the mask
    of [Model.v] give its biased exponent and its stored significand. *)
Lemma small_bits :
  forall x, is_finite x = true ->
  (0 <= to_bits (fabs x) < 2047 * 2^52)%Z /\
  B2R (fabs x) = magnitude (to_bits (fabs x)) /\
  Z.shiftr (to_bits (fabs x)) 52 = (to_bits (fabs x) / 2^52)%Z /\
  Z.land (to_bits (fabs x)) (Z.shiftl 1 52 - 1) = (to_bits (fabs x) mod 2^52)%Z.
Proof.
intros x Fx.
assert (Fa : is_finite (fabs x) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fx).
destruct (to_bits_finite (fabs x) Fa) as (c & Hc & Hb).
(* [|x|] has the sign bit clear, so its pattern is [c] itself. *)
replace (Bsign (fabs x)) with false in Hb by (symmetry; apply Bsign_Babs).
change (sign_bit false) with 0%Z in Hb. rewrite Z.add_0_l in Hb.
destruct (from_bits_finite false c Hc) as (_ & _ & E).
change (sign_bit false) with 0%Z in E. rewrite Z.add_0_l in E.
rewrite <- Hb, from_to_bits in E. rewrite Hb in E.
rewrite Hb.
split; [exact Hc|]. split; [exact E|]. split.
- apply Z.shiftr_div_pow2. lia.
- change (Z.shiftl 1 52 - 1)%Z with (Z.ones 52).
  apply Z.land_ones. lia.
Qed.

(** The [f64]s of the patterns [c] and [c + 1] are finite and have the
    values [magnitude c] and [magnitude (c + 1)], the [f64] after the
    first ([magnitude_succ]). *)
Lemma bits_pair :
  forall c, (0 <= c)%Z -> (c + 1 < 2047 * 2^52)%Z ->
  is_finite (from_bits c) = true /\ is_finite (from_bits (c + 1)) = true /\
  B2R (from_bits c) = magnitude c /\ B2R (from_bits (c + 1)) = magnitude (c + 1) /\
  magnitude (c + 1) = succ radix2 (SpecFloat.fexp 53 1024) (magnitude c).
Proof.
intros c Hc Hc1.
destruct (from_bits_finite false c ltac:(lia)) as (Flo & _ & Elo).
destruct (from_bits_finite false (c + 1) ltac:(lia)) as (Fhi & _ & Ehi).
change (sign_bit false) with 0%Z in Flo, Elo, Fhi, Ehi.
rewrite Z.add_0_l in Flo, Elo, Fhi, Ehi.
split; [exact Flo|]. split; [exact Fhi|]. split; [exact Elo|]. split; [exact Ehi|].
change (SpecFloat.fexp 53 1024) with fexp64.
apply magnitude_succ. exact Hc.
Qed.

(** A real strictly between the values of the patterns [c] and [c + 1]
    rounds down to the [f64] of [c] and up to that of [c + 1]. *)
Lemma bits_bracket :
  forall (c : Z) (up : bool) r, (0 <= c)%Z -> (c + 1 < 2047 * 2^52)%Z ->
  magnitude c < r < magnitude (c + 1) ->
  mpfr_round f64_format (rnd_of up) r (with_val (from_bits (c + Z.b2z up))).
Proof.
intros c up r Hc Hc1 Hr.
destruct (bits_pair c Hc Hc1) as (Flo & Fhi & Elo & Ehi & Hs).
replace (from_bits (c + Z.b2z up)) with (if up then from_bits (c + 1) else from_bits c)
  by (destruct up; cbn [Z.b2z]; [reflexivity | rewrite Z.add_0_r; reflexivity]).
apply (rnd_bracket (from_bits c) (from_bits (c + 1)) up r Flo Fhi).
- rewrite Elo, Ehi. exact Hs.
- rewrite Elo, Ehi. exact Hr.
Qed.

(** Its opposite rounds up to minus the first and down to minus the
    second, the [f64]s of [c + 1] and [c] in the other direction. *)
Lemma bits_bracket_opp :
  forall (c : Z) (up : bool) r, (0 <= c)%Z -> (c + 1 < 2047 * 2^52)%Z ->
  magnitude c < r < magnitude (c + 1) ->
  mpfr_round f64_format (rnd_of up) (- r) (with_val (opp (from_bits (c + Z.b2z (negb up))))).
Proof.
intros c up r Hc Hc1 Hr.
destruct (bits_pair c Hc Hc1) as (Flo & Fhi & Elo & Ehi & Hs).
replace (opp (from_bits (c + Z.b2z (negb up))))
  with (if up then opp (from_bits c) else opp (from_bits (c + 1)))
  by (destruct up; cbn [negb Z.b2z]; [rewrite Z.add_0_r; reflexivity | reflexivity]).
(* [- r] lies between [- magnitude (c + 1)] and [- magnitude c], and the
   [f64] after the first is the second: [succ (- y) = - pred y] and
   [pred (succ (magnitude c)) = magnitude c]. *)
assert (Gc : generic_format radix2 (SpecFloat.fexp 53 1024) (magnitude c))
  by (rewrite <- Elo; apply generic_format_B2R).
apply (rnd_bracket (opp (from_bits (c + 1))) (opp (from_bits c)) up (- r)).
- unfold opp. rewrite is_finite_Bopp. exact Fhi.
- unfold opp. rewrite is_finite_Bopp. exact Flo.
- unfold opp. rewrite !B2R_Bopp, Elo, Ehi, Hs.
  change (SpecFloat.fexp 53 1024) with fexp64 in Gc |- *.
  rewrite succ_opp, pred_succ by first [exact Gc | typeclasses eauto].
  reflexivity.
- unfold opp. rewrite !B2R_Bopp, Elo, Ehi. lra.
Qed.

(** [cube m] splits [m^3] at bit 64, for [0 <= m < 2^53]. *)
Lemma cube_correct :
  forall m, (0 <= m < 2^53)%Z ->
  (fst (DyadicTrig.cube m) * 2^64 + snd (DyadicTrig.cube m) = m ^ 3)%Z /\
  (0 <= snd (DyadicTrig.cube m) < 2^64)%Z /\ (0 <= fst (DyadicTrig.cube m))%Z.
Proof.
intros m Hm.
unfold DyadicTrig.cube. cbn [fst snd].
rewrite !Z.shiftr_div_pow2 by lia.
assert (H64 : (0 < 2^64)%Z) by reflexivity.
(* [m^2 = 2^64 a + b] and [b m = 2^64 c + d], so
   [m^3 = 2^64 a m + b m = 2^64 (a m + c) + d]. *)
assert (Hsq : (0 <= m * m)%Z) by (apply Z.mul_nonneg_nonneg; lia).
pose proof (Z.div_mod (m * m) (2^64) ltac:(lia)) as Ea.
pose proof (Z.mod_pos_bound (m * m) (2^64) H64) as Hb.
pose proof (Z.div_pos (m * m) (2^64) Hsq H64) as Ha.
set (a := ((m * m) / 2^64)%Z) in *. set (b := ((m * m) mod 2^64)%Z) in *.
assert (Hbm : (0 <= b * m)%Z) by (apply Z.mul_nonneg_nonneg; lia).
pose proof (Z.div_mod (b * m) (2^64) ltac:(lia)) as Ec.
pose proof (Z.mod_pos_bound (b * m) (2^64) H64) as Hd.
pose proof (Z.div_pos (b * m) (2^64) Hbm H64) as Hc.
set (c := ((b * m) / 2^64)%Z) in *. set (d := ((b * m) mod 2^64)%Z) in *.
clearbody a b c d.
split; [|split].
- replace (m ^ 3)%Z with (m * m * m)%Z by ring.
  rewrite Ea. lia.
- exact Hd.
- apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg|]; lia.
Qed.
