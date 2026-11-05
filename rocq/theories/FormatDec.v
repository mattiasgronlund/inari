(** * [format_fixed] and [format_sci] round the bounds of [{}] and [{:e}]

    [format_fixed x p up] is a finite nonzero [x] rounded to a multiple of
    [10^-p], and [format_sci x p up] is [x] rounded to [p + 1] significant
    decimal digits, toward +inf if [up] and toward -inf otherwise, as the
    digits [d] of the magnitude and the exponent [k] of 10. So they are as
    tight as their directions allow. [src/format.rs] writes [d] and [k] as
    the text, with [p = 6] for [{}] and [p = 16] for [{:e}] without a
    precision. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Spec FormatCut.
From Inari Require NatOps.

Open Scope Z_scope.

(** The checked [i64] operations of [format_fixed] and [format_sci] see
    only small values: numbers of digits and exponents of 10 of a few
    thousand at most in magnitude, and precisions capped at 1100. *)
Lemma checked_i_64 :
  forall z, -1000000 <= z <= 1000000 -> checked_i 64 z = Some z.
Proof.
intros z Hz. apply checked_i_ok.
change (2^(64 - 1)) with 9223372036854775808. lia.
Qed.

(** [z as i64] of a small [z >= 0] keeps it. *)
Lemma as_i64_small :
  forall z, 0 <= z <= 1000000 -> (z + 2^63) mod 2^64 - 2^63 = z.
Proof.
intros z Hz. rewrite Z.mod_small.
- lia.
- change (2^63) with 9223372036854775808.
  change (2^64) with 18446744073709551616. lia.
Qed.

(** Rounding a number [m * beta^e] that the format holds, which it does
    if its exponent [e] is at least the one that the format gives it,
    keeps the number. *)
Lemma round_F2R_exact :
  forall beta fexp, Valid_exp fexp -> forall (b : bool) m e,
  (m <> 0 -> cexp beta fexp (F2R (Float beta m e)) <= e) ->
  round beta fexp (if b then Zceil else Zfloor) (IZR m * bpow beta e) =
  (IZR m * bpow beta e)%R.
Proof.
intros beta fexp Hv b m e H.
change (IZR m * bpow beta e)%R with (F2R (Float beta m e)).
destruct b; apply round_generic; try typeclasses eauto;
  now apply generic_format_F2R.
Qed.

Theorem format_fixed_correct :
  forall x p up, is_finite x = true -> eq x zero = false -> 0 <= p < 2^64 ->
  exists d k, format_fixed x p up = Some (d, k) /\ 0 <= d /\ - p <= k <= 0 /\
  cond_Ropp (Bsign x) (IZR d * bpow radix10 k)%R =
  round radix10 (FIX_exp (- p)) (if up then Zceil else Zfloor) (B2R x).
Proof.
intros x p up Hx Hz Hp.
destruct (format_exact_dec_correct x Hx Hz) as (n & s & Hex & Hn & Hs & Hxr).
unfold format_fixed. rewrite Hex. cbv beta iota zeta.
(* [p.min(ALL_DIGITS) as i64] is [min p 1100], and [-c] fits an [i64]. *)
rewrite (as_i64_small (Z.min p 1100)) by lia.
rewrite checked_i_64 by lia.
destruct (format_cut_dec_correct n s (- Z.min p 1100) (format_away x up))
  as (d & Hcut & Hd & Hr);
  [lia | change (2^62) with 4611686018427387904; lia ..
  | change (2^32) with 4294967296; lia |].
exists d, (Z.max s (- Z.min p 1100)).
split; [exact Hcut |]. split; [exact Hd |].
(* [s] lies in [-1074, 0], so [max s (-min p 1100)] lies in [-p, 0]. *)
split; [lia |].
rewrite Hxr, round_sign. f_equal.
unfold format_away in Hr. rewrite Hr.
destruct (Z.le_gt_cases p 1100) as [Hp1 | Hp1].
- (* The cap does not apply: the cut is at [10^-p]. *)
  now rewrite Z.min_l by lia.
- (* With [p > 1100], [10^-1100] and [10^-p] both divide [10^s], as
     [s >= -1074]: both roundings keep [n * 10^s]. *)
  rewrite Z.min_r by lia.
  rewrite !round_F2R_exact; try typeclasses eauto; try reflexivity;
    intros _; unfold cexp, FIX_exp; lia.
Qed.

Theorem format_sci_correct :
  forall x p up, is_finite x = true -> eq x zero = false -> 0 <= p < 2^64 ->
  exists d k, format_sci x p up = Some (d, k) /\ 0 <= d /\
  cond_Ropp (Bsign x) (IZR d * bpow radix10 k)%R =
  round radix10 (FLX_exp (p + 1)) (if up then Zceil else Zfloor) (B2R x).
Proof.
intros x p up Hx Hz Hp.
destruct (format_exact_dec_correct x Hx Hz) as (n & s & Hex & Hn & Hs & Hxr).
(* [n] has between 1 and 767 digits. *)
assert (Hdg : 1 <= Zdigits radix10 n <= 767).
{ split.
  - assert (0 < Zdigits radix10 n) by (apply Zdigits_gt_0; lia). lia.
  - apply Zdigits_le_Zpower. rewrite Z.abs_eq by lia.
    change (Zpower radix10 767) with (10^767). lia. }
(* The magnitude [n * 10^s] lies in [10^(digits n + s - 1), 10^(digits n + s)). *)
assert (Hmag :
  mag radix10 (IZR n * bpow radix10 s) = Zdigits radix10 n + s :> Z).
{ change (IZR n * bpow radix10 s)%R with (F2R (Float radix10 n s)).
  apply mag_F2R_Zdigits. lia. }
unfold format_sci. rewrite Hex. cbv beta iota zeta.
rewrite NatOps.digits10_z_correct by lia. cbv beta iota zeta.
(* [n.digits10() as i64] and [p.min(ALL_DIGITS) as i64] keep their
   values, and the exponents [t1], [t2] and [t] fit an [i64]. *)
rewrite (as_i64_small (Zdigits radix10 n)) by lia.
rewrite checked_i_64 by lia. cbv beta iota.
rewrite checked_i_64 by lia. cbv beta iota.
rewrite (as_i64_small (Z.min p 1100)) by lia.
rewrite checked_i_64 by lia.
set (t := Zdigits radix10 n + s - 1 - Z.min p 1100).
destruct (format_cut_dec_correct n s t (format_away x up))
  as (d & Hcut & Hd & Hr);
  [lia | change (2^62) with 4611686018427387904; unfold t; lia ..
  | change (2^32) with 4294967296; unfold t; lia |].
exists d, (Z.max s t).
split; [exact Hcut |]. split; [exact Hd |].
rewrite Hxr, round_sign. f_equal.
unfold format_away in Hr. rewrite Hr.
destruct (Z.le_gt_cases p 1100) as [Hp1 | Hp1].
- (* The cap does not apply: [t] is the exponent [mag - (p + 1)] that
     [FLX_exp (p + 1)] gives [n * 10^s]. *)
  symmetry. apply round_FLX_FIX.
  rewrite Hmag. unfold t. rewrite Z.min_l by lia. lia.
- (* With [p > 1100], [n] has fewer than [p + 1] digits and [t < s]:
     both roundings keep [n * 10^s]. *)
  assert (Hprec : Prec_gt_0 (p + 1)) by (unfold Prec_gt_0; lia).
  rewrite !round_F2R_exact; try typeclasses eauto; try reflexivity;
    intros Hn0; unfold cexp.
  + unfold FLX_exp. rewrite mag_F2R_Zdigits by exact Hn0. lia.
  + unfold FIX_exp, t. rewrite Z.min_r by lia. lia.
Qed.
