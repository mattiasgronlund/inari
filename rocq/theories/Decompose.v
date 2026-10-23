(** * [eq], [decompose], [pow2] and [of_u64] against Flocq *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Spec.

Open Scope Z_scope.

(** [x == 0.0] holds exactly for the two zeros. *)
Lemma eq_zero_iff : forall x, eq x zero = true <-> exists s, x = B754_zero s.
Proof.
intros x. split.
- (* [eq] compares an infinity or a nonzero float with 0 by its sign, and
     a NaN with nothing. *)
  destruct x as [s|[|]| |[|] m e H]; intros Hx; try discriminate Hx.
  now exists s.
- intros (s & ->). destruct s; reflexivity.
Qed.

(** The operands that [add1_ru_slow] adds in the default rounding mode
    are +-inf, NaN or zeros, and then the rounding mode does not matter. *)
Lemma add_special :
  forall x y,
  negb (is_finite x && is_finite y) || eq x zero || eq y zero = true ->
  add x y = Bplus mode_UP x y.
Proof.
intros x y H.
unfold add.
(* [Bplus] looks at the rounding mode only for two finite nonzero
   operands, which [H] excludes, and for two zeros of opposite signs,
   where only [mode_DN] differs. *)
destruct x as [sx|sx| |[|] mx ex Hx], y as [sy|sy| |[|] my ey Hy];
  try discriminate H; reflexivity.
Qed.

(** ** [decompose] *)

(** The fields of a finite pattern [sign_bit s + c] that [decompose]
    extracts: the biased exponent, the stored significand and the sign. *)
Lemma biased_finite :
  forall s c, 0 <= c < 2047 * 2^52 ->
  Z.land (Z.shiftr (sign_bit s + c) 52) 0x7ff = c / 2^52.
Proof.
intros s c Hc.
rewrite Z.shiftr_div_pow2 by easy.
change 0x7ff with (Z.ones 11).
rewrite Z.land_ones by easy.
unfold sign_bit. destruct s; zlia.
Qed.

Lemma frac_finite :
  forall s c, 0 <= c < 2047 * 2^52 ->
  Z.land (sign_bit s + c) (Z.shiftl 1 52 - 1) = c mod 2^52.
Proof.
intros s c Hc.
change (Z.shiftl 1 52 - 1) with (Z.ones 52).
rewrite Z.land_ones by easy.
unfold sign_bit. destruct s; zlia.
Qed.

Lemma sign_finite :
  forall s c, 0 <= c < 2047 * 2^52 ->
  negb (Z.shiftr (sign_bit s + c) 63 =? 0) = s.
Proof.
intros s c Hc.
rewrite Z.shiftr_div_pow2 by easy.
replace ((sign_bit s + c) / 2^63) with (if s then 1 else 0)
  by (unfold sign_bit; destruct s; zlia).
now destruct s.
Qed.

(** Setting the implicit bit of a stored significand adds [2^52]. *)
Lemma lor_implicit :
  forall a, 0 <= a < 2^52 -> Z.lor a (Z.shiftl 1 52) = a + 2^52.
Proof.
intros a Ha.
change (Z.shiftl 1 52) with (2^52).
(* [a] has no bit in common with [2^52], as [a = a & (2^52 - 1)]. *)
assert (H0 : Z.land a (2^52) = 0).
{ replace a with (Z.land a (Z.ones 52))
    by (rewrite Z.land_ones by easy; now apply Z.mod_small).
  rewrite <- Z.land_assoc.
  change (Z.land (Z.ones 52) (2^52)) with 0.
  apply Z.land_0_r. }
now rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor by exact H0.
Qed.

(** [decompose] gives the sign, the integral significand and the exponent
    of a finite nonzero float. *)
Theorem decompose_correct :
  forall x, is_finite x = true -> eq x zero = false ->
  let '(s, m, e) := Generic.decompose x in
  s = Bsign x /\ 0 < m < 2^53 /\ -1074 <= e <= 971 /\
  B2R x = cond_Ropp s (F2R (Float radix2 m e)).
Proof.
intros x Fx Hz.
destruct (to_bits_finite x Fx) as (c & Hc & Hb).
destruct (from_bits_finite (Bsign x) c Hc) as (_ & _ & Hx).
rewrite <- Hb, from_to_bits in Hx.
(* The pattern 0 is a zero, which [eq] does not tell from [0.0]. *)
assert (Hc0 : c <> 0).
{ intros ->.
  unfold eq in Hz. rewrite Beqb_correct in Hz by easy.
  rewrite Req_bool_true in Hz; [discriminate|].
  rewrite Hx, magnitude_0. change (B2R zero) with 0%R.
  destruct (Bsign x); ring. }
unfold magnitude in Hx.
unfold Generic.decompose. cbv zeta.
rewrite Hb, biased_finite, frac_finite, sign_finite by exact Hc.
destruct (Z.eqb_spec (c / 2^52) 0) as [HE0|HE0]; cbv beta iota.
- (* A subnormal: no implicit bit, and the scale of the biased exponent 1,
     which is the [-1074] of [decompose]. *)
  replace (mant c) with (c mod 2^52) in Hx by (unfold mant; now rewrite HE0).
  replace (expo c) with (-1074) in Hx by (unfold expo; now rewrite HE0).
  split; [reflexivity|]. split; [zlia|]. split; [lia|].
  rewrite Hx. now destruct (Bsign x).
- (* A normal float: the implicit bit is set. *)
  rewrite lor_implicit by zlia.
  replace (mant c) with (c mod 2^52 + 2^52) in Hx
    by (unfold mant; now rewrite (proj2 (Z.eqb_neq _ _) HE0)).
  replace (expo c) with (c / 2^52 - 1075) in Hx by (unfold expo; zlia).
  split; [reflexivity|]. split; [zlia|]. split; [zlia|].
  rewrite Hx. now destruct (Bsign x).
Qed.

(** ** [pow2] *)

(** [pow2 e] is [2^e]: the biased exponent [e + 1023] over a zero stored
    significand if [2^e] is normal, and the stored significand
    [2^(e + 1074)] if it is subnormal. *)
Theorem pow2_correct :
  forall e, -1074 <= e <= 1023 ->
  exists p, Generic.pow2 e = Some p /\
    is_finite p = true /\ Bsign p = false /\ B2R p = bpow radix2 e.
Proof.
intros e He.
unfold Generic.pow2.
destruct (Z.leb_spec (-1022) e) as [Hn|Hs]; cbv beta iota.
- rewrite checked_i_ok by (simpl; lia). cbv beta iota.
  rewrite Z.mod_small by (simpl Z.pow; lia).
  rewrite shl_ok by (simpl Z.pow; lia).
  destruct (from_bits_finite false ((e + 1023) * 2^52)) as (F & S & R);
    [simpl Z.pow; lia|].
  cbn [sign_bit] in F, S, R. rewrite Z.add_0_l in F, S, R.
  exists (from_bits ((e + 1023) * 2^52)).
  split; [reflexivity|]. split; [exact F|]. split; [exact S|].
  rewrite R.
  replace ((e + 1023) * 2^52) with ((e + 1023) * 2^52 + 0) by ring.
  rewrite magnitude_split by (simpl Z.pow; lia).
  rewrite (proj2 (Z.eqb_neq (e + 1023) 0)) by lia.
  replace (Z.max (e + 1023) 1 - 1075) with (e - 52) by lia.
  (* [2^52 * 2^(e - 52)] *)
  unfold F2R; cbn [Fnum Fexp].
  rewrite Z.add_0_l, (IZR_Zpower radix2) by easy.
  rewrite <- bpow_plus. f_equal. ring.
- rewrite checked_i_ok by (simpl; lia). cbv beta iota.
  assert (Hc : 0 < 2^(e + 1074) < 2^52)
    by (split; [apply Z.pow_pos_nonneg | apply Z.pow_lt_mono_r]; lia).
  rewrite shl_ok by (simpl Z.pow in *; lia).
  rewrite Z.mul_1_l.
  destruct (from_bits_finite false (2^(e + 1074))) as (F & S & R);
    [simpl Z.pow in *; lia|].
  cbn [sign_bit] in F, S, R. rewrite Z.add_0_l in F, S, R.
  exists (from_bits (2^(e + 1074))).
  split; [reflexivity|]. split; [exact F|]. split; [exact S|].
  rewrite R.
  replace (2^(e + 1074)) with (0 * 2^52 + 2^(e + 1074)) by ring.
  rewrite magnitude_split by lia.
  cbn [Z.eqb]. change (Z.max 0 1 - 1075) with (-1074).
  (* [2^(e + 1074) * 2^-1074] *)
  unfold F2R; cbn [Fnum Fexp].
  rewrite (IZR_Zpower radix2) by lia.
  rewrite <- bpow_plus. f_equal. ring.
Qed.

(** ** [of_u64] *)

(** [k as f64] is exact for [k <= 2^53]. *)
Theorem of_u64_exact :
  forall k, 0 <= k <= 2^53 ->
  is_finite (of_u64 k) = true /\ Bsign (of_u64 k) = false /\
  B2R (of_u64 k) = IZR k.
Proof.
intros k Hk.
assert (Hk0 : (0 <= IZR k)%R) by (apply IZR_le; lia).
(* [k] is a float: below [2^53] it fits the significand, and [2^53] is a
   power of two. *)
assert (Fk : generic_format radix2 fexp64 (IZR k)).
{ destruct (Z.eq_dec k (2^53)) as [->|Hk53].
  - rewrite (IZR_Zpower radix2) by easy.
    apply generic_format_FLT_bpow; [typeclasses eauto | lia].
  - apply generic_format_FLT.
    apply FLT_spec with (Float radix2 k 0).
    + unfold F2R; simpl. ring.
    + cbn [Fnum]. rewrite Z.abs_eq by lia. simpl Z.pow in *. lia.
    + cbn [Fexp]. lia. }
unfold of_u64.
pose proof (binary_normalize_correct 53 1024 prec_gt_0_53 prec_lt_emax_53_1024
  mode_NE k 0 false) as H.
cbv zeta in H.
change (SpecFloat.fexp 53 1024) with fexp64 in H.
replace (F2R (Float radix2 k 0)) with (IZR k) in H
  by (unfold F2R; simpl; ring).
rewrite (round_generic _ _ _ (IZR k) Fk) in H.
rewrite Rlt_bool_true in H.
2: { (* [k <= 2^53 < 2^1024] *)
  rewrite Rabs_pos_eq by exact Hk0.
  apply Rle_lt_trans with (IZR (2^53)). apply IZR_le; lia.
  rewrite (IZR_Zpower radix2) by easy.
  apply bpow_lt. lia. }
destruct H as (HR & HF & HS).
split; [exact HF|]. split; [|exact HR].
rewrite HS.
destruct (Rcompare_spec (IZR k) 0) as [Hlt|Heq|Hgt]; [lra|reflexivity..].
Qed.
