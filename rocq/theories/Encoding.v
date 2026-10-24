(** * [exponent], [is_finite] and [step_up] against Flocq

    The functions in [Model.v] that look at the bits of a float: [exponent]
    is bounded by the magnitude of [x], [is_finite] is Flocq's, and
    [step_up] is Flocq's [Bsucc], i.e. IEEE 754 [nextUp], on finite floats. *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Flocq Require IEEE754.Binary IEEE754.Bits.
From Inari Require Import Model.

Open Scope Z_scope.

(** Linear arithmetic with division and remainder by powers of two. *)
Ltac zlia := Z.div_mod_to_equations; simpl Z.pow in *; lia.

(** The binary64 format: 53 bits of precision, subnormals down to 2^-1074,
    and no bound on the exponent (overflow is handled separately). *)
Notation fexp64 := (FLT_exp (-1074) 53).

(** ** Bit patterns

    A finite float is [sign_bit s + c], where [0 <= c < 2047 * 2^52] holds
    the biased exponent [c / 2^52] and the stored significand
    [c mod 2^52]. *)

Definition sign_bit (s : bool) : Z := if s then 2^63 else 0.

(** The integral significand and the exponent of the value of [c]: the
    implicit bit is 1 unless the biased exponent is 0, and the biased
    exponents 0 and 1 have the same scale. *)
Definition mant (c : Z) : Z :=
  if c / 2^52 =? 0 then c mod 2^52 else c mod 2^52 + 2^52.
Definition expo (c : Z) : Z := Z.max (c / 2^52) 1 - 1075.

(** The value of the bit pattern [c] with the sign bit clear. *)
Definition magnitude (c : Z) : R := F2R (Float radix2 (mant c) (expo c)).

Lemma magnitude_split :
  forall E M, 0 <= E -> 0 <= M < 2^52 ->
  magnitude (E * 2^52 + M) =
    F2R (Float radix2 (if E =? 0 then M else M + 2^52) (Z.max E 1 - 1075)).
Proof.
intros E M HE HM.
unfold magnitude, mant, expo.
replace ((E * 2^52 + M) / 2^52) with E by zlia.
replace ((E * 2^52 + M) mod 2^52) with M by zlia.
reflexivity.
Qed.

(** Every [c >= 0] splits into a biased exponent and a stored significand. *)
Lemma split_52 :
  forall c, 0 <= c ->
  c = c / 2^52 * 2^52 + c mod 2^52 /\ 0 <= c / 2^52 /\ 0 <= c mod 2^52 < 2^52.
Proof. intros c Hc. zlia. Qed.

(** [m * 2^e < 2^(k + e)] if [m < 2^k]. *)
Lemma F2R_lt_bpow_plus :
  forall m e k, 0 <= k -> 0 <= m < 2^k ->
  (F2R (Float radix2 m e) < bpow radix2 (k + e))%R.
Proof.
intros m e k Hk Hm.
unfold F2R; simpl.
rewrite bpow_plus.
apply Rmult_lt_compat_r. apply bpow_gt_0.
rewrite <- (IZR_Zpower radix2) by easy.
apply IZR_lt. apply Hm.
Qed.

(** [2^(k + e) <= m * 2^e] if [2^k <= m]. *)
Lemma bpow_plus_le_F2R :
  forall m e k, 0 <= k -> 2^k <= m ->
  (bpow radix2 (k + e) <= F2R (Float radix2 m e))%R.
Proof.
intros m e k Hk Hm.
unfold F2R; simpl.
rewrite bpow_plus.
apply Rmult_le_compat_r. apply bpow_ge_0.
rewrite <- (IZR_Zpower radix2) by easy.
apply IZR_le. apply Hm.
Qed.

Lemma magnitude_0 : magnitude 0 = 0%R.
Proof. apply F2R_0. Qed.

(** The largest pattern before the infinities is [MAX], and the next one
    would be [2^1024]. *)
Lemma magnitude_2047 : magnitude (2047 * 2^52) = bpow radix2 1024.
Proof.
unfold magnitude.
change (mant (2047 * 2^52)) with (radix2 ^ 52).
change (expo (2047 * 2^52)) with 972.
unfold F2R; cbn [Fnum Fexp].
rewrite IZR_Zpower by easy.
now rewrite <- bpow_plus.
Qed.

(** [0 <= magnitude c < 2^(E - 1022)], where [E] is the biased exponent,
    and [2^(E - 1023) <= magnitude c] if the float is normal. *)
Lemma magnitude_bounds :
  forall c, 0 <= c ->
  (0 <= magnitude c < bpow radix2 (c / 2^52 - 1022))%R /\
  (c / 2^52 <> 0 -> (bpow radix2 (c / 2^52 - 1023) <= magnitude c)%R).
Proof.
intros c Hc.
destruct (split_52 c Hc) as (Hcs & HE & HM).
set (E := c / 2^52) in *. set (M := c mod 2^52) in *.
replace (magnitude c) with (magnitude (E * 2^52 + M)) by now rewrite <- Hcs.
clearbody E M.
rewrite magnitude_split by easy.
split; [split|].
- apply F2R_ge_0; simpl.
  destruct (E =? 0); lia.
- destruct (Z.eqb_spec E 0) as [HE0|HE0].
  + replace (E - 1022) with (52 + (Z.max E 1 - 1075)) by lia.
    now apply F2R_lt_bpow_plus.
  + replace (E - 1022) with (53 + (Z.max E 1 - 1075)) by lia.
    apply F2R_lt_bpow_plus. lia. simpl Z.pow in *. lia.
- intros HE0.
  apply Z.eqb_neq in HE0. rewrite HE0.
  replace (E - 1023) with (52 + (Z.max E 1 - 1075)) by lia.
  apply bpow_plus_le_F2R; lia.
Qed.

(** The ulp of [magnitude c] is the weight of the last bit of [c]. *)
Lemma ulp_magnitude :
  forall c, 0 <= c ->
  ulp radix2 fexp64 (magnitude c) = bpow radix2 (expo c).
Proof.
intros c Hc.
destruct (magnitude_bounds c Hc) as ((H0 & Hlt) & Hge).
unfold expo.
destruct (Z.eq_dec (c / 2^52) 0) as [HE0|HE0].
- rewrite HE0 in Hlt |- *.
  apply ulp_FLT_small. easy.
  rewrite Rabs_pos_eq by easy.
  apply Rlt_le_trans with (1 := Hlt).
  now apply bpow_le.
- specialize (Hge HE0).
  rewrite ulp_neq_0.
  2: { apply Rgt_not_eq, Rlt_le_trans with (2 := Hge). apply bpow_gt_0. }
  unfold cexp.
  rewrite mag_unique_pos with (e := c / 2^52 - 1022).
  2: { split. now replace (c / 2^52 - 1022 - 1) with (c / 2^52 - 1023) by ring. easy. }
  unfold FLT_exp.
  f_equal. pose proof (split_52 c Hc). lia.
Qed.

(** Adding one to a pattern steps to the next float, including from the
    largest subnormal to the smallest normal, and between binades. *)
Lemma magnitude_succ :
  forall c, 0 <= c ->
  magnitude (c + 1) = succ radix2 fexp64 (magnitude c).
Proof.
intros c Hc.
rewrite succ_eq_pos by apply (magnitude_bounds c Hc).
rewrite ulp_magnitude by easy.
destruct (split_52 c Hc) as (Hcs & HE & HM).
unfold expo.
set (E := c / 2^52) in *. set (M := c mod 2^52) in *.
replace (magnitude c) with (magnitude (E * 2^52 + M)) by now rewrite <- Hcs.
replace (c + 1) with (E * 2^52 + M + 1) by now rewrite <- Hcs.
clearbody E M.
rewrite magnitude_split by easy.
destruct (Z.eq_dec (M + 1) (2^52)) as [HM1|HM1].
- (* The significand carries into the exponent. *)
  replace (E * 2^52 + M + 1) with ((E + 1) * 2^52 + 0) by lia.
  rewrite magnitude_split by (simpl Z.pow; lia).
  replace (E + 1 =? 0) with false by lia.
  replace M with (2^52 - 1) by lia.
  unfold F2R; cbn [Fnum Fexp].
  destruct (Z.eqb_spec E 0) as [HE0|HE0].
  + rewrite HE0.
    change (Z.max (0 + 1) 1 - 1075) with (Z.max 0 1 - 1075).
    rewrite plus_IZR, minus_IZR. ring.
  + replace (Z.max (E + 1) 1 - 1075) with (1 + (Z.max E 1 - 1075)) by lia.
    rewrite bpow_plus.
    change (bpow radix2 1) with 2%R.
    rewrite !plus_IZR, !minus_IZR.
    ring.
- replace (E * 2^52 + M + 1) with (E * 2^52 + (M + 1)) by ring.
  rewrite magnitude_split by lia.
  unfold F2R; cbn [Fnum Fexp].
  destruct (E =? 0); rewrite !plus_IZR; ring.
Qed.

(** ** [from_bits] and [to_bits] *)

Lemma from_to_bits : forall x, from_bits (to_bits x) = x.
Proof.
intros x.
unfold from_bits, to_bits, Bits.b64_of_bits, Bits.bits_of_b64.
rewrite Bits.binary_float_of_bits_of_binary_float.
apply Binary.B2BSN_BSN2B.
Qed.

Lemma split_bits_sign_bit :
  forall s c, 0 <= c < 2^63 ->
  Bits.split_bits 52 11 (sign_bit s + c) = (s, c mod 2^52, c / 2^52).
Proof.
intros s c Hc.
rewrite <- (Bits.split_join_bits 52 11 s (c mod 2^52) (c / 2^52)) by zlia.
f_equal.
unfold Bits.join_bits, sign_bit.
rewrite Z.shiftl_mul_pow2 by easy.
destruct s; zlia.
Qed.

(** The decoding of a finite pattern, before the validity proof is attached. *)
Lemma bits_aux_finite :
  forall s c, 0 <= c < 2047 * 2^52 ->
  Bits.binary_float_of_bits_aux 52 11 (sign_bit s + c) =
    if c =? 0 then Binary.F754_zero s
    else Binary.F754_finite s (Z.to_pos (mant c)) (expo c).
Proof.
intros s c Hc.
unfold Bits.binary_float_of_bits_aux.
rewrite split_bits_sign_bit by zlia.
destruct (split_52 c (proj1 Hc)) as (Hcs & HE & HM).
unfold mant, expo.
set (E := c / 2^52) in *. set (M := c mod 2^52) in *. clearbody E M.
case Zeq_bool_spec; intros HE0.
- (* Zeros and subnormals. *)
  rewrite HE0 in Hcs |- *. simpl Z.eqb. cbv iota.
  destruct M as [|p|p] eqn:HMp.
  + replace (c =? 0) with true by lia. reflexivity.
  + replace (c =? 0) with false by lia. reflexivity.
  + lia.
- case Zeq_bool_spec; intros HE1.
  + exfalso. subst c. simpl Z.pow in *. lia.
  + replace (c =? 0) with false
      by (symmetry; apply Z.eqb_neq; subst c; simpl Z.pow in *; lia).
    replace (E =? 0) with false by lia.
    destruct (M + 2^52) as [|p|p] eqn:HMp; [simpl Z.pow in *; lia| |simpl Z.pow in *; lia].
    f_equal.
    change (SpecFloat.emin (52 + 1) (2 ^ (11 - 1))) with (-1074).
    lia.
Qed.

(** A finite pattern decodes to a finite float with value [+/- magnitude c]. *)
Lemma from_bits_finite :
  forall s c, 0 <= c < 2047 * 2^52 ->
  is_finite (from_bits (sign_bit s + c)) = true /\
  Bsign (from_bits (sign_bit s + c)) = s /\
  B2R (from_bits (sign_bit s + c)) =
    (if s then - magnitude c else magnitude c)%R.
Proof.
intros s c Hc.
unfold from_bits, Bits.b64_of_bits, Bits.binary_float_of_bits.
rewrite Binary.is_finite_B2BSN, Binary.B2R_B2BSN, Binary.Bsign_B2BSN,
  Binary.is_finite_FF2B, Binary.Bsign_FF2B, Binary.B2R_FF2B.
2: rewrite Binary.is_nan_FF2B.
all: rewrite (bits_aux_finite s c Hc).
all: destruct (Z.eqb_spec c 0) as [Hc0|Hc0]; [|].
all: try easy.
- subst c. rewrite magnitude_0. simpl.
  split; [easy|]. split; [easy|].
  destruct s; [ring|easy].
- assert (Hm : 0 < mant c).
  { unfold mant. destruct (split_52 c (proj1 Hc)) as (Hcs & _ & _).
    destruct (Z.eqb_spec (c / 2^52) 0); zlia. }
  simpl. split; [easy|]. split; [easy|].
  unfold magnitude.
  rewrite Z2Pos.id by easy.
  destruct s; [|easy].
  now rewrite <- F2R_Zopp.
Qed.

Lemma from_bits_2047 : from_bits (2047 * 2^52) = B754_infinity false.
Proof. now apply B2SF_inj. Qed.

(** A finite float encodes to [sign_bit s + c] for a finite pattern [c]. *)
Lemma to_bits_finite :
  forall x, is_finite x = true ->
  exists c, 0 <= c < 2047 * 2^52 /\ to_bits x = sign_bit (Bsign x) + c.
Proof.
intros x Fx.
assert (Hr : 0 <= to_bits x < 2^64)
  by apply (Bits.bits_of_binary_float_range 52 11 eq_refl eq_refl).
pose proof (Bits.join_split_bits 52 11 eq_refl eq_refl (to_bits x) Hr) as Hj.
assert (Hs : Bits.split_bits 52 11 (to_bits x) =
  Bits.split_bits_of_binary_float 52 11 (Binary.BSN2B 53 1024 Bits.default_nan_pl64 x))
  by apply (Bits.split_bits_of_binary_float_correct 52 11 eq_refl eq_refl).
set (b := to_bits x) in *. clearbody b.
unfold Bits.split_bits, Bits.split_bits_of_binary_float, Binary.BSN2B in Hj, Hs.
cbv beta iota zeta in Hj.
unfold Bits.join_bits in Hj.
rewrite Z.shiftl_mul_pow2 in Hj by (clear; lia).
set (sb := 2^52 * 2^11 <=? b) in Hj, Hs. clearbody sb.
exists (b / 2^52 mod 2^11 * 2^52 + b mod 2^52).
destruct x as [s|s| |s m e H]; try discriminate; cbn [Bsign];
  cbv beta iota zeta in Hs.
- injection Hs as -> _ Hs3.
  unfold sign_bit. destruct s; cbv beta iota in Hj; zlia.
- assert (He : e <= 971).
  { destruct (andb_prop _ _ H) as [_ He]. now apply Zle_bool_imp_le in He. }
  (* [pair_equal_spec] splits [Hs] without reducing [Z.pos m - 2^52], whose
     reduction on a symbolic [m] does not terminate in practice. *)
  revert Hs. case Z.leb_spec; intros Hm Hs;
    apply pair_equal_spec in Hs as [Hs Hs3];
    apply pair_equal_spec in Hs as [-> _];
    unfold SpecFloat.emin in Hs3;
    unfold sign_bit; destruct s; cbv beta iota in Hj; zlia.
Qed.

(** ** [exponent] and [is_finite] *)

Lemma exponent_to_bits :
  forall x, Generic.exponent x = to_bits x / 2^52 mod 2^11 - 1023.
Proof.
intros x.
unfold Generic.exponent.
rewrite Z.shiftr_div_pow2 by easy.
change 0x7ff with (Z.ones 11).
now rewrite Z.land_ones.
Qed.

Lemma exponent_finite :
  forall x c, 0 <= c < 2047 * 2^52 -> to_bits x = sign_bit (Bsign x) + c ->
  Generic.exponent x = c / 2^52 - 1023.
Proof.
intros x c Hc Hb.
rewrite exponent_to_bits, Hb.
unfold sign_bit. destruct Bsign; zlia.
Qed.

Lemma is_finite_eq : forall x, Generic.is_finite x = is_finite x.
Proof.
intros x.
unfold Generic.is_finite.
destruct (is_finite x) eqn:Fx.
- destruct (to_bits_finite x Fx) as (c & Hc & Hb).
  rewrite (exponent_finite x c Hc Hb).
  apply Z.ltb_lt. zlia.
- destruct x as [| [|] | |]; easy.
Qed.

(** [|x| < 2^(exponent(x) + 1)] for finite [x]. *)
Theorem abs_B2R_lt_exponent :
  forall x, is_finite x = true ->
  (Rabs (B2R x) < bpow radix2 (Generic.exponent x + 1))%R.
Proof.
intros x Fx.
destruct (to_bits_finite x Fx) as (c & Hc & Hb).
rewrite (exponent_finite x c Hc Hb).
destruct (from_bits_finite (Bsign x) c Hc) as (_ & _ & Hx).
rewrite <- Hb, from_to_bits in Hx.
destruct (magnitude_bounds c (proj1 Hc)) as ((H0 & Hlt) & _).
replace (c / 2^52 - 1023 + 1) with (c / 2^52 - 1022) by ring.
rewrite Hx.
destruct Bsign; [rewrite Rabs_Ropp|]; now rewrite Rabs_pos_eq.
Qed.

(** [2^exponent(x) <= |x|] for finite normal [x], i.e. if
    [exponent(x) >= -1022]. *)
Theorem bpow_exponent_le_abs_B2R :
  forall x, is_finite x = true -> -1022 <= Generic.exponent x ->
  (bpow radix2 (Generic.exponent x) <= Rabs (B2R x))%R.
Proof.
intros x Fx He.
destruct (to_bits_finite x Fx) as (c & Hc & Hb).
rewrite (exponent_finite x c Hc Hb) in He |- *.
destruct (from_bits_finite (Bsign x) c Hc) as (_ & _ & Hx).
rewrite <- Hb, from_to_bits in Hx.
destruct (magnitude_bounds c (proj1 Hc)) as ((H0 & _) & Hge).
rewrite Hx.
destruct Bsign; [rewrite Rabs_Ropp|]; rewrite Rabs_pos_eq by exact H0;
  apply Hge; lia.
Qed.

(** ** [step_up] *)

(** [step_up] is IEEE 754 [nextUp] on finite floats: it steps [MAX] to
    [+inf], [-2^-1074] to [-0], and both zeros to [2^-1074]. *)
Theorem step_up_Bsucc :
  forall x, is_finite x = true -> Generic.step_up x = Bsucc x.
Proof.
intros x Fx.
destruct (to_bits_finite x Fx) as (c & Hc & Hb).
destruct (from_bits_finite (Bsign x) c Hc) as (_ & _ & Hx).
rewrite <- Hb, from_to_bits in Hx.
destruct (magnitude_bounds c (proj1 Hc)) as ((H0 & _) & _).
generalize (@Bsucc_correct 53 1024 _ _ x Fx).
change (SpecFloat.fexp 53 1024) with fexp64.
unfold Generic.step_up, gt, lt.
rewrite 2!Bltb_correct by easy.
change (B2R zero) with 0%R.
rewrite Hb.
destruct (Rlt_bool_spec 0 (B2R x)) as [Hpos|Hnpos].
- (* x > 0: increment the pattern. *)
  destruct (Bsign x) eqn:Hs; [lra|].
  rewrite Hx, <- magnitude_succ by easy.
  simpl sign_bit. rewrite Z.add_0_l.
  destruct (Z.eq_dec (c + 1) (2047 * 2^52)) as [Hmax|Hmax].
  + (* MAX steps to +inf. *)
    rewrite Hmax, magnitude_2047, Rlt_bool_false by apply Rle_refl.
    intros Hsucc.
    rewrite from_bits_2047.
    now apply B2SF_inj.
  + destruct (from_bits_finite false (c + 1)) as (F1 & S1 & R1); [lia|].
    simpl sign_bit in F1, S1, R1. rewrite Z.add_0_l in F1, S1, R1.
    rewrite <- R1, Rlt_bool_true.
    2: { apply Rle_lt_trans with (2 := abs_B2R_lt_emax _ _ (from_bits (c + 1))), Rle_abs. }
    intros (HR & HF & HS).
    apply B2R_Bsign_inj; [exact F1 | exact HF | now rewrite HR | now rewrite HS, S1].
- destruct (Rlt_bool_spec (B2R x) 0) as [Hneg|Hnneg].
  + (* x < 0: decrement the magnitude. *)
    destruct (Bsign x) eqn:Hs; [|lra].
    assert (Hc0 : c <> 0) by (intros ->; rewrite magnitude_0 in Hx; lra).
    replace (sign_bit true + c - 1) with (sign_bit true + (c - 1)) by ring.
    destruct (from_bits_finite true (c - 1)) as (F1 & S1 & R1); [lia|].
    pose proof (magnitude_succ (c - 1)) as Hsucc.
    replace (c - 1 + 1) with c in Hsucc by ring.
    rewrite Hx, Hsucc by lia.
    assert (Fm : generic_format radix2 fexp64 (magnitude (c - 1))).
    { replace (magnitude (c - 1)) with (- B2R (from_bits (sign_bit true + (c - 1))))%R
        by (rewrite R1; ring).
      apply generic_format_opp, generic_format_B2R. }
    rewrite succ_opp, pred_succ by first [exact Fm | typeclasses eauto].
    rewrite <- R1, Rlt_bool_true.
    2: { apply Rle_lt_trans with (2 := abs_B2R_lt_emax _ _ (from_bits (sign_bit true + (c - 1)))), Rle_abs. }
    intros (HR & HF & HS).
    apply B2R_Bsign_inj; [exact F1 | exact HF | now rewrite HR |].
    rewrite HS, S1, is_finite_strict_B2R; [easy|lra].
  + (* x = 0: both zeros step to 2^-1074. *)
    destruct x as [s| | |s m e H]; try discriminate.
    * intros _. apply B2SF_inj. destruct s; vm_compute; reflexivity.
    * exfalso. revert Hnpos Hnneg. simpl.
      assert (F2R (Float radix2 (SpecFloat.cond_Zopp s (Z.pos m)) e) <> 0%R).
      { apply F2R_neq_0. destruct s; discriminate. }
      lra.
Qed.

(** The patterns that [step_up] decodes are in the range of [u64], so its
    [b + 1] and [b - 1] do not wrap around (or panic) in Rust either. *)
Theorem step_up_no_wrap :
  forall x, is_finite x = true ->
  0 <= (if gt x zero then to_bits x + 1
        else if lt x zero then to_bits x - 1 else 1) < 2^64.
Proof.
intros x Fx.
destruct (to_bits_finite x Fx) as (c & Hc & Hb).
destruct (from_bits_finite (Bsign x) c Hc) as (_ & _ & Hx).
rewrite <- Hb, from_to_bits in Hx.
destruct (magnitude_bounds c (proj1 Hc)) as ((H0 & _) & _).
unfold gt, lt.
rewrite 2!Bltb_correct by easy.
change (B2R zero) with 0%R.
rewrite Hb.
destruct (Rlt_bool_spec 0 (B2R x)) as [Hpos|Hnpos].
- destruct (Bsign x); [lra|].
  unfold sign_bit. zlia.
- destruct (Rlt_bool_spec (B2R x) 0) as [Hneg|Hnneg]; [|lia].
  destruct (Bsign x); [|lra].
  assert (Hc0 : c <> 0) by (intros ->; rewrite magnitude_0 in Hx; lra).
  unfold sign_bit. zlia.
Qed.
