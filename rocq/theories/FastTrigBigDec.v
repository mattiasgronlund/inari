(** * The floats of the reduction of large arguments of the fast paths of [sin], [cos] and [tan]

    Where the exponent test of [DyadicTrig.fast_reduce_big] passes, [x] is
    finite, [|x| >= 2^16], and [x] is its sign times [m 2^(be - 1075)] for
    the significand [m] and the biased exponent [be] that it reads from
    the bits of [x] ([big_decode]). The two parts of the fraction, [fh]
    and [fl], are their integers times [2^-53] and [2^-106], not rounded
    ([big_fh], [big_fl]), and where [rh = fh (U1 + U2)] passes the test
    [|rh| >= 2^-65] as a float, it is finite and passes it as a real
    ([big_guard]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Encoding TwoSum TwoProduct FastTrigReduce FastTrigBigMul.
From Inari Require Limbs FastLogFin FastExpReduce.

Open Scope R_scope.

(** ** Literals *)

(** [B2R l] of an [f64] literal [l], as [m * 2^e] (as in [FastHypPos.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** A literal [2^k] with a mantissa of [2^52]. *)
Local Ltac lit_pow2 :=
  lit_B2R; change (IZR 4503599627370496) with (bpow radix2 52); rewrite <- bpow_plus;
  reflexivity.

Lemma big_lit53 : B2R (from_bits 0x3ca0000000000000) = bpow radix2 (-53).
Proof. lit_pow2. Qed.

Lemma big_lit106 : B2R (from_bits 0x3950000000000000) = bpow radix2 (-106).
Proof. lit_pow2. Qed.

Lemma big_lit65 : B2R (from_bits 0x3be0000000000000) = bpow radix2 (-65).
Proof. lit_pow2. Qed.

(** ** The bits of [x] *)

(** The exponent test keeps the biased exponents [1039 <= be <= 2046]: it
    rejects the infinities and NaN, whose biased exponent is 2047, and
    every finite [x] below [2^16], the zeros and subnormals (biased
    exponent 0) among them. For the others, the bits below the sign bit
    are [c = be 2^52 + (m - 2^52)], so that [|x| = m 2^(be - 1075)] by
    [Encoding.v]. *)
Lemma big_decode :
  forall x,
  let b := Z.land (to_bits x) (2 ^ 63 - 1)%Z in
  let be := Z.shiftr b 52 in
  ((1039 <=? be) && (be <=? 2046))%Z = true ->
  is_finite x = true /\ (1039 <= be <= 2046)%Z /\
  (2 ^ 52 <= Z.lor (Z.land b (2 ^ 52 - 1)) (2 ^ 52) < 2 ^ 53)%Z /\
  B2R x = (if lt x zero then - 1 else 1) *
          (IZR (Z.lor (Z.land b (2 ^ 52 - 1)) (2 ^ 52))%Z * bpow radix2 (be - 1075)) /\
  65536 <= Rabs (B2R x).
Proof.
intros x. cbv zeta. intros G.
destruct (is_finite x) eqn:Fx.
2: { destruct x as [s|s| |s m e Hv]; try discriminate Fx;
     [destruct s|]; vm_compute in G; discriminate G. }
destruct (to_bits_finite x Fx) as (c & Hc & Hb).
(* The mask [2^63 - 1] drops the sign bit. *)
assert (Eb : Z.land (to_bits x) (2 ^ 63 - 1) = c).
{ rewrite Hb. change (2 ^ 63 - 1)%Z with (Z.ones 63). rewrite Z.land_ones by lia.
  unfold sign_bit. destruct (Bsign x); zlia. }
rewrite Eb in G |- *.
rewrite Z.shiftr_div_pow2 in G |- * by lia.
apply andb_prop in G. destruct G as [G1 G2].
apply Z.leb_le in G1. apply Z.leb_le in G2.
(* The significand with its implicit bit. *)
assert (Em : Z.lor (Z.land c (2 ^ 52 - 1)) (2 ^ 52) = (c mod 2 ^ 52 + 2 ^ 52)%Z).
{ change (2 ^ 52 - 1)%Z with (Z.ones 52). rewrite Z.land_ones by lia.
  rewrite Z.lor_comm.
  pose proof (Limbs.lor_low 1 (c mod 2 ^ 52) 52) as L. rewrite Z.mul_1_l in L.
  rewrite L; [lia | lia |]. apply Z.mod_pos_bound. lia. }
rewrite Em.
assert (Hm : (2 ^ 52 <= c mod 2 ^ 52 + 2 ^ 52 < 2 ^ 53)%Z).
{ assert (HM : (0 <= c mod 2 ^ 52 < 2 ^ 52)%Z) by (apply Z.mod_pos_bound; lia). lia. }
(* The magnitude of [x], from its bits. *)
assert (Hmag : magnitude c = IZR (c mod 2 ^ 52 + 2 ^ 52) * bpow radix2 (c / 2 ^ 52 - 1075)).
{ unfold magnitude, mant, expo.
  replace (c / 2 ^ 52 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  replace (Z.max (c / 2 ^ 52) 1) with (c / 2 ^ 52)%Z by lia.
  reflexivity. }
assert (Hpos : 65536 <= magnitude c).
{ rewrite Hmag.
  assert (H52 : bpow radix2 52 <= IZR (c mod 2 ^ 52 + 2 ^ 52)).
  { change (bpow radix2 52) with (IZR (2 ^ 52)). apply IZR_le. lia. }
  assert (H36 : bpow radix2 (-36) <= bpow radix2 (c / 2 ^ 52 - 1075)).
  { apply bpow_le. lia. }
  apply Rle_trans with (bpow radix2 52 * bpow radix2 (-36)).
  - rewrite <- bpow_plus. apply Req_le. reflexivity.
  - apply Rmult_le_compat; [apply bpow_ge_0 | apply bpow_ge_0 | exact H52 | exact H36]. }
destruct (from_bits_finite (Bsign x) c Hc) as (_ & _ & Hx).
rewrite <- Hb, from_to_bits in Hx.
(* [x < 0] is the sign bit, as [x] is not zero. *)
unfold lt. rewrite Bltb_correct; [| exact Fx | reflexivity].
change (B2R zero) with 0.
split; [reflexivity |]. split; [lia |]. split; [exact Hm |].
rewrite Hx, <- Hmag.
destruct (Bsign x); cbv iota.
- rewrite Rlt_bool_true by lra. cbv iota. rewrite Rabs_Ropp, Rabs_pos_eq by lra. split; [ring | lra].
- rewrite Rlt_bool_false by lra. cbv iota. rewrite Rabs_pos_eq by lra. split; [ring | lra].
Qed.

(** ** The two parts of the fraction *)

(** [z as f64] is [z] for [|z| <= 2^52], and [z 2^-53] is a float, as
    [|z 2^-53| <= 1/2 < 2^0]. *)
Lemma big_fh :
  forall z, (- 2 ^ 52 <= z <= 2 ^ 52)%Z ->
  is_finite (mul (DyadicTrig.of_i64 z) (from_bits 0x3ca0000000000000)) = true /\
  B2R (mul (DyadicTrig.of_i64 z) (from_bits 0x3ca0000000000000)) =
    IZR z * bpow radix2 (-53).
Proof.
intros z Hz.
change (DyadicTrig.of_i64 z) with (DyadicLog.of_i64 z).
destruct (FastLogFin.fl_of_i64 z) as (Fz & Ez); [lia |].
assert (F53 : is_finite (from_bits 0x3ca0000000000000) = true) by reflexivity.
assert (Hb : Rabs (IZR z * bpow radix2 (-53)) < bpow radix2 (-53 + 53)).
{ rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (-53))) by apply bpow_ge_0.
  rewrite <- abs_IZR.
  assert (Hz' : IZR (Z.abs z) <= IZR (2 ^ 52)) by (apply IZR_le; lia).
  change (IZR (2 ^ 52)) with (bpow radix2 52) in Hz'.
  apply Rle_lt_trans with (bpow radix2 52 * bpow radix2 (-53)).
  - apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Hz'].
  - rewrite <- bpow_plus. apply bpow_lt. lia. }
destruct (mul_below_max _ _ Fz F53) as (F & R & _).
{ rewrite Ez, big_lit53. apply FastExpReduce.le_MAX.
  assert (B0 : bpow radix2 (-53 + 53) = 1) by reflexivity. lra. }
split; [exact F |].
rewrite R, Ez, big_lit53. apply round_generic; [typeclasses eauto |].
apply grid_format; [lia | exact Hb].
Qed.

(** [z as i64 as f64] is [z] for [0 <= z < 2^53], and [z 2^-106] is a
    float, as it is below [2^-53]. *)
Lemma big_fl :
  forall z, (0 <= z < 2 ^ 53)%Z ->
  is_finite (mul (DyadicTrig.of_i64 z) (from_bits 0x3950000000000000)) = true /\
  B2R (mul (DyadicTrig.of_i64 z) (from_bits 0x3950000000000000)) =
    IZR z * bpow radix2 (-106).
Proof.
intros z Hz.
change (DyadicTrig.of_i64 z) with (DyadicLog.of_i64 z).
destruct (FastLogFin.fl_of_i64 z) as (Fz & Ez); [lia |].
assert (F106 : is_finite (from_bits 0x3950000000000000) = true) by reflexivity.
assert (Hb : Rabs (IZR z * bpow radix2 (-106)) < bpow radix2 (-106 + 53)).
{ rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (-106))) by apply bpow_ge_0.
  rewrite <- abs_IZR.
  assert (Hz' : IZR (Z.abs z) < IZR (2 ^ 53)) by (apply IZR_lt; lia).
  change (IZR (2 ^ 53)) with (bpow radix2 53) in Hz'.
  rewrite bpow_plus, Rmult_comm.
  apply Rmult_lt_compat_l; [apply bpow_gt_0 | exact Hz']. }
destruct (mul_below_max _ _ Fz F106) as (F & R & _).
{ rewrite Ez, big_lit106. apply FastExpReduce.le_MAX.
  assert (B0 : bpow radix2 (-106 + 53) <= bpow radix2 0) by (apply bpow_le; lia).
  change (bpow radix2 0) with 1 in B0. lra. }
split; [exact F |].
rewrite R, Ez, big_lit106. apply round_generic; [typeclasses eauto |].
apply grid_format; [lia | exact Hb].
Qed.

(** ** The test [|rh| >= 2^-65] *)

(** [rh = RN(fh uh)] is finite, as [|fh uh| <= 2^-11], and the float
    comparison is the real one. *)
Lemma big_guard :
  forall fh, is_finite fh = true -> Rabs (B2R fh) <= / 2 ->
  lt (fabs (mul fh (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2))))
     (from_bits 0x3be0000000000000) = false ->
  is_finite (mul fh (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2))) = true /\
  bpow radix2 (-65) <=
    Rabs (B2R (mul fh (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)))).
Proof.
intros fh Ffh Hfh G.
destruct big_uh as (Fuh & _).
destruct big_u_bounds as (_ & (Hu1 & Hu2) & _).
set (uh := add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)) in *.
assert (Hp : Rabs (B2R fh * B2R uh) <= / 2).
{ rewrite Rabs_mult.
  assert (B10 : bpow radix2 (-10) <= bpow radix2 0) by (apply bpow_le; lia).
  change (bpow radix2 0) with 1 in B10.
  rewrite (Rabs_pos_eq (B2R uh)) by (pose proof (bpow_ge_0 radix2 (-11)); lra).
  apply Rle_trans with (/ 2 * 1); [| lra].
  apply Rmult_le_compat; [apply Rabs_pos | | exact Hfh | lra].
  pose proof (bpow_ge_0 radix2 (-11)); lra. }
destruct (mul_below_max _ _ Ffh Fuh) as (F & _ & _).
{ apply FastExpReduce.le_MAX. lra. }
split; [exact F |].
unfold lt, fabs in G.
rewrite Bltb_correct in G; [| rewrite is_finite_Babs; exact F | reflexivity].
rewrite B2R_Babs, big_lit65 in G.
apply Rnot_lt_le. intros Hl.
rewrite Rlt_bool_true in G by exact Hl. discriminate G.
Qed.
