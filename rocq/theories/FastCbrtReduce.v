(** * The reduction of the fast path of [cbrt]

    [DyadicRoot.fast_cbrt] splits the bits of a finite nonzero [x] into a
    52-bit fraction [m] and an exponent [e] with
    [|x| = (2^52 + m) 2^(e - 1075)], and normalizes a subnormal [x] by its
    leading zeros ([cbrt_split_bits]). From [m] and an [i] in [0, 2] it
    builds [zz = (2^52 + m) 2^(i - 52)] in [1, 8) and [rr], [1 / zz] with
    one rounding ([cbrt_zz_rr]). *)

From Stdlib Require Import ZArith Reals Lra Lia Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Relative Mult_error.
From Inari Require Import Model Encoding TwoSum.
From Inari Require Limbs SqrtSlow.

Open Scope R_scope.

(** A normal pattern [E 2^52 + M] with the sign bit clear is the finite
    [(2^52 + M) 2^(E - 1075)]. *)
Local Lemma normal_bits :
  forall E M, (1 <= E <= 2046)%Z -> (0 <= M < 2 ^ 52)%Z ->
  is_finite (from_bits (E * 2 ^ 52 + M)) = true /\
  B2R (from_bits (E * 2 ^ 52 + M)) = IZR (2 ^ 52 + M) * bpow radix2 (E - 1075).
Proof.
intros E M HE HM.
destruct (from_bits_finite false (E * 2 ^ 52 + M)) as (F & _ & V);
  [split; [lia | simpl Z.pow in *; lia] |].
unfold sign_bit in F, V. rewrite Z.add_0_l in F, V. cbv iota in V.
split; [exact F |]. rewrite V, magnitude_split by lia.
replace (E =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
replace (Z.max E 1) with E by lia.
unfold F2R; cbn [Fnum Fexp]. rewrite (Z.add_comm M). reflexivity.
Qed.

(** The relative error of rounding to nearest above the subnormals
    (as [FastPowCube.rn_rel]). *)
Local Lemma rn_rel :
  forall x, bpow radix2 (-1022) <= Rabs x -> Rabs (RN x - x) <= bpow radix2 (-53) * Rabs x.
Proof.
intros x Hx.
assert (H : Rabs (RN x - x) <= / 2 * bpow radix2 (- 53 + 1) * Rabs x)
  by exact (relative_error_N_FLT radix2 (-1074) 53 eq_refl (fun z => negb (Z.even z)) x Hx).
change (- 53 + 1)%Z with (-52)%Z in H.
assert (E : / 2 * bpow radix2 (-52) = bpow radix2 (-53))
  by (cbn [bpow radix_val radix2]; lra).
rewrite E in H. exact H.
Qed.

Theorem cbrt_split_bits :
  forall x m e,
  is_finite x = true -> B2R x <> 0 ->
  (let bits := Z.land (to_bits x) 0x7fffffffffffffff in
   if Z.shiftr bits 52 =? 0 then
     let nz := leading_zeros 64 bits - 11 in
     (Z.land (Z.shiftl (Z.land bits 0x000fffffffffffff) nz) 0x000fffffffffffff, 1 - nz)
   else (Z.land bits 0x000fffffffffffff, Z.shiftr bits 52))%Z = (m, e) ->
  (0 <= m < 2 ^ 52)%Z /\ (-51 <= e <= 2046)%Z /\
  Rabs (B2R x) = IZR (2 ^ 52 + m) * bpow radix2 (e - 1075).
Proof.
intros x m e Fx Hx H.
(* [x = +/- magnitude c] for the pattern [c] without the sign bit. *)
destruct (to_bits_finite x Fx) as (c & Hc & Hb).
destruct (from_bits_finite (Bsign x) c Hc) as (_ & _ & Hv).
rewrite <- Hb, from_to_bits in Hv.
destruct (magnitude_bounds c (proj1 Hc)) as ((H0 & _) & _).
assert (Hax : Rabs (B2R x) = magnitude c).
{ destruct (Bsign x); cbv iota in Hv; rewrite Hv;
    [rewrite Rabs_Ropp |]; apply Rabs_pos_eq; lra. }
assert (Hc0 : c <> 0%Z).
{ intros ->. rewrite magnitude_0 in Hax. pose proof (Rabs_pos_lt _ Hx). lra. }
assert (Hbits : Z.land (to_bits x) 0x7fffffffffffffff = c).
{ rewrite Hb. change 0x7fffffffffffffff%Z with (Z.ones 63).
  rewrite Z.land_ones by lia. destruct (Bsign x); cbn [sign_bit]; zlia. }
cbv zeta in H. rewrite Hbits in H.
change 0x000fffffffffffff%Z with (Z.ones 52) in H.
rewrite !Z.land_ones in H by lia.
rewrite Z.shiftr_div_pow2 in H by lia.
(* [c = E 2^52 + M] for the biased exponent [E] and the stored fraction [M]. *)
destruct (split_52 c (proj1 Hc)) as (Hcs & HE & HM).
set (E := (c / 2 ^ 52)%Z) in *. set (M := (c mod 2 ^ 52)%Z) in *.
clearbody E M.
revert H. destruct (Z.eqb_spec E 0) as [HE0 | HE0]; intros H; cbv iota in H.
- (* Subnormal: [c = M] in [[2^L, 2^(L+1))] for [L = log2 M] in [[0, 51]],
     and [x] has [nz = 52 - L] leading zeros after the sign and exponent. *)
  subst E.
  assert (EcM : c = M) by lia.
  rewrite EcM in H.
  assert (HM0 : (0 < M)%Z) by lia.
  unfold leading_zeros in H.
  replace (M =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.log2_spec M HM0) as (HL1 & HL2).
  assert (HL : (0 <= Z.log2 M < 52)%Z).
  { split; [apply Z.log2_nonneg |]. apply Z.log2_lt_pow2; lia. }
  rewrite Z.pow_succ_r in HL2 by lia.
  set (L := Z.log2 M) in *. clearbody L.
  rewrite Z.shiftl_mul_pow2 in H by lia.
  replace (64 - 1 - L - 11)%Z with (52 - L)%Z in H by lia.
  (* [N = M 2^nz] is the significand [2^52 + m], with its top bit set. *)
  assert (Hp : (2 ^ L * 2 ^ (52 - L) = 2 ^ 52)%Z)
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Hpp : (0 < 2 ^ (52 - L))%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (HN : (2 ^ 52 <= M * 2 ^ (52 - L) < 2 * 2 ^ 52)%Z).
  { rewrite <- Hp. nia. }
  set (N := (M * 2 ^ (52 - L))%Z) in *.
  assert (EN : (N mod 2 ^ 52 = N - 2 ^ 52)%Z) by zlia.
  apply pair_equal_spec in H as (Hm & He).
  rewrite EN in Hm. subst m e.
  split; [lia |]. split; [lia |].
  rewrite Hax, Hcs, magnitude_split by lia.
  change (0 =? 0)%Z with true. cbv iota.
  change (Z.max 0 1 - 1075)%Z with (-1074)%Z.
  replace (2 ^ 52 + (N - 2 ^ 52))%Z with N by ring.
  unfold N. rewrite mult_IZR.
  replace (IZR (2 ^ (52 - L))) with (bpow radix2 (52 - L))
    by (rewrite <- IZR_Zpower by lia; reflexivity).
  unfold F2R; cbn [Fnum Fexp].
  rewrite Rmult_assoc, <- bpow_plus. do 2 f_equal. lia.
- (* Normal: [m = M] and [e = E]. *)
  apply pair_equal_spec in H as (Hm & He). subst m e.
  split; [exact HM |]. split; [simpl Z.pow in *; lia |].
  rewrite Hax, Hcs, magnitude_split by lia.
  replace (E =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  replace (Z.max E 1) with E by lia.
  unfold F2R; cbn [Fnum Fexp]. rewrite (Z.add_comm M). reflexivity.
Qed.

Theorem cbrt_zz_rr :
  forall m i,
  (0 <= m < 2 ^ 52)%Z -> (0 <= i <= 2)%Z ->
  let zz := from_bits (Z.lor m 0x3ff0000000000000 + Z.shiftl i 52)%Z in
  let rr := mul (div Fast.one (from_bits (Z.lor m 0x3ff0000000000000)))
                (from_bits (Z.shiftl (1023 - i) 52)) in
  is_finite zz = true /\ B2R zz = IZR (2 ^ 52 + m) * bpow radix2 (i - 52) /\
  1 <= B2R zz < 8 /\
  is_finite rr = true /\ Rabs (B2R rr - / B2R zz) <= bpow radix2 (-53) * / B2R zz.
Proof.
intros m i Hm Hi. cbv zeta.
(* The patterns: [zz] has the biased exponent [1023 + i], [z] [1023] and
   the scale [d] [1023 - i]. *)
assert (El : Z.lor m 0x3ff0000000000000 = (1023 * 2 ^ 52 + m)%Z).
{ change 0x3ff0000000000000%Z with (1023 * 2 ^ 52)%Z.
  rewrite Z.lor_comm. apply Limbs.lor_low; lia. }
rewrite El, (Z.shiftl_mul_pow2 i 52), (Z.shiftl_mul_pow2 (1023 - i) 52) by lia.
replace (1023 * 2 ^ 52 + m + i * 2 ^ 52)%Z with ((1023 + i) * 2 ^ 52 + m)%Z by ring.
replace ((1023 - i) * 2 ^ 52)%Z with ((1023 - i) * 2 ^ 52 + 0)%Z by ring.
change Fast.one with (from_bits (1023 * 2 ^ 52 + 0)).
destruct (normal_bits (1023 + i) m) as (Fzz & Ezz); [lia | exact Hm |].
destruct (normal_bits 1023 m) as (Fz & Ez); [lia | exact Hm |].
destruct (normal_bits (1023 - i) 0) as (Fd & Ed); [lia | lia |].
destruct (normal_bits 1023 0) as (Fo & Eo); [lia | lia |].
set (zz := from_bits ((1023 + i) * 2 ^ 52 + m)) in *.
set (z := from_bits (1023 * 2 ^ 52 + m)) in *.
set (d := from_bits ((1023 - i) * 2 ^ 52 + 0)) in *.
set (o := from_bits (1023 * 2 ^ 52 + 0)) in *.
change (IZR (2 ^ 52 + 0)) with (bpow radix2 52) in Ed, Eo.
rewrite <- bpow_plus in Ed, Eo.
replace (52 + (1023 - i - 1075))%Z with (- i)%Z in Ed by ring.
change (52 + (1023 - 1075))%Z with 0%Z in Eo. change (bpow radix2 0) with 1 in Eo.
(* [z = (2^52 + m) 2^-52] in [[1, 2)] and [zz = z 2^i]. *)
assert (Hs : bpow radix2 52 <= IZR (2 ^ 52 + m) < bpow radix2 53).
{ change (bpow radix2 52) with (IZR (2 ^ 52)). change (bpow radix2 53) with (IZR (2 ^ 53)).
  split; [apply IZR_le | apply IZR_lt]; simpl Z.pow in *; lia. }
assert (Ezz' : B2R zz = B2R z * bpow radix2 i).
{ rewrite Ezz, Ez, Rmult_assoc, <- bpow_plus. do 2 f_equal. ring. }
assert (Bz : 1 <= B2R z < 2).
{ rewrite Ez. change (1023 - 1075)%Z with (-52)%Z.
  assert (P : bpow radix2 52 * bpow radix2 (-52) = 1 /\ bpow radix2 53 * bpow radix2 (-52) = 2)
    by (rewrite <- !bpow_plus; split; reflexivity).
  pose proof (bpow_gt_0 radix2 (-52)). nra. }
assert (Bi : 1 <= bpow radix2 i <= 4).
{ change 1 with (bpow radix2 0). change 4 with (bpow radix2 2).
  split; apply bpow_le; lia. }
pose proof (bpow_gt_0 radix2 i) as Pi.
(* [r = RN(1 / z)], with [1 / z] in [(1/2, 1]]. *)
assert (Hz0 : B2R z <> 0) by lra.
set (q := / B2R z).
assert (Hq : / 2 < q <= 1).
{ assert (Eq : q * B2R z = 1) by (unfold q; field; exact Hz0).
  assert (Pq : 0 < q) by (apply Rinv_0_lt_compat; lra).
  split; nra. }
assert (Hlt : Rabs (RN (B2R o / B2R z)) < bpow radix2 1024).
{ apply RN_no_overflow. rewrite Eo. unfold Rdiv. rewrite Rmult_1_l. fold q.
  rewrite Rabs_pos_eq by lra.
  assert (P : 1 <= bpow radix2 1023) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
  pose proof (bpow_gt_0 radix2 971). lra. }
generalize (@Bdiv_correct 53 1024 _ _ mode_NE o z Hz0).
rewrite Rlt_bool_true by exact Hlt.
intros (Er & Fr & _). rewrite Fo in Fr.
change (Bdiv mode_NE o z) with (div o z) in Er, Fr.
rewrite Eo in Er. unfold Rdiv in Er. rewrite Rmult_1_l in Er. fold q in Er.
set (r := div o z) in *.
(* [|RN q - q| <= 2^-53 q], so [r] lies in [[1/4, 2]]. *)
assert (Hrq : Rabs (B2R r - q) <= bpow radix2 (-53) * q).
{ rewrite Er.
  replace (bpow radix2 (-53) * q) with (bpow radix2 (-53) * Rabs q)
    by (rewrite Rabs_pos_eq by lra; reflexivity).
  apply rn_rel.
  rewrite Rabs_pos_eq by lra.
  assert (P : bpow radix2 (-1022) <= / 2) by (cbn [bpow radix_val radix2]; lra).
  lra. }
assert (P53 : 0 < bpow radix2 (-53) <= / 4) by (cbn [bpow radix_val radix2]; lra).
assert (Br : / 4 <= B2R r <= 2).
{ pose proof (Rabs_le_inv _ _ Hrq). nra. }
(* [rr = r 2^-i] exactly: [r >= 1/4] keeps the product normal. *)
assert (Gr : generic_format radix2 fexp64 (B2R r * B2R d)).
{ rewrite Ed. apply mult_bpow_exact_FLT; [apply generic_format_B2R |].
  assert (Hm' : (-1 <= mag radix2 (B2R r))%Z).
  { apply mag_ge_bpow. change (-1 - 1)%Z with (-2)%Z.
    rewrite Rabs_pos_eq by lra.
    replace (bpow radix2 (-2)) with (/ 4) by (cbn [bpow radix_val radix2]; lra).
    lra. }
  lia. }
assert (Hrd : Rabs (B2R r * B2R d) < bpow radix2 1024).
{ rewrite Ed, Rabs_mult, (Rabs_pos_eq (B2R r)), (Rabs_pos_eq (bpow _ _))
    by (try apply bpow_ge_0; lra).
  assert (P : bpow radix2 (- i) <= 1)
    by (change 1 with (bpow radix2 0); apply bpow_le; lia).
  assert (P' : 2 < bpow radix2 1024)
    by (change 2 with (bpow radix2 1); apply bpow_lt; lia).
  pose proof (bpow_gt_0 radix2 (- i)). nra. }
destruct (SqrtSlow.mul_exact r d Fr Fd Gr Hrd) as (Frr & Err & _).
split; [exact Fzz |]. split; [rewrite Ezz; do 2 f_equal; ring |].
split; [rewrite Ezz'; split; nra |].
split; [exact Frr |].
(* [rr - 1 / zz = (r - q) 2^-i]. *)
assert (Einv : / B2R zz = q * bpow radix2 (- i))
  by (rewrite Ezz', Rinv_mult, bpow_opp; reflexivity).
rewrite Err, Ed, Einv.
replace (B2R r * bpow radix2 (- i) - q * bpow radix2 (- i))
  with ((B2R r - q) * bpow radix2 (- i)) by ring.
rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0.
rewrite <- Rmult_assoc. apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Hrq].
Qed.
