(** * The integers of the reduction of large arguments of the fast paths of [sin], [cos] and [tan]

    [DyadicTrig.INV2PI] of [Model.v], read as one integer [T]
    ([inv2pi_val]), satisfies [T <= 2^1215 / π <= T + 1] (and [2^1215 / π
    = 2^1216 / (2π)]), from the bounds of π of [PI_bounds]
    ([DyConstPi.v]) through [km_t_bounds_gen] ([KahanMcDonald.v])
    ([inv2pi_bounds]); that [T] is floor(2^1215 / π) is checked against
    MPFR by the test [inv2pi_table], not proved. [DyadicTrig.big_w] reads
    192 bits of it ([big_w_window]); [m 2^e / (π/4096)] is [m] times those
    bits over 2^179, plus a multiple of 8192 and a term between 0 and
    [m 2^-179] ([big_frac]); the three products of [fast_reduce_big] give
    the top 128 bits of [m] times them mod 2^192 ([big_prod]), and its
    shifts split that into [n] and the two parts of the fraction
    ([big_split]). *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs DyConstPi KahanMcDonald.

Open Scope R_scope.

(** [INV2PI] as one integer, from its most significant limb. *)
Definition inv2pi_val : Z :=
  fold_left (fun acc l => acc * 2 ^ 64 + l)%Z DyadicTrig.INV2PI 0%Z.

(** The two ends of the bracket of [2^1215 / π] that [km_t_bounds_gen]
    gives from [PI_bounds], behind definitions so that only [vm_compute]
    sees their numerator 2^5437. *)
Definition inv2pi_lo : Z := (2 ^ (1215 + 4222) / (Limbs.val DyadicConsts.PI + 1))%Z.
Definition inv2pi_hi : Z := (2 ^ (1215 + 4222) / Limbs.val DyadicConsts.PI)%Z.

(** Both ends are [INV2PI]: the bracket of π is narrow enough that
    [2^5437 / L] and [2^5437 / (L + 1)] have the same integer part. *)
Lemma inv2pi_lo_eq : inv2pi_lo = inv2pi_val.
Proof. apply Z.eqb_eq. vm_compute. reflexivity. Qed.

Lemma inv2pi_hi_eq : inv2pi_hi = inv2pi_val.
Proof. apply Z.eqb_eq. vm_compute. reflexivity. Qed.

Lemma inv2pi_bounds :
  IZR inv2pi_val <= bpow radix2 1215 / PI <= IZR inv2pi_val + 1.
Proof.
assert (HN : (0 <= 1215)%Z) by lia.
pose proof (km_t_bounds_gen (Limbs.val DyadicConsts.PI) 1215 km_L_pos HN PI_bounds) as H.
(* Not [change ... with inv2pi_lo in H], nor a [rewrite] with the
   unfolded [inv2pi_lo_eq]: their conversion checks between [inv2pi_lo]
   and the quotient of 2^5437 took about 2 minutes each (in the tactic, or
   at [Qed]). Applying [G] to [H] checks the same conversions at once. *)
assert (G : forall lo hi : Z, lo = inv2pi_val -> hi = inv2pi_val ->
  IZR lo <= bpow radix2 1215 / PI <= IZR (hi + 1) ->
  IZR inv2pi_val <= bpow radix2 1215 / PI <= IZR inv2pi_val + 1).
{ intros lo hi -> ->. rewrite plus_IZR. auto. }
exact (G _ _ inv2pi_lo_eq inv2pi_hi_eq H).
Qed.

(** The statement of [big_w_window] at one [k], for the [INV2PI] value
    [T], which [vm_compute] then evaluates once for every [k]. *)
Definition big_w_ok (T k : Z) : bool :=
  ((0 <=? DyadicTrig.big_w k 0) && (DyadicTrig.big_w k 0 <? 2 ^ 64) &&
   (0 <=? DyadicTrig.big_w k 1) && (DyadicTrig.big_w k 1 <? 2 ^ 64) &&
   (0 <=? DyadicTrig.big_w k 2) && (DyadicTrig.big_w k 2 <? 2 ^ 64) &&
   (DyadicTrig.big_w k 0 * 2 ^ 128 + DyadicTrig.big_w k 1 * 2 ^ 64 + DyadicTrig.big_w k 2 =?
    Z.shiftr T (1088 - k) mod 2 ^ 192))%Z.

(** The 1,008 [k] in [[28, 1035]] *)
Lemma big_w_all :
  forallb (big_w_ok inv2pi_val) (map (fun i => 28 + Z.of_nat i)%Z (seq 0 1008)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma big_w_window :
  forall k, (28 <= k <= 1035)%Z ->
  (0 <= DyadicTrig.big_w k 0 < 2 ^ 64)%Z /\ (0 <= DyadicTrig.big_w k 1 < 2 ^ 64)%Z /\
  (0 <= DyadicTrig.big_w k 2 < 2 ^ 64)%Z /\
  (DyadicTrig.big_w k 0 * 2 ^ 128 + DyadicTrig.big_w k 1 * 2 ^ 64 + DyadicTrig.big_w k 2 =
   Z.shiftr inv2pi_val (1088 - k) mod 2 ^ 192)%Z.
Proof.
intros k Hk.
assert (Hin : In k (map (fun i => 28 + Z.of_nat i)%Z (seq 0 1008))).
{ apply in_map_iff. exists (Z.to_nat (k - 28)). split; [cbv beta; lia |].
  apply in_seq. lia. }
pose proof (proj1 (forallb_forall _ _) big_w_all k Hin) as H.
unfold big_w_ok in H.
repeat rewrite Bool.andb_true_iff in H.
destruct H as [[[[[[H1 H2] H3] H4] H5] H6] H7].
apply Z.leb_le in H1, H3, H5. apply Z.ltb_lt in H2, H4, H6. apply Z.eqb_eq in H7.
split; [split; assumption |]. split; [split; assumption |].
split; [split; assumption |]. exact H7.
Qed.

Lemma big_frac :
  forall m e, (0 < m < 2 ^ 53)%Z -> (-36 <= e <= 971)%Z ->
  exists (K : Z) (t : R),
  IZR m * bpow radix2 e / (PI / 4096) =
    8192 * IZR K +
    IZR ((m * (Z.shiftr inv2pi_val (1024 - e) mod 2 ^ 192)) mod 2 ^ 192) * bpow radix2 (-179) +
    t /\
  0 <= t <= IZR m * bpow radix2 (-179).
Proof.
intros m e Hm He.
(* [m 2^e / (π/4096) = m (2^1215 / π) 2^(e - 1203)] *)
assert (HX : IZR m * bpow radix2 e / (PI / 4096) =
             IZR m * (bpow radix2 1215 / PI) * bpow radix2 (e - 1203)).
{ assert (H12 : bpow radix2 1215 * bpow radix2 (e - 1203) = bpow radix2 e * 4096).
  { rewrite <- bpow_plus. replace (1215 + (e - 1203))%Z with (e + 12)%Z by ring.
    rewrite bpow_plus. reflexivity. }
  pose proof PI_neq0 as HPI.
  replace (IZR m * (bpow radix2 1215 / PI) * bpow radix2 (e - 1203))
    with (IZR m * (bpow radix2 1215 * bpow radix2 (e - 1203)) / PI) by (field; exact HPI).
  rewrite H12. field; exact HPI. }
rewrite HX.
pose proof inv2pi_bounds as HB.
set (T := inv2pi_val) in *. clearbody T.
set (B := bpow radix2 1215 / PI) in *.
(* [T = (Hi 2^192 + W) 2^s + Lo] with [s = 1024 - e] *)
set (s := (1024 - e)%Z).
assert (Hs : (0 <= s)%Z) by (unfold s; lia).
assert (Hps : (0 < 2 ^ s)%Z) by (apply Z.pow_pos_nonneg; lia).
rewrite (Z.shiftr_div_pow2 _ _ Hs).
set (W := (T / 2 ^ s mod 2 ^ 192)%Z).
set (Hi := (T / 2 ^ s / 2 ^ 192)%Z).
set (Lo := (T mod 2 ^ s)%Z).
assert (HT : (T = (Hi * 2 ^ 192 + W) * 2 ^ s + Lo)%Z).
{ pose proof (Z.div_mod T (2 ^ s) ltac:(lia)) as D1.
  pose proof (Z.div_mod (T / 2 ^ s) (2 ^ 192) ltac:(lia)) as D2.
  unfold Hi, W, Lo. rewrite D1 at 1. rewrite D2 at 1. ring. }
assert (HLo : (0 <= Lo < 2 ^ s)%Z) by (apply Z.mod_pos_bound; exact Hps).
clearbody W Hi Lo.
(* [m W = q 2^192 + r] *)
set (r := ((m * W) mod 2 ^ 192)%Z).
set (q := (m * W / 2 ^ 192)%Z).
assert (HmW : (m * W = q * 2 ^ 192 + r)%Z).
{ pose proof (Z.div_mod (m * W) (2 ^ 192) ltac:(lia)). unfold q, r. lia. }
clearbody r q.
(* the same in [R] *)
assert (HTR : IZR T = (IZR Hi * bpow radix2 192 + IZR W) * bpow radix2 s + IZR Lo).
{ rewrite HT, !plus_IZR, !mult_IZR, !plus_IZR, !mult_IZR, !km_IZR_pow2 by lia. reflexivity. }
assert (HmWR : IZR m * IZR W = IZR q * bpow radix2 192 + IZR r).
{ rewrite <- mult_IZR, HmW, plus_IZR, mult_IZR, km_IZR_pow2 by lia. reflexivity. }
assert (HLoR : 0 <= IZR Lo <= bpow radix2 s - 1).
{ rewrite <- km_IZR_pow2 by lia. split; [apply IZR_le; lia |].
  rewrite <- minus_IZR. apply IZR_le. lia. }
assert (HmR : 0 <= IZR m) by (apply IZR_le; lia).
set (P := bpow radix2 (e - 1203)).
set (Ps := bpow radix2 s) in *.
set (Q := bpow radix2 (-179)).
set (b192 := bpow radix2 192) in *.
assert (HP : 0 < P) by apply bpow_gt_0.
assert (HPQ : Ps * P = Q).
{ unfold Ps, P, Q, s. rewrite <- bpow_plus. f_equal. ring. }
assert (HbQ : b192 * Q = 8192).
{ unfold b192, Q. rewrite <- bpow_plus. reflexivity. }
exists (m * Hi + q)%Z, (IZR m * (IZR Lo + (B - IZR T)) * P).
split.
- assert (E1 : IZR m * IZR T * P =
               8192 * (IZR m * IZR Hi) + IZR m * IZR W * Q + IZR m * IZR Lo * P).
  { rewrite HTR.
    replace (IZR m * ((IZR Hi * b192 + IZR W) * Ps + IZR Lo) * P) with
      (IZR m * IZR Hi * (b192 * (Ps * P)) + IZR m * IZR W * (Ps * P) + IZR m * IZR Lo * P)
      by ring.
    rewrite HPQ, HbQ. ring. }
  assert (E2 : IZR m * IZR W * Q = 8192 * IZR q + IZR r * Q).
  { rewrite HmWR.
    replace ((IZR q * b192 + IZR r) * Q) with (IZR q * (b192 * Q) + IZR r * Q) by ring.
    rewrite HbQ. ring. }
  rewrite plus_IZR, mult_IZR.
  transitivity (IZR m * IZR T * P + IZR m * (B - IZR T) * P); [ring |].
  rewrite E1, E2. ring.
- (* [0 <= Lo + θ <= 2^s] with [θ = B - T] in [[0, 1]] *)
  assert (Hth : 0 <= IZR Lo + (B - IZR T) <= Ps) by lra.
  split.
  + apply Rmult_le_pos; [apply Rmult_le_pos |]; lra.
  + rewrite <- HPQ, <- Rmult_assoc.
    apply Rmult_le_compat_r; [lra |].
    apply Rmult_le_compat_l; lra.
Qed.

Lemma big_prod :
  forall m w0 w1 w2, (0 <= m < 2 ^ 53)%Z ->
  (0 <= w0 < 2 ^ 64)%Z -> (0 <= w1 < 2 ^ 64)%Z -> (0 <= w2 < 2 ^ 64)%Z ->
  let c := (Z.shiftr (m * w2) 64 + (m * w1) mod 2 ^ 64)%Z in
  let R := ((m * (w0 * 2 ^ 128 + w1 * 2 ^ 64 + w2)) mod 2 ^ 192)%Z in
  (c mod 2 ^ 64 = Z.shiftr R 64 mod 2 ^ 64 /\
   (m * w0 + Z.shiftr (m * w1) 64 + Z.shiftr c 64) mod 2 ^ 64 = Z.shiftr R 128)%Z.
Proof.
intros m w0 w1 w2 Hm H0 H1 H2 c R.
assert (Ec : c = (m * w2 / 2 ^ 64 + (m * w1) mod 2 ^ 64)%Z)
  by (unfold c; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
assert (ER : R = ((m * (w0 * 2 ^ 128 + w1 * 2 ^ 64 + w2)) mod 2 ^ 192)%Z) by reflexivity.
clearbody c R.
rewrite !Z.shiftr_div_pow2 by lia.
(* With [D] the top limb before its carry out, [m (w0 2^128 + w1 2^64 + w2)]
   is [D 2^128 + (c mod 2^64) 2^64 + (m w2) mod 2^64]. *)
set (D := (m * w0 + m * w1 / 2 ^ 64 + c / 2 ^ 64)%Z).
assert (ED : D = (m * w0 + m * w1 / 2 ^ 64 + c / 2 ^ 64)%Z) by reflexivity.
clearbody D.
pose proof (Z.div_mod (m * w2) (2 ^ 64) ltac:(lia)) as Da.
pose proof (Z.mod_pos_bound (m * w2) (2 ^ 64) ltac:(lia)) as Ba.
pose proof (Z.div_mod (m * w1) (2 ^ 64) ltac:(lia)) as Db.
pose proof (Z.mod_pos_bound (m * w1) (2 ^ 64) ltac:(lia)) as Bb.
pose proof (Z.div_mod c (2 ^ 64) ltac:(lia)) as Dc.
pose proof (Z.mod_pos_bound c (2 ^ 64) ltac:(lia)) as Bc.
pose proof (Z.div_mod D (2 ^ 64) ltac:(lia)) as DD.
pose proof (Z.mod_pos_bound D (2 ^ 64) ltac:(lia)) as BD.
assert (HR : R = (D mod 2 ^ 64 * 2 ^ 128 + c mod 2 ^ 64 * 2 ^ 64 + (m * w2) mod 2 ^ 64)%Z).
{ rewrite ER. symmetry. apply (Z.mod_unique _ _ (D / 2 ^ 64)); [left; lia | lia]. }
clear ER.
split.
- assert (HR1 : (R / 2 ^ 64 = D mod 2 ^ 64 * 2 ^ 64 + c mod 2 ^ 64)%Z).
  { symmetry. apply (Z.div_unique _ _ _ ((m * w2) mod 2 ^ 64)); [left; lia | lia]. }
  rewrite HR1. apply (Z.mod_unique _ _ (D mod 2 ^ 64)); [left; lia | lia].
- apply (Z.div_unique _ _ _ (c mod 2 ^ 64 * 2 ^ 64 + (m * w2) mod 2 ^ 64)); [left; lia | lia].
Qed.

(** [x / 2^a] split at bit [b] *)
Local Lemma dig :
  forall x a b c, (0 <= a)%Z -> (0 <= b)%Z -> c = (a + b)%Z ->
  (x / 2 ^ a = (x / 2 ^ a) mod 2 ^ b + 2 ^ b * (x / 2 ^ c))%Z.
Proof.
intros x a b c Ha Hb ->.
assert (Hb2 : (2 ^ b <> 0)%Z) by (apply Z.pow_nonzero; lia).
rewrite Z.pow_add_r, <- Z.div_div by (try apply Z.pow_pos_nonneg; lia).
pose proof (Z.div_mod (x / 2 ^ a) (2 ^ b) Hb2). lia.
Qed.

Lemma big_split :
  forall R, (0 <= R < 2 ^ 192)%Z ->
  let r2 := Z.shiftr R 128 in
  let r1 := (Z.shiftr R 64 mod 2 ^ 64)%Z in
  let a0 := Z.lor (Z.shiftl r2 13 mod 2 ^ 64) (Z.shiftr r1 51) in
  let a := if (a0 <? 2 ^ 63)%Z then a0 else (a0 - 2 ^ 64)%Z in
  let N0 := Z.shiftr (R + 2 ^ 178) 179 in
  (Z.shiftr ((r2 + 2 ^ 50) mod 2 ^ 64) 51 = N0 mod 8192 /\
   R = N0 * 2 ^ 179 + Z.shiftr a 11 * 2 ^ 126 + Z.land (Z.shiftr r1 9) (2 ^ 53 - 1) * 2 ^ 73
       + R mod 2 ^ 73 /\
   - 2 ^ 52 <= Z.shiftr a 11 < 2 ^ 52 /\ 0 <= Z.land (Z.shiftr r1 9) (2 ^ 53 - 1) < 2 ^ 53)%Z.
Proof.
intros R HR r2 r1 a0 a N0.
assert (Er2 : r2 = (R / 2 ^ 128)%Z)
  by (change r2 with (Z.shiftr R 128); apply Z.shiftr_div_pow2; lia).
assert (Er1 : r1 = ((R / 2 ^ 64) mod 2 ^ 64)%Z)
  by (change r1 with (Z.shiftr R 64 mod 2 ^ 64)%Z; rewrite Z.shiftr_div_pow2 by lia;
      reflexivity).
assert (Ea0 : a0 = Z.lor ((r2 * 2 ^ 13) mod 2 ^ 64) (r1 / 2 ^ 51)).
{ change a0 with (Z.lor (Z.shiftl r2 13 mod 2 ^ 64) (Z.shiftr r1 51)).
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. }
assert (Ea : a = if (a0 <? 2 ^ 63)%Z then a0 else (a0 - 2 ^ 64)%Z) by reflexivity.
assert (EN0 : N0 = ((R + 2 ^ 178) / 2 ^ 179)%Z)
  by (change N0 with (Z.shiftr (R + 2 ^ 178) 179); apply Z.shiftr_div_pow2; lia).
clearbody r2 r1 a0 a N0.
rewrite !Z.shiftr_div_pow2 by lia.
replace (2 ^ 53 - 1)%Z with (Z.ones 53) by reflexivity.
rewrite !Z.land_ones by lia.
(* The fields of [R] at bits 0, 64, 73, 115, 126, 128, 178 and 179 *)
pose proof (Z.div_mod R (2 ^ 64) ltac:(lia)) as D0.
pose proof (dig R 64 9 73 ltac:(lia) ltac:(lia) eq_refl) as D1.
pose proof (dig R 73 42 115 ltac:(lia) ltac:(lia) eq_refl) as D2.
pose proof (dig R 115 11 126 ltac:(lia) ltac:(lia) eq_refl) as D3.
pose proof (dig R 126 2 128 ltac:(lia) ltac:(lia) eq_refl) as D4.
pose proof (dig R 128 50 178 ltac:(lia) ltac:(lia) eq_refl) as D5.
pose proof (dig R 178 1 179 ltac:(lia) ltac:(lia) eq_refl) as D6.
pose proof (Z.mod_pos_bound R (2 ^ 64) ltac:(lia)) as B0.
pose proof (Z.mod_pos_bound (R / 2 ^ 64) (2 ^ 9) ltac:(lia)) as B1.
pose proof (Z.mod_pos_bound (R / 2 ^ 73) (2 ^ 42) ltac:(lia)) as B2.
pose proof (Z.mod_pos_bound (R / 2 ^ 115) (2 ^ 11) ltac:(lia)) as B3.
pose proof (Z.mod_pos_bound (R / 2 ^ 126) (2 ^ 2) ltac:(lia)) as B4.
pose proof (Z.mod_pos_bound (R / 2 ^ 128) (2 ^ 50) ltac:(lia)) as B5.
pose proof (Z.mod_pos_bound (R / 2 ^ 178) (2 ^ 1) ltac:(lia)) as B6.
assert (B7 : (0 <= R / 2 ^ 179 < 2 ^ 13)%Z).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
set (g0 := (R mod 2 ^ 64)%Z) in *.
set (g1 := ((R / 2 ^ 64) mod 2 ^ 9)%Z) in *.
set (g2 := ((R / 2 ^ 73) mod 2 ^ 42)%Z) in *.
set (g3 := ((R / 2 ^ 115) mod 2 ^ 11)%Z) in *.
set (g4 := ((R / 2 ^ 126) mod 2 ^ 2)%Z) in *.
set (g5 := ((R / 2 ^ 128) mod 2 ^ 50)%Z) in *.
set (g6 := ((R / 2 ^ 178) mod 2 ^ 1)%Z) in *.
set (g7 := (R / 2 ^ 179)%Z) in *.
clearbody g0 g1 g2 g3 g4 g5 g6 g7.
(* [r2], [r1], [a0], [a] and [N0] in fields *)
assert (Er2' : (r2 = g5 + 2 ^ 50 * g6 + 2 ^ 51 * g7)%Z) by lia.
assert (Er1' : (r1 = g1 + 2 ^ 9 * g2 + 2 ^ 51 * g3 + 2 ^ 62 * g4)%Z).
{ rewrite Er1. symmetry. apply (Z.mod_unique _ _ (R / 2 ^ 128)); [left; lia | lia]. }
assert (Ex : ((r2 * 2 ^ 13) mod 2 ^ 64 = (g5 + 2 ^ 50 * g6) * 2 ^ 13)%Z).
{ symmetry. apply (Z.mod_unique _ _ g7); [left; lia | lia]. }
assert (Ey : (r1 / 2 ^ 51 = g3 + 2 ^ 11 * g4)%Z).
{ symmetry. apply (Z.div_unique _ _ _ (g1 + 2 ^ 9 * g2)); [left; lia | lia]. }
assert (Ea0' : (a0 = (g5 + 2 ^ 50 * g6) * 2 ^ 13 + (g3 + 2 ^ 11 * g4))%Z).
{ rewrite Ea0, Ex, Ey. apply Limbs.lor_low; lia. }
(* [a0] is bits 115..178 of [R], and [a] that read as an [i64] *)
assert (Ea' : (a = g3 + 2 ^ 11 * g4 + 2 ^ 13 * g5 - 2 ^ 63 * g6)%Z).
{ rewrite Ea. destruct (Z.ltb_spec a0 (2 ^ 63)); cbv iota; lia. }
assert (Eas : (a / 2 ^ 11 = g4 + 4 * g5 - 2 ^ 52 * g6)%Z).
{ symmetry. apply (Z.div_unique _ _ _ g3); [left; lia | lia]. }
assert (Ec9 : (r1 / 2 ^ 9 = g2 + 2 ^ 42 * g3 + 2 ^ 53 * g4)%Z).
{ symmetry. apply (Z.div_unique _ _ _ g1); [left; lia | lia]. }
assert (Ec : ((r1 / 2 ^ 9) mod 2 ^ 53 = g2 + 2 ^ 42 * g3)%Z).
{ rewrite Ec9. symmetry. apply (Z.mod_unique _ _ g4); [left; lia | lia]. }
assert (El : (R mod 2 ^ 73 = g0 + 2 ^ 64 * g1)%Z).
{ symmetry. apply (Z.mod_unique _ _ (R / 2 ^ 73)); [left; lia | lia]. }
(* [N0] rounds [R / 2^179] to nearest, so it adds bit 178 to the top field. *)
assert (EN : (N0 = g7 + g6)%Z).
{ rewrite EN0. symmetry.
  apply (Z.div_unique _ _ _ (g0 + 2 ^ 64 * g1 + 2 ^ 73 * g2 + 2 ^ 115 * g3 + 2 ^ 126 * g4
                             + 2 ^ 128 * g5 + 2 ^ 178 * (1 - g6))); [left; lia | lia]. }
rewrite EN, Eas, Ec, El.
split; [| split; [lia | split; lia]].
pose proof (Z.div_mod (g7 + g6) 8192 ltac:(lia)) as DN.
pose proof (Z.mod_pos_bound (g7 + g6) 8192 ltac:(lia)) as BN.
assert (Em : ((r2 + 2 ^ 50) mod 2 ^ 64 =
              2 ^ 51 * ((g7 + g6) mod 8192) + (g5 + 2 ^ 50 * (1 - g6)))%Z).
{ symmetry. apply (Z.mod_unique _ _ ((g7 + g6) / 8192)); [left; lia | lia]. }
rewrite Em. symmetry. apply (Z.div_unique _ _ _ (g5 + 2 ^ 50 * (1 - g6))); [left; lia | lia].
Qed.
