(** * The reduction of the fast path of the logarithms

    [DyadicLog.ln_split] of [Model.v] writes a finite [x > 0] as [m 2^e]
    exactly, with [m] in the interval [[(362 + i) / 512, (363 + i) /
    512)] of the table, from the bits of [x], or of [x 2^52] for a
    subnormal [x] ([ln_split_correct]). [ln_z_exact] shows that [z = r m -
    1] is computed exactly as [z1 + z2] with [z1 = RN(z)], from [p =
    RN(r m)], the exact error of the product and Fast2Sum, for any [r]
    and [m] with [r m] within [1/256] of 1, and [ln_z_fma] that the error
    of the product is the same with and without an FMA. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Relative Sterbenz.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct FastRound.
From Inari Require Limbs MulRuTiny CancelLanes FastExpErr SqrtSlow.

Open Scope R_scope.

(** ** Literals *)

Lemma one_R : is_finite DyadicExp.one = true /\ B2R DyadicExp.one = 1.
Proof.
split; [vm_compute; reflexivity |].
rewrite <- SF2R_B2SF.
replace (B2SF DyadicExp.one) with (SpecFloat.S754_finite false 4503599627370496 (-52))
  by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

Lemma two52_R : is_finite DyadicLog.two52 = true /\ B2R DyadicLog.two52 = bpow radix2 52.
Proof.
split; [vm_compute; reflexivity |].
rewrite <- SF2R_B2SF.
replace (B2SF DyadicLog.two52) with (SpecFloat.S754_finite false 4503599627370496 0)
  by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

(** ** The fields of the bits *)

(** A finite [x > 0] is the pattern [c] with [0 < c < 2047 2^52], and its
    value is [magnitude c]. *)
Lemma pos_bits :
  forall x, is_finite x = true -> 0 < B2R x ->
  exists c, (0 < c < 2047 * 2 ^ 52)%Z /\ to_bits x = c /\ B2R x = magnitude c.
Proof.
intros x Fx Hx.
destruct (to_bits_finite x Fx) as (c & Hc & Hb).
destruct (from_bits_finite (Bsign x) c Hc) as (_ & _ & Hv).
rewrite <- Hb, from_to_bits in Hv.
destruct (magnitude_bounds c (proj1 Hc)) as ((H0 & _) & _).
destruct (Bsign x); cbv iota in Hv.
- lra.
- exists c.
  assert (Hc0 : c <> 0%Z) by (intros ->; rewrite magnitude_0 in Hv; lra).
  split; [lia |]. split; [unfold sign_bit in Hb; lia | exact Hv].
Qed.

(** [a / 512 <= n 2^e] if [a 2^s <= n] and [e = -(9 + s)], and the same
    with [<]. *)
Lemma scaled_le :
  forall a n s e, (0 <= s)%Z -> e = (- (9 + s))%Z -> (a * 2 ^ s <= n)%Z ->
  IZR a / 512 <= IZR n * bpow radix2 e.
Proof.
intros a n s e Hs -> H.
apply IZR_le in H. rewrite mult_IZR in H.
change (2 ^ s)%Z with (Zpower radix2 s) in H. rewrite IZR_Zpower in H by exact Hs.
replace (IZR a / 512) with (IZR a * bpow radix2 s * bpow radix2 (- (9 + s))).
- apply Rmult_le_compat_r; [apply bpow_ge_0 | exact H].
- rewrite Rmult_assoc, <- bpow_plus. replace (s + - (9 + s))%Z with (-9)%Z by ring.
  change (bpow radix2 (-9)) with (/ 512). reflexivity.
Qed.

Lemma scaled_lt :
  forall a n s e, (0 <= s)%Z -> e = (- (9 + s))%Z -> (n < a * 2 ^ s)%Z ->
  IZR n * bpow radix2 e < IZR a / 512.
Proof.
intros a n s e Hs -> H.
apply IZR_lt in H. rewrite mult_IZR in H.
change (2 ^ s)%Z with (Zpower radix2 s) in H. rewrite IZR_Zpower in H by exact Hs.
replace (IZR a / 512) with (IZR a * bpow radix2 s * bpow radix2 (- (9 + s))).
- apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact H].
- rewrite Rmult_assoc, <- bpow_plus. replace (s + - (9 + s))%Z with (-9)%Z by ring.
  change (bpow radix2 (-9)) with (/ 512). reflexivity.
Qed.

(** The split of a normal pattern [c]: [j] is the top 9 bits of the
    stored significand [M], [m] is [1 + M 2^-52] (or half of it if [j >=
    212]), and [c] has the value [m 2^(E - 1023 + k)] for its biased
    exponent [E]. *)
Lemma split_normal :
  forall c, (2 ^ 52 <= c < 2047 * 2 ^ 52)%Z ->
  let j := Z.land (Z.shiftr c 43) 0x1ff in
  let k := if Z.leb 212 j then 1%Z else 0%Z in
  let m := from_bits (Z.lor (Z.land c DyadicLog.frac) (Z.shiftl (1023 - k) 52)) in
  let i := if Z.eqb k 1 then (Z.shiftr j 1 - 106)%Z else (j + 150)%Z in
  is_finite m = true /\ (0 <= i < 362)%Z /\
  (-1022 <= Z.shiftr c 52 - 1023 + k <= 1024)%Z /\
  magnitude c = B2R m * bpow radix2 (Z.shiftr c 52 - 1023 + k) /\
  IZR (362 + i) / 512 <= B2R m < IZR (363 + i) / 512.
Proof.
intros c Hc. cbv zeta.
assert (HcE : (c = c / 2 ^ 52 * 2 ^ 52 + c mod 2 ^ 52 /\ 1 <= c / 2 ^ 52 <= 2046 /\
  0 <= c mod 2 ^ 52 < 2 ^ 52)%Z) by zlia.
assert (Ej : Z.land (Z.shiftr c 43) 0x1ff = (c mod 2 ^ 52 / 2 ^ 43)%Z).
{ rewrite Z.shiftr_div_pow2 by lia. change 0x1ff%Z with (Z.ones 9).
  rewrite Z.land_ones by lia. zlia. }
assert (Ef : Z.land c DyadicLog.frac = (c mod 2 ^ 52)%Z).
{ change DyadicLog.frac with (Z.ones 52). apply Z.land_ones. lia. }
assert (Es : Z.shiftr c 52 = (c / 2 ^ 52)%Z) by (apply Z.shiftr_div_pow2; lia).
rewrite Ej, Ef, Es.
set (E := (c / 2 ^ 52)%Z) in *. set (M := (c mod 2 ^ 52)%Z) in *.
destruct HcE as (HcE & HE & HM).
assert (HJ : (0 <= M / 2 ^ 43 < 512 /\ M / 2 ^ 43 * 2 ^ 43 <= M < (M / 2 ^ 43 + 1) * 2 ^ 43)%Z)
  by zlia.
set (J := (M / 2 ^ 43)%Z) in *. clearbody J.
(* The value of [c]: [(M + 2^52) 2^(E - 1075)]. *)
assert (Hc' : magnitude c = F2R (Float radix2 (M + 2 ^ 52) (E - 1075))).
{ rewrite HcE. rewrite magnitude_split by lia.
  replace (E =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  replace (Z.max E 1) with E by lia. reflexivity. }
rewrite Hc'.
(* [m] is the pattern [(1023 - k) 2^52 + M], so its value is
   [(M + 2^52) 2^(-52 - k)]. *)
assert (Hm : forall k, (0 <= k <= 1)%Z ->
  is_finite (from_bits (Z.lor M (Z.shiftl (1023 - k) 52))) = true /\
  B2R (from_bits (Z.lor M (Z.shiftl (1023 - k) 52))) =
    F2R (Float radix2 (M + 2 ^ 52) (-52 - k))).
{ intros k Hk.
  rewrite Z.shiftl_mul_pow2, Z.lor_comm, Limbs.lor_low by lia.
  destruct (from_bits_finite false ((1023 - k) * 2 ^ 52 + M)) as (Fm & _ & Em);
    [split; [lia | simpl Z.pow in *; lia] |].
  unfold sign_bit in Fm, Em. rewrite Z.add_0_l in Fm, Em. cbv iota in Em.
  split; [exact Fm |]. rewrite Em, magnitude_split by lia.
  replace (1023 - k =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  replace (Z.max (1023 - k) 1 - 1075)%Z with (-52 - k)%Z by lia. reflexivity. }
assert (Hv : forall k, F2R (Float radix2 (M + 2 ^ 52) (E - 1075)) =
  F2R (Float radix2 (M + 2 ^ 52) (-52 - k)) * bpow radix2 (E - 1023 + k)).
{ intros k. unfold F2R; cbn [Fnum Fexp].
  rewrite Rmult_assoc, <- bpow_plus. do 2 f_equal. ring. }
destruct (Z.leb_spec 212 J) as [HJk | HJk]; cbv iota.
- (* [M >= 212 2^43]: [m = (M + 2^52) 2^-53], [i = J / 2 - 106]. *)
  change (Z.eqb 1 1) with true. cbv iota.
  destruct (Hm 1%Z ltac:(lia)) as (Fm & Em).
  rewrite Em, <- Hv. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1)%Z with 2%Z.
  unfold F2R; cbn [Fnum Fexp].
  split; [exact Fm |]. split; [zlia |]. split; [lia |]. split; [reflexivity |].
  split.
  + apply (scaled_le _ _ 44); [lia | lia | zlia].
  + apply (scaled_lt _ _ 44); [lia | lia | zlia].
- (* [M < 212 2^43]: [m = (M + 2^52) 2^-52], [i = J + 150]. *)
  change (Z.eqb 0 1) with false. cbv iota.
  destruct (Hm 0%Z ltac:(lia)) as (Fm & Em).
  rewrite Em, <- Hv.
  unfold F2R; cbn [Fnum Fexp].
  split; [exact Fm |]. split; [lia |]. split; [lia |]. split; [reflexivity |].
  split.
  + apply (scaled_le _ _ 43); [lia | lia | zlia].
  + apply (scaled_lt _ _ 43); [lia | lia | zlia].
Qed.

Theorem ln_split_correct :
  forall x, is_finite x = true -> 0 < B2R x ->
  let '(e, m, i) := DyadicLog.ln_split x in
  is_finite m = true /\ (0 <= i < 362)%Z /\ (-1074 <= e <= 1024)%Z /\
  B2R x = B2R m * bpow radix2 e /\ IZR (362 + i) / 512 <= B2R m < IZR (363 + i) / 512.
Proof.
intros x Fx Hx.
destruct (pos_bits x Fx Hx) as (c & Hc & Hb & Hv).
unfold DyadicLog.ln_split. rewrite Hb.
destruct (Z.ltb_spec c (2 ^ 52)) as [Hs | Hs]; cbv beta iota zeta.
- (* A subnormal [x = c 2^-1074]: [x 2^52] is exact and normal. *)
  destruct two52_R as [F52 E52].
  assert (Hm0 : magnitude (0 * 2 ^ 52 + c) = IZR c * bpow radix2 (-1074)).
  { rewrite magnitude_split by lia. reflexivity. }
  rewrite Z.mul_0_l, Z.add_0_l in Hm0.
  destruct (magnitude_bounds c ltac:(lia)) as ((_ & Hlt) & _).
  replace (c / 2 ^ 52)%Z with 0%Z in Hlt by (symmetry; apply Z.div_small; lia).
  change (0 - 1022)%Z with (-1022)%Z in Hlt.
  assert (Hc1 : 1 <= IZR c) by (apply IZR_le; lia).
  pose proof (bpow_gt_0 radix2 (-1074)) as Hb0.
  assert (Hlo : bpow radix2 (-1074) <= B2R x) by (rewrite Hv, Hm0; nra).
  assert (Hhi : B2R x < bpow radix2 (-1022)) by (rewrite Hv; exact Hlt).
  assert (Hx2 : is_finite (mul x DyadicLog.two52) = true /\
    B2R (mul x DyadicLog.two52) = B2R x * bpow radix2 52).
  { destruct (MulRuTiny.mul_RN_spec x DyadicLog.two52 Fx F52) as (F & E & _).
    - rewrite E52, Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 52); nra).
      apply Rle_trans with (bpow radix2 (-1022) * bpow radix2 52).
      + apply Rmult_le_compat_r; [apply bpow_ge_0 | lra].
      + rewrite <- bpow_plus. apply bpow_le. lia.
    - split; [exact F |]. rewrite E, E52.
      apply round_generic; [typeclasses eauto |].
      apply SqrtSlow.format_scale_up; [apply generic_format_B2R | lia]. }
  destruct Hx2 as (Fx2 & Ex2).
  assert (Hx2lo : bpow radix2 (-1022) <= B2R (mul x DyadicLog.two52)).
  { rewrite Ex2. replace (-1022)%Z with (-1074 + 52)%Z by reflexivity.
    rewrite bpow_plus. apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Hlo]. }
  destruct (pos_bits (mul x DyadicLog.two52) Fx2
    ltac:(pose proof (bpow_gt_0 radix2 (-1022)); lra)) as (c2 & Hc2 & Hb2 & Hv2).
  rewrite Hb2.
  assert (Hn2 : (2 ^ 52 <= c2)%Z).
  { destruct (Z.lt_ge_cases c2 (2 ^ 52)) as [Hl | Hl]; [exfalso | exact Hl].
    destruct (magnitude_bounds c2 ltac:(lia)) as ((_ & Hlt2) & _).
    replace (c2 / 2 ^ 52)%Z with 0%Z in Hlt2 by (symmetry; apply Z.div_small; lia).
    change (0 - 1022)%Z with (-1022)%Z in Hlt2. lra. }
  pose proof (split_normal c2 (conj Hn2 (proj2 Hc2))) as H. cbv zeta in H.
  destruct H as (Fm & Hi & He & Hmag & Hlo2 & Hhi2).
  split; [exact Fm |]. split; [exact Hi |]. split; [lia |].
  split; [| split; [exact Hlo2 | exact Hhi2]].
  rewrite bpow_plus.
  match goal with |- _ = ?m * (?a * ?b) => replace (m * (a * b)) with (a * (m * b)) by ring end.
  rewrite <- Hmag, <- Hv2, Ex2.
  rewrite Rmult_comm, Rmult_assoc, <- bpow_plus. rewrite Rmult_1_r. reflexivity.
- (* A normal [x]. *)
  pose proof (split_normal c (conj Hs (proj2 Hc))) as H. cbv zeta in H.
  destruct H as (Fm & Hi & He & Hmag & Hlo2 & Hhi2).
  split; [exact Fm |]. split; [exact Hi |]. split; [lia |].
  split; [| split; [exact Hlo2 | exact Hhi2]].
  rewrite Z.add_0_l, Hv. exact Hmag.
Qed.

(** ** [z = r m - 1] *)

(** A float of magnitude at least [1/2] is a multiple of [2^-53]. *)
Lemma mult_53 :
  forall x : f64, / 2 <= Rabs (B2R x) -> exists n, B2R x = IZR n * bpow radix2 (-53).
Proof.
intros x Hx.
assert (G : generic_format radix2 fexp64 (B2R x)) by apply generic_format_B2R.
unfold generic_format, F2R in G. cbn [Fnum Fexp] in G.
assert (Hc : (-53 <= cexp radix2 fexp64 (B2R x))%Z).
{ unfold cexp.
  assert (Hm : (0 <= mag radix2 (B2R x))%Z)
    by (apply mag_ge_bpow; change (bpow radix2 (0 - 1)) with (/ 2); exact Hx).
  unfold FLT_exp. lia. }
set (e := cexp radix2 fexp64 (B2R x)) in *.
set (n := Ztrunc (scaled_mantissa radix2 fexp64 (B2R x))) in *.
exists (n * 2 ^ (e + 53))%Z.
rewrite G at 1.
rewrite mult_IZR. change (2 ^ (e + 53))%Z with (Zpower radix2 (e + 53)).
rewrite IZR_Zpower by lia.
rewrite Rmult_assoc, <- bpow_plus. do 2 f_equal. ring.
Qed.

Lemma sub1 :
  forall n e, (e <= 0)%Z -> IZR n * bpow radix2 e - 1 = IZR (n - 2 ^ (- e)) * bpow radix2 e.
Proof.
intros n e He.
rewrite minus_IZR. change (2 ^ (- e))%Z with (Zpower radix2 (- e)).
rewrite IZR_Zpower by lia.
rewrite Rmult_minus_distr_r, <- bpow_plus. replace (- e + e)%Z with 0%Z by ring.
reflexivity.
Qed.

Lemma mult_ge :
  forall k e, k <> 0%Z -> bpow radix2 e <= Rabs (IZR k * bpow radix2 e).
Proof.
intros k e Hk.
rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 e)) by apply bpow_ge_0.
rewrite <- abs_IZR.
rewrite <- (Rmult_1_l (bpow radix2 e)) at 1.
apply Rmult_le_compat_r; [apply bpow_ge_0 |].
apply IZR_le. lia.
Qed.

(** The ulp of a nonzero number below 2 in magnitude is at most [2^-52]. *)
Lemma ulp_lt_2 :
  forall y, y <> 0 -> Rabs y < 2 -> ulp radix2 fexp64 y <= bpow radix2 (-52).
Proof.
intros y Hy Hl.
rewrite ulp_neq_0 by exact Hy.
apply bpow_le. unfold cexp, FLT_exp.
assert (H : (mag radix2 y <= 1)%Z)
  by (apply mag_le_bpow; [exact Hy | change (bpow radix2 1) with 2; exact Hl]).
lia.
Qed.

(** [r m] rounded to nearest is in [[1/2, 2)], so [two_prod_is_exact]
    holds for it, with and without an FMA. *)
Lemma ln_prod_exact :
  forall b r m, is_finite r = true -> is_finite m = true ->
  / 2 <= B2R r <= 2 -> / 2 <= B2R m <= 2 -> Rabs (B2R r * B2R m - 1) <= / 256 ->
  Generic.two_prod_is_exact b r m (mul r m) = true.
Proof.
intros b r m Fr Fm Hr Hm Hrm.
apply Rabs_le_inv in Hrm.
destruct (FastExpErr.mul_k r m 2 Fr Fm) as (Fp & _ & Bp);
  [rewrite Rabs_pos_eq by lra; lra | lra |].
apply Rabs_le_inv in Bp.
cbn [bpow radix_val radix2] in Bp.
assert (Hp : / 2 <= B2R (mul r m) < 2) by lra.
assert (E1 : (-1 <= Generic.exponent (mul r m))%Z).
{ apply MulRuTiny.exponent_ge; [exact Fp |].
  rewrite Rabs_pos_eq by lra. change (bpow radix2 (-1)) with (/ 2). lra. }
assert (E2 : (Generic.exponent (mul r m) < 1)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fp | lia |].
  rewrite Rabs_pos_eq by lra. change (bpow radix2 1) with 2. lra. }
assert (E3 : (Generic.exponent r < 2)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fr | lia |].
  rewrite Rabs_pos_eq by lra. change (bpow radix2 2) with 4. lra. }
assert (E4 : (Generic.exponent m < 2)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fm | lia |].
  rewrite Rabs_pos_eq by lra. change (bpow radix2 2) with 4. lra. }
unfold Generic.two_prod_is_exact. cbv zeta.
destruct b; rewrite ?andb_true_iff, ?Z.leb_le; lia.
Qed.

Theorem ln_z_exact :
  forall fma r m,
  is_finite r = true -> is_finite m = true -> / 2 <= B2R r <= 2 -> / 2 <= B2R m <= 2 ->
  Rabs (B2R r * B2R m - 1) <= / 256 ->
  let p := mul r m in
  let '(z1, z2) := Fast.fast_two_sum (sub p DyadicExp.one) (Generic.two_prod_err fma r m p) in
  is_finite z1 = true /\ is_finite z2 = true /\ B2R z1 + B2R z2 = B2R r * B2R m - 1 /\
  Rabs (B2R z2) <= bpow radix2 (-53) * Rabs (B2R z1) /\
  (B2R z1 = 0 \/ bpow radix2 (-106) <= Rabs (B2R z1)) /\ (B2R r = 1 -> B2R z2 = 0).
Proof.
intros fma r m Fr Fm Hr Hm Hrm.
cbv zeta. unfold Fast.fast_two_sum. cbv beta iota zeta.
destruct one_R as [F1 E1].
assert (G1 : generic_format radix2 fexp64 1) by (rewrite <- E1; apply generic_format_B2R).
pose proof (ln_prod_exact fma r m Fr Fm Hr Hm Hrm) as Hex.
destruct (two_prod_err_correct fma r m Fr Fm Hex) as (Fp & Ep & _ & Fe & Ee).
apply Rabs_le_inv in Hrm.
destruct (FastExpErr.mul_k r m 2 Fr Fm) as (_ & _ & Bp);
  [rewrite Rabs_pos_eq by lra; lra | lra |].
apply Rabs_le_inv in Bp.
cbn [bpow radix_val radix2] in Bp.
set (p := mul r m) in *.
set (pe := Generic.two_prod_err fma r m p) in *.
assert (Hp : / 2 <= B2R p <= 2) by lra.
(* [p - 1] is exact by Sterbenz's lemma (P. H. Sterbenz, Floating-point
   computation, 1974). *)
destruct (FastExpErr.sub_e p DyadicExp.one Fp F1) as (Fd & Ed & _);
  [rewrite E1; apply Rabs_le; lra |].
assert (Ed' : B2R (sub p DyadicExp.one) = B2R p - 1).
{ rewrite Ed, E1. apply round_generic; [typeclasses eauto |].
  apply sterbenz; [typeclasses eauto .. | apply generic_format_B2R | exact G1 | lra]. }
set (d := sub p DyadicExp.one) in *.
destruct (FastExpErr.add_e d pe Fd Fe) as (Fz1 & Ez1 & _);
  [rewrite Ed', Ee; apply Rabs_le; lra |].
set (z1 := add d pe) in *.
replace (B2R d + B2R pe) with (B2R r * B2R m - 1) in Ez1 by (rewrite Ed', Ee; ring).
(* [r], [m] and [p] are multiples of [2^-53], so [p - 1] is one too, and
   [r m - 1] is a multiple of [2^-106]. *)
destruct (mult_53 r) as (nr & Er); [rewrite Rabs_pos_eq by lra; lra |].
destruct (mult_53 m) as (nm & Em); [rewrite Rabs_pos_eq by lra; lra |].
destruct (mult_53 p) as (np & Enp); [rewrite Rabs_pos_eq by lra; lra |].
assert (Ew : B2R r * B2R m - 1 = IZR (nr * nm - 2 ^ 106) * bpow radix2 (-106)).
{ replace (B2R r * B2R m) with (IZR (nr * nm) * bpow radix2 (-106)).
  - apply (sub1 (nr * nm) (-106)). lia.
  - rewrite Er, Em, mult_IZR. change (-106)%Z with (-53 + -53)%Z. rewrite bpow_plus. ring. }
assert (Edn : B2R d = IZR (np - 2 ^ 53) * bpow radix2 (-53)).
{ rewrite Ed', Enp. apply (sub1 np (-53)). lia. }
(* The error of [p] is at most half an ulp of [r m], i.e. [2^-53]. *)
assert (Hpe : Rabs (B2R pe) <= bpow radix2 (-53)).
{ rewrite Ee, Ep, <- Rabs_Ropp.
  replace (- (B2R r * B2R m - RN (B2R r * B2R m)))
    with (RN (B2R r * B2R m) - B2R r * B2R m) by ring.
  pose proof (error_le_half_ulp radix2 fexp64 (fun z => negb (Z.even z)) (B2R r * B2R m)) as H.
  assert (U : ulp radix2 fexp64 (B2R r * B2R m) <= bpow radix2 (-52)).
  { apply ulp_lt_2; [apply Rgt_not_eq; lra | rewrite Rabs_pos_eq by lra; lra]. }
  assert (B : bpow radix2 (-53) = / 2 * bpow radix2 (-52))
    by (change (-53)%Z with (-1 + -52)%Z; rewrite bpow_plus; reflexivity).
  lra. }
(* Fast2Sum (T. J. Dekker, A floating-point technique for extending the
   available precision, Numer. Math. 18, 1971) is exact: [|pe| <= 2^-53 <=
   |p - 1|] unless [p = 1], and then [z1 = pe] and [z2 = 0]. *)
assert (Hz2 : is_finite (add pe (sub d z1)) = true /\
  B2R (add pe (sub d z1)) = B2R d + B2R pe - B2R z1).
{ destruct (Req_dec (B2R d) 0) as [D0 | D0].
  - assert (Ez1' : B2R z1 = B2R pe).
    { rewrite Ez1. replace (B2R r * B2R m - 1) with (B2R pe) by (rewrite Ee; lra).
      apply round_generic; [typeclasses eauto | apply generic_format_B2R]. }
    destruct (FastExpErr.sub_e d z1 Fd Fz1) as (Fs & Es & _);
      [rewrite D0, Ez1'; cbn [bpow radix_val radix2] in Hpe;
       rewrite Rabs_minus_sym, Rminus_0_r; lra |].
    assert (Es' : B2R (sub d z1) = - B2R pe).
    { rewrite Es, D0, Ez1', Rminus_0_l. apply round_generic; [typeclasses eauto |].
      apply generic_format_opp, generic_format_B2R. }
    destruct (FastExpErr.add_e pe (sub d z1) Fe Fs) as (Fz2 & Ez2 & _);
      [rewrite Es', Rplus_opp_r, Rabs_R0; lra |].
    split; [exact Fz2 |].
    rewrite Ez2, Es', Rplus_opp_r, round_0 by typeclasses eauto.
    rewrite D0, Ez1'. ring.
  - apply (CancelLanes.fast_two_sum d pe z1 Fd Fe); [| exact Fz1 |].
    + apply Rle_trans with (1 := Hpe). rewrite Edn. apply mult_ge.
      intros Hn. apply D0. rewrite Edn, Hn. ring.
    + rewrite Ez1, Ed', Ee. f_equal. ring. }
destruct Hz2 as (Fz2 & Ez2).
set (w := B2R r * B2R m - 1) in *.
assert (Ez2' : B2R (add pe (sub d z1)) = w - RN w) by (rewrite Ez2, <- Ez1, Ed', Ee; unfold w; ring).
split; [exact Fz1 |]. split; [exact Fz2 |].
split; [rewrite Ez2'; rewrite <- Ez1; ring |].
destruct (Z.eq_dec (nr * nm - 2 ^ 106) 0) as [W0 | W0].
- (* [r m = 1]: [z1 = z2 = 0]. *)
  assert (Hw0 : w = 0) by (rewrite Ew, W0; ring).
  assert (Hz10 : B2R z1 = 0) by (rewrite Ez1, Hw0; apply round_0; typeclasses eauto).
  rewrite Ez2', Hz10, <- Ez1, Hz10, Hw0, Rminus_0_r, Rabs_R0, Rmult_0_r.
  split; [lra |]. split; [left; reflexivity |]. intros _. reflexivity.
- assert (Hw : bpow radix2 (-106) <= Rabs w) by (rewrite Ew; apply mult_ge; exact W0).
  split; [| split].
  + (* The error of [z1 = RN(w)] is at most [2^-53 |z1|], as [w] is normal. *)
    rewrite Ez2', Rabs_minus_sym, Ez1.
    assert (B : bpow radix2 (-53) = / 2 * bpow radix2 (- 53 + 1))
      by (change (-53)%Z with (-1 + (-53 + 1))%Z; rewrite bpow_plus; reflexivity).
    rewrite B.
    apply (relative_error_N_FLT_round radix2 (-1074) 53 eq_refl).
    apply Rle_trans with (2 := Hw). apply bpow_le. lia.
  + right. rewrite Ez1.
    apply abs_round_ge_generic; [typeclasses eauto .. | | exact Hw].
    apply generic_format_FLT_bpow; [typeclasses eauto .. | lia].
  + (* [r = 1]: [w = m - 1] is a float by Sterbenz's lemma, so [z1 = w]. *)
    intros R1.
    assert (Gw : generic_format radix2 fexp64 w).
    { unfold w. rewrite R1, Rmult_1_l.
      apply sterbenz; [typeclasses eauto .. | apply generic_format_B2R | exact G1 | lra]. }
    rewrite Ez2', round_generic by first [exact Gw | typeclasses eauto]. ring.
Qed.

Theorem ln_z_fma :
  forall r m,
  is_finite r = true -> is_finite m = true -> / 2 <= B2R r <= 2 -> / 2 <= B2R m <= 2 ->
  Rabs (B2R r * B2R m - 1) <= / 256 ->
  Generic.two_prod_err true r m (mul r m) = Generic.two_prod_err false r m (mul r m).
Proof.
intros r m Fr Fm Hr Hm Hrm.
apply two_prod_err_fma_eq; [exact Fr | exact Fm | apply ln_prod_exact; assumption ..].
Qed.
