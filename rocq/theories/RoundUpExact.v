(** * [round_up_exact] rounds toward +inf

    [round_up_exact neg m e sticky] rounds [v] with [|v| = (m + δ) * 2^e]
    toward +inf, where [δ = 0] if not [sticky] and [0 < δ < 1] if [sticky].
    With [top = log2 m], [2^(e + top) <= |v| < 2^(e + top + 1)], so the last
    bit of the result has the weight [2^lsb] with
    [lsb = max (e + top - 52) (-1074)], the canonical exponent of [|v|].

    The function keeps the bits of [m] from that weight up, i.e. the integer
    part [k] of the scaled mantissa [q = |v| * 2^-lsb], and notes whether it
    drops anything nonzero, i.e. whether [q] is not an integer. Then
    [RU v = Zceil q * 2^lsb] if [v > 0], which adds one to [k] if [q] is not
    an integer, and [RU v = - Zfloor q * 2^lsb] if [v < 0]. If [sticky],
    [m >= 2^52] puts [lsb] at or above [e], so [δ] is among the dropped
    bits; without that precondition the function would be wrong. *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Spec Decompose.

(** ** Splitting [m] at the last bit *)

Open Scope Z_scope.

(** The [kept] bits of [m] and whether any bit it drops is nonzero, or
    [sticky]: [m << -shift] if [shift <= 0], and [m >> shift] if not.
    A [shift] of 128 or more drops all of [m], which is nonzero. *)
Lemma split_ok :
  forall m shift (sticky : bool),
  0 < m < 2^128 -> - 2^31 <= shift < 2^31 ->
  (shift <= 0 -> - shift < 128 /\ m * 2^(- shift) < 2^128) ->
  (if shift <=? 0 then
     let* ns := checked_i 32 (- shift) in
     let* k := shl 128 m ns in
     Some (k, sticky)
   else if 128 <=? shift then Some (0, true)
   else
     let* k := shr 128 m shift in
     let* p := shl 128 1 shift in
     let* mask := checked_u 128 (p - 1) in
     Some (k, sticky || negb (Z.land m mask =? 0))) =
  Some (if shift <=? 0 then (m * 2^(- shift), sticky)
        else (m / 2^shift, sticky || negb (m mod 2^shift =? 0))).
Proof.
intros m shift sticky Hm Hs Hl.
destruct (Z.leb_spec shift 0) as [H0|H0].
- destruct (Hl H0) as (Hn & Hw).
  rewrite checked_i_ok by lia. cbv beta iota.
  rewrite shl_ok by lia.
  reflexivity.
- destruct (Z.leb_spec 128 shift) as [H1|H1].
  + (* [m < 2^128 <= 2^shift]. *)
    assert (Hp : 2^128 <= 2^shift) by (apply Z.pow_le_mono_r; lia).
    rewrite Z.div_small, Z.mod_small by lia.
    replace (m =? 0) with false by lia.
    now rewrite Bool.orb_true_r.
  + assert (Hp : 0 < 2^shift < 2^128).
    { split; [apply Z.pow_pos_nonneg | apply Z.pow_lt_mono_r]; lia. }
    rewrite shr_ok by lia. cbv beta iota.
    rewrite shl_ok by lia. cbv beta iota.
    rewrite Z.mul_1_l.
    rewrite checked_u_ok by lia. cbv beta iota.
    (* The mask is [Z.ones shift], which keeps [m mod 2^shift]. *)
    replace (2^shift - 1) with (Z.ones shift) by (rewrite Z.ones_equiv; lia).
    rewrite Z.land_ones by lia.
    reflexivity.
Qed.

(** ** The scaled mantissa *)

Open Scope R_scope.

(** [IZR_Zpower] for [Z.pow], which [Model.v] uses. *)
Lemma IZR_pow2 : forall n, (0 <= n)%Z -> IZR (2^n) = bpow radix2 n.
Proof. intros n Hn. exact (IZR_Zpower radix2 n Hn). Qed.

(** [b = a * 2^-e] is [m + δ] if [a] is as in [round_up_exact_pre]. *)
Lemma scale_bounds :
  forall m e (sticky : bool) a,
  (if sticky then F2R (Float radix2 m e) < a < F2R (Float radix2 (m + 1) e)
   else a = F2R (Float radix2 m e)) ->
  IZR m <= a * bpow radix2 (- e) < IZR m + 1 /\
  (sticky = false <-> a * bpow radix2 (- e) = IZR m).
Proof.
intros m e sticky a Ha.
assert (Hs : forall k, F2R (Float radix2 k e) * bpow radix2 (- e) = IZR k).
{ intros k. unfold F2R; cbn [Fnum Fexp].
  rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_r.
  change (bpow radix2 0) with 1. ring. }
destruct sticky.
- assert (H1 := Rmult_lt_compat_r _ _ _ (bpow_gt_0 radix2 (- e)) (proj1 Ha)).
  assert (H2 := Rmult_lt_compat_r _ _ _ (bpow_gt_0 radix2 (- e)) (proj2 Ha)).
  rewrite Hs in H1, H2. rewrite plus_IZR in H2.
  split; [lra|].
  split; intros H; [discriminate H | exfalso; lra].
- rewrite Ha, Hs.
  split; [lra|].
  split; intros _; reflexivity.
Qed.

(** If [shift <= 0], nothing is dropped: [q = b * 2^n] with [n = -shift]
    is [m * 2^n] if not [sticky], and [b] itself if [sticky], as [n = 0]
    then. *)
Lemma scaled_shl :
  forall m n b (sticky : bool), (0 <= n)%Z ->
  IZR m <= b < IZR m + 1 -> (sticky = false <-> b = IZR m) ->
  (sticky = true -> n = 0)%Z ->
  IZR (m * 2^n) <= b * bpow radix2 n < IZR (m * 2^n) + 1 /\
  (sticky = false <-> b * bpow radix2 n = IZR (m * 2^n)).
Proof.
intros m n b sticky Hn Hb Hbm H0.
destruct sticky.
- rewrite (H0 eq_refl), Z.pow_0_r, Z.mul_1_r.
  change (bpow radix2 0) with 1. rewrite Rmult_1_r.
  split; [exact Hb | exact Hbm].
- rewrite (proj1 Hbm eq_refl), mult_IZR, IZR_pow2 by exact Hn.
  split; [lra|].
  split; intros _; reflexivity.
Qed.

(** If [shift > 0], [q = b / s] with [s = 2^shift]. Write [m = k * s + r]
    with [0 <= r < s]: then [k * s <= m <= b < m + 1 <= (k + 1) * s], and
    [q] is the integer [k] iff [b = m] and [r = 0]. *)
Lemma scaled_div :
  forall m s b (sticky : bool), (0 < s)%Z ->
  IZR m <= b < IZR m + 1 -> (sticky = false <-> b = IZR m) ->
  IZR (m / s) <= b * / IZR s < IZR (m / s) + 1 /\
  ((sticky || negb (m mod s =? 0)) = false <-> b * / IZR s = IZR (m / s)).
Proof.
intros m s b sticky Hs Hb Hbm.
assert (HS : 0 < IZR s) by now apply IZR_lt.
pose proof (Z.div_mod m s ltac:(lia)) as Hd.
pose proof (Z.mod_pos_bound m s Hs) as Hr.
set (k := (m / s)%Z) in *. set (r := (m mod s)%Z) in *.
clearbody k r.
assert (H1 : IZR k * IZR s <= IZR m).
{ rewrite <- mult_IZR. apply IZR_le. nia. }
assert (H2 : IZR m + 1 <= (IZR k + 1) * IZR s).
{ rewrite <- plus_IZR, <- plus_IZR, <- mult_IZR. apply IZR_le. nia. }
assert (Hq : b * / IZR s * IZR s = b) by (field; lra).
split; [split|split].
- apply Rmult_le_reg_r with (IZR s); [exact HS|]. rewrite Hq. lra.
- apply Rmult_lt_reg_r with (IZR s); [exact HS|]. rewrite Hq. lra.
- intros H. apply Bool.orb_false_elim in H as [H0 Hr0].
  apply Bool.negb_false_iff, Z.eqb_eq in Hr0.
  apply Hbm in H0.
  rewrite H0, Hd, Hr0, Z.add_0_r, mult_IZR. field. lra.
- intros H.
  assert (Hbk : b = IZR k * IZR s) by (rewrite <- H; field; lra).
  (* [k * s] is an integer in [[m, m + 1)], so it is [m]. *)
  assert (Hm : (k * s = m)%Z).
  { assert (Hl : IZR m <= IZR (k * s)) by (rewrite mult_IZR; lra).
    assert (Hu : IZR (k * s) < IZR (m + 1)) by (rewrite mult_IZR, plus_IZR; lra).
    apply le_IZR in Hl. apply lt_IZR in Hu. lia. }
  assert (Hr0 : r = 0%Z) by nia.
  replace sticky with false.
  2: { symmetry. apply Hbm. rewrite Hbk, <- mult_IZR, Hm. reflexivity. }
  rewrite Hr0. reflexivity.
Qed.

(** The bits [m] keeps and whether it drops a nonzero one, or [sticky],
    are the integer part [k] of [q = b * 2^-shift] and whether [q] is not
    an integer. *)
Lemma split_correct :
  forall m shift (sticky : bool) b,
  (0 < m < 2^128)%Z -> (- 2^31 <= shift < 2^31)%Z ->
  (shift <= 0 -> - shift < 128 /\ m * 2^(- shift) < 2^128)%Z ->
  (sticky = true -> 0 <= shift)%Z ->
  IZR m <= b < IZR m + 1 -> (sticky = false <-> b = IZR m) ->
  exists kept lost,
    (if shift <=? 0 then
       let* ns := checked_i 32 (- shift) in
       let* k := shl 128 m ns in
       Some (k, sticky)
     else if 128 <=? shift then Some (0, true)
     else
       let* k := shr 128 m shift in
       let* p := shl 128 1 shift in
       let* mask := checked_u 128 (p - 1) in
       Some (k, sticky || negb (Z.land m mask =? 0)))%Z = Some (kept, lost) /\
    IZR kept <= b * bpow radix2 (- shift) < IZR kept + 1 /\
    (lost = false <-> b * bpow radix2 (- shift) = IZR kept).
Proof.
intros m shift sticky b Hm Hs Hl Hst Hb Hbm.
rewrite split_ok by assumption.
destruct (Z.leb_spec shift 0) as [H0|H0].
- exists (m * 2^(- shift))%Z, sticky. split; [reflexivity|].
  apply scaled_shl; [lia | exact Hb | exact Hbm |].
  intros Hs1. specialize (Hst Hs1). lia.
- exists (m / 2^shift)%Z, (sticky || negb (m mod 2^shift =? 0)).
  split; [reflexivity|].
  rewrite bpow_opp, <- IZR_pow2 by lia.
  apply scaled_div; [apply Z.pow_pos_nonneg; lia | exact Hb | exact Hbm].
Qed.

(** ** Rounding *)

(** [k] and [lost] are the integer part of [q] and whether [q] is not an
    integer. *)
Lemma Zfloor_Zceil_split :
  forall q k (lost : bool),
  IZR k <= q < IZR k + 1 -> (lost = false <-> q = IZR k) ->
  Zfloor q = k /\ Zceil q = (if lost then k + 1 else k)%Z.
Proof.
intros q k lost Hq Hl.
split.
- apply Zfloor_imp. rewrite plus_IZR. exact Hq.
- destruct lost.
  + apply Zceil_imp.
    replace (k + 1 - 1)%Z with k by ring.
    rewrite plus_IZR.
    assert (q <> IZR k) by (intros H; apply Hl in H; discriminate H).
    lra.
  + rewrite (proj1 Hl eq_refl). apply Zceil_IZR.
Qed.

(** [2^lead <= a < 2^(lead + 1)] puts the last bit of [a] rounded at the
    weight [2^max (lead - 52) (-1074)]. *)
Lemma cexp_lsb :
  forall a lead, bpow radix2 lead <= a < bpow radix2 (lead + 1) ->
  cexp radix2 fexp64 a = Z.max (lead - 52) (-1074).
Proof.
intros a lead Ha.
unfold cexp.
rewrite mag_unique_pos with (e := (lead + 1)%Z).
2: { replace (lead + 1 - 1)%Z with lead by ring. exact Ha. }
unfold FLT_exp. lia.
Qed.

(** [RU v] from the integer part [k] of the scaled mantissa [q] of [|v|]
    and whether [q] is not an integer: [Zceil q] if [v > 0], and
    [- Zfloor q] if [v < 0] ([round_UP_opp]). *)
Lemma RU_split :
  forall v lsb k (lost : bool),
  cexp radix2 fexp64 (Rabs v) = lsb ->
  IZR k <= Rabs v * bpow radix2 (- lsb) < IZR k + 1 ->
  (lost = false <-> Rabs v * bpow radix2 (- lsb) = IZR k) ->
  RU v = cond_Ropp (Rlt_bool v 0)
    (F2R (Float radix2 (if lost && negb (Rlt_bool v 0) then k + 1 else k)%Z lsb)).
Proof.
intros v lsb k lost Hc Hq Hl.
destruct (Zfloor_Zceil_split _ _ _ Hq Hl) as (Hf & Hce).
destruct (Rlt_bool_spec v 0) as [Hn|Hp]; cbn [negb cond_Ropp].
- rewrite Bool.andb_false_r.
  rewrite (Rabs_left v Hn) in Hc, Hf.
  replace v with (- - v) at 1 by ring.
  rewrite round_UP_opp. f_equal.
  unfold round, scaled_mantissa. rewrite Hc, Hf. reflexivity.
- rewrite Bool.andb_true_r.
  rewrite (Rabs_pos_eq v Hp) in Hc, Hce.
  unfold round, scaled_mantissa. rewrite Hc, Hce. reflexivity.
Qed.

(** ** The float *)

(** A finite float is not NaN, so [Bmult_correct] and [Bsign_Bopp] give
    its sign. *)
Lemma finite_not_nan : forall x : f64, is_finite x = true -> is_nan x = false.
Proof. now intros [| | |]. Qed.

(** On overflow, the result is +inf or -MAX. *)
Lemma B2SF_overflow :
  forall neg : bool,
  B2SF (if neg then min_f64 else infinity) = binary_overflow 53 1024 mode_UP neg.
Proof. intros [|]; vm_compute; reflexivity. Qed.

(** [kept * 2^lsb] is exact if it is [|RU v|] and below [2^1024]. *)
Lemma mul_exact :
  forall neg v kept lsb p,
  (0 <= kept <= 2^53)%Z -> Rlt_bool v 0 = neg ->
  is_finite p = true -> Bsign p = false -> B2R p = bpow radix2 lsb ->
  RU v = cond_Ropp neg (F2R (Float radix2 kept lsb)) ->
  F2R (Float radix2 kept lsb) < bpow radix2 1024 ->
  rounds_up_to v (if neg then opp (mul (of_u64 kept) p) else mul (of_u64 kept) p).
Proof.
intros neg v kept lsb p Hk Hneg Fp Sp Rp HRU Hlt.
subst neg.
destruct (of_u64_exact kept Hk) as (Fk & Sk & Rk).
set (F := F2R (Float radix2 kept lsb)) in *.
assert (HF0 : 0 <= F) by (apply F2R_ge_0; cbn [Fnum]; lia).
(* [F = |RU v|] is a float. *)
assert (Fmt : generic_format radix2 fexp64 F).
{ replace F with (cond_Ropp (Rlt_bool v 0) (RU v))
    by (rewrite HRU; apply cond_Ropp_involutive).
  destruct (Rlt_bool v 0); [apply generic_format_opp|];
    apply generic_format_round; typeclasses eauto. }
generalize (@Bmult_correct 53 1024 _ _ mode_NE (of_u64 kept) p).
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE))
  with (round radix2 fexp64 ZnearestE).
rewrite Rk, Rp.
change (IZR kept * bpow radix2 lsb) with F.
rewrite round_generic by first [typeclasses eauto | exact Fmt].
rewrite Rabs_pos_eq, Rlt_bool_true by first [exact HF0 | exact Hlt].
rewrite Fk, Fp, Sk, Sp. cbn [andb xorb].
change (Bmult mode_NE (of_u64 kept) p) with (mul (of_u64 kept) p).
set (mag := mul (of_u64 kept) p). clearbody mag.
intros (HR & HFm & HS).
specialize (HS (finite_not_nan mag HFm)).
unfold rounds_up_to.
rewrite HRU, abs_cond_Ropp, Rabs_pos_eq, Rlt_bool_true by first [exact HF0 | exact Hlt].
destruct (Rlt_bool v 0); cbn [cond_Ropp]; unfold opp.
- rewrite B2R_Bopp, is_finite_Bopp, Bsign_Bopp, HR, HFm, HS
    by exact (finite_not_nan mag HFm).
  split; [reflexivity | split; reflexivity].
- rewrite HR, HFm, HS.
  split; [reflexivity | split; reflexivity].
Qed.

(** The end of [round_up_exact], from the bits [kept] of [|RU v|] and the
    weight [2^lsb] of the last one: [kept * 2^lsb >= 2^1024] iff
    [lsb + bits > 1024], where [bits = log2 kept + 1] is the number of bits
    of [kept]. *)
Lemma tail_correct :
  forall neg v lsb kept,
  (0 <= kept <= 2^53)%Z -> (-1074 <= lsb <= 2^21)%Z ->
  (kept = 0 -> lsb = -1074)%Z -> Rlt_bool v 0 = neg ->
  RU v = cond_Ropp neg (F2R (Float radix2 kept lsb)) ->
  exists r,
    (let kept := kept mod 2^64 in
     let* bits := checked_i 32 (64 - leading_zeros 64 kept) in
     let* overflow :=
       if negb (kept =? 0) then
         let* t := checked_i 32 (lsb + bits) in
         Some (1024 <? t)
       else Some false in
     if overflow then Some (if neg then min_f64 else infinity)
     else
       let* p := Generic.pow2 lsb in
       let mag := mul (of_u64 kept) p in
       Some (if neg then opp mag else mag))%Z = Some r /\
    rounds_up_to v r.
Proof.
intros neg v lsb kept Hk Hl Hk0 Hneg HRU.
cbv zeta.
rewrite (Z.mod_small kept) by lia.
destruct (Z.eqb_spec kept 0) as [H0|H0].
- (* [kept = 0]: the result is a zero, at [lsb = -1074]. *)
  subst kept. specialize (Hk0 eq_refl). subst lsb.
  change (leading_zeros 64 0) with 64%Z.
  rewrite (checked_i_ok 32 (64 - 64)) by lia. cbv beta iota.
  cbn [negb]. cbv beta iota.
  destruct (pow2_correct (-1074) ltac:(lia)) as (p & -> & Fp & Sp & Rp).
  cbv beta iota zeta.
  eexists. split; [reflexivity|].
  apply (mul_exact neg v 0 (-1074) p); try assumption.
  rewrite F2R_0. apply bpow_gt_0.
- assert (Hk1 : (0 < kept)%Z) by lia.
  rewrite leading_zeros_pos by exact Hk1.
  pose proof (Z.log2_spec kept Hk1) as Hlog.
  rewrite <- Z.add_1_r in Hlog.
  pose proof (Z.log2_nonneg kept) as Hlog0.
  assert (Hlog54 : (Z.log2 kept < 54)%Z) by (apply Z.log2_lt_pow2; lia).
  set (lg := Z.log2 kept) in *. clearbody lg.
  replace (64 - (64 - 1 - lg))%Z with (lg + 1)%Z by ring.
  rewrite (checked_i_ok 32 (lg + 1)) by lia. cbv beta iota.
  replace (kept =? 0)%Z with false by lia. cbn [negb]. cbv beta iota.
  rewrite (checked_i_ok 32 (lsb + (lg + 1))) by lia. cbv beta iota.
  assert (HF0 : 0 <= F2R (Float radix2 kept lsb)) by (apply F2R_ge_0; cbn [Fnum]; lia).
  destruct (Z.ltb_spec 1024 (lsb + (lg + 1))) as [Ho|Ho]; cbv beta iota.
  + (* Overflow: [kept * 2^lsb >= 2^(lg + lsb) >= 2^1024]. *)
    eexists. split; [reflexivity|].
    unfold rounds_up_to.
    rewrite HRU, abs_cond_Ropp, Rabs_pos_eq by exact HF0.
    rewrite Rlt_bool_false.
    2: { apply Rle_trans with (bpow radix2 (lg + lsb)).
         - apply bpow_le. lia.
         - apply bpow_plus_le_F2R; lia. }
    rewrite Hneg. apply B2SF_overflow.
  + (* No overflow: [kept * 2^lsb < 2^(lg + 1 + lsb) <= 2^1024]. *)
    destruct (pow2_correct lsb ltac:(lia)) as (p & -> & Fp & Sp & Rp).
    cbv beta iota zeta.
    eexists. split; [reflexivity|].
    apply (mul_exact neg v kept lsb p); try assumption.
    apply Rlt_le_trans with (bpow radix2 (lg + 1 + lsb)).
    * apply F2R_lt_bpow_plus; lia.
    * apply bpow_le. lia.
Qed.

(** ** The theorem *)

Theorem round_up_exact_correct :
  forall neg m e sticky v,
  round_up_exact_pre neg m e sticky v ->
  exists r, Generic.round_up_exact neg m e sticky = Some r /\ rounds_up_to v r.
Proof.
intros neg m e sticky v (Hm & He & Hst & Hneg & Hloc).
(* [top = log2 m], so [2^top <= m < 2^(top + 1)] and [0 <= top < 128]. *)
pose proof (Z.log2_spec m (proj1 Hm)) as Htop.
rewrite <- Z.add_1_r in Htop.
pose proof (Z.log2_nonneg m) as Htop0.
assert (Htop1 : (Z.log2 m < 128)%Z) by (apply Z.log2_lt_pow2; lia).
(* With [sticky], [m >= 2^52], so [top >= 52]. *)
assert (Hst52 : sticky = true -> (52 <= Z.log2 m)%Z).
{ intros Hs. apply Z.log2_le_pow2; [lia | now apply Hst]. }
unfold Generic.round_up_exact.
rewrite leading_zeros_pos by lia.
replace (127 - (128 - 1 - Z.log2 m))%Z with (Z.log2 m) by ring.
set (top := Z.log2 m) in *. clearbody top.
rewrite (checked_i_ok 32 top) by lia. cbv beta iota.
rewrite (checked_i_ok 32 (e + top)) by lia. cbv beta iota.
rewrite (checked_i_ok 32 (e + top - 52)) by lia. cbv beta iota zeta.
remember (Z.max (e + top - 52) (-1074)) as lsb eqn:Hlsb.
rewrite (checked_i_ok 32 (lsb - e)) by lia. cbv beta iota.
remember (lsb - e)%Z as shift eqn:Hshift.
(* [b = |v| * 2^-e] is [m + δ]. *)
destruct (scale_bounds m e sticky (Rabs v) Hloc) as (Hb & Hbm).
set (b := Rabs v * bpow radix2 (- e)) in *.
assert (Hvb : Rabs v = b * bpow radix2 e).
{ unfold b. rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l.
  change (bpow radix2 0) with 1. ring. }
clearbody b.
(* [2^(e + top) <= |v| < 2^(e + top + 1)]. *)
assert (Hv : bpow radix2 (e + top) <= Rabs v < bpow radix2 (e + top + 1)).
{ replace (e + top)%Z with (top + e)%Z by ring.
  replace (top + e + 1)%Z with (top + 1 + e)%Z by ring.
  rewrite Hvb, (bpow_plus radix2 top e), (bpow_plus radix2 (top + 1) e).
  rewrite <- (IZR_pow2 top), <- (IZR_pow2 (top + 1)) by lia.
  pose proof (bpow_gt_0 radix2 e).
  assert (IZR (2^top) <= IZR m) by (apply IZR_le; lia).
  assert (IZR m + 1 <= IZR (2^(top + 1))) by (rewrite <- plus_IZR; apply IZR_le; lia).
  split; [apply Rmult_le_compat_r | apply Rmult_lt_compat_r]; lra. }
(* So the last bit of [RU v] has the weight [2^lsb]. *)
assert (Hc : cexp radix2 fexp64 (Rabs v) = lsb).
{ rewrite Hlsb. exact (cexp_lsb _ _ Hv). }
(* The scaled mantissa [q = |v| * 2^-lsb] is [b * 2^-shift]. *)
assert (Hq : Rabs v * bpow radix2 (- lsb) = b * bpow radix2 (- shift)).
{ rewrite Hvb, Rmult_assoc, <- bpow_plus. do 2 f_equal. lia. }
destruct (split_correct m shift sticky b) as (k & lost & Hsplit & Hk & Hlost).
{ exact Hm. }
{ lia. }
{ (* [shift >= top - 52], so [m * 2^-shift < 2^(top + 1) * 2^(52 - top)]. *)
  intros Hs0.
  assert (Hp : (0 < 2^(- shift) <= 2^(52 - top))%Z).
  { split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia. }
  assert (Hp53 : (2^(top + 1) * 2^(52 - top) = 2^53)%Z).
  { rewrite <- Z.pow_add_r by lia. f_equal. ring. }
  split; [lia | nia]. }
{ intros Hs. specialize (Hst52 Hs). lia. }
{ exact Hb. }
{ exact Hbm. }
rewrite Hsplit. cbv beta iota.
rewrite <- Hq in Hk, Hlost.
(* [0 < q < 2^(e + top + 1 - lsb) <= 2^53], so [0 <= k < 2^53]. *)
assert (Hq0 : 0 < Rabs v * bpow radix2 (- lsb)).
{ apply Rmult_lt_0_compat; [|apply bpow_gt_0].
  pose proof (bpow_gt_0 radix2 (e + top)). lra. }
assert (Hq53 : Rabs v * bpow radix2 (- lsb) < bpow radix2 53).
{ apply Rlt_le_trans with (bpow radix2 (e + top + 1) * bpow radix2 (- lsb)).
  - apply Rmult_lt_compat_r; [apply bpow_gt_0 | apply Hv].
  - rewrite <- bpow_plus. apply bpow_le. lia. }
assert (Hk0 : (0 <= k)%Z).
{ assert (H : 0 < IZR (k + 1)) by (rewrite plus_IZR; lra).
  apply lt_IZR in H. lia. }
assert (Hk53 : (k < 2^53)%Z).
{ assert (H : IZR k < IZR (2^53)) by (rewrite IZR_pow2 by lia; lra).
  apply lt_IZR in H. exact H. }
(* [k = 0] needs [|v| < 2^lsb], i.e. [e + top < lsb], so [lsb = -1074]. *)
assert (Hkz : k = 0%Z -> lsb = (-1074)%Z).
{ intros ->.
  assert (Hlo : bpow radix2 (e + top + - lsb) <= Rabs v * bpow radix2 (- lsb)).
  { rewrite bpow_plus. apply Rmult_le_compat_r; [apply bpow_ge_0 | apply Hv]. }
  assert (H1 : bpow radix2 (e + top + - lsb) < bpow radix2 0).
  { change (bpow radix2 0) with 1. lra. }
  apply lt_bpow in H1. lia. }
assert (HRU := RU_split v lsb k lost Hc Hk Hlost).
rewrite Hneg in HRU.
(* The [+ 1] does not overflow. *)
replace (if lost && negb neg then checked_u 128 (k + 1) else Some k)
  with (Some (if lost && negb neg then k + 1 else k)%Z).
2: { destruct (lost && negb neg); [|reflexivity].
     symmetry. apply checked_u_ok. lia. }
cbv beta iota.
apply (tail_correct neg v lsb).
- destruct (lost && negb neg); lia.
- lia.
- destruct (lost && negb neg); [lia | exact Hkz].
- exact Hneg.
- exact HRU.
Qed.
