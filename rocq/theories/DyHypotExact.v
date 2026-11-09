(** * The exact branch of [hypot] in the dyadic kernel

    For [2^63 <= M, m < 2^64] and a gap [0 <= g <= 26], the branch of
    [DyadicRoot.hypot_odd] below the cut computes [S = (M 2^g)^2 + m^2]
    exactly in 4 limbs ([S < 2^181]), shifts it by an even [2 h] so that
    [X = S 2^(2 h)] has [2^255 <= X < 2^257] (5 limbs), takes
    [s = floor(sqrt X)] ([isqrt_correct] of [DyIsqrt.v] at [n = 2]) and
    whether [s^2 < X], and passes them to [DyadicRoot.odd]
    ([hypot_exact_branch]). [DyHypotOdd.v] uses it. *)

From Stdlib Require Import ZArith Lia List.
From Inari Require Import Model Limbs Knuth DyRound DyIsqrt.

Open Scope Z_scope.

(** The [else] branch of [DyadicRoot.hypot_odd], with [Dyadic.dy_m a]
    and [Dyadic.dy_m b] the one-limb lists [M :: nil] and [m :: nil], and
    [Dyadic.dy_exp b] the integer [eb]. *)
Lemma hypot_exact_branch :
  forall M m eb g,
  2 ^ 63 <= M < 2 ^ 64 -> 2 ^ 63 <= m < 2 ^ 64 -> 0 <= g <= 26 ->
  exists s h b,
  (let wide := Limbs.shl_into 2 (M :: nil) (g mod 2 ^ 64) in
   let* sum := Limbs.mul_into 4 wide wide in
   let mb := Limbs.limb (m :: nil) 0 in
   let mm := mb * mb in
   let sum := fst (Limbs.add_assign sum (mm mod 2 ^ 64 :: mm / 2 ^ 64 :: nil)) in
   let* t := checked_u 64 (257 - Limbs.bit_len sum) in
   let h := t / 2 in
   let xx := Limbs.shl_into 5 sum (2 * h) in
   let* s := Dyadic.isqrt 2 xx in
   let* sq := Limbs.mul_into 6 s s in
   DyadicRoot.odd 3 false s (eb - h) (match Limbs.cmp sq xx with Eq => false | _ => true end))
  = DyadicRoot.odd 3 false s (eb - h) b /\
  limbs_ok s /\ 2 ^ 127 <= Limbs.val s < 2 ^ 129 /\ 0 <= h <= 65 /\
  Limbs.val s * Limbs.val s <= (M * M * 2 ^ (2 * g) + m * m) * 2 ^ (2 * h)
    < (Limbs.val s + 1) * (Limbs.val s + 1) /\
  (b = false <-> Limbs.val s * Limbs.val s = (M * M * 2 ^ (2 * g) + m * m) * 2 ^ (2 * h)).
Proof.
  intros M m eb g HM Hm Hg.
  cbv zeta.
  rewrite (Z.mod_small g (2 ^ 64)) by lia.
  change (Limbs.limb (m :: nil) 0) with m.
  assert (Hpg : 0 < 2 ^ g) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpg26 : 2 ^ g <= 2 ^ 26) by (apply Z.pow_le_mono_r; lia).
  assert (HW : 2 ^ 63 <= M * 2 ^ g < 2 ^ 90) by nia.
  (* [wide = M 2^g < 2^90] fits in its 2 limbs. *)
  assert (HMl : limbs_ok (M :: nil)) by (apply limbs_ok_cons; split; [lia | constructor]).
  destruct (shl_into_correct 2 (M :: nil) g HMl ltac:(lia)) as (Hw & Hwl & Hwv).
  revert Hw Hwl Hwv. generalize (Limbs.shl_into 2 (M :: nil) g) as wide.
  intros wide Hw Hwl Hwv.
  assert (Hwv' : Limbs.val wide = M * 2 ^ g).
  { rewrite Hwv. cbn [Limbs.val]. rewrite Z.mul_0_r, Z.add_0_r.
    change (64 * Z.of_nat 2) with 128. apply Z.mod_small. lia. }
  clear Hwv.
  (* [sum0 = wide^2 < 2^180] in 4 limbs. *)
  destruct (mul_into_correct wide wide Hw Hw) as (sum0 & Es & Hs & Hsl & Hsv).
  rewrite Hwl in Es. change (2 + 2)%nat with 4%nat in Es. rewrite Es. cbv beta iota.
  rewrite Hwv' in Hsv.
  (* [m^2 < 2^128] in 2 limbs. *)
  assert (Hmm : limbs_ok (m * m mod 2 ^ 64 :: m * m / 2 ^ 64 :: nil)).
  { apply limbs_ok_cons; split; [apply Z.mod_pos_bound; lia |].
    apply limbs_ok_cons; split; [| constructor].
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; nia]. }
  assert (Hmmv : Limbs.val (m * m mod 2 ^ 64 :: m * m / 2 ^ 64 :: nil) = m * m).
  { cbn [Limbs.val]. pose proof (Z.div_mod (m * m) (2 ^ 64) ltac:(lia)). lia. }
  (* [S = sum0 + m^2 < 2^181 < 2^256]: [add_assign] has no carry. *)
  rewrite Hwl in Hsl. change (2 + 2)%nat with 4%nat in Hsl.
  assert (Hml : Peano.le (length (m * m mod 2 ^ 64 :: m * m / 2 ^ 64 :: nil)) (length sum0))
    by (rewrite Hsl; cbn [length]; lia).
  destruct (Limbs.add_assign sum0 (m * m mod 2 ^ 64 :: m * m / 2 ^ 64 :: nil))
    as [sm c] eqn:EA.
  destruct (add_assign_correct _ _ _ _ Hs Hmm Hml EA) as (Hsm & Hsml & Hsmv).
  cbn [fst].
  rewrite Hsl, Hmmv, Hsv in Hsmv. change (64 * Z.of_nat 4) with 256 in Hsmv.
  pose proof (val_bounds sm Hsm) as Hsmb.
  assert (HWW : 2 ^ 126 <= M * 2 ^ g * (M * 2 ^ g) < 2 ^ 180) by nia.
  assert (Hm2 : 0 <= m * m < 2 ^ 128) by nia.
  assert (HSv : Limbs.val sm = M * 2 ^ g * (M * 2 ^ g) + m * m).
  { destruct c; cbn [Z.b2z] in Hsmv; lia. }
  clear Hsmv Hsmb EA Hml.
  (* [L = bit_len S = k + 1] with [2^k <= S < 2^(k + 1)] and [126 <= k <= 180]. *)
  assert (HV : 2 ^ 126 <= Limbs.val sm < 2 ^ 181) by lia.
  assert (HV0 : 0 < Limbs.val sm) by lia.
  assert (Hk : nat_bits (Limbs.val sm) = Z.log2 (Limbs.val sm) + 1).
  { unfold nat_bits. destruct (Z.eqb_spec (Limbs.val sm) 0); lia. }
  rewrite (bit_len_correct sm Hsm), Hk.
  pose proof (Z.log2_spec (Limbs.val sm) HV0) as [Hk1 Hk2]. unfold Z.succ in Hk2.
  pose proof (proj1 (Z.log2_le_pow2 _ 126 HV0) (proj1 HV)) as L1.
  pose proof (proj1 (Z.log2_lt_pow2 _ 181 HV0) (proj2 HV)) as L2.
  set (k := Z.log2 (Limbs.val sm)) in *. clearbody k.
  (* [t = 257 - L] fits in a [u64], and [h = t / 2] has [k + 2 h] in
     [{255, 256}]. *)
  rewrite (checked_u_ok 64 (257 - (k + 1))) by lia. cbv beta iota.
  assert (Hh : 38 <= (257 - (k + 1)) / 2 <= 65 /\
               (k + 2 * ((257 - (k + 1)) / 2) = 255 \/ k + 2 * ((257 - (k + 1)) / 2) = 256)).
  { pose proof (Z.div_mod (257 - (k + 1)) 2 ltac:(lia)).
    pose proof (Z.mod_pos_bound (257 - (k + 1)) 2 ltac:(lia)). lia. }
  revert Hh. generalize ((257 - (k + 1)) / 2) as h. intros h Hh.
  (* [xx = S 2^(2 h)] has [2^255 <= xx < 2^257] in its 5 limbs. *)
  destruct (shl_into_correct 5 sm (2 * h) Hsm ltac:(lia)) as (Hx & Hxl & Hxv).
  revert Hx Hxl Hxv. generalize (Limbs.shl_into 5 sm (2 * h)) as xx.
  intros xx Hx Hxl Hxv.
  change (64 * Z.of_nat 5) with 320 in Hxv.
  assert (Hp2h : 0 < 2 ^ (2 * h)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hkh : 2 ^ (k + 2 * h) = 2 ^ k * 2 ^ (2 * h))
    by (apply Z.pow_add_r; lia).
  assert (Hkh1 : 2 ^ (k + 1 + 2 * h) = 2 ^ (k + 1) * 2 ^ (2 * h))
    by (apply Z.pow_add_r; lia).
  assert (Hlo : 2 ^ 255 <= 2 ^ (k + 2 * h)) by (apply Z.pow_le_mono_r; lia).
  assert (Hhi : 2 ^ (k + 1 + 2 * h) <= 2 ^ 257) by (apply Z.pow_le_mono_r; lia).
  assert (HX : 2 ^ 255 <= Limbs.val sm * 2 ^ (2 * h) < 2 ^ 257).
  { split.
    - apply Z.le_trans with (2 ^ k * 2 ^ (2 * h)); [lia |].
      apply Z.mul_le_mono_nonneg_r; lia.
    - apply Z.lt_le_trans with (2 ^ (k + 1) * 2 ^ (2 * h)); [| lia].
      apply Z.mul_lt_mono_pos_r; lia. }
  rewrite Z.mod_small in Hxv by lia.
  assert (E2g : 2 ^ (2 * g) = 2 ^ g * 2 ^ g)
    by (replace (2 * g) with (g + g) by lia; apply Z.pow_add_r; lia).
  assert (HXv : Limbs.val xx = (M * M * 2 ^ (2 * g) + m * m) * 2 ^ (2 * h)).
  { rewrite Hxv, HSv, E2g. ring. }
  clear HSv E2g Hkh Hkh1 Hlo Hhi.
  (* [s = floor(sqrt xx)] in 3 limbs, by [isqrt_correct] at [n = 2]. *)
  assert (Hlev : level_ok 2) by (unfold level_ok; lia).
  assert (HXb : 2 ^ (128 * Z.of_nat 2 - 1) <= Limbs.val xx < 2 ^ (128 * Z.of_nat 2 + 1)).
  { change (128 * Z.of_nat 2 - 1) with 255. change (128 * Z.of_nat 2 + 1) with 257. lia. }
  destruct (isqrt_correct 2 xx Hlev Hx Hxl HXb) as (s & Ei & Hr & Hrl & Hrv).
  rewrite Ei. cbv beta iota.
  (* [sq = s^2] in 6 limbs, and [cmp] compares it with [xx]. *)
  destruct (mul_into_correct s s Hr Hr) as (sq & Em & Hq & Hql & Hqv).
  rewrite Hrl in Em. change (3 + 3)%nat with 6%nat in Em. rewrite Em. cbv beta iota.
  rewrite (Inari.Limbs.cmp_correct sq xx Hq Hx), Hqv.
  exists s, h,
    (match Z.compare (Limbs.val s * Limbs.val s) (Limbs.val xx) with Eq => false | _ => true end).
  split; [reflexivity |].
  rewrite <- HXv.
  pose proof (Z.sqrt_spec (Limbs.val xx) ltac:(lia)) as Hsp. cbv zeta in Hsp.
  rewrite <- Hrv in Hsp. unfold Z.succ in Hsp.
  pose proof (val_bounds s Hr) as Hrb.
  change (2 ^ (128 * Z.of_nat 2 - 1)) with (2 ^ 255) in HXb.
  change (2 ^ (128 * Z.of_nat 2 + 1)) with (2 ^ 257) in HXb.
  split; [exact Hr |].
  split; [split; nia |].
  split; [lia |].
  split; [exact Hsp |].
  destruct (Z.compare_spec (Limbs.val s * Limbs.val s) (Limbs.val xx)) as [E | E | E];
    split; intros H; first [reflexivity | discriminate | lia | exfalso; lia].
Qed.
