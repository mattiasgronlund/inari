(** * Conversions between [f64] and the dyadic kernel

    [Dyadic.from_f64] is exact, and [Dyadic.to_f64] rounds a dyadic number
    to an [f64] as [mpfr_round] says, with overflow to the infinities. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Spec Encoding Decompose RoundUpExact ParseScale
  ParseRound DyRound.

Open Scope Z_scope.

(** ** [from_f64] *)

(** [Dyadic.round] of [(-1)^s m 2^e], for an [f64] with [m < 2^53] and
    [e] in the exponent range of [f64], is exact, as [m] fits in [64 n]
    bits, and its exponent is within [64 n + 54] of [e]. *)
Lemma from_f64_round :
  forall n s m e (x : f64),
  level_ok n -> 0 <= m < 2 ^ 53 -> -1074 <= e <= 971 ->
  B2R x = cond_Ropp s (IZR m * bpow radix2 e)%R ->
  exists d,
  Dyadic.round n s (m :: nil) e false false = Some d /\ dy_ok n d /\ exp_small d /\
  Dyadic.dy_R d = B2R x.
Proof.
intros n s m e x Hn Hm He Hx.
pose proof (dprec_bounds n Hn) as Hp.
assert (Hok : limbs_ok (m :: nil)).
{ apply limbs_ok_cons. split; [lia | constructor]. }
assert (Hv : Limbs.val (m :: nil) = m) by (cbn [Limbs.val]; ring).
assert (Hbits : 0 <= nat_bits m <= 53).
{ unfold nat_bits. destruct (Z.eqb_spec m 0) as [H0 | H0]; [lia |].
  pose proof (Z.log2_nonneg m).
  assert (Z.log2 m < 53) by (apply Z.log2_lt_pow2; lia). lia. }
destruct (round_correct n s (m :: nil) e false false 0%R Hn Hok eq_refl)
  as (d & Hd & Hdok & HdR).
{ right. rewrite Hv. lia. }
assert (HR : Dyadic.dy_R d = B2R x).
{ rewrite HdR, Hv, Rplus_0_r, Hx. apply dround_id; [exact Hn |].
  unfold cond_Ropp. apply format_int; [exact Hn |].
  rewrite Z.abs_eq by lia.
  apply Z.lt_le_trans with (2 ^ 53); [lia | apply Z.pow_le_mono_r; lia]. }
exists d. split; [exact Hd |]. split; [exact Hdok |]. split; [| exact HR].
unfold exp_small.
destruct (dy_cases n d Hn Hdok) as [(_ & _ & _ & He0 & _) | (_ & _ & Hb1 & Hb2)];
  [lia |].
rewrite HR, Hx, abs_cond_Ropp in Hb1, Hb2.
assert (H0 : (0 <= IZR m * bpow radix2 e)%R).
{ apply Rmult_le_pos; [apply IZR_le; lia | apply bpow_ge_0]. }
rewrite Rabs_pos_eq in Hb1, Hb2 by exact H0.
(* [2^e <= m 2^e < 2^(e + 53)], as [m] is not 0. *)
assert (Hm1 : 1 <= m).
{ destruct (Z.eq_dec m 0) as [E | E]; [| lia].
  rewrite E, Rmult_0_l in Hb1.
  pose proof (bpow_gt_0 radix2 (Dyadic.dy_exp d + dprec n - 1)). lra. }
assert (Hlo : (bpow radix2 e <= IZR m * bpow radix2 e)%R).
{ rewrite <- (Rmult_1_l (bpow radix2 e)) at 1.
  apply Rmult_le_compat_r; [apply bpow_ge_0 | apply IZR_le; lia]. }
assert (Hhi : (IZR m * bpow radix2 e < bpow radix2 (53 + e))%R).
{ rewrite bpow_plus, <- (IZR_pow2 53) by lia.
  apply Rmult_lt_compat_r; [apply bpow_gt_0 | apply IZR_lt; lia]. }
assert (H1 : Dyadic.dy_exp d + dprec n - 1 < 53 + e).
{ apply (lt_bpow radix2). lra. }
assert (H2 : e < Dyadic.dy_exp d + dprec n).
{ apply (lt_bpow radix2). lra. }
lia.
Qed.

(** The [Dyadic] that [from_f64] builds from [(-1)^s m 2^e], for an [f64]
    with [m < 2^53] and [e] in the exponent range of [f64]: [m] shifted up to
    the top bit of the top limb, or the zero of [n] limbs for [m = 0], which
    is exact. *)
Lemma from_f64_top :
  forall n s m e (x : f64),
  level_ok n -> 0 <= m < 2 ^ 53 -> -1074 <= e <= 971 ->
  B2R x = cond_Ropp s (IZR m * bpow radix2 e)%R ->
  exists d,
  (if m =? 0 then Some (Dyadic.dy_zero n) else
   let lz := leading_zeros 64 m in
   let* top := shl 64 m lz in
   Some {| Dyadic.dy_neg := s; Dyadic.dy_exp := e - lz - 64 * (Z.of_nat n - 1);
           Dyadic.dy_m := Limbs.update (repeat 0 n) (n - 1) (top :: nil) |}) = Some d /\
  dy_ok n d /\ exp_small d /\ Dyadic.dy_R d = B2R x.
Proof.
intros n s m e x Hn Hm He Hx.
assert (Hn' : (1 <= n <= 64)%nat) by exact Hn.
destruct (Z.eqb_spec m 0) as [Hm0 | Hm0].
- (* [m = 0]: the zero of [n] limbs. *)
  destruct (dy_zero_ok n) as (Hok & HR & Hs).
  exists (Dyadic.dy_zero n). split; [reflexivity |]. split; [exact Hok |].
  split; [exact Hs |].
  rewrite HR, Hx, Hm0. destruct s; cbn [cond_Ropp]; ring.
- (* [lz = 63 - log2 m] is at least [11], as [m < 2^53]. *)
  assert (Hm1 : 0 < m) by lia.
  pose proof (Z.log2_spec m Hm1) as HL.
  assert (HL53 : Z.log2 m < 53) by (apply Z.log2_lt_pow2; lia).
  pose proof (Z.log2_nonneg m) as HL0.
  assert (Hlz : leading_zeros 64 m = 63 - Z.log2 m).
  { unfold leading_zeros. destruct (Z.eqb_spec m 0); lia. }
  (* [m 2^lz] has its top bit at bit [63], as in [Knuth.v]'s [dt 2^s]. *)
  assert (HT : 2 ^ 63 <= m * 2 ^ (63 - Z.log2 m) < 2 ^ 64).
  { assert (E1 : 2 ^ Z.log2 m * 2 ^ (63 - Z.log2 m) = 2 ^ 63)
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (E2 : 2 ^ Z.succ (Z.log2 m) * 2 ^ (63 - Z.log2 m) = 2 ^ 64)
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (0 < 2 ^ (63 - Z.log2 m)) by (apply Z.pow_pos_nonneg; lia).
    split; nia. }
  (* So the shift loses no bit. *)
  assert (Hshl : shl 64 m (63 - Z.log2 m) = Some (m * 2 ^ (63 - Z.log2 m))).
  { unfold shl.
    replace ((0 <=? 63 - Z.log2 m) && (63 - Z.log2 m <? 64)) with true
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia. reflexivity. }
  destruct (ex_intro (fun t => t = m * 2 ^ (63 - Z.log2 m)) _ eq_refl) as (t & Ht).
  rewrite <- Ht in HT, Hshl.
  (* The mantissa is [n - 1] zero limbs and then [t]. *)
  assert (Hu : Limbs.update (repeat 0 n) (n - 1) (t :: nil) = repeat 0 (n - 1) ++ t :: nil).
  { destruct n as [| k]; [lia |].
    replace (S k - 1)%nat with k by lia.
    unfold Limbs.update. cbn [length repeat]. rewrite repeat_cons.
    rewrite firstn_app, repeat_length, Nat.sub_diag. cbn [firstn].
    rewrite firstn_all2, app_nil_r by (rewrite repeat_length; lia).
    rewrite skipn_all2 by (rewrite length_app, repeat_length; cbn [length]; lia).
    reflexivity. }
  assert (Hval : Limbs.val (repeat 0 (n - 1) ++ t :: nil) = 2 ^ (64 * Z.of_nat (n - 1)) * t).
  { rewrite val_app, val_repeat0, repeat_length. cbn [Limbs.val]. ring. }
  assert (Hn1 : Z.of_nat (n - 1) = Z.of_nat n - 1) by lia.
  exists {| Dyadic.dy_neg := s; Dyadic.dy_exp := e - (63 - Z.log2 m) - 64 * (Z.of_nat n - 1);
            Dyadic.dy_m := Limbs.update (repeat 0 n) (n - 1) (t :: nil) |}.
  split; [cbv beta iota zeta; rewrite Hlz, Hshl; reflexivity |].
  unfold dy_ok, exp_small, Dyadic.dy_R. cbn [Dyadic.dy_m Dyadic.dy_exp Dyadic.dy_neg].
  rewrite Hu, Hval.
  split; [split; [| split; [| split]] | split].
  + apply limbs_ok_app; [apply limbs_ok_repeat0 |].
    apply limbs_ok_cons. split; [lia | constructor].
  + rewrite length_app, repeat_length. cbn [length]. lia.
  + lia.
  + (* [2^(64 n - 1) = 2^(64 (n - 1)) 2^63 <= 2^(64 (n - 1)) t]. *)
    right. unfold dprec.
    replace (64 * Z.of_nat n - 1) with (64 * Z.of_nat (n - 1) + 63) by lia.
    rewrite Z.pow_add_r by lia.
    apply Z.mul_le_mono_nonneg_l; [apply Z.pow_nonneg; lia | lia].
  + lia.
  + (* [2^(64 (n - 1)) m 2^lz 2^(e - lz - 64 (n - 1)) = m 2^e]. *)
    rewrite Hx, Ht, !mult_IZR, !IZR_pow2 by lia.
    replace (bpow radix2 e) with
      (bpow radix2 (64 * Z.of_nat (n - 1)) * bpow radix2 (63 - Z.log2 m) *
       bpow radix2 (e - (63 - Z.log2 m) - 64 * (Z.of_nat n - 1)))%R
      by (rewrite <- !bpow_plus; f_equal; lia).
    destruct s; cbn [cond_Ropp]; ring.
Qed.

(** [from_f64] reads the fields of the bits of [x] as
    [Generic.decompose] does ([Decompose.decompose_correct]), and the
    zeros too, as [m = 0]. *)
Lemma from_f64_correct :
  forall n x,
  level_ok n -> is_finite x = true ->
  exists d,
  Dyadic.from_f64 n x = Some d /\ dy_ok n d /\ exp_small d /\ Dyadic.dy_R d = B2R x.
Proof.
intros n x Hn Fx.
destruct (to_bits_finite x Fx) as (c & Hc & Hb).
destruct (from_bits_finite (Bsign x) c Hc) as (_ & _ & Hx).
rewrite <- Hb, from_to_bits in Hx.
unfold magnitude in Hx.
unfold Dyadic.from_f64. rewrite Fx. cbn [negb]. cbv zeta.
rewrite Hb, biased_finite, frac_finite, sign_finite by exact Hc.
destruct (Z.eqb_spec (c / 2^52) 0) as [HE0 | HE0]; cbv beta iota.
- (* A zero or a subnormal: no implicit bit, and the exponent [-1074]. *)
  replace (mant c) with (c mod 2^52) in Hx by (unfold mant; now rewrite HE0).
  replace (expo c) with (-1074) in Hx by (unfold expo; now rewrite HE0).
  apply from_f64_top; [exact Hn | zlia | lia |].
  rewrite Hx. unfold F2R; cbn [Fnum Fexp]. destruct (Bsign x); reflexivity.
- (* A normal float: the implicit bit is set. *)
  rewrite lor_implicit by zlia.
  replace (mant c) with (c mod 2^52 + 2^52) in Hx
    by (unfold mant; now rewrite (proj2 (Z.eqb_neq _ _) HE0)).
  replace (expo c) with (c / 2^52 - 1075) in Hx by (unfold expo; zlia).
  apply from_f64_top; [exact Hn | zlia | zlia |].
  rewrite Hx. unfold F2R; cbn [Fnum Fexp]. destruct (Bsign x); reflexivity.
Qed.

(** ** [to_f64] *)

Lemma checked_i128 : forall z, - 2 ^ 127 <= z < 2 ^ 127 -> checked_i 128 z = Some z.
Proof. intros z Hz. apply checked_i_ok. exact Hz. Qed.

(** The [q] and [sticky] that [round_up] passes to [round_up_exact] with
    the exponent [E + p - 128], for a mantissa [M] of [p = 64 n] bits: [q]
    is the top two limbs, [M / 2^(p - 128)], for [n >= 2], and [M 2^64]
    for [n = 1]; [sticky] says whether a limb below them is nonzero. So
    [q 2^(E + p - 128)] is [M 2^E] if not [sticky], and is below [M 2^E]
    by less than [2^(E + p - 128)] if [sticky]. *)
Lemma round_up_window :
  forall n m E,
  level_ok n -> limbs_ok m -> length m = n -> 2 ^ (dprec n - 1) <= Limbs.val m ->
  let lo := if (2 <=? n)%nat then Limbs.limb m (n - 2) else 0 in
  let q := Z.lor (Z.shiftl (Limbs.limb m (n - 1)) 64 mod 2 ^ 128) lo in
  let sticky := existsb (fun l => negb (l =? 0)) (firstn (n - 2) m) in
  2 ^ 127 <= q < 2 ^ 128 /\
  if sticky then
    (F2R (Float radix2 q (E + dprec n - 128)) < IZR (Limbs.val m) * bpow radix2 E <
     F2R (Float radix2 (q + 1) (E + dprec n - 128)))%R
  else (IZR (Limbs.val m) * bpow radix2 E = F2R (Float radix2 q (E + dprec n - 128)))%R.
Proof.
intros n m E Hn Hm Hl HM lo q sticky.
pose proof (val_bounds _ Hm) as Hb. rewrite Hl in Hb. fold (dprec n) in Hb.
pose proof (bpow_gt_0 radix2 E) as HE.
assert (Hw : (n = 1%nat /\ q = Limbs.val m * 2 ^ 64 /\ sticky = false) \/
             ((2 <= n)%nat /\ q = Limbs.val m / 2 ^ (dprec n - 128) /\
              (sticky = true <-> Limbs.val m mod 2 ^ (dprec n - 128) <> 0))).
{ destruct n as [| [| k]]; [unfold level_ok in Hn; lia | left | right].
  - (* One limb [a]: [q = a 2^64], and [firstn 0] is empty. *)
    destruct m as [| a [| b m]]; cbn [length] in Hl; try discriminate Hl.
    apply limbs_ok_cons in Hm. destruct Hm as [Ha _].
    split; [reflexivity |]. split; [| reflexivity].
    unfold q, lo. change (Limbs.limb (a :: nil) (1 - 1)) with a.
    change ((2 <=? 1)%nat) with false. cbv beta iota.
    rewrite Z.lor_0_r, Z.shiftl_mul_pow2 by lia.
    rewrite Z.mod_small by lia.
    cbn [Limbs.val]. ring.
  - (* [k + 2] limbs: [Y = M / 2^(64 k)] has 128 bits, its high limb is
       [limb m (k + 1)] and its low limb [limb m k]. *)
    assert (Hd : dprec (S (S k)) - 128 = 64 * Z.of_nat k) by (unfold dprec; lia).
    rewrite Hd. split; [lia |].
    pose proof (pow64_pos k) as HK.
    split.
    + unfold q, lo.
      replace (S (S k) - 1)%nat with (S k) by lia.
      replace (S (S k) - 2)%nat with k by lia.
      replace ((2 <=? S (S k))%nat) with true by reflexivity.
      rewrite !limb_val by exact Hm.
      rewrite pow64_S, (Z.mul_comm (2 ^ 64)), <- Z.div_div by lia.
      remember (Limbs.val m / 2 ^ (64 * Z.of_nat k)) as Y eqn:HY.
      assert (HY1 : 0 <= Y < 2 ^ 128).
      { subst Y. split; [apply Z.div_pos; lia |].
        apply Z.div_lt_upper_bound; [lia |].
        unfold dprec in Hb. rewrite !pow64_S in Hb. lia. }
      assert (H64 : 0 < 2 ^ 64) by lia.
      pose proof (Z.div_mod Y (2 ^ 64)) as HdY.
      pose proof (Z.mod_pos_bound Y (2 ^ 64) H64) as HmY.
      assert (Hh : 0 <= Y / 2 ^ 64 < 2 ^ 64).
      { split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
      rewrite (Z.mod_small (Y / 2 ^ 64) (2 ^ 64)) by lia.
      rewrite Z.shiftl_mul_pow2 by lia.
      rewrite (Z.mod_small (Y / 2 ^ 64 * 2 ^ 64) (2 ^ 128)) by lia.
      rewrite lor_low by lia.
      lia.
    + unfold sticky.
      replace (S (S k) - 2)%nat with k by lia.
      rewrite <- val_firstn by exact Hm.
      apply existsb_nonzero, limbs_ok_firstn, Hm. }
clearbody lo q sticky.
destruct Hw as [(Hn1 & Hq & Hs) | (Hn2 & Hq & Hs)].
- (* [subst n] leaves [length m] where [n] was. *)
  subst n. rewrite Hn1 in HM, Hb |- *. change (dprec 1) with 64 in *.
  assert (H63 : 2 ^ 63 <= Limbs.val m) by exact HM.
  rewrite Hs. split; [lia |]. cbv beta iota.
  rewrite Hq. unfold F2R; cbn [Fnum Fexp].
  rewrite mult_IZR, (IZR_pow2 64) by lia.
  rewrite Rmult_assoc, <- bpow_plus.
  replace (64 + (E + 64 - 128)) with E by ring. reflexivity.
- assert (Hk : 0 <= dprec n - 128) by (unfold level_ok, dprec in *; lia).
  (* [q 2^(E + p - 128)] is [(q K) 2^E] for [K = 2^(p - 128)]. *)
  assert (Hf : forall a, F2R (Float radix2 a (E + dprec n - 128)) =
                         (IZR (a * 2 ^ (dprec n - 128)) * bpow radix2 E)%R).
  { intros a. unfold F2R; cbn [Fnum Fexp].
    rewrite mult_IZR, IZR_pow2 by exact Hk.
    rewrite Rmult_assoc, <- bpow_plus.
    replace (dprec n - 128 + E) with (E + dprec n - 128) by ring. reflexivity. }
  assert (HKp : 2 ^ (dprec n - 1) = 2 ^ (dprec n - 128) * 2 ^ 127 /\
                2 ^ dprec n = 2 ^ (dprec n - 128) * 2 ^ 128).
  { rewrite <- !Z.pow_add_r by lia. split; f_equal; ring. }
  rewrite !Hf.
  remember (2 ^ (dprec n - 128)) as K eqn:HK.
  assert (HK0 : 0 < K) by (subst K; apply Z.pow_pos_nonneg; lia).
  remember (Limbs.val m) as M eqn:HMdef.
  pose proof (Z.div_mod M K) as HdM.
  pose proof (Z.mod_pos_bound M K HK0) as HmM.
  assert (Hq1 : 2 ^ 127 <= q < 2 ^ 128).
  { rewrite Hq. split.
    - apply Z.div_le_lower_bound; lia.
    - apply Z.div_lt_upper_bound; lia. }
  split; [exact Hq1 |].
  destruct sticky.
  + assert (Hr : M mod K <> 0) by (apply Hs; reflexivity).
    split; apply Rmult_lt_compat_r; try exact HE; apply IZR_lt; rewrite Hq; lia.
  + assert (Hr : M mod K = 0).
    { destruct (Z.eq_dec (M mod K) 0) as [E0 | E0]; [exact E0 |].
      apply Hs in E0. discriminate E0. }
    replace (q * K) with M by (rewrite Hq; lia). reflexivity.
Qed.

(** [round_up n x neg] is the nonzero [v] rounded up, for [v] of the sign
    [neg] and of the magnitude of [x]: [b = exp + 64 n] is the exponent of
    the bit above the top of [|v|], so [|v| >= 2^1024] overflows if
    [b >= 1025], [|v| < 2^-1074] is [Tiny] in [round_up_scaled] if
    [b <= -1074], and [round_up_exact] rounds the window of
    [round_up_window] otherwise. *)
Lemma round_up_correct :
  forall n x neg v,
  level_ok n -> dy_ok n x -> Dyadic.is_zero n x = false ->
  Rabs v = Rabs (Dyadic.dy_R x) -> Rlt_bool v 0 = neg ->
  exists r, Dyadic.round_up n x neg = Some r /\ rounds_up_to v r.
Proof.
intros n x neg v Hn Hx Hz Hv Hneg. subst neg.
pose proof (dprec_bounds n Hn) as Hp.
pose proof Hx as (Hm & Hl & He & _).
destruct (dy_cases n x Hn Hx) as [(Hz' & _) | (_ & HM & Hb1 & Hb2)];
  [rewrite Hz' in Hz; discriminate Hz |].
rewrite <- Hv in Hb1, Hb2.
assert (Hv0 : v <> 0%R).
{ intros H0. rewrite H0, Rabs_R0 in Hb1.
  pose proof (bpow_gt_0 radix2 (Dyadic.dy_exp x + dprec n - 1)). lra. }
unfold Dyadic.round_up.
change (64 * Z.of_nat n) with (dprec n).
rewrite (checked_i128 (Dyadic.dy_exp x + dprec n)) by lia.
cbv beta iota.
destruct (Z.leb_spec 1025 (Dyadic.dy_exp x + dprec n)) as [Hh | Hh].
- (* [|v| >= 2^(b - 1) >= 2^1024], so [|RU v| >= 2^1024]: as in
     [round_up_scaled_correct] for [Huge], with [<=]. For [v < 0],
     [-2^1024] is a float at or above [v], so at or above [RU v]. *)
  eexists. split; [reflexivity |]. unfold rounds_up_to.
  destruct (round_UP_pt radix2 fexp64 v) as (_ & Hge & Hmin).
  pose proof (bpow_gt_0 radix2 1024) as Hb.
  assert (Hs : (bpow radix2 1024 <= Rabs v)%R).
  { apply Rle_trans with (2 := Hb1). apply bpow_le. lia. }
  rewrite Rlt_bool_false; [apply B2SF_overflow |].
  destruct (Rdichotomy _ _ Hv0) as [Hn' | Hp'].
  + rewrite Rabs_left in Hs by exact Hn'.
    assert (G : generic_format radix2 fexp64 (- bpow radix2 1024)).
    { apply generic_format_opp, generic_format_bpow. unfold FLT_exp. lia. }
    assert (Hle : (v <= - bpow radix2 1024)%R) by lra.
    pose proof (Hmin _ G Hle).
    rewrite Rabs_left1 by lra. lra.
  + rewrite Rabs_pos_eq in Hs by lra. rewrite Rabs_pos_eq by lra. lra.
- destruct (Z.leb_spec (Dyadic.dy_exp x + dprec n) (-1074)) as [Ht | Ht].
  + (* [0 < |v| < 2^b <= 2^-1074] *)
    assert (Hs : scaled_ok Tiny (Rabs v)).
    { cbn [scaled_ok]. split; [apply Rabs_pos_lt; exact Hv0 |].
      apply Rlt_le_trans with (1 := Hb2). apply bpow_le. exact Ht. }
    destruct (round_up_scaled_correct Tiny v Hv0 Hs) as (r & Hr & Hu).
    cbn [round_up_scaled] in Hr.
    exists r. split; [exact Hr | exact Hu].
  + (* [-1074 < b < 1025]: [b - 128] fits in an [i32]. *)
    rewrite (checked_i128 (Dyadic.dy_exp x + dprec n - 128)) by lia.
    cbv beta iota.
    rewrite (Z.mod_small (Dyadic.dy_exp x + dprec n - 128 + 2 ^ 31) (2 ^ 32)) by lia.
    replace (Dyadic.dy_exp x + dprec n - 128 + 2 ^ 31 - 2 ^ 31)
      with (Dyadic.dy_exp x + dprec n - 128) by ring.
    pose proof (round_up_window n (Dyadic.dy_m x) (Dyadic.dy_exp x) Hn Hm Hl (proj1 HM))
      as Hw.
    cbv zeta in Hw |- *. destruct Hw as (Hq & Hw).
    apply round_up_exact_correct. unfold round_up_exact_pre.
    split; [lia |]. split; [lia |]. split; [intros _; lia |]. split; [reflexivity |].
    rewrite Hv, dy_abs by exact Hm. exact Hw.
Qed.

(** [to_f64] rounds as MPFR rounds to an [f64], with overflow to the
    infinities. *)
Lemma to_f64_correct :
  forall n x up,
  level_ok n -> dy_ok n x ->
  exists v,
  Dyadic.to_f64 n x up = Some v /\
  mpfr_round f64_format (if up then RNDU else RNDD) (Dyadic.dy_R x) (with_val v).
Proof.
intros n x up Hn Hx. unfold Dyadic.to_f64.
destruct (dy_cases n x Hn Hx) as [(Hz & _ & _ & _ & H0) | (Hz & _ & Hb & _)]; rewrite Hz.
- (* 0 rounds to [+0] both ways. *)
  exists zero. split; [reflexivity |]. rewrite H0.
  assert (F0 : f64_format 0%R) by (exists zero; split; reflexivity).
  destruct up; cbn [with_val zero mpfr_round].
  + split; [exact F0 |]. split; [apply Rle_refl |]. intros g _ Hg. exact Hg.
  + split; [exact F0 |]. split; [apply Rle_refl |]. intros g _ Hg. exact Hg.
- (* Rounding down is rounding up the negation, negated
     ([rounds_up_to_opp]). *)
  assert (Hm : limbs_ok (Dyadic.dy_m x)) by exact (proj1 Hx).
  assert (Hv0 : Dyadic.dy_R x <> 0%R).
  { intros E0. rewrite E0, Rabs_R0 in Hb.
    pose proof (bpow_gt_0 radix2 (Dyadic.dy_exp x + dprec n - 1)). lra. }
  assert (Hs : Rlt_bool (Dyadic.dy_R x) 0 = Dyadic.dy_neg x).
  { assert (Ha : (0 < Rabs (Dyadic.dy_R x))%R) by (apply Rabs_pos_lt; exact Hv0).
    rewrite (dy_R_sign x Hm).
    destruct (Dyadic.dy_neg x); [apply Rlt_bool_true | apply Rlt_bool_false]; lra. }
  destruct up.
  + destruct (round_up_correct n x (Dyadic.dy_neg x) (Dyadic.dy_R x) Hn Hx Hz eq_refl Hs)
      as (r & Hr & Hu).
    exists r. split; [exact Hr |].
    apply rounds_up_to_mpfr_round; [exact Hv0 | exact Hu].
  + assert (Hs' : Rlt_bool (- Dyadic.dy_R x) 0 = negb (Dyadic.dy_neg x)).
    { rewrite <- Hs. destruct (Rdichotomy _ _ Hv0) as [Hl | Hl].
      - rewrite (Rlt_bool_true _ _ Hl), Rlt_bool_false by lra. reflexivity.
      - rewrite (Rlt_bool_false (Dyadic.dy_R x) 0), Rlt_bool_true by lra. reflexivity. }
    destruct (round_up_correct n x (negb (Dyadic.dy_neg x)) (- Dyadic.dy_R x) Hn Hx Hz
                (Rabs_Ropp _) Hs') as (r & Hr & Hu).
    exists (opp r). rewrite Hr. split; [reflexivity |].
    apply rounds_up_to_opp; [exact Hv0 | exact Hu].
Qed.
