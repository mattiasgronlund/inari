(** * Rounding to odd in the roots of the dyadic kernel

    [DyadicRoot.odd n neg s e b] is [(-1)^neg (2 s + b) 2^(e - 1)]
    ([odd_correct]). For a real [r] with [s 2^E <= r < (s + 1) 2^E],
    [2^53 <= s], and [b] true exactly when [r] is above [s 2^E], that
    number is [r] rounded to odd at the bits of [s] and one more, and it
    rounds toward -inf and toward +inf ([odd_window_dir]) and to nearest
    ([odd_window_near]) as [r] does, with either sign: no [f64], no
    midpoint of two adjacent [f64]s and not the overflow threshold
    [2^1024 - 2^970] lies strictly between [s 2^E] and [(s + 1) 2^E], as
    each of them above [2^(53 + E)] is a multiple of [2^E]. For nearest
    this is [round_N_odd] of Flocq (S. Boldo and G. Melquiond, Emulation
    of FMA and correctly rounded sums: proved algorithms using rounding to
    odd, IEEE Trans. Computers 57(4), 2008, Theorem 2), with [FLX_exp]
    of [Z.log2 s + 2 >= 55] bits against [FLT_exp (-1074) 53]. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Round_odd.
From Inari Require Import Model Mpfr Limbs DyRound NearF64.

Open Scope Z_scope.

Theorem odd_correct :
  forall n neg s e b,
  level_ok n -> limbs_ok s ->
  2 ^ 53 <= Limbs.val s -> 2 * Limbs.val s + 1 < 2 ^ (64 * Z.of_nat n) ->
  - 2 ^ 62 <= e <= 2 ^ 62 ->
  exists d, DyadicRoot.odd n neg s e b = Some d /\ dy_ok n d /\
  Dyadic.dy_R d = cond_Ropp neg (IZR (2 * Limbs.val s + Z.b2z b) * bpow radix2 (e - 1)).
Proof.
intros n neg s e b Hn Hs Hs53 Hs2 He.
pose proof (dprec_bounds n Hn) as Hp.
pose proof (val_nonneg s Hs) as Hs0.
pose proof (b2z_bounds b) as Hb.
change (64 * Z.of_nat n) with (dprec n) in Hs2.
assert (Hn1 : (1 <= n)%nat) by (unfold level_ok in Hn; lia).
unfold DyadicRoot.odd. cbv zeta.
destruct (shl_into_correct n s 1 Hs ltac:(lia)) as (Wok & Wlen & Wval).
set (w := Limbs.shl_into n s 1) in *.
change (64 * Z.of_nat n) with (dprec n) in Wval.
rewrite Z.pow_1_r, Z.mod_small in Wval by lia.
(* [w] is [2 s], so its limb 0 is even, and [lor] with the bit adds it. *)
assert (L0 : Limbs.limb w 0 = Limbs.val s mod 2 ^ 63 * 2 ^ 1).
{ rewrite limb0_val by exact Wok. rewrite Wval.
  replace (Limbs.val s * 2) with (2 * Limbs.val s) by ring.
  replace (2 ^ 64) with (2 * 2 ^ 63) by reflexivity.
  rewrite Z.mul_mod_distr_l by lia. rewrite Z.pow_1_r. ring. }
pose proof (Z.mod_pos_bound (Limbs.val s) (2 ^ 63) ltac:(lia)) as Hm.
assert (Hlv : Z.lor (Limbs.limb w 0) (Z.b2z b) = 2 * (Limbs.val s mod 2 ^ 63) + Z.b2z b).
{ rewrite L0, lor_low; [rewrite Z.pow_1_r; ring | lia | rewrite Z.pow_1_r; lia]. }
set (lv := Z.lor (Limbs.limb w 0) (Z.b2z b)) in *.
set (w' := Limbs.update w 0 (lv :: nil)).
assert (Hlv_ok : limbs_ok (lv :: nil)).
{ apply limbs_ok_cons. split; [lia | apply Forall_nil]. }
assert (Hw'ok : limbs_ok w') by (apply limbs_ok_update; assumption).
assert (Hw'val : Limbs.val w' = 2 * Limbs.val s + Z.b2z b).
{ unfold w'. rewrite val_update by (try exact Wok; cbn [length]; lia).
  assert (V1 : Limbs.val (lv :: nil) = lv) by (cbn [Limbs.val]; ring).
  assert (V2 : Limbs.val (firstn (length (lv :: nil)) (skipn 0 w)) = Limbs.limb w 0).
  { cbn [length skipn]. rewrite val_firstn by exact Wok. rewrite limb0_val by exact Wok.
    reflexivity. }
  rewrite V1, V2, L0, Wval. rewrite Z.pow_1_r. change (2 ^ (64 * Z.of_nat 0)) with 1. lia. }
assert (HV : 0 < Limbs.val w' < 2 ^ dprec n) by lia.
assert (NB : 0 <= nat_bits (Limbs.val w') <= dprec n).
{ unfold nat_bits. destruct (Z.eqb_spec (Limbs.val w') 0) as [H0 | H0]; [lia |].
  pose proof (Z.log2_nonneg (Limbs.val w')).
  assert (Z.log2 (Limbs.val w') < dprec n) by (apply Z.log2_lt_pow2; lia).
  lia. }
assert (He' : Limbs.val w' = 0 \/
              - 2 ^ 63 <= e - 1 + nat_bits (Limbs.val w') - dprec n < 2 ^ 63 - 1)
  by (right; lia).
destruct (round_correct n neg w' (e - 1) false false 0%R Hn Hw'ok eq_refl He')
  as (d & Hd & Hok & HR).
exists d. split; [exact Hd |]. split; [exact Hok |].
rewrite HR, Rplus_0_r, Hw'val. apply dround_id; [exact Hn |].
apply (format_int n neg); [exact Hn |]. rewrite Z.abs_eq by lia. lia.
Qed.

(** ** No short number lies strictly inside the window *)

(** The reals [k 2^f] with [|k| < 2^54]: every [f64], every midpoint of
    two adjacent [f64]s, and [2^1024 - 2^970]. *)
Local Definition short (g : R) : Prop :=
  exists k f, g = (IZR k * bpow radix2 f)%R /\ Z.abs k < 2 ^ 54.

Local Lemma short_opp : forall g, short g -> short (- g).
Proof.
intros g (k & f & -> & Hk). exists (- k), f. split.
- rewrite opp_IZR. ring.
- rewrite Z.abs_opp. exact Hk.
Qed.

Local Lemma short_f64 : forall g, f64_format g -> short g.
Proof.
intros g (w & _ & <-).
assert (P53 : Prec_gt_0 53) by (unfold Prec_gt_0; lia).
assert (G : generic_format radix2 (FLT_exp (-1074) 53) (B2R w))
  by exact (generic_format_B2R 53 1024 w).
destruct (FLT_format_generic radix2 (-1074) 53 _ G) as [[m f] Hx Hm _].
exists m, f. split; [exact Hx |]. cbn [Fnum] in Hm.
change (Zpower radix2 53) with (2 ^ 53) in Hm. lia.
Qed.

Local Lemma short_overflow : short (bpow radix2 1024 - bpow radix2 970).
Proof.
exists (2 ^ 54 - 1), 970. split; [| lia].
rewrite minus_IZR. change (2 ^ 54) with (Zpower radix2 54).
rewrite (IZR_Zpower radix2 54) by lia.
replace 1024 with (54 + 970) by reflexivity. rewrite bpow_plus. ring.
Qed.

(** Above [2^(53 + E)], a short number is a multiple of [2^E]. *)
Local Lemma no_between :
  forall s E g, 2 ^ 53 <= s -> short g ->
  ~ (IZR s * bpow radix2 E < g < IZR (s + 1) * bpow radix2 E)%R.
Proof.
intros s E g Hs (k & f & -> & Hk) [H1 H2].
pose proof (bpow_gt_0 radix2 E) as HE.
pose proof (bpow_gt_0 radix2 f) as HF.
assert (Hs0 : (0 < IZR s)%R) by (apply IZR_lt; lia).
assert (Hk0 : 0 < k).
{ destruct (Z_lt_le_dec 0 k) as [Hk0 | Hk0]; [exact Hk0 |]. exfalso.
  assert (Hk1 : (0 <= - IZR k)%R) by (rewrite <- opp_IZR; apply IZR_le; lia).
  assert (0 <= - IZR k * bpow radix2 f)%R by (apply Rmult_le_pos; lra).
  assert (0 < IZR s * bpow radix2 E)%R by (apply Rmult_lt_0_compat; lra).
  lra. }
destruct (Z_lt_le_dec f E) as [Hf | Hf].
- (* [k 2^f < 2^54 2^(E - 1) = 2^53 2^E <= s 2^E] *)
  assert (B1 : (bpow radix2 f <= bpow radix2 (E - 1))%R) by (apply bpow_le; lia).
  assert (B2 : (IZR k < bpow radix2 54)%R).
  { rewrite <- (IZR_Zpower radix2 54) by lia. apply IZR_lt.
    change (Zpower radix2 54) with (2 ^ 54). lia. }
  assert (B3 : (bpow radix2 53 <= IZR s)%R).
  { rewrite <- (IZR_Zpower radix2 53) by lia. apply IZR_le.
    change (Zpower radix2 53) with (2 ^ 53). lia. }
  assert (B4 : (IZR k * bpow radix2 f <= IZR k * bpow radix2 (E - 1))%R).
  { apply Rmult_le_compat_l; [apply IZR_le; lia | exact B1]. }
  assert (B5 : (IZR k * bpow radix2 (E - 1) < bpow radix2 54 * bpow radix2 (E - 1))%R).
  { apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact B2]. }
  assert (B6 : (bpow radix2 53 * bpow radix2 E <= IZR s * bpow radix2 E)%R).
  { apply Rmult_le_compat_r; [lra | exact B3]. }
  assert (B7 : (bpow radix2 54 * bpow radix2 (E - 1) = bpow radix2 53 * bpow radix2 E)%R).
  { rewrite <- !bpow_plus. f_equal. ring. }
  lra.
- (* [k 2^f = (k 2^(f - E)) 2^E], an integer times [2^E] *)
  assert (Hg : (IZR k * bpow radix2 f = IZR (k * 2 ^ (f - E)) * bpow radix2 E)%R).
  { rewrite mult_IZR. change (2 ^ (f - E)) with (Zpower radix2 (f - E)).
    rewrite (IZR_Zpower radix2 (f - E)) by lia.
    rewrite Rmult_assoc, <- bpow_plus. f_equal. f_equal. ring. }
  rewrite Hg in H1, H2.
  apply Rmult_lt_reg_r in H1; [| exact HE].
  apply Rmult_lt_reg_r in H2; [| exact HE].
  apply lt_IZR in H1. apply lt_IZR in H2. lia.
Qed.

(** ** The window *)

(** For a positive [r] in the window, the odd number [v] and [r] lie on the
    same side of every short number. *)
Local Lemma window_pos :
  forall s E (b : bool) r g,
  2 ^ 53 <= s ->
  (IZR s * bpow radix2 E <= r < IZR (s + 1) * bpow radix2 E)%R ->
  (b = false <-> r = (IZR s * bpow radix2 E)%R) ->
  short g ->
  ((g <= r <-> g <= IZR (2 * s + Z.b2z b) * bpow radix2 (E - 1)) /\
   (r <= g <-> IZR (2 * s + Z.b2z b) * bpow radix2 (E - 1) <= g))%R.
Proof.
intros s E b r g Hs Hr Hb Hg.
pose proof (no_between s E g Hs Hg) as Hn.
pose proof (bpow_gt_0 radix2 (E - 1)) as HP.
assert (HE : bpow radix2 E = (2 * bpow radix2 (E - 1))%R).
{ replace E with (1 + (E - 1)) at 1 by ring. rewrite bpow_plus. reflexivity. }
rewrite plus_IZR, HE in Hr, Hn. rewrite HE in Hb.
rewrite plus_IZR, mult_IZR.
destruct b; cbn [Z.b2z].
- (* [r] and [v = (2 s + 1) 2^(E - 1)] are both strictly inside. *)
  assert (Hne : r <> (IZR s * (2 * bpow radix2 (E - 1)))%R)
    by (intros H; apply Hb in H; discriminate).
  destruct (Rle_or_lt g (IZR s * (2 * bpow radix2 (E - 1)))) as [G | G].
  + split; split; intros; lra.
  + assert (G2 : ((IZR s + 1) * (2 * bpow radix2 (E - 1)) <= g)%R).
    { apply Rnot_lt_le. intros G2. apply Hn. split; assumption. }
    split; split; intros; lra.
- (* [r = v = s 2^E] *)
  assert (Hrv : r = (IZR s * (2 * bpow radix2 (E - 1)))%R) by (apply Hb; reflexivity).
  rewrite Hrv. split; split; intros; lra.
Qed.

(** The same for either sign, with [v] first. *)
Local Lemma window_sides :
  forall neg s E (b : bool) r g,
  2 ^ 53 <= s ->
  (IZR s * bpow radix2 E <= r < IZR (s + 1) * bpow radix2 E)%R ->
  (b = false <-> r = (IZR s * bpow radix2 E)%R) ->
  short g ->
  ((g <= cond_Ropp neg (IZR (2 * s + Z.b2z b) * bpow radix2 (E - 1)) <->
    g <= cond_Ropp neg r) /\
   (cond_Ropp neg (IZR (2 * s + Z.b2z b) * bpow radix2 (E - 1)) <= g <->
    cond_Ropp neg r <= g))%R.
Proof.
intros neg s E b r g Hs Hr Hb Hg.
destruct (window_pos s E b r g Hs Hr Hb Hg) as [A1 B1].
destruct (window_pos s E b r (- g) Hs Hr Hb (short_opp g Hg)) as [A B].
revert A1 B1 A B. generalize (IZR (2 * s + Z.b2z b) * bpow radix2 (E - 1))%R.
intros v A1 B1 A B.
destruct neg; cbn [cond_Ropp].
- split; split; intros H.
  + assert (r <= - g)%R by (apply B; lra). lra.
  + assert (v <= - g)%R by (apply B; lra). lra.
  + assert (- g <= r)%R by (apply A; lra). lra.
  + assert (- g <= v)%R by (apply A; lra). lra.
- split; apply iff_sym; assumption.
Qed.

(** Rounding toward -inf or +inf to the elements of [F] is the same for two
    reals on the same side of every element of [F]. *)
Local Lemma round_iff :
  forall (F : R -> Prop) rnd r v w,
  (forall g, F g -> (g <= v <-> g <= r) /\ (v <= g <-> r <= g))%R ->
  (mpfr_round F rnd v w <-> mpfr_round F rnd r w).
Proof.
intros F rnd r v w H.
assert (DN : forall y, Rnd_DN_pt F v y <-> Rnd_DN_pt F r y).
{ intros y. unfold Rnd_DN_pt. split; intros (Fy & H1 & H2); split; [exact Fy | | exact Fy |].
  - split; [apply (H y Fy); exact H1 |].
    intros g Fg Hg. apply H2; [exact Fg | apply (H g Fg); exact Hg].
  - split; [apply (H y Fy); exact H1 |].
    intros g Fg Hg. apply H2; [exact Fg | apply (H g Fg); exact Hg]. }
assert (UP : forall y, Rnd_UP_pt F v y <-> Rnd_UP_pt F r y).
{ intros y. unfold Rnd_UP_pt. split; intros (Fy & H1 & H2); split; [exact Fy | | exact Fy |].
  - split; [apply (H y Fy); exact H1 |].
    intros g Fg Hg. apply H2; [exact Fg | apply (H g Fg); exact Hg].
  - split; [apply (H y Fy); exact H1 |].
    intros g Fg Hg. apply H2; [exact Fg | apply (H g Fg); exact Hg]. }
destruct rnd, w as [| [|] | z | y]; cbn [mpfr_round]; try tauto.
- (* RNDD, -inf *)
  split; intros H0 g Fg; specialize (H0 g Fg); apply Rnot_le_lt; intros H3;
    apply (Rlt_not_le _ _ H0); apply (H g Fg); exact H3.
- apply DN.
- split; intros [Hy H0]; split; try exact Hy; apply DN; exact H0.
- (* RNDU, +inf *)
  split; intros H0 g Fg; specialize (H0 g Fg); apply Rnot_le_lt; intros H3;
    apply (Rlt_not_le _ _ H0); apply (H g Fg); exact H3.
- apply UP.
- split; intros [Hy H0]; split; try exact Hy; apply UP; exact H0.
Qed.

Theorem odd_window_dir :
  forall neg s E b r (up : bool) w,
  2 ^ 53 <= s ->
  (IZR s * bpow radix2 E <= r < IZR (s + 1) * bpow radix2 E)%R ->
  (b = false <-> r = (IZR s * bpow radix2 E)%R) ->
  (mpfr_round f64_format (if up then RNDU else RNDD)
     (cond_Ropp neg (IZR (2 * s + Z.b2z b) * bpow radix2 (E - 1))) w <->
   mpfr_round f64_format (if up then RNDU else RNDD) (cond_Ropp neg r) w).
Proof.
intros neg s E b r up w Hs Hr Hb.
apply round_iff. intros g Hg.
apply (window_sides neg s E b r g Hs Hr Hb (short_f64 g Hg)).
Qed.

(** [v] is [r] rounded to odd with [Z.log2 s + 2] bits. *)
Local Lemma window_odd :
  forall s E (b : bool) r,
  2 ^ 53 <= s ->
  (IZR s * bpow radix2 E <= r < IZR (s + 1) * bpow radix2 E)%R ->
  (b = false <-> r = (IZR s * bpow radix2 E)%R) ->
  (IZR (2 * s + Z.b2z b) * bpow radix2 (E - 1))%R =
  round radix2 (FLX_exp (Z.log2 s + 2)) Zrnd_odd r.
Proof.
intros s E b r Hs Hr Hb.
set (L := Z.log2 s).
assert (HL : 2 ^ L <= s < 2 ^ (L + 1)).
{ pose proof (Z.log2_spec s ltac:(lia)) as H. unfold L. rewrite <- Z.add_1_r in H. exact H. }
assert (HL53 : 53 <= L).
{ unfold L. rewrite <- (Z.log2_pow2 53) by lia. apply Z.log2_le_mono. exact Hs. }
pose proof (bpow_gt_0 radix2 E) as HE0.
pose proof (bpow_gt_0 radix2 (E - 1)) as HP.
assert (HE : bpow radix2 E = (2 * bpow radix2 (E - 1))%R).
{ replace E with (1 + (E - 1)) at 1 by ring. rewrite bpow_plus. reflexivity. }
(* The magnitude of [r] is [L + 1 + E], so its exponent at [L + 2] bits is [E - 1]. *)
assert (Hmag : mag radix2 r = L + 1 + E :> Z).
{ apply mag_unique.
  assert (M1 : (bpow radix2 L <= IZR s)%R).
  { rewrite <- (IZR_Zpower radix2 L) by lia. apply IZR_le. exact (proj1 HL). }
  assert (M2 : (IZR (s + 1) <= bpow radix2 (L + 1))%R).
  { rewrite <- (IZR_Zpower radix2 (L + 1)) by lia. apply IZR_le.
    change (Zpower radix2 (L + 1)) with (2 ^ (L + 1)). lia. }
  assert (M3 : (bpow radix2 L * bpow radix2 E <= IZR s * bpow radix2 E)%R)
    by (apply Rmult_le_compat_r; lra).
  assert (M4 : (IZR (s + 1) * bpow radix2 E <= bpow radix2 (L + 1) * bpow radix2 E)%R)
    by (apply Rmult_le_compat_r; lra).
  rewrite <- !bpow_plus in M3, M4.
  pose proof (bpow_gt_0 radix2 (L + E)).
  replace (L + 1 + E - 1) with (L + E) by ring.
  rewrite Rabs_pos_eq by lra. split; lra. }
set (x := (r * bpow radix2 (- (E - 1)))%R).
assert (Hround : round radix2 (FLX_exp (L + 2)) Zrnd_odd r =
                 (IZR (Zrnd_odd x) * bpow radix2 (E - 1))%R).
{ unfold round, F2R, scaled_mantissa, cexp, FLX_exp. rewrite Hmag.
  replace (L + 1 + E - (L + 2)) with (E - 1) by ring. reflexivity. }
fold L. rewrite Hround. f_equal. f_equal.
(* [x] is in [[2 s, 2 s + 2)], and is [2 s] exactly when [b] is false. *)
assert (Hrx : r = (x * bpow radix2 (E - 1))%R).
{ unfold x. rewrite Rmult_assoc, <- bpow_plus. replace (- (E - 1) + (E - 1)) with 0 by ring.
  cbn [bpow]. ring. }
assert (S0 : (IZR s * bpow radix2 E = IZR (2 * s) * bpow radix2 (E - 1))%R).
{ rewrite HE, mult_IZR. ring. }
assert (S1 : (IZR (s + 1) * bpow radix2 E = IZR (2 * s + 2) * bpow radix2 (E - 1))%R).
{ rewrite HE, !plus_IZR, !mult_IZR. ring. }
rewrite S0, S1, Hrx in Hr. rewrite S0, Hrx in Hb.
destruct Hr as [Hx1 Hx2].
apply Rmult_le_reg_r in Hx1; [| exact HP].
apply Rmult_lt_reg_r in Hx2; [| exact HP].
assert (Hbx : b = false <-> x = IZR (2 * s)).
{ rewrite Hb. split; intros H.
  - apply (Rmult_eq_reg_r (bpow radix2 (E - 1))); [exact H | lra].
  - rewrite H. reflexivity. }
pose proof (Zfloor_lb x) as F1. pose proof (Zfloor_ub x) as F2.
assert (F3 : 2 * s <= Zfloor x <= 2 * s + 1).
{ split.
  - apply Zfloor_lub. exact Hx1.
  - assert (Zfloor x < 2 * s + 2); [| lia]. apply lt_IZR. lra. }
unfold Zrnd_odd. destruct (Req_EM_T x (IZR (Zfloor x))) as [Heq | Hne].
- destruct b; cbn [Z.b2z].
  + (* [x] is an integer other than [2 s], so [2 s + 1]. *)
    assert (Zfloor x <> 2 * s).
    { intros H. rewrite H in Heq. apply Hbx in Heq. discriminate. }
    lia.
  + rewrite (proj1 Hbx eq_refl), Zfloor_IZR. ring.
- destruct b; cbn [Z.b2z].
  + (* rounding to odd of a non-integer in [(2 s, 2 s + 2)] gives [2 s + 1] *)
    destruct (Z.eq_dec (Zfloor x) (2 * s)) as [H0 | H0].
    * rewrite H0. replace (Z.even (2 * s)) with true by (rewrite Z.even_mul; reflexivity).
      cbv iota.
      rewrite Zceil_floor_neq by (intros H; apply Hne; symmetry; exact H). lia.
    * replace (Zfloor x) with (2 * s + 1) by lia.
      replace (Z.even (2 * s + 1)) with false
        by (rewrite Z.even_add, Z.even_mul; reflexivity).
      cbv iota. ring.
  + exfalso. apply Hne. rewrite (proj1 Hbx eq_refl), Zfloor_IZR. reflexivity.
Qed.

Theorem odd_window_near :
  forall neg s E b r w,
  2 ^ 53 <= s ->
  (IZR s * bpow radix2 E <= r < IZR (s + 1) * bpow radix2 E)%R ->
  (b = false <-> r = (IZR s * bpow radix2 E)%R) ->
  (near_round (cond_Ropp neg (IZR (2 * s + Z.b2z b) * bpow radix2 (E - 1))) w <->
   near_round (cond_Ropp neg r) w).
Proof.
intros neg s E b r w Hs Hr Hb.
assert (Hs0 : (0 < IZR s * bpow radix2 E)%R).
{ apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0]. }
assert (Hv0 : (0 < IZR (2 * s + Z.b2z b) * bpow radix2 (E - 1))%R).
{ apply Rmult_lt_0_compat; [apply IZR_lt; pose proof (b2z_bounds b); lia |].
  apply bpow_gt_0. }
assert (Hr0 : (0 < r)%R) by lra.
(* The overflow threshold is on the same side of both. *)
destruct (window_pos s E b r _ Hs Hr Hb short_overflow) as [HT _].
pose proof (window_odd s E b r Hs Hr Hb) as Hodd'.
revert Hv0 HT Hodd'. generalize (IZR (2 * s + Z.b2z b) * bpow radix2 (E - 1))%R.
intros v Hv0 HT Hodd'.
(* Both have the sign [neg]. *)
assert (Sg : forall t, (0 < t)%R -> Rlt_bool (cond_Ropp neg t) 0 = neg).
{ intros t Ht. destruct neg; cbn [cond_Ropp].
  - apply Rlt_bool_true. lra.
  - apply Rlt_bool_false. lra. }
(* Rounding to odd at [Z.log2 s + 2 >= 55] bits, then to nearest [f64], is
   rounding to nearest [f64] (Flocq's [round_N_odd]). *)
assert (HN : round radix2 (FLT_exp (-1074) 53) ZnearestE (cond_Ropp neg v) =
             round radix2 (FLT_exp (-1074) 53) ZnearestE (cond_Ropp neg r)).
{ assert (HL53 : 53 <= Z.log2 s).
  { rewrite <- (Z.log2_pow2 53) by lia. apply Z.log2_le_mono. exact Hs. }
  assert (P53 : Prec_gt_0 53) by (unfold Prec_gt_0; lia).
  assert (Pq : Prec_gt_0 (Z.log2 s + 2)) by (unfold Prec_gt_0; lia).
  assert (Exists_NE radix2 (FLT_exp (-1074) 53)) by (apply exists_NE_FLT; right; lia).
  assert (Exists_NE radix2 (FLX_exp (Z.log2 s + 2))) by (apply exists_NE_FLX; right; lia).
  assert (Hodd : forall t, round radix2 (FLT_exp (-1074) 53) ZnearestE
                             (round radix2 (FLX_exp (Z.log2 s + 2)) Zrnd_odd t) =
                           round radix2 (FLT_exp (-1074) 53) ZnearestE t).
  { intros t. apply round_N_odd;
      [reflexivity | typeclasses eauto .. | intros e; unfold FLX_exp, FLT_exp; lia]. }
  rewrite Hodd'.
  destruct neg; cbn [cond_Ropp]; [rewrite !round_NE_opp; f_equal |]; apply Hodd. }
unfold near_round.
rewrite !abs_cond_Ropp, (Rabs_pos_eq v), (Rabs_pos_eq r) by lra.
rewrite (Sg v Hv0), (Sg r Hr0), HN.
assert (Nv : cond_Ropp neg v <> 0%R) by (destruct neg; cbn [cond_Ropp]; lra).
assert (Nr : cond_Ropp neg r <> 0%R) by (destruct neg; cbn [cond_Ropp]; lra).
destruct (Rle_dec (bpow radix2 1024 - bpow radix2 970) v) as [H1 | H1];
  destruct (Rle_dec (bpow radix2 1024 - bpow radix2 970) r) as [H2 | H2].
- reflexivity.
- exfalso. apply H2. apply HT. exact H1.
- exfalso. apply H1. apply HT. exact H2.
- tauto.
Qed.
