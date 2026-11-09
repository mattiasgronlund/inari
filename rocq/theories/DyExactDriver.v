(** * The drivers at the exact point 0, and [f64]s as rationals

    [driver_exact] of [DyPown.v] says that a driver returns a nonzero
    [f64] [v] where an evaluation encloses it by the point [v] at every
    level. [driver_exact_zero] says the same of the point 0: [to_f64] of
    [Model.v] returns [zero], the [f64] [+0], at a dyadic 0 in both
    directions, so that [ziv_at] passes at every level and both drivers
    return [zero] ([ziv_at_exact_zero], [ziv_strict_exact_zero] and
    [ziv_exact_zero]). Every finite [f64] is a rational [IZR p / IZR q]
    with [q > 0] ([f64_rational]); a power of 2 is a finite [f64] only
    from [2^-1074] to [2^1023] ([f64_pow2]), and a power of 10 only from
    [10^0] to [10^22] ([f64_pow10]), as [10^k] has [5^k] in its
    significand for [k > 0], and [5^23 > 2^53], and is not a dyadic for
    [k < 0]. *)

From Stdlib Require Import ZArith Reals Lra Lia List Znumtheory.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary MpfrRound OfPointCore DyRound DyConv DyOps
  DyDriver DyGrow DyPown.

Open Scope R_scope.

(** A driver [z] returns [zero] where [ev] encloses 0 by the point [0] at
    every level, from any start up to 64. *)
Definition driver_exact_zero (z : (nat -> option Dyadic.encl) -> bool -> nat -> option f64) : Prop :=
  forall ev (up : bool) start,
  (start <= 64)%nat ->
  (forall n, level_ok n -> exists a, ev n = Some a /\ encl_ok n a /\
     lo_R a = 0 /\ hi_R a = 0) ->
  z ev up start = Some zero.

Lemma ziv_at_exact_zero :
  forall ev (up : bool) n,
  level_ok n ->
  (exists a, ev n = Some a /\ encl_ok n a /\ lo_R a = 0 /\ hi_R a = 0) ->
  Dyadic.ziv_at ev n up = Some (Some zero).
Proof.
intros ev up n Hn (a & Ea & (Hlo & Hhi & _) & Vlo & Vhi).
unfold Dyadic.ziv_at, Dyadic.round_bounds. rewrite Ea. cbv beta iota.
(* [to_f64] returns [zero] at a dyadic 0, in both directions. *)
unfold Dyadic.to_f64.
rewrite (proj2 (is_zero_correct n _ Hn Hlo) Vlo), (proj2 (is_zero_correct n _ Hn Hhi) Vhi).
reflexivity.
Qed.

(** [ziv_strict], and so [ziv], returns [zero] at its first level. *)
Lemma ziv_strict_exact_zero : driver_exact_zero ziv_strict.
Proof.
intros ev up start Hs Hev. unfold ziv_strict.
rewrite (ziv_levels_exact ev up start zero).
- reflexivity.
- intros n Hin. unfold level_ok. cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]; [lia |]). destruct Hin.
- exists 64%nat. split; [| exact Hs]. cbn [In]. do 6 right. left. reflexivity.
- intros n Hn. apply ziv_at_exact_zero; [exact Hn | exact (Hev n Hn)].
Qed.

Lemma ziv_exact_zero : driver_exact_zero Dyadic.ziv.
Proof.
intros ev up start Hs Hev. apply ziv_strict_ziv. exact (ziv_strict_exact_zero ev up start Hs Hev).
Qed.

(** ** Helpers *)

(** [m] and [e] of a finite [f64]: [m < 2^53] and [e <= 971], as
    [km_bounded] of [KahanMcDonald.v]. *)
Lemma dxd_bounded :
  forall m e, SpecFloat.bounded 53 1024 m e = true ->
  (Z.pos m < 2 ^ 53)%Z /\ (e <= 971)%Z.
Proof.
intros m e H.
unfold SpecFloat.bounded, SpecFloat.canonical_mantissa, SpecFloat.fexp,
  SpecFloat.emin in H.
apply andb_prop in H as [H He]. apply Z.leb_le in He. split; [| lia].
apply Z.eqb_eq in H.
rewrite Zpos_digits2_pos in H.
pose proof (Zdigits_correct radix2 (Z.pos m)) as [_ Hd].
assert (Hd53 : (Zdigits radix2 (Z.pos m) <= 53)%Z) by lia.
apply (Z.lt_le_trans _ _ _ Hd).
change (2 ^ 53)%Z with (Zpower radix2 53).
apply Zpower_le. exact Hd53.
Qed.

Lemma dxd_IZR_pow2 : forall e, (0 <= e)%Z -> IZR (2 ^ e) = bpow radix2 e.
Proof. exact (IZR_Zpower radix2). Qed.

Lemma dxd_powerRZ_pos : forall c p, powerRZ (IZR c) (Z.pos p) = IZR (c ^ Z.pos p).
Proof. intros c p. unfold powerRZ. rewrite pow_IZR, positive_nat_Z. reflexivity. Qed.

Lemma dxd_powerRZ_neg : forall c p, powerRZ (IZR c) (Z.neg p) = / IZR (c ^ Z.pos p).
Proof. intros c p. unfold powerRZ. rewrite pow_IZR, positive_nat_Z. reflexivity. Qed.

Lemma dxd_rel_prime_pow :
  forall a b i : Z, (0 <= i)%Z -> rel_prime a b -> rel_prime a (b ^ i).
Proof.
intros a b i Hi Hab. pattern i. apply natlike_ind; [| | exact Hi].
- rewrite Z.pow_0_r. apply rel_prime_sym, rel_prime_1.
- intros j Hj IH. rewrite Z.pow_succ_r by exact Hj. apply rel_prime_mult; assumption.
Qed.

(** [5^i] and [2^j] have no common factor. *)
Lemma dxd_rel_prime_5_2 :
  forall i j : Z, (0 <= i)%Z -> (0 <= j)%Z -> rel_prime (5 ^ i) (2 ^ j).
Proof.
intros i j Hi Hj. apply rel_prime_sym, dxd_rel_prime_pow; [exact Hi |].
apply rel_prime_sym, dxd_rel_prime_pow; [exact Hj |].
apply Zgcd_1_rel_prime. reflexivity.
Qed.

Lemma f64_rational :
  forall x : f64, is_finite x = true -> exists p q : Z, (0 < q)%Z /\ B2R x = IZR p / IZR q.
Proof.
intros x Fx. destruct x as [s | s | | s m e B]; try discriminate Fx.
- exists 0%Z, 1%Z. split; [lia |]. cbn [B2R]. unfold Rdiv. rewrite Rmult_0_l. reflexivity.
- (* [B2R x = m 2^e], with [q = 1] or [q = 2^-e] *)
  unfold B2R, F2R. cbn [Fnum Fexp].
  destruct (Z.le_gt_cases 0 e) as [He | He].
  + exists (SpecFloat.cond_Zopp s (Z.pos m) * 2 ^ e)%Z, 1%Z. split; [lia |].
    rewrite mult_IZR, (dxd_IZR_pow2 e He).
    unfold Rdiv. rewrite Rinv_1, Rmult_1_r. reflexivity.
  + exists (SpecFloat.cond_Zopp s (Z.pos m)), (2 ^ (- e))%Z.
    split; [apply Z.pow_pos_nonneg; lia |].
    rewrite (dxd_IZR_pow2 (- e)) by lia. unfold Rdiv. rewrite bpow_opp, Rinv_inv. reflexivity.
Qed.

Lemma f64_pow2 :
  forall (v : f64) (k : Z), is_finite v = true -> B2R v = powerRZ 2 k -> (-1074 <= k <= 1023)%Z.
Proof.
intros v k Fv H.
assert (Hpos : 0 < B2R v) by (rewrite H; apply powerRZ_lt; lra).
assert (E : powerRZ 2 k = bpow radix2 k) by (rewrite bpow_powerRZ; reflexivity).
rewrite E in H.
assert (S : is_finite_strict v = true).
{ destruct v as [s | s | | s m e B]; try discriminate Fv; [cbn [B2R] in Hpos; lra | reflexivity]. }
(* [2^-1074 <= |B2R v| < 2^1024] *)
pose proof (abs_B2R_ge_emin 53 1024 v S) as L.
pose proof (abs_B2R_lt_emax 53 1024 v) as U.
rewrite H, Rabs_pos_eq in L, U by apply bpow_ge_0.
change (SpecFloat.emin 53 1024) with (-1074)%Z in L.
apply le_bpow in L. apply lt_bpow in U. lia.
Qed.

Lemma f64_pow10 :
  forall (v : f64) (k : Z), is_finite v = true -> B2R v = powerRZ 10 k -> (0 <= k <= 22)%Z.
Proof.
intros v k Fv H.
assert (Hpos : 0 < B2R v) by (rewrite H; apply powerRZ_lt; lra).
destruct v as [s | s | | s m e B]; try discriminate Fv; [cbn [B2R] in Hpos; lra |].
destruct (dxd_bounded m e B) as [Hm _].
unfold B2R, F2R in H, Hpos. cbn [Fnum Fexp] in H, Hpos.
assert (Pe := bpow_gt_0 radix2 e).
destruct s.
{ (* a negative [v] *)
  exfalso. cbn [SpecFloat.cond_Zopp Z.opp] in Hpos.
  assert (IZR (Z.neg m) < 0) by (apply IZR_lt; reflexivity). nra. }
cbn [SpecFloat.cond_Zopp Z.opp] in H.
assert (P5 : forall i j, (0 <= i)%Z -> (0 <= j)%Z -> rel_prime (5 ^ i) (2 ^ j)) by exact dxd_rel_prime_5_2.
assert (T10 : forall j, (0 <= j)%Z -> (10 ^ j = 5 ^ j * 2 ^ j)%Z)
  by (intros j _; rewrite <- Z.pow_mul_l; reflexivity).
destruct k as [| kp | kp]; [lia | |].
- (* [k > 0]: [5^k] divides [m], so [5^k <= m < 2^53] and [k <= 22]. *)
  rewrite (dxd_powerRZ_pos 10) in H.
  assert (D : (5 ^ Z.pos kp | Z.pos m)%Z).
  { destruct (Z.le_gt_cases 0 e) as [He | He].
    - rewrite <- (dxd_IZR_pow2 e He), <- mult_IZR in H. apply eq_IZR in H.
      apply (Gauss _ (2 ^ e)); [| apply P5; lia].
      exists (2 ^ Z.pos kp)%Z. rewrite Z.mul_comm, H, T10 by lia. ring.
    - replace (bpow radix2 e) with (/ IZR (2 ^ (- e))) in H
        by (rewrite (dxd_IZR_pow2 (- e)) by lia; rewrite bpow_opp, Rinv_inv; reflexivity).
      assert (P2 : 0 < IZR (2 ^ (- e))) by (apply IZR_lt, Z.pow_pos_nonneg; lia).
      assert (H' : IZR (Z.pos m) = IZR (10 ^ Z.pos kp * 2 ^ (- e))).
      { rewrite mult_IZR, <- H. field. lra. }
      apply eq_IZR in H'. rewrite H', T10 by lia.
      exists (2 ^ Z.pos kp * 2 ^ (- e))%Z. ring. }
  apply Z.divide_pos_le in D; [| lia].
  split; [lia |].
  destruct (Z.le_gt_cases (Z.pos kp) 22) as [| Hk]; [assumption | exfalso].
  assert (M : (5 ^ 23 <= 5 ^ Z.pos kp)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (C : (2 ^ 53 < 5 ^ 23)%Z) by reflexivity.
  lia.
- (* [k < 0]: [m 2^e 10^-k = 1] has no solution. *)
  exfalso. rewrite (dxd_powerRZ_neg 10) in H.
  assert (P10 : 0 < IZR (10 ^ Z.pos kp)) by (apply IZR_lt, Z.pow_pos_nonneg; lia).
  assert (L10 : (10 ^ 1 <= 10 ^ Z.pos kp)%Z) by (apply Z.pow_le_mono_r; lia).
  destruct (Z.le_gt_cases 0 e) as [He | He].
  + rewrite <- (dxd_IZR_pow2 e He), <- mult_IZR in H.
    assert (H' : IZR (Z.pos m * 2 ^ e * 10 ^ Z.pos kp) = IZR 1).
    { rewrite mult_IZR, H. field. lra. }
    apply eq_IZR in H'.
    assert (Q : (0 < 2 ^ e)%Z) by (apply Z.pow_pos_nonneg; lia).
    nia.
  + (* [m 10^-k = 2^-e], and [5] does not divide [2^-e] *)
    replace (bpow radix2 e) with (/ IZR (2 ^ (- e))) in H
      by (rewrite (dxd_IZR_pow2 (- e)) by lia; rewrite bpow_opp, Rinv_inv; reflexivity).
    assert (P2 : 0 < IZR (2 ^ (- e))) by (apply IZR_lt, Z.pow_pos_nonneg; lia).
    assert (H' : IZR (2 ^ (- e)) = IZR (Z.pos m * 10 ^ Z.pos kp)).
    { rewrite mult_IZR.
      assert (Hm' : IZR (Z.pos m) = IZR (2 ^ (- e)) * / IZR (10 ^ Z.pos kp)).
      { apply (Rmult_eq_reg_r (/ IZR (2 ^ (- e)))).
        - rewrite H. field. repeat split; lra.
        - apply Rinv_neq_0_compat. lra. }
      rewrite Hm'. field. lra. }
    apply eq_IZR in H'.
    assert (D : (5 ^ Z.pos kp | 1)%Z).
    { apply (Gauss _ (2 ^ (- e))); [| apply P5; lia].
      exists (Z.pos m * 2 ^ Z.pos kp)%Z. rewrite Z.mul_1_r, H', T10 by lia. ring. }
    apply Z.divide_pos_le in D; [| lia].
    assert (L5 : (5 ^ 1 <= 5 ^ Z.pos kp)%Z) by (apply Z.pow_le_mono_r; lia).
    lia.
Qed.
