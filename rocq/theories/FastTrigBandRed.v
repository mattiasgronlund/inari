(** * The reduction of the fast paths of [sin], [cos] and [tan] near the multiples of π/2 below 2^16

    [DyadicTrig.U4] of [Model.v] is finite with [|U4| <= 2^-120], and [U1
    + U2 + U3 + U4] is within 2^-174 of π/4096 ([band_consts]). Where
    [DyadicTrig.fast_reduce x] returns [(n, rh, rl, rr)] with [n] a
    nonzero multiple of 2048, ρ = x - n π/4096 is at least 2^-61 in
    magnitude ([km_distance] of [KahanMcDonald.v], as [n π/4096] is a
    nonzero multiple of π/2) and at most π/8192 (1 + 2^-24), and
    [DyadicTrig.fast_band_reduce false n rh rl] returns [(sh, sl, sr)]
    with [sh + sl] within a relative 2^-74 of ρ, [|sl| <= 2^-24 |sh|] and
    [sr = sh + sl] rounded ([fast_band_reduce_correct]): [rh = x - n U1 -
    n U2] is exact ([FastTrigReduce.v]), [n U3] is split exactly into
    [RN(n U3)] and its error [Dekker], [rh - RN(n U3)] is split exactly
    [Knuth], and [n U4] is added to the tail. It is the same with an FMA
    ([fast_band_reduce_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr TwoSum TwoProduct FastRound FastExpErr FastTrigTables
  FastTrigReduce KahanMcDonald.
From Inari Require FastExpTables FastExpReduce FastRoundErr MulRuTiny FastLogFin.

Open Scope R_scope.

(** ** The fourth part of π/4096

    As [fast_trig_consts] of [FastTrigTables.v] checks [U1 + U2 + U3], by
    [vm_compute] in integer fixed point with 200 fractional bits, against
    [π 2^-12] between [Pt 2^-200] and [(Pt + 1) 2^-200] for [Pt] from
    [pi_trunc 188]. [U4] has its last bit at 2^-173, so all four are exact
    there. The two helpers are those of [FastTrigTables.v], where they are
    [Local]. *)

Local Lemma IZR_pow2 : forall e, (0 <= e)%Z -> IZR (2 ^ e) = bpow radix2 e.
Proof. intros e He. rewrite <- IZR_Zpower by exact He. reflexivity. Qed.

(** [x] between [A 2^e] and [B 2^e] is within [K 2^e] of [T 2^e] if [A]
    and [B] are within [K] of [T]. *)
Local Lemma between_close :
  forall (x : R) (A B T K e : Z),
  IZR A * bpow radix2 e <= x <= IZR B * bpow radix2 e ->
  (T - K <= A)%Z -> (B <= T + K)%Z ->
  Rabs (IZR T * bpow radix2 e - x) <= IZR K * bpow radix2 e.
Proof.
intros x A B T K e [H1 H2] HA HB.
apply IZR_le in HA, HB. rewrite minus_IZR in HA. rewrite plus_IZR in HB.
assert (Hb : 0 <= bpow radix2 e) by apply bpow_ge_0.
pose proof (Rmult_le_compat_r _ _ _ Hb HA) as HA'.
pose proof (Rmult_le_compat_r _ _ _ Hb HB) as HB'.
apply Rabs_le. lra.
Qed.

(** [c] between [L 2^e] and [(L + 1) 2^e], times [s 2^f] for [s >= 0] *)
Local Lemma scale_encl :
  forall (c : R) (L s e f : Z), (0 <= s)%Z ->
  IZR L * bpow radix2 e <= c <= IZR (L + 1) * bpow radix2 e ->
  IZR (s * L) * bpow radix2 (e + f) <= IZR s * bpow radix2 f * c <=
  IZR (s * (L + 1)) * bpow radix2 (e + f).
Proof.
intros c L s e f Hs [H1 H2].
assert (Hk : 0 <= IZR s * bpow radix2 f)
  by (apply Rmult_le_pos; [apply IZR_le; exact Hs | apply bpow_ge_0]).
rewrite !mult_IZR, bpow_plus. split.
- replace (IZR s * IZR L * (bpow radix2 e * bpow radix2 f))
    with (IZR s * bpow radix2 f * (IZR L * bpow radix2 e)) by ring.
  apply Rmult_le_compat_l; [exact Hk | exact H1].
- replace (IZR s * IZR (L + 1) * (bpow radix2 e * bpow radix2 f))
    with (IZR s * bpow radix2 f * (IZR (L + 1) * bpow radix2 e)) by ring.
  apply Rmult_le_compat_l; [exact Hk | exact H2].
Qed.

(** [|U4| <= 2^80 2^-200] and [U1 + U2 + U3 + U4] within [2^26 2^-200]
    of [π 2^-12], with 200 fractional bits *)
Definition band_okb (Pt : Z) : bool :=
  match FastExpTables.fix_of 200 (from_bits DyadicTrig.U1),
        FastExpTables.fix_of 200 (from_bits DyadicTrig.U2),
        FastExpTables.fix_of 200 (from_bits DyadicTrig.U3),
        FastExpTables.fix_of 200 (from_bits DyadicTrig.U4) with
  | Some Ua, Some Ub, Some Uc, Some Ud =>
      (Z.abs Ud <=? 2 ^ 80)%Z &&
      (Ua + Ub + Uc + Ud - 2 ^ 26 <=? Pt)%Z && (Pt + 1 <=? Ua + Ub + Uc + Ud + 2 ^ 26)%Z
  | _, _, _, _ => false
  end.

Local Lemma band_ok : band_okb (Limbs.val DyadicConsts.PI / 2 ^ (4222 - 188)) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem band_consts :
  is_finite (from_bits DyadicTrig.U4) = true /\
  Rabs (B2R (from_bits DyadicTrig.U4)) <= bpow radix2 (-120) /\
  Rabs (PI / 4096 - (B2R (from_bits DyadicTrig.U1) + B2R (from_bits DyadicTrig.U2) +
    B2R (from_bits DyadicTrig.U3) + B2R (from_bits DyadicTrig.U4))) <= bpow radix2 (-174).
Proof.
pose proof (pi_trunc 188 ltac:(lia)) as HP.
pose proof band_ok as Hok.
set (Pt := (Limbs.val DyadicConsts.PI / 2 ^ (4222 - 188))%Z) in HP, Hok.
clearbody Pt.
unfold band_okb in Hok.
destruct (FastExpTables.fix_of 200 (from_bits DyadicTrig.U1)) as [Ua|] eqn:EA;
  [|discriminate Hok].
destruct (FastExpTables.fix_of 200 (from_bits DyadicTrig.U2)) as [Ub|] eqn:EB;
  [|discriminate Hok].
destruct (FastExpTables.fix_of 200 (from_bits DyadicTrig.U3)) as [Uc|] eqn:EC;
  [|discriminate Hok].
destruct (FastExpTables.fix_of 200 (from_bits DyadicTrig.U4)) as [Ud|] eqn:ED;
  [|discriminate Hok].
apply FastExpTables.fix_of_correct in EA as [_ RA].
apply FastExpTables.fix_of_correct in EB as [_ RB].
apply FastExpTables.fix_of_correct in EC as [_ RC].
apply FastExpTables.fix_of_correct in ED as [FD RD].
change (Z.opp 200) with (-200)%Z in RA, RB, RC, RD.
cbv beta iota in Hok.
apply andb_prop in Hok as [Hok H2]. apply andb_prop in Hok as [H0 H1].
apply Z.leb_le in H0, H1, H2.
split; [exact FD|]. split.
- (* [|Ud| <= 2^80] *)
  rewrite RD, Rabs_mult, (Rabs_pos_eq (bpow radix2 (-200))) by apply bpow_ge_0.
  rewrite <- abs_IZR.
  apply Rle_trans with (IZR (2 ^ 80) * bpow radix2 (-200)).
  + apply Rmult_le_compat_r; [apply bpow_ge_0 | apply IZR_le; exact H0].
  + rewrite IZR_pow2, <- bpow_plus by lia. apply Rle_refl.
- (* π/4096 between [Pt 2^-200] and [(Pt + 1) 2^-200] *)
  pose proof (scale_encl PI Pt 1 (-188) (-12) ltac:(lia) HP) as HQ.
  rewrite !Z.mul_1_l in HQ. change (-188 + -12)%Z with (-200)%Z in HQ.
  replace (IZR 1 * bpow radix2 (-12) * PI) with (PI / 4096) in HQ
    by (change (bpow radix2 (-12)) with (/ 4096); unfold Rdiv; ring).
  pose proof (between_close _ _ _ (Ua + Ub + Uc + Ud) (2 ^ 26) (-200) HQ H1 H2) as C.
  rewrite IZR_pow2, <- bpow_plus in C by lia.
  change (26 + -200)%Z with (-174)%Z in C.
  rewrite RA, RB, RC, RD, Rabs_minus_sym.
  replace (IZR Ua * bpow radix2 (-200) + IZR Ub * bpow radix2 (-200) +
    IZR Uc * bpow radix2 (-200) + IZR Ud * bpow radix2 (-200))
    with (IZR (Ua + Ub + Uc + Ud) * bpow radix2 (-200))
    by (rewrite !plus_IZR; ring).
  exact C.
Qed.

(** ** The reduction *)

(** What [fast_reduce] computes, as [fast_reduce_correct] unfolds it:
    [n] is the float [kf], [rh = x - n U1 - n U2] exactly, and [rl =
    -RN(n U3)]. *)
Local Lemma band_setup :
  forall x n rh rl rr,
  DyadicTrig.fast_reduce x = Some (n, rh, rl, rr) ->
  exists kf, is_finite kf = true /\ B2R kf = IZR n /\ (Z.abs n <= 85445659)%Z /\
  rl = opp (mul kf (from_bits DyadicTrig.U3)) /\
  B2R rh = B2R x - IZR n * (B2R (from_bits DyadicTrig.U1) + B2R (from_bits DyadicTrig.U2)).
Proof.
intros x n rh rl rr H.
destruct (fast_reduce_correct x n rh rl rr H) as (Fx & Hx & _).
unfold DyadicTrig.fast_reduce in H.
destruct (is_nan x || ge (fabs x) DyadicTrig.limit); [discriminate H|].
cbv beta iota zeta in H.
injection H as En Erh Erl Err. subst n rh rl rr.
pose proof (reduce_k x Fx Hx) as K. cbv zeta in K. destruct K as (Fkf & Ekf & Hn & Hb).
pose proof (reduce_rh x _ _ Fx Hx Fkf Ekf Hn Hb) as R. cbv zeta in R.
destruct R as (_ & Erh & _).
eexists. split; [exact Fkf|]. split; [exact Ekf|]. split; [exact Hn|].
split; [reflexivity | exact Erh].
Qed.

(** [p = RN(n U3)] is within [2^-91] of [n U3], which is at most [2^-38],
    for [|n| <= 85445659]. *)
Local Lemma band_p :
  forall kf n, is_finite kf = true -> B2R kf = IZR n -> (Z.abs n <= 85445659)%Z ->
  is_finite (mul kf (from_bits DyadicTrig.U3)) = true /\
  Rabs (B2R (mul kf (from_bits DyadicTrig.U3)) - IZR n * B2R (from_bits DyadicTrig.U3)) <=
    bpow radix2 (-91) /\
  Rabs (IZR n * B2R (from_bits DyadicTrig.U3)) <= bpow radix2 (-38).
Proof.
intros kf n Fkf Ekf Hn.
destruct reduce_lits as (_ & _ & _ & _ & _ & H3).
destruct reduce_bpow as (_ & _ & _ & _ & _ & _ & _ & B38 & _).
assert (F3 : is_finite (from_bits DyadicTrig.U3) = true) by reflexivity.
assert (Hnr : Rabs (IZR n) <= 85445659) by (rewrite <- abs_IZR; apply IZR_le; exact Hn).
apply Rabs_le_inv in Hnr.
assert (HnU3 : Rabs (IZR n * B2R (from_bits DyadicTrig.U3)) <= bpow radix2 (-38)).
{ rewrite H3, B38. apply Rabs_le. lra. }
destruct (mul_below_max kf (from_bits DyadicTrig.U3) Fkf F3) as (FM3 & HM3 & _).
{ apply FastExpReduce.le_MAX. rewrite Ekf. apply Rle_trans with (1 := HnU3). rewrite B38. lra. }
split; [exact FM3|]. split; [|exact HnU3].
rewrite HM3, Ekf. apply (FastExpReduce.RN_err_le _ (-38)); [lia | reflexivity | exact HnU3].
Qed.

(** For [n <> 0], [p] is at least [2^-65] and below 1, [n] below [2^27]
    and [U3] below [2^-63], so the error of [p] is exact (Dekker), with or
    without an FMA. *)
Local Lemma band_exact :
  forall b kf n, is_finite kf = true -> B2R kf = IZR n -> (Z.abs n <= 85445659)%Z ->
  n <> 0%Z ->
  Generic.two_prod_is_exact b kf (from_bits DyadicTrig.U3) (mul kf (from_bits DyadicTrig.U3)) =
    true.
Proof.
intros b kf n Fkf Ekf Hn Hn0.
destruct (band_p kf n Fkf Ekf Hn) as (Fp & Ep & HnU3).
destruct reduce_lits as (_ & _ & _ & _ & _ & H3).
assert (F3 : is_finite (from_bits DyadicTrig.U3) = true) by reflexivity.
assert (Hn1 : 1 <= Rabs (IZR n)) by (rewrite <- abs_IZR; apply IZR_le; lia).
assert (Hnr : Rabs (IZR n) <= 85445659) by (rewrite <- abs_IZR; apply IZR_le; exact Hn).
set (p := mul kf (from_bits DyadicTrig.U3)) in *.
assert (L : 4967757600021511 / 166153499473114484112975882535043072 <=
            Rabs (IZR n * B2R (from_bits DyadicTrig.U3))).
{ rewrite H3, Rabs_mult,
    (Rabs_pos_eq (4967757600021511 / 166153499473114484112975882535043072)) by lra.
  lra. }
pose proof (Rabs_triang_inv (IZR n * B2R (from_bits DyadicTrig.U3)) (B2R p)) as T1.
pose proof (Rabs_triang_inv (B2R p) (IZR n * B2R (from_bits DyadicTrig.U3))) as T2.
rewrite Rabs_minus_sym in T1.
cbn [bpow radix_val radix2 Z.opp] in *.
assert (E1 : (-65 <= Generic.exponent p)%Z).
{ apply MulRuTiny.exponent_ge; [exact Fp|]. cbn [bpow radix_val radix2 Z.opp]. lra. }
assert (E2 : (Generic.exponent p < 1)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fp | lia |]. cbn [bpow radix_val radix2 Z.opp]. lra. }
assert (E3 : (Generic.exponent kf < 27)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fkf | lia |]. rewrite Ekf.
  cbn [bpow radix_val radix2 Z.opp]. lra. }
assert (E4 : (Generic.exponent (from_bits DyadicTrig.U3) < -63)%Z).
{ apply MulRuTiny.exponent_lt; [exact F3 | lia |]. rewrite H3, Rabs_pos_eq by lra.
  cbn [bpow radix_val radix2 Z.opp]. lra. }
unfold Generic.two_prod_is_exact. cbv zeta.
destruct b; cbv beta iota; rewrite ?andb_true_iff, ?Z.leb_le; lia.
Qed.

(** A finite float with a nonzero value is not a zero. *)
Local Lemma strict_of_nonzero :
  forall f : f64, is_finite f = true -> B2R f <> 0 -> is_finite_strict f = true.
Proof.
intros [s|s| |s m e B] F H; try discriminate F; [|reflexivity].
exfalso. apply H. reflexivity.
Qed.

(** [n as f64] is the float [kf] of [fast_reduce] for [n <> 0]. *)
Local Lemma band_of_i64 :
  forall kf n, is_finite kf = true -> B2R kf = IZR n -> (Z.abs n <= 85445659)%Z ->
  n <> 0%Z -> DyadicTrig.of_i64 n = kf.
Proof.
intros kf n Fkf Ekf Hn Hn0.
change (DyadicTrig.of_i64 n) with (DyadicLog.of_i64 n).
destruct (FastLogFin.fl_of_i64 n) as (Fo & Eo).
{ assert (P53 : (2 ^ 53 = 9007199254740992)%Z) by reflexivity. lia. }
assert (Hz : IZR n <> 0) by (apply not_0_IZR; exact Hn0).
apply B2R_inj.
- apply strict_of_nonzero; [exact Fo | rewrite Eo; exact Hz].
- apply strict_of_nonzero; [exact Fkf | rewrite Ekf; exact Hz].
- rewrite Eo, Ekf. reflexivity.
Qed.

(** For [n] a nonzero multiple of 2048, [n π/4096] is a nonzero multiple
    of π/2, so [ρ] is at least [2^-61] in magnitude ([km_distance]). *)
Local Lemma band_dist_small :
  forall x n rh rl rr,
  DyadicTrig.fast_reduce x = Some (n, rh, rl, rr) -> Z.land n 2047 = 0%Z -> n <> 0%Z ->
  bpow radix2 (-61) <= Rabs (B2R x - IZR n * (PI / 4096)) <=
    PI / 8192 * (1 + bpow radix2 (-24)).
Proof.
intros x n rh rl rr H Hl Hn0.
destruct (fast_reduce_correct x n rh rl rr H) as (Fx & _ & _ & _ & _ & _ & _ & _ & Hu & _).
split; [|exact Hu].
change 2047%Z with (Z.ones 11) in Hl.
rewrite Z.land_ones in Hl by lia.
change (2 ^ 11)%Z with 2048%Z in Hl.
pose proof (Z_div_exact_2 n 2048 ltac:(lia) Hl) as En.
set (k := (n / 2048)%Z) in En.
assert (Hk : k <> 0%Z) by lia.
pose proof (km_distance x k Fx Hk) as K.
replace (IZR n * (PI / 4096)) with (IZR k * (PI / 2)); [exact K|].
rewrite En, mult_IZR. field.
Qed.

(** Two triangle inequalities, in the forms the budget uses. *)
Local Lemma abs_le_near : forall u v d, Rabs (u - v) <= d -> Rabs u <= Rabs v + d.
Proof. intros u v d H. pose proof (Rabs_triang_inv u v). lra. Qed.

Local Lemma Rabs_sub_le : forall u v, Rabs (u - v) <= Rabs u + Rabs v.
Proof. intros u v. unfold Rminus. rewrite <- (Rabs_Ropp v). apply Rabs_triang. Qed.

(** The error budget of [fast_band_reduce], in reals: [rho] is ρ, [Y = rh
    + rl] within [2^-90] of it, [s + e = Y] exactly (TwoSum), [pl] the
    exact error of [RN(n U3)], [nu4 = n U4], [nd = n (π/4096 - ΣU)], and
    [m], [a] and [t] are [n U4], [pl + m] and [e - a] rounded to nearest.
    Then [ρ - (s + t)] is [(e - a - t) + (a - (pl + m)) + (m - n U4) - nd],
    at most [2^-106 |ρ| + 2^-141], which is below [2^-74 |ρ|] for [|ρ| >=
    2^-61]. *)
Local Lemma band_budget :
  forall rho Y s e pl m a t nu4 nd : R,
  rho = Y - pl - nu4 - nd -> s + e = Y ->
  Rabs (rho - Y) <= bpow radix2 (-90) -> bpow radix2 (-61) <= Rabs rho ->
  Rabs (s - Y) <= bpow radix2 (-53) * Rabs Y + bpow radix2 (-1075) ->
  Rabs pl <= bpow radix2 (-91) -> Rabs nu4 <= bpow radix2 (-93) ->
  Rabs nd <= bpow radix2 (-147) ->
  Rabs (m - nu4) <= bpow radix2 (-53) * Rabs nu4 + bpow radix2 (-1075) ->
  Rabs (a - (pl + m)) <= bpow radix2 (-53) * Rabs (pl + m) + bpow radix2 (-1075) ->
  Rabs (t - (e - a)) <= bpow radix2 (-53) * Rabs (e - a) + bpow radix2 (-1075) ->
  Rabs (rho - (s + t)) <= bpow radix2 (-74) * Rabs rho /\
  Rabs t <= bpow radix2 (-24) * Rabs s.
Proof.
intros rho Y s e pl m a t nu4 nd ER ES HRY HR HsY Hpl Hnu4 Hnd Hm Ha Ht.
(* The triangle inequalities that bound each atom by the ones before it. *)
pose proof (Rabs_triang_inv m nu4) as T1.
pose proof (Rabs_triang pl m) as T2.
pose proof (Rabs_triang_inv a (pl + m)) as T3.
pose proof (Rabs_triang_inv rho Y) as T4.
pose proof (Rabs_triang_inv Y rho) as T5. rewrite Rabs_minus_sym in T5.
pose proof (Rabs_triang_inv Y s) as T6. rewrite Rabs_minus_sym in T6.
pose proof (Rabs_triang_inv t (e - a)) as T7.
assert (T8 : Rabs (e - a) <= Rabs (s - Y) + Rabs a).
{ replace (e - a) with (- ((s - Y) + a)) by lra. rewrite Rabs_Ropp. apply Rabs_triang. }
pose proof (Rabs_le_inv _ _ Hm) as Lm.
pose proof (Rabs_le_inv _ _ Ha) as La.
pose proof (Rabs_le_inv _ _ Ht) as Lt.
pose proof (Rabs_le_inv _ _ Hnd) as Ld.
cbn [bpow radix_val radix2 Z.opp] in *.
split.
- (* [ρ - (s + t) = (e - a - t) + (a - (pl + m)) + (m - n U4) - nd] *)
  apply Rabs_le. lra.
- lra.
Qed.

Theorem fast_band_reduce_correct :
  forall x n rh rl rr,
  DyadicTrig.fast_reduce x = Some (n, rh, rl, rr) -> Z.land n 2047 = 0%Z -> n <> 0%Z ->
  let '(sh, sl, sr) := DyadicTrig.fast_band_reduce false n rh rl in
  is_finite sh = true /\ is_finite sl = true /\ is_finite sr = true /\ sr = add sh sl /\
  bpow radix2 (-61) <= Rabs (B2R x - IZR n * (PI / 4096)) <=
    PI / 8192 * (1 + bpow radix2 (-24)) /\
  Rabs (B2R x - IZR n * (PI / 4096) - (B2R sh + B2R sl)) <=
    bpow radix2 (-74) * Rabs (B2R x - IZR n * (PI / 4096)) /\
  Rabs (B2R sl) <= bpow radix2 (-24) * Rabs (B2R sh).
Proof.
intros x n rh rl rr H Hl Hn0.
destruct (band_dist_small x n rh rl rr H Hl Hn0) as [D1 D2].
destruct (fast_reduce_correct x n rh rl rr H)
  as (_ & _ & _ & Frh & Frl & Frr & Err & HRY & _ & Hrl & _).
destruct (band_setup x n rh rl rr H) as (kf & Fkf & Ekf & Hn & Erl & Erh).
destruct band_consts as (F4 & H4 & Hd).
destruct (band_p kf n Fkf Ekf Hn) as (Fp & Ep & _).
assert (F3 : is_finite (from_bits DyadicTrig.U3) = true) by reflexivity.
(* [pl = n U3 - RN(n U3)] exactly (Dekker) *)
destruct (two_prod_err_correct false kf (from_bits DyadicTrig.U3) Fkf F3
  (band_exact false kf n Fkf Ekf Hn Hn0)) as (_ & _ & _ & Fpl & Epl).
assert (Eo : opp rl = mul kf (from_bits DyadicTrig.U3))
  by (rewrite Erl; unfold opp; apply Bopp_involutive).
assert (Erl' : B2R rl = - B2R (mul kf (from_bits DyadicTrig.U3)))
  by (rewrite Erl; unfold opp; apply B2R_Bopp).
assert (Frr' : is_finite (add rh rl) = true) by (rewrite <- Err; exact Frr).
(* [|n U4| <= 2^-93] and [|n (π/4096 - ΣU)| <= 2^-147], for [|n| < 2^27] *)
assert (HnR : Rabs (IZR n) <= 85445659) by (rewrite <- abs_IZR; apply IZR_le; exact Hn).
assert (Hnu4 : Rabs (IZR n * B2R (from_bits DyadicTrig.U4)) <= bpow radix2 (-93)).
{ rewrite Rabs_mult.
  apply Rle_trans with (85445659 * bpow radix2 (-120)).
  - apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact HnR | exact H4].
  - cbn [bpow radix_val radix2 Z.opp]. lra. }
assert (Hnd : Rabs (IZR n * (PI / 4096 - (B2R (from_bits DyadicTrig.U1) +
    B2R (from_bits DyadicTrig.U2) + B2R (from_bits DyadicTrig.U3) +
    B2R (from_bits DyadicTrig.U4)))) <= bpow radix2 (-147)).
{ rewrite Rabs_mult.
  apply Rle_trans with (85445659 * bpow radix2 (-174)).
  - apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact HnR | exact Hd].
  - cbn [bpow radix_val radix2 Z.opp]. lra. }
assert (Hpl : Rabs (B2R (Generic.two_prod_err false kf (from_bits DyadicTrig.U3)
    (mul kf (from_bits DyadicTrig.U3)))) <= bpow radix2 (-91)).
{ rewrite Epl, Ekf, Rabs_minus_sym. exact Ep. }
(* [Y = rh + rl] is within [2^-90] of ρ, so below 1. *)
assert (HY : Rabs (B2R rh + B2R rl) <= 1).
{ pose proof (Rabs_triang_inv (B2R rh + B2R rl) (B2R x - IZR n * (PI / 4096))) as T.
  rewrite (Rabs_minus_sym (B2R rh + B2R rl)) in T. pose proof PI_4.
  cbn [bpow radix_val radix2 Z.opp] in *. lra. }
assert (Brh : Rabs (B2R rh) < bpow radix2 1023).
{ apply Rle_lt_trans with 2.
  - replace (B2R rh) with ((B2R rh + B2R rl) + - B2R rl) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_Ropp.
    cbn [bpow radix_val radix2 Z.opp] in *. lra.
  - change 2 with (bpow radix2 1). apply bpow_lt. lia. }
assert (Brl : Rabs (B2R rl) < bpow radix2 1023)
  by (eapply Rle_lt_trans; [exact Hrl | apply bpow_lt; lia]).
destruct (add_e rh rl Frh Frl ltac:(lra)) as (_ & _ & HsY).
unfold DyadicTrig.fast_band_reduce.
rewrite (band_of_i64 kf n Fkf Ekf Hn Hn0), Eo.
cbv zeta.
(* [s + e = rh + rl] exactly (TwoSum) *)
generalize (FastRoundErr.two_sum_correct rh rl Frh Frl Brh Brl Frr').
destruct (Fast.two_sum rh rl) as (s, e).
intros TS. cbv beta iota in TS. destruct TS as (Es & Fe & Ee).
cbv beta iota.
rewrite <- Es in HsY.
assert (Fs : is_finite s = true) by (rewrite Es; exact Frr').
set (p := mul kf (from_bits DyadicTrig.U3)) in *.
set (pl := Generic.two_prod_err false kf (from_bits DyadicTrig.U3) p) in *.
(* [m = RN(n U4)] *)
assert (Pm : Rabs (B2R kf * B2R (from_bits DyadicTrig.U4)) <= 16).
{ rewrite Ekf. cbn [bpow radix_val radix2 Z.opp] in Hnu4. lra. }
destruct (mul_e kf (from_bits DyadicTrig.U4) Fkf F4 Pm) as (Fm & _ & Hm).
rewrite Ekf in Hm.
set (m := mul kf (from_bits DyadicTrig.U4)) in *.
pose proof (abs_le_near _ _ _ Hm) as Bm.
pose proof (Rabs_triang (B2R pl) (B2R m)) as Tplm.
(* [a = RN(pl + m)] *)
assert (Pa : Rabs (B2R pl + B2R m) <= 16).
{ cbn [bpow radix_val radix2 Z.opp] in *. lra. }
destruct (add_e pl m Fpl Fm Pa) as (Fa & _ & Ha).
set (a := add pl m) in *.
pose proof (abs_le_near _ _ _ Ha) as Ba.
(* [|e| = |s - (rh + rl)|] *)
assert (He : Rabs (B2R e) <= bpow radix2 (-53) * Rabs (B2R rh + B2R rl) +
    bpow radix2 (-1075)) by (rewrite Ee, Rabs_minus_sym; exact HsY).
pose proof (Rabs_sub_le (B2R e) (B2R a)) as Tea.
(* [t = RN(e - a)] *)
assert (Pt : Rabs (B2R e - B2R a) <= 16).
{ cbn [bpow radix_val radix2 Z.opp] in *. lra. }
destruct (sub_e e a Fe Fa Pt) as (Ft & _ & Ht).
set (t := sub e a) in *.
(* [sr = RN(s + t)] is finite. *)
assert (Ps : Rabs (B2R s + B2R t) <= 16).
{ pose proof (Rabs_triang (B2R s) (B2R t)).
  pose proof (abs_le_near _ _ _ HsY). pose proof (abs_le_near _ _ _ Ht).
  cbn [bpow radix_val radix2 Z.opp] in *. lra. }
destruct (add_e s t Fs Ft Ps) as (Fsr & _ & _).
(* [ρ = (rh + rl) - pl - n U4 - n (π/4096 - ΣU)] *)
assert (E1 : B2R x - IZR n * (PI / 4096) =
  B2R rh + B2R rl - B2R pl - IZR n * B2R (from_bits DyadicTrig.U4) -
  IZR n * (PI / 4096 - (B2R (from_bits DyadicTrig.U1) + B2R (from_bits DyadicTrig.U2) +
    B2R (from_bits DyadicTrig.U3) + B2R (from_bits DyadicTrig.U4)))).
{ rewrite Erh, Erl', Epl, Ekf. ring. }
assert (E2 : B2R s + B2R e = B2R rh + B2R rl) by (rewrite Ee; ring).
destruct (band_budget _ _ _ _ _ _ _ _ _ _ E1 E2 HRY D1 HsY Hpl Hnu4 Hnd Hm Ha Ht)
  as [B1 B2].
split; [exact Fs|]. split; [exact Ft|]. split; [exact Fsr|]. split; [reflexivity|].
split; [split; [exact D1 | exact D2]|]. split; [exact B1 | exact B2].
Qed.

Theorem fast_band_reduce_fma :
  forall x n rh rl rr, DyadicTrig.fast_reduce x = Some (n, rh, rl, rr) ->
  DyadicTrig.fast_band_reduce true n rh rl = DyadicTrig.fast_band_reduce false n rh rl.
Proof.
intros x n rh rl rr H.
destruct (band_setup x n rh rl rr H) as (kf & Fkf & Ekf & Hn & Erl & _).
assert (Eo : opp rl = mul kf (from_bits DyadicTrig.U3))
  by (rewrite Erl; unfold opp; apply Bopp_involutive).
(* Only the error of [RN(n U3)] can differ. *)
assert (E : Generic.two_prod_err true (DyadicTrig.of_i64 n) (from_bits DyadicTrig.U3) (opp rl) =
            Generic.two_prod_err false (DyadicTrig.of_i64 n) (from_bits DyadicTrig.U3) (opp rl)).
{ rewrite Eo. destruct (Z.eq_dec n 0) as [Z0|Z0].
  - (* [n = 0]: [kf] is a zero, and both errors are [+0]. *)
    subst n. destruct kf as [s|s| |s m e B]; try discriminate Fkf.
    + destruct s; vm_compute; reflexivity.
    + exfalso. revert Ekf. cbn [B2R]. apply F2R_neq_0. cbn [Fnum].
      intros C. destruct s; discriminate C.
  - (* Otherwise the error is exact, and the same float either way. *)
    rewrite (band_of_i64 kf n Fkf Ekf Hn Z0).
    apply two_prod_err_fma_eq; [exact Fkf | reflexivity | |];
      apply (band_exact _ kf n Fkf Ekf Hn Z0). }
unfold DyadicTrig.fast_band_reduce. cbv zeta. rewrite E. reflexivity.
Qed.
