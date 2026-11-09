(** * The reduction of sin, cos and tan keeps the sign of its argument

    [reduce n t] of [DyadicTrig] in [Model.v], for a finite [t > 0],
    returns an enclosure of [ρ] whose lower bound is above 0
    ([reduce_pos]), and for [t >= 0] one in [[0, 4/5]] ([reduce_le]).
    Where [reduce] rounds the quotient up ([2 R > P] in [DyTrigReduce.v]),
    [ρ] is at least [2^-(s+1)] by construction. Where it keeps the
    quotient [k >= 1], [ρ = t - k π/2] is at least 2^-61 by
    [km_distance] of [KahanMcDonald.v], as it is above [-k 2^-(s+1)],
    which is far smaller than 2^-61 in magnitude at every level, and the
    roundings of the enclosure at [n] limbs lose less than that. The upper
    bound is [π/4] and a rounding, or [t <= 201/256] itself. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Knuth Elementary DyRound DyConv DyOps DyDriver DyGrow
  DyConst DyExpCore DyExp DyExpRules DyConstPi DyAtanCore DyTrigReduce KahanMcDonald.

Open Scope Z_scope.

(** ** Helpers *)

(** [3.14 < π < 3.15], from the top limb of [PI] ([PI_top] at [l = 1]). *)
Lemma ts_PI : (314 / 100 < PI < 315 / 100)%R.
Proof.
destruct (PI_top 1 ltac:(lia)) as [H1 H2].
let v := eval vm_compute in (Limbs.val (skipn (66 - 1) DyadicConsts.PI)) in
change (Limbs.val (skipn (66 - 1) DyadicConsts.PI)) with v in H1, H2.
change (1 - 64 * Z.of_nat 1) with (-63) in H1, H2.
cbn [bpow radix_val radix2] in H1, H2. lra.
Qed.

(** A rounding at [n] limbs of an [r] in [[-1, 1]] moves it by at most
    [2^-63], as [dprec n >= 64]. *)
Lemma ts_round_abs :
  forall n r, level_ok n -> (Rabs r <= 1)%R ->
  (r - bpow radix2 (-63) <= dround n false r)%R /\ (dround n true r <= r + bpow radix2 (-63))%R.
Proof.
intros n r Hn Hr.
pose proof (dround_width n r Hn) as W. pose proof (dround_bounds n r Hn) as B.
pose proof (dprec_bounds n Hn) as Hp.
assert (E : (bpow radix2 (1 - dprec n) <= bpow radix2 (-63))%R) by (apply bpow_le; lia).
assert (F : (Rabs r * bpow radix2 (1 - dprec n) <= 1 * bpow radix2 (-63))%R).
{ apply Rmult_le_compat; [apply Rabs_pos | apply bpow_ge_0 | exact Hr | exact E]. }
lra.
Qed.

(** A rounding at [n] limbs of an [r >= 0] stays in [[r / 2, 2 r]]: its
    relative error is at most [2^(1 - 64 n) <= 1/2]. *)
Lemma ts_round_rel :
  forall n r, level_ok n -> (0 <= r)%R ->
  (r / 2 <= dround n false r)%R /\ (dround n true r <= 2 * r)%R.
Proof.
intros n r Hn Hr.
pose proof (dround_width n r Hn) as W. pose proof (dround_bounds n r Hn) as B.
pose proof (dprec_bounds n Hn) as Hp.
rewrite Rabs_pos_eq in W by exact Hr.
assert (E : (bpow radix2 (1 - dprec n) <= bpow radix2 (-1))%R) by (apply bpow_le; lia).
change (bpow radix2 (-1)) with (/ 2)%R in E.
assert (F : (r * bpow radix2 (1 - dprec n) <= r * / 2)%R) by (apply Rmult_le_compat_l; lra).
lra.
Qed.

(** Both lemmas of this file: the lower bound of the enclosure of [ρ] is
    not negative for [t >= 0] and positive for [t > 0], and its upper
    bound is at most 4/5. The steps up to [ρ] are those of
    [reduce_correct] in [DyTrigReduce.v]. *)
Lemma reduce_bounds :
  forall n t quad neg r,
  level_ok n -> is_finite t = true -> (0 <= B2R t)%R ->
  DyadicTrig.reduce n t = Some (quad, neg, r) ->
  (0 <= lo_R r)%R /\ (hi_R r <= 4 / 5)%R /\ ((0 < B2R t)%R -> (0 < lo_R r)%R).
Proof.
intros n t quad neg r Hn Ft Ht0 H.
pose proof (dprec_bounds n Hn) as Hp.
destruct no_reduce_R as [Fnr Vnr].
unfold DyadicTrig.reduce in H.
lazymatch type of H with
| ((if ?E then _ else _) = _) => destruct E eqn:Hle
end.
- (* [t <= 201/256]: [ρ = t] is a point. *)
  destruct (Dyadic.encl_point n t) as [c |] eqn:Ec; [| discriminate H].
  cbv beta iota in H. injection H as Hq Hng Hr. subst quad neg r.
  destruct (point_step n t c Hn Ec) as (_ & _ & Hlo & Hhi & _).
  assert (Ht1 : (B2R t <= 201 / 256)%R).
  { unfold Model.le in Hle. rewrite Bleb_correct in Hle by assumption.
    destruct (Rle_bool_spec (B2R t) (B2R DyadicTrig.no_reduce)); [lra | discriminate Hle]. }
  rewrite Hlo, Hhi. split; [lra |]. split; [lra |]. intro. lra.
- pose proof (ac_not_le t DyadicTrig.no_reduce Ft Fnr Hle) as Hgt. rewrite Vnr in Hgt.
  assert (H1 : level_ok 1) by (unfold level_ok; lia).
  destruct (Dyadic.from_f64 1 t) as [d |] eqn:Ed; [| discriminate H].
  destruct (from_f64_step 1 t d H1 Ed) as (Hd & Hde & Hdv & _).
  destruct Hd as (Hm & Hml & _ & _).
  pose proof (val_bounds _ Hm) as Hmb. rewrite Hml in Hmb.
  change (64 * Z.of_nat 1) with 64 in Hmb.
  (* [t > 0], so [d] is positive: [t = m 2^exp] with [m < 2^64]. *)
  assert (HdR : B2R t = (IZR (Limbs.val (Dyadic.dy_m d)) * bpow radix2 (Dyadic.dy_exp d))%R).
  { assert (0 <= IZR (Limbs.val (Dyadic.dy_m d)) * bpow radix2 (Dyadic.dy_exp d))%R
      by (apply Rmult_le_pos; [apply IZR_le; lia | apply bpow_ge_0]).
    rewrite <- Hdv. unfold Dyadic.dy_R in Hdv |- *. cbv zeta in Hdv |- *.
    destruct (Dyadic.dy_neg d); lra. }
  (* [t > 1/2], so [exp >= -64], and the shift below is not negative. *)
  assert (Hexp : -64 <= Dyadic.dy_exp d).
  { destruct (Z_lt_le_dec (Dyadic.dy_exp d) (-64)) as [Hlt | Hge]; [exfalso | exact Hge].
    assert (A : (IZR (Limbs.val (Dyadic.dy_m d)) < bpow radix2 64)%R)
      by (rewrite <- IZR_pow2 by lia; apply IZR_lt; lia).
    assert (B : (bpow radix2 (Dyadic.dy_exp d) <= bpow radix2 (-65))%R)
      by (apply bpow_le; lia).
    assert (C : (bpow radix2 64 * bpow radix2 (-65) = / 2)%R)
      by (rewrite <- bpow_plus; reflexivity).
    assert (M0 : (0 <= IZR (Limbs.val (Dyadic.dy_m d)))%R) by (apply IZR_le; lia).
    assert (D1 : (IZR (Limbs.val (Dyadic.dy_m d)) * bpow radix2 (Dyadic.dy_exp d) <=
                  IZR (Limbs.val (Dyadic.dy_m d)) * bpow radix2 (-65))%R)
      by (apply Rmult_le_compat_l; lra).
    assert (D2 : (IZR (Limbs.val (Dyadic.dy_m d)) * bpow radix2 (-65) <=
                  bpow radix2 64 * bpow radix2 (-65))%R)
      by (apply Rmult_le_compat_r; [apply bpow_ge_0 | lra]).
    lra. }
  (* [t < 2^(exp + 64)], as [m < 2^64]. *)
  assert (Htb : (B2R t < bpow radix2 (Dyadic.dy_exp d + 64))%R).
  { rewrite HdR, Z.add_comm, bpow_plus.
    apply Rmult_lt_compat_r; [apply bpow_gt_0 |].
    rewrite <- IZR_pow2 by lia. apply IZR_lt. lia. }
  cbv beta iota zeta in H.
  set (b := Z.to_nat (Dyadic.dy_exp d + 64)) in H.
  set (bq := (b / 64)%nat) in H.
  set (l := Nat.min (n + DyadicTrig.guard_limbs + bq) 66) in H.
  set (s := 64 * Z.of_nat l - 2) in H.
  set (nx := (l + 1 + bq)%nat) in H.
  set (p := skipn (66 - l) DyadicConsts.PI) in H.
  set (x := Limbs.shl_into nx (Dyadic.dy_m d) (Dyadic.dy_exp d + s + 1)) in H.
  set (e := - (s + 1)) in H.
  assert (Hb : Z.of_nat b = Dyadic.dy_exp d + 64) by (unfold b; lia).
  assert (Hbq : (64 * bq <= b < 64 * bq + 64)%nat).
  { unfold bq. pose proof (Nat.div_mod_eq b 64).
    pose proof (Nat.mod_upper_bound b 64 ltac:(lia)). lia. }
  assert (Hbq2 : (bq <= 129)%nat) by lia.
  assert (Hl : (3 <= l <= 66)%nat)
    by (unfold l, DyadicTrig.guard_limbs; unfold level_ok in Hn; lia).
  assert (Hlmin : l = Nat.min (n + 2 + bq) 66) by reflexivity.
  assert (Hnx : nx = (l + 1 + bq)%nat) by reflexivity.
  assert (He : e = 1 - 64 * Z.of_nat l) by (unfold e, s; lia).
  assert (Hs : s = 64 * Z.of_nat l - 2) by reflexivity.
  clearbody b bq l s nx e.
  (* [t 2^e < 2^-128]: [t < 2^b] with [b + e <= -64 n - 64] below the
     cap of 66 limbs, and [t < 2^1024] with [e = -4223] at it. *)
  assert (Hte : (B2R t * bpow radix2 e < bpow radix2 (-128))%R).
  { assert (A : (B2R t < bpow radix2 (Z.min (Z.of_nat b) 1024))%R).
    { destruct (Z.min_spec (Z.of_nat b) 1024) as [[_ ->] | [_ ->]].
      - rewrite Hb. exact Htb.
      - pose proof (abs_B2R_lt_emax _ _ t) as M. rewrite Rabs_pos_eq in M by lra. exact M. }
    apply Rlt_le_trans with (bpow radix2 (Z.min (Z.of_nat b) 1024) * bpow radix2 e)%R.
    - apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact A].
    - rewrite <- bpow_plus. apply bpow_le. unfold level_ok in Hn. lia. }
  (* The top [l] limbs [P] of [PI]: π/2 in [[P, P + 1) 2^e]. *)
  assert (Hpok : limbs_ok p) by (apply limbs_ok_skipn, PI_ok).
  assert (Hpl : length p = l) by (unfold p; rewrite length_skipn, PI_length; lia).
  destruct (PI_top l ltac:(lia)) as [HP1 HP2].
  change (skipn (66 - l) DyadicConsts.PI) with p in HP1, HP2.
  rewrite <- He in HP1, HP2.
  clearbody p.
  pose proof (bpow_gt_0 radix2 e) as Hbe.
  pose proof (val_nonneg p Hpok) as Hp0.
  assert (Hbe2 : (bpow radix2 e <= bpow radix2 (-128))%R) by (apply bpow_le; lia).
  (* Numbers: [2^-128 <= 2^-63 <= 1/1000] and [2^-61 = 4 2^-63]. *)
  assert (HM : (bpow radix2 (-63) <= / 1000 /\ bpow radix2 (-61) = 4 * bpow radix2 (-63) /\
                0 < bpow radix2 (-128) <= bpow radix2 (-63) /\
                1000 * bpow radix2 (-128) <= bpow radix2 (-63))%R)
    by (cbn [bpow radix_val radix2]; lra).
  pose proof ts_PI as HPI.
  (* [P >= 2], as π/2 > 1 and [2^e <= 1/4]. *)
  assert (Hp2 : 2 <= Limbs.val p).
  { destruct (Z_lt_le_dec (Limbs.val p) 2) as [Hlt | Hge]; [exfalso | exact Hge].
    pose proof PI2_1.
    assert (A : (bpow radix2 e <= bpow radix2 (-2))%R) by (apply bpow_le; lia).
    change (bpow radix2 (-2)) with (/ 4)%R in A.
    assert (B : (IZR (Limbs.val p) <= 1)%R) by (apply IZR_le; lia).
    assert (C : ((IZR (Limbs.val p) + 1) * bpow radix2 e <= 2 * bpow radix2 e)%R)
      by (apply Rmult_le_compat_r; lra).
    lra. }
  (* [X = m 2^(exp + s + 1)]: below [2^(b + 64 l - 1) <= 2^(64 nx)], so
     no bit falls off the top. *)
  assert (Hsh : 0 <= Dyadic.dy_exp d + s + 1) by lia.
  destruct (shl_into_correct nx (Dyadic.dy_m d) (Dyadic.dy_exp d + s + 1) Hm Hsh)
    as (Hxok & Hxl & Hxv).
  change (Limbs.shl_into nx (Dyadic.dy_m d) (Dyadic.dy_exp d + s + 1)) with x in Hxok, Hxl, Hxv.
  assert (Hxv' : Limbs.val x = Limbs.val (Dyadic.dy_m d) * 2 ^ (Dyadic.dy_exp d + s + 1)).
  { rewrite Hxv. apply Z.mod_small. split.
    - apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia].
    - apply Z.lt_le_trans with (2 ^ 64 * 2 ^ (Dyadic.dy_exp d + s + 1)).
      + apply Z.mul_lt_mono_pos_r; first [lia | apply Z.pow_pos_nonneg; lia].
      + rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
  clearbody x.
  assert (HtX : B2R t = (IZR (Limbs.val x) * bpow radix2 e)%R).
  { rewrite HdR, Hxv', mult_IZR, IZR_pow2 by lia. rewrite Rmult_assoc, <- bpow_plus.
    f_equal. f_equal. lia. }
  pose proof (val_bounds _ Hxok) as Hxb. rewrite Hxl in Hxb.
  assert (Hx2 : 2 ^ 1 <= 2 ^ (64 * Z.of_nat nx)) by (apply Z.pow_le_mono_r; lia).
  (* [X = q P + R] *)
  destruct (div_rem_correct x p Hxok Hpok ltac:(lia))
    as (q & R & Edr & Hqok & HRok & Hql & HRl & Hqv & HRv).
  rewrite Edr in H. cbv beta iota in H.
  pose proof (Z.mod_pos_bound (Limbs.val x) (Limbs.val p) ltac:(lia)) as HRm.
  rewrite <- HRv in HRm.
  pose proof (Z.div_mod (Limbs.val x) (Limbs.val p) ltac:(lia)) as Hdm.
  rewrite <- Hqv, <- HRv in Hdm.
  pose proof (val_nonneg q Hqok) as Hq0.
  (* [q 2^e <= 2 t 2^e < 2^-127]: [q P 2^e <= t] with [P 2^e > π/2 - 2^e >= 1/2]. *)
  assert (Hqe : (IZR (Limbs.val q) * bpow radix2 e <= 2 * (B2R t * bpow radix2 e))%R).
  { assert (A : (IZR (Limbs.val q) * (IZR (Limbs.val p) * bpow radix2 e) <= B2R t)%R).
    { rewrite HtX, Hdm, plus_IZR, mult_IZR.
      assert (0 <= IZR (Limbs.val R) * bpow radix2 e)%R
        by (apply Rmult_le_pos; [apply IZR_le; lia | lra]).
      lra. }
    assert (B : (/ 2 <= IZR (Limbs.val p) * bpow radix2 e)%R) by lra.
    assert (Q0 : (0 <= IZR (Limbs.val q))%R) by (apply IZR_le; lia).
    assert (C : (IZR (Limbs.val q) * / 2 <= IZR (Limbs.val q) * (IZR (Limbs.val p) * bpow radix2 e))%R)
      by (apply Rmult_le_compat_l; lra).
    assert (D : (IZR (Limbs.val q) <= 2 * B2R t)%R) by lra.
    apply Rmult_le_compat_r with (r := bpow radix2 e) in D; [| lra]. lra. }
  (* [c = P - R], without a borrow, as [R < P]. *)
  destruct (Limbs.sub_assign p R false) as [c cb] eqn:Esub. cbn [fst] in H.
  destruct (sub_assign_correct p R false c cb Hpok HRok ltac:(lia) Esub) as (Hcok & Hcl & Hcv).
  pose proof (val_bounds _ Hcok) as Hcb. rewrite Hcl, Hpl in Hcb.
  pose proof (val_bounds _ HRok) as HRb. rewrite HRl, Hpl in HRb.
  pose proof (val_bounds _ Hpok) as Hpb. rewrite Hpl in Hpb.
  assert (Hcv' : Limbs.val c = Limbs.val p - Limbs.val R).
  { rewrite Hpl in Hcv. destruct cb; cbn [Z.b2z] in Hcv; lia. }
  (* [up] iff [R > P - R] *)
  rewrite (Inari.Limbs.cmp_correct R c HRok Hcok) in H.
  set (up := match Limbs.val R ?= Limbs.val c with Gt => true | _ => false end) in H.
  assert (Hup : up = true <-> Limbs.val c < Limbs.val R).
  { unfold up. destruct (Z.compare_spec (Limbs.val R) (Limbs.val c)); split; intro;
      first [reflexivity | discriminate | lia | (exfalso; lia)]. }
  clearbody up.
  assert (Hup2 : if up then Limbs.val c < Limbs.val R else Limbs.val R <= Limbs.val c).
  { destruct up; [apply Hup; reflexivity |].
    destruct (Z_lt_le_dec (Limbs.val c) (Limbs.val R)) as [X | X];
      [apply Hup in X; discriminate X | exact X]. }
  (* [q' = q + 1] if [up], without a carry, as [2 q <= X < 2^(64 nx)]. *)
  set (q' := if up then fst (Limbs.add_assign q (1 :: nil)) else q) in H.
  assert (Hq' : limbs_ok q' /\ length q' = nx /\
                Limbs.val q' = Limbs.val q + (if up then 1 else 0)).
  { unfold q'. destruct up; cbv beta iota.
    - destruct (Limbs.add_assign q (1 :: nil)) as [q1 cq] eqn:Eadd. cbn [fst].
      assert (H1ok : limbs_ok (1 :: nil))
        by (apply limbs_ok_cons; split; [lia | constructor]).
      destruct (add_assign_correct q (1 :: nil) q1 cq Hqok H1ok ltac:(cbn [length]; lia) Eadd)
        as (Hq1ok & Hq1l & Hq1v).
      cbn [Limbs.val] in Hq1v. rewrite Hql, Hxl in Hq1v.
      pose proof (val_bounds _ Hq1ok) as Hq1b. rewrite Hq1l, Hql, Hxl in Hq1b.
      assert (A : 2 * Limbs.val q <= Limbs.val p * Limbs.val q)
        by (apply Z.mul_le_mono_nonneg_r; lia).
      split; [exact Hq1ok |]. split; [lia |].
      destruct cq; cbn [Z.b2z] in Hq1v; lia.
    - split; [exact Hqok |]. split; lia. }
  set (center := if up then c else R) in H.
  assert (Hcen : limbs_ok center /\ Limbs.val center < 2 ^ (64 * Z.of_nat l) /\
                 Limbs.val center = (if up then Limbs.val c else Limbs.val R)).
  { unfold center. destruct up; cbv beta iota; repeat split; first [assumption | lia]. }
  clearbody q' center.
  destruct Hq' as (Hq'ok & Hq'l & Hq'v). destruct Hcen as (Hcenok & Hcenb & Hcenv).
  pose proof (val_bounds _ Hq'ok) as Hq'b. rewrite Hq'l in Hq'b.
  pose proof (val_nonneg q' Hq'ok) as Hq'0. pose proof (val_nonneg center Hcenok) as Hcen0.
  (* The three roundings, of [q' 2^e] up and of [center 2^e] both ways. *)
  destruct (Dyadic.round n false q' e false true) as [K |] eqn:EK; [| discriminate H].
  cbv beta iota in H.
  destruct (round_int n q' e (64 * Z.of_nat nx) true K Hn Hq'ok ltac:(lia) ltac:(lia) (proj2 Hq'b) EK)
    as (HKok & HKv).
  assert (HKe : - 2 ^ 14 <= Dyadic.dy_exp K <= 2 ^ 14).
  { apply (grow_exp_of_win n K true _ e (64 * Z.of_nat nx + e) (2 ^ 14) Hn HKok HKv);
      [apply int_win; lia | lia | lia | lia]. }
  destruct (Dyadic.round n false center e false false) as [lo |] eqn:Elo; [| discriminate H].
  cbv beta iota in H.
  destruct (round_int n center e (64 * Z.of_nat l) false lo Hn Hcenok ltac:(lia) ltac:(lia)
              Hcenb Elo) as (Hlook & Hlov).
  assert (Hloe : - 2 ^ 14 <= Dyadic.dy_exp lo <= 2 ^ 14).
  { apply (grow_exp_of_win n lo false _ e (64 * Z.of_nat l + e) (2 ^ 14) Hn Hlook Hlov);
      [apply int_win; lia | lia | lia | lia]. }
  destruct (Dyadic.round n false center e false true) as [hi |] eqn:Ehi; [| discriminate H].
  cbv beta iota in H.
  destruct (round_int n center e (64 * Z.of_nat l) true hi Hn Hcenok ltac:(lia) ltac:(lia)
              Hcenb Ehi) as (Hhiok & Hhiv).
  assert (Hhie : - 2 ^ 14 <= Dyadic.dy_exp hi <= 2 ^ 14).
  { apply (grow_exp_of_win n hi true _ e (64 * Z.of_nat l + e) (2 ^ 14) Hn Hhiok Hhiv);
      [apply int_win; lia | lia | lia | lia]. }
  (* [w] is [center 2^e] rounded both ways, and [kd = [0, K]] with [K]
     the rounding up of [q' 2^e]. *)
  set (x0 := (IZR (Limbs.val center) * bpow radix2 e)%R) in *.
  set (kr := (IZR (Limbs.val q') * bpow radix2 e)%R) in *.
  set (w := {| Dyadic.en_lo := lo; Dyadic.en_hi := hi |}) in H.
  set (kd := {| Dyadic.en_lo := Dyadic.dy_zero n; Dyadic.en_hi := K |}) in H.
  destruct (dy_zero_ok n) as (Hz & HzR & _).
  assert (Hw : encl_ok n w /\ encl_small w /\
               lo_R w = dround n false x0 /\ hi_R w = dround n true x0).
  { pose proof (dround_bounds n x0 Hn).
    unfold w, encl_ok, encl_small, exp_small, lo_R, hi_R; cbn [Dyadic.en_lo Dyadic.en_hi].
    rewrite Hlov, Hhiv. split; [split; [exact Hlook | split; [exact Hhiok | lra]] |].
    split; [split; lia | split; reflexivity]. }
  assert (Hkd : encl_ok n kd /\ encl_small kd /\ lo_R kd = 0%R /\ hi_R kd = dround n true kr).
  { pose proof (dround_bounds n kr Hn).
    assert (0 <= kr)%R by (unfold kr; apply Rmult_le_pos; [apply IZR_le; lia | lra]).
    unfold kd, encl_ok, encl_small, exp_small, lo_R, hi_R; cbn [Dyadic.en_lo Dyadic.en_hi].
    rewrite HzR, HKv. split; [split; [exact Hz | split; [exact HKok | lra]] |].
    split; [cbn [Dyadic.dy_zero Dyadic.dy_exp]; split; lia | split; reflexivity]. }
  destruct Hw as (Hwok & Hws & Hwlo & Hwhi). destruct Hkd as (Hkdok & Hkds & Hkdlo & Hkdhi).
  (* [ρ = w + kd] if [up], and [w - kd] otherwise. *)
  lazymatch type of H with
  | (match ?E with Some _ => _ | None => _ end = _) => destruct E as [rho |] eqn:Erho
  end; [| discriminate H].
  assert (Hrho :
    lo_R rho = (if up then dround n false (lo_R w + lo_R kd)
                else dround n false (lo_R w - hi_R kd)) /\
    hi_R rho = (if up then dround n true (hi_R w + hi_R kd)
                else dround n true (hi_R w - lo_R kd))).
  { destruct up.
    - destruct (encl_add_correct n w kd Hn Hwok Hkdok Hws Hkds) as (c' & E' & _ & Vlo & Vhi & _).
      rewrite Erho in E'. injection E' as <-. split; assumption.
    - destruct (encl_sub_correct n w kd Hn Hwok Hkdok Hws Hkds) as (c' & E' & _ & Vlo & Vhi & _).
      rewrite Erho in E'. injection E' as <-. split; assumption. }
  clear Erho.
  cbv beta iota in H.
  (* The two tests of the [assert!] leave [ρ] as it is. *)
  destruct (Dyadic.from_f64 n DyadicExp.m_one) as [m1 |] eqn:Em1; [| discriminate H].
  cbv beta iota in H.
  destruct (DyadicExp.dy_lt n (Dyadic.en_lo rho) m1) eqn:Elt; [discriminate H |].
  cbv beta iota in H.
  destruct (Dyadic.from_f64 n DyadicExp.one) as [p1 |] eqn:Ep1; [| discriminate H].
  cbv beta iota in H.
  destruct (DyadicExp.dy_gt n (Dyadic.en_hi rho) p1) eqn:Egt; [discriminate H |].
  cbv beta iota in H.
  injection H as Hq Hng Hr. subst quad neg r.
  destruct Hrho as [Hrlo Hrhi].
  rewrite Hkdlo, Hkdhi, Hwlo in Hrlo. rewrite Hkdlo, Hkdhi, Hwhi in Hrhi.
  (* [x0 <= P 2^e / 2 <= π/4]: [center] is the smaller of [R] and [P - R]. *)
  assert (Hx0 : (0 <= x0 <= PI / 4)%R).
  { assert (A : (2 * IZR (Limbs.val center) <= IZR (Limbs.val p))%R).
    { rewrite <- mult_IZR. apply IZR_le. rewrite Hcenv.
      destruct up; cbv beta iota in Hup2 |- *; lia. }
    assert (B : (2 * x0 <= IZR (Limbs.val p) * bpow radix2 e)%R).
    { unfold x0. rewrite <- Rmult_assoc. apply Rmult_le_compat_r; lra. }
    assert (0 <= x0)%R by (unfold x0; apply Rmult_le_pos; [apply IZR_le; lia | lra]).
    lra. }
  assert (Hx01 : (Rabs x0 <= 1)%R) by (rewrite Rabs_pos_eq; lra).
  assert (Hkr : (0 <= kr <= 3 * bpow radix2 (-128))%R).
  { unfold kr. rewrite Hq'v, plus_IZR.
    assert (0 <= IZR (if up then 1 else 0) <= 1)%R by (destruct up; cbv beta iota; lra).
    assert (A : (IZR (if up then 1 else 0) * bpow radix2 e <= 1 * bpow radix2 e)%R)
      by (apply Rmult_le_compat_r; lra).
    assert (0 <= IZR (Limbs.val q) * bpow radix2 e)%R
      by (apply Rmult_le_pos; [apply IZR_le; lia | lra]).
    assert (0 <= IZR (if up then 1 else 0) * bpow radix2 e)%R by (apply Rmult_le_pos; lra).
    rewrite Rmult_plus_distr_r. lra. }
  destruct (ts_round_abs n x0 Hn Hx01) as [Rx0lo Rx0hi].
  destruct (ts_round_rel n x0 Hn (proj1 Hx0)) as [Rx0lo' _].
  destruct (ts_round_rel n kr Hn (proj1 Hkr)) as [_ Rkrhi].
  pose proof (dround_bounds n x0 Hn) as Bx0. pose proof (dround_bounds n kr Hn) as Bkr.
  assert (Hlo : (0 < lo_R rho)%R).
  { rewrite Hrlo. destruct up.
    - (* [up]: [lo = RD(RD(c 2^e) + 0)] with [c >= 1]. *)
      assert (A : (bpow radix2 e <= x0)%R).
      { unfold x0. rewrite Hcenv. pose proof (proj1 Hup eq_refl) as Hcr.
        assert (1 <= IZR (Limbs.val c))%R by (apply IZR_le; lia).
        replace (bpow radix2 e) with (1 * bpow radix2 e)%R at 1 by ring.
        apply Rmult_le_compat_r; lra. }
      assert (B : (0 <= dround n false x0 + 0)%R) by lra.
      destruct (ts_round_rel n _ Hn B) as [C _]. lra.
    - (* not [up]: [q' = q] and [center = R], so [ρ = x0 - q δ = t - q π/2]
         with [δ = π/2 - P 2^e] in [[0, 2^e]]. It is [t >= 201/256] if [q =
         0], and at least 2^-61 by [km_distance] otherwise, as [q δ <= q 2^e
         < 2^-61]. The roundings lose at most [2^-63 + 2 kr]. *)
      set (delta := (PI / 2 - IZR (Limbs.val p) * bpow radix2 e)%R).
      assert (Hdl : (0 <= delta <= bpow radix2 e)%R) by (unfold delta; lra).
      assert (Hy0 : (0 <= IZR (Limbs.val q) * delta <= IZR (Limbs.val q) * bpow radix2 e)%R).
      { assert (0 <= IZR (Limbs.val q))%R by (apply IZR_le; lia).
        split; [apply Rmult_le_pos; lra | apply Rmult_le_compat_l; lra]. }
      assert (Hrt : (B2R t - IZR (Limbs.val q) * (PI / 2) = x0 - IZR (Limbs.val q) * delta)%R).
      { unfold x0, delta. rewrite HtX, Hdm, Hcenv. rewrite plus_IZR, mult_IZR. ring. }
      assert (Hkm : (bpow radix2 (-61) <= x0 - IZR (Limbs.val q) * delta)%R).
      { destruct (Z.eq_dec (Limbs.val q) 0) as [Hq00 | Hq00].
        - rewrite <- Hrt, Hq00, Rmult_0_l, Rminus_0_r. lra.
        - pose proof (km_distance t (Limbs.val q) Ft Hq00) as HKd. rewrite Hrt in HKd.
          destruct (Rcase_abs (x0 - IZR (Limbs.val q) * delta)) as [N | P].
          + rewrite Rabs_left in HKd by exact N. lra.
          + rewrite Rabs_right in HKd by exact P. exact HKd. }
      assert (Hkq : kr = (IZR (Limbs.val q) * bpow radix2 e)%R)
        by (unfold kr; rewrite Hq'v, Z.add_0_r; reflexivity).
      assert (B : (0 <= dround n false x0 - dround n true kr)%R)  by lra.
      destruct (ts_round_rel n _ Hn B) as [C _]. lra. }
  split; [lra |]. split; [| intro; exact Hlo].
  (* [hi <= π/4 + 2^-63 + 6 2^-128 + 2^-63 < 4/5] *)
  rewrite Hrhi. destruct up.
  + assert (A : (Rabs (dround n true x0 + dround n true kr) <= 1)%R) by (rewrite Rabs_pos_eq; lra).
    destruct (ts_round_abs n _ Hn A) as [_ B]. lra.
  + rewrite Rminus_0_r.
    assert (A : (Rabs (dround n true x0) <= 1)%R) by (rewrite Rabs_pos_eq; lra).
    destruct (ts_round_abs n _ Hn A) as [_ B]. lra.
Qed.

Lemma reduce_pos :
  forall n t quad up r,
  level_ok n -> is_finite t = true -> (0 < B2R t)%R ->
  DyadicTrig.reduce n t = Some (quad, up, r) -> (0 < lo_R r)%R.
Proof.
intros n t quad up r Hn Ft Ht H.
apply (reduce_bounds n t quad up r Hn Ft ltac:(lra) H). exact Ht.
Qed.

Lemma reduce_le :
  forall n t quad up r,
  level_ok n -> is_finite t = true -> (0 <= B2R t)%R ->
  DyadicTrig.reduce n t = Some (quad, up, r) -> (0 <= lo_R r)%R /\ (hi_R r <= 4 / 5)%R.
Proof.
intros n t quad up r Hn Ft Ht H.
destruct (reduce_bounds n t quad up r Hn Ft Ht H) as (A & B & _). split; assumption.
Qed.
