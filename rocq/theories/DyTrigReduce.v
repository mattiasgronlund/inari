(** * The reduction of sin, cos and tan by multiples of π/2 in the dyadic kernel

    [reduce n t] of [DyadicTrig] in [Model.v], for a finite [t >= 0],
    returns [t] itself with [k = 0] if [t <= 201/256]. Otherwise it takes
    the top [l] limbs [P] of the table [PI] of [DyadicConsts], so that
    π/2 lies in [[P, P + 1) 2^-(s+1)] with [s = 64 l - 2] ([PI_bounds] of
    [DyConstPi.v]), and divides [X = t 2^(s+1)], an integer, by [P]: [X =
    k P + R] with [0 <= R < P] ([div_rem_correct] of [Knuth.v]). Then [t -
    k π/2 = R 2^-(s+1) - ε] with [ε = k (π/2 - P 2^-(s+1))] in [[0, k
    2^-(s+1)]], whatever the integer [k]; if [2 R > P], it takes [k + 1]
    and [k π/2 - t = (P - R) 2^-(s+1) + ε'] instead. [reduce_correct]
    states the result: [t = k π/2 + ρ], or [t = k π/2 - ρ] if [neg], with
    [ρ] in the returned enclosure, [k mod 4] the returned quadrant, and
    [|ρ| <= 1] from the [assert!]. That [k] is the nearest integer to [t
    / (π/2)] is not needed and not proved. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Knuth Elementary DyRound DyConv DyOps DyDriver DyGrow
  DyConst DyExpCore DyExp DyExpRules DyConstPi DyAtanCore.

Open Scope Z_scope.

(** ** The literals and the table [PI] *)

(** [NO_REDUCE] is 201/256 = 7072058789855232 2^-53. *)
Lemma no_reduce_R :
  is_finite DyadicTrig.no_reduce = true /\ B2R DyadicTrig.no_reduce = (201 / 256)%R.
Proof.
split; [vm_compute; reflexivity |].
rewrite <- SF2R_B2SF.
replace (B2SF DyadicTrig.no_reduce) with (SpecFloat.S754_finite false 7072058789855232 (-53))
  by (vm_compute; reflexivity).
unfold SF2R, F2R. cbn [Fnum Fexp SpecFloat.cond_Zopp].
change (bpow radix2 (-53)) with (/ 9007199254740992)%R.
lra.
Qed.

Lemma m_one_R : B2R DyadicExp.m_one = (-1)%R.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicExp.m_one) with (SpecFloat.S754_finite true 4503599627370496 (-52))
  by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]. unfold F2R; cbn [Fnum Fexp]. rewrite opp_IZR.
change (IZR 4503599627370496) with (bpow radix2 52).
rewrite <- Ropp_mult_distr_l, <- bpow_plus. reflexivity.
Qed.

(** Every entry of [PI] is a [u64], checked by computation. *)
Lemma PI_okb : forallb (fun a => (0 <=? a) && (a <? 2 ^ 64)) DyadicConsts.PI = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma PI_ok : limbs_ok DyadicConsts.PI.
Proof.
unfold limbs_ok. apply Forall_forall. intros a Ha.
pose proof (proj1 (forallb_forall _ _) PI_okb a Ha) as H. cbv beta in H.
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma PI_length : length DyadicConsts.PI = 66%nat.
Proof. reflexivity. Qed.

(** The top [l] limbs [P] of [PI] put π/2 in [[P, P + 1) 2^(1 - 64 l)]:
    [P] is [PI / D] rounded down for [D = 2^(64 (66 - l))], so [P D <=
    PI] and [PI + 1 <= (P + 1) D], and [D 2^-4222 = 2 2^(1 - 64 l)]. *)
Lemma PI_top :
  forall l : nat, (l <= 66)%nat ->
  (IZR (Limbs.val (skipn (66 - l) DyadicConsts.PI)) * bpow radix2 (1 - 64 * Z.of_nat l)
     <= PI / 2 <
   (IZR (Limbs.val (skipn (66 - l) DyadicConsts.PI)) + 1) * bpow radix2 (1 - 64 * Z.of_nat l))%R.
Proof.
intros l Hl.
destruct PI_bounds as [H1 H2].
assert (HD0 : 0 < 2 ^ (64 * Z.of_nat (66 - l))) by (apply Z.pow_pos_nonneg; lia).
rewrite (val_skipn _ _ PI_ok).
pose proof (Z.div_mod (Limbs.val DyadicConsts.PI) (2 ^ (64 * Z.of_nat (66 - l))) ltac:(lia))
  as Hdm.
pose proof (Z.mod_pos_bound (Limbs.val DyadicConsts.PI) (2 ^ (64 * Z.of_nat (66 - l))) HD0)
  as Hmb.
set (D := 2 ^ (64 * Z.of_nat (66 - l))) in *.
set (V := Limbs.val DyadicConsts.PI) in *.
set (P := V / D) in *.
assert (HB : (IZR D * bpow radix2 (-4222) = 2 * bpow radix2 (1 - 64 * Z.of_nat l))%R).
{ unfold D. rewrite IZR_pow2 by lia. rewrite <- bpow_plus.
  replace (64 * Z.of_nat (66 - l) + -4222) with (1 + (1 - 64 * Z.of_nat l)) by lia.
  rewrite bpow_plus. reflexivity. }
pose proof (bpow_gt_0 radix2 (-4222)) as HB0.
split.
- assert (A : (IZR (D * P) <= IZR V)%R) by (apply IZR_le; lia).
  rewrite mult_IZR in A.
  assert (A' : (IZR D * IZR P * bpow radix2 (-4222) <= IZR V * bpow radix2 (-4222))%R)
    by (apply Rmult_le_compat_r; lra).
  replace (IZR D * IZR P * bpow radix2 (-4222))%R
    with (IZR P * (IZR D * bpow radix2 (-4222)))%R in A' by ring.
  rewrite HB in A'. lra.
- assert (A : (IZR (V + 1) <= IZR (D * (P + 1)))%R) by (apply IZR_le; lia).
  rewrite mult_IZR, !plus_IZR in A.
  assert (A' : ((IZR V + 1) * bpow radix2 (-4222) <=
                IZR D * (IZR P + 1) * bpow radix2 (-4222))%R)
    by (apply Rmult_le_compat_r; lra).
  replace (IZR D * (IZR P + 1) * bpow radix2 (-4222))%R
    with ((IZR P + 1) * (IZR D * bpow radix2 (-4222)))%R in A' by ring.
  rewrite HB in A'. lra.
Qed.

(** ** Helpers *)

(** An integer [v] in [[0, 2^B)] times [2^e] is 0 or in [[2^e, 2^(B + e)]]. *)
Lemma int_win :
  forall v e B, 0 <= B -> 0 <= v < 2 ^ B -> grow_win e (B + e) (IZR v * bpow radix2 e).
Proof.
intros v e B HB Hv.
destruct (Z.eq_dec v 0) as [-> | Hv0]; [left; apply Rmult_0_l |].
right. pose proof (bpow_gt_0 radix2 e) as He.
assert (H1 : (1 <= IZR v)%R) by (apply IZR_le; lia).
assert (H2 : (IZR v <= bpow radix2 B)%R) by (rewrite <- IZR_pow2 by lia; apply IZR_le; lia).
rewrite Rabs_pos_eq by (apply Rmult_le_pos; lra).
rewrite bpow_plus. split; [| apply Rmult_le_compat_r; lra].
replace (bpow radix2 e) with (1 * bpow radix2 e)%R at 1 by ring.
apply Rmult_le_compat_r; lra.
Qed.

(** [round] of an integer [x] times [2^e], toward -inf or +inf, for an
    [e] and a bit length far from the ends of [i64]. *)
Lemma round_int :
  forall n x e B up d,
  level_ok n -> limbs_ok x -> 0 <= B <= 2 ^ 14 -> - 2 ^ 14 <= e <= 2 ^ 14 ->
  Limbs.val x < 2 ^ B -> Dyadic.round n false x e false up = Some d ->
  dy_ok n d /\ Dyadic.dy_R d = dround n up (IZR (Limbs.val x) * bpow radix2 e).
Proof.
intros n x e B up d Hn Hx HB He Hv H.
pose proof (dprec_bounds n Hn) as Hp. pose proof (val_nonneg x Hx) as H0.
pose proof (nat_bits_bounds (Limbs.val x) B ltac:(lia) ltac:(lia)) as Hb.
assert (Hc : Limbs.val x = 0 \/
             - 2 ^ 63 <= e + nat_bits (Limbs.val x) - dprec n < 2 ^ 63 - 1) by (right; lia).
destruct (round_correct n false x e false up 0 Hn Hx eq_refl Hc) as (d' & E & Ok & V).
rewrite H in E. injection E as <-. split; [exact Ok |].
rewrite V. cbn [cond_Ropp]. rewrite Rplus_0_r. reflexivity.
Qed.

(** [dy_lt n x y = false] means [y <= x], and [dy_gt n x y = false]
    means [x <= y]. *)
Lemma dy_lt_false :
  forall n x y,
  level_ok n -> dy_ok n x -> dy_ok n y -> DyadicExp.dy_lt n x y = false ->
  (Dyadic.dy_R y <= Dyadic.dy_R x)%R.
Proof.
intros n x y Hn Hx Hy H. unfold DyadicExp.dy_lt in H.
rewrite (Inari.DyRound.cmp_correct n _ _ Hn Hx Hy) in H.
destruct (Rcompare_spec (Dyadic.dy_R x) (Dyadic.dy_R y)); [discriminate H | lra | lra].
Qed.

Lemma dy_gt_false :
  forall n x y,
  level_ok n -> dy_ok n x -> dy_ok n y -> DyadicExp.dy_gt n x y = false ->
  (Dyadic.dy_R x <= Dyadic.dy_R y)%R.
Proof.
intros n x y Hn Hx Hy H. unfold DyadicExp.dy_gt in H.
rewrite (Inari.DyRound.cmp_correct n _ _ Hn Hx Hy) in H.
destruct (Rcompare_spec (Dyadic.dy_R x) (Dyadic.dy_R y)); [lra | lra | discriminate H].
Qed.

(** ** [reduce] *)

Lemma reduce_correct :
  forall n t quad neg r,
  level_ok n -> is_finite t = true -> (0 <= B2R t)%R ->
  DyadicTrig.reduce n t = Some (quad, neg, r) ->
  encl_ok n r /\ encl_le (2 ^ 15) r /\
  exists k rho, k mod 4 = quad /\ encl_has r rho /\ (-1 <= rho <= 1)%R /\
    B2R t = (IZR k * (PI / 2) + (if neg then - rho else rho))%R.
Proof.
intros n t quad neg r Hn Ft Ht0 H.
pose proof (dprec_bounds n Hn) as Hp.
destruct no_reduce_R as [Fnr Vnr].
unfold DyadicTrig.reduce in H.
lazymatch type of H with
| ((if ?E then _ else _) = _) => destruct E eqn:Hle
end.
- (* [t <= 201/256]: [k = 0], and [ρ = t] is a point. *)
  destruct (Dyadic.encl_point n t) as [c |] eqn:Ec; [| discriminate H].
  cbv beta iota in H. injection H as Hq Hng Hr. subst quad neg r.
  destruct (point_has n t c Hn Ec) as (Hc & HcE & Hct).
  assert (Ht1 : (B2R t <= 201 / 256)%R).
  { unfold Model.le in Hle. rewrite Bleb_correct in Hle by assumption.
    destruct (Rle_bool_spec (B2R t) (B2R DyadicTrig.no_reduce)); [lra | discriminate Hle]. }
  split; [exact Hc |]. split; [apply (encl_le_mono (2 ^ 13)); [lia | exact HcE] |].
  exists 0, (B2R t). split; [reflexivity |]. split; [exact Hct |]. split; [lra |]. cbv beta iota. ring.
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
  assert (Hnx : nx = (l + 1 + bq)%nat) by reflexivity.
  assert (He : e = 1 - 64 * Z.of_nat l) by (unfold e, s; lia).
  assert (Hs : s = 64 * Z.of_nat l - 2) by reflexivity.
  clearbody b bq l s nx e.
  (* The top [l] limbs [P] of [PI]: π/2 in [[P, P + 1) 2^e]. *)
  assert (Hpok : limbs_ok p) by (apply limbs_ok_skipn, PI_ok).
  assert (Hpl : length p = l) by (unfold p; rewrite length_skipn, PI_length; lia).
  destruct (PI_top l ltac:(lia)) as [HP1 HP2].
  change (skipn (66 - l) DyadicConsts.PI) with p in HP1, HP2.
  rewrite <- He in HP1, HP2.
  clearbody p.
  pose proof (bpow_gt_0 radix2 e) as Hbe.
  pose proof (val_nonneg p Hpok) as Hp0.
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
  (* The three roundings, of [q' 2^e] up and of [center 2^e] both ways,
     with exponents in [[-2^14, 2^14]]: the values are 0 or in [[2^e,
     2^(64 nx + e)]], with [e >= -4223] and [64 nx + e <= 65 + 64 bq]. *)
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
  (* [w] holds [x0 = center 2^e], and [kd = [0, K]] holds any [y] in
     [[0, q' 2^e]]. *)
  set (x0 := (IZR (Limbs.val center) * bpow radix2 e)%R) in *.
  set (w := {| Dyadic.en_lo := lo; Dyadic.en_hi := hi |}) in H.
  set (kd := {| Dyadic.en_lo := Dyadic.dy_zero n; Dyadic.en_hi := K |}) in H.
  assert (Hw : encl_ok n w /\ encl_le (2 ^ 14) w /\ encl_has w x0).
  { pose proof (dround_bounds n x0 Hn).
    unfold w, encl_ok, encl_le, encl_has; cbn [Dyadic.en_lo Dyadic.en_hi].
    rewrite Hlov, Hhiv. split; [split; [exact Hlook | split; [exact Hhiok | lra]] |].
    split; [split; lia | lra]. }
  assert (Hkd : encl_ok n kd /\ encl_le (2 ^ 14) kd /\
                forall y, (0 <= y <= IZR (Limbs.val q') * bpow radix2 e)%R -> encl_has kd y).
  { destruct (dy_zero_ok n) as (Hz & HzR & _).
    pose proof (dround_bounds n (IZR (Limbs.val q') * bpow radix2 e) Hn).
    assert (0 <= IZR (Limbs.val q') * bpow radix2 e)%R
      by (apply Rmult_le_pos; [apply IZR_le; lia | lra]).
    unfold kd, encl_ok, encl_le, encl_has; cbn [Dyadic.en_lo Dyadic.en_hi].
    rewrite HzR, HKv. split; [split; [exact Hz | split; [exact HKok | lra]] |].
    split; [cbn [Dyadic.dy_zero Dyadic.dy_exp]; split; lia |].
    intros y Hy. lra. }
  destruct Hw as (Hwok & Hwle & Hwx). destruct Hkd as (Hkdok & Hkdle & Hkdy).
  (* [ρ = x0 + y] if [up], and [x0 - y] otherwise. *)
  lazymatch type of H with
  | (match ?E with Some _ => _ | None => _ end = _) => destruct E as [rho |] eqn:Erho
  end; [| discriminate H].
  assert (Hrho : encl_ok n rho /\ encl_le (2 ^ 15) rho /\
                 forall x y, encl_has w x -> encl_has kd y ->
                 encl_has rho (if up then x + y else x - y)%R).
  { destruct up.
    - destruct (add_step n w kd rho (2 ^ 14) (2 ^ 14) Hn Hwok Hkdok Hwle Hkdle
                  ltac:(lia) ltac:(lia) Erho) as (A & B & C).
      split; [exact A |]. split; [apply (encl_le_mono (Z.max (2 ^ 14) (2 ^ 14) + 2 ^ 13));
                                  [lia | exact B] | exact C].
    - destruct (sub_step n w kd rho (2 ^ 14) (2 ^ 14) Hn Hwok Hkdok Hwle Hkdle
                  ltac:(lia) ltac:(lia) Erho) as (A & B & C).
      split; [exact A |]. split; [apply (encl_le_mono (Z.max (2 ^ 14) (2 ^ 14) + 2 ^ 13));
                                  [lia | exact B] | exact C]. }
  clear Erho.
  cbv beta iota in H.
  destruct Hrho as (Hrok & Hrle & Hrhas).
  (* The two tests of the [assert!]: [lo >= -1] and [hi <= 1]. *)
  destruct (Dyadic.from_f64 n DyadicExp.m_one) as [m1 |] eqn:Em1; [| discriminate H].
  cbv beta iota in H.
  destruct (from_f64_step n _ m1 Hn Em1) as (Hm1 & _ & Vm1 & _). rewrite m_one_R in Vm1.
  destruct (DyadicExp.dy_lt n (Dyadic.en_lo rho) m1) eqn:Elt; [discriminate H |].
  cbv beta iota in H.
  destruct (Dyadic.from_f64 n DyadicExp.one) as [p1 |] eqn:Ep1; [| discriminate H].
  cbv beta iota in H.
  destruct (from_f64_step n _ p1 Hn Ep1) as (Hpo1 & _ & Vp1 & _).
  rewrite (proj2 one_B2R) in Vp1.
  destruct (DyadicExp.dy_gt n (Dyadic.en_hi rho) p1) eqn:Egt; [discriminate H |].
  cbv beta iota in H.
  injection H as Hq Hng Hr. subst quad neg r.
  pose proof (dy_lt_false n _ _ Hn (proj1 Hrok) Hm1 Elt) as Hlo1.
  pose proof (dy_gt_false n _ _ Hn (proj1 (proj2 Hrok)) Hpo1 Egt) as Hhi1.
  rewrite Vm1 in Hlo1. rewrite Vp1 in Hhi1.
  split; [exact Hrok |]. split; [exact Hrle |].
  (* [k = q'], and [y0 = q' (π/2 - P 2^e)] is in [[0, q' 2^e]]. *)
  set (delta := (PI / 2 - IZR (Limbs.val p) * bpow radix2 e)%R).
  set (y0 := (IZR (Limbs.val q') * delta)%R).
  assert (Hy0 : (0 <= y0 <= IZR (Limbs.val q') * bpow radix2 e)%R).
  { assert (0 <= IZR (Limbs.val q'))%R by (apply IZR_le; lia).
    unfold y0. split; [apply Rmult_le_pos; unfold delta; lra |].
    apply Rmult_le_compat_l; [lra | unfold delta; lra]. }
  exists (Limbs.val q'), (if up then x0 + y0 else x0 - y0)%R.
  split.
  { (* [Z.land (limb q' 0) 3 = (q' mod 2^64) mod 4 = q' mod 4] *)
    rewrite (limb_val q' 0 Hq'ok). change (64 * Z.of_nat 0) with 0.
    rewrite Z.pow_0_r, Z.div_1_r. change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
    change (2 ^ 2) with 4. symmetry. apply Z.mod_mod_divide. exists (2 ^ 62). reflexivity. }
  assert (Hhas : encl_has rho (if up then x0 + y0 else x0 - y0)%R)
    by (apply Hrhas; [exact Hwx | apply Hkdy; exact Hy0]).
  split; [exact Hhas |].
  split; [unfold encl_has in Hhas; lra |].
  (* [X = q P + R]: if [up], [t = q' π/2 - ((P - R) 2^e + y0)], and
     otherwise [t = q π/2 + (R 2^e - y0)]. *)
  rewrite HtX, Hdm. unfold x0, y0, delta.
  rewrite Hq'v, Hcenv. destruct up; cbv beta iota.
  + rewrite Hcv'. rewrite !plus_IZR, !mult_IZR, minus_IZR. ring.
  + rewrite !plus_IZR, !mult_IZR. ring.
Qed.
