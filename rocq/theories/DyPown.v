(** * The integer powers of a positive [f64] in the dyadic kernel

    [ev_pown x k] of [DyadicPow] in [Model.v] encloses [x^k] of a finite
    [x > 0] and an [i32] [k <> 0] by binary powering of the point [x]
    ([powi]), and the quotient of 1 by it for [k < 0] ([ev_pown_correct]).
    The exponents of the dyadics stay small along the chain of squarings
    by the bounds of [DyGrow.v]. Where [x^k] is an [f64], every product
    and the quotient are exact, so the enclosure is that point at every
    level ([ev_pown_exact]), and [ziv] returns it ([ziv_exact]).
    [pown_pos x k up] rounds [x^k] in the direction [up]
    ([pown_pos_correct]): the rules below, which take bounds on [x^k] from
    the exponent of [x] ([expo_spec] of [DyPowRules.v]), where one
    applies, and otherwise [ziv_correct] of [DyDriver.v]. It returns the
    [f64] [x^k] wherever there is one ([pown_pos_exact]). [pown_dir]
    returns the special values that [pown_c] of [Contract.v] names
    ([pown_dir_zero_neg] and [pown_dir_inf]), and otherwise [pown_pos] of
    [|x|], negated for an odd [k] at [x < 0]. Where it returns, it rounds
    [powerRZ] of a finite [x] and an [i32] [n] in the domain [pown_dom n]
    in the direction [up] ([pown_dir_correct]), and it returns the [f64]
    [x^n] at a finite [x <> 0] wherever there is one ([pown_dir_exact]).
    That the loop ends before its cap elsewhere is not proved. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary MpfrRound OfPointCore DyRound DyConv DyOps
  DyDriver DyGrow DyExpRules DyExp DyPowArith DyPowRules.
From Stdlib Require Zquot.
From Inari Require ParseRound.

Open Scope Z_scope.

Local Notation FX n := (generic_format radix2 (FLX_exp (dprec n))) (only parsing).

(** ** Helpers *)

Lemma Rmin_same : forall r, Rmin r r = r.
Proof. intros r. apply Rmin_left. apply Rle_refl. Qed.

Lemma Rmax_same : forall r, Rmax r r = r.
Proof. intros r. apply Rmax_left. apply Rle_refl. Qed.

(** [(m 2^e)^j = m^j 2^(e j)]. *)
Lemma pown_dyadic_pow :
  forall m e j,
  ((IZR m * bpow radix2 e) ^ j = IZR (m ^ Z.of_nat j) * bpow radix2 (e * Z.of_nat j))%R.
Proof.
intros m e j. induction j as [|j IH].
- cbn [pow Z.of_nat]. rewrite Z.mul_0_r, Z.pow_0_r. simpl. ring.
- rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  replace (e * Z.succ (Z.of_nat j)) with (e + e * Z.of_nat j) by ring.
  rewrite bpow_plus, mult_IZR. cbn [pow]. rewrite IH. ring.
Qed.

Lemma pown_format :
  forall n m e, level_ok n -> 0 <= m < 2 ^ 53 -> FX n (IZR m * bpow radix2 e)%R.
Proof.
intros n m e Hn Hm. pose proof (dprec_bounds n Hn).
apply (format_int n false m e Hn).
rewrite Z.abs_eq by lia.
apply Z.lt_le_trans with (2 ^ 53); [lia | apply Z.pow_le_mono_r; lia].
Qed.

(** Every [x^j] for [j <= p] has an odd part at most [mx^p]. *)
Lemma pown_chain_format :
  forall n mx ex p j,
  level_ok n -> 0 < mx -> mx ^ Zpos p < 2 ^ 53 -> (1 <= j <= Pos.to_nat p)%nat ->
  FX n ((IZR mx * bpow radix2 ex) ^ j)%R.
Proof.
intros n mx ex p j Hn Pmx Bm Hj. rewrite pown_dyadic_pow. apply pown_format; [exact Hn |].
split; [apply Z.pow_nonneg; lia |].
apply Z.le_lt_trans with (mx ^ Zpos p); [| exact Bm].
apply Z.pow_le_mono_r; [exact Pmx |]. rewrite <- positive_nat_Z. apply Nat2Z.inj_le. lia.
Qed.

Lemma sq_pow : forall y j, ((y * y) ^ j = y ^ (2 * j))%R.
Proof. intros y j. rewrite pow_mult. f_equal. ring. Qed.

Lemma pow_xO : forall y q, (y ^ Pos.to_nat (xO q) = (y * y) ^ Pos.to_nat q)%R.
Proof. intros y q. rewrite Pos2Nat.inj_xO, sq_pow. reflexivity. Qed.

Lemma pow_xI : forall y q, (y ^ Pos.to_nat (xI q) = y * (y * y) ^ Pos.to_nat q)%R.
Proof. intros y q. rewrite Pos2Nat.inj_xI, sq_pow. reflexivity. Qed.

(** A product: [mul_step], and the point [y1 y2] where the operands are
    the points [y1] and [y2] and [y1 y2] has [dprec n] bits, by
    [encl_mul_correct] and [dround_id]. *)
Lemma pown_mul :
  forall n a b Ea Eb,
  level_ok n -> encl_ok n a -> encl_ok n b -> encl_le Ea a -> encl_le Eb b ->
  0 <= Ea <= 2 ^ 60 -> 0 <= Eb <= 2 ^ 60 ->
  exists c,
  Dyadic.encl_mul n a b = Some c /\ encl_ok n c /\ encl_le (Ea + Eb + 2 ^ 13) c /\
  (forall x y, encl_has a x -> encl_has b y -> encl_has c (x * y)) /\
  (forall y1 y2, lo_R a = y1 -> hi_R a = y1 -> lo_R b = y2 -> hi_R b = y2 ->
   FX n (y1 * y2)%R -> lo_R c = (y1 * y2)%R /\ hi_R c = (y1 * y2)%R).
Proof.
intros n a b Ea Eb Hn Ha Hb La Lb HEa HEb.
assert (Sa : encl_small a) by (apply (encl_le_small Ea); [lia | exact La]).
assert (Sb : encl_small b) by (apply (encl_le_small Eb); [lia | exact Lb]).
destruct (encl_mul_correct n a b Hn Ha Hb Sa Sb) as (c & E & Okc & Vlo & Vhi & _).
destruct (mul_step n a b c Ea Eb Hn Ha Hb La Lb HEa HEb E) as (_ & Lc & Hc).
exists c. split; [exact E |]. split; [exact Okc |]. split; [exact Lc |]. split; [exact Hc |].
intros y1 y2 E1 E2 E3 E4 F. rewrite E1, E2, E3, E4 in Vlo, Vhi.
rewrite !Rmin_same in Vlo. rewrite !Rmax_same in Vhi.
rewrite (dround_id n false _ Hn F) in Vlo. rewrite (dround_id n true _ Hn F) in Vhi.
split; assumption.
Qed.

(** ** Binary powering

    The bound [p (E + 2^13) - 2^13] on the exponents follows [mul_step]:
    a square of a bound [E] has [2 E + 2^13], and a product adds the
    bounds and [2^13]. *)
Lemma powi_spec :
  forall p n a E,
  level_ok n -> encl_ok n a -> encl_le E a -> 0 <= E -> Zpos p * (E + 2 ^ 13) <= 2 ^ 60 ->
  exists c,
  DyadicPow.powi n a p = Some c /\ encl_ok n c /\ encl_le (Zpos p * (E + 2 ^ 13) - 2 ^ 13) c /\
  (forall y, encl_has a y -> encl_has c (y ^ Pos.to_nat p)) /\
  (forall y, lo_R a = y -> hi_R a = y ->
   (forall j, (1 <= j <= Pos.to_nat p)%nat -> FX n (y ^ j)%R) ->
   lo_R c = (y ^ Pos.to_nat p)%R /\ hi_R c = (y ^ Pos.to_nat p)%R).
Proof.
induction p as [q IH | q IH |]; intros n a E Hn Ha La HE Hp.
- (* [x (x^2)^q] *)
  rewrite Pos2Z.inj_xI in Hp |- *.
  pose proof (Pos2Z.is_pos q) as Hq.
  assert (HE1 : 0 <= E <= 2 ^ 60) by nia.
  destruct (pown_mul n a a E E Hn Ha Ha La La HE1 HE1) as (x2 & E2 & Ok2 & L2 & H2 & P2).
  assert (HE2 : 0 <= E + E + 2 ^ 13) by lia.
  assert (Hp2 : Zpos q * (E + E + 2 ^ 13 + 2 ^ 13) <= 2 ^ 60) by nia.
  destruct (IH n x2 (E + E + 2 ^ 13) Hn Ok2 L2 HE2 Hp2) as (r & Er & Okr & Lr & Hr & Pr).
  assert (HE3 : 0 <= Zpos q * (E + E + 2 ^ 13 + 2 ^ 13) - 2 ^ 13 <= 2 ^ 60) by nia.
  destruct (pown_mul n a r E _ Hn Ha Okr La Lr HE1 HE3) as (c & Ec & Okc & Lc & Hc & Pc).
  exists c. split.
  { cbn [DyadicPow.powi]. rewrite E2. cbv beta iota. rewrite Er. exact Ec. }
  split; [exact Okc |]. split.
  { replace ((2 * Zpos q + 1) * (E + 2 ^ 13) - 2 ^ 13)
      with (E + (Zpos q * (E + E + 2 ^ 13 + 2 ^ 13) - 2 ^ 13) + 2 ^ 13) by ring.
    exact Lc. }
  split.
  { intros y Hy. rewrite pow_xI. apply Hc; [exact Hy |]. apply Hr. apply H2; exact Hy. }
  intros y Ely Ehy Hf.
  pose proof (Pos2Nat.is_pos q) as Hq'. pose proof (Pos2Nat.inj_xI q) as Hxi.
  destruct (P2 y y Ely Ehy Ely Ehy) as (X2lo & X2hi).
  { replace (y * y)%R with (y ^ 2)%R by ring. apply Hf. lia. }
  destruct (Pr (y * y)%R X2lo X2hi) as (Rlo & Rhi).
  { intros j Hj. rewrite sq_pow. apply Hf. lia. }
  rewrite pow_xI. apply Pc; [exact Ely | exact Ehy | exact Rlo | exact Rhi |].
  rewrite <- pow_xI. apply Hf. lia.
- (* [(x^2)^q] *)
  rewrite Pos2Z.inj_xO in Hp |- *.
  pose proof (Pos2Z.is_pos q) as Hq.
  assert (HE1 : 0 <= E <= 2 ^ 60) by nia.
  destruct (pown_mul n a a E E Hn Ha Ha La La HE1 HE1) as (x2 & E2 & Ok2 & L2 & H2 & P2).
  assert (HE2 : 0 <= E + E + 2 ^ 13) by lia.
  assert (Hp2 : Zpos q * (E + E + 2 ^ 13 + 2 ^ 13) <= 2 ^ 60) by nia.
  destruct (IH n x2 (E + E + 2 ^ 13) Hn Ok2 L2 HE2 Hp2) as (c & Ec & Okc & Lc & Hc & Pc).
  exists c. split.
  { cbn [DyadicPow.powi]. rewrite E2. cbv beta iota. exact Ec. }
  split; [exact Okc |]. split.
  { replace (2 * Zpos q * (E + 2 ^ 13) - 2 ^ 13)
      with (Zpos q * (E + E + 2 ^ 13 + 2 ^ 13) - 2 ^ 13) by ring.
    exact Lc. }
  split.
  { intros y Hy. rewrite pow_xO. apply Hc. apply H2; exact Hy. }
  intros y Ely Ehy Hf.
  pose proof (Pos2Nat.is_pos q) as Hq'. pose proof (Pos2Nat.inj_xO q) as Hxo.
  destruct (P2 y y Ely Ehy Ely Ehy) as (X2lo & X2hi).
  { replace (y * y)%R with (y ^ 2)%R by ring. apply Hf. lia. }
  rewrite pow_xO. apply Pc; [exact X2lo | exact X2hi |].
  intros j Hj. rewrite sq_pow. apply Hf. lia.
- (* [x] *)
  exists a. split; [reflexivity |]. split; [exact Ha |]. split.
  { replace (1 * (E + 2 ^ 13) - 2 ^ 13) with E by ring. exact La. }
  change (Pos.to_nat 1) with 1%nat. split.
  + intros y Hy. rewrite pow_1. exact Hy.
  + intros y Ely Ehy _. rewrite pow_1. split; assumption.
Qed.

(** ** The odd part of an exact power

    Where [x^k] is an [f64] [v], the odd part [mx] of [x] has [mx^|k| <
    2^53], as [mx^|k|] is the odd part of [v] for [k > 0], and [mx = 1]
    for [k < 0], as [mx^|k|] times the odd part of [v] is then 1
    ([odd_pow2_inj]). *)
Lemma pown_exact_odd :
  forall x k (v : f64) mx ex,
  is_finite x = true -> (0 < B2R x)%R -> k <> 0 ->
  is_finite v = true -> powerRZ (B2R x) k = B2R v ->
  DyadicPow.odd_parts x = (mx, ex) ->
  B2R x = (IZR mx * bpow radix2 ex)%R /\ 0 < mx /\
  mx ^ Zpos (Z.to_pos (Z.abs k)) < 2 ^ 53 /\ (k < 0 -> mx = 1).
Proof.
intros x k v mx ex Fx Hx Hk Fv Hv Ex.
destruct (odd_parts_spec x mx ex Fx (Rgt_not_eq _ _ Hx) Ex) as (Omx & Bmx & _ & Vx).
rewrite Rabs_pos_eq in Vx by lra.
assert (Pv : (0 < B2R v)%R) by (rewrite <- Hv; apply powerRZ_lt; exact Hx).
destruct (DyadicPow.odd_parts v) as [mv ev] eqn:Ev.
destruct (odd_parts_spec v mv ev Fv (Rgt_not_eq _ _ Pv) Ev) as (Omv & Bmv & _ & Vv).
rewrite Rabs_pos_eq in Vv by lra.
assert (Pmx : 0 < mx) by lia.
split; [exact Vx |]. split; [exact Pmx |].
destruct k as [| p | p]; [contradiction Hk; reflexivity | |].
- change (Z.to_pos (Z.abs (Zpos p))) with p.
  change (powerRZ (B2R x) (Zpos p)) with (B2R x ^ Pos.to_nat p)%R in Hv.
  rewrite Vx, pown_dyadic_pow, positive_nat_Z, Vv in Hv.
  destruct (odd_pow2_inj (mx ^ Zpos p) (ex * Zpos p) mv ev) as (Q & _).
  + rewrite Z.odd_pow by lia. exact Omx.
  + exact Omv.
  + exact Hv.
  + split; [lia | intros H; lia].
- change (Z.to_pos (Z.abs (Zneg p))) with p.
  change (powerRZ (B2R x) (Zneg p)) with (/ B2R x ^ Pos.to_nat p)%R in Hv.
  rewrite Vx, pown_dyadic_pow, positive_nat_Z, Vv in Hv.
  assert (Pm : 0 < mx ^ Zpos p) by (apply Z.pow_pos_nonneg; lia).
  assert (A0 : (IZR (mx ^ Zpos p) * bpow radix2 (ex * Zpos p) <> 0)%R).
  { apply Rgt_not_eq, Rmult_lt_0_compat; [apply IZR_lt; exact Pm | apply bpow_gt_0]. }
  assert (H1 : (IZR (mx ^ Zpos p * mv) * bpow radix2 (ex * Zpos p + ev) =
                IZR 1 * bpow radix2 0)%R).
  { rewrite mult_IZR, bpow_plus.
    replace (IZR (mx ^ Zpos p) * IZR mv * (bpow radix2 (ex * Zpos p) * bpow radix2 ev))%R
      with ((IZR (mx ^ Zpos p) * bpow radix2 (ex * Zpos p)) * (IZR mv * bpow radix2 ev))%R
      by ring.
    rewrite <- Hv, Rinv_r by exact A0. change (bpow radix2 0) with 1%R. ring. }
  destruct (odd_pow2_inj (mx ^ Zpos p * mv) (ex * Zpos p + ev) 1 0) as (Q & _).
  + rewrite Z.odd_mul, Z.odd_pow by lia. rewrite Omx, Omv. reflexivity.
  + reflexivity.
  + exact H1.
  + assert (Q1 : mx ^ Zpos p = 1) by nia.
    assert (Q2 : mx <= mx ^ Zpos p).
    { rewrite <- (Z.pow_1_r mx) at 1. apply Z.pow_le_mono_r; lia. }
    split; [lia | intros _; lia].
Qed.

(** ** The enclosures *)

Lemma ev_pown_correct :
  forall x k n a,
  level_ok n -> is_finite x = true -> (0 < B2R x)%R -> k <> 0 -> is_i32 k ->
  DyadicPow.ev_pown x k n = Some a ->
  encl_ok n a /\ encl_has a (powerRZ (B2R x) k).
Proof.
intros x k n a Hn Fx Hx Hk Hi E.
unfold DyadicPow.ev_pown in E.
destruct (Dyadic.encl_point n x) as [px |] eqn:Epx; [| discriminate E].
cbv beta iota in E.
destruct (point_step n x px Hn Epx) as (Okx & Lx & Vlo & Vhi & _).
assert (Hp : Zpos (Z.to_pos (Z.abs k)) * (2 ^ 13 + 2 ^ 13) <= 2 ^ 60).
{ rewrite Z2Pos.id by lia. unfold is_i32 in Hi. lia. }
assert (H13 : 0 <= 2 ^ 13) by lia.
destruct (powi_spec (Z.to_pos (Z.abs k)) n px (2 ^ 13) Hn Okx Lx H13 Hp)
  as (c & Ec & Okc & Lc & Hc & _).
rewrite Ec in E. cbv beta iota in E.
assert (Hy : encl_has px (B2R x)).
{ unfold encl_has. unfold lo_R, hi_R in Vlo, Vhi. rewrite Vlo, Vhi. lra. }
specialize (Hc (B2R x) Hy).
destruct k as [| p | p]; [contradiction Hk; reflexivity | |].
- change (Zpos p <? 0) with false in E. cbv beta iota in E. injection E as <-.
  split; [exact Okc | exact Hc].
- change (Zneg p <? 0) with true in E. cbv beta iota in E.
  destruct (Dyadic.encl_point n DyadicExp.one) as [o |] eqn:Eo; [| discriminate E].
  cbv beta iota in E.
  destruct (point_step n DyadicExp.one o Hn Eo) as (Oko & Lo & Volo & Vohi & _).
  assert (HE : 0 <= Zpos (Z.to_pos (Z.abs (Zneg p))) * (2 ^ 13 + 2 ^ 13) - 2 ^ 13 <= 2 ^ 60)
    by lia.
  assert (H13' : 0 <= 2 ^ 13 <= 2 ^ 60) by lia.
  destruct (div_step n o c a _ _ Hn Oko Okc Lo Lc H13' HE E) as (Oka & _ & Ha).
  split; [exact Oka |].
  change (powerRZ (B2R x) (Zneg p)) with (/ B2R x ^ Pos.to_nat p)%R.
  change (Z.to_pos (Z.abs (Zneg p))) with p in Hc.
  replace (/ B2R x ^ Pos.to_nat p)%R with (1 / B2R x ^ Pos.to_nat p)%R
    by (unfold Rdiv; apply Rmult_1_l).
  apply Ha; [| exact Hc].
  unfold encl_has. unfold lo_R, hi_R in Volo, Vohi. rewrite Volo, Vohi, (proj2 one_B2R). lra.
Qed.

Lemma ev_pown_exact :
  forall x k n (v : f64),
  level_ok n -> is_finite x = true -> (0 < B2R x)%R -> k <> 0 -> is_i32 k ->
  is_finite v = true -> powerRZ (B2R x) k = B2R v ->
  exists a, DyadicPow.ev_pown x k n = Some a /\ encl_ok n a /\
    lo_R a = B2R v /\ hi_R a = B2R v.
Proof.
intros x k n v Hn Fx Hx Hk Hi Fv Hv.
destruct (DyadicPow.odd_parts x) as [mx ex] eqn:Ex.
destruct (pown_exact_odd x k v mx ex Fx Hx Hk Fv Hv Ex) as (Vx & Pmx & Bm & M1).
destruct (encl_point_correct n x Hn Fx) as (px & Epx & Okx & _ & Vlo & Vhi).
destruct (point_step n x px Hn Epx) as (_ & Lx & _).
assert (Hp : Zpos (Z.to_pos (Z.abs k)) * (2 ^ 13 + 2 ^ 13) <= 2 ^ 60).
{ rewrite Z2Pos.id by lia. unfold is_i32 in Hi. lia. }
assert (H13 : 0 <= 2 ^ 13) by lia.
destruct (powi_spec (Z.to_pos (Z.abs k)) n px (2 ^ 13) Hn Okx Lx H13 Hp)
  as (c & Ec & Okc & Lc & _ & Pc).
assert (Sc : encl_small c)
  by (apply (encl_le_small (Zpos (Z.to_pos (Z.abs k)) * (2 ^ 13 + 2 ^ 13) - 2 ^ 13) c);
      [lia | exact Lc]).
destruct (Pc (B2R x) Vlo Vhi) as (Clo & Chi).
{ intros j Hj. rewrite Vx. exact (pown_chain_format n mx ex _ j Hn Pmx Bm Hj). }
unfold DyadicPow.ev_pown. rewrite Epx. cbv beta iota. rewrite Ec. cbv beta iota.
destruct k as [| p | p]; [contradiction Hk; reflexivity | |].
- change (Zpos p <? 0) with false. cbv beta iota.
  exists c. split; [reflexivity |]. split; [exact Okc |].
  change (Z.to_pos (Z.abs (Zpos p))) with p in Clo, Chi.
  change (powerRZ (B2R x) (Zpos p)) with (B2R x ^ Pos.to_nat p)%R in Hv.
  rewrite Clo, Chi. split; exact Hv.
- change (Zneg p <? 0) with true. cbv beta iota.
  assert (M : mx = 1) by (apply M1; lia). subst mx.
  change (Z.to_pos (Z.abs (Zneg p))) with p in Clo, Chi.
  change (powerRZ (B2R x) (Zneg p)) with (/ B2R x ^ Pos.to_nat p)%R in Hv.
  (* [x = 2^ex], so [x^|k|] is [2^(ex |k|)] and its inverse is exact. *)
  assert (Py : (B2R x ^ Pos.to_nat p = bpow radix2 (ex * Zpos p))%R).
  { rewrite Vx, pown_dyadic_pow, positive_nat_Z, Z.pow_1_l by lia. ring. }
  destruct (encl_point_correct n DyadicExp.one Hn (proj1 one_B2R))
    as (o & Eo & Oko & So & Volo & Vohi).
  rewrite Eo. cbv beta iota.
  assert (H0 : (0 < lo_R c)%R) by (rewrite Clo, Py; apply bpow_gt_0).
  destruct (encl_div_correct n o c Hn Oko Okc So Sc (or_introl H0))
    as (a & Ea & Oka & Alo & Ahi & _).
  rewrite Ea. exists a. split; [reflexivity |]. split; [exact Oka |].
  rewrite Volo, Vohi, Clo, Chi, (proj2 one_B2R) in Alo, Ahi.
  rewrite !Rmin_same in Alo. rewrite !Rmax_same in Ahi.
  assert (Q : (1 / B2R x ^ Pos.to_nat p = B2R v)%R)
    by (rewrite <- Hv; unfold Rdiv; apply Rmult_1_l).
  rewrite Q in Alo, Ahi.
  assert (FV : FX n (B2R v)).
  { rewrite <- Q, Py. unfold Rdiv. rewrite Rmult_1_l, <- bpow_opp.
    replace (bpow radix2 (- (ex * Zpos p))) with (IZR 1 * bpow radix2 (- (ex * Zpos p)))%R
      by ring.
    apply pown_format; [exact Hn | lia]. }
  rewrite (dround_id n false _ Hn FV) in Alo. rewrite (dround_id n true _ Hn FV) in Ahi.
  split; assumption.
Qed.

(** ** Ziv's strategy at an exact point *)

Lemma ziv_at_exact :
  forall ev (up : bool) n (v : f64),
  level_ok n -> is_finite v = true -> B2R v <> 0%R ->
  (exists a, ev n = Some a /\ encl_ok n a /\ lo_R a = B2R v /\ hi_R a = B2R v) ->
  Dyadic.ziv_at ev n up = Some (Some v).
Proof.
intros ev up n v Hn Fv Nv (a & Ea & (Hlo & Hhi & _) & Vlo & Vhi).
unfold Dyadic.ziv_at. rewrite Ea. cbv beta iota.
destruct (to_f64_correct n (Dyadic.en_lo a) up Hn Hlo) as (v1 & E1 & R1).
destruct (to_f64_correct n (Dyadic.en_hi a) up Hn Hhi) as (v2 & E2 & R2).
rewrite E1, E2. cbv beta iota.
unfold lo_R, hi_R in Vlo, Vhi. rewrite Vlo in R1. rewrite Vhi in R2.
assert (R : mpfr_round f64_format (if up then RNDU else RNDD) (B2R v) (with_val v)).
{ apply finite_mpfr_round; [exact Fv |].
  destruct up; cbn [MpfrRound.rnd_pt];
    [apply Rnd_UP_pt_refl | apply Rnd_DN_pt_refl]; apply f64_format_B2R; exact Fv. }
(* [B2R v] is an [f64], so it rounds to [v] alone: it is not a zero. *)
assert (Q : forall w, mpfr_round f64_format (if up then RNDU else RNDD) (B2R v) (with_val w) ->
            w = v).
{ intros w Rw. destruct (mpfr_round_unique _ _ _ _ _ Rw R) as [Q | (s & s' & Q1 & Q2)].
  - apply with_val_inj. exact Q.
  - exfalso.
    destruct (MpfrIdeal.with_val_finite_cases v Fv) as [(s0 & _ & Z0) | (Wv & _)];
      [exact (Nv Z0) |].
    rewrite Wv in Q2. discriminate Q2. }
rewrite (Q v1 R1), (Q v2 R2).
assert (Q3 : Model.eq v v = true).
{ unfold Model.eq. rewrite Beqb_refl. destruct v; try discriminate Fv; reflexivity. }
rewrite Q3. reflexivity.
Qed.

Lemma ziv_levels_exact :
  forall ev up start (v : f64) levels,
  (forall n, In n levels -> level_ok n) -> (exists n, In n levels /\ (start <= n)%nat) ->
  (forall n, level_ok n -> Dyadic.ziv_at ev n up = Some (Some v)) ->
  Dyadic.ziv_levels ev up start levels = Some v.
Proof.
intros ev up start v levels. induction levels as [|m ls IH]; intros Hl (n & Hin & Hs) Hz.
- destruct Hin.
- cbn [Dyadic.ziv_levels]. destruct (Nat.leb_spec start m) as [Hm | Hm].
  + rewrite (Hz m (Hl m (or_introl eq_refl))). reflexivity.
  + apply IH.
    * intros n' H'. apply Hl. right. exact H'.
    * destruct Hin as [<- | Hin]; [lia |]. exists n. split; assumption.
    * exact Hz.
Qed.

(** Where [ev] encloses a nonzero [f64] [v] by the point [v] at every
    level, [ziv] returns [v] at its first level. *)
Lemma ziv_exact :
  forall ev (up : bool) start (v : f64),
  is_finite v = true -> B2R v <> 0%R -> (start <= 64)%nat ->
  (forall n, level_ok n -> exists a, ev n = Some a /\ encl_ok n a /\
     lo_R a = B2R v /\ hi_R a = B2R v) ->
  Dyadic.ziv ev up start = Some v.
Proof.
intros ev up start v Fv Nv Hs Hev. unfold Dyadic.ziv.
apply ziv_levels_exact.
- intros n Hin. unfold level_ok. cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]; [lia |]). destruct Hin.
- exists 64%nat. split; [| exact Hs]. cbn [In]. do 6 right. left. reflexivity.
- intros n Hn. apply ziv_at_exact; [exact Hn | exact Fv | exact Nv | exact (Hev n Hn)].
Qed.

(** ** The rules of [pown_pos]

    [g = expo x] gives [2^(g k) <= x^k < 2^((g+1) k)] for [k > 0], and
    the reverse for [k < 0]. The bounds are taken on [k ln x], as
    [x^k = e^(k ln x)] for [x > 0] ([powerRZ_Rpower]). *)

Lemma pown_ln2_pos : (0 < ln 2)%R.
Proof. rewrite <- ln_1. apply ln_increasing; lra. Qed.

(** [g ln 2 <= ln x < (g + 1) ln 2] for [g = expo x], from
    [2^g <= x < 2^(g+1)] ([expo_spec]). *)
Lemma pown_ln_expo :
  forall x, is_finite x = true -> (0 < B2R x)%R ->
  (IZR (DyadicPow.expo x) * ln 2 <= ln (B2R x) < (IZR (DyadicPow.expo x) + 1) * ln 2)%R.
Proof.
intros x Fx Hx.
destruct (expo_spec x Fx (Rgt_not_eq _ _ Hx)) as [H1 H2].
rewrite Rabs_pos_eq in H1, H2 by lra.
rewrite bpow_exp2 in H1, H2. rewrite plus_IZR in H2.
split.
- rewrite <- (ln_exp (IZR (DyadicPow.expo x) * ln 2)).
  destruct H1 as [H1 | H1].
  + left. apply ln_increasing; [apply exp_pos | exact H1].
  + right. rewrite H1. reflexivity.
- rewrite <- (ln_exp ((IZR (DyadicPow.expo x) + 1) * ln 2)).
  apply ln_increasing; [exact Hx | exact H2].
Qed.

(** [2^1024 <= x^k] where the rule of overflow applies. *)
Lemma pown_over_bound :
  forall x k,
  is_finite x = true -> (0 < B2R x)%R ->
  1024 <= (if 0 <? k then DyadicPow.expo x * k else (DyadicPow.expo x + 1) * k) ->
  (bpow radix2 1024 <= powerRZ (B2R x) k)%R.
Proof.
intros x k Fx Hx Hk.
destruct (pown_ln_expo x Fx Hx) as [L1 L2]. pose proof pown_ln2_pos as P.
rewrite powerRZ_Rpower by exact Hx. unfold Rpower. rewrite bpow_exp2.
set (g := DyadicPow.expo x) in *.
assert (H : (IZR 1024 * ln 2 <= IZR k * ln (B2R x))%R).
{ destruct (0 <? k) eqn:K.
  - apply Z.ltb_lt, IZR_lt in K. apply IZR_le in Hk. rewrite mult_IZR in Hk.
    (* [k ln x >= k g ln 2 >= 1024 ln 2]. *)
    assert (A : (0 <= IZR k * (ln (B2R x) - IZR g * ln 2))%R) by (apply Rmult_le_pos; lra).
    assert (B : (0 <= ln 2 * (IZR g * IZR k - 1024))%R) by (apply Rmult_le_pos; lra).
    nra.
  - apply Z.ltb_ge in K. destruct (Z.eq_dec k 0) as [-> | K0]; [lia|].
    assert (K' : (IZR k < 0)%R) by (apply IZR_lt; lia).
    apply IZR_le in Hk. rewrite mult_IZR, plus_IZR in Hk.
    (* [k ln x > k (g + 1) ln 2 >= 1024 ln 2], as [k < 0]. *)
    assert (A : (0 <= - IZR k * ((IZR g + 1) * ln 2 - ln (B2R x)))%R)
      by (apply Rmult_le_pos; lra).
    assert (B : (0 <= ln 2 * ((IZR g + 1) * IZR k - 1024))%R) by (apply Rmult_le_pos; lra).
    nra. }
destruct H as [H | H]; [left; apply exp_increasing; exact H | right; rewrite H; reflexivity].
Qed.

(** [0 < x^k < 2^-1074] where the rule of underflow applies. *)
Lemma pown_under_bound :
  forall x k,
  is_finite x = true -> (0 < B2R x)%R ->
  (if 0 <? k then (DyadicPow.expo x + 1) * k else DyadicPow.expo x * k) <= -1075 ->
  (0 < powerRZ (B2R x) k < bpow radix2 (-1074))%R.
Proof.
intros x k Fx Hx Hk.
split; [apply powerRZ_lt; exact Hx|].
destruct (pown_ln_expo x Fx Hx) as [L1 L2]. pose proof pown_ln2_pos as P.
rewrite powerRZ_Rpower by exact Hx. unfold Rpower. rewrite bpow_exp2.
apply exp_increasing.
set (g := DyadicPow.expo x) in *.
destruct (0 <? k) eqn:K.
- apply Z.ltb_lt, IZR_lt in K. apply IZR_le in Hk. rewrite mult_IZR, plus_IZR in Hk.
  (* [k ln x < k (g + 1) ln 2 <= -1075 ln 2 < -1074 ln 2]. *)
  assert (A : (0 < IZR k * ((IZR g + 1) * ln 2 - ln (B2R x)))%R) by (apply Rmult_lt_0_compat; lra).
  assert (B : (0 <= ln 2 * (-1075 - (IZR g + 1) * IZR k))%R) by (apply Rmult_le_pos; lra).
  nra.
- apply Z.ltb_ge in K. destruct (Z.eq_dec k 0) as [-> | K0]; [lia|].
  assert (K' : (IZR k < 0)%R) by (apply IZR_lt; lia).
  apply IZR_le in Hk. rewrite mult_IZR in Hk.
  (* [k ln x <= k g ln 2 <= -1075 ln 2 < -1074 ln 2], as [k < 0]. *)
  assert (A : (0 <= - IZR k * (ln (B2R x) - IZR g * ln 2))%R) by (apply Rmult_le_pos; lra).
  assert (B : (0 <= ln 2 * (-1075 - IZR g * IZR k))%R) by (apply Rmult_le_pos; lra).
  nra.
Qed.

Lemma pown_rule_overflow :
  forall x k (up : bool),
  is_finite x = true -> (0 < B2R x)%R ->
  1024 <= (if 0 <? k then DyadicPow.expo x * k else (DyadicPow.expo x + 1) * k) ->
  mpfr_round f64_format (if up then RNDU else RNDD) (powerRZ (B2R x) k)
    (with_val (DyadicExp.overflow up)).
Proof.
intros x k up Fx Hx Hk. apply rnd_overflow. exact (pown_over_bound x k Fx Hx Hk).
Qed.

Lemma pown_rule_underflow :
  forall x k (up : bool),
  is_finite x = true -> (0 < B2R x)%R ->
  (if 0 <? k then (DyadicPow.expo x + 1) * k else DyadicPow.expo x * k) <= -1075 ->
  mpfr_round f64_format (if up then RNDU else RNDD) (powerRZ (B2R x) k)
    (with_val (DyadicExp.underflow up)).
Proof.
intros x k up Fx Hx Hk. apply rnd_underflow. exact (pown_under_bound x k Fx Hx Hk).
Qed.

(** A positive [f64] lies in [[2^-1074, 2^1024)], which the bounds of the
    two rules leave. *)
Lemma pown_rule_not_exact :
  forall x k (v : f64),
  is_finite x = true -> (0 < B2R x)%R -> is_finite v = true ->
  1024 <= (if 0 <? k then DyadicPow.expo x * k else (DyadicPow.expo x + 1) * k) \/
  (if 0 <? k then (DyadicPow.expo x + 1) * k else DyadicPow.expo x * k) <= -1075 ->
  powerRZ (B2R x) k <> B2R v.
Proof.
intros x k v Fx Hx Fv H E.
assert (Pv : (0 < B2R v)%R) by (rewrite <- E; apply powerRZ_lt; exact Hx).
destruct H as [H | H].
- pose proof (pown_over_bound x k Fx Hx H) as B.
  pose proof (abs_B2R_lt_emax _ _ v) as A. rewrite Rabs_pos_eq in A by lra. lra.
- pose proof (pown_under_bound x k Fx Hx H) as B.
  assert (M : (bpow radix2 (-1074) <= B2R v)%R).
  { apply (generic_format_ge_bpow radix2 (SpecFloat.fexp 53 1024));
      [| exact Pv | apply generic_format_B2R].
    intros e. unfold SpecFloat.fexp, SpecFloat.emin. lia. }
  lra.
Qed.

(** ** [pown_pos] *)

Lemma pown_pos_correct :
  forall x k (up : bool) v,
  is_finite x = true -> (0 < B2R x)%R -> k <> 0 -> is_i32 k ->
  DyadicPow.pown_pos x k up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (powerRZ (B2R x) k) (with_val v).
Proof.
intros x k up v Fx Hx Hk Hi E.
assert (Z : forall start, Dyadic.ziv (DyadicPow.ev_pown x k) up start = Some v ->
            mpfr_round f64_format (if up then RNDU else RNDD) (powerRZ (B2R x) k) (with_val v)).
{ intros start Hz. apply (ziv_correct (DyadicPow.ev_pown x k) up start _ v); [| exact Hz].
  intros n a Hn Ea. exact (ev_pown_correct x k n a Hn Fx Hx Hk Hi Ea). }
unfold DyadicPow.pown_pos in E. cbv zeta in E.
destruct (0 <? k) eqn:K; cbv beta iota in E.
- destruct (1024 <=? DyadicPow.expo x * k) eqn:O.
  + injection E as <-. apply pown_rule_overflow; [exact Fx | exact Hx |].
    rewrite K. apply Z.leb_le. exact O.
  + destruct ((DyadicPow.expo x + 1) * k <=? -1075) eqn:U.
    * injection E as <-. apply pown_rule_underflow; [exact Fx | exact Hx |].
      rewrite K. apply Z.leb_le. exact U.
    * exact (Z _ E).
- destruct (1024 <=? (DyadicPow.expo x + 1) * k) eqn:O.
  + injection E as <-. apply pown_rule_overflow; [exact Fx | exact Hx |].
    rewrite K. apply Z.leb_le. exact O.
  + destruct (DyadicPow.expo x * k <=? -1075) eqn:U.
    * injection E as <-. apply pown_rule_underflow; [exact Fx | exact Hx |].
      rewrite K. apply Z.leb_le. exact U.
    * exact (Z _ E).
Qed.

Lemma pown_pos_exact :
  forall x k (up : bool) (v : f64),
  is_finite x = true -> (0 < B2R x)%R -> k <> 0 -> is_i32 k ->
  is_finite v = true -> powerRZ (B2R x) k = B2R v ->
  DyadicPow.pown_pos x k up = Some v.
Proof.
intros x k up v Fx Hx Hk Hi Fv Hv.
assert (Nv : B2R v <> 0%R) by (rewrite <- Hv; apply Rgt_not_eq, powerRZ_lt; exact Hx).
assert (Hz : forall start, (start <= 64)%nat ->
             Dyadic.ziv (DyadicPow.ev_pown x k) up start = Some v).
{ intros start Hs. apply ziv_exact; [exact Fv | exact Nv | exact Hs |].
  intros n Hn. exact (ev_pown_exact x k n v Hn Fx Hx Hk Hi Fv Hv). }
unfold DyadicPow.pown_pos. cbv zeta.
destruct (0 <? k) eqn:K; cbv beta iota.
- destruct (1024 <=? DyadicPow.expo x * k) eqn:O.
  + exfalso. apply (pown_rule_not_exact x k v Fx Hx Fv); [| exact Hv].
    left. rewrite K. apply Z.leb_le. exact O.
  + destruct ((DyadicPow.expo x + 1) * k <=? -1075) eqn:U.
    * exfalso. apply (pown_rule_not_exact x k v Fx Hx Fv); [| exact Hv].
      right. rewrite K. apply Z.leb_le. exact U.
    * apply Hz. destruct (2 ^ DyadicPow.pown_start_bits <=? Z.abs k); lia.
- destruct (1024 <=? (DyadicPow.expo x + 1) * k) eqn:O.
  + exfalso. apply (pown_rule_not_exact x k v Fx Hx Fv); [| exact Hv].
    left. rewrite K. apply Z.leb_le. exact O.
  + destruct (DyadicPow.expo x * k <=? -1075) eqn:U.
    * exfalso. apply (pown_rule_not_exact x k v Fx Hx Fv); [| exact Hv].
      right. rewrite K. apply Z.leb_le. exact U.
    * apply Hz. destruct (2 ^ DyadicPow.pown_start_bits <=? Z.abs k); lia.
Qed.

(** ** Helpers of [pown_dir] *)

(** [n % 2 != 0] of the Rust is [Z.odd n]. *)
Lemma pown_odd_rem : forall n, negb (Z.rem n 2 =? 0) = Z.odd n.
Proof. intros n. symmetry. apply Zquot.Zodd_rem. Qed.

Lemma pown_dir_zero_pos :
  forall s n up, 0 < n ->
  DyadicPow.pown_dir (B754_zero s) n up = Some (B754_zero (s && Z.odd n)).
Proof.
intros s n up Hn. unfold DyadicPow.pown_dir.
rewrite (proj2 (Z.eqb_neq n 0)) by lia. rewrite (proj2 (Z.ltb_ge n 0)) by lia.
rewrite pown_odd_rem.
destruct s, (Z.odd n); reflexivity.
Qed.

(** At a finite [x <> 0] and [n <> 0], [pown_dir] calls [pown_pos]. *)
Lemma pown_dir_nonzero :
  forall x n up, is_finite x = true -> B2R x <> 0%R -> n <> 0 ->
  DyadicPow.pown_dir x n up =
  if Bsign x && Z.odd n then
    match DyadicPow.pown_pos (opp x) n (negb up) with Some v => Some (opp v) | None => None end
  else DyadicPow.pown_pos (fabs x) n up.
Proof.
intros x n up Fx Nx Hn.
destruct x as [s|s| |s m e B]; try discriminate Fx; [destruct (Nx eq_refl)|].
unfold DyadicPow.pown_dir.
rewrite (proj2 (Z.eqb_neq n 0) Hn).
replace infinity with (@B754_infinity 53 1024 false) by (vm_compute; reflexivity).
replace DyadicExp.neg_infinity with (@B754_infinity 53 1024 true) by (vm_compute; reflexivity).
rewrite pown_odd_rem.
destruct s; reflexivity.
Qed.

Lemma pown_sign_B2R :
  forall x : f64, is_finite x = true -> B2R x <> 0%R ->
  if Bsign x then (B2R x < 0)%R else (0 < B2R x)%R.
Proof.
intros [s|s| |s m e B] Fx Nx; try discriminate Fx; [destruct (Nx eq_refl)|].
destruct s; cbn [Bsign B2R].
- apply F2R_lt_0. cbn. lia.
- apply F2R_gt_0. cbn. lia.
Qed.

Lemma pown_pow_opp : forall r j, ((- r) ^ j = if Nat.odd j then - r ^ j else r ^ j)%R.
Proof.
intros r j. induction j as [|j IH]; [reflexivity|].
change ((- r) ^ S j)%R with (- r * (- r) ^ j)%R. change (r ^ S j)%R with (r * r ^ j)%R.
rewrite IH, Nat.odd_succ, <- Nat.negb_odd.
destruct (Nat.odd j); cbn [negb]; ring.
Qed.

Lemma pown_odd_nat : forall j, Z.odd (Z.of_nat j) = Nat.odd j.
Proof.
induction j as [|j IH]; [reflexivity|].
rewrite Nat2Z.inj_succ, Z.odd_succ, Nat.odd_succ, <- Z.negb_odd, <- Nat.negb_odd, IH.
reflexivity.
Qed.

Lemma pown_powerRZ_opp :
  forall r n, powerRZ (- r) n = (if Z.odd n then - powerRZ r n else powerRZ r n)%R.
Proof.
intros r [|p|p]; cbn [powerRZ]; [reflexivity| |change (Z.odd (Zneg p)) with (Z.odd (Zpos p))];
  replace (Z.odd (Zpos p)) with (Nat.odd (Pos.to_nat p))
    by (rewrite <- pown_odd_nat, positive_nat_Z; reflexivity);
  rewrite pown_pow_opp; destruct (Nat.odd (Pos.to_nat p)); try reflexivity.
apply Rinv_opp.
Qed.

(** Where [pown_dir] calls [pown_pos] of [|x|], [|x|^n = x^n]. *)
Lemma pown_abs_pow :
  forall (x : f64) n, is_finite x = true -> B2R x <> 0%R -> Bsign x && Z.odd n = false ->
  powerRZ (Rabs (B2R x)) n = powerRZ (B2R x) n.
Proof.
intros x n Fx Nx S. pose proof (pown_sign_B2R x Fx Nx) as Sx.
revert Sx S. destruct (Bsign x); cbn [andb]; intros Sx S.
- rewrite Rabs_left by exact Sx. rewrite pown_powerRZ_opp, S. reflexivity.
- rewrite Rabs_pos_eq by lra. reflexivity.
Qed.

(** Where [pown_dir] negates [pown_pos] of [-x], [(-x)^n = -x^n]. *)
Lemma pown_neg_pow :
  forall (x : f64) n, is_finite x = true -> B2R x <> 0%R -> Bsign x && Z.odd n = true ->
  (B2R x < 0)%R /\ powerRZ (- B2R x) n = (- powerRZ (B2R x) n)%R.
Proof.
intros x n Fx Nx S. apply andb_prop in S as [S1 S2].
pose proof (pown_sign_B2R x Fx Nx) as Sx. rewrite S1 in Sx.
split; [exact Sx|]. rewrite pown_powerRZ_opp, S2. reflexivity.
Qed.

(** [ParseRound.mpfr_round_up_opp] the other way round: the negation of
    [-v] rounded down is [v] rounded up. *)
Lemma mpfr_round_down_opp :
  forall v w, mpfr_round f64_format RNDD (- v) (with_val w) ->
  mpfr_round f64_format RNDU v (with_val (opp w)).
Proof.
intros v w H.
destruct (is_finite w) eqn:Fw.
- assert (Fo : is_finite (opp w) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fw).
  assert (Ro : (B2R (opp w) = - B2R w)%R) by apply B2R_Bopp.
  destruct (Req_dec (B2R w) 0%R) as [E0|N0].
  + destruct (ParseRound.with_val_zero w Fw E0) as (s & Es). rewrite Es in H. cbn [mpfr_round] in H.
    assert (E0' : B2R (opp w) = 0%R) by (rewrite Ro, E0; apply Ropp_0).
    destruct (ParseRound.with_val_zero _ Fo E0') as (s' & ->). cbn [mpfr_round].
    pose proof (Rnd_UP_pt_opp _ ParseRound.f64_format_opp _ _ H) as H'.
    rewrite Ropp_involutive, Ropp_0 in H'. exact H'.
  + rewrite (with_val_finite w Fw N0) in H. cbn [mpfr_round] in H. destruct H as (_ & H).
    assert (N0' : B2R (opp w) <> 0%R) by (rewrite Ro; lra).
    rewrite (with_val_finite _ Fo N0'). cbn [mpfr_round]. split; [exact N0'|].
    rewrite Ro. pose proof (Rnd_UP_pt_opp _ ParseRound.f64_format_opp _ _ H) as H'.
    rewrite Ropp_involutive in H'. exact H'.
- destruct w as [s|[|]| |s m e B]; try discriminate Fw;
    cbn [opp Bopp with_val mpfr_round negb] in *; try contradiction.
  intros g Fg. pose proof (H _ (ParseRound.f64_format_opp _ Fg)). lra.
Qed.

(** The negation of [-r] rounded in the direction [negb up] is [r]
    rounded in the direction [up]. *)
Lemma pown_rnd_opp :
  forall (up : bool) r w,
  mpfr_round f64_format (if negb up then RNDU else RNDD) (- r) (with_val w) ->
  mpfr_round f64_format (if up then RNDU else RNDD) r (with_val (opp w)).
Proof.
intros [|] r w H; cbn [negb] in H.
- exact (mpfr_round_down_opp r w H).
- exact (ParseRound.mpfr_round_up_opp r w H).
Qed.

(** ** The special values of [pown_dir] *)

Lemma pown_dir_zero_neg :
  forall s n up, n < 0 ->
  DyadicPow.pown_dir (B754_zero s) n up = Some (B754_infinity (s && Z.odd n)).
Proof.
intros s n up Hn. unfold DyadicPow.pown_dir.
rewrite (proj2 (Z.eqb_neq n 0)) by lia. rewrite (proj2 (Z.ltb_lt n 0) Hn).
replace infinity with (@B754_infinity 53 1024 false) by (vm_compute; reflexivity).
rewrite pown_odd_rem.
destruct s, (Z.odd n); reflexivity.
Qed.

Lemma pown_dir_inf :
  forall s n up, n <> 0 ->
  DyadicPow.pown_dir (B754_infinity s) n up =
  Some (if n <? 0 then B754_zero (s && Z.odd n) else B754_infinity (s && Z.odd n)).
Proof.
intros s n up Hn. unfold DyadicPow.pown_dir.
rewrite (proj2 (Z.eqb_neq n 0) Hn).
replace infinity with (@B754_infinity 53 1024 false) by (vm_compute; reflexivity).
replace DyadicExp.neg_infinity with (@B754_infinity 53 1024 true) by (vm_compute; reflexivity).
rewrite pown_odd_rem.
destruct s, (n <? 0), (Z.odd n); reflexivity.
Qed.

Theorem pown_dir_correct :
  forall x n (up : bool) v,
  is_i32 n -> is_finite x = true -> pown_dom n (B2R x) ->
  DyadicPow.pown_dir x n up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (powerRZ (B2R x) n) (with_val v).
Proof.
intros x n up v Hi Fx Hd E.
destruct (Z.eq_dec n 0) as [-> | Hn].
- change (DyadicPow.pown_dir x 0 up) with (Some DyadicExp.one) in E. injection E as <-.
  cbn [powerRZ]. apply rnd_exact; [exact (proj1 one_B2R) | exact (proj2 one_B2R)].
- destruct (Req_dec (B2R x) 0%R) as [Z0 | Nx].
  + (* [x = +-0]: the domain gives [n > 0], and [x^n = 0]. *)
    assert (Pn : 0 < n) by (destruct Hd as [Hd | Hd]; [lia | contradiction]).
    destruct x as [s|s| |s m e B]; try discriminate Fx.
    2: { exfalso. revert Z0. cbn [B2R]. apply F2R_neq_0. cbn [Fnum]. destruct s; discriminate. }
    rewrite pown_dir_zero_pos in E by exact Pn. injection E as <-.
    cbn [B2R]. destruct n as [|p|p]; try lia. cbn [powerRZ].
    rewrite pow_i by apply Pos2Nat.is_pos.
    cbn [with_val]. apply mpfr_round_zero. exists zero. split; reflexivity.
  + rewrite (pown_dir_nonzero x n up Fx Nx Hn) in E.
    assert (Fo : is_finite (opp x) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fx).
    assert (Ro : (B2R (opp x) = - B2R x)%R) by apply B2R_Bopp.
    assert (Fa : is_finite (fabs x) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fx).
    assert (Ra : B2R (fabs x) = Rabs (B2R x)) by apply B2R_Babs.
    destruct (Bsign x && Z.odd n) eqn:S.
    * (* [x < 0] and an odd [n]: [x^n = -(-x)^n], rounded the other way. *)
      destruct (pown_neg_pow x n Fx Nx S) as [Sx Hp].
      destruct (DyadicPow.pown_pos (opp x) n (negb up)) as [w|] eqn:P; [|discriminate E].
      injection E as <-. apply pown_rnd_opp. rewrite <- Hp, <- Ro.
      apply (pown_pos_correct (opp x) n (negb up) w Fo);
        [rewrite Ro; lra | exact Hn | exact Hi | exact P].
    * (* Otherwise [x^n = |x|^n]. *)
      pose proof (pown_pos_correct (fabs x) n up v Fa) as H.
      rewrite Ra, (pown_abs_pow x n Fx Nx S) in H.
      apply H; [apply Rabs_pos_lt; exact Nx | exact Hn | exact Hi | exact E].
Qed.

Theorem pown_dir_exact :
  forall x n (v : f64) (up : bool),
  is_i32 n -> is_finite x = true -> B2R x <> 0%R -> is_finite v = true ->
  powerRZ (B2R x) n = B2R v ->
  DyadicPow.pown_dir x n up = Some v.
Proof.
intros x n v up Hi Fx Nx Fv E.
destruct (Z.eq_dec n 0) as [-> | Hn].
- change (DyadicPow.pown_dir x 0 up) with (Some DyadicExp.one). f_equal.
  cbn [powerRZ] in E.
  apply B2R_inj; [vm_compute; reflexivity | |].
  + destruct v as [s|s| |s m e B]; try discriminate Fv; [|reflexivity].
    exfalso. cbn [B2R] in E. lra.
  + rewrite (proj2 one_B2R). exact E.
- rewrite (pown_dir_nonzero x n up Fx Nx Hn).
  assert (Fo : is_finite (opp x) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fx).
  assert (Ro : (B2R (opp x) = - B2R x)%R) by apply B2R_Bopp.
  assert (Fa : is_finite (fabs x) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fx).
  assert (Ra : B2R (fabs x) = Rabs (B2R x)) by apply B2R_Babs.
  destruct (Bsign x && Z.odd n) eqn:S.
  + destruct (pown_neg_pow x n Fx Nx S) as [Sx Hp].
    rewrite (pown_pos_exact (opp x) n (negb up) (opp v)).
    * f_equal. unfold opp. apply Bopp_involutive.
    * exact Fo.
    * rewrite Ro. lra.
    * exact Hn.
    * exact Hi.
    * unfold opp. rewrite is_finite_Bopp. exact Fv.
    * rewrite Ro, Hp, E. symmetry. apply B2R_Bopp.
  + apply pown_pos_exact; [exact Fa | | exact Hn | exact Hi | exact Fv |].
    * rewrite Ra. apply Rabs_pos_lt. exact Nx.
    * rewrite Ra, (pown_abs_pow x n Fx Nx S). exact E.
Qed.
