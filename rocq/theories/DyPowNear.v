(** * The powers of the dyadic kernel rounded to nearest

    [pow_near_with ziv_near_strict] and [pown_near_with ziv_near_strict]
    of [DyadicPow] return, where they return, x^y and x^n at finite
    arguments of their domains rounded to nearest as [near_round] says:
    the loop by [ziv_near_strict_correct] and the enclosures of
    [DyPowCore.v] and [DyPown.v], the rules before it by the cells of
    [NearCells.v] and the bounds of [DyPowRules.v], and [exact_near] by
    [exact_near_sound] of [DyPowNearExact.v]. As [exact_near] returns at
    every finite [x > 0] other than 1 and finite [y <> 0] at which x^y
    is q 2^e for an integer [0 < q < 2^54] and [e >= -1075], below
    2^1024 ([exact_near_complete]), and the rules before it return at
    [x = 1] and [y = 0], [pow_near] returns the rounding to nearest at
    every finite [x > 0] and finite [y] at which x^y is such a number
    ([pow_near_midpoint]), the midpoints of two adjacent [f64]s among
    them, which an enclosure settles only if it is one of its bounds. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr MpfrRound Limbs Elementary DyRound DyConv DyOps DyDriver
  DyGrow DyConst DyExpCore DyExpRules DyExp DyLogRules DyLogCore DyPowArith DyPowRules
  DyPowExact DyPowCore NearF64 NearCells DyDriverNear DyPowNearExact.
From Inari Require DyPown DyPow FastPow.

Open Scope Z_scope.

(** ** Bounds and cells *)

(** A finite [f64] rounds to itself, whatever real names its value. *)
Local Lemma near_of : forall (w : f64) r, is_finite w = true -> B2R w = r -> near_round r w.
Proof. intros w r Fw <-. exact (near_exact w Fw). Qed.

Local Lemma exp_le : forall r t, (r <= t)%R -> (exp r <= exp t)%R.
Proof.
intros r t [H | ->]; [left; apply exp_increasing; exact H | right; reflexivity].
Qed.

(** For [|y| < 2^-54], [1 - 2^-54 < 1 + y <= exp y], and for [y > 0],
    [exp y * (1 - y) < exp y * exp (-y) = 1], so [exp y < 1 + y exp y <
    1 + 2^-53], as [exp_tiny_near] of [DyExpNear.v]. *)
Local Lemma exp_tiny_near :
  forall y, (Rabs y < bpow radix2 (-54) ->
  1 - bpow radix2 (-54) <= exp y <= 1 + bpow radix2 (-53))%R.
Proof.
intros y Hy.
assert (Hb : (bpow radix2 (-53) = 2 * bpow radix2 (-54) /\ 0 < bpow radix2 (-54) < 1 / 1000)%R)
  by (cbn [bpow radix_val radix2]; lra).
apply Rabs_def2 in Hy as [Hy1 Hy2].
pose proof (exp_ineq1_le y) as Hl.
split; [lra|].
destruct (Rlt_or_le 0 y) as [Hp|Hn].
- assert (Hm : (1 + - y < exp (- y))%R) by (apply exp_ineq1; lra).
  assert (Hpr : (exp y * exp (- y) = 1)%R)
    by (rewrite <- exp_plus, Rplus_opp_r; exact exp_0).
  assert (He : (0 < exp y)%R) by apply exp_pos.
  assert (H1 : (exp y * (1 - y) < 1)%R) by (rewrite <- Hpr; apply Rmult_lt_compat_l; lra).
  assert (H2 : (exp y < 2)%R) by nra.
  assert (H3 : (exp y * y < 2 * bpow radix2 (-54))%R) by nra.
  lra.
- assert (Hu : (exp y <= exp 0)%R) by (apply exp_le; lra).
  rewrite exp_0 in Hu. lra.
Qed.

(** [x^k >= 2^1024] where the rule of overflow of [pown_pos_near]
    applies ([DyPown.pown_over_bound]). *)
Local Lemma pown_inf_near :
  forall x k,
  is_finite x = true -> (0 < B2R x)%R ->
  1024 <= (if 0 <? k then DyadicPow.expo x * k else (DyadicPow.expo x + 1) * k) ->
  near_round (powerRZ (B2R x) k) infinity.
Proof.
intros x k Fx Hx Hk. apply near_inf.
pose proof (DyPown.pown_over_bound x k Fx Hx Hk). pose proof (bpow_gt_0 radix2 970). lra.
Qed.

(** [0 < x^k <= 2^-1075] where the rule of underflow of [pown_pos_near]
    applies: the proof of [DyPown.pown_under_bound] shows
    [k ln x <= -1075 ln 2]. *)
Local Lemma pown_zero_near :
  forall x k,
  is_finite x = true -> (0 < B2R x)%R ->
  (if 0 <? k then (DyadicPow.expo x + 1) * k else DyadicPow.expo x * k) <= -1075 ->
  near_round (powerRZ (B2R x) k) zero.
Proof.
intros x k Fx Hx Hk. apply near_zero.
split; [apply powerRZ_lt; exact Hx|].
destruct (DyPown.pown_ln_expo x Fx Hx) as [L1 L2]. pose proof DyPown.pown_ln2_pos as P.
rewrite powerRZ_Rpower by exact Hx. unfold Rpower. rewrite bpow_exp2.
apply exp_le.
set (g := DyadicPow.expo x) in *.
destruct (0 <? k) eqn:K.
- apply Z.ltb_lt, IZR_lt in K. apply IZR_le in Hk. rewrite mult_IZR, plus_IZR in Hk.
  (* [k ln x < k (g + 1) ln 2 <= -1075 ln 2]. *)
  assert (A : (0 < IZR k * ((IZR g + 1) * ln 2 - ln (B2R x)))%R)
    by (apply Rmult_lt_0_compat; lra).
  assert (B : (0 <= ln 2 * (-1075 - (IZR g + 1) * IZR k))%R) by (apply Rmult_le_pos; lra).
  nra.
- apply Z.ltb_ge in K. destruct (Z.eq_dec k 0) as [-> | K0]; [lia|].
  assert (K' : (IZR k < 0)%R) by (apply IZR_lt; lia).
  apply IZR_le in Hk. rewrite mult_IZR in Hk.
  (* [k ln x <= k g ln 2 <= -1075 ln 2], as [k < 0]. *)
  assert (A : (0 <= - IZR k * (ln (B2R x) - IZR g * ln 2))%R) by (apply Rmult_le_pos; lra).
  assert (B : (0 <= ln 2 * (-1075 - IZR g * IZR k))%R) by (apply Rmult_le_pos; lra).
  nra.
Qed.

(** ** [pown_pos_near] *)

Local Lemma pown_pos_near :
  forall x k v,
  is_finite x = true -> (0 < B2R x)%R -> k <> 0 -> is_i32 k ->
  DyadicPow.pown_pos_near_with ziv_near_strict x k = Some v ->
  near_round (powerRZ (B2R x) k) v.
Proof.
intros x k v Fx Hx Hk Hi E.
assert (Hl : forall start, ziv_near_strict (DyadicPow.ev_pown x k) start = Some v ->
             near_round (powerRZ (B2R x) k) v).
{ intros start H. refine (ziv_near_strict_correct _ _ _ _ _ H).
  intros n a Hn Ea. exact (DyPown.ev_pown_correct x k n a Hn Fx Hx Hk Hi Ea). }
(* The fast path, then the driver. *)
assert (Hm : forall start,
  match DyadicPow.fast_pow_near false x (DyadicPow.of_i64 k) with
  | Some r => Some r
  | None => ziv_near_strict (DyadicPow.ev_pown x k) start
  end = Some v -> near_round (powerRZ (B2R x) k) v).
{ intros start. destruct (DyadicPow.fast_pow_near false x (DyadicPow.of_i64 k)) eqn:F.
  - intros H. injection H as <-.
    destruct (DyPown.pown_fast_hyp x k Fx Hx Hk Hi) as (Fk & Vk & H).
    rewrite (powerRZ_Rpower _ _ Hx), <- Vk.
    exact (FastPow.fast_pow_near_correct false x _ _ Fx Hx Fk H F).
  - exact (Hl start). }
unfold DyadicPow.pown_pos_near_with in E. cbv zeta in E.
destruct (0 <? k) eqn:K; cbv beta iota in E.
- destruct (1024 <=? DyadicPow.expo x * k) eqn:O.
  + injection E as <-. apply pown_inf_near; [exact Fx | exact Hx |].
    rewrite K. apply Z.leb_le. exact O.
  + destruct ((DyadicPow.expo x + 1) * k <=? -1075) eqn:U.
    * injection E as <-. apply pown_zero_near; [exact Fx | exact Hx |].
      rewrite K. apply Z.leb_le. exact U.
    * exact (Hm _ E).
- destruct (1024 <=? (DyadicPow.expo x + 1) * k) eqn:O.
  + injection E as <-. apply pown_inf_near; [exact Fx | exact Hx |].
    rewrite K. apply Z.leb_le. exact O.
  + destruct (DyadicPow.expo x * k <=? -1075) eqn:U.
    * injection E as <-. apply pown_zero_near; [exact Fx | exact Hx |].
      rewrite K. apply Z.leb_le. exact U.
    * exact (Hm _ E).
Qed.

(** Where [pown_pos_near_with ziv_near_strict] returns, [pown_pos_near]
    returns the same. *)
Local Lemma pown_pos_near_strict :
  forall x k v,
  DyadicPow.pown_pos_near_with ziv_near_strict x k = Some v ->
  DyadicPow.pown_pos_near_with Dyadic.ziv_near x k = Some v.
Proof.
intros x k v. unfold DyadicPow.pown_pos_near_with. cbv zeta.
destruct (0 <? k); cbv beta iota.
- destruct (1024 <=? DyadicPow.expo x * k); [exact (fun h => h) |].
  destruct ((DyadicPow.expo x + 1) * k <=? -1075); [exact (fun h => h) |].
  destruct (DyadicPow.fast_pow_near false x (DyadicPow.of_i64 k));
    [exact (fun h => h) | apply ziv_near_strict_ziv].
- destruct (1024 <=? (DyadicPow.expo x + 1) * k); [exact (fun h => h) |].
  destruct (DyadicPow.expo x * k <=? -1075); [exact (fun h => h) |].
  destruct (DyadicPow.fast_pow_near false x (DyadicPow.of_i64 k));
    [exact (fun h => h) | apply ziv_near_strict_ziv].
Qed.

(** ** Helpers of [pown_near], as [DyPown.pown_dir_zero_pos] and
    [DyPown.pown_dir_nonzero] of [pown_dir] *)

Local Lemma pown_near_zero_pos :
  forall z s n, 0 < n ->
  DyadicPow.pown_near_with z (B754_zero s) n = Some (B754_zero (s && Z.odd n)).
Proof.
intros z s n Hn. unfold DyadicPow.pown_near_with.
rewrite (proj2 (Z.eqb_neq n 0)) by lia. rewrite (proj2 (Z.ltb_ge n 0)) by lia.
rewrite DyPown.pown_odd_rem.
destruct s, (Z.odd n); reflexivity.
Qed.

(** At a finite [x <> 0] and [n <> 0], [pown_near] calls [pown_pos_near]. *)
Local Lemma pown_near_nonzero :
  forall z x n, is_finite x = true -> B2R x <> 0%R -> n <> 0 ->
  DyadicPow.pown_near_with z x n =
  if Bsign x && Z.odd n then
    match DyadicPow.pown_pos_near_with z (opp x) n with Some v => Some (opp v) | None => None end
  else DyadicPow.pown_pos_near_with z (fabs x) n.
Proof.
intros z x n Fx Nx Hn.
destruct x as [s|s| |s m e B]; try discriminate Fx; [destruct (Nx eq_refl)|].
unfold DyadicPow.pown_near_with.
rewrite (proj2 (Z.eqb_neq n 0) Hn).
replace infinity with (@B754_infinity 53 1024 false) by (vm_compute; reflexivity).
replace DyadicExp.neg_infinity with (@B754_infinity 53 1024 true) by (vm_compute; reflexivity).
rewrite DyPown.pown_odd_rem.
destruct s; reflexivity.
Qed.

(** ** The theorems *)

Theorem pow_near_correct :
  forall x y v,
  is_finite x = true -> is_finite y = true -> pow_dom (B2R x) (B2R y) ->
  DyadicPow.pow_near_with ziv_near_strict x y = Some v ->
  near_round (Rpow (B2R x) (B2R y)) v.
Proof.
intros x y v Fx Fy Hd E.
assert (Fz : is_finite zero = true) by reflexivity.
assert (F1 : is_finite DyadicExp.one = true) by exact (proj1 one_B2R).
assert (Hx0 : (0 <= B2R x)%R) by (destruct Hd as [H | [H _]]; lra).
unfold DyadicPow.pow_near_with in E.
destruct (eq y zero) eqn:Y0.
{ cbv iota in E. injection E as <-.
  apply (DyPow.eq_fin y zero Fy Fz) in Y0. change (B2R zero) with 0%R in Y0.
  assert (Px : (0 < B2R x)%R) by (destruct Hd as [H | [_ H]]; lra).
  unfold Rpow. destruct (Rle_dec (B2R x) 0) as [H | _]; [lra |].
  rewrite Y0, (Rpower_O _ Px). exact (near_of _ _ F1 (proj2 one_B2R)). }
rewrite (fin_not_nan x Fx), (fin_not_nan y Fy) in E. cbv iota in E.
destruct (lt x zero) eqn:L.
{ apply (DyPow.lt_fin x zero Fx Fz) in L. change (B2R zero) with 0%R in L. lra. }
destruct (eq x DyadicExp.one) eqn:X1.
{ cbv iota in E. injection E as <-.
  apply (DyPow.eq_fin x _ Fx F1) in X1. rewrite (proj2 one_B2R) in X1.
  unfold Rpow. destruct (Rle_dec (B2R x) 0) as [H | _]; [lra |].
  rewrite X1, DyPow.Rpower_base_1. exact (near_of _ _ F1 (proj2 one_B2R)). }
rewrite (fin_neq_inf y Fy), (fin_neq_ninf y Fy) in E. cbn [orb] in E. cbv iota in E.
destruct (eq x zero) eqn:X0.
{ (* [x = ±0] and [y > 0]: the result is a zero of either sign. *)
  cbv iota zeta in E. injection E as <-.
  apply (DyPow.eq_fin x zero Fx Fz) in X0. change (B2R zero) with 0%R in X0.
  assert (Py : (0 < B2R y)%R) by (destruct Hd as [H | [_ H]]; lra).
  destruct (lt y zero) eqn:Ly.
  { apply (DyPow.lt_fin y zero Fy Fz) in Ly. change (B2R zero) with 0%R in Ly. lra. }
  unfold Rpow. destruct (Rle_dec (B2R x) 0) as [_ | H]; [| lra].
  apply near_of; destruct (Bsign x && DyadicPow.is_odd_integer y); reflexivity. }
rewrite (fin_neq_inf x Fx) in E. cbv iota zeta in E.
apply (DyPow.eq_fin_false x _ Fx F1) in X1. rewrite (proj2 one_B2R) in X1.
apply (DyPow.eq_fin_false y zero Fy Fz) in Y0. change (B2R zero) with 0%R in Y0.
apply (DyPow.eq_fin_false x zero Fx Fz) in X0. change (B2R zero) with 0%R in X0.
assert (Px : (0 < B2R x)%R) by (destruct Hd as [H | [H _]]; lra).
replace (Rpow (B2R x) (B2R y)) with (Rpower (B2R x) (B2R y))
  by (unfold Rpow; destruct (Rle_dec (B2R x) 0) as [H | _]; [lra | reflexivity]).
destruct (pow_rule_bounds x y Fx Px X1 Fy Y0) as ([Hb1 Hb2] & Hpos & Hneg).
destruct (10 <=? DyadicPow.expo y + DyadicPow.ln_expo x) eqn:S1.
{ (* [|y ln x| >= 2^10]: x^y is above 2^1024 or below 2^-1075. *)
  apply Z.leb_le in S1. injection E as <-.
  assert (H10 : (bpow radix2 10 <= bpow radix2 (DyadicPow.expo y + DyadicPow.ln_expo x))%R)
    by (apply bpow_le; exact S1).
  change (bpow radix2 10) with 1024%R in H10.
  unfold Rpower.
  destruct (Bool.eqb (gt y zero) (gt x DyadicExp.one)) eqn:A.
  - specialize (Hpos eq_refl). rewrite Rabs_pos_eq in Hb1 by lra.
    apply near_inf.
    assert (H : (bpow radix2 1024 <= exp (B2R y * ln (B2R x)))%R) by (apply exp_710; lra).
    pose proof (bpow_gt_0 radix2 970). lra.
  - specialize (Hneg eq_refl). rewrite Rabs_left in Hb1 by lra.
    apply near_zero. split; [apply exp_pos|].
    (* [y ln x <= -1024 < -1075 ln 2]. *)
    rewrite bpow_exp2. apply exp_le. pose proof ln2_bounds. lra. }
destruct (DyadicPow.expo y + DyadicPow.ln_expo x <=? -58) eqn:S2.
{ (* [|y ln x| < 2^-54]. *)
  apply Z.leb_le in S2. injection E as <-.
  assert (H54 : (bpow radix2 (DyadicPow.expo y + DyadicPow.ln_expo x + 4) <=
                 bpow radix2 (-54))%R)
    by (apply bpow_le; lia).
  apply near_one. unfold Rpower. apply exp_tiny_near. lra. }
destruct (DyadicPow.exact_near x y) as [[w|]|] eqn:Ex; [| | discriminate E].
- injection E as <-. exact (exact_near_sound x y w Fx Px Fy Y0 Ex).
- cbv beta iota in E.
  destruct (eq (DyadicPow.of_i64 (DyadicPow.to_i32 y)) y) eqn:I.
  + (* An integer [y] from [-2^31] to [2^31 - 1]: x^y is [powerRZ x k] for [k = y]. *)
    assert (Hi : is_i32 (DyadicPow.to_i32 y)) by apply DyPow.to_i32_range.
    destruct (of_i64_exact (DyadicPow.to_i32 y)) as [Fk Vk]; [unfold is_i32 in Hi; lia |].
    apply (DyPow.eq_fin _ _ Fk Fy) in I. rewrite Vk in I.
    assert (Hk : DyadicPow.to_i32 y <> 0)
      by (intros K; apply Y0; rewrite <- I, K; reflexivity).
    rewrite <- I, <- (powerRZ_Rpower _ _ Px).
    exact (pown_pos_near x _ v Fx Px Hk Hi E).
  + (* The fast path, where [|y ln x| >= 2^-57], then the driver. *)
    destruct (DyadicPow.fast_pow_near_call false x y) eqn:F; cbv iota in E.
    { injection E as <-.
      apply (FastPow.fast_pow_near_correct false x y _ Fx Px Fy); [| exact F].
      right. destruct (pow_rule_bounds x y Fx Px X1 Fy Y0) as ([Hb _] & _).
      apply Rle_trans with (2 := Hb). apply bpow_le. apply Z.leb_gt in S2. lia. }
    refine (ziv_near_strict_correct _ _ _ _ _ E).
    intros n a Hn Ea. exact (ev_pow_correct n x y a Hn Fx Px Fy Ea).
Qed.

Theorem pown_near_correct :
  forall x n v,
  is_i32 n -> is_finite x = true -> pown_dom n (B2R x) ->
  DyadicPow.pown_near_with ziv_near_strict x n = Some v ->
  near_round (powerRZ (B2R x) n) v.
Proof.
intros x n v Hi Fx Hd E.
destruct (Z.eq_dec n 0) as [-> | Hn].
- change (DyadicPow.pown_near_with ziv_near_strict x 0) with (Some DyadicExp.one) in E.
  injection E as <-. cbn [powerRZ]. exact (near_of _ _ (proj1 one_B2R) (proj2 one_B2R)).
- destruct (Req_dec (B2R x) 0%R) as [Z0 | Nx].
  + (* [x = +-0]: the domain gives [n > 0], and [x^n = 0]. *)
    assert (Pn : 0 < n) by (destruct Hd as [Hd | Hd]; [lia | contradiction]).
    destruct x as [s|s| |s m e B]; try discriminate Fx.
    2: { exfalso. revert Z0. cbn [B2R]. apply F2R_neq_0. cbn [Fnum]. destruct s; discriminate. }
    rewrite (pown_near_zero_pos ziv_near_strict) in E by exact Pn. injection E as <-.
    cbn [B2R]. destruct n as [|p|p]; try lia. cbn [powerRZ].
    rewrite pow_i by apply Pos2Nat.is_pos.
    apply near_of; reflexivity.
  + rewrite (pown_near_nonzero ziv_near_strict x n Fx Nx Hn) in E.
    assert (Fo : is_finite (opp x) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fx).
    assert (Ro : (B2R (opp x) = - B2R x)%R) by apply B2R_Bopp.
    assert (Fa : is_finite (fabs x) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fx).
    assert (Ra : B2R (fabs x) = Rabs (B2R x)) by apply B2R_Babs.
    destruct (Bsign x && Z.odd n) eqn:S.
    * (* [x < 0] and an odd [n]: [x^n = -(-x)^n]. *)
      destruct (DyPown.pown_neg_pow x n Fx Nx S) as [Sx Hq].
      destruct (DyadicPow.pown_pos_near_with ziv_near_strict (opp x) n) as [w|] eqn:P;
        [|discriminate E].
      injection E as <-.
      rewrite <- (Ropp_involutive (powerRZ (B2R x) n)), <- Hq, <- Ro.
      apply near_opp.
      apply (pown_pos_near (opp x) n w Fo); [rewrite Ro; lra | exact Hn | exact Hi | exact P].
    * (* Otherwise [x^n = |x|^n]. *)
      pose proof (pown_pos_near (fabs x) n v Fa) as H.
      rewrite Ra, (DyPown.pown_abs_pow x n Fx Nx S) in H.
      apply H; [apply Rabs_pos_lt; exact Nx | exact Hn | exact Hi | exact E].
Qed.

Theorem pow_near_strict :
  forall x y v,
  DyadicPow.pow_near_with ziv_near_strict x y = Some v -> DyadicPow.pow_near x y = Some v.
Proof.
intros x y v. unfold DyadicPow.pow_near, DyadicPow.pow_near_with. cbv zeta.
destruct (eq y zero); [exact (fun h => h)|].
destruct (is_nan x); [exact (fun h => h)|].
destruct (is_nan y); [exact (fun h => h)|].
destruct (lt x zero); [exact (fun h => h)|].
destruct (eq x DyadicExp.one); [exact (fun h => h)|].
destruct (eq y infinity || eq y DyadicExp.neg_infinity); [exact (fun h => h)|].
destruct (eq x zero); [exact (fun h => h)|].
destruct (eq x infinity); [exact (fun h => h)|].
destruct (10 <=? DyadicPow.expo y + DyadicPow.ln_expo x); [exact (fun h => h)|].
destruct (DyadicPow.expo y + DyadicPow.ln_expo x <=? -58); [exact (fun h => h)|].
destruct (DyadicPow.exact_near x y) as [[w|]|]; [exact (fun h => h) | | exact (fun h => h)].
cbv beta iota.
destruct (eq (DyadicPow.of_i64 (DyadicPow.to_i32 y)) y); [apply pown_pos_near_strict |].
destruct (DyadicPow.fast_pow_near_call false x y);
  [exact (fun h => h) | apply ziv_near_strict_ziv].
Qed.

Theorem pown_near_strict :
  forall x n v,
  DyadicPow.pown_near_with ziv_near_strict x n = Some v -> DyadicPow.pown_near x n = Some v.
Proof.
intros x n v. unfold DyadicPow.pown_near, DyadicPow.pown_near_with.
destruct (n =? 0); [exact (fun h => h) |].
destruct (is_nan x); [exact (fun h => h) |].
destruct (eq x zero || (eq x infinity || eq x DyadicExp.neg_infinity)); [exact (fun h => h) |].
destruct (lt x zero && negb (Z.rem n 2 =? 0)).
- destruct (DyadicPow.pown_pos_near_with ziv_near_strict (opp x) n) as [w|] eqn:P;
    [| intros H; discriminate H].
  rewrite (pown_pos_near_strict _ _ _ P). exact (fun h => h).
- apply pown_pos_near_strict.
Qed.

Theorem pow_near_midpoint :
  forall x y q e,
  is_finite x = true -> (0 < B2R x)%R -> is_finite y = true ->
  0 < q < 2 ^ 54 -> -1075 <= e -> e + Z.log2 q <= 1023 ->
  Rpower (B2R x) (B2R y) = (IZR q * bpow radix2 e)%R ->
  exists v, DyadicPow.pow_near x y = Some v /\ near_round (Rpower (B2R x) (B2R y)) v.
Proof.
intros x y q e Fx Px Fy Hq He Hl Hv.
assert (Fz : is_finite zero = true) by reflexivity.
assert (F1 : is_finite DyadicExp.one = true) by exact (proj1 one_B2R).
(* The rules before [exact_near] return, and [exact_near] returns at x^y. *)
assert (Ex : exists v, DyadicPow.pow_near_with ziv_near_strict x y = Some v).
{ unfold DyadicPow.pow_near_with.
  destruct (eq y zero) eqn:Y0; [eexists; reflexivity |].
  rewrite (fin_not_nan x Fx), (fin_not_nan y Fy).
  rewrite (DyPow.lt_false_of x zero Fx Fz) by (change (B2R zero) with 0%R; lra).
  destruct (eq x DyadicExp.one) eqn:X1; [eexists; reflexivity |].
  rewrite (fin_neq_inf y Fy), (fin_neq_ninf y Fy). cbn [orb].
  rewrite (DyPow.eq_false_of x zero Fx Fz) by (change (B2R zero) with 0%R; lra).
  rewrite (fin_neq_inf x Fx). cbv iota zeta.
  destruct (10 <=? DyadicPow.expo y + DyadicPow.ln_expo x); [eexists; reflexivity |].
  destruct (DyadicPow.expo y + DyadicPow.ln_expo x <=? -58); [eexists; reflexivity |].
  apply (DyPow.eq_fin_false x _ Fx F1) in X1. rewrite (proj2 one_B2R) in X1.
  apply (DyPow.eq_fin_false y zero Fy Fz) in Y0. change (B2R zero) with 0%R in Y0.
  destruct (exact_near_complete x y q e Fx Px X1 Fy Y0 Hq He Hl Hv) as [w Ew].
  rewrite Ew. eexists; reflexivity. }
destruct Ex as [v Ev]. exists v. split; [exact (pow_near_strict x y v Ev) |].
pose proof (pow_near_correct x y v Fx Fy (or_introl Px) Ev) as H.
unfold Rpow in H. destruct (Rle_dec (B2R x) 0) as [H0 | _]; [lra | exact H].
Qed.
