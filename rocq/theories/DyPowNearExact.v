(** * The exact powers of the dyadic kernel rounded to nearest

    [exact_near] of [DyadicPow] returns, where it returns a value, x^y
    rounded to nearest as [near_round] says, by the integers of
    [DyPowArith.v] and [DyPowExact.v] ([exact_near_sound]). It returns at
    every finite [x > 0] other than 1 and finite [y <> 0] at which x^y
    is q 2^e for an integer [0 < q < 2^54] and [e >= -1075], below
    2^1024 ([exact_near_complete]): the [f64]s and the midpoints of two
    adjacent [f64]s, which an enclosure settles only if it is one of its
    bounds. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr MpfrRound Limbs Elementary DyRound DyConv DyOps DyDriver
  DyGrow DyConst DyExpCore DyExpRules DyExp DyLogRules DyLogCore DyPowArith DyPowRules
  DyPowExact DyPowCore NearF64 NearCells DyConvNear DyDriverNear.

Open Scope Z_scope.

(** ** The steps that differ from [exact]

    [exact_near] is [exact] with the bound [2^54] in [small_power_near],
    the lower bound [-1075] of the range check, and a last step that
    rounds [q 2^e] to nearest. These are the lemmas of [DyPowExact.v]
    with those bounds; the others are used as they are. *)

(** [small_power_near_loop f r q] is [q r^f] while that stays below
    [2^54], as [small_power_loop_spec] with [2^53]. *)
Local Lemma small_power_near_loop_spec :
  forall f r q t, 1 <= r -> 0 <= q < 2 ^ 54 ->
  (DyadicPow.small_power_near_loop f r q = Some t <->
   t = q * r ^ Z.of_nat f /\ q * r ^ Z.of_nat f < 2 ^ 54).
Proof.
induction f as [|f IH]; intros r q t Hr Hq; cbn [DyadicPow.small_power_near_loop].
- rewrite Z.pow_0_r, Z.mul_1_r. split.
  + intros H. injection H as <-. lia.
  + intros [-> _]. reflexivity.
- assert (Hp : 0 < r ^ Z.of_nat f) by (apply Z.pow_pos_nonneg; lia).
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  destruct (2 ^ 54 <=? q * r) eqn:B.
  + apply Z.leb_le in B. split; [discriminate | intros [_ H]; nia].
  + apply Z.leb_gt in B. rewrite (IH r (q * r) t Hr ltac:(nia)).
    rewrite Z.mul_assoc. reflexivity.
Qed.

Local Lemma small_power_near_spec :
  forall r p t, 1 <= r -> 0 <= p ->
  (DyadicPow.small_power_near r p = Some t <-> t = r ^ p /\ r ^ p < 2 ^ 54).
Proof.
intros r p t Hr Hp. unfold DyadicPow.small_power_near.
rewrite small_power_near_loop_spec by lia. rewrite Z2Nat.id, Z.mul_1_l by exact Hp.
reflexivity.
Qed.

(** The range check of [exact_near] on [q 2^e], where [63 -
    leading_zeros 64 q] is [log2 q]. *)
Local Lemma range_check_near :
  forall q e, 0 < q ->
  ((e <? -1075) || (1023 <? e + (63 - leading_zeros 64 q))) = false <->
  -1075 <= e /\ e + Z.log2 q <= 1023.
Proof.
intros q e Hq. unfold leading_zeros.
destruct (q =? 0) eqn:Q; [apply Z.eqb_eq in Q; lia |].
rewrite Bool.orb_false_iff, !Z.ltb_ge. lia.
Qed.

(** The last steps of [exact_near] round [q 2^e], for [0 < q < 2^54], to
    nearest: [Dyadic.round] at level 1 keeps [q 2^e] exactly, as [q] fits
    in its 64 bits, and [to_f64_near] rounds that to nearest. *)
Local Lemma exact_near_tail :
  forall q e, 0 < q < 2 ^ 54 -> -1075 <= e -> e + Z.log2 q <= 1023 ->
  exists w,
  (let* d := Dyadic.round 1 false (q :: nil) e false false in
   let* v := Dyadic.to_f64_near 1 d in
   Some (Some v)) = Some (Some w) /\
  near_round (IZR q * bpow radix2 e) w.
Proof.
intros q e Hq He Hl.
assert (Hn : level_ok 1) by (unfold level_ok; lia).
pose proof (dprec_bounds 1 Hn) as Hp.
pose proof (Z.log2_nonneg q) as L0.
assert (Hok : limbs_ok (q :: nil)).
{ apply limbs_ok_cons. split; [lia | constructor]. }
assert (Hv : Limbs.val (q :: nil) = q) by (cbn [Limbs.val]; ring).
assert (Hbits : 0 <= nat_bits q <= 54).
{ unfold nat_bits. destruct (Z.eqb_spec q 0) as [H0 | H0]; [lia |].
  assert (Z.log2 q < 54) by (apply Z.log2_lt_pow2; lia). lia. }
destruct (round_correct 1 false (q :: nil) e false false 0%R Hn Hok eq_refl)
  as (d & Hd & Hdok & HdR).
{ right. rewrite Hv. lia. }
(* [q 2^e] has at most 54 significant bits, so the rounding to 64 bits
   keeps it. *)
assert (HR : Dyadic.dy_R d = (IZR q * bpow radix2 e)%R).
{ rewrite HdR, Hv, Rplus_0_r. unfold cond_Ropp. cbv beta iota.
  apply dround_id; [exact Hn |].
  apply (format_int 1 false); [exact Hn |].
  rewrite Z.abs_eq by lia.
  apply Z.lt_le_trans with (2 ^ 54); [lia | apply Z.pow_le_mono_r; lia]. }
destruct (to_f64_near_correct 1 d Hn Hdok) as (w & Hw & Nw & _).
rewrite Hd. rewrite Hw. exists w. split; [reflexivity |].
rewrite <- HR. exact Nw.
Qed.

(** ** Soundness *)

Lemma exact_near_sound :
  forall x y v,
  is_finite x = true -> (0 < B2R x)%R -> is_finite y = true -> B2R y <> 0%R ->
  DyadicPow.exact_near x y = Some (Some v) ->
  near_round (Rpower (B2R x) (B2R y)) v.
Proof.
intros x y v Fx Hx Fy Hy0 H.
destruct (DyadicPow.odd_parts x) as [mx ex] eqn:Ox.
destruct (odd_parts_spec x mx ex Fx ltac:(lra) Ox) as (Hmx & Hmx0 & Hex & Ax).
rewrite Rabs_pos_eq in Ax by lra.
destruct (DyadicPow.odd_parts y) as [my ey] eqn:Oy.
destruct (odd_parts_spec y my ey Fy Hy0 Oy) as (Hmy & Hmy0 & Hey & Ay).
unfold DyadicPow.exact_near in H. rewrite Ox, Oy in H.
destruct (11 <? ey) eqn:E11; [discriminate H |].
destruct (if 0 <=? ey then (Z.shiftl my ey, 0) else (my, - ey)) as [p k] eqn:PK.
destruct (pk_spec my ey p k ltac:(lia) PK) as (Hp & Hk & _ & _ & Ey).
destruct (DyadicPow.roots_loop (Z.to_nat k) mx ex) as [[mr er]|] eqn:RL; [|discriminate H].
destruct (roots_loop_sound _ mx ex mr er ltac:(lia) RL) as (Hmr & Emx & Eex).
rewrite Z2Nat.id in Emx, Eex by exact Hk.
assert (Ly : lt y zero = Rlt_bool (B2R y) 0) by (apply Bltb_correct; [exact Fy | reflexivity]).
rewrite Ly in H.
destruct (Rlt_bool_cases (B2R y) 0) as [[SB Yn] | [SB Yp]]; rewrite SB in H.
- (* [y < 0]: only [mr = 1] gets past the check, and [x^y = 2^(-er p)]. *)
  destruct (mr =? 1) eqn:M; [|discriminate H]. apply Z.eqb_eq in M. subst mr.
  cbv zeta in H.
  destruct ((- (er * p) <? -1075) || (1023 <? - (er * p) + (63 - leading_zeros 64 1)))
    eqn:Rg; [discriminate H|].
  apply range_check_near in Rg; [|lia]. destruct Rg as [He1 He2].
  destruct (exact_near_tail 1 (- (er * p)) ltac:(lia) He1 He2) as (w & Hw & Nw).
  rewrite Hw in H. injection H as <-.
  replace (Rpower (B2R x) (B2R y)) with (IZR 1 * bpow radix2 (- (er * p)))%R;
    [exact Nw |].
  rewrite Ax, Emx, Eex.
  rewrite Rabs_left in Ay by exact Yn.
  replace (B2R y) with (- (IZR p / IZR (2 ^ k)))%R by lra.
  rewrite Rpower_Ropp, pow_dyadic_sound by lia.
  rewrite Z.pow_1_l, bpow_opp by lia. field. apply Rgt_not_eq, bpow_gt_0.
- (* [y > 0]: [q = mr^p] and [x^y = mr^p 2^(er p)]. *)
  assert (Yp' : (0 < B2R y)%R) by lra.
  destruct (if mr =? 1 then Some 1 else DyadicPow.small_power_near mr p) as [q|] eqn:Q;
    [|discriminate H].
  assert (Hq : q = mr ^ p /\ q < 2 ^ 54).
  { destruct (mr =? 1) eqn:M.
    - apply Z.eqb_eq in M. subst mr. injection Q as <-. rewrite Z.pow_1_l by lia. lia.
    - apply small_power_near_spec in Q; [destruct Q as [-> Hb]; lia | lia | lia]. }
  destruct Hq as (Eq & Hqb).
  assert (Hq0 : 0 < q) by (rewrite Eq; apply Z.pow_pos_nonneg; lia).
  cbv zeta in H.
  destruct ((er * p <? -1075) || (1023 <? er * p + (63 - leading_zeros 64 q)))
    eqn:Rg; [discriminate H|].
  apply range_check_near in Rg; [|exact Hq0]. destruct Rg as [He1 He2].
  destruct (exact_near_tail q (er * p) ltac:(lia) He1 He2) as (w & Hw & Nw).
  rewrite Hw in H. injection H as <-.
  replace (Rpower (B2R x) (B2R y)) with (IZR q * bpow radix2 (er * p))%R; [exact Nw |].
  rewrite Ax, Emx, Eex, Eq.
  rewrite Rabs_pos_eq in Ay by lra. rewrite Ay, Ey.
  rewrite pow_dyadic_sound by lia. reflexivity.
Qed.

(** ** Completeness *)

(** Where [x^y] is [mv 2^ev] with an odd [mv > 0], with the [(p, k)] of
    [exact_near], [pow_dyadic_complete] writes [x] as the [2^k]-th power
    of [r 2^er] and [mv 2^ev] as [(r 2^er)^(± p)], with [r = 1] for
    [y < 0], as [exact_root] does for an [f64] [v]. *)
Local Lemma exact_near_root :
  forall x y mx ex my ey mv ev p k,
  is_finite x = true -> (0 < B2R x)%R -> is_finite y = true -> B2R y <> 0%R ->
  Z.odd mv = true -> 0 < mv ->
  Rpower (B2R x) (B2R y) = (IZR mv * bpow radix2 ev)%R ->
  DyadicPow.odd_parts x = (mx, ex) -> DyadicPow.odd_parts y = (my, ey) ->
  (if 0 <=? ey then (Z.shiftl my ey, 0) else (my, - ey)) = (p, k) ->
  exists r er, 0 < r /\ mx = r ^ (2 ^ k) /\ ex = er * 2 ^ k /\ mv = r ^ p /\
  (if Rlt_bool (B2R y) 0 then r = 1 /\ ev = - (er * p) else ev = er * p).
Proof.
intros x y mx ex my ey mv ev p k Fx Hx Fy Hy0 Hmv Hmv0 Hv Ox Oy PK.
destruct (odd_parts_spec x mx ex Fx ltac:(lra) Ox) as (Hmx & Hmx0 & _ & Ax).
rewrite Rabs_pos_eq in Ax by lra.
destruct (odd_parts_spec y my ey Fy Hy0 Oy) as (Hmy & Hmy0 & _ & Ay).
destruct (pk_spec my ey p k ltac:(lia) PK) as (Hp & Hk & Hkp & _ & Ey).
apply (pow_dyadic_complete (Rlt_bool (B2R y) 0) mx ex mv ev p k Hmx ltac:(lia) Hmv
  Hmv0 Hp Hk).
- destruct Hkp as [-> | ->]; [left; reflexivity | right; exact Hmy].
- rewrite <- Ax, <- Hv. f_equal. rewrite Ey in Ay.
  destruct (Rlt_bool_cases (B2R y) 0) as [[SB Yn] | [SB Yp]]; rewrite SB.
  + rewrite Rabs_left in Ay by exact Yn. lra.
  + rewrite Rabs_pos_eq in Ay by exact Yp. lra.
Qed.

(** [exact_near] gives up at [ey >= 12], and rightly so, as [exact]
    does ([exact_ey_small]): [y] is then [± p] for an integer
    [p >= 2^12], and for [x <> 1] no [x^y] is [mv 2^ev] in range. For
    [x = 2^er], [er <> 0], the exponent [± er p] has [|± er p| >= 2^12],
    out of [[-1075, 1023]]. For [x = r 2^er] with an odd [r >= 3], [x^y]
    is a dyadic only for [y > 0], and then [r^p >= 2^54] is too wide. *)
Local Lemma exact_near_ey_small :
  forall x y mx ex my ey mv ev,
  is_finite x = true -> (0 < B2R x)%R -> B2R x <> 1%R -> is_finite y = true -> B2R y <> 0%R ->
  Z.odd mv = true -> 0 < mv < 2 ^ 54 -> -1075 <= ev -> ev + Z.log2 mv <= 1023 ->
  Rpower (B2R x) (B2R y) = (IZR mv * bpow radix2 ev)%R ->
  DyadicPow.odd_parts x = (mx, ex) -> DyadicPow.odd_parts y = (my, ey) -> ey <= 11.
Proof.
intros x y mx ex my ey mv ev Fx Hx Hx1 Fy Hy0 Hmv Hmv0 Hev Hev2 Hv Ox Oy.
destruct (Z_le_gt_dec ey 11) as [|H12]; [assumption | exfalso].
destruct (odd_parts_spec x mx ex Fx ltac:(lra) Ox) as (_ & _ & _ & Ax).
rewrite Rabs_pos_eq in Ax by lra.
destruct (odd_parts_spec y my ey Fy Hy0 Oy) as (_ & Hmy0 & _ & _).
assert (PK : (if 0 <=? ey then (Z.shiftl my ey, 0) else (my, - ey)) = (my * 2 ^ ey, 0)).
{ rewrite (proj2 (Z.leb_le 0 ey)) by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
destruct (exact_near_root x y mx ex my ey mv ev _ _ Fx Hx Fy Hy0 Hmv ltac:(lia) Hv Ox Oy PK)
  as (r & er & Hr & Emx & Eex & Emv & Hneg).
rewrite Z.pow_0_r, Z.pow_1_r in Emx. rewrite Z.pow_0_r, Z.mul_1_r in Eex.
assert (Hp : 2 ^ 12 <= my * 2 ^ ey).
{ assert (2 ^ 12 <= 2 ^ ey) by (apply Z.pow_le_mono_r; lia). nia. }
destruct (Z.eq_dec r 1) as [R1 | R1].
- (* [x = 2^er], and [er <> 0] as [x <> 1]. *)
  rewrite R1 in Emx, Emv. rewrite Z.pow_1_l in Emv by lia. subst mv. rewrite Z.log2_1 in Hev2.
  assert (Eer : er <> 0).
  { intros E0. apply Hx1. rewrite Ax, Emx, Eex, E0. change (bpow radix2 0) with 1%R. lra. }
  destruct (Rlt_bool (B2R y) 0); [destruct Hneg as [_ Hneg] |];
    destruct (Z_lt_le_dec er 0); nia.
- (* An odd [r >= 3], and so [y > 0]: [r^p >= 2^p >= 2^54]. *)
  destruct (Rlt_bool (B2R y) 0); [destruct Hneg as [Hr1 _]; contradiction |].
  assert (2 ^ (my * 2 ^ ey) <= r ^ (my * 2 ^ ey)) by (apply Z.pow_le_mono_l; lia).
  assert (2 ^ 54 <= 2 ^ (my * 2 ^ ey)) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

Theorem exact_near_complete :
  forall x y q e,
  is_finite x = true -> (0 < B2R x)%R -> B2R x <> 1%R -> is_finite y = true -> B2R y <> 0%R ->
  0 < q < 2 ^ 54 -> -1075 <= e -> e + Z.log2 q <= 1023 ->
  Rpower (B2R x) (B2R y) = (IZR q * bpow radix2 e)%R ->
  exists v, DyadicPow.exact_near x y = Some (Some v).
Proof.
intros x y q e Fx Hx Hx1 Fy Hy0 Hq He1 He2 Hv.
(* Write [q 2^e] as [mv 2^ev] with an odd [mv = q / 2^z] and [ev = e + z],
   which has the same top bit, [ev + log2 mv = e + log2 q]. *)
destruct (trailing_zeros_odd q ltac:(lia)) as (Hz & Hmv & Eq).
revert Hz Hmv Eq. generalize (trailing_zeros 64 q) as z. intros z Hz.
generalize (Z.shiftr q z) as mv. intros mv Hmv Eq. subst q.
assert (H2z : 0 < 2 ^ z) by (apply Z.pow_pos_nonneg; lia).
assert (Hmv0 : 0 < mv < 2 ^ 54) by nia.
rewrite Z.log2_mul_pow2 in He2 by lia.
assert (Hev1 : -1075 <= e + z) by lia.
assert (Hev2 : e + z + Z.log2 mv <= 1023) by lia.
assert (Av : Rpower (B2R x) (B2R y) = (IZR mv * bpow radix2 (e + z))%R).
{ assert (E2 : IZR (2 ^ z) = bpow radix2 z) by (rewrite <- IZR_Zpower by lia; reflexivity).
  rewrite Hv, mult_IZR, E2, Rmult_assoc, <- bpow_plus. f_equal. f_equal. ring. }
clear Hv He1 He2 Hq.
destruct (DyadicPow.odd_parts x) as [mx ex] eqn:Ox.
destruct (odd_parts_spec x mx ex Fx ltac:(lra) Ox) as (_ & Hmx0 & _ & _).
destruct (DyadicPow.odd_parts y) as [my ey] eqn:Oy.
destruct (odd_parts_spec y my ey Fy Hy0 Oy) as (_ & Hmy0 & _ & _).
pose proof (exact_near_ey_small x y mx ex my ey mv (e + z) Fx Hx Hx1 Fy Hy0 Hmv Hmv0
  Hev1 Hev2 Av Ox Oy) as H11.
unfold DyadicPow.exact_near. rewrite Ox, Oy, (proj2 (Z.ltb_ge 11 ey) H11).
destruct (if 0 <=? ey then (Z.shiftl my ey, 0) else (my, - ey)) as [p k] eqn:PK.
destruct (pk_spec my ey p k ltac:(lia) PK) as (Hp & Hk & _ & _ & _).
destruct (exact_near_root x y mx ex my ey mv (e + z) p k Fx Hx Fy Hy0 Hmv ltac:(lia) Av
  Ox Oy PK) as (r & er & Hr & Emx & Eex & Emv & Hneg).
(* The [k] square roots of [mx = r^(2^k) < 2^53] are exact. *)
assert (RL : DyadicPow.roots_loop (Z.to_nat k) mx ex = Some (r, er)).
{ pose proof (roots_loop_complete (Z.to_nat k) r er Hr) as RC.
  rewrite Z2Nat.id in RC by exact Hk. rewrite Emx, Eex. apply RC. rewrite <- Emx. lia. }
assert (Ly : lt y zero = Rlt_bool (B2R y) 0) by (apply Bltb_correct; [exact Fy | reflexivity]).
(* [q = r^p = mv], which is 1 for [y < 0]. *)
assert (Q : (if r =? 1 then Some 1 else if Rlt_bool (B2R y) 0 then None
             else DyadicPow.small_power_near r p) = Some mv).
{ destruct (r =? 1) eqn:R1.
  - apply Z.eqb_eq in R1. rewrite Emv, R1, Z.pow_1_l by lia. reflexivity.
  - apply Z.eqb_neq in R1.
    destruct (Rlt_bool (B2R y) 0); [destruct Hneg as [Hr1 _]; contradiction |].
    apply (proj2 (small_power_near_spec r p mv ltac:(lia) ltac:(lia))).
    split; [exact Emv | rewrite <- Emv; lia]. }
assert (E : (if Rlt_bool (B2R y) 0 then - (er * p) else er * p) = e + z).
{ destruct (Rlt_bool (B2R y) 0); [destruct Hneg as [_ Hneg] |]; lia. }
rewrite RL, Ly. cbv beta iota zeta. rewrite Q. cbv beta iota zeta. rewrite E.
rewrite (proj2 (range_check_near mv (e + z) ltac:(lia)) (conj Hev1 Hev2)). cbv beta iota.
destruct (exact_near_tail mv (e + z) Hmv0 Hev1 Hev2) as (w & Hw & _).
rewrite Hw. exists w. reflexivity.
Qed.
