(** * The exact cases of the dyadic [pow]

    [exact x y] of [DyadicPow] in [Model.v] checks, with integers only,
    whether [x^y] is an [f64] for a finite [x > 0] and a finite [y <> 0],
    and returns it if so. It writes [x = mx 2^ex] and [y = ± p / 2^k] with
    odd [mx] and [p], takes [k] exact square roots of [mx], and raises the
    root to the power [p]. Where it returns an [f64], that is [x^y]
    ([exact_sound]), and it returns one at every such [x] other than 1
    whose [x^y] is a finite [f64] ([exact_complete]), by the arithmetic
    of [DyPowArith.v]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Elementary DyRound DyConv DyPowArith DyPowRules.
From Inari Require FastExpReduce.

Open Scope Z_scope.

Local Notation G := (generic_format radix2 (SpecFloat.fexp 53 1024)).

(** ** The [f64]s that [exact] builds *)

(** An integer [m < 2^53] times [2^e] that lies in the range of [f64] is
    an [f64], which [binary_normalize] returns exactly. *)
Lemma normalize_exact :
  forall m e,
  0 <= m < 2 ^ 53 -> -1074 <= e -> (IZR m * bpow radix2 e < bpow radix2 1024)%R ->
  is_finite (binary_normalize 53 1024 _ _ mode_NE m e false) = true /\
  B2R (binary_normalize 53 1024 _ _ mode_NE m e false) = (IZR m * bpow radix2 e)%R.
Proof.
intros m e Hm He Hlt.
assert (E : F2R (Float radix2 m e) = (IZR m * bpow radix2 e)%R) by reflexivity.
assert (Gm : G (IZR m * bpow radix2 e)).
{ change (SpecFloat.fexp 53 1024) with (FLT_exp (-1074) 53).
  apply generic_format_FLT.
  apply (FLT_spec _ _ _ _ (Float radix2 m e)); [exact E | |].
  - cbn [Fnum radix_val radix2]. rewrite Z.abs_eq by lia. exact (proj2 Hm).
  - cbn [Fexp]. exact He. }
pose proof (binary_normalize_correct 53 1024 _ _ mode_NE m e false) as Hn.
cbv zeta in Hn. rewrite E in Hn.
rewrite round_generic in Hn by first [exact Gm | typeclasses eauto].
rewrite Rabs_pos_eq in Hn
  by (apply Rmult_le_pos; [apply IZR_le; lia | apply bpow_ge_0]).
rewrite Rlt_bool_true in Hn by exact Hlt.
destruct Hn as (Hz & Fz & _). split; [exact Fz | exact Hz].
Qed.

(** [m as f64] is [m] for [m < 2^53]. *)
Lemma of_u64_exact :
  forall m, 0 <= m < 2 ^ 53 ->
  is_finite (of_u64 m) = true /\ B2R (of_u64 m) = IZR m.
Proof.
intros m Hm.
assert (Hlt : (IZR m * bpow radix2 0 < bpow radix2 1024)%R).
{ rewrite Rmult_1_r. rewrite <- (IZR_Zpower radix2 1024) by lia. apply IZR_lt.
  assert (2 ^ 53 < 2 ^ 1024) by (apply Z.pow_lt_mono_r; lia).
  change (radix_val radix2) with 2. lia. }
destruct (normalize_exact m 0 Hm ltac:(lia) Hlt) as (F & E).
unfold of_u64. split; [exact F |]. rewrite E. apply Rmult_1_r.
Qed.

(** [q 2^e] with [q > 0] lies below [2^1024] exactly when its top bit,
    [2^(e + log2 q)], is at most [2^1023]. *)
Lemma dyadic_lt_bpow :
  forall q e, 0 < q ->
  ((IZR q * bpow radix2 e < bpow radix2 1024)%R <-> e + Z.log2 q <= 1023).
Proof.
intros q e Hq.
destruct (Z.log2_spec q Hq) as [L U].
pose proof (Z.log2_nonneg q) as L0.
assert (EL : IZR (2 ^ Z.log2 q) = bpow radix2 (Z.log2 q))
  by (rewrite <- IZR_Zpower by lia; reflexivity).
assert (EU : IZR (2 ^ Z.succ (Z.log2 q)) = bpow radix2 (Z.log2 q + 1))
  by (rewrite <- IZR_Zpower by lia; reflexivity).
apply IZR_le in L. apply IZR_lt in U. rewrite EL in L. rewrite EU in U.
pose proof (bpow_gt_0 radix2 e) as B0.
split; intros H.
- destruct (Z_le_gt_dec (e + Z.log2 q) 1023) as [|Hc]; [assumption | exfalso].
  assert (bpow radix2 1024 <= bpow radix2 (Z.log2 q) * bpow radix2 e)%R.
  { rewrite <- bpow_plus. apply bpow_le. lia. }
  assert (bpow radix2 (Z.log2 q) * bpow radix2 e <= IZR q * bpow radix2 e)%R
    by (apply Rmult_le_compat_r; lra).
  lra.
- apply Rlt_le_trans with (bpow radix2 (Z.log2 q + 1) * bpow radix2 e)%R.
  + apply Rmult_lt_compat_r; lra.
  + rewrite <- bpow_plus. apply bpow_le. lia.
Qed.

(** The range check of [exact] on [q 2^e], where [63 - leading_zeros 64
    q] is [log2 q]. *)
Lemma range_check :
  forall q e, 0 < q ->
  ((e <? -1074) || (1023 <? e + (63 - leading_zeros 64 q))) = false <->
  -1074 <= e /\ e + Z.log2 q <= 1023.
Proof.
intros q e Hq. unfold leading_zeros.
destruct (q =? 0) eqn:Q; [apply Z.eqb_eq in Q; lia |].
rewrite Bool.orb_false_iff, !Z.ltb_ge. lia.
Qed.

(** The square root of the square of an integer [0 < s < 2^53], which is
    an [f64]. *)
Lemma fsqrt_exact :
  forall w s,
  is_finite w = true -> B2R w = IZR (s * s) -> 0 < s < 2 ^ 53 ->
  is_finite (fsqrt w) = true /\ B2R (fsqrt w) = IZR s.
Proof.
intros w s Fw Hw Hs.
assert (Gs : G (IZR s)).
{ destruct (of_u64_exact s ltac:(lia)) as (_ & E). rewrite <- E.
  apply generic_format_B2R. }
destruct (Bsqrt_correct 53 1024 _ _ mode_NE w) as (Hr & Hf & _).
unfold fsqrt. split.
- rewrite Hf. destruct w as [sw|sw| |sw mw ew Bw]; try discriminate Fw; [reflexivity|].
  destruct sw; [exfalso | reflexivity].
  assert (B2R (B754_finite true mw ew Bw) < 0)%R by (apply F2R_lt_0; cbn; lia).
  assert (0 < IZR (s * s))%R by (apply IZR_lt; nia).
  lra.
- rewrite Hr, Hw, mult_IZR, sqrt_square by (apply IZR_le; lia).
  apply round_generic; first [exact Gs | typeclasses eauto].
Qed.

(** A real [r <> 0] that an [f64] holds rounds down to that [f64]. *)
Lemma round_dn_exact :
  forall r v, f64_format r -> r <> 0%R ->
  mpfr_round f64_format RNDD r (with_val v) -> is_finite v = true /\ B2R v = r.
Proof.
intros r v Fr Hr H.
destruct v as [s|s| |s m e B]; cbn [with_val mpfr_round] in H.
- exfalso. destruct H as (_ & H0 & Hmax).
  assert (r <= 0)%R by (apply Hmax; [exact Fr | apply Rle_refl]). lra.
- destruct s; [| destruct H]. exfalso. specialize (H r Fr). lra.
- destruct H.
- destruct H as (_ & _ & Hle & Hmax). split; [reflexivity|].
  assert (r <= B2R (B754_finite s m e B))%R by (apply Hmax; [exact Fr | apply Rle_refl]).
  lra.
Qed.

(** ** The loops of [exact] *)

(** [small_power_loop f r q] is [q r^f] while that stays below [2^53]:
    as [r >= 1], the products only grow, so none of them is [2^53] or
    more exactly when the last one is not. *)
Lemma small_power_loop_spec :
  forall f r q t, 1 <= r -> 0 <= q < 2 ^ 53 ->
  (DyadicPow.small_power_loop f r q = Some t <->
   t = q * r ^ Z.of_nat f /\ q * r ^ Z.of_nat f < 2 ^ 53).
Proof.
induction f as [|f IH]; intros r q t Hr Hq; cbn [DyadicPow.small_power_loop].
- rewrite Z.pow_0_r, Z.mul_1_r. split.
  + intros H. injection H as <-. lia.
  + intros [-> _]. reflexivity.
- assert (Hp : 0 < r ^ Z.of_nat f) by (apply Z.pow_pos_nonneg; lia).
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  destruct (2 ^ 53 <=? q * r) eqn:B.
  + apply Z.leb_le in B. split; [discriminate | intros [_ H]; nia].
  + apply Z.leb_gt in B. rewrite (IH r (q * r) t Hr ltac:(nia)).
    rewrite Z.mul_assoc. reflexivity.
Qed.

Lemma small_power_spec :
  forall r p t, 1 <= r -> 0 <= p ->
  (DyadicPow.small_power r p = Some t <-> t = r ^ p /\ r ^ p < 2 ^ 53).
Proof.
intros r p t Hr Hp. unfold DyadicPow.small_power.
rewrite small_power_loop_spec by lia. rewrite Z2Nat.id, Z.mul_1_l by exact Hp. reflexivity.
Qed.

(** Where [roots_loop f mx ex] returns [(mr, er)], each of its [f] steps
    has taken an exact square root [s] of the odd part, checked by [s * s
    = mx], and halved an even exponent, so [mx 2^ex = (mr 2^er)^(2^f)]
    with [mx = mr^(2^f)] and [ex = er 2^f]. *)
Lemma roots_loop_sound :
  forall f mx ex mr er, 0 < mx ->
  DyadicPow.roots_loop f mx ex = Some (mr, er) ->
  0 < mr /\ mx = mr ^ (2 ^ Z.of_nat f) /\ ex = er * 2 ^ Z.of_nat f.
Proof.
induction f as [|f IH]; intros mx ex mr er Hmx H; cbn [DyadicPow.roots_loop] in H.
- injection H as <- <-. rewrite Z.pow_0_r, Z.pow_1_r, Z.mul_1_r. lia.
- set (s := DyadicExp.to_i64 (fsqrt (DyadicPow.of_i64 mx)) mod 2 ^ 64) in H.
  destruct (negb (Z.rem ex 2 =? 0) || negb (s * s =? mx)) eqn:B; [discriminate H|].
  apply Bool.orb_false_iff in B. destruct B as [B1 B2].
  apply Bool.negb_false_iff, Z.eqb_eq in B1, B2.
  assert (Hs : 0 <= s) by (apply Z.mod_pos_bound; lia).
  assert (Hs0 : 0 < s) by (destruct (Z.eq_dec s 0); [subst s; lia | lia]).
  destruct (IH s (Z.quot ex 2) mr er Hs0 H) as (Hmr & Es & Ee).
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  split; [exact Hmr|]. split.
  + rewrite <- B2, Es, <- Z.pow_add_r by (try apply Z.pow_nonneg; lia). f_equal. ring.
  + rewrite (Z.quot_rem ex 2) by lia. rewrite B1, Ee. ring.
Qed.

(** Conversely, on [r^(2^f) < 2^53] and [er 2^f], each step finds the
    square root, as [sqrt] of an [f64] that holds a square [s0^2 < 2^53]
    is exact, and so the loop returns [(r, er)]. *)
Lemma roots_loop_complete :
  forall f r er, 0 < r -> r ^ (2 ^ Z.of_nat f) < 2 ^ 53 ->
  DyadicPow.roots_loop f (r ^ (2 ^ Z.of_nat f)) (er * 2 ^ Z.of_nat f) = Some (r, er).
Proof.
induction f as [|f IH]; intros r er Hr Hb; cbn [DyadicPow.roots_loop].
- rewrite Z.pow_0_r, Z.pow_1_r, Z.mul_1_r. reflexivity.
- set (s0 := r ^ (2 ^ Z.of_nat f)).
  assert (H2f : 0 <= 2 ^ Z.of_nat f) by (apply Z.pow_nonneg; lia).
  assert (Hs0 : 0 < s0) by (apply Z.pow_pos_nonneg; lia).
  assert (Esq : r ^ (2 ^ Z.of_nat (S f)) = s0 * s0).
  { rewrite Nat2Z.inj_succ, Z.pow_succ_r, Z.mul_comm, Z.pow_mul_r by lia.
    rewrite Z.pow_2_r. reflexivity. }
  assert (Ee : er * 2 ^ Z.of_nat (S f) = er * 2 ^ Z.of_nat f * 2)
    by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; ring).
  rewrite Esq in Hb |- *. rewrite Ee.
  assert (Hb0 : s0 < 2 ^ 53) by nia.
  destruct (of_u64_exact (s0 * s0) ltac:(nia)) as (F1 & E1).
  destruct (fsqrt_exact (of_u64 (s0 * s0)) s0 F1 E1 ltac:(lia)) as (F2 & E2).
  change (DyadicPow.of_i64 (s0 * s0)) with (of_u64 (s0 * s0)).
  rewrite (FastExpReduce.to_i64_int _ s0 F2 E2), Z.mod_small by lia.
  rewrite Z.rem_mul, !Z.eqb_refl by lia. cbn [negb orb].
  rewrite Z.quot_mul by lia. exact (IH r er Hr Hb0).
Qed.

(** ** The ends of [exact] *)

(** The last steps of [exact] build the [f64] [q 2^e] exactly, for [0 < q
    < 2^53] and [q 2^e] in the range of [f64]: [q as f64] is [q], the shift
    by [e] is exact, and so is [to_f64] rounding down, as its argument is
    an [f64]. *)
Lemma exact_tail :
  forall q e, 0 < q < 2 ^ 53 -> -1074 <= e -> e + Z.log2 q <= 1023 ->
  exists w,
  (let* d := Dyadic.from_f64 1 (of_u64 q) in
   let* d' := Dyadic.shl 1 d e in
   let* v := Dyadic.to_f64 1 d' false in
   Some (Some v)) = Some (Some w) /\
  is_finite w = true /\ B2R w = (IZR q * bpow radix2 e)%R.
Proof.
intros q e Hq He Hl.
assert (Hn : level_ok 1) by (unfold level_ok; lia).
pose proof (Z.log2_nonneg q).
destruct (of_u64_exact q ltac:(lia)) as (Fq & Eq).
destruct (from_f64_correct 1 (of_u64 q) Hn Fq) as (d & Hd & Od & Sd & Ed).
rewrite Hd.
assert (Hk : - 2 ^ 63 <= Dyadic.dy_exp d + e < 2 ^ 63) by (unfold exp_small in Sd; lia).
destruct (shl_correct 1 d e Hn Od Hk) as (d' & Hd' & Od' & Ed').
rewrite Hd'.
destruct (to_f64_correct 1 d' false Hn Od') as (v & Hv & Rv).
rewrite Hv. exists v. split; [reflexivity|].
rewrite Ed', Ed, Eq in Rv.
assert (Hlt : (IZR q * bpow radix2 e < bpow radix2 1024)%R) by (apply dyadic_lt_bpow; lia).
destruct (normalize_exact q e ltac:(lia) He Hlt) as (Fw & Ew).
apply round_dn_exact; [| | exact Rv].
- exists (binary_normalize 53 1024 _ _ mode_NE q e false). split; [exact Fw | exact Ew].
- apply Rgt_not_eq, Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
Qed.

(** The [(p, k)] of [exact] writes [|y| = my 2^ey] as [p / 2^k]: [p = my
    2^ey] and [k = 0] for [ey >= 0], and [p = my] and [k = -ey] below. *)
Lemma pk_spec :
  forall my ey p k, 0 < my ->
  (if 0 <=? ey then (Z.shiftl my ey, 0) else (my, - ey)) = (p, k) ->
  0 < p /\ 0 <= k /\ (k = 0 \/ p = my) /\ (0 <= ey -> p = my * 2 ^ ey) /\
  (IZR my * bpow radix2 ey = IZR p / IZR (2 ^ k))%R.
Proof.
intros my ey p k Hmy H.
destruct (0 <=? ey) eqn:B.
- apply Z.leb_le in B. injection H as <- <-.
  rewrite Z.shiftl_mul_pow2 by exact B.
  assert (0 < 2 ^ ey) by (apply Z.pow_pos_nonneg; lia).
  split; [nia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|].
  assert (E : IZR (2 ^ ey) = bpow radix2 ey) by (rewrite <- IZR_Zpower by lia; reflexivity).
  rewrite Z.pow_0_r, mult_IZR, E. unfold Rdiv. rewrite Rinv_1, Rmult_1_r. reflexivity.
- apply Z.leb_gt in B. injection H as <- <-.
  split; [exact Hmy|]. split; [lia|]. split; [right; reflexivity|]. split; [lia|].
  assert (E : IZR (2 ^ (- ey)) = bpow radix2 (- ey))
    by (rewrite <- IZR_Zpower by lia; reflexivity).
  rewrite E. unfold Rdiv. f_equal.
  replace ey with (- - ey) at 1 by ring. rewrite bpow_opp. reflexivity.
Qed.

(** ** Soundness and completeness *)

Lemma Rlt_bool_cases :
  forall a b, (Rlt_bool a b = true /\ (a < b)%R) \/ (Rlt_bool a b = false /\ (b <= a)%R).
Proof. intros a b. destruct (Rlt_bool_spec a b); [left | right]; split; auto. Qed.

Lemma exact_sound :
  forall x y (v : f64),
  is_finite x = true -> (0 < B2R x)%R -> is_finite y = true -> B2R y <> 0%R ->
  DyadicPow.exact x y = Some (Some v) ->
  is_finite v = true /\ B2R v = Rpower (B2R x) (B2R y).
Proof.
intros x y v Fx Hx Fy Hy0 H.
destruct (DyadicPow.odd_parts x) as [mx ex] eqn:Ox.
destruct (odd_parts_spec x mx ex Fx ltac:(lra) Ox) as (Hmx & Hmx0 & Hex & Ax).
rewrite Rabs_pos_eq in Ax by lra.
destruct (DyadicPow.odd_parts y) as [my ey] eqn:Oy.
destruct (odd_parts_spec y my ey Fy Hy0 Oy) as (Hmy & Hmy0 & Hey & Ay).
unfold DyadicPow.exact in H. rewrite Ox, Oy in H.
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
  destruct ((- (er * p) <? -1074) || (1023 <? - (er * p) + (63 - leading_zeros 64 1)))
    eqn:Rg; [discriminate H|].
  apply range_check in Rg; [|lia]. destruct Rg as [He1 He2].
  destruct (exact_tail 1 (- (er * p)) ltac:(lia) He1 He2) as (w & Hw & Fw & Ew).
  rewrite Hw in H. injection H as <-.
  split; [exact Fw|]. rewrite Ew, Ax, Emx, Eex.
  rewrite Rabs_left in Ay by exact Yn.
  replace (B2R y) with (- (IZR p / IZR (2 ^ k)))%R by lra.
  rewrite Rpower_Ropp, pow_dyadic_sound by lia.
  rewrite Z.pow_1_l, bpow_opp by lia. field. apply Rgt_not_eq, bpow_gt_0.
- (* [y > 0]: [q = mr^p] and [x^y = mr^p 2^(er p)]. *)
  assert (Yp' : (0 < B2R y)%R) by lra.
  destruct (if mr =? 1 then Some 1 else DyadicPow.small_power mr p) as [q|] eqn:Q;
    [|discriminate H].
  assert (Hq : q = mr ^ p /\ q < 2 ^ 53).
  { destruct (mr =? 1) eqn:M.
    - apply Z.eqb_eq in M. subst mr. injection Q as <-. rewrite Z.pow_1_l by lia. lia.
    - apply small_power_spec in Q; [destruct Q as [-> Hb]; lia | lia | lia]. }
  destruct Hq as (Eq & Hqb).
  assert (Hq0 : 0 < q) by (rewrite Eq; apply Z.pow_pos_nonneg; lia).
  cbv zeta in H.
  destruct ((er * p <? -1074) || (1023 <? er * p + (63 - leading_zeros 64 q)))
    eqn:Rg; [discriminate H|].
  apply range_check in Rg; [|exact Hq0]. destruct Rg as [He1 He2].
  destruct (exact_tail q (er * p) ltac:(lia) He1 He2) as (w & Hw & Fw & Ew).
  rewrite Hw in H. injection H as <-.
  split; [exact Fw|]. rewrite Ew, Ax, Emx, Eex, Eq.
  rewrite Rabs_pos_eq in Ay by lra. rewrite Ay, Ey.
  rewrite pow_dyadic_sound by lia. reflexivity.
Qed.

(** The odd part [mv] and the exponent [ev] of a finite [v > 0], with
    [mv 2^ev] below [2^1024]. *)
Lemma exact_v_parts :
  forall v mv ev,
  is_finite v = true -> (0 < B2R v)%R -> DyadicPow.odd_parts v = (mv, ev) ->
  Z.odd mv = true /\ 0 < mv < 2 ^ 53 /\ -1074 <= ev /\ ev + Z.log2 mv <= 1023 /\
  B2R v = (IZR mv * bpow radix2 ev)%R.
Proof.
intros v mv ev Fv Hv Ov.
destruct (odd_parts_spec v mv ev Fv ltac:(lra) Ov) as (Hmv & Hmv0 & Hev & Av).
pose proof (abs_B2R_lt_emax _ _ v) as Hlt.
rewrite Av in Hlt. rewrite Rabs_pos_eq in Av by lra.
apply dyadic_lt_bpow in Hlt; [|lia].
split; [exact Hmv|]. split; [exact Hmv0|]. split; [exact Hev|]. split; [exact Hlt | exact Av].
Qed.

(** Where [x^y] is a finite [f64] [v], with the [(p, k)] of [exact],
    [pow_dyadic_complete] writes [x] as the [2^k]-th power of [r 2^er]
    and [v] as [(r 2^er)^(± p)], with [r = 1] for [y < 0]. *)
Lemma exact_root :
  forall x y (v : f64) mx ex my ey mv ev p k,
  is_finite x = true -> (0 < B2R x)%R -> is_finite y = true -> B2R y <> 0%R ->
  is_finite v = true -> Rpower (B2R x) (B2R y) = B2R v ->
  DyadicPow.odd_parts x = (mx, ex) -> DyadicPow.odd_parts y = (my, ey) ->
  DyadicPow.odd_parts v = (mv, ev) ->
  (if 0 <=? ey then (Z.shiftl my ey, 0) else (my, - ey)) = (p, k) ->
  exists r er, 0 < r /\ mx = r ^ (2 ^ k) /\ ex = er * 2 ^ k /\ mv = r ^ p /\
  (if Rlt_bool (B2R y) 0 then r = 1 /\ ev = - (er * p) else ev = er * p).
Proof.
intros x y v mx ex my ey mv ev p k Fx Hx Fy Hy0 Fv Hv Ox Oy Ov PK.
assert (Hv0 : (0 < B2R v)%R) by (rewrite <- Hv; apply exp_pos).
destruct (odd_parts_spec x mx ex Fx ltac:(lra) Ox) as (Hmx & Hmx0 & _ & Ax).
rewrite Rabs_pos_eq in Ax by lra.
destruct (odd_parts_spec y my ey Fy Hy0 Oy) as (Hmy & Hmy0 & _ & Ay).
destruct (exact_v_parts v mv ev Fv Hv0 Ov) as (Hmv & Hmv0 & _ & _ & Av).
destruct (pk_spec my ey p k ltac:(lia) PK) as (Hp & Hk & Hkp & _ & Ey).
apply (pow_dyadic_complete (Rlt_bool (B2R y) 0) mx ex mv ev p k Hmx ltac:(lia) Hmv
  ltac:(lia) Hp Hk).
- destruct Hkp as [-> | ->]; [left; reflexivity | right; exact Hmy].
- rewrite <- Ax, <- Av, <- Hv. f_equal. rewrite Ey in Ay.
  destruct (Rlt_bool_cases (B2R y) 0) as [[SB Yn] | [SB Yp]]; rewrite SB.
  + rewrite Rabs_left in Ay by exact Yn. lra.
  + rewrite Rabs_pos_eq in Ay by exact Yp. lra.
Qed.

(** [exact] gives up at [ey >= 12], and rightly so: [y] is then [± p]
    for an integer [p >= 2^12], and [x^y] with [x <> 1] is not a finite
    [f64]. For [x = 2^er], [er <> 0], the exponent [± er p] is out of
    range. For [x = r 2^er] with an odd [r >= 3], [x^y] is a dyadic only
    for [y > 0], and then [r^p >= 2^53] is too wide. *)
Lemma exact_ey_small :
  forall x y (v : f64) mx ex my ey,
  is_finite x = true -> (0 < B2R x)%R -> B2R x <> 1%R -> is_finite y = true -> B2R y <> 0%R ->
  is_finite v = true -> Rpower (B2R x) (B2R y) = B2R v ->
  DyadicPow.odd_parts x = (mx, ex) -> DyadicPow.odd_parts y = (my, ey) -> ey <= 11.
Proof.
intros x y v mx ex my ey Fx Hx Hx1 Fy Hy0 Fv Hv Ox Oy.
destruct (Z_le_gt_dec ey 11) as [|H12]; [assumption | exfalso].
assert (Hv0 : (0 < B2R v)%R) by (rewrite <- Hv; apply exp_pos).
destruct (DyadicPow.odd_parts v) as [mv ev] eqn:Ov.
destruct (exact_v_parts v mv ev Fv Hv0 Ov) as (_ & Hmv0 & Hev & Hev2 & _).
destruct (odd_parts_spec x mx ex Fx ltac:(lra) Ox) as (_ & _ & _ & Ax).
rewrite Rabs_pos_eq in Ax by lra.
destruct (odd_parts_spec y my ey Fy Hy0 Oy) as (_ & Hmy0 & _ & _).
assert (PK : (if 0 <=? ey then (Z.shiftl my ey, 0) else (my, - ey)) = (my * 2 ^ ey, 0)).
{ rewrite (proj2 (Z.leb_le 0 ey)) by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
destruct (exact_root x y v mx ex my ey mv ev _ _ Fx Hx Fy Hy0 Fv Hv Ox Oy Ov PK)
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
- (* An odd [r >= 3], and so [y > 0]: [r^p >= 2^p >= 2^53]. *)
  destruct (Rlt_bool (B2R y) 0); [destruct Hneg as [Hr1 _]; contradiction |].
  assert (2 ^ (my * 2 ^ ey) <= r ^ (my * 2 ^ ey)) by (apply Z.pow_le_mono_l; lia).
  assert (2 ^ 53 <= 2 ^ (my * 2 ^ ey)) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

Lemma exact_complete :
  forall x y (v : f64),
  is_finite x = true -> (0 < B2R x)%R -> B2R x <> 1%R -> is_finite y = true -> B2R y <> 0%R ->
  is_finite v = true -> Rpower (B2R x) (B2R y) = B2R v ->
  DyadicPow.exact x y = Some (Some v).
Proof.
intros x y v Fx Hx Hx1 Fy Hy0 Fv Hv.
assert (Hv0 : (0 < B2R v)%R) by (rewrite <- Hv; apply exp_pos).
destruct (DyadicPow.odd_parts x) as [mx ex] eqn:Ox.
destruct (odd_parts_spec x mx ex Fx ltac:(lra) Ox) as (_ & Hmx0 & _ & _).
destruct (DyadicPow.odd_parts y) as [my ey] eqn:Oy.
destruct (odd_parts_spec y my ey Fy Hy0 Oy) as (_ & Hmy0 & _ & _).
destruct (DyadicPow.odd_parts v) as [mv ev] eqn:Ov.
destruct (exact_v_parts v mv ev Fv Hv0 Ov) as (_ & Hmv0 & Hev1 & Hev2 & Av).
pose proof (exact_ey_small x y v mx ex my ey Fx Hx Hx1 Fy Hy0 Fv Hv Ox Oy) as H11.
unfold DyadicPow.exact. rewrite Ox, Oy, (proj2 (Z.ltb_ge 11 ey) H11).
destruct (if 0 <=? ey then (Z.shiftl my ey, 0) else (my, - ey)) as [p k] eqn:PK.
destruct (pk_spec my ey p k ltac:(lia) PK) as (Hp & Hk & _ & _ & _).
destruct (exact_root x y v mx ex my ey mv ev p k Fx Hx Fy Hy0 Fv Hv Ox Oy Ov PK)
  as (r & er & Hr & Emx & Eex & Emv & Hneg).
(* The [k] square roots of [mx = r^(2^k) < 2^53] are exact. *)
assert (RL : DyadicPow.roots_loop (Z.to_nat k) mx ex = Some (r, er)).
{ pose proof (roots_loop_complete (Z.to_nat k) r er Hr) as RC.
  rewrite Z2Nat.id in RC by exact Hk. rewrite Emx, Eex. apply RC. rewrite <- Emx. lia. }
assert (Ly : lt y zero = Rlt_bool (B2R y) 0) by (apply Bltb_correct; [exact Fy | reflexivity]).
(* [q = r^p = mv], which is 1 for [y < 0]. *)
assert (Q : (if r =? 1 then Some 1 else if Rlt_bool (B2R y) 0 then None
             else DyadicPow.small_power r p) = Some mv).
{ destruct (r =? 1) eqn:R1.
  - apply Z.eqb_eq in R1. rewrite Emv, R1, Z.pow_1_l by lia. reflexivity.
  - apply Z.eqb_neq in R1.
    destruct (Rlt_bool (B2R y) 0); [destruct Hneg as [Hr1 _]; contradiction |].
    apply (proj2 (small_power_spec r p mv ltac:(lia) ltac:(lia))).
    split; [exact Emv | rewrite <- Emv; lia]. }
assert (E : (if Rlt_bool (B2R y) 0 then - (er * p) else er * p) = ev).
{ destruct (Rlt_bool (B2R y) 0); [destruct Hneg as [_ Hneg] |]; lia. }
rewrite RL, Ly. cbv beta iota zeta. rewrite Q. cbv beta iota zeta. rewrite E.
rewrite (proj2 (range_check mv ev ltac:(lia)) (conj Hev1 Hev2)). cbv beta iota.
destruct (exact_tail mv ev ltac:(lia) Hev1 Hev2) as (w & Hw & Fw & Ew).
rewrite Hw. do 2 f_equal.
assert (Hw0 : B2R w <> 0%R) by lra.
apply B2R_inj; [apply is_finite_strict_B2R; exact Hw0 | apply is_finite_strict_B2R; lra | lra].
Qed.
