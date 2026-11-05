(** * Division of limbs: Algorithm D of Knuth

    [Limbs.div_rem] of [Model.v] computes the quotient and the remainder
    of a division of naturals, by one limb or by Algorithm D of Knuth, The
    Art of Computer Programming, vol. 2, 3rd ed., 4.3.1, with base
    [B = 2^64]: the estimate [qhat] of each quotient limb is at most 2 too
    large once the top limb of the divisor is at least [B/2] (Theorem B),
    so that the loop of D3 tests its condition at most 3 times, and the
    add-back of D6 happens at most once. [KnuthStep.v] proves one step
    (D3-D6); this file proves the loop over the windows (D2, D7), the
    normalization (D1, D8) and the cases of [div_rem]. *)

From Stdlib Require Import ZArith Lia List.
(* [Limbs] last, so that its helpers take precedence over any of the same
   name in [KnuthStep]. *)
From Inari Require Import Model KnuthStep Limbs.

Open Scope Z_scope.

(** ** Helpers *)

Local Ltac split_all := repeat match goal with |- _ /\ _ => split end.

(** The [_] arm of a [match] on a [comparison] that is not [Lt]. *)
Lemma match_lt_else :
  forall (T : Type) (c : comparison) (a b : T),
  c <> Lt -> match c with Lt => a | _ => b end = b.
Proof. intros T [] a b H; [reflexivity | congruence | reflexivity]. Qed.

(** [a / b < c] makes [a < b * c]. *)
Lemma div_lt_mul : forall a b c, 0 < b -> a / b < c -> a < b * c.
Proof.
  intros a b c Hb H.
  pose proof (Z.div_mod a b ltac:(lia)) as E. pose proof (Z.mod_pos_bound a b Hb).
  nia.
Qed.

(** The quotient and the remainder of [s0 + P * s1] by [P * d1], for a
    low part [s0 < P]. *)
Lemma div_shift :
  forall s0 s1 P d1,
  0 <= s0 < P -> 0 < d1 ->
  (s0 + P * s1) / (P * d1) = s1 / d1 /\
  (s0 + P * s1) mod (P * d1) = s0 + P * (s1 mod d1).
Proof.
  intros s0 s1 P d1 Hs0 Hd1. split.
  - rewrite <- Z.div_div by lia. rewrite div_split by lia. reflexivity.
  - apply mod_split; lia.
Qed.

(** ** D1-D8 *)

(** D2 and D7: before the step [j = k - 1], the quotient limbs from [k]
    up are in [acc], and [u[k..] < v]. *)
Lemma knuth_loop_correct :
  forall k u v acc,
  limbs_ok u -> limbs_ok v -> limbs_ok acc -> (2 <= length v)%nat ->
  2 ^ 63 <= Limbs.limb v (length v - 1) ->
  (k + length v <= length u)%nat ->
  Limbs.val (skipn k u) < Limbs.val v ->
  exists q u',
  Limbs.knuth_loop k u v acc = Some (q, u') /\ limbs_ok q /\ limbs_ok u' /\
  length q = (k + length acc)%nat /\ length u' = length u /\
  Limbs.val u' < Limbs.val v /\
  Limbs.val u' + Limbs.val v * Limbs.val q =
  Limbs.val u + Limbs.val v * 2 ^ (64 * Z.of_nat k) * Limbs.val acc.
Proof.
  induction k as [|j IH]; intros u v acc Hu Hv Hacc Hn Hv1 Hlen Hlt.
  - exists acc, u. cbn [Limbs.knuth_loop skipn] in *.
    rewrite pow64_0. repeat split; try assumption; try lia.
  - cbn [Limbs.knuth_loop].
    pose proof (val_bounds v Hv) as HVb.
    pose proof (val_bounds (skipn (S j) u) (limbs_ok_skipn _ _ Hu)) as HSb.
    pose proof (pow64_pos j) as HP.
    remember (2 ^ (64 * Z.of_nat j)) as P eqn:HPdef.
    remember (Limbs.val u / P) as Y eqn:HYdef.
    assert (HYS : Limbs.val (skipn (S j) u) = Y / 2 ^ 64).
    { rewrite val_skipn by exact Hu. rewrite pow64_S, <- HPdef, Z.mul_comm.
      rewrite <- Z.div_div by lia. rewrite HYdef. reflexivity. }
    assert (HY0 : 0 <= Y).
    { rewrite HYdef. apply Z.div_pos; [apply val_bounds; exact Hu | lia]. }
    assert (HYlt : Y < 2 ^ 64 * Limbs.val v).
    { apply div_lt_mul; [lia |]. rewrite <- HYS. exact Hlt. }
    remember (firstn (S (length v)) (skipn j u)) as w eqn:Hw.
    assert (Hwok : limbs_ok w).
    { rewrite Hw. apply limbs_ok_firstn, limbs_ok_skipn. exact Hu. }
    assert (Hlw : length w = S (length v)).
    { rewrite Hw, length_firstn, length_skipn. lia. }
    assert (Hwval : Limbs.val w = Y).
    { rewrite Hw, val_firstn, val_skipn by (try apply limbs_ok_skipn; exact Hu).
      rewrite <- HPdef, <- HYdef. apply Z.mod_small. rewrite pow64_S. nia. }
    assert (Hw1 : Limbs.val (skipn 1 w) < Limbs.val v).
    { rewrite val_skipn by exact Hwok. change (64 * Z.of_nat 1) with 64.
      rewrite Hwval, <- HYS. exact Hlt. }
    destruct (knuth_step_correct w v Hwok Hv Hn Hlw Hv1 Hw1)
      as (q & w' & Hstep & Hw'ok & Hlw' & Hq & Hw'val).
    rewrite Hstep. cbv beta iota.
    assert (HV0 : 0 < Limbs.val v) by lia.
    assert (Hqb : 0 <= q < 2 ^ 64).
    { rewrite Hq, Hwval. split; [apply Z.div_pos; lia |].
      apply Z.div_lt_upper_bound; lia. }
    assert (Hqw : Limbs.val w = Limbs.val v * q + Limbs.val w').
    { rewrite Hq, Hw'val. apply Z.div_mod. lia. }
    assert (Hw'b : 0 <= Limbs.val w' < Limbs.val v).
    { rewrite Hw'val. apply Z.mod_pos_bound. exact HV0. }
    assert (Hlu : (j + length w' <= length u)%nat) by lia.
    assert (Hupd :
      Limbs.val (Limbs.update u j w') = Limbs.val u - P * (Limbs.val v * q)).
    { rewrite val_update by assumption. rewrite Hlw', Hlw, <- Hw, <- HPdef. lia. }
    assert (Hu'ok : limbs_ok (Limbs.update u j w')).
    { apply limbs_ok_update; assumption. }
    assert (Hlu' : length (Limbs.update u j w') = length u).
    { apply update_length. exact Hlu. }
    assert (Hlt' : Limbs.val (skipn j (Limbs.update u j w')) < Limbs.val v).
    { rewrite val_skipn by exact Hu'ok. rewrite <- HPdef, Hupd.
      pose proof (Z.div_mod (Limbs.val u) P ltac:(lia)) as E.
      pose proof (Z.mod_pos_bound (Limbs.val u) P HP) as Hm.
      rewrite <- HYdef in E.
      replace (Limbs.val u - P * (Limbs.val v * q))
        with (Limbs.val u mod P + P * Limbs.val w') by lia.
      rewrite div_split by lia. lia. }
    assert (Hacc' : limbs_ok (q :: acc)).
    { apply limbs_ok_cons. split; assumption. }
    destruct (IH (Limbs.update u j w') v (q :: acc) Hu'ok Hv Hacc' Hn Hv1
                 ltac:(rewrite Hlu'; lia) Hlt')
      as (q0 & u0 & Hloop & Hq0ok & Hu0ok & Hlq0 & Hlu0 & Hu0lt & Heq).
    exists q0, u0. split; [exact Hloop |].
    repeat split; try assumption.
    + rewrite Hlq0. cbn [length]. lia.
    + rewrite Hlu0, Hlu'. reflexivity.
    + rewrite Heq, Hupd. cbn [Limbs.val]. rewrite pow64_S, <- HPdef. ring.
Qed.

Lemma div_rem_knuth_correct :
  forall x d,
  limbs_ok x -> limbs_ok d -> (2 <= length d <= length x)%nat ->
  Limbs.limb d (length d - 1) <> 0 ->
  exists q r,
  Limbs.div_rem_knuth x d = Some (q, r) /\ limbs_ok q /\ limbs_ok r /\
  length q = S (length x - length d) /\ length r = length d /\
  Limbs.val q = Limbs.val x / Limbs.val d /\ Limbs.val r = Limbs.val x mod Limbs.val d.
Proof.
  intros x d Hx Hd [Hn Hnx] Htop.
  unfold Limbs.div_rem_knuth. cbv zeta.
  (* D1: the top limb [dt] of [d] shifted by [s] bits is in [[B/2, B)]. *)
  assert (Hdt : 0 < Limbs.limb d (length d - 1) < 2 ^ 64).
  { pose proof (limb_bound d (length d - 1) Hd). lia. }
  remember (Limbs.limb d (length d - 1)) as dt eqn:Hdtdef.
  remember (leading_zeros 64 dt) as s eqn:Hsdef.
  pose proof (Z.log2_spec dt (proj1 Hdt)) as HL.
  assert (HL64 : Z.log2 dt < 64) by (apply Z.log2_lt_pow2; lia).
  pose proof (Z.log2_nonneg dt) as HL0.
  assert (Hs : s = 63 - Z.log2 dt).
  { rewrite Hsdef. unfold leading_zeros. destruct (Z.eqb_spec dt 0); lia. }
  assert (Hs0 : 0 <= s) by lia.
  assert (HA0 : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert (HA63 : 2 ^ s <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
  assert (HT : 2 ^ 63 <= dt * 2 ^ s /\ dt * 2 ^ s + 2 ^ s <= 2 ^ 64).
  { assert (E1 : 2 ^ Z.log2 dt * 2 ^ s = 2 ^ 63)
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (E2 : 2 ^ Z.succ (Z.log2 dt) * 2 ^ s = 2 ^ 64)
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    split; nia. }
  (* [d = lo + B^(n-1) dt], so that [B^(n-1) B/2 <= d 2^s < B^n]. *)
  pose proof (val_bounds x Hx) as HXb. pose proof (val_bounds d Hd) as HDb.
  assert (Hdnil : d <> nil) by (intros ->; cbn [length] in Hn; lia).
  pose proof (val_last d Hdnil) as HD. rewrite <- Hdtdef in HD.
  pose proof (val_bounds (firstn (length d - 1) d) (limbs_ok_firstn _ _ Hd)) as Hlo.
  rewrite length_firstn, Nat.min_l in Hlo by lia.
  pose proof (pow64_S (length d - 1)) as HBn.
  replace (S (length d - 1)) with (length d) in HBn by lia.
  assert (HDge : 2 ^ (64 * Z.of_nat (length d - 1)) <= Limbs.val d).
  { rewrite HD. nia. }
  assert (HD0 : 0 < Limbs.val d).
  { pose proof (pow64_pos (length d - 1)). lia. }
  assert (HDA :
    2 ^ (64 * Z.of_nat (length d - 1)) * 2 ^ 63 <= Limbs.val d * 2 ^ s <
    2 ^ (64 * Z.of_nat (length d))).
  { rewrite HBn, HD.
    remember (2 ^ (64 * Z.of_nat (length d - 1))) as Bn1.
    remember (Limbs.val (firstn (length d - 1) d)) as lo.
    remember (2 ^ s) as A.
    nia. }
  (* [v = d 2^s], of [n] limbs, with its top limb at least [B/2]. *)
  destruct (shl_into_correct (S (length d)) d s Hd Hs0) as (Hv0ok & Hv0l & Hv0v).
  remember (firstn (length d) (Limbs.shl_into (S (length d)) d s)) as v eqn:Hvdef.
  assert (Hvok : limbs_ok v).
  { rewrite Hvdef. apply limbs_ok_firstn. exact Hv0ok. }
  assert (Hlv : length v = length d).
  { rewrite Hvdef, length_firstn, Hv0l. lia. }
  assert (Hvv : Limbs.val v = Limbs.val d * 2 ^ s).
  { rewrite Hvdef, val_firstn, Hv0v by exact Hv0ok.
    assert (0 <= Limbs.val d * 2 ^ s) by (apply Z.mul_nonneg_nonneg; lia).
    rewrite (Z.mod_small (Limbs.val d * 2 ^ s) (2 ^ (64 * Z.of_nat (S (length d))))).
    - apply Z.mod_small. lia.
    - rewrite pow64_S. lia. }
  assert (HV : 2 ^ 63 <= Limbs.limb v (length v - 1)).
  { rewrite (limb_val v _ Hvok), Hvv, Hlv.
    pose proof (pow64_pos (length d - 1)).
    rewrite Z.mod_small.
    - apply Z.div_le_lower_bound; lia.
    - split; [apply Z.div_pos; lia |].
      apply Z.div_lt_upper_bound; lia. }
  (* [u = x 2^s], of [m + n + 1] limbs. *)
  destruct (shl_into_correct (S (length x)) x s Hx Hs0) as (Huok & Hlu & Huv).
  remember (Limbs.shl_into (S (length x)) x s) as u eqn:Hudef.
  assert (Huv' : Limbs.val u = Limbs.val x * 2 ^ s).
  { rewrite Huv. apply Z.mod_small. rewrite pow64_S.
    split; [apply Z.mul_nonneg_nonneg; lia |].
    remember (2 ^ (64 * Z.of_nat (length x))) as Bx. remember (2 ^ s) as A. nia. }
  (* D2-D7: before the first step, [u[m + 1..] < B^(n-1) 2^s <= v]. *)
  assert (Hk : (S (length x - length d) + length v <= length u)%nat) by lia.
  assert (Hwin : Limbs.val (skipn (S (length x - length d)) u) < Limbs.val v).
  { rewrite val_skipn, Huv', Hvv by exact Huok.
    apply Z.div_lt_upper_bound; [apply pow64_pos |].
    pose proof (pow64_add (S (length x - length d)) (length d - 1)) as E.
    replace (S (length x - length d) + (length d - 1))%nat with (length x) in E by lia.
    pose proof (pow64_pos (S (length x - length d))).
    remember (2 ^ (64 * Z.of_nat (S (length x - length d)))) as Bk.
    remember (2 ^ (64 * Z.of_nat (length d - 1))) as Bn1.
    remember (2 ^ (64 * Z.of_nat (length x))) as Bx.
    remember (2 ^ s) as A.
    assert (Limbs.val x * A < Bx * A) by nia.
    assert (Bk * Bn1 * A <= Bk * (Limbs.val d * A)) by nia.
    nia. }
  assert (Hnil : limbs_ok nil) by constructor.
  assert (Hlv2 : (2 <= length v)%nat) by lia.
  destruct (knuth_loop_correct (S (length x - length d)) u v nil Huok Hvok Hnil Hlv2 HV Hk
              Hwin)
    as (q & u' & Hloop & Hqok & Hu'ok & Hlq & _ & Hu'lt & Heq).
  rewrite Hloop. cbv beta iota.
  exists q, (Limbs.shr_into (length d) (firstn (length d) u') s).
  split; [reflexivity |].
  (* [q = u / v] and [u' = u mod v = (x mod d) 2^s]. *)
  cbn [Limbs.val] in Heq. rewrite Z.mul_0_r, Z.add_0_r, Huv', Hvv in Heq.
  rewrite Hvv in Hu'lt.
  pose proof (val_bounds u' Hu'ok) as Hu'b.
  assert (Hqv : Limbs.val q = Limbs.val x / Limbs.val d).
  { rewrite <- (Z.div_mul_cancel_r (Limbs.val x) (Limbs.val d) (2 ^ s)) by lia.
    apply (Z.div_unique _ _ _ (Limbs.val u')); [left; lia | lia]. }
  assert (Hrv : Limbs.val u' = Limbs.val x mod Limbs.val d * 2 ^ s).
  { rewrite <- Z.mul_mod_distr_r by lia.
    apply (Z.mod_unique _ _ (Limbs.val q)); [left; lia | lia]. }
  (* D8: the remainder is [u'] shifted back by [s] bits. *)
  assert (Hfu : Limbs.val (firstn (length d) u') = Limbs.val u').
  { rewrite val_firstn by exact Hu'ok. apply Z.mod_small. lia. }
  destruct (shr_into_correct (length d) (firstn (length d) u') s
              (limbs_ok_firstn _ _ Hu'ok) Hs0) as (Hrok & Hlr & Hrv').
  pose proof (Z.mod_pos_bound (Limbs.val x) (Limbs.val d) HD0).
  split_all; try assumption.
  - rewrite Hlq. cbn [length]. lia.
  - rewrite Hrv', Hfu, Hrv, Z.div_mul by lia. apply Z.mod_small. lia.
Qed.

(** ** The cases of [div_rem] *)

Lemma zeros_low_le : forall d, (Limbs.zeros_low d <= length d)%nat.
Proof.
  induction d as [|a d IH]; cbn [Limbs.zeros_low length]; [lia |].
  destruct (a =? 0); lia.
Qed.

Lemma zeros_low_firstn :
  forall d, firstn (Limbs.zeros_low d) d = repeat 0 (Limbs.zeros_low d).
Proof.
  induction d as [|a d IH]; cbn [Limbs.zeros_low]; [reflexivity |].
  destruct (Z.eqb_spec a 0) as [-> | _]; cbn [firstn repeat]; [rewrite IH |]; reflexivity.
Qed.

Lemma zeros_low_limb : forall d k, (k < Limbs.zeros_low d)%nat -> Limbs.limb d k = 0.
Proof.
  induction d as [|a d IH]; intros k Hk; cbn [Limbs.zeros_low] in Hk; [lia |].
  destruct (Z.eqb_spec a 0) as [Ha | _]; [| lia].
  destruct k as [|k].
  - rewrite limb_cons_0. exact Ha.
  - rewrite limb_cons_S. apply IH. lia.
Qed.

Lemma div_rem_correct :
  forall x d,
  limbs_ok x -> limbs_ok d -> Limbs.val d <> 0 ->
  exists q r,
  Limbs.div_rem x d = Some (q, r) /\ limbs_ok q /\ limbs_ok r /\
  length q = length x /\ length r = length d /\
  Limbs.val q = Limbs.val x / Limbs.val d /\ Limbs.val r = Limbs.val x mod Limbs.val d.
Proof.
  intros x d Hx Hd Hd0.
  pose proof (rposition_nonzero_correct d Hd) as Hr.
  pose proof (val_bounds x Hx) as Hxb. pose proof (val_bounds d Hd) as Hdb.
  unfold Limbs.div_rem.
  destruct (Limbs.rposition_nonzero d) as [i |]; [| lia].
  destruct Hr as (Hi & Hdi & Hdlo & Hdhi).
  cbv beta iota zeta.
  rewrite (cmp_correct x d Hx Hd).
  destruct (Z.ltb_spec (Limbs.val x) (Limbs.val d)) as [Hlt | Hge].
  - (* x < d: the quotient is 0 and the remainder [x]. *)
    rewrite (proj2 (Z.compare_lt_iff _ _) Hlt). cbv beta iota.
    exists (repeat 0 (length x)), (map (Limbs.limb x) (seq 0 (length d))).
    split; [reflexivity |].
    assert (Hm : Limbs.val (map (Limbs.limb x) (seq 0 (length d))) = Limbs.val x).
    { rewrite (val_map_seq (Limbs.limb x) (Limbs.val x) 0 (length d))
        by (intros k; apply limb_val; exact Hx).
      rewrite pow64_0, Z.div_1_r. apply Z.mod_small. lia. }
    split_all.
    + apply limbs_ok_repeat0.
    + unfold limbs_ok. apply Forall_forall. intros a Ha.
      apply in_map_iff in Ha. destruct Ha as (k & <- & _). apply limb_bound. exact Hx.
    + apply repeat_length.
    + rewrite length_map, length_seq. reflexivity.
    + rewrite val_repeat0. symmetry. apply Z.div_small. lia.
    + rewrite Hm. symmetry. apply Z.mod_small. lia.
  - assert (Hne : Z.compare (Limbs.val x) (Limbs.val d) <> Lt)
      by (apply Z.compare_ge_iff; exact Hge).
    rewrite (match_lt_else _ _ _ _ Hne).
    (* The [j] zero limbs at the bottom of [d]. *)
    pose proof (zeros_low_le d) as Hjl.
    pose proof (zeros_low_firstn d) as Hj0.
    pose proof (zeros_low_limb d) as Hjz.
    remember (Limbs.zeros_low d) as j eqn:Hjdef.
    assert (Hji : (j <= i)%nat).
    { destruct (Nat.le_gt_cases j i) as [H | H]; [exact H |].
      exfalso. apply Hdi. apply Hjz. exact H. }
    assert (Hix : (i < length x)%nat).
    { destruct (Nat.lt_ge_cases i (length x)) as [H | H]; [exact H |].
      assert (2 ^ (64 * Z.of_nat (length x)) <= 2 ^ (64 * Z.of_nat i))
        by (apply Z.pow_le_mono_r; lia).
      lia. }
    pose proof (pow64_pos j) as HP.
    pose proof (pow64_add j (S i - j)) as HPadd.
    replace (j + (S i - j))%nat with (S i) in HPadd by lia.
    remember (2 ^ (64 * Z.of_nat j)) as P eqn:HPdef.
    remember (2 ^ (64 * Z.of_nat (S i - j))) as Q eqn:HQdef.
    (* d = d1 * P *)
    assert (Hdsplit : Limbs.val d = P * Limbs.val (skipn j d)).
    { rewrite (val_split j d) by lia. rewrite Hj0, val_repeat0, <- HPdef. ring. }
    pose proof (val_bounds (skipn j d) (limbs_ok_skipn _ _ Hd)) as Hd'b.
    assert (Hd'Q : Limbs.val (skipn j d) < Q).
    { apply (Z.mul_lt_mono_pos_l P); lia. }
    remember (firstn (S i - j) (skipn j d)) as d1 eqn:Hd1def.
    assert (Hd1ok : limbs_ok d1).
    { rewrite Hd1def. apply limbs_ok_firstn, limbs_ok_skipn. exact Hd. }
    assert (Hld1 : length d1 = (S i - j)%nat).
    { rewrite Hd1def, length_firstn, length_skipn. lia. }
    assert (HdP : Limbs.val d = P * Limbs.val d1).
    { rewrite Hdsplit, Hd1def, val_firstn by (apply limbs_ok_skipn; exact Hd).
      rewrite <- HQdef, Z.mod_small by lia. reflexivity. }
    assert (HD1 : 0 < Limbs.val d1).
    { pose proof (val_bounds d1 Hd1ok).
      destruct (Z.eq_dec (Limbs.val d1) 0) as [E | E]; [| lia].
      rewrite E, Z.mul_0_r in HdP. lia. }
    (* x = s1 * P + s0 *)
    assert (Hxsplit : Limbs.val x = Limbs.val (firstn j x) + P * Limbs.val (skipn j x)).
    { rewrite (val_split j x) by lia. rewrite <- HPdef. reflexivity. }
    pose proof (val_bounds (firstn j x) (limbs_ok_firstn _ _ Hx)) as Hs0b.
    rewrite length_firstn in Hs0b. replace (Nat.min j (length x)) with j in Hs0b by lia.
    rewrite <- HPdef in Hs0b.
    destruct (div_shift (Limbs.val (firstn j x)) (Limbs.val (skipn j x)) P (Limbs.val d1)
                Hs0b HD1) as [Hdiv Hmod].
    rewrite <- Hxsplit, <- HdP in Hdiv, Hmod.
    assert (Hls1 : length (skipn j x) = (length x - j)%nat) by apply length_skipn.
    assert (Hd1s1 : (length d1 <= length (skipn j x))%nat) by lia.
    assert (Hs0l : length (firstn j x) = j).
    { rewrite length_firstn. lia. }
    destruct d1 as [| c [| c' d1']].
    + cbn [length] in Hld1. lia.
    + (* A divisor of one limb [c]. *)
      cbv beta iota.
      assert (Hc : Limbs.val (c :: nil) = c) by (cbn [Limbs.val]; ring).
      rewrite Hc in Hdiv, Hmod, HD1.
      apply limbs_ok_cons in Hd1ok as [Hcb _].
      assert (Hc0 : 0 < c < 2 ^ 64) by lia.
      destruct (div_rem_limb_correct (skipn j x) c (limbs_ok_skipn _ _ Hx) Hc0)
        as (q1 & r1 & Hq1e & Hq1ok & Hlq1 & Hq1v & Hr1).
      rewrite Hq1e. cbv beta iota.
      exists (q1 ++ repeat 0 (length x - length (skipn j x))),
        (firstn j x ++ r1 :: repeat 0 (length d - j - 1)).
      split; [reflexivity |].
      assert (Hr1b : 0 <= r1 < c) by (rewrite Hr1; apply Z.mod_pos_bound; lia).
      split_all.
      * apply limbs_ok_app; [exact Hq1ok | apply limbs_ok_repeat0].
      * apply limbs_ok_app; [apply limbs_ok_firstn; exact Hx |].
        apply limbs_ok_cons. split; [lia | apply limbs_ok_repeat0].
      * rewrite length_app, repeat_length, Hlq1, Hls1. lia.
      * rewrite length_app, Hs0l. cbn [length]. rewrite repeat_length. lia.
      * rewrite val_app, val_repeat0, Z.mul_0_r, Z.add_0_r, Hq1v, Hdiv. reflexivity.
      * rewrite val_app, Hs0l, <- HPdef. cbn [Limbs.val]. rewrite val_repeat0, Hmod, Hr1.
        ring.
    + (* Algorithm D, for a divisor of at least two limbs. *)
      cbv beta iota.
      remember (c :: c' :: d1') as d1 eqn:Hd1e in *.
      assert (Hld1' : (2 <= length d1)%nat) by (rewrite Hd1e; cbn [length]; lia).
      assert (Htop1 : Limbs.limb d1 (length d1 - 1) <> 0).
      { rewrite Hld1, Hd1def. unfold Limbs.limb. rewrite nth_firstn.
        replace (S i - j - 1 <? S i - j)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_skipn. replace (j + (S i - j - 1))%nat with i by lia. exact Hdi. }
      destruct (div_rem_knuth_correct (skipn j x) d1 (limbs_ok_skipn _ _ Hx) Hd1ok
                  (conj Hld1' Hd1s1) Htop1)
        as (q1 & r1 & Hk & Hq1ok & Hr1ok & Hlq1 & Hlr1 & Hq1v & Hr1v).
      rewrite Hk. cbv beta iota.
      exists (q1 ++ repeat 0 (length x - (length (skipn j x) - length d1 + 1))),
        (firstn j x ++ r1 ++ repeat 0 (length d - S i)).
      split; [reflexivity |].
      split_all.
      * apply limbs_ok_app; [exact Hq1ok | apply limbs_ok_repeat0].
      * apply limbs_ok_app; [apply limbs_ok_firstn; exact Hx |].
        apply limbs_ok_app; [exact Hr1ok | apply limbs_ok_repeat0].
      * rewrite length_app, repeat_length, Hlq1, Hls1. lia.
      * rewrite !length_app, Hs0l, repeat_length, Hlr1, Hld1. lia.
      * rewrite val_app, val_repeat0, Z.mul_0_r, Z.add_0_r, Hq1v, Hdiv. reflexivity.
      * rewrite !val_app, val_repeat0, Z.mul_0_r, Z.add_0_r, Hs0l, <- HPdef, Hmod, Hr1v.
        reflexivity.
Qed.

(** [expect("division by zero")] *)
Lemma div_rem_zero : forall x d, limbs_ok d -> Limbs.val d = 0 -> Limbs.div_rem x d = None.
Proof.
  intros x d Hd H0. unfold Limbs.div_rem.
  pose proof (rposition_nonzero_correct d Hd) as Hr.
  destruct (Limbs.rposition_nonzero d) as [i |]; [| reflexivity].
  destruct Hr as (_ & _ & Hlo & _). pose proof (pow64_pos i). lia.
Qed.
