(** * The integer square root of the dyadic kernel

    [Dyadic.isqrt], Newton's iteration on limbs, returns [floor(sqrt(x))]
    for the [x] of [2 n + 1] limbs that [Dyadic.sqrt] passes it, and its
    fuel is enough. [DyOps.v] uses it for [Dyadic.sqrt]. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core.
From Inari Require Import Model Limbs Knuth DyRound.

Open Scope Z_scope.
Open Scope list_scope.

(** ** The seed *)

(** The seed [c] is the implicit bit of an [f64] above the top 31 bits of
    its fraction, so [2^31 <= c < 2^32] whatever the bits [b] of the square
    root are. *)
Lemma seed_bounds :
  forall b,
  2 ^ 31 <= Z.shiftr (Z.lor (Z.land b (Z.shiftl 1 52 - 1)) (Z.shiftl 1 52)) 21 < 2 ^ 32.
Proof.
  intros b.
  change (Z.shiftl 1 52 - 1) with (Z.ones 52).
  rewrite Z.land_ones by lia.
  assert (Hm : 0 <= b mod 2 ^ 52 < 2 ^ 52) by (apply Z.mod_pos_bound; lia).
  change (Z.shiftl 1 52) with (1 * 2 ^ 52).
  rewrite Z.lor_comm, lor_low by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia.
Qed.

(** ** Newton's step on integers *)

(** From any [s > 0], the step [floor((floor(x / s) + s) / 2)] is at least
    [r = floor(sqrt(x))], by the inequality of the arithmetic and geometric
    means: if [x / s + s <= 2 r - 1], then
    [(x / s + 1) s <= (2 r - s) s = r^2 - (r - s)^2 <= x], against
    [x < (x / s + 1) s]. *)
Lemma newton_ge : forall x s, 0 <= x -> 0 < s -> Z.sqrt x <= (x / s + s) / 2.
Proof.
  intros x s Hx Hs.
  pose proof (Z.sqrt_spec x Hx) as Hr. cbv zeta in Hr. destruct Hr as [Hr1 Hr2].
  assert (Hm : 0 <= x mod s < s) by (apply Z.mod_pos_bound; lia).
  assert (Hs0 : s <> 0) by lia.
  pose proof (Z.div_mod x s Hs0) as Hd.
  remember (Z.sqrt x) as r eqn:Er. remember (x / s) as q eqn:Eq.
  remember (x mod s) as m eqn:Em. clear Er Eq Em.
  destruct (Z.le_gt_cases r ((q + s) / 2)) as [H | H]; [exact H | exfalso].
  assert (Hq : q + 1 <= 2 * r - s) by (Z.div_mod_to_equations; lia).
  assert (H1 : s * (q + 1) <= s * (2 * r - s)) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (H2 : 0 <= (r - s) * (r - s)) by apply Z.square_nonneg.
  nia.
Qed.

(** Above [r = floor(sqrt(x))], the step lowers [s]: [s >= r + 1] gives
    [s^2 > x], so [x / s <= s - 1]. *)
Lemma newton_lt : forall x s, 0 <= x -> Z.sqrt x < s -> (x / s + s) / 2 < s.
Proof.
  intros x s Hx Hs.
  pose proof (Z.sqrt_spec x Hx) as Hr. cbv zeta in Hr. destruct Hr as [Hr1 Hr2].
  pose proof (Z.sqrt_nonneg x) as Hr0.
  assert (Hq : x / s < s).
  { apply Z.div_lt_upper_bound; [lia |].
    assert (Z.succ (Z.sqrt x) * Z.succ (Z.sqrt x) <= s * s)
      by (apply Z.mul_le_mono_nonneg; lia).
    lia. }
  remember (x / s) as q eqn:Eq. clear Eq.
  Z.div_mod_to_equations. lia.
Qed.

(** From [1 <= s <= x], the step is at most [x]. *)
Lemma newton_le : forall x s, 1 <= s <= x -> (x / s + s) / 2 <= x.
Proof.
  intros x s Hs.
  assert (Hq : x / s <= x) by (apply Z.div_le_upper_bound; nia).
  assert (Hq0 : 0 <= x / s) by (apply Z.div_pos; lia).
  remember (x / s) as q eqn:Eq. clear Eq.
  Z.div_mod_to_equations. lia.
Qed.

(** [floor(sqrt(x)) >= 2^(N - 1)] for [x >= 2^(2 N - 1)]. *)
Lemma sqrt_lower : forall N x, 1 <= N -> 2 ^ (2 * N - 1) <= x -> 2 ^ (N - 1) <= Z.sqrt x.
Proof.
  intros N x HN Hx.
  assert (H0 : 0 < 2 ^ (N - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (H1 : 0 < 2 ^ (2 * N - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (Ha : 0 <= x) by lia.
  assert (Hb : 0 <= 2 ^ (N - 1)) by lia.
  apply (proj1 (Z.sqrt_le_square x (2 ^ (N - 1)) Ha Hb)).
  rewrite <- Z.pow_add_r by lia.
  assert (2 ^ (N - 1 + (N - 1)) <= 2 ^ (2 * N - 1)) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

(** ** One step on limbs *)

(** One step of [isqrt_loop] from [s] with
    [2^(64 n - 1) <= s < 2^(64 (n + 1))]: [div_rem] gives [x / s], which is
    below [2^(64 n + 2)] as [x < 2^(128 n + 1)] and [s >= 2^(64 n - 1)]; its
    sum with [s] does not carry out of the [2 n + 1] limbs of the quotient;
    and the shift by one bit gives the step [y], which fits the [n + 1]
    limbs. *)
Lemma isqrt_step :
  forall f n x s first,
  level_ok n -> limbs_ok x -> length x = (2 * n + 1)%nat ->
  Limbs.val x < 2 ^ (128 * Z.of_nat n + 1) ->
  limbs_ok s -> length s = S n ->
  2 ^ (64 * Z.of_nat n - 1) <= Limbs.val s < 2 ^ (64 * Z.of_nat (S n)) ->
  exists y,
  limbs_ok y /\ length y = S n /\
  Limbs.val y = (Limbs.val x / Limbs.val s + Limbs.val s) / 2 /\
  Dyadic.isqrt_loop (S f) n x s first =
  if negb first && negb (Limbs.val y <? Limbs.val s) then Some s
  else Dyadic.isqrt_loop f n x y false.
Proof.
  intros f n x s first Hn Hx Hlx Hxb Hs Hls [Hs1 Hs2].
  unfold level_ok in Hn.
  remember (64 * Z.of_nat n) as N eqn:HN.
  assert (E2N : 128 * Z.of_nat n = 2 * N) by lia.
  assert (ESn : 64 * Z.of_nat (S n) = N + 64) by lia.
  rewrite E2N in Hxb. rewrite ESn in Hs2.
  pose proof (val_bounds x Hx) as Hx0.
  assert (Hp1 : 0 < 2 ^ (N - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hs0 : Limbs.val s <> 0) by lia.
  destruct (div_rem_correct x s Hx Hs Hs0) as (q & rr & Hdr & Hq & _ & Hlq & _ & Hvq & _).
  pose proof (val_bounds q Hq) as Hq0.
  (* [x / s < 2^(N + 2)], as [x < 2^(2 N + 1) = 2^(N - 1) 2^(N + 2) <= s 2^(N + 2)]. *)
  assert (Hp2 : 0 < 2 ^ (N + 2)) by (apply Z.pow_pos_nonneg; lia).
  assert (E1 : 2 ^ (2 * N + 1) = 2 ^ (N - 1) * 2 ^ (N + 2)).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (Hqb : Limbs.val q < 2 ^ (N + 2)).
  { rewrite Hvq. apply Z.div_lt_upper_bound; [lia |].
    assert (2 ^ (N - 1) * 2 ^ (N + 2) <= Limbs.val s * 2 ^ (N + 2))
      by (apply Z.mul_le_mono_nonneg_r; lia).
    lia. }
  (* [x / s + s < 2 2^(N + 64) = 2^(N + 65) <= 2^(2 N + 64)]: no carry out
     of [q]. *)
  assert (E3 : 2 ^ (N + 2) <= 2 ^ (N + 64)) by (apply Z.pow_le_mono_r; lia).
  assert (E4 : 2 ^ (N + 65) = 2 * 2 ^ (N + 64)).
  { replace (N + 65) with (1 + (N + 64)) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
  assert (E5 : 2 ^ (N + 65) <= 2 ^ (64 * Z.of_nat (length q))).
  { apply Z.pow_le_mono_r; [lia |]. rewrite Hlq, Hlx. lia. }
  assert (Hlen : (length s <= length q)%nat) by lia.
  destruct (Limbs.add_assign q s) as [q' c] eqn:Ha.
  destruct (add_assign_correct q s q' c Hq Hs Hlen Ha) as (Hq' & Hlq' & Hvq').
  pose proof (val_bounds q' Hq') as Hq'0.
  assert (Hc : c = false).
  { destruct c; [exfalso | reflexivity]. cbn [Z.b2z] in Hvq'. rewrite Hlq' in Hq'0. lia. }
  subst c. cbn [Z.b2z] in Hvq'. rewrite Z.mul_0_l, Z.add_0_r in Hvq'.
  assert (H01 : 0 <= 1) by lia.
  destruct (shr_into_correct (S n) q' 1 Hq' H01) as (Hy & Hly & Hvy).
  exists (Limbs.shr_into (S n) q' 1).
  assert (Hyv :
    Limbs.val (Limbs.shr_into (S n) q' 1) = (Limbs.val x / Limbs.val s + Limbs.val s) / 2).
  { rewrite Hvy, Z.pow_1_r, Hvq', <- Hvq, ESn. apply Z.mod_small.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  split; [exact Hy |]. split; [exact Hly |]. split; [exact Hyv |].
  cbn [Dyadic.isqrt_loop]. rewrite Hdr. cbv beta iota zeta. rewrite Ha. cbn [fst].
  rewrite (Inari.Limbs.cmp_correct _ _ Hy Hs). reflexivity.
Qed.

(** ** The loop *)

(** From [s >= r = floor(sqrt(x))] after the first step, each step lowers
    [s] by at least one until [s = r] ([newton_lt]), and stays at least [r]
    ([newton_ge]); at [s = r] the step is at least [s], so the loop stops
    with [s]. That takes [s - r + 1] steps of fuel. *)
Lemma isqrt_loop_correct :
  forall f n x s,
  level_ok n -> limbs_ok x -> length x = (2 * n + 1)%nat ->
  2 ^ (128 * Z.of_nat n - 1) <= Limbs.val x < 2 ^ (128 * Z.of_nat n + 1) ->
  limbs_ok s -> length s = S n -> Limbs.val s < 2 ^ (64 * Z.of_nat (S n)) ->
  Z.sqrt (Limbs.val x) <= Limbs.val s ->
  (Z.to_nat (Limbs.val s - Z.sqrt (Limbs.val x)) < f)%nat ->
  exists s',
  Dyadic.isqrt_loop f n x s false = Some s' /\ limbs_ok s' /\ length s' = S n /\
  Limbs.val s' = Z.sqrt (Limbs.val x).
Proof.
  induction f as [| f IH]; intros n x s Hn Hx Hlx [Hx1 Hx2] Hs Hls Hs2 Hr Hf; [lia |].
  assert (Hn' := Hn). unfold level_ok in Hn'.
  assert (Hrl : 2 ^ (64 * Z.of_nat n - 1) <= Z.sqrt (Limbs.val x)).
  { apply sqrt_lower; [lia |].
    replace (2 * (64 * Z.of_nat n) - 1) with (128 * Z.of_nat n - 1) by lia. exact Hx1. }
  assert (Hx0 : 0 <= Limbs.val x) by (pose proof (val_bounds x Hx); lia).
  assert (Hsb : 2 ^ (64 * Z.of_nat n - 1) <= Limbs.val s < 2 ^ (64 * Z.of_nat (S n)))
    by lia.
  destruct (isqrt_step f n x s false Hn Hx Hlx Hx2 Hs Hls Hsb)
    as (y & Hy & Hly & Hvy & ->).
  cbn [negb andb].
  destruct (Z.ltb_spec (Limbs.val y) (Limbs.val s)) as [Hlt | Hge]; cbn [negb].
  - (* [y < s]: on to the next step, with [r <= y]. *)
    assert (Hp : 0 < 2 ^ (64 * Z.of_nat n - 1)) by (apply Z.pow_pos_nonneg; lia).
    assert (Hry : Z.sqrt (Limbs.val x) <= Limbs.val y)
      by (rewrite Hvy; apply newton_ge; lia).
    apply IH; auto; lia.
  - (* [y >= s]: [s = r], as [s > r] would give [y < s]. *)
    exists s. split; [reflexivity |]. split; [exact Hs |]. split; [exact Hls |].
    destruct (Z.eq_dec (Limbs.val s) (Z.sqrt (Limbs.val x))) as [E | E]; [exact E | exfalso].
    assert (Hlt : (Limbs.val x / Limbs.val s + Limbs.val s) / 2 < Limbs.val s)
      by (apply newton_lt; lia).
    lia.
Qed.

(** ** [isqrt] *)

(** Newton's iteration of [isqrt] ends, at [floor(sqrt(x))], from the seed
    whatever [fsqrt] returns. *)
Lemma isqrt_correct :
  forall n x,
  level_ok n -> limbs_ok x -> length x = (2 * n + 1)%nat ->
  2 ^ (128 * Z.of_nat n - 1) <= Limbs.val x < 2 ^ (128 * Z.of_nat n + 1) ->
  exists s,
  Dyadic.isqrt n x = Some s /\ limbs_ok s /\ length s = S n /\
  Limbs.val s = Z.sqrt (Limbs.val x).
Proof.
  intros n x Hn Hx Hlx [Hx1 Hx2].
  assert (Hn' := Hn). unfold level_ok in Hn'.
  remember (64 * Z.of_nat n) as N eqn:HN.
  assert (E2N : 128 * Z.of_nat n = 2 * N) by lia.
  assert (ESn : 64 * Z.of_nat (S n) = N + 64) by lia.
  assert (Hp : 0 < 2 ^ (2 * N - 1)) by (apply Z.pow_pos_nonneg; lia).
  (* [x] has [2 N] or [2 N + 1] bits. *)
  assert (Hl : nat_bits (Limbs.val x) = 2 * N \/ nat_bits (Limbs.val x) = 2 * N + 1).
  { unfold nat_bits. rewrite E2N in Hx1, Hx2.
    destruct (Z.eqb_spec (Limbs.val x) 0) as [E | _]; [lia |].
    assert (Hx0 : 0 < Limbs.val x) by lia.
    pose proof (proj1 (Z.log2_le_pow2 _ _ Hx0) Hx1) as L1.
    pose proof (proj1 (Z.log2_lt_pow2 _ _ Hx0) Hx2) as L2.
    lia. }
  unfold Dyadic.isqrt.
  rewrite (bit_len_correct x Hx).
  rewrite (checked_u_ok 64 (nat_bits (Limbs.val x) - 63)) by lia.
  cbv beta iota zeta.
  match goal with
  | |- context [Limbs.shl_into (S n) (?c :: nil) ?k] =>
      remember c as c0 eqn:Hc0; remember k as k0 eqn:Hk0
  end.
  assert (Hc : 2 ^ 31 <= c0 < 2 ^ 32) by (rewrite Hc0; apply seed_bounds).
  (* [k = (l - 63) / 2] is [N - 32] for [l = 2 N] and [N - 31] for
     [l = 2 N + 1]. *)
  assert (Hk : k0 = N - 32 \/ k0 = N - 31).
  { rewrite Hk0. destruct Hl as [-> | ->]; Z.div_mod_to_equations; lia. }
  clear Hc0 Hk0.
  (* The seed [s0 = c 2^k] is in [[2^(N - 1), 2^(N + 1))]. *)
  assert (Hk1 : 0 <= k0) by lia.
  assert (Pk : 0 < 2 ^ k0) by (apply Z.pow_pos_nonneg; lia).
  assert (A1 : 2 ^ (N - 1) = 2 ^ (N - 1 - k0) * 2 ^ k0).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (A2 : 2 ^ (N + 1) = 2 ^ (N + 1 - k0) * 2 ^ k0).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (B1 : 2 ^ (N - 1 - k0) <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
  assert (B2 : 2 ^ 32 <= 2 ^ (N + 1 - k0)) by (apply Z.pow_le_mono_r; lia).
  assert (Hcs : 2 ^ (N - 1) <= c0 * 2 ^ k0 < 2 ^ (N + 1)).
  { rewrite A1, A2. split.
    - apply Z.mul_le_mono_nonneg_r; lia.
    - apply Z.mul_lt_mono_pos_r; lia. }
  assert (Hc1 : limbs_ok (c0 :: nil)).
  { apply limbs_ok_cons. split; [lia | constructor]. }
  destruct (shl_into_correct (S n) (c0 :: nil) k0 Hc1 Hk1) as (Hs & Hls & Hvs).
  cbn [Limbs.val] in Hvs. rewrite Z.mul_0_r, Z.add_0_r in Hvs.
  remember (Limbs.shl_into (S n) (c0 :: nil) k0) as s0 eqn:Hs0.
  assert (E6 : 2 ^ (N + 1) <= 2 ^ (N + 64)) by (apply Z.pow_le_mono_r; lia).
  assert (Hvs0 : Limbs.val s0 = c0 * 2 ^ k0).
  { rewrite Hvs, ESn. apply Z.mod_small. lia. }
  (* The first step, to [y >= r] ([newton_ge]) with [y <= x] ([newton_le]),
     as [s0 < 2^(N + 1) <= 2^(2 N - 1) <= x]. *)
  assert (Hsb : 2 ^ (64 * Z.of_nat n - 1) <= Limbs.val s0 < 2 ^ (64 * Z.of_nat (S n)))
    by (rewrite <- HN, ESn; lia).
  replace (Z.to_nat (Limbs.val x) + 2)%nat with (S (Z.to_nat (Limbs.val x) + 1)) by lia.
  destruct (isqrt_step (Z.to_nat (Limbs.val x) + 1) n x s0 true Hn Hx Hlx Hx2 Hs Hls Hsb)
    as (y & Hy & Hly & Hvy & ->).
  cbn [negb andb].
  assert (Hx0 : 0 <= Limbs.val x) by lia.
  assert (Hs0x : Limbs.val s0 <= Limbs.val x).
  { assert (2 ^ (N + 1) <= 2 ^ (2 * N - 1)) by (apply Z.pow_le_mono_r; lia).
    rewrite E2N in Hx1. lia. }
  assert (Hry : Z.sqrt (Limbs.val x) <= Limbs.val y)
    by (rewrite Hvy; apply newton_ge; lia).
  assert (Hyx : Limbs.val y <= Limbs.val x) by (rewrite Hvy; apply newton_le; lia).
  pose proof (val_bounds y Hy) as Hyb. rewrite Hly in Hyb.
  pose proof (Z.sqrt_nonneg (Limbs.val x)) as Hr0.
  apply isqrt_loop_correct; auto; lia.
Qed.
