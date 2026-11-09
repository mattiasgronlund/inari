(** * The integer cube root of the dyadic kernel

    [DyadicRoot.icbrt], Newton's iteration on integers, returns
    [floor(cbrt x)] and whether its cube is below [x], for the [x] of 3
    limbs with [2^159 <= x < 2^162] that [DyadicRoot.cbrt_odd] passes it,
    and its fuel is enough. Only the clamp of the seed to [2^53, 2^54]
    matters, not the [f64] operations before it. A step
    [y = floor((2 s + floor(x / s^2)) / 3)] from any [s > 0] has
    [y >= r = floor(cbrt x)], as [(r - s)^2 (r + 2 s) >= 0] gives
    [3 r s^2 - 2 s^3 <= r^3 <= x], and [y < s] if [s > r] (R. Brent and
    P. Zimmermann, Modern Computer Arithmetic, 1.5.2). *)

From Stdlib Require Import ZArith Lia List.
From Inari Require Import Model Limbs Knuth.

Open Scope Z_scope.

(** ** The integer cube root over [Z] *)

(** Every [x >= 0] has an [r >= 0] with [r^3 <= x < (r + 1)^3]: the
    largest [m < n] with [m^3 <= x], for any [n] with [x < n^3]. *)
Lemma cbrt_exists : forall x, 0 <= x -> exists r, 0 <= r /\ r ^ 3 <= x < (r + 1) ^ 3.
Proof.
  intros x Hx.
  assert (H : forall n : nat, x < Z.of_nat n ^ 3 ->
    exists r, 0 <= r /\ r ^ 3 <= x < (r + 1) ^ 3).
  { induction n as [| n IH]; intros Hn.
    - cbn in Hn. lia.
    - destruct (Z.lt_ge_cases x (Z.of_nat n ^ 3)) as [Hl | Hl]; [exact (IH Hl) |].
      exists (Z.of_nat n). split; [lia |]. split; [exact Hl |].
      rewrite Nat2Z.inj_succ, <- Z.add_1_r in Hn. exact Hn. }
  apply (H (Z.to_nat x + 1)%nat).
  rewrite Nat2Z.inj_add, Z2Nat.id by lia.
  change (Z.of_nat 1) with 1.
  assert (E : (x + 1) ^ 3 = (x + 1) * ((x + 1) * (x + 1))) by ring.
  rewrite E. nia.
Qed.

(** The cube is monotone on [a >= 0]. *)
Lemma cube_le : forall a b, 0 <= a <= b -> a * (a * a) <= b * (b * b).
Proof.
  intros a b H.
  apply Z.mul_le_mono_nonneg; [lia | lia | apply Z.square_nonneg |].
  apply Z.mul_le_mono_nonneg; lia.
Qed.

(** A [y >= r] whose cube is at most [x < (r + 1)^3] is [r]. *)
Lemma cube_root_eq :
  forall x r y,
  0 <= r <= y -> x < (r + 1) * ((r + 1) * (r + 1)) -> y * (y * y) <= x -> y = r.
Proof.
  intros x r y Hr Hx Hy.
  destruct (Z.eq_dec y r) as [E | E]; [exact E | exfalso].
  pose proof (cube_le (r + 1) y ltac:(lia)). lia.
Qed.

(** A [y >= 0] whose cube is above [x >= r^3] is above [r]. *)
Lemma cube_root_lt :
  forall x r y, 0 <= y -> r * (r * r) <= x -> x < y * (y * y) -> r < y.
Proof.
  intros x r y Hy Hr Hx.
  destruct (Z.lt_ge_cases r y) as [H | H]; [exact H | exfalso].
  pose proof (cube_le y r ltac:(lia)). lia.
Qed.

(** ** Newton's step on integers *)

(** From any [s > 0], the step [floor((2 s + floor(x / s^2)) / 3)] is at
    least any [r >= 0] with [r^3 <= x]: if [2 s + x / s^2 <= 3 r - 1], then
    [(x / s^2 + 1) s^2 <= (3 r - 2 s) s^2 = r^3 - (r - s)^2 (r + 2 s) <= r^3
    <= x], against [x < (x / s^2 + 1) s^2]. *)
Lemma newton3_ge :
  forall x s r, 0 <= r -> r ^ 3 <= x -> 0 < s -> r <= (2 * s + x / (s * s)) / 3.
Proof.
  intros x s r Hr Hrx Hs.
  assert (Hss : 0 < s * s) by nia.
  assert (Hm : 0 <= x mod (s * s) < s * s) by (apply Z.mod_pos_bound; lia).
  pose proof (Z.div_mod x (s * s) ltac:(lia)) as Hd.
  remember (x / (s * s)) as q eqn:Eq. remember (x mod (s * s)) as m eqn:Em.
  clear Eq Em.
  assert (E3 : r ^ 3 = r * (r * r)) by ring. rewrite E3 in Hrx.
  destruct (Z.le_gt_cases r ((2 * s + q) / 3)) as [H | H]; [exact H | exfalso].
  assert (Hq : q + 1 <= 3 * r - 2 * s) by (Z.div_mod_to_equations; lia).
  assert (H1 : s * s * (q + 1) <= s * s * (3 * r - 2 * s))
    by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (H2 : 0 <= (r - s) * (r - s) * (r + 2 * s))
    by (apply Z.mul_nonneg_nonneg; [apply Z.square_nonneg | lia]).
  nia.
Qed.

(** Above any [r >= 0] with [x < (r + 1)^3], the step lowers [s]:
    [s >= r + 1] gives [s^3 > x], so [x / s^2 <= s - 1]. *)
Lemma newton3_lt :
  forall x s r, 0 <= r -> x < (r + 1) ^ 3 -> r < s -> (2 * s + x / (s * s)) / 3 < s.
Proof.
  intros x s r Hr Hrx Hs.
  assert (E3 : (r + 1) ^ 3 = (r + 1) * ((r + 1) * (r + 1))) by ring. rewrite E3 in Hrx.
  assert (Hq : x / (s * s) < s).
  { apply Z.div_lt_upper_bound; [nia |].
    assert ((r + 1) * ((r + 1) * (r + 1)) <= s * ((s * s))) by
      (apply Z.mul_le_mono_nonneg; [lia | lia | nia | apply Z.mul_le_mono_nonneg; lia]).
    nia. }
  remember (x / (s * s)) as q eqn:Eq. clear Eq.
  Z.div_mod_to_equations. lia.
Qed.

(** ** One step on limbs *)

(** One step of [icbrt_loop] from [s] with [2^53 <= s <= 2^55]: [s^2] fits
    the 2 limbs of the divisor and its top limb is nonzero; [div_rem] gives
    [q = x / s^2 < 2^162 / 2^106 = 2^56], which is limb 0 of the quotient;
    [2 s + q < 2^57] fits a [u64]; and the step [y < 2^56] has [y^2] in 2
    limbs and [y^3 < 2^168] in the 3 limbs of [cube]. *)
Lemma icbrt_step :
  forall f x s,
  limbs_ok x -> 0 <= Limbs.val x < 2 ^ 162 -> 2 ^ 53 <= s <= 2 ^ 55 ->
  DyadicRoot.icbrt_loop (S f) x s =
  let y := (2 * s + Limbs.val x / (s * s)) / 3 in
  match Z.compare (y * (y * y)) (Limbs.val x) with
  | Gt => DyadicRoot.icbrt_loop f x y
  | Lt => Some (y, true)
  | Eq => Some (y, false)
  end.
Proof.
  intros f x s Hx Hxb Hs.
  assert (Hss : 2 ^ 106 <= s * s <= 2 ^ 110).
  { change (2 ^ 106) with (2 ^ 53 * 2 ^ 53). change (2 ^ 110) with (2 ^ 55 * 2 ^ 55).
    split; apply Z.mul_le_mono_nonneg; lia. }
  (* The divisor [s^2] in 2 limbs. *)
  assert (Hd : limbs_ok (s * s mod 2 ^ 64 :: s * s / 2 ^ 64 :: nil)).
  { apply limbs_ok_cons. split; [apply Z.mod_pos_bound; lia |].
    apply limbs_ok_cons. split; [| constructor].
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (Hvd : Limbs.val (s * s mod 2 ^ 64 :: s * s / 2 ^ 64 :: nil) = s * s).
  { cbn [Limbs.val]. pose proof (Z.div_mod (s * s) (2 ^ 64) ltac:(lia)). lia. }
  assert (Hd0 : Limbs.val (s * s mod 2 ^ 64 :: s * s / 2 ^ 64 :: nil) <> 0) by lia.
  destruct (div_rem_correct x _ Hx Hd Hd0) as (q & rr & Hdr & Hq & _ & _ & _ & Hvq & _).
  rewrite Hvd in Hvq.
  (* [q = x / s^2 < 2^56]. *)
  assert (Hqb : 0 <= Limbs.val q < 2 ^ 56).
  { rewrite Hvq. split; [apply Z.div_pos; lia |].
    apply Z.div_lt_upper_bound; [lia |].
    assert (2 ^ 106 * 2 ^ 56 <= s * s * 2 ^ 56) by (apply Z.mul_le_mono_nonneg_r; lia).
    lia. }
  assert (Hl0 : Limbs.limb q 0 = Limbs.val x / (s * s)).
  { rewrite (limb0_val q Hq), Z.mod_small by lia. exact Hvq. }
  cbn [DyadicRoot.icbrt_loop]. rewrite Hdr. cbv beta iota zeta.
  rewrite Hl0.
  remember (Limbs.val x / (s * s)) as q0 eqn:Hq0.
  rewrite <- Hvq in Hq0. subst q0.
  rewrite (checked_u_ok 64 (2 * s + Limbs.val q)) by lia.
  cbv beta iota zeta.
  (* [y = (2 s + q) / 3 < 2^56], so [y^2 < 2^112] has 2 limbs. *)
  remember ((2 * s + Limbs.val q) / 3) as y eqn:Hy.
  assert (Hyb : 0 <= y < 2 ^ 56) by (rewrite Hy; Z.div_mod_to_equations; lia).
  assert (Hyy : 0 <= y * y < 2 ^ 112).
  { change (2 ^ 112) with (2 ^ 56 * 2 ^ 56). split; [nia |].
    apply Z.mul_lt_mono_nonneg; lia. }
  assert (Hy1 : limbs_ok (y :: nil)).
  { apply limbs_ok_cons. split; [lia | constructor]. }
  assert (Hy2 : limbs_ok (y * y mod 2 ^ 64 :: y * y / 2 ^ 64 :: nil)).
  { apply limbs_ok_cons. split; [apply Z.mod_pos_bound; lia |].
    apply limbs_ok_cons. split; [| constructor].
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (Hvy2 : Limbs.val (y * y mod 2 ^ 64 :: y * y / 2 ^ 64 :: nil) = y * y).
  { cbn [Limbs.val]. pose proof (Z.div_mod (y * y) (2 ^ 64) ltac:(lia)). lia. }
  destruct (mul_into_correct _ _ Hy1 Hy2) as (cube & Hm & Hc & _ & Hvc).
  cbn [length Nat.add] in Hm. rewrite Hm. cbv beta iota zeta.
  rewrite (cmp_correct cube x Hc Hx), Hvc, Hvy2. cbn [Limbs.val].
  rewrite Z.mul_0_r, Z.add_0_r.
  destruct (Z.compare (y * (y * y)) (Limbs.val x)); reflexivity.
Qed.

(** ** The loop *)

(** From [s] with [r < s <= 2^55] for [r = floor(cbrt x)], each step
    lowers [s] ([newton3_lt]) and stays at least [r] ([newton3_ge]); it
    returns once the cube of the step is at most [x], which happens at
    [r] and only there. That takes at most [s - r] steps of fuel. *)
Lemma icbrt_loop_correct :
  forall f x s r,
  limbs_ok x -> 0 <= Limbs.val x < 2 ^ 162 ->
  2 ^ 53 <= r -> r ^ 3 <= Limbs.val x < (r + 1) ^ 3 ->
  r < s <= 2 ^ 55 -> s - r <= Z.of_nat f ->
  exists b, DyadicRoot.icbrt_loop f x s = Some (r, b) /\ (b = true <-> r ^ 3 < Limbs.val x).
Proof.
  induction f as [| f IH]; intros x s r Hx Hxb Hr [Hr1 Hr2] Hs Hf; [lia |].
  rewrite (icbrt_step f x s Hx Hxb ltac:(lia)). cbv zeta.
  remember ((2 * s + Limbs.val x / (s * s)) / 3) as y eqn:Hy.
  assert (Hry : r <= y) by (rewrite Hy; apply newton3_ge; lia).
  assert (Hys : y < s) by (rewrite Hy; apply (newton3_lt _ _ r); lia).
  assert (E3 : forall a, a ^ 3 = a * (a * a)) by (intros; ring).
  rewrite E3 in Hr1, Hr2 |- *.
  destruct (Z.compare_spec (y * (y * y)) (Limbs.val x)) as [He | Hl | Hg].
  - (* [y^3 = x]: [y = r], exact. *)
    assert (Er : y = r) by (apply (cube_root_eq (Limbs.val x)); lia). rewrite Er.
    exists false. split; [reflexivity |]. split; [discriminate | lia].
  - (* [y^3 < x]: [y = r], inexact. *)
    assert (Er : y = r) by (apply (cube_root_eq (Limbs.val x)); lia). rewrite Er.
    exists true. split; [reflexivity |]. split; [lia | reflexivity].
  - (* [y^3 > x]: [y > r], on to the next step. *)
    assert (r < y) by (apply (cube_root_lt (Limbs.val x)); lia).
    rewrite <- !E3 in Hr1, Hr2 |- *.
    apply IH; auto; lia.
Qed.

(** ** [icbrt] *)

(** Newton's iteration of [icbrt] ends, at [floor(cbrt x)], from the seed
    whatever the [f64] operations before its clamp to [2^53, 2^54] return:
    the first step gives [y >= r] with [y < (2^55 + 2^56) / 3 = 2^55], and
    from there [icbrt_loop_correct] needs at most [2^55] of its fuel. *)
Theorem icbrt_correct :
  forall x,
  limbs_ok x -> length x = 3%nat -> 2 ^ 159 <= Limbs.val x < 2 ^ 162 ->
  exists s b, DyadicRoot.icbrt x = Some (s, b) /\
  s ^ 3 <= Limbs.val x < (s + 1) ^ 3 /\ (b = true <-> s ^ 3 < Limbs.val x).
Proof.
  intros x Hx _ [Hx1 Hx2].
  destruct (cbrt_exists (Limbs.val x) ltac:(lia)) as (r & Hr0 & Hr1 & Hr2).
  assert (E3 : forall a, a ^ 3 = a * (a * a)) by (intros; ring).
  (* [2^53 <= r < 2^54], as [(2^53)^3 = 2^159] and [(2^54)^3 = 2^162]. *)
  assert (Hrb : 2 ^ 53 <= r < 2 ^ 54).
  { rewrite E3 in Hr1, Hr2. split.
    - destruct (Z.lt_ge_cases r (2 ^ 53)) as [H | H]; [exfalso | exact H].
      pose proof (cube_le (r + 1) (2 ^ 53) ltac:(lia)). lia.
    - destruct (Z.lt_ge_cases r (2 ^ 54)) as [H | H]; [exact H | exfalso].
      pose proof (cube_le (2 ^ 54) r ltac:(lia)). lia. }
  exists r.
  unfold DyadicRoot.icbrt. cbv zeta.
  match goal with
  | |- context [DyadicRoot.icbrt_loop _ _ (Z.max (2 ^ 53) (Z.min (2 ^ 54) ?u))] =>
      remember (Z.max (2 ^ 53) (Z.min (2 ^ 54) u)) as s0 eqn:Hs0
  end.
  assert (Hs0b : 2 ^ 53 <= s0 <= 2 ^ 54) by lia.
  clear Hs0.
  replace (Z.to_nat (Limbs.val x) + 2)%nat with (S (Z.to_nat (Limbs.val x) + 1)) by lia.
  rewrite (icbrt_step _ x s0 Hx ltac:(lia) ltac:(lia)). cbv zeta.
  remember ((2 * s0 + Limbs.val x / (s0 * s0)) / 3) as y eqn:Hy.
  assert (Hry : r <= y) by (rewrite Hy; apply newton3_ge; lia).
  (* [y < 2^55]: [2 s0 <= 2^55] and [x / s0^2 < 2^162 / 2^106 = 2^56]. *)
  assert (Hy55 : y < 2 ^ 55).
  { assert (Hss : 2 ^ 106 <= s0 * s0).
    { change (2 ^ 106) with (2 ^ 53 * 2 ^ 53). apply Z.mul_le_mono_nonneg; lia. }
    assert (Hq : Limbs.val x / (s0 * s0) < 2 ^ 56).
    { apply Z.div_lt_upper_bound; [lia |].
      assert (2 ^ 106 * 2 ^ 56 <= s0 * s0 * 2 ^ 56) by (apply Z.mul_le_mono_nonneg_r; lia).
      lia. }
    rewrite Hy. apply Z.div_lt_upper_bound; lia. }
  rewrite E3 in Hr1, Hr2.
  destruct (Z.compare_spec (y * (y * y)) (Limbs.val x)) as [He | Hl | Hg].
  - (* [y^3 = x]: [y = r], exact. *)
    assert (Er : y = r) by (apply (cube_root_eq (Limbs.val x)); lia). rewrite Er.
    exists false. split; [reflexivity |]. rewrite !E3. split; [lia |].
    split; [discriminate | lia].
  - (* [y^3 < x]: [y = r], inexact. *)
    assert (Er : y = r) by (apply (cube_root_eq (Limbs.val x)); lia). rewrite Er.
    exists true. split; [reflexivity |]. rewrite !E3. split; [lia |].
    split; [lia | reflexivity].
  - (* [y^3 > x]: [r < y < 2^55], and the loop has fuel for [y - r]. *)
    assert (Hlt : r < y) by (apply (cube_root_lt (Limbs.val x)); lia).
    rewrite <- !E3 in Hr1, Hr2.
    destruct (icbrt_loop_correct (Z.to_nat (Limbs.val x) + 1) x y r Hx ltac:(lia)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (b & Hb & Hbr).
    exists b. split; [exact Hb |]. split; [lia | exact Hbr].
Qed.
