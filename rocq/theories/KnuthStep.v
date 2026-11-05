(** * One step of Algorithm D of Knuth

    D3-D6 of Algorithm D of Knuth, The Art of Computer Programming, vol. 2,
    3rd ed., 4.3.1, with base [B = 2^64], on a window of [n + 1] limbs:
    the estimate [qhat] of the quotient limb is at most 2 too large once
    the top limb of the divisor is at least [B/2] (Theorem B), so that the
    loop of D3 tests its condition at most 3 times, and the add-back of D6
    happens at most once. [Knuth.v] proves the loop over the windows. *)

From Stdlib Require Import ZArith Lia List.
From Inari Require Import Model Limbs.

Open Scope Z_scope.

(** ** Arithmetic on limbs *)

Lemma pow64_pos : forall k, 0 < 2 ^ (64 * Z.of_nat k).
Proof. intros k. apply Z.pow_pos_nonneg; lia. Qed.

Lemma pow64_S : forall k, 2 ^ (64 * Z.of_nat (S k)) = 2 ^ (64 * Z.of_nat k) * 2 ^ 64.
Proof. intros k. rewrite Nat2Z.inj_succ, <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma pow64_add :
  forall a b, 2 ^ (64 * Z.of_nat (a + b)) = 2 ^ (64 * Z.of_nat a) * 2 ^ (64 * Z.of_nat b).
Proof. intros a b. rewrite Nat2Z.inj_add, <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma checked_u_some : forall w z, 0 <= z < 2 ^ w -> checked_u w z = Some z.
Proof.
intros w z Hz. unfold checked_u.
destruct (Z.leb_spec 0 z), (Z.ltb_spec z (2 ^ w)); cbn; [reflexivity | lia | lia | lia].
Qed.

(** [u128::from(a) << 64 | u128::from(b)] for limbs [a] and [b] *)
Lemma lor_shift64 :
  forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  Z.lor (Z.shiftl a 64 mod 2 ^ 128) b = a * 2 ^ 64 + b.
Proof.
intros a b Ha Hb.
rewrite Z.shiftl_mul_pow2 by lia.
rewrite Z.mod_small by lia.
(* The bits of [b] are below 64, those of [a * 2^64] from 64 up. *)
assert (H0 : Z.land (a * 2 ^ 64) b = 0).
{ apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0, <- Z.shiftl_mul_pow2, Z.shiftl_spec by lia.
  destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
  - rewrite (Z.testbit_neg_r a (i - 64)) by lia. reflexivity.
  - destruct (Z.eq_dec b 0) as [->|Hb0].
    + rewrite Z.bits_0. apply Bool.andb_false_r.
    + assert (Hl : Z.log2 b < i).
      { apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia | lia]. }
      rewrite (Z.bits_above_log2 b i) by lia. apply Bool.andb_false_r. }
now rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor by exact H0.
Qed.

Lemma mod_neg64 : forall a, - 2 ^ 64 <= a < 0 -> a mod 2 ^ 64 = a + 2 ^ 64.
Proof.
intros a Ha. rewrite <- (Z.mod_add a 1) by lia. apply Z.mod_small. lia.
Qed.

Lemma ovf_sub_spec :
  forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  0 <= fst (Limbs.ovf_sub x y) < 2 ^ 64 /\
  fst (Limbs.ovf_sub x y) - 2 ^ 64 * Z.b2z (snd (Limbs.ovf_sub x y)) = x - y.
Proof.
intros x y Hx Hy. unfold Limbs.ovf_sub. cbn [fst snd].
destruct (Z.ltb_spec x y).
- rewrite mod_neg64 by lia. cbn [Z.b2z]. lia.
- rewrite Z.mod_small by lia. cbn [Z.b2z]. lia.
Qed.

(** Two [overflowing_sub]s in a row borrow at most once. *)
Lemma ovf_sub2 :
  forall x y b t1 b1 t2 b2,
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  Limbs.ovf_sub x y = (t1, b1) -> Limbs.ovf_sub t1 (Z.b2z b) = (t2, b2) ->
  0 <= t2 < 2 ^ 64 /\ t2 - 2 ^ 64 * Z.b2z (b1 || b2) = x - y - Z.b2z b.
Proof.
intros x y b t1 b1 t2 b2 Hx Hy E1 E2.
pose proof (ovf_sub_spec x y Hx Hy) as H1. rewrite E1 in H1. cbn [fst snd] in H1.
assert (Hb : 0 <= Z.b2z b < 2 ^ 64) by (destruct b; cbn; lia).
pose proof (ovf_sub_spec t1 (Z.b2z b) (proj1 H1) Hb) as H2.
rewrite E2 in H2. cbn [fst snd] in H2.
(* After the first borrow, [t1 = x - y + 2^64 >= 1], so the second one
   does not borrow. *)
destruct b1, b2, b; cbn [orb Z.b2z] in *; lia.
Qed.

(** ** D3: the estimate [qhat] (Theorems A and B)

    [est W V P top w2 v1 v2] reads a window [W] of [n + 1] limbs and the
    divisor [V] of [n] limbs with [P = B^(n-2)]: [top] holds the top two
    limbs of [W] and [w2] the next one, [v1] and [v2] are the top two
    limbs of [V], and [W < B V]. *)
Definition est (W V P top w2 v1 v2 : Z) : Prop :=
  0 < P /\ 2 ^ 63 <= v1 < 2 ^ 64 /\ 0 <= v2 < 2 ^ 64 /\ 0 <= w2 < 2 ^ 64 /\ 0 <= top /\
  0 <= W /\ 0 < V /\
  (top * 2 ^ 64 + w2) * P <= W < (top * 2 ^ 64 + w2 + 1) * P /\
  (v1 * 2 ^ 64 + v2) * P <= V < (v1 * 2 ^ 64 + v2 + 1) * P /\
  W < 2 ^ 64 * V.

Lemma est_q :
  forall W V P top w2 v1 v2, est W V P top w2 v1 v2 -> 0 <= W / V < 2 ^ 64.
Proof.
intros W V P top w2 v1 v2 (HP & Hv1 & Hv2 & Hw2 & Htop & HW0 & HV0 & HW & HV & HWV).
split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

(** Theorem A: [qhat >= q]. *)
Lemma est_upper :
  forall W V P top w2 v1 v2, est W V P top w2 v1 v2 ->
  W / V <= Z.min (top / v1) (2 ^ 64 - 1).
Proof.
intros W V P top w2 v1 v2 E.
pose proof (est_q W V P top w2 v1 v2 E) as Hq.
destruct E as (HP & Hv1 & Hv2 & Hw2 & Htop & HW0 & HV0 & HW & HV & HWV).
apply Z.min_glb; [|lia].
apply Z.div_le_lower_bound; [lia|].
set (q := W / V) in *.
assert (H0 : V * q <= W) by (apply Z.mul_div_le; lia).
(* [q v1 B P <= q V <= W < (top + 1) B P] *)
assert (H1 : q * ((v1 * 2 ^ 64 + v2) * P) <= q * V) by (apply Z.mul_le_mono_nonneg_l; lia).
assert (H2 : 0 <= q * v2 * P) by (apply Z.mul_nonneg_nonneg; [apply Z.mul_nonneg_nonneg|]; lia).
assert (H3 : 0 <= (2 ^ 64 - w2 - 1) * P) by (apply Z.mul_nonneg_nonneg; lia).
assert (H4 : q * v1 < top + 1).
{ apply (Z.mul_lt_mono_pos_r (2 ^ 64 * P)); lia. }
lia.
Qed.

(** Theorem B: [qhat <= q + 2], as [v1 >= B/2]. *)
Lemma est_lower :
  forall W V P top w2 v1 v2, est W V P top w2 v1 v2 ->
  Z.min (top / v1) (2 ^ 64 - 1) <= W / V + 2.
Proof.
intros W V P top w2 v1 v2 (HP & Hv1 & Hv2 & Hw2 & Htop & HW0 & HV0 & HW & HV & HWV).
set (h := Z.min (top / v1) (2 ^ 64 - 1)).
assert (Hh : h <= top / v1) by apply Z.le_min_l.
assert (HhB : h <= 2 ^ 64 - 1) by apply Z.le_min_r.
assert (Hh0 : 0 <= h) by (apply Z.min_glb; [apply Z.div_pos|]; lia).
assert (Hhv : h * v1 <= top).
{ pose proof (Z.mul_div_le top v1 ltac:(lia)).
  assert (h * v1 <= top / v1 * v1) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
enough (H : V * (h - 2) <= W).
{ pose proof (Z.div_le_lower_bound W V (h - 2) HV0 H). lia. }
destruct (Z.lt_ge_cases h 2) as [Hh2|Hh2].
{ assert (V * (h - 2) <= 0) by (apply Z.mul_nonneg_nonpos; lia). lia. }
(* [(h - 2) V < (h - 2) (v1 + 1) B P <= h v1 B P <= top B P <= W], as
   [h - 2 <= 2 v1]. *)
assert (H1 : V * (h - 2) <= (v1 + 1) * 2 ^ 64 * P * (h - 2)).
{ apply Z.mul_le_mono_nonneg_r; [lia|].
  assert (0 <= (2 ^ 64 - v2 - 1) * P) by (apply Z.mul_nonneg_nonneg; lia). lia. }
assert (H2 : 0 <= (2 * v1 - (h - 2)) * (2 ^ 64 * P)) by (apply Z.mul_nonneg_nonneg; lia).
assert (H3 : 0 <= (top - h * v1) * (2 ^ 64 * P)) by (apply Z.mul_nonneg_nonneg; lia).
assert (H4 : 0 <= w2 * P) by (apply Z.mul_nonneg_nonneg; lia).
lia.
Qed.

(** The test of D3 holds: [qhat > q]. *)
Lemma est_test_true :
  forall W V P top w2 v1 v2, est W V P top w2 v1 v2 ->
  forall h, 0 <= h -> (top - h * v1) * 2 ^ 64 + w2 < h * v2 -> W / V < h.
Proof.
intros W V P top w2 v1 v2 (HP & Hv1 & Hv2 & Hw2 & Htop & HW0 & HV0 & HW & HV & HWV) h Hh Ht.
apply Z.div_lt_upper_bound; [lia|].
(* [W < (top B + w2 + 1) P <= h (v1 B + v2) P <= h V] *)
assert (H1 : (top * 2 ^ 64 + w2 + 1) * P <= h * (v1 * 2 ^ 64 + v2) * P).
{ apply Z.mul_le_mono_nonneg_r; lia. }
assert (H2 : h * ((v1 * 2 ^ 64 + v2) * P) <= h * V) by (apply Z.mul_le_mono_nonneg_l; lia).
lia.
Qed.

(** The test of D3 is not made as [rhat >= B]: [qhat <= q + 1]. *)
Lemma est_rhat_big :
  forall W V P top w2 v1 v2, est W V P top w2 v1 v2 ->
  forall h, 0 <= h < 2 ^ 64 -> 2 ^ 64 <= top - h * v1 -> h - 1 <= W / V.
Proof.
intros W V P top w2 v1 v2 (HP & Hv1 & Hv2 & Hw2 & Htop & HW0 & HV0 & HW & HV & HWV) h Hh Hr.
apply Z.div_le_lower_bound; [lia|].
destruct (Z.eq_dec h 0) as [->|Hh0]; [lia|].
(* [(h - 1) V < (h - 1) (v1 B + v2 + 1) P <= (top B + w2) P <= W] *)
assert (H1 : V * (h - 1) <= (v1 * 2 ^ 64 + v2 + 1) * P * (h - 1)).
{ apply Z.mul_le_mono_nonneg_r; lia. }
assert (H2 : (v2 + 1) * (h - 1) <= 2 ^ 64 * 2 ^ 64) by (apply Z.mul_le_mono_nonneg; lia).
assert (H3 : (v1 * 2 ^ 64 + v2 + 1) * (h - 1) <= top * 2 ^ 64 + w2) by lia.
assert (H4 : (v1 * 2 ^ 64 + v2 + 1) * (h - 1) * P <= (top * 2 ^ 64 + w2) * P).
{ apply Z.mul_le_mono_nonneg_r; lia. }
lia.
Qed.

(** The test of D3 fails: [qhat <= q + 1]. *)
Lemma est_test_false :
  forall W V P top w2 v1 v2, est W V P top w2 v1 v2 ->
  forall h, 0 <= h < 2 ^ 64 -> h * v2 <= (top - h * v1) * 2 ^ 64 + w2 -> h - 1 <= W / V.
Proof.
intros W V P top w2 v1 v2 (HP & Hv1 & Hv2 & Hw2 & Htop & HW0 & HV0 & HW & HV & HWV) h Hh Ht.
apply Z.div_le_lower_bound; [lia|].
destruct (Z.eq_dec h 0) as [->|Hh0]; [lia|].
(* [h (v1 B + v2) <= top B + w2], and [(h - 1) (v1 B + v2 + 1) <= h (v1 B + v2)]
   as [h <= B <= v1 B + v2]. *)
assert (H1 : V * (h - 1) <= (v1 * 2 ^ 64 + v2 + 1) * P * (h - 1)).
{ apply Z.mul_le_mono_nonneg_r; lia. }
assert (H3 : (v1 * 2 ^ 64 + v2 + 1) * (h - 1) <= top * 2 ^ 64 + w2) by lia.
assert (H4 : (v1 * 2 ^ 64 + v2 + 1) * (h - 1) * P <= (top * 2 ^ 64 + w2) * P).
{ apply Z.mul_le_mono_nonneg_r; lia. }
lia.
Qed.

(** The loop of D3 ends with [q <= qhat <= q + 1] once [qhat - q] is
    below its fuel. *)
Lemma qhat_loop :
  forall W V P top w2 v1 v2, est W V P top w2 v1 v2 ->
  forall f h r,
  r = top - h * v1 -> 0 <= r -> W / V <= h < 2 ^ 64 -> h - W / V < Z.of_nat f ->
  exists h',
  Limbs.knuth_qhat f h r v1 v2 w2 = Some h' /\ W / V <= h' <= W / V + 1 /\ h' <= h.
Proof.
intros W V P top w2 v1 v2 E.
pose proof (est_q W V P top w2 v1 v2 E) as Hq.
pose proof E as (HP & Hv1 & Hv2 & Hw2 & Htop & HW0 & HV0 & HW & HV & HWV).
induction f as [|f IH]; intros h r Hr Hr0 Hh Hf.
{ cbn [Z.of_nat] in Hf. lia. }
cbn [Limbs.knuth_qhat].
destruct (Z.ltb_spec r (2 ^ 64)) as [Hrb|Hrb].
- rewrite (checked_u_some 128 (h * v2)) by nia.
  cbn beta iota.
  rewrite lor_shift64 by lia.
  destruct (Z.ltb_spec (r * 2 ^ 64 + w2) (h * v2)) as [Ht|Ht].
  + assert (Hlt : W / V < h).
    { apply (est_test_true W V P top w2 v1 v2 E); [lia|]. subst r. lia. }
    rewrite (checked_u_some 128 (h - 1)) by lia.
    rewrite (checked_u_some 128 (r + v1)) by lia.
    cbn beta iota.
    destruct (IH (h - 1) (r + v1)) as (h' & Hs & Hh' & Hle); [lia | lia | lia | lia |].
    exists h'. split; [exact Hs | lia].
  + exists h. split; [reflexivity|].
    assert (Hge : h - 1 <= W / V).
    { apply (est_test_false W V P top w2 v1 v2 E); [lia|]. subst r. lia. }
    lia.
- exists h. split; [reflexivity|].
  assert (Hge : h - 1 <= W / V).
  { apply (est_rhat_big W V P top w2 v1 v2 E); lia. }
  lia.
Qed.

(** The numbers that D3 reads from a window [w] and the divisor [v]. *)
Lemma est_intro :
  forall W V P a b c v1 v2,
  0 < P -> 0 <= W < P * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 -> 0 <= V < P * 2 ^ 64 * 2 ^ 64 ->
  c = W / P mod 2 ^ 64 -> b = W / (P * 2 ^ 64) mod 2 ^ 64 ->
  a = W / (P * 2 ^ 64 * 2 ^ 64) mod 2 ^ 64 ->
  v2 = V / P mod 2 ^ 64 -> v1 = V / (P * 2 ^ 64) mod 2 ^ 64 ->
  2 ^ 63 <= v1 -> W / 2 ^ 64 < V ->
  est W V P (a * 2 ^ 64 + b) c v1 v2.
Proof.
intros W V P a b c v1 v2 HP HW HV Hc Hb Ha Hv2 Hv1 Hv1' Hlt.
assert (HB : 0 < 2 ^ 64) by lia.
rewrite <- (Z.div_div W (P * 2 ^ 64)), <- (Z.div_div W P) in Ha by lia.
rewrite <- (Z.div_div W P) in Hb by lia.
rewrite <- (Z.div_div V P) in Hv1 by lia.
assert (HX : 0 <= W / P < 2 ^ 64 * 2 ^ 64 * 2 ^ 64).
{ split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
assert (HY : 0 <= V / P < 2 ^ 64 * 2 ^ 64).
{ split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
pose proof (Z.div_mod W P ltac:(lia)) as HWd.
pose proof (Z.mod_pos_bound W P HP) as HWm.
pose proof (Z.div_mod V P ltac:(lia)) as HVd.
pose proof (Z.mod_pos_bound V P HP) as HVm.
remember (W / P) as X eqn:HXe.
remember (V / P) as Y eqn:HYe.
(* The digits of [X = W / P] and [Y = V / P], one [Z.div_mod] each. *)
pose proof (Z.div_mod X (2 ^ 64) ltac:(lia)) as HX0.
pose proof (Z.mod_pos_bound X (2 ^ 64) HB) as HX0m.
assert (HX1 : 0 <= X / 2 ^ 64 < 2 ^ 64 * 2 ^ 64).
{ split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
pose proof (Z.div_mod (X / 2 ^ 64) (2 ^ 64) ltac:(lia)) as HX1d.
pose proof (Z.mod_pos_bound (X / 2 ^ 64) (2 ^ 64) HB) as HX1m.
assert (HX2 : 0 <= X / 2 ^ 64 / 2 ^ 64 < 2 ^ 64).
{ split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
rewrite (Z.mod_small (X / 2 ^ 64 / 2 ^ 64)) in Ha by exact HX2.
pose proof (Z.div_mod Y (2 ^ 64) ltac:(lia)) as HY0.
pose proof (Z.mod_pos_bound Y (2 ^ 64) HB) as HY0m.
assert (HY1 : 0 <= Y / 2 ^ 64 < 2 ^ 64).
{ split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
rewrite (Z.mod_small (Y / 2 ^ 64)) in Hv1 by exact HY1.
remember (X / 2 ^ 64) as X1 eqn:HX1e.
remember (X1 / 2 ^ 64) as X2 eqn:HX2e.
remember (Y / 2 ^ 64) as Y1 eqn:HY1e.
subst a b c v1 v2.
assert (Htop : (X2 * 2 ^ 64 + X1 mod 2 ^ 64) * 2 ^ 64 + X mod 2 ^ 64 = X) by lia.
assert (Hv : Y1 * 2 ^ 64 + Y mod 2 ^ 64 = Y) by lia.
(* [W / B < V] gives [W < B V]. *)
pose proof (Z.div_mod W (2 ^ 64) ltac:(lia)) as HWB.
pose proof (Z.mod_pos_bound W (2 ^ 64) HB) as HWBm.
assert (HPY : 0 < P * Y) by (apply Z.mul_pos_pos; lia).
unfold est. rewrite Htop, Hv.
repeat split; lia.
Qed.

Lemma window_est :
  forall w v n,
  limbs_ok w -> limbs_ok v -> (2 <= n)%nat -> length v = n -> length w = S n ->
  2 ^ 63 <= Limbs.limb v (n - 1) -> Limbs.val (skipn 1 w) < Limbs.val v ->
  est (Limbs.val w) (Limbs.val v) (2 ^ (64 * Z.of_nat (n - 2)))
    (Limbs.limb w n * 2 ^ 64 + Limbs.limb w (n - 1)) (Limbs.limb w (n - 2))
    (Limbs.limb v (n - 1)) (Limbs.limb v (n - 2)).
Proof.
intros w v n Hw Hv Hn Hlv Hlw Hv1 Hlt.
assert (HP1 : 2 ^ (64 * Z.of_nat (n - 1)) = 2 ^ (64 * Z.of_nat (n - 2)) * 2 ^ 64).
{ replace (n - 1)%nat with (S (n - 2)) by lia. apply pow64_S. }
assert (HP2 : 2 ^ (64 * Z.of_nat n) = 2 ^ (64 * Z.of_nat (n - 2)) * 2 ^ 64 * 2 ^ 64).
{ rewrite <- HP1. assert (Hn1 : n = S (n - 1)) by lia. rewrite Hn1 at 1. apply pow64_S. }
apply est_intro.
- apply pow64_pos.
- pose proof (val_bounds w Hw) as H. rewrite Hlw, pow64_S, HP2 in H. exact H.
- pose proof (val_bounds v Hv) as H. rewrite Hlv, HP2 in H. exact H.
- apply limb_val; exact Hw.
- rewrite <- HP1. apply limb_val; exact Hw.
- rewrite <- HP2. apply limb_val; exact Hw.
- apply limb_val; exact Hv.
- rewrite <- HP1. apply limb_val; exact Hv.
- exact Hv1.
- rewrite val_skipn in Hlt by exact Hw. exact Hlt.
Qed.

(** ** D4: [w := w - qhat v]

    [knuth_submul] subtracts [qhat * v + mc] from [w], with the carry [mc]
    of the products and the borrow [b] of the subtractions, and returns
    the last carry and borrow. *)
Lemma submul_correct :
  forall w v qhat mc b,
  limbs_ok w -> limbs_ok v -> length w = length v ->
  0 <= qhat < 2 ^ 64 -> 0 <= mc < 2 ^ 64 ->
  exists r mc' b',
  Limbs.knuth_submul w v qhat mc b = Some (r, mc', b') /\ limbs_ok r /\
  length r = length w /\ 0 <= mc' < 2 ^ 64 /\
  Limbs.val r - Z.b2z b' * 2 ^ (64 * Z.of_nat (length w)) =
  Limbs.val w - qhat * Limbs.val v - mc + mc' * 2 ^ (64 * Z.of_nat (length w)) - Z.b2z b.
Proof.
induction w as [|x w IH]; intros v qhat mc b Hw Hv Hl Hq Hmc.
- destruct v; [|discriminate].
  exists nil, mc, b. cbn [Limbs.knuth_submul Limbs.val length].
  change (2 ^ (64 * Z.of_nat 0)) with 1.
  repeat split; [constructor | lia | lia | lia].
- destruct v as [|y v]; [discriminate|].
  unfold limbs_ok in Hw, Hv.
  apply Forall_cons_iff in Hw as [Hx Hw].
  apply Forall_cons_iff in Hv as [Hy Hv].
  cbn [length] in Hl. injection Hl as Hl.
  cbn [Limbs.knuth_submul].
  (* [qhat * y + mc <= (B - 1)^2 + B - 1 < B^2] *)
  assert (Hp : 0 <= qhat * y + mc <= (2 ^ 64 - 1) * (2 ^ 64 - 1) + (2 ^ 64 - 1)).
  { assert (0 <= qhat * y <= (2 ^ 64 - 1) * (2 ^ 64 - 1)) by (split; [|apply Z.mul_le_mono_nonneg]; nia).
    lia. }
  rewrite (checked_u_some 128 (qhat * y + mc)) by lia.
  cbn beta iota.
  rewrite Z.shiftr_div_pow2 by lia.
  destruct (Limbs.ovf_sub x ((qhat * y + mc) mod 2 ^ 64)) as [t1 b1] eqn:E1.
  destruct (Limbs.ovf_sub t1 (Z.b2z b)) as [t2 b2] eqn:E2.
  cbn beta iota.
  assert (Hpm : 0 <= (qhat * y + mc) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  destruct (ovf_sub2 x _ b t1 b1 t2 b2 Hx Hpm E1 E2) as (Ht2 & Ht2e).
  assert (Hc : 0 <= (qhat * y + mc) / 2 ^ 64 < 2 ^ 64).
  { split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
  destruct (IH v qhat ((qhat * y + mc) / 2 ^ 64) (b1 || b2) Hw Hv Hl Hq Hc)
    as (r & mc' & b' & Hs & Hr & Hlr & Hmc' & He).
  rewrite Hs. cbv beta iota.
  exists (t2 :: r), mc', b'.
  split; [reflexivity|].
  split; [constructor; assumption|].
  split; [cbn [length]; lia|].
  split; [exact Hmc'|].
  cbn [Limbs.val length]. rewrite pow64_S.
  pose proof (Z.div_mod (qhat * y + mc) (2 ^ 64) ltac:(lia)) as Hpd.
  (* [p = B (p / B) + p mod B]: the carry [p / B] of this limb goes into
     the next one with weight [B]. *)
  remember (Limbs.val r) as R. remember (Limbs.val w) as Wv. remember (Limbs.val v) as Vv.
  remember (2 ^ (64 * Z.of_nat (length w))) as Pw.
  remember (qhat * y + mc) as p.
  remember (p / 2 ^ 64) as pc. remember (p mod 2 ^ 64) as pm.
  remember (Z.b2z (b1 || b2)) as bb. remember (Z.b2z b') as bb'.
  lia.
Qed.

(** ** D3-D6 *)

(** D3-D6 on a window [w] of [n + 1] limbs with [w[1..] < v]. *)
Lemma knuth_step_correct :
  forall w v,
  limbs_ok w -> limbs_ok v -> (2 <= length v)%nat -> length w = S (length v) ->
  2 ^ 63 <= Limbs.limb v (length v - 1) ->
  Limbs.val (skipn 1 w) < Limbs.val v ->
  exists q w',
  Limbs.knuth_step w v = Some (q, w') /\ limbs_ok w' /\ length w' = length w /\
  q = Limbs.val w / Limbs.val v /\ Limbs.val w' = Limbs.val w mod Limbs.val v.
Proof.
intros w v Hw Hv Hn Hlw Hv1 Hlt.
remember (length v) as n eqn:Hlv.
pose proof (window_est w v n Hw Hv Hn (eq_sym Hlv) Hlw Hv1 Hlt) as E.
pose proof (est_q _ _ _ _ _ _ _ E) as Hq.
pose proof (est_upper _ _ _ _ _ _ _ E) as HA.
pose proof (est_lower _ _ _ _ _ _ _ E) as HB.
pose proof (limb_bound w n Hw) as Hwn.
pose proof (limb_bound w (n - 1) Hw) as Hwn1.
unfold Limbs.knuth_step. cbv zeta. rewrite <- Hlv.
rewrite lor_shift64 by assumption.
set (top := Limbs.limb w n * 2 ^ 64 + Limbs.limb w (n - 1)) in *.
set (v1 := Limbs.limb v (n - 1)) in *.
unfold div_u.
destruct (Z.eqb_spec v1 0) as [H0|_]; [lia|].
cbv beta iota.
set (h0 := Z.min (top / v1) (2 ^ 64 - 1)) in *.
assert (Hh0 : 0 <= h0 <= 2 ^ 64 - 1).
{ split; [apply Z.min_glb; [apply Z.div_pos|]; lia | apply Z.le_min_r]. }
assert (Hh0v : h0 * v1 <= top).
{ pose proof (Z.mul_div_le top v1 ltac:(lia)).
  assert (h0 * v1 <= top / v1 * v1) by (apply Z.mul_le_mono_nonneg_r; [lia | apply Z.le_min_l]).
  lia. }
rewrite (checked_u_some 128 (h0 * v1)) by nia.
rewrite (checked_u_some 128 (top - h0 * v1)) by lia.
cbv beta iota.
destruct (qhat_loop _ _ _ _ _ _ _ E 3 h0 (top - h0 * v1)) as (h & Hs & Hh & Hhh0);
  [reflexivity | lia | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia |].
rewrite Hs. cbv beta iota.
(* D4: [lo - b B^n = w[..n] - h v + mc B^n]. *)
assert (Hfw : limbs_ok (firstn n w)) by (apply limbs_ok_firstn; exact Hw).
assert (Hfl : length (firstn n w) = n) by (rewrite length_firstn; lia).
assert (Hfv : length (firstn n w) = length v) by lia.
assert (Hh64 : 0 <= h < 2 ^ 64) by lia.
assert (Hmc0 : 0 <= 0 < 2 ^ 64) by lia.
destruct (submul_correct (firstn n w) v h 0 false Hfw Hv Hfv Hh64 Hmc0)
  as (lo & mc & b & Hs4 & Hlo & Hlol & Hmc & He4).
rewrite Hs4. cbv beta iota.
rewrite Hfl in He4, Hlol. cbn [Z.b2z] in He4.
(* The top limb: [t2 - B bb = w[n] - mc - b]. *)
rewrite (Z.mod_small mc) by exact Hmc.
destruct (Limbs.ovf_sub (Limbs.limb w n) mc) as [t1 b1] eqn:E1.
destruct (Limbs.ovf_sub t1 (Z.b2z b)) as [t2 b2] eqn:E2.
cbv beta iota.
destruct (ovf_sub2 (Limbs.limb w n) mc b t1 b1 t2 b2 Hwn Hmc E1 E2) as (Ht2 & Ht2e).
(* [w = w[..n] + B^n w[n]] *)
assert (Hvw : Limbs.val w = Limbs.val (firstn n w) + 2 ^ (64 * Z.of_nat n) * Limbs.limb w n).
{ assert (Hne : w <> nil) by (intros ->; cbn [length] in Hlw; discriminate).
  rewrite (val_last w Hne), Hlw. replace (S n - 1)%nat with n by lia. reflexivity. }
pose proof (val_bounds v Hv) as HVb. rewrite <- Hlv in HVb.
pose proof (val_bounds lo Hlo) as Hlob. rewrite Hlol in Hlob.
pose proof E as (_ & _ & _ & _ & _ & HW0 & HV0 & _).
assert (HV0' : Limbs.val v <> 0) by lia.
pose proof (Z.div_mod (Limbs.val w) (Limbs.val v) HV0') as HWd.
assert (HV0'' : 0 < Limbs.val v) by lia.
pose proof (Z.mod_pos_bound (Limbs.val w) (Limbs.val v) HV0'') as HWm.
remember (2 ^ (64 * Z.of_nat n)) as Pn eqn:HPn.
assert (HPn0 : 0 < Pn) by (subst Pn; apply pow64_pos).
(* After D4, [lo + B^n t2 = w - h v + B^(n+1) bb]. *)
assert (Htot : Limbs.val lo + Pn * t2 - Pn * 2 ^ 64 * Z.b2z (b1 || b2) =
               Limbs.val w - h * Limbs.val v).
{ assert (Hm : Pn * (t2 - 2 ^ 64 * Z.b2z (b1 || b2)) =
               Pn * (Limbs.limb w n - mc - Z.b2z b)) by (rewrite Ht2e; reflexivity).
  lia. }
remember (Limbs.val w) as W eqn:HW. remember (Limbs.val v) as V eqn:HV.
remember (W / V) as q eqn:Hqe.
destruct (b1 || b2) eqn:Ebb; cbn [Z.b2z] in Htot.
- (* D5 borrows: [h = q + 1], as [h = q] leaves [lo + B^n t2 >= B^(n+1)]. *)
  assert (Hhq : h = q + 1).
  { destruct (Z.eq_dec h (q + 1)) as [|Hne]; [assumption|].
    assert (Hq' : h = q) by lia. rewrite Hq' in Htot.
    assert (Pn * t2 <= Pn * (2 ^ 64 - 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
    lia. }
  rewrite (checked_u_some 128 (h - 1)) by lia.
  cbv beta iota.
  (* D6: [lo' + c B^n = lo + v], and the top limb [t2 + c] carries out. *)
  assert (Hlen : (length v <= length lo)%nat) by lia.
  destruct (Limbs.add_assign lo v) as [lo' c] eqn:E3.
  destruct (add_assign_correct lo v lo' c Hlo Hv Hlen E3) as (Hlo' & Hlo'l & He6).
  rewrite Hlol, <- HPn, <- HV in He6.
  pose proof (val_bounds lo' Hlo') as Hlo'b. rewrite Hlo'l, Hlol, <- HPn in Hlo'b.
  pose proof (b2z_bounds c) as Hc.
  rewrite Hhq in Htot.
  assert (Hcarry : t2 + Z.b2z c = 2 ^ 64).
  { destruct (Z.lt_trichotomy (t2 + Z.b2z c) (2 ^ 64)) as [Hlt'|[Heq|Hgt]];
      [| exact Heq |].
    - assert (Pn * (t2 + Z.b2z c) <= Pn * (2 ^ 64 - 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
      lia.
    - assert (Pn * (2 ^ 64 + 1) <= Pn * (t2 + Z.b2z c)) by (apply Z.mul_le_mono_nonneg_l; lia).
      lia. }
  exists ((h - 1) mod 2 ^ 64), (lo' ++ (t2 + Z.b2z c) mod 2 ^ 64 :: nil).
  split; [reflexivity|].
  split.
  { apply limbs_ok_app; [exact Hlo'|].
    apply limbs_ok_cons. split; [apply Z.mod_pos_bound; lia | constructor]. }
  split; [rewrite length_app, Hlo'l, Hlol, Hlw; cbn [length]; lia|].
  split; [rewrite Z.mod_small; lia|].
  rewrite Hcarry, Z_mod_same_full, val_app, Hlo'l, Hlol, <- HPn. cbn [Limbs.val].
  assert (Pn * (t2 + Z.b2z c) = Pn * 2 ^ 64) by (rewrite Hcarry; reflexivity).
  lia.
- (* D5 does not borrow: [h = q], as [h = q + 1] makes [lo + B^n t2 < 0]. *)
  assert (Hhq : h = q).
  { destruct (Z.eq_dec h q) as [|Hne]; [assumption|].
    assert (Hq' : h = q + 1) by lia. rewrite Hq' in Htot.
    assert (0 <= Pn * t2) by (apply Z.mul_nonneg_nonneg; lia).
    lia. }
  exists (h mod 2 ^ 64), (lo ++ t2 :: nil).
  split; [reflexivity|].
  split.
  { apply limbs_ok_app; [exact Hlo|].
    apply limbs_ok_cons. split; [exact Ht2 | constructor]. }
  split; [rewrite length_app, Hlol, Hlw; cbn [length]; lia|].
  split; [rewrite Z.mod_small; lia|].
  rewrite val_app, Hlol, <- HPn. cbn [Limbs.val].
  rewrite Hhq in Htot.
  lia.
Qed.
