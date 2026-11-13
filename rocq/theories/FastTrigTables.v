(** * The table and constants of the fast paths of [sin], [cos] and [tan]

    The rows of [DyadicTrig.SC] of [Model.v] are sin and cos of i π/4096
    for i in [0, 1024] in double-double, within 2^-104, with each low part
    at most 2^-53 times its high part ([sc_correct]). [INV] is 4096/π
    within a relative 2^-52, and [U1 + U2 + U3] is π/4096 within 2^-119
    ([fast_trig_consts]).

    The bounds are checked by evaluation in the virtual machine, in
    integer fixed point with [P = 160] fractional bits for the rows
    ([SC_ok]) and [P = 200] for the constants ([consts_ok]). π comes from
    [PI_bounds] of [DyConstPi.v], [floor(π 2^4222)], cut to [q] fractional
    bits ([pi_trunc]), so that the angle [b = m π / 2^d] of a row lies
    between [m Pt 2^-P] and [m (Pt + 1) 2^-P] for [q = P - d] and [Pt =
    floor(π 2^q)]. For [0 <= b <= 1], sin is increasing and cos
    decreasing, and the partial sums of their series bracket them
    ([trig_bounds_even] of [TrigSeries.v]): [sin b] lies between the sum
    of [2 j] terms at the lower end and the sum of [2 j + 1] terms at the
    upper end, and [cos b] between the sum of [2 j] terms at the upper end
    and the sum of [2 j + 1] terms at the lower end. The terms [b^n / n!]
    are bounded below and above in fixed point by multiplying by [b] and
    dividing by [n] with the quotients rounded down and up ([terms]).
    With [j = 8], the two sums of sin at one angle differ by its term of
    degree 33, and those of cos by its term of degree 32: below 2^-122 and
    2^-117 for [b <= 1], and below 2^-134 and 2^-128 for the angles of
    [SC], which are at most π/4. For [SC], the ends of the interval of the
    angle are [m 2^-160 <= 2^-150] apart, and the partial sums move by at
    most as much between them, as their derivatives are partial sums of
    cos and sin, at most 1 in absolute value for [b <= 1]. Each bound of a
    term is within 2 2^-160 of the term: the step to degree [n] rounds
    once, by less than 2^-160, and multiplies the error so far by [b / n],
    at most 1/2 from [n = 2] on. So the 33 bounds in the two sums of sin
    or of cos add less than 2^-153, and the bracket is wider than its term
    of degree 33 or 32 by less than 2^-149.

    [rows_okb] and [table_correct] can also take the rows above an index
    [h] as cos and sin of [2 h - i] steps, for a table that goes past π/4.
    [SC] stops at π/4, and [SC_ok] and [sc_correct] take [h = 1024], so no
    row of it is taken that way.

    As in [DyConstPi.v], the 4,222-bit table of π stays behind a variable
    in every lemma that is not proved by that evaluation. *)

From Stdlib Require Import ZArith Reals Lra Lia List Bool.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr TwoSum TrigSeries.
From Inari Require FastExpTables DyConstPi.

Import ListNotations.

Open Scope R_scope.

(** ** Helpers *)

Local Lemma IZR_pow2 : forall e, (0 <= e)%Z -> IZR (2 ^ e) = bpow radix2 e.
Proof. intros e He. rewrite <- IZR_Zpower by exact He. reflexivity. Qed.

(** [x] between [A 2^e] and [B 2^e] is within [K 2^e] of [T 2^e] if [A]
    and [B] are within [K] of [T]. *)
Local Lemma between_close :
  forall (x : R) (A B T K e : Z),
  IZR A * bpow radix2 e <= x <= IZR B * bpow radix2 e ->
  (T - K <= A)%Z -> (B <= T + K)%Z ->
  Rabs (IZR T * bpow radix2 e - x) <= IZR K * bpow radix2 e.
Proof.
intros x A B T K e [H1 H2] HA HB.
apply IZR_le in HA, HB. rewrite minus_IZR in HA. rewrite plus_IZR in HB.
assert (Hb : 0 <= bpow radix2 e) by apply bpow_ge_0.
pose proof (Rmult_le_compat_r _ _ _ Hb HA) as HA'.
pose proof (Rmult_le_compat_r _ _ _ Hb HB) as HB'.
apply Rabs_le. lra.
Qed.

(** [c] between [L 2^e] and [(L + 1) 2^e], times [s 2^f] for [s >= 0] *)
Local Lemma scale_encl :
  forall (c : R) (L s e f : Z), (0 <= s)%Z ->
  IZR L * bpow radix2 e <= c <= IZR (L + 1) * bpow radix2 e ->
  IZR (s * L) * bpow radix2 (e + f) <= IZR s * bpow radix2 f * c <=
  IZR (s * (L + 1)) * bpow radix2 (e + f).
Proof.
intros c L s e f Hs [H1 H2].
assert (Hk : 0 <= IZR s * bpow radix2 f)
  by (apply Rmult_le_pos; [apply IZR_le; exact Hs | apply bpow_ge_0]).
rewrite !mult_IZR, bpow_plus. split.
- replace (IZR s * IZR L * (bpow radix2 e * bpow radix2 f))
    with (IZR s * bpow radix2 f * (IZR L * bpow radix2 e)) by ring.
  apply Rmult_le_compat_l; [exact Hk | exact H1].
- replace (IZR s * IZR (L + 1) * (bpow radix2 e * bpow radix2 f))
    with (IZR s * bpow radix2 f * (IZR (L + 1) * bpow radix2 e)) by ring.
  apply Rmult_le_compat_l; [exact Hk | exact H2].
Qed.

(** π between [Pt 2^-q] and [(Pt + 1) 2^-q] for [Pt = floor(π 2^q)], from
    the 4,222 bits of [DyadicConsts.PI] *)
Lemma pi_trunc :
  forall q, (0 <= q <= 4222)%Z ->
  IZR (Limbs.val DyadicConsts.PI / 2 ^ (4222 - q)) * bpow radix2 (- q) <= PI <=
  IZR (Limbs.val DyadicConsts.PI / 2 ^ (4222 - q) + 1) * bpow radix2 (- q).
Proof.
intros q Hq.
pose proof DyConstPi.PI_bounds as HP. revert HP.
generalize (Limbs.val DyadicConsts.PI). intros V [H1 H2].
assert (Hd : (0 < 2 ^ (4222 - q))%Z) by (apply Z.pow_pos_nonneg; lia).
assert (K : IZR (2 ^ (4222 - q)) * bpow radix2 (-4222) = bpow radix2 (- q))
  by (rewrite IZR_pow2, <- bpow_plus by lia; f_equal; ring).
set (d := (2 ^ (4222 - q))%Z) in *.
set (t := (V / d)%Z).
assert (E1 : (d * t <= V)%Z) by (apply Z.mul_div_le; exact Hd).
assert (E2 : (V + 1 <= d * (t + 1))%Z)
  by (pose proof (Z.mul_succ_div_gt V d Hd); unfold t; lia).
apply IZR_le in E1, E2. rewrite mult_IZR in E1, E2. rewrite (plus_IZR V 1) in E2.
assert (Hb : 0 < bpow radix2 (-4222)) by apply bpow_gt_0.
rewrite <- K. split.
- apply Rle_trans with (IZR V * bpow radix2 (-4222)); [|exact H1].
  replace (IZR t * (IZR d * bpow radix2 (-4222))) with (IZR d * IZR t * bpow radix2 (-4222))
    by ring.
  apply Rmult_le_compat_r; lra.
- apply Rlt_le, Rlt_le_trans with ((IZR V + 1) * bpow radix2 (-4222)); [exact H2|].
  replace (IZR (t + 1) * (IZR d * bpow radix2 (-4222)))
    with (IZR d * IZR (t + 1) * bpow radix2 (-4222)) by ring.
  apply Rmult_le_compat_r; lra.
Qed.

(** ** The terms of the series in fixed point *)

(** [x 2^-P / k] rounded down and up *)
Definition dn (P k x : Z) : Z := (Z.shiftr x P / k)%Z.
Definition up (P k x : Z) : Z := (- (Z.shiftr (- x) P / k))%Z.

Local Lemma dn_le :
  forall P k x, (0 <= P)%Z -> (0 < k)%Z ->
  IZR (dn P k x) * bpow radix2 (- P) * IZR k <= IZR x * bpow radix2 (- P) * bpow radix2 (- P).
Proof.
intros P k x HP Hk.
assert (H2 : (0 < 2 ^ P)%Z) by (apply Z.pow_pos_nonneg; lia).
unfold dn. rewrite Z.shiftr_div_pow2, Z.div_div by lia.
pose proof (Z.mul_div_le x (2 ^ P * k) (Z.mul_pos_pos _ _ H2 Hk)) as H.
set (y := (x / (2 ^ P * k))%Z) in *.
apply IZR_le in H. rewrite !mult_IZR, IZR_pow2 in H by exact HP.
set (w := bpow radix2 (- P)).
assert (Hw : bpow radix2 P * w = 1)
  by (unfold w; rewrite <- bpow_plus, Z.add_opp_diag_r; reflexivity).
assert (Hw0 : 0 < w) by apply bpow_gt_0.
apply Rle_trans with (bpow radix2 P * IZR k * IZR y * (w * w)).
- right. replace (bpow radix2 P * IZR k * IZR y * (w * w))
    with (bpow radix2 P * w * (IZR y * w * IZR k)) by ring.
  rewrite Hw. ring.
- replace (IZR x * w * w) with (IZR x * (w * w)) by ring.
  apply Rmult_le_compat_r; [nra | exact H].
Qed.

Local Lemma up_ge :
  forall P k x, (0 <= P)%Z -> (0 < k)%Z ->
  IZR x * bpow radix2 (- P) * bpow radix2 (- P) <= IZR (up P k x) * bpow radix2 (- P) * IZR k.
Proof.
intros P k x HP Hk.
assert (H2 : (0 < 2 ^ P)%Z) by (apply Z.pow_pos_nonneg; lia).
unfold up. rewrite Z.shiftr_div_pow2, Z.div_div by lia.
pose proof (Z.mul_div_le (- x) (2 ^ P * k) (Z.mul_pos_pos _ _ H2 Hk)) as H.
set (y := (- x / (2 ^ P * k))%Z) in *.
assert (H' : (x <= 2 ^ P * k * - y)%Z) by nia.
apply IZR_le in H'. rewrite !mult_IZR, IZR_pow2 in H' by exact HP.
set (w := bpow radix2 (- P)).
assert (Hw : bpow radix2 P * w = 1)
  by (unfold w; rewrite <- bpow_plus, Z.add_opp_diag_r; reflexivity).
assert (Hw0 : 0 < w) by apply bpow_gt_0.
apply Rle_trans with (bpow radix2 P * IZR k * IZR (- y) * (w * w)).
- replace (IZR x * w * w) with (IZR x * (w * w)) by ring.
  apply Rmult_le_compat_r; [nra | exact H'].
- right. replace (bpow radix2 P * IZR k * IZR (- y) * (w * w))
    with (bpow radix2 P * w * (IZR (- y) * w * IZR k)) by ring.
  rewrite Hw. ring.
Qed.

(** [terms_from P B n lo hi r] lists bounds [(lo', hi')] of [b^n' / n'!]
    for [b = B 2^-P] and [n'] from [n] to [n + r], each step multiplying
    by [b] and dividing by [n' + 1] rounded down for [lo'] and up for
    [hi'], starting from [(lo, hi)] at [n]. *)
Fixpoint terms_from (P B : Z) (n : nat) (lo hi : Z) (r : nat) : list (Z * Z) :=
  match r with
  | O => [(lo, hi)]
  | S r' =>
      (lo, hi) :: terms_from P B (S n) (dn P (Z.of_nat (S n)) (lo * B))
                    (up P (Z.of_nat (S n)) (hi * B)) r'
  end.

Definition terms (P B : Z) (N : nat) : list (Z * Z) := terms_from P B 0 (2 ^ P) (2 ^ P) N.

(** [p] bounds [b^n / n!] in fixed point with [P] fractional bits. *)
Definition tbound (P : Z) (b : R) (n : nat) (p : Z * Z) : Prop :=
  IZR (fst p) * bpow radix2 (- P) <= b ^ n / INR (fact n) <= IZR (snd p) * bpow radix2 (- P).

Local Lemma tstep :
  forall P B n lo hi, (0 <= P)%Z -> (0 <= B)%Z ->
  tbound P (IZR B * bpow radix2 (- P)) n (lo, hi) ->
  tbound P (IZR B * bpow radix2 (- P)) (S n)
    (dn P (Z.of_nat (S n)) (lo * B), up P (Z.of_nat (S n)) (hi * B)).
Proof.
intros P B n lo hi HP HB H. unfold tbound in *. cbn [fst snd] in *.
destruct H as [H1 H2].
assert (Hk : (0 < Z.of_nat (S n))%Z) by lia.
pose proof (dn_le P _ (lo * B) HP Hk) as D. pose proof (up_ge P _ (hi * B) HP Hk) as U.
assert (HK : IZR (Z.of_nat (S n)) = INR (S n)) by (rewrite INR_IZR_INZ; reflexivity).
rewrite HK, mult_IZR in D, U.
set (w := bpow radix2 (- P)) in *.
set (b := IZR B * w) in *.
assert (HK0 : 0 < INR (S n)) by (apply lt_0_INR; lia).
assert (Hb : 0 <= b)
  by (unfold b, w; apply Rmult_le_pos; [apply IZR_le; exact HB | apply bpow_ge_0]).
assert (E : b ^ S n / INR (fact (S n)) = b ^ n / INR (fact n) * b / INR (S n)).
{ rewrite fact_simpl, mult_INR. cbn [pow]. field.
  split; [apply INR_fact_neq_0 | lra]. }
rewrite E. set (c := b ^ n / INR (fact n)) in *.
split.
- apply (Rmult_le_reg_r (INR (S n))); [exact HK0|].
  replace (c * b / INR (S n) * INR (S n)) with (c * b) by (field; lra).
  apply Rle_trans with (IZR lo * IZR B * w * w); [exact D|].
  replace (IZR lo * IZR B * w * w) with (IZR lo * w * b) by (unfold b; ring).
  apply Rmult_le_compat_r; [exact Hb | exact H1].
- apply (Rmult_le_reg_r (INR (S n))); [exact HK0|].
  replace (c * b / INR (S n) * INR (S n)) with (c * b) by (field; lra).
  apply Rle_trans with (IZR hi * IZR B * w * w); [|exact U].
  replace (IZR hi * IZR B * w * w) with (IZR hi * w * b) by (unfold b; ring).
  apply Rmult_le_compat_r; [exact Hb | exact H2].
Qed.

Local Lemma terms_from_correct :
  forall P B r n lo hi k, (0 <= P)%Z -> (0 <= B)%Z ->
  tbound P (IZR B * bpow radix2 (- P)) n (lo, hi) -> (k <= r)%nat ->
  tbound P (IZR B * bpow radix2 (- P)) (n + k) (nth k (terms_from P B n lo hi r) (0, 0)%Z).
Proof.
intros P B r; induction r as [|r IH]; intros n lo hi k HP HB H Hk.
- assert (k = 0)%nat as -> by lia. cbn [terms_from nth]. rewrite Nat.add_0_r. exact H.
- destruct k as [|k]; cbn [terms_from nth].
  + rewrite Nat.add_0_r. exact H.
  + replace (n + S k)%nat with (S n + k)%nat by lia.
    apply IH; [exact HP | exact HB | apply tstep; assumption | lia].
Qed.

Local Lemma terms_correct :
  forall P B N n, (0 <= P)%Z -> (0 <= B)%Z -> (n <= N)%nat ->
  tbound P (IZR B * bpow radix2 (- P)) n (nth n (terms P B N) (0, 0)%Z).
Proof.
intros P B N n HP HB Hn.
assert (H0 : tbound P (IZR B * bpow radix2 (- P)) 0 (2 ^ P, 2 ^ P)%Z).
{ unfold tbound. cbn [fst snd].
  rewrite IZR_pow2, <- bpow_plus, Z.add_opp_diag_r by exact HP.
  replace (_ ^ 0 / INR (fact 0)) with 1 by (cbn; field). cbn [bpow]. lra. }
exact (terms_from_correct P B N 0 _ _ n HP HB H0 Hn).
Qed.

(** ** The partial sums of the series *)

(** Lower and upper bounds of [trig_sum odd k b] from the bounds [t] of
    the terms *)
Fixpoint sum_lo (t : list (Z * Z)) (odd : bool) (k : nat) : Z :=
  match k with
  | O => 0%Z
  | S i =>
      (sum_lo t odd i +
       (if Nat.even i then fst (nth (2 * i + Nat.b2n odd) t (0, 0)%Z)
        else - snd (nth (2 * i + Nat.b2n odd) t (0, 0)%Z)))%Z
  end.

Fixpoint sum_hi (t : list (Z * Z)) (odd : bool) (k : nat) : Z :=
  match k with
  | O => 0%Z
  | S i =>
      (sum_hi t odd i +
       (if Nat.even i then snd (nth (2 * i + Nat.b2n odd) t (0, 0)%Z)
        else - fst (nth (2 * i + Nat.b2n odd) t (0, 0)%Z)))%Z
  end.

Local Lemma m1_pow : forall i, (-1) ^ i = if Nat.even i then 1 else -1.
Proof.
induction i as [|i IH]; [reflexivity|].
cbn [pow]. rewrite IH, Nat.even_succ, <- Nat.negb_even.
destruct (Nat.even i); cbn [negb]; ring.
Qed.

Local Lemma sum_correct :
  forall P (b : R) t odd N k,
  (forall n, (n <= N)%nat -> tbound P b n (nth n t (0, 0)%Z)) -> (2 * k <= S N)%nat ->
  IZR (sum_lo t odd k) * bpow radix2 (- P) <= trig_sum odd k b <=
  IZR (sum_hi t odd k) * bpow radix2 (- P).
Proof.
intros P b t odd N k Ht. induction k as [|i IH]; intros Hk.
- cbn [sum_lo sum_hi trig_sum]. rewrite Rmult_0_l. lra.
- cbn [sum_lo sum_hi]. rewrite trig_sum_S.
  destruct IH as [IH1 IH2]; [lia|].
  assert (Hd : (2 * i + Nat.b2n odd <= N)%nat) by (destruct odd; cbn [Nat.b2n]; lia).
  pose proof (Ht _ Hd) as T. unfold tbound in T.
  set (d := (2 * i + Nat.b2n odd)%nat) in *.
  replace (trig_term odd b i) with ((-1) ^ i * (b ^ d / INR (fact d)))
    by (unfold trig_term, d; unfold Rdiv; ring).
  rewrite m1_pow. set (p := nth d t (0, 0)%Z) in *. set (c := b ^ d / INR (fact d)) in *.
  destruct T as [T1 T2].
  destruct (Nat.even i); cbv beta iota;
    rewrite !plus_IZR, !Rmult_plus_distr_r; [|rewrite !opp_IZR]; lra.
Qed.

(** ** sin and cos between the sums *)

Local Lemma sin_mono : forall x y, 0 <= x <= y -> y <= 1 -> sin x <= sin y.
Proof.
intros x y Hxy Hy. pose proof PI2_1. destruct (Req_dec x y) as [->|Hne]; [lra|].
apply Rlt_le, sin_increasing_1; lra.
Qed.

Local Lemma cos_mono : forall x y, 0 <= x <= y -> y <= 1 -> cos y <= cos x.
Proof.
intros x y Hxy Hy. pose proof PI2_1. destruct (Req_dec x y) as [->|Hne]; [lra|].
apply Rlt_le, cos_decreasing_1; lra.
Qed.

(** [V 2^-P] is within 2^-104 of every number between [lo 2^-P] and [hi
    2^-P]. *)
Definition near_okb (P V lo hi : Z) : bool :=
  (V - 2 ^ (P - 104) <=? lo)%Z && (hi <=? V + 2 ^ (P - 104))%Z.

Local Lemma near_correct :
  forall P V lo hi (y : R), (104 <= P)%Z ->
  IZR lo * bpow radix2 (- P) <= y <= IZR hi * bpow radix2 (- P) ->
  near_okb P V lo hi = true ->
  Rabs (IZR V * bpow radix2 (- P) - y) <= bpow radix2 (-104).
Proof.
intros P V lo hi y HP Hy Hok. unfold near_okb in Hok.
apply andb_true_iff in Hok as [H1 H2]. apply Z.leb_le in H1, H2.
pose proof (between_close y lo hi V _ (- P) Hy H1 H2) as H.
rewrite IZR_pow2, <- bpow_plus in H by lia.
replace (P - 104 + - P)%Z with (-104)%Z in H by ring. exact H.
Qed.

Local Lemma norm_correct :
  forall P H L, (Z.abs L * 2 ^ 53 <= H)%Z ->
  Rabs (IZR L * bpow radix2 (- P)) <= bpow radix2 (-53) * (IZR H * bpow radix2 (- P)).
Proof.
intros P H L Hn.
rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0. rewrite <- abs_IZR.
apply IZR_le in Hn. rewrite mult_IZR, IZR_pow2 in Hn by lia.
assert (K : bpow radix2 53 * bpow radix2 (-53) = 1) by (rewrite <- bpow_plus; reflexivity).
assert (Hw : 0 < bpow radix2 (- P)) by apply bpow_gt_0.
assert (H5 : 0 < bpow radix2 (-53)) by apply bpow_gt_0.
replace (IZR (Z.abs L) * bpow radix2 (- P))
  with (IZR (Z.abs L) * bpow radix2 53 * bpow radix2 (-53) * bpow radix2 (- P))
  by (rewrite (Rmult_assoc (IZR (Z.abs L)) (bpow radix2 53)), K; ring).
replace (bpow radix2 (-53) * (IZR H * bpow radix2 (- P)))
  with (IZR H * bpow radix2 (-53) * bpow radix2 (- P)) by ring.
apply Rmult_le_compat_r; [lra|]. apply Rmult_le_compat_r; [lra | exact Hn].
Qed.

(** ** One row *)

(** The check of the row [(a, b, c, d)] (as bits) for the angle [x]
    between [Bl 2^-P] and [Bh 2^-P]: [a + b] near [sin x] and [c + d]
    near [cos x], or the other way round if [swap], with the sums of [2 j]
    and [2 j + 1] terms. *)
Definition row_okb (P : Z) (j : nat) (swap : bool) (Bl Bh : Z) (row : Z * Z * Z * Z) : bool :=
  let '(a, b, c, d) := row in
  match FastExpTables.fix_of P (from_bits a), FastExpTables.fix_of P (from_bits b),
        FastExpTables.fix_of P (from_bits c), FastExpTables.fix_of P (from_bits d) with
  | Some SH, Some SL, Some CH, Some CL =>
      let tl := terms P Bl (4 * j + 1) in
      let th := terms P Bh (4 * j + 1) in
      let s1 := sum_lo tl true (2 * j) in
      let s2 := sum_hi th true (2 * j + 1) in
      let c1 := sum_lo th false (2 * j) in
      let c2 := sum_hi tl false (2 * j + 1) in
      (0 <=? Bl)%Z && (Bl <=? Bh)%Z && (Bh <=? 2 ^ P)%Z &&
      near_okb P (SH + SL) (if swap then c1 else s1) (if swap then c2 else s2) &&
      near_okb P (CH + CL) (if swap then s1 else c1) (if swap then s2 else c2) &&
      (Z.abs SL * 2 ^ 53 <=? SH)%Z && (Z.abs CL * 2 ^ 53 <=? CH)%Z
  | _, _, _, _ => false
  end.

Local Lemma row_correct :
  forall P j swap Bl Bh a b c d (x : R), (104 <= P)%Z ->
  IZR Bl * bpow radix2 (- P) <= x <= IZR Bh * bpow radix2 (- P) ->
  row_okb P j swap Bl Bh (a, b, c, d) = true ->
  is_finite (from_bits a) = true /\ is_finite (from_bits b) = true /\
  is_finite (from_bits c) = true /\ is_finite (from_bits d) = true /\
  Rabs (B2R (from_bits a) + B2R (from_bits b) - (if swap then cos x else sin x))
    <= bpow radix2 (-104) /\
  Rabs (B2R (from_bits c) + B2R (from_bits d) - (if swap then sin x else cos x))
    <= bpow radix2 (-104) /\
  Rabs (B2R (from_bits b)) <= bpow radix2 (-53) * B2R (from_bits a) /\
  Rabs (B2R (from_bits d)) <= bpow radix2 (-53) * B2R (from_bits c).
Proof.
intros P j swap Bl Bh a b c d x HP Hx Hok.
unfold row_okb in Hok.
destruct (FastExpTables.fix_of P (from_bits a)) as [SH|] eqn:Ea; [|discriminate Hok].
destruct (FastExpTables.fix_of P (from_bits b)) as [SL|] eqn:Eb; [|discriminate Hok].
destruct (FastExpTables.fix_of P (from_bits c)) as [CH|] eqn:Ec; [|discriminate Hok].
destruct (FastExpTables.fix_of P (from_bits d)) as [CL|] eqn:Ed; [|discriminate Hok].
apply FastExpTables.fix_of_correct in Ea as [Fa Ra].
apply FastExpTables.fix_of_correct in Eb as [Fb Rb].
apply FastExpTables.fix_of_correct in Ec as [Fc Rc].
apply FastExpTables.fix_of_correct in Ed as [Fd Rd].
cbv zeta in Hok. repeat rewrite andb_true_iff in Hok.
destruct Hok as [[[[[[H0 H1] H2] Hs] Hc] Ns] Nc].
apply Z.leb_le in H0, H1, H2, Ns, Nc.
assert (HP0 : (0 <= P)%Z) by lia.
set (w := bpow radix2 (- P)) in *.
assert (Hw : 0 < w) by apply bpow_gt_0.
set (bl := IZR Bl * w) in *. set (bh := IZR Bh * w) in *.
assert (Hbl : 0 <= bl) by (unfold bl; apply Rmult_le_pos; [apply IZR_le; exact H0 | lra]).
assert (Hbh : bh <= 1).
{ apply IZR_le in H2. rewrite IZR_pow2 in H2 by exact HP0.
  unfold bh. replace 1 with (bpow radix2 P * w)
    by (unfold w; rewrite <- bpow_plus, Z.add_opp_diag_r; reflexivity).
  apply Rmult_le_compat_r; lra. }
set (N := (4 * j + 1)%nat).
pose proof (terms_correct P Bl N) as Tl. pose proof (terms_correct P Bh N) as Th.
fold w bl in Tl. fold w bh in Th.
assert (Tl' : forall n, (n <= N)%nat -> tbound P bl n (nth n (terms P Bl N) (0, 0)%Z))
  by (intros n Hn; apply Tl; [exact HP0 | exact H0 | exact Hn]).
assert (Th' : forall n, (n <= N)%nat -> tbound P bh n (nth n (terms P Bh N) (0, 0)%Z))
  by (intros n Hn; apply Th; [exact HP0 | lia | exact Hn]).
pose proof (sum_correct P _ _ true N (2 * j) Tl' ltac:(unfold N; lia)) as [S1 _].
pose proof (sum_correct P _ _ true N (2 * j + 1) Th' ltac:(unfold N; lia)) as [_ S2].
pose proof (sum_correct P _ _ false N (2 * j) Th' ltac:(unfold N; lia)) as [C1 _].
pose proof (sum_correct P _ _ false N (2 * j + 1) Tl' ltac:(unfold N; lia)) as [_ C2].
fold w in S1, S2, C1, C2.
pose proof (trig_bounds_even true bl j ltac:(lra)) as [TS1 _].
pose proof (trig_bounds_even true bh j ltac:(lra)) as [_ TS2].
pose proof (trig_bounds_even false bh j ltac:(lra)) as [TC1 _].
pose proof (trig_bounds_even false bl j ltac:(lra)) as [_ TC2].
cbn [trig_fn] in TS1, TS2, TC1, TC2.
pose proof (sin_mono bl x ltac:(lra) ltac:(lra)).
pose proof (sin_mono x bh ltac:(lra) ltac:(lra)).
pose proof (cos_mono bl x ltac:(lra) ltac:(lra)).
pose proof (cos_mono x bh ltac:(lra) ltac:(lra)).
set (s1 := sum_lo (terms P Bl N) true (2 * j)) in *.
set (s2 := sum_hi (terms P Bh N) true (2 * j + 1)) in *.
set (c1 := sum_lo (terms P Bh N) false (2 * j)) in *.
set (c2 := sum_hi (terms P Bl N) false (2 * j + 1)) in *.
assert (HS : IZR s1 * w <= sin x <= IZR s2 * w) by lra.
assert (HC : IZR c1 * w <= cos x <= IZR c2 * w) by lra.
assert (EA : B2R (from_bits a) + B2R (from_bits b) = IZR (SH + SL) * w)
  by (rewrite Ra, Rb, plus_IZR; ring).
assert (EC : B2R (from_bits c) + B2R (from_bits d) = IZR (CH + CL) * w)
  by (rewrite Rc, Rd, plus_IZR; ring).
rewrite EA, EC, Ra, Rb, Rc, Rd.
do 4 (split; [assumption|]).
split; [|split; [|split]].
- destruct swap; eapply near_correct; eassumption.
- destruct swap; eapply near_correct; eassumption.
- apply norm_correct. exact Ns.
- apply norm_correct. exact Nc.
Qed.

(** ** The tables *)

(** The multiple of the step for row [i]: [i], or [2 h - i] above [h] *)
Definition mof (h i : Z) : Z := if (h <? i)%Z then (2 * h - i)%Z else i.

Fixpoint rows_okb (P : Z) (j : nat) (Pt h : Z) (t : list (Z * Z * Z * Z)) (i : Z) : bool :=
  match t with
  | [] => true
  | r :: t =>
      row_okb P j (h <? i)%Z (mof h i * Pt) (mof h i * (Pt + 1)) r &&
      rows_okb P j Pt h t (i + 1)
  end.

Local Lemma rows_okb_nth :
  forall P j Pt h t i0 k, rows_okb P j Pt h t i0 = true -> (k < length t)%nat ->
  let i := (i0 + Z.of_nat k)%Z in
  row_okb P j (h <? i)%Z (mof h i * Pt) (mof h i * (Pt + 1)) (nth k t (0, 0, 0, 0)%Z) = true.
Proof.
intros P j Pt h t; induction t as [|r t IH]; intros i0 k H Hk; [cbn [length] in Hk; lia|].
cbn [rows_okb] in H. apply andb_prop in H as [H1 H2].
destruct k as [|k]; cbn [nth].
- replace (i0 + Z.of_nat 0)%Z with i0 by lia. exact H1.
- replace (i0 + Z.of_nat (S k))%Z with ((i0 + 1) + Z.of_nat k)%Z by lia.
  apply IH; [exact H2 | cbn [length] in Hk; lia].
Qed.

(** A row of a table that passed the check, at the angle [mof h i π / D]
    for [D = 2^dl] and [Pt] such that [Pt 2^(dl - P) <= π <= (Pt + 1)
    2^(dl - P)] *)
Local Lemma table_correct :
  forall t P j dl (D : R) Pt h i, (104 <= P)%Z -> D = bpow radix2 dl ->
  IZR Pt * bpow radix2 (dl - P) <= PI <= IZR (Pt + 1) * bpow radix2 (dl - P) ->
  rows_okb P j Pt h t 0 = true -> (0 <= i)%Z -> (Z.to_nat i < length t)%nat ->
  (0 <= mof h i)%Z ->
  let '(sh, sl, ch, cl) := DyadicTrig.sc t i in
  is_finite sh = true /\ is_finite sl = true /\ is_finite ch = true /\ is_finite cl = true /\
  Rabs (B2R sh + B2R sl -
    (if (h <? i)%Z then cos (IZR (mof h i) * (PI / D)) else sin (IZR (mof h i) * (PI / D))))
    <= bpow radix2 (-104) /\
  Rabs (B2R ch + B2R cl -
    (if (h <? i)%Z then sin (IZR (mof h i) * (PI / D)) else cos (IZR (mof h i) * (PI / D))))
    <= bpow radix2 (-104) /\
  Rabs (B2R sl) <= bpow radix2 (-53) * B2R sh /\
  Rabs (B2R cl) <= bpow radix2 (-53) * B2R ch.
Proof.
intros t P j dl D Pt h i HP HD Hpi Hok Hi Hlen Hm.
pose proof (rows_okb_nth P j Pt h t 0 (Z.to_nat i) Hok Hlen) as R. cbv zeta in R.
rewrite Z.add_0_l, Z2Nat.id in R by exact Hi.
unfold DyadicTrig.sc.
destruct (nth (Z.to_nat i) t (0, 0, 0, 0)%Z) as [[[a b] c] d].
apply (row_correct P j (h <? i)%Z (mof h i * Pt) (mof h i * (Pt + 1)) a b c d
  (IZR (mof h i) * (PI / D)) HP); [|exact R].
pose proof (scale_encl PI Pt (mof h i) (dl - P) (- dl) Hm Hpi) as Hx.
replace (dl - P + - dl)%Z with (- P)%Z in Hx by ring.
replace (IZR (mof h i) * bpow radix2 (- dl) * PI) with (IZR (mof h i) * (PI / D)) in Hx
  by (rewrite HD, bpow_opp; unfold Rdiv; ring).
exact Hx.
Qed.

(** [P = 160] fractional bits and [j = 8]: sums of up to 17 terms, of degree
    up to 33. With [h = 1024], no row is checked as the cos and sin of [2 h
    - i]: every angle of the table is at most π/4 < 1. The kernel evaluates
    the check once, at [Qed] ([vm_cast_no_check], as in [DyConst.v]). *)
Lemma SC_ok :
  rows_okb 160 8 (Limbs.val DyadicConsts.PI / 2 ^ (4222 - 148)) 1024 DyadicTrig.SC 0 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem sc_correct :
  forall i, (0 <= i <= 1024)%Z ->
  let '(sh, sl, ch, cl) := DyadicTrig.sc DyadicTrig.SC i in
  is_finite sh = true /\ is_finite sl = true /\ is_finite ch = true /\ is_finite cl = true /\
  Rabs (B2R sh + B2R sl - sin (IZR i * (PI / 4096))) <= bpow radix2 (-104) /\
  Rabs (B2R ch + B2R cl - cos (IZR i * (PI / 4096))) <= bpow radix2 (-104) /\
  Rabs (B2R sl) <= bpow radix2 (-53) * B2R sh /\
  Rabs (B2R cl) <= bpow radix2 (-53) * B2R ch.
Proof.
intros i Hi.
pose proof (pi_trunc 148 ltac:(lia)) as HP.
pose proof SC_ok as Hok.
set (Pt := (Limbs.val DyadicConsts.PI / 2 ^ (4222 - 148))%Z) in HP, Hok.
clearbody Pt.
change (- (148))%Z with (12 - 160)%Z in HP.
assert (Hlen : length DyadicTrig.SC = 1025%nat) by reflexivity.
assert (Hm : (0 <= mof 1024 i)%Z) by (unfold mof; destruct (Z.ltb_spec 1024 i); lia).
pose proof (table_correct DyadicTrig.SC 160 8 12 4096 Pt 1024 i ltac:(lia) eq_refl HP Hok
  ltac:(lia) ltac:(rewrite Hlen; lia) Hm) as T.
revert T. destruct (DyadicTrig.sc DyadicTrig.SC i) as [[[sh sl] ch] cl].
unfold mof. destruct (Z.ltb_spec 1024 i) as [Hs|Hs]; intros T; [lia|]. exact T.
Qed.

(** ** The constants *)

(** [INV] and [U1 + U2 + U3] with [200] fractional bits, against [π 2^-12]
    between [Pt 2^-200] and [(Pt + 1) 2^-200] *)
Definition consts_okb (Pt : Z) : bool :=
  match FastExpTables.fix_of 200 (from_bits DyadicTrig.INV),
        FastExpTables.fix_of 200 (from_bits DyadicTrig.U1),
        FastExpTables.fix_of 200 (from_bits DyadicTrig.U2),
        FastExpTables.fix_of 200 (from_bits DyadicTrig.U3) with
  | Some Iv, Some Ua, Some Ub, Some Uc =>
      (0 <=? Iv)%Z && (2 ^ 400 - 2 ^ 348 <=? Iv * Pt)%Z &&
      (Iv * (Pt + 1) <=? 2 ^ 400 + 2 ^ 348)%Z &&
      (Ua + Ub + Uc - 2 ^ 81 <=? Pt)%Z && (Pt + 1 <=? Ua + Ub + Uc + 2 ^ 81)%Z
  | _, _, _, _ => false
  end.

Lemma consts_ok : consts_okb (Limbs.val DyadicConsts.PI / 2 ^ (4222 - 188)) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem fast_trig_consts :
  Rabs (B2R (from_bits DyadicTrig.INV) * (PI / 4096) - 1) <= bpow radix2 (-52) /\
  Rabs (PI / 4096 - (B2R (from_bits DyadicTrig.U1) + B2R (from_bits DyadicTrig.U2) +
    B2R (from_bits DyadicTrig.U3))) <= bpow radix2 (-119).
Proof.
pose proof (pi_trunc 188 ltac:(lia)) as HP.
pose proof consts_ok as Hok.
set (Pt := (Limbs.val DyadicConsts.PI / 2 ^ (4222 - 188))%Z) in HP, Hok.
clearbody Pt.
unfold consts_okb in Hok.
destruct (FastExpTables.fix_of 200 (from_bits DyadicTrig.INV)) as [Iv|] eqn:EI;
  [|discriminate Hok].
destruct (FastExpTables.fix_of 200 (from_bits DyadicTrig.U1)) as [Ua|] eqn:EA;
  [|discriminate Hok].
destruct (FastExpTables.fix_of 200 (from_bits DyadicTrig.U2)) as [Ub|] eqn:EB;
  [|discriminate Hok].
destruct (FastExpTables.fix_of 200 (from_bits DyadicTrig.U3)) as [Uc|] eqn:EC;
  [|discriminate Hok].
apply FastExpTables.fix_of_correct in EI as [_ RI].
apply FastExpTables.fix_of_correct in EA as [_ RA].
apply FastExpTables.fix_of_correct in EB as [_ RB].
apply FastExpTables.fix_of_correct in EC as [_ RC].
change (Z.opp 200) with (-200)%Z in RI, RA, RB, RC.
repeat rewrite andb_true_iff in Hok.
destruct Hok as [[[[H0 H1] H2] H3] H4].
apply Z.leb_le in H0, H1, H2, H3, H4.
(* π/4096 between [Pt 2^-200] and [(Pt + 1) 2^-200] *)
pose proof (scale_encl PI Pt 1 (-188) (-12) ltac:(lia) HP) as HQ.
rewrite !Z.mul_1_l in HQ. change (-188 + -12)%Z with (-200)%Z in HQ.
replace (IZR 1 * bpow radix2 (-12) * PI) with (PI / 4096) in HQ
  by (change (bpow radix2 (-12)) with (/ 4096); unfold Rdiv; ring).
split.
- pose proof (scale_encl (PI / 4096) Pt Iv (-200) (-200) H0 HQ) as HX.
  change (-200 + -200)%Z with (-400)%Z in HX.
  pose proof (between_close _ _ _ (2 ^ 400) (2 ^ 348) (-400) HX H1 H2) as C.
  rewrite !IZR_pow2, <- !bpow_plus in C by lia.
  change (400 + -400)%Z with 0%Z in C. change (348 + -400)%Z with (-52)%Z in C.
  change (bpow radix2 0) with 1 in C.
  rewrite RI, Rabs_minus_sym. exact C.
- pose proof (between_close _ _ _ (Ua + Ub + Uc) (2 ^ 81) (-200) HQ H3 H4) as C.
  rewrite IZR_pow2, <- bpow_plus in C by lia.
  change (81 + -200)%Z with (-119)%Z in C.
  rewrite RA, RB, RC, Rabs_minus_sym.
  replace (IZR Ua * bpow radix2 (-200) + IZR Ub * bpow radix2 (-200) +
    IZR Uc * bpow radix2 (-200)) with (IZR (Ua + Ub + Uc) * bpow radix2 (-200))
    by (rewrite !plus_IZR; ring).
  exact C.
Qed.
