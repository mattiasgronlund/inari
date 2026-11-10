(** * The table and constants of the fast path of the logarithms

    [DyadicLog.LOG_TABLE] of [Model.v] gives, for each of the 362
    intervals [[(362 + i) / 512, (363 + i) / 512)] of [m], an [f64] [r]
    and -ln r in double-double [th + tl] within [2^-104], with [r m]
    within [3/2048] of 1 on the interval, or [r = 1] and [th = tl = 0]
    for the two intervals next to 1, one on each side ([ltbl_correct]). Each entry
    is checked by [vm_compute] on integers: -ln r = 2 atanh(s) for the
    rational s = (1 - r)/(1 + r), bounded by the partial sums of
    [AtanhSeries.atanh_sum] and [AtanhSeries.atanh_sum_bounds]; with
    |s| <= 0.172 on this table, 22 terms reach the bound.
    The constants: [LN2H] and [LG2H] have significands of 42 bits
    ([ln2h_exact], [lg2h_exact]), so that [e LN2H] and [e LG2H] are exact
    for [|e| < 2^11]; [LN2H + LN2L] is ln 2 and [LG2] is log10(2) within
    [2^-100]; [C2] and [C10] are 1/ln 2 and 1/ln 10 within [2^-104], from
    the bounds of ln 2 and ln 10 of [DyConst.v].

    The partial sums are computed in integer fixed point with [P = 160]
    fractional bits at [s = a / b]: [u_0 = 2^P a / b], [u_(j+1) = u_j a^2
    / b^2], and the sum of [u_j / (2j + 1)] for [j < 22], once with every
    quotient rounded down ([lg_lo]) and once rounded up ([lg_hi]). As
    [s^2 >= 0], rounding each step down (up) keeps every [u_j] below
    (above) [2^P s^(2j+1)], so the two sums bracket [2^P] times the
    partial sum. The remainder after 22 terms is at most [s^45 / (1 -
    s^2) <= 2 s^45] when [s^2 <= 1/2] (checked for each entry), and [2
    u_22] of the upper sum bounds it. The check of all 362 entries takes
    about 11 s in [vm_compute], and as long again at [Qed]. *)

From Stdlib Require Import ZArith Reals Lra Lia List Bool.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary AtanhSeries DyConst FastExpTables.

Import ListNotations.

Open Scope R_scope.

(** ** Helpers *)

Local Lemma lg_pow2 : forall e, (0 <= e)%Z -> IZR (2 ^ e) = bpow radix2 e.
Proof. intros e He. rewrite <- IZR_Zpower by exact He. reflexivity. Qed.

(** [X 2^p <= Y 2^q], checked on integers at the scale [2^E] *)
Local Lemma lg_cmp :
  forall X Y p q E, (E <= p)%Z -> (E <= q)%Z -> (X * 2 ^ (p - E) <= Y * 2 ^ (q - E))%Z ->
  IZR X * bpow radix2 p <= IZR Y * bpow radix2 q.
Proof.
intros X Y p q E Hp Hq H.
apply IZR_le in H. rewrite !mult_IZR, !lg_pow2 in H by lia.
apply (Rmult_le_compat_r (bpow radix2 E)) in H; [|apply bpow_ge_0].
rewrite !Rmult_assoc, <- !bpow_plus in H.
replace (p - E + E)%Z with p in H by ring. replace (q - E + E)%Z with q in H by ring.
exact H.
Qed.

Local Lemma lg_abs : forall X e, Rabs (IZR X * bpow radix2 e) = IZR (Z.abs X) * bpow radix2 e.
Proof.
intros X e. rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 e)) by apply bpow_ge_0.
rewrite abs_IZR. reflexivity.
Qed.

(** The upper bound of [DyConst.v] as a closed interval *)
Local Lemma lg_closed :
  forall (c : R) (L e : Z),
  IZR L * bpow radix2 e <= c < (IZR L + 1) * bpow radix2 e ->
  IZR L * bpow radix2 e <= c <= IZR (L + 1) * bpow radix2 e.
Proof. intros c L e [H1 H2]. rewrite plus_IZR. lra. Qed.

(** ** The constants *)

Theorem ln2h_exact :
  B2R (from_bits DyadicLog.LN2H) = IZR 3048493539143 * bpow radix2 (-42).
Proof.
assert (H : fix_of 53 (from_bits DyadicLog.LN2H) = Some (3048493539143 * 2 ^ 11)%Z)
  by (vm_compute; reflexivity).
apply fix_of_correct in H as [_ H].
rewrite H, mult_IZR, lg_pow2, Rmult_assoc, <- bpow_plus by lia.
reflexivity.
Qed.

Theorem ln2_split_correct :
  Rabs (B2R (from_bits DyadicLog.LN2H) + B2R (from_bits DyadicLog.LN2L) - ln 2) <=
  bpow radix2 (-100).
Proof.
destruct LN2_bounds as [H1 H2].
apply (dd_close _ _ 97 (Limbs.val DyadicConsts.LN2) (-4224) (-100));
  [vm_compute; reflexivity | split; [exact H1 | apply Rlt_le; exact H2]].
Qed.

Theorem lg2h_exact :
  B2R (from_bits (fst DyadicLog.LG2)) = IZR 2647887844335 * bpow radix2 (-43).
Proof.
assert (H : fix_of 54 (from_bits (fst DyadicLog.LG2)) = Some (2647887844335 * 2 ^ 11)%Z)
  by (vm_compute; reflexivity).
apply fix_of_correct in H as [_ H].
rewrite H, mult_IZR, lg_pow2, Rmult_assoc, <- bpow_plus by lia.
reflexivity.
Qed.

(** [|v - a / b| <= 2^k] for [v = S 2^-P], [a] in [[Alo, Ahi] 2^ea] and
    [b] in [[Blo, Bhi] 2^eb] with [Blo > 0], if [(v - 2^k) Bhi 2^eb <=
    Alo 2^ea] and [Ahi 2^ea <= (v + 2^k) Blo 2^eb], checked on integers
    at the scale [2^E]: then [(v - 2^k) b <= a <= (v + 2^k) b]. *)
Local Definition quot_okb (S P k Alo Ahi ea Blo Bhi eb E : Z) : bool :=
  (0 <=? P + k)%Z && (E <=? eb - P)%Z && (E <=? ea)%Z && (0 <? Blo)%Z &&
  (2 ^ (P + k) <=? S)%Z &&
  ((S - 2 ^ (P + k)) * Bhi * 2 ^ (eb - P - E) <=? Alo * 2 ^ (ea - E))%Z &&
  (Ahi * 2 ^ (ea - E) <=? (S + 2 ^ (P + k)) * Blo * 2 ^ (eb - P - E))%Z.

Local Lemma quot_close :
  forall (v a b : R) (S P k Alo Ahi ea Blo Bhi eb E : Z),
  quot_okb S P k Alo Ahi ea Blo Bhi eb E = true ->
  v = IZR S * bpow radix2 (- P) ->
  IZR Alo * bpow radix2 ea <= a <= IZR Ahi * bpow radix2 ea ->
  IZR Blo * bpow radix2 eb <= b <= IZR Bhi * bpow radix2 eb ->
  Rabs (v - a / b) <= bpow radix2 k.
Proof.
intros v a b S P k Alo Ahi ea Blo Bhi eb E Hok Hv Ha Hb.
unfold quot_okb in Hok. repeat rewrite andb_true_iff in Hok.
destruct Hok as [[[[[[H0 H1] H2] H3] H4] H5] H6].
apply Z.leb_le in H0. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
apply Z.leb_le in H4. apply Z.leb_le in H5. apply Z.leb_le in H6.
set (D := (2 ^ (P + k))%Z) in *.
set (w := bpow radix2 (- P)) in *.
assert (Hw : 0 < w) by apply bpow_gt_0.
assert (HD : IZR D * w = bpow radix2 k).
{ unfold D, w. rewrite lg_pow2, <- bpow_plus by exact H0. f_equal. ring. }
assert (Ebp : bpow radix2 (eb - P - E) * bpow radix2 E = bpow radix2 eb * w).
{ unfold w. rewrite <- !bpow_plus. f_equal. ring. }
assert (Eea : bpow radix2 (ea - E) * bpow radix2 E = bpow radix2 ea).
{ rewrite <- bpow_plus. f_equal. ring. }
assert (HE : 0 <= bpow radix2 E) by apply bpow_ge_0.
apply IZR_le in H5. apply IZR_le in H6. apply IZR_le in H4. apply IZR_lt in H3.
rewrite !mult_IZR, minus_IZR, !lg_pow2 in H5 by lia.
rewrite !mult_IZR, plus_IZR, !lg_pow2 in H6 by lia.
apply (Rmult_le_compat_r _ _ _ HE) in H5. apply (Rmult_le_compat_r _ _ _ HE) in H6.
assert (G5 : (IZR S * w - IZR D * w) * (IZR Bhi * bpow radix2 eb) <= IZR Alo * bpow radix2 ea).
{ replace ((IZR S * w - IZR D * w) * (IZR Bhi * bpow radix2 eb))
    with ((IZR S - IZR D) * IZR Bhi * (bpow radix2 (eb - P - E) * bpow radix2 E))
    by (rewrite Ebp; ring).
  rewrite <- Eea. lra. }
assert (G6 : IZR Ahi * bpow radix2 ea <= (IZR S * w + IZR D * w) * (IZR Blo * bpow radix2 eb)).
{ replace ((IZR S * w + IZR D * w) * (IZR Blo * bpow radix2 eb))
    with ((IZR S + IZR D) * IZR Blo * (bpow radix2 (eb - P - E) * bpow radix2 E))
    by (rewrite Ebp; ring).
  rewrite <- Eea. lra. }
rewrite <- Hv, HD in G5, G6.
assert (Hlo : 0 <= v - bpow radix2 k).
{ rewrite Hv, <- HD. nra. }
assert (HB0 : 0 < IZR Blo * bpow radix2 eb)
  by (apply Rmult_lt_0_compat; [exact H3 | apply bpow_gt_0]).
assert (Hb0 : 0 < b) by lra.
assert (Hk : 0 < bpow radix2 k) by apply bpow_gt_0.
assert (L1 : (v - bpow radix2 k) * b <= a).
{ apply Rle_trans with ((v - bpow radix2 k) * (IZR Bhi * bpow radix2 eb)); [|lra].
  apply Rmult_le_compat_l; lra. }
assert (L2 : a <= (v + bpow radix2 k) * b).
{ apply Rle_trans with ((v + bpow radix2 k) * (IZR Blo * bpow radix2 eb)); [lra|].
  apply Rmult_le_compat_l; lra. }
assert (Q1 : v - bpow radix2 k <= a / b).
{ apply (Rmult_le_reg_r b); [exact Hb0|].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. exact L1. }
assert (Q2 : a / b <= v + bpow radix2 k).
{ apply (Rmult_le_reg_r b); [exact Hb0|].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. exact L2. }
apply Rabs_le. lra.
Qed.

Local Definition dd_quot_okb (hb lb P k Alo Ahi ea Blo Bhi eb E : Z) : bool :=
  match dd_fix P hb lb with Some s => quot_okb s P k Alo Ahi ea Blo Bhi eb E | None => false end.

Local Lemma dd_quot_close :
  forall (a b : R) (hb lb P k Alo Ahi ea Blo Bhi eb E : Z),
  dd_quot_okb hb lb P k Alo Ahi ea Blo Bhi eb E = true ->
  IZR Alo * bpow radix2 ea <= a <= IZR Ahi * bpow radix2 ea ->
  IZR Blo * bpow radix2 eb <= b <= IZR Bhi * bpow radix2 eb ->
  Rabs (B2R (from_bits hb) + B2R (from_bits lb) - a / b) <= bpow radix2 k.
Proof.
intros a b hb lb P k Alo Ahi ea Blo Bhi eb E Hok Ha Hb.
unfold dd_quot_okb, dd_fix in Hok.
destruct (fix_of P (from_bits hb)) as [x|] eqn:Ex; [|discriminate Hok].
destruct (fix_of P (from_bits lb)) as [y|] eqn:Ey; [|discriminate Hok].
apply fix_of_correct in Ex as [_ Rx]. apply fix_of_correct in Ey as [_ Ry].
apply (quot_close _ _ _ _ _ _ _ _ _ _ _ _ _ Hok); [|exact Ha | exact Hb].
rewrite Rx, Ry, plus_IZR. ring.
Qed.

Theorem lg2_split_correct :
  Rabs (B2R (from_bits (fst DyadicLog.LG2)) + B2R (from_bits (snd DyadicLog.LG2)) - ln 2 / ln 10)
  <= bpow radix2 (-100).
Proof.
apply (dd_quot_close _ _ _ _ 100 (-100)
         (Limbs.val DyadicConsts.LN2) (Limbs.val DyadicConsts.LN2 + 1) (-4224)
         (Limbs.val DyadicConsts.LN10) (Limbs.val DyadicConsts.LN10 + 1) (-4222) (-4322)).
- vm_compute. reflexivity.
- apply lg_closed. exact LN2_bounds.
- apply lg_closed. exact LN10_bounds.
Qed.

Theorem c2_correct :
  Rabs (B2R (from_bits (fst DyadicLog.C2)) + B2R (from_bits (snd DyadicLog.C2)) - / ln 2) <=
  bpow radix2 (-104).
Proof.
replace (/ ln 2) with (1 / ln 2) by (unfold Rdiv; ring).
apply (dd_quot_close _ _ _ _ 108 (-104) 1 1 0
         (Limbs.val DyadicConsts.LN2) (Limbs.val DyadicConsts.LN2 + 1) (-4224) (-4332)).
- vm_compute. reflexivity.
- change (bpow radix2 0) with 1. lra.
- apply lg_closed. exact LN2_bounds.
Qed.

Theorem c10_correct :
  Rabs (B2R (from_bits (fst DyadicLog.C10)) + B2R (from_bits (snd DyadicLog.C10)) - / ln 10) <=
  bpow radix2 (-104).
Proof.
replace (/ ln 10) with (1 / ln 10) by (unfold Rdiv; ring).
apply (dd_quot_close _ _ _ _ 109 (-104) 1 1 0
         (Limbs.val DyadicConsts.LN10) (Limbs.val DyadicConsts.LN10 + 1) (-4222) (-4331)).
- vm_compute. reflexivity.
- change (bpow radix2 0) with 1. lra.
- apply lg_closed. exact LN10_bounds.
Qed.

(** ** The partial sums of atanh in integer fixed point *)

(** [x / y] rounded down, or up if [up], for [y > 0] *)
Local Definition lg_div (up : bool) (x y : Z) : Z := if up then (- (- x / y))%Z else (x / y)%Z.

(** [y] is above [x] if [up], below it otherwise *)
Local Definition lg_dir (up : bool) (x y : R) : Prop := if up then x <= y else y <= x.

Local Lemma lg_dir_trans : forall up x y z, lg_dir up x y -> lg_dir up y z -> lg_dir up x z.
Proof. intros [|] x y z; cbn [lg_dir]; lra. Qed.

Local Lemma lg_dir_eq : forall up x y, x = y -> lg_dir up x y.
Proof. intros [|] x y ->; cbn [lg_dir]; lra. Qed.

Local Lemma lg_dir_plus :
  forall up x y x' y', lg_dir up x y -> lg_dir up x' y' -> lg_dir up (x + x') (y + y').
Proof. intros [|] x y x' y'; cbn [lg_dir]; lra. Qed.

Local Lemma lg_dir_mul :
  forall up x y c, 0 <= c -> lg_dir up x y -> lg_dir up (x * c) (y * c).
Proof. intros [|] x y c Hc H; cbn [lg_dir] in H |- *; apply Rmult_le_compat_r; assumption. Qed.

Local Lemma lg_div_dir :
  forall up x y, (0 < y)%Z -> lg_dir up (IZR x / IZR y) (IZR (lg_div up x y)).
Proof.
intros up x y Hy.
assert (HY : 0 < IZR y) by (apply IZR_lt; exact Hy).
destruct up; cbn [lg_dir lg_div]; apply (Rmult_le_reg_r (IZR y)); try exact HY;
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
- pose proof (Z.mul_div_le (- x) y Hy) as H. apply IZR_le in H.
  rewrite mult_IZR, opp_IZR in H. rewrite opp_IZR. lra.
- pose proof (Z.mul_div_le x y Hy) as H. apply IZR_le in H. rewrite mult_IZR in H. lra.
Qed.

(** [(Σ_{j < n} u_j / (2 (i + j) + 1), u_n)] for [u_0 = u] and [u_(j+1) =
    u_j a2 / b2], each quotient rounded down, or up if [up] *)
Local Fixpoint lg_sum (up : bool) (a2 b2 u i : Z) (n : nat) : Z * Z :=
  match n with
  | O => (0%Z, u)
  | S m =>
      let z := lg_sum up a2 b2 (lg_div up (u * a2) b2) (i + 1) m in
      ((lg_div up u (2 * i + 1) + fst z)%Z, snd z)
  end.

Local Lemma lg_sum_dir :
  forall up a2 b2 x P n i0 u, (0 < b2)%Z -> x ^ 2 = IZR a2 / IZR b2 ->
  lg_dir up (bpow radix2 P * x ^ (2 * i0 + 1)) (IZR u) ->
  lg_dir up (bpow radix2 P * as_tsum i0 n x) (IZR (fst (lg_sum up a2 b2 u (Z.of_nat i0) n))) /\
  lg_dir up (bpow radix2 P * x ^ (2 * (i0 + n) + 1))
    (IZR (snd (lg_sum up a2 b2 u (Z.of_nat i0) n))).
Proof.
intros up a2 b2 x P n. induction n as [| m IH]; intros i0 u Hb Hx Hu.
- cbn [lg_sum fst snd as_tsum]. rewrite Nat.add_0_r.
  split; [apply lg_dir_eq; ring | exact Hu].
- cbn [lg_sum fst snd as_tsum].
  (* The next power: [u a2 / b2] is [u x^2] rounded. *)
  assert (Hu' : lg_dir up (bpow radix2 P * x ^ (2 * S i0 + 1))
                  (IZR (lg_div up (u * a2) b2))).
  { apply lg_dir_trans with (IZR (u * a2) / IZR b2); [| apply lg_div_dir; exact Hb].
    apply lg_dir_trans with (IZR u * x ^ 2).
    - replace (bpow radix2 P * x ^ (2 * S i0 + 1))
        with (bpow radix2 P * x ^ (2 * i0 + 1) * x ^ 2)
        by ((replace (2 * S i0 + 1)%nat with (2 * i0 + 1 + 2)%nat by lia);
            rewrite (pow_add x (2 * i0 + 1) 2); ring).
      apply lg_dir_mul; [apply pow2_ge_0 | exact Hu].
    - apply lg_dir_eq. rewrite Hx, mult_IZR. unfold Rdiv. ring. }
  replace (Z.of_nat i0 + 1)%Z with (Z.of_nat (S i0)) by lia.
  destruct (IH (S i0) _ Hb Hx Hu') as [IH1 IH2].
  split.
  + rewrite plus_IZR, Rmult_plus_distr_l. apply lg_dir_plus; [| exact IH1].
    apply lg_dir_trans with (IZR u / IZR (2 * Z.of_nat i0 + 1)); [| apply lg_div_dir; lia].
    replace (bpow radix2 P * (x ^ (2 * i0 + 1) / INR (2 * i0 + 1)))
      with (bpow radix2 P * x ^ (2 * i0 + 1) * / IZR (2 * Z.of_nat i0 + 1)).
    * apply lg_dir_mul; [| exact Hu]. apply Rlt_le, Rinv_0_lt_compat, IZR_lt. lia.
    * rewrite INR_IZR_INZ. replace (Z.of_nat (2 * i0 + 1)) with (2 * Z.of_nat i0 + 1)%Z by lia.
      unfold Rdiv. ring.
  + replace (2 * (i0 + S m) + 1)%nat with (2 * (S i0 + m) + 1)%nat by lia. exact IH2.
Qed.

(** The lower and upper bounds of [2^P atanh(a / b)] *)
Local Definition lg_lo (P : Z) (n : nat) (a b : Z) : Z :=
  fst (lg_sum false (a * a) (b * b) (lg_div false (2 ^ P * a) b) 0 n).

Local Definition lg_hi (P : Z) (n : nat) (a b : Z) : Z :=
  let z := lg_sum true (a * a) (b * b) (lg_div true (2 ^ P * a) b) 0 n in (fst z + 2 * snd z)%Z.

Local Lemma lg_atanh_bounds :
  forall P n a b, (0 <= P)%Z -> (0 <= a)%Z -> (0 < b)%Z -> (2 * (a * a) <= b * b)%Z ->
  IZR (lg_lo P n a b) * bpow radix2 (- P) <= Ratanh (IZR a / IZR b) <=
  IZR (lg_hi P n a b) * bpow radix2 (- P).
Proof.
intros P n a b HP Ha Hb Hab.
set (s := IZR a / IZR b).
assert (HB : 0 < IZR b) by (apply IZR_lt; exact Hb).
assert (HA : 0 <= IZR a) by (apply IZR_le; exact Ha).
assert (Hs0 : 0 <= s).
{ unfold s, Rdiv. apply Rmult_le_pos; [exact HA | apply Rlt_le, Rinv_0_lt_compat; exact HB]. }
assert (Hs2 : s ^ 2 = IZR (a * a) / IZR (b * b)) by (unfold s; rewrite !mult_IZR; field; lra).
assert (Hbb : (0 < b * b)%Z) by nia.
assert (Hs2h : s ^ 2 <= / 2).
{ assert (HBB : 0 < IZR (b * b)) by (apply IZR_lt; exact Hbb).
  rewrite Hs2. apply IZR_le in Hab. rewrite mult_IZR in Hab.
  unfold Rdiv. apply (Rmult_le_reg_r (IZR (b * b))); [exact HBB |].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. lra. }
assert (Hs1 : s < 1).
{ destruct (Rlt_or_le s 1) as [H|H]; [exact H|]. exfalso.
  assert (1 <= s ^ 2) by (cbn [pow]; nra). lra. }
destruct (atanh_sum_bounds n s (conj Hs0 Hs1)) as [R1 R2].
rewrite as_tsum_atanh_sum in R1, R2.
assert (HC : bpow radix2 P * bpow radix2 (- P) = 1).
{ rewrite <- bpow_plus, Z.add_opp_diag_r. reflexivity. }
assert (H0 : forall up, lg_dir up (bpow radix2 P * s ^ (2 * 0 + 1))
                          (IZR (lg_div up (2 ^ P * a) b))).
{ intros up. apply lg_dir_trans with (IZR (2 ^ P * a) / IZR b); [| apply lg_div_dir; exact Hb].
  apply lg_dir_eq. rewrite mult_IZR, lg_pow2 by exact HP. unfold s. cbn [Nat.mul Nat.add pow].
  unfold Rdiv. ring. }
split.
- pose proof (lg_sum_dir false (a * a) (b * b) s P n 0 _ Hbb Hs2 (H0 false)) as [L1 _].
  cbn [lg_dir] in L1. change (Z.of_nat 0) with 0%Z in L1. unfold lg_lo.
  apply (Rmult_le_compat_r (bpow radix2 (- P))) in L1; [| apply bpow_ge_0].
  replace (bpow radix2 P * as_tsum 0 n s * bpow radix2 (- P))
    with (as_tsum 0 n s * (bpow radix2 P * bpow radix2 (- P))) in L1 by ring.
  rewrite HC, Rmult_1_r in L1. lra.
- pose proof (lg_sum_dir true (a * a) (b * b) s P n 0 _ Hbb Hs2 (H0 true)) as [U1 U2].
  cbn [lg_dir] in U1, U2. change (Z.of_nat 0) with 0%Z in U1, U2. rewrite Nat.add_0_l in U2.
  unfold lg_hi. cbv zeta. rewrite plus_IZR, mult_IZR.
  set (t := s ^ (2 * n + 1)) in *.
  assert (Ht : 0 <= t) by (apply pow_le; exact Hs0).
  (* The remainder [t / (1 - s^2)] is at most [2 t] as [s^2 <= 1/2]. *)
  assert (Hi : / (1 - s ^ 2) <= 2).
  { apply (Rmult_le_reg_r (1 - s ^ 2)); [lra|]. rewrite Rinv_l by lra. lra. }
  assert (Hr : Ratanh s <= as_tsum 0 n s + 2 * t).
  { assert (t / (1 - s ^ 2) <= t * 2) by (unfold Rdiv; apply Rmult_le_compat_l; assumption).
    lra. }
  assert (Hr' : bpow radix2 P * Ratanh s <=
                IZR (fst (lg_sum true (a * a) (b * b) (lg_div true (2 ^ P * a) b) 0 n)) +
                2 * IZR (snd (lg_sum true (a * a) (b * b) (lg_div true (2 ^ P * a) b) 0 n))).
  { apply Rle_trans with (bpow radix2 P * (as_tsum 0 n s + 2 * t)).
    - apply Rmult_le_compat_l; [apply bpow_ge_0 | exact Hr].
    - rewrite Rmult_plus_distr_l. lra. }
  apply (Rmult_le_compat_r (bpow radix2 (- P))) in Hr'; [| apply bpow_ge_0].
  replace (bpow radix2 P * Ratanh s * bpow radix2 (- P))
    with (Ratanh s * (bpow radix2 P * bpow radix2 (- P))) in Hr' by ring.
  rewrite HC, Rmult_1_r in Hr'. exact Hr'.
Qed.

(** The check of [V 2^-160] against [2 atanh(a / b)] within [2^-104],
    with 22 terms at [P = 160] *)
Local Definition lg_ser_okb (a b V : Z) : bool :=
  (0 <=? a)%Z && (0 <? b)%Z && (2 * (a * a) <=? b * b)%Z &&
  (V - 2 ^ 56 <=? 2 * lg_lo 160 22 a b)%Z && (2 * lg_hi 160 22 a b <=? V + 2 ^ 56)%Z.

Local Lemma lg_ser_correct :
  forall a b V, lg_ser_okb a b V = true ->
  Rabs (IZR V * bpow radix2 (-160) - 2 * Ratanh (IZR a / IZR b)) <= bpow radix2 (-104).
Proof.
intros a b V Hok. unfold lg_ser_okb in Hok. repeat rewrite andb_true_iff in Hok.
destruct Hok as [[[[H1 H2] H3] H4] H5].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
apply Z.leb_le in H4. apply Z.leb_le in H5.
destruct (lg_atanh_bounds 160 22 a b ltac:(lia) H1 H2 H3) as [Lo Hi].
change (Z.opp 160) with (-160)%Z in Lo. change (Z.opp 160) with (-160)%Z in Hi.
apply IZR_le in H4. apply IZR_le in H5.
rewrite minus_IZR, mult_IZR, lg_pow2 in H4 by lia.
rewrite mult_IZR, plus_IZR, lg_pow2 in H5 by lia.
assert (Hu : 0 < bpow radix2 (-160)) by apply bpow_gt_0.
assert (K : bpow radix2 56 * bpow radix2 (-160) = bpow radix2 (-104))
  by (rewrite <- bpow_plus; reflexivity).
apply (Rmult_le_compat_r (bpow radix2 (-160))) in H4; [| lra].
apply (Rmult_le_compat_r (bpow radix2 (-160))) in H5; [| lra].
apply Rabs_le. split; lra.
Qed.

(** -ln r = 2 atanh((1 - r) / (1 + r)) for [r = R 2^-53], with the sign
    taken out of the quotient *)
Local Lemma lg_ln_correct :
  forall R W, (0 < R)%Z ->
  lg_ser_okb (Z.abs (2 ^ 53 - R)) (2 ^ 53 + R) (if (R <=? 2 ^ 53)%Z then W else - W)%Z = true ->
  Rabs (IZR W * bpow radix2 (-160) + ln (IZR R * bpow radix2 (-53))) <= bpow radix2 (-104).
Proof.
intros R W HR Hok. apply lg_ser_correct in Hok. revert Hok.
assert (HK0 : 0 < IZR (2 ^ 53)) by (apply IZR_lt, Z.pow_pos_nonneg; lia).
assert (HR0 : 0 < IZR R) by (apply IZR_lt; exact HR).
assert (Hb : bpow radix2 (-53) = / IZR (2 ^ 53)).
{ rewrite lg_pow2, <- bpow_opp by lia. reflexivity. }
rewrite Hb.
assert (Hr0 : 0 < IZR R * / IZR (2 ^ 53))
  by (apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; lra]).
destruct (Z.leb_spec R (2 ^ 53)) as [Hle | Hgt]; intros Hok; cbv iota in Hok.
- rewrite Z.abs_eq in Hok by lia. rewrite minus_IZR, plus_IZR in Hok.
  replace (ln (IZR R * / IZR (2 ^ 53)))
    with (- (2 * Ratanh ((IZR (2 ^ 53) - IZR R) / (IZR (2 ^ 53) + IZR R)))).
  { exact Hok. }
  unfold Ratanh.
  replace ((1 + (IZR (2 ^ 53) - IZR R) / (IZR (2 ^ 53) + IZR R)) /
           (1 - (IZR (2 ^ 53) - IZR R) / (IZR (2 ^ 53) + IZR R)))
    with (/ (IZR R * / IZR (2 ^ 53))) by (field; lra).
  rewrite ln_Rinv by exact Hr0. field.
- rewrite Z.abs_neq in Hok by lia.
  rewrite opp_IZR, opp_IZR, minus_IZR, plus_IZR in Hok.
  replace (ln (IZR R * / IZR (2 ^ 53)))
    with (2 * Ratanh (- (IZR (2 ^ 53) - IZR R) / (IZR (2 ^ 53) + IZR R))).
  { replace (IZR W * bpow radix2 (-160) +
             2 * Ratanh (- (IZR (2 ^ 53) - IZR R) / (IZR (2 ^ 53) + IZR R)))
      with (- (- IZR W * bpow radix2 (-160) -
               2 * Ratanh (- (IZR (2 ^ 53) - IZR R) / (IZR (2 ^ 53) + IZR R)))) by ring.
    rewrite Rabs_Ropp. exact Hok. }
  unfold Ratanh.
  replace ((1 + - (IZR (2 ^ 53) - IZR R) / (IZR (2 ^ 53) + IZR R)) /
           (1 - - (IZR (2 ^ 53) - IZR R) / (IZR (2 ^ 53) + IZR R)))
    with (IZR R * / IZR (2 ^ 53)) by (field; lra).
  field.
Qed.

(** ** The table *)

(** [B2R r * (k / 512) - 1] for [r = R 2^-53] *)
Local Lemma lg_ends :
  forall R k, IZR R * bpow radix2 (-53) * (IZR k / 512) - 1 =
  IZR (R * k - 2 ^ 62) * bpow radix2 (-62).
Proof.
intros R k. rewrite minus_IZR, mult_IZR, lg_pow2 by lia.
assert (K1 : bpow radix2 62 * bpow radix2 (-62) = 1) by (rewrite <- bpow_plus; reflexivity).
assert (K2 : bpow radix2 (-62) = bpow radix2 (-53) * / 512).
{ change (/ 512) with (bpow radix2 (-9)). rewrite <- bpow_plus. reflexivity. }
rewrite Rmult_minus_distr_r, K1, K2. unfold Rdiv. ring.
Qed.

(** The check of the entry [i], [(r, th, tl)] as bits: [r] at 53
    fractional bits and [th], [tl] at 160, each test in the form of
    [lg_cmp] or [lg_ser_okb]. *)
Local Definition lg_entry_okb (i : Z) (e : Z * Z * Z) : bool :=
  match fix_of 53 (from_bits (fst (fst e))), fix_of 160 (from_bits (snd (fst e))),
        fix_of 160 (from_bits (snd e)) with
  | Some R, Some H, Some L =>
      (1 * 2 ^ 52 <=? R * 2 ^ 0)%Z && (R * 2 ^ 0 <=? 1 * 2 ^ 54)%Z &&
      lg_ser_okb (Z.abs (2 ^ 53 - R)) (2 ^ 53 + R)
        (if (R <=? 2 ^ 53)%Z then H + L else - (H + L))%Z &&
      (Z.abs L * 2 ^ 53 <=? Z.abs H * 2 ^ 0)%Z &&
      if (i =? 149)%Z || (i =? 150)%Z then (R =? 2 ^ 53)%Z && (H =? 0)%Z && (L =? 0)%Z
      else
        (1 * 2 ^ 151 <=? Z.abs H * 2 ^ 0)%Z && (Z.abs H * 2 ^ 0 <=? 3 * 2 ^ 157)%Z &&
        (Z.abs (R * (362 + i) - 2 ^ 62) * 2 ^ 0 <=? 3 * 2 ^ 51)%Z &&
        (Z.abs (R * (363 + i) - 2 ^ 62) * 2 ^ 0 <=? 3 * 2 ^ 51)%Z
  | _, _, _ => false
  end.

Local Lemma lg_entry_correct :
  forall i rb hb lb, lg_entry_okb i (rb, hb, lb) = true ->
  is_finite (from_bits rb) = true /\ is_finite (from_bits hb) = true /\
  is_finite (from_bits lb) = true /\
  / 2 <= B2R (from_bits rb) <= 2 /\
  Rabs (B2R (from_bits hb) + B2R (from_bits lb) + ln (B2R (from_bits rb))) <=
    bpow radix2 (-104) /\
  Rabs (B2R (from_bits lb)) <= bpow radix2 (-53) * Rabs (B2R (from_bits hb)) /\
  if (i =? 149)%Z || (i =? 150)%Z then
    B2R (from_bits rb) = 1 /\ B2R (from_bits hb) = 0 /\ B2R (from_bits lb) = 0
  else
    bpow radix2 (-9) <= Rabs (B2R (from_bits hb)) <= 3 / 8 /\
    Rabs (B2R (from_bits rb) * (IZR (362 + i) / 512) - 1) <= 3 / 2048 /\
    Rabs (B2R (from_bits rb) * (IZR (363 + i) / 512) - 1) <= 3 / 2048.
Proof.
intros i rb hb lb Hok.
unfold lg_entry_okb in Hok. cbn [fst snd] in Hok.
destruct (fix_of 53 (from_bits rb)) as [R|] eqn:ER; [|discriminate Hok].
destruct (fix_of 160 (from_bits hb)) as [H|] eqn:EH; [|discriminate Hok].
destruct (fix_of 160 (from_bits lb)) as [L|] eqn:EL; [|discriminate Hok].
apply fix_of_correct in ER as [Fr Rr]. apply fix_of_correct in EH as [Fh Rh].
apply fix_of_correct in EL as [Fl Rl].
change (Z.opp 53) with (-53)%Z in Rr. change (Z.opp 160) with (-160)%Z in Rh.
change (Z.opp 160) with (-160)%Z in Rl.
rewrite Rr, Rh, Rl.
repeat rewrite andb_true_iff in Hok.
destruct Hok as [[[[H1 H2] H3] H4] H5].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H4.
assert (HR : (0 < R)%Z).
{ assert (0 < 2 ^ 52)%Z by (apply Z.pow_pos_nonneg; lia). rewrite Z.pow_0_r in H1. lia. }
split; [exact Fr|]. split; [exact Fh|]. split; [exact Fl|].
split; [split|].
{ pose proof (lg_cmp 1 R (-1) (-53) (-53) ltac:(lia) ltac:(lia) H1) as K.
  change (bpow radix2 (-1)) with (/ 2) in K. lra. }
{ pose proof (lg_cmp R 1 (-53) 1 (-53) ltac:(lia) ltac:(lia) H2) as K.
  change (bpow radix2 1) with 2 in K. lra. }
split.
{ pose proof (lg_ln_correct R (H + L) HR H3) as K.
  rewrite plus_IZR, Rmult_plus_distr_r in K. exact K. }
split.
{ rewrite !lg_abs.
  pose proof (lg_cmp (Z.abs L) (Z.abs H) (-160) (-213) (-213) ltac:(lia) ltac:(lia) H4) as K.
  replace (bpow radix2 (-213)) with (bpow radix2 (-53) * bpow radix2 (-160)) in K
    by (rewrite <- bpow_plus; reflexivity).
  lra. }
destruct ((i =? 149)%Z || (i =? 150)%Z).
- repeat rewrite andb_true_iff in H5. destruct H5 as [[E1 E2] E3].
  apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3. subst R H L.
  split; [|split; ring].
  rewrite lg_pow2, <- bpow_plus by lia. reflexivity.
- repeat rewrite andb_true_iff in H5. destruct H5 as [[[E1 E2] E3] E4].
  apply Z.leb_le in E1. apply Z.leb_le in E2. apply Z.leb_le in E3. apply Z.leb_le in E4.
  rewrite lg_abs. split; [split|split].
  + pose proof (lg_cmp 1 (Z.abs H) (-9) (-160) (-160) ltac:(lia) ltac:(lia) E1) as K. lra.
  + pose proof (lg_cmp (Z.abs H) 3 (-160) (-3) (-160) ltac:(lia) ltac:(lia) E2) as K.
    change (bpow radix2 (-3)) with (/ 8) in K. lra.
  + rewrite lg_ends, lg_abs.
    pose proof (lg_cmp _ 3 (-62) (-11) (-62) ltac:(lia) ltac:(lia) E3) as K.
    change (bpow radix2 (-11)) with (/ 2048) in K. lra.
  + rewrite lg_ends, lg_abs.
    pose proof (lg_cmp _ 3 (-62) (-11) (-62) ltac:(lia) ltac:(lia) E4) as K.
    change (bpow radix2 (-11)) with (/ 2048) in K. lra.
Qed.

Local Fixpoint lg_all_okb (t : list (Z * Z * Z)) (i : Z) : bool :=
  match t with
  | [] => true
  | e :: t => lg_entry_okb i e && lg_all_okb t (i + 1)
  end.

Local Lemma lg_all_okb_nth :
  forall t i0 k, lg_all_okb t i0 = true -> (k < length t)%nat ->
  lg_entry_okb (i0 + Z.of_nat k) (nth k t (0, 0, 0)%Z) = true.
Proof.
intros t; induction t as [|p t IH]; intros i0 k H Hk; [cbn [length] in Hk; lia|].
cbn [lg_all_okb] in H. apply andb_prop in H as [H1 H2].
destruct k as [|k]; cbn [nth].
- replace (i0 + Z.of_nat 0)%Z with i0 by lia. exact H1.
- replace (i0 + Z.of_nat (S k))%Z with ((i0 + 1) + Z.of_nat k)%Z by lia.
  apply IH; [exact H2 | cbn [length] in Hk; lia].
Qed.

(** The check of all 362 entries ([vm_compute]) *)
Local Lemma lg_table_ok : lg_all_okb DyadicLog.LOG_TABLE 0 = true.
Proof. vm_compute. reflexivity. Qed.

Local Lemma lg_table_length : length DyadicLog.LOG_TABLE = 362%nat.
Proof. vm_compute. reflexivity. Qed.

(** Each entry: [r] between 1/2 and 2, [th + tl] within [2^-104] of
    -ln r with [|tl| <= 2^-53 |th|], and either [i] is 149 or 150 and
    [r = 1], [th = tl = 0], or [2^-9 <= |th| <= 3/8] and [r m] is within
    [3/2048] of 1 at both ends of the interval of [m], and so on all of
    it. *)
Theorem ltbl_correct :
  forall i, (0 <= i < 362)%Z ->
  let '(r, th, tl) := DyadicLog.ltbl i in
  is_finite r = true /\ is_finite th = true /\ is_finite tl = true /\
  / 2 <= B2R r <= 2 /\
  Rabs (B2R th + B2R tl + ln (B2R r)) <= bpow radix2 (-104) /\
  Rabs (B2R tl) <= bpow radix2 (-53) * Rabs (B2R th) /\
  if (i =? 149)%Z || (i =? 150)%Z then B2R r = 1 /\ B2R th = 0 /\ B2R tl = 0
  else
    bpow radix2 (-9) <= Rabs (B2R th) <= 3 / 8 /\
    Rabs (B2R r * (IZR (362 + i) / 512) - 1) <= 3 / 2048 /\
    Rabs (B2R r * (IZR (363 + i) / 512) - 1) <= 3 / 2048.
Proof.
intros i Hi.
pose proof (lg_all_okb_nth DyadicLog.LOG_TABLE 0 (Z.to_nat i) lg_table_ok
              ltac:(rewrite lg_table_length; lia)) as He.
rewrite Z.add_0_l, Z2Nat.id in He by lia.
unfold DyadicLog.ltbl.
set (p := nth (Z.to_nat i) DyadicLog.LOG_TABLE (0, 0, 0)%Z) in He |- *.
clearbody p. destruct p as [[rb hb] lb].
exact (lg_entry_correct i rb hb lb He).
Qed.
