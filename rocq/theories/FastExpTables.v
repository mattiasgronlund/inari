(** * The tables and constants of the fast path of [exp]

    [DyadicExp.T1] and [DyadicExp.T2] of [Model.v] hold 2^(i/4096) and
    2^(j/64) for [i, j] in [0, 63] in double-double, within 2^-104
    ([t1_correct], [t2_correct]), and the constants of
    [DyadicExp.fast_exp] are within the bounds that its proof uses. The
    bounds are checked by [vm_compute] against the enclosures of ln 2 and
    ln 10 of [DyConst.v] and, for the tables, against powers of 2 by
    squarings of lower and upper bounds.

    A table entry [v = h + l] is within [d = 2^-104] of [2^(i/N)], with
    [N = 2^n], if [(v - d)^N <= 2^i <= (v + d)^N], as [t -> t^N] is
    increasing on [t >= 0] and [(2^(i/N))^N = 2^i]. The exact [N]-th
    powers of these 107-bit numbers have about [107 N] bits, so the check
    squares fixed-point numbers with [P = 256] fractional bits [n] times
    instead, rounding up for [v - d] and down for [v + d] ([sq_up],
    [sq_dn]): the rounding errors, relative [2^-256] at each squaring and
    at most [2 N] times that in all, are far below the margin that the
    entries leave (their errors are below 2^-105). *)

From Stdlib Require Import ZArith Reals Lra Lia List Bool.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary DyConst.

Import ListNotations.

Open Scope R_scope.

(** ** Helpers *)

Local Lemma IZR_pow2 : forall e, (0 <= e)%Z -> IZR (2 ^ e) = bpow radix2 e.
Proof. intros e He. rewrite <- IZR_Zpower by exact He. reflexivity. Qed.

(** [2^a] with [P] fractional bits is [2^(a - P)]. *)
Local Lemma pow2_scale :
  forall a P, (0 <= a)%Z -> IZR (2 ^ a) * bpow radix2 (- P) = bpow radix2 (a - P).
Proof.
intros a P Ha. rewrite IZR_pow2, <- bpow_plus by exact Ha. reflexivity.
Qed.

(** The value of a finite [x] as an integer with [P] fractional bits, if
    [x] is a multiple of [2^-P]. *)
Definition fix_of (P : Z) (x : f64) : option Z :=
  match x with
  | B754_zero _ => Some 0%Z
  | B754_finite s m e _ =>
      if (- P <=? e)%Z then Some (cond_Zopp s (Zpos m) * Zpower radix2 (e + P))%Z else None
  | _ => None
  end.

Lemma fix_of_correct :
  forall P x n, fix_of P x = Some n ->
  is_finite x = true /\ B2R x = IZR n * bpow radix2 (- P).
Proof.
intros P [s|s| |s m e Hb] n H; cbn [fix_of] in H; try discriminate H.
- injection H as <-. split; [reflexivity | cbn [B2R]; ring].
- destruct (- P <=? e)%Z eqn:He; [|discriminate H]. apply Z.leb_le in He.
  injection H as <-. split; [reflexivity|].
  cbn [B2R]. unfold F2R. cbn [Fnum Fexp].
  rewrite mult_IZR, IZR_pow2 by lia.
  rewrite Rmult_assoc, <- bpow_plus. f_equal. f_equal. ring.
Qed.

(** ** Squarings rounded up and down

    [sq_up n P X] and [sq_dn n P X] square the fixed-point number
    [X 2^-P] [n] times, rounding each square up (down) to a multiple of
    [2^-P], so they bound [x^(2^n)] above (below) for [x] below (above)
    [X 2^-P]. *)
Fixpoint sq_up (n : nat) (P X : Z) : Z :=
  match n with O => X | S n => sq_up n P (- (- (X * X) / 2 ^ P)) end.

Fixpoint sq_dn (n : nat) (P X : Z) : Z :=
  match n with O => X | S n => sq_dn n P (X * X / 2 ^ P) end.

Local Lemma bpow_cancel : forall P, bpow radix2 P * bpow radix2 (- P) = 1.
Proof. intros P. rewrite <- bpow_plus, Z.add_opp_diag_r. reflexivity. Qed.

Local Lemma up_step :
  forall P X, (0 <= P)%Z ->
  (IZR X * bpow radix2 (- P)) ^ 2 <= IZR (- (- (X * X) / 2 ^ P)) * bpow radix2 (- P).
Proof.
intros P X HP.
set (Y := (- (- (X * X) / 2 ^ P))%Z).
assert (HD : (0 < 2 ^ P)%Z) by (apply Z.pow_pos_nonneg; lia).
assert (H : (X * X <= 2 ^ P * Y)%Z).
{ pose proof (Z.mul_div_le (- (X * X)) (2 ^ P) HD). unfold Y. lia. }
apply IZR_le in H. rewrite !mult_IZR, IZR_pow2 in H by exact HP.
apply Rle_trans with (bpow radix2 P * IZR Y * (bpow radix2 (- P) * bpow radix2 (- P))).
- replace ((IZR X * bpow radix2 (- P)) ^ 2)
    with (IZR X * IZR X * (bpow radix2 (- P) * bpow radix2 (- P))) by ring.
  apply Rmult_le_compat_r; [apply Rmult_le_pos; apply bpow_ge_0 | exact H].
- right. transitivity (IZR Y * bpow radix2 (- P) * (bpow radix2 P * bpow radix2 (- P)));
    [ring | rewrite bpow_cancel; ring].
Qed.

Local Lemma dn_step :
  forall P X, (0 <= P)%Z ->
  IZR (X * X / 2 ^ P) * bpow radix2 (- P) <= (IZR X * bpow radix2 (- P)) ^ 2.
Proof.
intros P X HP.
set (Y := (X * X / 2 ^ P)%Z).
assert (HD : (0 < 2 ^ P)%Z) by (apply Z.pow_pos_nonneg; lia).
assert (H : (2 ^ P * Y <= X * X)%Z) by exact (Z.mul_div_le (X * X) (2 ^ P) HD).
apply IZR_le in H. rewrite !mult_IZR, IZR_pow2 in H by exact HP.
apply Rle_trans with (bpow radix2 P * IZR Y * (bpow radix2 (- P) * bpow radix2 (- P))).
- right. transitivity (IZR Y * bpow radix2 (- P) * (bpow radix2 P * bpow radix2 (- P)));
    [rewrite bpow_cancel; ring | ring].
- replace ((IZR X * bpow radix2 (- P)) ^ 2)
    with (IZR X * IZR X * (bpow radix2 (- P) * bpow radix2 (- P))) by ring.
  apply Rmult_le_compat_r; [apply Rmult_le_pos; apply bpow_ge_0 | exact H].
Qed.

Lemma sq_up_correct :
  forall n P X x, (0 <= P)%Z -> 0 <= x -> x <= IZR X * bpow radix2 (- P) ->
  x ^ (2 ^ n)%nat <= IZR (sq_up n P X) * bpow radix2 (- P).
Proof.
intros n; induction n as [|n IH]; intros P X x HP Hx H.
- cbn [Nat.pow sq_up]. rewrite pow_1. exact H.
- cbn [sq_up]. replace (2 ^ S n)%nat with (2 * 2 ^ n)%nat by reflexivity.
  rewrite pow_mult. apply IH; [exact HP | apply pow_le; exact Hx |].
  apply Rle_trans with ((IZR X * bpow radix2 (- P)) ^ 2); [|apply up_step; exact HP].
  apply pow_incr. lra.
Qed.

Lemma sq_dn_correct :
  forall n P X x, (0 <= P)%Z -> (0 <= X)%Z -> IZR X * bpow radix2 (- P) <= x ->
  IZR (sq_dn n P X) * bpow radix2 (- P) <= x ^ (2 ^ n)%nat.
Proof.
intros n; induction n as [|n IH]; intros P X x HP HX H.
- cbn [Nat.pow sq_dn]. rewrite pow_1. exact H.
- cbn [sq_dn]. replace (2 ^ S n)%nat with (2 * 2 ^ n)%nat by reflexivity.
  rewrite pow_mult. apply IH; [exact HP | apply Z.div_pos; [nia | apply Z.pow_pos_nonneg; lia] |].
  apply Rle_trans with ((IZR X * bpow radix2 (- P)) ^ 2); [apply dn_step; exact HP |].
  assert (0 <= IZR X * bpow radix2 (- P))
    by (apply Rmult_le_pos; [apply IZR_le; exact HX | apply bpow_ge_0]).
  apply pow_incr. lra.
Qed.

(** ** Powers of 2 *)

Local Lemma pow_lt_compat : forall x y k, 0 <= x < y -> (k <> 0)%nat -> x ^ k < y ^ k.
Proof.
intros x y [|k] Hxy Hk; [contradiction|].
cbn [pow]. pose proof (pow_incr x y k ltac:(lra)). pose proof (pow_lt y k ltac:(lra)).
pose proof (pow_le x k ltac:(lra)). nra.
Qed.

(** [(2^(i/k))^k = 2^i] *)
Lemma rexp2_pow :
  forall (i : Z) (k : nat) (d : R), d = INR k -> (k <> 0)%nat -> (0 <= i)%Z ->
  Rexp2 (IZR i / d) ^ k = bpow radix2 i.
Proof.
intros i k d -> Hk Hi. unfold Rexp2.
rewrite <- Rpower_pow by (unfold Rpower; apply exp_pos).
rewrite Rpower_mult.
replace (IZR i / INR k * INR k) with (IZR i) by (field; apply not_0_INR; exact Hk).
rewrite <- (Z2Nat.id i Hi). set (m := Z.to_nat i).
rewrite <- INR_IZR_INZ, Rpower_pow by lra.
rewrite pow_IZR. apply IZR_pow2. lia.
Qed.

(** An entry [v] is within 2^-104 of [2^(i/2^n)] if the squarings of
    [v - 2^-104] rounded up and of [v + 2^-104] rounded down bracket
    [2^i]. *)
Lemma entry_close :
  forall (v d : R) (i P A B : Z) (n : nat),
  d = INR (2 ^ n)%nat -> (0 <= i)%Z -> (0 <= P)%Z ->
  v - bpow radix2 (-104) = IZR A * bpow radix2 (- P) ->
  v + bpow radix2 (-104) = IZR B * bpow radix2 (- P) ->
  (0 <= B)%Z ->
  (sq_up n P A <= 2 ^ (P + i))%Z ->
  (2 ^ (P + i) <= sq_dn n P B)%Z ->
  Rabs (v - Rexp2 (IZR i / d)) <= bpow radix2 (-104).
Proof.
intros v d i P A B n Hd Hi HP HA HB HB0 Hup Hdn.
assert (Hk : (2 ^ n <> 0)%nat) by (apply Nat.pow_nonzero; lia).
set (E := Rexp2 (IZR i / d)).
assert (HE : E ^ (2 ^ n)%nat = bpow radix2 i) by (unfold E; apply rexp2_pow; assumption).
assert (HE0 : 0 < E) by (unfold E, Rexp2, Rpower; apply exp_pos).
assert (H2 : IZR (2 ^ (P + i)) * bpow radix2 (- P) = bpow radix2 i)
  by (rewrite pow2_scale by lia; f_equal; ring).
assert (Hb : 0 < bpow radix2 (- P)) by apply bpow_gt_0.
apply Rabs_le. split.
- destruct (Rle_or_lt E (v + bpow radix2 (-104))) as [H|H]; [lra | exfalso].
  assert (HB0' : 0 <= IZR B * bpow radix2 (- P))
    by (apply Rmult_le_pos; [apply IZR_le; exact HB0 | lra]).
  assert (H0 : 0 <= v + bpow radix2 (-104)) by lra.
  pose proof (pow_lt_compat (v + bpow radix2 (-104)) E _ (conj H0 H) Hk) as H3.
  pose proof (sq_dn_correct n P B (v + bpow radix2 (-104)) HP HB0 (Req_le _ _ (eq_sym HB)))
    as H4.
  apply IZR_le in Hdn.
  pose proof (Rmult_le_compat_r _ _ _ (Rlt_le _ _ Hb) Hdn) as H5.
  lra.
- destruct (Rle_or_lt (v - bpow radix2 (-104)) E) as [H|H]; [lra | exfalso].
  assert (H0 : 0 <= E) by lra.
  assert (H0' : 0 <= v - bpow radix2 (-104)) by lra.
  pose proof (pow_lt_compat E (v - bpow radix2 (-104)) _ (conj H0 H) Hk) as H3.
  pose proof (sq_up_correct n P A (v - bpow radix2 (-104)) HP H0' (Req_le _ _ HA)) as H4.
  apply IZR_le in Hup.
  pose proof (Rmult_le_compat_r _ _ _ (Rlt_le _ _ Hb) Hup) as H5.
  lra.
Qed.

(** ** The tables *)

(** The check of the entry [(h, l)] (as bits) for [2^(i/2^n)], with
    [P = 256] fractional bits: [1 <= h < 2], [|l| <= 2^-53], and the
    squarings of [h + l -/+ 2^-104] bracket [2^i]. *)
Definition entry_okb (n : nat) (i : Z) (p : Z * Z) : bool :=
  match fix_of 256 (from_bits (fst p)), fix_of 256 (from_bits (snd p)) with
  | Some H, Some L =>
      (2 ^ 256 <=? H)%Z && (H <? 2 ^ 257)%Z && (Z.abs L <=? 2 ^ 203)%Z &&
      (0 <=? H + L + 2 ^ 152)%Z &&
      (sq_up n 256 (H + L - 2 ^ 152) <=? 2 ^ (256 + i))%Z &&
      (2 ^ (256 + i) <=? sq_dn n 256 (H + L + 2 ^ 152))%Z
  | _, _ => false
  end.

Fixpoint all_okb (n : nat) (t : list (Z * Z)) (i : Z) : bool :=
  match t with
  | [] => true
  | p :: t => entry_okb n i p && all_okb n t (i + 1)
  end.

Lemma all_okb_nth :
  forall n t i0 k, all_okb n t i0 = true -> (k < length t)%nat ->
  entry_okb n (i0 + Z.of_nat k) (nth k t (0, 0)%Z) = true.
Proof.
intros n t; induction t as [|p t IH]; intros i0 k H Hk; [cbn [length] in Hk; lia|].
cbn [all_okb] in H. apply andb_prop in H as [H1 H2].
destruct k as [|k]; cbn [nth].
- replace (i0 + Z.of_nat 0)%Z with i0 by lia. exact H1.
- replace (i0 + Z.of_nat (S k))%Z with ((i0 + 1) + Z.of_nat k)%Z by lia.
  apply IH; [exact H2 | cbn [length] in Hk; lia].
Qed.

Lemma entry_correct :
  forall n d i hb lb, d = INR (2 ^ n)%nat -> (0 <= i)%Z -> entry_okb n i (hb, lb) = true ->
  is_finite (from_bits hb) = true /\ is_finite (from_bits lb) = true /\
  1 <= B2R (from_bits hb) < 2 /\ Rabs (B2R (from_bits lb)) <= bpow radix2 (-53) /\
  Rabs (B2R (from_bits hb) + B2R (from_bits lb) - Rexp2 (IZR i / d)) <= bpow radix2 (-104).
Proof.
intros n d i hb lb Hd Hi Hok.
unfold entry_okb in Hok. cbn [fst snd] in Hok.
destruct (fix_of 256 (from_bits hb)) as [H|] eqn:EH; [|discriminate Hok].
destruct (fix_of 256 (from_bits lb)) as [L|] eqn:EL; [|discriminate Hok].
apply fix_of_correct in EH as [Fh Rh]. apply fix_of_correct in EL as [Fl Rl].
repeat rewrite andb_true_iff in Hok.
destruct Hok as [[[[[H1 H2] H3] H4] H5] H6].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
apply Z.leb_le in H4. apply Z.leb_le in H5. apply Z.leb_le in H6.
assert (Hb : 0 < bpow radix2 (-256)) by apply bpow_gt_0.
assert (Hb' : 0 < bpow radix2 (- (256))) by apply bpow_gt_0.
split; [exact Fh|]. split; [exact Fl|]. split; [|split].
- rewrite Rh. apply IZR_le in H1. apply IZR_lt in H2.
  pose proof (pow2_scale 256 256 ltac:(lia)) as K1.
  pose proof (pow2_scale 257 256 ltac:(lia)) as K2.
  replace (256 - 256)%Z with 0%Z in K1 by reflexivity.
  replace (257 - 256)%Z with 1%Z in K2 by reflexivity.
  change (bpow radix2 0) with 1 in K1. change (bpow radix2 1) with 2 in K2.
  split.
  + rewrite <- K1. apply Rmult_le_compat_r; lra.
  + rewrite <- K2. apply Rmult_lt_compat_r; lra.
- rewrite Rl, Rabs_mult, (Rabs_pos_eq (bpow radix2 _)) by apply bpow_ge_0.
  rewrite <- abs_IZR. apply IZR_le in H3.
  pose proof (pow2_scale 203 256 ltac:(lia)) as K.
  replace (203 - 256)%Z with (-53)%Z in K by reflexivity.
  rewrite <- K. apply Rmult_le_compat_r; lra.
- pose proof (pow2_scale 152 256 ltac:(lia)) as K.
  replace (152 - 256)%Z with (-104)%Z in K by reflexivity.
  apply (entry_close _ _ i 256 (H + L - 2 ^ 152) (H + L + 2 ^ 152) n Hd Hi ltac:(lia));
    [| | exact H4 | exact H5 | exact H6];
    rewrite Rh, Rl, ?minus_IZR, !plus_IZR, <- K; ring.
Qed.

Lemma tbl_correct :
  forall t n d i h l,
  all_okb n t 0 = true -> length t = 64%nat -> d = INR (2 ^ n)%nat ->
  (0 <= i < 64)%Z -> DyadicExp.tbl t i = (h, l) ->
  is_finite h = true /\ is_finite l = true /\ 1 <= B2R h < 2 /\
  Rabs (B2R l) <= bpow radix2 (-53) /\
  Rabs (B2R h + B2R l - Rexp2 (IZR i / d)) <= bpow radix2 (-104).
Proof.
intros t n d i h l Hok Hlen Hd Hi Ht.
pose proof (all_okb_nth n t 0 (Z.to_nat i) Hok ltac:(rewrite Hlen; lia)) as He.
rewrite Z.add_0_l, Z2Nat.id in He by lia.
unfold DyadicExp.tbl in Ht.
set (p := nth (Z.to_nat i) t (0, 0)%Z) in He, Ht. clearbody p. destruct p as [hb lb].
change ((from_bits hb, from_bits lb) = (h, l)) in Ht. injection Ht as <- <-.
apply (entry_correct n); [exact Hd | lia | exact He].
Qed.

Lemma T1_ok : all_okb 12 DyadicExp.T1 0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma T2_ok : all_okb 6 DyadicExp.T2 0 = true.
Proof. vm_compute. reflexivity. Qed.

(** 2^(i/4096) in double-double, for [i] in [0, 63]. *)
Theorem t1_correct :
  forall i h l, (0 <= i < 64)%Z -> DyadicExp.tbl DyadicExp.T1 i = (h, l) ->
  is_finite h = true /\ is_finite l = true /\ 1 <= B2R h < 2 /\
  Rabs (B2R l) <= bpow radix2 (-53) /\
  Rabs (B2R h + B2R l - Rexp2 (IZR i / 4096)) <= bpow radix2 (-104).
Proof.
intros i h l Hi Ht. apply (tbl_correct DyadicExp.T1 12); try assumption.
- exact T1_ok.
- vm_compute. reflexivity.
- rewrite INR_IZR_INZ. reflexivity.
Qed.

(** 2^(j/64) in double-double, for [j] in [0, 63]. *)
Theorem t2_correct :
  forall j h l, (0 <= j < 64)%Z -> DyadicExp.tbl DyadicExp.T2 j = (h, l) ->
  is_finite h = true /\ is_finite l = true /\ 1 <= B2R h < 2 /\
  Rabs (B2R l) <= bpow radix2 (-53) /\
  Rabs (B2R h + B2R l - Rexp2 (IZR j / 64)) <= bpow radix2 (-104).
Proof.
intros j h l Hj Ht. apply (tbl_correct DyadicExp.T2 6); try assumption.
- exact T2_ok.
- vm_compute. reflexivity.
- rewrite INR_IZR_INZ. reflexivity.
Qed.

(** ** The constants *)

(** [|v - c| <= 2^e3] for [v = S 2^e1] and [c] in [[L, L + 1] 2^e2], as
    checked on integers. *)
Definition close_okb (S L e1 e2 e3 : Z) : bool :=
  (e2 <=? e1)%Z && (e2 <=? e3)%Z &&
  (2 ^ (e1 - e2) * S - L <=? 2 ^ (e3 - e2))%Z &&
  (L + 1 - 2 ^ (e1 - e2) * S <=? 2 ^ (e3 - e2))%Z.

Lemma close_correct :
  forall (v c : R) (S L e1 e2 e3 : Z),
  close_okb S L e1 e2 e3 = true ->
  v = IZR S * bpow radix2 e1 ->
  IZR L * bpow radix2 e2 <= c <= (IZR L + 1) * bpow radix2 e2 ->
  Rabs (v - c) <= bpow radix2 e3.
Proof.
intros v c S L e1 e2 e3 Hok Hv Hc.
unfold close_okb in Hok. repeat rewrite andb_true_iff in Hok.
destruct Hok as [[[H1 H2] H3] H4].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
apply IZR_le in H3. apply IZR_le in H4.
rewrite minus_IZR, mult_IZR, !IZR_pow2 in H3 by lia.
rewrite minus_IZR, plus_IZR, mult_IZR, !IZR_pow2 in H4 by lia.
assert (K1 : bpow radix2 (e1 - e2) * bpow radix2 e2 = bpow radix2 e1)
  by (rewrite <- bpow_plus; f_equal; ring).
assert (K3 : bpow radix2 (e3 - e2) * bpow radix2 e2 = bpow radix2 e3)
  by (rewrite <- bpow_plus; f_equal; ring).
assert (Hb : 0 <= bpow radix2 e2) by apply bpow_ge_0.
apply (Rmult_le_compat_r _ _ _ Hb) in H3. apply (Rmult_le_compat_r _ _ _ Hb) in H4.
rewrite K3 in H3. rewrite K3 in H4.
replace ((bpow radix2 (e1 - e2) * IZR S - IZR L) * bpow radix2 e2)
  with (IZR S * bpow radix2 e1 - IZR L * bpow radix2 e2) in H3 by (rewrite <- K1; ring).
replace ((IZR L + 1 - bpow radix2 (e1 - e2) * IZR S) * bpow radix2 e2)
  with ((IZR L + 1) * bpow radix2 e2 - IZR S * bpow radix2 e1) in H4 by (rewrite <- K1; ring).
apply Rabs_le. lra.
Qed.

(** The sum of two [f64]s given by their bits, with [P] fractional bits *)
Definition dd_fix (P a b : Z) : option Z :=
  match fix_of P (from_bits a), fix_of P (from_bits b) with
  | Some x, Some y => Some (x + y)%Z
  | _, _ => None
  end.

Definition dd_close_okb (a b P L e2 e3 : Z) : bool :=
  match dd_fix P a b with Some s => close_okb s L (- P) e2 e3 | None => false end.

Lemma dd_close :
  forall (a b P L e2 e3 : Z) (c : R),
  dd_close_okb a b P L e2 e3 = true ->
  IZR L * bpow radix2 e2 <= c <= (IZR L + 1) * bpow radix2 e2 ->
  Rabs (B2R (from_bits a) + B2R (from_bits b) - c) <= bpow radix2 e3.
Proof.
intros a b P L e2 e3 c Hok Hc.
unfold dd_close_okb, dd_fix in Hok.
destruct (fix_of P (from_bits a)) as [x|] eqn:Ea; [|discriminate Hok].
destruct (fix_of P (from_bits b)) as [y|] eqn:Eb; [|discriminate Hok].
apply fix_of_correct in Ea as [_ Ra]. apply fix_of_correct in Eb as [_ Rb].
apply (close_correct _ _ _ _ _ _ _ Hok); [|exact Hc].
rewrite Ra, Rb, plus_IZR. ring.
Qed.

(** The bounds on ln 2 and ln 10 of [DyConst.v], scaled, with the
    4,224-bit integers behind the variable [L]. *)
Local Lemma ln_scaled :
  forall (c : R) (L e k : Z),
  IZR L * bpow radix2 e <= c < (IZR L + 1) * bpow radix2 e ->
  IZR L * bpow radix2 (e + k) <= c * bpow radix2 k <= (IZR L + 1) * bpow radix2 (e + k).
Proof.
intros c L e k Hc. rewrite bpow_plus.
assert (Hk : 0 < bpow radix2 k) by apply bpow_gt_0.
split.
- rewrite <- Rmult_assoc. apply Rmult_le_compat_r; lra.
- rewrite <- Rmult_assoc. apply Rmult_le_compat_r; lra.
Qed.

(** [C1] is [ln 2 / 4096] with its significand cut to 31 bits, and [C1 +
    C2] is [ln 2 / 4096] within 2^-98. *)
Theorem c1_exact : B2R (from_bits DyadicExp.C1) = IZR 1488522235 * bpow radix2 (-43).
Proof.
assert (H : fix_of 65 (from_bits DyadicExp.C1) = Some (1488522235 * 2 ^ 22)%Z)
  by (vm_compute; reflexivity).
apply fix_of_correct in H as [_ H]. rewrite H, mult_IZR, Rmult_assoc, pow2_scale by lia.
reflexivity.
Qed.

Theorem c12_correct :
  Rabs (B2R (from_bits DyadicExp.C1) + B2R (from_bits DyadicExp.C2) - ln 2 / 4096)
    <= bpow radix2 (-98).
Proof.
pose proof (ln_scaled _ _ _ (-12) LN2_bounds) as H.
replace (ln 2 * bpow radix2 (-12)) with (ln 2 / 4096) in H
  by (change (bpow radix2 (-12)) with (/ 4096); reflexivity).
apply (dd_close _ _ 96 (Limbs.val DyadicConsts.LN2) (-4224 + -12) (-98));
  [vm_compute; reflexivity | exact H].
Qed.

(** [INV] is [4096 / ln 2] within 2^-41, half its ulp. *)
Theorem inv_correct : Rabs (B2R (from_bits DyadicExp.INV) - 4096 / ln 2) <= bpow radix2 (-41).
Proof.
(* The steps that use [lra] and the large constants are checked as lemmas
   of their own ([abstract]): checked as one term, the kernel did not end
   its check of this proof at [Qed] within 15 minutes. *)
assert (HM : fix_of 41 (from_bits DyadicExp.INV) = Some 12994641697113596%Z)
  by (vm_compute; reflexivity).
apply fix_of_correct in HM as [_ HV]. change (Z.opp 41) with (-41)%Z in HV. rewrite HV.
pose proof LN2_bounds as HL. set (L := Limbs.val DyadicConsts.LN2) in HL.
assert (H1 : ((12994641697113596 - 1) * (L + 1) <= 2 ^ (12 + 41 + 4224))%Z).
{ abstract (apply Z.leb_le; unfold L; vm_compute; reflexivity). }
assert (H2 : (2 ^ (12 + 41 + 4224) <= (12994641697113596 + 1) * L)%Z).
{ abstract (apply Z.leb_le; unfold L; vm_compute; reflexivity). }
clearbody L.
apply IZR_le in H1, H2. rewrite mult_IZR, minus_IZR, plus_IZR, IZR_pow2 in H1 by lia.
rewrite mult_IZR, plus_IZR, IZR_pow2 in H2 by lia.
set (M := IZR 12994641697113596) in *.
set (b := bpow radix2 (-41)).
set (u := bpow radix2 (-4224)) in HL.
assert (Hu : 0 < u) by apply bpow_gt_0.
assert (Hbu : bpow radix2 (12 + 41 + 4224) * (b * u) = 4096).
{ abstract (unfold b, u; rewrite <- !bpow_plus; reflexivity). }
assert (Hln : 0 < ln 2) by (rewrite <- ln_1; apply ln_increasing; lra).
assert (HM1 : 1 <= M) by abstract (unfold M; apply IZR_le; lia).
assert (Hb0 : 0 < b) by apply bpow_gt_0.
apply Rabs_le. split.
- abstract (cut (4096 / ln 2 <= (M + 1) * b); [lra|];
  apply (Rmult_le_reg_r (ln 2)); [exact Hln|];
  replace (4096 / ln 2 * ln 2) with 4096 by (field; lra);
  rewrite <- Hbu;
  apply Rle_trans with ((M + 1) * IZR L * (b * u));
  [apply Rmult_le_compat_r; [apply Rmult_le_pos; lra | exact H2]
  |replace ((M + 1) * IZR L * (b * u)) with ((M + 1) * b * (IZR L * u)) by ring;
   apply Rmult_le_compat_l; [apply Rmult_le_pos; lra | lra]]).
- abstract (cut ((M - 1) * b <= 4096 / ln 2); [lra|];
  apply (Rmult_le_reg_r (ln 2)); [exact Hln|];
  replace (4096 / ln 2 * ln 2) with 4096 by (field; lra);
  rewrite <- Hbu;
  apply Rle_trans with ((M - 1) * (IZR L + 1) * (b * u));
  [replace ((M - 1) * (IZR L + 1) * (b * u)) with ((M - 1) * b * ((IZR L + 1) * u)) by ring;
   apply Rmult_le_compat_l; [apply Rmult_le_pos; lra | lra]
  |apply Rmult_le_compat_r; [apply Rmult_le_pos; lra | exact H1]]).
Qed.

(** [P3] and [P4] are 1/6 and 1/24 rounded to nearest. *)
Theorem p3_correct : Rabs (B2R (from_bits DyadicExp.P3) - / 6) <= bpow radix2 (-56).
Proof.
assert (H : fix_of 55 (from_bits DyadicExp.P3) = Some 6004799503160661%Z)
  by (vm_compute; reflexivity).
apply fix_of_correct in H as [_ H]. rewrite H.
cbn [bpow radix_val radix2 Z.opp].
apply Rabs_le. split; lra.
Qed.

Theorem p4_correct : Rabs (B2R (from_bits DyadicExp.P4) - / 24) <= bpow radix2 (-58).
Proof.
assert (H : fix_of 57 (from_bits DyadicExp.P4) = Some 6004799503160661%Z)
  by (vm_compute; reflexivity).
apply fix_of_correct in H as [_ H]. rewrite H.
cbn [bpow radix_val radix2 Z.opp].
apply Rabs_le. split; lra.
Qed.

(** [LN2] and [LN10] are ln 2 and ln 10 in double-double. *)
Theorem ln2_dd_correct :
  Rabs (B2R (from_bits (fst DyadicExp.LN2)) + B2R (from_bits (snd DyadicExp.LN2)) - ln 2)
    <= bpow radix2 (-106).
Proof.
destruct LN2_bounds as [H1 H2].
apply (dd_close _ _ 108 (Limbs.val DyadicConsts.LN2) (-4224) (-106));
  [vm_compute; reflexivity | split; [exact H1 | apply Rlt_le; exact H2]].
Qed.

Theorem ln10_dd_correct :
  Rabs (B2R (from_bits (fst DyadicExp.LN10)) + B2R (from_bits (snd DyadicExp.LN10)) - ln 10)
    <= bpow radix2 (-105).
Proof.
destruct LN10_bounds as [H1 H2].
apply (dd_close _ _ 105 (Limbs.val DyadicConsts.LN10) (-4222) (-105));
  [vm_compute; reflexivity | split; [exact H1 | apply Rlt_le; exact H2]].
Qed.
