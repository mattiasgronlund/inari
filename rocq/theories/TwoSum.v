(** * [two_sum_err] is exact in binary64

    [two_sum_err x y s] with [s = RN(x + y)] is Knuth's TwoSum (D. E. Knuth,
    The Art of Computer Programming, Vol. 2, 3rd ed., 1998, Section 4.2.2,
    Theorem B): six operations rounded to nearest give the exact error
    [e = (x + y) - s] of the addition.

    Flocq proves TwoSum for formats with subnormals and no largest exponent
    ([Pff2Flocq.TwoSum_correct], from Boldo's Pff library), so it holds even
    if an operation underflows. Binary64 does have a largest exponent: what
    is left to prove here is that no operation overflows, which holds if
    [|x|, |y| < 2^1023] and [s] is finite. *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Flocq Require Pff.Pff2Flocq.
From Inari Require Import Model Encoding.

Open Scope R_scope.

(** Rounding to nearest, ties to even, in binary64 without overflow. *)
Notation RN := (round radix2 fexp64 ZnearestE).

(** ** One operation at a time *)

(** The powers of two that bound the operands: rounding a value below
    [2^1024] moves it by at most [2^971], half an ulp of the top binade. *)
Lemma bpow_facts :
  0 < bpow radix2 971 /\ 8 * bpow radix2 971 <= bpow radix2 1023 /\
  bpow radix2 1024 = 2 * bpow radix2 1023.
Proof.
split; [apply bpow_gt_0 | split].
- change 8 with (bpow radix2 3).
  rewrite <- bpow_plus. apply bpow_le. lia.
- change 2 with (bpow radix2 1).
  rewrite <- bpow_plus. reflexivity.
Qed.

(** [|RN z - z| <= ulp(2^1024) / 2 = 2^971] if [|z| <= 2^1024]. *)
Lemma RN_error :
  forall z, Rabs z <= bpow radix2 1024 -> Rabs (RN z - z) <= bpow radix2 971.
Proof.
intros z Hz.
apply Rle_trans with (/2 * ulp radix2 fexp64 z).
{ apply error_le_half_ulp; typeclasses eauto. }
apply Rle_trans with (/2 * ulp radix2 fexp64 (bpow radix2 1024)).
{ apply Rmult_le_compat_l. lra.
  apply ulp_le; [typeclasses eauto .. |].
  rewrite (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0. exact Hz. }
rewrite ulp_bpow.
change (fexp64 (1024 + 1)) with (1 + 971)%Z.
rewrite bpow_plus. change (bpow radix2 1) with 2.
lra.
Qed.

(** Every operand of [two_sum_err] is at most [2^1023 + 2^971] in
    magnitude, which keeps its rounded value below [2^1024]. *)
Lemma RN_no_overflow :
  forall z, Rabs z <= bpow radix2 1023 + bpow radix2 971 ->
  Rabs (RN z) < bpow radix2 1024.
Proof.
intros z Hz.
destruct bpow_facts as (Hu & H8 & H2).
assert (He : Rabs (RN z - z) <= bpow radix2 971) by (apply RN_error; lra).
apply Rabs_le_inv in Hz, He.
apply Rabs_lt. lra.
Qed.

(** [x - y] and [x + y] are finite and rounded to nearest if the exact
    result is at most [2^1023 + 2^971] in magnitude. *)
Lemma sub_no_overflow :
  forall x y, is_finite x = true -> is_finite y = true ->
  Rabs (B2R x - B2R y) <= bpow radix2 1023 + bpow radix2 971 ->
  is_finite (sub x y) = true /\ B2R (sub x y) = RN (B2R x - B2R y).
Proof.
intros x y Fx Fy H.
generalize (@Bminus_correct 53 1024 _ _ mode_NE x y Fx Fy).
rewrite Rlt_bool_true by exact (RN_no_overflow _ H).
intros (HR & HF & _).
split; [exact HF | exact HR].
Qed.

Lemma add_no_overflow :
  forall x y, is_finite x = true -> is_finite y = true ->
  Rabs (B2R x + B2R y) <= bpow radix2 1023 + bpow radix2 971 ->
  is_finite (add x y) = true /\ B2R (add x y) = RN (B2R x + B2R y).
Proof.
intros x y Fx Fy H.
generalize (@Bplus_correct 53 1024 _ _ mode_NE x y Fx Fy).
rewrite Rlt_bool_true by exact (RN_no_overflow _ H).
intros (HR & HF & _).
split; [exact HF | exact HR].
Qed.

(** If [x + y] is finite, it is [RN(x + y)], because an overflow when
    rounding to nearest gives an infinity. *)
Lemma add_B2R :
  forall x y, is_finite x = true -> is_finite y = true ->
  is_finite (add x y) = true -> B2R (add x y) = RN (B2R x + B2R y).
Proof.
intros x y Fx Fy Fs.
generalize (@Bplus_correct 53 1024 _ _ mode_NE x y Fx Fy).
destruct (Rlt_bool _ _).
- intros (HR & _). exact HR.
- intros (HO & _). exfalso.
  revert Fs HO. unfold add.
  destruct (Bplus mode_NE x y); intros F HO; discriminate.
Qed.

(** ** TwoSum *)

(** [e = two_sum_err x y (x + y)] is finite and [e = (x + y) - s] exactly,
    where [s = x + y] is the rounded sum. *)
Theorem two_sum_err_correct :
  forall x y,
  is_finite x = true -> is_finite y = true ->
  Rabs (B2R x) < bpow radix2 1023 -> Rabs (B2R y) < bpow radix2 1023 ->
  is_finite (add x y) = true ->
  is_finite (Generic.two_sum_err x y (add x y)) = true /\
  B2R (Generic.two_sum_err x y (add x y)) = B2R x + B2R y - B2R (add x y).
Proof.
intros x y Fx Fy Hx Hy Fs.
destruct bpow_facts as (Hu & H8 & H2).
apply Rabs_lt_inv in Hx, Hy.
unfold Generic.two_sum_err. cbv beta zeta.
(* Each step bounds the operands of the next by the rounding errors so far,
   each at most [2^971] by [RN_error]. *)
assert (HS := add_B2R x y Fx Fy Fs).
assert (ES : Rabs (B2R (add x y) - (B2R x + B2R y)) <= bpow radix2 971).
{ rewrite HS. apply RN_error. apply Rabs_le. lra. }
apply Rabs_le_inv in ES.
set (s := add x y) in *. clearbody s.
(* [s - y = x + (s - (x + y))]. *)
destruct (sub_no_overflow s y Fs Fy) as (Fa & HA).
{ apply Rabs_le. lra. }
assert (EA : Rabs (B2R (sub s y) - (B2R s - B2R y)) <= bpow radix2 971).
{ rewrite HA. apply RN_error. apply Rabs_le. lra. }
apply Rabs_le_inv in EA.
set (a := sub s y) in *. clearbody a.
(* [s - a = y - (a - (s - y))]. *)
destruct (sub_no_overflow s a Fs Fa) as (Fb & HB).
{ apply Rabs_le. lra. }
assert (EB : Rabs (B2R (sub s a) - (B2R s - B2R a)) <= bpow radix2 971).
{ rewrite HB. apply RN_error. apply Rabs_le. lra. }
apply Rabs_le_inv in EB.
set (b := sub s a) in *. clearbody b.
(* [x - a] and [y - b] are each the sum of two rounding errors. *)
destruct (sub_no_overflow x a Fx Fa) as (Fda & HDA).
{ apply Rabs_le. lra. }
assert (EDA : Rabs (B2R (sub x a) - (B2R x - B2R a)) <= bpow radix2 971).
{ rewrite HDA. apply RN_error. apply Rabs_le. lra. }
destruct (sub_no_overflow y b Fy Fb) as (Fdb & HDB).
{ apply Rabs_le. lra. }
assert (EDB : Rabs (B2R (sub y b) - (B2R y - B2R b)) <= bpow radix2 971).
{ rewrite HDB. apply RN_error. apply Rabs_le. lra. }
apply Rabs_le_inv in EDA, EDB.
destruct (add_no_overflow (sub x a) (sub y b) Fda Fdb) as (Fe & HE).
{ apply Rabs_le. lra. }
split; [exact Fe |].
(* Flocq's TwoSum computes [a] as [RN(s - x)], so swap [x] and [y]: its
   [x'] is our [a], its [dx] our [y - b] and its [dy] our [x - a]. *)
(* Ties to even is symmetric, [RN(-z) = -RN(z)], as Flocq's
   [TwoSum_correct] requires. *)
assert (Hchoice : forall z, negb (Z.even z) = negb (negb (Z.even (- (z + 1))))).
{ intros z. rewrite Z.even_opp, Z.even_add. destruct (Z.even z); reflexivity. }
pose proof (Pff2Flocq.TwoSum_correct (-1074) 53 (fun z => negb (Z.even z))
  ltac:(lia) ltac:(lia) Hchoice (B2R y) (B2R x)
  (generic_format_B2R _ _ y) (generic_format_B2R _ _ x)) as T.
rewrite (Rplus_comm (B2R y) (B2R x)) in T.
rewrite <- HS, <- HA, <- HB, <- HDA, <- HDB in T.
rewrite (Rplus_comm (B2R (sub y b))), <- HE in T.
lra.
Qed.
