(** * The slow path of [mul_add_ru] rounds toward +inf

    [mul_add1_ru_slow a b c] is IEEE 754 [a * b + c] with a single rounding
    toward +inf, i.e. Flocq's [Bfma mode_UP a b c], including the sign of a
    zero, overflow, the infinities and NaN. It never panics.

    If an input is not finite, or [a] or [b] is zero, the result is the
    same rounded to nearest as toward +inf, and [mul_add1_special] computes
    it with the default rounding mode. If [c] is zero, [a * b + c] is the
    product [a * b], which [mul1_ru_slow] rounds up. Otherwise the product
    of the significands is exact in a [u128] ([< 2^106]), and
    [sum_round_up] adds it to [c] and rounds the sum itself, as
    [add1_ru_slow] does for two floats. *)

From Stdlib Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Calc.Operations.
From Inari Require Import Model Encoding Spec Decompose RoundUpExact
  SumRoundUp StepUp MulRu.

Open Scope R_scope.

(** ** The special cases *)

(** If an input is +-inf or NaN, or [a] or [b] is zero, [a * b + c] in the
    default rounding mode, which [mul_add1_special] computes as [mul] then
    [add], is [Bfma mode_UP a b c]. *)
Lemma mul_add1_special_correct :
  forall a b c,
  negb (Generic.is_finite a && Generic.is_finite b && Generic.is_finite c)
    || eq a zero || eq b zero = true ->
  Generic.mul_add1_special a b c = Bfma mode_UP a b c.
Proof.
intros a b c H.
unfold Generic.mul_add1_special, add, mul.
rewrite !is_finite_eq in H |- *.
(* With every sign fixed, both sides compute. A zero product plus a zero
   [c] is [Bplus mode_NE] of two zeros, whose sign is [false] unless both
   are [true], as is [Bfma_szero mode_UP]. A finite nonzero [a * b] plus
   [c] is excluded by [H] unless [c] is +-inf or NaN, and then both sides
   are [c]. *)
destruct a as [[|]|[|]| |[|] ma ea Ha], b as [[|]|[|]| |[|] mb eb Hb],
  c as [[|]|[|]| |[|] mc ec Hc];
  try discriminate H; reflexivity.
Qed.

(** ** Rounding up a fused multiply-add *)

(** A finite float that [eq] does not find equal to [zero] is nonzero. *)
Lemma B2R_neq_0 :
  forall x : f64, is_finite x = true -> eq x zero = false -> B2R x <> 0.
Proof.
intros x Fx Hx.
unfold eq in Hx.
rewrite Beqb_correct in Hx by first [exact Fx | reflexivity].
change (B2R zero) with 0 in Hx.
destruct (Req_bool_spec (B2R x) 0); [discriminate | assumption].
Qed.

(** For finite [a], [b] and [c] with [a * b + c <> 0], a float that is
    [a * b + c] rounded up as [rounds_up_to] describes is
    [Bfma mode_UP a b c]. *)
Lemma Bfma_rounds_up :
  forall a b c r : f64,
  is_finite a = true -> is_finite b = true -> is_finite c = true ->
  B2R a * B2R b + B2R c <> 0 ->
  rounds_up_to (B2R a * B2R b + B2R c) r -> r = Bfma mode_UP a b c.
Proof.
intros a b c r Fa Fb Fc H0 Hr.
unfold rounds_up_to in Hr.
generalize (@Bfma_correct 53 1024 _ _ mode_UP a b c Fa Fb Fc).
cbv zeta.
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_UP)) with RU.
destruct (Rlt_bool (Rabs (RU (B2R a * B2R b + B2R c))) (bpow radix2 1024)).
- destruct Hr as (HR & HF & HS). intros (HR' & HF' & HS').
  apply B2R_Bsign_inj; [exact HF | exact HF' | congruence |].
  (* [Bfma] gives a nonzero result the sign of [a * b + c]. *)
  rewrite HS, HS'.
  destruct (Rcompare_spec (B2R a * B2R b + B2R c) 0) as [H|H|H].
  + now apply Rlt_bool_true.
  + contradiction.
  + apply Rlt_bool_false. lra.
- intros HO. apply B2SF_inj. rewrite Hr, HO. reflexivity.
Qed.

(** For finite nonzero [x] and [y], [Bmult mode_UP x y] is [x * y] rounded
    up as [rounds_up_to] describes. *)
Lemma Bmult_rounds_up_to :
  forall x y : f64,
  is_finite x = true -> is_finite y = true -> B2R x <> 0 -> B2R y <> 0 ->
  rounds_up_to (B2R x * B2R y) (Bmult mode_UP x y).
Proof.
intros x y Fx Fy Hx0 Hy0.
(* [Bmult] gives the product the sign [xorb (Bsign x) (Bsign y)]. *)
assert (Hs : Rlt_bool (B2R x * B2R y) 0 = xorb (Bsign x) (Bsign y)).
{ rewrite (Bsign_B2R x Fx Hx0), (Bsign_B2R y Fy Hy0).
  now apply Rlt_bool_mult. }
unfold rounds_up_to. rewrite Hs.
generalize (@Bmult_correct 53 1024 _ _ mode_UP x y).
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_UP)) with RU.
destruct (Rlt_bool (Rabs (RU (B2R x * B2R y))) (bpow radix2 1024)).
- intros (HR & HF & HS). rewrite Fx, Fy in HF.
  split; [exact HR|]. split; [exact HF|].
  apply HS. apply finite_not_nan. exact HF.
- intros HO. exact HO.
Qed.

(** ** The slow path *)

Theorem mul_add1_ru_slow_correct :
  forall a b c, Generic.mul_add1_ru_slow a b c = Some (Bfma mode_UP a b c).
Proof.
intros a b c.
unfold Generic.mul_add1_ru_slow.
destruct (negb (Generic.is_finite a && Generic.is_finite b && Generic.is_finite c)
  || eq a zero || eq b zero) eqn:Hsp.
{ f_equal. now apply mul_add1_special_correct. }
rewrite !is_finite_eq in Hsp.
apply Bool.orb_false_elim in Hsp as [Hsp Hb0].
apply Bool.orb_false_elim in Hsp as [Hf Ha0].
apply Bool.negb_false_iff, andb_prop in Hf as [Hf Fc].
apply andb_prop in Hf as [Fa Fb].
assert (Ha0' := B2R_neq_0 a Fa Ha0).
assert (Hb0' := B2R_neq_0 b Fb Hb0).
destruct (eq c zero) eqn:Hc0.
{ (* [c] is a zero, so [a * b + c] is [a * b], which [mul1_ru_slow] rounds
     up. *)
  rewrite mul1_ru_slow_correct. f_equal.
  apply eq_zero_iff in Hc0 as (sc & ->).
  apply Bfma_rounds_up; [exact Fa | exact Fb | reflexivity | ..];
    cbn [B2R]; rewrite Rplus_0_r.
  - now apply Rmult_integral_contrapositive_currified.
  - now apply Bmult_rounds_up_to. }
generalize (decompose_correct a Fa Ha0) (decompose_correct b Fb Hb0)
  (decompose_correct c Fc Hc0).
destruct (Generic.decompose a) as ((sa, ma), ea).
destruct (Generic.decompose b) as ((sb, mb), eb).
destruct (Generic.decompose c) as ((sc, mc), ec).
intros (-> & Hma & Hea & Ha) (-> & Hmb & Heb & Hb) (-> & Hmc & Hec & Hc).
(* [ma * mb < 2^106] fits [u128], and [ea + eb] fits [i32]. *)
assert (Hmab : (0 < ma * mb < 2^106)%Z) by nia.
rewrite checked_u_ok by lia. cbv beta iota.
rewrite checked_i_ok by (simpl; lia). cbv beta iota.
(* The product is exact: [a * b = +-(ma * mb) * 2^(ea + eb)], negative if
   exactly one of [a] and [b] is. *)
assert (Hab : cond_Ropp (negb (Bool.eqb (Bsign a) (Bsign b)))
    (F2R (Float radix2 (ma * mb) (ea + eb))) = B2R a * B2R b).
{ rewrite Ha, Hb.
  change (Float radix2 (ma * mb) (ea + eb))
    with (Fmult (Float radix2 ma ea) (Float radix2 mb eb)).
  rewrite F2R_mult.
  destruct (Bsign a), (Bsign b); cbn [Bool.eqb negb cond_Ropp]; ring. }
assert (HP : 0 < F2R (Float radix2 (ma * mb) (ea + eb)))
  by (apply F2R_gt_0; simpl; lia).
assert (HZ : 0 < F2R (Float radix2 mc ec)) by (apply F2R_gt_0; simpl; lia).
generalize (sum_round_up_reduce (negb (Bool.eqb (Bsign a) (Bsign b)))
  (ma * mb) (ea + eb) (Bsign c) mc ec
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
cbv zeta. rewrite Hab, <- Hc.
generalize (@Bfma_correct 53 1024 _ _ mode_UP a b c Fa Fb Fc).
cbv zeta.
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_UP)) with RU.
intros HB [(H0 & ->) | (neg & m & e & sticky & Hpre & ->)].
- (* An exact cancellation gives +0, as [a * b] and [c] then have opposite
     signs, so that [Bfma_szero mode_UP] is [false]. *)
  rewrite H0, round_0, Rabs_R0, Rlt_bool_true, Rcompare_Eq in HB
    by first [reflexivity | apply bpow_gt_0 | typeclasses eauto].
  destruct HB as (HR & HF & HS).
  f_equal. apply B2R_Bsign_inj; [reflexivity | exact HF | now rewrite HR |].
  rewrite HS.
  revert H0. rewrite <- Hab, Hc. unfold Bfma_szero.
  destruct (Bsign a), (Bsign b), (Bsign c);
    cbn [Bool.eqb negb xorb cond_Ropp]; try reflexivity; lra.
- destruct (round_up_exact_correct neg m e sticky _ Hpre) as (r & -> & Hr).
  assert (Hv : B2R a * B2R b + B2R c <> 0).
  { destruct Hpre as (Hm & _ & _ & _ & Hloc).
    assert (0 < F2R (Float radix2 m e)) by (apply F2R_gt_0; simpl; lia).
    intros H0. rewrite H0, Rabs_R0 in Hloc.
    destruct sticky; lra. }
  f_equal. now apply Bfma_rounds_up.
Qed.
