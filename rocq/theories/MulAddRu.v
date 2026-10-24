(** * [mul_add_ru] rounds toward +inf

    [mul_add_ru] is IEEE 754 fused multiply-add rounded toward +inf on both
    lanes, i.e. Flocq's [Bfma mode_UP], including the sign of a zero,
    overflow, the infinities and NaN, both with and without an FMA. It
    never panics.

    The fast path, [mul_add1_ru_fast], computes [r1 = RN(a * b + c)], with
    the FMA or with [mul_add1_rn_emulated] (S. Boldo and G. Melquiond,
    Emulation of FMA and correctly rounded sums: proved algorithms using
    rounding to odd, IEEE Trans. Computers 57(4), 2008, Algorithm 1;
    EmulatedFma.v), and the sign of its error with ErrFma (S. Boldo and
    J.-M. Muller, Exact and approximated error of the FMA, IEEE Trans.
    Computers 60(2), 2011, Algorithm 4), and steps [r1] up to the next
    float if the error is positive (MulAddRuFast.v). If an input is not
    finite, or [a] or [b] is zero, the result is the same rounded to
    nearest as toward +inf, and [mul_add1_special] computes it with the
    default rounding mode. The slow path, [mul_add1_ru_slow], adds the
    exact product of the significands to [c] and rounds the sum itself
    (MulAddRuSlow.v). *)

From Stdlib Require Import Reals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Spec EmulatedFma MulAddRuFast MulAddRuSlow.

Open Scope R_scope.

(** ** The fast path *)

Theorem mul_add1_ru_fast_correct :
  forall fma a b c,
  snd (Generic.mul_add1_ru_fast fma a b c) = true ->
  fst (Generic.mul_add1_ru_fast fma a b c) = Bfma mode_UP a b c.
Proof.
intros fma a b c Hok.
destruct (negb (Generic.is_finite a && Generic.is_finite b && Generic.is_finite c)
  || eq a zero || eq b zero) eqn:Hsp.
{ unfold Generic.mul_add1_ru_fast. cbv zeta. cbn [fst].
  rewrite Hsp. now apply mul_add1_special_correct. }
(* [a], [b] and [c] are finite. *)
assert (Hf := Hsp).
apply Bool.orb_false_elim in Hf as [Hf _].
apply Bool.orb_false_elim in Hf as [Hf _].
rewrite !is_finite_eq in Hf.
apply Bool.negb_false_iff, andb_prop in Hf as [Hf Fc].
apply andb_prop in Hf as [Fa Fb].
(* [r1] is [Bfma mode_NE a b c]: with an FMA by the definition of
   [mul_add], and without one by [mul_add1_rn_emulated_correct]. *)
destruct (mul_add1_ru_fast_rounds_up fma a b c) as [(_ & H) | (H0 & Hr)];
  [destruct fma; [reflexivity | now apply mul_add1_rn_emulated_correct]
  | exact Hsp | exact Hok | exact H |].
now apply Bfma_rounds_up.
Qed.

(** ** Both lanes *)

Theorem mul_add_ru_impl_correct :
  forall fma x y z,
  Generic.mul_add_ru_impl fma x y z =
    Some (Bfma mode_UP (fst x) (fst y) (fst z),
          Bfma mode_UP (snd x) (snd y) (snd z)).
Proof.
intros fma [x0 x1] [y0 y1] [z0 z1].
(* Each lane is the fast path if it is valid, and the slow path if not. *)
assert (L : forall a b c,
  (if snd (Generic.mul_add1_ru_fast fma a b c)
   then Some (fst (Generic.mul_add1_ru_fast fma a b c))
   else Generic.mul_add1_ru_slow a b c) = Some (Bfma mode_UP a b c)).
{ intros a b c.
  destruct (snd (Generic.mul_add1_ru_fast fma a b c)) eqn:Hok.
  - f_equal. now apply mul_add1_ru_fast_correct.
  - apply mul_add1_ru_slow_correct. }
generalize (L x0 y0 z0) (L x1 y1 z1).
unfold Generic.mul_add_ru_impl. cbn [fst snd].
destruct (Generic.mul_add1_ru_fast fma x0 y0 z0) as (r0, ok0).
destruct (Generic.mul_add1_ru_fast fma x1 y1 z1) as (r1, ok1).
cbn [fst snd].
intros H0 H1.
destruct ok0, ok1; cbn [andb];
  rewrite ?H0, ?H1; try injection H0 as ->; try injection H1 as ->; reflexivity.
Qed.

(** [mul_add_ru] is correct whether the target has an FMA or not. *)
Theorem mul_add_ru_correct :
  forall has_fma x y z,
  Generic.mul_add_ru has_fma x y z =
    Some (Bfma mode_UP (fst x) (fst y) (fst z),
          Bfma mode_UP (snd x) (snd y) (snd z)).
Proof.
intros has_fma x y z. apply mul_add_ru_impl_correct.
Qed.
