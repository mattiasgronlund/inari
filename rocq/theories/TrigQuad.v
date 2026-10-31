(** * The quadrant of a float, from the signs of [sin] and [cos]

    [quadrant] in [src/elementary.rs] returns [floor(r / (π/2)) mod 4] for
    a finite float [r], from the signs of MPFR's [sin_rd(r)] and
    [cos_ru(r)] ([quadrant_correct]). Rounding down keeps [sin r < 0] and
    never makes a [sin r >= 0] negative, and rounding up keeps [cos r > 0]
    and never makes a [cos r <= 0] positive, so the tests decide the signs
    of [sin r] and [cos r] exactly. On [[k * π/2, (k + 1) * π/2)], the
    signs are those of the quadrant [k mod 4]: [sin r >= 0] and [cos r > 0]
    for 0, [sin r >= 0] and [cos r <= 0] for 1, [sin r < 0] and
    [cos r <= 0] for 2, and [sin r < 0] and [cos r > 0] for 3. The strict
    ones fail only at the lower ends of quadrants 2 and 3, the odd
    multiples of π and of π/2, which no float is, as π is irrational
    ([pi_irrational], and [tan_dom_f64] in [TrigPieces.v]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr MpfrRound PiIrrational TrigPieces
  TrigBranch.

Open Scope R_scope.

(** ** The signs that [quadrant] tests *)

(** [sin_rd(r) < 0] exactly when [sin r < 0]: rounding down keeps a
    negative value below 0, and rounds a value of at least 0 to at least 0,
    as 0 is a float. The result is finite, as [-1 <= sin r] and -1 is a
    float. *)
Lemma qd_sin_neg :
  forall emin emax m (r : f64), range_ok emin emax -> get_d_ok emin emax m ->
  sin_ok emin emax m -> is_finite r = true ->
  (Model.lt (sin_rd m r) Model.zero = true <-> sin (B2R r) < 0).
Proof.
intros emin emax m r Hr Hget Hsin Fr.
pose proof (mpfr_fn_correct emin emax m real_dom sin (mpfr_sin m) Hr Hget Hsin RNDD r Fr I)
  as H.
change (mpfr_fn m (mpfr_sin m) RNDD r) with (sin_rd m r) in H.
set (w := sin_rd m r) in *. clearbody w.
assert (Fw : is_finite w = true)
  by exact (tb_rd_finite _ _ H (proj1 (SIN_bound _))).
destruct (round_finite_pt _ _ _ _ Fw H) as (_ & Hle & Hmax).
assert (F0 : f64_format 0) by (exists Model.zero; split; reflexivity).
unfold Model.lt. rewrite Bltb_correct by first [exact Fw | reflexivity].
change (B2R Model.zero) with 0.
case Rlt_bool_spec; intros Hw; split; intros E; try reflexivity; try discriminate E.
- (* A [sin r >= 0] would round down to at least the float 0. *)
  destruct (Rlt_or_le (sin (B2R r)) 0) as [Hn | Hn]; [exact Hn |].
  specialize (Hmax 0 F0 Hn). lra.
- lra.
Qed.

(** [cos_ru(r) > 0] exactly when [cos r > 0], in the same way. *)
Lemma qd_cos_pos :
  forall emin emax m (r : f64), range_ok emin emax -> get_d_ok emin emax m ->
  cos_ok emin emax m -> is_finite r = true ->
  (Model.lt Model.zero (cos_ru m r) = true <-> 0 < cos (B2R r)).
Proof.
intros emin emax m r Hr Hget Hcos Fr.
pose proof (mpfr_fn_correct emin emax m real_dom cos (mpfr_cos m) Hr Hget Hcos RNDU r Fr I)
  as H.
change (mpfr_fn m (mpfr_cos m) RNDU r) with (cos_ru m r) in H.
set (w := cos_ru m r) in *. clearbody w.
assert (Fw : is_finite w = true)
  by exact (tb_ru_finite _ _ H (proj2 (COS_bound _))).
destruct (round_finite_pt _ _ _ _ Fw H) as (_ & Hge & Hmin).
assert (F0 : f64_format 0) by (exists Model.zero; split; reflexivity).
unfold Model.lt. rewrite Bltb_correct by first [exact Fw | reflexivity].
change (B2R Model.zero) with 0.
case Rlt_bool_spec; intros Hw; split; intros E; try reflexivity; try discriminate E.
- (* A [cos r <= 0] would round up to at most the float 0. *)
  destruct (Rlt_or_le 0 (cos (B2R r))) as [Hp | Hp]; [exact Hp |].
  specialize (Hmin 0 F0 Hp). lra.
- lra.
Qed.

(** No finite [f64] is a nonzero integer multiple of π, as no finite
    [f64] is a pole of [tan] ([tan_dom_f64] in [TrigPieces.v]): it is a
    dyadic rational, and π is irrational. *)
Lemma qd_not_kpi :
  forall w : f64, is_finite w = true -> forall k : Z, k <> 0%Z -> B2R w <> IZR k * PI.
Proof.
intros w Hw k Hk0 Hk.
destruct (tp_B2R_rat w Hw) as (n & d & Hd & Hnd).
(* [k * PI = n / d], so [PI = n / (d * k)], whose divisor is a nonzero
   integer; flip both signs if it is negative. *)
assert (Hd' : IZR d <> 0) by (apply not_0_IZR; lia).
assert (Hk' : IZR k <> 0) by (apply not_0_IZR; exact Hk0).
assert (Hn : IZR n = IZR k * PI * IZR d) by (rewrite <- Hk, Hnd; field; exact Hd').
assert (Heq : PI = IZR n / IZR (d * k)).
{ rewrite mult_IZR, Hn; field; split; assumption. }
destruct (Z.lt_trichotomy 0 (d * k)) as [Hq | [Hq | Hq]].
- exact (pi_irrational _ _ Hq Heq).
- symmetry in Hq; apply Z.mul_eq_0 in Hq; lia.
- apply (pi_irrational (- n)%Z (- (d * k))%Z); [lia |].
  rewrite Heq, !opp_IZR; field.
  apply not_0_IZR; lia.
Qed.

(** ** The quadrant *)

(** The float that [quadrant] returns for the quadrant [j]. *)
Definition quad_f (j : Z) : f64 :=
  if (j =? 0)%Z then Model.zero
  else if (j =? 1)%Z then of_u64 1
  else if (j =? 2)%Z then of_u64 2
  else of_u64 3.

Theorem quadrant_correct :
  forall emin emax m (r : f64) k,
  range_ok emin emax -> get_d_ok emin emax m -> sin_ok emin emax m -> cos_ok emin emax m ->
  is_finite r = true -> IZR k * (PI / 2) <= B2R r < (IZR k + 1) * (PI / 2) ->
  quadrant m r = quad_f (k mod 4).
Proof.
intros emin emax m r k Hr Hget Hsin Hcos Fr Hk.
pose proof (qd_sin_neg emin emax m r Hr Hget Hsin Fr) as Hs.
pose proof (qd_cos_pos emin emax m r Hr Hget Hcos Fr) as Hc.
pose proof PI_RGT_0 as HPI.
unfold quadrant. cbv zeta.
(* [k = 4 * i + j] with [j = k mod 4], and [u = r - 2 * i * PI] is in
   [[j * PI/2, (j + 1) * PI/2)], with the [sin] and [cos] of [r]. *)
assert (Hj : (k mod 4 = 0 \/ k mod 4 = 1 \/ k mod 4 = 2 \/ k mod 4 = 3)%Z)
  by (pose proof (Z.mod_pos_bound k 4); lia).
destruct Hj as [Hj | [Hj | [Hj | Hj]]]; rewrite Hj;
  destruct (tp_mod4 k _ Hj) as [i Hi]; rewrite Hi in Hk;
  rewrite (tp_sin_sub (B2R r) i) in Hs; rewrite (tp_cos_sub (B2R r) i) in Hc.
- (* Quadrant 0: [sin u >= 0] and [cos u > 0]. *)
  set (u := B2R r - 2 * IZR i * PI) in *.
  assert (Hu : 0 <= u < PI / 2) by (unfold u; lra).
  pose proof (sin_ge_0 u ltac:(lra) ltac:(lra)) as S.
  pose proof (cos_gt_0 u ltac:(lra) ltac:(lra)) as C.
  assert (E1 : Model.lt (sin_rd m r) Model.zero = false)
    by (apply Bool.not_true_is_false; intros E; apply Hs in E; lra).
  assert (E2 : Model.lt Model.zero (cos_ru m r) = true) by (apply Hc; exact C).
  rewrite E1, E2. reflexivity.
- (* Quadrant 1: [sin u >= 0] and [cos u <= 0]. *)
  set (u := B2R r - 2 * IZR i * PI) in *.
  assert (Hu : PI / 2 <= u < PI) by (unfold u; lra).
  pose proof (sin_ge_0 u ltac:(lra) ltac:(lra)) as S.
  pose proof (cos_le_0 u ltac:(lra) ltac:(lra)) as C.
  assert (E1 : Model.lt (sin_rd m r) Model.zero = false)
    by (apply Bool.not_true_is_false; intros E; apply Hs in E; lra).
  assert (E2 : Model.lt Model.zero (cos_ru m r) = false)
    by (apply Bool.not_true_is_false; intros E; apply Hc in E; lra).
  rewrite E1, E2. reflexivity.
- (* Quadrant 2: [sin u < 0], as [u] is not [PI], and [cos u <= 0]. *)
  assert (Hn : B2R r <> (2 * IZR i + 1) * PI).
  { replace (2 * IZR i + 1) with (IZR (2 * i + 1)) by (rewrite plus_IZR, mult_IZR; reflexivity).
    apply (qd_not_kpi r Fr); lia. }
  set (u := B2R r - 2 * IZR i * PI) in *.
  assert (Hu : PI <= u < 3 * (PI / 2)) by (unfold u; lra).
  assert (Hu' : PI < u).
  { destruct Hu as [[Hlt | Heq] _]; [exact Hlt |].
    exfalso; apply Hn; unfold u in Heq; lra. }
  pose proof (sin_lt_0 u ltac:(lra) ltac:(lra)) as S.
  pose proof (cos_le_0 u ltac:(lra) ltac:(lra)) as C.
  assert (E1 : Model.lt (sin_rd m r) Model.zero = true) by (apply Hs; exact S).
  assert (E2 : Model.lt Model.zero (cos_ru m r) = false)
    by (apply Bool.not_true_is_false; intros E; apply Hc in E; lra).
  rewrite E1, E2. reflexivity.
- (* Quadrant 3: [sin u < 0], and [cos u > 0] as [u] is not [3 * PI/2]. *)
  assert (Hn : B2R r <> (2 * IZR i + 1 + / 2) * PI).
  { replace (2 * IZR i + 1) with (IZR (2 * i + 1)) by (rewrite plus_IZR, mult_IZR; reflexivity).
    exact (tan_dom_f64 r Fr (2 * i + 1)%Z). }
  set (u := B2R r - 2 * IZR i * PI) in *.
  assert (Hu : 3 * (PI / 2) <= u < 2 * PI) by (unfold u; lra).
  assert (Hu' : 3 * (PI / 2) < u).
  { destruct Hu as [[Hlt | Heq] _]; [exact Hlt |].
    exfalso; apply Hn; unfold u in Heq; lra. }
  pose proof (sin_lt_0 u ltac:(lra) ltac:(lra)) as S.
  (* [cos u = cos (u - 2 * PI)], with [u - 2 * PI] in [(-PI/2, 0)]. *)
  rewrite (tp_cos_sub u 1) in Hc.
  pose proof (cos_gt_0 (u - 2 * IZR 1 * PI) ltac:(lra) ltac:(lra)) as C.
  assert (E1 : Model.lt (sin_rd m r) Model.zero = true) by (apply Hs; exact S).
  assert (E2 : Model.lt Model.zero (cos_ru m r) = true) by (apply Hc; exact C).
  rewrite E1, E2. reflexivity.
Qed.
