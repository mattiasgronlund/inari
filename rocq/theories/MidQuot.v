(** * The quotient of [midpoint_quotient] at a midpoint of the subnormal [f64]s

    [DyadicAtan.midpoint_quotient] of [Model.v] divides [y] by [x] at one
    limb, rounded toward -inf to [lo] and toward +inf to [hi], and tests
    that [lo] and [hi] have the same fields [neg], [exp] and [m[0]], that
    [lo.exp] plus the trailing zeros of [lo.m[0]] is -1075, and, before
    the divisions, that [a.exp - b.exp <= -1022] for the dyadic numbers
    [a] of [y] and [b] of [x]. Where the tests pass, for [y] nonzero and
    [x > 0], [div_mid] proves that [lo] is [y / x], and an odd multiple
    [o 2^-1075] of 2^-1075 in magnitude below 2^-1021, which with
    [dy_ok 1 lo] are the hypotheses of [to_f64_mid] of [MidRound.v]. With
    one limb, [m[0]] is the whole mantissa ([val_limb0]), so [lo] and
    [hi] are the same number, and as [lo <= y / x <= hi]
    ([dround_bounds]) it is [y / x] ([div_exact]). [o] is the odd part
    of [lo.m[0]] ([DyPowRules.trailing_zeros_odd]).
    The bound comes from the exponents: [|y| < 2^(a.exp + 64)] and
    [|x| >= 2^(b.exp + 63)] ([dy_cases]), so
    [|y / x| < 2^(a.exp - b.exp + 1) <= 2^-1021]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Limbs DyRound DyConv DyOps.
From Inari Require DyPowRules.

Open Scope R_scope.

(** ** Helpers *)

(** With one limb, the mantissa is its limb 0. *)
Local Lemma val_limb0 :
  forall d, dy_ok 1 d -> Limbs.val (Dyadic.dy_m d) = Limbs.limb (Dyadic.dy_m d) 0.
Proof.
intros d Hd.
assert (Hn : level_ok 1) by (unfold level_ok; lia).
pose proof Hd as (Hm & _).
rewrite (limb0_val _ Hm).
destruct (dy_cases 1 d Hn Hd) as [(_ & Hv & _) | (_ & Hv & _)].
- rewrite Hv. reflexivity.
- symmetry. apply Z.mod_small. split; [apply val_nonneg, Hm | exact (proj2 Hv)].
Qed.

(** The dyadic numbers [a] of [y] and [b] of [x] are exact, and the
    divisions rounded both ways give the same fields, so the same number,
    which lies between them and is thus [y / x]. *)
Local Lemma div_exact :
  forall y x a b lo hi,
  is_finite y = true -> is_finite x = true -> 0 < B2R x ->
  Dyadic.from_f64 1 y = Some a -> Dyadic.from_f64 1 x = Some b ->
  Dyadic.div 1 a b false = Some lo -> Dyadic.div 1 a b true = Some hi ->
  Dyadic.dy_neg lo = Dyadic.dy_neg hi -> Dyadic.dy_exp lo = Dyadic.dy_exp hi ->
  Limbs.limb (Dyadic.dy_m lo) 0 = Limbs.limb (Dyadic.dy_m hi) 0 ->
  dy_ok 1 a /\ dy_ok 1 b /\ Dyadic.dy_R a = B2R y /\ Dyadic.dy_R b = B2R x /\
  dy_ok 1 lo /\ Dyadic.dy_R lo = B2R y / B2R x.
Proof.
intros y x a b lo hi Fy Fx Hx Ea Eb Elo Ehi Hneg Hexp Hm.
assert (Hn : level_ok 1) by (unfold level_ok; lia).
destruct (from_f64_correct 1 y Hn Fy) as (a' & Ea' & Oa & Sa & Va).
rewrite Ea in Ea'. injection Ea' as <-.
destruct (from_f64_correct 1 x Hn Fx) as (b' & Eb' & Ob & Sb & Vb).
rewrite Eb in Eb'. injection Eb' as <-.
assert (Hb : Dyadic.dy_R b <> 0) by (rewrite Vb; lra).
destruct (div_correct 1 a b false Hn Oa Ob Sa Sb Hb) as (lo' & Elo' & Olo & Vlo).
rewrite Elo in Elo'. injection Elo' as <-.
destruct (div_correct 1 a b true Hn Oa Ob Sa Sb Hb) as (hi' & Ehi' & Ohi & Vhi).
rewrite Ehi in Ehi'. injection Ehi' as <-.
assert (E : Dyadic.dy_R lo = Dyadic.dy_R hi).
{ unfold Dyadic.dy_R. rewrite (val_limb0 lo Olo), (val_limb0 hi Ohi), Hneg, Hexp, Hm.
  reflexivity. }
pose proof (dround_bounds 1 (Dyadic.dy_R a / Dyadic.dy_R b) Hn) as Hr.
rewrite Va, Vb in Hr, Vlo, Vhi.
split; [exact Oa |]. split; [exact Ob |]. split; [exact Va |]. split; [exact Vb |].
split; [exact Olo |]. lra.
Qed.

(** ** [midpoint_quotient] *)

(** The arithmetic of [DyadicAtan.midpoint_quotient]: its hypotheses on
    [a], [b], [lo] and [hi] are those of its branch that returns
    [Some (Some f)], as [Z.ltb_ge], [Bool.eqb_prop] and [Z.eqb_eq] give
    them, for [y] nonzero and [x > 0], as in [atan2_near_with]. Then [lo]
    is [y / x], of magnitude [o 2^-1075] with [o] odd, below 2^-1021. *)
Lemma div_mid :
  forall y x a b lo hi,
  is_finite y = true -> is_finite x = true -> B2R y <> 0 -> 0 < B2R x ->
  Dyadic.from_f64 1 y = Some a -> Dyadic.from_f64 1 x = Some b ->
  (Dyadic.dy_exp a - Dyadic.dy_exp b <= -1022)%Z ->
  Dyadic.div 1 a b false = Some lo -> Dyadic.div 1 a b true = Some hi ->
  Dyadic.dy_neg lo = Dyadic.dy_neg hi -> Dyadic.dy_exp lo = Dyadic.dy_exp hi ->
  Limbs.limb (Dyadic.dy_m lo) 0 = Limbs.limb (Dyadic.dy_m hi) 0 ->
  (Dyadic.dy_exp lo + trailing_zeros 64 (Limbs.limb (Dyadic.dy_m lo) 0) = -1075)%Z ->
  dy_ok 1 lo /\ Dyadic.dy_R lo = B2R y / B2R x /\
  exists o, Z.odd o = true /\ (0 < o)%Z /\
    Rabs (Dyadic.dy_R lo) = IZR o * bpow radix2 (-1075) /\
    IZR o * bpow radix2 (-1075) < bpow radix2 (-1021).
Proof.
intros y x a b lo hi Fy Fx Hy Hx Ea Eb He Elo Ehi Hneg Hexp Hm Htz.
assert (Hn : level_ok 1) by (unfold level_ok; lia).
destruct (div_exact y x a b lo hi Fy Fx Hx Ea Eb Elo Ehi Hneg Hexp Hm)
  as (Oa & Ob & Va & Vb & Olo & Vlo).
split; [exact Olo |]. split; [exact Vlo |].
assert (Hq : B2R y / B2R x <> 0).
{ unfold Rdiv. apply Rmult_integral_contrapositive_currified; [exact Hy |].
  apply Rinv_neq_0_compat. lra. }
pose proof (dprec_bounds 1 Hn) as Hp.
(* [lo] is not zero, so its limb 0 is its mantissa of 64 bits. *)
assert (Hm0 : (0 < Limbs.limb (Dyadic.dy_m lo) 0)%Z).
{ destruct (dy_cases 1 lo Hn Olo) as [(_ & _ & _ & _ & H0) | (_ & Hv & _)].
  - rewrite Vlo in H0. contradiction.
  - rewrite (val_limb0 lo Olo) in Hv.
    assert (0 < 2 ^ (dprec 1 - 1))%Z by (apply Z.pow_pos_nonneg; lia).
    lia. }
(* [m = o 2^t] with [o] odd, and [lo.exp + t = -1075]. *)
destruct (DyPowRules.trailing_zeros_odd _ Hm0) as (Ht & Ho & Hmo).
assert (Habs : Rabs (Dyadic.dy_R lo) =
  IZR (Z.shiftr (Limbs.limb (Dyadic.dy_m lo) 0)
    (trailing_zeros 64 (Limbs.limb (Dyadic.dy_m lo) 0))) * bpow radix2 (-1075)).
{ rewrite (dy_abs lo (proj1 Olo)), (val_limb0 lo Olo).
  rewrite Hmo at 1. rewrite mult_IZR, (DyOps.IZR_pow2 _ Ht), Rmult_assoc, <- bpow_plus.
  replace (trailing_zeros 64 (Limbs.limb (Dyadic.dy_m lo) 0) + Dyadic.dy_exp lo)%Z
    with (-1075)%Z by lia.
  reflexivity. }
exists (Z.shiftr (Limbs.limb (Dyadic.dy_m lo) 0)
  (trailing_zeros 64 (Limbs.limb (Dyadic.dy_m lo) 0))).
split; [exact Ho |].
split.
{ assert (0 < 2 ^ trailing_zeros 64 (Limbs.limb (Dyadic.dy_m lo) 0))%Z
    by (apply Z.pow_pos_nonneg; lia).
  nia. }
split; [exact Habs |].
rewrite <- Habs, Vlo.
(* [|y| < 2^(a.exp + 64)] and [|x| >= 2^(b.exp + 63)], as [a] and [b]
   are not zero. *)
destruct (dy_cases 1 a Hn Oa) as [(_ & _ & _ & _ & H0) | (_ & _ & _ & Ha)].
{ rewrite Va in H0. contradiction. }
destruct (dy_cases 1 b Hn Ob) as [(_ & _ & _ & _ & H0) | (_ & _ & Hb & _)].
{ rewrite Vb in H0. lra. }
rewrite Va in Ha. rewrite Vb in Hb.
assert (Hyx : Rabs (B2R y) = Rabs (B2R y / B2R x) * Rabs (B2R x)).
{ rewrite <- Rabs_mult. f_equal. field. lra. }
assert (HB : 0 < bpow radix2 (Dyadic.dy_exp b + dprec 1 - 1)) by apply bpow_gt_0.
assert (Hlt : Rabs (B2R y / B2R x) * bpow radix2 (Dyadic.dy_exp b + dprec 1 - 1) <
  bpow radix2 (Dyadic.dy_exp a + dprec 1)).
{ apply Rle_lt_trans with (Rabs (B2R y)); [| exact Ha].
  rewrite Hyx. apply Rmult_le_compat_l; [apply Rabs_pos | exact Hb]. }
(* [2^(a.exp + 64) <= 2^-1021 2^(b.exp + 63)] by the test on the exponents. *)
assert (Hle : bpow radix2 (Dyadic.dy_exp a + dprec 1) <=
  bpow radix2 (-1021) * bpow radix2 (Dyadic.dy_exp b + dprec 1 - 1)).
{ rewrite <- bpow_plus. apply bpow_le. lia. }
apply Rmult_lt_reg_r with (bpow radix2 (Dyadic.dy_exp b + dprec 1 - 1)); [exact HB | lra].
Qed.
