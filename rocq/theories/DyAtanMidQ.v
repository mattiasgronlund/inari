(** * The quotients of [atan2_near] midway between two [f64]s below 2^-1021

    For finite [y <> 0] and [x > 0], [midpoint_quotient y x] of
    [DyadicAtan] in [Model.v] returns an [f64] [f] only if [y / x] is an
    odd multiple of 2^-1075 below 2^-1021 in absolute value, a midpoint
    between two [f64]s, and then [f] is the [f64] next to [y / x] toward
    zero, so that [atan (y / x)] rounds to nearest to [f] by
    [near_atan_mid] and [near_atan_mid_neg] of [NearAtanMid.v]
    ([midpoint_quotient_correct]). The exponents of [y] and [x] as
    dyadics of normalized mantissas bound [|y / x|] by 2^-1021, the two
    quotients at 1 limb rounded down and up agree only if they are
    [y / x] exactly, the trailing zeros of the mantissa make it an odd
    multiple of 2^-1075 ([div_mid] of [MidQuot.v]), and [Dyadic.to_f64]
    rounds it toward zero ([to_f64_mid] of [MidRound.v]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model NearF64 NearAtanMid DyRound MidRound MidQuot.

Open Scope R_scope.

(** For finite [y <> 0] and [x > 0], an [f64] that [midpoint_quotient]
    returns is [atan (y / x)] rounded to nearest. *)
Lemma midpoint_quotient_correct :
  forall y x f,
  is_finite y = true -> is_finite x = true -> B2R y <> 0 -> 0 < B2R x ->
  DyadicAtan.midpoint_quotient y x = Some (Some f) ->
  near_round (atan (B2R y / B2R x)) f.
Proof.
intros y x f Fy Fx Zy Px H.
unfold DyadicAtan.midpoint_quotient in H.
destruct (ge (mul (fabs y) DyadicAtan.two_1021) x); [discriminate H|].
destruct (Dyadic.from_f64 1 y) as [a|] eqn:Ea; [|discriminate H].
cbv beta iota zeta in H.
destruct (Dyadic.from_f64 1 x) as [b|] eqn:Eb; [|discriminate H].
cbv beta iota zeta in H.
destruct (-1022 <? Dyadic.dy_exp a - Dyadic.dy_exp b)%Z eqn:Ee; [discriminate H|].
apply Z.ltb_ge in Ee.
destruct (Dyadic.div 1 a b false) as [lo|] eqn:Elo; [|discriminate H].
cbv beta iota zeta in H.
destruct (Dyadic.div 1 a b true) as [hi|] eqn:Ehi; [|discriminate H].
cbv beta iota zeta in H.
match type of H with context [if ?c then _ else _] => destruct c eqn:C end;
  [|discriminate H].
apply andb_prop in C as [C Ct]. apply andb_prop in C as [C Cm].
apply andb_prop in C as [Cn Ce].
apply Bool.eqb_prop in Cn. apply Z.eqb_eq in Ce, Cm, Ct.
destruct (MidQuot.div_mid y x a b lo hi Fy Fx Zy Px Ea Eb Ee Elo Ehi Cn Ce Cm Ct)
  as (Olo & Vlo & o & Oo & Po & Ao & Bo).
destruct (to_f64_mid lo o Olo Oo Po Ao Bo) as (f' & Ef & Ff & Sf & Vf).
rewrite Ef in H. cbv beta iota in H. injection H as <-.
pose proof (dy_R_sign lo (proj1 Olo)) as HR. rewrite Ao in HR.
rewrite <- Vlo.
destruct (Dyadic.dy_neg lo).
- apply near_atan_mid_neg; [exact Ff | exact Sf | lra | lra].
- apply near_atan_mid; [exact Ff | exact Sf | lra | lra].
Qed.
