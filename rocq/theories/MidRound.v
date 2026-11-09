(** * [to_f64] toward zero at a midpoint of the subnormal [f64]s

    Below 2^-1021 the [f64]s are the multiples of 2^-1074, and the
    midpoints between them the odd multiples of 2^-1075. [Dyadic.to_f64]
    of a dyadic [lo] with [up] the sign of [lo] rounds toward zero, so at
    such a midpoint, of magnitude [o 2^-1075], it gives the [f64] of
    magnitude [(o - 1) 2^-1075] toward zero from it, with the sign of
    [lo], also when that [f64] is a zero ([to_f64_mid]). For both signs
    [to_f64] in [Model.v] calls [round_up lo true], which rounds
    [-(o 2^-1075)] up, and negates its result for [lo > 0].
    [round_up_correct] of [DyConv.v] states that rounding as
    [rounds_up_to], which fixes the sign of a zero result, where
    [mpfr_round] leaves it free. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model DyRound DyConv.

Open Scope R_scope.

(** ** Helpers *)

(** Below 2^-1021 the exponent of the format is -1074, as [cexp_sub] of
    [NearAtanMid.v], which is local there. *)
Local Lemma cexp_sub :
  forall r, r <> 0 -> Rabs r < bpow radix2 (-1021) ->
  cexp radix2 (FLT_exp (-1074) 53) r = (-1074)%Z.
Proof.
intros r H0 H1. unfold cexp, FLT_exp. apply Z.max_r.
assert (mag radix2 r <= -1021)%Z by now apply mag_le_bpow.
lia.
Qed.

(** Rounded up, the midpoint [-(2 k + 1) 2^-1075] below 2^-1021 in
    magnitude is [-k 2^-1074], as [-(2 k + 1) 2^-1075 2^1074] is
    [-k - 1/2]. *)
Local Lemma round_up_mid :
  forall k, (0 <= k)%Z ->
  IZR (2 * k + 1) * bpow radix2 (-1075) < bpow radix2 (-1021) ->
  round radix2 (FLT_exp (-1074) 53) Zceil (- (IZR (2 * k + 1) * bpow radix2 (-1075))) =
  - (IZR k * bpow radix2 (-1074)).
Proof.
intros k Hk Hs.
pose proof (bpow_gt_0 radix2 (-1075)) as Hb.
assert (HV : 0 < IZR (2 * k + 1) * bpow radix2 (-1075)).
{ apply Rmult_lt_0_compat; [apply IZR_lt; lia | exact Hb]. }
unfold round, scaled_mantissa, F2R. cbn [Fnum Fexp].
rewrite cexp_sub.
2: { lra. }
2: { rewrite Rabs_Ropp, Rabs_pos_eq by lra. exact Hs. }
change (- (-1074))%Z with 1074%Z.
assert (Hh : bpow radix2 (-1075) * bpow radix2 1074 = / 2).
{ rewrite <- bpow_plus. reflexivity. }
replace (- (IZR (2 * k + 1) * bpow radix2 (-1075)) * bpow radix2 1074)
  with (- (IZR k + / 2)).
2: { rewrite plus_IZR, mult_IZR, Ropp_mult_distr_l, Rmult_assoc, Hh. field. }
rewrite (Zceil_imp (- k)%Z).
- rewrite opp_IZR. ring.
- rewrite minus_IZR, opp_IZR. lra.
Qed.

(** ** [to_f64] at a midpoint *)

(** At an odd multiple [o 2^-1075] of 2^-1075 below 2^-1021 in magnitude,
    [to_f64] with [up] the sign of [lo] gives the [f64] 2^-1075 nearer to
    zero than [lo], with the sign of [lo]: [+0] for [lo = 2^-1075] and
    [-0] for [lo = -2^-1075]. *)
Lemma to_f64_mid :
  forall lo o, dy_ok 1 lo -> Z.odd o = true -> (0 < o)%Z ->
  Rabs (Dyadic.dy_R lo) = IZR o * bpow radix2 (-1075) ->
  IZR o * bpow radix2 (-1075) < bpow radix2 (-1021) ->
  exists f, Dyadic.to_f64 1 lo (Dyadic.dy_neg lo) = Some f /\ is_finite f = true /\
    Bsign f = Dyadic.dy_neg lo /\
    B2R f = (if Dyadic.dy_neg lo then Dyadic.dy_R lo + bpow radix2 (-1075)
             else Dyadic.dy_R lo - bpow radix2 (-1075)).
Proof.
intros lo o Hx Ho Ho0 Ha Hs.
assert (Hn : level_ok 1) by (unfold level_ok; lia).
destruct (proj1 (Z.odd_spec o) Ho) as [k Hk]. subst o.
assert (Hk0 : (0 <= k)%Z) by lia.
pose proof (bpow_gt_0 radix2 (-1075)) as Hb.
assert (HV : 0 < IZR (2 * k + 1) * bpow radix2 (-1075)).
{ apply Rmult_lt_0_compat; [apply IZR_lt; lia | exact Hb]. }
assert (HVe : IZR (2 * k + 1) * bpow radix2 (-1075) =
              2 * (IZR k * bpow radix2 (-1075)) + bpow radix2 (-1075)).
{ rewrite plus_IZR, mult_IZR. ring. }
assert (H2 : bpow radix2 (-1074) = 2 * bpow radix2 (-1075)).
{ change (-1074)%Z with (1 + -1075)%Z. rewrite bpow_plus. reflexivity. }
assert (H1024 : bpow radix2 (-1021) < bpow radix2 1024) by (apply bpow_lt; lia).
assert (Hk' : 0 <= IZR k * bpow radix2 (-1075)).
{ apply Rmult_le_pos; [apply IZR_le; exact Hk0 | lra]. }
destruct (dy_cases 1 lo Hn Hx) as [(_ & _ & _ & _ & H0) | (Hz & _)].
{ rewrite H0, Rabs_R0 in Ha. lra. }
pose proof Hx as (Hm & _).
(* Both signs round [-(o 2^-1075)] up. *)
destruct (round_up_correct 1 lo true (- (IZR (2 * k + 1) * bpow radix2 (-1075))) Hn Hx Hz)
  as (r & Hr & Hu).
{ rewrite Rabs_Ropp, Rabs_pos_eq by lra. symmetry. exact Ha. }
{ apply Rlt_bool_true. lra. }
unfold Spec.rounds_up_to in Hu.
rewrite (round_up_mid k Hk0 Hs) in Hu.
rewrite (Rlt_bool_true (Rabs _) (bpow radix2 1024)) in Hu.
2: { rewrite Rabs_Ropp, H2, Rabs_pos_eq; lra. }
rewrite (Rlt_bool_true (- _) 0) in Hu by lra.
destruct Hu as (Hv & Hf & Hsg).
pose proof (dy_R_sign lo Hm) as HR. rewrite Ha in HR.
unfold Dyadic.to_f64. rewrite Hz. revert HR.
destruct (Dyadic.dy_neg lo); cbv beta iota; intros HR.
- (* [lo < 0]: [round_up] itself. *)
  exists r. split; [exact Hr |]. split; [exact Hf |]. split; [exact Hsg |].
  rewrite Hv, HR, H2. lra.
- (* [lo > 0]: [round_up] of [-lo], negated. *)
  assert (Hr' : is_nan r = false) by (destruct r; try discriminate Hf; reflexivity).
  exists (opp r). split; [cbn [negb]; rewrite Hr; reflexivity |].
  unfold opp. split; [rewrite is_finite_Bopp; exact Hf |].
  split; [rewrite Bsign_Bopp, Hsg by exact Hr'; reflexivity |].
  rewrite B2R_Bopp, Hv, HR, H2. lra.
Qed.
