(** * The series of [acosh] near 1

    [DyadicLog.fast_acosh_near1] of [Model.v] computes [acosh x] for
    [1 < x < 1 + 2^-8] as [2 asinh s] with [s = sqrt u] and
    [u = (x - 1)/2] ([acosh_asinh_half]):
    - [u] is exact (Sterbenz's lemma, then a halving), in
      [[2^-53, 2^-9)];
    - [(sh, sl) = Fast.dd_sqrt(u, 0)] is within [2^-100 s] of [s]
      ([dd_sqrt_correct] of [FastDdSqrt.v]);
    - [asinh s = s (1 + W(u))] up to [s^17/80 <= 2^-78 s]
      ([asinh_taylor15] of [AsinhTaylor.v]), where
      [W(u) = -u/6 + 3u^2/40 - 5u^3/112 + 35u^4/1152 - 63u^5/2816
      + 231u^6/13312 - 143u^7/10240];
    - [-mh + wl] is within [2^-71] of [W(u)]: [mh = RN(u c3)] with
      [c3 = RN(1/6)], and [wl] holds the rest, Horner's scheme for the
      tail, the error of [mh] and [u] times the low part of [1/6];
    - [(h, l)] is within [2^-70 sh] of [(sh + sl)(1 - mh + wl)], by two
      exact Fast2Sums;
    - [Fast.normalize] scales [h] into [[1, 2)] by [2^-k'], and the
      branch returns [k = k' + 1], since [acosh x 2^-(k'+1) = asinh s 2^-k'].

    The error is at most [2^-69 h] before the scaling, so within [2^-68]
    after it. [acosh_near1_correct] states [2^-67], the bound of the
    [ERR67] rounding tests of the wrappers ([FastAhyp.v]), and
    [acosh_near1_fma] that the branch does not depend on [HAS_FMA].

    Both rest on five bounds on the steps of the branch: [near1_u],
    [near1_w] and [near1_ml_fma] of [FastAhypNear1Poly.v] for [u], [mh]
    and [wl], and [near1_sum] and [near1_pe_fma] of [FastAhypNear1Sum.v]
    for [(h, l)]. *)

From Stdlib Require Import ZArith Reals Lra Lia Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Relative.
From Inari Require Import Model Elementary Encoding TwoSum FastDdSqrt FastRoundErr AsinhTaylor
  FastAhypNear1Poly FastAhypNear1Sum.
From Inari Require FastLogReduce.

Open Scope R_scope.

Local Notation format := (generic_format radix2 fexp64).

(** Powers of 2 as numerals, for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp].

(** ** The identity *)

(** [acosh(1 + d) = 2 asinh(sqrt(d/2))]: with [s = sqrt(d/2)] and
    [q = sqrt(s^2 + 1)], [(s + q)^2 = 1 + d + 2 s q], and [2 s q] is
    [sqrt((1 + d)^2 - 1)], as both are nonnegative with the square
    [d^2 + 2d]. *)
Theorem acosh_asinh_half :
  forall d, 0 <= d -> Racosh (1 + d) = 2 * arcsinh (sqrt (d / 2)).
Proof.
intros d Hd.
unfold Racosh, arcsinh.
set (s := sqrt (d / 2)).
assert (Hs : 0 <= s) by apply sqrt_pos.
assert (Ss : s * s = d / 2) by (apply sqrt_sqrt; lra).
set (q := sqrt (s ^ 2 + 1)).
assert (Hq : 0 < q) by (apply sqrt_lt_R0; nra).
assert (Qq : q * q = s * s + 1)
  by (unfold q; rewrite sqrt_sqrt by nra; ring).
assert (R : sqrt ((1 + d) * (1 + d) - 1) = 2 * s * q).
{ rewrite <- (sqrt_square (2 * s * q)) by nra.
  f_equal.
  replace (2 * s * q * (2 * s * q)) with (4 * (s * s) * (q * q)) by ring.
  rewrite Qq, Ss. field. }
assert (E : (s + q) * (s + q) = 1 + d + 2 * s * q).
{ replace ((s + q) * (s + q)) with (s * s + q * q + 2 * s * q) by ring.
  rewrite Qq, Ss. field. }
rewrite R, <- E, ln_mult by lra.
ring.
Qed.

(** ** Helpers *)

Local Lemma format_bpow64 : forall e, (-1074 <= e)%Z -> format (bpow radix2 e).
Proof. intros e He. apply generic_format_bpow. unfold FLT_exp. lia. Qed.

(** [x <= y] is false for [f64]s with [y < x] (and not otherwise). *)
Local Lemma le_false :
  forall x y, is_finite x = true -> is_finite y = true -> Model.le x y = false ->
  B2R y < B2R x.
Proof.
intros x y Fx Fy H. unfold Model.le in H. rewrite Bleb_correct in H by assumption.
destruct (Rle_bool_spec (B2R x) (B2R y)); [discriminate | assumption].
Qed.

(** The rounding to nearest of a normal [x] is within [2^-53] of [x]
    relatively to the result (as [rn_rel] of [FastAhypAcosh.v]). *)
Local Lemma rn_rel :
  forall x, bpow radix2 (-1022) <= Rabs x ->
  Rabs (RN x - x) <= bpow radix2 (-53) * Rabs (RN x).
Proof.
intros x Hx.
assert (H : Rabs (RN x - x) <= / 2 * bpow radix2 (-52) * Rabs (RN x))
  by exact (relative_error_N_FLT_round radix2 (-1074) 53 eq_refl
    (fun z => negb (Z.even z)) x Hx).
assert (E : / 2 * bpow radix2 (-52) = bpow radix2 (-53))
  by (cbn [bpow radix_val radix2]; lra).
rewrite E in H. exact H.
Qed.

(** Rounding to nearest is monotone, and leaves a [f64] in place. *)
Local Lemma rn_ge :
  forall a b, format a -> a <= b -> a <= RN b.
Proof.
intros a b Fa H.
rewrite <- (round_generic radix2 fexp64 ZnearestE a Fa) at 1.
apply round_le; [typeclasses eauto .. | exact H].
Qed.

Local Lemma rn_le :
  forall a b, format a -> b <= a -> RN b <= a.
Proof.
intros a b Fa H.
rewrite <- (round_generic radix2 fexp64 ZnearestE a Fa).
apply round_le; [typeclasses eauto .. | exact H].
Qed.

(** ** The square root *)

Local Lemma u_range :
  forall u : f64, bpow radix2 (-53) <= B2R u < bpow radix2 (-9) ->
  bpow radix2 (-900) <= B2R u <= bpow radix2 900.
Proof.
intros u Hu.
split.
- apply Rle_trans with (bpow radix2 (-53)); [apply bpow_le; lia | lra].
- apply Rle_trans with (bpow radix2 (-9)); [lra | apply bpow_le; lia].
Qed.

(** [(sh, sl) = Fast.dd_sqrt(u, 0)] for [u] in [[2^-53, 2^-9)]: [s = sqrt u]
    is in [[2^-26.5, 2^-4.5)], so [sh] is in [[2^-27, 2^-4]], and
    [|sl| <= 2^-53 sh] as [sh = RN(sh + sl)]. *)
Local Lemma near1_sqrt :
  forall fma u sh sl, is_finite u = true ->
  bpow radix2 (-53) <= B2R u < bpow radix2 (-9) ->
  Fast.dd_sqrt fma u zero = (sh, sl) ->
  is_finite sh = true /\ is_finite sl = true /\ B2R sh = RN (B2R sh + B2R sl) /\
  bpow radix2 (-27) <= B2R sh <= bpow radix2 (-4) /\
  Rabs (B2R sl) <= bpow radix2 (-53) * B2R sh /\
  sqrt (B2R u) <= / 16 /\
  Rabs (B2R sh + B2R sl - sqrt (B2R u)) <= bpow radix2 (-100) * sqrt (B2R u).
Proof.
intros fma u sh sl Fu Hu E.
assert (Z0 : B2R zero = 0) by reflexivity.
assert (Hal : Rabs (B2R zero) <= bpow radix2 (-52) * B2R u).
{ rewrite Z0, Rabs_R0. apply Rmult_le_pos; [apply bpow_ge_0 |].
  pose proof (bpow_gt_0 radix2 (-53)). lra. }
destruct (dd_sqrt_correct fma u zero sh sl Fu eq_refl (u_range u Hu) Hal E)
  as (Fsh & Fsl & Rsh & D).
rewrite Z0, Rplus_0_r in D.
set (S := sqrt (B2R u)) in *.
(* [2^-27 < 5/4 2^-27 <= s <= 3/4 2^-4 < 2^-4], with margins for the
   [2^-100] of [dd_sqrt]. *)
assert (S1 : 5 / 4 * bpow radix2 (-27) <= S).
{ unfold S. rewrite <- (sqrt_square (5 / 4 * bpow radix2 (-27)))
    by (pose proof (bpow_gt_0 radix2 (-27)); lra).
  apply sqrt_le_1_alt. revert Hu. num. lra. }
assert (S2 : S <= 3 / 4 * bpow radix2 (-4)).
{ unfold S. rewrite <- (sqrt_square (3 / 4 * bpow radix2 (-4)))
    by (pose proof (bpow_gt_0 radix2 (-4)); lra).
  apply sqrt_le_1_alt. revert Hu. num. lra. }
pose proof (Rabs_le_inv _ _ D) as D'.
assert (Z1 : bpow radix2 (-27) <= B2R sh + B2R sl) by (revert D' S1; num; lra).
assert (Z2 : B2R sh + B2R sl <= bpow radix2 (-4)) by (revert D' S2; num; lra).
assert (Hsh : bpow radix2 (-27) <= B2R sh <= bpow radix2 (-4)).
{ rewrite Rsh.
  split; [apply rn_ge | apply rn_le]; try (apply format_bpow64; lia); assumption. }
assert (Hsl : Rabs (B2R sl) <= bpow radix2 (-53) * B2R sh).
{ assert (P : bpow radix2 (-1022) <= Rabs (B2R sh + B2R sl)).
  { pose proof (bpow_gt_0 radix2 (-27)).
    rewrite Rabs_pos_eq by lra.
    apply Rle_trans with (bpow radix2 (-27)); [apply bpow_le; lia | exact Z1]. }
  pose proof (rn_rel _ P) as R. rewrite <- Rsh in R.
  replace (B2R sh - (B2R sh + B2R sl)) with (- B2R sl) in R by ring.
  pose proof (bpow_gt_0 radix2 (-27)).
  rewrite Rabs_Ropp, (Rabs_pos_eq (B2R sh)) in R by lra. exact R. }
repeat (split; [assumption |]).
split; [revert S2; num; lra | exact D].
Qed.

(** ** The error budget *)

(** With [T = s + s W] within [2^-78 s] of [a = asinh s], [sh + sl]
    within [2^-100 s] of [s], [-mh + wl] within [2^-71] of [W] and [h + l]
    within [2^-70 sh] of [(sh + sl)(1 - mh + wl)], [h + l] is within
    [(2^-70 + 2^-71 + 2^-78 + 2^-99)(1 + 2^-52) sh] of [a], and so within
    [2^-69 h] as [h >= sh (1 - 2^-10)]. *)
Local Lemma near1_budget :
  forall a s sh sl mh wl h l w t,
  0 <= s -> t = s + s * w ->
  Rabs (a - t) <= bpow radix2 (-78) * s ->
  Rabs (sh + sl - s) <= bpow radix2 (-100) * s ->
  Rabs sl <= bpow radix2 (-53) * sh -> 0 <= sh ->
  0 <= mh <= bpow radix2 (-11) -> Rabs wl <= bpow radix2 (-21) ->
  Rabs (wl - mh - w) <= bpow radix2 (-71) ->
  sh * (1 - bpow radix2 (-10)) <= h ->
  Rabs (h + l - (sh + sl) * (1 - mh + wl)) <= bpow radix2 (-70) * sh ->
  Rabs (a - (h + l)) <= bpow radix2 (-69) * h.
Proof.
intros a s sh sl mh wl h l w t Ps Et Ta D Hsl Psh Hmh Hwl W Bh Es.
apply Rabs_le_inv in Hwl.
(* The two products, with [|1 - mh + wl| <= 2]. *)
assert (P1 : Rabs (s * (wl - mh - w)) <= bpow radix2 (-71) * s).
{ rewrite Rabs_mult, (Rabs_pos_eq s) by exact Ps. rewrite Rmult_comm.
  apply Rmult_le_compat_r; assumption. }
assert (P2 : Rabs ((sh + sl - s) * (1 - mh + wl)) <= bpow radix2 (-100) * s * 2).
{ rewrite Rabs_mult.
  apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact D |].
  apply Rabs_le. revert Hmh Hwl. num. lra. }
apply Rabs_le_inv in Ta. apply Rabs_le_inv in D. apply Rabs_le_inv in Hsl.
apply Rabs_le_inv in P1. apply Rabs_le_inv in P2. apply Rabs_le_inv in Es.
(* [a - (h + l)] is [(a - t) - s (wl - mh - w) - (sh + sl - s)(1 - mh + wl)
   - (h + l - (sh + sl)(1 - mh + wl))]. *)
apply Rabs_le.
revert Ta D Hsl P1 P2 Es Bh Psh Ps. rewrite Et. num. intros. lra.
Qed.

(** [s^17/80 <= 2^-78 s] for [s^2 = u <= 2^-9]. *)
Local Lemma near1_taylor :
  forall s u, 0 <= s -> s * s = u -> 0 <= u <= bpow radix2 (-9) ->
  s ^ 17 / 80 <= bpow radix2 (-78) * s.
Proof.
intros s u Ps Su Hu.
replace (s ^ 17) with (s * u ^ 8) by (rewrite <- Su; ring).
assert (U8 : u ^ 8 <= bpow radix2 (-72)).
{ apply Rle_trans with (bpow radix2 (-9) ^ 8); [apply pow_incr; lra |].
  num. lra. }
assert (P : 0 <= s * u ^ 8 <= s * bpow radix2 (-72)).
{ split; [apply Rmult_le_pos; [lra | apply pow_le; lra] |].
  apply Rmult_le_compat_l; lra. }
revert P. num. lra.
Qed.

(** ** The branch *)

Theorem acosh_near1_correct :
  forall fma x h l k,
  is_finite x = true -> 1 <= B2R x < 1 + bpow radix2 (-8) ->
  DyadicLog.fast_acosh_near1 fma x = Some (h, l, k) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= k <= 1022)%Z /\
  Rabs (Racosh (B2R x) * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-67).
Proof.
intros fma x h l k Fx Hx E.
destruct FastLogReduce.one_R as [F1 E1].
unfold DyadicLog.fast_acosh_near1 in E.
destruct (Model.le x DyadicExp.one) eqn:L; [discriminate E |].
pose proof (le_false x DyadicExp.one Fx F1 L) as X1. rewrite E1 in X1.
destruct (near1_u x Fx (conj X1 (proj2 Hx))) as (Fu & Eu & Hu).
cbv beta iota zeta in E.
set (u := mul DyadicLog.half (sub x DyadicExp.one)) in *.
destruct (Fast.dd_sqrt fma u zero) as [sh sl] eqn:Esq.
destruct (near1_sqrt fma u sh sl Fu Hu Esq) as (Fsh & Fsl & Rsh & Hsh & Hsl & S16 & D).
pose proof (near1_w fma u _ _ _ _ Fu Hu eq_refl eq_refl eq_refl eq_refl)
  as (Fmh & Fwl & Hmh & Hwl & W).
match type of Hmh with _ <= B2R ?m <= _ => set (mh := m) in * end.
match type of E with
| context [Fast.fast_two_sum sh ?t] => destruct (Fast.fast_two_sum sh t) as [a b] eqn:Eab
end.
match type of E with
| context [Fast.fast_two_sum a ?t] => destruct (Fast.fast_two_sum a t) as [h0 l0] eqn:Ehl
end.
destruct (near1_sum fma sh sl _ _ a b h0 l0 Fsh Fsl Fmh Fwl Rsh Hsh Hmh Hwl Eab Ehl)
  as (Fh0 & Fl0 & Rh0 & Bh0 & Es).
assert (Hh0 : bpow radix2 (-1021) <= B2R h0 < 2) by (revert Hsh Bh0; num; lra).
pose proof (normalize_correct h0 l0 Fh0 Fl0 Rh0 Hh0) as N.
destruct (Fast.normalize h0 l0) as [[h1 l1] k1] eqn:EN.
cbv beta iota in E. injection E as <- <- <-.
destruct N as (Fh1 & Fl1 & Hk & Eh1 & El1 & Bk & Rh1).
do 3 (split; [assumption |]). split; [lia |].
(* [acosh x = 2 asinh s] with [s = sqrt u]. *)
set (S := sqrt (B2R u)) in *.
assert (PS : 0 <= S) by apply sqrt_pos.
assert (PU : 0 <= B2R u) by (pose proof (bpow_gt_0 radix2 (-53)); lra).
assert (SS : S * S = B2R u) by (apply sqrt_sqrt; exact PU).
assert (AC : Racosh (B2R x) = 2 * arcsinh S).
{ pose proof (acosh_asinh_half (B2R x - 1) ltac:(lra)) as A.
  rewrite <- Eu in A. replace (1 + (B2R x - 1)) with (B2R x) in A by ring. exact A. }
(* [asinh s] is within [2^-78 s] of its Taylor polynomial [s (1 + W(u))]. *)
pose proof (asinh_taylor15 S (conj PS S16)) as T.
pose proof (near1_taylor S (B2R u) PS SS (conj PU (Rlt_le _ _ (proj2 Hu)))) as T17.
assert (T' : Rabs (arcsinh S - (S - S ^ 3 / 6 + 3 * S ^ 5 / 40 - 5 * S ^ 7 / 112
  + 35 * S ^ 9 / 1152 - 63 * S ^ 11 / 2816 + 231 * S ^ 13 / 13312 - 143 * S ^ 15 / 10240))
  <= bpow radix2 (-78) * S) by lra.
assert (Hmh' : 0 <= B2R mh <= bpow radix2 (-11))
  by (pose proof (bpow_gt_0 radix2 (-57)); lra).
assert (Psh : 0 <= B2R sh) by (pose proof (bpow_gt_0 radix2 (-27)); lra).
assert (B0 : Rabs (arcsinh S - (B2R h0 + B2R l0)) <= bpow radix2 (-69) * B2R h0).
{ match type of T' with Rabs (_ - ?tp) <= _ =>
  match type of W with Rabs (_ - _ - ?wp) <= _ =>
    assert (ET : tp = S + S * wp) by (rewrite <- SS; field);
    exact (near1_budget _ _ _ _ _ _ _ _ _ _ PS ET T' D Hsl Psh Hmh' Hwl W (proj1 Bh0) Es)
  end end. }
(* Scaled by [2^-(k' + 1)], with [h 2^-k' < 2]. *)
rewrite Eh1, El1, AC.
set (B := bpow radix2 (- k1)).
assert (PB : 0 < B) by apply bpow_gt_0.
replace (bpow radix2 (- (k1 + 1))) with (B * / 2)
  by (unfold B; replace (- (k1 + 1))%Z with (- k1 + -1)%Z by ring;
      rewrite bpow_plus; reflexivity).
replace (2 * arcsinh S * (B * / 2) - (B2R h0 * B + B2R l0 * B))
  with ((arcsinh S - (B2R h0 + B2R l0)) * B) by field.
rewrite Rabs_mult, (Rabs_pos_eq B) by lra.
assert (HB : B2R h0 * B < 2).
{ assert (EB : bpow radix2 (k1 + 1) * B = 2)
    by (unfold B; rewrite <- bpow_plus; replace (k1 + 1 + - k1)%Z with 1%Z by ring;
        reflexivity).
  rewrite <- EB. apply Rmult_lt_compat_r; [exact PB | exact (proj2 Bk)]. }
apply Rle_trans with (bpow radix2 (-69) * B2R h0 * B).
{ apply Rmult_le_compat_r; lra. }
rewrite Rmult_assoc.
apply Rle_trans with (bpow radix2 (-69) * 2).
{ apply Rmult_le_compat_l; [apply bpow_ge_0 | lra]. }
num. lra.
Qed.

(** The square in [dd_sqrt], [ml] and [pe] are exact products, so
    [HAS_FMA] does not change them. *)
Theorem acosh_near1_fma :
  forall x,
  is_finite x = true -> 1 <= B2R x < 1 + bpow radix2 (-8) ->
  DyadicLog.fast_acosh_near1 true x = DyadicLog.fast_acosh_near1 false x.
Proof.
intros x Fx Hx.
destruct FastLogReduce.one_R as [F1 E1].
unfold DyadicLog.fast_acosh_near1.
destruct (Model.le x DyadicExp.one) eqn:L; [reflexivity |].
pose proof (le_false x DyadicExp.one Fx F1 L) as X1. rewrite E1 in X1.
destruct (near1_u x Fx (conj X1 (proj2 Hx))) as (Fu & _ & Hu).
cbv beta iota zeta.
set (u := mul DyadicLog.half (sub x DyadicExp.one)) in *.
rewrite (dd_sqrt_fma u zero Fu eq_refl (u_range u Hu)).
destruct (Fast.dd_sqrt false u zero) as [sh sl] eqn:Esq.
destruct (near1_sqrt false u sh sl Fu Hu Esq) as (Fsh & _ & _ & Hsh & _).
pose proof (near1_w false u _ _ _ _ Fu Hu eq_refl eq_refl eq_refl eq_refl)
  as (Fmh & _ & Hmh & _).
cbv beta iota.
rewrite (near1_ml_fma u Fu Hu), (near1_pe_fma sh _ Fsh Fmh Hsh Hmh).
reflexivity.
Qed.

