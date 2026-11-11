(** * The product y ln x of the fast path of [pow]

    [DyadicPow.pow_t] of [Model.v] computes [t = y ln x] as [th + tl],
    with [(lh, ll) = DyadicLog.ln_acc x] ([FastPowLn.v]), [th = RN(y lh)]
    and [tl] the error of that product (TwoProduct, [TwoProduct.v]) plus
    [RN(y ll)], for [DyadicExp.fast_exp], which returns [None] unless
    [|th| <= 709], and for [DyadicExp.fast_exp_edge] beyond.

    [fast_pow_mul] covers [|y ln x| >= 2^-60] and [|th| <= 709]: then [x
    <> 1], so [|ln x| >= 2^-54] ([FastLogNorm.ln_f64_ne1]) and [|y| <
    2^65], and [2^-61 <= |th|], so that [y lh] is exact as [th] plus its
    error with and without an FMA; [|tl| <= 2^-40], as [fast_exp] needs;
    and [th + tl] is within [3/4 2^-69] of [y ln x]: [17/16 2^-79 |y ln
    x|] from [ln_acc], with [|y ln x| <= 709.001], plus the two roundings
    of [tl], below [2^-92]. [fast_pow_mul_wide] is the same for [|th| <=
    752], with [|tl| <= 3 2^-42], as [fast_exp_edge] needs, and [13/16
    2^-69] in place of [3/4 2^-69]. [fast_pow_mul_one] covers [x = 1]:
    [ln_acc] returns zeros there, and so do the product and its error,
    for [|y| <= 2^900]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Relative.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct FastRound FastExpErr
  FastLogNorm FastPowLn.
From Inari Require MulRuTiny FastLogFin FastExp.

Open Scope R_scope.

(** Rounding to nearest of an [x] of at least [2^-1022] in magnitude moves
    it by at most [2^-53 |x|] (a copy of the [Local] lemma of
    [FastSinhHorner.v]). *)
Local Lemma rn_rel :
  forall x, bpow radix2 (-1022) <= Rabs x -> Rabs (RN x - x) <= bpow radix2 (-53) * Rabs x.
Proof.
intros x Hx.
assert (H : Rabs (RN x - x) <= / 2 * bpow radix2 (- 53 + 1) * Rabs x)
  by exact (relative_error_N_FLT radix2 (-1074) 53 eq_refl (fun z => negb (Z.even z)) x Hx).
change (- 53 + 1)%Z with (-52)%Z in H.
assert (E : / 2 * bpow radix2 (-52) = bpow radix2 (-53))
  by (cbn [bpow radix_val radix2]; lra).
rewrite E in H. exact H.
Qed.

(** [|a b| = |a| |b|] with [|b|] bounded below by [c |d|] gives [|a b| >=
    c |a d|]. *)
Local Lemma mul_ge :
  forall a b c d, 0 <= c -> c * Rabs d <= Rabs b -> c * Rabs (a * d) <= Rabs (a * b).
Proof.
intros a b c d Hc H.
rewrite !Rabs_mult.
pose proof (Rabs_pos a).
replace (c * (Rabs a * Rabs d)) with (Rabs a * (c * Rabs d)) by ring.
apply Rmult_le_compat_l; assumption.
Qed.

Local Lemma tri3 : forall a b c, Rabs (a - b - c) <= Rabs a + Rabs b + Rabs c.
Proof.
intros a b c.
replace (a - b - c) with (a + - b + - c) by ring.
pose proof (Rabs_triang (a + - b) (- c)) as T1. pose proof (Rabs_triang a (- b)) as T2.
rewrite Rabs_Ropp in T1, T2. lra.
Qed.

(** The part [fast_pow_mul] and [fast_pow_mul_wide] share, for [|th| <=
    752]: [|tl| <= 2^-41 + 2^-94]; [(1 - 17/16 2^-79) |y ln x| <= |th| +
    2^-43 + 2^-42], which bounds [|y ln x|] by about [|th|]; and the
    error of [th + tl] is at most [17/16 2^-79 |y ln x|] from [ln_acc]
    plus [2^-95] and [2^-94] for the roundings of [RN(y ll)] and of
    [tl]. *)
Local Lemma fast_pow_mul_core :
  forall fma x y,
  is_finite x = true -> 0 < B2R x -> is_finite y = true ->
  bpow radix2 (-60) <= Rabs (B2R y * ln (B2R x)) ->
  let '(lh, ll) := DyadicLog.ln_acc fma x in
  let th := mul y lh in
  is_finite th = true -> Rabs (B2R th) <= 752 ->
  let tl := add (Generic.two_prod_err fma y lh th) (mul y ll) in
  is_finite tl = true /\ Rabs (B2R tl) <= bpow radix2 (-41) + bpow radix2 (-94) /\
  (1 - 17 / 16 * bpow radix2 (-79)) * Rabs (B2R y * ln (B2R x))
    <= Rabs (B2R th) + bpow radix2 (-43) + bpow radix2 (-42) /\
  Rabs (B2R y * ln (B2R x) - (B2R th + B2R tl))
    <= 17 / 16 * bpow radix2 (-79) * Rabs (B2R y * ln (B2R x))
       + bpow radix2 (-95) + bpow radix2 (-94) /\
  Generic.two_prod_err true y lh th = Generic.two_prod_err false y lh th.
Proof.
intros fma x y Fx Px Fy Hyl.
(* [x <> 1], as [ln 1 = 0], so [|ln x| >= 2^-54]. *)
assert (X1 : B2R x <> 1).
{ intros E. rewrite E, ln_1, Rmult_0_r, Rabs_R0 in Hyl.
  pose proof (bpow_gt_0 radix2 (-60)). lra. }
pose proof (ln_f64_ne1 x Fx Px X1) as HL54.
pose proof (ln_acc_correct fma x Fx Px) as HA.
destruct (DyadicLog.ln_acc fma x) as [lh ll].
cbv beta iota in HA |- *.
destruct HA as (Flh & Fll & Elh & Blh & Err).
cbv zeta. intros Fth Bth.
set (L := ln (B2R x)) in *.
set (S := B2R lh + B2R ll) in *.
change (bpow radix2 (-79)) with (/ 604462909807314587353088) in Err.
change (bpow radix2 (-54)) with (/ 18014398509481984) in HL54.
(* [|S|] is [|ln x|] within the relative bound of [ln_acc]. *)
assert (HS : (1 - 17 / 16 / 604462909807314587353088) * Rabs L <= Rabs S <=
             (1 + 17 / 16 / 604462909807314587353088) * Rabs L).
{ pose proof (Rabs_triang_inv L S). pose proof (Rabs_triang_inv S L).
  rewrite (Rabs_minus_sym S L) in *. split; lra. }
(* [ll] is the rounding error of [lh = RN(S)], at most [2^-53 |S|], so
   at most [2^-52 |lh|]. *)
assert (Hll : Rabs (B2R ll) <= / 9007199254740992 * Rabs S).
{ replace (B2R ll) with (- (RN S - S)) by (rewrite <- Elh; unfold S; ring).
  rewrite Rabs_Ropp.
  change (/ 9007199254740992) with (bpow radix2 (-53)).
  apply rn_rel.
  apply Rle_trans with (bpow radix2 (-55)); [apply bpow_le; lia|].
  change (bpow radix2 (-55)) with (/ 36028797018963968). lra. }
assert (Hll2 : Rabs (B2R ll) <= / 4503599627370496 * Rabs (B2R lh)).
{ pose proof (Rabs_triang (B2R lh) (B2R ll)) as T. fold S in T.
  pose proof (Rabs_pos (B2R lh)). lra. }
assert (Hlh : (1 - / 4503599627370496) * Rabs S <= Rabs (B2R lh)).
{ replace (B2R lh) with (S - B2R ll) by (unfold S; ring).
  pose proof (Rabs_triang_inv S (B2R ll)). pose proof (Rabs_pos S). lra. }
(* [|lh| >= k |ln x|] for [k = (1 - 2^-52) (1 - 17/16 2^-79)]. *)
set (k := (1 - / 4503599627370496) * (1 - 17 / 16 / 604462909807314587353088)).
assert (Hk : k * Rabs L <= Rabs (B2R lh)).
{ unfold k. pose proof (Rabs_pos L). lra. }
(* [th = RN(y lh)] with [|y lh| < 2^10]. *)
pose proof (mul_B2R y lh Fy Flh Fth) as Eth.
assert (Hp10 : Rabs (B2R y * B2R lh) < bpow radix2 10).
{ apply MulRuTiny.abs_lt_of_RN_lt; [lia|]. rewrite <- Eth.
  change (bpow radix2 10) with 1024. lra. }
change (bpow radix2 10) with 1024 in Hp10.
(* [|y| < 2^65], as [|lh| > 2^-55]. *)
assert (Hy65 : Rabs (B2R y) < bpow radix2 65).
{ change (bpow radix2 65) with 36893488147419103232.
  assert (H55 : / 36028797018963968 <= Rabs (B2R lh)).
  { apply Rle_trans with (2 := Hk). unfold k. lra. }
  rewrite Rabs_mult in Hp10. pose proof (Rabs_pos (B2R y)).
  assert (Rabs (B2R y) * / 36028797018963968 <= Rabs (B2R y) * Rabs (B2R lh))
    by (apply Rmult_le_compat_l; assumption).
  lra. }
(* [|th| >= 2^-61], as [|y lh| >= k |y ln x| >= k 2^-60 > 2^-61]. *)
assert (Hth61 : bpow radix2 (-61) <= Rabs (B2R (mul y lh))).
{ rewrite Eth. apply abs_round_ge_generic; [typeclasses eauto .. | |].
  - apply generic_format_FLT_bpow; [typeclasses eauto .. | lia].
  - pose proof (mul_ge (B2R y) (B2R lh) k L ltac:(unfold k; lra) Hk) as H.
    change (bpow radix2 (-60)) with (/ 1152921504606846976) in Hyl.
    change (bpow radix2 (-61)) with (/ 2305843009213693952).
    unfold k in H. lra. }
(* The exponents: [th] in [-61, 9], [y] at most 64, [lh] at most 9. *)
assert (E1 : (-61 <= Generic.exponent (mul y lh))%Z)
  by (apply MulRuTiny.exponent_ge; assumption).
assert (E2 : (Generic.exponent (mul y lh) < 10)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fth | lia |].
  change (bpow radix2 10) with 1024. lra. }
assert (E3 : (Generic.exponent y < 65)%Z)
  by (apply MulRuTiny.exponent_lt; [exact Fy | lia | exact Hy65]).
assert (E4 : (Generic.exponent lh < 10)%Z).
{ apply MulRuTiny.exponent_lt; [exact Flh | lia |].
  change (bpow radix2 10) with 1024. lra. }
assert (Ex : forall f, Generic.two_prod_is_exact f y lh (mul y lh) = true).
{ intros f. unfold Generic.two_prod_is_exact.
  destruct f; cbv beta iota zeta; repeat (apply andb_true_intro; split); apply Z.leb_le; lia. }
(* The error of the product is exact, at most [2^-43]. *)
destruct (two_prod_err_correct fma y lh Fy Flh (Ex fma)) as (_ & _ & _ & Fe & Ee).
set (er := Generic.two_prod_err fma y lh (mul y lh)) in *.
assert (He : Rabs (B2R er) <= / 8796093022208).
{ rewrite Ee, Eth.
  replace (B2R y * B2R lh - RN (B2R y * B2R lh)) with (- (RN (B2R y * B2R lh) - B2R y * B2R lh))
    by ring.
  rewrite Rabs_Ropp.
  change (/ 8796093022208) with (bpow radix2 (10 - 53)).
  apply FastExp.fe_RN_err; [lia|]. change (bpow radix2 10) with 1024. lra. }
(* [m = RN(y ll)], with [|y ll| <= 2^-52 |y lh| < 2^-42]. *)
assert (Hyll : Rabs (B2R y * B2R ll) <= / 4398046511104).
{ rewrite Rabs_mult. rewrite Rabs_mult in Hp10. pose proof (Rabs_pos (B2R y)).
  assert (Rabs (B2R y) * Rabs (B2R ll) <= Rabs (B2R y) * (/ 4503599627370496 * Rabs (B2R lh)))
    by (apply Rmult_le_compat_l; assumption).
  nra. }
pose proof FastLogFin.fl_max as HM.
destruct (mul_below_max y ll Fy Fll ltac:(lra)) as (Fm & Em & _).
assert (Hm : Rabs (B2R (mul y ll) - B2R y * B2R ll) <= / 39614081257132168796771975168).
{ rewrite Em. change (/ 39614081257132168796771975168) with (bpow radix2 (-42 - 53)).
  apply FastExp.fe_RN_err; [lia|]. change (bpow radix2 (-42)) with (/ 4398046511104). lra. }
(* [tl = RN(er + m)], with [|er + m| < 2^-41]. *)
assert (Hs41 : Rabs (B2R er + B2R (mul y ll)) <= / 2199023255552).
{ pose proof (Rabs_triang (B2R er) (B2R (mul y ll))).
  pose proof (Rabs_triang_inv (B2R (mul y ll)) (B2R y * B2R ll)). lra. }
destruct (add_below_max er (mul y ll) Fe Fm ltac:(lra)) as (Ft & Et & _).
assert (Ht : Rabs (B2R (add er (mul y ll)) - (B2R er + B2R (mul y ll)))
             <= / 19807040628566084398385987584).
{ rewrite Et. change (/ 19807040628566084398385987584) with (bpow radix2 (-41 - 53)).
  apply FastExp.fe_RN_err; [lia|]. change (bpow radix2 (-41)) with (/ 2199023255552). lra. }
split; [exact Ft|]. split.
{ pose proof (Rabs_triang_inv (B2R (add er (mul y ll))) (B2R er + B2R (mul y ll))).
  change (bpow radix2 (-41)) with (/ 2199023255552).
  change (bpow radix2 (-94)) with (/ 19807040628566084398385987584). lra. }
split.
(* [(1 - 17/16 2^-79) |y ln x| <= |y S| <= |y lh| + |y ll|], with [|y lh|
   <= |th| + |er| <= |th| + 2^-43] and [|y ll| <= 2^-42]. *)
{ assert (Hyh : Rabs (B2R y * B2R lh) <= Rabs (B2R (mul y lh)) + / 8796093022208).
  { rewrite Ee in He. pose proof (Rabs_triang_inv (B2R y * B2R lh) (B2R (mul y lh))). lra. }
  assert (HyS : Rabs (B2R y * S) <= Rabs (B2R y * B2R lh) + Rabs (B2R y * B2R ll))
    by (unfold S; rewrite Rmult_plus_distr_l; apply Rabs_triang).
  pose proof (mul_ge (B2R y) S (1 - 17 / 16 / 604462909807314587353088) L ltac:(lra)
    (proj1 HS)) as H.
  change (bpow radix2 (-79)) with (/ 604462909807314587353088).
  change (bpow radix2 (-43)) with (/ 8796093022208).
  change (bpow radix2 (-42)) with (/ 4398046511104).
  lra. }
split.
(* The error: [y ln x - (th + tl) = y (ln x - S) - (m - y ll) - (tl - (er +
   m))], as [th + er = y lh]. *)
- replace (B2R y * L - (B2R (mul y lh) + B2R (add er (mul y ll))))
    with (B2R y * (L - S) - (B2R (mul y ll) - B2R y * B2R ll)
          - (B2R (add er (mul y ll)) - (B2R er + B2R (mul y ll))))
    by (unfold S; rewrite Ee; ring).
  assert (Hd : Rabs (B2R y * (L - S)) <= 17 / 16 / 604462909807314587353088 * Rabs (B2R y * L)).
  { rewrite !Rabs_mult. pose proof (Rabs_pos (B2R y)).
    replace (17 / 16 / 604462909807314587353088 * (Rabs (B2R y) * Rabs L))
      with (Rabs (B2R y) * (17 / 16 * / 604462909807314587353088 * Rabs L)) by field.
    apply Rmult_le_compat_l; assumption. }
  pose proof (tri3 (B2R y * (L - S)) (B2R (mul y ll) - B2R y * B2R ll)
    (B2R (add er (mul y ll)) - (B2R er + B2R (mul y ll)))).
  change (bpow radix2 (-79)) with (/ 604462909807314587353088).
  change (bpow radix2 (-95)) with (/ 39614081257132168796771975168).
  change (bpow radix2 (-94)) with (/ 19807040628566084398385987584).
  lra.
- exact (two_prod_err_fma_eq y lh Fy Flh (Ex true) (Ex false)).
Qed.

Theorem fast_pow_mul :
  forall fma x y,
  is_finite x = true -> 0 < B2R x -> is_finite y = true ->
  bpow radix2 (-60) <= Rabs (B2R y * ln (B2R x)) ->
  let '(lh, ll) := DyadicLog.ln_acc fma x in
  let th := mul y lh in
  is_finite th = true -> Rabs (B2R th) <= 709 ->
  let tl := add (Generic.two_prod_err fma y lh th) (mul y ll) in
  is_finite tl = true /\ Rabs (B2R tl) <= bpow radix2 (-40) /\
  Rabs (B2R y * ln (B2R x) - (B2R th + B2R tl)) <= 3 / 4 * bpow radix2 (-69) /\
  Generic.two_prod_err true y lh th = Generic.two_prod_err false y lh th.
Proof.
intros fma x y Fx Px Fy Hyl.
pose proof (fast_pow_mul_core fma x y Fx Px Fy Hyl) as C.
destruct (DyadicLog.ln_acc fma x) as [lh ll].
cbv beta iota zeta in C |- *. intros Fth Bth.
assert (B752 : Rabs (B2R (mul y lh)) <= 752) by lra.
destruct (C Fth B752) as (Ft & Bt & HP & Err & Eq).
change (bpow radix2 (-41)) with (/ 2199023255552) in Bt.
change (bpow radix2 (-94)) with (/ 19807040628566084398385987584) in Bt, Err.
change (bpow radix2 (-79)) with (/ 604462909807314587353088) in HP, Err.
change (bpow radix2 (-43)) with (/ 8796093022208) in HP.
change (bpow radix2 (-42)) with (/ 4398046511104) in HP.
change (bpow radix2 (-95)) with (/ 39614081257132168796771975168) in Err.
split; [exact Ft|]. split.
{ change (bpow radix2 (-40)) with (/ 1099511627776). lra. }
split; [|exact Eq].
(* [|th| <= 709] gives [|y ln x| <= 709.001], so the error is at most
   [17/16 2^-79 709.001 + 2^-95 + 2^-94 <= 3/4 2^-69]. *)
change (bpow radix2 (-69)) with (/ 590295810358705651712).
lra.
Qed.

Theorem fast_pow_mul_wide :
  forall fma x y,
  is_finite x = true -> 0 < B2R x -> is_finite y = true ->
  bpow radix2 (-60) <= Rabs (B2R y * ln (B2R x)) ->
  let '(lh, ll) := DyadicLog.ln_acc fma x in
  let th := mul y lh in
  is_finite th = true -> Rabs (B2R th) <= 752 ->
  let tl := add (Generic.two_prod_err fma y lh th) (mul y ll) in
  is_finite tl = true /\ Rabs (B2R tl) <= 3 * bpow radix2 (-42) /\
  Rabs (B2R y * ln (B2R x) - (B2R th + B2R tl)) <= 13 / 16 * bpow radix2 (-69) /\
  Generic.two_prod_err true y lh th = Generic.two_prod_err false y lh th.
Proof.
intros fma x y Fx Px Fy Hyl.
pose proof (fast_pow_mul_core fma x y Fx Px Fy Hyl) as C.
destruct (DyadicLog.ln_acc fma x) as [lh ll].
cbv beta iota zeta in C |- *. intros Fth Bth.
destruct (C Fth Bth) as (Ft & Bt & HP & Err & Eq).
change (bpow radix2 (-41)) with (/ 2199023255552) in Bt.
change (bpow radix2 (-94)) with (/ 19807040628566084398385987584) in Bt, Err.
change (bpow radix2 (-79)) with (/ 604462909807314587353088) in HP, Err.
change (bpow radix2 (-43)) with (/ 8796093022208) in HP.
change (bpow radix2 (-42)) with (/ 4398046511104) in HP.
change (bpow radix2 (-95)) with (/ 39614081257132168796771975168) in Err.
split; [exact Ft|]. split.
{ change (bpow radix2 (-42)) with (/ 4398046511104). lra. }
split; [|exact Eq].
(* [|th| <= 752] gives [|y ln x| <= 752.001], so the error is at most
   [17/16 2^-79 752.001 + 2^-95 + 2^-94 <= 13/16 2^-69] (about [0.7803
   2^-69]). *)
change (bpow radix2 (-69)) with (/ 590295810358705651712).
lra.
Qed.

(** ** [x = 1] *)

(** [a] is a zero of either sign. *)
Local Definition zr (a : f64) : Prop := exists s, a = B754_zero s.

Local Lemma zr_mul_r : forall a b, is_finite a = true -> zr b -> zr (mul a b).
Proof. intros a b Fa [s ->]. destruct a as [sa|sa| |sa ma ea Ha]; try discriminate;
  eexists; reflexivity. Qed.

Local Lemma zr_mul_l : forall a b, zr a -> is_finite b = true -> zr (mul a b).
Proof. intros a b [s ->] Fb. destruct b as [sb|sb| |sb mb eb Hb]; try discriminate;
  eexists; reflexivity. Qed.

Local Lemma zr_add : forall a b, zr a -> zr b -> zr (add a b).
Proof. intros a b [s ->] [t ->]. destruct s, t; eexists; reflexivity. Qed.

Local Lemma zr_sub : forall a b, zr a -> zr b -> zr (sub a b).
Proof. intros a b [s ->] [t ->]. destruct s, t; eexists; reflexivity. Qed.

Local Lemma zr_mul_add :
  forall a b c, is_finite a = true -> zr b -> zr c -> zr (mul_add a b c).
Proof.
intros a b c Fa [s ->] [t ->].
destruct a as [sa|sa| |sa ma ea Ha]; try discriminate; destruct s, t;
  try (destruct sa); eexists; reflexivity.
Qed.

Theorem fast_pow_mul_one :
  forall fma x y,
  is_finite x = true -> B2R x = 1 -> is_finite y = true -> Rabs (B2R y) <= bpow radix2 900 ->
  exists sh sl, DyadicPow.pow_t fma x y = (B754_zero sh, B754_zero sl).
Proof.
intros fma x y Fx Ex Fy Hy.
(* [x] is the literal [1.0]. *)
assert (F1 : is_finite DyadicExp.one = true) by (vm_compute; reflexivity).
assert (E1 : B2R DyadicExp.one = 1).
{ rewrite <- SF2R_B2SF.
  replace (B2SF DyadicExp.one) with (SpecFloat.S754_finite false 4503599627370496 (-52))
    by (vm_compute; reflexivity).
  unfold SF2R, F2R. cbn [Fnum Fexp SpecFloat.cond_Zopp].
  change (bpow radix2 (-52)) with (/ 4503599627370496). lra. }
assert (X : x = DyadicExp.one).
{ apply B2R_inj; [| vm_compute; reflexivity | lra].
  destruct x as [s|s| |s m e H]; try discriminate; [|reflexivity].
  cbn in Ex. lra. }
subst x.
(* [ln_acc] of [1.0] is [(+0, +0)], with and without an FMA. *)
assert (L1 : DyadicLog.ln_acc fma DyadicExp.one = (B754_zero false, B754_zero false))
  by (destruct fma; vm_compute; reflexivity).
unfold DyadicPow.pow_t. rewrite L1. cbv beta iota zeta.
assert (Z0 : zr (B754_zero false)) by (exists false; reflexivity).
assert (Zt : zr (mul y (B754_zero false))) by (apply zr_mul_r; assumption).
(* The error of the product [y 0] is a zero: with an FMA, [y 0 - th];
   without, the sum of [-th] and the four products of [Generic.split]'s
   halves of [y] and of [+0] (which splits into [(+0, +0)]), as [y]'s
   halves are finite for [|y| < 2^996]. *)
assert (Ze : zr (Generic.two_prod_err fma y (B754_zero false) (mul y (B754_zero false)))).
{ destruct fma.
  - unfold Generic.two_prod_err. cbv beta iota.
    apply zr_mul_add; [exact Fy | exact Z0 |].
    destruct Zt as [s Hs]. rewrite Hs. exists (negb s). reflexivity.
  - assert (Hy996 : Rabs (B2R y) < bpow radix2 996)
      by (apply Rle_lt_trans with (1 := Hy); apply bpow_lt; lia).
    pose proof (split_correct y Fy Hy996) as Hs.
    unfold Generic.two_prod_err.
    destruct (Generic.split y) as [yh yl].
    destruct Hs as (Fyh & Fyl & _).
    replace (Generic.split (B754_zero false))
      with ((B754_zero false : f64), (B754_zero false : f64)) by (vm_compute; reflexivity).
    cbv beta iota.
    apply zr_add; [apply zr_add; [apply zr_add|] |].
    + apply zr_sub; [apply zr_mul_r; assumption | exact Zt].
    + apply zr_mul_r; assumption.
    + apply zr_mul_r; assumption.
    + apply zr_mul_r; assumption. }
destruct (zr_add _ _ Ze (zr_mul_r y _ Fy Z0)) as [sl Hl].
destruct Zt as [sh Hh].
exists sh, sl. rewrite Hl, Hh. reflexivity.
Qed.
