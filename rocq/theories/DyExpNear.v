(** * The exponential and hyperbolic functions of the dyadic kernel rounded to nearest

    [exp_near_with ziv_near_strict] and the others of [DyadicExp] return,
    where they return, their function at a finite [x] rounded to nearest
    as [near_round] says: the loop by [ziv_near_strict_correct] and the
    enclosures of [DyExp.v] and [DyHyp.v], and the rules before it by the
    cells of [NearCells.v] and the bounds of [DyExpRules.v],
    [DyHypRules.v], [DySinhTiny.v] and [DyTanhTiny.v]. Where they return
    with [ziv_near_strict], they return the same with [Dyadic.ziv_near]
    ([exp_near_strict] and the others). *)

From Stdlib Require Import ZArith Reals Lra Lia List QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary ExpReal DyRound DyConv DyOps DyDriver
  DyGrow DyConst DyExpCore DyExpRules DyHypRules DySinhTiny DyTanhTiny DyExp DyHyp
  NearF64 NearCells DyDriverNear ExpSeries FastExp FastHyp.
From Inari Require ConstTight.

Open Scope Z_scope.

(** Where [ziv_near_strict] returns, [Dyadic.ziv_near] returns the same:
    the goal [<body with ziv_near_strict> = Some v -> <body with
    Dyadic.ziv_near> = Some v] of a function of this file, split at its
    guards, which name neither driver, as [dir_strict] of [DyExp.v]. *)
Local Ltac near_strict :=
  repeat match goal with
  | |- (if ?c then _ else _) = Some _ -> _ => destruct c; [exact (fun h => h)|]
  | |- match ?c with Some _ => _ | None => _ end = Some _ -> _ =>
      destruct c; [exact (fun h => h)|]
  end;
  apply ziv_near_strict_ziv.

(** [lit w H] adds [H : B2R w = n * / d] for the literal [w], with [n] and
    [d] numerals that [lra] reads, as in [DyExpRules.v]. *)
Local Ltac lit w H :=
  let q := eval vm_compute in (ConstTight.B2Q w) in
  assert (H : B2R w = Q2R q) by (apply lit_R; vm_compute; reflexivity);
  unfold Q2R in H; cbn [Qnum Qden] in H.

Local Open Scope R_scope.

(** ** Bounds *)

(** For [|y| < 2^-54], [1 - 2^-54 < 1 + y <= exp y], and for [y > 0],
    [exp y * (1 - y) < exp y * exp (-y) = 1], so [exp y < 1 + y exp y <
    1 + 2^-53], as [exp_near_one] of [DyExpRules.v] shows. *)
Local Lemma exp_tiny_near :
  forall y, Rabs y < bpow radix2 (-54) -> 1 - bpow radix2 (-54) <= exp y <= 1 + bpow radix2 (-53).
Proof.
intros y Hy.
assert (Hb : bpow radix2 (-53) = 2 * bpow radix2 (-54) /\ 0 < bpow radix2 (-54) < 1 / 1000)
  by (cbn [bpow radix_val radix2]; lra).
apply Rabs_def2 in Hy as [Hy1 Hy2].
pose proof (exp_ineq1_le y) as Hl.
split; [lra|].
destruct (Rlt_or_le 0 y) as [Hp|Hn].
- assert (Hm : 1 + - y < exp (- y)) by (apply exp_ineq1; lra).
  assert (Hpr : exp y * exp (- y) = 1)
    by (rewrite <- exp_plus, Rplus_opp_r; exact exp_0).
  assert (He : 0 < exp y) by apply exp_pos.
  assert (H1 : exp y * (1 - y) < 1) by (rewrite <- Hpr; apply Rmult_lt_compat_l; lra).
  assert (H2 : exp y < 2) by nra.
  assert (H3 : exp y * y < 2 * bpow radix2 (-54)) by nra.
  lra.
- assert (Hu : exp y <= exp 0) by (apply exp_inc; lra).
  rewrite exp_0 in Hu. lra.
Qed.

(** For [0 < y < 2^-27], [y < sinh y < y + y 2^-54]: the proof of
    [sinh_tiny_real] of [DySinhTiny.v] bounds [sinh y] above by [y +
    y^3/2], and [y^2 < 2^-54]. *)
Local Lemma sinh_tiny_bound :
  forall y, 0 < y < bpow radix2 (-27) -> Rabs (sinh y - y) <= y * bpow radix2 (-54).
Proof.
intros y Hy.
assert (Hb : 0 < bpow radix2 (-27) < 1 / 1000) by (cbn [bpow radix_val radix2]; lra).
assert (Hbb : bpow radix2 (-27) * bpow radix2 (-27) = bpow radix2 (-54))
  by (rewrite <- bpow_plus; reflexivity).
assert (Hy1 : 0 <= y <= 1) by lra.
set (e := exp y). set (f := exp (- y)).
assert (Hef : e * f = 1) by (unfold e, f; rewrite <- exp_plus, Rplus_opp_r; exact exp_0).
assert (He0 : 0 < e) by apply exp_pos.
assert (Hf0 : 0 < f) by apply exp_pos.
destruct (exp_alt_bounds y 1 Hy1) as [Hfl Hfu]. fold f in Hfl, Hfu.
replace (sum_f_R0 (tg_alt (exp_tg y)) (S (2 * 1))) with (1 - y + y^2/2 - y^3/6) in Hfl
  by (unfold tg_alt, exp_tg; cbn; field).
replace (sum_f_R0 (tg_alt (exp_tg y)) (2 * 1)) with (1 - y + y^2/2) in Hfu
  by (unfold tg_alt, exp_tg; cbn; field).
assert (Hel : sum_f_R0 (fun i => / INR (fact i) * y ^ i) 3 <= e).
{ apply sum_incr.
  - exact (proj2_sig (exist_exp y)).
  - intros n. apply Rmult_le_pos;
      [left; apply Rinv_0_lt_compat, INR_fact_lt_0 | apply pow_le; lra]. }
replace (sum_f_R0 (fun i => / INR (fact i) * y ^ i) 3) with (1 + y + y^2/2 + y^3/6) in Hel
  by (cbn; field).
assert (Hy3 : 0 < y^3) by (apply pow_lt; lra).
assert (Hyy : y * y < bpow radix2 (-54)).
{ rewrite <- Hbb. apply Rmult_le_0_lt_compat; lra. }
assert (Hyyy : y * (y * y) <= y * bpow radix2 (-54))
  by (apply Rmult_le_compat_l; lra).
(* [exp y < 1 + y + y^2/2 + 5 y^3/6]. *)
assert (Hp : 0 < 2/3 - 3/4 * y + 1/3 * y^2 - 5/36 * y^3).
{ assert (0 <= y^2) by (apply pow_le; lra).
  assert (y^3 <= y) by (replace (y^3) with (y * y^2) by ring; nra).
  lra. }
assert (Hcb : 1 < (1 + y + y^2/2 + 5/6 * y^3) * (1 - y + y^2/2 - y^3/6)).
{ assert (0 < y^3 * (2/3 - 3/4 * y + 1/3 * y^2 - 5/36 * y^3))
    by (apply Rmult_lt_0_compat; assumption).
  replace ((1 + y + y^2/2 + 5/6 * y^3) * (1 - y + y^2/2 - y^3/6))
    with (1 + y^3 * (2/3 - 3/4 * y + 1/3 * y^2 - 5/36 * y^3)) by field.
  lra. }
assert (Heu : e < 1 + y + y^2/2 + 5/6 * y^3).
{ assert (Hb0 : 0 < 1 - y + y^2/2 - y^3/6) by lra.
  apply (Rmult_lt_reg_r (1 - y + y^2/2 - y^3/6)); [exact Hb0|].
  apply Rle_lt_trans with (e * f); [apply Rmult_le_compat_l; lra | lra]. }
unfold sinh. fold e f.
assert (E3 : y^3 = y * (y * y)) by ring.
(* [y < sinh y < y + y^3/2 <= y + y 2^-54 / 2]. *)
rewrite Rabs_pos_eq by lra.
lra.
Qed.

(** For [0 < y < 2^-27], [y - 2/5 y^3 <= tanh y < y] ([tanh_tiny_bounds]
    of [DyTanhTiny.v]), and [y^2 < 2^-54]. *)
Local Lemma tanh_tiny_bound :
  forall y, 0 < y < bpow radix2 (-27) -> Rabs (tanh y - y) <= y * bpow radix2 (-54).
Proof.
intros y Hy.
assert (Hc : bpow radix2 (-27) < bpow radix2 (-26)) by (apply bpow_lt; lia).
assert (Hy' : 0 < y < bpow radix2 (-26)) by lra.
destruct (tanh_tiny_bounds y Hy') as [H1 H2].
assert (Hbb : bpow radix2 (-27) * bpow radix2 (-27) = bpow radix2 (-54))
  by (rewrite <- bpow_plus; reflexivity).
assert (Hyy : y * y < bpow radix2 (-54)).
{ rewrite <- Hbb. apply Rmult_le_0_lt_compat; lra. }
assert (Hyyy : y * (y * y) <= y * bpow radix2 (-54))
  by (apply Rmult_le_compat_l; lra).
assert (Hp : 0 <= y * bpow radix2 (-54))
  by (apply Rmult_le_pos; [lra | apply bpow_ge_0]).
assert (E3 : y ^ 3 = y * (y * y)) by ring.
rewrite Rabs_left1 by lra.
lra.
Qed.

(** [tanh t] lies strictly between [1 - 2^-54] and 1 for [t >= 20], as
    [tanh_big_bounds] of [DyHypRules.v] shows for 19 and [2^-53]: [tanh t
    = 1 - 2 / (exp (2 t) + 1)] ([tanh_eq]), where [exp (2 t) >= exp 40 >
    2^55], as [55 ln 2 < 38.13]. *)
Local Lemma tanh_big_near_bounds : forall t, 20 <= t -> 1 - bpow radix2 (-54) < tanh t < 1.
Proof.
intros t Ht. rewrite tanh_eq. pose proof ln2_bounds as Hl.
assert (HE : bpow radix2 55 <= exp (2 * t)) by (rewrite bpow_exp2; apply exp_inc; lra).
assert (HB : 0 < bpow radix2 55) by apply bpow_gt_0.
assert (Hb : 0 < bpow radix2 (-54)) by apply bpow_gt_0.
assert (Hbb : bpow radix2 (-54) * bpow radix2 55 = 2) by (rewrite <- bpow_plus; reflexivity).
set (E := exp (2 * t)) in *.
assert (HI : 0 < / (E + 1)) by (apply Rinv_0_lt_compat; lra).
assert (HP : E * / (E + 1) + / (E + 1) = 1).
{ transitivity ((E + 1) * / (E + 1)); [ring | apply Rinv_r; lra]. }
(* [2 / (E + 1) = 2^-54 * (2^55 / (E + 1)) <= 2^-54 * (E / (E + 1)) < 2^-54]. *)
assert (H1 : bpow radix2 55 * / (E + 1) <= E * / (E + 1))
  by (apply Rmult_le_compat_r; lra).
assert (H2 : bpow radix2 (-54) * (bpow radix2 55 * / (E + 1)) < bpow radix2 (-54) * 1)
  by (apply Rmult_lt_compat_l; lra).
assert (H3 : 2 * / (E + 1) = bpow radix2 (-54) * (bpow radix2 55 * / (E + 1)))
  by (rewrite <- Rmult_assoc, Hbb; reflexivity).
split; lra.
Qed.

(** 10^23 is [5^23 2^23], with [2^53 < 5^23 < 2^54]: the midpoint of
    [5960464477539062 2^24] and [5960464477539063 2^24], whose tie goes to
    the even significand. *)
Local Lemma round_1e23 :
  round radix2 (FLT_exp (-1074) 53) ZnearestE (IZR 100000000000000000000000) =
  IZR 5960464477539062 * bpow radix2 24.
Proof.
set (r := IZR 100000000000000000000000).
assert (Hm : (mag radix2 r : Z) = 77%Z).
{ apply mag_unique_pos. change (77 - 1)%Z with 76%Z. unfold r.
  cbn [bpow radix_val radix2]. lra. }
unfold round, scaled_mantissa, cexp. rewrite Hm.
assert (Hs : r * bpow radix2 (- FLT_exp (-1074) 53 77) = IZR 5960464477539062 + / 2).
{ change (- FLT_exp (-1074) 53 77)%Z with (-24)%Z.
  unfold r; cbn [bpow radix_val radix2]; lra. }
rewrite Hs.
change (FLT_exp (-1074) 53 77) with 24%Z.
unfold F2R. cbn [Fnum Fexp]. f_equal. f_equal.
assert (Hf : Zfloor (IZR 5960464477539062 + / 2) = 5960464477539062%Z).
{ apply Zfloor_imp. rewrite plus_IZR. lra. }
unfold Znearest. rewrite Hf.
rewrite Rcompare_Eq by ring.
change (negb (Z.even 5960464477539062)) with false.
reflexivity.
Qed.

(** [sinh] is odd. *)
Local Lemma sinh_odd : forall r, sinh (- r) = - sinh r.
Proof. intros r. unfold sinh. rewrite Ropp_involutive. field. Qed.

(** ** The rules *)

(** An odd [f] with [|f y - y| <= y 2^-54] for [0 < y < 2^-27] rounds
    [x] with [|x| < 2^-27] to nearest to [x]: by [near_x] for [x <> 0],
    and [f 0 = 0] for a zero [x]. *)
Local Lemma odd_tiny_near :
  forall (f : R -> R) x,
  (forall r, f (- r) = - f r) ->
  (forall y, 0 < y < bpow radix2 (-27) -> Rabs (f y - y) <= y * bpow radix2 (-54)) ->
  is_finite x = true -> lt (fabs x) DyadicExp.tiny_near = true -> near_round (f (B2R x)) x.
Proof.
intros f x Hodd Hb Fx Hx.
apply fabs_lt_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit DyadicExp.tiny_near E.
assert (Ht : Rabs (B2R x) < bpow radix2 (-27)) by (cbn [bpow radix_val radix2]; lra).
destruct (Rtotal_order (B2R x) 0) as [N|[Z0|P]].
- apply near_x; [exact Fx | lra |].
  rewrite (Rabs_left (B2R x)) in Ht |- * by exact N.
  replace (f (B2R x) - B2R x) with (- (f (- B2R x) - - B2R x))
    by (rewrite Hodd; ring).
  rewrite Rabs_Ropp. apply Hb. lra.
- (* [f 0 = - f 0]. *)
  assert (H0 : f 0 = 0) by (pose proof (Hodd 0) as H; rewrite Ropp_0 in H; lra).
  replace (f (B2R x)) with (B2R x) by (rewrite Z0, H0; reflexivity).
  exact (near_exact x Fx).
- apply near_x; [exact Fx | lra |].
  rewrite (Rabs_pos_eq (B2R x)) in Ht |- * by lra.
  apply Hb. lra.
Qed.

(** exp *)

Local Lemma exp_inf_near :
  forall x, is_finite x = true -> ge x (from_bits 0x4086300000000000) = true ->
  near_round (exp (B2R x)) infinity.
Proof.
intros x Fx Hx. apply near_inf.
apply ge_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit (from_bits 0x4086300000000000) E.
assert (H : bpow radix2 1024 <= exp (B2R x)) by (apply exp_710; lra).
pose proof (bpow_gt_0 radix2 970). lra.
Qed.

(** [exp x <= exp (-746) < 2^-1075], as [1075 ln 2 < 745.14]. *)
Local Lemma exp_zero_near :
  forall x, is_finite x = true -> le x (from_bits 0xc087500000000000) = true ->
  near_round (exp (B2R x)) zero.
Proof.
intros x Fx Hx. apply near_zero.
apply le_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit (from_bits 0xc087500000000000) E.
split; [apply exp_pos|]. rewrite bpow_exp2. apply exp_inc.
pose proof ln2_bounds. lra.
Qed.

Local Lemma exp_one_near :
  forall x, is_finite x = true -> lt (fabs x) DyadicExp.tiny_exp = true ->
  near_round (exp (B2R x)) DyadicExp.one.
Proof.
intros x Fx Hx. apply near_one.
apply fabs_lt_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit DyadicExp.tiny_exp E.
apply exp_tiny_near. cbn [bpow radix_val radix2]. lra.
Qed.

(** exp2 *)

Local Lemma exp2_inf_near :
  forall x, is_finite x = true -> ge x (from_bits 0x4090000000000000) = true ->
  near_round (Rexp2 (B2R x)) infinity.
Proof.
intros x Fx Hx. apply near_inf.
apply ge_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit (from_bits 0x4090000000000000) E.
assert (H : bpow radix2 1024 <= Rexp2 (B2R x)).
{ unfold Rexp2, Rpower. rewrite bpow_exp2. apply exp_inc.
  pose proof ln2_bounds. apply Rmult_le_compat_r; lra. }
pose proof (bpow_gt_0 radix2 970). lra.
Qed.

Local Lemma exp2_zero_near :
  forall x, is_finite x = true -> lt x (from_bits 0xc090cc0000000000) = true ->
  near_round (Rexp2 (B2R x)) zero.
Proof.
intros x Fx Hx. apply near_zero.
apply lt_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit (from_bits 0xc090cc0000000000) E.
unfold Rexp2, Rpower. split; [apply exp_pos|].
rewrite bpow_exp2. apply exp_inc.
pose proof ln2_bounds. apply Rmult_le_compat_r; lra.
Qed.

(** [|x ln 2| <= |x| < 2^-54]. *)
Local Lemma exp2_one_near :
  forall x, is_finite x = true -> lt (fabs x) DyadicExp.tiny_exp = true ->
  near_round (Rexp2 (B2R x)) DyadicExp.one.
Proof.
intros x Fx Hx. apply near_one.
apply fabs_lt_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit DyadicExp.tiny_exp E.
pose proof ln2_bounds as Hl.
unfold Rexp2, Rpower. apply exp_tiny_near.
rewrite Rabs_mult, (Rabs_pos_eq (ln 2)) by lra.
pose proof (Rabs_pos (B2R x)).
assert (Rabs (B2R x) * ln 2 <= Rabs (B2R x)) by nra.
cbn [bpow radix_val radix2]. lra.
Qed.

(** exp10 *)

(** [1024 ln 2 < 709.79 < 711.49 < 309 ln 10 <= x ln 10]. *)
Local Lemma exp10_inf_near :
  forall x, is_finite x = true -> ge x (from_bits 0x4073500000000000) = true ->
  near_round (Rexp10 (B2R x)) infinity.
Proof.
intros x Fx Hx. apply near_inf.
apply ge_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit (from_bits 0x4073500000000000) E.
assert (H : bpow radix2 1024 <= Rexp10 (B2R x)).
{ unfold Rexp10, Rpower. rewrite bpow_exp2. apply exp_inc.
  pose proof ln2_bounds. pose proof ln10_bounds.
  assert (309 * ln 10 <= B2R x * ln 10) by (apply Rmult_le_compat_r; lra).
  lra. }
pose proof (bpow_gt_0 radix2 970). lra.
Qed.

(** [x ln 10 <= -324 ln 10 < -746.03 < -745.14 < -1075 ln 2]. *)
Local Lemma exp10_zero_near :
  forall x, is_finite x = true -> le x (from_bits 0xc074400000000000) = true ->
  near_round (Rexp10 (B2R x)) zero.
Proof.
intros x Fx Hx. apply near_zero.
apply le_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit (from_bits 0xc074400000000000) E.
unfold Rexp10, Rpower. split; [apply exp_pos|].
rewrite bpow_exp2. apply exp_inc.
pose proof ln2_bounds. pose proof ln10_bounds.
assert (B2R x * ln 10 <= -324 * ln 10) by (apply Rmult_le_compat_r; lra).
lra.
Qed.

(** [|x ln 10| < 4 |x| < 4 * 2^-56 = 2^-54]. *)
Local Lemma exp10_one_near :
  forall x, is_finite x = true -> lt (fabs x) DyadicExp.tiny_exp10 = true ->
  near_round (Rexp10 (B2R x)) DyadicExp.one.
Proof.
intros x Fx Hx. apply near_one.
apply fabs_lt_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit DyadicExp.tiny_exp10 E.
pose proof ln10_bounds as Hl.
unfold Rexp10, Rpower. apply exp_tiny_near.
rewrite Rabs_mult, (Rabs_pos_eq (ln 10)) by lra.
pose proof (Rabs_pos (B2R x)).
assert (Rabs (B2R x) * ln 10 <= 4 * Rabs (B2R x)) by nra.
cbn [bpow radix_val radix2]. lra.
Qed.

(** [10^k] for an integer [1 <= k <= 22] is the [f64] [pow10 k]
    ([pow10_exact]), as the proof of [exp10_int_rule] of [DyExpRules.v]
    shows. *)
Local Lemma exp10_int_near :
  forall x, is_finite x = true ->
  le DyadicExp.one x && le x (from_bits 0x4036000000000000) && eq x (ffloor x) = true ->
  near_round (Rexp10 (B2R x)) (DyadicExp.pow10 (DyadicExp.to_i64 x)).
Proof.
intros x Fx Hx.
apply andb_prop in Hx as [Hx He]. apply andb_prop in Hx as [H1 H22].
apply le_R in H1; [| vm_compute; reflexivity | exact Fx].
apply le_R in H22; [| exact Fx | vm_compute; reflexivity].
lit DyadicExp.one Eone. lit (from_bits 0x4036000000000000) E22.
(* [x] is [floor x], an integer [k]. *)
destruct (Bnearbyint_correct 53 1024 _ mode_DN x) as (Ef & Ff & _).
unfold eq, ffloor in He. rewrite Beqb_correct in He by (try rewrite Ff; exact Fx).
rewrite Ef, round_FIX_IZR in He.
destruct (Req_bool_spec (B2R x) (IZR (round_mode mode_DN (B2R x)))) as [Hk|];
  [|discriminate].
set (k := round_mode mode_DN (B2R x)) in Hk. clearbody k.
assert (Hk1 : (1 <= k <= 22)%Z) by (split; apply le_IZR; lra).
(* [to_i64 x] is [k]: [Btrunc x] is [trunc k = k]. *)
assert (Ht : DyadicExp.to_i64 x = k).
{ assert (Et : IZR (Btrunc x) = IZR k)
    by (rewrite Btrunc_correct, round_FIX_IZR, Hk, Ztrunc_IZR; reflexivity).
  apply eq_IZR in Et.
  destruct x as [s|s| |s m e B]; try discriminate.
  - cbn [B2R] in Hk. apply eq_IZR in Hk. lia.
  - cbn [DyadicExp.to_i64]. rewrite Et. lia. }
rewrite Ht. destruct (pow10_exact k Hk1) as [Fp Ep].
replace (Rexp10 (B2R x)) with (B2R (DyadicExp.pow10 k)); [exact (near_exact _ Fp)|].
rewrite Ep, Hk.
(* [10 ^ k] for the natural number [k]. *)
assert (Hn : IZR k = INR (Z.to_nat k)) by (rewrite INR_IZR_INZ, Z2Nat.id by lia; reflexivity).
unfold Rexp10. rewrite Hn, Rpower_pow by lra.
rewrite pow_IZR, Z2Nat.id by lia. reflexivity.
Qed.

(** [10^23] rounds to nearest to the literal [1e23] ([round_1e23]). *)
Local Lemma exp10_23_near :
  forall x, is_finite x = true -> eq x (from_bits 0x4037000000000000) = true ->
  near_round (Rexp10 (B2R x)) (from_bits 0x44b52d02c7e14af6).
Proof.
intros x Fx Hx.
unfold eq in Hx. rewrite Beqb_correct in Hx by first [exact Fx | vm_compute; reflexivity].
destruct (Req_bool_spec (B2R x) (B2R (from_bits 0x4037000000000000))) as [Hk|];
  [|discriminate].
lit (from_bits 0x4037000000000000) E23.
assert (Hn : B2R x = INR 23).
{ rewrite INR_IZR_INZ. change (Z.of_nat 23) with 23%Z. lra. }
assert (Hr : Rexp10 (B2R x) = IZR 100000000000000000000000).
{ unfold Rexp10. rewrite Hn, Rpower_pow by lra. rewrite pow_IZR. reflexivity. }
rewrite Hr.
lit (from_bits 0x44b52d02c7e14af6) Ev.
unfold near_round.
destruct (Rle_dec (bpow radix2 1024 - bpow radix2 970) (Rabs (IZR 100000000000000000000000)))
  as [Hc|_].
{ exfalso. rewrite Rabs_pos_eq in Hc by lra. revert Hc.
  cbn [bpow radix_val radix2]. lra. }
split; [vm_compute; reflexivity|]. split.
- rewrite round_1e23, Ev. cbn [bpow radix_val radix2]. lra.
- intros _ H0. lra.
Qed.

(** sinh *)

(** [sinh x >= (2^1025 + 1 - 1) / 2] by [exp_711] of [DyHypRules.v]. *)
Local Lemma sinh_inf_near :
  forall x, is_finite x = true -> ge x (from_bits 0x4086380000000000) = true ->
  near_round (sinh (B2R x)) infinity.
Proof.
intros x Fx Hx. apply near_inf.
apply ge_R in Hx; [| exact Fx | vm_compute; reflexivity]. rewrite hyp_lit_711 in Hx.
pose proof (exp_711 _ Hx) as H.
assert (H1 : exp (- B2R x) <= 1) by (rewrite <- exp_0; apply exp_inc; lra).
pose proof (bpow_gt_0 radix2 970).
unfold sinh. lra.
Qed.

Local Lemma sinh_ninf_near :
  forall x, is_finite x = true -> le x (from_bits 0xc086380000000000) = true ->
  near_round (sinh (B2R x)) DyadicExp.neg_infinity.
Proof.
intros x Fx Hx. apply near_ninf.
apply le_R in Hx; [| exact Fx | vm_compute; reflexivity]. rewrite hyp_lit_m711 in Hx.
assert (Ht : 711 <= - B2R x) by lra.
pose proof (exp_711 _ Ht) as H.
assert (H1 : exp (B2R x) <= 1) by (rewrite <- exp_0; apply exp_inc; lra).
pose proof (bpow_gt_0 radix2 970).
unfold sinh. lra.
Qed.

(** cosh *)

Local Lemma cosh_inf_near :
  forall x, is_finite x = true -> ge (fabs x) (from_bits 0x4086380000000000) = true ->
  near_round (cosh (B2R x)) infinity.
Proof.
intros x Fx Hx. apply near_inf.
apply ge_R in Hx; [| unfold fabs; rewrite is_finite_Babs; exact Fx | vm_compute; reflexivity].
rewrite hyp_lit_711 in Hx. unfold fabs in Hx. rewrite B2R_Babs in Hx.
pose proof (exp_711 _ Hx) as H. pose proof (exp_pos (- Rabs (B2R x))) as H1.
pose proof (bpow_gt_0 radix2 970).
rewrite cosh_Rabs. unfold cosh. lra.
Qed.

(** [1 < cosh y <= 1 + y^2 < 1 + 2^-54] for [0 < y = |x| < 2^-27]
    ([cosh_tiny_bounds] of [DyHypRules.v]), and [cosh 0 = 1]. *)
Local Lemma cosh_one_near :
  forall x, is_finite x = true -> lt (fabs x) DyadicExp.tiny_near = true ->
  near_round (cosh (B2R x)) DyadicExp.one.
Proof.
intros x Fx Hx. apply near_one.
apply fabs_lt_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit DyadicExp.tiny_near E.
assert (Hy : Rabs (B2R x) < bpow radix2 (-27)) by (cbn [bpow radix_val radix2]; lra).
assert (Hc : bpow radix2 (-27) < 1 / 2 /\ 0 < bpow radix2 (-27) /\
             bpow radix2 (-53) = 2 * bpow radix2 (-54) /\ 0 < bpow radix2 (-54))
  by (cbn [bpow radix_val radix2]; lra).
assert (Hbb : bpow radix2 (-27) * bpow radix2 (-27) = bpow radix2 (-54))
  by (rewrite <- bpow_plus; reflexivity).
pose proof (Rabs_pos (B2R x)) as Hp.
rewrite cosh_Rabs.
destruct (Rlt_or_le 0 (Rabs (B2R x))) as [Pos|Z0].
- assert (Hyy : Rabs (B2R x) * Rabs (B2R x) < bpow radix2 (-27) * bpow radix2 (-27))
    by (apply Rmult_le_0_lt_compat; lra).
  assert (Hy2 : 0 < Rabs (B2R x) < 1 / 2) by lra.
  destruct (cosh_tiny_bounds _ Hy2) as [H1 H2]. lra.
- assert (E0 : Rabs (B2R x) = 0) by lra.
  rewrite E0. unfold cosh. rewrite Ropp_0, exp_0. lra.
Qed.

(** tanh *)

Local Lemma tanh_one_near :
  forall x, is_finite x = true -> ge x (from_bits 0x4034000000000000) = true ->
  near_round (tanh (B2R x)) DyadicExp.one.
Proof.
intros x Fx Hx. apply near_one.
apply ge_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit (from_bits 0x4034000000000000) E.
assert (Ht : 20 <= B2R x) by lra.
destruct (tanh_big_near_bounds _ Ht) as [H1 H2].
pose proof (bpow_gt_0 radix2 (-53)). lra.
Qed.

Local Lemma tanh_m_one_near :
  forall x, is_finite x = true -> le x (from_bits 0xc034000000000000) = true ->
  near_round (tanh (B2R x)) DyadicExp.m_one.
Proof.
intros x Fx Hx. apply near_m_one.
apply le_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit (from_bits 0xc034000000000000) E.
assert (Ht : 20 <= - B2R x) by lra.
destruct (tanh_big_near_bounds _ Ht) as [H1 H2]. rewrite tanh_odd in H1, H2.
pose proof (bpow_gt_0 radix2 (-53)). lra.
Qed.

Local Close Scope R_scope.

(** ** The functions *)

Theorem exp_near_correct :
  forall x v,
  is_finite x = true -> DyadicExp.exp_near_with ziv_near_strict x = Some v ->
  near_round (exp (B2R x)) v.
Proof.
intros x v Fx H. unfold DyadicExp.exp_near_with in H.
rewrite (fin_not_nan x Fx), (fin_neq_inf x Fx), (fin_neq_ninf x Fx) in H. cbn [orb] in H.
destruct (ge x (from_bits 0x4086300000000000)) eqn:G1; cbv iota in H.
{ injection H as <-. exact (exp_inf_near x Fx G1). }
destruct (le x (from_bits 0xc087500000000000)) eqn:G2; cbv iota in H.
{ injection H as <-. exact (exp_zero_near x Fx G2). }
destruct (lt (fabs x) DyadicExp.tiny_exp) eqn:G3; cbv iota in H.
{ injection H as <-. exact (exp_one_near x Fx G3). }
destruct (DyadicExp.fast_exp_near false x) eqn:F; cbv iota in H.
{ injection H as <-. exact (fast_exp_near_correct false x _ Fx F). }
exact (ziv_near_strict_correct _ _ _ _ (fun n a Hn Ha => ev_exp_correct x n a Hn Ha) H).
Qed.

Theorem exp2_near_correct :
  forall x v,
  is_finite x = true -> DyadicExp.exp2_near_with ziv_near_strict x = Some v ->
  near_round (Rexp2 (B2R x)) v.
Proof.
intros x v Fx H. unfold DyadicExp.exp2_near_with in H.
rewrite (fin_not_nan x Fx), (fin_neq_inf x Fx), (fin_neq_ninf x Fx) in H. cbn [orb] in H.
destruct (ge x (from_bits 0x4090000000000000)) eqn:G1; cbv iota in H.
{ injection H as <-. exact (exp2_inf_near x Fx G1). }
destruct (lt x (from_bits 0xc090cc0000000000)) eqn:G2; cbv iota in H.
{ injection H as <-. exact (exp2_zero_near x Fx G2). }
destruct (lt (fabs x) DyadicExp.tiny_exp) eqn:G3; cbv iota in H.
{ injection H as <-. exact (exp2_one_near x Fx G3). }
destruct (DyadicExp.fast_exp2_near false x) eqn:F; cbv iota in H.
{ injection H as <-. exact (fast_exp2_near_correct false x _ Fx (tiny_exp_false x Fx G3) F). }
exact (ziv_near_strict_correct _ _ _ _ (fun n a Hn Ha => ev_exp2_correct x n a Hn Ha) H).
Qed.

Theorem exp10_near_correct :
  forall x v,
  is_finite x = true -> DyadicExp.exp10_near_with ziv_near_strict x = Some v ->
  near_round (Rexp10 (B2R x)) v.
Proof.
intros x v Fx H. unfold DyadicExp.exp10_near_with in H.
rewrite (fin_not_nan x Fx), (fin_neq_inf x Fx), (fin_neq_ninf x Fx) in H. cbn [orb] in H.
destruct (ge x (from_bits 0x4073500000000000)) eqn:G1; cbv iota in H.
{ injection H as <-. exact (exp10_inf_near x Fx G1). }
destruct (le x (from_bits 0xc074400000000000)) eqn:G2; cbv iota in H.
{ injection H as <-. exact (exp10_zero_near x Fx G2). }
destruct (lt (fabs x) DyadicExp.tiny_exp10) eqn:G3; cbv iota in H.
{ injection H as <-. exact (exp10_one_near x Fx G3). }
destruct (le DyadicExp.one x && le x (from_bits 0x4036000000000000) && eq x (ffloor x))
  eqn:G4; cbv iota in H.
{ injection H as <-. exact (exp10_int_near x Fx G4). }
destruct (eq x (from_bits 0x4037000000000000)) eqn:G5; cbv iota in H.
{ injection H as <-. exact (exp10_23_near x Fx G5). }
destruct (DyadicExp.fast_exp10_near false x) eqn:F; cbv iota in H.
{ injection H as <-. exact (fast_exp10_near_correct false x _ Fx (tiny_exp10_false x Fx G3) F). }
exact (ziv_near_strict_correct _ _ _ _ (fun n a Hn Ha => ev_exp10_correct x n a Hn Ha) H).
Qed.

Theorem sinh_near_correct :
  forall x v,
  is_finite x = true -> DyadicExp.sinh_near_with ziv_near_strict x = Some v ->
  near_round (sinh (B2R x)) v.
Proof.
intros x v Fx H. unfold DyadicExp.sinh_near_with in H.
rewrite (fin_not_nan x Fx), (fin_neq_inf x Fx), (fin_neq_ninf x Fx) in H. cbn [orb] in H.
destruct (ge x (from_bits 0x4086380000000000)) eqn:G1; cbv iota in H.
{ injection H as <-. exact (sinh_inf_near x Fx G1). }
destruct (le x (from_bits 0xc086380000000000)) eqn:G2; cbv iota in H.
{ injection H as <-. exact (sinh_ninf_near x Fx G2). }
destruct (lt (fabs x) DyadicExp.tiny_near) eqn:G3; cbv iota in H.
{ injection H as <-. exact (odd_tiny_near sinh x sinh_odd sinh_tiny_bound Fx G3). }
destruct (DyadicExp.fast_sinh_near false x) eqn:F; cbv iota in H.
{ injection H as <-. exact (fast_sinh_near_correct false x _ Fx F). }
exact (ziv_near_strict_correct _ _ _ _ (fun n a Hn Ha => ev_sinh_correct x n a Hn Ha) H).
Qed.

Theorem cosh_near_correct :
  forall x v,
  is_finite x = true -> DyadicExp.cosh_near_with ziv_near_strict x = Some v ->
  near_round (cosh (B2R x)) v.
Proof.
intros x v Fx H. unfold DyadicExp.cosh_near_with in H. cbv zeta in H.
assert (Ft : is_finite (fabs x) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fx).
rewrite (fin_not_nan _ Ft), (fin_neq_inf _ Ft) in H. cbn [orb] in H.
destruct (ge (fabs x) (from_bits 0x4086380000000000)) eqn:G1; cbv iota in H.
{ injection H as <-. exact (cosh_inf_near x Fx G1). }
destruct (lt (fabs x) DyadicExp.tiny_near) eqn:G3; cbv iota in H.
{ injection H as <-. exact (cosh_one_near x Fx G3). }
destruct (DyadicExp.fast_cosh_near false (fabs x)) eqn:F; cbv iota in H.
{ injection H as <-. rewrite cosh_Rabs, <- hyp_fabs.
  apply (fast_cosh_near_correct false (fabs x) _ Ft); [|exact F].
  rewrite hyp_fabs. apply Rabs_pos. }
assert (Hev : forall n a, level_ok n -> DyadicExp.ev_cosh (fabs x) n = Some a ->
                encl_ok n a /\ encl_has a (cosh (B2R x))).
{ intros n a Hn Ha. destruct (ev_cosh_correct _ n a Hn Ha) as (Oa & Ha').
  split; [exact Oa|]. rewrite hyp_fabs in Ha'. rewrite cosh_Rabs. exact Ha'. }
exact (ziv_near_strict_correct _ _ _ _ Hev H).
Qed.

Theorem tanh_near_correct :
  forall x v,
  is_finite x = true -> DyadicExp.tanh_near_with ziv_near_strict x = Some v ->
  near_round (tanh (B2R x)) v.
Proof.
intros x v Fx H. unfold DyadicExp.tanh_near_with in H.
rewrite (fin_not_nan x Fx) in H. cbv iota in H.
destruct (ge x (from_bits 0x4034000000000000)) eqn:G1; cbv iota in H.
{ injection H as <-. exact (tanh_one_near x Fx G1). }
destruct (le x (from_bits 0xc034000000000000)) eqn:G2; cbv iota in H.
{ injection H as <-. exact (tanh_m_one_near x Fx G2). }
destruct (lt (fabs x) DyadicExp.tiny_near) eqn:G3; cbv iota in H.
{ injection H as <-. exact (odd_tiny_near tanh x tanh_odd tanh_tiny_bound Fx G3). }
destruct (DyadicExp.fast_tanh_near false x) eqn:F; cbv iota in H.
{ injection H as <-. exact (fast_tanh_near_correct false x _ Fx F). }
exact (ziv_near_strict_correct _ _ _ _ (fun n a Hn Ha => ev_tanh_correct x n a Hn Ha) H).
Qed.

Theorem exp_near_strict :
  forall x v, DyadicExp.exp_near_with ziv_near_strict x = Some v -> DyadicExp.exp_near x = Some v.
Proof.
intros x v. unfold DyadicExp.exp_near, DyadicExp.exp_near_with. near_strict.
Qed.

Theorem exp2_near_strict :
  forall x v, DyadicExp.exp2_near_with ziv_near_strict x = Some v -> DyadicExp.exp2_near x = Some v.
Proof.
intros x v. unfold DyadicExp.exp2_near, DyadicExp.exp2_near_with. near_strict.
Qed.

Theorem exp10_near_strict :
  forall x v,
  DyadicExp.exp10_near_with ziv_near_strict x = Some v -> DyadicExp.exp10_near x = Some v.
Proof.
intros x v. unfold DyadicExp.exp10_near, DyadicExp.exp10_near_with. near_strict.
Qed.

Theorem sinh_near_strict :
  forall x v, DyadicExp.sinh_near_with ziv_near_strict x = Some v -> DyadicExp.sinh_near x = Some v.
Proof.
intros x v. unfold DyadicExp.sinh_near, DyadicExp.sinh_near_with. near_strict.
Qed.

Theorem cosh_near_strict :
  forall x v, DyadicExp.cosh_near_with ziv_near_strict x = Some v -> DyadicExp.cosh_near x = Some v.
Proof.
intros x v. unfold DyadicExp.cosh_near, DyadicExp.cosh_near_with. cbv zeta. near_strict.
Qed.

Theorem tanh_near_strict :
  forall x v, DyadicExp.tanh_near_with ziv_near_strict x = Some v -> DyadicExp.tanh_near x = Some v.
Proof.
intros x v. unfold DyadicExp.tanh_near, DyadicExp.tanh_near_with. near_strict.
Qed.
