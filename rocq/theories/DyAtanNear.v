(** * The inverse trigonometric functions of the dyadic kernel rounded to nearest

    [atan_near_with ziv_near_strict] and the others of [DyadicAtan]
    return, where they return, their function at finite arguments of its
    domain rounded to nearest as [near_round] says: the loop by
    [ziv_near_strict_correct] and the enclosures of [DyAtan.v] and
    [DyAsin.v], and the rules before it by the cells of [NearCells.v],
    the bounds of [DyAtanTiny.v] and of π, and, for the quotients of
    [atan2_near_with] midway between two [f64]s below 2^-1021, by
    [DyAtanMidQ.v]. Where they return with
    [ziv_near_strict], they return the same with [Dyadic.ziv_near]
    ([atan_near_strict] and the others). *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary LogReal AtanReal DyRound DyConv DyOps
  DyDriver DyGrow DyConst DyExpCore DyExpRules DyExp ExpReal DyHyp DyHypRules DyLogRules
  DyLogCore DyLog DyLogHyp AtanSeries AtanIdent DyConstPi DyAtanTiny DyAtanCore DyAtan DyAsin
  MpfrRound NearF64 NearCells DyDriverNear DyAtanMidQ FastAtan FastAsin AtanPiConst.
From Inari Require PiBounds PiTight.

Open Scope Z_scope.

(** ** Helpers *)

(** [tiny_near] is [2^-27]: [B2SF] of the literal computes to its sign,
    significand and exponent, as [asin_lit_tiny] of [DyAtanTiny.v] has it. *)
Local Lemma tn_lit_tiny : B2R DyadicExp.tiny_near = bpow radix2 (-27).
Proof.
rewrite <- (SF2R_B2SF _ _ DyadicExp.tiny_near).
let s := eval vm_compute in (B2SF DyadicExp.tiny_near) in
replace (B2SF DyadicExp.tiny_near) with s by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]; unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
reflexivity.
Qed.

(** [lt (fabs x) tiny_near] is [|x| < 2^-27]. *)
Local Lemma tn_tiny :
  forall x, is_finite x = true -> lt (fabs x) DyadicExp.tiny_near = true ->
  (Rabs (B2R x) < bpow radix2 (-27))%R.
Proof.
intros x Fx G. rewrite <- tn_lit_tiny.
apply fabs_lt_R; [exact Fx | vm_compute; reflexivity | exact G].
Qed.

(** [lt (fabs x) tiny_asin] is [|x| < 2^-27] too ([asin_lit_tiny]). *)
Local Lemma tn_tiny_asin :
  forall x, is_finite x = true -> lt (fabs x) DyadicAtan.tiny_asin = true ->
  (Rabs (B2R x) < bpow radix2 (-27))%R.
Proof.
intros x Fx G. rewrite <- asin_lit_tiny.
apply fabs_lt_R; [exact Fx | vm_compute; reflexivity | exact G].
Qed.

(** For [0 < w < 2^-27], [w^3 < w 2^-54], as [w^2 < 2^-54]. *)
Local Lemma tn_cube :
  forall w, (0 < w < bpow radix2 (-27))%R -> (w ^ 3 < w * bpow radix2 (-54))%R.
Proof.
intros w Hw.
assert (E : bpow radix2 (-54) = (bpow radix2 (-27) * bpow radix2 (-27))%R)
  by (rewrite <- bpow_plus; reflexivity).
assert (Hww : (w * w < bpow radix2 (-54))%R) by (rewrite E; apply Rmult_le_0_lt_compat; lra).
replace (w ^ 3)%R with (w * (w * w))%R by ring.
apply Rmult_lt_compat_l; lra.
Qed.

(** An odd [f] within [w 2^-54] of [w] for [0 < w < 2^-27] rounds to
    nearest to [x] at a finite [x] with [|x| < 2^-27]: by [near_exact] at
    [x = 0], where [f 0 = 0], and otherwise by [near_x], as
    [f x - x = - (f (-x) - (-x))]. *)
Local Lemma tn_odd :
  forall (f : R -> R) x,
  (forall w, f (- w) = - f w)%R ->
  (forall w, 0 < w < bpow radix2 (-27) -> Rabs (f w - w) <= w * bpow radix2 (-54))%R ->
  is_finite x = true -> (Rabs (B2R x) < bpow radix2 (-27))%R ->
  near_round (f (B2R x)) x.
Proof.
intros f x Fo Fb Fx Hx.
destruct (Req_dec (B2R x) 0) as [X0|X0].
- assert (F0 : f 0%R = 0%R) by (pose proof (Fo 0%R) as E; rewrite Ropp_0 in E; lra).
  rewrite X0, F0, <- X0. exact (near_exact x Fx).
- apply (near_x x _ Fx X0).
  destruct (Rlt_or_le 0 (B2R x)) as [P|N].
  + rewrite (Rabs_pos_eq (B2R x)) in Hx |- * by lra. apply Fb. lra.
  + assert (N' : (B2R x < 0)%R)
      by (destruct (Rle_lt_or_eq_dec _ _ N); [assumption | contradiction]).
    rewrite (Rabs_left1 (B2R x)) in Hx |- * by lra.
    replace (f (B2R x) - B2R x)%R with (- (f (- B2R x) - - B2R x))%R by (rewrite Fo; ring).
    rewrite Rabs_Ropp. apply Fb. lra.
Qed.

(** For [0 < w < 2^-27], [w - w^3/3 <= atan w < w] ([atan_tiny_real]),
    and [w^3 < w 2^-54]. *)
Local Lemma tn_atan :
  forall w, (0 < w < bpow radix2 (-27))%R -> (Rabs (atan w - w) <= w * bpow radix2 (-54))%R.
Proof.
intros w Hw.
pose proof (tn_cube w Hw) as H3.
assert (B : (bpow radix2 (-27) < bpow radix2 (-26))%R) by (apply bpow_lt; lia).
destruct (atan_tiny_real w ltac:(lra)) as [A1 A2].
assert (P3 : (0 < w ^ 3)%R) by (apply pow_lt; lra).
apply Rabs_le. lra.
Qed.

(** For [0 < w < 2^-27], [w < asin w <= w + w^3] ([asin_tiny_real]),
    and [w^3 < w 2^-54]. *)
Local Lemma tn_asin :
  forall w, (0 < w < bpow radix2 (-27))%R -> (Rabs (asin w - w) <= w * bpow radix2 (-54))%R.
Proof.
intros w Hw.
pose proof (tn_cube w Hw) as H3.
destruct (asin_tiny_real w Hw) as [A1 A2].
assert (P3 : (0 < w ^ 3)%R) by (apply pow_lt; lra).
apply Rabs_le. lra.
Qed.

(** The [f64] below [π/2] ([PiTight.v]). *)
Local Notation pi2_lo := (Interval.inf_raw Interval.FRAC_PI_2).

(** Every real in [(pi2_lo, π/2]] rounds to nearest to [pi2_lo]: [pi2_lo]
    is [7074237752028440 / 2^52] ([pb_frac_lo], [pb_lo_R]), which π to
    18 decimals ([PI_Q]) puts less than [6.2e-17] below [π/2], within
    [pi2_lo 2^-54 > 8.7e-17] ([near_x]). *)
Local Lemma tn_pi2 : forall r, (B2R pi2_lo < r <= PI / 2)%R -> near_round r pi2_lo.
Proof.
intros r Hr.
destruct PiTight.pt_FRAC_PI_2_facts as (Flo & _ & _).
destruct PiBounds.PI_Q as [P1 P2].
unfold Q2R, PiBounds.pi_lo, PiBounds.pi_hi in P1, P2.
cbn [QArith_base.Qnum QArith_base.Qden] in P1, P2.
assert (L : B2R pi2_lo = (7074237752028440 / 4503599627370496)%R).
{ rewrite PiBounds.pb_frac_lo, PiBounds.pb_lo_R.
  unfold Q2R; cbn [QArith_base.Qnum QArith_base.Qden]. lra. }
assert (E : bpow radix2 (-54) = (1 / 18014398509481984)%R)
  by (cbn [bpow radix_val radix2]; lra).
apply (near_x _ r Flo).
- rewrite L. lra.
- rewrite E, L in *. rewrite Rabs_pos_eq by lra. rewrite Rabs_pos_eq by lra. lra.
Qed.

(** [pi_times_near_with ziv_near_strict c] rounds [c π] to nearest, by
    the constants of [pi_bounds] ([pi_const_near]) or the loop on
    [ev_pi]. *)
Local Lemma tn_pi_times :
  forall c v, is_finite c = true ->
  DyadicAtan.pi_times_near_with ziv_near_strict c = Some v -> near_round (B2R c * PI) v.
Proof.
intros c v Fc H. unfold DyadicAtan.pi_times_near_with in H.
destruct (DyadicAtan.pi_bounds (fabs c)) as [[lo hi]|] eqn:Eb; cbv beta iota in H.
{ injection H as <-. exact (pi_const_near c lo hi Fc Eb). }
apply (ziv_near_strict_correct (DyadicAtan.ev_pi c) 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_pi_correct c n a Hn Fc Ha).
Qed.

(** For a finite [x] with [|x| >= 2^54], [atan |x|] lies in
    [(pi2_lo, π/2)] ([atn_huge_between], [atan_bound]), so it and [π/2]
    both round to [pi2_lo] ([tn_pi2]), and [pi_times_near (copysign 0.5 x)], which
    rounds [±π/2] ([tn_pi_times]), is [±pi2_lo] ([near_unique],
    [near_opp]), the rounding of [atan x = ± atan |x|]. *)
Local Lemma tn_huge :
  forall x v,
  is_finite x = true -> ge (fabs x) DyadicAtan.huge_atan = true ->
  DyadicAtan.pi_times_near_with ziv_near_strict (copysign DyadicLog.half x) = Some v ->
  near_round (atan (B2R x)) v.
Proof.
intros x v Fx G H.
(* [huge_atan] is [2^54]. *)
assert (Fh : is_finite DyadicAtan.huge_atan = true) by (vm_compute; reflexivity).
assert (Hh : B2R DyadicAtan.huge_atan = 18014398509481984%R).
{ rewrite <- SF2R_B2SF.
  replace (B2SF DyadicAtan.huge_atan) with (SpecFloat.S754_finite false 4503599627370496 2)
    by (vm_compute; reflexivity).
  cbn [SF2R SpecFloat.cond_Zopp cond_Zopp]. unfold F2R; cbn [Fnum Fexp bpow radix_val radix2].
  lra. }
assert (Ht : (18014398509481984 <= Rabs (B2R x))%R).
{ assert (Fa : is_finite (fabs x) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fx).
  unfold ge in G. rewrite Bleb_correct in G by assumption.
  unfold fabs in G. rewrite B2R_Babs, Hh in G.
  destruct (Rle_bool_spec 18014398509481984%R (Rabs (B2R x))) as [L|L];
    [exact L | discriminate G]. }
destruct (atn_huge_between _ Ht) as (A & P).
destruct (atan_bound (Rabs (B2R x))) as [_ B].
assert (Ra : near_round (atan (Rabs (B2R x))) pi2_lo) by (apply tn_pi2; lra).
assert (Rp : near_round (1 / 2 * PI) pi2_lo) by (apply tn_pi2; lra).
assert (Pn : (1 / 2 * PI <> 0)%R) by (pose proof PI_RGT_0; lra).
assert (Sh : Bsign DyadicLog.half = false) by (vm_compute; reflexivity).
assert (Fhalf : is_finite DyadicLog.half = true) by (vm_compute; reflexivity).
destruct (atn_copysign DyadicLog.half x Sh Fhalf) as (Fc & Vc).
pose proof (tn_pi_times _ v Fc H) as R.
rewrite Vc, lc_half_R in R.
revert R. destruct (Bsign x) eqn:Sx; intros R.
- (* [x <= -2^54]: [atan x = - atan |x|], and [R] rounds [-π/2]. *)
  pose proof (atn_sign_true x Sx) as Xn.
  rewrite (Rabs_left1 _ Xn), atan_opp in Ra.
  apply near_opp in Ra, Rp. rewrite Ropp_involutive in Ra.
  replace (- (1 / 2) * PI)%R with (- (1 / 2 * PI))%R in R by ring.
  assert (Pm : (- (1 / 2 * PI) <> 0)%R) by (pose proof PI_RGT_0; lra).
  rewrite (near_unique _ v (opp pi2_lo) Pm R Rp). exact Ra.
- (* [x >= 2^54], and [R] rounds [π/2]. *)
  pose proof (atn_sign_false x Sx) as Xp.
  rewrite (Rabs_pos_eq _ Xp) in Ra.
  rewrite (near_unique _ v pi2_lo Pn R Rp). exact Ra.
Qed.

(** [pi_times_near_with ziv_near_strict c] returns as [pi_times_near c]. *)
Local Lemma pi_times_near_strict :
  forall c v,
  DyadicAtan.pi_times_near_with ziv_near_strict c = Some v -> DyadicAtan.pi_times_near c = Some v.
Proof.
intros c v. unfold DyadicAtan.pi_times_near, DyadicAtan.pi_times_near_with.
destruct (DyadicAtan.pi_bounds (fabs c)) as [[lo hi]|];
  [exact (fun h => h) | apply ziv_near_strict_ziv].
Qed.

(** Where [ziv_near_strict] returns, [Dyadic.ziv_near] returns the same:
    the goal [<body with ziv_near_strict> = Some v -> <body with
    Dyadic.ziv_near> = Some v] of a function of this file, split at its
    guards, which name neither driver, as [dir_strict] of [DyExp.v]. A
    guarded branch is the same value on both sides, or
    [pi_times_near_with] with the two drivers ([pi_times_near_strict]). *)
Local Ltac near_strict :=
  repeat match goal with
  | |- (if ?c then _ else _) = Some _ -> _ =>
      destruct c; [first [exact (fun h => h) | apply pi_times_near_strict]|]
  | |- (match ?c with Some _ => _ | None => _ end) = Some _ -> _ =>
      destruct c; [exact (fun h => h)|]
  end;
  apply ziv_near_strict_ziv.

(** ** The functions *)

(** At [|x| >= 2^54], [tn_huge]; at [|x| < 2^-27], [x] ([tn_odd]); and
    otherwise the loop. *)
Theorem atan_near_correct :
  forall x v,
  is_finite x = true -> DyadicAtan.atan_near_with ziv_near_strict x = Some v ->
  near_round (atan (B2R x)) v.
Proof.
intros x v Fx H. unfold DyadicAtan.atan_near_with in H.
rewrite (fin_not_nan x Fx) in H. cbv iota in H.
destruct (ge (fabs x) DyadicAtan.huge_atan) eqn:G0; cbv iota in H.
{ exact (tn_huge x v Fx G0 H). }
destruct (lt (fabs x) DyadicExp.tiny_near) eqn:G; cbv iota in H.
{ injection H as <-. exact (tn_odd atan x atan_opp tn_atan Fx (tn_tiny x Fx G)). }
destruct (DyadicAtan.fast_atan_near false x) eqn:F; cbv iota in H.
{ injection H as <-.
  exact (fast_atan_near_correct false x _ Fx (fast_atan_near_range x Fx G0 G) F). }
apply (ziv_near_strict_correct (DyadicAtan.ev_atan x) 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_atan_correct x n a Hn Fx Ha).
Qed.

(** [|x| > 1.0] is false on [asin_dom]; at [|x| < 2^-27], [x]
    ([tn_odd]); and otherwise the loop. *)
Theorem asin_near_correct :
  forall x v,
  is_finite x = true -> asin_dom (B2R x) -> DyadicAtan.asin_near_with ziv_near_strict x = Some v ->
  near_round (asin (B2R x)) v.
Proof.
intros x v Fx Dx H.
unfold asin_dom in Dx. unfold DyadicAtan.asin_near_with in H.
destruct (as_fabs x Fx Dx) as (Ft & Dt).
rewrite (fin_not_nan x Fx) in H. cbv iota in H.
destruct (gt (fabs x) DyadicExp.one) eqn:G1; cbv iota in H.
{ exfalso. assert (G1' : lt DyadicExp.one (fabs x) = true) by exact G1.
  apply lt_R in G1'; [|reflexivity|exact Ft].
  rewrite dexp_one_R in G1'. lra. }
destruct (lt (fabs x) DyadicAtan.tiny_asin) eqn:G2; cbv iota in H.
{ injection H as <-. exact (tn_odd asin x asin_opp tn_asin Fx (tn_tiny_asin x Fx G2)). }
destruct (DyadicAtan.fast_asin_near false x) eqn:F; cbv iota in H.
{ injection H as <-.
  exact (fast_asin_near_correct false x _ Fx (fast_asin_range x Fx G1 G2) F). }
apply (ziv_near_strict_correct (DyadicAtan.ev_asin x) 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_asin_correct x n a Hn Fx Dx Ha).
Qed.

(** [|x| > 1.0] is false on [acos_dom]; then the loop. *)
Theorem acos_near_correct :
  forall x v,
  is_finite x = true -> acos_dom (B2R x) -> DyadicAtan.acos_near_with ziv_near_strict x = Some v ->
  near_round (acos (B2R x)) v.
Proof.
intros x v Fx Dx H.
unfold acos_dom in Dx. unfold DyadicAtan.acos_near_with in H.
destruct (as_fabs x Fx Dx) as (Ft & Dt).
rewrite (fin_not_nan x Fx) in H. cbv iota in H.
destruct (gt (fabs x) DyadicExp.one) eqn:G1; cbv iota in H.
{ exfalso. assert (G1' : lt DyadicExp.one (fabs x) = true) by exact G1.
  apply lt_R in G1'; [|reflexivity|exact Ft].
  rewrite dexp_one_R in G1'. lra. }
destruct (DyadicAtan.fast_acos_near false x) eqn:F; cbv iota in H.
{ injection H as <-. exact (fast_acos_near_correct false x _ Fx (fast_acos_range x Fx G1) F). }
apply (ziv_near_strict_correct (DyadicAtan.ev_acos x) 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_acos_correct x n a Hn Fx Dx Ha).
Qed.

(** [atan2_fast_near_with ziv_near_strict], at nonzero finite [y] and
    [x]: the fast path ([fast_atan2_near_correct]), and otherwise the
    loop. *)
Local Lemma tn_atan2_fast :
  forall y x v,
  is_finite y = true -> is_finite x = true -> (B2R y <> 0)%R -> (B2R x <> 0)%R ->
  DyadicAtan.atan2_fast_near_with ziv_near_strict y x = Some v ->
  near_round (Ratan2 (B2R y) (B2R x)) v.
Proof.
intros y x v Fy Fx Y0 X0 H. unfold DyadicAtan.atan2_fast_near_with in H.
destruct (DyadicAtan.fast_atan2_near false y x) eqn:F; cbv iota in H.
{ injection H as <-. exact (fast_atan2_near_correct false y x _ Fy Fx Y0 X0 F). }
apply (ziv_near_strict_correct (DyadicAtan.ev_atan2 y x) 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_atan2_correct y x n a Hn Fy Fx Y0 X0 Ha).
Qed.

(** Where [atan2_fast_near_with ziv_near_strict] returns,
    [atan2_fast_near_with Dyadic.ziv_near] returns the same. *)
Local Lemma tn_atan2_fast_strict :
  forall y x v,
  DyadicAtan.atan2_fast_near_with ziv_near_strict y x = Some v ->
  DyadicAtan.atan2_fast_near_with Dyadic.ziv_near y x = Some v.
Proof.
intros y x v. unfold DyadicAtan.atan2_fast_near_with.
destruct (DyadicAtan.fast_atan2_near false y x); [exact (fun h => h) | apply ziv_near_strict_ziv].
Qed.

(** As [atan2_dir_post] of [DyAtan.v]: at [y = ±0] (so [x > 0]), [y],
    which is [atan2 0 x = 0]; at [x = ±0], [±π/2] by the sign of [y];
    for [x > 0], where [midpoint_quotient] finds [y / x] midway between
    two [f64]s below 2^-1021, the [f64] next to it toward zero, which rounds
    [atan (y / x)] ([midpoint_quotient_correct] of [DyAtanMidQ.v]); for
    [x > 0] and an exact quotient [q = y / x] with [|q| < 2^-27], [q],
    which rounds [atan q] ([tn_odd]); and otherwise the loop. *)
Theorem atan2_near_correct :
  forall y x v,
  is_finite y = true -> is_finite x = true -> (B2R y <> 0 \/ 0 < B2R x)%R ->
  DyadicAtan.atan2_near_with ziv_near_strict y x = Some v ->
  near_round (Ratan2 (B2R y) (B2R x)) v.
Proof.
intros y x v Fy Fx D H. unfold DyadicAtan.atan2_near_with in H.
rewrite (fin_not_nan y Fy), (fin_not_nan x Fx) in H. cbn [orb] in H.
destruct (atn_eq_zero y Fy) as (Z1 & Z2).
destruct (eq y zero) eqn:Ey0; cbv iota in H.
{ (* [y = ±0], so [x > 0] and the result is [y]. *)
  specialize (Z1 eq_refl).
  assert (Px : (0 < B2R x)%R) by (destruct D as [D|D]; [contradiction | exact D]).
  assert (Sx : Bsign x = false)
    by (destruct (Bsign x) eqn:S; [apply atn_sign_true in S; lra | reflexivity]).
  rewrite Sx in H. cbn [negb] in H. injection H as <-.
  rewrite Z1, (Ratan2_zero_y_pos _ Px), <- Z1. exact (near_exact y Fy). }
specialize (Z2 eq_refl).
rewrite (fin_neq_inf y Fy), (fin_neq_ninf y Fy), (fin_neq_inf x Fx), (fin_neq_ninf x Fx)
  in H.
cbn [orb] in H.
destruct (atn_eq_zero x Fx) as (X1 & X2).
destruct (eq x zero) eqn:Ex0; cbv iota in H.
{ (* [x = ±0]: [±π/2]. *)
  specialize (X1 eq_refl).
  assert (Sh : Bsign DyadicLog.half = false) by (vm_compute; reflexivity).
  assert (Fh : is_finite DyadicLog.half = true) by (vm_compute; reflexivity).
  destruct (atn_copysign DyadicLog.half y Sh Fh) as (Fc & Vc).
  pose proof (tn_pi_times _ v Fc H) as R.
  rewrite Vc, lc_half_R in R. rewrite X1.
  revert R. destruct (Bsign y) eqn:Sy; intros R.
  - pose proof (atn_sign_true y Sy) as Yn.
    assert (Yn' : (B2R y < 0)%R)
      by (destruct (Rle_lt_or_eq_dec _ _ Yn); [assumption | contradiction]).
    rewrite (Ratan2_zero_x_neg _ Yn').
    replace (- (PI / 2))%R with (- (1 / 2) * PI)%R by field. exact R.
  - pose proof (atn_sign_false y Sy) as Yp.
    assert (Yp' : (0 < B2R y)%R)
      by (destruct (Rle_lt_or_eq_dec _ _ Yp) as [L|L]; [assumption | contradiction (Z2 (eq_sym L))]).
    rewrite (Ratan2_zero_x_pos _ Yp').
    replace (PI / 2)%R with (1 / 2 * PI)%R by field. exact R. }
specialize (X2 eq_refl).
destruct (atn_gt_zero x Fx) as (G1 & _).
destruct (gt x zero) eqn:Gx; cbv beta iota in H.
- specialize (G1 eq_refl).
  destruct (DyadicAtan.midpoint_quotient y x) as [[f|]|] eqn:Em; cbv beta iota in H;
    [| |discriminate H].
  { (* A quotient [y / x] midway between two [f64]s below 2^-1021. *)
    injection H as <-. rewrite (Ratan2_pos_x _ _ G1).
    exact (midpoint_quotient_correct y x f Fy Fx Z2 G1 Em). }
  destruct (DyadicAtan.tiny_quotient y x) as [[q|]|] eqn:Eq; cbv beta iota in H;
    [| |discriminate H].
  + (* The exact quotient [q = y / x]. *)
    destruct (tiny_quotient_correct y x q Fy Fx G1 Eq) as (Fq & Vq & _).
    destruct (lt (fabs q) DyadicExp.tiny_near) eqn:Tq; cbv iota in H.
    * injection H as <-. rewrite (Ratan2_pos_x _ _ G1), <- Vq.
      exact (tn_odd atan q atan_opp tn_atan Fq (tn_tiny q Fq Tq)).
    * exact (tn_atan2_fast y x v Fy Fx Z2 X2 H).
  + exact (tn_atan2_fast y x v Fy Fx Z2 X2 H).
- exact (tn_atan2_fast y x v Fy Fx Z2 X2 H).
Qed.

Theorem atan_near_strict :
  forall x v, DyadicAtan.atan_near_with ziv_near_strict x = Some v -> DyadicAtan.atan_near x = Some v.
Proof. intros x v. unfold DyadicAtan.atan_near, DyadicAtan.atan_near_with. near_strict. Qed.

Theorem asin_near_strict :
  forall x v, DyadicAtan.asin_near_with ziv_near_strict x = Some v -> DyadicAtan.asin_near x = Some v.
Proof. intros x v. unfold DyadicAtan.asin_near, DyadicAtan.asin_near_with. near_strict. Qed.

Theorem acos_near_strict :
  forall x v, DyadicAtan.acos_near_with ziv_near_strict x = Some v -> DyadicAtan.acos_near x = Some v.
Proof. intros x v. unfold DyadicAtan.acos_near, DyadicAtan.acos_near_with. near_strict. Qed.

Theorem atan2_near_strict :
  forall y x v,
  DyadicAtan.atan2_near_with ziv_near_strict y x = Some v -> DyadicAtan.atan2_near y x = Some v.
Proof.
intros y x v. unfold DyadicAtan.atan2_near, DyadicAtan.atan2_near_with.
destruct (is_nan y || is_nan x); [exact (fun h => h)|].
destruct (eq y zero).
{ destruct (negb (Bsign x)); [exact (fun h => h) | apply pi_times_near_strict]. }
destruct (eq y infinity || eq y DyadicExp.neg_infinity); [apply pi_times_near_strict|].
destruct (eq x infinity); [exact (fun h => h)|].
destruct (eq x DyadicExp.neg_infinity); [apply pi_times_near_strict|].
destruct (eq x zero); [apply pi_times_near_strict|].
destruct (gt x zero); [|apply tn_atan2_fast_strict].
destruct (DyadicAtan.midpoint_quotient y x) as [[f|]|];
  [exact (fun h => h) | | exact (fun h => h)].
destruct (DyadicAtan.tiny_quotient y x) as [[q|]|];
  [| apply tn_atan2_fast_strict | exact (fun h => h)].
destruct (lt (fabs q) DyadicExp.tiny_near); [exact (fun h => h) | apply tn_atan2_fast_strict].
Qed.
