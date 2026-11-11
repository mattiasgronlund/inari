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
    rounds it toward zero ([to_f64_mid] of [MidRound.v]). That is the
    path at [x >= 2^996] ([midpoint_quotient_dyadic_correct]). Below it,
    [2y] is exact, [exact_div] returns [q] only if [q = 2y / x]
    ([exact_div_correct] of [AtanExactDiv.v]), and below 2^-1021 the bits
    of [q] without the sign are [|q|] in units of 2^-1074, so an odd last
    bit makes [y / x] an odd multiple of 2^-1075, and [q] with that bit
    cleared, halved exactly, is the [f64] next to [y / x] toward zero. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding NearF64 NearAtanMid DyRound MidRound MidQuot
  AtanExactDiv.

Open Scope R_scope.

(** [B2R l] of an [f64] literal [l], as [m * 2^e] (as in [FastExp.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** Below 2^53 the bits [c] of an [f64] of sign bit 0 are its value in
    units of 2^-1074: the biased exponent is 0 or 1, both of scale
    2^-1074, and the integral significand is [c] (as
    [FastRoundSubBits.small_bits], which stops at 2^52). *)
Local Lemma magnitude_small :
  forall c, (0 <= c < 2^53)%Z -> magnitude c = IZR c * bpow radix2 (-1074).
Proof.
intros c Hc.
assert (Hm : mant c = c /\ expo c = (-1074)%Z).
{ unfold mant, expo. case Z.eqb_spec; intros E; split; zlia. }
unfold magnitude, F2R. cbn [Fnum Fexp]. rewrite (proj1 Hm), (proj2 Hm). reflexivity.
Qed.

(** For finite [y <> 0] and [x > 0], an [f64] that
    [midpoint_quotient_dyadic] returns is [atan (y / x)] rounded to
    nearest. *)
Lemma midpoint_quotient_dyadic_correct :
  forall y x f,
  is_finite y = true -> is_finite x = true -> B2R y <> 0 -> 0 < B2R x ->
  DyadicAtan.midpoint_quotient_dyadic y x = Some (Some f) ->
  near_round (atan (B2R y / B2R x)) f.
Proof.
intros y x f Fy Fx Zy Px H.
unfold DyadicAtan.midpoint_quotient_dyadic in H.
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

(** For finite [y <> 0] and [x > 0], an [f64] that [midpoint_quotient]
    returns is [atan (y / x)] rounded to nearest: at [x >= 2^996] by
    [midpoint_quotient_dyadic_correct], and below from [exact_div_correct]
    at [2y], and the bits of the quotient. *)
Lemma midpoint_quotient_correct :
  forall y x f,
  is_finite y = true -> is_finite x = true -> B2R y <> 0 -> 0 < B2R x ->
  DyadicAtan.midpoint_quotient y x = Some (Some f) ->
  near_round (atan (B2R y / B2R x)) f.
Proof.
intros y x f Fy Fx Zy Px H.
unfold DyadicAtan.midpoint_quotient in H.
destruct (ge (mul (fabs y) DyadicAtan.two_1021) x) eqn:G1021; [discriminate H|].
destruct (ge x DyadicAtan.two_996) eqn:G996.
{ exact (midpoint_quotient_dyadic_correct y x f Fy Fx Zy Px H). }
(* Below 2^996: the checks give [|y| 2^1021 < x < 2^996]. *)
assert (F1021 : is_finite DyadicAtan.two_1021 = true) by (vm_compute; reflexivity).
assert (F996 : is_finite DyadicAtan.two_996 = true) by (vm_compute; reflexivity).
assert (Fm1021 : is_finite DyadicAtan.two_m1021 = true) by (vm_compute; reflexivity).
assert (P1021 : 0 < B2R DyadicAtan.two_1021) by (rewrite two_1021_R; apply bpow_gt_0).
pose proof (ge_mul_false y x _ Fy Fx F1021 P1021 G1021) as Hyx.
pose proof (ge_false x _ Fx F996 G996) as Hx.
rewrite two_1021_R in Hyx. rewrite two_996_R in Hx.
assert (Hy2 : 2 * Rabs (B2R y) < B2R x).
{ assert (B2 : 2 <= bpow radix2 1021) by (change 2 with (bpow radix2 1); apply bpow_le; lia).
  pose proof (Rabs_pos (B2R y)). nra. }
(* [2 y] is exact: it is [y]'s integral significand at the next exponent,
   below [x], so below 2^1024. *)
assert (R2 : B2R DyadicExp.two = 2) by (lit_B2R; cbn [bpow radix_val radix2]; lra).
assert (F2 : is_finite DyadicExp.two = true) by (vm_compute; reflexivity).
assert (Gt : generic_format radix2 fexp64 (B2R DyadicExp.two * B2R y)).
{ rewrite R2.
  assert (Hy : FLT_format radix2 (SpecFloat.emin 53 1024) 53 (B2R y))
    by (apply FLT_format_B2R; unfold Prec_gt_0; lia).
  destruct Hy as [[my ey] E1 E2 E3].
  change (SpecFloat.emin 53 1024) with (-1074)%Z in E3.
  apply generic_format_FLT, (FLT_spec _ _ _ _ (Float radix2 my (ey + 1))).
  - rewrite E1. unfold F2R; cbn [Fnum Fexp]. rewrite bpow_plus.
    change (bpow radix2 1) with 2. ring.
  - exact E2.
  - cbn [Fexp] in E3 |- *. lia. }
pose proof (Bmult_correct 53 1024 _ _ mode_NE DyadicExp.two y) as Hm.
change (SpecFloat.fexp 53 1024) with fexp64 in Hm. cbn [round_mode] in Hm.
rewrite (round_generic _ _ _ _ Gt), R2 in Hm.
rewrite Rlt_bool_true in Hm.
2:{ rewrite Rabs_mult, (Rabs_pos_eq 2) by lra.
    apply Rlt_trans with (bpow radix2 996); [lra | apply bpow_lt; lia]. }
destruct Hm as (Rt & Ft & _).
change (Bmult mode_NE DyadicExp.two y) with (mul DyadicExp.two y) in Rt, Ft.
rewrite F2, Fy in Ft. cbn [andb] in Ft.
(* The quotient [q = 2 y / x]. *)
destruct (DyadicAtan.exact_div false (mul DyadicExp.two y) x) as [q|] eqn:Eq;
  cbv beta iota in H; [|discriminate H].
assert (Bt : Rabs (B2R (mul DyadicExp.two y)) < B2R x < bpow radix2 996).
{ rewrite Rt, Rabs_mult, (Rabs_pos_eq 2) by lra. split; lra. }
destruct (exact_div_correct false _ x q Ft Fx Bt Eq) as (Fq & Rq2).
rewrite Rt in Rq2.
match type of H with context [if ?c then _ else _] => destruct c eqn:C end;
  [|discriminate H].
cbv beta iota in H. injection H as <-.
apply andb_prop in C as [Cl Cb].
assert (Hq : Rabs (B2R q) < bpow radix2 (-1021)).
{ unfold Model.lt, Model.fabs in Cl.
  rewrite Bltb_correct in Cl by (rewrite ?is_finite_Babs; assumption).
  rewrite B2R_Babs, two_m1021_R in Cl.
  destruct (Rlt_le_dec (Rabs (B2R q)) (bpow radix2 (-1021))) as [L|L]; [exact L|].
  rewrite Rlt_bool_false in Cl by exact L. discriminate Cl. }
(* The bits of [q]: [sign_bit (Bsign q) + c], with [c] its magnitude in
   units of 2^-1074, below 2^53, and odd. *)
destruct (to_bits_finite q Fq) as (c & Hc & Eb).
assert (Rq : B2R q = if Bsign q then - magnitude c else magnitude c).
{ destruct (from_bits_finite (Bsign q) c Hc) as (_ & _ & R).
  rewrite <- Eb, from_to_bits in R. exact R. }
pose proof (proj1 (proj1 (magnitude_bounds c (proj1 Hc)))) as M0.
assert (Ma : Rabs (B2R q) = magnitude c).
{ rewrite Rq. destruct (Bsign q); [rewrite Rabs_Ropp|]; apply Rabs_pos_eq; exact M0. }
assert (Hc53 : (c < 2^53)%Z).
{ destruct (Z.eq_dec (c / 2^52) 0) as [E0|E0]; [zlia|].
  pose proof (proj2 (magnitude_bounds c (proj1 Hc)) E0) as Mge.
  assert (L : bpow radix2 (c / 2^52 - 1023) < bpow radix2 (-1021)) by lra.
  apply lt_bpow in L. zlia. }
assert (Hodd : (c mod 2 = 1)%Z).
{ apply Z.eqb_eq in Cb. rewrite Eb in Cb.
  change (Z.land (sign_bit (Bsign q) + c) 1)
    with (Z.land (sign_bit (Bsign q) + c) (Z.ones 1)) in Cb.
  rewrite Z.land_ones in Cb by lia.
  revert Cb. unfold sign_bit. destruct (Bsign q); intros Cb; zlia. }
assert (Hk : exists k, c = (2 * k + 1)%Z /\ (0 <= k < 2^52)%Z) by (exists (c / 2)%Z; zlia).
destruct Hk as (k & Ek & Hk).
(* [f] is the [f64] of bits [sign_bit (Bsign q) + 2 k], [(2 k) 2^-1074]
   with the sign of [q], times [1/2], which is exact. *)
rewrite Eb.
replace (sign_bit (Bsign q) + c - 1)%Z with (sign_bit (Bsign q) + 2 * k)%Z by lia.
assert (Hk2 : (0 <= 2 * k < 2047 * 2^52)%Z) by zlia.
destruct (from_bits_finite (Bsign q) (2 * k) Hk2) as (Fg & Sg & Rg).
rewrite magnitude_small in Rg by zlia.
revert Fg Sg Rg. generalize (from_bits (sign_bit (Bsign q) + 2 * k)) as g.
intros g Fg Sg Rg.
assert (Rh : B2R Model.half = / 2) by (lit_B2R; cbn [bpow radix_val radix2]; lra).
assert (Fh : is_finite Model.half = true) by (vm_compute; reflexivity).
assert (Sh : Bsign Model.half = false) by (vm_compute; reflexivity).
assert (Vg : B2R g * B2R Model.half =
  IZR (if Bsign q then - k else k) * bpow radix2 (-1074)).
{ rewrite Rg, Rh, mult_IZR. destruct (Bsign q); [rewrite opp_IZR|]; field. }
assert (Gf : generic_format radix2 fexp64 (B2R g * B2R Model.half)).
{ rewrite Vg. apply generic_format_FLT.
  apply (FLT_spec _ _ _ _ (Float radix2 (if Bsign q then - k else k) (-1074)));
    [reflexivity | |].
  - cbn [Fnum]. change (Zpower radix2 53) with (2 ^ 53)%Z.
    destruct (Bsign q); rewrite ?Z.abs_opp, Z.abs_eq by lia; zlia.
  - cbn [Fexp]. lia. }
pose proof (Bmult_correct 53 1024 _ _ mode_NE g Model.half) as Hm.
change (SpecFloat.fexp 53 1024) with fexp64 in Hm. cbn [round_mode] in Hm.
rewrite (round_generic _ _ _ _ Gf) in Hm.
rewrite Rlt_bool_true in Hm.
2:{ rewrite Rabs_mult, Rh, (Rabs_pos_eq (/ 2)) by lra.
    assert (Lg : Rabs (B2R g) < bpow radix2 1024) by apply abs_B2R_lt_emax.
    pose proof (Rabs_pos (B2R g)). lra. }
destruct Hm as (Rf & Ff & Sf).
change (Bmult mode_NE g Model.half) with (mul g Model.half) in Rf, Ff, Sf.
rewrite Fg, Fh in Ff. cbn [andb] in Ff.
assert (Sf' : Bsign (mul g Model.half) = Bsign q).
{ rewrite Sf, Sg, Sh by (revert Ff; destruct (mul g Model.half); easy).
  apply Bool.xorb_false_r. }
(* [y / x = q / 2 = (k + 1/2) 2^-1074] with the sign of [q], the midpoint
   between [f] and the next [f64] away from zero. *)
assert (B : bpow radix2 (-1074) = 2 * bpow radix2 (-1075)).
{ replace (-1074)%Z with (1 + -1075)%Z by lia. rewrite bpow_plus.
  change (bpow radix2 1) with 2. reflexivity. }
assert (Hyq : B2R y / B2R x = B2R q / 2) by (rewrite Rq2; field; lra).
pose proof (Rabs_def2 _ _ Hq) as (Hq1 & Hq2).
assert (Ic : IZR c = 2 * IZR k + 1) by (rewrite Ek, plus_IZR, mult_IZR; reflexivity).
rewrite magnitude_small, Ic in Rq by zlia.
rewrite Vg in Rf.
destruct (Bsign q) eqn:Sq; rewrite ?opp_IZR in Rf.
- apply near_atan_mid_neg; [exact Ff | exact Sf' | |]; rewrite Hyq; [|lra].
  rewrite Rq, Rf. lra.
- apply near_atan_mid; [exact Ff | exact Sf' | |]; rewrite Hyq; [|lra].
  rewrite Rq, Rf. lra.
Qed.
