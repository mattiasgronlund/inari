(** * ln, log2 and acosh of the kernel at their exact results

    At each level, [ev_ln] and [ev_acosh] of [DyadicLog] at [x = 1], and
    [ev_log2] at the [f64] [x = 2^k], return the point of the exact result,
    by the point lemmas of [DyExactPoint.v] and [DyLogSeries.v]. At
    [x = 2^k], [reduce] gives the exponent [k] and the point 0
    ([reduce_pow2]). So at [x = 1], [ln_dy] adds that point 0 to
    [0 h + 0 l], where [mul_int] by 0 gives the point 0 ([ev_ln_one]); and
    [ev_log2] divides the point 0 by the enclosure [c = [h, h] + l] of
    ln 2, whose lower bound is at least the positive [h] of [DyConst.v],
    and adds the quotient, the point 0, to [1 k], the point [k]
    ([ev_log2_exact]). At [x = 1], [ev_acosh] takes the square root of
    [(x - 1) (x + 1)], the point 0, and, as [x] is at most
    [ACOSH_SERIES_MAX], divides it by [x] and sums the series of atanh at
    the quotient, the point 0, which gives the point 0
    ([atanh_series_zero], [ev_acosh_one]). *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary LogReal DyRound DyConv DyOps DyDriver
  DyGrow DyConst DyExpCore DyExpRules DyExp DyHyp DyLogRules DyLogTiny DyLogCore DyLog DyLogHyp
  DyPowExact DyPown DyExactDriver PowFactor ExpIrrational ExpQuadratic DyExactPoint DyLogSeries.

Open Scope R_scope.

(** ** The split of ln 2 *)

(** A dyadic number that [dc_dy_okb] accepts is positive: its exponent
    plus [dc_K] is not negative and its significand is at least
    [2^(dprec n - 1)]. *)
Lemma lp_dc_dy_pos : forall n d, level_ok n -> dc_dy_okb n d = true -> 0 < Dyadic.dy_R d.
Proof.
intros n d Hn H.
destruct (dc_dy_okb_correct n d H) as (_ & V). rewrite V.
apply Rmult_lt_0_compat; [| apply bpow_gt_0]. apply IZR_lt.
unfold dc_dy_okb in H. repeat rewrite Bool.andb_true_iff in H.
destruct H as [[[[[[_ _] _] _] H5] _] H7]. apply Z.leb_le in H5, H7.
pose proof (dprec_bounds n Hn) as Hp.
unfold dc_scaled. apply Z.mul_pos_pos.
- apply Z.pow_pos_nonneg; lia.
- apply (Z.lt_le_trans _ (2 ^ (dprec n - 1))); [apply Z.pow_pos_nonneg; lia | exact H5].
Qed.

(** [h] and the lower bound of [l] of [ln2 n = Some (h, l)] are positive. *)
Lemma lp_ln2_pos :
  forall n h l, level_ok n -> DyadicConsts.ln2 n = Some (h, l) ->
  0 < Dyadic.dy_R h /\ 0 < lo_R l.
Proof.
intros n h l Hn E. destruct (dc_level n Hn) as [H _]. rewrite E in H.
unfold dc_split_okb in H. cbv beta iota zeta in H. repeat rewrite Bool.andb_true_iff in H.
destruct H as [[[[[[[[[[Hh Hlo] _] _] _] _] _] _] _] _] _].
split; [exact (lp_dc_dy_pos n h Hn Hh) | exact (lp_dc_dy_pos n _ Hn Hlo)].
Qed.

(** ** The points *)

(** [ev_ln] encloses [ln 1 = 0] by the point 0 at every level. *)
Lemma ev_ln_one :
  forall n, level_ok n ->
  exists a, DyadicLog.ev_ln DyadicExp.one n = Some a /\ encl_ok n a /\ lo_R a = 0 /\ hi_R a = 0.
Proof.
intros n Hn.
destruct one_B2R as (F1 & V1).
destruct (from_f64_correct n DyadicExp.one Hn F1) as (d & Ed & Od & _ & Vd).
assert (Vd' : Dyadic.dy_R d = bpow radix2 0) by (rewrite Vd, V1; reflexivity).
(* [reduce] at [1 = 2^0]: the exponent 0 and the point 0 *)
destruct (reduce_pow2 n d 0 Hn Od Vd' ltac:(lia)) as (b & Er & Pb).
destruct (dc_level n Hn) as [Hsplit _].
destruct (DyadicConsts.ln2 n) as [[h l]|] eqn:El; [| discriminate Hsplit].
destruct (ln2_correct n h l Hn El) as (Hh & Heh & Ol & HEl & _).
destruct (hh_correct n h (2 ^ 13) Hh Heh) as (Ohh & Lhh & _).
assert (Shh : encl_small {| Dyadic.en_lo := h; Dyadic.en_hi := h |})
  by (apply (encl_le_small (2 ^ 13)); [lia | exact Lhh]).
assert (Sl : encl_small l) by (apply (encl_le_small (2 ^ 14)); [lia | exact HEl]).
(* [0 h] and [0 l], and their sum, are the point 0 *)
destruct (pt_mul_int_0 n _ Hn Ohh Shh) as (k1 & E1 & P1).
destruct (pt_mul_int_0 n l Hn Ol Sl) as (k2 & E2 & P2).
assert (W0 : grow_win (-4096) 4096 0) by (left; reflexivity).
assert (F0 : generic_format radix2 (FLX_exp (dprec n)) (0 + 0))
  by (rewrite Rplus_0_r; apply generic_format_0).
destruct (pt_add n k1 k2 0 0 Hn P1 P2 (pt_small n k1 0 Hn P1 W0) (pt_small n k2 0 Hn P2 W0) F0)
  as (k & Ek & Pk).
rewrite Rplus_0_r in Pk.
destruct (pt_add n k b 0 0 Hn Pk Pb (pt_small n k 0 Hn Pk W0) (pt_small n b 0 Hn Pb W0) F0)
  as (a & Ea & Pa).
rewrite Rplus_0_r in Pa.
exists a. split; [| exact Pa].
unfold DyadicLog.ev_ln, DyadicLog.ln_dy.
rewrite Ed; cbv beta iota. rewrite Er; cbv beta iota. rewrite El; cbv beta iota.
rewrite E1; cbv beta iota. rewrite E2; cbv beta iota. rewrite Ek; cbv beta iota.
exact Ea.
Qed.

(** [ev_log2 x] encloses [log2 x = k] by the point [k] at every level, at
    the [f64] [x = 2^k]. *)
Lemma ev_log2_exact :
  forall (x : f64) (k : Z) n,
  is_finite x = true -> B2R x = powerRZ 2 k -> (-1074 <= k <= 1023)%Z -> level_ok n ->
  exists a, DyadicLog.ev_log2 x n = Some a /\ encl_ok n a /\ lo_R a = IZR k /\ hi_R a = IZR k.
Proof.
intros x k n Fx Vx Hk Hn.
destruct (from_f64_correct n x Hn Fx) as (d & Ed & Od & _ & Vd).
assert (Vd' : Dyadic.dy_R d = bpow radix2 k) by (rewrite Vd, Vx, bpow_powerRZ; reflexivity).
(* [reduce] at [2^k]: the exponent [k] and the point 0 *)
destruct (reduce_pow2 n d k Hn Od Vd' ltac:(lia)) as (b & Er & Pb).
destruct (dc_level n Hn) as [Hsplit _].
destruct (DyadicConsts.ln2 n) as [[h l]|] eqn:El; [| discriminate Hsplit].
destruct (ln2_correct n h l Hn El) as (Hh & Heh & Ol & HEl & Hhl).
destruct (hh_correct n h (2 ^ 13) Hh Heh) as (Ohh & Lhh & _).
assert (Shh : encl_small {| Dyadic.en_lo := h; Dyadic.en_hi := h |})
  by (apply (encl_le_small (2 ^ 13)); [lia | exact Lhh]).
assert (Sl : encl_small l) by (apply (encl_le_small (2 ^ 14)); [lia | exact HEl]).
destruct (encl_add_correct n _ l Hn Ohh Ol Shh Sl) as (c & Ec & Oc & Lc & _).
destruct (split_sum n h l c (ln 2) Hn Hh Heh Ol HEl Hhl Ec) as (_ & LEc & _).
assert (Sc : encl_small c) by (apply (encl_le_small (2 ^ 15)); [lia | exact LEc]).
(* The lower bound of [c] is [h + lo l] rounded down, at least [h], which
   is in the format, and so positive. *)
destruct (lp_ln2_pos n h l Hn El) as (Ph & Pl).
assert (Pc : 0 < lo_R c).
{ rewrite Lc. change (lo_R {| Dyadic.en_lo := h; Dyadic.en_hi := h |}) with (Dyadic.dy_R h).
  apply (Rlt_le_trans _ (dround n false (Dyadic.dy_R h))).
  - rewrite (dround_id n false _ Hn (dy_format n h Hn Hh)). exact Ph.
  - apply dround_le; [exact Hn | lra]. }
(* [0 / c] is the point 0, and [1 * k] the point [k] *)
destruct (pt_div_0_l n b c Hn Pb Oc Sc (or_introl Pc)) as (r & Erd & Pr).
destruct one_B2R as (F1 & V1).
destruct (pt_point n DyadicExp.one Hn F1) as (p1 & Ep & Pp & Sp).
rewrite V1 in Pp.
assert (Hk64 : (Z.abs k < 2 ^ 64)%Z) by lia.
assert (Fk : generic_format radix2 (FLX_exp (dprec n)) (1 * IZR k))
  by (rewrite Rmult_1_l; exact (pt_format_int n k Hn Hk64)).
assert (Wk : grow_win (-4096) 4096 (1 * IZR k)) by (rewrite Rmult_1_l; exact (pt_win_int k Hk64)).
destruct (pt_mul_int n p1 1 k Hn Pp Sp Hk64 Fk Wk) as (kk & Ek & Pk).
rewrite Rmult_1_l in Pk.
assert (Fk0 : generic_format radix2 (FLX_exp (dprec n)) (IZR k + 0))
  by (rewrite Rplus_0_r; exact (pt_format_int n k Hn Hk64)).
destruct (pt_add n kk r (IZR k) 0 Hn Pk Pr (pt_small n kk (IZR k) Hn Pk (pt_win_int k Hk64))
            (pt_small n r 0 Hn Pr (or_introl eq_refl)) Fk0) as (a & Ea & Pa).
rewrite Rplus_0_r in Pa.
exists a. split; [| exact Pa].
unfold DyadicLog.ev_log2.
rewrite Ed; cbv beta iota. rewrite Er; cbv beta iota. rewrite El; cbv beta iota.
rewrite Ec; cbv beta iota. rewrite Erd; cbv beta iota. rewrite Ep; cbv beta iota.
rewrite Ek; cbv beta iota.
exact Ea.
Qed.

(** [ev_acosh] encloses [acosh 1 = 0] by the point 0 at every level. *)
Lemma ev_acosh_one :
  forall n, level_ok n ->
  exists a, DyadicLog.ev_acosh DyadicExp.one n = Some a /\ encl_ok n a /\
    lo_R a = 0 /\ hi_R a = 0.
Proof.
intros n Hn.
destruct one_B2R as (F1 & V1).
(* [px] and [one_e] are both the point 1 *)
destruct (pt_point n DyadicExp.one Hn F1) as (px & Ep & Pp & Sp).
rewrite V1 in Pp.
assert (F0 : generic_format radix2 (FLX_exp (dprec n)) (1 - 1))
  by (replace (1 - 1) with 0 by ring; apply generic_format_0).
destruct (pt_sub n px px 1 1 Hn Pp Pp Sp Sp F0) as (xm & Exm & Pxm).
replace (1 - 1) with 0 in Pxm by ring.
assert (F2 : generic_format radix2 (FLX_exp (dprec n)) (1 + 1))
  by (replace (1 + 1) with (IZR 2) by (cbn; ring); apply pt_format_int; [exact Hn | lia]).
destruct (pt_add n px px 1 1 Hn Pp Pp Sp Sp F2) as (xp & Exp & Pxp).
assert (Sxp : encl_small xp).
{ apply (pt_small n xp (1 + 1) Hn Pxp).
  replace (1 + 1) with (IZR 2) by (cbn; ring). apply pt_win_int. lia. }
(* [(x - 1) (x + 1)] and its square root are the point 0 *)
destruct (pt_mul_0_l n xm xp Hn Pxm (proj1 Pxp) Sxp) as (p & Epm & Ppm).
assert (W0 : grow_win (-4096) 4096 0) by (left; reflexivity).
assert (Fs : generic_format radix2 (FLX_exp (dprec n)) (sqrt 0))
  by (rewrite sqrt_0; apply generic_format_0).
destruct (pt_sqrt n p 0 Hn Ppm (pt_small n p 0 Hn Ppm W0) (Rle_refl 0) Fs) as (r & Es & Pr).
rewrite sqrt_0 in Pr.
assert (Hle : le DyadicExp.one DyadicLog.acosh_series_max = true) by (vm_compute; reflexivity).
(* [u = 0 / x], the point 0, and the series at it *)
assert (Lp : 0 < lo_R px) by (destruct Pp as (_ & L & _); rewrite L; lra).
destruct (pt_div_0_l n r px Hn Pr (proj1 Pp) Sp (or_introl Lp)) as (u & Eu & Pu).
destruct (atanh_series_zero n u Hn Pu) as (a & Ea & Pa).
exists a. split; [| exact Pa].
unfold DyadicLog.ev_acosh.
rewrite Ep; cbv beta iota. rewrite Exm; cbv beta iota. rewrite Exp; cbv beta iota.
rewrite Epm; cbv beta iota. rewrite Es; cbv beta iota. rewrite Hle; cbv beta iota.
rewrite Eu; cbv beta iota.
exact Ea.
Qed.
