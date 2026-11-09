(** * The series and the reduction of the logarithms of the kernel at their exact points

    [atanh_series] at the point [u = 0] is the point 0: [z = u^2] is the
    point 0, so each step of its loop adds the point 0 to [1 / (2k + 1)]
    and gives a valid enclosure whose exponents stay within [2^15]
    ([lg_series_loop]), and the result is [u] times that, the point 0
    ([atanh_series_zero]). [reduce] at a dyadic [d = 2^k] finds the
    exponent [k]: the significand of [d] is [2^(p - 1)] for the precision
    [p] of the level, so its top limb is [2^63], which is below
    [SQRT_HALF]; the reduced [m = d / 2^k] is then the point 1, so
    [(m - 1) / (m + 1)] is the point 0, and so is the series of it,
    doubled ([reduce_pow2]). Unlike the lemmas of [DyLogCore.v], these
    show that the functions return. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs DyRound DyConv DyOps DyDriver DyGrow DyExpCore DyExp
  DyLogCore DyExactPoint.

Open Scope Z_scope.

(** ** Points 0 *)

(** The bounds of the point 0 have exponent 0 ([pt_exp0]). *)
Lemma ls_pt0_le : forall n a, level_ok n -> encl_pt n a 0 -> encl_le 0 a.
Proof.
intros n a Hn ((Ol & Oh & _) & L & H). unfold lo_R, hi_R in L, H. unfold encl_le.
rewrite (pt_exp0 n _ Hn Ol L), (pt_exp0 n _ Hn Oh H). lia.
Qed.

Lemma ls_min0 : Rmin (Rmin (Rmin 0 0) 0) 0 = 0%R.
Proof. unfold Rmin. repeat destruct Rle_dec; reflexivity. Qed.

Lemma ls_max0 : Rmax (Rmax (Rmax 0 0) 0) 0 = 0%R.
Proof. unfold Rmax. repeat destruct Rle_dec; reflexivity. Qed.

(** ** [atanh_series] at 0 *)

(** Each step of the loop of [atanh_series] at the point [z = 0] gives
    [1 / (2k + 1) + 0 * t]: the quotient has exponents within [2^13 +
    2^13] ([div_u64_step]), the product is the point 0, of exponent 0,
    and the sum adds [2^13] at most ([add_step]), so the exponents of
    every [t] stay within [2^15]. *)
Lemma lg_series_loop :
  forall n one_e z i t,
  level_ok n -> encl_ok n one_e -> encl_le (2 ^ 13) one_e -> encl_pt n z 0 ->
  encl_ok n t -> encl_le (2 ^ 15) t -> 2 * Z.of_nat i + 1 < 2 ^ 64 ->
  exists t',
  DyadicLog.series_loop n one_e z i t = Some t' /\ encl_ok n t' /\ encl_le (2 ^ 15) t'.
Proof.
intros n one_e z i t Hn Ho HoE Hz. revert t.
induction i as [|k IH]; intros t Ht HtE Hi.
- exists t. split; [reflexivity |]. split; assumption.
- cbn [DyadicLog.series_loop]. rewrite Nat2Z.inj_succ in Hi.
  assert (Hk : 0 < 2 * Z.of_nat k + 1 < 2 ^ 64) by lia.
  assert (So : encl_small one_e) by (apply (encl_le_small (2 ^ 13)); [lia | exact HoE]).
  assert (St : encl_small t) by (apply (encl_le_small (2 ^ 15)); [lia | exact HtE]).
  destruct (encl_div_u64_correct n one_e _ Hn Ho So Hk) as (q & Eq & _).
  destruct (div_u64_step n one_e _ q (2 ^ 13) Hn Ho HoE ltac:(lia) Hk Eq) as (Oq & LqE & _).
  destruct (pt_mul_0_l n z t Hn Hz Ht St) as (p & Ep & Hp).
  pose proof (ls_pt0_le n p Hn Hp) as LpE. destruct Hp as (Op & _ & _).
  assert (Sq : encl_small q) by (apply (encl_le_small (2 ^ 13 + 2 ^ 13)); [lia | exact LqE]).
  assert (Sp : encl_small p) by (apply (encl_le_small 0); [lia | exact LpE]).
  destruct (encl_add_correct n q p Hn Oq Op Sq Sp) as (t1 & Et1 & _).
  destruct (add_step n q p t1 _ _ Hn Oq Op LqE LpE ltac:(lia) ltac:(lia) Et1) as (Ot1 & Lt1E & _).
  rewrite Eq. cbv beta iota. rewrite Ep. cbv beta iota. rewrite Et1. cbv beta iota.
  apply IH; [exact Ot1 | | lia].
  apply (encl_le_mono (Z.max (2 ^ 13 + 2 ^ 13) 0 + 2 ^ 13)); [lia | exact Lt1E].
Qed.

(** [atanh_series] encloses [atanh 0 = 0] by the point 0 at every
    level: [0] passes both checks, [0 <= 0] and [0 <= 1/2], [z = u * u]
    is the point 0, the loop starts from [[0, 2]], of exponents within
    [2^13] ([from_f64_step]), and runs [terms n <= 821] steps
    ([lc_terms]), and [u] times its result is the point 0. *)
Lemma atanh_series_zero :
  forall n u,
  level_ok n -> encl_pt n u 0 ->
  exists a, DyadicLog.atanh_series n u = Some a /\ encl_pt n a 0.
Proof.
intros n u Hn Hu.
assert (Su : encl_small u) by (apply (encl_le_small 0); [lia | exact (ls_pt0_le n u Hn Hu)]).
pose proof Hu as ((Olo & Ohi & _) & Lu & Uu). unfold lo_R, hi_R in Lu, Uu.
assert (Fh : is_finite DyadicLog.half = true) by (vm_compute; reflexivity).
destruct (from_f64_correct n _ Hn Fh) as (h & Eh & Oh & _ & Vh). rewrite lc_half_R in Vh.
destruct (dy_zero_ok n) as (Oz & Vz & _).
assert (L1 : DyadicExp.dy_lt n (Dyadic.en_lo u) (Dyadic.dy_zero n) = false).
{ unfold DyadicExp.dy_lt. rewrite (cmp_correct n _ _ Hn Olo Oz), Lu, Vz, Rcompare_Eq by reflexivity.
  reflexivity. }
assert (L2 : DyadicExp.dy_gt n (Dyadic.en_hi u) h = false).
{ unfold DyadicExp.dy_gt. rewrite (cmp_correct n _ _ Hn Ohi Oh), Uu, Vh, Rcompare_Lt by lra.
  reflexivity. }
destruct (pt_mul_0_l n u u Hn Hu (proj1 Hu) Su) as (z & Ez & Hz).
destruct (encl_point_correct n _ Hn (proj1 one_B2R)) as (o & Eo & _).
destruct (point_step n _ o Hn Eo) as (Oo & LoE & _).
destruct (from_f64_correct n _ Hn (proj1 two_B2R)) as (w & Ew & _).
destruct (from_f64_step n _ w Hn Ew) as (Ow & LwE & Vw & _). rewrite (proj2 two_B2R) in Vw.
assert (Ot0 : encl_ok n {| Dyadic.en_lo := Dyadic.dy_zero n; Dyadic.en_hi := w |}).
{ unfold encl_ok; cbn [Dyadic.en_lo Dyadic.en_hi]. split; [exact Oz |]. split; [exact Ow |].
  rewrite Vz, Vw. lra. }
assert (Lt0E : encl_le (2 ^ 15) {| Dyadic.en_lo := Dyadic.dy_zero n; Dyadic.en_hi := w |}).
{ unfold encl_le; cbn [Dyadic.en_lo Dyadic.en_hi Dyadic.dy_zero Dyadic.dy_exp]. lia. }
pose proof (lc_terms n Hn) as Hk.
destruct (lg_series_loop n o z (Z.to_nat (DyadicLog.terms n)) _ Hn Oo LoE Hz Ot0 Lt0E
  ltac:(rewrite Z2Nat.id by lia; lia)) as (t1 & Et1 & Ot1 & Lt1E).
assert (St1 : encl_small t1) by (apply (encl_le_small (2 ^ 15)); [lia | exact Lt1E]).
destruct (pt_mul_0_l n u t1 Hn Hu Ot1 St1) as (a & Ea & Ha).
exists a. split; [| exact Ha].
unfold DyadicLog.atanh_series. rewrite Eh. cbv beta iota.
rewrite L1, L2. cbv beta iota delta [orb].
rewrite Ez. cbv beta iota. rewrite Eo. cbv beta iota. rewrite Ew. cbv beta iota.
rewrite Et1. cbv beta iota. exact Ea.
Qed.

(** ** [reduce] at a power of 2 *)

(** [reduce] at [d = 2^k] returns [k], the point 0 and [false]. *)
Lemma reduce_pow2 :
  forall n d k,
  level_ok n -> dy_ok n d -> Dyadic.dy_R d = bpow radix2 k -> Z.abs k <= 2048 ->
  exists a, DyadicLog.reduce n d = Some (k, a, false) /\ encl_pt n a 0.
Proof.
intros n d k Hn Hd Vd Hk.
pose proof (bpow_gt_0 radix2 k) as Pk.
pose proof (dprec_bounds n Hn) as Hp.
pose proof Hd as (Hm & _ & _ & _).
destruct (dy_cases n d Hn Hd) as [(_ & _ & _ & _ & V0) | (Zd & _ & B1 & B2)].
{ rewrite Vd in V0. lra. }
(* [d] is positive, so its sign bit is clear. *)
assert (Ng : Dyadic.dy_neg d = false).
{ destruct (Dyadic.dy_neg d) eqn:N; [exfalso | reflexivity].
  rewrite dy_R_eq, N in Vd. cbn [cond_Ropp] in Vd.
  assert (0 <= IZR (Limbs.val (Dyadic.dy_m d)) * bpow radix2 (Dyadic.dy_exp d))%R
    by (apply Rmult_le_pos; [apply IZR_le, val_nonneg, Hm | apply bpow_ge_0]).
  lra. }
(* [2^k] lies in [[2^(e + p - 1), 2^(e + p))] for the exponent [e] of [d]
   and the precision [p], so [k = e + p - 1], and the significand of [d]
   is [2^(p - 1)]. *)
rewrite Vd, Rabs_pos_eq in B1, B2 by lra.
apply le_bpow in B1. apply lt_bpow in B2.
assert (Ek : k = Dyadic.dy_exp d + dprec n - 1) by lia.
assert (Vm : Limbs.val (Dyadic.dy_m d) = 2 ^ (dprec n - 1)).
{ rewrite dy_R_eq, Ng in Vd. cbn [cond_Ropp] in Vd.
  replace k with ((dprec n - 1) + Dyadic.dy_exp d) in Vd by lia.
  rewrite bpow_plus, <- (IZR_pow2 (dprec n - 1)) in Vd by lia.
  apply eq_IZR, (Rmult_eq_reg_r (bpow radix2 (Dyadic.dy_exp d))); [exact Vd |].
  apply Rgt_not_eq, bpow_gt_0. }
(* Its top limb is then [2^63], below [SQRT_HALF], so [reduce] takes
   [e = b - 1 = k]. *)
assert (Tl : Limbs.limb (Dyadic.dy_m d) (n - 1) = 2 ^ 63).
{ rewrite limb_val by exact Hm. rewrite Vm. destruct (dprec_split n Hn) as [H1 _]. rewrite H1.
  rewrite Z.div_mul by (apply Z.pow_nonzero; lia). reflexivity. }
assert (Hsh : (DyadicLog.sqrt_half <=? 2 ^ 63) = false) by reflexivity.
(* [m = d 2^-k] is 1. *)
destruct (shl_correct n d (- k) Hn Hd ltac:(lia)) as (m & Em & Om & Vm1).
rewrite Vd, <- bpow_plus, Z.add_opp_diag_r in Vm1. change (bpow radix2 0) with 1%R in Vm1.
destruct (encl_point_correct n _ Hn (proj1 one_B2R)) as (o & Eo & Oo & So & Lo & Uo).
rewrite (proj2 one_B2R) in Lo, Uo. unfold lo_R, hi_R in Lo, Uo.
destruct (point_step n _ o Hn Eo) as (_ & LoE & _).
pose proof Oo as (Oolo & _ & _).
assert (Ls : DyadicExp.dy_lt n m (Dyadic.en_lo o) = false).
{ unfold DyadicExp.dy_lt. rewrite (cmp_correct n _ _ Hn Om Oolo), Vm1, Lo, Rcompare_Eq by reflexivity.
  reflexivity. }
(* The exponent of [m] is fixed by its value 1 ([grow_exp_win]). *)
assert (Xm : - 4096 <= Dyadic.dy_exp m <= 4096).
{ assert (W : grow_win 0 0 (Dyadic.dy_R m)).
  { right. rewrite Vm1, Rabs_R1. change (bpow radix2 0) with 1%R. lra. }
  destruct (grow_exp_win n m 0 0 Hn Om W); lia. }
destruct (hh_correct n m 4096 Om Xm) as (Ome & Lme & _).
assert (Sme : encl_small {| Dyadic.en_lo := m; Dyadic.en_hi := m |})
  by (apply (encl_le_small 4096); [lia | exact Lme]).
(* [num = m - 1] is the point 0. *)
destruct (encl_sub_correct n _ _ Hn Ome Oo Sme So) as (num & En & On & Ln & Un & _).
unfold lo_R, hi_R in Ln, Un; cbn [Dyadic.en_lo Dyadic.en_hi] in Ln, Un.
rewrite Vm1, Uo, Rminus_diag, dround_0 in Ln by exact Hn.
rewrite Vm1, Lo, Rminus_diag, dround_0 in Un by exact Hn.
assert (Pnum : encl_pt n num 0) by (split; [exact On | split; assumption]).
assert (Snum : encl_small num)
  by (apply (encl_le_small 0); [lia | exact (ls_pt0_le n num Hn Pnum)]).
(* [den = m + 1] is the point 2, which is in the format. *)
destruct (encl_add_correct n _ _ Hn Ome Oo Sme So) as (den & Ed & Od & Ld & _ & _).
destruct (add_step n _ _ den _ _ Hn Ome Oo Lme LoE ltac:(lia) ltac:(lia) Ed) as (_ & LdE & _).
assert (Sden : encl_small den) by (apply (encl_le_small (Z.max 4096 (2 ^ 13) + 2 ^ 13)); [lia | exact LdE]).
assert (Two : dround n false 2 = 2%R).
{ change 2%R with (bpow radix2 1). apply dround_id; [exact Hn | apply grow_bpow_format, Hn]. }
unfold lo_R at 2 3 in Ld; cbn [Dyadic.en_lo] in Ld.
rewrite Vm1, Lo in Ld. replace (1 + 1)%R with 2%R in Ld by ring. rewrite Two in Ld.
(* [s = num / den] is the point 0, and so are its series and its double. *)
destruct (encl_div_correct n num den Hn On Od Snum Sden ltac:(left; rewrite Ld; lra))
  as (s & Es & Os & Lsv & Usv & _).
assert (Ln0 : lo_R num = 0%R) by exact Ln. assert (Un0 : hi_R num = 0%R) by exact Un.
rewrite Ln0, Un0 in Lsv, Usv. unfold Rdiv in Lsv, Usv. rewrite !Rmult_0_l in Lsv, Usv.
rewrite ls_min0, dround_0 in Lsv by exact Hn. rewrite ls_max0, dround_0 in Usv by exact Hn.
destruct (atanh_series_zero n s Hn (conj Os (conj Lsv Usv))) as (a & Ea & Ha).
assert (Sa : encl_small a) by (apply (encl_le_small 0); [lia | exact (ls_pt0_le n a Hn Ha)]).
destruct Ha as (Oa & La & Ua).
destruct (encl_shl_correct n a 1 Hn Oa Sa ltac:(lia)) as (a2 & Ea2 & Oa2 & La2 & Ua2 & _).
rewrite La, Rmult_0_l in La2. rewrite Ua, Rmult_0_l in Ua2.
exists a2. split; [| split; [exact Oa2 | split; assumption]].
unfold DyadicLog.reduce. rewrite Ng, Zd. cbv beta iota zeta delta [orb].
rewrite Tl, Hsh. cbv beta iota.
replace (Dyadic.dy_exp d + 64 * Z.of_nat n - 1) with k by (unfold dprec in Ek; lia).
replace (2048 <? Z.abs k) with false by (symmetry; apply Z.ltb_ge; lia). cbv beta iota.
rewrite Em. cbv beta iota. rewrite Eo. cbv beta iota. rewrite Ls. cbv beta iota.
rewrite En. cbv beta iota. rewrite Ed. cbv beta iota. rewrite Es. cbv beta iota.
rewrite Ea. cbv beta iota. rewrite Ea2. reflexivity.
Qed.
