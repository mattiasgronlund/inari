(** * The evaluation of [2^x] of the kernel at an integer [x]

    At an [f64] [x = m] with [m] an integer, [ev_exp2] computes
    [y = (m - x) ln 2] as the point 0, since the enclosure [m - x] is the
    point 0 and 0 times any valid enclosure is 0 ([pt_mul_0_l] of
    [DyExactPoint.v]). [scaled] keeps [y] as it is, as [y] is not
    negative. The series of [exp_neg] at the point [s = 0] is the point
    0: each step of its loop gives the point [1 - 0 t / i = 1], so that
    the loop ends at a valid enclosure [t] ([xp_series_loop]), and the
    series is [s t = 0] ([xp_series]). So [exp_neg] gives the point
    [1 - 0 = 1], which its squarings keep ([xp_square_loop],
    [xp_exp_neg]), and the shift by [m] gives the point [2^m]
    ([xp_scaled]). So [ev_exp2] encloses [2^m] by the point [2^m] at
    every level ([ev_exp2_exact]). *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary ExpReal DyRound DyConv DyOps DyDriver
  DyGrow DyConst DyExpCore DyExp DyExactPoint.

Open Scope R_scope.

(** The format of the bounds at level [n]. *)
Local Notation fmt n := (generic_format radix2 (FLX_exp (dprec n))).

(** ** The points 0 and 1 *)

Lemma xp_win_0 : grow_win (-4096) 4096 0.
Proof. left. reflexivity. Qed.

Lemma xp_win_1 : grow_win (-4096) 4096 1.
Proof. change 1 with (bpow radix2 0). apply pt_win_bpow. lia. Qed.

Lemma xp_fmt_1 : forall n, level_ok n -> fmt n 1.
Proof. intros n Hn. change 1 with (bpow radix2 0). exact (pt_format_bpow n 0 Hn). Qed.

(** [j <= 16] and [K <= 182] at every level. *)
Lemma xp_params :
  forall n,
  (0 <= fst (DyadicExp.params n) <= 16)%Z /\ (0 <= snd (DyadicExp.params n) <= 182)%Z.
Proof.
intros n. unfold DyadicExp.params.
repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb a b) end;
  cbn [fst snd]; lia.
Qed.

(** ** [series] and [exp_neg] at the point 0 *)

(** Each step of the loop of [series] at the point [s = 0] gives
    [1 - 0 * t / i], the point 1. *)
Lemma xp_series_loop :
  forall n one_e s i t,
  level_ok n -> encl_pt n one_e 1 -> encl_small one_e -> encl_pt n s 0 ->
  encl_ok n t -> encl_small t -> (Z.of_nat i < 2 ^ 64)%Z ->
  exists t', DyadicExp.series_loop n one_e s i t = Some t' /\ encl_ok n t' /\ encl_small t'.
Proof.
intros n one_e s i. induction i as [|i IH]; intros t Hn Ho So Hs Ht St Hi.
- exists t. split; [reflexivity | split; assumption].
- destruct i as [|i].
  + exists t. split; [reflexivity | split; assumption].
  + cbn [DyadicExp.series_loop].
    destruct (pt_mul_0_l n s t Hn Hs Ht St) as (q & Eq & Hq).
    assert (Sq : encl_small q) by exact (pt_small n q 0 Hn Hq xp_win_0).
    assert (Hk : (0 < Z.of_nat (S (S i)) < 2 ^ 64)%Z) by lia.
    assert (F0 : fmt n (0 / IZR (Z.of_nat (S (S i)))))
      by (unfold Rdiv; rewrite Rmult_0_l; apply generic_format_0).
    destruct (pt_div_u64 n q 0 (Z.of_nat (S (S i))) Hn Hq Sq Hk F0) as (q' & Eq' & Hq').
    replace (0 / IZR (Z.of_nat (S (S i)))) with 0 in Hq' by (unfold Rdiv; ring).
    assert (Sq' : encl_small q') by exact (pt_small n q' 0 Hn Hq' xp_win_0).
    assert (F1 : fmt n (1 - 0)) by (rewrite Rminus_0_r; exact (xp_fmt_1 n Hn)).
    destruct (pt_sub n one_e q' 1 0 Hn Ho Hq' So Sq' F1) as (t' & Et' & Ht').
    rewrite Rminus_0_r in Ht'.
    assert (St' : encl_small t') by exact (pt_small n t' 1 Hn Ht' xp_win_1).
    assert (Hi' : (Z.of_nat (S i) < 2 ^ 64)%Z) by lia.
    rewrite Eq, Eq', Et'. cbv beta iota.
    exact (IH t' Hn Ho So Hs (proj1 Ht') St' Hi').
Qed.

(** [series n s k] at the point [s = 0] is [s t] for the valid
    enclosure [t] that the loop ends at, the point 0. *)
Lemma xp_series :
  forall n s k,
  level_ok n -> encl_pt n s 0 -> (0 <= k < 2 ^ 64)%Z ->
  exists u, DyadicExp.series n s k = Some u /\ encl_pt n u 0.
Proof.
intros n s k Hn Hs Hk. unfold DyadicExp.series.
destruct (pt_point n DyadicExp.one Hn (proj1 one_B2R)) as (one_e & Eo & Ho & So).
rewrite (proj2 one_B2R) in Ho.
destruct (from_f64_correct n DyadicExp.one Hn (proj1 one_B2R)) as (hi & Eh & Oh & Sh & Vh).
rewrite (proj2 one_B2R) in Vh.
destruct (dy_zero_ok n) as (Oz & Vz & Sz).
(* The start [t = [0, 1]] of the loop. *)
assert (Ot : encl_ok n {| Dyadic.en_lo := Dyadic.dy_zero n; Dyadic.en_hi := hi |}).
{ unfold encl_ok; cbn [Dyadic.en_lo Dyadic.en_hi]. rewrite Vz, Vh. split; [exact Oz |].
  split; [exact Oh | lra]. }
assert (St : encl_small {| Dyadic.en_lo := Dyadic.dy_zero n; Dyadic.en_hi := hi |})
  by (split; assumption).
assert (Hi : (Z.of_nat (Z.to_nat k) < 2 ^ 64)%Z) by (rewrite Z2Nat.id; lia).
destruct (xp_series_loop n one_e s (Z.to_nat k) _ Hn Ho So Hs Ot St Hi) as (t & Et & Ot' & St').
rewrite Eo, Eh. cbv beta iota. rewrite Et. cbv beta iota.
exact (pt_mul_0_l n s t Hn Hs Ot' St').
Qed.

Lemma xp_square_loop :
  forall n j e,
  level_ok n -> encl_pt n e 1 ->
  exists e', DyadicExp.square_loop n j e = Some e' /\ encl_pt n e' 1.
Proof.
intros n j. induction j as [|j IH]; intros e Hn He.
- exists e. split; [reflexivity | exact He].
- cbn [DyadicExp.square_loop].
  assert (Se : encl_small e) by exact (pt_small n e 1 Hn He xp_win_1).
  assert (F1 : fmt n (1 * 1)) by (rewrite Rmult_1_r; exact (xp_fmt_1 n Hn)).
  destruct (pt_mul n e e 1 1 Hn He He Se Se F1) as (e' & Ee & He').
  rewrite Rmult_1_r in He'. rewrite Ee. cbv beta iota.
  exact (IH e' Hn He').
Qed.

(** [exp_neg] at the point 0 is the point [1 - 0 = 1], squared [j]
    times. *)
Lemma xp_exp_neg :
  forall n y,
  level_ok n -> encl_pt n y 0 ->
  exists e, DyadicExp.exp_neg n y = Some e /\ encl_pt n e 1.
Proof.
intros n y Hn Hy. unfold DyadicExp.exp_neg.
pose proof (xp_params n) as Hp.
destruct (DyadicExp.params n) as [j k]. cbn [fst snd] in Hp.
destruct (pt_point n DyadicExp.one Hn (proj1 one_B2R)) as (one_e & Eo & Ho & So).
rewrite (proj2 one_B2R) in Ho.
assert (Sy : encl_small y) by exact (pt_small n y 0 Hn Hy xp_win_0).
assert (Hj : (- 2 ^ 62 <= - j <= 2 ^ 62)%Z) by lia.
destruct (pt_shl n y 0 (- j) Hn Hy Sy Hj) as (s & Es & Hs).
rewrite Rmult_0_l in Hs.
assert (Hk : (0 <= k < 2 ^ 64)%Z) by lia.
destruct (xp_series n s k Hn Hs Hk) as (u & Eu & Hu).
assert (Su : encl_small u) by exact (pt_small n u 0 Hn Hu xp_win_0).
assert (F1 : fmt n (1 - 0)) by (rewrite Rminus_0_r; exact (xp_fmt_1 n Hn)).
destruct (pt_sub n one_e u 1 0 Hn Ho Hu So Su F1) as (e & Ee & He).
rewrite Rminus_0_r in He.
rewrite Eo, Es, Eu, Ee. cbv beta iota.
exact (xp_square_loop n (Z.to_nat j) e Hn He).
Qed.

(** ** [scaled] at the point 0 *)

(** At the point [y = 0], neither [y < 0] nor [y > 2] holds, so that
    [scaled] shifts [exp_neg y], the point 1, by [m]. *)
Lemma xp_scaled :
  forall n y m h l,
  level_ok n -> encl_pt n y 0 -> (Z.abs m <= 2048)%Z ->
  exists e, DyadicExp.scaled n y m h l = Some e /\ encl_pt n e (bpow radix2 m).
Proof.
intros n y m h l Hn Hy Hm. unfold DyadicExp.scaled.
pose proof Hy as ((Olo & Ohi & _) & Ly & Uy). unfold lo_R, hi_R in Ly, Uy.
destruct (dy_zero_ok n) as (Oz & Vz & _).
destruct (from_f64_correct n DyadicExp.two Hn (proj1 two_B2R)) as (two_d & Et & Ot & _ & Vt).
rewrite (proj2 two_B2R) in Vt.
assert (L1 : DyadicExp.dy_lt n (Dyadic.en_lo y) (Dyadic.dy_zero n) = false).
{ destruct (DyadicExp.dy_lt n (Dyadic.en_lo y) (Dyadic.dy_zero n)) eqn:E; [| reflexivity].
  apply (pt_dy_lt n _ _ Hn Olo Oz) in E. rewrite Ly, Vz in E. lra. }
assert (L2 : DyadicExp.dy_gt n (Dyadic.en_hi y) two_d = false).
{ destruct (DyadicExp.dy_gt n (Dyadic.en_hi y) two_d) eqn:E; [| reflexivity].
  apply (pt_dy_gt n _ _ Hn Ohi Ot) in E. rewrite Uy, Vt in E. lra. }
destruct (xp_exp_neg n y Hn Hy) as (e & Ee & He).
assert (Se : encl_small e) by exact (pt_small n e 1 Hn He xp_win_1).
assert (Hm' : (- 2 ^ 62 <= m <= 2 ^ 62)%Z) by lia.
destruct (pt_shl n e 1 m Hn He Se Hm') as (c & Ec & Hc).
rewrite Rmult_1_l in Hc.
rewrite L1. cbv beta iota. rewrite Et. cbv beta iota. rewrite L1, L2. cbn [orb].
rewrite Ee. cbv beta iota.
exists c. split; [exact Ec | exact Hc].
Qed.

(** ** [ev_exp2] at an integer *)

(** [to_k c] is [m] at a finite [c] of the integer value [m], for
    [|m| <= 2048]. *)
Lemma xp_to_k :
  forall c m,
  is_finite c = true -> B2R c = IZR m -> (Z.abs m <= 2048)%Z -> DyadicExp.to_k c = Some m.
Proof.
intros c m Fc Hc Hm.
assert (T : Btrunc c = m).
{ apply eq_IZR. rewrite Btrunc_correct, Hc by reflexivity.
  unfold round, F2R, scaled_mantissa, cexp, FIX_exp.
  cbn [Fnum Fexp bpow Z.opp]. rewrite !Rmult_1_r. now rewrite Ztrunc_IZR. }
assert (M : DyadicExp.to_i64 c = Z.max (- 2 ^ 63) (Z.min (2 ^ 63 - 1) (Btrunc c)))
  by (destruct c; try discriminate Fc; reflexivity).
unfold DyadicExp.to_k. rewrite M, T.
replace (Z.max (- 2 ^ 63) (Z.min (2 ^ 63 - 1) m)) with m by lia.
destruct (Z.abs m <=? 2048) eqn:B; [reflexivity |].
apply Z.leb_gt in B. lia.
Qed.

(** [ev_exp2 x] encloses [2^m] by the point [2^m] at every level, at an
    [f64] [x = m] with [m <> 0] and [-1074 <= m <= 1023]. *)
Lemma ev_exp2_exact :
  forall (x : f64) (m : Z) n,
  is_finite x = true -> B2R x = IZR m -> m <> 0%Z -> (-1074 <= m <= 1023)%Z -> level_ok n ->
  exists a, DyadicExp.ev_exp2 x n = Some a /\ encl_ok n a /\
    lo_R a = powerRZ 2 m /\ hi_R a = powerRZ 2 m.
Proof.
intros x m n Fx Hx _ Hm Hn. unfold DyadicExp.ev_exp2. cbv zeta.
(* [ceil x] is [x] itself, the integer [m]. *)
assert (Fc : is_finite (fceil x) = true).
{ unfold fceil. rewrite (proj1 (proj2 (Bnearbyint_correct 53 1024 _ mode_UP x))). exact Fx. }
assert (Vc : B2R (fceil x) = IZR m) by (rewrite fceil_IZR, Hx, Zceil_IZR; reflexivity).
assert (Hm' : (Z.abs m <= 2048)%Z) by lia.
rewrite (xp_to_k (fceil x) m Fc Vc Hm'). cbv beta iota.
(* The enclosure [[h, h] + l] of ln 2 is valid and small. *)
destruct (DyadicConsts.ln2 n) as [[h l] |] eqn:El;
  [| destruct (dc_level n Hn) as [H _]; rewrite El in H; discriminate H].
cbv beta iota.
destruct (ln2_correct n h l Hn El) as (Hh & Heh & Hl & HEl & _).
destruct (hh_correct n h (2 ^ 13) Hh Heh) as (Ohh & Lhh & _).
assert (Shh : encl_small {| Dyadic.en_lo := h; Dyadic.en_hi := h |})
  by (apply (encl_le_small (2 ^ 13)); [lia | exact Lhh]).
assert (Sl : encl_small l) by (apply (encl_le_small (2 ^ 14)); [lia | exact HEl]).
destruct (encl_add_correct n _ l Hn Ohh Hl Shh Sl) as (ln2e & E2 & _).
assert (B13 : (0 <= 2 ^ 13 <= 2 ^ 60)%Z) by lia.
assert (B14 : (0 <= 2 ^ 14 <= 2 ^ 60)%Z) by lia.
destruct (add_step n _ l ln2e _ _ Hn Ohh Hl Lhh HEl B13 B14 E2) as (O2 & L2 & _).
assert (S2 : encl_small ln2e)
  by (apply (encl_le_small (Z.max (2 ^ 13) (2 ^ 14) + 2 ^ 13)); [lia | exact L2]).
(* [ceil x - x] is the point 0, and so is [y = (ceil x - x) ln 2]. *)
destruct (pt_point n (fceil x) Hn Fc) as (pc & Epc & Hpc & Spc).
destruct (pt_point n x Hn Fx) as (px & Epx & Hpx & Spx).
rewrite Vc in Hpc. rewrite Hx in Hpx.
assert (F0 : fmt n (IZR m - IZR m))
  by (replace (IZR m - IZR m) with 0 by ring; apply generic_format_0).
destruct (pt_sub n pc px _ _ Hn Hpc Hpx Spc Spx F0) as (g & Eg & Hg).
replace (IZR m - IZR m) with 0 in Hg by ring.
destruct (pt_mul_0_l n g ln2e Hn Hg O2 S2) as (y & Ey & Hy).
destruct (xp_scaled n y m h l Hn Hy Hm') as (a & Ea & (Oa & La & Ua)).
rewrite E2, Epc, Epx, Eg, Ey. cbv beta iota.
exists a. split; [exact Ea |]. split; [exact Oa |].
rewrite bpow_powerRZ in La, Ua. split; [exact La | exact Ua].
Qed.
