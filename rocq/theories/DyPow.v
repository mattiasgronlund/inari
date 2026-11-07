(** * pow in the dyadic kernel

    [pow_dir] of [DyadicPow] in [Model.v] returns the special values that
    [pow_c] of [Contract.v] names ([pow_dir_zero_neg] and the others
    below). Where it returns, it rounds [Rpow] of [Elementary.v] of finite
    [x] and [y] in the domain [pow_dom] in the direction [up]
    ([pow_dir_correct]): the rules of [DyPowRules.v] where one applies,
    the exact cases of [DyPowExact.v], and otherwise [ziv_correct] of
    [DyDriver.v] with the enclosure of [ev_pow_correct] of [DyPowCore.v].
    Where the result at a finite [x > 0] is itself a finite [f64], it
    returns it ([pow_dir_exact]), so Ziv's loop never runs on such an
    argument. That the loop ends before its cap at the other arguments is
    not proved. [pown_dir] is in [DyPown.v]. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr MpfrRound Limbs Elementary DyRound DyConv DyOps DyDriver
  DyGrow DyConst DyExpCore DyExpRules DyExp DyLogRules DyLogCore DyPowArith DyPowRules
  DyPowExact DyPowCore.

Open Scope Z_scope.

(** ** Comparisons of finite [f64]s *)

(** [eq] and [lt] of two finite [f64]s compare their reals. *)
Lemma eq_fin :
  forall a b : f64, is_finite a = true -> is_finite b = true ->
  eq a b = true <-> B2R a = B2R b.
Proof.
intros a b Fa Fb. unfold eq. rewrite Beqb_correct by assumption.
destruct (Req_bool_spec (B2R a) (B2R b)) as [H | H];
  split; intros E; first [reflexivity | exact H | discriminate E | contradiction].
Qed.

Lemma lt_fin :
  forall a b : f64, is_finite a = true -> is_finite b = true ->
  lt a b = true <-> (B2R a < B2R b)%R.
Proof.
intros a b Fa Fb. unfold lt. rewrite Bltb_correct by assumption.
destruct (Rlt_bool_spec (B2R a) (B2R b)) as [H | H];
  split; intros E; first [reflexivity | exact H | discriminate E | lra].
Qed.

(** The [false] sides of [eq_fin] and [lt_fin]. [gt a b] is [lt b a]. *)
Lemma eq_fin_false :
  forall a b : f64, is_finite a = true -> is_finite b = true ->
  eq a b = false -> B2R a <> B2R b.
Proof.
intros a b Fa Fb E H. apply (eq_fin a b Fa Fb) in H. congruence.
Qed.

Lemma eq_false_of :
  forall a b : f64, is_finite a = true -> is_finite b = true ->
  B2R a <> B2R b -> eq a b = false.
Proof.
intros a b Fa Fb H. destruct (eq a b) eqn:E; [| reflexivity].
exfalso. exact (H (proj1 (eq_fin a b Fa Fb) E)).
Qed.

Lemma lt_false_of :
  forall a b : f64, is_finite a = true -> is_finite b = true ->
  (B2R b <= B2R a)%R -> lt a b = false.
Proof.
intros a b Fa Fb H. destruct (lt a b) eqn:E; [| reflexivity].
apply (proj1 (lt_fin a b Fa Fb)) in E. lra.
Qed.

(** A finite [f64] of value 1 is [DyadicExp.one]: it is not a zero, and
    [B2R] is injective on the nonzero finite [f64]s. *)
Lemma f64_one : forall w : f64, is_finite w = true -> B2R w = 1%R -> w = DyadicExp.one.
Proof.
intros w Fw Hw. apply B2R_inj; [| reflexivity | rewrite Hw; exact (eq_sym (proj2 one_B2R))].
destruct w as [s|s| |s m e H]; try discriminate Fw; [| reflexivity].
cbn [B2R] in Hw. lra.
Qed.

(** [1^y = 1]. *)
Lemma Rpower_base_1 : forall y, Rpower 1 y = 1%R.
Proof.
intros y. unfold Rpower. rewrite ln_1, Rmult_0_r. exact exp_0.
Qed.

(** ** The special values of [pow_dir] *)

Lemma pow_dir_zero_neg :
  forall y up, is_finite y = true -> (B2R y < 0)%R ->
  DyadicPow.pow_dir (B754_zero false) y up = Some (B754_infinity false).
Proof.
intros y up Fy Hy.
assert (Y0 : B2R y <> B2R zero) by (change (B2R zero) with 0%R; lra).
unfold DyadicPow.pow_dir.
rewrite (eq_false_of y zero Fy eq_refl Y0), (fin_not_nan y Fy), (fin_neq_inf y Fy),
  (fin_neq_ninf y Fy), (proj2 (lt_fin y zero Fy eq_refl) Hy).
vm_compute. reflexivity.
Qed.

Lemma pow_dir_one_inf :
  forall x s up, is_finite x = true -> B2R x = 1%R ->
  DyadicPow.pow_dir x (B754_infinity s) up = Some DyadicExp.one.
Proof.
intros x s up Fx Hx.
destruct one_B2R as [F1 H1].
assert (Lx : (B2R zero <= B2R x)%R) by (change (B2R zero) with 0%R; lra).
assert (Ex : B2R x = B2R DyadicExp.one) by lra.
unfold DyadicPow.pow_dir.
rewrite (fin_not_nan x Fx), (lt_false_of x zero Fx eq_refl Lx), (proj2 (eq_fin x _ Fx F1) Ex).
destruct s; vm_compute; reflexivity.
Qed.

Lemma pow_dir_lt1_inf :
  forall x s up, is_finite x = true -> (0 < B2R x < 1)%R ->
  DyadicPow.pow_dir x (B754_infinity s) up =
  Some (if s then B754_infinity false else B754_zero false).
Proof.
intros x s up Fx Hx.
destruct one_B2R as [F1 H1].
assert (Lx : (B2R zero <= B2R x)%R) by (change (B2R zero) with 0%R; lra).
assert (Ex : B2R x <> B2R DyadicExp.one) by lra.
assert (Gx : (B2R x <= B2R DyadicExp.one)%R) by lra.
unfold DyadicPow.pow_dir.
rewrite (fin_not_nan x Fx), (lt_false_of x zero Fx eq_refl Lx), (eq_false_of x _ Fx F1 Ex).
change (gt x DyadicExp.one) with (lt DyadicExp.one x).
rewrite (lt_false_of DyadicExp.one x F1 Fx Gx).
destruct s; vm_compute; reflexivity.
Qed.

Lemma pow_dir_gt1_inf :
  forall x s up, is_finite x = true -> (1 < B2R x)%R ->
  DyadicPow.pow_dir x (B754_infinity s) up =
  Some (if s then B754_zero false else B754_infinity false).
Proof.
intros x s up Fx Hx.
destruct one_B2R as [F1 H1].
assert (Lx : (B2R zero <= B2R x)%R) by (change (B2R zero) with 0%R; lra).
assert (Ex : B2R x <> B2R DyadicExp.one) by lra.
assert (Gx : (B2R DyadicExp.one < B2R x)%R) by lra.
unfold DyadicPow.pow_dir.
rewrite (fin_not_nan x Fx), (lt_false_of x zero Fx eq_refl Lx), (eq_false_of x _ Fx F1 Ex).
change (gt x DyadicExp.one) with (lt DyadicExp.one x).
rewrite (proj2 (lt_fin DyadicExp.one x F1 Fx) Gx).
destruct s; vm_compute; reflexivity.
Qed.

Lemma pow_dir_inf_neg :
  forall y up, is_finite y = true -> (B2R y < 0)%R ->
  DyadicPow.pow_dir (B754_infinity false) y up = Some (B754_zero false).
Proof.
intros y up Fy Hy.
assert (Y0 : B2R y <> B2R zero) by (change (B2R zero) with 0%R; lra).
assert (Gy : (B2R y <= B2R zero)%R) by (change (B2R zero) with 0%R; lra).
unfold DyadicPow.pow_dir.
rewrite (eq_false_of y zero Fy eq_refl Y0), (fin_not_nan y Fy), (fin_neq_inf y Fy),
  (fin_neq_ninf y Fy).
change (gt y zero) with (lt zero y).
rewrite (lt_false_of zero y eq_refl Fy Gy).
vm_compute. reflexivity.
Qed.

Lemma pow_dir_inf_pos :
  forall y up, is_finite y = true -> (0 < B2R y)%R ->
  DyadicPow.pow_dir (B754_infinity false) y up = Some (B754_infinity false).
Proof.
intros y up Fy Hy.
assert (Y0 : B2R y <> B2R zero) by (change (B2R zero) with 0%R; lra).
unfold DyadicPow.pow_dir.
rewrite (eq_false_of y zero Fy eq_refl Y0), (fin_not_nan y Fy), (fin_neq_inf y Fy),
  (fin_neq_ninf y Fy).
change (gt y zero) with (lt zero y).
rewrite (proj2 (lt_fin zero y eq_refl Fy) Hy).
vm_compute. reflexivity.
Qed.

Theorem pow_dir_correct :
  forall x y (up : bool) v,
  is_finite x = true -> is_finite y = true -> pow_dom (B2R x) (B2R y) ->
  DyadicPow.pow_dir x y up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (Rpow (B2R x) (B2R y)) (with_val v).
Proof.
intros x y up v Fx Fy Hd E.
assert (Fz : is_finite zero = true) by reflexivity.
assert (F1 : is_finite DyadicExp.one = true) by exact (proj1 one_B2R).
assert (Hx0 : (0 <= B2R x)%R) by (destruct Hd as [H | [H _]]; lra).
unfold DyadicPow.pow_dir in E.
destruct (eq y zero) eqn:Y0.
{ cbv iota in E. injection E as <-.
  apply (eq_fin y zero Fy Fz) in Y0. change (B2R zero) with 0%R in Y0.
  assert (Px : (0 < B2R x)%R) by (destruct Hd as [H | [_ H]]; lra).
  unfold Rpow. destruct (Rle_dec (B2R x) 0) as [H | _]; [lra |].
  rewrite Y0, (Rpower_O _ Px). exact (rnd_exact _ _ _ F1 (proj2 one_B2R)). }
rewrite (fin_not_nan x Fx), (fin_not_nan y Fy) in E. cbv iota in E.
destruct (lt x zero) eqn:L.
{ apply (lt_fin x zero Fx Fz) in L. change (B2R zero) with 0%R in L. lra. }
destruct (eq x DyadicExp.one) eqn:X1.
{ cbv iota in E. injection E as <-.
  apply (eq_fin x _ Fx F1) in X1. rewrite (proj2 one_B2R) in X1.
  unfold Rpow. destruct (Rle_dec (B2R x) 0) as [H | _]; [lra |].
  rewrite X1, Rpower_base_1. exact (rnd_exact _ _ _ F1 (proj2 one_B2R)). }
rewrite (fin_neq_inf y Fy), (fin_neq_ninf y Fy) in E. cbn [orb] in E. cbv iota in E.
destruct (eq x zero) eqn:X0.
{ (* [x = ±0] and [y > 0]: the result is a zero of either sign. *)
  cbv iota zeta in E. injection E as <-.
  apply (eq_fin x zero Fx Fz) in X0. change (B2R zero) with 0%R in X0.
  assert (Py : (0 < B2R y)%R) by (destruct Hd as [H | [_ H]]; lra).
  destruct (lt y zero) eqn:Ly.
  { apply (lt_fin y zero Fy Fz) in Ly. change (B2R zero) with 0%R in Ly. lra. }
  unfold Rpow. destruct (Rle_dec (B2R x) 0) as [_ | H]; [| lra].
  apply rnd_exact; destruct (Bsign x && DyadicPow.is_odd_integer y); reflexivity. }
rewrite (fin_neq_inf x Fx) in E. cbv iota zeta in E.
apply (eq_fin_false x _ Fx F1) in X1. rewrite (proj2 one_B2R) in X1.
apply (eq_fin_false y zero Fy Fz) in Y0. change (B2R zero) with 0%R in Y0.
apply (eq_fin_false x zero Fx Fz) in X0. change (B2R zero) with 0%R in X0.
assert (Px : (0 < B2R x)%R) by (destruct Hd as [H | [H _]]; lra).
replace (Rpow (B2R x) (B2R y)) with (Rpower (B2R x) (B2R y))
  by (unfold Rpow; destruct (Rle_dec (B2R x) 0) as [H | _]; [lra | reflexivity]).
destruct (10 <=? DyadicPow.expo y + DyadicPow.ln_expo x) eqn:S1.
{ apply Z.leb_le in S1. injection E as <-.
  destruct (Bool.eqb (gt y zero) (gt x DyadicExp.one)) eqn:A.
  - exact (pow_rule_overflow x y up Fx Px X1 Fy Y0 S1 A).
  - exact (pow_rule_underflow x y up Fx Px X1 Fy Y0 S1 A). }
destruct (DyadicPow.expo y + DyadicPow.ln_expo x <=? -58) eqn:S2.
{ apply Z.leb_le in S2. injection E as <-.
  exact (pow_rule_near_one x y up Fx Px X1 Fy Y0 S2). }
destruct (DyadicPow.exact x y) as [[w|]|] eqn:Ex; [| | discriminate E].
- injection E as <-. destruct (exact_sound x y w Fx Px Fy Y0 Ex) as [Fw Hw].
  exact (rnd_exact _ _ _ Fw Hw).
- refine (ziv_correct (DyadicPow.ev_pow x y) up _ _ v _ E).
  intros n a Hn Ea. exact (ev_pow_correct n x y a Hn Fx Px Fy Ea).
Qed.

Theorem pow_dir_exact :
  forall x y (v : f64) (up : bool),
  is_finite x = true -> (0 < B2R x)%R -> is_finite y = true -> is_finite v = true ->
  Rpower (B2R x) (B2R y) = B2R v ->
  DyadicPow.pow_dir x y up = Some v.
Proof.
intros x y v up Fx Hx Fy Fv Hv.
assert (Fz : is_finite zero = true) by reflexivity.
assert (F1 : is_finite DyadicExp.one = true) by exact (proj1 one_B2R).
unfold DyadicPow.pow_dir.
destruct (eq y zero) eqn:Y0.
{ apply (eq_fin y zero Fy Fz) in Y0. change (B2R zero) with 0%R in Y0.
  rewrite Y0, (Rpower_O _ Hx) in Hv. cbv iota. f_equal. symmetry.
  apply f64_one; [exact Fv | lra]. }
rewrite (fin_not_nan x Fx), (fin_not_nan y Fy). cbv iota.
destruct (lt x zero) eqn:L.
{ apply (lt_fin x zero Fx Fz) in L. change (B2R zero) with 0%R in L. lra. }
destruct (eq x DyadicExp.one) eqn:X1.
{ apply (eq_fin x _ Fx F1) in X1. rewrite (proj2 one_B2R) in X1.
  rewrite X1, Rpower_base_1 in Hv. cbv iota. f_equal. symmetry.
  apply f64_one; [exact Fv | lra]. }
rewrite (fin_neq_inf y Fy), (fin_neq_ninf y Fy). cbn [orb]. cbv iota.
destruct (eq x zero) eqn:X0.
{ apply (eq_fin x zero Fx Fz) in X0. change (B2R zero) with 0%R in X0. lra. }
rewrite (fin_neq_inf x Fx). cbv iota zeta.
apply (eq_fin_false x _ Fx F1) in X1. rewrite (proj2 one_B2R) in X1.
apply (eq_fin_false y zero Fy Fz) in Y0. change (B2R zero) with 0%R in Y0.
destruct (10 <=? DyadicPow.expo y + DyadicPow.ln_expo x) eqn:S1.
{ exfalso. apply (pow_rule_not_exact x y v Fx Hx X1 Fy Y0 Fv); [| exact Hv].
  left. apply Z.leb_le. exact S1. }
destruct (DyadicPow.expo y + DyadicPow.ln_expo x <=? -58) eqn:S2.
{ exfalso. apply (pow_rule_not_exact x y v Fx Hx X1 Fy Y0 Fv); [| exact Hv].
  right. apply Z.leb_le. exact S2. }
rewrite (exact_complete x y v Fx Hx X1 Fy Y0 Fv Hv). reflexivity.
Qed.
