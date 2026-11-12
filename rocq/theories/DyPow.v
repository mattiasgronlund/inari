(** * pow in the dyadic kernel

    [pow_dir_with ziv_strict] of [DyadicPow] in [Model.v], the kernel
    with the driver [ziv_strict] of [DyDriver.v], returns the special
    values that [pow_c] of [Contract.v] names ([pow_dir_zero_neg] and the
    others below). [pow_dir_post] proves that, for finite [x] and [y] in
    the domain [pow_dom], the results of [pow_dir_with z] have the
    property [post] of [Rpow] of [Elementary.v], for any driver [z] and
    any property [post] that every correct rounding has ([rounds_post])
    and that the results of [z] have ([driver_post]): by the rules of
    [DyPowRules.v] where one applies; then the exact cases of
    [DyPowExact.v] and the fast path ([FastPow.fast_pow_dir_correct], as
    [|y ln x| >= 2^-57] there by the rules), in the order that
    [maybe_exact] picks, which no proof unfolds, as the proofs cover
    both orders; then [pown_pos_ziv_post] of [DyPown.v] for an integer
    [y] from [-2^31] to [2^31 - 1], which [pow] passes to
    [pown_pos_ziv], [pown_pos] without the fast path that [pow] has
    already tried; and otherwise the driver with the enclosure of
    [ev_pow_correct] of [DyPowCore.v]. So,
    for such [x] and [y]: with [ziv_strict], the kernel rounds [Rpow] in
    the direction [up] where it returns
    ([pow_dir_correct]); the Rust ([pow_dir], with [Dyadic.ziv]) returns
    the same value there ([pow_dir_strict]); and wherever the Rust
    returns, its result is at or above [Rpow] if [up] and at or below it
    otherwise ([pow_dir_side]). Where the result at a finite [x > 0] is
    itself a finite [f64], the Rust returns it ([pow_dir_exact]), from
    [exact] ([exact_complete]) or from the fast path where that comes
    first and returns ([fast_pow_dir_exact]), so Ziv's loop never runs
    on such an argument. That a rounding test
    passes by the cap at the other arguments is not proved.
    [pown_dir] is in [DyPown.v]. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr MpfrRound Limbs Elementary DyRound DyConv DyOps DyDriver
  DyGrow DyConst DyExpCore DyExpRules DyExp DyLogRules DyLogCore DyPowArith DyPowRules
  DyPowExact DyPowCore.
From Inari Require DyPown FastPow.

Open Scope Z_scope.

(** [c as i32] is in the range of an [i32]. *)
Lemma to_i32_range : forall c, is_i32 (DyadicPow.to_i32 c).
Proof. intros c. unfold DyadicPow.to_i32, is_i32. destruct c; try destruct s; lia. Qed.

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
  DyadicPow.pow_dir_with ziv_strict (B754_zero false) y up = Some (B754_infinity false).
Proof.
intros y up Fy Hy.
assert (Y0 : B2R y <> B2R zero) by (change (B2R zero) with 0%R; lra).
unfold DyadicPow.pow_dir_with.
rewrite (eq_false_of y zero Fy eq_refl Y0), (fin_not_nan y Fy), (fin_neq_inf y Fy),
  (fin_neq_ninf y Fy), (proj2 (lt_fin y zero Fy eq_refl) Hy).
vm_compute. reflexivity.
Qed.

Lemma pow_dir_one_inf :
  forall x s up, is_finite x = true -> B2R x = 1%R ->
  DyadicPow.pow_dir_with ziv_strict x (B754_infinity s) up = Some DyadicExp.one.
Proof.
intros x s up Fx Hx.
destruct one_B2R as [F1 H1].
assert (Lx : (B2R zero <= B2R x)%R) by (change (B2R zero) with 0%R; lra).
assert (Ex : B2R x = B2R DyadicExp.one) by lra.
unfold DyadicPow.pow_dir_with.
rewrite (fin_not_nan x Fx), (lt_false_of x zero Fx eq_refl Lx), (proj2 (eq_fin x _ Fx F1) Ex).
destruct s; vm_compute; reflexivity.
Qed.

Lemma pow_dir_lt1_inf :
  forall x s up, is_finite x = true -> (0 < B2R x < 1)%R ->
  DyadicPow.pow_dir_with ziv_strict x (B754_infinity s) up =
  Some (if s then B754_infinity false else B754_zero false).
Proof.
intros x s up Fx Hx.
destruct one_B2R as [F1 H1].
assert (Lx : (B2R zero <= B2R x)%R) by (change (B2R zero) with 0%R; lra).
assert (Ex : B2R x <> B2R DyadicExp.one) by lra.
assert (Gx : (B2R x <= B2R DyadicExp.one)%R) by lra.
unfold DyadicPow.pow_dir_with.
rewrite (fin_not_nan x Fx), (lt_false_of x zero Fx eq_refl Lx), (eq_false_of x _ Fx F1 Ex).
change (gt x DyadicExp.one) with (lt DyadicExp.one x).
rewrite (lt_false_of DyadicExp.one x F1 Fx Gx).
destruct s; vm_compute; reflexivity.
Qed.

Lemma pow_dir_gt1_inf :
  forall x s up, is_finite x = true -> (1 < B2R x)%R ->
  DyadicPow.pow_dir_with ziv_strict x (B754_infinity s) up =
  Some (if s then B754_zero false else B754_infinity false).
Proof.
intros x s up Fx Hx.
destruct one_B2R as [F1 H1].
assert (Lx : (B2R zero <= B2R x)%R) by (change (B2R zero) with 0%R; lra).
assert (Ex : B2R x <> B2R DyadicExp.one) by lra.
assert (Gx : (B2R DyadicExp.one < B2R x)%R) by lra.
unfold DyadicPow.pow_dir_with.
rewrite (fin_not_nan x Fx), (lt_false_of x zero Fx eq_refl Lx), (eq_false_of x _ Fx F1 Ex).
change (gt x DyadicExp.one) with (lt DyadicExp.one x).
rewrite (proj2 (lt_fin DyadicExp.one x F1 Fx) Gx).
destruct s; vm_compute; reflexivity.
Qed.

Lemma pow_dir_inf_neg :
  forall y up, is_finite y = true -> (B2R y < 0)%R ->
  DyadicPow.pow_dir_with ziv_strict (B754_infinity false) y up = Some (B754_zero false).
Proof.
intros y up Fy Hy.
assert (Y0 : B2R y <> B2R zero) by (change (B2R zero) with 0%R; lra).
assert (Gy : (B2R y <= B2R zero)%R) by (change (B2R zero) with 0%R; lra).
unfold DyadicPow.pow_dir_with.
rewrite (eq_false_of y zero Fy eq_refl Y0), (fin_not_nan y Fy), (fin_neq_inf y Fy),
  (fin_neq_ninf y Fy).
change (gt y zero) with (lt zero y).
rewrite (lt_false_of zero y eq_refl Fy Gy).
vm_compute. reflexivity.
Qed.

Lemma pow_dir_inf_pos :
  forall y up, is_finite y = true -> (0 < B2R y)%R ->
  DyadicPow.pow_dir_with ziv_strict (B754_infinity false) y up = Some (B754_infinity false).
Proof.
intros y up Fy Hy.
assert (Y0 : B2R y <> B2R zero) by (change (B2R zero) with 0%R; lra).
unfold DyadicPow.pow_dir_with.
rewrite (eq_false_of y zero Fy eq_refl Y0), (fin_not_nan y Fy), (fin_neq_inf y Fy),
  (fin_neq_ninf y Fy).
change (gt y zero) with (lt zero y).
rewrite (proj2 (lt_fin zero y eq_refl Fy) Hy).
vm_compute. reflexivity.
Qed.

Lemma pow_dir_post :
  forall z post, rounds_post post -> driver_post z post ->
  forall x y (up : bool) v,
  is_finite x = true -> is_finite y = true -> pow_dom (B2R x) (B2R y) ->
  DyadicPow.pow_dir_with z x y up = Some v ->
  post up (Rpow (B2R x) (B2R y)) v.
Proof.
intros z post Hp Hz x y up v Fx Fy Hd E.
assert (Fz : is_finite zero = true) by reflexivity.
assert (F1 : is_finite DyadicExp.one = true) by exact (proj1 one_B2R).
assert (Hx0 : (0 <= B2R x)%R) by (destruct Hd as [H | [H _]]; lra).
unfold DyadicPow.pow_dir_with in E.
destruct (eq y zero) eqn:Y0.
{ cbv iota in E. injection E as <-.
  apply (eq_fin y zero Fy Fz) in Y0. change (B2R zero) with 0%R in Y0.
  assert (Px : (0 < B2R x)%R) by (destruct Hd as [H | [_ H]]; lra).
  unfold Rpow. destruct (Rle_dec (B2R x) 0) as [H | _]; [lra |].
  rewrite Y0, (Rpower_O _ Px). apply Hp. exact (rnd_exact _ _ _ F1 (proj2 one_B2R)). }
rewrite (fin_not_nan x Fx), (fin_not_nan y Fy) in E. cbv iota in E.
destruct (lt x zero) eqn:L.
{ apply (lt_fin x zero Fx Fz) in L. change (B2R zero) with 0%R in L. lra. }
destruct (eq x DyadicExp.one) eqn:X1.
{ cbv iota in E. injection E as <-.
  apply (eq_fin x _ Fx F1) in X1. rewrite (proj2 one_B2R) in X1.
  unfold Rpow. destruct (Rle_dec (B2R x) 0) as [H | _]; [lra |].
  rewrite X1, Rpower_base_1. apply Hp. exact (rnd_exact _ _ _ F1 (proj2 one_B2R)). }
rewrite (fin_neq_inf y Fy), (fin_neq_ninf y Fy) in E. cbn [orb] in E. cbv iota in E.
destruct (eq x zero) eqn:X0.
{ (* [x = ±0] and [y > 0]: the result is a zero of either sign. *)
  cbv iota zeta in E. injection E as <-.
  apply (eq_fin x zero Fx Fz) in X0. change (B2R zero) with 0%R in X0.
  assert (Py : (0 < B2R y)%R) by (destruct Hd as [H | [_ H]]; lra).
  destruct (lt y zero) eqn:Ly.
  { apply (lt_fin y zero Fy Fz) in Ly. change (B2R zero) with 0%R in Ly. lra. }
  unfold Rpow. destruct (Rle_dec (B2R x) 0) as [_ | H]; [| lra].
  apply Hp. apply rnd_exact; destruct (Bsign x && DyadicPow.is_odd_integer y); reflexivity. }
rewrite (fin_neq_inf x Fx) in E. cbv iota zeta in E.
apply (eq_fin_false x _ Fx F1) in X1. rewrite (proj2 one_B2R) in X1.
apply (eq_fin_false y zero Fy Fz) in Y0. change (B2R zero) with 0%R in Y0.
apply (eq_fin_false x zero Fx Fz) in X0. change (B2R zero) with 0%R in X0.
assert (Px : (0 < B2R x)%R) by (destruct Hd as [H | [H _]]; lra).
replace (Rpow (B2R x) (B2R y)) with (Rpower (B2R x) (B2R y))
  by (unfold Rpow; destruct (Rle_dec (B2R x) 0) as [H | _]; [lra | reflexivity]).
destruct (10 <=? DyadicPow.expo y + DyadicPow.ln_expo x) eqn:S1.
{ apply Z.leb_le in S1. injection E as <-. apply Hp.
  destruct (Bool.eqb (gt y zero) (gt x DyadicExp.one)) eqn:A.
  - exact (pow_rule_overflow x y up Fx Px X1 Fy Y0 S1 A).
  - exact (pow_rule_underflow x y up Fx Px X1 Fy Y0 S1 A). }
destruct (DyadicPow.expo y + DyadicPow.ln_expo x <=? -58) eqn:S2.
{ apply Z.leb_le in S2. injection E as <-. apply Hp.
  exact (pow_rule_near_one x y up Fx Px X1 Fy Y0 S2). }
assert (Hb60 : (bpow radix2 (-60) <= Rabs (B2R y * ln (B2R x)))%R).
{ destruct (pow_rule_bounds x y Fx Px X1 Fy Y0) as ([Hb _] & _).
  apply Rle_trans with (2 := Hb). apply bpow_le. apply Z.leb_gt in S2. lia. }
(* [exact] and the fast path, where [|y ln x| >= 2^-60], in either order. *)
assert (HE : forall w, DyadicPow.exact x y = Some (Some w) ->
             post up (Rpower (B2R x) (B2R y)) w).
{ intros w Ex. destruct (exact_sound x y w Fx Px Fy Y0 Ex) as [Fw Hw].
  apply Hp. exact (rnd_exact _ _ _ Fw Hw). }
assert (HF : forall w, DyadicPow.fast_pow_dir_call false x y up = Some w ->
             post up (Rpower (B2R x) (B2R y)) w).
{ intros w F. apply Hp.
  exact (FastPow.fast_pow_dir_correct false x y up w Fx Px Fy (or_intror Hb60) F). }
(* What both orders reach last: [pown_pos_ziv] or the driver. *)
assert (HT : forall start,
  (if eq (DyadicPow.of_i64 (DyadicPow.to_i32 y)) y
   then DyadicPow.pown_pos_ziv_with z x (DyadicPow.to_i32 y) up
   else z (DyadicPow.ev_pow x y) up start) = Some v ->
  post up (Rpower (B2R x) (B2R y)) v).
{ intros start E'. destruct (eq (DyadicPow.of_i64 (DyadicPow.to_i32 y)) y) eqn:I.
  - (* An integer [y] from [-2^31] to [2^31 - 1]: x^y is [powerRZ x k] for [k = y]. *)
    assert (Hi : is_i32 (DyadicPow.to_i32 y)) by apply to_i32_range.
    destruct (of_i64_exact (DyadicPow.to_i32 y)) as [Fk Vk]; [unfold is_i32 in Hi; lia |].
    apply (eq_fin _ _ Fk Fy) in I. rewrite Vk in I.
    assert (Hk : DyadicPow.to_i32 y <> 0)
      by (intros K; apply Y0; rewrite <- I, K; reflexivity).
    rewrite <- I, <- (powerRZ_Rpower _ _ Px).
    exact (DyPown.pown_pos_ziv_post z post Hp Hz x _ up v Fx Px Hk Hi E').
  - refine (Hz (DyadicPow.ev_pow x y) up _ _ v _ E').
    intros n a Hn Ea. exact (ev_pow_correct n x y a Hn Fx Px Fy Ea). }
destruct (DyadicPow.maybe_exact x y); cbv iota in E.
- (* [exact] first, then the fast path. *)
  destruct (DyadicPow.exact x y) as [[w|]|] eqn:Ex in E; [| | discriminate E].
  { injection E as <-. exact (HE w Ex). }
  cbv beta iota in E.
  destruct (DyadicPow.fast_pow_dir_call false x y up) as [w|] eqn:F in E; cbv iota in E.
  { injection E as <-. exact (HF w F). }
  exact (HT _ E).
- (* The fast path first, then [exact]. *)
  destruct (DyadicPow.fast_pow_dir_call false x y up) as [w|] eqn:F in E; cbv iota in E.
  { injection E as <-. exact (HF w F). }
  destruct (DyadicPow.exact x y) as [[w|]|] eqn:Ex in E; [| | discriminate E].
  { injection E as <-. exact (HE w Ex). }
  cbv beta iota in E. exact (HT _ E).
Qed.

Theorem pow_dir_correct :
  forall x y (up : bool) v,
  is_finite x = true -> is_finite y = true -> pow_dom (B2R x) (B2R y) ->
  DyadicPow.pow_dir_with ziv_strict x y up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (Rpow (B2R x) (B2R y)) (with_val v).
Proof. exact (pow_dir_post ziv_strict rounds (fun _ _ _ H => H) ziv_strict_correct). Qed.

Theorem pow_dir_side :
  forall x y (up : bool) v,
  is_finite x = true -> is_finite y = true -> pow_dom (B2R x) (B2R y) ->
  DyadicPow.pow_dir x y up = Some v ->
  f64_side up (Rpow (B2R x) (B2R y)) v.
Proof. exact (pow_dir_post Dyadic.ziv f64_side rounds_side ziv_side). Qed.

Theorem pow_dir_strict :
  forall x y (up : bool) v,
  DyadicPow.pow_dir_with ziv_strict x y up = Some v -> DyadicPow.pow_dir x y up = Some v.
Proof.
intros x y up v. unfold DyadicPow.pow_dir, DyadicPow.pow_dir_with. cbv zeta.
destruct (eq y zero); [exact (fun h => h)|].
destruct (is_nan x); [exact (fun h => h)|].
destruct (is_nan y); [exact (fun h => h)|].
destruct (lt x zero); [exact (fun h => h)|].
destruct (eq x DyadicExp.one); [exact (fun h => h)|].
destruct (eq y infinity || eq y DyadicExp.neg_infinity); [exact (fun h => h)|].
destruct (eq x zero); [exact (fun h => h)|].
destruct (eq x infinity); [exact (fun h => h)|].
destruct (10 <=? DyadicPow.expo y + DyadicPow.ln_expo x); [exact (fun h => h)|].
destruct (DyadicPow.expo y + DyadicPow.ln_expo x <=? -58); [exact (fun h => h)|].
destruct (DyadicPow.maybe_exact x y); cbv beta iota.
- destruct (DyadicPow.exact x y) as [[w|]|]; [exact (fun h => h) | | exact (fun h => h)].
  cbv beta iota.
  destruct (DyadicPow.fast_pow_dir_call false x y up); [exact (fun h => h) |].
  cbv beta iota.
  destruct (eq (DyadicPow.of_i64 (DyadicPow.to_i32 y)) y);
    [apply DyPown.pown_pos_ziv_strict | apply ziv_strict_ziv].
- destruct (DyadicPow.fast_pow_dir_call false x y up); [exact (fun h => h) |].
  cbv beta iota.
  destruct (DyadicPow.exact x y) as [[w|]|]; [exact (fun h => h) | | exact (fun h => h)].
  cbv beta iota.
  destruct (eq (DyadicPow.of_i64 (DyadicPow.to_i32 y)) y);
    [apply DyPown.pown_pos_ziv_strict | apply ziv_strict_ziv].
Qed.

(** Where x^y is a finite [f64] [v] and the fast path returns, it returns
    [v], as it returns the rounding of x^y. *)
Lemma fast_pow_dir_exact :
  forall x y up (v r : f64),
  is_finite x = true -> (0 < B2R x)%R -> is_finite y = true -> is_finite v = true ->
  Rpower (B2R x) (B2R y) = B2R v ->
  (bpow radix2 (-60) <= Rabs (B2R y * ln (B2R x)))%R ->
  DyadicPow.fast_pow_dir_call false x y up = Some r -> r = v.
Proof.
intros x y up v r Fx Hx Fy Fv Hv Hb F.
unfold DyadicPow.fast_pow_dir_call in F.
pose proof (FastPow.fast_pow_dir_correct false x y up r Fx Hx Fy (or_intror Hb) F) as R.
assert (Nv : B2R v <> 0%R)
  by (rewrite <- Hv; apply Rgt_not_eq; unfold Rpower; apply exp_pos).
(* The fast path returns the correct rounding of the [f64] [v], which is [v]. *)
unfold rounds in R. rewrite Hv in R.
destruct (OfPointCore.round_f64_unique _ _ _ _ R (rnd_exact v _ _ Fv eq_refl))
  as [-> | (s & s' & _ & E)]; [reflexivity |].
exfalso. apply Nv. rewrite E. reflexivity.
Qed.

Lemma pow_dir_exact_with :
  forall z x y (v : f64) (up : bool),
  is_finite x = true -> (0 < B2R x)%R -> is_finite y = true -> is_finite v = true ->
  Rpower (B2R x) (B2R y) = B2R v ->
  DyadicPow.pow_dir_with z x y up = Some v.
Proof.
intros z x y v up Fx Hx Fy Fv Hv.
assert (Fz : is_finite zero = true) by reflexivity.
assert (F1 : is_finite DyadicExp.one = true) by exact (proj1 one_B2R).
unfold DyadicPow.pow_dir_with.
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
(* Where [maybe_exact] puts [exact] first, it returns [v]; otherwise the
   fast path returns [v] where it returns, and [exact] after it. *)
destruct (DyadicPow.maybe_exact x y).
{ rewrite (exact_complete x y v Fx Hx X1 Fy Y0 Fv Hv). reflexivity. }
destruct (DyadicPow.fast_pow_dir_call false x y up) as [r|] eqn:F.
- assert (Hb60 : (bpow radix2 (-60) <= Rabs (B2R y * ln (B2R x)))%R).
  { destruct (pow_rule_bounds x y Fx Hx X1 Fy Y0) as ([Hb _] & _).
    apply Rle_trans with (2 := Hb). apply bpow_le. apply Z.leb_gt in S2. lia. }
  cbv beta iota. f_equal. exact (fast_pow_dir_exact x y up v r Fx Hx Fy Fv Hv Hb60 F).
- rewrite (exact_complete x y v Fx Hx X1 Fy Y0 Fv Hv). reflexivity.
Qed.

Theorem pow_dir_exact :
  forall x y (v : f64) (up : bool),
  is_finite x = true -> (0 < B2R x)%R -> is_finite y = true -> is_finite v = true ->
  Rpower (B2R x) (B2R y) = B2R v ->
  DyadicPow.pow_dir x y up = Some v.
Proof. exact (pow_dir_exact_with Dyadic.ziv). Qed.
