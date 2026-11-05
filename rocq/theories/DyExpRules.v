(** * The rules before Ziv's strategy in the exponential family

    [exp_dir] and the other functions of [DyadicExp] in [Model.v] settle
    some finite arguments before the loop: those whose results overflow or
    underflow, those whose results lie within an ulp of 1 or of [x], and
    the exact powers of 10. Each lemma below is one such branch: where its
    test on [x] is true, the [f64] that the branch returns is the result
    rounded in the direction [up]. The thresholds follow from the bounds
    on [ln 2] and [ln 10] of [ConstLn.v]. *)

From Stdlib Require Import ZArith Reals Lra Lia QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Elementary ExpReal ConstLn Encoding IdealGetD OfPointCore.
From Inari Require Import MpfrRound MpfrIdeal.
From Inari Require ConstTight.

Open Scope R_scope.

Local Notation rnd_of up := (if up then RNDU else RNDD).

(** The format of the finite [f64]s without the bound above, as in
    [IdealGetD.v]: [FLT_exp (-1074) 53]. *)
Local Notation G := (generic_format radix2 (SpecFloat.fexp 53 1024)).

(** ** Helpers *)

(** The real of an [f64] literal is the rational that [vm_compute] finds
    for it. *)
Lemma lit_R : forall (w : f64) (q : Q), ConstTight.B2Q w = q -> B2R w = Q2R q.
Proof. intros w q H. rewrite ConstTight.B2Q_correct, H. reflexivity. Qed.

(** [lit w H] adds [H : B2R w = n * / d] for the literal [w], with [n] and
    [d] numerals that [lra] reads. *)
Local Ltac lit w H :=
  let q := eval vm_compute in (ConstTight.B2Q w) in
  assert (H : B2R w = Q2R q) by (apply lit_R; vm_compute; reflexivity);
  unfold Q2R in H; cbn [Qnum Qden] in H.

(** The comparisons of [Model.v] between finite [f64]s are those of their
    reals. *)
Lemma ge_R :
  forall x y, is_finite x = true -> is_finite y = true -> ge x y = true -> B2R y <= B2R x.
Proof.
intros x y Fx Fy H. unfold ge in H. rewrite Bleb_correct in H by assumption.
destruct (Rle_bool_spec (B2R y) (B2R x)); [assumption | discriminate].
Qed.

Lemma le_R :
  forall x y, is_finite x = true -> is_finite y = true -> le x y = true -> B2R x <= B2R y.
Proof.
intros x y Fx Fy H. unfold le in H. rewrite Bleb_correct in H by assumption.
destruct (Rle_bool_spec (B2R x) (B2R y)); [assumption | discriminate].
Qed.

Lemma lt_R :
  forall x y, is_finite x = true -> is_finite y = true -> lt x y = true -> B2R x < B2R y.
Proof.
intros x y Fx Fy H. unfold lt in H. rewrite Bltb_correct in H by assumption.
destruct (Rlt_bool_spec (B2R x) (B2R y)); [assumption | discriminate].
Qed.

Lemma fabs_lt_R :
  forall x t, is_finite x = true -> is_finite t = true -> lt (fabs x) t = true ->
  Rabs (B2R x) < B2R t.
Proof.
intros x t Fx Ft H. apply lt_R in H; [| unfold fabs; rewrite is_finite_Babs; exact Fx | exact Ft].
unfold fabs in H. rewrite B2R_Babs in H. exact H.
Qed.

(** [ln 2] and [ln 10] to 10 decimals, from [ConstLn.v]. *)
Lemma ln2_bounds : 6931471805 / 10000000000 < ln 2 < 6931471806 / 10000000000.
Proof.
destruct LN_2_Q as [H1 H2]. unfold Q2R, ln2_lo, ln2_hi in H1, H2.
cbn [Qnum Qden] in H1, H2. lra.
Qed.

Lemma ln10_bounds : 23025850929 / 10000000000 < ln 10 < 23025850930 / 10000000000.
Proof.
destruct LN_10_Q as [H1 H2]. unfold Q2R, ln10_lo, ln10_hi in H1, H2.
cbn [Qnum Qden] in H1, H2. lra.
Qed.

(** A power of 2 is the exponential of its exponent times [ln 2]. *)
Lemma bpow_exp2 : forall e, bpow radix2 e = exp (IZR e * ln 2).
Proof. intros e. rewrite bpow_exp. reflexivity. Qed.

(** An [f64] whose real is [r] is [r] rounded in either direction. *)
Lemma rnd_exact :
  forall (w : f64) rnd r, is_finite w = true -> B2R w = r ->
  mpfr_round f64_format rnd r (with_val w).
Proof.
intros w rnd r Fw <-. apply finite_round_ok; [exact Fw|].
assert (Gw : G (B2R w)) by exact (generic_format_B2R 53 1024 w).
destruct rnd; cbn [rnd_pt].
- apply Rnd_DN_pt_refl. exact Gw.
- apply Rnd_UP_pt_refl. exact Gw.
Qed.

(** If [hi] is the [f64] after [lo] and [r] lies strictly between them,
    [r] rounds down to [lo] and up to [hi]. *)
Lemma rnd_bracket :
  forall (lo hi : f64) (up : bool) r,
  is_finite lo = true -> is_finite hi = true ->
  B2R hi = succ radix2 (SpecFloat.fexp 53 1024) (B2R lo) ->
  B2R lo < r < B2R hi ->
  mpfr_round f64_format (rnd_of up) r (with_val (if up then hi else lo)).
Proof.
intros lo hi up r Flo Fhi Hs Hr.
assert (Glo : G (B2R lo)) by exact (generic_format_B2R 53 1024 lo).
assert (Ghi : G (B2R hi)) by exact (generic_format_B2R 53 1024 hi).
destruct up; apply finite_round_ok; try assumption; cbn [rnd_pt].
- split; [exact Ghi|]. split; [lra|].
  intros g Gg Hg. rewrite Hs.
  apply succ_le_lt; [typeclasses eauto | exact Glo | exact Gg | lra].
- split; [exact Glo|]. split; [lra|].
  intros g Gg Hg. destruct (Rle_or_lt g (B2R lo)) as [H|H]; [exact H|].
  assert (succ radix2 (SpecFloat.fexp 53 1024) (B2R lo) <= g)
    by (apply succ_le_lt; [typeclasses eauto | exact Glo | exact Gg | exact H]).
  lra.
Qed.

(** A real at or above [2^1024] rounds up to +inf and down to [f64::MAX],
    [2^1024 - 2^971]. [finite_round_ok] does not apply to the second, as
    [G] has elements above [f64::MAX]: the elements of [f64_format] are
    below [2^1024], so at most [f64::MAX] by [G_le_max]. *)
Lemma rnd_overflow :
  forall (up : bool) r, bpow radix2 1024 <= r ->
  mpfr_round f64_format (rnd_of up) r (with_val (DyadicExp.overflow up)).
Proof.
intros up r Hr. destruct up.
- replace (DyadicExp.overflow true) with (@B754_infinity 53 1024 false)
    by (vm_compute; reflexivity).
  cbn [with_val mpfr_round]. intros g Fg.
  destruct (f64_format_G g Fg) as [_ Hg]. apply Rabs_def2 in Hg. lra.
- change (DyadicExp.overflow false) with DyadicExp.max_f64.
  assert (Fm : is_finite DyadicExp.max_f64 = true) by (vm_compute; reflexivity).
  assert (Em : B2R DyadicExp.max_f64 = bpow radix2 1024 - bpow radix2 971).
  { lit DyadicExp.max_f64 Hm. rewrite Hm. cbn [bpow radix_val radix2]. lra. }
  assert (H971 : 0 < bpow radix2 971 < bpow radix2 1024)
    by (split; [apply bpow_gt_0 | apply bpow_lt; lia]).
  destruct (with_val_finite_cases _ Fm) as [(s & _ & H0) | (-> & H0)]; [lra|].
  cbn [mpfr_round]. split; [exact H0|].
  split; [exact (f64_format_B2R _ Fm)|]. split; [lra|].
  intros g Fg Hg. destruct (f64_format_G g Fg) as [Gg Hg'].
  apply Rabs_def2 in Hg' as [Hg' _].
  rewrite Em. apply G_le_max; [exact Gg | exact Hg'].
Qed.

(** [succ 0] is [2^-1074], [succ 1] is [1 + 2^-52], and [pred 1] is
    [1 - 2^-53]. *)
Lemma succ_zero : succ radix2 (SpecFloat.fexp 53 1024) 0 = bpow radix2 (-1074).
Proof.
rewrite succ_0. change (SpecFloat.fexp 53 1024) with (FLT_exp (-1074) 53).
apply ulp_FLT_0. unfold Prec_gt_0. lia.
Qed.

Lemma succ_one : succ radix2 (SpecFloat.fexp 53 1024) 1 = 1 + bpow radix2 (-52).
Proof.
rewrite succ_eq_pos by lra. change 1 with (bpow radix2 0) at 1 2.
rewrite ulp_bpow. reflexivity.
Qed.

Lemma pred_one : pred radix2 (SpecFloat.fexp 53 1024) 1 = 1 - bpow radix2 (-53).
Proof. change 1 with (bpow radix2 0) at 1. rewrite pred_bpow. reflexivity. Qed.

(** A real strictly between 0 and [2^-1074] rounds down to +0 and up to
    [2^-1074]. *)
Lemma rnd_underflow :
  forall (up : bool) r, 0 < r < bpow radix2 (-1074) ->
  mpfr_round f64_format (rnd_of up) r (with_val (DyadicExp.underflow up)).
Proof.
intros up r Hr. unfold DyadicExp.underflow.
assert (Em : B2R DyadicExp.min_pos = bpow radix2 (-1074)).
{ lit DyadicExp.min_pos Hm. rewrite Hm. cbn [bpow radix_val radix2]. lra. }
assert (E0 : B2R zero = 0) by reflexivity.
apply rnd_bracket.
- reflexivity.
- vm_compute. reflexivity.
- rewrite Em, E0. symmetry. exact succ_zero.
- rewrite Em, E0. exact Hr.
Qed.

(** [near_one x up] is [r] rounded in the direction [up] where [r] is 1
    if [x] is 0, between 1 and [1 + 2^-52] if [x] is positive, and between
    [1 - 2^-53] and 1 if [x] is negative. *)
Lemma rnd_near_one :
  forall x (up : bool) r, is_finite x = true ->
  (B2R x = 0 -> r = 1) ->
  (0 < B2R x -> 1 < r < 1 + bpow radix2 (-52)) ->
  (B2R x < 0 -> 1 - bpow radix2 (-53) < r < 1) ->
  mpfr_round f64_format (rnd_of up) r (with_val (DyadicExp.near_one x up)).
Proof.
intros x up r Fx H0 Hp Hn.
assert (F1 : is_finite DyadicExp.one = true) by (vm_compute; reflexivity).
assert (E1 : B2R DyadicExp.one = 1).
{ lit DyadicExp.one H. rewrite H. lra. }
assert (Fz : is_finite zero = true) by reflexivity.
assert (Ez : B2R zero = 0) by reflexivity.
unfold DyadicExp.near_one, eq, gt.
rewrite Beqb_correct by assumption. rewrite Bltb_correct by assumption.
rewrite Ez.
destruct (Req_bool_spec (B2R x) 0) as [Hx|Hx].
{ apply rnd_exact; [exact F1|]. rewrite E1. symmetry. exact (H0 Hx). }
destruct (Rlt_bool_spec 0 (B2R x)) as [Hx'|Hx'].
- apply rnd_bracket.
  + exact F1.
  + vm_compute. reflexivity.
  + rewrite E1, succ_one. lit DyadicExp.one_plus_ulp H. rewrite H.
    cbn [bpow radix_val radix2]. lra.
  + rewrite E1. lit DyadicExp.one_plus_ulp H. rewrite H.
    specialize (Hp Hx'). cbn [bpow radix_val radix2] in Hp. lra.
- assert (Hneg : B2R x < 0) by lra.
  assert (Em : B2R DyadicExp.one_minus_ulp = pred radix2 (SpecFloat.fexp 53 1024) 1).
  { rewrite pred_one. lit DyadicExp.one_minus_ulp H. rewrite H.
    cbn [bpow radix_val radix2]. lra. }
  apply rnd_bracket.
  + vm_compute. reflexivity.
  + exact F1.
  + assert (G1 : G 1) by (rewrite <- E1; exact (generic_format_B2R 53 1024 DyadicExp.one)).
    rewrite E1, Em. symmetry. apply succ_pred; [typeclasses eauto | exact G1].
  + rewrite E1, Em, pred_one. exact (Hn Hneg).
Qed.

(** The exponential of [y] with [|y| < 2^-54] is 1 if [y] is 0, and
    otherwise lies strictly between 1 and its neighbour [f64] on the side
    of the sign of [y]: [1 + y < exp y] for [y <> 0], and [exp y * (1 - y)
    < exp y * exp (-y) = 1] gives [exp y < 1 + 2^-53] for [y > 0]. *)
Lemma exp_near_one :
  forall y, Rabs y < bpow radix2 (-54) ->
  (y = 0 -> exp y = 1) /\
  (0 < y -> 1 < exp y < 1 + bpow radix2 (-52)) /\
  (y < 0 -> 1 - bpow radix2 (-53) < exp y < 1).
Proof.
intros y Hy.
assert (Hb : bpow radix2 (-52) = 4 * bpow radix2 (-54) /\
             bpow radix2 (-53) = 2 * bpow radix2 (-54) /\
             0 < bpow radix2 (-54) < 1 / 1000)
  by (cbn [bpow radix_val radix2]; lra).
apply Rabs_def2 in Hy as [Hy1 Hy2].
split; [|split].
- intros ->. exact exp_0.
- intros Hp. assert (Hl : 1 + y < exp y) by (apply exp_ineq1; lra).
  assert (Hm : 1 + - y < exp (- y)) by (apply exp_ineq1; lra).
  assert (Hpr : exp y * exp (- y) = 1)
    by (rewrite <- exp_plus, Rplus_opp_r; exact exp_0).
  assert (He : 0 < exp y) by apply exp_pos.
  (* [exp y * (1 - y) < 1], so [exp y < 2] and [exp y * y < 2 * 2^-54]. *)
  assert (H1 : exp y * (1 - y) < 1) by (rewrite <- Hpr; apply Rmult_lt_compat_l; lra).
  assert (Hh : y < 1 / 2) by lra.
  assert (H2 : exp y < 2) by nra.
  assert (H3 : exp y * y < 2 * bpow radix2 (-54)) by nra.
  lra.
- intros Hn. assert (Hl : 1 + y < exp y) by (apply exp_ineq1; lra).
  assert (Hu : exp y < exp 0) by (apply exp_increasing; lra).
  rewrite exp_0 in Hu. lra.
Qed.

(** [near_one x up] is [exp y] rounded in the direction [up] where [y]
    has the sign of [x] and [|y| < 2^-54]. *)
Lemma rnd_near_one_exp :
  forall x (up : bool) y, is_finite x = true -> Rabs y < bpow radix2 (-54) ->
  (B2R x = 0 -> y = 0) -> (0 < B2R x -> 0 < y) -> (B2R x < 0 -> y < 0) ->
  mpfr_round f64_format (rnd_of up) (exp y) (with_val (DyadicExp.near_one x up)).
Proof.
intros x up y Fx Hy H0 Hp Hn. destruct (exp_near_one y Hy) as (E0 & Ep & En).
apply rnd_near_one; [exact Fx | ..]; intros H; auto.
Qed.

(** [exp t] is above [2^1024] for [t >= 710], and below [2^-1074] for
    [t <= -746], as [1024 ln 2 < 709.79] and [1074 ln 2 < 744.45]. *)
Lemma exp_710 : forall t, 710 <= t -> bpow radix2 1024 <= exp t.
Proof.
intros t Ht. rewrite bpow_exp2. apply exp_inc.
pose proof ln2_bounds. lra.
Qed.

Lemma exp_m746 : forall t, t <= -746 -> 0 < exp t < bpow radix2 (-1074).
Proof.
intros t Ht. split; [apply exp_pos|]. rewrite bpow_exp2. apply exp_increasing.
pose proof ln2_bounds. lra.
Qed.

(** ** exp *)

Lemma exp_overflow_rule :
  forall x (up : bool), is_finite x = true -> ge x (from_bits 0x4086300000000000) = true ->
  mpfr_round f64_format (rnd_of up) (exp (B2R x)) (with_val (DyadicExp.overflow up)).
Proof.
intros x up Fx Hx. apply rnd_overflow, exp_710.
apply ge_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit (from_bits 0x4086300000000000) H. lra.
Qed.

Lemma exp_underflow_rule :
  forall x (up : bool), is_finite x = true -> le x (from_bits 0xc087500000000000) = true ->
  mpfr_round f64_format (rnd_of up) (exp (B2R x)) (with_val (DyadicExp.underflow up)).
Proof.
intros x up Fx Hx. apply rnd_underflow, exp_m746.
apply le_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit (from_bits 0xc087500000000000) H. lra.
Qed.

Lemma exp_tiny_rule :
  forall x (up : bool), is_finite x = true -> lt (fabs x) DyadicExp.tiny_exp = true ->
  mpfr_round f64_format (rnd_of up) (exp (B2R x)) (with_val (DyadicExp.near_one x up)).
Proof.
intros x up Fx Hx.
apply fabs_lt_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit DyadicExp.tiny_exp H.
apply rnd_near_one_exp; [exact Fx | | auto | auto | auto].
cbn [bpow radix_val radix2]. lra.
Qed.

(** ** exp2 *)

Lemma exp2_overflow_rule :
  forall x (up : bool), is_finite x = true -> ge x (from_bits 0x4090000000000000) = true ->
  mpfr_round f64_format (rnd_of up) (Rexp2 (B2R x)) (with_val (DyadicExp.overflow up)).
Proof.
intros x up Fx Hx. apply rnd_overflow.
apply ge_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit (from_bits 0x4090000000000000) H.
unfold Rexp2, Rpower. rewrite bpow_exp2. apply exp_inc.
pose proof ln2_bounds. apply Rmult_le_compat_r; lra.
Qed.

Lemma exp2_underflow_rule :
  forall x (up : bool), is_finite x = true -> lt x (from_bits 0xc090cc0000000000) = true ->
  mpfr_round f64_format (rnd_of up) (Rexp2 (B2R x)) (with_val (DyadicExp.underflow up)).
Proof.
intros x up Fx Hx. apply rnd_underflow.
apply lt_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit (from_bits 0xc090cc0000000000) H.
unfold Rexp2, Rpower. split; [apply exp_pos|].
rewrite bpow_exp2. apply exp_increasing.
pose proof ln2_bounds. apply Rmult_lt_compat_r; lra.
Qed.

Lemma exp2_tiny_rule :
  forall x (up : bool), is_finite x = true -> lt (fabs x) DyadicExp.tiny_exp = true ->
  mpfr_round f64_format (rnd_of up) (Rexp2 (B2R x)) (with_val (DyadicExp.near_one x up)).
Proof.
intros x up Fx Hx.
apply fabs_lt_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit DyadicExp.tiny_exp H.
pose proof ln2_bounds as Hl.
unfold Rexp2, Rpower. apply rnd_near_one_exp; [exact Fx | | | |].
- (* [|x ln 2| <= |x| < 2^-54]. *)
  rewrite Rabs_mult, (Rabs_pos_eq (ln 2)) by lra.
  pose proof (Rabs_pos (B2R x)).
  assert (Rabs (B2R x) * ln 2 <= Rabs (B2R x)) by nra.
  cbn [bpow radix_val radix2]. lra.
- intros H0. rewrite H0. ring.
- intros Hp. nra.
- intros Hn. nra.
Qed.

(** ** exp10 *)

Lemma exp10_overflow_rule :
  forall x (up : bool), is_finite x = true -> ge x (from_bits 0x4073500000000000) = true ->
  mpfr_round f64_format (rnd_of up) (Rexp10 (B2R x)) (with_val (DyadicExp.overflow up)).
Proof.
intros x up Fx Hx. apply rnd_overflow.
apply ge_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit (from_bits 0x4073500000000000) H.
unfold Rexp10, Rpower. rewrite bpow_exp2. apply exp_inc.
(* [1024 ln 2 < 709.79 < 711.49 < 309 ln 10 <= x ln 10]. *)
pose proof ln2_bounds. pose proof ln10_bounds.
assert (309 * ln 10 <= B2R x * ln 10) by (apply Rmult_le_compat_r; lra).
lra.
Qed.

Lemma exp10_underflow_rule :
  forall x (up : bool), is_finite x = true -> le x (from_bits 0xc074400000000000) = true ->
  mpfr_round f64_format (rnd_of up) (Rexp10 (B2R x)) (with_val (DyadicExp.underflow up)).
Proof.
intros x up Fx Hx. apply rnd_underflow.
apply le_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit (from_bits 0xc074400000000000) H.
unfold Rexp10, Rpower. split; [apply exp_pos|].
rewrite bpow_exp2. apply exp_increasing.
(* [x ln 10 <= -324 ln 10 < -746.03 < -744.45 < -1074 ln 2]. *)
pose proof ln2_bounds. pose proof ln10_bounds.
assert (B2R x * ln 10 <= -324 * ln 10) by (apply Rmult_le_compat_r; lra).
lra.
Qed.

Lemma exp10_tiny_rule :
  forall x (up : bool), is_finite x = true -> lt (fabs x) DyadicExp.tiny_exp10 = true ->
  mpfr_round f64_format (rnd_of up) (Rexp10 (B2R x)) (with_val (DyadicExp.near_one x up)).
Proof.
intros x up Fx Hx.
apply fabs_lt_R in Hx; [| exact Fx | vm_compute; reflexivity].
lit DyadicExp.tiny_exp10 H.
pose proof ln10_bounds as Hl.
unfold Rexp10, Rpower. apply rnd_near_one_exp; [exact Fx | | | |].
- (* [|x ln 10| < 4 |x| < 4 * 2^-56 = 2^-54]. *)
  rewrite Rabs_mult, (Rabs_pos_eq (ln 10)) by lra.
  pose proof (Rabs_pos (B2R x)).
  assert (Rabs (B2R x) * ln 10 <= 4 * Rabs (B2R x)) by nra.
  cbn [bpow radix_val radix2]. lra.
- intros H0. rewrite H0. ring.
- intros Hp. nra.
- intros Hn. nra.
Qed.

(** [10^k] for [1 <= k <= 22] is [5^k * 2^k], with [5^k < 2^53]: an
    [f64], which [pow10 k] holds exactly. *)
Lemma pow10_exact :
  forall k, (1 <= k <= 22)%Z ->
  is_finite (DyadicExp.pow10 k) = true /\ B2R (DyadicExp.pow10 k) = IZR (10 ^ k).
Proof.
intros k Hk.
assert (E : F2R (Float radix2 (10 ^ k) 0) = IZR (10 ^ k))
  by (unfold F2R; cbn [Fnum Fexp bpow]; ring).
assert (Gk : G (IZR (10 ^ k))).
{ change (SpecFloat.fexp 53 1024) with (FLT_exp (-1074) 53).
  apply generic_format_FLT.
  apply (FLT_spec _ _ _ _ (Float radix2 (5 ^ k) k)).
  - unfold F2R. cbn [Fnum Fexp].
    rewrite <- (IZR_Zpower radix2 k) by lia. rewrite <- mult_IZR.
    change (radix_val radix2) with 2%Z. rewrite <- Z.pow_mul_l. reflexivity.
  - cbn [Fnum]. rewrite Z.abs_eq by (apply Z.pow_nonneg; lia).
    assert (H5 : (5 ^ k <= 5 ^ 22)%Z) by (apply Z.pow_le_mono_r; lia).
    assert (H53 : (5 ^ 22 < radix2 ^ 53)%Z) by (vm_compute; reflexivity).
    lia.
  - cbn [Fexp]. lia. }
assert (Hlt : Rabs (IZR (10 ^ k)) < bpow radix2 1024).
{ rewrite Rabs_pos_eq by (apply IZR_le, Z.pow_nonneg; lia).
  rewrite <- (IZR_Zpower radix2 1024) by lia. apply IZR_lt.
  assert (H10 : (10 ^ k <= 10 ^ 22)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (H2 : (10 ^ 22 < radix2 ^ 1024)%Z) by (vm_compute; reflexivity).
  lia. }
pose proof (binary_normalize_correct 53 1024 _ _ mode_NE (10 ^ k) 0 false) as Hn.
cbv zeta in Hn. rewrite E in Hn.
assert (Er : round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE) (IZR (10 ^ k)) =
              IZR (10 ^ k))
  by (apply round_generic; first [exact Gk | typeclasses eauto]).
rewrite Er in Hn.
rewrite Rlt_bool_true in Hn by exact Hlt.
destruct Hn as (Hz & Fz & _). unfold DyadicExp.pow10.
split; [exact Fz | exact Hz].
Qed.

Lemma exp10_int_rule :
  forall x (up : bool), is_finite x = true ->
  le DyadicExp.one x && le x (from_bits 0x4036000000000000) && eq x (ffloor x) = true ->
  mpfr_round f64_format (rnd_of up) (Rexp10 (B2R x))
    (with_val (DyadicExp.pow10 (DyadicExp.to_i64 x))).
Proof.
intros x up Fx Hx.
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
apply rnd_exact; [exact Fp|]. rewrite Ep, Hk.
(* [10 ^ k] for the natural number [k]. *)
assert (Hn : IZR k = INR (Z.to_nat k)) by (rewrite INR_IZR_INZ, Z2Nat.id by lia; reflexivity).
unfold Rexp10. rewrite Hn, Rpower_pow by lra.
rewrite pow_IZR, Z2Nat.id by lia. reflexivity.
Qed.
