(** * The rules before Ziv's strategy for sinh, cosh and tanh

    As [DyExpRules.v] for [exp], [exp2] and [exp10]: each lemma below is
    one branch of [sinh_dir], [cosh_dir] or [tanh_dir] of [DyadicExp] in
    [Model.v] that settles a finite argument before the loop. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Elementary ExpReal ConstLn Encoding IdealGetD OfPointCore
  MpfrRound MpfrIdeal ExpSeries DyExpRules.

Open Scope R_scope.

Local Notation rnd_of up := (if up then RNDU else RNDD).

(** The format of the finite [f64]s without the bound above, as in
    [DyExpRules.v]. *)
Local Notation G := (generic_format radix2 (SpecFloat.fexp 53 1024)).

(** ** The literals of [DyadicExp] that the rules below use, as reals *)

(** [B2R l] for a literal [l]: [B2SF l] computes to its sign, significand
    and exponent. *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

Lemma hyp_lit_711 : B2R (from_bits 0x4086380000000000) = 711.
Proof. lit_B2R. cbn [bpow radix_val radix2]. lra. Qed.

Lemma hyp_lit_m711 : B2R (from_bits 0xc086380000000000) = -711.
Proof. lit_B2R. cbn [bpow radix_val radix2]. lra. Qed.

Lemma hyp_lit_19 : B2R (from_bits 0x4033000000000000) = 19.
Proof. lit_B2R. cbn [bpow radix_val radix2]. lra. Qed.

Lemma hyp_lit_m19 : B2R (from_bits 0xc033000000000000) = -19.
Proof. lit_B2R. cbn [bpow radix_val radix2]. lra. Qed.

Lemma hyp_lit_tiny : B2R DyadicExp.tiny_hyp = bpow radix2 (-26).
Proof.
lit_B2R. change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
reflexivity.
Qed.

Lemma hyp_lit_one : B2R DyadicExp.one = 1.
Proof.
lit_B2R. change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
reflexivity.
Qed.

Lemma hyp_lit_m_one : B2R DyadicExp.m_one = -1.
Proof.
lit_B2R. change (IZR 4503599627370496) with (bpow radix2 52).
rewrite <- Ropp_mult_distr_l, <- bpow_plus. reflexivity.
Qed.

Lemma hyp_lit_one_plus_ulp : B2R DyadicExp.one_plus_ulp = 1 + bpow radix2 (-52).
Proof. lit_B2R. cbn [bpow radix_val radix2]. lra. Qed.

Lemma hyp_lit_one_minus_ulp : B2R DyadicExp.one_minus_ulp = 1 - bpow radix2 (-53).
Proof. lit_B2R. cbn [bpow radix_val radix2]. lra. Qed.

Lemma hyp_lit_max : B2R DyadicExp.max_f64 = bpow radix2 1024 - bpow radix2 971.
Proof.
lit_B2R.
replace 9007199254740991%Z with (2 ^ 53 - 1)%Z by reflexivity. rewrite minus_IZR.
change (IZR (2 ^ 53)) with (bpow radix2 53). rewrite Rmult_minus_distr_r, <- bpow_plus.
change (53 + 971)%Z with 1024%Z. ring.
Qed.

Lemma hyp_with_val_inf : with_val infinity = MInf false.
Proof. vm_compute. reflexivity. Qed.

Lemma hyp_with_val_opp_inf : with_val (opp infinity) = MInf true.
Proof. vm_compute. reflexivity. Qed.

(** ** Helpers *)

(** [exp t] is above [2 * 2^1024 + 1] for [t >= 711]: [exp t = 2^1025 *
    exp (t - 1025 ln 2)], where [1025 ln 2 < 710.48] and [exp 0.5 > 1.5]
    by [exp_ineq1]. *)
Lemma exp_711 : forall t, 711 <= t -> 2 * bpow radix2 1024 + 1 <= exp t.
Proof.
intros t Ht. pose proof ln2_bounds as Hl.
assert (E : exp t = bpow radix2 1025 * exp (t - IZR 1025 * ln 2)).
{ rewrite bpow_exp2, <- exp_plus. f_equal. ring. }
assert (Hd : 1 + (t - IZR 1025 * ln 2) < exp (t - IZR 1025 * ln 2)) by (apply exp_ineq1; lra).
assert (He : 3 / 2 < exp (t - IZR 1025 * ln 2)) by lra.
assert (H2 : bpow radix2 1025 = 2 * bpow radix2 1024).
{ replace 1025%Z with (1 + 1024)%Z by reflexivity. rewrite bpow_plus. reflexivity. }
assert (HB : 1 <= bpow radix2 1024) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
rewrite E, H2. nra.
Qed.

(** [cosh] is even, so it is [cosh] of the magnitude. *)
Lemma cosh_Rabs : forall r, cosh r = cosh (Rabs r).
Proof.
intros r. unfold Rabs. destruct (Rcase_abs r); [rewrite cosh_even|]; reflexivity.
Qed.

(** [tanh t] lies strictly between [1 - 2^-53] and 1 for [t >= 19]:
    [tanh t = 1 - 2 / (exp (2 t) + 1)] ([tanh_eq]), where [exp (2 t) >=
    exp 38 > 2^54], as [54 ln 2 < 37.43]. *)
Lemma tanh_big_bounds : forall t, 19 <= t -> 1 - bpow radix2 (-53) < tanh t < 1.
Proof.
intros t Ht. rewrite tanh_eq. pose proof ln2_bounds as Hl.
assert (HE : bpow radix2 54 <= exp (2 * t)) by (rewrite bpow_exp2; apply exp_inc; lra).
assert (HB : 0 < bpow radix2 54) by apply bpow_gt_0.
assert (Hb : 0 < bpow radix2 (-53)) by apply bpow_gt_0.
assert (Hbb : bpow radix2 (-53) * bpow radix2 54 = 2) by (rewrite <- bpow_plus; reflexivity).
set (E := exp (2 * t)) in *.
assert (HI : 0 < / (E + 1)) by (apply Rinv_0_lt_compat; lra).
assert (HP : E * / (E + 1) + / (E + 1) = 1).
{ transitivity ((E + 1) * / (E + 1)); [ring | apply Rinv_r; lra]. }
(* [2 / (E + 1) = 2^-53 * (2^54 / (E + 1)) <= 2^-53 * (E / (E + 1)) < 2^-53]. *)
assert (H1 : bpow radix2 54 * / (E + 1) <= E * / (E + 1))
  by (apply Rmult_le_compat_r; lra).
assert (H2 : bpow radix2 (-53) * (bpow radix2 54 * / (E + 1)) < bpow radix2 (-53) * 1)
  by (apply Rmult_lt_compat_l; lra).
assert (H3 : 2 * / (E + 1) = bpow radix2 (-53) * (bpow radix2 54 * / (E + 1)))
  by (rewrite <- Rmult_assoc, Hbb; reflexivity).
split; lra.
Qed.

(** [cosh y] lies strictly above 1 and at most at [1 + y^2] for [0 < y <
    1/2]. Below: [exp y > 1 + y] and [exp (-y) > 1 - y] ([exp_ineq1]).
    Above: [exp (-y) <= 1 - y + y^2/2] and [exp (-y) >= 1 - y + y^2/2 -
    y^3/6 >= 1 - y + y^2/3] ([exp_alt_bounds]); with [(1 - y + y^2/3) (1 +
    y + y^2) = 1 + y^2 (1 - y)^2 / 3 >= 1] and [exp y * exp (-y) = 1], the
    latter gives [exp y <= 1 + y + y^2]. *)
Lemma cosh_tiny_bounds : forall y, 0 < y < 1 / 2 -> 1 < cosh y <= 1 + y * y.
Proof.
intros y Hy. unfold cosh.
assert (Ha : 1 + y < exp y) by (apply exp_ineq1; lra).
assert (Hb : 1 + - y < exp (- y)) by (apply exp_ineq1; lra).
assert (Hab : exp y * exp (- y) = 1) by (rewrite <- exp_plus, Rplus_opp_r; exact exp_0).
assert (Hy1 : 0 <= y <= 1) by lra.
destruct (exp_alt_bounds y 1 Hy1) as [Hlo Hhi].
assert (S3 : sum_f_R0 (tg_alt (exp_tg y)) (S (2 * 1)) = 1 - y + y * y / 2 - y * y * y / 6).
{ unfold tg_alt, exp_tg. cbn [sum_f_R0 fact pow INR Nat.mul Nat.add]. field. }
assert (S2 : sum_f_R0 (tg_alt (exp_tg y)) (2 * 1) = 1 - y + y * y / 2).
{ unfold tg_alt, exp_tg. cbn [sum_f_R0 fact pow INR Nat.mul Nat.add]. field. }
rewrite S3 in Hlo. rewrite S2 in Hhi.
assert (Hyy : 0 <= y * y) by nra.
assert (Hc : 0 <= y * y * (1 - y)) by (apply Rmult_le_pos; lra).
assert (HL : 1 - y + y * y / 3 <= exp (- y)) by lra.
assert (HL0 : 0 < 1 - y + y * y / 3) by lra.
assert (Hq : 0 <= y * y * ((1 - y) * (1 - y))) by (apply Rmult_le_pos; nra).
assert (HP : 1 <= (1 - y + y * y / 3) * (1 + y + y * y)) by lra.
assert (HU : exp y <= 1 + y + y * y).
{ apply (Rmult_le_reg_r (1 - y + y * y / 3)); [exact HL0|].
  assert (exp y * (1 - y + y * y / 3) <= exp y * exp (- y))
    by (apply Rmult_le_compat_l; [left; apply exp_pos | exact HL]).
  lra. }
split; lra.
Qed.

(** A real at or below [-2^1024] rounds down to -inf and up to
    [-f64::MAX], as [rnd_overflow] of [DyExpRules.v] mirrored. *)
Lemma rnd_overflow_neg :
  forall (up : bool) r, r <= - bpow radix2 1024 ->
  mpfr_round f64_format (rnd_of up) r (with_val (opp (DyadicExp.overflow (negb up)))).
Proof.
intros up r Hr. destruct up; cbn [negb].
- change (DyadicExp.overflow false) with DyadicExp.max_f64.
  assert (Fm : is_finite (opp DyadicExp.max_f64) = true) by (vm_compute; reflexivity).
  assert (Em : B2R (opp DyadicExp.max_f64) = - (bpow radix2 1024 - bpow radix2 971))
    by (unfold opp; rewrite B2R_Bopp, hyp_lit_max; reflexivity).
  assert (H971 : 0 < bpow radix2 971 < bpow radix2 1024)
    by (split; [apply bpow_gt_0 | apply bpow_lt; lia]).
  destruct (with_val_finite_cases _ Fm) as [(s & _ & H0) | (-> & H0)]; [lra|].
  cbn [mpfr_round]. split; [exact H0|].
  split; [exact (f64_format_B2R _ Fm)|]. split; [lra|].
  intros g Fg Hg. destruct (f64_format_G g Fg) as [Gg Hg'].
  apply Rabs_def2 in Hg' as [_ Hg'].
  assert (Gn : G (- g)) by (apply generic_format_opp; exact Gg).
  assert (Hn : - g < bpow radix2 1024) by lra.
  pose proof (G_le_max (- g) Gn Hn). rewrite Em. lra.
- replace (with_val (opp (DyadicExp.overflow true))) with (MInf true)
    by (vm_compute; reflexivity).
  cbn [mpfr_round]. intros g Fg.
  destruct (f64_format_G g Fg) as [_ Hg]. apply Rabs_def2 in Hg. lra.
Qed.

(** ** sinh *)

Lemma sinh_overflow_rule :
  forall x (up : bool), is_finite x = true -> ge x (from_bits 0x4086380000000000) = true ->
  mpfr_round f64_format (rnd_of up) (sinh (B2R x)) (with_val (DyadicExp.overflow up)).
Proof.
intros x up Fx Hx. apply rnd_overflow.
apply ge_R in Hx; [| exact Fx | vm_compute; reflexivity]. rewrite hyp_lit_711 in Hx.
pose proof (exp_711 _ Hx) as H.
assert (H1 : exp (- B2R x) <= 1) by (rewrite <- exp_0; apply exp_inc; lra).
unfold sinh. lra.
Qed.

Lemma sinh_overflow_neg_rule :
  forall x (up : bool), is_finite x = true -> le x (from_bits 0xc086380000000000) = true ->
  mpfr_round f64_format (rnd_of up) (sinh (B2R x))
    (with_val (opp (DyadicExp.overflow (negb up)))).
Proof.
intros x up Fx Hx. apply rnd_overflow_neg.
apply le_R in Hx; [| exact Fx | vm_compute; reflexivity]. rewrite hyp_lit_m711 in Hx.
assert (Ht : 711 <= - B2R x) by lra.
pose proof (exp_711 _ Ht) as H.
assert (H1 : exp (B2R x) <= 1) by (rewrite <- exp_0; apply exp_inc; lra).
unfold sinh. lra.
Qed.

(** The rule for tiny arguments is [sinh_tiny_rule] of [DySinhTiny.v]. *)

(** ** cosh *)

Lemma cosh_overflow_rule :
  forall x (up : bool), is_finite x = true -> ge (fabs x) (from_bits 0x4086380000000000) = true ->
  mpfr_round f64_format (rnd_of up) (cosh (B2R x)) (with_val (DyadicExp.overflow up)).
Proof.
intros x up Fx Hx. apply rnd_overflow.
apply ge_R in Hx; [| unfold fabs; rewrite is_finite_Babs; exact Fx | vm_compute; reflexivity].
rewrite hyp_lit_711 in Hx. unfold fabs in Hx. rewrite B2R_Babs in Hx.
pose proof (exp_711 _ Hx) as H. pose proof (exp_pos (- Rabs (B2R x))) as H1.
rewrite cosh_Rabs. unfold cosh. lra.
Qed.

Lemma cosh_tiny_rule :
  forall x (up : bool), is_finite x = true -> lt (fabs x) DyadicExp.tiny_hyp = true ->
  mpfr_round f64_format (rnd_of up) (cosh (B2R x)) (with_val (DyadicExp.near_one (fabs x) up)).
Proof.
intros x up Fx Hx.
assert (Ft : is_finite (fabs x) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fx).
assert (Et : B2R (fabs x) = Rabs (B2R x)) by (unfold fabs; apply B2R_Babs).
assert (Hy : Rabs (B2R x) < bpow radix2 (-26)).
{ rewrite <- hyp_lit_tiny. apply fabs_lt_R; [exact Fx | vm_compute; reflexivity | exact Hx]. }
assert (Hc : bpow radix2 (-26) < 1 / 2 /\ 0 < bpow radix2 (-26))
  by (cbn [bpow radix_val radix2]; lra).
assert (Hb : bpow radix2 (-26) * bpow radix2 (-26) = bpow radix2 (-52))
  by (rewrite <- bpow_plus; reflexivity).
pose proof (Rabs_pos (B2R x)) as Hp.
rewrite cosh_Rabs. apply rnd_near_one; [exact Ft | intros H; rewrite Et in H ..].
- rewrite H. unfold cosh. rewrite Ropp_0, exp_0. lra.
- assert (Hyy : Rabs (B2R x) * Rabs (B2R x) < bpow radix2 (-26) * bpow radix2 (-26))
    by (apply Rmult_le_0_lt_compat; lra).
  assert (Hy2 : 0 < Rabs (B2R x) < 1 / 2) by lra.
  destruct (cosh_tiny_bounds _ Hy2) as [H1 H2]. lra.
- lra.
Qed.

(** ** tanh *)

Lemma tanh_big_rule :
  forall x (up : bool), is_finite x = true -> ge x (from_bits 0x4033000000000000) = true ->
  mpfr_round f64_format (rnd_of up) (tanh (B2R x))
    (with_val (if up then DyadicExp.one else DyadicExp.one_minus_ulp)).
Proof.
intros x up Fx Hx.
apply ge_R in Hx; [| exact Fx | vm_compute; reflexivity]. rewrite hyp_lit_19 in Hx.
assert (G1 : G 1) by (rewrite <- hyp_lit_one; exact (generic_format_B2R 53 1024 DyadicExp.one)).
apply rnd_bracket.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- rewrite hyp_lit_one, hyp_lit_one_minus_ulp, <- pred_one. symmetry.
  apply succ_pred; [typeclasses eauto | exact G1].
- rewrite hyp_lit_one, hyp_lit_one_minus_ulp. exact (tanh_big_bounds _ Hx).
Qed.

Lemma tanh_big_neg_rule :
  forall x (up : bool), is_finite x = true -> le x (from_bits 0xc033000000000000) = true ->
  mpfr_round f64_format (rnd_of up) (tanh (B2R x))
    (with_val (if up then opp DyadicExp.one_minus_ulp else DyadicExp.m_one)).
Proof.
intros x up Fx Hx.
apply le_R in Hx; [| exact Fx | vm_compute; reflexivity]. rewrite hyp_lit_m19 in Hx.
assert (Ht : 19 <= - B2R x) by lra.
destruct (tanh_big_bounds _ Ht) as [H1 H2]. rewrite tanh_odd in H1, H2.
assert (Eo : B2R (opp DyadicExp.one_minus_ulp) = - (1 - bpow radix2 (-53)))
  by (unfold opp; rewrite B2R_Bopp, hyp_lit_one_minus_ulp; reflexivity).
apply rnd_bracket.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- rewrite Eo, hyp_lit_m_one. replace (-1) with (Ropp 1) by ring.
  rewrite succ_opp, pred_one. reflexivity.
- rewrite Eo, hyp_lit_m_one. lra.
Qed.

(** The rule for tiny arguments is [tanh_tiny_rule] of [DyTanhTiny.v]. *)
