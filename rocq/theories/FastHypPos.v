(** * The scaled result of the fast path of [sinh]

    [DyadicExp.fast_sinh_pos] of [Model.v] returns, for [t >= 0], an
    unevaluated sum [h + l] with [h] the rounding of [h + l] to nearest,
    an exponent [e] and a bound [err = 2^-p] with [|sinh t 2^-e - (h +
    l)| <= err], which the tests of [FastRoundErr.v] take
    ([fast_sinh_pos_correct]):
    - [t >= 26]: [e^t / 2] from [fast_exp_correct] of [FastExpCore.v],
      where the term [e^-t / 2] it drops is below [2^-74] once scaled, and
      fits the room [2^-72] that [fast_exp_correct] leaves below [2^-68];
    - [1/4 <= t < 26]: [(E - 1/E) / 2] for [E = e^t] from
      [fast_exp_correct] and [1/E] from the double-double quotient of
      [FastDiv.v], with [err = 2^-67];
    - [2^-27 <= t < 1/4]: the polynomial of [FastHypPoly.v], scaled by
      [Fast.normalize], with [err = 2^-63].
    It returns the same with and without an FMA ([fast_sinh_pos_fma]).
    [FastCoshPos.v] proves the same of [cosh] with the lemmas here. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error.
From Inari Require Import Model Mpfr Encoding Elementary TwoSum TwoProduct MulRuTiny DyDriver
  NearF64 FastRound FastExpTables FastExpCore FastRoundErr FastDiv FastHypPoly.
From Inari Require DyExpRules CancelLanes SqrtSlow.

Open Scope R_scope.

Local Notation G := (generic_format radix2 fexp64).
Local Notation succ64 := (succ radix2 fexp64).
Local Notation pred64 := (pred radix2 fexp64).

(** ** Literals and comparisons *)

(** [B2R l] of an [f64] literal [l], as [m * 2^e] (as in [FastExp.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** A literal [2^k] with a mantissa of [2^52]. *)
Local Ltac lit_pow2 :=
  lit_B2R; change (IZR 4503599627370496) with (bpow radix2 52); rewrite <- bpow_plus;
  reflexivity.

Lemma lit_26 : B2R (from_bits 0x403a000000000000) = 26.
Proof. lit_B2R. cbn [bpow radix_val radix2]. lra. Qed.

Lemma lit_quarter : B2R (from_bits 0x3fd0000000000000) = bpow radix2 (-2).
Proof. lit_pow2. Qed.

Lemma lit_tiny : B2R DyadicExp.tiny_near = bpow radix2 (-27).
Proof. lit_pow2. Qed.

Lemma lit_two : B2R DyadicExp.two = 2.
Proof. lit_B2R. cbn [bpow radix_val radix2]. lra. Qed.

Lemma lit_half : B2R Model.half = / 2.
Proof. lit_B2R. cbn [bpow radix_val radix2]. lra. Qed.

Lemma lit_err63 : B2R DyadicExp.err63 = bpow radix2 (-63).
Proof. lit_pow2. Qed.

Lemma lit_err67 : B2R DyadicExp.err67 = bpow radix2 (-67).
Proof. lit_pow2. Qed.

Lemma lit_err68 : B2R DyadicExp.err68 = bpow radix2 (-68).
Proof. lit_pow2. Qed.

Lemma lt_true :
  forall x y, is_finite x = true -> is_finite y = true -> Model.lt x y = true -> B2R x < B2R y.
Proof.
intros x y Fx Fy H. unfold Model.lt in H. rewrite Bltb_correct in H by assumption.
destruct (Rlt_bool_spec (B2R x) (B2R y)); [assumption | discriminate].
Qed.

Lemma lt_false :
  forall x y, is_finite x = true -> is_finite y = true -> Model.lt x y = false -> B2R y <= B2R x.
Proof.
intros x y Fx Fy H. unfold Model.lt in H. rewrite Bltb_correct in H by assumption.
destruct (Rlt_bool_spec (B2R x) (B2R y)); [discriminate | assumption].
Qed.

(** ** Rounding to nearest *)

(** [|RN z - z| <= 2^k] for [|z| <= 2^(k + 53)]: half an ulp of [2^(k + 53)]. *)
Lemma rn_err :
  forall z k, (-1074 <= k)%Z -> Rabs z <= bpow radix2 (k + 53) -> Rabs (RN z - z) <= bpow radix2 k.
Proof.
intros z k Hk Hz.
apply Rle_trans with (/ 2 * ulp radix2 fexp64 z).
{ apply error_le_half_ulp; typeclasses eauto. }
apply Rle_trans with (/ 2 * ulp radix2 fexp64 (bpow radix2 (k + 53))).
{ apply Rmult_le_compat_l; [lra|].
  apply ulp_le; [typeclasses eauto .. |].
  rewrite (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0. exact Hz. }
rewrite ulp_bpow.
replace (FLT_exp (-1074) 53 (k + 53 + 1)) with (1 + k)%Z by (unfold FLT_exp; lia).
rewrite bpow_plus. change (bpow radix2 1) with 2. lra.
Qed.

(** The ulp of a value from [1/2] on is at least [2^-53]. *)
Lemma ulp_ge_53 : forall v, / 2 <= v -> bpow radix2 (-53) <= ulp radix2 fexp64 v.
Proof.
intros v Hv.
replace (bpow radix2 (-53)) with (ulp radix2 fexp64 (bpow radix2 (-1)))
  by (rewrite ulp_bpow; reflexivity).
apply ulp_le_pos; [typeclasses eauto .. | apply bpow_ge_0 |].
change (bpow radix2 (-1)) with (/ 2). exact Hv.
Qed.

(** A float [x > 1/2] absorbs a [z] below [2^-54]: both gaps around [x]
    are at least [2^-53]. It covers [x = 2], where the gap below is
    [2^-52], and no other [x] needs it here. *)
Lemma rn_absorb :
  forall x z, G x -> / 2 < x -> Rabs z < bpow radix2 (-54) -> RN (x + z) = x.
Proof.
intros x z Fx Hx Hz.
pose proof (pred_ge_half x Fx Hx) as P1.
pose proof (succ_pred radix2 fexp64 x Fx) as P2.
rewrite succ_eq_pos in P2 by lra.
pose proof (ulp_ge_53 _ P1) as P3.
assert (S1 : succ64 x = x + ulp radix2 fexp64 x) by (apply succ_eq_pos; lra).
pose proof (ulp_ge_53 x ltac:(lra)) as S2.
assert (K : bpow radix2 (-54) * 2 = bpow radix2 (-53)).
{ change 2 with (bpow radix2 1). rewrite <- bpow_plus. reflexivity. }
apply Rabs_lt_inv in Hz.
apply rn_between; [exact Fx | lra | lra].
Qed.

(** [h = RN(h + l)] with [1/2 < h < 2] leaves [|l| <= 2^-53]. *)
Lemma low53 :
  forall h l : f64, is_finite h = true -> B2R h = RN (B2R h + B2R l) -> / 2 < B2R h < 2 ->
  Rabs (B2R l) <= bpow radix2 (-53).
Proof.
intros h l Fh Hrn Hh.
destruct (low_bounds h l Fh Hrn Hh) as (L1 & L2 & _).
assert (Fx : G (B2R h)) by apply generic_format_B2R.
assert (K : bpow radix2 (-53) <= bpow radix2 (-52) /\ bpow radix2 (-53) * 2 = bpow radix2 (-52)).
{ split; [apply bpow_le; lia|].
  change 2 with (bpow radix2 1). rewrite <- bpow_plus. reflexivity. }
assert (S : succ64 (B2R h) - B2R h <= bpow radix2 (-52)).
{ destruct (Rle_lt_dec 1 (B2R h)).
  - rewrite succ_hi by lra. lra.
  - rewrite succ_lo by lra. lra. }
assert (P : B2R h - pred64 (B2R h) <= bpow radix2 (-52)).
{ destruct (Rlt_le_dec 1 (B2R h)).
  - rewrite pred_hi by (assumption || lra). lra.
  - rewrite pred_lo by (assumption || lra). lra. }
apply Rabs_le. lra.
Qed.

(** [x * y] is finite and rounded to nearest if the exact result is at
    most [2^1023 + 2^971] in magnitude. *)
Lemma mul_fin :
  forall x y, is_finite x = true -> is_finite y = true ->
  Rabs (B2R x * B2R y) <= bpow radix2 1023 + bpow radix2 971 ->
  is_finite (mul x y) = true /\ B2R (mul x y) = RN (B2R x * B2R y).
Proof.
intros x y Fx Fy H.
generalize (@Bmult_correct 53 1024 _ _ mode_NE x y).
rewrite Rlt_bool_true by exact (RN_no_overflow _ H).
intros (HR & HF & _).
split; [unfold mul; rewrite HF, Fx, Fy; reflexivity | exact HR].
Qed.

(** ** What [fast_exp] returns for [t >= 0] *)

(** [exp 26 <= 2^38] and [2^74 <= exp 52], as [26.34 < 38 ln 2] and [74 ln 2 < 51.3]. *)
Lemma exp_26 : exp 26 <= bpow radix2 38.
Proof.
rewrite bpow_exp. apply exp_le. destruct DyExpRules.ln2_bounds as [L1 L2].
change (IZR (radix_val radix2)) with 2. lra.
Qed.

Lemma exp_52 : bpow radix2 74 <= exp 52.
Proof.
rewrite bpow_exp. apply exp_le. destruct DyExpRules.ln2_bounds as [L1 L2].
change (IZR (radix_val radix2)) with 2. lra.
Qed.

(** [fast_exp_correct] for [zl = 0], with [|l| <= 2^-53] and [e >= -1]:
    [e^t >= 1] and [e^t 2^-e < 3] leave [2^-e < 4]. *)
Lemma fe_facts :
  forall fma t h l e,
  is_finite t = true -> 0 <= B2R t ->
  DyadicExp.fast_exp fma t zero = Some (h, l, e) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < B2R h < 2 /\ (-1 <= e <= 1022)%Z /\ Rabs (B2R l) <= bpow radix2 (-53) /\
  Rabs (exp (B2R t) * bpow radix2 (- e) - (B2R h + B2R l))
    <= bpow radix2 (-68) - bpow radix2 (-72).
Proof.
intros fma t h l e Ft Ht H.
assert (Z0 : Rabs (B2R zero) <= bpow radix2 (-40))
  by (change (B2R zero) with 0; rewrite Rabs_R0; apply bpow_ge_0).
destruct (fast_exp_correct fma t zero h l e Ft eq_refl Z0 H) as (Fh & Fl & Eh & Hh & He & Herr).
change (B2R zero) with 0 in Herr. rewrite Rplus_0_r in Herr.
pose proof (low53 h l Fh Eh Hh) as Hl.
assert (E1 : 1 <= exp (B2R t)) by (rewrite <- exp_0; apply exp_le; exact Ht).
assert (He1 : (-1 <= e)%Z).
{ destruct (Z_lt_le_dec e (-1)) as [Hlt|Hge]; [exfalso | exact Hge].
  assert (P4 : 4 <= bpow radix2 (- e)) by (change 4 with (bpow radix2 2); apply bpow_le; lia).
  assert (EP : 1 * 4 <= exp (B2R t) * bpow radix2 (- e)) by (apply Rmult_le_compat; lra).
  assert (K : bpow radix2 (-53) <= / 4 /\ bpow radix2 (-68) <= / 4 /\ 0 < bpow radix2 (-72))
    by (cbn [bpow radix_val radix2]; repeat split; lra).
  apply Rabs_le_inv in Herr. apply Rabs_le_inv in Hl. lra. }
refine (conj Fh (conj Fl (conj Eh (conj Hh (conj _ (conj Hl Herr)))))). lia.
Qed.

(** For [t < 26], [e <= 39]: [e^t 2^-e > 1/4] and [e^t < 2^38] leave [2^-e > 2^-40]. *)
Lemma fe_mid :
  forall (t h l : f64) e,
  B2R t < 26 -> / 2 < B2R h < 2 -> Rabs (B2R l) <= bpow radix2 (-53) ->
  Rabs (exp (B2R t) * bpow radix2 (- e) - (B2R h + B2R l))
    <= bpow radix2 (-68) - bpow radix2 (-72) ->
  (e <= 39)%Z.
Proof.
intros t h l e Ht Hh Hl Herr.
destruct (Z_le_gt_dec e 39) as [|Hgt]; [assumption | exfalso].
assert (P : bpow radix2 (- e) <= bpow radix2 (-40)) by (apply bpow_le; lia).
assert (E : exp (B2R t) <= bpow radix2 38).
{ apply Rle_trans with (exp 26); [apply exp_le; lra | apply exp_26]. }
assert (EP : exp (B2R t) * bpow radix2 (- e) <= bpow radix2 38 * bpow radix2 (-40)).
{ apply Rmult_le_compat; [apply Rlt_le, exp_pos | apply bpow_ge_0 | exact E | exact P]. }
rewrite <- bpow_plus in EP.
assert (K : bpow radix2 (38 + -40) = / 4 /\ bpow radix2 (-53) <= / 64 /\
            bpow radix2 (-68) <= / 64 /\ 0 < bpow radix2 (-72))
  by (cbn [bpow radix_val radix2 Z.add]; repeat split; lra).
apply Rabs_le_inv in Herr. apply Rabs_le_inv in Hl. lra.
Qed.

(** The term [e^-t 2^-e] that the range [t >= 26] drops is at most
    [3 / 2^74 <= 2^-72], as [e^(2 t) >= 2^74]. *)
Lemma tail_small :
  forall x P, 26 <= x -> 0 <= P -> exp x * P <= 3 -> exp (- x) * P <= bpow radix2 (-72).
Proof.
intros x P Hx HP H3.
assert (E52 : bpow radix2 74 <= exp x * exp x).
{ rewrite <- exp_plus. apply Rle_trans with (exp 52); [apply exp_52 | apply exp_le; lra]. }
assert (Ex : 0 < exp x) by apply exp_pos.
assert (Ex' : exp x <> 0) by (apply Rgt_not_eq; exact Ex).
rewrite exp_Ropp.
replace (/ exp x * P) with ((exp x * P) * / (exp x * exp x)) by (field; exact Ex').
apply Rle_trans with (3 * / bpow radix2 74).
- apply Rmult_le_compat; [apply Rmult_le_pos; lra | | exact H3 |].
  + left. apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; exact Ex.
  + apply Rinv_le_contravar; [apply bpow_gt_0 | exact E52].
- rewrite <- bpow_opp. cbn [bpow radix_val radix2 Z.opp]. lra.
Qed.

(** [cosh t 2^-(e - 1)] and [sinh t 2^-(e - 1)] as [E P + P / E] and
    [E P - P / E], for [E = e^t] and [P = 2^-e]. *)
Lemma cosh_scale :
  forall x e,
  cosh x * bpow radix2 (- (e - 1)) = exp x * bpow radix2 (- e) + exp (- x) * bpow radix2 (- e).
Proof.
intros x e. replace (- (e - 1))%Z with (1 + - e)%Z by lia.
rewrite bpow_plus. change (bpow radix2 1) with 2. unfold cosh. field.
Qed.

Lemma sinh_scale :
  forall x e,
  sinh x * bpow radix2 (- (e - 1)) = exp x * bpow radix2 (- e) - exp (- x) * bpow radix2 (- e).
Proof.
intros x e. replace (- (e - 1))%Z with (1 + - e)%Z by lia.
rewrite bpow_plus. change (bpow radix2 1) with 2. unfold sinh. field.
Qed.

(** ** The quotient [2^-2e / (h + l)] of the middle range *)

(** [two_pow (-2 e)] is [2^-e 2^-e], between [2^-80] and 4. *)
Lemma tp_facts :
  forall e, (-1 <= e <= 39)%Z ->
  is_finite (DyadicExp.two_pow (-2 * e)) = true /\
  B2R (DyadicExp.two_pow (-2 * e)) = bpow radix2 (- e) * bpow radix2 (- e) /\
  bpow radix2 (-80) <= B2R (DyadicExp.two_pow (-2 * e)) <= 4.
Proof.
intros e He. unfold DyadicExp.two_pow.
destruct (pow2_bits (-2 * e)) as (F & R); [lia|].
rewrite R. split; [exact F|]. split.
- rewrite <- bpow_plus. f_equal. lia.
- split; [apply bpow_le; lia|]. change 4 with (bpow radix2 2). apply bpow_le. lia.
Qed.

(** The hypotheses of [dd_div_correct] for [nh = two_pow (-2 e)], [nl = 0],
    [dh = h] and [dl = l]. *)
Lemma dd_hyps :
  forall (h l : f64) e,
  / 2 < B2R h < 2 -> Rabs (B2R l) <= bpow radix2 (-53) -> (-1 <= e <= 39)%Z ->
  Rabs (B2R zero) <= bpow radix2 (-50) * B2R (DyadicExp.two_pow (-2 * e)) /\
  / 2 <= B2R h <= 4 /\ Rabs (B2R l) <= bpow radix2 (-52) * B2R h.
Proof.
intros h l e Hh Hl He.
destruct (tp_facts e He) as (_ & _ & Bn).
pose proof (bpow_gt_0 radix2 (-80)) as B80.
split; [|split; [lra|]].
- change (B2R zero) with 0. rewrite Rabs_R0.
  apply Rmult_le_pos; [apply bpow_ge_0 | lra].
- assert (K : bpow radix2 (-52) * / 2 = bpow radix2 (-53)).
  { change (/ 2) with (bpow radix2 (-1)). rewrite <- bpow_plus. reflexivity. }
  apply Rle_trans with (bpow radix2 (-52) * / 2); [lra|].
  apply Rmult_le_compat_l; [apply bpow_ge_0 | lra].
Qed.

(** [P / E] and the quotient [q = P P / y] of the middle range, through
    [r = P / (E y)]: [P / E - q = - (E P - y) r] and [q = r E P], so the
    error [E P - y] of [fast_exp] passes to [P / E] scaled by [r]. *)
Lemma quot_split :
  forall E P y, 0 < E -> 0 < P -> 0 < y ->
  exists r, 0 < r /\ r * y * (E * E) = E * P /\
    / E * P - P * P / y = - (E * P - y) * r /\ P * P / y = r * (E * P).
Proof.
intros E P y HE HP Hy.
assert (E0 : E <> 0) by (apply Rgt_not_eq; exact HE).
assert (Y0 : y <> 0) by (apply Rgt_not_eq; exact Hy).
exists (P / (E * y)).
split; [apply Rdiv_lt_0_compat; [exact HP | apply Rmult_lt_0_compat; assumption]|].
split; [field; split; assumption|].
split; field; split; assumption.
Qed.

(** ** The range [t >= 26] *)

(** [h + l] is [e^t 2^-e] within [2^-68 - 2^-72], and the term [e^-t
    2^-e] that [sinh] drops is at most [2^-72] ([tail_small]). *)
Local Lemma sinh_large_core :
  forall fma t h l e,
  is_finite t = true -> 26 <= B2R t ->
  DyadicExp.fast_exp fma t zero = Some (h, l, e) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= e - 1 <= 1022)%Z /\
  Rabs (sinh (B2R t) * bpow radix2 (- (e - 1)) - (B2R h + B2R l)) <= bpow radix2 (-68).
Proof.
intros fma t h l e Ft Ht H.
destruct (fe_facts fma t h l e Ft ltac:(lra) H) as (Fh & Fl & Eh & Hh & He & Hl & Herr).
assert (He' : (-1021 <= e - 1 <= 1022)%Z) by lia.
refine (conj Fh (conj Fl (conj Eh (conj He' _)))).
rewrite sinh_scale.
assert (K : bpow radix2 (-53) <= / 4 /\ bpow radix2 (-68) <= / 4 /\ 0 <= bpow radix2 (-72))
  by (cbn [bpow radix_val radix2]; repeat split; lra).
apply Rabs_le_inv in Herr. apply Rabs_le_inv in Hl.
pose proof (bpow_gt_0 radix2 (- e)) as HP.
assert (E3 : exp (B2R t) * bpow radix2 (- e) <= 3) by lra.
pose proof (tail_small (B2R t) (bpow radix2 (- e)) Ht (Rlt_le _ _ HP) E3) as T.
assert (T0 : 0 <= exp (- B2R t) * bpow radix2 (- e))
  by (apply Rmult_le_pos; [apply Rlt_le, exp_pos | lra]).
apply Rabs_le. lra.
Qed.

(** ** The range [1/4 <= t < 26] *)

(** With [E = e^t], [P = 2^-e] and [y = h + l] from [fast_exp], [wh + wl]
    is [q = P P / y] within [2^-98 q] ([dd_div_correct]), [s + s0] is [h -
    wh] exactly and [h' + l'] is [s + RN (RN (s0 + l) - wl)] exactly
    ([two_sum_correct], Knuth's TwoSum), so [h' + l'] is [y - (wh + wl)]
    up to two roundings of at most [2^-101] and [2^-100]. As [P / E - q =
    - (E P - y) r] with [r = P / (E y) <= 7/10] ([quot_split], [E E >=
    e^(1/2) >= 3/2]), the error is [(E P - y) (1 + r)] plus those, at most
    [1.7 (2^-68 - 2^-72) + 3 2^-98 + 2^-101 + 2^-100 <= 2^-67]. *)
Local Lemma sinh_mid_core :
  forall fma t h0 l0 e0 wh wl s s0 h1 l1,
  is_finite t = true -> / 4 <= B2R t < 26 ->
  DyadicExp.fast_exp fma t zero = Some (h0, l0, e0) ->
  Fast.dd_div fma (DyadicExp.two_pow (-2 * e0)) zero h0 l0 = (wh, wl) ->
  Fast.two_sum h0 (opp wh) = (s, s0) ->
  Fast.two_sum s (sub (add s0 l0) wl) = (h1, l1) ->
  is_finite h1 = true /\ is_finite l1 = true /\ B2R h1 = RN (B2R h1 + B2R l1) /\
  (-1021 <= e0 - 1 <= 1022)%Z /\
  Rabs (sinh (B2R t) * bpow radix2 (- (e0 - 1)) - (B2R h1 + B2R l1)) <= bpow radix2 (-67).
Proof.
intros fma t h0 l0 e0 wh wl s s0 h1 l1 Ft Ht Hfe Hdd Hs1 Hs2.
assert (Ht0 : 0 <= B2R t) by lra.
destruct (fe_facts fma t h0 l0 e0 Ft Ht0 Hfe) as (Fh0 & Fl0 & Eh0 & Hh0 & He0 & Hl0 & Herr).
assert (Ht26 : B2R t < 26) by lra.
pose proof (fe_mid t h0 l0 e0 Ht26 Hh0 Hl0 Herr) as He1.
assert (He : (-1 <= e0 <= 39)%Z) by lia.
assert (He' : (-1021 <= e0 - 1 <= 1022)%Z) by lia.
(* The constants. *)
assert (K : bpow radix2 (-53) <= / 64 /\ bpow radix2 (-68) <= / 64 /\ 0 <= bpow radix2 (-72) /\
            bpow radix2 (-98) * 3 <= / 64 /\ bpow radix2 (-50) <= / 64 /\
            bpow radix2 (-49) + bpow radix2 (-53) <= bpow radix2 (-48) /\
            bpow radix2 (-48) + bpow radix2 (-101) + bpow radix2 (-50) <= bpow radix2 (-47) /\
            bpow radix2 (-47) + bpow radix2 (-100) <= 1 /\
            (bpow radix2 (-68) - bpow radix2 (-72)) * (17 / 10) + bpow radix2 (-98) * 3 +
              bpow radix2 (-101) + bpow radix2 (-100) <= bpow radix2 (-67))
  by (cbn [bpow radix_val radix2]; repeat split; lra).
assert (K0 : 0 < bpow radix2 (-101) /\ 0 < bpow radix2 (-100) /\ 0 < bpow radix2 (-98) /\
             0 < bpow radix2 (-53) /\ 0 < bpow radix2 (-50) /\ 0 < bpow radix2 (-49))
  by (repeat split; apply bpow_gt_0).
assert (B : 32 <= bpow radix2 1023 /\ 0 <= bpow radix2 971).
{ split; [change 32 with (bpow radix2 5); apply bpow_le; lia | apply bpow_ge_0]. }
pose proof Herr as Herr'. apply Rabs_le_inv in Herr'.
pose proof Hl0 as Hl0'. apply Rabs_le_inv in Hl0'.
(* The quotient [wh + wl] of [P P] by [y]. *)
destruct (tp_facts e0 He) as (Fn & Rn & Bn).
destruct (dd_hyps h0 l0 e0 Hh0 Hl0 He) as (N1 & D1 & D2).
pose proof (dd_div_correct fma (DyadicExp.two_pow (-2 * e0)) zero h0 l0 Fn eq_refl Fh0 Fl0
  Bn N1 D1 D2) as DD.
rewrite Hdd in DD. cbv beta iota in DD.
destruct DD as (Fwh & Fwl & Ewh & Hw).
change (B2R zero) with 0 in Hw. rewrite Rplus_0_r, Rn in Hw.
assert (Hy : 0 < B2R h0 + B2R l0) by lra.
destruct (quot_split (exp (B2R t)) (bpow radix2 (- e0)) (B2R h0 + B2R l0) (exp_pos _)
  (bpow_gt_0 _ _) Hy) as (r & Hr0 & Hr1 & Hr2 & Hr3).
assert (EE : 3 / 2 <= exp (B2R t) * exp (B2R t)).
{ rewrite <- exp_plus. pose proof (exp_ineq1_le (B2R t + B2R t)). lra. }
assert (Hr : r <= 7 / 10).
{ assert (A : r * (B2R h0 + B2R l0) * (3 / 2) <=
              r * (B2R h0 + B2R l0) * (exp (B2R t) * exp (B2R t)))
    by (apply Rmult_le_compat_l; [apply Rmult_le_pos; lra | exact EE]).
  destruct (Rle_lt_dec r (7 / 10)) as [|Hlt]; [assumption | exfalso].
  assert (A2 : 7 / 10 * (B2R h0 + B2R l0) < r * (B2R h0 + B2R l0))
    by (apply Rmult_lt_compat_r; lra).
  lra. }
rewrite Hr3 in Hw.
assert (EP : 0 <= exp (B2R t) * bpow radix2 (- e0) <= 3).
{ split; [apply Rmult_le_pos; [apply Rlt_le, exp_pos | apply bpow_ge_0] | lra]. }
assert (Q : 0 <= r * (exp (B2R t) * bpow radix2 (- e0)) <= 3).
{ split; [apply Rmult_le_pos; lra|].
  apply Rle_trans with (1 * 3); [apply Rmult_le_compat; lra | lra]. }
assert (Hw' : Rabs (B2R wh + B2R wl - r * (exp (B2R t) * bpow radix2 (- e0)))
              <= bpow radix2 (-98) * 3).
{ eapply Rle_trans; [exact Hw|]. apply Rmult_le_compat_l; [apply bpow_ge_0 | lra]. }
apply Rabs_le_inv in Hw'.
assert (W8 : Rabs (B2R wh + B2R wl) <= bpow radix2 3)
  by (change (bpow radix2 3) with 8; apply Rabs_le; lra).
pose proof (rn_err (B2R wh + B2R wl) (-50) ltac:(lia) W8) as Hwl.
rewrite <- Ewh in Hwl.
replace (B2R wh - (B2R wh + B2R wl)) with (- B2R wl) in Hwl by ring.
rewrite Rabs_Ropp in Hwl. apply Rabs_le_inv in Hwl.
(* [s + s0 = h - wh]. *)
assert (Fo : is_finite (opp wh) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fwh).
assert (Eo : B2R (opp wh) = - B2R wh) by (unfold opp; apply B2R_Bopp).
assert (Z1 : Rabs (B2R h0 + B2R (opp wh)) <= bpow radix2 1023 + bpow radix2 971)
  by (rewrite Eo; apply Rabs_le; lra).
destruct (add_no_overflow h0 (opp wh) Fh0 Fo Z1) as (Fs & Rs).
assert (Z2 : Rabs (B2R h0) < bpow radix2 1023) by (apply Rabs_lt; lra).
assert (Z3 : Rabs (B2R (opp wh)) < bpow radix2 1023) by (rewrite Eo; apply Rabs_lt; lra).
pose proof (two_sum_correct h0 (opp wh) Fh0 Fo Z2 Z3 Fs) as TS1.
rewrite Hs1 in TS1. cbv beta iota in TS1. destruct TS1 as (Es & Fs0 & Es0).
rewrite <- Es in Fs, Rs. rewrite Eo in Rs, Es0.
assert (Z4 : Rabs (B2R h0 + - B2R wh) <= bpow radix2 (-49 + 53))
  by (change (bpow radix2 (-49 + 53)) with 16; apply Rabs_le; lra).
pose proof (rn_err _ (-49) ltac:(lia) Z4) as Hs0.
rewrite <- Rs in Hs0. apply Rabs_le_inv in Hs0.
(* [a = RN (s0 + l)] and [b = RN (a - wl)]. *)
assert (Z5 : Rabs (B2R s0 + B2R l0) <= bpow radix2 (-48)) by (apply Rabs_le; lra).
assert (Z6 : Rabs (B2R s0 + B2R l0) <= bpow radix2 1023 + bpow radix2 971)
  by (apply Rabs_le; apply Rabs_le_inv in Z5; lra).
destruct (add_no_overflow s0 l0 Fs0 Fl0 Z6) as (Fa & Ra).
pose proof (rn_err _ (-101) ltac:(lia) Z5) as Ha.
rewrite <- Ra in Ha. apply Rabs_le_inv in Ha. apply Rabs_le_inv in Z5.
assert (Z7 : Rabs (B2R (add s0 l0) - B2R wl) <= bpow radix2 (-47)) by (apply Rabs_le; lra).
assert (Z8 : Rabs (B2R (add s0 l0) - B2R wl) <= bpow radix2 1023 + bpow radix2 971)
  by (apply Rabs_le; apply Rabs_le_inv in Z7; lra).
destruct (sub_no_overflow (add s0 l0) wl Fa Fwl Z8) as (Fb & Rb).
pose proof (rn_err _ (-100) ltac:(lia) Z7) as Hb.
rewrite <- Rb in Hb. apply Rabs_le_inv in Hb. apply Rabs_le_inv in Z7.
(* [h' + l' = s + b]. *)
assert (Z9 : Rabs (B2R s + B2R (sub (add s0 l0) wl)) <= bpow radix2 1023 + bpow radix2 971)
  by (apply Rabs_le; lra).
destruct (add_no_overflow s (sub (add s0 l0) wl) Fs Fb Z9) as (Fh1 & Rh1).
assert (Z10 : Rabs (B2R s) < bpow radix2 1023) by (apply Rabs_lt; lra).
assert (Z11 : Rabs (B2R (sub (add s0 l0) wl)) < bpow radix2 1023) by (apply Rabs_lt; lra).
pose proof (two_sum_correct s (sub (add s0 l0) wl) Fs Fb Z10 Z11 Fh1) as TS2.
rewrite Hs2 in TS2. cbv beta iota in TS2. destruct TS2 as (Eh1 & Fl1 & El1).
rewrite <- Eh1 in Fh1, Rh1.
refine (conj Fh1 (conj Fl1 (conj _ (conj He' _)))).
{ rewrite El1. replace (B2R h1 + (B2R s + B2R (sub (add s0 l0) wl) - B2R h1))
    with (B2R s + B2R (sub (add s0 l0) wl)) by ring.
  exact Rh1. }
(* The error. *)
assert (DR : Rabs ((exp (B2R t) * bpow radix2 (- e0) - (B2R h0 + B2R l0)) * (1 + r))
             <= (bpow radix2 (-68) - bpow radix2 (-72)) * (17 / 10)).
{ rewrite Rabs_mult, (Rabs_pos_eq (1 + r)) by lra.
  apply Rmult_le_compat; [apply Rabs_pos | lra | exact Herr | lra]. }
apply Rabs_le_inv in DR.
rewrite sinh_scale, exp_Ropp.
apply Rabs_le. lra.
Qed.

(** ** The range [2^-27 <= t < 1/4] *)

(** The polynomial gives [sh + sl] within [2^-65 S] of [S = sinh t]
    ([sinh_poly_correct]), so [S <= 2 sh], and [normalize] scales both by
    [2^-k] with [sh 2^-k < 2] ([normalize_correct]): the error is at most
    [2^-65 S 2^-k <= 2^-64 sh 2^-k < 2^-63]. *)
Local Lemma sinh_small_core :
  forall fma t sh sl h l k,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < / 4 ->
  DyadicExp.fast_sinh_poly fma t = (sh, sl) ->
  Fast.normalize sh sl = (h, l, k) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= k <= 1022)%Z /\
  Rabs (sinh (B2R t) * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-63).
Proof.
intros fma t sh sl h l k Ft Ht Hp Hn.
pose proof (sinh_poly_correct fma t Ft Ht) as SP.
rewrite Hp in SP. cbv beta iota in SP.
destruct SP as (Fsh & Fsl & Esh & Hsh & Hsl & Herr).
assert (Hsh' : bpow radix2 (-1021) <= B2R sh < 2).
{ split; [|lra]. apply Rle_trans with (bpow radix2 (-27)); [apply bpow_le; lia | lra]. }
pose proof (normalize_correct sh sl Fsh Fsl Esh Hsh') as NC.
rewrite Hn in NC. cbv beta iota in NC.
destruct NC as (Fh & Fl & Hk & Eh & El & Hb & Eh').
assert (Hk' : (-1021 <= k <= 1022)%Z) by lia.
refine (conj Fh (conj Fl (conj Eh' (conj Hk' _)))).
rewrite Eh, El.
replace (sinh (B2R t) * bpow radix2 (- k) - (B2R sh * bpow radix2 (- k) + B2R sl * bpow radix2 (- k)))
  with ((sinh (B2R t) - (B2R sh + B2R sl)) * bpow radix2 (- k)) by ring.
rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (- k))) by apply bpow_ge_0.
rewrite Rabs_minus_sym.
(* [S <= 2 sh]. *)
pose proof (bpow_ge_0 radix2 (-27)) as K27.
assert (S0 : 0 <= sinh (B2R t)).
{ unfold sinh. assert (X : exp (- B2R t) <= exp (B2R t)) by (apply exp_le; lra). lra. }
assert (K : 0 <= / 4 - bpow radix2 (-65) /\ 0 <= / 4 - bpow radix2 (-52))
  by (cbn [bpow radix_val radix2]; split; lra).
assert (A1 : 0 <= sinh (B2R t) * (/ 4 - bpow radix2 (-65))) by (apply Rmult_le_pos; lra).
assert (A2 : 0 <= B2R sh * (/ 4 - bpow radix2 (-52))) by (apply Rmult_le_pos; lra).
pose proof Herr as Herr'. apply Rabs_le_inv in Herr'. apply Rabs_le_inv in Hsl.
assert (S2 : sinh (B2R t) <= 2 * B2R sh) by lra.
(* [h = sh 2^-k < 2]. *)
assert (H2 : B2R sh * bpow radix2 (- k) < 2).
{ apply Rlt_le_trans with (bpow radix2 (k + 1) * bpow radix2 (- k)).
  - apply Rmult_lt_compat_r; [apply bpow_gt_0 | lra].
  - rewrite <- bpow_plus. replace (k + 1 + - k)%Z with 1%Z by ring.
    change (bpow radix2 1) with 2. lra. }
apply Rle_trans with (bpow radix2 (-65) * sinh (B2R t) * bpow radix2 (- k)).
{ apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Herr]. }
apply Rle_trans with (bpow radix2 (-65) * ((2 * B2R sh) * bpow radix2 (- k))).
{ rewrite Rmult_assoc. apply Rmult_le_compat_l; [apply bpow_ge_0|].
  apply Rmult_le_compat_r; [apply bpow_ge_0 | exact S2]. }
assert (K4 : bpow radix2 (-65) * 4 = bpow radix2 (-63))
  by (change 4 with (bpow radix2 2); rewrite <- bpow_plus; reflexivity).
pose proof (bpow_gt_0 radix2 (-65)) as K65.
apply Rle_trans with (bpow radix2 (-65) * 4); [apply Rmult_le_compat_l; lra | lra].
Qed.

(** ** The theorems *)

(** Where [fast_sinh_pos] returns [(h, l, e, err)], [h + l] is [sinh t
    2^-e] within [err = 2^-p], and [h] is the rounding of [h + l] to
    nearest. *)
Theorem fast_sinh_pos_correct :
  forall fma t h l e err,
  is_finite t = true -> 0 <= B2R t ->
  DyadicExp.fast_sinh_pos fma t = Some (h, l, e, err) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= e <= 1022)%Z /\
  exists p, (55 <= p <= 105)%Z /\ B2R err = bpow radix2 (- p) /\
    Rabs (sinh (B2R t) * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (- p).
Proof.
intros fma t h l e err Ft Ht H.
unfold DyadicExp.fast_sinh_pos in H.
assert (Fti : is_finite DyadicExp.tiny_near = true) by (vm_compute; reflexivity).
assert (Fq : is_finite (from_bits 0x3fd0000000000000) = true) by (vm_compute; reflexivity).
assert (F26 : is_finite (from_bits 0x403a000000000000) = true) by (vm_compute; reflexivity).
destruct (lt t DyadicExp.tiny_near) eqn:L1; [discriminate H|].
pose proof (lt_false _ _ Ft Fti L1) as T1. rewrite lit_tiny in T1.
destruct (lt t (from_bits 0x3fd0000000000000)) eqn:L2.
- pose proof (lt_true _ _ Ft Fq L2) as T2. rewrite lit_quarter in T2.
  change (bpow radix2 (-2)) with (/ 4) in T2.
  destruct (DyadicExp.fast_sinh_poly fma t) as [sh sl] eqn:Hp. cbv beta iota in H.
  destruct (Fast.normalize sh sl) as [[h1 l1] k] eqn:Hn. cbv beta iota in H.
  injection H as <- <- <- <-.
  destruct (sinh_small_core fma t sh sl h1 l1 k Ft (conj T1 T2) Hp Hn) as (F1 & F2 & R & Hk & B).
  refine (conj F1 (conj F2 (conj R (conj Hk _)))).
  exists 63%Z. split; [lia|]. split; [exact lit_err63 | exact B].
- pose proof (lt_false _ _ Ft Fq L2) as T2. rewrite lit_quarter in T2.
  change (bpow radix2 (-2)) with (/ 4) in T2.
  destruct (DyadicExp.fast_exp fma t zero) as [[[h0 l0] e0]|] eqn:Hfe; [|discriminate H].
  cbv beta iota in H.
  destruct (ge t (from_bits 0x403a000000000000)) eqn:Hge.
  + pose proof (ge_true _ _ Ft F26 Hge) as T3. rewrite lit_26 in T3.
    injection H as <- <- <- <-.
    destruct (sinh_large_core fma t h0 l0 e0 Ft T3 Hfe) as (F1 & F2 & R & Hk & B).
    refine (conj F1 (conj F2 (conj R (conj Hk _)))).
    exists 68%Z. split; [lia|]. split; [exact lit_err68 | exact B].
  + pose proof (ge_false _ _ Ft F26 Hge) as T3. rewrite lit_26 in T3.
    destruct (Fast.dd_div fma (DyadicExp.two_pow (-2 * e0)) zero h0 l0) as [wh wl] eqn:Hdd.
    cbv beta iota in H.
    destruct (Fast.two_sum h0 (opp wh)) as [s s0] eqn:Hs1. cbv beta iota in H.
    destruct (Fast.two_sum s (sub (add s0 l0) wl)) as [h1 l1] eqn:Hs2. cbv beta iota in H.
    injection H as <- <- <- <-.
    destruct (sinh_mid_core fma t h0 l0 e0 wh wl s s0 h1 l1 Ft (conj T2 T3) Hfe Hdd Hs1 Hs2)
      as (F1 & F2 & R & Hk & B).
    refine (conj F1 (conj F2 (conj R (conj Hk _)))).
    exists 67%Z. split; [lia|]. split; [exact lit_err67 | exact B].
Qed.

(** [fast_sinh_pos] returns the same with and without an FMA. *)
Theorem fast_sinh_pos_fma :
  forall t,
  is_finite t = true -> 0 <= B2R t ->
  DyadicExp.fast_sinh_pos true t = DyadicExp.fast_sinh_pos false t.
Proof.
intros t Ft Ht.
unfold DyadicExp.fast_sinh_pos.
assert (Fti : is_finite DyadicExp.tiny_near = true) by (vm_compute; reflexivity).
assert (Fq : is_finite (from_bits 0x3fd0000000000000) = true) by (vm_compute; reflexivity).
assert (F26 : is_finite (from_bits 0x403a000000000000) = true) by (vm_compute; reflexivity).
destruct (lt t DyadicExp.tiny_near) eqn:L1; [reflexivity|].
pose proof (lt_false _ _ Ft Fti L1) as T1. rewrite lit_tiny in T1.
destruct (lt t (from_bits 0x3fd0000000000000)) eqn:L2.
- pose proof (lt_true _ _ Ft Fq L2) as T2. rewrite lit_quarter in T2.
  change (bpow radix2 (-2)) with (/ 4) in T2.
  rewrite (sinh_poly_fma t Ft (conj T1 T2)). reflexivity.
- pose proof (lt_false _ _ Ft Fq L2) as T2. rewrite lit_quarter in T2.
  change (bpow radix2 (-2)) with (/ 4) in T2.
  rewrite fast_exp_fma.
  destruct (DyadicExp.fast_exp false t zero) as [[[h0 l0] e0]|] eqn:Hfe; [|reflexivity].
  cbv beta iota.
  destruct (ge t (from_bits 0x403a000000000000)) eqn:Hge; [reflexivity|].
  pose proof (ge_false _ _ Ft F26 Hge) as T3. rewrite lit_26 in T3.
  destruct (fe_facts false t h0 l0 e0 Ft Ht Hfe) as (Fh0 & Fl0 & _ & Hh0 & He0 & Hl0 & Herr).
  pose proof (fe_mid t h0 l0 e0 T3 Hh0 Hl0 Herr) as He1.
  assert (He : (-1 <= e0 <= 39)%Z) by lia.
  destruct (tp_facts e0 He) as (Fn & _ & Bn).
  destruct (dd_hyps h0 l0 e0 Hh0 Hl0 He) as (N1 & D1 & D2).
  rewrite (dd_div_fma (DyadicExp.two_pow (-2 * e0)) zero h0 l0 Fn eq_refl Fh0 Fl0 Bn N1 D1 D2).
  reflexivity.
Qed.
