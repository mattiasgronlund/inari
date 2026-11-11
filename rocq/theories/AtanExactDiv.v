(** * The quotients of [atan2]'s rules that are [f64]s, decided in [f64]

    [exact_div fma y x] of [DyadicAtan] in [Model.v] returns an [f64]
    only if it is [y / x] exactly, for finite [y] and [|y| < x < 2^996]
    ([exact_div_correct]). [q] is [y / x] rounded to nearest, and the
    function checks that [q x = y] through [q s x = y s], with [s = 2^128]
    for [|y| < 2^-968] and [s = 1] otherwise: scaling by [s] is exact, as
    [|q| <= 1] and, where [s = 2^128], [|y| < 2^-968], the product [p] of
    [q s] by [x] rounded to nearest is [y s], whose magnitude is then at
    least 2^-968 for [y <> 0], and the error of that product,
    which [Generic.two_prod_err] computes exactly there
    ([TwoProduct.two_prod_err_correct]), is 0. With and without an FMA
    the function returns the same ([exact_div_fma]), from
    [FastRound.two_prod_err_fma_eq]. [ge_mul_false] and [ge_false] give the
    real bounds that the checks of [tiny_quotient] and [midpoint_quotient]
    leave before they call it. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Mult_error.
From Inari Require Import Model Encoding TwoSum TwoProduct FastRound.

Open Scope R_scope.

(** ** The constants *)

Lemma two_25_R : B2R DyadicAtan.two_25 = bpow radix2 25.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicAtan.two_25) with (SpecFloat.S754_finite false 4503599627370496 (-27))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

Lemma two_1021_R : B2R DyadicAtan.two_1021 = bpow radix2 1021.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicAtan.two_1021) with (SpecFloat.S754_finite false 4503599627370496 969)
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

Lemma two_m968_R : B2R DyadicAtan.two_m968 = bpow radix2 (-968).
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicAtan.two_m968) with (SpecFloat.S754_finite false 4503599627370496 (-1020))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

Lemma two_128_R : B2R DyadicAtan.two_128 = bpow radix2 128.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicAtan.two_128) with (SpecFloat.S754_finite false 4503599627370496 76)
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

Lemma two_996_R : B2R DyadicAtan.two_996 = bpow radix2 996.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicAtan.two_996) with (SpecFloat.S754_finite false 4503599627370496 944)
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

Lemma two_m1021_R : B2R DyadicAtan.two_m1021 = bpow radix2 (-1021).
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicAtan.two_m1021) with (SpecFloat.S754_finite false 4503599627370496 (-1073))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

(** [1.0], the factor [s] of [exact_div] for [|y| >= 2^-968]. *)
Local Lemma one_R : B2R DyadicExp.one = bpow radix2 0.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicExp.one) with (SpecFloat.S754_finite false 4503599627370496 (-52))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

(** ** The checks before [exact_div] *)

(** [|y| c], rounded to nearest, is below [x] only if [|y| c] is. *)
Lemma ge_mul_false :
  forall y x c,
  is_finite y = true -> is_finite x = true -> is_finite c = true -> 0 < B2R c ->
  ge (mul (fabs y) c) x = false ->
  Rabs (B2R y) * B2R c < B2R x.
Proof.
intros y x c Fy Fx Fc Hc G.
unfold ge in G.
assert (Fa : is_finite (fabs y) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fy).
assert (Ra : B2R (fabs y) = Rabs (B2R y)) by (unfold fabs; apply B2R_Babs).
generalize (Bmult_correct 53 1024 _ _ mode_NE (fabs y) c).
change (Bmult mode_NE (fabs y) c) with (mul (fabs y) c).
change (SpecFloat.fexp 53 1024) with fexp64. cbn [round_mode].
rewrite Ra.
destruct (Rlt_bool _ _).
- intros (Hm & Fm & _). rewrite Fa, Fc in Fm. cbn [andb] in Fm.
  rewrite Bleb_correct in G by assumption.
  revert G. destruct (Rle_bool_spec (B2R x) (B2R (mul (fabs y) c))) as [H|H];
    intros G; [discriminate G|].
  (* [x] is a float, so [x <= |y| c] would give [x <= RN(|y| c)]. *)
  apply Rnot_le_lt. intros L.
  apply (Rlt_not_le _ _ H). rewrite Hm.
  rewrite <- (round_generic radix2 fexp64 ZnearestE (B2R x)) by apply generic_format_B2R.
  apply round_le; try typeclasses eauto. exact L.
- (* An overflow gives [+inf], as [|y| c >= 0], and [x <= +inf]. *)
  intros Ho. exfalso.
  change (Bsign (fabs y)) with (Bsign (Babs y)) in Ho. rewrite Bsign_Babs in Ho.
  rewrite (StepUp.Bsign_B2R c Fc) in Ho by lra.
  rewrite Rlt_bool_false in Ho by lra. cbn [xorb] in Ho.
  assert (Hi : mul (fabs y) c = B754_infinity false).
  { apply B2SF_inj. rewrite Ho. reflexivity. }
  rewrite Hi in G.
  destruct x as [sx|sx| |sx mx ex Hx]; try discriminate Fx; discriminate G.
Qed.

Lemma ge_false :
  forall x c,
  is_finite x = true -> is_finite c = true ->
  ge x c = false ->
  B2R x < B2R c.
Proof.
intros x c Fx Fc G.
unfold ge in G. rewrite Bleb_correct in G by assumption.
revert G. destruct (Rle_bool_spec (B2R c) (B2R x)) as [H|H]; intros G;
  [discriminate G | exact H].
Qed.

(** ** [exact_div] *)

(** [a == b] with [b] finite: [a] is finite and has [b]'s value. *)
Local Lemma eq_finite :
  forall a b : f64, is_finite b = true -> eq a b = true ->
  is_finite a = true /\ B2R a = B2R b.
Proof.
intros a b Fb E.
assert (Fa : is_finite a = true).
{ destruct a as [sa|sa| |sa ma ea Ha]; try reflexivity.
  - destruct b as [sb|sb| |sb mb eb Hb]; try discriminate Fb; destruct sa; discriminate E.
  - discriminate E. }
split; [exact Fa|].
unfold eq in E. rewrite Beqb_correct in E by assumption.
revert E. destruct (Req_bool_spec (B2R a) (B2R b)) as [H|H]; intros E;
  [exact H | discriminate E].
Qed.

(** A float times [2^k], [k >= 0], is exact if it does not overflow. *)
Local Lemma mul_bpow_exact :
  forall a s k, is_finite a = true -> is_finite s = true ->
  B2R s = bpow radix2 k -> (0 <= k)%Z ->
  Rabs (B2R a) * bpow radix2 k < bpow radix2 1024 ->
  is_finite (mul a s) = true /\ B2R (mul a s) = B2R a * bpow radix2 k.
Proof.
intros a s k Fa Fs Hs Hk Hb.
assert (G : generic_format radix2 fexp64 (B2R a * bpow radix2 k)).
{ apply mult_bpow_pos_exact_FLT; [apply generic_format_B2R | exact Hk]. }
pose proof (Bmult_correct 53 1024 _ _ mode_NE a s) as Hm.
change (SpecFloat.fexp 53 1024) with fexp64 in Hm.
cbn [round_mode] in Hm. rewrite Hs, (round_generic _ _ _ _ G) in Hm.
rewrite Rlt_bool_true in Hm.
2: { rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 k)) by apply bpow_ge_0. exact Hb. }
destruct Hm as (HR & HF & _). rewrite Fa, Fs in HF.
split; [exact HF | exact HR].
Qed.

(** [q = y / x] rounded to nearest is finite and at most 1 in magnitude,
    for [|y| < x]. *)
Local Lemma div_facts :
  forall y x, is_finite y = true -> is_finite x = true -> Rabs (B2R y) < B2R x ->
  is_finite (div y x) = true /\ B2R (div y x) = RN (B2R y / B2R x) /\
  Rabs (B2R (div y x)) <= 1.
Proof.
intros y x Fy Fx H.
assert (Hx : B2R x <> 0) by (pose proof (Rabs_pos (B2R y)); intros X0; lra).
assert (Q : Rabs (B2R y / B2R x) < 1).
{ unfold Rdiv.
  rewrite Rabs_mult, (Rabs_pos_eq (/ B2R x))
    by (apply Rlt_le, Rinv_0_lt_compat; pose proof (Rabs_pos (B2R y)); lra).
  apply Rmult_lt_reg_r with (B2R x); [pose proof (Rabs_pos (B2R y)); lra|].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l by exact Hx. exact H. }
assert (F1 : generic_format radix2 fexp64 1).
{ apply (generic_format_bpow radix2 fexp64 0). unfold FLT_exp. lia. }
assert (A : Rabs (RN (B2R y / B2R x)) <= 1).
{ apply abs_round_le_generic; try typeclasses eauto; [exact F1 | lra]. }
pose proof (Bdiv_correct 53 1024 _ _ mode_NE y x Hx) as Hd.
change (SpecFloat.fexp 53 1024) with fexp64 in Hd.
cbn [round_mode] in Hd.
rewrite Rlt_bool_true in Hd.
2: { apply Rle_lt_trans with (1 := A). apply (bpow_lt radix2 0 1024). lia. }
destruct Hd as (HR & HF & _). rewrite Fy in HF.
change (Bdiv mode_NE y x) with (div y x) in HR, HF.
split; [exact HF|]. split; [exact HR|]. rewrite HR. exact A.
Qed.

(** [exponent(a) < k] for finite [a] with [|a| < 2^k] and [k > -1022]. *)
Local Lemma exponent_lt :
  forall a k, is_finite a = true -> (-1021 <= k)%Z ->
  Rabs (B2R a) < bpow radix2 k -> (Generic.exponent a < k)%Z.
Proof.
intros a k Fa Hk H.
destruct (Z_lt_le_dec (Generic.exponent a) (-1022)) as [L|L]; [lia|].
pose proof (bpow_exponent_le_abs_B2R a Fa L) as B.
apply (lt_bpow radix2). lra.
Qed.

(** [k <= exponent(a)] for finite [a] with [2^k <= |a|]. *)
Local Lemma exponent_ge :
  forall a k, is_finite a = true ->
  bpow radix2 k <= Rabs (B2R a) -> (k <= Generic.exponent a)%Z.
Proof.
intros a k Fa H.
pose proof (abs_B2R_lt_exponent a Fa) as B.
assert (k < Generic.exponent a + 1)%Z by (apply (lt_bpow radix2); lra).
lia.
Qed.

(** What [exact_div] computes, for [y <> 0]: [s = 2^k], [q s] and [y s]
    are exact, and where [q s x] rounded to nearest is [y s],
    [Generic.two_prod_is_exact] holds for both values of [fma], as
    [2^-968 <= |y s| < 2^996], [|q s| <= 2^128] and [x < 2^996]. *)
Local Lemma exact_div_parts :
  forall y x s, is_finite y = true -> is_finite x = true -> B2R y <> 0 ->
  Rabs (B2R y) < B2R x < bpow radix2 996 ->
  s = (if lt (fabs y) DyadicAtan.two_m968 then DyadicAtan.two_128 else DyadicExp.one) ->
  exists k : Z,
  is_finite (mul (div y x) s) = true /\
  B2R (mul (div y x) s) = B2R (div y x) * bpow radix2 k /\
  is_finite (mul y s) = true /\ B2R (mul y s) = B2R y * bpow radix2 k /\
  (eq (mul (mul (div y x) s) x) (mul y s) = true ->
   forall fma,
   Generic.two_prod_is_exact fma (mul (div y x) s) x (mul (mul (div y x) s) x) = true).
Proof.
intros y x s Fy Fx Y H Hs.
destruct (div_facts y x Fy Fx (proj1 H)) as (Fq & _ & Aq).
assert (Ymin : bpow radix2 (-1074) <= Rabs (B2R y)).
{ apply generic_format_ge_bpow with (fexp := fexp64).
  - intros e'. unfold FLT_exp. lia.
  - apply Rabs_pos_lt, Y.
  - apply generic_format_abs, generic_format_B2R. }
assert (Lt : lt (fabs y) DyadicAtan.two_m968 = Rlt_bool (Rabs (B2R y)) (bpow radix2 (-968))).
{ unfold lt, fabs. rewrite Bltb_correct.
  - rewrite B2R_Babs, two_m968_R. reflexivity.
  - rewrite is_finite_Babs. exact Fy.
  - vm_compute. reflexivity. }
(* Both cases give [s = 2^k] with [0 <= k <= 128] and
   [2^-968 <= |y| 2^k < 2^996]. *)
assert (C : exists k, is_finite s = true /\ B2R s = bpow radix2 k /\ (0 <= k <= 128)%Z /\
  bpow radix2 (-968) <= Rabs (B2R y) * bpow radix2 k < bpow radix2 996).
{ rewrite Hs, Lt.
  destruct (Rlt_bool_spec (Rabs (B2R y)) (bpow radix2 (-968))) as [L|L].
  - exists 128%Z. split; [vm_compute; reflexivity|]. split; [exact two_128_R|].
    split; [lia|]. split.
    + (* [|y| >= 2^-1074], so [|y| 2^128 >= 2^-946]. *)
      apply Rle_trans with (bpow radix2 (-1074) * bpow radix2 128).
      * rewrite <- bpow_plus. apply bpow_le. lia.
      * apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Ymin].
    + apply Rlt_le_trans with (bpow radix2 (-968) * bpow radix2 128).
      * apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact L].
      * rewrite <- bpow_plus. apply bpow_le. lia.
  - exists 0%Z. split; [vm_compute; reflexivity|]. split; [exact one_R|].
    split; [lia|]. change (bpow radix2 0) with 1. rewrite Rmult_1_r.
    split; [exact L | lra]. }
destruct C as (k & Fs & Rs & Hk & Hys).
exists k.
assert (Hq : Rabs (B2R (div y x)) * bpow radix2 k <= bpow radix2 128).
{ rewrite <- (Rmult_1_l (bpow radix2 128)).
  apply Rmult_le_compat; [apply Rabs_pos | apply bpow_ge_0 | exact Aq | apply bpow_le; lia]. }
destruct (mul_bpow_exact (div y x) s k Fq Fs Rs (proj1 Hk)) as (Fqs & Rqs).
{ apply Rle_lt_trans with (1 := Hq). apply bpow_lt. lia. }
destruct (mul_bpow_exact y s k Fy Fs Rs (proj1 Hk)) as (Fys & Rys).
{ apply Rlt_trans with (1 := proj2 Hys). apply bpow_lt. lia. }
split; [exact Fqs|]. split; [exact Rqs|]. split; [exact Fys|]. split; [exact Rys|].
intros P fma.
destruct (eq_finite _ _ Fys P) as (Fp & Rp).
assert (Ap : bpow radix2 (-968) <= Rabs (B2R (mul (mul (div y x) s) x)) < bpow radix2 996).
{ rewrite Rp, Rys, Rabs_mult, (Rabs_pos_eq (bpow radix2 k)) by apply bpow_ge_0.
  exact Hys. }
assert (E1 : (-968 <= Generic.exponent (mul (mul (div y x) s) x))%Z).
{ apply exponent_ge; [exact Fp | exact (proj1 Ap)]. }
assert (E2 : (Generic.exponent (mul (mul (div y x) s) x) < 996)%Z).
{ apply exponent_lt; [exact Fp | lia | exact (proj2 Ap)]. }
assert (E3 : (Generic.exponent (mul (div y x) s) < 129)%Z).
{ apply exponent_lt; [exact Fqs | lia |].
  rewrite Rqs, Rabs_mult, (Rabs_pos_eq (bpow radix2 k)) by apply bpow_ge_0.
  apply Rle_lt_trans with (1 := Hq). apply bpow_lt. lia. }
assert (E4 : (Generic.exponent x < 996)%Z).
{ apply exponent_lt; [exact Fx | lia |].
  rewrite Rabs_pos_eq by (pose proof (Rabs_pos (B2R y)); lra). exact (proj2 H). }
unfold Generic.two_prod_is_exact. cbv zeta.
destruct fma; rewrite ?Bool.andb_true_iff, ?Z.leb_le; lia.
Qed.

Lemma exact_div_correct :
  forall fma y x q,
  is_finite y = true -> is_finite x = true ->
  Rabs (B2R y) < B2R x < bpow radix2 996 ->
  DyadicAtan.exact_div fma y x = Some q ->
  is_finite q = true /\ B2R q = B2R y / B2R x.
Proof.
intros fma y x q Fy Fx H E.
unfold DyadicAtan.exact_div in E. cbv zeta in E.
set (s := if lt (fabs y) DyadicAtan.two_m968 then DyadicAtan.two_128 else DyadicExp.one) in E.
destruct (eq (mul (mul (div y x) s) x) (mul y s)) eqn:P; cbn [andb] in E; [|discriminate E].
destruct (eq (Generic.two_prod_err fma (mul (div y x) s) x (mul (mul (div y x) s) x)) zero)
  eqn:Ze; [|discriminate E].
injection E as <-.
destruct (div_facts y x Fy Fx (proj1 H)) as (Fq & Rq & _).
split; [exact Fq|].
destruct (Req_dec (B2R y) 0) as [Y|Y].
{ (* [y = 0]: [q] is a zero. *)
  rewrite Rq, Y. unfold Rdiv. rewrite Rmult_0_l. apply round_0; try typeclasses eauto. }
destruct (exact_div_parts y x s Fy Fx Y H eq_refl) as (k & Fqs & Rqs & Fys & Rys & Ex).
destruct (two_prod_err_correct fma _ _ Fqs Fx (Ex P fma)) as (_ & _ & _ & _ & Re).
destruct (eq_finite _ _ Fys P) as (_ & Rp).
destruct (eq_finite _ zero eq_refl Ze) as (_ & R0).
change (B2R zero) with 0 in R0.
(* The error [q s x - p] is 0 and [p = y s], so [q s x = y s]. *)
assert (A : B2R (mul (div y x) s) * B2R x = B2R (mul y s)) by lra.
rewrite Rqs, Rys in A.
assert (Hx0 : B2R x <> 0) by (pose proof (Rabs_pos (B2R y)); intros X0; lra).
assert (B : B2R (div y x) * B2R x = B2R y).
{ apply Rmult_eq_reg_r with (bpow radix2 k); [|apply Rgt_not_eq, bpow_gt_0].
  rewrite <- A. ring. }
rewrite <- B. field. exact Hx0.
Qed.

Theorem exact_div_fma :
  forall y x,
  is_finite y = true -> is_finite x = true -> B2R y <> 0 ->
  Rabs (B2R y) < B2R x < bpow radix2 996 ->
  DyadicAtan.exact_div true y x = DyadicAtan.exact_div false y x.
Proof.
intros y x Fy Fx Y H.
unfold DyadicAtan.exact_div. cbv zeta.
set (s := if lt (fabs y) DyadicAtan.two_m968 then DyadicAtan.two_128 else DyadicExp.one).
destruct (eq (mul (mul (div y x) s) x) (mul y s)) eqn:P; [|reflexivity].
destruct (exact_div_parts y x s Fy Fx Y H eq_refl) as (k & Fqs & _ & _ & _ & Ex).
(* Where [p = y s], both exactness tests hold, and the two errors are the
   same [f64]. *)
rewrite (two_prod_err_fma_eq _ _ Fqs Fx (Ex P true) (Ex P false)).
reflexivity.
Qed.
