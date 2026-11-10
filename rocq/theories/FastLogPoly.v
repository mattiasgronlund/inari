(** * The polynomial of the fast path of the logarithms

    [DyadicLog.log1p_poly] of [Model.v] evaluates the Taylor polynomial
    of degree 8 of ln(1 + z) at [z1], with [z1 - z1^2/2] in
    double-double and the terms of degree 3 to 8 by Horner's scheme in
    [f64] ([FastLogHorner.v]), and adds [z2 (1 - z1)], the term of
    ln(1 + z1 + z2) of first order in [z2] ([FastLogTaylor.v]).
    [log1p_poly_correct] bounds the error of the evaluation for [|z1| <=
    2^-9], [z1 = 0] or [|z1| >= 2^-200], and [|z2| <= 2^-53 |z1|],
    relative to [|z1|^3].
    [log1p_poly_fma] shows that an FMA gives the same result.

    [z1^2] is exact as [sh + sl] (TwoProduct, [TwoProduct.v]), [-sh/2]
    is exact, and [z1 - sh/2] is exact as [ah + al] (Fast2Sum [Dekker]).

    [Dekker] T. J. Dekker, A floating-point technique for extending the
    available precision, Numer. Math. 18 (1971). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct FastExpErr FastLogTaylor
  FastLogHorner.
From Inari Require SqrtSlow MulRuTiny CancelLanes FastRound.

Open Scope R_scope.

(** ** Helpers *)

(** [B2R l] of an [f64] literal [l], as [m * 2^e] (as in [FastExp.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** Powers of 2 as numerals, for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp] in *.

Local Lemma one_F : is_finite DyadicExp.one = true /\ B2R DyadicExp.one = 1.
Proof.
split; [vm_compute; reflexivity|]. lit_B2R. cbn [bpow radix_val radix2]. lra.
Qed.

Local Lemma half_F : is_finite DyadicLog.half = true /\ B2R DyadicLog.half = / 2.
Proof.
split; [vm_compute; reflexivity|]. lit_B2R. cbn [bpow radix_val radix2]. lra.
Qed.

Local Lemma neg_half_F : is_finite DyadicLog.neg_half = true /\ B2R DyadicLog.neg_half = - / 2.
Proof.
split; [vm_compute; reflexivity|]. lit_B2R. cbn [bpow radix_val radix2]. lra.
Qed.

(** A finite [f64] of value 0 is a zero. *)
Local Lemma zero_of_B2R : forall x : f64, is_finite x = true -> B2R x = 0 -> exists s, x = B754_zero s.
Proof.
intros [s|s| |s m e Hb] F H; try discriminate F.
- exists s. reflexivity.
- exfalso. cbn [B2R] in H. apply eq_0_F2R in H. destruct s; simpl in H; discriminate H.
Qed.

(** [add_k], [sub_k] and [mul_k] of [FastExpErr.v] for a named result
    [z], with the error as two inequalities for [lra] (as in
    [FastExpPoly.v]). *)
Local Lemma add_kz :
  forall x y z K, z = add x y -> is_finite x = true -> is_finite y = true ->
  Rabs (B2R x + B2R y) <= K -> K <= 16 ->
  is_finite z = true /\
  - (bpow radix2 (-53) * K + bpow radix2 (-1075)) <= B2R z - (B2R x + B2R y) <=
    bpow radix2 (-53) * K + bpow radix2 (-1075).
Proof.
intros x y z K -> Fx Fy H HK.
destruct (add_k x y K Fx Fy H HK) as (F & _ & B).
split; [exact F | apply Rabs_le_inv; exact B].
Qed.

Local Lemma sub_kz :
  forall x y z K, z = sub x y -> is_finite x = true -> is_finite y = true ->
  Rabs (B2R x - B2R y) <= K -> K <= 16 ->
  is_finite z = true /\
  - (bpow radix2 (-53) * K + bpow radix2 (-1075)) <= B2R z - (B2R x - B2R y) <=
    bpow radix2 (-53) * K + bpow radix2 (-1075).
Proof.
intros x y z K -> Fx Fy H HK.
destruct (sub_k x y K Fx Fy H HK) as (F & _ & B).
split; [exact F | apply Rabs_le_inv; exact B].
Qed.

Local Lemma mul_kz :
  forall x y z K, z = mul x y -> is_finite x = true -> is_finite y = true ->
  Rabs (B2R x * B2R y) <= K -> K <= 16 ->
  is_finite z = true /\
  - (bpow radix2 (-53) * K + bpow radix2 (-1075)) <= B2R z - B2R x * B2R y <=
    bpow radix2 (-53) * K + bpow radix2 (-1075).
Proof.
intros x y z K -> Fx Fy H HK.
destruct (mul_k x y K Fx Fy H HK) as (F & _ & B).
split; [exact F | apply Rabs_le_inv; exact B].
Qed.

(** [-s/2] is exact for [2^-1021 <= |s| <= 1]. *)
Local Lemma neg_half_kz :
  forall s n, n = mul DyadicLog.neg_half s -> is_finite s = true ->
  bpow radix2 (-1021) <= Rabs (B2R s) -> Rabs (B2R s) <= 1 ->
  is_finite n = true /\ B2R n = - (B2R s / 2).
Proof.
intros s n -> Fs Hlo Hhi.
destruct neg_half_F as (Fh & Eh).
assert (Hm : Rabs (B2R DyadicLog.neg_half * B2R s) <= MAX).
{ rewrite Eh, Rabs_mult, Rabs_Ropp, Rabs_pos_eq by lra. cbn [bpow radix_val radix2]. lra. }
destruct (mul_below_max _ _ Fh Fs Hm) as (F & E & _).
split; [exact F|]. rewrite E, Eh.
replace (- / 2 * B2R s) with (- (B2R s * bpow radix2 (-1)))
  by (change (bpow radix2 (-1)) with (/ 2); ring).
rewrite (round_generic radix2 fexp64 ZnearestE);
  [change (bpow radix2 (-1)) with (/ 2); field|].
apply generic_format_opp, SqrtSlow.format_scale; [apply generic_format_B2R | |].
- eapply Rle_trans; [| exact Hlo]. apply bpow_le. lia.
- rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0. num. lra.
Qed.

(** [|log1p_tail z| <= 0.33383] for [|z| <= 2^-9]. *)
Local Lemma tail_step :
  forall c z t C B, Rabs c <= C -> Rabs z <= / 512 -> Rabs t <= B ->
  Rabs (c + z * t) <= C + / 512 * B.
Proof.
intros c z t C B Hc Hz Ht.
eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_mult.
assert (Rabs z * Rabs t <= / 512 * B)
  by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hz | exact Ht]).
lra.
Qed.

Local Lemma tail_bound :
  forall z, Rabs z <= bpow radix2 (-9) -> Rabs (log1p_tail z) <= 33383 / 100000.
Proof.
intros z Hz.
assert (Hz' : Rabs z <= / 512) by (num; lra).
unfold log1p_tail.
eapply Rle_trans.
{ apply (tail_step _ _ _ (/ 3)); [rewrite Rabs_pos_eq; lra | exact Hz'|].
  apply (tail_step _ _ _ (/ 4)); [apply Rabs_le; lra | exact Hz'|].
  apply (tail_step _ _ _ (/ 5)); [rewrite Rabs_pos_eq; lra | exact Hz'|].
  apply (tail_step _ _ _ (/ 6)); [apply Rabs_le; lra | exact Hz'|].
  apply (tail_step _ _ _ (/ 7)); [rewrite Rabs_pos_eq; lra | exact Hz'|].
  apply Rle_refl. }
rewrite Rabs_Ropp, Rabs_pos_eq by lra. lra.
Qed.

(** The Taylor polynomial of degree 8 at [z] is [z - z^2/2 + z^3
    log1p_tail z], and its error is at most [0.0557 2^-53 |z|^3] for
    [|z| <= 2^-9]: [|z|^9 / (9 (1 - |z|)) <= 2^-54 |z|^3 / (9 * 511/512)]. *)
Local Lemma taylor8 :
  forall z, Rabs z <= bpow radix2 (-9) ->
  Rabs (ln (1 + z) - (z - z ^ 2 / 2 + z ^ 3 * log1p_tail z)) <=
    557 / 10000 * bpow radix2 (-53) * Rabs z ^ 3.
Proof.
intros z Hz.
assert (Hz' : Rabs z <= / 512) by (num; lra).
pose proof (log1p_taylor 8 z ltac:(lra)) as T.
replace (log1p_sum 8 z) with (z - z ^ 2 / 2 + z ^ 3 * log1p_tail z) in T
  by (cbn [log1p_sum INR pow]; unfold log1p_tail; field).
eapply Rle_trans; [exact T|].
replace (INR (S 8)) with 9 by (cbn [INR]; ring).
pose proof (Rabs_pos z) as H0.
assert (H3 : 0 <= Rabs z ^ 3) by (apply pow_le; lra).
assert (H6 : Rabs z ^ 6 <= (/ 512) ^ 6) by (apply pow_incr; lra).
assert (H9 : Rabs z ^ S 8 <= (/ 512) ^ 6 * Rabs z ^ 3).
{ replace (Rabs z ^ S 8) with (Rabs z ^ 6 * Rabs z ^ 3) by ring.
  apply Rmult_le_compat_r; assumption. }
assert (Hi : / (9 * (1 - Rabs z)) <= / (9 * (511 / 512)))
  by (apply Rinv_le_contravar; lra).
unfold Rdiv. eapply Rle_trans.
{ apply Rmult_le_compat_l; [apply pow_le; lra | exact Hi]. }
eapply Rle_trans.
{ apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | exact H9]. }
cbn [pow] in *. num. lra.
Qed.

(** [z1^2] is exact as [sh + sl] for [2^-200 <= |z1| <= 2^-9]: the
    exponent of [sh] is in [[-401, -18]], and that of [z1] below [-8]. *)
Local Lemma sq_exact :
  forall fma z1, is_finite z1 = true -> Rabs (B2R z1) <= bpow radix2 (-9) ->
  bpow radix2 (-200) <= Rabs (B2R z1) ->
  Generic.two_prod_is_exact fma z1 z1 (mul z1 z1) = true.
Proof.
intros fma z1 Fz1 HZ HZlo.
assert (Ez2 : B2R z1 * B2R z1 = Rabs (B2R z1) * Rabs (B2R z1))
  by (rewrite <- Rabs_mult, Rabs_pos_eq; [ring | nra]).
assert (L2 : bpow radix2 (-200) * bpow radix2 (-200) <= Rabs (B2R z1) * Rabs (B2R z1))
  by (apply Rmult_le_compat; [apply bpow_ge_0 | apply bpow_ge_0 | exact HZlo | exact HZlo]).
assert (U2 : Rabs (B2R z1) * Rabs (B2R z1) <= bpow radix2 (-9) * bpow radix2 (-9))
  by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact HZ | exact HZ]).
assert (Hm : Rabs (B2R z1 * B2R z1) <= 16).
{ rewrite Ez2, Rabs_pos_eq by (apply Rmult_le_pos; apply Rabs_pos). num. lra. }
destruct (mul_e z1 z1 Fz1 Fz1 Hm) as (Fp & _ & Bp).
rewrite Ez2, (Rabs_pos_eq (Rabs (B2R z1) * Rabs (B2R z1))) in Bp
  by (apply Rmult_le_pos; apply Rabs_pos).
apply Rabs_le_inv in Bp.
assert (Elo : (-401 <= Generic.exponent (mul z1 z1))%Z).
{ apply MulRuTiny.exponent_ge; [exact Fp|].
  eapply Rle_trans; [| apply Rle_abs]. num. lra. }
assert (Ehi : (Generic.exponent (mul z1 z1) < -17)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fp | lia |].
  apply Rabs_lt. num. lra. }
assert (Ez : (Generic.exponent z1 < -8)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fz1 | lia |].
  eapply Rle_lt_trans; [exact HZ | apply bpow_lt; lia]. }
unfold Generic.two_prod_is_exact. cbv zeta.
destruct fma; repeat (apply andb_true_intro; split); apply Z.leb_le; lia.
Qed.

(** ** The evaluation *)

(** For [|z1| <= 2^-9] and [|z2| <= 2^-53 |z1|], [log1p_poly] returns
    [ah] and [pl] with [ah + pl] within [5/2 2^-53 |z1|^3 + 2 |z2| |z1|^2
    + 2^-103 |z1|] of ln(1 + z1 + z2). [z1] is 0 or at least [2^-200],
    so that no product of the evaluation is subnormal. *)
Theorem log1p_poly_correct :
  forall fma z1 z2,
  is_finite z1 = true -> is_finite z2 = true ->
  Rabs (B2R z1) <= bpow radix2 (-9) ->
  (B2R z1 = 0 \/ bpow radix2 (-200) <= Rabs (B2R z1)) ->
  Rabs (B2R z2) <= bpow radix2 (-53) * Rabs (B2R z1) ->
  let '(ah, pl) := DyadicLog.log1p_poly fma z1 z2 in
  is_finite ah = true /\ is_finite pl = true /\
  Rabs (B2R z1) * (1 - bpow radix2 (-9)) <= Rabs (B2R ah) <=
    Rabs (B2R z1) * (1 + bpow radix2 (-9)) /\
  Rabs (B2R pl) <= Rabs (B2R z1) ^ 3 / 2 + bpow radix2 (-51) * Rabs (B2R z1) /\
  Rabs (ln (1 + (B2R z1 + B2R z2)) - (B2R ah + B2R pl)) <=
    5 / 2 * bpow radix2 (-53) * Rabs (B2R z1) ^ 3 + 2 * Rabs (B2R z2) * Rabs (B2R z1) ^ 2
    + bpow radix2 (-103) * Rabs (B2R z1).
Proof.
intros fma z1 z2 Fz1 Fz2 HZ Hz0 Hw.
destruct Hz0 as [Z0 | HZlo].
{ (* [z1 = 0]: then [z2 = 0], and the result is a pair of zeros. *)
  assert (W0 : B2R z2 = 0).
  { rewrite Z0, Rabs_R0, Rmult_0_r in Hw. pose proof (Rabs_pos (B2R z2)).
    apply Rabs_le_inv in Hw. lra. }
  destruct (zero_of_B2R z1 Fz1 Z0) as [s1 ->].
  destruct (zero_of_B2R z2 Fz2 W0) as [s2 ->].
  remember (DyadicLog.log1p_poly fma (B754_zero s1) (B754_zero s2)) as p eqn:Ep.
  destruct fma, s1, s2; vm_compute in Ep; subst p; cbv beta iota; cbn [B2R].
  all: split; [reflexivity|]; split; [reflexivity|].
  all: replace (1 + (0 + 0)) with 1 by ring; rewrite ln_1, Rabs_R0.
  all: replace (0 ^ 3) with 0 by ring; replace (0 ^ 2) with 0 by ring.
  all: num; split; [lra|]; split; [lra|]; apply Rabs_le; lra. }
unfold DyadicLog.log1p_poly, Fast.fast_two_sum. cbv beta iota zeta.
change (mul (mul z1 (mul z1 z1)) ?r) with (log1p_horner z1).
set (sh := mul z1 z1).
set (sl := Generic.two_prod_err fma z1 z1 sh).
set (nh := mul DyadicLog.neg_half sh).
set (ah := add z1 nh).
set (al := add nh (sub z1 ah)).
set (q := log1p_horner z1).
set (hs := mul DyadicLog.half sl).
set (d := sub q hs).
set (o := sub DyadicExp.one z1).
set (m := mul z2 o).
set (g := add d m).
set (pl := add al g).
destruct one_F as (F1 & E1).
destruct half_F as (Fh & Eh).
(* Powers of [|z1|]. *)
pose proof (Rabs_pos (B2R z1)) as Z0.
pose proof (Rabs_pos (B2R z2)) as W0.
pose proof (Rabs_le_inv (B2R z1) _ (Rle_refl _)) as Hz.
assert (Ez2 : B2R z1 * B2R z1 = Rabs (B2R z1) ^ 2) by (rewrite pow2_abs; ring).
assert (Z2 : Rabs (B2R z1) ^ 2 <= bpow radix2 (-9) * Rabs (B2R z1)).
{ replace (Rabs (B2R z1) ^ 2) with (Rabs (B2R z1) * Rabs (B2R z1)) by ring.
  apply Rmult_le_compat_r; assumption. }
assert (Z3 : Rabs (B2R z1) ^ 3 <= bpow radix2 (-9) * Rabs (B2R z1) ^ 2).
{ replace (Rabs (B2R z1) ^ 3) with (Rabs (B2R z1) * Rabs (B2R z1) ^ 2) by ring.
  apply Rmult_le_compat_r; [apply pow_le|]; assumption. }
assert (Z2p : 0 <= Rabs (B2R z1) ^ 2) by (apply pow_le; exact Z0).
assert (Z3p : 0 <= Rabs (B2R z1) ^ 3) by (apply pow_le; exact Z0).
assert (WZp : 0 <= Rabs (B2R z2) * Rabs (B2R z1) ^ 2) by (apply Rmult_le_pos; assumption).
(* [sh = z1^2] rounded, and [sl = z1^2 - sh] exactly. *)
assert (Hsq : Rabs (B2R z1 * B2R z1) <= Rabs (B2R z1) ^ 2) by (rewrite Ez2, Rabs_pos_eq; lra).
destruct (mul_kz z1 z1 sh _ eq_refl Fz1 Fz1 Hsq ltac:(num; lra)) as (Fsh & Bsh).
destruct (two_prod_err_correct fma z1 z1 Fz1 Fz1 (sq_exact fma z1 Fz1 HZ HZlo))
  as (_ & _ & _ & Fsl & Esl).
change (Generic.two_prod_err fma z1 z1 (mul z1 z1)) with sl in Fsl, Esl.
change (mul z1 z1) with sh in Esl.
(* [nh = -sh/2] exactly. *)
assert (L2 : bpow radix2 (-200) * bpow radix2 (-200) <= Rabs (B2R z1) ^ 2).
{ replace (Rabs (B2R z1) ^ 2) with (Rabs (B2R z1) * Rabs (B2R z1)) by ring.
  apply Rmult_le_compat; [apply bpow_ge_0 | apply bpow_ge_0 | exact HZlo | exact HZlo]. }
assert (Hsh : bpow radix2 (-1021) <= Rabs (B2R sh) <= 1).
{ split; [eapply Rle_trans; [| apply Rle_abs] | apply Rabs_le]; num; lra. }
destruct (neg_half_kz sh nh eq_refl Fsh (proj1 Hsh) (proj2 Hsh)) as (Fnh & Enh).
(* [ah = z1 + nh] rounded, and [al = z1 + nh - ah] exactly (Fast2Sum
   [Dekker], as [|nh| <= |z1|]). *)
assert (HA : Rabs (B2R z1 + B2R nh) <= Rabs (B2R z1) + Rabs (B2R z1) ^ 2)
  by (apply Rabs_le; num; lra).
destruct (add_k z1 nh _ Fz1 Fnh HA ltac:(num; lra)) as (Fah & Eah & Bah).
fold ah in Fah, Eah, Bah. apply Rabs_le_inv in Bah.
assert (Hle : Rabs (B2R nh) <= Rabs (B2R z1)) by (apply Rabs_le; num; lra).
destruct (CancelLanes.fast_two_sum z1 nh ah Fz1 Fnh Hle Fah Eah) as (Fal & Eal).
fold al in Fal, Eal.
(* [q = z1^3 log1p_tail z1] within [1.421 2^-53 |z1|^3 + 2^-1073]. *)
destruct (log1p_horner_correct z1 Fz1 HZ) as (Fq & Bq).
fold q in Fq, Bq. apply Rabs_le_inv in Bq.
assert (HP : Rabs (B2R z1 ^ 3 * log1p_tail (B2R z1)) <= Rabs (B2R z1) ^ 3 * (33383 / 100000))
  by (apply Rabs_mul_le; [rewrite RPow_abs; apply Rle_refl | apply tail_bound; exact HZ]).
apply Rabs_le_inv in HP.
(* [hs = sl/2] rounded. *)
assert (Hhs : Rabs (B2R DyadicLog.half * B2R sl) <=
              bpow radix2 (-53) * Rabs (B2R z1) ^ 2 + bpow radix2 (-1075))
  by (rewrite Eh; apply Rabs_le; num; lra).
destruct (mul_kz _ _ hs _ eq_refl Fh Fsl Hhs ltac:(num; lra)) as (Fhs & Bhs).
rewrite Eh in Bhs.
(* [d = q - hs] rounded. *)
assert (Hd : Rabs (B2R q - B2R hs) <=
             33384 / 100000 * Rabs (B2R z1) ^ 3 + bpow radix2 (-53) * Rabs (B2R z1) ^ 2
             + bpow radix2 (-1072))
  by (apply Rabs_le; num; lra).
destruct (sub_kz q hs d _ eq_refl Fq Fhs Hd ltac:(num; lra)) as (Fd & Bd).
(* [o = 1 - z1] rounded, [m = z2 o] rounded. *)
assert (Ho : Rabs (B2R DyadicExp.one - B2R z1) <= 1 + Rabs (B2R z1))
  by (rewrite E1; apply Rabs_le; lra).
destruct (sub_kz _ z1 o _ eq_refl F1 Fz1 Ho ltac:(num; lra)) as (Fo & Bo).
rewrite E1 in Bo.
assert (Hm : Rabs (B2R z2 * B2R o) <= Rabs (B2R z2) * (1 + / 256))
  by (apply Rabs_mul_le; [apply Rle_refl | apply Rabs_le; num; lra]).
destruct (mul_kz z2 o m _ eq_refl Fz2 Fo Hm ltac:(num; lra)) as (Fm & Bm).
apply Rabs_le_inv in Hm.
assert (He5 : Rabs (B2R z2 * (B2R o - (1 - B2R z1))) <=
              Rabs (B2R z2) * (bpow radix2 (-53) * (1 + / 512) + bpow radix2 (-1075)))
  by (apply Rabs_mul_le; [apply Rle_refl | apply Rabs_le; num; lra]).
apply Rabs_le_inv in He5.
(* [g = d + m] rounded. *)
assert (Hg : Rabs (B2R d + B2R m) <=
             3339 / 10000 * Rabs (B2R z1) ^ 3 + 101 / 100 * Rabs (B2R z2)
             + 2 * bpow radix2 (-53) * Rabs (B2R z1) ^ 2 + bpow radix2 (-1070))
  by (apply Rabs_le; num; lra).
destruct (add_kz d m g _ eq_refl Fd Fm Hg ltac:(num; lra)) as (Fg & Bg).
(* [pl = al + g] rounded. *)
assert (Hp : Rabs (B2R al + B2R g) <=
             334 / 1000 * Rabs (B2R z1) ^ 3 + 102 / 100 * Rabs (B2R z2)
             + bpow radix2 (-53) * Rabs (B2R z1) + 3 * bpow radix2 (-53) * Rabs (B2R z1) ^ 2
             + bpow radix2 (-1068))
  by (apply Rabs_le; num; lra).
destruct (add_kz al g pl _ eq_refl Fal Fg Hp ltac:(num; lra)) as (Fpl & Bpl).
split; [exact Fah|]. split; [exact Fpl|].
split.
{ (* [|ah - z1| <= 2^-9 |z1|]. *)
  assert (D : Rabs (B2R ah - B2R z1) <= bpow radix2 (-9) * Rabs (B2R z1))
    by (apply Rabs_le; num; lra).
  pose proof (Rabs_triang_inv (B2R z1) (B2R ah)) as T1.
  pose proof (Rabs_triang_inv (B2R ah) (B2R z1)) as T2.
  rewrite Rabs_minus_sym in T1. split; lra. }
split; [apply Rabs_le; num; lra|].
(* The sum: the Taylor error of degree 8 (0.0557u |z1|^3, [u = 2^-53]),
   Horner's (1.421u), the roundings of [d], [g] and [pl] (0.33384u,
   0.3339u and 0.334u, plus terms in [|z2|] and [u^2 |z1|]), the first
   order in [z2] (log1p_shift) and the roundings of [o] and [m]. *)
pose proof (log1p_shift (B2R z1) (B2R z2) HZ Hw) as TS.
pose proof (taylor8 (B2R z1) HZ) as TT.
apply Rabs_le_inv in TS, TT.
clear - TS TT Bq HP Esl Enh Bah Eal Bsh Bhs Bd Bo Bm Hm He5 Bg Bpl Eh
  Hw HZ HZlo Z0 W0 Z2 Z3 Z2p Z3p WZp Ez2 L2.
apply Rabs_le. num. lra.
Qed.

(** An FMA gives the same [sl], and so the same result: [z1^2] is exact
    either way, and for [z1 = 0] both give [+0]. *)
Theorem log1p_poly_fma :
  forall z1 z2,
  is_finite z1 = true -> Rabs (B2R z1) <= bpow radix2 (-9) ->
  (B2R z1 = 0 \/ bpow radix2 (-200) <= Rabs (B2R z1)) ->
  DyadicLog.log1p_poly true z1 z2 = DyadicLog.log1p_poly false z1 z2.
Proof.
intros z1 z2 Fz1 HZ Hz0.
assert (E : Generic.two_prod_err true z1 z1 (mul z1 z1) =
            Generic.two_prod_err false z1 z1 (mul z1 z1)).
{ destruct Hz0 as [Z0 | HZlo].
  - destruct (zero_of_B2R z1 Fz1 Z0) as [s ->]. destruct s; vm_compute; reflexivity.
  - apply FastRound.two_prod_err_fma_eq; [exact Fz1 | exact Fz1 | |];
      apply sq_exact; assumption. }
unfold DyadicLog.log1p_poly. cbv zeta. rewrite E. reflexivity.
Qed.
