(** * The polynomial of the logarithm of x^y

    [DyadicLog.log1p_poly_acc] of [Model.v] evaluates the Taylor
    polynomial of degree 9 of ln(1 + z) at [z1], with [z1 - z1^2/2 +
    z1^3/3] in double-double and the terms of degree 4 to 9 by Horner's
    scheme in [f64] ([FastPowHorner.v]), added last, and adds [z2 (1 -
    z1 + z1^2)], the term of ln(1 + z1 + z2) of first order in [z2]
    ([FastPowTaylor.v]). [log1p_poly_acc_correct] bounds the error of the
    evaluation for [|z1| <= 2^-9], [z1 = 0] or [|z1| >= 2^-200], and
    [|z2| <= 2^-53 |z1|], relative to [|z1|^4], [|z2| |z1|^3] and
    [|z1|]. [log1p_poly_acc_fma] shows that an FMA gives the same
    result.

    [z1^2] is exact as [sh + sl] and [z1 sh] as [ch] plus its error
    (TwoProduct, [TwoProduct.v]), so that [ch + cl] is [z1^3] up to the
    rounding of [z1 sl]; [ch Q3] is exact as [dh] plus its error, so
    that [dh + dl] is [z1^3 / 3] up to the roundings of [cl Q3], [ch
    Q3L] and their sum, with [Q3 + Q3L] within [2^-109] of 1/3; [-sh/2]
    is exact; and [z1 - sh/2] and [ah + dh] are exact as [ah + al] and
    [bh + bl] (Fast2Sum [Dekker]).

    [Dekker] T. J. Dekker, A floating-point technique for extending the
    available precision, Numer. Math. 18 (1971). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct FastExpErr FastLogTaylor
  FastPowTaylor FastPowHorner FastPowCube.
From Inari Require SqrtSlow CancelLanes.

Open Scope R_scope.

(** ** Helpers (as in [FastLogPoly.v]) *)

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
    [z], with the error as two inequalities for [lra]. *)
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

(** [|log1p_tail4 z| <= 0.2505] for [|z| <= 2^-9]. *)
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

Local Lemma tail4_bound :
  forall z, Rabs z <= bpow radix2 (-9) -> Rabs (log1p_tail4 z) <= 2505 / 10000.
Proof.
intros z Hz.
assert (Hz' : Rabs z <= / 512) by (num; lra).
unfold log1p_tail4.
eapply Rle_trans.
{ apply (tail_step _ _ _ (/ 4)); [apply Rabs_le; lra | exact Hz'|].
  apply (tail_step _ _ _ (/ 5)); [rewrite Rabs_pos_eq; lra | exact Hz'|].
  apply (tail_step _ _ _ (/ 6)); [apply Rabs_le; lra | exact Hz'|].
  apply (tail_step _ _ _ (/ 7)); [rewrite Rabs_pos_eq; lra | exact Hz'|].
  apply (tail_step _ _ _ (/ 8)); [apply Rabs_le; lra | exact Hz'|].
  apply Rle_refl. }
rewrite Rabs_pos_eq by lra. lra.
Qed.

(** The Taylor polynomial of degree 9 at [z] is [z - z^2/2 + z^3/3 +
    z^4 log1p_tail4 z], and its error is at most [0.0501 2^-53 |z|^4]
    for [|z| <= 2^-9]: [|z|^10 / (10 (1 - |z|)) <= 2^-54 |z|^4 / (10 *
    511/512)]. *)
Local Lemma taylor9 :
  forall z, Rabs z <= bpow radix2 (-9) ->
  Rabs (ln (1 + z) - (z - z ^ 2 / 2 + z ^ 3 / 3 + z ^ 4 * log1p_tail4 z)) <=
    501 / 10000 * bpow radix2 (-53) * Rabs z ^ 4.
Proof.
intros z Hz.
assert (Hz' : Rabs z <= / 512) by (num; lra).
pose proof (log1p_taylor 9 z ltac:(lra)) as T.
replace (log1p_sum 9 z) with (z - z ^ 2 / 2 + z ^ 3 / 3 + z ^ 4 * log1p_tail4 z) in T
  by (cbn [log1p_sum INR pow]; unfold log1p_tail4; field).
eapply Rle_trans; [exact T|].
replace (INR (S 9)) with 10 by (cbn [INR]; ring).
pose proof (Rabs_pos z) as H0.
assert (H6 : Rabs z ^ 6 <= (/ 512) ^ 6) by (apply pow_incr; lra).
assert (H10 : Rabs z ^ S 9 <= (/ 512) ^ 6 * Rabs z ^ 4).
{ replace (Rabs z ^ S 9) with (Rabs z ^ 6 * Rabs z ^ 4) by ring.
  apply Rmult_le_compat_r; [apply pow_le; lra | assumption]. }
assert (Hi : / (10 * (1 - Rabs z)) <= / (10 * (511 / 512)))
  by (apply Rinv_le_contravar; lra).
unfold Rdiv. eapply Rle_trans.
{ apply Rmult_le_compat_l; [apply pow_le; lra | exact Hi]. }
eapply Rle_trans.
{ apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | exact H10]. }
assert (H4 : 0 <= Rabs z ^ 4) by (apply pow_le; lra).
cbn [pow] in *. num. lra.
Qed.

(** ** The evaluation *)

(** For [|z1| <= 2^-9], [z1 = 0] or [|z1| >= 2^-200], and [|z2| <=
    2^-53 |z1|], [bh + pl] is within [7/4 2^-53 |z1|^4 + 512/511 |z2|
    |z1|^3 + 2^-100 |z1|] of ln(1 + z1 + z2). [z1] is 0 or at least
    [2^-200], so that no product of the evaluation is subnormal. *)
Theorem log1p_poly_acc_correct :
  forall fma z1 z2,
  is_finite z1 = true -> is_finite z2 = true ->
  Rabs (B2R z1) <= bpow radix2 (-9) ->
  (B2R z1 = 0 \/ bpow radix2 (-200) <= Rabs (B2R z1)) ->
  Rabs (B2R z2) <= bpow radix2 (-53) * Rabs (B2R z1) ->
  let '(bh, pl) := DyadicLog.log1p_poly_acc fma z1 z2 in
  is_finite bh = true /\ is_finite pl = true /\
  Rabs (B2R z1) * (1 - bpow radix2 (-9)) <= Rabs (B2R bh) <=
    Rabs (B2R z1) * (1 + bpow radix2 (-9)) /\
  Rabs (B2R pl) <= Rabs (B2R z1) ^ 4 / 2 + bpow radix2 (-51) * Rabs (B2R z1) /\
  Rabs (ln (1 + (B2R z1 + B2R z2)) - (B2R bh + B2R pl)) <=
    7 / 4 * bpow radix2 (-53) * Rabs (B2R z1) ^ 4 + 512 / 511 * Rabs (B2R z2) * Rabs (B2R z1) ^ 3
    + bpow radix2 (-100) * Rabs (B2R z1).
Proof.
intros fma z1 z2 Fz1 Fz2 HZ Hz0 Hw.
destruct Hz0 as [Z0 | HZlo].
{ (* [z1 = 0]: then [z2 = 0], and the result is a pair of zeros. *)
  assert (W0 : B2R z2 = 0).
  { rewrite Z0, Rabs_R0, Rmult_0_r in Hw. pose proof (Rabs_pos (B2R z2)).
    apply Rabs_le_inv in Hw. lra. }
  destruct (zero_of_B2R z1 Fz1 Z0) as [s1 ->].
  destruct (zero_of_B2R z2 Fz2 W0) as [s2 ->].
  remember (DyadicLog.log1p_poly_acc fma (B754_zero s1) (B754_zero s2)) as p eqn:Ep.
  destruct fma, s1, s2; vm_compute in Ep; subst p; cbv beta iota; cbn [B2R].
  all: split; [reflexivity|]; split; [reflexivity|].
  all: replace (1 + (0 + 0)) with 1 by ring; rewrite ln_1, Rabs_R0.
  all: replace (0 ^ 4) with 0 by ring; replace (0 ^ 3) with 0 by ring.
  all: num; split; [lra|]; split; [lra|]; apply Rabs_le; lra. }
pose proof (log1p_cube_correct fma z1 Fz1 (conj HZlo HZ)) as C.
cbv zeta in C.
unfold DyadicLog.log1p_poly_acc, Fast.fast_two_sum. cbv beta iota zeta.
change (mul (mul (mul z1 (mul z1 z1)) z1) ?r) with (log1p_horner4 z1).
set (sh := mul z1 z1) in *.
set (sl := Generic.two_prod_err fma z1 z1 sh) in *.
set (ch := mul z1 sh) in *.
set (cl := add (Generic.two_prod_err fma z1 sh ch) (mul z1 sl)) in *.
set (dh := mul ch (from_bits DyadicLog.Q3)) in *.
set (dl := add (Generic.two_prod_err fma ch (from_bits DyadicLog.Q3) dh)
             (add (mul cl (from_bits DyadicLog.Q3)) (mul ch (from_bits DyadicLog.Q3L)))) in *.
destruct C as (Fsh & Fsl & Fdh & Fdl & Esq & Bsl & Bdh & Bdl & Bc).
set (q := log1p_horner4 z1).
set (nh := mul DyadicLog.neg_half sh).
set (ah := add z1 nh).
set (al := add nh (sub z1 ah)).
set (bh := add ah dh).
set (bl := add dh (sub ah bh)).
set (hs := mul DyadicLog.half sl).
set (s1 := add al bl).
set (s2 := sub dl hs).
set (o := sub DyadicExp.one z1).
set (o2 := add o sh).
set (m := mul z2 o2).
set (s3 := add s2 m).
set (s4 := add s1 s3).
set (pl := add q s4).
destruct one_F as (F1 & E1).
destruct half_F as (Fh & Eh).
(* Powers of [Z = |z1|], and [W = |z2| <= 2^-53 Z]. Below, [u = 2^-53]
   and [T = 2^-1075]: as [Z >= 2^-200], every [T] is far below [2^-100 Z]. *)
pose proof (Rabs_pos (B2R z1)) as Z0.
pose proof (Rabs_pos (B2R z2)) as W0.
pose proof (Rabs_le_inv (B2R z1) _ (Rle_refl _)) as Hz.
assert (Ez2 : B2R z1 ^ 2 = Rabs (B2R z1) ^ 2) by (rewrite pow2_abs; reflexivity).
assert (Z2 : Rabs (B2R z1) ^ 2 <= bpow radix2 (-9) * Rabs (B2R z1)).
{ replace (Rabs (B2R z1) ^ 2) with (Rabs (B2R z1) * Rabs (B2R z1)) by ring.
  apply Rmult_le_compat_r; assumption. }
assert (Z3 : Rabs (B2R z1) ^ 3 <= bpow radix2 (-9) * Rabs (B2R z1) ^ 2).
{ replace (Rabs (B2R z1) ^ 3) with (Rabs (B2R z1) * Rabs (B2R z1) ^ 2) by ring.
  apply Rmult_le_compat_r; [apply pow_le|]; assumption. }
assert (Z2p : 0 <= Rabs (B2R z1) ^ 2) by (apply pow_le; exact Z0).
assert (Z3p : 0 <= Rabs (B2R z1) ^ 3) by (apply pow_le; exact Z0).
assert (Z4p : 0 <= Rabs (B2R z1) ^ 4) by (apply pow_le; exact Z0).
assert (Z4 : Rabs (B2R z1) ^ 4 <= bpow radix2 (-9) * Rabs (B2R z1) ^ 3).
{ replace (Rabs (B2R z1) ^ 4) with (Rabs (B2R z1) * Rabs (B2R z1) ^ 3) by ring.
  apply Rmult_le_compat_r; [apply pow_le|]; assumption. }
assert (L2 : bpow radix2 (-200) * bpow radix2 (-200) <= Rabs (B2R z1) ^ 2).
{ replace (Rabs (B2R z1) ^ 2) with (Rabs (B2R z1) * Rabs (B2R z1)) by ring.
  apply Rmult_le_compat; [apply bpow_ge_0 | apply bpow_ge_0 | exact HZlo | exact HZlo]. }
(* [sh + sl = z1^2] with [|sl| <= u z1^2] ([FastPowCube.v]). *)
pose proof Bdh as Bdh2. apply Rabs_le_inv in Bsl, Bdh2, Bdl.
(* [nh = -sh/2] exactly. *)
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
(* [bh = ah + dh] rounded, and [bl = ah + dh - bh] exactly (Fast2Sum
   [Dekker], as [|dh| <= |z1|^3/2 <= |ah|]). *)
assert (Dah : Rabs (B2R z1 - B2R ah) <= Rabs (B2R z1) / 2) by (apply Rabs_le; num; lra).
pose proof (Rabs_triang_inv (B2R z1) (B2R ah)) as Tah.
assert (Hle2 : Rabs (B2R dh) <= Rabs (B2R ah)) by (num; lra).
assert (HB : Rabs (B2R ah + B2R dh) <=
             Rabs (B2R z1) + 2 * Rabs (B2R z1) ^ 2 + 2 * bpow radix2 (-53) * Rabs (B2R z1)
             + 2 * bpow radix2 (-1075))
  by (apply Rabs_le; num; lra).
destruct (add_k ah dh _ Fah Fdh HB ltac:(num; lra)) as (Fbh & Ebh & Bbh).
fold bh in Fbh, Ebh, Bbh. apply Rabs_le_inv in Bbh.
destruct (CancelLanes.fast_two_sum ah dh bh Fah Fdh Hle2 Fbh Ebh) as (Fbl & Ebl).
fold bl in Fbl, Ebl.
(* [q = z1^4 log1p_tail4 z1] within [1.3 u Z^4 + 2^-1073]. *)
destruct (log1p_horner4_correct z1 Fz1 HZ) as (Fq & Bq).
fold q in Fq, Bq. apply Rabs_le_inv in Bq.
assert (HP : Rabs (B2R z1 ^ 4 * log1p_tail4 (B2R z1)) <= Rabs (B2R z1) ^ 4 * (2505 / 10000))
  by (apply Rabs_mul_le; [rewrite RPow_abs; apply Rle_refl | apply tail4_bound; exact HZ]).
apply Rabs_le_inv in HP.
(* [hs = sl/2] rounded. *)
assert (Hhs : Rabs (B2R DyadicLog.half * B2R sl) <= bpow radix2 (-53) * Rabs (B2R z1) ^ 2)
  by (rewrite Eh; apply Rabs_le; num; lra).
destruct (mul_kz _ _ hs _ eq_refl Fh Fsl Hhs ltac:(num; lra)) as (Fhs & Bhs).
rewrite Eh in Bhs.
(* [s1 = al + bl] rounded: both are roundings of sums of size about [Z]. *)
assert (Hs1 : Rabs (B2R al + B2R bl) <=
              2 * bpow radix2 (-53) * Rabs (B2R z1) + 3 * bpow radix2 (-53) * Rabs (B2R z1) ^ 2
              + 3 * bpow radix2 (-106) * Rabs (B2R z1) + 3 * bpow radix2 (-1075))
  by (apply Rabs_le; num; lra).
destruct (add_kz al bl s1 _ eq_refl Fal Fbl Hs1 ltac:(num; lra)) as (Fs1 & Bs1).
apply Rabs_le_inv in Hs1.
(* [s2 = dl - hs] rounded. *)
assert (Hs2 : Rabs (B2R dl - B2R hs) <=
              bpow radix2 (-51) * Rabs (B2R z1) ^ 3 + bpow radix2 (-53) * Rabs (B2R z1) ^ 2
              + bpow radix2 (-1075))
  by (apply Rabs_le; num; lra).
destruct (sub_kz dl hs s2 _ eq_refl Fdl Fhs Hs2 ltac:(num; lra)) as (Fs2 & Bs2).
apply Rabs_le_inv in Hs2.
(* [o = 1 - z1], [o2 = o + sh] and [m = z2 o2] rounded: [o2] is [1 - z1
   + z1^2] within [2.01 u]. *)
assert (Ho : Rabs (B2R DyadicExp.one - B2R z1) <= 1 + Rabs (B2R z1))
  by (rewrite E1; apply Rabs_le; lra).
destruct (sub_kz _ z1 o _ eq_refl F1 Fz1 Ho ltac:(num; lra)) as (Fo & Bo).
rewrite E1 in Bo.
assert (Ho2 : Rabs (B2R o + B2R sh) <= 1 + / 256) by (apply Rabs_le; num; lra).
destruct (add_kz o sh o2 _ eq_refl Fo Fsh Ho2 ltac:(num; lra)) as (Fo2 & Bo2).
assert (Hm : Rabs (B2R z2 * B2R o2) <= Rabs (B2R z2) * (1 + / 128))
  by (apply Rabs_mul_le; [apply Rle_refl | apply Rabs_le; num; lra]).
destruct (mul_kz z2 o2 m _ eq_refl Fz2 Fo2 Hm ltac:(num; lra)) as (Fm & Bm).
apply Rabs_le_inv in Hm.
assert (He : Rabs (B2R z2 * (B2R o2 - (1 - B2R z1 + B2R z1 ^ 2))) <=
             Rabs (B2R z2) * (201 / 100 * bpow radix2 (-53)))
  by (apply Rabs_mul_le; [apply Rle_refl | apply Rabs_le; num; lra]).
apply Rabs_le_inv in He.
(* [s3 = s2 + m], [s4 = s1 + s3] and [pl = q + s4] rounded. *)
assert (Hs3 : Rabs (B2R s2 + B2R m) <=
              bpow radix2 (-50) * Rabs (B2R z1) ^ 3 + 2 * bpow radix2 (-53) * Rabs (B2R z1) ^ 2
              + (1 + / 64) * bpow radix2 (-53) * Rabs (B2R z1) + 4 * bpow radix2 (-1075))
  by (apply Rabs_le; num; lra).
destruct (add_kz s2 m s3 _ eq_refl Fs2 Fm Hs3 ltac:(num; lra)) as (Fs3 & Bs3).
apply Rabs_le_inv in Hs3.
assert (Hs4 : Rabs (B2R s1 + B2R s3) <=
              bpow radix2 (-50) * Rabs (B2R z1) ^ 3 + 6 * bpow radix2 (-53) * Rabs (B2R z1) ^ 2
              + (3 + / 32) * bpow radix2 (-53) * Rabs (B2R z1) + 10 * bpow radix2 (-1075))
  by (apply Rabs_le; num; lra).
destruct (add_kz s1 s3 s4 _ eq_refl Fs1 Fs3 Hs4 ltac:(num; lra)) as (Fs4 & Bs4).
apply Rabs_le_inv in Hs4.
assert (Hpl : Rabs (B2R q + B2R s4) <=
              2506 / 10000 * Rabs (B2R z1) ^ 4 + bpow radix2 (-49) * Rabs (B2R z1) ^ 3
              + 7 * bpow radix2 (-53) * Rabs (B2R z1) ^ 2
              + (3 + / 16) * bpow radix2 (-53) * Rabs (B2R z1) + bpow radix2 (-1071))
  by (apply Rabs_le; num; lra).
destruct (add_kz q s4 pl _ eq_refl Fq Fs4 Hpl ltac:(num; lra)) as (Fpl & Bpl).
apply Rabs_le_inv in Hpl.
split; [exact Fbh|]. split; [exact Fpl|].
split.
{ (* [|bh - z1| <= 2^-9 |z1|]. *)
  assert (D : Rabs (B2R bh - B2R z1) <= bpow radix2 (-9) * Rabs (B2R z1))
    by (apply Rabs_le; num; lra).
  pose proof (Rabs_triang_inv (B2R z1) (B2R bh)) as T1.
  pose proof (Rabs_triang_inv (B2R bh) (B2R z1)) as T2.
  rewrite Rabs_minus_sym in T1. split; lra. }
split; [apply Rabs_le; num; lra|].
(* The sum: [bh + bl = ah + dh] and [ah + al = z1 - sh/2], so that [bh
   + pl] is [z1 - z1^2/2 + (dh + dl) + q + z2 (1 - z1 + z1^2)] up to the
   roundings of [pl] (0.2506 u Z^4 and 3.07 u^2 Z), [s4], [s3], [s1],
   [m], [o2] and [hs], about 12.2 u^2 Z in all. *)
assert (Hsum : Rabs (B2R bh + B2R pl -
                     (B2R z1 - B2R z1 ^ 2 / 2 + (B2R dh + B2R dl) + B2R q
                      + B2R z2 * (1 - B2R z1 + B2R z1 ^ 2))) <=
               2507 / 10000 * bpow radix2 (-53) * Rabs (B2R z1) ^ 4
               + bpow radix2 (-102) * Rabs (B2R z1)).
{ clear - Eal Ebl Enh Esq Bhs Bs1 Bs2 Bs3 Bs4 Bpl Bm He Hw HZlo Z0 W0 Z2 Z3 Z2p Z3p Z4p.
  apply Rabs_le. num. lra. }
(* Then the Taylor error of degree 9 (0.0501 u Z^4), Horner's (1.3 u
   Z^4), the sum's (0.2507 u Z^4): 1.6008 u Z^4 in all; the first order
   in [z2] ([log1p_shift2]) and the cube ([FastPowCube.v]). *)
pose proof (log1p_shift2 (B2R z1) (B2R z2) HZ Hw) as TS.
pose proof (taylor9 (B2R z1) HZ) as TT.
apply Rabs_le_inv in TS, TT, Hsum, Bc.
clear - TS TT Bq Bc Hsum Hw HZlo Z0 W0 Z2 Z3 Z2p Z3p Z4p.
apply Rabs_le. num. lra.
Qed.

(** An FMA gives the same [sl], [cl] and [dl], and so the same result:
    the three products are exact either way, and for [z1 = 0] both give
    zeros. *)
Theorem log1p_poly_acc_fma :
  forall z1 z2,
  is_finite z1 = true -> Rabs (B2R z1) <= bpow radix2 (-9) ->
  (B2R z1 = 0 \/ bpow radix2 (-200) <= Rabs (B2R z1)) ->
  DyadicLog.log1p_poly_acc true z1 z2 = DyadicLog.log1p_poly_acc false z1 z2.
Proof.
intros z1 z2 Fz1 HZ Hz0.
assert (E :
  Generic.two_prod_err true z1 z1 (mul z1 z1) = Generic.two_prod_err false z1 z1 (mul z1 z1) /\
  Generic.two_prod_err true z1 (mul z1 z1) (mul z1 (mul z1 z1)) =
    Generic.two_prod_err false z1 (mul z1 z1) (mul z1 (mul z1 z1)) /\
  Generic.two_prod_err true (mul z1 (mul z1 z1)) (from_bits DyadicLog.Q3)
    (mul (mul z1 (mul z1 z1)) (from_bits DyadicLog.Q3)) =
  Generic.two_prod_err false (mul z1 (mul z1 z1)) (from_bits DyadicLog.Q3)
    (mul (mul z1 (mul z1 z1)) (from_bits DyadicLog.Q3))).
{ destruct Hz0 as [Z0 | HZlo].
  - destruct (zero_of_B2R z1 Fz1 Z0) as [s ->]. destruct s; vm_compute; repeat split.
  - exact (log1p_cube_fma z1 Fz1 (conj HZlo HZ)). }
destruct E as (E1 & E2 & E3).
unfold DyadicLog.log1p_poly_acc. cbv zeta. rewrite E1, E2, E3. reflexivity.
Qed.
