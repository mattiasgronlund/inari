(** * The rule of the fast paths of [sin] and [cos] for results near ±1

    sin x is never ±1 at a finite [f64] [x] ([sin_not_one]), and cos t is
    never ±1 at a finite nonzero [t] ([cos_not_one]): either would make [x]
    or [t] an odd or a nonzero even multiple of π/2, which [km_distance] of
    [KahanMcDonald.v] keeps at least 2^-61 away. Where
    [DyadicTrig.fast_one_dir h up] of [Model.v] returns [v], [h = ±1], and
    for a [y] with [|y| < 1] that [h + l] is within a relative 2^-71 of,
    with [h = RN(h + l)], [y] lies strictly between [±(1 - 2^-53)] and
    [±1], so [v] is [y] rounded toward +inf if [up] and toward -inf
    otherwise ([fast_one_dir_correct]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Encoding TwoSum DyDriver KahanMcDonald DyExpRules.

Open Scope R_scope.

(** ** sin and cos are never ±1 *)

(** [|sin x| = 1] gives [cos x = 0] by [sin2_cos2], so [x = k π + π/2 =
    (2k + 1) π/2] by [cos_eq_0_0], which [km_distance] rules out. *)
Theorem sin_not_one : forall x : f64, is_finite x = true -> Rabs (sin (B2R x)) <> 1.
Proof.
intros x Fx H.
assert (Hc : cos (B2R x) = 0).
{ pose proof (sin2_cos2 (B2R x)) as S.
  rewrite (Rsqr_abs (sin (B2R x))), H, Rsqr_1 in S.
  apply Rsqr_0_uniq. lra. }
destruct (cos_eq_0_0 _ Hc) as [k Hk].
assert (Hk0 : (2 * k + 1 <> 0)%Z) by lia.
pose proof (km_distance x (2 * k + 1) Fx Hk0) as D.
assert (E : B2R x - IZR (2 * k + 1) * (PI / 2) = 0)
  by (rewrite Hk, plus_IZR, mult_IZR; field).
rewrite E, Rabs_R0 in D.
pose proof (bpow_gt_0 radix2 (-61)). lra.
Qed.

(** [|cos t| = 1] gives [sin t = 0], so [t = k π = 2k π/2] by
    [sin_eq_0_0], with [k <> 0] as [t <> 0], which [km_distance] rules
    out. *)
Theorem cos_not_one :
  forall t : f64, is_finite t = true -> B2R t <> 0 -> Rabs (cos (B2R t)) <> 1.
Proof.
intros t Ft Ht0 H.
assert (Hs : sin (B2R t) = 0).
{ pose proof (sin2_cos2 (B2R t)) as S.
  rewrite (Rsqr_abs (cos (B2R t))), H, Rsqr_1 in S.
  apply Rsqr_0_uniq. lra. }
destruct (sin_eq_0_0 _ Hs) as [k Hk].
destruct (Z.eq_dec k 0) as [Hk0 | Hk0].
- apply Ht0. rewrite Hk, Hk0. ring.
- assert (H2k : (2 * k <> 0)%Z) by lia.
  pose proof (km_distance t (2 * k) Ft H2k) as D.
  assert (E : B2R t - IZR (2 * k) * (PI / 2) = 0) by (rewrite Hk, mult_IZR; field).
  rewrite E, Rabs_R0 in D.
  pose proof (bpow_gt_0 radix2 (-61)). lra.
Qed.

(** ** The rounding of a [y] next to ±1 *)

(** [B2R] of a literal, by its [B2SF], as in [FastTrig.v]. *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** The [f64] below 1 is [1 - 2^-53], and 1 is the one after it; the
    [f64] after -1 is [-(1 - 2^-53)]. *)
Local Lemma pred_one_64 : pred radix2 fexp64 1 = 1 - bpow radix2 (-53).
Proof. change 1 with (bpow radix2 0) at 1. rewrite pred_bpow. reflexivity. Qed.

Local Lemma format_one : generic_format radix2 fexp64 1.
Proof. change 1 with (bpow radix2 0). apply generic_format_bpow. unfold FLT_exp. lia. Qed.

Local Lemma succ_below_one : succ radix2 fexp64 (1 - bpow radix2 (-53)) = 1.
Proof.
rewrite <- pred_one_64. apply succ_pred; [typeclasses eauto | exact format_one].
Qed.

Local Lemma succ_m_one : succ radix2 fexp64 (Ropp 1) = - (1 - bpow radix2 (-53)).
Proof. rewrite succ_opp, pred_one_64. reflexivity. Qed.

(** Below [1 - 2^-54], the midpoint of [1 - 2^-53] and 1, [RN] is at most
    [1 - 2^-53], so [RN z = 1] puts [z] at or above that midpoint. *)
Local Lemma rn_one_ge : forall z, RN z = 1 -> 1 - bpow radix2 (-54) <= z.
Proof.
intros z H.
destruct (Rlt_or_le z (1 - bpow radix2 (-54))) as [Hz | Hz]; [| exact Hz].
assert (L : RN z <= pred radix2 fexp64 1).
{ apply round_N_le_midp;
    [typeclasses eauto | apply generic_format_pred; [typeclasses eauto | exact format_one] |].
  rewrite succ_pred by first [exact format_one | typeclasses eauto]. rewrite pred_one_64.
  assert (B : bpow radix2 (-53) = / 9007199254740992 /\
              bpow radix2 (-54) = / 18014398509481984) by (split; reflexivity).
  destruct B as (B1 & B2). rewrite B1. rewrite B2 in Hz. lra. }
rewrite pred_one_64, H in L.
pose proof (bpow_gt_0 radix2 (-53)). lra.
Qed.

(** [fast_one_dir] returns only at [h = ±1]. With [|y - (h + l)| <= 2^-71
    |y| < 2^-71] and [h + l] on the side of the midpoint [±(1 - 2^-54)]
    that rounds to [h] ([rn_one_ge], and [round_NE_opp] for [h = -1]), [y]
    lies strictly between the [f64]s [±(1 - 2^-53)] and [±1], as [|y| < 1],
    and [v] is the one of the two on the side [up] ([rnd_bracket]). *)
Theorem fast_one_dir_correct :
  forall (h l : f64) up v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (-71) * Rabs y -> Rabs y < 1 ->
  DyadicTrig.fast_one_dir h up = Some v -> rounds up y v.
Proof.
intros h l up v y Fh Fl Hrn Hy Hy1 H.
unfold DyadicTrig.fast_one_dir in H.
destruct (eq (fabs h) Fast.one) eqn:E; [| discriminate H].
cbn [negb] in H.
(* The literals, and [|h| = 1]. *)
assert (L1 : B2R Fast.one = 1).
{ lit_B2R. change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
  reflexivity. }
assert (E1 : B2R DyadicExp.one = 1).
{ lit_B2R. change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
  reflexivity. }
assert (Em : B2R DyadicExp.one_minus_ulp = 1 - bpow radix2 (-53)).
{ lit_B2R. assert (B : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
  rewrite B. lra. }
assert (Ha : Rabs (B2R h) = 1).
{ unfold eq in E.
  rewrite Beqb_correct in E
    by (unfold fabs; rewrite ?is_finite_Babs; first [exact Fh | vm_compute; reflexivity]).
  unfold fabs in E. rewrite B2R_Babs in E.
  destruct (Req_bool_spec (Rabs (B2R h)) (B2R Fast.one)) as [Q | Q]; [| discriminate E].
  rewrite Q. exact L1. }
assert (Hlt : lt h zero = Rlt_bool (B2R h) 0)
  by (unfold lt; apply Bltb_correct; [exact Fh | reflexivity]).
assert (M1 : eq DyadicExp.m_one zero = false) by (vm_compute; reflexivity).
assert (M2 : gt DyadicExp.m_one zero = false) by (vm_compute; reflexivity).
unfold DyadicExp.near_one in H. rewrite M1, M2, Hlt in H. cbv beta iota zeta in H.
(* [|y - (h + l)| < 2^-71], and the constants. *)
assert (Hy' : Rabs (y - (B2R h + B2R l)) < bpow radix2 (-71)).
{ apply Rle_lt_trans with (1 := Hy). rewrite <- (Rmult_1_r (bpow radix2 (-71))) at 2.
  apply Rmult_lt_compat_l; [apply bpow_gt_0 | exact Hy1]. }
apply Rabs_lt_inv in Hy'. apply Rabs_lt_inv in Hy1.
assert (HM : bpow radix2 (-54) + bpow radix2 (-71) < bpow radix2 (-53)).
{ assert (B : bpow radix2 (-53) = / 9007199254740992 /\
              bpow radix2 (-54) = / 18014398509481984 /\
              bpow radix2 (-71) = / 2361183241434822606848) by (repeat split; reflexivity).
  destruct B as (B1 & B2 & B3). rewrite B1, B2, B3. lra. }
assert (Fo : is_finite DyadicExp.one = true) by (vm_compute; reflexivity).
assert (Fm : is_finite DyadicExp.one_minus_ulp = true) by (vm_compute; reflexivity).
unfold rounds.
assert (Hpm : B2R h = 1 \/ B2R h = -1).
{ revert Ha. unfold Rabs. destruct (Rcase_abs (B2R h)); intros; lra. }
destruct Hpm as [P | P].
- (* [h = 1]: [y] is in [(1 - 2^-53, 1)]. *)
  rewrite P, (Rlt_bool_false 1 0) in H by lra. cbv iota in H.
  rewrite P in Hrn, Hy'.
  pose proof (rn_one_ge _ (eq_sym Hrn)) as G.
  assert (S : B2R DyadicExp.one =
              succ radix2 (SpecFloat.fexp 53 1024) (B2R DyadicExp.one_minus_ulp))
    by (rewrite E1, Em; symmetry; exact succ_below_one).
  assert (Y : B2R DyadicExp.one_minus_ulp < y < B2R DyadicExp.one) by (rewrite E1, Em; lra).
  destruct up; cbn [xorb] in H; injection H as <-.
  + exact (rnd_bracket _ _ true y Fm Fo S Y).
  + exact (rnd_bracket _ _ false y Fm Fo S Y).
- (* [h = -1]: [-y] is in [(1 - 2^-53, 1)]. *)
  rewrite P, (Rlt_bool_true (-1) 0) in H by lra. cbv iota in H.
  rewrite P in Hrn, Hy'.
  assert (Hrn' : RN (- (-1 + B2R l)) = 1) by (rewrite round_NE_opp, <- Hrn; ring).
  pose proof (rn_one_ge _ Hrn') as G.
  assert (Fo' : is_finite (opp DyadicExp.one) = true) by (vm_compute; reflexivity).
  assert (Fm' : is_finite (opp DyadicExp.one_minus_ulp) = true) by (vm_compute; reflexivity).
  assert (S : B2R (opp DyadicExp.one_minus_ulp) =
              succ radix2 (SpecFloat.fexp 53 1024) (B2R (opp DyadicExp.one))).
  { unfold opp. rewrite !B2R_Bopp, E1, Em. symmetry. exact succ_m_one. }
  assert (Y : B2R (opp DyadicExp.one) < y < B2R (opp DyadicExp.one_minus_ulp)).
  { unfold opp. rewrite !B2R_Bopp, E1, Em. lra. }
  destruct up; cbn [xorb] in H; injection H as <-.
  + exact (rnd_bracket _ _ true y Fo' Fm' S Y).
  + exact (rnd_bracket _ _ false y Fo' Fm' S Y).
Qed.
