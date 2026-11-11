(** * Rounding tests with an error bound for an exponent from -1085 to 1023

    [Fast.round_dir_wide_err] and [Fast.round_near_wide_err] of [Model.v]
    are [Fast.round_dir_wide] and [Fast.round_near_wide] for a fast path
    that bounds [|y - (h + l)|] by [err = 2^-p], [p] from 55 to 105, in
    place of [2^-68], as the fast path of [pow] does at [2^-67]. They send
    [y 2^e] with [e < -1022], or [e = -1022] and [h <= 1], to
    [Fast.round_dir_sub_err] and [Fast.round_near_sub_err], the tests of
    [FastRoundSub.v] with the bounds [2 err C] and [2^-53 C - 2 err C] in
    place of [2^-67 C] and [2^-53 C - 2^-67 C], for [C =
    Fast.sub_unit e = 2^(-1022 - e)] ([sub_err_consts]), and with the
    bound [2^-53 C + 2 err C] in place of [2^-53 C + 2^-67 C], beyond
    which the test to nearest takes the [f64] after or before [s]
    ([sub_err_far_consts]): [C + y] is within [2^-p + 2^-105 C <= 2 2^-p
    C] of [s + u] ([FastRoundSubCommon.sub_common_err]). The others go to
    the tests of [FastRoundErr.v], which are right from [e = -1022], where
    [h > 1], to [e = 1023] ([FastRoundWide.round_dir_err_normal_correct]
    and [FastRoundWide.round_near_err_normal_correct]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error.
From Inari Require Import Model Mpfr Encoding TwoSum TwoProduct DyDriver NearF64 NearCells
  FastRound FastRoundSubBits FastRoundSubCommon FastRoundWide.
From Inari Require StepUp DyExpRules.

Open Scope R_scope.

Local Notation G := (generic_format radix2 fexp64).

(** ** The bounds of the tests *)

(** A copy of [FastRoundSubBits.two_R], which is local there. *)
Local Lemma two_R : B2R Fast.two = 2.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF Fast.two) with (SpecFloat.S754_finite false 4503599627370496 (-51))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

(** A copy of [FastRoundErr.gap1_R], which is local there. *)
Local Lemma gap1_R : B2R Fast.gap1 = bpow radix2 (-53).
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF Fast.gap1) with (SpecFloat.S754_finite false 4503599627370496 (-105))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

(** A copy of [FastRoundErr.finite_of_pos], which is local there: a float
    with a positive value is finite. *)
Local Lemma finite_of_pos : forall x : f64, 0 < B2R x -> is_finite x = true.
Proof. intros [s|s| |s m e' H] Hx; try reflexivity; cbn [B2R] in Hx; lra. Qed.

(** A copy of [FastRoundErr.sub_pow2], which is local there: [2^-q - 2^-p]
    is the float [(2^(p-q) - 1) 2^-p] for [q < p <= q + 53], so [sub]
    computes it exactly. *)
Local Lemma sub_pow2 :
  forall g x q p, is_finite g = true -> is_finite x = true ->
  B2R g = bpow radix2 (- q) -> B2R x = bpow radix2 (- p) ->
  (0 <= q < p)%Z -> (p <= q + 53)%Z -> (p <= 1074)%Z ->
  is_finite (sub g x) = true /\ B2R (sub g x) = bpow radix2 (- q) - bpow radix2 (- p).
Proof.
intros g x q p Fg Fx Rg Rx Hq Hp Hp'.
assert (E : bpow radix2 (- q) - bpow radix2 (- p) =
            F2R (Float radix2 (2 ^ (p - q) - 1) (- p))).
{ unfold F2R; cbn [Fnum Fexp]. rewrite minus_IZR, (IZR_Zpower radix2) by lia.
  rewrite Rmult_minus_distr_r, <- bpow_plus. replace (p - q + - p)%Z with (- q)%Z by ring.
  ring. }
assert (P1 : (2 ^ 0 <= 2 ^ (p - q) <= 2 ^ 53)%Z) by (split; apply Z.pow_le_mono_r; lia).
change (2 ^ 0)%Z with 1%Z in P1.
assert (Ff : G (bpow radix2 (- q) - bpow radix2 (- p))).
{ rewrite E. apply generic_format_FLT.
  apply (FLT_spec _ _ _ _ (Float radix2 (2 ^ (p - q) - 1) (- p))); [reflexivity | |].
  - cbn [Fnum]. rewrite Z.abs_eq by lia. change (Zpower radix2 53) with (2 ^ 53)%Z. lia.
  - cbn [Fexp]. lia. }
assert (B1 : bpow radix2 (- p) <= bpow radix2 (- q)) by (apply bpow_le; lia).
assert (B2 : bpow radix2 (- q) <= bpow radix2 0) by (apply bpow_le; lia).
assert (B3 : bpow radix2 0 < bpow radix2 1024) by (apply bpow_lt; lia).
pose proof (bpow_gt_0 radix2 (- p)) as B4.
unfold sub.
generalize (@Bminus_correct 53 1024 _ _ mode_NE g x Fg Fx).
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE)) with RN.
rewrite Rg, Rx, (round_generic _ _ _ _ Ff).
rewrite Rlt_bool_true by (rewrite Rabs_pos_eq; lra).
intros (HR & HF & _).
split; [exact HF | exact HR].
Qed.

(** [sub_pow2] for the sum: [2^-q + 2^-p] is the float [(2^(p-q) + 1)
    2^-p] for [q < p <= q + 52], whose significand is at most [2^52 + 1],
    so [add] computes it exactly. *)
Local Lemma add_pow2 :
  forall g x q p, is_finite g = true -> is_finite x = true ->
  B2R g = bpow radix2 (- q) -> B2R x = bpow radix2 (- p) ->
  (0 <= q < p)%Z -> (p <= q + 52)%Z -> (p <= 1074)%Z ->
  is_finite (add g x) = true /\ B2R (add g x) = bpow radix2 (- q) + bpow radix2 (- p).
Proof.
intros g x q p Fg Fx Rg Rx Hq Hp Hp'.
assert (E : bpow radix2 (- q) + bpow radix2 (- p) =
            F2R (Float radix2 (2 ^ (p - q) + 1) (- p))).
{ unfold F2R; cbn [Fnum Fexp]. rewrite plus_IZR, (IZR_Zpower radix2) by lia.
  rewrite Rmult_plus_distr_r, <- bpow_plus. replace (p - q + - p)%Z with (- q)%Z by ring.
  ring. }
assert (P1 : (2 ^ 0 <= 2 ^ (p - q) <= 2 ^ 52)%Z) by (split; apply Z.pow_le_mono_r; lia).
change (2 ^ 0)%Z with 1%Z in P1. change (2 ^ 52)%Z with 4503599627370496%Z in P1.
assert (Ff : G (bpow radix2 (- q) + bpow radix2 (- p))).
{ rewrite E. apply generic_format_FLT.
  apply (FLT_spec _ _ _ _ (Float radix2 (2 ^ (p - q) + 1) (- p))); [reflexivity | |].
  - cbn [Fnum]. rewrite Z.abs_eq by lia.
    change (Zpower radix2 53) with 9007199254740992%Z. lia.
  - cbn [Fexp]. lia. }
assert (B1 : bpow radix2 (- p) <= bpow radix2 (- q)) by (apply bpow_le; lia).
assert (B2 : bpow radix2 (- q) <= bpow radix2 0) by (apply bpow_le; lia).
assert (B3 : bpow radix2 0 + bpow radix2 0 < bpow radix2 1024).
{ change (bpow radix2 0) with 1.
  assert (bpow radix2 1 < bpow radix2 1024) by (apply bpow_lt; lia).
  change (bpow radix2 1) with 2 in *. lra. }
pose proof (bpow_gt_0 radix2 (- p)) as B4.
unfold add.
generalize (@Bplus_correct 53 1024 _ _ mode_NE g x Fg Fx).
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE)) with RN.
rewrite Rg, Rx, (round_generic _ _ _ _ Ff).
rewrite Rlt_bool_true by (rewrite Rabs_pos_eq; lra).
intros (HR & HF & _).
split; [exact HF | exact HR].
Qed.

(** A copy of [FastRoundSubBits.mul_exact], which is local there: a
    product that is an [f64] below [2^1024] is exact. *)
Local Lemma mul_exact :
  forall x y : f64, is_finite x = true -> is_finite y = true ->
  G (B2R x * B2R y) -> Rabs (B2R x * B2R y) < bpow radix2 1024 ->
  is_finite (mul x y) = true /\ B2R (mul x y) = B2R x * B2R y.
Proof.
intros x y Fx Fy Fm Hm.
unfold mul.
generalize (@Bmult_correct 53 1024 _ _ mode_NE x y).
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE)) with RN.
rewrite (round_generic _ _ _ _ Fm).
rewrite Rlt_bool_true by exact Hm.
intros (HR & HF & _).
split; [rewrite HF, Fx, Fy; reflexivity | exact HR].
Qed.

(** [2 err C] and [(2^-53 - 2 err) C] are exact, for [err = 2^-p] and [C =
    2^(-1022 - e)]. *)
Lemma sub_err_consts :
  forall (e : Z) (err : f64) (p : Z),
  (-1085 <= e <= -1022)%Z -> (55 <= p <= 105)%Z -> B2R err = bpow radix2 (- p) ->
  is_finite (mul (Fast.sub_unit e) (mul Fast.two err)) = true /\
  B2R (mul (Fast.sub_unit e) (mul Fast.two err)) =
    2 * bpow radix2 (- p) * bpow radix2 (-1022 - e) /\
  is_finite (mul (Fast.sub_unit e) (sub Fast.gap1 (mul Fast.two err))) = true /\
  B2R (mul (Fast.sub_unit e) (sub Fast.gap1 (mul Fast.two err))) =
    (bpow radix2 (-53) - 2 * bpow radix2 (- p)) * bpow radix2 (-1022 - e).
Proof.
intros e err p He Hp Herr.
destruct (sub_unit_spec e He) as (Fc & _ & Rc).
assert (Ft : is_finite Fast.two = true) by (vm_compute; reflexivity).
assert (Fg : is_finite Fast.gap1 = true) by (vm_compute; reflexivity).
assert (Ferr : is_finite err = true).
{ apply finite_of_pos. rewrite Herr. apply bpow_gt_0. }
assert (H2p : bpow radix2 (- (p - 1)) = 2 * bpow radix2 (- p)).
{ replace (- (p - 1))%Z with (1 + - p)%Z by ring. rewrite bpow_plus. reflexivity. }
(* [2 err = 2^(1 - p)] is a power of 2 in the range of the format. *)
assert (P1 : B2R Fast.two * B2R err = bpow radix2 (- (p - 1))).
{ rewrite two_R, Herr. symmetry. exact H2p. }
assert (G1 : G (B2R Fast.two * B2R err)).
{ rewrite P1. apply generic_format_bpow. unfold FLT_exp. lia. }
assert (B1 : Rabs (B2R Fast.two * B2R err) < bpow radix2 1024).
{ rewrite P1, Rabs_pos_eq by apply bpow_ge_0. apply bpow_lt. lia. }
destruct (mul_exact _ _ Ft Ferr G1 B1) as (F1 & R1).
rewrite P1 in R1.
(* [C 2^(1 - p)] is a power of 2 with the exponent [-1021 - e - p] in
   [-104, 9]. *)
assert (P2 : B2R (Fast.sub_unit e) * B2R (mul Fast.two err) =
             bpow radix2 (-1022 - e + - (p - 1))).
{ rewrite Rc, R1, <- bpow_plus. reflexivity. }
assert (G2 : G (B2R (Fast.sub_unit e) * B2R (mul Fast.two err))).
{ rewrite P2. apply generic_format_bpow. unfold FLT_exp. lia. }
assert (B2 : Rabs (B2R (Fast.sub_unit e) * B2R (mul Fast.two err)) < bpow radix2 1024).
{ rewrite P2, Rabs_pos_eq by apply bpow_ge_0. apply bpow_lt. lia. }
destruct (mul_exact _ _ Fc F1 G2 B2) as (F2 & R2).
(* [gap1 - 2 err = 2^-53 - 2^(1 - p)] is exact, as [53 < p - 1 <= 104]. *)
assert (Hq : (0 <= 53 < p - 1)%Z) by lia.
assert (Hq' : (p - 1 <= 53 + 53)%Z) by lia.
assert (Hq'' : (p - 1 <= 1074)%Z) by lia.
destruct (sub_pow2 Fast.gap1 (mul Fast.two err) 53 (p - 1) Fg F1 gap1_R R1 Hq Hq' Hq'')
  as (F3 & R3').
assert (R3 : B2R (sub Fast.gap1 (mul Fast.two err)) =
             bpow radix2 (-53) - bpow radix2 (- (p - 1))) by exact R3'.
(* [C (2^-53 - 2^(1 - p))] is [(2^(p - 54) - 1) 2^(-1021 - e - p)], with a
   significand below [2^53] and the exponent at least [-104]. *)
assert (P4 : B2R (Fast.sub_unit e) * B2R (sub Fast.gap1 (mul Fast.two err)) =
             F2R (Float radix2 (2 ^ (p - 54) - 1) (-1021 - e - p))).
{ rewrite Rc, R3. unfold F2R; cbn [Fnum Fexp].
  rewrite minus_IZR, (IZR_Zpower radix2) by lia.
  assert (E1 : bpow radix2 (p - 54) * bpow radix2 (-1021 - e - p) =
               bpow radix2 (-1022 - e) * bpow radix2 (-53)).
  { rewrite <- 2 bpow_plus. f_equal. ring. }
  assert (E2 : bpow radix2 (-1021 - e - p) =
               bpow radix2 (-1022 - e) * bpow radix2 (- (p - 1))).
  { rewrite <- bpow_plus. f_equal. ring. }
  rewrite Rmult_minus_distr_r, E1, E2. ring. }
assert (Q1 : (2 ^ 0 <= 2 ^ (p - 54) <= 2 ^ 53)%Z) by (split; apply Z.pow_le_mono_r; lia).
change (2 ^ 0)%Z with 1%Z in Q1.
assert (G4 : G (B2R (Fast.sub_unit e) * B2R (sub Fast.gap1 (mul Fast.two err)))).
{ rewrite P4. apply generic_format_FLT.
  apply (FLT_spec _ _ _ _ (Float radix2 (2 ^ (p - 54) - 1) (-1021 - e - p)));
    [reflexivity | |].
  - cbn [Fnum]. rewrite Z.abs_eq by lia. change (Zpower radix2 53) with (2 ^ 53)%Z. lia.
  - cbn [Fexp]. lia. }
(* [0 < 2^-53 - 2^(1 - p) < 1] and [C <= 2^63]. *)
assert (B4 : Rabs (B2R (Fast.sub_unit e) * B2R (sub Fast.gap1 (mul Fast.two err))) <
             bpow radix2 1024).
{ rewrite Rc, R3.
  assert (0 < bpow radix2 (- (p - 1)) < bpow radix2 (-53))
    by (split; [apply bpow_gt_0 | apply bpow_lt; lia]).
  assert (bpow radix2 (-53) <= bpow radix2 0) by (apply bpow_le; lia).
  assert (0 < bpow radix2 (-1022 - e) < bpow radix2 1024)
    by (split; [apply bpow_gt_0 | apply bpow_lt; lia]).
  change (bpow radix2 0) with 1 in *.
  rewrite Rabs_pos_eq by nra. nra. }
destruct (mul_exact _ _ Fc F3 G4 B4) as (F5 & R5).
split; [exact F2|]. split.
{ rewrite R2, Rc, R1, H2p. ring. }
split; [exact F5|]. rewrite R5, Rc, R3, H2p. ring.
Qed.

(** [(2^-53 + 2 err) C] is exact, for [err = 2^-p] and [C = 2^(-1022 -
    e)]. *)
Lemma sub_err_far_consts :
  forall (e : Z) (err : f64) (p : Z),
  (-1085 <= e <= -1022)%Z -> (55 <= p <= 105)%Z -> B2R err = bpow radix2 (- p) ->
  is_finite (mul (Fast.sub_unit e) (add Fast.gap1 (mul Fast.two err))) = true /\
  B2R (mul (Fast.sub_unit e) (add Fast.gap1 (mul Fast.two err))) =
    (bpow radix2 (-53) + 2 * bpow radix2 (- p)) * bpow radix2 (-1022 - e).
Proof.
intros e err p He Hp Herr.
destruct (sub_unit_spec e He) as (Fc & _ & Rc).
assert (Ft : is_finite Fast.two = true) by (vm_compute; reflexivity).
assert (Fg : is_finite Fast.gap1 = true) by (vm_compute; reflexivity).
assert (Ferr : is_finite err = true).
{ apply finite_of_pos. rewrite Herr. apply bpow_gt_0. }
assert (H2p : bpow radix2 (- (p - 1)) = 2 * bpow radix2 (- p)).
{ replace (- (p - 1))%Z with (1 + - p)%Z by ring. rewrite bpow_plus. reflexivity. }
(* [2 err = 2^(1 - p)] is a power of 2 in the range of the format. *)
assert (P1 : B2R Fast.two * B2R err = bpow radix2 (- (p - 1))).
{ rewrite two_R, Herr. symmetry. exact H2p. }
assert (G1 : G (B2R Fast.two * B2R err)).
{ rewrite P1. apply generic_format_bpow. unfold FLT_exp. lia. }
assert (B1 : Rabs (B2R Fast.two * B2R err) < bpow radix2 1024).
{ rewrite P1, Rabs_pos_eq by apply bpow_ge_0. apply bpow_lt. lia. }
destruct (mul_exact _ _ Ft Ferr G1 B1) as (F1 & R1).
rewrite P1 in R1.
(* [gap1 + 2 err = 2^-53 + 2^(1 - p)] is exact, as [53 < p - 1 <= 104]. *)
assert (Hq : (0 <= 53 < p - 1)%Z) by lia.
assert (Hq' : (p - 1 <= 53 + 52)%Z) by lia.
assert (Hq'' : (p - 1 <= 1074)%Z) by lia.
destruct (add_pow2 Fast.gap1 (mul Fast.two err) 53 (p - 1) Fg F1 gap1_R R1 Hq Hq' Hq'')
  as (F3 & R3').
assert (R3 : B2R (add Fast.gap1 (mul Fast.two err)) =
             bpow radix2 (-53) + bpow radix2 (- (p - 1))) by exact R3'.
(* [C (2^-53 + 2^(1 - p))] is [(2^(p - 54) + 1) 2^(-1021 - e - p)], with a
   significand of at most [2^51 + 1] and the exponent at least [-104]. *)
assert (P4 : B2R (Fast.sub_unit e) * B2R (add Fast.gap1 (mul Fast.two err)) =
             F2R (Float radix2 (2 ^ (p - 54) + 1) (-1021 - e - p))).
{ rewrite Rc, R3. unfold F2R; cbn [Fnum Fexp].
  rewrite plus_IZR, (IZR_Zpower radix2) by lia.
  assert (E1 : bpow radix2 (p - 54) * bpow radix2 (-1021 - e - p) =
               bpow radix2 (-1022 - e) * bpow radix2 (-53)).
  { rewrite <- 2 bpow_plus. f_equal. ring. }
  assert (E2 : bpow radix2 (-1021 - e - p) =
               bpow radix2 (-1022 - e) * bpow radix2 (- (p - 1))).
  { rewrite <- bpow_plus. f_equal. ring. }
  rewrite Rmult_plus_distr_r, E1, E2. ring. }
assert (Q1 : (2 ^ 0 <= 2 ^ (p - 54) <= 2 ^ 51)%Z) by (split; apply Z.pow_le_mono_r; lia).
change (2 ^ 0)%Z with 1%Z in Q1. change (2 ^ 51)%Z with 2251799813685248%Z in Q1.
assert (G4 : G (B2R (Fast.sub_unit e) * B2R (add Fast.gap1 (mul Fast.two err)))).
{ rewrite P4. apply generic_format_FLT.
  apply (FLT_spec _ _ _ _ (Float radix2 (2 ^ (p - 54) + 1) (-1021 - e - p)));
    [reflexivity | |].
  - cbn [Fnum]. rewrite Z.abs_eq by lia.
    change (Zpower radix2 53) with 9007199254740992%Z. lia.
  - cbn [Fexp]. lia. }
(* [0 < 2^-53 + 2^(1 - p) < 1] and [C <= 2^63]. *)
assert (B4 : Rabs (B2R (Fast.sub_unit e) * B2R (add Fast.gap1 (mul Fast.two err))) <
             bpow radix2 1024).
{ rewrite Rc, R3.
  assert (0 < bpow radix2 (- (p - 1)) < bpow radix2 (-53))
    by (split; [apply bpow_gt_0 | apply bpow_lt; lia]).
  assert (bpow radix2 (-53) <= bpow radix2 (-1)) by (apply bpow_le; lia).
  assert (0 < bpow radix2 (-1022 - e) < bpow radix2 1024)
    by (split; [apply bpow_gt_0 | apply bpow_lt; lia]).
  change (bpow radix2 (-1)) with (/ 2) in *.
  rewrite Rabs_pos_eq by nra. nra. }
destruct (mul_exact _ _ Fc F3 G4 B4) as (F5 & R5).
split; [exact F5|]. rewrite R5, Rc, R3, H2p. ring.
Qed.

(** ** The tests for subnormal results *)

Theorem round_dir_sub_err_correct :
  forall h l e err p up v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < B2R h < 2 -> (-1085 <= e <= -1022)%Z ->
  (55 <= p <= 105)%Z -> B2R err = bpow radix2 (- p) ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (- p) ->
  Fast.round_dir_sub_err h l e err up = Some v ->
  rounds up (y * bpow radix2 e) v.
Proof.
intros h l e err p up v y Fh Fl Hrn Hh He Hp Herr Hy Hv.
destruct (sub_unit_spec e He) as (Fc & Bc & _).
destruct (sub_consts e He) as (F2c & R2c & _ & _ & _ & _).
destruct (sub_err_consts e err p He Hp Herr) as (Fb & Rb & _ & _).
destruct (sub_common_err h l e p y Fh Fl Hrn Hh He Hp Hy) as (Fs & Hk).
unfold Fast.round_dir_sub_err, Fast.fast_two_sum in Hv; cbv beta iota zeta in Hv.
set (c := Fast.sub_unit e) in *.
set (s := add c h) in *.
set (u := add (add h (sub c s)) l) in *.
set (b := mul c (mul Fast.two err)) in *.
set (g := bpow radix2 (-1074 - e)) in *.
(* The guard [s < 2C] keeps [s] in the binade of [C], where [s = C + N g]. *)
destruct (ge s (mul Fast.two c)) eqn:G0; [discriminate Hv|].
pose proof (FastRound.ge_false _ _ Fs F2c G0) as Hs2. rewrite R2c in Hs2.
destruct (Hk Hs2) as (Fu & Hy0 & N & HN & Hbits & HD1 & HD2).
apply Rabs_le_inv in HD1. apply Rabs_def2 in HD2.
destruct (gt u b) eqn:G1.
- (* [u > b]: [y - N g >= u - b > 0], so [y] is in [(N g, (N + 1) g)],
     whose ends are [s - C] and its successor, the bits of [s] and [s + 1]
     less those of [C]. *)
  pose proof (FastRound.gt_true _ _ Fu Fb G1) as Hub. rewrite Rb in Hub.
  injection Hv as <-.
  replace (to_bits (if up then from_bits (to_bits s + 1) else s) - to_bits c)%Z
    with (if up then (N + 1)%Z else N).
  2: { destruct up; [rewrite to_from_bits by lia|]; rewrite Hbits, Bc; ring. }
  apply (sub_bracket e N up y); [lia | fold g; lra].
- destruct (lt u (opp b)) eqn:G2; [|discriminate Hv].
  (* [u < -b]: [y - N g <= u + b < 0], so [y] is in [((N - 1) g, N g)],
     the bits of [s - 1] and [s] less those of [C]; [N >= 1] as [y > 0]. *)
  assert (Fob : is_finite (opp b) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fb).
  pose proof (DyExpRules.lt_R _ _ Fu Fob G2) as Hub.
  unfold opp in Hub. rewrite B2R_Bopp, Rb in Hub.
  assert (Hg : 0 < g) by apply bpow_gt_0.
  assert (HN1 : (1 <= N)%Z).
  { destruct (Z_lt_le_dec 0 N) as [HN0|HN0]; [lia|]. exfalso.
    apply IZR_le in HN0. nra. }
  injection Hv as <-.
  replace (to_bits (if up then s else from_bits (to_bits s - 1)) - to_bits c)%Z
    with (if up then (N - 1 + 1)%Z else (N - 1)%Z).
  2: { destruct up; [|rewrite to_from_bits by lia]; rewrite Hbits, Bc; ring. }
  apply (sub_bracket e (N - 1) up y); [lia|]. fold g. rewrite minus_IZR. lra.
Qed.

Theorem round_near_sub_err_correct :
  forall h l e err p v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < B2R h < 2 -> (-1085 <= e <= -1022)%Z ->
  (55 <= p <= 105)%Z -> B2R err = bpow radix2 (- p) ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (- p) ->
  Fast.round_near_sub_err h l e err = Some v ->
  near_round (y * bpow radix2 e) v.
Proof.
intros h l e err p v y Fh Fl Hrn Hh He Hp Herr Hy Hv.
destruct (sub_unit_spec e He) as (Fc & Bc & _).
destruct (sub_consts e He) as (F2c & R2c & _ & _ & _ & _).
destruct (sub_err_consts e err p He Hp Herr) as (_ & _ & Fb & Rb).
destruct (sub_err_far_consts e err p He Hp Herr) as (Ff & Rf).
destruct (sub_common_err h l e p y Fh Fl Hrn Hh He Hp Hy) as (Fs & Hk).
unfold Fast.round_near_sub_err, Fast.fast_two_sum in Hv; cbv beta iota zeta in Hv.
set (c := Fast.sub_unit e) in *.
set (s := add c h) in *.
set (u := add (add h (sub c s)) l) in *.
set (b := mul c (sub Fast.gap1 (mul Fast.two err))) in *.
set (f := mul c (add Fast.gap1 (mul Fast.two err))) in *.
set (g := bpow radix2 (-1074 - e)) in *.
(* The guard [s < 2C] keeps [s] in the binade of [C], where [s = C + N g]. *)
destruct (ge s (mul Fast.two c)) eqn:G0; [discriminate Hv|].
pose proof (FastRound.ge_false _ _ Fs F2c G0) as Hs2. rewrite R2c in Hs2.
destruct (Hk Hs2) as (Fu & Hy0 & N & HN & Hbits & HD1 & HD2).
apply Rabs_le_inv in HD1. apply Rabs_def2 in HD2.
assert (Hg : 0 < g) by apply bpow_gt_0.
assert (Hg2 : bpow radix2 (-53) * bpow radix2 (-1022 - e) = g / 2).
{ unfold g. rewrite <- bpow_plus.
  replace (-1074 - e)%Z with (1 + (-53 + (-1022 - e)))%Z by ring.
  rewrite (bpow_plus _ 1). change (bpow radix2 1) with 2. field. }
destruct (lt u b && gt u (opp b)) eqn:G1.
- (* [|u| < (2^-53 - 2 err) C] and [|y - N g - u| <= 2 err C] put [y]
     within [2^-53 C = g / 2] of [N g], and the result is the [f64] whose
     bits are those of [s] less those of [C], [N]. *)
  apply andb_prop in G1 as (G1 & G2).
  assert (Fob : is_finite (opp b) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fb).
  pose proof (DyExpRules.lt_R _ _ Fu Fb G1) as Hub.
  pose proof (FastRound.gt_true _ _ Fu Fob G2) as Hlb.
  unfold opp in Hlb. rewrite B2R_Bopp in Hlb. rewrite Rb in Hub, Hlb.
  injection Hv as <-.
  replace (to_bits s - to_bits c)%Z with N by (rewrite Hbits, Bc; ring).
  apply (sub_near_grid e N y); [lia | exact Hy0 | apply Rabs_def1; fold g; lra].
- destruct (gt u f) eqn:G2.
  + (* [u > (2^-53 + 2 err) C]: [y - N g >= u - 2 err C > 2^-53 C = g / 2],
       and [y - N g < g], so [y] is within [g / 2] of [(N + 1) g], whose
       bits are those of the [f64] after [s] less those of [C]. *)
    pose proof (FastRound.gt_true _ _ Fu Ff G2) as Huf. rewrite Rf in Huf.
    (* [injection] on [Hv] as it stands ran for over ten minutes without
       finishing, so the bits are rewritten to [N + 1] first (here and in
       the next case). *)
    cbv beta iota in Hv.
    replace (to_bits (from_bits (to_bits s + 1)) - to_bits c)%Z with (N + 1)%Z in Hv
      by (rewrite to_from_bits by lia; rewrite Hbits, Bc; ring).
    injection Hv as <-.
    apply (sub_near_grid e (N + 1) y); [lia | exact Hy0 |].
    rewrite plus_IZR. apply Rabs_def1; fold g; lra.
  + destruct (lt u (opp f)) eqn:G3; [|discriminate Hv].
    (* [u < -(2^-53 + 2 err) C]: [y - N g <= u + 2 err C < -g / 2], and
       [y - N g > -g], so [y] is within [g / 2] of [(N - 1) g], whose bits
       are those of the [f64] before [s] less those of [C]; [N >= 1] as
       [y > 0]. *)
    assert (Fof : is_finite (opp f) = true) by (unfold opp; rewrite is_finite_Bopp; exact Ff).
    pose proof (DyExpRules.lt_R _ _ Fu Fof G3) as Huf.
    unfold opp in Huf. rewrite B2R_Bopp, Rf in Huf.
    assert (Hlt : y - IZR N * g < - (g / 2)) by lra.
    assert (HN1 : (1 <= N)%Z).
    { destruct (Z_lt_le_dec 0 N) as [HN0|HN0]; [lia|]. exfalso.
      apply IZR_le in HN0. nra. }
    cbv beta iota in Hv.
    replace (to_bits (from_bits (to_bits s - 1)) - to_bits c)%Z with (N - 1)%Z in Hv
      by (rewrite to_from_bits by lia; rewrite Hbits, Bc; ring).
    injection Hv as <-.
    apply (sub_near_grid e (N - 1) y); [lia | exact Hy0 |].
    rewrite minus_IZR. apply Rabs_def1; fold g; lra.
Qed.

(** ** The theorems *)

(** [e = -1022] with [h <= 1] fails the test [le h one], and so gives [h >
    1] in the other branch. *)
Local Lemma wide_err_split :
  forall (h : f64) (e : Z), is_finite h = true -> (-1085 <= e <= 1023)%Z ->
  ((e <? -1022)%Z || ((e =? -1022)%Z && le h Fast.one)) = true /\ (-1085 <= e <= -1022)%Z \/
  ((e <? -1022)%Z || ((e =? -1022)%Z && le h Fast.one)) = false /\
  (-1022 <= e <= 1023)%Z /\ ((e = -1022)%Z -> 1 < B2R h).
Proof.
intros h e Fh He.
destruct ((e <? -1022)%Z || ((e =? -1022)%Z && le h Fast.one)) eqn:K2.
- left. split; [reflexivity|].
  apply Bool.orb_true_iff in K2 as [K2|K2].
  + apply Z.ltb_lt in K2. lia.
  + apply Bool.andb_true_iff in K2 as [K2 _]. apply Z.eqb_eq in K2. lia.
- right. split; [reflexivity|].
  apply Bool.orb_false_iff in K2 as [K2 K3].
  apply Z.ltb_ge in K2. split; [lia|].
  intros Ee. subst e. rewrite Z.eqb_refl in K3. cbn [andb] in K3.
  (* [le h one] is [ge one h]. *)
  pose proof (ge_false Fast.one h eq_refl Fh K3) as L. rewrite one_R in L. exact L.
Qed.

Theorem round_dir_wide_err_correct :
  forall h l e err p up v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < B2R h < 2 -> (-1085 <= e)%Z ->
  (55 <= p <= 105)%Z -> B2R err = bpow radix2 (- p) ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (- p) ->
  Fast.round_dir_wide_err h l e err up = Some v ->
  rounds up (y * bpow radix2 e) v.
Proof.
intros h l e err p up v y Fh Fl Hrn Hh He Hp Herr Hy Hv.
unfold Fast.round_dir_wide_err in Hv.
destruct (1023 <? e)%Z eqn:K1; [discriminate|].
apply Z.ltb_ge in K1.
destruct (wide_err_split h e Fh ltac:(lia)) as [(K2 & He') | (K2 & He' & H1)];
  rewrite K2 in Hv.
- exact (round_dir_sub_err_correct h l e err p up v y Fh Fl Hrn Hh He' Hp Herr Hy Hv).
- exact (round_dir_err_normal_correct h l e err p up v y Fh Fl Hrn He' H1 Hp Herr Hy Hv).
Qed.

Theorem round_near_wide_err_correct :
  forall h l e err p v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < B2R h < 2 -> (-1085 <= e)%Z ->
  (55 <= p <= 105)%Z -> B2R err = bpow radix2 (- p) ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (- p) ->
  Fast.round_near_wide_err h l e err = Some v ->
  near_round (y * bpow radix2 e) v.
Proof.
intros h l e err p v y Fh Fl Hrn Hh He Hp Herr Hy Hv.
unfold Fast.round_near_wide_err in Hv.
destruct (1023 <? e)%Z eqn:K1; [discriminate|].
apply Z.ltb_ge in K1.
destruct (wide_err_split h e Fh ltac:(lia)) as [(K2 & He') | (K2 & He' & H1)];
  rewrite K2 in Hv.
- exact (round_near_sub_err_correct h l e err p v y Fh Fl Hrn Hh He' Hp Herr Hy Hv).
- exact (round_near_err_normal_correct h l e err p v y Fh Fl Hrn He' H1 Hp Herr Hy Hv).
Qed.
