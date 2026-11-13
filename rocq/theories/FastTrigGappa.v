(** * Round-off bounds of the fast path of [sin] and [cos], by Gappa

    [DyadicTrig.fast_eval] of [Model.v] computes the polynomials [cm = z (z
    C4 - 1/2)] of cos [rr] - 1 and [s3 = rr z (z S5 - S3)] of sin [rr] -
    [rr], for [z = rr^2], in [f64] rounded to nearest. [cm_gappa] and
    [s3_gappa] bound their round-off for [|rr| <= 6436 2^-24] (about
    3.836e-4), against the polynomials with 1/24, 1/120 and 1/6, so the
    bounds include the errors of the constants [C4], [S5] and [S3]. The
    [gappa] tactic of coq-gappa runs the Gappa program on the goal and turns
    its answer into a proof term that Rocq's kernel checks at [Qed], so the
    bounds rest on the same axioms as the rest of the proofs. [poly_cm_gappa]
    and [poly_s3_gappa] restate them for the [f64] operations of [Model.v],
    as [fast_eval_correct] of [FastTrigEval.v] uses them. *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Gappa Require Import Gappa_tactic.
From Inari Require Import Model TwoSum FastExpErr FastExpTables.

(* coq-gappa 1.11.0 names [Coq.Init.Logic.and] and other paths that Rocq 9
   renamed, and Rocq warns about each at every [gappa] call. The build turns
   warnings into errors ([-w +default] in [rocq/Makefile]), so this file,
   and only this file, turns the warning off: a [Set] in a file does not
   reach the files that require it. *)
Set Warnings "-deprecated-dirpath-Coq".

Open Scope R_scope.

(** Powers of 2 as numerals, for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp] in *.

(** [cm] for [C4 = 6004799503160661 2^-57], 1/24 rounded to nearest. The
    exact term has the shape of the computation, [r * r * / 24]: with
    [r * r / 24], Gappa gave no answer within 300 s when it was tried. *)
Lemma cm_gappa :
  forall r, Rabs r <= 6436 * bpow radix2 (-24) ->
  Rabs (RN (RN (r * r) * RN (RN (RN (r * r) * (6004799503160661 * bpow radix2 (-57))) - / 2)) -
        r * r * (r * r * / 24 - / 2)) <= 21 * bpow radix2 (-80).
Proof. intros r Hr. gappa. Qed.

(** [s3] for [S5 = 4803839602528529 2^-59] and [S3 = 6004799503160661
    2^-55], 1/120 and 1/6 rounded to nearest. *)
Lemma s3_gappa :
  forall r, Rabs r <= 6436 * bpow radix2 (-24) ->
  Rabs (RN (RN (r * RN (r * r)) *
            RN (RN (RN (r * r) * (4803839602528529 * bpow radix2 (-59))) -
                6004799503160661 * bpow radix2 (-55))) -
        r * (r * r) * (r * r * / 120 - / 6)) <= 5 * bpow radix2 (-90).
Proof. intros r Hr. gappa. Qed.

(** [cm_gappa] for the [f64] operations, with the bound of the hand-proved
    [poly_cm] of [FastTrigEval.v] at [X = 3836e-7]. *)
Lemma poly_cm_gappa :
  forall rr, is_finite rr = true -> Rabs (B2R rr) <= 3836e-7 ->
  let z := mul rr rr in
  let cm := mul z (sub (mul z (from_bits DyadicTrig.C4)) half) in
  is_finite cm = true /\
  Rabs (B2R cm - B2R rr ^ 2 * (B2R rr ^ 2 / 24 - / 2)) <=
    bpow radix2 (-53) * 3836e-7 ^ 2 * (3 / 2 + bpow radix2 (-12)) + bpow radix2 (-1070).
Proof.
intros rr Frr Hrr. cbv zeta.
(* Gappa drops the decimal bound [3836e-7]: give it a dyadic one. *)
assert (Hr : Rabs (B2R rr) <= 6436 * bpow radix2 (-24)) by (num; lra).
(* [C4] and [half] as the exact dyadic numbers of [cm_gappa]. *)
assert (E4 : fix_of 57 (from_bits DyadicTrig.C4) = Some 6004799503160661%Z)
  by (vm_compute; reflexivity).
apply fix_of_correct in E4 as [F4 E4].
assert (Eh : fix_of 53 half = Some 4503599627370496%Z) by (vm_compute; reflexivity).
apply fix_of_correct in Eh as [Fh Eh].
cbn [Z.opp] in E4, Eh.
replace (IZR 4503599627370496 * bpow radix2 (-53)) with (/ 2) in Eh by (num; lra).
(* Each step is [RN] of its exact result, which Gappa bounds by 16. *)
destruct (mul_e rr rr Frr Frr ltac:(gappa)) as (Fz & Ez & _).
destruct (mul_e _ _ Fz F4 ltac:(rewrite Ez, E4; gappa)) as (F1 & E1 & _).
destruct (sub_e _ _ F1 Fh ltac:(rewrite E1, Ez, E4, Eh; gappa)) as (F2 & E2 & _).
destruct (mul_e _ _ Fz F2 ltac:(rewrite E2, E1, Ez, E4, Eh; gappa)) as (Fcm & Ecm & _).
split; [exact Fcm|].
rewrite Ecm, E2, E1, Ez, E4, Eh.
replace (B2R rr ^ 2 * (B2R rr ^ 2 / 24 - / 2))
  with (B2R rr * B2R rr * (B2R rr * B2R rr * / 24 - / 2)) by (unfold Rdiv; ring).
eapply Rle_trans; [exact (cm_gappa _ Hr)|]. num. lra.
Qed.

(** [s3_gappa] for the [f64] operations, with the bound of the hand-proved
    [poly_s3] of [FastTrigEval.v] at [X = 3836e-7]. *)
Lemma poly_s3_gappa :
  forall rr, is_finite rr = true -> Rabs (B2R rr) <= 3836e-7 ->
  let z := mul rr rr in
  let s3 := mul (mul rr z) (sub (mul z (from_bits DyadicTrig.S5)) (from_bits DyadicTrig.S3)) in
  is_finite s3 = true /\
  Rabs (B2R s3 - B2R rr ^ 3 * (B2R rr ^ 2 / 120 - / 6)) <=
    bpow radix2 (-53) * 3836e-7 ^ 3 + bpow radix2 (-1070).
Proof.
intros rr Frr Hrr. cbv zeta.
(* Gappa drops the decimal bound [3836e-7]: give it a dyadic one. *)
assert (Hr : Rabs (B2R rr) <= 6436 * bpow radix2 (-24)) by (num; lra).
(* [S5] and [S3] as the exact dyadic numbers of [s3_gappa]. *)
assert (E5 : fix_of 59 (from_bits DyadicTrig.S5) = Some 4803839602528529%Z)
  by (vm_compute; reflexivity).
apply fix_of_correct in E5 as [F5 E5].
assert (E3 : fix_of 55 (from_bits DyadicTrig.S3) = Some 6004799503160661%Z)
  by (vm_compute; reflexivity).
apply fix_of_correct in E3 as [F3 E3].
cbn [Z.opp] in E5, E3.
(* Each step is [RN] of its exact result, which Gappa bounds by 16. *)
destruct (mul_e rr rr Frr Frr ltac:(gappa)) as (Fz & Ez & _).
destruct (mul_e _ _ Frr Fz ltac:(rewrite Ez; gappa)) as (Fv & Ev & _).
destruct (mul_e _ _ Fz F5 ltac:(rewrite Ez, E5; gappa)) as (F1 & E1 & _).
destruct (sub_e _ _ F1 F3 ltac:(rewrite E1, Ez, E5, E3; gappa)) as (F2 & E2 & _).
destruct (mul_e _ _ Fv F2 ltac:(rewrite Ev, E2, E1, Ez, E5, E3; gappa)) as (Fs3 & Es3 & _).
split; [exact Fs3|].
rewrite Es3, Ev, E2, E1, Ez, E5, E3.
replace (B2R rr ^ 3 * (B2R rr ^ 2 / 120 - / 6))
  with (B2R rr * (B2R rr * B2R rr) * (B2R rr * B2R rr * / 120 - / 6)) by (unfold Rdiv; ring).
eapply Rle_trans; [exact (s3_gappa _ Hr)|]. num. lra.
Qed.
