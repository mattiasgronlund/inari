(** * The count of multiples of π/2 between two floats

    [quadrants a b] in [src/elementary.rs], for finite [a <= b], returns
    the quadrant of [a] and a count [n] of [kb - ka], where
    [ka = floor(a / (π/2))] and [kb = floor(b / (π/2))]
    ([quadrants_correct]). The quadrants of [a] and [b] ([TrigQuad.v])
    give [d = (kb - ka) mod 4], so [kb - ka] is [d] or at least [d + 4].
    In the first case [b - a < (d + 1) * π/2], and in the second
    [b - a > (d + 3) * π/2]. [2 * d + 3] lies between the two, and is a
    float, so [b - a] rounded to nearest is at most [2 * d + 3] in the
    first case and above it in the second, or +inf. [n] is then [d], or
    [d + 4] ([count_f]), which is [kb - ka] if that is less than 4, and at
    least 4 otherwise ([count_f_val]). [int_tests] gives the tests that
    the branches of [sin], [cos] and [tan] make of such an [n]. *)

From Stdlib Require Import ZArith Reals Lra Lia QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr MpfrRound TrigPieces TrigQuad
  Encoding Decompose AddSub AddRu PiBounds TrigReduce.

Open Scope R_scope.

(** The count that [quadrants] returns for the quadrants [ja] of [a] and
    [jb] of [b], where [big] says whether [kb - ka >= 4]. *)
Definition count_f (ja jb : Z) (big : bool) : f64 :=
  let d := rem_euclid (Model.sub (quad_f jb) (quad_f ja)) (of_u64 4) in
  if big then Model.add d (of_u64 4) else d.

(** A finite float that compares equal to [k as f64], for
    [0 <= k <= 2^53], is [k]. The bounds are a [bool] test, so that
    [vm_compute] decides them for a closed [k]. *)
Lemma ct_eq_val :
  forall f k, ((0 <=? k) && (k <=? 2^53))%Z = true -> is_finite f = true ->
  Model.eq f (of_u64 k) = true ->
  B2R f = IZR k.
Proof.
intros f k Hk Ff E.
apply andb_prop in Hk. destruct Hk as [Hk1 Hk2].
apply Z.leb_le in Hk1, Hk2.
destruct (of_u64_exact k (conj Hk1 Hk2)) as (Fk & _ & Rk).
unfold Model.eq in E. rewrite Beqb_correct in E by easy.
rewrite <- Rk. revert E. case Req_bool_spec; easy.
Qed.

Lemma ct_cases :
  forall j, (0 <= j <= 3)%Z -> j = 0%Z \/ j = 1%Z \/ j = 2%Z \/ j = 3%Z.
Proof. intros j Hj. lia. Qed.

(** The bound [2 * d + 3] that [quadrants] compares [b - a] with, for the
    quadrants [ja] of [a] and [jb] of [b]. Each case is a closed float
    term, which [vm_compute] evaluates. *)
Lemma ct_bound :
  forall ja jb, (0 <= ja <= 3)%Z -> (0 <= jb <= 3)%Z ->
  is_finite (Model.add (Model.mul (of_u64 2)
    (rem_euclid (Model.sub (quad_f jb) (quad_f ja)) (of_u64 4))) (of_u64 3)) = true /\
  B2R (Model.add (Model.mul (of_u64 2)
    (rem_euclid (Model.sub (quad_f jb) (quad_f ja)) (of_u64 4))) (of_u64 3)) =
  IZR (2 * ((jb - ja) mod 4) + 3).
Proof.
intros ja jb Hja Hjb.
destruct (ct_cases ja Hja) as [-> | [-> | [-> | ->]]], (ct_cases jb Hjb) as [-> | [-> | [-> | ->]]];
  (split; [vm_compute; reflexivity | apply ct_eq_val; vm_compute; reflexivity]).
Qed.

Lemma count_f_val :
  forall ja jb big, (0 <= ja <= 3)%Z -> (0 <= jb <= 3)%Z ->
  is_finite (count_f ja jb big) = true /\
  B2R (count_f ja jb big) = IZR ((jb - ja) mod 4 + if big then 4 else 0).
Proof.
intros ja jb big Hja Hjb.
destruct (ct_cases ja Hja) as [-> | [-> | [-> | ->]]], (ct_cases jb Hjb) as [-> | [-> | [-> | ->]]], big;
  (split; [vm_compute; reflexivity | apply ct_eq_val; vm_compute; reflexivity]).
Qed.

(** Comparisons of integers as reals. *)
Lemma ct_cmp :
  forall V j,
  Req_bool (IZR V) (IZR j) = (V =? j)%Z /\
  Rlt_bool (IZR V) (IZR j) = (V <? j)%Z /\
  Rle_bool (IZR V) (IZR j) = (V <=? j)%Z.
Proof.
intros V j.
destruct (Z.compare_spec V j) as [->|Hlt|Hgt].
- rewrite Req_bool_true, Rlt_bool_false, Rle_bool_true by lra.
  rewrite Z.eqb_refl, Z.ltb_irrefl, Z.leb_refl. auto.
- apply IZR_lt in Hlt as H.
  rewrite Req_bool_false, Rlt_bool_true, Rle_bool_true by lra.
  destruct (Z.eqb_spec V j), (Z.ltb_spec V j), (Z.leb_spec V j); try lia; auto.
- apply IZR_lt in Hgt as H.
  rewrite Req_bool_false, Rlt_bool_false, Rle_bool_false by lra.
  destruct (Z.eqb_spec V j), (Z.ltb_spec V j), (Z.leb_spec V j); try lia; auto.
Qed.

(** The tests of a float that holds an integer [V] against 0 to 4. *)
Lemma int_tests :
  forall v V, is_finite v = true -> B2R v = IZR V ->
  Model.eq v Model.zero = (V =? 0)%Z /\
  forall j, (1 <= j <= 4)%Z ->
    Model.lt v (of_u64 j) = (V <? j)%Z /\
    Model.le v (of_u64 j) = (V <=? j)%Z /\
    Model.eq v (of_u64 j) = (V =? j)%Z.
Proof.
intros v V Fv Ev.
unfold Model.eq, Model.lt, Model.le.
split.
- rewrite Beqb_correct by easy. rewrite Ev.
  change (B2R Model.zero) with (IZR 0).
  now destruct (ct_cmp V 0) as (R1 & _ & _).
- intros j Hj.
  destruct (of_u64_exact j) as (Fj & _ & Rj); [lia|].
  rewrite Beqb_correct, Bltb_correct, Bleb_correct by easy. rewrite Ev, Rj.
  destruct (ct_cmp V j) as (R1 & R2 & R3). auto.
Qed.

(** [n / 4] is a float for [0 <= n <= 64]. *)
Lemma ct_quarter_format :
  forall n, (0 <= n <= 64)%Z -> generic_format radix2 fexp64 (IZR n / 4).
Proof.
intros n Hn.
apply generic_format_FLT.
apply FLT_spec with (Float radix2 n (-2)).
- unfold F2R; cbn [Fnum Fexp bpow radix_val radix2 Z.pow_pos]. lra.
- cbn [Fnum]. simpl Z.pow. lia.
- cbn [Fexp]. lia.
Qed.

Theorem quadrants_correct :
  forall emin emax m a b ka kb,
  range_ok emin emax -> get_d_ok emin emax m -> sin_ok emin emax m -> cos_ok emin emax m ->
  is_finite a = true -> is_finite b = true -> B2R a <= B2R b ->
  IZR ka * (PI / 2) <= B2R a < (IZR ka + 1) * (PI / 2) ->
  IZR kb * (PI / 2) <= B2R b < (IZR kb + 1) * (PI / 2) ->
  quadrants m a b = (quad_f (ka mod 4), count_f (ka mod 4) (kb mod 4) (4 <=? kb - ka)%Z).
Proof.
intros emin emax m a b ka kb Hrng Hg Hs Hc Fa Fb Hab Ha Hb.
unfold quadrants, count_f; cbv zeta.
rewrite (quadrant_correct emin emax m a ka Hrng Hg Hs Hc Fa Ha).
rewrite (quadrant_correct emin emax m b kb Hrng Hg Hs Hc Fb Hb).
assert (Hja : (0 <= ka mod 4 <= 3)%Z) by (pose proof (Z.mod_pos_bound ka 4); lia).
assert (Hjb : (0 <= kb mod 4 <= 3)%Z) by (pose proof (Z.mod_pos_bound kb 4); lia).
destruct (ct_bound _ _ Hja Hjb) as (FT & RT).
set (d := rem_euclid (Model.sub (quad_f (kb mod 4)) (quad_f (ka mod 4))) (of_u64 4)) in *.
set (T := Model.add (Model.mul (of_u64 2) d) (of_u64 3)) in *.
(* [3.14 < π < 3.15], from the bounds of [Interval::PI]. *)
assert (HPI : 314 / 100 < PI < 315 / 100).
{ destruct PI_bounds as [H1 H2]. rewrite pb_lo_R in H1. rewrite pb_hi_R in H2.
  unfold Q2R in H1, H2; cbn [Qnum Qden] in H1, H2. lra. }
assert (Hk : (ka <= kb)%Z).
{ assert (L : IZR ka < IZR (kb + 1)).
  { rewrite plus_IZR. apply (Rmult_lt_reg_r (PI / 2)); lra. }
  apply lt_IZR in L. lia. }
(* [d = (kb - ka) mod 4]. *)
rewrite <- Zminus_mod in RT.
assert (ED : IZR kb = IZR ka + IZR (kb - ka)) by (rewrite minus_IZR; ring).
rewrite ED in Hb.
set (D := (kb - ka)%Z) in *.
assert (HD0 : (0 <= D)%Z) by lia.
pose proof (Z.mod_pos_bound D 4) as Hdd.
set (dd := (D mod 4)%Z) in *.
assert (Idd : 0 <= IZR dd <= 3) by (split; apply IZR_le; lia).
assert (FT2 : generic_format radix2 fexp64 (IZR (2 * dd + 3))) by (apply rd_int_format; lia).
rewrite plus_IZR, mult_IZR in RT.
pose proof (Bminus_correct 53 1024 _ _ mode_NE b a Fb Fa) as H.
change (Bminus mode_NE b a) with (Model.sub b a) in H.
change (SpecFloat.fexp 53 1024) with fexp64 in H. cbn [round_mode] in H.
set (n := Model.sub b a) in *. clearbody n.
assert (Hle : Model.le n T = negb (4 <=? D)%Z).
{ destruct (Z_lt_le_dec D 4) as [HD|HD].
  - (* [kb - ka = d], and [b - a < (d + 1) * π/2 < 2 * d + 3]. *)
    assert (E : D = dd) by (unfold dd; symmetry; apply Z.mod_small; lia).
    assert (W1 : B2R b - B2R a < (IZR D + 1) * (PI / 2)) by lra.
    rewrite E in W1.
    assert (W2 : (IZR dd + 1) * (PI / 2) <= (IZR dd + 1) * 2)
      by (apply Rmult_le_compat_l; lra).
    assert (R1 : rd_RNE (B2R b - B2R a) <= IZR (2 * dd + 3)).
    { rewrite <- (round_generic _ _ ZnearestE _ FT2).
      apply round_le; [typeclasses eauto..|].
      rewrite plus_IZR, mult_IZR. lra. }
    rewrite plus_IZR, mult_IZR in R1.
    assert (R0 : 0 <= rd_RNE (B2R b - B2R a)).
    { rewrite <- (round_0 radix2 fexp64 ZnearestE).
      apply round_le; [typeclasses eauto..|]. lra. }
    rewrite (proj2 (Z.leb_gt 4 D) HD). cbn [negb].
    revert H. case Rlt_bool_spec; intros Hr H.
    + destruct H as (Rn & Fn & _).
      unfold Model.le. rewrite Bleb_correct by easy. rewrite Rn, RT.
      apply Rle_bool_true. lra.
    + (* No overflow: [b - a] is below 9. *)
      exfalso. revert Hr. rewrite Rabs_pos_eq by exact R0.
      cbn [bpow radix_val radix2 Z.pow_pos]. lra.
  - (* [kb - ka >= d + 4], and
       [b - a > (d + 3) * π/2 > 2 * d + 3.25 > 2 * d + 3]. *)
    assert (HD4 : (dd + 4 <= D)%Z).
    { pose proof (Z.div_mod D 4) as M. unfold dd in *. lia. }
    assert (I4 : IZR (dd + 3) <= IZR (D - 1)) by (apply IZR_le; lia).
    rewrite plus_IZR, minus_IZR in I4.
    assert (W1 : (IZR D - 1) * (PI / 2) < B2R b - B2R a) by lra.
    assert (W2 : (IZR dd + 3) * (PI / 2) <= (IZR D - 1) * (PI / 2))
      by (apply Rmult_le_compat_r; lra).
    assert (W3 : (IZR dd + 3) * (157 / 100) <= (IZR dd + 3) * (PI / 2))
      by (apply Rmult_le_compat_l; lra).
    assert (FQ : generic_format radix2 fexp64 (IZR (8 * dd + 13) / 4))
      by (apply ct_quarter_format; lia).
    assert (R2 : IZR (8 * dd + 13) / 4 <= rd_RNE (B2R b - B2R a)).
    { rewrite <- (round_generic _ _ ZnearestE _ FQ).
      apply round_le; [typeclasses eauto..|].
      rewrite plus_IZR, mult_IZR. lra. }
    rewrite plus_IZR, mult_IZR in R2.
    rewrite (proj2 (Z.leb_le 4 D) HD). cbn [negb].
    revert H. case Rlt_bool_spec; intros Hr H.
    + destruct H as (Rn & Fn & _).
      unfold Model.le. rewrite Bleb_correct by easy. rewrite Rn, RT.
      apply Rle_bool_false. lra.
    + (* An overflow: [b] is positive, so [n] is +inf. *)
      destruct H as (Hn & Hsg).
      assert (Sb : Bsign b = false).
      { destruct (Bsign b) eqn:Sb; [exfalso|easy].
        assert (Sa : Bsign a = false).
        { destruct (Bsign a) eqn:Sa; [|easy]. rewrite ?Sb, ?Sa in Hsg. easy. }
        apply B2R_Bsign_true in Sb. apply B2R_Bsign_false in Sa. lra. }
      rewrite Sb in Hn.
      assert (En : n = B754_infinity false)
        by (apply B2SF_inj; rewrite Hn; reflexivity).
      rewrite En. now destruct (rd_inf_cmp T FT) as (_ & R & _). }
rewrite Hle. destruct (4 <=? D)%Z; reflexivity.
Qed.
