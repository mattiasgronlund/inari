(** * [add_odd] rounds to odd

    [add_odd x y] is [x + y] rounded to odd ([BM08] S. Boldo and
    G. Melquiond, Emulation of FMA and correctly rounded sums: proved
    algorithms using rounding to odd, IEEE Trans. Computers 57(4), 2008):
    [x + y] itself if it is a float, and otherwise the one of the two floats
    around [x + y] whose integral significand is odd. [mul_add1_rn_emulated]
    uses it to emulate an FMA.

    It computes [s = RN(x + y)] and the exact error [e = (x + y) - s] with
    TwoSum. If [e = 0], the sum is the float [s]. Otherwise [x + y] is not a
    float, and [s] is one of its two neighbours; the other one is the next
    float from [s] on the side of [x + y]. Consecutive finite floats of one
    sign have consecutive bit patterns, so that neighbour is the pattern of
    [s] plus or minus one. The last bit of the pattern is the last bit of
    the canonical significand, so exactly one of the two neighbours has an
    odd pattern: [s] if its pattern is odd, the other one otherwise. *)

From Stdlib Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Round_odd Plus_error.
From Inari Require Import Model Encoding TwoSum StepUp.

Open Scope R_scope.

(** Flocq defines rounding to odd for formats where every number has a
    neighbour with an even significand, which holds as [53 > 1]. *)
#[local] Instance exists_NE_fexp64 : Exists_NE radix2 fexp64.
Proof. apply exists_NE_FLT. right. lia. Qed.

(** Rounding to odd in binary64 without overflow. *)
Local Notation RO := (round radix2 fexp64 Zrnd_odd).

(** ** Odd patterns *)

(** A float whose pattern [sign_bit sg + c] is odd and which is [z] rounded
    down or up is [z] rounded to odd: its canonical significand is
    [mant c], which has the parity of [c]. *)
Lemma Rnd_odd_bits :
  forall (sg : bool) c z,
  (0 <= c < 2047 * 2^52)%Z -> Z.even c = false ->
  B2R (from_bits (sign_bit sg + c)) = round radix2 fexp64 Zfloor z \/
  B2R (from_bits (sign_bit sg + c)) = round radix2 fexp64 Zceil z ->
  B2R (from_bits (sign_bit sg + c)) = RO z.
Proof.
intros sg c z Hc Hodd Hz.
assert (Fv : generic_format radix2 fexp64 (B2R (from_bits (sign_bit sg + c))))
  by apply generic_format_B2R.
destruct (from_bits_finite sg c Hc) as (_ & _ & Hv).
set (v := B2R (from_bits (sign_bit sg + c))) in *. clearbody v.
(* The implicit bit [2^52] of a normal float is even, so [mant c] has the
   parity of [c], and it is positive as [c <> 0]. *)
assert (Hm : (0 < mant c)%Z /\ Z.even (mant c) = false).
{ rewrite Zeven_mod in Hodd |- *. apply Z.eqb_neq in Hodd.
  destruct (split_52 c (proj1 Hc)) as (Hcs & _ & _).
  unfold mant. destruct (Z.eqb_spec (c / 2^52) 0).
  - split; [|apply Z.eqb_neq]; clear - Hc Hodd Hcs; zlia.
  - split; [|apply Z.eqb_neq]; clear - Hc Hodd Hcs; zlia. }
assert (Hmag : magnitude c <> 0).
{ unfold magnitude. apply Rgt_not_eq, F2R_gt_0. apply Hm. }
(* [expo c] is the canonical exponent of [magnitude c], since both give
   its ulp. *)
assert (Hcan : canonical radix2 fexp64 (Float radix2 (mant c) (expo c))).
{ unfold canonical. cbn [Fexp]. fold (magnitude c).
  apply bpow_inj with radix2.
  rewrite <- ulp_neq_0 by exact Hmag.
  rewrite ulp_magnitude by lia.
  reflexivity. }
apply (@Rnd_odd_pt_unique radix2 fexp64 _ _ z).
- split; [exact Fv|]. right. split.
  + destruct Hz as [H|H]; rewrite H;
      [left; apply round_DN_pt | right; apply round_UP_pt]; typeclasses eauto.
  + exists (Float radix2 (SpecFloat.cond_Zopp sg (mant c)) (expo c)).
    rewrite Hv. destruct sg; cbn [SpecFloat.cond_Zopp Fnum].
    * split; [rewrite F2R_Zopp; reflexivity|].
      split; [now apply canonical_opp|].
      rewrite Z.even_opp. apply Hm.
    * split; [reflexivity|]. split; [exact Hcan|]. apply Hm.
- exact (@round_odd_pt radix2 fexp64 _ _ z).
Qed.

(** ** [add_odd] *)

(** [add_odd x y] is [x + y] rounded to odd if [|x|, |y| < 2^1023] and
    [x + y] is finite, the hypotheses of [two_sum_err_correct]. *)
Theorem add_odd_correct :
  forall x y, is_finite x = true -> is_finite y = true ->
  Rabs (B2R x) < bpow radix2 1023 -> Rabs (B2R y) < bpow radix2 1023 ->
  is_finite (add x y) = true ->
  is_finite (Generic.add_odd x y) = true /\
  B2R (Generic.add_odd x y) = RO (B2R x + B2R y).
Proof.
intros x y Fx Fy Hx Hy Fs.
destruct (two_sum_err_correct x y Fx Fy Hx Hy Fs) as (Fe & He).
assert (Hs := add_B2R x y Fx Fy Fs).
unfold Generic.add_odd. cbv zeta.
set (z := B2R x + B2R y) in *.
set (s := add x y) in *.
set (e := Generic.two_sum_err x y s) in *.
clearbody s e.
unfold Model.eq, Model.gt.
rewrite Beqb_correct by first [exact Fe | reflexivity].
rewrite 2!Bltb_correct by first [exact Fe | exact Fs | reflexivity].
change (B2R zero) with 0.
destruct (Req_bool_spec (B2R e) 0) as [He0|He0]; cbn [negb andb].
{ (* [e = 0]: the sum is the float [s]. *)
  split; [exact Fs|].
  replace z with (B2R s) by lra.
  symmetry. apply (round_generic radix2 fexp64 Zrnd_odd), generic_format_B2R. }
(* [e <> 0]: [z] is not a float, and [s] is [z] rounded down or up. *)
assert (Nz : ~ generic_format radix2 fexp64 z).
{ intros Fz. apply He0. rewrite He, Hs, (round_generic radix2 fexp64 ZnearestE z Fz). ring. }
assert (Hz0 : z <> 0).
{ intros H. apply Nz. rewrite H. apply generic_format_0. }
(* A nonzero sum of floats does not round to zero. *)
assert (Hv0 : B2R s <> 0).
{ rewrite Hs. apply (round_plus_neq_0 radix2 fexp64 ZnearestE); [apply generic_format_B2R .. | exact Hz0]. }
assert (Hdn : B2R s < z -> B2R s = round radix2 fexp64 Zfloor z).
{ intros H. rewrite Hs in H |- *.
  destruct (round_DN_or_UP radix2 fexp64 ZnearestE z) as [H1|H1]; [exact H1|].
  exfalso. destruct (round_UP_pt radix2 fexp64 z) as (_ & H2 & _). lra. }
assert (Hup : z < B2R s -> B2R s = round radix2 fexp64 Zceil z).
{ intros H. rewrite Hs in H |- *.
  destruct (round_DN_or_UP radix2 fexp64 ZnearestE z) as [H1|H1]; [|exact H1].
  exfalso. destruct (round_DN_pt radix2 fexp64 z) as (_ & H2 & _). lra. }
destruct (to_bits_finite s Fs) as (c & Hc & Hb).
assert (Hv : B2R s = B2R (from_bits (sign_bit (Bsign s) + c)))
  by now rewrite <- Hb, from_to_bits.
(* The last bit of the pattern, as the sign bit [2^63] is even. *)
assert (Hland : Z.land (to_bits s) 1 = (c mod 2)%Z).
{ assert (H1 := Z.land_ones (to_bits s) 1).
  change (Z.ones 1) with 1%Z in H1. change (2^1)%Z with 2%Z in H1.
  rewrite H1 by lia. rewrite Hb. unfold sign_bit.
  destruct (Bsign s); clear - Hc; zlia. }
rewrite Hland, <- Zeven_mod.
destruct (Z.even c) eqn:Hev; cbn [andb].
2: { (* The pattern of [s] is odd: [s] is [z] rounded to odd. *)
  split; [exact Fs|].
  rewrite Hv. apply Rnd_odd_bits; [exact Hc | exact Hev |].
  rewrite <- Hv, Hs. apply (round_DN_or_UP radix2 fexp64 ZnearestE). }
(* The pattern of [s] is even: the result is the other neighbour of [z],
   whose pattern [c + 1] or [c - 1] is odd, and finite as the largest
   finite pattern [2047 * 2^52 - 1] is odd. *)
destruct (from_bits_finite (Bsign s) c Hc) as (_ & _ & Hm).
rewrite <- Hv in Hm.
destruct (magnitude_bounds c (proj1 Hc)) as ((Hm0 & _) & _).
assert (Hmpos : 0 < magnitude c).
{ destruct (Rle_lt_or_eq_dec _ _ Hm0) as [H|H]; [exact H|].
  exfalso. apply Hv0. rewrite Hm, <- H. destruct (Bsign s); ring. }
assert (Hc0 : c <> 0%Z) by (intros ->; rewrite magnitude_0 in Hmpos; lra).
destruct (proj1 (Z.even_spec c) Hev) as (k & Hk).
assert (Hc1 : (0 <= c + 1 < 2047 * 2^52)%Z) by (clear - Hc Hk Hc0; zlia).
assert (Hc2 : (0 <= c - 1 < 2047 * 2^52)%Z) by (clear - Hc Hk Hc0; zlia).
assert (Ho1 : Z.even (c + 1) = false) by (rewrite Z.even_add, Hev; reflexivity).
assert (Ho2 : Z.even (c - 1) = false) by (rewrite Z.even_sub, Hev; reflexivity).
(* The patterns next to [c] are the floats next to [magnitude c]. *)
assert (Hsucc := magnitude_succ c (proj1 Hc)).
assert (Hpred : magnitude (c - 1) = pred radix2 fexp64 (magnitude c)).
{ destruct (from_bits_finite false (c - 1) Hc2) as (_ & _ & R1).
  cbv beta iota in R1.
  pose proof (magnitude_succ (c - 1)) as H.
  replace (c - 1 + 1)%Z with c in H by ring.
  rewrite H by lia.
  rewrite (pred_succ radix2 fexp64); [reflexivity|].
  rewrite <- R1. apply generic_format_B2R. }
rewrite Hb.
destruct (Rtotal_order (B2R e) 0) as [Hen|[Hen|Hep]]; [|contradiction|].
- (* [z < s]: the result is [z] rounded down. *)
  assert (HU : B2R s = round radix2 fexp64 Zceil z) by (apply Hup; lra).
  rewrite (Rlt_bool_false 0 (B2R e)) by lra.
  destruct (Bsign s); cbv beta iota in Hm.
  + (* [s < 0]: increment the magnitude. *)
    rewrite (Rlt_bool_false 0 (B2R s)) by lra. cbn [Bool.eqb].
    rewrite <- Z.add_assoc.
    destruct (from_bits_finite true (c + 1) Hc1) as (F1 & _ & R1).
    cbv beta iota in R1.
    split; [exact F1|].
    apply Rnd_odd_bits; [exact Hc1 | exact Ho1 |]. left.
    rewrite R1, Hsucc, <- (pred_UP_eq_DN radix2 fexp64 z Nz), <- HU, Hm.
    rewrite pred_opp. reflexivity.
  + (* [s > 0]: decrement the magnitude. *)
    rewrite (Rlt_bool_true 0 (B2R s)) by lra. cbn [Bool.eqb].
    rewrite <- Z.add_sub_assoc.
    destruct (from_bits_finite false (c - 1) Hc2) as (F1 & _ & R1).
    cbv beta iota in R1.
    split; [exact F1|].
    apply Rnd_odd_bits; [exact Hc2 | exact Ho2 |]. left.
    rewrite R1, Hpred, <- Hm, HU.
    exact (pred_UP_eq_DN radix2 fexp64 z Nz).
- (* [s < z]: the result is [z] rounded up. *)
  assert (HD : B2R s = round radix2 fexp64 Zfloor z) by (apply Hdn; lra).
  rewrite (Rlt_bool_true 0 (B2R e)) by lra.
  destruct (Bsign s); cbv beta iota in Hm.
  + (* [s < 0]: decrement the magnitude. *)
    rewrite (Rlt_bool_false 0 (B2R s)) by lra. cbn [Bool.eqb].
    rewrite <- Z.add_sub_assoc.
    destruct (from_bits_finite true (c - 1) Hc2) as (F1 & _ & R1).
    cbv beta iota in R1.
    split; [exact F1|].
    apply Rnd_odd_bits; [exact Hc2 | exact Ho2 |]. right.
    rewrite R1, Hpred, <- (succ_DN_eq_UP radix2 fexp64 z Nz), <- HD, Hm.
    rewrite succ_opp. reflexivity.
  + (* [s > 0]: increment the magnitude. *)
    rewrite (Rlt_bool_true 0 (B2R s)) by lra. cbn [Bool.eqb].
    rewrite <- Z.add_assoc.
    destruct (from_bits_finite false (c + 1) Hc1) as (F1 & _ & R1).
    cbv beta iota in R1.
    split; [exact F1|].
    apply Rnd_odd_bits; [exact Hc1 | exact Ho1 |]. right.
    rewrite R1, Hsucc, <- Hm, HD.
    exact (succ_DN_eq_UP radix2 fexp64 z Nz).
Qed.
