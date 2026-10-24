(** * Stepping up a result rounded to nearest

    The fast paths compute [p = RN(z)] for an exact result [z], and its
    exact error [e = z - p] with an error-free transformation. Then [p] is
    [z] rounded toward +inf if [e <= 0], and the next float up if [e > 0].
    [step_up_rounds_up] proves this for a nonzero [p], including the sign
    of the result and overflow. The fast paths of [div_ru] and [sqrt1_ru]
    instead tell whether [p < z] from the sign of an exact remainder, and
    [step_up_rounds_up_iff] takes that as a hypothesis. *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Spec TwoSum AddRu.

Open Scope R_scope.

(** The sign bit of a finite nonzero float is the sign of its value. *)
Lemma Bsign_B2R :
  forall x : f64, is_finite x = true -> B2R x <> 0 ->
  Bsign x = Rlt_bool (B2R x) 0.
Proof.
intros [s|s| |s m e H] Fx Hx; try discriminate Fx.
- exfalso. now apply Hx.
- cbn [B2R Bsign]. destruct s.
  + symmetry. apply Rlt_bool_true. apply F2R_lt_0. cbn [Fnum SpecFloat.cond_Zopp]. lia.
  + symmetry. apply Rlt_bool_false. apply F2R_ge_0. cbn [Fnum SpecFloat.cond_Zopp]. lia.
Qed.

(** If [p = RN(z)] is nonzero and [up] is whether [p < z], then
    [if up { step_up(p) } else { p }] is [z] rounded toward +inf. *)
Theorem step_up_rounds_up_iff :
  forall z (p : f64) (up : bool),
  is_finite p = true -> B2R p = RN z -> B2R p <> 0 ->
  (up = true <-> B2R p < z) ->
  rounds_up_to z (if up then Generic.step_up p else p).
Proof.
intros z p up Fp Hp Hp0 Hup.
(* [p] has the sign of [z], as rounding is monotone and [RN 0 = 0]. *)
assert (Hsp : Bsign p = Rlt_bool z 0).
{ rewrite (Bsign_B2R p Fp Hp0).
  destruct (Rlt_bool_spec (B2R p) 0) as [Hn|Hn];
    destruct (Rlt_bool_spec z 0) as [Hz|Hz]; try reflexivity; exfalso.
  - apply (round_le radix2 fexp64 ZnearestE) in Hz; [|typeclasses eauto ..].
    rewrite round_0, <- Hp in Hz by typeclasses eauto. lra.
  - apply Rlt_le, (round_le radix2 fexp64 ZnearestE) in Hz;
      [|typeclasses eauto ..].
    rewrite round_0, <- Hp in Hz by typeclasses eauto. apply Hp0. lra. }
unfold rounds_up_to.
destruct up.
- (* [p] is below [z], so rounding up gives [succ p]. *)
  assert (Hpos : B2R p < z) by now apply Hup.
  rewrite step_up_Bsucc by exact Fp.
  assert (HU : RU z = succ radix2 fexp64 (B2R p)).
  { rewrite Hp. apply RU_RN_below. rewrite <- Hp. lra. }
  rewrite HU.
  generalize (@Bsucc_correct 53 1024 _ _ p Fp).
  change (SpecFloat.fexp 53 1024) with fexp64.
  destruct (Rlt_bool_spec (succ radix2 fexp64 (B2R p)) (bpow radix2 1024))
    as [Hlt|Hge].
  + (* [succ p] is finite and keeps the sign of [p], even if it is zero:
       [Bsucc] steps [-2^-1074] to [-0]. *)
    intros (HR & HF & HS).
    rewrite Rlt_bool_true.
    2: { apply Rabs_lt. split; [|exact Hlt].
         apply Rlt_le_trans with (B2R p).
         - exact (proj1 (Rabs_lt_inv _ _ (abs_B2R_lt_emax _ _ p))).
         - apply succ_ge_id. }
    split; [exact HR|]. split; [exact HF|].
    rewrite HS, (is_finite_strict_B2R _ _ p Hp0), Bool.andb_true_r.
    exact Hsp.
  + (* [succ p] overflows to +inf, and so does rounding up, as [z > 0]:
       rounding up a value [<= 0] gives at most 0. *)
    intros HB.
    rewrite Rlt_bool_false by (apply Rle_trans with (1 := Hge), Rle_abs).
    assert (Hz : 0 < z).
    { apply Rnot_le_lt. intros Hle.
      apply (round_le radix2 fexp64 Zceil) in Hle; [|typeclasses eauto ..].
      rewrite round_0, HU in Hle by typeclasses eauto.
      pose proof (bpow_gt_0 radix2 1024). lra. }
    rewrite HB, Rlt_bool_false by lra. reflexivity.
- (* [z <= p], so [p] is [z] rounded up. *)
  assert (Hnpos : z <= B2R p).
  { apply Rnot_lt_le. intros Hlt. apply Hup in Hlt. discriminate Hlt. }
  assert (HU : RU z = B2R p).
  { rewrite Hp. apply RU_RN_above. rewrite <- Hp. lra. }
  rewrite HU, Rlt_bool_true by apply abs_B2R_lt_emax.
  split; [reflexivity|]. split; [exact Fp | exact Hsp].
Qed.

(** If [p = RN(z)] is nonzero and [e = z - p] exactly, then
    [if e > 0 { step_up(p) } else { p }] is [z] rounded toward +inf. *)
Theorem step_up_rounds_up :
  forall z (p e : f64),
  is_finite p = true -> B2R p = RN z -> B2R p <> 0 ->
  is_finite e = true -> B2R e = z - B2R p ->
  rounds_up_to z (if gt e zero then Generic.step_up p else p).
Proof.
intros z p e Fp Hp Hp0 Fe He.
apply step_up_rounds_up_iff; [exact Fp | exact Hp | exact Hp0 |].
unfold gt.
rewrite Bltb_correct by first [exact Fe | reflexivity].
change (B2R zero) with 0.
rewrite He.
destruct (Rlt_bool_spec 0 (z - B2R p)) as [H|H]; split; intros H';
  first [reflexivity | lra | discriminate H'].
Qed.
