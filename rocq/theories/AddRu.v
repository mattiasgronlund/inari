(** * [add_ru] rounds toward +inf

    [add_ru] is IEEE 754 addition rounded toward +inf on both lanes, i.e.
    Flocq's [Bplus mode_UP], including the sign of a zero, overflow, the
    infinities and NaN. It never panics.

    The fast path, [add1_ru_fast], computes [s = RN(x + y)] and its exact
    error [e = (x + y) - s] with [two_sum_err], and steps [s] up to the next
    float if [e > 0]. If [x] or [y] is not finite, the sum does not depend
    on the rounding mode. The slow path, [add1_ru_slow], adds the
    significands as integers and rounds the sum itself. *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error.
From Inari Require Import Model Encoding Spec TwoSum Decompose RoundUpExact
  SumRoundUp.

Open Scope R_scope.

(** ** Rounding up from rounding to nearest *)

(** If [RN z < z], then [z] is not a float, [RN z] is the float below it
    and [RU z] the one above. *)
Lemma RU_RN_below :
  forall z, RN z < z -> RU z = succ radix2 fexp64 (RN z).
Proof.
intros z Hz.
assert (Fz : ~ generic_format radix2 fexp64 z).
{ intros Fz. rewrite (round_generic _ _ _ z Fz) in Hz. lra. }
destruct (round_DN_or_UP radix2 fexp64 ZnearestE z) as [Hd|Hu].
- rewrite Hd. symmetry. apply succ_DN_eq_UP; [typeclasses eauto | exact Fz].
- destruct (round_UP_pt radix2 fexp64 z) as (_ & Hle & _). lra.
Qed.

(** If [z <= RN z], then [RN z] is [RU z]. *)
Lemma RU_RN_above :
  forall z, z <= RN z -> RU z = RN z.
Proof.
intros z Hz.
destruct (generic_format_EM radix2 fexp64 z) as [Fz|Fz].
- rewrite (round_generic _ _ _ z Fz), (round_generic _ _ _ z Fz).
  reflexivity.
- assert (Hlt : z < RN z).
  { destruct Hz as [Hz|Hz]; [exact Hz|].
    exfalso. apply Fz. rewrite Hz. apply generic_format_round; typeclasses eauto. }
  destruct (round_DN_or_UP radix2 fexp64 ZnearestE z) as [Hd|Hu].
  + destruct (round_DN_pt radix2 fexp64 z) as (_ & Hle & _). lra.
  + symmetry. exact Hu.
Qed.

(** A float with the sign bit set is at most 0. *)
Lemma B2R_Bsign_true : forall x : f64, Bsign x = true -> B2R x <= 0.
Proof.
intros [s|s| |s m e H] Hs; cbn [B2R]; try apply Rle_refl.
cbn [Bsign] in Hs. subst s.
apply F2R_le_0. cbn [Fnum SpecFloat.cond_Zopp]. lia.
Qed.

(** ** The fast path *)

Theorem add1_ru_fast_correct :
  forall x y,
  snd (Generic.add1_ru_fast x y) = true ->
  fst (Generic.add1_ru_fast x y) = Bplus mode_UP x y.
Proof.
intros x y.
unfold Generic.add1_ru_fast. cbv beta zeta. cbn [fst snd].
rewrite !is_finite_eq.
destruct (is_finite x) eqn:Fx; destruct (is_finite y) eqn:Fy;
  cbn [andb orb negb].
2-4: (* [x] or [y] is +-inf or NaN: only the zero and finite cases of
        [Bplus] depend on the rounding mode. *)
  intros _; unfold add; destruct x, y; try discriminate; reflexivity.
intros H.
apply andb_prop in H as [H Fs]. apply andb_prop in H as [Ex Ey].
apply Z.leb_le in Ex, Ey.
assert (Hx : Rabs (B2R x) < bpow radix2 1023).
{ apply Rlt_le_trans with (1 := abs_B2R_lt_exponent x Fx). apply bpow_le. lia. }
assert (Hy : Rabs (B2R y) < bpow radix2 1023).
{ apply Rlt_le_trans with (1 := abs_B2R_lt_exponent y Fy). apply bpow_le. lia. }
destruct (two_sum_err_correct x y Fx Fy Hx Hy Fs) as (Fe & He).
assert (HS := add_B2R x y Fx Fy Fs).
(* The sign of [s]: that of [x + y], or of an exact zero sum. [s] is
   finite, so [Bplus_correct] is in its no-overflow case. *)
generalize (@Bplus_correct 53 1024 _ _ mode_NE x y Fx Fy).
change (Bplus mode_NE x y) with (add x y).
rewrite Rlt_bool_true.
2: { apply Rle_lt_trans with (2 := abs_B2R_lt_emax _ _ (add x y)).
     rewrite HS. apply Rle_refl. }
intros (_ & _ & HsS).
(* The value and sign of the specification, [Bplus mode_UP x y]. *)
generalize (@Bplus_correct 53 1024 _ _ mode_UP x y Fx Fy).
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_UP)) with RU.
set (s := add x y) in *. clearbody s.
set (e := Generic.two_sum_err x y s) in *. clearbody e.
unfold gt.
rewrite Bltb_correct by first [exact Fe | reflexivity].
change (B2R zero) with 0.
rewrite He.
destruct (Rlt_bool_spec 0 (B2R x + B2R y - B2R s)) as [Hpos|Hnpos].
- (* [e > 0]: [s] is below [x + y], so rounding up gives [succ s]. *)
  rewrite step_up_Bsucc by exact Fs.
  assert (HU : RU (B2R x + B2R y) = succ radix2 fexp64 (B2R s)).
  { rewrite HS. apply RU_RN_below. rewrite <- HS. lra. }
  (* [x + y = 0] would give [s = 0] and [e = 0]. *)
  assert (Hxy0 : B2R x + B2R y <> 0).
  { intros H0. rewrite H0, round_0 in HS by typeclasses eauto. lra. }
  generalize (@Bsucc_correct 53 1024 _ _ s Fs).
  change (SpecFloat.fexp 53 1024) with fexp64.
  destruct (Rlt_bool_spec (succ radix2 fexp64 (B2R s)) (bpow radix2 1024))
    as [Hlt|Hge].
  + (* [succ s] is finite: compare values and signs. *)
    intros (HR & HF & HSg).
    rewrite Rlt_bool_true.
    2: { rewrite HU. apply Rabs_lt. split; [|exact Hlt].
         apply Rlt_le_trans with (B2R s).
         - exact (proj1 (Rabs_lt_inv _ _ (abs_B2R_lt_emax _ _ s))).
         - apply succ_ge_id. }
    intros (HRu & HFu & HSu).
    apply B2R_Bsign_inj; [exact HF | exact HFu | rewrite HR, HRu, HU; reflexivity |].
    (* [s] is not zero, as [x + y] is not ([round_plus_neq_0]), so
       [Bsucc s] keeps its sign. *)
    assert (Hs0 : B2R s <> 0).
    { rewrite HS. apply round_plus_neq_0; try typeclasses eauto;
        first [apply generic_format_B2R | exact Hxy0]. }
    rewrite HSg, HSu, HsS, (is_finite_strict_B2R _ _ s Hs0).
    destruct (Rcompare_spec (B2R x + B2R y) 0) as [H0|H0|H0];
      [reflexivity | exact (False_ind _ (Hxy0 H0)) | reflexivity].
  + (* [succ s] overflows to +inf, and so does rounding up. *)
    intros HB.
    rewrite Rlt_bool_false.
    2: { rewrite HU. apply Rle_trans with (1 := Hge), Rle_abs. }
    intros (HO & Hsxy).
    (* [x + y > 0], as rounding up a sum [<= 0] gives at most 0, so [x] and
       [y] are not both negative. *)
    assert (Hxy : 0 < B2R x + B2R y).
    { apply Rnot_le_lt. intros Hle.
      apply (round_le radix2 fexp64 Zceil) in Hle; [|typeclasses eauto ..].
      rewrite round_0, HU in Hle by typeclasses eauto.
      pose proof (bpow_gt_0 radix2 1024). lra. }
    assert (Hsx : Bsign x = false).
    { destruct (Bsign x) eqn:Hsx; [|reflexivity].
      exfalso. symmetry in Hsxy.
      pose proof (B2R_Bsign_true x Hsx). pose proof (B2R_Bsign_true y Hsxy). lra. }
    apply B2SF_inj. rewrite HB, HO, Hsx. reflexivity.
- (* [e <= 0]: [s] is [x + y] rounded up, with the same sign in both modes. *)
  assert (HU : RU (B2R x + B2R y) = B2R s).
  { rewrite HS. apply RU_RN_above. rewrite <- HS. lra. }
  rewrite Rlt_bool_true by (rewrite HU; apply abs_B2R_lt_emax).
  intros (HRu & HFu & HSu).
  apply B2R_Bsign_inj; [exact Fs | exact HFu | rewrite HRu, HU; reflexivity |].
  rewrite HsS, HSu. reflexivity.
Qed.

(** ** The slow path *)

Theorem add1_ru_slow_correct :
  forall x y, Generic.add1_ru_slow x y = Some (Bplus mode_UP x y).
Proof.
intros x y.
unfold Generic.add1_ru_slow.
rewrite !is_finite_eq.
destruct (negb (is_finite x && is_finite y) || eq x zero || eq y zero) eqn:Hsp.
{ f_equal. now apply add_special. }
apply Bool.orb_false_elim in Hsp as [Hsp Hy0].
apply Bool.orb_false_elim in Hsp as [Hf Hx0].
apply Bool.negb_false_iff, andb_prop in Hf as [Fx Fy].
generalize (decompose_correct x Fx Hx0) (decompose_correct y Fy Hy0).
destruct (Generic.decompose x) as ((sx, mx), ex).
destruct (Generic.decompose y) as ((sy, my), ey).
intros (-> & Hmx & Hex & Hx) (-> & Hmy & Hey & Hy).
assert (HX : 0 < F2R (Float radix2 mx ex)) by (apply F2R_gt_0; simpl; lia).
assert (HY : 0 < F2R (Float radix2 my ey)) by (apply F2R_gt_0; simpl; lia).
generalize (sum_round_up_reduce (Bsign x) mx ex (Bsign y) my ey
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
cbv zeta. rewrite <- Hx, <- Hy.
generalize (@Bplus_correct 53 1024 _ _ mode_UP x y Fx Fy).
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_UP)) with RU.
intros HB [(H0 & ->) | (neg & m & e & sticky & Hpre & ->)].
- (* An exact cancellation gives +0, as [x] and [y] have opposite signs. *)
  rewrite H0, round_0, Rabs_R0, Rlt_bool_true, Rcompare_Eq in HB
    by first [reflexivity | apply bpow_gt_0 | typeclasses eauto].
  destruct HB as (HR & HF & HS).
  f_equal. apply B2R_Bsign_inj; [reflexivity | exact HF | now rewrite HR |].
  rewrite HS.
  revert H0. rewrite Hx, Hy.
  destruct (Bsign x), (Bsign y); unfold cond_Ropp; try reflexivity; lra.
- destruct (round_up_exact_correct neg m e sticky _ Hpre) as (r & -> & Hr).
  assert (Hv : B2R x + B2R y <> 0).
  { destruct Hpre as (Hm & _ & _ & _ & Hloc).
    assert (0 < F2R (Float radix2 m e)) by (apply F2R_gt_0; simpl; lia).
    intros H0. rewrite H0, Rabs_R0 in Hloc.
    destruct sticky; lra. }
  f_equal. unfold rounds_up_to in Hr.
  destruct Rlt_bool.
  + destruct Hr as (HR & HF & HS). destruct HB as (HR' & HF' & HS').
    apply B2R_Bsign_inj; [exact HF | exact HF' | congruence |].
    rewrite HS, HS'.
    destruct (Rcompare_spec (B2R x + B2R y) 0) as [H|H|H].
    * now apply Rlt_bool_true.
    * contradiction.
    * apply Rlt_bool_false. lra.
  + (* Overflow: [x] and [y] have the same sign, which the sum has too. *)
    destruct HB as (HO & Hsxy).
    apply B2SF_inj. rewrite Hr, HO. f_equal.
    rewrite Hx, Hy, <- Hsxy.
    destruct (Bsign x); unfold cond_Ropp.
    * apply Rlt_bool_true. lra.
    * apply Rlt_bool_false. lra.
Qed.

(** ** Both lanes *)

Theorem add_ru_correct :
  forall x y,
  Generic.add_ru x y =
    Some (Bplus mode_UP (fst x) (fst y), Bplus mode_UP (snd x) (snd y)).
Proof.
intros [x0 x1] [y0 y1].
(* Each lane is the fast path if it is valid, and the slow path if not. *)
assert (L : forall a b,
  (if snd (Generic.add1_ru_fast a b) then Some (fst (Generic.add1_ru_fast a b))
   else Generic.add1_ru_slow a b) = Some (Bplus mode_UP a b)).
{ intros a b.
  destruct (snd (Generic.add1_ru_fast a b)) eqn:Hok.
  - f_equal. now apply add1_ru_fast_correct.
  - apply add1_ru_slow_correct. }
generalize (L x0 y0) (L x1 y1).
unfold Generic.add_ru, Generic.lanewise2. cbn [fst snd].
destruct (Generic.add1_ru_fast x0 y0) as (r0, ok0).
destruct (Generic.add1_ru_fast x1 y1) as (r1, ok1).
cbn [fst snd].
intros H0 H1.
destruct ok0, ok1; cbn [andb];
  rewrite ?H0, ?H1; try injection H0 as ->; try injection H1 as ->; reflexivity.
Qed.
