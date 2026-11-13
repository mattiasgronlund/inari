(** * The rounding tests of the fast paths

    [Fast.round_dir] and [Fast.round_near] of [Model.v] decide the
    rounding of a real [y 2^e] from an unevaluated sum [h + l] of two
    [f64]s with [h = RN(h + l)], [1/2 < h < 2] and [|y - (h + l)| <=
    2^-68], by comparisons of [l] with bounds that depend only on [h],
    and scale it by [2^e] ([round_dir_correct], [round_near_correct]).
    The fast paths of [exp], [exp2] and [exp10] use both, and their
    hypotheses leave room for the fast paths of other functions to reuse
    them. [two_prod_err_fma_eq] shows that the
    error of an exact product is the same [f64] with and without an FMA,
    which lets [Model.v] pass [false] for [HAS_FMA] to the fast paths. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error.
From Inari Require Import Model Mpfr Encoding TwoSum TwoProduct DyDriver NearF64 NearCells.
From Inari Require StepUp DyExpRules.

Open Scope R_scope.

Local Notation G := (generic_format radix2 fexp64).
Local Notation succ64 := (succ radix2 fexp64).
Local Notation pred64 := (pred radix2 fexp64).

(** ** Powers of two, scaling and the neighbours of [h] *)

(** The bits that [scale] builds are those of [2^e] for a normal [2^e]. *)
Lemma pow2_bits :
  forall e, (-1022 <= e <= 1023)%Z ->
  is_finite (from_bits (Z.shiftl ((e + 1023) mod 2^64) 52 mod 2^64)%Z) = true /\
  B2R (from_bits (Z.shiftl ((e + 1023) mod 2^64) 52 mod 2^64)%Z) = bpow radix2 e.
Proof.
intros e He.
rewrite (Z.mod_small (e + 1023)) by (simpl Z.pow; lia).
rewrite Z.shiftl_mul_pow2 by lia.
rewrite Z.mod_small by (simpl Z.pow; lia).
destruct (from_bits_finite false ((e + 1023) * 2^52)) as (Fp & _ & Rp);
  [simpl Z.pow; lia|].
cbn [sign_bit] in Fp, Rp. rewrite Z.add_0_l in Fp, Rp.
split; [exact Fp|]. rewrite Rp.
replace ((e + 1023) * 2^52)%Z with ((e + 1023) * 2^52 + 0)%Z by ring.
rewrite magnitude_split by (simpl Z.pow; lia).
rewrite (proj2 (Z.eqb_neq (e + 1023) 0)) by lia.
replace (Z.max (e + 1023) 1 - 1075)%Z with (e - 52)%Z by lia.
unfold F2R; cbn [Fnum Fexp].
rewrite Z.add_0_l, (IZR_Zpower radix2) by easy.
rewrite <- bpow_plus. f_equal. ring.
Qed.

Lemma mag_ge_0 : forall x, / 2 <= Rabs x -> (0 <= mag radix2 x)%Z.
Proof.
intros x Hx. apply mag_ge_bpow. change (bpow radix2 (0 - 1)) with (/ 2). exact Hx.
Qed.

(** [x 2^e] is a float with [x], for [|x| >= 1/2] and [e >= -1021]. *)
Lemma format_shift :
  forall x e, G x -> / 2 <= Rabs x -> (-1021 <= e)%Z -> G (x * bpow radix2 e).
Proof.
intros x e Fx Hx He.
apply mult_bpow_exact_FLT; [exact Fx|].
pose proof (mag_ge_0 x Hx). lia.
Qed.

(** [scale r e] is [r 2^e] exactly, for [1/2 <= r <= 2]. *)
Lemma scale_correct :
  forall r e, is_finite r = true -> / 2 <= B2R r <= 2 -> (-1021 <= e <= 1022)%Z ->
  is_finite (Fast.scale r e) = true /\ B2R (Fast.scale r e) = B2R r * bpow radix2 e.
Proof.
intros r e Fr Hr He.
destruct (pow2_bits e ltac:(lia)) as (Fp & Rp).
assert (Fm : G (B2R r * bpow radix2 e)).
{ apply format_shift; [apply generic_format_B2R | rewrite Rabs_pos_eq; lra | lia]. }
assert (HB : 0 < bpow radix2 e <= bpow radix2 1022)
  by (split; [apply bpow_gt_0 | apply bpow_le; lia]).
assert (HT : 2 * bpow radix2 1022 < bpow radix2 1024) by (cbn [bpow radix_val radix2]; lra).
unfold Fast.scale, mul.
set (p := from_bits _) in *.
generalize (@Bmult_correct 53 1024 _ _ mode_NE r p).
rewrite Rp.
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE)) with RN.
rewrite (round_generic _ _ _ _ Fm).
rewrite Rlt_bool_true.
2: { rewrite Rabs_pos_eq by (apply Rmult_le_pos; lra).
     apply Rle_lt_trans with (2 := HT).
     apply Rmult_le_compat; lra. }
intros (HR & HF & _).
split; [rewrite HF, Fr, Fp; reflexivity | exact HR].
Qed.

(** Adding one to the bits of [h] steps to [succ h]. *)
Lemma bits_succ :
  forall h, is_finite h = true -> 0 < B2R h < 2 ->
  is_finite (from_bits (to_bits h + 1)) = true /\
  B2R (from_bits (to_bits h + 1)) = succ64 (B2R h).
Proof.
intros h Fh Hh.
destruct (to_bits_finite h Fh) as (c & Hc & Hb).
assert (Sh : Bsign h = false).
{ rewrite StepUp.Bsign_B2R by (assumption || lra). apply Rlt_bool_false. lra. }
destruct (from_bits_finite (Bsign h) c Hc) as (_ & _ & Hx).
rewrite <- Hb, from_to_bits, Sh in Hx. cbv beta iota in Hx.
rewrite Hb, Sh. cbn [sign_bit]. rewrite Z.add_0_l.
(* [h < 2] keeps the biased exponent of [h] below 2046. *)
destruct (magnitude_bounds c (proj1 Hc)) as (_ & Hge).
assert (H2 : bpow radix2 1 <= bpow radix2 1023) by (apply bpow_le; lia).
change (bpow radix2 1) with 2 in H2.
assert (Hc2 : (c + 1 < 2047 * 2^52)%Z).
{ destruct (Z_lt_le_dec (c / 2^52) 2046) as [Hl|Hl]; [zlia|].
  exfalso.
  assert (H3 : bpow radix2 1023 <= bpow radix2 (c / 2^52 - 1023)) by (apply bpow_le; lia).
  specialize (Hge ltac:(lia)). lra. }
destruct (from_bits_finite false (c + 1)) as (F1 & _ & R1); [lia|].
cbn [sign_bit] in F1, R1. rewrite Z.add_0_l in F1, R1. cbv beta iota in R1.
split; [exact F1|].
rewrite R1, Hx. apply magnitude_succ. lia.
Qed.

(** Subtracting one from the bits of [h > 0] steps to [pred h]. *)
Lemma bits_pred :
  forall h, is_finite h = true -> 0 < B2R h ->
  is_finite (from_bits (to_bits h - 1)) = true /\
  B2R (from_bits (to_bits h - 1)) = pred64 (B2R h).
Proof.
intros h Fh Hh.
destruct (to_bits_finite h Fh) as (c & Hc & Hb).
assert (Sh : Bsign h = false).
{ rewrite StepUp.Bsign_B2R by (assumption || lra). apply Rlt_bool_false. lra. }
destruct (from_bits_finite (Bsign h) c Hc) as (_ & _ & Hx).
rewrite <- Hb, from_to_bits, Sh in Hx. cbv beta iota in Hx.
assert (Hc0 : c <> 0%Z) by (intros ->; rewrite magnitude_0 in Hx; lra).
rewrite Hb, Sh. cbn [sign_bit]. rewrite Z.add_0_l.
destruct (from_bits_finite false (c - 1)) as (F1 & _ & R1); [lia|].
cbn [sign_bit] in F1, R1. rewrite Z.add_0_l in F1, R1. cbv beta iota in R1.
split; [exact F1|].
pose proof (magnitude_succ (c - 1) ltac:(lia)) as Hs.
replace (c - 1 + 1)%Z with c in Hs by ring.
rewrite R1, Hx, Hs, pred_succ.
all: try reflexivity.
all: try (rewrite <- R1; apply generic_format_B2R).
all: try exact _.
Qed.

(** The gaps around [x] in [[1/2, 2)]: [2^-53] below 1 and [2^-52] from 1 on. *)
Lemma succ_hi : forall x, 1 <= x < 2 -> succ64 x = x + bpow radix2 (-52).
Proof.
intros x Hx. rewrite succ_eq_pos by lra. f_equal.
rewrite ulp_neq_0 by lra. unfold cexp.
rewrite (mag_unique_pos radix2 x 1); [reflexivity|].
change (bpow radix2 (1 - 1)) with 1. change (bpow radix2 1) with 2. lra.
Qed.

Lemma succ_lo : forall x, / 2 <= x < 1 -> succ64 x = x + bpow radix2 (-53).
Proof.
intros x Hx. rewrite succ_eq_pos by lra. f_equal.
rewrite ulp_neq_0 by lra. unfold cexp.
rewrite (mag_unique_pos radix2 x 0); [reflexivity|].
change (bpow radix2 (0 - 1)) with (/ 2). change (bpow radix2 0) with 1. lra.
Qed.

Lemma format_half : G (/ 2).
Proof.
change (/ 2) with (bpow radix2 (-1)). apply generic_format_FLT_bpow; [easy | lia].
Qed.

Lemma format_one : G 1.
Proof.
change 1 with (bpow radix2 0). apply generic_format_FLT_bpow; [easy | lia].
Qed.

Lemma format_two : G 2.
Proof.
change 2 with (bpow radix2 1). apply generic_format_FLT_bpow; [easy | lia].
Qed.

Lemma pred_hi : forall x, G x -> 1 < x < 2 -> pred64 x = x - bpow radix2 (-52).
Proof.
intros x Fx Hx.
assert (P1 : 1 <= pred64 x) by (apply (pred_ge_gt radix2 fexp64); [exact format_one | exact Fx | lra]).
pose proof (pred_le_id radix2 fexp64 x) as P2.
pose proof (succ_pred radix2 fexp64 x Fx) as P3.
rewrite succ_hi in P3 by lra. lra.
Qed.

Lemma pred_lo : forall x, G x -> / 2 < x <= 1 -> pred64 x = x - bpow radix2 (-53).
Proof.
intros x Fx Hx.
assert (P1 : / 2 <= pred64 x) by (apply (pred_ge_gt radix2 fexp64); [exact format_half | exact Fx | lra]).
pose proof (pred_lt_id radix2 fexp64 x ltac:(lra)) as P2.
pose proof (succ_pred radix2 fexp64 x Fx) as P3.
rewrite succ_lo in P3 by lra. lra.
Qed.

(** The neighbours of [x] stay in [[1/2, 2]]. *)
Lemma succ_le_2 : forall x, G x -> x < 2 -> succ64 x <= 2.
Proof. intros x Fx Hx. apply (succ_le_lt radix2 fexp64); [exact Fx | exact format_two | exact Hx]. Qed.

Lemma pred_ge_half : forall x, G x -> / 2 < x -> / 2 <= pred64 x.
Proof. intros x Fx Hx. apply (pred_ge_gt radix2 fexp64); [exact format_half | exact Fx | exact Hx]. Qed.

(** [succ] and [pred] commute with scaling by [2^e] from [1/2] on. The
    shift lemma for [pred] needs [e >= -1020 - mag x], which fails at [e =
    -1021] for [x < 1], so [pred] goes through [succ]. *)
Lemma succ_shift :
  forall x e, / 2 <= x -> (-1021 <= e)%Z ->
  succ64 (x * bpow radix2 e) = succ64 x * bpow radix2 e.
Proof.
intros x e Hx He.
pose proof (mag_ge_0 x ltac:(rewrite Rabs_pos_eq; lra)).
apply succ_FLT_exact_shift_pos; [lra | lia | lia].
Qed.

Lemma pred_shift :
  forall x e, G x -> / 2 < x -> (-1021 <= e)%Z ->
  pred64 (x * bpow radix2 e) = pred64 x * bpow radix2 e.
Proof.
intros x e Fx Hx He.
pose proof (pred_ge_half x Fx Hx) as P1.
assert (Fp : G (pred64 x)) by (apply (generic_format_pred radix2 fexp64); exact Fx).
rewrite <- (succ_pred radix2 fexp64 x Fx) at 1.
rewrite <- (succ_shift (pred64 x) e P1 He).
apply (pred_succ radix2 fexp64).
apply format_shift; [exact Fp | rewrite Rabs_pos_eq; lra | exact He].
Qed.

(** A real strictly between the midpoints around a float [x > 0] rounds
    to [x] to nearest. *)
Lemma rn_between :
  forall x r, G x -> 0 < x ->
  (pred64 x + x) / 2 < r < (x + succ64 x) / 2 ->
  RN r = x.
Proof.
intros x r Fx Hx Hr.
pose proof (succ_gt_id radix2 fexp64 x ltac:(lra)) as S1.
pose proof (pred_lt_id radix2 fexp64 x ltac:(lra)) as P1.
destruct (Rtotal_order r x) as [Hlt | [Heq | Hgt]].
- assert (Fp : G (pred64 x)) by (apply (generic_format_pred radix2 fexp64); exact Fx).
  assert (HD : round radix2 fexp64 Zfloor r = pred64 x).
  { apply (round_DN_eq radix2 fexp64); [exact Fp|]. rewrite (succ_pred radix2 fexp64) by exact Fx. lra. }
  assert (HU : round radix2 fexp64 Zceil r = x).
  { apply (round_UP_eq radix2 fexp64); [exact Fx|]. lra. }
  rewrite <- HU. apply (round_N_eq_UP radix2 fexp64). rewrite HD, HU. lra.
- subst r. apply round_generic; [typeclasses eauto | exact Fx].
- assert (Fs : G (succ64 x)) by (apply (generic_format_succ radix2 fexp64); exact Fx).
  assert (HD : round radix2 fexp64 Zfloor r = x).
  { apply (round_DN_eq radix2 fexp64); [exact Fx | lra]. }
  assert (HU : round radix2 fexp64 Zceil r = succ64 x).
  { apply (round_UP_eq radix2 fexp64); [exact Fs|]. rewrite (pred_succ radix2 fexp64) by exact Fx. lra. }
  rewrite <- HD. apply (round_N_eq_DN radix2 fexp64). rewrite HD, HU. lra.
Qed.

(** ** The literals of [Fast] *)

Lemma err_R : B2R Fast.err = bpow radix2 (-68).
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF Fast.err) with (SpecFloat.S754_finite false 4503599627370496 (-120))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

Lemma near1_R : B2R Fast.near1 = bpow radix2 (-53) - bpow radix2 (-68).
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF Fast.near1) with (SpecFloat.S754_finite false 9006924376834048 (-106))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
(* [(2^53 - 2^38) 2^-106] *)
replace (bpow radix2 (-53)) with (bpow radix2 53 * bpow radix2 (-106))
  by (rewrite <- bpow_plus; reflexivity).
replace (bpow radix2 (-68)) with (bpow radix2 38 * bpow radix2 (-106))
  by (rewrite <- bpow_plus; reflexivity).
change (bpow radix2 53) with (IZR 9007199254740992).
change (bpow radix2 38) with (IZR 274877906944).
lra.
Qed.

Lemma near0_R : B2R Fast.near0 = bpow radix2 (-54) - bpow radix2 (-68).
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF Fast.near0) with (SpecFloat.S754_finite false 9006649498927104 (-107))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
(* [(2^53 - 2^39) 2^-107] *)
replace (bpow radix2 (-54)) with (bpow radix2 53 * bpow radix2 (-107))
  by (rewrite <- bpow_plus; reflexivity).
replace (bpow radix2 (-68)) with (bpow radix2 39 * bpow radix2 (-107))
  by (rewrite <- bpow_plus; reflexivity).
change (bpow radix2 53) with (IZR 9007199254740992).
change (bpow radix2 39) with (IZR 549755813888).
lra.
Qed.

Lemma one_R : B2R Fast.one = 1.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF Fast.one) with (SpecFloat.S754_finite false 4503599627370496 (-52))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

(** The comparisons of finite floats as comparisons of reals. *)
Lemma gt_true :
  forall x y, is_finite x = true -> is_finite y = true -> gt x y = true -> B2R y < B2R x.
Proof.
intros x y Fx Fy H. unfold gt in H. rewrite Bltb_correct in H by assumption.
destruct (Rlt_bool_spec (B2R y) (B2R x)); [assumption | discriminate].
Qed.

Lemma gt_false :
  forall x y, is_finite x = true -> is_finite y = true -> gt x y = false -> B2R x <= B2R y.
Proof.
intros x y Fx Fy H. unfold gt in H. rewrite Bltb_correct in H by assumption.
destruct (Rlt_bool_spec (B2R y) (B2R x)); [discriminate | assumption].
Qed.

Lemma ge_false :
  forall x y, is_finite x = true -> is_finite y = true -> ge x y = false -> B2R x < B2R y.
Proof.
intros x y Fx Fy H. unfold ge in H. rewrite Bleb_correct in H by assumption.
destruct (Rle_bool_spec (B2R y) (B2R x)); [discriminate | assumption].
Qed.

Lemma ge_true :
  forall x y, is_finite x = true -> is_finite y = true -> ge x y = true -> B2R y <= B2R x.
Proof.
intros x y Fx Fy H. unfold ge in H. rewrite Bleb_correct in H by assumption.
destruct (Rle_bool_spec (B2R y) (B2R x)); [assumption | discriminate].
Qed.

(** ** What [h = RN(h + l)] says about [l] *)

(** [|l|] is at most half the gap to each neighbour of [h], and each gap
    is at least [2^-53]. *)
Lemma low_bounds :
  forall h l : f64, is_finite h = true -> B2R h = RN (B2R h + B2R l) -> / 2 < B2R h < 2 ->
  B2R l <= (succ64 (B2R h) - B2R h) / 2 /\
  - B2R l <= (B2R h - pred64 (B2R h)) / 2 /\
  bpow radix2 (-53) <= succ64 (B2R h) - B2R h /\
  bpow radix2 (-53) <= B2R h - pred64 (B2R h).
Proof.
intros h l Fh Hrn Hh.
assert (Fx : G (B2R h)) by apply generic_format_B2R.
pose proof (round_N_pt radix2 fexp64 (fun z => negb (Z.even z)) (B2R h + B2R l)) as HN.
rewrite <- Hrn in HN. destruct HN as (_ & HN).
assert (Fs : G (succ64 (B2R h))) by (apply (generic_format_succ radix2 fexp64); exact Fx).
assert (Fp : G (pred64 (B2R h))) by (apply (generic_format_pred radix2 fexp64); exact Fx).
pose proof (HN _ Fs) as N1. pose proof (HN _ Fp) as N2.
pose proof (succ_gt_id radix2 fexp64 (B2R h) ltac:(lra)) as S1.
pose proof (pred_lt_id radix2 fexp64 (B2R h) ltac:(lra)) as P1.
assert (H52 : bpow radix2 (-53) <= bpow radix2 (-52)) by (apply bpow_le; lia).
split; [|split; [|split]].
- revert N1. unfold Rabs. destruct (Rcase_abs _); destruct (Rcase_abs _); intros; lra.
- revert N2. unfold Rabs. destruct (Rcase_abs _); destruct (Rcase_abs _); intros; lra.
- destruct (Rle_lt_dec 1 (B2R h)).
  + rewrite succ_hi by lra. lra.
  + rewrite succ_lo by lra. lra.
- destruct (Rlt_le_dec 1 (B2R h)).
  + rewrite pred_hi by (assumption || lra). lra.
  + rewrite pred_lo by (assumption || lra). lra.
Qed.

(** ** The signs of zeros *)

(** A finite float with its sign bit set is at most 0. *)
Lemma sign_le_0 : forall a : f64, is_finite a = true -> Bsign a = true -> B2R a <= 0.
Proof.
intros a Fa Sa.
destruct (Req_dec (B2R a) 0) as [Z|Z]; [lra|].
rewrite StepUp.Bsign_B2R in Sa by assumption.
destruct (Rlt_bool_spec (B2R a) 0); [lra | discriminate].
Qed.

(** A finite float with its sign bit clear is at least 0. *)
Lemma sign_ge_0 : forall a : f64, is_finite a = true -> Bsign a = false -> 0 <= B2R a.
Proof.
intros a Fa Sa.
destruct (Req_dec (B2R a) 0) as [Z|Z]; [lra|].
rewrite StepUp.Bsign_B2R in Sa by assumption.
destruct (Rlt_bool_spec (B2R a) 0); [discriminate | lra].
Qed.

(** A sum of finite floats that rounds to 0 is 0 (Flocq's
    [round_plus_eq_0]: such a sum is a float if it is small). *)
Lemma RN_plus_eq_0 : forall a b : f64, RN (B2R a + B2R b) = 0 -> B2R a + B2R b = 0.
Proof.
intros a b H.
apply (@round_plus_eq_0 radix2 fexp64 _ _ ZnearestE _);
  [apply generic_format_B2R | apply generic_format_B2R | exact H].
Qed.

(** In [mode_NE], a sum of floats is [-0] only if its first operand is a
    finite [-0], since an exact zero sum gets the sign bit only when both
    operands have it. *)
Lemma add_neg_zero :
  forall a b, is_finite (add a b) = true -> B2R (add a b) = 0 -> Bsign (add a b) = true ->
  is_finite a = true /\ B2R a = 0 /\ Bsign a = true.
Proof.
intros a b F Z S.
assert (Fab : is_finite a = true /\ is_finite b = true).
{ revert F. unfold add.
  destruct a as [sa|sa| |sa ma ea Ha], b as [sb|sb| |sb mb eb Hb];
    try (intros; split; reflexivity); try destruct sa; try destruct sb;
    intros F; simpl in F; discriminate F. }
destruct Fab as (Fa & Fb).
generalize (@Bplus_correct 53 1024 _ _ mode_NE a b Fa Fb).
destruct (Rlt_bool _ _).
- intros (HR & _ & HS).
  change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE)) with RN in HR.
  unfold add in Z, S. rewrite HR in Z. rewrite HS in S.
  pose proof (RN_plus_eq_0 a b Z) as E.
  rewrite Rcompare_Eq in S by exact E.
  apply andb_prop in S as [Sa Sb].
  pose proof (sign_le_0 a Fa Sa). pose proof (sign_le_0 b Fb Sb).
  split; [exact Fa|]. split; [lra | exact Sa].
- intros (HO & _). exfalso. revert F HO. unfold add.
  destruct (Bplus mode_NE a b); intros F HO; discriminate.
Qed.

(** In [mode_NE], a difference of floats is [-0] only if it subtracts a
    finite [+0]: an exact zero difference gets the sign bit only from a
    [-0] minus a [+0]. *)
Lemma sub_neg_zero :
  forall a b, is_finite (sub a b) = true -> B2R (sub a b) = 0 -> Bsign (sub a b) = true ->
  is_finite b = true /\ B2R b = 0.
Proof.
intros a b F Z S.
assert (Fab : is_finite a = true /\ is_finite b = true).
{ revert F. unfold sub.
  destruct a as [sa|sa| |sa ma ea Ha], b as [sb|sb| |sb mb eb Hb];
    try (intros; split; reflexivity); try destruct sa; try destruct sb;
    intros F; simpl in F; discriminate F. }
destruct Fab as (Fa & Fb).
generalize (@Bminus_correct 53 1024 _ _ mode_NE a b Fa Fb).
destruct (Rlt_bool _ _).
- intros (HR & _ & HS).
  change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE)) with RN in HR.
  unfold sub in Z, S. rewrite HR in Z. rewrite HS in S.
  assert (E : B2R a - B2R b = 0).
  { unfold Rminus in Z |- *. rewrite <- B2R_Bopp in Z |- *. apply RN_plus_eq_0. exact Z. }
  rewrite Rcompare_Eq in S by exact E.
  apply andb_prop in S as [Sa Sb]. apply Bool.negb_true_iff in Sb.
  pose proof (sign_le_0 a Fa Sa). pose proof (sign_ge_0 b Fb Sb).
  split; [exact Fb | lra].
- intros (HO & _). exfalso. revert F HO. unfold sub.
  destruct (Bminus mode_NE a b); intros F HO; discriminate.
Qed.

(** With an FMA, a zero error of [p = x y] is [+0]: [x y] and [-p] have
    opposite signs, and an exact zero sum of terms of opposite signs is
    [+0] in [mode_NE]. *)
Lemma fma_err_zero_sign :
  forall x y, is_finite x = true -> is_finite y = true ->
  is_finite (mul x y) = true -> B2R (mul x y) <> 0 ->
  B2R x * B2R y - B2R (mul x y) = 0 ->
  Bsign (Generic.two_prod_err true x y (mul x y)) = false.
Proof.
intros x y Fx Fy Fp Hp0 Z.
set (p := mul x y) in *. clearbody p.
assert (Fo : is_finite (opp p) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fp).
assert (Hx : B2R x <> 0) by (intros H; rewrite H in Z; lra).
assert (Hy : B2R y <> 0) by (intros H; rewrite H in Z; lra).
assert (Xs : B2R x < 0 \/ 0 < B2R x)
  by (destruct (Rtotal_order (B2R x) 0) as [?|[?|?]]; [left | contradiction | right]; assumption).
assert (Ys : B2R y < 0 \/ 0 < B2R y)
  by (destruct (Rtotal_order (B2R y) 0) as [?|[?|?]]; [left | contradiction | right]; assumption).
assert (Sp : Bsign p = Rlt_bool (B2R x * B2R y) 0)
  by (rewrite StepUp.Bsign_B2R by assumption; f_equal; lra).
unfold Generic.two_prod_err, mul_add.
generalize (@Bfma_correct 53 1024 _ _ mode_NE x y (opp p) Fx Fy Fo). cbv zeta.
replace (B2R (opp p)) with (- B2R p) by (unfold opp; symmetry; apply B2R_Bopp).
replace (B2R x * B2R y + - B2R p) with 0 by lra.
rewrite round_0, Rabs_R0, Rlt_bool_true by (typeclasses eauto || apply bpow_gt_0).
intros (_ & _ & HS). rewrite HS, Rcompare_Eq by reflexivity.
unfold Bfma_szero, opp. rewrite Bsign_Bopp by (destruct p; easy).
rewrite Sp, (StepUp.Bsign_B2R x), (StepUp.Bsign_B2R y) by assumption.
destruct Xs as [X|X]; destruct Ys as [Y|Y].
- rewrite (Rlt_bool_true _ _ X), (Rlt_bool_true _ _ Y), Rlt_bool_false by nra. reflexivity.
- rewrite (Rlt_bool_true _ _ X), (Rlt_bool_false _ _ (Rlt_le _ _ Y)), Rlt_bool_true by nra.
  reflexivity.
- rewrite (Rlt_bool_false _ _ (Rlt_le _ _ X)), (Rlt_bool_true _ _ Y), Rlt_bool_true by nra.
  reflexivity.
- rewrite (Rlt_bool_false _ _ (Rlt_le _ _ X)), (Rlt_bool_false _ _ (Rlt_le _ _ Y)),
    Rlt_bool_false by nra.
  reflexivity.
Qed.

(** Without an FMA, a zero error of [p = x y] is [+0]: by [add_neg_zero]
    a [-0] would come from the first subtraction [xh yh - p], which by
    [sub_neg_zero] needs [p = 0]. *)
Lemma dekker_err_zero_sign :
  forall x y,
  is_finite (Generic.two_prod_err false x y (mul x y)) = true ->
  B2R (Generic.two_prod_err false x y (mul x y)) = 0 -> B2R (mul x y) <> 0 ->
  Bsign (Generic.two_prod_err false x y (mul x y)) = false.
Proof.
intros x y F Z Hp0.
destruct (Bsign _) eqn:S; [exfalso | reflexivity].
revert F Z S. unfold Generic.two_prod_err. cbv iota.
destruct (Generic.split x) as (xh, xl). destruct (Generic.split y) as (yh, yl).
intros F Z S.
destruct (add_neg_zero _ _ F Z S) as (F3 & Z3 & S3).
destruct (add_neg_zero _ _ F3 Z3 S3) as (F2 & Z2 & S2).
destruct (add_neg_zero _ _ F2 Z2 S2) as (F1 & Z1 & S1).
destruct (sub_neg_zero _ _ F1 Z1 S1) as (_ & Zp).
exact (Hp0 Zp).
Qed.

(** ** The theorems *)

(** The error of an exact product is the same [f64], [+0] if it is
    zero, whether [Generic.two_prod_err] uses an FMA or Dekker's product. *)
Theorem two_prod_err_fma_eq :
  forall x y, is_finite x = true -> is_finite y = true ->
  Generic.two_prod_is_exact true x y (mul x y) = true ->
  Generic.two_prod_is_exact false x y (mul x y) = true ->
  Generic.two_prod_err true x y (mul x y) = Generic.two_prod_err false x y (mul x y).
Proof.
intros x y Fx Fy E1 E0.
destruct (two_prod_err_correct true x y Fx Fy E1) as (Fp & _ & Hp0 & F1 & R1).
destruct (two_prod_err_correct false x y Fx Fy E0) as (_ & _ & _ & F0 & R0).
(* Both are [x y - p] exactly, so they are the same float up to the sign
   of a zero, which is [+] for both. *)
apply B2R_Bsign_inj; [exact F1 | exact F0 | rewrite R1, R0; reflexivity |].
destruct (Req_dec (B2R x * B2R y - B2R (mul x y)) 0) as [Z|Z].
- rewrite (fma_err_zero_sign x y Fx Fy Fp Hp0 Z).
  rewrite (dekker_err_zero_sign x y F0 ltac:(rewrite R0; exact Z) Hp0).
  reflexivity.
- rewrite (StepUp.Bsign_B2R _ F1), (StepUp.Bsign_B2R _ F0) by (rewrite ?R1, ?R0; exact Z).
  rewrite R1, R0. reflexivity.
Qed.

(** ** The step from [h] by the sign bit of [l] *)

(** For a finite [err >= 0], the three outcomes of the comparisons in
    [dir_step_eq]: [l > err] with the sign bit of [l] clear, [l < -err]
    with it set, or [|l| <= err] and neither. *)
Local Lemma dir_step_cases :
  forall l err : f64, is_finite err = true -> 0 <= B2R err ->
  (gt (fabs l) err = true /\ gt l err = true /\ Z.shiftr (to_bits l) 63 = 0%Z) \/
  (gt (fabs l) err = true /\ gt l err = false /\ lt l (opp err) = true /\
   Z.shiftr (to_bits l) 63 = 1%Z) \/
  (gt (fabs l) err = false /\ gt l err = false /\ lt l (opp err) = false).
Proof.
intros l err Fe Pe.
destruct (is_finite l) eqn:Fl.
- (* Bit 63 of a finite [l] is its sign, as its other bits are below
     [2047 * 2^52 < 2^63]. *)
  assert (Hs : Z.shiftr (to_bits l) 63 = Z.b2z (Bsign l)).
  { destruct (to_bits_finite l Fl) as (c & Hc & Hb).
    rewrite Hb, Z.shiftr_div_pow2 by lia. unfold sign_bit.
    simpl Z.pow in Hc |- *.
    destruct (Bsign l); cbn [Z.b2z].
    - symmetry. apply Z.div_unique with (r := c); lia.
    - apply Z.div_small. lia. }
  assert (Ga : gt (fabs l) err = Rlt_bool (B2R err) (Rabs (B2R l))).
  { unfold gt, fabs. rewrite Bltb_correct by (rewrite ?is_finite_Babs; assumption).
    rewrite B2R_Babs. reflexivity. }
  assert (Gl : gt l err = Rlt_bool (B2R err) (B2R l))
    by (unfold gt; apply Bltb_correct; assumption).
  assert (Ll : lt l (opp err) = Rlt_bool (B2R l) (- B2R err)).
  { unfold lt, opp. rewrite Bltb_correct by (rewrite ?is_finite_Bopp; assumption).
    rewrite B2R_Bopp. reflexivity. }
  rewrite Ga, Gl, Ll, Hs.
  destruct (Rlt_bool_spec (B2R err) (Rabs (B2R l))) as [A|A].
  + (* [|l| > err >= 0], so the sign of [l] decides. *)
    destruct (Bsign l) eqn:Sl.
    * pose proof (sign_le_0 l Fl Sl) as N. rewrite Rabs_left1 in A by exact N.
      right; left. rewrite Rlt_bool_false, Rlt_bool_true by lra.
      repeat split.
    * pose proof (sign_ge_0 l Fl Sl) as N. rewrite Rabs_pos_eq in A by exact N.
      left. rewrite Rlt_bool_true by lra.
      repeat split.
  + (* [-err <= l <= err]. *)
    pose proof (Rabs_le_inv _ _ A) as N.
    right; right. rewrite !Rlt_bool_false by lra.
    repeat split.
- destruct l as [s|s| |s m ex Hb]; try discriminate Fl.
  + (* [l = +-inf] is beyond every finite [err] and [-err]. *)
    destruct s; [right; left | left];
      destruct err as [se|se| |se me ee Hbe]; try discriminate Fe;
      repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity.
  + (* Every comparison with a NaN is false. *)
    right; right.
    destruct err as [se|se| |se me ee Hbe]; try discriminate Fe;
      repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity.
Qed.

(** For [err >= 0], the step from [h] that [Fast.round_dir] and
    [Fast.round_dir_err] take where [|l| > err], to the bits of [h] plus
    [up] less the sign bit of [l], is the one that the comparisons
    [l > err] and [l < -err] choose, and both fail on the same [l]. *)
Lemma dir_step_eq :
  forall (h l err : f64) (e : Z) (up : bool),
  is_finite err = true -> 0 <= B2R err ->
  (if gt (fabs l) err
   then Some (Fast.scale (from_bits (to_bits h + Z.b2z up - Z.shiftr (to_bits l) 63)) e)
   else None) =
  (if gt l err then Some (Fast.scale (if up then from_bits (to_bits h + 1) else h) e)
   else if lt l (opp err) then Some (Fast.scale (if up then h else from_bits (to_bits h - 1)) e)
   else None).
Proof.
intros h l err e up Fe Pe.
destruct (dir_step_cases l err Fe Pe) as [(A & B & C) | [(A & B & C & D) | (A & B & C)]].
- (* [l > err]: the bits of [h] plus [up]. *)
  rewrite A, B, C. cbv beta iota. destruct up.
  + change (Z.b2z true) with 1%Z. rewrite Z.sub_0_r. reflexivity.
  + change (Z.b2z false) with 0%Z. rewrite Z.sub_0_r, Z.add_0_r, from_to_bits.
    reflexivity.
- (* [l < -err]: the bits of [h] plus [up] less 1. *)
  rewrite A, B, C, D. cbv beta iota. destruct up.
  + change (Z.b2z true) with 1%Z. rewrite Z.add_simpl_r, from_to_bits. reflexivity.
  + change (Z.b2z false) with 0%Z. rewrite Z.add_0_r. reflexivity.
- rewrite A, B, C. reflexivity.
Qed.

(** [Fast.round_dir] is the test by the comparisons [l > 2^-68] and
    [l < -2^-68]. *)
Lemma round_dir_eq :
  forall h l e up,
  Fast.round_dir h l e up =
  if gt l Fast.err then Some (Fast.scale (if up then from_bits (to_bits h + 1) else h) e)
  else if lt l (opp Fast.err) then
    Some (Fast.scale (if up then h else from_bits (to_bits h - 1)) e)
  else None.
Proof.
intros h l e up. unfold Fast.round_dir.
apply dir_step_eq; [reflexivity|]. rewrite err_R. apply bpow_ge_0.
Qed.

(** If [|y - (h + l)| <= 2^-68], with [h] the rounding of [h + l] to
    nearest between 1/2 and 2, then where [round_dir] returns, it returns
    [y 2^e] rounded toward +inf if [up] and toward -inf otherwise. *)
Theorem round_dir_correct :
  forall h l e up v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < B2R h < 2 -> (-1021 <= e <= 1022)%Z ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  Fast.round_dir h l e up = Some v ->
  rounds up (y * bpow radix2 e) v.
Proof.
intros h l e up v y Fh Fl Hrn Hh He Hy Hv.
destruct (low_bounds h l Fh Hrn Hh) as (U1 & U2 & Gs & Gp).
assert (Fx : G (B2R h)) by apply generic_format_B2R.
assert (HM : bpow radix2 (-68) < bpow radix2 (-53) / 2) by (cbn [bpow radix_val radix2]; lra).
assert (HE : 0 < bpow radix2 e) by apply bpow_gt_0.
apply Rabs_le_inv in Hy.
assert (Fe : is_finite Fast.err = true) by reflexivity.
assert (Fo : is_finite (opp Fast.err) = true) by reflexivity.
rewrite round_dir_eq in Hv.
destruct (gt l Fast.err) eqn:G1.
- (* [l > 2^-68]: [h < y < succ h]. *)
  pose proof (gt_true l Fast.err Fl Fe G1) as L1. rewrite err_R in L1.
  injection Hv as Hv. subst v.
  pose proof (succ_le_2 (B2R h) Fx (proj2 Hh)) as S2.
  pose proof (succ_gt_id radix2 fexp64 (B2R h) ltac:(lra)) as S1.
  destruct (bits_succ h Fh ltac:(lra)) as (Fs & Rs).
  destruct (scale_correct h e Fh ltac:(lra) He) as (Flo & Rlo).
  destruct (scale_correct _ e Fs ltac:(rewrite Rs; lra) He) as (Fhi & Rhi).
  assert (Hs : B2R (Fast.scale (from_bits (to_bits h + 1)) e) =
               succ radix2 (SpecFloat.fexp 53 1024) (B2R (Fast.scale h e))).
  { change (SpecFloat.fexp 53 1024) with fexp64.
    rewrite Rhi, Rlo, Rs, succ_shift by (lra || lia). reflexivity. }
  assert (Hb : B2R (Fast.scale h e) < y * bpow radix2 e <
               B2R (Fast.scale (from_bits (to_bits h + 1)) e)).
  { rewrite Rlo, Rhi, Rs. split; apply Rmult_lt_compat_r; lra. }
  destruct up;
    [exact (DyExpRules.rnd_bracket _ _ true _ Flo Fhi Hs Hb)
    |exact (DyExpRules.rnd_bracket _ _ false _ Flo Fhi Hs Hb)].
- destruct (lt l (opp Fast.err)) eqn:G2; [|discriminate].
  (* [l < -2^-68]: [pred h < y < h]. *)
  pose proof (DyExpRules.lt_R l (opp Fast.err) Fl Fo G2) as L1.
  unfold opp in L1. rewrite B2R_Bopp, err_R in L1.
  injection Hv as Hv. subst v.
  pose proof (pred_ge_half (B2R h) Fx (proj1 Hh)) as P2.
  pose proof (pred_lt_id radix2 fexp64 (B2R h) ltac:(lra)) as P1.
  destruct (bits_pred h Fh ltac:(lra)) as (Fp & Rp).
  destruct (scale_correct _ e Fp ltac:(rewrite Rp; lra) He) as (Flo & Rlo).
  destruct (scale_correct h e Fh ltac:(lra) He) as (Fhi & Rhi).
  assert (Hs : B2R (Fast.scale h e) =
               succ radix2 (SpecFloat.fexp 53 1024)
                 (B2R (Fast.scale (from_bits (to_bits h - 1)) e))).
  { change (SpecFloat.fexp 53 1024) with fexp64.
    rewrite Rhi, Rlo, Rp, succ_shift by (lra || lia).
    rewrite (succ_pred radix2 fexp64) by exact Fx. reflexivity. }
  assert (Hb : B2R (Fast.scale (from_bits (to_bits h - 1)) e) < y * bpow radix2 e <
               B2R (Fast.scale h e)).
  { rewrite Rlo, Rhi, Rp. split; apply Rmult_lt_compat_r; lra. }
  destruct up;
    [exact (DyExpRules.rnd_bracket _ _ true _ Flo Fhi Hs Hb)
    |exact (DyExpRules.rnd_bracket _ _ false _ Flo Fhi Hs Hb)].
Qed.

(** The same rounded to nearest, ties to even, as [near_round] says. *)
Theorem round_near_correct :
  forall h l e v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < B2R h < 2 -> (-1021 <= e <= 1022)%Z ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  Fast.round_near h l e = Some v ->
  near_round (y * bpow radix2 e) v.
Proof.
intros h l e v y Fh Fl Hrn Hh He Hy Hv.
assert (Fx : G (B2R h)) by apply generic_format_B2R.
assert (Fo : is_finite Fast.one = true) by reflexivity.
assert (HP : bpow radix2 (-52) = 2 * bpow radix2 (-53) /\
             bpow radix2 (-53) = 2 * bpow radix2 (-54))
  by (cbn [bpow radix_val radix2]; split; lra).
apply Rabs_le_inv in Hy.
unfold Fast.round_near in Hv. cbv zeta in Hv.
destruct (lt l _ && gt l _) eqn:HC; [|discriminate].
injection Hv as Hv. subst v.
apply andb_prop in HC as [C1 C2].
(* Above: from 1 on, the gap to [succ h] is [2^-52] and [l < 2^-53 -
   2^-68]; below 1, it is [2^-53] and [l < 2^-54 - 2^-68]. *)
assert (HA : y < (B2R h + succ64 (B2R h)) / 2).
{ destruct (ge h Fast.one) eqn:G1.
  - pose proof (DyExpRules.lt_R l Fast.near1 Fl eq_refl C1) as L1. rewrite near1_R in L1.
    pose proof (ge_true h Fast.one Fh Fo G1) as H1. rewrite one_R in H1.
    rewrite succ_hi by lra. lra.
  - pose proof (DyExpRules.lt_R l Fast.near0 Fl eq_refl C1) as L1. rewrite near0_R in L1.
    pose proof (ge_false h Fast.one Fh Fo G1) as H1. rewrite one_R in H1.
    rewrite succ_lo by lra. lra. }
(* Below: above 1, the gap to [pred h] is [2^-52] and [l > -(2^-53 -
   2^-68)]; from 1 down, it is [2^-53] and [l > -(2^-54 - 2^-68)]. *)
assert (HB : (pred64 (B2R h) + B2R h) / 2 < y).
{ destruct (gt h Fast.one) eqn:G2.
  - pose proof (gt_true l (opp Fast.near1) Fl eq_refl C2) as L1.
    unfold opp in L1. rewrite B2R_Bopp, near1_R in L1.
    pose proof (gt_true h Fast.one Fh Fo G2) as H1. rewrite one_R in H1.
    rewrite pred_hi by (assumption || lra). lra.
  - pose proof (gt_true l (opp Fast.near0) Fl eq_refl C2) as L1.
    unfold opp in L1. rewrite B2R_Bopp, near0_R in L1.
    pose proof (gt_false h Fast.one Fh Fo G2) as H1. rewrite one_R in H1.
    rewrite pred_lo by (assumption || lra). lra. }
destruct (scale_correct h e Fh ltac:(lra) He) as (Fv & Rv).
pose proof (succ_le_2 (B2R h) Fx (proj2 Hh)) as S2.
pose proof (pred_ge_half (B2R h) Fx (proj1 Hh)) as P2.
assert (HE : 0 < bpow radix2 e) by apply bpow_gt_0.
assert (HE2 : bpow radix2 e <= bpow radix2 1022) by (apply bpow_le; lia).
assert (HT : 2 * bpow radix2 1022 < bpow radix2 1024 - bpow radix2 970)
  by (cbn [bpow radix_val radix2]; lra).
assert (Hy0 : 0 < y * bpow radix2 e) by (apply Rmult_lt_0_compat; lra).
unfold near_round.
destruct (Rle_dec _ _) as [HO|_].
{ (* [y 2^e < 2 * 2^1022] is below the overflow threshold. *)
  exfalso. rewrite Rabs_pos_eq in HO by lra.
  assert (y * bpow radix2 e <= 2 * bpow radix2 1022) by (apply Rmult_le_compat; lra).
  lra. }
split; [exact Fv|]. split.
- rewrite Rv. symmetry. apply rn_between.
  + apply format_shift; [exact Fx | rewrite Rabs_pos_eq; lra | lia].
  + apply Rmult_lt_0_compat; lra.
  + (* The midpoints around [h 2^e] are those around [h], times [2^e]. *)
    rewrite succ_shift, pred_shift by (assumption || lra || lia).
    split.
    * replace ((pred64 (B2R h) * bpow radix2 e + B2R h * bpow radix2 e) / 2)
        with ((pred64 (B2R h) + B2R h) / 2 * bpow radix2 e) by field.
      apply Rmult_lt_compat_r; lra.
    * replace ((B2R h * bpow radix2 e + succ64 (B2R h) * bpow radix2 e) / 2)
        with ((B2R h + succ64 (B2R h)) / 2 * bpow radix2 e) by field.
      apply Rmult_lt_compat_r; lra.
- intros _ H0. rewrite Rv in H0.
  assert (0 < B2R h * bpow radix2 e) by (apply Rmult_lt_0_compat; lra). lra.
Qed.
