(** * The cells of rounding to nearest

    The real numbers that round to nearest to an [f64] of the rules of
    the kernel's functions rounded to nearest: the [f64] itself
    ([near_exact]), the numbers within [|x| 2^-54] of a nonzero [x]
    ([near_x]), 1 and -1 ([near_one], [near_m_one]), the infinities
    ([near_inf], [near_ninf]), and +0 ([near_zero]), the symmetry of the
    rounding ([near_opp]), and its uniqueness at a nonzero number
    ([near_unique]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model NearF64.

Open Scope R_scope.

(** ** Helpers *)

(** The exponent of the format at a number of magnitude [k]. *)
Local Lemma cexp_at :
  forall r k, bpow radix2 (k - 1) <= Rabs r < bpow radix2 k ->
  cexp radix2 (FLT_exp (-1074) 53) r = Z.max (k - 53) (-1074).
Proof.
intros r k H. unfold cexp, FLT_exp. now rewrite (mag_unique radix2 r k H).
Qed.

(** A number nearer than half a gap to [m 2^e], at exponent [e], rounds
    to it. *)
Local Lemma near_imp :
  forall r m e, cexp radix2 (FLT_exp (-1074) 53) r = e ->
  Rabs (r - IZR m * bpow radix2 e) < bpow radix2 (e - 1) ->
  round radix2 (FLT_exp (-1074) 53) ZnearestE r = IZR m * bpow radix2 e.
Proof.
intros r m e Hc H.
unfold round, scaled_mantissa, F2R. rewrite Hc. cbn [Fnum Fexp].
rewrite (Znearest_imp _ _ m); [reflexivity |].
replace (r * bpow radix2 (- e) - IZR m)
  with ((r - IZR m * bpow radix2 e) * bpow radix2 (- e)).
2: { rewrite Rmult_minus_distr_r, Rmult_assoc, <- bpow_plus, Z.add_opp_diag_r.
     change (bpow radix2 0) with 1. ring. }
rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (- e))) by apply bpow_ge_0.
replace (/ 2) with (bpow radix2 (e - 1) * bpow radix2 (- e)).
2: { rewrite <- bpow_plus. replace (e - 1 + - e)%Z with (-1)%Z by ring. reflexivity. }
apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact H].
Qed.

(** The same with half a gap allowed, toward an even [m]: a tie at
    [(m + 1/2) 2^e] goes to the even [m], and one at [(m - 1/2) 2^e]
    goes from the odd [m - 1] up to [m]. *)
Local Lemma near_even :
  forall r m e, cexp radix2 (FLT_exp (-1074) 53) r = e ->
  Rabs (r - IZR m * bpow radix2 e) <= bpow radix2 (e - 1) -> Z.even m = true ->
  round radix2 (FLT_exp (-1074) 53) ZnearestE r = IZR m * bpow radix2 e.
Proof.
intros r m e Hc H Hm.
destruct (Rlt_le_dec (Rabs (r - IZR m * bpow radix2 e)) (bpow radix2 (e - 1))) as [Hl | Hg].
{ now apply near_imp. }
assert (Heq : Rabs (r - IZR m * bpow radix2 e) = bpow radix2 (e - 1)) by lra.
assert (Hb : bpow radix2 (e - 1) = / 2 * bpow radix2 e).
{ replace (e - 1)%Z with (-1 + e)%Z by ring. rewrite bpow_plus. reflexivity. }
assert (He : bpow radix2 e * bpow radix2 (- e) = 1).
{ rewrite <- bpow_plus, Z.add_opp_diag_r. reflexivity. }
unfold round, scaled_mantissa, F2R. rewrite Hc. cbn [Fnum Fexp].
f_equal. f_equal.
destruct (Rle_or_lt 0 (r - IZR m * bpow radix2 e)) as [H0 | H0].
- rewrite Rabs_pos_eq in Heq by exact H0.
  assert (Hr : r = (IZR m + / 2) * bpow radix2 e) by lra.
  rewrite Hr, Rmult_assoc, He, Rmult_1_r.
  unfold Znearest.
  rewrite (Zfloor_imp m) by (rewrite plus_IZR; lra).
  replace (IZR m + / 2 - IZR m) with (/ 2) by ring.
  rewrite Rcompare_Eq by reflexivity.
  cbv beta. rewrite Hm. reflexivity.
- rewrite Rabs_left in Heq by exact H0.
  assert (Hr : r = (IZR (m - 1) + / 2) * bpow radix2 e) by (rewrite minus_IZR; lra).
  rewrite Hr, Rmult_assoc, He, Rmult_1_r.
  unfold Znearest.
  rewrite (Zfloor_imp (m - 1)) by (rewrite plus_IZR; lra).
  replace (IZR (m - 1) + / 2 - IZR (m - 1)) with (/ 2) by ring.
  rewrite Rcompare_Eq by reflexivity.
  cbv beta. rewrite Z.even_sub, Hm. cbn [Z.even Bool.eqb negb].
  apply Zceil_imp. rewrite !minus_IZR. lra.
Qed.

(** Below the overflow threshold, [near_round] is the rounding of a
    finite [v] with its sign clause. *)
Local Lemma near_fin :
  forall r v, Rabs r < bpow radix2 1024 - bpow radix2 970 ->
  is_finite v = true -> B2R v = round radix2 (FLT_exp (-1074) 53) ZnearestE r ->
  (r <> 0 -> B2R v = 0 -> Bsign v = Rlt_bool r 0) -> near_round r v.
Proof.
intros r v Hr Hf Hv Hs. unfold near_round.
destruct (Rle_dec _ _) as [H | _]; [lra | auto].
Qed.

Local Lemma Rlt_bool_opp : forall r, r <> 0 -> Rlt_bool (- r) 0 = negb (Rlt_bool r 0).
Proof.
intros r Hr.
destruct (Rlt_bool_spec r 0); destruct (Rlt_bool_spec (- r) 0); try reflexivity; lra.
Qed.

(** The sign bit of a finite nonzero float is the sign of its value, as
    [StepUp.Bsign_B2R]. *)
Local Lemma sign_B2R :
  forall x : f64, is_finite x = true -> B2R x <> 0 ->
  Bsign x = Rlt_bool (B2R x) 0.
Proof.
intros [s|s| |s m e H] Fx Hx; try discriminate Fx.
- exfalso. now apply Hx.
- cbn [B2R Bsign]. destruct s.
  + symmetry. apply Rlt_bool_true. apply F2R_lt_0. cbn [Fnum SpecFloat.cond_Zopp]. lia.
  + symmetry. apply Rlt_bool_false. apply F2R_ge_0. cbn [Fnum SpecFloat.cond_Zopp]. lia.
Qed.

Local Lemma one_R : B2R DyadicExp.one = 1.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicExp.one) with (SpecFloat.S754_finite false 4503599627370496 (-52))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

(** ** The cells *)

Lemma near_exact : forall w, is_finite w = true -> near_round (B2R w) w.
Proof.
intros w Hw.
apply near_fin; [| exact Hw | | intros H1 H2; contradiction].
- pose proof (abs_B2R_le_emax_minus_prec 53 1024 eq_refl w) as H.
  assert (bpow radix2 970 < bpow radix2 971) by (apply bpow_lt; lia).
  change (1024 - 53)%Z with 971%Z in H. lra.
- symmetry. apply round_generic; [typeclasses eauto |]. apply generic_format_B2R.
Qed.

Lemma near_opp : forall r v, near_round r v -> near_round (- r) (opp v).
Proof.
intros r v. unfold near_round. rewrite Rabs_Ropp.
destruct (Rle_dec _ _) as [Hr | Hr]; intros H.
- subst v. unfold opp. cbn [Bopp]. f_equal. symmetry. apply Rlt_bool_opp.
  intros ->. rewrite Rabs_R0 in Hr.
  assert (bpow radix2 970 < bpow radix2 1024) by (apply bpow_lt; lia). lra.
- destruct H as (Hf & Hv & Hs). unfold opp. split; [| split].
  + now rewrite is_finite_Bopp.
  + rewrite B2R_Bopp, Hv. symmetry. apply round_NE_opp.
  + intros Hr0 Hv0. rewrite B2R_Bopp in Hv0.
    assert (Hr1 : r <> 0) by (intros ->; apply Hr0; apply Ropp_0).
    assert (Hv1 : B2R v = 0) by lra.
    rewrite Bsign_Bopp by (destruct v; easy).
    rewrite (Hs Hr1 Hv1). symmetry. now apply Rlt_bool_opp.
Qed.

(** [near_x] at a positive [x]. *)
Local Lemma near_x_pos :
  forall x r,
  is_finite x = true -> 0 < B2R x -> Rabs (r - B2R x) <= B2R x * bpow radix2 (-54) ->
  near_round r x.
Proof.
intros x r Hf HX Hr.
pose proof (abs_B2R_le_emax_minus_prec 53 1024 eq_refl x) as Hmax.
change (1024 - 53)%Z with 971%Z in Hmax.
pose proof (generic_format_B2R 53 1024 x) as HF.
change (SpecFloat.fexp 53 1024) with (FLT_exp (-1074) 53) in HF.
set (X := B2R x) in *.
rewrite Rabs_pos_eq in Hmax by lra.
apply Rabs_le_inv in Hr.
destruct (mag radix2 X) as [k Hk].
specialize (Hk (Rgt_not_eq _ _ HX)). rewrite Rabs_pos_eq in Hk by lra.
remember (Z.max (k - 53) (-1074)) as e eqn:He.
assert (HcX : cexp radix2 (FLT_exp (-1074) 53) X = e).
{ rewrite He. apply cexp_at. now rewrite Rabs_pos_eq by lra. }
(* [X = m 2^e], and the next float up, [X + 2^e], is at most [2^k]. *)
assert (HXm : X = IZR (Ztrunc (scaled_mantissa radix2 (FLT_exp (-1074) 53) X)) * bpow radix2 e).
{ unfold generic_format, F2R in HF. cbn [Fnum Fexp] in HF. now rewrite HcX in HF. }
set (m := Ztrunc _) in HXm.
assert (HU : X + bpow radix2 e <= bpow radix2 k).
{ rewrite <- HcX, <- ulp_neq_0 by lra.
  apply id_p_ulp_le_bpow; [exact HX | exact HF | lra]. }
(* The atoms of the linear arithmetic below: [B = 2^(k-54)]. *)
set (B := bpow radix2 (k - 54)).
assert (HB0 : 0 < B) by apply bpow_gt_0.
assert (Hk0 : bpow radix2 k = bpow radix2 54 * B).
{ unfold B. rewrite <- bpow_plus. f_equal. ring. }
assert (Hk1 : bpow radix2 (k - 1) = bpow radix2 53 * B).
{ unfold B. rewrite <- bpow_plus. f_equal. ring. }
assert (Hk2 : bpow radix2 (k - 1 - 1) = bpow radix2 52 * B).
{ unfold B. rewrite <- bpow_plus. f_equal. ring. }
change (bpow radix2 54) with 18014398509481984 in Hk0.
change (bpow radix2 53) with 9007199254740992 in Hk1.
change (bpow radix2 52) with 4503599627370496 in Hk2.
assert (HXB : X * bpow radix2 (-54) < B).
{ unfold B. replace (k - 54)%Z with (k + -54)%Z by ring. rewrite bpow_plus.
  apply Rmult_lt_compat_r; [apply bpow_gt_0 | lra]. }
assert (HBe : B <= bpow radix2 (e - 1)) by (apply bpow_le; lia).
assert (Hee : bpow radix2 (e - 1) <= bpow radix2 e) by (apply bpow_le; lia).
apply near_fin; [| exact Hf | | intros _ H0; fold X in H0; lra].
- (* [r] is at most [(2^1024 - 2^971) (1 + 2^-54)]. *)
  assert (HM : X * bpow radix2 (-54) <= (bpow radix2 1024 - bpow radix2 971) * bpow radix2 (-54)).
  { apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Hmax]. }
  assert (HC : bpow radix2 1024 - bpow radix2 971
      + (bpow radix2 1024 - bpow radix2 971) * bpow radix2 (-54)
      < bpow radix2 1024 - bpow radix2 970).
  { cbn [bpow radix_val radix2]. lra. }
  rewrite Rabs_pos_eq by lra. lra.
- fold X. symmetry.
  destruct (Rle_lt_dec (bpow radix2 (k - 1)) r) as [Hl | Hl].
  + (* The same binade as [X]. *)
    assert (Hc : cexp radix2 (FLT_exp (-1074) 53) r = e).
    { rewrite He. apply cexp_at. rewrite Rabs_pos_eq by lra. lra. }
    rewrite (near_imp r m e Hc); [now rewrite <- HXm |]. rewrite <- HXm.
    apply Rabs_lt. lra.
  + (* The binade below [X], so [X] is the power of 2 [2^(k-1)]. *)
    assert (Hc : cexp radix2 (FLT_exp (-1074) 53) r = Z.max (k - 1 - 53) (-1074)).
    { apply cexp_at. rewrite Rabs_pos_eq by lra. lra. }
    destruct (Z_le_dec (k - 53) (-1074)) as [Hs | Hs].
    * (* Subnormal: the gap is the same on both sides. *)
      rewrite Z.max_r in Hc by lia. rewrite Z.max_r in He by lia.
      assert (Hc' : cexp radix2 (FLT_exp (-1074) 53) r = e) by (rewrite He; exact Hc).
      rewrite (near_imp r m e Hc'); [now rewrite <- HXm |]. rewrite <- HXm.
      apply Rabs_lt. lra.
    * rewrite Z.max_l in Hc by lia. rewrite Z.max_l in He by lia.
      assert (He2 : bpow radix2 e = 2 * B).
      { rewrite He. unfold B. replace (k - 53)%Z with (1 + (k - 54))%Z by ring.
        now rewrite bpow_plus. }
      (* [m] is [2^52], since [m <= 2^52 - 1] puts [X] below [2^(k-1)] and
         [m >= 2^52 + 1] puts [r] above it. *)
      assert (Hm : m = 4503599627370496%Z).
      { destruct (Z_lt_le_dec m 4503599627370496) as [Hm | Hm].
        - assert (H1 : IZR m * B <= 4503599627370495 * B).
          { apply Rmult_le_compat_r; [lra |]. apply IZR_le. lia. }
          rewrite He2 in HXm. lra.
        - destruct (Z.eq_dec m 4503599627370496) as [-> | Hn]; [reflexivity |].
          assert (H1 : 4503599627370497 * B <= IZR m * B).
          { apply Rmult_le_compat_r; [lra |]. apply IZR_le. lia. }
          rewrite He2 in HXm. lra. }
      rewrite Hm, He2 in HXm.
      assert (HXk : X = bpow radix2 (k - 1)) by lra.
      rewrite HXk in Hr. rewrite <- bpow_plus in Hr.
      replace (k - 1 + -54)%Z with (k - 54 - 1)%Z in Hr by ring.
      replace (k - 1 - 53)%Z with (k - 54)%Z in Hc by ring.
      rewrite (near_even r 9007199254740992 (k - 54) Hc); [| | reflexivity].
      { fold B. lra. }
      fold B. apply Rabs_le. lra.
Qed.

(** The half-gaps around [x] are at least [|x| 2^-54], with equality
    only below a power of 2, whose tie goes to [x], whose significand is
    even. *)
Lemma near_x :
  forall x r,
  is_finite x = true -> B2R x <> 0 -> Rabs (r - B2R x) <= Rabs (B2R x) * bpow radix2 (-54) ->
  near_round r x.
Proof.
intros x r Hf H0 Hr.
destruct (Rlt_or_le 0 (B2R x)) as [Hp | Hn].
- apply near_x_pos; [exact Hf | exact Hp |].
  rewrite (Rabs_pos_eq (B2R x)) in Hr by lra. exact Hr.
- rewrite <- (Ropp_involutive r).
  replace x with (opp (opp x)) by apply Bopp_involutive.
  apply near_opp. apply near_x_pos.
  + unfold opp. now rewrite is_finite_Bopp.
  + unfold opp. rewrite B2R_Bopp. lra.
  + unfold opp. rewrite B2R_Bopp.
    replace (- r - - B2R x) with (- (r - B2R x)) by ring. rewrite Rabs_Ropp.
    rewrite (Rabs_left (B2R x)) in Hr by lra. exact Hr.
Qed.

Lemma near_one :
  forall r, 1 - bpow radix2 (-54) <= r <= 1 + bpow radix2 (-53) -> near_round r DyadicExp.one.
Proof.
intros r Hr.
assert (H54 : 0 < bpow radix2 (-54) < / 4) by (cbn [bpow radix_val radix2]; lra).
assert (H53 : 0 < bpow radix2 (-53) < / 4) by (cbn [bpow radix_val radix2]; lra).
apply near_fin; [| vm_compute; reflexivity | | rewrite one_R; intros _ H; lra].
- assert (HT : 2 < bpow radix2 1024 - bpow radix2 970) by (cbn [bpow radix_val radix2]; lra).
  rewrite Rabs_pos_eq by lra. lra.
- rewrite one_R. symmetry.
  destruct (Rlt_le_dec r 1) as [Hl | Hl].
  + (* In [[1/2, 1)], at exponent -53, the tie [1 - 2^-54] goes up. *)
    assert (Hc : cexp radix2 (FLT_exp (-1074) 53) r = (-53)%Z).
    { apply (cexp_at r 0). rewrite Rabs_pos_eq by lra.
      change (bpow radix2 (0 - 1)) with (/ 2). change (bpow radix2 0) with 1. lra. }
    assert (H1 : IZR 9007199254740992 * bpow radix2 (-53) = 1).
    { change (IZR 9007199254740992) with (bpow radix2 53). rewrite <- bpow_plus. reflexivity. }
    rewrite <- H1. apply near_even; [exact Hc | | reflexivity].
    rewrite H1. change (-53 - 1)%Z with (-54)%Z. apply Rabs_le. lra.
  + (* In [[1, 2)], at exponent -52, the tie [1 + 2^-53] goes down. *)
    assert (Hc : cexp radix2 (FLT_exp (-1074) 53) r = (-52)%Z).
    { apply (cexp_at r 1). rewrite Rabs_pos_eq by lra.
      change (bpow radix2 (1 - 1)) with 1. change (bpow radix2 1) with 2. lra. }
    assert (H1 : IZR 4503599627370496 * bpow radix2 (-52) = 1).
    { change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity. }
    rewrite <- H1. apply near_even; [exact Hc | | reflexivity].
    rewrite H1. change (-52 - 1)%Z with (-53)%Z. apply Rabs_le. lra.
Qed.

Lemma near_m_one :
  forall r, - (1 + bpow radix2 (-53)) <= r <= - (1 - bpow radix2 (-54)) ->
  near_round r DyadicExp.m_one.
Proof.
intros r Hr.
replace DyadicExp.m_one with (opp DyadicExp.one) by (apply B2SF_inj; vm_compute; reflexivity).
rewrite <- (Ropp_involutive r). apply near_opp. apply near_one. lra.
Qed.

Lemma near_inf : forall r, bpow radix2 1024 - bpow radix2 970 <= r -> near_round r infinity.
Proof.
intros r Hr. unfold near_round.
assert (H0 : 0 < bpow radix2 1024 - bpow radix2 970).
{ assert (bpow radix2 970 < bpow radix2 1024) by (apply bpow_lt; lia). lra. }
rewrite Rabs_pos_eq by lra.
destruct (Rle_dec _ _) as [_ | H]; [| lra].
rewrite Rlt_bool_false by lra. vm_compute. reflexivity.
Qed.

Lemma near_ninf :
  forall r, r <= - (bpow radix2 1024 - bpow radix2 970) -> near_round r DyadicExp.neg_infinity.
Proof.
intros r Hr. unfold near_round.
assert (H0 : 0 < bpow radix2 1024 - bpow radix2 970).
{ assert (bpow radix2 970 < bpow radix2 1024) by (apply bpow_lt; lia). lra. }
rewrite Rabs_left by lra.
destruct (Rle_dec _ _) as [_ | H]; [| lra].
rewrite Rlt_bool_true by lra. vm_compute. reflexivity.
Qed.

(** The tie at 2^-1075 goes to +0, whose significand is even. *)
Lemma near_zero : forall r, 0 < r <= bpow radix2 (-1075) -> near_round r zero.
Proof.
intros r [H0 H1].
assert (Hc : cexp radix2 (FLT_exp (-1074) 53) r = (-1074)%Z).
{ unfold cexp, FLT_exp. apply Z.max_r.
  assert (mag radix2 r <= -1074)%Z.
  { apply mag_le_bpow; [lra |]. rewrite Rabs_pos_eq by lra.
    apply Rle_lt_trans with (1 := H1). apply bpow_lt. lia. }
  lia. }
apply near_fin; [| reflexivity | |].
- assert (HT : 1 < bpow radix2 1024 - bpow radix2 970) by (cbn [bpow radix_val radix2]; lra).
  assert (bpow radix2 (-1075) < 1) by (cbn [bpow radix_val radix2]; lra).
  rewrite Rabs_pos_eq by lra. lra.
- change (B2R zero) with 0. symmetry.
  transitivity (IZR 0 * bpow radix2 (-1074)); [| ring].
  apply near_even; [exact Hc | | reflexivity].
  change (-1074 - 1)%Z with (-1075)%Z. rewrite Rmult_0_l, Rminus_0_r.
  rewrite Rabs_pos_eq by lra. exact H1.
- intros _ _. cbn [zero Bsign]. symmetry. apply Rlt_bool_false. lra.
Qed.

(** A nonzero number has one rounding: at 0, either zero is one. *)
Lemma near_unique : forall r v w, r <> 0 -> near_round r v -> near_round r w -> v = w.
Proof.
intros r v w Hr. unfold near_round.
destruct (Rle_dec _ _) as [_ | _]; intros Hv Hw.
- now rewrite Hv, Hw.
- destruct Hv as (Fv & Rv & Sv), Hw as (Fw & Rw & Sw).
  assert (HR : B2R v = B2R w) by now rewrite Rv, Rw.
  apply B2R_Bsign_inj; [exact Fv | exact Fw | exact HR |].
  destruct (Req_dec (B2R v) 0) as [Z | NZ].
  + rewrite (Sv Hr Z), (Sw Hr) by congruence. reflexivity.
  + rewrite (sign_B2R v Fv NZ), (sign_B2R w Fw) by congruence. now rewrite HR.
Qed.
