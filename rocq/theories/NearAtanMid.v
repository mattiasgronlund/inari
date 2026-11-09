(** * [atan] at a midpoint of the subnormal [f64]s rounded to nearest

    Below 2^-1021 the [f64]s are the multiples of 2^-1074, and the
    midpoints between them the odd multiples of 2^-1075. At such a
    midpoint [M = f + 2^-1075], with [f] the [f64] toward zero from it,
    [atan M] lies in [(f, M)], as [atan_tiny_real] of [DyAtanTiny.v] puts
    it at or above [M - M^3/3] and [M^3/3 < 2^-3000] is less than
    2^-1075, so [atan M] rounds to nearest to [f] ([near_atan_mid]), and
    the same holds below 0 by the oddness of [atan]
    ([near_atan_mid_neg]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model NearF64 NearCells DyAtanTiny.

Open Scope R_scope.

(** ** Helpers *)

(** Below 2^-1021 the exponent of the format is -1074. *)
Local Lemma cexp_sub :
  forall r, r <> 0 -> Rabs r < bpow radix2 (-1021) ->
  cexp radix2 (FLT_exp (-1074) 53) r = (-1074)%Z.
Proof.
intros r H0 H1. unfold cexp, FLT_exp. apply Z.max_r.
assert (mag radix2 r <= -1021)%Z by now apply mag_le_bpow.
lia.
Qed.

(** A number nearer than half a gap to [m 2^e], at exponent [e], rounds
    to it, as [near_imp] of [NearCells.v], which is local there. *)
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

(** A finite [f64] of sign bit 0 is at least 0. *)
Local Lemma B2R_ge_0 : forall f : f64, is_finite f = true -> Bsign f = false -> 0 <= B2R f.
Proof.
intros [s|s| |s m e H] Hf Hs; try discriminate Hf.
- apply Rle_refl.
- cbn [Bsign] in Hs. subst s. cbn [B2R]. apply F2R_ge_0. cbn [Fnum SpecFloat.cond_Zopp]. lia.
Qed.

(** ** The rule *)

(** At the midpoint [M = f + 2^-1075] above a finite [f64] [f] of sign
    bit 0, below 2^-1021, [atan M] rounds to nearest to [f]. *)
Lemma near_atan_mid :
  forall (f : f64) (M : R), is_finite f = true -> Bsign f = false ->
  M = B2R f + bpow radix2 (-1075) -> M < bpow radix2 (-1021) ->
  near_round (atan M) f.
Proof.
intros f M Hf Hs HM HT.
pose proof (B2R_ge_0 f Hf Hs) as HF0.
set (F := B2R f) in *.
set (B := bpow radix2 (-1075)) in *.
assert (HB0 : 0 < B) by apply bpow_gt_0.
assert (HM0 : 0 < M) by lra.
(* The constants, with the [bpow]s as atoms of [lra]. *)
assert (HTB : bpow radix2 (-1021) < bpow radix2 (-26)) by (apply bpow_lt; lia).
assert (HT1 : bpow radix2 (-1021) < 1) by (cbn [bpow radix_val radix2]; lra).
assert (HTO : 1 < bpow radix2 1024 - bpow radix2 970) by (cbn [bpow radix_val radix2]; lra).
(* [M^3/3 < 2^-1075]: [M^3 <= 2^-3063]. *)
assert (H3 : M ^ 3 / 3 < B).
{ assert (Hp : M ^ 3 <= bpow radix2 (-1021) ^ 3) by (apply pow_incr; lra).
  assert (Hc : bpow radix2 (-1021) ^ 3 = bpow radix2 (-3063)).
  { cbn [pow]. rewrite Rmult_1_r, <- !bpow_plus. reflexivity. }
  assert (Hl : bpow radix2 (-3063) <= B) by (apply bpow_le; lia).
  lra. }
assert (Hw : 0 < M < bpow radix2 (-26)) by lra.
destruct (atan_tiny_real M Hw) as [Hlo Hhi].
(* So [f < atan M < f + 2^-1075]. *)
assert (Hlo' : F < atan M) by lra.
assert (Hhi' : atan M < F + B) by lra.
assert (Ha0 : 0 < atan M) by lra.
unfold near_round.
destruct (Rle_dec _ _) as [Hr | _].
{ exfalso. rewrite Rabs_pos_eq in Hr by lra. lra. }
split; [exact Hf | split].
- (* [f = m 2^-1074], and [atan M] is within 2^-1075 of it. *)
  assert (Hc : cexp radix2 (FLT_exp (-1074) 53) (atan M) = (-1074)%Z).
  { apply cexp_sub; [lra |]. rewrite Rabs_pos_eq by lra. lra. }
  assert (Hm : exists m, F = IZR m * bpow radix2 (-1074)).
  { destruct (Req_dec F 0) as [H0 | H0].
    - exists 0%Z. rewrite H0. ring.
    - pose proof (generic_format_B2R 53 1024 f) as HG.
      change (SpecFloat.fexp 53 1024) with (FLT_exp (-1074) 53) in HG.
      fold F in HG.
      assert (HcF : cexp radix2 (FLT_exp (-1074) 53) F = (-1074)%Z).
      { apply cexp_sub; [exact H0 |]. rewrite Rabs_pos_eq by lra. lra. }
      unfold generic_format, F2R in HG. cbn [Fnum Fexp] in HG. rewrite HcF in HG.
      eexists. exact HG. }
  destruct Hm as [m Hm].
  fold F. rewrite Hm. symmetry. apply near_imp; [exact Hc |].
  rewrite <- Hm. change (-1074 - 1)%Z with (-1075)%Z. fold B.
  rewrite Rabs_pos_eq by lra. lra.
- (* [atan M > 0], and [f] has sign bit 0. *)
  intros _ _. rewrite Hs. symmetry. apply Rlt_bool_false. lra.
Qed.

(** The same below 0: at the midpoint [M = f - 2^-1075] below a finite
    [f64] [f] of sign bit 1, above -2^-1021, [atan M] rounds to nearest
    to [f], since [atan M = - atan (- M)] and [- M] is the midpoint above
    [- f]. *)
Lemma near_atan_mid_neg :
  forall (f : f64) (M : R), is_finite f = true -> Bsign f = true ->
  M = B2R f - bpow radix2 (-1075) -> - bpow radix2 (-1021) < M ->
  near_round (atan M) f.
Proof.
intros f M Hf Hs HM HT.
assert (Hn : is_nan f = false) by (destruct f; easy).
assert (H : near_round (atan (- M)) (opp f)).
{ apply near_atan_mid; unfold opp.
  - now rewrite is_finite_Bopp.
  - rewrite Bsign_Bopp by exact Hn. now rewrite Hs.
  - rewrite B2R_Bopp. lra.
  - lra. }
apply near_opp in H. unfold opp in H.
now rewrite Bopp_involutive, atan_opp, Ropp_involutive in H.
Qed.
