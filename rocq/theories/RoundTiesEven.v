(** * [round_ties_even1] rounds to an integer, ties to even

    [Generic::round_ties_even1] is IEEE 754's roundToIntegralTiesToEven,
    i.e. [Bnearbyint mode_NE], including the sign of a zero result, the
    infinities and NaN.

    A NaN fails the test [x.abs() < 2^52], as every comparison with a NaN
    does, and so does an infinity, so both are returned as they are, as
    [Bnearbyint] does. A finite [x] with [|x| >= 2^52] has an exponent of
    at least 0, so it is an integer, which rounding to an integer gives
    back.

    For a finite [x] with [|x| < 2^52], [|x| + 2^52] is in [[2^52, 2^53)],
    where the ulp of binary64 is 1, so the sum rounds to [2^52 + n], with
    [n] the integer nearest to [|x|]. Of two integers equally near, the
    sum takes the one that makes [2^52 + n] even, which is the even [n]
    as [2^52] is even: [n = ZnearestE |x|]. [2^52 + n <= 2^53] is a float,
    so the sum does not overflow, and subtracting [2^52] again gives [n]
    exactly. The difference is never [-0]: [n >= 0], and an exact zero
    difference of [Bminus mode_NE] is [+0]. [copysign] then gives [n] the
    sign of [x], which is right because rounding to nearest, ties to even,
    is odd: [ZnearestE (-r) = - ZnearestE r]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Decompose Integer.

Open Scope R_scope.

Lemma finite_not_nan : forall x : f64, is_finite x = true -> is_nan x = false.
Proof. now intros [| | |]. Qed.

(** A float other than NaN is [|x|] or [-|x|], as its sign says. *)
Lemma B2R_sign_abs :
  forall x : f64, is_nan x = false ->
  B2R x = if Bsign x then - Rabs (B2R x) else Rabs (B2R x).
Proof.
intros x Nx. rewrite <- B2R_Babs.
destruct x as [s|s| |s m e H]; try discriminate Nx; destruct s;
  cbn [Bsign Babs]; first [rewrite <- B2R_Bopp; reflexivity | reflexivity].
Qed.

(** Adding an even integer [k] commutes with rounding to nearest, ties to
    even: it moves the integers below and above by [k], and keeps the
    parity of the one below, which breaks a tie. *)
Lemma ZnearestE_plus_even :
  forall y k, Z.even k = true -> ZnearestE (y + IZR k) = (ZnearestE y + k)%Z.
Proof.
intros y k Hk.
assert (Hf : Zfloor (y + IZR k) = (Zfloor y + k)%Z).
{ apply Zfloor_imp. rewrite !plus_IZR.
  pose proof (Zfloor_lb y). pose proof (Zfloor_ub y). lra. }
assert (Hc : Zceil (y + IZR k) = (Zceil y + k)%Z).
{ apply Zceil_imp. rewrite minus_IZR, !plus_IZR.
  pose proof (Zceil_lb y). pose proof (Zceil_ub y). lra. }
unfold Znearest. rewrite Hf, Hc.
replace (y + IZR k - IZR (Zfloor y + k)) with (y - IZR (Zfloor y))
  by (rewrite plus_IZR; ring).
destruct (Rcompare _ _); try reflexivity.
cbv beta. rewrite Z.even_add, Hk.
now destruct (Z.even (Zfloor y)).
Qed.

(** For [0 <= u < 2^52], [u + 2^52] is in [[2^52, 2^53)], where the
    floats are the integers, so it rounds to [ZnearestE u + 2^52]. *)
Lemma round_plus_2_52 :
  forall u, 0 <= u < IZR (2^52) ->
  round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE) (u + IZR (2^52))
  = IZR (ZnearestE u + 2^52).
Proof.
intros u Hu.
assert (Hc : cexp radix2 (SpecFloat.fexp 53 1024) (u + IZR (2^52)) = 0%Z).
{ unfold cexp. rewrite (mag_unique_pos radix2 _ 53); [reflexivity|].
  change (53 - 1)%Z with 52%Z.
  rewrite <- (IZR_Zpower radix2 52), <- (IZR_Zpower radix2 53) by easy.
  change (Zpower radix2 52) with (2^52)%Z.
  change (Zpower radix2 53) with (2 * 2^52)%Z.
  rewrite mult_IZR. lra. }
unfold round, F2R, scaled_mantissa. rewrite Hc.
cbn [Fnum Fexp bpow Z.opp round_mode]. rewrite !Rmult_1_r.
rewrite ZnearestE_plus_even by reflexivity. reflexivity.
Qed.

Theorem round_ties_even1_correct :
  forall x, Generic.round_ties_even1 x = Bnearbyint mode_NE x.
Proof.
intros x.
destruct (is_finite x) eqn:Fx.
2: { (* NaN and the infinities fail the test and are returned as they are. *)
  destruct x as [[|]|[|]| |s m e H]; try discriminate Fx;
    vm_compute; reflexivity. }
assert (H52 : (0 <= 2^52 <= 2^53)%Z) by lia.
destruct (of_u64_exact (2^52) H52) as (FT & ST & RT).
assert (Fa : is_finite (Babs x) = true) by now rewrite is_finite_Babs.
destruct (Bnearbyint_correct 53 1024 _ mode_NE x) as (HR & HF & HS).
cbn [round_mode] in HR.
specialize (HS (finite_not_nan _ (eq_trans HF Fx))).
unfold Generic.round_ties_even1, lt, fabs, add, sub, copysign, opp.
cbv zeta.
set (T := of_u64 (2^52)) in *.
rewrite Bltb_correct by assumption.
rewrite B2R_Babs, RT.
destruct (Rlt_bool_spec (Rabs (B2R x)) (IZR (2^52))) as [Hlt|Hge].
2: { (* [|x| >= 2^52]: [x] is an integer. *)
  apply B2R_Bsign_inj; [exact Fx | rewrite HF; exact Fx | | now rewrite HS].
  rewrite HR. symmetry. apply round_generic; [typeclasses eauto|].
  (* From [2^52] up, binary64's exponent is at least 0. *)
  apply generic_inclusion_ge
    with (fexp1 := SpecFloat.fexp 53 1024) (e1 := 52%Z).
  - intros e He. unfold FIX_exp, SpecFloat.fexp, SpecFloat.emin. lia.
  - rewrite <- (IZR_Zpower radix2 52) by easy. exact Hge.
  - apply generic_format_B2R. }
(* The sum [s = |x| + 2^52]. *)
pose proof (@Bplus_correct 53 1024 _ _ mode_NE (Babs x) T Fa FT) as Hs.
rewrite B2R_Babs, RT in Hs.
set (u := Rabs (B2R x)) in *.
assert (Hu : 0 <= u < IZR (2^52)) by (split; [apply Rabs_pos | exact Hlt]).
set (n := ZnearestE u).
assert (Hn : (0 <= n <= 2^52)%Z).
{ split.
  - apply Z.le_trans with (Zfloor u).
    + apply Zfloor_lub. apply Hu.
    + apply Znearest_ge_floor.
  - apply Z.le_trans with (Zceil u).
    + apply Znearest_le_ceil.
    + apply Zceil_glb. lra. }
rewrite round_plus_2_52 in Hs by exact Hu. fold n in Hs.
rewrite Rlt_bool_true in Hs.
2: { rewrite Rabs_pos_eq by (apply IZR_le; lia).
     apply Rle_lt_trans with (IZR (2^53)); [apply IZR_le; lia|].
     rewrite (IZR_Zpower radix2) by easy. apply bpow_lt. lia. }
destruct Hs as (Rs & Fs & Ss).
rewrite Rcompare_Gt in Ss by lra.
set (s := Bplus mode_NE (Babs x) T) in *.
(* The difference [d = s - 2^52 = n], exact. *)
pose proof (@Bminus_correct 53 1024 _ _ mode_NE s T Fs FT) as Hd.
rewrite Rs, RT in Hd.
replace (IZR (n + 2^52) - IZR (2^52)) with (IZR n) in Hd
  by (rewrite plus_IZR; ring).
assert (Fn : generic_format radix2 (SpecFloat.fexp 53 1024) (IZR n)).
{ change (SpecFloat.fexp 53 1024) with fexp64.
  apply generic_format_FLT.
  apply FLT_spec with (Float radix2 n 0).
  - unfold F2R; simpl. ring.
  - cbn [Fnum]. rewrite Z.abs_eq by lia. simpl Z.pow in *. lia.
  - cbn [Fexp]. lia. }
rewrite (round_generic _ _ _ (IZR n) Fn) in Hd.
rewrite Rlt_bool_true in Hd.
2: { rewrite Rabs_pos_eq by (apply IZR_le; lia).
     apply Rle_lt_trans with (IZR (2^52)); [apply IZR_le; lia|].
     rewrite (IZR_Zpower radix2) by easy. apply bpow_lt. lia. }
destruct Hd as (Rd & Fd & Sd).
rewrite Ss, ST in Sd.
set (d := Bminus mode_NE s T) in *.
(* [d] is [n], and [+0], not [-0], if [n = 0]. *)
assert (Sd' : Bsign d = false).
{ rewrite Sd. destruct (Rcompare_spec (IZR n) 0) as [Hlt0|_|_];
    [apply lt_IZR in Hlt0; lia | reflexivity | reflexivity]. }
pose proof (B2R_sign_abs x (finite_not_nan x Fx)) as Hx.
rewrite Sd'.
destruct (Bsign x) eqn:Sx; cbn [Bool.eqb].
- (* [x] is [-u]: [-n], as [ZnearestE (-u) = - ZnearestE u]. *)
  apply B2R_Bsign_inj.
  + rewrite is_finite_Bopp. exact Fd.
  + rewrite HF. exact Fx.
  + rewrite B2R_Bopp, Rd, HR, Hx, round_NE_opp, round_FIX_0. reflexivity.
  + rewrite Bsign_Bopp by exact (finite_not_nan d Fd). now rewrite Sd', HS.
- (* [x] is [u]: [n]. *)
  apply B2R_Bsign_inj.
  + exact Fd.
  + rewrite HF. exact Fx.
  + rewrite Rd, HR, Hx, round_FIX_0. reflexivity.
  + now rewrite Sd', HS.
Qed.
