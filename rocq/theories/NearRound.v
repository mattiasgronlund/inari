(** * Rounding to nearest at the overflow bound and in a window of bits

    Rounded to nearest, ties to even, a real number at or above
    [2^1024 - 2^970], the bound of [near_round], is at least [2^1024]
    ([RN_ge_T]), and one below it is less than [2^1024] ([RN_lt_T]). If
    [Spec.rounds_up_to] gives [w] at the rounding to nearest of a positive
    real number [r], [r] rounds to nearest to [w] ([near_of_up]).
    [near_window] rounds [X * 2^-s] to the nearest integer, ties to even,
    where [X] is an integer [q] or a real number strictly between [q] and
    [q + 1], with the integer arithmetic of [Dyadic.round_near]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model NearF64.
From Inari Require Spec RoundUpExact.

Open Scope R_scope.

(** [2^1024 - 2^970], the midpoint of [f64::MAX] and [2^1024], rounds to
    the even [2^1024]: its exponent is 971, and the scaled mantissa
    [2^53 - 1/2] is a tie between [2^53 - 1], odd, and [2^53]. *)
Lemma RN_T :
  round radix2 (FLT_exp (-1074) 53) ZnearestE (bpow radix2 1024 - bpow radix2 970) =
  bpow radix2 1024.
Proof.
  assert (Hu : 0 < bpow radix2 970) by apply bpow_gt_0.
  assert (H1024 : bpow radix2 1024 = IZR (2^54) * bpow radix2 970).
  { rewrite (RoundUpExact.IZR_pow2 54) by lia. rewrite <- bpow_plus. reflexivity. }
  assert (Hmag : mag radix2 (bpow radix2 1024 - bpow radix2 970) = 1024%Z :> Z).
  { apply mag_unique. rewrite Rabs_pos_eq.
    - assert (H1023 : bpow radix2 (1024 - 1) = IZR (2^53) * bpow radix2 970).
      { rewrite (RoundUpExact.IZR_pow2 53) by lia. rewrite <- bpow_plus. reflexivity. }
      rewrite H1023, H1024. change (2^53)%Z with 9007199254740992%Z.
      change (2^54)%Z with 18014398509481984%Z. nra.
    - rewrite H1024. change (2^54)%Z with 18014398509481984%Z. nra. }
  unfold round, scaled_mantissa, cexp. rewrite Hmag.
  change (FLT_exp (-1074) 53 1024) with 971%Z.
  assert (Hm : (bpow radix2 1024 - bpow radix2 970) * bpow radix2 (- 971) =
               IZR (2^53 - 1) + /2).
  { rewrite Rmult_minus_distr_r, <- !bpow_plus, minus_IZR.
    rewrite (RoundUpExact.IZR_pow2 53) by lia.
    change (1024 + - 971)%Z with 53%Z. change (970 + - 971)%Z with (-1)%Z.
    change (bpow radix2 (-1)) with (/ 2). lra. }
  change (- (971))%Z with (-971)%Z. rewrite Hm. unfold Znearest.
  rewrite (Zfloor_imp (2^53 - 1)) by (rewrite plus_IZR; lra).
  rewrite Rcompare_Eq by ring.
  change (negb (Z.even (2^53 - 1))) with true.
  rewrite (Zceil_imp (2^53)) by (rewrite minus_IZR; lra).
  unfold F2R; cbn [Fnum Fexp].
  rewrite (RoundUpExact.IZR_pow2 53) by lia. rewrite <- bpow_plus. reflexivity.
Qed.

Lemma RN_ge_T :
  forall r, bpow radix2 1024 - bpow radix2 970 <= r ->
  bpow radix2 1024 <= round radix2 (FLT_exp (-1074) 53) ZnearestE r.
Proof.
  intros r Hr. rewrite <- RN_T. apply round_le; [typeclasses eauto .. | exact Hr].
Qed.

(** Below [2^1024 - 2^970], [f64::MAX = 2^1024 - 2^971] is nearer to [r]
    than any number from [2^1024] up. *)
Lemma RN_lt_T :
  forall r, r < bpow radix2 1024 - bpow radix2 970 ->
  round radix2 (FLT_exp (-1074) 53) ZnearestE r < bpow radix2 1024.
Proof.
  intros r Hr.
  assert (Hu : 0 < bpow radix2 970) by apply bpow_gt_0.
  assert (H971 : bpow radix2 971 = 2 * bpow radix2 970).
  { change 971%Z with (1 + 970)%Z. rewrite bpow_plus. reflexivity. }
  set (MAX := F2R (Float radix2 (2^53 - 1) 971)).
  assert (HMAX : MAX = bpow radix2 1024 - 2 * bpow radix2 970).
  { unfold MAX, F2R; cbn [Fnum Fexp].
    rewrite minus_IZR, (RoundUpExact.IZR_pow2 53) by lia.
    rewrite Rmult_minus_distr_r, <- bpow_plus, H971. simpl (53 + 971)%Z. ring. }
  assert (Hf : generic_format radix2 (FLT_exp (-1074) 53) MAX).
  { apply generic_format_FLT. apply (FLT_spec _ _ _ _ (Float radix2 (2^53 - 1) 971)).
    - reflexivity.
    - simpl Fnum. vm_compute. reflexivity.
    - simpl Fexp. lia. }
  destruct (round_N_pt radix2 (FLT_exp (-1074) 53) (fun x => negb (Z.even x)) r)
    as [_ HN].
  specialize (HN MAX Hf).
  set (f := round radix2 (FLT_exp (-1074) 53) ZnearestE r) in HN |- *.
  destruct (Rlt_or_le f (bpow radix2 1024)) as [Hlt|Hge]; [exact Hlt|].
  exfalso. rewrite HMAX in HN. revert HN.
  unfold Rabs; destruct (Rcase_abs (f - r)); destruct (Rcase_abs _); lra.
Qed.

(** [RN r] is in the format, so rounding it up gives it back, and it is
    not negative: [rounds_up_to] gives a finite [w] of value [RN r] and
    positive sign if [RN r < 2^1024], which [RN_ge_T] puts at [r] below
    the bound, and +inf otherwise, which [RN_lt_T] puts at [r] from the
    bound up. *)
Lemma near_of_up :
  forall r w, 0 < r ->
  Spec.rounds_up_to (round radix2 (FLT_exp (-1074) 53) ZnearestE r) w -> near_round r w.
Proof.
  intros r w Hr.
  set (f := round radix2 (FLT_exp (-1074) 53) ZnearestE r).
  assert (Hf0 : 0 <= f).
  { rewrite <- (round_0 radix2 (FLT_exp (-1074) 53) ZnearestE).
    apply round_le; [typeclasses eauto .. | lra]. }
  assert (HU : round radix2 (FLT_exp (-1074) 53) Zceil f = f).
  { apply round_generic; [typeclasses eauto .. |].
    apply generic_format_round; typeclasses eauto. }
  unfold Spec.rounds_up_to. rewrite HU, (Rabs_pos_eq f) by exact Hf0.
  rewrite (Rlt_bool_false f 0) by exact Hf0.
  unfold near_round. rewrite (Rabs_pos_eq r) by lra.
  rewrite (Rlt_bool_false r 0) by lra.
  destruct (Rlt_bool_spec f (bpow radix2 1024)) as [Hlt|Hge]; intros H.
  - destruct (Rle_dec (bpow radix2 1024 - bpow radix2 970) r) as [HT|HT].
    + exfalso. generalize (RN_ge_T r HT). fold f. lra.
    + destruct H as (H1 & H2 & H3).
      split; [exact H2|]. split; [exact H1|]. intros _ _. exact H3.
  - destruct (Rle_dec (bpow radix2 1024 - bpow radix2 970) r) as [HT|HT].
    + apply B2SF_inj. rewrite H. reflexivity.
    + exfalso. generalize (RN_lt_T r (Rnot_le_lt _ _ HT)). fold f. lra.
Qed.

(** With [K = 2^s = 2 * h], [k = q / K] and [rest = q mod K],
    [X * 2^-s = k + (rest + d) / K] where [d = X - q] is 0 if not
    [sticky] and strictly between 0 and 1 if [sticky]. It is within 1/2
    of [k + 1] if [rest > h], or [rest = h] and [sticky], and of [k] if
    [rest < h]. At [rest = h] and not [sticky] it is the tie [k + 1/2],
    which goes to [k + 1] if [k] is odd. *)
Lemma near_window :
  forall q s (sticky : bool) (X : R),
  (1 <= s)%Z -> (0 <= q)%Z ->
  (if sticky then IZR q < X < IZR q + 1 else X = IZR q) ->
  ZnearestE (X * bpow radix2 (- s)) =
  (if (2 ^ (s - 1) <? q mod 2 ^ s) ||
      ((q mod 2 ^ s =? 2 ^ (s - 1)) && (sticky || (q / 2 ^ s mod 2 =? 1)))
   then q / 2 ^ s + 1 else q / 2 ^ s)%Z.
Proof.
  intros q s sticky X Hs Hq HX.
  rewrite bpow_opp, <- (RoundUpExact.IZR_pow2 s) by lia.
  assert (HK : (2 ^ s = 2 * 2 ^ (s - 1))%Z).
  { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  assert (Hh : (1 <= 2 ^ (s - 1))%Z).
  { change 1%Z with (2 ^ 0)%Z. apply Z.pow_le_mono_r; lia. }
  set (K := (2 ^ s)%Z) in *. set (h := (2 ^ (s - 1))%Z) in *.
  pose proof (Z.div_mod q K ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound q K ltac:(lia)) as Hb.
  set (k := (q / K)%Z) in *. set (rest := (q mod K)%Z) in *.
  assert (HKh : IZR K = 2 * IZR h) by (rewrite HK, mult_IZR; reflexivity).
  assert (Hh1 : 1 <= IZR h) by (apply IZR_le; exact Hh).
  assert (Hr0 : 0 <= IZR rest) by (apply IZR_le; lia).
  assert (Hr1 : IZR rest + 1 <= IZR K) by (rewrite <- plus_IZR; apply IZR_le; lia).
  assert (Hq' : IZR q = IZR K * IZR k + IZR rest).
  { rewrite <- mult_IZR, <- plus_IZR. f_equal. exact Hdm. }
  assert (HD : 0 <= X - IZR q < 1) by (destruct sticky; lra).
  assert (E0 : X - IZR k * IZR K = IZR rest + (X - IZR q)) by (rewrite Hq'; ring).
  assert (E1 : X - IZR (k + 1) * IZR K = IZR rest - IZR K + (X - IZR q))
    by (rewrite plus_IZR, Hq'; ring).
  (* [n] is the nearest integer to [X / K] if [X - n * K] is within [K / 2]. *)
  assert (Himp : forall n, - IZR K < 2 * (X - IZR n * IZR K) < IZR K ->
                 ZnearestE (X * / IZR K) = n).
  { intros n Hn. apply Znearest_imp.
    assert (E : (X * / IZR K - IZR n) * IZR K = X - IZR n * IZR K) by (field; lra).
    apply Rabs_def1; apply (Rmult_lt_reg_r (IZR K)); try lra; rewrite E; lra. }
  destruct (Z.ltb_spec h rest) as [Hgt|Hle].
  - (* [rest > h]: [k + 1]. *)
    assert (Hg : IZR h + 1 <= IZR rest) by (rewrite <- plus_IZR; apply IZR_le; lia).
    cbv [orb]. apply Himp. rewrite E1. lra.
  - destruct (Z.eqb_spec rest h) as [Heq|Hne].
    + assert (Hr : IZR rest = IZR h) by (f_equal; exact Heq).
      destruct sticky.
      * (* [rest = h] and [sticky]: [k + 1]. *)
        cbv [orb andb]. apply Himp. rewrite E1. lra.
      * (* The tie [k + 1/2]. *)
        cbv [orb andb].
        assert (Ey : X * / IZR K = IZR k + / 2).
        { rewrite HX, Hq', Hr, HKh. field. lra. }
        rewrite Ey. unfold Znearest.
        rewrite (Zfloor_imp k) by (rewrite plus_IZR; lra).
        rewrite Rcompare_Eq by ring.
        rewrite (Zceil_imp (k + 1)) by (rewrite minus_IZR, plus_IZR; lra).
        rewrite Zeven_mod.
        assert (Hk2 : (k mod 2 = 0 \/ k mod 2 = 1)%Z)
          by (pose proof (Z.mod_pos_bound k 2 ltac:(lia)); lia).
        destruct Hk2 as [E|E]; rewrite E; reflexivity.
    + (* [rest < h]: [k]. *)
      assert (Hl : IZR rest + 1 <= IZR h) by (rewrite <- plus_IZR; apply IZR_le; lia).
      cbv [orb andb]. apply Himp. rewrite E0. lra.
Qed.
