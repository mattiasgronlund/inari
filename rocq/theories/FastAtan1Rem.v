(** * The remainder of the quotients of the first stage of the fast path of atan

    [DyadicAtan.fast_quot], [DyadicAtan.fast_recip] and
    [DyadicAtan.fast_atan1] of [Model.v] compute [qh = RN(n / d)] and the
    remainder [n - qh d] as [sub (sub n p) pe], from the product
    [qh d = p + pe] of [Generic.two_prod_err] (Dekker). For [2^-80 <= |n|
    <= 4] and [1/2 <= d <= 2^54], the remainder is an [f64]
    ([DivRemainder.div_remainder], Boldo-Daumas), the product is exact and
    the two subtractions are ([DivRuFast.div_dekker_remainder]), and [pe]
    is the same [f64] with and without an FMA ([atan1_rem]). *)

From Stdlib Require Import ZArith Reals Lra Lia QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error Sterbenz.
From Inari Require Import Model Mpfr Encoding Elementary TwoSum TwoProduct DyDriver NearF64
  FastRound FastRoundErr FastDiv CancelLanes FastHypPos FastAtanTables FastAtanIdent
  FastAtanPoly FastAtanCore.
From Inari Require FastExpErr FastExpReduce ConstTight DivRemainder DivRuFast.

Open Scope R_scope.

Local Notation format := (generic_format radix2 fexp64).

(* Closes a linear goal whose constants are literal powers of two: [cbn]
   turns each [bpow radix2 n] into a rational constant for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2] in *; lra.

(** [x / y] of finite [f64]s with an exact result of at most 16 in
    magnitude is finite and rounded to nearest, as in [FastDiv.v]. *)
Local Lemma div_e :
  forall x y, is_finite x = true -> is_finite y = true -> B2R y <> 0 ->
  Rabs (B2R x / B2R y) <= 16 ->
  is_finite (div x y) = true /\ B2R (div x y) = RN (B2R x / B2R y).
Proof.
intros x y Fx Fy Hy H.
destruct (RN_below_max _ (FastExpErr.small_le_max _ H)) as (Hlt & _).
generalize (@Bdiv_correct 53 1024 _ _ mode_NE x y Hy).
rewrite Rlt_bool_true by exact Hlt.
intros (HR & HF & _).
change (Bdiv mode_NE x y) with (div x y) in HR, HF.
rewrite Fx in HF. split; [exact HF | exact HR].
Qed.

(** The exponent of a finite [f64] of at most 8 is below 4, as in
    [FastDiv.v]. *)
Local Lemma exponent_small :
  forall x, is_finite x = true -> Rabs (B2R x) <= 8 -> (Generic.exponent x < 4)%Z.
Proof.
intros x Fx H.
apply exponent_lt; [exact Fx | lia |].
change (bpow radix2 4) with 16. lra.
Qed.

(** [qh = RN(n / d)] is finite and in [[2^-134, 8]] in magnitude, the
    error of the product [qh d] is the same with and without an FMA, and
    [sub (sub n p) pe] is the remainder [n - qh d] exactly. *)
Lemma atan1_rem :
  forall fma n d,
  is_finite n = true -> is_finite d = true ->
  bpow radix2 (-80) <= Rabs (B2R n) <= 4 -> / 2 <= B2R d <= bpow radix2 54 ->
  let q := div n d in
  let p := mul q d in
  is_finite q = true /\ B2R q = RN (B2R n / B2R d) /\
  bpow radix2 (-134) <= Rabs (B2R q) <= 8 /\
  Generic.two_prod_err fma q d p = Generic.two_prod_err false q d p /\
  is_finite (sub (sub n p) (Generic.two_prod_err false q d p)) = true /\
  B2R (sub (sub n p) (Generic.two_prod_err false q d p)) = B2R n - B2R q * B2R d.
Proof.
intros fma n d Fn Fd HN HD. cbv zeta.
assert (HD0 : 0 < B2R d) by lra.
assert (Hd0 : B2R d <> 0) by lra.
(* [|n / d|] lies in [[2^-80 / 2^54, 4 / (1/2)]]. *)
assert (Hz : bpow radix2 (-134) <= Rabs (B2R n / B2R d) <= 8).
{ unfold Rdiv. rewrite Rabs_mult, Rabs_inv, (Rabs_pos_eq (B2R d)) by lra.
  split; apply Rmult_le_reg_r with (B2R d); try lra;
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra; num. }
assert (Hz16 : Rabs (B2R n / B2R d) <= 16) by lra.
destruct (div_e n d Fn Fd Hd0 Hz16) as (Fq & Rq).
(* Rounding is monotone in magnitude and [2^-134] and [8] are [f64]s. *)
assert (HQ : bpow radix2 (-134) <= Rabs (B2R (div n d)) <= 8).
{ rewrite Rq. split.
  - apply abs_round_ge_generic; [typeclasses eauto .. | | lra].
    apply generic_format_FLT_bpow; [typeclasses eauto | lia].
  - apply abs_round_le_generic; [typeclasses eauto .. | | lra].
    change 8 with (bpow radix2 3).
    apply generic_format_FLT_bpow; [typeclasses eauto | lia]. }
assert (HN0 : bpow radix2 (-967) <= Rabs (B2R n)).
{ apply Rle_trans with (2 := proj1 HN). apply bpow_le. lia. }
assert (HQn : bpow radix2 (-1022) <= Rabs (RN (B2R n / B2R d))).
{ rewrite <- Rq. apply Rle_trans with (2 := proj1 HQ). apply bpow_le. lia. }
assert (Gn : format (B2R n)) by apply generic_format_B2R.
assert (Gd : format (B2R d)) by apply generic_format_B2R.
destruct (DivRemainder.div_remainder (B2R n) (B2R d) Gn Gd Hd0 HQn HN0) as (Fr0 & Hr0).
rewrite <- Rq in Fr0, Hr0.
(* [qh d] is within [2^-52 |n|] of [n], so [|qh d|] lies in
   [[|n| / 2, 2 |n|]]. *)
assert (HQD : Rabs (B2R n) / 2 <= Rabs (B2R (div n d) * B2R d) <= 2 * Rabs (B2R n)).
{ pose proof (Rabs_triang_inv (B2R n) (B2R n - B2R (div n d) * B2R d)) as T1.
  replace (B2R n - (B2R n - B2R (div n d) * B2R d))
    with (B2R (div n d) * B2R d) in T1 by ring.
  pose proof (Rabs_triang (B2R n) (B2R (div n d) * B2R d - B2R n)) as T2.
  replace (B2R n + (B2R (div n d) * B2R d - B2R n))
    with (B2R (div n d) * B2R d) in T2 by ring.
  rewrite Rabs_minus_sym in T2.
  pose proof (Rabs_pos (B2R n)).
  split; num. }
assert (KQD : Rabs (B2R (div n d) * B2R d) <= 16) by lra.
destruct (FastExpErr.mul_e (div n d) d Fq Fd KQD) as (Fp & Rp & _).
assert (HP : bpow radix2 (-82) <= Rabs (B2R (mul (div n d) d)) <= 8).
{ rewrite Rp. split.
  - apply abs_round_ge_generic; [typeclasses eauto .. | | num].
    apply generic_format_FLT_bpow; [typeclasses eauto | lia].
  - apply abs_round_le_generic; [typeclasses eauto .. | | lra].
    change 8 with (bpow radix2 3).
    apply generic_format_FLT_bpow; [typeclasses eauto | lia]. }
(* The exponents that [two_prod_is_exact] and [div_dekker_remainder]
   check. *)
assert (Ep1 : (-82 <= Generic.exponent (mul (div n d) d))%Z).
{ apply exponent_ge; [exact Fp | lra]. }
assert (Ep2 : (Generic.exponent (mul (div n d) d) < 4)%Z).
{ apply exponent_small; [exact Fp | lra]. }
assert (Eq : (Generic.exponent (div n d) < 4)%Z).
{ apply exponent_small; [exact Fq | lra]. }
assert (Ed : (Generic.exponent d < 55)%Z).
{ apply exponent_lt; [exact Fd | lia |].
  rewrite Rabs_pos_eq by lra.
  apply Rle_lt_trans with (1 := proj2 HD). apply bpow_lt. lia. }
assert (En : (Generic.exponent n < 4)%Z).
{ apply exponent_small; [exact Fn | lra]. }
assert (T1 : Generic.two_prod_is_exact true (div n d) d (mul (div n d) d) = true)
  by (apply two_prod_is_exact_of; lia).
assert (T0 : Generic.two_prod_is_exact false (div n d) d (mul (div n d) d) = true)
  by (apply two_prod_is_exact_of; lia).
assert (En' : (Generic.exponent n <= 1021)%Z) by lia.
assert (Eq' : (Generic.exponent (div n d) <= 995)%Z) by lia.
assert (Ed' : (Generic.exponent d <= 995)%Z) by lia.
(* The remainder [(n - p) - pe] is [n - qh d] exactly, and [pe] is the
   same with an FMA as with Dekker's product. *)
destruct (DivRuFast.div_dekker_remainder n (div n d) d Fn Fq Fd Fr0 Hr0 HN0 En' Eq' Ed')
  as (Fa & Ra).
split; [exact Fq |]. split; [exact Rq |]. split; [exact HQ |].
split; [destruct fma; [exact (two_prod_err_fma_eq _ _ Fq Fd T1 T0) | reflexivity] |].
split; [exact Fa | exact Ra].
Qed.
