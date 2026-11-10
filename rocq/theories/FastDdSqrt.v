(** * The square root of a double-double

    [Fast.dd_sqrt fma ah al] of [Model.v] is Dekker's square root of a
    double-double [ah + al] [Dekker 1971, "A floating-point technique for
    extending the available precision", [sqrt2]]: [s = RN(√ah)], the
    exact residual [ah - s^2] from [s^2 = p + pe] in double-double, and
    the correction [((ah - p) - pe + al) / (2 s)] added by [Fast2Sum]. For
    [2^-900 <= ah <= 2^900] and [|al| <= 2^-52 ah] it is within [2^-100]
    of [√(ah + al)] relatively ([dd_sqrt_correct]), and returns the same
    with and without an FMA ([dd_sqrt_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error Sterbenz.
From Inari Require Import Model Mpfr Encoding TwoSum TwoProduct DyDriver NearF64
  FastRound CancelLanes FastHypPos.
From Inari Require SqrtFast SqrtRem SqrtSlow FastExpErr.

Open Scope R_scope.

Local Notation format := (generic_format radix2 fexp64).

(** ** Helpers *)

(** [x / y] of finite [f64]s with an exact result of at most [MAX] in
    magnitude is finite and rounded to nearest, as [FastDiv.div_e]. *)
Local Lemma div_e :
  forall x y, is_finite x = true -> is_finite y = true -> B2R y <> 0 ->
  Rabs (B2R x / B2R y) <= MAX ->
  is_finite (div x y) = true /\ B2R (div x y) = RN (B2R x / B2R y).
Proof.
intros x y Fx Fy Hy H.
destruct (RN_below_max _ H) as (Hlt & _).
generalize (@Bdiv_correct 53 1024 _ _ mode_NE x y Hy).
rewrite Rlt_bool_true by exact Hlt.
intros (HR & HF & _).
change (Bdiv mode_NE x y) with (div x y) in HR, HF.
rewrite Fx in HF. split; [exact HF | exact HR].
Qed.

(** The exponent of a finite [f64] below [2^k] is below [k], and that of
    one at least [2^k] at least [k] (as in [FastDiv.v]). *)
Local Lemma exponent_lt :
  forall x k, is_finite x = true -> (-1022 <= k)%Z ->
  Rabs (B2R x) < bpow radix2 k -> (Generic.exponent x < k)%Z.
Proof.
intros x k Fx Hk H.
destruct (Z_lt_le_dec (Generic.exponent x) (-1022)) as [L|L]; [lia|].
pose proof (bpow_exponent_le_abs_B2R x Fx L) as H0.
assert (H1 : bpow radix2 (Generic.exponent x) < bpow radix2 k) by lra.
apply lt_bpow in H1. exact H1.
Qed.

Local Lemma exponent_ge :
  forall x k, is_finite x = true -> bpow radix2 k <= Rabs (B2R x) ->
  (k <= Generic.exponent x)%Z.
Proof.
intros x k Fx H.
pose proof (abs_B2R_lt_exponent x Fx) as H0.
assert (H1 : bpow radix2 k < bpow radix2 (Generic.exponent x + 1)) by lra.
apply lt_bpow in H1. lia.
Qed.

(** Both variants of [two_prod_is_exact] hold for operands and a product
    of moderate exponents (as in [FastDiv.v]). *)
Local Lemma two_prod_is_exact_of :
  forall fma x y,
  (-968 <= Generic.exponent (mul x y) <= 1022)%Z ->
  (Generic.exponent x <= 995)%Z -> (Generic.exponent y <= 995)%Z ->
  Generic.two_prod_is_exact fma x y (mul x y) = true.
Proof.
intros fma x y Ep Ex Ey.
destruct fma; cbv beta iota zeta delta [Generic.two_prod_is_exact];
  repeat (apply andb_true_intro; split); apply Z.leb_le; lia.
Qed.

(** The literal [2.0] (as in [FastRoundErr.v]). *)
Local Lemma two_R : B2R Fast.two = 2.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF Fast.two) with (SpecFloat.S754_finite false 4503599627370496 (-51))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

(** [2^-450 <= √z <= 2^450] on the range of [ah]. *)
Local Lemma sqrt_range :
  forall z, bpow radix2 (-900) <= z <= bpow radix2 900 ->
  bpow radix2 (-450) <= sqrt z <= bpow radix2 450.
Proof.
intros z Hz. split.
- rewrite <- (sqrt_bpow radix2 (-450)). apply sqrt_le_1_alt.
  change (2 * -450)%Z with (-900)%Z. lra.
- rewrite <- (sqrt_bpow radix2 450). apply sqrt_le_1_alt.
  change (2 * 450)%Z with 900%Z. lra.
Qed.

(** If [0 < X <= b], a bound of [a b] by [k X^2] is one of [a] by [k X]. *)
Local Lemma div_bound :
  forall a b k X, 0 < X -> X <= b -> Rabs (a * b) <= k * (X * X) -> Rabs a <= k * X.
Proof.
intros a b k X HX Hb H.
rewrite Rabs_mult, (Rabs_pos_eq b) in H by lra.
apply Rmult_le_reg_r with X; [exact HX |].
apply Rle_trans with (Rabs a * b).
- apply Rmult_le_compat_l; [apply Rabs_pos | exact Hb].
- lra.
Qed.

Local Lemma half_le :
  forall X Y, 0 < X -> 0 <= Y -> X * X / 4 <= Y * Y -> X / 2 <= Y.
Proof.
intros X Y HX HY H.
destruct (Rle_or_lt (X / 2) Y) as [L | L]; [exact L | nra].
Qed.

(** ** The root and its square

    [s = RN(√ah)] is finite, in [[2^-483, 2^451]], [p = RN(s^2)] is
    finite, and [s^2] is exact in double-double either way: [p] is in
    [[2^-966, 2^902]], far from underflow and overflow. *)
Local Lemma root :
  forall ah, is_finite ah = true ->
  bpow radix2 (-900) <= B2R ah <= bpow radix2 900 ->
  is_finite (fsqrt ah) = true /\ B2R (fsqrt ah) = RN (sqrt (B2R ah)) /\
  bpow radix2 (-483) <= B2R (fsqrt ah) <= bpow radix2 451 /\
  bpow radix2 (-966) <= B2R (fsqrt ah) * B2R (fsqrt ah) <= bpow radix2 902 /\
  is_finite (mul (fsqrt ah) (fsqrt ah)) = true /\
  B2R (mul (fsqrt ah) (fsqrt ah)) = RN (B2R (fsqrt ah) * B2R (fsqrt ah)) /\
  (forall fma,
   Generic.two_prod_is_exact fma (fsqrt ah) (fsqrt ah) (mul (fsqrt ah) (fsqrt ah)) = true).
Proof.
intros ah Fah Hah.
pose proof (bpow_gt_0 radix2 (-900)) as P900.
pose proof (bpow_gt_0 radix2 (-483)) as P483.
pose proof (bpow_gt_0 radix2 (-966)) as P966.
destruct (SqrtFast.fsqrt_correct ah Fah ltac:(lra)) as (Fs & Hs).
assert (Hlo : bpow radix2 (-966) <= B2R ah).
{ apply Rle_trans with (bpow radix2 (-900)); [apply bpow_le; lia | lra]. }
assert (Hhi : B2R ah < bpow radix2 (2 * 451)).
{ apply Rle_lt_trans with (bpow radix2 900); [lra | apply bpow_lt; lia]. }
destruct (SqrtFast.RN_sqrt_bounds (B2R ah) 451 ltac:(lia) Hlo Hhi)
  as ((Hslo & Hshi) & (Hsslo & Hsshi)).
rewrite <- Hs in Hslo, Hshi, Hsslo, Hsshi.
change (2 * 451)%Z with 902%Z in Hsshi.
set (s := fsqrt ah) in *.
(* [p = RN(s^2)], with [s^2 <= 2^902] far below overflow. *)
assert (Hm : Rabs (B2R s * B2R s) <= bpow radix2 1023 + bpow radix2 971).
{ rewrite Rabs_pos_eq by lra.
  pose proof (bpow_gt_0 radix2 971).
  apply Rle_trans with (bpow radix2 1023); [| lra].
  apply Rle_trans with (bpow radix2 902); [exact Hsshi | apply bpow_le; lia]. }
destruct (mul_fin s s Fs Fs Hm) as (Fp & Hp).
(* [2^-966 <= p <= 2^902], as both bounds are [f64]s. *)
assert (Hplo : bpow radix2 (-966) <= B2R (mul s s)).
{ rewrite Hp. apply round_ge_generic;
    [typeclasses eauto .. | apply generic_format_FLT_bpow; [easy | lia] | exact Hsslo]. }
assert (Hphi : B2R (mul s s) <= bpow radix2 902).
{ rewrite Hp. apply round_le_generic;
    [typeclasses eauto .. | apply generic_format_FLT_bpow; [easy | lia] | exact Hsshi]. }
(* So the exponents meet both variants of [two_prod_is_exact]. *)
assert (Es : (Generic.exponent s <= 995)%Z).
{ assert (E : (Generic.exponent s < 452)%Z); [| lia].
  apply exponent_lt; [exact Fs | lia |].
  rewrite Rabs_pos_eq by lra.
  apply Rle_lt_trans with (bpow radix2 451); [exact Hshi | apply bpow_lt; lia]. }
assert (Ep : (-968 <= Generic.exponent (mul s s) <= 1022)%Z).
{ split.
  - assert (E : (-966 <= Generic.exponent (mul s s))%Z); [| lia].
    apply exponent_ge; [exact Fp |]. rewrite Rabs_pos_eq by lra. exact Hplo.
  - assert (E : (Generic.exponent (mul s s) < 903)%Z); [| lia].
    apply exponent_lt; [exact Fp | lia |].
    rewrite Rabs_pos_eq by lra.
    apply Rle_lt_trans with (bpow radix2 902); [exact Hphi | apply bpow_lt; lia]. }
split; [exact Fs |]. split; [exact Hs |]. split; [exact (conj Hslo Hshi) |].
split; [exact (conj Hsslo Hsshi) |]. split; [exact Fp |]. split; [exact Hp |].
intros fma. apply two_prod_is_exact_of; [exact Ep | exact Es | exact Es].
Qed.

(** ** The residual

    [q = ah - p] is exact by Sterbenz's lemma, as [p / 2 <= ah <= 2 p],
    and [r = RN(q - pe) = RN(ah - s^2)] is exact as [ah - s^2] is an
    [f64] ([SqrtRem.sqrt_rem_format]); the argument of
    [SqrtFast.sqrt1_fast] without an FMA. *)
Local Lemma rem_exact :
  forall fma ah, is_finite ah = true ->
  bpow radix2 (-900) <= B2R ah <= bpow radix2 900 ->
  let s := fsqrt ah in
  let p := mul s s in
  let r := sub (sub ah p) (Generic.two_prod_err fma s s p) in
  is_finite r = true /\ B2R r = B2R ah - B2R s * B2R s.
Proof.
intros fma ah Fah Hah.
destruct (root ah Fah Hah) as (Fs & Hs & (Hslo & _) & (Hsslo & Hsshi) & Fp & Hp & T).
destruct (two_prod_err_correct fma _ _ Fs Fs (T fma)) as (_ & _ & _ & Fpe & Hpe).
cbv zeta.
set (s := fsqrt ah) in *.
set (p := mul s s) in *.
set (pe := Generic.two_prod_err fma s s p) in *.
pose proof (bpow_gt_0 radix2 (-966)) as P966.
pose proof (bpow_gt_0 radix2 (-450)) as P450.
assert (M902 : 2 * bpow radix2 902 <= MAX) by (cbn [bpow radix_val radix2]; lra).
assert (H900 : bpow radix2 900 <= bpow radix2 902) by (apply bpow_le; lia).
assert (H966 : bpow radix2 (-966) <= bpow radix2 (-900)) by (apply bpow_le; lia).
(* The relative errors: [|s - √ah| <= 2^-53 √ah], as [√ah >= 2^-450] is
   normal, and [|p - s^2| <= 2^-53 s^2]. *)
destruct (sqrt_range _ Hah) as (Halo & _).
assert (Haa : sqrt (B2R ah) * sqrt (B2R ah) = B2R ah) by (apply sqrt_sqrt; lra).
assert (Ha1022 : bpow radix2 (-1022) <= sqrt (B2R ah)).
{ apply Rle_trans with (bpow radix2 (-450)); [apply bpow_le; lia | exact Halo]. }
pose proof (SqrtFast.RN_rel (sqrt (B2R ah))) as E1.
rewrite (Rabs_pos_eq (sqrt (B2R ah))) in E1 by lra.
rewrite <- Hs in E1. specialize (E1 Ha1022).
assert (Hss1022 : bpow radix2 (-1022) <= B2R s * B2R s).
{ apply Rle_trans with (bpow radix2 (-966)); [apply bpow_le; lia | exact Hsslo]. }
pose proof (SqrtFast.RN_rel (B2R s * B2R s)) as E2.
rewrite (Rabs_pos_eq (B2R s * B2R s)) in E2 by lra.
rewrite <- Hp in E2. specialize (E2 Hss1022).
apply Rabs_le_inv in E1. apply Rabs_le_inv in E2.
assert (Hu : 0 < bpow radix2 (-53) <= / 8).
{ split; [apply bpow_gt_0 |].
  apply Rle_trans with (bpow radix2 (-3)); [apply bpow_le; lia |].
  change (bpow radix2 (-3)) with (/ 8). lra. }
set (a := sqrt (B2R ah)) in *.
set (u := bpow radix2 (-53)) in *.
assert (Hss0 : 0 <= B2R s * B2R s) by lra.
(* With [u <= 1/8]: [7/8 √ah <= s <= 9/8 √ah], so
   [49/64 ah <= s^2 <= 81/64 ah], and [7/8 s^2 <= p <= 9/8 s^2]. *)
assert (S1 : 7/8 * a <= B2R s <= 9/8 * a) by (split; nra).
assert (S2 : 49/64 * (a * a) <= B2R s * B2R s <= 81/64 * (a * a))
  by (split; nra).
assert (P : 7/8 * (B2R s * B2R s) <= B2R p <= 9/8 * (B2R s * B2R s))
  by (split; nra).
(* So [343/512 ah <= p <= 729/512 ah], and Sterbenz's lemma applies. *)
assert (Hst : B2R p / 2 <= B2R ah <= 2 * B2R p) by lra.
assert (Fxp : format (B2R ah - B2R p)).
{ apply sterbenz;
    [typeclasses eauto .. | apply generic_format_B2R | apply generic_format_B2R
    | exact Hst]. }
assert (Hxp : Rabs (B2R ah - B2R p) <= MAX) by (apply Rabs_le; split; lra).
destruct (sub_below_max ah p Fah Fp Hxp) as (Fq & Hq & _).
rewrite round_generic in Hq by first [exact Fxp | typeclasses eauto].
set (q := sub ah p) in *.
(* [q - pe = ah - s^2], an [f64] of at most [2^902] in magnitude. *)
assert (Fr0 : format (B2R ah - B2R s * B2R s)).
{ rewrite Hs. apply SqrtRem.sqrt_rem_format; [apply generic_format_B2R | lra]. }
assert (Hqe : Rabs (B2R q - B2R pe) <= MAX).
{ rewrite Hq, Hpe. apply Rabs_le. split; lra. }
destruct (sub_below_max q pe Fq Fpe Hqe) as (Fr & Hr & _).
rewrite Hq, Hpe in Hr.
replace (B2R ah - B2R p - (B2R s * B2R s - B2R p))
  with (B2R ah - B2R s * B2R s) in Hr by ring.
rewrite round_generic in Hr by first [exact Fr0 | typeclasses eauto].
split; [exact Fr | exact Hr].
Qed.

(** ** The error over the reals

    With [X = √ah], [u = 2^-53] and [w = 2^-1075]: [|s - X| <= u X],
    [r = X^2 - s^2], [|al| <= 2 u X^2], [t = RN(r + al)] and
    [c = RN(t / 2s)]. Then [|r| <= 3 u X^2], [|r + al| <= 5 u X^2],
    [|t| <= 6 u X^2], and with [Q = t / 2s] and [cs = (r + al) / 2s]:
    [|Q| <= 6 u X], [|Q - cs| <= 6 u^2 X] and [|c - Q| <= 6 u^2 X + w].
    For [Y = √(ah + al)], [(s + cs - Y) 2s = (s - Y)^2] (the correction
    of Dekker's [sqrt2] is one Newton step), [|X - Y| <= 2 u X] and
    [|s - Y| <= 3 u X], so [|s + cs - Y| <= 9 u^2 X], and in all
    [|s + c - Y| <= 22 u^2 X <= 64 u^2 (X / 2) <= 2^-100 Y]. The other
    conclusions keep each operation in range and let Fast2Sum apply. *)
Local Lemma sqrt_err :
  forall X s r al,
  bpow radix2 (-450) <= X <= bpow radix2 450 ->
  Rabs (s - X) <= bpow radix2 (-53) * X ->
  r = X * X - s * s ->
  Rabs al <= bpow radix2 (-52) * (X * X) ->
  0 < s /\ Rabs (r + al) <= bpow radix2 1000 /\
  Rabs (RN (r + al) / (2 * s)) <= bpow radix2 1000 /\
  Rabs (RN (RN (r + al) / (2 * s))) <= s /\
  Rabs (s + RN (RN (r + al) / (2 * s))) <= bpow radix2 1000 /\
  Rabs (s + RN (RN (r + al) / (2 * s)) - sqrt (X * X + al))
    <= bpow radix2 (-100) * sqrt (X * X + al).
Proof.
intros X s r al HX Hs Hr Hal.
pose proof (bpow_gt_0 radix2 (-450)) as P450.
(* The constants: [u <= 2^-10], [2^-52 = 2 u], [2^-100 = 64 u^2],
   [w <= u^2 X] and [w <= u^2 X^2]. *)
assert (Hu : 0 < bpow radix2 (-53) <= / 1024).
{ split; [apply bpow_gt_0 |].
  apply Rle_trans with (bpow radix2 (-10)); [apply bpow_le; lia |].
  change (bpow radix2 (-10)) with (/ 1024). lra. }
assert (H52 : bpow radix2 (-52) = 2 * bpow radix2 (-53)).
{ change (-52)%Z with (1 + -53)%Z. rewrite bpow_plus. reflexivity. }
assert (H100 : bpow radix2 (-100) = 64 * (bpow radix2 (-53) * bpow radix2 (-53))).
{ rewrite <- bpow_plus. change (-100)%Z with (6 + (-53 + -53))%Z.
  rewrite (bpow_plus radix2 6). reflexivity. }
assert (Hw1 : bpow radix2 (-1075) <= bpow radix2 (-53) * bpow radix2 (-53) * X).
{ apply Rle_trans with (bpow radix2 (-53) * bpow radix2 (-53) * bpow radix2 (-450)).
  - rewrite <- !bpow_plus. apply bpow_le. lia.
  - apply Rmult_le_compat_l; [| lra].
    apply Rmult_le_pos; apply bpow_ge_0. }
assert (Hw2 : bpow radix2 (-1075) <= bpow radix2 (-53) * bpow radix2 (-53) * (X * X)).
{ apply Rle_trans with
    (bpow radix2 (-53) * bpow radix2 (-53) * (bpow radix2 (-450) * bpow radix2 (-450))).
  - rewrite <- !bpow_plus. apply bpow_le. lia.
  - apply Rmult_le_compat_l; [apply Rmult_le_pos; apply bpow_ge_0 |].
    apply Rmult_le_compat; lra. }
(* The range: [X^2 <= 2^1000] and [4 X <= 2^1000]. *)
assert (HK : X * X <= bpow radix2 1000).
{ apply Rle_trans with (bpow radix2 450 * bpow radix2 450).
  - apply Rmult_le_compat; lra.
  - rewrite <- bpow_plus. apply bpow_le. lia. }
assert (H4X : 4 * X <= bpow radix2 1000).
{ apply Rle_trans with (bpow radix2 2 * bpow radix2 450).
  - change (bpow radix2 2) with 4. lra.
  - rewrite <- bpow_plus. apply bpow_le. lia. }
(* The two roundings. *)
pose proof (FastExpErr.rn_err (r + al)) as Et.
set (t := RN (r + al)) in *.
pose proof (FastExpErr.rn_err (t / (2 * s))) as Ec.
set (c := RN (t / (2 * s))) in *.
rewrite H52 in Hal. rewrite H100.
set (u := bpow radix2 (-53)) in *.
set (w := bpow radix2 (-1075)) in *.
clearbody u w t c.
destruct Hu as (Hu0 & Hu1).
assert (HX0 : 0 < X) by lra.
apply Rabs_le_inv in Hs.
pose proof (Rabs_le_inv _ _ Hal) as Hal2.
assert (UX : u * X <= / 1024 * X) by (apply Rmult_le_compat_r; lra).
assert (HuX : 0 < u * X) by (apply Rmult_lt_0_compat; lra).
assert (HXX : 0 < X * X) by (apply Rmult_lt_0_compat; lra).
assert (UXX : u * (X * X) <= / 1024 * (X * X)) by (apply Rmult_le_compat_r; lra).
assert (HuXX : 0 < u * (X * X)) by (apply Rmult_lt_0_compat; lra).
assert (UUXX : u * (u * (X * X)) <= / 1024 * (u * (X * X)))
  by (apply Rmult_le_compat_r; lra).
assert (UUX : u * (u * X) <= / 1024 * (u * X)) by (apply Rmult_le_compat_r; lra).
assert (Huu : 0 < u * u) by (apply Rmult_lt_0_compat; lra).
assert (Hs0 : 0 < s) by lra.
assert (Hs2 : X <= 2 * s) by lra.
(* [r = (X - s)(X + s)], so [|r| <= u X * 3 X]. *)
assert (Hr3 : Rabs r <= 3 * u * (X * X)).
{ rewrite Hr. replace (X * X - s * s) with ((X - s) * (X + s)) by ring.
  rewrite Rabs_mult, (Rabs_pos_eq (X + s)) by lra.
  apply Rle_trans with (u * X * (X + s)).
  - apply Rmult_le_compat_r; [lra | apply Rabs_le; lra].
  - replace (3 * u * (X * X)) with (u * X * (3 * X)) by ring.
    apply Rmult_le_compat_l; lra. }
assert (Hra : Rabs (r + al) <= 5 * u * (X * X)).
{ eapply Rle_trans; [apply Rabs_triang | lra]. }
(* [t] is within [6 u^2 X^2] of [r + al], and at most [6 u X^2]. *)
assert (Hu5 : u * Rabs (r + al) <= u * (5 * u * (X * X)))
  by (apply Rmult_le_compat_l; lra).
assert (Ht1 : Rabs (t - (r + al)) <= 6 * (u * (u * (X * X)))) by lra.
assert (Ht : Rabs t <= 6 * u * (X * X)).
{ pose proof (Rabs_triang_inv t (r + al)). lra. }
(* [Q = t / 2s] and [cs = (r + al) / 2s], with [2s >= X]. *)
assert (HQ : Rabs (t / (2 * s)) <= 6 * u * X).
{ apply (div_bound _ (2 * s)); [lra | lra |].
  replace (t / (2 * s) * (2 * s)) with t by (field; lra). exact Ht. }
assert (HQc : Rabs (t / (2 * s) - (r + al) / (2 * s)) <= 6 * (u * u) * X).
{ apply (div_bound _ (2 * s)); [lra | lra |].
  replace ((t / (2 * s) - (r + al) / (2 * s)) * (2 * s)) with (t - (r + al))
    by (field; lra).
  lra. }
assert (HuQ : u * Rabs (t / (2 * s)) <= u * (6 * u * X))
  by (apply Rmult_le_compat_l; lra).
assert (Hc : Rabs (c - t / (2 * s)) <= 6 * (u * u) * X + w) by lra.
(* [Y = √(X^2 + al) >= X / 2], as [al >= -2 u X^2]. *)
assert (HY0 : 0 <= X * X + al) by lra.
pose proof (sqrt_sqrt _ HY0) as HYY.
pose proof (sqrt_pos (X * X + al)) as HY.
set (Y := sqrt (X * X + al)) in *.
assert (HYX : X / 2 <= Y) by (apply half_le; [lra | exact HY | rewrite HYY; lra]).
(* [(X - Y)(X + Y) = -al], so [|X - Y| <= 2 u X] and [|s - Y| <= 3 u X]. *)
assert (HXY : Rabs (X - Y) <= 2 * u * X).
{ apply (div_bound _ (X + Y)); [lra | lra |].
  replace ((X - Y) * (X + Y)) with (- al) by lra.
  rewrite Rabs_Ropp. exact Hal. }
assert (HsY : Rabs (s - Y) <= 3 * u * X).
{ replace (s - Y) with ((s - X) + (X - Y)) by ring.
  eapply Rle_trans; [apply Rabs_triang |].
  assert (Rabs (s - X) <= u * X) by (apply Rabs_le; lra). lra. }
(* The Newton step: [(s + cs - Y) 2s = 2 s^2 + r + al - 2 s Y = (s - Y)^2],
   by [r = X^2 - s^2] and [Y^2 = X^2 + al]. *)
assert (HE : Rabs (s + (r + al) / (2 * s) - Y) <= 9 * (u * u) * X).
{ apply (div_bound _ (2 * s)); [lra | lra |].
  replace ((s + (r + al) / (2 * s) - Y) * (2 * s)) with ((s - Y) * (s - Y)).
  - rewrite Rabs_mult.
    apply Rle_trans with ((3 * u * X) * (3 * u * X)).
    + apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact HsY | exact HsY].
    + right. ring.
  - replace ((s + (r + al) / (2 * s) - Y) * (2 * s))
      with (2 * s * s + (r + al) - 2 * s * Y) by (field; lra).
    rewrite Hr. lra. }
(* [|c| <= 6 u X + 7 u^2 X <= 7 u X <= (1 - u) X <= s]. *)
assert (Hc7 : Rabs c <= 7 * u * X).
{ pose proof (Rabs_triang_inv c (t / (2 * s))). lra. }
split; [exact Hs0 |].
split; [lra |].
split; [lra |].
split; [lra |].
split.
{ eapply Rle_trans; [apply Rabs_triang |]. rewrite (Rabs_pos_eq s) by lra. lra. }
(* The error: [s + c - Y = (c - Q) + (Q - cs) + (s + cs - Y)]. *)
replace (s + c - Y)
  with ((c - t / (2 * s)) + (t / (2 * s) - (r + al) / (2 * s))
        + (s + (r + al) / (2 * s) - Y)) by (field; lra).
eapply Rle_trans; [apply Rabs_triang |].
eapply Rle_trans; [apply Rplus_le_compat_r; apply Rabs_triang |].
assert (HY2 : 64 * (u * u) * (X / 2) <= 64 * (u * u) * Y)
  by (apply Rmult_le_compat_l; [lra | exact HYX]).
assert (HuuX : 0 < u * u * X) by (apply Rmult_lt_0_compat; lra).
lra.
Qed.

(** ** The theorems *)

Theorem dd_sqrt_correct :
  forall fma ah al sh sl,
  is_finite ah = true -> is_finite al = true ->
  bpow radix2 (-900) <= B2R ah <= bpow radix2 900 ->
  Rabs (B2R al) <= bpow radix2 (-52) * B2R ah ->
  Fast.dd_sqrt fma ah al = (sh, sl) ->
  is_finite sh = true /\ is_finite sl = true /\ B2R sh = RN (B2R sh + B2R sl) /\
  Rabs (B2R sh + B2R sl - sqrt (B2R ah + B2R al)) <= bpow radix2 (-100) * sqrt (B2R ah + B2R al).
Proof.
intros fma ah al sh sl Fah Fal Hah Hal Hsq.
destruct (root ah Fah Hah) as (Fs & Hs & (_ & Hshi) & _ & _ & _ & _).
pose proof (rem_exact fma ah Fah Hah) as Hrem. cbv zeta in Hrem.
destruct Hrem as (Fr & Hr).
cbv beta iota zeta delta [Fast.dd_sqrt Fast.fast_two_sum] in Hsq.
set (s := fsqrt ah) in *.
set (r := sub (sub ah (mul s s)) (Generic.two_prod_err fma s s (mul s s))) in *.
(* [X = √ah], with [|s - X| <= 2^-53 X] as [X >= 2^-450] is normal. *)
pose proof (sqrt_range _ Hah) as HX.
pose proof (bpow_gt_0 radix2 (-450)) as P450.
assert (HXX : sqrt (B2R ah) * sqrt (B2R ah) = B2R ah)
  by (apply sqrt_sqrt; pose proof (bpow_gt_0 radix2 (-900)); lra).
pose proof (SqrtFast.RN_rel (sqrt (B2R ah))) as E1.
rewrite (Rabs_pos_eq (sqrt (B2R ah))) in E1 by lra.
rewrite <- Hs in E1.
specialize (E1 ltac:(apply Rle_trans with (bpow radix2 (-450)); [apply bpow_le; lia | lra])).
set (X := sqrt (B2R ah)) in *.
rewrite <- HXX in Hr, Hal.
destruct (sqrt_err X (B2R s) (B2R r) (B2R al) HX E1 Hr Hal)
  as (Hs0 & Kra & KQ & Kc & Ksc & Kerr).
assert (BM : bpow radix2 1000 <= MAX) by (cbn [bpow radix_val radix2]; lra).
(* [t = RN(r + al)]. *)
destruct (add_below_max r al Fr Fal ltac:(lra)) as (Ft & Rt & _).
set (t := add r al) in *.
(* [d = 2 s] exactly. *)
assert (Ftwo : is_finite Fast.two = true) by reflexivity.
assert (H452 : 2 * bpow radix2 451 < bpow radix2 1024).
{ apply Rle_lt_trans with (bpow radix2 1 * bpow radix2 451); [right; reflexivity |].
  rewrite <- bpow_plus. apply bpow_lt. lia. }
assert (Fd2 : format (B2R Fast.two * B2R s)).
{ rewrite two_R.
  replace (2 * B2R s) with (B2R s * bpow radix2 1)
    by (change (bpow radix2 1) with 2; ring).
  apply SqrtSlow.format_scale_up; [apply generic_format_B2R | lia]. }
assert (Hd2 : Rabs (B2R Fast.two * B2R s) < bpow radix2 1024).
{ rewrite two_R, Rabs_pos_eq by lra. lra. }
destruct (SqrtSlow.mul_exact Fast.two s Ftwo Fs Fd2 Hd2) as (Fd & Rd & _).
rewrite two_R in Rd.
set (d := mul Fast.two s) in *.
(* [c = RN(t / d)]. *)
assert (Hd0 : B2R d <> 0) by lra.
assert (Kt : Rabs (B2R t / B2R d) <= MAX) by (rewrite Rt, Rd; lra).
destruct (div_e t d Ft Fd Hd0 Kt) as (Fc & Rc).
rewrite Rt, Rd in Rc.
set (c := div t d) in *.
rewrite <- Rc in Kc, Ksc, Kerr.
(* [sh = RN(s + c)], and Fast2Sum makes [sl = s + c - sh], as [|c| <= s]. *)
destruct (add_below_max s c Fs Fc ltac:(lra)) as (Fh & Rh & _).
assert (Hcs : Rabs (B2R c) <= Rabs (B2R s))
  by (rewrite (Rabs_pos_eq (B2R s)) by lra; exact Kc).
destruct (CancelLanes.fast_two_sum s c (add s c) Fs Fc Hcs Fh Rh) as (Fl & Rl).
injection Hsq as Hsh Hsl. subst sh sl.
rewrite Rl.
replace (B2R (add s c) + (B2R s + B2R c - B2R (add s c))) with (B2R s + B2R c) by ring.
split; [exact Fh |]. split; [exact Fl |]. split; [exact Rh |].
rewrite <- HXX. exact Kerr.
Qed.

(** [Fast.dd_sqrt] returns the same with and without an FMA. *)
Theorem dd_sqrt_fma :
  forall ah al,
  is_finite ah = true -> is_finite al = true ->
  bpow radix2 (-900) <= B2R ah <= bpow radix2 900 ->
  Fast.dd_sqrt true ah al = Fast.dd_sqrt false ah al.
Proof.
intros ah al Fah Fal Hah.
destruct (root ah Fah Hah) as (Fs & _ & _ & _ & _ & _ & T).
(* The square [s s] is exact, so its error is the same [f64] either way
   ([FastRound.two_prod_err_fma_eq]). *)
cbv beta iota zeta delta [Fast.dd_sqrt].
rewrite (two_prod_err_fma_eq _ _ Fs Fs (T true) (T false)).
reflexivity.
Qed.
