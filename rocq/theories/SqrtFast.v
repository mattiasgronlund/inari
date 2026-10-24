(** * The fast path of [sqrt_rd] and [sqrt_ru]: the remainder

    [sqrt1_fast fma x] computes [s = RN(sqrt x)] and a remainder [r] whose
    sign is that of [x - s * s], and checks [-966 <= exponent(x) <= 1023],
    or [<= 1021] without an FMA. If the check passes, [r] is exactly
    [x - s * s].

    The remainder [x - s * s] is a float if [x >= 2^-966] (S. Boldo and
    M. Daumas, Representable correcting terms for possibly underflowing
    floating point operations, ARITH 16, 2003, [BD03]); this file takes
    that as a hypothesis. What is left to prove is that the operations
    that compute [r] are exact and do not overflow:
    - With an FMA, [r = RN(x - s * s)] in one rounding, and
      [|x - s * s| < 2^1024] because [0 < x < 2^1024] and
      [0 < s * s <= 2^1024].
    - Without one, [p = RN(s * s)] and [e = s * s - p] is its exact error by
      Dekker's TwoProduct ([two_prod_err_dekker]), which needs
      [s * s < 2^1023], hence [x < 2^1022]. [x - p] is exact by Sterbenz's
      lemma, since [s] and [p] are within a relative [2^-53] of [sqrt x]
      and [s * s], and then [r = RN((x - p) - e) = RN(x - s * s)] is
      exact too. *)

From Stdlib Require Import Bool ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Relative Sterbenz.
From Inari Require Import Model Encoding TwoSum TwoProduct.

Open Scope R_scope.

Local Notation format := (generic_format radix2 fexp64).

(** [sqrt1_fast] with its [let]s and pattern matches unfolded. *)
Lemma sqrt1_fast_eq :
  forall fma x,
  Generic.sqrt1_fast fma x =
  (fsqrt x,
   (if fma then mul_add (opp (fsqrt x)) (fsqrt x) x
    else sub (sub x (mul (fsqrt x) (fsqrt x)))
           (Generic.two_prod_err false (fsqrt x) (fsqrt x)
              (mul (fsqrt x) (fsqrt x)))),
   ((-966 <=? Generic.exponent x) &&
    (Generic.exponent x <=? if fma then 1023 else 1021))%Z).
Proof.
intros fma x.
destruct fma; reflexivity.
Qed.

(** ** Bounds on [x] and [s] *)

(** The square root of a positive finite float is finite and rounded to
    nearest. *)
Lemma fsqrt_correct :
  forall x, is_finite x = true -> 0 < B2R x ->
  is_finite (fsqrt x) = true /\ B2R (fsqrt x) = RN (sqrt (B2R x)).
Proof.
intros x Fx Hx.
destruct (@Bsqrt_correct 53 1024 _ _ mode_NE x) as (HR & HF & _).
split; [|exact HR].
unfold fsqrt. rewrite HF.
(* Only [+0] and the positive finite floats have a finite square root,
   and only the latter are positive. *)
destruct x as [sx|sx| |[|] mx ex Bx]; try discriminate Fx; try reflexivity.
exfalso. revert Hx. apply Rle_not_lt, Rlt_le.
cbn [B2R]. apply F2R_lt_0. cbn. lia.
Qed.

(** [ok] bounds [x] by powers of two. *)
Lemma exponent_bounds :
  forall x e, is_finite x = true -> 0 < B2R x ->
  (-966 <= Generic.exponent x /\ Generic.exponent x <= e)%Z ->
  bpow radix2 (-966) <= B2R x < bpow radix2 (e + 1).
Proof.
intros x e Fx Hx He.
pose proof (abs_B2R_lt_exponent x Fx) as Hhi.
pose proof (bpow_exponent_le_abs_B2R x Fx) as Hlo.
rewrite Rabs_pos_eq in Hhi, Hlo by lra.
split.
- apply Rle_trans with (bpow radix2 (Generic.exponent x));
    [apply bpow_le; lia | apply Hlo; lia].
- apply Rlt_le_trans with (bpow radix2 (Generic.exponent x + 1));
    [exact Hhi | apply bpow_le; lia].
Qed.

(** If [2^-966 <= z < 2^(2 * e)], then [2^-483 <= RN(sqrt z) <= 2^e],
    because rounding is monotone and powers of two are floats. *)
Lemma RN_sqrt_bounds :
  forall z e, (-483 <= e)%Z ->
  bpow radix2 (-966) <= z -> z < bpow radix2 (2 * e) ->
  bpow radix2 (-483) <= RN (sqrt z) <= bpow radix2 e /\
  bpow radix2 (-966) <= RN (sqrt z) * RN (sqrt z) <= bpow radix2 (2 * e).
Proof.
intros z e He Hlo Hhi.
pose proof (bpow_gt_0 radix2 (-483)).
assert (Hl : bpow radix2 (-483) <= RN (sqrt z)).
{ apply round_ge_generic;
    [typeclasses eauto .. | apply generic_format_FLT_bpow; try typeclasses eauto; lia |].
  rewrite <- (sqrt_bpow radix2 (-483)).
  apply sqrt_le_1_alt. exact Hlo. }
assert (Hu : RN (sqrt z) <= bpow radix2 e).
{ apply round_le_generic;
    [typeclasses eauto .. | apply generic_format_FLT_bpow; try typeclasses eauto; lia |].
  rewrite <- (sqrt_bpow radix2 e).
  apply sqrt_le_1_alt. lra. }
split; [lra|].
(* [2^-966 = 2^-483 * 2^-483] and [2^(2 * e) = 2^e * 2^e]. *)
replace (2 * e)%Z with (e + e)%Z by ring.
change (bpow radix2 (-966)) with (bpow radix2 (-483 + -483)).
rewrite !bpow_plus.
split; apply Rmult_le_compat; lra.
Qed.

(** Rounding to nearest moves a normal value by at most a relative
    [2^-53]. *)
Lemma RN_rel :
  forall z, bpow radix2 (-1022) <= Rabs z ->
  Rabs (RN z - z) <= bpow radix2 (-53) * Rabs z.
Proof.
intros z Hz.
change (-53)%Z with (-1 + -52)%Z.
rewrite bpow_plus.
change (bpow radix2 (-1)) with (/ 2).
apply (relative_error_N_FLT radix2 (-1074) 53); [lia | exact Hz].
Qed.

(** ** The remainder *)

(** If [ok] holds and [x - s * s] is a float, [r = x - s * s] exactly. *)
Theorem sqrt1_fast_rem :
  forall fma x, is_finite x = true -> 0 < B2R x ->
  snd (Generic.sqrt1_fast fma x) = true ->
  format (B2R x - RN (sqrt (B2R x)) * RN (sqrt (B2R x))) ->
  let s := fst (fst (Generic.sqrt1_fast fma x)) in
  let r := snd (fst (Generic.sqrt1_fast fma x)) in
  s = fsqrt x /\ is_finite s = true /\ B2R s = RN (sqrt (B2R x)) /\
  0 < B2R s /\ is_finite r = true /\ B2R r = B2R x - B2R s * B2R s.
Proof.
intros fma x Fx Hx Hok Hf.
cbv zeta.
rewrite sqrt1_fast_eq in Hok |- *.
destruct (fsqrt_correct x Fx Hx) as (Fs & Hs).
rewrite <- Hs in Hf.
set (s := fsqrt x) in *.
pose proof (bpow_gt_0 radix2 (-483)).
pose proof (bpow_gt_0 radix2 (-966)).
destruct fma; cbn [fst snd] in Hok |- *; rewrite andb_true_iff, !Z.leb_le in Hok.
- (* With an FMA, [r = RN(x - s * s)]. *)
  destruct (exponent_bounds x 1023 Fx Hx Hok) as (Hxlo & Hxhi).
  change (1023 + 1)%Z with 1024%Z in Hxhi.
  assert (Hb := RN_sqrt_bounds (B2R x) 512 ltac:(lia) Hxlo Hxhi).
  rewrite <- Hs in Hb. change (2 * 512)%Z with 1024%Z in Hb.
  destruct Hb as ((Hslo & Hshi) & (Hsslo & Hsshi)).
  assert (Fo : is_finite (opp s) = true)
    by (unfold opp; rewrite is_finite_Bopp; exact Fs).
  assert (Ho : B2R (opp s) = - B2R s) by apply B2R_Bopp.
  generalize (@Bfma_correct 53 1024 _ _ mode_NE (opp s) s x Fo Fs Fx).
  cbv zeta. rewrite Ho.
  replace (- B2R s * B2R s + B2R x) with (B2R x - B2R s * B2R s) by ring.
  (* [x - s * s] is a float, so rounding it is exact. *)
  rewrite round_generic by first [exact Hf | typeclasses eauto].
  (* [|x - s * s| < 2^1024], as [0 < x < 2^1024] and [0 < s * s <= 2^1024]. *)
  rewrite Rlt_bool_true by (apply Rabs_lt; split; lra).
  intros (HR & HF & _).
  change (Bfma mode_NE (opp s) s x) with (mul_add (opp s) s x) in HR, HF.
  split; [reflexivity|]. split; [exact Fs|]. split; [exact Hs|].
  split; [lra|]. split; [exact HF | exact HR].
- (* Without an FMA, [r = RN(RN(x - p) - e)]. *)
  destruct (exponent_bounds x 1021 Fx Hx Hok) as (Hxlo & Hxhi).
  change (1021 + 1)%Z with 1022%Z in Hxhi.
  assert (Hb := RN_sqrt_bounds (B2R x) 511 ltac:(lia) Hxlo Hxhi).
  rewrite <- Hs in Hb. change (2 * 511)%Z with 1022%Z in Hb.
  destruct Hb as ((Hslo & Hshi) & (Hsslo & Hsshi)).
  assert (HM : bpow radix2 1022 <= MAX) by (cbn [bpow radix_val radix2]; lra).
  assert (Hss : Rabs (B2R s * B2R s) = B2R s * B2R s)
    by (apply Rabs_pos_eq; lra).
  (* [p = RN(s * s)], and [s * s <= 2^1022] does not overflow. *)
  assert (Hsp : Rabs (B2R s * B2R s) <= MAX) by (rewrite Hss; lra).
  destruct (mul_below_max s s Fs Fs Hsp) as (Fp & Hp & _).
  (* [e = s * s - p] exactly, by Dekker's TwoProduct: [s <= 2^511 < 2^996]
     and [2^-969 <= 2^-966 <= s * s <= 2^1022 < 2^1023]. *)
  assert (Hs996 : Rabs (B2R s) < bpow radix2 996).
  { rewrite Rabs_pos_eq by lra.
    apply Rle_lt_trans with (bpow radix2 511); [exact Hshi | apply bpow_lt; lia]. }
  assert (Hlo969 : bpow radix2 (-969) <= Rabs (B2R s * B2R s)).
  { rewrite Hss.
    apply Rle_trans with (bpow radix2 (-966)); [apply bpow_le; lia | exact Hsslo]. }
  assert (Hhi1023 : Rabs (B2R s * B2R s) < bpow radix2 1023).
  { rewrite Hss.
    apply Rle_lt_trans with (bpow radix2 1022); [exact Hsshi | apply bpow_lt; lia]. }
  destruct (two_prod_err_dekker s s Fs Fs Hs996 Hs996 Fp Hp Hlo969 Hhi1023)
    as (Fe & He).
  set (p := mul s s) in *.
  set (e := Generic.two_prod_err false s s p) in *.
  (* The relative errors: [|s - sqrt x| <= 2^-53 * sqrt x], as
     [sqrt x >= 2^-483] is normal, and [|p - s * s| <= 2^-53 * s * s]. *)
  assert (Ha : 0 <= sqrt (B2R x)) by apply sqrt_pos.
  assert (Haa : sqrt (B2R x) * sqrt (B2R x) = B2R x) by (apply sqrt_sqrt; lra).
  assert (Ha1022 : bpow radix2 (-1022) <= sqrt (B2R x)).
  { apply Rle_trans with (bpow radix2 (-483)); [apply bpow_le; lia |].
    rewrite <- (sqrt_bpow radix2 (-483)).
    apply sqrt_le_1_alt. exact Hxlo. }
  pose proof (RN_rel (sqrt (B2R x))) as E1.
  rewrite (Rabs_pos_eq (sqrt (B2R x))) in E1 by exact Ha.
  rewrite <- Hs in E1. specialize (E1 Ha1022).
  assert (Hss1022 : bpow radix2 (-1022) <= B2R s * B2R s).
  { apply Rle_trans with (bpow radix2 (-966)); [apply bpow_le; lia | exact Hsslo]. }
  pose proof (RN_rel (B2R s * B2R s)) as E2.
  rewrite Hss, <- Hp in E2. specialize (E2 Hss1022).
  apply Rabs_le_inv in E1. apply Rabs_le_inv in E2.
  assert (Hu : 0 < bpow radix2 (-53) <= / 8).
  { split; [apply bpow_gt_0|].
    apply Rle_trans with (bpow radix2 (-3)); [apply bpow_le; lia|].
    change (bpow radix2 (-3)) with (/ 8). lra. }
  set (a := sqrt (B2R x)) in *.
  set (u := bpow radix2 (-53)) in *.
  assert (Hss0 : 0 <= B2R s * B2R s) by lra.
  (* With [u <= 1/8]: [7/8 sqrt x <= s <= 9/8 sqrt x], so
     [49/64 x <= s * s <= 81/64 x], and [7/8 s * s <= p <= 9/8 s * s]. *)
  assert (S1 : 7/8 * a <= B2R s <= 9/8 * a) by (split; nra).
  assert (S2 : 49/64 * (a * a) <= B2R s * B2R s <= 81/64 * (a * a))
    by (split; nra).
  assert (P : 7/8 * (B2R s * B2R s) <= B2R p <= 9/8 * (B2R s * B2R s))
    by (split; nra).
  (* So [343/512 x <= p <= 729/512 x], and Sterbenz's lemma applies. *)
  assert (Hst : B2R p / 2 <= B2R x <= 2 * B2R p) by lra.
  assert (Fxp : format (B2R x - B2R p)).
  { apply sterbenz;
      [typeclasses eauto .. | apply generic_format_B2R | apply generic_format_B2R
      | exact Hst]. }
  (* [x - p] is exact, and [|x - p| <= x < 2^1022]. *)
  assert (Hxp : Rabs (B2R x - B2R p) <= MAX) by (apply Rabs_le; split; lra).
  destruct (sub_below_max x p Fx Fp Hxp) as (Fq & Hq & _).
  rewrite round_generic in Hq by first [exact Fxp | typeclasses eauto].
  set (q := sub x p) in *.
  (* [q - e = x - s * s], which is a float and at most [2^1022] in
     magnitude. *)
  assert (Hqe : Rabs (B2R q - B2R e) <= MAX).
  { rewrite Hq, He. apply Rabs_le. split; lra. }
  destruct (sub_below_max q e Fq Fe Hqe) as (Fr & Hr & _).
  rewrite Hq, He in Hr.
  replace (B2R x - B2R p - (B2R s * B2R s - B2R p))
    with (B2R x - B2R s * B2R s) in Hr by ring.
  rewrite round_generic in Hr by first [exact Hf | typeclasses eauto].
  split; [reflexivity|]. split; [exact Fs|]. split; [exact Hs|].
  split; [lra|]. split; [exact Fr | exact Hr].
Qed.
