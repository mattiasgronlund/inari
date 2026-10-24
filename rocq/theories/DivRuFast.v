(** * The remainder in [div1_ru_fast] is computed exactly

    [div1_ru_fast fma x y] computes [q = RN(x / y)] and the remainder
    [r = x - q * y], whose sign tells whether [q] is below [x / y]. With an
    FMA, [r = RN(x - q * y)] in one operation. Without one, [p = RN(q * y)],
    [e = q * y - p] exactly by Dekker's TwoProduct ([two_prod_err_dekker]),
    and [r = RN(RN(x - p) - e)].

    The exact remainder [x - q * y] is a float with
    [|x - q * y| <= 2^-52 |x|] if [q] is normal and [|x| >= 2^-967]
    (S. Boldo and M. Daumas, Representable correcting terms for possibly
    underflowing floating point operations, ARITH 16, 2003, [BD03]). That is
    [div_remainder], and [div_exact] shows that the bounds the code checks
    on the exponents of [q] and [x] are those it needs. The other lemmas
    take it as a hypothesis, and show that the code then computes the
    remainder exactly:
    - With an FMA, [x - q * y] is a float of magnitude at most [|x|], so it
      is its own rounding and does not overflow.
    - Without one, [q * y] is within [2^-52 |x|] of [x], so [p] is within
      about [2^-51 |x|] of [x] and [x - p] is exact by Sterbenz's lemma
      (P. H. Sterbenz, Floating-point computation, 1974). Then
      [(x - p) - e = x - q * y] is a float, so the last subtraction is
      exact too. The bounds on the exponents of [x], [q] and [y] keep every
      operation below the largest float and are what [two_prod_err_dekker]
      needs. *)

From Stdlib Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Relative Sterbenz.
From Inari Require Import Model Encoding TwoSum TwoProduct DivRemainder.

Open Scope R_scope.

Local Notation format := (generic_format radix2 fexp64).

(** ** The quotient *)

(** If [x / y] is finite, it is [RN(x / y)], because an overflow when
    rounding to nearest gives an infinity. *)
Lemma div_B2R :
  forall x y, is_finite x = true -> is_finite y = true -> B2R y <> 0 ->
  is_finite (div x y) = true -> B2R (div x y) = RN (B2R x / B2R y).
Proof.
intros x y _ _ Hy Fq.
generalize (@Bdiv_correct 53 1024 _ _ mode_NE x y Hy).
destruct (Rlt_bool _ _).
- intros (HR & _). exact HR.
- intros HO. exfalso.
  revert Fq HO. unfold div.
  destruct (Bdiv mode_NE x y); intros F HO; discriminate.
Qed.

(** The bounds that [div1_ru_fast] checks, [-1022 <= exponent q <= 1023]
    and [-967 <= exponent x], make [q] finite and normal and
    [|x| >= 2^-967], so [div_remainder] applies. *)
Lemma div_exact :
  forall x y, is_finite x = true -> is_finite y = true ->
  B2R x <> 0 -> B2R y <> 0 ->
  (-1022 <= Generic.exponent (div x y) <= 1023)%Z ->
  (-967 <= Generic.exponent x)%Z ->
  is_finite (div x y) = true /\ B2R (div x y) = RN (B2R x / B2R y) /\
  B2R (div x y) <> 0 /\
  format (B2R x - B2R (div x y) * B2R y) /\
  Rabs (B2R x - B2R (div x y) * B2R y) <= bpow radix2 (-52) * Rabs (B2R x) /\
  bpow radix2 (-967) <= Rabs (B2R x).
Proof.
intros x y Fx Fy Hx0 Hy0 Eq Ex.
(* [Generic.is_finite q] is [exponent q < 1024]. *)
assert (Fq : is_finite (div x y) = true).
{ rewrite <- is_finite_eq. unfold Generic.is_finite. apply Z.ltb_lt. lia. }
pose proof (div_B2R x y Fx Fy Hy0 Fq) as Hq.
(* [|q| >= 2^exponent q >= 2^-1022] and [|x| >= 2^exponent x >= 2^-967]. *)
assert (Eq' : (-1022 <= Generic.exponent (div x y))%Z) by lia.
assert (Ex' : (-1022 <= Generic.exponent x)%Z) by lia.
assert (Hqlo : bpow radix2 (-1022) <= Rabs (B2R (div x y))).
{ apply Rle_trans with (2 := bpow_exponent_le_abs_B2R _ Fq Eq').
  apply bpow_le. lia. }
assert (Hxlo : bpow radix2 (-967) <= Rabs (B2R x)).
{ apply Rle_trans with (2 := bpow_exponent_le_abs_B2R _ Fx Ex').
  apply bpow_le. lia. }
assert (Hq0 : B2R (div x y) <> 0).
{ intros H0. rewrite H0, Rabs_R0 in Hqlo.
  pose proof (bpow_gt_0 radix2 (-1022)). lra. }
rewrite Hq in Hqlo.
assert (Fx' : format (B2R x)) by apply generic_format_B2R.
assert (Fy' : format (B2R y)) by apply generic_format_B2R.
destruct (div_remainder (B2R x) (B2R y) Fx' Fy' Hy0 Hqlo Hxlo)
  as (Fr & Hr).
rewrite <- Hq in Fr, Hr.
repeat split; assumption.
Qed.

(** ** With an FMA *)

(** [x - q * y] is a float of magnitude at most [|x|], so the FMA computes
    it exactly. *)
Lemma div_fma_remainder :
  forall q y x, is_finite q = true -> is_finite y = true -> is_finite x = true ->
  format (B2R x - B2R q * B2R y) ->
  Rabs (B2R x - B2R q * B2R y) <= Rabs (B2R x) ->
  is_finite (mul_add (opp q) y x) = true /\
  B2R (mul_add (opp q) y x) = B2R x - B2R q * B2R y.
Proof.
intros q y x Fq Fy Fx Fr Hr.
assert (Fo : is_finite (opp q) = true)
  by (unfold opp; rewrite is_finite_Bopp; exact Fq).
generalize (@Bfma_correct 53 1024 _ _ mode_NE (opp q) y x Fo Fy Fx).
cbv zeta.
replace (B2R (opp q) * B2R y + B2R x) with (B2R x - B2R q * B2R y)
  by (unfold opp; rewrite B2R_Bopp; ring).
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE)) with RN.
rewrite (round_generic _ _ _ _ Fr).
rewrite Rlt_bool_true.
2: { apply Rle_lt_trans with (1 := Hr). apply abs_B2R_lt_emax. }
intros (HR & HF & _).
split; [exact HF | exact HR].
Qed.

(** ** Without an FMA *)

(** If [b] is within [e |a|] of [a], then [|b|] is within [e |a|] of
    [|a|]. *)
Lemma Rabs_close_rel :
  forall a b e, Rabs (a - b) <= e * Rabs a ->
  (1 - e) * Rabs a <= Rabs b <= (1 + e) * Rabs a.
Proof.
intros a b e H.
pose proof (Rabs_triang_inv a b) as H1.
pose proof (Rabs_triang_inv b a) as H2.
rewrite Rabs_minus_sym in H2.
split; lra.
Qed.

(** Sterbenz's lemma, for floats of either sign: if [b] is within
    [|a| / 2] of [a], then [b] lies in [[a / 2, 2 a]] (or [[2 a, a / 2]])
    and [a - b] is a float. *)
Lemma sterbenz_abs :
  forall a b, format a -> format b -> Rabs (a - b) <= / 2 * Rabs a ->
  format (a - b).
Proof.
intros a b Fa Fb H.
destruct (Rle_or_lt 0 a) as [Ha | Ha].
- rewrite (Rabs_pos_eq a Ha) in H. apply Rabs_le_inv in H.
  apply sterbenz; [typeclasses eauto .. | exact Fa | exact Fb | lra].
- rewrite (Rabs_left a Ha) in H. apply Rabs_le_inv in H.
  replace (a - b) with (- (- a - - b)) by ring.
  apply generic_format_opp.
  apply sterbenz;
    [typeclasses eauto .. | apply generic_format_opp; exact Fa
    | apply generic_format_opp; exact Fb | lra].
Qed.

(** [x - p] with [p = RN(q * y)] is exact by Sterbenz's lemma, and
    [(x - p) - e = x - q * y] with [e = q * y - p] from Dekker's
    TwoProduct is exact because it is a float. *)
Lemma div_dekker_remainder :
  forall x q y, is_finite x = true -> is_finite q = true -> is_finite y = true ->
  format (B2R x - B2R q * B2R y) ->
  Rabs (B2R x - B2R q * B2R y) <= bpow radix2 (-52) * Rabs (B2R x) ->
  bpow radix2 (-967) <= Rabs (B2R x) ->
  (Generic.exponent x <= 1021)%Z -> (Generic.exponent q <= 995)%Z ->
  (Generic.exponent y <= 995)%Z ->
  is_finite (sub (sub x (mul q y)) (Generic.two_prod_err false q y (mul q y)))
    = true /\
  B2R (sub (sub x (mul q y)) (Generic.two_prod_err false q y (mul q y))) =
    B2R x - B2R q * B2R y.
Proof.
intros x q y Fx Fq Fy Fr Hr Hlo Ex Eq Ey.
(* The magnitudes of the operands. *)
assert (Hx : Rabs (B2R x) < bpow radix2 1022).
{ apply Rlt_le_trans with (1 := abs_B2R_lt_exponent x Fx). apply bpow_le. lia. }
assert (Hq : Rabs (B2R q) < bpow radix2 996).
{ apply Rlt_le_trans with (1 := abs_B2R_lt_exponent q Fq). apply bpow_le. lia. }
assert (Hy : Rabs (B2R y) < bpow radix2 996).
{ apply Rlt_le_trans with (1 := abs_B2R_lt_exponent y Fy). apply bpow_le. lia. }
(* [|q * y|] is within [2^-52 |x|] of [|x|]. *)
destruct (Rabs_close_rel _ _ _ Hr) as (HQlo & HQhi).
(* The constants: [(1 - 2^-52) * 2^-967 >= 2^-969 >= 2^-1022], and
   [(1 + 2^-52) * 2^1022 < 2^1023 <= MAX]. *)
assert (HM : bpow radix2 (-1022) <= bpow radix2 (-969) <=
               (1 - bpow radix2 (-52)) * bpow radix2 (-967) /\
             (1 + bpow radix2 (-52)) * bpow radix2 1022 < bpow radix2 1023 /\
             0 <= bpow radix2 1022 <= bpow radix2 1023 /\
             bpow radix2 1023 <= MAX)
  by (cbn [bpow radix_val radix2]; lra).
assert (He52 : 0 < bpow radix2 (-52) < 1) by (cbn [bpow radix_val radix2]; lra).
(* So [2^-969 <= |q * y| < 2^1023]. *)
assert (HQ : bpow radix2 (-969) <= Rabs (B2R q * B2R y) < bpow radix2 1023).
{ split.
  - apply Rle_trans with (1 := proj2 (proj1 HM)).
    apply Rle_trans with (2 := HQlo).
    apply Rmult_le_compat_l; lra.
  - apply Rle_lt_trans with (1 := HQhi).
    apply Rle_lt_trans with (2 := proj1 (proj2 HM)).
    apply Rmult_le_compat_l; lra. }
(* [p = RN(q * y)] and [e = q * y - p]. *)
destruct (mul_below_max q y Fq Fy) as (Fp & Hp & _).
{ lra. }
destruct (two_prod_err_dekker q y Fq Fy Hq Hy Fp Hp (proj1 HQ) (proj2 HQ))
  as (Fe & He).
set (p := mul q y) in *. clearbody p.
set (e := Generic.two_prod_err false q y p) in *. clearbody e.
(* [p] is within [2^-53 |q * y|] of [q * y], as [|q * y| >= 2^-1022]. *)
assert (Hrel : Rabs (B2R p - B2R q * B2R y) <=
                 / 2 * bpow radix2 (-52) * Rabs (B2R q * B2R y)).
{ rewrite Hp.
  assert (H53 : (0 < 53)%Z) by lia.
  generalize (relative_error_N_FLT radix2 (-1074) 53 H53
    (fun z => negb (Z.even z)) (B2R q * B2R y)).
  change (-1074 + 53 - 1)%Z with (-1022)%Z.
  change (- 53 + 1)%Z with (-52)%Z.
  intros H. apply H. lra. }
(* So [|x - p| <= (2^-52 + 2^-53 (1 + 2^-52)) |x| <= |x| / 2]. *)
assert (Hxp : Rabs (B2R x - B2R p) <= / 2 * Rabs (B2R x)).
{ apply Rabs_le_inv in Hr. apply Rabs_le_inv in Hrel.
  apply Rabs_le.
  assert (/ 2 * bpow radix2 (-52) * Rabs (B2R q * B2R y) <=
            / 2 * bpow radix2 (-52) * ((1 + bpow radix2 (-52)) * Rabs (B2R x))).
  { apply Rmult_le_compat_l; [lra | exact HQhi]. }
  assert (bpow radix2 (-52) * Rabs (B2R x) +
            / 2 * bpow radix2 (-52) * ((1 + bpow radix2 (-52)) * Rabs (B2R x))
          <= / 2 * Rabs (B2R x)).
  { pose proof (Rabs_pos (B2R x)). cbn [bpow radix_val radix2]. lra. }
  lra. }
(* [x - p] is exact. *)
assert (Fxp : format (B2R x - B2R p))
  by (apply sterbenz_abs; [apply generic_format_B2R .. | exact Hxp]).
destruct (sub_below_max x p Fx Fp) as (Fs & Hs & _).
{ apply Rle_trans with (1 := Hxp). pose proof (Rabs_pos (B2R x)). lra. }
rewrite (round_generic _ _ _ _ Fxp) in Hs.
(* [(x - p) - e = x - q * y] is exact. *)
destruct (sub_below_max (sub x p) e Fs Fe) as (Fr' & Hr' & _).
{ rewrite Hs, He.
  replace (B2R x - B2R p - (B2R q * B2R y - B2R p))
    with (B2R x - B2R q * B2R y) by ring.
  apply Rle_trans with (1 := Hr).
  apply Rle_trans with (Rabs (B2R x)); [|lra].
  pose proof (Rabs_pos (B2R x)). nra. }
rewrite Hs, He in Hr'.
replace (B2R x - B2R p - (B2R q * B2R y - B2R p))
  with (B2R x - B2R q * B2R y) in Hr' by ring.
rewrite (round_generic _ _ _ _ Fr) in Hr'.
split; [exact Fr' | exact Hr'].
Qed.
