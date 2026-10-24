(** * [mul_add1_rn_emulated] is the FMA rounded to nearest

    [mul_add1_rn_emulated u1 u2 c] computes [RN(a * b + c)] without an
    FMA, from [u1 = RN(a * b)] and its exact error [u2 = a * b - u1]. It
    is [BM08, Algorithm 1 and Theorem 4] (S. Boldo and G. Melquiond,
    Emulation of FMA and correctly rounded sums: proved algorithms using
    rounding to odd, IEEE Trans. Computers 57(4), 2008):

      (t1, t2) = TwoSum(c, u1)
      v = RO(t2 + u2)
      r = RN(t1 + v)

    where RO is rounding to odd, which [add_odd] computes from
    [RN(t2 + u2)] and its exact error by stepping to the neighbour with an
    odd bit pattern.

    Flocq proves that rounding to odd in a format with at least two more
    digits, then to nearest, is rounding to nearest ([round_N_odd]). BM08's
    argument reduces the emulated FMA to it: [t1 + (t2 + u2) = a * b + c]
    exactly, and if [y = t2 + u2] is not a float, then [|y| < 2 ulp(t1)],
    so [t1] is an even multiple of the ulp [2^k] of [y], and [t1 + RO(y)]
    is [a * b + c] rounded to odd at [2^k], which is at least 55 bits
    below its leading bit. [|y| < 2 ulp(t1)] holds as [|t2| <= ulp(t1)/2]
    and, unless [c + u1] is exact by Sterbenz's lemma, so that [t2 = 0],
    [|t1| >= |u1|/2] and [|u2| <= ulp(u1)/2 <= ulp(t1)].

    [RN_plus_RO] is that step, and [emulated_bound] the bound on [y].

    [mul_add1_rn_emulated_correct] puts them together: whenever the fast
    path of [mul_add_ru] accepts [a], [b] and [c] without an FMA and does
    not return [mul_add1_special a b c], the emulation returns
    [Bfma mode_NE a b c], the zero sign included. Of what [ok] checks, it
    uses only [two_prod_is_exact], which makes [u2] exact and
    [|u1| >= 2^-968], and [exponent(u1), exponent(c) <= 1021]. No other
    underflow hypothesis is needed: all the values are multiples of
    [2^-1074], and [y] is then a float if it is below [2^-1021]. With
    [|c|, |u1| < 2^1022], nothing overflows. A zero result is [+0], as the
    FMA's is: [a * b + c], a multiple of [2^-1074], is then exactly zero,
    so [c = -a * b] with [a * b <> 0], and [t1] and [v] are opposite
    nonzero floats or [t1 = +0]. *)

From Stdlib Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Round_odd Sterbenz
  Plus_error.
From Inari Require Import Model Encoding TwoSum TwoProduct StepUp MulRu AddOdd.

Open Scope R_scope.

(** Rounding to odd in binary64, without overflow. *)
Notation RO := (round radix2 fexp64 Zrnd_odd).

(** Binary64 has ties to even, which rounding to odd needs. *)
#[local] Instance exists_NE_fexp64 : Exists_NE radix2 fexp64.
Proof. apply exists_NE_FLT. right. lia. Qed.

(** ** Multiples of the smallest subnormal *)

(** Every float is a multiple of [2^-1074]. *)
Lemma format_multiple :
  forall x, generic_format radix2 fexp64 x ->
  exists m, x = IZR m * bpow radix2 (-1074).
Proof.
intros x Fx.
exists (Ztrunc (scaled_mantissa radix2 fexp64 x)
  * Zpower radix2 (cexp radix2 fexp64 x + 1074))%Z.
rewrite Fx at 1. unfold F2R; cbn [Fnum Fexp].
rewrite mult_IZR, IZR_Zpower by (unfold cexp, FLT_exp; lia).
rewrite Rmult_assoc, <- bpow_plus. do 2 f_equal. ring.
Qed.

(** A multiple of [2^-1074] below [2^-1021] is a float, a subnormal. *)
Lemma multiple_small_format :
  forall m, Rabs (IZR m * bpow radix2 (-1074)) < bpow radix2 (-1021) ->
  generic_format radix2 fexp64 (IZR m * bpow radix2 (-1074)).
Proof.
intros m H.
apply generic_format_FLT.
apply FLT_spec with (Float radix2 m (-1074)); [reflexivity | | cbn; lia].
cbn [Fnum].
assert (Hm : IZR (Z.abs m) < bpow radix2 53).
{ apply Rmult_lt_reg_r with (bpow radix2 (-1074)); [apply bpow_gt_0|].
  rewrite abs_IZR, <- bpow_plus.
  rewrite <- (Rabs_pos_eq (bpow radix2 (-1074))) at 1 by apply bpow_ge_0.
  rewrite <- Rabs_mult. exact H. }
rewrite <- IZR_Zpower in Hm by lia.
now apply lt_IZR.
Qed.

(** ** Rounding to odd, then to nearest *)

(** If [y] is a multiple of [2^-1074] that is a float or below [2 ulp(t)]
    in magnitude, then [RN(t + RO(y)) = RN(t + y)]. *)
Lemma RN_plus_RO :
  forall t y, generic_format radix2 fexp64 t ->
  (exists m, y = IZR m * bpow radix2 (-1074)) ->
  generic_format radix2 fexp64 y \/ Rabs y < 2 * ulp radix2 fexp64 t ->
  RN (t + RO y) = RN (t + y).
Proof.
intros t y Ft (m & Hm) Hy.
destruct (generic_format_EM radix2 fexp64 y) as [Fy|Fy].
{ now rewrite (round_generic _ _ _ _ Fy). }
destruct Hy as [Hy|Hy]; [easy|].
(* [y] is not a subnormal, so [|y| >= 2^-1021]. *)
assert (Hy1 : bpow radix2 (-1021) <= Rabs y).
{ apply Rnot_lt_le. intros H. apply Fy. rewrite Hm.
  apply multiple_small_format. now rewrite <- Hm. }
assert (Hy0 : y <> 0).
{ intros H0. rewrite H0, Rabs_R0 in Hy1.
  pose proof (bpow_gt_0 radix2 (-1021)). lra. }
(* Then [t] is not zero, whose ulp is [2^-1074]. *)
assert (Ht0 : t <> 0).
{ intros H0. rewrite H0, ulp_FLT_0 in Hy by easy.
  assert (2 * bpow radix2 (-1074) <= bpow radix2 (-1021)).
  { change 2 with (bpow radix2 1). rewrite <- bpow_plus. apply bpow_le. lia. }
  lra. }
rewrite ulp_neq_0 in Hy by exact Ht0.
replace (2 * bpow radix2 (cexp radix2 fexp64 t))
  with (bpow radix2 (cexp radix2 fexp64 t + 1)) in Hy
  by (rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
assert (My := mag_le_bpow radix2 y _ Hy0 Hy).
assert (My1 : (-1020 <= mag radix2 y)%Z).
{ apply mag_ge_bpow. exact Hy1. }
(* So [t] is normal: [cexp(t) = mag(t) - 53]. *)
assert (Et : cexp radix2 fexp64 t = (mag radix2 t - 53)%Z).
{ unfold cexp, FLT_exp in *. lia. }
rewrite Et in Hy, My.
(* [t + y] is at least [2^(mag(t) - 2)], as [|y| < 2^(mag(t) - 52)]. *)
assert (Mx : (mag radix2 t - 1 <= mag radix2 (t + y))%Z).
{ apply mag_ge_bpow.
  pose proof (bpow_mag_le radix2 t Ht0) as Ht.
  assert (H2 : bpow radix2 (mag radix2 t - 1) =
    2 * bpow radix2 (mag radix2 t - 1 - 1)).
  { change 2 with (bpow radix2 1). rewrite <- bpow_plus. f_equal. ring. }
  assert (H52 : bpow radix2 (mag radix2 t - 53 + 1) <=
    bpow radix2 (mag radix2 t - 1 - 1)) by (apply bpow_le; lia).
  assert (Rabs t - Rabs y <= Rabs (t + y))
    by (unfold Rabs; repeat destruct Rcase_abs; lra).
  lra. }
(* [RO(y)] rounds [y] to odd at [2^k], its ulp. *)
set (k := cexp radix2 fexp64 y).
assert (Ek : k = (mag radix2 y - 53)%Z) by (unfold k, cexp, FLT_exp; lia).
(* Rounding [t + y] to odd at [2^k] is rounding it to odd with [P] digits. *)
set (P := (mag radix2 (t + y) - k)%Z).
assert (HP : (55 <= P)%Z) by (unfold P; lia).
assert (Prec_gt_0 P) by (unfold Prec_gt_0; lia).
assert (HRO : t + RO y = round radix2 (FLX_exp P) Zrnd_odd (t + y)).
{ unfold round, F2R, scaled_mantissa. cbn [Fnum Fexp].
  replace (cexp radix2 (FLX_exp P) (t + y)) with k
    by (unfold cexp, FLX_exp, P; ring).
  fold k.
  (* [t] is [n * 2^k] for an even [n], as [cexp(t) > k]. *)
  set (n := (Ztrunc (scaled_mantissa radix2 fexp64 t)
    * Zpower radix2 (mag radix2 t - 53 - k))%Z).
  assert (Hn : t = IZR n * bpow radix2 k).
  { rewrite Ft at 1. unfold F2R, n; cbn [Fnum Fexp].
    rewrite Et, mult_IZR, IZR_Zpower by lia.
    rewrite Rmult_assoc, <- bpow_plus. do 2 f_equal. ring. }
  assert (Hev : Z.even n = true).
  { unfold n. rewrite Z.even_mul, Z.even_pow by lia.
    apply Bool.orb_true_r. }
  rewrite Rmult_plus_distr_r.
  replace (t * bpow radix2 (- k)) with (IZR n)
    by (rewrite Hn, Rmult_assoc, <- bpow_plus, Z.add_opp_diag_r, Rmult_1_r;
        reflexivity).
  rewrite Zrnd_odd_plus by (rewrite Zfloor_IZR; easy).
  rewrite Rmult_plus_distr_r, <- Hn. reflexivity. }
rewrite HRO.
assert (Exists_NE radix2 (FLX_exp P)) by (apply exists_NE_FLX; right; lia).
apply round_N_odd;
  [reflexivity | typeclasses eauto .. | intros e; unfold FLX_exp, FLT_exp; lia].
Qed.

(** ** The bound on [t2 + u2] *)

(** [BM08, proof of Theorem 4]: with [t1 = RN(c + u1)] and its error
    [t2 = c + u1 - t1], [t2 + u2] is a float or below [2 ulp(t1)] in
    magnitude, when [u1] is normal and [|u2| <= ulp(u1)/2], as for
    [u1 = RN(a * b)] and [u2 = a * b - u1]. This is the third hypothesis
    of [RN_plus_RO] for [t = t1] and [y = t2 + u2]. *)
Lemma emulated_bound :
  forall c u1 u2,
  generic_format radix2 fexp64 c -> generic_format radix2 fexp64 u1 ->
  generic_format radix2 fexp64 u2 ->
  bpow radix2 (-1022) <= Rabs u1 ->
  Rabs u2 <= /2 * ulp radix2 fexp64 u1 ->
  generic_format radix2 fexp64 (c + u1 - RN (c + u1) + u2) \/
  Rabs (c + u1 - RN (c + u1) + u2) < 2 * ulp radix2 fexp64 (RN (c + u1)).
Proof.
intros c u1 u2 Fc Fu1 Fu2 Hu1 Hu2.
destruct (generic_format_EM radix2 fexp64 (c + u1)) as [Fs|Fs].
{ (* [c + u1] is a float, so [t2 = 0] and [t2 + u2 = u2]. *)
  left. rewrite (round_generic _ _ _ _ Fs).
  replace (c + u1 - (c + u1) + u2) with u2 by ring. exact Fu2. }
right.
assert (Hu0 : u1 <> 0).
{ intros H0. rewrite H0, Rabs_R0 in Hu1.
  pose proof (bpow_gt_0 radix2 (-1022)). lra. }
(* Otherwise [|c + u1| >= |u1|/2]: if not, [c] and [-u1] are within a
   factor of 2 of each other, and [c + u1] is a float by Sterbenz's
   lemma. *)
assert (Hs : Rabs u1 / 2 <= Rabs (c + u1)).
{ apply Rnot_lt_le. intros Hlt. apply Fs.
  destruct (Rle_or_lt 0 u1) as [Hp|Hn].
  - rewrite (Rabs_pos_eq u1) in Hlt by exact Hp.
    destruct (Rabs_def2 _ _ Hlt).
    replace (c + u1) with (- (- c - u1)) by ring.
    apply generic_format_opp, sterbenz;
      [typeclasses eauto .. | now apply generic_format_opp | exact Fu1 | lra].
  - rewrite (Rabs_left u1) in Hlt by exact Hn.
    destruct (Rabs_def2 _ _ Hlt).
    replace (c + u1) with (c - - u1) by ring.
    apply sterbenz;
      [typeclasses eauto .. | exact Fc | now apply generic_format_opp | lra]. }
(* So [|t1| >= 2^(mag(u1) - 2)], which is a float, as [u1] is normal. *)
assert (Mu : (-1021 <= mag radix2 u1)%Z) by (apply mag_ge_bpow; exact Hu1).
assert (Ht : bpow radix2 (mag radix2 u1 - 2) <= Rabs (RN (c + u1))).
{ apply abs_round_ge_generic; [typeclasses eauto .. | |].
  - apply generic_format_FLT_bpow; [typeclasses eauto | lia].
  - pose proof (bpow_mag_le radix2 u1 Hu0).
    assert (bpow radix2 (mag radix2 u1 - 1) =
      2 * bpow radix2 (mag radix2 u1 - 2)).
    { change 2 with (bpow radix2 1). rewrite <- bpow_plus. f_equal. ring. }
    lra. }
assert (Ht0 : RN (c + u1) <> 0).
{ intros H0. rewrite H0, Rabs_R0 in Ht.
  pose proof (bpow_gt_0 radix2 (mag radix2 u1 - 2)). lra. }
assert (Mt : (mag radix2 u1 - 1 <= mag radix2 (RN (c + u1)))%Z).
{ apply mag_ge_bpow.
  replace (mag radix2 u1 - 1 - 1)%Z with (mag radix2 u1 - 2)%Z by ring.
  exact Ht. }
(* Then [ulp(u1) <= 2 ulp(t1)], as [ulp(u1) = 2^(mag(u1) - 53)]. *)
assert (Hulp : ulp radix2 fexp64 u1 <= 2 * ulp radix2 fexp64 (RN (c + u1))).
{ rewrite 2!ulp_neq_0 by assumption.
  change 2 with (bpow radix2 1). rewrite <- bpow_plus. apply bpow_le.
  (* [FLT_exp] also occurs in [RN], so unfold it in [Mt] too. *)
  unfold cexp. unfold FLT_exp in Mt |- *. lia. }
assert (Hpos : 0 < ulp radix2 fexp64 (RN (c + u1)))
  by (rewrite ulp_neq_0 by exact Ht0; apply bpow_gt_0).
(* [|t2| <= ulp(t1)/2] and [|u2| <= ulp(t1)], so
   [|t2 + u2| <= 3/2 ulp(t1)]. *)
pose proof (error_le_half_ulp_round radix2 fexp64
  (fun x => negb (Z.even x)) (c + u1)) as He.
rewrite Rabs_minus_sym in He.
pose proof (Rabs_triang (c + u1 - RN (c + u1)) u2).
lra.
Qed.

(** ** Zeros *)

(** A multiple of [2^-1074] that rounds to zero is zero, as [2^-1074] is a
    float. *)
Lemma RN_multiple_eq_0 :
  forall m, RN (IZR m * bpow radix2 (-1074)) = 0 ->
  IZR m * bpow radix2 (-1074) = 0.
Proof.
intros m H.
destruct (Z.eq_dec m 0) as [->|Hm]; [ring|].
exfalso.
pose proof (bpow_gt_0 radix2 (-1074)) as Hb.
assert (H1 : bpow radix2 (-1074) <= Rabs (IZR m * bpow radix2 (-1074))).
{ rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)) by lra.
  rewrite <- abs_IZR.
  assert (1 <= IZR (Z.abs m)) by (apply IZR_le; lia).
  nra. }
assert (H2 : bpow radix2 (-1074) <= Rabs (RN (IZR m * bpow radix2 (-1074)))).
{ apply abs_round_ge_generic; [typeclasses eauto .. | | exact H1].
  apply generic_format_FLT_bpow; [typeclasses eauto | lia]. }
rewrite H, Rabs_R0 in H2. lra.
Qed.

(** A sum that is exactly zero is the zero with the sign
    [Bsign x && Bsign y]: rounding to nearest gives [+0] unless both
    operands are [-0]. *)
Lemma add_zero_sign :
  forall x y : f64, is_finite x = true -> is_finite y = true ->
  B2R x + B2R y = 0 ->
  is_finite (add x y) = true /\ B2R (add x y) = 0 /\
  Bsign (add x y) = Bsign x && Bsign y.
Proof.
intros x y Fx Fy H0.
generalize (@Bplus_correct 53 1024 _ _ mode_NE x y Fx Fy).
rewrite H0, round_0, Rabs_R0, Rlt_bool_true, Rcompare_Eq
  by first [apply bpow_gt_0 | reflexivity | typeclasses eauto].
intros (HR & HF & HS).
split; [exact HF|]. split; [exact HR | exact HS].
Qed.

(** Two finite floats with a nonzero sum of zero have opposite signs. *)
Lemma Bsign_andb_opp :
  forall x y : f64, is_finite x = true -> is_finite y = true ->
  B2R x + B2R y = 0 -> B2R x <> 0 -> Bsign x && Bsign y = false.
Proof.
intros x y Fx Fy H0 Hx.
assert (Hy : B2R y <> 0) by (intros H; apply Hx; lra).
rewrite (Bsign_B2R x Fx Hx), (Bsign_B2R y Fy Hy).
destruct (Rdichotomy _ _ Hx) as [Hl|Hl].
- rewrite (Rlt_bool_false (B2R y)) by lra. apply Bool.andb_false_r.
- rewrite (Rlt_bool_false (B2R x)) by lra. reflexivity.
Qed.

(** ** [mul_add1_rn_emulated] *)

(** Without an FMA, [mul_add1_ru_fast] computes [r1 = RN(a * b + c)] with
    [mul_add1_rn_emulated], which is [Bfma mode_NE a b c] whenever the
    fast path accepts the operands and does not return
    [mul_add1_special a b c], including the sign of a zero. (If an operand
    is +-inf, the emulation can return NaN.) Of what [ok] checks, it uses
    only [two_prod_is_exact], which makes [u2] the exact error of
    [u1 = RN(a * b)] and [|u1| >= 2^-968], and
    [exponent(u1), exponent(c) <= 1021]. *)
Theorem mul_add1_rn_emulated_correct :
  forall a b c : f64,
  negb (Generic.is_finite a && Generic.is_finite b && Generic.is_finite c)
    || eq a zero || eq b zero = false ->
  snd (Generic.mul_add1_ru_fast false a b c) = true ->
  Generic.mul_add1_rn_emulated (mul a b)
    (Generic.two_prod_err false a b (mul a b)) c = Bfma mode_NE a b c.
Proof.
intros a b c Hsp Hok.
unfold Generic.mul_add1_ru_fast in Hok. cbv zeta in Hok. cbn [snd] in Hok.
rewrite Hsp in Hok. cbn [orb] in Hok.
(* Of [ok], only [two_prod_is_exact] and the bounds on [u1] and [c] are
   needed. The [not_tiny] checks are ErrFma's, and MulAddRuFast.v does not
   need [is_finite r1] either: the bounds imply it. *)
apply andb_prop in Hok as [Hok _]. apply andb_prop in Hok as [Hok _].
apply andb_prop in Hok as [Hok _]. apply andb_prop in Hok as [Hok _].
apply andb_prop in Hok as [Hok Ec]. apply andb_prop in Hok as [Hex Eu].
apply Z.leb_le in Ec, Eu.
apply Bool.orb_false_elim in Hsp as [Hsp _].
apply Bool.orb_false_elim in Hsp as [Hf _].
rewrite !is_finite_eq in Hf.
apply Bool.negb_false_iff, andb_prop in Hf as [Hf Fc].
apply andb_prop in Hf as [Fa Fb].
assert (He : (-968 <= Generic.exponent (mul a b))%Z).
{ unfold Generic.two_prod_is_exact in Hex. cbv beta iota zeta in Hex.
  apply andb_prop in Hex as [Hex _]. apply andb_prop in Hex as [Hex _].
  apply andb_prop in Hex as [Hex _]. now apply Z.leb_le in Hex. }
assert (He' : (-968 <= Generic.exponent (mul a b) <= 1023)%Z) by lia.
destruct (mul_exponent_bounds a b Fa Fb He') as (_ & _ & _ & _ & Hab).
destruct (two_prod_err_correct false a b Fa Fb Hex)
  as (Fu1 & Hu1 & Hu10 & Fu2 & Hu2).
assert (He'' : (-1022 <= Generic.exponent (mul a b))%Z) by lia.
pose proof (bpow_exponent_le_abs_B2R (mul a b) Fu1 He'') as Hu1lo.
pose proof (abs_B2R_lt_exponent (mul a b) Fu1) as Hu1hi.
pose proof (abs_B2R_lt_exponent c Fc) as Hchi.
unfold Generic.mul_add1_rn_emulated. cbv zeta.
set (u1 := mul a b) in *.
set (u2 := Generic.two_prod_err false a b u1) in *.
clear Hex He' He''.
assert (B1 : bpow radix2 (-1022) <= Rabs (B2R u1)).
{ apply Rle_trans with (2 := Hu1lo). apply bpow_le. lia. }
assert (B2 : Rabs (B2R u1) < bpow radix2 1022).
{ apply Rlt_le_trans with (1 := Hu1hi). apply bpow_le. lia. }
assert (B3 : Rabs (B2R c) < bpow radix2 1022).
{ apply Rlt_le_trans with (1 := Hchi). apply bpow_le. lia. }
assert (B4 : Rabs (B2R a * B2R b) < bpow radix2 1022).
{ apply Rlt_le_trans with (1 := Hab). apply bpow_le. lia. }
assert (HM : bpow radix2 1023 = 2 * bpow radix2 1022 /\
  bpow radix2 1024 = 2 * bpow radix2 1023 /\
  bpow radix2 972 = 2 * bpow radix2 971 /\ 0 < bpow radix2 971 /\
  8 * bpow radix2 971 <= bpow radix2 1022)
  by (cbn [bpow radix_val radix2]; lra).
destruct HM as (M1 & M2 & M3 & M4 & M5).
(* [|u2| <= ulp(u1)/2 <= 2^971], as [u1 = RN(a * b)]. *)
assert (U2 : Rabs (B2R u2) <= /2 * ulp radix2 fexp64 (B2R u1)).
{ rewrite Hu2, <- Rabs_Ropp, Hu1.
  replace (- (B2R a * B2R b - RN (B2R a * B2R b)))
    with (RN (B2R a * B2R b) - B2R a * B2R b) by ring.
  apply error_le_half_ulp_round; typeclasses eauto. }
assert (U2' : Rabs (B2R u2) <= bpow radix2 971).
{ rewrite Hu2, <- Rabs_Ropp, Hu1.
  replace (- (B2R a * B2R b - RN (B2R a * B2R b)))
    with (RN (B2R a * B2R b) - B2R a * B2R b) by ring.
  apply RN_error. lra. }
(* [t1 = RN(c + u1)] and [t2 = c + u1 - t1], with [|t2| <= 2^971]. *)
assert (Hcu : Rabs (B2R c + B2R u1) < bpow radix2 1023).
{ pose proof (Rabs_triang (B2R c) (B2R u1)). lra. }
destruct (add_no_overflow c u1 Fc Fu1) as (Ft1 & Ht1); [lra|].
assert (Hc1023 : Rabs (B2R c) < bpow radix2 1023) by lra.
assert (Hu1023 : Rabs (B2R u1) < bpow radix2 1023) by lra.
destruct (two_sum_err_correct c u1 Fc Fu1 Hc1023 Hu1023 Ft1) as (Ft2 & Ht2).
set (t1 := add c u1) in *.
set (t2 := Generic.two_sum_err c u1 t1) in *.
assert (T1 : Rabs (B2R t1) <= bpow radix2 1023).
{ rewrite Ht1. apply abs_round_le_generic; [typeclasses eauto .. | | lra].
  apply generic_format_FLT_bpow; [typeclasses eauto | lia]. }
assert (T2 : Rabs (B2R t2) <= bpow radix2 971).
{ rewrite Ht2, Ht1, <- Rabs_Ropp.
  replace (- (B2R c + B2R u1 - RN (B2R c + B2R u1)))
    with (RN (B2R c + B2R u1) - (B2R c + B2R u1)) by ring.
  apply RN_error. lra. }
(* [v = RO(t2 + u2)], with [|v| <= 2^972]. *)
assert (Hs2 : Rabs (B2R t2 + B2R u2) <= bpow radix2 972).
{ pose proof (Rabs_triang (B2R t2) (B2R u2)). lra. }
destruct (add_no_overflow t2 u2 Ft2 Fu2) as (Fs2 & _); [lra|].
assert (Ht2' : Rabs (B2R t2) < bpow radix2 1023) by lra.
assert (Hu2' : Rabs (B2R u2) < bpow radix2 1023) by lra.
destruct (add_odd_correct t2 u2 Ft2 Fu2 Ht2' Hu2' Fs2) as (Fv & Hv).
assert (V : Rabs (B2R (Generic.add_odd t2 u2)) <= bpow radix2 972).
{ rewrite Hv. apply abs_round_le_generic; [typeclasses eauto .. | | exact Hs2].
  apply generic_format_FLT_bpow; [typeclasses eauto | lia]. }
set (v := Generic.add_odd t2 u2) in *.
(* [r = RN(t1 + v)] does not overflow. *)
destruct (add_below_max t1 v Ft1 Fv) as (Fr & Hr & _).
{ pose proof (Rabs_triang (B2R t1) (B2R v)). lra. }
(* [r = RN(t1 + RO(t2 + u2)) = RN(t1 + t2 + u2) = RN(a * b + c)]. *)
assert (HR : B2R (add t1 v) = RN (B2R a * B2R b + B2R c)).
{ rewrite Hr, Hv, RN_plus_RO.
  - f_equal. rewrite Ht2, Hu2. ring.
  - apply generic_format_B2R.
  - destruct (format_multiple _ (generic_format_B2R _ _ t2)) as (m2 & Hm2).
    destruct (format_multiple _ (generic_format_B2R _ _ u2)) as (m3 & Hm3).
    exists (m2 + m3)%Z. rewrite Hm2, Hm3, plus_IZR. ring.
  - rewrite Ht2, Ht1.
    apply emulated_bound; [apply generic_format_B2R .. | exact B1 | exact U2]. }
(* [Bfma] rounds [a * b + c] to nearest without overflow too. *)
assert (Hz : Rabs (B2R a * B2R b + B2R c) <= bpow radix2 1023 + bpow radix2 971).
{ pose proof (Rabs_triang (B2R a * B2R b) (B2R c)). lra. }
pose proof (@Bfma_correct 53 1024 _ _ mode_NE a b c Fa Fb Fc) as HF.
cbv zeta in HF.
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE)) with RN in HF.
rewrite Rlt_bool_true in HF by exact (RN_no_overflow _ Hz).
destruct HF as (HFR & HFF & HFS).
apply B2R_Bsign_inj; [exact Fr | exact HFF | congruence |].
destruct (Req_dec (B2R (add t1 v)) 0) as [Hr0|Hr0].
2: { rewrite (Bsign_B2R _ Fr Hr0), (Bsign_B2R _ HFF) by congruence.
     rewrite HR, HFR. reflexivity. }
(* A zero result: [a * b + c] is a multiple of [2^-1074] that rounds to
   zero, so it is zero. *)
assert (Hz0 : B2R a * B2R b + B2R c = 0).
{ destruct (format_multiple _ (generic_format_B2R _ _ u1)) as (m1 & Hm1).
  destruct (format_multiple _ (generic_format_B2R _ _ u2)) as (m2 & Hm2).
  destruct (format_multiple _ (generic_format_B2R _ _ c)) as (m3 & Hm3).
  assert (Hm : B2R a * B2R b + B2R c =
    IZR (m1 + m2 + m3) * bpow radix2 (-1074)).
  { rewrite 2!plus_IZR, 2!Rmult_plus_distr_r, <- Hm1, <- Hm2, <- Hm3, Hu2.
    ring. }
  rewrite Hm. apply RN_multiple_eq_0. rewrite <- Hm, <- HR. exact Hr0. }
(* Then [c = -a * b <> 0], so [Bfma] gives [+0]. *)
assert (Hab0 : B2R a * B2R b <> 0).
{ intros H0. apply Hu10. rewrite Hu1, H0. apply round_0. typeclasses eauto. }
assert (Ha0 : B2R a <> 0) by (intros H0; apply Hab0; rewrite H0; ring).
assert (Hb0 : B2R b <> 0) by (intros H0; apply Hab0; rewrite H0; ring).
assert (Hc0 : B2R c <> 0) by (intros H0; apply Hab0; lra).
rewrite Hz0, Rcompare_Eq in HFS by reflexivity.
assert (Hsz : Bfma_szero 53 1024 mode_NE a b c = false).
{ unfold Bfma_szero.
  rewrite (Bsign_B2R a Fa Ha0), (Bsign_B2R b Fb Hb0), (Bsign_B2R c Fc Hc0).
  rewrite <- Rlt_bool_mult by assumption.
  destruct (Rdichotomy _ _ Hab0) as [Hl|Hl].
  - rewrite (Rlt_bool_true _ _ Hl), (Rlt_bool_false (B2R c)) by lra.
    reflexivity.
  - rewrite (Rlt_bool_false (B2R a * B2R b)), (Rlt_bool_true (B2R c)) by lra.
    reflexivity. }
rewrite HFS, Hsz.
(* [r] is [+0] too: [t1 + v = 0] exactly, as it rounds to zero, and [t1]
   and [v] have opposite signs unless [t1 = +0]. *)
assert (Htv : B2R t1 + B2R v = 0).
{ destruct (Req_dec (B2R t1 + B2R v) 0) as [H|H]; [exact H|].
  exfalso.
  apply (round_plus_neq_0 radix2 fexp64 ZnearestE (B2R t1) (B2R v));
    [apply generic_format_B2R .. | exact H |].
  rewrite <- Hr. exact Hr0. }
rewrite (proj2 (proj2 (add_zero_sign t1 v Ft1 Fv Htv))).
destruct (Req_dec (B2R t1) 0) as [Ht0|Ht0].
2: exact (Bsign_andb_opp t1 v Ft1 Fv Htv Ht0).
(* If [t1 = 0], then [c + u1 = 0] exactly, and [c] and [u1] have opposite
   signs, so [t1 = +0]. *)
assert (Hcu0 : B2R c + B2R u1 = 0).
{ destruct (Req_dec (B2R c + B2R u1) 0) as [H|H]; [exact H|].
  exfalso.
  apply (round_plus_neq_0 radix2 fexp64 ZnearestE (B2R c) (B2R u1));
    [apply generic_format_B2R .. | exact H |].
  rewrite <- Ht1. exact Ht0. }
assert (Hs1 : Bsign t1 = Bsign c && Bsign u1)
  by exact (proj2 (proj2 (add_zero_sign c u1 Fc Fu1 Hcu0))).
rewrite Hs1, (Bsign_andb_opp c u1 Fc Fu1 Hcu0 Hc0).
reflexivity.
Qed.
