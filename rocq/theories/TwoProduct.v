(** * [two_prod_err] is exact in binary64

    [two_prod_err fma x y p] with [p = RN(x * y)] computes the exact error
    [e = x * y - p] of the multiplication, if [two_prod_is_exact] holds.
    With an FMA, [e = RN(x * y - p)], and [e] is a float
    ([mult_error_FLT]). Without one, it is Dekker's TwoProduct
    (T. J. Dekker, A floating-point technique for extending the available
    precision, Numer. Math. 18, 1971): Veltkamp's [split] cuts [x] and [y]
    into halves of 26 bits, whose products are exact, and four additions
    gather the error.

    Flocq proves both for formats with subnormals and no largest exponent:
    [mult_error_FLT], and [Pff2Flocq.Dekker] and [Pff2Flocq.Veltkamp] from
    Boldo's Pff library (S. Boldo, Pitfalls of a full floating-point proof:
    example on the formal proof of the Veltkamp/Dekker algorithms, IJCAR
    2006). They need [|x * y| >= 2^-969]. What is left to prove here is that
    [two_prod_is_exact] implies that bound and that no operation overflows. *)

From Stdlib Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Mult_error Relative.
From Flocq Require Pff.Pff2Flocq.
From Inari Require Import Model Encoding Decompose TwoSum.

Open Scope R_scope.

(** ** One operation at a time *)

(** [MAX], the largest finite float. *)
Notation MAX := (bpow radix2 1024 - bpow radix2 971).

Lemma format_MAX : generic_format radix2 fexp64 MAX.
Proof.
apply generic_format_FLT.
apply FLT_spec with (Float radix2 (2^53 - 1) 971).
- unfold F2R; cbn [Fnum Fexp]. rewrite minus_IZR.
  cbn [bpow radix_val radix2]. lra.
- cbn [Fnum]. simpl Z.pow. lia.
- cbn [Fexp]. lia.
Qed.

(** Rounding a value of at most [MAX] in magnitude to nearest does not
    overflow, and moves it by at most [2^971]. *)
Lemma RN_below_max :
  forall z, Rabs z <= MAX ->
  Rabs (RN z) < bpow radix2 1024 /\ Rabs (RN z - z) <= bpow radix2 971.
Proof.
intros z Hz.
pose proof (bpow_gt_0 radix2 971).
split.
- apply Rle_lt_trans with MAX; [|lra].
  apply abs_round_le_generic; [typeclasses eauto .. | exact format_MAX | exact Hz].
- apply RN_error. lra.
Qed.

(** [x * y], [x - y] and [x + y] are finite and rounded to nearest if the
    exact result is at most [MAX] in magnitude. *)
Lemma mul_below_max :
  forall x y, is_finite x = true -> is_finite y = true ->
  Rabs (B2R x * B2R y) <= MAX ->
  is_finite (mul x y) = true /\ B2R (mul x y) = RN (B2R x * B2R y) /\
  Rabs (B2R (mul x y) - B2R x * B2R y) <= bpow radix2 971.
Proof.
intros x y Fx Fy H.
destruct (RN_below_max _ H) as (Hlt & He).
generalize (@Bmult_correct 53 1024 _ _ mode_NE x y).
rewrite Rlt_bool_true by exact Hlt.
intros (HR & HF & _). rewrite Fx, Fy in HF.
change (Bmult mode_NE x y) with (mul x y) in HR, HF.
split; [exact HF|]. split; [exact HR|]. rewrite HR. exact He.
Qed.

Lemma sub_below_max :
  forall x y, is_finite x = true -> is_finite y = true ->
  Rabs (B2R x - B2R y) <= MAX ->
  is_finite (sub x y) = true /\ B2R (sub x y) = RN (B2R x - B2R y) /\
  Rabs (B2R (sub x y) - (B2R x - B2R y)) <= bpow radix2 971.
Proof.
intros x y Fx Fy H.
destruct (RN_below_max _ H) as (Hlt & He).
generalize (@Bminus_correct 53 1024 _ _ mode_NE x y Fx Fy).
rewrite Rlt_bool_true by exact Hlt.
intros (HR & HF & _).
change (Bminus mode_NE x y) with (sub x y) in HR, HF.
split; [exact HF|]. split; [exact HR|]. rewrite HR. exact He.
Qed.

Lemma add_below_max :
  forall x y, is_finite x = true -> is_finite y = true ->
  Rabs (B2R x + B2R y) <= MAX ->
  is_finite (add x y) = true /\ B2R (add x y) = RN (B2R x + B2R y) /\
  Rabs (B2R (add x y) - (B2R x + B2R y)) <= bpow radix2 971.
Proof.
intros x y Fx Fy H.
destruct (RN_below_max _ H) as (Hlt & He).
generalize (@Bplus_correct 53 1024 _ _ mode_NE x y Fx Fy).
rewrite Rlt_bool_true by exact Hlt.
intros (HR & HF & _).
change (Bplus mode_NE x y) with (add x y) in HR, HF.
split; [exact HF|]. split; [exact HR|]. rewrite HR. exact He.
Qed.

(** If [x * y] is finite, it is [RN(x * y)], because an overflow when
    rounding to nearest gives an infinity. *)
Lemma mul_B2R :
  forall x y, is_finite x = true -> is_finite y = true ->
  is_finite (mul x y) = true -> B2R (mul x y) = RN (B2R x * B2R y).
Proof.
intros x y Fx Fy Fp.
generalize (@Bmult_correct 53 1024 _ _ mode_NE x y).
destruct (Rlt_bool _ _).
- intros (HR & _). exact HR.
- intros HO. exfalso.
  revert Fp HO. unfold mul.
  destruct (Bmult mode_NE x y); intros F HO; discriminate.
Qed.

(** ** What [two_prod_is_exact] checks *)

(** Both variants check [-968 <= exponent(p) <= 1023] for [p = x * y].
    Then [p] is finite and nonzero, [|x * y| >= 2^-969], as needed for the
    error to be a float, and [|x * y| < 2^(exponent(p) + 1)]. *)
Lemma mul_exponent_bounds :
  forall x y, is_finite x = true -> is_finite y = true ->
  (-968 <= Generic.exponent (mul x y) <= 1023)%Z ->
  is_finite (mul x y) = true /\ B2R (mul x y) = RN (B2R x * B2R y) /\
  B2R (mul x y) <> 0 /\
  bpow radix2 (-969) <= Rabs (B2R x * B2R y) <
    bpow radix2 (Generic.exponent (mul x y) + 1).
Proof.
intros x y Fx Fy He.
assert (Fp : is_finite (mul x y) = true).
{ rewrite <- is_finite_eq. unfold Generic.is_finite. apply Z.ltb_lt. lia. }
assert (Hp := mul_B2R x y Fx Fy Fp).
set (p := mul x y) in *. clearbody p.
assert (H968 : bpow radix2 (-968) <= Rabs (B2R p)).
{ apply Rle_trans with (bpow radix2 (Generic.exponent p)).
  - apply bpow_le. lia.
  - apply bpow_exponent_le_abs_B2R; [exact Fp | lia]. }
pose proof (abs_B2R_lt_exponent p Fp) as Hlt.
split; [exact Fp|]. split; [exact Hp|]. split.
{ intros H0. rewrite H0, Rabs_R0 in H968.
  pose proof (bpow_gt_0 radix2 (-968)). lra. }
split.
- (* Otherwise [|RN(x * y)| <= 2^-969], as [2^-969] is a float. *)
  apply Rnot_lt_le. intros Hxy.
  assert (Rabs (B2R p) <= bpow radix2 (-969)).
  { rewrite Hp. apply abs_round_le_generic; [typeclasses eauto .. | |lra].
    apply generic_format_FLT_bpow; [typeclasses eauto .. | lia]. }
  pose proof (bpow_lt radix2 (-969) (-968) ltac:(lia)). lra.
- (* Otherwise [|RN(x * y)| >= 2^(exponent(p) + 1)]. *)
  apply Rnot_le_lt. intros Hxy.
  assert (bpow radix2 (Generic.exponent p + 1) <= Rabs (B2R p)).
  { rewrite Hp. apply abs_round_ge_generic; [typeclasses eauto .. | |exact Hxy].
    apply generic_format_FLT_bpow; [typeclasses eauto .. | lia]. }
  lra.
Qed.

(** ** With an FMA *)

(** [x * y - p] is a float ([mult_error_FLT]) of magnitude at most
    [2^971], so the FMA computes it exactly. *)
Lemma two_prod_err_fma :
  forall x y, is_finite x = true -> is_finite y = true ->
  is_finite (mul x y) = true -> B2R (mul x y) = RN (B2R x * B2R y) ->
  bpow radix2 (-969) <= Rabs (B2R x * B2R y) ->
  Rabs (B2R x * B2R y) < bpow radix2 1024 ->
  is_finite (mul_add x y (opp (mul x y))) = true /\
  B2R (mul_add x y (opp (mul x y))) = B2R x * B2R y - B2R (mul x y).
Proof.
intros x y Fx Fy Fp Hp Hlo Hhi.
assert (Fe : generic_format radix2 fexp64 (B2R x * B2R y - B2R (mul x y))).
{ replace (B2R x * B2R y - B2R (mul x y))
    with (- (RN (B2R x * B2R y) - B2R x * B2R y)) by (rewrite Hp; ring).
  apply generic_format_opp.
  apply mult_error_FLT;
    [typeclasses eauto .. | apply generic_format_B2R | apply generic_format_B2R |].
  intros _. exact Hlo. }
assert (He : Rabs (B2R x * B2R y - B2R (mul x y)) <= bpow radix2 971).
{ rewrite <- Rabs_Ropp, Ropp_minus_distr, Hp. apply RN_error. lra. }
assert (Fo : is_finite (opp (mul x y)) = true)
  by (unfold opp; rewrite is_finite_Bopp; exact Fp).
generalize (@Bfma_correct 53 1024 _ _ mode_NE x y (opp (mul x y)) Fx Fy Fo).
cbv zeta.
replace (B2R (opp (mul x y))) with (- B2R (mul x y))
  by (unfold opp; symmetry; apply B2R_Bopp).
change (B2R x * B2R y + - B2R (mul x y)) with (B2R x * B2R y - B2R (mul x y)).
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE)) with RN.
rewrite (round_generic _ _ _ _ Fe).
rewrite Rlt_bool_true.
2: { apply Rle_lt_trans with (1 := He). apply bpow_lt. lia. }
intros (HR & HF & _).
split; [exact HF | exact HR].
Qed.

(** ** Without an FMA *)

(** Veltkamp's [split] of [x] with [|x| < 2^996]: [hi] is Flocq's [hx], [x]
    rounded to 26 bits, and [lo = x - hi] exactly. The bound on [x] keeps
    [C * x] below [MAX]. *)
Lemma split_correct :
  forall x, is_finite x = true -> Rabs (B2R x) < bpow radix2 996 ->
  let '(hi, lo) := Generic.split x in
  is_finite hi = true /\ is_finite lo = true /\
  B2R hi = RN (RN (B2R x - RN (B2R x * (bpow radix2 27 + 1)))
               + RN (B2R x * (bpow radix2 27 + 1))) /\
  B2R lo = RN (B2R x - B2R hi) /\
  B2R x = B2R hi + B2R lo /\
  Rabs (B2R lo) <= bpow radix2 (-26) * Rabs (B2R x) + bpow radix2 (-1075).
Proof.
intros x Fx Hx.
(* The magnitudes: [134217729 * x] and the other operands are below
   [134217730 * 2^996 + 2 * 2^971 <= MAX]. *)
assert (HM : 0 <= bpow radix2 971 <= bpow radix2 996 /\
             134217730 * bpow radix2 996 + 2 * bpow radix2 971 <= MAX)
  by (cbn [bpow radix_val radix2]; lra).
apply Rabs_lt_inv in Hx.
unfold Generic.split. cbv beta iota zeta.
destruct (of_u64_exact 134217729) as (Fc & _ & Hc); [lia|].
set (c := of_u64 134217729) in *. clearbody c.
(* [t = RN(C * x)], [|C * x| < (2^27 + 1) * 2^996]. *)
destruct (mul_below_max c x Fc Fx) as (Ft & Ht & Et).
{ rewrite Hc. apply Rabs_le. lra. }
rewrite Hc in Ht, Et.
replace (IZR 134217729 * B2R x) with (B2R x * (bpow radix2 27 + 1)) in Ht
  by (cbn [bpow radix_val radix2]; lra).
apply Rabs_le_inv in Et.
set (t := mul c x) in *. clearbody t.
(* [a = RN(t - x)], with [t - x] close to [2^27 * x]. *)
destruct (sub_below_max t x Ft Fx) as (Fa & Ha & Ea).
{ apply Rabs_le. lra. }
apply Rabs_le_inv in Ea.
set (a := sub t x) in *. clearbody a.
(* [hi = RN(t - a)], with [t - a] within [2^971] of [x]. *)
destruct (sub_below_max t a Ft Fa) as (Fh & Hh & Eh).
{ apply Rabs_le. lra. }
apply Rabs_le_inv in Eh.
set (hi := sub t a) in *. clearbody hi.
(* [lo = RN(x - hi)], with [x - hi] within [2^972] of 0. *)
destruct (sub_below_max x hi Fx Fh) as (Fl & Hl & _).
{ apply Rabs_le. lra. }
set (lo := sub x hi) in *. clearbody lo.
(* Flocq computes [q = RN(x - t)], which is [-a] as ties to even is
   symmetric, and then [hx = RN(q + t)]. *)
assert (Hhi : B2R hi = RN (RN (B2R x - RN (B2R x * (bpow radix2 27 + 1)))
                           + RN (B2R x * (bpow radix2 27 + 1)))).
{ rewrite <- Ht.
  replace (B2R x - B2R t) with (- (B2R t - B2R x)) by ring.
  rewrite round_NE_opp, <- Ha, Hh.
  f_equal. ring. }
split; [exact Fh|]. split; [exact Fl|]. split; [exact Hhi|]. split; [exact Hl|].
(* Veltkamp: [hx] is [x] rounded to nearest with 26 bits, with some tie
   breaking rule, and [x = hx + tx] exactly. *)
destruct (Pff2Flocq.Veltkamp radix2 (-1074) 53 (fun z => negb (Z.even z)) 27
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (B2R x) (generic_format_B2R _ _ x))
  as (choice & V).
destruct (Pff2Flocq.Veltkamp_tail radix2 (-1074) 53 (fun z => negb (Z.even z)) 27
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (B2R x) (generic_format_B2R _ _ x))
  as (T & _).
rewrite <- Hhi in V, T. rewrite <- Hl in T.
split; [exact T|].
(* [hx = x * (1 + eps) + eta], so [|lo| = |x * eps + eta|]. *)
destruct (error_N_FLT radix2 (-1074) (53 - 27) ltac:(lia) choice (B2R x))
  as (eps & eta & Heps & Heta & _ & He).
rewrite <- V in He.
change (- (53 - 27) + 1)%Z with (-25)%Z in Heps.
replace (B2R lo) with (- (B2R x * eps) + - eta) by lra.
apply Rle_trans with (1 := Rabs_triang _ _).
rewrite 2!Rabs_Ropp, Rabs_mult, (Rmult_comm (Rabs (B2R x))).
apply Rplus_le_compat.
- apply Rmult_le_compat_r; [apply Rabs_pos|].
  cbn [bpow radix_val radix2] in Heps |- *. lra.
- cbn [bpow radix_val radix2] in Heta |- *. lra.
Qed.

(** [|a * b| <= 2^1000] if [|a| <= (1 + 2^-26)|x| + 2^-1075] and
    [|b| <= 2^-26 |y| + 2^-1075], as for the products of the halves of [x]
    and [y] other than [hx * hy], with the bounds of [two_prod_err_dekker]
    on [x] and [y]. *)
Lemma cross_bound :
  forall a b x y,
  Rabs x <= bpow radix2 996 -> Rabs y <= bpow radix2 996 ->
  Rabs x * Rabs y <= bpow radix2 1023 ->
  Rabs a <= Rabs x + bpow radix2 (-26) * Rabs x + bpow radix2 (-1075) ->
  Rabs b <= bpow radix2 (-26) * Rabs y + bpow radix2 (-1075) ->
  Rabs (a * b) <= bpow radix2 1000.
Proof.
intros a b x y Hx Hy Hxy Ha Hb.
rewrite Rabs_mult.
apply Rle_trans with
  ((Rabs x + bpow radix2 (-26) * Rabs x + bpow radix2 (-1075))
   * (bpow radix2 (-26) * Rabs y + bpow radix2 (-1075))).
{ apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Ha | exact Hb]. }
pose proof (Rabs_pos x). pose proof (Rabs_pos y).
cbn [bpow radix_val radix2] in *. nra.
Qed.

(** Dekker's TwoProduct, if [|x|, |y| < 2^996] and
    [2^-969 <= |x * y| < 2^1023]. The products of the halves differ from
    [x * y] by at most [3 * 2^1000], so [hx * hy] stays below [MAX], and
    each addition adds at most [2^1000 + 2^971]. *)
Lemma two_prod_err_dekker :
  forall x y, is_finite x = true -> is_finite y = true ->
  Rabs (B2R x) < bpow radix2 996 -> Rabs (B2R y) < bpow radix2 996 ->
  is_finite (mul x y) = true -> B2R (mul x y) = RN (B2R x * B2R y) ->
  bpow radix2 (-969) <= Rabs (B2R x * B2R y) ->
  Rabs (B2R x * B2R y) < bpow radix2 1023 ->
  is_finite (Generic.two_prod_err false x y (mul x y)) = true /\
  B2R (Generic.two_prod_err false x y (mul x y)) =
    B2R x * B2R y - B2R (mul x y).
Proof.
intros x y Fx Fy Hx Hy Fp Hp Hlo Hhi.
(* The magnitudes: [2^971 <= 2^1000] bounds each rounding error, and
   [2^1023 + 16 * 2^1000 <= MAX]. *)
assert (HM : 0 <= bpow radix2 971 <= bpow radix2 1000 /\
             bpow radix2 1023 + 16 * bpow radix2 1000 <= MAX /\
             16 * bpow radix2 1000 <= MAX /\ bpow radix2 1023 <= bpow radix2 1024)
  by (cbn [bpow radix_val radix2]; lra).
assert (Ep : Rabs (B2R (mul x y) - B2R x * B2R y) <= bpow radix2 971).
{ rewrite Hp. apply RN_error. lra. }
unfold Generic.two_prod_err.
generalize (split_correct x Fx Hx) (split_correct y Fy Hy).
destruct (Generic.split x) as (xh, xl).
destruct (Generic.split y) as (yh, yl).
cbv beta iota.
intros (Fxh & Fxl & Hxh & Hxl & Sx & Bxl) (Fyh & Fyl & Hyh & Hyl & Sy & Byl).
set (p := mul x y) in *. clearbody p.
(* The products of the halves other than [hx * hy]. *)
assert (Bxh : Rabs (B2R xh) <=
  Rabs (B2R x) + bpow radix2 (-26) * Rabs (B2R x) + bpow radix2 (-1075)).
{ replace (B2R xh) with (B2R x - B2R xl) by lra.
  apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. lra. }
assert (Byh : Rabs (B2R yh) <=
  Rabs (B2R y) + bpow radix2 (-26) * Rabs (B2R y) + bpow radix2 (-1075)).
{ replace (B2R yh) with (B2R y - B2R yl) by lra.
  apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. lra. }
assert (Hxy' : Rabs (B2R x) * Rabs (B2R y) < bpow radix2 1023)
  by (rewrite <- Rabs_mult; exact Hhi).
assert (B12 : Rabs (B2R xh * B2R yl) <= bpow radix2 1000)
  by (apply cross_bound with (B2R x) (B2R y); lra).
assert (B21 : Rabs (B2R xl * B2R yh) <= bpow radix2 1000).
{ rewrite (Rmult_comm (B2R xl)).
  apply cross_bound with (B2R y) (B2R x); lra. }
assert (B22 : Rabs (B2R xl * B2R yl) <= bpow radix2 1000).
{ apply cross_bound with (B2R x) (B2R y); try lra.
  pose proof (Rabs_pos (B2R x)). lra. }
assert (Hxy : B2R x * B2R y =
  B2R xh * B2R yh + B2R xh * B2R yl + B2R xl * B2R yh + B2R xl * B2R yl)
  by (rewrite Sx, Sy; ring).
apply Rabs_le_inv in B12, B21, B22, Ep.
apply Rabs_lt_inv in Hhi.
(* [x1y1 = RN(hx * hy)] *)
destruct (mul_below_max xh yh Fxh Fyh) as (F1 & H1 & E1).
{ apply Rabs_le. lra. }
apply Rabs_le_inv in E1.
set (x1y1 := mul xh yh) in *. clearbody x1y1.
(* [t1 = RN(x1y1 - p)] *)
destruct (sub_below_max x1y1 p F1 Fp) as (F2 & H2 & E2).
{ apply Rabs_le. lra. }
apply Rabs_le_inv in E2.
set (t1 := sub x1y1 p) in *. clearbody t1.
(* [x1y2 = RN(hx * ty)] *)
destruct (mul_below_max xh yl Fxh Fyl) as (F3 & H3 & E3).
{ apply Rabs_le. lra. }
apply Rabs_le_inv in E3.
set (x1y2 := mul xh yl) in *. clearbody x1y2.
(* [t2 = RN(t1 + x1y2)] *)
destruct (add_below_max t1 x1y2 F2 F3) as (F4 & H4 & E4).
{ apply Rabs_le. lra. }
apply Rabs_le_inv in E4.
set (t2 := add t1 x1y2) in *. clearbody t2.
(* [x2y1 = RN(tx * hy)] *)
destruct (mul_below_max xl yh Fxl Fyh) as (F5 & H5 & E5).
{ apply Rabs_le. lra. }
apply Rabs_le_inv in E5.
set (x2y1 := mul xl yh) in *. clearbody x2y1.
(* [t3 = RN(t2 + x2y1)] *)
destruct (add_below_max t2 x2y1 F4 F5) as (F6 & H6 & E6).
{ apply Rabs_le. lra. }
apply Rabs_le_inv in E6.
set (t3 := add t2 x2y1) in *. clearbody t3.
(* [x2y2 = RN(tx * ty)] *)
destruct (mul_below_max xl yl Fxl Fyl) as (F7 & H7 & E7).
{ apply Rabs_le. lra. }
apply Rabs_le_inv in E7.
set (x2y2 := mul xl yl) in *. clearbody x2y2.
(* [t4 = RN(t3 + x2y2)] *)
destruct (add_below_max t3 x2y2 F6 F7) as (F8 & H8 & _).
{ apply Rabs_le. lra. }
split; [exact F8|].
(* Dekker: [x * y = r + t4], where Flocq computes [t1] as [RN(-r + x1y1)]. *)
destruct (Pff2Flocq.Dekker radix2 (-1074) 53 (fun z => negb (Z.even z))
  ltac:(lia) ltac:(lia) (B2R x) (B2R y)
  (generic_format_B2R _ _ x) (generic_format_B2R _ _ y) (or_introl eq_refl))
  as (D & _).
change (53 - Z.div2 53)%Z with 27%Z in D.
rewrite <- Hxh, <- Hyh, <- Hxl, <- Hyl, <- Hp, <- H1 in D.
replace (- B2R p + B2R x1y1) with (B2R x1y1 - B2R p) in D by ring.
rewrite <- H2, <- H3, <- H4, <- H5, <- H6, <- H7, <- H8 in D.
specialize (D (or_intror Hlo)).
lra.
Qed.

(** ** TwoProduct *)

(** If [two_prod_is_exact fma x y (x * y)] holds, then [p = x * y] is
    finite and nonzero, and [two_prod_err fma x y p] is finite and is
    [x * y - p] exactly. *)
Theorem two_prod_err_correct :
  forall fma x y,
  is_finite x = true -> is_finite y = true ->
  Generic.two_prod_is_exact fma x y (mul x y) = true ->
  is_finite (mul x y) = true /\ B2R (mul x y) = RN (B2R x * B2R y) /\
  B2R (mul x y) <> 0 /\
  is_finite (Generic.two_prod_err fma x y (mul x y)) = true /\
  B2R (Generic.two_prod_err fma x y (mul x y)) =
    B2R x * B2R y - B2R (mul x y).
Proof.
intros fma x y Fx Fy H.
unfold Generic.two_prod_is_exact in H. cbv zeta in H.
destruct fma.
- apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2.
  destruct (mul_exponent_bounds x y Fx Fy (conj H1 H2))
    as (Fp & Hp & Hp0 & Hlo & Hhi).
  destruct (two_prod_err_fma x y Fx Fy Fp Hp Hlo) as (Fe & He).
  { apply Rlt_le_trans with (1 := Hhi). apply bpow_le. lia. }
  split; [exact Fp|]. split; [exact Hp|]. split; [exact Hp0|].
  split; [exact Fe | exact He].
- apply andb_prop in H as [H Ey]. apply andb_prop in H as [H Ex].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2, Ex, Ey.
  assert (H3 : (Generic.exponent (mul x y) <= 1023)%Z) by lia.
  destruct (mul_exponent_bounds x y Fx Fy (conj H1 H3))
    as (Fp & Hp & Hp0 & Hlo & Hhi).
  assert (Hx : Rabs (B2R x) < bpow radix2 996).
  { apply Rlt_le_trans with (1 := abs_B2R_lt_exponent x Fx).
    apply bpow_le. lia. }
  assert (Hy : Rabs (B2R y) < bpow radix2 996).
  { apply Rlt_le_trans with (1 := abs_B2R_lt_exponent y Fy).
    apply bpow_le. lia. }
  destruct (two_prod_err_dekker x y Fx Fy Hx Hy Fp Hp Hlo) as (Fe & He).
  { apply Rlt_le_trans with (1 := Hhi). apply bpow_le. lia. }
  split; [exact Fp|]. split; [exact Hp|]. split; [exact Hp0|].
  split; [exact Fe | exact He].
Qed.
