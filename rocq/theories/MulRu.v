(** * [mul_ru] rounds toward +inf

    [mul_ru] is IEEE 754 multiplication rounded toward +inf on both lanes,
    i.e. Flocq's [Bmult mode_UP], including the sign of a zero, overflow,
    the infinities and NaN, both with and without an FMA. It never panics.

    The fast path, [mul1_ru_fast], computes [p = RN(x * y)] and its exact
    error [e = x * y - p] with [two_prod_err], and steps [p] up to the next
    float if [e > 0]. If [x] or [y] is zero or not finite, the product does
    not depend on the rounding mode. The lanes that it rejects go to
    [mul1_ru_tiny]. If [|RN(x * y)| < 2^-968], it rounds the product up
    through [x * 2^128 * y] on the fast path, or by the sign of
    [RN(x * y)] if that is zero ([MulRuTiny.v]). Otherwise the
    slow path, [mul1_ru_slow], multiplies the significands as integers and
    rounds the product with [round_up_exact]. *)

From Stdlib Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Calc.Operations.
From Inari Require Import Model Encoding Spec Decompose RoundUpExact
  SumRoundUp StepUp TwoProduct MulRuTiny.

Open Scope R_scope.

(** The operands that [mul1_ru_fast] and [mul1_ru_slow] multiply in the
    default rounding mode are +-inf, NaN or zeros, and then the rounding
    mode does not matter. *)
Lemma mul_special :
  forall x y,
  negb (is_finite x && is_finite y) || eq x zero || eq y zero = true ->
  mul x y = Bmult mode_UP x y.
Proof.
intros x y H.
unfold mul.
(* [Bmult] looks at the rounding mode only for two finite nonzero
   operands, which [H] excludes. *)
destruct x as [sx|sx| |[|] mx ex Hx], y as [sy|sy| |[|] my ey Hy];
  try discriminate H; reflexivity.
Qed.

(** A product of nonzero reals is negative if exactly one factor is. *)
Lemma Rlt_bool_mult :
  forall a b, a <> 0 -> b <> 0 ->
  Rlt_bool (a * b) 0 = xorb (Rlt_bool a 0) (Rlt_bool b 0).
Proof.
intros a b Ha Hb.
destruct (Rdichotomy _ _ Ha) as [Ha'|Ha'];
  [rewrite (Rlt_bool_true _ _ Ha') | rewrite (Rlt_bool_false _ _ (Rlt_le _ _ Ha'))];
  destruct (Rdichotomy _ _ Hb) as [Hb'|Hb'];
  [rewrite (Rlt_bool_true _ _ Hb') | rewrite (Rlt_bool_false _ _ (Rlt_le _ _ Hb'))
  | rewrite (Rlt_bool_true _ _ Hb') | rewrite (Rlt_bool_false _ _ (Rlt_le _ _ Hb'))];
  cbn [xorb];
  [apply Rlt_bool_false | apply Rlt_bool_true | apply Rlt_bool_true
  | apply Rlt_bool_false]; nra.
Qed.

(** For finite nonzero [x] and [y], a float that is [x * y] rounded up as
    [rounds_up_to] describes is [Bmult mode_UP x y]. *)
Lemma Bmult_rounds_up :
  forall x y r : f64,
  is_finite x = true -> is_finite y = true -> B2R x <> 0 -> B2R y <> 0 ->
  rounds_up_to (B2R x * B2R y) r -> r = Bmult mode_UP x y.
Proof.
intros x y r Fx Fy Hx0 Hy0 Hr.
(* [Bmult] gives the product the sign [xorb (Bsign x) (Bsign y)]. *)
assert (Hs : Rlt_bool (B2R x * B2R y) 0 = xorb (Bsign x) (Bsign y)).
{ rewrite (Bsign_B2R x Fx Hx0), (Bsign_B2R y Fy Hy0).
  now apply Rlt_bool_mult. }
unfold rounds_up_to in Hr. rewrite Hs in Hr.
generalize (@Bmult_correct 53 1024 _ _ mode_UP x y).
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_UP)) with RU.
destruct (Rlt_bool (Rabs (RU (B2R x * B2R y))) (bpow radix2 1024)).
- destruct Hr as (HR & HF & HS). intros (HR' & HF' & HS').
  rewrite Fx, Fy in HF'.
  apply B2R_Bsign_inj; [exact HF | exact HF' | congruence |].
  rewrite HS, HS' by (apply finite_not_nan; exact HF'). reflexivity.
- intros HO. apply B2SF_inj. rewrite Hr, HO. reflexivity.
Qed.

(** ** The fast path *)

Theorem mul1_ru_fast_correct :
  forall fma x y,
  snd (Generic.mul1_ru_fast fma x y) = true ->
  fst (Generic.mul1_ru_fast fma x y) = Bmult mode_UP x y.
Proof.
intros fma x y.
unfold Generic.mul1_ru_fast. cbv zeta. cbn [fst snd].
rewrite !is_finite_eq.
destruct (negb (is_finite x && is_finite y) || eq x zero || eq y zero) eqn:Hsp;
  cbn [negb orb andb].
{ intros _. now apply mul_special. }
intros H.
apply Bool.orb_false_elim in Hsp as [Hsp _].
apply Bool.orb_false_elim in Hsp as [Hf _].
apply Bool.negb_false_iff, andb_prop in Hf as [Fx Fy].
destruct (two_prod_err_correct fma x y Fx Fy H) as (Fp & Hp & Hp0 & Fe & He).
(* [x] and [y] are nonzero, as [p = RN(x * y)] is. *)
assert (Hxy : B2R x * B2R y <> 0).
{ intros H0. apply Hp0. rewrite Hp, H0. apply round_0. typeclasses eauto. }
apply Bmult_rounds_up;
  [exact Fx | exact Fy | intros H0; apply Hxy; rewrite H0; ring ..|].
apply step_up_rounds_up; assumption.
Qed.

(** ** The slow path *)

Theorem mul1_ru_slow_correct :
  forall x y, Generic.mul1_ru_slow x y = Some (Bmult mode_UP x y).
Proof.
intros x y.
unfold Generic.mul1_ru_slow.
rewrite !is_finite_eq.
destruct (negb (is_finite x && is_finite y) || eq x zero || eq y zero) eqn:Hsp.
{ f_equal. now apply mul_special. }
apply Bool.orb_false_elim in Hsp as [Hsp Hy0].
apply Bool.orb_false_elim in Hsp as [Hf Hx0].
apply Bool.negb_false_iff, andb_prop in Hf as [Fx Fy].
generalize (decompose_correct x Fx Hx0) (decompose_correct y Fy Hy0).
destruct (Generic.decompose x) as ((sx, mx), ex).
destruct (Generic.decompose y) as ((sy, my), ey).
intros (-> & Hmx & Hex & Hx) (-> & Hmy & Hey & Hy).
(* [mx * my < 2^106] fits [u128], and [ex + ey] fits [i32]. *)
assert (Hm : (0 < mx * my < 2^106)%Z) by nia.
rewrite checked_u_ok by lia. cbv beta iota.
rewrite checked_i_ok by (simpl; lia). cbv beta iota.
assert (HX : 0 < F2R (Float radix2 mx ex)) by (apply F2R_gt_0; simpl; lia).
assert (HY : 0 < F2R (Float radix2 my ey)) by (apply F2R_gt_0; simpl; lia).
destruct (cond_Ropp_pos (Bsign x) _ HX) as (Hsx & Hax).
destruct (cond_Ropp_pos (Bsign y) _ HY) as (Hsy & Hay).
rewrite <- Hx in Hsx, Hax. rewrite <- Hy in Hsy, Hay.
assert (Hx0' : B2R x <> 0) by (intros H0; rewrite H0, Rabs_R0 in Hax; lra).
assert (Hy0' : B2R y <> 0) by (intros H0; rewrite H0, Rabs_R0 in Hay; lra).
(* The product is exact: [|x * y| = (mx * my) * 2^(ex + ey)]. *)
destruct (round_up_exact_correct (negb (Bool.eqb (Bsign x) (Bsign y)))
  (mx * my) (ex + ey) false (B2R x * B2R y)) as (r & -> & Hr).
{ split; [lia|]. split; [simpl; lia|]. split; [discriminate|].
  split.
  - rewrite Rlt_bool_mult, Hsx, Hsy by assumption.
    now destruct (Bsign x), (Bsign y).
  - rewrite Rabs_mult, Hax, Hay, <- F2R_mult. reflexivity. }
f_equal. now apply Bmult_rounds_up.
Qed.

(** ** Tiny products *)

(** For finite [x], [eq x zero] tests [x = 0]. *)
Lemma eq_zero_B2R :
  forall x : f64, is_finite x = true -> eq x zero = true <-> B2R x = 0.
Proof.
intros x Fx.
unfold eq.
rewrite Beqb_correct by first [exact Fx | reflexivity].
change (B2R zero) with 0.
destruct (Req_bool_spec (B2R x) 0) as [H|H]; split; intros; congruence.
Qed.

(** A factor of a product below [2^-968] is below [2^106] if the other
    factor is at least [2^-1074], as [2^106 * 2^-1074 = 2^-968]. *)
Lemma tiny_factor_lt :
  forall a b, bpow radix2 (-1074) <= b -> a * b < bpow radix2 (-968) ->
  a < bpow radix2 106.
Proof.
intros a b Hb H.
assert (HC : bpow radix2 106 * bpow radix2 (-1074) = bpow radix2 (-968))
  by (rewrite <- bpow_plus; reflexivity).
pose proof (bpow_gt_0 radix2 106). pose proof (bpow_gt_0 radix2 (-1074)).
nra.
Qed.

(** Comparing [a * 2^128] with [b] is comparing [a] with [b * 2^-128]. *)
Lemma lt_scale_iff :
  forall a b, a * bpow radix2 128 < b <-> a < b * bpow radix2 (-128).
Proof.
intros a b.
assert (HC : bpow radix2 128 * bpow radix2 (-128) = 1)
  by (rewrite <- bpow_plus; reflexivity).
pose proof (bpow_gt_0 radix2 128) as H1. pose proof (bpow_gt_0 radix2 (-128)) as H2.
split; intros H.
- replace a with (a * bpow radix2 128 * bpow radix2 (-128))
    by (rewrite Rmult_assoc, HC; ring).
  now apply Rmult_lt_compat_r.
- replace b with (b * bpow radix2 (-128) * bpow radix2 128)
    by (rewrite Rmult_assoc, (Rmult_comm (bpow _ (-128))), HC; ring).
  now apply Rmult_lt_compat_r.
Qed.

(** [mul1_ru_fast] accepts the scaled operands of [mul1_ru_tiny], with and
    without an FMA: [|xs| < 2^234] and [|y| < 2^106] are below the [2^996]
    that the variant without an FMA checks, and [|xs * y|] in
    [[2^-947, 2^-840]] keeps [|p| = |RN(xs * y)|] there too, so
    [-947 <= exponent(p) <= -840]. *)
Lemma mul1_ru_fast_scaled_ok :
  forall fma (xs y : f64),
  is_finite xs = true -> is_finite y = true ->
  B2R xs <> 0 -> B2R y <> 0 ->
  Rabs (B2R xs) < bpow radix2 234 -> Rabs (B2R y) < bpow radix2 106 ->
  bpow radix2 (-947) <= Rabs (B2R xs * B2R y) <= bpow radix2 (-840) ->
  snd (Generic.mul1_ru_fast fma xs y) = true.
Proof.
intros fma xs y Fxs Fy Hxs0 Hy0 Hxs Hy (Hlo & Hhi).
unfold Generic.mul1_ru_fast. cbv zeta. cbn [snd].
rewrite !is_finite_eq, Fxs, Fy.
assert (Exs : eq xs zero = false).
{ destruct (eq xs zero) eqn:E; [|reflexivity].
  exfalso. apply Hxs0, (eq_zero_B2R xs Fxs), E. }
assert (Ey : eq y zero = false).
{ destruct (eq y zero) eqn:E; [|reflexivity].
  exfalso. apply Hy0, (eq_zero_B2R y Fy), E. }
rewrite Exs, Ey. cbn [negb andb orb].
assert (H1023 : bpow radix2 (-840) <= bpow radix2 1023) by (apply bpow_le; lia).
assert (Hb : Rabs (B2R xs * B2R y) <= bpow radix2 1023) by lra.
destruct (mul_RN_spec xs y Fxs Fy Hb) as (Fp & Hp & _).
set (p := mul xs y) in *. clearbody p.
(* [2^-947] and [2^-840] are floats, so rounding keeps [|p|] between
   them. *)
assert (Hp1 : bpow radix2 (-947) <= Rabs (B2R p)).
{ rewrite Hp. apply abs_round_ge_generic; [typeclasses eauto .. | | exact Hlo].
  apply generic_format_FLT_bpow; [typeclasses eauto .. | lia]. }
assert (Hp2 : Rabs (B2R p) <= bpow radix2 (-840)).
{ rewrite Hp. apply abs_round_le_generic; [typeclasses eauto .. | | exact Hhi].
  apply generic_format_FLT_bpow; [typeclasses eauto .. | lia]. }
assert (E1 := exponent_ge p (-947) Fp Hp1).
assert (E2 : (Generic.exponent p < -839)%Z).
{ apply exponent_lt; [exact Fp | lia |].
  pose proof (bpow_lt radix2 (-840) (-839) ltac:(lia)). lra. }
assert (E3 : (Generic.exponent xs < 234)%Z).
{ apply exponent_lt; [exact Fxs | lia | exact Hxs]. }
assert (E4 : (Generic.exponent y < 106)%Z).
{ apply exponent_lt; [exact Fy | lia | exact Hy]. }
unfold Generic.two_prod_is_exact. cbv zeta.
destruct fma; repeat (apply andb_true_intro; split); apply Z.leb_le; lia.
Qed.

(** [mul1_ru_tiny] is correct for every [x] and [y], with and without an
    FMA, and its [debug_assert!] does not fail: where [x] and [y] are
    finite and nonzero and [0 < |RN(x * y)| < 2^-968], [mul1_ru_fast]
    accepts [x * 2^128] and [y]. Where they are finite and nonzero and
    [RN(x * y)] is a zero, the result follows from its sign, and the other
    inputs go to [mul1_ru_slow]. *)
Theorem mul1_ru_tiny_correct :
  forall fma x y, Generic.mul1_ru_tiny fma x y = Some (Bmult mode_UP x y).
Proof.
intros fma x y.
unfold Generic.mul1_ru_tiny. cbv zeta.
destruct two_pow_128_spec as (F128 & S128 & R128).
destruct two_pow_m128_spec as (Fm128 & Sm128 & Rm128).
set (T128 := mul (of_u64 (2^64)) (of_u64 (2^64))) in *.
set (Tm128 := div (of_u64 1) T128) in *.
clearbody T128 Tm128.
rewrite !is_finite_eq.
destruct (negb (is_finite x && is_finite y) || eq x zero || eq y zero) eqn:Hsp;
  cbn [orb].
{ apply mul1_ru_slow_correct. }
destruct (-968 <=? Generic.exponent (mul x y))%Z eqn:He.
{ apply mul1_ru_slow_correct. }
apply Z.leb_gt in He.
apply Bool.orb_false_elim in Hsp as [Hsp Hy0].
apply Bool.orb_false_elim in Hsp as [Hf Hx0].
apply Bool.negb_false_iff, andb_prop in Hf as [Fx Fy].
assert (Hx0' : B2R x <> 0) by (intros H; apply (eq_zero_B2R x Fx) in H; congruence).
assert (Hy0' : B2R y <> 0) by (intros H; apply (eq_zero_B2R y Fy) in H; congruence).
clear Hx0 Hy0. rename Hx0' into Hx0, Hy0' into Hy0.
set (z := B2R x * B2R y).
assert (Hz0 : z <> 0) by (apply Rmult_integral_contrapositive_currified; assumption).
assert (Hsz : Rlt_bool z 0 = xorb (Bsign x) (Bsign y)).
{ unfold z. rewrite (Bsign_B2R x Fx Hx0), (Bsign_B2R y Fy Hy0).
  now apply Rlt_bool_mult. }
(* [p = RN(z)] is finite and below [2^(exponent(p) + 1) <= 2^-968], and so
   is [z], as [2^-968] is a float. *)
assert (Fp : is_finite (mul x y) = true).
{ rewrite <- is_finite_eq. unfold Generic.is_finite. apply Z.ltb_lt. lia. }
assert (Hp := mul_B2R x y Fx Fy Fp). fold z in Hp.
assert (Hz968 : Rabs z < bpow radix2 (-968)).
{ apply abs_lt_of_RN_lt; [lia|]. rewrite <- Hp.
  apply Rlt_le_trans with (1 := abs_B2R_lt_exponent _ Fp).
  apply bpow_le. lia. }
assert (H1023 : bpow radix2 (-968) <= bpow radix2 1023) by (apply bpow_le; lia).
assert (Hz1023 : Rabs z <= bpow radix2 1023) by lra.
destruct (mul_RN_spec x y Fx Fy Hz1023) as (_ & _ & Sp).
set (p := mul x y) in *. clearbody p.
destruct (eq p zero) eqn:Hp0.
{ (* The zero rule: [p] is a zero with the sign of [z]. *)
  apply (eq_zero_B2R p Fp) in Hp0.
  f_equal. apply Bmult_rounds_up; [exact Fx | exact Fy | exact Hx0 | exact Hy0 |].
  apply zero_rule_rounds_up; [exact Hz0 | exact Fp | exact Hp | exact Hp0 |].
  rewrite Sp. exact (eq_sym Hsz). }
assert (Hp0' : B2R p <> 0) by (intros H; apply (eq_zero_B2R p Fp) in H; congruence).
clear Hp0.
(* [p] is nonzero, so [|z| >= 2^-1075]. [x] and [y] are nonzero floats, so
   [|x|, |y| >= 2^-1074], and then [|z| < 2^-968] gives [|x|, |y| < 2^106]. *)
assert (Hz1075 : bpow radix2 (-1075) <= Rabs z).
{ apply RN_nonzero_ge. rewrite <- Hp. exact Hp0'. }
assert (Hzxy : Rabs z = Rabs (B2R x) * Rabs (B2R y)) by apply Rabs_mult.
assert (Hx106 : Rabs (B2R x) < bpow radix2 106).
{ apply tiny_factor_lt with (Rabs (B2R y)); [now apply abs_B2R_ge_min | lra]. }
assert (Hy106 : Rabs (B2R y) < bpow radix2 106).
{ apply tiny_factor_lt with (Rabs (B2R x)); [now apply abs_B2R_ge_min | lra]. }
(* The constant facts, with the [bpow]s as atoms. *)
assert (Hpos128 := bpow_gt_0 radix2 128).
assert (Hposm128 := bpow_gt_0 radix2 (-128)).
assert (C1 : bpow radix2 (-1075) * bpow radix2 128 = bpow radix2 (-947))
  by (rewrite <- bpow_plus; reflexivity).
assert (C2 : bpow radix2 (-968) * bpow radix2 128 = bpow radix2 (-840))
  by (rewrite <- bpow_plus; reflexivity).
assert (C3 : bpow radix2 106 * bpow radix2 128 = bpow radix2 234)
  by (rewrite <- bpow_plus; reflexivity).
assert (C4 : bpow radix2 (-840) * bpow radix2 (-128) = bpow radix2 (-968))
  by (rewrite <- bpow_plus; reflexivity).
assert (C5 : bpow radix2 234 <= bpow radix2 1023) by (apply bpow_le; lia).
assert (C6 : bpow radix2 1023 < bpow radix2 1024) by (apply bpow_lt; lia).
assert (C7 : bpow radix2 (-840) <= bpow radix2 1023) by (apply bpow_le; lia).
(* [xs = x * 2^128] is exact: [x * 2^128] is a float below [2^234]. *)
assert (Hxs : Rabs (B2R x * B2R T128) = Rabs (B2R x) * bpow radix2 128).
{ rewrite R128, Rabs_mult, (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0.
  reflexivity. }
assert (Hxs234 : Rabs (B2R x * B2R T128) < bpow radix2 234).
{ rewrite Hxs, <- C3. now apply Rmult_lt_compat_r. }
assert (Hxsf : generic_format radix2 fexp64 (B2R x * B2R T128)).
{ rewrite R128. apply SqrtSlow.format_scale_up; [apply generic_format_B2R | lia]. }
destruct (SqrtSlow.mul_exact x T128 Fx F128 Hxsf ltac:(lra))
  as (Fxs & Rxs & Sxs).
rewrite S128, Bool.xorb_false_r in Sxs.
rewrite <- Rxs in Hxs234.
rewrite R128 in Rxs.
set (xs := mul x T128) in *. clearbody xs.
assert (Hxs0 : B2R xs <> 0).
{ rewrite Rxs. apply Rmult_integral_contrapositive_currified;
    [exact Hx0 | apply Rgt_not_eq, bpow_gt_0]. }
(* The scaled product [zs = z * 2^128] is in [[2^-947, 2^-840]]. *)
assert (Hzs : B2R xs * B2R y = z * bpow radix2 128).
{ rewrite Rxs. unfold z. ring. }
assert (Hazs : Rabs (z * bpow radix2 128) = Rabs z * bpow radix2 128).
{ rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0.
  reflexivity. }
assert (Hlo : bpow radix2 (-947) <= Rabs (z * bpow radix2 128)).
{ rewrite Hazs, <- C1. now apply Rmult_le_compat_r; [lra|]. }
assert (Hhi : Rabs (z * bpow radix2 128) <= bpow radix2 (-840)).
{ rewrite Hazs, <- C2. apply Rmult_le_compat_r; lra. }
(* So [mul1_ru_fast] accepts [xs] and [y], and gives [rs = RU(zs)]. *)
assert (Hok : snd (Generic.mul1_ru_fast fma xs y) = true).
{ apply mul1_ru_fast_scaled_ok; try assumption. rewrite Hzs. lra. }
assert (Hrs := mul1_ru_fast_correct fma xs y Hok).
revert Hok Hrs.
destruct (Generic.mul1_ru_fast fma xs y) as (rs, ok).
cbn [fst snd]. intros -> Hrs. cbn [negb].
assert (Hb : Rabs (B2R xs * B2R y) <= bpow radix2 1023) by (rewrite Hzs; lra).
destruct (Bmult_UP_spec xs y Fxs Fy Hb) as (Frs & Rrs & Srs).
rewrite <- Hrs in Frs, Rrs, Srs. clear Hrs.
rewrite Hzs in Rrs. rewrite Sxs, <- Hsz in Srs.
(* [2^-947] and [2^-840] are floats, so rounding keeps [|rs|] between
   them, and [rs] has the sign of [z]. *)
assert (Hrs1 : bpow radix2 (-947) <= Rabs (B2R rs)).
{ rewrite Rrs. apply abs_round_ge_generic; [typeclasses eauto .. | | exact Hlo].
  apply generic_format_FLT_bpow; [typeclasses eauto .. | lia]. }
assert (Hrs2 : Rabs (B2R rs) <= bpow radix2 (-840)).
{ rewrite Rrs. apply abs_round_le_generic; [typeclasses eauto .. | | exact Hhi].
  apply generic_format_FLT_bpow; [typeclasses eauto .. | lia]. }
assert (Hrs0 : B2R rs <> 0).
{ intros H. rewrite H, Rabs_R0 in Hrs1. pose proof (bpow_gt_0 radix2 (-947)). lra. }
(* [q = RN(rs * 2^-128)], with [|rs * 2^-128| <= 2^-968]. *)
set (w := B2R rs * bpow radix2 (-128)).
assert (Haw : Rabs w = Rabs (B2R rs) * bpow radix2 (-128)).
{ unfold w. rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0.
  reflexivity. }
assert (Hw968 : Rabs w <= bpow radix2 (-968)).
{ rewrite Haw, <- C4. apply Rmult_le_compat_r; lra. }
assert (Hw0 : w <> 0).
{ unfold w. apply Rmult_integral_contrapositive_currified;
    [exact Hrs0 | apply Rgt_not_eq, bpow_gt_0]. }
assert (Hsw : Rlt_bool w 0 = Bsign rs).
{ unfold w. rewrite Rlt_bool_mult by (try exact Hrs0; apply Rgt_not_eq, bpow_gt_0).
  rewrite (Rlt_bool_false (bpow _ _) 0) by apply bpow_ge_0.
  rewrite Bool.xorb_false_r. symmetry. now apply Bsign_B2R. }
assert (Hq : Rabs (B2R rs * B2R Tm128) <= bpow radix2 1023).
{ rewrite Rm128. fold w. lra. }
destruct (mul_RN_spec rs Tm128 Frs Fm128 Hq) as (Fq & Rq & Sq).
rewrite Rm128 in Rq. fold w in Rq. rewrite Sm128, Bool.xorb_false_r in Sq.
set (q := mul rs Tm128) in *. clearbody q.
(* [qs = q * 2^128] is exact: [|q| <= 2^-968], as [2^-968] is a float. *)
assert (Hq968 : Rabs (B2R q) <= bpow radix2 (-968)).
{ rewrite Rq. apply abs_round_le_generic; [typeclasses eauto .. | | exact Hw968].
  apply generic_format_FLT_bpow; [typeclasses eauto .. | lia]. }
assert (Hqs : Rabs (B2R q * B2R T128) <= bpow radix2 (-840)).
{ rewrite R128, Rabs_mult, (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0.
  rewrite <- C2. apply Rmult_le_compat_r; lra. }
assert (Hqsf : generic_format radix2 fexp64 (B2R q * B2R T128)).
{ rewrite R128. apply SqrtSlow.format_scale_up; [apply generic_format_B2R | lia]. }
destruct (SqrtSlow.mul_exact q T128 Fq F128 Hqsf ltac:(lra)) as (Fqs & Rqs & _).
rewrite R128 in Rqs.
set (qs := mul q T128) in *. clearbody qs.
(* [qs < rs] iff [q < rs * 2^-128 = w]. *)
assert (Hup : lt qs rs = true <-> B2R q < w).
{ unfold lt. rewrite Bltb_correct by assumption. rewrite Rqs. unfold w.
  rewrite <- lt_scale_iff.
  destruct (Rlt_bool_spec (B2R q * bpow radix2 128) (B2R rs)); split;
    intros; first [reflexivity | assumption | discriminate | lra]. }
(* [q], stepped up if [q < w], is [w] rounded up, and that is [z] rounded
   up, as [RU(RU(z * 2^128) * 2^-128) = RU(z)] and [w] has the sign of
   [z]. *)
assert (Hr : rounds_up_to w (if lt qs rs then Generic.step_up q else q)).
{ apply step_up_rounds_up_iff0; [exact Hw0 | exact Fq | exact Rq | | exact Hup].
  intros _. rewrite Sq, Hsw. reflexivity. }
f_equal. apply Bmult_rounds_up; [exact Fx | exact Fy | exact Hx0 | exact Hy0 |].
apply (rounds_up_to_ext w); [| | exact Hr].
- unfold w. rewrite Rrs. apply RU_scaled.
- rewrite Hsw, Srs. reflexivity.
Qed.

(** ** Both lanes *)

Theorem mul_ru_impl_correct :
  forall fma x y,
  Generic.mul_ru_impl fma x y =
    Some (Bmult mode_UP (fst x) (fst y), Bmult mode_UP (snd x) (snd y)).
Proof.
intros fma [x0 x1] [y0 y1].
(* Each lane is the fast path if it is valid, and [mul1_ru_tiny] if not. *)
assert (L : forall a b,
  (if snd (Generic.mul1_ru_fast fma a b)
   then Some (fst (Generic.mul1_ru_fast fma a b))
   else Generic.mul1_ru_tiny fma a b) = Some (Bmult mode_UP a b)).
{ intros a b.
  destruct (snd (Generic.mul1_ru_fast fma a b)) eqn:Hok.
  - f_equal. now apply mul1_ru_fast_correct.
  - apply mul1_ru_tiny_correct. }
generalize (L x0 y0) (L x1 y1).
unfold Generic.mul_ru_impl, Generic.lanewise2. cbn [fst snd].
destruct (Generic.mul1_ru_fast fma x0 y0) as (r0, ok0).
destruct (Generic.mul1_ru_fast fma x1 y1) as (r1, ok1).
cbn [fst snd].
intros H0 H1.
destruct ok0, ok1; cbn [andb];
  rewrite ?H0, ?H1; try injection H0 as ->; try injection H1 as ->; reflexivity.
Qed.

(** [mul_ru] is correct whether the target has an FMA or not. *)
Theorem mul_ru_correct :
  forall has_fma x y,
  Generic.mul_ru has_fma x y =
    Some (Bmult mode_UP (fst x) (fst y), Bmult mode_UP (snd x) (snd y)).
Proof.
intros has_fma x y. apply mul_ru_impl_correct.
Qed.
