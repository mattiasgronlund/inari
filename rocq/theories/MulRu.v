(** * [mul_ru] rounds toward +inf

    [mul_ru] is IEEE 754 multiplication rounded toward +inf on both lanes,
    i.e. Flocq's [Bmult mode_UP], including the sign of a zero, overflow,
    the infinities and NaN, both with and without an FMA. It never panics.

    The fast path, [mul1_ru_fast], computes [p = RN(x * y)] and its exact
    error [e = x * y - p] with [two_prod_err], and steps [p] up to the next
    float if [e > 0]. If [x] or [y] is zero or not finite, the product does
    not depend on the rounding mode. The slow path, [mul1_ru_slow],
    multiplies the significands as integers and rounds the product with
    [round_up_exact]. *)

From Stdlib Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Calc.Operations.
From Inari Require Import Model Encoding Spec Decompose RoundUpExact
  SumRoundUp StepUp TwoProduct.

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

(** ** Both lanes *)

Theorem mul_ru_impl_correct :
  forall fma x y,
  Generic.mul_ru_impl fma x y =
    Some (Bmult mode_UP (fst x) (fst y), Bmult mode_UP (snd x) (snd y)).
Proof.
intros fma [x0 x1] [y0 y1].
(* Each lane is the fast path if it is valid, and the slow path if not. *)
assert (L : forall a b,
  (if snd (Generic.mul1_ru_fast fma a b)
   then Some (fst (Generic.mul1_ru_fast fma a b))
   else Generic.mul1_ru_slow a b) = Some (Bmult mode_UP a b)).
{ intros a b.
  destruct (snd (Generic.mul1_ru_fast fma a b)) eqn:Hok.
  - f_equal. now apply mul1_ru_fast_correct.
  - apply mul1_ru_slow_correct. }
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
