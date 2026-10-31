(** * What [atan2_rd] and [atan2_ru] return

    [Interval::atan2] calls [atan2_rd(y, x)] and [atan2_ru(y, x)] at
    corners of the box, which may be at an infinity. [at_val y x] is the
    real that they round: [Ratan2] of the reals of [y] and [x] if both are
    finite, and otherwise its limit, which is the special value of MPFR.
    [at_args] holds for every corner that the code passes ([atan2_round]
    needs it): no NaN, not two infinities, and a zero [y] only with [x]
    above 0 or +inf, where the sign of the zero does not change the value.
    [at_hi_lane] and [at_lo_lane] give the lanes of the result from the
    least upper or greatest lower bound of the image, as [pl_hi] and
    [pl_lo] in [PowMpfr.v] do for [pow]. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Integer Sign MaxMin AddSub
  DivTight MpfrRound MonoInc PowMpfr.

Open Scope R_scope.

(** The real that [atan2] rounds at [(y, x)]. *)
Definition at_val (y x : f64) : R :=
  match y with
  | B754_infinity sy => if sy then - (PI / 2) else PI / 2
  | _ =>
      match x with
      | B754_infinity false => 0
      | B754_infinity true => if Rlt_bool 0 (B2R y) then PI else - PI
      | _ => Ratan2 (B2R y) (B2R x)
      end
  end.

(** The corners that [Interval::atan2] passes to [atan2]. *)
Definition at_args (y x : f64) : Prop :=
  is_nan y = false /\ is_nan x = false /\
  (is_finite y = true \/ is_finite x = true) /\
  (is_finite y = true -> B2R y = 0 ->
   x = B754_infinity false \/ (is_finite x = true /\ 0 < B2R x)).

(** ** [at_val] at finite and infinite corners *)

Lemma at_val_fin :
  forall y x : f64, is_finite y = true -> is_finite x = true ->
  at_val y x = Ratan2 (B2R y) (B2R x).
Proof.
intros [sy|sy| |sy my ey Hy] [sx|sx| |sx mx ex Hx] Fy Fx;
  try discriminate Fy; try discriminate Fx; reflexivity.
Qed.

Lemma at_val_x_pinf :
  forall y : f64, is_finite y = true -> at_val y (B754_infinity false) = 0.
Proof.
intros [sy|sy| |sy my ey Hy] Fy; try discriminate Fy; reflexivity.
Qed.

Lemma at_val_x_ninf_pos :
  forall y : f64, is_finite y = true -> 0 < B2R y -> at_val y (B754_infinity true) = PI.
Proof.
intros y Fy Hy.
assert (E : at_val y (B754_infinity true) = if Rlt_bool 0 (B2R y) then PI else - PI)
  by (destruct y; try discriminate Fy; reflexivity).
rewrite E, Rlt_bool_true by exact Hy. reflexivity.
Qed.

Lemma at_val_x_ninf_neg :
  forall y : f64, is_finite y = true -> B2R y < 0 -> at_val y (B754_infinity true) = - PI.
Proof.
intros y Fy Hy.
assert (E : at_val y (B754_infinity true) = if Rlt_bool 0 (B2R y) then PI else - PI)
  by (destruct y; try discriminate Fy; reflexivity).
rewrite E, Rlt_bool_false by lra. reflexivity.
Qed.

Lemma at_val_y_pinf : forall x : f64, at_val (B754_infinity false) x = PI / 2.
Proof.
intros x. reflexivity.
Qed.

Lemma at_val_y_ninf : forall x : f64, at_val (B754_infinity true) x = - (PI / 2).
Proof.
intros x. reflexivity.
Qed.

(** ** The rounding *)

(** [with_val] of a finite float whose real is 0 is a zero. *)
Lemma am_with_val_zero :
  forall y : f64, is_finite y = true -> B2R y = 0 -> exists s, with_val y = MZero s.
Proof.
intros [s|s| |s my ey Hy] Fy E; try discriminate Fy.
- exists s. reflexivity.
- (* A finite float that is not a zero has a nonzero significand. *)
  exfalso. cbn [B2R] in E. apply eq_0_F2R in E. destruct s; discriminate E.
Qed.

(** [atan2] at a corner that the code passes rounds [at_val] once, in the
    direction asked, to an [f64]: for finite [y] and [x] by
    [mpfr_correct2] and [mpfr_fn_round], and otherwise by the special
    values of [atan2_ok]. *)
Lemma atan2_round :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m ->
  forall rnd (y x : f64), at_args y x ->
  mpfr_round f64_format rnd (at_val y x) (with_val (mpfr_fn2 m (mpfr_atan2 m) rnd y x)).
Proof.
intros emin emax m Hr Hget (Hc & H1 & H2 & H3 & H4 & H5 & H6 & H7) rnd y x
  (Ny & Nx & Hfin & Hz).
unfold mpfr_fn2.
destruct (is_finite y) eqn:Fy.
- destruct (is_finite x) eqn:Fx.
  + (* Both finite: [Ratan2] of the reals, on the domain of [mpfr_correct2]
       as a zero [y] comes only with [x] above 0. *)
    rewrite (at_val_fin y x Fy Fx).
    apply (mpfr_fn_round emin emax); [exact Hr | exact Hget |].
    apply (Hc rnd y x Fy Fx).
    destruct (Req_dec (B2R y) 0) as [E|E]; [right | left; exact E].
    destruct (Hz eq_refl E) as [Ex|(_ & Hx)]; [rewrite Ex in Fx; discriminate Fx | exact Hx].
  + destruct x as [sx|[|]| |sx mx ex Hx]; try discriminate Fx; try discriminate Nx.
    * (* [x = -inf]: [y] is not a zero, and the value is [PI] or [-PI] by its
         sign. *)
      assert (Hy0 : B2R y <> 0).
      { intros E. destruct (Hz eq_refl E) as [Ex|(Fx' & _)]; discriminate. }
      rewrite (with_val_finite y Fy Hy0). cbn [with_val].
      destruct (Rlt_dec 0 (B2R y)) as [Hp|Hn].
      -- rewrite (at_val_x_ninf_pos y Fy Hp).
         apply (mpfr_fn_round emin emax); [exact Hr | exact Hget | exact (H4 rnd _ Hp)].
      -- rewrite (at_val_x_ninf_neg y Fy) by lra.
         apply (mpfr_fn_round emin emax); [exact Hr | exact Hget |].
         apply H5. lra.
    * (* [x = +inf]: MPFR returns a zero, which [mpfr_get_d] keeps. *)
      rewrite (at_val_x_pinf y Fy). cbn [with_val].
      assert (E : exists s, mpfr_atan2 m rnd (with_val y) (MInf false) = MZero s).
      { destruct (Req_dec (B2R y) 0) as [E|E].
        - destruct (am_with_val_zero y Fy E) as (s & ->). exists s. apply H3.
        - rewrite (with_val_finite y Fy E).
          destruct (Rlt_dec 0 (B2R y)) as [Hp|Hn].
          + exists false. apply H1. exact Hp.
          + exists true. apply H2. lra. }
      destruct E as (s & ->). exact (pm_get_zero _ _ _ Hget _ _).
- (* [y] is an infinity, so [x] is finite. *)
  destruct Hfin as [Hfy|Fx]; [discriminate Hfy|].
  destruct y as [sy|[|]| |sy my ey Hy]; try discriminate Fy; try discriminate Ny.
  + rewrite at_val_y_ninf. cbn [with_val].
    apply (mpfr_fn_round emin emax); [exact Hr | exact Hget | exact (H7 rnd x Fx)].
  + rewrite at_val_y_pinf. cbn [with_val].
    apply (mpfr_fn_round emin emax); [exact Hr | exact Hget | exact (H6 rnd x Fx)].
Qed.

(** ** The lanes *)

(** The upper lane [atan2_ru m y x] of a set [S] whose least upper bound
    is [at_val y x]. *)
Lemma at_hi_lane :
  forall emin emax m (S : R -> Prop) (y x : f64),
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m -> at_args y x ->
  (forall s, S s -> s <= at_val y x) ->
  (forall eps, 0 < eps -> exists s, S s /\ at_val y x - eps < s) ->
  lane_ok S (atan2_ru m y x).
Proof.
intros emin emax m S y x Hr Hget Hok Ha Hub Happ.
unfold atan2_ru. apply (pl_hi S (at_val y x)); [exact Hub | exact Happ |].
exact (atan2_round emin emax m Hr Hget Hok RNDU y x Ha).
Qed.

(** The lower lane [-(atan2_rd m y x)] of a set [S] whose greatest lower
    bound is [at_val y x]. *)
Lemma at_lo_lane :
  forall emin emax m (S : R -> Prop) (y x : f64),
  range_ok emin emax -> get_d_ok emin emax m -> atan2_ok emin emax m -> at_args y x ->
  (forall s, S s -> at_val y x <= s) ->
  (forall eps, 0 < eps -> exists s, S s /\ s < at_val y x + eps) ->
  lane_ok (fun s => S (- s)) (opp (atan2_rd m y x)).
Proof.
intros emin emax m S y x Hr Hget Hok Ha Hlb Happ.
unfold atan2_rd. apply (pl_lo S (at_val y x)); [exact Hlb | exact Happ |].
exact (atan2_round emin emax m Hr Hget Hok RNDD y x Ha).
Qed.
