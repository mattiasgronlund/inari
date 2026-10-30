(** * [sin], [cos] and [tan] piece by piece

    [Interval::cos] splits R at the multiples [k * PI], where [cos] is 1 or
    -1, and [Interval::sin] and [Interval::tan] at the multiples
    [k * (PI / 2)], where [sin] is 0, 1 or -1 and [tan] is 0 or has a pole.
    Between two of them each function is monotone. This file states that,
    the values at the split points, and what an interval of length at
    least [2 * PI] (or [PI] for [tan]) contains. Only real analysis, from
    Stdlib's periodicity and monotonicity lemmas. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary.

Open Scope R_scope.

(** ** Integer shifts

    Stdlib's [sin_period] and [cos_period] shift by [2 * INR k * PI] for a
    [nat] [k]. These are the same for an integer [j], and the shifts by
    [j * PI], which multiply [sin] and [cos] by [(-1) ^ j] ([neg_sin],
    [neg_cos]) and leave [tan] alone. *)

Lemma tp_sin_period : forall x j, sin (x + 2 * IZR j * PI) = sin x.
Proof.
  intros x [|p|p].
  - f_equal; simpl; ring.
  - rewrite <- (positive_nat_Z p), <- INR_IZR_INZ; apply sin_period.
  - change (IZR (Zneg p)) with (- IZR (Zpos p)).
    rewrite <- (positive_nat_Z p), <- INR_IZR_INZ.
    rewrite <- (sin_period (x + 2 * - INR (Pos.to_nat p) * PI) (Pos.to_nat p)).
    f_equal; ring.
Qed.

Lemma tp_cos_period : forall x j, cos (x + 2 * IZR j * PI) = cos x.
Proof.
  intros x [|p|p].
  - f_equal; simpl; ring.
  - rewrite <- (positive_nat_Z p), <- INR_IZR_INZ; apply cos_period.
  - change (IZR (Zneg p)) with (- IZR (Zpos p)).
    rewrite <- (positive_nat_Z p), <- INR_IZR_INZ.
    rewrite <- (cos_period (x + 2 * - INR (Pos.to_nat p) * PI) (Pos.to_nat p)).
    f_equal; ring.
Qed.

(** The forms in which the lemmas below use the periods: [x] moved back by
    [j] periods. *)
Lemma tp_sin_sub : forall x j, sin x = sin (x - 2 * IZR j * PI).
Proof.
  intros x j; rewrite <- (tp_sin_period (x - 2 * IZR j * PI) j); f_equal; ring.
Qed.

Lemma tp_cos_sub : forall x j, cos x = cos (x - 2 * IZR j * PI).
Proof.
  intros x j; rewrite <- (tp_cos_period (x - 2 * IZR j * PI) j); f_equal; ring.
Qed.

Lemma tp_even : forall k, Z.even k = true -> exists j, IZR k = 2 * IZR j.
Proof.
  intros k Hk; apply Z.even_spec in Hk; destruct Hk as [j ->].
  exists j; rewrite mult_IZR; reflexivity.
Qed.

Lemma tp_odd : forall k, Z.odd k = true -> exists j, IZR k = 2 * IZR j + 1.
Proof.
  intros k Hk; apply Z.odd_spec in Hk; destruct Hk as [j ->].
  exists j; rewrite plus_IZR, mult_IZR; reflexivity.
Qed.

Lemma tp_not_even : forall k, Z.even k = false -> exists j, IZR k = 2 * IZR j + 1.
Proof.
  intros k Hk; apply tp_odd; rewrite <- Z.negb_even, Hk; reflexivity.
Qed.

(** [k = 4 * (k / 4) + k mod 4]. *)
Lemma tp_mod4 : forall k m, (k mod 4 = m)%Z -> exists j, IZR k = 4 * IZR j + IZR m.
Proof.
  intros k m Hm; exists (k / 4)%Z.
  rewrite (Z.div_mod k 4) at 1 by lia.
  rewrite plus_IZR, mult_IZR, Hm; reflexivity.
Qed.

Lemma tp_sin_kPI :
  forall x k, sin (x + IZR k * PI) = (if Z.even k then 1 else -1) * sin x.
Proof.
  intros x k; destruct (Z.even k) eqn:Ek.
  - destruct (tp_even k Ek) as [j ->].
    rewrite Rmult_assoc, <- (Rmult_assoc 2), tp_sin_period; ring.
  - destruct (tp_not_even k Ek) as [j ->].
    replace (x + (2 * IZR j + 1) * PI) with ((x + PI) + 2 * IZR j * PI) by ring.
    rewrite tp_sin_period, neg_sin; ring.
Qed.

Lemma tp_cos_kPI :
  forall x k, cos (x + IZR k * PI) = (if Z.even k then 1 else -1) * cos x.
Proof.
  intros x k; destruct (Z.even k) eqn:Ek.
  - destruct (tp_even k Ek) as [j ->].
    rewrite Rmult_assoc, <- (Rmult_assoc 2), tp_cos_period; ring.
  - destruct (tp_not_even k Ek) as [j ->].
    replace (x + (2 * IZR j + 1) * PI) with ((x + PI) + 2 * IZR j * PI) by ring.
    rewrite tp_cos_period, neg_cos; ring.
Qed.

(** [tan] has the period [PI], even at its poles, where [sin x / cos x]
    is [sin x * / 0] and [/ - 0 = - / 0] ([Rinv_opp]). *)
Lemma tp_tan_period : forall x k, tan (x + IZR k * PI) = tan x.
Proof.
  intros x k; unfold tan; rewrite tp_sin_kPI, tp_cos_kPI.
  destruct (Z.even k).
  - rewrite !Rmult_1_l; reflexivity.
  - unfold Rdiv; replace (-1 * cos x) with (- cos x) by ring.
    rewrite Rinv_opp; ring.
Qed.

(** Stdlib's monotonicity lemmas are strict; these are their non-strict
    forms. *)

Lemma tp_cos_dec : forall x y, 0 <= x -> y <= PI -> x <= y -> cos y <= cos x.
Proof.
  intros x y Hx Hy [Hxy | <-]; [| right; reflexivity].
  left; apply cos_decreasing_1; lra.
Qed.

Lemma tp_cos_inc : forall x y, PI <= x -> y <= 2 * PI -> x <= y -> cos x <= cos y.
Proof.
  intros x y Hx Hy [Hxy | <-]; [| right; reflexivity].
  left; apply cos_increasing_1; lra.
Qed.

Lemma tp_sin_inc : forall x y, - (PI / 2) <= x -> y <= PI / 2 -> x <= y -> sin x <= sin y.
Proof.
  intros x y Hx Hy [Hxy | <-]; [| right; reflexivity].
  left; apply sin_increasing_1; lra.
Qed.

Lemma tp_sin_dec :
  forall x y, PI / 2 <= x -> y <= 3 * (PI / 2) -> x <= y -> sin y <= sin x.
Proof.
  intros x y Hx Hy [Hxy | <-]; [| right; reflexivity].
  left; apply sin_decreasing_1; lra.
Qed.

Lemma tp_tan_inc : forall x y, - PI / 2 < x -> y < PI / 2 -> x <= y -> tan x <= tan y.
Proof.
  intros x y Hx Hy [Hxy | <-]; [| right; reflexivity].
  left; apply tan_increasing; lra.
Qed.

(** [up] rounds up: [a / c < up (a / c) <= a / c + 1], so [a] is below
    [up (a / c) * c] by at most [c]. *)
Lemma tp_up : forall a c, 0 < c -> exists k, a < IZR k * c <= a + c.
Proof.
  intros a c Hc; exists (up (a / c)).
  destruct (archimed (a / c)) as [H1 H2].
  set (q := a / c) in *.
  assert (Ha : a = q * c) by (unfold q; field; lra).
  rewrite Ha; split; nra.
Qed.

(** ** [cos] *)

Lemma cos_piece_dec :
  forall k r t, Z.even k = true ->
  IZR k * PI <= r -> r <= t -> t <= (IZR k + 1) * PI -> cos t <= cos r.
Proof.
  intros k r t Hk H1 H2 H3; destruct (tp_even k Hk) as [j Hj]; rewrite Hj in H1, H3.
  rewrite (tp_cos_sub r j), (tp_cos_sub t j).
  apply tp_cos_dec; lra.
Qed.

Lemma cos_piece_inc :
  forall k r t, Z.even k = false ->
  IZR k * PI <= r -> r <= t -> t <= (IZR k + 1) * PI -> cos r <= cos t.
Proof.
  intros k r t Hk H1 H2 H3; destruct (tp_not_even k Hk) as [j Hj]; rewrite Hj in H1, H3.
  rewrite (tp_cos_sub r j), (tp_cos_sub t j).
  apply tp_cos_inc; lra.
Qed.

Lemma cos_kPI : forall k, cos (IZR k * PI) = if Z.even k then 1 else -1.
Proof.
  intros k; rewrite <- (Rplus_0_l (IZR k * PI)), tp_cos_kPI, cos_0; ring.
Qed.

(** Two consecutive multiples of [PI] lie in [(a, a + 2 * PI]], and [cos]
    is 1 at one and -1 at the other. *)
Lemma cos_wide :
  forall a b, a + 2 * PI <= b ->
  exists r t, a <= r <= b /\ a <= t <= b /\ cos r = 1 /\ cos t = -1.
Proof.
  intros a b Hab; destruct (tp_up a PI PI_RGT_0) as [k Hk].
  assert (Hn : cos (IZR k * PI + PI) = - cos (IZR k * PI)) by apply neg_cos.
  pose proof (cos_kPI k) as Hc.
  destruct (Z.even k).
  - exists (IZR k * PI), (IZR k * PI + PI); lra.
  - exists (IZR k * PI + PI), (IZR k * PI); lra.
Qed.

(** ** [sin]

    The quarter [[k * (PI / 2), (k + 1) * (PI / 2)]] with [k = 4 * j + m]
    is moved back by [j] periods into [[m * (PI / 2), (m + 1) * (PI / 2)]]
    (by [j + 1] periods for [m = 3], into [[- (PI / 2), 0]]), inside
    [[- (PI / 2), PI / 2]] where [sin] increases or [[PI / 2, 3 * (PI / 2)]]
    where it decreases. *)

Lemma sin_piece_inc :
  forall k r t, (k mod 4 = 0 \/ k mod 4 = 3)%Z ->
  IZR k * (PI / 2) <= r -> r <= t -> t <= (IZR k + 1) * (PI / 2) -> sin r <= sin t.
Proof.
  intros k r t [Hk | Hk] H1 H2 H3; destruct (tp_mod4 k _ Hk) as [j Hj];
    rewrite Hj in H1, H3.
  - rewrite (tp_sin_sub r j), (tp_sin_sub t j).
    apply tp_sin_inc; lra.
  - rewrite (tp_sin_sub r (j + 1)), (tp_sin_sub t (j + 1)), plus_IZR.
    apply tp_sin_inc; lra.
Qed.

Lemma sin_piece_dec :
  forall k r t, (k mod 4 = 1 \/ k mod 4 = 2)%Z ->
  IZR k * (PI / 2) <= r -> r <= t -> t <= (IZR k + 1) * (PI / 2) -> sin t <= sin r.
Proof.
  intros k r t [Hk | Hk] H1 H2 H3; destruct (tp_mod4 k _ Hk) as [j Hj];
    rewrite Hj in H1, H3; rewrite (tp_sin_sub r j), (tp_sin_sub t j);
    apply tp_sin_dec; lra.
Qed.

Lemma sin_kPI2_1 : forall k, (k mod 4 = 1)%Z -> sin (IZR k * (PI / 2)) = 1.
Proof.
  intros k Hk; destruct (tp_mod4 k _ Hk) as [j ->].
  replace ((4 * IZR j + IZR 1) * (PI / 2)) with (PI / 2 + 2 * IZR j * PI) by (simpl; field).
  rewrite tp_sin_period; exact sin_PI2.
Qed.

Lemma sin_kPI2_3 : forall k, (k mod 4 = 3)%Z -> sin (IZR k * (PI / 2)) = -1.
Proof.
  intros k Hk; destruct (tp_mod4 k _ Hk) as [j ->].
  replace ((4 * IZR j + IZR 3) * (PI / 2)) with ((PI / 2 + PI) + 2 * IZR j * PI)
    by (simpl; field).
  rewrite tp_sin_period, neg_sin, sin_PI2; reflexivity.
Qed.

(** From [cos_wide], as [sin (PI / 2 + x) = cos x] ([cos_sin]). *)
Lemma sin_wide :
  forall a b, a + 2 * PI <= b ->
  exists r t, a <= r <= b /\ a <= t <= b /\ sin r = 1 /\ sin t = -1.
Proof.
  intros a b Hab.
  destruct (cos_wide (a - PI / 2) (b - PI / 2)) as (r & t & Hr & Ht & Hcr & Hct); [lra |].
  exists (PI / 2 + r), (PI / 2 + t); rewrite <- !cos_sin; lra.
Qed.

(** ** [tan]

    For an odd [k], [k * (PI / 2)] is a pole, and [tan] is defined,
    continuous and increasing between it and the next pole
    [(k + 2) * (PI / 2)]. *)

(** The poles are the [j * PI + PI / 2]; between two consecutive ones
    there is none. *)
Lemma tp_dom_between :
  forall j r, IZR j * PI - PI / 2 < r < IZR j * PI + PI / 2 -> tan_dom r.
Proof.
  intros j r [H1 H2] m Hm; subst r.
  pose proof PI_RGT_0 as Hpi.
  assert (Hjm : IZR j - 1 < IZR m) by (apply Rmult_lt_reg_r with PI; lra).
  assert (Hmj : IZR m < IZR j) by (apply Rmult_lt_reg_r with PI; lra).
  rewrite <- minus_IZR in Hjm; apply lt_IZR in Hjm; apply lt_IZR in Hmj; lia.
Qed.

Lemma tp_pole_j : forall k, Z.odd k = true -> exists j, IZR k * (PI / 2) = IZR j * PI + PI / 2.
Proof.
  intros k Hk; destruct (tp_odd k Hk) as [j ->]; exists j; field.
Qed.

Lemma tan_pole : forall k, Z.odd k = true -> ~ tan_dom (IZR k * (PI / 2)).
Proof.
  intros k Hk H; destruct (tp_pole_j k Hk) as [j Hj]; apply (H j); rewrite Hj; field.
Qed.

Lemma tan_piece_dom :
  forall k r, Z.odd k = true ->
  IZR k * (PI / 2) < r < (IZR k + 2) * (PI / 2) -> tan_dom r.
Proof.
  intros k r Hk Hr; destruct (tp_pole_j k Hk) as [j Hj].
  apply (tp_dom_between (j + 1)); rewrite plus_IZR; lra.
Qed.

(** The piece between [j * PI - PI / 2] and [j * PI + PI / 2] is
    [(- (PI / 2), PI / 2)] moved by [j * PI], where Stdlib's
    [tan_increasing] applies. *)
Lemma tp_tan_inc_j :
  forall j r t,
  IZR j * PI - PI / 2 < r -> r <= t -> t < IZR j * PI + PI / 2 -> tan r <= tan t.
Proof.
  intros j r t H1 H2 H3.
  assert (Hr : tan r = tan (r - IZR j * PI)).
  { rewrite <- (tp_tan_period (r - IZR j * PI) j); f_equal; ring. }
  assert (Ht : tan t = tan (t - IZR j * PI)).
  { rewrite <- (tp_tan_period (t - IZR j * PI) j); f_equal; ring. }
  rewrite Hr, Ht; apply tp_tan_inc; lra.
Qed.

Lemma tp_tan_period1 : forall x j, tan (x + (IZR j + 1) * PI) = tan x.
Proof. intros x j; rewrite <- (tp_tan_period x (j + 1)), plus_IZR; reflexivity. Qed.

Lemma tan_piece_inc :
  forall k r t, Z.odd k = true ->
  IZR k * (PI / 2) < r -> r <= t -> t < (IZR k + 2) * (PI / 2) -> tan r <= tan t.
Proof.
  intros k r t Hk H1 H2 H3; destruct (tp_pole_j k Hk) as [j Hj].
  apply (tp_tan_inc_j (j + 1)); try rewrite plus_IZR; lra.
Qed.

(** [tan = sin / cos], and [cos] is 0 only at the poles ([cos_eq_0_0]). *)
Lemma tan_dom_cont : forall r, tan_dom r -> continuity_pt tan r.
Proof.
  intros r Hr.
  assert (Hc : cos r <> 0).
  { intro H0; destruct (cos_eq_0_0 r H0) as [k Hk]; apply (Hr k); rewrite Hk; field. }
  change (continuity_pt (sin / cos)%F r).
  apply continuity_pt_div; [apply continuity_sin | apply continuity_cos | exact Hc].
Qed.

(** The pole [p = j * PI + PI / 2]. Left of it, [atan M1 + j * PI] has
    [tan] equal to [M1], and is at least [r0 = max a (j * PI)] because
    [tan] increases on the piece and [M1 > tan r0]. Right of it,
    [atan (- M2) + (j + 1) * PI] likewise, below [t0 = min b ((j + 1) * PI)]. *)
Lemma tp_pole_unbounded_j :
  forall j a b M, a < IZR j * PI + PI / 2 < b ->
  exists r t,
    a <= r < IZR j * PI + PI / 2 /\ tan_dom r /\ M <= tan r /\
    IZR j * PI + PI / 2 < t <= b /\ tan_dom t /\ tan t <= - M.
Proof.
  intros j a b M [Ha Hb].
  pose proof PI_RGT_0 as Hpi.
  set (r0 := Rmax a (IZR j * PI)).
  set (M1 := Rmax M (tan r0) + 1).
  set (t0 := Rmin b ((IZR j + 1) * PI)).
  set (M2 := Rmax M (- tan t0) + 1).
  assert (Hr0 : a <= r0 /\ IZR j * PI <= r0 < IZR j * PI + PI / 2).
  { unfold r0; split; [apply Rmax_l |]; split; [apply Rmax_r |].
    apply Rmax_lub_lt; lra. }
  assert (Ht0 : t0 <= b /\ IZR j * PI + PI / 2 < t0 <= (IZR j + 1) * PI).
  { unfold t0; split; [apply Rmin_l |]; split; [| apply Rmin_r].
    apply Rmin_glb_lt; lra. }
  assert (HM1 : M <= M1 - 1 /\ tan r0 <= M1 - 1).
  { pose proof (Rmax_l M (tan r0)); pose proof (Rmax_r M (tan r0)); unfold M1; lra. }
  assert (HM2 : M <= M2 - 1 /\ - tan t0 <= M2 - 1).
  { pose proof (Rmax_l M (- tan t0)); pose proof (Rmax_r M (- tan t0)); unfold M2; lra. }
  destruct (atan_bound M1) as [Hm1 Hp1].
  destruct (atan_bound (- M2)) as [Hm2 Hp2].
  assert (Hr : r0 <= atan M1 + IZR j * PI).
  { destruct (Rle_or_lt r0 (atan M1 + IZR j * PI)) as [H | H]; [exact H | exfalso].
    assert (H' : tan (atan M1 + IZR j * PI) <= tan r0) by (apply (tp_tan_inc_j j); lra).
    rewrite tp_tan_period, tan_atan in H'; lra. }
  assert (Ht : atan (- M2) + (IZR j + 1) * PI <= t0).
  { destruct (Rle_or_lt (atan (- M2) + (IZR j + 1) * PI) t0) as [H | H]; [exact H | exfalso].
    assert (H' : tan t0 <= tan (atan (- M2) + (IZR j + 1) * PI)).
    { apply (tp_tan_inc_j (j + 1)); try rewrite plus_IZR; lra. }
    rewrite tp_tan_period1, tan_atan in H'; lra. }
  exists (atan M1 + IZR j * PI), (atan (- M2) + (IZR j + 1) * PI).
  rewrite tp_tan_period1, tp_tan_period, !tan_atan.
  split; [lra |]; split; [apply (tp_dom_between j); lra |]; split; [lra |].
  split; [lra |]; split; [apply (tp_dom_between (j + 1)); rewrite plus_IZR; lra |]; lra.
Qed.

(** On each side of a pole, [tan] takes values beyond any bound. *)
Lemma tan_pole_unbounded :
  forall k a b M, Z.odd k = true -> a < IZR k * (PI / 2) < b ->
  exists r t,
    a <= r < IZR k * (PI / 2) /\ tan_dom r /\ M <= tan r /\
    IZR k * (PI / 2) < t <= b /\ tan_dom t /\ tan t <= - M.
Proof.
  intros k a b M Hk Hab; destruct (tp_pole_j k Hk) as [j Hj]; rewrite Hj in *.
  apply tp_pole_unbounded_j; exact Hab.
Qed.

(** A pole in [(a, a + PI]]: [j * PI + PI / 2] for [j = up ((a - PI / 2) / PI)]. *)
Lemma tp_pole_in : forall a, exists j, a < IZR j * PI + PI / 2 <= a + PI.
Proof.
  intros a; destruct (tp_up (a - PI / 2) PI PI_RGT_0) as [j Hj]; exists j; lra.
Qed.

(** With the pole [p] of [tp_pole_in], [tan] is beyond [M] left of [p]
    in [[a, p)]. If [p < b], it is below [- M] right of [p] in [(p, b]];
    otherwise [p = b = a + PI], and [a = p - PI] is a pole too, with
    [tan] below [- M] right of it in [(a, b]]. *)
Lemma tan_wide :
  forall a b M, a + PI <= b ->
  exists r t,
    a <= r <= b /\ tan_dom r /\ M <= tan r /\
    a <= t <= b /\ tan_dom t /\ tan t <= - M.
Proof.
  intros a b M Hab; destruct (tp_pole_in a) as [j Hj].
  pose proof PI_RGT_0 as Hpi.
  destruct (tp_pole_unbounded_j j a (b + 1) M) as (r & _ & Hr & Hdr & HMr & _); [lra |].
  destruct (Rlt_or_le (IZR j * PI + PI / 2) b) as [Hb | Hb].
  - destruct (tp_pole_unbounded_j j a b M) as (_ & t & _ & _ & _ & Ht & Hdt & HMt); [lra |].
    exists r, t; repeat split; lra || assumption.
  - destruct (tp_pole_unbounded_j (j - 1) (a - 1) b M) as (_ & t & _ & _ & _ & Ht & Hdt & HMt);
      rewrite minus_IZR in *; [lra |].
    exists r, t; repeat split; lra || assumption.
Qed.

Lemma tan_wide_pole : forall a b, a + PI <= b -> exists r, a <= r <= b /\ ~ tan_dom r.
Proof.
  intros a b Hab; destruct (tp_pole_in a) as [j Hj].
  exists (IZR j * PI + PI / 2); split; [lra |].
  intro H; apply (H j); field.
Qed.

(** A finite float is a quotient of integers [n / d] with [d > 0]. *)
Lemma tp_B2R_rat :
  forall w : f64, is_finite w = true -> exists n d : Z, (0 < d)%Z /\ B2R w = IZR n / IZR d.
Proof.
  intros [s | s | | s m e He] Hw; try discriminate.
  - exists 0%Z, 1%Z; split; [lia |]; simpl; field.
  - unfold B2R, F2R; cbn [Fnum Fexp].
    destruct e as [|p|p].
    + exists (cond_Zopp s (Zpos m)), 1%Z; split; [lia |]; cbn [bpow]; field.
    + exists (cond_Zopp s (Zpos m) * Z.pow_pos 2 p)%Z, 1%Z; split; [lia |].
      rewrite mult_IZR; cbn [bpow radix_val radix2]; field.
    + exists (cond_Zopp s (Zpos m)), (Z.pow_pos 2 p); split.
      * change (Z.pow_pos 2 p) with (2 ^ Zpos p)%Z; apply Z.pow_pos_nonneg; lia.
      * cbn [bpow radix_val radix2]; reflexivity.
Qed.

(** If π is irrational, no finite [f64] is a pole: it is a dyadic
    rational. *)
Lemma tan_dom_f64 :
  pi_irrational -> forall w : f64, is_finite w = true -> tan_dom (B2R w).
Proof.
  intros Hpi w Hw k Hk.
  destruct (tp_B2R_rat w Hw) as (n & d & Hd & Hnd).
  (* [(k + 1/2) * PI = n / d], so [PI = 2 * n / (d * (2 * k + 1))], whose
     divisor is a nonzero integer; flip both signs if it is negative. *)
  assert (Hd' : IZR d <> 0) by (apply not_0_IZR; lia).
  assert (Hk' : 2 * IZR k + 1 <> 0).
  { replace (2 * IZR k + 1) with (IZR (2 * k + 1)) by (rewrite plus_IZR, mult_IZR; reflexivity).
    apply not_0_IZR; lia. }
  assert (Hn : IZR n = (IZR k + / 2) * PI * IZR d).
  { rewrite <- Hk, Hnd; field; exact Hd'. }
  assert (Heq : PI = IZR (2 * n) / IZR (d * (2 * k + 1))).
  { rewrite !mult_IZR, plus_IZR, mult_IZR, Hn; field; split; assumption. }
  destruct (Z.lt_trichotomy 0 (d * (2 * k + 1))) as [Hq | [Hq | Hq]].
  - exact (Hpi _ _ Hq Heq).
  - symmetry in Hq; apply Z.mul_eq_0 in Hq; lia.
  - apply (Hpi (- (2 * n))%Z (- (d * (2 * k + 1)))%Z); [lia |].
    rewrite Heq, !opp_IZR; field.
    apply not_0_IZR; lia.
Qed.
