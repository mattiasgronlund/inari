(** * [Interval::FRAC_1_PI], [FRAC_2_PI], [FRAC_2_SQRT_PI], [SQRT_2] and [FRAC_1_SQRT_2] are the tightest intervals around their values

    1 and 2 divided by the rational bounds [pi_lo] and [pi_hi] of π
    ([PI_Q] in [ConstPi.v]) bound [1 / π] and [2 / π]. The bounds [lo] and
    [hi] of the other constants are compared with their values through
    squares, which [vm_compute] computes exactly: [lo < 2 / sqrt π < hi]
    if [lo^2 * pi_hi < 4 < hi^2 * pi_lo], [lo < sqrt 2 < hi] if
    [lo^2 < 2 < hi^2], and [lo < 1 / sqrt 2 < hi] if
    [2 * lo^2 < 1 < 2 * hi^2], all bounds being positive. Each theorem
    also covers the [DecInterval] constant that [def_com!] makes from the
    [Interval] one, whose interval is the same. *)

From Stdlib Require Import ZArith Reals Lra QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 ConstTight ConstPi.

Open Scope R_scope.

(** An integer as a rational has the same real value. *)
Lemma Q2R_Z : forall z : Z, Q2R (z # 1) = IZR z.
Proof.
  intros z. unfold Q2R. cbn [Qnum Qden]. field.
Qed.

(** [z / pi_hi <= z / π <= z / pi_lo] for an integer [z >= 0], by [PI_Q].
    The sign condition is a boolean, so that [eq_refl] proves it for a
    literal. *)
Lemma div_PI_Q :
  forall z : Z, (0 <=? z)%Z = true ->
  Q2R ((z # 1) / pi_hi) <= IZR z / PI <= Q2R ((z # 1) / pi_lo).
Proof.
  intros z Hz.
  apply Z.leb_le, IZR_le in Hz.
  pose proof PI_Q as [Hlo Hhi].
  assert (Hlo0 : 0 < Q2R pi_lo).
  { rewrite <- (Q2R_Z 0). apply Qlt_Rlt. vm_compute; reflexivity. }
  rewrite !Q2R_div by (intro H; vm_compute in H; discriminate H).
  rewrite (Q2R_Z z).
  (* [/ x] is decreasing for [x > 0], and [pi_lo < π < pi_hi]. *)
  unfold Rdiv. split; apply Rmult_le_compat_l; try exact Hz;
    apply Rinv_le_contravar; lra.
Qed.

(** If the squares of the positive floats [a] and [b] lie strictly below
    and above rational bounds [l] and [u] of [y], then [sqrt y] lies
    strictly between [a] and [b], as [sqrt] is increasing and
    [sqrt (x * x) = x] for [x >= 0]. *)
Lemma const_tightest_sqrt :
  forall (a b : f64) (y : R) (l u : Q),
  is_finite a = true -> is_finite b = true -> Bsucc a = b ->
  (0 < B2Q a)%Q -> (0 < B2Q b)%Q ->
  (B2Q a * B2Q a < l)%Q -> (u < B2Q b * B2Q b)%Q ->
  Q2R l <= y <= Q2R u ->
  is_tightest (fun r => r = sqrt y) (Interval.const_interval a b).
Proof.
  intros a b y l u Ha Hb Hab Ha0 Hb0 Hl Hu Hy.
  apply const_tightest; [exact Ha | exact Hb | exact Hab |].
  apply Qlt_Rlt in Ha0. apply Qlt_Rlt in Hb0.
  apply Qlt_Rlt in Hl. apply Qlt_Rlt in Hu.
  rewrite Q2R_mult in Hl, Hu. rewrite Q2R_Z in Ha0, Hb0.
  rewrite !B2Q_correct.
  set (A := Q2R (B2Q a)) in *. set (B := Q2R (B2Q b)) in *.
  split.
  - (* [A = sqrt (A * A) < sqrt y] *)
    assert (HA : A = sqrt (A * A)) by (rewrite sqrt_square by lra; reflexivity).
    rewrite HA at 1. apply sqrt_lt_1_alt. split; [nra | lra].
  - (* [sqrt y < sqrt (B * B) = B] *)
    assert (HB : B = sqrt (B * B)) by (rewrite sqrt_square by lra; reflexivity).
    rewrite HB. apply sqrt_lt_1_alt. split; [nra | lra].
Qed.

Theorem FRAC_1_PI_tightest :
  is_tightest (fun r => r = / PI) Interval.FRAC_1_PI /\
  is_tightest (fun r => r = / PI) (itv DecInterval.FRAC_1_PI).
Proof.
  assert (H : is_tightest (fun r => r = / PI) Interval.FRAC_1_PI).
  { apply (const_tightest_Q _ _ _ ((1 # 1) / pi_hi) ((1 # 1) / pi_lo)).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply B2SF_inj; vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - (* [1 / π] is [/ π]. *)
      pose proof (div_PI_Q 1 eq_refl) as Hd. lra. }
  split; exact H.
Qed.

Theorem FRAC_2_PI_tightest :
  is_tightest (fun r => r = 2 / PI) Interval.FRAC_2_PI /\
  is_tightest (fun r => r = 2 / PI) (itv DecInterval.FRAC_2_PI).
Proof.
  assert (H : is_tightest (fun r => r = 2 / PI) Interval.FRAC_2_PI).
  { apply (const_tightest_Q _ _ _ ((2 # 1) / pi_hi) ((2 # 1) / pi_lo)).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply B2SF_inj; vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - exact (div_PI_Q 2 eq_refl). }
  split; exact H.
Qed.

Theorem FRAC_2_SQRT_PI_tightest :
  is_tightest (fun r => r = 2 / sqrt PI) Interval.FRAC_2_SQRT_PI /\
  is_tightest (fun r => r = 2 / sqrt PI) (itv DecInterval.FRAC_2_SQRT_PI).
Proof.
  (* [2 / sqrt π = sqrt 4 / sqrt π = sqrt (4 / π)], and [4 / π] lies
     between [4 / pi_hi] and [4 / pi_lo]. Comparing [lo^2] with
     [4 / pi_hi] is comparing [lo^2 * pi_hi] with 4. *)
  assert (Hs : 2 / sqrt PI = sqrt (4 / PI)).
  { rewrite sqrt_div_alt by exact PI_RGT_0.
    replace 4 with (2 * 2) by lra. rewrite sqrt_square by lra. reflexivity. }
  rewrite Hs.
  assert (H : is_tightest (fun r => r = sqrt (4 / PI)) Interval.FRAC_2_SQRT_PI).
  { apply (const_tightest_sqrt _ _ _ ((4 # 1) / pi_hi) ((4 # 1) / pi_lo)).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply B2SF_inj; vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - exact (div_PI_Q 4 eq_refl). }
  split; exact H.
Qed.

Theorem SQRT_2_tightest :
  is_tightest (fun r => r = sqrt 2) Interval.SQRT_2 /\
  is_tightest (fun r => r = sqrt 2) (itv DecInterval.SQRT_2).
Proof.
  assert (H : is_tightest (fun r => r = sqrt 2) Interval.SQRT_2).
  { apply (const_tightest_sqrt _ _ _ (2 # 1) (2 # 1)).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply B2SF_inj; vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - rewrite Q2R_Z. lra. }
  split; exact H.
Qed.

Theorem FRAC_1_SQRT_2_tightest :
  is_tightest (fun r => r = / sqrt 2) Interval.FRAC_1_SQRT_2 /\
  is_tightest (fun r => r = / sqrt 2) (itv DecInterval.FRAC_1_SQRT_2).
Proof.
  (* [/ sqrt 2 = sqrt (1 / 2)], so [lo^2 < 1 / 2 < hi^2] suffices, that
     is [2 * lo^2 < 1 < 2 * hi^2]. *)
  rewrite <- sqrt_inv.
  assert (H : is_tightest (fun r => r = sqrt (/ 2)) Interval.FRAC_1_SQRT_2).
  { apply (const_tightest_sqrt _ _ _ (1 # 2) (1 # 2)).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply B2SF_inj; vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - assert (Hh : Q2R (1 # 2) = / 2) by (unfold Q2R; cbn [Qnum Qden]; field).
      rewrite Hh. lra. }
  split; exact H.
Qed.
