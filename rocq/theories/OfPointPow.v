(** * MPFR functions made of functions of [f64]s: [atan2], [pow] and
    [pow_si]

    Each of these MPFR functions of [of_point p] satisfies the hypothesis
    of [Mpfr.v] at the exponent range of [f64] where the field of [p]
    satisfies its counterpart in [Contract.v]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Mpfr MpfrRound MpfrIdeal IdealRound IdealGetD
  Contract OfPointCore OfPoint.

Open Scope R_scope.

(** ** [lift2] and [lift_si] at known arguments *)

Lemma lift2_eq :
  forall F h rnd v u,
  lift2 F h rnd v u =
  match F (ideal_get_d RNDD v) (ideal_get_d RNDD u) with
  | Some r => lift_val rnd r (h rnd (ideal_get_d RNDD v) (ideal_get_d RNDD u))
  | None => with_val (h rnd (ideal_get_d RNDD v) (ideal_get_d RNDD u))
  end.
Proof. reflexivity. Qed.

Lemma lift2_some :
  forall F h rnd v u x y r,
  ideal_get_d RNDD v = x -> ideal_get_d RNDD u = y -> F x y = Some r ->
  lift2 F h rnd v u = lift_val rnd r (h rnd x y).
Proof. intros F h rnd v u x y r Ev Eu E. rewrite lift2_eq, Ev, Eu, E. reflexivity. Qed.

Lemma lift2_none :
  forall F h rnd v u x y,
  ideal_get_d RNDD v = x -> ideal_get_d RNDD u = y -> F x y = None ->
  lift2 F h rnd v u = with_val (h rnd x y).
Proof. intros F h rnd v u x y Ev Eu E. rewrite lift2_eq, Ev, Eu, E. reflexivity. Qed.

Lemma lift_si_eq :
  forall F h rnd v n,
  lift_si F h rnd v n =
  match F (ideal_get_d RNDD v) n with
  | Some r => lift_val rnd r (h rnd (ideal_get_d RNDD v) n)
  | None => with_val (h rnd (ideal_get_d RNDD v) n)
  end.
Proof. reflexivity. Qed.

Lemma lift_si_some :
  forall F h rnd v n x r,
  ideal_get_d RNDD v = x -> F x n = Some r ->
  lift_si F h rnd v n = lift_val rnd r (h rnd x n).
Proof. intros F h rnd v n x r Ev E. rewrite lift_si_eq, Ev, E. reflexivity. Qed.

Lemma lift_si_none :
  forall F h rnd v n x,
  ideal_get_d RNDD v = x -> F x n = None ->
  lift_si F h rnd v n = with_val (h rnd x n).
Proof. intros F h rnd v n x Ev E. rewrite lift_si_eq, Ev, E. reflexivity. Qed.

(** ** Conversions and exact results *)

(** [ideal_get_d] keeps the zeros and the infinities, as [with_val]
    does. *)
Lemma get_d_zero : forall rnd s, ideal_get_d rnd (MZero s) = B754_zero s.
Proof. intros rnd s. exact (ideal_get_d_with_val rnd (B754_zero s)). Qed.

Lemma get_d_inf : forall rnd s, ideal_get_d rnd (MInf s) = B754_infinity s.
Proof. intros rnd s. exact (ideal_get_d_with_val rnd (B754_infinity s)). Qed.

(** An [f64] that [with_val] makes [MNum 1] is 1, which is above
    [2^-1022], so [lift_val] gives it whatever the exact result. *)
Lemma lift_val_one :
  forall rnd r w, with_val w = MNum 1 -> lift_val rnd r w = MNum 1.
Proof.
intros rnd r w Hw.
assert (H1 : B2R w = 1).
{ destruct w as [s|s| |s mx ex Hx]; try discriminate Hw.
  change (MNum (B2R (B754_finite s mx ex Hx)) = MNum 1) in Hw.
  congruence. }
rewrite lift_val_exact; [exact Hw|].
right; right.
rewrite H1, Rabs_pos_eq by lra.
assert (Hb : bpow radix2 (-1022) < bpow radix2 0) by (apply bpow_lt; lia).
change (bpow radix2 0) with 1 in Hb.
exact Hb.
Qed.

(** An infinite [f64] [w] is what [lift_val] gives. *)
Lemma lift_val_inf :
  forall rnd r s, lift_val rnd r (B754_infinity s) = MInf s.
Proof. intros rnd r s. rewrite lift_val_exact by (left; reflexivity). reflexivity. Qed.

(** ** The exact results of [OfPoint.v] at the points of [Mpfr.v] *)

Lemma atan2_val_fin :
  forall y x, is_finite y = true -> is_finite x = true ->
  atan2_val y x = Some (Ratan2 (B2R y) (B2R x)).
Proof. intros y x Hy Hx. unfold atan2_val. rewrite Hy, Hx. reflexivity. Qed.

Lemma atan2_val_pinf :
  forall y, is_finite y = true -> atan2_val y (B754_infinity false) = None.
Proof. intros [s|s| |s my ey Hb] Hy; try discriminate Hy; reflexivity. Qed.

Lemma atan2_val_minf :
  forall y, is_finite y = true ->
  atan2_val y (B754_infinity true) = Some (if Rlt_dec 0 (B2R y) then PI else - PI).
Proof. intros [s|s| |s my ey Hb] Hy; try discriminate Hy; reflexivity. Qed.

Lemma atan2_val_inf_l :
  forall s x, is_finite x = true ->
  atan2_val (B754_infinity s) x = Some (if s then - (PI / 2) else PI / 2).
Proof. intros s [sx|sx| |sx mx ex Hb] Hx; try discriminate Hx; reflexivity. Qed.

Lemma pow_val_fin :
  forall x y, is_finite x = true -> is_finite y = true ->
  pow_val x y = Some (Rpow (B2R x) (B2R y)).
Proof. intros x y Hx Hy. unfold pow_val. rewrite Hx, Hy. reflexivity. Qed.

Lemma pow_val_inf_r : forall x s, pow_val x (B754_infinity s) = None.
Proof. intros x s. unfold pow_val. destruct (is_finite x); reflexivity. Qed.

Lemma pown_val_fin :
  forall x n, is_finite x = true -> pown_val x n = Some (powerRZ (B2R x) n).
Proof. intros x n Hx. unfold pown_val. rewrite Hx. reflexivity. Qed.

(** ** The theorems *)

Theorem of_point_atan2_ok :
  forall p, atan2_c (p_atan2 p) -> atan2_ok (-1073) 1024 (of_point p).
Proof.
intros p (Hc & H1 & H2 & H3 & H4 & H5 & H6 & H7).
unfold atan2_ok.
change (mpfr_atan2 (of_point p)) with (lift2 atan2_val (p_atan2 p)).
repeat split.
- (* finite arguments: [lift_val] of [Ratan2] *)
  intros rnd y x Hy Hx HD.
  rewrite (lift2_some _ _ _ _ _ _ _ _ (ideal_get_d_with_val _ y) (ideal_get_d_with_val _ x)
    (atan2_val_fin y x Hy Hx)).
  apply lift_val_correct. exact (Hc rnd y x Hy Hx HD).
- intros rnd y Hy Hpos.
  destruct (H1 rnd y Hy Hpos) as [s' Hs']. exists s'.
  rewrite (lift2_none _ _ _ _ _ _ _ (ideal_get_d_with_val _ y) (get_d_inf _ false)
    (atan2_val_pinf y Hy)), Hs'.
  reflexivity.
- intros rnd y Hy Hneg.
  destruct (H2 rnd y Hy Hneg) as [s' Hs']. exists s'.
  rewrite (lift2_none _ _ _ _ _ _ _ (ideal_get_d_with_val _ y) (get_d_inf _ false)
    (atan2_val_pinf y Hy)), Hs'.
  reflexivity.
- intros rnd s.
  destruct (H3 rnd s) as [s' Hs']. exists s'.
  rewrite (lift2_none _ _ _ _ _ _ _ (get_d_zero _ s) (get_d_inf _ false)
    (atan2_val_pinf (B754_zero s) eq_refl)), Hs'.
  reflexivity.
- intros rnd y Hy Hpos.
  assert (E : atan2_val y (B754_infinity true) = Some PI).
  { rewrite (atan2_val_minf y Hy). destruct (Rlt_dec 0 (B2R y)); [reflexivity | lra]. }
  rewrite (lift2_some _ _ _ _ _ _ _ _ (ideal_get_d_with_val _ y) (get_d_inf _ true) E).
  apply lift_val_correct. exact (H4 rnd y Hy Hpos).
- intros rnd y Hy Hneg.
  assert (E : atan2_val y (B754_infinity true) = Some (- PI)).
  { rewrite (atan2_val_minf y Hy). destruct (Rlt_dec 0 (B2R y)); [lra | reflexivity]. }
  rewrite (lift2_some _ _ _ _ _ _ _ _ (ideal_get_d_with_val _ y) (get_d_inf _ true) E).
  apply lift_val_correct. exact (H5 rnd y Hy Hneg).
- intros rnd x Hx.
  rewrite (lift2_some _ _ _ _ _ _ _ _ (get_d_inf _ false) (ideal_get_d_with_val _ x)
    (atan2_val_inf_l false x Hx)).
  apply lift_val_correct. exact (H6 rnd x Hx).
- intros rnd x Hx.
  rewrite (lift2_some _ _ _ _ _ _ _ _ (get_d_inf _ true) (ideal_get_d_with_val _ x)
    (atan2_val_inf_l true x Hx)).
  apply lift_val_correct. exact (H7 rnd x Hx).
Qed.

Theorem of_point_pow_ok :
  forall p, pow_c (p_pow p) -> pow_ok (-1073) 1024 (of_point p).
Proof.
intros p (Hc & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14).
unfold pow_ok.
change (mpfr_pow (of_point p)) with (lift2 pow_val (p_pow p)).
repeat split.
- (* finite arguments: [lift_val] of [Rpow] *)
  intros rnd x y Hx Hy HD.
  rewrite (lift2_some _ _ _ _ _ _ _ _ (ideal_get_d_with_val _ x) (ideal_get_d_with_val _ y)
    (pow_val_fin x y Hx Hy)).
  apply lift_val_correct. exact (Hc rnd x y Hx Hy HD).
- (* [pow(+0, y) = +inf] for a finite [y < 0]: the [f64] is infinite *)
  intros rnd y Hy Hneg.
  rewrite (lift2_some _ _ _ _ _ _ _ _ (get_d_zero _ false) (ideal_get_d_with_val _ y)
    (pow_val_fin (B754_zero false) y eq_refl Hy)), (H1 rnd y Hy Hneg).
  apply lift_val_inf.
- intros rnd.
  rewrite (lift2_none pow_val _ _ _ _ _ _ (get_d_zero _ false) (get_d_inf _ true)
    (pow_val_inf_r _ true)), (H2 rnd).
  reflexivity.
- intros rnd.
  destruct (H3 rnd) as [s Hs]. exists s.
  rewrite (lift2_none pow_val _ _ _ _ _ _ (get_d_zero _ false) (get_d_inf _ false)
    (pow_val_inf_r _ false)), Hs.
  reflexivity.
- (* [pow(+0, ±0) = 1]: the [f64] is 1 *)
  intros rnd s.
  rewrite (lift2_some _ _ _ _ _ _ _ _ (get_d_zero _ false) (get_d_zero _ s)
    (pow_val_fin (B754_zero false) (B754_zero s) eq_refl eq_refl)).
  apply lift_val_one.
  exact (with_val_round_one rnd 1 _ (or_introl eq_refl) (H4 rnd s)).
- intros rnd s.
  rewrite (lift2_none pow_val _ _ _ _ _ _ (get_d_inf _ false) (get_d_zero _ s) eq_refl).
  exact (with_val_round_one rnd 1 _ (or_introl eq_refl) (H5 rnd s)).
- (* [pow(+1, ±inf) = 1]: [MNum 1] converts to the [f64] 1 *)
  intros rnd s.
  destruct (ideal_get_d_one RNDD) as [Hf Hv].
  rewrite (lift2_none pow_val _ _ _ _ _ _ eq_refl (get_d_inf _ s) (pow_val_inf_r _ s)).
  exact (with_val_round_one rnd 1 _ (or_introl eq_refl) (H6 rnd _ s Hf Hv)).
- intros rnd x Hx Hr.
  rewrite (lift2_none pow_val _ _ _ _ _ _ (ideal_get_d_with_val _ x) (get_d_inf _ true)
    (pow_val_inf_r _ true)), (H7 rnd x Hx Hr).
  reflexivity.
- intros rnd x Hx Hr.
  destruct (H8 rnd x Hx Hr) as [s Hs]. exists s.
  rewrite (lift2_none pow_val _ _ _ _ _ _ (ideal_get_d_with_val _ x) (get_d_inf _ true)
    (pow_val_inf_r _ true)), Hs.
  reflexivity.
- intros rnd x Hx Hr.
  destruct (H9 rnd x Hx Hr) as [s Hs]. exists s.
  rewrite (lift2_none pow_val _ _ _ _ _ _ (ideal_get_d_with_val _ x) (get_d_inf _ false)
    (pow_val_inf_r _ false)), Hs.
  reflexivity.
- intros rnd x Hx Hr.
  rewrite (lift2_none pow_val _ _ _ _ _ _ (ideal_get_d_with_val _ x) (get_d_inf _ false)
    (pow_val_inf_r _ false)), (H10 rnd x Hx Hr).
  reflexivity.
- intros rnd y Hy Hneg.
  destruct (H11 rnd y Hy Hneg) as [s Hs]. exists s.
  rewrite (lift2_none pow_val _ _ _ _ _ _ (get_d_inf _ false) (ideal_get_d_with_val _ y)
    eq_refl), Hs.
  reflexivity.
- intros rnd.
  destruct (H12 rnd) as [s Hs]. exists s.
  rewrite (lift2_none pow_val _ _ _ _ _ _ (get_d_inf _ false) (get_d_inf _ true) eq_refl), Hs.
  reflexivity.
- intros rnd y Hy Hpos.
  rewrite (lift2_none pow_val _ _ _ _ _ _ (get_d_inf _ false) (ideal_get_d_with_val _ y)
    eq_refl), (H13 rnd y Hy Hpos).
  reflexivity.
- intros rnd.
  rewrite (lift2_none pow_val _ _ _ _ _ _ (get_d_inf _ false) (get_d_inf _ false) eq_refl),
    (H14 rnd).
  reflexivity.
Qed.

Theorem of_point_pown_ok :
  forall p, pown_c (p_pown p) -> pown_ok (-1073) 1024 (of_point p).
Proof.
intros p (Hc & H1 & H2 & H3 & H4 & H5 & H6 & H7).
unfold pown_ok.
change (mpfr_pow_si (of_point p)) with (lift_si pown_val (p_pown p)).
repeat split.
- (* finite [x]: [lift_val] of [powerRZ] *)
  intros rnd x n Hn Hx HD.
  rewrite (lift_si_some _ _ _ _ _ _ _ (ideal_get_d_with_val _ x) (pown_val_fin x n Hx)).
  apply lift_val_correct. exact (Hc rnd x n Hn Hx HD).
- (* [pow_si(±0, n)] for [n < 0]: the [f64] is infinite *)
  intros rnd s n Hn Hneg Hev.
  rewrite (lift_si_some _ _ _ _ _ _ _ (get_d_zero _ s) (pown_val_fin (B754_zero s) n eq_refl)),
    (H1 rnd s n Hn Hneg Hev).
  apply lift_val_inf.
- intros rnd s n Hn Hneg Hodd.
  rewrite (lift_si_some _ _ _ _ _ _ _ (get_d_zero _ s) (pown_val_fin (B754_zero s) n eq_refl)),
    (H2 rnd s n Hn Hneg Hodd).
  apply lift_val_inf.
- intros rnd n Hn Hneg.
  destruct (H3 rnd n Hn Hneg) as [s Hs]. exists s.
  rewrite (lift_si_none pown_val _ _ _ _ _ (get_d_inf _ false) eq_refl), Hs.
  reflexivity.
- intros rnd.
  rewrite (lift_si_none pown_val _ _ _ _ _ (get_d_inf _ false) eq_refl).
  exact (with_val_round_one rnd 1 _ (or_introl eq_refl) (H4 rnd)).
- intros rnd n Hn Hpos.
  rewrite (lift_si_none pown_val _ _ _ _ _ (get_d_inf _ false) eq_refl), (H5 rnd n Hn Hpos).
  reflexivity.
- intros rnd n Hn Hneg Hodd.
  destruct (H6 rnd n Hn Hneg Hodd) as [s Hs]. exists s.
  rewrite (lift_si_none pown_val _ _ _ _ _ (get_d_inf _ true) eq_refl), Hs.
  reflexivity.
- intros rnd n Hn Hpos Hodd.
  rewrite (lift_si_none pown_val _ _ _ _ _ (get_d_inf _ true) eq_refl), (H7 rnd n Hn Hpos Hodd).
  reflexivity.
Qed.
