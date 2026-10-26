(** * [x * y] of intervals where one argument has 0 in its interior

    [x * y] of [Interval]s returns the tightest interval that contains the
    image of the box [x × y] under [*] when exactly one of [x = [a, b]]
    and [y = [c, d]] is in the class [M] ([a < 0 < b]), and the other is in
    [N0] or [N1] ([a < 0] and [b <= 0]) or in [P0] or [P1] ([0 <= a] and
    [0 < b]): the cases [M × N], [M × P], [N × M] and [P × M].

    As in [AddSub.v], the second lane of [[-a; b]] is the largest real [r]
    of [x], and the first lane the largest negation [-r] ([tight]). The
    first lane of the result has to be the least float or +inf at or above
    the largest negated product [-(r * t)], and the second at or above the
    largest product [r * t]. Each is a product of [r] or [-r] and [t] or
    [-t], as [-(r * t) = (-r) * t = r * (-t)] and [r * t = (-r) * (-t)].
    Pick the form in which the factor from the argument in [N] or [P] is
    at least 0: [-r] or [-t] for [N], and [r] or [t] for [P]. That factor
    takes a value above 0, as the argument has a real that is not 0, and
    so does the other factor in either form, as the argument in [M] has
    reals below and above 0. Then
    [tight_mult_pos_r] (or [tight_mult_pos_l] if [x] is the argument in [N]
    or [P]) shows that the largest product is the product of the largest
    factors, i.e. of two lanes:
    - [M × N]: [r * (-t)] gives [b * (-c)], and [(-r) * (-t)] gives
      [(-a) * (-c)];
    - [M × P]: [(-r) * t] gives [(-a) * d], and [r * t] gives [b * d];
    - [N × M]: [(-r) * t] gives [(-a) * d], and [(-r) * (-t)] gives
      [(-a) * (-c)];
    - [P × M]: [r * (-t)] gives [b * (-c)], and [r * t] gives [b * d].

    [Interval::mul] picks exactly these lanes with [swap], [shuffle02] and
    [shuffle13], and multiplies them with [mul_ru], which gives
    [Bmult mode_UP] in each lane ([mul_ru_correct]). Each lane it
    multiplies is above 0, a positive float or +inf, so [mul_lane_pos] in
    [MulLane.v] shows that [Bmult mode_UP] gives the least float or +inf at
    or above their product, where +inf times anything above 0 is +inf
    ([umult]). [tightest_lanes] in [AddSub.v] puts the two lanes together
    ([tightest_mul_pos]).

    [N0] and [N1], and [P0] and [P1], take the same branch of
    [Interval::mul], and the proofs only need what they have in common
    ([mul_N_lanes], [mul_P_lanes]): the lane that is multiplied, [-a] for
    [N] and [b] for [P], is above 0, and the reals have one sign and
    include one that is not 0. *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer MaxMin DecBinary AddSub MulRu
  Classify2 Classes MulLane MulTight.

Open Scope R_scope.

(** ** The classes *)

(** What [x * y] needs of an [x] in [M]: both lanes are above 0, and [x]
    has a real below 0 and one above 0, i.e. a negation of a real above 0
    and a real above 0. *)
Lemma mul_M_lanes :
  forall x, valid x -> Interval.classify x = Some CM ->
  pos_lane (fst (rep x)) /\ pos_lane (snd (rep x)) /\ (exists r, mem r x) /\
  tight (bound (fst (rep x))) (fun r => mem (- r) x) /\
  tight (bound (snd (rep x))) (fun r => mem r x) /\
  (exists r, mem (- r) x /\ 0 < r) /\ (exists r, mem r x /\ 0 < r).
Proof.
intros x Hx Cx.
destruct (classify_lanes x CM Hx Cx) as [P0 P1].
destruct (classify_mem x CM Hx Cx) as [(rn & Hrn & Hrn0) Hp].
destruct (lanes_tight x Hx (not_nan_upper _ (pos_lane_upper _ P0)))
  as (_ & _ & Ex & T0 & T1).
split; [exact P0|]. split; [exact P1|]. split; [exact Ex|].
split; [exact T0|]. split; [exact T1|]. split; [|exact Hp].
exists (- rn). rewrite Ropp_involutive. split; [exact Hrn | lra].
Qed.

(** What [x * y] needs of an [x] in [N0] or [N1]: the first lane is above
    0, and the negations of the reals of [x] are at least 0, with one
    above 0. *)
Lemma mul_N_lanes :
  forall x, valid x ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  pos_lane (fst (rep x)) /\ (exists r, mem r x) /\
  tight (bound (fst (rep x))) (fun r => mem (- r) x) /\
  (forall r, mem (- r) x -> 0 <= r) /\ (exists r, mem (- r) x /\ 0 < r).
Proof.
intros x Hx Cx.
(* [N0] and [N1] both have reals at most 0, with one below 0. *)
assert (H : pos_lane (fst (rep x)) /\ (forall r, mem r x -> r <= 0) /\
            exists r, mem r x /\ r < 0).
{ destruct Cx as [Cx|Cx].
  - destruct (classify_lanes x CN0 Hx Cx) as (P0 & _ & _).
    destruct (classify_mem x CN0 Hx Cx) as (Hle & _ & Hn).
    split; [exact P0 | split; [exact Hle | exact Hn]].
  - destruct (classify_lanes x CN1 Hx Cx) as (P0 & _ & _).
    destruct (classify_mem x CN1 Hx Cx) as (Hlt & r1 & Hr1).
    split; [exact P0 | split].
    + intros r Hr. apply Rlt_le, Hlt, Hr.
    + exists r1. split; [exact Hr1 | apply Hlt, Hr1]. }
destruct H as (P0 & Hle & rn & Hrn & Hrn0).
destruct (lanes_tight x Hx (not_nan_upper _ (pos_lane_upper _ P0)))
  as (_ & _ & Ex & T0 & _).
split; [exact P0|]. split; [exact Ex|]. split; [exact T0|]. split.
- intros r Hr. specialize (Hle _ Hr). lra.
- exists (- rn). rewrite Ropp_involutive. split; [exact Hrn | lra].
Qed.

(** What [x * y] needs of an [x] in [P0] or [P1]: the second lane is
    above 0, and the reals of [x] are at least 0, with one above 0. *)
Lemma mul_P_lanes :
  forall x, valid x ->
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  pos_lane (snd (rep x)) /\ (exists r, mem r x) /\
  tight (bound (snd (rep x))) (fun r => mem r x) /\
  (forall r, mem r x -> 0 <= r) /\ (exists r, mem r x /\ 0 < r).
Proof.
intros x Hx Cx.
(* [P0] and [P1] both have reals at least 0, with one above 0. *)
assert (H : is_nan (fst (rep x)) = false /\ pos_lane (snd (rep x)) /\
            (forall r, mem r x -> 0 <= r) /\ exists r, mem r x /\ 0 < r).
{ destruct Cx as [Cx|Cx].
  - destruct (classify_lanes x CP0 Hx Cx) as (F0 & _ & P1).
    destruct (classify_mem x CP0 Hx Cx) as (Hge & _ & Hp).
    split; [exact (not_nan_upper _ (or_introl F0))|].
    split; [exact P1 | split; [exact Hge | exact Hp]].
  - destruct (classify_lanes x CP1 Hx Cx) as (F0 & _ & P1).
    destruct (classify_mem x CP1 Hx Cx) as (Hgt & r1 & Hr1).
    split; [exact (not_nan_upper _ (or_introl F0))|].
    split; [exact P1 | split].
    + intros r Hr. apply Rlt_le, Hgt, Hr.
    + exists r1. split; [exact Hr1 | apply Hgt, Hr1]. }
destruct H as (N0 & P1 & Hge & Hp).
destruct (lanes_tight x Hx N0) as (_ & _ & Ex & _ & T1).
split; [exact P1|]. split; [exact Ex|]. split; [exact T1|].
split; [exact Hge | exact Hp].
Qed.

(** ** The tightest interval *)

(** If the lanes [u0], [v0], [u1] and [v1] are above 0, the negated
    products of reals of [x] and [y] are the products [r * t] of reals of
    [A0] and [B0], whose largest is the product of the bounds of [u0] and
    [v0] (+inf if either is +inf), and likewise for the products with [A1],
    [B1], [u1] and [v1], then the lanes [Bmult mode_UP u0 v0] and
    [Bmult mode_UP u1 v1] give the tightest interval. *)
Lemma tightest_mul_pos :
  forall x y u0 v0 u1 v1 A0 B0 A1 B1,
  pos_lane u0 -> pos_lane v0 -> pos_lane u1 -> pos_lane v1 ->
  (exists r, mem r x) -> (exists t, mem t y) ->
  (forall s, image2 Rmult x y (- s) <-> exists r t, A0 r /\ B0 t /\ s = r * t) ->
  (forall s, image2 Rmult x y s <-> exists r t, A1 r /\ B1 t /\ s = r * t) ->
  tight (umult (bound u0) (bound v0)) (fun s => exists r t, A0 r /\ B0 t /\ s = r * t) ->
  tight (umult (bound u1) (bound v1)) (fun s => exists r t, A1 r /\ B1 t /\ s = r * t) ->
  is_tightest (image2 Rmult x y) {| rep := (Bmult mode_UP u0 v0, Bmult mode_UP u1 v1) |}.
Proof.
intros x y u0 v0 u1 v1 A0 B0 A1 B1 P0 Q0 P1 Q1 [r0 Hr0] [t0 Ht0] E0 E1 T0 T1.
apply (tightest_lanes _ _ (umult (bound u0) (bound v0)) (umult (bound u1) (bound v1))).
- exists (r0 * t0). exact (image2_mem Rmult x y r0 t0 Hr0 Ht0).
- exact (tight_ext _ _ _ (fun s => iff_sym (E0 s)) T0).
- exact (tight_ext _ _ _ (fun s => iff_sym (E1 s)) T1).
- exact (mul_lane_pos u0 v0 P0 Q0).
- exact (mul_lane_pos u1 v1 P1 Q1).
Qed.

(** ** The theorems *)

(** [M × N]: every [-t] is at least 0. The first lane is
    [RU(b * (-c))], for the largest [r * (-t)], and the second
    [RU((-a) * (-c))], for the largest [(-r) * (-t)]. *)
Lemma mul_MN :
  forall has_fma x y, valid x -> valid y ->
  Interval.classify x = Some CM ->
  (Interval.classify y = Some CN0 \/ Interval.classify y = Some CN1) ->
  exists z, Interval.mul has_fma x y = Some z /\ is_tightest (image2 Rmult x y) z.
Proof.
intros has_fma x y Hx Hy Cx Cy.
destruct (mul_M_lanes x Hx Cx) as (Px0 & Px1 & Ex & Tx0 & Tx1 & Nx & Px).
destruct (mul_N_lanes y Hy Cy) as (Py0 & Ey & Ty0 & Gy & Ny).
exists {| rep := (Bmult mode_UP (snd (rep x)) (fst (rep y)),
                  Bmult mode_UP (fst (rep x)) (fst (rep y))) |}.
split.
- (* [N0] and [N1] take the same branch: [x] swapped times [-c] twice. *)
  unfold Interval.mul.
  destruct Cy as [Cy|Cy]; rewrite (classify2_pair _ _ _ _ Cx Cy); cbv beta iota zeta;
    rewrite mul_ru_correct; reflexivity.
- apply (tightest_mul_pos x y _ _ _ _
    (fun r => mem r x) (fun t => mem (- t) y) (fun r => mem (- r) x) (fun t => mem (- t) y)
    Px1 Py0 Px0 Py0 Ex Ey (image2_mult_opp_r x y) (image2_mult_opp_lr x y)).
  + exact (tight_mult_pos_r _ _ _ _ Tx1 Ty0 Gy Px Ny).
  + exact (tight_mult_pos_r _ _ _ _ Tx0 Ty0 Gy Nx Ny).
Qed.

(** [M × P]: every [t] is at least 0. The first lane is [RU((-a) * d)],
    for the largest [(-r) * t], and the second [RU(b * d)], for the
    largest [r * t]. *)
Lemma mul_MP :
  forall has_fma x y, valid x -> valid y ->
  Interval.classify x = Some CM ->
  (Interval.classify y = Some CP0 \/ Interval.classify y = Some CP1) ->
  exists z, Interval.mul has_fma x y = Some z /\ is_tightest (image2 Rmult x y) z.
Proof.
intros has_fma x y Hx Hy Cx Cy.
destruct (mul_M_lanes x Hx Cx) as (Px0 & Px1 & Ex & Tx0 & Tx1 & Nx & Px).
destruct (mul_P_lanes y Hy Cy) as (Py1 & Ey & Ty1 & Gy & Py).
exists {| rep := (Bmult mode_UP (fst (rep x)) (snd (rep y)),
                  Bmult mode_UP (snd (rep x)) (snd (rep y))) |}.
split.
- (* [P0] and [P1] take the same branch: [x] times [d] twice. *)
  unfold Interval.mul.
  destruct Cy as [Cy|Cy]; rewrite (classify2_pair _ _ _ _ Cx Cy); cbv beta iota zeta;
    rewrite mul_ru_correct; reflexivity.
- apply (tightest_mul_pos x y _ _ _ _
    (fun r => mem (- r) x) (fun t => mem t y) (fun r => mem r x) (fun t => mem t y)
    Px0 Py1 Px1 Py1 Ex Ey (image2_mult_opp_l x y) (fun s => iff_refl _)).
  + exact (tight_mult_pos_r _ _ _ _ Tx0 Ty1 Gy Nx Py).
  + exact (tight_mult_pos_r _ _ _ _ Tx1 Ty1 Gy Px Py).
Qed.

(** [N × M]: every [-r] is at least 0. The first lane is [RU((-a) * d)],
    for the largest [(-r) * t], and the second [RU((-a) * (-c))], for the
    largest [(-r) * (-t)]. *)
Lemma mul_NM :
  forall has_fma x y, valid x -> valid y ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  Interval.classify y = Some CM ->
  exists z, Interval.mul has_fma x y = Some z /\ is_tightest (image2 Rmult x y) z.
Proof.
intros has_fma x y Hx Hy Cx Cy.
destruct (mul_N_lanes x Hx Cx) as (Px0 & Ex & Tx0 & Gx & Nx).
destruct (mul_M_lanes y Hy Cy) as (Py0 & Py1 & Ey & Ty0 & Ty1 & Ny & Py).
exists {| rep := (Bmult mode_UP (fst (rep x)) (snd (rep y)),
                  Bmult mode_UP (fst (rep x)) (fst (rep y))) |}.
split.
- (* [N0] and [N1] take the same branch: [-a] twice times [y] swapped. *)
  unfold Interval.mul.
  destruct Cx as [Cx|Cx]; rewrite (classify2_pair _ _ _ _ Cx Cy); cbv beta iota zeta;
    rewrite mul_ru_correct; reflexivity.
- apply (tightest_mul_pos x y _ _ _ _
    (fun r => mem (- r) x) (fun t => mem t y) (fun r => mem (- r) x) (fun t => mem (- t) y)
    Px0 Py1 Px0 Py0 Ex Ey (image2_mult_opp_l x y) (image2_mult_opp_lr x y)).
  + exact (tight_mult_pos_l _ _ _ _ Tx0 Ty1 Gx Nx Py).
  + exact (tight_mult_pos_l _ _ _ _ Tx0 Ty0 Gx Nx Ny).
Qed.

(** [P × M]: every [r] is at least 0. The first lane is [RU(b * (-c))],
    for the largest [r * (-t)], and the second [RU(b * d)], for the
    largest [r * t]. *)
Lemma mul_PM :
  forall has_fma x y, valid x -> valid y ->
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  Interval.classify y = Some CM ->
  exists z, Interval.mul has_fma x y = Some z /\ is_tightest (image2 Rmult x y) z.
Proof.
intros has_fma x y Hx Hy Cx Cy.
destruct (mul_P_lanes x Hx Cx) as (Px1 & Ex & Tx1 & Gx & Px).
destruct (mul_M_lanes y Hy Cy) as (Py0 & Py1 & Ey & Ty0 & Ty1 & Ny & Py).
exists {| rep := (Bmult mode_UP (snd (rep x)) (fst (rep y)),
                  Bmult mode_UP (snd (rep x)) (snd (rep y))) |}.
split.
- (* [P0] and [P1] take the same branch: [b] twice times [y]. *)
  unfold Interval.mul.
  destruct Cx as [Cx|Cx]; rewrite (classify2_pair _ _ _ _ Cx Cy); cbv beta iota zeta;
    rewrite mul_ru_correct; reflexivity.
- apply (tightest_mul_pos x y _ _ _ _
    (fun r => mem r x) (fun t => mem (- t) y) (fun r => mem r x) (fun t => mem t y)
    Px1 Py0 Px1 Py1 Ex Ey (image2_mult_opp_r x y) (fun s => iff_refl _)).
  + exact (tight_mult_pos_l _ _ _ _ Tx1 Ty0 Gx Px Ny).
  + exact (tight_mult_pos_l _ _ _ _ Tx1 Ty1 Gx Px Py).
Qed.
