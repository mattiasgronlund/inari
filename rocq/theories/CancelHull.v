(** * The lanes that [sub_ru] gives are the tightest interval

    For common [x = [-a; b]] and [y = [-c; d]] with [a - c <= b - d],
    [[RU(-a - (-c)); RU(b - d)]] = [[RU(c - a); RU(b - d)]], i.e.
    [[RD(a - c), RU(b - d)]], is the tightest interval that contains
    [[a - c, b - d]]: [Bminus mode_UP u v] is [Bplus mode_UP u (-v)]
    ([Bminus_Bplus_Bopp]), which [add_lane] shows to be the least float or
    +inf at or above [u - v], and [tightest_lanes] does the rest. The first
    lane is never -inf, as [Bplus mode_UP] of finite floats gives
    [-f64::MAX] on a negative overflow, so the lower bound is never +inf. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Ieee1788 Integer Sign MaxMin AddSub
  SubRu CancelLanes.

Open Scope R_scope.

Theorem sub_lanes_tightest :
  forall x y, valid x -> valid y ->
  Interval.is_common_interval x = true -> Interval.is_common_interval y = true ->
  B2R (snd (rep y)) + B2R (fst (rep y)) <= B2R (snd (rep x)) + B2R (fst (rep x)) ->
  is_tightest
    (fun r => - B2R (fst (rep x)) - - B2R (fst (rep y)) <= r <=
              B2R (snd (rep x)) - B2R (snd (rep y)))
    {| rep := (Bminus mode_UP (fst (rep x)) (fst (rep y)),
               Bminus mode_UP (snd (rep x)) (snd (rep y))) |}.
Proof.
intros x y Hx Hy Cx Cy Hw.
destruct (common_lanes x Hx Cx) as (Fx0 & Fx1 & _ & _).
destruct (common_lanes y Hy Cy) as (Fy0 & Fy1 & _ & _).
(* [Bminus mode_UP u v] is [Bplus mode_UP u (-v)], whose lane [add_lane]
   gives, and the bound of [-v] is [-] that of [v]. *)
rewrite !Bminus_Bplus_Bopp.
assert (Fo0 : is_finite (Bopp (fst (rep y))) = true) by now rewrite is_finite_Bopp.
assert (Fo1 : is_finite (Bopp (snd (rep y))) = true) by now rewrite is_finite_Bopp.
assert (Up : forall u v : f64, is_finite u = true -> is_finite (Bopp v) = true ->
             uplus (bound u) (bound (Bopp v)) = Some (B2R u - B2R v)).
{ intros u v Fu Fv. rewrite (bound_finite _ Fu), (bound_finite _ Fv), B2R_Bopp.
  cbn [uplus]. f_equal; ring. }
apply (tightest_lanes _ _
  (Some (B2R (fst (rep x)) - B2R (fst (rep y))))
  (Some (B2R (snd (rep x)) - B2R (snd (rep y))))).
- (* [b - d] is in the set, as [a - c <= b - d]. *)
  exists (B2R (snd (rep x)) - B2R (snd (rep y))). lra.
- (* The largest [-r] for [r] in the set is [c - a]. *)
  intros s. cbn [below]. split.
  + intros Hs. exists (B2R (fst (rep x)) - B2R (fst (rep y))). lra.
  + intros (r & Hr & Hs). lra.
- intros s. cbn [below]. split.
  + intros Hs. exists (B2R (snd (rep x)) - B2R (snd (rep y))). lra.
  + intros (r & Hr & Hs). lra.
- cbn [rep fst]. rewrite <- (Up _ _ Fx0 Fo0).
  apply add_lane; left; assumption.
- cbn [rep snd]. rewrite <- (Up _ _ Fx1 Fo1).
  apply add_lane; left; assumption.
Qed.
