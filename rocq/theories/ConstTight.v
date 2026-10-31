(** * A constant between two consecutive floats is the tightest interval around it

    Each constant [C] of [Interval] other than [EMPTY] and [ENTIRE] is
    [const_interval a b] for two finite floats [a] and [b], where [b] is
    the float after [a] (Flocq's [Bsucc]). If a real [c] lies strictly
    between them, the upper bound [b] is the least float at or above [c],
    and [-a] the least at or above [-c] ([pt_up] and [pt_dn] in
    [PiTight.v]), so [[a, b]] is the tightest interval around [c]
    ([const_tightest], by [tightest_lanes] in [AddSub.v]). [B2Q] gives the
    value of a float as a rational, so that [vm_compute] can compare the
    bounds with rational bounds of [c] ([const_tightest_Q]). *)

From Stdlib Require Import ZArith Reals Lra QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer MaxMin AddSub PiTight.

Open Scope R_scope.

(** The value of the float [x] as a rational: [m * 2^e] for a finite [x],
    and 0, as [B2R] gives, otherwise. *)
Definition B2Q (x : f64) : Q :=
  match x with
  | B754_finite s m e _ =>
      if (0 <=? e)%Z then inject_Z (cond_Zopp s (Zpos m) * 2 ^ e)
      else (cond_Zopp s (Zpos m) # Z.to_pos (2 ^ (- e)))%Q
  | _ => 0%Q
  end.

Lemma B2Q_correct : forall x : f64, B2R x = Q2R (B2Q x).
Proof.
intros [s|s| |s m e Hb]; try (unfold Q2R; simpl; lra).
unfold B2R, F2R, B2Q, Q2R. cbn [Fnum Fexp].
set (n := cond_Zopp s (Zpos m)).
destruct e as [|p|p]; cbn [Z.leb Z.compare Qnum Qden inject_Z Z.opp].
- (* [2 ^ 0 = 1] and [bpow radix2 0 = 1]. *)
  change (2 ^ 0)%Z with 1%Z. cbn [bpow]. rewrite Z.mul_1_r. lra.
- (* [bpow radix2 p] is [2 ^ p] by definition. *)
  change (bpow radix2 (Zpos p)) with (IZR (2 ^ Zpos p)).
  rewrite mult_IZR. lra.
- (* [bpow radix2 (-p)] is [/ 2 ^ p] by definition, and [Z.to_pos]
     keeps [2 ^ p], which is positive. *)
  change (bpow radix2 (Zneg p)) with (/ IZR (2 ^ Zpos p)).
  assert (Hp : (0 < 2 ^ Zpos p)%Z)
    by (apply Z.pow_pos_nonneg; [reflexivity | apply Pos2Z.is_nonneg]).
  rewrite Z2Pos.id by exact Hp. reflexivity.
Qed.

(** If [b] is the float after the finite float [a], and [c] lies strictly
    between them, then [[a, b]] is the tightest interval around [c]. *)
Lemma const_tightest :
  forall (a b : f64) (c : R),
  is_finite a = true -> is_finite b = true -> Bsucc a = b ->
  B2R a < c < B2R b ->
  is_tightest (fun r => r = c) (Interval.const_interval a b).
Proof.
intros a b c Fa Fb Hs Hc.
(* The largest element of [{c}] is [c], and of its negation [-c]. *)
apply (tightest_lanes (fun r => r = c) _ (Some (- c)) (Some c)).
- exists c. reflexivity.
- intros s. cbn [below]. split.
  + intros H. exists (- c). split; [ring | exact H].
  + intros (r & Hr & H). lra.
- intros s. cbn [below]. split.
  + intros H. exists c. split; [reflexivity | exact H].
  + intros (r & Hr & H). lra.
- (* The first lane of [const_interval a b] is [-a]. *)
  cbn [Interval.const_interval rep fst snd].
  exact (pt_dn a b c Fa Fb Hs Hc).
- cbn [Interval.const_interval rep fst snd].
  exact (pt_up a b c Fa Fb Hs Hc).
Qed.

(** The same, with [c] between two rationals [l] and [u] that
    [vm_compute] compares with the bounds. *)
Lemma const_tightest_Q :
  forall (a b : f64) (c : R) (l u : Q),
  is_finite a = true -> is_finite b = true -> Bsucc a = b ->
  (B2Q a < l)%Q -> (u < B2Q b)%Q -> Q2R l <= c <= Q2R u ->
  is_tightest (fun r => r = c) (Interval.const_interval a b).
Proof.
intros a b c l u Fa Fb Hs Hl Hu Hc.
apply (const_tightest a b c Fa Fb Hs).
rewrite !B2Q_correct.
apply Qlt_Rlt in Hl. apply Qlt_Rlt in Hu. lra.
Qed.
