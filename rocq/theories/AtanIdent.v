(** * Identities of atan, asin, acos and atan2 for the dyadic kernel

    The reductions of [atan_encl], [asin_parts] and [ev_atan2] of
    [DyadicAtan] in [Model.v]: [atan w] from [atan] of an argument of
    absolute value at most [tan(π/8)], through [π/4] and [π/2]; [asin t]
    and [acos t] as [atan] of a quotient with [√((1 - t)(1 + t))]; and
    the sign of [y] in [atan2(y, x)]. *)

From Stdlib Require Import Reals Lra.
(* [Machin.v] has the subtraction formula [atan_sub_correct]. *)
From Stdlib Require Import Machin.
From Inari Require Import Elementary AtanReal.

Open Scope R_scope.

(** [atan w = atan 1 + atan ((w - 1) / (1 + w))] by Stdlib's subtraction
    formula, whose side conditions hold as [-π/4 < atan w < π/2] for
    [w > -1]. *)
Lemma atan_quarter_plus : forall w, -1 < w -> atan w = PI / 4 + atan ((w - 1) / (w + 1)).
Proof.
intros w Hw.
assert (Hlo : atan (Ropp 1) < atan w) by (apply atan_increasing; lra).
rewrite atan_opp, atan_1 in Hlo.
pose proof (atan_bound w) as Hw'.
pose proof PI_RGT_0 as Hpi.
rewrite (atan_sub_correct w 1).
- rewrite atan_1. unfold atan_sub.
  replace (1 + w * 1) with (w + 1) by ring. reflexivity.
- lra.
- rewrite atan_1. lra.
- apply atan_bound.
Qed.

Lemma atan_quarter_minus : forall w, -1 < w -> atan w = PI / 4 - atan ((1 - w) / (1 + w)).
Proof.
intros w Hw. rewrite (atan_quarter_plus w Hw).
(* [(w - 1) / (w + 1) = - ((1 - w) / (1 + w))], and [atan] is odd. *)
replace ((w - 1) / (w + 1)) with (- ((1 - w) / (1 + w))).
- rewrite atan_opp. ring.
- unfold Rdiv. rewrite (Rplus_comm w 1). ring.
Qed.

Lemma atan_half_inv : forall w, 0 < w -> atan w = PI / 2 - atan (1 / w).
Proof.
intros w Hw. unfold Rdiv at 2. rewrite Rmult_1_l, (atan_inv w Hw). ring.
Qed.

(** Stdlib's [asin_atan] and [acos_atan], with [1 - t²] written as the
    product [(1 - t)(1 + t)] that the kernel computes. *)
Lemma asin_as_atan : forall t, 0 <= t < 1 -> asin t = atan (t / sqrt ((1 - t) * (1 + t))).
Proof.
intros t Ht. rewrite asin_atan by lra.
replace ((1 - t) * (1 + t)) with (1 - t²) by (unfold Rsqr; ring). reflexivity.
Qed.

Lemma acos_as_atan : forall t, 0 < t <= 1 -> acos t = atan (sqrt ((1 - t) * (1 + t)) / t).
Proof.
intros t Ht. rewrite acos_atan by lra.
replace ((1 - t) * (1 + t)) with (1 - t²) by (unfold Rsqr; ring). reflexivity.
Qed.

Lemma asin_plus_acos : forall t, -1 <= t <= 1 -> asin t + acos t = PI / 2.
Proof. intros t Ht. rewrite (asin_acos t Ht). ring. Qed.

(** By the cases of [Ratan2]: on [x > 0] it is [atan (y / x)], which is
    odd in [y]; on [x < 0] the sign of [y] picks [+ π] or [- π], and it
    flips with [y]; on [x = 0] it is [± π/2] by the sign of [y]. *)
Lemma Ratan2_opp_y : forall y x, y <> 0 -> Ratan2 (- y) x = - Ratan2 y x.
Proof.
intros y x Hy.
assert (Hq : - y / x = - (y / x)) by (unfold Rdiv; ring).
destruct (Rtotal_order 0 x) as [Hx|[Hx|Hx]].
- rewrite !Ratan2_pos_x by exact Hx. rewrite Hq. apply atan_opp.
- subst x. destruct (Rtotal_order 0 y) as [H|[H|H]].
  + rewrite (Ratan2_zero_x_pos y) by exact H. rewrite (Ratan2_zero_x_neg (- y)) by lra.
    reflexivity.
  + lra.
  + rewrite (Ratan2_zero_x_neg y) by exact H. rewrite (Ratan2_zero_x_pos (- y)) by lra. ring.
- destruct (Rtotal_order 0 y) as [H|[H|H]].
  + rewrite (Ratan2_neg_x_lt (- y)) by lra. rewrite (Ratan2_neg_x_ge y) by lra.
    rewrite Hq, atan_opp. ring.
  + lra.
  + rewrite (Ratan2_neg_x_ge (- y)) by lra. rewrite (Ratan2_neg_x_lt y) by lra.
    rewrite Hq, atan_opp. ring.
Qed.
