(** * The real cube root, and [hypot] far above its smaller argument

    [Rcbrt] of [Elementary.v] is a real whose cube is its argument
    ([Rcbrt_cube]) and the only one ([Rcbrt_unique]), so it is odd
    ([Rcbrt_opp]) and increasing ([Rcbrt_lt]). [hypot_cut] bounds
    [hypot(x, y)] above [|x|] where the exponent of [|x|] is at least 27
    above that of [|y|]: the rule of [DyadicRoot.hypot_odd] there. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core.
From Inari Require Import Elementary.

Open Scope R_scope.

(** [Rpower r (/ 3)] is a cube root of a positive [r], as the three
    exponents [/ 3] add up to 1. *)
Local Lemma Rpower_third_cube :
  forall r, 0 < r -> Rpower r (/ 3) * Rpower r (/ 3) * Rpower r (/ 3) = r.
Proof.
intros r Hr.
rewrite <- !Rpower_plus.
replace (/ 3 + / 3 + / 3) with 1 by field.
apply Rpower_1. exact Hr.
Qed.

(** Cubing is strictly increasing: [t^3 - r^3 = (t - r) (r^2 + r t + t^2)],
    and [4 (r^2 + r t + t^2) = 3 (r + t)^2 + (t - r)^2 > 0]. *)
Local Lemma cube_lt : forall r t, r < t -> r * r * r < t * t * t.
Proof.
intros r t H.
assert (H1 : 0 <= (r + t) * (r + t)) by apply Rle_0_sqr.
assert (H2 : 0 < (t - r) * (t - r)) by (apply Rmult_lt_0_compat; lra).
assert (Hq : 0 < r * r + r * t + t * t) by nra.
assert (H3 : 0 < (t - r) * (r * r + r * t + t * t)) by (apply Rmult_lt_0_compat; lra).
nra.
Qed.

Lemma Rcbrt_cube : forall r, Rcbrt r * Rcbrt r * Rcbrt r = r.
Proof.
intros r. unfold Rcbrt.
destruct (Rlt_dec 0 r) as [Hp | Hp]; [apply Rpower_third_cube; exact Hp |].
destruct (Rlt_dec r 0) as [Hn | Hn]; [| lra].
(* [(-c)^3 = -(c^3)] with [c^3 = -r]. *)
pose proof (Rpower_third_cube (- r) ltac:(lra)) as H.
lra.
Qed.

(** If [t^3 = r] and [Rcbrt r] were another real, one of them would be
    the smaller, and so would its cube ([cube_lt]); but both cubes are
    [r] ([Rcbrt_cube]). *)
Lemma Rcbrt_unique : forall r t, t * t * t = r -> Rcbrt r = t.
Proof.
intros r t Ht.
pose proof (Rcbrt_cube r) as Hc.
destruct (Rtotal_order (Rcbrt r) t) as [Hl | [He | Hg]]; [| exact He |].
- pose proof (cube_lt _ _ Hl). lra.
- pose proof (cube_lt _ _ Hg). lra.
Qed.

(** If [Rcbrt t <= Rcbrt r], their cubes [t] and [r] would be in the same
    order ([cube_lt]). *)
Lemma Rcbrt_lt : forall r t, r < t -> Rcbrt r < Rcbrt t.
Proof.
intros r t H.
pose proof (Rcbrt_cube r) as Hr. pose proof (Rcbrt_cube t) as Ht.
destruct (Rlt_or_le (Rcbrt r) (Rcbrt t)) as [Hl | Hle]; [exact Hl |].
destruct (Rle_lt_or_eq_dec _ _ Hle) as [Hl | He].
- pose proof (cube_lt _ _ Hl). lra.
- rewrite He in Ht. lra.
Qed.

(** [(- Rcbrt r)^3 = - r]. *)
Lemma Rcbrt_opp : forall r, Rcbrt (- r) = - Rcbrt r.
Proof.
intros r. apply Rcbrt_unique.
pose proof (Rcbrt_cube r) as H. lra.
Qed.

(** For [|x| = mx 2^ex] and [|y| = my 2^ey], with [mx] and [my] of 64
    bits and [ex - ey >= 27]:
    [0 < hypot(x, y) - |x| < |y|^2 / (2 |x|) < 2^(ex + 10)]. *)
Theorem hypot_cut :
  forall mx my ex ey,
  (2 ^ 63 <= mx < 2 ^ 64)%Z -> (2 ^ 63 <= my < 2 ^ 64)%Z -> (27 <= ex - ey)%Z ->
  IZR mx * bpow radix2 ex
  < sqrt (IZR mx * bpow radix2 ex * (IZR mx * bpow radix2 ex)
          + IZR my * bpow radix2 ey * (IZR my * bpow radix2 ey))
  < IZR (mx + 2 ^ 10) * bpow radix2 ex.
Proof.
intros mx my ex ey Hmx Hmy Hg.
rewrite plus_IZR.
change (IZR (2 ^ 10)) with 1024.
set (a := bpow radix2 ex). set (b := bpow radix2 ey).
set (M := IZR mx). set (N := IZR my).
assert (Ha : 0 < a) by apply bpow_gt_0.
assert (Hb : 0 < b) by apply bpow_gt_0.
(* [2^27 b <= a], as [ey + 27 <= ex]. *)
assert (Hab : 134217728 * b <= a).
{ change 134217728 with (bpow radix2 27). unfold a, b.
  rewrite <- bpow_plus. apply bpow_le. lia. }
assert (HM : 9223372036854775808 <= M).
{ apply IZR_le. change (2 ^ 63)%Z with 9223372036854775808%Z in Hmx. lia. }
assert (HN : 9223372036854775808 <= N < 18446744073709551616).
{ change (2 ^ 63)%Z with 9223372036854775808%Z in Hmy.
  change (2 ^ 64)%Z with 18446744073709551616%Z in Hmy.
  split; [apply IZR_le | apply IZR_lt]; lia. }
(* [0 < Y^2], and [Y^2 < 2^128 b^2 <= 2^74 a^2 <= 2 X 2^10 a], as
   [M >= 2^63]: so [X^2 + Y^2 < (X + 2^10 a)^2]. *)
assert (HY0 : 0 < N * b * (N * b)).
{ assert (0 < N * b) by nra. nra. }
assert (HN2 : N * N < 340282366920938463463374607431768211456) by nra.
assert (Hb2 : 134217728 * b * (134217728 * b) <= a * a) by nra.
assert (HY : N * b * (N * b) < 18889465931478580854784 * (a * a)).
{ assert (H1 : N * N * (b * b) < 340282366920938463463374607431768211456 * (b * b)).
  { apply Rmult_lt_compat_r; [nra | exact HN2]. }
  nra. }
assert (HX : 18889465931478580854784 * (a * a) <= 2 * (M * a) * (1024 * a)).
{ assert (0 <= (2048 * M - 18889465931478580854784) * (a * a)).
  { apply Rmult_le_pos; nra. }
  nra. }
assert (HS : 0 <= M * a * (M * a)) by nra.
split.
- (* [X = sqrt (X^2) < sqrt (X^2 + Y^2)] *)
  rewrite <- (sqrt_square (M * a)) at 1 by nra.
  apply sqrt_lt_1_alt. lra.
- rewrite <- (sqrt_square ((M + 1024) * a)) by nra.
  apply sqrt_lt_1_alt. split; [lra |]. nra.
Qed.
