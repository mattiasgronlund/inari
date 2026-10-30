(** * [cancel_minus] of common intervals compares their widths exactly

    For common [x = [a, b]] and [y = [c, d]], [Interval.cancel_minus x y]
    returns the lanes [[RU(c - a); RU(b - d)]] that [sub_ru] computes if
    [d - c <= b - a], and [Interval::ENTIRE] otherwise. The widths are
    rounded to nearest ([width_lane]). If both overflow, every bound is at
    least [2^970] in magnitude, so the bounds are halved exactly ([halve]),
    and the halved widths, which are at most [f64::MAX], are compared
    instead: halving keeps the order of the widths. If the rounded widths
    differ, rounding is monotone, so they are in the order of the exact
    ones; a width that overflows rounds, without a largest exponent, to at
    least [2^1024], above every finite float ([add_inf_ge]). If they are
    equal, Fast2Sum on the larger and the smaller addend of each width
    ([max_min_lanes], [fast_two_sum]) gives the exact errors
    [dwx = (b - a) - w] and [dwy = (d - c) - w] of the same [w], so
    [dwx >= dwy] is [d - c <= b - a]. [partial_cmp] of the rounded widths
    is never [None], as they are finite or +inf. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Ieee1788 Integer MaxMin AddRu SubRu
  TwoSum AddSub CancelLanes.

Open Scope R_scope.

(** What [cancel_minus] does after the widths [w_rn = hadd_rn x y] of the
    lanes [x] and [y] (the halved ones, if both widths overflowed), with
    [z] from [sub_ru]: compare [wx] with [wy], and if they are equal, the
    Fast2Sum errors [dwx] and [dwy]. *)
Definition cancel_tail (x y z : Generic.F64X2) : option Interval :=
  let '(wx, wy) := Generic.extract (Generic.hadd_rn x y) in
  match partial_cmp wx wy with
  | Some Eq =>
      let '(dwx, dwy) :=
        Generic.extract
          (Generic.add_rn
             (Generic.min (Generic.shuffle02 x y) (Generic.shuffle13 x y))
             (Generic.sub_rn
                (Generic.max (Generic.shuffle02 x y) (Generic.shuffle13 x y))
                (Generic.hadd_rn x y))) in
      if ge dwx dwy then Some {| rep := z |} else Some Interval.ENTIRE
  | Some Lt => Some Interval.ENTIRE
  | Some Gt => Some {| rep := z |}
  | None => None
  end.

(** For nonempty common intervals, [cancel_minus] is [cancel_tail] of the
    halved lanes if both widths round to +inf, and of the lanes otherwise. *)
Lemma cancel_minus_unfold :
  forall x0 x1 y0 y1 : f64,
  Interval.is_empty {| rep := (x0, x1) |} = false ->
  Interval.is_common_interval {| rep := (x0, x1) |} = true ->
  Interval.is_empty {| rep := (y0, y1) |} = false ->
  Interval.is_common_interval {| rep := (y0, y1) |} = true ->
  Interval.cancel_minus {| rep := (x0, x1) |} {| rep := (y0, y1) |} =
    let z := (Bminus mode_UP x0 y0, Bminus mode_UP x1 y1) in
    if eq (add x0 x1) infinity && eq (add y0 y1) infinity
    then cancel_tail (mul half x0, mul half x1) (mul half y0, mul half y1) z
    else cancel_tail (x0, x1) (y0, y1) z.
Proof.
intros x0 x1 y0 y1 E1 C1 E2 C2.
unfold Interval.cancel_minus. rewrite E1, C1, E2, C2, sub_ru_correct.
cbn [andb orb negb rep fst snd Generic.extract Generic.hadd_rn
  Generic.constant].
destruct (eq (add x0 x1) infinity && eq (add y0 y1) infinity); reflexivity.
Qed.

(** A finite float is not NaN, is not +inf, and compares below +inf. *)
Lemma is_nan_finite : forall u : f64, is_finite u = true -> is_nan u = false.
Proof.
now intros [s|s| |s m e H].
Qed.

Lemma eq_inf_finite :
  forall u : f64, is_finite u = true -> eq u infinity = false.
Proof.
intros [s|s| |s m e H] F; try discriminate F; rewrite infinity_eq;
  reflexivity.
Qed.

Lemma partial_cmp_inf_l :
  forall u : f64, is_finite u = true ->
  partial_cmp (B754_infinity false) u = Some Gt.
Proof.
intros [s|s| |s m e H] F; try discriminate F; reflexivity.
Qed.

Lemma partial_cmp_inf_r :
  forall u : f64, is_finite u = true ->
  partial_cmp u (B754_infinity false) = Some Lt.
Proof.
intros [s|s| |s m e H] F; try discriminate F; reflexivity.
Qed.

(** Every float is at most [f64::MAX = 2^1024 - 2^971]. *)
Lemma le_f64_max :
  forall u : f64, B2R u <= bpow radix2 1024 - bpow radix2 971.
Proof.
intros u. pose proof (neg_max_le (Bopp u)) as H. rewrite B2R_Bopp in H.
lra.
Qed.

(** A sum [u + v >= 0] that overflows to +inf rounds (without a largest
    exponent) to at least [2^1024]: [Bplus] is finite whenever the rounded
    sum is below [2^1024] in magnitude. *)
Lemma add_inf_ge :
  forall u v : f64, is_finite u = true -> is_finite v = true ->
  0 <= B2R u + B2R v -> is_finite (add u v) = false ->
  bpow radix2 1024 <= RN (B2R u + B2R v).
Proof.
intros u v Fu Fv H0 Hf.
generalize (@Bplus_correct 53 1024 _ _ mode_NE u v Fu Fv).
case Rlt_bool_spec; intros Hlt H.
- destruct H as (_ & HF & _). unfold add in Hf. congruence.
- assert (P : 0 <= RN (B2R u + B2R v)).
  { apply round_ge_generic;
      [typeclasses eauto .. | apply generic_format_0 | exact H0]. }
  rewrite Rabs_pos_eq in Hlt by exact P. exact Hlt.
Qed.

(** [cancel_tail] of finite lanes with widths [x0 + x1 >= 0] and
    [y0 + y1 >= 0], not both of which round to +inf, returns [z] exactly
    when [y1 + y0 <= x1 + x0]. *)
Lemma cancel_tail_correct :
  forall (x0 x1 y0 y1 : f64) (z : Generic.F64X2),
  is_finite x0 = true -> is_finite x1 = true ->
  is_finite y0 = true -> is_finite y1 = true ->
  0 <= B2R x0 + B2R x1 -> 0 <= B2R y0 + B2R y1 ->
  is_finite (add x0 x1) = true \/ is_finite (add y0 y1) = true ->
  cancel_tail (x0, x1) (y0, y1) z =
    Some (if Rle_dec (B2R y1 + B2R y0) (B2R x1 + B2R x0)
          then {| rep := z |} else Interval.ENTIRE).
Proof.
intros x0 x1 y0 y1 z Fx0 Fx1 Fy0 Fy1 Hx Hy Hxy.
unfold cancel_tail.
cbn [Generic.extract Generic.hadd_rn Generic.add_rn Generic.sub_rn
  Generic.max Generic.min Generic.shuffle02 Generic.shuffle13 fst snd].
destruct (width_lane x0 x1 Fx0 Fx1 Hx) as [[Fwx Wx] | [Ix _]];
  destruct (width_lane y0 y1 Fy0 Fy1 Hy) as [[Fwy Wy] | [Iy _]].
- (* Both rounded widths are finite. Rounding is monotone, so unequal
     rounded widths are in the order of the exact ones. *)
  rewrite partial_cmp_finite by assumption.
  destruct (Rcompare_spec (B2R (add x0 x1)) (B2R (add y0 y1)))
    as [Hlt|Heq|Hgt].
  + destruct (Rle_dec _ _) as [H|H]; [exfalso|reflexivity].
    assert (R : RN (B2R y0 + B2R y1) <= RN (B2R x0 + B2R x1))
      by (apply round_le; [typeclasses eauto .. | lra]).
    lra.
  + (* Equal rounded widths [w]: Fast2Sum on the larger and the smaller
       lane of each width gives its exact error [width - w], and the
       errors compare as the widths. *)
    destruct (max_min_lanes x0 x1 Fx0 Fx1 Hx) as (Fhx & Flx & Ax & Sx).
    destruct (max_min_lanes y0 y1 Fy0 Fy1 Hy) as (Fhy & Fly & Ay & Sy).
    assert (Wx' : B2R (add x0 x1) =
                  RN (B2R (Generic.max1 x0 x1) + B2R (Generic.min1 x0 x1)))
      by (rewrite Sx; exact Wx).
    assert (Wy' : B2R (add y0 y1) =
                  RN (B2R (Generic.max1 y0 y1) + B2R (Generic.min1 y0 y1)))
      by (rewrite Sy; exact Wy).
    destruct (fast_two_sum _ _ _ Fhx Flx Ax Fwx Wx') as (Fdx & Dx).
    destruct (fast_two_sum _ _ _ Fhy Fly Ay Fwy Wy') as (Fdy & Dy).
    unfold ge. rewrite Bleb_correct by assumption. rewrite Dx, Dy.
    destruct (Rle_bool_spec
                (B2R (Generic.max1 y0 y1) + B2R (Generic.min1 y0 y1) -
                 B2R (add y0 y1))
                (B2R (Generic.max1 x0 x1) + B2R (Generic.min1 x0 x1) -
                 B2R (add x0 x1))) as [H|H];
      destruct (Rle_dec _ _) as [H'|H']; try reflexivity; exfalso; lra.
  + destruct (Rle_dec _ _) as [H|H]; [reflexivity|exfalso].
    assert (R : RN (B2R x0 + B2R x1) <= RN (B2R y0 + B2R y1))
      by (apply round_le; [typeclasses eauto .. | lra]).
    lra.
- (* Only the width of [y] overflows: it rounds to at least [2^1024], and
     the finite rounded width of [x] is below that, so [x] is narrower. *)
  rewrite Iy, partial_cmp_inf_r by exact Fwx.
  destruct (Rle_dec _ _) as [H|H]; [exfalso|reflexivity].
  assert (R : RN (B2R y0 + B2R y1) <= RN (B2R x0 + B2R x1))
    by (apply round_le; [typeclasses eauto .. | lra]).
  assert (G : bpow radix2 1024 <= RN (B2R y0 + B2R y1))
    by (apply add_inf_ge; [assumption .. | rewrite Iy; reflexivity]).
  pose proof (abs_B2R_lt_emax _ _ (add x0 x1)) as A.
  apply Rabs_lt_inv in A. lra.
- (* Only the width of [x] overflows, so [y] is narrower. *)
  rewrite Ix, partial_cmp_inf_l by exact Fwy.
  destruct (Rle_dec _ _) as [H|H]; [reflexivity|exfalso].
  assert (R : RN (B2R x0 + B2R x1) <= RN (B2R y0 + B2R y1))
    by (apply round_le; [typeclasses eauto .. | lra]).
  assert (G : bpow radix2 1024 <= RN (B2R x0 + B2R x1))
    by (apply add_inf_ge; [assumption .. | rewrite Ix; reflexivity]).
  pose proof (abs_B2R_lt_emax _ _ (add y0 y1)) as A.
  apply Rabs_lt_inv in A. lra.
- rewrite Ix, Iy in Hxy. destruct Hxy as [H|H]; discriminate H.
Qed.

Theorem cancel_common_eq :
  forall x y, valid x -> valid y ->
  Interval.is_common_interval x = true -> Interval.is_common_interval y = true ->
  Interval.cancel_minus x y =
    Some (if Rle_dec (B2R (snd (rep y)) + B2R (fst (rep y)))
                     (B2R (snd (rep x)) + B2R (fst (rep x)))
          then {| rep := (Bminus mode_UP (fst (rep x)) (fst (rep y)),
                          Bminus mode_UP (snd (rep x)) (snd (rep y))) |}
          else Interval.ENTIRE).
Proof.
intros x y Vx Vy Cx Cy.
destruct (common_lanes x Vx Cx) as (Fx0 & Fx1 & Hx & _).
destruct (common_lanes y Vy Cy) as (Fy0 & Fy1 & Hy & _).
destruct x as [[x0 x1]], y as [[y0 y1]].
cbn [rep fst snd] in Fx0, Fx1, Fy0, Fy1, Hx, Hy |- *.
assert (Hx' : 0 <= B2R x0 + B2R x1) by lra.
assert (Hy' : 0 <= B2R y0 + B2R y1) by lra.
rewrite cancel_minus_unfold by
  (try exact Cx; try exact Cy; apply is_nan_finite; assumption).
cbv zeta.
destruct (width_lane x0 x1 Fx0 Fx1 Hx') as [[Fwx _] | [Ix Tx]];
  [rewrite (eq_inf_finite _ Fwx); apply cancel_tail_correct; auto|].
destruct (width_lane y0 y1 Fy0 Fy1 Hy') as [[Fwy _] | [Iy Ty]];
  [rewrite (eq_inf_finite _ Fwy), Bool.andb_false_r;
   apply cancel_tail_correct; auto|].
(* Both widths overflow: [b - a >= 2^1024 - 2^970] and [b <= f64::MAX =
   2^1024 - 2^971] give [-a >= 2^970], and the same for the other three
   bounds, so halving them is exact ([halve]). The halved widths are at
   most [f64::MAX], below [2^1024 - 2^970], so they do not overflow. *)
assert (E : eq (B754_infinity false) (B754_infinity false) = true)
  by reflexivity.
rewrite Ix, Iy, infinity_eq, E. cbn [andb].
assert (P : bpow radix2 971 = 2 * bpow radix2 970 /\ 0 < bpow radix2 970).
{ split; [|apply bpow_gt_0].
  change 2 with (bpow radix2 1). rewrite <- bpow_plus. reflexivity. }
pose proof (le_f64_max x0) as Mx0. pose proof (le_f64_max x1) as Mx1.
pose proof (le_f64_max y0) as My0. pose proof (le_f64_max y1) as My1.
assert (A0 : bpow radix2 970 <= Rabs (B2R x0)) by (rewrite Rabs_pos_eq; lra).
assert (A1 : bpow radix2 970 <= Rabs (B2R x1)) by (rewrite Rabs_pos_eq; lra).
assert (B0 : bpow radix2 970 <= Rabs (B2R y0)) by (rewrite Rabs_pos_eq; lra).
assert (B1 : bpow radix2 970 <= Rabs (B2R y1)) by (rewrite Rabs_pos_eq; lra).
destruct (halve x0 Fx0 A0) as (Gx0 & Hx0).
destruct (halve x1 Fx1 A1) as (Gx1 & Hx1).
destruct (halve y0 Fy0 B0) as (Gy0 & Hy0).
destruct (halve y1 Fy1 B1) as (Gy1 & Hy1).
assert (Hhx : 0 <= B2R (mul half x0) + B2R (mul half x1))
  by (rewrite Hx0, Hx1; lra).
assert (Hhy : 0 <= B2R (mul half y0) + B2R (mul half y1))
  by (rewrite Hy0, Hy1; lra).
assert (Wx : is_finite (add (mul half x0) (mul half x1)) = true).
{ destruct (width_lane _ _ Gx0 Gx1 Hhx) as [[F _] | [_ T]]; [exact F|].
  rewrite Hx0, Hx1 in T. lra. }
rewrite cancel_tail_correct by auto.
rewrite Hx0, Hx1, Hy0, Hy1.
(* Halving both widths keeps their order. *)
destruct (Rle_dec _ _) as [H1|H1]; destruct (Rle_dec _ _) as [H2|H2];
  try reflexivity; exfalso; lra.
Qed.
