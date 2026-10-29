(** * The proved operations on intervals keep them [valid]

    Each theorem that states that an operation is correct concludes
    [is_hull s y] or [is_tightest s y] of its result [y], and both include
    [valid y] (in [Ieee1788.v]). Where the operation returns an [option],
    the theorem also shows that it returns [Some]. The theorems here take
    [valid y] out of them. *)

From Inari Require Import Model Ieee1788.
From Inari Require Integer Round Trunc Sign Abs MaxMin Neg AddSub Mul Sqr Sqrt
  Recip Div.

Theorem floor_valid : forall x, valid x -> valid (Interval.floor x).
Proof.
intros x Hx. exact (proj1 (Integer.floor_correct x Hx)).
Qed.

Theorem ceil_valid : forall x, valid x -> valid (Interval.ceil x).
Proof.
intros x Hx. exact (proj1 (Integer.ceil_correct x Hx)).
Qed.

Theorem round_valid : forall x, valid x -> valid (Interval.round x).
Proof.
intros x Hx. exact (proj1 (Round.round_correct x Hx)).
Qed.

Theorem round_ties_even_valid :
  forall x, valid x -> valid (Interval.round_ties_even x).
Proof.
intros x Hx. exact (proj1 (Round.round_ties_even_correct x Hx)).
Qed.

Theorem trunc_valid : forall x, valid x -> valid (Interval.trunc x).
Proof.
intros x Hx. exact (proj1 (Trunc.trunc_correct x Hx)).
Qed.

Theorem sign_valid : forall x, valid x -> valid (Interval.sign x).
Proof.
intros x Hx. exact (proj1 (Sign.sign_correct x Hx)).
Qed.

Theorem neg_valid : forall x, valid x -> valid (Interval.neg x).
Proof.
intros x Hx. exact (proj1 (Neg.neg_correct x Hx)).
Qed.

Theorem abs_valid :
  forall x y, valid x -> Interval.abs x = Some y -> valid y.
Proof.
intros x y Hx E. destruct (Abs.abs_correct x Hx) as (y' & E' & H).
rewrite E in E'. injection E' as <-. exact (proj1 H).
Qed.

Theorem max_valid :
  forall has_maximum x y, valid x -> valid y ->
  valid (Interval.max has_maximum x y).
Proof.
intros has_maximum x y Hx Hy.
exact (proj1 (MaxMin.max_correct has_maximum x y Hx Hy)).
Qed.

Theorem min_valid :
  forall has_maximum x y, valid x -> valid y ->
  valid (Interval.min has_maximum x y).
Proof.
intros has_maximum x y Hx Hy.
exact (proj1 (MaxMin.min_correct has_maximum x y Hx Hy)).
Qed.

Theorem add_valid :
  forall x y z, valid x -> valid y -> Interval.add x y = Some z -> valid z.
Proof.
intros x y z Hx Hy E.
destruct (AddSub.add_correct x y Hx Hy) as (z' & E' & H).
rewrite E in E'. injection E' as <-. exact (proj1 H).
Qed.

Theorem sub_valid :
  forall x y z, valid x -> valid y -> Interval.sub x y = Some z -> valid z.
Proof.
intros x y z Hx Hy E.
destruct (AddSub.sub_correct x y Hx Hy) as (z' & E' & H).
rewrite E in E'. injection E' as <-. exact (proj1 H).
Qed.

Theorem mul_valid :
  forall has_fma x y z, valid x -> valid y ->
  Interval.mul has_fma x y = Some z -> valid z.
Proof.
intros has_fma x y z Hx Hy E.
destruct (Mul.mul_correct has_fma x y Hx Hy) as (z' & E' & H).
rewrite E in E'. injection E' as <-. exact (proj1 H).
Qed.

Theorem div_valid :
  forall has_fma x y z, valid x -> valid y ->
  Interval.div has_fma x y = Some z -> valid z.
Proof.
intros has_fma x y z Hx Hy E.
destruct (Div.div_correct has_fma x y Hx Hy) as (z' & E' & H).
rewrite E in E'. injection E' as <-. exact (proj1 H).
Qed.

Theorem sqr_valid :
  forall has_fma x y, valid x -> Interval.sqr has_fma x = Some y -> valid y.
Proof.
intros has_fma x y Hx E.
destruct (Sqr.sqr_correct has_fma x Hx) as (y' & E' & H).
rewrite E in E'. injection E' as <-. exact (proj1 H).
Qed.

Theorem sqrt_valid :
  forall has_fma x y, valid x -> Interval.sqrt has_fma x = Some y -> valid y.
Proof.
intros has_fma x y Hx E.
destruct (Sqrt.sqrt_correct has_fma x Hx) as (y' & E' & H).
rewrite E in E'. injection E' as <-. exact (proj1 H).
Qed.

Theorem recip_valid :
  forall has_fma x y, valid x -> Interval.recip has_fma x = Some y -> valid y.
Proof.
intros has_fma x y Hx E.
destruct (Recip.recip_correct has_fma x Hx) as (y' & E' & H).
rewrite E in E'. injection E' as <-. exact (proj1 H).
Qed.
