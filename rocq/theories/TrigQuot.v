(** * The bounds of the quotient in the argument reduction of [sin], [cos] and [tan]

    [trig_reduce] in [TrigReduce.v] floors the bounds of [z = x / C], the
    tightest quotient ([div_correct] in [Div.v]) of a nonempty
    [x = [a, b]] by an interval [C = [lo, hi]] that holds [c]
    ([trig_const]). [trig_quot_lo] and [trig_quot_hi] give what that needs
    of the bounds of [z]: an infinite bound of [x] gives an infinite one,
    and a finite [a] a finite lower bound of [z] at most [a / t] for [t] =
    [c], [lo] and [hi], as [a / t] is in the image; a finite [b] a finite
    upper bound at least [b / c]. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer PiBounds Sign DecBinary ClosedDom.

Open Scope R_scope.

(** ** Helpers *)

(** [r / t] for [r] in [x] and a nonzero [t] in [C] is in the image. *)
Lemma tq_img :
  forall x C r t, mem r x -> mem t C -> t <> 0 ->
  image2_dom div_dom1 div_dom2 Rdiv x C (r / t).
Proof.
intros x C r t Hr Ht Ht0. exists r, t.
exact (conj Hr (conj Ht (conj I (conj Ht0 eq_refl)))).
Qed.

(** The reals between the bounds of [C] are in [C], and they are at
    least 1. *)
Lemma tq_C_mem :
  forall C c t, trig_const C c ->
  B2R (Interval.inf_raw C) <= t <= B2R (Interval.sup_raw C) -> mem t C.
Proof.
intros C c t (HC & EC & Fl & Fh & _) Ht.
apply (cl_mem_iff C t HC EC). rewrite (bound_finite _ Fl), (bound_finite _ Fh).
exact Ht.
Qed.

Lemma tq_C_ge1 :
  forall C c t, trig_const C c -> mem t C -> 1 <= t.
Proof.
intros C c t (HC & EC & Fl & _ & H1 & _) Ht.
pose proof (cl_mem_inf C t HC EC Fl Ht). lra.
Qed.

(** [x] with the lower bound -inf holds a real at or below any [M], and
    [x] with the upper bound +inf one at or above any [M]. *)
Lemma tq_below :
  forall x M, valid x -> Interval.is_empty x = false ->
  Interval.inf_raw x = B754_infinity true -> exists r, mem r x /\ r <= M.
Proof.
intros x M Hx E Ea.
set (t := match bound (Interval.sup_raw x) with
          | Some b => Rmin M b | None => M end).
exists t. split.
- apply (cl_mem_iff x t Hx E). rewrite Ea. split; [exact I|]. unfold t.
  destruct (bound (Interval.sup_raw x)); [apply Rmin_r | exact I].
- unfold t. destruct (bound (Interval.sup_raw x)); [apply Rmin_l | apply Rle_refl].
Qed.

Lemma tq_above :
  forall x M, valid x -> Interval.is_empty x = false ->
  Interval.sup_raw x = B754_infinity false -> exists r, mem r x /\ M <= r.
Proof.
intros x M Hx E Eb.
set (t := match bound (Interval.inf_raw x) with
          | Some a => Rmax M a | None => M end).
exists t. split.
- apply (cl_mem_iff x t Hx E). rewrite Eb. split; [|exact I]. unfold t.
  destruct (bound (Interval.inf_raw x)); [apply Rmax_r | exact I].
- unfold t. destruct (bound (Interval.inf_raw x)); [apply Rmax_l | apply Rle_refl].
Qed.

(** A nonempty tightest [z] of a set [s] whose reals are at least the
    finite [opp x0] has a finite lower bound: the valid interval
    [[opp x0, +inf]] contains [s], so it contains [z], and [cl_inf_finite]
    applies. *)
Lemma tq_inf_finite :
  forall s z x0, is_finite (opp x0) = true -> is_tightest s z ->
  Interval.is_empty z = false -> (forall r, s r -> B2R (opp x0) <= r) ->
  is_finite (Interval.inf_raw z) = true.
Proof.
intros s z x0 F (Hz & _ & Ht) E Hs.
set (z' := {| rep := (x0, B754_infinity false) |}).
assert (Lo : lower_ok (opp (fst (rep z')))) by (left; exact F).
assert (Up : upper_ok (snd (rep z'))) by (right; reflexivity).
assert (Hz' : valid z').
{ apply (valid_bounds z' Lo Up).
  change (ordered (bound (opp x0)) (bound (B754_infinity false))).
  rewrite (bound_finite _ F), bound_inf. exact I. }
assert (Hsz : forall r, s r -> mem r z').
{ intros r Hr. apply (mem_bounds z' r Lo Up).
  change (in_bounds (bound (opp x0)) (bound (B754_infinity false)) r).
  rewrite (bound_finite _ F), bound_inf. split; [exact (Hs r Hr) | exact I]. }
apply (cl_inf_finite z (B2R (opp x0)) Hz E). intros r Hr.
pose proof (Ht z' Hz' Hsz r Hr) as Hr'.
apply (mem_bounds z' r Lo Up) in Hr'.
change (in_bounds (bound (opp x0)) (bound (B754_infinity false)) r) in Hr'.
rewrite (bound_finite _ F) in Hr'. exact (proj1 Hr').
Qed.

(** The mirror: reals at most the finite [x1], with [[-inf, x1]] and
    [cl_sup_finite]. The lower bound -inf is [opp (B754_infinity false)]. *)
Lemma tq_sup_finite :
  forall s z (x1 : f64), is_finite x1 = true -> is_tightest s z ->
  Interval.is_empty z = false -> (forall r, s r -> r <= B2R x1) ->
  is_finite (Interval.sup_raw z) = true.
Proof.
intros s z x1 F (Hz & _ & Ht) E Hs.
set (z' := {| rep := (B754_infinity false, x1) |}).
assert (Lo : lower_ok (opp (fst (rep z')))) by (right; reflexivity).
assert (Up : upper_ok (snd (rep z'))) by (left; exact F).
assert (Hz' : valid z').
{ apply (valid_bounds z' Lo Up).
  change (ordered (bound (B754_infinity true)) (bound x1)).
  rewrite bound_inf. exact I. }
assert (Hsz : forall r, s r -> mem r z').
{ intros r Hr. apply (mem_bounds z' r Lo Up).
  change (in_bounds (bound (B754_infinity true)) (bound x1) r).
  rewrite (bound_finite _ F), bound_inf. split; [exact I | exact (Hs r Hr)]. }
apply (cl_sup_finite z (B2R x1) Hz E). intros r Hr.
pose proof (Ht z' Hz' Hsz r Hr) as Hr'.
apply (mem_bounds z' r Lo Up) in Hr'.
change (in_bounds (bound (B754_infinity true)) (bound x1) r) in Hr'.
rewrite (bound_finite _ F) in Hr'. exact (proj2 Hr').
Qed.

(** Dividing by [t >= 1] moves [r] toward 0, so [r / t] stays at or above
    a bound [m <= 0] of [r], and at or below a bound [m >= 0]. [nra] does
    not see through [/], so the quotient is named [q] with [q * t = r]. *)
Lemma tq_div_lb :
  forall m r t, 1 <= t -> m <= 0 -> m <= r -> m <= r / t.
Proof.
intros m r t H1 Hm Hr.
set (q := r / t). assert (Hq : q * t = r) by (unfold q; field; lra).
clearbody q. nra.
Qed.

Lemma tq_div_ub :
  forall m r t, 1 <= t -> 0 <= m -> r <= m -> r / t <= m.
Proof.
intros m r t H1 Hm Hr.
set (q := r / t). assert (Hq : q * t = r) by (unfold q; field; lra).
clearbody q. nra.
Qed.

(** [r <= M * c] gives [r / c <= M], and [M * c <= r] gives [M <= r / c],
    for [c > 0]. *)
Lemma tq_div_le :
  forall r c M, 0 < c -> r <= M * c -> r / c <= M.
Proof.
intros r c M Hc Hr.
set (q := r / c). assert (Hq : q * c = r) by (unfold q; field; lra).
clearbody q. nra.
Qed.

Lemma tq_le_div :
  forall r c M, 0 < c -> M * c <= r -> M <= r / c.
Proof.
intros r c M Hc Hr.
set (q := r / c). assert (Hq : q * c = r) by (unfold q; field; lra).
clearbody q. nra.
Qed.

(** ** The bounds of [z] *)

(** If [a = -inf], [x] holds reals [r] below [(L - 1) * c] for any [L],
    and [r / c < L] is in [z], so [z] has no finite lower bound [L]. If
    [a] is finite, every real of the image is at least [min(a, 0)] by
    [tq_div_lb], so [z] has a finite lower bound by [tq_inf_finite], with
    [m = a] or [m = 0]; it is at most [a / t] for each [t] in [C], as that
    is in the image. *)
Lemma trig_quot_lo :
  forall C c x z, trig_const C c -> valid x -> Interval.is_empty x = false ->
  is_tightest (image2_dom div_dom1 div_dom2 Rdiv x C) z ->
  (Interval.inf_raw x = B754_infinity true -> Interval.inf_raw z = B754_infinity true) /\
  (is_finite (Interval.inf_raw x) = true ->
   is_finite (Interval.inf_raw z) = true /\
   B2R (Interval.inf_raw z) <= B2R (Interval.inf_raw x) / c /\
   B2R (Interval.inf_raw z) <= B2R (Interval.inf_raw x) / B2R (Interval.inf_raw C) /\
   B2R (Interval.inf_raw z) <= B2R (Interval.inf_raw x) / B2R (Interval.sup_raw C)).
Proof.
intros C c x z HC Hx E Hz.
pose proof HC as (HCv & EC & Fl & Fh & H1 & Hlc & Hch).
pose proof Hz as (Hzv & Hin & _).
assert (Hc : mem c C) by (apply (tq_C_mem C c c HC); lra).
assert (Hc0 : 0 < c) by lra.
split.
- intros Ea.
  destruct (tq_below x 0 Hx E Ea) as (r0 & Hr0 & _).
  assert (Ez : Interval.is_empty z = false).
  { apply (mem_not_empty z (r0 / c) Hzv). apply Hin. apply tq_img; trivial; lra. }
  destruct (valid_nonempty z Hzv Ez) as ([Fz|Ez'] & _ & _); [exfalso|exact Ez'].
  change (opp (fst (rep z))) with (Interval.inf_raw z) in Fz.
  destruct (tq_below x ((B2R (Interval.inf_raw z) - 1) * c) Hx E Ea) as (r & Hr & Hrl).
  assert (Hm : mem (r / c) z) by (apply Hin; apply tq_img; trivial; lra).
  pose proof (cl_mem_inf z (r / c) Hzv Ez Fz Hm) as Hle.
  pose proof (tq_div_le r c _ Hc0 Hrl). lra.
- intros Fa.
  pose proof (cl_inf_mem x Hx E Fa) as Ha.
  assert (Hdiv : forall t, mem t C -> 0 < t -> mem (B2R (Interval.inf_raw x) / t) z).
  { intros t Ht Ht0. apply Hin. apply tq_img; trivial; lra. }
  pose proof (mem_not_empty z _ Hzv (Hdiv c Hc Hc0)) as Ez.
  assert (Fz : is_finite (Interval.inf_raw z) = true).
  { destruct (Rle_dec (B2R (Interval.inf_raw x)) 0) as [Hle|Hgt].
    - apply (tq_inf_finite _ z (fst (rep x)) Fa Hz Ez).
      intros s (r & t & Hr & Ht & _ & _ & ->).
      apply tq_div_lb;
        [exact (tq_C_ge1 C c t HC Ht) | exact Hle | exact (cl_mem_inf x r Hx E Fa Hr)].
    - apply (tq_inf_finite _ z (B754_zero true) eq_refl Hz Ez).
      intros s (r & t & Hr & Ht & _ & _ & ->).
      change (B2R (opp (B754_zero true))) with 0.
      pose proof (cl_mem_inf x r Hx E Fa Hr).
      apply tq_div_lb; [exact (tq_C_ge1 C c t HC Ht) | apply Rle_refl | lra]. }
  assert (Hl : mem (B2R (Interval.inf_raw C)) C) by (apply (tq_C_mem C c _ HC); lra).
  assert (Hh : mem (B2R (Interval.sup_raw C)) C) by (apply (tq_C_mem C c _ HC); lra).
  split; [exact Fz|].
  split; [|split]; apply (cl_mem_inf z _ Hzv Ez Fz); apply Hdiv; trivial; lra.
Qed.

(** The mirror of [trig_quot_lo] for the upper bound, with [r / c] above
    [U + 1] if [b = +inf], and [max(b, 0)] and [tq_sup_finite] if [b] is
    finite. *)
Lemma trig_quot_hi :
  forall C c x z, trig_const C c -> valid x -> Interval.is_empty x = false ->
  is_tightest (image2_dom div_dom1 div_dom2 Rdiv x C) z ->
  (Interval.sup_raw x = B754_infinity false -> Interval.sup_raw z = B754_infinity false) /\
  (is_finite (Interval.sup_raw x) = true ->
   is_finite (Interval.sup_raw z) = true /\
   B2R (Interval.sup_raw x) / c <= B2R (Interval.sup_raw z)).
Proof.
intros C c x z HC Hx E Hz.
pose proof HC as (HCv & EC & Fl & Fh & H1 & Hlc & Hch).
pose proof Hz as (Hzv & Hin & _).
assert (Hc : mem c C) by (apply (tq_C_mem C c c HC); lra).
assert (Hc0 : 0 < c) by lra.
split.
- intros Eb.
  destruct (tq_above x 0 Hx E Eb) as (r0 & Hr0 & _).
  assert (Ez : Interval.is_empty z = false).
  { apply (mem_not_empty z (r0 / c) Hzv). apply Hin. apply tq_img; trivial; lra. }
  destruct (valid_nonempty z Hzv Ez) as (_ & [Fz|Ez'] & _); [exfalso|exact Ez'].
  change (snd (rep z)) with (Interval.sup_raw z) in Fz.
  destruct (tq_above x ((B2R (Interval.sup_raw z) + 1) * c) Hx E Eb) as (r & Hr & Hrl).
  assert (Hm : mem (r / c) z) by (apply Hin; apply tq_img; trivial; lra).
  pose proof (cl_mem_sup z (r / c) Hzv Ez Fz Hm) as Hle.
  pose proof (tq_le_div r c _ Hc0 Hrl). lra.
- intros Fb.
  pose proof (cl_sup_mem x Hx E Fb) as Hb.
  assert (Hm : mem (B2R (Interval.sup_raw x) / c) z)
    by (apply Hin; apply tq_img; trivial; lra).
  pose proof (mem_not_empty z _ Hzv Hm) as Ez.
  assert (Fz : is_finite (Interval.sup_raw z) = true).
  { destruct (Rle_dec 0 (B2R (Interval.sup_raw x))) as [Hle|Hgt].
    - apply (tq_sup_finite _ z (Interval.sup_raw x) Fb Hz Ez).
      intros s (r & t & Hr & Ht & _ & _ & ->).
      apply tq_div_ub;
        [exact (tq_C_ge1 C c t HC Ht) | exact Hle | exact (cl_mem_sup x r Hx E Fb Hr)].
    - apply (tq_sup_finite _ z (B754_zero false) eq_refl Hz Ez).
      intros s (r & t & Hr & Ht & _ & _ & ->).
      change (B2R (B754_zero false)) with 0.
      pose proof (cl_mem_sup x r Hx E Fb Hr).
      apply tq_div_ub; [exact (tq_C_ge1 C c t HC Ht) | apply Rle_refl | lra]. }
  split; [exact Fz|].
  exact (cl_mem_sup z _ Hzv Ez Fz Hm).
Qed.
