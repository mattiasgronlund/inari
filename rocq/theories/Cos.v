(** * [cos] of intervals is the tightest

    [Interval::cos] of [x = [a, b]] computes [q = floor(x / PI)] with
    bounds [qa] and [qb] ([trig_reduce] in [TrigReduce.v]), and
    [n = qb - qa] (0 if [a == b]) and the parity of [qa]. On
    [[k * PI, (k + 1) * PI]], [cos] decreases for even [k] and increases
    for odd [k] ([TrigPieces.v]). Every real of [x] lies in
    [[qa * PI, (qb + 1) * PI)], so: for [n = 0] [x] is in one piece and
    the result is that of a monotone function; for [n = 1] it spans two
    pieces with the minimum -1 (even [qa]) or the maximum 1 (odd [qa])
    between them; otherwise the result is [[-1, 1]].

    The result is the tightest for every [x] ([cos_correct]). If [x]
    holds one real, [n] is 0. If [b - a >= 8] (rounded to nearest) or [x]
    is unbounded, [x] holds two reals [2 * PI] apart ([trig_wide] in
    [TrigCert.v]), so a maximum and a minimum, and [n >= 2]. Otherwise
    the branches see the floors [ka] and [kb] of [a / PI] and [b / PI],
    which make every branch attain its bounds ([cs_exact]): [qa] and [qb]
    are those floors if [n = 0], or if [floors_exact] says so
    ([floors_exact_ok] in [TrigCert.v]); if not, [Interval::cos] takes
    the parity of [ka] and the tests of [kb - ka] from the quadrants of
    [a] and [b] ([quadrants_correct] in [TrigCount.v]), as
    [floor(r / PI) = floor(floor(r / (PI / 2)) / 2)].

    [DecInterval::cos] keeps the decoration of [x]: [cos] is defined and
    continuous everywhere, and the result is always bounded. So it is the
    strongest decoration ([dec_cos_correct]) if [x] is [com] only when it
    is bounded ([com_common]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr ComCommon Integer
  PiBounds TrigPieces TrigReduce TrigBranch TrigQuad TrigCount TrigCert
  AddSub DecBinary MonoInc Sqrt ElemDec.

Open Scope R_scope.

(** ** Helpers *)

(** The tests of [n] and [q] that the branches make, at the constants
    they meet. *)
Lemma cs_eq_zero : Model.eq Model.zero Model.zero = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cs_eq_one : Model.eq (of_u64 1) Model.zero = false.
Proof. vm_compute. reflexivity. Qed.

Lemma cs_inf_eq : Model.eq (B754_infinity false) Model.zero = false.
Proof. vm_compute. reflexivity. Qed.

Lemma cs_inf_le : Model.le (B754_infinity false) (of_u64 1) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma cs_tight_encl : forall s y, is_tightest s y -> encloses s y.
Proof.
intros s y (Hy & Hs & _). split; assumption.
Qed.

Lemma cs_even_succ : forall k, Z.even (k + 1) = negb (Z.even k).
Proof.
intros k. rewrite Z.add_1_r, Z.even_succ, <- Z.negb_even. reflexivity.
Qed.

(** [cos] at the multiple of π after [k * PI]. *)
Lemma cs_cos_succ : forall k, cos ((IZR k + 1) * PI) = if Z.even k then -1 else 1.
Proof.
intros k. rewrite <- plus_IZR, cos_kPI, cs_even_succ. destruct (Z.even k); reflexivity.
Qed.

(** Intervals are convex. *)
Lemma cs_mem_between :
  forall x r t u, valid x -> mem r x -> mem t x -> r <= u <= t -> mem u x.
Proof.
intros x r t u Hx Hr Ht Hu.
destruct (Interval.is_empty x) eqn:Hn; [destruct (mem_empty x r Hx Hn Hr)|].
destruct (valid_nonempty x Hx Hn) as (Ha & Hb & _).
apply (proj2 (mem_bounds x u Ha Hb)).
apply (in_bounds_between _ _ r t u); [| |exact Hu].
- exact (proj1 (mem_bounds x r Ha Hb) Hr).
- exact (proj1 (mem_bounds x t Ha Hb) Ht).
Qed.

(** An unbounded nonempty [x] holds two reals [2 * PI] apart. *)
Lemma cs_unbounded :
  forall x, valid x -> Interval.is_empty x = false ->
  Interval.inf_raw x = B754_infinity true \/ Interval.sup_raw x = B754_infinity false ->
  exists r t, mem r x /\ mem t x /\ 2 * PI <= t - r.
Proof.
intros x Hx Hn Hinf. pose proof PI_RGT_0 as HPI.
destruct (nonempty_mem x Hx Hn) as (r0 & Hr0).
destruct Hinf as [Ea|Eb].
- exists (r0 - 2 * PI), r0. split; [|split; [exact Hr0 | lra]].
  apply (mono_mem_dn x r0); [exact Hr0 | exact Ea | lra].
- exists r0, (r0 + 2 * PI). split; [exact Hr0|]. split; [|lra].
  apply (mono_mem_up x r0); [exact Hr0 | exact Eb | lra].
Qed.

(** [n] is +inf when [qa] or [qb] is infinite. *)
Lemma cs_n_inf :
  forall qa qb, (qa = B754_infinity true \/ is_finite qa = true) ->
  (qb = B754_infinity false \/ is_finite qb = true) ->
  qa = B754_infinity true \/ qb = B754_infinity false ->
  Model.sub qb qa = B754_infinity false.
Proof.
intros qa qb Ha Hb Hinf. apply n_inf; [| | | |exact Hinf].
- destruct Ha as [->|F]; [reflexivity|]. destruct qa; try discriminate F; reflexivity.
- destruct Hb as [->|F]; [reflexivity|]. destruct qb; try discriminate F; reflexivity.
- destruct Ha as [->|F]; intros E; [discriminate E | rewrite E in F; discriminate F].
- destruct Hb as [->|F]; intros E; [discriminate E | rewrite E in F; discriminate F].
Qed.

(** [b - a] is +inf when [a] or [b] is infinite, so the width test of
    [Interval::cos] holds. *)
Lemma cs_sub_inf :
  forall a b, (a = B754_infinity true \/ is_finite a = true) ->
  (b = B754_infinity false \/ is_finite b = true) ->
  a = B754_infinity true \/ b = B754_infinity false ->
  Model.sub b a = B754_infinity false.
Proof.
intros a b Ha Hb Hinf.
destruct Ha as [->|Fa]; destruct Hb as [->|Fb].
- reflexivity.
- destruct b; try discriminate Fb; reflexivity.
- destruct a; try discriminate Fa; reflexivity.
- destruct Hinf as [->| ->]; [discriminate Fa | discriminate Fb].
Qed.

Lemma cs_le8_inf : Model.le (of_u64 8) (B754_infinity false) = true.
Proof. vm_compute. reflexivity. Qed.

(** Two counts that are equal, or both at least 2, pass the same tests. *)
Lemma cs_tests_eq :
  forall u v, (u = v \/ (2 <= u /\ 2 <= v))%Z ->
  (u =? 0)%Z = (v =? 0)%Z /\ (u <=? 1)%Z = (v <=? 1)%Z.
Proof.
intros u v [->|[Hu Hv]]; [split; reflexivity|].
split; [destruct (Z.eqb_spec u 0), (Z.eqb_spec v 0) | destruct (Z.leb_spec u 1), (Z.leb_spec v 1)];
  try lia; reflexivity.
Qed.

(** The [n] that [Interval::cos] computes from the quadrants [j] of [a]
    and [jb] of [b]: [floor((j % 2 + d) / 2)] for the count [d] of
    [quadrants] ([count_f]). *)
Definition cs_kd (j jb : Z) (big : bool) : Z :=
  (j mod 2 + ((jb - j) mod 4 + if big then 4 else 0)) / 2.

(** [q] and the tests of [n] that [Interval::cos] computes from the
    quadrants, at each of the 32 closed cases. *)
Lemma cs_quad_tests :
  forall j jb big, (0 <= j <= 3)%Z -> (0 <= jb <= 3)%Z ->
  Model.eq (ffloor (Model.div (quad_f j) (of_u64 2))) Model.zero = (j <? 2)%Z /\
  Model.eq (ffloor (Model.div (Model.add (frem (quad_f j) (of_u64 2)) (count_f j jb big))
    (of_u64 2))) Model.zero = (cs_kd j jb big =? 0)%Z /\
  Model.le (ffloor (Model.div (Model.add (frem (quad_f j) (of_u64 2)) (count_f j jb big))
    (of_u64 2))) (of_u64 1) = (cs_kd j jb big <=? 1)%Z.
Proof.
intros j jb big Hj Hjb.
assert (Ej : j = 0%Z \/ j = 1%Z \/ j = 2%Z \/ j = 3%Z) by lia.
assert (Ejb : jb = 0%Z \/ jb = 1%Z \/ jb = 2%Z \/ jb = 3%Z) by lia.
destruct Ej as [-> | [-> | [-> | ->]]]; destruct Ejb as [-> | [-> | [-> | ->]]];
  destruct big; vm_compute; repeat split.
Qed.

(** The branches of [Interval::cos] after [(q, n)] is chosen, as in
    [Model.v]. *)
Definition cs_branch (m : mpfr) (first : bool) (a b q n : f64) : option Interval :=
  if Model.eq n Model.zero then
    if Model.eq q Model.zero then Some (Interval.with_infsup_raw (cos_rd m b) (cos_ru m a))
    else Some (Interval.with_infsup_raw (cos_rd m a) (cos_ru m b))
  else if Model.le n (of_u64 1) then
    if Model.eq q Model.zero then
      Some (Interval.with_infsup_raw (opp (of_u64 1)) (fmax first (cos_ru m a) (cos_ru m b)))
    else Some (Interval.with_infsup_raw (fmin first (cos_rd m a) (cos_rd m b)) (of_u64 1))
  else Some (Interval.const_interval (opp (of_u64 1)) (of_u64 1)).

(** ** [[-1, 1]] *)

Lemma cs_full_encl :
  forall x,
  encloses (image_dom real_dom cos x) (Interval.const_interval (opp (of_u64 1)) (of_u64 1)).
Proof.
intros x. apply br_full_encl. intros r _ _. apply COS_bound.
Qed.

(** [x] holds a maximum and a minimum of [cos] if it holds two reals
    [2 * PI] apart ([cos_wide]), or two consecutive multiples of π. *)
Lemma cs_full_tight :
  forall x r t, valid x -> mem r x -> mem t x -> 2 * PI <= t - r ->
  is_tightest (image_dom real_dom cos x) (Interval.const_interval (opp (of_u64 1)) (of_u64 1)).
Proof.
intros x r t Hx Hr Ht Hrt. apply br_full_tight; [intros u _ _; apply COS_bound|].
destruct (cos_wide r t ltac:(lra)) as (u & v & Hu & Hv & Cu & Cv).
exists u, v.
split; [exact (cs_mem_between x r t u Hx Hr Ht Hu)|]. split; [exact I|]. split; [exact Cu|].
split; [exact (cs_mem_between x r t v Hx Hr Ht Hv)|]. split; [exact I | exact Cv].
Qed.

Lemma cs_full_tight_k :
  forall x k, mem (IZR k * PI) x -> mem ((IZR k + 1) * PI) x ->
  is_tightest (image_dom real_dom cos x) (Interval.const_interval (opp (of_u64 1)) (of_u64 1)).
Proof.
intros x k H0 H1. apply br_full_tight; [intros r _ _; apply COS_bound|].
pose proof (cos_kPI k) as C0. pose proof (cs_cos_succ k) as C1.
destruct (Z.even k).
- exists (IZR k * PI), ((IZR k + 1) * PI).
  exact (conj H0 (conj I (conj C0 (conj H1 (conj I C1))))).
- exists ((IZR k + 1) * PI), (IZR k * PI).
  exact (conj H1 (conj I (conj C1 (conj H0 (conj I C0))))).
Qed.

(** ** The branches with MPFR *)

Section CsBranches.

Variables (emin emax : Z) (m : mpfr).

Hypothesis Hrange : range_ok emin emax.
Hypothesis Hget : get_d_ok emin emax m.
Hypothesis Hc : cos_ok emin emax m.

(** If [a == b], [x] holds the one real [a], and both monotone forms are
    [[cos_rd(a), cos_ru(a)]]. *)
Lemma cs_single :
  forall x, valid x -> Interval.is_empty x = false ->
  Model.eq (Interval.inf_raw x) (Interval.sup_raw x) = true ->
  is_tightest (image_dom real_dom cos x)
    (Interval.with_infsup_raw (cos_rd m (Interval.sup_raw x)) (cos_ru m (Interval.inf_raw x))) /\
  is_tightest (image_dom real_dom cos x)
    (Interval.with_infsup_raw (cos_rd m (Interval.inf_raw x)) (cos_ru m (Interval.sup_raw x))).
Proof using Hrange Hget Hc.
intros x Hx Hn Eab.
destruct (bounds_eq_finite x Hx Hn Eab) as (Fa & Fb & _).
pose proof (proj1 (bounds_eq x Hx Hn) Eab) as Hall.
assert (Hfin : finite_itv x) by exact (conj Hx (conj Hn (conj Fa Fb))).
split.
- apply (br_dec_tight emin emax m real_dom cos (mpfr_cos m) Hrange Hget Hc x Hfin).
  + intros r _. exact I.
  + intros r t Hr Ht _. rewrite (Hall r t Hr Ht). apply Rle_refl.
- apply (br_inc_tight emin emax m real_dom cos (mpfr_cos m) Hrange Hget Hc x Hfin).
  + intros r _. exact I.
  + intros r t Hr Ht _. rewrite (Hall r t Hr Ht). apply Rle_refl.
Qed.

(** [n = 0]: [x] lies in [[k * PI, (k + 1) * PI)], where [cos] is
    monotone. *)
Lemma cs_piece0 :
  forall x k, finite_itv x ->
  IZR k * PI <= B2R (Interval.inf_raw x) -> B2R (Interval.sup_raw x) < (IZR k + 1) * PI ->
  (Z.even k = true ->
   is_tightest (image_dom real_dom cos x)
     (Interval.with_infsup_raw (cos_rd m (Interval.sup_raw x))
        (cos_ru m (Interval.inf_raw x)))) /\
  (Z.even k = false ->
   is_tightest (image_dom real_dom cos x)
     (Interval.with_infsup_raw (cos_rd m (Interval.inf_raw x))
        (cos_ru m (Interval.sup_raw x)))).
Proof using Hrange Hget Hc.
intros x k Hfin Ha Hb.
assert (Hin : forall r, mem r x -> IZR k * PI <= r <= (IZR k + 1) * PI).
{ intros r Hr. apply (finite_itv_mem x r Hfin) in Hr. lra. }
split; intros Ev.
- apply (br_dec_tight emin emax m real_dom cos (mpfr_cos m) Hrange Hget Hc x Hfin).
  + intros r _. exact I.
  + intros r t Hr Ht Hrt.
    exact (cos_piece_dec k r t Ev (proj1 (Hin r Hr)) Hrt (proj2 (Hin t Ht))).
- apply (br_inc_tight emin emax m real_dom cos (mpfr_cos m) Hrange Hget Hc x Hfin).
  + intros r _. exact I.
  + intros r t Hr Ht Hrt.
    exact (cos_piece_inc k r t Ev (proj1 (Hin r Hr)) Hrt (proj2 (Hin t Ht))).
Qed.

(** [n = 1]: [x] lies in [[k * PI, (k + 2) * PI)]. For an even [k],
    [cos] decreases up to [(k + 1) * PI] and then increases, so it is at
    most [cos a] before and at most [cos b] after; it attains -1 there if
    [(k + 1) * PI] is in [x]. An odd [k] is the same upside down. *)
Lemma cs_piece1 :
  forall first x k, finite_itv x ->
  IZR k * PI <= B2R (Interval.inf_raw x) -> B2R (Interval.sup_raw x) < (IZR k + 2) * PI ->
  (Z.even k = true ->
   let y := Interval.with_infsup_raw (opp (of_u64 1))
     (fmax first (cos_ru m (Interval.inf_raw x)) (cos_ru m (Interval.sup_raw x))) in
   encloses (image_dom real_dom cos x) y /\
   (B2R (Interval.inf_raw x) <= (IZR k + 1) * PI <= B2R (Interval.sup_raw x) ->
    is_tightest (image_dom real_dom cos x) y)) /\
  (Z.even k = false ->
   let y := Interval.with_infsup_raw
     (fmin first (cos_rd m (Interval.inf_raw x)) (cos_rd m (Interval.sup_raw x))) (of_u64 1) in
   encloses (image_dom real_dom cos x) y /\
   (B2R (Interval.inf_raw x) <= (IZR k + 1) * PI <= B2R (Interval.sup_raw x) ->
    is_tightest (image_dom real_dom cos x) y)).
Proof using Hrange Hget Hc.
intros first x k Hfin Ha Hb.
assert (Hin : forall r, mem r x ->
  B2R (Interval.inf_raw x) <= r <= B2R (Interval.sup_raw x))
  by (intros r Hr; exact (proj1 (finite_itv_mem x r Hfin) Hr)).
assert (Hk1 : IZR (k + 1) * PI = (IZR k + 1) * PI) by (rewrite plus_IZR; reflexivity).
assert (Hk2 : (IZR (k + 1) + 1) * PI = (IZR k + 2) * PI) by (rewrite plus_IZR; ring).
split; intros Ev; cbv zeta.
- assert (Ev1 : Z.even (k + 1) = false) by (rewrite cs_even_succ, Ev; reflexivity).
  (* Before [(k + 1) * PI], [cos r <= cos a]; after it, [cos r <= cos b]. *)
  assert (Hub : forall r, mem r x -> real_dom r ->
    -1 <= cos r <= Rmax (cos (B2R (Interval.inf_raw x))) (cos (B2R (Interval.sup_raw x)))).
  { intros r Hr _. destruct (Hin r Hr) as [Har Hrb].
    split; [apply COS_bound|].
    destruct (Rle_or_lt r ((IZR k + 1) * PI)) as [H1|H1].
    - eapply Rle_trans; [|apply Rmax_l]. exact (cos_piece_dec k _ r Ev Ha Har H1).
    - eapply Rle_trans; [|apply Rmax_r]. apply (cos_piece_inc (k + 1) r _ Ev1).
      + rewrite Hk1. lra.
      + exact Hrb.
      + rewrite Hk2. lra. }
  split.
  + exact (br_min_encl emin emax m real_dom cos (mpfr_cos m) Hrange Hget Hc first x Hfin I I
      (fun r _ _ => COS_bound r) Hub).
  + intros Hcrit.
    apply (br_min_tight emin emax m real_dom cos (mpfr_cos m) Hrange Hget Hc first x Hfin).
    * intros r _. exact I.
    * intros r _. apply COS_bound.
    * intros r Hr. exact (Hub r Hr I).
    * exists ((IZR k + 1) * PI). split; [exact (proj2 (finite_itv_mem x _ Hfin) Hcrit)|].
      rewrite cs_cos_succ, Ev. reflexivity.
- assert (Ev1 : Z.even (k + 1) = true) by (rewrite cs_even_succ, Ev; reflexivity).
  (* Before [(k + 1) * PI], [cos a <= cos r]; after it, [cos b <= cos r]. *)
  assert (Hlb : forall r, mem r x -> real_dom r ->
    Rmin (cos (B2R (Interval.inf_raw x))) (cos (B2R (Interval.sup_raw x))) <= cos r <= 1).
  { intros r Hr _. destruct (Hin r Hr) as [Har Hrb].
    split; [|apply COS_bound].
    destruct (Rle_or_lt r ((IZR k + 1) * PI)) as [H1|H1].
    - eapply Rle_trans; [apply Rmin_l|]. exact (cos_piece_inc k _ r Ev Ha Har H1).
    - eapply Rle_trans; [apply Rmin_r|]. apply (cos_piece_dec (k + 1) r _ Ev1).
      + rewrite Hk1. lra.
      + exact Hrb.
      + rewrite Hk2. lra. }
  split.
  + exact (br_max_encl emin emax m real_dom cos (mpfr_cos m) Hrange Hget Hc first x Hfin I I
      (fun r _ _ => COS_bound r) Hlb).
  + intros Hcrit.
    apply (br_max_tight emin emax m real_dom cos (mpfr_cos m) Hrange Hget Hc first x Hfin).
    * intros r _. exact I.
    * intros r _. apply COS_bound.
    * intros r Hr. exact (Hlb r Hr I).
    * exists ((IZR k + 1) * PI). split; [exact (proj2 (finite_itv_mem x _ Hfin) Hcrit)|].
      rewrite cs_cos_succ, Ev. reflexivity.
Qed.

(** With the floors [ka] of [a / PI] and [kb] of [b / PI], and [q] and
    [n] that pass the tests as [ka mod 2] and [kb - ka] would, every
    branch is the tightest: [x] lies in one piece for [kb = ka]; for
    [kb = ka + 1], [kb * PI] is in [x]; otherwise [(ka + 1) * PI] and
    [(ka + 2) * PI] are. *)
Lemma cs_exact :
  forall first x ka kb q n, finite_itv x ->
  IZR ka * PI <= B2R (Interval.inf_raw x) < (IZR ka + 1) * PI ->
  IZR kb * PI <= B2R (Interval.sup_raw x) < (IZR kb + 1) * PI ->
  Model.eq q Model.zero = Z.even ka ->
  Model.eq n Model.zero = (kb - ka =? 0)%Z ->
  Model.le n (of_u64 1) = (kb - ka <=? 1)%Z ->
  exists y, cs_branch m first (Interval.inf_raw x) (Interval.sup_raw x) q n = Some y /\
    is_tightest (image_dom real_dom cos x) y.
Proof using Hrange Hget Hc.
intros first x ka kb q n Hfin [Ha1 Ha2] [Hb1 Hb2] Eqz E0 E1.
pose proof PI_RGT_0 as HPI.
pose proof Hfin as (Hx & Hn & _).
destruct (nonempty_mem x Hx Hn) as (r0 & Hr0).
pose proof (proj1 (finite_itv_mem x r0 Hfin) Hr0) as Hr0'.
assert (Hk : (ka <= kb)%Z).
{ assert (H : IZR ka < IZR kb + 1) by (apply (Rmult_lt_reg_r PI); [exact HPI | lra]).
  rewrite <- plus_IZR in H. apply lt_IZR in H. lia. }
unfold cs_branch. rewrite Eqz, E0, E1.
destruct (Z.eq_dec (kb - ka) 0) as [D0|D0];
  [|destruct (Z.eq_dec (kb - ka) 1) as [D1|D1]].
- (* [kb = ka]: one piece. *)
  rewrite (proj2 (Z.eqb_eq _ _) D0). cbv beta iota.
  assert (Ekb : kb = ka) by lia. subst kb.
  pose proof (cs_piece0 x ka Hfin Ha1 Hb2) as Hp.
  destruct (Z.even ka) eqn:Ev; cbv beta iota; (eexists; split; [reflexivity|]);
    [exact (proj1 Hp eq_refl) | exact (proj2 Hp eq_refl)].
- (* [kb = ka + 1]: two pieces, with -1 or 1 at [kb * PI] between them. *)
  rewrite (proj2 (Z.eqb_neq _ _) D0), (proj2 (Z.leb_le (kb - ka) 1) ltac:(lia)).
  cbv beta iota.
  assert (Ekb : IZR kb = IZR ka + 1)
    by (replace kb with (ka + 1)%Z by lia; apply plus_IZR).
  rewrite Ekb in Hb1, Hb2.
  assert (Hb3 : B2R (Interval.sup_raw x) < (IZR ka + 2) * PI) by lra.
  assert (Hcrit : B2R (Interval.inf_raw x) <= (IZR ka + 1) * PI <= B2R (Interval.sup_raw x))
    by lra.
  pose proof (cs_piece1 first x ka Hfin Ha1 Hb3) as Hp.
  destruct (Z.even ka) eqn:Ev; cbv beta iota;
    [pose proof (proj1 Hp eq_refl) as T | pose proof (proj2 Hp eq_refl) as T];
    cbv zeta in T; destruct T as [_ T];
    (eexists; split; [reflexivity | exact (T Hcrit)]).
- (* [kb >= ka + 2]: [(ka + 1) * PI] and [(ka + 2) * PI] are in [x]. *)
  rewrite (proj2 (Z.eqb_neq _ _) D0), (proj2 (Z.leb_gt (kb - ka) 1) ltac:(lia)).
  cbv beta iota.
  eexists. split; [reflexivity|].
  assert (Ekb : IZR ka + 2 <= IZR kb) by (rewrite <- plus_IZR; apply IZR_le; lia).
  assert (H3 : (IZR ka + 2) * PI <= IZR kb * PI)
    by (apply Rmult_le_compat_r; [lra | exact Ekb]).
  apply (cs_full_tight_k x (ka + 1)); rewrite plus_IZR;
    apply (proj2 (finite_itv_mem x _ Hfin)); lra.
Qed.

End CsBranches.

(** ** [Interval::cos] *)

(** The result is the tightest for every [x]. The [(q, n)] that the
    branches test come from floors of [a / PI] and [b / PI] that are exact
    ([floors_exact_ok] in [TrigCert.v], or [n = 0]), from the quadrants
    ([quadrants_correct] in [TrigCount.v]), or [x] is a singleton, or at
    least [2 * PI] wide ([trig_wide]), or unbounded. *)
Lemma cs_main :
  forall emin emax m has_fma first x,
  range_ok emin emax -> get_d_ok emin emax m -> cos_ok emin emax m -> sin_ok emin emax m ->
  valid x ->
  exists y, Interval.cos m has_fma first x = Some y /\
    is_tightest (image_dom real_dom cos x) y.
Proof.
intros emin emax m has_fma first x Hrange Hget Hc Hs Hx.
pose proof PI_RGT_0 as HPI.
destruct (Interval.is_empty x) eqn:Hn.
{ (* An empty [x] is returned, and its image is empty. *)
  exists x. unfold Interval.cos. rewrite Hn. split; [reflexivity|].
  rewrite (valid_empty_eq x Hx Hn). apply tightest_empty. intros u (r & Hr & _).
  exact (mem_nan Interval.EMPTY r eq_refl Hr). }
destruct (trig_reduce has_fma Interval.PI PI x PI_const Hx Hn) as (z & Hz & Hlo & Hhi).
unfold Interval.cos. rewrite Hn, Hz. cbv beta iota zeta.
destruct (Model.eq (Interval.inf_raw x) (Interval.sup_raw x)) eqn:Eab; cbv beta iota.
{ (* [a == b]: [n = 0], so [(q, n)] is kept, and either branch is the
     tightest. *)
  rewrite cs_eq_zero. cbv beta iota delta [orb]. rewrite cs_eq_zero. cbv beta iota.
  destruct (cs_single emin emax m Hrange Hget Hc x Hx Hn Eab) as [T1 T2].
  destruct (Model.eq (rem_euclid_2 (Interval.inf_raw (Interval.floor z))) Model.zero);
    cbv beta iota; (eexists; split; [reflexivity|]); assumption. }
assert (Hfull : Interval.inf_raw x = B754_infinity true \/
    Interval.sup_raw x = B754_infinity false ->
  is_tightest (image_dom real_dom cos x)
    (Interval.const_interval (opp (of_u64 1)) (of_u64 1))).
{ (* An unbounded [x] gives [[-1, 1]], the tightest. *)
  intros Hinf. destruct (cs_unbounded x Hx Hn Hinf) as (r & t & Hr & Ht & Hrt).
  exact (cs_full_tight x r t Hx Hr Ht Hrt). }
destruct Hlo as [(Ea & Eqa) | (Fa & Fqa & ka & Hka & Hkpa & _)];
  destruct Hhi as [(Eb & Eqb) | (Fb & Fqb & kb & Hkb & Hkpb)].
- (* [a = -inf] and [b = +inf]: [n = +inf] and [b - a = +inf], so
     [(q, n)] is kept and gives [[-1, 1]]. *)
  rewrite (cs_n_inf _ _ (or_introl Eqa) (or_introl Eqb) (or_introl Eqa)), cs_inf_eq,
    (cs_sub_inf _ _ (or_introl Ea) (or_introl Eb) (or_introl Ea)), cs_le8_inf.
  cbv beta iota delta [orb]. rewrite cs_inf_eq, cs_inf_le. cbv beta iota.
  eexists. split; [reflexivity|]. exact (Hfull (or_introl Ea)).
- rewrite (cs_n_inf _ _ (or_introl Eqa) (or_intror Fqb) (or_introl Eqa)), cs_inf_eq,
    (cs_sub_inf _ _ (or_introl Ea) (or_intror Fb) (or_introl Ea)), cs_le8_inf.
  cbv beta iota delta [orb]. rewrite cs_inf_eq, cs_inf_le. cbv beta iota.
  eexists. split; [reflexivity|]. exact (Hfull (or_introl Ea)).
- rewrite (cs_n_inf _ _ (or_intror Fqa) (or_introl Eqb) (or_intror Eqb)), cs_inf_eq,
    (cs_sub_inf _ _ (or_intror Fa) (or_introl Eb) (or_intror Eb)), cs_le8_inf.
  cbv beta iota delta [orb]. rewrite cs_inf_eq, cs_inf_le. cbv beta iota.
  eexists. split; [reflexivity|]. exact (Hfull (or_intror Eb)).
- (* Finite bounds: [ka * PI <= a <= b < (kb + 1) * PI], so [ka <= kb],
     and the tests of [n] decide [kb - ka]. *)
  assert (Hfin : finite_itv x) by exact (conj Hx (conj Hn (conj Fa Fb))).
  destruct (nonempty_mem x Hx Hn) as (r0 & Hr0).
  pose proof (proj1 (finite_itv_mem x r0 Hfin) Hr0) as Hr0'.
  assert (Hab : B2R (Interval.inf_raw x) <= B2R (Interval.sup_raw x)) by lra.
  assert (Hk : (ka <= kb)%Z).
  { assert (H : IZR ka < IZR kb + 1) by (apply (Rmult_lt_reg_r PI); [exact HPI | lra]).
    rewrite <- plus_IZR in H. apply lt_IZR in H. lia. }
  pose proof (n_small _ _ ka kb Fqa Fqb Hka Hkb Hk) as Hns. cbv zeta in Hns.
  destruct Hns as (Hn0 & Hj).
  destruct (Hj 1%Z ltac:(lia)) as (_ & Hle1 & _).
  assert (Hq : Model.eq (rem_euclid_2 (Interval.inf_raw (Interval.floor z))) Model.zero =
    Z.even ka).
  { rewrite (rem_euclid_2_int _ ka Fqa Hka).
    destruct (Z.even ka); [exact cs_eq_zero | exact cs_eq_one]. }
  set (qa := Interval.inf_raw (Interval.floor z)) in *.
  set (qb := Interval.sup_raw (Interval.floor z)) in *.
  destruct (Z.eq_dec (kb - ka) 0) as [D0|D0].
  + (* [kb = ka]: [n = 0], so [(q, n)] is kept, and [ka] and [kb] are the
       floors of [a / PI] and [b / PI]. *)
    assert (Et : (Model.eq (Model.sub qb qa) Model.zero ||
      Model.le (of_u64 8) (Model.sub (Interval.sup_raw x) (Interval.inf_raw x))) = true)
      by (rewrite Hn0, (proj2 (Z.eqb_eq _ _) D0); reflexivity).
    rewrite Et. cbv beta iota.
    assert (Ekb : kb = ka) by lia. subst kb.
    assert (Ha1 : B2R (Interval.inf_raw x) < (IZR ka + 1) * PI) by lra.
    assert (Hb1 : IZR ka * PI <= B2R (Interval.sup_raw x)) by lra.
    exact (cs_exact emin emax m Hrange Hget Hc first x ka ka _ _ Hfin (conj Hkpa Ha1)
      (conj Hb1 Hkpb) Hq Hn0 Hle1).
  + destruct (Model.le (of_u64 8) (Model.sub (Interval.sup_raw x) (Interval.inf_raw x)))
      eqn:Ew.
    * (* [b - a >= 8]: [(q, n)] is kept, and [x] holds two reals [2 * PI]
         apart, so [kb >= ka + 2] and the result is [[-1, 1]]. *)
      assert (Et : (Model.eq (Model.sub qb qa) Model.zero || true) = true)
        by (destruct (Model.eq (Model.sub qb qa) Model.zero); reflexivity).
      rewrite Et. cbv beta iota.
      assert (H27 : 2 * PI <= IZR 8 - 1).
      { destruct PI_bounds as [_ H]. rewrite pb_hi_R in H. lra. }
      destruct (trig_wide x 8 (2 * PI) Hx Hn ltac:(lia) H27 Ew) as (r & t & Hr & Ht & Hrt).
      pose proof (proj1 (finite_itv_mem x r Hfin) Hr) as Hr'.
      pose proof (proj1 (finite_itv_mem x t Hfin) Ht) as Ht'.
      assert (H2 : (2 <= kb - ka)%Z).
      { assert (H : IZR ka + 2 < IZR kb + 1)
          by (apply (Rmult_lt_reg_r PI); [exact HPI | lra]).
        rewrite <- !plus_IZR in H. apply lt_IZR in H. lia. }
      rewrite Hn0, Hle1, (proj2 (Z.eqb_neq _ _) D0), (proj2 (Z.leb_gt (kb - ka) 1) ltac:(lia)).
      cbv beta iota.
      eexists. split; [reflexivity|]. exact (cs_full_tight x r t Hx Hr Ht Hrt).
    * (* Otherwise [floors_exact] decides. *)
      assert (Et : (Model.eq (Model.sub qb qa) Model.zero || false) = false)
        by (rewrite Hn0, (proj2 (Z.eqb_neq _ _) D0); reflexivity).
      rewrite Et. cbv beta iota.
      destruct (floors_exact_ok has_fma Interval.PI PI (Interval.inf_raw x)
        (Interval.sup_raw x) qa qb ka kb PI_const Fa Fb Fqa Hka Fqb Hkb) as (e & Ee & He).
      rewrite Ee. cbv beta iota.
      destruct e; cbv beta iota.
      -- (* The floors are exact, and [(q, n)] is kept. *)
         destruct (He eq_refl) as [Ha1 Hb1].
         exact (cs_exact emin emax m Hrange Hget Hc first x ka kb _ _ Hfin (conj Hkpa Ha1)
           (conj Hb1 Hkpb) Hq Hn0 Hle1).
      -- (* [(q, n)] comes from the quadrants [ha] of [a] and [hb] of [b]:
            [floor(r / PI) = floor(floor(r / (PI / 2)) / 2)]. *)
         assert (HPI2 : 0 < PI / 2) by lra.
         destruct (floor_div_bounds (PI / 2) (B2R (Interval.inf_raw x)) HPI2) as [Ba1 Ba2].
         destruct (floor_div_bounds (PI / 2) (B2R (Interval.sup_raw x)) HPI2) as [Bb1 Bb2].
         unfold Rfloor in Ba1, Ba2, Bb1, Bb2.
         set (ha := Zfloor (B2R (Interval.inf_raw x) / (PI / 2))) in *.
         set (hb := Zfloor (B2R (Interval.sup_raw x) / (PI / 2))) in *.
         clearbody ha hb.
         assert (Hh : (ha <= hb)%Z).
         { assert (H : IZR ha < IZR hb + 1)
             by (apply (Rmult_lt_reg_r (PI / 2)); [exact HPI2 | lra]).
           rewrite <- plus_IZR in H. apply lt_IZR in H. lia. }
         rewrite (quadrants_correct emin emax m (Interval.inf_raw x) (Interval.sup_raw x) ha hb
           Hrange Hget Hs Hc Fa Fb Hab (conj Ba1 Ba2) (conj Bb1 Bb2)).
         cbv beta iota.
         assert (Ja : (0 <= ha mod 4 <= 3)%Z) by (pose proof (Z.mod_pos_bound ha 4); lia).
         assert (Jb : (0 <= hb mod 4 <= 3)%Z) by (pose proof (Z.mod_pos_bound hb 4); lia).
         destruct (cs_quad_tests (ha mod 4) (hb mod 4) (4 <=? hb - ha)%Z Ja Jb)
           as (Q0 & N0 & N1).
         (* [ha = 2 * (ha / 2) + ha mod 2], so [ha / 2] is the floor of
            [a / PI]; the same for [hb]. *)
         assert (Ia : IZR ha = 2 * IZR (ha / 2) + IZR (ha mod 2)).
         { rewrite <- mult_IZR, <- plus_IZR. apply f_equal. apply Z.div_mod. lia. }
         assert (Ib : IZR hb = 2 * IZR (hb / 2) + IZR (hb mod 2)).
         { rewrite <- mult_IZR, <- plus_IZR. apply f_equal. apply Z.div_mod. lia. }
         assert (Sa : 0 <= IZR (ha mod 2) <= 1).
         { pose proof (Z.mod_pos_bound ha 2). split; apply IZR_le; lia. }
         assert (Sb : 0 <= IZR (hb mod 2) <= 1).
         { pose proof (Z.mod_pos_bound hb 2). split; apply IZR_le; lia. }
         rewrite Ia in Ba1, Ba2. rewrite Ib in Bb1, Bb2.
         assert (Ra : IZR (ha / 2) * PI <= B2R (Interval.inf_raw x) <
           (IZR (ha / 2) + 1) * PI) by (split; nra).
         assert (Rb : IZR (hb / 2) * PI <= B2R (Interval.sup_raw x) <
           (IZR (hb / 2) + 1) * PI) by (split; nra).
         (* The parity of [ha / 2] is [ha mod 4 < 2]. *)
         assert (Hev : Z.even (ha / 2) = (ha mod 4 <? 2)%Z).
         { pose proof (Zmod_even (ha / 2)) as E.
           destruct (Z.even (ha / 2)); cbv beta iota in E; symmetry;
             [apply Z.ltb_lt | apply Z.ltb_ge]; Z.div_mod_to_equations; lia. }
         (* For [hb - ha < 4] the count is [hb / 2 - ha / 2]; otherwise both
            are at least 2. *)
         assert (HKD : (cs_kd (ha mod 4) (hb mod 4) (4 <=? hb - ha) = hb / 2 - ha / 2 \/
           (2 <= cs_kd (ha mod 4) (hb mod 4) (4 <=? hb - ha) /\ 2 <= hb / 2 - ha / 2))%Z).
         { unfold cs_kd. destruct (Z.leb_spec 4 (hb - ha)); [right | left];
             Z.div_mod_to_equations; lia. }
         destruct (cs_tests_eq _ _ HKD) as [T0 T1].
         exact (cs_exact emin emax m Hrange Hget Hc first x (ha / 2) (hb / 2) _ _ Hfin Ra Rb
           (eq_trans Q0 (eq_sym Hev)) (eq_trans N0 T0) (eq_trans N1 T1)).
Qed.

Theorem cos_encloses :
  forall emin emax m has_fma first x,
  range_ok emin emax -> get_d_ok emin emax m -> cos_ok emin emax m -> sin_ok emin emax m ->
  valid x ->
  exists y, Interval.cos m has_fma first x = Some y /\
    encloses (image_dom real_dom cos x) y.
Proof.
intros emin emax m has_fma first x Hrange Hget Hc Hs Hx.
destruct (cs_main emin emax m has_fma first x Hrange Hget Hc Hs Hx) as (y & Ey & Ht).
exists y. split; [exact Ey | exact (cs_tight_encl _ _ Ht)].
Qed.

Theorem cos_correct :
  forall emin emax m has_fma first x,
  range_ok emin emax -> get_d_ok emin emax m -> cos_ok emin emax m -> sin_ok emin emax m ->
  valid x ->
  exists y, Interval.cos m has_fma first x = Some y /\
    is_tightest (image_dom real_dom cos x) y.
Proof. exact cs_main. Qed.

(** ** [DecInterval::cos] *)

Theorem dec_cos_correct :
  forall emin emax m has_fma first x,
  range_ok emin emax -> get_d_ok emin emax m -> cos_ok emin emax m -> sin_ok emin emax m ->
  valid (itv x) -> com_common x ->
  exists y, DecInterval.cos m has_fma first x = Some y /\
    if DecInterval.is_nai x then y = DecInterval.NAI
    else
      is_tightest (image_dom real_dom cos (itv x)) (itv y) /\
      exists d, strongest_dom real_dom d cos (itv x) (itv y) /\
        dec y = dec_min d (dec x).
Proof.
intros emin emax m has_fma first x Hrange Hget Hc Hs Hx Hcc.
destruct (cs_main emin emax m has_fma first (itv x) Hrange Hget Hc Hs Hx) as (y & Ey & Ht).
pose proof (cs_tight_encl _ _ Ht) as He.
unfold DecInterval.cos. rewrite Ey. cbv beta iota.
exists (DecInterval.set_dec y (dec x)). split; [reflexivity|].
destruct (DecInterval.is_nai x) eqn:Enai.
- (* NaI: [set_dec] of [ill] is NaI. *)
  unfold DecInterval.is_nai, dec_eqb in Enai. revert Enai.
  destruct (dec x); intros Enai; cbn in Enai; try discriminate Enai. reflexivity.
- assert (Hd : dec x <> Ill).
  { intros E. unfold DecInterval.is_nai in Enai. rewrite E in Enai.
    vm_compute in Enai. discriminate Enai. }
  (* An empty [x] is returned as it is. *)
  assert (Hempty : (forall r, ~ mem r (itv x)) -> Interval.is_empty y = true).
  { intros Hno. destruct (Interval.is_empty (itv x)) eqn:Ex.
    - unfold Interval.cos in Ey. rewrite Ex in Ey. cbv beta iota in Ey.
      injection Ey as E'. rewrite <- E'. exact Ex.
    - destruct (nonempty_mem _ Hx Ex) as (r & Hr). destruct (Hno r Hr). }
  (* [cos] is continuous and defined everywhere, so [e = com]; a [com]
     [x] is common ([com_common]), so bounded. *)
  pose proof (trig_set_dec_correct real_dom cos x y Com Hx Hd He Hempty
    (fun r _ _ => continuity_pt_continue_in cos real_dom r (continuity_cos r))
    (or_intror (conj eq_refl (conj (fun r _ => I)
      (fun Ed _ => common_bounded _ (Hcc Ed)))))) as T.
  cbv zeta in T. rewrite dec_min_Com_r in T.
  destruct T as (_ & T2 & _ & T4).
  split; [exact (T2 Ht)|].
  apply T4. intros E. discriminate E.
Qed.
