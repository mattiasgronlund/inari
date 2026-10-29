(** * [x / y] of intervals whose divisor, and [recip x] of intervals
    whose argument, does not contain 0 in its interior

    If [x] is in [M], [N0], [N1], [P0] or [P1] and [y] in [N0], [N1], [P0]
    or [P1], except for [M × N0] and [M × P0], [x / y] returns the tightest
    interval that contains the image of [x × y] under [/] on its domain
    ([image2_dom] in [Ieee1788.v]), and the same holds for [recip x] with
    [x] in [N0], [N1], [P0] or [P1].

    Each case calls one of the [div_*] helpers of [src/basic.rs], or a
    branch of [Interval::recip], whose [div_ru] is [Bdiv mode_UP] in each
    lane ([div_ru_correct] in [DivRu.v]). [x = [a, b]] is stored as
    [[-a; b]] and [y = [c, d]] as [[-c; d]]. Each lane of the result is
    one of the forms of [DivLane.v], for the sets of [DivSets.v]:
    - [M × N1]: [[RU(b / (-d)); RU((-a) / (-d))]], both (a).
    - [M × P1]: [[RU((-a) / c); RU(b / c)]], both (a).
    - [N × N0]: [[RU(b / (-c)); +inf]], (c) and (b).
    - [N × N1]: [[RU(b / (-c)); RU(a / d)]], (c) and (a').
    - [N × P0]: [[+inf; RU(b / d)]], (b) and (c).
    - [N × P1]: [[RU((-a) / c); RU(b / d)]], (a) and (c).
    - [P × N0]: [[+inf; RU((-a) / (-c))]], (b) and (c).
    - [P × N1]: [[RU((-b) / d); RU((-a) / (-c))]], (a') and (c).
    - [P × P0]: [[RU((-a) / d); +inf]], (c) and (b).
    - [P × P1]: [[RU((-a) / d); RU(b / c)]], (c) and (a).
    - [recip] of [N0]: [[+inf; RU((-1) / (-a))]], (b) and (c).
    - [recip] of [N1]: [[RU((-1) / b); RU((-1) / (-a))]], (a') and (c).
    - [recip] of [P0]: [[RU((-1) / b); +inf]], (c) and (b).
    - [recip] of [P1]: [[RU((-1) / b); RU((-1) / (-a))]], (c) and (a').
    Here [N] is [N0] or [N1] and [P] is [P0] or [P1], as both take the
    same branch of [Interval::div]. *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer Sign MaxMin AddSub Classify2
  Classes DivRu DivTight DivLane DivSets.

Open Scope R_scope.

(** ** What [Interval::div] and [Interval::recip] compute *)

(** [x / y] for [M × N1] divides [[b; -a]] by [[-d; -d]]. *)
Lemma div_MN1_eq :
  forall has_fma x y,
  Interval.classify x = Some CM -> Interval.classify y = Some CN1 ->
  Interval.div has_fma x y =
  Some {| rep := (Bdiv mode_UP (snd (rep x)) (opp (snd (rep y))),
                  Bdiv mode_UP (fst (rep x)) (opp (snd (rep y)))) |}.
Proof.
intros has_fma x y Cx Cy. unfold Interval.div, Interval.div_m_n1.
rewrite (classify2_pair _ _ _ _ Cx Cy); cbv beta iota zeta.
rewrite div_ru_correct. reflexivity.
Qed.

(** [x / y] for [M × P1] divides [[-a; b]] by [[c; c]]. *)
Lemma div_MP1_eq :
  forall has_fma x y,
  Interval.classify x = Some CM -> Interval.classify y = Some CP1 ->
  Interval.div has_fma x y =
  Some {| rep := (Bdiv mode_UP (fst (rep x)) (opp (fst (rep y))),
                  Bdiv mode_UP (snd (rep x)) (opp (fst (rep y)))) |}.
Proof.
intros has_fma x y Cx Cy. unfold Interval.div, Interval.div_m_p1.
rewrite (classify2_pair _ _ _ _ Cx Cy); cbv beta iota zeta.
rewrite div_ru_correct. reflexivity.
Qed.

(** [x / y] for [N × N0] divides [b] by [-c], and the second lane is
    +inf. *)
Lemma div_NN0_eq :
  forall has_fma x y,
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  Interval.classify y = Some CN0 ->
  Interval.div has_fma x y =
  Some {| rep := (Bdiv mode_UP (snd (rep x)) (fst (rep y)), B754_infinity false) |}.
Proof.
intros has_fma x y Cx Cy. unfold Interval.div, Interval.div_n_n0.
destruct Cx as [Cx|Cx]; rewrite (classify2_pair _ _ _ _ Cx Cy);
  cbv beta iota zeta; rewrite div_ru_correct, infinity_eq; reflexivity.
Qed.

(** [x / y] for [N × N1] divides [[b; a]] by [[-c; d]]. *)
Lemma div_NN1_eq :
  forall has_fma x y,
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  Interval.classify y = Some CN1 ->
  Interval.div has_fma x y =
  Some {| rep := (Bdiv mode_UP (snd (rep x)) (fst (rep y)),
                  Bdiv mode_UP (opp (fst (rep x))) (snd (rep y))) |}.
Proof.
intros has_fma x y Cx Cy. unfold Interval.div, Interval.div_n_n1.
destruct Cx as [Cx|Cx]; rewrite (classify2_pair _ _ _ _ Cx Cy);
  cbv beta iota zeta; rewrite div_ru_correct; reflexivity.
Qed.

(** [x / y] for [N × P0] divides [b] by [d], and the first lane is +inf. *)
Lemma div_NP0_eq :
  forall has_fma x y,
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  Interval.classify y = Some CP0 ->
  Interval.div has_fma x y =
  Some {| rep := (B754_infinity false, Bdiv mode_UP (snd (rep x)) (snd (rep y))) |}.
Proof.
intros has_fma x y Cx Cy. unfold Interval.div, Interval.div_n_p0.
destruct Cx as [Cx|Cx]; rewrite (classify2_pair _ _ _ _ Cx Cy);
  cbv beta iota zeta; rewrite div_ru_correct, infinity_eq; reflexivity.
Qed.

(** [x / y] for [N × P1] divides [[-a; b]] by [[c; d]]. *)
Lemma div_NP1_eq :
  forall has_fma x y,
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  Interval.classify y = Some CP1 ->
  Interval.div has_fma x y =
  Some {| rep := (Bdiv mode_UP (fst (rep x)) (opp (fst (rep y))),
                  Bdiv mode_UP (snd (rep x)) (snd (rep y))) |}.
Proof.
intros has_fma x y Cx Cy. unfold Interval.div, Interval.div_n_p1.
destruct Cx as [Cx|Cx]; rewrite (classify2_pair _ _ _ _ Cx Cy);
  cbv beta iota zeta; rewrite div_ru_correct; reflexivity.
Qed.

(** [x / y] for [P × N0] divides [-a] by [-c], and the first lane is
    +inf. *)
Lemma div_PN0_eq :
  forall has_fma x y,
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  Interval.classify y = Some CN0 ->
  Interval.div has_fma x y =
  Some {| rep := (B754_infinity false, Bdiv mode_UP (fst (rep x)) (fst (rep y))) |}.
Proof.
intros has_fma x y Cx Cy. unfold Interval.div, Interval.div_p_n0.
destruct Cx as [Cx|Cx]; rewrite (classify2_pair _ _ _ _ Cx Cy);
  cbv beta iota zeta; rewrite div_ru_correct, infinity_eq; reflexivity.
Qed.

(** [x / y] for [P × N1] divides [[-b; -a]] by [[d; -c]]. *)
Lemma div_PN1_eq :
  forall has_fma x y,
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  Interval.classify y = Some CN1 ->
  Interval.div has_fma x y =
  Some {| rep := (Bdiv mode_UP (opp (snd (rep x))) (snd (rep y)),
                  Bdiv mode_UP (fst (rep x)) (fst (rep y))) |}.
Proof.
intros has_fma x y Cx Cy. unfold Interval.div, Interval.div_p_n1.
destruct Cx as [Cx|Cx]; rewrite (classify2_pair _ _ _ _ Cx Cy);
  cbv beta iota zeta; rewrite div_ru_correct; reflexivity.
Qed.

(** [x / y] for [P × P0] divides [-a] by [d], and the second lane is
    +inf. *)
Lemma div_PP0_eq :
  forall has_fma x y,
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  Interval.classify y = Some CP0 ->
  Interval.div has_fma x y =
  Some {| rep := (Bdiv mode_UP (fst (rep x)) (snd (rep y)), B754_infinity false) |}.
Proof.
intros has_fma x y Cx Cy. unfold Interval.div, Interval.div_p_p0.
destruct Cx as [Cx|Cx]; rewrite (classify2_pair _ _ _ _ Cx Cy);
  cbv beta iota zeta; rewrite div_ru_correct, infinity_eq; reflexivity.
Qed.

(** [x / y] for [P × P1] divides [[-a; b]] by [[d; c]]. *)
Lemma div_PP1_eq :
  forall has_fma x y,
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  Interval.classify y = Some CP1 ->
  Interval.div has_fma x y =
  Some {| rep := (Bdiv mode_UP (fst (rep x)) (snd (rep y)),
                  Bdiv mode_UP (snd (rep x)) (opp (fst (rep y)))) |}.
Proof.
intros has_fma x y Cx Cy. unfold Interval.div, Interval.div_p_p1.
destruct Cx as [Cx|Cx]; rewrite (classify2_pair _ _ _ _ Cx Cy);
  cbv beta iota zeta; rewrite div_ru_correct; reflexivity.
Qed.

(** [recip x] for [N0] divides [-1] by [-a], and the first lane is +inf.
    [Interval::recip] writes [-1.0] as [opp (of_u64 1)], which is
    [opp one]. *)
Lemma recip_N0_eq :
  forall has_fma x, Interval.classify x = Some CN0 ->
  Interval.recip has_fma x =
  Some {| rep := (B754_infinity false, Bdiv mode_UP (opp one) (fst (rep x))) |}.
Proof.
intros has_fma x Cx. unfold Interval.recip. rewrite Cx. cbv beta iota zeta.
rewrite div_ru_correct, infinity_eq. reflexivity.
Qed.

(** [recip x] for [N1] divides [[-1; -1]] by [[b; -a]]. *)
Lemma recip_N1_eq :
  forall has_fma x, Interval.classify x = Some CN1 ->
  Interval.recip has_fma x =
  Some {| rep := (Bdiv mode_UP (opp one) (snd (rep x)),
                  Bdiv mode_UP (opp one) (fst (rep x))) |}.
Proof.
intros has_fma x Cx. unfold Interval.recip. rewrite Cx. cbv beta iota zeta.
rewrite div_ru_correct. reflexivity.
Qed.

(** [recip x] for [P0] divides [-1] by [b], and the second lane is +inf. *)
Lemma recip_P0_eq :
  forall has_fma x, Interval.classify x = Some CP0 ->
  Interval.recip has_fma x =
  Some {| rep := (Bdiv mode_UP (opp one) (snd (rep x)), B754_infinity false) |}.
Proof.
intros has_fma x Cx. unfold Interval.recip. rewrite Cx. cbv beta iota zeta.
rewrite div_ru_correct, infinity_eq. reflexivity.
Qed.

(** [recip x] for [P1] divides [[-1; -1]] by [[b; -a]]. *)
Lemma recip_P1_eq :
  forall has_fma x, Interval.classify x = Some CP1 ->
  Interval.recip has_fma x =
  Some {| rep := (Bdiv mode_UP (opp one) (snd (rep x)),
                  Bdiv mode_UP (opp one) (fst (rep x))) |}.
Proof.
intros has_fma x Cx. unfold Interval.recip. rewrite Cx. cbv beta iota zeta.
rewrite div_ru_correct. reflexivity.
Qed.

(** ** [x / y] *)

Lemma div_MN1 :
  forall has_fma x y, valid x -> valid y ->
  Interval.classify x = Some CM -> Interval.classify y = Some CN1 ->
  exists z, Interval.div has_fma x y = Some z /\
    is_tightest (image2_dom div_dom1 div_dom2 Rdiv x y) z.
Proof.
intros has_fma x y Hx Hy Cx Cy. rewrite (div_MN1_eq has_fma x y Cx Cy).
eexists. split; [reflexivity|].
destruct (xset_M x Hx Cx) as (Hup & Hum).
destruct (yset_N1 y Hy Cy) as (Fd & Dmin & Dsup).
apply div_tightest_N.
- exact (classify_nonpos y Hy (or_intror Cy)).
- destruct Hup as (_ & _ & r & Hr & _). exists r. exact Hr.
- destruct Dmin as (Hq & _). eexists. exact Hq.
- (* (a): [RU(b / (-d))]. *)
  apply div_lane_pos; [exact Hup | rewrite B2R_opp; exact Dmin |].
  rewrite is_finite_opp. exact Fd.
- (* (a): [RU((-a) / (-d))]. *)
  apply div_lane_pos; [exact Hum | rewrite B2R_opp; exact Dmin |].
  rewrite is_finite_opp. exact Fd.
Qed.

Lemma div_MP1 :
  forall has_fma x y, valid x -> valid y ->
  Interval.classify x = Some CM -> Interval.classify y = Some CP1 ->
  exists z, Interval.div has_fma x y = Some z /\
    is_tightest (image2_dom div_dom1 div_dom2 Rdiv x y) z.
Proof.
intros has_fma x y Hx Hy Cx Cy. rewrite (div_MP1_eq has_fma x y Cx Cy).
eexists. split; [reflexivity|].
destruct (xset_M x Hx Cx) as (Hup & Hum).
destruct (yset_P1 y Hy Cy) as (Fc & Dmin & Dsup).
apply div_tightest_P.
- exact (classify_nonneg y Hy (or_intror Cy)).
- destruct Hup as (_ & _ & r & Hr & _). exists r. exact Hr.
- destruct Dmin as (Hq & _). eexists. exact Hq.
- (* (a): [RU((-a) / c)]. *)
  apply div_lane_pos; [exact Hum | rewrite B2R_opp; exact Dmin |].
  rewrite is_finite_opp. exact Fc.
- (* (a): [RU(b / c)]. *)
  apply div_lane_pos; [exact Hup | rewrite B2R_opp; exact Dmin |].
  rewrite is_finite_opp. exact Fc.
Qed.

Lemma div_NN0 :
  forall has_fma x y, valid x -> valid y ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  Interval.classify y = Some CN0 ->
  exists z, Interval.div has_fma x y = Some z /\
    is_tightest (image2_dom div_dom1 div_dom2 Rdiv x y) z.
Proof.
intros has_fma x y Hx Hy Cx Cy. rewrite (div_NN0_eq has_fma x y Cx Cy).
eexists. split; [reflexivity|].
destruct (xset_N x Hx Cx) as (Hup & Hum).
destruct (yset_N0 y Hy Cy) as (Dnear & Dsup).
apply div_tightest_N.
- exact (classify_nonpos y Hy (or_introl Cy)).
- destruct Hup as (_ & Hb & _). eexists. exact Hb.
- destruct Dsup as (_ & _ & Hne & _). exact Hne.
- (* (c): [RU(b / (-c))]. *)
  exact (div_lane_nonpos _ _ _ _ Hup Dsup).
- (* (b): +inf, as [-c = 0]. *)
  apply div_lane_inf; [|exact Dnear].
  destruct Hum as (_ & _ & Hpos). exact Hpos.
Qed.

Lemma div_NN1 :
  forall has_fma x y, valid x -> valid y ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  Interval.classify y = Some CN1 ->
  exists z, Interval.div has_fma x y = Some z /\
    is_tightest (image2_dom div_dom1 div_dom2 Rdiv x y) z.
Proof.
intros has_fma x y Hx Hy Cx Cy. rewrite (div_NN1_eq has_fma x y Cx Cy).
eexists. split; [reflexivity|].
destruct (xset_N x Hx Cx) as (Hup & Hum).
destruct (yset_N1 y Hy Cy) as (Fd & Dmin & Dsup).
apply div_tightest_N.
- exact (classify_nonpos y Hy (or_intror Cy)).
- destruct Hup as (_ & Hb & _). eexists. exact Hb.
- destruct Dmin as (Hq & _). eexists. exact Hq.
- (* (c): [RU(b / (-c))]. *)
  exact (div_lane_nonpos _ _ _ _ Hup Dsup).
- (* (a'): [RU(a / d)], which is [RU((-a) / (-d))]. *)
  apply div_lane_neg; [exact Hum | exact Dmin | exact Fd].
Qed.

Lemma div_NP0 :
  forall has_fma x y, valid x -> valid y ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  Interval.classify y = Some CP0 ->
  exists z, Interval.div has_fma x y = Some z /\
    is_tightest (image2_dom div_dom1 div_dom2 Rdiv x y) z.
Proof.
intros has_fma x y Hx Hy Cx Cy. rewrite (div_NP0_eq has_fma x y Cx Cy).
eexists. split; [reflexivity|].
destruct (xset_N x Hx Cx) as (Hup & Hum).
destruct (yset_P0 y Hy Cy) as (Dnear & Dsup).
apply div_tightest_P.
- exact (classify_nonneg y Hy (or_introl Cy)).
- destruct Hup as (_ & Hb & _). eexists. exact Hb.
- destruct Dsup as (_ & _ & Hne & _). exact Hne.
- (* (b): +inf, as [c = 0]. *)
  apply div_lane_inf; [|exact Dnear].
  destruct Hum as (_ & _ & Hpos). exact Hpos.
- (* (c): [RU(b / d)]. *)
  exact (div_lane_nonpos _ _ _ _ Hup Dsup).
Qed.

Lemma div_NP1 :
  forall has_fma x y, valid x -> valid y ->
  (Interval.classify x = Some CN0 \/ Interval.classify x = Some CN1) ->
  Interval.classify y = Some CP1 ->
  exists z, Interval.div has_fma x y = Some z /\
    is_tightest (image2_dom div_dom1 div_dom2 Rdiv x y) z.
Proof.
intros has_fma x y Hx Hy Cx Cy. rewrite (div_NP1_eq has_fma x y Cx Cy).
eexists. split; [reflexivity|].
destruct (xset_N x Hx Cx) as (Hup & Hum).
destruct (yset_P1 y Hy Cy) as (Fc & Dmin & Dsup).
apply div_tightest_P.
- exact (classify_nonneg y Hy (or_intror Cy)).
- destruct Hup as (_ & Hb & _). eexists. exact Hb.
- destruct Dmin as (Hq & _). eexists. exact Hq.
- (* (a): [RU((-a) / c)]. *)
  apply div_lane_pos; [exact Hum | rewrite B2R_opp; exact Dmin |].
  rewrite is_finite_opp. exact Fc.
- (* (c): [RU(b / d)]. *)
  exact (div_lane_nonpos _ _ _ _ Hup Dsup).
Qed.

Lemma div_PN0 :
  forall has_fma x y, valid x -> valid y ->
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  Interval.classify y = Some CN0 ->
  exists z, Interval.div has_fma x y = Some z /\
    is_tightest (image2_dom div_dom1 div_dom2 Rdiv x y) z.
Proof.
intros has_fma x y Hx Hy Cx Cy. rewrite (div_PN0_eq has_fma x y Cx Cy).
eexists. split; [reflexivity|].
destruct (xset_P x Hx Cx) as (Hup & Hum).
destruct (yset_N0 y Hy Cy) as (Dnear & Dsup).
apply div_tightest_N.
- exact (classify_nonpos y Hy (or_introl Cy)).
- destruct Hup as (_ & _ & r & Hr & _). exists r. exact Hr.
- destruct Dsup as (_ & _ & Hne & _). exact Hne.
- (* (b): +inf, as [-c = 0]. *)
  apply div_lane_inf; [|exact Dnear].
  destruct Hup as (_ & _ & Hpos). exact Hpos.
- (* (c): [RU((-a) / (-c))]. *)
  exact (div_lane_nonpos _ _ _ _ Hum Dsup).
Qed.

Lemma div_PN1 :
  forall has_fma x y, valid x -> valid y ->
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  Interval.classify y = Some CN1 ->
  exists z, Interval.div has_fma x y = Some z /\
    is_tightest (image2_dom div_dom1 div_dom2 Rdiv x y) z.
Proof.
intros has_fma x y Hx Hy Cx Cy. rewrite (div_PN1_eq has_fma x y Cx Cy).
eexists. split; [reflexivity|].
destruct (xset_P x Hx Cx) as (Hup & Hum).
destruct (yset_N1 y Hy Cy) as (Fd & Dmin & Dsup).
apply div_tightest_N.
- exact (classify_nonpos y Hy (or_intror Cy)).
- destruct Hup as (_ & _ & r & Hr & _). exists r. exact Hr.
- destruct Dmin as (Hq & _). eexists. exact Hq.
- (* (a'): [RU((-b) / d)], which is [RU(b / (-d))]. *)
  apply div_lane_neg; [exact Hup | exact Dmin | exact Fd].
- (* (c): [RU((-a) / (-c))]. *)
  exact (div_lane_nonpos _ _ _ _ Hum Dsup).
Qed.

Lemma div_PP0 :
  forall has_fma x y, valid x -> valid y ->
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  Interval.classify y = Some CP0 ->
  exists z, Interval.div has_fma x y = Some z /\
    is_tightest (image2_dom div_dom1 div_dom2 Rdiv x y) z.
Proof.
intros has_fma x y Hx Hy Cx Cy. rewrite (div_PP0_eq has_fma x y Cx Cy).
eexists. split; [reflexivity|].
destruct (xset_P x Hx Cx) as (Hup & Hum).
destruct (yset_P0 y Hy Cy) as (Dnear & Dsup).
apply div_tightest_P.
- exact (classify_nonneg y Hy (or_introl Cy)).
- destruct Hup as (_ & _ & r & Hr & _). exists r. exact Hr.
- destruct Dsup as (_ & _ & Hne & _). exact Hne.
- (* (c): [RU((-a) / d)]. *)
  exact (div_lane_nonpos _ _ _ _ Hum Dsup).
- (* (b): +inf, as [c = 0]. *)
  apply div_lane_inf; [|exact Dnear].
  destruct Hup as (_ & _ & Hpos). exact Hpos.
Qed.

Lemma div_PP1 :
  forall has_fma x y, valid x -> valid y ->
  (Interval.classify x = Some CP0 \/ Interval.classify x = Some CP1) ->
  Interval.classify y = Some CP1 ->
  exists z, Interval.div has_fma x y = Some z /\
    is_tightest (image2_dom div_dom1 div_dom2 Rdiv x y) z.
Proof.
intros has_fma x y Hx Hy Cx Cy. rewrite (div_PP1_eq has_fma x y Cx Cy).
eexists. split; [reflexivity|].
destruct (xset_P x Hx Cx) as (Hup & Hum).
destruct (yset_P1 y Hy Cy) as (Fc & Dmin & Dsup).
apply div_tightest_P.
- exact (classify_nonneg y Hy (or_intror Cy)).
- destruct Hup as (_ & _ & r & Hr & _). exists r. exact Hr.
- destruct Dmin as (Hq & _). eexists. exact Hq.
- (* (c): [RU((-a) / d)]. *)
  exact (div_lane_nonpos _ _ _ _ Hum Dsup).
- (* (a): [RU(b / c)], with [c] the negated first lane of [y]. *)
  apply div_lane_pos; [exact Hup | rewrite B2R_opp; exact Dmin |].
  rewrite is_finite_opp. exact Fc.
Qed.

(** ** [recip x] *)

Lemma recip_N0 :
  forall has_fma x, valid x -> Interval.classify x = Some CN0 ->
  exists z, Interval.recip has_fma x = Some z /\
    is_tightest (image_dom recip_dom Rinv x) z.
Proof.
intros has_fma x Hx Cx. rewrite (recip_N0_eq has_fma x Cx).
eexists. split; [reflexivity|].
destruct (yset_N0 x Hx Cx) as (Dnear & Dsup).
apply recip_tightest_N.
- exact (classify_nonpos x Hx (or_introl Cx)).
- destruct Dsup as (_ & _ & Hne & _). exact Hne.
- (* (b): +inf, as [-a = 0]. *)
  apply div_lane_inf; [|exact Dnear].
  exists 1. split; [reflexivity | lra].
- (* (c): [RU((-1) / (-a))]. *)
  exact (div_lane_nonpos _ _ _ _ one_nonpos_set Dsup).
Qed.

Lemma recip_N1 :
  forall has_fma x, valid x -> Interval.classify x = Some CN1 ->
  exists z, Interval.recip has_fma x = Some z /\
    is_tightest (image_dom recip_dom Rinv x) z.
Proof.
intros has_fma x Hx Cx. rewrite (recip_N1_eq has_fma x Cx).
eexists. split; [reflexivity|].
destruct (yset_N1 x Hx Cx) as (Fb & Dmin & Dsup).
apply recip_tightest_N.
- exact (classify_nonpos x Hx (or_intror Cx)).
- destruct Dmin as (Hq & _). eexists. exact Hq.
- (* (a'): [RU((-1) / b)], which is [RU(1 / (-b))]. *)
  apply div_lane_neg; [exact one_pos_set | exact Dmin | exact Fb].
- (* (c): [RU((-1) / (-a))]. *)
  exact (div_lane_nonpos _ _ _ _ one_nonpos_set Dsup).
Qed.

Lemma recip_P0 :
  forall has_fma x, valid x -> Interval.classify x = Some CP0 ->
  exists z, Interval.recip has_fma x = Some z /\
    is_tightest (image_dom recip_dom Rinv x) z.
Proof.
intros has_fma x Hx Cx. rewrite (recip_P0_eq has_fma x Cx).
eexists. split; [reflexivity|].
destruct (yset_P0 x Hx Cx) as (Dnear & Dsup).
apply recip_tightest_P.
- exact (classify_nonneg x Hx (or_introl Cx)).
- destruct Dsup as (_ & _ & Hne & _). exact Hne.
- (* (c): [RU((-1) / b)]. *)
  exact (div_lane_nonpos _ _ _ _ one_nonpos_set Dsup).
- (* (b): +inf, as [a = 0]. *)
  apply div_lane_inf; [|exact Dnear].
  exists 1. split; [reflexivity | lra].
Qed.

Lemma recip_P1 :
  forall has_fma x, valid x -> Interval.classify x = Some CP1 ->
  exists z, Interval.recip has_fma x = Some z /\
    is_tightest (image_dom recip_dom Rinv x) z.
Proof.
intros has_fma x Hx Cx. rewrite (recip_P1_eq has_fma x Cx).
eexists. split; [reflexivity|].
destruct (yset_P1 x Hx Cx) as (Fa & Dmin & Dsup).
apply recip_tightest_P.
- exact (classify_nonneg x Hx (or_intror Cx)).
- destruct Dmin as (Hq & _). eexists. exact Hq.
- (* (c): [RU((-1) / b)]. *)
  exact (div_lane_nonpos _ _ _ _ one_nonpos_set Dsup).
- (* (a'): [RU((-1) / (-a))], which is [RU(1 / a)]. *)
  apply div_lane_neg; [exact one_pos_set | exact Dmin | exact Fa].
Qed.
