(** * [sin] of intervals is the tightest

    As [Cos.v], for [Interval::sin], which reduces by [FRAC_PI_2] and
    reads [q = qa mod 4] ([rem_euclid_4_int] in [TrigReduce.v]). On the
    quarter [[k * (PI / 2), (k + 1) * (PI / 2)]], [sin] increases for
    [k mod 4] = 0 or 3 and decreases for 1 or 2, with its maximum 1 at
    [k mod 4 = 1] and its minimum -1 at [k mod 4 = 3]. The branches join
    quarters: [q = 3, n < 2] covers quarters 3 and 0, where [sin]
    increases throughout, and so on. Each branch encloses the image, and
    it is the tightest if [x] holds two reals [2 * PI] apart or if the
    tests on [q] and [n] are those on the exact floors of [a / (PI / 2)]
    and [b / (PI / 2)] ([sn_pick]). The fast [(q, n)] from [q_nowrap] are
    kept for a singleton, for [n = 0], for [b - a >= 8] (then [x] holds
    two reals [2 * PI] apart, [trig_wide] in [TrigCert.v]) and when
    [floors_exact] certifies the floors ([floors_exact_ok]); otherwise
    [quadrants] reads the exact quadrants from the signs of [sin_rd] and
    [cos_ru] ([quadrants_correct] in [TrigCount.v]). So the result is the
    tightest for every [x] ([sin_correct]). The decoration is as for
    [cos] ([dec_sin_correct]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr ComCommon Integer
  PiBounds TrigPieces TrigReduce TrigBranch TrigQuad TrigCount TrigCert DecBinary AddSub
  MonoInc Sqrt ElemDec.

Open Scope R_scope.

(** ** [sin] on half periods *)

Lemma sn_mod_add : forall j q d, (j mod 4 = q)%Z -> ((j + d) mod 4 = (q + d) mod 4)%Z.
Proof.
intros j q d <-. rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Lemma sn_mod_sub : forall j q d, (j mod 4 = q)%Z -> ((j - d) mod 4 = (q - d) mod 4)%Z.
Proof.
intros j q d H. unfold Z.sub. apply sn_mod_add. exact H.
Qed.

(** [sin] increases on [[j * (PI / 2), (j + 2) * (PI / 2)]] for
    [j mod 4 = 3]: on both quarters [j] and [j + 1], so also across their
    common bound. *)
Lemma sn_inc :
  forall j r t, (j mod 4 = 3)%Z ->
  IZR j * (PI / 2) <= r -> r <= t -> t <= (IZR j + 2) * (PI / 2) -> sin r <= sin t.
Proof.
intros j r t Hj Hr Hrt Ht.
assert (Hj1 : ((j + 1) mod 4 = 0)%Z) by exact (sn_mod_add j 3 1 Hj).
pose proof PI_RGT_0 as HPI.
destruct (Rle_or_lt t ((IZR j + 1) * (PI / 2))) as [H1|H1].
- exact (sin_piece_inc j r t (or_intror Hj) Hr Hrt H1).
- destruct (Rle_or_lt ((IZR j + 1) * (PI / 2)) r) as [H2|H2].
  + apply (sin_piece_inc (j + 1));
      [left; exact Hj1 | rewrite plus_IZR; exact H2 | exact Hrt | rewrite plus_IZR; lra].
  + apply Rle_trans with (sin ((IZR j + 1) * (PI / 2))).
    * apply (sin_piece_inc j); [right; exact Hj | exact Hr | lra | lra].
    * apply (sin_piece_inc (j + 1));
        [left; exact Hj1 | rewrite plus_IZR; lra | lra | rewrite plus_IZR; lra].
Qed.

(** [sin] decreases on [[j * (PI / 2), (j + 2) * (PI / 2)]] for
    [j mod 4 = 1]. *)
Lemma sn_dec :
  forall j r t, (j mod 4 = 1)%Z ->
  IZR j * (PI / 2) <= r -> r <= t -> t <= (IZR j + 2) * (PI / 2) -> sin t <= sin r.
Proof.
intros j r t Hj Hr Hrt Ht.
assert (Hj1 : ((j + 1) mod 4 = 2)%Z) by exact (sn_mod_add j 1 1 Hj).
pose proof PI_RGT_0 as HPI.
destruct (Rle_or_lt t ((IZR j + 1) * (PI / 2))) as [H1|H1].
- exact (sin_piece_dec j r t (or_introl Hj) Hr Hrt H1).
- destruct (Rle_or_lt ((IZR j + 1) * (PI / 2)) r) as [H2|H2].
  + apply (sin_piece_dec (j + 1));
      [right; exact Hj1 | rewrite plus_IZR; exact H2 | exact Hrt | rewrite plus_IZR; lra].
  + apply Rle_trans with (sin ((IZR j + 1) * (PI / 2))).
    * apply (sin_piece_dec (j + 1));
        [right; exact Hj1 | rewrite plus_IZR; lra | lra | rewrite plus_IZR; lra].
    * apply (sin_piece_dec j); [left; exact Hj | exact Hr | lra | lra].
Qed.

(** Around the maximum at [j * (PI / 2)], [j mod 4 = 1], [sin] increases
    to the left and decreases to the right, so between [a] and [b] it is
    at least the smaller of [sin a] and [sin b]. *)
Lemma sn_max :
  forall j a r b, (j mod 4 = 1)%Z ->
  (IZR j - 2) * (PI / 2) <= a -> a <= r -> r <= b -> b <= (IZR j + 2) * (PI / 2) ->
  Rmin (sin a) (sin b) <= sin r.
Proof.
intros j a r b Hj Ha Har Hrb Hb.
destruct (Rle_or_lt r (IZR j * (PI / 2))) as [H|H].
- apply Rle_trans with (sin a); [apply Rmin_l|].
  apply (sn_inc (j - 2)); [exact (sn_mod_sub j 1 2 Hj) | rewrite minus_IZR; exact Ha |
    exact Har | rewrite minus_IZR; lra].
- apply Rle_trans with (sin b); [apply Rmin_r|].
  apply (sn_dec j); [exact Hj | lra | exact Hrb | exact Hb].
Qed.

(** Around the minimum at [j * (PI / 2)], [j mod 4 = 3], likewise. *)
Lemma sn_min :
  forall j a r b, (j mod 4 = 3)%Z ->
  (IZR j - 2) * (PI / 2) <= a -> a <= r -> r <= b -> b <= (IZR j + 2) * (PI / 2) ->
  sin r <= Rmax (sin a) (sin b).
Proof.
intros j a r b Hj Ha Har Hrb Hb.
destruct (Rle_or_lt r (IZR j * (PI / 2))) as [H|H].
- apply Rle_trans with (sin a); [|apply Rmax_l].
  apply (sn_dec (j - 2)); [exact (sn_mod_sub j 3 2 Hj) | rewrite minus_IZR; exact Ha |
    exact Har | rewrite minus_IZR; lra].
- apply Rle_trans with (sin b); [|apply Rmax_r].
  apply (sn_inc j); [exact Hj | lra | exact Hrb | exact Hb].
Qed.

(** ** Intervals *)

Lemma sn_le :
  forall x, finite_itv x -> B2R (Interval.inf_raw x) <= B2R (Interval.sup_raw x).
Proof.
intros x Hfx. pose proof Hfx as (Hx & Hn & _ & _).
destruct (nonempty_mem x Hx Hn) as (r & Hr).
apply (finite_itv_mem x r Hfx) in Hr. lra.
Qed.

Lemma sn_mem_between : forall x r s t, mem r x -> mem t x -> r <= s <= t -> mem s x.
Proof.
intros x r s t [H0 _] [_ H3] Hs. split.
- revert H0. destruct (opp (fst (rep x))); intros H0; try exact H0; lra.
- revert H3. destruct (snd (rep x)); intros H3; try exact H3; lra.
Qed.

(** An unbounded interval holds two reals [2 * PI] apart. *)
Lemma sn_unbounded_wide :
  forall x, valid x -> Interval.is_empty x = false ->
  Interval.inf_raw x = B754_infinity true \/ Interval.sup_raw x = B754_infinity false ->
  exists r t, mem r x /\ mem t x /\ 2 * PI <= t - r.
Proof.
intros x Hx Hn Hinf. destruct (nonempty_mem x Hx Hn) as (r0 & Hr0).
pose proof PI_RGT_0 as HPI.
destruct Hinf as [Ea|Eb].
- exists (r0 - 2 * PI), r0. split; [|split; [exact Hr0 | lra]].
  apply (mono_mem_dn x r0); [exact Hr0 | exact Ea | lra].
- exists r0, (r0 + 2 * PI). split; [exact Hr0|]. split; [|lra].
  apply (mono_mem_up x r0); [exact Hr0 | exact Eb | lra].
Qed.

(** [qa] and [qb] give [qa <= qb]: [qa * (PI / 2) <= a <= b <
    (qb + 1) * (PI / 2)]. *)
Lemma sn_k_le :
  forall x ka kb, finite_itv x ->
  IZR ka * (PI / 2) <= B2R (Interval.inf_raw x) ->
  B2R (Interval.sup_raw x) < (IZR kb + 1) * (PI / 2) -> (ka <= kb)%Z.
Proof.
intros x ka kb Hfx Ha Hb. pose proof (sn_le x Hfx) as Hab.
assert (Hc : 0 < PI / 2) by (pose proof PI_RGT_0; lra).
assert (H : IZR ka < IZR (kb + 1)).
{ rewrite plus_IZR. apply (Rmult_lt_reg_r (PI / 2)); [exact Hc | lra]. }
apply lt_IZR in H. lia.
Qed.

(** An [x] in at most four quarters from [ka] holds no two reals [2 * PI]
    apart. *)
Lemma sn_not_wide :
  forall x ka, finite_itv x -> IZR ka * (PI / 2) <= B2R (Interval.inf_raw x) ->
  B2R (Interval.sup_raw x) < (IZR ka + 4) * (PI / 2) ->
  ~ (exists r t, mem r x /\ mem t x /\ 2 * PI <= t - r).
Proof.
intros x ka Hfx Ha Hb (r & t & Hr & Ht & Hrt).
apply (finite_itv_mem x r Hfx) in Hr. apply (finite_itv_mem x t Hfx) in Ht. lra.
Qed.

(** ** The forms of the result *)

Lemma sn_full_encl :
  forall x,
  encloses (image_dom real_dom sin x) (Interval.const_interval (opp (of_u64 1)) (of_u64 1)).
Proof.
intros x. apply br_full_encl. intros r _ _. apply SIN_bound.
Qed.

Lemma sn_full_pts :
  forall x j1 j3, (j1 mod 4 = 1)%Z -> (j3 mod 4 = 3)%Z ->
  mem (IZR j1 * (PI / 2)) x -> mem (IZR j3 * (PI / 2)) x ->
  is_tightest (image_dom real_dom sin x) (Interval.const_interval (opp (of_u64 1)) (of_u64 1)).
Proof.
intros x j1 j3 H1 H3 M1 M3. apply br_full_tight.
- intros r _ _. apply SIN_bound.
- exists (IZR j1 * (PI / 2)), (IZR j3 * (PI / 2)).
  split; [exact M1|]. split; [exact I|]. split; [exact (sin_kPI2_1 j1 H1)|].
  split; [exact M3|]. split; [exact I|]. exact (sin_kPI2_3 j3 H3).
Qed.

Lemma sn_full_wide :
  forall x, (exists r t, mem r x /\ mem t x /\ 2 * PI <= t - r) ->
  is_tightest (image_dom real_dom sin x) (Interval.const_interval (opp (of_u64 1)) (of_u64 1)).
Proof.
intros x (r0 & t0 & Hr0 & Ht0 & Hw).
assert (H2 : r0 + 2 * PI <= t0) by lra.
destruct (sin_wide r0 t0 H2) as (r & t & Hr & Ht & Er & Et).
apply br_full_tight.
- intros u _ _. apply SIN_bound.
- exists r, t. split; [exact (sn_mem_between x r0 r t0 Hr0 Ht0 Hr)|].
  split; [exact I|]. split; [exact Er|].
  split; [exact (sn_mem_between x r0 t t0 Hr0 Ht0 Ht)|]. split; [exact I | exact Et].
Qed.

Section SnForms.

Variables (emin emax : Z) (m : mpfr).

Hypothesis Hrange : range_ok emin emax.
Hypothesis Hget : get_d_ok emin emax m.
Hypothesis Hs : sin_ok emin emax m.

(** Where [sin] increases on [x], [[sin_rd(a), sin_ru(b)]]. *)
Lemma sn_inc_form :
  forall x j, finite_itv x -> (j mod 4 = 3)%Z ->
  IZR j * (PI / 2) <= B2R (Interval.inf_raw x) ->
  B2R (Interval.sup_raw x) <= (IZR j + 2) * (PI / 2) ->
  encloses (image_dom real_dom sin x)
    (Interval.with_infsup_raw (sin_rd m (Interval.inf_raw x)) (sin_ru m (Interval.sup_raw x))) /\
  is_tightest (image_dom real_dom sin x)
    (Interval.with_infsup_raw (sin_rd m (Interval.inf_raw x)) (sin_ru m (Interval.sup_raw x))).
Proof using Hrange Hget Hs.
intros x j Hfx Hj Ha Hb. pose proof (sn_le x Hfx) as Hab.
assert (Hm : forall r t, mem r x -> mem t x -> r <= t -> sin r <= sin t).
{ intros r t Hr Ht Hrt.
  apply (finite_itv_mem x r Hfx) in Hr. apply (finite_itv_mem x t Hfx) in Ht.
  apply (sn_inc j); [exact Hj | lra | exact Hrt | lra]. }
assert (Ma : mem (B2R (Interval.inf_raw x)) x) by (apply (finite_itv_mem x _ Hfx); lra).
assert (Mb : mem (B2R (Interval.sup_raw x)) x) by (apply (finite_itv_mem x _ Hfx); lra).
unfold sin_rd, sin_ru. split.
- apply (br_inc_encl emin emax m real_dom sin (mpfr_sin m) Hrange Hget Hs x Hfx I I).
  intros r Hr _. pose proof (proj1 (finite_itv_mem x r Hfx) Hr) as Hr'.
  split; apply Hm; first [exact Ma | exact Mb | exact Hr | lra].
- apply (br_inc_tight emin emax m real_dom sin (mpfr_sin m) Hrange Hget Hs x Hfx).
  + intros r _. exact I.
  + exact Hm.
Qed.

(** Where [sin] decreases on [x], [[sin_rd(b), sin_ru(a)]]. *)
Lemma sn_dec_form :
  forall x j, finite_itv x -> (j mod 4 = 1)%Z ->
  IZR j * (PI / 2) <= B2R (Interval.inf_raw x) ->
  B2R (Interval.sup_raw x) <= (IZR j + 2) * (PI / 2) ->
  encloses (image_dom real_dom sin x)
    (Interval.with_infsup_raw (sin_rd m (Interval.sup_raw x)) (sin_ru m (Interval.inf_raw x))) /\
  is_tightest (image_dom real_dom sin x)
    (Interval.with_infsup_raw (sin_rd m (Interval.sup_raw x)) (sin_ru m (Interval.inf_raw x))).
Proof using Hrange Hget Hs.
intros x j Hfx Hj Ha Hb. pose proof (sn_le x Hfx) as Hab.
assert (Hm : forall r t, mem r x -> mem t x -> r <= t -> sin t <= sin r).
{ intros r t Hr Ht Hrt.
  apply (finite_itv_mem x r Hfx) in Hr. apply (finite_itv_mem x t Hfx) in Ht.
  apply (sn_dec j); [exact Hj | lra | exact Hrt | lra]. }
assert (Ma : mem (B2R (Interval.inf_raw x)) x) by (apply (finite_itv_mem x _ Hfx); lra).
assert (Mb : mem (B2R (Interval.sup_raw x)) x) by (apply (finite_itv_mem x _ Hfx); lra).
unfold sin_rd, sin_ru. split.
- apply (br_dec_encl emin emax m real_dom sin (mpfr_sin m) Hrange Hget Hs x Hfx I I).
  intros r Hr _. pose proof (proj1 (finite_itv_mem x r Hfx) Hr) as Hr'.
  split; apply Hm; first [exact Ma | exact Mb | exact Hr | lra].
- apply (br_dec_tight emin emax m real_dom sin (mpfr_sin m) Hrange Hget Hs x Hfx).
  + intros r _. exact I.
  + exact Hm.
Qed.

(** For a single real, both monotone forms. *)
Lemma sn_one_form :
  forall x, finite_itv x -> B2R (Interval.inf_raw x) = B2R (Interval.sup_raw x) ->
  (encloses (image_dom real_dom sin x)
     (Interval.with_infsup_raw (sin_rd m (Interval.inf_raw x)) (sin_ru m (Interval.sup_raw x))) /\
   is_tightest (image_dom real_dom sin x)
     (Interval.with_infsup_raw (sin_rd m (Interval.inf_raw x)) (sin_ru m (Interval.sup_raw x)))) /\
  (encloses (image_dom real_dom sin x)
     (Interval.with_infsup_raw (sin_rd m (Interval.sup_raw x)) (sin_ru m (Interval.inf_raw x))) /\
   is_tightest (image_dom real_dom sin x)
     (Interval.with_infsup_raw (sin_rd m (Interval.sup_raw x)) (sin_ru m (Interval.inf_raw x)))).
Proof using Hrange Hget Hs.
intros x Hfx EAB.
assert (Hone : forall r, mem r x -> r = B2R (Interval.inf_raw x)).
{ intros r Hr. apply (finite_itv_mem x r Hfx) in Hr. lra. }
assert (Hm : forall r t, mem r x -> mem t x -> sin r = sin t).
{ intros r t Hr Ht. rewrite (Hone r Hr), (Hone t Ht). reflexivity. }
unfold sin_rd, sin_ru. split; split.
- apply (br_inc_encl emin emax m real_dom sin (mpfr_sin m) Hrange Hget Hs x Hfx I I).
  intros r Hr _. rewrite (Hone r Hr), <- EAB. split; apply Rle_refl.
- apply (br_inc_tight emin emax m real_dom sin (mpfr_sin m) Hrange Hget Hs x Hfx).
  + intros r _. exact I.
  + intros r t Hr Ht _. rewrite (Hm r t Hr Ht). apply Rle_refl.
- apply (br_dec_encl emin emax m real_dom sin (mpfr_sin m) Hrange Hget Hs x Hfx I I).
  intros r Hr _. rewrite (Hone r Hr), <- EAB. split; apply Rle_refl.
- apply (br_dec_tight emin emax m real_dom sin (mpfr_sin m) Hrange Hget Hs x Hfx).
  + intros r _. exact I.
  + intros r t Hr Ht _. rewrite (Hm r t Hr Ht). apply Rle_refl.
Qed.

(** Around the maximum at [j * (PI / 2)], [[min(sin_rd(a), sin_rd(b)), 1]],
    the tightest if [x] holds the maximum. *)
Lemma sn_max_form :
  forall first x j, finite_itv x -> (j mod 4 = 1)%Z ->
  (IZR j - 2) * (PI / 2) <= B2R (Interval.inf_raw x) ->
  B2R (Interval.sup_raw x) <= (IZR j + 2) * (PI / 2) ->
  encloses (image_dom real_dom sin x)
    (Interval.with_infsup_raw
       (fmin first (sin_rd m (Interval.inf_raw x)) (sin_rd m (Interval.sup_raw x)))
       (of_u64 1)) /\
  (B2R (Interval.inf_raw x) <= IZR j * (PI / 2) <= B2R (Interval.sup_raw x) ->
   is_tightest (image_dom real_dom sin x)
     (Interval.with_infsup_raw
        (fmin first (sin_rd m (Interval.inf_raw x)) (sin_rd m (Interval.sup_raw x)))
        (of_u64 1))).
Proof using Hrange Hget Hs.
intros first x j Hfx Hj Ha Hb.
assert (Hm : forall r, mem r x ->
  Rmin (sin (B2R (Interval.inf_raw x))) (sin (B2R (Interval.sup_raw x))) <= sin r <= 1).
{ intros r Hr. apply (finite_itv_mem x r Hfx) in Hr. split; [|apply SIN_bound].
  apply (sn_max j); [exact Hj | exact Ha | lra | lra | exact Hb]. }
unfold sin_rd. split.
- apply (br_max_encl emin emax m real_dom sin (mpfr_sin m) Hrange Hget Hs first x Hfx I I).
  + intros r _ _. apply SIN_bound.
  + intros r Hr _. exact (Hm r Hr).
- intros Hp.
  apply (br_max_tight emin emax m real_dom sin (mpfr_sin m) Hrange Hget Hs first x Hfx).
  + intros r _. exact I.
  + intros r _. apply SIN_bound.
  + exact Hm.
  + exists (IZR j * (PI / 2)).
    split; [apply (finite_itv_mem x _ Hfx); exact Hp | exact (sin_kPI2_1 j Hj)].
Qed.

(** Around the minimum at [j * (PI / 2)], [[-1, max(sin_ru(a), sin_ru(b))]]. *)
Lemma sn_min_form :
  forall first x j, finite_itv x -> (j mod 4 = 3)%Z ->
  (IZR j - 2) * (PI / 2) <= B2R (Interval.inf_raw x) ->
  B2R (Interval.sup_raw x) <= (IZR j + 2) * (PI / 2) ->
  encloses (image_dom real_dom sin x)
    (Interval.with_infsup_raw (opp (of_u64 1))
       (fmax first (sin_ru m (Interval.inf_raw x)) (sin_ru m (Interval.sup_raw x)))) /\
  (B2R (Interval.inf_raw x) <= IZR j * (PI / 2) <= B2R (Interval.sup_raw x) ->
   is_tightest (image_dom real_dom sin x)
     (Interval.with_infsup_raw (opp (of_u64 1))
        (fmax first (sin_ru m (Interval.inf_raw x)) (sin_ru m (Interval.sup_raw x))))).
Proof using Hrange Hget Hs.
intros first x j Hfx Hj Ha Hb.
assert (Hm : forall r, mem r x ->
  -1 <= sin r <= Rmax (sin (B2R (Interval.inf_raw x))) (sin (B2R (Interval.sup_raw x)))).
{ intros r Hr. apply (finite_itv_mem x r Hfx) in Hr. split; [apply SIN_bound|].
  apply (sn_min j); [exact Hj | exact Ha | lra | lra | exact Hb]. }
unfold sin_ru. split.
- apply (br_min_encl emin emax m real_dom sin (mpfr_sin m) Hrange Hget Hs first x Hfx I I).
  + intros r _ _. apply SIN_bound.
  + intros r Hr _. exact (Hm r Hr).
- intros Hp.
  apply (br_min_tight emin emax m real_dom sin (mpfr_sin m) Hrange Hget Hs first x Hfx).
  + intros r _. exact I.
  + intros r _. apply SIN_bound.
  + exact Hm.
  + exists (IZR j * (PI / 2)).
    split; [apply (finite_itv_mem x _ Hfx); exact Hp | exact (sin_kPI2_3 j Hj)].
Qed.

(** ** The branches

    The tests of [Interval::sin], with [t_i] for [q == i] and [l_j] for
    [n < j]. *)

(** A single real: [n] is 0, so every [n < j] holds, and the branch is
    monotone. *)
Lemma sn_single :
  forall first x ka (t0 t1 t2 t3 l1 l2 l3 l4 : bool), finite_itv x ->
  B2R (Interval.inf_raw x) = B2R (Interval.sup_raw x) ->
  t0 = (ka mod 4 =? 0)%Z -> t1 = (ka mod 4 =? 1)%Z ->
  t2 = (ka mod 4 =? 2)%Z -> t3 = (ka mod 4 =? 3)%Z ->
  l1 = true -> l2 = true -> l3 = true -> l4 = true ->
  exists y,
    (if t0 && l1 || t3 && l2 then
       Some (Interval.with_infsup_raw (sin_rd m (Interval.inf_raw x))
               (sin_ru m (Interval.sup_raw x)))
     else if t1 && l2 || t2 && l1 then
       Some (Interval.with_infsup_raw (sin_rd m (Interval.sup_raw x))
               (sin_ru m (Interval.inf_raw x)))
     else if t0 && l3 || t3 && l4 then
       Some (Interval.with_infsup_raw
               (fmin first (sin_rd m (Interval.inf_raw x)) (sin_rd m (Interval.sup_raw x)))
               (of_u64 1))
     else if t1 && l4 || t2 && l3 then
       Some (Interval.with_infsup_raw (opp (of_u64 1))
               (fmax first (sin_ru m (Interval.inf_raw x)) (sin_ru m (Interval.sup_raw x))))
     else Some (Interval.const_interval (opp (of_u64 1)) (of_u64 1))) = Some y /\
    encloses (image_dom real_dom sin x) y /\ is_tightest (image_dom real_dom sin x) y.
Proof using Hrange Hget Hs.
intros first x ka t0 t1 t2 t3 l1 l2 l3 l4 Hfx EAB Ht0 Ht1 Ht2 Ht3 -> -> -> ->.
assert (Hq : (ka mod 4 = 0 \/ ka mod 4 = 1 \/ ka mod 4 = 2 \/ ka mod 4 = 3)%Z)
  by (pose proof (Z.mod_pos_bound ka 4); lia).
destruct (sn_one_form x Hfx EAB) as [[Hie Hit] [Hde Hdt]].
destruct Hq as [Hq|[Hq|[Hq|Hq]]]; rewrite Hq in Ht0, Ht1, Ht2, Ht3;
  cbn in Ht0, Ht1, Ht2, Ht3; subst t0 t1 t2 t3; cbn [andb orb];
  (eexists; split; [reflexivity|]); split; assumption.
Qed.

(** Bounds that are not equal: [qa] = [ka], [qb] = [kb], and [n] is
    [kb - ka]. Every branch encloses the image of [x], which lies in
    [[ka * (PI / 2), (kb + 1) * (PI / 2))]; it is the tightest if [x]
    holds two reals [2 * PI] apart, or if [ka] and [kb] are the exact
    floors of [a / (PI / 2)] and [b / (PI / 2)], so that [x] holds every
    [j * (PI / 2)] for [ka < j <= kb]. *)
Lemma sn_pick :
  forall first x ka kb (t0 t1 t2 t3 l1 l2 l3 l4 : bool), finite_itv x ->
  IZR ka * (PI / 2) <= B2R (Interval.inf_raw x) ->
  B2R (Interval.sup_raw x) < (IZR kb + 1) * (PI / 2) ->
  t0 = (ka mod 4 =? 0)%Z -> t1 = (ka mod 4 =? 1)%Z ->
  t2 = (ka mod 4 =? 2)%Z -> t3 = (ka mod 4 =? 3)%Z ->
  l1 = (kb - ka <? 1)%Z -> l2 = (kb - ka <? 2)%Z ->
  l3 = (kb - ka <? 3)%Z -> l4 = (kb - ka <? 4)%Z ->
  exists y,
    (if t0 && l1 || t3 && l2 then
       Some (Interval.with_infsup_raw (sin_rd m (Interval.inf_raw x))
               (sin_ru m (Interval.sup_raw x)))
     else if t1 && l2 || t2 && l1 then
       Some (Interval.with_infsup_raw (sin_rd m (Interval.sup_raw x))
               (sin_ru m (Interval.inf_raw x)))
     else if t0 && l3 || t3 && l4 then
       Some (Interval.with_infsup_raw
               (fmin first (sin_rd m (Interval.inf_raw x)) (sin_rd m (Interval.sup_raw x)))
               (of_u64 1))
     else if t1 && l4 || t2 && l3 then
       Some (Interval.with_infsup_raw (opp (of_u64 1))
               (fmax first (sin_ru m (Interval.inf_raw x)) (sin_ru m (Interval.sup_raw x))))
     else Some (Interval.const_interval (opp (of_u64 1)) (of_u64 1))) = Some y /\
    encloses (image_dom real_dom sin x) y /\
    ((B2R (Interval.inf_raw x) < (IZR ka + 1) * (PI / 2) /\
      IZR kb * (PI / 2) <= B2R (Interval.sup_raw x)) \/
     (exists r t, mem r x /\ mem t x /\ 2 * PI <= t - r) ->
     is_tightest (image_dom real_dom sin x) y).
Proof using Hrange Hget Hs.
intros first x ka kb t0 t1 t2 t3 l1 l2 l3 l4 Hfx Ha Hb Ht0 Ht1 Ht2 Ht3 Hl1 Hl2 Hl3 Hl4.
assert (Hc : 0 < PI / 2) by (pose proof PI_RGT_0; lra).
pose proof (sn_le x Hfx) as Hab.
pose proof (sn_k_le x ka kb Hfx Ha Hb) as Hk.
assert (Hq : (ka mod 4 = 0 \/ ka mod 4 = 1 \/ ka mod 4 = 2 \/ ka mod 4 = 3)%Z)
  by (pose proof (Z.mod_pos_bound ka 4); lia).
destruct (Z_lt_le_dec (kb - ka) 4) as [HD4|HD4].
- (* [kb - ka] is 0 to 3: [x] is narrower than [2 * PI]. *)
  assert (HD : (kb - ka = 0 \/ kb - ka = 1 \/ kb - ka = 2 \/ kb - ka = 3)%Z) by lia.
  assert (Hnw : ~ (exists r t, mem r x /\ mem t x /\ 2 * PI <= t - r)).
  { apply (sn_not_wide x ka Hfx Ha).
    assert (H3 : IZR kb <= IZR ka + 3) by (rewrite <- plus_IZR; apply IZR_le; lia).
    apply Rlt_le_trans with (1 := Hb). apply Rmult_le_compat_r; lra. }
  destruct HD as [HD|[HD|[HD|HD]]];
    (assert (Ekb : IZR kb = IZR ka + IZR (kb - ka))
       by (rewrite <- plus_IZR; f_equal; lia));
    rewrite HD in Ekb, Hl1, Hl2, Hl3, Hl4; rewrite Ekb in Hb |- *;
    cbn in Hl1, Hl2, Hl3, Hl4; subst l1 l2 l3 l4;
    (destruct Hq as [Hq|[Hq|[Hq|Hq]]]; rewrite Hq in Ht0, Ht1, Ht2, Ht3;
     cbn in Ht0, Ht1, Ht2, Ht3; subst t0 t1 t2 t3; cbn [andb orb];
     (eexists; split; [reflexivity|])).
  (* [kb = ka] *)
  + (* quarter 0: increasing *)
    destruct (sn_inc_form x (ka - 1) Hfx (sn_mod_sub _ _ 1 Hq)
      ltac:(rewrite minus_IZR; lra) ltac:(rewrite minus_IZR; lra)) as [He Ht].
    split; [exact He | intros _; exact Ht].
  + (* quarter 1: decreasing *)
    destruct (sn_dec_form x ka Hfx Hq ltac:(lra) ltac:(lra)) as [He Ht].
    split; [exact He | intros _; exact Ht].
  + (* quarter 2: decreasing *)
    destruct (sn_dec_form x (ka - 1) Hfx (sn_mod_sub _ _ 1 Hq)
      ltac:(rewrite minus_IZR; lra) ltac:(rewrite minus_IZR; lra)) as [He Ht].
    split; [exact He | intros _; exact Ht].
  + (* quarter 3: increasing *)
    destruct (sn_inc_form x ka Hfx Hq ltac:(lra) ltac:(lra)) as [He Ht].
    split; [exact He | intros _; exact Ht].
  (* [kb = ka + 1] *)
  + (* quarters 0, 1: maximum at [(ka + 1) * (PI / 2)] *)
    destruct (sn_max_form first x (ka + 1) Hfx (sn_mod_add _ _ 1 Hq)
      ltac:(rewrite plus_IZR; lra) ltac:(rewrite plus_IZR; lra)) as [He Ht].
    split; [exact He|]. intros [HE|Hw]; [|contradiction].
    apply Ht. rewrite plus_IZR. split; lra.
  + (* quarters 1, 2: decreasing *)
    destruct (sn_dec_form x ka Hfx Hq ltac:(lra) ltac:(lra)) as [He Ht].
    split; [exact He | intros _; exact Ht].
  + (* quarters 2, 3: minimum at [(ka + 1) * (PI / 2)] *)
    destruct (sn_min_form first x (ka + 1) Hfx (sn_mod_add _ _ 1 Hq)
      ltac:(rewrite plus_IZR; lra) ltac:(rewrite plus_IZR; lra)) as [He Ht].
    split; [exact He|]. intros [HE|Hw]; [|contradiction].
    apply Ht. rewrite plus_IZR. split; lra.
  + (* quarters 3, 0: increasing *)
    destruct (sn_inc_form x ka Hfx Hq ltac:(lra) ltac:(lra)) as [He Ht].
    split; [exact He | intros _; exact Ht].
  (* [kb = ka + 2] *)
  + (* quarters 0 to 2: maximum at [(ka + 1) * (PI / 2)] *)
    destruct (sn_max_form first x (ka + 1) Hfx (sn_mod_add _ _ 1 Hq)
      ltac:(rewrite plus_IZR; lra) ltac:(rewrite plus_IZR; lra)) as [He Ht].
    split; [exact He|]. intros [HE|Hw]; [|contradiction].
    apply Ht. rewrite plus_IZR. split; lra.
  + (* quarters 1 to 3: minimum at [(ka + 2) * (PI / 2)] *)
    destruct (sn_min_form first x (ka + 2) Hfx (sn_mod_add _ _ 2 Hq)
      ltac:(rewrite plus_IZR; lra) ltac:(rewrite plus_IZR; lra)) as [He Ht].
    split; [exact He|]. intros [HE|Hw]; [|contradiction].
    apply Ht. rewrite plus_IZR. split; lra.
  + (* quarters 2, 3, 0: minimum at [(ka + 1) * (PI / 2)] *)
    destruct (sn_min_form first x (ka + 1) Hfx (sn_mod_add _ _ 1 Hq)
      ltac:(rewrite plus_IZR; lra) ltac:(rewrite plus_IZR; lra)) as [He Ht].
    split; [exact He|]. intros [HE|Hw]; [|contradiction].
    apply Ht. rewrite plus_IZR. split; lra.
  + (* quarters 3, 0, 1: maximum at [(ka + 2) * (PI / 2)] *)
    destruct (sn_max_form first x (ka + 2) Hfx (sn_mod_add _ _ 2 Hq)
      ltac:(rewrite plus_IZR; lra) ltac:(rewrite plus_IZR; lra)) as [He Ht].
    split; [exact He|]. intros [HE|Hw]; [|contradiction].
    apply Ht. rewrite plus_IZR. split; lra.
  (* [kb = ka + 3] *)
  + (* quarters 0 to 3: both extrema *)
    split; [apply sn_full_encl|]. intros [[HA HB]|Hw]; [|contradiction].
    apply (sn_full_pts x (ka + 1) (ka + 3) (sn_mod_add _ _ 1 Hq) (sn_mod_add _ _ 3 Hq));
      apply (finite_itv_mem x _ Hfx); rewrite plus_IZR; split; lra.
  + (* quarters 1 to 0: minimum at [(ka + 2) * (PI / 2)] *)
    destruct (sn_min_form first x (ka + 2) Hfx (sn_mod_add _ _ 2 Hq)
      ltac:(rewrite plus_IZR; lra) ltac:(rewrite plus_IZR; lra)) as [He Ht].
    split; [exact He|]. intros [HE|Hw]; [|contradiction].
    apply Ht. rewrite plus_IZR. split; lra.
  + (* quarters 2 to 1: both extrema *)
    split; [apply sn_full_encl|]. intros [[HA HB]|Hw]; [|contradiction].
    apply (sn_full_pts x (ka + 3) (ka + 1) (sn_mod_add _ _ 3 Hq) (sn_mod_add _ _ 1 Hq));
      apply (finite_itv_mem x _ Hfx); rewrite plus_IZR; split; lra.
  + (* quarters 3 to 2: maximum at [(ka + 2) * (PI / 2)] *)
    destruct (sn_max_form first x (ka + 2) Hfx (sn_mod_add _ _ 2 Hq)
      ltac:(rewrite plus_IZR; lra) ltac:(rewrite plus_IZR; lra)) as [He Ht].
    split; [exact He|]. intros [HE|Hw]; [|contradiction].
    apply Ht. rewrite plus_IZR. split; lra.
- (* [kb - ka >= 4]: every test fails, and [[-1, 1]] is the result. *)
  assert (E1 : l1 = false) by (rewrite Hl1; apply Z.ltb_ge; lia).
  assert (E2 : l2 = false) by (rewrite Hl2; apply Z.ltb_ge; lia).
  assert (E3 : l3 = false) by (rewrite Hl3; apply Z.ltb_ge; lia).
  assert (E4 : l4 = false) by (rewrite Hl4; apply Z.ltb_ge; lia).
  rewrite E1, E2, E3, E4, !Bool.andb_false_r. cbn [orb].
  eexists. split; [reflexivity|]. split; [apply sn_full_encl|].
  intros [[HA HB]|Hw]; [|exact (sn_full_wide x Hw)].
  (* With the exact floors, [x] holds [j * (PI / 2)] for
     [ka < j <= ka + 4]. *)
  assert (H4 : (IZR ka + 4) * (PI / 2) <= IZR kb * (PI / 2)).
  { apply Rmult_le_compat_r; [lra|]. rewrite <- (plus_IZR ka 4). apply IZR_le. lia. }
  assert (Hj : forall d, (1 <= d <= 4)%Z -> mem (IZR (ka + d) * (PI / 2)) x).
  { intros d Hd. apply (finite_itv_mem x _ Hfx). rewrite plus_IZR.
    assert (Hd1 : 1 * (PI / 2) <= IZR d * (PI / 2))
      by (apply Rmult_le_compat_r; [lra | apply IZR_le; lia]).
    assert (Hd4 : IZR d * (PI / 2) <= 4 * (PI / 2))
      by (apply Rmult_le_compat_r; [lra | apply IZR_le; lia]).
    split; lra. }
  destruct Hq as [Hq|[Hq|[Hq|Hq]]].
  + apply (sn_full_pts x (ka + 1) (ka + 3) (sn_mod_add _ _ 1 Hq) (sn_mod_add _ _ 3 Hq));
      apply Hj; lia.
  + apply (sn_full_pts x (ka + 4) (ka + 2) (sn_mod_add _ _ 4 Hq) (sn_mod_add _ _ 2 Hq));
      apply Hj; lia.
  + apply (sn_full_pts x (ka + 3) (ka + 1) (sn_mod_add _ _ 3 Hq) (sn_mod_add _ _ 1 Hq));
      apply Hj; lia.
  + apply (sn_full_pts x (ka + 2) (ka + 4) (sn_mod_add _ _ 2 Hq) (sn_mod_add _ _ 4 Hq));
      apply Hj; lia.
Qed.

End SnForms.

(** ** The theorems *)

Lemma sn_lt_pinf : forall y, Model.lt (B754_infinity false) y = false.
Proof.
intros [s|s| |s my ey Hy]; [| destruct s | |]; reflexivity.
Qed.

Lemma sn_lt0_1 : Model.lt Model.zero (of_u64 1) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sn_lt0_2 : Model.lt Model.zero (of_u64 2) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sn_lt0_3 : Model.lt Model.zero (of_u64 3) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sn_lt0_4 : Model.lt Model.zero (of_u64 4) = true.
Proof. vm_compute. reflexivity. Qed.

(** An infinite bound makes [n] +inf. *)
Lemma sn_n_inf :
  forall c a b qa qb, red_lo c a qa -> red_hi c b qb ->
  a = B754_infinity true \/ b = B754_infinity false ->
  Model.sub qb qa = B754_infinity false.
Proof.
intros c a b qa qb Hlo Hhi Hab.
assert (Nqa : is_nan qa = false /\ qa <> B754_infinity false).
{ destruct Hlo as [(_ & ->) | (_ & Fqa & _)]; [split; [reflexivity | discriminate]|].
  destruct qa; try discriminate Fqa; split; first [reflexivity | discriminate]. }
assert (Nqb : is_nan qb = false /\ qb <> B754_infinity true).
{ destruct Hhi as [(_ & ->) | (_ & Fqb & _)]; [split; [reflexivity | discriminate]|].
  destruct qb; try discriminate Fqb; split; first [reflexivity | discriminate]. }
apply n_inf; try tauto.
destruct Hab as [Ea|Eb].
- left. destruct Hlo as [(_ & ->) | (Fa & _)]; [reflexivity | rewrite Ea in Fa; discriminate Fa].
- right. destruct Hhi as [(_ & ->) | (Fb & _)]; [reflexivity | rewrite Eb in Fb; discriminate Fb].
Qed.

(** An infinite bound makes [b - a] +inf. *)
Lemma sn_ba_inf :
  forall c a b qa qb, red_lo c a qa -> red_hi c b qb ->
  a = B754_infinity true \/ b = B754_infinity false ->
  Model.sub b a = B754_infinity false.
Proof.
intros c a b qa qb Hlo Hhi Hab.
assert (Na : is_nan a = false /\ a <> B754_infinity false).
{ destruct Hlo as [(-> & _) | (Fa & _)]; [split; [reflexivity | discriminate]|].
  destruct a; try discriminate Fa; split; first [reflexivity | discriminate]. }
assert (Nb : is_nan b = false /\ b <> B754_infinity true).
{ destruct Hhi as [(-> & _) | (Fb & _)]; [split; [reflexivity | discriminate]|].
  destruct b; try discriminate Fb; split; first [reflexivity | discriminate]. }
apply n_inf; tauto.
Qed.

Lemma sn_eq00 : Model.eq Model.zero Model.zero = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sn_le8_pinf : Model.le (of_u64 8) (B754_infinity false) = true.
Proof. vm_compute. reflexivity. Qed.

(** [2 * PI <= 8 - 1], for [trig_wide] with [w = 8]. *)
Lemma sn_2PI_7 : 2 * PI <= IZR 8 - 1.
Proof.
destruct PI_bounds as [_ H].
let v := eval vm_compute in (Interval.sup_raw Interval.PI) in
change (Interval.sup_raw Interval.PI) with v in H.
unfold B2R, F2R in H. cbn [Fnum Fexp bpow radix_val radix2 cond_Zopp] in H. lra.
Qed.

(** The tests of the quadrant [quad_f (k mod 4)] that [quadrants] returns
    are those of [k mod 4]. *)
Lemma sn_quad_tests :
  forall k,
  Model.eq (quad_f (k mod 4)) Model.zero = (k mod 4 =? 0)%Z /\
  Model.eq (quad_f (k mod 4)) (of_u64 1) = (k mod 4 =? 1)%Z /\
  Model.eq (quad_f (k mod 4)) (of_u64 2) = (k mod 4 =? 2)%Z /\
  Model.eq (quad_f (k mod 4)) (of_u64 3) = (k mod 4 =? 3)%Z.
Proof.
intros k.
assert (Hq : (k mod 4 = 0 \/ k mod 4 = 1 \/ k mod 4 = 2 \/ k mod 4 = 3)%Z)
  by (pose proof (Z.mod_pos_bound k 4); lia).
destruct Hq as [Hq|[Hq|[Hq|Hq]]]; rewrite Hq; vm_compute; repeat split.
Qed.

(** The count that [quadrants] returns is [kb - ka] when that is below 4,
    and at least 4 otherwise, so its tests [n < j] for [j <= 4] are those
    of [kb - ka]. *)
Lemma sn_count_tests :
  forall ka kb j, (ka <= kb)%Z -> (1 <= j <= 4)%Z ->
  Model.lt (count_f (ka mod 4) (kb mod 4) (4 <=? kb - ka)%Z) (of_u64 j) = (kb - ka <? j)%Z.
Proof.
intros ka kb j Hk Hj.
destruct (count_f_val (ka mod 4) (kb mod 4) (4 <=? kb - ka)%Z) as (Fn & Rn);
  [pose proof (Z.mod_pos_bound ka 4); lia | pose proof (Z.mod_pos_bound kb 4); lia |].
destruct (int_tests _ _ Fn Rn) as (_ & Ht).
rewrite (proj1 (Ht j Hj)), <- Zminus_mod.
pose proof (Z.mod_pos_bound (kb - ka) 4 ltac:(lia)) as Hm.
destruct (Z.leb_spec 4 (kb - ka)) as [H4|H4]; cbv beta iota.
- apply Bool.eq_true_iff_eq. rewrite !Z.ltb_lt. split; intros; lia.
- rewrite Z.add_0_r, Z.mod_small by lia. reflexivity.
Qed.

(** The result is the tightest for every [x]: the [(q, n)] that the
    branches test come from exact floors of [a / (PI / 2)] and
    [b / (PI / 2)] ([floors_exact_ok] in [TrigCert.v], or [n = 0]), from
    the quadrants ([quadrants_correct] in [TrigCount.v]), or [x] is a
    singleton, or at least [2 * PI] wide ([trig_wide]), or unbounded. *)
Lemma sn_main :
  forall emin emax m has_fma first x,
  range_ok emin emax -> get_d_ok emin emax m -> sin_ok emin emax m -> cos_ok emin emax m ->
  valid x ->
  exists y, Interval.sin m has_fma first x = Some y /\
    is_tightest (image_dom real_dom sin x) y.
Proof.
intros emin emax m has_fma first x Hrange Hget Hs Hc Hx.
unfold Interval.sin.
destruct (Interval.is_empty x) eqn:Hn.
{ (* An empty interval has an empty image. *)
  exists x. split; [reflexivity|].
  rewrite (valid_empty_eq x Hx Hn). apply tightest_empty.
  intros u (r & Hr & _). exact (mem_nan Interval.EMPTY r eq_refl Hr). }
assert (HPI2 : 0 < PI / 2) by (pose proof PI_RGT_0; lra).
destruct (trig_reduce has_fma Interval.FRAC_PI_2 (PI / 2) x FRAC_PI_2_const Hx Hn)
  as (z & Hz & Hlo & Hhi).
cbv beta iota zeta. rewrite Hz. cbv beta iota zeta.
set (qa := Interval.inf_raw (Interval.floor z)) in *.
set (qb := Interval.sup_raw (Interval.floor z)) in *.
clearbody qa qb.
assert (Hfin :
  (is_finite (Interval.inf_raw x) = true /\ is_finite (Interval.sup_raw x) = true) \/
  (Interval.inf_raw x = B754_infinity true \/ Interval.sup_raw x = B754_infinity false)).
{ destruct Hlo as [(Ea & _)|(Fa & _)], Hhi as [(Eb & _)|(Fb & _)]; tauto. }
destruct Hfin as [(Fa & Fb) | Hinf].
2: { (* An infinite bound: [n] and [b - a] are +inf, so the fast [(q, n)]
        are kept, every test fails, and [x] holds two reals [2 * PI]
        apart. *)
  assert (Eab : Model.eq (Interval.inf_raw x) (Interval.sup_raw x) = false).
  { destruct (Model.eq _ _) eqn:E; [|reflexivity].
    destruct (bounds_eq_finite x Hx Hn E) as (Fa & Fb & _).
    destruct Hinf as [Ea|Eb]; [rewrite Ea in Fa | rewrite Eb in Fb]; discriminate. }
  rewrite Eab. cbv beta iota.
  rewrite (sn_n_inf _ _ _ _ _ Hlo Hhi Hinf), (sn_ba_inf _ _ _ _ _ Hlo Hhi Hinf), sn_le8_pinf,
    Bool.orb_true_r.
  cbv beta iota.
  rewrite !sn_lt_pinf, !Bool.andb_false_r. cbn [orb].
  eexists. split; [reflexivity|].
  exact (sn_full_wide x (sn_unbounded_wide x Hx Hn Hinf)). }
destruct Hlo as [(Ea & _) | (_ & Fqa & ka & Eka & Hka & _)];
  [rewrite Ea in Fa; discriminate Fa|].
destruct Hhi as [(Eb & _) | (_ & Fqb & kb & Ekb & Hkb)];
  [rewrite Eb in Fb; discriminate Fb|].
assert (Hfx : finite_itv x) by (split; [exact Hx|]; split; [exact Hn|]; split; assumption).
pose proof (sn_le x Hfx) as Hab.
pose proof (rem_euclid_4_int _ ka Fqa Eka) as Hq. cbv zeta in Hq.
destruct Hq as (Ht0 & Ht1 & Ht2 & Ht3).
destruct (Model.eq (Interval.inf_raw x) (Interval.sup_raw x)) eqn:Eab.
{ (* [a == b]: [n] is 0, so the fast [(q, n)] are kept. *)
  cbv beta iota. rewrite sn_eq00. cbn [orb]. cbv beta iota.
  destruct (bounds_eq_finite x Hx Hn Eab) as (_ & _ & EAB).
  destruct (sn_single emin emax m Hrange Hget Hs first x ka _ _ _ _ _ _ _ _ Hfx EAB
    Ht0 Ht1 Ht2 Ht3 sn_lt0_1 sn_lt0_2 sn_lt0_3 sn_lt0_4) as (y & Ey & _ & Ht).
  exists y. split; [exact Ey | exact Ht]. }
cbv beta iota.
(* [n = qb - qa], whose tests decide [kb - ka]. *)
pose proof (sn_k_le x ka kb Hfx Hka Hkb) as Hk.
pose proof (n_small _ _ ka kb Fqa Fqb Eka Ekb Hk) as Hns. cbv zeta in Hns.
destruct Hns as (Hn0 & Hns).
destruct (Hns 1%Z ltac:(lia)) as (Hl1 & _ & _).
destruct (Hns 2%Z ltac:(lia)) as (Hl2 & _ & _).
destruct (Hns 3%Z ltac:(lia)) as (Hl3 & _ & _).
destruct (Hns 4%Z ltac:(lia)) as (Hl4 & _ & _).
destruct (Model.eq (Model.sub qb qa) Model.zero
          || Model.le (of_u64 8) (Model.sub (Interval.sup_raw x) (Interval.inf_raw x)))
  eqn:Ew.
- (* The fast [(q, n)] are kept: [n = 0] makes [kb = ka], and [b - a >= 8]
     puts two reals [2 * PI] apart in [x]. *)
  cbv beta iota.
  destruct (sn_pick emin emax m Hrange Hget Hs first x ka kb _ _ _ _ _ _ _ _ Hfx Hka Hkb
    Ht0 Ht1 Ht2 Ht3 Hl1 Hl2 Hl3 Hl4) as (y & Ey & _ & Ht).
  exists y. split; [exact Ey|]. apply Ht.
  apply Bool.orb_true_iff in Ew. destruct Ew as [E0|E8].
  + left. rewrite Hn0 in E0. apply Z.eqb_eq in E0.
    assert (E1 : kb = ka) by lia. subst kb. split; lra.
  + right. apply (trig_wide x 8 (2 * PI) Hx Hn); [lia | exact sn_2PI_7 | exact E8].
- cbv beta iota.
  destruct (floors_exact_ok has_fma Interval.FRAC_PI_2 (PI / 2) _ _ qa qb ka kb
    FRAC_PI_2_const Fa Fb Fqa Eka Fqb Ekb) as (e & Ee & He).
  rewrite Ee. cbv beta iota.
  destruct e; cbv beta iota.
  + (* [floors_exact] certifies that [ka] and [kb] are the exact floors. *)
    destruct (sn_pick emin emax m Hrange Hget Hs first x ka kb _ _ _ _ _ _ _ _ Hfx Hka Hkb
      Ht0 Ht1 Ht2 Ht3 Hl1 Hl2 Hl3 Hl4) as (y & Ey & _ & Ht).
    exists y. split; [exact Ey|]. apply Ht. left. exact (He eq_refl).
  + (* The quadrants of [a] and [b] give the tests of the exact floors
       [ka'] and [kb']. *)
    pose proof (floor_div_bounds (PI / 2) (B2R (Interval.inf_raw x)) HPI2) as Ha'.
    pose proof (floor_div_bounds (PI / 2) (B2R (Interval.sup_raw x)) HPI2) as Hb'.
    unfold Rfloor in Ha', Hb'.
    set (ka' := Zfloor (B2R (Interval.inf_raw x) / (PI / 2))) in *.
    set (kb' := Zfloor (B2R (Interval.sup_raw x) / (PI / 2))) in *.
    clearbody ka' kb'.
    rewrite (quadrants_correct emin emax m _ _ ka' kb' Hrange Hget Hs Hc Fa Fb Hab Ha' Hb').
    cbv beta iota.
    assert (Hk' : (ka' <= kb')%Z) by (apply (sn_k_le x ka' kb' Hfx); lra).
    destruct (sn_quad_tests ka') as (Hu0 & Hu1 & Hu2 & Hu3).
    destruct (sn_pick emin emax m Hrange Hget Hs first x ka' kb' _ _ _ _ _ _ _ _ Hfx
      (proj1 Ha') (proj2 Hb') Hu0 Hu1 Hu2 Hu3
      (sn_count_tests ka' kb' 1 Hk' ltac:(lia)) (sn_count_tests ka' kb' 2 Hk' ltac:(lia))
      (sn_count_tests ka' kb' 3 Hk' ltac:(lia)) (sn_count_tests ka' kb' 4 Hk' ltac:(lia)))
      as (y & Ey & _ & Ht).
    exists y. split; [exact Ey|]. apply Ht. left. split; lra.
Qed.

Theorem sin_encloses :
  forall emin emax m has_fma first x,
  range_ok emin emax -> get_d_ok emin emax m -> sin_ok emin emax m -> cos_ok emin emax m ->
  valid x ->
  exists y, Interval.sin m has_fma first x = Some y /\
    encloses (image_dom real_dom sin x) y.
Proof.
intros emin emax m has_fma first x Hrange Hget Hs Hc Hx.
destruct (sn_main emin emax m has_fma first x Hrange Hget Hs Hc Hx) as (y & Ey & (Hy & Hi & _)).
exists y. split; [exact Ey | exact (conj Hy Hi)].
Qed.

Theorem sin_correct :
  forall emin emax m has_fma first x,
  range_ok emin emax -> get_d_ok emin emax m -> sin_ok emin emax m -> cos_ok emin emax m ->
  valid x ->
  exists y, Interval.sin m has_fma first x = Some y /\
    is_tightest (image_dom real_dom sin x) y.
Proof. exact sn_main. Qed.

(** [sin] is defined and continuous everywhere, so the decoration of [x]
    is kept ([e = Com] in [trig_set_dec_correct]); a [com] [x] is
    bounded by [com_common]. *)
Theorem dec_sin_correct :
  forall emin emax m has_fma first x,
  range_ok emin emax -> get_d_ok emin emax m -> sin_ok emin emax m -> cos_ok emin emax m ->
  valid (itv x) -> com_common x ->
  exists y, DecInterval.sin m has_fma first x = Some y /\
    if DecInterval.is_nai x then y = DecInterval.NAI
    else
      is_tightest (image_dom real_dom sin (itv x)) (itv y) /\
      exists d, strongest_dom real_dom d sin (itv x) (itv y) /\
        dec y = dec_min d (dec x).
Proof.
intros emin emax m has_fma first x Hrange Hget Hs Hc Hx Hcc.
destruct (sn_main emin emax m has_fma first (itv x) Hrange Hget Hs Hc Hx) as (y0 & Ey0 & Ht).
assert (He : encloses (image_dom real_dom sin (itv x)) y0)
  by (destruct Ht as (Hy & Hi & _); exact (conj Hy Hi)).
exists (DecInterval.set_dec y0 (dec x)).
split; [unfold DecInterval.sin; rewrite Ey0; reflexivity|].
destruct (DecInterval.is_nai x) eqn:Hnai.
- (* NaI gives NaI. *)
  unfold DecInterval.is_nai in Hnai. unfold DecInterval.set_dec. rewrite Hnai. reflexivity.
- assert (Hdx : dec x <> Ill).
  { intros E. unfold DecInterval.is_nai in Hnai. rewrite E in Hnai. discriminate Hnai. }
  assert (Hemp : (forall r, ~ mem r (itv x)) -> Interval.is_empty y0 = true).
  { intros Hno. destruct (Interval.is_empty (itv x)) eqn:Hn.
    - unfold Interval.sin in Ey0. rewrite Hn in Ey0. injection Ey0 as <-. exact Hn.
    - destruct (nonempty_mem (itv x) Hx Hn) as (r & Hr). destruct (Hno r Hr). }
  pose proof (trig_set_dec_correct real_dom sin x y0 Com Hx Hdx He Hemp
    (fun r _ _ => continuity_pt_continue_in sin real_dom r (continuity_sin r))
    (or_intror (conj eq_refl (conj (fun _ _ => I) (fun Hd _ => common_bounded _ (Hcc Hd))))))
    as H. cbv zeta in H. rewrite dec_min_Com_r in H.
  destruct H as (_ & H2 & _ & H4).
  split; [exact (H2 Ht)|].
  apply H4. intros E. discriminate E.
Qed.
