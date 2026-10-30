(** * What [pow_rd], [pow_ru], [pown_rd] and [pown_ru] return

    The values of the functions that [mpfr_fn2!(pow, pow_rd, pow_ru)] and
    [mpfr_fn_si!(pow_si, pown_rd, pown_ru)] define, as [f64]s, from what
    [Mpfr.v] assumes of MPFR: at finite arguments in the domain, the value
    of the point function rounded once ([pow_fin], [pown_fin], by
    [mpfr_fn_round]), and at the special arguments that [Interval::pow]
    and [Interval::powi] pass, a zero, 1 or an infinity. A result that is
    [r] rounded is stated as [mpfr_round f64_format rnd r (with_val w)],
    the form that [round_up_lane] and [round_dn_lane] take; a zero result
    of either sign is 0 rounded, and 1 is 1 rounded.

    The second part gives the lanes of an interval from a greatest lower
    bound or least upper bound that a float rounds ([pl_lo], [pl_hi],
    [pl_lo_inf]), and from two such lanes the lane of [fmin] or [fmax] of
    them ([pl_lo_fmin], [pl_hi_fmax]), as [Interval::pow] takes the minimum
    and maximum of the values at two corners. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Mpfr MpfrRound Ieee1788 Integer MaxMin
  AddSub DivTight MonoInc Sign.

Open Scope R_scope.

(** What [mpfr_get_d] gives for the exact results of the special values: a
    zero, which is 0 rounded, 1 rounded, and an infinity. *)
Lemma pm_get_zero :
  forall emin emax m, get_d_ok emin emax m -> forall rnd s,
  mpfr_round f64_format rnd 0 (with_val (mpfr_get_d m rnd (MZero s))).
Proof.
intros emin emax m (_ & Hzero & _) rnd s.
destruct (Hzero rnd s) as (s' & ->). cbn [with_val].
apply mpfr_round_zero. exists zero. split; reflexivity.
Qed.

Lemma pm_get_one :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> forall rnd,
  mpfr_round f64_format rnd 1 (with_val (mpfr_get_d m rnd (MNum 1))).
Proof.
intros emin emax m Hr (Hnum & _ & _) rnd.
apply Hnum; [exact R1_neq_R0 | exact (proj1 (mpfr_format_1 emin emax Hr))].
Qed.

Lemma pm_get_inf :
  forall emin emax m, get_d_ok emin emax m -> forall rnd s,
  mpfr_get_d m rnd (MInf s) = B754_infinity s.
Proof.
intros emin emax m (_ & _ & Hinf) rnd s. apply Hinf.
Qed.

(** ** [pow] *)

Lemma pow_fin :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall rnd p q, is_finite p = true -> is_finite q = true -> pow_dom (B2R p) (B2R q) ->
  mpfr_round f64_format rnd (Rpow (B2R p) (B2R q))
    (with_val (mpfr_fn2 m (mpfr_pow m) rnd p q)).
Proof.
intros emin emax m Hr Hget (Hc & _) rnd p q Fp Fq Hd.
unfold mpfr_fn2. apply (mpfr_fn_round emin emax); [exact Hr | exact Hget|].
exact (Hc rnd p q Fp Fq Hd).
Qed.

(** [pow(+0, y)] for [y < 0] or [y = -inf], for [y = +inf], and for a zero
    [y]. *)
Lemma pow_zero_neg :
  forall emin emax m, get_d_ok emin emax m -> pow_ok emin emax m ->
  forall rnd q, (is_finite q = true /\ B2R q < 0) \/ q = B754_infinity true ->
  mpfr_fn2 m (mpfr_pow m) rnd (B754_zero false) q = B754_infinity false.
Proof.
intros emin emax m Hget (Hc & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) rnd q [(Fq & Hq)| ->];
  unfold mpfr_fn2; cbn [with_val].
- rewrite (with_val_finite q Fq) by lra. rewrite H1 by exact Hq.
  exact (pm_get_inf _ _ _ Hget _ _).
- rewrite H2. exact (pm_get_inf _ _ _ Hget _ _).
Qed.

Lemma pow_zero_pinf :
  forall emin emax m, get_d_ok emin emax m -> pow_ok emin emax m ->
  forall rnd,
  mpfr_round f64_format rnd 0
    (with_val (mpfr_fn2 m (mpfr_pow m) rnd (B754_zero false) (B754_infinity false))).
Proof.
intros emin emax m Hget (Hc & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) rnd.
unfold mpfr_fn2; cbn [with_val]. rewrite H3. exact (pm_get_zero _ _ _ Hget _ _).
Qed.

Lemma pow_zero_zero :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall rnd s,
  mpfr_round f64_format rnd 1
    (with_val (mpfr_fn2 m (mpfr_pow m) rnd (B754_zero false) (B754_zero s))).
Proof.
intros emin emax m Hr Hget (Hc & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) rnd s.
unfold mpfr_fn2; cbn [with_val]. rewrite H4. exact (pm_get_one _ _ _ Hr Hget _).
Qed.

(** [pow(+inf, y)] for a zero [y], for [y < 0] or [y = -inf], and for
    [y > 0] or [y = +inf]. *)
Lemma pow_pinf_zero :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall rnd s,
  mpfr_round f64_format rnd 1
    (with_val (mpfr_fn2 m (mpfr_pow m) rnd (B754_infinity false) (B754_zero s))).
Proof.
intros emin emax m Hr Hget (Hc & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) rnd s.
unfold mpfr_fn2; cbn [with_val]. rewrite H5. exact (pm_get_one _ _ _ Hr Hget _).
Qed.

Lemma pow_pinf_neg :
  forall emin emax m, get_d_ok emin emax m -> pow_ok emin emax m ->
  forall rnd q, (is_finite q = true /\ B2R q < 0) \/ q = B754_infinity true ->
  mpfr_round f64_format rnd 0
    (with_val (mpfr_fn2 m (mpfr_pow m) rnd (B754_infinity false) q)).
Proof.
intros emin emax m Hget (Hc & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) rnd q [(Fq & Hq)| ->];
  unfold mpfr_fn2; cbn [with_val].
- rewrite (with_val_finite q Fq) by lra. rewrite H11 by exact Hq.
  exact (pm_get_zero _ _ _ Hget _ _).
- rewrite H12. exact (pm_get_zero _ _ _ Hget _ _).
Qed.

Lemma pow_pinf_pos :
  forall emin emax m, get_d_ok emin emax m -> pow_ok emin emax m ->
  forall rnd q, (is_finite q = true /\ 0 < B2R q) \/ q = B754_infinity false ->
  mpfr_fn2 m (mpfr_pow m) rnd (B754_infinity false) q = B754_infinity false.
Proof.
intros emin emax m Hget (Hc & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) rnd q [(Fq & Hq)| ->];
  unfold mpfr_fn2; cbn [with_val].
- rewrite (with_val_finite q Fq) by lra. rewrite H13 by exact Hq.
  exact (pm_get_inf _ _ _ Hget _ _).
- rewrite H14. exact (pm_get_inf _ _ _ Hget _ _).
Qed.

(** [pow(x, ±inf)] for a finite [x] of 1, between 0 and 1, and above 1. *)
Lemma pow_one_inf :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pow_ok emin emax m ->
  forall rnd p s, is_finite p = true -> B2R p = 1 ->
  mpfr_round f64_format rnd 1
    (with_val (mpfr_fn2 m (mpfr_pow m) rnd p (B754_infinity s))).
Proof.
intros emin emax m Hr Hget (Hc & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) rnd p s Fp Hp.
unfold mpfr_fn2. rewrite (with_val_finite p Fp) by lra. rewrite Hp. cbn [with_val].
rewrite H6. exact (pm_get_one _ _ _ Hr Hget _).
Qed.

Lemma pow_lt1_ninf :
  forall emin emax m, get_d_ok emin emax m -> pow_ok emin emax m ->
  forall rnd p, is_finite p = true -> 0 < B2R p < 1 ->
  mpfr_fn2 m (mpfr_pow m) rnd p (B754_infinity true) = B754_infinity false.
Proof.
intros emin emax m Hget (Hc & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) rnd p Fp Hp.
unfold mpfr_fn2. rewrite (with_val_finite p Fp) by lra. cbn [with_val].
rewrite H7 by exact Hp. exact (pm_get_inf _ _ _ Hget _ _).
Qed.

Lemma pow_gt1_ninf :
  forall emin emax m, get_d_ok emin emax m -> pow_ok emin emax m ->
  forall rnd p, is_finite p = true -> 1 < B2R p ->
  mpfr_round f64_format rnd 0
    (with_val (mpfr_fn2 m (mpfr_pow m) rnd p (B754_infinity true))).
Proof.
intros emin emax m Hget (Hc & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) rnd p Fp Hp.
unfold mpfr_fn2. rewrite (with_val_finite p Fp) by lra. cbn [with_val].
rewrite H8 by exact Hp. exact (pm_get_zero _ _ _ Hget _ _).
Qed.

Lemma pow_lt1_pinf :
  forall emin emax m, get_d_ok emin emax m -> pow_ok emin emax m ->
  forall rnd p, is_finite p = true -> 0 < B2R p < 1 ->
  mpfr_round f64_format rnd 0
    (with_val (mpfr_fn2 m (mpfr_pow m) rnd p (B754_infinity false))).
Proof.
intros emin emax m Hget (Hc & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) rnd p Fp Hp.
unfold mpfr_fn2. rewrite (with_val_finite p Fp) by lra. cbn [with_val].
rewrite H9 by exact Hp. exact (pm_get_zero _ _ _ Hget _ _).
Qed.

Lemma pow_gt1_pinf :
  forall emin emax m, get_d_ok emin emax m -> pow_ok emin emax m ->
  forall rnd p, is_finite p = true -> 1 < B2R p ->
  mpfr_fn2 m (mpfr_pow m) rnd p (B754_infinity false) = B754_infinity false.
Proof.
intros emin emax m Hget (Hc & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) rnd p Fp Hp.
unfold mpfr_fn2. rewrite (with_val_finite p Fp) by lra. cbn [with_val].
rewrite H10 by exact Hp. exact (pm_get_inf _ _ _ Hget _ _).
Qed.

(** ** [pown] *)

Lemma pown_fin :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pown_ok emin emax m ->
  forall rnd p n, is_i32 n -> is_finite p = true -> pown_dom n (B2R p) ->
  mpfr_round f64_format rnd (powerRZ (B2R p) n)
    (with_val (mpfr_fn_si m (mpfr_pow_si m) rnd p n)).
Proof.
intros emin emax m Hr Hget (Pc & _) rnd p n Hn Fp Hd.
unfold mpfr_fn_si. apply (mpfr_fn_round emin emax); [exact Hr | exact Hget|].
exact (Pc rnd p n Hn Fp Hd).
Qed.

(** [pow_si(±0, n)] for [n < 0], even and odd. *)
Lemma pown_zero_neg_even :
  forall emin emax m, get_d_ok emin emax m -> pown_ok emin emax m ->
  forall rnd s n, is_i32 n -> (n < 0)%Z -> Z.even n = true ->
  mpfr_fn_si m (mpfr_pow_si m) rnd (B754_zero s) n = B754_infinity false.
Proof.
intros emin emax m Hget (Pc & P1 & P2 & P3 & P4 & P5 & P6 & P7) rnd s n Hn Hneg He.
unfold mpfr_fn_si; cbn [with_val]. rewrite (P1 rnd s n Hn Hneg He).
exact (pm_get_inf _ _ _ Hget _ _).
Qed.

Lemma pown_zero_neg_odd :
  forall emin emax m, get_d_ok emin emax m -> pown_ok emin emax m ->
  forall rnd s n, is_i32 n -> (n < 0)%Z -> Z.odd n = true ->
  mpfr_fn_si m (mpfr_pow_si m) rnd (B754_zero s) n = B754_infinity s.
Proof.
intros emin emax m Hget (Pc & P1 & P2 & P3 & P4 & P5 & P6 & P7) rnd s n Hn Hneg Ho.
unfold mpfr_fn_si; cbn [with_val]. rewrite (P2 rnd s n Hn Hneg Ho).
exact (pm_get_inf _ _ _ Hget _ _).
Qed.

(** [pow_si(+inf, n)] for [n < 0], [n = 0] and [n > 0], and
    [pow_si(-inf, n)] for an odd [n]. *)
Lemma pown_pinf_neg :
  forall emin emax m, get_d_ok emin emax m -> pown_ok emin emax m ->
  forall rnd n, is_i32 n -> (n < 0)%Z ->
  mpfr_round f64_format rnd 0
    (with_val (mpfr_fn_si m (mpfr_pow_si m) rnd (B754_infinity false) n)).
Proof.
intros emin emax m Hget (Pc & P1 & P2 & P3 & P4 & P5 & P6 & P7) rnd n Hn Hneg.
unfold mpfr_fn_si; cbn [with_val]. rewrite (P3 rnd n Hn Hneg).
exact (pm_get_zero _ _ _ Hget _ _).
Qed.

Lemma pown_pinf_0 :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pown_ok emin emax m ->
  forall rnd,
  mpfr_round f64_format rnd 1
    (with_val (mpfr_fn_si m (mpfr_pow_si m) rnd (B754_infinity false) 0)).
Proof.
intros emin emax m Hr Hget (Pc & P1 & P2 & P3 & P4 & P5 & P6 & P7) rnd.
unfold mpfr_fn_si; cbn [with_val]. rewrite P4.
exact (pm_get_one _ _ _ Hr Hget _).
Qed.

Lemma pown_pinf_pos :
  forall emin emax m, get_d_ok emin emax m -> pown_ok emin emax m ->
  forall rnd n, is_i32 n -> (0 < n)%Z ->
  mpfr_fn_si m (mpfr_pow_si m) rnd (B754_infinity false) n = B754_infinity false.
Proof.
intros emin emax m Hget (Pc & P1 & P2 & P3 & P4 & P5 & P6 & P7) rnd n Hn Hpos.
unfold mpfr_fn_si; cbn [with_val]. rewrite (P5 rnd n Hn Hpos).
exact (pm_get_inf _ _ _ Hget _ _).
Qed.

Lemma pown_ninf_neg_odd :
  forall emin emax m, get_d_ok emin emax m -> pown_ok emin emax m ->
  forall rnd n, is_i32 n -> (n < 0)%Z -> Z.odd n = true ->
  mpfr_round f64_format rnd 0
    (with_val (mpfr_fn_si m (mpfr_pow_si m) rnd (B754_infinity true) n)).
Proof.
intros emin emax m Hget (Pc & P1 & P2 & P3 & P4 & P5 & P6 & P7) rnd n Hn Hneg Ho.
unfold mpfr_fn_si; cbn [with_val]. rewrite (P6 rnd n Hn Hneg Ho).
exact (pm_get_zero _ _ _ Hget _ _).
Qed.

Lemma pown_ninf_pos_odd :
  forall emin emax m, get_d_ok emin emax m -> pown_ok emin emax m ->
  forall rnd n, is_i32 n -> (0 < n)%Z -> Z.odd n = true ->
  mpfr_fn_si m (mpfr_pow_si m) rnd (B754_infinity true) n = B754_infinity true.
Proof.
intros emin emax m Hget (Pc & P1 & P2 & P3 & P4 & P5 & P6 & P7) rnd n Hn Hpos Ho.
unfold mpfr_fn_si; cbn [with_val]. rewrite (P7 rnd n Hn Hpos Ho).
exact (pm_get_inf _ _ _ Hget _ _).
Qed.

(** ** Lanes from bounds *)

(** The least upper bound of the union of two sets is the larger of their
    least upper bounds, with [None] for +inf. *)
Definition pm_omax (o1 o2 : option R) : option R :=
  match o1, o2 with Some a, Some b => Some (Rmax a b) | _, _ => None end.

Lemma pm_lub_union :
  forall o1 o2 (T1 T2 : R -> Prop), lub o1 T1 -> lub o2 T2 ->
  lub (pm_omax o1 o2) (fun s => T1 s \/ T2 s).
Proof.
intros [a|] [b|] T1 T2 H1 H2 s; cbn [pm_omax below].
- split.
  + (* Every upper bound of the union bounds both sets, so is at or above
       [a] and [b]. *)
    intros Hs m Hm.
    assert (Ha : a <= m).
    { apply (proj1 (H1 a) (Rle_refl a)). intros r Hr. apply Hm. left. exact Hr. }
    assert (Hb : b <= m).
    { apply (proj1 (H2 b) (Rle_refl b)). intros r Hr. apply Hm. right. exact Hr. }
    revert Hs. unfold Rmax. destruct (Rle_dec a b); lra.
  + intros H. apply H. intros r [Hr|Hr].
    * pose proof (lub_below _ _ _ H1 Hr) as Hb. cbn [below] in Hb.
      unfold Rmax. destruct (Rle_dec a b); lra.
    * pose proof (lub_below _ _ _ H2 Hr) as Hb. cbn [below] in Hb.
      unfold Rmax. destruct (Rle_dec a b); lra.
- (* [T2] has no upper bound, so neither has the union. *)
  split; [|intros _; exact I]. intros _ m Hm.
  apply (proj1 (H2 s) I). intros r Hr. apply Hm. right. exact Hr.
- split; [|intros _; exact I]. intros _ m Hm.
  apply (proj1 (H1 s) I). intros r Hr. apply Hm. left. exact Hr.
- split; [|intros _; exact I]. intros _ m Hm.
  apply (proj1 (H1 s) I). intros r Hr. apply Hm. left. exact Hr.
Qed.

Lemma pm_omax_ule :
  forall o1 o2 o, ule o1 o -> ule o2 o -> ule (pm_omax o1 o2) o.
Proof.
intros [a|] [b|] o H1 H2 s Hs; cbn [pm_omax below] in Hs.
- unfold Rmax in Hs. destruct (Rle_dec a b); [apply H2 | apply H1]; exact Hs.
- apply H2. exact I.
- apply H1. exact I.
- apply H1. exact I.
Qed.

Lemma pm_ule_omax_r : forall o1 o2, ule o2 (pm_omax o1 o2).
Proof.
intros [a|] [b|] s Hs; cbn [pm_omax below] in *; try exact I.
unfold Rmax. destruct (Rle_dec a b); lra.
Qed.

(** The least float or +inf at or above the larger of two upper bounds is
    the larger of the two lanes. [least_lane] depends on the lane only
    through [upper_ok] and its [bound], so of two lanes with the same
    bound either one is it. *)
Lemma pm_least_max :
  forall o1 o2 w1 w2, least_lane o1 w1 -> least_lane o2 w2 ->
  ule (bound w1) (bound w2) -> least_lane (pm_omax o1 o2) w2.
Proof.
intros o1 o2 w1 w2 (_ & L1 & _) (U2 & L2 & M2) H12.
split; [exact U2|]. split.
- apply pm_omax_ule; [|exact L2]. intros s Hs. apply H12, L1, Hs.
- intros z Uz Hz. apply (M2 z Uz). intros s Hs. apply Hz, pm_ule_omax_r, Hs.
Qed.

Lemma pm_union_lane :
  forall (T1 T2 : R -> Prop) w1 w2, lane_ok T1 w1 -> lane_ok T2 w2 ->
  ule (bound w1) (bound w2) -> lane_ok (fun s => T1 s \/ T2 s) w2.
Proof.
intros T1 T2 w1 w2 (o1 & H1 & L1) (o2 & H2 & L2) H12.
exists (pm_omax o1 o2).
split; [exact (pm_lub_union _ _ _ _ H1 H2) | exact (pm_least_max _ _ _ _ L1 L2 H12)].
Qed.

Lemma pm_union_lane_l :
  forall (T1 T2 : R -> Prop) w1 w2, lane_ok T1 w1 -> lane_ok T2 w2 ->
  ule (bound w2) (bound w1) -> lane_ok (fun s => T1 s \/ T2 s) w1.
Proof.
intros T1 T2 w1 w2 H1 H2 H21.
apply lane_ok_ext with (fun s => T2 s \/ T1 s); [intros r; tauto|].
exact (pm_union_lane T2 T1 w2 w1 H2 H1 H21).
Qed.

(** The comparisons that [fmax] makes, on two upper lanes, and those that
    [fmin] makes, on the negations of two upper lanes. *)
Lemma pm_lt_true_ule :
  forall a b, upper_ok a -> upper_ok b -> Model.lt a b = true -> ule (bound a) (bound b).
Proof.
intros a b [Fa| ->] [Fb| ->] H.
- rewrite !bound_finite by assumption. unfold Model.lt in H.
  rewrite Bltb_correct in H by assumption.
  destruct (Rlt_bool_spec (B2R a) (B2R b)) as [Hab|]; [|discriminate H].
  intros s Hs. cbn [below] in *. lra.
- intros s _. exact I.
- destruct b as [sb|sb| |sb mb eb Hb]; try discriminate Fb; discriminate H.
- intros s _. exact I.
Qed.

Lemma pm_lt_false_ule :
  forall a b, upper_ok a -> upper_ok b -> Model.lt b a = false -> ule (bound a) (bound b).
Proof.
intros a b [Fa| ->] [Fb| ->] H.
- rewrite !bound_finite by assumption. unfold Model.lt in H.
  rewrite Bltb_correct in H by assumption.
  destruct (Rlt_bool_spec (B2R b) (B2R a)) as [|Hba]; [discriminate H|].
  intros s Hs. cbn [below] in *. lra.
- intros s _. exact I.
- destruct b as [sb|sb| |sb mb eb Hb]; try discriminate Fb; discriminate H.
- intros s _. exact I.
Qed.

(** The negation of an upper lane is a finite float or -inf. *)
Lemma pm_upper_opp :
  forall a, upper_ok (opp a) -> is_finite a = true \/ a = B754_infinity true.
Proof.
intros a [Fa|E]; [left; rewrite is_finite_opp in Fa; exact Fa|right].
destruct a as [sa|[|]| |sa ma ea Ha]; cbn in E; try discriminate E; reflexivity.
Qed.

Lemma pm_lt_true_ule_opp :
  forall a b, upper_ok (opp a) -> upper_ok (opp b) -> Model.lt a b = true ->
  ule (bound (opp b)) (bound (opp a)).
Proof.
intros a b Ua Ub H.
destruct (pm_upper_opp a Ua) as [Fa| ->]; [|intros s _; exact I].
destruct (pm_upper_opp b Ub) as [Fb| ->].
- rewrite !bound_finite by (rewrite is_finite_opp; assumption).
  rewrite !B2R_opp. unfold Model.lt in H. rewrite Bltb_correct in H by assumption.
  destruct (Rlt_bool_spec (B2R a) (B2R b)) as [Hab|]; [|discriminate H].
  intros s Hs. cbn [below] in *. lra.
- (* No float is below -inf. *)
  destruct a as [sa|sa| |sa ma ea Ha]; try discriminate Fa; discriminate H.
Qed.

Lemma pm_lt_false_ule_opp :
  forall a b, upper_ok (opp a) -> upper_ok (opp b) -> Model.lt b a = false ->
  ule (bound (opp b)) (bound (opp a)).
Proof.
intros a b Ua Ub H.
destruct (pm_upper_opp a Ua) as [Fa| ->]; [|intros s _; exact I].
destruct (pm_upper_opp b Ub) as [Fb| ->].
- rewrite !bound_finite by (rewrite is_finite_opp; assumption).
  rewrite !B2R_opp. unfold Model.lt in H. rewrite Bltb_correct in H by assumption.
  destruct (Rlt_bool_spec (B2R b) (B2R a)) as [|Hba]; [discriminate H|].
  intros s Hs. cbn [below] in *. lra.
- (* -inf is below every finite float. *)
  destruct a as [sa|sa| |sa ma ea Ha]; try discriminate Fa; discriminate H.
Qed.

(** The lower lane of an interval whose lower bound [w] is [L] rounded
    down, for the greatest lower bound [L] of the set [S]. *)
Lemma pl_lo :
  forall (S : R -> Prop) L w,
  (forall s, S s -> L <= s) -> (forall eps, 0 < eps -> exists s, S s /\ s < L + eps) ->
  mpfr_round f64_format RNDD L (with_val w) ->
  lane_ok (fun s => S (- s)) (opp w).
Proof.
intros S L w Hlb Happ Hw. exists (Some (- L)). split.
- (* [-L] is the least upper bound of the negations of the elements of
     [S]. *)
  apply mono_lub_approx.
  + intros s Hs. cbv beta in Hs. specialize (Hlb _ Hs). lra.
  + intros eps He. destruct (Happ eps He) as (s & Hs & Hlt).
    exists (- s). cbv beta. rewrite Ropp_involutive. split; [exact Hs | lra].
- exact (round_dn_lane L w Hw).
Qed.

(** The upper lane [w], [U] rounded up, for the least upper bound [U] of
    [S]. *)
Lemma pl_hi :
  forall (S : R -> Prop) U w,
  (forall s, S s -> s <= U) -> (forall eps, 0 < eps -> exists s, S s /\ U - eps < s) ->
  mpfr_round f64_format RNDU U (with_val w) ->
  lane_ok S w.
Proof.
intros S U w Hub Happ Hw. exists (Some U).
split; [exact (mono_lub_approx U S Hub Happ) | exact (round_up_lane U w Hw)].
Qed.

(** The lower lane of a lower bound -inf, for a set with no lower
    bound. *)
Lemma pl_lo_inf :
  forall (S : R -> Prop), (forall M, exists s, S s /\ s <= M) ->
  lane_ok (fun s => S (- s)) (opp (B754_infinity true)).
Proof.
intros S HS. change (opp (B754_infinity true)) with (B754_infinity false : f64).
apply lane_ok_inf. intros M. destruct (HS (- M)) as (s & Hs & Hle).
exists (- s). cbv beta. rewrite Ropp_involutive. split; [exact Hs | lra].
Qed.

(** The lower bound [fmin first w1 w2] of the union of two sets, from
    their lower bounds [w1] and [w2], and the upper bound
    [fmax first w1 w2] from their upper bounds. *)
Lemma pl_lo_fmin :
  forall (S1 S2 : R -> Prop) w1 w2 first, is_nan w1 = false -> is_nan w2 = false ->
  lane_ok (fun s => S1 (- s)) (opp w1) -> lane_ok (fun s => S2 (- s)) (opp w2) ->
  lane_ok (fun s => S1 (- s) \/ S2 (- s)) (opp (fmin first w1 w2)).
Proof.
intros S1 S2 w1 w2 first _ _ H1 H2.
assert (U1 : upper_ok (opp w1)) by (destruct H1 as (o & _ & U & _); exact U).
assert (U2 : upper_ok (opp w2)) by (destruct H2 as (o & _ & U & _); exact U).
(* [fmin] returns the smaller float, whose negation is the larger lane. *)
unfold fmin. destruct (Model.lt w1 w2) eqn:E12.
- apply (pm_union_lane_l (fun s => S1 (- s)) (fun s => S2 (- s)) _ _ H1 H2).
  exact (pm_lt_true_ule_opp w1 w2 U1 U2 E12).
- destruct (Model.lt w2 w1) eqn:E21.
  + apply (pm_union_lane (fun s => S1 (- s)) (fun s => S2 (- s)) _ _ H1 H2).
    exact (pm_lt_true_ule_opp w2 w1 U2 U1 E21).
  + destruct first.
    * apply (pm_union_lane_l (fun s => S1 (- s)) (fun s => S2 (- s)) _ _ H1 H2).
      exact (pm_lt_false_ule_opp w1 w2 U1 U2 E21).
    * apply (pm_union_lane (fun s => S1 (- s)) (fun s => S2 (- s)) _ _ H1 H2).
      exact (pm_lt_false_ule_opp w2 w1 U2 U1 E12).
Qed.

Lemma pl_hi_fmax :
  forall (S1 S2 : R -> Prop) w1 w2 first, is_nan w1 = false -> is_nan w2 = false ->
  lane_ok S1 w1 -> lane_ok S2 w2 ->
  lane_ok (fun s => S1 s \/ S2 s) (fmax first w1 w2).
Proof.
intros S1 S2 w1 w2 first _ _ H1 H2.
assert (U1 : upper_ok w1) by (destruct H1 as (o & _ & U & _); exact U).
assert (U2 : upper_ok w2) by (destruct H2 as (o & _ & U & _); exact U).
unfold fmax. destruct (Model.lt w1 w2) eqn:E12.
- exact (pm_union_lane S1 S2 _ _ H1 H2 (pm_lt_true_ule w1 w2 U1 U2 E12)).
- destruct (Model.lt w2 w1) eqn:E21.
  + exact (pm_union_lane_l S1 S2 _ _ H1 H2 (pm_lt_false_ule w2 w1 U2 U1 E12)).
  + destruct first.
    * exact (pm_union_lane_l S1 S2 _ _ H1 H2 (pm_lt_false_ule w2 w1 U2 U1 E12)).
    * exact (pm_union_lane S1 S2 _ _ H1 H2 (pm_lt_false_ule w1 w2 U1 U2 E21)).
Qed.
