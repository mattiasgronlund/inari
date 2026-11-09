(** * [hypot] of intervals and decorated intervals

    [Interval::hypot] takes the absolute values of its arguments
    ([abs_correct] of [Abs.v]), as [Rhypot r t = Rhypot |r| |t|], and
    [Rhypot] increases in each argument on [[0, +inf)]. So the image is
    from [Rhypot] at the lower bounds of [|x|] and [|y|] to [Rhypot] at
    their upper bounds. [Rhypot] is defined and continuous on the whole
    plane ([Rhypot_continuous]), so the decoration is that of
    [set_dec_correct] of [DecBinary.v]. As [|r|, |t| <= Rhypot r t], a
    bounded image has bounded arguments, so the decorated theorem needs
    no hypothesis [com_common]. Each assumes what [Mpfr.v] says of
    MPFR. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr RealBounds ComCommon
  Integer AddSub MulTight DivTight MpfrRound Interior MonoInc Abs DecBinary.

Open Scope R_scope.

(** ** The point function *)

Lemma Rhypot_nonneg : forall r t, 0 <= Rhypot r t.
Proof.
intros r t. apply sqrt_pos.
Qed.

Lemma Rhypot_sqr : forall r t, Rhypot r t * Rhypot r t = r * r + t * t.
Proof.
intros r t. unfold Rhypot. apply sqrt_sqrt.
pose proof (Rle_0_sqr r). pose proof (Rle_0_sqr t). unfold Rsqr in *. lra.
Qed.

(** [|r| = sqrt (r * r) <= sqrt (r * r + t * t)], and the same for [t]. *)
Lemma Rabs_le_Rhypot_l : forall r t, Rabs r <= Rhypot r t.
Proof.
intros r t. rewrite <- sqrt_Rsqr_abs. unfold Rhypot, Rsqr. apply sqrt_le_1_alt.
pose proof (Rle_0_sqr t). unfold Rsqr in *. lra.
Qed.

Lemma Rabs_le_Rhypot_r : forall r t, Rabs t <= Rhypot r t.
Proof.
intros r t. rewrite <- sqrt_Rsqr_abs. unfold Rhypot, Rsqr. apply sqrt_le_1_alt.
pose proof (Rle_0_sqr r). unfold Rsqr in *. lra.
Qed.

Lemma Rhypot_abs : forall r t, Rhypot r t = Rhypot (Rabs r) (Rabs t).
Proof.
intros r t. unfold Rhypot. f_equal.
pose proof (Rsqr_abs r) as Hr. pose proof (Rsqr_abs t) as Ht.
unfold Rsqr in Hr, Ht. lra.
Qed.

(** [Rhypot] increases in each argument on [[0, +inf)]. *)
Lemma Rhypot_le :
  forall a b c d, 0 <= a <= c -> 0 <= b <= d -> Rhypot a b <= Rhypot c d.
Proof.
intros a b c d Hac Hbd. unfold Rhypot. apply sqrt_le_1_alt.
apply Rplus_le_compat; apply Rmult_le_compat; lra.
Qed.

(** [Rhypot] is 1-Lipschitz in each argument: with [u = Rhypot a b] and
    [v = Rhypot c d], [(u - v) (u + v) = u² - v²] is
    [(a - c) (a + c) + (b - d) (b + d)], and [|a + c|] and [|b + d|] are
    at most [u + v]. *)
Lemma Rhypot_lipschitz :
  forall a b c d, Rabs (Rhypot a b - Rhypot c d) <= Rabs (a - c) + Rabs (b - d).
Proof.
intros a b c d.
pose proof (Rhypot_nonneg a b) as Hu0. pose proof (Rhypot_nonneg c d) as Hv0.
pose proof (Rhypot_sqr a b) as Huu. pose proof (Rhypot_sqr c d) as Hvv.
pose proof (Rabs_le_Rhypot_l a b) as Ha. pose proof (Rabs_le_Rhypot_r a b) as Hb.
pose proof (Rabs_le_Rhypot_l c d) as Hc. pose proof (Rabs_le_Rhypot_r c d) as Hd.
revert Hu0 Hv0 Huu Hvv Ha Hb Hc Hd. generalize (Rhypot a b) (Rhypot c d).
intros u v Hu0 Hv0 Huu Hvv Ha Hb Hc Hd.
pose proof (Rabs_pos (a - c)) as P1. pose proof (Rabs_pos (b - d)) as P2.
destruct (Req_dec (u + v) 0) as [Euv|Euv].
- (* [u = v = 0]. *)
  replace (u - v) with 0 by lra. rewrite Rabs_R0. lra.
- assert (Huv : 0 < u + v) by lra.
  apply (Rmult_le_reg_r (u + v)); [exact Huv|].
  assert (E : (u - v) * (u + v) = (a - c) * (a + c) + (b - d) * (b + d)) by nra.
  assert (L : Rabs (u - v) * (u + v) = Rabs ((a - c) * (a + c) + (b - d) * (b + d))).
  { rewrite <- E, Rabs_mult, (Rabs_pos_eq (u + v)) by lra. reflexivity. }
  rewrite L.
  assert (Hac : Rabs (a + c) <= u + v)
    by (apply Rle_trans with (Rabs a + Rabs c); [apply Rabs_triang | lra]).
  assert (Hbd : Rabs (b + d) <= u + v)
    by (apply Rle_trans with (Rabs b + Rabs d); [apply Rabs_triang | lra]).
  apply Rle_trans with (Rabs ((a - c) * (a + c)) + Rabs ((b - d) * (b + d)));
    [apply Rabs_triang|].
  rewrite !Rabs_mult, Rmult_plus_distr_r.
  apply Rplus_le_compat; apply Rmult_le_compat_l; assumption.
Qed.

Lemma Rhypot_continuous : forall r t, continuity2_pt Rhypot r t.
Proof.
intros r t eps Heps. exists (eps / 2). split; [lra|].
intros r' t' _ _ Hr Ht. pose proof (Rhypot_lipschitz r' t' r t). lra.
Qed.

(** ** Hulls of sets of reals

    [Interval::abs] returns the hull of the absolute values of the reals
    of its argument. A finite bound of a hull is an element of the set,
    and bounds it. [hull_mem] of [DecBinary.v] says that a hull contains
    its set. *)

Lemma hull_nonempty :
  forall s y, is_hull s y -> Interval.is_empty y = false -> exists u, s u.
Proof.
intros s y Hh Hn. destruct (nonempty_mem y (proj1 Hh) Hn) as (r & Hr).
destruct (proj1 (proj2 Hh r) Hr) as (u & _ & Hu & _). exists u. exact Hu.
Qed.

Lemma hull_sup :
  forall s y, is_hull s y -> Interval.is_empty y = false ->
  is_finite (snd (rep y)) = true ->
  s (B2R (snd (rep y))) /\ forall u, s u -> u <= B2R (snd (rep y)).
Proof.
intros s y Hh Hn Fb.
assert (Hle : forall u, s u -> u <= B2R (snd (rep y))).
{ intros u Hu. exact (mono_mem_le_sup y u (hull_mem s y u Hh Hu) Fb). }
split; [|exact Hle].
destruct (proj1 (proj2 Hh _) (mono_mem_sup y (proj1 Hh) Hn Fb))
  as (u & v & _ & Hv & _ & H).
pose proof (Hle v Hv). replace (B2R (snd (rep y))) with v by lra. exact Hv.
Qed.

Lemma hull_inf :
  forall s y, is_hull s y -> Interval.is_empty y = false ->
  is_finite (opp (fst (rep y))) = true ->
  s (B2R (opp (fst (rep y)))) /\ forall u, s u -> B2R (opp (fst (rep y))) <= u.
Proof.
intros s y Hh Hn Fa.
assert (Hge : forall u, s u -> B2R (opp (fst (rep y))) <= u).
{ intros u Hu. exact (mono_inf_le_mem y u (hull_mem s y u Hh Hu) Fa). }
split; [|exact Hge].
destruct (proj1 (proj2 Hh _) (mono_mem_inf y (proj1 Hh) Hn Fa))
  as (u & v & Hu & _ & H & _).
pose proof (Hge u Hu). replace (B2R (opp (fst (rep y)))) with u by lra. exact Hu.
Qed.

(** A hull with the upper bound +inf has elements of the set as large as
    asked. *)
Lemma hull_up :
  forall s y, is_hull s y -> Interval.is_empty y = false ->
  snd (rep y) = B754_infinity false -> forall M, exists u, s u /\ M <= u.
Proof.
intros s y Hh Hn Eb M.
destruct (nonempty_mem y (proj1 Hh) Hn) as (r0 & Hr0).
pose proof (mono_mem_up y r0 (Rmax M r0) Hr0 Eb (Rmax_r M r0)) as Hm.
destruct (proj1 (proj2 Hh _) Hm) as (u & v & _ & Hv & _ & H).
exists v. split; [exact Hv|]. pose proof (Rmax_l M r0). lra.
Qed.

(** The lower bound of a nonempty hull of reals at or above 0 is finite:
    at -inf, the hull would hold -1, which is below every element. *)
Lemma hull_inf_finite :
  forall s y, is_hull s y -> (forall u, s u -> 0 <= u) -> Interval.is_empty y = false ->
  is_finite (opp (fst (rep y))) = true.
Proof.
intros s y Hh Hs Hn.
destruct (valid_nonempty y (proj1 Hh) Hn) as ([Fa|Ea] & _ & _); [exact Fa|exfalso].
destruct (nonempty_mem y (proj1 Hh) Hn) as (r0 & Hr0).
pose proof (mono_mem_dn y r0 (Rmin (-1) r0) Hr0 Ea (Rmin_r (-1) r0)) as Hm.
destruct (proj1 (proj2 Hh _) Hm) as (u & v & Hu & _ & H & _).
pose proof (Hs u Hu). pose proof (Rmin_l (-1) r0). lra.
Qed.

Lemma image_Rabs_nonneg : forall x u, image Rabs x u -> 0 <= u.
Proof.
intros x u (r & _ & ->). apply Rabs_pos.
Qed.

(** ** The upper bound at +inf *)

(** [hypot_ru(+inf, y) = hypot_ru(x, +inf) = +inf]. *)
Lemma mpfr_hypot_inf_l :
  forall emin emax m, get_d_ok emin emax m ->
  (forall y : f64, mpfr_hypot m RNDU (MInf false) (with_val y) = MInf false) ->
  forall b, mpfr_fn2 m (mpfr_hypot m) RNDU (B754_infinity false) b = B754_infinity false.
Proof.
intros emin emax m (_ & _ & Hinf) H b. unfold mpfr_fn2. cbn [with_val].
rewrite H. apply Hinf.
Qed.

Lemma mpfr_hypot_inf_r :
  forall emin emax m, get_d_ok emin emax m ->
  (forall x : f64, mpfr_hypot m RNDU (with_val x) (MInf false) = MInf false) ->
  forall a, mpfr_fn2 m (mpfr_hypot m) RNDU a (B754_infinity false) = B754_infinity false.
Proof.
intros emin emax m (_ & _ & Hinf) H a. unfold mpfr_fn2. cbn [with_val].
rewrite H. apply Hinf.
Qed.

(** ** The theorems *)

(** [Interval::hypot] returns the tightest interval that contains the image
    of the box [x × y] under [Rhypot]. *)
Theorem hypot_correct :
  forall emin emax m x y, range_ok emin emax -> get_d_ok emin emax m -> hypot_ok emin emax m ->
  valid x -> valid y ->
  exists z, Interval.hypot m x y = Some z /\ is_tightest (image2 Rhypot x y) z.
Proof.
intros emin emax m x y Hr Hg (Hc & Hix & Hiy) Hx Hy.
destruct (abs_correct x Hx) as (ax & Ex & Hax).
destruct (abs_correct y Hy) as (ay & Ey & Hay).
unfold Interval.hypot. rewrite Ex, Ey.
destruct (Interval.is_empty ax || Interval.is_empty ay) eqn:Ee;
  eexists; (split; [reflexivity|]).
- (* An empty [|x|] or [|y|] comes from an empty [x] or [y], whose box has
     an empty image. *)
  apply tightest_empty. intros u (r & t & Hr0 & Ht0 & _).
  apply Bool.orb_true_iff in Ee. destruct Ee as [E|E].
  + exact (mem_empty ax _ (proj1 Hax) E
             (hull_mem _ _ _ Hax (ex_intro _ r (conj Hr0 eq_refl)))).
  + exact (mem_empty ay _ (proj1 Hay) E
             (hull_mem _ _ _ Hay (ex_intro _ t (conj Ht0 eq_refl)))).
- apply Bool.orb_false_iff in Ee. destruct Ee as [Nx Ny].
  unfold Interval.with_infsup_raw, Interval.inf_raw, Interval.sup_raw, Generic.constant,
    hypot_rd, hypot_ru.
  cbn [p_hypot mpfr_point].
  destruct (hull_nonempty _ _ Hax Nx) as (u0 & r0 & Hr0 & _).
  destruct (hull_nonempty _ _ Hay Ny) as (v0 & t0 & Ht0 & _).
  apply tightest_lanes_lub.
  + exists (Rhypot r0 t0), r0, t0. split; [exact Hr0|]. split; [exact Ht0 | reflexivity].
  + (* The lower bounds [a1] of [|x|] and [a2] of [|y|] are finite, and
       [|r1| = a1], [|t1| = a2] for some [r1] in [x] and [t1] in [y]. So
       [Rhypot a1 a2] is the least element of the image, as [Rhypot]
       increases in [|r|] and [|t|], and [hypot_rd(a1, a2)] is it rounded
       down. *)
    pose proof (hull_inf_finite _ _ Hax (image_Rabs_nonneg x) Nx) as Fa1.
    pose proof (hull_inf_finite _ _ Hay (image_Rabs_nonneg y) Ny) as Fa2.
    destruct (hull_inf _ _ Hax Nx Fa1) as ((r1 & Hr1 & E1) & Ha1).
    destruct (hull_inf _ _ Hay Ny Fa2) as ((t1 & Ht1 & E2) & Ha2).
    exists (Some (- Rhypot (B2R (opp (fst (rep ax)))) (B2R (opp (fst (rep ay)))))). split.
    * apply tight_lub, tight_Some. split.
      -- exists r1, t1. split; [exact Hr1|]. split; [exact Ht1|].
         rewrite Ropp_involutive, E1, E2. symmetry. apply Rhypot_abs.
      -- intros s (r & t & Hr' & Ht' & Hs).
         assert (Hle : Rhypot (B2R (opp (fst (rep ax)))) (B2R (opp (fst (rep ay))))
                       <= Rhypot r t).
         { rewrite (Rhypot_abs r t). apply Rhypot_le.
           - split; [rewrite E1; apply Rabs_pos|].
             apply Ha1. exists r. split; [exact Hr' | reflexivity].
           - split; [rewrite E2; apply Rabs_pos|].
             apply Ha2. exists t. split; [exact Ht' | reflexivity]. }
         lra.
    * apply round_dn_lane.
      exact (mpfr_fn_round emin emax m RNDD _ _ Hr Hg (Hc RNDD _ _ Fa1 Fa2 I)).
  + (* An upper bound +inf of [|x|] or [|y|] gives reals [r] of [x] or [t]
       of [y] as large as asked in absolute value, with [Rhypot r t] at
       least that, and [hypot_ru] returns +inf there. *)
    destruct (valid_nonempty ax (proj1 Hax) Nx) as (_ & [Fb1|Eb1] & _).
    2: { rewrite Eb1, (mpfr_hypot_inf_l emin emax m Hg Hix). apply lane_ok_inf.
         intros M. destruct (hull_up _ _ Hax Nx Eb1 M) as (u & (r & Hr' & ->) & HM).
         exists (Rhypot r t0). split.
         - exists r, t0. split; [exact Hr'|]. split; [exact Ht0 | reflexivity].
         - pose proof (Rabs_le_Rhypot_l r t0). lra. }
    destruct (valid_nonempty ay (proj1 Hay) Ny) as (_ & [Fb2|Eb2] & _).
    2: { rewrite Eb2, (mpfr_hypot_inf_r emin emax m Hg Hiy). apply lane_ok_inf.
         intros M. destruct (hull_up _ _ Hay Ny Eb2 M) as (u & (t & Ht' & ->) & HM).
         exists (Rhypot r0 t). split.
         - exists r0, t. split; [exact Hr0|]. split; [exact Ht' | reflexivity].
         - pose proof (Rabs_le_Rhypot_r r0 t). lra. }
    (* Finite upper bounds [b1] of [|x|] and [b2] of [|y|] are [|r1|] and
       [|t1|] for some [r1] in [x] and [t1] in [y], so [Rhypot b1 b2] is
       the largest element of the image, and [hypot_ru(b1, b2)] is it
       rounded up. *)
    destruct (hull_sup _ _ Hax Nx Fb1) as ((r1 & Hr1 & E1) & Hb1).
    destruct (hull_sup _ _ Hay Ny Fb2) as ((t1 & Ht1 & E2) & Hb2).
    exists (Some (Rhypot (B2R (snd (rep ax))) (B2R (snd (rep ay))))). split.
    * apply tight_lub, tight_Some. split.
      -- exists r1, t1. split; [exact Hr1|]. split; [exact Ht1|].
         rewrite E1, E2. symmetry. apply Rhypot_abs.
      -- intros s (r & t & Hr' & Ht' & ->). rewrite (Rhypot_abs r t). apply Rhypot_le.
         ++ split; [apply Rabs_pos|].
            apply Hb1. exists r. split; [exact Hr' | reflexivity].
         ++ split; [apply Rabs_pos|].
            apply Hb2. exists t. split; [exact Ht' | reflexivity].
    * apply round_up_lane.
      exact (mpfr_fn_round emin emax m RNDU _ _ Hr Hg (Hc RNDU _ _ Fb1 Fb2 I)).
Qed.

(** Its decorated version returns NaI if either argument is NaI, and
    otherwise the same interval with the strongest decoration, lowered to
    those of the arguments. A nonempty box whose image is bounded by [M]
    is bounded by [M], as [|r|, |t| <= Rhypot r t]. *)
Theorem dec_hypot_correct :
  forall emin emax m x y, range_ok emin emax -> get_d_ok emin emax m -> hypot_ok emin emax m ->
  valid (itv x) -> valid (itv y) ->
  exists z, DecInterval.hypot m x y = Some z /\
    if DecInterval.is_nai x || DecInterval.is_nai y then z = DecInterval.NAI
    else
      is_tightest (image2 Rhypot (itv x) (itv y)) (itv z) /\
      exists d, strongest2 d Rhypot (itv x) (itv y) (itv z) /\
        dec z = dec_min d (dec_min (dec x) (dec y)).
Proof.
intros emin emax m x y Hr Hg Ho Hx Hy. unfold DecInterval.hypot.
destruct (DecInterval.is_nai x || DecInterval.is_nai y) eqn:N;
  [exists DecInterval.NAI; split; reflexivity|].
apply Bool.orb_false_iff in N. destruct N as [Nx Ny].
unfold DecInterval.is_nai in Nx, Ny.
assert (He : dec_min (dec x) (dec y) <> Ill).
{ apply dec_min_not_Ill; intros E; [rewrite E in Nx | rewrite E in Ny];
    discriminate. }
destruct (hypot_correct emin emax m (itv x) (itv y) Hr Hg Ho Hx Hy) as (z & -> & Hz).
cbv beta iota.
exists (DecInterval.set_dec z (dec_min (dec x) (dec y))). split; [reflexivity|].
assert (Hc : dec_min (dec x) (dec y) = Com ->
             (exists r, mem r (itv x)) -> (exists t, mem t (itv y)) ->
             bounded (image2 Rhypot (itv x) (itv y)) ->
             bounded (fun r => mem r (itv x)) /\
             bounded (fun t => mem t (itv y))).
{ intros _ (r0 & Hr0) (t0 & Ht0) (M & HM). split; exists M.
  - intros r Hr'.
    pose proof (HM (Rhypot r t0) (ex_intro _ r (ex_intro _ t0 (conj Hr' (conj Ht0 eq_refl)))))
      as H.
    rewrite (Rabs_pos_eq _ (Rhypot_nonneg r t0)) in H.
    pose proof (Rabs_le_Rhypot_l r t0). lra.
  - intros t Ht'.
    pose proof (HM (Rhypot r0 t) (ex_intro _ r0 (ex_intro _ t (conj Hr0 (conj Ht' eq_refl)))))
      as H.
    rewrite (Rabs_pos_eq _ (Rhypot_nonneg r0 t)) in H.
    pose proof (Rabs_le_Rhypot_r r0 t). lra. }
destruct (set_dec_correct Rhypot Rhypot_continuous _ _ z _ Hx Hy He Hz Hc)
  as (E & d & Hd & Ed).
rewrite E. split; [exact Hz|]. exists d. split; [exact Hd | exact Ed].
Qed.
