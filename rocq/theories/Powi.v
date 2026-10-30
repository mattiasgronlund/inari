(** * [Interval::powi] and [DecInterval::powi]

    [powi_correct]: [Interval::powi] returns the tightest interval that
    contains the image of [x] under IEEE 1788's [pown(x, n)], Stdlib's
    [powerRZ], defined on [pown_dom n], for every [i32] [n].
    [dec_powi_correct]: its decorated version returns NaI for NaI, and
    otherwise the same interval with the strongest decoration, lowered to
    that of the argument. The decoration needs [com_common x] for
    [n <= 0], as an unbounded [x] can then give a bounded result:
    [[1, +inf]] to the power -2 is [[0, 1]], and any nonempty interval to
    the power 0 is [[1, 1]]. Both assume what [Mpfr.v] says of MPFR.

    The code splits on the sign of [n] and on its parity, which the cases
    below follow: for [n < 0], the image of [[0, 0]] is empty
    ([pwi_neg_zero]); an even [n] works on [|x|], where [r^n] decreases
    ([pwi_neg_even]); an odd [n] gives Entire for an [x] with reals on both
    sides of 0 ([pwi_neg_odd_entire]), and otherwise decreases on the side
    of 0 that [x] is on, with a zero bound made +0 for a lower bound and -0
    for an upper bound, so that [pow_si] returns +inf and -inf there
    ([pwi_neg_odd]). For [n >= 0], an even [n] works on [|x|], where [r^n]
    increases ([pwi_pos_even]), and an odd [n] increases on all of R
    ([pwi_pos_odd]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Integer Sign MaxMin AddSub
  DecBinary DivTight MpfrRound MonoInc Abs ComCommon ElemDec PownReal PowMpfr
  RealBounds Sqrt.

Open Scope R_scope.

(** ** Comparisons of a bound with 0 *)

(** A float equal to 0 is a zero. *)
Lemma pwx_eq_zero :
  forall a, Model.eq a Model.zero = true -> is_finite a = true /\ B2R a = 0.
Proof.
intros a H. unfold Model.eq in H.
destruct a as [s|s| |s ma ea Hea]; try (destruct s; discriminate H); try discriminate H.
split; reflexivity.
Qed.

(** A finite float whose value is 0 is a zero. *)
Lemma pwx_B2R_zero :
  forall w : f64, is_finite w = true -> B2R w = 0 -> exists s, w = B754_zero s.
Proof.
intros [s|s| |s mw ew Hw] Fw E; try discriminate Fw; [exists s; reflexivity|].
exfalso. cbn [B2R] in E. apply eq_0_F2R in E. destruct s; discriminate E.
Qed.

Lemma pwx_eq_fin :
  forall a, is_finite a = true -> Model.eq a Model.zero = Req_bool (B2R a) 0.
Proof.
intros a Fa. unfold Model.eq. rewrite Beqb_correct by first [exact Fa | reflexivity].
reflexivity.
Qed.

Lemma pwx_lt_fin :
  forall a, is_finite a = true -> Model.lt a Model.zero = Rlt_bool (B2R a) 0.
Proof.
intros a Fa. unfold Model.lt. rewrite Bltb_correct by first [exact Fa | reflexivity].
reflexivity.
Qed.

Lemma pwx_gt_fin :
  forall b, is_finite b = true -> Model.gt b Model.zero = Rlt_bool 0 (B2R b).
Proof.
intros b Fb. unfold Model.gt. rewrite Bltb_correct by first [exact Fb | reflexivity].
reflexivity.
Qed.

Lemma pwx_le_fin :
  forall a, is_finite a = true -> Model.le a Model.zero = Rle_bool (B2R a) 0.
Proof.
intros a Fa. unfold Model.le. rewrite Bleb_correct by first [exact Fa | reflexivity].
reflexivity.
Qed.

Lemma pwx_ge_fin :
  forall b, is_finite b = true -> Model.ge b Model.zero = Rle_bool 0 (B2R b).
Proof.
intros b Fb. unfold Model.ge. rewrite Bleb_correct by first [exact Fb | reflexivity].
reflexivity.
Qed.

(** [Z.rem n 2 =? 0], the test [rhs % 2 == 0], is [Z.even n]. *)
Lemma pwx_rem_even : forall n, Z.eqb (Z.rem n 2) 0 = Z.even n.
Proof.
intros n. destruct (Z.eqb_spec (Z.rem n 2) 0) as [E|E].
- apply Z.rem_mod_eq_0 in E; [|lia]. rewrite Zmod_even in E.
  destruct (Z.even n); [reflexivity | discriminate E].
- symmetry. destruct (Z.even n) eqn:Ev; [|reflexivity]. exfalso. apply E.
  apply Z.rem_mod_eq_0; [lia|]. rewrite Zmod_even, Ev. reflexivity.
Qed.

(** ** Reals of a nonempty interval *)

(** An upper bound above 0 leaves a real of [x] above 0, and a lower
    bound below 0 one below 0. *)
Lemma pwx_pos_mem :
  forall x, valid x -> Interval.is_empty x = false ->
  Model.gt (Interval.sup_raw x) Model.zero = true -> exists t, 0 < t /\ mem t x.
Proof.
intros x Hx Hn Hb. unfold Interval.sup_raw in Hb.
destruct (nonempty_mem x Hx Hn) as (r0 & Hr0).
destruct (valid_nonempty x Hx Hn) as (_ & [Fb|Eb] & _).
- exists (B2R (snd (rep x))). split; [|exact (mono_mem_sup x Hx Hn Fb)].
  rewrite (pwx_gt_fin _ Fb) in Hb. revert Hb. case Rlt_bool_spec; [easy | discriminate].
- exists (Rmax r0 1). split; [pose proof (Rmax_r r0 1); lra|].
  exact (mono_mem_up x r0 _ Hr0 Eb (Rmax_l r0 1)).
Qed.

Lemma pwx_neg_mem :
  forall x, valid x -> Interval.is_empty x = false ->
  Model.lt (Interval.inf_raw x) Model.zero = true -> exists t, t < 0 /\ mem t x.
Proof.
intros x Hx Hn Ha. unfold Interval.inf_raw in Ha.
destruct (nonempty_mem x Hx Hn) as (r0 & Hr0).
destruct (valid_nonempty x Hx Hn) as ([Fa|Ea] & _ & _).
- exists (B2R (opp (fst (rep x)))). split; [|exact (mono_mem_inf x Hx Hn Fa)].
  rewrite (pwx_lt_fin _ Fa) in Ha. revert Ha. case Rlt_bool_spec; [easy | discriminate].
- exists (Rmin r0 (-1)). split; [pose proof (Rmin_r r0 (-1)); lra|].
  exact (mono_mem_dn x r0 _ Hr0 Ea (Rmin_l r0 (-1))).
Qed.

(** [a <= 0 && b >= 0] tests whether 0 is in [x]. *)
Lemma pwx_mem_zero :
  forall x, valid x -> Interval.is_empty x = false ->
  ((Model.le (Interval.inf_raw x) Model.zero && Model.ge (Interval.sup_raw x) Model.zero)
     = true <-> mem 0 x).
Proof.
intros x Hx Hn. unfold Interval.inf_raw, Interval.sup_raw.
destruct (valid_nonempty x Hx Hn) as (Ha & Hb & _).
rewrite (mem_bounds x 0 Ha Hb). unfold in_bounds.
destruct Ha as [Fa|Ea], Hb as [Fb|Eb].
- rewrite (bound_finite _ Fa), (bound_finite _ Fb), (pwx_le_fin _ Fa), (pwx_ge_fin _ Fb).
  case Rle_bool_spec; case Rle_bool_spec; cbn; intros H1 H2;
    split; intros H; try lra; try discriminate H; try reflexivity; destruct H; lra.
- rewrite (bound_finite _ Fa), Eb, bound_inf, (pwx_le_fin _ Fa).
  case Rle_bool_spec; cbn; intros H1; split; intros H; try lra; try discriminate H;
    try (split; [lra | exact I]); destruct H; lra.
- rewrite Ea, (bound_finite _ Fb), bound_inf, (pwx_ge_fin _ Fb).
  case Rle_bool_spec; cbn; intros H1; split; intros H; try lra; try discriminate H;
    try (split; [exact I | lra]); destruct H; lra.
- rewrite Ea, Eb. cbn. split; intros _; [split; exact I | reflexivity].
Qed.

(** An [x] other than [[0, 0]] has a real other than 0. *)
Lemma pwx_nonzero_mem :
  forall x, valid x -> Interval.is_empty x = false ->
  (Model.eq (Interval.inf_raw x) Model.zero && Model.eq (Interval.sup_raw x) Model.zero) =
    false ->
  exists t, t <> 0 /\ mem t x.
Proof.
intros x Hx Hn Hz. unfold Interval.inf_raw, Interval.sup_raw in Hz.
destruct (nonempty_mem x Hx Hn) as (r0 & Hr0).
destruct (valid_nonempty x Hx Hn) as ([Fa|Ea] & [Fb|Eb] & _).
- apply Bool.andb_false_iff in Hz. destruct Hz as [Hz|Hz].
  + exists (B2R (opp (fst (rep x)))). split; [|exact (mono_mem_inf x Hx Hn Fa)].
    rewrite (pwx_eq_fin _ Fa) in Hz. revert Hz. case Req_bool_spec; [discriminate | easy].
  + exists (B2R (snd (rep x))). split; [|exact (mono_mem_sup x Hx Hn Fb)].
    rewrite (pwx_eq_fin _ Fb) in Hz. revert Hz. case Req_bool_spec; [discriminate | easy].
- exists (Rmax r0 1). split; [pose proof (Rmax_r r0 1); lra|].
  exact (mono_mem_up x r0 _ Hr0 Eb (Rmax_l r0 1)).
- exists (Rmin r0 (-1)). split; [pose proof (Rmin_r r0 (-1)); lra|].
  exact (mono_mem_dn x r0 _ Hr0 Ea (Rmin_l r0 (-1))).
- exists (Rmax r0 1). split; [pose proof (Rmax_r r0 1); lra|].
  exact (mono_mem_up x r0 _ Hr0 Eb (Rmax_l r0 1)).
Qed.

(** ** Lanes of attained bounds *)

Lemma pwx_lo_att :
  forall (S : R -> Prop) L w, S L -> (forall s, S s -> L <= s) ->
  mpfr_round f64_format RNDD L (with_val w) -> lane_ok (fun s => S (- s)) (opp w).
Proof.
intros S L w HL Hmin Hw. apply (pl_lo S L w Hmin); [|exact Hw].
intros eps Heps. exists L. split; [exact HL | lra].
Qed.

Lemma pwx_hi_att :
  forall (S : R -> Prop) U w, S U -> (forall s, S s -> s <= U) ->
  mpfr_round f64_format RNDU U (with_val w) -> lane_ok S w.
Proof.
intros S U w HU Hmax Hw. apply (pl_hi S U w Hmax); [|exact Hw].
intros eps Heps. exists U. split; [exact HU | lra].
Qed.

(** ** [pown] on the reals *)

(** For an odd [n < 0], [r^n] is below 0 for [r < 0], and decreases
    there, as [r^n = - (-r)^n]. *)
Lemma pwx_odd_neg_lt0 :
  forall n r, Z.odd n = true -> r < 0 -> powerRZ r n < 0.
Proof.
intros n r Ho Hr.
replace r with (- - r) by ring. rewrite (pown_odd_opp (- r) n Ho).
pose proof (pown_gt_0 (- r) n ltac:(lra)). lra.
Qed.

Lemma pwx_odd_neg_dec :
  forall n r t, (n < 0)%Z -> Z.odd n = true -> r <= t < 0 -> powerRZ t n <= powerRZ r n.
Proof.
intros n r t Hn Ho H.
replace r with (- - r) by ring. replace t with (- - t) by ring.
rewrite (pown_odd_opp (- r) n Ho), (pown_odd_opp (- t) n Ho).
pose proof (pown_le_neg (- t) (- r) n Hn ltac:(lra)). lra.
Qed.

(** ** The hull [y] of a set [T]

    [Interval::abs] returns the hull of the absolute values of the reals of
    [x] ([abs_correct]). A finite bound of the hull is an element of the
    set, as it is in the hull, so between two elements, which it bounds,
    and an infinite bound leaves elements beyond any real. *)

Lemma pwx_hull_mem : forall T y, is_hull T y -> forall u, T u -> mem u y.
Proof.
intros T y [_ Hy] u Hu. apply Hy. exists u, u.
split; [exact Hu|]. split; [exact Hu|]. lra.
Qed.

Lemma pwx_hull_ne : forall T y, is_hull T y -> (exists u, T u) -> Interval.is_empty y = false.
Proof.
intros T y Hh (u & Hu). destruct (Interval.is_empty y) eqn:E; [|reflexivity].
exfalso. exact (mem_empty y u (proj1 Hh) E (pwx_hull_mem T y Hh u Hu)).
Qed.

Lemma pwx_hull_sup :
  forall T y, is_hull T y -> (exists u, T u) ->
  (is_finite (Interval.sup_raw y) = true /\ T (B2R (Interval.sup_raw y)) /\
   forall u, T u -> u <= B2R (Interval.sup_raw y)) \/
  (Interval.sup_raw y = B754_infinity false /\ forall M, exists u, T u /\ M <= u).
Proof.
intros T y Hh (u0 & Hu0). pose proof (pwx_hull_ne T y Hh (ex_intro _ u0 Hu0)) as Ne.
pose proof (pwx_hull_mem T y Hh) as Mu. destruct Hh as [Vy Hy].
unfold Interval.sup_raw.
destruct (valid_nonempty y Vy Ne) as (_ & [Fd|Ed] & _).
- left. split; [exact Fd|].
  destruct (proj1 (Hy _) (mono_mem_sup y Vy Ne Fd)) as (u & v & Hu & Hv & Huv).
  pose proof (mono_mem_le_sup y v (Mu v Hv) Fd).
  replace (B2R (snd (rep y))) with v by lra. split; [exact Hv|].
  intros w Hw. pose proof (mono_mem_le_sup y w (Mu w Hw) Fd). lra.
- right. split; [exact Ed|]. intros M.
  destruct (proj1 (Hy _) (mono_mem_up y u0 (Rmax M u0) (Mu u0 Hu0) Ed (Rmax_r M u0)))
    as (u & v & Hu & Hv & Huv).
  exists v. split; [exact Hv|]. pose proof (Rmax_l M u0). lra.
Qed.

Lemma pwx_hull_inf :
  forall T y, is_hull T y -> (exists u, T u) ->
  (is_finite (Interval.inf_raw y) = true /\ T (B2R (Interval.inf_raw y)) /\
   forall u, T u -> B2R (Interval.inf_raw y) <= u) \/
  (Interval.inf_raw y = B754_infinity true /\ forall M, exists u, T u /\ u <= M).
Proof.
intros T y Hh (u0 & Hu0). pose proof (pwx_hull_ne T y Hh (ex_intro _ u0 Hu0)) as Ne.
pose proof (pwx_hull_mem T y Hh) as Mu. destruct Hh as [Vy Hy].
unfold Interval.inf_raw.
destruct (valid_nonempty y Vy Ne) as ([Fc|Ec] & _ & _).
- left. split; [exact Fc|].
  destruct (proj1 (Hy _) (mono_mem_inf y Vy Ne Fc)) as (u & v & Hu & Hv & Huv).
  pose proof (mono_inf_le_mem y u (Mu u Hu) Fc).
  replace (B2R (opp (fst (rep y)))) with u by lra. split; [exact Hu|].
  intros w Hw. pose proof (mono_inf_le_mem y w (Mu w Hw) Fc). lra.
- right. split; [exact Ec|]. intros M.
  destruct (proj1 (Hy _) (mono_mem_dn y u0 (Rmin M u0) (Mu u0 Hu0) Ec (Rmin_r M u0)))
    as (u & v & Hu & Hv & Huv).
  exists u. split; [exact Hu|]. pose proof (Rmin_l M u0). lra.
Qed.

Lemma pwi_neg_zero :
  forall n x, (n < 0)%Z -> valid x ->
  (Model.eq (Interval.inf_raw x) Model.zero && Model.eq (Interval.sup_raw x) Model.zero) =
    true ->
  forall s, ~ image_dom (pown_dom n) (fun r => powerRZ r n) x s.
Proof.
intros n x Hn Hx Hz s (r & Hr & Hd & _).
apply andb_prop in Hz. destruct Hz as [Ha Hb].
destruct (pwx_eq_zero _ Ha) as [Fa Ea], (pwx_eq_zero _ Hb) as [Fb Eb].
unfold Interval.inf_raw, Interval.sup_raw in *.
pose proof (mono_inf_le_mem x r Hr Fa). pose proof (mono_mem_le_sup x r Hr Fb).
destruct Hd as [Hd|Hd]; [lia|]. apply Hd. lra.
Qed.

Lemma pwi_neg_even :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pown_ok emin emax m ->
  forall n x, is_i32 n -> (n < 0)%Z -> Z.even n = true ->
  valid x -> Interval.is_empty x = false ->
  (Model.eq (Interval.inf_raw x) Model.zero && Model.eq (Interval.sup_raw x) Model.zero) =
    false ->
  exists y, Interval.abs x = Some y /\
    is_tightest (image_dom (pown_dom n) (fun r => powerRZ r n) x)
      (Interval.with_infsup_raw (pown_rd m (Interval.sup_raw y) n)
         (pown_ru m (Interval.inf_raw y) n)).
Proof.
intros emin emax m Hr Hgd Hp n x Hn32 Hn Hev Hx Hne Hz.
destruct (abs_correct x Hx) as (y & Ey & Hh). exists y. split; [exact Ey|].
destruct (pwx_nonzero_mem x Hx Hne Hz) as (t & Ht & Mt).
assert (Tt : image Rabs x (Rabs t)) by (exists t; split; [exact Mt | reflexivity]).
assert (HT : exists u, image Rabs x u) by (exists (Rabs t); exact Tt).
assert (T0 : forall u, image Rabs x u -> 0 <= u) by (intros u (r & _ & ->); apply Rabs_pos).
pose proof (Rabs_pos_lt t Ht) as Ht0.
(* The values are [u^n] for [u] in [|x|] other than 0, where [u^n]
   decreases. *)
assert (HS : forall u, image Rabs x u -> u <> 0 ->
  image_dom (pown_dom n) (fun r => powerRZ r n) x (powerRZ u n)).
{ intros u (r & Hr' & ->) Hu. exists r. split; [exact Hr'|]. split.
  - right. intros E. apply Hu. rewrite E. apply Rabs_R0.
  - exact (eq_sym (pown_even_abs r n Hev)). }
assert (HS' : forall s, image_dom (pown_dom n) (fun r => powerRZ r n) x s ->
  exists u, image Rabs x u /\ 0 < u /\ s = powerRZ u n).
{ intros s (r & Hr' & Hd & ->). destruct Hd as [Hd|Hd]; [lia|]. exists (Rabs r).
  split; [exists r; split; [exact Hr' | reflexivity]|].
  split; [exact (Rabs_pos_lt r Hd) | exact (pown_even_abs r n Hev)]. }
unfold Interval.with_infsup_raw, Generic.constant. apply tightest_lanes_lub.
- exists (powerRZ t n), t. split; [exact Mt|]. split; [right; exact Ht | reflexivity].
- destruct (pwx_hull_sup _ y Hh HT) as [(Fd & Td & Hd) | (Ed & Hd)].
  + (* A finite upper bound [d] of [|x|] is in [|x|], above 0, and its
       value is the least. *)
    assert (Hd0 : 0 < B2R (Interval.sup_raw y)) by (pose proof (Hd _ Tt); lra).
    apply (pwx_lo_att _ (powerRZ (B2R (Interval.sup_raw y)) n)).
    * apply HS; [exact Td | lra].
    * intros s Hs. destruct (HS' s Hs) as (u & Hu & Hu0 & ->).
      apply pown_le_neg; [exact Hn|]. split; [exact Hu0 | exact (Hd u Hu)].
    * apply (pown_fin emin emax m Hr Hgd Hp RNDD _ n Hn32 Fd). right. lra.
  + (* [d = +inf], and [pow_si(+inf, n) = +0]: the values are above 0 and
       come as close to it as asked. *)
    rewrite Ed. apply (pl_lo _ 0).
    * intros s Hs. destruct (HS' s Hs) as (u & _ & Hu0 & ->).
      pose proof (pown_gt_0 u n Hu0). lra.
    * intros eps Heps. destruct (pown_large_neg n eps Hn Heps) as (r1 & Hr1 & H).
      destruct (Hd r1) as (u & Hu & Hu1). exists (powerRZ u n).
      split; [apply HS; [exact Hu | lra] | pose proof (H u Hu1); lra].
    * exact (pown_pinf_neg emin emax m Hgd Hp RNDD n Hn32 Hn).
- destruct (pwx_hull_inf _ y Hh HT) as [(Fc & Tc & Hc) | (_ & Hc)];
    [|exfalso; destruct (Hc (-1)) as (u & Hu & Hu1); pose proof (T0 u Hu); lra].
  pose proof (T0 _ Tc) as Hc0.
  destruct (Req_dec (B2R (Interval.inf_raw y)) 0) as [Ec|Ec].
  + (* [c = 0], a zero of either sign, and [pow_si(±0, n) = +inf]: 0 is
       in [x], and so are the reals between 0 and [t], whose values rise
       without bound near 0. *)
    destruct (pwx_B2R_zero _ Fc Ec) as (sc & Esc). rewrite Esc.
    unfold pown_ru. rewrite (pown_zero_neg_even emin emax m Hgd Hp RNDU sc n Hn32 Hn Hev).
    destruct Tc as (r & Hr' & Er). rewrite Ec in Er.
    assert (M0 : mem 0 x).
    { replace 0 with r; [exact Hr'|]. revert Er. unfold Rabs. destruct (Rcase_abs r); lra. }
    apply lane_ok_inf. intros M.
    destruct (pown_small_neg n M Hn) as (r1 & Hr1 & H).
    assert (Hq : 0 < Rmin r1 (Rabs t)) by (apply Rmin_glb_lt; lra).
    pose proof (Rmin_l r1 (Rabs t)). pose proof (Rmin_r r1 (Rabs t)).
    exists (powerRZ (Rmin r1 (Rabs t)) n). split; [|apply H; lra].
    apply HS; [|lra].
    destruct (Rlt_or_le 0 t) as [Htp|Htn].
    * rewrite (Rabs_pos_eq t) in * by lra.
      exists (Rmin r1 t). split; [apply (mem_between x 0 t); auto; lra|].
      rewrite Rabs_pos_eq; lra.
    * rewrite (Rabs_left t) in * by lra.
      exists (- Rmin r1 (- t)). split; [apply (mem_between x t 0); auto; lra|].
      rewrite Rabs_Ropp, Rabs_pos_eq; lra.
  + (* [c > 0] is in [|x|], and its value is the largest. *)
    apply (pwx_hi_att _ (powerRZ (B2R (Interval.inf_raw y)) n)).
    * apply HS; [exact Tc | exact Ec].
    * intros s Hs. destruct (HS' s Hs) as (u & Hu & _ & ->).
      apply pown_le_neg; [exact Hn|]. split; [lra | exact (Hc u Hu)].
    * apply (pown_fin emin emax m Hr Hgd Hp RNDU _ n Hn32 Fc). right. exact Ec.
Qed.

Lemma pwi_neg_odd_entire :
  forall n x, (n < 0)%Z -> Z.odd n = true -> valid x ->
  (Model.lt (Interval.inf_raw x) Model.zero && Model.gt (Interval.sup_raw x) Model.zero) =
    true ->
  is_tightest (image_dom (pown_dom n) (fun r => powerRZ r n) x) Interval.ENTIRE.
Proof.
intros n x Hn Hodd Hx Hs.
apply andb_prop in Hs. destruct Hs as [Ha Hb].
assert (Hne : Interval.is_empty x = false).
{ destruct (Interval.is_empty x) eqn:E; [|reflexivity].
  unfold Interval.inf_raw in Ha. rewrite (empty_nan x Hx E) in Ha. discriminate Ha. }
destruct (pwx_neg_mem x Hx Hne Ha) as (t1 & Ht1 & Mt1).
destruct (pwx_pos_mem x Hx Hne Hb) as (t2 & Ht2 & Mt2).
unfold Interval.ENTIRE, Interval.const_interval. apply tightest_lanes_lub.
- exists (powerRZ t2 n), t2. split; [exact Mt2|]. split; [right; lra | reflexivity].
- (* Values as low as asked, near 0 from below. *)
  apply pl_lo_inf. intros M.
  destruct (pown_small_neg n (- M) Hn) as (r0 & Hr0 & H).
  assert (Hr : 0 < Rmin r0 (- t1)) by (apply Rmin_glb_lt; lra).
  pose proof (Rmin_l r0 (- t1)). pose proof (Rmin_r r0 (- t1)).
  exists (powerRZ (- Rmin r0 (- t1)) n). split.
  + exists (- Rmin r0 (- t1)). split; [apply (mem_between x t1 t2); auto; lra|].
    split; [right; lra | reflexivity].
  + rewrite (pown_odd_opp _ n Hodd). specialize (H (Rmin r0 (- t1)) ltac:(lra)). lra.
- (* Values as high as asked, near 0 from above. *)
  apply lane_ok_inf. intros M.
  destruct (pown_small_neg n M Hn) as (r0 & Hr0 & H).
  assert (Hr : 0 < Rmin r0 t2) by (apply Rmin_glb_lt; lra).
  pose proof (Rmin_l r0 t2). pose proof (Rmin_r r0 t2).
  exists (powerRZ (Rmin r0 t2) n). split.
  + exists (Rmin r0 t2). split; [apply (mem_between x t1 t2); auto; lra|].
    split; [right; lra | reflexivity].
  + apply H. lra.
Qed.

Lemma pwi_neg_odd :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pown_ok emin emax m ->
  forall n x, is_i32 n -> (n < 0)%Z -> Z.odd n = true ->
  valid x -> Interval.is_empty x = false ->
  (Model.eq (Interval.inf_raw x) Model.zero && Model.eq (Interval.sup_raw x) Model.zero) =
    false ->
  (Model.lt (Interval.inf_raw x) Model.zero && Model.gt (Interval.sup_raw x) Model.zero) =
    false ->
  let a :=
    if Model.eq (Interval.inf_raw x) Model.zero then Model.zero else Interval.inf_raw x in
  let b :=
    if Model.eq (Interval.sup_raw x) Model.zero then opp Model.zero else Interval.sup_raw x in
  is_tightest (image_dom (pown_dom n) (fun r => powerRZ r n) x)
    (Interval.with_infsup_raw (pown_rd m b n) (pown_ru m a n)).
Proof.
intros emin emax m Hr Hgd Hp n x Hn32 Hn Hodd Hx Hne Hz Hs. cbv zeta.
unfold Interval.inf_raw, Interval.sup_raw in *.
destruct (valid_nonempty x Hx Hne) as (La & Ub & Ord).
destruct (nonempty_mem x Hx Hne) as (r0 & Hr0).
unfold Interval.with_infsup_raw, Generic.constant.
destruct (Model.lt (opp (fst (rep x))) Model.zero) eqn:HA.
- (* [a < 0], so [b <= 0], as the test for reals on both sides of 0 is
     false: [x] is at most 0, and [r^n] decreases below 0. *)
  cbn [andb] in Hs.
  destruct (pwx_neg_mem x Hx Hne HA) as (t1 & Ht1 & Mt1).
  destruct Ub as [Fb|Eb]; [|rewrite Eb in Hs; discriminate Hs].
  assert (Hb0 : B2R (snd (rep x)) <= 0).
  { rewrite (pwx_gt_fin _ Fb) in Hs. revert Hs. case Rlt_bool_spec; [discriminate | easy]. }
  assert (Hx0 : forall r, mem r x -> r <= 0).
  { intros r Hr'. pose proof (mono_mem_le_sup x r Hr' Fb). lra. }
  assert (HAe : Model.eq (opp (fst (rep x))) Model.zero = false).
  { destruct La as [Fa|Ea]; [|rewrite Ea; reflexivity].
    rewrite (pwx_lt_fin _ Fa) in HA. rewrite (pwx_eq_fin _ Fa).
    revert HA. case Rlt_bool_spec; [|discriminate]. intros H _.
    case Req_bool_spec; [lra | reflexivity]. }
  rewrite HAe. apply tightest_lanes_lub.
  + exists (powerRZ t1 n), t1. split; [exact Mt1|]. split; [right; lra | reflexivity].
  + destruct (Model.eq (snd (rep x)) Model.zero) eqn:HBe.
    * (* [b = 0], made -0, and [pow_si(-0, n)] is -inf: the values fall
         without bound near 0. *)
      destruct (pwx_eq_zero _ HBe) as [_ Eb0].
      pose proof (mono_mem_sup x Hx Hne Fb) as M0. rewrite Eb0 in M0.
      change (pown_rd m (opp Model.zero) n)
        with (mpfr_fn_si m (mpfr_pow_si m) RNDD (B754_zero true) n).
      rewrite (pown_zero_neg_odd emin emax m Hgd Hp RNDD true n Hn32 Hn Hodd).
      apply pl_lo_inf. intros M.
      destruct (pown_small_neg n (- M) Hn) as (r1 & Hr1 & H).
      assert (Hp1 : 0 < Rmin r1 (- t1)) by (apply Rmin_glb_lt; lra).
      pose proof (Rmin_l r1 (- t1)). pose proof (Rmin_r r1 (- t1)).
      exists (powerRZ (- Rmin r1 (- t1)) n). split.
      -- exists (- Rmin r1 (- t1)). split; [apply (mem_between x t1 0); auto; lra|].
         split; [right; lra | reflexivity].
      -- rewrite (pown_odd_opp _ n Hodd). specialize (H (Rmin r1 (- t1)) ltac:(lra)). lra.
    * (* [b < 0] is in [x], and its value is the least. *)
      assert (Hb1 : B2R (snd (rep x)) < 0).
      { rewrite (pwx_eq_fin _ Fb) in HBe. revert HBe.
        case Req_bool_spec; [discriminate|]. intros; lra. }
      apply (pwx_lo_att _ (powerRZ (B2R (snd (rep x))) n)).
      -- exists (B2R (snd (rep x))). split; [exact (mono_mem_sup x Hx Hne Fb)|].
         split; [right; lra | reflexivity].
      -- intros s (r & Hr' & _ & ->). apply pwx_odd_neg_dec; [exact Hn | exact Hodd|].
         split; [exact (mono_mem_le_sup x r Hr' Fb) | exact Hb1].
      -- apply (pown_fin emin emax m Hr Hgd Hp RNDD _ n Hn32 Fb). right. lra.
  + destruct La as [Fa|Ea].
    * (* A finite [a < 0] is in [x], and its value is the largest. *)
      assert (Ha1 : B2R (opp (fst (rep x))) < 0).
      { rewrite (pwx_lt_fin _ Fa) in HA. revert HA. case Rlt_bool_spec; [easy | discriminate]. }
      apply (pwx_hi_att _ (powerRZ (B2R (opp (fst (rep x)))) n)).
      -- exists (B2R (opp (fst (rep x)))). split; [exact (mono_mem_inf x Hx Hne Fa)|].
         split; [right; lra | reflexivity].
      -- intros s (r & Hr' & Hd & ->). destruct Hd as [Hd|Hd]; [lia|].
         pose proof (mono_inf_le_mem x r Hr' Fa). pose proof (Hx0 r Hr').
         apply pwx_odd_neg_dec; [exact Hn | exact Hodd | lra].
      -- apply (pown_fin emin emax m Hr Hgd Hp RNDU _ n Hn32 Fa). right. lra.
    * (* [a = -inf], and [pow_si(-inf, n) = -0]: the values are below 0
         and come as close to it as asked. *)
      rewrite Ea. apply (pl_hi _ 0).
      -- intros s (r & Hr' & Hd & ->). destruct Hd as [Hd|Hd]; [lia|].
         pose proof (Hx0 r Hr'). pose proof (pwx_odd_neg_lt0 n r Hodd ltac:(lra)). lra.
      -- intros eps Heps. destruct (pown_large_neg n eps Hn Heps) as (r1 & Hr1 & H).
         pose proof (Rmin_l r0 (- r1)). pose proof (Rmin_r r0 (- r1)).
         exists (powerRZ (Rmin r0 (- r1)) n). split.
         ++ exists (Rmin r0 (- r1)).
            split; [exact (mono_mem_dn x r0 _ Hr0 Ea (Rmin_l r0 (- r1)))|].
            split; [right; lra | reflexivity].
         ++ replace (Rmin r0 (- r1)) with (- - Rmin r0 (- r1)) by ring.
            rewrite (pown_odd_opp _ n Hodd).
            specialize (H (- Rmin r0 (- r1)) ltac:(lra)). lra.
      -- exact (pown_ninf_neg_odd emin emax m Hgd Hp RNDU n Hn32 Hn Hodd).
- (* [a >= 0] is finite, and [x] is not [[0, 0]], so [b > 0]: [x] is at
     least 0, and [r^n] decreases above 0. *)
  destruct La as [Fa|Ea]; [|rewrite Ea in HA; discriminate HA].
  assert (Ha0 : 0 <= B2R (opp (fst (rep x)))).
  { rewrite (pwx_lt_fin _ Fa) in HA. revert HA. case Rlt_bool_spec; [discriminate | easy]. }
  assert (Hx0 : forall r, mem r x -> 0 <= r).
  { intros r Hr'. pose proof (mono_inf_le_mem x r Hr' Fa). lra. }
  assert (HBe : Model.eq (snd (rep x)) Model.zero = false).
  { destruct Ub as [Fb|Eb]; [|rewrite Eb; reflexivity].
    destruct (Model.eq (snd (rep x)) Model.zero) eqn:E; [|reflexivity]. exfalso.
    destruct (pwx_eq_zero _ E) as [_ Eb0].
    assert (HAe : Model.eq (opp (fst (rep x))) Model.zero = true).
    { rewrite (pwx_eq_fin _ Fa). apply Req_bool_true.
      rewrite (bound_finite _ Fa), (bound_finite _ Fb) in Ord. cbn [ordered] in Ord. lra. }
    rewrite HAe in Hz. discriminate Hz. }
  assert (HB : Model.gt (snd (rep x)) Model.zero = true).
  { destruct Ub as [Fb|Eb]; [|rewrite Eb; reflexivity].
    rewrite (pwx_gt_fin _ Fb). rewrite (pwx_eq_fin _ Fb) in HBe. apply Rlt_bool_true.
    rewrite (bound_finite _ Fa), (bound_finite _ Fb) in Ord. cbn [ordered] in Ord.
    revert HBe. case Req_bool_spec; [discriminate|]. intros; lra. }
  destruct (pwx_pos_mem x Hx Hne HB) as (t2 & Ht2 & Mt2).
  rewrite HBe. apply tightest_lanes_lub.
  + exists (powerRZ t2 n), t2. split; [exact Mt2|]. split; [right; lra | reflexivity].
  + destruct Ub as [Fb|Eb].
    * (* A finite [b > 0] is in [x], and its value is the least. *)
      assert (Hb1 : 0 < B2R (snd (rep x))).
      { rewrite (pwx_gt_fin _ Fb) in HB. revert HB. case Rlt_bool_spec; [easy | discriminate]. }
      apply (pwx_lo_att _ (powerRZ (B2R (snd (rep x))) n)).
      -- exists (B2R (snd (rep x))). split; [exact (mono_mem_sup x Hx Hne Fb)|].
         split; [right; lra | reflexivity].
      -- intros s (r & Hr' & Hd & ->). destruct Hd as [Hd|Hd]; [lia|].
         pose proof (Hx0 r Hr'). pose proof (mono_mem_le_sup x r Hr' Fb).
         apply pown_le_neg; [exact Hn | lra].
      -- apply (pown_fin emin emax m Hr Hgd Hp RNDD _ n Hn32 Fb). right. lra.
    * (* [b = +inf], and [pow_si(+inf, n) = +0]: the values are above 0 and
         come as close to it as asked. *)
      rewrite Eb. apply (pl_lo _ 0).
      -- intros s (r & Hr' & Hd & ->). destruct Hd as [Hd|Hd]; [lia|].
         pose proof (Hx0 r Hr'). pose proof (pown_gt_0 r n ltac:(lra)). lra.
      -- intros eps Heps. destruct (pown_large_neg n eps Hn Heps) as (r1 & Hr1 & H).
         pose proof (Rmax_r r0 r1).
         exists (powerRZ (Rmax r0 r1) n). split.
         ++ exists (Rmax r0 r1).
            split; [exact (mono_mem_up x r0 _ Hr0 Eb (Rmax_l r0 r1))|].
            split; [right; lra | reflexivity].
         ++ pose proof (H (Rmax r0 r1) (Rmax_r r0 r1)). lra.
      -- exact (pown_pinf_neg emin emax m Hgd Hp RNDD n Hn32 Hn).
  + destruct (Model.eq (opp (fst (rep x))) Model.zero) eqn:HAe.
    * (* [a = 0], made +0, and [pow_si(+0, n)] is +inf: the values rise
         without bound near 0. *)
      destruct (pwx_eq_zero _ HAe) as [_ Ea0].
      pose proof (mono_mem_inf x Hx Hne Fa) as M0. rewrite Ea0 in M0.
      change (pown_ru m Model.zero n)
        with (mpfr_fn_si m (mpfr_pow_si m) RNDU (B754_zero false) n).
      rewrite (pown_zero_neg_odd emin emax m Hgd Hp RNDU false n Hn32 Hn Hodd).
      apply lane_ok_inf. intros M.
      destruct (pown_small_neg n M Hn) as (r1 & Hr1 & H).
      assert (Hp1 : 0 < Rmin r1 t2) by (apply Rmin_glb_lt; lra).
      pose proof (Rmin_l r1 t2). pose proof (Rmin_r r1 t2).
      exists (powerRZ (Rmin r1 t2) n). split.
      -- exists (Rmin r1 t2). split; [apply (mem_between x 0 t2); auto; lra|].
         split; [right; lra | reflexivity].
      -- apply H. lra.
    * (* [a > 0] is in [x], and its value is the largest. *)
      assert (Ha1 : 0 < B2R (opp (fst (rep x)))).
      { rewrite (pwx_eq_fin _ Fa) in HAe. revert HAe.
        case Req_bool_spec; [discriminate|]. intros; lra. }
      apply (pwx_hi_att _ (powerRZ (B2R (opp (fst (rep x)))) n)).
      -- exists (B2R (opp (fst (rep x)))). split; [exact (mono_mem_inf x Hx Hne Fa)|].
         split; [right; lra | reflexivity].
      -- intros s (r & Hr' & _ & ->). pose proof (mono_inf_le_mem x r Hr' Fa).
         apply pown_le_neg; [exact Hn | lra].
      -- apply (pown_fin emin emax m Hr Hgd Hp RNDU _ n Hn32 Fa). right. lra.
Qed.

Lemma pwi_pos_even :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pown_ok emin emax m ->
  forall n x, is_i32 n -> (0 <= n)%Z -> Z.even n = true ->
  valid x -> Interval.is_empty x = false ->
  exists y, Interval.abs x = Some y /\
    is_tightest (image_dom (pown_dom n) (fun r => powerRZ r n) x)
      (Interval.with_infsup_raw (pown_rd m (Interval.inf_raw y) n)
         (pown_ru m (Interval.sup_raw y) n)).
Proof.
intros emin emax m Hr Hgd Hp n x Hn32 Hn Hev Hx Hne.
destruct (abs_correct x Hx) as (y & Ey & Hh). exists y. split; [exact Ey|].
destruct (nonempty_mem x Hx Hne) as (r0 & Hr0).
assert (HT : exists u, image Rabs x u) by (exists (Rabs r0), r0; split; [exact Hr0 | reflexivity]).
assert (T0 : forall u, image Rabs x u -> 0 <= u) by (intros u (r & _ & ->); apply Rabs_pos).
(* The values are [u^n] for [u] in [|x|], where [u^n] increases. *)
assert (HS : forall u, image Rabs x u ->
  image_dom (pown_dom n) (fun r => powerRZ r n) x (powerRZ u n)).
{ intros u (r & Hr' & ->). exists r. split; [exact Hr'|].
  split; [left; exact Hn | exact (eq_sym (pown_even_abs r n Hev))]. }
assert (HS' : forall s, image_dom (pown_dom n) (fun r => powerRZ r n) x s ->
  exists u, image Rabs x u /\ s = powerRZ u n).
{ intros s (r & Hr' & _ & ->). exists (Rabs r).
  split; [exists r; split; [exact Hr' | reflexivity] | exact (pown_even_abs r n Hev)]. }
unfold Interval.with_infsup_raw, Generic.constant. apply tightest_lanes_lub.
- exists (powerRZ r0 n), r0. split; [exact Hr0|]. split; [left; exact Hn | reflexivity].
- (* The lower bound [c] of [|x|] is in [|x|], and its value is the
     least. *)
  destruct (pwx_hull_inf _ y Hh HT) as [(Fc & Tc & Hc) | (_ & Hc)].
  + apply (pwx_lo_att _ (powerRZ (B2R (Interval.inf_raw y)) n)).
    * apply HS, Tc.
    * intros s Hs. destruct (HS' s Hs) as (u & Hu & ->).
      apply pown_le_pos; [exact Hn|]. split; [exact (T0 _ Tc) | exact (Hc u Hu)].
    * apply (pown_fin emin emax m Hr Hgd Hp RNDD _ n Hn32 Fc). left. exact Hn.
  + exfalso. destruct (Hc (-1)) as (u & Hu & Hu1). pose proof (T0 u Hu). lra.
- destruct (pwx_hull_sup _ y Hh HT) as [(Fd & Td & Hd) | (Ed & Hd)].
  + (* A finite upper bound [d] of [|x|] is in [|x|], and its value is the
       largest. *)
    apply (pwx_hi_att _ (powerRZ (B2R (Interval.sup_raw y)) n)).
    * apply HS, Td.
    * intros s Hs. destruct (HS' s Hs) as (u & Hu & ->).
      apply pown_le_pos; [exact Hn|]. split; [exact (T0 u Hu) | exact (Hd u Hu)].
    * apply (pown_fin emin emax m Hr Hgd Hp RNDU _ n Hn32 Fd). left. exact Hn.
  + rewrite Ed. destruct (Z.eq_dec n 0) as [->|Hn0].
    * (* [n = 0]: every value is 1, and [pow_si(+inf, 0) = 1]. *)
      apply (pwx_hi_att _ 1).
      -- exists r0. split; [exact Hr0|]. split; [left; lia | rewrite pown_0; reflexivity].
      -- intros s (r & _ & _ & ->). rewrite pown_0. lra.
      -- exact (pown_pinf_0 emin emax m Hr Hgd Hp RNDU).
    * (* [n > 0]: [pow_si(+inf, n) = +inf], and the values rise without
         bound. *)
      assert (Hn' : (0 < n)%Z) by lia.
      unfold pown_ru. rewrite (pown_pinf_pos emin emax m Hgd Hp RNDU n Hn32 Hn').
      apply lane_ok_inf. intros M.
      destruct (pown_large_pos n M Hn') as (r1 & Hr1 & H).
      destruct (Hd r1) as (u & Hu & Hu1).
      exists (powerRZ u n). split; [apply HS, Hu | apply H, Hu1].
Qed.

Lemma pwi_pos_odd :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> pown_ok emin emax m ->
  forall n x, is_i32 n -> (0 <= n)%Z -> Z.odd n = true ->
  valid x -> Interval.is_empty x = false ->
  is_tightest (image_dom (pown_dom n) (fun r => powerRZ r n) x)
    (Interval.with_infsup_raw (pown_rd m (Interval.inf_raw x) n)
       (pown_ru m (Interval.sup_raw x) n)).
Proof.
intros emin emax m Hr Hgd Hp n x Hn32 Hn Hodd Hx Hne.
assert (Hn' : (0 < n)%Z).
{ destruct (Z.eq_dec n 0) as [->|Hn0]; [discriminate Hodd | lia]. }
destruct Hp as (Hc & _ & _ & _ & _ & Hpinf & _ & Hninf).
(* [r^n] increases on R, without bound in either direction. *)
assert (Hua : unbounded_above (fun r => powerRZ r n)).
{ intros M. destruct (pown_large_pos n M Hn') as (r0 & Hr0 & H).
  exists r0. apply H, Rle_refl. }
assert (Hub : unbounded_below (fun r => powerRZ r n)).
{ intros M. destruct (pown_large_pos n (- M) Hn') as (r0 & Hr0 & H). exists (- r0).
  rewrite (pown_odd_opp r0 n Hodd). specialize (H r0 (Rle_refl r0)). lra. }
pose proof (mono_inc_correct emin emax m (fun r => powerRZ r n)
  (fun rnd v => mpfr_pow_si m rnd v n) Hr Hgd
  (fun rnd v Fv _ => Hc rnd v n Hn32 Fv (or_introl Hn))
  (or_intror (conj Hub (Hninf RNDD n Hn32 Hn' Hodd)))
  (or_intror (conj Hua (Hpinf RNDU n Hn32 Hn')))
  (fun r t Hrt => pown_le_odd r t n Hn' Hodd Hrt)
  (fun r => pown_cont n r (or_introl Hn)) x Hx) as H.
unfold Interval.mono_inc in H. rewrite Hne in H.
refine (is_tightest_ext _ _ _ _ H).
intros s. split; intros (r & Hr' & _ & Hs); exists r; (split; [exact Hr'|]).
- split; [exact (or_introl Hn) | exact Hs].
- split; [exact I | exact Hs].
Qed.

(** The decoration for [n < 0]: [trv] if 0 is in [x], where [pown] is
    not defined, and [com] otherwise, as [x] is then a subset of the
    domain. *)
Lemma pwx_dec_neg :
  forall n x z, (n < 0)%Z -> valid x -> Interval.is_empty x = false ->
  ((if Model.le (Interval.inf_raw x) Model.zero && Model.ge (Interval.sup_raw x) Model.zero
    then Trv else Com) = Trv /\
   ~ ((exists r, mem r x) /\ forall r, mem r x -> pown_dom n r)) \/
  ((if Model.le (Interval.inf_raw x) Model.zero && Model.ge (Interval.sup_raw x) Model.zero
    then Trv else Com) = Com /\ (forall r, mem r x -> pown_dom n r) /\
   ((0 < n)%Z -> Interval.is_common_interval z = true -> bounded (fun r => mem r x))).
Proof.
intros n x z Hn Hx Hne.
destruct (Model.le (Interval.inf_raw x) Model.zero &&
          Model.ge (Interval.sup_raw x) Model.zero) eqn:H0.
- left. split; [reflexivity|]. intros (_ & Hd).
  apply (pwx_mem_zero x Hx Hne) in H0.
  destruct (Hd 0 H0) as [Hd'|Hd']; [lia | apply Hd'; reflexivity].
- right. split; [reflexivity|]. split; [|intros Hn'; lia].
  intros r Hr'. right. intros E. subst r.
  apply (pwx_mem_zero x Hx Hne) in Hr'. rewrite Hr' in H0. discriminate H0.
Qed.

(** [Interval::powi_impl]: the tightest interval, with [Trv] when [x] is
    not a nonempty subset of the domain, and [Com] when it is a subset, in
    which case, for [n > 0], [x] is bounded if the result is common. *)
Lemma pwi_impl :
  forall emin emax m n x,
  range_ok emin emax -> get_d_ok emin emax m -> pown_ok emin emax m -> is_i32 n ->
  valid x ->
  exists p, Interval.powi_impl m n x = Some p /\
    is_tightest (image_dom (pown_dom n) (fun r => powerRZ r n) x) (fst p) /\
    ((snd p = Trv /\ ~ ((exists r, mem r x) /\ forall r, mem r x -> pown_dom n r)) \/
     (snd p = Com /\ (forall r, mem r x -> pown_dom n r) /\
      ((0 < n)%Z -> Interval.is_common_interval (fst p) = true ->
       bounded (fun r => mem r x)))).
Proof.
intros emin emax m n x Hr Hgd Hp Hn32 Hx.
unfold Interval.powi_impl.
destruct (Interval.is_empty x) eqn:Hne.
- (* An empty [x] is returned, with [trv]. *)
  exists (x, Trv). split; [reflexivity|]. cbn [fst snd].
  rewrite (valid_empty_eq x Hx Hne). split.
  + apply tightest_empty. intros u (r & Hr' & _).
    exact (mem_nan Interval.EMPTY r eq_refl Hr').
  + left. split; [reflexivity|]. intros ((r & Hr') & _).
    exact (mem_nan Interval.EMPTY r eq_refl Hr').
- cbv zeta. rewrite pwx_rem_even.
  destruct (Z.ltb_spec n 0) as [Hn|Hn].
  + (* [n < 0]: the decoration is [trv] exactly when 0 is in [x]. *)
    destruct (Model.eq (Interval.inf_raw x) Model.zero &&
              Model.eq (Interval.sup_raw x) Model.zero) eqn:Hz.
    * eexists. split; [reflexivity|]. cbn [fst snd].
      split; [apply tightest_empty; exact (pwi_neg_zero n x Hn Hx Hz)|].
      apply pwx_dec_neg; assumption.
    * destruct (Z.even n) eqn:Hev.
      -- destruct (pwi_neg_even emin emax m Hr Hgd Hp n x Hn32 Hn Hev Hx Hne Hz)
           as (y & Ey & Ht).
         rewrite Ey. eexists. split; [reflexivity|]. cbn [fst snd].
         split; [exact Ht|]. apply pwx_dec_neg; assumption.
      -- assert (Hodd : Z.odd n = true) by (rewrite <- Z.negb_even, Hev; reflexivity).
         destruct (Model.lt (Interval.inf_raw x) Model.zero &&
                   Model.gt (Interval.sup_raw x) Model.zero) eqn:Hs.
         ++ eexists. split; [reflexivity|]. cbn [fst snd].
            split; [exact (pwi_neg_odd_entire n x Hn Hodd Hx Hs)|].
            apply pwx_dec_neg; assumption.
         ++ eexists. split; [reflexivity|]. cbn [fst snd].
            split; [exact (pwi_neg_odd emin emax m Hr Hgd Hp n x Hn32 Hn Hodd Hx Hne Hz Hs)|].
            apply pwx_dec_neg; assumption.
  + (* [n >= 0]: [com], as the domain is R. For [n > 0], an infinite bound
       of [x] gives an infinite bound of the result, which is then not
       common. *)
    destruct (Z.even n) eqn:Hev.
    * destruct (pwi_pos_even emin emax m Hr Hgd Hp n x Hn32 Hn Hev Hx Hne) as (y & Ey & Ht).
      rewrite Ey. eexists. split; [reflexivity|]. cbn [fst snd].
      split; [exact Ht|]. right. split; [reflexivity|].
      split; [intros r _; left; exact Hn|].
      intros Hn' Hc.
      destruct (abs_correct x Hx) as (y' & Ey' & Hh). rewrite Ey in Ey'.
      injection Ey' as <-.
      destruct (nonempty_mem x Hx Hne) as (r0 & Hr0).
      destruct (pwx_hull_sup _ y Hh (ex_intro _ (Rabs r0) (ex_intro _ r0 (conj Hr0 eq_refl))))
        as [(Fd & _ & Hd) | (Ed & _)].
      -- exists (B2R (Interval.sup_raw y)). intros r Hr'. apply Hd.
         exists r. split; [exact Hr' | reflexivity].
      -- exfalso. unfold Interval.with_infsup_raw, Generic.constant, pown_ru in Hc.
         rewrite Ed, (pown_pinf_pos emin emax m Hgd Hp RNDU n Hn32 Hn'),
           mono_not_common_hi in Hc.
         discriminate Hc.
    * assert (Hodd : Z.odd n = true) by (rewrite <- Z.negb_even, Hev; reflexivity).
      assert (Hn' : (0 < n)%Z).
      { destruct (Z.eq_dec n 0) as [->|Hn0]; [discriminate Hodd | lia]. }
      eexists. split; [reflexivity|]. cbn [fst snd].
      split; [exact (pwi_pos_odd emin emax m Hr Hgd Hp n x Hn32 Hn Hodd Hx Hne)|].
      right. split; [reflexivity|]. split; [intros r _; left; exact Hn|].
      intros _ Hc.
      unfold Interval.with_infsup_raw, Generic.constant, Interval.inf_raw, Interval.sup_raw,
        pown_rd, pown_ru in Hc.
      destruct (valid_nonempty x Hx Hne) as ([Fa|Ea] & [Fb|Eb] & _).
      -- exact (common_bounded x (finite_common x Fa Fb)).
      -- exfalso. rewrite Eb, (pown_pinf_pos emin emax m Hgd Hp RNDU n Hn32 Hn'),
           mono_not_common_hi in Hc.
         discriminate Hc.
      -- exfalso. rewrite Ea, (pown_ninf_pos_odd emin emax m Hgd Hp RNDD n Hn32 Hn' Hodd),
           mono_not_common_lo in Hc.
         discriminate Hc.
      -- exfalso. rewrite Eb, (pown_pinf_pos emin emax m Hgd Hp RNDU n Hn32 Hn'),
           mono_not_common_hi in Hc.
         discriminate Hc.
Qed.

Theorem powi_correct :
  forall emin emax m n x,
  range_ok emin emax -> get_d_ok emin emax m -> pown_ok emin emax m -> is_i32 n ->
  valid x ->
  exists y, Interval.powi m n x = Some y /\
    is_tightest (image_dom (pown_dom n) (fun r => powerRZ r n) x) y.
Proof.
intros emin emax m n x Hr Hgd Hp Hn32 Hx.
destruct (pwi_impl emin emax m n x Hr Hgd Hp Hn32 Hx) as (p & Ep & Ht & _).
exists (fst p). unfold Interval.powi. rewrite Ep. split; [reflexivity | exact Ht].
Qed.

Theorem dec_powi_correct :
  forall emin emax m n x,
  range_ok emin emax -> get_d_ok emin emax m -> pown_ok emin emax m -> is_i32 n ->
  valid (itv x) -> (0 < n)%Z \/ com_common x ->
  exists y, DecInterval.powi m n x = Some y /\
    if DecInterval.is_nai x then y = DecInterval.NAI
    else
      is_tightest (image_dom (pown_dom n) (fun r => powerRZ r n) (itv x)) (itv y) /\
      exists d, strongest_dom (pown_dom n) d (fun r => powerRZ r n) (itv x) (itv y) /\
        dec y = dec_min d (dec x).
Proof.
intros emin emax m n x Hr Hgd Hp Hn32 Hx Hc.
destruct (pwi_impl emin emax m n (itv x) Hr Hgd Hp Hn32 Hx) as (p & Ep & Ht & Hd).
unfold DecInterval.powi. rewrite Ep.
exists (DecInterval.set_dec (fst p) (dec_min (dec x) (snd p))). split; [reflexivity|].
destruct (DecInterval.is_nai x) eqn:Hn.
- (* NaI: [dec_min] keeps [ill], and [set_dec] returns NaI. *)
  destruct x as [z dx]. destruct dx; try discriminate Hn.
  destruct p as [z' []]; reflexivity.
- assert (Hdx : dec x <> Ill).
  { intros E. unfold DecInterval.is_nai in Hn. rewrite E in Hn. discriminate Hn. }
  refine (elem_set_dec_correct (pown_dom n) (fun r => powerRZ r n) x (fst p) (snd p)
    Hx Hdx Ht _ _).
  + intros r _ Hd'. exact (continuity_pt_continue_in _ _ r (pown_cont n r Hd')).
  + (* A [com] [x] is bounded if the result is common: for [n > 0] by
       [pwi_impl], and otherwise as [x] is then common. *)
    destruct Hd as [Hd|(E & HD & Hb)]; [left; exact Hd|].
    right. split; [exact E|]. split; [exact HD|].
    intros Edx Hz. destruct Hc as [Hc|Hc]; [exact (Hb Hc Hz)|].
    exact (common_bounded _ (Hc Edx)).
Qed.
