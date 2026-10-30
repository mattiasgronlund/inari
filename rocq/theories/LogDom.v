(** * [impl_log!] of intervals and decorated intervals

    The functions that [impl_log!] defines, [ln], [log10] and [log2],
    intersect their argument with [[0, +inf]] and return
    [[f_rd(a), f_ru(b)]] for the intersection [[a, b]], unless it is empty
    or [b <= 0], where [f_rd] and [f_ru] compute, with MPFR, a function [f]
    that is increasing and continuous on [(0, +inf)] and has no bound at
    either end. MPFR returns -inf for a zero and +inf for +inf. The
    decoration is [com] if the argument is in the interior of
    [[0, +inf]], i.e. in [(0, +inf)], and [trv] otherwise. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Integer Sign MaxMin AddSub
  MulTight DecBinary DivTight Sqrt MpfrRound ValidSetOp Interior ElemDec.

Open Scope R_scope.

(** ** The bounds of an interval, which [Atanh.v] uses too *)

(** A lower bound [L] of the reals of a nonempty interval bounds its lower
    bound, which is then finite: a lower bound -inf would let it hold reals
    below [L]. *)
Lemma ld_lower :
  forall z L, valid z -> Interval.is_empty z = false ->
  (forall r, mem r z -> L <= r) ->
  is_finite (Interval.inf_raw z) = true /\ L <= B2R (Interval.inf_raw z).
Proof.
intros z L Hz He HL.
destruct (valid_nonempty z Hz He) as (Ha & Hb & Hord).
pose proof (fun r => mem_bounds z r Ha Hb) as HM.
unfold Interval.inf_raw.
destruct Ha as [Fa | Ea].
- split; [exact Fa|]. apply HL, HM. cbn [in_bounds].
  rewrite (bound_finite _ Fa) in Hord |- *. split; [apply Rle_refl|].
  destruct Hb as [Fb | Eb].
  + rewrite (bound_finite _ Fb) in Hord |- *. exact Hord.
  + rewrite Eb. exact I.
- exfalso.
  assert (H : mem (Rmin (L - 1) (B2R (snd (rep z)))) z).
  { apply HM. cbn [in_bounds]. rewrite Ea, bound_inf. split; [exact I|].
    destruct Hb as [Fb | Eb].
    - rewrite (bound_finite _ Fb). apply Rmin_r.
    - rewrite Eb. exact I. }
  specialize (HL _ H). pose proof (Rmin_l (L - 1) (B2R (snd (rep z)))). lra.
Qed.

(** An upper bound [U] of the reals of a nonempty interval bounds its upper
    bound, which is then finite. *)
Lemma ld_upper :
  forall z U, valid z -> Interval.is_empty z = false ->
  (forall r, mem r z -> r <= U) ->
  is_finite (Interval.sup_raw z) = true /\ B2R (Interval.sup_raw z) <= U.
Proof.
intros z U Hz He HU.
destruct (valid_nonempty z Hz He) as (Ha & Hb & Hord).
pose proof (fun r => mem_bounds z r Ha Hb) as HM.
unfold Interval.sup_raw.
destruct Hb as [Fb | Eb].
- split; [exact Fb|]. apply HU, HM. cbn [in_bounds].
  rewrite (bound_finite _ Fb) in Hord |- *. split; [|apply Rle_refl].
  destruct Ha as [Fa | Ea].
  + rewrite (bound_finite _ Fa) in Hord |- *. exact Hord.
  + rewrite Ea. exact I.
- exfalso.
  assert (H : mem (Rmax (U + 1) (B2R (opp (fst (rep z))))) z).
  { apply HM. cbn [in_bounds]. rewrite Eb, bound_inf. split; [|exact I].
    destruct Ha as [Fa | Ea].
    - rewrite (bound_finite _ Fa). apply Rmax_r.
    - rewrite Ea. exact I. }
  specialize (HU _ H). pose proof (Rmax_l (U + 1) (B2R (opp (fst (rep z))))). lra.
Qed.

(** The reals of a nonempty interval with a finite lower bound. *)
Lemma ld_mem :
  forall z r, valid z -> Interval.is_empty z = false ->
  is_finite (Interval.inf_raw z) = true ->
  (mem r z <-> B2R (Interval.inf_raw z) <= r /\ below (bound (Interval.sup_raw z)) r).
Proof.
intros z r Hz He Fa.
destruct (valid_nonempty z Hz He) as (Ha & Hb & _).
rewrite (mem_bounds z r Ha Hb), in_bounds_iff.
unfold Interval.inf_raw, Interval.sup_raw in *. rewrite (bound_finite _ Fa).
cbn [above]. reflexivity.
Qed.

(** A real of an interval with a finite upper bound is at most that bound. *)
Lemma ld_mem_le_sup :
  forall z r, mem r z -> is_finite (Interval.sup_raw z) = true ->
  r <= B2R (Interval.sup_raw z).
Proof.
intros z r [_ H] Fb. unfold Interval.sup_raw in *.
destruct (snd (rep z)); try discriminate Fb; exact H.
Qed.

(** A finite float of value 0 is a zero. *)
Lemma ld_B2R_zero :
  forall w : f64, is_finite w = true -> B2R w = 0 -> exists s, w = B754_zero s.
Proof.
intros [s|s| |s mw ew Hw] Fw H; try discriminate Fw.
- exists s. reflexivity.
- exfalso. cbn [B2R] in H. apply eq_0_F2R in H. destruct s; discriminate H.
Qed.

(** [mpfr_fn] of a zero toward -inf, for an MPFR function that returns -inf
    for a zero, as [log] does. *)
Lemma ld_fn_zero :
  forall emin emax m g s, get_d_ok emin emax m -> g RNDD (MZero s) = MInf true ->
  mpfr_fn m g RNDD (B754_zero s) = B754_infinity true.
Proof.
intros emin emax m g s (_ & _ & Hinf) Hg. unfold mpfr_fn. cbn [with_val].
rewrite Hg. apply Hinf.
Qed.

(** ** The two cases of [log_impl]

    Either [log_impl] returns [(EMPTY, trv)] for an argument with no real
    above 0, or it calls [f_rd] and [f_ru] on the bounds [a] and [b] of the
    intersection with [[0, +inf]], where [a] is finite and at least 0, [b]
    is +inf or finite and above 0, and the reals of the argument above 0
    are those of [[a, b]]. *)
Lemma ld_log_impl_cases :
  forall f_rd f_ru x, valid x ->
  (Interval.log_impl f_rd f_ru x = (Interval.EMPTY, Trv) /\
   forall r, mem r x -> 0 < r -> False) \/
  (exists a b,
   Interval.log_impl f_rd f_ru x =
     (Interval.with_infsup_raw (f_rd a) (f_ru b),
      if Interval.interior x dom_nonneg then Com else Trv) /\
   is_finite a = true /\ 0 <= B2R a /\
   (b = B754_infinity false \/
    (is_finite b = true /\ 0 < B2R b /\ B2R a <= B2R b)) /\
   forall r, 0 < r -> (mem r x <-> B2R a <= r /\ below (bound b) r)).
Proof.
intros f_rd f_ru x Hx.
pose proof (intersection_valid x dom_nonneg Hx dom_nonneg_valid) as Hxi.
assert (Hm : forall r,
  mem r (Interval.intersection x dom_nonneg) <-> mem r x /\ 0 <= r).
{ intros r. rewrite (intersection_mem x dom_nonneg r Hx dom_nonneg_valid).
  rewrite dom_nonneg_mem. reflexivity. }
unfold Interval.log_impl. cbv zeta. fold dom_nonneg.
set (xi := Interval.intersection x dom_nonneg) in *. clearbody xi.
destruct (Interval.is_empty xi) eqn:He; cbn [orb].
- left. split; [reflexivity|]. intros r Hr Hr0.
  apply (mem_nan xi r (empty_nan xi Hxi He)), Hm. split; [exact Hr | lra].
- (* The reals of [xi] are at least 0, so its lower bound is finite. *)
  destruct (ld_lower xi 0 Hxi He (fun r Hr => proj2 (proj1 (Hm r) Hr)))
    as [Fa Ha0].
  assert (HM : forall r, 0 < r ->
    (mem r x <-> B2R (Interval.inf_raw xi) <= r /\
                 below (bound (Interval.sup_raw xi)) r)).
  { intros r Hr. rewrite <- (ld_mem xi r Hxi He Fa), Hm.
    split; [intros H; split; [exact H | lra] | intros [H _]; exact H]. }
  destruct (valid_nonempty xi Hxi He) as (_ & Hb & Hord).
  destruct Hb as [Fb | Eb].
  + destruct (Model.le (Interval.sup_raw xi) Model.zero) eqn:Hle.
    * (* [b <= 0], and the reals of [x] above 0 would be in [xi]. *)
      left. split; [reflexivity|]. intros r Hr Hr0.
      unfold Model.le in Hle. rewrite Bleb_correct in Hle by easy.
      change (B2R Model.zero) with 0 in Hle. revert Hle.
      case Rle_bool_spec; [intros Hb0 _ | discriminate].
      pose proof (ld_mem_le_sup xi r (proj2 (Hm r) (conj Hr (Rlt_le _ _ Hr0))) Fb).
      lra.
    * right. exists (Interval.inf_raw xi), (Interval.sup_raw xi).
      split; [reflexivity|]. split; [exact Fa|]. split; [exact Ha0|].
      split; [|exact HM]. right. split; [exact Fb|].
      unfold Model.le in Hle. rewrite Bleb_correct in Hle by easy.
      change (B2R Model.zero) with 0 in Hle. revert Hle.
      case Rle_bool_spec; [discriminate | intros Hb0 _].
      split; [exact Hb0|].
      (* [bound_finite] on the unfolded bounds, as [Hord] states them. *)
      rewrite (bound_finite (opp (fst (rep xi))) Fa),
        (bound_finite (snd (rep xi)) Fb) in Hord.
      exact Hord.
  + replace (Model.le (Interval.sup_raw xi) Model.zero) with false
      by (unfold Model.le, Interval.sup_raw; rewrite Eb; reflexivity).
    right. exists (Interval.inf_raw xi), (Interval.sup_raw xi).
    split; [reflexivity|]. split; [exact Fa|]. split; [exact Ha0|].
    split; [left; exact Eb | exact HM].
Qed.

Section Log.

Variables (emin emax : Z) (m : mpfr) (f : R -> R) (g : mpfr_rnd -> mpfr_t -> mpfr_t).

Hypothesis Hrange : range_ok emin emax.
Hypothesis Hget : get_d_ok emin emax m.
Hypothesis Hg : mpfr_correct emin emax log_dom f g.
Hypothesis Hg0 : forall s, g RNDD (MZero s) = MInf true.
Hypothesis Hginf : g RNDU (MInf false) = MInf false.
Hypothesis Hinc : forall r t, 0 < r -> r <= t -> f r <= f t.
Hypothesis Hcont : forall r, 0 < r -> continuity_pt f r.
Hypothesis Hnear0 : forall M b, 0 < b -> exists r, 0 < r <= b /\ f r <= M.
Hypothesis Hbig : forall M, exists r, 0 < r /\ M <= f r.

(** The second case of [ld_log_impl_cases]: the image of [x] under [f] on
    [(0, +inf)] is that of the reals [r > 0] of [[a, b]]. Its least element
    is [f(a)] if [a > 0], and it has no lower bound if [a = 0]. Its largest
    element is [f(b)] if [b] is finite, and it has no upper bound if [b] is
    +inf. *)
Lemma ld_log_lanes :
  forall x a b, is_finite a = true -> 0 <= B2R a ->
  (b = B754_infinity false \/
   (is_finite b = true /\ 0 < B2R b /\ B2R a <= B2R b)) ->
  (forall r, 0 < r -> (mem r x <-> B2R a <= r /\ below (bound b) r)) ->
  is_tightest (image_dom log_dom f x)
    (Interval.with_infsup_raw (mpfr_fn m g RNDD a) (mpfr_fn m g RNDU b)).
Proof using Hrange Hget Hg Hg0 Hginf Hinc Hcont Hnear0 Hbig.
intros x a b Fa Ha0 Hb Hmem.
assert (HS : forall s, image_dom log_dom f x s <->
  exists r, 0 < r /\ B2R a <= r /\ below (bound b) r /\ s = f r).
{ intros s. unfold image_dom, log_dom. split.
  - intros (r & Hr & Hr0 & ->). destruct (proj1 (Hmem r Hr0) Hr) as [Hra Hrb].
    exists r. split; [exact Hr0|]. split; [exact Hra|]. split; [exact Hrb | reflexivity].
  - intros (r & Hr0 & Hra & Hrb & ->). exists r.
    split; [apply (Hmem r Hr0); split; assumption|]. split; [exact Hr0 | reflexivity]. }
(* The reals of [x] above 0 up to some [c > 0]. *)
assert (Hc : exists c, 0 < c /\ B2R a <= c /\ forall r, r <= c -> below (bound b) r).
{ destruct Hb as [-> | (Fb & Hb0 & Hab)].
  - exists (B2R a + 1). split; [lra|]. split; [lra|].
    intros r _. rewrite bound_inf. exact I.
  - exists (B2R b). split; [exact Hb0|]. split; [exact Hab|].
    intros r Hr. rewrite (bound_finite _ Fb). exact Hr. }
destruct Hc as (c & Hc0 & Hac & Hc).
unfold Interval.with_infsup_raw, Generic.constant.
apply tightest_lanes_lub.
- exists (f c). apply HS. exists c.
  split; [exact Hc0|]. split; [exact Hac|]. split; [exact (Hc c (Rle_refl c)) | reflexivity].
- destruct (Rle_lt_or_eq_dec 0 (B2R a) Ha0) as [Ha | Ha].
  + (* [a > 0]: the least element is [f(a)], rounded down. *)
    pose proof (mpfr_fn_correct emin emax m log_dom f g Hrange Hget Hg RNDD a Fa Ha)
      as Hd.
    exists (Some (- f (B2R a))). split; [|exact (round_dn_lane _ _ Hd)].
    apply tight_lub, tight_Some. cbv beta. split.
    * apply HS. exists (B2R a). rewrite Ropp_involutive.
      split; [exact Ha|]. split; [apply Rle_refl|]. split; [|reflexivity].
      apply Hc. exact Hac.
    * intros s Hs. apply HS in Hs. destruct Hs as (r & Hr0 & Hra & _ & Hs).
      pose proof (Hinc (B2R a) r Ha Hra). lra.
  + (* [a = 0]: MPFR returns -inf for a zero, and [f] has no lower bound
       near 0. *)
    destruct (ld_B2R_zero a Fa (eq_sym Ha)) as [s ->].
    rewrite (ld_fn_zero emin emax m g s Hget (Hg0 s)).
    change (opp (B754_infinity true)) with (B754_infinity false : f64).
    apply lane_ok_inf. intros M.
    destruct (Hnear0 (- M) c Hc0) as (r & (Hr0 & Hrc) & HrM).
    exists (- f r). split; [|lra]. cbv beta.
    apply HS. exists r. rewrite Ropp_involutive.
    split; [exact Hr0|]. split; [lra|]. split; [exact (Hc r Hrc) | reflexivity].
- destruct Hb as [-> | (Fb & Hb0 & Hab)].
  + (* [b = +inf]: MPFR returns +inf, and [f] has no upper bound. *)
    rewrite (mpfr_fn_inf emin emax m g RNDU false false Hget Hginf).
    apply lane_ok_inf. intros M.
    destruct (Hbig M) as (r & Hr0 & HrM).
    pose proof (Rmax_l r (B2R a)) as Hr1. pose proof (Rmax_r r (B2R a)) as Hr2.
    exists (f (Rmax r (B2R a))). split.
    * apply HS. exists (Rmax r (B2R a)).
      split; [lra|]. split; [exact Hr2|]. split; [rewrite bound_inf; exact I | reflexivity].
    * pose proof (Hinc r (Rmax r (B2R a)) Hr0 Hr1). lra.
  + (* [b] finite: the largest element is [f(b)], rounded up. *)
    pose proof (mpfr_fn_correct emin emax m log_dom f g Hrange Hget Hg RNDU b Fb Hb0)
      as Hu.
    exists (Some (f (B2R b))). split; [|exact (round_up_lane _ _ Hu)].
    apply tight_lub, tight_Some. split.
    * apply HS. exists (B2R b). split; [exact Hb0|]. split; [exact Hab|].
      split; [rewrite (bound_finite _ Fb); apply Rle_refl | reflexivity].
    * intros s Hs. apply HS in Hs. destruct Hs as (r & Hr0 & _ & Hrb & ->).
      rewrite (bound_finite _ Fb) in Hrb. exact (Hinc r (B2R b) Hr0 Hrb).
Qed.

(** [$f] returns the tightest interval that contains the image. *)
Theorem log_correct :
  forall x, valid x ->
  is_tightest (image_dom log_dom f x)
    (fst (Interval.log_impl (mpfr_fn m g RNDD) (mpfr_fn m g RNDU) x)).
Proof using Hrange Hget Hg Hg0 Hginf Hinc Hcont Hnear0 Hbig.
intros x Hx.
destruct (ld_log_impl_cases (mpfr_fn m g RNDD) (mpfr_fn m g RNDU) x Hx)
  as [[E H0] | (a & b & E & Fa & Ha0 & Hb & Hmem)]; rewrite E; cbn [fst].
- apply tightest_empty. intros u (r & Hr & Hd & _). exact (H0 r Hr Hd).
- exact (ld_log_lanes x a b Fa Ha0 Hb Hmem).
Qed.

(** Its decorated version, [impl_dec!($f, $f_impl)], returns NaI for NaI,
    and otherwise the tightest interval, decorated as IEEE 1788 asks. *)
Theorem dec_log_correct :
  forall x, valid (itv x) ->
  let y :=
    DecInterval.elem_dec_impl
      (Interval.log_impl (mpfr_fn m g RNDD) (mpfr_fn m g RNDU)) x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom log_dom f (itv x)) (itv y) /\
    exists d, strongest_dom log_dom d f (itv x) (itv y) /\ dec y = dec_min d (dec x).
Proof using Hrange Hget Hg Hg0 Hginf Hinc Hcont Hnear0 Hbig.
intros x Hx.
apply (elem_dec_impl_correct log_dom f _ x Hx).
- exact (log_correct (itv x) Hx).
- intros r _ Hr. apply continuity_pt_continue_in, Hcont, Hr.
- destruct (ld_log_impl_cases (mpfr_fn m g RNDD) (mpfr_fn m g RNDU) (itv x) Hx)
    as [[E H0] | (a & b & E & Fa & Ha0 & Hb & Hmem)]; rewrite E; cbn [fst snd].
  + left. split; [reflexivity|]. intros [[r Hr] HD]. exact (H0 r Hr (HD r Hr)).
  + destruct (Interval.interior (itv x) dom_nonneg) eqn:Ei;
      pose proof (interior_mem (itv x) dom_nonneg Hx dom_nonneg_valid) as Hi.
    * (* Each real of [x] has a neighbourhood in [[0, +inf]], so is above
         0. *)
      assert (HD : forall r, mem r (itv x) -> log_dom r).
      { intros r Hr. destruct (proj1 Hi Ei r Hr) as (eps & He & Ht).
        assert (H : mem (r - eps / 2) dom_nonneg).
        { apply Ht. replace (r - eps / 2 - r) with (- (eps / 2)) by ring.
          rewrite Rabs_Ropp, Rabs_pos_eq by lra. lra. }
        apply dom_nonneg_mem in H. unfold log_dom. lra. }
      right. split; [reflexivity|]. split; [exact HD|].
      intros _ Hcom. destruct Hb as [-> | (Fb & Hb0 & Hab)].
      -- (* For [b = +inf], MPFR returns +inf, which is not common. *)
         exfalso.
         rewrite (mpfr_fn_inf emin emax m g RNDU false false Hget Hginf) in Hcom.
         rewrite is_common_interval_lt, infinity_eq in Hcom.
         cbn [Interval.with_infsup_raw rep Generic.constant fst snd] in Hcom.
         change (lt (B754_infinity false : f64) (B754_infinity false)) with false in Hcom.
         rewrite Bool.andb_false_r in Hcom. discriminate Hcom.
      -- (* For [b] finite, the reals of [x] are in [(0, b]]. *)
         exists (B2R b). intros r Hr. pose proof (HD r Hr) as Hr0. unfold log_dom in Hr0.
         destruct (proj1 (Hmem r Hr0) Hr) as [_ Hrb].
         rewrite (bound_finite _ Fb) in Hrb.
         rewrite Rabs_pos_eq by lra. exact Hrb.
    * (* A subset of [(0, +inf)] is in the interior of [[0, +inf]]: a real
         [r] of it has the neighbourhood [(0, 2 r)]. *)
      left. split; [reflexivity|]. intros [_ HD].
      assert (Ht : Interval.interior (itv x) dom_nonneg = true).
      { apply Hi. intros r Hr. pose proof (HD r Hr) as Hr0. unfold log_dom in Hr0.
        exists r. split; [exact Hr0|]. intros t Ht. apply dom_nonneg_mem.
        destruct (Rabs_def2 _ _ Ht). lra. }
      rewrite Ei in Ht. discriminate Ht.
Qed.

End Log.
