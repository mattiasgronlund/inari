(** * [atanh] of intervals and decorated intervals

    [Interval::atanh] intersects its argument with [[-1, 1]] and returns
    [[atanh_rd(a), atanh_ru(b)]] for the intersection [[a, b]], unless it
    is empty, [b <= -1] or [a >= 1]. The domain of [atanh] is [(-1, 1)],
    and MPFR returns -inf at -1 and +inf at 1, which are the bounds of the
    image there, as [atanh] has no bound at either end of its domain. The
    decoration is [com] if the argument is in the interior of [[-1, 1]],
    i.e. in [(-1, 1)], and [trv] otherwise. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr Integer Sign MaxMin AddSub
  MulTight DecBinary DivTight Sqrt MpfrRound ValidSetOp Interior ElemDec LogReal LogDom.

Open Scope R_scope.

(** ** The two cases of [atanh_impl]

    Either [atanh_impl] returns [(EMPTY, trv)] for an argument with no real
    in [(-1, 1)], or it calls [atanh_rd] and [atanh_ru] on the bounds [a]
    and [b] of the intersection with [[-1, 1]], which are finite, with
    [-1 <= a < 1] and [-1 < b <= 1], and the reals of the argument in
    [[-1, 1]] are those of [[a, b]]. As in [ld_log_impl_cases]. *)
Lemma ath_cases :
  forall m x, valid x ->
  (Interval.atanh_impl m x = (Interval.EMPTY, Trv) /\
   forall r, mem r x -> -1 < r < 1 -> False) \/
  (exists a b,
   Interval.atanh_impl m x =
     (Interval.with_infsup_raw (atanh_rd m a) (atanh_ru m b),
      if Interval.interior x dom_unit then Com else Trv) /\
   is_finite a = true /\ is_finite b = true /\
   -1 <= B2R a < 1 /\ -1 < B2R b <= 1 /\ B2R a <= B2R b /\
   forall r, -1 <= r <= 1 -> (mem r x <-> B2R a <= r <= B2R b)).
Proof.
intros m x Hx.
pose proof (intersection_valid x dom_unit Hx dom_unit_valid) as Hxi.
assert (Hm : forall r,
  mem r (Interval.intersection x dom_unit) <-> mem r x /\ -1 <= r <= 1).
{ intros r. rewrite (intersection_mem x dom_unit r Hx dom_unit_valid).
  rewrite dom_unit_mem. reflexivity. }
destruct one_B2R as [F1 E1]. unfold one in F1, E1.
assert (Fm1 : is_finite (opp (of_u64 1)) = true) by (rewrite is_finite_opp; exact F1).
assert (Em1 : B2R (opp (of_u64 1)) = -1) by (rewrite B2R_opp, E1; reflexivity).
unfold Interval.atanh_impl. cbv zeta. fold dom_unit.
set (xi := Interval.intersection x dom_unit) in *. clearbody xi.
destruct (Interval.is_empty xi) eqn:He; cbn [orb].
- left. split; [reflexivity|]. intros r Hr Hr1.
  apply (mem_nan xi r (empty_nan xi Hxi He)), Hm. split; [exact Hr | lra].
- (* The reals of [xi] are in [[-1, 1]], so both its bounds are finite. *)
  destruct (ld_lower xi (-1) Hxi He (fun r Hr => proj1 (proj2 (proj1 (Hm r) Hr))))
    as [Fa Ha1].
  destruct (ld_upper xi 1 Hxi He (fun r Hr => proj2 (proj2 (proj1 (Hm r) Hr))))
    as [Fb Hb1].
  assert (HM : forall r, -1 <= r <= 1 ->
    (mem r x <-> B2R (Interval.inf_raw xi) <= r <= B2R (Interval.sup_raw xi))).
  { intros r Hr. pose proof (ld_mem xi r Hxi He Fa) as H.
    rewrite (bound_finite _ Fb) in H. cbn [below] in H. rewrite <- H, Hm. tauto. }
  assert (Hab : B2R (Interval.inf_raw xi) <= B2R (Interval.sup_raw xi)).
  { destruct (valid_nonempty xi Hxi He) as (_ & _ & Hord).
    (* [bound_finite] on the unfolded bounds, as [Hord] states them. *)
    rewrite (bound_finite (opp (fst (rep xi))) Fa),
      (bound_finite (snd (rep xi)) Fb) in Hord.
    exact Hord. }
  destruct (Model.le (Interval.sup_raw xi) (opp (of_u64 1))) eqn:Hle; cbn [orb].
  + (* [b <= -1], and the reals of [x] in [(-1, 1)] would be in [xi]. *)
    left. split; [reflexivity|]. intros r Hr Hr1.
    unfold Model.le in Hle. rewrite Bleb_correct in Hle by assumption.
    rewrite Em1 in Hle. revert Hle.
    case Rle_bool_spec; [intros Hb0 _ | discriminate].
    assert (Hr' : -1 <= r <= 1) by lra.
    pose proof (proj2 (proj1 (HM r Hr') Hr)). lra.
  + destruct (Model.ge (Interval.inf_raw xi) (of_u64 1)) eqn:Hge.
    * (* [a >= 1], and likewise. *)
      left. split; [reflexivity|]. intros r Hr Hr1.
      unfold Model.ge in Hge. rewrite Bleb_correct in Hge by assumption.
      rewrite E1 in Hge. revert Hge.
      case Rle_bool_spec; [intros Ha0 _ | discriminate].
      assert (Hr' : -1 <= r <= 1) by lra.
      pose proof (proj1 (proj1 (HM r Hr') Hr)). lra.
    * assert (Hb0 : -1 < B2R (Interval.sup_raw xi)).
      { unfold Model.le in Hle. rewrite Bleb_correct in Hle by assumption.
        rewrite Em1 in Hle. revert Hle.
        case Rle_bool_spec; [discriminate | intros H _; exact H]. }
      assert (Ha0 : B2R (Interval.inf_raw xi) < 1).
      { unfold Model.ge in Hge. rewrite Bleb_correct in Hge by assumption.
        rewrite E1 in Hge. revert Hge.
        case Rle_bool_spec; [discriminate | intros H _; exact H]. }
      right. exists (Interval.inf_raw xi), (Interval.sup_raw xi).
      split; [reflexivity|]. split; [exact Fa|]. split; [exact Fb|].
      split; [lra|]. split; [lra|]. split; [exact Hab | exact HM].
Qed.

(** ** The special values of MPFR at -1 and 1 *)

(** [atanh_rd] of a float of value -1 is -inf. *)
Lemma ath_rd_m1 :
  forall emin emax m w, get_d_ok emin emax m -> atanh_ok emin emax m ->
  is_finite w = true -> B2R w = -1 -> atanh_rd m w = B754_infinity true.
Proof.
intros emin emax m w (_ & _ & Hinf) (_ & Hm1 & _) Fw Hw.
unfold atanh_rd, mpfr_fn. rewrite (with_val_finite w Fw) by lra.
rewrite Hw, Hm1. apply Hinf.
Qed.

(** [atanh_ru] of a float of value 1 is +inf. *)
Lemma ath_ru_1 :
  forall emin emax m w, get_d_ok emin emax m -> atanh_ok emin emax m ->
  is_finite w = true -> B2R w = 1 -> atanh_ru m w = B754_infinity false.
Proof.
intros emin emax m w (_ & _ & Hinf) (_ & _ & H1) Fw Hw.
unfold atanh_ru, mpfr_fn. rewrite (with_val_finite w Fw) by lra.
rewrite Hw, H1. apply Hinf.
Qed.

(** ** The image

    The second case of [ath_cases]: the image of [x] under [atanh] on
    [(-1, 1)] is that of the reals of [[a, b]] in [(-1, 1)]. Its least
    element is [atanh(a)] if [a > -1], and it has no lower bound if
    [a = -1]. Its largest element is [atanh(b)] if [b < 1], and it has no
    upper bound if [b = 1]. *)
Lemma ath_lanes :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> atanh_ok emin emax m ->
  forall x a b, is_finite a = true -> is_finite b = true ->
  -1 <= B2R a < 1 -> -1 < B2R b <= 1 -> B2R a <= B2R b ->
  (forall r, -1 <= r <= 1 -> (mem r x <-> B2R a <= r <= B2R b)) ->
  is_tightest (image_dom atanh_dom Ratanh x)
    (Interval.with_infsup_raw (atanh_rd m a) (atanh_ru m b)).
Proof.
intros emin emax m Hrange Hget Hok x a b Fa Fb Ha Hb Hab Hmem.
pose proof Hok as (Hc & _ & _).
assert (HS : forall s, image_dom atanh_dom Ratanh x s <->
  exists r, -1 < r < 1 /\ B2R a <= r <= B2R b /\ s = Ratanh r).
{ intros s. unfold image_dom, atanh_dom. split.
  - intros (r & Hrx & Hr & ->). assert (Hr' : -1 <= r <= 1) by lra.
    exists r. split; [exact Hr|]. split; [exact (proj1 (Hmem r Hr') Hrx) | reflexivity].
  - intros (r & Hr & Hrab & ->). assert (Hr' : -1 <= r <= 1) by lra.
    exists r. split; [exact (proj2 (Hmem r Hr') Hrab)|]. split; [exact Hr | reflexivity]. }
unfold Interval.with_infsup_raw, Generic.constant.
apply tightest_lanes_lub.
- (* The midpoint of [[a, b]] is in [(-1, 1)]. *)
  exists (Ratanh ((B2R a + B2R b) / 2)). apply HS. exists ((B2R a + B2R b) / 2).
  split; [lra|]. split; [lra | reflexivity].
- destruct (Rle_lt_or_eq_dec (-1) (B2R a) (proj1 Ha)) as [Ha1 | Ha1].
  + (* [a > -1]: the least element is [atanh(a)], rounded down. *)
    pose proof (mpfr_fn_correct emin emax m atanh_dom Ratanh (mpfr_atanh m)
      Hrange Hget Hc RNDD a Fa (conj Ha1 (proj2 Ha))) as Hd.
    exists (Some (- Ratanh (B2R a))). split; [|exact (round_dn_lane _ _ Hd)].
    apply tight_lub, tight_Some. cbv beta. split.
    * apply HS. exists (B2R a). rewrite Ropp_involutive.
      split; [lra|]. split; [lra | reflexivity].
    * intros s Hs. apply HS in Hs. destruct Hs as (r & Hr & Hrab & Hs).
      pose proof (atanh_inc (B2R a) r Ha1 (proj1 Hrab) (proj2 Hr)). lra.
  + (* [a = -1]: MPFR returns -inf, and [atanh] has no lower bound near
       -1. *)
    rewrite (ath_rd_m1 emin emax m a Hget Hok Fa (eq_sym Ha1)).
    change (opp (B754_infinity true)) with (B754_infinity false : f64).
    apply lane_ok_inf. intros M.
    destruct (atanh_near_m1 (- M) (B2R b) (proj1 Hb)) as (r & Hr & Hr1 & HrM).
    exists (- Ratanh r). split; [|lra]. cbv beta.
    apply HS. exists r. rewrite Ropp_involutive.
    split; [lra|]. split; [lra | reflexivity].
- destruct (Rle_lt_or_eq_dec (B2R b) 1 (proj2 Hb)) as [Hb1 | Hb1].
  + (* [b < 1]: the largest element is [atanh(b)], rounded up. *)
    pose proof (mpfr_fn_correct emin emax m atanh_dom Ratanh (mpfr_atanh m)
      Hrange Hget Hc RNDU b Fb (conj (proj1 Hb) Hb1)) as Hu.
    exists (Some (Ratanh (B2R b))). split; [|exact (round_up_lane _ _ Hu)].
    apply tight_lub, tight_Some. split.
    * apply HS. exists (B2R b). split; [lra|]. split; [lra | reflexivity].
    * intros s Hs. apply HS in Hs. destruct Hs as (r & Hr & Hrab & ->).
      exact (atanh_inc r (B2R b) (proj1 Hr) (proj2 Hrab) Hb1).
  + (* [b = 1]: MPFR returns +inf, and [atanh] has no upper bound near 1. *)
    rewrite (ath_ru_1 emin emax m b Hget Hok Fb Hb1).
    apply lane_ok_inf. intros M.
    destruct (atanh_near_1 M (B2R a) (proj2 Ha)) as (r & Hr & Hr1 & HrM).
    exists (Ratanh r). split; [|exact HrM].
    apply HS. exists r. split; [lra|]. split; [lra | reflexivity].
Qed.

(** ** The theorems *)

(** [Interval::atanh] returns the tightest interval that contains the
    image. *)
Theorem atanh_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> atanh_ok emin emax m ->
  forall x, valid x -> is_tightest (image_dom atanh_dom Ratanh x) (Interval.atanh m x).
Proof.
intros emin emax m Hrange Hget Hok x Hx. unfold Interval.atanh.
destruct (ath_cases m x Hx)
  as [[E H0] | (a & b & E & Fa & Fb & Ha & Hb & Hab & Hmem)]; rewrite E; cbn [fst].
- apply tightest_empty. intros u (r & Hr & Hd & _). exact (H0 r Hr Hd).
- exact (ath_lanes emin emax m Hrange Hget Hok x a b Fa Fb Ha Hb Hab Hmem).
Qed.

(** [DecInterval::atanh] returns NaI for NaI, and otherwise the tightest
    interval, decorated as IEEE 1788 asks. *)
Theorem dec_atanh_correct :
  forall emin emax m, range_ok emin emax -> get_d_ok emin emax m -> atanh_ok emin emax m ->
  forall x, valid (itv x) ->
  let y := DecInterval.atanh m x in
  if DecInterval.is_nai x then y = DecInterval.NAI
  else
    is_tightest (image_dom atanh_dom Ratanh (itv x)) (itv y) /\
    exists d, strongest_dom atanh_dom d Ratanh (itv x) (itv y) /\
      dec y = dec_min d (dec x).
Proof.
intros emin emax m Hrange Hget Hok x Hx. unfold DecInterval.atanh.
apply (elem_dec_impl_correct atanh_dom Ratanh _ x Hx).
- exact (atanh_correct emin emax m Hrange Hget Hok (itv x) Hx).
- intros r _ Hr. apply continuity_pt_continue_in, atanh_cont, Hr.
- destruct (ath_cases m (itv x) Hx)
    as [[E H0] | (a & b & E & Fa & Fb & Ha & Hb & Hab & Hmem)]; rewrite E; cbn [fst snd].
  + left. split; [reflexivity|]. intros [[r Hr] HD]. exact (H0 r Hr (HD r Hr)).
  + destruct (Interval.interior (itv x) dom_unit) eqn:Ei;
      pose proof (interior_mem (itv x) dom_unit Hx dom_unit_valid) as Hi.
    * (* Each real of [x] has a neighbourhood in [[-1, 1]], so is in
         [(-1, 1)]. *)
      assert (HD : forall r, mem r (itv x) -> atanh_dom r).
      { intros r Hr. destruct (proj1 Hi Ei r Hr) as (eps & He & Ht).
        assert (H1 : mem (r - eps / 2) dom_unit).
        { apply Ht. replace (r - eps / 2 - r) with (- (eps / 2)) by ring.
          rewrite Rabs_Ropp, Rabs_pos_eq by lra. lra. }
        assert (H2 : mem (r + eps / 2) dom_unit).
        { apply Ht. replace (r + eps / 2 - r) with (eps / 2) by ring.
          rewrite Rabs_pos_eq by lra. lra. }
        apply dom_unit_mem in H1. apply dom_unit_mem in H2. unfold atanh_dom. lra. }
      (* The reals of [x] are then in [(-1, 1)], so [x] is bounded. *)
      right. split; [reflexivity|]. split; [exact HD|].
      intros _ _. exists 1. intros r Hr. pose proof (HD r Hr) as Hr1.
      unfold atanh_dom in Hr1. apply Rabs_le. lra.
    * (* A subset of [(-1, 1)] is in the interior of [[-1, 1]]: a real [r]
         of it has the neighbourhood of radius [min (r + 1) (1 - r)]. *)
      left. split; [reflexivity|]. intros [_ HD].
      assert (Ht : Interval.interior (itv x) dom_unit = true).
      { apply Hi. intros r Hr. pose proof (HD r Hr) as Hr1. unfold atanh_dom in Hr1.
        exists (Rmin (r + 1) (1 - r)). split; [apply Rmin_glb_lt; lra|].
        intros t Ht. apply dom_unit_mem.
        pose proof (Rmin_l (r + 1) (1 - r)). pose proof (Rmin_r (r + 1) (1 - r)).
        destruct (Rabs_def2 _ _ Ht). lra. }
      rewrite Ei in Ht. discriminate Ht.
Qed.
