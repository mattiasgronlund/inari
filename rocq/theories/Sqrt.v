(** * [sqrt] of intervals is tightest and decorated correctly

    [Interval::sqrt] returns the tightest interval that contains the image
    of its argument under the point function [sqrt] on its domain
    [[0, +inf)] ([image_dom] and [sqrt_dom] in [Ieee1788.v]), for either
    value of [has_fma], and [DecInterval::sqrt] decorates it with the
    minimum of the strongest decoration that holds and the decoration of
    its argument, as IEEE 1788 asks of a tightest interval version of a
    function.

    The image of a nonempty [x = [a, b]] is empty if [b < 0], and
    otherwise holds the reals between [sqrt(max(a, 0))] and [sqrt b], with
    no upper bound if [b] is +inf ([sqrt_image]). Those bounds need not be
    floats, so, as for [x + y] in [AddSub.v], the result is the tightest
    interval with bounds that are floats or infinities ([is_tightest]),
    rather than the hull. [x] is stored as [[-a; b]]. If [b < 0],
    [Interval::sqrt] returns [EMPTY]. If [a <= 0], it stores
    [[-0; sqrt1_ru(b)]], i.e. [[0, sqrt1_ru(b)]], and otherwise [neg0]
    turns [[-a; b]] into [[a; b]], [sqrt_rd_ru] takes the square root of
    lane 0 rounded down and of lane 1 rounded up, and [neg0] turns the
    result back. [SqrtRdRu.v] shows that [sqrt1_ru] and [sqrt_rd_ru] are
    Flocq's [Bsqrt mode_UP] and [Bsqrt mode_DN]. The square root of a
    finite [b >= 0] is below [2^512], so it stays finite when rounded up,
    and the second lane is [sqrt b] rounded up, or +inf if [b] is, which is
    the least float or +inf at or above it ([least_lane] in [AddSub.v]).
    The first lane is [-0] or [-(sqrt a rounded down)], the least float at
    or above [-sqrt(max(a, 0))].

    [sqrt] is continuous at each point of its domain, relative to the
    domain, 0 included. The strongest decoration of [sqrt] on [x], with the
    result [z], is:

    - [trv] if [x] is empty, as [def] asks for a nonempty [x]. [z] is then
      empty, and [set_dec] returns [EMPTY], whose [trv] is the minimum of
      [trv] and the decoration of [x].
    - [trv] if [x] has a real below 0, as [def] asks for [x] to be a subset
      of the domain. That is when [a < 0], the test of
      [DecInterval::sqrt], which then passes [trv] to [set_dec].
    - [com] if [0 <= a] and [b] is finite. [x] and [z] are then bounded,
      [z] is common, and [set_dec] keeps the decoration of [x], which is
      its minimum with [com].
    - [dac] if [0 <= a] and [b] is +inf, as [com] asks for a bounded [x].
      [z] is then [[.., +inf]], which is not common, and [set_dec] lowers
      [com] to [dac] and keeps any other decoration, which gives the
      minimum of [dac] and the decoration of [x].

    So, unlike [dec_mul_correct], [dec_sqrt_correct] needs no hypothesis
    that [x] is [com] only if its interval is common: whenever [set_dec]
    gets the decoration of a nonempty [x], [z] is common exactly when [x]
    is bounded. *)

From Stdlib Require Import ZArith Reals Lra Lia Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Spec Ieee1788 Integer Sign MaxMin
  DecBinary AddSub SqrtRdRu.

Open Scope R_scope.

(** ** The image *)

(** The least real of [x] in the domain of [sqrt], if [x] has the lower
    bound [lo] and a real at or above 0. *)
Definition dom_lo (lo : option R) : R :=
  match lo with Some a => Rmax a 0 | None => 0 end.

Lemma dom_lo_nonneg : forall lo, 0 <= dom_lo lo.
Proof.
intros [a|]; cbn [dom_lo]; [apply Rmax_r | apply Rle_refl].
Qed.

Lemma dom_lo_in :
  forall lo hi, ordered lo hi -> below hi 0 -> in_bounds lo hi (dom_lo lo).
Proof.
intros [a|] [b|] Hord Hb; cbn [ordered below dom_lo] in *.
- split; [apply Rmax_l | apply Rmax_le_iff; split; assumption].
- split; [apply Rmax_l | exact I].
- split; [exact I | exact Hb].
- split; exact I.
Qed.

(** The image of [[lo, hi]] under [sqrt] on its domain, if [hi] is at
    least 0, holds the reals between [sqrt (dom_lo lo)] and [sqrt hi]. *)
Lemma sqrt_image :
  forall x lo hi,
  (forall r, mem r x <-> in_bounds lo hi r) -> below hi 0 ->
  forall s, image_dom sqrt_dom sqrt x s <->
    in_bounds (Some (sqrt (dom_lo lo))) (option_map sqrt hi) s.
Proof.
intros x lo hi HX Hb s. split.
- intros (r & Hr & Hd & ->). apply HX in Hr. destruct Hr as [Hlo Hhi].
  unfold sqrt_dom in Hd. split.
  + apply sqrt_le_1_alt.
    destruct lo as [a|]; cbn [dom_lo] in *; [|exact Hd].
    apply Rmax_le_iff. split; assumption.
  + destruct hi as [b|]; cbn [option_map] in *; [|exact I].
    apply sqrt_le_1_alt. exact Hhi.
- (* [s] is the square root of [s * s], which is in [x]. *)
  intros [Hlo Hhi].
  assert (Hs : 0 <= s) by (eapply Rle_trans; [apply sqrt_pos | exact Hlo]).
  exists (s * s). split; [|split].
  + apply HX. split.
    * destruct lo as [a|]; cbn [dom_lo] in *; [|exact I].
      pose proof (sqrt_sqrt (Rmax a 0) (Rmax_r a 0)).
      pose proof (sqrt_pos (Rmax a 0)). pose proof (Rmax_l a 0).
      nra.
    * destruct hi as [b|]; cbn [option_map below] in *; [|exact I].
      pose proof (sqrt_sqrt b Hb). pose proof (sqrt_pos b).
      nra.
  + unfold sqrt_dom. nra.
  + symmetry. apply sqrt_square. exact Hs.
Qed.

(** The reals between [lo] and [hi] have the largest element [hi], and
    their negations have the largest element [-lo]. *)
Lemma tight_in_bounds :
  forall lo hi, ordered lo hi ->
  tight hi (in_bounds lo hi) /\ tight (oopp lo) (fun u => in_bounds lo hi (- u)).
Proof.
intros lo hi Hord. split.
- intros s. exact (below_points lo hi s Hord).
- intros s. cbv beta. rewrite <- (Ropp_involutive s) at 1.
  rewrite below_oopp, (above_points lo hi (- s) Hord).
  split; intros (r & Hr & Hs).
  + exists (- r). rewrite Ropp_involutive. split; [exact Hr | lra].
  + exists (- r). split; [exact Hr | lra].
Qed.

(** ** Signs of the bounds

    [lt] and [le] compare the values of finite floats ([Bltb_correct] and
    [Bleb_correct]), and -inf is below 0 and +inf above. A zero of either
    sign is not below 0, and is at most 0. *)

Lemma upper_lt_zero :
  forall b, upper_ok b ->
  if lt b zero then (match bound b with Some r => r < 0 | None => False end)
  else below (bound b) 0.
Proof.
intros b [Fb| ->]; [|exact I].
unfold lt. rewrite (Bltb_correct _ _ b zero Fb eq_refl), (bound_finite _ Fb).
change (B2R zero) with 0%R.
case Rlt_bool_spec; intros H; cbn [below]; lra.
Qed.

Lemma lower_le_zero :
  forall a, lower_ok a ->
  if le a zero then dom_lo (bound a) = 0 else is_finite a = true /\ 0 < B2R a.
Proof.
intros a [Fa| ->]; [|reflexivity].
unfold le. rewrite (Bleb_correct _ _ a zero Fa eq_refl), (bound_finite _ Fa).
change (B2R zero) with 0%R.
case Rle_bool_spec; intros H.
- cbn [dom_lo]. apply Rmax_right. exact H.
- split; [exact Fa | lra].
Qed.

Lemma lower_lt_zero :
  forall a, lower_ok a ->
  if lt a zero then (match bound a with Some r => r < 0 | None => True end)
  else exists r, bound a = Some r /\ 0 <= r.
Proof.
intros a [Fa| ->]; [|exact I].
unfold lt. rewrite (Bltb_correct _ _ a zero Fa eq_refl), (bound_finite _ Fa).
change (B2R zero) with 0%R.
case Rlt_bool_spec; intros H; [exact H|].
exists (B2R a). split; [reflexivity | exact H].
Qed.

(** An interval whose lower bound is below 0 has a real below 0. *)
Lemma neg_point :
  forall lo hi, ordered lo hi ->
  match lo with Some a => a < 0 | None => True end ->
  exists r, in_bounds lo hi r /\ r < 0.
Proof.
intros [a|] [b|] Hord Ha; cbn [ordered] in Hord.
- exists a. split; [split; [apply Rle_refl | exact Hord] | exact Ha].
- exists a. split; [split; [apply Rle_refl | exact I] | exact Ha].
- exists (Rmin (-1) b). split; [split; [exact I | apply Rmin_r]|].
  generalize (Rmin_l (-1) b). lra.
- exists (-1). split; [split; exact I | lra].
Qed.

Lemma bound_Some_finite : forall a r, bound a = Some r -> is_finite a = true.
Proof.
intros a r. unfold bound. destruct (is_finite a); [reflexivity | discriminate].
Qed.

(** ** The lanes *)

Lemma least_lane_exact :
  forall w, is_finite w = true -> least_lane (Some (B2R w)) w.
Proof.
intros w Fw. split; [left; exact Fw|]. rewrite (bound_finite _ Fw).
split; [intros s Hs; exact Hs|].
intros z _ Hz. exact Hz.
Qed.

(** A finite float that is [r] rounded up is the least float or +inf at or
    above [r]. *)
Lemma least_lane_RU :
  forall r w, is_finite w = true -> B2R w = RU r -> least_lane (Some r) w.
Proof.
intros r w Fw Rw.
destruct (round_UP_pt radix2 fexp64 r) as (_ & Hge & Hmin).
split; [left; exact Fw|]. rewrite (bound_finite _ Fw), Rw. split.
- intros s Hs. cbn [below] in *. lra.
- intros z [Fz| ->] Hz; [|intros s _; exact I].
  rewrite (bound_finite _ Fz) in *.
  (* [z] is a float at or above [r], so at or above [r] rounded up. *)
  assert (Hle : r <= B2R z) by exact (Hz _ (Rle_refl _)).
  pose proof (Hmin _ (generic_format_B2R _ _ z) Hle).
  intros s Hs. cbn [below] in *. lra.
Qed.

(** The negation of a finite float that is [r] rounded down is the least
    float or +inf at or above [-r]. *)
Lemma least_lane_RD :
  forall r w, is_finite w = true -> B2R w = round radix2 fexp64 Zfloor r ->
  least_lane (Some (- r)) (opp w).
Proof.
intros r w Fw Rw.
destruct (round_DN_pt radix2 fexp64 r) as (_ & Hle & Hmax).
assert (Fw' : is_finite (opp w) = true) by (rewrite is_finite_opp; exact Fw).
split; [left; exact Fw'|]. rewrite (bound_finite _ Fw'), B2R_opp, Rw. split.
- intros s Hs. cbn [below] in *. lra.
- intros z [Fz| ->] Hz; [|intros s _; exact I].
  rewrite (bound_finite _ Fz) in *.
  (* [-z] is a float at or below [r], so at or below [r] rounded down. *)
  assert (Hle' : - r <= B2R z) by exact (Hz _ (Rle_refl _)).
  assert (Hf : generic_format radix2 fexp64 (- B2R z)).
  { apply generic_format_opp. apply generic_format_B2R. }
  assert (Hzr : - B2R z <= r) by lra.
  pose proof (Hmax _ Hf Hzr).
  intros s Hs. cbn [below] in *. lra.
Qed.

(** A finite float at or above 0 is a zero or positive, the floats whose
    square root [Bsqrt_correct] says is finite. *)
Lemma nonneg_finite :
  forall b : f64, is_finite b = true -> 0 <= B2R b ->
  match b with
  | B754_zero _ => true
  | B754_finite false _ _ _ => true
  | _ => false
  end = true.
Proof.
intros [s|s| |[|] m e H] Fb Hb; try discriminate Fb; try reflexivity.
exfalso. cbn [B2R] in Hb. revert Hb. apply Rlt_not_le.
apply F2R_lt_0. cbn. lia.
Qed.

(** The second lane of the result, for an upper bound [b] at least 0. *)
Lemma up_lane :
  forall b, upper_ok b -> below (bound b) 0 ->
  least_lane (option_map sqrt (bound b)) (Bsqrt mode_UP b) /\
  (is_finite b = true -> is_finite (Bsqrt mode_UP b) = true).
Proof.
intros b [Fb| ->] Hb.
2: { split; [exact least_lane_inf | intros F; discriminate F]. }
rewrite (bound_finite _ Fb) in *. cbn [below option_map] in *.
destruct (@Bsqrt_correct 53 1024 _ _ mode_UP b) as (HR & HF & _).
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_UP)) with RU in HR.
assert (Fs : is_finite (Bsqrt mode_UP b) = true).
{ rewrite HF. exact (nonneg_finite b Fb Hb). }
split; [exact (least_lane_RU _ _ Fs HR) | intros _; exact Fs].
Qed.

(** The first lane of the result, for a lower bound [a]. *)
Lemma lo_lane :
  forall a, lower_ok a ->
  least_lane (Some (- sqrt (dom_lo (bound a))))
    (if le a zero then opp zero else opp (Bsqrt mode_DN a)) /\
  is_finite (if le a zero then opp zero else opp (Bsqrt mode_DN a)) = true.
Proof.
intros a Ha. pose proof (lower_le_zero a Ha) as H.
destruct (le a zero).
- rewrite H, sqrt_0, Ropp_0. split; [|reflexivity].
  exact (least_lane_exact (opp zero) eq_refl).
- destruct H as (Fa & Ha0).
  destruct (Bsqrt_pos_bound mode_DN a Fa Ha0) as (Fs & _ & Rs & _).
  change (round_mode mode_DN) with Zfloor in Rs.
  assert (E : dom_lo (bound a) = B2R a).
  { rewrite (bound_finite _ Fa). cbn [dom_lo]. apply Rmax_left. lra. }
  rewrite E. split; [exact (least_lane_RD _ _ Fs Rs)|].
  rewrite is_finite_opp. exact Fs.
Qed.

(** The lanes of a nonempty [x] whose upper bound is at least 0 hold the
    tightest interval that contains the image. *)
Lemma sqrt_tightest :
  forall x, valid x -> is_nan (fst (rep x)) = false ->
  below (bound (snd (rep x))) 0 ->
  is_tightest (image_dom sqrt_dom sqrt x)
    {| rep := (if le (opp (fst (rep x))) zero then opp zero
               else opp (Bsqrt mode_DN (opp (fst (rep x)))),
               Bsqrt mode_UP (snd (rep x))) |}.
Proof.
intros x Hx Hn Hb0.
destruct (valid_nonempty x Hx Hn) as (Ha & Hb & Hord).
pose proof (sqrt_image x _ _ (fun r => mem_bounds x r Ha Hb) Hb0) as HI.
set (lo := bound (opp (fst (rep x)))) in *.
set (hi := bound (snd (rep x))) in *.
(* The square root of the least real of [x] in the domain is in the
   image. *)
assert (Hs0 : image_dom sqrt_dom sqrt x (sqrt (dom_lo lo))).
{ exists (dom_lo lo). split; [apply (mem_bounds x _ Ha Hb), dom_lo_in; assumption|].
  split; [apply dom_lo_nonneg | reflexivity]. }
destruct (tight_in_bounds _ _ (in_bounds_ordered _ _ _ (proj1 (HI _) Hs0)))
  as (Thi & Tlo).
apply (tightest_lanes _ _ (oopp (Some (sqrt (dom_lo lo)))) (option_map sqrt hi)).
- exists (sqrt (dom_lo lo)). exact Hs0.
- apply (tight_ext _
    (fun u => in_bounds (Some (sqrt (dom_lo lo))) (option_map sqrt hi) (- u)));
    [|exact Tlo].
  intros u. cbv beta. symmetry. apply HI.
- apply (tight_ext _ (in_bounds (Some (sqrt (dom_lo lo))) (option_map sqrt hi)));
    [|exact Thi].
  intros u. symmetry. apply HI.
- exact (proj1 (lo_lane _ Ha)).
- exact (proj1 (up_lane _ Hb Hb0)).
Qed.

(** ** The computation *)

Lemma sqrt_empty_or_neg :
  forall has_fma x,
  is_nan (fst (rep x)) = true \/ lt (snd (rep x)) zero = true ->
  Interval.sqrt has_fma x = Some Interval.EMPTY.
Proof.
intros has_fma x H.
unfold Interval.sqrt, Interval.is_empty, Interval.inf_raw, Interval.sup_raw.
cbv zeta. destruct H as [H|H]; rewrite H; [reflexivity|].
destruct (is_nan (fst (rep x))); reflexivity.
Qed.

(** [with_infsup_raw zero s] stores [[-0; s]], and [neg0] of
    [[RD(sqrt a); RU(sqrt b)]] stores [[-RD(sqrt a); RU(sqrt b)]]. *)
Lemma sqrt_some :
  forall has_fma x,
  is_nan (fst (rep x)) = false -> lt (snd (rep x)) zero = false ->
  Interval.sqrt has_fma x =
    Some {| rep := (if le (opp (fst (rep x))) zero then opp zero
                    else opp (Bsqrt mode_DN (opp (fst (rep x)))),
                    Bsqrt mode_UP (snd (rep x))) |}.
Proof.
intros has_fma x Hn Hb.
unfold Interval.sqrt, Interval.is_empty, Interval.inf_raw, Interval.sup_raw.
cbv zeta. rewrite Hn, Hb.
destruct (le (opp (fst (rep x))) zero).
- rewrite sqrt1_ru_correct. reflexivity.
- rewrite sqrt_rd_ru_correct. reflexivity.
Qed.

(** ** The theorems *)

(** [Interval::sqrt] returns the tightest interval that contains the image
    of [x] under [sqrt] on its domain. *)
Theorem sqrt_correct :
  forall has_fma x, valid x ->
  exists y, Interval.sqrt has_fma x = Some y /\
    is_tightest (image_dom sqrt_dom sqrt x) y.
Proof.
intros has_fma x Hx.
destruct (is_nan (fst (rep x))) eqn:Hn.
- (* An empty [x] has an empty image. *)
  rewrite (sqrt_empty_or_neg has_fma x (or_introl Hn)).
  eexists. split; [reflexivity|]. apply tightest_empty.
  intros u (r & Hr & _). exact (mem_nan x r (empty_nan x Hx Hn) Hr).
- destruct (valid_nonempty x Hx Hn) as (Ha & Hb & _).
  pose proof (upper_lt_zero _ Hb) as HB.
  destruct (lt (snd (rep x)) zero) eqn:Hlt.
  + (* Every real of [x] is below 0, so outside the domain. *)
    rewrite (sqrt_empty_or_neg has_fma x (or_intror Hlt)).
    eexists. split; [reflexivity|]. apply tightest_empty.
    intros u (r & Hr & Hd & _). apply (mem_bounds x r Ha Hb) in Hr.
    destruct Hr as [_ Hr]. unfold sqrt_dom in Hd.
    destruct (bound (snd (rep x))); [lra | contradiction].
  + rewrite (sqrt_some has_fma x Hn Hlt). eexists. split; [reflexivity|].
    apply sqrt_tightest; assumption.
Qed.

(** ** The decorated version *)

(** A function that is continuous at a point is continuous there relative
    to any set. *)
Lemma continuity_pt_continue_in :
  forall f D r, continuity_pt f r -> continue_in f D r.
Proof.
intros f D r Hc eps Heps. destruct (Hc eps Heps) as (alp & Halp & H).
exists alp. split; [exact Halp|].
intros s [[_ Hs] Hd]. apply H. split; [split; [exact I | exact Hs] | exact Hd].
Qed.

Lemma strongest_dom_Trv :
  forall D f x z, ~ p_dom D Def f x z -> strongest_dom D Trv f x z.
Proof.
intros D f x z H. split; [exact I|].
intros [] He; cbn [discriminant]; try lia; exfalso; apply H; cbn [p_dom] in *.
- exact He.
- destruct He as (Hne & HD & _). split; assumption.
- destruct He as (Hne & HD & _). split; assumption.
Qed.

Lemma strongest_dom_Dac :
  forall D f x z, p_dom D Dac f x z -> ~ p_dom D Com f x z ->
  strongest_dom D Dac f x z.
Proof.
intros D f x z Hd Hc. split; [exact Hd|].
intros [] He; cbn [discriminant]; try lia. exfalso. exact (Hc He).
Qed.

Lemma strongest_dom_Com :
  forall D f x z, p_dom D Com f x z -> strongest_dom D Com f x z.
Proof.
intros D f x z Hc. split; [exact Hc|].
intros [] _; cbn [discriminant]; lia.
Qed.

(** [DecInterval::sqrt] returns NaI for NaI, and otherwise the tightest
    interval, decorated with the decoration that IEEE 1788 asks for. *)
Theorem dec_sqrt_correct :
  forall has_fma x, valid (itv x) ->
  exists y, DecInterval.sqrt has_fma x = Some y /\
    if DecInterval.is_nai x then y = x
    else
      is_tightest (image_dom sqrt_dom sqrt (itv x)) (itv y) /\
      exists d, strongest_dom sqrt_dom d sqrt (itv x) (itv y) /\
        dec y = dec_min d (dec x).
Proof.
intros has_fma x Hx. unfold DecInterval.sqrt.
destruct (DecInterval.is_nai x) eqn:Hnai; [exists x; split; reflexivity|].
assert (Hdx : dec x <> Ill).
{ intros E. unfold DecInterval.is_nai in Hnai. now rewrite E in Hnai. }
destruct (sqrt_correct has_fma (itv x) Hx) as (z & Ez & Hz).
cbv zeta. rewrite Ez. cbv beta iota.
set (d := if lt (Interval.inf_raw (itv x)) zero then Trv else dec x).
assert (Hd : d <> Ill).
{ unfold d. destruct (lt (Interval.inf_raw (itv x)) zero);
    [discriminate | exact Hdx]. }
exists (DecInterval.set_dec z d). split; [reflexivity|].
destruct (Interval.is_empty z) eqn:Ez0.
- (* [z] is empty, so the image is, and [x] has no real in the domain. *)
  pose proof (valid_empty_eq z (proj1 Hz) Ez0) as Ez1.
  rewrite (set_dec_empty_any z d Ez0 Hd). cbn [itv dec DecInterval.EMPTY].
  rewrite <- Ez1. split; [exact Hz|]. exists Trv.
  split; [|symmetry; now apply dec_min_Trv_l].
  apply strongest_dom_Trv. intros Hdef. cbn [p_dom] in Hdef.
  destruct Hdef as ((r & Hr) & HD).
  apply (mem_empty z (sqrt r) (proj1 Hz) Ez0).
  apply (proj1 (proj2 Hz)). exists r.
  split; [exact Hr|]. split; [exact (HD r Hr) | reflexivity].
- (* [x] is nonempty, as its image is, and [b] is at least 0. *)
  assert (Nx : Interval.is_empty (itv x) = false).
  { destruct (Interval.is_empty (itv x)) eqn:Ex; [|reflexivity].
    rewrite (no_mem_empty z (proj1 Hz)) in Ez0; [discriminate Ez0|].
    apply (tightest_no_mem _ _ Hz). intros u (r & Hr & _).
    exact (mem_empty _ r Hx Ex Hr). }
  assert (Hlt : lt (snd (rep (itv x))) zero = false).
  { destruct (lt (snd (rep (itv x))) zero) eqn:Hlt; [|reflexivity].
    rewrite (sqrt_empty_or_neg has_fma (itv x) (or_intror Hlt)) in Ez.
    injection Ez as Ez. subst z. discriminate Ez0. }
  destruct (valid_nonempty (itv x) Hx Nx) as (Ha & Hb & Hord).
  assert (HX : forall r, mem r (itv x) <->
    in_bounds (bound (opp (fst (rep (itv x))))) (bound (snd (rep (itv x)))) r).
  { intros r. exact (mem_bounds _ r Ha Hb). }
  assert (Rz : rep z =
    (if le (opp (fst (rep (itv x)))) zero then opp zero
     else opp (Bsqrt mode_DN (opp (fst (rep (itv x))))),
     Bsqrt mode_UP (snd (rep (itv x))))).
  { rewrite (sqrt_some has_fma (itv x) Nx Hlt) in Ez.
    injection Ez as Ez. subst z. reflexivity. }
  pose proof (upper_lt_zero _ Hb) as HB. rewrite Hlt in HB.
  pose proof (lower_lt_zero _ Ha) as HA.
  unfold d. change (Interval.inf_raw (itv x)) with (opp (fst (rep (itv x)))).
  destruct (lt (opp (fst (rep (itv x)))) zero) eqn:HltA.
  + (* [a < 0]: [x] has a real below 0. *)
    assert (Hc : Trv = Com -> Interval.is_common_interval z = true)
      by (intros E; discriminate E).
    rewrite (set_dec_keep z Trv Ez0 ltac:(discriminate) Hc).
    cbn [itv dec DecInterval.new_unchecked]. split; [exact Hz|].
    exists Trv. split; [|symmetry; now apply dec_min_Trv_l].
    apply strongest_dom_Trv. intros Hdef. cbn [p_dom] in Hdef.
    destruct Hdef as (_ & HD).
    destruct (neg_point _ _ Hord HA) as (r & Hr & Hr0).
    specialize (HD r (proj2 (HX r) Hr)). unfold sqrt_dom in HD. lra.
  + (* [0 <= a]: [x] is in the domain, where [sqrt] is continuous. *)
    destruct HA as (a0 & Ea0 & Ha0).
    assert (HD : forall r, mem r (itv x) -> sqrt_dom r).
    { intros r Hr. apply HX in Hr. rewrite Ea0 in Hr. destruct Hr as [Hr _].
      unfold sqrt_dom. lra. }
    assert (Hcont : forall D r, mem r (itv x) -> continue_in sqrt D r).
    { intros D r Hr. apply continuity_pt_continue_in, continuity_pt_sqrt, HD, Hr. }
    destruct (nonempty_mem _ Hx Nx) as (r0 & Hr0).
    assert (Hdac : p_dom sqrt_dom Dac sqrt (itv x) z).
    { cbn [p_dom]. split; [exists r0; exact Hr0|].
      split; [exact HD|]. intros r Hr. exact (Hcont _ r Hr). }
    destruct Hb as [Fb|Eb].
    * (* A finite [b]: [x] and [z] are bounded. *)
      destruct (lo_lane _ Ha) as (_ & Flo).
      destruct (up_lane _ (or_introl Fb) HB) as (_ & Fup).
      assert (Cz : Interval.is_common_interval z = true).
      { apply finite_common; rewrite Rz; cbn [fst snd].
        - rewrite is_finite_opp. exact Flo.
        - exact (Fup Fb). }
      rewrite (set_dec_keep z (dec x) Ez0 Hdx (fun _ => Cz)).
      cbn [itv dec DecInterval.new_unchecked]. split; [exact Hz|].
      exists Com. split; [|symmetry; apply dec_min_Com_l].
      apply strongest_dom_Com. cbn [p_dom].
      split; [exists r0; exact Hr0|]. split; [exact HD|]. split.
      -- apply common_bounded, finite_common;
           [exact (bound_Some_finite _ _ Ea0) | exact Fb].
      -- split; [intros r Hr; exact (Hcont _ r Hr) | exact (common_bounded z Cz)].
    * (* [b = +inf]: [z] is [[.., +inf]], which is not bounded. *)
      assert (Cz : Interval.is_common_interval z = false).
      { rewrite is_common_interval_lt, infinity_eq, Rz, Eb. cbn [fst snd].
        change (lt (Bsqrt mode_UP (B754_infinity false)) (B754_infinity false))
          with false.
        apply Bool.andb_false_r. }
      rewrite (set_dec_lower z (dec x) Ez0 Cz Hdx).
      cbn [itv dec DecInterval.new_unchecked]. split; [exact Hz|].
      exists Dac. split; [|reflexivity].
      apply strongest_dom_Dac; [exact Hdac|].
      intros Hcom. cbn [p_dom] in Hcom. destruct Hcom as (_ & _ & _ & _ & Bz).
      rewrite (bounded_common z (proj1 Hz) Ez0 Bz) in Cz. discriminate Cz.
Qed.
