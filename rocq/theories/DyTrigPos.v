(** * The signs of sin and cos in the dyadic kernel, and tan's divisor

    For [0 <= ρ <= 4/5], the series of [series] stay in [(0, 1]]:
    Horner's scheme starts from [[0, 1]], and each step [1 - z t / d]
    with [z = ρ^2 <= 0.64] and [d >= 2] keeps the enclosure in [[0, 1]]
    and above 0 after the first step, and [sin ρ] is below 1
    ([series_pos] and [series_sin_lt1] of [DyTrigSeriesPos.v]). With
    [reduce_pos] and [reduce_le] of [DyTrigSign.v], the enclosures of
    [sin x] and [cos x] at every level exclude 0 ([ev_sin_sign],
    [ev_cos_sign]), and so does the divisor of [tan]'s [Encl::div]
    ([tan_div_pos]). [Dyadic.ziv] returns a bound of one of these
    enclosures rounded, at a level where a test passes or at its cap, so
    its sign is that of the real number ([ziv_sign] of [DyTrigZivSign.v]),
    and the rules are correct roundings. So [sin_dir x false] is below 0 exactly
    where [sin x] is ([sin_dir_sign]), and [cos_dir x true] above 0
    exactly where [cos x] is ([cos_dir_sign]), at every finite [x],
    whether a rounding test passes or not: these are the signs that
    [quadrant] of [Model.v] reads. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary LogReal DyRound DyConv DyOps DyDriver DyGrow
  DyConst DyExpCore DyExpRules DyExp ExpReal DyHypRules DyLogRules DyLogCore DyLog DyLogHyp
  TrigSeries DyTrigTiny DyCosSmall DySinSmall DyTanSmall DyTrigReduce DyTrigCore MpfrRound DyTrig
  DyTrigSign DyTrigSeriesPos DyTrigZivSign.
From Inari Require FastTrig.

Open Scope Z_scope.

(** ** Helpers *)

(** A value on the side below a negative real is below 0, and one on the
    side above a positive real is above 0. The signs of a rounding are
    [rnd_dn_neg] and [rnd_up_pos] of [DyTrigZivSign.v]. *)
Lemma dp_side_neg :
  forall r v, f64_side false r v -> (r < 0)%R -> Model.lt v Model.zero = true.
Proof.
intros r v S Hr.
destruct v as [s|[|]| |s m e B]; cbn [f64_side negb] in S.
- cbn [B2R] in S. lra.
- reflexivity.
- discriminate S.
- contradiction.
- unfold Model.lt. rewrite Bltb_correct by reflexivity. change (B2R Model.zero) with 0%R.
  apply Rlt_bool_true. lra.
Qed.

Lemma dp_side_pos :
  forall r v, f64_side true r v -> (0 < r)%R -> Model.lt Model.zero v = true.
Proof.
intros r v S Hr.
destruct v as [s|[|]| |s m e B]; cbn [f64_side negb] in S.
- cbn [B2R] in S. lra.
- discriminate S.
- reflexivity.
- contradiction.
- unfold Model.lt. rewrite Bltb_correct by reflexivity. change (B2R Model.zero) with 0%R.
  apply Rlt_bool_true. lra.
Qed.

(** [reduce] at [t = 0] takes its first branch ([t <= 201/256]): the
    quadrant is 0 and [ρ] is the point 0. *)
Lemma dp_reduce_zero :
  forall n t quad neg r,
  level_ok n -> is_finite t = true -> B2R t = 0%R ->
  DyadicTrig.reduce n t = Some (quad, neg, r) ->
  quad = 0 /\ lo_R r = 0%R /\ hi_R r = 0%R.
Proof.
intros n t quad neg r Hn Ft Ht H.
destruct no_reduce_R as [Fnr Vnr].
assert (Hle : Model.le t DyadicTrig.no_reduce = true).
{ unfold Model.le. rewrite Bleb_correct by assumption. rewrite Ht, Vnr.
  apply Rle_bool_true. lra. }
unfold DyadicTrig.reduce in H. rewrite Hle in H.
destruct (Dyadic.encl_point n t) as [c|] eqn:Ec; [|discriminate H].
cbv beta iota in H. injection H as Hq Hng Hr. subst quad neg r.
destruct (point_step n t c Hn Ec) as (_ & _ & Hlo & Hhi & _).
rewrite Hlo, Hhi, Ht. split; [reflexivity | split; reflexivity].
Qed.

(** The bounds of [reduce_bounds], with [0 < lo ρ] at a quadrant other
    than 0 ([t <> 0] there, by [dp_reduce_zero]). *)
Lemma dp_reduce :
  forall n t quad neg r,
  level_ok n -> is_finite t = true -> (0 <= B2R t)%R ->
  DyadicTrig.reduce n t = Some (quad, neg, r) ->
  encl_ok n r /\ encl_le (2 ^ 15) r /\ (0 <= lo_R r)%R /\ (hi_R r <= 4 / 5)%R /\
  (quad <> 0 -> (0 < lo_R r)%R).
Proof.
intros n t quad neg r Hn Ft Ht H.
destruct (reduce_correct n t quad neg r Hn Ft Ht H) as (Or & Lr & _).
destruct (reduce_bounds n t quad neg r Hn Ft Ht H) as (A & B & C).
split; [exact Or|]. split; [exact Lr|]. split; [exact A|]. split; [exact B|].
intros Hq. apply C. destruct (Rle_lt_or_eq_dec 0 (B2R t) Ht) as [P|Z]; [exact P|].
exfalso. apply Hq. exact (proj1 (dp_reduce_zero n t quad neg r Hn Ft (eq_sym Z) H)).
Qed.

(** [series_correct] at [ρ = lo r], for the bookkeeping of the result. *)
Lemma dp_series_ok :
  forall n r odd c,
  level_ok n -> encl_ok n r -> encl_le (2 ^ 15) r -> (0 <= lo_R r)%R -> (hi_R r <= 4 / 5)%R ->
  DyadicTrig.series n r odd = Some c -> encl_ok n c /\ encl_le (2 ^ 50) c.
Proof.
intros n r odd c Hn Or Lr L0 H45 H.
assert (Hh : encl_has r (lo_R r)).
{ destruct Or as (_ & _ & Ole). unfold encl_has, lo_R. lra. }
assert (Hb : (-1 <= lo_R r <= 1)%R).
{ destruct Or as (_ & _ & Ole). unfold lo_R, hi_R in *. lra. }
destruct (series_correct n r odd c (2 ^ 15) (lo_R r) Hn Or Lr ltac:(lia) Hh Hb H)
  as (Oc & Lc & _).
split; assumption.
Qed.

(** At [ρ = 0] the series of [sin] is [ρ T] with a lower bound 0: every
    product of the bounds is 0. Its steps are those of [series_correct]. *)
Lemma dp_series_zero :
  forall n r s E,
  level_ok n -> encl_ok n r -> encl_le E r -> 0 <= E <= 2 ^ 34 ->
  lo_R r = 0%R -> hi_R r = 0%R ->
  DyadicTrig.series n r true = Some s -> lo_R s = 0%R.
Proof.
intros n r s E Hn Hr HrE HE Hlo Hhi H. unfold DyadicTrig.series in H.
destruct (Dyadic.encl_point n DyadicExp.one) as [one_e|] eqn:E1; [|discriminate H].
destruct (Dyadic.encl_mul n r r) as [z|] eqn:Ez; [|discriminate H].
set (K := DyadicTrig.terms n z) in H.
assert (Hk : 0 <= K <= 389) by exact (tc_terms n z Hn).
clearbody K.
set (t0 := {| Dyadic.en_lo := Dyadic.dy_zero n; Dyadic.en_hi := Dyadic.en_hi one_e |}) in H.
destruct (DyadicTrig.series_loop n one_e z (Z.b2z true) (Z.to_nat K) t0) as [t|] eqn:Et;
  [|discriminate H].
cbv beta iota in H.
destruct (point_has n _ _ Hn E1) as (Ho & HoE & Ho1). rewrite dexp_one_R in Ho1.
assert (HE1 : 0 <= E <= 2 ^ 60) by lia.
destruct (mul_step n r r z _ _ Hn Hr Hr HrE HrE HE1 HE1 Ez) as (Hz & HzE & Hzv).
destruct (dy_zero_ok n) as (Oz & Vz & _).
assert (Hhi1 : Dyadic.dy_R (Dyadic.en_hi one_e) = 1%R).
{ destruct (point_step n _ _ Hn E1) as (_ & _ & _ & Hh & _).
  unfold hi_R in Hh. rewrite Hh. exact dexp_one_R. }
assert (Ht0 : encl_ok n t0).
{ destruct Ho as (_ & Ohi & _).
  unfold encl_ok, t0; cbn [Dyadic.en_lo Dyadic.en_hi].
  split; [exact Oz|]. split; [exact Ohi|]. rewrite Vz, Hhi1. lra. }
assert (Ht0E : encl_le (2 ^ 13) t0).
{ destruct HoE as (_ & Lhi).
  unfold encl_le, t0; cbn [Dyadic.en_lo Dyadic.en_hi Dyadic.dy_zero Dyadic.dy_exp].
  split; [lia | exact Lhi]. }
assert (Hrho1 : (Rabs 0 <= 1)%R) by (rewrite Rabs_R0; lra).
destruct (trig_tail_bounds true (Z.to_nat K) 0%R Hrho1) as (T & HT01 & HT).
assert (HT0 : encl_has t0 T).
{ unfold encl_has, t0; cbn [Dyadic.en_lo Dyadic.en_hi]. rewrite Vz, Hhi1. lra. }
assert (Hrh : encl_has r 0%R) by (unfold encl_has; unfold lo_R, hi_R in Hlo, Hhi; lra).
assert (HEz : 0 <= E + E + 2 ^ 13 <= 2 ^ 40) by lia.
assert (HE0 : 0 <= (2 ^ 13 : Z)) by lia.
assert (HKi : Z.of_nat (Z.to_nat K) <= 389) by lia.
assert (HEb : 2 ^ 13 + Z.of_nat (Z.to_nat K) * (E + E + 2 ^ 13 + 2 ^ 15) <= 2 ^ 59).
{ rewrite Z2Nat.id by lia. nia. }
destruct (tc_series_loop_correct n one_e z true 0%R _ Hn Ho HoE Ho1 Hz HzE HEz
  (Hzv _ _ Hrh Hrh) _ t0 _ t T HKi Ht0 Ht0E HE0 HEb HT0 HT Et) as (Ht & HtE & _).
assert (Sr : encl_small r) by (apply (encl_le_small E); [lia | exact HrE]).
assert (St : encl_small t) by (eapply encl_le_small; [|exact HtE]; nia).
destruct (encl_mul_correct n r t Hn Hr Ht Sr St) as (c & Ec & _ & Hlc & _).
rewrite H in Ec. injection Ec as Ec. subst c.
rewrite Hlc, Hlo, Hhi, !Rmult_0_l.
assert (M : forall u : R, Rmin u u = u)
  by (intros u; unfold Rmin; destruct (Rle_dec u u); reflexivity).
rewrite !M. apply dround_0. exact Hn.
Qed.

(** A negation swaps the bounds negated, so it keeps an enclosure that
    excludes 0 away from 0. *)
Lemma dp_neg :
  forall n a,
  level_ok n -> encl_ok n a -> (0 < lo_R a \/ hi_R a < 0)%R ->
  encl_ok n (Dyadic.encl_neg n a) /\
  (0 < lo_R (Dyadic.encl_neg n a) \/ hi_R (Dyadic.encl_neg n a) < 0)%R.
Proof.
intros n a Hn (Hla & Hha & Ha) S.
destruct (neg_correct n _ Hn Hla) as (Olo & Vlo & _).
destruct (neg_correct n _ Hn Hha) as (Ohi & Vhi & _).
unfold encl_ok, lo_R, hi_R, Dyadic.encl_neg in *; cbn [Dyadic.en_lo Dyadic.en_hi].
rewrite Vlo, Vhi.
split; [split; [exact Ohi | split; [exact Olo | lra]] |].
destruct S; [right | left]; lra.
Qed.

(** [sin_k] at a [ρ] in [[0, 4/5]], with [ρ > 0] where it takes the series
    of [sin]: the series is above 0 ([series_pos]), and a negation puts it
    below 0. *)
Lemma dp_sin_k_sign :
  forall n quad neg r c,
  level_ok n -> encl_ok n r -> encl_le (2 ^ 15) r ->
  (0 <= lo_R r)%R -> (hi_R r <= 4 / 5)%R -> (quad mod 2 = 0 -> (0 < lo_R r)%R) ->
  DyadicTrig.sin_k n quad neg r = Some c ->
  encl_ok n c /\ (0 < lo_R c \/ hi_R c < 0)%R.
Proof.
intros n quad neg r c Hn Or Lr L0 H45 Hodd H.
unfold DyadicTrig.sin_k in H.
destruct (quad mod 2 =? 0) eqn:Q.
- destruct (DyadicTrig.series n r true) as [v|] eqn:Ev; [|discriminate H].
  injection H as <-.
  destruct (dp_series_ok n r true v Hn Or Lr L0 H45 Ev) as (Ov & _).
  assert (P : (0 < lo_R v)%R).
  { apply (series_pos n r true v (2 ^ 15) Hn Or Lr ltac:(lia) L0 H45); [|exact Ev].
    intros _. apply Hodd. apply Z.eqb_eq. exact Q. }
  destruct (xorb neg (quad mod 4 =? 2)).
  + exact (dp_neg n v Hn Ov (or_introl P)).
  + split; [exact Ov | left; exact P].
- destruct (DyadicTrig.series n r false) as [v|] eqn:Ev; [|discriminate H].
  injection H as <-.
  destruct (dp_series_ok n r false v Hn Or Lr L0 H45 Ev) as (Ov & _).
  assert (P : (0 < lo_R v)%R).
  { apply (series_pos n r false v (2 ^ 15) Hn Or Lr ltac:(lia) L0 H45);
      [intros D; discriminate D | exact Ev]. }
  destruct (quad mod 4 =? 3).
  + exact (dp_neg n v Hn Ov (or_introl P)).
  + split; [exact Ov | left; exact P].
Qed.

(** ** The enclosures *)

Lemma ev_sin_sign :
  forall x n a,
  level_ok n -> is_finite x = true -> B2R x <> 0%R ->
  DyadicTrig.ev_sin x n = Some a -> (0 < lo_R a \/ hi_R a < 0)%R.
Proof.
intros x n a Hn Fx Hx H. unfold DyadicTrig.ev_sin in H.
destruct (DyadicTrig.reduce n (fabs x)) as [[[quad neg] r]|] eqn:Er; [|discriminate H].
cbv beta iota in H.
destruct (DyadicTrig.sin_k n quad neg r) as [v|] eqn:Ev; [|discriminate H].
cbv beta iota in H. injection H as <-.
assert (Pt : (0 < B2R (fabs x))%R) by (rewrite trg_fabs_R; apply Rabs_pos_lt; exact Hx).
destruct (dp_reduce n (fabs x) quad neg r Hn (trg_fabs_finite x Fx) (trg_fabs_pos x) Er)
  as (Or & Lr & L0 & H45 & _).
pose proof (reduce_pos n (fabs x) quad neg r Hn (trg_fabs_finite x Fx) Pt Er) as P.
destruct (dp_sin_k_sign n quad neg r v Hn Or Lr L0 H45 (fun _ => P) Ev) as (Ov & Sv).
destruct (lt x zero); [exact (proj2 (dp_neg n v Hn Ov Sv)) | exact Sv].
Qed.

Lemma ev_cos_sign :
  forall t n a,
  level_ok n -> is_finite t = true -> (0 <= B2R t)%R ->
  DyadicTrig.ev_cos t n = Some a -> (0 < lo_R a \/ hi_R a < 0)%R.
Proof.
intros t n a Hn Ft Pt H. unfold DyadicTrig.ev_cos in H.
destruct (DyadicTrig.reduce n t) as [[[quad neg] r]|] eqn:Er; [|discriminate H].
cbv beta iota in H.
destruct (dp_reduce n t quad neg r Hn Ft Pt Er) as (Or & Lr & L0 & H45 & Hq).
refine (proj2 (dp_sin_k_sign n (quad + 1) neg r a Hn Or Lr L0 H45 _ H)).
intros Q. apply Hq. intros E. subst quad. vm_compute in Q. discriminate Q.
Qed.

Theorem tan_div_pos :
  forall x n quad neg r one_e s a b p c,
  level_ok n -> is_finite x = true ->
  DyadicTrig.reduce n (fabs x) = Some (quad, neg, r) ->
  Dyadic.encl_point n DyadicExp.one = Some one_e ->
  DyadicTrig.series n r true = Some s ->
  Dyadic.encl_sub n one_e s = Some a -> Dyadic.encl_add n one_e s = Some b ->
  Dyadic.encl_mul n a b = Some p -> Dyadic.encl_sqrt n p = Some c ->
  (quad mod 2 = 1 -> (0 < lo_R s)%R) /\ (0 < lo_R c)%R.
Proof.
intros x n quad neg r one_e s a b p c Hn Fx Er E1 Es Ea Eb Ep Ec.
pose proof (trg_fabs_finite x Fx) as Ft.
destruct (dp_reduce n (fabs x) quad neg r Hn Ft (trg_fabs_pos x) Er)
  as (Or & Lr & L0 & H45 & Hq).
split.
{ intros Q. apply (series_pos n r true s (2 ^ 15) Hn Or Lr ltac:(lia) L0 H45); [|exact Es].
  intros _. apply Hq. intros E. subst quad. vm_compute in Q. discriminate Q. }
(* [s] lies in [[0, 1)]: above 0 by [series_pos] where [t > 0], 0 below
   where [t = 0] ([dp_series_zero]), and below 1 by [series_sin_lt1]. *)
assert (Hs2 : (hi_R s < 1)%R)
  by exact (series_sin_lt1 n r s (2 ^ 15) Hn Or Lr ltac:(lia) L0 H45 Es).
assert (Hs0 : (0 <= lo_R s)%R).
{ destruct (Rle_lt_or_eq_dec 0 (B2R (fabs x)) (trg_fabs_pos x)) as [P|Z].
  - pose proof (reduce_pos n (fabs x) quad neg r Hn Ft P Er) as Pr.
    apply Rlt_le.
    apply (series_pos n r true s (2 ^ 15) Hn Or Lr ltac:(lia) L0 H45); [|exact Es].
    intros _. exact Pr.
  - destruct (dp_reduce_zero n (fabs x) quad neg r Hn Ft (eq_sym Z) Er) as (_ & Zlo & Zhi).
    rewrite (dp_series_zero n r s (2 ^ 15) Hn Or Lr ltac:(lia) Zlo Zhi Es). apply Rle_refl. }
(* The steps, as in [ev_tan_correct] of [DyTrig.v], then the formulas of
   the lower bounds: [1 - hi s > 0], [1 + lo s > 0], four positive
   products, and the square root of a positive number. *)
destruct (point_has n _ one_e Hn E1) as (O1 & L1 & _).
destruct (point_step n _ _ Hn E1) as (_ & _ & V1 & _ & _). rewrite dexp_one_R in V1.
destruct (dp_series_ok n r true s Hn Or Lr L0 H45 Es) as (Os & Ls).
destruct (sub_step n one_e s a _ _ Hn O1 Os L1 Ls ltac:(lia) ltac:(lia) Ea) as (Oa & La & _).
assert (La' : encl_le (2 ^ 51) a) by (eapply encl_le_mono; [|exact La]; lia).
destruct (add_step n one_e s b _ _ Hn O1 Os L1 Ls ltac:(lia) ltac:(lia) Eb) as (Ob & Lb & _).
assert (Lb' : encl_le (2 ^ 51) b) by (eapply encl_le_mono; [|exact Lb]; lia).
destruct (mul_step n a b p _ _ Hn Oa Ob La' Lb' ltac:(lia) ltac:(lia) Ep) as (Op & Lp & _).
assert (Lp' : encl_le (2 ^ 53) p) by (eapply encl_le_mono; [|exact Lp]; lia).
assert (S1 : encl_small one_e) by (apply (encl_le_small (2 ^ 13)); [lia | exact L1]).
assert (Ss : encl_small s) by (apply (encl_le_small (2 ^ 50)); [lia | exact Ls]).
assert (Sa : encl_small a) by (apply (encl_le_small (2 ^ 51)); [lia | exact La']).
assert (Sb : encl_small b) by (apply (encl_le_small (2 ^ 51)); [lia | exact Lb']).
assert (Sp : encl_small p) by (apply (encl_le_small (2 ^ 53)); [lia | exact Lp']).
destruct (encl_sub_correct n one_e s Hn O1 Os S1 Ss) as (a' & Ea' & _ & Ha & _).
rewrite Ea in Ea'. injection Ea' as <-.
assert (Pa : (0 < lo_R a)%R) by (rewrite Ha, V1; apply sp_rd_pos; [exact Hn | lra]).
destruct (encl_add_correct n one_e s Hn O1 Os S1 Ss) as (b' & Eb' & _ & Hb & _).
rewrite Eb in Eb'. injection Eb' as <-.
assert (Pb : (0 < lo_R b)%R) by (rewrite Hb, V1; apply sp_rd_pos; [exact Hn | lra]).
destruct (encl_mul_correct n a b Hn Oa Ob Sa Sb) as (p' & Ep' & _ & Hp & _).
rewrite Ep in Ep'. injection Ep' as <-.
assert (Pp : (0 < lo_R p)%R).
{ rewrite Hp. apply sp_rd_pos; [exact Hn|].
  destruct Oa as (_ & _ & Oa). destruct Ob as (_ & _ & Ob).
  unfold lo_R, hi_R in *.
  repeat apply Rmin_glb_lt; apply Rmult_lt_0_compat; lra. }
assert (Hph : (0 <= hi_R p)%R)
  by (destruct Op as (_ & _ & Op'); unfold lo_R, hi_R in *; lra).
destruct (encl_sqrt_correct n p Hn Op Sp Hph) as (c' & Ec' & _ & Hc & _).
rewrite Ec in Ec'. injection Ec' as <-.
rewrite Hc. apply sp_rd_pos; [exact Hn|].
rewrite Rmax_left by lra. apply sqrt_lt_R0. exact Pp.
Qed.

(** ** The functions *)

Theorem sin_dir_sign :
  forall x v,
  is_finite x = true -> DyadicTrig.sin_dir x false = Some v ->
  (Model.lt v Model.zero = true <-> sin (B2R x) < 0)%R.
Proof.
intros x v Fx H. split.
2: { intros Hs. exact (dp_side_neg _ _ (sin_dir_side x false v Fx H) Hs). }
intros L. unfold DyadicTrig.sin_dir, DyadicTrig.sin_dir_with in H.
rewrite Fx in H. cbv [negb] in H.
destruct (lt (fabs x) DyadicExp.tiny_hyp) eqn:G; cbv iota in H.
{ injection H as <-. exact (proj1 (rnd_dn_neg _ _ (sin_tiny_rule x false Fx G)) L). }
destruct (DyadicTrig.sin_small x false) as [w|] eqn:S; cbv iota in H.
{ injection H as <-. exact (proj1 (rnd_dn_neg _ _ (sin_small_rule x false w Fx S)) L). }
destruct (DyadicTrig.fast_sin_dir false x false) eqn:F; cbv iota in H.
{ injection H as <-. exact (proj1 (rnd_dn_neg _ _
    (FastTrig.fast_sin_dir_correct false x false _ Fx (FastTrig.fast_arg_hyp x Fx G) F)) L). }
(* The driver: [|x| >= 2^-26], so every enclosure excludes 0. *)
assert (Hx : B2R x <> 0%R).
{ intros Z.
  assert (Ftn : is_finite DyadicExp.tiny_hyp = true) by (vm_compute; reflexivity).
  pose proof (trg_fabs_finite x Fx) as Fa.
  unfold Model.lt in G. rewrite Bltb_correct in G by assumption.
  rewrite trg_fabs_R, Z, Rabs_R0, hyp_lit_tiny in G.
  rewrite Rlt_bool_true in G; [discriminate G | apply bpow_gt_0]. }
pose proof (ziv_sign (DyadicTrig.ev_sin x) false 1%nat (sin (B2R x)) v) as Zs.
cbv iota in Zs. refine (Zs _ H L).
intros n a Hn Ha.
destruct (ev_sin_correct x n a Hn Fx Ha) as (Oa & Ha').
split; [exact Oa|]. split; [exact Ha'|]. exact (ev_sin_sign x n a Hn Fx Hx Ha).
Qed.

Theorem cos_dir_sign :
  forall x v,
  is_finite x = true -> DyadicTrig.cos_dir x true = Some v ->
  (Model.lt Model.zero v = true <-> 0 < cos (B2R x))%R.
Proof.
intros x v Fx H. split.
2: { intros Hc. exact (dp_side_pos _ _ (cos_dir_side x true v Fx H) Hc). }
intros L. unfold DyadicTrig.cos_dir, DyadicTrig.cos_dir_with in H. cbv zeta in H.
rewrite (trg_fabs_finite x Fx) in H. cbv [negb] in H.
destruct (lt (fabs x) DyadicExp.tiny_hyp) eqn:G; cbv iota in H.
{ injection H as <-. exact (proj1 (rnd_up_pos _ _ (cos_tiny_rule x true Fx G)) L). }
destruct (DyadicTrig.cos_small (fabs x) true) as [w|] eqn:S; cbv iota in H.
{ injection H as <-. exact (proj1 (rnd_up_pos _ _ (cos_small_rule x true w Fx S)) L). }
destruct (DyadicTrig.fast_cos_dir false (fabs x) true) eqn:F; cbv iota in H.
{ injection H as <-.
  destruct (FastTrig.fast_arg_fabs x (FastTrig.fast_arg_hyp x Fx G) Fx) as (Fa & Ga).
  pose proof (FastTrig.fast_cos_dir_correct false (fabs x) true _ Fa Ga F) as R.
  rewrite FastTrig.cos_fabs in R. exact (proj1 (rnd_up_pos _ _ R) L). }
pose proof (ziv_sign (DyadicTrig.ev_cos (fabs x)) true 1%nat (cos (B2R x)) v) as Zc.
cbv iota in Zc. refine (Zc _ H L).
intros n a Hn Ha.
destruct (ev_cos_correct (fabs x) n a Hn (trg_fabs_finite x Fx) (trg_fabs_pos x) Ha)
  as (Oa & Ha').
split; [exact Oa|]. split.
- rewrite trg_fabs_R in Ha'. unfold Rabs in Ha'.
  destruct (Rcase_abs (B2R x)); [rewrite cos_neg in Ha'|]; exact Ha'.
- exact (ev_cos_sign (fabs x) n a Hn (trg_fabs_finite x Fx) (trg_fabs_pos x) Ha).
Qed.
