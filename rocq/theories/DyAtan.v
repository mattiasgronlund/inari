(** * atan and atan2 in the dyadic kernel

    [atan_dir] and [atan2_dir] of [DyadicAtan] in [Model.v], where they
    return, round [atan] of a finite [x] and [Ratan2] of finite [y] and
    [x] with [y <> 0] or [x > 0] in the direction [up]
    ([atan_dir_correct] and [atan2_dir_correct]): the rules of
    [DyAtanTiny.v] for tiny arguments and quotients, [atan_huge_rule]
    for atan at [|x| >= 2^54], and otherwise
    [ziv_correct] of [DyDriver.v] with the enclosures of
    [ev_atan_correct] and [ev_atan2_correct]. [ev_atan2] reduces
    [atan2(y, x)] to [atan] of [|y|/|x|] or [|x|/|y|] by the octant of
    [(x, y)], with π of [DyConstPi.v]. [pi_times c up] rounds [c π]
    ([pi_times_correct]); it gives the values at the infinities,
    which the last lemmas state. That the loop ends before its cap is
    not proved. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary LogReal AtanReal DyRound DyConv DyOps
  DyDriver DyGrow DyConst DyExpCore DyExpRules DyExp ExpReal DyHypRules DyLogRules DyLogCore
  DyLog DyLogHyp AtanSeries AtanIdent DyConstPi DyAtanTiny DyAtanCore MpfrRound.
From Inari Require PiBounds PiTight.

Open Scope Z_scope.

(** ** Helpers *)

Lemma atn_sign_true : forall x : f64, Bsign x = true -> (B2R x <= 0)%R.
Proof.
intros [s|s| |s m e H] Hs; cbn [B2R]; try apply Rle_refl.
cbn [Bsign] in Hs. subst s.
apply F2R_le_0. cbn [Fnum SpecFloat.cond_Zopp]. lia.
Qed.

Lemma atn_sign_false : forall x : f64, Bsign x = false -> (0 <= B2R x)%R.
Proof.
intros [s|s| |s m e H] Hs; cbn [B2R]; try apply Rle_refl.
cbn [Bsign] in Hs. subst s.
apply F2R_ge_0. cbn [Fnum SpecFloat.cond_Zopp]. lia.
Qed.

Lemma atn_eq_zero :
  forall x : f64, is_finite x = true ->
  (eq x zero = true -> B2R x = 0%R) /\ (eq x zero = false -> B2R x <> 0%R).
Proof.
intros x Fx. unfold eq. rewrite Beqb_correct by (first [exact Fx | reflexivity]).
change (B2R zero) with 0%R.
destruct (Req_bool_spec (B2R x) 0) as [H|H]; split; intros H'; first [exact H | discriminate H'].
Qed.

Lemma atn_gt_zero :
  forall x : f64, is_finite x = true ->
  (gt x zero = true -> 0 < B2R x)%R /\ (gt x zero = false -> B2R x <= 0)%R.
Proof.
intros x Fx. unfold gt. rewrite Bltb_correct by (first [exact Fx | reflexivity]).
change (B2R zero) with 0%R.
destruct (Rlt_bool_spec 0 (B2R x)) as [H|H]; split; intros H';
  first [exact H | discriminate H'].
Qed.

(** [copysign c y] of a positive [c] is [c] or [-c] by the sign of [y]. *)
Lemma atn_copysign :
  forall c y, Bsign c = false -> is_finite c = true ->
  is_finite (copysign c y) = true /\ B2R (copysign c y) = (if Bsign y then - B2R c else B2R c)%R.
Proof.
intros c y Sc Fc. unfold copysign. rewrite Sc.
destruct (Bsign y); cbn [Bool.eqb].
- unfold opp. rewrite is_finite_Bopp, B2R_Bopp. split; [exact Fc | reflexivity].
- split; [exact Fc | reflexivity].
Qed.

Lemma ev_pi_correct :
  forall c n a,
  level_ok n -> is_finite c = true -> DyadicAtan.ev_pi c n = Some a ->
  encl_ok n a /\ encl_has a (B2R c * PI).
Proof.
intros c n a Hn _ H. unfold DyadicAtan.ev_pi in H.
destruct (Dyadic.encl_point n c) as [pc|] eqn:Ec; [|discriminate H].
destruct (DyadicConsts.pi n) as [p|] eqn:Ep; [|discriminate H].
cbv beta iota in H.
destruct (point_has n c pc Hn Ec) as (Oc & Lc & Hc).
destruct (pi_correct n p Hn Ep) as (Op & Lp & Hp).
destruct (mul_step n pc p a _ _ Hn Oc Op Lc Lp ltac:(lia) ltac:(lia) H) as (Oa & _ & Ha).
split; [exact Oa | exact (Ha _ _ Hc Hp)].
Qed.

Lemma pi_times_correct :
  forall c up v,
  is_finite c = true -> DyadicAtan.pi_times c up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (B2R c * PI) (with_val v).
Proof.
intros c up v Fc H. unfold DyadicAtan.pi_times in H.
apply (ziv_correct (DyadicAtan.ev_pi c) up 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_pi_correct c n a Hn Fc Ha).
Qed.

(** [atan |x|] by [atan_encl], then [atan (-t) = - atan t]. *)
Lemma ev_atan_correct :
  forall x n a,
  level_ok n -> is_finite x = true -> DyadicAtan.ev_atan x n = Some a ->
  encl_ok n a /\ encl_has a (atan (B2R x)).
Proof.
intros x n a Hn _ H. unfold DyadicAtan.ev_atan in H.
destruct (Dyadic.encl_point n (fabs x)) as [t|] eqn:Et; [|discriminate H].
destruct (DyadicAtan.atan_encl n t) as [r|] eqn:Er; [|discriminate H].
cbv beta iota in H. injection H as <-.
destruct (point_has n _ t Hn Et) as (Ot & Lt & Ht).
unfold fabs in Ht. rewrite B2R_Babs in Ht.
destruct (atan_encl_correct n t r _ _ Hn Ot Lt ltac:(lia) Ht Er) as (Or & Lr & Hr).
apply (lh_odd n x r (2 ^ 51) atan Hn Or Lr); [|exact Hr].
intros _. rewrite atan_opp, Ropp_involutive. reflexivity.
Qed.

(** For [y > 0], by the octant of [(x, y)]: [atan (y / x)] for
    [y <= |x|] and [x > 0], [π - atan (y / |x|)] for [y <= |x|] and
    [x < 0], and [π/2 - atan (x / y)] for [y > |x|], which [ev_atan2]
    computes as [π/2 + atan (|x| / y)] for [x < 0]; then
    [atan2 (-y) x = - atan2 y x]. *)
Lemma ev_atan2_correct :
  forall y x n a,
  level_ok n -> is_finite y = true -> is_finite x = true -> B2R y <> 0%R -> B2R x <> 0%R ->
  DyadicAtan.ev_atan2 y x n = Some a ->
  encl_ok n a /\ encl_has a (Ratan2 (B2R y) (B2R x)).
Proof.
intros y x n a Hn Fy Fx Y0 X0 H. unfold DyadicAtan.ev_atan2 in H.
destruct (Dyadic.encl_point n (fabs y)) as [ea|] eqn:Ea; [|discriminate H].
destruct (Dyadic.encl_point n (fabs x)) as [eb|] eqn:Eb; [|discriminate H].
destruct (if le (fabs y) (fabs x) then _ else _) as [r|] eqn:Er in H; [|discriminate H].
cbv beta iota in H. injection H as <-.
destruct (point_has n _ ea Hn Ea) as (Oa & La & Ha).
unfold fabs in Ha. rewrite B2R_Babs in Ha.
destruct (point_has n _ eb Hn Eb) as (Ob & Lb & Hb).
unfold fabs in Hb. rewrite B2R_Babs in Hb.
assert (Py : (0 < Rabs (B2R y))%R) by (apply Rabs_pos_lt; exact Y0).
destruct (atn_gt_zero x Fx) as (G1 & G2).
(* [r] holds [atan2 |y| x]. *)
assert (Hr : encl_ok n r /\ encl_le (2 ^ 52) r /\ encl_has r (Ratan2 (Rabs (B2R y)) (B2R x))).
{ destruct (le (fabs y) (fabs x)).
  - destruct (Dyadic.encl_div n ea eb) as [q|] eqn:Eq; [|discriminate Er].
    destruct (DyadicAtan.atan_encl n q) as [t|] eqn:Et; [|discriminate Er].
    cbv beta iota in Er.
    destruct (div_step n ea eb q _ _ Hn Oa Ob La Lb ltac:(lia) ltac:(lia) Eq) as (Oq & Lq & Hq).
    specialize (Hq _ _ Ha Hb).
    destruct (atan_encl_correct n q t _ _ Hn Oq Lq ltac:(lia) Hq Et) as (Ot & Lt & Ht).
    destruct (gt x zero).
    + injection Er as <-. specialize (G1 eq_refl).
      split; [exact Ot|]. split; [eapply encl_le_mono; [|exact Lt]; lia|].
      rewrite (Ratan2_pos_x _ _ G1). rewrite (Rabs_pos_eq (B2R x)) in Ht by lra. exact Ht.
    + destruct (DyadicConsts.pi n) as [p|] eqn:Ep; [|discriminate Er].
      cbv beta iota in Er.
      destruct (pi_correct n p Hn Ep) as (Op & Lp & Hp).
      destruct (sub_step n p t r _ _ Hn Op Ot Lp Lt ltac:(lia) ltac:(lia) Er) as (Or & Lr & Hr).
      specialize (Hr _ _ Hp Ht).
      split; [exact Or|]. split; [eapply encl_le_mono; [|exact Lr]; lia|].
      assert (Xn : (B2R x < 0)%R)
        by (destruct (Rle_lt_or_eq_dec _ _ (G2 eq_refl)); [assumption | contradiction]).
      rewrite (Ratan2_neg_x_ge _ _ Xn (Rlt_le _ _ Py)).
      rewrite (Rabs_left (B2R x) Xn) in Hr.
      replace (Rabs (B2R y) / - B2R x)%R with (- (Rabs (B2R y) / B2R x))%R in Hr
        by (field; lra).
      rewrite atan_opp in Hr.
      replace (atan (Rabs (B2R y) / B2R x) + PI)%R
        with (PI - - atan (Rabs (B2R y) / B2R x))%R by ring.
      exact Hr.
  - destruct (Dyadic.encl_div n eb ea) as [q|] eqn:Eq; [|discriminate Er].
    destruct (DyadicAtan.atan_encl n q) as [t|] eqn:Et; [|discriminate Er].
    destruct (DyadicConsts.pi n) as [p|] eqn:Ep; [|discriminate Er].
    destruct (Dyadic.encl_shl n p (-1)) as [h|] eqn:Eh; [|discriminate Er].
    cbv beta iota in Er.
    destruct (div_step n eb ea q _ _ Hn Ob Oa Lb La ltac:(lia) ltac:(lia) Eq) as (Oq & Lq & Hq).
    specialize (Hq _ _ Hb Ha).
    destruct (atan_encl_correct n q t _ _ Hn Oq Lq ltac:(lia) Hq Et) as (Ot & Lt & Ht).
    destruct (pi_correct n p Hn Ep) as (Op & Lp & Hp).
    destruct (shl_step n p (-1) h _ Hn Op Lp ltac:(lia) ltac:(lia) Eh) as (Oh & Lh & Hh).
    specialize (Hh _ Hp).
    (* [π 2^-1] is [π/2]. *)
    replace (PI * bpow radix2 (-1))%R with (PI / 2)%R in Hh
      by (change (bpow radix2 (-1)) with (/ 2)%R; reflexivity).
    rewrite (ar_up _ _ Py).
    destruct (gt x zero).
    + specialize (G1 eq_refl).
      destruct (sub_step n h t r _ _ Hn Oh Ot Lh Lt ltac:(lia) ltac:(lia) Er) as (Or & Lr & Hr).
      specialize (Hr _ _ Hh Ht).
      split; [exact Or|]. split; [eapply encl_le_mono; [|exact Lr]; lia|].
      rewrite (Rabs_pos_eq (B2R x)) in Hr by lra. exact Hr.
    + assert (Xn : (B2R x < 0)%R)
        by (destruct (Rle_lt_or_eq_dec _ _ (G2 eq_refl)); [assumption | contradiction]).
      destruct (add_step n h t r _ _ Hn Oh Ot Lh Lt ltac:(lia) ltac:(lia) Er) as (Or & Lr & Hr).
      specialize (Hr _ _ Hh Ht).
      split; [exact Or|]. split; [eapply encl_le_mono; [|exact Lr]; lia|].
      rewrite (Rabs_left (B2R x) Xn) in Hr.
      replace (- B2R x / Rabs (B2R y))%R with (- (B2R x / Rabs (B2R y)))%R in Hr
        by (field; lra).
      rewrite atan_opp in Hr.
      replace (PI / 2 - atan (B2R x / Rabs (B2R y)))%R
        with (PI / 2 + - atan (B2R x / Rabs (B2R y)))%R by ring.
      exact Hr. }
destruct Hr as (Or & Lr & Hr).
apply (lh_odd n y r (2 ^ 52) (fun v => Ratan2 v (B2R x)) Hn Or Lr); [|exact Hr].
intros _. cbv beta.
rewrite <- (Ratan2_opp_y (- B2R y) (B2R x)) by (intros E; apply Y0; lra).
rewrite Ropp_involutive. reflexivity.
Qed.

(** ** The directed functions *)

(** If no element of [f64_format] lies strictly between [lo] and [hi],
    two reals strictly between them round to the same result in each
    direction. *)
Lemma atn_round_gap :
  forall rnd lo hi ra rb v,
  (forall g, f64_format g -> g <= lo \/ hi <= g)%R ->
  (lo < ra < hi)%R -> (lo < rb < hi)%R ->
  mpfr_round f64_format rnd ra v -> mpfr_round f64_format rnd rb v.
Proof.
intros rnd lo hi ra rb v Hg Ha Hb H.
assert (DN : forall y, Rnd_DN_pt f64_format ra y -> Rnd_DN_pt f64_format rb y).
{ intros y (Fy & Hy & Hext). split; [exact Fy|]. split; [destruct (Hg y Fy); lra|].
  intros g Fg Hgb. destruct (Hg g Fg); [apply Hext; [exact Fg | lra] | lra]. }
assert (UP : forall y, Rnd_UP_pt f64_format ra y -> Rnd_UP_pt f64_format rb y).
{ intros y (Fy & Hy & Hext). split; [exact Fy|]. split; [destruct (Hg y Fy); lra|].
  intros g Fg Hgb. destruct (Hg g Fg); [lra | apply Hext; [exact Fg | lra]]. }
destruct rnd, v as [|[|]|s|y]; cbn [mpfr_round] in *; try contradiction;
  first
    [ (intros g Fg; specialize (H g Fg); destruct (Hg g Fg); lra)
    | exact (DN _ H)
    | exact (UP _ H)
    | (destruct H as [H0 H]; split; [exact H0 | first [exact (DN _ H) | exact (UP _ H)]]) ].
Qed.

(** The bounds of [Interval::FRAC_PI_2], the [f64]s next to [π/2]
    ([PiTight.v]). *)
Local Notation pi2_lo := (Interval.inf_raw Interval.FRAC_PI_2).
Local Notation pi2_hi := (Interval.sup_raw Interval.FRAC_PI_2).

(** No [f64] lies strictly between [pi2_lo] and [pi2_hi], which is the
    [f64] after it, nor between their negations. *)
Lemma atn_pi2_gap :
  forall g, f64_format g ->
  (g <= B2R pi2_lo \/ B2R pi2_hi <= g)%R /\ (g <= - B2R pi2_hi \/ - B2R pi2_lo <= g)%R.
Proof.
destruct PiTight.pt_FRAC_PI_2_facts as (Flo & Fhi & Hs).
intros g (w & Fw & <-). rewrite <- Hs in Fhi |- *.
split.
- destruct (Rle_or_lt (B2R w) (B2R pi2_lo)) as [L|L]; [left; exact L|].
  right. exact (PiTight.pt_succ_le _ w Flo Fhi L).
- destruct (Rle_or_lt (B2R (Bopp w)) (B2R pi2_lo)) as [L|L].
  + right. rewrite B2R_Bopp in L. lra.
  + left. pose proof (PiTight.pt_succ_le _ (Bopp w) Flo Fhi L) as P.
    rewrite B2R_Bopp in P. lra.
Qed.

(** For [t >= 2^54], [atan t] and [π/2] lie strictly between [pi2_lo]
    and [pi2_hi]: [atan t = π/2 - atan (1/t)] ([atan_inv]) with
    [0 < atan (1/t)] ([atan_increasing]) and [atan (1/t) < 1/t <= 2^-54]
    ([atan_tiny_real]), and π to 18 decimals ([PI_Q] of [PiBounds.v])
    puts [pi2_lo] more than [2^-54] below [π/2]. *)
Lemma atn_huge_between :
  forall t, (18014398509481984 <= t)%R ->
  (B2R pi2_lo < atan t < B2R pi2_hi)%R /\ (B2R pi2_lo < PI / 2 < B2R pi2_hi)%R.
Proof.
intros t Ht.
assert (Tp : (0 < t)%R) by lra.
assert (Le : (/ t <= / 18014398509481984)%R) by (apply Rinv_le_contravar; lra).
assert (Ip : (0 < / t)%R) by (apply Rinv_0_lt_compat; exact Tp).
assert (Hb : bpow radix2 (-26) = (1 / 67108864)%R) by (cbn [bpow radix_val radix2]; lra).
assert (Hs : (0 < / t < bpow radix2 (-26))%R) by (rewrite Hb; lra).
destruct (atan_tiny_real (/ t) Hs) as [_ A].
pose proof (atan_increasing 0 (/ t) Ip) as A0. rewrite atan_0 in A0.
rewrite atan_inv in A, A0 by exact Tp.
destruct (atan_bound t) as [_ B].
destruct PiBounds.PI_Q as [P1 P2].
unfold Q2R, PiBounds.pi_lo, PiBounds.pi_hi in P1, P2.
cbn [QArith_base.Qnum QArith_base.Qden] in P1, P2.
rewrite PiBounds.pb_frac_lo, PiBounds.pb_frac_hi, PiBounds.pb_lo_R, PiBounds.pb_hi_R.
unfold Q2R; cbn [QArith_base.Qnum QArith_base.Qden].
split; split; lra.
Qed.

(** For a finite [x] with [|x| >= 2^54], [atan x] and [±π/2] (the sign of
    [x]) lie strictly between the same two adjacent [f64]s, so that
    [pi_times (copysign 0.5 x) up] rounds [atan x]: [atan x] is above
    [π/2 - 2^-54] for [x >= 2^54], and the [f64] below [π/2] is
    [π/2 - 6.1e-17]. *)
Lemma atan_huge_rule :
  forall x up v,
  is_finite x = true -> ge (fabs x) DyadicAtan.huge_atan = true ->
  DyadicAtan.pi_times (copysign DyadicLog.half x) up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (atan (B2R x)) (with_val v).
Proof.
intros x up v Fx G H.
(* [huge_atan] is [2^54]. *)
assert (Fh : is_finite DyadicAtan.huge_atan = true) by (vm_compute; reflexivity).
assert (Hh : B2R DyadicAtan.huge_atan = 18014398509481984%R).
{ rewrite <- SF2R_B2SF.
  replace (B2SF DyadicAtan.huge_atan) with (SpecFloat.S754_finite false 4503599627370496 2)
    by (vm_compute; reflexivity).
  cbn [SF2R SpecFloat.cond_Zopp cond_Zopp]. unfold F2R; cbn [Fnum Fexp bpow radix_val radix2].
  lra. }
assert (Ht : (18014398509481984 <= Rabs (B2R x))%R).
{ assert (Fa : is_finite (fabs x) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fx).
  unfold ge in G. rewrite Bleb_correct in G by assumption.
  unfold fabs in G. rewrite B2R_Babs, Hh in G.
  destruct (Rle_bool_spec 18014398509481984%R (Rabs (B2R x))) as [L|L];
    [exact L | discriminate G]. }
destruct (atn_huge_between _ Ht) as (A & P).
assert (Sh : Bsign DyadicLog.half = false) by (vm_compute; reflexivity).
assert (Fhalf : is_finite DyadicLog.half = true) by (vm_compute; reflexivity).
destruct (atn_copysign DyadicLog.half x Sh Fhalf) as (Fc & Vc).
pose proof (pi_times_correct _ up v Fc H) as R.
rewrite Vc, lc_half_R in R.
revert R. destruct (Bsign x) eqn:Sx; intros R.
- (* [x <= -2^54]: [atan x = - atan |x|], and [R] rounds [-π/2]. *)
  pose proof (atn_sign_true x Sx) as Xn.
  rewrite (Rabs_left1 _ Xn), atan_opp in A.
  apply (atn_round_gap _ (- B2R pi2_hi) (- B2R pi2_lo) (- (1 / 2) * PI)%R);
    [| lra | lra | exact R].
  intros g Fg. exact (proj2 (atn_pi2_gap g Fg)).
- (* [x >= 2^54], and [R] rounds [π/2]. *)
  pose proof (atn_sign_false x Sx) as Xp.
  rewrite (Rabs_pos_eq _ Xp) in A.
  apply (atn_round_gap _ (B2R pi2_lo) (B2R pi2_hi) (1 / 2 * PI)%R);
    [| lra | lra | exact R].
  intros g Fg. exact (proj1 (atn_pi2_gap g Fg)).
Qed.

Theorem atan_dir_correct :
  forall x up v,
  is_finite x = true -> DyadicAtan.atan_dir x up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (atan (B2R x)) (with_val v).
Proof.
intros x up v Fx H. unfold DyadicAtan.atan_dir in H.
rewrite (fin_not_nan x Fx) in H.
destruct (ge (fabs x) DyadicAtan.huge_atan) eqn:G0; cbv iota in H.
{ exact (atan_huge_rule x up v Fx G0 H). }
destruct (lt (fabs x) DyadicExp.tiny_hyp) eqn:G; cbv iota in H.
{ injection H as <-. exact (atan_tiny_rule x up Fx G). }
apply (ziv_correct (DyadicAtan.ev_atan x) up 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_atan_correct x n a Hn Fx Ha).
Qed.

(** [pi_times (copysign 0.5 (±∞)) up] returns, and rounds [±π/2]. *)
Lemma atn_pi_half_inf :
  forall s up, exists v,
  DyadicAtan.pi_times (copysign DyadicLog.half (B754_infinity s)) up = Some v /\
  mpfr_round f64_format (if up then RNDU else RNDD) (if s then - (PI / 2) else PI / 2)%R
    (with_val v).
Proof.
intros s up.
(* A test of [Some] by [vm_compute]: [vm_compute in E] of the [None]
   case takes minutes. *)
assert (Hs : match DyadicAtan.pi_times (copysign DyadicLog.half (B754_infinity s)) up with
             | Some _ => true | None => false end = true)
  by (destruct s, up; vm_compute; reflexivity).
destruct (DyadicAtan.pi_times (copysign DyadicLog.half (B754_infinity s)) up) as [v|] eqn:E;
  [| discriminate Hs].
exists v. split; [reflexivity|].
assert (Sh : Bsign DyadicLog.half = false) by (vm_compute; reflexivity).
assert (Fh : is_finite DyadicLog.half = true) by (vm_compute; reflexivity).
destruct (atn_copysign DyadicLog.half (B754_infinity s) Sh Fh) as (Fc & Vc).
pose proof (pi_times_correct _ up v Fc E) as R.
rewrite Vc, lc_half_R in R. cbn [Bsign] in R.
destruct s.
- replace (- (PI / 2))%R with (- (1 / 2) * PI)%R by field. exact R.
- replace (PI / 2)%R with (1 / 2 * PI)%R by field. exact R.
Qed.

(** [pi_times (copysign 1.0 y) up] of a finite [y] other than 0 returns,
    and rounds [±π] by the sign of [y]. *)
Lemma atn_pi_one :
  forall y up, is_finite y = true -> B2R y <> 0%R -> exists v,
  DyadicAtan.pi_times (copysign DyadicExp.one y) up = Some v /\
  mpfr_round f64_format (if up then RNDU else RNDD) (if Bsign y then - PI else PI)%R
    (with_val v).
Proof.
intros y up Fy Y0.
assert (S1 : Bsign DyadicExp.one = false) by (vm_compute; reflexivity).
assert (C : copysign DyadicExp.one y =
            if Bsign y then opp DyadicExp.one else DyadicExp.one)
  by (unfold copysign; rewrite S1; destruct (Bsign y); reflexivity).
assert (Hs : forall b : bool,
             match DyadicAtan.pi_times (if b then opp DyadicExp.one else DyadicExp.one) up with
             | Some _ => true | None => false end = true)
  by (intros b; destruct b, up; vm_compute; reflexivity).
destruct (DyadicAtan.pi_times (copysign DyadicExp.one y) up) as [v|] eqn:E;
  [| specialize (Hs (Bsign y)); rewrite <- C, E in Hs; discriminate Hs].
exists v. split; [reflexivity|].
destruct (atn_copysign DyadicExp.one y S1 (proj1 one_B2R)) as (Fc & Vc).
pose proof (pi_times_correct _ up v Fc E) as R.
rewrite Vc, (proj2 one_B2R) in R.
destruct (Bsign y).
- (* [R] has [Ropp 1], which [- 1] does not write: that is the literal. *)
  rewrite <- Ropp_mult_distr_l, Rmult_1_l in R. exact R.
- rewrite Rmult_1_l in R. exact R.
Qed.

Lemma atan_dir_infinity :
  forall s up, exists v,
  DyadicAtan.atan_dir (B754_infinity s) up = Some v /\
  mpfr_round f64_format (if up then RNDU else RNDD) (if s then - (PI / 2) else PI / 2)%R
    (with_val v).
Proof.
intros s up.
assert (E : DyadicAtan.atan_dir (B754_infinity s) up =
            DyadicAtan.pi_times (copysign DyadicLog.half (B754_infinity s)) up).
{ unfold DyadicAtan.atan_dir.
  replace (ge (fabs (B754_infinity s)) DyadicAtan.huge_atan)
    with true by (destruct s; vm_compute; reflexivity).
  reflexivity. }
rewrite E. apply atn_pi_half_inf.
Qed.

(** At [y = ±0] (so [x > 0]), [y] is [atan2 0 x = 0]; at [x = ±0],
    [π/2] of the sign of [y]; for [x > 0] and an exact tiny [y / x], the
    rule of [atan_tiny_rule]; and otherwise the loop. *)
Theorem atan2_dir_correct :
  forall y x up v,
  is_finite y = true -> is_finite x = true -> (B2R y <> 0 \/ 0 < B2R x)%R ->
  DyadicAtan.atan2_dir y x up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (Ratan2 (B2R y) (B2R x)) (with_val v).
Proof.
intros y x up v Fy Fx D H. unfold DyadicAtan.atan2_dir in H.
rewrite (fin_not_nan y Fy), (fin_not_nan x Fx) in H. cbn [orb] in H.
destruct (atn_eq_zero y Fy) as (Z1 & Z2).
destruct (eq y zero) eqn:Ey0; cbv iota in H.
{ (* [y = ±0], so [x > 0] and the result is [y]. *)
  specialize (Z1 eq_refl).
  assert (Px : (0 < B2R x)%R) by (destruct D as [D|D]; [contradiction | exact D]).
  assert (Sx : Bsign x = false)
    by (destruct (Bsign x) eqn:S; [apply atn_sign_true in S; lra | reflexivity]).
  rewrite Sx in H. cbn [negb] in H. injection H as <-.
  rewrite Z1, (Ratan2_zero_y_pos _ Px).
  destruct y as [s|s| |s m e Hb]; try discriminate Fy.
  - cbn [with_val]. apply mpfr_round_zero. exists zero. split; reflexivity.
  - exfalso. revert Z1. cbn [B2R]. apply F2R_neq_0. cbn [Fnum].
    destruct s; cbn [SpecFloat.cond_Zopp]; lia. }
specialize (Z2 eq_refl).
rewrite (fin_neq_inf y Fy), (fin_neq_ninf y Fy), (fin_neq_inf x Fx), (fin_neq_ninf x Fx)
  in H.
cbn [orb] in H.
destruct (atn_eq_zero x Fx) as (X1 & X2).
destruct (eq x zero) eqn:Ex0; cbv iota in H.
{ (* [x = ±0]: [±π/2]. *)
  specialize (X1 eq_refl).
  assert (Sh : Bsign DyadicLog.half = false) by (vm_compute; reflexivity).
  assert (Fh : is_finite DyadicLog.half = true) by (vm_compute; reflexivity).
  destruct (atn_copysign DyadicLog.half y Sh Fh) as (Fc & Vc).
  pose proof (pi_times_correct _ up v Fc H) as R.
  rewrite Vc, lc_half_R in R. rewrite X1.
  revert R. destruct (Bsign y) eqn:Sy; intros R.
  - pose proof (atn_sign_true y Sy) as Yn.
    assert (Yn' : (B2R y < 0)%R)
      by (destruct (Rle_lt_or_eq_dec _ _ Yn); [assumption | contradiction]).
    rewrite (Ratan2_zero_x_neg _ Yn').
    replace (- (PI / 2))%R with (- (1 / 2) * PI)%R by field. exact R.
  - pose proof (atn_sign_false y Sy) as Yp.
    assert (Yp' : (0 < B2R y)%R)
      by (destruct (Rle_lt_or_eq_dec _ _ Yp) as [L|L]; [assumption | contradiction (Z2 (eq_sym L))]).
    rewrite (Ratan2_zero_x_pos _ Yp').
    replace (PI / 2)%R with (1 / 2 * PI)%R by field. exact R. }
specialize (X2 eq_refl).
destruct (atn_gt_zero x Fx) as (G1 & _).
destruct (gt x zero) eqn:Gx; cbv beta iota in H.
- specialize (G1 eq_refl).
  destruct (DyadicAtan.tiny_quotient y x) as [[q|]|] eqn:Eq; cbv beta iota in H;
    [| |discriminate H].
  + (* The exact tiny quotient [q = y / x]. *)
    injection H as <-.
    destruct (tiny_quotient_correct y x q Fy Fx G1 Eq) as (Fq & Vq & Tq).
    rewrite (Ratan2_pos_x _ _ G1), <- Vq.
    exact (atan_tiny_rule q up Fq Tq).
  + apply (ziv_correct (DyadicAtan.ev_atan2 y x) up 1%nat); [|exact H].
    intros n a Hn Ha. exact (ev_atan2_correct y x n a Hn Fy Fx Z2 X2 Ha).
- apply (ziv_correct (DyadicAtan.ev_atan2 y x) up 1%nat); [|exact H].
  intros n a Hn Ha. exact (ev_atan2_correct y x n a Hn Fy Fx Z2 X2 Ha).
Qed.

Lemma atan2_dir_inf_pos :
  forall y up, is_finite y = true ->
  exists s', DyadicAtan.atan2_dir y (B754_infinity false) up = Some (B754_zero s' : f64).
Proof.
intros y up Fy.
destruct y as [s|s| |s m e Hb]; try discriminate Fy;
  exists s; destruct s, up; vm_compute; reflexivity.
Qed.

(** [atan2_dir y (-∞) up] of a finite [y] other than 0 is
    [pi_times (copysign 1.0 y) up]. *)
Lemma atn_inf_neg :
  forall y up, is_finite y = true -> B2R y <> 0%R ->
  DyadicAtan.atan2_dir y (B754_infinity true) up =
  DyadicAtan.pi_times (copysign DyadicExp.one y) up.
Proof.
intros y up Fy Y0.
assert (Ey0 : eq y zero = false)
  by (destruct (eq y zero) eqn:E0; [apply (proj1 (atn_eq_zero y Fy)) in E0; contradiction
                                    | reflexivity]).
unfold DyadicAtan.atan2_dir.
rewrite (fin_not_nan y Fy), Ey0, (fin_neq_inf y Fy), (fin_neq_ninf y Fy).
replace (eq (B754_infinity true : f64) infinity) with false by (vm_compute; reflexivity).
replace (eq (B754_infinity true : f64) DyadicExp.neg_infinity) with true
  by (vm_compute; reflexivity).
reflexivity.
Qed.

Lemma atan2_dir_inf_neg_pos :
  forall y up, is_finite y = true -> (0 < B2R y)%R -> exists v,
  DyadicAtan.atan2_dir y (B754_infinity true) up = Some v /\
  mpfr_round f64_format (if up then RNDU else RNDD) PI (with_val v).
Proof.
intros y up Fy Py.
assert (Y0 : B2R y <> 0%R) by lra.
assert (Sy : Bsign y = false)
  by (destruct (Bsign y) eqn:S; [apply atn_sign_true in S; lra | reflexivity]).
rewrite (atn_inf_neg y up Fy Y0).
destruct (atn_pi_one y up Fy Y0) as (v & Ev & Rv). rewrite Sy in Rv.
exists v. split; [exact Ev | exact Rv].
Qed.

Lemma atan2_dir_inf_neg_neg :
  forall y up, is_finite y = true -> (B2R y < 0)%R -> exists v,
  DyadicAtan.atan2_dir y (B754_infinity true) up = Some v /\
  mpfr_round f64_format (if up then RNDU else RNDD) (- PI)%R (with_val v).
Proof.
intros y up Fy Ny.
assert (Y0 : B2R y <> 0%R) by lra.
assert (Sy : Bsign y = true)
  by (destruct (Bsign y) eqn:S; [reflexivity | apply atn_sign_false in S; lra]).
rewrite (atn_inf_neg y up Fy Y0).
destruct (atn_pi_one y up Fy Y0) as (v & Ev & Rv). rewrite Sy in Rv.
exists v. split; [exact Ev | exact Rv].
Qed.

Lemma atan2_dir_y_inf :
  forall s x up, is_finite x = true -> exists v,
  DyadicAtan.atan2_dir (B754_infinity s) x up = Some v /\
  mpfr_round f64_format (if up then RNDU else RNDD) (if s then - (PI / 2) else PI / 2)%R
    (with_val v).
Proof.
intros s x up Fx.
assert (E : DyadicAtan.atan2_dir (B754_infinity s) x up =
            DyadicAtan.pi_times (copysign DyadicLog.half (B754_infinity s)) up).
{ unfold DyadicAtan.atan2_dir.
  rewrite (fin_not_nan x Fx), (fin_neq_inf x Fx), (fin_neq_ninf x Fx).
  replace (eq (B754_infinity s) zero) with false by (destruct s; vm_compute; reflexivity).
  replace (eq (B754_infinity s) infinity || eq (B754_infinity s) DyadicExp.neg_infinity)
    with true by (destruct s; vm_compute; reflexivity).
  reflexivity. }
rewrite E. apply atn_pi_half_inf.
Qed.
