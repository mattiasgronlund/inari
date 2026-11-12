(** * The fast paths of [asin] and [acos]

    [DyadicAtan.fast_sqrt1m t] of [Model.v] is [r = √((1 - t)(1 + t))] in
    double-double ([FastAsinSqrt.v]).
    [DyadicAtan.fast_asin_atan t] is atan(t / r) = asin t for [t <=
    181/256] and atan(r / t) = acos t above ([AtanIdent.asin_as_atan],
    [acos_as_atan]), by [dd_div] and the core of [FastAtanCore.v]
    ([fast_asin_atan_correct]); 181/256 < 1/√2 keeps both quotients
    below 129/128. [asin t] above the split is π/2 - acos t
    ([AtanIdent.asin_plus_acos]), [acos t] below it is π/2 - asin t,
    [acos(-t)] is π - acos t, and [acos x] at [|x| < 2^-27] is π/2 - x
    in double-double, as π/2 - x is within [|x|^3 < 2^-81] of it
    ([DyAtanTiny.asin_tiny_real]); [asin 1] is π/2 and
    [acos(-1)] is π, and [acos 1 = 0] returns [None] for the kernel's
    exact case. Where [fast_asin_dir] and the others return, they round
    [asin x] and [acos x] ([fast_asin_dir_correct] and the others), with
    [asin] odd; they return the same with and without an FMA
    ([fast_asin_dir_fma] and the others). [fast_asin_range] and
    [fast_acos_range] give the ranges from the rules that run first. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Sterbenz.
From Inari Require Import Model Mpfr Elementary AtanReal AtanIdent TwoSum TwoProduct DyDriver
  NearF64 NearCells FastRound FastRoundErr FastDiv FastHypPos FastAtanTables FastAtanIdent
  FastAtanCore FastAtanAsm FastDdSqrt FastAtan1Quot FastAtan1.
From Inari Require DyExp DyPown DyAtanTiny DyExpRules FastExpErr MulRuTiny FastLogNorm.
From Inari Require Import FastAsinReal FastAsinAngle FastAsinSqrt FastAsinQuot.

Open Scope R_scope.

Local Lemma fabs_facts :
  forall x, is_finite x = true ->
  is_finite (fabs x) = true /\ B2R (fabs x) = Rabs (B2R x) /\ 0 <= B2R (fabs x).
Proof.
intros x Fx. unfold fabs. rewrite is_finite_Babs, B2R_Babs.
split; [exact Fx | split; [reflexivity | apply Rabs_pos]].
Qed.

(** ** The ranges the rules leave *)

Lemma fast_asin_range :
  forall x,
  is_finite x = true -> gt (fabs x) DyadicExp.one = false ->
  lt (fabs x) DyadicAtan.tiny_asin = false ->
  bpow radix2 (-27) <= Rabs (B2R x) <= 1.
Proof.
intros x Fx G1 G2.
destruct DyExp.one_B2R as (F1 & E1).
destruct (fabs_facts x Fx) as (Fa & Ea & _).
assert (Ft : is_finite DyadicAtan.tiny_asin = true) by (vm_compute; reflexivity).
apply gt_false in G1; [| exact Fa | exact F1].
apply lt_false in G2; [| exact Fa | exact Ft].
rewrite Ea, E1 in G1. rewrite Ea, DyAtanTiny.asin_lit_tiny in G2.
split; assumption.
Qed.

Lemma fast_acos_range :
  forall x, is_finite x = true -> gt (fabs x) DyadicExp.one = false -> Rabs (B2R x) <= 1.
Proof.
intros x Fx G1.
destruct DyExp.one_B2R as (F1 & E1).
destruct (fabs_facts x Fx) as (Fa & Ea & _).
apply gt_false in G1; [| exact Fa | exact F1].
rewrite Ea, E1 in G1. exact G1.
Qed.

(** ** Before the rounding *)

(** [fast_asin_atan] gives the same with and without an FMA. *)
Local Lemma asin_atan_fma :
  forall t, is_finite t = true -> bpow radix2 (-27) <= B2R t < 1 ->
  DyadicAtan.fast_asin_atan true t = DyadicAtan.fast_asin_atan false t.
Proof.
intros t Ft Ht.
unfold DyadicAtan.fast_asin_atan.
rewrite (sqrt1m_fma t Ft Ht).
destruct (DyadicAtan.fast_sqrt1m false t) as (rh, rl) eqn:Es.
cbv beta iota.
destruct (sqrt1m_facts false t rh rl Ft Ht Es) as (Frh & Frl & Hrh & Hrl & Hhalf & _).
destruct lit_asin_s as (Fs & Esv).
assert (Fz : is_finite zero = true) by reflexivity.
assert (Bz : B2R zero = 0) by reflexivity.
pose proof (bpow_gt_0 radix2 (-28)) as P28.
pose proof (bpow_gt_0 radix2 (-27)) as P27.
pose proof (bpow_gt_0 radix2 (-52)) as P52.
pose proof (bpow_gt_0 radix2 (-50)) as P50.
pose proof (bpow_le radix2 (-80) (-28) ltac:(lia)) as K28.
pose proof (bpow_le radix2 (-80) (-27) ltac:(lia)) as K27.
pose proof (bpow_le radix2 (-53) (-52) ltac:(lia)) as K52.
pose proof (bpow_le radix2 (-53) (-50) ltac:(lia)) as K50.
(* [dd_div_fma]'s side conditions on [rh + rl] and on [t + 0]. *)
assert (Hrl52 : Rabs (B2R rl) <= bpow radix2 (-52) * B2R rh).
{ apply Rle_trans with (1 := Hrl). apply Rmult_le_compat_r; lra. }
assert (Hrl50 : Rabs (B2R rl) <= bpow radix2 (-50) * B2R rh).
{ apply Rle_trans with (1 := Hrl). apply Rmult_le_compat_r; lra. }
assert (Hz50 : Rabs (B2R zero) <= bpow radix2 (-50) * B2R t).
{ rewrite Bz, Rabs_R0. apply Rmult_le_pos; lra. }
assert (Hz52 : Rabs (B2R zero) <= bpow radix2 (-52) * B2R t).
{ rewrite Bz, Rabs_R0. apply Rmult_le_pos; lra. }
destruct (Model.le t DyadicAtan.asin_s) eqn:L.
- (* [t <= 181/256]: [t / r]. *)
  pose proof (ge_true DyadicAtan.asin_s t Fs Ft L) as G. rewrite Esv in G.
  assert (Hn : bpow radix2 (-80) <= B2R t <= 4) by (split; lra).
  assert (Hd : / 2 <= B2R rh <= 4) by (split; [exact (Hhalf G) | lra]).
  rewrite (dd_div_fma t zero rh rl Ft Fz Frh Frl Hn Hz50 Hd Hrl52).
  destruct (Fast.dd_div false t zero rh rl) as (qh, ql) eqn:Ed.
  cbv beta iota.
  destruct (asin_quot false t rh rl qh ql Ft Ht Es ltac:(rewrite L; exact Ed))
    as (Fqh & Fql & Hqh & Hql & _).
  apply fast_atan_core_fma; assumption.
- (* [t > 181/256]: [r / t]. *)
  pose proof (ge_false DyadicAtan.asin_s t Fs Ft L) as G. rewrite Esv in G.
  assert (Hn : bpow radix2 (-80) <= B2R rh <= 4) by (split; lra).
  assert (Hd : / 2 <= B2R t <= 4) by (split; lra).
  rewrite (dd_div_fma rh rl t zero Frh Frl Ft Fz Hn Hrl50 Hd Hz52).
  destruct (Fast.dd_div false rh rl t zero) as (qh, ql) eqn:Ed.
  cbv beta iota.
  destruct (asin_quot false t rh rl qh ql Ft Ht Es ltac:(rewrite L; exact Ed))
    as (Fqh & Fql & Hqh & Hql & _).
  apply fast_atan_core_fma; assumption.
Qed.

(** [B2R l] of an [f64] literal [l], as [m * 2^e] (as in [FastHypPos.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** [PIO2] is a normalized double-double: [PIO2.0 + PIO2.1] rounds to
    [PIO2.0], checked by computation. *)
Local Lemma pio2_pair :
  is_finite (from_bits (fst DyadicAtan.PIO2)) = true /\
  is_finite (from_bits (snd DyadicAtan.PIO2)) = true /\
  B2R (from_bits (fst DyadicAtan.PIO2))
    = RN (B2R (from_bits (fst DyadicAtan.PIO2)) + B2R (from_bits (snd DyadicAtan.PIO2))) /\
  Rabs (B2R (from_bits (fst DyadicAtan.PIO2)) + B2R (from_bits (snd DyadicAtan.PIO2)) - PI / 2)
    <= bpow radix2 (-107).
Proof.
destruct fast_pio2_correct as (Fh & Fl & Eh & Hl & Hp).
split; [exact Fh | split; [exact Fl | split; [| exact Hp]]].
assert (Hs : Rabs (B2R (from_bits (fst DyadicAtan.PIO2)) + B2R (from_bits (snd DyadicAtan.PIO2)))
             <= bpow radix2 1023 + bpow radix2 971).
{ apply Rabs_le_inv in Hl.
  assert (K : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
  assert (2 <= bpow radix2 1023) by (change 2 with (bpow radix2 1); apply bpow_le; lia).
  pose proof (bpow_gt_0 radix2 971).
  apply Rabs_le. rewrite K in Hl. rewrite Eh. lra. }
destruct (add_no_overflow _ _ Fh Fl Hs) as (_ & Ea).
rewrite <- Ea.
rewrite <- (SF2R_B2SF _ _ (add (from_bits (fst DyadicAtan.PIO2)) (from_bits (snd DyadicAtan.PIO2)))).
rewrite <- (SF2R_B2SF _ _ (from_bits (fst DyadicAtan.PIO2))).
f_equal; vm_compute; reflexivity.
Qed.

Local Lemma lit_err70 : B2R DyadicAtan.err70 = bpow radix2 (-70).
Proof.
lit_B2R. change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
reflexivity.
Qed.

Local Lemma lit_err62 : B2R DyadicAtan.err62 = bpow radix2 (-62).
Proof.
lit_B2R. change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
reflexivity.
Qed.

(** [DyTrigReduce.m_one_R]. *)
Local Lemma lit_m_one : is_finite DyadicExp.m_one = true /\ B2R DyadicExp.m_one = -1.
Proof.
split; [vm_compute; reflexivity |].
lit_B2R. assert (K : bpow radix2 (-52) = / 4503599627370496) by reflexivity.
rewrite K. lra.
Qed.

Local Lemma eq_R :
  forall x y, is_finite x = true -> is_finite y = true ->
  (Model.eq x y = true -> B2R x = B2R y) /\ (Model.eq x y = false -> B2R x <> B2R y).
Proof.
intros x y Fx Fy. unfold Model.eq. rewrite Beqb_correct by assumption.
destruct (Req_bool_spec (B2R x) (B2R y)); split; intros Hq; (discriminate Hq || assumption).
Qed.

(** The argument [fast_asin_atan] gets from [fast_asin_pos] and
    [fast_acos_val]. *)
Local Lemma asin_t_range :
  forall t, is_finite t = true -> bpow radix2 (-27) <= B2R t <= 1 ->
  Model.eq t DyadicExp.one = false -> bpow radix2 (-27) <= B2R t < 1.
Proof.
intros t Ft Ht Q.
destruct DyExp.one_B2R as (F1 & E1).
apply (proj2 (eq_R t DyadicExp.one Ft F1)) in Q. rewrite E1 in Q.
split; [apply Ht |].
destruct (proj2 Ht) as [H | H]; [exact H | contradiction].
Qed.

Local Lemma acos_t_range :
  forall x, is_finite x = true -> Rabs (B2R x) <= 1 ->
  Model.eq x DyadicExp.one = false -> Model.lt (fabs x) DyadicAtan.tiny_asin = false ->
  Model.eq x DyadicExp.m_one = false ->
  bpow radix2 (-27) <= B2R (fabs x) < 1.
Proof.
intros x Fx Hx Q1 Q2 Q3.
destruct DyExp.one_B2R as (F1 & E1). destruct lit_m_one as (Fm & Em).
destruct (fabs_facts x Fx) as (Ft & Et & _).
apply (proj2 (eq_R x _ Fx F1)) in Q1. apply (proj2 (eq_R x _ Fx Fm)) in Q3.
rewrite E1 in Q1. rewrite Em in Q3.
apply FastHypPos.lt_false in Q2; [| exact Ft | vm_compute; reflexivity].
rewrite DyAtanTiny.asin_lit_tiny in Q2.
split; [exact Q2 |]. rewrite Et.
destruct Hx as [H | H]; [exact H | exfalso].
destruct (Rcase_abs (B2R x)) as [N | P].
- rewrite Rabs_left in H by exact N. apply Q3. lra.
- rewrite Rabs_pos_eq in H by lra. apply Q1. exact H.
Qed.

Lemma fast_asin_atan_correct :
  forall fma t ch cl,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < 1 ->
  DyadicAtan.fast_asin_atan fma t = Some (ch, cl) ->
  is_finite ch = true /\ is_finite cl = true /\ B2R ch = RN (B2R ch + B2R cl) /\
  let V := if Rle_bool (B2R t) (181 / 256) then asin (B2R t) else acos (B2R t) in
  Rabs (B2R ch + B2R cl - V) <= bpow radix2 (-73) * V.
Proof.
intros fma t ch cl Ft Ht H.
unfold DyadicAtan.fast_asin_atan in H.
destruct (DyadicAtan.fast_sqrt1m fma t) as (rh, rl) eqn:Es.
cbv beta iota in H.
destruct (if Model.le t DyadicAtan.asin_s then Fast.dd_div fma t zero rh rl
          else Fast.dd_div fma rh rl t zero) as (qh, ql) eqn:Eq.
cbv beta iota in H.
destruct (asin_quot fma t rh rl qh ql Ft Ht Es Eq)
  as (Fqh & Fql & Hqh & Hql & q & Hq & Hqq & EV).
destruct (fast_atan_core_correct fma qh ql ch cl Fqh Fql Hqh Hql H) as (Fch & Fcl & Ech & Hc).
split; [exact Fch | split; [exact Fcl | split; [exact Ech |]]].
cbv zeta. rewrite EV.
apply (atan_rel_err (B2R qh + B2R ql) q); [| exact Hqq | exact Hc].
pose proof (bpow_gt_0 radix2 (-27)). lra.
Qed.

Theorem fast_asin_pos_correct :
  forall fma t h l e err,
  is_finite t = true -> bpow radix2 (-27) <= B2R t <= 1 ->
  DyadicAtan.fast_asin_pos fma t = Some (h, l, e, err) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= e <= 1022)%Z /\
  exists p, (55 <= p <= 105)%Z /\ B2R err = bpow radix2 (- p) /\
    Rabs (asin (B2R t) * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (- p).
Proof.
intros fma t h l e err Ft Ht H.
destruct DyExp.one_B2R as (F1 & E1).
destruct lit_asin_s as (Fs & Es).
pose proof (bpow_gt_0 radix2 (-28)) as P28.
pose proof (bpow_gt_0 radix2 (-73)) as P73.
pose proof (bpow_le radix2 (-1020) (-28) ltac:(lia)) as B1020.
unfold DyadicAtan.fast_asin_pos in H.
destruct (Model.eq t DyadicExp.one) eqn:Q.
- (* [asin 1 = π/2]. *)
  injection H as <- <- <- <-.
  apply (proj1 (eq_R t _ Ft F1)) in Q. rewrite E1 in Q.
  destruct pio2_pair as (Fh & Fl & Eh & Hp).
  split; [exact Fh | split; [exact Fl | split; [exact Eh | split; [lia |]]]].
  exists 70%Z. split; [lia | split; [exact lit_err70 |]].
  rewrite Q, asin_1. change (bpow radix2 (- 0)) with 1. rewrite Rmult_1_r.
  rewrite Rabs_minus_sym. apply Rle_trans with (1 := Hp). apply bpow_le. lia.
- pose proof (asin_t_range t Ft Ht Q) as Ht'.
  destruct (DyadicAtan.fast_asin_atan fma t) as [[ch cl]|] eqn:Ea; [| discriminate H].
  injection H as Ho.
  destruct (fast_asin_atan_correct fma t ch cl Ft Ht' Ea) as (Fch & Fcl & Ech & Hc).
  pose proof (asin_atan_range t Ft Ht') as HV.
  cbv zeta in Hc.
  destruct (Model.gt t DyadicAtan.asin_s) eqn:G.
  + (* Above the split, [asin t = π/2 - acos t]. *)
    apply gt_true in G; [| exact Ft | exact Fs]. rewrite Es in G.
    rewrite Rle_bool_false in Hc, HV by lra.
    assert (Ha : Rabs (B2R ch + B2R cl - acos (B2R t)) <= bpow radix2 (-73)) by nra.
    destruct (octant_correct true false ch cl (acos (B2R t)) h l e err Fch Fcl Ech
                ltac:(lra) Ha Ho) as (Fh & Fl & Eh & He & Herr & Hb).
    split; [exact Fh | split; [exact Fl | split; [exact Eh | split; [lia |]]]].
    exists 70%Z. split; [lia | split; [exact Herr |]].
    cbv beta iota in Hb.
    replace (PI / 2 - acos (B2R t)) with (asin (B2R t)) in Hb
      by (pose proof (asin_plus_acos (B2R t) ltac:(lra)); lra).
    exact Hb.
  + apply gt_false in G; [| exact Ft | exact Fs]. rewrite Es in G.
    rewrite Rle_bool_true in Hc, HV by lra.
    assert (Hv : bpow radix2 (-1020) <= asin (B2R t)) by lra.
    destruct (octant_correct false false ch cl (asin (B2R t)) h l e err Fch Fcl Ech
                ltac:(lra) (conj Hv Hc) Ho) as (Fh & Fl & Eh & He & Herr & Hb).
    split; [exact Fh | split; [exact Fl | split; [exact Eh | split; [lia |]]]].
    exists 70%Z. split; [lia | split; [exact Herr | exact Hb]].
Qed.

Theorem fast_acos_val_correct :
  forall fma x h l e err,
  is_finite x = true -> Rabs (B2R x) <= 1 ->
  DyadicAtan.fast_acos_val fma x = Some (h, l, e, err) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= e <= 1022)%Z /\
  exists p, (55 <= p <= 105)%Z /\ B2R err = bpow radix2 (- p) /\
    Rabs (acos (B2R x) * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (- p).
Proof.
intros fma x h l e err Fx Hx H.
destruct DyExp.one_B2R as (F1 & E1).
destruct lit_m_one as (Fm & Em).
destruct lit_asin_s as (Fs & Es).
destruct (fabs_facts x Fx) as (Ft & Et & _).
pose proof (bpow_gt_0 radix2 (-28)) as P28.
pose proof (bpow_gt_0 radix2 (-73)) as P73.
pose proof (bpow_le radix2 (-1020) (-28) ltac:(lia)) as B1020.
pose proof (Rabs_le_inv _ _ Hx) as Hx'.
(* [acos x = π/2 - asin x]. *)
pose proof (asin_plus_acos (B2R x) Hx') as Hsa.
unfold DyadicAtan.fast_acos_val in H.
destruct (Model.eq x DyadicExp.one) eqn:Q1; [discriminate H |].
destruct (Model.lt (fabs x) DyadicAtan.tiny_asin) eqn:Q2.
- (* [|x| < 2^-27]: [π/2 - x] is within [|x|^3] of [acos x]. *)
  apply FastHypPos.lt_true in Q2; [| exact Ft | vm_compute; reflexivity].
  rewrite Et, DyAtanTiny.asin_lit_tiny in Q2.
  assert (Fo : is_finite (opp x) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fx).
  assert (Eo : B2R (opp x) = - B2R x) by (unfold opp; apply B2R_Bopp).
  assert (Ho : Rabs (B2R (opp x)) <= B2R DyadicExp.one) by (rewrite Eo, Rabs_Ropp, E1; exact Hx).
  assert (Hz : Rabs (B2R zero) <= bpow radix2 (-52))
    by (change (B2R zero) with 0; rewrite Rabs_R0; apply bpow_ge_0).
  pose proof (pio2_add_correct DyadicExp.one (opp x) zero F1 Fo eq_refl (or_intror E1) Ho Hz)
    as P.
  destruct (DyadicAtan.pio2_add DyadicExp.one (opp x) zero) as (h', l').
  injection H as <- <- <- <-.
  destruct P as (Fh & Fl & Eh & Hp).
  split; [exact Fh | split; [exact Fl | split; [exact Eh | split; [lia |]]]].
  exists 70%Z. split; [lia | split; [exact lit_err70 |]].
  assert (K27 : bpow radix2 (-27) = / 134217728) by reflexivity.
  assert (K70 : bpow radix2 (Z.opp 70) = / 1180591620717411303424) by reflexivity.
  assert (K102 : bpow radix2 (-102) = / 5070602400912917605986812821504) by reflexivity.
  rewrite K27 in Q2. rewrite K70. rewrite K102 in Hp.
  assert (A : Rabs (asin (B2R x) - B2R x) <= / 2417851639229258349412352).
  { assert (C : forall y, 0 < y < / 134217728 -> 0 <= asin y - y <= / 2417851639229258349412352).
    { intros y Hy.
      assert (Hy' : 0 < y < bpow radix2 (-27)) by (rewrite K27; exact Hy).
      destruct (DyAtanTiny.asin_tiny_real y Hy') as (A1 & A2).
      assert (y * y < / 134217728 * / 134217728) by nra.
      assert (y * y * y < / 134217728 * / 134217728 * / 134217728) by nra.
      lra. }
    destruct (Rtotal_order (B2R x) 0) as [N | [Z | P]].
    - rewrite Rabs_left in Q2 by exact N.
      destruct (C (- B2R x) ltac:(lra)) as (C1 & C2). rewrite asin_opp in C1, C2.
      apply Rabs_le. lra.
    - rewrite Z, asin_0, Rminus_0_r, Rabs_R0. lra.
    - rewrite Rabs_pos_eq in Q2 by lra.
      destruct (C (B2R x) ltac:(lra)) as (C1 & C2).
      apply Rabs_le. lra. }
  change (bpow radix2 (- 0)) with 1. rewrite Rmult_1_r.
  rewrite E1, Eo in Hp. change (B2R zero) with 0 in Hp.
  apply Rabs_le_inv in A. apply Rabs_le_inv in Hp. apply Rabs_le. lra.
- destruct (Model.eq x DyadicExp.m_one) eqn:Q3.
  + (* [acos(-1) = π]. *)
    injection H as <- <- <- <-.
    apply (proj1 (eq_R x _ Fx Fm)) in Q3. rewrite Em in Q3.
    destruct pio2_pair as (Fh & Fl & Eh & Hp).
    split; [exact Fh | split; [exact Fl | split; [exact Eh | split; [lia |]]]].
    exists 70%Z. split; [lia | split; [exact lit_err70 |]].
    rewrite Q3. replace (-1) with (- (1)) by ring. rewrite acos_opp, acos_1, Rminus_0_r.
    assert (K : bpow radix2 (Z.opp 1) = / 2) by reflexivity. rewrite K.
    replace (PI * / 2) with (PI / 2) by (unfold Rdiv; reflexivity).
    rewrite Rabs_minus_sym. apply Rle_trans with (1 := Hp). apply bpow_le. lia.
  + pose proof (acos_t_range x Fx Hx Q1 Q2 Q3) as Ht.
    cbv zeta in H.
    destruct (DyadicAtan.fast_asin_atan fma (fabs x)) as [[ch cl]|] eqn:Ea; [| discriminate H].
    injection H as Ho.
    destruct (fast_asin_atan_correct fma (fabs x) ch cl Ft Ht Ea) as (Fch & Fcl & Ech & Hc).
    pose proof (asin_atan_range (fabs x) Ft Ht) as HV.
    cbv zeta in Hc.
    rewrite Et in Hc, HV, Ht.
    destruct (DyExp.lt_zero_spec x) as (N1 & N2).
    destruct (Model.le (fabs x) DyadicAtan.asin_s) eqn:L.
    * (* Up to the split, [acos x = π/2 - asin x] and [asin(-x) = -asin x]. *)
      pose proof (ge_true DyadicAtan.asin_s (fabs x) Fs Ft L) as G.
      rewrite Es, Et in G.
      rewrite Rle_bool_true in Hc, HV by lra.
      assert (Ha : Rabs (B2R ch + B2R cl - asin (Rabs (B2R x))) <= bpow radix2 (-73)) by nra.
      destruct (octant_correct true (Model.lt x zero) ch cl (asin (Rabs (B2R x))) h l e err
                  Fch Fcl Ech ltac:(lra) Ha Ho) as (Fh & Fl & Eh & He & Herr & Hb).
      split; [exact Fh | split; [exact Fl | split; [exact Eh | split; [lia |]]]].
      exists 70%Z. split; [lia | split; [exact Herr |]].
      cbv beta iota in Hb.
      destruct (Model.lt x zero) eqn:N.
      -- specialize (N1 eq_refl).
         rewrite (Rabs_left1 (B2R x)), asin_opp in Hb by exact N1.
         replace (PI / 2 + - asin (B2R x)) with (acos (B2R x)) in Hb by lra.
         exact Hb.
      -- specialize (N2 eq_refl).
         rewrite (Rabs_pos_eq (B2R x)) in Hb by exact N2.
         replace (PI / 2 - asin (B2R x)) with (acos (B2R x)) in Hb by lra.
         exact Hb.
    * (* Above it, [acos(-x) = π - acos x]. *)
      pose proof (ge_false DyadicAtan.asin_s (fabs x) Fs Ft L) as G.
      rewrite Es, Et in G.
      rewrite Rle_bool_false in Hc, HV by lra.
      destruct (Model.lt x zero) eqn:N.
      -- specialize (N1 eq_refl).
         assert (Ha : Rabs (B2R ch + B2R cl - acos (Rabs (B2R x))) <= bpow radix2 (-73)) by nra.
         destruct (octant_correct false true ch cl (acos (Rabs (B2R x))) h l e err
                     Fch Fcl Ech ltac:(lra) Ha Ho) as (Fh & Fl & Eh & He & Herr & Hb).
         split; [exact Fh | split; [exact Fl | split; [exact Eh | split; [lia |]]]].
         exists 70%Z. split; [lia | split; [exact Herr |]].
         cbv beta iota in Hb.
         rewrite (Rabs_left1 (B2R x)), acos_opp in Hb by exact N1.
         replace (PI - (PI - acos (B2R x))) with (acos (B2R x)) in Hb by ring.
         exact Hb.
      -- specialize (N2 eq_refl).
         rewrite (Rabs_pos_eq (B2R x)) in Hc, HV by exact N2.
         assert (Hv : bpow radix2 (-1020) <= acos (B2R x)) by lra.
         destruct (octant_correct false false ch cl (acos (B2R x)) h l e err
                     Fch Fcl Ech ltac:(lra) (conj Hv Hc) Ho)
           as (Fh & Fl & Eh & He & Herr & Hb).
         split; [exact Fh | split; [exact Fl | split; [exact Eh | split; [lia |]]]].
         exists 70%Z. split; [lia | split; [exact Herr | exact Hb]].
Qed.

Theorem fast_asin_pos_fma :
  forall t,
  is_finite t = true -> bpow radix2 (-27) <= B2R t <= 1 ->
  DyadicAtan.fast_asin_pos true t = DyadicAtan.fast_asin_pos false t.
Proof.
intros t Ft Ht.
unfold DyadicAtan.fast_asin_pos.
destruct (Model.eq t DyadicExp.one) eqn:Q; [reflexivity |].
rewrite (asin_atan_fma t Ft (asin_t_range t Ft Ht Q)). reflexivity.
Qed.

Theorem fast_acos_val_fma :
  forall x,
  is_finite x = true -> Rabs (B2R x) <= 1 ->
  DyadicAtan.fast_acos_val true x = DyadicAtan.fast_acos_val false x.
Proof.
intros x Fx Hx.
destruct (fabs_facts x Fx) as (Ft & _ & _).
unfold DyadicAtan.fast_acos_val.
destruct (Model.eq x DyadicExp.one) eqn:Q1; [reflexivity |].
destruct (Model.lt (fabs x) DyadicAtan.tiny_asin) eqn:Q2; [reflexivity |].
destruct (Model.eq x DyadicExp.m_one) eqn:Q3; [reflexivity |].
cbv zeta.
rewrite (asin_atan_fma (fabs x) Ft (acos_t_range x Fx Hx Q1 Q2 Q3)). reflexivity.
Qed.

(** ** The first stages *)

(** [fast_asin_atan1]: [fast_asin_atan] with [fast_atan1] in place of the
    core, within [2^-64 + 2^-84] of [V] relatively ([asin_quot],
    [FastAtan1.fast_atan1_correct], [FastAtan1.atan1_rel_err]). *)
Lemma fast_asin_atan1_correct :
  forall fma t ch cl,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < 1 ->
  DyadicAtan.fast_asin_atan1 fma t = Some (ch, cl) ->
  is_finite ch = true /\ is_finite cl = true /\ B2R ch = RN (B2R ch + B2R cl) /\
  let V := if Rle_bool (B2R t) (181 / 256) then asin (B2R t) else acos (B2R t) in
  Rabs (B2R ch + B2R cl - V) <= (bpow radix2 (-64) + bpow radix2 (-84)) * V.
Proof.
intros fma t ch cl Ft Ht H.
unfold DyadicAtan.fast_asin_atan1 in H.
destruct (DyadicAtan.fast_sqrt1m fma t) as (rh, rl) eqn:Es.
cbv beta iota in H.
destruct (if Model.le t DyadicAtan.asin_s then Fast.dd_div fma t zero rh rl
          else Fast.dd_div fma rh rl t zero) as (qh, ql) eqn:Eq.
cbv beta iota in H.
destruct (asin_quot fma t rh rl qh ql Ft Ht Es Eq)
  as (Fqh & Fql & Hqh & Hql & q & Hq & Hqq & EV).
destruct (FastAtan1.fast_atan1_correct fma qh ql ch cl Fqh Fql Hqh Hql H)
  as (Fch & Fcl & Ech & Hc).
split; [exact Fch | split; [exact Fcl | split; [exact Ech |]]].
cbv zeta. rewrite EV.
apply (FastAtan1.atan1_rel_err (B2R qh + B2R ql) q); [| exact Hqq | exact Hc].
pose proof (bpow_gt_0 radix2 (-27)). lra.
Qed.

(** [fast_asin_atan1] gives the same with and without an FMA. *)
Local Lemma asin_atan1_fma :
  forall t, is_finite t = true -> bpow radix2 (-27) <= B2R t < 1 ->
  DyadicAtan.fast_asin_atan1 true t = DyadicAtan.fast_asin_atan1 false t.
Proof.
intros t Ft Ht.
unfold DyadicAtan.fast_asin_atan1.
rewrite (sqrt1m_fma t Ft Ht).
destruct (DyadicAtan.fast_sqrt1m false t) as (rh, rl) eqn:Es.
cbv beta iota.
destruct (sqrt1m_facts false t rh rl Ft Ht Es) as (Frh & Frl & Hrh & Hrl & Hhalf & _).
destruct lit_asin_s as (Fs & Esv).
assert (Fz : is_finite zero = true) by reflexivity.
assert (Bz : B2R zero = 0) by reflexivity.
pose proof (bpow_gt_0 radix2 (-28)) as P28.
pose proof (bpow_gt_0 radix2 (-27)) as P27.
pose proof (bpow_gt_0 radix2 (-52)) as P52.
pose proof (bpow_gt_0 radix2 (-50)) as P50.
pose proof (bpow_le radix2 (-80) (-28) ltac:(lia)) as K28.
pose proof (bpow_le radix2 (-80) (-27) ltac:(lia)) as K27.
pose proof (bpow_le radix2 (-53) (-52) ltac:(lia)) as K52.
pose proof (bpow_le radix2 (-53) (-50) ltac:(lia)) as K50.
(* [dd_div_fma]'s side conditions on [rh + rl] and on [t + 0]. *)
assert (Hrl52 : Rabs (B2R rl) <= bpow radix2 (-52) * B2R rh).
{ apply Rle_trans with (1 := Hrl). apply Rmult_le_compat_r; lra. }
assert (Hrl50 : Rabs (B2R rl) <= bpow radix2 (-50) * B2R rh).
{ apply Rle_trans with (1 := Hrl). apply Rmult_le_compat_r; lra. }
assert (Hz50 : Rabs (B2R zero) <= bpow radix2 (-50) * B2R t).
{ rewrite Bz, Rabs_R0. apply Rmult_le_pos; lra. }
assert (Hz52 : Rabs (B2R zero) <= bpow radix2 (-52) * B2R t).
{ rewrite Bz, Rabs_R0. apply Rmult_le_pos; lra. }
destruct (Model.le t DyadicAtan.asin_s) eqn:L.
- (* [t <= 181/256]: [t / r]. *)
  pose proof (ge_true DyadicAtan.asin_s t Fs Ft L) as G. rewrite Esv in G.
  assert (Hn : bpow radix2 (-80) <= B2R t <= 4) by (split; lra).
  assert (Hd : / 2 <= B2R rh <= 4) by (split; [exact (Hhalf G) | lra]).
  rewrite (dd_div_fma t zero rh rl Ft Fz Frh Frl Hn Hz50 Hd Hrl52).
  destruct (Fast.dd_div false t zero rh rl) as (qh, ql) eqn:Ed.
  cbv beta iota.
  destruct (asin_quot false t rh rl qh ql Ft Ht Es ltac:(rewrite L; exact Ed))
    as (Fqh & Fql & Hqh & Hql & _).
  apply FastAtan1.fast_atan1_fma; assumption.
- (* [t > 181/256]: [r / t]. *)
  pose proof (ge_false DyadicAtan.asin_s t Fs Ft L) as G. rewrite Esv in G.
  assert (Hn : bpow radix2 (-80) <= B2R rh <= 4) by (split; lra).
  assert (Hd : / 2 <= B2R t <= 4) by (split; lra).
  rewrite (dd_div_fma rh rl t zero Frh Frl Ft Fz Hn Hrl50 Hd Hz52).
  destruct (Fast.dd_div false rh rl t zero) as (qh, ql) eqn:Ed.
  cbv beta iota.
  destruct (asin_quot false t rh rl qh ql Ft Ht Es ltac:(rewrite L; exact Ed))
    as (Fqh & Fql & Hqh & Hql & _).
  apply FastAtan1.fast_atan1_fma; assumption.
Qed.

(** The [d] of [octant_bound] for [fast_asin_atan1]: [d] relatively, as
    [fast_asin_atan1_correct] gives it, and so [d] absolutely, as [V <=
    4/5]; [3 d <= 2^-62]. *)
Local Lemma asin1_d :
  bpow radix2 (-100) <= bpow radix2 (-64) + bpow radix2 (-84) <= bpow radix2 (-60) /\
  3 * (bpow radix2 (-64) + bpow radix2 (-84)) <= bpow radix2 (-62).
Proof. cbn [bpow radix_val radix2]. lra. Qed.

Local Lemma asin1_abs :
  forall a V, 0 <= V <= 1 ->
  Rabs a <= (bpow radix2 (-64) + bpow radix2 (-84)) * V ->
  Rabs a <= bpow radix2 (-64) + bpow radix2 (-84).
Proof.
intros a V HV H.
apply Rle_trans with (1 := H).
pose proof (bpow_gt_0 radix2 (-64)). pose proof (bpow_gt_0 radix2 (-84)).
rewrite <- (Rmult_1_r (bpow radix2 (-64) + bpow radix2 (-84))) at 2.
apply Rmult_le_compat_l; lra.
Qed.

(** [fast_asin_pos1] and [fast_acos_val1], with the bounds of
    [fast_asin_pos] and [fast_acos_val]. *)
Theorem fast_asin_pos1_correct :
  forall fma t h l e err,
  is_finite t = true -> bpow radix2 (-27) <= B2R t <= 1 ->
  DyadicAtan.fast_asin_pos1 fma t = Some (h, l, e, err) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= e <= 1022)%Z /\
  exists p, (55 <= p <= 105)%Z /\ B2R err = bpow radix2 (- p) /\
    Rabs (asin (B2R t) * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (- p).
Proof.
intros fma t h l e err Ft Ht H.
destruct DyExp.one_B2R as (F1 & E1).
destruct lit_asin_s as (Fs & Es).
destruct asin1_d as (Hd & H3d).
pose proof (bpow_gt_0 radix2 (-28)) as P28.
pose proof (bpow_gt_0 radix2 (-64)) as P64.
pose proof (bpow_gt_0 radix2 (-84)) as P84.
assert (K1020 : (-1020 <= -28)%Z) by lia.
pose proof (bpow_le radix2 (-1020) (-28) K1020) as B1020.
unfold DyadicAtan.fast_asin_pos1 in H.
destruct (Model.eq t DyadicExp.one) eqn:Q.
- (* [asin 1 = π/2]. *)
  injection H as <- <- <- <-.
  apply (proj1 (eq_R t _ Ft F1)) in Q. rewrite E1 in Q.
  destruct pio2_pair as (Fh & Fl & Eh & Hp).
  split; [exact Fh | split; [exact Fl | split; [exact Eh | split; [lia |]]]].
  exists 70%Z. split; [lia | split; [exact lit_err70 |]].
  rewrite Q, asin_1. change (bpow radix2 (- 0)) with 1. rewrite Rmult_1_r.
  rewrite Rabs_minus_sym. apply Rle_trans with (1 := Hp). apply bpow_le. lia.
- pose proof (asin_t_range t Ft Ht Q) as Ht'.
  destruct (DyadicAtan.fast_asin_atan1 fma t) as [[ch cl]|] eqn:Ea; [| discriminate H].
  cbv beta iota in H.
  destruct (DyadicAtan.octant (Model.gt t DyadicAtan.asin_s) false ch cl)
    as [[[h' l'] e'] err'] eqn:Ho.
  cbv beta iota in H.
  injection H as <- <- <- <-.
  destruct (fast_asin_atan1_correct fma t ch cl Ft Ht' Ea) as (Fch & Fcl & Ech & Hc).
  pose proof (asin_atan_range t Ft Ht') as HV.
  cbv zeta in Hc.
  destruct (Model.gt t DyadicAtan.asin_s) eqn:G.
  + (* Above the split, [asin t = π/2 - acos t], within [3 d] absolutely. *)
    apply gt_true in G; [| exact Ft | exact Fs]. rewrite Es in G.
    rewrite Rle_bool_false in Hc, HV by lra.
    assert (Ha : Rabs (B2R ch + B2R cl - acos (B2R t))
                 <= bpow radix2 (-64) + bpow radix2 (-84)).
    { apply (asin1_abs _ (acos (B2R t))); [lra | exact Hc]. }
    destruct (octant_bound true false ch cl (acos (B2R t)) h' l' e' err'
                (bpow radix2 (-64) + bpow radix2 (-84)) Fch Fcl Ech ltac:(lra) Hd Ha Ho)
      as (Fh & Fl & Eh & He & Hb).
    split; [exact Fh | split; [exact Fl | split; [exact Eh | split; [lia |]]]].
    exists 62%Z. split; [lia | split; [exact lit_err62 |]].
    cbv beta iota in Hb.
    replace (PI / 2 - acos (B2R t)) with (asin (B2R t)) in Hb
      by (pose proof (asin_plus_acos (B2R t) ltac:(lra)); lra).
    apply Rle_trans with (1 := Hb). exact H3d.
  + (* Up to it, [asin t] within [3 d] relatively. *)
    apply gt_false in G; [| exact Ft | exact Fs]. rewrite Es in G.
    rewrite Rle_bool_true in Hc, HV by lra.
    assert (Hv : bpow radix2 (-1020) <= asin (B2R t)) by lra.
    destruct (octant_bound false false ch cl (asin (B2R t)) h' l' e' err'
                (bpow radix2 (-64) + bpow radix2 (-84)) Fch Fcl Ech ltac:(lra) Hd
                (conj Hv Hc) Ho)
      as (Fh & Fl & Eh & He & Hb).
    split; [exact Fh | split; [exact Fl | split; [exact Eh | split; [lia |]]]].
    exists 62%Z. split; [lia | split; [exact lit_err62 |]].
    cbv beta iota in Hb.
    apply Rle_trans with (1 := Hb). exact H3d.
Qed.

Theorem fast_acos_val1_correct :
  forall fma x h l e err,
  is_finite x = true -> Rabs (B2R x) <= 1 ->
  DyadicAtan.fast_acos_val1 fma x = Some (h, l, e, err) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= e <= 1022)%Z /\
  exists p, (55 <= p <= 105)%Z /\ B2R err = bpow radix2 (- p) /\
    Rabs (acos (B2R x) * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (- p).
Proof.
intros fma x h l e err Fx Hx H.
destruct DyExp.one_B2R as (F1 & E1).
destruct lit_m_one as (Fm & Em).
destruct lit_asin_s as (Fs & Es).
destruct (fabs_facts x Fx) as (Ft & Et & _).
destruct asin1_d as (Hd & H3d).
pose proof (bpow_gt_0 radix2 (-28)) as P28.
pose proof (bpow_gt_0 radix2 (-64)) as P64.
pose proof (bpow_gt_0 radix2 (-84)) as P84.
assert (K1020 : (-1020 <= -28)%Z) by lia.
pose proof (bpow_le radix2 (-1020) (-28) K1020) as B1020.
pose proof (Rabs_le_inv _ _ Hx) as Hx'.
(* [acos x = π/2 - asin x]. *)
pose proof (asin_plus_acos (B2R x) Hx') as Hsa.
unfold DyadicAtan.fast_acos_val1 in H.
destruct (Model.eq x DyadicExp.one) eqn:Q1; [discriminate H |].
destruct (Model.lt (fabs x) DyadicAtan.tiny_asin) eqn:Q2.
- (* [|x| < 2^-27]: [π/2 - x] is within [|x|^3] of [acos x]. *)
  apply FastHypPos.lt_true in Q2; [| exact Ft | vm_compute; reflexivity].
  rewrite Et, DyAtanTiny.asin_lit_tiny in Q2.
  assert (Fo : is_finite (opp x) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fx).
  assert (Eo : B2R (opp x) = - B2R x) by (unfold opp; apply B2R_Bopp).
  assert (Ho : Rabs (B2R (opp x)) <= B2R DyadicExp.one) by (rewrite Eo, Rabs_Ropp, E1; exact Hx).
  assert (Hz : Rabs (B2R zero) <= bpow radix2 (-52))
    by (change (B2R zero) with 0; rewrite Rabs_R0; apply bpow_ge_0).
  pose proof (pio2_add_correct DyadicExp.one (opp x) zero F1 Fo eq_refl (or_intror E1) Ho Hz)
    as P.
  destruct (DyadicAtan.pio2_add DyadicExp.one (opp x) zero) as (h', l').
  injection H as <- <- <- <-.
  destruct P as (Fh & Fl & Eh & Hp).
  split; [exact Fh | split; [exact Fl | split; [exact Eh | split; [lia |]]]].
  exists 70%Z. split; [lia | split; [exact lit_err70 |]].
  assert (K27 : bpow radix2 (-27) = / 134217728) by reflexivity.
  assert (K70 : bpow radix2 (Z.opp 70) = / 1180591620717411303424) by reflexivity.
  assert (K102 : bpow radix2 (-102) = / 5070602400912917605986812821504) by reflexivity.
  rewrite K27 in Q2. rewrite K70. rewrite K102 in Hp.
  assert (A : Rabs (asin (B2R x) - B2R x) <= / 2417851639229258349412352).
  { assert (C : forall y, 0 < y < / 134217728 -> 0 <= asin y - y <= / 2417851639229258349412352).
    { intros y Hy.
      assert (Hy' : 0 < y < bpow radix2 (-27)) by (rewrite K27; exact Hy).
      destruct (DyAtanTiny.asin_tiny_real y Hy') as (A1 & A2).
      assert (y * y < / 134217728 * / 134217728) by nra.
      assert (y * y * y < / 134217728 * / 134217728 * / 134217728) by nra.
      lra. }
    destruct (Rtotal_order (B2R x) 0) as [N | [Z | P]].
    - rewrite Rabs_left in Q2 by exact N.
      destruct (C (- B2R x) ltac:(lra)) as (C1 & C2). rewrite asin_opp in C1, C2.
      apply Rabs_le. lra.
    - rewrite Z, asin_0, Rminus_0_r, Rabs_R0. lra.
    - rewrite Rabs_pos_eq in Q2 by lra.
      destruct (C (B2R x) ltac:(lra)) as (C1 & C2).
      apply Rabs_le. lra. }
  change (bpow radix2 (- 0)) with 1. rewrite Rmult_1_r.
  rewrite E1, Eo in Hp. change (B2R zero) with 0 in Hp.
  apply Rabs_le_inv in A. apply Rabs_le_inv in Hp. apply Rabs_le. lra.
- destruct (Model.eq x DyadicExp.m_one) eqn:Q3.
  + (* [acos(-1) = π]. *)
    injection H as <- <- <- <-.
    apply (proj1 (eq_R x _ Fx Fm)) in Q3. rewrite Em in Q3.
    destruct pio2_pair as (Fh & Fl & Eh & Hp).
    split; [exact Fh | split; [exact Fl | split; [exact Eh | split; [lia |]]]].
    exists 70%Z. split; [lia | split; [exact lit_err70 |]].
    rewrite Q3. replace (-1) with (- (1)) by ring. rewrite acos_opp, acos_1, Rminus_0_r.
    assert (K : bpow radix2 (Z.opp 1) = / 2) by reflexivity. rewrite K.
    replace (PI * / 2) with (PI / 2) by (unfold Rdiv; reflexivity).
    rewrite Rabs_minus_sym. apply Rle_trans with (1 := Hp). apply bpow_le. lia.
  + pose proof (acos_t_range x Fx Hx Q1 Q2 Q3) as Ht.
    cbv zeta in H.
    destruct (DyadicAtan.fast_asin_atan1 fma (fabs x)) as [[ch cl]|] eqn:Ea; [| discriminate H].
    cbv beta iota in H.
    destruct (DyadicAtan.octant (Model.le (fabs x) DyadicAtan.asin_s) (Model.lt x zero) ch cl)
      as [[[h' l'] e'] err'] eqn:Ho.
    cbv beta iota in H.
    injection H as <- <- <- <-.
    destruct (fast_asin_atan1_correct fma (fabs x) ch cl Ft Ht Ea) as (Fch & Fcl & Ech & Hc).
    pose proof (asin_atan_range (fabs x) Ft Ht) as HV.
    cbv zeta in Hc.
    rewrite Et in Hc, HV, Ht.
    destruct (DyExp.lt_zero_spec x) as (N1 & N2).
    destruct (Model.le (fabs x) DyadicAtan.asin_s) eqn:L.
    * (* Up to the split, [acos x = π/2 - asin x] and [asin(-x) = -asin x],
         within [3 d] absolutely. *)
      pose proof (ge_true DyadicAtan.asin_s (fabs x) Fs Ft L) as G.
      rewrite Es, Et in G.
      rewrite Rle_bool_true in Hc, HV by lra.
      assert (Ha : Rabs (B2R ch + B2R cl - asin (Rabs (B2R x)))
                   <= bpow radix2 (-64) + bpow radix2 (-84)).
      { apply (asin1_abs _ (asin (Rabs (B2R x)))); [lra | exact Hc]. }
      destruct (octant_bound true (Model.lt x zero) ch cl (asin (Rabs (B2R x))) h' l' e' err'
                  (bpow radix2 (-64) + bpow radix2 (-84)) Fch Fcl Ech ltac:(lra) Hd Ha Ho)
        as (Fh & Fl & Eh & He & Hb).
      split; [exact Fh | split; [exact Fl | split; [exact Eh | split; [lia |]]]].
      exists 62%Z. split; [lia | split; [exact lit_err62 |]].
      cbv beta iota in Hb.
      apply Rle_trans with (2 := H3d).
      destruct (Model.lt x zero) eqn:N.
      -- specialize (N1 eq_refl).
         rewrite (Rabs_left1 (B2R x)), asin_opp in Hb by exact N1.
         replace (PI / 2 + - asin (B2R x)) with (acos (B2R x)) in Hb by lra.
         exact Hb.
      -- specialize (N2 eq_refl).
         rewrite (Rabs_pos_eq (B2R x)) in Hb by exact N2.
         replace (PI / 2 - asin (B2R x)) with (acos (B2R x)) in Hb by lra.
         exact Hb.
    * (* Above it, [acos(-x) = π - acos x] within [3 d] absolutely, and
         [acos x] within [3 d] relatively. *)
      pose proof (ge_false DyadicAtan.asin_s (fabs x) Fs Ft L) as G.
      rewrite Es, Et in G.
      rewrite Rle_bool_false in Hc, HV by lra.
      destruct (Model.lt x zero) eqn:N.
      -- specialize (N1 eq_refl).
         assert (Ha : Rabs (B2R ch + B2R cl - acos (Rabs (B2R x)))
                      <= bpow radix2 (-64) + bpow radix2 (-84)).
         { apply (asin1_abs _ (acos (Rabs (B2R x)))); [lra | exact Hc]. }
         destruct (octant_bound false true ch cl (acos (Rabs (B2R x))) h' l' e' err'
                     (bpow radix2 (-64) + bpow radix2 (-84)) Fch Fcl Ech ltac:(lra) Hd Ha Ho)
           as (Fh & Fl & Eh & He & Hb).
         split; [exact Fh | split; [exact Fl | split; [exact Eh | split; [lia |]]]].
         exists 62%Z. split; [lia | split; [exact lit_err62 |]].
         cbv beta iota in Hb.
         rewrite (Rabs_left1 (B2R x)), acos_opp in Hb by exact N1.
         replace (PI - (PI - acos (B2R x))) with (acos (B2R x)) in Hb by ring.
         apply Rle_trans with (1 := Hb). exact H3d.
      -- specialize (N2 eq_refl).
         rewrite (Rabs_pos_eq (B2R x)) in Hc, HV by exact N2.
         assert (Hv : bpow radix2 (-1020) <= acos (B2R x)) by lra.
         destruct (octant_bound false false ch cl (acos (B2R x)) h' l' e' err'
                     (bpow radix2 (-64) + bpow radix2 (-84)) Fch Fcl Ech ltac:(lra) Hd
                     (conj Hv Hc) Ho)
           as (Fh & Fl & Eh & He & Hb).
         split; [exact Fh | split; [exact Fl | split; [exact Eh | split; [lia |]]]].
         exists 62%Z. split; [lia | split; [exact lit_err62 |]].
         cbv beta iota in Hb.
         apply Rle_trans with (1 := Hb). exact H3d.
Qed.

Theorem fast_asin_pos1_fma :
  forall t,
  is_finite t = true -> bpow radix2 (-27) <= B2R t <= 1 ->
  DyadicAtan.fast_asin_pos1 true t = DyadicAtan.fast_asin_pos1 false t.
Proof.
intros t Ft Ht.
unfold DyadicAtan.fast_asin_pos1.
destruct (Model.eq t DyadicExp.one) eqn:Q; [reflexivity |].
rewrite (asin_atan1_fma t Ft (asin_t_range t Ft Ht Q)). reflexivity.
Qed.

Theorem fast_acos_val1_fma :
  forall x,
  is_finite x = true -> Rabs (B2R x) <= 1 ->
  DyadicAtan.fast_acos_val1 true x = DyadicAtan.fast_acos_val1 false x.
Proof.
intros x Fx Hx.
destruct (fabs_facts x Fx) as (Ft & _ & _).
unfold DyadicAtan.fast_acos_val1.
destruct (Model.eq x DyadicExp.one) eqn:Q1; [reflexivity |].
destruct (Model.lt (fabs x) DyadicAtan.tiny_asin) eqn:Q2; [reflexivity |].
destruct (Model.eq x DyadicExp.m_one) eqn:Q3; [reflexivity |].
cbv zeta.
rewrite (asin_atan1_fma (fabs x) Ft (acos_t_range x Fx Hx Q1 Q2 Q3)). reflexivity.
Qed.

(** ** The common part (as in [FastHyp.v], on a range [P]) *)

(** What [fast_asin_pos_correct] and [fast_acos_val_correct] prove of
    [pos] for [f] = [asin] and [acos], on the arguments in [P]. *)
Local Definition pos_bound (P : R -> Prop) (f : R -> R)
    (pos : f64 -> option (f64 * f64 * Z * f64)) : Prop :=
  forall t h l e err,
  is_finite t = true -> P (B2R t) -> pos t = Some (h, l, e, err) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= e <= 1022)%Z /\
  exists p, (55 <= p <= 105)%Z /\ B2R err = bpow radix2 (- p) /\
    Rabs (f (B2R t) * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (- p).

Local Lemma scale_back : forall y e, y = y * bpow radix2 (- e) * bpow radix2 e.
Proof.
intros y e. rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l.
change (bpow radix2 0) with 1. ring.
Qed.

(** For [t] in [P], the tests of [FastRoundErr.v] on the bound of [f(t)]. *)
Local Lemma pos_dir :
  forall (P : R -> Prop) f pos t up v,
  pos_bound P f pos -> is_finite t = true -> P (B2R t) ->
  match pos t with
  | Some (h, l, e, err) => Fast.round_dir_err h l e err up
  | None => None
  end = Some v ->
  rounds up (f (B2R t)) v.
Proof.
intros P f pos t up v HP Ft Ht H.
destruct (pos t) as [[[[h l] e] err]|] eqn:E; [|discriminate H].
destruct (HP t h l e err Ft Ht E) as (Fh & Fl & Eh & He & p & Hp & Herr & Hb).
rewrite (scale_back (f (B2R t)) e).
exact (round_dir_err_correct h l e err p up v _ Fh Fl Eh He Hp Herr Hb H).
Qed.

Local Lemma pos_near :
  forall (P : R -> Prop) f pos t v,
  pos_bound P f pos -> is_finite t = true -> P (B2R t) ->
  match pos t with
  | Some (h, l, e, err) => Fast.round_near_err h l e err
  | None => None
  end = Some v ->
  near_round (f (B2R t)) v.
Proof.
intros P f pos t v HP Ft Ht H.
destruct (pos t) as [[[[h l] e] err]|] eqn:E; [|discriminate H].
destruct (HP t h l e err Ft Ht E) as (Fh & Fl & Eh & He & p & Hp & Herr & Hb).
rewrite (scale_back (f (B2R t)) e).
exact (round_near_err_correct h l e err p v _ Fh Fl Eh He Hp Herr Hb H).
Qed.

(** An odd [f] at [x < 0] is [-f(|x|)]: rounding [f(|x|)] in the other
    direction and negating it rounds [f(x)] ([DyPown.rounds_odd]). [x =
    -0] is not below [0] and takes the branch of [x >= 0]. *)
Local Lemma odd_dir :
  forall (P : R -> Prop) f pos x up v,
  pos_bound P f pos -> (forall r, f (- r) = - f r) -> is_finite x = true ->
  P (Rabs (B2R x)) ->
  match pos (fabs x) with
  | Some (h, l, e, err) =>
    match Fast.round_dir_err h l e err (xorb up (lt x zero)) with
    | Some r => Some (if lt x zero then opp r else r)
    | None => None
    end
  | None => None
  end = Some v ->
  rounds up (f (B2R x)) v.
Proof.
intros P f pos x up v HP O Fx Hx H.
destruct (fabs_facts x Fx) as (Ft & Et & _).
assert (Ht : P (B2R (fabs x))) by (rewrite Et; exact Hx).
destruct (pos (fabs x)) as [[[[h l] e] err]|] eqn:E; [|discriminate H].
destruct (Fast.round_dir_err h l e err (xorb up (lt x zero))) as [r|] eqn:R; [|discriminate H].
injection H as <-.
assert (Hr : rounds (xorb up (lt x zero)) (f (B2R (fabs x))) r).
{ apply (pos_dir P f pos (fabs x) _ r HP Ft Ht). rewrite E. exact R. }
rewrite Et in Hr.
destruct (DyExp.lt_zero_spec x) as (N1 & N2).
destruct (lt x zero) eqn:L.
- rewrite Rabs_left1 in Hr by (apply N1; reflexivity).
  rewrite O, Bool.xorb_true_r in Hr.
  exact (DyPown.rounds_odd up (f (B2R x)) r Hr).
- rewrite Rabs_pos_eq in Hr by (apply N2; reflexivity).
  rewrite Bool.xorb_false_r in Hr. exact Hr.
Qed.

Local Lemma odd_near :
  forall (P : R -> Prop) f pos x v,
  pos_bound P f pos -> (forall r, f (- r) = - f r) -> is_finite x = true ->
  P (Rabs (B2R x)) ->
  match pos (fabs x) with
  | Some (h, l, e, err) =>
    match Fast.round_near_err h l e err with
    | Some r => Some (if lt x zero then opp r else r)
    | None => None
    end
  | None => None
  end = Some v ->
  near_round (f (B2R x)) v.
Proof.
intros P f pos x v HP O Fx Hx H.
destruct (fabs_facts x Fx) as (Ft & Et & _).
assert (Ht : P (B2R (fabs x))) by (rewrite Et; exact Hx).
destruct (pos (fabs x)) as [[[[h l] e] err]|] eqn:E; [|discriminate H].
destruct (Fast.round_near_err h l e err) as [r|] eqn:R; [|discriminate H].
injection H as <-.
assert (Hr : near_round (f (B2R (fabs x))) r).
{ apply (pos_near P f pos (fabs x) r HP Ft Ht). rewrite E. exact R. }
rewrite Et in Hr.
destruct (DyExp.lt_zero_spec x) as (N1 & N2).
destruct (lt x zero) eqn:L.
- rewrite Rabs_left1, O in Hr by (apply N1; reflexivity).
  rewrite <- (Ropp_involutive (f (B2R x))).
  exact (near_opp _ r Hr).
- rewrite Rabs_pos_eq in Hr by (apply N2; reflexivity). exact Hr.
Qed.

(** The range of [asin]'s positive part, and of [acos]. *)
Local Definition asin_P (r : R) : Prop := bpow radix2 (-27) <= r <= 1.
Local Definition acos_P (r : R) : Prop := Rabs r <= 1.

(** ** Rounded toward -inf and +inf *)

Theorem fast_asin_dir_correct :
  forall fma x up v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) <= 1 ->
  DyadicAtan.fast_asin_dir fma x up = Some v ->
  rounds up (asin (B2R x)) v.
Proof.
intros fma x up v Fx Hx H.
unfold DyadicAtan.fast_asin_dir in H.
destruct (DyadicAtan.fast_asin_dir1 fma x up) as [w|] eqn:E1; cbv beta iota in H.
- injection H as <-.
  exact (odd_dir asin_P asin _ x up w (fast_asin_pos1_correct fma) asin_opp Fx Hx E1).
- exact (odd_dir asin_P asin _ x up v (fast_asin_pos_correct fma) asin_opp Fx Hx H).
Qed.

Theorem fast_acos_dir_correct :
  forall fma x up v,
  is_finite x = true -> Rabs (B2R x) <= 1 ->
  DyadicAtan.fast_acos_dir fma x up = Some v ->
  rounds up (acos (B2R x)) v.
Proof.
intros fma x up v Fx Hx H.
unfold DyadicAtan.fast_acos_dir in H.
destruct (DyadicAtan.fast_acos_dir1 fma x up) as [w|] eqn:E1; cbv beta iota in H.
- injection H as <-.
  exact (pos_dir acos_P acos _ x up w (fast_acos_val1_correct fma) Fx Hx E1).
- exact (pos_dir acos_P acos _ x up v (fast_acos_val_correct fma) Fx Hx H).
Qed.

(** ** Rounded to nearest *)

Theorem fast_asin_near_correct :
  forall fma x v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) <= 1 ->
  DyadicAtan.fast_asin_near fma x = Some v ->
  near_round (asin (B2R x)) v.
Proof.
intros fma x v Fx Hx H.
unfold DyadicAtan.fast_asin_near in H.
destruct (DyadicAtan.fast_asin_near1 fma x) as [w|] eqn:E1; cbv beta iota in H.
- injection H as <-.
  exact (odd_near asin_P asin _ x w (fast_asin_pos1_correct fma) asin_opp Fx Hx E1).
- exact (odd_near asin_P asin _ x v (fast_asin_pos_correct fma) asin_opp Fx Hx H).
Qed.

Theorem fast_acos_near_correct :
  forall fma x v,
  is_finite x = true -> Rabs (B2R x) <= 1 ->
  DyadicAtan.fast_acos_near fma x = Some v ->
  near_round (acos (B2R x)) v.
Proof.
intros fma x v Fx Hx H.
unfold DyadicAtan.fast_acos_near in H.
destruct (DyadicAtan.fast_acos_near1 fma x) as [w|] eqn:E1; cbv beta iota in H.
- injection H as <-.
  exact (pos_near acos_P acos _ x w (fast_acos_val1_correct fma) Fx Hx E1).
- exact (pos_near acos_P acos _ x v (fast_acos_val_correct fma) Fx Hx H).
Qed.

(** ** With and without an FMA *)

Theorem fast_asin_dir_fma :
  forall x up,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) <= 1 ->
  DyadicAtan.fast_asin_dir true x up = DyadicAtan.fast_asin_dir false x up.
Proof.
intros x up Fx Hx. destruct (fabs_facts x Fx) as (Ft & Et & _).
rewrite <- Et in Hx.
unfold DyadicAtan.fast_asin_dir, DyadicAtan.fast_asin_dir1, DyadicAtan.fast_asin_dir2.
rewrite (fast_asin_pos1_fma _ Ft Hx), (fast_asin_pos_fma _ Ft Hx). reflexivity.
Qed.

Theorem fast_asin_near_fma :
  forall x,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) <= 1 ->
  DyadicAtan.fast_asin_near true x = DyadicAtan.fast_asin_near false x.
Proof.
intros x Fx Hx. destruct (fabs_facts x Fx) as (Ft & Et & _).
rewrite <- Et in Hx.
unfold DyadicAtan.fast_asin_near, DyadicAtan.fast_asin_near1, DyadicAtan.fast_asin_near2.
rewrite (fast_asin_pos1_fma _ Ft Hx), (fast_asin_pos_fma _ Ft Hx). reflexivity.
Qed.

Theorem fast_acos_dir_fma :
  forall x up,
  is_finite x = true -> Rabs (B2R x) <= 1 ->
  DyadicAtan.fast_acos_dir true x up = DyadicAtan.fast_acos_dir false x up.
Proof.
intros x up Fx Hx.
unfold DyadicAtan.fast_acos_dir, DyadicAtan.fast_acos_dir1, DyadicAtan.fast_acos_dir2.
rewrite (fast_acos_val1_fma x Fx Hx), (fast_acos_val_fma x Fx Hx). reflexivity.
Qed.

Theorem fast_acos_near_fma :
  forall x,
  is_finite x = true -> Rabs (B2R x) <= 1 ->
  DyadicAtan.fast_acos_near true x = DyadicAtan.fast_acos_near false x.
Proof.
intros x Fx Hx.
unfold DyadicAtan.fast_acos_near, DyadicAtan.fast_acos_near1, DyadicAtan.fast_acos_near2.
rewrite (fast_acos_val1_fma x Fx Hx), (fast_acos_val_fma x Fx Hx). reflexivity.
Qed.
