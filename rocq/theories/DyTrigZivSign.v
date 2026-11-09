(** * [Dyadic.ziv] keeps the sign of enclosures that exclude 0

    [Dyadic.ziv] returns a bound of an enclosure rounded, at a level where
    a rounding test passes or at its cap: the lower bound rounded down if
    it rounds down, and the upper bound, or a lower bound equal to it,
    rounded up if it rounds up. If every enclosure excludes 0, the sign of
    the result is that of the real number ([ziv_sign]). *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary DyRound DyConv DyOps DyDriver MpfrRound.

Open Scope Z_scope.

(** A real rounded down to an [f64] is below 0 exactly when the real is,
    and a real rounded up is above 0 exactly when the real is: 0 is an
    [f64]. The proofs are those of [st_dn_neg] and [st_up_pos] in
    [SideTight.v], which this file does not import. *)
Lemma rnd_dn_neg :
  forall r v, mpfr_round f64_format RNDD r (with_val v) ->
  (Model.lt v Model.zero = true <-> r < 0)%R.
Proof.
intros r v H.
assert (F0 : f64_format 0%R) by exact (f64_format_B2R (B754_zero false) eq_refl).
destruct v as [s|[|]| |s m e B]; cbn [with_val mpfr_round] in H; try contradiction.
- destruct H as (_ & H & _).
  change (Model.lt (B754_zero s) Model.zero) with false.
  split; [discriminate | intros; lra].
- split; [intros _; exact (H 0%R F0) | reflexivity].
- destruct H as (_ & _ & H1 & H2).
  unfold Model.lt. rewrite Bltb_correct by reflexivity.
  set (y := B2R (B754_finite s m e B)) in *. change (B2R Model.zero) with 0%R.
  destruct (Rlt_bool_spec y 0) as [L|L].
  + split; [intros _ | reflexivity].
    destruct (Rlt_or_le r 0) as [Hr|Hr]; [exact Hr|].
    specialize (H2 0%R F0 Hr). lra.
  + split; [discriminate | intros; lra].
Qed.

Lemma rnd_up_pos :
  forall r v, mpfr_round f64_format RNDU r (with_val v) ->
  (Model.lt Model.zero v = true <-> 0 < r)%R.
Proof.
intros r v H.
assert (F0 : f64_format 0%R) by exact (f64_format_B2R (B754_zero false) eq_refl).
destruct v as [s|[|]| |s m e B]; cbn [with_val mpfr_round] in H; try contradiction.
- destruct H as (_ & H & _).
  change (Model.lt Model.zero (B754_zero s)) with false.
  split; [discriminate | intros; lra].
- split; [intros _; exact (H 0%R F0) | reflexivity].
- destruct H as (_ & _ & H1 & H2).
  unfold Model.lt. rewrite Bltb_correct by reflexivity.
  set (y := B2R (B754_finite s m e B)) in *. change (B2R Model.zero) with 0%R.
  destruct (Rlt_bool_spec 0 y) as [L|L].
  + split; [intros _ | reflexivity].
    destruct (Rlt_or_le 0 r) as [Hr|Hr]; [exact Hr|].
    specialize (H2 0%R F0 Hr). lra.
  + split; [discriminate | intros; lra].
Qed.

(** [ziv] returns one of the two bounds of the enclosure at some level
    from 1 to 64 limbs, rounded up if [up] and down otherwise: [lo] where
    a test passes, and at the cap [lo] or [hi] (cases as in [ziv_side]). *)
Lemma ziv_bound :
  forall ev up start v,
  (forall n a, level_ok n -> ev n = Some a -> encl_ok n a) ->
  Dyadic.ziv ev up start = Some v ->
  exists n a d,
  level_ok n /\ ev n = Some a /\ (d = lo_R a \/ d = hi_R a) /\
  mpfr_round f64_format (if up then RNDU else RNDD) d (with_val v).
Proof.
intros ev up start v Hev Hz. unfold Dyadic.ziv in Hz.
destruct (Dyadic.ziv_levels ev up start _) as [[x|]|] eqn:L; cbv beta iota in Hz;
  [| |discriminate Hz].
- (* A level below the cap passes: [ziv_at] returns [lo]. *)
  injection Hz as <-.
  destruct (ziv_levels_some _ _ _ _ _ L) as (n & Hin & E).
  assert (Hn : level_ok n).
  { unfold level_ok. cbn [In] in Hin.
    repeat (destruct Hin as [<-|Hin]; [lia|]). destruct Hin. }
  unfold Dyadic.ziv_at, Dyadic.round_bounds in E.
  destruct (ev n) as [a|] eqn:Ea; [|discriminate]. cbv beta iota in E.
  destruct (Hev n a Hn Ea) as (Hlo & Hhi & _).
  destruct (to_f64_correct n (Dyadic.en_lo a) up Hn Hlo) as (v1 & E1 & R1).
  destruct (to_f64_correct n (Dyadic.en_hi a) up Hn Hhi) as (v2 & E2 & R2).
  rewrite E1, E2 in E. cbv beta iota in E.
  destruct (Model.eq v1 v2); [|discriminate]. injection E as <-.
  exists n, a, (lo_R a). split; [exact Hn|]. split; [exact Ea|].
  split; [left; reflexivity | exact R1].
- (* The cap: [lo] or [hi] of the enclosure at 64 limbs. *)
  assert (H64 : level_ok 64) by (unfold level_ok; lia).
  unfold Dyadic.ziv_cap, Dyadic.round_bounds in Hz.
  destruct (ev 64%nat) as [a|] eqn:Ea; [|discriminate]. cbv beta iota in Hz.
  destruct (Hev 64%nat a H64 Ea) as (Hlo & Hhi & _).
  destruct (to_f64_correct 64 (Dyadic.en_lo a) up H64 Hlo) as (v1 & E1 & R1).
  destruct (to_f64_correct 64 (Dyadic.en_hi a) up H64 Hhi) as (v2 & E2 & R2).
  rewrite E1, E2 in Hz. cbv beta iota in Hz. injection Hz as <-.
  exists 64%nat, a. destruct (Model.eq v1 v2 || negb up).
  + exists (lo_R a). split; [exact H64|]. split; [exact Ea|].
    split; [left; reflexivity | exact R1].
  + exists (hi_R a). split; [exact H64|]. split; [exact Ea|].
    split; [right; reflexivity | exact R2].
Qed.

(** If [up], a result above 0 is a bound [d] rounded up with [0 < d], so
    [0 < hi], which excludes [hi < 0]: then [0 < lo <= r]. Otherwise a
    result below 0 is a bound [d] rounded down with [d < 0], so [lo < 0],
    which excludes [0 < lo]: then [r <= hi < 0]. *)
Lemma ziv_sign :
  forall ev up start r v,
  (forall n a, level_ok n -> ev n = Some a ->
   encl_ok n a /\ encl_has a r /\ (0 < lo_R a \/ hi_R a < 0)%R) ->
  Dyadic.ziv ev up start = Some v ->
  if up then (Model.lt Model.zero v = true -> (0 < r)%R)
  else (Model.lt v Model.zero = true -> (r < 0)%R).
Proof.
intros ev up start r v Hev Hz.
destruct (ziv_bound ev up start v (fun n a Hn Ea => proj1 (Hev n a Hn Ea)) Hz)
  as (n & a & d & Hn & Ea & Hd & R).
destruct (Hev n a Hn Ea) as ((_ & _ & Hle) & (Hr1 & Hr2) & Hs).
unfold lo_R, hi_R in Hd, Hs. destruct up; intros Hv.
- pose proof (proj1 (rnd_up_pos _ _ R) Hv).
  destruct Hd as [-> | ->]; destruct Hs; lra.
- pose proof (proj1 (rnd_dn_neg _ _ R) Hv).
  destruct Hd as [-> | ->]; destruct Hs; lra.
Qed.
