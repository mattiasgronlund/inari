(** * The fast paths of [asinh], [acosh] and [atanh]

    Each of [DyadicLog.fast_asinh_dir] and the others of [Model.v] has two
    branches:
    - near 0 ([|x| < 2^-8]) for [asinh] and [atanh], and near 1 ([x < 1 +
      2^-8]) for [acosh]: [DyadicLog.odd_series] of [|x|] and
      [DyadicLog.fast_acosh_near1] of [x] return [h + l] within [2^-67] of
      the result scaled by [2^-k] ([asinh_odd_correct] and
      [atanh_odd_correct] of [FastAhypOdd.v], [acosh_near1_correct] of
      [FastAhypNear1.v]), and the tests [Fast.round_dir_err] and
      [Fast.round_near_err] of [FastRoundErr.v] round it with [err =
      2^-67]. [asinh] and [atanh] are odd: for [x < 0] the wrappers round
      [f(|x|)] in the other direction and negate it, as [FastHyp.v] does
      for [sinh] and [tanh]. [fast_acosh_near1] returns [None] at [x = 1],
      where [acosh x = 0] ([fast_acosh_one]).
    - above: [fast_asinh_pos_correct] ([FastAhypAsinh.v]),
      [fast_acosh_correct] ([FastAhypAcosh.v]) and [fast_atanh_pos_correct]
      ([FastAhypAtanh.v]) show that [DyadicLog.fast_asinh_pos],
      [DyadicLog.fast_acosh] and [DyadicLog.fast_atanh_pos] return [h + l]
      within [2^-68] of the result scaled by [2^-k], with [1/2 < |h| < 2].
      [DyadicLog.fast_asinh] and [DyadicLog.fast_atanh] negate [h] and [l]
      for [x < 0] ([fast_asinh_correct], [fast_atanh_correct]), and
      [Fast.round_dir_signed] and [Fast.round_near_signed] of [FastSign.v]
      apply.
    The theorems [fast_asinh_dir_correct] and the others prove the fast
    paths of the three functions in all three roundings, and
    [fast_asinh_dir_fma] and the others that an FMA gives the same
    results. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Elementary Encoding TwoSum TwoProduct DyDriver NearF64
  FastRound FastSign FastLogNorm FastLogDd FastAhypAsinh FastAhypAcosh FastAhypAtanh
  FastAhypOdd FastAhypNear1.
From Inari Require DyLogRules DyExp DyPown NearCells FastRoundErr FastHypPos.

Open Scope R_scope.

(** ** The signed results *)

(** [fabs x] is finite for a finite [x], and its value is [|x|]. *)
Local Lemma fabs_finite : forall x, is_finite x = true -> is_finite (fabs x) = true.
Proof.
intros x F. unfold fabs. rewrite is_finite_Babs. exact F.
Qed.

Local Lemma fabs_R : forall x, B2R (fabs x) = Rabs (B2R x).
Proof.
intros x. apply B2R_Babs.
Qed.

(** If [h + l] is within [2^-68] of [y 2^-k], with [h] the rounding of
    [h + l] to nearest and [1/2 < |h| < 2], then [-h + -l] is within
    [2^-68] of [-y 2^-k], and [-h] is the rounding of [-h + -l] to
    nearest, as rounding to nearest is odd. *)
Local Lemma opp_out :
  forall y h l k,
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < Rabs (B2R h) < 2 /\ (-1021 <= k <= 1022)%Z /\
  Rabs (y * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  is_finite (opp h) = true /\ is_finite (opp l) = true /\
  B2R (opp h) = RN (B2R (opp h) + B2R (opp l)) /\
  / 2 < Rabs (B2R (opp h)) < 2 /\ (-1021 <= k <= 1022)%Z /\
  Rabs (- y * bpow radix2 (- k) - (B2R (opp h) + B2R (opp l))) <= bpow radix2 (-68).
Proof.
intros y h l k (Fh & Fl & Hrn & Hh & Hk & Hy). unfold opp.
rewrite !is_finite_Bopp, !B2R_Bopp, Rabs_Ropp.
split; [exact Fh |]. split; [exact Fl |].
split; [rewrite <- Ropp_plus_distr, round_NE_opp, <- Hrn; reflexivity |].
split; [exact Hh |]. split; [exact Hk |].
replace (- y * bpow radix2 (- k) - (- B2R h + - B2R l))
  with (- (y * bpow radix2 (- k) - (B2R h + B2R l))) by ring.
rewrite Rabs_Ropp. exact Hy.
Qed.

Theorem fast_asinh_correct :
  forall fma x h l k,
  is_finite x = true -> bpow radix2 (-8) <= Rabs (B2R x) ->
  DyadicLog.fast_asinh fma x = Some (h, l, k) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < Rabs (B2R h) < 2 /\ (-1021 <= k <= 1022)%Z /\
  Rabs (arcsinh (B2R x) * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-68).
Proof.
intros fma x h l k Fx Hx E. unfold DyadicLog.fast_asinh in E.
destruct (DyadicLog.fast_asinh_pos fma (fabs x)) as [[[h0 l0] k0]|] eqn:E0; [| discriminate E].
assert (Ht : bpow radix2 (-8) <= B2R (fabs x)) by (rewrite fabs_R; exact Hx).
pose proof (fast_asinh_pos_correct fma (fabs x) h0 l0 k0 (fabs_finite x Fx) Ht E0) as O.
rewrite fabs_R in O.
pose proof (lt_zero_R x Fx) as Hs.
destruct (lt x zero); cbv iota in E; injection E as <- <- <-.
- (* [x < 0]: [asinh x = - asinh |x|]. *)
  rewrite (Rabs_left _ Hs) in O. apply opp_out in O.
  rewrite DyLogRules.arcsinh_odd, Ropp_involutive in O. exact O.
- rewrite (Rabs_pos_eq _ Hs) in O. exact O.
Qed.

Theorem fast_atanh_correct :
  forall fma x h l k,
  is_finite x = true -> bpow radix2 (-8) <= Rabs (B2R x) < 1 ->
  DyadicLog.fast_atanh fma x = Some (h, l, k) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < Rabs (B2R h) < 2 /\ (-1021 <= k <= 1022)%Z /\
  Rabs (Ratanh (B2R x) * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-68).
Proof.
intros fma x h l k Fx Hx E. unfold DyadicLog.fast_atanh in E.
destruct (DyadicLog.fast_atanh_pos fma (fabs x)) as [[[h0 l0] k0]|] eqn:E0; [| discriminate E].
assert (Ht : bpow radix2 (-8) <= B2R (fabs x) < 1) by (rewrite fabs_R; exact Hx).
pose proof (fast_atanh_pos_correct fma (fabs x) h0 l0 k0 (fabs_finite x Fx) Ht E0) as O.
rewrite fabs_R in O.
pose proof (lt_zero_R x Fx) as Hs.
destruct (lt x zero); cbv iota in E; injection E as <- <- <-.
- (* [x < 0]: [atanh x = - atanh |x|], where [-1 < x < 0]. *)
  rewrite (Rabs_left _ Hs) in O, Hx. apply opp_out in O.
  rewrite DyLogRules.Ratanh_odd, Ropp_involutive in O by (split; lra). exact O.
- rewrite (Rabs_pos_eq _ Hs) in O. exact O.
Qed.

(** ** The branch tests *)

(** [B2R l] of an [f64] literal [l], as [m * 2^e] (as in [FastHypPos.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** The literals [2^-8] and [1 + 2^-8] of the tests. *)
Local Lemma ahyp_near_R :
  is_finite DyadicLog.ahyp_near = true /\ B2R DyadicLog.ahyp_near = bpow radix2 (-8).
Proof.
split; [reflexivity |]. lit_B2R.
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

Local Lemma acosh_near1_R :
  is_finite DyadicLog.acosh_near1 = true /\ B2R DyadicLog.acosh_near1 = 1 + bpow radix2 (-8).
Proof.
split; [reflexivity |]. lit_B2R. cbn [bpow radix_val radix2]. lra.
Qed.

(** The test [|x| < 2^-8] of [asinh] and [atanh], and the test [x < 1 +
    2^-8] of [acosh]. *)
Local Lemma ahyp_near_test :
  forall x, is_finite x = true ->
  if lt (fabs x) DyadicLog.ahyp_near then Rabs (B2R x) < bpow radix2 (-8)
  else bpow radix2 (-8) <= Rabs (B2R x).
Proof.
intros x Fx. destruct ahyp_near_R as (FN & EN).
destruct (lt (fabs x) DyadicLog.ahyp_near) eqn:L.
- pose proof (FastHypPos.lt_true _ _ (fabs_finite x Fx) FN L) as T.
  rewrite fabs_R, EN in T. exact T.
- pose proof (FastHypPos.lt_false _ _ (fabs_finite x Fx) FN L) as T.
  rewrite fabs_R, EN in T. exact T.
Qed.

Local Lemma acosh_near1_test :
  forall x, is_finite x = true ->
  if lt x DyadicLog.acosh_near1 then B2R x < 1 + bpow radix2 (-8)
  else 1 + bpow radix2 (-8) <= B2R x.
Proof.
intros x Fx. destruct acosh_near1_R as (FN & EN).
destruct (lt x DyadicLog.acosh_near1) eqn:L.
- pose proof (FastHypPos.lt_true _ _ Fx FN L) as T. rewrite EN in T. exact T.
- pose proof (FastHypPos.lt_false _ _ Fx FN L) as T. rewrite EN in T. exact T.
Qed.

(** ** The branches near 0 of [asinh] and [atanh] *)

(** [r 2^-k 2^k = r] (as in [FastLog.v]). *)
Local Lemma unscale : forall r k, r * bpow radix2 (- k) * bpow radix2 k = r.
Proof.
intros r k. rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l. cbn [bpow]. ring.
Qed.

(** What [FastAhypOdd.v] proves of [DyadicLog.odd_series] with the
    coefficients [c] of [f] = [asinh] and [atanh]. *)
Local Definition odd_bound (f : R -> R) (c : Z * Z * Z * Z) : Prop :=
  forall t h l k,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < bpow radix2 (-8) ->
  DyadicLog.odd_series t c = (h, l, k) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= k <= 1022)%Z /\
  Rabs (f (B2R t) * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-67).

(** [|x| < 2^-8] lies in [(-1, 1)], where [atanh] is odd. *)
Local Lemma near_unit : forall r, Rabs r < bpow radix2 (-8) -> -1 < r < 1.
Proof.
intros r Hr. pose proof (bpow_lt radix2 (-8) 0 ltac:(lia)) as B.
change (bpow radix2 0) with 1 in B.
destruct (Rabs_def2 r (bpow radix2 (-8)) Hr). lra.
Qed.

(** For [2^-27 <= |x| < 2^-8], the test [Fast.round_dir_err] at [err =
    2^-67] rounds [f(|x|)]. An odd [f] at [x < 0] is [-f(|x|)]: rounding
    [f(|x|)] in the other direction and negating it rounds [f(x)]
    ([DyPown.rounds_odd]), as [odd_dir] of [FastHyp.v] does. *)
Local Lemma odd_dir :
  forall f c x up v,
  odd_bound f c -> (forall r, -1 < r < 1 -> f (- r) = - f r) -> is_finite x = true ->
  bpow radix2 (-27) <= Rabs (B2R x) < bpow radix2 (-8) ->
  (let '(h, l, k) := DyadicLog.odd_series (fabs x) c in
   match Fast.round_dir_err h l k DyadicExp.err67 (xorb up (lt x zero)) with
   | Some r => Some (if lt x zero then opp r else r)
   | None => None
   end) = Some v ->
  rounds up (f (B2R x)) v.
Proof.
intros f c x up v P O Fx Hx H.
destruct (DyadicLog.odd_series (fabs x) c) as [[h l] k] eqn:E.
destruct (Fast.round_dir_err h l k DyadicExp.err67 (xorb up (lt x zero))) as [r|] eqn:R;
  [| discriminate H].
injection H as <-.
assert (Ht : bpow radix2 (-27) <= B2R (fabs x) < bpow radix2 (-8)) by (rewrite fabs_R; exact Hx).
destruct (P (fabs x) h l k (fabs_finite x Fx) Ht E) as (Fh & Fl & Eh & Hk & Hb).
pose proof (FastRoundErr.round_dir_err_correct h l k DyadicExp.err67 67 _ r _ Fh Fl Eh Hk
  ltac:(lia) FastHypPos.lit_err67 Hb R) as Hr.
rewrite unscale, fabs_R in Hr.
pose proof (near_unit (B2R x) (proj2 Hx)) as U.
destruct (DyExp.lt_zero_spec x) as (N1 & N2).
destruct (lt x zero).
- rewrite Rabs_left1 in Hr by (apply N1; reflexivity).
  rewrite (O (B2R x) U), Bool.xorb_true_r in Hr.
  exact (DyPown.rounds_odd up (f (B2R x)) r Hr).
- rewrite Rabs_pos_eq in Hr by (apply N2; reflexivity).
  rewrite Bool.xorb_false_r in Hr. exact Hr.
Qed.

(** The same with [Fast.round_near_err] and rounding to nearest, which is
    odd ([NearCells.near_opp]). *)
Local Lemma odd_near :
  forall f c x v,
  odd_bound f c -> (forall r, -1 < r < 1 -> f (- r) = - f r) -> is_finite x = true ->
  bpow radix2 (-27) <= Rabs (B2R x) < bpow radix2 (-8) ->
  (let '(h, l, k) := DyadicLog.odd_series (fabs x) c in
   match Fast.round_near_err h l k DyadicExp.err67 with
   | Some r => Some (if lt x zero then opp r else r)
   | None => None
   end) = Some v ->
  near_round (f (B2R x)) v.
Proof.
intros f c x v P O Fx Hx H.
destruct (DyadicLog.odd_series (fabs x) c) as [[h l] k] eqn:E.
destruct (Fast.round_near_err h l k DyadicExp.err67) as [r|] eqn:R; [| discriminate H].
injection H as <-.
assert (Ht : bpow radix2 (-27) <= B2R (fabs x) < bpow radix2 (-8)) by (rewrite fabs_R; exact Hx).
destruct (P (fabs x) h l k (fabs_finite x Fx) Ht E) as (Fh & Fl & Eh & Hk & Hb).
pose proof (FastRoundErr.round_near_err_correct h l k DyadicExp.err67 67 r _ Fh Fl Eh Hk
  ltac:(lia) FastHypPos.lit_err67 Hb R) as Hr.
rewrite unscale, fabs_R in Hr.
pose proof (near_unit (B2R x) (proj2 Hx)) as U.
destruct (DyExp.lt_zero_spec x) as (N1 & N2).
destruct (lt x zero).
- rewrite Rabs_left1 in Hr by (apply N1; reflexivity).
  rewrite (O (B2R x) U) in Hr.
  rewrite <- (Ropp_involutive (f (B2R x))).
  exact (NearCells.near_opp _ r Hr).
- rewrite Rabs_pos_eq in Hr by (apply N2; reflexivity). exact Hr.
Qed.

Local Lemma asinh_odd : odd_bound arcsinh DyadicLog.ASINH_ODD.
Proof. exact FastAhypOdd.asinh_odd_correct. Qed.

Local Lemma atanh_odd : odd_bound Ratanh DyadicLog.ATANH_ODD.
Proof. exact FastAhypOdd.atanh_odd_correct. Qed.

Local Lemma arcsinh_odd' : forall r, -1 < r < 1 -> arcsinh (- r) = - arcsinh r.
Proof. intros r _. apply DyLogRules.arcsinh_odd. Qed.

(** ** The three roundings *)

Theorem fast_asinh_dir_correct :
  forall fma x up v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) -> DyadicLog.fast_asinh_dir fma x up = Some v ->
  rounds up (arcsinh (B2R x)) v.
Proof.
intros fma x up v Fx Hx H. unfold DyadicLog.fast_asinh_dir in H. cbv zeta in H.
pose proof (ahyp_near_test x Fx) as T.
destruct (lt (fabs x) DyadicLog.ahyp_near).
- exact (odd_dir arcsinh DyadicLog.ASINH_ODD x up v asinh_odd arcsinh_odd' Fx (conj Hx T) H).
- destruct (DyadicLog.fast_asinh fma x) as [[[h l] k]|] eqn:E; [| discriminate H].
  destruct (fast_asinh_correct fma x h l k Fx T E) as (Fh & Fl & Hrn & Hh & Hk & Hy).
  pose proof (round_dir_signed_correct h l k up v _ Fh Fl Hrn Hh Hk Hy H) as R.
  rewrite unscale in R. exact R.
Qed.

Theorem fast_asinh_near_correct :
  forall fma x v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) -> DyadicLog.fast_asinh_near fma x = Some v ->
  near_round (arcsinh (B2R x)) v.
Proof.
intros fma x v Fx Hx H. unfold DyadicLog.fast_asinh_near in H. cbv zeta in H.
pose proof (ahyp_near_test x Fx) as T.
destruct (lt (fabs x) DyadicLog.ahyp_near).
- exact (odd_near arcsinh DyadicLog.ASINH_ODD x v asinh_odd arcsinh_odd' Fx (conj Hx T) H).
- destruct (DyadicLog.fast_asinh fma x) as [[[h l] k]|] eqn:E; [| discriminate H].
  destruct (fast_asinh_correct fma x h l k Fx T E) as (Fh & Fl & Hrn & Hh & Hk & Hy).
  pose proof (round_near_signed_correct h l k v _ Fh Fl Hrn Hh Hk Hy H) as R.
  rewrite unscale in R. exact R.
Qed.

Theorem fast_acosh_dir_correct :
  forall fma x up v,
  is_finite x = true -> 1 <= B2R x -> DyadicLog.fast_acosh_dir fma x up = Some v ->
  rounds up (Racosh (B2R x)) v.
Proof.
intros fma x up v Fx Hx H. unfold DyadicLog.fast_acosh_dir in H.
pose proof (acosh_near1_test x Fx) as T.
destruct (lt x DyadicLog.acosh_near1).
- destruct (DyadicLog.fast_acosh_near1 fma x) as [[[h l] k]|] eqn:E; [| discriminate H].
  destruct (FastAhypNear1.acosh_near1_correct fma x h l k Fx (conj Hx T) E)
    as (Fh & Fl & Eh & Hk & Hb).
  pose proof (FastRoundErr.round_dir_err_correct h l k DyadicExp.err67 67 up v _ Fh Fl Eh Hk
    ltac:(lia) FastHypPos.lit_err67 Hb H) as R.
  rewrite unscale in R. exact R.
- destruct (DyadicLog.fast_acosh fma x) as [[[h l] k]|] eqn:E; [| discriminate H].
  destruct (fast_acosh_correct fma x h l k Fx T E) as (Fh & Fl & Hrn & Hh & Hk & Hy).
  pose proof (round_dir_signed_correct h l k up v _ Fh Fl Hrn Hh Hk Hy H) as R.
  rewrite unscale in R. exact R.
Qed.

Theorem fast_acosh_near_correct :
  forall fma x v,
  is_finite x = true -> 1 <= B2R x -> DyadicLog.fast_acosh_near fma x = Some v ->
  near_round (Racosh (B2R x)) v.
Proof.
intros fma x v Fx Hx H. unfold DyadicLog.fast_acosh_near in H.
pose proof (acosh_near1_test x Fx) as T.
destruct (lt x DyadicLog.acosh_near1).
- destruct (DyadicLog.fast_acosh_near1 fma x) as [[[h l] k]|] eqn:E; [| discriminate H].
  destruct (FastAhypNear1.acosh_near1_correct fma x h l k Fx (conj Hx T) E)
    as (Fh & Fl & Eh & Hk & Hb).
  pose proof (FastRoundErr.round_near_err_correct h l k DyadicExp.err67 67 v _ Fh Fl Eh Hk
    ltac:(lia) FastHypPos.lit_err67 Hb H) as R.
  rewrite unscale in R. exact R.
- destruct (DyadicLog.fast_acosh fma x) as [[[h l] k]|] eqn:E; [| discriminate H].
  destruct (fast_acosh_correct fma x h l k Fx T E) as (Fh & Fl & Hrn & Hh & Hk & Hy).
  pose proof (round_near_signed_correct h l k v _ Fh Fl Hrn Hh Hk Hy H) as R.
  rewrite unscale in R. exact R.
Qed.

Theorem fast_atanh_dir_correct :
  forall fma x up v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) < 1 -> DyadicLog.fast_atanh_dir fma x up = Some v ->
  rounds up (Ratanh (B2R x)) v.
Proof.
intros fma x up v Fx Hx H. unfold DyadicLog.fast_atanh_dir in H. cbv zeta in H.
pose proof (ahyp_near_test x Fx) as T.
destruct (lt (fabs x) DyadicLog.ahyp_near).
- exact (odd_dir Ratanh DyadicLog.ATANH_ODD x up v atanh_odd DyLogRules.Ratanh_odd Fx
    (conj (proj1 Hx) T) H).
- destruct (DyadicLog.fast_atanh fma x) as [[[h l] k]|] eqn:E; [| discriminate H].
  destruct (fast_atanh_correct fma x h l k Fx (conj T (proj2 Hx)) E)
    as (Fh & Fl & Hrn & Hh & Hk & Hy).
  pose proof (round_dir_signed_correct h l k up v _ Fh Fl Hrn Hh Hk Hy H) as R.
  rewrite unscale in R. exact R.
Qed.

Theorem fast_atanh_near_correct :
  forall fma x v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) < 1 -> DyadicLog.fast_atanh_near fma x = Some v ->
  near_round (Ratanh (B2R x)) v.
Proof.
intros fma x v Fx Hx H. unfold DyadicLog.fast_atanh_near in H. cbv zeta in H.
pose proof (ahyp_near_test x Fx) as T.
destruct (lt (fabs x) DyadicLog.ahyp_near).
- exact (odd_near Ratanh DyadicLog.ATANH_ODD x v atanh_odd DyLogRules.Ratanh_odd Fx
    (conj (proj1 Hx) T) H).
- destruct (DyadicLog.fast_atanh fma x) as [[[h l] k]|] eqn:E; [| discriminate H].
  destruct (fast_atanh_correct fma x h l k Fx (conj T (proj2 Hx)) E)
    as (Fh & Fl & Hrn & Hh & Hk & Hy).
  pose proof (round_near_signed_correct h l k v _ Fh Fl Hrn Hh Hk Hy H) as R.
  rewrite unscale in R. exact R.
Qed.

(** ** With an FMA, and at 1 *)

(** [DyadicLog.odd_series] takes no FMA, so the branches near 0 of [asinh]
    and [atanh] are the same with and without one. *)
Theorem fast_asinh_dir_fma :
  forall x up, is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicLog.fast_asinh_dir true x up = DyadicLog.fast_asinh_dir false x up.
Proof.
intros x up Fx Hx. unfold DyadicLog.fast_asinh_dir. cbv zeta.
pose proof (ahyp_near_test x Fx) as T.
destruct (lt (fabs x) DyadicLog.ahyp_near); [reflexivity |].
unfold DyadicLog.fast_asinh.
rewrite (fast_asinh_pos_fma (fabs x) (fabs_finite x Fx)) by (rewrite fabs_R; exact T).
reflexivity.
Qed.

Theorem fast_asinh_near_fma :
  forall x, is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicLog.fast_asinh_near true x = DyadicLog.fast_asinh_near false x.
Proof.
intros x Fx Hx. unfold DyadicLog.fast_asinh_near. cbv zeta.
pose proof (ahyp_near_test x Fx) as T.
destruct (lt (fabs x) DyadicLog.ahyp_near); [reflexivity |].
unfold DyadicLog.fast_asinh.
rewrite (fast_asinh_pos_fma (fabs x) (fabs_finite x Fx)) by (rewrite fabs_R; exact T).
reflexivity.
Qed.

Theorem fast_acosh_dir_fma :
  forall x up, is_finite x = true -> 1 <= B2R x ->
  DyadicLog.fast_acosh_dir true x up = DyadicLog.fast_acosh_dir false x up.
Proof.
intros x up Fx Hx. unfold DyadicLog.fast_acosh_dir.
pose proof (acosh_near1_test x Fx) as T.
destruct (lt x DyadicLog.acosh_near1).
- rewrite (FastAhypNear1.acosh_near1_fma x Fx (conj Hx T)). reflexivity.
- rewrite (fast_acosh_fma x Fx T). reflexivity.
Qed.

Theorem fast_acosh_near_fma :
  forall x, is_finite x = true -> 1 <= B2R x ->
  DyadicLog.fast_acosh_near true x = DyadicLog.fast_acosh_near false x.
Proof.
intros x Fx Hx. unfold DyadicLog.fast_acosh_near.
pose proof (acosh_near1_test x Fx) as T.
destruct (lt x DyadicLog.acosh_near1).
- rewrite (FastAhypNear1.acosh_near1_fma x Fx (conj Hx T)). reflexivity.
- rewrite (fast_acosh_fma x Fx T). reflexivity.
Qed.

Theorem fast_atanh_dir_fma :
  forall x up, is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) < 1 ->
  DyadicLog.fast_atanh_dir true x up = DyadicLog.fast_atanh_dir false x up.
Proof.
intros x up Fx Hx. unfold DyadicLog.fast_atanh_dir. cbv zeta.
pose proof (ahyp_near_test x Fx) as T.
destruct (lt (fabs x) DyadicLog.ahyp_near); [reflexivity |].
unfold DyadicLog.fast_atanh.
rewrite (fast_atanh_pos_fma (fabs x) (fabs_finite x Fx))
  by (rewrite fabs_R; exact (conj T (proj2 Hx))).
reflexivity.
Qed.

Theorem fast_atanh_near_fma :
  forall x, is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) < 1 ->
  DyadicLog.fast_atanh_near true x = DyadicLog.fast_atanh_near false x.
Proof.
intros x Fx Hx. unfold DyadicLog.fast_atanh_near. cbv zeta.
pose proof (ahyp_near_test x Fx) as T.
destruct (lt (fabs x) DyadicLog.ahyp_near); [reflexivity |].
unfold DyadicLog.fast_atanh.
rewrite (fast_atanh_pos_fma (fabs x) (fabs_finite x Fx))
  by (rewrite fabs_R; exact (conj T (proj2 Hx))).
reflexivity.
Qed.

(** At [x = 1], [acosh x = 0], and the directed fast paths return [None],
    so that the kernel's exact enclosure settles it. *)
Theorem fast_acosh_one :
  forall fma up, DyadicLog.fast_acosh_dir fma DyadicExp.one up = None.
Proof.
intros [|] [|]; vm_compute; reflexivity.
Qed.
