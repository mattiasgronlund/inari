(** * The fast paths of [asinh], [acosh] and [atanh]

    [fast_asinh_pos_correct] ([FastAhypAsinh.v]), [fast_acosh_correct]
    ([FastAhypAcosh.v]) and [fast_atanh_pos_correct] ([FastAhypAtanh.v])
    show that [DyadicLog.fast_asinh_pos], [DyadicLog.fast_acosh] and
    [DyadicLog.fast_atanh_pos] of [Model.v] return [h + l] within [2^-68]
    of the result scaled by [2^-k], with [1/2 < |h| < 2]. [asinh] and
    [atanh] are odd, so [DyadicLog.fast_asinh] and [DyadicLog.fast_atanh]
    negate [h] and [l] for [x < 0] ([fast_asinh_correct],
    [fast_atanh_correct]), and [Fast.round_dir_signed] and
    [Fast.round_near_signed] of [FastSign.v] apply. [fast_acosh] returns
    [None] at [x = 1], where [acosh x = 0] ([fast_acosh_one]). The theorems
    [fast_asinh_dir_correct] and the others prove the fast paths of the
    three functions in all three roundings, and [fast_asinh_dir_fma] and
    the others that an FMA gives the same results. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Elementary Encoding TwoSum TwoProduct DyDriver NearF64
  FastRound FastSign FastLogNorm FastLogDd FastAhypAsinh FastAhypAcosh FastAhypAtanh.
From Inari Require DyLogRules.

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
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicLog.fast_asinh fma x = Some (h, l, k) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < Rabs (B2R h) < 2 /\ (-1021 <= k <= 1022)%Z /\
  Rabs (arcsinh (B2R x) * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-68).
Proof.
intros fma x h l k Fx Hx E. unfold DyadicLog.fast_asinh in E.
destruct (DyadicLog.fast_asinh_pos fma (fabs x)) as [[[h0 l0] k0]|] eqn:E0; [| discriminate E].
assert (Ht : bpow radix2 (-27) <= B2R (fabs x)) by (rewrite fabs_R; exact Hx).
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
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) < 1 ->
  DyadicLog.fast_atanh fma x = Some (h, l, k) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < Rabs (B2R h) < 2 /\ (-1021 <= k <= 1022)%Z /\
  Rabs (Ratanh (B2R x) * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-68).
Proof.
intros fma x h l k Fx Hx E. unfold DyadicLog.fast_atanh in E.
destruct (DyadicLog.fast_atanh_pos fma (fabs x)) as [[[h0 l0] k0]|] eqn:E0; [| discriminate E].
assert (Ht : bpow radix2 (-27) <= B2R (fabs x) < 1) by (rewrite fabs_R; exact Hx).
pose proof (fast_atanh_pos_correct fma (fabs x) h0 l0 k0 (fabs_finite x Fx) Ht E0) as O.
rewrite fabs_R in O.
pose proof (lt_zero_R x Fx) as Hs.
destruct (lt x zero); cbv iota in E; injection E as <- <- <-.
- (* [x < 0]: [atanh x = - atanh |x|], where [-1 < x < 0]. *)
  rewrite (Rabs_left _ Hs) in O, Hx. apply opp_out in O.
  rewrite DyLogRules.Ratanh_odd, Ropp_involutive in O by (split; lra). exact O.
- rewrite (Rabs_pos_eq _ Hs) in O. exact O.
Qed.

(** ** The three roundings *)

(** [r 2^-k 2^k = r] (as in [FastLog.v]). *)
Local Lemma unscale : forall r k, r * bpow radix2 (- k) * bpow radix2 k = r.
Proof.
intros r k. rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l. cbn [bpow]. ring.
Qed.

Theorem fast_asinh_dir_correct :
  forall fma x up v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) -> DyadicLog.fast_asinh_dir fma x up = Some v ->
  rounds up (arcsinh (B2R x)) v.
Proof.
intros fma x up v Fx Hx H. unfold DyadicLog.fast_asinh_dir in H.
destruct (DyadicLog.fast_asinh fma x) as [[[h l] k]|] eqn:E; [| discriminate H].
destruct (fast_asinh_correct fma x h l k Fx Hx E) as (Fh & Fl & Hrn & Hh & Hk & Hy).
pose proof (round_dir_signed_correct h l k up v _ Fh Fl Hrn Hh Hk Hy H) as R.
rewrite unscale in R. exact R.
Qed.

Theorem fast_asinh_near_correct :
  forall fma x v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) -> DyadicLog.fast_asinh_near fma x = Some v ->
  near_round (arcsinh (B2R x)) v.
Proof.
intros fma x v Fx Hx H. unfold DyadicLog.fast_asinh_near in H.
destruct (DyadicLog.fast_asinh fma x) as [[[h l] k]|] eqn:E; [| discriminate H].
destruct (fast_asinh_correct fma x h l k Fx Hx E) as (Fh & Fl & Hrn & Hh & Hk & Hy).
pose proof (round_near_signed_correct h l k v _ Fh Fl Hrn Hh Hk Hy H) as R.
rewrite unscale in R. exact R.
Qed.

Theorem fast_acosh_dir_correct :
  forall fma x up v,
  is_finite x = true -> 1 <= B2R x -> DyadicLog.fast_acosh_dir fma x up = Some v ->
  rounds up (Racosh (B2R x)) v.
Proof.
intros fma x up v Fx Hx H. unfold DyadicLog.fast_acosh_dir in H.
destruct (DyadicLog.fast_acosh fma x) as [[[h l] k]|] eqn:E; [| discriminate H].
destruct (fast_acosh_correct fma x h l k Fx Hx E) as (Fh & Fl & Hrn & Hh & Hk & Hy).
pose proof (round_dir_signed_correct h l k up v _ Fh Fl Hrn Hh Hk Hy H) as R.
rewrite unscale in R. exact R.
Qed.

Theorem fast_acosh_near_correct :
  forall fma x v,
  is_finite x = true -> 1 <= B2R x -> DyadicLog.fast_acosh_near fma x = Some v ->
  near_round (Racosh (B2R x)) v.
Proof.
intros fma x v Fx Hx H. unfold DyadicLog.fast_acosh_near in H.
destruct (DyadicLog.fast_acosh fma x) as [[[h l] k]|] eqn:E; [| discriminate H].
destruct (fast_acosh_correct fma x h l k Fx Hx E) as (Fh & Fl & Hrn & Hh & Hk & Hy).
pose proof (round_near_signed_correct h l k v _ Fh Fl Hrn Hh Hk Hy H) as R.
rewrite unscale in R. exact R.
Qed.

Theorem fast_atanh_dir_correct :
  forall fma x up v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) < 1 -> DyadicLog.fast_atanh_dir fma x up = Some v ->
  rounds up (Ratanh (B2R x)) v.
Proof.
intros fma x up v Fx Hx H. unfold DyadicLog.fast_atanh_dir in H.
destruct (DyadicLog.fast_atanh fma x) as [[[h l] k]|] eqn:E; [| discriminate H].
destruct (fast_atanh_correct fma x h l k Fx Hx E) as (Fh & Fl & Hrn & Hh & Hk & Hy).
pose proof (round_dir_signed_correct h l k up v _ Fh Fl Hrn Hh Hk Hy H) as R.
rewrite unscale in R. exact R.
Qed.

Theorem fast_atanh_near_correct :
  forall fma x v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) < 1 -> DyadicLog.fast_atanh_near fma x = Some v ->
  near_round (Ratanh (B2R x)) v.
Proof.
intros fma x v Fx Hx H. unfold DyadicLog.fast_atanh_near in H.
destruct (DyadicLog.fast_atanh fma x) as [[[h l] k]|] eqn:E; [| discriminate H].
destruct (fast_atanh_correct fma x h l k Fx Hx E) as (Fh & Fl & Hrn & Hh & Hk & Hy).
pose proof (round_near_signed_correct h l k v _ Fh Fl Hrn Hh Hk Hy H) as R.
rewrite unscale in R. exact R.
Qed.

(** ** With an FMA, and at 1 *)

Theorem fast_asinh_dir_fma :
  forall x up, is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicLog.fast_asinh_dir true x up = DyadicLog.fast_asinh_dir false x up.
Proof.
intros x up Fx Hx. unfold DyadicLog.fast_asinh_dir, DyadicLog.fast_asinh.
rewrite (fast_asinh_pos_fma (fabs x) (fabs_finite x Fx)) by (rewrite fabs_R; exact Hx).
reflexivity.
Qed.

Theorem fast_asinh_near_fma :
  forall x, is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicLog.fast_asinh_near true x = DyadicLog.fast_asinh_near false x.
Proof.
intros x Fx Hx. unfold DyadicLog.fast_asinh_near, DyadicLog.fast_asinh.
rewrite (fast_asinh_pos_fma (fabs x) (fabs_finite x Fx)) by (rewrite fabs_R; exact Hx).
reflexivity.
Qed.

Theorem fast_acosh_dir_fma :
  forall x up, is_finite x = true -> 1 <= B2R x ->
  DyadicLog.fast_acosh_dir true x up = DyadicLog.fast_acosh_dir false x up.
Proof.
intros x up Fx Hx. unfold DyadicLog.fast_acosh_dir. rewrite (fast_acosh_fma x Fx Hx).
reflexivity.
Qed.

Theorem fast_acosh_near_fma :
  forall x, is_finite x = true -> 1 <= B2R x ->
  DyadicLog.fast_acosh_near true x = DyadicLog.fast_acosh_near false x.
Proof.
intros x Fx Hx. unfold DyadicLog.fast_acosh_near. rewrite (fast_acosh_fma x Fx Hx).
reflexivity.
Qed.

Theorem fast_atanh_dir_fma :
  forall x up, is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) < 1 ->
  DyadicLog.fast_atanh_dir true x up = DyadicLog.fast_atanh_dir false x up.
Proof.
intros x up Fx Hx. unfold DyadicLog.fast_atanh_dir, DyadicLog.fast_atanh.
rewrite (fast_atanh_pos_fma (fabs x) (fabs_finite x Fx)) by (rewrite fabs_R; exact Hx).
reflexivity.
Qed.

Theorem fast_atanh_near_fma :
  forall x, is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) < 1 ->
  DyadicLog.fast_atanh_near true x = DyadicLog.fast_atanh_near false x.
Proof.
intros x Fx Hx. unfold DyadicLog.fast_atanh_near, DyadicLog.fast_atanh.
rewrite (fast_atanh_pos_fma (fabs x) (fabs_finite x Fx)) by (rewrite fabs_R; exact Hx).
reflexivity.
Qed.

(** At [x = 1], [acosh x = 0], and the directed fast paths return [None],
    so that the kernel's exact enclosure settles it. *)
Theorem fast_acosh_one :
  forall fma up, DyadicLog.fast_acosh_dir fma DyadicExp.one up = None.
Proof.
intros [|] [|]; vm_compute; reflexivity.
Qed.
