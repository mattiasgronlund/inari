(** * The fast paths of [sin], [cos] and [tan]

    Where [DyadicTrig.fast_sin_dir] and the others of [Model.v] return at
    an [x] with [|x| >= 2^-27], they return the function rounded toward
    +inf if [up] and toward -inf otherwise ([fast_sin_dir_correct] and the
    others), and rounded to nearest ([fast_sin_near_correct] and the
    others), from the results before the rounding of [FastTrigCore.v] and
    the rounding of [FastTrigRound.v]. They return the same with and
    without an FMA ([fast_sin_dir_fma] and the others). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr TwoSum DyDriver NearF64 FastRound FastTrigTables
  FastTrigReduce FastTrigSC FastTrigEval FastTrigDiv FastTrigRound FastTrigCore.

Open Scope R_scope.

(** ** The arguments that reach the fast paths *)

(** [B2R] of a literal, by its [B2SF]. *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** The rules before the fast paths leave [|x| >= 2^-26] (rounded toward
    +inf or -inf) and [|x| >= 2^-27] (rounded to nearest). *)
Lemma fast_arg_hyp :
  forall x, is_finite x = true -> lt (fabs x) DyadicExp.tiny_hyp = false ->
  bpow radix2 (-27) <= Rabs (B2R x).
Proof.
intros x Fx H. unfold Model.lt in H.
rewrite Bltb_correct in H
  by (unfold fabs; rewrite ?is_finite_Babs; first [exact Fx | vm_compute; reflexivity]).
assert (L : B2R DyadicExp.tiny_hyp = bpow radix2 (-26)).
{ lit_B2R. change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
  reflexivity. }
destruct (Rlt_bool_spec (B2R (fabs x)) (B2R DyadicExp.tiny_hyp)); [discriminate H|].
unfold fabs in *. rewrite B2R_Babs in *.
assert (bpow radix2 (-27) <= bpow radix2 (-26)) by (apply bpow_le; lia).
lra.
Qed.

Lemma fast_arg_near :
  forall x, is_finite x = true -> lt (fabs x) DyadicExp.tiny_near = false ->
  bpow radix2 (-27) <= Rabs (B2R x).
Proof.
intros x Fx H. unfold Model.lt in H.
rewrite Bltb_correct in H
  by (unfold fabs; rewrite ?is_finite_Babs; first [exact Fx | vm_compute; reflexivity]).
assert (L : B2R DyadicExp.tiny_near = bpow radix2 (-27)).
{ lit_B2R. change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
  reflexivity. }
destruct (Rlt_bool_spec (B2R (fabs x)) (B2R DyadicExp.tiny_near)); [discriminate H|].
unfold fabs in *. rewrite B2R_Babs in *. lra.
Qed.

(** [cos] works on [t = |x|]. *)
Lemma fast_arg_fabs :
  forall x, bpow radix2 (-27) <= Rabs (B2R x) ->
  is_finite x = true -> is_finite (fabs x) = true /\ bpow radix2 (-27) <= Rabs (B2R (fabs x)).
Proof.
intros x Hx Fx. unfold fabs. rewrite is_finite_Babs, B2R_Babs, Rabs_Rabsolu.
split; [exact Fx | exact Hx].
Qed.

Lemma cos_fabs : forall x, cos (B2R (fabs x)) = cos (B2R x).
Proof.
intros x. unfold fabs. rewrite B2R_Babs. unfold Rabs.
destruct (Rcase_abs (B2R x)); [apply cos_neg | reflexivity].
Qed.

(** ** Rounded toward -inf and +inf *)

Theorem fast_sin_dir_correct :
  forall fma x up v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicTrig.fast_sin_dir fma x up = Some v ->
  rounds up (sin (B2R x)) v.
Proof.
intros fma x up v Fx Hx H. unfold DyadicTrig.fast_sin_dir in H.
destruct fma; [rewrite (FastTrigCore.fast_sin_fma x Hx) in H|].
all: destruct (DyadicTrig.fast_sin false x) as [[h l]|] eqn:E; [|discriminate H].
all: destruct (FastTrigCore.fast_sin_correct x h l Fx Hx E) as (Fh & Fl & Hrn & Hh & Herr).
all: apply (FastTrigRound.fast_round_dir_correct h l up v _ Fh Fl Hrn Hh); [|exact H].
all: assert (0 <= bpow radix2 (-71) * Rabs (sin (B2R x)))
       by (apply Rmult_le_pos; [apply bpow_ge_0 | apply Rabs_pos]).
all: lra.
Qed.

Theorem fast_cos_dir_correct :
  forall fma t up v,
  is_finite t = true -> bpow radix2 (-27) <= Rabs (B2R t) ->
  DyadicTrig.fast_cos_dir fma t up = Some v ->
  rounds up (cos (B2R t)) v.
Proof.
intros fma t up v Ft Ht H. unfold DyadicTrig.fast_cos_dir in H.
destruct fma; [rewrite (FastTrigCore.fast_cos_fma t Ht) in H|].
all: destruct (DyadicTrig.fast_cos false t) as [[h l]|] eqn:E; [|discriminate H].
all: destruct (FastTrigCore.fast_cos_correct t h l Ft Ht E) as (Fh & Fl & Hrn & Hh & Herr).
all: apply (FastTrigRound.fast_round_dir_correct h l up v _ Fh Fl Hrn Hh); [|exact H].
all: assert (0 <= bpow radix2 (-71) * Rabs (cos (B2R t)))
       by (apply Rmult_le_pos; [apply bpow_ge_0 | apply Rabs_pos]).
all: lra.
Qed.

Theorem fast_tan_dir_correct :
  forall fma x up v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicTrig.fast_tan_dir fma x up = Some v ->
  rounds up (tan (B2R x)) v.
Proof.
intros fma x up v Fx Hx H. unfold DyadicTrig.fast_tan_dir in H.
destruct fma; [rewrite (FastTrigCore.fast_tan_fma x Hx) in H|].
all: destruct (DyadicTrig.fast_tan false x) as [[h l]|] eqn:E; [|discriminate H].
all: destruct (FastTrigCore.fast_tan_correct x h l Fx Hx E) as (Fh & Fl & Hrn & Hh & Herr).
all: apply (FastTrigRound.fast_round_dir_correct h l up v _ Fh Fl Hrn Hh); [|exact H].
all: exact Herr.
Qed.

(** ** Rounded to nearest *)

Theorem fast_sin_near_correct :
  forall fma x v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicTrig.fast_sin_near fma x = Some v ->
  near_round (sin (B2R x)) v.
Proof.
intros fma x v Fx Hx H. unfold DyadicTrig.fast_sin_near in H.
destruct fma; [rewrite (FastTrigCore.fast_sin_fma x Hx) in H|].
all: destruct (DyadicTrig.fast_sin false x) as [[h l]|] eqn:E; [|discriminate H].
all: destruct (FastTrigCore.fast_sin_correct x h l Fx Hx E) as (Fh & Fl & Hrn & Hh & Herr).
all: apply (FastTrigRound.fast_round_near_correct h l v _ Fh Fl Hrn Hh); [|exact H].
all: assert (0 <= bpow radix2 (-71) * Rabs (sin (B2R x)))
       by (apply Rmult_le_pos; [apply bpow_ge_0 | apply Rabs_pos]).
all: lra.
Qed.

Theorem fast_cos_near_correct :
  forall fma t v,
  is_finite t = true -> bpow radix2 (-27) <= Rabs (B2R t) ->
  DyadicTrig.fast_cos_near fma t = Some v ->
  near_round (cos (B2R t)) v.
Proof.
intros fma t v Ft Ht H. unfold DyadicTrig.fast_cos_near in H.
destruct fma; [rewrite (FastTrigCore.fast_cos_fma t Ht) in H|].
all: destruct (DyadicTrig.fast_cos false t) as [[h l]|] eqn:E; [|discriminate H].
all: destruct (FastTrigCore.fast_cos_correct t h l Ft Ht E) as (Fh & Fl & Hrn & Hh & Herr).
all: apply (FastTrigRound.fast_round_near_correct h l v _ Fh Fl Hrn Hh); [|exact H].
all: assert (0 <= bpow radix2 (-71) * Rabs (cos (B2R t)))
       by (apply Rmult_le_pos; [apply bpow_ge_0 | apply Rabs_pos]).
all: lra.
Qed.

Theorem fast_tan_near_correct :
  forall fma x v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicTrig.fast_tan_near fma x = Some v ->
  near_round (tan (B2R x)) v.
Proof.
intros fma x v Fx Hx H. unfold DyadicTrig.fast_tan_near in H.
destruct fma; [rewrite (FastTrigCore.fast_tan_fma x Hx) in H|].
all: destruct (DyadicTrig.fast_tan false x) as [[h l]|] eqn:E; [|discriminate H].
all: destruct (FastTrigCore.fast_tan_correct x h l Fx Hx E) as (Fh & Fl & Hrn & Hh & Herr).
all: apply (FastTrigRound.fast_round_near_correct h l v _ Fh Fl Hrn Hh); [|exact H].
all: exact Herr.
Qed.

(** ** With and without an FMA *)

Theorem fast_sin_dir_fma :
  forall x up, bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicTrig.fast_sin_dir true x up = DyadicTrig.fast_sin_dir false x up.
Proof.
intros x up Hx. unfold DyadicTrig.fast_sin_dir. rewrite (FastTrigCore.fast_sin_fma x Hx). reflexivity.
Qed.

Theorem fast_cos_dir_fma :
  forall t up, bpow radix2 (-27) <= Rabs (B2R t) ->
  DyadicTrig.fast_cos_dir true t up = DyadicTrig.fast_cos_dir false t up.
Proof.
intros t up Ht. unfold DyadicTrig.fast_cos_dir. rewrite (FastTrigCore.fast_cos_fma t Ht). reflexivity.
Qed.

Theorem fast_tan_dir_fma :
  forall x up, bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicTrig.fast_tan_dir true x up = DyadicTrig.fast_tan_dir false x up.
Proof.
intros x up Hx. unfold DyadicTrig.fast_tan_dir. rewrite (FastTrigCore.fast_tan_fma x Hx). reflexivity.
Qed.

Theorem fast_sin_near_fma :
  forall x, bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicTrig.fast_sin_near true x = DyadicTrig.fast_sin_near false x.
Proof.
intros x Hx. unfold DyadicTrig.fast_sin_near. rewrite (FastTrigCore.fast_sin_fma x Hx). reflexivity.
Qed.

Theorem fast_cos_near_fma :
  forall t, bpow radix2 (-27) <= Rabs (B2R t) ->
  DyadicTrig.fast_cos_near true t = DyadicTrig.fast_cos_near false t.
Proof.
intros t Ht. unfold DyadicTrig.fast_cos_near. rewrite (FastTrigCore.fast_cos_fma t Ht). reflexivity.
Qed.

Theorem fast_tan_near_fma :
  forall x, bpow radix2 (-27) <= Rabs (B2R x) ->
  DyadicTrig.fast_tan_near true x = DyadicTrig.fast_tan_near false x.
Proof.
intros x Hx. unfold DyadicTrig.fast_tan_near. rewrite (FastTrigCore.fast_tan_fma x Hx). reflexivity.
Qed.
