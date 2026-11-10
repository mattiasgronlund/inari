(** * The fast paths of [sinh], [cosh] and [tanh]

    Where [DyadicExp.fast_sinh_dir] and the others of [Model.v] return,
    they return [sinh x], [cosh t] and [tanh x] rounded toward +inf if
    [up] and toward -inf otherwise ([fast_sinh_dir_correct] and the
    others), and rounded to nearest ([fast_sinh_near_correct] and the
    others), from the bounds of [FastHypPos.v], [FastCoshPos.v] and
    [FastTanhPos.v] and the tests of [FastRoundErr.v]. [sinh] and [tanh]
    are odd: for [x < 0] they round [f(|x|)] in the other direction and
    negate it. They return the same with and without an FMA
    ([fast_sinh_dir_fma] and the others). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Elementary ExpReal TwoSum DyDriver NearF64 NearCells
  FastRound FastRoundErr FastDiv FastHypPos FastCoshPos FastTanhPos.
From Inari Require DyExp DyPown.

Open Scope R_scope.

(** ** The common part *)

(** What [FastHypPos.v], [FastCoshPos.v] and [FastTanhPos.v] prove of
    [fast_sinh_pos] and the others for [f] = [sinh], [cosh] and [tanh]. *)
Local Definition pos_bound (f : R -> R) (pos : f64 -> option (f64 * f64 * Z * f64)) : Prop :=
  forall t h l e err,
  is_finite t = true -> 0 <= B2R t -> pos t = Some (h, l, e, err) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= e <= 1022)%Z /\
  exists p, (55 <= p <= 105)%Z /\ B2R err = bpow radix2 (- p) /\
    Rabs (f (B2R t) * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (- p).

Local Lemma fabs_facts :
  forall x, is_finite x = true ->
  is_finite (fabs x) = true /\ B2R (fabs x) = Rabs (B2R x) /\ 0 <= B2R (fabs x).
Proof.
intros x Fx. unfold fabs. rewrite is_finite_Babs, B2R_Babs.
split; [exact Fx | split; [reflexivity | apply Rabs_pos]].
Qed.

Local Lemma scale_back : forall y e, y = y * bpow radix2 (- e) * bpow radix2 e.
Proof.
intros y e. rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l.
change (bpow radix2 0) with 1. ring.
Qed.

(** For [t >= 0], the tests of [FastRoundErr.v] on the bound of [f(t)]. *)
Local Lemma pos_dir :
  forall f pos t up v,
  pos_bound f pos -> is_finite t = true -> 0 <= B2R t ->
  match pos t with
  | Some (h, l, e, err) => Fast.round_dir_err h l e err up
  | None => None
  end = Some v ->
  rounds up (f (B2R t)) v.
Proof.
intros f pos t up v P Ft Ht H.
destruct (pos t) as [[[[h l] e] err]|] eqn:E; [|discriminate H].
destruct (P t h l e err Ft Ht E) as (Fh & Fl & Eh & He & p & Hp & Herr & Hb).
rewrite (scale_back (f (B2R t)) e).
exact (round_dir_err_correct h l e err p up v _ Fh Fl Eh He Hp Herr Hb H).
Qed.

Local Lemma pos_near :
  forall f pos t v,
  pos_bound f pos -> is_finite t = true -> 0 <= B2R t ->
  match pos t with
  | Some (h, l, e, err) => Fast.round_near_err h l e err
  | None => None
  end = Some v ->
  near_round (f (B2R t)) v.
Proof.
intros f pos t v P Ft Ht H.
destruct (pos t) as [[[[h l] e] err]|] eqn:E; [|discriminate H].
destruct (P t h l e err Ft Ht E) as (Fh & Fl & Eh & He & p & Hp & Herr & Hb).
rewrite (scale_back (f (B2R t)) e).
exact (round_near_err_correct h l e err p v _ Fh Fl Eh He Hp Herr Hb H).
Qed.

(** An odd [f] at [x < 0] is [-f(|x|)]: rounding [f(|x|)] in the other
    direction and negating it rounds [f(x)] ([DyPown.rounds_odd]). [x =
    -0] is not below [0] and takes the branch of [x >= 0]. *)
Local Lemma odd_dir :
  forall f pos x up v,
  pos_bound f pos -> (forall r, f (- r) = - f r) -> is_finite x = true ->
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
intros f pos x up v P O Fx H.
destruct (fabs_facts x Fx) as (Ft & Et & Ht).
destruct (pos (fabs x)) as [[[[h l] e] err]|] eqn:E; [|discriminate H].
destruct (Fast.round_dir_err h l e err (xorb up (lt x zero))) as [r|] eqn:R; [|discriminate H].
injection H as <-.
assert (Hr : rounds (xorb up (lt x zero)) (f (B2R (fabs x))) r).
{ apply (pos_dir f pos (fabs x) _ r P Ft Ht). rewrite E. exact R. }
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
  forall f pos x v,
  pos_bound f pos -> (forall r, f (- r) = - f r) -> is_finite x = true ->
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
intros f pos x v P O Fx H.
destruct (fabs_facts x Fx) as (Ft & Et & Ht).
destruct (pos (fabs x)) as [[[[h l] e] err]|] eqn:E; [|discriminate H].
destruct (Fast.round_near_err h l e err) as [r|] eqn:R; [|discriminate H].
injection H as <-.
assert (Hr : near_round (f (B2R (fabs x))) r).
{ apply (pos_near f pos (fabs x) r P Ft Ht). rewrite E. exact R. }
rewrite Et in Hr.
destruct (DyExp.lt_zero_spec x) as (N1 & N2).
destruct (lt x zero) eqn:L.
- rewrite Rabs_left1, O in Hr by (apply N1; reflexivity).
  rewrite <- (Ropp_involutive (f (B2R x))).
  exact (near_opp _ r Hr).
- rewrite Rabs_pos_eq in Hr by (apply N2; reflexivity). exact Hr.
Qed.

(** [sinh] is odd ([tanh_odd] of [ExpReal.v] is [tanh]'s). *)
Local Lemma sinh_odd : forall r, sinh (- r) = - sinh r.
Proof. intros r. unfold sinh. rewrite Ropp_involutive. field. Qed.

(** ** Rounded toward -inf and +inf *)

Theorem fast_sinh_dir_correct :
  forall fma x up v,
  is_finite x = true -> DyadicExp.fast_sinh_dir fma x up = Some v ->
  rounds up (sinh (B2R x)) v.
Proof.
intros fma x up v Fx H.
exact (odd_dir sinh _ x up v (fast_sinh_pos_correct fma) sinh_odd Fx H).
Qed.

Theorem fast_cosh_dir_correct :
  forall fma t up v,
  is_finite t = true -> 0 <= B2R t -> DyadicExp.fast_cosh_dir fma t up = Some v ->
  rounds up (cosh (B2R t)) v.
Proof.
intros fma t up v Ft Ht H.
exact (pos_dir cosh _ t up v (fast_cosh_pos_correct fma) Ft Ht H).
Qed.

Theorem fast_tanh_dir_correct :
  forall fma x up v,
  is_finite x = true -> DyadicExp.fast_tanh_dir fma x up = Some v ->
  rounds up (tanh (B2R x)) v.
Proof.
intros fma x up v Fx H.
exact (odd_dir tanh _ x up v (fast_tanh_pos_correct fma) tanh_odd Fx H).
Qed.

(** ** Rounded to nearest *)

Theorem fast_sinh_near_correct :
  forall fma x v,
  is_finite x = true -> DyadicExp.fast_sinh_near fma x = Some v ->
  near_round (sinh (B2R x)) v.
Proof.
intros fma x v Fx H.
exact (odd_near sinh _ x v (fast_sinh_pos_correct fma) sinh_odd Fx H).
Qed.

Theorem fast_cosh_near_correct :
  forall fma t v,
  is_finite t = true -> 0 <= B2R t -> DyadicExp.fast_cosh_near fma t = Some v ->
  near_round (cosh (B2R t)) v.
Proof.
intros fma t v Ft Ht H.
exact (pos_near cosh _ t v (fast_cosh_pos_correct fma) Ft Ht H).
Qed.

Theorem fast_tanh_near_correct :
  forall fma x v,
  is_finite x = true -> DyadicExp.fast_tanh_near fma x = Some v ->
  near_round (tanh (B2R x)) v.
Proof.
intros fma x v Fx H.
exact (odd_near tanh _ x v (fast_tanh_pos_correct fma) tanh_odd Fx H).
Qed.

(** ** With and without an FMA *)

Theorem fast_sinh_dir_fma :
  forall x up,
  is_finite x = true ->
  DyadicExp.fast_sinh_dir true x up = DyadicExp.fast_sinh_dir false x up.
Proof.
intros x up Fx. destruct (fabs_facts x Fx) as (Ft & _ & Ht).
unfold DyadicExp.fast_sinh_dir. rewrite (fast_sinh_pos_fma _ Ft Ht). reflexivity.
Qed.

Theorem fast_cosh_dir_fma :
  forall t up,
  is_finite t = true -> 0 <= B2R t ->
  DyadicExp.fast_cosh_dir true t up = DyadicExp.fast_cosh_dir false t up.
Proof.
intros t up Ft Ht.
unfold DyadicExp.fast_cosh_dir. rewrite (fast_cosh_pos_fma _ Ft Ht). reflexivity.
Qed.

Theorem fast_tanh_dir_fma :
  forall x up,
  is_finite x = true ->
  DyadicExp.fast_tanh_dir true x up = DyadicExp.fast_tanh_dir false x up.
Proof.
intros x up Fx. destruct (fabs_facts x Fx) as (Ft & _ & Ht).
unfold DyadicExp.fast_tanh_dir. rewrite (fast_tanh_pos_fma _ Ft Ht). reflexivity.
Qed.

Theorem fast_sinh_near_fma :
  forall x,
  is_finite x = true ->
  DyadicExp.fast_sinh_near true x = DyadicExp.fast_sinh_near false x.
Proof.
intros x Fx. destruct (fabs_facts x Fx) as (Ft & _ & Ht).
unfold DyadicExp.fast_sinh_near. rewrite (fast_sinh_pos_fma _ Ft Ht). reflexivity.
Qed.

Theorem fast_cosh_near_fma :
  forall t,
  is_finite t = true -> 0 <= B2R t ->
  DyadicExp.fast_cosh_near true t = DyadicExp.fast_cosh_near false t.
Proof.
intros t Ft Ht.
unfold DyadicExp.fast_cosh_near. rewrite (fast_cosh_pos_fma _ Ft Ht). reflexivity.
Qed.

Theorem fast_tanh_near_fma :
  forall x,
  is_finite x = true ->
  DyadicExp.fast_tanh_near true x = DyadicExp.fast_tanh_near false x.
Proof.
intros x Fx. destruct (fabs_facts x Fx) as (Ft & _ & Ht).
unfold DyadicExp.fast_tanh_near. rewrite (fast_tanh_pos_fma _ Ft Ht). reflexivity.
Qed.
