(** * [try_from_ninterval_exact], which [interval_exact!] calls

    [try_from_ninterval_exact] returns [Ok] exactly when both bounds of [x]
    are exact, and then an interval that holds exactly the reals that [x]
    denotes, which is the tightest one. Unlike [From<NInterval>], it needs
    no hypothesis on [x]: bounds in the wrong order give the empty
    interval, which holds no real, as [x] then denotes none. *)

From Stdlib Require Import ZArith Reals Qreals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Mpfr MpfrRound ParseRound Integer ValidMake.

Open Scope R_scope.

(** [r] is at or above the lower bound [a] of an interval, and at or below
    its upper bound [b], as [mem] says of the bounds: -inf bounds no real
    from below and +inf none from above, while no real passes a NaN bound,
    a lower bound +inf or an upper bound -inf. *)
Definition lo_mem (a : f64) (r : R) : Prop :=
  match a with
  | B754_infinity s => s = true
  | B754_nan => False
  | a => B2R a <= r
  end.

Definition hi_mem (b : f64) (r : R) : Prop :=
  match b with
  | B754_infinity s => s = false
  | B754_nan => False
  | b => r <= B2R b
  end.

(** [with_infsup_raw a b] stores [[-a; b]], so [mem] reads [a] back as
    [-(-a)]. *)
Lemma mem_with_infsup_raw :
  forall a b r,
  mem r (Interval.with_infsup_raw a b) <-> lo_mem a r /\ hi_mem b r.
Proof.
intros a b r. unfold mem, Interval.with_infsup_raw, Generic.constant.
cbn [rep fst snd]. unfold opp. rewrite (Bopp_involutive _ _ a).
unfold lo_mem, hi_mem. destruct a, b; cbn beta iota; tauto.
Qed.

(** An exact lower bound [n], rounded down to [w], bounds the same reals
    as [w]: an infinity is itself, and rounding a rational that is a float
    gives that float, or a zero for 0, as a float at or below it cannot be
    above it. *)
Lemma lo_mem_exact :
  forall n w, number_exact n -> number_round Inf n w ->
  forall r, lo_mem w r <-> above_num n r.
Proof.
intros [|q|] w Hn Hw r; cbn [number_round number_exact above_num as_rnd_t] in *.
- subst w. cbn [lo_mem]. split; intros _; [exact I | reflexivity].
- destruct w as [s|[|]| |s mw ew Hw'];
    cbn [with_val mpfr_round] in Hw; cbn [lo_mem].
  + (* [Rnd_DN_pt] of a float is that float, here 0. *)
    pose proof (Rnd_DN_pt_idempotent _ _ _ Hw Hn) as E.
    cbn [B2R]. split; intros; lra.
  + (* -inf is below every float, and [Q2R q] is one. *)
    pose proof (Hw _ Hn). lra.
  + contradiction.
  + contradiction.
  + destruct Hw as [_ Hw].
    pose proof (Rnd_DN_pt_idempotent _ _ _ Hw Hn) as E.
    rewrite E. tauto.
- subst w. cbn [lo_mem]. split; intros H; [discriminate H | destruct H].
Qed.

(** The same for an exact upper bound, rounded up. *)
Lemma hi_mem_exact :
  forall n w, number_exact n -> number_round Sup n w ->
  forall r, hi_mem w r <-> below_num n r.
Proof.
intros [|q|] w Hn Hw r; cbn [number_round number_exact below_num as_rnd_t] in *.
- subst w. cbn [hi_mem]. split; intros H; [discriminate H | destruct H].
- destruct w as [s|[|]| |s mw ew Hw'];
    cbn [with_val mpfr_round] in Hw; cbn [hi_mem].
  + pose proof (Rnd_UP_pt_idempotent _ _ _ Hw Hn) as E.
    cbn [B2R]. split; intros; lra.
  + contradiction.
  + (* +inf is above every float, and [Q2R q] is one. *)
    pose proof (Hw _ Hn). lra.
  + contradiction.
  + destruct Hw as [_ Hw].
    pose proof (Rnd_UP_pt_idempotent _ _ _ Hw Hn) as E.
    rewrite E. tauto.
- subst w. cbn [hi_mem]. split; intros _; [exact I | reflexivity].
Qed.

(** [TryFrom<(f64, f64)>] returns [with_infsup_raw a b] when it succeeds. *)
Lemma try_from_raw :
  forall a b y, Interval.try_from a b = Some y -> y = Interval.with_infsup_raw a b.
Proof.
intros a b y T. unfold Interval.try_from in T.
match type of T with
| (if ?g then _ else _) = _ => destruct g; [|discriminate T]
end.
injection T as <-. reflexivity.
Qed.

(** If a real [r] lies between [a] and [b], they pass the test of
    [TryFrom<(f64, f64)>]: [a] is -inf or finite, [b] is +inf or finite,
    and [a <= r <= b] when both are finite. *)
Lemma try_from_lo_hi :
  forall a b r, lo_mem a r -> hi_mem b r ->
  Interval.try_from a b = Some (Interval.with_infsup_raw a b).
Proof.
intros a b r Ha Hb. unfold Interval.try_from, Model.le, Model.eq.
assert (G : Bleb a b = true).
{ destruct a as [sa|[|]| |sa ma ea Ea], b as [sb|[|]| |sb mb eb Eb];
    cbn [lo_mem hi_mem] in Ha, Hb; try discriminate; try contradiction;
    try reflexivity;
    rewrite Bleb_correct by reflexivity; apply Rle_bool_true; lra. }
rewrite G.
destruct a as [sa|[|]| |sa ma ea Ea], b as [sb|[|]| |sb mb eb Eb];
  cbn [lo_mem hi_mem] in Ha, Hb; try discriminate; try contradiction;
  reflexivity.
Qed.

Theorem try_from_ninterval_exact_correct :
  forall m x, parse_ok m ->
  match Interval.try_from_ninterval_exact m x with
  | Some y =>
      number_exact (ninf x) /\ number_exact (nsup x) /\
      is_tightest (ninterval_set x) y /\ (forall r, mem r y <-> ninterval_set x r)
  | None => ~ (number_exact (ninf x) /\ number_exact (nsup x))
  end.
Proof.
intros m x Hm.
destruct (number_to_f64_correct m (ninf x) Inf Hm) as (Ra & Ea & _).
destruct (number_to_f64_correct m (nsup x) Sup Hm) as (Rb & Eb & _).
unfold Interval.try_from_ninterval_exact. cbv zeta.
set (a := number_to_f64 m (ninf x) Inf) in *.
set (b := number_to_f64 m (nsup x) Sup) in *.
destruct (f64_inexact a) eqn:Ia; [|destruct (f64_inexact b) eqn:Ib]; cbn [orb].
- (* An inexact bound gives [Err], and the bound is not exact. *)
  intros [Na _]. apply Ea in Na. congruence.
- intros [_ Nb]. apply Eb in Nb. congruence.
- assert (Na : number_exact (ninf x)) by (apply Ea; congruence).
  assert (Nb : number_exact (nsup x)) by (apply Eb; congruence).
  set (y := match Interval.try_from (f64_f a) (f64_f b) with
            | Some y => y | None => Interval.EMPTY end).
  (* Exact bounds bound the same reals as the floats they round to, so
     [y] holds exactly the reals of [x]. If [TryFrom] fails, no real lies
     between the floats, so none lies between the bounds either. *)
  assert (Hmem : forall r, mem r y <-> ninterval_set x r).
  { intros r. unfold ninterval_set.
    destruct (lo_mem_exact _ _ Na Ra r) as [A1 A2].
    destruct (hi_mem_exact _ _ Nb Rb r) as [B1 B2].
    unfold y. destruct (Interval.try_from (f64_f a) (f64_f b)) as [z|] eqn:T.
    - apply try_from_raw in T. subst z.
      destruct (mem_with_infsup_raw (f64_f a) (f64_f b) r) as [M1 M2].
      split.
      + intros H. destruct (M1 H) as [H1 H2]. split; auto.
      + intros [H1 H2]. apply M2. split; auto.
    - split.
      + intros H. destruct (mem_nan Interval.EMPTY r eq_refl H).
      + intros [H1 H2].
        rewrite (try_from_lo_hi _ _ r (A2 H1) (B2 H2)) in T. discriminate T. }
  assert (V : valid y).
  { unfold y. destruct (Interval.try_from (f64_f a) (f64_f b)) as [z|] eqn:T.
    - exact (try_from_valid _ _ _ T).
    - exact EMPTY_valid. }
  split; [exact Na|]. split; [exact Nb|]. split; [|exact Hmem].
  split; [exact V|]. split.
  + intros r Hr. apply Hmem. exact Hr.
  + intros z _ Hz r Hr. apply Hz. apply Hmem. exact Hr.
Qed.
