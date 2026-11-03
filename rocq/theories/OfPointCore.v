(** * MPFR functions made of functions of [f64]s: the pieces

    [OfPoint.v] makes, of every record [point] [p], MPFR functions
    [of_point p] with [mpfr_point (of_point p) = p]. This file has the
    pieces that it builds them of. MPFR's exponent range is that of
    [f64], [emin = -1073] and [emax = 1024], as [rational_to_f64] sets it:
    the least positive MPFR number of 53 bits, [2^(emin - 1)], and the
    largest, [(2^53 - 1) * 2^(emax - 53)], are then those of [f64]. *)

From Stdlib Require Import ZArith Reals Lra Lia Eqdep_dec.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Mpfr MpfrRound MpfrIdeal IdealRound IdealGetD
  Contract.

Open Scope R_scope.

Lemma range_ok_f64 : range_ok (-1073) 1024.
Proof. split; lia. Qed.

(** Equality of [f64]s is decidable, without an axiom: the proof in
    [B754_finite] is one of [bounded _ _ = true], an equality of
    booleans. *)
Definition f64_eq_dec (x y : f64) : {x = y} + {x <> y}.
Proof.
destruct x as [s|s| |s mx ex Hx], y as [s'|s'| |s' my ey Hy];
  try (right; discriminate).
- destruct (Bool.bool_dec s s') as [<-|Hs];
    [left; reflexivity | right; intros E; injection E; exact Hs].
- destruct (Bool.bool_dec s s') as [<-|Hs];
    [left; reflexivity | right; intros E; injection E; exact Hs].
- left; reflexivity.
- destruct (Bool.bool_dec s s') as [<-|Hs];
    [|right; intros E; injection E; intros; exact (Hs ltac:(assumption))].
  destruct (Pos.eq_dec mx my) as [<-|Hm];
    [|right; intros E; injection E; intros; exact (Hm ltac:(assumption))].
  destruct (Z.eq_dec ex ey) as [<-|He];
    [|right; intros E; injection E; intros; exact (He ltac:(assumption))].
  left. f_equal. apply UIP_dec, Bool.bool_dec.
Defined.

(** An MPFR number for the [f64] [w] that a function of [f64]s returns,
    where the exact result is [r]: [r] rounded in the direction [rnd] to
    an MPFR number of 53 bits if [mpfr_get_d], as [ideal_get_d] models
    it, converts that to [w], and [w] itself otherwise. Either way it
    converts to [w] ([ideal_get_d_lift_val]), and if [w] is [r] rounded
    to an [f64], it is [r] rounded to an MPFR number
    ([lift_val_correct]). *)
Definition lift_val (rnd : mpfr_rnd) (r : R) (w : f64) : mpfr_t :=
  let y := round_mpfr (-1073) 1024 rnd r in
  if f64_eq_dec (ideal_get_d rnd y) w then y else with_val w.

(** [f] at a finite [f64], and nothing at the others. *)
Definition fin (f : R -> R) (x : f64) : option R :=
  if is_finite x then Some (f (B2R x)) else None.

(** The MPFR function of one number made of the function [h] of [f64]s:
    the argument converted to an [f64], [h] of it, and that as an MPFR
    number, with [lift_val] where [F] gives the exact result. *)
Definition lift1 (F : f64 -> option R) (h : mpfr_rnd -> f64 -> f64)
    (rnd : mpfr_rnd) (v : mpfr_t) : mpfr_t :=
  let x := ideal_get_d RNDD v in
  match F x with
  | Some r => lift_val rnd r (h rnd x)
  | None => with_val (h rnd x)
  end.

(** The same for two numbers. *)
Definition lift2 (F : f64 -> f64 -> option R) (h : mpfr_rnd -> f64 -> f64 -> f64)
    (rnd : mpfr_rnd) (v u : mpfr_t) : mpfr_t :=
  let x := ideal_get_d RNDD v in
  let y := ideal_get_d RNDD u in
  match F x y with
  | Some r => lift_val rnd r (h rnd x y)
  | None => with_val (h rnd x y)
  end.

(** The same for a number and an integer. *)
Definition lift_si (F : f64 -> Z -> option R) (h : mpfr_rnd -> f64 -> Z -> f64)
    (rnd : mpfr_rnd) (v : mpfr_t) (n : Z) : mpfr_t :=
  let x := ideal_get_d RNDD v in
  match F x n with
  | Some r => lift_val rnd r (h rnd x n)
  | None => with_val (h rnd x n)
  end.

(** ** Helpers *)

(** The format of the finite [f64]s without the bound above, as in
    [IdealGetD.v]. *)
Local Notation G := (generic_format radix2 (SpecFloat.fexp 53 1024)).

(** [round_f64] keeps a float of [G] below [2^1024] in magnitude. *)
Lemma round_f64_exact :
  forall rnd x, G x -> Rabs x < bpow radix2 1024 ->
  is_finite (round_f64 rnd x) = true /\ B2R (round_f64 rnd x) = x.
Proof.
intros rnd x Gx Hx.
pose proof (round_f64_cases rnd x) as Hc. cbv zeta in Hc.
rewrite (round_generic radix2 _ _ x Gx) in Hc.
destruct Hc as [(_ & Fz & Ez) | (Hb & _)]; [split; assumption | lra].
Qed.

Lemma f64_format_G_lt : forall x, G x -> Rabs x < bpow radix2 1024 -> f64_format x.
Proof.
intros x Gx Hx. destruct (round_f64_exact RNDD x Gx Hx) as [Fz Ez].
exists (round_f64 RNDD x). split; assumption.
Qed.

(** The powers of 2 from [2^-1074] to [2^1023], and their negations, are
    [f64]s. *)
Lemma f64_format_bpow :
  forall e, (-1074 <= e < 1024)%Z ->
  f64_format (bpow radix2 e) /\ f64_format (- bpow radix2 e).
Proof.
intros e He.
assert (Ge : G (bpow radix2 e))
  by (apply generic_format_bpow; unfold SpecFloat.fexp, SpecFloat.emin; lia).
assert (Hb : bpow radix2 e < bpow radix2 1024) by (apply bpow_lt; lia).
assert (Hp : 0 < bpow radix2 e) by apply bpow_gt_0.
split; apply f64_format_G_lt.
- exact Ge.
- rewrite Rabs_pos_eq; lra.
- apply generic_format_opp. exact Ge.
- rewrite Rabs_Ropp, Rabs_pos_eq; lra.
Qed.

(** The largest MPFR number at [emax = 1024], [(2^53 - 1) * 2^971], and
    its negation are [f64]s. *)
Lemma f64_format_max : f64_format (mpfr_max 1024) /\ f64_format (- mpfr_max 1024).
Proof.
assert (Gm : G (mpfr_max 1024)).
{ change (generic_format radix2 (FLT_exp (-1074) 53) (mpfr_max 1024)).
  apply generic_format_FLT.
  apply (FLT_spec _ _ _ _ (Float radix2 (2 ^ 53 - 1) (1024 - 53))); [reflexivity | |].
  - cbn [Fnum]. vm_compute. reflexivity.
  - cbn [Fexp]. lia. }
assert (E : mpfr_max 1024 = bpow radix2 1024 - bpow radix2 (1024 - 53))
  by apply mpfr_max_eq.
assert (H0 : 0 < bpow radix2 (1024 - 53)) by apply bpow_gt_0.
assert (H1 : bpow radix2 (1024 - 53) < bpow radix2 1024) by (apply bpow_lt; lia).
split; apply f64_format_G_lt.
- exact Gm.
- rewrite Rabs_pos_eq; lra.
- apply generic_format_opp. exact Gm.
- rewrite Rabs_Ropp, Rabs_pos_eq; lra.
Qed.

(** A result [MNum y] of [mpfr_round] is an element of [F] other than 0. *)
Lemma mpfr_round_num :
  forall F rnd r y, mpfr_round F rnd r (MNum y) -> y <> 0 /\ F y.
Proof.
intros F [|] r y H; cbn [mpfr_round] in H; destruct H as (H0 & Fy & _);
  split; assumption.
Qed.

(** Rounding in a direction is unique, except for the sign of a zero: an
    infinity means that no element of [F] is on the far side of [r], and
    the elements of [F] that [Rnd_DN_pt] and [Rnd_UP_pt] give are
    unique. *)
Lemma mpfr_round_unique :
  forall F rnd r v v', mpfr_round F rnd r v -> mpfr_round F rnd r v' ->
  v = v' \/ exists s s', v = MZero s /\ v' = MZero s'.
Proof.
intros F [|] r [|[|]|s|y] [|[|]|s'|y'] H H'; cbn [mpfr_round] in H, H';
  try contradiction; try (left; reflexivity);
  try (right; exists s, s'; split; reflexivity);
  repeat match goal with Hc : _ <> 0 /\ _ |- _ => destruct Hc end.
(* [F] and [r] are pattern variables here: after [all:], Rocq rejects a
   hypothesis named in the tactic as an unknown reference. *)
all: first
  [ match goal with
    | Hi : forall g, ?F g -> ?r < g, Hd : Rnd_DN_pt ?F ?r ?a |- _ =>
        destruct Hd as (Fa & Ha & _); pose proof (Hi a Fa); lra
    end
  | match goal with
    | Hi : forall g, ?F g -> g < ?r, Hd : Rnd_UP_pt ?F ?r ?a |- _ =>
        destruct Hd as (Fa & Ha & _); pose proof (Hi a Fa); lra
    end
  | left; f_equal; eapply Rnd_DN_pt_unique; eassumption
  | left; f_equal; eapply Rnd_UP_pt_unique; eassumption
  | exfalso; match goal with
    | Ha : Rnd_DN_pt ?F ?r ?a, Hb : Rnd_DN_pt ?F ?r ?b, Hn : ?b <> 0 |- _ =>
        pose proof (Rnd_DN_pt_unique F r a b Ha Hb); apply Hn; lra
    | Ha : Rnd_UP_pt ?F ?r ?a, Hb : Rnd_UP_pt ?F ?r ?b, Hn : ?b <> 0 |- _ =>
        pose proof (Rnd_UP_pt_unique F r a b Ha Hb); apply Hn; lra
    end ].
Qed.

(** [with_val] is one to one: it keeps the sign of a zero and of an
    infinity, and the nonzero finite floats are determined by their
    reals. *)
Lemma with_val_inj : forall w w', with_val w = with_val w' -> w = w'.
Proof.
intros [s|s| |s m e H] [s'|s'| |s' m' e' H'] E; cbn [with_val] in E;
  try discriminate E.
- injection E as ->. reflexivity.
- injection E as ->. reflexivity.
- reflexivity.
- injection E as E. apply B2R_inj; [reflexivity | reflexivity | exact E].
Qed.

(** Two [f64]s that round [r] in the same direction are equal, or two
    zeros. *)
Lemma round_f64_unique :
  forall rnd r w w', mpfr_round f64_format rnd r (with_val w) ->
  mpfr_round f64_format rnd r (with_val w') ->
  w = w' \/ exists s s', w = B754_zero s /\ w' = B754_zero s'.
Proof.
intros rnd r w w' H H'.
destruct (mpfr_round_unique _ _ _ _ _ H H') as [E | (s & s' & E & E')].
- left. exact (with_val_inj _ _ E).
- right. exists s, s'. split; apply with_val_inj; assumption.
Qed.

(** A real that rounds to a zero [f64] is below [2^-1074], the least
    positive [f64], in magnitude. *)
Lemma round_f64_zero_small :
  forall rnd r s, mpfr_round f64_format rnd r (MZero s) ->
  Rabs r < bpow radix2 (-1074).
Proof.
intros rnd r s H.
assert (He : (-1074 <= -1074 < 1024)%Z) by lia.
destruct (f64_format_bpow (-1074) He) as [Fp Fn].
pose proof (bpow_gt_0 radix2 (-1074)) as Hp.
destruct rnd; cbn [mpfr_round] in H; destruct H as (_ & H0 & Hext).
- (* Toward -inf: [0 <= r], and [2^-1074] is not at or below [r]. *)
  rewrite Rabs_pos_eq by exact H0. apply Rnot_le_lt. intros Hle.
  pose proof (Hext _ Fp Hle). lra.
- (* Toward +inf: [r <= 0], and [-2^-1074] is not at or above [r]. *)
  rewrite Rabs_left1 by exact H0. apply Rnot_le_lt. intros Hle.
  assert (Hr : r <= - bpow radix2 (-1074)) by lra.
  pose proof (Hext _ Fn Hr). lra.
Qed.

(** A zero that rounds [r] to an [f64] rounds it to an MPFR number too:
    [r] is below [2^-1074] in magnitude, and the least positive MPFR
    number at [emin = -1073] is [2^(emin - 1) = 2^-1074]. *)
Lemma round_zero_mpfr :
  forall rnd r s, mpfr_round f64_format rnd r (MZero s) ->
  mpfr_round (mpfr_format (-1073) 1024) rnd r (MZero s).
Proof.
intros rnd r s H.
pose proof (round_f64_zero_small _ _ _ H) as Hs. apply Rabs_lt_inv in Hs.
destruct rnd; cbn [mpfr_round] in *; destruct H as (_ & H0 & _);
  (split; [apply mpfr_format_0|]); (split; [exact H0|]);
  intros g [Hg | (_ & Hb & _)] Hgr; try lra;
  change (-1073 - 1)%Z with (-1074)%Z in Hb.
- (* A positive MPFR number is at least [2^-1074], so above [r]. *)
  destruct (Rle_or_lt g 0) as [Hg | Hg]; [exact Hg|].
  rewrite Rabs_pos_eq in Hb by lra. lra.
- destruct (Rle_or_lt 0 g) as [Hg | Hg]; [exact Hg|].
  rewrite Rabs_left in Hb by exact Hg. lra.
Qed.

(** [ideal_get_d] converts [with_val w] back to [w]. *)
Lemma ideal_get_d_with_val : forall rnd w, ideal_get_d rnd (with_val w) = w.
Proof.
intros rnd [s|s| |s m e H]; try reflexivity.
(* A finite float other than 0: [round_f64] keeps its real, which is in
   [G] and below [2^1024] in magnitude. *)
set (w := B754_finite s m e H).
change (ideal_get_d rnd (with_val w)) with (round_f64 rnd (B2R w)).
destruct (round_f64_exact rnd (B2R w) (generic_format_B2R 53 1024 w)
  (abs_B2R_lt_emax 53 1024 w)) as [Fz Ez].
assert (Hw0 : B2R w <> 0)
  by (unfold w; cbn [B2R]; apply F2R_neq_0; destruct s; discriminate).
apply with_val_inj.
rewrite (with_val_finite _ Fz) by (rewrite Ez; exact Hw0).
rewrite Ez. reflexivity.
Qed.

Lemma ideal_get_d_lift_val : forall rnd r w, ideal_get_d rnd (lift_val rnd r w) = w.
Proof.
intros rnd r w. unfold lift_val. cbv zeta.
destruct (f64_eq_dec (ideal_get_d rnd (round_mpfr (-1073) 1024 rnd r)) w) as [E | _].
- exact E.
- apply ideal_get_d_with_val.
Qed.

Lemma lift_val_correct :
  forall rnd r w, mpfr_round f64_format rnd r (with_val w) ->
  mpfr_round (mpfr_format (-1073) 1024) rnd r (lift_val rnd r w).
Proof.
intros rnd r w Hw. unfold lift_val. cbv zeta.
pose proof (round_mpfr_correct (-1073) 1024 rnd r range_ok_f64) as Hy.
set (y := round_mpfr (-1073) 1024 rnd r) in *.
destruct (f64_eq_dec (ideal_get_d rnd y) w) as [_ | Hne]; [exact Hy|].
(* [ideal_get_d rnd y] rounds [r] to an [f64] too, as [y] rounds it to an
   MPFR number. It is not [w], so both are zeros, and a zero that rounds
   [r] to an [f64] rounds it to an MPFR number. *)
pose proof (mpfr_fn_round (-1073) 1024 (ideal 0 0) rnd r y range_ok_f64
  (ideal_get_d_ok (-1073) 1024 0 0) Hy) as Hy'.
change (mpfr_get_d (ideal 0 0)) with ideal_get_d in Hy'.
destruct (round_f64_unique _ _ _ _ Hy' Hw) as [E | (s & s' & _ & ->)].
- destruct (Hne E).
- cbn [with_val] in *. exact (round_zero_mpfr _ _ _ Hw).
Qed.

(** At an [f64] [w] that is not finite, is a zero or is above [2^-1022]
    in magnitude, [lift_val rnd r w] is [with_val w], whatever [r]. *)
Lemma lift_val_exact :
  forall rnd r w,
  is_finite w = false \/ B2R w = 0 \/ bpow radix2 (-1022) < Rabs (B2R w) ->
  lift_val rnd r w = with_val w.
Proof.
intros rnd r w Hc. unfold lift_val. cbv zeta.
pose proof (round_mpfr_correct (-1073) 1024 rnd r range_ok_f64) as Hy.
set (y := round_mpfr (-1073) 1024 rnd r) in *.
destruct (f64_eq_dec (ideal_get_d rnd y) w) as [E | _]; [|reflexivity].
subst w. clearbody y.
(* [ideal_get_d] converts NaN, the infinities and the zeros to themselves. *)
destruct y as [|s|s|v]; try reflexivity.
cbn [ideal_get_d] in Hc |- *.
destruct (mpfr_round_num _ _ _ _ Hy) as [Hv0 Fv].
pose proof (round_f64_correct rnd v) as Hw.
revert Hc Hw. generalize (round_f64 rnd v) as w. intros w Hc Hw.
(* [w] is finite: [|v|] is at most the largest finite [f64]. *)
assert (Fw : is_finite w = true).
{ destruct w as [t|t| |t mw ew Hw0]; try reflexivity; exfalso.
  - destruct f64_format_max as [Fm Fm'].
    pose proof (mpfr_format_abs_le _ _ _ Fv) as Hm. apply Rabs_le_inv in Hm.
    destruct rnd, t; cbn [with_val mpfr_round] in Hw; try contradiction.
    + pose proof (Hw _ Fm'). lra.
    + pose proof (Hw _ Fm). lra.
  - destruct rnd; exact Hw. }
destruct Hc as [Hc | [Hc | Hc]].
- rewrite Fw in Hc. discriminate Hc.
- (* [w] is not a zero: [|v|] is at least [2^-1074], which is an [f64]. *)
  exfalso.
  destruct (with_val_finite_cases w Fw) as [(s & Ew & _) | (_ & Hne)];
    [|exact (Hne Hc)].
  rewrite Ew in Hw. pose proof (round_f64_zero_small _ _ _ Hw) as Hs.
  destruct Fv as [Hv | (_ & Hb & _)]; [exact (Hv0 Hv)|].
  change (-1073 - 1)%Z with (-1074)%Z in Hb. lra.
- (* [|v|] is at least [2^-1022], or [w] would be between [-2^-1022] and
     [2^-1022], which are [f64]s. So [v], of 53 bits, is an [f64], and it
     rounds to itself. *)
  assert (Hv : bpow radix2 (-1022) <= Rabs v).
  { apply Rnot_lt_le. intros Hlt. apply Rabs_lt_inv in Hlt.
    assert (He : (-1074 <= -1022 < 1024)%Z) by lia.
    destruct (f64_format_bpow (-1022) He) as [Fp Fn].
    pose proof (round_finite_pt _ _ _ _ Fw Hw) as Hpt.
    destruct rnd; cbn [rnd_pt] in Hpt; destruct Hpt as (_ & Hwv & Hext).
    - assert (Hn : - bpow radix2 (-1022) <= v) by lra.
      pose proof (Hext _ Fn Hn).
      assert (Rabs (B2R w) <= bpow radix2 (-1022)) by (apply Rabs_le; lra). lra.
    - assert (Hn : v <= bpow radix2 (-1022)) by lra.
      pose proof (Hext _ Fp Hn).
      assert (Rabs (B2R w) <= bpow radix2 (-1022)) by (apply Rabs_le; lra). lra. }
  destruct Fv as [Hv' | (Fx & _ & Hlt)]; [destruct (Hv0 Hv')|].
  assert (Gv : G v).
  { change (generic_format radix2 (FLT_exp (-1074) 53) v).
    apply generic_format_FLT_FLX; [exact Hv | exact Fx]. }
  pose proof (f64_format_G_lt v Gv Hlt) as F64v.
  destruct (mpfr_round_unique _ _ _ _ _ Hw (mpfr_round_exact _ rnd v Hv0 F64v))
    as [E | (s & s' & _ & E)]; [symmetry; exact E | discriminate E].
Qed.

(** [MNum 1] and [MNum (-1)] convert to the [f64]s 1 and -1. *)
Lemma ideal_get_d_one :
  forall rnd,
  is_finite (ideal_get_d rnd (MNum 1)) = true /\ B2R (ideal_get_d rnd (MNum 1)) = 1.
Proof.
intros rnd. cbn [ideal_get_d]. apply round_f64_exact.
- change 1 with (bpow radix2 0).
  apply generic_format_bpow. unfold SpecFloat.fexp, SpecFloat.emin. lia.
- rewrite Rabs_R1. change 1 with (bpow radix2 0). apply bpow_lt. lia.
Qed.

Lemma ideal_get_d_m_one :
  forall rnd,
  is_finite (ideal_get_d rnd (MNum (-1))) = true /\ B2R (ideal_get_d rnd (MNum (-1))) = -1.
Proof.
intros rnd. cbn [ideal_get_d]. apply round_f64_exact.
- change (-1) with (- bpow radix2 0). apply generic_format_opp.
  apply generic_format_bpow. unfold SpecFloat.fexp, SpecFloat.emin. lia.
- assert (H1 : bpow radix2 0 < bpow radix2 1024) by (apply bpow_lt; lia).
  change (bpow radix2 0) with 1 in H1. rewrite Rabs_left by lra. lra.
Qed.

(** An [f64] that is 1 or -1 rounded is that real. *)
Lemma with_val_round_one :
  forall rnd v w, v = 1 \/ v = -1 ->
  mpfr_round f64_format rnd v (with_val w) -> with_val w = MNum v.
Proof.
intros rnd v w Hv H.
(* [v] is an [f64] other than 0, so it rounds to itself. *)
assert (He : (-1074 <= 0 < 1024)%Z) by lia.
destruct (f64_format_bpow 0 He) as [F1 F1'].
assert (Fv : f64_format v) by (destruct Hv as [-> | ->]; [exact F1 | exact F1']).
assert (Hv0 : v <> 0) by (destruct Hv as [-> | ->]; intros E0; lra).
destruct (mpfr_round_unique _ _ _ _ _ H (mpfr_round_exact _ rnd v Hv0 Fv))
  as [E | (s & s' & _ & E)]; [exact E | discriminate E].
Qed.
