(** * Ziv's strategy rounded to nearest

    [Dyadic.to_f64_near] rounds a dyadic number to the nearest [f64],
    ties to even, as [near_round] says, and gives +0 for a zero
    ([DyConvNear.to_f64_near_correct]). Where a rounding test of
    [Dyadic.ziv_near] passes, both bounds of an enclosure have the same
    bits once rounded,
    so that every number between them rounds to that [f64], a zero
    included, whose sign the bits fix. [ziv_near_strict] is
    [Dyadic.ziv_near] without its last step at the cap, so it returns
    only where a test passes, and there it returns the rounding to
    nearest ([ziv_near_strict_correct]), as [Dyadic.ziv_near] does
    ([ziv_near_strict_ziv]). At the cap, where no test passes,
    [Dyadic.ziv_near] returns the rounding to nearest of a bound of the
    enclosure at 64 limbs ([ziv_near_cap_round]). [near_post z post] says
    that the driver [z] gives a result with the property [post], as
    [DyDriver.driver_post] does for the directed one. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs IdealGetD DyRound DyConv DyOps OfPointCore DyDriver
  NearF64 NearCells DyConvNear.
From Inari Require RoundUpExact Encoding.

Open Scope Z_scope.

(** [Dyadic.ziv_near] without its last step at the cap: the rounding test
    at the levels of [Dyadic.ziv_near] and at 64 limbs, with [None] where
    none passes or an evaluation panics. *)
Definition ziv_near_strict (ev : nat -> option Dyadic.encl) (start : nat) : option f64 :=
  let* r := Dyadic.ziv_near_levels ev start (1 :: 2 :: 4 :: 8 :: 16 :: 32 :: 64 :: nil)%nat in r.

(** The driver [z] gives a result with the property [post] of every real
    number that each level of [ev] encloses. *)
Definition near_post (z : (nat -> option Dyadic.encl) -> nat -> option f64)
    (post : R -> f64 -> Prop) : Prop :=
  forall ev start r v,
  (forall n a, level_ok n -> ev n = Some a -> encl_ok n a /\ encl_has a r) ->
  z ev start = Some v -> post r v.

(** Every number between two numbers that round to nearest to the same
    [f64] rounds to it: the rounding is monotone, a number at or above
    [2^1024 - 2^970] in magnitude between two such numbers of one sign has
    their sign, and a nonzero number between them has the sign of [lo]
    if negative and of [hi] if positive. *)
Local Lemma near_between :
  forall lo hi r v,
  (lo <= r <= hi)%R -> near_round lo v -> near_round hi v -> near_round r v.
Proof.
  intros lo hi r v Hr. unfold near_round.
  set (T := (bpow radix2 1024 - bpow radix2 970)%R).
  destruct (Rle_dec T (Rabs lo)) as [Hl|Hl]; destruct (Rle_dec T (Rabs hi)) as [Hh|Hh];
    destruct (Rle_dec T (Rabs r)) as [Hrr|Hrr]; intros E1 E2.
  - (* Both bounds round to infinities, which are one, so of one sign. *)
    rewrite E1 in E2 |- *. injection E2 as E2. revert E2.
    destruct (Rlt_bool_spec lo 0), (Rlt_bool_spec hi 0), (Rlt_bool_spec r 0); intros E2;
      try reflexivity; try discriminate E2; lra.
  - exfalso. rewrite E1 in E2. injection E2 as E2. revert E2 Hl Hh Hrr. unfold Rabs.
    destruct (Rlt_bool_spec lo 0), (Rlt_bool_spec hi 0); intros E2; try discriminate E2;
      destruct (Rcase_abs lo), (Rcase_abs hi), (Rcase_abs r); intros; lra.
  - rewrite E1 in E2. destruct E2 as (F & _). discriminate F.
  - rewrite E1 in E2. destruct E2 as (F & _). discriminate F.
  - rewrite E2 in E1. destruct E1 as (F & _). discriminate F.
  - rewrite E2 in E1. destruct E1 as (F & _). discriminate F.
  - exfalso. revert Hl Hh Hrr. unfold Rabs.
    destruct (Rcase_abs lo), (Rcase_abs hi), (Rcase_abs r); intros; lra.
  - destruct E1 as (F & E1 & S1). destruct E2 as (_ & E2 & S2).
    split; [exact F | split].
    + (* [RN lo <= RN r <= RN hi] by monotony, and both ends are [v]. *)
      apply Rle_antisym.
      * rewrite E1. apply (round_le radix2 (FLT_exp (-1074) 53) ZnearestE). lra.
      * rewrite E2. apply (round_le radix2 (FLT_exp (-1074) 53) ZnearestE). lra.
    + intros Hr0 Hv0. destruct (Rtotal_order r 0) as [Hn|[He|Hp]].
      * rewrite (S1 (Rlt_not_eq lo 0 ltac:(lra)) Hv0).
        rewrite !Rlt_bool_true by lra. reflexivity.
      * contradiction.
      * rewrite (S2 (Rgt_not_eq hi 0 ltac:(lra)) Hv0).
        rewrite !Rlt_bool_false by lra. reflexivity.
Qed.

(** The level of the levels list that passes. *)
Local Lemma ziv_near_levels_some :
  forall ev start levels v,
  Dyadic.ziv_near_levels ev start levels = Some (Some v) ->
  exists n, In n levels /\ Dyadic.ziv_near_at ev n = Some (Some v).
Proof.
  intros ev start levels v. induction levels as [|n ls IH]; cbn [Dyadic.ziv_near_levels].
  - discriminate.
  - destruct (start <=? n)%nat.
    + destruct (Dyadic.ziv_near_at ev n) as [[x|]|] eqn:E.
      * intros H. injection H as <-. exists n. split; [left; reflexivity | exact E].
      * intros H. destruct (IH H) as (m & Hm & Em). exists m. split; [right; exact Hm | exact Em].
      * discriminate.
    + intros H. destruct (IH H) as (m & Hm & Em). exists m. split; [right; exact Hm | exact Em].
Qed.

(** A level that passes, in a list of levels of 1 to 64 limbs, gives the
    rounding to nearest: both bounds round to the same bits, so to the
    same [f64], and every number between them rounds to it. *)
Local Lemma ziv_near_levels_correct :
  forall ev start levels r v,
  (forall n, In n levels -> level_ok n) ->
  (forall n a, level_ok n -> ev n = Some a -> encl_ok n a /\ encl_has a r) ->
  Dyadic.ziv_near_levels ev start levels = Some (Some v) -> near_round r v.
Proof.
  intros ev start levels r v Hl Hev L.
  destruct (ziv_near_levels_some _ _ _ _ L) as (n & Hin & E).
  pose proof (Hl n Hin) as Hn.
  unfold Dyadic.ziv_near_at, Dyadic.round_bounds_near in E.
  destruct (ev n) as [x|] eqn:Ex; [|discriminate]. cbv beta iota in E.
  destruct (Hev n x Hn Ex) as ((Hlo & Hhi & _) & Hr).
  destruct (to_f64_near_correct n (Dyadic.en_lo x) Hn Hlo) as (v1 & E1 & R1 & _).
  destruct (to_f64_near_correct n (Dyadic.en_hi x) Hn Hhi) as (v2 & E2 & R2 & _).
  rewrite E1, E2 in E. cbv beta iota in E.
  destruct (Z.eqb_spec (to_bits v1) (to_bits v2)) as [Q|]; [|discriminate].
  injection E as <-.
  assert (v1 = v2) as <-.
  { rewrite <- (Encoding.from_to_bits v1), <- (Encoding.from_to_bits v2), Q. reflexivity. }
  exact (near_between _ _ _ _ Hr R1 R2).
Qed.

Theorem ziv_near_strict_correct : near_post ziv_near_strict near_round.
Proof.
  intros ev start r v Hev Hz. unfold ziv_near_strict in Hz.
  destruct (Dyadic.ziv_near_levels ev start _) as [o|] eqn:L; [|discriminate Hz]. subst o.
  refine (ziv_near_levels_correct ev start _ r v _ Hev L).
  intros n Hin. unfold level_ok. cbn [In] in Hin.
  repeat (destruct Hin as [<-|Hin]; [lia|]). destruct Hin.
Qed.

(** Where one of the levels [ls] and then 64 limbs passes, the levels
    [ls] and then [Dyadic.ziv_near_cap] return the same value: a test
    that passes at 64 limbs makes [Dyadic.ziv_near_cap] return [lo], as
    [Dyadic.ziv_near_at] does. *)
Local Lemma ziv_near_levels_cap :
  forall ev start ls v,
  Dyadic.ziv_near_levels ev start (ls ++ 64 :: nil)%nat = Some (Some v) ->
  (let* r := Dyadic.ziv_near_levels ev start ls in
   match r with Some x => Some x | None => Dyadic.ziv_near_cap ev end) = Some v.
Proof.
  intros ev start ls v. induction ls as [|n ls IH]; cbn [Dyadic.ziv_near_levels app].
  - destruct (start <=? 64)%nat; [|discriminate].
    unfold Dyadic.ziv_near_at, Dyadic.ziv_near_cap.
    destruct (Dyadic.round_bounds_near ev 64) as [[lo hi]|]; cbv beta iota; [|discriminate].
    destruct (to_bits lo =? to_bits hi); cbv beta iota; [|discriminate].
    intros H. injection H as ->. reflexivity.
  - destruct (start <=? n)%nat; [|exact IH].
    destruct (Dyadic.ziv_near_at ev n) as [[x|]|]; cbv beta iota; [| exact IH | discriminate].
    intros H. injection H as ->. reflexivity.
Qed.

(** Where [ziv_near_strict] returns, [Dyadic.ziv_near] returns the same. *)
Lemma ziv_near_strict_ziv :
  forall ev start v, ziv_near_strict ev start = Some v -> Dyadic.ziv_near ev start = Some v.
Proof.
  intros ev start v Hz. unfold ziv_near_strict in Hz. unfold Dyadic.ziv_near.
  destruct (Dyadic.ziv_near_levels ev start _) as [o|] eqn:L; [|discriminate Hz]. subst o.
  exact (ziv_near_levels_cap ev start (1 :: 2 :: 4 :: 8 :: 16 :: 32 :: nil)%nat v L).
Qed.

Theorem ziv_near_cap_round :
  forall ev v,
  (forall a, ev 64%nat = Some a -> encl_ok 64 a) ->
  Dyadic.ziv_near_cap ev = Some v ->
  exists a, ev 64%nat = Some a /\ (near_round (lo_R a) v \/ near_round (hi_R a) v).
Proof.
  intros ev v Hev Hz. unfold Dyadic.ziv_near_cap, Dyadic.round_bounds_near in Hz.
  destruct (ev 64%nat) as [a|] eqn:Ea; [|discriminate Hz]. cbv beta iota in Hz.
  (* The destruct rewrote [ev 64] in [Hev] too. *)
  destruct (Hev a eq_refl) as (Hlo & Hhi & _).
  assert (H64 : level_ok 64) by (unfold level_ok; lia).
  destruct (to_f64_near_correct 64 (Dyadic.en_lo a) H64 Hlo) as (v1 & E1 & R1 & _).
  destruct (to_f64_near_correct 64 (Dyadic.en_hi a) H64 Hhi) as (v2 & E2 & R2 & _).
  rewrite E1, E2 in Hz. cbv beta iota in Hz.
  exists a. split; [reflexivity|].
  (* [Dyadic.ziv_near_cap] returns one of the two roundings. *)
  destruct ((to_bits v1 =? to_bits v2) || (Z.land (to_bits v1) 1 =? 0));
    injection Hz as <-; [left | right]; assumption.
Qed.
