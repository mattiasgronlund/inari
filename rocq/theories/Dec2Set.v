(** * The decorated version of a function of two reals that is not continuous on its domain

    [elem2_set_dec_correct] in [Dom2.v] is for an interval function that
    returns the decoration [trv] or [com], so for a point function that is
    continuous at each point of its domain. [atan2] is not continuous on
    the half-line [y = 0], [x < 0] of its domain, and [Interval::atan2]
    also returns [dac] and [def]. [dec_holds D f x y z e] says what the
    decoration [e] that the interval function returns for the box
    [x × y] claims, as the strongest one: [trv], that [def] does not hold;
    [def], that [def] holds and [dac] does not; [dac], that [dac] holds and
    [f] is not continuous relative to [D] at some point of the box; and
    [com], that [dac] holds and [f] is continuous relative to [D] at each
    point of the box. [elem2_set_dec_strongest] then shows that
    [impl_dec2!] returns the strongest decoration, lowered to those of the
    arguments, for a tightest [z] that is common if it is not empty. *)

From Stdlib Require Import ZArith Reals Lra Lia Classical_Prop.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer DecBinary ElemDec Dom2.

Open Scope R_scope.

Definition dec_holds (D : R -> R -> Prop) (f : R -> R -> R) (x y z : Interval)
    (e : Decoration) : Prop :=
  match e with
  | Ill => False
  | Trv => ~ p2_set D Def f x y z
  | Def => p2_set D Def f x y z /\ ~ p2_set D Dac f x y z
  | Dac =>
      p2_set D Dac f x y z /\
      ~ (forall r t, mem r x -> mem t y -> continue_in2_set f D r t)
  | Com =>
      p2_set D Dac f x y z /\
      (forall r t, mem r x -> mem t y -> continue_in2_set f D r t)
  end.

(** The float [4.0], and the interval [[-4, 4]], whose lanes are [4] and
    [4]. *)
Definition ds_four : f64 := from_bits 0x4010000000000000.

Lemma ds_four_mem : forall r, mem r {| rep := (ds_four, ds_four) |} <-> -4 <= r <= 4.
Proof.
intros r. unfold mem, ds_four. cbn [fst snd rep].
let v := eval vm_compute in (opp (from_bits 0x4010000000000000)) in
change (opp (from_bits 0x4010000000000000)) with v.
let v := eval vm_compute in (from_bits 0x4010000000000000) in
change (from_bits 0x4010000000000000) with v.
unfold B2R, F2R; cbn [Fnum Fexp bpow radix_val radix2 cond_Zopp].
(* The lower lane's significand is [cond_Zopp true _]: normalize it to a
   literal, and compute both bounds, [2^52 * 2^-50]. *)
match goal with |- (IZR ?z * _ <= r <= _ <-> _) =>
  let z' := eval vm_compute in z in change z with z' end.
change (Z.pow_pos 2 50) with 1125899906842624%Z.
assert (E : 4503599627370496 * / 1125899906842624 = 4) by field.
assert (E' : -4503599627370496 * / 1125899906842624 = -4) by field.
rewrite E, E'. split; intros [H1 H2]; split; lra.
Qed.

Lemma ds_four_valid : valid {| rep := (ds_four, ds_four) |}.
Proof.
unfold valid, ds_four. cbn [rep]. right. vm_compute.
split; [reflexivity | split; intros E; discriminate E].
Qed.

(** A tightest interval of a nonempty set of reals between -4 and 4 is
    common. *)
Lemma tightest_common :
  forall S z, is_tightest S z -> (forall s, S s -> -4 <= s <= 4) ->
  Interval.is_empty z = false -> Interval.is_common_interval z = true.
Proof.
intros S z (Hz & _ & Hmin) H4 Hn.
apply (bounded_common z Hz Hn).
(* [z] is inside every valid interval that contains [S], so inside
   [[-4, 4]]. *)
exists 4. intros r Hr.
assert (H : -4 <= r <= 4).
{ apply (proj1 (ds_four_mem r)). apply (Hmin _ ds_four_valid); [|exact Hr].
  intros s Hs. apply (proj2 (ds_four_mem s)). exact (H4 s Hs). }
apply Rabs_le. lra.
Qed.

(** [dec_min] is associative and commutative. *)
Lemma ds_dec_min_assoc :
  forall a b e, dec_min a (dec_min b e) = dec_min e (dec_min a b).
Proof.
intros [] [] []; reflexivity.
Qed.

(** [set_dec] of the tightest interval [z] with the decoration [e] that
    the interval function returns. *)
Theorem elem2_set_dec_strongest :
  forall D f x y z e,
  valid (itv x) -> valid (itv y) -> dec x <> Ill -> dec y <> Ill ->
  is_tightest (image2_set D f (itv x) (itv y)) z ->
  (Interval.is_empty z = false -> Interval.is_common_interval z = true) ->
  dec_holds D f (itv x) (itv y) z e ->
  (e = Com -> dec x = Com -> dec y = Com ->
   bounded (fun r => mem r (itv x)) /\ bounded (fun t => mem t (itv y))) ->
  let w := DecInterval.set_dec z (dec_min (dec x) (dec_min (dec y) e)) in
  is_tightest (image2_set D f (itv x) (itv y)) (itv w) /\
  exists d, strongest2_set D d f (itv x) (itv y) (itv w) /\
    dec w = dec_min d (dec_min (dec x) (dec y)).
Proof.
intros D f x y z e Hx Hy Hdx Hdy Ht Hcz Hh Hb. cbv zeta.
pose proof (proj1 Ht) as Hz.
assert (Hm3 : forall e', e' <> Ill -> dec_min (dec x) (dec_min (dec y) e') <> Ill).
{ intros e' He'. apply dec_min_not_Ill; [exact Hdx|]. apply dec_min_not_Ill; assumption. }
(* A nonempty box in [D] has a point whose image is in [z], so [z] is not
   empty, and then common. *)
assert (Hne : (exists r, mem r (itv x)) -> (exists t, mem t (itv y)) ->
              (forall r t, mem r (itv x) -> mem t (itv y) -> D r t) ->
              Interval.is_empty z = false).
{ intros (r & Hr) (t & Htm) HD.
  apply (mem_not_empty z (f r t) Hz). apply (proj1 (proj2 Ht)).
  exists r, t. split; [exact Hr|]. split; [exact Htm|].
  split; [exact (HD r t Hr Htm) | reflexivity]. }
destruct e; cbn [dec_holds] in Hh.
- destruct Hh.
- (* [e = trv]: not even [def] holds, and [set_dec] keeps [trv] for any
     [z], as in [elem2_set_dec_correct]. *)
  assert (Hm : dec_min (dec x) (dec y) <> Ill) by now apply dec_min_not_Ill.
  rewrite (ed_dec_min_Trv_r _ Hdy), (ed_dec_min_Trv_r _ Hdx).
  destruct (Interval.is_empty z) eqn:Ez0.
  + rewrite (set_dec_empty_any z Trv Ez0 ltac:(discriminate)).
    cbn [itv dec DecInterval.EMPTY]. rewrite <- (valid_empty_eq z Hz Ez0).
    split; [exact Ht|]. exists Trv.
    split; [apply strongest2_set_Trv; exact Hh|].
    symmetry. now apply dec_min_Trv_l.
  + assert (Hc0 : Trv = Com -> Interval.is_common_interval z = true)
      by (intros E; discriminate E).
    rewrite (set_dec_keep z Trv Ez0 ltac:(discriminate) Hc0).
    cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|]. exists Trv.
    split; [apply strongest2_set_Trv; exact Hh|].
    symmetry. now apply dec_min_Trv_l.
- (* [e = def]: [dac] does not hold, nor [com], which implies it. *)
  destruct Hh as (Hdef & Nd).
  destruct Hdef as (Nx & Ny & HD).
  pose proof (Hne Nx Ny HD) as Ez0.
  rewrite (set_dec_keep z _ Ez0 (Hm3 Def ltac:(discriminate)) (fun _ => Hcz Ez0)).
  cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
  exists Def. split; [|apply ds_dec_min_assoc].
  split; [split; [exact Nx|]; split; [exact Ny | exact HD]|].
  intros [] He; cbn [discriminant]; try lia; exfalso; apply Nd.
  + exact He.
  + destruct He as (Hx' & Hy' & HD' & _ & _ & Hc & _).
    split; [exact Hx'|]. split; [exact Hy'|]. split; [exact HD'|].
    intros r t Hr Htm. exact (d2_continue_in2_sub f D _ _ r t (Hc r t Hr Htm) HD').
- (* [e = dac]: [com] does not hold. *)
  destruct Hh as (Hdac & Nc).
  pose proof Hdac as (Nx & Ny & HD & _).
  pose proof (Hne Nx Ny HD) as Ez0.
  rewrite (set_dec_keep z _ Ez0 (Hm3 Dac ltac:(discriminate)) (fun _ => Hcz Ez0)).
  cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
  exists Dac. split; [|apply ds_dec_min_assoc].
  apply strongest2_set_Dac; [exact Hdac|].
  intros (_ & _ & _ & _ & _ & Hc & _). exact (Nc Hc).
- (* [e = com]: [com] holds if [x] and [y] are [com], as the box is then
     bounded and [z] is common; otherwise the minimum of their
     decorations is below [com], and [d] is whichever of [com] and [dac]
     holds. *)
  destruct Hh as (Hdac & Hc).
  pose proof Hdac as (Nx & Ny & HD & _).
  pose proof (Hne Nx Ny HD) as Ez0.
  rewrite (set_dec_keep z _ Ez0 (Hm3 Com ltac:(discriminate)) (fun _ => Hcz Ez0)).
  cbn [itv dec DecInterval.new_unchecked]. split; [exact Ht|].
  rewrite (ds_dec_min_assoc (dec x) (dec y) Com), dec_min_Com_l.
  destruct (classic (p2_set D Com f (itv x) (itv y) z)) as [Pc|Pc].
  + exists Com.
    split; [now apply strongest2_set_Com | symmetry; apply dec_min_Com_l].
  + exists Dac. split; [now apply strongest2_set_Dac|].
    symmetry. apply dec_min_Dac_l. intros E. apply Pc.
    destruct (dec_min_Com _ _ E) as (Edx & Edy).
    destruct (Hb eq_refl Edx Edy) as (Bx & By).
    split; [exact Nx|]. split; [exact Ny|]. split; [exact HD|].
    split; [exact Bx|]. split; [exact By|]. split; [exact Hc|].
    exact (common_bounded z (Hcz Ez0)).
Qed.
