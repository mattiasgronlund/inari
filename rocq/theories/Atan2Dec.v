(** * The decorations of [Interval::atan2_impl]

    What [dec_holds] of [Dec2Set.v] asks of each decoration that
    [Interval::atan2_impl] returns, from where the box [y × x] lies
    ([y] the interval of [y] coordinates, [x] that of [x] coordinates):
    - [trv] ([ad_trv], [ad_empty]): the box contains [(0, 0)], which is
      not in the domain, or is empty;
    - [com] ([ad_com]): the box is nonempty and has no point of the closed
      half-line [y = 0], [x <= 0], so [Ratan2] is continuous at each of
      its points ([Ratan2_cont]);
    - [dac] ([ad_dac]): [y >= 0] with [0] in [y], and [x < 0]: the box is
      in the domain and [Ratan2] is [atan (y / x) + PI] on it, so its
      restriction is continuous ([Ratan2_cont_upper]), but it is not
      continuous relative to the domain at [(0, t)] ([Ratan2_not_cont]);
    - [def] ([ad_def]): [y] contains [0] and reals below it, and [x < 0]:
      the box is in the domain, and the restriction is not continuous at
      [(0, t)], as the box has points just below it
      ([Ratan2_not_cont_in2]). *)

From Stdlib Require Import Reals Lra Classical_Prop.
From Inari Require Import Model Ieee1788 Elementary AtanReal Dec2Set.

Open Scope R_scope.

(** ** Helpers *)

(** A real between two members of an interval is a member, from the
    definition of [mem] (no [valid] needed). *)
Lemma adc_mem_between :
  forall x u v r, mem u x -> mem v x -> u <= r <= v -> mem r x.
Proof.
intros x u v r [Hu _] [_ Hv] Hr. unfold mem. split.
- revert Hu. destruct (opp (fst (rep x))); cbv beta iota; intros Hu;
    try exact Hu; lra.
- revert Hv. destruct (snd (rep x)); cbv beta iota; intros Hv;
    try exact Hv; lra.
Qed.

(** A function continuous at a point is continuous there relative to any
    box, and relative to any domain. *)
Lemma adc_cont_in2 :
  forall f X Y r t, continuity2_pt f r t -> continue_in2 f X Y r t.
Proof.
intros f X Y r t Hc eps Heps. destruct (Hc eps Heps) as (delta & Hd & H).
exists delta. split; [exact Hd|].
intros r' t' _ _. exact (H r' t' I I).
Qed.

Lemma adc_cont_set :
  forall f D r t, continuity2_pt f r t -> continue_in2_set f D r t.
Proof.
intros f D r t Hc eps Heps. destruct (Hc eps Heps) as (delta & Hd & H).
exists delta. split; [exact Hd|].
intros r' t' _. exact (H r' t' I I).
Qed.

(** Continuity relative to a box carries over to a smaller box. *)
Lemma adc_in2_sub :
  forall f (X Y X' Y' : R -> Prop) r t, continue_in2 f X Y r t ->
  (forall r', X' r' -> X r') -> (forall t', Y' t' -> Y t') ->
  continue_in2 f X' Y' r t.
Proof.
intros f X Y X' Y' r t Hc HX HY eps Heps. destruct (Hc eps Heps) as (delta & Hd & H).
exists delta. split; [exact Hd|].
intros r' t' Hr Ht. exact (H r' t' (HX r' Hr) (HY t' Ht)).
Qed.

(** ** The decorations *)

Lemma ad_empty :
  forall y x z, ((forall r, ~ mem r y) \/ (forall t, ~ mem t x)) ->
  dec_holds atan2_dom Ratan2 y x z Trv.
Proof.
intros y x z H (Ny & Nx & _).
destruct Ny as (r & Hr), Nx as (t & Ht).
destruct H as [H|H]; [exact (H r Hr) | exact (H t Ht)].
Qed.

Lemma ad_trv :
  forall y x z, mem 0 y -> mem 0 x -> dec_holds atan2_dom Ratan2 y x z Trv.
Proof.
intros y x z Hy Hx (_ & _ & HD).
(* [(0, 0)] is in the box but not in the domain. *)
destruct (HD 0 0 Hy Hx) as [H|H]; exact (H eq_refl).
Qed.

Lemma ad_com :
  forall y x z, (exists r, mem r y) -> (exists t, mem t x) ->
  (forall r t, mem r y -> mem t x -> r <> 0 \/ 0 < t) ->
  dec_holds atan2_dom Ratan2 y x z Com.
Proof.
intros y x z Ny Nx H. cbn [dec_holds].
assert (HD : forall r t, mem r y -> mem t x -> atan2_dom r t).
{ intros r t Hr Ht. destruct (H r t Hr Ht) as [H0|H0]; [left; exact H0 | right; lra]. }
split.
- split; [exact Ny|]. split; [exact Nx|]. split; [exact HD|].
  intros r t Hr Ht. apply adc_cont_in2, Ratan2_cont. exact (H r t Hr Ht).
- intros r t Hr Ht. apply adc_cont_set, Ratan2_cont. exact (H r t Hr Ht).
Qed.

Lemma ad_dac :
  forall y x z, mem 0 y -> (forall r, mem r y -> 0 <= r) ->
  (exists t, mem t x) -> (forall t, mem t x -> t < 0) ->
  dec_holds atan2_dom Ratan2 y x z Dac.
Proof.
intros y x z H0 Hy Nx Hx. cbn [dec_holds].
split.
- (* The box is inside [r >= 0], [t < 0], where [Ratan2] is continuous. *)
  split; [exists 0; exact H0|]. split; [exact Nx|].
  split; [intros r t _ Ht; right; specialize (Hx t Ht); lra|].
  intros r t Hr Ht.
  apply (adc_in2_sub _ (fun r' => 0 <= r') (fun t' => t' < 0));
    [exact (Ratan2_cont_upper r t (Hy r Hr) (Hx t Ht)) | exact Hy | exact Hx].
- (* It is not continuous relative to the domain at [(0, t)]. *)
  intros Hc. destruct Nx as (t & Ht).
  exact (Ratan2_not_cont t (Hx t Ht) (Hc 0 t H0 Ht)).
Qed.

Lemma ad_def :
  forall y x z, mem 0 y -> (exists r, mem r y /\ r < 0) ->
  (exists t, mem t x) -> (forall t, mem t x -> t < 0) ->
  dec_holds atan2_dom Ratan2 y x z Def.
Proof.
intros y x z H0 (r0 & Hr0 & Hneg) Nx Hx. cbn [dec_holds].
split.
- split; [exists 0; exact H0|]. split; [exact Nx|].
  intros r t _ Ht. right. specialize (Hx t Ht). lra.
- (* [y] has points in [(-eps, 0)] for every [eps > 0], between [r0] and
     [0], so the box has points just below [(0, t)]. *)
  intros (_ & _ & _ & Hc). destruct Nx as (t & Ht).
  apply (Ratan2_not_cont_in2 (fun r => mem r y) (fun t => mem t x) t (Hx t Ht) Ht).
  + intros eps He. exists (Rmax r0 (- eps / 2)).
    split.
    * apply (adc_mem_between y r0 0); [exact Hr0 | exact H0|].
      split; [apply Rmax_l|]. apply Rmax_lub; lra.
    * split; [apply Rlt_le_trans with (- eps / 2); [lra | apply Rmax_r]|].
      apply Rmax_lub_lt; lra.
  + exact (Hc 0 t H0 Ht).
Qed.
