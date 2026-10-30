(** * The set of two-output division and its components

    [mul_rev x y] in [Ieee1788.v] is the set of reals [z] with [t * z] in
    [y] for some [t] in [x]. Its elements with [t > 0] are the quotients
    [quot] of [DivTight.v] of the reals of [y] ([Up]) by the reals of [x]
    above 0 ([Qp]), as [z = (t * z) / t], and those with [t < 0] the
    quotients of the negated reals of [y] ([Um]) by the negated reals of
    [x] above 0 ([Qn]), as [z = (-(t * z)) / (-t)]. [t = 0] gives every
    real if 0 is in [x] and in [y], and none otherwise ([mul_rev_split]).

    A set of quotients of a convex set by a convex set of reals above 0 is
    convex ([quot_convex]). So if the reals of [x] are all at least 0 or
    all at most 0, [mul_rev x y] is convex ([mul_rev_convex]), and if 0 is
    not in [x] or not in [y], it is the image of [y × x] under [/]
    ([mul_rev_div]).

    [two_output_empty], [two_output_one] and [two_output_two] give the three
    forms of [two_output]: for an empty set, for a nonempty convex set,
    which is its only component ([component_self]), and for the union of
    two nonempty convex sets with a real between them that is not in the
    union, which are its two components. [mul_rev_one_component] is the
    table in the doc comment of [Interval::mul_rev_to_pair]: if [x] and [y]
    are nonempty and 0 is in [y] or not in [x], [mul_rev x y] has one
    component. *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer DecBinary AddSub DivTight DivSets.

Open Scope R_scope.

(** ** Components *)

(** A nonempty convex set is its only component. *)
Lemma component_self :
  forall s, (exists r, s r) -> convex s ->
  component s s /\ forall k', component s k' -> forall r, k' r <-> s r.
Proof.
intros s Hne Hc. split.
- split; [exact Hne | split; [exact Hc | split; [intros r Hr; exact Hr |]]].
  intros k' _ _ Hk' r Hr. exact (Hk' r Hr).
- (* [s] is a convex subset of [s] that contains [k'], so the maximality
     of [k'] puts [s] inside [k']. *)
  intros k' (_ & _ & Hk' & Hmax) r. split; [exact (Hk' r) |].
  exact (Hmax s Hc Hk' (fun r Hr => Hr) r).
Qed.

Lemma two_output_empty :
  forall s, (forall r, ~ s r) -> two_output s Interval.EMPTY Interval.EMPTY.
Proof.
intros s Hs. unfold two_output. left.
split; [exact Hs | split; reflexivity].
Qed.

Lemma two_output_one :
  forall s u, (exists r, s r) -> convex s -> is_tightest s u ->
  two_output s u Interval.EMPTY.
Proof.
intros s u Hne Hc Hu. unfold two_output. right. left.
destruct (component_self s Hne Hc) as [Hk Hall].
exists s. split; [exact Hk | split; [exact Hall | split; [exact Hu | reflexivity]]].
Qed.

(** [s] is the union of the nonempty convex sets [k1] and [k2], and [g],
    which is not in [s], is above every element of [k1] and below every
    element of [k2]. *)
Lemma two_output_two :
  forall s k1 k2 g u v,
  (forall r, s r <-> k1 r \/ k2 r) ->
  (exists r, k1 r) -> (exists r, k2 r) -> convex k1 -> convex k2 ->
  ~ s g -> (forall r, k1 r -> r < g) -> (forall r, k2 r -> g < r) ->
  is_tightest k1 u -> is_tightest k2 v ->
  two_output s u v.
Proof.
intros s k1 k2 g u v Hs [r1 Hr1] [r2 Hr2] Hc1 Hc2 Hg H1 H2 Hu Hv.
assert (Hk1 : forall r, k1 r -> s r) by (intros r Hr; apply Hs; left; exact Hr).
assert (Hk2 : forall r, k2 r -> s r) by (intros r Hr; apply Hs; right; exact Hr).
(* A convex subset of [s] with an element in [k1] is inside [k1], and one
   with an element in [k2] is inside [k2]: otherwise it would hold [g]. *)
assert (Hin1 : forall k, convex k -> (forall r, k r -> s r) ->
  forall a, k a -> k1 a -> forall r, k r -> k1 r).
{ intros k Hc Hks a Ha Ha1 r Hr.
  destruct (proj1 (Hs r) (Hks r Hr)) as [Hr' | Hr']; [exact Hr' |].
  exfalso. apply Hg, Hks, (Hc a r g Ha Hr).
  split; apply Rlt_le; [apply H1, Ha1 | apply H2, Hr']. }
assert (Hin2 : forall k, convex k -> (forall r, k r -> s r) ->
  forall a, k a -> k2 a -> forall r, k r -> k2 r).
{ intros k Hc Hks a Ha Ha2 r Hr.
  destruct (proj1 (Hs r) (Hks r Hr)) as [Hr' | Hr']; [| exact Hr'].
  exfalso. apply Hg, Hks, (Hc r a g Hr Ha).
  split; apply Rlt_le; [apply H1, Hr' | apply H2, Ha2]. }
assert (C1 : component s k1).
{ split; [exists r1; exact Hr1 | split; [exact Hc1 | split; [exact Hk1 |]]].
  intros k' Hc' H1' Hs'. exact (Hin1 k' Hc' Hs' r1 (H1' r1 Hr1) Hr1). }
assert (C2 : component s k2).
{ split; [exists r2; exact Hr2 | split; [exact Hc2 | split; [exact Hk2 |]]].
  intros k' Hc' H2' Hs'. exact (Hin2 k' Hc' Hs' r2 (H2' r2 Hr2) Hr2). }
unfold two_output. right. right. exists k1, k2.
split; [exact C1 | split; [exact C2 | split; [| split; [| split; [exact Hu | exact Hv]]]]].
- intros r t Hr Ht. apply (Rlt_trans _ g); [apply H1, Hr | apply H2, Ht].
- (* A component [k'] has an element [r0] in [k1] or in [k2]; it is then
     inside that set, which is a convex subset of [s] that contains it, so
     the maximality of [k'] gives the converse. *)
  intros k' ([r0 Hr0] & Hc' & Hs' & Hmax).
  destruct (proj1 (Hs r0) (Hs' r0 Hr0)) as [H0 | H0].
  + left. intros r. pose proof (Hin1 k' Hc' Hs' r0 Hr0 H0) as Hsub.
    split; [exact (Hsub r) | exact (Hmax k1 Hc1 Hsub Hk1 r)].
  + right. intros r. pose proof (Hin2 k' Hc' Hs' r0 Hr0 H0) as Hsub.
    split; [exact (Hsub r) | exact (Hmax k2 Hc2 Hsub Hk2 r)].
Qed.

(** ** Convex sets *)

(** A weighted mean of two elements of a convex set is in the set. *)
Lemma convex_comb :
  forall S, convex S -> forall a b mu, S a -> S b -> 0 <= mu <= 1 ->
  S (mu * a + (1 - mu) * b).
Proof.
intros S HS a b mu Ha Hb Hmu.
destruct (Rle_lt_dec a b) as [L | L].
- apply (HS a b); [exact Ha | exact Hb | split; nra].
- apply (HS b a); [exact Hb | exact Ha | split; nra].
Qed.

(** [mu = B / (A + B)] *)
Lemma mix_weight :
  forall A B, 0 < A -> 0 < B -> exists mu, 0 <= mu <= 1 /\ mu * A = (1 - mu) * B.
Proof.
intros A B HA HB. exists (B / (A + B)).
assert (E : 1 - B / (A + B) = A / (A + B)) by (field; lra).
assert (P : 0 < A / (A + B)) by (apply Rdiv_lt_0_compat; lra).
assert (P' : 0 < B / (A + B)) by (apply Rdiv_lt_0_compat; lra).
split; [lra |]. rewrite E. field. lra.
Qed.

Lemma mem_convex : forall x, valid x -> convex (fun r => mem r x).
Proof.
intros x Hx u v r Hu Hv Hr. exact (mem_between x u v r Hx Hu Hv Hr).
Qed.

Lemma Up_convex : forall x, valid x -> convex (Up x).
Proof.
intros x Hx. exact (mem_convex x Hx).
Qed.

Lemma Um_convex : forall x, valid x -> convex (Um x).
Proof.
intros x Hx u v r Hu Hv Hr. unfold Um in *.
apply (mem_between x (- v) (- u) (- r) Hx Hv Hu). lra.
Qed.

Lemma Qp_convex : forall x, valid x -> convex (Qp x).
Proof.
intros x Hx u v r [Hu Hu0] [Hv Hv0] Hr.
split; [exact (mem_between x u v r Hx Hu Hv Hr) | lra].
Qed.

Lemma Qn_convex : forall x, valid x -> convex (Qn x).
Proof.
intros x Hx u v r [Hu Hu0] [Hv Hv0] Hr.
split; [apply (mem_between x (- v) (- u) (- r) Hx Hv Hu); lra | lra].
Qed.

(** For [z1 = u1 / q1 <= z <= z2 = u2 / q2], [z = u / q] with
    [u = mu * u1 + (1 - mu) * u2] and [q = mu * q1 + (1 - mu) * q2], where
    [mu = q2 * (z2 - z) / (q1 * (z - z1) + q2 * (z2 - z))] is in [[0, 1]]. *)
Lemma quot_convex :
  forall U Q, convex U -> convex Q -> (forall q, Q q -> 0 < q) ->
  convex (quot U Q).
Proof.
intros U Q HU HQ HQp z1 z2 z (u1 & q1 & Hu1 & Hq1 & E1)
  (u2 & q2 & Hu2 & Hq2 & E2) [Hz1 Hz2].
destruct (Rle_lt_or_eq_dec _ _ Hz1) as [L1 | H1];
  [| exists u1, q1; split; [exact Hu1 | split; [exact Hq1 | rewrite <- H1; exact E1]]].
destruct (Rle_lt_or_eq_dec _ _ Hz2) as [L2 | H2];
  [| exists u2, q2; split; [exact Hu2 | split; [exact Hq2 | rewrite H2; exact E2]]].
pose proof (HQp q1 Hq1) as P1. pose proof (HQp q2 Hq2) as P2.
assert (F1 : u1 = z1 * q1) by (rewrite E1; field; lra).
assert (F2 : u2 = z2 * q2) by (rewrite E2; field; lra).
assert (HA : 0 < q1 * (z - z1)) by (apply Rmult_lt_0_compat; lra).
assert (HB : 0 < q2 * (z2 - z)) by (apply Rmult_lt_0_compat; lra).
destruct (mix_weight _ _ HA HB) as (mu & Hmu & Emu).
exists (mu * u1 + (1 - mu) * u2), (mu * q1 + (1 - mu) * q2).
assert (Hq : Q (mu * q1 + (1 - mu) * q2)) by exact (convex_comb Q HQ q1 q2 mu Hq1 Hq2 Hmu).
pose proof (HQp _ Hq) as Pq.
split; [exact (convex_comb U HU u1 u2 mu Hu1 Hu2 Hmu) | split; [exact Hq |]].
(* [u - z * q = mu * q1 * (z1 - z) + (1 - mu) * q2 * (z2 - z)], which is 0
   by the choice of [mu]. *)
assert (E : mu * u1 + (1 - mu) * u2 = z * (mu * q1 + (1 - mu) * q2)).
{ rewrite F1, F2. lra. }
rewrite E. field. lra.
Qed.

(** ** Signs and negations of quotients *)

Lemma quot_neg :
  forall U Q s, (forall u, U u -> u < 0) -> (forall q, Q q -> 0 < q) ->
  quot U Q s -> s < 0.
Proof.
intros U Q s HU HQ (u & q & Hu & Hq & ->).
pose proof (HU u Hu) as Pu. pose proof (Rinv_0_lt_compat q (HQ q Hq)) as Pq.
unfold Rdiv. nra.
Qed.

Lemma quot_pos :
  forall U Q s, (forall u, U u -> 0 < u) -> (forall q, Q q -> 0 < q) ->
  quot U Q s -> 0 < s.
Proof.
intros U Q s HU HQ (u & q & Hu & Hq & ->).
apply Rdiv_lt_0_compat; [exact (HU u Hu) | exact (HQ q Hq)].
Qed.

(** [-(u / q) = (-u) / q]. *)
Lemma quot_Up_opp :
  forall y Q s, quot (Up y) Q (- s) <-> quot (Um y) Q s.
Proof.
intros y Q s. unfold quot, Up, Um. split.
- intros (u & q & Hu & Hq & E). exists (- u), q.
  split; [rewrite Ropp_involutive; exact Hu | split; [exact Hq |]].
  rewrite <- (Ropp_involutive s), E. unfold Rdiv. ring.
- intros (u & q & Hu & Hq & E). exists (- u), q.
  split; [exact Hu | split; [exact Hq |]].
  rewrite E. unfold Rdiv. ring.
Qed.

Lemma quot_Um_opp :
  forall y Q s, quot (Um y) Q (- s) <-> quot (Up y) Q s.
Proof.
intros y Q s. unfold quot, Up, Um. split.
- intros (u & q & Hu & Hq & E). exists (- u), q.
  split; [exact Hu | split; [exact Hq |]].
  rewrite <- (Ropp_involutive s), E. unfold Rdiv. ring.
- intros (u & q & Hu & Hq & E). exists (- u), q.
  split; [rewrite Ropp_involutive; exact Hu | split; [exact Hq |]].
  rewrite E. unfold Rdiv. ring.
Qed.

(** ** The set of two-output division *)

Lemma mul_rev_split :
  forall x y z, mul_rev x y z <->
    (mem 0 x /\ mem 0 y) \/ quot (Up y) (Qp x) z \/ quot (Um y) (Qn x) z.
Proof.
intros x y z. unfold mul_rev, quot, Up, Um, Qp, Qn. split.
- intros (t & Ht & Htz). destruct (Rtotal_order t 0) as [N | [-> | P]].
  + (* [z = (-(t * z)) / (-t)] *)
    right. right. exists (- (t * z)), (- t).
    split; [rewrite Ropp_involutive; exact Htz |].
    split; [split; [rewrite Ropp_involutive; exact Ht | lra] |]. field. lra.
  + left. rewrite Rmult_0_l in Htz. split; [exact Ht | exact Htz].
  + (* [z = (t * z) / t] *)
    right. left. exists (t * z), t.
    split; [exact Htz | split; [split; [exact Ht | lra] |]]. field. lra.
- intros [[H0x H0y] | [(u & q & Hu & [Hq Hq0] & E) | (u & q & Hu & [Hq Hq0] & E)]].
  + exists 0. rewrite Rmult_0_l. split; [exact H0x | exact H0y].
  + exists q. split; [exact Hq |].
    replace (q * z) with u by (rewrite E; field; lra). exact Hu.
  + exists (- q). split; [exact Hq |].
    replace (- q * z) with (- u) by (rewrite E; field; lra). exact Hu.
Qed.

(** 0 is not in [mul_rev x y] if it is not in [y], as [t * 0 = 0]. *)
Lemma mul_rev_no0 : forall x y, ~ mem 0 y -> ~ mul_rev x y 0.
Proof.
intros x y H (t & _ & Ht). rewrite Rmult_0_r in Ht. exact (H Ht).
Qed.

(** If 0 is not in [x] or not in [y], [t * z] in [y] for [t] in [x]
    implies [t <> 0], so [z = r / t] for [r = t * z] in [y]. *)
Lemma mul_rev_div :
  forall x y, ~ mem 0 x \/ ~ mem 0 y ->
  forall z, mul_rev x y z <-> image2_dom div_dom1 div_dom2 Rdiv y x z.
Proof.
intros x y H z. unfold mul_rev, image2_dom, div_dom1, div_dom2. split.
- intros (t & Ht & Htz).
  assert (N : t <> 0).
  { intros ->. rewrite Rmult_0_l in Htz. destruct H as [H | H]; contradiction. }
  exists (t * z), t. split; [exact Htz | split; [exact Ht | split; [exact I | split; [exact N |]]]].
  field. exact N.
- intros (r & t & Hr & Ht & _ & N & E). exists t. split; [exact Ht |].
  replace (t * z) with r by (rewrite E; field; exact N). exact Hr.
Qed.

(** [mul_rev x y] is convex if 0 is in [x] and in [y] whenever [x] has
    reals above 0 and below 0: elements of the set from [Qp x] and from
    [Qn x] then make it all of R. *)
Lemma mul_rev_convex_if :
  forall x y, valid x -> valid y ->
  ((exists q, Qp x q) -> (exists q, Qn x q) -> mem 0 x /\ mem 0 y) ->
  convex (mul_rev x y).
Proof.
intros x y Hx Hy H0 u v r Hu Hv Hr. apply mul_rev_split.
destruct (proj1 (mul_rev_split x y u) Hu) as [Z | [Hu' | Hu']]; [left; exact Z | |];
  (destruct (proj1 (mul_rev_split x y v) Hv) as [Z | [Hv' | Hv']]; [left; exact Z | |]).
- right. left.
  exact (quot_convex _ _ (Up_convex y Hy) (Qp_convex x Hx) (fun q Hq => proj2 Hq) u v r Hu' Hv' Hr).
- left. destruct Hu' as (a & q1 & _ & Hq1 & _). destruct Hv' as (b & q2 & _ & Hq2 & _).
  apply H0; [exists q1; exact Hq1 | exists q2; exact Hq2].
- left. destruct Hu' as (a & q1 & _ & Hq1 & _). destruct Hv' as (b & q2 & _ & Hq2 & _).
  apply H0; [exists q2; exact Hq2 | exists q1; exact Hq1].
- right. right.
  exact (quot_convex _ _ (Um_convex y Hy) (Qn_convex x Hx) (fun q Hq => proj2 Hq) u v r Hu' Hv' Hr).
Qed.

(** If the reals of [x] are all at least 0, or all at most 0, [mul_rev x y]
    is all of R if 0 is in [x] and in [y], and otherwise
    [quot (Up y) (Qp x)] or [quot (Um y) (Qn x)], as the other is empty. *)
Lemma mul_rev_convex :
  forall x y, valid x -> valid y ->
  (forall t, mem t x -> 0 <= t) \/ (forall t, mem t x -> t <= 0) ->
  convex (mul_rev x y).
Proof.
intros x y Hx Hy Hs. apply mul_rev_convex_if; [exact Hx | exact Hy |].
(* One of [Qp x] and [Qn x] is empty. *)
intros [q1 [Hq1 P1]] [q2 [Hq2 P2]]. exfalso.
destruct Hs as [Hs | Hs]; [specialize (Hs _ Hq2) | specialize (Hs _ Hq1)]; lra.
Qed.

(** The table in the doc comment of [Interval::mul_rev_to_pair]: for
    nonempty [x] and [y], [mul_rev x y] has one component if 0 is in [y],
    or not in [x]. *)
Theorem mul_rev_one_component :
  forall x y, valid x -> valid y -> (exists r, mem r x) -> (exists r, mem r y) ->
  mem 0 y \/ ~ mem 0 x ->
  exists k, component (mul_rev x y) k /\
    forall k', component (mul_rev x y) k' -> forall r, k' r <-> k r.
Proof.
intros x y Hx Hy [t Ht] [r Hr] H0.
assert (Hne : exists z, mul_rev x y z).
{ destruct (Req_dec t 0) as [-> | N].
  - (* 0 is in [x], so in [y], and [0 * z] is in [y] for every [z]. *)
    exists 0, 0. rewrite Rmult_0_r. split; [exact Ht |].
    destruct H0 as [H0 | H0]; [exact H0 | contradiction].
  - (* [t * (r / t) = r] *)
    exists (r / t), t. split; [exact Ht |].
    replace (t * (r / t)) with r by (field; exact N). exact Hr. }
assert (Hc : convex (mul_rev x y)).
{ apply mul_rev_convex_if; [exact Hx | exact Hy |].
  (* [x] holds [-q2 < 0 < q1], so it holds 0, and then so does [y]. *)
  intros [q1 [Hq1 P1]] [q2 [Hq2 P2]].
  assert (Z : mem 0 x) by (apply (mem_between x (- q2) q1 0 Hx Hq2 Hq1); lra).
  split; [exact Z |]. destruct H0 as [H0 | H0]; [exact H0 | contradiction]. }
destruct (component_self _ Hne Hc) as [Hk Hall].
exists (mul_rev x y). split; [exact Hk | exact Hall].
Qed.
