(** * The proved operations on decorated intervals keep their intervals
    [valid]

    A decorated operation returns its argument or NaI if an argument is
    NaI, and otherwise [set_dec] of the interval that the operation on the
    intervals returns, which holds that interval or the empty one, except
    [convex_hull] and [intersection], which return that interval itself,
    decorated [trv] ([set_op]). So its interval is [valid] if the
    arguments' intervals are, by the theorems in [ValidOps.v] and
    [ValidSetOp.v] and [set_dec_valid]. *)

From Inari Require Import Model ValidMake ValidSetOp ValidOps.

(** [impl_dec!] in [src/integer.rs], for any [f] that keeps intervals
    [valid]. *)
Lemma impl_dec_valid :
  forall f is_not_com x, (forall u, valid u -> valid (f u)) ->
  valid (itv x) -> valid (itv (DecInterval.impl_dec f is_not_com x)).
Proof.
  intros f is_not_com x Hf Hx. unfold DecInterval.impl_dec.
  destruct (DecInterval.is_nai x); [exact Hx |].
  cbv zeta. apply set_dec_valid, Hf, Hx.
Qed.

(** [impl_dec!] in [src/set_op.rs], for any [f] that keeps intervals
    [valid]. *)
Lemma set_op_valid :
  forall f x y, (forall u v, valid u -> valid v -> valid (f u v)) ->
  valid (itv x) -> valid (itv y) -> valid (itv (DecInterval.set_op f x y)).
Proof.
  intros f x y Hf Hx Hy. unfold DecInterval.set_op.
  destruct (DecInterval.is_nai x || DecInterval.is_nai y).
  - exact (proj1 (proj2 dec_constants_valid)).
  - exact (Hf _ _ Hx Hy).
Qed.

Theorem dec_floor_valid :
  forall x, valid (itv x) -> valid (itv (DecInterval.floor x)).
Proof.
  intros x Hx. unfold DecInterval.floor.
  apply impl_dec_valid; [exact floor_valid | exact Hx].
Qed.

Theorem dec_ceil_valid :
  forall x, valid (itv x) -> valid (itv (DecInterval.ceil x)).
Proof.
  intros x Hx. unfold DecInterval.ceil.
  apply impl_dec_valid; [exact ceil_valid | exact Hx].
Qed.

Theorem dec_round_valid :
  forall x, valid (itv x) -> valid (itv (DecInterval.round x)).
Proof.
  intros x Hx. unfold DecInterval.round.
  apply impl_dec_valid; [exact round_valid | exact Hx].
Qed.

Theorem dec_round_ties_even_valid :
  forall x, valid (itv x) -> valid (itv (DecInterval.round_ties_even x)).
Proof.
  intros x Hx. unfold DecInterval.round_ties_even.
  apply impl_dec_valid; [exact round_ties_even_valid | exact Hx].
Qed.

Theorem dec_trunc_valid :
  forall x, valid (itv x) -> valid (itv (DecInterval.trunc x)).
Proof.
  intros x Hx. unfold DecInterval.trunc.
  apply impl_dec_valid; [exact trunc_valid | exact Hx].
Qed.

Theorem dec_sign_valid :
  forall x, valid (itv x) -> valid (itv (DecInterval.sign x)).
Proof.
  intros x Hx. unfold DecInterval.sign.
  apply impl_dec_valid; [exact sign_valid | exact Hx].
Qed.

Theorem dec_neg_valid :
  forall x, valid (itv x) -> valid (itv (DecInterval.neg x)).
Proof.
  intros x Hx. unfold DecInterval.neg.
  destruct (DecInterval.is_nai x); [exact Hx |].
  apply set_dec_valid, neg_valid, Hx.
Qed.

Theorem dec_abs_valid :
  forall x z, valid (itv x) -> DecInterval.abs x = Some z -> valid (itv z).
Proof.
  intros x z Hx H. unfold DecInterval.abs in H.
  destruct (DecInterval.is_nai x).
  - injection H as <-. exact Hx.
  - destruct (Interval.abs (itv x)) as [y |] eqn:E; [| discriminate].
    injection H as <-. apply set_dec_valid. exact (abs_valid _ _ Hx E).
Qed.

Theorem dec_max_valid :
  forall has_maximum x y, valid (itv x) -> valid (itv y) ->
  valid (itv (DecInterval.max has_maximum x y)).
Proof.
  intros has_maximum x y Hx Hy. unfold DecInterval.max.
  destruct (DecInterval.is_nai x); [exact Hx |].
  apply set_dec_valid, max_valid; [exact Hx | exact Hy].
Qed.

Theorem dec_min_valid :
  forall has_maximum x y, valid (itv x) -> valid (itv y) ->
  valid (itv (DecInterval.min has_maximum x y)).
Proof.
  intros has_maximum x y Hx Hy. unfold DecInterval.min.
  destruct (DecInterval.is_nai x); [exact Hx |].
  apply set_dec_valid, min_valid; [exact Hx | exact Hy].
Qed.

Theorem dec_add_valid :
  forall x y z, valid (itv x) -> valid (itv y) ->
  DecInterval.add x y = Some z -> valid (itv z).
Proof.
  intros x y z Hx Hy H. unfold DecInterval.add in H.
  destruct (DecInterval.is_nai x || DecInterval.is_nai y).
  - injection H as <-. exact (proj1 (proj2 dec_constants_valid)).
  - destruct (Interval.add (itv x) (itv y)) as [w |] eqn:E; [| discriminate].
    injection H as <-. apply set_dec_valid. exact (add_valid _ _ _ Hx Hy E).
Qed.

Theorem dec_sub_valid :
  forall x y z, valid (itv x) -> valid (itv y) ->
  DecInterval.sub x y = Some z -> valid (itv z).
Proof.
  intros x y z Hx Hy H. unfold DecInterval.sub in H.
  destruct (DecInterval.is_nai x || DecInterval.is_nai y).
  - injection H as <-. exact (proj1 (proj2 dec_constants_valid)).
  - destruct (Interval.sub (itv x) (itv y)) as [w |] eqn:E; [| discriminate].
    injection H as <-. apply set_dec_valid. exact (sub_valid _ _ _ Hx Hy E).
Qed.

Theorem dec_mul_valid :
  forall has_fma x y z, valid (itv x) -> valid (itv y) ->
  DecInterval.mul has_fma x y = Some z -> valid (itv z).
Proof.
  intros has_fma x y z Hx Hy H. unfold DecInterval.mul in H.
  destruct (DecInterval.is_nai x || DecInterval.is_nai y).
  - injection H as <-. exact (proj1 (proj2 dec_constants_valid)).
  - cbv zeta in H.
    destruct (Interval.mul has_fma (itv x) (itv y)) as [w |] eqn:E;
      [| discriminate].
    injection H as <-. apply set_dec_valid.
    exact (mul_valid _ _ _ _ Hx Hy E).
Qed.

Theorem dec_div_valid :
  forall has_fma x y z, valid (itv x) -> valid (itv y) ->
  DecInterval.div has_fma x y = Some z -> valid (itv z).
Proof.
  intros has_fma x y z Hx Hy H. unfold DecInterval.div in H.
  destruct (DecInterval.is_nai x || DecInterval.is_nai y).
  - injection H as <-. exact (proj1 (proj2 dec_constants_valid)).
  - cbv zeta in H.
    destruct (Interval.div has_fma (itv x) (itv y)) as [w |] eqn:E;
      [| discriminate].
    (* [injection H as <-] does not finish on this [H]; it does on an
       abstract [u]. *)
    assert (Hs : forall u, Some u = Some z -> valid (itv u) -> valid (itv z))
      by (intros u Hu; injection Hu as ->; exact (fun h => h)).
    apply (Hs _ H), set_dec_valid. exact (div_valid _ _ _ _ Hx Hy E).
Qed.

Theorem dec_sqr_valid :
  forall has_fma x z, valid (itv x) ->
  DecInterval.sqr has_fma x = Some z -> valid (itv z).
Proof.
  intros has_fma x z Hx H. unfold DecInterval.sqr in H.
  destruct (DecInterval.is_nai x).
  - injection H as <-. exact Hx.
  - cbv zeta in H.
    destruct (Interval.sqr has_fma (itv x)) as [y |] eqn:E; [| discriminate].
    injection H as <-. apply set_dec_valid. exact (sqr_valid _ _ _ Hx E).
Qed.

Theorem dec_sqrt_valid :
  forall has_fma x z, valid (itv x) ->
  DecInterval.sqrt has_fma x = Some z -> valid (itv z).
Proof.
  intros has_fma x z Hx H. unfold DecInterval.sqrt in H.
  destruct (DecInterval.is_nai x).
  - injection H as <-. exact Hx.
  - cbv zeta in H.
    destruct (Interval.sqrt has_fma (itv x)) as [y |] eqn:E; [| discriminate].
    injection H as <-. apply set_dec_valid. exact (sqrt_valid _ _ _ Hx E).
Qed.

Theorem dec_recip_valid :
  forall has_fma x z, valid (itv x) ->
  DecInterval.recip has_fma x = Some z -> valid (itv z).
Proof.
  intros has_fma x z Hx H. unfold DecInterval.recip in H.
  destruct (DecInterval.is_nai x).
  - injection H as <-. exact Hx.
  - cbv zeta in H.
    destruct (Interval.recip has_fma (itv x)) as [y |] eqn:E; [| discriminate].
    (* [injection H as <-] does not finish on this [H]; it does on an
       abstract [u]. *)
    assert (Hs : forall u, Some u = Some z -> valid (itv u) -> valid (itv z))
      by (intros u Hu; injection Hu as ->; exact (fun h => h)).
    apply (Hs _ H), set_dec_valid. exact (recip_valid _ _ _ Hx E).
Qed.

Theorem dec_convex_hull_valid :
  forall x y, valid (itv x) -> valid (itv y) ->
  valid (itv (DecInterval.convex_hull x y)).
Proof.
  intros x y Hx Hy. unfold DecInterval.convex_hull.
  apply set_op_valid; [exact convex_hull_valid | exact Hx | exact Hy].
Qed.

Theorem dec_intersection_valid :
  forall x y, valid (itv x) -> valid (itv y) ->
  valid (itv (DecInterval.intersection x y)).
Proof.
  intros x y Hx Hy. unfold DecInterval.intersection.
  apply set_op_valid; [exact intersection_valid | exact Hx | exact Hy].
Qed.
