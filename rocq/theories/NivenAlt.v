(** * Chains of derivatives, and Niven's alternating sum

    For [PiIrrational.v]. [ch_chain d] says that each [d (S k)] is the
    derivative of [d k], so [d k] is the [k]-th derivative of [d 0]. Two
    chains that start with the same function agree everywhere
    ([ch_unique]), and [x => (-1) ^ k * d k (c - x)] is the chain of
    [x => d 0 (c - x)] ([ch_reflect]). [ch_alt d s m] is the alternating
    sum [d s - d (s + 2) + ... + (-1) ^ m * d (s + 2 m)], whose derivative
    is [ch_alt d (S s) m] ([ch_alt_deriv]), and which, added to its second
    derivative, telescopes to [d s] and one last term ([ch_alt_rec]). *)

From Stdlib Require Import Reals Lra Lia ZArith.

Open Scope R_scope.

Definition ch_chain (d : nat -> R -> R) : Prop :=
  forall k x, derivable_pt_lim (d k) x (d (S k) x).

Lemma ch_unique :
  forall d e, ch_chain d -> ch_chain e -> (forall x, d O x = e O x) ->
  forall k x, d k x = e k x.
Proof.
  intros d e Hd He H0 k.
  induction k as [|k IHk]; intros x.
  - apply H0.
  - (* [d k] and [e k] are the same function, so both [d (S k) x] and
       [e (S k) x] are its derivative at [x]. *)
    apply (uniqueness_limite (d k) x).
    + apply Hd.
    + apply (derivable_pt_lim_ext (e k)).
      * intros z. symmetry. apply IHk.
      * apply He.
Qed.

Lemma ch_reflect :
  forall d c, ch_chain d -> ch_chain (fun k x => (-1) ^ k * d k (c - x)).
Proof.
  intros d c Hd k x.
  cbv beta.
  assert (H1 : derivable_pt_lim (fun x => c - x) x (-1)).
  { replace (-1) with (0 - 1) by ring.
    apply (derivable_pt_lim_minus (fct_cte c) id).
    - apply derivable_pt_lim_const.
    - apply derivable_pt_lim_id. }
  (* Chain rule for [comp (d k) (fun x => c - x)], then scale by [(-1) ^ k]. *)
  replace ((-1) ^ S k * d (S k) (c - x))
    with ((-1) ^ k * (d (S k) (c - x) * -1)) by (simpl; ring).
  apply (derivable_pt_lim_scal (comp (d k) (fun x => c - x))).
  apply derivable_pt_lim_comp.
  - exact H1.
  - apply Hd.
Qed.

Fixpoint ch_alt (d : nat -> R -> R) (s m : nat) (x : R) : R :=
  match m with
  | O => d s x
  | S m => d s x - ch_alt d (S (S s)) m x
  end.

Lemma ch_alt_deriv :
  forall d, ch_chain d -> forall m s x, derivable_pt_lim (ch_alt d s m) x (ch_alt d (S s) m x).
Proof.
  intros d Hd m.
  induction m as [|m IHm]; intros s x; simpl.
  - apply Hd.
  - apply (derivable_pt_lim_minus (d s) (ch_alt d (S (S s)) m)).
    + apply Hd.
    + apply IHm.
Qed.

Lemma ch_alt_rec :
  forall d m s x,
  ch_alt d (S (S s)) m x + ch_alt d s m x = d s x + (-1) ^ m * d (s + 2 * m + 2)%nat x.
Proof.
  intros d m.
  induction m as [|m IHm]; intros s x.
  - simpl. replace (s + 0 + 2)%nat with (S (S s)) by lia. ring.
  - change (ch_alt d (S (S s)) (S m) x)
      with (d (S (S s)) x - ch_alt d (S (S (S (S s)))) m x).
    change (ch_alt d s (S m) x) with (d s x - ch_alt d (S (S s)) m x).
    pose proof (IHm (S (S s)) x) as H.
    replace (S (S s) + 2 * m + 2)%nat with (s + 2 * S m + 2)%nat in H by lia.
    simpl pow. lra.
Qed.

(** If every [d k] is a multiple of [N] at [x0], so is every sum. *)
Lemma ch_alt_mult :
  forall d N x0, (forall k, exists z, d k x0 = N * IZR z) ->
  forall m s, exists z, ch_alt d s m x0 = N * IZR z.
Proof.
  intros d N x0 Hk m.
  induction m as [|m IHm]; intros s.
  - apply Hk.
  - destruct (Hk s) as [z1 H1]. destruct (IHm (S (S s))) as [z2 H2].
    exists (z1 - z2)%Z. simpl. rewrite H1, H2, minus_IZR. ring.
Qed.

Lemma ch_alt_reflect :
  forall d x0 x1, (forall k, d k x1 = (-1) ^ k * d k x0) ->
  forall m s, ch_alt d s m x1 = (-1) ^ s * ch_alt d s m x0.
Proof.
  intros d x0 x1 H m.
  induction m as [|m IHm]; intros s.
  - apply H.
  - simpl ch_alt. rewrite H, IHm. simpl pow. ring.
Qed.
