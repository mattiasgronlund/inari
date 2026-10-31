(** * Polynomials with integer coefficients, and their derivatives

    For [PiIrrational.v]. A polynomial is the list of its integer
    coefficients, lowest degree first, and [zp_ev l x] its value at the
    real [x], by Horner's rule. [zp_d l] is the formal derivative, and
    [zp_ev (zp_d l)] is the derivative of [zp_ev l] ([zp_ev_d]). Its
    [k]-th iterate [zp_dn k l] has the constant coefficient [k! * l_k]
    ([zp_ev_dn_0]), and is 0 once [k] reaches the length of [l]
    ([zp_ev_dn_high]). [zp_qpow a b n] is [(a - b x) ^ n]. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
Import ListNotations.

Open Scope R_scope.

Fixpoint zp_ev (l : list Z) (x : R) : R :=
  match l with
  | [] => 0
  | c :: l => IZR c + x * zp_ev l x
  end.

(** The sum, coefficient by coefficient. *)
Fixpoint zp_add (l m : list Z) : list Z :=
  match l, m with
  | [], m => m
  | l, [] => l
  | c :: l, d :: m => (c + d)%Z :: zp_add l m
  end.

Definition zp_scale (z : Z) (l : list Z) : list Z := map (Z.mul z) l.

(** The derivative of [c + x * p(x)] is [p(x) + x * p'(x)]. *)
Fixpoint zp_d (l : list Z) : list Z :=
  match l with
  | [] => []
  | _ :: l => zp_add l (0%Z :: zp_d l)
  end.

Fixpoint zp_dn (k : nat) (l : list Z) : list Z :=
  match k with
  | O => l
  | S k => zp_d (zp_dn k l)
  end.

(** [l] multiplied by [a - b x]. *)
Definition zp_lin (a b : Z) (l : list Z) : list Z :=
  zp_add (zp_scale a l) (0%Z :: zp_scale (- b) l).

Fixpoint zp_qpow (a b : Z) (n : nat) : list Z :=
  match n with
  | O => [1%Z]
  | S n => zp_lin a b (zp_qpow a b n)
  end.

Lemma zp_nth_nil : forall i, nth i [] 0%Z = 0%Z.
Proof.
  intros [| i]; reflexivity.
Qed.

Lemma zp_length_add :
  forall l m, length (zp_add l m) = Nat.max (length l) (length m).
Proof.
  induction l as [| c l IH]; intros m.
  - reflexivity.
  - destruct m as [| d m].
    + cbn [zp_add length]. lia.
    + cbn [zp_add length]. rewrite IH. lia.
Qed.

Lemma zp_ev_add : forall l m x, zp_ev (zp_add l m) x = zp_ev l x + zp_ev m x.
Proof.
  induction l as [| c l IH]; intros m x.
  - cbn [zp_add zp_ev]. ring.
  - destruct m as [| d m].
    + cbn [zp_add zp_ev]. ring.
    + cbn [zp_add zp_ev]. rewrite IH, plus_IZR. ring.
Qed.

Lemma zp_ev_scale : forall z l x, zp_ev (zp_scale z l) x = IZR z * zp_ev l x.
Proof.
  intros z l x. unfold zp_scale. induction l as [| c l IH].
  - cbn [map zp_ev]. ring.
  - cbn [map zp_ev]. rewrite IH, mult_IZR. ring.
Qed.

Lemma zp_ev_lin :
  forall a b l x, zp_ev (zp_lin a b l) x = (IZR a - IZR b * x) * zp_ev l x.
Proof.
  intros a b l x. unfold zp_lin.
  rewrite zp_ev_add. cbn [zp_ev]. rewrite !zp_ev_scale, opp_IZR. ring.
Qed.

Lemma zp_ev_qpow : forall a b n x, zp_ev (zp_qpow a b n) x = (IZR a - IZR b * x) ^ n.
Proof.
  intros a b n x. induction n as [| n IH].
  - cbn [zp_qpow zp_ev pow]. ring.
  - cbn [zp_qpow pow]. rewrite zp_ev_lin, IH. ring.
Qed.

Lemma zp_length_qpow : forall a b n, length (zp_qpow a b n) = S n.
Proof.
  intros a b n. induction n as [| n IH].
  - reflexivity.
  - cbn [zp_qpow]. unfold zp_lin, zp_scale.
    rewrite zp_length_add. cbn [length]. rewrite !length_map, IH. lia.
Qed.

(** [n] zero coefficients in front multiply by [x ^ n]. *)
Lemma zp_ev_shift : forall n l x, zp_ev (repeat 0%Z n ++ l) x = x ^ n * zp_ev l x.
Proof.
  induction n as [| n IH]; intros l x.
  - cbn [repeat app pow]. ring.
  - cbn [repeat app zp_ev pow]. rewrite IH. ring.
Qed.

Lemma zp_ev_d : forall l x, derivable_pt_lim (zp_ev l) x (zp_ev (zp_d l) x).
Proof.
  induction l as [| c l IH]; intros x.
  - apply (derivable_pt_lim_ext (fct_cte 0)).
    + intro z. reflexivity.
    + apply derivable_pt_lim_const.
  - (* [zp_ev (c :: l)] is [fct_cte (IZR c) + id * zp_ev l], whose
       derivative by the sum and product rules is
       [0 + (1 * zp_ev l x + id x * zp_ev (zp_d l) x)]. *)
    assert (H : derivable_pt_lim (fct_cte (IZR c) + id * zp_ev l)%F x
                  (0 + (1 * zp_ev l x + id x * zp_ev (zp_d l) x))).
    { apply derivable_pt_lim_plus.
      - apply derivable_pt_lim_const.
      - apply derivable_pt_lim_mult.
        + apply derivable_pt_lim_id.
        + apply IH. }
    replace (zp_ev (zp_d (c :: l)) x)
      with (0 + (1 * zp_ev l x + id x * zp_ev (zp_d l) x)).
    + apply (derivable_pt_lim_ext (fct_cte (IZR c) + id * zp_ev l)%F).
      * intro z. reflexivity.
      * exact H.
    + cbn [zp_d]. rewrite zp_ev_add. cbn [zp_ev]. unfold id. ring.
Qed.

Lemma zp_ev_dn :
  forall k l x, derivable_pt_lim (zp_ev (zp_dn k l)) x (zp_ev (zp_dn (S k) l) x).
Proof.
  intros k l x. exact (zp_ev_d (zp_dn k l) x).
Qed.

Lemma zp_nth_add :
  forall l m i, nth i (zp_add l m) 0%Z = (nth i l 0%Z + nth i m 0%Z)%Z.
Proof.
  induction l as [| c l IH]; intros m i.
  - cbn [zp_add]. rewrite zp_nth_nil. lia.
  - destruct m as [| d m].
    + cbn [zp_add]. rewrite zp_nth_nil. lia.
    + cbn [zp_add]. destruct i as [| i].
      * reflexivity.
      * cbn [nth]. apply IH.
Qed.

Lemma zp_nth_d : forall l i, nth i (zp_d l) 0%Z = (Z.of_nat (S i) * nth (S i) l 0%Z)%Z.
Proof.
  induction l as [| c l IH]; intros i.
  - cbn [zp_d]. rewrite !zp_nth_nil. ring.
  - cbn [zp_d]. rewrite zp_nth_add. destruct i as [| i].
    + cbn [nth]. change (Z.of_nat 1) with 1%Z. ring.
    + cbn [nth]. rewrite IH, !Nat2Z.inj_succ. unfold Z.succ. ring.
Qed.

(** The [k]-th derivative multiplies the coefficient of [x ^ (i + k)] by
    [(i + k)! / i!] and moves it to [x ^ i]. *)
Lemma zp_nth_dn :
  forall k l i,
  (Z.of_nat (fact i) * nth i (zp_dn k l) 0%Z = Z.of_nat (fact (i + k)) * nth (i + k) l 0%Z)%Z.
Proof.
  induction k as [| k IH]; intros l i.
  - cbn [zp_dn]. rewrite Nat.add_0_r. reflexivity.
  - cbn [zp_dn]. rewrite zp_nth_d.
    replace (i + S k)%nat with (S i + k)%nat by lia.
    rewrite <- (IH l (S i)).
    (* [(S i)! = S i * i!] *)
    change (fact (S i)) with (S i * fact i)%nat.
    rewrite Nat2Z.inj_mul. ring.
Qed.

Lemma zp_ev_0 : forall l, zp_ev l 0 = IZR (nth 0 l 0%Z).
Proof.
  intros [| c l]; cbn [zp_ev nth].
  - reflexivity.
  - ring.
Qed.

Lemma zp_ev_dn_0 : forall k l, zp_ev (zp_dn k l) 0 = IZR (Z.of_nat (fact k) * nth k l 0%Z).
Proof.
  intros k l. rewrite zp_ev_0. f_equal.
  pose proof (zp_nth_dn k l 0) as H. cbn [Nat.add fact] in H.
  rewrite <- H. change (Z.of_nat 1) with 1%Z. ring.
Qed.

Lemma zp_ev_nth_0 : forall l x, (forall i, nth i l 0%Z = 0%Z) -> zp_ev l x = 0.
Proof.
  induction l as [| c l IH]; intros x H.
  - reflexivity.
  - pose proof (H O) as H0. cbn [nth] in H0. subst c.
    cbn [zp_ev]. rewrite (IH x).
    + ring.
    + intro i. exact (H (S i)).
Qed.

Lemma zp_ev_dn_high : forall k l x, (length l <= k)%nat -> zp_ev (zp_dn k l) x = 0.
Proof.
  intros k l x Hk. apply zp_ev_nth_0. intro i.
  pose proof (zp_nth_dn k l i) as H.
  (* The coefficient of [x ^ (i + k)] in [l] is past its end. *)
  rewrite (nth_overflow l) in H by lia.
  rewrite Z.mul_0_r in H.
  apply Z.mul_eq_0 in H. destruct H as [H | H].
  - exfalso. pose proof (lt_O_fact i). lia.
  - exact H.
Qed.
