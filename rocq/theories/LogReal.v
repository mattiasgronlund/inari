(** * Facts about [log], [log2], [log10], [atanh] and [acosh] on the reals

    What [Elem.v], [Atanh.v] and [ClosedDom.v] need of these functions:
    that they are increasing and continuous on their domains, and that
    they have no bound at the ends of their domains. *)

From Stdlib Require Import Reals Lra.
From Inari Require Import Elementary.

Open Scope R_scope.

(** ** [log], Stdlib's [ln] *)

Lemma ln_inc : forall r t, 0 < r -> r <= t -> ln r <= ln t.
Proof.
  intros r t Hr [Hlt | <-].
  - left; apply ln_increasing; assumption.
  - right; reflexivity.
Qed.

Lemma ln_cont : forall r, 0 < r -> continuity_pt ln r.
Proof.
  intros r Hr.
  apply derivable_continuous_pt.
  exact (exist _ (/ r) (derivable_pt_lim_ln r Hr)).
Qed.

Lemma ln_near0 : forall M b, 0 < b -> exists r, 0 < r <= b /\ ln r <= M.
Proof.
  intros M b Hb.
  (* Below [exp M], [ln] is below [M]. *)
  exists (Rmin b (exp M)).
  assert (H0 : 0 < Rmin b (exp M)) by (apply Rmin_glb_lt; [lra | apply exp_pos]).
  split; [split; [exact H0 | apply Rmin_l] |].
  rewrite <- (ln_exp M) at 2.
  apply ln_inc; [exact H0 | apply Rmin_r].
Qed.

Lemma ln_big : forall M, exists r, 0 < r /\ M <= ln r.
Proof.
  intros M; exists (exp M); split; [apply exp_pos | rewrite ln_exp; lra].
Qed.

(** ** [log2] and [log10] *)

(** [Rlog c] is [ln] divided by the constant [ln c]. Everything below holds
    for any [c > 1], where [ln c > 0]. *)

Lemma ln_base_pos : forall c, 1 < c -> 0 < ln c.
Proof.
  intros c Hc; rewrite <- ln_1; apply ln_increasing; lra.
Qed.

Lemma Rlog_inc :
  forall c r t, 1 < c -> 0 < r -> r <= t -> Rlog c r <= Rlog c t.
Proof.
  intros c r t Hc Hr Hrt; unfold Rlog, Rdiv.
  apply Rmult_le_compat_r.
  - left; apply Rinv_0_lt_compat, ln_base_pos, Hc.
  - apply ln_inc; assumption.
Qed.

Lemma Rlog_cont : forall c r, 1 < c -> 0 < r -> continuity_pt (Rlog c) r.
Proof.
  intros c r Hc Hr.
  change (continuity_pt (div_fct ln (fct_cte (ln c))) r).
  apply continuity_pt_div.
  - apply ln_cont, Hr.
  - apply continuity_pt_const; intros x y; reflexivity.
  - unfold fct_cte; apply Rgt_not_eq, ln_base_pos, Hc.
Qed.

(** [ln r <= M * ln c] gives [Rlog c r <= M], and the other way round. *)
Lemma Rlog_le : forall c r M, 1 < c -> ln r <= M * ln c -> Rlog c r <= M.
Proof.
  intros c r M Hc H; assert (Hl := ln_base_pos c Hc); unfold Rlog.
  apply Rmult_le_reg_r with (ln c); [exact Hl |].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; lra.
Qed.

Lemma Rlog_ge : forall c r M, 1 < c -> M * ln c <= ln r -> M <= Rlog c r.
Proof.
  intros c r M Hc H; assert (Hl := ln_base_pos c Hc); unfold Rlog.
  apply Rmult_le_reg_r with (ln c); [exact Hl |].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; lra.
Qed.

Lemma Rlog_near0 :
  forall c M b, 1 < c -> 0 < b -> exists r, 0 < r <= b /\ Rlog c r <= M.
Proof.
  intros c M b Hc Hb.
  destruct (ln_near0 (M * ln c) b Hb) as [r [Hr Hl]].
  exists r; split; [exact Hr | apply Rlog_le; assumption].
Qed.

Lemma Rlog_big : forall c M, 1 < c -> exists r, 0 < r /\ M <= Rlog c r.
Proof.
  intros c M Hc.
  destruct (ln_big (M * ln c)) as [r [Hr Hl]].
  exists r; split; [exact Hr | apply Rlog_ge; assumption].
Qed.

Lemma log2_inc : forall r t, 0 < r -> r <= t -> Rlog2 r <= Rlog2 t.
Proof.
  intros r t Hr Hrt; apply Rlog_inc; lra.
Qed.

Lemma log2_cont : forall r, 0 < r -> continuity_pt Rlog2 r.
Proof.
  intros r Hr; apply Rlog_cont; lra.
Qed.

Lemma log2_near0 : forall M b, 0 < b -> exists r, 0 < r <= b /\ Rlog2 r <= M.
Proof.
  intros M b Hb; apply Rlog_near0; lra.
Qed.

Lemma log2_big : forall M, exists r, 0 < r /\ M <= Rlog2 r.
Proof.
  intros M; apply Rlog_big; lra.
Qed.

Lemma log10_inc : forall r t, 0 < r -> r <= t -> Rlog10 r <= Rlog10 t.
Proof.
  intros r t Hr Hrt; apply Rlog_inc; lra.
Qed.

Lemma log10_cont : forall r, 0 < r -> continuity_pt Rlog10 r.
Proof.
  intros r Hr; apply Rlog_cont; lra.
Qed.

Lemma log10_near0 : forall M b, 0 < b -> exists r, 0 < r <= b /\ Rlog10 r <= M.
Proof.
  intros M b Hb; apply Rlog_near0; lra.
Qed.

Lemma log10_big : forall M, exists r, 0 < r /\ M <= Rlog10 r.
Proof.
  intros M; apply Rlog_big; lra.
Qed.

(** ** [atanh] *)

(** On [(-1, 1)], [(1 + r) / (1 - r) = 2 / (1 - r) - 1], which is positive
    and increasing in [r]. *)
Lemma atanh_arg : forall r, r < 1 -> (1 + r) / (1 - r) = 2 * / (1 - r) - 1.
Proof.
  intros r Hr; field; lra.
Qed.

Lemma atanh_arg_pos : forall r, -1 < r < 1 -> 0 < (1 + r) / (1 - r).
Proof.
  intros r Hr; apply Rdiv_lt_0_compat; lra.
Qed.

Lemma atanh_inc :
  forall r t, -1 < r -> r <= t -> t < 1 -> Ratanh r <= Ratanh t.
Proof.
  intros r t Hr Hrt Ht; unfold Ratanh.
  (* Both sides are halved: compare the logarithms. *)
  enough (H : ln ((1 + r) / (1 - r)) <= ln ((1 + t) / (1 - t))) by lra.
  apply ln_inc; [apply atanh_arg_pos; lra |].
  rewrite !atanh_arg by lra.
  apply Rplus_le_compat_r, Rmult_le_compat_l; [lra |].
  apply Rinv_le_contravar; lra.
Qed.

Lemma id_cont : forall r, continuity_pt id r.
Proof.
  intros r; apply derivable_continuous_pt, derivable_pt_id.
Qed.

Lemma const_cont : forall c r, continuity_pt (fct_cte c) r.
Proof.
  intros c r; apply continuity_pt_const; intros x y; reflexivity.
Qed.

Lemma atanh_cont : forall r, -1 < r < 1 -> continuity_pt Ratanh r.
Proof.
  intros r Hr.
  change (continuity_pt
    (div_fct
       (comp ln (div_fct (plus_fct (fct_cte 1) id) (minus_fct (fct_cte 1) id)))
       (fct_cte 2)) r).
  apply continuity_pt_div; [| apply const_cont | unfold fct_cte; lra].
  apply continuity_pt_comp.
  - apply continuity_pt_div.
    + apply continuity_pt_plus; [apply const_cont | apply id_cont].
    + apply continuity_pt_minus; [apply const_cont | apply id_cont].
    + unfold minus_fct, fct_cte, id; lra.
  - apply ln_cont.
    unfold div_fct, plus_fct, minus_fct, fct_cte, id.
    apply atanh_arg_pos, Hr.
Qed.

(** Every real [M] is [Ratanh r] for [r = (e - 1) / (e + 1)], [e = exp (2 M)]
    (the [tanh] of [M]). *)
Lemma atanh_onto : forall M, exists r, -1 < r < 1 /\ Ratanh r = M.
Proof.
  intros M.
  set (e := exp (2 * M)).
  assert (He : 0 < e) by apply exp_pos.
  set (i := / (e + 1)).
  assert (Hi : (e + 1) * i = 1) by (unfold i; field; lra).
  assert (Hi0 : 0 < i) by (unfold i; apply Rinv_0_lt_compat; lra).
  assert (Hei : 0 < e * i) by (apply Rmult_lt_0_compat; assumption).
  exists ((e - 1) * i).
  (* [1 + r = 2 e i] and [1 - r = 2 i], with [e i + i = 1]. *)
  split; [lra |].
  unfold Ratanh.
  replace ((1 + (e - 1) * i) / (1 - (e - 1) * i)) with e.
  - unfold e; rewrite ln_exp; field.
  - replace (1 + (e - 1) * i) with (2 * (e * i)) by lra.
    replace (1 - (e - 1) * i) with (2 * i) by lra.
    field; lra.
Qed.

Lemma atanh_near_m1 :
  forall M b, -1 < b -> exists r, -1 < r <= b /\ r < 1 /\ Ratanh r <= M.
Proof.
  intros M b Hb.
  destruct (atanh_onto M) as [s [Hs HsM]].
  (* [Rmin b 0] keeps the point below 1 even when [b] is not. *)
  set (r := Rmin (Rmin b 0) s).
  assert (Hrb : r <= Rmin b 0) by apply Rmin_l.
  assert (Hrs : r <= s) by apply Rmin_r.
  assert (Hb0 : Rmin b 0 <= b) by apply Rmin_l.
  assert (Hb1 : Rmin b 0 <= 0) by apply Rmin_r.
  assert (Hr1 : -1 < r) by (apply Rmin_glb_lt; [apply Rmin_glb_lt |]; lra).
  exists r; split; [lra | split; [lra |]].
  rewrite <- HsM; apply atanh_inc; lra.
Qed.

Lemma atanh_near_1 :
  forall M a, a < 1 -> exists r, a <= r < 1 /\ -1 < r /\ M <= Ratanh r.
Proof.
  intros M a Ha.
  destruct (atanh_onto M) as [s [Hs HsM]].
  (* [Rmax a 0] keeps the point above -1 even when [a] is not. *)
  set (r := Rmax (Rmax a 0) s).
  assert (Hra : Rmax a 0 <= r) by apply Rmax_l.
  assert (Hrs : s <= r) by apply Rmax_r.
  assert (Ha0 : a <= Rmax a 0) by apply Rmax_l.
  assert (Ha1 : 0 <= Rmax a 0) by apply Rmax_r.
  assert (Hr1 : r < 1) by (apply Rmax_lub_lt; [apply Rmax_lub_lt |]; lra).
  exists r; split; [lra | split; [lra |]].
  rewrite <- HsM; apply atanh_inc; lra.
Qed.

(** ** [acosh] *)

(** On [[1, +inf)], the argument of [ln] in [Racosh] is at least 1. *)
Lemma acosh_arg_ge : forall r, 1 <= r -> r <= r + sqrt (r * r - 1).
Proof.
  intros r Hr; assert (H := sqrt_pos (r * r - 1)); lra.
Qed.

Lemma acosh_inc : forall r t, 1 <= r -> r <= t -> Racosh r <= Racosh t.
Proof.
  intros r t Hr Hrt; unfold Racosh.
  assert (H := acosh_arg_ge r Hr).
  apply ln_inc; [lra |].
  apply Rplus_le_compat; [exact Hrt |].
  apply sqrt_le_1_alt; nra.
Qed.

(** [Racosh] is continuous at 1 too, as a function on R: below 1, the
    argument of [sqrt] is below 0, where Stdlib's [sqrt] is 0. *)
Lemma acosh_cont : forall r, 1 <= r -> continuity_pt Racosh r.
Proof.
  intros r Hr.
  change (continuity_pt
    (comp ln (plus_fct id (comp sqrt (minus_fct (mult_fct id id) (fct_cte 1)))))
    r).
  apply continuity_pt_comp.
  - apply continuity_pt_plus; [apply id_cont |].
    apply continuity_pt_comp.
    + apply continuity_pt_minus; [| apply const_cont].
      apply continuity_pt_mult; apply id_cont.
    + (* [continuity_pt_sqrt] needs [0 <= r * r - 1], which holds at 1. *)
      apply continuity_pt_sqrt.
      unfold minus_fct, mult_fct, fct_cte, id; nra.
  - apply ln_cont.
    unfold plus_fct, comp, minus_fct, mult_fct, fct_cte, id.
    assert (H := acosh_arg_ge r Hr); lra.
Qed.

Lemma acosh_big : forall M, exists r, 1 <= r /\ M <= Racosh r.
Proof.
  intros M.
  (* [Racosh r >= ln r >= M] once [r >= exp M]. *)
  set (r := Rmax 1 (exp M)).
  assert (H1 : 1 <= r) by apply Rmax_l.
  assert (HM : exp M <= r) by apply Rmax_r.
  exists r; split; [exact H1 |].
  unfold Racosh; rewrite <- (ln_exp M) at 1.
  apply ln_inc; [apply exp_pos |].
  assert (H := acosh_arg_ge r H1); lra.
Qed.
