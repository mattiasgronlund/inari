(** * π is irrational

    Niven's proof (1947, "A simple proof that π is irrational"), with the
    integral replaced by the mean value theorem. Suppose [PI = a / b] with
    [b > 0], and let [f] be Niven's polynomial [x ^ n * (a - b x) ^ n] for
    some [n] ([NivenSym.v]), here without the division by [n!]. Let [F] be
    the alternating sum [f - f'' + f'''' - ...] of its even derivatives,
    and [G(x) = F'(x) sin x - F(x) cos x]. As [F'' + F = f], [G' = f sin]
    ([nv_G_deriv]). [G(PI) - G(0) = F(PI) + F(0) = 2 F(0)], which is
    [2 n!] times an integer ([nv_G_ends], [nv_d_int]). By the mean value
    theorem it is also [PI * f(c) * sin c] for some [c] in [(0, PI)],
    which is positive and at most [PI * (PI * a) ^ n]. So the integer is
    at least 1, and [2 n! <= PI * (PI * a) ^ n] ([nv_bound]). That fails
    for large [n], as [(PI * a) ^ n / n!] tends to 0
    ([cv_speed_pow_fact]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Inari Require Import NivenPoly NivenAlt NivenSym.

Open Scope R_scope.

Definition nv_G (a b : Z) (n : nat) (x : R) : R :=
  ch_alt (nv_d a b n) 1 n x * sin x - ch_alt (nv_d a b n) 0 n x * cos x.

(** [derivable_pt_lim] with its limit rewritten. *)
Lemma nv_lim_eq :
  forall f x l l', l = l' -> derivable_pt_lim f x l -> derivable_pt_lim f x l'.
Proof.
  intros f x l l' E H. rewrite <- E. exact H.
Qed.

Lemma nv_G_deriv :
  forall a b n x, derivable_pt_lim (nv_G a b n) x (zp_ev (nv_poly a b n) x * sin x).
Proof.
  intros a b n x.
  pose proof (nv_d_chain a b n) as Hc.
  pose proof (derivable_pt_lim_mult _ _ x _ _
    (ch_alt_deriv _ Hc n 1 x) (derivable_pt_lim_sin x)) as H1.
  pose proof (derivable_pt_lim_mult _ _ x _ _
    (ch_alt_deriv _ Hc n 0 x) (derivable_pt_lim_cos x)) as H0.
  pose proof (derivable_pt_lim_minus _ _ x _ _ H1 H0) as H.
  (* [F'' + F = f]: the sum telescopes to [f] and a derivative of order
     [2 n + 2], which vanishes as [f] has degree [2 n]. *)
  pose proof (ch_alt_rec (nv_d a b n) n 0 x) as Hr.
  replace (0 + 2 * n + 2)%nat with (2 * n + 2)%nat in Hr by lia.
  rewrite nv_d_high, Rmult_0_r, Rplus_0_r in Hr.
  change (zp_ev (nv_poly a b n) x) with (nv_d a b n O x).
  rewrite <- Hr.
  eapply nv_lim_eq; [| exact H].
  ring.
Qed.

Lemma nv_G_ends :
  forall a b n, (0 < b)%Z -> PI = IZR a / IZR b ->
  nv_G a b n PI - nv_G a b n 0 = 2 * ch_alt (nv_d a b n) 0 n 0.
Proof.
  intros a b n Hb E.
  unfold nv_G.
  rewrite sin_PI, cos_PI, sin_0, cos_0.
  (* [F(PI) = F(0)], as [f(PI - x) = f(x)] and [F] is a sum of derivatives of
     [f] of even order. *)
  rewrite (ch_alt_reflect (nv_d a b n) 0 PI (fun k => nv_d_sym a b n k Hb E) n 0).
  rewrite pow_O.
  ring.
Qed.

Lemma nv_bound :
  forall a b n, (0 < b)%Z -> PI = IZR a / IZR b -> 2 * INR (fact n) <= PI * (PI * IZR a) ^ n.
Proof.
  intros a b n Hb E.
  assert (Hb' : 0 < IZR b) by (apply IZR_lt; exact Hb).
  assert (Ea : IZR a = PI * IZR b) by (rewrite E; field; lra).
  assert (HPI : 0 < PI) by apply PI_RGT_0.
  assert (Ha : 0 < IZR a) by (rewrite Ea; apply Rmult_lt_0_compat; assumption).
  destruct (MVT_cor2 (nv_G a b n) (fun x => zp_ev (nv_poly a b n) x * sin x) 0 PI HPI
    (fun c _ => nv_G_deriv a b n c)) as [c [Hc [Hc0 HcPI]]].
  cbv beta in Hc.
  rewrite nv_G_ends in Hc by assumption.
  destruct (ch_alt_mult (nv_d a b n) (INR (fact n)) 0 (fun k => nv_d_int a b n k) n 0)
    as [z Hz].
  rewrite Hz, nv_poly_ev, Rminus_0_r in Hc.
  (* Hc : 2 * (n! * z) = c ^ n * (a - b c) ^ n * sin c * PI. *)
  assert (Hs : 0 < sin c) by (apply sin_gt_0; assumption).
  assert (Hs1 : sin c <= 1) by apply SIN_bound.
  assert (Hq : 0 < IZR a - IZR b * c) by (rewrite Ea; nra).
  assert (Hf : 0 < c ^ n * (IZR a - IZR b * c) ^ n)
    by (apply Rmult_lt_0_compat; apply pow_lt; assumption).
  assert (Hfb : c ^ n * (IZR a - IZR b * c) ^ n <= (PI * IZR a) ^ n).
  { rewrite <- Rpow_mult_distr. apply pow_incr. split.
    - apply Rmult_le_pos; lra.
    - apply Rmult_le_compat; nra. }
  assert (Hn : 0 < INR (fact n)) by apply INR_fact_lt_0.
  (* The integer [z] is positive, so at least 1. *)
  assert (Hz1 : 1 <= IZR z).
  { assert (Hz0 : 0 < IZR z).
    { apply (Rmult_lt_reg_l (2 * INR (fact n))); [lra |].
      rewrite Rmult_0_r.
      replace (2 * INR (fact n) * IZR z) with (2 * (INR (fact n) * IZR z)) by ring.
      rewrite Hc.
      apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat |]; assumption. }
    apply IZR_le. apply lt_0_IZR in Hz0. lia. }
  assert (A : 2 * INR (fact n) <= 2 * (INR (fact n) * IZR z)) by nra.
  assert (B : c ^ n * (IZR a - IZR b * c) ^ n * sin c <= (PI * IZR a) ^ n) by nra.
  assert (C : c ^ n * (IZR a - IZR b * c) ^ n * sin c * PI <= (PI * IZR a) ^ n * PI)
    by (apply Rmult_le_compat_r; lra).
  lra.
Qed.

Theorem pi_irrational : forall p q : Z, (0 < q)%Z -> PI <> IZR p / IZR q.
Proof.
  intros p q Hq E.
  assert (Hh : 1 / 2 > 0) by lra.
  destruct (cv_speed_pow_fact (PI * IZR p) (1 / 2) Hh) as [N HN].
  specialize (HN N (Nat.le_refl N)).
  unfold R_dist in HN.
  cbv beta in HN.
  rewrite Rminus_0_r in HN.
  apply Rabs_def2 in HN.
  destruct HN as [HN _].
  pose proof (nv_bound p q N Hq E) as Hb.
  pose proof (INR_fact_lt_0 N) as Hf.
  pose proof PI_4 as H4.
  pose proof PI_RGT_0 as H0.
  (* [(PI * p) ^ N < N! / 2], so [PI * (PI * p) ^ N < 2 N!], against [nv_bound]. *)
  assert (HX : (PI * IZR p) ^ N < INR (fact N) / 2).
  { apply (Rmult_lt_reg_r (/ INR (fact N))).
    - apply Rinv_0_lt_compat; lra.
    - replace (INR (fact N) / 2 * / INR (fact N)) with (1 / 2) by (field; lra).
      exact HN. }
  assert (H1 : PI * (PI * IZR p) ^ N < PI * (INR (fact N) / 2))
    by (apply Rmult_lt_compat_l; lra).
  assert (H2 : PI * INR (fact N) <= 4 * INR (fact N))
    by (apply Rmult_le_compat_r; lra).
  lra.
Qed.
