(** * The odd value of [hypot] in the dyadic kernel

    At finite nonzero [x] and [y], [DyadicRoot.hypot_odd x y] is
    [(2 s + b) 2^(E - 1)] with [2^53 <= s],
    [s 2^E <= sqrt(x^2 + y^2) < (s + 1) 2^E], and [b] false exactly when
    the root is [s 2^E] ([hypot_odd_correct]). With [|x| >= |y|] (else the
    two are swapped, which leaves the root unchanged),
    [|x| = M 2^e] and [|y| = m 2^f] with [2^63 <= M, m < 2^64]
    ([Dyadic.from_f64]), and [g = e - f >= 0]. For [g >= 27], [M] is a
    multiple of [2^10], as [|x|] has 53 bits, [s = M / 2^10] and
    [E = e + 10] ([hypot_cut] of [RootReal.v]). Otherwise
    [sqrt(x^2 + y^2) = sqrt((M^2 2^(2 g) + m^2) 2^(2 h)) 2^(f - h)], and
    [hypot_exact_branch] of [DyHypotExact.v] gives [s] and [b] with
    [E = f - h]. [DyHypot.v] uses it. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Limbs DyRound DyConv RootReal RootRound DyHypotExact.

Open Scope Z_scope.

(** ** Lemmas *)

Local Lemma hy_IZR_pow2 : forall e, 0 <= e -> IZR (2 ^ e) = bpow radix2 e.
Proof. intros e He. exact (IZR_Zpower radix2 e He). Qed.

Local Lemma hy_sq_abs : forall r, (r * r = Rabs r * Rabs r)%R.
Proof. intros r. unfold Rabs. destruct (Rcase_abs r); ring. Qed.

(** [Dyadic.from_f64 1] of [|x|], for a finite nonzero [x], is
    [M 2^e] with the one limb [M] of 64 bits. *)
Local Lemma hy_from :
  forall x, is_finite x = true -> B2R x <> 0%R ->
  exists a M,
  Dyadic.from_f64 1 (fabs x) = Some a /\ Dyadic.dy_m a = M :: nil /\
  2 ^ 63 <= M < 2 ^ 64 /\ - 2 ^ 61 <= Dyadic.dy_exp a <= 2 ^ 61 /\
  Rabs (B2R x) = (IZR M * bpow radix2 (Dyadic.dy_exp a))%R.
Proof.
intros x Fx Hx0.
assert (Hn : level_ok 1) by (unfold level_ok; lia).
assert (Fa : is_finite (fabs x) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fx).
destruct (from_f64_correct 1 (fabs x) Hn Fa) as (a & Ea & Oa & Sa & Va).
unfold fabs in Va. rewrite B2R_Babs in Va.
assert (Hpos : (0 < Rabs (B2R x))%R) by (apply Rabs_pos_lt; exact Hx0).
destruct (dy_cases 1 a Hn Oa) as [(_ & _ & _ & _ & H0) | (_ & HM & _)].
{ rewrite Va in H0. lra. }
assert (HM' : 2 ^ 63 <= Limbs.val (Dyadic.dy_m a) < 2 ^ 64) by exact HM.
clear HM.
destruct Oa as (_ & Hl & _ & _).
unfold exp_small in Sa.
unfold Dyadic.dy_R in Va. cbv beta zeta in Va.
revert Hl HM' Va.
destruct (Dyadic.dy_m a) as [| M [| M' r]] eqn:Ma; cbn [length]; intros Hl HM' Va;
  try discriminate Hl.
assert (VM : Limbs.val (M :: nil) = M) by (cbn [Limbs.val]; ring).
rewrite VM in HM', Va.
exists a, M.
split; [exact Ea |]. split; [exact Ma |]. split; [exact HM' |]. split; [exact Sa |].
pose proof (bpow_gt_0 radix2 (Dyadic.dy_exp a)) as He.
assert (HM0 : (0 < IZR M)%R) by (apply IZR_lt; lia).
revert Va. destruct (Dyadic.dy_neg a); intros Va.
- (* A negative [Dyadic] is not [|x|]. *)
  exfalso.
  assert (0 < IZR M * bpow radix2 (Dyadic.dy_exp a))%R by (apply Rmult_lt_0_compat; lra).
  lra.
- symmetry. exact Va.
Qed.

(** A finite [x] with [|x| = M 2^e] and [2^63 <= M] has [M] a multiple
    of [2^10]: [|x| = n 2^f] with [|n| < 2^53] (an [f64] has 53 bits), so
    [M = n 2^(f - e)] with [f - e >= 11]. *)
Local Lemma hy_low :
  forall (x : f64) M e, 2 ^ 63 <= M -> Rabs (B2R x) = (IZR M * bpow radix2 e)%R -> M mod 2 ^ 10 = 0.
Proof.
intros x M e HM Hx.
assert (G : generic_format radix2 (FLT_exp (-1074) 53) (B2R (fabs x)))
  by exact (generic_format_B2R 53 1024 (fabs x)).
unfold fabs in G. rewrite B2R_Babs, Hx in G.
destruct (FLT_format_generic radix2 (-1074) 53 _ G) as [[n f] Hxf Hn _].
cbn [Fnum] in Hn. change (Zpower radix2 53) with (2 ^ 53) in Hn.
unfold F2R in Hxf. cbn [Fnum Fexp] in Hxf.
pose proof (bpow_gt_0 radix2 e) as He.
destruct (Z_lt_le_dec f e) as [Hf | Hf].
- (* [n = M 2^(e - f) >= M >= 2^63]. *)
  exfalso.
  assert (H1 : IZR n = IZR (M * 2 ^ (e - f))).
  { rewrite mult_IZR, hy_IZR_pow2 by lia.
    apply Rmult_eq_reg_r with (bpow radix2 f); [| apply Rgt_not_eq, bpow_gt_0].
    rewrite <- Hxf, Rmult_assoc, <- bpow_plus.
    replace (e - f + f) with e by ring. reflexivity. }
  apply eq_IZR in H1.
  assert (H2 : 2 ^ 0 <= 2 ^ (e - f)) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 0) with 1 in H2.
  nia.
- assert (H1 : IZR M = IZR (n * 2 ^ (f - e))).
  { rewrite mult_IZR, hy_IZR_pow2 by lia.
    apply Rmult_eq_reg_r with (bpow radix2 e); [| apply Rgt_not_eq; exact He].
    rewrite Hxf, Rmult_assoc, <- bpow_plus.
    replace (f - e + e) with f by ring. reflexivity. }
  apply eq_IZR in H1.
  destruct (Z_lt_le_dec (f - e) 11) as [Hg | Hg].
  + (* [M <= |n| 2^10 < 2^63]. *)
    exfalso.
    assert (H2 : 2 ^ (f - e) <= 2 ^ 10) by (apply Z.pow_le_mono_r; lia).
    assert (H3 : 0 < 2 ^ (f - e)) by (apply Z.pow_pos_nonneg; lia).
    nia.
  + rewrite H1. replace (f - e) with (f - e - 10 + 10) by ring.
    rewrite Z.pow_add_r by lia. rewrite Z.mul_assoc. apply Z.mod_mul. lia.
Qed.

(** [s^2 <= X < (s + 1)^2] puts [sqrt X] in [[s, s + 1)], at [s] exactly
    when [X = s^2]. *)
Local Lemma hy_window :
  forall s X E, 0 <= s -> s * s <= X < (s + 1) * (s + 1) ->
  (IZR s * bpow radix2 E <= sqrt (IZR X) * bpow radix2 E < IZR (s + 1) * bpow radix2 E)%R /\
  ((sqrt (IZR X) * bpow radix2 E = IZR s * bpow radix2 E)%R <-> s * s = X).
Proof.
intros s X E Hs HX.
pose proof (bpow_gt_0 radix2 E) as HE.
assert (Q : forall t, 0 <= t -> sqrt (IZR (t * t)) = IZR t).
{ intros t Ht. rewrite mult_IZR. apply sqrt_square. apply IZR_le. exact Ht. }
assert (L : (IZR s <= sqrt (IZR X))%R).
{ rewrite <- (Q s Hs). apply sqrt_le_1_alt, IZR_le. lia. }
assert (U : (sqrt (IZR X) < IZR (s + 1))%R).
{ rewrite <- (Q (s + 1)) by lia. apply sqrt_lt_1_alt.
  split; [apply IZR_le; nia | apply IZR_lt; lia]. }
split; [split |].
- apply Rmult_le_compat_r; lra.
- apply Rmult_lt_compat_r; lra.
- split.
  + intros H.
    assert (H' : sqrt (IZR X) = IZR s).
    { apply Rmult_eq_reg_r with (bpow radix2 E); [exact H | apply Rgt_not_eq; exact HE]. }
    apply eq_IZR. rewrite mult_IZR, <- H'. apply sqrt_sqrt, IZR_le. nia.
  + intros H. rewrite <- H, (Q s Hs). reflexivity.
Qed.

(** [|x|^2 + |y|^2 = X 2^(2 (f - h))] for [|x| = M 2^e], [|y| = m 2^f]
    and [X = (M^2 2^(2 (e - f)) + m^2) 2^(2 h)]. *)
Local Lemma hy_sum :
  forall M m ea eb h, eb <= ea -> 0 <= h ->
  (IZR M * bpow radix2 ea * (IZR M * bpow radix2 ea)
   + IZR m * bpow radix2 eb * (IZR m * bpow radix2 eb) =
   IZR ((M * M * 2 ^ (2 * (ea - eb)) + m * m) * 2 ^ (2 * h))
   * (bpow radix2 (eb - h) * bpow radix2 (eb - h)))%R.
Proof.
intros M m ea eb h Hg Hh.
rewrite !mult_IZR, plus_IZR, !mult_IZR, !hy_IZR_pow2 by lia.
assert (B1 : bpow radix2 ea = (bpow radix2 (ea - eb) * bpow radix2 (eb - h) * bpow radix2 h)%R).
{ rewrite <- !bpow_plus. f_equal. ring. }
assert (B2 : bpow radix2 eb = (bpow radix2 (eb - h) * bpow radix2 h)%R).
{ rewrite <- bpow_plus. f_equal. ring. }
assert (B3 : bpow radix2 (2 * (ea - eb)) = (bpow radix2 (ea - eb) * bpow radix2 (ea - eb))%R).
{ rewrite <- bpow_plus. f_equal. ring. }
assert (B4 : bpow radix2 (2 * h) = (bpow radix2 h * bpow radix2 h)%R).
{ rewrite <- bpow_plus. f_equal. ring. }
rewrite B1, B2, B3, B4. ring.
Qed.

(** [hypot_odd_correct] with [|y| <= |x|], where [hypot_odd] takes
    [|x|] as the larger argument. *)
Local Lemma hypot_odd_ge :
  forall x y,
  is_finite x = true -> is_finite y = true -> B2R x <> 0%R -> B2R y <> 0%R ->
  ge (fabs x) (fabs y) = true ->
  exists d s E b,
  DyadicRoot.hypot_odd x y = Some d /\ dy_ok 3 d /\
  Dyadic.dy_R d = (IZR (2 * s + Z.b2z b) * bpow radix2 (E - 1))%R /\
  2 ^ 53 <= s /\
  (IZR s * bpow radix2 E <= sqrt (B2R x * B2R x + B2R y * B2R y)
     < IZR (s + 1) * bpow radix2 E)%R /\
  (b = false <-> sqrt (B2R x * B2R x + B2R y * B2R y) = (IZR s * bpow radix2 E)%R).
Proof.
intros x y Fx Fy Hx0 Hy0 Hge.
assert (Hn : level_ok 3) by (unfold level_ok; lia).
destruct (hy_from x Fx Hx0) as (da & M & Ea & Ma & HM & Sa & Va).
destruct (hy_from y Fy Hy0) as (db & m & Eb & Mb & Hm & Sb & Vb).
(* [|y| <= |x|]. *)
assert (Hle : (Rabs (B2R y) <= Rabs (B2R x))%R).
{ assert (Fax : is_finite (fabs x) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fx).
  assert (Fay : is_finite (fabs y) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fy).
  pose proof Hge as G0.
  unfold ge in G0. rewrite Bleb_correct in G0 by assumption.
  unfold fabs in G0. rewrite !B2R_Babs in G0.
  destruct (Rle_bool_spec (Rabs (B2R y)) (Rabs (B2R x))) as [L | L];
    [exact L | discriminate G0]. }
(* [x^2 + y^2 = |x|^2 + |y|^2]. *)
assert (Hsum :
  (B2R x * B2R x + B2R y * B2R y =
   IZR M * bpow radix2 (Dyadic.dy_exp da) * (IZR M * bpow radix2 (Dyadic.dy_exp da))
   + IZR m * bpow radix2 (Dyadic.dy_exp db) * (IZR m * bpow radix2 (Dyadic.dy_exp db)))%R).
{ rewrite (hy_sq_abs (B2R x)), (hy_sq_abs (B2R y)), Va, Vb. reflexivity. }
rewrite Va, Vb in Hle.
(* [eb <= ea], as [m 2^eb <= M 2^ea] with [2^63 <= m] and [M < 2^64]. *)
assert (Hg0 : Dyadic.dy_exp db <= Dyadic.dy_exp da).
{ destruct (Z_lt_le_dec (Dyadic.dy_exp da) (Dyadic.dy_exp db)) as [L | L]; [exfalso | exact L].
  assert (B : (bpow radix2 (Dyadic.dy_exp da) * 2 <= bpow radix2 (Dyadic.dy_exp db))%R).
  { change 2%R with (bpow radix2 1). rewrite <- bpow_plus. apply bpow_le. lia. }
  pose proof (bpow_gt_0 radix2 (Dyadic.dy_exp da)) as Pa.
  assert (RM : (IZR M < 18446744073709551616)%R) by (apply IZR_lt; lia).
  assert (Rm : (9223372036854775808 <= IZR m)%R) by (apply IZR_le; lia).
  nra. }
unfold DyadicRoot.hypot_odd. rewrite Hge. cbv beta iota zeta.
rewrite Ea, Eb. cbv beta iota. rewrite Ma, Mb.
destruct (27 <=? Dyadic.dy_exp da - Dyadic.dy_exp db) eqn:G.
- (* The cut: [s = M / 2^10], [E = e + 10], [b] true ([hypot_cut]). *)
  apply Z.leb_le in G.
  assert (Hlow : M mod 2 ^ 10 = 0) by exact (hy_low x M (Dyadic.dy_exp da) (proj1 HM) Va).
  change (Limbs.limb (M :: nil) 0) with M.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (HMs : M = 2 ^ 10 * (M / 2 ^ 10))
    by (pose proof (Z.div_mod M (2 ^ 10) ltac:(lia)); lia).
  set (s0 := M / 2 ^ 10) in *.
  assert (Hs0 : 2 ^ 53 <= s0 < 2 ^ 54) by lia.
  assert (Vs : Limbs.val (s0 :: nil) = s0) by (cbn [Limbs.val]; ring).
  assert (Os : limbs_ok (s0 :: nil)) by (apply limbs_ok_cons; split; [lia | constructor]).
  assert (Hs1 : 2 ^ 53 <= Limbs.val (s0 :: nil)) by (rewrite Vs; lia).
  assert (Hs2 : 2 * Limbs.val (s0 :: nil) + 1 < 2 ^ (64 * Z.of_nat 3)).
  { rewrite Vs. change (64 * Z.of_nat 3) with 192. lia. }
  assert (HE : - 2 ^ 62 <= Dyadic.dy_exp da + 10 <= 2 ^ 62) by lia.
  destruct (odd_correct 3 false (s0 :: nil) (Dyadic.dy_exp da + 10) true Hn Os Hs1 Hs2 HE)
    as (d & Hd & Od & Vd).
  rewrite Vs in Vd.
  assert (Hg27 : 27 <= Dyadic.dy_exp da - Dyadic.dy_exp db) by lia.
  destruct (hypot_cut M m (Dyadic.dy_exp da) (Dyadic.dy_exp db) HM Hm Hg27) as (C1 & C2).
  rewrite <- Hsum in C1, C2.
  (* [s 2^(e + 10) = M 2^e]. *)
  assert (B10 : bpow radix2 (Dyadic.dy_exp da + 10) = (bpow radix2 (Dyadic.dy_exp da) * 1024)%R).
  { rewrite bpow_plus. reflexivity. }
  assert (RM : IZR M = (IZR s0 * 1024)%R).
  { rewrite HMs at 1. rewrite mult_IZR. change (IZR (2 ^ 10)) with 1024%R. ring. }
  rewrite RM in C1. rewrite plus_IZR, RM in C2. change (IZR (2 ^ 10)) with 1024%R in C2.
  exists d, s0, (Dyadic.dy_exp da + 10), true.
  split; [exact Hd |]. split; [exact Od |]. split; [exact Vd |]. split; [lia |].
  rewrite B10, plus_IZR. split; [split; lra |].
  split; [discriminate | intros H; lra].
- (* [hypot_exact_branch]: [E = f - h]. *)
  apply Z.leb_gt in G.
  assert (Hg : 0 <= Dyadic.dy_exp da - Dyadic.dy_exp db <= 26) by lia.
  destruct (hypot_exact_branch M m (Dyadic.dy_exp db) (Dyadic.dy_exp da - Dyadic.dy_exp db)
              HM Hm Hg) as (s & h & b & Heq & Os & Hs & Hh & Hw & Hb).
  cbv zeta in Heq. rewrite Heq.
  assert (HE : - 2 ^ 62 <= Dyadic.dy_exp db - h <= 2 ^ 62) by lia.
  assert (Hs1 : 2 ^ 53 <= Limbs.val s) by lia.
  assert (Hs2 : 2 * Limbs.val s + 1 < 2 ^ (64 * Z.of_nat 3)).
  { change (64 * Z.of_nat 3) with 192. lia. }
  destruct (odd_correct 3 false s (Dyadic.dy_exp db - h) b Hn Os Hs1 Hs2 HE) as (d & Hd & Od & Vd).
  rewrite (hy_sum M m (Dyadic.dy_exp da) (Dyadic.dy_exp db) h) in Hsum by lia.
  set (X := (M * M * 2 ^ (2 * (Dyadic.dy_exp da - Dyadic.dy_exp db)) + m * m) * 2 ^ (2 * h))
    in *.
  assert (HX0 : 0 <= X) by nia.
  destruct (hy_window (Limbs.val s) X (Dyadic.dy_exp db - h) ltac:(lia) Hw) as (W & Wb).
  (* [sqrt(x^2 + y^2) = sqrt(X) 2^(f - h)]. *)
  assert (Hr : sqrt (B2R x * B2R x + B2R y * B2R y)
               = (sqrt (IZR X) * bpow radix2 (Dyadic.dy_exp db - h))%R).
  { rewrite Hsum, sqrt_mult_alt by (apply IZR_le; exact HX0).
    rewrite sqrt_square by (apply Rlt_le, bpow_gt_0). reflexivity. }
  exists d, (Limbs.val s), (Dyadic.dy_exp db - h), b.
  rewrite Hr.
  split; [exact Hd |]. split; [exact Od |]. split; [exact Vd |]. split; [exact Hs1 |].
  split; [exact W |].
  split; intros H; [apply Wb, Hb, H | apply Hb, Wb, H].
Qed.

(** ** The theorem *)

Lemma hypot_odd_correct :
  forall x y,
  is_finite x = true -> is_finite y = true -> B2R x <> 0%R -> B2R y <> 0%R ->
  exists d s E b,
  DyadicRoot.hypot_odd x y = Some d /\ dy_ok 3 d /\
  Dyadic.dy_R d = (IZR (2 * s + Z.b2z b) * bpow radix2 (E - 1))%R /\
  2 ^ 53 <= s /\
  (IZR s * bpow radix2 E <= sqrt (B2R x * B2R x + B2R y * B2R y)
     < IZR (s + 1) * bpow radix2 E)%R /\
  (b = false <-> sqrt (B2R x * B2R x + B2R y * B2R y) = (IZR s * bpow radix2 E)%R).
Proof.
intros x y Fx Fy Hx0 Hy0.
destruct (ge (fabs x) (fabs y)) eqn:Hge.
{ apply hypot_odd_ge; assumption. }
(* [|x| < |y|]: [hypot_odd] swaps them, as [hypot_odd y x] does. *)
assert (Fax : is_finite (fabs x) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fx).
assert (Fay : is_finite (fabs y) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fy).
assert (Hge' : ge (fabs y) (fabs x) = true).
{ pose proof Hge as G0. unfold ge in G0 |- *.
  rewrite Bleb_correct in G0 |- * by assumption.
  destruct (Rle_bool_spec (B2R (fabs y)) (B2R (fabs x))) as [L | L]; [discriminate G0 |].
  apply Rle_bool_true. lra. }
assert (Hs : DyadicRoot.hypot_odd x y = DyadicRoot.hypot_odd y x).
{ unfold DyadicRoot.hypot_odd. rewrite Hge, Hge'. reflexivity. }
destruct (hypot_odd_ge y x Fy Fx Hy0 Hx0 Hge') as (d & s & E & b & H1 & H2 & H3 & H4 & H5 & H6).
exists d, s, E, b.
rewrite Hs, (Rplus_comm (B2R x * B2R x)).
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))).
Qed.
