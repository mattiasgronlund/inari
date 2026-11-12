(** * [cbrt] of the dyadic kernel

    [DyadicRoot.cbrt] and [DyadicRoot.cbrt_near] return, at every finite
    [x], [Rcbrt (B2R x)] rounded toward -inf or +inf ([cbrt_dir_correct])
    and to nearest ([cbrt_near_correct]), and [x] itself at the zeros,
    the infinities and NaN ([cbrt_special]). For [x <> 0],
    [|x| = M 2^e] with [2^63 <= M < 2^64] ([Dyadic.from_f64]), and for
    the [k] in [96, 98] with [e - k] a multiple of 3, [X = M 2^k] has
    [2^159 <= X < 2^162], so [s = floor(cbrt X)] ([icbrt_correct]) has
    [2^53 <= s < 2^54] and [cbrt |x| = cbrt X 2^((e - k) / 3)] lies in
    [s 2^E <= _ < (s + 1) 2^E] for [E = (e - k) / 3] ([Rcbrt_unique],
    [Rcbrt_lt]). [odd_correct] and [odd_window_dir] or [odd_window_near]
    then give the rounding, and [to_f64_correct] or [to_f64_near_correct]
    the [f64]. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs Elementary Decompose DyRound DyConv DyConvNear NearF64
  RootReal RootRound DyIcbrt.
From Inari Require FastCbrt.

Open Scope Z_scope.

(** ** Lemmas *)

(** [x == 0.0] of a finite [x] says whether [x] is 0. *)
Local Lemma cb_eq_zero :
  forall x : f64, is_finite x = true -> (eq x zero = true <-> B2R x = 0%R).
Proof.
intros x Fx. unfold eq. rewrite Beqb_correct by (first [exact Fx | reflexivity]).
change (B2R zero) with 0%R.
destruct (Req_bool_spec (B2R x) 0) as [H | H]; split; intros H';
  first [exact H | reflexivity | discriminate H' | contradiction].
Qed.

Local Lemma cb_IZR_pow2 : forall e, 0 <= e -> IZR (2 ^ e) = bpow radix2 e.
Proof. intros e He. exact (IZR_Zpower radix2 e He). Qed.

Local Lemma cb_cbrt0 : Rcbrt 0 = 0%R.
Proof. apply Rcbrt_unique. ring. Qed.

(** [s = floor(cbrt X)] for [2^159 <= X < 2^162] has [2^53 <= s < 2^54],
    as [(2^53)^3 = 2^159] and [(2^54)^3 = 2^162]. *)
Local Lemma cb_root_bounds :
  forall s X, s ^ 3 <= X < (s + 1) ^ 3 -> 2 ^ 159 <= X < 2 ^ 162 -> 2 ^ 53 <= s < 2 ^ 54.
Proof.
intros s X Hs HX. split.
- destruct (Z_lt_le_dec s (2 ^ 53)) as [H | H]; [exfalso | exact H].
  destruct (Z_lt_le_dec (s + 1) 0) as [H0 | H0].
  + (* The cube of a negative number is negative. *)
    assert (H1 : 0 < (s + 1) * (s + 1)) by (apply Z.mul_neg_neg; lia).
    assert (H2 : (s + 1) * (s + 1) * (s + 1) < 0) by (apply Z.mul_pos_neg; lia).
    replace ((s + 1) ^ 3) with ((s + 1) * (s + 1) * (s + 1)) in Hs by ring. lia.
  + assert (H1 : (s + 1) ^ 3 <= 2 ^ 159).
    { change (2 ^ 159) with ((2 ^ 53) ^ 3). apply Z.pow_le_mono_l. lia. }
    lia.
- destruct (Z_lt_le_dec s (2 ^ 54)) as [H | H]; [exact H | exfalso].
  assert (H1 : 2 ^ 162 <= s ^ 3).
  { change (2 ^ 162) with ((2 ^ 54) ^ 3). apply Z.pow_le_mono_l. lia. }
  lia.
Qed.

(** [DyadicRoot.cbrt_odd] of a finite nonzero [x] is
    [(-1)^neg (2 s + b) 2^(E - 1)] for the [s], [E] and [b] that
    [odd_window_dir] and [odd_window_near] ask for, with
    [cbrt x = (-1)^neg r]: [|x| = M 2^e = X 2^(3 E)] for [X = M 2^k], so
    [cbrt |x| = cbrt(X) 2^E] ([Rcbrt_unique]), and
    [s^3 <= X < (s + 1)^3] puts [cbrt X] in [[s, s + 1)] ([Rcbrt_lt]),
    at [s] exactly when [X = s^3], that is, when [b] is false. *)
Local Lemma cbrt_odd_correct :
  forall x,
  is_finite x = true -> B2R x <> 0%R ->
  exists d neg s E b r,
  DyadicRoot.cbrt_odd x = Some d /\ dy_ok 1 d /\
  Dyadic.dy_R d = cond_Ropp neg (IZR (2 * s + Z.b2z b) * bpow radix2 (E - 1))%R /\
  2 ^ 53 <= s /\
  (IZR s * bpow radix2 E <= r < IZR (s + 1) * bpow radix2 E)%R /\
  (b = false <-> r = (IZR s * bpow radix2 E)%R) /\
  Rcbrt (B2R x) = cond_Ropp neg r.
Proof.
intros x Fx Hx0.
assert (Hn : level_ok 1) by (unfold level_ok; lia).
destruct (from_f64_correct 1 x Hn Fx) as (a & Ea & Oa & Sa & Va).
destruct (dy_cases 1 a Hn Oa) as [(_ & _ & _ & _ & H0) | (_ & HM & _)].
{ rewrite Va in H0. contradiction. }
assert (HM' : 2 ^ 63 <= Limbs.val (Dyadic.dy_m a) < 2 ^ 64) by exact HM.
clear HM.
destruct Oa as (Ma & _ & _ & _).
unfold exp_small in Sa.
unfold DyadicRoot.cbrt_odd. rewrite Ea. cbv beta iota zeta.
(* [k] is 96, 97 or 98, and [e - k = 3 E]. *)
set (k := 96 + (Dyadic.dy_exp a - 96) mod 3).
assert (Hk : 96 <= k <= 98).
{ unfold k. pose proof (Z.mod_pos_bound (Dyadic.dy_exp a - 96) 3 ltac:(lia)). lia. }
set (E := (Dyadic.dy_exp a - 96) / 3).
assert (HE : Dyadic.dy_exp a = k + 3 * E).
{ unfold k, E. pose proof (Z.div_mod (Dyadic.dy_exp a - 96) 3 ltac:(lia)). lia. }
assert (HEb : - 2 ^ 62 <= E <= 2 ^ 62) by lia.
assert (Hq : Z.quot (Dyadic.dy_exp a - k) 3 = E).
{ rewrite HE. replace (k + 3 * E - k) with (E * 3) by ring. apply Z.quot_mul. lia. }
rewrite Hq.
(* [X = M 2^k] fits in 3 limbs, with [2^159 <= X < 2^162]. *)
destruct (shl_into_correct 3 (Dyadic.dy_m a) k Ma ltac:(lia)) as (Xok & Xl & Xv).
set (X := Limbs.shl_into 3 (Dyadic.dy_m a) k) in *.
assert (H2k : 2 ^ 96 <= 2 ^ k <= 2 ^ 98) by (split; apply Z.pow_le_mono_r; lia).
assert (HX : Limbs.val X = Limbs.val (Dyadic.dy_m a) * 2 ^ k).
{ rewrite Xv. apply Z.mod_small. change (64 * Z.of_nat 3) with 192. nia. }
assert (HXb : 2 ^ 159 <= Limbs.val X < 2 ^ 162) by (rewrite HX; nia).
destruct (icbrt_correct X Xok Xl HXb) as (s & b & Hi & Hs3 & Hb).
rewrite Hi. cbv beta iota.
destruct (cb_root_bounds s (Limbs.val X) Hs3 HXb) as (Hs53 & Hs54).
assert (Vs : Limbs.val (s :: nil) = s) by (cbn [Limbs.val]; ring).
assert (Os : limbs_ok (s :: nil)) by (apply limbs_ok_cons; split; [lia | constructor]).
assert (Hs1 : 2 ^ 53 <= Limbs.val (s :: nil)) by (rewrite Vs; lia).
assert (Hs2 : 2 * Limbs.val (s :: nil) + 1 < 2 ^ (64 * Z.of_nat 1)).
{ rewrite Vs. change (64 * Z.of_nat 1) with 64. lia. }
destruct (odd_correct 1 (Dyadic.dy_neg a) (s :: nil) E b Hn Os Hs1 Hs2 HEb)
  as (d & Hd & Od & Vd).
rewrite Vs in Vd.
(* [|x| = X 2^(3 E)]. *)
pose proof (bpow_gt_0 radix2 E) as HbE.
assert (Hx : B2R x = cond_Ropp (Dyadic.dy_neg a)
                       (IZR (Limbs.val X) * (bpow radix2 E * bpow radix2 E * bpow radix2 E))%R).
{ rewrite <- Va. unfold Dyadic.dy_R, cond_Ropp. cbv zeta.
  rewrite HX, mult_IZR, cb_IZR_pow2 by lia.
  replace (Dyadic.dy_exp a) with (k + (E + (E + E))) by lia.
  rewrite !bpow_plus. destruct (Dyadic.dy_neg a); ring. }
(* [cbrt |x| = c 2^E] for [c = cbrt X]. *)
set (c := Rcbrt (IZR (Limbs.val X))).
assert (Hc3 : (c * c * c = IZR (Limbs.val X))%R) by (unfold c; apply Rcbrt_cube).
set (r := (c * bpow radix2 E)%R).
assert (Hr : Rcbrt (B2R x) = cond_Ropp (Dyadic.dy_neg a) r).
{ rewrite Hx.
  assert (H3 : Rcbrt (IZR (Limbs.val X) * (bpow radix2 E * bpow radix2 E * bpow radix2 E)) = r).
  { apply Rcbrt_unique. unfold r. rewrite <- Hc3. ring. }
  destruct (Dyadic.dy_neg a); cbn [cond_Ropp]; [rewrite Rcbrt_opp |]; rewrite H3; reflexivity. }
(* [s <= c < s + 1], from [s^3 <= X < (s + 1)^3]. *)
assert (Hcs : forall t, Rcbrt (IZR (t ^ 3)) = IZR t).
{ intros t. apply Rcbrt_unique. rewrite <- !mult_IZR. f_equal. ring. }
assert (Hlo : (IZR s <= c)%R).
{ destruct (Z.eq_dec (s ^ 3) (Limbs.val X)) as [H | H].
  - unfold c. rewrite <- H, Hcs. apply Rle_refl.
  - rewrite <- (Hcs s). unfold c. apply Rlt_le, Rcbrt_lt, IZR_lt. lia. }
assert (Hhi : (c < IZR (s + 1))%R).
{ rewrite <- (Hcs (s + 1)). unfold c. apply Rcbrt_lt, IZR_lt. lia. }
exists d, (Dyadic.dy_neg a), s, E, b, r.
split; [exact Hd |]. split; [exact Od |]. split; [exact Vd |]. split; [exact Hs53 |].
split.
{ unfold r. split.
  - apply Rmult_le_compat_r; [apply Rlt_le; exact HbE | exact Hlo].
  - apply Rmult_lt_compat_r; [exact HbE | exact Hhi]. }
split; [| exact Hr].
split.
- (* [b] is false: [X = s^3], so [c = s]. *)
  intros Hb0.
  assert (H3 : s ^ 3 = Limbs.val X).
  { destruct (Z.eq_dec (s ^ 3) (Limbs.val X)) as [H | H]; [exact H |].
    assert (b = true) by (apply Hb; lia). congruence. }
  unfold r, c. rewrite <- H3, Hcs. reflexivity.
- (* [c = s], so [X = c^3 = s^3], and [b] is false. *)
  intros Hr0.
  assert (Hcs' : c = IZR s).
  { apply Rmult_eq_reg_r with (bpow radix2 E); [exact Hr0 | apply Rgt_not_eq; exact HbE]. }
  assert (H3 : Limbs.val X = s ^ 3).
  { apply eq_IZR. rewrite <- Hc3, Hcs', <- !mult_IZR. f_equal. ring. }
  destruct b; [| reflexivity]. exfalso.
  assert (s ^ 3 < Limbs.val X) by (apply Hb; reflexivity). lia.
Qed.

(** ** The theorems *)

Theorem cbrt_dir_correct :
  forall x up,
  is_finite x = true ->
  exists v, DyadicRoot.cbrt x up = Some v /\
  mpfr_round f64_format (if up then RNDU else RNDD) (Rcbrt (B2R x)) (with_val v).
Proof.
intros x up Fx.
unfold DyadicRoot.cbrt. rewrite Fx.
destruct (eq x zero) eqn:Z0; cbn [orb negb].
- (* [cbrt 0 = 0], and a zero rounds to itself both ways. *)
  destruct (proj1 (Decompose.eq_zero_iff x) Z0) as (sx & ->).
  exists (B754_zero sx). split; [reflexivity |].
  change (B2R (B754_zero sx)) with 0%R. rewrite cb_cbrt0.
  assert (F0 : f64_format 0%R) by (exists zero; split; reflexivity).
  destruct up; cbn [with_val mpfr_round].
  + split; [exact F0 |]. split; [apply Rle_refl |]. intros g _ Hg. exact Hg.
  + split; [exact F0 |]. split; [apply Rle_refl |]. intros g _ Hg. exact Hg.
- assert (Hx0 : B2R x <> 0%R).
  { intros H. rewrite (proj2 (cb_eq_zero x Fx) H) in Z0. discriminate Z0. }
  (* The fast path, where it returns. *)
  destruct (DyadicRoot.fast_cbrt_dir false x up) as [w |] eqn:F.
  { exists w. split; [reflexivity |].
    exact (FastCbrt.fast_cbrt_dir_correct false x up w Fx Hx0 F). }
  destruct (cbrt_odd_correct x Fx Hx0)
    as (d & neg & s & E & b & r & Hd & Od & Vd & Hs & Hw & Hb & Hr).
  rewrite Hd.
  assert (Hn : level_ok 1) by (unfold level_ok; lia).
  destruct (to_f64_correct 1 d up Hn Od) as (v & Ev & Rv).
  exists v. split; [exact Ev |].
  rewrite Hr. apply (proj1 (odd_window_dir neg s E b r up (with_val v) Hs Hw Hb)).
  rewrite <- Vd. exact Rv.
Qed.

Theorem cbrt_near_correct :
  forall x,
  is_finite x = true ->
  exists v, DyadicRoot.cbrt_near x = Some v /\ near_round (Rcbrt (B2R x)) v.
Proof.
intros x Fx.
unfold DyadicRoot.cbrt_near. rewrite Fx.
destruct (eq x zero) eqn:Z0; cbn [orb negb].
- (* [cbrt 0 = 0], and a zero rounds to itself. *)
  destruct (proj1 (Decompose.eq_zero_iff x) Z0) as (sx & ->).
  exists (B754_zero sx). split; [reflexivity |].
  change (B2R (B754_zero sx)) with 0%R. rewrite cb_cbrt0.
  unfold near_round. rewrite Rabs_R0.
  destruct (Rle_dec _ _) as [H | _].
  { assert (bpow radix2 970 < bpow radix2 1024)%R by (apply bpow_lt; lia). lra. }
  split; [reflexivity |]. split.
  + rewrite round_0 by auto with typeclass_instances. reflexivity.
  + intros H. exfalso. apply H. reflexivity.
- assert (Hx0 : B2R x <> 0%R).
  { intros H. rewrite (proj2 (cb_eq_zero x Fx) H) in Z0. discriminate Z0. }
  (* The fast path, where it returns. *)
  destruct (DyadicRoot.fast_cbrt_near false x) as [w |] eqn:F.
  { exists w. split; [reflexivity |].
    exact (FastCbrt.fast_cbrt_near_correct false x w Fx Hx0 F). }
  destruct (cbrt_odd_correct x Fx Hx0)
    as (d & neg & s & E & b & r & Hd & Od & Vd & Hs & Hw & Hb & Hr).
  rewrite Hd.
  assert (Hn : level_ok 1) by (unfold level_ok; lia).
  destruct (to_f64_near_correct 1 d Hn Od) as (v & Ev & Rv & _).
  exists v. split; [exact Ev |].
  rewrite Hr. apply (proj1 (odd_window_near neg s E b r v Hs Hw Hb)).
  rewrite <- Vd. exact Rv.
Qed.

Theorem cbrt_special :
  forall x up,
  is_finite x = false \/ B2R x = 0%R ->
  DyadicRoot.cbrt x up = Some x /\ DyadicRoot.cbrt_near x = Some x.
Proof.
intros x up H.
unfold DyadicRoot.cbrt, DyadicRoot.cbrt_near.
destruct (is_finite x) eqn:Fx.
- destruct H as [H | H]; [discriminate H |].
  rewrite (proj2 (cb_eq_zero x Fx) H). split; reflexivity.
- destruct (eq x zero); split; reflexivity.
Qed.
