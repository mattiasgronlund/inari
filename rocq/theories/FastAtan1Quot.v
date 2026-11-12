(** * The quotients of the first stage of the fast path of atan

    [DyadicAtan.fast_quot n d] of [Model.v] is [n / d] in double-double
    for [n] and [d] in [[1, 2)], and [DyadicAtan.fast_recip t] is [1 / t]
    for [t] in [(1, 2^54)]: [qh] is the quotient rounded to nearest, the
    remainder [n - qh d] is an [f64] computed exactly
    ([FastAtan1Rem.atan1_rem]), and [ql] is the remainder divided by [d],
    or times [qh]. They are within [2^-105] and [2^-104] of the quotient
    relatively ([fast_quot_correct], [fast_recip_correct]), [qh] is the
    rounding of [qh + ql] for [fast_quot] ([FastAtan1Mid.quot_mid]), and
    each returns the same with and without an FMA ([fast_quot_fma],
    [fast_recip_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error Sterbenz Relative.
From Inari Require Import Model Mpfr Encoding Elementary TwoSum TwoProduct DyDriver NearF64
  FastRound FastRoundErr FastDiv CancelLanes FastHypPos FastAtanTables FastAtanIdent
  FastAtanPoly FastAtanCore FastAtan1Rem FastAtan1Mid.
From Inari Require FastExpErr FastExpReduce ConstTight FastAtanQuot DyExpCore.

Open Scope R_scope.

(** ** Helpers *)

(** The hypotheses of [atan1_rem] for the arguments of [fast_quot] and
    [fast_recip]. *)
Local Lemma num_ok :
  forall n : f64, 1 <= B2R n < 2 -> bpow radix2 (-80) <= Rabs (B2R n) <= 4.
Proof.
intros n Hn. rewrite Rabs_pos_eq by lra.
assert (bpow radix2 (-80) <= 1) by (cbn [bpow radix_val radix2]; lra). lra.
Qed.

Local Lemma den_ok :
  forall d : f64, 1 <= B2R d < 2 -> / 2 <= B2R d <= bpow radix2 54.
Proof.
intros d Hd. assert (2 <= bpow radix2 54) by (cbn [bpow radix_val radix2]; lra). lra.
Qed.

Local Lemma den_ok' :
  forall t : f64, 1 < B2R t < bpow radix2 54 -> / 2 <= B2R t <= bpow radix2 54.
Proof. intros t Ht. lra. Qed.

Local Notation G := (generic_format radix2 fexp64).

(** [x / y] of finite [f64]s with an exact result of at most 16 in
    magnitude is finite and rounded to nearest, as [FastDiv]'s Local
    [div_e]. *)
Local Lemma div_e :
  forall x y, is_finite x = true -> is_finite y = true -> B2R y <> 0 ->
  Rabs (B2R x / B2R y) <= 16 ->
  is_finite (div x y) = true /\ B2R (div x y) = RN (B2R x / B2R y).
Proof.
intros x y Fx Fy Hy H.
destruct (RN_below_max _ (FastExpErr.small_le_max _ H)) as (Hlt & _).
generalize (@Bdiv_correct 53 1024 _ _ mode_NE x y Hy).
rewrite Rlt_bool_true by exact Hlt.
intros (HR & HF & _).
change (Bdiv mode_NE x y) with (div x y) in HR, HF.
rewrite Fx in HF. split; [exact HF | exact HR].
Qed.

Local Lemma one_fin : is_finite DyadicExp.one = true.
Proof. reflexivity. Qed.

Local Lemma one_ok : bpow radix2 (-80) <= Rabs (B2R DyadicExp.one) <= 4.
Proof.
rewrite DyExpCore.dexp_one_R, Rabs_R1.
assert (bpow radix2 (-80) <= 1) by (cbn [bpow radix_val radix2]; lra). lra.
Qed.

(** The conclusions of [FastAtanQuot.quot_facts], with [2^-105] for
    [2^-98]. *)
Theorem fast_quot_correct :
  forall fma n d qh ql,
  is_finite n = true -> is_finite d = true -> 1 <= B2R n < 2 -> 1 <= B2R d < 2 ->
  DyadicAtan.fast_quot fma n d = (qh, ql) ->
  is_finite qh = true /\ is_finite ql = true /\ B2R qh = RN (B2R qh + B2R ql) /\
  Rabs (B2R qh + B2R ql - B2R n / B2R d) <= bpow radix2 (-105) * (B2R n / B2R d) /\
  / 2 <= B2R qh < 2 /\ Rabs (B2R ql) <= bpow radix2 (-53) * B2R qh /\
  / 2 < B2R n / B2R d < 2.
Proof.
intros fma n d qh ql Fn Fd Hn Hd E.
destruct (atan1_rem fma n d Fn Fd (num_ok _ Hn) (den_ok _ Hd)) as (Fq & Rq & _ & Epe & Fa & Ra).
cbv [DyadicAtan.fast_quot] in E. rewrite Epe in E.
apply pair_equal_spec in E. destruct E as (Eh & El). subst qh ql.
set (q := div n d) in *.
set (a := sub (sub n (mul q d)) (Generic.two_prod_err false q d (mul q d))) in *.
set (z := B2R n / B2R d) in *.
pose proof (FastAtanQuot.below_two n Fn (proj2 Hn)) as Hn2.
assert (B52 : 0 < bpow radix2 (-53) < bpow radix2 (-52) /\ bpow radix2 (-52) <= 1)
  by (cbn [bpow radix_val radix2]; lra).
(* [z = n / d] is in [(1/2, 2 - 2^-52]], as [n <= 2 - 2^-52] and [d] is
   in [[1, 2)]. *)
assert (Ez : z * B2R d = B2R n) by (unfold z; field; lra).
assert (Z1 : / 2 < z) by nra.
assert (Z2 : z <= 2 - bpow radix2 (-52)) by nra.
(* [qh = RN(z)] is in [[1/2, 2)], and within [2^-53 qh] of [z]. *)
assert (Q1 : / 2 <= B2R q).
{ rewrite Rq. apply round_ge_generic; [typeclasses eauto | typeclasses eauto | | lra].
  change (/ 2) with (bpow radix2 (-1)).
  apply generic_format_bpow. unfold FLT_exp. lia. }
assert (Q2 : B2R q < 2).
{ rewrite Rq. pose proof (FastAtanQuot.rn_below_two z ltac:(lra)). lra. }
assert (Lq : Rabs (z - B2R q) <= bpow radix2 (-53) * B2R q).
{ rewrite <- (Rabs_pos_eq (B2R q)) at 2 by lra. apply low_rel; [exact Rq |].
  rewrite Rabs_pos_eq by lra.
  assert (bpow radix2 (-1022) <= / 2) by (cbn [bpow radix_val radix2]; lra). lra. }
assert (S53 : bpow radix2 (-53) * B2R q <= bpow radix2 (-52))
  by (assert (bpow radix2 (-53) * 2 = bpow radix2 (-52)) by (cbn [bpow radix_val radix2]; lra);
      pose proof (bpow_gt_0 radix2 (-53)); nra).
(* The remainder [n - qh d] is [d (z - qh)], so [ql = RN((n - qh d) / d)]
   is [RN(z - qh)]. *)
assert (Ea : B2R a / B2R d = z - B2R q) by (rewrite Ra; unfold z; field; lra).
destruct (div_e a d Fa Fd ltac:(lra) ltac:(rewrite Ea; lra)) as (Fl & Rl).
rewrite Ea in Rl.
(* [|z - qh| <= 2^-53 qh], an [f64], so [ql = RN(z - qh)] is at most it
   in magnitude too. *)
assert (Gq : G (bpow radix2 (-53) * B2R q)).
{ rewrite Rmult_comm. apply mult_bpow_exact_FLT; [apply generic_format_B2R |].
  assert (M : (-53 <= mag radix2 (B2R q))%Z).
  { apply mag_ge_bpow. rewrite Rabs_pos_eq by lra. replace (-53 - 1)%Z with (-54)%Z by lia.
    assert (bpow radix2 (-54) <= / 2) by (cbn [bpow radix_val radix2]; lra). lra. }
  lia. }
assert (Ll : Rabs (B2R (div a d)) <= bpow radix2 (-53) * B2R q)
  by (rewrite Rl; apply abs_round_le_generic;
      [typeclasses eauto | typeclasses eauto | exact Gq | exact Lq]).
split; [exact Fq |]. split; [exact Fl |]. split.
{ (* [FastAtan1Mid.quot_mid]: [qh = RN(qh + RN(z - qh))] for [qh = RN(z)]. *)
  rewrite Rl, Rq. symmetry. unfold z.
  apply quot_mid; [apply generic_format_B2R | apply generic_format_B2R | exact Hn | exact Hd]. }
split.
{ (* [qh + ql - z = RN(z - qh) - (z - qh)], one rounding of a number of at
     most [2^-53 qh], and [z >= (1 - 2^-53) qh]. *)
  replace (B2R q + B2R (div a d) - z) with (RN (z - B2R q) - (z - B2R q)) by (rewrite Rl; ring).
  pose proof (FastExpErr.rn_err (z - B2R q)) as Er.
  assert (Lz : B2R q - bpow radix2 (-53) * B2R q <= z)
    by (apply Rabs_le_inv in Lq; lra).
  assert (Lr : bpow radix2 (-53) * Rabs (z - B2R q) <=
    bpow radix2 (-53) * (bpow radix2 (-53) * B2R q))
    by (apply Rmult_le_compat_l; [apply bpow_ge_0 | exact Lq]).
  assert (Lz' : bpow radix2 (-105) * (B2R q - bpow radix2 (-53) * B2R q) <= bpow radix2 (-105) * z)
    by (apply Rmult_le_compat_l; [apply bpow_ge_0 | exact Lz]).
  clear - Er Lr Lz' Q1.
  cbn [bpow radix_val radix2] in *. lra. }
split; [lra |]. split; [exact Ll |]. lra.
Qed.

Theorem fast_quot_fma :
  forall n d,
  is_finite n = true -> is_finite d = true -> 1 <= B2R n < 2 -> 1 <= B2R d < 2 ->
  DyadicAtan.fast_quot true n d = DyadicAtan.fast_quot false n d.
Proof.
intros n d Fn Fd Hn Hd.
destruct (atan1_rem true n d Fn Fd (num_ok _ Hn) (den_ok _ Hd)) as (_ & _ & _ & Epe & _).
cbv [DyadicAtan.fast_quot]. rewrite Epe. reflexivity.
Qed.

Theorem fast_recip_correct :
  forall fma t qh ql,
  is_finite t = true -> 1 < B2R t < bpow radix2 54 ->
  DyadicAtan.fast_recip fma t = (qh, ql) ->
  is_finite qh = true /\ is_finite ql = true /\
  bpow radix2 (-54) <= B2R qh <= 1 /\ Rabs (B2R ql) <= bpow radix2 (-53) * B2R qh /\
  Rabs (B2R qh + B2R ql - / B2R t) <= bpow radix2 (-104) * / B2R t.
Proof.
intros fma t qh ql Ft Ht E.
destruct (atan1_rem fma DyadicExp.one t one_fin Ft one_ok (den_ok' _ Ht))
  as (Fq & Rq & _ & Epe & Fa & Ra).
cbv [DyadicAtan.fast_recip] in E. rewrite Epe in E.
apply pair_equal_spec in E. destruct E as (Eh & El). subst qh ql.
rewrite DyExpCore.dexp_one_R in Rq, Ra. rewrite Rdiv_1_l in Rq.
set (q := div DyadicExp.one t) in *.
set (a := sub (sub DyadicExp.one (mul q t)) (Generic.two_prod_err false q t (mul q t))) in *.
set (T := B2R t) in *. set (Q := B2R q) in *. set (A := B2R a) in *.
set (iT := / T) in *.
assert (ET : iT * T = 1) by (unfold iT; field; lra).
assert (B54 : bpow radix2 (-54) * bpow radix2 54 = 1 /\ 0 < bpow radix2 (-54) <= 1)
  by (cbn [bpow radix_val radix2]; lra).
(* [1/t] is in [(2^-54, 1)]. *)
assert (I1 : bpow radix2 (-54) < iT < 1) by nra.
(* [qh = RN(1/t)] is in [[2^-54, 1]]. *)
assert (Q1 : bpow radix2 (-54) <= Q).
{ rewrite Rq. apply round_ge_generic; [typeclasses eauto | typeclasses eauto | | lra].
  apply generic_format_bpow. unfold FLT_exp. lia. }
assert (Q2 : Q <= 1).
{ rewrite Rq. apply round_le_generic; [typeclasses eauto | typeclasses eauto | | lra].
  change 1 with (bpow radix2 0). apply generic_format_bpow. unfold FLT_exp. lia. }
(* [|qh - 1/t| <= 2^-53 / t], relatively to [1/t] and without the
   [2^-1075] of [FastExpErr.rn_err], as [1/t] is normal. *)
assert (Lq : Rabs (Q - iT) <= bpow radix2 (-53) * iT).
{ assert (N : bpow radix2 (-1074 + 53 - 1) <= Rabs iT).
  { rewrite Rabs_pos_eq by lra.
    assert (bpow radix2 (-1074 + 53 - 1) <= bpow radix2 (-54)) by (apply bpow_le; lia). lra. }
  assert (H : Rabs (RN iT - iT) <= / 2 * bpow radix2 (-52) * Rabs iT)
    by exact (relative_error_N_FLT radix2 (-1074) 53 eq_refl (fun z => negb (Z.even z)) iT N).
  assert (E2 : / 2 * bpow radix2 (-52) = bpow radix2 (-53)) by (cbn [bpow radix_val radix2]; lra).
  rewrite E2, (Rabs_pos_eq iT) in H by lra.
  rewrite Rq. exact H. }
(* So the remainder [a = 1 - qh t = t (1/t - qh)] is at most [2^-53]
   exactly. *)
assert (La : Rabs A <= bpow radix2 (-53)).
{ replace A with (T * (iT - Q)) by (rewrite Ra; unfold iT; field; lra).
  rewrite Rabs_mult, (Rabs_pos_eq T), Rabs_minus_sym by lra.
  apply Rle_trans with (T * (bpow radix2 (-53) * iT)).
  - apply Rmult_le_compat_l; [lra | exact Lq].
  - right. unfold iT. field. lra. }
assert (LaQ : Rabs (A * Q) <= bpow radix2 (-53) * Q).
{ rewrite Rabs_mult, (Rabs_pos_eq Q) by lra.
  apply Rmult_le_compat_r; [lra | exact La]. }
assert (S53 : bpow radix2 (-53) <= 16) by (cbn [bpow radix_val radix2]; lra).
destruct (FastExpErr.mul_e a q Fa Fq ltac:(fold A Q; nra)) as (Fl & Rl & El).
fold A Q in Rl, El.
(* [2^-53 qh] is an [f64], so the rounding [ql] of [a qh] is at most it. *)
assert (Gq : G (bpow radix2 (-53) * Q)).
{ rewrite Rmult_comm. apply mult_bpow_exact_FLT; [apply generic_format_B2R |].
  assert (M : (-53 <= mag radix2 Q)%Z).
  { apply mag_ge_bpow. rewrite Rabs_pos_eq by lra.
    replace (-53 - 1)%Z with (-54)%Z by lia. exact Q1. }
  lia. }
split; [exact Fq |]. split; [exact Fl |]. split; [lra |]. split.
{ rewrite Rl.
  apply abs_round_le_generic; [typeclasses eauto | typeclasses eauto | exact Gq | exact LaQ]. }
(* [qh + qh a - 1/t = -a^2 / t] (Newton's step for [1/t]), so the error
   is [a^2 / t] plus the rounding of [a qh]. *)
assert (Id : Q + A * Q - iT = - (A * A * iT))
  by (rewrite Ra; unfold iT; field; lra).
replace (Q + B2R (mul a q) - iT) with ((B2R (mul a q) - A * Q) - A * A * iT) by lra.
assert (AA : A * A <= bpow radix2 (-53) * bpow radix2 (-53))
  by (apply Rabs_le_inv in La; pose proof (bpow_gt_0 radix2 (-53)); nra).
assert (AAi : 0 <= A * A * iT <= bpow radix2 (-53) * bpow radix2 (-53) * iT).
{ split.
  - apply Rmult_le_pos; [apply Rle_0_sqr | lra].
  - apply Rmult_le_compat_r; [lra | exact AA]. }
assert (Lr : bpow radix2 (-53) * Rabs (A * Q) <= bpow radix2 (-53) * (bpow radix2 (-53) * Q))
  by (apply Rmult_le_compat_l; [apply bpow_ge_0 | exact LaQ]).
assert (Lq' : Q <= iT + bpow radix2 (-53) * iT) by (apply Rabs_le_inv in Lq; lra).
assert (Lq'' : bpow radix2 (-106) * Q <= bpow radix2 (-106) * (iT + bpow radix2 (-53) * iT))
  by (apply Rmult_le_compat_l; [apply bpow_ge_0 | exact Lq']).
eapply Rle_trans; [apply Rabs_triang |].
rewrite Rabs_Ropp, (Rabs_pos_eq (A * A * iT)) by lra.
clear - El AAi Lr Lq'' I1.
cbn [bpow radix_val radix2] in *. lra.
Qed.

Theorem fast_recip_fma :
  forall t,
  is_finite t = true -> 1 < B2R t < bpow radix2 54 ->
  DyadicAtan.fast_recip true t = DyadicAtan.fast_recip false t.
Proof.
intros t Ft Ht.
destruct (atan1_rem true DyadicExp.one t one_fin Ft one_ok (den_ok' _ Ht)) as (_ & _ & _ & Epe & _).
cbv [DyadicAtan.fast_recip]. rewrite Epe. reflexivity.
Qed.
