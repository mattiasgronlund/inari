(** * [tan] of intervals is the tightest, with the strongest decoration

    [Interval::tan_impl] reduces by [FRAC_PI_2] as [Interval::sin] does
    and reads the parity [q] of [qa]. The poles of [tan] are the odd
    multiples of [PI / 2], and it increases between two of them
    ([TrigPieces.v]). It returns [[tan_rd(a), tan_ru(b)]] with [com] when
    [x] lies between two poles: for even [qa], if [n = 0], and for odd
    [qa], if [n <= 1]. Otherwise it returns [[-inf, +inf]] with [trv]. If
    [a == b], [n] is 0 whatever [q] is, so the first case is taken whether
    or not [a] is a pole. The proofs derive that it is not from the
    irrationality of π ([pi_irrational] in [PiIrrational.v]).

    The [(q, n)] that the branches test come from one of two places. The
    floors [qa] and [qb] of the bounds of [x / FRAC_PI_2] are kept if
    [n = 0], if [b - a], rounded to nearest, is at least 4, or if
    [floors_exact] certifies them as the floors of [a / (PI / 2)] and
    [b / (PI / 2)] ([floors_exact_ok] in [TrigCert.v]). Every real of [x]
    lies in [[qa * (PI / 2), (qb + 1) * (PI / 2))], and [qa * (PI / 2)] is
    strictly below [a] unless [qa] is 0, so each [com] case puts [x]
    between two poles, and [[tan_rd(a), tan_ru(b)]] is the tightest. In
    the [trv] case, [x] holds a pole: its floors are exact, so [(a, b]]
    holds an odd multiple of [PI / 2], or [x] is more than [PI] wide.
    Otherwise [quadrants] gives the exact floors modulo 4 and a count [n]
    that is [kb - ka] below 4 and at least 4 otherwise
    ([quadrants_correct] in [TrigCount.v]); the branches read the same
    from those. So the result is the tightest for
    every [x] ([tan_correct]), [com] holds when it is returned, and [trv]
    is returned only if [x] is empty or holds a pole, so the decoration is
    the strongest ([dec_tan_correct]). *)

From Stdlib Require Import ZArith Reals Lra Lia QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr ComCommon Integer Encoding
  Decompose PiBounds TrigPieces TrigReduce TrigBranch TrigQuad TrigCount TrigCert
  DecBinary MonoInc Sqrt ElemDec.

Open Scope R_scope.

(** ** Helpers *)

(** The float constants that the tests of [Interval::tan_impl] compare. *)
Lemma tn_consts :
  Model.eq Model.zero Model.zero = true /\ Model.eq Model.zero (of_u64 1) = false /\
  Model.eq (of_u64 1) Model.zero = false /\ Model.eq (of_u64 1) (of_u64 1) = true /\
  Model.lt Model.zero (of_u64 1) = true /\ Model.lt Model.zero (of_u64 2) = true /\
  Model.lt (B754_infinity false) (of_u64 1) = false /\
  Model.lt (B754_infinity false) (of_u64 2) = false /\
  Model.eq (B754_infinity false) Model.zero = false /\
  Model.le (of_u64 4) (B754_infinity false) = true.
Proof.
vm_compute. repeat split.
Qed.

Lemma tn_fin_nan : forall w : f64, is_finite w = true -> is_nan w = false.
Proof.
intros [s|s| |s mw ew Hw] F; try discriminate F; reflexivity.
Qed.

Lemma tn_mul_le : forall u v w, 0 < w -> u <= v -> u * w <= v * w.
Proof.
intros u v w Hw H. apply Rmult_le_compat_r; lra.
Qed.

(** An interval that holds [[r, t]] with [t - r >= PI] holds a pole, and
    [tan] takes values beyond any bound on it ([tan_wide]). *)
Lemma tn_wide :
  forall x r t, PI <= t - r -> (forall s, r <= s <= t -> mem s x) ->
  is_tightest (image_dom tan_dom tan x) Interval.ENTIRE /\
  ~ (forall s, mem s x -> tan_dom s).
Proof.
intros x r t Hw Hm. split.
- apply br_entire_tight; intros M;
    destruct (tan_wide r t M ltac:(lra)) as (r1 & t1 & Hr1 & D1 & M1 & Ht1 & D2 & M2).
  + exists r1. split; [exact (Hm r1 Hr1)|]. split; assumption.
  + exists t1. split; [exact (Hm t1 Ht1)|]. split; assumption.
- intros HD. destruct (tan_wide_pole r t ltac:(lra)) as (p & Hp & Np).
  exact (Np (HD p (Hm p Hp))).
Qed.

(** A nonempty interval with an infinite bound holds [[r, r + PI]] or
    [[r - PI, r]] for any of its reals [r]. *)
Lemma tn_unb_wide :
  forall x, valid x -> Interval.is_empty x = false ->
  Interval.inf_raw x = B754_infinity true \/ Interval.sup_raw x = B754_infinity false ->
  exists r t, PI <= t - r /\ forall s, r <= s <= t -> mem s x.
Proof.
intros x Hx Hn Hinf. destruct (nonempty_mem x Hx Hn) as (r0 & Hr0).
destruct Hinf as [Ea|Eb].
- exists (r0 - PI), r0. split; [lra|]. intros s Hs.
  exact (mono_mem_dn x r0 s Hr0 Ea (proj2 Hs)).
- exists r0, (r0 + PI). split; [lra|]. intros s Hs.
  exact (mono_mem_up x r0 s Hr0 Eb (proj1 Hs)).
Qed.

(** A bound that is an infinity and another that is not NaN compare
    unequal. *)
Lemma tn_eq_unb :
  forall a b : f64,
  a = B754_infinity true \/ is_finite a = true ->
  b = B754_infinity false \/ is_finite b = true ->
  a = B754_infinity true \/ b = B754_infinity false ->
  Model.eq a b = false.
Proof.
intros a b Ha Hb Hab. destruct Ha as [->|Fa], Hb as [->|Fb]; try reflexivity.
- destruct b; try discriminate Fb; reflexivity.
- destruct a; try discriminate Fa; reflexivity.
- destruct Hab as [E|E]; rewrite E in *; discriminate.
Qed.

(** If a bound is an infinity, [b - a] is +inf. *)
Lemma tn_sub_unb :
  forall a b : f64,
  a = B754_infinity true \/ is_finite a = true ->
  b = B754_infinity false \/ is_finite b = true ->
  a = B754_infinity true \/ b = B754_infinity false ->
  Model.sub b a = B754_infinity false.
Proof.
intros a b Ha Hb Hab. unfold Model.sub.
destruct Ha as [->|Fa], Hb as [->|Fb].
- reflexivity.
- destruct b; try discriminate Fb; reflexivity.
- destruct a; try discriminate Fa; reflexivity.
- destruct Hab as [E|E]; rewrite E in *; discriminate.
Qed.

(** If [b - a], rounded to nearest, is at least 4, then [b - a > PI]: a
    [b - a] from 0 to [PI < 7 / 2] rounds to at most the float [7 / 2]. *)
Lemma tn_sub_wide :
  forall a b : f64, is_finite a = true -> is_finite b = true -> B2R a <= B2R b ->
  Model.le (of_u64 4) (Model.sub b a) = true -> PI < B2R b - B2R a.
Proof.
intros a b Fa Fb Hab H.
destruct (Rlt_or_le PI (B2R b - B2R a)) as [L|L]; [exact L | exfalso].
assert (Hpi : PI < 7 / 2).
{ destruct PI_bounds as [_ H1]. rewrite pb_hi_R in H1. unfold Q2R in H1.
  cbn [Qnum Qden] in H1. lra. }
assert (F7 : generic_format radix2 fexp64 (7 / 2)).
{ replace (7 / 2) with (F2R (Float radix2 7 (-1))) by (unfold F2R; cbn; lra).
  apply generic_format_FLT. apply FLT_spec with (Float radix2 7 (-1));
    [reflexivity | cbn; lia | cbn; lia]. }
assert (R0 : 0 <= rd_RNE (B2R b - B2R a)).
{ rewrite <- (round_0 radix2 fexp64 ZnearestE).
  apply round_le; [typeclasses eauto.. | lra]. }
assert (R7 : rd_RNE (B2R b - B2R a) <= 7 / 2).
{ rewrite <- (round_generic _ _ ZnearestE _ F7).
  apply round_le; [typeclasses eauto.. | lra]. }
pose proof (Bminus_correct 53 1024 _ _ mode_NE b a Fb Fa) as E.
change (SpecFloat.fexp 53 1024) with fexp64 in E. cbn [round_mode] in E.
rewrite Rlt_bool_true in E.
2:{ rewrite Rabs_pos_eq by exact R0.
    assert (B : bpow radix2 2 <= bpow radix2 1024) by (apply bpow_le; lia).
    change (bpow radix2 2) with 4 in B. lra. }
destruct E as (E & Fs & _).
destruct (of_u64_exact 4 ltac:(lia)) as (F4 & _ & R4).
unfold Model.le, Model.sub in H. rewrite Bleb_correct, E, R4 in H by assumption.
revert H. case Rle_bool_spec; [intros H _; lra | intros _ H; discriminate H].
Qed.

(** The parity [qa % 2] of the quadrant [qa = quad_f j] that [quadrants]
    returns. *)
Lemma tn_quad_par :
  forall j, (0 <= j <= 3)%Z ->
  Model.eq (frem (quad_f j) (of_u64 2)) Model.zero = Z.even j /\
  Model.eq (frem (quad_f j) (of_u64 2)) (of_u64 1) = negb (Z.even j).
Proof.
intros j Hj.
assert (E : j = 0%Z \/ j = 1%Z \/ j = 2%Z \/ j = 3%Z) by lia.
destruct E as [-> | [-> | [-> | ->]]]; vm_compute; split; reflexivity.
Qed.

Lemma tn_even_mod4 : forall k, Z.even (k mod 4) = Z.even k.
Proof.
intros k. pose proof (Z.div_mod k 4 ltac:(lia)) as E.
set (j := (k mod 4)%Z) in *. set (h := (k / 4)%Z) in *. clearbody j h. subst k.
replace (4 * h + j)%Z with (j + 2 * (2 * h))%Z by ring.
rewrite Z.even_add_mul_2. reflexivity.
Qed.

(** The count [N] that [quadrants] returns for the floors [ka <= kb]
    ([count_f_val]) is [kb - ka] below 4, and at least 4 otherwise. *)
Lemma tn_count :
  forall ka kb, (ka <= kb)%Z ->
  let N := ((kb mod 4 - ka mod 4) mod 4 + if (4 <=? kb - ka)%Z then 4 else 0)%Z in
  ((N < 4)%Z -> N = (kb - ka)%Z) /\ ((4 <= N)%Z -> (4 <= kb - ka)%Z).
Proof.
intros ka kb Hk N.
assert (E : ((kb mod 4 - ka mod 4) mod 4 = (kb - ka) mod 4)%Z)
  by (symmetry; apply Zminus_mod).
unfold N. rewrite E.
pose proof (Z.mod_pos_bound (kb - ka) 4 ltac:(lia)).
destruct (Z.leb_spec 4 (kb - ka)).
- lia.
- rewrite Z.mod_small by lia. lia.
Qed.

Lemma tn_bounded :
  forall x, finite_itv x -> bounded (fun r => mem r x).
Proof.
intros x Hf. exists (Rabs (B2R (Interval.inf_raw x)) + Rabs (B2R (Interval.sup_raw x))).
intros r Hr. apply (finite_itv_mem x r Hf) in Hr.
unfold Rabs. repeat case Rcase_abs; intros; lra.
Qed.

(** What [tn_impl] says of a result [(y, e)] for [x]. *)
Definition tn_spec (x y : Interval) (e : Decoration) : Prop :=
  encloses (image_dom tan_dom tan x) y /\
  (e = Trv \/ (e = Com /\ (forall r, mem r x -> tan_dom r) /\ bounded (fun r => mem r x))) /\
  is_tightest (image_dom tan_dom tan x) y /\
  (e = Trv -> ~ ((exists r, mem r x) /\ forall r, mem r x -> tan_dom r)).

(** The two results of [Interval::tan_impl] for a nonempty [x]: the [com]
    form, when it is the tightest and [x] a bounded subset of the domain,
    and [[-inf, +inf]] with [trv], when that is the tightest and [x] has a
    real outside the domain. *)
Lemma tn_res_com :
  forall x y, finite_itv x -> (forall r, mem r x -> tan_dom r) ->
  is_tightest (image_dom tan_dom tan x) y -> tn_spec x y Com.
Proof.
intros x y Hf HD Ht.
split; [exact (conj (proj1 Ht) (proj1 (proj2 Ht)))|].
split; [right; split; [reflexivity|]; split; [exact HD | exact (tn_bounded x Hf)]|].
split; [exact Ht | intros E; discriminate E].
Qed.

Lemma tn_res_entire :
  forall x, valid x -> Interval.is_empty x = false ->
  is_tightest (image_dom tan_dom tan x) Interval.ENTIRE /\
  ~ (forall s, mem s x -> tan_dom s) ->
  tn_spec x Interval.ENTIRE Trv.
Proof.
intros x Hx Hn (Ht & ND).
split; [apply br_entire_encl|].
split; [left; reflexivity|].
split; [exact Ht|].
intros _ (_ & HD). exact (ND HD).
Qed.

(** The branches of [Interval::tan_impl] on [(q, n)]. *)
Definition tn_br (m : mpfr) (a b q n : f64) : option (Interval * Decoration) :=
  if Model.eq q Model.zero && Model.lt n (of_u64 1)
     || Model.eq q (of_u64 1) && Model.lt n (of_u64 2)
  then Some (Interval.with_infsup_raw (tan_rd m a) (tan_ru m b), Com)
  else Some (Interval.ENTIRE, Trv).

Section TnImpl.

Variables (emin emax : Z) (m : mpfr) (has_fma : bool).

Hypothesis Hrange : range_ok emin emax.
Hypothesis Hget : get_d_ok emin emax m.
Hypothesis Htan : tan_ok emin emax m.
Hypothesis Hsin : sin_ok emin emax m.
Hypothesis Hcos : cos_ok emin emax m.

(** Between two poles [k * (PI / 2)] and [(k + 2) * (PI / 2)], for an odd
    [k], [tan] is defined and increases, so [[tan_rd(a), tan_ru(b)]] is the
    tightest. *)
Lemma tn_piece :
  forall x k, finite_itv x -> Z.odd k = true ->
  IZR k * (PI / 2) < B2R (Interval.inf_raw x) ->
  B2R (Interval.sup_raw x) < (IZR k + 2) * (PI / 2) ->
  (forall r, mem r x -> tan_dom r) /\
  is_tightest (image_dom tan_dom tan x)
    (Interval.with_infsup_raw (tan_rd m (Interval.inf_raw x)) (tan_ru m (Interval.sup_raw x))).
Proof using Hrange Hget Htan.
intros x k Hf Hk Ha Hb.
assert (HD : forall r, mem r x -> tan_dom r).
{ intros r Hr. apply (finite_itv_mem x r Hf) in Hr. apply (tan_piece_dom k r Hk). lra. }
split; [exact HD|].
apply (br_inc_tight emin emax m tan_dom tan (mpfr_tan m) Hrange Hget Htan x Hf HD).
intros r t Hr Ht Hrt.
apply (finite_itv_mem x r Hf) in Hr. apply (finite_itv_mem x t Hf) in Ht.
apply (tan_piece_inc k r t Hk); lra.
Qed.

(** A singleton [[a, a]] is not a pole, as π is irrational, so
    [[tan_rd(a), tan_ru(a)]] is the tightest. *)
Lemma tn_single :
  forall x, finite_itv x -> B2R (Interval.inf_raw x) = B2R (Interval.sup_raw x) ->
  (forall r, mem r x -> tan_dom r) /\
  is_tightest (image_dom tan_dom tan x)
    (Interval.with_infsup_raw (tan_rd m (Interval.inf_raw x)) (tan_ru m (Interval.sup_raw x))).
Proof using Hrange Hget Htan.
intros x Hf Eab.
pose proof (tan_dom_f64 (Interval.inf_raw x) (proj1 (proj2 (proj2 Hf)))) as Da.
assert (Hr : forall r, mem r x -> r = B2R (Interval.inf_raw x)).
{ intros r Hr. apply (finite_itv_mem x r Hf) in Hr. lra. }
assert (HD : forall r, mem r x -> tan_dom r) by (intros r H; rewrite (Hr r H); exact Da).
split; [exact HD|].
apply (br_inc_tight emin emax m tan_dom tan (mpfr_tan m) Hrange Hget Htan x Hf HD).
intros r t Hr' Ht' _. rewrite (Hr r Hr'), (Hr t Ht'). apply Rle_refl.
Qed.

(** An odd multiple [k * (PI / 2)] in [(a, b]] is in [(a, b)], as [b] is
    not a pole, and [tan] takes values beyond any bound on each side of
    it. *)
Lemma tn_pole_in :
  forall x k, finite_itv x -> Z.odd k = true ->
  B2R (Interval.inf_raw x) < IZR k * (PI / 2) <= B2R (Interval.sup_raw x) ->
  is_tightest (image_dom tan_dom tan x) Interval.ENTIRE /\
  ~ (forall s, mem s x -> tan_dom s).
Proof using Hrange Hget Htan.
intros x k Hf Hk [H1 H2].
pose proof (tan_pole k Hk) as Np.
pose proof (tan_dom_f64 (Interval.sup_raw x) (proj2 (proj2 (proj2 Hf)))) as Db.
assert (H3 : IZR k * (PI / 2) < B2R (Interval.sup_raw x)).
{ destruct (Rle_lt_or_eq_dec _ _ H2) as [H3|H3]; [exact H3|].
  rewrite H3 in Np. contradiction. }
split.
- apply br_entire_tight; intros M;
    destruct (tan_pole_unbounded k _ _ M Hk (conj H1 H3))
      as (r & t & (Hr1 & Hr2) & Dr & Mr & (Ht1 & Ht2) & Dt & Mt).
  + exists r. split; [apply (finite_itv_mem x r Hf); lra|]. split; assumption.
  + exists t. split; [apply (finite_itv_mem x t Hf); lra|]. split; assumption.
- intros HD. apply Np, HD. apply (finite_itv_mem x _ Hf). lra.
Qed.

(** With exact floors [ka] of [a / (PI / 2)] and [kb] of [b / (PI / 2)],
    an odd [j] with [ka < j <= kb] gives the pole [j * (PI / 2)] in
    [(a, b]]. *)
Lemma tn_ent_exact :
  forall x ka kb, finite_itv x ->
  B2R (Interval.inf_raw x) < (IZR ka + 1) * (PI / 2) ->
  IZR kb * (PI / 2) <= B2R (Interval.sup_raw x) ->
  forall j, Z.odd j = true -> (ka < j <= kb)%Z ->
  is_tightest (image_dom tan_dom tan x) Interval.ENTIRE /\
  ~ (forall s, mem s x -> tan_dom s).
Proof using Hrange Hget Htan.
intros x ka kb Hf Ha Hb j Hj [Hj1 Hj2].
pose proof PI_RGT_0 as Hpi.
apply (tn_pole_in x j Hf Hj).
assert (H1 : IZR ka + 1 <= IZR j) by (rewrite <- plus_IZR; apply IZR_le; lia).
assert (H2 : IZR j <= IZR kb) by (apply IZR_le; lia).
pose proof (tn_mul_le _ _ (PI / 2) ltac:(lra) H1).
pose proof (tn_mul_le _ _ (PI / 2) ltac:(lra) H2).
lra.
Qed.

(** The branches for a bounded [x] with [a <> b], from [ka] and [kb] with
    [x] in [[ka * (PI / 2), (kb + 1) * (PI / 2))], [a] above
    [ka * (PI / 2)] for an odd [ka], [q] the parity of [ka], [n] tests as
    an integer [N] that is [kb - ka] below 4 and implies [kb - ka >= 4]
    otherwise. Each [com] case puts [x] between two poles ([tn_piece]); the
    [trv] case has an odd [j] with [ka < j <= kb], so [Ent] says when it
    is the tightest. *)
Lemma tn_br_spec :
  forall x q n ka kb N, finite_itv x -> (ka <= kb)%Z ->
  IZR ka * (PI / 2) <= B2R (Interval.inf_raw x) ->
  (Z.odd ka = true -> IZR ka * (PI / 2) < B2R (Interval.inf_raw x)) ->
  B2R (Interval.sup_raw x) < (IZR kb + 1) * (PI / 2) ->
  Model.eq q Model.zero = Z.even ka -> Model.eq q (of_u64 1) = negb (Z.even ka) ->
  Model.lt n (of_u64 1) = (N <? 1)%Z -> Model.lt n (of_u64 2) = (N <? 2)%Z ->
  ((N < 4)%Z -> N = (kb - ka)%Z) -> ((4 <= N)%Z -> (4 <= kb - ka)%Z) ->
  (forall j, Z.odd j = true -> (ka < j <= kb)%Z ->
   is_tightest (image_dom tan_dom tan x) Interval.ENTIRE /\
   ~ (forall s, mem s x -> tan_dom s)) ->
  exists y e, tn_br m (Interval.inf_raw x) (Interval.sup_raw x) q n = Some (y, e) /\
    tn_spec x y e.
Proof using Hrange Hget Htan.
intros x q n ka kb N Hf Hle Ha1 Ha2 Hb Q0 Q1 L1 L2 HN1 HN2 Ent.
pose proof PI_RGT_0 as Hpi.
pose proof Hf as (Hx & Hn & _ & _).
assert (Hk1 : (1 <= N)%Z -> (ka + 1 <= kb)%Z)
  by (intros H; destruct (Z.lt_ge_cases N 4) as [H'|H'];
      [specialize (HN1 H') | specialize (HN2 H')]; lia).
assert (Hk2 : (2 <= N)%Z -> (ka + 2 <= kb)%Z)
  by (intros H; destruct (Z.lt_ge_cases N 4) as [H'|H'];
      [specialize (HN1 H') | specialize (HN2 H')]; lia).
unfold tn_br. rewrite Q0, Q1, L1, L2.
destruct (Z.even ka) eqn:Ev; cbn [andb orb negb]; rewrite ?Bool.orb_false_r.
- (* [ka] is even: the piece is [((ka - 1) * c, (ka + 1) * c)], with [b]
     below its end if [N = 0]. *)
  assert (Od : Z.odd (ka - 1) = true) by (rewrite Z.sub_1_r, Z.odd_pred; exact Ev).
  assert (Od1 : Z.odd (ka + 1) = true) by (rewrite Z.add_1_r, Z.odd_succ; exact Ev).
  destruct (N <? 1)%Z eqn:D0; cbn [orb].
  { apply Z.ltb_lt in D0.
    assert (Ek : kb = ka) by (specialize (HN1 ltac:(lia)); lia). subst kb.
    destruct (tn_piece x (ka - 1) Hf Od) as (HD & Ht);
      [rewrite minus_IZR; lra | rewrite minus_IZR; lra|].
    eexists _, _. split; [reflexivity|]. exact (tn_res_com x _ Hf HD Ht). }
  apply Z.ltb_ge in D0.
  (* Otherwise [N >= 1], so [kb >= ka + 1]. *)
  eexists _, _. split; [reflexivity|].
  apply (tn_res_entire x Hx Hn).
  apply (Ent (ka + 1)%Z Od1). specialize (Hk1 D0). lia.
- (* [ka] is odd, and [a > ka * c]: the piece is [(ka * c, (ka + 2) * c)],
     with [b] below its end if [N <= 1]. *)
  assert (Od : Z.odd ka = true) by (rewrite <- Z.negb_even, Ev; reflexivity).
  assert (Od2 : Z.odd (ka + 2) = true).
  { replace (ka + 2)%Z with (Z.succ (Z.succ ka)) by lia.
    rewrite Z.odd_succ, Z.even_succ. exact Od. }
  pose proof (Ha2 Od) as Ha3.
  destruct (N <? 2)%Z eqn:D0; cbn [orb].
  { apply Z.ltb_lt in D0.
    assert (Hk : (kb <= ka + 1)%Z)
      by (destruct (Z.lt_ge_cases N 4) as [H'|H']; [specialize (HN1 H') | lia]; lia).
    assert (H : IZR kb + 1 <= IZR ka + 2) by (rewrite <- !plus_IZR; apply IZR_le; lia).
    pose proof (tn_mul_le _ _ (PI / 2) ltac:(lra) H).
    destruct (tn_piece x ka Hf Od) as (HD & Ht); [lra | lra|].
    eexists _, _. split; [reflexivity|]. exact (tn_res_com x _ Hf HD Ht). }
  apply Z.ltb_ge in D0.
  (* Otherwise [N >= 2], so [kb >= ka + 2]. *)
  eexists _, _. split; [reflexivity|].
  apply (tn_res_entire x Hx Hn).
  apply (Ent (ka + 2)%Z Od2). specialize (Hk2 D0). lia.
Qed.

(** What the theorems need of [Interval::tan_impl]: it returns [(y, e)]
    with [y] the tightest enclosure; [e] is [trv], or [com] for a bounded
    [x] in the domain, and [trv] only if [x] is empty or holds a pole. A
    singleton gives the [com] form ([tn_single]), and an unbounded [x]
    [[-inf, +inf]] ([tn_unb_wide]).
    Otherwise the [(q, n)] of the floors [qa] and [qb] are kept when
    [n = 0], when [b - a] rounds to at least 4, so [x] is more than [PI]
    wide ([tn_sub_wide]), and when they are exact ([floors_exact_ok]);
    else [quadrants] gives them from the exact floors
    ([quadrants_correct]). [tn_br_spec] covers all four. *)
Lemma tn_impl :
  forall x, valid x ->
  exists y e, Interval.tan_impl m has_fma x = Some (y, e) /\
  encloses (image_dom tan_dom tan x) y /\
  (e = Trv \/ (e = Com /\ (forall r, mem r x -> tan_dom r) /\ bounded (fun r => mem r x))) /\
  is_tightest (image_dom tan_dom tan x) y /\
  (e = Trv -> ~ ((exists r, mem r x) /\ forall r, mem r x -> tan_dom r)).
Proof using Hrange Hget Htan Hsin Hcos.
intros x Hx.
destruct (Interval.is_empty x) eqn:Hn.
{ (* An empty [x] is returned with [trv]. *)
  exists x, Trv. unfold Interval.tan_impl. rewrite Hn. split; [reflexivity|].
  assert (Nm : forall r, ~ mem r x) by (intros r; exact (mem_empty x r Hx Hn)).
  split; [split; [exact Hx | intros s (r & Hr & _); destruct (Nm r Hr)]|].
  split; [left; reflexivity|].
  split.
  - split; [exact Hx|]. split; [intros s (r & Hr & _); destruct (Nm r Hr)|].
    intros w _ _ r Hr. destruct (Nm r Hr).
  - intros _ ((r & Hr) & _). exact (Nm r Hr). }
destruct (trig_reduce has_fma _ _ x FRAC_PI_2_const Hx Hn) as (z & Ez & Hlo & Hhi).
unfold Interval.tan_impl. rewrite Hn. cbv zeta. rewrite Ez.
set (a := Interval.inf_raw x) in *.
set (b := Interval.sup_raw x) in *.
set (qa := Interval.inf_raw (Interval.floor z)) in *.
set (qb := Interval.sup_raw (Interval.floor z)) in *.
destruct tn_consts as (EZZ & EZ1 & E1Z & E11 & LZ1 & LZ2 & LI1 & LI2 & EIZ & LI4).
pose proof PI_RGT_0 as Hpi0.
assert (La : a = B754_infinity true \/ is_finite a = true)
  by (destruct Hlo as [(E & _)|(F & _)]; [left | right]; assumption).
assert (Lb : b = B754_infinity false \/ is_finite b = true)
  by (destruct Hhi as [(E & _)|(F & _)]; [left | right]; assumption).
match goal with |- ?G => assert (Unb : a = B754_infinity true \/ b = B754_infinity false -> G) end.
{ (* An infinite bound gives [n = +inf] and [b - a = +inf], so the floors
     are kept and the result is [[-inf, +inf]], the tightest as [x] holds
     a whole period. *)
  intros Hab. rewrite (tn_eq_unb a b La Lb Hab), (tn_sub_unb a b La Lb Hab).
  assert (Nqa : is_nan qa = false /\ qa <> B754_infinity false).
  { destruct Hlo as [(_ & ->)|(_ & F & _)]; [split; [reflexivity | discriminate]|].
    split; [exact (tn_fin_nan qa F) | intros E; rewrite E in F; discriminate F]. }
  assert (Nqb : is_nan qb = false /\ qb <> B754_infinity true).
  { destruct Hhi as [(_ & ->)|(_ & F & _)]; [split; [reflexivity | discriminate]|].
    split; [exact (tn_fin_nan qb F) | intros E; rewrite E in F; discriminate F]. }
  assert (Hq : qa = B754_infinity true \/ qb = B754_infinity false).
  { destruct Hab as [E|E]; [left | right].
    - destruct Hlo as [(_ & E')|(F & _)]; [exact E' | rewrite E in F; discriminate F].
    - destruct Hhi as [(_ & E')|(F & _)]; [exact E' | rewrite E in F; discriminate F]. }
  cbv beta iota.
  rewrite (n_inf qa qb (proj1 Nqa) (proj1 Nqb) (proj2 Nqa) (proj2 Nqb) Hq).
  rewrite EIZ, LI4. cbv beta iota. cbn [orb]. cbv beta iota.
  rewrite LI1, LI2. rewrite !Bool.andb_false_r. cbn [orb].
  eexists _, _. split; [reflexivity|].
  destruct (tn_unb_wide x Hx Hn Hab) as (r & t & Hw & Hm).
  exact (tn_res_entire x Hx Hn (tn_wide x r t Hw Hm)). }
destruct La as [Ea|Fa]; [exact (Unb (or_introl Ea))|].
destruct Lb as [Eb|Fb]; [exact (Unb (or_intror Eb))|].
clear Unb.
destruct Hlo as [(Ea & _)|(_ & Fqa & ka & Hka & Hka1 & Hka2)];
  [rewrite Ea in Fa; discriminate Fa|].
destruct Hhi as [(Eb & _)|(_ & Fqb & kb & Hkb & Hkb1)];
  [rewrite Eb in Fb; discriminate Fb|].
assert (Hf : finite_itv x) by exact (conj Hx (conj Hn (conj Fa Fb))).
destruct (nonempty_mem x Hx Hn) as (r0 & Hr0).
pose proof (proj1 (finite_itv_mem x r0 Hf) Hr0) as Hr0'. fold a b in Hr0'.
assert (Hab : B2R a <= B2R b) by lra.
assert (Hle : (ka <= kb)%Z).
{ destruct (Z.le_gt_cases ka kb) as [H|H]; [exact H|]. exfalso.
  assert (H' : IZR kb + 1 <= IZR ka) by (rewrite <- plus_IZR; apply IZR_le; lia).
  pose proof (tn_mul_le _ _ (PI / 2) ltac:(lra) H'). lra. }
rewrite (rem_euclid_2_int qa ka Fqa Hka).
assert (Hq : Model.eq (if Z.even ka then Model.zero else of_u64 1) Model.zero = Z.even ka /\
  Model.eq (if Z.even ka then Model.zero else of_u64 1) (of_u64 1) = negb (Z.even ka))
  by (destruct (Z.even ka); [rewrite EZZ, EZ1 | rewrite E1Z, E11]; split; reflexivity).
destruct (Model.eq a b) eqn:Eab.
{ (* [a == b]: [n = 0], and both parities give the [com] form. *)
  cbv beta iota. rewrite EZZ. cbn [orb]. cbv beta iota.
  rewrite LZ1, LZ2. cbn [orb]. rewrite !Bool.andb_true_r.
  destruct (tn_single x Hf (proj2 (proj2 (bounds_eq_finite x Hx Hn Eab)))) as (HD & Ht).
  destruct (Z.even ka); [rewrite EZZ | rewrite E1Z, E11]; cbn [orb];
    (eexists _, _; split; [reflexivity|]); exact (tn_res_com x _ Hf HD Ht). }
cbv beta iota.
pose proof (n_small qa qb ka kb Fqa Fqb Hka Hkb Hle) as HN. cbv zeta in HN.
destruct HN as (N0 & Nj).
destruct (Nj 1%Z ltac:(lia)) as (L1 & _).
destruct (Nj 2%Z ltac:(lia)) as (L2 & _).
(* The floors [qa] and [qb] kept, for which [Ent] says when the [trv]
   case is the tightest. *)
assert (Fast : (forall j, Z.odd j = true -> (ka < j <= kb)%Z ->
    is_tightest (image_dom tan_dom tan x) Interval.ENTIRE /\
    ~ (forall s, mem s x -> tan_dom s)) ->
  exists y e, tn_br m a b (if Z.even ka then Model.zero else of_u64 1)
    (Model.sub qb qa) = Some (y, e) /\ tn_spec x y e).
{ intros Ent.
  assert (Ha2 : Z.odd ka = true -> IZR ka * (PI / 2) < B2R a).
  { intros Od. apply Hka2. intros E. rewrite E in Od. discriminate Od. }
  exact (tn_br_spec x _ _ ka kb (kb - ka)%Z Hf Hle Hka1 Ha2 Hkb1 (proj1 Hq) (proj2 Hq)
    L1 L2 (fun _ => eq_refl) (fun H => H) Ent). }
rewrite N0.
destruct (kb - ka =? 0)%Z eqn:D0; cbn [orb]; cbv beta iota.
{ (* [n = 0]: [x] lies in one piece. *)
  apply Z.eqb_eq in D0. apply Fast. intros j _ Hj. lia. }
destruct (Model.le (of_u64 4) (Model.sub b a)) eqn:W; cbv beta iota.
{ (* [b - a >= 4]: [x] is more than [PI] wide. *)
  apply Fast. intros j _ _.
  apply (tn_wide x (B2R a) (B2R b) (Rlt_le _ _ (tn_sub_wide a b Fa Fb Hab W))).
  intros s Hs. exact (proj2 (finite_itv_mem x s Hf) Hs). }
destruct (floors_exact_ok has_fma Interval.FRAC_PI_2 (PI / 2) a b qa qb ka kb
  FRAC_PI_2_const Fa Fb Fqa Hka Fqb Hkb) as (e & Ee & He).
rewrite Ee. cbv beta iota.
destruct e.
{ (* The floors are exact. *)
  apply Fast. destruct (He eq_refl) as (Xa & Xb).
  exact (tn_ent_exact x ka kb Hf Xa Xb). }
(* [quadrants] gives the exact floors [ka'] and [kb'] modulo 4. *)
clear Fast Hq N0 Nj L1 L2 He Ee W D0 Eab.
pose proof (floor_div_bounds (PI / 2) (B2R a) ltac:(lra)) as Ba.
pose proof (floor_div_bounds (PI / 2) (B2R b) ltac:(lra)) as Bb.
unfold Rfloor in Ba, Bb.
set (ka' := Zfloor (B2R a / (PI / 2))) in *.
set (kb' := Zfloor (B2R b / (PI / 2))) in *.
assert (Hle' : (ka' <= kb')%Z).
{ destruct (Z.le_gt_cases ka' kb') as [H|H]; [exact H|]. exfalso.
  assert (H' : IZR kb' + 1 <= IZR ka') by (rewrite <- plus_IZR; apply IZR_le; lia).
  pose proof (tn_mul_le _ _ (PI / 2) ltac:(lra) H'). lra. }
rewrite (quadrants_correct emin emax m a b ka' kb' Hrange Hget Hsin Hcos Fa Fb Hab Ba Bb).
cbv beta iota.
pose proof (Z.mod_pos_bound ka' 4 ltac:(lia)) as Ma.
pose proof (Z.mod_pos_bound kb' 4 ltac:(lia)) as Mb.
destruct (tn_quad_par (ka' mod 4)%Z ltac:(lia)) as (Q0 & Q1).
rewrite tn_even_mod4 in Q0, Q1.
destruct (count_f_val (ka' mod 4) (kb' mod 4) (4 <=? kb' - ka')%Z ltac:(lia) ltac:(lia))
  as (Fn & Vn).
destruct (int_tests _ _ Fn Vn) as (_ & Tj).
destruct (Tj 1%Z ltac:(lia)) as (L1 & _).
destruct (Tj 2%Z ltac:(lia)) as (L2 & _).
destruct (tn_count ka' kb' Hle') as (HN1 & HN2).
assert (Ha2 : Z.odd ka' = true -> IZR ka' * (PI / 2) < B2R a).
{ intros Od. destruct (Rle_lt_or_eq_dec _ _ (proj1 Ba)) as [H|H]; [exact H|].
  exfalso. apply (tan_pole ka' Od). rewrite H. exact (tan_dom_f64 a Fa). }
exact (tn_br_spec x _ _ ka' kb' _ Hf Hle' (proj1 Ba) Ha2 (proj2 Bb) Q0 Q1
  L1 L2 HN1 HN2 (tn_ent_exact x ka' kb' Hf (proj2 Ba) (proj1 Bb))).
Qed.

End TnImpl.

Theorem tan_encloses :
  forall emin emax m has_fma x,
  range_ok emin emax -> get_d_ok emin emax m -> tan_ok emin emax m ->
  sin_ok emin emax m -> cos_ok emin emax m -> valid x ->
  exists y, Interval.tan m has_fma x = Some y /\
    encloses (image_dom tan_dom tan x) y.
Proof.
intros emin emax m has_fma x Hrange Hget Htan Hs Hc Hx.
destruct (tn_impl emin emax m has_fma Hrange Hget Htan Hs Hc x Hx)
  as (y & e & Ei & Henc & _).
exists y. unfold Interval.tan. rewrite Ei. split; [reflexivity | exact Henc].
Qed.

Theorem tan_correct :
  forall emin emax m has_fma x,
  range_ok emin emax -> get_d_ok emin emax m -> tan_ok emin emax m ->
  sin_ok emin emax m -> cos_ok emin emax m -> valid x ->
  exists y, Interval.tan m has_fma x = Some y /\
    is_tightest (image_dom tan_dom tan x) y.
Proof.
intros emin emax m has_fma x Hrange Hget Htan Hs Hc Hx.
destruct (tn_impl emin emax m has_fma Hrange Hget Htan Hs Hc x Hx)
  as (y & e & Ei & _ & _ & Ht & _).
exists y. unfold Interval.tan. rewrite Ei. split; [reflexivity | exact Ht].
Qed.

Theorem dec_tan_correct :
  forall emin emax m has_fma x,
  range_ok emin emax -> get_d_ok emin emax m -> tan_ok emin emax m ->
  sin_ok emin emax m -> cos_ok emin emax m -> valid (itv x) ->
  exists y, DecInterval.tan m has_fma x = Some y /\
    if DecInterval.is_nai x then y = DecInterval.NAI
    else
      is_tightest (image_dom tan_dom tan (itv x)) (itv y) /\
      exists d, strongest_dom tan_dom d tan (itv x) (itv y) /\
        dec y = dec_min d (dec x).
Proof.
intros emin emax m has_fma x Hrange Hget Htan Hs Hc Hx.
destruct (tn_impl emin emax m has_fma Hrange Hget Htan Hs Hc (itv x) Hx)
  as (y & e & Ei & _ & He & Ht1 & Ht2).
unfold DecInterval.tan. rewrite Ei. eexists. split; [reflexivity|]. cbn [fst snd].
destruct (DecInterval.is_nai x) eqn:Enai.
- (* NaI: [dec_min] keeps [ill], and [set_dec] returns NaI. *)
  destruct x as [w []]; try discriminate Enai. destruct e; reflexivity.
- assert (Hd : dec x <> Ill).
  { intros E. unfold DecInterval.is_nai in Enai. rewrite E in Enai. discriminate Enai. }
  (* [tan] is continuous on its domain, and [e] is [trv], or [com] for a
     bounded [x] in the domain. *)
  assert (He' :
    (e = Trv /\ ~ ((exists r, mem r (itv x)) /\ forall r, mem r (itv x) -> tan_dom r)) \/
    (e = Com /\ (forall r, mem r (itv x) -> tan_dom r) /\
     (dec x = Com -> Interval.is_common_interval y = true ->
      bounded (fun r => mem r (itv x))))).
  { destruct He as [E|(E & HD & Hb)]; [left; split; [exact E | exact (Ht2 E)]|].
    right. split; [exact E|]. split; [exact HD | intros _ _; exact Hb]. }
  exact (elem_set_dec_trv_com tan_dom tan x y e Hx Hd Ht1
    (fun r _ Hr => continuity_pt_continue_in tan tan_dom r (tan_dom_cont r Hr)) He').
Qed.
