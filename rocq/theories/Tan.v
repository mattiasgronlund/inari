(** * [tan] of intervals encloses the image, and when it is tightest

    [Interval::tan_impl] reduces by [FRAC_PI_2] as [Interval::sin] does
    and reads the parity [q] of [qa]. The poles of [tan] are the odd
    multiples of [PI / 2], and it increases between two of them
    ([TrigPieces.v]). It returns [[tan_rd(a), tan_ru(b)]] with [com] when
    [x] lies between two poles: for even [qa], if [n = 0], or [n = 1] and
    [cont], i.e. [b] is at most the lower bound of [qb * FRAC_PI_2], so
    below the pole [qb * (PI / 2)]; for odd [qa], if [n <= 1], or [n = 2]
    and [cont]. Otherwise it returns [[-inf, +inf]] with [trv]. Every real
    of [x] lies in [[qa * (PI / 2), (qb + 1) * (PI / 2))], and
    [qa * (PI / 2)] is strictly below [a] unless [qa] is 0, so for
    [a != b] the first case never holds a pole. If [a == b], [n] is 0
    whatever [q] is, so the first case is taken whether or not [a] is a
    pole. The proofs derive that it is not from the irrationality of π
    ([pi_irrational] in [Elementary.v]), which Stdlib does not prove, so
    the theorems assume it. So the result encloses the image
    ([tan_encloses]); the decoration [com] then holds, and [trv] always
    does.

    The result is the tightest, with the strongest decoration, under
    [trig_tight] ([tan_correct], [dec_tan_correct]). It is not for every
    [x]: [[7.853981633974484, 7.853981633974485]], just above the pole
    [5 * (PI / 2)], gives [[-inf, +inf]] with [trv], where the tightest is
    [[-1.718163698371049e15, -6.80181816043107e14]] and [com] holds, as
    [qa] is one too small there. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr ComCommon Integer
  PiBounds TrigPieces TrigSpec TrigReduce TrigBranch Mul DecBinary MonoInc Sqrt.

Open Scope R_scope.

(** ** Helpers *)

(** The float constants that the tests of [Interval::tan_impl] compare. *)
Lemma tn_consts :
  Model.eq Model.zero Model.zero = true /\ Model.eq Model.zero (of_u64 1) = false /\
  Model.eq (of_u64 1) Model.zero = false /\ Model.eq (of_u64 1) (of_u64 1) = true /\
  Model.lt Model.zero (of_u64 1) = true /\ Model.lt Model.zero (of_u64 2) = true /\
  Model.lt (B754_infinity false) (of_u64 1) = false /\
  Model.eq (B754_infinity false) (of_u64 1) = false /\
  Model.lt (B754_infinity false) (of_u64 2) = false /\
  Model.eq (B754_infinity false) (of_u64 2) = false.
Proof.
vm_compute. repeat split.
Qed.

Lemma tn_fin_nan : forall w : f64, is_finite w = true -> is_nan w = false.
Proof.
intros [s|s| |s mw ew Hw] F; try discriminate F; reflexivity.
Qed.

Lemma tn_le_fin :
  forall u v, is_finite u = true -> is_finite v = true -> Model.le u v = true ->
  B2R u <= B2R v.
Proof.
intros u v Fu Fv. unfold Model.le. rewrite Bleb_correct by assumption.
case Rle_bool_spec; [intros H _; exact H | intros _ E; discriminate E].
Qed.

(** If a finite [b] is at most the lower bound [w] of an interval that
    holds [r], it is at most [r]: [w] is not NaN then, and if infinite it
    is -inf, which no finite [b] is at most. *)
Lemma tn_le_lower :
  forall (b : f64) z r, is_finite b = true -> Model.le b (Interval.inf_raw z) = true ->
  mem r z -> B2R b <= r.
Proof.
intros b z r Fb Hle [Hm _]. revert Hle Hm. unfold Interval.inf_raw.
destruct (opp (fst (rep z))) as [s|[|]| |s mw ew Hw]; intros Hle Hm.
- pose proof (tn_le_fin b (B754_zero s) Fb eq_refl Hle). lra.
- destruct b; try discriminate Fb; discriminate Hle.
- discriminate Hm.
- destruct Hm.
- pose proof (tn_le_fin b (B754_finite s mw ew Hw) Fb eq_refl Hle). lra.
Qed.

Lemma tn_with_valid :
  forall q, is_finite q = true -> valid (Interval.with_infsup_raw q q).
Proof.
intros q Fq. unfold valid, Interval.with_infsup_raw, Generic.constant. cbn [rep].
right. unfold opp. rewrite Bopp_involutive. split; [|split].
- rewrite Bleb_correct by exact Fq. apply Rle_bool_true, Rle_refl.
- destruct q; try discriminate Fq; discriminate.
- destruct q; try discriminate Fq; discriminate.
Qed.

Lemma tn_mem_with :
  forall q, is_finite q = true -> mem (B2R q) (Interval.with_infsup_raw q q).
Proof.
intros q Fq. unfold mem, Interval.with_infsup_raw, Generic.constant. cbn [rep fst snd].
unfold opp. rewrite Bopp_involutive.
destruct q; try discriminate Fq; split; apply Rle_refl.
Qed.

Lemma tn_mul_le : forall u v w, 0 < w -> u <= v -> u * w <= v * w.
Proof.
intros u v w Hw H. apply Rmult_le_compat_r; lra.
Qed.

(** [cont] in [Interval::tan_impl] is computed, and if it is true for a
    finite [qb = k] with [k <> 0], then [b < k * (PI / 2)]: [b] is at most
    the lower bound of [[qb, qb] * FRAC_PI_2], which is at most [k * lo]
    for [k > 0] and [k * hi] for [k < 0], where [lo] and [hi] are the
    bounds of [FRAC_PI_2], and both are below [k * (PI / 2)] as
    [lo < PI / 2 < hi]. *)
Lemma tn_cont :
  forall has_fma (qb b : f64), qb = B754_infinity false \/ is_finite qb = true ->
  exists cb,
    (if negb (Model.eq qb (B754_infinity false)) then
       let* p := Interval.mul has_fma (Interval.with_infsup_raw qb qb) Interval.FRAC_PI_2 in
       Some (Model.le b (Interval.inf_raw p))
     else Some false) = Some cb /\
    (cb = true -> is_finite qb = true -> is_finite b = true ->
     forall k, B2R qb = IZR k -> k <> 0%Z -> B2R b < IZR k * (PI / 2)).
Proof.
intros has_fma qb b [->|Fq].
- exists false. split; [reflexivity|]. intros E; discriminate E.
- assert (E : Model.eq qb (B754_infinity false) = false)
    by (destruct qb; try discriminate Fq; reflexivity).
  rewrite E. cbn [negb].
  destruct FRAC_PI_2_const as (HC & HCn & Flo & Fhi & H1 & Hlo & Hhi).
  destruct (mul_correct has_fma (Interval.with_infsup_raw qb qb) Interval.FRAC_PI_2
    (tn_with_valid qb Fq) HC) as (p & Ep & Hp).
  rewrite Ep. eexists. split; [reflexivity|].
  intros Hle _ Fb k Hk Hk0.
  assert (Ht : exists t, mem t Interval.FRAC_PI_2 /\ IZR k * t < IZR k * (PI / 2)).
  { destruct (Z.lt_ge_cases 0 k) as [Kp|Kn].
    - exists (B2R (Interval.inf_raw Interval.FRAC_PI_2)).
      split; [exact (mono_mem_inf _ HC HCn Flo)|].
      apply Rmult_lt_compat_l; [apply IZR_lt; exact Kp | exact Hlo].
    - exists (B2R (Interval.sup_raw Interval.FRAC_PI_2)).
      split; [exact (mono_mem_sup _ HC HCn Fhi)|].
      assert (IZR k < 0) by (apply IZR_lt; lia). nra. }
  destruct Ht as (t & Ht & Hkt).
  assert (Hm : mem (B2R qb * t) p).
  { apply (proj1 (proj2 Hp)). exists (B2R qb), t.
    split; [exact (tn_mem_with qb Fq)|]. split; [exact Ht | reflexivity]. }
  rewrite Hk in Hm.
  pose proof (tn_le_lower b _ _ Fb Hle Hm). lra.
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

Lemma tn_bounded :
  forall x, finite_itv x -> bounded (fun r => mem r x).
Proof.
intros x Hf. exists (Rabs (B2R (Interval.inf_raw x)) + Rabs (B2R (Interval.sup_raw x))).
intros r Hr. apply (finite_itv_mem x r Hf) in Hr.
unfold Rabs. repeat case Rcase_abs; intros; lra.
Qed.

(** The two results of [Interval::tan_impl] for a nonempty [x], with what
    [tn_impl] says of them: the [com] form, when it is the tightest and
    [x] a bounded subset of the domain, and [[-inf, +inf]] with [trv]. *)
Lemma tn_res_com :
  forall has_fma x y, finite_itv x -> (forall r, mem r x -> tan_dom r) ->
  is_tightest (image_dom tan_dom tan x) y ->
  encloses (image_dom tan_dom tan x) y /\
  ((forall r, ~ mem r x) -> Interval.is_empty y = true) /\
  (Com = Trv \/ (Com = Com /\ (forall r, mem r x -> tan_dom r) /\ bounded (fun r => mem r x))) /\
  (trig_tight has_fma Interval.FRAC_PI_2 (PI / 2) PI x ->
   is_tightest (image_dom tan_dom tan x) y /\
   (Com = Trv -> ~ ((exists r, mem r x) /\ forall r, mem r x -> tan_dom r))).
Proof.
intros has_fma x y Hf HD Ht.
split; [exact (conj (proj1 Ht) (proj1 (proj2 Ht)))|].
split.
{ intros N. destruct (nonempty_mem x (proj1 Hf) (proj1 (proj2 Hf))) as (r & Hr).
  destruct (N r Hr). }
split; [right; split; [reflexivity|]; split; [exact HD | exact (tn_bounded x Hf)]|].
intros _. split; [exact Ht | intros E; discriminate E].
Qed.

Lemma tn_res_entire :
  forall has_fma x, valid x -> Interval.is_empty x = false ->
  (trig_tight has_fma Interval.FRAC_PI_2 (PI / 2) PI x ->
   is_tightest (image_dom tan_dom tan x) Interval.ENTIRE /\
   ~ (forall s, mem s x -> tan_dom s)) ->
  encloses (image_dom tan_dom tan x) Interval.ENTIRE /\
  ((forall r, ~ mem r x) -> Interval.is_empty Interval.ENTIRE = true) /\
  (Trv = Trv \/ (Trv = Com /\ (forall r, mem r x -> tan_dom r) /\ bounded (fun r => mem r x))) /\
  (trig_tight has_fma Interval.FRAC_PI_2 (PI / 2) PI x ->
   is_tightest (image_dom tan_dom tan x) Interval.ENTIRE /\
   (Trv = Trv -> ~ ((exists r, mem r x) /\ forall r, mem r x -> tan_dom r))).
Proof.
intros has_fma x Hx Hn Ht.
split; [apply br_entire_encl|].
split.
{ intros N. destruct (nonempty_mem x Hx Hn) as (r & Hr). destruct (N r Hr). }
split; [left; reflexivity|].
intros Htt. destruct (Ht Htt) as (H1 & H2). split; [exact H1|].
intros _ (_ & HD). exact (H2 HD).
Qed.

Section TnImpl.

Variables (emin emax : Z) (m : mpfr) (has_fma : bool).

Hypothesis Hrange : range_ok emin emax.
Hypothesis Hget : get_d_ok emin emax m.
Hypothesis Htan : tan_ok emin emax m.
Hypothesis Hpi : pi_irrational.

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
Proof using Hrange Hget Htan Hpi.
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
Proof using Hrange Hget Htan Hpi.
intros x Hf Eab.
pose proof (tan_dom_f64 Hpi (Interval.inf_raw x) (proj1 (proj2 (proj2 Hf)))) as Da.
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
Proof using Hrange Hget Htan Hpi.
intros x k Hf Hk [H1 H2].
pose proof (tan_pole k Hk) as Np.
pose proof (tan_dom_f64 Hpi (Interval.sup_raw x) (proj2 (proj2 (proj2 Hf)))) as Db.
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

(** Under [trig_tight], a bounded [x] with [a <> b] for which an exact
    reduction would show a pole in [(a, b]] gets the tightest result
    [[-inf, +inf]], and has a real outside the domain. *)
Lemma tn_entire_tight :
  forall x z, finite_itv x ->
  Model.eq (Interval.inf_raw x) (Interval.sup_raw x) = false ->
  Interval.div has_fma x Interval.FRAC_PI_2 = Some z ->
  (is_hull (image (fun r => Rfloor (r / (PI / 2))) x) (Interval.floor z) ->
   exists k, Z.odd k = true /\
     B2R (Interval.inf_raw x) < IZR k * (PI / 2) <= B2R (Interval.sup_raw x)) ->
  trig_tight has_fma Interval.FRAC_PI_2 (PI / 2) PI x ->
  is_tightest (image_dom tan_dom tan x) Interval.ENTIRE /\
  ~ (forall s, mem s x -> tan_dom s).
Proof using Hrange Hget Htan Hpi.
intros x z Hf Eab Ez Hk [Hs|[(r & t & Hr & Ht & Hw)|He]].
- destruct Hf as (Hx & Hn & _). rewrite (proj2 (bounds_eq x Hx Hn) Hs) in Eab.
  discriminate Eab.
- apply (tn_wide x r t Hw). intros s Hs. apply (finite_itv_mem x s Hf).
  apply (finite_itv_mem x r Hf) in Hr. apply (finite_itv_mem x t Hf) in Ht. lra.
- destruct (Hk (He z Ez)) as (k & Hk1 & Hk2). exact (tn_pole_in x k Hf Hk1 Hk2).
Qed.

(** What the theorems need of [Interval::tan_impl]: it returns [(y, e)]
    with [y] an enclosure, empty for an empty [x]; [e] is [trv], or [com]
    for a bounded [x] in the domain; and under [trig_tight], [y] is the
    tightest, and [e] is [trv] only if [x] is empty or holds a pole. *)
Lemma tn_impl :
  forall x, valid x ->
  exists y e, Interval.tan_impl m has_fma x = Some (y, e) /\
  encloses (image_dom tan_dom tan x) y /\
  ((forall r, ~ mem r x) -> Interval.is_empty y = true) /\
  (e = Trv \/ (e = Com /\ (forall r, mem r x -> tan_dom r) /\ bounded (fun r => mem r x))) /\
  (trig_tight has_fma Interval.FRAC_PI_2 (PI / 2) PI x ->
   is_tightest (image_dom tan_dom tan x) y /\
   (e = Trv -> ~ ((exists r, mem r x) /\ forall r, mem r x -> tan_dom r))).
Proof using Hrange Hget Htan Hpi.
intros x Hx.
destruct (Interval.is_empty x) eqn:Hn.
{ (* An empty [x] is returned with [trv]. *)
  exists x, Trv. unfold Interval.tan_impl. rewrite Hn. split; [reflexivity|].
  assert (Nm : forall r, ~ mem r x) by (intros r; exact (mem_empty x r Hx Hn)).
  split; [split; [exact Hx | intros s (r & Hr & _); destruct (Nm r Hr)]|].
  split; [intros _; reflexivity|].
  split; [left; reflexivity|].
  intros _. split.
  - split; [exact Hx|]. split; [intros s (r & Hr & _); destruct (Nm r Hr)|].
    intros w _ _ r Hr. destruct (Nm r Hr).
  - intros _ ((r & Hr) & _). exact (Nm r Hr). }
destruct (trig_reduce has_fma _ _ x FRAC_PI_2_const Hx Hn) as (z & Ez & Hlo & Hhi).
unfold Interval.tan_impl. rewrite Hn. cbv zeta. rewrite Ez.
set (a := Interval.inf_raw x) in *.
set (b := Interval.sup_raw x) in *.
set (qa := Interval.inf_raw (Interval.floor z)) in *.
set (qb := Interval.sup_raw (Interval.floor z)) in *.
assert (Qb : qb = B754_infinity false \/ is_finite qb = true)
  by (destruct Hhi as [(_ & E)|(_ & F & _)]; [left; exact E | right; exact F]).
destruct (tn_cont has_fma qb b Qb) as (cb & Ecb & Hcb). rewrite Ecb.
destruct tn_consts as (EZZ & EZ1 & E1Z & E11 & LZ1 & LZ2 & LI1 & EI1 & LI2 & EI2).
pose proof PI_RGT_0 as Hpi0.
assert (La : a = B754_infinity true \/ is_finite a = true)
  by (destruct Hlo as [(E & _)|(F & _)]; [left | right]; assumption).
assert (Lb : b = B754_infinity false \/ is_finite b = true)
  by (destruct Hhi as [(E & _)|(F & _)]; [left | right]; assumption).
match goal with |- ?G => assert (Unb : a = B754_infinity true \/ b = B754_infinity false -> G) end.
{ (* An infinite bound gives [n = +inf], so [[-inf, +inf]], the tightest
     as [x] holds a whole period. *)
  intros Hab. rewrite (tn_eq_unb a b La Lb Hab).
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
  rewrite (n_inf qa qb (proj1 Nqa) (proj1 Nqb) (proj2 Nqa) (proj2 Nqb) Hq).
  rewrite LI1, EI1, LI2, EI2. cbn [orb andb]. rewrite !Bool.andb_false_r. cbn [orb].
  eexists _, _. split; [reflexivity|].
  destruct (tn_unb_wide x Hx Hn Hab) as (r & t & Hw & Hm).
  apply tn_res_entire; [exact Hx | exact Hn |]. intros _. exact (tn_wide x r t Hw Hm). }
destruct La as [Ea|Fa]; [exact (Unb (or_introl Ea))|].
destruct Lb as [Eb|Fb]; [exact (Unb (or_intror Eb))|].
clear Unb.
destruct Hlo as [(Ea & _)|(_ & Fqa & ka & Hka & Hka1 & Hka2)];
  [rewrite Ea in Fa; discriminate Fa|].
destruct Hhi as [(Eb & _)|(_ & Fqb & kb & Hkb & Hkb1)];
  [rewrite Eb in Fb; discriminate Fb|].
assert (Hf : finite_itv x) by exact (conj Hx (conj Hn (conj Fa Fb))).
destruct (nonempty_mem x Hx Hn) as (r0 & Hr0).
pose proof (proj1 (finite_itv_mem x r0 Hf) Hr0) as Hab. fold a b in Hab.
assert (Hle : (ka <= kb)%Z).
{ destruct (Z.le_gt_cases ka kb) as [H|H]; [exact H|]. exfalso.
  assert (H' : IZR kb + 1 <= IZR ka) by (rewrite <- plus_IZR; apply IZR_le; lia).
  pose proof (tn_mul_le _ _ (PI / 2) ltac:(lra) H'). lra. }
rewrite (rem_euclid_2_int qa ka Fqa Hka).
destruct (Model.eq a b) eqn:Eab.
{ (* [a == b]: [n = 0], and both parities give the [com] form. *)
  rewrite LZ1, LZ2. cbn [orb]. rewrite !Bool.andb_true_r.
  destruct (tn_single x Hf (proj2 (proj2 (bounds_eq_finite x Hx Hn Eab)))) as (HD & Ht).
  destruct (Z.even ka); [rewrite EZZ | rewrite E1Z, E11]; cbn [orb];
    (eexists _, _; split; [reflexivity|]); exact (tn_res_com has_fma x _ Hf HD Ht). }
pose proof (n_small qa qb ka kb Fqa Fqb Hka Hkb Hle) as HN. cbv zeta in HN.
destruct HN as (_ & Nj).
destruct (Nj 1%Z ltac:(lia)) as (L1 & _ & E1).
destruct (Nj 2%Z ltac:(lia)) as (L2 & _ & E2).
rewrite L1, E1, L2, E2.
(* The exact floors of [a / (PI / 2)] and [b / (PI / 2)], if the reduction
   is exact. *)
assert (Hex : is_hull (image (fun r => Rfloor (r / (PI / 2))) x) (Interval.floor z) ->
  B2R a < (IZR ka + 1) * (PI / 2) /\ IZR kb * (PI / 2) <= B2R b).
{ intros Hhull.
  destruct (trig_reduce_exact has_fma _ _ x z FRAC_PI_2_const Hx Hn Ez Hhull) as (Xa & Xb).
  specialize (Xa Fa). specialize (Xb Fb). fold a b qa qb in Xa, Xb.
  rewrite Hka in Xa. rewrite Hkb in Xb. unfold Rfloor in Xa, Xb.
  apply eq_IZR in Xa, Xb.
  pose proof (floor_div_bounds (PI / 2) (B2R a) ltac:(lra)) as Ba.
  pose proof (floor_div_bounds (PI / 2) (B2R b) ltac:(lra)) as Bb.
  unfold Rfloor in Ba, Bb. rewrite <- Xa in Ba. rewrite <- Xb in Bb. lra. }
destruct (Z.even ka) eqn:Ev.
- (* [qa] is even: the piece is [((ka - 1) * c, (ka + 1) * c)], with
     [b] below its end if [n = 0], or [n = 1] and [cont]. *)
  rewrite EZZ, EZ1. cbn [andb]. rewrite Bool.orb_false_r.
  assert (Od : Z.odd (ka - 1) = true) by (rewrite Z.sub_1_r, Z.odd_pred; exact Ev).
  destruct ((kb - ka <? 1)%Z) eqn:D0; cbn [orb].
  { apply Z.ltb_lt in D0. assert (Ek : kb = ka) by lia. subst kb.
    destruct (tn_piece x (ka - 1) Hf Od) as (HD & Ht);
      [rewrite minus_IZR; fold a b; lra | rewrite minus_IZR; fold a b; lra|].
    eexists _, _. split; [reflexivity|]. exact (tn_res_com has_fma x _ Hf HD Ht). }
  destruct ((kb - ka =? 1)%Z && cb) eqn:D1.
  { apply andb_prop in D1. destruct D1 as (D1 & ->). apply Z.eqb_eq in D1.
    assert (Kb0 : kb <> 0%Z).
    { intros E. assert (Ek : ka = (-1)%Z) by lia. rewrite Ek in Ev. discriminate Ev. }
    pose proof (Hcb eq_refl Fqb Fb kb Hkb Kb0) as Hb2.
    replace kb with (ka + 1)%Z in Hb2 by lia. rewrite plus_IZR in Hb2.
    destruct (tn_piece x (ka - 1) Hf Od) as (HD & Ht);
      [rewrite minus_IZR; fold a b; lra | rewrite minus_IZR; fold a b; lra|].
    eexists _, _. split; [reflexivity|]. exact (tn_res_com has_fma x _ Hf HD Ht). }
  (* Otherwise [kb >= ka + 1], and an exact reduction shows the pole
     [(ka + 1) * c] in [(a, b]]. *)
  eexists _, _. split; [reflexivity|].
  apply tn_res_entire; [exact Hx | exact Hn|]. intros Htt.
  apply (tn_entire_tight x z Hf Eab Ez); [|exact Htt].
  intros Hhull. destruct (Hex Hhull) as (Xa & Xb). apply Z.ltb_ge in D0.
  exists (ka + 1)%Z. split; [rewrite Z.add_1_r, Z.odd_succ; exact Ev|].
  rewrite plus_IZR. fold a b. split; [lra|].
  assert (H : IZR ka + 1 <= IZR kb) by (rewrite <- plus_IZR; apply IZR_le; lia).
  pose proof (tn_mul_le _ _ (PI / 2) ltac:(lra) H). lra.
- (* [qa] is odd, so not 0 and [a > ka * c]: the piece is
     [(ka * c, (ka + 2) * c)], with [b] below its end if [n <= 1], or
     [n = 2] and [cont]. *)
  rewrite E1Z, E11. cbn [andb orb].
  assert (Od : Z.odd ka = true) by (rewrite <- Z.negb_even, Ev; reflexivity).
  assert (Ka0 : ka <> 0%Z) by (intros E; rewrite E in Od; discriminate Od).
  pose proof (Hka2 Ka0) as Ha2.
  destruct ((kb - ka <? 2)%Z) eqn:D0; cbn [orb].
  { apply Z.ltb_lt in D0.
    assert (H : IZR kb + 1 <= IZR ka + 2) by (rewrite <- !plus_IZR; apply IZR_le; lia).
    pose proof (tn_mul_le _ _ (PI / 2) ltac:(lra) H).
    destruct (tn_piece x ka Hf Od) as (HD & Ht); [fold a b; lra | fold a b; lra|].
    eexists _, _. split; [reflexivity|]. exact (tn_res_com has_fma x _ Hf HD Ht). }
  destruct ((kb - ka =? 2)%Z && cb) eqn:D1.
  { apply andb_prop in D1. destruct D1 as (D1 & ->). apply Z.eqb_eq in D1.
    assert (Kb0 : kb <> 0%Z).
    { intros E. assert (Ek : ka = (-2)%Z) by lia. rewrite Ek in Ev. discriminate Ev. }
    pose proof (Hcb eq_refl Fqb Fb kb Hkb Kb0) as Hb2.
    replace kb with (ka + 2)%Z in Hb2 by lia. rewrite plus_IZR in Hb2.
    destruct (tn_piece x ka Hf Od) as (HD & Ht); [fold a b; lra | fold a b; lra|].
    eexists _, _. split; [reflexivity|]. exact (tn_res_com has_fma x _ Hf HD Ht). }
  (* Otherwise [kb >= ka + 2], and an exact reduction shows the pole
     [(ka + 2) * c] in [(a, b]]. *)
  eexists _, _. split; [reflexivity|].
  apply tn_res_entire; [exact Hx | exact Hn|]. intros Htt.
  apply (tn_entire_tight x z Hf Eab Ez); [|exact Htt].
  intros Hhull. destruct (Hex Hhull) as (Xa & Xb). apply Z.ltb_ge in D0.
  exists (ka + 2)%Z. split.
  { replace (ka + 2)%Z with (Z.succ (Z.succ ka)) by lia.
    rewrite Z.odd_succ, Z.even_succ. exact Od. }
  rewrite plus_IZR. fold a b. split; [lra|].
  assert (H : IZR ka + 2 <= IZR kb) by (rewrite <- plus_IZR; apply IZR_le; lia).
  pose proof (tn_mul_le _ _ (PI / 2) ltac:(lra) H). lra.
Qed.

End TnImpl.

Theorem tan_encloses :
  forall emin emax m has_fma x,
  range_ok emin emax -> get_d_ok emin emax m -> tan_ok emin emax m ->
  pi_irrational -> valid x ->
  exists y, Interval.tan m has_fma x = Some y /\
    encloses (image_dom tan_dom tan x) y.
Proof.
intros emin emax m has_fma x Hrange Hget Htan Hpi Hx.
destruct (tn_impl emin emax m has_fma Hrange Hget Htan Hpi x Hx)
  as (y & e & Ei & Henc & _).
exists y. unfold Interval.tan. rewrite Ei. split; [reflexivity | exact Henc].
Qed.

Theorem tan_correct :
  forall emin emax m has_fma x,
  range_ok emin emax -> get_d_ok emin emax m -> tan_ok emin emax m ->
  pi_irrational -> valid x ->
  trig_tight has_fma Interval.FRAC_PI_2 (PI / 2) PI x ->
  exists y, Interval.tan m has_fma x = Some y /\
    is_tightest (image_dom tan_dom tan x) y.
Proof.
intros emin emax m has_fma x Hrange Hget Htan Hpi Hx Htt.
destruct (tn_impl emin emax m has_fma Hrange Hget Htan Hpi x Hx)
  as (y & e & Ei & _ & _ & _ & Ht).
exists y. unfold Interval.tan. rewrite Ei. split; [reflexivity | exact (proj1 (Ht Htt))].
Qed.

Theorem dec_tan_correct :
  forall emin emax m has_fma x,
  range_ok emin emax -> get_d_ok emin emax m -> tan_ok emin emax m ->
  pi_irrational -> valid (itv x) ->
  exists y, DecInterval.tan m has_fma x = Some y /\
    if DecInterval.is_nai x then y = DecInterval.NAI
    else
      encloses (image_dom tan_dom tan (itv x)) (itv y) /\
      (exists d, p_dom tan_dom d tan (itv x) (itv y) /\ dec y = dec_min d (dec x)) /\
      (trig_tight has_fma Interval.FRAC_PI_2 (PI / 2) PI (itv x) ->
       is_tightest (image_dom tan_dom tan (itv x)) (itv y) /\
       exists d, strongest_dom tan_dom d tan (itv x) (itv y) /\
         dec y = dec_min d (dec x)).
Proof.
intros emin emax m has_fma x Hrange Hget Htan Hpi Hx.
destruct (tn_impl emin emax m has_fma Hrange Hget Htan Hpi (itv x) Hx)
  as (y & e & Ei & Henc & Hemp & He & Ht).
unfold DecInterval.tan. rewrite Ei. eexists. split; [reflexivity|]. cbn [fst snd].
destruct (DecInterval.is_nai x) eqn:Enai.
- (* NaI: [dec_min] keeps [ill], and [set_dec] returns NaI. *)
  destruct x as [w []]; try discriminate Enai. destruct e; reflexivity.
- assert (Hd : dec x <> Ill).
  { intros E. unfold DecInterval.is_nai in Enai. rewrite E in Enai. discriminate Enai. }
  (* [tan] is continuous on its domain, and [e] is [trv], or [com] for a
     bounded [x] in the domain. *)
  assert (He' : e = Trv \/
    (e = Com /\ (forall r, mem r (itv x) -> tan_dom r) /\
     (dec x = Com -> Interval.is_common_interval y = true ->
      bounded (fun r => mem r (itv x))))).
  { destruct He as [E|(E & HD & Hb)]; [left; exact E|].
    right. split; [exact E|]. split; [exact HD | intros _ _; exact Hb]. }
  pose proof (trig_set_dec_correct tan_dom tan x y e Hx Hd Henc Hemp
    (fun r _ Hr => continuity_pt_continue_in tan tan_dom r (tan_dom_cont r Hr)) He')
    as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [exact H3|].
  intros Htt. destruct (Ht Htt) as (Ht1 & Ht2).
  split; [exact (H2 Ht1) | exact (H4 Ht2)].
Qed.
