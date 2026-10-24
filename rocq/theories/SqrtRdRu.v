(** * [sqrt_rd_ru] rounds down and up

    [sqrt_rd_ru] is the IEEE 754 square root of lane 0 rounded toward -inf
    and of lane 1 rounded toward +inf, i.e. Flocq's [Bsqrt mode_DN] and
    [Bsqrt mode_UP], including zeros, negative inputs, the infinities and
    NaN, both with and without an FMA. One nested call through
    [sqrt1_slow] is always enough.

    The fast path, [sqrt1_fast], computes [s = RN(sqrt x)] and the
    remainder [r = x - s * s] with one FMA or with Dekker's TwoProduct.
    If it accepts [x] and [x] is positive, [r] is a float [BD03] (S. Boldo,
    M. Daumas, Representable correcting terms for possibly underflowing
    floating point operations, ARITH 2003) and is computed exactly
    ([sqrt1_fast_rem]), and [r > 0] iff [s < sqrt x]. [sqrt1_ru_impl]
    then steps [s] up if [r > 0], and [sqrt1_rd_impl] steps it down if
    [r < 0], which is stepping [-s = RN(-sqrt x)] up and negating
    ([step_down]). If it accepts a negative [x], [s] and [r] are NaN, and
    so is the result, as the comparisons with NaN are false.

    A stepped [s] [rounds_up_to] [sqrt x] (or [-sqrt x]), and for a
    positive finite [x], [sqrt x < 2^512], so rounding it never
    overflows, and such a float is [Bsqrt mode_UP x] (or
    [-Bsqrt mode_DN x]). The inputs that the fast path rejects go to
    [sqrt1_slow], which scales positive finite inputs into its range and
    returns [fsqrt x] for the others ([sqrt1_slow_correct]). *)

From Stdlib Require Import Bool ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Spec TwoSum RoundUpExact StepUp MulRu
  SqrtRem SqrtFast SqrtSlow.

Open Scope R_scope.

(** For a positive finite [x], [Bsqrt m x] is finite and positive, and it
    is [sqrt x] rounded with [m], which is at most [2^512]. *)
Lemma Bsqrt_pos_bound :
  forall m (x : f64), is_finite x = true -> 0 < B2R x ->
  is_finite (Bsqrt m x) = true /\ Bsign (Bsqrt m x) = false /\
  B2R (Bsqrt m x) = round radix2 fexp64 (round_mode m) (sqrt (B2R x)) /\
  0 <= B2R (Bsqrt m x) <= bpow radix2 512.
Proof.
intros m x Fx Hx.
destruct (@Bsqrt_correct 53 1024 _ _ m x) as (HR & HF & HS).
change (SpecFloat.fexp 53 1024) with fexp64 in HR.
(* [x] is positive, so it is [B754_finite false ..]. *)
assert (Sx : Bsign x = false).
{ rewrite (Bsign_B2R x Fx) by lra. apply Rlt_bool_false. lra. }
assert (Fs : is_finite (Bsqrt m x) = true).
{ rewrite HF. clear HR HF HS Hx.
  destruct x as [s|s| |[|] mx ex Hex];
    try discriminate Fx; try discriminate Sx; reflexivity. }
(* [x < 2^1024 = 2^512 * 2^512], so [sqrt x < 2^512]. *)
assert (Hs : 0 < sqrt (B2R x) < bpow radix2 512).
{ split; [now apply sqrt_lt_R0|].
  assert (H1 := @abs_B2R_lt_emax 53 1024 x). rewrite Rabs_pos_eq in H1 by lra.
  assert (H2 := sqrt_sqrt (B2R x) (Rlt_le _ _ Hx)).
  assert (H3 : bpow radix2 1024 = bpow radix2 512 * bpow radix2 512)
    by (rewrite <- bpow_plus; reflexivity).
  assert (H4 := bpow_gt_0 radix2 512).
  assert (H5 := sqrt_pos (B2R x)).
  nra. }
split; [exact Fs|].
split; [rewrite HS by (apply finite_not_nan; exact Fs); exact Sx|].
split; [exact HR|].
(* [0] and [2^512] are floats, so rounding keeps [sqrt x] between them. *)
rewrite HR. split.
- apply round_ge_generic; [typeclasses eauto | typeclasses eauto
  | apply generic_format_0 | lra].
- apply round_le_generic; [typeclasses eauto | typeclasses eauto
  | apply generic_format_FLT_bpow; [typeclasses eauto | lia] | lra].
Qed.

(** For a positive finite [x], a float that is [sqrt x] rounded up as
    [rounds_up_to] describes is [Bsqrt mode_UP x]. *)
Lemma Bsqrt_rounds_up :
  forall x r : f64, is_finite x = true -> 0 < B2R x ->
  rounds_up_to (sqrt (B2R x)) r -> r = Bsqrt mode_UP x.
Proof.
intros x r Fx Hx Hr.
destruct (Bsqrt_pos_bound mode_UP x Fx Hx) as (Fs & Ss & HR & Hb).
change (round_mode mode_UP) with Zceil in HR.
assert (Hs := sqrt_lt_R0 _ Hx).
(* [RU(sqrt x) <= 2^512] does not overflow, and [sqrt x] is positive. *)
assert (Hb' : Rabs (RU (sqrt (B2R x))) < bpow radix2 1024).
{ rewrite <- HR, Rabs_pos_eq by lra.
  apply Rle_lt_trans with (1 := proj2 Hb). apply bpow_lt. lia. }
unfold rounds_up_to in Hr.
rewrite (Rlt_bool_true _ _ Hb'), (Rlt_bool_false (sqrt (B2R x)) 0) in Hr
  by lra.
destruct Hr as (HR' & HF & HS).
apply B2R_Bsign_inj; [exact HF | exact Fs | now rewrite HR', HR |].
now rewrite HS, Ss.
Qed.

(** For a positive finite [x], if [w] is [-sqrt x] rounded up as
    [rounds_up_to] describes, [-w] is [Bsqrt mode_DN x]. *)
Lemma Bsqrt_rounds_down :
  forall x w : f64, is_finite x = true -> 0 < B2R x ->
  rounds_up_to (- sqrt (B2R x)) w -> Bopp w = Bsqrt mode_DN x.
Proof.
intros x w Fx Hx Hw.
destruct (Bsqrt_pos_bound mode_DN x Fx Hx) as (Fs & Ss & HR & Hb).
change (round_mode mode_DN) with Zfloor in HR.
assert (Hs := sqrt_lt_R0 _ Hx).
(* Rounding [-sqrt x] up is rounding [sqrt x] down and negating. *)
assert (Ho : RU (- sqrt (B2R x)) = - B2R (Bsqrt mode_DN x)).
{ rewrite HR. apply round_UP_opp. }
(* [|RU(-sqrt x)| <= 2^512] does not overflow, and [-sqrt x] is
   negative. *)
assert (Hb' : Rabs (RU (- sqrt (B2R x))) < bpow radix2 1024).
{ rewrite Ho, Rabs_Ropp, Rabs_pos_eq by lra.
  apply Rle_lt_trans with (1 := proj2 Hb). apply bpow_lt. lia. }
unfold rounds_up_to in Hw.
rewrite (Rlt_bool_true _ _ Hb'), (Rlt_bool_true (- sqrt (B2R x)) 0) in Hw
  by lra.
destruct Hw as (HR' & HF & HS).
apply B2R_Bsign_inj.
- rewrite is_finite_Bopp. exact HF.
- exact Fs.
- rewrite B2R_Bopp, HR', Ho. ring.
- rewrite Bsign_Bopp, HS, Ss by (apply finite_not_nan; exact HF).
  reflexivity.
Qed.

(** ** The fast path *)

Lemma Rlt_bool_true_iff : forall a b, Rlt_bool a b = true <-> a < b.
Proof.
intros a b.
destruct (Rlt_bool_spec a b); split; intros H'; first [reflexivity | discriminate | lra].
Qed.

(** If [sqrt1_fast] accepts [x], either [x] is positive, [s = RN(sqrt x)]
    and [r = x - s * s] exactly, or [x] is negative and [s], [r] and the
    square root of [x] in every mode are NaN. [ok] rules out zero, whose
    exponent is [-1023], and infinity and NaN, whose exponent is [1024]. *)
Lemma sqrt1_fast_cases :
  forall fma x s r, Generic.sqrt1_fast fma x = (s, r, true) ->
  (is_finite x = true /\ 0 < B2R x /\
   is_finite s = true /\ B2R s = RN (sqrt (B2R x)) /\ 0 < B2R s /\
   is_finite r = true /\ B2R r = B2R x - B2R s * B2R s) \/
  (s = B754_nan /\ r = B754_nan /\ forall m, Bsqrt m x = B754_nan).
Proof.
intros fma x s r E.
assert (Hok : snd (Generic.sqrt1_fast fma x) = true) by (rewrite E; reflexivity).
assert (He : (-966 <= Generic.exponent x <= 1023)%Z).
{ rewrite sqrt1_fast_eq in Hok. cbn [snd] in Hok.
  rewrite andb_true_iff, !Z.leb_le in Hok. destruct fma; lia. }
assert (Fx : is_finite x = true).
{ rewrite <- is_finite_eq. apply Z.ltb_lt. lia. }
assert (Hx0 : bpow radix2 (-966) <= Rabs (B2R x)).
{ apply Rle_trans with (bpow radix2 (Generic.exponent x));
    [apply bpow_le; lia | apply bpow_exponent_le_abs_B2R; [exact Fx | lia]]. }
pose proof (bpow_gt_0 radix2 (-966)) as H966.
destruct (Rlt_le_dec 0 (B2R x)) as [Hx|Hx].
- left.
  rewrite Rabs_pos_eq in Hx0 by lra.
  (* [x >= 2^-966], so [x - s * s] is a float [BD03]. *)
  pose proof (sqrt1_fast_rem fma x Fx Hx Hok
    (sqrt_rem_format (B2R x) (generic_format_B2R 53 1024 x) Hx0)) as H.
  cbv zeta in H. rewrite E in H. cbn [fst snd] in H.
  tauto.
- right.
  (* [x] is a negative finite float. *)
  destruct x as [sx|sx| |[|] mx ex Bx]; try discriminate Fx.
  + cbn [B2R] in Hx0. rewrite Rabs_R0 in Hx0. lra.
  + rewrite sqrt1_fast_eq in E.
    apply pair_equal_spec in E as [E _].
    apply pair_equal_spec in E as [Es Er].
    subst s r.
    split; [reflexivity|].
    split; [destruct fma; reflexivity | intros m; reflexivity].
  + exfalso. revert Hx. apply Rlt_not_le.
    cbn [B2R]. apply F2R_gt_0. cbn. lia.
Qed.

(** On the fast path, [sqrt1_ru_impl] steps [s = RN(sqrt x)] up if
    [r = x - s * s > 0], i.e. if [s < sqrt x]. *)
Theorem sqrt1_ru_fast_correct :
  forall fma x s r, Generic.sqrt1_fast fma x = (s, r, true) ->
  (if gt r zero then Generic.step_up s else s) = Bsqrt mode_UP x.
Proof.
intros fma x s r E.
destruct (sqrt1_fast_cases fma x s r E)
  as [(Fx & Hx & Fs & Hs & Hs0 & Fr & Hr) | (-> & -> & HN)].
2: { rewrite HN. reflexivity. }
apply Bsqrt_rounds_up; [exact Fx | exact Hx |].
apply step_up_rounds_up_iff; [exact Fs | exact Hs | intros H0; lra |].
destruct (sqrt_rem_sign (B2R x) (B2R s) ltac:(lra) Hs0) as (Hlt & _).
unfold gt. rewrite Bltb_correct by first [reflexivity | exact Fr].
change (B2R zero) with 0.
rewrite Rlt_bool_true_iff, Hr. exact Hlt.
Qed.

(** On the fast path, [sqrt1_rd_impl] steps [s = RN(sqrt x)] down if
    [r = x - s * s < 0], i.e. if [sqrt x < s]. Stepping [s] down is
    stepping [-s = RN(-sqrt x)] up and negating. *)
Theorem sqrt1_rd_fast_correct :
  forall fma x s r, Generic.sqrt1_fast fma x = (s, r, true) ->
  (if lt r zero then Generic.step_down s else s) = Bsqrt mode_DN x.
Proof.
intros fma x s r E.
destruct (sqrt1_fast_cases fma x s r E)
  as [(Fx & Hx & Fs & Hs & Hs0 & Fr & Hr) | (-> & -> & HN)].
2: { rewrite HN. reflexivity. }
assert (Ho : forall b : bool,
  (if b then Generic.step_down s else s) =
  Bopp (if b then Generic.step_up (opp s) else opp s)).
{ intros []; [reflexivity | symmetry; apply Bopp_involutive]. }
rewrite Ho. clear Ho.
apply Bsqrt_rounds_down; [exact Fx | exact Hx |].
assert (Hos : B2R (opp s) = - B2R s) by apply B2R_Bopp.
apply step_up_rounds_up_iff.
- unfold opp. rewrite is_finite_Bopp. exact Fs.
- rewrite Hos, Hs. symmetry. apply round_NE_opp.
- rewrite Hos. intros H0. lra.
- destruct (sqrt_rem_sign (B2R x) (B2R s) ltac:(lra) Hs0) as (_ & Hlt).
  unfold lt. rewrite Bltb_correct by first [reflexivity | exact Fr].
  change (B2R zero) with 0.
  rewrite Rlt_bool_true_iff, Hr, Hlt, Hos.
  split; intros H0; lra.
Qed.

(** ** Both paths *)

(** [sqrt1_rd_impl n] and [sqrt1_ru_impl n] are correct for any [n] on the
    inputs that the fast path accepts. *)
Lemma sqrt1_rd_impl_fast :
  forall n fma x, snd (Generic.sqrt1_fast fma x) = true ->
  Generic.sqrt1_rd_impl n fma x = Some (Bsqrt mode_DN x).
Proof.
intros n fma x Hok.
destruct n; cbn [Generic.sqrt1_rd_impl];
  destruct (Generic.sqrt1_fast fma x) as ((s, r), ok) eqn:E;
  cbn [snd] in Hok; subst ok;
  f_equal; exact (sqrt1_rd_fast_correct fma x s r E).
Qed.

Lemma sqrt1_ru_impl_fast :
  forall n fma x, snd (Generic.sqrt1_fast fma x) = true ->
  Generic.sqrt1_ru_impl n fma x = Some (Bsqrt mode_UP x).
Proof.
intros n fma x Hok.
destruct n; cbn [Generic.sqrt1_ru_impl];
  destruct (Generic.sqrt1_fast fma x) as ((s, r), ok) eqn:E;
  cbn [snd] in Hok; subst ok;
  f_equal; exact (sqrt1_ru_fast_correct fma x s r E).
Qed.

(** With one nested call left, the inputs that the fast path rejects go to
    [sqrt1_slow], which calls [sqrt1_rd_impl n] only on inputs that the
    fast path accepts. *)
Theorem sqrt1_rd_impl_correct :
  forall n fma x, Generic.sqrt1_rd_impl (S n) fma x = Some (Bsqrt mode_DN x).
Proof.
intros n fma x.
destruct (snd (Generic.sqrt1_fast fma x)) eqn:Hok.
{ now apply sqrt1_rd_impl_fast. }
cbn [Generic.sqrt1_rd_impl].
destruct (Generic.sqrt1_fast fma x) as ((s, r), ok) eqn:E.
cbn [snd] in Hok. subst ok.
apply (sqrt1_slow_correct fma).
intros y Hy. now apply sqrt1_rd_impl_fast.
Qed.

Theorem sqrt1_ru_impl_correct :
  forall n fma x, Generic.sqrt1_ru_impl (S n) fma x = Some (Bsqrt mode_UP x).
Proof.
intros n fma x.
destruct (snd (Generic.sqrt1_fast fma x)) eqn:Hok.
{ now apply sqrt1_ru_impl_fast. }
cbn [Generic.sqrt1_ru_impl].
destruct (Generic.sqrt1_fast fma x) as ((s, r), ok) eqn:E.
cbn [snd] in Hok. subst ok.
apply (sqrt1_slow_correct fma).
intros y Hy. now apply sqrt1_ru_impl_fast.
Qed.

(** [sqrt1_rd], [sqrt1_ru] and [sqrt_rd_ru] are correct whether the target
    has an FMA or not. *)
Theorem sqrt1_rd_correct :
  forall has_fma x, Generic.sqrt1_rd has_fma x = Some (Bsqrt mode_DN x).
Proof.
intros has_fma x. apply sqrt1_rd_impl_correct.
Qed.

Theorem sqrt1_ru_correct :
  forall has_fma x, Generic.sqrt1_ru has_fma x = Some (Bsqrt mode_UP x).
Proof.
intros has_fma x. apply sqrt1_ru_impl_correct.
Qed.

Theorem sqrt_rd_ru_correct :
  forall has_fma x,
  Generic.sqrt_rd_ru has_fma x = Some (Bsqrt mode_DN (fst x), Bsqrt mode_UP (snd x)).
Proof.
intros has_fma x.
unfold Generic.sqrt_rd_ru.
rewrite sqrt1_rd_correct, sqrt1_ru_correct.
reflexivity.
Qed.
