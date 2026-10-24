(** * [div_ru] rounds toward +inf

    [div_ru] is IEEE 754 division rounded toward +inf on both lanes, i.e.
    Flocq's [Bdiv mode_UP], including the sign of a zero, overflow,
    division by zero, the infinities and NaN, both with and without an
    FMA. It never panics.

    The fast path, [div1_ru_fast], computes [q = RN(x / y)] and the
    remainder [r = x - q * y]. If [q] is normal and [|x| >= 2^-967], [r] is
    a float ([div_remainder], after S. Boldo and M. Daumas, Representable
    correcting terms for possibly underflowing floating point operations,
    ARITH 2003), and the code computes it exactly, with an FMA or with
    Dekker's TwoProduct (T. J. Dekker, A floating-point technique for
    extending the available precision, Numer. Math. 18, 1971) and
    Sterbenz's lemma ([div_fma_remainder], [div_dekker_remainder]). It
    steps [q] up to the next float if [r != 0] and [r] has the sign of
    [y]: as [r = (x / y - q) * y], that is exactly when [q < x / y]
    ([div1_ru_fast_tail]). If [x] or [y] is zero or not finite, the
    quotient does not depend on the rounding mode ([div_special]). The
    slow path, [div1_ru_slow], divides the significands as integers and
    rounds the quotient with [round_up_exact]
    ([div1_ru_slow_rounds_up]). *)

From Stdlib Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Spec TwoSum RoundUpExact StepUp MulRu
  DivRuFast DivRuSlow.

Open Scope R_scope.

(** [q] is below [x / y] iff the remainder [r = x - q * y] is nonzero and
    has the sign of [y]. *)
Lemma up_iff :
  forall x y q r : R, y <> 0 -> r = x - q * y ->
  (negb (Req_bool r 0) && Bool.eqb (Rlt_bool 0 r) (Rlt_bool 0 y) = true
   <-> q < x / y).
Proof.
intros x y q r Hy Hr.
(* [r = (x / y - q) * y], so [r] has the sign of [y] iff [q < x / y]. *)
assert (Hr' : r = (x / y - q) * y) by (rewrite Hr; field; exact Hy).
clear Hr.
destruct (Rtotal_order r 0) as [H|[H|H]].
- rewrite (Req_bool_false r 0), (Rlt_bool_false 0 r) by lra.
  destruct (Rdichotomy _ _ Hy) as [Hy'|Hy'];
    [rewrite (Rlt_bool_false 0 y) by lra | rewrite (Rlt_bool_true 0 y) by lra];
    cbn [negb andb Bool.eqb];
    split; intros H'; first [reflexivity | discriminate | exfalso; nra | nra].
- rewrite (Req_bool_true r 0) by exact H.
  cbn [negb andb].
  (* [r = 0] means [q = x / y]. *)
  assert (Hq : x / y - q = 0).
  { destruct (Rmult_integral _ _ (eq_sym (eq_trans (eq_sym H) Hr'))) as [H0|H0];
      [exact H0 | contradiction]. }
  split; intros H'; [discriminate | exfalso; lra].
- rewrite (Req_bool_false r 0), (Rlt_bool_true 0 r) by lra.
  destruct (Rdichotomy _ _ Hy) as [Hy'|Hy'];
    [rewrite (Rlt_bool_false 0 y) by lra | rewrite (Rlt_bool_true 0 y) by lra];
    cbn [negb andb Bool.eqb];
    split; intros H'; first [reflexivity | discriminate | exfalso; nra | nra].
Qed.

(** For finite nonzero [x] and [y], a float that is [x / y] rounded up as
    [rounds_up_to] describes is [Bdiv mode_UP x y]. *)
Lemma Bdiv_rounds_up :
  forall x y r : f64,
  is_finite x = true -> is_finite y = true -> B2R x <> 0 -> B2R y <> 0 ->
  rounds_up_to (B2R x / B2R y) r -> r = Bdiv mode_UP x y.
Proof.
intros x y r Fx Fy Hx0 Hy0 Hr.
(* [Bdiv] gives the quotient the sign [xorb (Bsign x) (Bsign y)], and
   [/ y] has the sign of [y]. *)
assert (Hs : Rlt_bool (B2R x / B2R y) 0 = xorb (Bsign x) (Bsign y)).
{ rewrite (Bsign_B2R x Fx Hx0), (Bsign_B2R y Fy Hy0).
  unfold Rdiv. rewrite Rlt_bool_mult by (auto using Rinv_neq_0_compat).
  f_equal.
  destruct (Rdichotomy _ _ Hy0) as [H|H].
  - rewrite (Rlt_bool_true _ _ H). apply Rlt_bool_true.
    now apply Rinv_lt_0_compat.
  - rewrite (Rlt_bool_false _ _ (Rlt_le _ _ H)). apply Rlt_bool_false.
    apply Rlt_le. now apply Rinv_0_lt_compat. }
unfold rounds_up_to in Hr. rewrite Hs in Hr.
generalize (@Bdiv_correct 53 1024 _ _ mode_UP x y Hy0).
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_UP)) with RU.
destruct (Rlt_bool (Rabs (RU (B2R x / B2R y))) (bpow radix2 1024)).
- destruct Hr as (HR & HF & HS). intros (HR' & HF' & HS').
  rewrite Fx in HF'.
  apply B2R_Bsign_inj; [exact HF | exact HF' | congruence |].
  rewrite HS, HS' by (apply finite_not_nan; exact HF'). reflexivity.
- intros HO. apply B2SF_inj. rewrite Hr, HO. reflexivity.
Qed.

(** The last step of [div1_ru_fast]: given [q = RN(x / y)] and its exact
    remainder [r = x - q * y], stepping [q] up if [r != 0] and
    [(r > 0) == (y > 0)] gives [Bdiv mode_UP x y]. *)
Lemma div1_ru_fast_tail :
  forall x y r : f64,
  is_finite x = true -> is_finite y = true -> B2R x <> 0 -> B2R y <> 0 ->
  is_finite (div x y) = true -> B2R (div x y) = RN (B2R x / B2R y) ->
  B2R (div x y) <> 0 ->
  is_finite r = true -> B2R r = B2R x - B2R (div x y) * B2R y ->
  (if negb (eq r zero) && Bool.eqb (gt r zero) (gt y zero)
   then Generic.step_up (div x y) else div x y) = Bdiv mode_UP x y.
Proof.
intros x y r Fx Fy Hx0 Hy0 Fq Hq Hq0 Fr Hr.
apply Bdiv_rounds_up; [exact Fx | exact Fy | exact Hx0 | exact Hy0 |].
apply step_up_rounds_up_iff; [exact Fq | exact Hq | exact Hq0 |].
(* The comparisons with [zero] are the real ones. *)
unfold eq, gt.
rewrite Beqb_correct, 2!Bltb_correct by first [exact Fr | exact Fy | reflexivity].
change (B2R zero) with 0.
now apply up_iff.
Qed.

(** Where [div1_ru_fast] and [div1_ru_slow] do not take their special
    case, [x] and [y] are finite and nonzero. *)
Lemma div_not_special :
  forall x y,
  negb (Generic.is_finite x && Generic.is_finite y) || eq x zero || eq y zero = false ->
  is_finite x = true /\ is_finite y = true /\ B2R x <> 0 /\ B2R y <> 0.
Proof.
intros x y Hsp.
rewrite !is_finite_eq in Hsp.
apply Bool.orb_false_elim in Hsp as [Hsp Hy0].
apply Bool.orb_false_elim in Hsp as [Hf Hx0].
apply Bool.negb_false_iff, andb_prop in Hf as [Fx Fy].
unfold eq in Hx0, Hy0.
rewrite Beqb_correct in Hx0 by first [exact Fx | reflexivity].
rewrite Beqb_correct in Hy0 by first [exact Fy | reflexivity].
change (B2R zero) with 0 in Hx0, Hy0.
destruct (Req_bool_spec (B2R x) 0) as [|Hx]; [discriminate|].
destruct (Req_bool_spec (B2R y) 0) as [|Hy]; [discriminate|].
repeat split; assumption.
Qed.

(** ** The fast path *)

Theorem div1_ru_fast_correct :
  forall fma x y,
  snd (Generic.div1_ru_fast fma x y) = true ->
  fst (Generic.div1_ru_fast fma x y) = Bdiv mode_UP x y.
Proof.
intros fma x y.
unfold Generic.div1_ru_fast. cbv zeta.
destruct (negb (Generic.is_finite x && Generic.is_finite y) || eq x zero || eq y zero)
  eqn:Hsp.
{ destruct fma; cbv beta iota; cbn [fst snd negb orb andb];
    intros _; apply div_special; exact Hsp. }
destruct (div_not_special x y Hsp) as (Fx & Fy & Hx0 & Hy0).
destruct fma; cbv beta iota; cbn [fst snd negb orb andb];
  intros H; rewrite !Bool.andb_true_iff, !Z.leb_le in H.
- (* With an FMA, [r = RN(x - q * y)], which is [x - q * y] as that is a
     float no larger than [x]. *)
  destruct H as ((Hq1 & Hq2) & Hx1).
  destruct (div_exact x y Fx Fy Hx0 Hy0 (conj Hq1 Hq2) Hx1)
    as (Fq & Hq & Hq0 & Fr & Hr & Hxlo).
  destruct (div_fma_remainder (div x y) y x Fq Fy Fx Fr) as (Fr' & Hr').
  { assert (H52 : bpow radix2 (-52) <= 1) by (cbn [bpow radix_val radix2]; lra).
    pose proof (Rabs_pos (B2R x)).
    apply Rle_trans with (1 := Hr). nra. }
  exact (div1_ru_fast_tail x y _ Fx Fy Hx0 Hy0 Fq Hq Hq0 Fr' Hr').
- (* Without one, [r = RN(RN(x - p) - e)] with [p = RN(q * y)] and
     [e = q * y - p], which is [x - q * y] under the bounds on the
     exponents of [q], [x] and [y] that the code checks. *)
  destruct H as (((Hq1 & Hq2) & Hx1) & ((Hq3 & Hy3) & Hx3)).
  destruct (div_exact x y Fx Fy Hx0 Hy0 (conj Hq1 Hq2) Hx1)
    as (Fq & Hq & Hq0 & Fr & Hr & Hxlo).
  destruct (div_dekker_remainder x (div x y) y Fx Fq Fy Fr Hr Hxlo Hx3 Hq3 Hy3)
    as (Fr' & Hr').
  exact (div1_ru_fast_tail x y _ Fx Fy Hx0 Hy0 Fq Hq Hq0 Fr' Hr').
Qed.

(** ** The slow path *)

Theorem div1_ru_slow_correct :
  forall x y, Generic.div1_ru_slow x y = Some (Bdiv mode_UP x y).
Proof.
intros x y.
destruct (negb (Generic.is_finite x && Generic.is_finite y) || eq x zero || eq y zero)
  eqn:Hsp.
- unfold Generic.div1_ru_slow. rewrite Hsp. f_equal.
  apply div_special. exact Hsp.
- destruct (div1_ru_slow_rounds_up x y Hsp) as (r & -> & Hr).
  destruct (div_not_special x y Hsp) as (Fx & Fy & Hx0 & Hy0).
  f_equal. now apply Bdiv_rounds_up.
Qed.

(** ** Both lanes *)

Theorem div_ru_impl_correct :
  forall fma x y,
  Generic.div_ru_impl fma x y =
    Some (Bdiv mode_UP (fst x) (fst y), Bdiv mode_UP (snd x) (snd y)).
Proof.
intros fma [x0 x1] [y0 y1].
(* Each lane is the fast path if it is valid, and the slow path if not. *)
assert (L : forall a b,
  (if snd (Generic.div1_ru_fast fma a b)
   then Some (fst (Generic.div1_ru_fast fma a b))
   else Generic.div1_ru_slow a b) = Some (Bdiv mode_UP a b)).
{ intros a b.
  destruct (snd (Generic.div1_ru_fast fma a b)) eqn:Hok.
  - f_equal. now apply div1_ru_fast_correct.
  - apply div1_ru_slow_correct. }
generalize (L x0 y0) (L x1 y1).
unfold Generic.div_ru_impl, Generic.lanewise2. cbn [fst snd].
destruct (Generic.div1_ru_fast fma x0 y0) as (r0, ok0).
destruct (Generic.div1_ru_fast fma x1 y1) as (r1, ok1).
cbn [fst snd].
intros H0 H1.
destruct ok0, ok1; cbn [andb];
  rewrite ?H0, ?H1; try injection H0 as ->; try injection H1 as ->; reflexivity.
Qed.

(** [div_ru] is correct whether the target has an FMA or not. *)
Theorem div_ru_correct :
  forall has_fma x y,
  Generic.div_ru has_fma x y =
    Some (Bdiv mode_UP (fst x) (fst y), Bdiv mode_UP (snd x) (snd y)).
Proof.
intros has_fma x y. apply div_ru_impl_correct.
Qed.
