(** * e^-y and 1 - e^-y in the dyadic kernel

    [series] of [DyadicExp] in [Model.v] evaluates by Horner's scheme the
    scaled remainders [T_i(s) = (e^-s - Σ_{l < i} (-s)^l / l!) i! / (-s)^i]
    of the Taylor series of [e^-s], with [T_i(0) = 1]: they satisfy
    [T_(i-1) = 1 - s T_i / i] and [1 - e^-s = s T_1], and for
    [0 <= s <= 1], each lies in [[0, 1]] ([exp_alt_bounds] of
    [ExpSeries.v]), from which the scheme starts. [exp_neg] squares
    [e^-s] [j] times and [expm1_neg] doubles [1 - e^-s] [j] times with
    [1 - e^-2a = u (2 - u)] for [u = 1 - e^-a]. Each lemma is partial
    correctness: if the function returns, its enclosure holds the real
    number. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs DyRound DyConv DyOps DyDriver DyGrow ExpSeries.

Open Scope Z_scope.

Lemma params_bounds :
  forall n, 1 <= fst (DyadicExp.params n) <= 16 /\ 1 <= snd (DyadicExp.params n) <= 256.
Proof.
intros n. unfold DyadicExp.params.
repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn [fst snd]; lia.
Qed.

(** ** The scaled remainders of the series of [e^-s] *)

(** [exp_psum s i] is the partial sum [Σ_{l < i} (-s)^l / l!] and
    [exp_cterm s i] its next term [(-s)^i / i!]. *)
Fixpoint exp_psum (s : R) (i : nat) : R :=
  match i with
  | O => 0%R
  | S i' => (exp_psum s i' + (- s) ^ i' / INR (fact i'))%R
  end.

Definition exp_cterm (s : R) (i : nat) : R := ((- s) ^ i / INR (fact i))%R.

Lemma exp_psum_S : forall s i, exp_psum s (S i) = (exp_psum s i + exp_cterm s i)%R.
Proof. reflexivity. Qed.

(** [(-s)^(i+1) / (i+1)! = -s (-s)^i / i! / (i+1)] *)
Lemma exp_cterm_S : forall s i, exp_cterm s (S i) = (- s * exp_cterm s i / INR (S i))%R.
Proof.
intros s i. unfold exp_cterm. rewrite fact_simpl, mult_INR. cbn [pow].
pose proof (INR_fact_neq_0 i) as H1.
assert (H2 : INR (S i) <> 0%R) by (apply not_0_INR; lia).
field. split; assumption.
Qed.

(** [sum_f_R0] adds the terms up to [i] included. *)
Lemma exp_psum_sum : forall s i, sum_f_R0 (tg_alt (exp_tg s)) i = exp_psum s (S i).
Proof.
intros s i. induction i as [|i IH].
- cbn [sum_f_R0 exp_psum]. rewrite exp_tg_alt. ring.
- cbn [sum_f_R0]. rewrite IH, exp_tg_alt. reflexivity.
Qed.

(** For [0 <= s <= 1] and [i >= 1], [e^-s] lies between the partial sums
    of [i] and [i + 1] terms ([exp_alt_bounds]), so the remainder
    [e^-s - exp_psum s i] lies between 0 and the next term: above 0 for
    an even [i] and below it for an odd one. *)
Lemma exp_rem_between :
  forall s i, (0 <= s <= 1)%R -> (1 <= i)%nat ->
  (0 <= exp (- s) - exp_psum s i <= exp_cterm s i \/
   exp_cterm s i <= exp (- s) - exp_psum s i <= 0)%R.
Proof.
intros s i Hs Hi. destruct (Nat.Even_or_Odd i) as [[N HN] | [N HN]].
- destruct N as [|N]; [lia|].
  destruct (exp_alt_bounds s N Hs) as [H1 _].
  destruct (exp_alt_bounds s (S N) Hs) as [_ H2].
  rewrite exp_psum_sum in H1, H2.
  replace (S (S (2 * N))) with i in H1 by lia.
  replace (S (2 * S N)) with (S i) in H2 by lia.
  rewrite exp_psum_S in H2. left; lra.
- destruct (exp_alt_bounds s N Hs) as [H1 H2].
  rewrite exp_psum_sum in H1, H2.
  replace (S (2 * N)) with i in H2 by lia.
  replace (S (S (2 * N))) with (S i) in H1 by lia.
  rewrite exp_psum_S in H1. right; lra.
Qed.

(** So the remainder is [T_i(s)] times the next term for some [T_i(s)]
    in [[0, 1]]: the quotient if the term is not 0, and any number of
    [[0, 1]] if it is (at [s = 0], where the remainder is 0 too). *)
Lemma exp_rem_scaled :
  forall s i, (0 <= s <= 1)%R -> (1 <= i)%nat ->
  exists T, (0 <= T <= 1)%R /\ (T * exp_cterm s i = exp (- s) - exp_psum s i)%R.
Proof.
intros s i Hs Hi. pose proof (exp_rem_between s i Hs Hi) as H.
set (r := (exp (- s) - exp_psum s i)%R) in *. set (c := exp_cterm s i) in *.
clearbody r c.
destruct (Rtotal_order c 0) as [Hc | [Hc | Hc]].
- exists (r / c)%R. assert (HT : (r / c * c = r)%R) by (field; lra).
  set (T := (r / c)%R) in *. clearbody T. split; [| exact HT]. destruct H; nra.
- exists 0%R. subst c. split; [lra |]. destruct H; lra.
- exists (r / c)%R. assert (HT : (r / c * c = r)%R) by (field; lra).
  set (T := (r / c)%R) in *. clearbody T. split; [| exact HT]. destruct H; nra.
Qed.

(** ** The literals 1 and 2 *)

Lemma dexp_one_R : B2R DyadicExp.one = 1%R.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicExp.one) with (SpecFloat.S754_finite false 4503599627370496 (-52))
  by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

Lemma dexp_two_R : B2R DyadicExp.two = 2%R.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicExp.two) with (SpecFloat.S754_finite false 4503599627370496 (-51))
  by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

(** An [encl_point] of a literal holds its value. *)
Lemma point_has :
  forall n x c,
  level_ok n -> Dyadic.encl_point n x = Some c ->
  encl_ok n c /\ encl_le (2 ^ 13) c /\ encl_has c (B2R x).
Proof.
intros n x c Hn H. destruct (point_step n x c Hn H) as (Hc & HcE & Hl & Hh & _).
split; [exact Hc|]. split; [exact HcE|]. unfold encl_has, lo_R, hi_R in *. lra.
Qed.

(** ** The loop of [series]

    If [t] holds [T_i(s)], a step holds [1 - s T_i(s) / i = T_(i-1)(s)],
    as [T_i(s) (-s)^i / i! = e^-s - Σ_{l < i} (-s)^l / l!]. Each step
    adds [E + 3 2^13] at most to the bound of the exponents of [t]
    (a product, a division by [i] and a subtraction from 1). *)
Lemma series_loop_correct :
  forall n one_e s sv E,
  level_ok n -> encl_ok n one_e -> encl_le (2 ^ 13) one_e -> encl_has one_e 1 ->
  encl_ok n s -> encl_le E s -> 0 <= E <= 2 ^ 30 -> encl_has s sv ->
  forall i t Et t' T,
  (1 <= i <= 256)%nat -> encl_ok n t -> encl_le Et t ->
  0 <= Et -> Et + Z.of_nat i * (E + 2 ^ 15) <= 2 ^ 59 ->
  encl_has t T -> (T * exp_cterm sv i = exp (- sv) - exp_psum sv i)%R ->
  DyadicExp.series_loop n one_e s i t = Some t' ->
  encl_ok n t' /\ encl_le (Et + Z.of_nat i * (E + 2 ^ 15)) t' /\
  exists T', encl_has t' T' /\ (T' * exp_cterm sv 1 = exp (- sv) - exp_psum sv 1)%R.
Proof.
intros n one_e s sv E Hn Ho HoE Ho1 Hs HsE HE Hsv i.
induction i as [|i IH]; intros t Et t' T Hi Ht HtE HEt0 HEt HT HTr H; [lia|].
destruct i as [|i].
- cbn [DyadicExp.series_loop] in H. injection H as <-.
  split; [exact Ht|]. split.
  + apply (encl_le_mono Et); [lia | exact HtE].
  + exists T. split; assumption.
- cbn [DyadicExp.series_loop] in H.
  destruct (Dyadic.encl_mul n s t) as [q|] eqn:Eq; [|discriminate H].
  destruct (Dyadic.encl_div_u64 n q (Z.of_nat (S (S i)))) as [q'|] eqn:Eq'; [|discriminate H].
  destruct (Dyadic.encl_sub n one_e q') as [t1|] eqn:Et1; [|discriminate H].
  assert (HEt' : Et <= 2 ^ 59) by nia.
  assert (HE1 : 0 <= E <= 2 ^ 60) by lia.
  assert (HE2 : 0 <= Et <= 2 ^ 60) by lia.
  destruct (mul_step n s t q E Et Hn Hs Ht HsE HtE HE1 HE2 Eq) as (Hq & HqE & Hqv).
  assert (HE3 : 0 <= E + Et + 2 ^ 13 <= 2 ^ 60) by lia.
  assert (Hk : 0 < Z.of_nat (S (S i)) < 2 ^ 64) by lia.
  destruct (div_u64_step n q (Z.of_nat (S (S i))) q' (E + Et + 2 ^ 13) Hn Hq HqE HE3 Hk Eq')
    as (Hq' & Hq'E & Hq'v).
  assert (HE4 : 0 <= 2 ^ 13 <= 2 ^ 60) by lia.
  assert (HE5 : 0 <= E + Et + 2 ^ 13 + 2 ^ 13 <= 2 ^ 60) by lia.
  destruct (sub_step n one_e q' t1 (2 ^ 13) (E + Et + 2 ^ 13 + 2 ^ 13) Hn Ho Hq' HoE Hq'E
    HE4 HE5 Et1) as (Ht1 & Ht1E & Ht1v).
  assert (Hm : INR (S (S i)) <> 0%R) by (apply not_0_INR; lia).
  set (T1 := (1 - sv * T / INR (S (S i)))%R).
  assert (HT1 : encl_has t1 T1).
  { unfold T1. rewrite INR_IZR_INZ. apply Ht1v; [exact Ho1 |]. apply Hq'v, Hqv; assumption. }
  assert (HT1r : (T1 * exp_cterm sv (S i) = exp (- sv) - exp_psum sv (S i))%R).
  { rewrite (exp_psum_S sv (S i)), (exp_cterm_S sv (S i)) in HTr. unfold T1.
    set (c := exp_cterm sv (S i)) in *. set (m := INR (S (S i))) in *.
    replace ((1 - sv * T / m) * c)%R with (c + T * (- sv * c / m))%R by (field; exact Hm).
    rewrite HTr. ring. }
  assert (Ht1E' : encl_le (Et + (E + 2 ^ 15)) t1).
  { apply (encl_le_mono (Z.max (2 ^ 13) (E + Et + 2 ^ 13 + 2 ^ 13) + 2 ^ 13)); [lia | exact Ht1E]. }
  assert (Hi' : (1 <= S i <= 256)%nat) by lia.
  assert (HEt1 : 0 <= Et + (E + 2 ^ 15)) by lia.
  assert (HEt2 : Et + (E + 2 ^ 15) + Z.of_nat (S i) * (E + 2 ^ 15) <= 2 ^ 59).
  { rewrite Nat2Z.inj_succ in *. nia. }
  destruct (IH t1 (Et + (E + 2 ^ 15)) t' T1 Hi' Ht1 Ht1E' HEt1 HEt2 HT1 HT1r H)
    as (A & B & C).
  split; [exact A|]. split; [| exact C].
  apply (encl_le_mono (Et + (E + 2 ^ 15) + Z.of_nat (S i) * (E + 2 ^ 15))); [| exact B].
  rewrite !Nat2Z.inj_succ. nia.
Qed.

Lemma series_correct :
  forall n s k t E sv,
  level_ok n -> encl_ok n s -> encl_le E s -> 0 <= E <= 2 ^ 30 -> 1 <= k <= 256 ->
  encl_has s sv -> (0 <= sv <= 1)%R ->
  DyadicExp.series n s k = Some t ->
  encl_ok n t /\ encl_le (2 ^ 9 * (E + 2 ^ 15)) t /\ encl_has t (1 - exp (- sv)).
Proof.
intros n s k t E sv Hn Hs HsE HE Hk Hsv Hsv01 H.
unfold DyadicExp.series in H.
destruct (Dyadic.encl_point n DyadicExp.one) as [one_e|] eqn:E1; [|discriminate H].
destruct (Dyadic.from_f64 n DyadicExp.one) as [hi|] eqn:E2; [|discriminate H].
set (t0 := {| Dyadic.en_lo := Dyadic.dy_zero n; Dyadic.en_hi := hi |}) in H.
destruct (DyadicExp.series_loop n one_e s (Z.to_nat k) t0) as [t1|] eqn:E3; [|discriminate H].
destruct (point_has n _ _ Hn E1) as (Ho & HoE & Ho1). rewrite dexp_one_R in Ho1.
destruct (from_f64_step n _ _ Hn E2) as (Hh & HhE & HhR & _). rewrite dexp_one_R in HhR.
destruct (dy_zero_ok n) as (Hz & HzR & _).
(* The scheme starts from [[0, 1]], which holds [T_K(s)]. *)
assert (Ht0 : encl_ok n t0).
{ unfold encl_ok, t0; cbn [Dyadic.en_lo Dyadic.en_hi].
  split; [exact Hz|]. split; [exact Hh|]. rewrite HzR, HhR. lra. }
assert (Ht0E : encl_le (2 ^ 13) t0).
{ unfold encl_le, t0; cbn [Dyadic.en_lo Dyadic.en_hi Dyadic.dy_zero Dyadic.dy_exp]. lia. }
assert (HK : (1 <= Z.to_nat k <= 256)%nat) by lia.
destruct (exp_rem_scaled sv (Z.to_nat k) Hsv01 ltac:(lia)) as (T & HT01 & HT).
assert (HT0 : encl_has t0 T).
{ unfold encl_has, t0; cbn [Dyadic.en_lo Dyadic.en_hi]. rewrite HzR, HhR. lra. }
assert (HE0 : 0 <= (2 ^ 13 : Z)) by lia.
assert (HEb : 2 ^ 13 + Z.of_nat (Z.to_nat k) * (E + 2 ^ 15) <= 2 ^ 59).
{ rewrite Z2Nat.id by lia. nia. }
destruct (series_loop_correct n one_e s sv E Hn Ho HoE Ho1 Hs HsE HE Hsv (Z.to_nat k) t0
  (2 ^ 13) t1 T HK Ht0 Ht0E HE0 HEb HT0 HT E3) as (Ht1 & Ht1E & T1 & HT1 & HT1r).
rewrite Z2Nat.id in Ht1E by lia.
assert (HE1 : 0 <= E <= 2 ^ 60) by lia.
assert (HE2 : 0 <= 2 ^ 13 + k * (E + 2 ^ 15) <= 2 ^ 60) by nia.
destruct (mul_step n s t1 t E _ Hn Hs Ht1 HsE Ht1E HE1 HE2 H) as (Ht & HtE & Htv).
split; [exact Ht|]. split.
- apply (encl_le_mono (E + (2 ^ 13 + k * (E + 2 ^ 15)) + 2 ^ 13)); [nia | exact HtE].
- (* [T_1(s) (-s) = e^-s - 1]. *)
  assert (Hc : exp_cterm sv 1 = (- sv)%R) by (unfold exp_cterm; simpl; field).
  assert (Hp : exp_psum sv 1 = 1%R) by (simpl; field).
  rewrite Hc, Hp in HT1r.
  replace (1 - exp (- sv))%R with (sv * T1)%R by lra.
  apply Htv; assumption.
Qed.

(** ** Squaring and doubling *)

(** Each squaring doubles the bound of the exponents and adds [2^13]. *)
Lemma square_loop_correct :
  forall n j e Ee w e',
  level_ok n -> encl_ok n e -> encl_le Ee e -> 0 <= Ee ->
  2 ^ Z.of_nat j * (Ee + 2 ^ 13) <= 2 ^ 60 ->
  encl_has e (exp (- w)) ->
  DyadicExp.square_loop n j e = Some e' ->
  encl_ok n e' /\ encl_le (2 ^ Z.of_nat j * (Ee + 2 ^ 13)) e' /\
  encl_has e' (exp (- (w * bpow radix2 (Z.of_nat j)))).
Proof.
intros n j. induction j as [|j IH]; intros e Ee w e' Hn He HeE HE0 HEb Hw H.
- cbn [DyadicExp.square_loop] in H. injection H as <-.
  split; [exact He|]. split.
  + apply (encl_le_mono Ee); [cbn [Z.of_nat Z.pow]; lia | exact HeE].
  + cbn [Z.of_nat bpow]. rewrite Rmult_1_r. exact Hw.
- cbn [DyadicExp.square_loop] in H.
  destruct (Dyadic.encl_mul n e e) as [e1|] eqn:E1; [|discriminate H].
  assert (Hp : 0 < 2 ^ Z.of_nat j) by (apply Z.pow_pos_nonneg; lia).
  rewrite Nat2Z.inj_succ, Z.pow_succ_r in HEb by lia.
  assert (HE1 : 0 <= Ee <= 2 ^ 60) by nia.
  destruct (mul_step n e e e1 Ee Ee Hn He He HeE HeE HE1 HE1 E1) as (H1 & H1E & H1v).
  assert (Hw1 : encl_has e1 (exp (- (w + w)))).
  { replace (exp (- (w + w))) with (exp (- w) * exp (- w))%R
      by (rewrite <- exp_plus; f_equal; ring).
    apply H1v; exact Hw. }
  assert (HE2 : 0 <= Ee + Ee + 2 ^ 13) by lia.
  assert (HE3 : 2 ^ Z.of_nat j * (Ee + Ee + 2 ^ 13 + 2 ^ 13) <= 2 ^ 60) by nia.
  destruct (IH e1 (Ee + Ee + 2 ^ 13) (w + w)%R e' Hn H1 H1E HE2 HE3 Hw1 H) as (A & B & C).
  split; [exact A|]. split.
  + rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    apply (encl_le_mono (2 ^ Z.of_nat j * (Ee + Ee + 2 ^ 13 + 2 ^ 13))); [nia | exact B].
  + rewrite Nat2Z.inj_succ, <- Z.add_1_r, bpow_plus.
    change (bpow radix2 1) with 2%R.
    replace (w * (bpow radix2 (Z.of_nat j) * 2))%R
      with ((w + w) * bpow radix2 (Z.of_nat j))%R by ring.
    exact C.
Qed.

(** The bound of the exponents of the result is linear in the bound [E]
    of those of [y]: [series] gives [2^9 (E + j + 2^15)] and each of the
    [j <= 16] squarings doubles the bound and adds [2^13]. *)
Lemma exp_neg_correct :
  forall n y e E yv,
  level_ok n -> encl_ok n y -> encl_le E y -> 0 <= E <= 2 ^ 29 + 2 ^ 20 ->
  encl_has y yv -> (0 <= yv <= 2)%R ->
  DyadicExp.exp_neg n y = Some e ->
  encl_ok n e /\ encl_le (2 ^ 25 * (E + 2 ^ 16)) e /\ encl_has e (exp (- yv)).
Proof.
intros n y e E yv Hn Hy HyE HE Hyv Hyv02 H.
unfold DyadicExp.exp_neg in H.
pose proof (params_bounds n) as Hp.
destruct (DyadicExp.params n) as [j k]. cbn [fst snd] in Hp.
destruct (Dyadic.encl_point n DyadicExp.one) as [one_e|] eqn:E1; [|discriminate H].
destruct (Dyadic.encl_shl n y (- j)) as [s|] eqn:E2; [|discriminate H].
destruct (DyadicExp.series n s k) as [u|] eqn:E3; [|discriminate H].
destruct (Dyadic.encl_sub n one_e u) as [e0|] eqn:E4; [|discriminate H].
destruct (point_has n _ _ Hn E1) as (Ho & HoE & Ho1). rewrite dexp_one_R in Ho1.
assert (HE1 : 0 <= E <= 2 ^ 60) by lia.
assert (Hj : - 2 ^ 20 <= - j <= 2 ^ 20) by lia.
destruct (shl_step n y (- j) s E Hn Hy HyE HE1 Hj E2) as (Hs & HsE & Hsv).
(* [s] holds [y 2^-j], in [[0, 1]] as [y <= 2] and [j >= 1]. *)
set (sv := (yv * bpow radix2 (- j))%R).
assert (Hsv01 : (0 <= sv <= 1)%R).
{ assert (Hb : (bpow radix2 (- j) <= bpow radix2 (-1))%R) by (apply bpow_le; lia).
  change (bpow radix2 (-1)) with (/ 2)%R in Hb.
  pose proof (bpow_gt_0 radix2 (- j)). unfold sv. nra. }
assert (HE2 : 0 <= E + Z.abs (- j) <= 2 ^ 30) by lia.
assert (Hk : 1 <= k <= 256) by lia.
destruct (series_correct n s k u (E + Z.abs (- j)) sv Hn Hs HsE HE2 Hk (Hsv yv Hyv) Hsv01 E3)
  as (Hu & HuE & Huv).
assert (HE3 : 0 <= 2 ^ 13 <= 2 ^ 60) by lia.
assert (HE4 : 0 <= 2 ^ 9 * (E + Z.abs (- j) + 2 ^ 15) <= 2 ^ 60) by lia.
destruct (sub_step n one_e u e0 _ _ Hn Ho Hu HoE HuE HE3 HE4 E4) as (He0 & He0E & He0v).
assert (Hev : encl_has e0 (exp (- sv))).
{ replace (exp (- sv)) with (1 - (1 - exp (- sv)))%R by ring. apply He0v; assumption. }
(* After [j <= 16] squarings, the bound is below [2^16 2^39]. *)
assert (Hpj : 1 <= 2 ^ j <= 2 ^ 16).
{ split; [cut (0 < 2 ^ j); [lia | apply Z.pow_pos_nonneg; lia] | apply Z.pow_le_mono_r; lia]. }
set (Ee := Z.max (2 ^ 13) (2 ^ 9 * (E + Z.abs (- j) + 2 ^ 15)) + 2 ^ 13) in He0E.
assert (HEe : 0 <= Ee /\ Ee <= 2 ^ 9 * (E + 2 ^ 4 + 2 ^ 15) + 2 ^ 13 /\ Ee + 2 ^ 13 <= 2 ^ 39)
  by (unfold Ee; lia).
assert (HEb : 2 ^ Z.of_nat (Z.to_nat j) * (Ee + 2 ^ 13) <= 2 ^ 60).
{ rewrite Z2Nat.id by lia. nia. }
destruct (square_loop_correct n (Z.to_nat j) e0 Ee sv e Hn He0 He0E (proj1 HEe) HEb Hev H)
  as (A & B & C).
rewrite Z2Nat.id in B, C by lia.
split; [exact A|]. split.
- assert (Hb : 2 ^ j * (Ee + 2 ^ 13) <= 2 ^ 16 * (2 ^ 9 * (E + 2 ^ 4 + 2 ^ 15) + 2 ^ 14)) by nia.
  apply (encl_le_mono (2 ^ j * (Ee + 2 ^ 13))); [lia | exact B].
- (* [y 2^-j 2^j = y] *)
  replace yv with (sv * bpow radix2 j)%R; [exact C |].
  unfold sv. rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l. cbn [bpow]. ring.
Qed.

(** Each doubling [u (2 - u)] doubles the bound of the exponents and adds
    [2^14]. *)
Lemma double_loop_correct :
  forall n two_e j u Eu w u',
  level_ok n -> encl_ok n two_e -> encl_le (2 ^ 13) two_e -> encl_has two_e 2 ->
  encl_ok n u -> encl_le Eu u -> 2 ^ 13 <= Eu ->
  2 ^ Z.of_nat j * (Eu + 2 ^ 14) <= 2 ^ 60 ->
  encl_has u (1 - exp (- w)) ->
  DyadicExp.double_loop n two_e j u = Some u' ->
  encl_ok n u' /\ encl_le (2 ^ Z.of_nat j * (Eu + 2 ^ 14)) u' /\
  encl_has u' (1 - exp (- (w * bpow radix2 (Z.of_nat j)))).
Proof.
intros n two_e j. induction j as [|j IH];
  intros u Eu w u' Hn Ht HtE Ht2 Hu HuE HE0 HEb Hw H.
- cbn [DyadicExp.double_loop] in H. injection H as <-.
  split; [exact Hu|]. split.
  + apply (encl_le_mono Eu); [cbn [Z.of_nat Z.pow]; lia | exact HuE].
  + cbn [Z.of_nat bpow]. rewrite Rmult_1_r. exact Hw.
- cbn [DyadicExp.double_loop] in H.
  destruct (Dyadic.encl_sub n two_e u) as [d|] eqn:E1; [|discriminate H].
  destruct (Dyadic.encl_mul n u d) as [u1|] eqn:E2; [|discriminate H].
  assert (Hp : 0 < 2 ^ Z.of_nat j) by (apply Z.pow_pos_nonneg; lia).
  rewrite Nat2Z.inj_succ, Z.pow_succ_r in HEb by lia.
  assert (HE1 : 0 <= 2 ^ 13 <= 2 ^ 60) by lia.
  assert (HE2 : 0 <= Eu <= 2 ^ 60) by nia.
  destruct (sub_step n two_e u d _ _ Hn Ht Hu HtE HuE HE1 HE2 E1) as (Hd & HdE & Hdv).
  assert (HE3 : 0 <= Z.max (2 ^ 13) Eu + 2 ^ 13 <= 2 ^ 60) by nia.
  destruct (mul_step n u d u1 _ _ Hn Hu Hd HuE HdE HE2 HE3 E2) as (H1 & H1E & H1v).
  (* [(1 - e^-w) (2 - (1 - e^-w)) = 1 - e^-2w] *)
  assert (Hw1 : encl_has u1 (1 - exp (- (w + w)))).
  { replace (1 - exp (- (w + w)))%R with ((1 - exp (- w)) * (2 - (1 - exp (- w))))%R.
    - apply H1v; [exact Hw | apply Hdv; assumption].
    - replace (- (w + w))%R with (- w + - w)%R by ring. rewrite exp_plus. ring. }
  assert (H1E' : encl_le (Eu + Eu + 2 ^ 14) u1).
  { apply (encl_le_mono (Eu + (Z.max (2 ^ 13) Eu + 2 ^ 13) + 2 ^ 13)); [lia | exact H1E]. }
  assert (HE4 : 2 ^ 13 <= Eu + Eu + 2 ^ 14) by lia.
  assert (HE5 : 2 ^ Z.of_nat j * (Eu + Eu + 2 ^ 14 + 2 ^ 14) <= 2 ^ 60) by nia.
  destruct (IH u1 (Eu + Eu + 2 ^ 14) (w + w)%R u' Hn Ht HtE Ht2 H1 H1E' HE4 HE5 Hw1 H)
    as (A & B & C).
  split; [exact A|]. split.
  + rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    apply (encl_le_mono (2 ^ Z.of_nat j * (Eu + Eu + 2 ^ 14 + 2 ^ 14))); [nia | exact B].
  + rewrite Nat2Z.inj_succ, <- Z.add_1_r, bpow_plus.
    change (bpow radix2 1) with 2%R.
    replace (w * (bpow radix2 (Z.of_nat j) * 2))%R
      with ((w + w) * bpow radix2 (Z.of_nat j))%R by ring.
    exact C.
Qed.

Lemma expm1_neg_correct :
  forall n y u E yv,
  level_ok n -> encl_ok n y -> encl_le E y -> 0 <= E <= 2 ^ 21 ->
  encl_has y yv -> (0 <= yv <= 2)%R ->
  DyadicExp.expm1_neg n y = Some u ->
  encl_ok n u /\ encl_le (2 ^ 47) u /\ encl_has u (1 - exp (- yv)).
Proof.
intros n y u E yv Hn Hy HyE HE Hyv Hyv02 H.
unfold DyadicExp.expm1_neg in H.
pose proof (params_bounds n) as Hp.
destruct (DyadicExp.params n) as [j k]. cbn [fst snd] in Hp.
destruct (Dyadic.encl_point n DyadicExp.two) as [two_e|] eqn:E1; [|discriminate H].
destruct (Dyadic.encl_shl n y (- j)) as [s|] eqn:E2; [|discriminate H].
destruct (DyadicExp.series n s k) as [u0|] eqn:E3; [|discriminate H].
destruct (point_has n _ _ Hn E1) as (Ht & HtE & Ht2). rewrite dexp_two_R in Ht2.
assert (HE1 : 0 <= E <= 2 ^ 60) by lia.
assert (Hj : - 2 ^ 20 <= - j <= 2 ^ 20) by lia.
destruct (shl_step n y (- j) s E Hn Hy HyE HE1 Hj E2) as (Hs & HsE & Hsv).
(* [s] holds [y 2^-j], in [[0, 1]] as [y <= 2] and [j >= 1]. *)
set (sv := (yv * bpow radix2 (- j))%R).
assert (Hsv01 : (0 <= sv <= 1)%R).
{ assert (Hb : (bpow radix2 (- j) <= bpow radix2 (-1))%R) by (apply bpow_le; lia).
  change (bpow radix2 (-1)) with (/ 2)%R in Hb.
  pose proof (bpow_gt_0 radix2 (- j)). unfold sv. nra. }
assert (HE2 : 0 <= E + Z.abs (- j) <= 2 ^ 30) by lia.
assert (Hk : 1 <= k <= 256) by lia.
destruct (series_correct n s k u0 (E + Z.abs (- j)) sv Hn Hs HsE HE2 Hk (Hsv yv Hyv) Hsv01 E3)
  as (Hu & HuE & Huv).
(* After [j <= 16] doublings, the bound is below [2^16 2^31]. *)
assert (Hpj : 1 <= 2 ^ j <= 2 ^ 16).
{ split; [cut (0 < 2 ^ j); [lia | apply Z.pow_pos_nonneg; lia] | apply Z.pow_le_mono_r; lia]. }
set (Eu := 2 ^ 9 * (E + Z.abs (- j) + 2 ^ 15)) in HuE.
assert (HEu : 2 ^ 13 <= Eu /\ Eu + 2 ^ 14 <= 2 ^ 31) by (unfold Eu; lia).
assert (HEb : 2 ^ Z.of_nat (Z.to_nat j) * (Eu + 2 ^ 14) <= 2 ^ 60).
{ rewrite Z2Nat.id by lia. nia. }
destruct (double_loop_correct n two_e (Z.to_nat j) u0 Eu sv u Hn Ht HtE Ht2 Hu HuE
  (proj1 HEu) HEb Huv H) as (A & B & C).
rewrite Z2Nat.id in B, C by lia.
split; [exact A|]. split.
- apply (encl_le_mono (2 ^ j * (Eu + 2 ^ 14))); [nia | exact B].
- (* [y 2^-j 2^j = y] *)
  replace yv with (sv * bpow radix2 j)%R; [exact C |].
  unfold sv. rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l. cbn [bpow]. ring.
Qed.

