(** * The last product of [acosh] near 1, for its fast path

    [DyadicLog.fast_acosh_near1] of [Model.v] computes [acosh x] for
    [1 < x < 1 + 2^-8] as [2 s (1 - u/6 + 3 u^2/40 - ...)], with
    [u = (x - 1)/2] and [s = sh + sl] a double-double of [√u]. Its last
    steps multiply [sh + sl] by [1 - mh + wl], where [mh] and [wl] are the
    correction of [FastAhypNear1Poly.v] ([mh <= 2^-11], [|wl| <= 2^-21]):
    [ph = RN(sh mh)] with its exact error [pe], [sh - ph] as a
    double-double [(a, b)] by Fast2Sum [Dekker], the small terms
    [sl + sh wl - (pe + sl mh)] added to [b] in [f64] as
    [t1 = RN(sh wl)], [t2 = RN(sl + t1)], [t3 = RN(sl mh)],
    [t4 = RN(pe + t3)], [t5 = RN(t2 - t4)] and [t6 = RN(b + t5)], and a
    second Fast2Sum of [a] and [t6].
    - [near1_sum]: [h + l] is within [2^-70 sh] of
      [(sh + sl) (1 - mh + wl)], with [h] the rounding of [h + l] to
      nearest and [sh (1 - 2^-10) <= h <= 2 sh]. The roundings of
      [sh wl], [sl + t1], [t2 - t4] and [b + t5] each move the sum by
      about [2^-74 sh], those of [sl mh] and [pe + t3] by less than
      [2^-110 sh], and the omitted [sl wl] by at most [2^-73 sh] with the
      bound [|sl| <= 2^-52 sh] used here: about [6 2^-74 sh] in all.
    - [near1_pe_fma]: [pe] is the same [f64] with an FMA and with Dekker's
      product, as the error of [sh mh] is exact in both.

    [Dekker] T. J. Dekker, A floating-point technique for extending the
    available precision, Numer. Math. 18 (1971). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding TwoSum TwoProduct FastExpErr.
From Inari Require FastRound FastLogNorm.

Open Scope R_scope.

(** ** Helpers *)

(** Powers of 2 as numerals, for [lra], in the goal and every hypothesis. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp] in *.

(** [rn_err] with a bound [K] of [|x|]. *)
Local Lemma rn_k :
  forall x K, Rabs x <= K -> Rabs (RN x - x) <= bpow radix2 (-53) * K + bpow radix2 (-1075).
Proof.
intros x K H. eapply Rle_trans; [apply rn_err |].
apply Rplus_le_compat_r, Rmult_le_compat_l; [apply bpow_ge_0 | exact H].
Qed.

(** The exponent of a finite [f64] below [2^k] is below [k], and that of
    one at least [2^k] at least [k] (as in [FastDdSqrt.v]). *)
Local Lemma exponent_lt :
  forall x k, is_finite x = true -> (-1022 <= k)%Z ->
  Rabs (B2R x) < bpow radix2 k -> (Generic.exponent x < k)%Z.
Proof.
intros x k Fx Hk H.
destruct (Z_lt_le_dec (Generic.exponent x) (-1022)) as [L|L]; [lia|].
pose proof (bpow_exponent_le_abs_B2R x Fx L) as H0.
assert (H1 : bpow radix2 (Generic.exponent x) < bpow radix2 k) by lra.
apply lt_bpow in H1. exact H1.
Qed.

Local Lemma exponent_ge :
  forall x k, is_finite x = true -> bpow radix2 k <= Rabs (B2R x) ->
  (k <= Generic.exponent x)%Z.
Proof.
intros x k Fx H.
pose proof (abs_B2R_lt_exponent x Fx) as H0.
assert (H1 : bpow radix2 k < bpow radix2 (Generic.exponent x + 1)) by lra.
apply lt_bpow in H1. lia.
Qed.

(** Both variants of [two_prod_is_exact] hold for operands and a product
    of moderate exponents (as in [FastDdSqrt.v]). *)
Local Lemma two_prod_is_exact_of :
  forall fma x y,
  (-968 <= Generic.exponent (mul x y) <= 1022)%Z ->
  (Generic.exponent x <= 995)%Z -> (Generic.exponent y <= 995)%Z ->
  Generic.two_prod_is_exact fma x y (mul x y) = true.
Proof.
intros fma x y Ep Ex Ey.
destruct fma; cbv beta iota zeta delta [Generic.two_prod_is_exact];
  repeat (apply andb_true_intro; split); apply Z.leb_le; lia.
Qed.

(** [sh mh] is at least [2^-84] and below 1, so its error is exact with
    either variant of [two_prod_err]. *)
Local Lemma pe_exact :
  forall fma sh mh, is_finite sh = true -> is_finite mh = true ->
  bpow radix2 (-27) <= B2R sh <= bpow radix2 (-4) ->
  bpow radix2 (-57) <= B2R mh <= bpow radix2 (-11) ->
  Generic.two_prod_is_exact fma sh mh (mul sh mh) = true.
Proof.
intros fma sh mh Fsh Fmh Hs Hm.
pose proof (bpow_gt_0 radix2 (-27)) as P27.
pose proof (bpow_gt_0 radix2 (-57)) as P57.
pose proof (bpow_gt_0 radix2 (-84)) as P84.
assert (HP : bpow radix2 (-84) <= B2R sh * B2R mh <= bpow radix2 (-15)).
{ split.
  - replace (-84)%Z with (-27 + -57)%Z by lia. rewrite bpow_plus.
    apply Rmult_le_compat; lra.
  - replace (-15)%Z with (-4 + -11)%Z by lia. rewrite bpow_plus.
    apply Rmult_le_compat; lra. }
assert (HP16 : Rabs (B2R sh * B2R mh) <= 16).
{ rewrite Rabs_pos_eq by lra. clear -HP. num. lra. }
destruct (mul_e sh mh Fsh Fmh HP16) as (Fp & _ & Bp).
rewrite (Rabs_pos_eq (B2R sh * B2R mh)) in Bp by lra.
apply Rabs_le_inv in Bp.
assert (Hp : bpow radix2 (-85) <= B2R (mul sh mh) < 1).
{ clear -Bp HP. num. lra. }
apply two_prod_is_exact_of.
- split.
  + apply Z.le_trans with (-85)%Z; [lia |]. apply exponent_ge; [exact Fp |].
    rewrite Rabs_pos_eq; [lra |]. pose proof (bpow_gt_0 radix2 (-85)). lra.
  + apply Z.lt_le_incl, Z.lt_le_trans with 0%Z; [| lia].
    apply exponent_lt; [exact Fp | lia |]. apply Rabs_lt.
    pose proof (bpow_gt_0 radix2 (-85)). change (bpow radix2 0) with 1. lra.
- apply Z.lt_le_incl, Z.lt_le_trans with 0%Z; [| lia].
  apply exponent_lt; [exact Fsh | lia |]. apply Rabs_lt.
  clear -Hs P27. num. lra.
- apply Z.lt_le_incl, Z.lt_le_trans with 0%Z; [| lia].
  apply exponent_lt; [exact Fmh | lia |]. apply Rabs_lt.
  clear -Hm P57. num. lra.
Qed.

(** ** The theorems *)

Lemma near1_sum : forall fma sh sl mh wl a b h l,
  is_finite sh = true -> is_finite sl = true -> is_finite mh = true -> is_finite wl = true ->
  B2R sh = RN (B2R sh + B2R sl) -> bpow radix2 (-27) <= B2R sh <= bpow radix2 (-4) ->
  bpow radix2 (-57) <= B2R mh <= bpow radix2 (-11) -> Rabs (B2R wl) <= bpow radix2 (-21) ->
  Fast.fast_two_sum sh (opp (mul sh mh)) = (a, b) ->
  Fast.fast_two_sum a (add b (sub (add sl (mul sh wl))
    (add (Generic.two_prod_err fma sh mh (mul sh mh)) (mul sl mh)))) = (h, l) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  B2R sh * (1 - bpow radix2 (-10)) <= B2R h <= 2 * B2R sh /\
  Rabs (B2R h + B2R l - (B2R sh + B2R sl) * (1 - B2R mh + B2R wl)) <= bpow radix2 (-70) * B2R sh.
Proof.
intros fma sh sl mh wl a b h l Fsh Fsl Fmh Fwl Esh Hs Hm Hw E1 E2.
pose proof (bpow_gt_0 radix2 (-27)) as P27.
pose proof (bpow_gt_0 radix2 (-57)) as P57.
pose proof (bpow_gt_0 radix2 (-84)) as P84.
(* [|sl| <= 2^-53 (sh + |sl|) + 2^-1075], as [sh] is [sh + sl] rounded. *)
assert (HL : Rabs (B2R sl) <= bpow radix2 (-52) * B2R sh).
{ pose proof (rn_err (B2R sh + B2R sl)) as H. rewrite <- Esh in H.
  replace (B2R sh - (B2R sh + B2R sl)) with (- B2R sl) in H by ring.
  rewrite Rabs_Ropp in H.
  pose proof (Rabs_triang (B2R sh) (B2R sl)) as T.
  rewrite (Rabs_pos_eq (B2R sh)) in T by lra.
  assert (H' : Rabs (B2R sl) <=
    bpow radix2 (-53) * (B2R sh + Rabs (B2R sl)) + bpow radix2 (-1075)).
  { eapply Rle_trans; [exact H |].
    apply Rplus_le_compat_r, Rmult_le_compat_l; [apply bpow_ge_0 | exact T]. }
  clear -H' Hs. num. lra. }
(* The exact products, which [lra] takes as atoms. *)
assert (HSM : bpow radix2 (-84) <= B2R sh * B2R mh <= bpow radix2 (-11) * B2R sh).
{ split.
  - replace (-84)%Z with (-27 + -57)%Z by lia. rewrite bpow_plus.
    apply Rmult_le_compat; lra.
  - rewrite (Rmult_comm (bpow _ _)). apply Rmult_le_compat_l; lra. }
assert (HSW : Rabs (B2R sh * B2R wl) <= bpow radix2 (-21) * B2R sh).
{ rewrite Rabs_mult, (Rabs_pos_eq (B2R sh)) by lra.
  rewrite (Rmult_comm (bpow _ _)). apply Rmult_le_compat_l; lra. }
assert (HLM : Rabs (B2R sl * B2R mh) <= bpow radix2 (-52) * B2R sh * bpow radix2 (-11)).
{ apply Rabs_mul_le; [exact HL |]. rewrite Rabs_pos_eq; lra. }
assert (HLW : Rabs (B2R sl * B2R wl) <= bpow radix2 (-52) * B2R sh * bpow radix2 (-21)).
{ apply Rabs_mul_le; [exact HL | exact Hw]. }
(* [ph = RN(sh mh)] and its exact error [pe = sh mh - ph]. *)
assert (HSM16 : Rabs (B2R sh * B2R mh) <= 16).
{ rewrite Rabs_pos_eq by lra. clear -HSM Hs. num. lra. }
destruct (mul_e sh mh Fsh Fmh HSM16) as (Fph & _ & Bph).
rewrite (Rabs_pos_eq (B2R sh * B2R mh)) in Bph by lra.
apply Rabs_le_inv in Bph.
destruct (two_prod_err_correct fma sh mh Fsh Fmh (pe_exact fma sh mh Fsh Fmh Hs Hm))
  as (_ & _ & _ & Fpe & Epe).
set (pe := Generic.two_prod_err fma sh mh (mul sh mh)) in *.
set (ph := mul sh mh) in *.
(* [(a, b)] is [sh - ph] exactly, by Fast2Sum, as [0 < ph < sh]. *)
assert (Fo : is_finite (opp ph) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fph).
assert (Eo : B2R (opp ph) = - B2R ph) by (unfold opp; apply B2R_Bopp).
assert (Hph : 0 <= B2R ph <= bpow radix2 (-10) * B2R sh).
{ clear -Bph HSM Hs. num. lra. }
assert (Hab : Rabs (B2R (opp ph)) <= Rabs (B2R sh) \/ B2R sh = 0).
{ left. rewrite Eo, Rabs_Ropp, (Rabs_pos_eq (B2R sh)), (Rabs_pos_eq (B2R ph)) by lra.
  clear -Hph Hs. num. lra. }
assert (Hab2 : Rabs (B2R sh + B2R (opp ph)) <= 2048).
{ rewrite Eo. apply Rabs_le. clear -Hph Hs. num. lra. }
destruct (FastLogNorm.fts_exact sh (opp ph) a b Fsh Fo Hab Hab2 E1) as (Fa & Fb & Ea & Eab).
rewrite Eo in Ea, Eab.
assert (Ba : Rabs (B2R a - (B2R sh + - B2R ph)) <=
  bpow radix2 (-53) * B2R sh + bpow radix2 (-1075)).
{ rewrite Ea. apply rn_k. apply Rabs_le. clear -Hph Hs. num. lra. }
assert (Bb : Rabs (B2R b) <= bpow radix2 (-53) * B2R sh + bpow radix2 (-1075)).
{ replace (B2R b) with (- (B2R a - (B2R sh + - B2R ph))) by lra.
  rewrite Rabs_Ropp. exact Ba. }
(* The small terms, each rounded: [t1 = RN(sh wl)], [t2 = RN(sl + t1)],
   [t3 = RN(sl mh)], [t4 = RN(pe + t3)], [t5 = RN(t2 - t4)] and
   [t6 = RN(b + t5)]. *)
assert (K1 : bpow radix2 (-21) * B2R sh <= 16) by (clear -Hs; num; lra).
destruct (mul_k sh wl _ Fsh Fwl HSW K1) as (F1 & _ & B1).
set (t1 := mul sh wl) in *.
apply Rabs_le_inv in HL, HSW, HLM, HLW, B1.
assert (M2 : Rabs (B2R sl + B2R t1) <= (bpow radix2 (-21) + bpow radix2 (-40)) * B2R sh).
{ apply Rabs_le. clear -HL HSW B1 Hs. num. lra. }
assert (K2 : (bpow radix2 (-21) + bpow radix2 (-40)) * B2R sh <= 16) by (clear -Hs; num; lra).
destruct (add_k sl t1 _ Fsl F1 M2 K2) as (F2 & _ & B2).
set (t2 := add sl t1) in *.
apply Rabs_le_inv in B2.
assert (M3 : Rabs (B2R sl * B2R mh) <= bpow radix2 (-63) * B2R sh).
{ apply Rabs_le. clear -HLM Hs. num. lra. }
assert (K3 : bpow radix2 (-63) * B2R sh <= 16) by (clear -Hs; num; lra).
destruct (mul_k sl mh _ Fsl Fmh M3 K3) as (F3 & _ & B3).
set (t3 := mul sl mh) in *.
apply Rabs_le_inv in B3.
assert (M4 : Rabs (B2R pe + B2R t3) <= bpow radix2 (-62) * B2R sh).
{ apply Rabs_le. rewrite Epe. clear -Bph HSM HLM B3 Hs. num. lra. }
assert (K4 : bpow radix2 (-62) * B2R sh <= 16) by (clear -Hs; num; lra).
destruct (add_k pe t3 _ Fpe F3 M4 K4) as (F4 & _ & B4).
set (t4 := add pe t3) in *.
apply Rabs_le_inv in B4. rewrite Epe in B4.
assert (M5 : Rabs (B2R t2 - B2R t4) <= (bpow radix2 (-21) + bpow radix2 (-39)) * B2R sh).
{ apply Rabs_le. clear -HL HSW B1 B2 Bph HSM HLM B3 B4 Hs. num. lra. }
assert (K5 : (bpow radix2 (-21) + bpow radix2 (-39)) * B2R sh <= 16) by (clear -Hs; num; lra).
destruct (sub_k t2 t4 _ F2 F4 M5 K5) as (F5 & _ & B5).
set (t5 := sub t2 t4) in *.
apply Rabs_le_inv in B5, M5, Bb.
assert (M6 : Rabs (B2R b + B2R t5) <= (bpow radix2 (-21) + bpow radix2 (-38)) * B2R sh).
{ apply Rabs_le. clear -Bb M5 B5 Hs. num. lra. }
assert (K6 : (bpow radix2 (-21) + bpow radix2 (-38)) * B2R sh <= 16) by (clear -Hs; num; lra).
destruct (add_k b t5 _ Fb F5 M6 K6) as (F6 & _ & B6).
set (t6 := add b t5) in *.
apply Rabs_le_inv in B6, M6, Ba.
(* [(h, l)] is [a + t6] exactly, by Fast2Sum, as [|t6| < 2^-20 sh < a]. *)
assert (Hapos : / 2 * B2R sh <= B2R a).
{ clear -Ba Hph Hs. num. lra. }
assert (Hat : Rabs (B2R t6) <= Rabs (B2R a) \/ B2R a = 0).
{ left. rewrite (Rabs_pos_eq (B2R a)) by lra. apply Rabs_le.
  clear -M6 B6 Hapos Hs. num. lra. }
assert (Hat2 : Rabs (B2R a + B2R t6) <= 2048).
{ apply Rabs_le. clear -M6 B6 Ba Hph Hs. num. lra. }
destruct (FastLogNorm.fts_exact a t6 h l Fa F6 Hat Hat2 E2) as (Fh & Fl & Eh & Ehl).
(* The error: [h + l = a + b + t5 + e6 = sh - ph + t5 + e6], where [t5]
   is [sl + sh wl - (pe + sl mh)] up to the roundings [e1] to [e5], and
   [ph + pe = sh mh]. Against [(sh + sl) (1 - mh + wl)] that leaves those
   six roundings and [-sl wl]: about [6 2^-74 sh] in all. *)
replace ((B2R sh + B2R sl) * (1 - B2R mh + B2R wl)) with
  (B2R sh - B2R sh * B2R mh + B2R sh * B2R wl + B2R sl - B2R sl * B2R mh
   + B2R sl * B2R wl) by ring.
assert (Herr : - (bpow radix2 (-70) * B2R sh) <=
  B2R a + B2R t6 - (B2R sh - B2R sh * B2R mh + B2R sh * B2R wl + B2R sl
    - B2R sl * B2R mh + B2R sl * B2R wl) <= bpow radix2 (-70) * B2R sh).
{ clear -HL HSW HLM HLW HSM B1 B2 Bph B3 B4 B5 B6 Eab Hs. num. lra. }
(* [h] is [h + l] rounded, and [h + l] is within [2^-10.9 sh] of [sh]. *)
assert (Bhl : Rabs (B2R a + B2R t6) <= 2 * B2R sh).
{ apply Rabs_le. clear -Herr HL HSW HLM HLW HSM Hs. num. lra. }
pose proof (rn_k (B2R a + B2R t6) (2 * B2R sh) Bhl) as Bh.
rewrite <- Eh in Bh. apply Rabs_le_inv in Bh.
rewrite Ehl.
split; [exact Fh |]. split; [exact Fl |]. split; [exact Eh |].
split; [| apply Rabs_le; exact Herr].
clear -Bh Herr HL HSW HLM HLW HSM Hs. num. lra.
Qed.

(** The error of [sh mh] is exact, so both variants of [two_prod_err]
    give the same [f64] ([FastRound.two_prod_err_fma_eq]). *)
Lemma near1_pe_fma : forall sh mh, is_finite sh = true -> is_finite mh = true ->
  bpow radix2 (-27) <= B2R sh <= bpow radix2 (-4) -> bpow radix2 (-57) <= B2R mh <= bpow radix2 (-11) ->
  Generic.two_prod_err true sh mh (mul sh mh) = Generic.two_prod_err false sh mh (mul sh mh).
Proof.
intros sh mh Fsh Fmh Hs Hm.
apply FastRound.two_prod_err_fma_eq; [exact Fsh | exact Fmh | apply pe_exact; assumption ..].
Qed.
