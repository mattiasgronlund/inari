(** * The low part of the quotient of [fast_quot] keeps its high part

    For [f64]s [n] and [d] in [[1, 2)], [n = N 2^-52] and [d = D 2^-52]
    with [D < 2^53], so the quotient [z = n / d] differs from a midpoint
    [M 2^-k] between two [f64]s of [[1/2, 2)], with [M] odd and [k] 53 or
    54, by [(N 2^k - M D) / (D 2^k)], whose numerator is a nonzero
    integer: [z] is more than [2^(-k-53)] away from it. The error
    [z - qh] of [qh = RN(z)] is then at most the [f64]
    [2^-k - 2^(-k-53)], which is less than half the gap between [qh] and
    its neighbour on that side, and so is its rounding, and [qh] is the
    rounding of [qh + RN(z - qh)] ([quot_mid]), as
    [FastAtanQuot.quot_facts] gives it for [dd_div]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core.
From Inari Require Import Model Encoding TwoSum.

Open Scope R_scope.

Local Notation format := (generic_format radix2 fexp64).

(** ** Helpers *)

(** An [f64] of magnitude at least [2^(e+52)] is an integer multiple of
    [2^e]: its exponent [cexp x] is at least [mag x - 53 >= e]. *)
Local Lemma fmt_int :
  forall x e, format x -> bpow radix2 (e + 52) <= Rabs x ->
  exists m, x = IZR m * bpow radix2 e.
Proof.
intros x e Fx Hx.
assert (He : (e <= cexp radix2 fexp64 x)%Z).
{ assert (Hm : (e + 53 <= mag radix2 x)%Z).
  { apply mag_ge_bpow. replace (e + 53 - 1)%Z with (e + 52)%Z by ring. exact Hx. }
  unfold cexp, FLT_exp. lia. }
exists (Ztrunc (scaled_mantissa radix2 fexp64 x) * Zpower radix2 (cexp radix2 fexp64 x - e))%Z.
rewrite mult_IZR, IZR_Zpower by lia.
rewrite Rmult_assoc, <- bpow_plus.
replace (cexp radix2 fexp64 x - e + e)%Z with (cexp radix2 fexp64 x) by ring.
exact Fx.
Qed.

(** An odd [A] times [0 < D < 2^k] is not a multiple of [2^k]: while [D]
    is even, halve it and the multiple of [2^k]; an odd [D] makes [A D]
    odd. *)
Local Lemma odd_ne :
  forall k A D N, Z.odd A = true -> (0 < D < Zpower_nat radix2 k)%Z ->
  (A * D <> N * Zpower_nat radix2 k)%Z.
Proof.
induction k as [| k IH]; intros A D N HA HD E.
- cbn in HD. lia.
- rewrite Zpower_nat_S in HD, E. set (P := Zpower_nat radix2 k) in *.
  change (radix_val radix2) with 2%Z in HD, E.
  destruct (Z.even D) eqn:ED.
  + apply Z.even_spec in ED. destruct ED as [D' ED]. subst D.
    apply (IH A D' N HA); lia.
  + assert (O : Z.odd (A * D) = true).
    { rewrite Z.odd_mul, HA, <- Z.negb_even, ED. reflexivity. }
    rewrite E in O.
    replace (N * (2 * P))%Z with (2 * (N * P))%Z in O by ring.
    rewrite Z.odd_mul in O. cbn in O. discriminate O.
Qed.

(** The quotient of two [f64]s of [[1, 2)] is more than [2^(-k-53)] away
    from the midpoint [u + 2^-k] above an [f64] [u >= 2^(53-k)], for
    [k >= 53]: [u = U 2^(1-k)], so the midpoint is [M 2^-k] with
    [M = 2 U + 1] odd, and [n / d - M 2^-k = (N 2^k - M D) / (D 2^k)],
    whose numerator is a nonzero integer ([odd_ne], with [D < 2^53 <= 2^k])
    and whose denominator is below [2^(k+53)]. *)
Local Lemma mid_far :
  forall n d u k, format n -> format d -> 1 <= n < 2 -> 1 <= d < 2 ->
  format u -> (53 <= k)%Z -> bpow radix2 (53 - k) <= u ->
  bpow radix2 (- k - 53) < Rabs (n / d - (u + bpow radix2 (- k))).
Proof.
intros n d u k Fn Fd Hn Hd Fu Hk Hu.
assert (H0 : bpow radix2 (-52 + 52) = 1) by reflexivity.
destruct (fmt_int n (-52) Fn) as [N EN]; [rewrite H0, Rabs_pos_eq; lra |].
destruct (fmt_int d (-52) Fd) as [D ED]; [rewrite H0, Rabs_pos_eq; lra |].
pose proof (bpow_gt_0 radix2 (53 - k)) as P53.
destruct (fmt_int u (1 - k) Fu) as [U EU].
{ replace (1 - k + 52)%Z with (53 - k)%Z by ring. rewrite Rabs_pos_eq by lra. exact Hu. }
assert (B52 : bpow radix2 (-52) = / 4503599627370496) by reflexivity.
rewrite B52 in EN, ED.
(* [0 < D < 2^53], from [1 <= d < 2]. *)
assert (HD : 0 < IZR D < 9007199254740992) by (rewrite ED in Hd; lra).
pose proof (bpow_gt_0 radix2 k) as HK.
assert (EP : bpow radix2 k = IZR (Zpower radix2 k)) by (rewrite IZR_Zpower by lia; reflexivity).
assert (Ek : bpow radix2 (- k) = / bpow radix2 k) by apply bpow_opp.
assert (EK : bpow radix2 (1 - k) = 2 * / bpow radix2 k).
{ replace (1 - k)%Z with (1 + - k)%Z by ring. rewrite bpow_plus, Ek. reflexivity. }
assert (E53 : bpow radix2 (- k - 53) = / (bpow radix2 k * 9007199254740992)).
{ replace (- k - 53)%Z with (- (k + 53))%Z by ring. rewrite bpow_opp, bpow_plus. reflexivity. }
(* The midpoint is [M 2^-k], with [M] odd. *)
set (M := (2 * U + 1)%Z).
assert (Em : u + bpow radix2 (- k) = IZR M / bpow radix2 k).
{ unfold M. rewrite EU, EK, Ek, plus_IZR, mult_IZR. field. lra. }
assert (EX : (n / d - (u + bpow radix2 (- k))) * (IZR D * bpow radix2 k)
  = IZR (N * Zpower radix2 k - M * D)).
{ rewrite Em, EN, ED, minus_IZR, !mult_IZR, <- EP. field. lra. }
(* The numerator [N 2^k - M D] is not 0. *)
assert (NZ : (N * Zpower radix2 k - M * D <> 0)%Z).
{ assert (OM : Z.odd M = true) by (unfold M; apply Z.odd_odd).
  assert (DK : (0 < D < Zpower radix2 k)%Z).
  { split; apply lt_IZR; [lra |]. rewrite <- EP.
    apply Rlt_le_trans with 9007199254740992; [lra |].
    change 9007199254740992 with (bpow radix2 53). apply bpow_le. lia. }
  rewrite Zpower_Zpower_nat in DK |- * by lia.
  pose proof (odd_ne (Z.abs_nat k) M D N OM DK). lia. }
assert (AX : 1 <= Rabs (IZR (N * Zpower radix2 k - M * D))).
{ rewrite <- abs_IZR. apply (IZR_le 1). lia. }
rewrite <- EX, Rabs_mult, (Rabs_pos_eq (IZR D * bpow radix2 k)) in AX
  by (apply Rmult_le_pos; lra).
(* [|n / d - M 2^-k| D 2^k >= 1 > 2^(-k-53) D 2^k], as [D < 2^53]. *)
rewrite E53.
apply Rmult_lt_reg_r with (IZR D * bpow radix2 k); [apply Rmult_lt_0_compat; lra |].
apply Rlt_le_trans with 1; [| exact AX].
replace (/ (bpow radix2 k * 9007199254740992) * (IZR D * bpow radix2 k))
  with (IZR D / 9007199254740992) by (field; lra).
lra.
Qed.

(** Above an [f64] [u] of [[1/2, 2)], the next [f64] is [u + 2 h] with
    [h = 2^-k], [k] 53 or 54, and the quotient of two [f64]s of [[1, 2)]
    is more than [h - B] away from the midpoint [u + h], for the [f64]
    [B = 2^-k - 2^(-k-53) < h] ([mid_far]). *)
Local Lemma gap :
  forall n d u, format n -> format d -> 1 <= n < 2 -> 1 <= d < 2 ->
  format u -> / 2 <= u < 2 ->
  exists h B, format B /\ 0 <= B < h /\ succ radix2 fexp64 u = u + 2 * h /\
  h - B < Rabs (n / d - (u + h)).
Proof.
intros n d u Fn Fd Hn Hd Fu Hu.
assert (K : exists k, (53 <= k <= 54)%Z /\
  bpow radix2 (53 - k) <= u < bpow radix2 (54 - k)).
{ destruct (Rlt_or_le u 1) as [L | L].
  - exists 54%Z. split; [lia |].
    change (bpow radix2 (53 - 54)) with (/ 2). change (bpow radix2 (54 - 54)) with 1. lra.
  - exists 53%Z. split; [lia |].
    change (bpow radix2 (53 - 53)) with 1. change (bpow radix2 (54 - 53)) with 2. lra. }
destruct K as (k & Hk & Hku).
pose proof (bpow_gt_0 radix2 (53 - k)) as P.
pose proof (bpow_gt_0 radix2 (- k - 53)) as P53.
assert (Ek : bpow radix2 (- k) = 9007199254740992 * bpow radix2 (- k - 53)).
{ change 9007199254740992 with (bpow radix2 53). rewrite <- bpow_plus. f_equal. ring. }
exists (bpow radix2 (- k)), (IZR 9007199254740991 * bpow radix2 (- k - 53)).
split; [| split; [split; nra | split]].
- (* [B = (2^53 - 1) 2^(-k-53)] has 53 bits. *)
  apply generic_format_FLT.
  apply (FLT_spec _ _ _ _ (Float radix2 9007199254740991 (- k - 53))).
  + reflexivity.
  + cbv. reflexivity.
  + cbn. lia.
- (* The ulp of [u] is [2^(mag u - 53) = 2^(1-k)]. *)
  rewrite succ_eq_pos by lra. rewrite ulp_neq_0 by lra.
  assert (Hm : mag radix2 u = (54 - k)%Z :> Z).
  { apply mag_unique_pos. replace (54 - k - 1)%Z with (53 - k)%Z by ring. exact Hku. }
  unfold cexp. rewrite Hm. unfold FLT_exp. rewrite Z.max_l by lia.
  replace (54 - k - 53)%Z with (1 + - k)%Z by ring. rewrite bpow_plus. reflexivity.
- replace (bpow radix2 (- k) - IZR 9007199254740991 * bpow radix2 (- k - 53))
    with (bpow radix2 (- k - 53)) by (rewrite Ek; ring).
  apply mid_far; [assumption .. | lia | lra].
Qed.

(** ** The theorem *)

(** For [f64]s [n] and [d] in [[1, 2)], [qh = RN(n / d)] is the rounding
    of [qh + RN(n / d - qh)]: the error [z - qh] of [z = n / d] is on the
    side of [z], between 0 and the [f64] [B] of [gap], and so is its
    rounding, which keeps [qh + RN(z - qh)] strictly on [qh]'s side of the
    midpoint between [qh] and its neighbour on that side. *)
Lemma quot_mid :
  forall n d, format n -> format d -> 1 <= n < 2 -> 1 <= d < 2 ->
  RN (RN (n / d) + RN (n / d - RN (n / d))) = RN (n / d).
Proof.
intros n d Fn Fd Hn Hd.
remember (n / d) as z eqn:Ez.
assert (Ed : z * d = n) by (rewrite Ez; field; lra).
assert (Hz : / 2 < z < 2) by (split; nra).
remember (RN z) as qh eqn:Eq.
assert (F2 : format (/ 2)).
{ change (/ 2) with (bpow radix2 (-1)). apply generic_format_bpow. unfold FLT_exp. lia. }
assert (Fq : format qh) by (rewrite Eq; apply generic_format_round; typeclasses eauto).
assert (Hq1 : / 2 <= qh).
{ rewrite Eq. apply round_ge_generic; [typeclasses eauto .. | exact F2 | lra]. }
assert (Hq2 : qh <= 2).
{ rewrite Eq. apply round_le_generic; [typeclasses eauto .. | | lra].
  change 2 with (bpow radix2 1). apply generic_format_bpow. unfold FLT_exp. lia. }
destruct (Rtotal_order z qh) as [Lt | [Eqz | Gt]].
- (* [z < qh]: the neighbour below [qh] is [u = pred qh], and
     [qh = u + 2 h]. *)
  remember (pred radix2 fexp64 qh) as u eqn:Eu.
  assert (Hu1 : / 2 <= u).
  { rewrite Eu. apply pred_ge_gt; [typeclasses eauto .. | exact F2 | exact Fq | lra]. }
  assert (Hu2 : u < qh).
  { rewrite Eu. apply pred_lt_id. apply Rgt_not_eq. lra. }
  assert (Fu : format u).
  { rewrite Eu. apply generic_format_pred; [typeclasses eauto .. | exact Fq]. }
  assert (Su : succ radix2 fexp64 u = qh).
  { rewrite Eu. apply succ_pred; [typeclasses eauto .. | exact Fq]. }
  assert (Hu : / 2 <= u < 2) by lra.
  destruct (gap n d u Fn Fd Hn Hd Fu Hu) as (h & B & FB & HB & Es & Hf).
  rewrite Su in Es. rewrite <- Ez in Hf.
  (* [RN z = qh], so [z] is at least the midpoint [u + h]. *)
  assert (Hm : u + h <= z).
  { destruct (Rle_or_lt (u + h) z) as [L | L]; [exact L | exfalso].
    assert (S : RN z <= u).
    { apply round_N_le_midp; [typeclasses eauto .. | exact Fu | rewrite Su; lra]. }
    rewrite <- Eq in S. lra. }
  (* So [z > qh - B], and [-B <= RN(z - qh) <= 0]. *)
  rewrite Rabs_pos_eq in Hf by lra.
  assert (L0 : RN (z - qh) <= 0).
  { apply round_le_generic; [typeclasses eauto .. | apply generic_format_0 | lra]. }
  assert (L1 : - B <= RN (z - qh)).
  { apply round_ge_generic;
      [typeclasses eauto .. | apply generic_format_opp; exact FB | lra]. }
  apply Rle_antisym.
  + apply round_le_generic; [typeclasses eauto .. | exact Fq | lra].
  + apply round_N_ge_midp; [typeclasses eauto .. | exact Fq |].
    rewrite <- Eu. lra.
- (* [z = qh]: the error is 0. *)
  replace (z - qh) with 0 by lra. rewrite round_0 by typeclasses eauto. rewrite Rplus_0_r.
  apply round_generic; [typeclasses eauto .. | exact Fq].
- (* [z > qh]: [qh < 2], and the neighbour above [qh] is [qh + 2 h]. *)
  assert (Hu : / 2 <= qh < 2) by lra.
  destruct (gap n d qh Fn Fd Hn Hd Fq Hu) as (h & B & FB & HB & Es & Hf).
  rewrite <- Ez in Hf.
  (* [RN z = qh], so [z] is at most the midpoint [qh + h]. *)
  assert (Hm : z <= qh + h).
  { destruct (Rle_or_lt z (qh + h)) as [L | L]; [exact L | exfalso].
    assert (S : succ radix2 fexp64 qh <= RN z).
    { apply round_N_ge_midp;
        [typeclasses eauto .. | apply generic_format_succ; [typeclasses eauto .. | exact Fq] |].
      rewrite (pred_succ radix2 fexp64 qh Fq). lra. }
    rewrite <- Eq in S.
    assert (Q0 : qh <> 0) by (apply Rgt_not_eq; lra).
    pose proof (succ_gt_id radix2 fexp64 qh Q0). lra. }
  (* So [z < qh + B], and [0 <= RN(z - qh) <= B]. *)
  rewrite Rabs_left1 in Hf by lra.
  assert (L0 : 0 <= RN (z - qh)).
  { apply round_ge_generic; [typeclasses eauto .. | apply generic_format_0 | lra]. }
  assert (L1 : RN (z - qh) <= B).
  { apply round_le_generic; [typeclasses eauto .. | exact FB | lra]. }
  apply Rle_antisym.
  + apply round_N_le_midp; [typeclasses eauto .. | exact Fq | lra].
  + apply round_ge_generic; [typeclasses eauto .. | exact Fq | lra].
Qed.
