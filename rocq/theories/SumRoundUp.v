(** * [sum_round_up] reduces a sum to [round_up_exact]

    [sum_round_up] normalizes both significands to [[2^125, 2^126)], swaps
    the operands so that [X] is the larger one, aligns the significand of
    the smaller one, [Y], to the exponent of [X] with a sticky bit, and adds
    or subtracts the significands. The lemmas below follow those steps. *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Spec.

Open Scope R_scope.

(** ** Floats with the same exponent *)

(** [(a + b) * 2^e = a * 2^e + b * 2^e]. *)
Lemma F2R_add :
  forall a b e,
  F2R (Float radix2 (a + b) e) =
    F2R (Float radix2 a e) + F2R (Float radix2 b e).
Proof. intros a b e. unfold F2R; cbn [Fnum Fexp]. rewrite plus_IZR. ring. Qed.

(** [(a - b) * 2^e = a * 2^e - b * 2^e]. *)
Lemma F2R_sub :
  forall a b e,
  F2R (Float radix2 (a - b) e) =
    F2R (Float radix2 a e) - F2R (Float radix2 b e).
Proof. intros a b e. unfold F2R; cbn [Fnum Fexp]. rewrite minus_IZR. ring. Qed.

(** [m * 2^e = (m * 2^d) * 2^(e - d)]. *)
Lemma F2R_shl :
  forall m e d, (0 <= d)%Z ->
  F2R (Float radix2 (m * 2^d) (e - d)) = F2R (Float radix2 m e).
Proof.
intros m e d Hd.
rewrite (F2R_change_exp radix2 (e - d) m e) by lia.
now replace (e - (e - d))%Z with d by ring.
Qed.

(** [cond_Ropp s p] has the sign [s] and the magnitude [p] if [p > 0]. *)
Lemma cond_Ropp_pos :
  forall s p, 0 < p ->
  Rlt_bool (cond_Ropp s p) 0 = s /\ Rabs (cond_Ropp s p) = p.
Proof.
intros s p Hp.
rewrite abs_cond_Ropp, Rabs_pos_eq by lra.
split; [|reflexivity].
destruct s; unfold cond_Ropp.
- apply Rlt_bool_true. lra.
- apply Rlt_bool_false. lra.
Qed.

(** ** Normalization *)

(** [norm m e] shifts [m] left by [sh = 125 - log2 m] bits, which puts it
    in [[2^125, 2^126)] and keeps the value [m * 2^e]. As [m < 2^106],
    [sh >= 20], so the lowest 20 bits of the result are zero. *)
Lemma norm_ok :
  forall m e, (0 < m < 2^106)%Z -> (-2^19 <= e <= 2^19)%Z ->
  exists mn en,
    (let* sh := checked_u 32 (leading_zeros 128 m - 2) in
     let* m' := shl 128 m sh in
     let* e' := checked_i 32 (e - sh) in
     Some (m', e'))%Z = Some (mn, en) /\
    (2^125 <= mn < 2^126)%Z /\ (mn mod 2^20 = 0)%Z /\
    (-2^19 - 125 <= en <= 2^19)%Z /\
    F2R (Float radix2 mn en) = F2R (Float radix2 m e).
Proof.
intros m e Hm He.
rewrite leading_zeros_pos by lia.
assert (Hk : (0 <= Z.log2 m < 106)%Z).
{ split; [apply Z.log2_nonneg|]. apply Z.log2_lt_pow2; lia. }
pose proof (Z.log2_spec m ltac:(lia)) as Hl.
set (k := Z.log2 m) in *. clearbody k.
replace (128 - 1 - k - 2)%Z with (125 - k)%Z by ring.
(* [2^k <= m < 2^(k + 1)], so [2^125 <= m * 2^(125 - k) < 2^126]. *)
assert (Hp : (2^k * 2^(125 - k) = 2^125 /\
              2^(Z.succ k) * 2^(125 - k) = 2^126)%Z).
{ rewrite <- !Z.pow_add_r by lia. split; f_equal; lia. }
assert (Hp0 : (0 < 2^(125 - k))%Z) by (apply Z.pow_pos_nonneg; lia).
assert (Hmn : (2^125 <= m * 2^(125 - k) < 2^126)%Z) by nia.
exists (m * 2^(125 - k))%Z, (e - (125 - k))%Z.
rewrite checked_u_ok by (simpl Z.pow in *; lia). cbv beta iota.
rewrite shl_ok by (simpl Z.pow in *; lia). cbv beta iota.
rewrite checked_i_ok by (simpl Z.pow in *; lia).
split; [reflexivity|].
split; [exact Hmn|].
split; [| split; [simpl Z.pow in *; lia|]].
- (* [2^(125 - k)] is a multiple of [2^20]. *)
  replace (125 - k)%Z with (105 - k + 20)%Z by ring.
  rewrite Z.pow_add_r, Z.mul_assoc by lia.
  apply Z.mod_mul, Z.pow_nonzero; lia.
- apply F2R_shl. lia.
Qed.

(** ** Ordering *)

(** With significands in [[2^125, 2^126)], comparing [(e, m)]
    lexicographically compares the values [m * 2^e]: a larger exponent [e1]
    gives at least [2^(125 + e1) >= 2^(126 + e2)]. *)
Lemma F2R_lex :
  forall m1 e1 m2 e2,
  (2^125 <= m1)%Z -> (0 <= m2 < 2^126)%Z ->
  (e2 < e1 \/ (e2 = e1 /\ m2 <= m1))%Z ->
  F2R (Float radix2 m2 e2) <= F2R (Float radix2 m1 e1).
Proof.
intros m1 e1 m2 e2 Hm1 Hm2 [He|[-> Hm]].
- apply Rle_trans with (bpow radix2 (126 + e2)).
  + apply Rlt_le, F2R_lt_bpow_plus; lia.
  + apply Rle_trans with (bpow radix2 (125 + e1)).
    * apply bpow_le. lia.
    * apply bpow_plus_le_F2R; lia.
- now apply F2R_le.
Qed.

(** [sum_round_up] swaps the operands so that [X = m1 * 2^e1] is the
    larger one, which keeps the sum. *)
Lemma order_ok :
  forall sx mx ex sy my ey,
  (2^125 <= mx < 2^126)%Z -> (2^125 <= my < 2^126)%Z ->
  (mx mod 2^20 = 0)%Z -> (my mod 2^20 = 0)%Z ->
  exists s1 m1 e1 s2 m2 e2,
    (if (ex <? ey) || ((ex =? ey) && (mx <? my))
     then ((sy, my, ey), (sx, mx, ex))
     else ((sx, mx, ex), (sy, my, ey)))%Z = ((s1, m1, e1), (s2, m2, e2)) /\
    (2^125 <= m1 < 2^126)%Z /\ (2^125 <= m2 < 2^126)%Z /\
    (m2 mod 2^20 = 0)%Z /\
    ((e1 = ex /\ e2 = ey) \/ (e1 = ey /\ e2 = ex)) /\ (e2 <= e1)%Z /\
    F2R (Float radix2 m2 e2) <= F2R (Float radix2 m1 e1) /\
    cond_Ropp sx (F2R (Float radix2 mx ex))
      + cond_Ropp sy (F2R (Float radix2 my ey)) =
    cond_Ropp s1 (F2R (Float radix2 m1 e1))
      + cond_Ropp s2 (F2R (Float radix2 m2 e2)).
Proof.
intros sx mx ex sy my ey Hmx Hmy Hlx Hly.
destruct ((ex <? ey) || ((ex =? ey) && (mx <? my)))%Z eqn:Hc.
- exists sy, my, ey, sx, mx, ex.
  split; [reflexivity|].
  repeat split; try lia.
  + apply F2R_lex; lia.
  + ring.
- exists sx, mx, ex, sy, my, ey.
  split; [reflexivity|].
  repeat split; try lia.
  apply F2R_lex; lia.
Qed.

(** ** Alignment *)

(** The lowest [d <= 20] bits of a multiple of [2^20] are zero. *)
Lemma mod_pow2_low :
  forall m d, (0 <= d <= 20)%Z -> (m mod 2^20 = 0)%Z -> (m mod 2^d = 0)%Z.
Proof.
intros m d Hd Hm.
assert (H0 : forall k, (0 <= k)%Z -> (2^k <> 0)%Z)
  by (intros k Hk; apply Z.pow_nonzero; lia).
apply Z.mod_divide in Hm; [|apply H0; lia].
apply Z.mod_divide; [apply H0; lia|].
apply Z.divide_trans with (2 := Hm).
exists (2^(20 - d))%Z. rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(** [sum_round_up] shifts the significand of [Y = my * 2^(ex - d)] right
    by [d] bits, to the exponent [ex] of [X]. The result [y] has
    [y * 2^ex <= Y < (y + 1) * 2^ex], and [sticky] tells whether
    [Y <> y * 2^ex]. As the lowest 20 bits of [my] are zero, bits are lost
    only if [d > 20], which leaves [y < 2^105]. *)
Lemma align_ok :
  forall my ex d,
  (2^125 <= my < 2^126)%Z -> (my mod 2^20 = 0)%Z -> (0 <= d)%Z ->
  exists y sticky,
    (if 128 <=? d then Some (0, true)
     else
       let* yd := shr 128 my d in
       let* p := shl 128 1 d in
       let* mask := checked_u 128 (p - 1) in
       Some (yd, negb (Z.land my mask =? 0)))%Z = Some (y, sticky) /\
    (0 <= y < 2^126)%Z /\ (sticky = true -> y < 2^105)%Z /\
    if sticky then
      F2R (Float radix2 y ex) < F2R (Float radix2 my (ex - d)) <
        F2R (Float radix2 (y + 1) ex)
    else F2R (Float radix2 my (ex - d)) = F2R (Float radix2 y ex).
Proof.
intros my ex d Hm Hl Hd.
destruct (Z.leb_spec 128 d) as [Hd128|Hd128].
- (* [Y < 2^(126 + ex - d) <= 2^ex]: all of [Y] is below the last bit
     of [X]. *)
  exists 0%Z, true.
  split; [reflexivity|].
  split; [simpl Z.pow; lia|].
  split; [intros _; simpl Z.pow; lia|].
  rewrite F2R_0, Z.add_0_l, F2R_bpow.
  split.
  + apply F2R_gt_0. cbn [Fnum]. lia.
  + apply Rlt_le_trans with (bpow radix2 (126 + (ex - d))).
    * apply F2R_lt_bpow_plus; lia.
    * apply bpow_le. lia.
- assert (Hpd : (0 < 2^d < 2^128)%Z).
  { split; [apply Z.pow_pos_nonneg | apply Z.pow_lt_mono_r]; lia. }
  rewrite shr_ok, shl_ok by lia. cbv beta iota.
  rewrite checked_u_ok by lia. cbv beta iota.
  (* The mask keeps the bits shifted out: [Z.land my (2^d - 1) = my mod 2^d]. *)
  replace (1 * 2^d - 1)%Z with (Z.ones d) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia.
  eexists _, _. split; [reflexivity|].
  pose proof (Z.div_mod my (2^d) ltac:(lia)) as Hqr.
  pose proof (Z.mod_pos_bound my (2^d) ltac:(lia)) as Hr.
  assert (Hq : (0 <= my / 2^d)%Z) by (apply Z.div_pos; lia).
  (* Bits are lost only if [d > 20]. *)
  assert (Hd20 : (my mod 2^d <> 0 -> 20 < d)%Z).
  { intros Hr0. destruct (Z.le_gt_cases d 20) as [Hd20|Hd20]; [|exact Hd20].
    exfalso. apply Hr0, mod_pow2_low; [lia | exact Hl]. }
  set (q := (my / 2^d)%Z) in *. set (r := (my mod 2^d)%Z) in *.
  clearbody q r.
  split; [simpl Z.pow in *; nia|].
  split.
  + (* [q * 2^21 <= q * 2^d <= my < 2^126]. *)
    intros Hs. apply Bool.negb_true_iff, Z.eqb_neq, Hd20 in Hs.
    assert (H21 : (2^21 <= 2^d)%Z) by (apply Z.pow_le_mono_r; lia).
    simpl Z.pow in *. nia.
  + (* [Y = (q * 2^d + r) * 2^(ex - d)], where [q * 2^d * 2^(ex - d)] is
       [q * 2^ex], and [r < 2^d]. *)
    rewrite <- (F2R_shl q ex d), <- (F2R_shl (q + 1) ex d) by lia.
    destruct (Z.eqb_spec r 0) as [Hr0|Hr0]; cbn [negb].
    * f_equal. f_equal. lia.
    * split; apply F2R_lt; lia.
Qed.

(** ** The sum *)

(** Operands with the same sign: [|v| = X + Y], which is [(mx + y) * 2^e]
    if not [sticky], and [(mx + y + δ) * 2^e] with [0 < δ < 1] if
    [sticky]. *)
Lemma same_sign_pre :
  forall s mx y e Y (sticky : bool),
  (2^125 <= mx < 2^126)%Z -> (0 <= y < 2^126)%Z -> (-2^20 <= e <= 2^20)%Z ->
  (if sticky then
     F2R (Float radix2 y e) < Y < F2R (Float radix2 (y + 1) e)
   else Y = F2R (Float radix2 y e)) ->
  round_up_exact_pre s (mx + y) e sticky
    (cond_Ropp s (F2R (Float radix2 mx e)) + cond_Ropp s Y).
Proof.
intros s mx y e Y sticky Hmx Hy He HY.
assert (HX : 0 < F2R (Float radix2 mx e)) by (apply F2R_gt_0; cbn [Fnum]; lia).
assert (Hy0 : 0 <= F2R (Float radix2 y e))
  by (apply F2R_ge_0; cbn [Fnum]; lia).
replace (cond_Ropp s (F2R (Float radix2 mx e)) + cond_Ropp s Y)
  with (cond_Ropp s (F2R (Float radix2 mx e) + Y))
  by (destruct s; unfold cond_Ropp; ring).
destruct (cond_Ropp_pos s (F2R (Float radix2 mx e) + Y)) as (Hs & Ha).
{ destruct sticky; lra. }
unfold round_up_exact_pre. rewrite Hs, Ha.
split; [simpl Z.pow in *; lia|].
split; [exact He|].
split; [intros _; simpl Z.pow in *; lia|].
split; [reflexivity|].
replace (mx + y + 1)%Z with (mx + (y + 1))%Z by ring.
rewrite (F2R_add mx y e), (F2R_add mx (y + 1) e).
destruct sticky; lra.
Qed.

(** Operands with opposite signs, where [Y <= X]: [|v| = X - Y], which is
    [(mx - y) * 2^e] if not [sticky], and [(mx - y - 1 + (1 - δ)) * 2^e]
    with [0 < 1 - δ < 1] if [sticky]. A [sticky] [Y] has [y < 2^105], so
    [mx - y - 1 >= 2^52]. *)
Lemma opposite_sign_pre :
  forall s mx y e Y (sticky : bool),
  (2^125 <= mx < 2^126)%Z -> (0 <= y)%Z -> (sticky = true -> y < 2^105)%Z ->
  (-2^20 <= e <= 2^20)%Z -> Y <= F2R (Float radix2 mx e) ->
  (if sticky then
     F2R (Float radix2 y e) < Y < F2R (Float radix2 (y + 1) e)
   else Y = F2R (Float radix2 y e)) ->
  (0 <= mx - y < 2^128)%Z /\ (0 <= mx - y - Z.b2z sticky < 2^128)%Z /\
  ((mx - y - Z.b2z sticky = 0)%Z -> sticky = false /\
     cond_Ropp s (F2R (Float radix2 mx e)) + cond_Ropp (negb s) Y = 0) /\
  ((mx - y - Z.b2z sticky <> 0)%Z ->
     round_up_exact_pre s (mx - y - Z.b2z sticky) e sticky
       (cond_Ropp s (F2R (Float radix2 mx e)) + cond_Ropp (negb s) Y)).
Proof.
intros s mx y e Y sticky Hmx Hy Hy105 He HXY HY.
replace (cond_Ropp s (F2R (Float radix2 mx e)) + cond_Ropp (negb s) Y)
  with (cond_Ropp s (F2R (Float radix2 mx e) - Y))
  by (destruct s; unfold cond_Ropp, negb; ring).
destruct sticky; cbn [Z.b2z].
- (* [y * 2^e < Y <= X], so [y < mx]. *)
  assert (Hlt : (y < mx)%Z) by (apply (lt_F2R radix2 e); lra).
  specialize (Hy105 eq_refl).
  assert (Hlo :
    F2R (Float radix2 (mx - y - 1) e) < F2R (Float radix2 mx e) - Y).
  { replace (mx - y - 1)%Z with (mx - (y + 1))%Z by ring.
    rewrite F2R_sub. lra. }
  assert (Hhi :
    F2R (Float radix2 mx e) - Y < F2R (Float radix2 (mx - y - 1 + 1) e)).
  { replace (mx - y - 1 + 1)%Z with (mx - y)%Z by ring.
    rewrite F2R_sub. lra. }
  assert (H0 : 0 < F2R (Float radix2 (mx - y - 1) e))
    by (apply F2R_gt_0; cbn [Fnum]; simpl Z.pow in *; lia).
  destruct (cond_Ropp_pos s (F2R (Float radix2 mx e) - Y)) as (Hs & Ha);
    [lra|].
  split; [simpl Z.pow in *; lia|].
  split; [simpl Z.pow in *; lia|].
  split; [intros Hm0; exfalso; simpl Z.pow in *; lia|].
  intros _. unfold round_up_exact_pre. rewrite Hs, Ha.
  split; [simpl Z.pow in *; lia|].
  split; [exact He|].
  split; [intros _; simpl Z.pow in *; lia|].
  split; [reflexivity|].
  split; assumption.
- (* [Y = y * 2^e <= X], so [y <= mx], and [X - Y = (mx - y) * 2^e]. *)
  rewrite Z.sub_0_r.
  assert (Hle : (y <= mx)%Z) by (apply (le_F2R radix2 e); lra).
  replace (F2R (Float radix2 mx e) - Y) with (F2R (Float radix2 (mx - y) e))
    by (rewrite F2R_sub; lra).
  split; [simpl Z.pow in *; lia|].
  split; [simpl Z.pow in *; lia|].
  split.
  + intros Hm0. split; [reflexivity|].
    rewrite Hm0, F2R_0. destruct s; unfold cond_Ropp; ring.
  + intros Hm0.
    assert (H0 : 0 < F2R (Float radix2 (mx - y) e))
      by (apply F2R_gt_0; cbn [Fnum]; lia).
    destruct (cond_Ropp_pos s _ H0) as (Hs & Ha).
    unfold round_up_exact_pre. rewrite Hs, Ha.
    split; [simpl Z.pow in *; lia|].
    split; [exact He|].
    split; [intros [=]|].
    split; reflexivity.
Qed.

(** ** [sum_round_up] *)

(** Either the sum is zero and [sum_round_up] returns +0 (so its
    [debug_assert!] holds), or [sum_round_up] calls [round_up_exact] with
    arguments that describe the sum. *)
Theorem sum_round_up_reduce :
  forall sx mx ex sy my ey,
  (0 < mx < 2^106)%Z -> (0 < my < 2^106)%Z ->
  (-2^19 <= ex <= 2^19)%Z -> (-2^19 <= ey <= 2^19)%Z ->
  let v := cond_Ropp sx (F2R (Float radix2 mx ex))
         + cond_Ropp sy (F2R (Float radix2 my ey)) in
  (v = 0 /\ Generic.sum_round_up sx mx ex sy my ey = Some zero) \/
  (exists neg m e sticky,
     round_up_exact_pre neg m e sticky v /\
     Generic.sum_round_up sx mx ex sy my ey = Generic.round_up_exact neg m e sticky).
Proof.
intros sx mx ex sy my ey Hmx Hmy Hex Hey v.
destruct (norm_ok mx ex Hmx Hex) as (mx' & ex' & Hnx & Hmx' & Hlx & Hex' & HX).
destruct (norm_ok my ey Hmy Hey) as (my' & ey' & Hny & Hmy' & Hly & Hey' & HY).
assert (Hv : v = cond_Ropp sx (F2R (Float radix2 mx' ex'))
               + cond_Ropp sy (F2R (Float radix2 my' ey')))
  by (unfold v; now rewrite HX, HY).
clearbody v. clear HX HY.
unfold Generic.sum_round_up. cbv beta zeta.
rewrite Hnx, Hny. cbv beta iota. clear Hnx Hny.
destruct (order_ok sx mx' ex' sy my' ey' Hmx' Hmy' Hlx Hly)
  as (s1 & m1 & e1 & s2 & m2 & e2 & -> & Hm1 & Hm2 & Hl2 & He & He12 & HXY
      & Hsum).
cbv beta iota.
rewrite Hsum in Hv. clear Hsum.
(* [0 <= e1 - e2 <= 2^20 + 125], so the casts to [i32] and [u32] keep it. *)
rewrite checked_i_ok by (simpl Z.pow in *; lia). cbv beta iota.
rewrite Z.mod_small by (simpl Z.pow in *; lia).
destruct (align_ok m2 e1 (e1 - e2) Hm2 Hl2 ltac:(lia))
  as (y & sticky & -> & Hy & Hy105 & Hloc).
replace (e1 - (e1 - e2))%Z with e2 in Hloc by ring.
cbv beta iota.
destruct (Bool.eqb s1 s2) eqn:Hs; cbv beta iota.
- (* Same signs: [m = m1 + y >= 2^125]. *)
  apply Bool.eqb_prop in Hs. subst s2 v.
  rewrite checked_u_ok by (simpl Z.pow in *; lia). cbv beta iota.
  replace (m1 + y =? 0)%Z with false by (simpl Z.pow in *; lia).
  right. exists s1, (m1 + y)%Z, e1, sticky. split; [|reflexivity].
  apply same_sign_pre;
    [exact Hm1 | exact Hy | simpl Z.pow in *; lia | exact Hloc].
- (* Opposite signs: [m = m1 - y - sticky], which is 0 only if [v = 0]. *)
  assert (Hs2 : s2 = negb s1) by (destruct s1, s2; easy).
  subst s2 v.
  destruct (opposite_sign_pre s1 m1 y e1 (F2R (Float radix2 m2 e2)) sticky)
    as (Ht & Hm & H0 & Hpre);
    [exact Hm1 | lia | exact Hy105 | simpl Z.pow in *; lia | exact HXY
    | exact Hloc |].
  rewrite (checked_u_ok 128 (m1 - y)) by exact Ht. cbv beta iota.
  rewrite (checked_u_ok 128 (m1 - y - Z.b2z sticky)) by exact Hm.
  cbv beta iota.
  destruct (Z.eqb_spec (m1 - y - Z.b2z sticky) 0) as [Hm0|Hm0].
  + (* An exact cancellation, which leaves [sticky] clear. *)
    destruct (H0 Hm0) as (-> & Hv0).
    left. split; [exact Hv0 | reflexivity].
  + right. exists s1, (m1 - y - Z.b2z sticky)%Z, e1, sticky.
    split; [now apply Hpre | reflexivity].
Qed.
