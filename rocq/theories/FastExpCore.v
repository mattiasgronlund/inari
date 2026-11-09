(** * The error of the fast path of [exp]

    Where [DyadicExp.fast_exp zh zl] returns [(h, l, e)], [h + l] is
    [e^(zh + zl) 2^-e] within [2^-68 - 2^-72], with [h] the rounding of [h
    + l] to nearest between 1/2 and 2 ([fast_exp_correct]): the reduction
    of [FastExpReduce.v], the Taylor polynomial of degree 4 of [e^r], the
    tables of [FastExpTables.v], and the errors of the roundings of
    [fast_exp], each of the products of two [f64]s that it does not round
    exact by [TwoProduct.v] [Dekker], and its sums of two [f64]s by
    Fast2Sum [Dekker]. It returns the same with and without an FMA
    ([fast_exp_fma]).

    [Dekker] T. J. Dekker, A floating-point technique for extending the
    available precision, Numer. Math. 18 (1971). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Relative.
From Inari Require Import Model Encoding Elementary TwoSum TwoProduct CancelLanes ExpSeries FastRound
  FastExpTables FastExpReduce FastExpErr FastExpPoly FastExpTbl FastExpProd.
From Inari Require MulRuTiny.

Open Scope R_scope.

(** ** The range test

    Copies of [FastExp.v]'s, which imports this file, with the range
    two-sided. *)

(** [B2R l] of an [f64] literal [l], as [m * 2^e]. *)
Local Ltac fc_lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** The range test of [fast_exp], [-707.0 <= zh && zh <= 709.0]. *)
Local Notation in_range zh :=
  (Model.le (from_bits 0xc086180000000000) zh && Model.le zh (from_bits 0x4086280000000000)).

Local Lemma fc_le_R :
  forall x y, is_finite x = true -> is_finite y = true -> Model.le x y = true -> B2R x <= B2R y.
Proof.
intros x y Fx Fy H. unfold Model.le in H. rewrite Bleb_correct in H by assumption.
destruct (Rle_bool_spec (B2R x) (B2R y)); [assumption | discriminate].
Qed.

Local Lemma fc_range :
  forall zh, in_range zh = true -> is_finite zh = true /\ -707 <= B2R zh <= 709.
Proof.
intros zh G. apply andb_prop in G as [G1 G2].
assert (Fz : is_finite zh = true).
{ destruct zh as [s|[|]| |s m e B]; try reflexivity; vm_compute in G1, G2; discriminate. }
split; [exact Fz|].
apply fc_le_R in G1; [| vm_compute; reflexivity | exact Fz].
apply fc_le_R in G2; [| exact Fz | vm_compute; reflexivity].
assert (L1 : B2R (from_bits 0xc086180000000000) = -707)
  by (fc_lit_B2R; cbn [bpow radix_val radix2]; lra).
assert (L2 : B2R (from_bits 0x4086280000000000) = 709)
  by (fc_lit_B2R; cbn [bpow radix_val radix2]; lra).
lra.
Qed.

(** [|e^d - 1| <= |d| (1 + 2 |d|)]: [1 + d <= e^d] and [1 - d <= e^-d],
    so [e^d (1 - d) <= 1]. *)
Local Lemma fc_exp_close : forall d, Rabs d <= / 4 -> Rabs (exp d - 1) <= Rabs d * (1 + 2 * Rabs d).
Proof.
intros d Hd.
pose proof (exp_ineq1_le d) as H1. pose proof (exp_ineq1_le (- d)) as H2.
pose proof (exp_pos d) as P.
assert (E : exp d * exp (- d) = 1)
  by (rewrite <- exp_plus; replace (d + - d) with 0 by ring; apply exp_0).
assert (H3 : exp d * (1 - d) <= 1) by (rewrite <- E; apply Rmult_le_compat_l; lra).
apply Rabs_le_inv in Hd.
destruct (Rle_or_lt 0 d) as [Hp | Hn].
- rewrite (Rabs_pos_eq d Hp).
  assert (E2 : exp d <= 1 + 2 * d) by nra.
  apply Rabs_le; split; nra.
- rewrite (Rabs_left d Hn).
  assert (E1 : exp d <= 1) by nra.
  apply Rabs_le; split; nra.
Qed.

(** ** The reduction *)

(** [k = 4096 (k >> 12) + 64 ((k >> 6) & 63) + (k & 63)], with both
    masked parts in [[0, 64)]. *)
Lemma k_split :
  forall k : Z,
  (0 <= Z.land k 63 < 64)%Z /\ (0 <= Z.land (Z.shiftr k 6) 63 < 64)%Z /\
  k = (4096 * Z.shiftr k 12 + 64 * Z.land (Z.shiftr k 6) 63 + Z.land k 63)%Z.
Proof.
intros k.
change 63%Z with (Z.ones 6).
rewrite !Z.land_ones, !Z.shiftr_div_pow2 by lia.
change (2 ^ 6)%Z with 64%Z. change (2 ^ 12)%Z with 4096%Z.
Z.div_mod_to_equations. lia.
Qed.

(** The reduction of [fast_exp]: [e^(zh + zl) 2^-e] is [2^(i/4096)
    2^(j/64) e^(rh + rl + d)] with [|d| <= 2^-72], where [i] and [j] are
    the indices of the two tables and [e = k >> 12]
    ([FastExpReduce.fast_exp_reduce]). *)
Lemma fast_exp_r :
  forall zh zl,
  is_finite zh = true -> is_finite zl = true -> Rabs (B2R zl) <= bpow radix2 (-40) ->
  -707 <= B2R zh <= 709 ->
  let kf := sub (add (mul zh (from_bits DyadicExp.INV)) DyadicExp.shifter) DyadicExp.shifter in
  let k := DyadicExp.to_i64 kf in
  let rh := sub zh (mul kf (from_bits DyadicExp.C1)) in
  let rl := sub zl (mul kf (from_bits DyadicExp.C2)) in
  is_finite rh = true /\ is_finite rl = true /\
  Rabs (B2R rh) <= 3 * bpow radix2 (-15) /\ Rabs (B2R rl) <= bpow radix2 (-20) /\
  (0 <= Z.land k 63 < 64)%Z /\ (0 <= Z.land (Z.shiftr k 6) 63 < 64)%Z /\
  (-1021 <= Z.shiftr k 12 <= 1022)%Z /\
  exists d, Rabs d <= bpow radix2 (-72) /\
  exp (B2R zh + B2R zl) * bpow radix2 (- Z.shiftr k 12) =
    Rexp2 (IZR (Z.land k 63) / 4096) * Rexp2 (IZR (Z.land (Z.shiftr k 6) 63) / 64)
    * exp (B2R rh + B2R rl + d).
Proof.
intros zh zl Fzh Fzl Hzl Hzh kf k rh rl.
pose proof (fast_exp_reduce zh zl Fzh Fzl Hzl Hzh) as H. cbv zeta in H.
fold kf in H. fold k in H. fold rh rl in H.
destruct H as (_ & _ & _ & He & Frh & Frl & _ & Hrh & Hrl & Hd).
destruct (k_split k) as (Hi & Hj & Hk).
do 7 (split; [assumption|]).
set (d := B2R zh + B2R zl - IZR k * (ln 2 / 4096) - (B2R rh + B2R rl)) in Hd.
exists d. split; [exact Hd|].
unfold Rexp2, Rpower. rewrite bpow_exp. change (IZR (radix_val radix2)) with 2.
rewrite <- !exp_plus. f_equal.
assert (Rk : IZR k = 4096 * IZR (Z.shiftr k 12) + 64 * IZR (Z.land (Z.shiftr k 6) 63)
                     + IZR (Z.land k 63))
  by (rewrite Hk at 1; rewrite !plus_IZR, !mult_IZR; reflexivity).
unfold d. rewrite Rk, opp_IZR. field.
Qed.

Theorem fast_exp_correct :
  forall fma zh zl h l e,
  is_finite zh = true -> is_finite zl = true -> Rabs (B2R zl) <= bpow radix2 (-40) ->
  DyadicExp.fast_exp fma zh zl = Some (h, l, e) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < B2R h < 2 /\ (-1021 <= e <= 1022)%Z /\
  Rabs (exp (B2R zh + B2R zl) * bpow radix2 (- e) - (B2R h + B2R l))
    <= bpow radix2 (-68) - bpow radix2 (-72).
Proof.
intros fma zh zl h l e Fzh Fzl Hzl H.
destruct (in_range zh) eqn:G.
2:{ unfold DyadicExp.fast_exp in H. rewrite G in H. discriminate H. }
destruct (fc_range zh G) as [_ Hzh].
pose proof (fast_exp_r zh zl Fzh Fzl Hzl Hzh) as Hr. cbv zeta in Hr.
unfold DyadicExp.fast_exp in H. rewrite G in H.
cbv beta iota zeta delta [negb Fast.fast_two_sum] in H.
set (kf := sub (add (mul zh (from_bits DyadicExp.INV)) DyadicExp.shifter) DyadicExp.shifter) in *.
set (k := DyadicExp.to_i64 kf) in *.
set (rh := sub zh (mul kf (from_bits DyadicExp.C1))) in *.
set (rl := sub zl (mul kf (from_bits DyadicExp.C2))) in *.
destruct Hr as (Frh & Frl & Hrh & Hrl & Hi & Hj & He & d & Hd & Hexp).
pose proof (fast_exp_poly rh rl Frh Frl Hrh Hrl) as Hp. cbv zeta in Hp.
set (rr := add rh rl) in *.
set (q := mul (mul rr rr)
  (add half (mul rr (add (from_bits DyadicExp.P3) (mul rr (from_bits DyadicExp.P4)))))) in *.
set (s := add DyadicExp.one rh) in *.
set (pl := add (add (add rh (sub DyadicExp.one s)) rl) q) in *.
destruct Hp as (Fs & Fpl & Hs & Hpl & Hspl & Hpoly).
destruct (DyadicExp.tbl DyadicExp.T1 (Z.land k 63)) as [a1h a1l] eqn:E1.
destruct (DyadicExp.tbl DyadicExp.T2 (Z.land (Z.shiftr k 6) 63)) as [a2h a2l] eqn:E2.
cbv beta iota in H.
pose proof (fast_exp_tbl fma _ _ a1h a1l a2h a2l Hi Hj E1 E2) as Ht. cbv zeta in Ht.
set (th := mul a1h a2h) in *.
set (tl := add (Generic.two_prod_err fma a1h a2h th) (add (mul a1h a2l) (mul a1l a2h))) in *.
destruct Ht as (Fth & Ftl & Hth & Htl & Htt & _).
pose proof (tbl_T_bounds _ _ Hi Hj) as HT.
set (TT := Rexp2 (IZR (Z.land k 63) / 4096) * Rexp2 (IZR (Z.land (Z.shiftr k 6) 63) / 64)) in *.
(* [s + pl] is within [25 * 2^-18] of 1 and [th + tl] within [2^-100] of
   [TT], so their product is between 3/4 and [2 - 2^-15]. *)
pose proof Hspl as Hspl'. apply Rabs_le_inv in Hspl'.
pose proof Htt as Htt'. apply Rabs_le_inv in Htt'.
assert (Hpth : 3 / 4 <= (B2R s + B2R pl) * (B2R th + B2R tl) <= 2 - bpow radix2 (-15)).
{ cbn [bpow radix_val radix2] in Hspl', Htt', HT |- *. split.
  - apply Rle_trans with ((1 - 25 * / IZR (Z.pow_pos 2 18)) * (1 - / IZR (Z.pow_pos 2 100))).
    + lra.
    + apply Rmult_le_compat; lra.
  - apply Rle_trans with ((1 + 25 * / IZR (Z.pow_pos 2 18))
      * (2 - / IZR (Z.pow_pos 2 12) + / IZR (Z.pow_pos 2 26) + / IZR (Z.pow_pos 2 100))).
    + apply Rmult_le_compat; lra.
    + lra. }
pose proof (fast_exp_prod fma s pl th tl Fs Fpl Fth Ftl Hs Hpl Hth Htl Hpth) as Hq. cbv zeta in Hq.
injection H as <- <- <-.
destruct Hq as (Fh & Fl & Hh & Hh2 & Hq).
do 5 (split; [assumption|]).
match goal with |- Rabs (_ - ?x) <= _ => set (hl := x) in * end.
rewrite Hexp, exp_plus.
set (E := exp (B2R rh + B2R rl)) in *.
set (P := B2R s + B2R pl) in *.
set (Th := B2R th + B2R tl) in *.
(* The error is [TT E (e^d - 1) + TT (E - P) + P (TT - Th) + (P Th -
   hl)]: at most [2^-71 + 2^-70 + 2^-99 + 2^-69]. *)
assert (Hid : TT * (E * exp d) - hl
              = TT * E * (exp d - 1) + TT * (E - P) + P * (TT - Th) + (P * Th - hl)) by ring.
rewrite Hid.
pose proof Hpoly as Hpoly'. apply Rabs_le_inv in Hpoly'.
assert (E0 : 0 < E) by apply exp_pos.
assert (HA : Rabs (TT * E * (exp d - 1)) <= bpow radix2 (-71)).
{ assert (Hd4 : Rabs d <= / 4)
    by (apply Rle_trans with (1 := Hd); cbn [bpow radix_val radix2]; lra).
  pose proof (fc_exp_close d Hd4) as Hc.
  assert (HTE : TT * E <= 2 - bpow radix2 (-16)).
  { apply Rle_trans with ((2 - bpow radix2 (-12) + bpow radix2 (-26))
                          * (1 + 25 * bpow radix2 (-18) + bpow radix2 (-71))).
    - apply Rmult_le_compat; lra.
    - cbn [bpow radix_val radix2]; lra. }
  assert (Hd2 : Rabs d * (1 + 2 * Rabs d)
                <= bpow radix2 (-72) * (1 + 2 * bpow radix2 (-72))).
  { pose proof (Rabs_pos d). apply Rmult_le_compat; lra. }
  rewrite Rabs_mult, (Rabs_pos_eq (TT * E)) by nra.
  apply Rle_trans with ((2 - bpow radix2 (-16)) * (bpow radix2 (-72) * (1 + 2 * bpow radix2 (-72)))).
  - apply Rmult_le_compat; [nra | apply Rabs_pos | exact HTE | lra].
  - cbn [bpow radix_val radix2]; lra. }
assert (HB : Rabs (TT * (E - P)) <= bpow radix2 (-70)).
{ rewrite Rabs_mult, (Rabs_pos_eq TT) by lra.
  apply Rle_trans with (2 * bpow radix2 (-71)).
  - apply Rmult_le_compat; [lra | apply Rabs_pos | cbn [bpow radix_val radix2] in HT; lra | exact Hpoly].
  - cbn [bpow radix_val radix2]; lra. }
assert (HC : Rabs (P * (TT - Th)) <= bpow radix2 (-99)).
{ rewrite Rabs_mult, (Rabs_pos_eq P) by (cbn [bpow radix_val radix2] in Hspl'; lra).
  rewrite Rabs_minus_sym.
  apply Rle_trans with (2 * bpow radix2 (-100)).
  - apply Rmult_le_compat; [cbn [bpow radix_val radix2] in Hspl'; lra | apply Rabs_pos
      | cbn [bpow radix_val radix2] in Hspl'; lra | exact Htt].
  - cbn [bpow radix_val radix2]; lra. }
apply Rabs_le_inv in HA, HB, HC, Hq.
apply Rabs_le. cbn [bpow radix_val radix2] in HA, HB, HC, Hq |- *. split; lra.
Qed.

Theorem fast_exp_fma :
  forall zh zl, DyadicExp.fast_exp true zh zl = DyadicExp.fast_exp false zh zl.
Proof.
intros zh zl.
destruct (in_range zh) eqn:G.
2:{ unfold DyadicExp.fast_exp. rewrite G. reflexivity. }
destruct (fc_range zh G) as [Fzh Hzh].
(* [rh], [k], [s] and [th] do not depend on [zl], so the reduction of
   [zh + 0] bounds them. *)
assert (Hz0 : Rabs (B2R zero) <= bpow radix2 (-40))
  by (cbn [B2R zero]; rewrite Rabs_R0; apply bpow_ge_0).
pose proof (fast_exp_r zh zero Fzh eq_refl Hz0 Hzh) as Hr. cbv zeta in Hr.
unfold DyadicExp.fast_exp. rewrite G.
cbv beta iota zeta delta [negb Fast.fast_two_sum].
set (kf := sub (add (mul zh (from_bits DyadicExp.INV)) DyadicExp.shifter) DyadicExp.shifter) in *.
set (k := DyadicExp.to_i64 kf) in *.
set (rh := sub zh (mul kf (from_bits DyadicExp.C1))) in *.
destruct Hr as (Frh & _ & Hrh & _ & Hi & Hj & _).
destruct (fast_exp_s rh Frh Hrh) as [Fs Hs].
set (s := add DyadicExp.one rh) in *.
destruct (DyadicExp.tbl DyadicExp.T1 (Z.land k 63)) as [a1h a1l] eqn:E1.
destruct (DyadicExp.tbl DyadicExp.T2 (Z.land (Z.shiftr k 6) 63)) as [a2h a2l] eqn:E2.
cbv beta iota.
destruct (t1_correct _ _ _ Hi E1) as (Fa1 & _).
destruct (t2_correct _ _ _ Hj E2) as (Fa2 & _).
pose proof (fast_exp_tbl false _ _ a1h a1l a2h a2l Hi Hj E1 E2) as Ht. cbv zeta in Ht.
set (th := mul a1h a2h) in *.
destruct Ht as (Fth & _ & Hth & _ & _ & Hx).
(* Both products are exact, so [Generic.two_prod_err] gives the same
   [f64] with and without an FMA ([FastRound.two_prod_err_fma_eq]). *)
assert (X1 : Generic.two_prod_err true a1h a2h th = Generic.two_prod_err false a1h a2h th)
  by exact (two_prod_err_fma_eq a1h a2h Fa1 Fa2 (Hx true) (Hx false)).
assert (X2 : Generic.two_prod_err true s th (mul s th) = Generic.two_prod_err false s th (mul s th))
  by exact (two_prod_err_fma_eq s th Fs Fth
              (prod_exact true s th Fs Fth Hs Hth) (prod_exact false s th Fs Fth Hs Hth)).
rewrite X1, X2. reflexivity.
Qed.
