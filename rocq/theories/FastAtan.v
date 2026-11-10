(** * The fast paths of [atan] and [atan2]

    Where [DyadicAtan.fast_atan_dir] and the others of [Model.v] return,
    they return [atan x] and [Ratan2 y x] rounded toward +inf if [up] and
    toward -inf otherwise ([fast_atan_dir_correct],
    [fast_atan2_dir_correct]), and rounded to nearest
    ([fast_atan_near_correct], [fast_atan2_near_correct]), from the core
    of [FastAtanCore.v], the assembly of [FastAtanAsm.v] and the tests of
    [FastRoundErr.v]. [atan] at [|x| <= 1] is the core at [|x|], and above
    1 it is π/2 - atan(1/|x|) ([AtanIdent.atan_half_inv]). [atan2] of
    [(y, x)] is atan of the quotient [q] of the smaller of [|y|], [|x|]
    by the larger, then [atan q], [π - atan q], [π/2 - atan q] or [π/2 +
    atan q] by the octant ([AtanReal.Ratan2_pos_x], [Ratan2_neg_x_ge],
    [ar_up]), with the sign of [y]; for [q < 2^-59], atan q is [q]
    within far less than the test needs, and a result below 2^-1021
    returns [None]. [atan] is odd in [x], and [atan2] in [y]. They
    return the same with and without an FMA ([fast_atan_dir_fma] and the
    others). [fast_atan_dir_range] and the other range lemmas give the
    ranges from the rules of [atan_dir_with] and [atan_near_with] that
    run first. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Encoding Elementary AtanReal AtanIdent TwoSum DyDriver
  NearF64 NearCells FastRound FastRoundErr FastDiv FastHypPos FastAtanTables FastAtanIdent
  FastAtanCore FastAtanAsm FastAtanQuot.
From Inari Require DyExp DyPown FastExpErr FastLogReduce AtanSeries TwoProduct.

Open Scope R_scope.

(** ** The ranges the rules leave *)

(** [B2R l] of an [f64] literal [l], as [m * 2^e] (as in [FastHypPos.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** A literal [2^k] with a mantissa of [2^52]. *)
Local Ltac lit_pow2 :=
  lit_B2R; change (IZR 4503599627370496) with (bpow radix2 52); rewrite <- bpow_plus;
  reflexivity.

Local Lemma lit_huge : B2R DyadicAtan.huge_atan = bpow radix2 54.
Proof. lit_pow2. Qed.

Local Lemma lit_tiny_hyp : B2R DyadicExp.tiny_hyp = bpow radix2 (-26).
Proof. lit_pow2. Qed.

Local Lemma fabs_facts :
  forall x, is_finite x = true ->
  is_finite (fabs x) = true /\ B2R (fabs x) = Rabs (B2R x) /\ 0 <= B2R (fabs x).
Proof.
intros x Fx. unfold fabs. rewrite is_finite_Babs, B2R_Babs.
split; [exact Fx | split; [reflexivity | apply Rabs_pos]].
Qed.

(** [ge (fabs x) huge_atan = false] is [|x| < 2^54], and [lt (fabs x) c =
    false] is [c <= |x|]. *)
Local Lemma range_of :
  forall x c k,
  is_finite x = true -> is_finite c = true -> B2R c = bpow radix2 k -> (-27 <= k)%Z ->
  ge (fabs x) DyadicAtan.huge_atan = false -> lt (fabs x) c = false ->
  bpow radix2 (-27) <= Rabs (B2R x) < bpow radix2 54.
Proof.
intros x c k Fx Fc Ec Hk G L.
destruct (fabs_facts x Fx) as (Ft & Et & _).
assert (Fh : is_finite DyadicAtan.huge_atan = true) by (vm_compute; reflexivity).
pose proof (ge_false _ _ Ft Fh G) as Hh. pose proof (lt_false _ _ Ft Fc L) as Hl.
rewrite Et, lit_huge in Hh. rewrite Et, Ec in Hl.
split; [|exact Hh].
apply Rle_trans with (2 := Hl). apply bpow_le. exact Hk.
Qed.

Lemma fast_atan_dir_range :
  forall x,
  is_finite x = true -> ge (fabs x) DyadicAtan.huge_atan = false ->
  lt (fabs x) DyadicExp.tiny_hyp = false ->
  bpow radix2 (-27) <= Rabs (B2R x) < bpow radix2 54.
Proof.
intros x Fx G L.
apply (range_of x DyadicExp.tiny_hyp (-26) Fx); [vm_compute; reflexivity | exact lit_tiny_hyp
  | lia | exact G | exact L].
Qed.

Lemma fast_atan_near_range :
  forall x,
  is_finite x = true -> ge (fabs x) DyadicAtan.huge_atan = false ->
  lt (fabs x) DyadicExp.tiny_near = false ->
  bpow radix2 (-27) <= Rabs (B2R x) < bpow radix2 54.
Proof.
intros x Fx G L.
apply (range_of x DyadicExp.tiny_near (-27) Fx); [vm_compute; reflexivity | exact lit_tiny
  | lia | exact G | exact L].
Qed.

(** ** Before the rounding *)

Local Notation G := (generic_format radix2 fexp64).

Local Lemma lit_err70 : B2R DyadicAtan.err70 = bpow radix2 (-70).
Proof. lit_pow2. Qed.

(** The low part of a rounded-to-nearest normal value is within [2^-53] of
    it relatively (as in [FastAtanCore.v]). *)
Local Lemma low_rel :
  forall x (h : f64), B2R h = RN x -> bpow radix2 (-1022) <= Rabs (B2R h) ->
  Rabs (x - B2R h) <= bpow radix2 (-53) * Rabs (B2R h).
Proof.
intros x h Hh Hb.
rewrite Hh in *.
rewrite <- Rabs_Ropp, Ropp_minus_distr.
apply Rle_trans with (/ 2 * ulp radix2 fexp64 (RN x)).
{ apply error_le_half_ulp_round; typeclasses eauto. }
assert (Hb' : bpow radix2 (-1074 + 53 - 1) <= Rabs (RN x)) by exact Hb.
pose proof (ulp_FLT_le radix2 (-1074) 53 (RN x) Hb') as U.
assert (B : bpow radix2 (1 - 53) = / 4503599627370496 /\ bpow radix2 (-53) = / 9007199254740992)
  by (split; reflexivity).
destruct B as (B1 & B2). rewrite B1 in U. rewrite B2. lra.
Qed.

Theorem fast_atan_pos_correct :
  forall fma t h l e err,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < bpow radix2 54 ->
  DyadicAtan.fast_atan_pos fma t = Some (h, l, e, err) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= e <= 1022)%Z /\
  exists p, (55 <= p <= 105)%Z /\ B2R err = bpow radix2 (- p) /\
    Rabs (atan (B2R t) * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (- p).
Proof.
intros fma t h l e err Ft Ht H.
destruct FastLogReduce.one_R as (F1 & E1).
assert (Fz : is_finite zero = true) by reflexivity.
assert (Ez : B2R zero = 0) by reflexivity.
pose proof (bpow_gt_0 radix2 (-27)) as P27.
assert (B53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
unfold DyadicAtan.fast_atan_pos in H.
destruct (le t DyadicExp.one) eqn:Le.
- (* [t <= 1]: the core at [t], and the octant [(false, false)]. *)
  assert (Ht1 : B2R t <= 1).
  { rewrite <- E1. exact (ge_true DyadicExp.one t F1 Ft Le). }
  destruct (DyadicAtan.fast_atan_core fma t zero) as [[ah al]|] eqn:Ec; [|discriminate H].
  assert (Eo : DyadicAtan.octant false false ah al = (h, l, e, err)) by congruence.
  assert (Hth : bpow radix2 (-61) <= B2R t <= 129 / 128).
  { split; [|lra]. apply Rle_trans with (2 := proj1 Ht). apply bpow_le. lia. }
  assert (Htl : Rabs (B2R zero) <= bpow radix2 (-53) * B2R t).
  { rewrite Ez, Rabs_R0. apply Rmult_le_pos; [apply bpow_ge_0 | lra]. }
  destruct (fast_atan_core_correct fma t zero ah al Ft Fz Hth Htl Ec) as (Fah & Fal & Rah & Hc).
  rewrite Ez, Rplus_0_r in Hc.
  assert (Hv : 0 < atan (B2R t) <= 4 / 5) by (apply atan_pos_le; lra).
  assert (Hlo : bpow radix2 (-1020) <= atan (B2R t)).
  { apply Rle_trans with (B2R t / 2); [|apply atan_lower; lra].
    assert (E28 : bpow radix2 (-28) = bpow radix2 (-27) / 2)
      by (cbn [bpow radix_val radix2]; lra).
    apply Rle_trans with (bpow radix2 (-28)); [apply bpow_le; lia | lra]. }
  assert (Hc' : Rabs (B2R ah + B2R al - atan (B2R t)) <= bpow radix2 (-73) * atan (B2R t)).
  { apply Rle_trans with (1 := Hc). apply Rmult_le_compat_r; [lra | apply bpow_le; lia]. }
  destruct (octant_correct false false ah al (atan (B2R t)) h l e err Fah Fal Rah Hv
    (conj Hlo Hc') Eo) as (Fh & Fl & Rh & He & Herr & Hb).
  split; [exact Fh|]. split; [exact Fl|]. split; [exact Rh|]. split; [lia|].
  exists 70%Z. split; [lia|]. split; [exact Herr | exact Hb].
- (* [t > 1]: [π/2 - atan (1/t)], with [1/t = (1/m) 2^-k]. *)
  assert (Ht1 : 1 < B2R t).
  { rewrite <- E1. exact (ge_false DyadicExp.one t F1 Ft Le). }
  destruct (DyadicAtan.split t) as (m, k) eqn:Es.
  cbv beta iota zeta in H.
  destruct (Fast.dd_div fma DyadicExp.one zero m zero) as (qh, ql) eqn:Ed.
  destruct (big_input fma t m k qh ql Ft (conj Ht1 (proj2 Ht)) Es Ed) as (_ & _ & S).
  cbv zeta in S. destruct S as (Fth & Ftl & Hth & Htl & Hin).
  destruct (DyadicAtan.fast_atan_core fma (mul qh (DyadicExp.two_pow (- k)))
    (mul ql (DyadicExp.two_pow (- k)))) as [[ah al]|] eqn:Ec; [|discriminate H].
  assert (Eo : DyadicAtan.octant true false ah al = (h, l, e, err)) by congruence.
  destruct (fast_atan_core_correct fma _ _ ah al Fth Ftl Hth Htl Ec) as (Fah & Fal & Rah & Hc).
  assert (Hq : 0 < 1 / B2R t < 1).
  { split; [apply Rdiv_lt_0_compat; lra|].
    apply Rmult_lt_reg_r with (B2R t); [lra|].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  assert (Ha : Rabs (B2R ah + B2R al - atan (1 / B2R t)) <= bpow radix2 (-73)).
  { apply (atan_abs_err (B2R (mul qh (DyadicExp.two_pow (- k))) + B2R (mul ql (DyadicExp.two_pow (- k)))));
      [| |exact Hc].
    - rewrite B53 in Htl. apply Rabs_le_inv in Htl. lra.
    - apply Rle_trans with (1 := Hin).
      apply Rle_trans with (bpow radix2 (-96) * 1).
      + apply Rmult_le_compat_l; [apply bpow_ge_0 | lra].
      + rewrite Rmult_1_r. apply bpow_le. lia. }
  assert (Hv : 0 < atan (1 / B2R t) <= 4 / 5) by (apply atan_pos_le; lra).
  destruct (octant_correct true false ah al (atan (1 / B2R t)) h l e err Fah Fal Rah Hv Ha Eo)
    as (Fh & Fl & Rh & He & Herr & Hb).
  rewrite (atan_half_inv (B2R t)) by lra.
  split; [exact Fh|]. split; [exact Fl|]. split; [exact Rh|]. split; [lia|].
  exists 70%Z. split; [lia|]. split; [exact Herr | exact Hb].
Qed.

(** The quotient [n / d] of [atan2]: the smaller of [a] and [b] by the
    larger, and [Ratan2] of [(a, +-b)] from [atan (n / d)] by the octant
    ([AtanReal.ar_up], [Ratan2_pos_x], [Ratan2_neg_x_ge]), in the form of
    [FastAtanAsm.octant_correct]. *)
Local Lemma atan2_nd :
  forall a b (neg : bool) n d,
  is_finite a = true -> is_finite b = true -> 0 < B2R a -> 0 < B2R b ->
  (if gt a b then (b, a) else (a, b)) = (n, d) ->
  is_finite n = true /\ is_finite d = true /\ 0 < B2R n <= B2R d /\
  Ratan2 (B2R a) (if neg then - B2R b else B2R b) =
    (if gt a b then
       (if neg then PI / 2 + atan (B2R n / B2R d) else PI / 2 - atan (B2R n / B2R d))
     else (if neg then PI - atan (B2R n / B2R d) else atan (B2R n / B2R d))).
Proof.
intros a b neg n d Fa Fb Ha Hb End.
destruct (gt a b) eqn:Gab; cbv beta iota in End; injection End as <- <-.
- (* [b < a]: [π/2 - atan (+-b / a)] ([ar_up]). *)
  pose proof (gt_true a b Fa Fb Gab) as Hlt.
  split; [exact Fb|]. split; [exact Fa|]. split; [lra|].
  rewrite ar_up by exact Ha.
  destruct neg; cbv beta iota; [|reflexivity].
  replace (- B2R b / B2R a) with (- (B2R b / B2R a)) by (unfold Rdiv; ring).
  rewrite atan_opp. ring.
- (* [a <= b]: [atan (a / b)], or [atan (a / -b) + π] ([Ratan2_neg_x_ge]). *)
  pose proof (gt_false a b Fa Fb Gab) as Hle.
  split; [exact Fa|]. split; [exact Fb|]. split; [lra|].
  destruct neg; cbv beta iota.
  + rewrite Ratan2_neg_x_ge by lra.
    replace (B2R a / - B2R b) with (- (B2R a / B2R b)) by (field; apply Rgt_not_eq; lra).
    rewrite atan_opp. ring.
  + apply Ratan2_pos_x. exact Hb.
Qed.

(** [n / d] as the quotient of the significands of [n] and [d] times
    [2^(en - ed)], with [en - ed <= 0] as [n <= d]. *)
Local Lemma atan2_split :
  forall n d mn en md ed,
  is_finite n = true -> is_finite d = true -> 0 < B2R n <= B2R d ->
  DyadicAtan.split n = (mn, en) -> DyadicAtan.split d = (md, ed) ->
  is_finite mn = true /\ is_finite md = true /\ 1 <= B2R mn < 2 /\ 1 <= B2R md < 2 /\
  B2R n / B2R d = B2R mn / B2R md * bpow radix2 (en - ed) /\ (en - ed <= 0)%Z /\
  0 < B2R n / B2R d <= 1.
Proof.
intros n d mn en md ed Fn Fd Hnd Esn Esd.
pose proof (FastAtanAsm.split_correct n Fn (proj1 Hnd)) as Sn.
rewrite Esn in Sn. cbv beta iota in Sn. destruct Sn as (Fmn & Hmn & Vn & _).
pose proof (FastAtanAsm.split_correct d Fd ltac:(lra)) as Sd.
rewrite Esd in Sd. cbv beta iota in Sd. destruct Sd as (Fmd & Hmd & Vd & _).
assert (Q : B2R n / B2R d = B2R mn / B2R md * bpow radix2 (en - ed)).
{ rewrite Vn, Vd. replace (en - ed)%Z with (en + - ed)%Z by lia.
  rewrite bpow_plus, bpow_opp.
  assert (B2R md <> 0) by (apply Rgt_not_eq; lra).
  assert (bpow radix2 ed <> 0) by (apply Rgt_not_eq, bpow_gt_0).
  field; repeat split; assumption. }
assert (Hq01 : 0 < B2R n / B2R d <= 1).
{ split; [apply Rdiv_lt_0_compat; lra|].
  apply Rmult_le_reg_r with (B2R d); [lra|].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l by (apply Rgt_not_eq; lra). lra. }
(* [mn / md > 1/2], so [en - ed >= 1] would make [n / d > 1]. *)
assert (Hr : / 2 < B2R mn / B2R md).
{ apply Rmult_lt_reg_r with (B2R md); [lra|].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l by (apply Rgt_not_eq; lra). lra. }
split; [exact Fmn|]. split; [exact Fmd|]. split; [exact Hmn|]. split; [exact Hmd|].
split; [exact Q|]. split; [|exact Hq01].
destruct (Z_le_gt_dec (en - ed) 0) as [Hle | Hgt]; [exact Hle | exfalso].
assert (B : 2 <= bpow radix2 (en - ed)).
{ change 2 with (bpow radix2 1). apply bpow_le. lia. }
set (r := B2R mn / B2R md) in *. set (q := B2R n / B2R d) in *.
set (E := bpow radix2 (en - ed)) in *.
nra.
Qed.

(** [x / y] of finite [f64]s with an exact result of at most 16 in
    magnitude is finite and rounded to nearest (as in [FastDiv.v]). *)
Local Lemma div_e :
  forall x y, is_finite x = true -> is_finite y = true -> B2R y <> 0 ->
  Rabs (B2R x / B2R y) <= 16 ->
  is_finite (div x y) = true /\ B2R (div x y) = RN (B2R x / B2R y).
Proof.
intros x y Fx Fy Hy H.
destruct (TwoProduct.RN_below_max _ (FastExpErr.small_le_max _ H)) as (Hlt & _).
generalize (@Bdiv_correct 53 1024 _ _ mode_NE x y Hy).
rewrite Rlt_bool_true by exact Hlt.
intros (HR & HF & _).
change (Bdiv mode_NE x y) with (div x y) in HR, HF.
rewrite Fx in HF. split; [exact HF | exact HR].
Qed.

Theorem fast_atan2_pos_correct :
  forall fma a b neg h l e err,
  is_finite a = true -> is_finite b = true -> 0 < B2R a -> 0 < B2R b ->
  DyadicAtan.fast_atan2_pos fma a b neg = Some (h, l, e, err) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= e <= 1022)%Z /\
  exists p, (55 <= p <= 105)%Z /\ B2R err = bpow radix2 (- p) /\
    Rabs (Ratan2 (B2R a) (if neg then - B2R b else B2R b) * bpow radix2 (- e) - (B2R h + B2R l))
      <= bpow radix2 (- p).
Proof.
intros fma a b neg h l e err Fa Fb Ha Hb H.
assert (Fz : is_finite zero = true) by reflexivity.
assert (Ez : B2R zero = 0) by reflexivity.
assert (B53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
unfold DyadicAtan.fast_atan2_pos in H. cbv zeta in H.
(* A [destruct] of [if gt a b then (b, a) else (a, b)] as typed here
   does not find that term in [H], so the term of the first [let '(n, d)
   := ..] is taken from [H]. Each [let '(x, y) := ..] is a [match] on a
   pair, reduced ([cbv beta iota]) after each [destruct], so that the
   next one finds its term. *)
lazymatch type of H with
| (match ?t with (_, _) => _ end) = _ => destruct t as (n, d) eqn:End
end.
cbv beta iota in H.
destruct (atan2_nd a b neg n d Fa Fb Ha Hb End) as (Fn & Fd & Hnd & Hoct).
rewrite Hoct.
destruct (DyadicAtan.split n) as (mn, en) eqn:Esn. cbv beta iota in H.
destruct (DyadicAtan.split d) as (md, ed) eqn:Esd. cbv beta iota in H.
destruct (atan2_split n d mn en md ed Fn Fd Hnd Esn Esd)
  as (Fmn & Fmd & Hmn & Hmd & Q & Hj & Hq01).
destruct (Fast.dd_div fma mn zero md zero) as (qh, ql) eqn:Ed. cbv beta iota in H.
destruct (quot_facts fma mn md qh ql Fmn Fmd Hmn Hmd Ed)
  as (Fqh & Fql & Rq & Hq & Hqh & Hql & Hr).
assert (Hpos : 0 < atan (B2R n / B2R d) <= 4 / 5) by (apply atan_pos_le; lra).
destruct (Z.leb_spec (-60) (en - ed)) as [Le | Lt]; cbv beta iota in H.
- (* [e >= -60]: the core at [n / d = (qh + ql) 2^e]. *)
  pose proof (scaled_input qh ql _ (en - ed) Fqh Fql Hq Hqh Hql (conj Le Hj)
    ltac:(rewrite <- Q; lra)) as S.
  cbv zeta in S. destruct S as (Fth & Ftl & Hth & Htl & Hin).
  rewrite <- Q in Hin.
  destruct (DyadicAtan.fast_atan_core fma (mul qh (DyadicExp.two_pow (en - ed)))
    (mul ql (DyadicExp.two_pow (en - ed)))) as [[rh rl]|] eqn:Ec; [|discriminate H].
  assert (Eo : DyadicAtan.octant (gt a b) neg rh rl = (h, l, e, err)) by congruence.
  destruct (fast_atan_core_correct fma _ _ rh rl Fth Ftl Hth Htl Ec) as (Frh & Frl & Rrh & Hc).
  pose proof (bpow_gt_0 radix2 (-61)) as P61.
  assert (Hc' : if gt a b || neg
    then Rabs (B2R rh + B2R rl - atan (B2R n / B2R d)) <= bpow radix2 (-73)
    else bpow radix2 (-1020) <= atan (B2R n / B2R d) /\
      Rabs (B2R rh + B2R rl - atan (B2R n / B2R d)) <= bpow radix2 (-73) * atan (B2R n / B2R d)).
  { destruct (gt a b || neg).
    - (* An absolute error ([atan_abs_err]). *)
      apply (atan_abs_err (B2R (mul qh (DyadicExp.two_pow (en - ed))) +
        B2R (mul ql (DyadicExp.two_pow (en - ed))))); [| |exact Hc].
      + rewrite B53 in Htl. apply Rabs_le_inv in Htl. lra.
      + apply Rle_trans with (1 := Hin).
        apply Rle_trans with (bpow radix2 (-96) * 1).
        * apply Rmult_le_compat_l; [apply bpow_ge_0 | lra].
        * rewrite Rmult_1_r. apply bpow_le. lia.
    - (* A relative error ([atan_rel_err]), with [n / d >= 2^-61]. *)
      split.
      + assert (E61 : bpow radix2 (-61) = / 2 * bpow radix2 (-60)).
        { replace (-61)%Z with (-1 + -60)%Z by lia. rewrite bpow_plus. reflexivity. }
        assert (E62 : bpow radix2 (-62) = / 2 * bpow radix2 (-61)).
        { replace (-62)%Z with (-1 + -61)%Z by lia. rewrite bpow_plus. reflexivity. }
        assert (L61 : bpow radix2 (-61) <= B2R n / B2R d).
        { rewrite Q, E61. apply Rmult_le_compat; [lra | apply bpow_ge_0 | lra |].
          apply bpow_le. exact Le. }
        assert (L1020 : bpow radix2 (-1020) <= bpow radix2 (-62)) by (apply bpow_le; lia).
        apply Rle_trans with (B2R n / B2R d / 2); [lra | apply atan_lower; lra].
      + apply (atan_rel_err (B2R (mul qh (DyadicExp.two_pow (en - ed))) +
          B2R (mul ql (DyadicExp.two_pow (en - ed))))); [lra | exact Hin | exact Hc]. }
  destruct (octant_correct (gt a b) neg rh rl (atan (B2R n / B2R d)) h l e err Frh Frl Rrh
    Hpos Hc' Eo) as (Fh & Fl & Rh & He & Herr & Hbo).
  split; [exact Fh|]. split; [exact Fl|]. split; [exact Rh|]. split; [lia|].
  exists 70%Z. split; [lia|]. split; [exact Herr | exact Hbo].
- (* [e < -60]: [n / d < 2^-60], and [atan (n / d)] is [n / d] within
     [(n / d)^3 / 3] ([atan_cubic]). *)
  assert (Hqs : B2R n / B2R d < bpow radix2 (-60)).
  { rewrite Q. apply Rlt_le_trans with (2 * bpow radix2 (en - ed)).
    - apply Rmult_lt_compat_r; [apply bpow_gt_0 | lra].
    - assert (bpow radix2 (en - ed) <= bpow radix2 (-61)) by (apply bpow_le; lia).
      assert (E60 : bpow radix2 (-60) = 2 * bpow radix2 (-61)).
      { replace (-60)%Z with (1 + -61)%Z by lia. rewrite bpow_plus. reflexivity. }
      lra. }
  pose proof (atan_cubic (B2R n / B2R d) ltac:(lra)) as Cub.
  assert (Hq3 : (B2R n / B2R d) ^ 3 <= bpow radix2 (-180)).
  { apply Rle_trans with (bpow radix2 (-60) ^ 3); [apply pow_incr; lra|].
    cbn [pow]. rewrite Rmult_1_r, <- !bpow_plus. apply bpow_le. lia. }
  destruct (gt a b || neg) eqn:Sw; cbv beta iota in H.
  + (* The octants of [π/2 +- atan] and [π - atan]: [RN (n / d)] within
       an absolute [2^-73]. *)
    assert (Eo : DyadicAtan.octant (gt a b) neg (div n d) zero = (h, l, e, err)) by congruence.
    destruct (div_e n d Fn Fd ltac:(apply Rgt_not_eq; lra) ltac:(rewrite Rabs_pos_eq by lra; lra)) as (Fq & Rqd).
    assert (Rrh : B2R (div n d) = RN (B2R (div n d) + B2R zero)).
    { rewrite Ez, Rplus_0_r. symmetry. apply round_generic; [typeclasses eauto |].
      apply generic_format_B2R. }
    assert (Hc' : if gt a b || neg
      then Rabs (B2R (div n d) + B2R zero - atan (B2R n / B2R d)) <= bpow radix2 (-73)
      else bpow radix2 (-1020) <= atan (B2R n / B2R d) /\
        Rabs (B2R (div n d) + B2R zero - atan (B2R n / B2R d))
          <= bpow radix2 (-73) * atan (B2R n / B2R d)).
    { rewrite Sw. cbv beta iota. rewrite Rqd, Ez, Rplus_0_r.
      pose proof (rn_err (B2R n / B2R d) (-113) ltac:(lia)
        ltac:(rewrite Rabs_pos_eq by lra; apply Rlt_le; exact Hqs)) as Rn.
      apply Rabs_le_inv in Rn.
      change (bpow radix2 (-113)) with (/ 10384593717069655257060992658440192) in Rn.
      change (bpow radix2 (-180))
        with (/ 1532495540865888858358347027150309183618739122183602176) in Hq3.
      change (bpow radix2 (-73)) with (/ 9444732965739290427392).
      apply Rabs_le. split; lra. }
    destruct (octant_correct (gt a b) neg (div n d) zero (atan (B2R n / B2R d)) h l e err
      Fq Fz Rrh Hpos Hc' Eo) as (Fh & Fl & Rh & He & Herr & Hbo).
    split; [exact Fh|]. split; [exact Fl|]. split; [exact Rh|]. split; [lia|].
    exists 70%Z. split; [lia|]. split; [exact Herr | exact Hbo].
  + (* The first octant: [qh + ql] times [2^e] by [normalize], with
       [atan (n / d) 2^-e] within [r (n / d)^2 / 3] of [r = mn / md]. *)
    apply Bool.orb_false_iff in Sw. destruct Sw as (Sw1 & Sw2).
    rewrite Sw1, Sw2. cbv beta iota.
    assert (Hqh2 : bpow radix2 (-1021) <= B2R qh < 2).
    { split; [|lra]. apply Rle_trans with (/ 2); [|lra].
      change (/ 2) with (bpow radix2 (-1)). apply bpow_le. lia. }
    destruct (Fast.normalize qh ql) as [[h' l'] k] eqn:En. cbv beta iota in H.
    pose proof (normalize_correct qh ql Fqh Fql Rq Hqh2) as N. rewrite En in N.
    cbv beta iota in N.
    destruct N as (Fh' & Fl' & Hk & Eh' & El' & Hkb & Rh').
    destruct (Z.ltb_spec (en - ed + k) (-1021)) as [Lk | Lk]; cbv beta iota in H;
      [discriminate H|].
    injection H as <- <- <- <-.
    split; [exact Fh'|]. split; [exact Fl'|]. split; [exact Rh'|]. split; [lia|].
    exists 70%Z. split; [lia|]. split; [exact lit_err70|].
    assert (Kk : (-1 <= k)%Z).
    { assert (L : bpow radix2 (-1) < bpow radix2 (k + 1)).
      { apply Rle_lt_trans with (B2R qh); [|exact (proj2 Hkb)].
        change (bpow radix2 (-1)) with (/ 2). lra. }
      apply lt_bpow in L. lia. }
    assert (K2 : bpow radix2 (- k) <= 2).
    { change 2 with (bpow radix2 1). apply bpow_le. lia. }
    rewrite Eh', El'.
    replace (- (en - ed + k))%Z with (- (en - ed) + - k)%Z by lia.
    rewrite bpow_plus.
    set (E := bpow radix2 (- (en - ed))).
    replace (atan (B2R n / B2R d) * (E * bpow radix2 (- k)) -
        (B2R qh * bpow radix2 (- k) + B2R ql * bpow radix2 (- k)))
      with ((atan (B2R n / B2R d) * E - (B2R qh + B2R ql)) * bpow radix2 (- k)) by ring.
    rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (- k))) by apply bpow_ge_0.
    assert (QE : B2R n / B2R d * E = B2R mn / B2R md).
    { unfold E. rewrite Q, Rmult_assoc, <- bpow_plus.
      replace (en - ed + - (en - ed))%Z with 0%Z by lia. exact (Rmult_1_r _). }
    assert (D : atan (B2R n / B2R d) * E - (B2R qh + B2R ql) =
      (B2R mn / B2R md - (B2R qh + B2R ql)) - (B2R n / B2R d - atan (B2R n / B2R d)) * E)
      by (rewrite <- QE; ring).
    assert (PE : 0 <= E) by apply bpow_ge_0.
    assert (C1 : 0 <= (B2R n / B2R d - atan (B2R n / B2R d)) * E <=
      B2R n / B2R d * (B2R n / B2R d) * (B2R mn / B2R md) / 3).
    { split; [apply Rmult_le_pos; lra|].
      rewrite <- QE.
      apply Rle_trans with ((B2R n / B2R d) ^ 3 / 3 * E).
      - apply Rmult_le_compat_r; lra.
      - (* [ring] of Rocq 9.1 fails on [/ 3], so [Rdiv] is unfolded first. *)
        apply Req_le. unfold Rdiv. ring. }
    assert (Q2 : B2R n / B2R d * (B2R n / B2R d) <= bpow radix2 (-120)).
    { replace (-120)%Z with (-60 + -60)%Z by lia. rewrite bpow_plus.
      apply Rmult_le_compat; lra. }
    assert (C2 : B2R n / B2R d * (B2R n / B2R d) * (B2R mn / B2R md) / 3 <=
      bpow radix2 (-120)).
    { pose proof (bpow_gt_0 radix2 (-120)).
      assert (M : B2R n / B2R d * (B2R n / B2R d) * (B2R mn / B2R md) <= bpow radix2 (-120) * 2).
      { apply Rmult_le_compat; [nra | lra | exact Q2 | lra]. }
      lra. }
    assert (A : Rabs (atan (B2R n / B2R d) * E - (B2R qh + B2R ql)) <= bpow radix2 (-96)).
    { rewrite D. apply Rabs_le_inv in Hq.
      change (bpow radix2 (-98)) with (/ 316912650057057350374175801344) in Hq.
      change (bpow radix2 (-120)) with (/ 1329227995784915872903807060280344576) in C2.
      change (bpow radix2 (-96)) with (/ 79228162514264337593543950336).
      apply Rabs_le. split; lra. }
    apply Rle_trans with (bpow radix2 (-96) * 2).
    { apply Rmult_le_compat; [apply Rabs_pos | apply bpow_ge_0 | exact A | exact K2]. }
    assert (F : bpow radix2 (-96) * 2 <= bpow radix2 (-70)).
    { change (bpow radix2 (-96)) with (/ 79228162514264337593543950336).
      change (bpow radix2 (-70)) with (/ 1180591620717411303424). lra. }
    exact F.
Qed.

Theorem fast_atan_pos_fma :
  forall t,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < bpow radix2 54 ->
  DyadicAtan.fast_atan_pos true t = DyadicAtan.fast_atan_pos false t.
Proof.
intros t Ft Ht.
destruct FastLogReduce.one_R as (F1 & E1).
assert (Fz : is_finite zero = true) by reflexivity.
assert (Ez : B2R zero = 0) by reflexivity.
pose proof (bpow_gt_0 radix2 (-27)) as P27.
unfold DyadicAtan.fast_atan_pos.
destruct (le t DyadicExp.one) eqn:Le.
- assert (Ht1 : B2R t <= 1).
  { rewrite <- E1. exact (ge_true DyadicExp.one t F1 Ft Le). }
  assert (Hth : bpow radix2 (-61) <= B2R t <= 129 / 128).
  { split; [|lra]. apply Rle_trans with (2 := proj1 Ht). apply bpow_le. lia. }
  assert (Htl : Rabs (B2R zero) <= bpow radix2 (-53) * B2R t).
  { rewrite Ez, Rabs_R0. apply Rmult_le_pos; [apply bpow_ge_0 | lra]. }
  rewrite (fast_atan_core_fma t zero Ft Fz Hth Htl). reflexivity.
- assert (Ht1 : 1 < B2R t).
  { rewrite <- E1. exact (ge_false DyadicExp.one t F1 Ft Le). }
  destruct (DyadicAtan.split t) as (m, k) eqn:Es.
  cbv beta iota zeta.
  destruct (Fast.dd_div false DyadicExp.one zero m zero) as (qh, ql) eqn:Ed.
  destruct (big_input false t m k qh ql Ft (conj Ht1 (proj2 Ht)) Es Ed) as (Fm & Hm & S).
  cbv zeta in S. destruct S as (Fth & Ftl & Hth & Htl & _).
  (* The quotient is the same with and without an FMA ([dd_div_fma]). *)
  assert (HN : bpow radix2 (-80) <= B2R DyadicExp.one <= 4).
  { rewrite E1. split; [apply (bpow_le radix2 (-80) 0); lia | lra]. }
  assert (HD : / 2 <= B2R m <= 4) by lra.
  rewrite (dd_div_fma DyadicExp.one zero m zero F1 Fz Fm Fz HN
    ltac:(rewrite Ez, Rabs_R0, E1; rewrite Rmult_1_r; apply bpow_ge_0) HD
    ltac:(rewrite Ez, Rabs_R0; apply Rmult_le_pos; [apply bpow_ge_0 | lra])), Ed.
  rewrite (fast_atan_core_fma _ _ Fth Ftl Hth Htl). reflexivity.
Qed.

Theorem fast_atan2_pos_fma :
  forall a b neg,
  is_finite a = true -> is_finite b = true -> 0 < B2R a -> 0 < B2R b ->
  DyadicAtan.fast_atan2_pos true a b neg = DyadicAtan.fast_atan2_pos false a b neg.
Proof.
intros a b neg Fa Fb Ha Hb.
assert (Fz : is_finite zero = true) by reflexivity.
assert (Ez : B2R zero = 0) by reflexivity.
unfold DyadicAtan.fast_atan2_pos. cbv zeta.
(* The pair [(n, d)] taken from the goal, and the [match]es on pairs
   reduced after each [destruct], as in [fast_atan2_pos_correct]. *)
lazymatch goal with
| |- (match ?t with (_, _) => _ end) = _ => destruct t as (n, d) eqn:End
end.
cbv beta iota.
destruct (atan2_nd a b neg n d Fa Fb Ha Hb End) as (Fn & Fd & Hnd & _).
destruct (DyadicAtan.split n) as (mn, en) eqn:Esn. cbv beta iota.
destruct (DyadicAtan.split d) as (md, ed) eqn:Esd. cbv beta iota.
destruct (atan2_split n d mn en md ed Fn Fd Hnd Esn Esd)
  as (Fmn & Fmd & Hmn & Hmd & Q & Hj & Hq).
(* The quotient is the same with and without an FMA ([dd_div_fma]). *)
assert (HN : bpow radix2 (-80) <= B2R mn <= 4).
{ split; [|lra]. apply Rle_trans with 1; [apply (bpow_le radix2 (-80) 0); lia | lra]. }
rewrite (dd_div_fma mn zero md zero Fmn Fz Fmd Fz HN
  ltac:(rewrite Ez, Rabs_R0; apply Rmult_le_pos; [apply bpow_ge_0 | lra]) ltac:(lra)
  ltac:(rewrite Ez, Rabs_R0; apply Rmult_le_pos; [apply bpow_ge_0 | lra])).
destruct (Fast.dd_div false mn zero md zero) as (qh, ql) eqn:Ed. cbv beta iota.
destruct (Z.leb_spec (-60) (en - ed)) as [Le | Lt]; cbv beta iota; [|reflexivity].
destruct (quot_facts false mn md qh ql Fmn Fmd Hmn Hmd Ed) as (Fqh & Fql & _ & Hd & Hqh & Hql & _).
pose proof (scaled_input qh ql _ (en - ed) Fqh Fql Hd Hqh Hql (conj Le Hj)
  ltac:(rewrite <- Q; lra)) as S.
cbv zeta in S. destruct S as (Fth & Ftl & Hth & Htl & _).
rewrite (fast_atan_core_fma _ _ Fth Ftl Hth Htl). reflexivity.
Qed.

(** ** The sign and the rounding *)

(** What [fast_atan_pos_correct] and [fast_atan2_pos_correct] prove of
    their result [o] for the real [r]. *)
Local Definition res_bound (r : R) (o : option (f64 * f64 * Z * f64)) : Prop :=
  forall h l e err, o = Some (h, l, e, err) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-1021 <= e <= 1022)%Z /\
  exists p, (55 <= p <= 105)%Z /\ B2R err = bpow radix2 (- p) /\
    Rabs (r * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (- p).

Local Lemma scale_back : forall y e, y = y * bpow radix2 (- e) * bpow radix2 e.
Proof.
intros y e. rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l.
change (bpow radix2 0) with 1. ring.
Qed.

(** The tests of [FastRoundErr.v] on the bound of [r], and for [s] the
    other direction and a negation, which rounds [- r]
    ([DyPown.rounds_odd]). *)
Local Lemma signed_dir :
  forall r o s up v,
  res_bound r o ->
  match o with
  | Some (h, l, e, err) =>
    match Fast.round_dir_err h l e err (xorb up s) with
    | Some w => Some (if s then opp w else w)
    | None => None
    end
  | None => None
  end = Some v ->
  rounds up (if s then - r else r) v.
Proof.
intros r o s up v B H.
destruct o as [[[[h l] e] err]|]; [|discriminate H].
destruct (Fast.round_dir_err h l e err (xorb up s)) as [w|] eqn:R; [|discriminate H].
injection H as <-.
destruct (B h l e err eq_refl) as (Fh & Fl & Eh & He & p & Hp & Herr & Hb).
assert (Hr : rounds (xorb up s) r w).
{ rewrite (scale_back r e).
  exact (round_dir_err_correct h l e err p _ w _ Fh Fl Eh He Hp Herr Hb R). }
destruct s.
- rewrite Bool.xorb_true_r in Hr. apply DyPown.rounds_odd. rewrite Ropp_involutive. exact Hr.
- rewrite Bool.xorb_false_r in Hr. exact Hr.
Qed.

Local Lemma signed_near :
  forall r o (s : bool) v,
  res_bound r o ->
  match o with
  | Some (h, l, e, err) =>
    match Fast.round_near_err h l e err with
    | Some w => Some (if s then opp w else w)
    | None => None
    end
  | None => None
  end = Some v ->
  near_round (if s then - r else r) v.
Proof.
intros r o s v B H.
destruct o as [[[[h l] e] err]|]; [|discriminate H].
destruct (Fast.round_near_err h l e err) as [w|] eqn:R; [|discriminate H].
injection H as <-.
destruct (B h l e err eq_refl) as (Fh & Fl & Eh & He & p & Hp & Herr & Hb).
assert (Hr : near_round r w).
{ rewrite (scale_back r e).
  exact (round_near_err_correct h l e err p w _ Fh Fl Eh He Hp Herr Hb R). }
destruct s; [exact (near_opp r w Hr) | exact Hr].
Qed.

(** [atan] is odd: for [x < 0], [atan x = - atan |x|]. [x = -0] is not
    below [0] and takes the branch of [x >= 0]. *)
Local Lemma atan_sign :
  forall x,
  (if lt x zero then - atan (Rabs (B2R x)) else atan (Rabs (B2R x))) = atan (B2R x).
Proof.
intros x. destruct (DyExp.lt_zero_spec x) as (N1 & N2).
destruct (lt x zero).
- rewrite Rabs_left1, atan_opp, Ropp_involutive by (apply N1; reflexivity). reflexivity.
- rewrite Rabs_pos_eq by (apply N2; reflexivity). reflexivity.
Qed.

(** [Ratan2 y x] from [|y|], [|x|] and the signs of [x] and [y]: [x] is
    [-|x|] where [lt x zero], and [Ratan2] is odd in [y] for [y <> 0]
    ([AtanIdent.Ratan2_opp_y]). *)
Local Lemma atan2_args :
  forall y x,
  B2R y <> 0 ->
  (if lt y zero
   then - Ratan2 (Rabs (B2R y)) (if lt x zero then - Rabs (B2R x) else Rabs (B2R x))
   else Ratan2 (Rabs (B2R y)) (if lt x zero then - Rabs (B2R x) else Rabs (B2R x)))
  = Ratan2 (B2R y) (B2R x).
Proof.
intros y x Hy.
assert (Ex : (if lt x zero then - Rabs (B2R x) else Rabs (B2R x)) = B2R x).
{ destruct (DyExp.lt_zero_spec x) as (N1 & N2). destruct (lt x zero).
  - rewrite Rabs_left1 by (apply N1; reflexivity). apply Ropp_involutive.
  - apply Rabs_pos_eq. apply N2. reflexivity. }
rewrite Ex. destruct (DyExp.lt_zero_spec y) as (N1 & N2). destruct (lt y zero).
- rewrite Rabs_left1 by (apply N1; reflexivity).
  rewrite (Ratan2_opp_y _ _ Hy). apply Ropp_involutive.
- rewrite Rabs_pos_eq by (apply N2; reflexivity). reflexivity.
Qed.

Local Lemma atan_res :
  forall fma x,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) < bpow radix2 54 ->
  res_bound (atan (Rabs (B2R x))) (DyadicAtan.fast_atan_pos fma (fabs x)).
Proof.
intros fma x Fx Hx h l e err E.
destruct (fabs_facts x Fx) as (Ft & Et & _).
rewrite <- Et. apply (fast_atan_pos_correct fma (fabs x)); [exact Ft | rewrite Et; exact Hx | exact E].
Qed.

Local Lemma atan2_res :
  forall fma y x,
  is_finite y = true -> is_finite x = true -> B2R y <> 0 -> B2R x <> 0 ->
  res_bound (Ratan2 (Rabs (B2R y)) (if lt x zero then - Rabs (B2R x) else Rabs (B2R x)))
    (DyadicAtan.fast_atan2_pos fma (fabs y) (fabs x) (lt x zero)).
Proof.
intros fma y x Fy Fx Hy Hx h l e err E.
destruct (fabs_facts y Fy) as (Fa & Ea & _). destruct (fabs_facts x Fx) as (Fb & Eb & _).
rewrite <- Ea, <- Eb.
apply (fast_atan2_pos_correct fma (fabs y) (fabs x) (lt x zero)); try assumption.
- rewrite Ea. apply Rabs_pos_lt. exact Hy.
- rewrite Eb. apply Rabs_pos_lt. exact Hx.
Qed.

(** ** Rounded toward -inf and +inf *)

Theorem fast_atan_dir_correct :
  forall fma x up v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) < bpow radix2 54 ->
  DyadicAtan.fast_atan_dir fma x up = Some v ->
  rounds up (atan (B2R x)) v.
Proof.
intros fma x up v Fx Hx H.
rewrite <- atan_sign.
exact (signed_dir _ _ (lt x zero) up v (atan_res fma x Fx Hx) H).
Qed.

Theorem fast_atan2_dir_correct :
  forall fma y x up v,
  is_finite y = true -> is_finite x = true -> B2R y <> 0 -> B2R x <> 0 ->
  DyadicAtan.fast_atan2_dir fma y x up = Some v ->
  rounds up (Ratan2 (B2R y) (B2R x)) v.
Proof.
intros fma y x up v Fy Fx Hy Hx H.
rewrite <- (atan2_args y x Hy).
exact (signed_dir _ _ (lt y zero) up v (atan2_res fma y x Fy Fx Hy Hx) H).
Qed.

(** ** Rounded to nearest *)

Theorem fast_atan_near_correct :
  forall fma x v,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) < bpow radix2 54 ->
  DyadicAtan.fast_atan_near fma x = Some v ->
  near_round (atan (B2R x)) v.
Proof.
intros fma x v Fx Hx H.
rewrite <- atan_sign.
exact (signed_near _ _ (lt x zero) v (atan_res fma x Fx Hx) H).
Qed.

Theorem fast_atan2_near_correct :
  forall fma y x v,
  is_finite y = true -> is_finite x = true -> B2R y <> 0 -> B2R x <> 0 ->
  DyadicAtan.fast_atan2_near fma y x = Some v ->
  near_round (Ratan2 (B2R y) (B2R x)) v.
Proof.
intros fma y x v Fy Fx Hy Hx H.
rewrite <- (atan2_args y x Hy).
exact (signed_near _ _ (lt y zero) v (atan2_res fma y x Fy Fx Hy Hx) H).
Qed.

(** ** With and without an FMA *)

Theorem fast_atan_dir_fma :
  forall x up,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) < bpow radix2 54 ->
  DyadicAtan.fast_atan_dir true x up = DyadicAtan.fast_atan_dir false x up.
Proof.
intros x up Fx Hx. destruct (fabs_facts x Fx) as (Ft & Et & _).
rewrite <- Et in Hx.
unfold DyadicAtan.fast_atan_dir. rewrite (fast_atan_pos_fma _ Ft Hx). reflexivity.
Qed.

Theorem fast_atan_near_fma :
  forall x,
  is_finite x = true -> bpow radix2 (-27) <= Rabs (B2R x) < bpow radix2 54 ->
  DyadicAtan.fast_atan_near true x = DyadicAtan.fast_atan_near false x.
Proof.
intros x Fx Hx. destruct (fabs_facts x Fx) as (Ft & Et & _).
rewrite <- Et in Hx.
unfold DyadicAtan.fast_atan_near. rewrite (fast_atan_pos_fma _ Ft Hx). reflexivity.
Qed.

Theorem fast_atan2_dir_fma :
  forall y x up,
  is_finite y = true -> is_finite x = true -> B2R y <> 0 -> B2R x <> 0 ->
  DyadicAtan.fast_atan2_dir true y x up = DyadicAtan.fast_atan2_dir false y x up.
Proof.
intros y x up Fy Fx Hy Hx.
destruct (fabs_facts y Fy) as (Fa & Ea & _). destruct (fabs_facts x Fx) as (Fb & Eb & _).
assert (Ha : 0 < B2R (fabs y)) by (rewrite Ea; apply Rabs_pos_lt; exact Hy).
assert (Hb : 0 < B2R (fabs x)) by (rewrite Eb; apply Rabs_pos_lt; exact Hx).
unfold DyadicAtan.fast_atan2_dir. rewrite (fast_atan2_pos_fma _ _ _ Fa Fb Ha Hb). reflexivity.
Qed.

Theorem fast_atan2_near_fma :
  forall y x,
  is_finite y = true -> is_finite x = true -> B2R y <> 0 -> B2R x <> 0 ->
  DyadicAtan.fast_atan2_near true y x = DyadicAtan.fast_atan2_near false y x.
Proof.
intros y x Fy Fx Hy Hx.
destruct (fabs_facts y Fy) as (Fa & Ea & _). destruct (fabs_facts x Fx) as (Fb & Eb & _).
assert (Ha : 0 < B2R (fabs y)) by (rewrite Ea; apply Rabs_pos_lt; exact Hy).
assert (Hb : 0 < B2R (fabs x)) by (rewrite Eb; apply Rabs_pos_lt; exact Hx).
unfold DyadicAtan.fast_atan2_near. rewrite (fast_atan2_pos_fma _ _ _ Fa Fb Ha Hb). reflexivity.
Qed.
