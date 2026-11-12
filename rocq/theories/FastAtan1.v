(** * The first stage of the fast path of atan

    [DyadicAtan.fast_atan1] of [Model.v] computes atan t for a
    double-double [t = th + tl] in [[2^-61, 129/128]] as
    [DyadicAtan.fast_atan_core] does, with the same [i], [c], [n] and [d]
    ([FastAtanCore.core_index], [core_num], [core_den]), but in plain
    [f64] past them: [u = n / d] by one division and the rest of the
    quotient from the remainder ([FastAtan1Div.atan1_div]), and atan u
    by the plain polynomial of [FastAtan1Poly.v]; for [64 th <= 1/2] the
    polynomial at [th] alone. Where it returns, it is within [2^-64] of
    atan t relatively ([fast_atan1_correct]); it returns [None] only where
    [0 <= |t - c| < 2^-80]. It returns the same with and without an FMA
    ([fast_atan1_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error Sterbenz.
From Inari Require Import Model Mpfr Encoding Elementary TwoSum TwoProduct DyDriver NearF64
  FastRound FastRoundErr FastDiv CancelLanes FastHypPos FastAtanTables FastAtanIdent
  FastAtanPoly FastAtanCore FastAtan1Poly FastAtan1Div.
From Inari Require FastExpErr FastExpReduce ConstTight.

Open Scope R_scope.

(** The [2^-64] relative error at [q'] near [q], as an absolute error at
    [q], as [FastAtanIdent.atan_abs_err] for the core's [2^-74]. *)
Lemma atan1_abs_err :
  forall q' q s,
  0 <= q' <= 129 / 128 -> Rabs (q' - q) <= bpow radix2 (-90) ->
  Rabs (s - atan q') <= bpow radix2 (-64) * atan q' ->
  Rabs (s - atan q) <= bpow radix2 (-64).
Proof.
intros q' q s Hq' Hd Hs.
(* [atan q' <= 4/5 + 1/128]: [atan_pos_le] up to 1, and above 1 [atan q'
   <= atan 1 + (q' - 1)] ([atan_lipschitz]). Then [|s - atan q| <= 2^-64
   atan q' + |q' - q| <= 0.81 2^-64 + 2^-90 <= 2^-64]. *)
assert (Hu : atan q' <= 4 / 5 + / 128).
{ destruct (Rle_lt_dec q' 1) as [H1 | H1].
  - destruct (Rle_lt_or_eq_dec 0 q' (proj1 Hq')) as [H0 | H0].
    + pose proof (atan_pos_le q' ltac:(lra)) as A. lra.
    + rewrite <- H0, atan_0. lra.
  - pose proof (atan_pos_le 1 ltac:(lra)) as A.
    pose proof (atan_lipschitz q' 1) as L.
    rewrite (Rabs_pos_eq (q' - 1)) in L by lra.
    apply Rabs_le_inv in L. lra. }
assert (Hl : Rabs (atan q' - atan q) <= bpow radix2 (-90)).
{ eapply Rle_trans; [apply atan_lipschitz | exact Hd]. }
assert (E64 : bpow radix2 (-64) = / 18446744073709551616) by reflexivity.
assert (E90 : bpow radix2 (-90) = / 1237940039285380274899124224) by reflexivity.
rewrite E64 in Hs |- *. rewrite E90 in Hl.
apply Rabs_le_inv in Hs. apply Rabs_le_inv in Hl.
apply Rabs_le. split; lra.
Qed.

(** The same, as a relative error at [q], as [FastAtanIdent.atan_rel_err]. *)
Lemma atan1_rel_err :
  forall q' q s,
  0 < q <= 2 -> Rabs (q' - q) <= bpow radix2 (-96) * q ->
  Rabs (s - atan q') <= bpow radix2 (-64) * atan q' ->
  Rabs (s - atan q) <= (bpow radix2 (-64) + bpow radix2 (-84)) * atan q.
Proof.
intros q' q s Hq Hd Hs.
(* [|s - atan q| <= 2^-64 atan q' + |atan q' - atan q|], with [atan q' <=
   atan q + 2^-96 q] and [|atan q' - atan q| <= 2^-96 q]; then [q <= 2
   atan q] makes the sum at most [(2^-64 + 2^-159 + 2^-95) atan q]. *)
assert (Hlo : q / 2 <= atan q) by (apply atan_lower; lra).
assert (Hl : Rabs (atan q' - atan q) <= bpow radix2 (-96) * q).
{ eapply Rle_trans; [apply atan_lipschitz | exact Hd]. }
assert (E64 : bpow radix2 (-64) = / 18446744073709551616) by reflexivity.
assert (E84 : bpow radix2 (-84) = / 19342813113834066795298816) by reflexivity.
assert (E96 : bpow radix2 (-96) = / 79228162514264337593543950336) by reflexivity.
rewrite E64 in Hs |- *. rewrite E84. rewrite E96 in Hl.
apply Rabs_le_inv in Hs. apply Rabs_le_inv in Hl.
apply Rabs_le. split; lra.
Qed.

(** ** Helpers *)

(** [poly9 x] is the term of [fast_atan1] past [cbv zeta]. *)
Local Lemma poly9_fold :
  forall x, mul (mul x (mul x x)) (sub (from_bits (fst DyadicAtan.A3))
    (mul (mul x x) (sub (from_bits DyadicAtan.A5) (mul (mul x x) (sub (from_bits DyadicAtan.A7)
      (mul (mul x x) (from_bits DyadicAtan.A9))))))) = poly9 x.
Proof. reflexivity. Qed.

(** atan b - atan a is b - a within [|b - a| M^2] for [|a|, |b| <= M]: by
    the mean value theorem it is [(b - a) / (1 + ξ^2)] for some ξ between
    a and b, and [1 - 1 / (1 + ξ^2) <= ξ^2]. *)
Local Lemma atan_mvt :
  forall a b M, Rabs a <= M -> Rabs b <= M ->
  Rabs (atan b - atan a - (b - a)) <= Rabs (b - a) * (M * M).
Proof.
assert (key : forall x y M, x < y -> Rabs x <= M -> Rabs y <= M ->
  Rabs (atan y - atan x - (y - x)) <= Rabs (y - x) * (M * M)).
{ intros x y M Hxy Hx Hy.
  destruct (MVT_cor2 atan (fun c => / (1 + c ^ 2)) x y Hxy) as [c [Hc Hcb]].
  { intros c _. apply derivable_pt_lim_atan. }
  rewrite Hc.
  apply Rabs_le_inv in Hx. apply Rabs_le_inv in Hy.
  assert (Hc2 : c ^ 2 <= M * M).
  { assert (0 <= M - c) by lra. assert (0 <= M + c) by lra. nra. }
  pose proof (pow2_ge_0 c) as Hc0.
  set (k := / (1 + c ^ 2)) in *.
  assert (Hk : k * (1 + c ^ 2) = 1) by (unfold k; field; lra).
  assert (Hk0 : 0 < k) by (unfold k; apply Rinv_0_lt_compat; lra).
  assert (Hkc : 0 <= k * c ^ 2) by (apply Rmult_le_pos; lra).
  assert (Hk1 : k * c ^ 2 <= c ^ 2).
  { assert (k <= 1) by nra. nra. }
  replace (k * (y - x) - (y - x)) with (- (k * c ^ 2) * (y - x)) by nra.
  rewrite Rabs_mult, Rabs_Ropp, (Rabs_pos_eq (k * c ^ 2)) by exact Hkc.
  rewrite Rmult_comm. apply Rmult_le_compat_l; [apply Rabs_pos | lra]. }
intros a b M Ha Hb.
destruct (Rtotal_order a b) as [H | [H | H]].
- apply key; assumption.
- subst b. replace (atan a - atan a - (a - a)) with 0 by ring.
  replace (a - a) with 0 by ring. rewrite Rabs_R0. lra.
- replace (atan b - atan a - (b - a)) with (- (atan a - atan b - (a - b))) by ring.
  rewrite Rabs_Ropp, (Rabs_minus_sym b a). apply key; assumption.
Qed.

(** The final sums of [fast_atan1]: [gh + uh] by [fast_two_sum], exact as
    [|uh| <= gh], then the three roundings of the low parts, each of a sum
    of about [2^-22], and the last [fast_two_sum], exact as that sum is
    below [sh]. *)
Local Lemma fin1 :
  forall gh gl uh ul m sh s1 ah al,
  is_finite gh = true -> is_finite gl = true -> is_finite uh = true -> is_finite ul = true ->
  is_finite m = true ->
  / 128 <= B2R gh <= 4 / 5 -> Rabs (B2R gl) <= bpow radix2 (-53) * B2R gh ->
  Rabs (B2R uh) <= / 128 -> Rabs (B2R ul) <= bpow radix2 (-58) ->
  Rabs (B2R m) <= bpow radix2 (-22) -> / 512 <= B2R gh + B2R uh ->
  Fast.fast_two_sum gh uh = (sh, s1) ->
  Fast.fast_two_sum sh (add s1 (add gl (sub ul m))) = (ah, al) ->
  is_finite ah = true /\ is_finite al = true /\ B2R ah = RN (B2R ah + B2R al) /\
  Rabs (B2R ah + B2R al - (B2R gh + B2R gl + B2R uh + (B2R ul - B2R m))) <= bpow radix2 (-73).
Proof.
intros gh gl uh ul m sh s1 ah al Fgh Fgl Fuh Ful Fm Hgh Hgl Huh Hul Hm Hsum E1 E2.
pose proof (bpow_gt_0 radix2 (-1075)) as W0.
assert (W1 : bpow radix2 (-1075) <=
  / 1606938044258990275541962092341162602522202993782792835301376).
{ apply Rle_trans with (bpow radix2 (-200)); [apply bpow_le; lia|].
  change (bpow radix2 (-200))
    with (/ 1606938044258990275541962092341162602522202993782792835301376). lra. }
change (bpow radix2 (-53)) with (/ 9007199254740992) in Hgl.
change (bpow radix2 (-58)) with (/ 288230376151711744) in Hul.
change (bpow radix2 (-22)) with (/ 4194304) in Hm.
change (bpow radix2 (-73)) with (/ 9444732965739290427392).
pose proof (Rabs_le_inv _ _ Hgl) as Hgl'.
pose proof (Rabs_le_inv _ _ Hul) as Hul'.
pose proof (Rabs_le_inv _ _ Hm) as Hm'.
pose proof (Rabs_le_inv _ _ Huh) as Huh'.
(* [|uh| <= 2^-7 <= gh], so the first [fast_two_sum] is exact. *)
destruct (lc_fts gh uh sh s1 Fgh Fuh) as (Fsh & Fs1 & Rsh & Es).
{ left. rewrite (Rabs_pos_eq (B2R gh)) by lra. lra. }
{ apply Rabs_le. lra. }
{ exact E1. }
(* [s1] is the rounding error of [gh + uh]. *)
pose proof (FastExpErr.rn_err (B2R gh + B2R uh)) as Es1.
rewrite <- Rsh in Es1.
replace (B2R sh - (B2R gh + B2R uh)) with (- B2R s1) in Es1 by lra.
rewrite Rabs_Ropp, (Rabs_pos_eq (B2R gh + B2R uh)) in Es1 by lra.
change (bpow radix2 (-53)) with (/ 9007199254740992) in Es1.
pose proof (Rabs_le_inv _ _ Es1) as Es1'.
(* [x1 = RN (ul - m)], [|ul - m| <= 1.01 2^-22]. *)
assert (HK1 : Rabs (B2R ul - B2R m) <= / 4194304 * (101 / 100)) by (apply Rabs_le; lra).
destruct (FastExpErr.sub_k ul m _ Ful Fm HK1 ltac:(lra)) as (Fx1 & _ & Ex1).
set (x1 := sub ul m) in *.
change (bpow radix2 (-53)) with (/ 9007199254740992) in Ex1.
pose proof (Rabs_le_inv _ _ Ex1) as Ex1'.
(* [x2 = RN (gl + x1)], [|gl + x1| <= 1.02 2^-22]. *)
assert (HK2 : Rabs (B2R gl + B2R x1) <= / 4194304 * (102 / 100)) by (apply Rabs_le; lra).
destruct (FastExpErr.add_k gl x1 _ Fgl Fx1 HK2 ltac:(lra)) as (Fx2 & _ & Ex2).
set (x2 := add gl x1) in *.
change (bpow radix2 (-53)) with (/ 9007199254740992) in Ex2.
pose proof (Rabs_le_inv _ _ Ex2) as Ex2'.
(* [x3 = RN (s1 + x2)], [|s1 + x2| <= 1.03 2^-22]. *)
assert (HK3 : Rabs (B2R s1 + B2R x2) <= / 4194304 * (103 / 100)) by (apply Rabs_le; lra).
destruct (FastExpErr.add_k s1 x2 _ Fs1 Fx2 HK3 ltac:(lra)) as (Fx3 & _ & Ex3).
set (x3 := add s1 x2) in *.
change (bpow radix2 (-53)) with (/ 9007199254740992) in Ex3.
pose proof (Rabs_le_inv _ _ Ex3) as Ex3'.
(* The second [fast_two_sum] is exact: [|x3| <= 2^-21 <= sh]. *)
destruct (lc_fts sh x3 ah al Fsh Fx3) as (Fah & Fal & Rah & Ea).
{ left. rewrite (Rabs_pos_eq (B2R sh)) by lra. apply Rabs_le. lra. }
{ apply Rabs_le. lra. }
{ exact E2. }
do 2 (split; [assumption|]).
split; [rewrite Ea; exact Rah|].
(* The error: [x3 - (s1 + x2) + (x2 - (gl + x1)) + (x1 - (ul - m))], at
   most 3.06 2^-75 + 3 2^-1075. *)
rewrite Ea. apply Rabs_le. lra.
Qed.

(** ** The theorems *)

Theorem fast_atan1_correct :
  forall fma th tl ah al,
  is_finite th = true -> is_finite tl = true ->
  bpow radix2 (-61) <= B2R th <= 129 / 128 -> Rabs (B2R tl) <= bpow radix2 (-53) * B2R th ->
  DyadicAtan.fast_atan1 fma th tl = Some (ah, al) ->
  is_finite ah = true /\ is_finite al = true /\ B2R ah = RN (B2R ah + B2R al) /\
  Rabs (B2R ah + B2R al - atan (B2R th + B2R tl)) <= bpow radix2 (-64) * atan (B2R th + B2R tl).
Proof.
intros fma th tl ah al Fth Ftl Hth Htl H.
pose proof (core_index th Fth Hth) as HI. cbv zeta in HI.
cbv beta zeta delta [DyadicAtan.fast_atan1] in H.
set (kf := sub (add (mul th (from_bits 0x4050000000000000)) DyadicExp.shifter)
  DyadicExp.shifter) in H, HI.
set (i := DyadicExp.to_i64 kf) in H, HI.
set (c := mul kf (from_bits 0x3f90000000000000)) in H, HI.
destruct HI as (Hi & Hidx & Fc & Ec & Hi0).
pose proof (bpow_gt_0 radix2 (-61)) as P61.
(* [t] is positive, and atan t >= t / 2. *)
assert (Htl' : Rabs (B2R tl) <= / 9007199254740992 * B2R th)
  by (change (bpow radix2 (-53)) with (/ 9007199254740992) in Htl; exact Htl).
assert (Ht : 0 < B2R th + B2R tl <= 2) by (apply Rabs_le_inv in Htl'; lra).
assert (Hat : (B2R th + B2R tl) / 2 <= atan (B2R th + B2R tl)) by (apply atan_lower; lra).
pose proof (bpow_gt_0 radix2 (-1075)) as W0.
assert (W1 : bpow radix2 (-1075) <=
  / 1606938044258990275541962092341162602522202993782792835301376).
{ apply Rle_trans with (bpow radix2 (-200)); [apply bpow_le; lia|].
  change (bpow radix2 (-200))
    with (/ 1606938044258990275541962092341162602522202993782792835301376). lra. }
change (bpow radix2 (-64)) with (/ 18446744073709551616).
destruct (Z.eqb_spec i 0) as [I0|I0].
- (* [64 th <= 1/2]: [th - poly9 th + tl], with [tl - poly9 th] rounded. *)
  specialize (Hi0 I0).
  assert (R1 : bpow radix2 (-82) <= Rabs (B2R th) <= bpow radix2 (-7)).
  { rewrite Rabs_pos_eq by lra. split; [|exact Hi0].
    apply Rle_trans with (bpow radix2 (-61)); [apply bpow_le; lia | lra]. }
  change (bpow radix2 (-7)) with (/ 128) in Hi0.
  change (bpow radix2 (-61)) with (/ 2305843009213693952) in Hth.
  pose proof (poly9_err th Fth R1) as P.
  rewrite poly9_fold in H.
  set (m := poly9 th) in H, P.
  destruct P as (Fm & Hm & Pm).
  apply (f_equal (fun o => match o with Some v => v | None => (ah, al) end)) in H.
  cbv beta iota in H.
  rewrite (Rabs_pos_eq (B2R th)) in Hm, Pm by lra.
  change (bpow radix2 (-15)) with (/ 32768) in Hm.
  pose proof (Rabs_le_inv _ _ Htl') as Htl''.
  pose proof (Rabs_le_inv _ _ Hm) as Hm'.
  (* [r = RN (tl - m)], [|tl - m| <= (2^-53 + 2^-15) th]. *)
  assert (K : Rabs (B2R tl - B2R m) <= (/ 9007199254740992 + / 32768) * B2R th)
    by (apply Rabs_le; lra).
  destruct (FastExpErr.sub_k tl m _ Ftl Fm K ltac:(lra)) as (Fr & _ & Er).
  set (r := sub tl m) in *.
  change (bpow radix2 (-53)) with (/ 9007199254740992) in Er.
  pose proof (Rabs_le_inv _ _ Er) as Er'.
  (* [|r| <= th], so the [fast_two_sum] is exact. *)
  destruct (lc_fts th r ah al Fth Fr) as (Fah & Fal & Rah & Ea).
  { left. rewrite (Rabs_pos_eq (B2R th)) by lra. apply Rabs_le. lra. }
  { apply Rabs_le. lra. }
  { exact H. }
  do 2 (split; [assumption|]).
  split; [rewrite Ea; exact Rah|].
  (* [poly9]'s error: [2^-52 th^3 <= 2^-66 th]. *)
  assert (T3 : B2R th ^ 3 <= / 16384 * B2R th).
  { assert (B2R th * B2R th <= / 16384) by nra. nra. }
  assert (Pm' : Rabs (B2R th - B2R m - atan (B2R th)) <= / 73786976294838206464 * B2R th).
  { eapply Rle_trans; [exact Pm|].
    change (bpow radix2 (-52)) with (/ 4503599627370496). lra. }
  (* atan (th + tl) - atan th is tl within [|tl| (2^-7 + 2^-60)^2]. *)
  pose proof (atan_mvt (B2R th) (B2R th + B2R tl) (/ 128 + / 1152921504606846976)) as Mv.
  replace (B2R th + B2R tl - B2R th) with (B2R tl) in Mv by ring.
  specialize (Mv ltac:(apply Rabs_le; lra) ltac:(apply Rabs_le; lra)).
  pose proof (Rabs_le_inv _ _ Mv) as Mv'.
  pose proof (Rabs_le_inv _ _ Pm') as Pm''.
  pose proof (Rabs_pos (B2R tl)) as Ptl.
  (* The sum: [(2^-68 + 2^-66 + 2^-67 (1 + 2^-52)) th + 2^-1075 <= 2^-65 t]. *)
  rewrite Ea. apply Rabs_le. split; lra.
- (* The table and the reduction. *)
  assert (I1 : (1 <= i <= 64)%Z) by lia.
  assert (Hic : 1 <= IZR i <= 64) by (split; apply IZR_le; lia).
  assert (Hc : / 64 <= B2R c <= 1) by (rewrite Ec; lra).
  destruct (core_range th tl c Hth Htl Hc) as (Hth' & HN & HD).
  { rewrite Ec. replace (64 * (IZR i / 64)) with (IZR i) by field. exact Hidx. }
  pose proof (fast_atan_table_correct i I1) as T.
  revert H T. destruct (DyadicAtan.atbl i) as (gh, gl). intros H T.
  destruct T as (Fgh & Fgl & Hgh & Hgl & Eg).
  rewrite <- Ec in Eg.
  change (bpow radix2 (-7)) with (/ 128) in Hgh.
  revert H. destruct (Fast.fast_two_sum (sub th c) tl) as (nh, nl) eqn:EN. intros H.
  destruct (core_num th tl c i nh nl Fth Ftl Fc Hth' Htl I1 Hidx Ec EN)
    as (Fnh & Fnl & Rnh & Enh & _).
  revert H. destruct (Model.lt (fabs nh) DyadicAtan.two_m80) eqn:E80; intros H;
    [discriminate H|].
  destruct (core_nh (B2R th + B2R tl - B2R c) nh nl Fnh Rnh Enh) as (Hnh & Hnl);
    [|exact E80|].
  { apply Rle_trans with (1 := HN).
    change (bpow radix2 (-52)) with (/ 4503599627370496). lra. }
  revert H. destruct (Fast.two_sum DyadicExp.one (mul th c)) as (s, s0) eqn:ES. intros H.
  revert H.
  destruct (Fast.fast_two_sum s
    (add s0 (add (Generic.two_prod_err fma th c (mul th c)) (mul tl c)))) as (dh, dl) eqn:ED.
  intros H.
  destruct (core_den fma th tl c s s0 dh dl Fth Ftl Fc Hth' Htl Hc ES ED)
    as (Fdh & Fdl & Hdh & Hdl & Ed).
  set (D := 1 + (B2R th + B2R tl) * B2R c) in *.
  rewrite <- Enh in HN.
  pose proof (atan1_div fma nh nl dh dl D Fnh Fnl Fdh Fdl Hnh Hnl HN Hdh Hdl HD Ed) as A.
  cbv zeta in A.
  set (uh := div nh dh) in H, A.
  set (ul := div (sub (add (sub (sub nh (mul uh dh)) (Generic.two_prod_err fma uh dh (mul uh dh)))
    nl) (mul uh dl)) dh) in H, A.
  destruct A as (Fuh & Ful & Huh & Hul & Hu7 & Eu).
  pose proof (poly9_err uh Fuh Huh) as P.
  rewrite poly9_fold in H.
  set (m := poly9 uh) in H, P.
  destruct P as (Fm & Hm & Pm).
  revert H. destruct (Fast.fast_two_sum gh uh) as (sh, s1) eqn:ES1. intros H.
  apply (f_equal (fun o => match o with Some v => v | None => (ah, al) end)) in H.
  cbv beta iota in H.
  (* The identity atan t = atan c + atan q and the error terms. *)
  pose proof (atan_sub_table (B2R th + B2R tl) (B2R c)) as Id.
  rewrite <- Enh in Id. fold D in Id.
  specialize (Id ltac:(lra) ltac:(lra)).
  change (bpow radix2 (-7)) with (/ 128) in Huh, Hu7.
  change (bpow radix2 (-16)) with (/ 65536) in Hu7.
  change (bpow radix2 (-52)) with (/ 4503599627370496) in Hul, HN.
  change (bpow radix2 (-15)) with (/ 32768) in Hm.
  change (bpow radix2 (-97)) with (/ 158456325028528675187087900672) in Eu.
  change (bpow radix2 (-53)) with (/ 9007199254740992) in Hgl.
  change (bpow radix2 (-104)) with (/ 20282409603651670423947251286016) in Eg.
  (* [poly9]'s error: [2^-52 |uh|^3 <= 2^-73]. *)
  assert (U3 : Rabs (B2R uh) ^ 3 <= / 2097152).
  { replace (/ 2097152) with ((/ 128) ^ 3) by field.
    apply pow_incr. split; [apply Rabs_pos | lra]. }
  assert (Pm' : Rabs (B2R uh - B2R m - atan (B2R uh)) <= / 9444732965739290427392).
  { eapply Rle_trans; [exact Pm|].
    apply Rle_trans with (bpow radix2 (-52) * / 2097152).
    - apply Rmult_le_compat_l; [apply bpow_ge_0 | exact U3].
    - change (bpow radix2 (-52)) with (/ 4503599627370496). lra. }
  (* atan (uh + ul) - atan uh is ul within [|ul| 2^-14 <= 13/8 2^-73]. *)
  assert (Hul7 : Rabs (B2R ul) <= 13 / 8 * / 576460752303423488) by lra.
  pose proof (atan_mvt (B2R uh) (B2R uh + B2R ul) (/ 128)) as Mv.
  replace (B2R uh + B2R ul - B2R uh) with (B2R ul) in Mv by ring.
  specialize (Mv ltac:(lra) ltac:(lra)).
  set (u := B2R uh + B2R ul) in *.
  set (q := (B2R nh + B2R nl) / D) in *.
  set (t := B2R th + B2R tl) in *.
  pose proof (atan_lipschitz u q) as L.
  (* atan t >= atan (1/129) >= 1/129 - 1/(3 129^3) ([atan_cubic]). *)
  assert (Ht2 : / 129 <= t) by (unfold t; apply Rabs_le_inv in Htl'; lra).
  assert (At : / 129 - / 6440067 <= atan t).
  { pose proof (atan_cubic (/ 129) ltac:(lra)) as C.
    replace ((/ 129) ^ 3 / 3) with (/ 6440067) in C by field.
    destruct (Rle_lt_or_eq_dec (/ 129) t Ht2) as [Lt | Eq].
    - pose proof (atan_increasing _ _ Lt). lra.
    - rewrite <- Eq. lra. }
  pose proof (Rabs_le_inv _ _ Pm') as Pm''.
  pose proof (Rabs_le_inv _ _ Mv) as Mv'.
  pose proof (Rabs_le_inv _ _ Eu) as Eu'.
  pose proof (Rabs_le_inv _ _ Eg) as Eg'.
  pose proof (Rabs_le_inv _ _ Hgl) as Hgl'.
  pose proof (Rabs_le_inv _ _ L) as L'.
  pose proof (Rabs_le_inv _ _ Hm) as Hm'.
  pose proof (Rabs_le_inv _ _ Hul7) as Hul7'.
  pose proof (Rabs_le_inv _ _ (proj2 Huh)) as Huh'.
  pose proof (Rabs_pos (B2R nh + B2R nl)) as PN.
  pose proof (Rabs_pos (u - q)) as Puq.
  assert (Hm22 : Rabs (B2R m) <= bpow radix2 (-22)).
  { change (bpow radix2 (-22)) with (/ 4194304). lra. }
  (* [gh + uh] is atan t up to errors far below atan t / 2. *)
  assert (Hsum : / 512 <= B2R gh + B2R uh) by lra.
  destruct (fin1 gh gl uh ul m sh s1 ah al Fgh Fgl Fuh Ful Fm Hgh) as (Fah & Fal & Rah & Ea);
    [ change (bpow radix2 (-53)) with (/ 9007199254740992); exact Hgl | lra
    | change (bpow radix2 (-58)) with (/ 288230376151711744); lra
    | exact Hm22 | exact Hsum | exact ES1 | exact H |].
  do 3 (split; [assumption|]).
  change (bpow radix2 (-73)) with (/ 9444732965739290427392) in Ea.
  pose proof (Rabs_le_inv _ _ Ea) as Ea'.
  (* The sum: (2 + 13/8) 2^-73 + 2^-104 + 2^-97 |n| <= 3.96 2^-73 <= 2^-64 atan t. *)
  apply Rabs_le. lra.
Qed.

Theorem fast_atan1_fma :
  forall th tl,
  is_finite th = true -> is_finite tl = true ->
  bpow radix2 (-61) <= B2R th <= 129 / 128 -> Rabs (B2R tl) <= bpow radix2 (-53) * B2R th ->
  DyadicAtan.fast_atan1 true th tl = DyadicAtan.fast_atan1 false th tl.
Proof.
intros th tl Fth Ftl Hth Htl.
pose proof (core_index th Fth Hth) as HI. cbv zeta in HI.
cbv beta zeta delta [DyadicAtan.fast_atan1].
set (kf := sub (add (mul th (from_bits 0x4050000000000000)) DyadicExp.shifter)
  DyadicExp.shifter) in HI |- *.
set (i := DyadicExp.to_i64 kf) in HI |- *.
set (c := mul kf (from_bits 0x3f90000000000000)) in HI |- *.
destruct HI as (Hi & Hidx & Fc & Ec & Hi0).
(* The polynomial at [th] alone takes no product error. *)
destruct (Z.eqb i 0) eqn:I0; [reflexivity|].
apply Z.eqb_neq in I0.
assert (I1 : (1 <= i <= 64)%Z) by lia.
assert (Hic : 1 <= IZR i <= 64) by (split; apply IZR_le; lia).
assert (Hc : / 64 <= B2R c <= 1) by (rewrite Ec; lra).
destruct (core_range th tl c Hth Htl Hc) as (Hth' & HN & HD).
{ rewrite Ec. replace (64 * (IZR i / 64)) with (IZR i) by field. exact Hidx. }
destruct (DyadicAtan.atbl i) as (gh, gl).
destruct (Fast.fast_two_sum (sub th c) tl) as (nh, nl) eqn:EN.
destruct (core_num th tl c i nh nl Fth Ftl Fc Hth' Htl I1 Hidx Ec EN)
  as (Fnh & Fnl & Rnh & Enh & _).
destruct (Model.lt (fabs nh) DyadicAtan.two_m80) eqn:E80; [reflexivity|].
destruct (core_nh (B2R th + B2R tl - B2R c) nh nl Fnh Rnh Enh) as (Hnh & Hnl);
  [|exact E80|].
{ apply Rle_trans with (1 := HN).
  change (bpow radix2 (-52)) with (/ 4503599627370496). lra. }
(* [th c] is exact either way, so its error is the same [f64]. *)
rewrite (two_prod_err_fma_eq th c Fth Fc (core_exact true th c Fth Fc Hth' Hc)
  (core_exact false th c Fth Fc Hth' Hc)).
destruct (Fast.two_sum DyadicExp.one (mul th c)) as (s, s0) eqn:ES.
destruct (Fast.fast_two_sum s
  (add s0 (add (Generic.two_prod_err false th c (mul th c)) (mul tl c)))) as (dh, dl) eqn:ED.
destruct (core_den false th tl c s s0 dh dl Fth Ftl Fc Hth' Htl Hc ES ED)
  as (Fdh & Fdl & Hdh & Hdl & _).
(* So is the error of [uh dh]. *)
rewrite (atan1_div_fma nh dh Fnh Fdh Hnh Hdh). reflexivity.
Qed.
