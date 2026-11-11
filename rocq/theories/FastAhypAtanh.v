(** * The fast path of [atanh] before the rounding, for [2^-8 <= t < 1]

    [DyadicLog.fast_atanh_pos] of [Model.v] computes
    [2 atanh t = ln((1 + t) / (1 - t))], with [1 - t] and [1 + t] exact
    as double-doubles, as [-j ln 2 + ln q] for [q = (1 + t) / ((1 - t) 2^-j)]
    by [Fast.dd_div] ([FastDiv.v]),
    where [Fast.normalize] ([FastRoundErr.v]) scales [1 - t] into [[1, 2)]
    exactly ([fast_ln_dd_correct] with [e0 = -j]). The exponent [k - 1]
    halves the result. [fast_atanh_pos_correct] shows that the result is
    within [2^-68] of [atanh t 2^-k], with [1/2 < |h| < 2]. *)

From Stdlib Require Import ZArith Reals Lra Lia Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error Sterbenz.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct FastRound FastRoundErr
  FastDiv FastDdSqrt FastLogTables FastLogPoly FastLogCore FastLogNorm FastLogFin FastLogDd
  FastExpErr.

Open Scope R_scope.

Local Ltac num := cbn [bpow radix_val radix2] in *; lra.

(** ** Helpers *)

(** RN keeps a number on the same side of a power of 2. *)
Local Lemma rn_ge_bpow :
  forall e y, (-1073 <= e)%Z -> bpow radix2 e <= y -> bpow radix2 e <= RN y.
Proof.
intros e y He Hy. apply round_ge_generic; [typeclasses eauto | typeclasses eauto | | exact Hy].
apply generic_format_bpow. unfold FLT_exp. lia.
Qed.

Local Lemma rn_le_bpow :
  forall e y, (-1073 <= e)%Z -> y <= bpow radix2 e -> RN y <= bpow radix2 e.
Proof.
intros e y He Hy. apply round_le_generic; [typeclasses eauto | typeclasses eauto | | exact Hy].
apply generic_format_bpow. unfold FLT_exp. lia.
Qed.

(** A normal [h = RN x] is within [2^-53 |h|] of [x]: the error is at
    most half an ulp of [h] (Flocq [error_le_half_ulp_round]), and
    [ulp h <= 2^-52 |h|] ([ulp_FLT_le]). *)
Local Lemma rn_low :
  forall h x, h = RN x -> bpow radix2 (-1022) <= Rabs h ->
  Rabs (x - h) <= bpow radix2 (-53) * Rabs h.
Proof.
intros h x Eh Hh.
assert (E : Rabs (RN x - x) <= / 2 * ulp radix2 fexp64 (RN x))
  by (apply error_le_half_ulp_round; typeclasses eauto).
rewrite <- Eh in E.
pose proof (ulp_FLT_le radix2 (-1074) 53 h Hh) as U. change (1 - 53)%Z with (-52)%Z in U.
rewrite Rabs_minus_sym.
apply Rle_trans with (/ 2 * ulp radix2 fexp64 h); [exact E|].
pose proof (Rabs_pos h). cbn [bpow radix_val radix2] in *. lra.
Qed.

(** [ln x <= x - 1], from [1 + ln x <= exp (ln x)]. *)
Local Lemma ln_le_sub1 : forall x, 0 < x -> ln x <= x - 1.
Proof.
intros x Hx. pose proof (exp_ineq1_le (ln x)) as H. rewrite exp_ln in H by exact Hx. lra.
Qed.

(** [ln] is [1/c]-Lipschitz above [c]: [ln a - ln b = ln (a / b) <= (a - b) / b]. *)
Local Lemma ln_close :
  forall a b c, 0 < c -> c <= a -> c <= b -> Rabs (ln a - ln b) * c <= Rabs (a - b).
Proof.
intros a b c Hc Ha Hb.
assert (Q : forall u v, 0 < u -> 0 < v -> ln u - ln v <= u / v - 1).
{ intros u v Hu Hv. unfold Rdiv.
  assert (Hv' : 0 < / v) by (apply Rinv_0_lt_compat; exact Hv).
  replace (ln u - ln v) with (ln (u * / v)) by (rewrite ln_mult, ln_Rinv by assumption; ring).
  apply ln_le_sub1. apply Rmult_lt_0_compat; assumption. }
pose proof (Q a b ltac:(lra) ltac:(lra)) as H1.
pose proof (Q b a ltac:(lra) ltac:(lra)) as H2.
destruct (Rle_or_lt 0 (ln a - ln b)) as [P|P].
- rewrite Rabs_pos_eq by exact P.
  apply Rle_trans with ((ln a - ln b) * b); [apply Rmult_le_compat_l; lra|].
  apply Rle_trans with ((a / b - 1) * b); [apply Rmult_le_compat_r; lra|].
  replace ((a / b - 1) * b) with (a - b) by (field; lra).
  apply Rle_abs.
- rewrite Rabs_left by exact P.
  replace (- (ln a - ln b)) with (ln b - ln a) by ring.
  apply Rle_trans with ((ln b - ln a) * a); [apply Rmult_le_compat_l; lra|].
  apply Rle_trans with ((b / a - 1) * a); [apply Rmult_le_compat_r; lra|].
  replace ((b / a - 1) * a) with (b - a) by (field; lra).
  rewrite Rabs_minus_sym. apply Rle_abs.
Qed.

(** [T <= ln ((1 + T) / (1 - T))]: with [X] the quotient,
    [ln X = - ln (1 / X) >= 1 - 1 / X = 2T / (1 + T) >= T]. *)
Local Lemma ln_ge_T : forall T, 0 <= T < 1 -> T <= ln ((1 + T) / (1 - T)).
Proof.
intros T HT.
assert (HX : 0 < (1 + T) / (1 - T)) by (apply Rdiv_lt_0_compat; lra).
pose proof (ln_le_sub1 (/ ((1 + T) / (1 - T))) (Rinv_0_lt_compat _ HX)) as H.
rewrite ln_Rinv in H by exact HX.
replace (/ ((1 + T) / (1 - T))) with ((1 - T) / (1 + T)) in H by (field; lra).
assert (L : (1 - T) / (1 + T) <= 1 - T).
{ unfold Rdiv. rewrite <- (Rmult_1_r (1 - T)) at 2. apply Rmult_le_compat_l; [lra|].
  rewrite <- Rinv_1. apply Rinv_le_contravar; lra. }
lra.
Qed.

(** ** The denominator [1 - t] *)

(** [Fast.fast_two_sum 1 (-t)] is exact ([fts_exact]): [dh + dl = 1 - t]
    with [dh = RN (1 - t)]. As [t <= pred 1 = 1 - 2^-53],
    [2^-53 <= dh <= 1]. *)
Local Lemma den_facts :
  forall t dh dl, is_finite t = true -> bpow radix2 (-27) <= B2R t < 1 ->
  Fast.fast_two_sum DyadicExp.one (opp t) = (dh, dl) ->
  is_finite dh = true /\ is_finite dl = true /\ B2R dh + B2R dl = 1 - B2R t /\
  B2R dh = RN (B2R dh + B2R dl) /\ bpow radix2 (-53) <= B2R dh <= 1 /\
  Rabs (B2R dl) <= bpow radix2 (-53) * B2R dh.
Proof.
intros t dh dl Ft HT E.
pose proof (bpow_gt_0 radix2 (-27)) as P27.
assert (O1 : B2R DyadicExp.one = 1) by exact one_R.
assert (Fo : is_finite DyadicExp.one = true) by reflexivity.
assert (Fm : is_finite (opp t) = true) by (unfold opp; rewrite is_finite_Bopp; exact Ft).
assert (Rm : B2R (opp t) = - B2R t) by (unfold opp; apply B2R_Bopp).
destruct (fts_exact DyadicExp.one (opp t) dh dl Fo Fm) as (Fh & Fl & Rh & S).
{ left. rewrite O1, Rm, Rabs_Ropp, Rabs_R1, Rabs_pos_eq; lra. }
{ rewrite O1, Rm, Rabs_pos_eq; lra. }
{ exact E. }
rewrite O1, Rm in Rh, S.
(* [t < 1] are floats, so [t <= pred 1 = 1 - 2^-53]. *)
assert (Tp : B2R t <= 1 - bpow radix2 (-53)).
{ rewrite <- (pred_lo 1 format_one) by lra.
  apply (pred_ge_gt radix2 fexp64); [apply generic_format_B2R | exact format_one | lra]. }
assert (Hd : bpow radix2 (-53) <= B2R dh <= 1).
{ rewrite Rh. split.
  - apply rn_ge_bpow; [lia | lra].
  - apply (rn_le_bpow 0); [lia | cbn [bpow]; lra]. }
assert (Rh' : B2R dh = RN (B2R dh + B2R dl)) by (rewrite S; exact Rh).
assert (Hn : bpow radix2 (-1022) <= Rabs (B2R dh)).
{ rewrite Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 (-53)); lra).
  apply Rle_trans with (bpow radix2 (-53)); [apply bpow_le; lia | lra]. }
pose proof (rn_low (B2R dh) (B2R dh + B2R dl) Rh' Hn) as L.
replace (B2R dh + B2R dl - B2R dh) with (B2R dl) in L by ring.
rewrite (Rabs_pos_eq (B2R dh)) in L by (pose proof (bpow_gt_0 radix2 (-53)); lra).
repeat split; try assumption; try lra.
Qed.

(** ** The quotient: [-j ln 2 + ln q] *)

(** [nh + nl = 1 + t] exactly ([fts_exact]); [Fast.normalize] scales
    [dh + dl = 1 - t] by [B = 2^-j] into [dh' in [1, 2]], with
    [-53 <= j <= 0] as [dh >= 2^-53]. Then [q = (1 + t) / ((1 - t) B)]
    is in [[1/3, 4]], [(1 + t) / (1 - t) = q B] and
    [ln ((1 + t) / (1 - t)) = -j ln 2 + ln q]; [qh + ql] is within
    [2^-98 q] of [q] ([dd_div_correct]), so [ln_close] with [c = q / 2]
    puts [ln (qh + ql)] within [2^-97 <= 2^-80 t] of [ln q]. *)
Local Lemma large_case :
  forall fma t dh dl nh nl dh' dl' j, is_finite t = true -> bpow radix2 (-12) <= B2R t < 1 ->
  is_finite dh = true -> is_finite dl = true -> B2R dh + B2R dl = 1 - B2R t ->
  B2R dh = RN (B2R dh + B2R dl) -> bpow radix2 (-53) <= B2R dh <= 1 ->
  Rabs (B2R dl) <= bpow radix2 (-53) * B2R dh ->
  Fast.fast_two_sum DyadicExp.one t = (nh, nl) -> Fast.normalize dh dl = (dh', dl', j) ->
  Fast.dd_div true nh nl dh' dl' = Fast.dd_div false nh nl dh' dl' /\
  let '(qh, ql) := Fast.dd_div fma nh nl dh' dl' in
  is_finite qh = true /\ is_finite ql = true /\ 0 < B2R qh /\
  Rabs (B2R ql) <= bpow radix2 (-51) * B2R qh /\ (0 <= - j <= 64)%Z /\
  B2R qh * bpow radix2 (- j) <= bpow radix2 1025 /\
  bpow radix2 (-20) <= Rabs (ln ((1 + B2R t) / (1 - B2R t))) /\
  Rabs (ln ((1 + B2R t) / (1 - B2R t)) - (IZR (- j) * ln 2 + ln (B2R qh + B2R ql)))
    <= bpow radix2 (-80) * Rabs (ln ((1 + B2R t) / (1 - B2R t))).
Proof.
intros fma t dh dl nh nl dh' dl' j Ft HT Fh Fl S Rh Hd Hl En Ej.
pose proof (bpow_gt_0 radix2 (-12)) as P12.
assert (O1 : B2R DyadicExp.one = 1) by exact one_R.
assert (Fo : is_finite DyadicExp.one = true) by reflexivity.
(* [nh + nl = 1 + t] exactly, [nh = RN (1 + t)] in [[1, 2]]. *)
destruct (fts_exact DyadicExp.one t nh nl Fo Ft) as (Fnh & Fnl & Rnh & Sn).
{ left. rewrite O1, Rabs_R1, Rabs_pos_eq; lra. }
{ rewrite O1, Rabs_pos_eq; lra. }
{ exact En. }
rewrite O1 in Rnh, Sn.
assert (Hnh : 1 <= B2R nh <= 2).
{ rewrite Rnh. split.
  - apply (rn_ge_bpow 0); [lia | cbn [bpow]; lra].
  - apply (rn_le_bpow 1); [lia | num]. }
assert (Rnh' : B2R nh = RN (B2R nh + B2R nl)) by (rewrite Sn; exact Rnh).
assert (Hnl : Rabs (B2R nl) <= bpow radix2 (-53) * B2R nh).
{ assert (Hn : bpow radix2 (-1022) <= Rabs (B2R nh)).
  { rewrite Rabs_pos_eq by lra. apply Rle_trans with (bpow radix2 0); [apply bpow_le; lia|].
    cbn [bpow]. lra. }
  pose proof (rn_low (B2R nh) (B2R nh + B2R nl) Rnh' Hn) as L.
  replace (B2R nh + B2R nl - B2R nh) with (B2R nl) in L by ring.
  rewrite (Rabs_pos_eq (B2R nh)) in L by lra. exact L. }
(* [dh' = dh 2^-j] in [[1, 2]], [dl' = dl 2^-j] ([FastRoundErr.normalize_correct]). *)
assert (Hdh : bpow radix2 (-1021) <= B2R dh < 2).
{ split; [apply Rle_trans with (bpow radix2 (-53)); [apply bpow_le; lia | lra] | lra]. }
pose proof (FastRoundErr.normalize_correct dh dl Fh Fl Rh Hdh) as C.
rewrite Ej in C. cbv beta iota in C.
destruct C as (Fdh' & Fdl' & Hj & Rdh' & Rdl' & Bj & _).
assert (Hj53 : (-53 <= j)%Z).
{ assert (L1 : bpow radix2 (-53) < bpow radix2 (j + 1)) by lra. apply lt_bpow in L1. lia. }
set (B := bpow radix2 (- j)) in *.
assert (PB : 0 < B) by apply bpow_gt_0.
assert (EB : ln B = IZR (- j) * ln 2) by (unfold B; rewrite bpow_exp, ln_exp; reflexivity).
assert (E1 : bpow radix2 j * B = 1).
{ unfold B. rewrite <- bpow_plus, Z.add_opp_diag_r. reflexivity. }
assert (E2 : bpow radix2 (j + 1) * B = 2).
{ unfold B. rewrite <- bpow_plus. replace (j + 1 + - j)%Z with 1%Z by lia. reflexivity. }
assert (Hdh' : 1 <= B2R dh' <= 2).
{ rewrite Rdh'. split.
  - apply Rle_trans with (bpow radix2 j * B); [lra | apply Rmult_le_compat_r; lra].
  - apply Rle_trans with (bpow radix2 (j + 1) * B); [apply Rmult_le_compat_r; lra | lra]. }
assert (Hdl' : Rabs (B2R dl') <= bpow radix2 (-53) * B2R dh').
{ rewrite Rdl', Rdh', Rabs_mult, (Rabs_pos_eq B) by lra.
  replace (bpow radix2 (-53) * (B2R dh * B)) with (bpow radix2 (-53) * B2R dh * B) by ring.
  apply Rmult_le_compat_r; lra. }
assert (SD : B2R dh' + B2R dl' = (1 - B2R t) * B) by (rewrite Rdh', Rdl', <- S; ring).
pose proof (Rabs_le_inv _ _ Hdl') as Hdl2.
assert (P1 : bpow radix2 (-80) <= B2R nh <= 4) by num.
assert (P2 : Rabs (B2R nl) <= bpow radix2 (-50) * B2R nh) by num.
assert (P3 : / 2 <= B2R dh' <= 4) by lra.
assert (P4 : Rabs (B2R dl') <= bpow radix2 (-52) * B2R dh') by num.
assert (HD : / 2 <= B2R dh' + B2R dl' <= 3) by num.
split; [apply dd_div_fma; assumption|].
destruct (Fast.dd_div fma nh nl dh' dl') as [qh ql] eqn:Eq. cbv beta iota.
pose proof (dd_div_correct fma nh nl dh' dl' Fnh Fnl Fdh' Fdl' P1 P2 P3 P4) as C.
rewrite Eq in C. cbv beta iota in C. destruct C as (Fqh & Fql & Rq & Hq).
set (D := B2R dh' + B2R dl') in *.
set (Q := (B2R nh + B2R nl) / D) in *.
assert (EQ : Q * D = 1 + B2R t) by (unfold Q; rewrite <- Sn; field; lra).
assert (HQ : / 3 <= Q <= 4) by (split; nra).
pose proof (Rabs_le_inv _ _ Hq) as Hq2.
(* [qh = RN (qh + ql)] in [[1/4, 8]]. *)
assert (Hqh : bpow radix2 (-2) <= B2R qh <= bpow radix2 3).
{ rewrite Rq. split; [apply rn_ge_bpow | apply rn_le_bpow]; try lia; num. }
pose proof (bpow_gt_0 radix2 (-2)) as P2'.
assert (Hn : bpow radix2 (-1022) <= Rabs (B2R qh)).
{ rewrite Rabs_pos_eq by lra.
  apply Rle_trans with (bpow radix2 (-2)); [apply bpow_le; lia | lra]. }
pose proof (rn_low (B2R qh) (B2R qh + B2R ql) Rq Hn) as L.
replace (B2R qh + B2R ql - B2R qh) with (B2R ql) in L by ring.
rewrite (Rabs_pos_eq (B2R qh)) in L by lra.
(* [(1 + t) / (1 - t) = q 2^-j], so its [ln] is [-j ln 2 + ln q]. *)
assert (EX : (1 + B2R t) / (1 - B2R t) = Q * B).
{ rewrite <- EQ, SD. field. lra. }
assert (Ly : ln ((1 + B2R t) / (1 - B2R t)) = IZR (- j) * ln 2 + ln Q).
{ rewrite EX, ln_mult, EB by lra. ring. }
assert (Hy : B2R t <= ln ((1 + B2R t) / (1 - B2R t))) by (apply ln_ge_T; lra).
assert (Lq : Rabs (ln Q - ln (B2R qh + B2R ql)) <= bpow radix2 (-97)).
{ pose proof (ln_close Q (B2R qh + B2R ql) (Q / 2) ltac:(lra) ltac:(lra) ltac:(num)) as Lc.
  rewrite (Rabs_minus_sym Q (B2R qh + B2R ql)) in Lc.
  apply (Rmult_le_reg_r (Q / 2)); [lra|].
  num. }
refine (conj Fqh (conj Fql (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
- lra.
- num.
- lia.
- apply Rle_trans with (bpow radix2 3 * bpow radix2 53).
  + apply Rmult_le_compat; [lra | lra | lra | unfold B; apply bpow_le; lia].
  + rewrite <- bpow_plus. apply bpow_le. lia.
- rewrite Rabs_pos_eq by lra.
  apply Rle_trans with (bpow radix2 (-12)); [apply bpow_le; lia | lra].
- replace (ln ((1 + B2R t) / (1 - B2R t)) - (IZR (- j) * ln 2 + ln (B2R qh + B2R ql)))
    with (ln Q - ln (B2R qh + B2R ql)) by (rewrite Ly; ring).
  rewrite (Rabs_pos_eq (ln ((1 + B2R t) / (1 - B2R t)))) by lra.
  apply Rle_trans with (bpow radix2 (-97)); [exact Lq|].
  apply Rle_trans with (bpow radix2 (-80) * bpow radix2 (-12)).
  + rewrite <- bpow_plus. apply bpow_le. lia.
  + apply Rmult_le_compat_l; [apply bpow_ge_0 | lra].
Qed.

(** ** Halving: the exponent [k - 1] *)

(** A kernel result [h + l] within [2^-68] of [2r 2^-k] is within [2^-68]
    of [r 2^-(k - 1)]. And [k > -1021]: otherwise
    [2r 2^-k >= 2^-27 2^30 = 8] would be far above [|h + l| < 3]. *)
Local Lemma half_out :
  forall (r : R) (h l : f64) (k : Z), bpow radix2 (-27) <= 2 * r ->
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < Rabs (B2R h) < 2 -> (-1021 <= k <= 1022)%Z ->
  Rabs (2 * r * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < Rabs (B2R h) < 2 /\ (-1021 <= k - 1 <= 1022)%Z /\
  Rabs (r * bpow radix2 (- (k - 1)) - (B2R h + B2R l)) <= bpow radix2 (-68).
Proof.
intros r h l k Hr Fh Fl Rh Hh Hk E.
assert (Ek : r * bpow radix2 (- (k - 1)) = 2 * r * bpow radix2 (- k)).
{ replace (- (k - 1))%Z with (- k + 1)%Z by lia. rewrite bpow_plus.
  change (bpow radix2 1) with 2. ring. }
rewrite Ek.
assert (K : (k <> -1021)%Z).
{ intros ->.
  pose proof (bpow_gt_0 radix2 (-27)) as P.
  assert (B30 : bpow radix2 30 <= bpow radix2 (- (-1021))) by (apply bpow_le; lia).
  assert (X8 : bpow radix2 (-27) * bpow radix2 30 <= 2 * r * bpow radix2 (- (-1021))).
  { apply Rmult_le_compat; [lra | apply bpow_ge_0 | exact Hr | exact B30]. }
  rewrite <- bpow_plus in X8. change (bpow radix2 (-27 + 30)) with 8 in X8.
  clear B30.
  set (X := 2 * r * bpow radix2 (- (-1021))) in *. clearbody X.
  assert (Hn : bpow radix2 (-1022) <= Rabs (B2R h)).
  { apply Rle_trans with (/ 2); [|lra]. change (/ 2) with (bpow radix2 (-1)). apply bpow_le. lia. }
  pose proof (rn_low (B2R h) (B2R h + B2R l) Rh Hn) as L.
  replace (B2R h + B2R l - B2R h) with (B2R l) in L by ring.
  pose proof (Rle_abs (B2R h)). pose proof (Rle_abs (B2R l)).
  pose proof (Rle_abs (X - (B2R h + B2R l))).
  clear Hr Hn. num. }
split; [exact Fh|]. split; [exact Fl|]. split; [exact Rh|]. split; [exact Hh|].
split; [lia | exact E].
Qed.

(** ** The theorems *)

Theorem fast_atanh_pos_correct :
  forall fma t h l k,
  is_finite t = true -> bpow radix2 (-8) <= B2R t < 1 ->
  DyadicLog.fast_atanh_pos fma t = Some (h, l, k) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < Rabs (B2R h) < 2 /\ (-1021 <= k <= 1022)%Z /\
  Rabs (Ratanh (B2R t) * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-68).
Proof.
intros fma t h l k Ft HT8.
assert (HT' : bpow radix2 (-12) <= B2R t)
  by (apply (Rle_trans _ (bpow radix2 (-8))); [apply bpow_le; lia | exact (proj1 HT8)]).
assert (HT : bpow radix2 (-27) <= B2R t < 1)
  by (split; [apply (Rle_trans _ (bpow radix2 (-12))); [apply bpow_le; lia | exact HT'] |
    exact (proj2 HT8)]).
unfold DyadicLog.fast_atanh_pos.
destruct (Fast.fast_two_sum DyadicExp.one (opp t)) as [dh dl] eqn:Ed. cbv beta iota.
destruct (den_facts t dh dl Ft HT Ed) as (Fh & Fl & S & Rh & Hd & Hl).
(* The kernel approximates [y = ln ((1 + t) / (1 - t)) = 2 atanh t >= t]. *)
assert (Hy : B2R t <= ln ((1 + B2R t) / (1 - B2R t))).
{ apply ln_ge_T. pose proof (bpow_gt_0 radix2 (-27)). lra. }
assert (Ey : ln ((1 + B2R t) / (1 - B2R t)) = 2 * Ratanh (B2R t)) by (unfold Ratanh; field).
assert (Hr : bpow radix2 (-27) <= 2 * Ratanh (B2R t)) by lra.
destruct (Fast.fast_two_sum DyadicExp.one t) as [nh nl] eqn:En. cbv beta iota.
destruct (Fast.normalize dh dl) as [[dh' dl'] j] eqn:Ej. cbv beta iota.
destruct (Fast.dd_div fma nh nl dh' dl') as [qh ql] eqn:Eq. cbv beta iota.
destruct (large_case fma t dh dl nh nl dh' dl' j Ft (conj HT' (proj2 HT)) Fh Fl S Rh Hd Hl En Ej)
  as [_ C].
rewrite Eq in C. cbv beta iota in C.
destruct C as (Fqh & Fql & Pq & Lq & Hj & Hm & Hy20 & Herr).
destruct (DyadicLog.fast_ln_dd fma qh ql (- j)) as [[[h0 l0] k0]|] eqn:El;
  cbv beta iota; [|discriminate].
intros E. injection E as <- <- <-.
destruct (fast_ln_dd_correct fma qh ql (- j) _ h0 l0 k0 Fqh Fql Pq Lq Hj Hm Hy20 Herr El)
  as (F1 & F2 & R1 & B1 & K1 & E1).
rewrite Ey in E1.
apply half_out; assumption.
Qed.

Theorem fast_atanh_pos_fma :
  forall t,
  is_finite t = true -> bpow radix2 (-8) <= B2R t < 1 ->
  DyadicLog.fast_atanh_pos true t = DyadicLog.fast_atanh_pos false t.
Proof.
intros t Ft HT8.
assert (HT' : bpow radix2 (-12) <= B2R t)
  by (apply (Rle_trans _ (bpow radix2 (-8))); [apply bpow_le; lia | exact (proj1 HT8)]).
assert (HT : bpow radix2 (-27) <= B2R t < 1)
  by (split; [apply (Rle_trans _ (bpow radix2 (-12))); [apply bpow_le; lia | exact HT'] |
    exact (proj2 HT8)]).
unfold DyadicLog.fast_atanh_pos.
destruct (Fast.fast_two_sum DyadicExp.one (opp t)) as [dh dl] eqn:Ed. cbv beta iota.
destruct (den_facts t dh dl Ft HT Ed) as (Fh & Fl & S & Rh & Hd & Hl).
destruct (Fast.fast_two_sum DyadicExp.one t) as [nh nl] eqn:En. cbv beta iota.
destruct (Fast.normalize dh dl) as [[dh' dl'] j] eqn:Ej. cbv beta iota.
destruct (large_case false t dh dl nh nl dh' dl' j Ft (conj HT' (proj2 HT)) Fh Fl S Rh Hd Hl En Ej)
  as [D _].
rewrite D.
destruct (Fast.dd_div false nh nl dh' dl') as [qh ql] eqn:Eq. cbv beta iota.
destruct (large_case false t dh dl nh nl dh' dl' j Ft (conj HT' (proj2 HT)) Fh Fl S Rh Hd Hl En Ej)
  as [_ C].
rewrite Eq in C. cbv beta iota in C. destruct C as (Fqh & Fql & Pq & _).
rewrite fast_ln_dd_fma by assumption. reflexivity.
Qed.
