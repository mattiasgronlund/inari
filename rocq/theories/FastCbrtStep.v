(** * The last Newton step of the fast path of [cbrt]

    [DyadicRoot.cbrt_step fma y zz rr], for [zz] in [1, 8) and [rr] within
    2^-53 of [1/zz] relatively, returns [None] or a double-double
    [(h, l)] with [h = RN (h + l)] within 2^-65 of [Rcbrt zz]
    ([cbrt_step_correct]), and the same with and without an FMA
    ([cbrt_step_fma]). [y] is any [f64]: the check [|y^3 - zz| <= 2^-32],
    as computed, bounds it. *)

From Stdlib Require Import ZArith Reals Lra Lia Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Sterbenz.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct FastExpErr
  FastCbrtNewton.
From Inari Require MulRuTiny CancelLanes FastRound.

Open Scope R_scope.

(** The value of a literal [f64], as in [FastPowCube.v]. *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** Powers of 2 as numerals, for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp] in *.

Local Lemma third_B2R :
  B2R DyadicRoot.third = 6004799503160661 * bpow radix2 (-54).
Proof. lit_B2R. reflexivity. Qed.

Local Lemma cbrt_res_B2R : B2R DyadicRoot.cbrt_res = bpow radix2 (-32).
Proof. lit_B2R. num. lra. Qed.

(** A finite product or difference has finite arguments. *)
Local Lemma mul_fin :
  forall a b, is_finite (mul a b) = true -> is_finite a = true /\ is_finite b = true.
Proof.
intros [sa|sa| |sa ma ea Ha] [sb|sb| |sb mb eb Hb] H; try (split; reflexivity);
  cbn in H; discriminate H.
Qed.

Local Lemma sub_fin :
  forall a b, is_finite (sub a b) = true -> is_finite a = true /\ is_finite b = true.
Proof.
intros [sa|sa| |sa ma ea Ha] [sb|sb| |sb mb eb Hb] H; try (split; reflexivity);
  try destruct sa; try destruct sb; cbn in H; discriminate H.
Qed.

(** If [x - y] is finite, it is [RN(x - y)], as in [FastExpEdge.v]. *)
Local Lemma sub_B2R :
  forall x y, is_finite x = true -> is_finite y = true ->
  is_finite (sub x y) = true -> B2R (sub x y) = RN (B2R x - B2R y).
Proof.
intros x y Fx Fy Fs.
generalize (@Bminus_correct 53 1024 _ _ mode_NE x y Fx Fy).
destruct (Rlt_bool _ _).
- intros (HR & _). exact HR.
- intros (HO & _). exfalso.
  revert Fs HO. unfold sub.
  destruct (Bminus mode_NE x y); intros F HO; discriminate.
Qed.

(** [|d| <= cbrt_res] as computed means [d] is finite and [|d| <= 2^-32]. *)
Local Lemma check_le :
  forall d, Model.le (fabs d) DyadicRoot.cbrt_res = true ->
  is_finite d = true /\ Rabs (B2R d) <= bpow radix2 (-32).
Proof.
intros d H.
assert (Fd : is_finite d = true).
{ revert H. destruct d as [s|s| |s m e B]; intros H; try reflexivity;
    vm_compute in H; discriminate H. }
split; [exact Fd|].
unfold Model.le, fabs in H.
rewrite Bleb_correct in H; [| rewrite is_finite_Babs; exact Fd | reflexivity].
rewrite B2R_Babs, cbrt_res_B2R in H.
destruct (Rle_bool_spec (Rabs (B2R d)) (bpow radix2 (-32))); [assumption | discriminate H].
Qed.

(** What the check of [cbrt_step] gives: [y^3 - zz], as computed, is
    exact (Sterbenz) and at most 2^-32, so [y] is in [0.999, 2.001] and
    both products of [y^3] are exact enough for [two_prod_err]. *)
Local Lemma check_facts :
  forall y zz, is_finite zz = true -> 1 <= B2R zz < 8 ->
  Model.le (fabs (sub (mul y (mul y y)) zz)) DyadicRoot.cbrt_res = true ->
  is_finite y = true /\ is_finite (mul y y) = true /\
  is_finite (sub (mul y (mul y y)) zz) = true /\
  B2R (sub (mul y (mul y y)) zz) = B2R (mul y (mul y y)) - B2R zz /\
  Rabs (B2R (mul y (mul y y)) - B2R zz) <= bpow radix2 (-32) /\
  999 / 1000 <= B2R y <= 2001 / 1000 /\
  (forall fma, Generic.two_prod_is_exact fma y y (mul y y) = true) /\
  (forall fma, Generic.two_prod_is_exact fma y (mul y y) (mul y (mul y y)) = true).
Proof.
intros y zz Fz Hz Hc.
set (y2 := mul y y) in *. set (y3 := mul y y2) in *.
destruct (check_le _ Hc) as [Fd Hd].
destruct (sub_fin _ _ Fd) as [Fy3 _].
destruct (mul_fin _ _ Fy3) as [Fy Fy2].
assert (Ey2 : B2R y2 = RN (B2R y * B2R y)) by (apply mul_B2R; assumption).
assert (Ey3 : B2R y3 = RN (B2R y * B2R y2)) by (apply mul_B2R; assumption).
assert (Ed0 : B2R (sub y3 zz) = RN (B2R y3 - B2R zz)) by (apply sub_B2R; assumption).
(* [|RN(y3 - zz)| <= 2^-32] gives [|y3 - zz| < 2^-31], as 2^-31 is a [f64]. *)
assert (Hlt : Rabs (B2R y3 - B2R zz) < bpow radix2 (-31)).
{ apply Rnot_le_lt. intros Hge.
  assert (H31 : bpow radix2 (-31) <= Rabs (RN (B2R y3 - B2R zz))).
  { apply abs_round_ge_generic;
      [typeclasses eauto .. | apply generic_format_bpow; unfold FLT_exp; lia | exact Hge]. }
  rewrite <- Ed0 in H31.
  assert (bpow radix2 (-32) < bpow radix2 (-31)) by (apply bpow_lt; lia).
  lra. }
(* Sterbenz: [zz / 2 <= y3 <= 2 zz], so [y3 - zz] is a [f64]. *)
assert (Ed : B2R (sub y3 zz) = B2R y3 - B2R zz).
{ rewrite Ed0. apply round_generic; [typeclasses eauto ..|].
  apply Rabs_lt_inv in Hlt.
  assert (bpow radix2 (-31) <= 1 / 2) by (num; lra).
  apply sterbenz; [typeclasses eauto .. | apply generic_format_B2R
    | apply generic_format_B2R | lra]. }
assert (Hd' : Rabs (B2R y3 - B2R zz) <= bpow radix2 (-32)) by (rewrite <- Ed; exact Hd).
assert (Hy3 : 99999 / 100000 <= B2R y3 <= 800001 / 100000).
{ apply Rabs_le_inv in Hd'. num. lra. }
pose proof (rn_err (B2R y * B2R y)) as R2. rewrite <- Ey2 in R2.
pose proof (rn_err (B2R y * B2R y2)) as R3. rewrite <- Ey3 in R3.
(* [V = y y2] is within 2^-53 of [y3], relatively. *)
assert (HV : 9999 / 10000 <= B2R y * B2R y2 <= 80001 / 10000).
{ destruct (Rle_or_lt 0 (B2R y * B2R y2)) as [H0|H0].
  - rewrite (Rabs_pos_eq (B2R y * B2R y2) H0) in R3. apply Rabs_le_inv in R3. num. lra.
  - rewrite (Rabs_left (B2R y * B2R y2) H0) in R3. apply Rabs_le_inv in R3. num. lra. }
assert (Hy2p : 0 <= B2R y2).
{ rewrite Ey2. apply round_ge_generic; [typeclasses eauto .. | apply generic_format_0 | nra]. }
assert (Hy0 : 0 < B2R y).
{ destruct (Rle_or_lt (B2R y) 0) as [H|H]; [|exact H]. exfalso. nra. }
rewrite (Rabs_pos_eq (B2R y * B2R y)) in R2 by nra. apply Rabs_le_inv in R2.
(* [y > 2.001] gives [y2 >= 4] and [V > 8.004]. *)
assert (Hyhi : B2R y <= 2001 / 1000).
{ apply Rnot_lt_le. intros H.
  assert (Hyy : 4004 / 1000 < B2R y * B2R y) by nra.
  assert (4 <= B2R y2) by (num; lra).
  nra. }
(* [y < 0.999] gives [y2 <= 0.9991] and [V < 0.999]. *)
assert (Hylo : 999 / 1000 <= B2R y).
{ apply Rnot_lt_le. intros H.
  assert (Hyy : B2R y * B2R y < 999 / 1000) by nra.
  assert (B2R y2 <= 9991 / 10000) by (num; lra).
  nra. }
assert (Hy2 : 1 / 2 <= B2R y2 <= 5).
{ assert (998 / 1000 <= B2R y * B2R y <= 4005 / 1000) by nra. num. lra. }
assert (Ey : (Generic.exponent y < 4)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fy | lia |].
  rewrite Rabs_pos_eq by lra. num. lra. }
assert (Ey2lo : (-1 <= Generic.exponent y2)%Z).
{ apply MulRuTiny.exponent_ge; [exact Fy2|]. rewrite Rabs_pos_eq by lra. num. lra. }
assert (Ey2hi : (Generic.exponent y2 < 4)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fy2 | lia |].
  rewrite Rabs_pos_eq by lra. num. lra. }
assert (Ey3lo : (-1 <= Generic.exponent y3)%Z).
{ apply MulRuTiny.exponent_ge; [exact Fy3|]. rewrite Rabs_pos_eq by lra. num. lra. }
assert (Ey3hi : (Generic.exponent y3 < 4)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fy3 | lia |].
  rewrite Rabs_pos_eq by lra. num. lra. }
do 5 (split; [assumption|]). split; [lra|].
split; intros fma; unfold Generic.two_prod_is_exact; cbv zeta;
  destruct fma; repeat (apply andb_true_intro; split); apply Z.leb_le; lia.
Qed.

(** Dekker's FastTwoSum (T. J. Dekker, A floating-point technique for
    extending the available precision, 1971): [s = RN(a + b)] and
    [s + t = a + b] exactly, up to [MAX], as in [FastAhypAsinh.v]. *)
Local Lemma fts :
  forall a b s t, is_finite a = true -> is_finite b = true ->
  Rabs (B2R b) <= Rabs (B2R a) -> Rabs (B2R a + B2R b) <= MAX ->
  Fast.fast_two_sum a b = (s, t) ->
  is_finite s = true /\ is_finite t = true /\ B2R s = RN (B2R a + B2R b) /\
  B2R s + B2R t = B2R a + B2R b.
Proof.
intros a b s t Fa Fb Hab Hab2 E.
unfold Fast.fast_two_sum in E. injection E as <- <-.
destruct (add_below_max a b Fa Fb Hab2) as (Fs & Es & _).
destruct (CancelLanes.fast_two_sum a b (add a b) Fa Fb Hab Fs Es) as [Ft Et].
do 3 (split; [assumption|]). rewrite Et. ring.
Qed.

Theorem cbrt_step_correct :
  forall fma y zz rr h l,
  is_finite zz = true -> is_finite rr = true ->
  1 <= B2R zz < 8 ->
  Rabs (B2R rr - / B2R zz) <= bpow radix2 (-53) * / B2R zz ->
  DyadicRoot.cbrt_step fma y zz rr = Some (h, l) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  Rabs (Rcbrt (B2R zz) - (B2R h + B2R l)) <= bpow radix2 (-65).
Proof.
intros fma y zz rr h l Fz Fr Hz Hr E.
unfold DyadicRoot.cbrt_step in E. cbv zeta in E.
destruct (Model.le (fabs (sub (mul y (mul y y)) zz)) DyadicRoot.cbrt_res) eqn:Hc;
  [|discriminate E].
injection E as Eh0 El0.
destruct (check_facts y zz Fz Hz Hc) as (Fy & Fy2 & Fd & Ed & Hd & Hy & Ex2 & Ex3).
destruct (two_prod_err_correct fma y y Fy Fy (Ex2 fma)) as (_ & Ey2 & _ & Fy2l & Ey2l).
destruct (two_prod_err_correct fma y (mul y y) Fy Fy2 (Ex3 fma))
  as (Fy3 & Ey3 & _ & Fe3 & Ee3).
clear Hc Ex2 Ex3.
set (y2 := mul y y) in *. set (y3 := mul y y2) in *. set (d := sub y3 zz) in *.
set (y2l := Generic.two_prod_err fma y y y2) in *.
set (e3 := Generic.two_prod_err fma y y2 y3) in *.
set (m := mul y y2l) in *. set (y3l := add e3 m) in *.
set (s1 := add d y3l) in *. set (hh := mul s1 rr) in *.
set (yt := mul y DyadicRoot.third) in *. set (dy := mul hh yt) in *.
(* Bounds on [y2], [y2l] and [e3], the errors of the two products. *)
assert (Hy2l : Rabs (B2R y2l) <= 5 * bpow radix2 (-53)).
{ rewrite Ey2l, Ey2, Rabs_minus_sym. eapply Rle_trans; [apply rn_err|].
  rewrite Rabs_pos_eq by nra. assert (B2R y * B2R y <= 4005 / 1000) by nra. num. lra. }
assert (Hy2 : 0 <= B2R y2 <= 401 / 100).
{ apply Rabs_le_inv in Hy2l. assert (998 / 1000 <= B2R y * B2R y <= 4005 / 1000) by nra.
  rewrite Ey2l in Hy2l. num. lra. }
assert (He3 : Rabs (B2R e3) <= 9 * bpow radix2 (-53)).
{ rewrite Ee3, Ey3, Rabs_minus_sym. eapply Rle_trans; [apply rn_err|].
  rewrite Rabs_pos_eq by nra. assert (B2R y * B2R y2 <= 803 / 100) by nra. num. lra. }
assert (Hyl : Rabs (B2R y * B2R y2l) <= 11 * bpow radix2 (-53)).
{ rewrite Rabs_mult, (Rabs_pos_eq (B2R y)) by lra.
  assert (0 <= Rabs (B2R y2l)) by apply Rabs_pos. nra. }
(* [m = RN(y y2l)], [y3l = RN(e3 + m)]: tiny, so their errors are 2^-106. *)
destruct (mul_e y y2l Fy Fy2l ltac:(num; lra)) as (Fm & _ & Rm).
fold m in Fm, Rm.
assert (Hm : Rabs (B2R m) <= 12 * bpow radix2 (-53)).
{ apply Rabs_le_inv in Rm. pose proof (Rabs_le_inv _ _ Hyl). apply Rabs_le.
  num. lra. }
assert (Hem : Rabs (B2R e3 + B2R m) <= 21 * bpow radix2 (-53)).
{ eapply Rle_trans; [apply Rabs_triang|]. lra. }
destruct (add_e e3 m Fe3 Fm ltac:(num; lra)) as (Fy3l & _ & Ry3l).
fold y3l in Fy3l, Ry3l.
(* The products are error-free ([y2 + y2l = y y], [y3 + e3 = y y2]), so
   [D = y^3 - zz = d + e3 + y y2l], and [d + y3l] is [D] up to [eta]. *)
set (D := B2R y * (B2R y * B2R y) - B2R zz).
set (eta := B2R y3l - (B2R e3 + B2R y * B2R y2l)).
assert (EDe : B2R d + B2R y3l = D + eta).
{ unfold D, eta. rewrite Ed, Ee3, Ey2l. ring. }
assert (HD : Rabs D <= bpow radix2 (-32) + bpow radix2 (-48)).
{ replace D with (B2R d + B2R e3 + B2R y * B2R y2l)
    by (unfold D; rewrite Ed, Ee3, Ey2l; ring).
  rewrite <- Ed in Hd.
  apply Rabs_le_inv in Hd. apply Rabs_le_inv in He3. apply Rabs_le_inv in Hyl.
  apply Rabs_le. num. lra. }
assert (Heta : Rabs eta <= bpow radix2 (-100)).
{ unfold eta.
  apply Rabs_le_inv in Ry3l. apply Rabs_le_inv in Rm.
  apply Rabs_le. num. lra. }
(* The correction: [s1 = RN(d + y3l)], [hh = RN(s1 rr)], [yt = RN(y third)]
   and [dy = RN(hh yt)]. *)
assert (Hiz : 0 < / B2R zz <= 1).
{ split; [apply Rinv_0_lt_compat; lra|]. rewrite <- Rinv_1.
  apply Rinv_le_contravar; lra. }
assert (Hrr : Rabs (B2R rr) <= 2).
{ apply Rabs_le_inv in Hr. apply Rabs_le. num. lra. }
assert (HDe : Rabs (D + eta) <= 1).
{ eapply Rle_trans; [apply Rabs_triang|]. num. lra. }
destruct (add_e d y3l Fd Fy3l ltac:(rewrite EDe; lra)) as (Fs1 & _ & Rs1).
fold s1 in Fs1, Rs1.
rewrite EDe in Rs1.
assert (Hs1 : Rabs (B2R s1) <= 2).
{ apply Rabs_le_inv in Rs1. pose proof (Rabs_le_inv _ _ HDe). apply Rabs_le.
  num. lra. }
assert (Hsr : Rabs (B2R s1 * B2R rr) <= 4)
  by (replace 4 with (2 * 2) by ring; apply Rabs_mul_le; assumption).
destruct (mul_e s1 rr Fs1 Fr ltac:(lra)) as (Fhh & _ & Rhh).
fold hh in Fhh, Rhh.
assert (Hhh : Rabs (B2R hh) <= 5).
{ apply Rabs_le_inv in Rhh. pose proof (Rabs_le_inv _ _ Hsr). apply Rabs_le.
  num. lra. }
assert (Hyq : Rabs (B2R y * B2R DyadicRoot.third) <= 1).
{ rewrite third_B2R, Rabs_mult, (Rabs_pos_eq (B2R y)) by lra.
  rewrite Rabs_pos_eq by (num; lra). num. nra. }
destruct (mul_e y DyadicRoot.third Fy ltac:(reflexivity) ltac:(lra)) as (Fyt & _ & Ryt).
fold yt in Fyt, Ryt.
rewrite third_B2R in Ryt.
assert (Hyt : Rabs (B2R yt) <= 2).
{ rewrite third_B2R in Hyq.
  apply Rabs_le_inv in Ryt. pose proof (Rabs_le_inv _ _ Hyq). apply Rabs_le.
  num. lra. }
assert (Hht : Rabs (B2R hh * B2R yt) <= 10)
  by (replace 10 with (5 * 2) by ring; apply Rabs_mul_le; assumption).
destruct (mul_e hh yt Fhh Fyt ltac:(lra)) as (Fdy & _ & Rdy).
fold dy in Fdy, Rdy.
destruct (cbrt_step_err (B2R y) (B2R zz) (B2R rr) (B2R s1) (B2R hh) (B2R yt) (B2R dy)
  D eta Hy ltac:(lra) Hr HD Heta Rs1 Rhh Ryt Rdy) as [Hdy Hstep].
pose proof (cbrt_newton (B2R zz) (B2R y) ltac:(lra) ltac:(lra) HD) as Hn.
fold D in Hn.
(* FastTwoSum: [h + l = y - dy] exactly, as [|dy| <= 1/2 <= y]. *)
assert (Ody : B2R (opp dy) = - B2R dy) by (unfold opp; apply B2R_Bopp).
assert (Fody : is_finite (opp dy) = true)
  by (unfold opp; rewrite is_finite_Bopp; exact Fdy).
destruct (fts y (opp dy) h l Fy Fody) as (Fh & Fl & Eh & Ehl).
{ rewrite Ody, Rabs_Ropp, (Rabs_pos_eq (B2R y)) by lra. lra. }
{ rewrite Ody. apply Rabs_le_inv in Hdy. apply Rabs_le. num. lra. }
{ unfold Fast.fast_two_sum. rewrite El0, Eh0. reflexivity. }
split; [exact Fh|]. split; [exact Fl|]. split.
- rewrite Ehl. exact Eh.
- rewrite Ehl, Ody.
  set (Q := B2R y * D / (3 * B2R zz)) in *.
  apply Rabs_le_inv in Hn. apply Rabs_le_inv in Hstep.
  assert (bpow radix2 (-66) + bpow radix2 (-82) <= bpow radix2 (-65)) by (num; lra).
  apply Rabs_le. lra.
Qed.

Theorem cbrt_step_fma :
  forall y zz rr,
  is_finite zz = true -> 1 <= B2R zz < 8 ->
  DyadicRoot.cbrt_step true y zz rr = DyadicRoot.cbrt_step false y zz rr.
Proof.
intros y zz rr Fz Hz.
unfold DyadicRoot.cbrt_step. cbv zeta.
destruct (Model.le (fabs (sub (mul y (mul y y)) zz)) DyadicRoot.cbrt_res) eqn:Hc;
  [|reflexivity].
destruct (check_facts y zz Fz Hz Hc) as (Fy & Fy2 & _ & _ & _ & _ & Ex2 & Ex3).
rewrite (FastRound.two_prod_err_fma_eq y y Fy Fy (Ex2 true) (Ex2 false)).
rewrite (FastRound.two_prod_err_fma_eq y (mul y y) Fy Fy2 (Ex3 true) (Ex3 false)).
reflexivity.
Qed.
