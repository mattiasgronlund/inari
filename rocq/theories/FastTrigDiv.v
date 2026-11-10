(** * The quotient of the fast path of [tan]

    [DyadicTrig.fast_div false nh nl dh dl] of [Model.v] is [n / d] within
    a relative [3 * 2^-71] when [nh + nl] and [dh + dl] are [n] and [d]
    within a relative 2^-71, with [2^-28 <= |n| <= 1] and [2^-13 <= d <=
    1]: the quotient [qh = RN(nh / dh)], its remainder [nh - qh dh], which
    is exact [Dekker], and one correction ([fast_div_correct]). It is the
    same with an FMA ([fast_div_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Encoding TwoSum TwoProduct FastRound.
From Inari Require DivRuFast DivRemainder MulRuTiny CancelLanes FastExpErr.

Open Scope R_scope.

Local Notation format := (generic_format radix2 fexp64).

Local Lemma format_pow2 : forall e, (-1074 <= e)%Z -> format (bpow radix2 e).
Proof. intros e He. apply generic_format_bpow. unfold FLT_exp. lia. Qed.

(** [x / y] of finite [f64]s with an exact result of at most [MAX] in
    magnitude is finite and rounded to nearest. *)
Local Lemma div_e :
  forall x y, is_finite x = true -> is_finite y = true -> B2R y <> 0 ->
  Rabs (B2R x / B2R y) <= MAX ->
  is_finite (div x y) = true /\ B2R (div x y) = RN (B2R x / B2R y).
Proof.
intros x y Fx Fy Hy H.
destruct (RN_below_max _ H) as (Hlt & _).
generalize (@Bdiv_correct 53 1024 _ _ mode_NE x y Hy).
rewrite Rlt_bool_true by exact Hlt.
intros (HR & HF & _). rewrite Fx in HF.
change (Bdiv mode_NE x y) with (div x y) in HR, HF.
split; [exact HF | exact HR].
Qed.

(** The quotient [qh = RN(nh / dh)] and the remainder [nh - qh dh]: a
    float of at most [2^-52 |nh|] ([DivRemainder.div_remainder]), which
    [sub (sub nh p) pe] computes exactly with Dekker's TwoProduct
    ([DivRuFast.div_dekker_remainder]). [p = RN(qh dh)] lies in
    [[2^-30, 4]] in magnitude, so [two_prod_is_exact] holds with and
    without an FMA. *)
Local Lemma div_rem :
  forall nh dh, is_finite nh = true -> is_finite dh = true ->
  bpow radix2 (-29) <= Rabs (B2R nh) <= 2 -> bpow radix2 (-14) <= B2R dh <= 2 ->
  let qh := div nh dh in
  let p := mul qh dh in
  is_finite qh = true /\ B2R qh = RN (B2R nh / B2R dh) /\
  bpow radix2 (-30) <= Rabs (B2R qh) <= bpow radix2 15 /\
  Rabs (B2R nh - B2R qh * B2R dh) <= bpow radix2 (-52) * Rabs (B2R nh) /\
  is_finite (sub (sub nh p) (Generic.two_prod_err false qh dh p)) = true /\
  B2R (sub (sub nh p) (Generic.two_prod_err false qh dh p)) = B2R nh - B2R qh * B2R dh /\
  Generic.two_prod_is_exact true qh dh p = true /\
  Generic.two_prod_is_exact false qh dh p = true.
Proof.
intros nh dh Fnh Fdh Hnh Hdh qh p.
pose proof (bpow_gt_0 radix2 (-14)) as P14.
assert (Hd0 : B2R dh <> 0) by lra.
(* [|nh / dh| = |nh| / dh] lies in [[2^-30, 2^15]]. *)
assert (Hi : / 2 <= / B2R dh <= bpow radix2 14).
{ split; [apply Rinv_le_contravar; lra |].
  replace (bpow radix2 14) with (/ bpow radix2 (-14))
    by (cbn [bpow radix_val radix2]; rewrite Rinv_inv; reflexivity).
  apply Rinv_le_contravar; lra. }
assert (Hx : Rabs (B2R nh / B2R dh) = Rabs (B2R nh) * / B2R dh).
{ unfold Rdiv. rewrite Rabs_mult, Rabs_inv, (Rabs_pos_eq (B2R dh)) by lra. reflexivity. }
assert (Hxl : bpow radix2 (-30) <= Rabs (B2R nh / B2R dh)).
{ rewrite Hx. cbn [bpow radix_val radix2] in *. nra. }
assert (Hxu : Rabs (B2R nh / B2R dh) <= bpow radix2 15).
{ rewrite Hx. cbn [bpow radix_val radix2] in *. nra. }
destruct (div_e nh dh Fnh Fdh Hd0) as (Fq & Rq).
{ cbn [bpow radix_val radix2] in *. lra. }
fold qh in Fq, Rq.
assert (Hq : bpow radix2 (-30) <= Rabs (B2R qh) <= bpow radix2 15).
{ rewrite Rq. split.
  - apply abs_round_ge_generic; [typeclasses eauto .. | apply format_pow2; lia | exact Hxl].
  - apply abs_round_le_generic; [typeclasses eauto .. | apply format_pow2; lia | exact Hxu]. }
destruct (DivRemainder.div_remainder (B2R nh) (B2R dh)
            (generic_format_B2R 53 1024 nh) (generic_format_B2R 53 1024 dh) Hd0) as (Fr & Hr).
{ rewrite <- Rq. apply Rle_trans with (bpow radix2 (-30)); [apply bpow_le; lia | apply Hq]. }
{ apply Rle_trans with (bpow radix2 (-29)); [apply bpow_le; lia | apply Hnh]. }
rewrite <- Rq in Fr, Hr.
(* The exponents that [div_dekker_remainder] and [two_prod_is_exact] need. *)
assert (Enh : (Generic.exponent nh < 2)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fnh | lia |]. cbn [bpow radix_val radix2]. lra. }
assert (Edh : (Generic.exponent dh < 2)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fdh | lia |].
  rewrite Rabs_pos_eq by lra. cbn [bpow radix_val radix2]. lra. }
assert (Eq : (Generic.exponent qh < 16)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fq | lia |].
  apply Rle_lt_trans with (bpow radix2 15); [apply Hq | apply bpow_lt; lia]. }
destruct (DivRuFast.div_dekker_remainder nh qh dh Fnh Fq Fdh Fr Hr) as (Fs & Rs).
{ apply Rle_trans with (bpow radix2 (-29)); [apply bpow_le; lia | apply Hnh]. }
{ lia. } { lia. } { lia. }
(* [|qh dh|] is within [2^-52 |nh|] of [|nh|], and so in [[2^-30, 4]]. *)
assert (Hqd : bpow radix2 (-30) <= Rabs (B2R qh * B2R dh) <= 4).
{ assert (T := Rabs_triang_inv (B2R nh) (B2R nh - B2R qh * B2R dh)).
  assert (T2 := Rabs_triang (B2R nh) (- (B2R nh - B2R qh * B2R dh))).
  rewrite Rabs_Ropp in T2.
  replace (B2R nh - (B2R nh - B2R qh * B2R dh)) with (B2R qh * B2R dh) in T by ring.
  replace (B2R nh + - (B2R nh - B2R qh * B2R dh)) with (B2R qh * B2R dh) in T2 by ring.
  cbn [bpow radix_val radix2] in *. split; lra. }
destruct (FastExpErr.mul_e qh dh Fq Fdh) as (Fp & Rp & _); [lra |].
fold p in Fp, Rp.
assert (Hp : bpow radix2 (-30) <= Rabs (B2R p) <= bpow radix2 2).
{ rewrite Rp. split.
  - apply abs_round_ge_generic; [typeclasses eauto .. | apply format_pow2; lia | apply Hqd].
  - apply abs_round_le_generic; [typeclasses eauto .. | apply format_pow2; lia |].
    cbn [bpow radix_val radix2]. lra. }
assert (Ep1 : (-30 <= Generic.exponent p)%Z) by (apply MulRuTiny.exponent_ge; [exact Fp | apply Hp]).
assert (Ep2 : (Generic.exponent p < 3)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fp | lia |].
  apply Rle_lt_trans with (bpow radix2 2); [apply Hp | apply bpow_lt; lia]. }
split; [exact Fq |]. split; [exact Rq |]. split; [exact Hq |]. split; [exact Hr |].
split; [exact Fs |]. split; [exact Rs |].
unfold Generic.two_prod_is_exact. cbv beta zeta iota.
split; repeat rewrite Bool.andb_true_iff; repeat split; apply Z.leb_le; lia.
Qed.

(** ** The error in real numbers *)

Local Lemma abs_near :
  forall x y e, Rabs (x - y) <= e -> Rabs x <= Rabs y + e /\ Rabs y <= Rabs x + e.
Proof.
intros x y e H. apply Rabs_le_inv in H.
split; unfold Rabs; destruct (Rcase_abs x), (Rcase_abs y); lra.
Qed.

Local Lemma abs_sub : forall a b, Rabs (a - b) <= Rabs a + Rabs b.
Proof. intros a b. unfold Rminus. rewrite <- (Rabs_Ropp b). apply Rabs_triang. Qed.

Local Lemma abs_div : forall x y, 0 < y -> Rabs (x / y) = Rabs x * / y.
Proof.
intros x y Hy. unfold Rdiv. rewrite Rabs_mult, Rabs_inv, (Rabs_pos_eq y) by lra.
reflexivity.
Qed.

(** A pair with [h = RN(h + l)] and [h + l] within a relative [2^-71] of
    [v], where [a <= |v| <= 1] and [a >= 2^-28]: [|h|] lies in
    [[a / 2, 2]], and [|l| <= 2^-52 |h|], as [h + l] rounds to [h]. *)
Local Lemma pair_near :
  forall h l v a, bpow radix2 (-28) <= a -> a <= Rabs v <= 1 ->
  h = RN (h + l) -> Rabs (h + l - v) <= bpow radix2 (-71) * Rabs v ->
  a / 2 <= Rabs h <= 2 /\ Rabs l <= bpow radix2 (-52) * Rabs h.
Proof.
intros h l v a Ha Hv Rh H.
pose proof (FastExpErr.rn_err (h + l)) as E. rewrite <- Rh in E.
replace (h - (h + l)) with (- l) in E by ring. rewrite Rabs_Ropp in E.
pose proof (Rabs_triang h l) as T1.
pose proof (abs_sub (h + l) l) as T2. replace (h + l - l) with h in T2 by ring.
destruct (abs_near _ _ _ H) as (T3 & T4).
pose proof (bpow_gt_0 radix2 (-1075)).
pose proof (Rabs_pos v).
cbn [bpow radix_val radix2] in *.
assert (Hh : a / 2 <= Rabs h) by lra.
split; [split; lra | lra].
Qed.

(** The correction's numerator [u = RN(r + t)], with [t = RN(nl - m)] and
    [m = RN(qh dl)], where [r] is the exact remainder [nh - qh dh]: [u] is
    finite, each of the three roundings errs by at most [2^-53] of its
    exact result plus [2^-1075], and [|qh dl|], [|nl - m|], [|r + t|] and
    [|u|] are at most [|nh|] times [2^-51], [2^-50], [2^-49] and
    [2^-48]. *)
Local Lemma corr_ops :
  forall nh nl qh dh dl r : f64,
  is_finite nl = true -> is_finite qh = true -> is_finite dl = true -> is_finite r = true ->
  bpow radix2 (-29) <= Rabs (B2R nh) <= 2 -> 0 < B2R dh ->
  Rabs (B2R nl) <= bpow radix2 (-52) * Rabs (B2R nh) ->
  Rabs (B2R dl) <= bpow radix2 (-52) * B2R dh ->
  Rabs (B2R nh - B2R qh * B2R dh) <= bpow radix2 (-52) * Rabs (B2R nh) ->
  B2R r = B2R nh - B2R qh * B2R dh ->
  let m := mul qh dl in
  let t := sub nl m in
  let u := add r t in
  is_finite u = true /\
  Rabs (B2R qh * B2R dl) <= bpow radix2 (-51) * Rabs (B2R nh) /\
  Rabs (B2R nl - B2R m) <= bpow radix2 (-50) * Rabs (B2R nh) /\
  Rabs (B2R nh - B2R qh * B2R dh + B2R t) <= bpow radix2 (-49) * Rabs (B2R nh) /\
  Rabs (B2R u) <= bpow radix2 (-48) * Rabs (B2R nh) /\
  Rabs (B2R m - B2R qh * B2R dl) <=
    bpow radix2 (-53) * Rabs (B2R qh * B2R dl) + bpow radix2 (-1075) /\
  Rabs (B2R t - (B2R nl - B2R m)) <=
    bpow radix2 (-53) * Rabs (B2R nl - B2R m) + bpow radix2 (-1075) /\
  Rabs (B2R u - (B2R nh - B2R qh * B2R dh + B2R t)) <=
    bpow radix2 (-53) * Rabs (B2R nh - B2R qh * B2R dh + B2R t) + bpow radix2 (-1075).
Proof.
intros nh nl qh dh dl r Fnl Fq Fdl Fr Hnh Hdh Hnl Hdl Hr Rr m t u.
pose proof (bpow_gt_0 radix2 (-1075)) as P0.
(* [|qh dl| <= 2^-52 |qh dh|], and [|qh dh| <= (1 + 2^-52) |nh|]. *)
assert (Hqdl : Rabs (B2R qh * B2R dl) <= bpow radix2 (-51) * Rabs (B2R nh)).
{ destruct (abs_near _ _ _ Hr) as (_ & T).
  rewrite Rabs_mult, (Rabs_pos_eq (B2R dh)) in T by lra.
  rewrite Rabs_mult.
  assert (X : Rabs (B2R qh) * Rabs (B2R dl) <= Rabs (B2R qh) * (bpow radix2 (-52) * B2R dh))
    by (apply Rmult_le_compat_l; [apply Rabs_pos | exact Hdl]).
  replace (Rabs (B2R qh) * (bpow radix2 (-52) * B2R dh))
    with (bpow radix2 (-52) * (Rabs (B2R qh) * B2R dh)) in X by ring.
  cbn [bpow radix_val radix2] in *. lra. }
destruct (FastExpErr.mul_e qh dl Fq Fdl) as (Fm & _ & Em).
{ cbn [bpow radix_val radix2] in *. lra. }
fold m in Fm, Em.
assert (Hm : Rabs (B2R nl - B2R m) <= bpow radix2 (-50) * Rabs (B2R nh)).
{ destruct (abs_near _ _ _ Em) as (T & _).
  pose proof (abs_sub (B2R nl) (B2R m)) as T2.
  cbn [bpow radix_val radix2] in *. lra. }
destruct (FastExpErr.sub_e nl m Fnl Fm) as (Ft & _ & Et).
{ cbn [bpow radix_val radix2] in *. lra. }
fold t in Ft, Et.
assert (Ht : Rabs (B2R nh - B2R qh * B2R dh + B2R t) <= bpow radix2 (-49) * Rabs (B2R nh)).
{ destruct (abs_near _ _ _ Et) as (T & _).
  pose proof (Rabs_triang (B2R nh - B2R qh * B2R dh) (B2R t)) as T2.
  cbn [bpow radix_val radix2] in *. lra. }
destruct (FastExpErr.add_e r t Fr Ft) as (Fu & _ & Eu).
{ rewrite Rr. cbn [bpow radix_val radix2] in *. lra. }
fold u in Fu, Eu. rewrite Rr in Eu.
assert (Hu : Rabs (B2R u) <= bpow radix2 (-48) * Rabs (B2R nh)).
{ destruct (abs_near _ _ _ Eu) as (T & _). cbn [bpow radix_val radix2] in *. lra. }
split; [exact Fu |]. split; [exact Hqdl |]. split; [exact Hm |]. split; [exact Ht |].
split; [exact Hu |]. split; [exact Em |]. split; [exact Et | exact Eu].
Qed.

(** With [N = nh + nl] and [D = dh + dl], the exact remainder
    [r = nh - q dh], [m = RN(q dl)], [t = RN(nl - m)], [u = RN(r + t)] and
    [c = RN(u / dh)], [q + c - N / D] is
    [(c - u / dh) + (d2 + d3 + d4) / dh + E dl / (dh D)], where [d2], [d3]
    and [d4] are the errors of [u], [t] and [m], and [E = N - q D] is what
    [r + t] approximates. Each of the three terms is at most about
    [2^-101 |nh| / dh]. With [|nh| / dh <= 4 |n / d|], [q + c] is [N / D]
    within [2^-97 |n / d|] (plus a term below [2^-1000 |n / d|]), and
    [N / D] is [n / d] within [2^-70 (1 + 2^-70) |n / d|]. *)
Local Lemma div_err :
  forall nh nl dh dl n d q m t u c,
  bpow radix2 (-29) <= Rabs nh -> bpow radix2 (-14) <= dh ->
  Rabs nl <= bpow radix2 (-52) * Rabs nh -> Rabs dl <= bpow radix2 (-52) * dh ->
  bpow radix2 (-28) <= Rabs n -> bpow radix2 (-13) <= d <= 1 ->
  Rabs (nh + nl - n) <= bpow radix2 (-71) * Rabs n ->
  Rabs (dh + dl - d) <= bpow radix2 (-71) * d ->
  Rabs (nh - q * dh) <= bpow radix2 (-52) * Rabs nh ->
  Rabs (q * dl) <= bpow radix2 (-51) * Rabs nh ->
  Rabs (nl - m) <= bpow radix2 (-50) * Rabs nh ->
  Rabs (nh - q * dh + t) <= bpow radix2 (-49) * Rabs nh ->
  Rabs u <= bpow radix2 (-48) * Rabs nh ->
  Rabs (m - q * dl) <= bpow radix2 (-53) * Rabs (q * dl) + bpow radix2 (-1075) ->
  Rabs (t - (nl - m)) <= bpow radix2 (-53) * Rabs (nl - m) + bpow radix2 (-1075) ->
  Rabs (u - (nh - q * dh + t)) <=
    bpow radix2 (-53) * Rabs (nh - q * dh + t) + bpow radix2 (-1075) ->
  Rabs (c - u / dh) <= bpow radix2 (-53) * Rabs (u / dh) + bpow radix2 (-1075) ->
  Rabs (q + c - n / d) <= 3 * bpow radix2 (-71) * Rabs (n / d).
Proof.
intros nh nl dh dl n d q m t u c Hnh Hdh Hnl Hdl Hn Hd HN HD Hr Hqdl Hnm Hrt Hu
  Em Et Eu Ec.
pose proof (bpow_gt_0 radix2 (-1075)) as P0.
pose proof (bpow_gt_0 radix2 (-70)) as P70.
pose proof (Rabs_pos nh) as P1.
assert (Hdh0 : 0 < dh) by (pose proof (bpow_gt_0 radix2 (-14)); lra).
assert (Hd0 : 0 < d) by (pose proof (bpow_gt_0 radix2 (-13)); lra).
pose proof (Rabs_le_inv _ _ HD) as HD'.
pose proof (Rabs_le_inv _ _ Hdl) as Hdl'.
(* [D] is within a relative [2^-52] of [dh], and [dh] within about
   [2^-52] of [d]. *)
assert (HDdh : dh / 2 <= dh + dl) by (cbn [bpow radix_val radix2] in *; lra).
assert (Hdhd : d / 2 <= dh) by (cbn [bpow radix_val radix2] in *; lra).
set (idh := / dh).
assert (Hidh : 0 < idh) by (apply Rinv_0_lt_compat; lra).
assert (Hidh2 : idh <= bpow radix2 14).
{ replace (bpow radix2 14) with (/ bpow radix2 (-14))
    by (cbn [bpow radix_val radix2]; rewrite Rinv_inv; reflexivity).
  apply Rinv_le_contravar; [apply bpow_gt_0 | exact Hdh]. }
assert (HiD : / (dh + dl) <= 2 * idh).
{ replace (2 * idh) with (/ (dh / 2)) by (unfold idh; field; lra).
  apply Rinv_le_contravar; [lra | exact HDdh]. }
assert (Hid : idh <= 2 * / d).
{ replace (2 * / d) with (/ (d / 2)) by (field; lra).
  apply Rinv_le_contravar; [lra | exact Hdhd]. }
assert (HiDd : / (dh + dl) <= (1 + bpow radix2 (-70)) * / d).
{ apply Rmult_le_reg_l with (dh + dl); [lra |].
  rewrite Rinv_r by lra.
  apply Rmult_le_reg_r with d; [lra |].
  replace ((dh + dl) * ((1 + bpow radix2 (-70)) * / d) * d)
    with ((dh + dl) * (1 + bpow radix2 (-70))) by (field; lra).
  cbn [bpow radix_val radix2] in *. lra. }
(* The three terms of [q + c - N / D]. *)
set (E := nh - q * dh + nl - q * dl).
assert (Id : q + c - (nh + nl) / (dh + dl) =
  (c - u / dh) + ((u - (nh - q * dh + t)) + (t - (nl - m)) + (q * dl - m)) * idh
  + E * dl * idh * / (dh + dl)).
{ unfold E, idh. field. split; lra. }
assert (B1 : Rabs (c - u / dh) <= bpow radix2 (-101) * (Rabs nh * idh) + bpow radix2 (-1075)).
{ assert (U : Rabs (u / dh) <= bpow radix2 (-48) * (Rabs nh * idh)).
  { rewrite abs_div by lra. change (/ dh) with idh. rewrite <- Rmult_assoc.
    apply Rmult_le_compat_r; [lra | exact Hu]. }
  cbn [bpow radix_val radix2] in *. lra. }
assert (B2 : Rabs (((u - (nh - q * dh + t)) + (t - (nl - m)) + (q * dl - m)) * idh)
             <= bpow radix2 (-101) * (Rabs nh * idh) + bpow radix2 (-1059)).
{ rewrite Rabs_mult, (Rabs_pos_eq idh) by lra.
  assert (T : Rabs ((u - (nh - q * dh + t)) + (t - (nl - m)) + (q * dl - m))
              <= bpow radix2 (-101) * Rabs nh + 3 * bpow radix2 (-1075)).
  { eapply Rle_trans; [apply Rabs_triang |].
    eapply Rle_trans; [apply Rplus_le_compat_r, Rabs_triang |].
    rewrite (Rabs_minus_sym (q * dl) m).
    cbn [bpow radix_val radix2] in *. lra. }
  apply Rle_trans with ((bpow radix2 (-101) * Rabs nh + 3 * bpow radix2 (-1075)) * idh).
  - apply Rmult_le_compat_r; lra.
  - cbn [bpow radix_val radix2] in *. lra. }
assert (HE : Rabs E <= bpow radix2 (-50) * Rabs nh).
{ unfold E. eapply Rle_trans; [apply abs_sub |].
  eapply Rle_trans; [apply Rplus_le_compat_r, Rabs_triang |].
  cbn [bpow radix_val radix2] in *. lra. }
assert (B3 : Rabs (E * dl * idh * / (dh + dl)) <= bpow radix2 (-101) * (Rabs nh * idh)).
{ assert (Pi : 0 < / (dh + dl)) by (apply Rinv_0_lt_compat; lra).
  rewrite !Rabs_mult, (Rabs_pos_eq idh), (Rabs_pos_eq (/ (dh + dl))) by lra.
  assert (X : Rabs E * Rabs dl <= (bpow radix2 (-50) * Rabs nh) * (bpow radix2 (-52) * dh))
    by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact HE | exact Hdl]).
  apply Rle_trans with ((bpow radix2 (-50) * Rabs nh) * (bpow radix2 (-52) * dh)
                        * idh * / (dh + dl)).
  { apply Rmult_le_compat_r; [lra |]. apply Rmult_le_compat_r; [lra | exact X]. }
  replace ((bpow radix2 (-50) * Rabs nh) * (bpow radix2 (-52) * dh) * idh * / (dh + dl))
    with (bpow radix2 (-50) * bpow radix2 (-52) * Rabs nh * / (dh + dl))
    by (unfold idh; field; split; lra).
  apply Rle_trans with (bpow radix2 (-50) * bpow radix2 (-52) * Rabs nh * (2 * idh)).
  - apply Rmult_le_compat_l; [| exact HiD].
    apply Rmult_le_pos; [apply Rmult_le_pos; apply bpow_ge_0 | exact P1].
  - cbn [bpow radix_val radix2]. lra. }
assert (HND : Rabs (q + c - (nh + nl) / (dh + dl))
              <= bpow radix2 (-99) * (Rabs nh * idh) + bpow radix2 (-1058)).
{ assert (PK : 0 <= Rabs nh * idh) by (apply Rmult_le_pos; lra).
  rewrite Id. eapply Rle_trans; [apply Rabs_triang |].
  eapply Rle_trans; [apply Rplus_le_compat_r, Rabs_triang |].
  cbn [bpow radix_val radix2] in *. lra. }
(* [|nh| / dh <= 4 |n / d|], and [|n / d| >= 2^-28]. *)
assert (HA : Rabs nh <= 2 * Rabs n).
{ pose proof (abs_sub (nh + nl) nl) as T.
  replace (nh + nl - nl) with nh in T by ring.
  destruct (abs_near _ _ _ HN) as (T2 & _).
  cbn [bpow radix_val radix2] in *. lra. }
assert (HK : Rabs nh * idh <= 4 * (Rabs n * / d)).
{ apply Rle_trans with ((2 * Rabs n) * (2 * / d)).
  - apply Rmult_le_compat; [exact P1 | lra | exact HA | exact Hid].
  - lra. }
assert (Hnd : Rabs (n / d) = Rabs n * / d) by (apply abs_div; lra).
assert (Hnd1 : bpow radix2 (-28) <= Rabs n * / d).
{ rewrite <- (Rmult_1_r (bpow radix2 (-28))).
  apply Rmult_le_compat; [apply bpow_ge_0 | lra | exact Hn |].
  rewrite <- Rinv_1. apply Rinv_le_contravar; lra. }
(* [N / D - n / d = ((N - n) - (n / d) (D - d)) / D]. *)
assert (HNd : Rabs ((nh + nl) / (dh + dl) - n / d)
              <= bpow radix2 (-70) * (1 + bpow radix2 (-70)) * (Rabs n * / d)).
{ replace ((nh + nl) / (dh + dl) - n / d)
    with (((nh + nl - n) - n / d * (dh + dl - d)) * / (dh + dl)) by (field; split; lra).
  rewrite Rabs_mult, (Rabs_pos_eq (/ (dh + dl)))
    by (left; apply Rinv_0_lt_compat; lra).
  assert (T : Rabs ((nh + nl - n) - n / d * (dh + dl - d)) <= bpow radix2 (-70) * Rabs n).
  { eapply Rle_trans; [apply abs_sub |]. rewrite Rabs_mult, Hnd.
    assert (T2 : Rabs n * / d * Rabs (dh + dl - d)
                 <= Rabs n * / d * (bpow radix2 (-71) * d)).
    { apply Rmult_le_compat_l; [| exact HD].
      apply Rmult_le_pos; [apply Rabs_pos | left; apply Rinv_0_lt_compat; lra]. }
    replace (Rabs n * / d * (bpow radix2 (-71) * d)) with (bpow radix2 (-71) * Rabs n)
      in T2 by (field; lra).
    cbn [bpow radix_val radix2] in *. lra. }
  apply Rle_trans with ((bpow radix2 (-70) * Rabs n) * ((1 + bpow radix2 (-70)) * / d)).
  - apply Rmult_le_compat; [apply Rabs_pos | left; apply Rinv_0_lt_compat; lra
                           | exact T | exact HiDd].
  - right. ring. }
replace (q + c - n / d)
  with ((q + c - (nh + nl) / (dh + dl)) + ((nh + nl) / (dh + dl) - n / d)) by ring.
rewrite Hnd.
eapply Rle_trans; [apply Rabs_triang |].
cbn [bpow radix_val radix2] in *. lra.
Qed.

Theorem fast_div_correct :
  forall nh nl dh dl n d,
  is_finite nh = true -> is_finite nl = true -> is_finite dh = true -> is_finite dl = true ->
  B2R nh = RN (B2R nh + B2R nl) -> B2R dh = RN (B2R dh + B2R dl) ->
  bpow radix2 (-28) <= Rabs n <= 1 -> bpow radix2 (-13) <= d <= 1 ->
  Rabs (B2R nh + B2R nl - n) <= bpow radix2 (-71) * Rabs n ->
  Rabs (B2R dh + B2R dl - d) <= bpow radix2 (-71) * d ->
  let '(h, l) := DyadicTrig.fast_div false nh nl dh dl in
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  Rabs (B2R h + B2R l - n / d) <= 3 * bpow radix2 (-71) * Rabs (n / d).
Proof.
intros nh nl dh dl n d Fnh Fnl Fdh Fdl Rnh Rdh Hn Hd HN HD.
pose proof (bpow_gt_0 radix2 (-1075)) as P0.
pose proof (bpow_gt_0 radix2 (-13)) as P13.
(* The ranges of [nh] and [dh], with [|nl| <= 2^-52 |nh|] and
   [|dl| <= 2^-52 dh]. *)
destruct (pair_near (B2R nh) (B2R nl) n (bpow radix2 (-28)) (Rle_refl _) Hn Rnh HN)
  as (Hnh & Hnl).
assert (Hd' : bpow radix2 (-13) <= Rabs d <= 1) by (rewrite Rabs_pos_eq; [exact Hd | lra]).
assert (HD' : Rabs (B2R dh + B2R dl - d) <= bpow radix2 (-71) * Rabs d)
  by (rewrite (Rabs_pos_eq d); lra).
destruct (pair_near (B2R dh) (B2R dl) d (bpow radix2 (-13))
            ltac:(apply bpow_le; lia) Hd' Rdh HD') as (Hdh & Hdl).
(* [dh + dl] is near [d > 0], and [|dl|] is much smaller than [|dh|]. *)
assert (Pdh : 0 < B2R dh).
{ pose proof (Rabs_le_inv _ _ HD) as T1. pose proof (Rabs_le_inv _ _ Hdl) as T2.
  destruct (Rle_or_lt (B2R dh) 0) as [X|X]; [| exact X].
  rewrite (Rabs_left1 _ X) in T2, Hdh. cbn [bpow radix_val radix2] in *. lra. }
rewrite (Rabs_pos_eq (B2R dh)) in Hdh, Hdl by lra.
assert (Hnh2 : bpow radix2 (-29) <= Rabs (B2R nh) <= 2)
  by (cbn [bpow radix_val radix2] in *; split; lra).
assert (Hdh2 : bpow radix2 (-14) <= B2R dh <= 2)
  by (cbn [bpow radix_val radix2] in *; split; lra).
(* The quotient [qh], the exact remainder [r], and the numerator [u] of
   the correction. *)
destruct (div_rem nh dh Fnh Fdh Hnh2 Hdh2) as (Fq & Rq & Hq & Hr & Fr & Rr & _ & _).
unfold DyadicTrig.fast_div, Fast.fast_two_sum. cbv beta zeta iota.
set (qh := div nh dh) in *.
set (p := mul qh dh) in *.
set (r := sub (sub nh p) (Generic.two_prod_err false qh dh p)) in *.
pose proof (corr_ops nh nl qh dh dl r Fnl Fq Fdl Fr Hnh2 Pdh Hnl Hdl Hr Rr) as X.
cbv zeta in X. destruct X as (Fu & Hqdl & Hnm & Hrt & Hu & Em & Et & Eu).
set (m := mul qh dl) in *. set (t := sub nl m) in *. set (u := add r t) in *.
(* The correction [c = RN(u / dh)], with [|u / dh| <= 2^-48 |nh| / dh]
   and [|nh| / dh] in [[2^-30, 2^15]]. *)
assert (Hud : Rabs (B2R u / B2R dh) <= bpow radix2 (-48) * (Rabs (B2R nh) * / B2R dh)).
{ rewrite abs_div by lra. rewrite <- Rmult_assoc.
  apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra | exact Hu]. }
assert (Hidh : / 2 <= / B2R dh <= bpow radix2 14).
{ split; [apply Rinv_le_contravar; lra |].
  replace (bpow radix2 14) with (/ bpow radix2 (-14))
    by (cbn [bpow radix_val radix2]; rewrite Rinv_inv; reflexivity).
  apply Rinv_le_contravar; [apply bpow_gt_0 | apply Hdh2]. }
assert (HK : bpow radix2 (-30) <= Rabs (B2R nh) * / B2R dh <= bpow radix2 15).
{ cbn [bpow radix_val radix2] in *. split; nra. }
destruct (div_e u dh Fu Fdh) as (Fc & Rc).
{ lra. }
{ apply FastExpErr.small_le_max. cbn [bpow radix_val radix2] in *. lra. }
set (c := div u dh) in *.
pose proof (FastExpErr.rn_err (B2R u / B2R dh)) as Ec. rewrite <- Rc in Ec.
(* [|c| <= |qh|], as [|c|] is about [2^-48 |nh| / dh] at most and [|qh|]
   about [|nh| / dh >= 2^-30]. *)
assert (Hcq : Rabs (B2R c) <= Rabs (B2R qh)).
{ pose proof (FastExpErr.rn_err (B2R nh / B2R dh)) as Eq. rewrite <- Rq in Eq.
  destruct (abs_near _ _ _ Ec) as (T1 & _).
  destruct (abs_near _ _ _ Eq) as (_ & T2).
  rewrite abs_div in T2 by lra.
  cbn [bpow radix_val radix2] in *. lra. }
(* [h + l = qh + c] exactly, with [h = RN(qh + c)]. *)
destruct (add_below_max qh c Fq Fc) as (Fs & Rs & _).
{ pose proof (Rabs_triang (B2R qh) (B2R c)). cbn [bpow radix_val radix2] in *. lra. }
set (s := add qh c) in *.
destruct (CancelLanes.fast_two_sum qh c s Fq Fc Hcq Fs Rs) as (Fl & Rl).
rewrite Rl. replace (B2R s + (B2R qh + B2R c - B2R s)) with (B2R qh + B2R c) by ring.
split; [exact Fs |]. split; [exact Fl |]. split; [exact Rs |].
exact (div_err (B2R nh) (B2R nl) (B2R dh) (B2R dl) n d (B2R qh) (B2R m) (B2R t) (B2R u) (B2R c)
  (proj1 Hnh2) (proj1 Hdh2) Hnl Hdl (proj1 Hn) Hd HN HD Hr Hqdl Hnm Hrt Hu Em Et Eu Ec).
Qed.

Theorem fast_div_fma :
  forall nh nl dh dl,
  is_finite nh = true -> is_finite dh = true ->
  bpow radix2 (-29) <= Rabs (B2R nh) <= 2 -> bpow radix2 (-14) <= B2R dh <= 2 ->
  DyadicTrig.fast_div true nh nl dh dl = DyadicTrig.fast_div false nh nl dh dl.
Proof.
intros nh nl dh dl Fnh Fdh Hnh Hdh.
destruct (div_rem nh dh Fnh Fdh Hnh Hdh) as (Fq & _ & _ & _ & _ & _ & X1 & X2).
unfold DyadicTrig.fast_div. cbv zeta.
rewrite (two_prod_err_fma_eq (div nh dh) dh Fq Fdh X1 X2).
reflexivity.
Qed.
