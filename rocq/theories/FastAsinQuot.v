(** * The quotient of the fast paths of [asin] and [acos]

    [DyadicAtan.fast_asin_atan t] of [Model.v] divides [t] by the [r] of
    [FastAsinSqrt.v] up to the split [181/256], and [r] by [t] above it,
    by [Fast.dd_div]. The quotient is within [2^-96 q] of the [q] of
    [FastAsinAngle.v] and is an input of the core of [FastAtanCore.v]
    ([asin_quot]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Sterbenz.
From Inari Require Import Model Mpfr Elementary AtanReal AtanIdent TwoSum TwoProduct DyDriver
  NearF64 NearCells FastRound FastRoundErr FastDiv FastHypPos FastAtanTables FastAtanIdent
  FastAtanCore FastAtanAsm FastDdSqrt.
From Inari Require DyExp DyPown DyAtanTiny DyExpRules FastExpErr MulRuTiny FastLogNorm.
From Inari Require Import FastAsinReal FastAsinAngle FastAsinSqrt.

Open Scope R_scope.

(** [B2R l] of an [f64] literal [l], as [m * 2^e] (as in [FastHypPos.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** [DyadicAtan.asin_s], the split, is [181/256]. *)
Lemma lit_asin_s : is_finite DyadicAtan.asin_s = true /\ B2R DyadicAtan.asin_s = 181 / 256.
Proof.
split; [vm_compute; reflexivity |].
lit_B2R. assert (K : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
rewrite K. lra.
Qed.

(** [dd_div] errs by [2^-98] and [r] by [2^-99], so the quotient is
    within [2^-96] of [q]. *)
Lemma asin_quot :
  forall fma t rh rl qh ql,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < 1 ->
  DyadicAtan.fast_sqrt1m fma t = (rh, rl) ->
  (if le t DyadicAtan.asin_s then Fast.dd_div fma t zero rh rl
   else Fast.dd_div fma rh rl t zero) = (qh, ql) ->
  is_finite qh = true /\ is_finite ql = true /\
  bpow radix2 (-61) <= B2R qh <= 129 / 128 /\ Rabs (B2R ql) <= bpow radix2 (-53) * B2R qh /\
  exists q, bpow radix2 (-27) <= q <= 10003 / 10000 /\
    Rabs (B2R qh + B2R ql - q) <= bpow radix2 (-96) * q /\
    (if Rle_bool (B2R t) (181 / 256) then asin (B2R t) else acos (B2R t)) = atan q.
Proof.
intros fma t rh rl qh ql Ft Ht Es Ed.
destruct lit_asin_s as (Fs & Esv).
destruct (sqrt1m_facts fma t rh rl Ft Ht Es) as (Frh & Frl & Hrh & Hrl & Hhalf & Hr).
destruct (asin_q (B2R t) (conj (proj1 Ht) (below_one t Ft (proj2 Ht))))
  as ((Hr0 & Hr1) & Hr707 & q & Hq & Eqq & EV).
set (r := sqrt ((1 - B2R t) * (1 + B2R t))) in *.
assert (Fz : is_finite zero = true) by reflexivity.
assert (Bz : B2R zero = 0) by reflexivity.
assert (K27 : bpow radix2 (-27) = / 134217728) by reflexivity.
assert (K28 : bpow radix2 (-28) = / 268435456) by reflexivity.
assert (K50 : bpow radix2 (-50) = / 1125899906842624) by reflexivity.
assert (K52 : bpow radix2 (-52) = / 4503599627370496) by reflexivity.
assert (K53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
assert (K80 : bpow radix2 (-80) = / 1208925819614629174706176) by reflexivity.
assert (K96 : bpow radix2 (-96) = / 79228162514264337593543950336) by reflexivity.
assert (K98 : bpow radix2 (-98) = / 316912650057057350374175801344) by reflexivity.
assert (K99 : bpow radix2 (-99) = / 633825300114114700748351602688) by reflexivity.
assert (Hq0 : 0 <= q) by (rewrite K27 in Hq; lra).
(* [dd_div] gives [qh + ql] within [2^-98] of [N / D], and [N / D] is
   within [2^-98] ([div_den], below the split) or [2^-99] ([div_num],
   above it) of [q]: in all within [2^-98 (1 + 2^-98) q + 2^-98 q], less
   than [2^-96 q]. *)
assert (M : is_finite qh = true /\ is_finite ql = true /\ B2R qh = RN (B2R qh + B2R ql) /\
            Rabs (B2R qh + B2R ql - q) <= bpow radix2 (-96) * q).
{ revert Ed. destruct (le t DyadicAtan.asin_s) eqn:L; intro Ed.
  - (* Up to the split, [q = t / r]. *)
    pose proof (ge_true DyadicAtan.asin_s t Fs Ft L) as G.
    rewrite Esv in G.
    rewrite Rle_bool_true in Eqq by exact G.
    assert (Hn : bpow radix2 (-80) <= B2R t <= 4) by (rewrite K80; rewrite K27 in Ht; lra).
    assert (Hnl : Rabs (B2R zero) <= bpow radix2 (-50) * B2R t).
    { rewrite Bz, Rabs_R0. apply Rmult_le_pos; [apply bpow_ge_0 | rewrite K27 in Ht; lra]. }
    assert (Hd : / 2 <= B2R rh <= 4) by (split; [exact (Hhalf G) | lra]).
    assert (Hdl : Rabs (B2R rl) <= bpow radix2 (-52) * B2R rh)
      by (rewrite K52; rewrite K53 in Hrl; lra).
    pose proof (dd_div_correct fma t zero rh rl Ft Fz Frh Frl Hn Hnl Hd Hdl) as D.
    rewrite Ed in D. cbv beta iota in D.
    destruct D as (Fqh & Fql & Eqh & He).
    rewrite Bz, Rplus_0_r in He.
    assert (Hk : 0 <= bpow radix2 (-99) <= / 2) by (rewrite K99; lra).
    pose proof (div_den (B2R t) r (B2R rh + B2R rl) (bpow radix2 (-99))
                  ltac:(rewrite K27 in Ht; lra) ltac:(rewrite K27 in Hr0; lra) Hk Hr) as Hdd.
    rewrite <- Eqq in Hdd.
    set (QR := B2R t / (B2R rh + B2R rl)) in *.
    rewrite K98 in He. rewrite K99 in Hdd. rewrite K96.
    apply Rabs_le_inv in He. apply Rabs_le_inv in Hdd.
    split; [exact Fqh | split; [exact Fql | split; [exact Eqh |]]].
    apply Rabs_le. lra.
  - (* Above it, [q = r / t]. *)
    pose proof (ge_false DyadicAtan.asin_s t Fs Ft L) as G.
    rewrite Esv in G.
    rewrite Rle_bool_false in Eqq by lra.
    assert (Hn : bpow radix2 (-80) <= B2R rh <= 4) by (rewrite K80; rewrite K28 in Hrh; lra).
    assert (Hnl : Rabs (B2R rl) <= bpow radix2 (-50) * B2R rh)
      by (rewrite K50; rewrite K53 in Hrl; rewrite K28 in Hrh; lra).
    assert (Hd : / 2 <= B2R t <= 4) by lra.
    assert (Hdl : Rabs (B2R zero) <= bpow radix2 (-52) * B2R t).
    { rewrite Bz, Rabs_R0. apply Rmult_le_pos; [apply bpow_ge_0 | lra]. }
    pose proof (dd_div_correct fma rh rl t zero Frh Frl Ft Fz Hn Hnl Hd Hdl) as D.
    rewrite Ed in D. cbv beta iota in D.
    destruct D as (Fqh & Fql & Eqh & He).
    rewrite Bz, Rplus_0_r in He.
    pose proof (div_num (B2R rh + B2R rl) r (B2R t) (bpow radix2 (-99))
                  ltac:(lra) Hr) as Hdd.
    rewrite <- Eqq in Hdd.
    set (QR := (B2R rh + B2R rl) / B2R t) in *.
    rewrite K98 in He. rewrite K99 in Hdd. rewrite K96.
    apply Rabs_le_inv in He. apply Rabs_le_inv in Hdd.
    split; [exact Fqh | split; [exact Fql | split; [exact Eqh |]]].
    apply Rabs_le. lra. }
destruct M as (Fqh & Fql & Eqh & Htot).
destruct (quot_tail qh ql q Eqh Hq Htot) as (Hqh & Hql).
split; [exact Fqh |]. split; [exact Fql |]. split; [exact Hqh |]. split; [exact Hql |].
exists q. split; [exact Hq | split; [exact Htot | exact EV]].
Qed.
