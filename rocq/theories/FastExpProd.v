(** * The last product of the fast path of [exp]

    [DyadicExp.fast_exp] multiplies [s + pl] by [th + tl] into [h + l]:
    [ph] is [s th] rounded, [low] adds the error of that rounding, exact
    by [TwoProduct.v] [Dekker], to [s tl] and [pl th], and [(h, l)] is the
    Fast2Sum [Dekker] of [ph] and [low] ([fast_exp_prod]). [pl tl] is left
    out. The product [s th] is exact for [Generic.two_prod_err] with and
    without an FMA ([prod_exact]).

    [Dekker] T. J. Dekker, A floating-point technique for extending the
    available precision, Numer. Math. 18 (1971). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Relative.
From Inari Require Import Model Encoding Elementary TwoSum TwoProduct CancelLanes FastExpErr.
From Inari Require MulRuTiny.

Open Scope R_scope.

Lemma prod_exact :
  forall b s th,
  is_finite s = true -> is_finite th = true ->
  Rabs (B2R s - 1) <= bpow radix2 (-13) -> 1 <= B2R th < 2 ->
  Generic.two_prod_is_exact b s th (mul s th) = true.
Proof.
intros b s th Fs Fth Hs Hth.
apply Rabs_le_inv in Hs.
cbn [bpow radix_val radix2 Z.opp] in Hs.
(* [s th] is in [[1 - 2^-13, 3]], and [s th] rounded is in [[1/2, 4)]: its
   exponent is -1, 0 or 1, and those of [s] and [th] are at most 0. *)
assert (Hst : 1 - / 8192 <= B2R s * B2R th <= 3) by (split; nra).
destruct (mul_k s th 3 Fs Fth) as (Fp & _ & Bp);
  [rewrite Rabs_pos_eq by lra; lra | lra |].
apply Rabs_le_inv in Bp.
cbn [bpow radix_val radix2 Z.opp] in Bp.
assert (Hp : / 2 <= B2R (mul s th) < 4) by lra.
assert (E1 : (-1 <= Generic.exponent (mul s th))%Z).
{ apply MulRuTiny.exponent_ge; [exact Fp |].
  rewrite Rabs_pos_eq by lra. cbn [bpow radix_val radix2 Z.opp]. lra. }
assert (E2 : (Generic.exponent (mul s th) < 2)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fp | lia |].
  rewrite Rabs_pos_eq by lra. cbn [bpow radix_val radix2 Z.opp]. lra. }
assert (E3 : (Generic.exponent s < 1)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fs | lia |].
  rewrite Rabs_pos_eq by lra. cbn [bpow radix_val radix2 Z.opp]. lra. }
assert (E4 : (Generic.exponent th < 1)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fth | lia |].
  rewrite Rabs_pos_eq by lra. cbn [bpow radix_val radix2 Z.opp]. lra. }
unfold Generic.two_prod_is_exact. cbv zeta.
destruct b; rewrite ?andb_true_iff, ?Z.leb_le; lia.
Qed.

(** [h + l] is [(s + pl) (th + tl)] within [2^-69], and [h] is [h + l]
    rounded to nearest. *)
Lemma fast_exp_prod :
  forall fma s pl th tl,
  is_finite s = true -> is_finite pl = true -> is_finite th = true -> is_finite tl = true ->
  Rabs (B2R s - 1) <= bpow radix2 (-13) ->
  Rabs (B2R pl) <= bpow radix2 (-20) + bpow radix2 (-25) ->
  1 <= B2R th < 2 -> Rabs (B2R tl) <= 3 * bpow radix2 (-52) ->
  3 / 4 <= (B2R s + B2R pl) * (B2R th + B2R tl) <= 2 - bpow radix2 (-15) ->
  let ph := mul s th in
  let low := add (Generic.two_prod_err fma s th ph) (add (mul s tl) (mul pl th)) in
  let h := add ph low in
  let l := add low (sub ph h) in
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < B2R h < 2 /\
  Rabs ((B2R s + B2R pl) * (B2R th + B2R tl) - (B2R h + B2R l)) <= bpow radix2 (-69).
Proof.
intros fma s pl th tl Fs Fpl Fth Ftl Hs Hpl Hth Htl HP.
cbv zeta.
pose proof (prod_exact fma s th Fs Fth Hs Hth) as Hex.
destruct (two_prod_err_correct fma s th Fs Fth Hex) as (Fph & _ & _ & Fe1 & Ee1).
apply Rabs_le_inv in Hs, Hpl, Htl.
cbn [bpow radix_val radix2 Z.opp] in Hs, Hpl, Htl, HP.
(* [ph] is [s th] rounded, and [e1] its exact error [TwoProduct.v]. *)
assert (Hst : 1 - / 8192 <= B2R s * B2R th <= 3) by (split; nra).
destruct (mul_k s th 3 Fs Fth) as (_ & _ & Bph);
  [rewrite Rabs_pos_eq by lra; lra | lra |].
set (ph := mul s th) in *.
set (e1 := Generic.two_prod_err fma s th ph) in *.
(* [a = s tl] rounded, [b = pl th] rounded, [c = a + b] rounded and
   [low = e1 + c] rounded, each with an exact result of at most the
   [K] given to [mul_k] or [add_k]: the error of each is relative. *)
assert (Hstl : Rabs (B2R s * B2R tl) <= bpow radix2 (-50)).
{ eapply Rle_trans;
    [apply (Rabs_mul_le _ _ (1 + / 8192) (3 * / 2 ^ 52)); apply Rabs_le; lra |].
  cbn [bpow radix_val radix2 Z.opp]. lra. }
destruct (mul_k s tl _ Fs Ftl Hstl) as (Fa & _ & Ba);
  [cbn [bpow radix_val radix2 Z.opp]; lra |].
set (a := mul s tl) in *.
assert (Hplth : Rabs (B2R pl * B2R th) <= bpow radix2 (-19) + bpow radix2 (-24)).
{ eapply Rle_trans;
    [apply (Rabs_mul_le _ _ (/ 2 ^ 20 + / 2 ^ 25) 2); apply Rabs_le; lra |].
  cbn [bpow radix_val radix2 Z.opp]. lra. }
destruct (mul_k pl th _ Fpl Fth Hplth) as (Fb & _ & Bb);
  [cbn [bpow radix_val radix2 Z.opp]; lra |].
set (b := mul pl th) in *.
apply Rabs_le_inv in Bph, Hstl, Ba, Hplth, Bb.
cbn [bpow radix_val radix2 Z.opp] in Bph, Hstl, Ba, Hplth, Bb.
destruct (add_k a b (bpow radix2 (-19) + bpow radix2 (-24) + bpow radix2 (-49)) Fa Fb)
  as (Fc & _ & Bc);
  [apply Rabs_le; cbn [bpow radix_val radix2 Z.opp]; lra |
   cbn [bpow radix_val radix2 Z.opp]; lra |].
set (c := add a b) in *.
apply Rabs_le_inv in Bc. cbn [bpow radix_val radix2 Z.opp] in Bc.
destruct (add_k e1 c (bpow radix2 (-19) + bpow radix2 (-24) + bpow radix2 (-48)) Fe1 Fc)
  as (Flow & _ & Blow);
  [apply Rabs_le; cbn [bpow radix_val radix2 Z.opp]; lra |
   cbn [bpow radix_val radix2 Z.opp]; lra |].
set (low := add e1 c) in *.
apply Rabs_le_inv in Blow. cbn [bpow radix_val radix2 Z.opp] in Blow.
(* [h] is [ph + low] rounded; [ph] is at least [1/2] and [|low|] at
   most [2^-18], so Fast2Sum [Dekker] gives [l = ph + low - h]. *)
destruct (add_k ph low 4 Fph Flow) as (Fh & Eh & Bh);
  [apply Rabs_le; lra | lra |].
set (h := add ph low) in *.
apply Rabs_le_inv in Bh. cbn [bpow radix_val radix2 Z.opp] in Bh.
assert (Hle : Rabs (B2R low) <= Rabs (B2R ph)).
{ apply Rabs_le. rewrite Rabs_pos_eq by lra. lra. }
destruct (CancelLanes.fast_two_sum ph low h Fph Flow Hle Fh Eh) as (Fl & El).
set (l := add low (sub ph h)) in *.
assert (Hhl : B2R h + B2R l = B2R ph + B2R low) by lra.
(* [(s + pl) (th + tl) - (ph + low)] is [pl tl] (left out) minus the
   errors of [a], [b], [c] and [low]: [12.375 + 0 + 4.125 + 4.125 +
   4.125] units of [2^-74] and a little more, at most [2^-69]. *)
assert (Hpltl : Rabs (B2R pl * B2R tl) <= (/ 2 ^ 20 + / 2 ^ 25) * (3 * / 2 ^ 52))
  by (apply Rabs_mul_le; apply Rabs_le; lra).
apply Rabs_le_inv in Hpltl.
assert (Hx : (B2R s + B2R pl) * (B2R th + B2R tl) =
             B2R s * B2R th + B2R s * B2R tl + B2R pl * B2R th + B2R pl * B2R tl)
  by ring.
assert (Hd : Rabs ((B2R s + B2R pl) * (B2R th + B2R tl) - (B2R h + B2R l)) <=
             bpow radix2 (-69)).
{ rewrite Hx, Hhl. apply Rabs_le. cbn [bpow radix_val radix2 Z.opp]. lra. }
split; [exact Fh |]. split; [exact Fl |].
split; [rewrite Hhl; exact Eh |].
split; [| exact Hd].
apply Rabs_le_inv in Hd. cbn [bpow radix_val radix2 Z.opp] in Hd.
lra.
Qed.
