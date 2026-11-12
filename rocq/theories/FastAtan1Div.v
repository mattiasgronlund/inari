(** * The quotient of the first stage of the fast path of atan

    The quotient [u = n / d] of [DyadicAtan.fast_atan1] of [Model.v] is
    [uh = RN(nh / dh)] and [ul], the rest of the quotient from the
    remainder [nh - uh dh] ([FastAtan1Rem.atan1_rem]), plus [nl] and
    minus [uh dl], divided by [dh]. It is within [2^-97 |n|] of [n / d]
    ([atan1_div]), and the same with and without an FMA
    ([atan1_div_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error Sterbenz.
From Inari Require Import Model Mpfr Encoding Elementary TwoSum TwoProduct DyDriver NearF64
  FastRound FastRoundErr FastDiv CancelLanes FastHypPos FastAtanTables FastAtanIdent
  FastAtanPoly FastAtanCore FastAtan1Rem.
From Inari Require FastExpErr FastExpReduce ConstTight.

Open Scope R_scope.

(** The triangle inequality in the form the bounds below use. *)
Local Lemma abs_le_sub : forall x y, Rabs x <= Rabs (x - y) + Rabs y.
Proof.
intros x y. pose proof (Rabs_triang (x - y) y) as H.
replace (x - y + y) with x in H by ring. exact H.
Qed.

(** [|x / d| d = |x|] for [d > 0]. *)
Local Lemma abs_div_mul : forall x d, 0 < d -> Rabs (x / d) * d = Rabs x.
Proof.
intros x d Hd. unfold Rdiv. rewrite Rabs_mult, Rabs_inv, (Rabs_pos_eq d) by lra.
field. lra.
Qed.

(** The residual quotient of [fast_atan1], on the hypotheses of
    [FastAtanCore.core_u] but [2^-53] for [2^-52] on [dl], as
    [FastAtanCore.core_den] gives it. [ul] is the rounding error of [uh]
    plus [nl / dh] and [- uh dl / dh], each up to [2^-53 |uh|], so [|ul|]
    reaches about [3 2^-53 |uh|]; [13/8 2^-52] leaves room for the
    roundings of the four operations that compute [ul]. *)
Lemma atan1_div :
  forall fma nh nl dh dl D,
  is_finite nh = true -> is_finite nl = true -> is_finite dh = true -> is_finite dl = true ->
  bpow radix2 (-80) <= Rabs (B2R nh) <= / 64 ->
  Rabs (B2R nl) <= bpow radix2 (-53) * Rabs (B2R nh) ->
  Rabs (B2R nh + B2R nl) <= / 128 + bpow radix2 (-52) ->
  1 <= B2R dh <= 41 / 20 -> Rabs (B2R dl) <= bpow radix2 (-53) * B2R dh ->
  1 + bpow radix2 (-14) <= D -> Rabs (B2R dh + B2R dl - D) <= bpow radix2 (-103) ->
  let uh := div nh dh in
  let q := mul uh dh in
  let ul := div (sub (add (sub (sub nh q) (Generic.two_prod_err fma uh dh q)) nl) (mul uh dl)) dh in
  is_finite uh = true /\ is_finite ul = true /\
  bpow radix2 (-82) <= Rabs (B2R uh) <= bpow radix2 (-7) /\
  Rabs (B2R ul) <= 13 / 8 * bpow radix2 (-52) * Rabs (B2R uh) /\
  Rabs (B2R uh + B2R ul) <= bpow radix2 (-7) * (1 - bpow radix2 (-16)) /\
  Rabs (B2R uh + B2R ul - (B2R nh + B2R nl) / D) <= bpow radix2 (-97) * Rabs (B2R nh + B2R nl).
Proof.
intros fma nh nl dh dl D Fnh Fnl Fdh Fdl HN HL HS Hdh Hdl HD Ed.
cbv zeta.
assert (K : bpow radix2 (-53) = / 9007199254740992 /\ bpow radix2 (-52) = / 4503599627370496 /\
  bpow radix2 (-80) = / 1208925819614629174706176 /\
  bpow radix2 (-82) = / 4835703278458516698824704 /\
  bpow radix2 (-97) = / 158456325028528675187087900672 /\
  bpow radix2 (-103) = / 10141204801825835211973625643008 /\
  bpow radix2 (-7) = / 128 /\ bpow radix2 (-16) = / 65536 /\ bpow radix2 (-14) = / 16384)
  by (repeat split; reflexivity).
destruct K as (K53 & K52 & K80 & K82 & K97 & K103 & K7 & K16 & K14).
pose proof (bpow_gt_0 radix2 (-1075)) as W0.
assert (W1 : bpow radix2 (-1075) <=
  / 1606938044258990275541962092341162602522202993782792835301376).
{ apply Rle_trans with (bpow radix2 (-200)); [apply bpow_le; lia|].
  change (bpow radix2 (-200))
    with (/ 1606938044258990275541962092341162602522202993782792835301376). lra. }
(* [uh = RN(nh / dh)], and the remainder [a = nh - uh dh] is exact. *)
assert (H1 : bpow radix2 (-80) <= Rabs (B2R nh) <= 4) by lra.
assert (H2 : / 2 <= B2R dh <= bpow radix2 54).
{ split; [lra|]. apply Rle_trans with 4; [lra|].
  change 4 with (bpow radix2 2). apply bpow_le. lia. }
destruct (atan1_rem fma nh dh Fnh Fdh H1 H2) as (Fuh & Ruh & _ & Epe & Fa & Ea).
clear H1 H2.
rewrite Epe. clear Epe.
set (uh := div nh dh) in *.
set (a := sub (sub nh (mul uh dh)) (Generic.two_prod_err false uh dh (mul uh dh))) in *.
rewrite K53 in HL, Hdl.
(* [|nh| (1 - 2^-53) <= |nh + nl|], and [dh (1 + 2^-53) >= dh + dl >= D - 2^-103]. *)
assert (T0 : Rabs (B2R nh) <= Rabs (B2R nh + B2R nl) + Rabs (B2R nl)).
{ pose proof (abs_le_sub (B2R nh) (- B2R nl)) as T.
  replace (B2R nh - - B2R nl) with (B2R nh + B2R nl) in T by ring.
  rewrite Rabs_Ropp in T. exact T. }
assert (Hdh1 : 1 + / 16384 - / 10141204801825835211973625643008 <=
  B2R dh * (1 + / 9007199254740992)).
{ apply Rabs_le_inv in Ed. apply Rabs_le_inv in Hdl. lra. }
(* So [2^-82 <= |nh / dh| <= 2^-7], and the same for [uh]. *)
pose proof (abs_div_mul (B2R nh) (B2R dh) ltac:(lra)) as HZ.
assert (HZ7 : Rabs (B2R nh / B2R dh) <= / 128).
{ apply (Rmult_le_reg_r (B2R dh)); [lra|]. rewrite HZ. lra. }
assert (HZ82 : / 4835703278458516698824704 <= Rabs (B2R nh / B2R dh)).
{ apply (Rmult_le_reg_r (B2R dh)); [lra|]. rewrite HZ. lra. }
assert (Huh : bpow radix2 (-82) <= Rabs (B2R uh) <= bpow radix2 (-7)).
{ rewrite Ruh. split.
  - apply abs_round_ge_generic; [typeclasses eauto .. | | lra].
    apply generic_format_bpow. unfold FLT_exp. lia.
  - apply abs_round_le_generic; [typeclasses eauto .. | | lra].
    apply generic_format_bpow. unfold FLT_exp. lia. }
assert (B1022 : bpow radix2 (-1022) <= Rabs (B2R uh)).
{ apply Rle_trans with (2 := proj1 Huh). apply bpow_le. lia. }
pose proof (low_rel _ uh Ruh B1022) as Hz.
rewrite K53 in Hz.
(* [M = |uh| dh], the magnitude the bounds below are relative to:
   [|a| <= 2^-53 M], and [|nh|] is [M] up to [2^-53 M]. *)
set (M := Rabs (B2R uh) * B2R dh).
assert (HP : Rabs (B2R uh * B2R dh) = M).
{ unfold M. rewrite Rabs_mult, (Rabs_pos_eq (B2R dh)) by lra. reflexivity. }
assert (HM : Rabs (B2R uh) <= M <= 41 / 20 * Rabs (B2R uh)).
{ unfold M. split.
  - rewrite <- (Rmult_1_r (Rabs (B2R uh))) at 1.
    apply Rmult_le_compat_l; [apply Rabs_pos | lra].
  - rewrite Rmult_comm. apply Rmult_le_compat_r; [apply Rabs_pos | lra]. }
assert (Ha : Rabs (B2R a) <= / 9007199254740992 * M).
{ rewrite Ea.
  replace (B2R nh - B2R uh * B2R dh) with (B2R dh * (B2R nh / B2R dh - B2R uh))
    by (field; lra).
  rewrite Rabs_mult, (Rabs_pos_eq (B2R dh)) by lra. unfold M.
  replace (/ 9007199254740992 * (Rabs (B2R uh) * B2R dh))
    with (B2R dh * (/ 9007199254740992 * Rabs (B2R uh))) by ring.
  apply Rmult_le_compat_l; [lra | exact Hz]. }
assert (T2 : Rabs (B2R nh) <= Rabs (B2R a) + M).
{ rewrite <- HP. replace (B2R nh) with (B2R a + B2R uh * B2R dh) by (rewrite Ea; ring).
  apply Rabs_triang. }
assert (T3 : M <= Rabs (B2R nh) + Rabs (B2R a)).
{ rewrite <- HP. pose proof (abs_le_sub (B2R uh * B2R dh) (B2R nh)) as T.
  replace (B2R uh * B2R dh - B2R nh) with (- B2R a) in T by (rewrite Ea; ring).
  rewrite Rabs_Ropp in T. lra. }
assert (HM0 : / 4835703278458516698824704 <= M) by lra.
(* [c = RN(uh dl)], [|uh dl| <= 2^-53 M]. *)
assert (Hc0 : Rabs (B2R uh * B2R dl) <= / 9007199254740992 * M).
{ rewrite Rabs_mult. unfold M.
  replace (/ 9007199254740992 * (Rabs (B2R uh) * B2R dh))
    with (Rabs (B2R uh) * (/ 9007199254740992 * B2R dh)) by ring.
  apply Rmult_le_compat_l; [apply Rabs_pos | exact Hdl]. }
destruct (FastExpErr.mul_k uh dl _ Fuh Fdl Hc0 ltac:(lra)) as (Fc & _ & Ec).
rewrite K53 in Ec.
set (c := mul uh dl) in *.
(* [b = RN(a + nl)], [|a + nl| <= 2.01 2^-53 M]. *)
assert (Hb0 : Rabs (B2R a + B2R nl) <= / 9007199254740992 * (201 / 100) * M).
{ eapply Rle_trans; [apply Rabs_triang|]. lra. }
destruct (FastExpErr.add_k a nl _ Fa Fnl Hb0 ltac:(lra)) as (Fb & _ & Eb).
rewrite K53 in Eb.
set (b := add a nl) in *.
(* [r = RN(b - c)], [|b - c| <= 3.02 2^-53 M]. *)
assert (Hr0 : Rabs (B2R b - B2R c) <= / 9007199254740992 * (151 / 50) * M).
{ apply Rabs_le_inv in Eb. apply Rabs_le_inv in Ec.
  apply Rabs_le_inv in Hb0. apply Rabs_le_inv in Hc0. apply Rabs_le. lra. }
destruct (FastExpErr.sub_k b c _ Fb Fc Hr0 ltac:(lra)) as (Fr & _ & Er).
rewrite K53 in Er.
set (r := sub b c) in *.
assert (Hr : Rabs (B2R r) <= / 9007199254740992 * (303 / 100) * M).
{ pose proof (abs_le_sub (B2R r) (B2R b - B2R c)). lra. }
(* [ul = RN(r / dh)], [|r / dh| <= 3.03 2^-53 |uh|], so [|ul| <= 3.04 2^-53 |uh|]. *)
pose proof (abs_div_mul (B2R r) (B2R dh) ltac:(lra)) as HR.
assert (Hrd : Rabs (B2R r / B2R dh) <= / 9007199254740992 * (303 / 100) * Rabs (B2R uh)).
{ apply (Rmult_le_reg_r (B2R dh)); [lra|]. rewrite HR.
  replace (/ 9007199254740992 * (303 / 100) * Rabs (B2R uh) * B2R dh)
    with (/ 9007199254740992 * (303 / 100) * M) by (unfold M; ring).
  exact Hr. }
destruct (FastDiv.div_e r dh Fr Fdh ltac:(lra) ltac:(lra)) as (Ful & Rul).
pose proof (FastExpErr.rn_err (B2R r / B2R dh)) as Eul.
rewrite <- Rul in Eul.
pose proof (FastDiv.mul_div_err (B2R (div r dh)) (B2R r) (B2R dh) ltac:(lra) Eul) as Ediv.
rewrite K53 in Eul, Ediv.
set (ul := div r dh) in *.
assert (Hul : Rabs (B2R ul) <= / 9007199254740992 * (304 / 100) * Rabs (B2R uh)).
{ pose proof (abs_le_sub (B2R ul) (B2R r / B2R dh)). lra. }
assert (Wd : bpow radix2 (-1075) * B2R dh <= bpow radix2 (-1075) * (41 / 20))
  by (apply Rmult_le_compat_l; lra).
assert (Huldl : Rabs (B2R ul * B2R dl) <=
  / 9007199254740992 * (304 / 100) * / 9007199254740992 * M).
{ rewrite Rabs_mult. unfold M.
  replace (/ 9007199254740992 * (304 / 100) * / 9007199254740992 * (Rabs (B2R uh) * B2R dh))
    with ((/ 9007199254740992 * (304 / 100) * Rabs (B2R uh)) * (/ 9007199254740992 * B2R dh))
    by ring.
  apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hul | exact Hdl]. }
(* [E = (uh + ul) (dh + dl) - (nh + nl)] is the sum of the four rounding
   errors (of [b], [c], [r] and [ul], the last one times [dh]) and [ul dl]:
   at most (2.01 + 1 + 3.02 + 3.03 + 3.04) 2^-106 M. *)
assert (HE : (B2R uh + B2R ul) * (B2R dh + B2R dl) - (B2R nh + B2R nl) =
  (B2R b - (B2R a + B2R nl)) - (B2R c - B2R uh * B2R dl) + (B2R r - (B2R b - B2R c)) +
  (B2R ul * B2R dh - B2R r) + B2R ul * B2R dl) by (rewrite Ea; ring).
assert (HEb : Rabs ((B2R uh + B2R ul) * (B2R dh + B2R dl) - (B2R nh + B2R nl)) <=
  13 * / 81129638414606681695789005144064 * M).
{ rewrite HE.
  apply Rabs_le_inv in Eb. apply Rabs_le_inv in Ec. apply Rabs_le_inv in Er.
  apply Rabs_le_inv in Ediv. apply Rabs_le_inv in Huldl. apply Rabs_le. lra. }
set (N := B2R nh + B2R nl) in *.
set (Dp := B2R dh + B2R dl) in *.
set (S := B2R uh + B2R ul) in *.
(* [(S - N / D) D Dp = E D + N (D - Dp)] with [D, Dp >= 1], so
   [|S - N / D| <= |E| + 2^-103 |N|]. *)
assert (HDp : 1 <= Dp) by (apply Rabs_le_inv in Ed; lra).
assert (HXD : (S - N / D) * (D * Dp) = (S * Dp - N) * D + N * (D - Dp)) by (field; lra).
assert (HX : Rabs (S - N / D) * (D * Dp) <=
  (Rabs (S * Dp - N) + / 10141204801825835211973625643008 * Rabs N) * D).
{ rewrite <- (Rabs_pos_eq (D * Dp)) by (apply Rmult_le_pos; lra).
  rewrite <- Rabs_mult, HXD.
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite !Rabs_mult, (Rabs_pos_eq D) by lra.
  assert (E1 : Rabs (D - Dp) <= / 10141204801825835211973625643008)
    by (rewrite Rabs_minus_sym; lra).
  assert (E2 : Rabs N * Rabs (D - Dp) <= Rabs N * / 10141204801825835211973625643008)
    by (apply Rmult_le_compat_l; [apply Rabs_pos | exact E1]).
  assert (E3 : Rabs N * 1 <= Rabs N * D) by (apply Rmult_le_compat_l; [apply Rabs_pos | lra]).
  lra. }
assert (HX2 : Rabs (S - N / D) <=
  Rabs (S * Dp - N) + / 10141204801825835211973625643008 * Rabs N).
{ assert (HX1 : Rabs (S - N / D) * Dp <=
    Rabs (S * Dp - N) + / 10141204801825835211973625643008 * Rabs N).
  { apply (Rmult_le_reg_r D); [lra|].
    replace (Rabs (S - N / D) * Dp * D) with (Rabs (S - N / D) * (D * Dp)) by ring.
    exact HX. }
  assert (Rabs (S - N / D) * 1 <= Rabs (S - N / D) * Dp)
    by (apply Rmult_le_compat_l; [apply Rabs_pos | exact HDp]).
  lra. }
(* [M (1 - 2^-53)^2 <= |N|]: [|E| + 2^-103 |N| <= 21.1 2^-106 |N| <= 2^-97 |N|]. *)
assert (Hfin : Rabs (S - N / D) <= / 158456325028528675187087900672 * Rabs N) by lra.
split; [exact Fuh|]. split; [exact Ful|]. split; [exact Huh|].
split.
{ rewrite K52. lra. }
split; [|rewrite K97; exact Hfin].
(* [|S| <= |N| / D + 2^-97 |N|] with [D >= 1 + 2^-14]. *)
pose proof (abs_div_mul N D ltac:(lra)) as HND.
assert (HND1 : Rabs (N / D) * (1 + / 16384) <= Rabs (N / D) * D)
  by (apply Rmult_le_compat_l; [apply Rabs_pos | lra]).
pose proof (abs_le_sub S (N / D)) as HSN.
rewrite K7, K16. lra.
Qed.

Lemma atan1_div_fma :
  forall nh dh,
  is_finite nh = true -> is_finite dh = true ->
  bpow radix2 (-80) <= Rabs (B2R nh) <= / 64 -> 1 <= B2R dh <= 41 / 20 ->
  Generic.two_prod_err true (div nh dh) dh (mul (div nh dh) dh) =
  Generic.two_prod_err false (div nh dh) dh (mul (div nh dh) dh).
Proof.
intros nh dh Fnh Fdh HN Hdh.
assert (H1 : bpow radix2 (-80) <= Rabs (B2R nh) <= 4) by lra.
assert (H2 : / 2 <= B2R dh <= bpow radix2 54).
{ split; [lra|]. apply Rle_trans with 4; [lra|].
  change 4 with (bpow radix2 2). apply bpow_le. lia. }
destruct (atan1_rem true nh dh Fnh Fdh H1 H2) as (_ & _ & _ & E & _).
exact E.
Qed.
