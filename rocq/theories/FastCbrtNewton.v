(** * The last Newton step of [cbrt], on real numbers

    For [Z >= 1] and [y > 0] with [|y^3 - Z| <= 2^-32 + 2^-48], one
    Newton step [y - y (y^3 - Z) / (3 Z)] is within 2^-66 of [Rcbrt Z]
    ([cbrt_newton]). The roundings of that step in [FastCbrtStep.v], each
    within [2^-53 |v| + 2^-1075] of its exact value [v], and an error
    [eta] of at most 2^-100 in [y^3], move its correction by at most
    2^-82 ([cbrt_step_err]). [q] is the [f64] nearest 1/3, 1/3 - 2^-54/3. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core.
From Inari Require Import Elementary RootReal.

Open Scope R_scope.

Theorem cbrt_newton :
  forall Z y,
  1 <= Z -> 0 < y ->
  Rabs (y * (y * y) - Z) <= bpow radix2 (-32) + bpow radix2 (-48) ->
  Rabs (y - y * (y * (y * y) - Z) / (3 * Z) - Rcbrt Z) <= bpow radix2 (-66).
Proof.
intros Z y HZ Hy Hd.
assert (Hk32 : bpow radix2 (-32) = / 4294967296) by reflexivity.
assert (Hk48 : bpow radix2 (-48) = / 281474976710656) by reflexivity.
assert (Hk66 : bpow radix2 (-66) = / 73786976294838206464) by reflexivity.
rewrite Hk32, Hk48 in Hd. rewrite Hk66. clear Hk32 Hk48 Hk66.
pose proof (Rcbrt_cube Z) as Hc3.
set (c := Rcbrt Z) in *. clearbody c. subst Z.
(* [c >= 1]: otherwise [1 - c^3 = (1 - c) (c^2 + c + 1) > 0]. *)
assert (Hc1 : 1 <= c).
{ destruct (Rle_or_lt 1 c) as [H | H]; [exact H |].
  pose proof (Rle_0_sqr (c + / 2)) as Hs. unfold Rsqr in Hs.
  assert (0 < (1 - c) * (c * c + c + 1)) by (apply Rmult_lt_0_compat; lra).
  lra. }
assert (Hc0 : c <> 0) by lra.
(* Write [y = c (1 + u)]. *)
set (u := y / c - 1).
assert (Hyu : y = c * (1 + u)) by (unfold u; field; exact Hc0).
clearbody u. subst y.
(* [y^3 - c^3 = c^3 u (3 + 3u + u^2)], and the step leaves
   [- c u^2 (2 + 4u/3 + u^2/3)]. *)
assert (HD : c * (1 + u) * (c * (1 + u) * (c * (1 + u))) - c * c * c
             = c * c * c * u * (3 + 3 * u + u * u)) by ring.
rewrite HD in Hd |- *.
match goal with |- Rabs ?x <= _ =>
  replace x with (- (c * (u * u) * (2 + 4 / 3 * u + u * u / 3)))
    by (field; exact Hc0)
end.
rewrite Rabs_Ropp.
pose proof (Rle_0_sqr (u + 3 / 2)) as Hs. unfold Rsqr in Hs.
pose proof (Rle_0_sqr u) as Huu. unfold Rsqr in Huu.
assert (Hul : - Rabs u <= u <= Rabs u)
  by (unfold Rabs; destruct (Rcase_abs u); lra).
assert (Hau : Rabs u * Rabs u = u * u)
  by (unfold Rabs; destruct (Rcase_abs u); ring).
set (Q := 3 + 3 * u + u * u) in *.
(* [3 + 3u + u^2 = (u + 3/2)^2 + 3/4]. *)
assert (HQ : 3 / 4 <= Q) by (unfold Q; lra).
rewrite Rabs_mult, Rabs_mult, (Rabs_pos_eq (c * c * c)), (Rabs_pos_eq Q) in Hd
  by lra.
assert (Hw0 : 0 <= c * c * c * Rabs u)
  by (apply Rmult_le_pos; [lra | apply Rabs_pos]).
(* A first bound [c^3 |u| <= (4/3) (2^-32 + 2^-48)] gives [|u| <= 2^-30]. *)
assert (Hw1 : c * c * c * Rabs u * (3 / 4) <= c * c * c * Rabs u * Q)
  by (apply Rmult_le_compat_l; lra).
assert (Huw : 1 * Rabs u <= c * c * c * Rabs u)
  by (apply Rmult_le_compat_r; [apply Rabs_pos | lra]).
assert (Hu30 : Rabs u <= / 1073741824) by lra.
(* Then [Q >= 3 - 3 * 2^-30] gives [c^3 |u| <= 0.33334 * 2^-32]. *)
assert (HQ2 : 3 - 3 * / 1073741824 <= Q) by (unfold Q; lra).
assert (Hw2 : c * c * c * Rabs u * (3 - 3 * / 1073741824)
              <= c * c * c * Rabs u * Q)
  by (apply Rmult_le_compat_l; lra).
assert (Hw : c * c * c * Rabs u <= 33334 / 100000 * / 4294967296) by lra.
(* [c u^2 <= c^6 u^2 = (c^3 |u|)^2], as [c >= 1]. *)
assert (Hc6 : c <= c * c * c * (c * c * c)).
{ assert (c * 1 <= c * c) by (apply Rmult_le_compat_l; lra).
  assert (c * c * 1 <= c * c * c)
    by (apply Rmult_le_compat_l; [apply Rmult_le_pos | ]; lra).
  assert (c * c * c * 1 <= c * c * c * (c * c * c))
    by (apply Rmult_le_compat_l; lra).
  lra. }
assert (Hcu : c * (u * u) <= (c * c * c * Rabs u) * (c * c * c * Rabs u)).
{ replace ((c * c * c * Rabs u) * (c * c * c * Rabs u))
    with (c * c * c * (c * c * c) * (u * u)) by (rewrite <- Hau; ring).
  apply Rmult_le_compat_r; lra. }
assert (Hww : (c * c * c * Rabs u) * (c * c * c * Rabs u)
              <= (33334 / 100000 * / 4294967296) * (33334 / 100000 * / 4294967296))
  by (apply Rmult_le_compat; lra).
(* [|2 + 4u/3 + u^2/3| <= 2 + 5|u|/3 <= 2 + 8 * 2^-32]. *)
assert (Huu1 : Rabs u * Rabs u <= 1 * Rabs u)
  by (apply Rmult_le_compat_r; [apply Rabs_pos | lra]).
assert (HP0 : 0 <= 2 + 4 / 3 * u + u * u / 3) by lra.
assert (HP : 2 + 4 / 3 * u + u * u / 3 <= 2 + 8 / 4294967296) by lra.
rewrite Rabs_mult, Rabs_mult, (Rabs_pos_eq c), (Rabs_pos_eq (u * u)),
  (Rabs_pos_eq (2 + 4 / 3 * u + u * u / 3)) by lra.
assert (Hfin : c * (u * u) * (2 + 4 / 3 * u + u * u / 3)
               <= (33334 / 100000 * / 4294967296) * (33334 / 100000 * / 4294967296)
                  * (2 + 8 / 4294967296))
  by (apply Rmult_le_compat; [apply Rmult_le_pos | | | ]; lra).
lra.
Qed.

(** Triangle-inequality helpers for the bounds of [cbrt_step_err]. *)
Local Lemma abs_from_err :
  forall X v a b, Rabs (X - v) <= a * Rabs v + b -> Rabs X <= (1 + a) * Rabs v + b.
Proof.
intros X v a b H. pose proof (Rabs_triang (X - v) v) as T.
replace (X - v + v) with X in T by ring. lra.
Qed.

Local Lemma abs_mul_le :
  forall a b A B, Rabs a <= A -> Rabs b <= B -> Rabs (a * b) <= A * B.
Proof.
intros a b A B Ha Hb. rewrite Rabs_mult.
apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Ha | exact Hb].
Qed.

Local Lemma abs_sum3 : forall a b c, Rabs (a + b + c) <= Rabs a + Rabs b + Rabs c.
Proof.
intros a b c. pose proof (Rabs_triang (a + b) c). pose proof (Rabs_triang a b). lra.
Qed.

Local Lemma abs_sum5 :
  forall a b c d e,
  Rabs (a + b + c + d + e) <= Rabs a + Rabs b + Rabs c + Rabs d + Rabs e.
Proof.
intros a b c d e.
pose proof (Rabs_triang (a + b + c + d) e). pose proof (Rabs_triang (a + b + c) d).
pose proof (Rabs_triang (a + b) c). pose proof (Rabs_triang a b). lra.
Qed.

Theorem cbrt_step_err :
  forall Y Z R S HH T DY D eta,
  999 / 1000 <= Y <= 2001 / 1000 -> 1 <= Z ->
  Rabs (R - / Z) <= bpow radix2 (-53) * / Z ->
  Rabs D <= bpow radix2 (-32) + bpow radix2 (-48) ->
  Rabs eta <= bpow radix2 (-100) ->
  Rabs (S - (D + eta)) <= bpow radix2 (-53) * Rabs (D + eta) + bpow radix2 (-1075) ->
  Rabs (HH - S * R) <= bpow radix2 (-53) * Rabs (S * R) + bpow radix2 (-1075) ->
  Rabs (T - Y * (6004799503160661 * bpow radix2 (-54)))
    <= bpow radix2 (-53) * Rabs (Y * (6004799503160661 * bpow radix2 (-54)))
       + bpow radix2 (-1075) ->
  Rabs (DY - HH * T) <= bpow radix2 (-53) * Rabs (HH * T) + bpow radix2 (-1075) ->
  Rabs DY <= / 2 /\ Rabs (DY - Y * D / (3 * Z)) <= bpow radix2 (-82).
Proof.
intros Y Z R S HH T DY D eta HY HZ HR HD Heta HS HHH HT HDY.
assert (E32 : bpow radix2 (-32) = / 4294967296) by reflexivity.
assert (E48 : bpow radix2 (-48) = / 281474976710656) by reflexivity.
assert (E53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
assert (E54 : bpow radix2 (-54) = / 18014398509481984) by reflexivity.
assert (E82 : bpow radix2 (-82) = / 4835703278458516698824704) by reflexivity.
assert (E100 : bpow radix2 (-100) = / 1267650600228229401496703205376)
  by reflexivity.
assert (Hm : 0 <= bpow radix2 (-1075) <= bpow radix2 (-100))
  by (split; [apply bpow_ge_0 | apply bpow_le; lia]).
rewrite E100 in Heta, Hm. rewrite E32, E48 in HD. rewrite E82.
rewrite E53 in HR, HS, HHH, HT, HDY.
set (m := bpow radix2 (-1075)) in *. clearbody m.
(* [q], the [f64] nearest 1/3, is [1/3 - 2^-54/3]. *)
set (q := 6004799503160661 * bpow radix2 (-54)) in *.
assert (Hq : q = 6004799503160661 / 18014398509481984)
  by (unfold q; rewrite E54; reflexivity).
clearbody q. clear E32 E48 E53 E54 E82 E100.
assert (HZ0 : Z <> 0) by lra.
assert (HZi : Z * / Z = 1) by (field; exact HZ0).
assert (HiZ0 : 0 < / Z) by (apply Rinv_0_lt_compat; lra).
assert (HiZ1 : / Z <= 1) by nra.
(* Bounds on the inputs and the intermediate values. *)
assert (BRZ : Rabs (R - / Z) <= / 9007199254740992) by lra.
assert (BR : Rabs R <= 10001 / 10000).
{ pose proof (Rabs_triang (R - / Z) (/ Z)) as T1.
  replace (R - / Z + / Z) with R in T1 by ring.
  rewrite (Rabs_pos_eq (/ Z)) in T1 by lra. lra. }
assert (BD : Rabs D <= 10001 / 10000 * / 4294967296) by lra.
assert (BDe : Rabs (D + eta) <= 10002 / 10000 * / 4294967296)
  by (pose proof (Rabs_triang D eta); lra).
assert (BS : Rabs S <= 10003 / 10000 * / 4294967296)
  by (pose proof (abs_from_err _ _ _ _ HS); lra).
pose proof (abs_mul_le _ _ _ _ BS BR) as BSR.
assert (BHH : Rabs HH <= 10006 / 10000 * / 4294967296)
  by (pose proof (abs_from_err _ _ _ _ HHH); lra).
assert (BYq : Rabs (Y * q) <= 6671 / 10000)
  by (rewrite Hq; rewrite Rabs_pos_eq by lra; lra).
assert (BT : Rabs T <= 6672 / 10000)
  by (pose proof (abs_from_err _ _ _ _ HT); lra).
pose proof (abs_mul_le _ _ _ _ BHH BT) as BHT.
split.
{ pose proof (abs_from_err _ _ _ _ HDY). lra. }
(* Split the error of [DY] into the roundings, [eta], the error of [R] and
   the error of [q]. *)
assert (Hid : DY - Y * D / (3 * Z)
  = (DY - HH * T) + (HH - S * R) * T + S * R * (T - Y * q)
    + Y * q * ((S - (D + eta)) * R + eta * R + D * (R - / Z))
    + Y * D / Z * (q - / 3)) by (field; exact HZ0).
rewrite Hid. eapply Rle_trans; [apply abs_sum5 |].
assert (T1 : Rabs (DY - HH * T)
             <= / 9007199254740992 * (10006 / 10000 * / 4294967296 * (6672 / 10000))
                + m) by lra.
assert (BHSR : Rabs (HH - S * R)
               <= / 9007199254740992 * (10003 / 10000 * / 4294967296 * (10001 / 10000))
                  + m) by lra.
pose proof (abs_mul_le _ _ _ _ BHSR BT) as T2.
assert (BTq : Rabs (T - Y * q) <= / 9007199254740992 * (6671 / 10000) + m) by lra.
pose proof (abs_mul_le _ _ _ _ BSR BTq) as T3.
assert (BSD : Rabs (S - (D + eta))
              <= / 9007199254740992 * (10002 / 10000 * / 4294967296) + m) by lra.
pose proof (abs_mul_le _ _ _ _ BSD BR) as T4a.
pose proof (abs_mul_le _ _ _ _ Heta BR) as T4b.
pose proof (abs_mul_le _ _ _ _ BD BRZ) as T4c.
pose proof (abs_sum3 ((S - (D + eta)) * R) (eta * R) (D * (R - / Z))) as T4d.
assert (T4in : Rabs ((S - (D + eta)) * R + eta * R + D * (R - / Z))
  <= (/ 9007199254740992 * (10002 / 10000 * / 4294967296) + m) * (10001 / 10000)
     + / 1267650600228229401496703205376 * (10001 / 10000)
     + 10001 / 10000 * / 4294967296 * / 9007199254740992) by lra.
pose proof (abs_mul_le _ _ _ _ BYq T4in) as T4.
assert (Hq3 : Rabs (q - / 3) <= / 54043195528445952)
  by (rewrite Hq; apply Rabs_le; lra).
assert (BYD : Rabs (Y * D / Z) <= 2001 / 1000 * (10001 / 10000 * / 4294967296) * 1).
{ change (Y * D / Z) with (Y * D * / Z).
  apply abs_mul_le; [apply abs_mul_le |].
  - rewrite Rabs_pos_eq; lra.
  - exact BD.
  - rewrite Rabs_pos_eq; lra. }
pose proof (abs_mul_le _ _ _ _ BYD Hq3) as T5.
lra.
Qed.
