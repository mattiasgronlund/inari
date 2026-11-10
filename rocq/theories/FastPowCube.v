(** * The cube of the polynomial of the logarithm of x^y

    [DyadicLog.log1p_poly_acc] of [Model.v] computes [z1^3 / 3] in
    double-double: [z1^2] is exact as [sh + sl] and [z1 sh] as [ch] plus
    its error (TwoProduct, [TwoProduct.v]), so that [ch + cl] is [z1^3]
    up to the roundings of [z1 sl] and of [cl]; [ch Q3] is exact as [dh]
    plus its error, so that [dh + dl] is [z1^3 / 3] up to the roundings
    of [cl Q3], [ch Q3L] and the two sums of [dl], with [Q3 + Q3L]
    within [2^-109] of 1/3. [log1p_cube_correct] bounds them for
    [2^-200 <= |z1| <= 2^-9], where no product is subnormal, and
    [log1p_cube_fma] shows that the three products are exact either way,
    so that an FMA gives the same errors. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Relative.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct FastRound FastExpErr.
From Inari Require MulRuTiny.

Open Scope R_scope.

(** ** Helpers (as in [FastPowPoly.v]) *)

(** [B2R l] of an [f64] literal [l], as [m * 2^e] (as in [FastExp.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** Powers of 2 as numerals, for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp] in *.

(** [Q3] is [(2^54 - 1) / 3 * 2^-54] and [Q3L] is [(2^54 - 1) / 3 * 2^-108],
    so that [Q3 + Q3L = 1/3 - 2^-108/3]. *)
Local Lemma q3_F :
  is_finite (from_bits DyadicLog.Q3) = true /\
  B2R (from_bits DyadicLog.Q3) = 6004799503160661 * bpow radix2 (-54).
Proof.
split; [vm_compute; reflexivity|]. lit_B2R. reflexivity.
Qed.

Local Lemma q3l_F :
  is_finite (from_bits DyadicLog.Q3L) = true /\
  B2R (from_bits DyadicLog.Q3L) = 6004799503160661 * bpow radix2 (-108).
Proof.
split; [vm_compute; reflexivity|]. lit_B2R. reflexivity.
Qed.

(** Rounding to nearest of an [x] of at least [2^-1022] in magnitude moves
    it by at most [2^-53 |x|] (as in [FastSinhHorner.v]). *)
Local Lemma rn_rel :
  forall x, bpow radix2 (-1022) <= Rabs x -> Rabs (RN x - x) <= bpow radix2 (-53) * Rabs x.
Proof.
intros x Hx.
assert (H : Rabs (RN x - x) <= / 2 * bpow radix2 (- 53 + 1) * Rabs x)
  by exact (relative_error_N_FLT radix2 (-1074) 53 eq_refl (fun z => negb (Z.even z)) x Hx).
change (- 53 + 1)%Z with (-52)%Z in H.
assert (E : / 2 * bpow radix2 (-52) = bpow radix2 (-53))
  by (cbn [bpow radix_val radix2]; lra).
rewrite E in H. exact H.
Qed.

(** [add_k] and [mul_k] of [FastExpErr.v] for a named result [z], with the
    error as two inequalities for [lra] (as in [FastPowPoly.v]). *)
Local Lemma add_kz :
  forall x y z K, z = add x y -> is_finite x = true -> is_finite y = true ->
  Rabs (B2R x + B2R y) <= K -> K <= 16 ->
  is_finite z = true /\
  - (bpow radix2 (-53) * K + bpow radix2 (-1075)) <= B2R z - (B2R x + B2R y) <=
    bpow radix2 (-53) * K + bpow radix2 (-1075).
Proof.
intros x y z K -> Fx Fy H HK.
destruct (add_k x y K Fx Fy H HK) as (F & _ & B).
split; [exact F | apply Rabs_le_inv; exact B].
Qed.

Local Lemma mul_kz :
  forall x y z K, z = mul x y -> is_finite x = true -> is_finite y = true ->
  Rabs (B2R x * B2R y) <= K -> K <= 16 ->
  is_finite z = true /\
  - (bpow radix2 (-53) * K + bpow radix2 (-1075)) <= B2R z - B2R x * B2R y <=
    bpow radix2 (-53) * K + bpow radix2 (-1075).
Proof.
intros x y z K -> Fx Fy H HK.
destruct (mul_k x y K Fx Fy H HK) as (F & _ & B).
split; [exact F | apply Rabs_le_inv; exact B].
Qed.

(** Bounds on [|a b|] from bounds on [|a|] and [|b|]. *)
Local Lemma abs_mul_in :
  forall a b A1 A2 B1 B2, 0 <= A1 -> 0 <= B1 ->
  A1 <= Rabs a <= A2 -> B1 <= Rabs b <= B2 ->
  A1 * B1 <= Rabs (a * b) <= A2 * B2.
Proof.
intros a b A1 A2 B1 B2 HA HB [Ha1 Ha2] [Hb1 Hb2].
rewrite Rabs_mult.
split; apply Rmult_le_compat; lra.
Qed.

(** ** The three products are exact *)

(** The product of two finite [x] and [y] of magnitude at most 1, whose
    exact value is at least [2^-900] in magnitude, is within a factor 2
    of [x y], and TwoProduct is exact for it with and without an FMA: its
    exponent is in [[-901, 1]], and those of [x] and [y] are at most 0. *)
Local Lemma prod_exact :
  forall fma x y, is_finite x = true -> is_finite y = true ->
  Rabs (B2R x) <= 1 -> Rabs (B2R y) <= 1 ->
  bpow radix2 (-900) <= Rabs (B2R x * B2R y) ->
  is_finite (mul x y) = true /\
  Rabs (B2R x * B2R y) / 2 <= Rabs (B2R (mul x y)) <= 2 * Rabs (B2R x * B2R y) /\
  Generic.two_prod_is_exact fma x y (mul x y) = true.
Proof.
intros fma x y Fx Fy Hx Hy Hlo.
assert (Hm : Rabs (B2R x * B2R y) <= 1 * 1)
  by (rewrite Rabs_mult;
      apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hx | exact Hy]).
destruct (mul_e x y Fx Fy ltac:(lra)) as (Fp & _ & Bp).
assert (HT : bpow radix2 (-53) * Rabs (B2R x * B2R y) + bpow radix2 (-1075) <=
  Rabs (B2R x * B2R y) / 2) by (num; lra).
pose proof (Rabs_triang_inv (B2R (mul x y)) (B2R x * B2R y)) as T1.
pose proof (Rabs_triang_inv (B2R x * B2R y) (B2R (mul x y))) as T2.
rewrite Rabs_minus_sym in T2.
assert (B : Rabs (B2R x * B2R y) / 2 <= Rabs (B2R (mul x y)) <= 2 * Rabs (B2R x * B2R y))
  by lra.
split; [exact Fp | split; [exact B |]].
assert (Elo : (-901 <= Generic.exponent (mul x y))%Z).
{ apply MulRuTiny.exponent_ge; [exact Fp|].
  assert (bpow radix2 (-901) = bpow radix2 (-900) / 2) by (num; lra). lra. }
assert (Ehi : (Generic.exponent (mul x y) < 2)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fp | lia |]. num. lra. }
assert (Ex : (Generic.exponent x < 1)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fx | lia |]. num. lra. }
assert (Ey : (Generic.exponent y < 1)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fy | lia |]. num. lra. }
unfold Generic.two_prod_is_exact. cbv zeta.
destruct fma; repeat (apply andb_true_intro; split); apply Z.leb_le; lia.
Qed.

(** The three products of [log1p_poly_acc] are exact for
    [2^-200 <= |z1| <= 2^-9]: their factors are at most 1 in magnitude,
    and their exact values at least [2^-604]. *)
Local Lemma cube_prods :
  forall fma z1, is_finite z1 = true ->
  bpow radix2 (-200) <= Rabs (B2R z1) <= bpow radix2 (-9) ->
  is_finite (mul z1 z1) = true /\ is_finite (mul z1 (mul z1 z1)) = true /\
  Generic.two_prod_is_exact fma z1 z1 (mul z1 z1) = true /\
  Generic.two_prod_is_exact fma z1 (mul z1 z1) (mul z1 (mul z1 z1)) = true /\
  Generic.two_prod_is_exact fma (mul z1 (mul z1 z1)) (from_bits DyadicLog.Q3)
    (mul (mul z1 (mul z1 z1)) (from_bits DyadicLog.Q3)) = true.
Proof.
intros fma z1 Fz HZ.
destruct q3_F as (Fq & Eq).
assert (Z1 : Rabs (B2R z1) <= 1) by (destruct HZ; num; lra).
pose proof (abs_mul_in (B2R z1) (B2R z1) _ _ _ _ (bpow_ge_0 _ _) (bpow_ge_0 _ _) HZ HZ) as A1.
destruct (prod_exact fma z1 z1 Fz Fz Z1 Z1) as (Fsh & Bsh & E1).
{ destruct A1. num. lra. }
set (sh := mul z1 z1) in *.
assert (Bsh' : bpow radix2 (-200) * bpow radix2 (-200) / 2 <= Rabs (B2R sh) <=
  2 * (bpow radix2 (-9) * bpow radix2 (-9))) by lra.
assert (Sh1 : Rabs (B2R sh) <= 1) by (destruct Bsh'; num; lra).
assert (A2 : bpow radix2 (-200) * (bpow radix2 (-200) * bpow radix2 (-200) / 2) <=
  Rabs (B2R z1 * B2R sh) <= bpow radix2 (-9) * (2 * (bpow radix2 (-9) * bpow radix2 (-9)))).
{ apply abs_mul_in; [apply bpow_ge_0 | num; lra | exact HZ | exact Bsh']. }
destruct (prod_exact fma z1 sh Fz Fsh Z1 Sh1) as (Fch & Bch & E2).
{ destruct A2. num. lra. }
set (ch := mul z1 sh) in *.
assert (Ch1 : Rabs (B2R ch) <= 1) by (destruct A2, Bch; num; lra).
assert (Q1 : / 4 <= Rabs (B2R (from_bits DyadicLog.Q3)) <= / 2)
  by (rewrite Eq, Rabs_pos_eq by (num; lra); num; lra).
assert (Q1' : Rabs (B2R (from_bits DyadicLog.Q3)) <= 1) by lra.
assert (Ch2 : bpow radix2 (-602) <= Rabs (B2R ch)) by (destruct A2, Bch; num; lra).
assert (Ch2' : bpow radix2 (-602) <= Rabs (B2R ch) <= 1) by lra.
assert (A3 : bpow radix2 (-602) * / 4 <= Rabs (B2R ch * B2R (from_bits DyadicLog.Q3)) <= 1 * / 2)
  by (apply abs_mul_in; [apply bpow_ge_0 | lra | exact Ch2' | exact Q1]).
destruct (prod_exact fma ch _ Fch Fq Ch1 Q1') as (_ & _ & E3).
{ destruct A3. num. lra. }
split; [exact Fsh | split; [exact Fch | split; [exact E1 | split; [exact E2 | exact E3]]]].
Qed.

(** ** The results *)

(** The products and sums of [log1p_poly_acc] up to [dl], as its
    definition in [Model.v] binds them. *)
Theorem log1p_cube_correct :
  forall fma z1,
  is_finite z1 = true ->
  bpow radix2 (-200) <= Rabs (B2R z1) <= bpow radix2 (-9) ->
  let sh := mul z1 z1 in
  let sl := Generic.two_prod_err fma z1 z1 sh in
  let ch := mul z1 sh in
  let cl := add (Generic.two_prod_err fma z1 sh ch) (mul z1 sl) in
  let dh := mul ch (from_bits DyadicLog.Q3) in
  let dl :=
    add (Generic.two_prod_err fma ch (from_bits DyadicLog.Q3) dh)
      (add (mul cl (from_bits DyadicLog.Q3)) (mul ch (from_bits DyadicLog.Q3L))) in
  is_finite sh = true /\ is_finite sl = true /\ is_finite dh = true /\ is_finite dl = true /\
  B2R sh + B2R sl = B2R z1 ^ 2 /\
  Rabs (B2R sl) <= bpow radix2 (-53) * B2R z1 ^ 2 /\
  Rabs (B2R dh) <= Rabs (B2R z1) ^ 3 / 2 /\
  Rabs (B2R dl) <= bpow radix2 (-51) * Rabs (B2R z1) ^ 3 /\
  Rabs (B2R dh + B2R dl - B2R z1 ^ 3 / 3) <= bpow radix2 (-100) * Rabs (B2R z1) ^ 3.
Proof.
intros fma z1 Fz HZ.
destruct (cube_prods fma z1 Fz HZ) as (Fsh & Fch & T1 & T2 & T3).
destruct q3_F as (Fq & Eq3).
destruct q3l_F as (Fql & Eql).
(* TwoProduct gives [sh = RN(z1^2)], [ch = RN(z1 sh)], [dh = RN(ch Q3)]
   and their errors exactly. *)
destruct (two_prod_err_correct fma z1 z1 Fz Fz T1) as (_ & Rsh & _ & Fsl & Esl).
destruct (two_prod_err_correct fma z1 (mul z1 z1) Fz Fsh T2) as (_ & Rch & _ & Fe1 & Ee1).
destruct (two_prod_err_correct fma _ _ Fch Fq T3) as (Fdh & Rdh & _ & Fe2 & Ee2).
cbv zeta.
set (sh := mul z1 z1) in *.
set (sl := Generic.two_prod_err fma z1 z1 sh) in *.
set (ch := mul z1 sh) in *.
set (e1 := Generic.two_prod_err fma z1 sh ch) in *.
set (m1 := mul z1 sl) in *.
set (cl := add e1 m1) in *.
set (q3 := from_bits DyadicLog.Q3) in *.
set (q3l := from_bits DyadicLog.Q3L) in *.
set (dh := mul ch q3) in *.
set (e2 := Generic.two_prod_err fma ch q3 dh) in *.
set (k2 := mul cl q3) in *.
set (k3 := mul ch q3l) in *.
set (k23 := add k2 k3) in *.
set (dl := add e2 k23) in *.
destruct HZ as [Zlo Zhi].
pose proof (Rabs_pos (B2R z1)) as Z0.
(* [z1^2] and [|z1|^3]. *)
assert (A1 : bpow radix2 (-200) * bpow radix2 (-200) <= Rabs (B2R z1 * B2R z1) <=
  bpow radix2 (-9) * bpow radix2 (-9))
  by (apply abs_mul_in;
      [apply bpow_ge_0 | apply bpow_ge_0 | split; assumption | split; assumption]).
assert (Ez2 : Rabs (B2R z1 * B2R z1) = B2R z1 ^ 2) by (rewrite Rabs_pos_eq by nra; ring).
assert (Z3lo : bpow radix2 (-600) <= Rabs (B2R z1) ^ 3).
{ replace (bpow radix2 (-600)) with (bpow radix2 (-200) ^ 3)
    by (cbn [pow]; rewrite Rmult_1_r, <- !bpow_plus; reflexivity).
  apply pow_incr. split; [apply bpow_ge_0 | exact Zlo]. }
assert (Z3hi : Rabs (B2R z1) ^ 3 <= bpow radix2 (-27)).
{ replace (bpow radix2 (-27)) with (bpow radix2 (-9) ^ 3)
    by (cbn [pow]; rewrite Rmult_1_r, <- !bpow_plus; reflexivity).
  apply pow_incr. split; [exact Z0 | exact Zhi]. }
assert (Ecube : B2R z1 ^ 3 = B2R z1 * B2R sh + B2R z1 * B2R sl) by (rewrite Esl; ring).
set (Z3 := Rabs (B2R z1) ^ 3) in *.
(* [sl] is the rounding error of [z1^2], which is at least [2^-400]. *)
assert (Bsl : Rabs (B2R sl) <= bpow radix2 (-53) * B2R z1 ^ 2).
{ rewrite Esl, Rsh, Rabs_minus_sym, <- Ez2. apply rn_rel. destruct A1. num. lra. }
assert (Esh : B2R sh + B2R sl = B2R z1 ^ 2) by (rewrite Esl; ring).
assert (Bsh : (1 - bpow radix2 (-53)) * B2R z1 ^ 2 <= B2R sh <=
  (1 + bpow radix2 (-53)) * B2R z1 ^ 2) by (pose proof (Rabs_le_inv _ _ Bsl); num; lra).
assert (Bz1sl : Rabs (B2R z1 * B2R sl) <= bpow radix2 (-53) * Z3).
{ rewrite Rabs_mult. unfold Z3.
  replace (bpow radix2 (-53) * Rabs (B2R z1) ^ 3) with
    (Rabs (B2R z1) * (bpow radix2 (-53) * B2R z1 ^ 2))
    by (rewrite <- (pow2_abs (B2R z1)); ring).
  apply Rmult_le_compat_l; [exact Z0 | exact Bsl]. }
assert (Bz1sh : (1 - bpow radix2 (-53)) * Z3 <= Rabs (B2R z1 * B2R sh) <=
  (1 + bpow radix2 (-53)) * Z3).
{ rewrite Rabs_mult, (Rabs_pos_eq (B2R sh))
    by (pose proof (pow2_ge_0 (B2R z1)); destruct Bsh; num; lra).
  unfold Z3. rewrite <- (pow2_abs (B2R z1)) in Bsh.
  replace ((1 - bpow radix2 (-53)) * Rabs (B2R z1) ^ 3) with
    (Rabs (B2R z1) * ((1 - bpow radix2 (-53)) * Rabs (B2R z1) ^ 2)) by ring.
  replace ((1 + bpow radix2 (-53)) * Rabs (B2R z1) ^ 3) with
    (Rabs (B2R z1) * ((1 + bpow radix2 (-53)) * Rabs (B2R z1) ^ 2)) by ring.
  destruct Bsh as [B1 B2].
  split; apply Rmult_le_compat_l; assumption. }
(* [e1] is the rounding error of [z1 sh], which is at least [2^-601]. *)
assert (Be1 : Rabs (B2R e1) <= bpow radix2 (-53) * Rabs (B2R z1 * B2R sh)).
{ rewrite Ee1, Rch, Rabs_minus_sym. apply rn_rel. destruct Bz1sh. num. lra. }
assert (Ch : - ((1 + bpow radix2 (-51)) * Z3) <= B2R ch <= (1 + bpow radix2 (-51)) * Z3).
{ pose proof (Rabs_le_inv _ _ Be1). pose proof (Rabs_le_inv _ _ (proj2 Bz1sh)).
  destruct Bz1sh. num. lra. }
assert (Chlo : Z3 / 2 <= Rabs (B2R ch)).
{ replace (B2R ch) with (B2R z1 * B2R sh - B2R e1) by lra.
  pose proof (Rabs_triang_inv (B2R z1 * B2R sh) (B2R e1)). destruct Bz1sh. num. lra. }
(* [e2] is the rounding error of [ch Q3], which is at least [2^-603]. *)
assert (Bchq : Rabs (B2R ch * B2R q3) = Rabs (B2R ch) * (6004799503160661 * bpow radix2 (-54)))
  by (rewrite Rabs_mult, Eq3, (Rabs_pos_eq (6004799503160661 * _)) by (num; lra); reflexivity).
assert (Bq : Rabs (B2R ch * B2R q3) <=
  (1 + bpow radix2 (-51)) * Z3 * (6004799503160661 * bpow radix2 (-54))).
{ rewrite Bchq. apply Rmult_le_compat_r; [num; lra | apply Rabs_le; exact Ch]. }
assert (Be2 : Rabs (B2R e2) <= bpow radix2 (-53) * Rabs (B2R ch * B2R q3)).
{ rewrite Ee2, Rdh, Rabs_minus_sym. apply rn_rel. rewrite Bchq. num. lra. }
(* The roundings of the low parts. *)
destruct (mul_kz z1 sl m1 (bpow radix2 (-53) * Z3) eq_refl Fz Fsl Bz1sl ltac:(num; lra))
  as (Fm1 & Em1).
assert (Kcl : Rabs (B2R e1 + B2R m1) <= 21 / 10 * bpow radix2 (-53) * Z3).
{ apply Rabs_le. pose proof (Rabs_le_inv _ _ Be1). pose proof (Rabs_le_inv _ _ Bz1sl).
  destruct Bz1sh. num. lra. }
destruct (add_kz e1 m1 cl _ eq_refl Fe1 Fm1 Kcl ltac:(num; lra)) as (Fcl & Ecl).
assert (Cl : - (11 / 5 * bpow radix2 (-53) * Z3) <= B2R cl <= 11 / 5 * bpow radix2 (-53) * Z3)
  by (pose proof (Rabs_le_inv _ _ Kcl); num; lra).
assert (Kk2 : Rabs (B2R cl * B2R q3) <= 3 / 4 * bpow radix2 (-53) * Z3).
{ rewrite Rabs_mult, Eq3, (Rabs_pos_eq (6004799503160661 * _)) by (num; lra).
  assert (Rabs (B2R cl) <= 11 / 5 * bpow radix2 (-53) * Z3) by (apply Rabs_le; exact Cl).
  num. lra. }
destruct (mul_kz cl q3 k2 _ eq_refl Fcl Fq Kk2 ltac:(num; lra)) as (Fk2 & Ek2).
assert (Kk3 : Rabs (B2R ch * B2R q3l) <= / 5 * bpow radix2 (-53) * Z3).
{ rewrite Rabs_mult, Eql, (Rabs_pos_eq (6004799503160661 * _)) by (num; lra).
  assert (Rabs (B2R ch) <= (1 + bpow radix2 (-51)) * Z3) by (apply Rabs_le; exact Ch).
  num. lra. }
destruct (mul_kz ch q3l k3 _ eq_refl Fch Fql Kk3 ltac:(num; lra)) as (Fk3 & Ek3).
assert (Kk23 : Rabs (B2R k2 + B2R k3) <= bpow radix2 (-53) * Z3).
{ apply Rabs_le. pose proof (Rabs_le_inv _ _ Kk2). pose proof (Rabs_le_inv _ _ Kk3).
  num. lra. }
destruct (add_kz k2 k3 k23 _ eq_refl Fk2 Fk3 Kk23 ltac:(num; lra)) as (Fk23 & Ek23).
assert (Kdl : Rabs (B2R e2 + B2R k23) <= 3 / 2 * bpow radix2 (-53) * Z3).
{ apply Rabs_le. pose proof (Rabs_le_inv _ _ Be2). pose proof (Rabs_le_inv _ _ Kk23).
  num. lra. }
destruct (add_kz e2 k23 dl _ eq_refl Fe2 Fk23 Kdl ltac:(num; lra)) as (Fdl & Edl).
split; [exact Fsh|]. split; [exact Fsl|]. split; [exact Fdh|]. split; [exact Fdl|].
split; [exact Esh|]. split; [exact Bsl|]. split; [|split].
- (* [dh = ch Q3 - e2]. *)
  apply Rabs_le. pose proof (Rabs_le_inv _ _ Bq). pose proof (Rabs_le_inv _ _ Be2). num. lra.
- apply Rabs_le. pose proof (Rabs_le_inv _ _ Kdl). num. lra.
- (* [dh + dl - z1^3/3] is [(z1^3 + (m1 - z1 sl) + (cl - e1 - m1)) (Q3 + Q3L) - cl Q3L
     - z1^3/3] plus the roundings of [k2], [k3], [k23] and [dl], where
     [Q3 + Q3L = 1/3 - 2^-108/3]. With the bounds above, that is below
     [5 * 2^-106 |z1|^3], as the [2^-1075] terms are below [2^-475 |z1|^3]. *)
  apply Rabs_le.
  rewrite Eq3 in Ee2, Ek2. rewrite Eql in Ek3.
  pose proof (Rabs_le_inv _ _ Be1) as Be1'.
  pose proof (Rabs_le_inv _ _ (proj2 Bz1sh)) as Bz1sh'.
  pose proof (Rabs_le_inv _ _ Bz1sl) as Bz1sl'.
  destruct Bz1sh as [_ Bz1shu].
  clear - Ee1 Ee2 Ek2 Ek3 Ek23 Edl Ecl Em1 Ecube Be1' Bz1sh' Bz1sl' Bz1shu Z3lo Z3hi.
  num. lra.
Qed.

(** The three products are exact with and without an FMA. *)
Theorem log1p_cube_fma :
  forall z1,
  is_finite z1 = true ->
  bpow radix2 (-200) <= Rabs (B2R z1) <= bpow radix2 (-9) ->
  let sh := mul z1 z1 in
  let ch := mul z1 sh in
  let dh := mul ch (from_bits DyadicLog.Q3) in
  Generic.two_prod_err true z1 z1 sh = Generic.two_prod_err false z1 z1 sh /\
  Generic.two_prod_err true z1 sh ch = Generic.two_prod_err false z1 sh ch /\
  Generic.two_prod_err true ch (from_bits DyadicLog.Q3) dh =
    Generic.two_prod_err false ch (from_bits DyadicLog.Q3) dh.
Proof.
intros z1 Fz HZ sh ch dh.
destruct (cube_prods true z1 Fz HZ) as (Fsh & Fch & T1 & T2 & T3).
destruct (cube_prods false z1 Fz HZ) as (_ & _ & F1 & F2 & F3).
destruct q3_F as (Fq & _).
split; [|split].
- exact (two_prod_err_fma_eq z1 z1 Fz Fz T1 F1).
- exact (two_prod_err_fma_eq z1 sh Fz Fsh T2 F2).
- exact (two_prod_err_fma_eq ch _ Fch Fq T3 F3).
Qed.
