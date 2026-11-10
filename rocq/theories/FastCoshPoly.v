(** * The Taylor polynomial of the fast path of [cosh]

    [DyadicExp.fast_cosh_poly] of [Model.v] evaluates the even Taylor
    polynomial [1 + t^2/2! + ... + t^12/12!] of [cosh t] on [2^-27 <= t <
    1/8], within [2^-66] relatively ([cosh_poly_correct]). [tanh] divides
    the polynomial of [sinh] of [FastHypPoly.v] by it on [t < 1/8]. It
    returns the same with and without an FMA ([cosh_poly_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error.
From Inari Require Import Model Mpfr Encoding Elementary TwoSum TwoProduct DyDriver NearF64
  FastRound FastExpErr CancelLanes MulRuTiny ExpSeries HypTaylor.

Open Scope R_scope.

(** ** Literals and rounding errors *)

(** [B2R l] of an [f64] literal [l] in the goal, as [m * 2^e] (as
    [lit_B2R] of [FastHypPos.v], for a literal anywhere in the goal). *)
Local Ltac lit_R l :=
  rewrite <- (SF2R_B2SF _ _ l);
  let s := eval vm_compute in (B2SF l) in
  replace (B2SF l) with s by (vm_compute; reflexivity);
  cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR.

(** Powers of 2 as numerals, for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp].

Local Lemma one_F : is_finite DyadicExp.one = true /\ B2R DyadicExp.one = 1.
Proof. split; [vm_compute; reflexivity|]. lit_R DyadicExp.one. num. lra. Qed.

Local Lemma half_F : is_finite half = true /\ B2R half = / 2.
Proof. split; [vm_compute; reflexivity|]. lit_R half. num. lra. Qed.

(** [add_k] and [mul_k] of [FastExpErr.v] for a named result [z], with the
    error as two inequalities for [lra] (as in [FastExpPoly.v]). *)
Local Lemma add_kz :
  forall x y z K, z = add x y -> is_finite x = true -> is_finite y = true ->
  Rabs (B2R x + B2R y) <= K -> K <= 16 ->
  is_finite z = true /\ B2R z = RN (B2R x + B2R y) /\
  - (bpow radix2 (-53) * K + bpow radix2 (-1075)) <= B2R z - (B2R x + B2R y) <=
    bpow radix2 (-53) * K + bpow radix2 (-1075).
Proof.
intros x y z K -> Fx Fy H HK.
destruct (add_k x y K Fx Fy H HK) as (F & E & B).
split; [exact F | split; [exact E | apply Rabs_le_inv; exact B]].
Qed.

Local Lemma mul_kz :
  forall x y z K, z = mul x y -> is_finite x = true -> is_finite y = true ->
  Rabs (B2R x * B2R y) <= K -> K <= 16 ->
  is_finite z = true /\ B2R z = RN (B2R x * B2R y) /\
  - (bpow radix2 (-53) * K + bpow radix2 (-1075)) <= B2R z - B2R x * B2R y <=
    bpow radix2 (-53) * K + bpow radix2 (-1075).
Proof.
intros x y z K -> Fx Fy H HK.
destruct (mul_k x y K Fx Fy H HK) as (F & E & B).
split; [exact F | split; [exact E | apply Rabs_le_inv; exact B]].
Qed.

(** The product of two [f64]s below 1 in magnitude, with an exact product
    of at least [2^-900], has an exact error with and without an FMA: its
    rounding has an exponent in [[-901, 0]], and theirs are negative (as
    [prod_exact] of [FastExpProd.v]). *)
Local Lemma tp_exact :
  forall b x y, is_finite x = true -> is_finite y = true ->
  bpow radix2 (-900) <= Rabs (B2R x * B2R y) -> Rabs (B2R x) < 1 -> Rabs (B2R y) < 1 ->
  Generic.two_prod_is_exact b x y (mul x y) = true.
Proof.
intros b x y Fx Fy Hl Hx Hy.
assert (Hxy : Rabs (B2R x * B2R y) < 1).
{ rewrite Rabs_mult. pose proof (Rabs_pos (B2R x)). pose proof (Rabs_pos (B2R y)). nra. }
destruct (mul_k x y (Rabs (B2R x * B2R y)) Fx Fy (Rle_refl _) ltac:(lra)) as (Fp & _ & Bp).
assert (U : Rabs (B2R (mul x y)) <=
            Rabs (B2R x * B2R y) + Rabs (B2R (mul x y) - B2R x * B2R y)).
{ replace (B2R (mul x y)) with (B2R x * B2R y + (B2R (mul x y) - B2R x * B2R y)) at 1
    by ring.
  apply Rabs_triang. }
assert (L : Rabs (B2R x * B2R y) <=
            Rabs (B2R (mul x y)) + Rabs (B2R (mul x y) - B2R x * B2R y)).
{ rewrite (Rabs_minus_sym (B2R (mul x y))).
  replace (B2R x * B2R y) with (B2R (mul x y) + (B2R x * B2R y - B2R (mul x y))) at 1
    by ring.
  apply Rabs_triang. }
assert (E1 : (-901 <= Generic.exponent (mul x y))%Z).
{ apply MulRuTiny.exponent_ge; [exact Fp |]. revert Hl Bp L. num. intros. nra. }
assert (E2 : (Generic.exponent (mul x y) < 1)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fp | lia |]. revert Hxy Bp U. num. intros. nra. }
assert (E3 : (Generic.exponent x < 0)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fx | lia |]. num. lra. }
assert (E4 : (Generic.exponent y < 0)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fy | lia |]. num. lra. }
unfold Generic.two_prod_is_exact. cbv zeta.
destruct b; rewrite ?andb_true_iff, ?Z.leb_le; lia.
Qed.

(** Halving an [f64] of at least [2^-1000] in magnitude is exact. *)
Local Lemma mul_half :
  forall y z, z = mul y half -> is_finite y = true ->
  bpow radix2 (-1000) <= Rabs (B2R y) <= 16 ->
  is_finite z = true /\ B2R z = B2R y / 2.
Proof.
intros y z -> Fy Hy.
destruct half_F as (Fh & Eh).
assert (HK : Rabs (B2R y * B2R half) <= 16).
{ rewrite Eh, Rabs_mult, (Rabs_pos_eq (/ 2)) by lra. lra. }
destruct (mul_k y half 16 Fy Fh HK ltac:(lra)) as (F & E & _).
split; [exact F|]. rewrite E, Eh.
assert (G : generic_format radix2 fexp64 (B2R y * bpow radix2 (-1))).
{ apply mult_bpow_exact_FLT; [apply generic_format_B2R|].
  assert (M : (-1020 <= mag radix2 (B2R y))%Z).
  { apply mag_ge_bpow. eapply Rle_trans; [| exact (proj1 Hy)]. apply bpow_le. lia. }
  lia. }
change (bpow radix2 (-1)) with (/ 2) in G.
unfold Rdiv. apply round_generic; [typeclasses eauto | exact G].
Qed.

(** The coefficients [CH4] to [CH12] are [1/4!] to [1/12!] within
    [2^-57/3], [2^-64], [2^-75], [2^-75] and [2^-82]. *)
Local Ltac coef c :=
  split; [vm_compute; reflexivity|]; lit_R (from_bits c); num; apply Rabs_le; lra.

Local Lemma ch4_b :
  is_finite (from_bits DyadicExp.CH4) = true /\
  Rabs (B2R (from_bits DyadicExp.CH4) - / 24) <= bpow radix2 (-57) / 3.
Proof. coef DyadicExp.CH4. Qed.

Local Lemma ch6_b :
  is_finite (from_bits DyadicExp.CH6) = true /\
  Rabs (B2R (from_bits DyadicExp.CH6) - / 720) <= bpow radix2 (-64).
Proof. coef DyadicExp.CH6. Qed.

Local Lemma ch8_b :
  is_finite (from_bits DyadicExp.CH8) = true /\
  Rabs (B2R (from_bits DyadicExp.CH8) - / 40320) <= bpow radix2 (-75).
Proof. coef DyadicExp.CH8. Qed.

Local Lemma ch10_b :
  is_finite (from_bits DyadicExp.CH10) = true /\
  Rabs (B2R (from_bits DyadicExp.CH10) - / 3628800) <= bpow radix2 (-75).
Proof. coef DyadicExp.CH10. Qed.

Local Lemma ch12_b :
  is_finite (from_bits DyadicExp.CH12) = true /\
  Rabs (B2R (from_bits DyadicExp.CH12) - / 479001600) <= bpow radix2 (-82).
Proof. coef DyadicExp.CH12. Qed.

(** ** Horner's scheme

    On [x = t^2] rounded, [0 <= x <= X = 2^-6 + 2^-58], each step keeps a
    bound [E] of its error against the exact Horner scheme with [1/4!] to
    [1/12!] on the same [x], and a bound [W] of its magnitude. A step [y p]
    or [C + p] rounds an exact result of at most [K] within [2^-53 K +
    2^-1075]. *)

Local Lemma hmul :
  forall y p P Ep Wp K E W,
  is_finite y = true -> is_finite p = true ->
  0 <= B2R y <= bpow radix2 (-6) + bpow radix2 (-58) ->
  Rabs (B2R p - P) <= Ep -> Rabs (B2R p) <= Wp ->
  (bpow radix2 (-6) + bpow radix2 (-58)) * Wp <= K -> K <= 16 ->
  bpow radix2 (-53) * K + bpow radix2 (-1075) + (bpow radix2 (-6) + bpow radix2 (-58)) * Ep
    <= E ->
  K + bpow radix2 (-53) * K + bpow radix2 (-1075) <= W ->
  is_finite (mul y p) = true /\ Rabs (B2R (mul y p) - B2R y * P) <= E /\
  Rabs (B2R (mul y p)) <= W.
Proof.
intros y p P Ep Wp K E W Fy Fp Hy HP Hp HK HK16 HE HW.
assert (Hy' : Rabs (B2R y) <= bpow radix2 (-6) + bpow radix2 (-58))
  by (rewrite Rabs_pos_eq by lra; exact (proj2 Hy)).
assert (Hm : Rabs (B2R y * B2R p) <= K)
  by (eapply Rle_trans; [apply Rabs_mul_le; [exact Hy' | exact Hp] | exact HK]).
destruct (mul_kz y p (mul y p) K eq_refl Fy Fp Hm HK16) as (F & _ & B).
assert (Hd : Rabs (B2R y * (B2R p - P)) <= (bpow radix2 (-6) + bpow radix2 (-58)) * Ep)
  by (apply Rabs_mul_le; [exact Hy' | exact HP]).
apply Rabs_le_inv in Hd, Hm.
split; [exact F | split; apply Rabs_le; lra].
Qed.

Local Lemma hadd :
  forall C p c P d Ep Wp K E W,
  is_finite C = true -> is_finite p = true ->
  Rabs (B2R C - c) <= d -> Rabs (B2R p - P) <= Ep -> Rabs (B2R p) <= Wp ->
  Rabs (B2R C) + Wp <= K -> K <= 16 ->
  bpow radix2 (-53) * K + bpow radix2 (-1075) + d + Ep <= E ->
  K + bpow radix2 (-53) * K + bpow radix2 (-1075) <= W ->
  is_finite (add C p) = true /\ Rabs (B2R (add C p) - (c + P)) <= E /\
  Rabs (B2R (add C p)) <= W.
Proof.
intros C p c P d Ep Wp K E W FC Fp Hd HP Hp HK HK16 HE HW.
assert (Hs : Rabs (B2R C + B2R p) <= K)
  by (eapply Rle_trans; [apply Rabs_triang | lra]).
destruct (add_kz C p (add C p) K eq_refl FC Fp Hs HK16) as (F & _ & B).
apply Rabs_le_inv in Hd, HP, Hs.
split; [exact F | split; apply Rabs_le; lra].
Qed.

(** The even part of the Taylor polynomial of [cosh] beyond degree 2, as
    [z^2 ch_A z] with [z = t^2]. *)
Local Definition ch_A (z : R) : R :=
  / 24 + z * (/ 720 + z * (/ 40320 + z * (/ 3628800 + z * / 479001600))).

(** [a] is [ch_A x] within [17 * 2^-61], and at most [1/22]. *)
Local Lemma horner :
  forall uh a,
  a = add (from_bits DyadicExp.CH4) (mul uh (add (from_bits DyadicExp.CH6)
        (mul uh (add (from_bits DyadicExp.CH8) (mul uh (add (from_bits DyadicExp.CH10)
        (mul uh (from_bits DyadicExp.CH12)))))))) ->
  is_finite uh = true -> 0 <= B2R uh <= bpow radix2 (-6) + bpow radix2 (-58) ->
  is_finite a = true /\ Rabs (B2R a - ch_A (B2R uh)) <= 17 * bpow radix2 (-61) /\
  Rabs (B2R a) <= / 22.
Proof.
intros uh a -> Fu Hu.
destruct ch4_b as (F4 & B4). destruct ch6_b as (F6 & B6). destruct ch8_b as (F8 & B8).
destruct ch10_b as (F10 & B10). destruct ch12_b as (F12 & B12).
assert (W12 : Rabs (B2R (from_bits DyadicExp.CH12)) <= / 400000000).
{ apply Rabs_le_inv in B12. apply Rabs_le. revert B12. num. lra. }
assert (A10 : Rabs (B2R (from_bits DyadicExp.CH10)) <= / 3628800 + bpow radix2 (-75)).
{ apply Rabs_le_inv in B10. apply Rabs_le. lra. }
assert (A8 : Rabs (B2R (from_bits DyadicExp.CH8)) <= / 40320 + bpow radix2 (-75)).
{ apply Rabs_le_inv in B8. apply Rabs_le. lra. }
assert (A6 : Rabs (B2R (from_bits DyadicExp.CH6)) <= / 720 + bpow radix2 (-64)).
{ apply Rabs_le_inv in B6. apply Rabs_le. lra. }
assert (A4 : Rabs (B2R (from_bits DyadicExp.CH4)) <= / 24 + bpow radix2 (-57) / 3).
{ apply Rabs_le_inv in B4. apply Rabs_le. lra. }
destruct (hmul uh _ _ (bpow radix2 (-82)) (/ 400000000) (bpow radix2 (-34))
  (bpow radix2 (-86)) (bpow radix2 (-33)) Fu F12 Hu B12 W12
  ltac:(num; lra) ltac:(num; lra) ltac:(num; lra) ltac:(num; lra)) as (Fq1 & E1 & W1).
destruct (hadd _ _ _ _ _ _ _ (bpow radix2 (-21)) (bpow radix2 (-73)) (bpow radix2 (-20))
  F10 Fq1 B10 E1 W1 ltac:(revert A10; num; lra) ltac:(num; lra) ltac:(num; lra)
  ltac:(num; lra)) as (Fq2 & E2 & W2).
destruct (hmul uh _ _ _ _ (bpow radix2 (-25)) (bpow radix2 (-77)) (bpow radix2 (-24))
  Fu Fq2 Hu E2 W2
  ltac:(num; lra) ltac:(num; lra) ltac:(num; lra) ltac:(num; lra)) as (Fq3 & E3 & W3).
destruct (hadd _ _ _ _ _ _ _ (bpow radix2 (-15)) (bpow radix2 (-67)) (bpow radix2 (-14))
  F8 Fq3 B8 E3 W3 ltac:(revert A8; num; lra) ltac:(num; lra) ltac:(num; lra)
  ltac:(num; lra)) as (Fq4 & E4 & W4).
destruct (hmul uh _ _ _ _ (bpow radix2 (-19)) (bpow radix2 (-71)) (bpow radix2 (-18))
  Fu Fq4 Hu E4 W4
  ltac:(num; lra) ltac:(num; lra) ltac:(num; lra) ltac:(num; lra)) as (Fq5 & E5 & W5).
destruct (hadd _ _ _ _ _ _ _ (bpow radix2 (-9)) (bpow radix2 (-61)) (bpow radix2 (-8))
  F6 Fq5 B6 E5 W5 ltac:(revert A6; num; lra) ltac:(num; lra) ltac:(num; lra)
  ltac:(num; lra)) as (Fq6 & E6 & W6).
destruct (hmul uh _ _ _ _ (bpow radix2 (-13)) (bpow radix2 (-65)) (bpow radix2 (-12))
  Fu Fq6 Hu E6 W6
  ltac:(num; lra) ltac:(num; lra) ltac:(num; lra) ltac:(num; lra)) as (Fq7 & E7 & W7).
destruct (hadd _ _ _ _ _ _ _ (/ 23) (17 * bpow radix2 (-61)) (/ 22)
  F4 Fq7 B4 E7 W7 ltac:(revert A4; num; lra) ltac:(num; lra) ltac:(num; lra)
  ltac:(num; lra)) as (Fa & Ea & Wa).
split; [exact Fa | split; [unfold ch_A; exact Ea | exact Wa]].
Qed.

(** ** Assembly *)

(** [ch_A x - ch_A u = (x - u) ch_N x u]. *)
Local Definition ch_N (x u : R) : R :=
  / 720 + (x + u) / 40320 + (x * x + x * u + u * u) / 3628800
  + (x + u) * (x * x + u * u) / 479001600.

Local Lemma ch_A_bound :
  forall x, 0 <= x <= bpow radix2 (-6) + bpow radix2 (-58) -> 0 <= ch_A x <= / 22.
Proof.
intros x Hx. revert Hx. num. intros Hx. unfold ch_A.
assert (H1 : 0 <= x * / 479001600 <= / 1000) by (split; nra).
assert (H2 : 0 <= x * (/ 3628800 + x * / 479001600) <= / 1000) by (split; nra).
assert (H3 : 0 <= x * (/ 40320 + x * (/ 3628800 + x * / 479001600)) <= / 1000)
  by (split; nra).
assert (H4 : 0 <= x * (/ 720 + x * (/ 40320 + x * (/ 3628800 + x * / 479001600))) <= / 10000)
  by (split; nra).
lra.
Qed.

Local Lemma ch_N_bound :
  forall x u, 0 <= x <= bpow radix2 (-6) + bpow radix2 (-58) ->
  0 <= u <= bpow radix2 (-6) + bpow radix2 (-58) -> 0 <= ch_N x u <= / 700.
Proof.
intros x u Hx Hu. revert Hx Hu. num. intros Hx Hu. unfold ch_N.
assert (H1 : 0 <= x * x <= / 1000) by (split; nra).
assert (H2 : 0 <= x * u <= / 1000) by (split; nra).
assert (H3 : 0 <= u * u <= / 1000) by (split; nra).
assert (H4 : 0 <= (x + u) * (x * x + u * u) <= / 1000) by (split; nra).
lra.
Qed.

(** The error terms of [ch + cl] against [1 + u/2 + u^2 ch_A u], for [u =
    t^2], [x = uh] and [ul = u - x]: the roundings of [v], [x2] and [a],
    [x^2 ch_A x - u^2 ch_A u = (x - u) (x + u) ch_A x + u^2 (x - u) ch_N x
    u], and the roundings of the low part. *)
Local Lemma assemble :
  forall u x ul x2 a v mh m0 ch c0 w w1 cl,
  0 <= u <= bpow radix2 (-6) -> x + ul = u ->
  Rabs ul <= bpow radix2 (-59) + bpow radix2 (-1075) ->
  0 <= x <= bpow radix2 (-6) + bpow radix2 (-58) ->
  Rabs (a - ch_A x) <= 17 * bpow radix2 (-61) -> Rabs a <= / 22 ->
  Rabs (x2 - x * x) <=
    bpow radix2 (-53) * ((bpow radix2 (-6) + bpow radix2 (-58)) *
                         (bpow radix2 (-6) + bpow radix2 (-58))) + bpow radix2 (-1075) ->
  Rabs (v - x2 * a) <= bpow radix2 (-53) * (/ 4000 * / 22) + bpow radix2 (-1075) ->
  mh + m0 = x / 2 + v -> ch + c0 = 1 + mh ->
  Rabs (w - ul / 2) <= bpow radix2 (-112) + bpow radix2 (-1075) ->
  Rabs (w1 - (m0 + w)) <= bpow radix2 (-111) + bpow radix2 (-1075) ->
  Rabs (cl - (c0 + w1)) <= bpow radix2 (-105) + bpow radix2 (-1075) ->
  Rabs (ch + cl - (1 + u / 2 + u * u * ch_A u)) <= bpow radix2 (-66) - bpow radix2 (-77).
Proof.
intros u x ul x2 a v mh m0 ch c0 w w1 cl Hu Hul Bul Hx Ba Wa Bx2 Bv Em Ec Bw Bw1 Bcl.
assert (Hu' : 0 <= u <= bpow radix2 (-6) + bpow radix2 (-58))
  by (pose proof (bpow_ge_0 radix2 (-58)); lra).
pose proof (ch_A_bound x Hx) as HA.
pose proof (ch_N_bound x u Hx Hu') as HN.
assert (EM : x * x * ch_A x - u * u * ch_A u =
             (x - u) * (x + u) * ch_A x + u * u * (x - u) * ch_N x u)
  by (unfold ch_A, ch_N; field).
assert (Bxu : Rabs (x - u) <= bpow radix2 (-59) + bpow radix2 (-1075))
  by (replace (x - u) with (- ul) by lra; rewrite Rabs_Ropp; exact Bul).
assert (P1 : Rabs ((x2 - x * x) * a) <=
             (bpow radix2 (-53) * ((bpow radix2 (-6) + bpow radix2 (-58)) *
                                   (bpow radix2 (-6) + bpow radix2 (-58)))
              + bpow radix2 (-1075)) * / 22)
  by (apply Rabs_mul_le; assumption).
assert (Hxx : Rabs (x * x) <=
              (bpow radix2 (-6) + bpow radix2 (-58)) * (bpow radix2 (-6) + bpow radix2 (-58)))
  by (apply Rabs_mul_le; rewrite Rabs_pos_eq; lra).
assert (P2 : Rabs (x * x * (a - ch_A x)) <=
             (bpow radix2 (-6) + bpow radix2 (-58)) * (bpow radix2 (-6) + bpow radix2 (-58))
             * (17 * bpow radix2 (-61)))
  by (apply Rabs_mul_le; assumption).
assert (P3 : Rabs ((x - u) * (x + u) * ch_A x) <=
             (bpow radix2 (-59) + bpow radix2 (-1075)) *
             (2 * (bpow radix2 (-6) + bpow radix2 (-58))) * / 22).
{ apply Rabs_mul_le; [apply Rabs_mul_le; [exact Bxu |] |].
  - rewrite Rabs_pos_eq; lra.
  - rewrite Rabs_pos_eq; lra. }
assert (Huu : Rabs (u * u) <=
              (bpow radix2 (-6) + bpow radix2 (-58)) * (bpow radix2 (-6) + bpow radix2 (-58)))
  by (apply Rabs_mul_le; rewrite Rabs_pos_eq; lra).
assert (P4 : Rabs (u * u * (x - u) * ch_N x u) <=
             (bpow radix2 (-6) + bpow radix2 (-58)) * (bpow radix2 (-6) + bpow radix2 (-58))
             * (bpow radix2 (-59) + bpow radix2 (-1075)) * / 700).
{ apply Rabs_mul_le; [apply Rabs_mul_le; [exact Huu | exact Bxu] |].
  rewrite Rabs_pos_eq; lra. }
apply Rabs_le_inv in Bul, Ba, Bx2, Bv, Bw, Bw1, Bcl, P1, P2, P3, P4.
apply Rabs_le.
revert Bul Ba Bx2 Bv Bw Bw1 Bcl P1 P2 P3 P4. num. intros. lra.
Qed.

(** The polynomial of [cosh] as [ch + cl], within [2^-66] of [cosh t]
    relatively. *)
Theorem cosh_poly_correct :
  forall fma t,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < / 8 ->
  let '(ch, cl) := DyadicExp.fast_cosh_poly fma t in
  is_finite ch = true /\ is_finite cl = true /\ 1 <= B2R ch <= 2 /\
  Rabs (B2R cl) <= bpow radix2 (-52) * B2R ch /\
  Rabs (B2R ch + B2R cl - cosh (B2R t)) <= bpow radix2 (-66) * cosh (B2R t).
Proof.
intros fma t Ft Ht.
unfold DyadicExp.fast_cosh_poly, Fast.fast_two_sum. cbv beta iota zeta.
set (uh := mul t t).
set (ul := Generic.two_prod_err fma t t uh).
set (a := add (from_bits DyadicExp.CH4) (mul uh (add (from_bits DyadicExp.CH6)
            (mul uh (add (from_bits DyadicExp.CH8) (mul uh (add (from_bits DyadicExp.CH10)
            (mul uh (from_bits DyadicExp.CH12))))))))).
set (x2 := mul uh uh).
set (v := mul x2 a).
set (hu := mul uh half).
set (mh := add hu v).
set (m0 := add v (sub hu mh)).
set (ch := add DyadicExp.one mh).
set (c0 := add mh (sub DyadicExp.one ch)).
set (w := mul ul half).
set (w1 := add m0 w).
set (cl := add c0 w1).
destruct one_F as (F1 & E1).
destruct half_F as (Fh & Eh).
pose proof (bpow_ge_0 radix2 (-55)) as P55.
(* [u = t^2] is in [[2^-54, 2^-6]]. *)
assert (HT0 : 0 <= B2R t) by (pose proof (bpow_ge_0 radix2 (-27)); lra).
assert (HT : bpow radix2 (-54) <= B2R t * B2R t <= bpow radix2 (-6)).
{ destruct Ht as (Ht0 & Ht1). revert Ht0 Ht1. num. intros. split; nra. }
(* [uh = u] rounded, within [2^-53 u + 2^-1075], so [2^-55 <= uh <= X]. *)
assert (Hu0 : Rabs (B2R t * B2R t) <= B2R t * B2R t)
  by (rewrite Rabs_pos_eq; [lra | nra]).
assert (HT16 : B2R t * B2R t <= 16) by (revert HT; num; intros; lra).
destruct (mul_kz t t uh _ eq_refl Ft Ft Hu0 HT16) as (Fu & _ & Bu).
assert (Hx : bpow radix2 (-55) <= B2R uh <= bpow radix2 (-6) + bpow radix2 (-58))
  by (revert HT Bu; num; intros; lra).
assert (Hx0 : 0 <= B2R uh <= bpow radix2 (-6) + bpow radix2 (-58)) by lra.
(* [ul = u - uh] exactly, with and without an FMA. *)
assert (HT1 : Rabs (B2R t) < 1)
  by (rewrite Rabs_pos_eq by lra; destruct Ht as (_ & Ht1); lra).
assert (Hex : Generic.two_prod_is_exact fma t t uh = true).
{ apply tp_exact; [exact Ft | exact Ft | | exact HT1 | exact HT1].
  rewrite Rabs_pos_eq by nra.
  apply Rle_trans with (bpow radix2 (-54)); [apply bpow_le; lia | exact (proj1 HT)]. }
assert (Rul : is_finite ul = true /\ B2R ul = B2R t * B2R t - B2R uh)
  by exact (proj2 (proj2 (proj2 (two_prod_err_correct fma t t Ft Ft Hex)))).
destruct Rul as (Ful & Eul).
assert (Bul : Rabs (B2R ul) <= bpow radix2 (-59) + bpow radix2 (-1075)).
{ rewrite Eul. apply Rabs_le. revert HT Bu. num. intros. lra. }
(* Horner's scheme. *)
destruct (horner uh a eq_refl Fu Hx0) as (Fa & Ba & Wa).
(* [x2 = uh^2] rounded, at most [1/4000] and [2 X uh]. *)
assert (Hxx : Rabs (B2R uh * B2R uh) <=
              (bpow radix2 (-6) + bpow radix2 (-58)) * (bpow radix2 (-6) + bpow radix2 (-58)))
  by (apply Rabs_mul_le; rewrite Rabs_pos_eq; lra).
destruct (mul_kz uh uh x2 _ eq_refl Fu Fu Hxx ltac:(num; lra)) as (Fx2 & _ & Bx2).
assert (Wx2 : Rabs (B2R x2) <= / 4000).
{ apply Rabs_le_inv in Hxx. apply Rabs_le. revert Hxx Bx2. num. intros. lra. }
assert (Hxx2 : 0 <= B2R uh * B2R uh <= (bpow radix2 (-6) + bpow radix2 (-58)) * B2R uh)
  by (split; [nra | apply Rmult_le_compat_r; lra]).
assert (Wx2' : Rabs (B2R x2) <= 2 * (bpow radix2 (-6) + bpow radix2 (-58)) * B2R uh).
{ apply Rabs_le. revert Hxx2 Bx2 Hx. num. intros. lra. }
(* [v = x2 a] rounded, at most [uh / 2]. *)
assert (Hm : Rabs (B2R x2 * B2R a) <= / 4000 * / 22) by (apply Rabs_mul_le; assumption).
destruct (mul_kz x2 a v _ eq_refl Fx2 Fa Hm ltac:(lra)) as (Fv & _ & Bv).
assert (Hm' : Rabs (B2R x2 * B2R a) <=
              2 * (bpow radix2 (-6) + bpow radix2 (-58)) * B2R uh * / 22)
  by (apply Rabs_mul_le; assumption).
assert (Hhu : bpow radix2 (-1000) <= Rabs (B2R uh) <= 16).
{ rewrite Rabs_pos_eq by lra. split.
  - apply Rle_trans with (bpow radix2 (-55)); [apply bpow_le; lia | lra].
  - revert Hx. num. intros. lra. }
destruct (mul_half uh hu eq_refl Fu Hhu) as (Fhu & Ehu).
assert (Wv : Rabs (B2R v) <= Rabs (B2R hu)).
{ rewrite Ehu, (Rabs_pos_eq (B2R uh / 2)) by lra.
  apply Rabs_le_inv in Hm'. apply Rabs_le. revert Hm' Bv Hx. num. intros. lra. }
(* [mh + m0 = hu + v] exactly (Fast2Sum [Dekker]), and [mh >= 0]. *)
assert (Hs : Rabs (B2R hu + B2R v) <= bpow radix2 (-6) + bpow radix2 (-58)).
{ apply Rabs_le_inv in Wv. rewrite Ehu, (Rabs_pos_eq (B2R uh / 2)) in Wv by lra.
  apply Rabs_le. rewrite Ehu. lra. }
destruct (add_kz hu v mh _ eq_refl Fhu Fv Hs ltac:(num; lra)) as (Fmh & Rmh & Bmh).
destruct (fast_two_sum hu v mh Fhu Fv Wv Fmh Rmh) as (Fm0 & Em0).
change (add v (sub hu mh)) with m0 in Fm0, Em0.
assert (Hmh0 : 0 <= B2R mh).
{ rewrite Rmh. apply round_ge_generic; [typeclasses eauto .. | apply generic_format_0 |].
  apply Rabs_le_inv in Wv. rewrite Ehu, (Rabs_pos_eq (B2R uh / 2)) in Wv by lra.
  rewrite Ehu. lra. }
assert (Hmh1 : B2R mh <= bpow radix2 (-5)).
{ apply Rabs_le_inv in Hs. revert Hs Bmh. num. intros. lra. }
(* [ch + c0 = 1 + mh] exactly (Fast2Sum), and [1 <= ch <= 2]. *)
assert (Hs1 : Rabs (B2R DyadicExp.one + B2R mh) <= 1 + bpow radix2 (-5))
  by (rewrite E1, Rabs_pos_eq by lra; lra).
destruct (add_kz DyadicExp.one mh ch _ eq_refl F1 Fmh Hs1 ltac:(num; lra))
  as (Fch & Rch & Bch).
assert (Hle1 : Rabs (B2R mh) <= Rabs (B2R DyadicExp.one)).
{ rewrite E1, Rabs_R1, Rabs_pos_eq by lra. revert Hmh1. num. intros. lra. }
destruct (fast_two_sum DyadicExp.one mh ch F1 Fmh Hle1 Fch Rch) as (Fc0 & Ec0).
change (add mh (sub DyadicExp.one ch)) with c0 in Fc0, Ec0.
assert (Hch : 1 <= B2R ch <= 2).
{ rewrite Rch, E1. split.
  - apply round_ge_generic; [typeclasses eauto .. | | lra].
    rewrite <- E1. apply generic_format_B2R.
  - apply round_le_generic; [typeclasses eauto .. | | revert Hmh1; num; intros; lra].
    change 2 with (bpow radix2 1). apply generic_format_bpow. unfold FLT_exp. lia. }
(* The low part: [w = ul / 2], [w1 = m0 + w] and [cl = c0 + w1], each
   rounded. *)
assert (Hw : Rabs (B2R ul * B2R half) <= bpow radix2 (-59)).
{ rewrite Eh. apply Rabs_le_inv in Bul. apply Rabs_le. revert Bul. num. intros. lra. }
destruct (mul_kz ul half w _ eq_refl Ful Fh Hw ltac:(num; lra)) as (Fw & _ & Bw).
rewrite Eh in Bw.
assert (Hs2 : Rabs (B2R m0 + B2R w) <= bpow radix2 (-58)).
{ apply Rabs_le_inv in Bul. apply Rabs_le. revert Bul Bw Bmh Em0. num. intros. lra. }
destruct (add_kz m0 w w1 _ eq_refl Fm0 Fw Hs2 ltac:(num; lra)) as (Fw1 & _ & Bw1).
assert (Hs3 : Rabs (B2R c0 + B2R w1) <= bpow radix2 (-52)).
{ apply Rabs_le. rewrite E1 in Ec0. revert Hs2 Bw1 Bch Ec0. num. intros.
  apply Rabs_le_inv in Hs2. lra. }
destruct (add_kz c0 w1 cl _ eq_refl Fc0 Fw1 Hs3 ltac:(num; lra)) as (Fcl & _ & Bcl).
split; [exact Fch|]. split; [exact Fcl|]. split; [exact Hch|]. split.
{ apply Rabs_le. rewrite E1 in Ec0. apply Rabs_le_inv in Hs2.
  revert Hs2 Bw1 Bch Ec0 Bcl Hch. num. intros. lra. }
(* The sum, against the Taylor polynomial of degree 12 and then [cosh]. *)
assert (HA : Rabs (B2R ch + B2R cl -
                   (1 + B2R t * B2R t / 2 + B2R t * B2R t * (B2R t * B2R t) *
                    ch_A (B2R t * B2R t))) <= bpow radix2 (-66) - bpow radix2 (-77)).
{ apply (assemble (B2R t * B2R t) (B2R uh) (B2R ul) (B2R x2) (B2R a) (B2R v) (B2R mh)
           (B2R m0) (B2R ch) (B2R c0) (B2R w) (B2R w1) (B2R cl)).
  - pose proof (bpow_ge_0 radix2 (-54)). lra.
  - lra.
  - exact Bul.
  - exact Hx0.
  - exact Ba.
  - exact Wa.
  - apply Rabs_le. exact Bx2.
  - apply Rabs_le. exact Bv.
  - rewrite Em0, Ehu. lra.
  - rewrite Ec0, E1. lra.
  - apply Rabs_le. revert Bw. num. intros. lra.
  - apply Rabs_le. revert Bw1. num. intros. lra.
  - apply Rabs_le. revert Bcl. num. intros. lra. }
destruct (cosh_taylor (B2R t) ltac:(destruct Ht as (_ & Ht1); lra)) as (C0 & C1).
assert (EC : cosh_taylor12 (B2R t) =
             1 + B2R t * B2R t / 2 + B2R t * B2R t * (B2R t * B2R t) *
             ch_A (B2R t * B2R t))
  by (unfold cosh_taylor12, ch_A; field).
assert (Htau : 3 / 2 * (B2R t ^ 14 / 87178291200) <= bpow radix2 (-77)).
{ assert (H14 : B2R t ^ 14 <= (/ 8) ^ 14)
    by (apply pow_incr; destruct Ht as (_ & Ht1); lra).
  replace ((/ 8) ^ 14) with (/ 4398046511104) in H14 by field.
  num. lra. }
assert (Hc1 : 1 <= cosh_taylor12 (B2R t)).
{ unfold cosh_taylor12.
  pose proof (pow_le (B2R t) 2 HT0). pose proof (pow_le (B2R t) 4 HT0).
  pose proof (pow_le (B2R t) 6 HT0). pose proof (pow_le (B2R t) 8 HT0).
  pose proof (pow_le (B2R t) 10 HT0). pose proof (pow_le (B2R t) 12 HT0).
  lra. }
apply Rabs_le_inv in HA. apply Rabs_le.
revert HA EC Htau Hc1 C0 C1. num. intros. lra.
Qed.

(** The polynomial of [cosh] is the same with and without an FMA. *)
Theorem cosh_poly_fma :
  forall t,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < / 8 ->
  DyadicExp.fast_cosh_poly true t = DyadicExp.fast_cosh_poly false t.
Proof.
intros t Ft Ht.
(* The only use of the FMA is the error of [t * t], which is exact. *)
assert (HT0 : 0 <= B2R t) by (pose proof (bpow_ge_0 radix2 (-27)); lra).
assert (HT1 : Rabs (B2R t) < 1)
  by (rewrite Rabs_pos_eq by lra; destruct Ht as (_ & Ht1); lra).
assert (H900 : bpow radix2 (-900) <= Rabs (B2R t * B2R t)).
{ rewrite Rabs_pos_eq by nra.
  apply Rle_trans with (bpow radix2 (-54)); [apply bpow_le; lia |].
  destruct Ht as (Ht0 & _). revert Ht0. num. intros. nra. }
pose proof (tp_exact true t t Ft Ft H900 HT1 HT1) as E1.
pose proof (tp_exact false t t Ft Ft H900 HT1 HT1) as E0.
unfold DyadicExp.fast_cosh_poly.
rewrite (two_prod_err_fma_eq t t Ft Ft E1 E0).
reflexivity.
Qed.
