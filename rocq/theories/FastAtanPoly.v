(** * The Taylor polynomial of the fast path of atan

    [DyadicAtan.fast_atan_poly] of [Model.v] evaluates the odd Taylor
    polynomial [u - u^3/3 + u^5/5 - ... - u^11/11] of [atan u], for a
    double-double [u = uh + ul] with [2^-82 <= |uh| <= 2^-7] and [|ul| <=
    2^-53 |uh|], as [u - u^3 B], with [B = 1/3 - u^2 (1/5 - u^2 (1/7 -
    u^2 (1/9 - u^2/11)))], [u^2], [u^3], [1/3], [B] and the product [u^3
    B] in double-double and the rest of [B] in [f64], and is within
    [2^-78 |u|] of [atan u] ([fast_atan_poly_correct]). The remainder
    after six terms is at most [|u|^13/13] by
    [AtanSeries.atan_tail_bounds]. It returns the same with and without
    an FMA ([fast_atan_poly_fma]).

    The steps, with [u = x + y] the input [uh + ul], [X = |x|], [S = x^2]
    and [C = X S = |x|^3]: [u^2] as [vh + vl] ([ap_v]), [B] in [vh] as
    [bh + bl] ([ap_b]), [u^3] as [wh + wl] ([ap_w]), [u^3 B] as [ch + cl]
    ([ap_c]), and [x + y - ch - cl] as the result [rh + rl] ([ap_final]).
    [ap_assemble] adds their errors to the truncation on the reals. The
    products [x^2], [x vh] and [wh bh] are exact as [vh + e] (TwoProduct,
    [TwoProduct.v]) and the sums [1/3 - m] and [x - ch] are exact as [s +
    s0] (Fast2Sum [Dekker]).

    [Dekker] T. J. Dekker, A floating-point technique for extending the
    available precision, Numer. Math. 18 (1971). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error Relative.
From Inari Require Import Model Mpfr Encoding Elementary TwoSum TwoProduct DyDriver NearF64
  FastRound FastExpErr CancelLanes MulRuTiny AtanSeries FastHypPos FastAtanTables.

Open Scope R_scope.

(** ** Helpers (as in [FastSinhSteps.v] and [FastSinhHorner.v]) *)

(** Powers of 2 as numerals, for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp].

(** [add_k], [sub_k] and [mul_k] of [FastExpErr.v] for a named result
    [z], with the error as two inequalities for [lra]. *)
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

Local Lemma sub_kz :
  forall x y z K, z = sub x y -> is_finite x = true -> is_finite y = true ->
  Rabs (B2R x - B2R y) <= K -> K <= 16 ->
  is_finite z = true /\
  - (bpow radix2 (-53) * K + bpow radix2 (-1075)) <= B2R z - (B2R x - B2R y) <=
    bpow radix2 (-53) * K + bpow radix2 (-1075).
Proof.
intros x y z K -> Fx Fy H HK.
destruct (sub_k x y K Fx Fy H HK) as (F & _ & B).
split; [exact F | apply Rabs_le_inv; exact B].
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

(** Rounding to nearest in the normal range moves [x] by at most [2^-53 |x|]. *)
Local Lemma rn_rel :
  forall x, bpow radix2 (-1022) <= Rabs x -> Rabs (RN x - x) <= bpow radix2 (-53) * Rabs x.
Proof.
intros x Hx.
assert (H : Rabs (RN x - x) <= / 2 * bpow radix2 (- 53 + 1) * Rabs x)
  by exact (relative_error_N_FLT radix2 (-1074) 53 eq_refl (fun z => negb (Z.even z)) x Hx).
change (- 53 + 1)%Z with (-52)%Z in H.
assert (E : / 2 * bpow radix2 (-52) = bpow radix2 (-53)) by (num; lra).
rewrite E in H. exact H.
Qed.

(** The product of two [f64]s below 1 in magnitude, with an exact product
    of at least [2^-900], has an exact error with and without an FMA: its
    rounding has an exponent in [[-901, 0]], and theirs are negative (as
    [tp_exact] of [FastCoshPoly.v]). *)
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

(** [opp] negates exactly. *)
Local Lemma opp_F :
  forall z, is_finite z = true -> is_finite (opp z) = true /\ B2R (opp z) = - B2R z.
Proof.
intros z Fz. split; [unfold opp; rewrite is_finite_Bopp; exact Fz | apply B2R_Bopp].
Qed.

(** ** The steps *)

(** [u^2] as [vh + vl], with [vh] the rounding of [x^2] and [vh + e =
    x^2] exactly (TwoProduct): [vl] is [e + 2 x y] rounded, and the
    dropped [y^2] is at most [2^-106 x^2]. *)
Local Lemma ap_v :
  forall fma uh ul,
  is_finite uh = true -> is_finite ul = true ->
  bpow radix2 (-82) <= Rabs (B2R uh) <= bpow radix2 (-7) ->
  Rabs (B2R ul) <= bpow radix2 (-53) * Rabs (B2R uh) ->
  let vh := mul uh uh in
  let vl := add (Generic.two_prod_err fma uh uh vh) (mul DyadicExp.two (mul uh ul)) in
  is_finite vh = true /\ is_finite vl = true /\
  (forall b, Generic.two_prod_is_exact b uh uh vh = true) /\
  0 <= B2R vh <= bpow radix2 (-14) /\
  Rabs (B2R vh - B2R uh * B2R uh) <= bpow radix2 (-53) * (B2R uh * B2R uh) /\
  Rabs (B2R vl) <= bpow radix2 (-51) * (B2R uh * B2R uh) /\
  Rabs (B2R vh - (B2R uh + B2R ul) * (B2R uh + B2R ul)) <=
    bpow radix2 (-51) * (B2R uh * B2R uh) /\
  Rabs (B2R vh + B2R vl - (B2R uh + B2R ul) * (B2R uh + B2R ul)) <=
    bpow radix2 (-102) * (B2R uh * B2R uh).
Proof.
intros fma uh ul Fu Fl Hx Hy. cbv zeta.
pose proof (bpow_gt_0 radix2 (-82)) as P82.
pose proof (bpow_gt_0 radix2 (-1075)) as Peps.
(* [S = x^2 = X^2] lies in [[2^-164, 2^-14]], so [eps = 2^-1075] is at
   most [2^-900 S]. *)
assert (ES : B2R uh * B2R uh = Rabs (B2R uh) * Rabs (B2R uh)).
{ rewrite <- Rabs_mult. symmetry. apply Rabs_pos_eq. pose proof (Rle_0_sqr (B2R uh)) as H.
  unfold Rsqr in H. exact H. }
assert (HS : bpow radix2 (-164) <= B2R uh * B2R uh <= bpow radix2 (-14)).
{ rewrite ES. split.
  - replace (bpow radix2 (-164)) with (bpow radix2 (-82) * bpow radix2 (-82))
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; lra.
  - replace (bpow radix2 (-14)) with (bpow radix2 (-7) * bpow radix2 (-7))
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | lra | lra]. }
pose proof (bpow_gt_0 radix2 (-164)) as P164.
assert (Heps : bpow radix2 (-1075) <= bpow radix2 (-900) * (B2R uh * B2R uh)).
{ apply Rle_trans with (bpow radix2 (-900) * bpow radix2 (-164)).
  - rewrite <- bpow_plus. apply bpow_le. lia.
  - apply Rmult_le_compat_l; [apply bpow_ge_0 | apply HS]. }
(* [vh] is [x^2] rounded and [e = x^2 - vh] exactly (TwoProduct). *)
assert (Hx1 : Rabs (B2R uh) < 1) by (revert Hx; num; intros; lra).
assert (Ex1 : forall b, Generic.two_prod_is_exact b uh uh (mul uh uh) = true).
{ intros b. apply tp_exact; [exact Fu | exact Fu | | exact Hx1 | exact Hx1].
  rewrite Rabs_pos_eq by lra. eapply Rle_trans; [| apply HS]. apply bpow_le. lia. }
destruct (two_prod_err_correct fma uh uh Fu Fu (Ex1 fma)) as (Fvh & Evh & _ & Fe & Ee).
set (vh := mul uh uh) in *.
set (e := Generic.two_prod_err fma uh uh vh) in *.
assert (Rvh : Rabs (B2R vh - B2R uh * B2R uh) <= bpow radix2 (-53) * (B2R uh * B2R uh)).
{ assert (H := rn_rel (B2R uh * B2R uh)).
  rewrite (Rabs_pos_eq (B2R uh * B2R uh)) in H by lra. rewrite Evh. apply H.
  eapply Rle_trans; [| apply HS]. apply bpow_le. lia. }
(* [vh <= 2^-14], a float, as rounding is monotone. *)
assert (Bvh : 0 <= B2R vh <= bpow radix2 (-14)).
{ split.
  - pose proof Rvh as R. apply Rabs_le_inv in R. revert R HS. num. intros. lra.
  - rewrite Evh. apply round_le_generic; [typeclasses eauto .. | | apply HS].
    apply generic_format_bpow. unfold FLT_exp. lia. }
(* [m0 = RN(x y)], with [|x y| <= 2^-53 S]. *)
assert (H0 : Rabs (B2R uh * B2R ul) <= Rabs (B2R uh) * (bpow radix2 (-53) * Rabs (B2R uh)))
  by (apply Rabs_mul_le; [apply Rle_refl | exact Hy]).
destruct (mul_kz uh ul (mul uh ul) _ eq_refl Fu Fl H0 ltac:(revert HS ES; num; intros; lra))
  as (Fm0 & _ & Bm0).
set (m0 := mul uh ul) in *.
(* [m1 = RN(2 m0)], with [|2 m0| <= 2^-51 S]. *)
assert (F2 : is_finite DyadicExp.two = true) by (vm_compute; reflexivity).
assert (H1 : Rabs (B2R DyadicExp.two * B2R m0) <= bpow radix2 (-51) * (B2R uh * B2R uh)).
{ rewrite lit_two. apply Rabs_le. apply Rabs_le_inv in H0.
  revert H0 Bm0 ES Heps HS. num. intros. lra. }
destruct (mul_kz DyadicExp.two m0 (mul DyadicExp.two m0) _ eq_refl F2 Fm0 H1
  ltac:(revert HS; num; intros; lra)) as (Fm1 & _ & Bm1).
rewrite lit_two in Bm1.
set (m1 := mul DyadicExp.two m0) in *.
(* [vl = RN(e + m1)], with [|e + m1| <= (2^-53 + 2^-52) S + 3 eps]. *)
pose proof Rvh as Rvh'. apply Rabs_le_inv in Rvh'.
pose proof H0 as H0'. apply Rabs_le_inv in H0'.
assert (H2 : Rabs (B2R e + B2R m1) <= bpow radix2 (-51) * (B2R uh * B2R uh)).
{ apply Rabs_le. revert Ee Rvh' H0' Bm0 Bm1 ES Heps HS. num. intros. lra. }
destruct (add_kz e m1 (add e m1) _ eq_refl Fe Fm1 H2 ltac:(revert HS; num; intros; lra))
  as (Fvl & _ & Bvl).
set (vl := add e m1) in *.
(* The dropped [y^2] is at most [2^-106 X^2]. *)
assert (Hyy : Rabs (B2R ul * B2R ul) <=
              (bpow radix2 (-53) * Rabs (B2R uh)) * (bpow radix2 (-53) * Rabs (B2R uh)))
  by (apply Rabs_mul_le; exact Hy).
apply Rabs_le_inv in Hyy.
split; [exact Fvh |]. split; [exact Fvl |]. split; [exact Ex1 |].
split; [exact Bvh |]. split; [exact Rvh |].
split; [| split].
- apply Rabs_le. revert Ee Rvh' H0' Bm0 Bm1 Bvl ES Heps HS. num. intros. lra.
- (* [vh - u^2 = (vh - x^2) - 2 x y - y^2]. *)
  apply Rabs_le. revert Rvh' H0' Hyy ES HS. num. intros. lra.
- (* [vh + vl - u^2 = (m1 - 2 m0) + 2 (m0 - x y) + (vl - (e + m1)) - y^2]:
     [(2^-104 + 2^-105 + 2^-104 + 2^-106) S + 4 eps]. *)
  apply Rabs_le. revert Ee Bm0 Bm1 Bvl Hyy ES Heps HS. num. intros. lra.
Qed.

(** [B] in [vh] by Horner's scheme as [bh + bl]. *)
Local Definition atB (v : R) : R := / 3 - v * (/ 5 - v * (/ 7 - v * (/ 9 - v * / 11))).

(** [B2R l] of an [f64] literal [l] in the goal, as [m * 2^e] (as
    [lit_R] of [FastSinhHorner.v]). *)
Local Ltac lit_R l :=
  rewrite <- (SF2R_B2SF _ _ l);
  let s := eval vm_compute in (B2SF l) in
  replace (B2SF l) with s by (vm_compute; reflexivity);
  cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR.

(** The coefficients [A5] to [A11] are [1/5] to [1/11] rounded to
    nearest, so within [2^-56], and [A3] is the double-double [1/3]
    within [2^-100]: its high part is [1/3 - 2^-54/3], and its low part
    is about [2^-54/3]. *)
Local Ltac coef c :=
  split; [vm_compute; reflexivity|]; lit_R (from_bits c); num; apply Rabs_le; lra.

Local Lemma at5_b :
  is_finite (from_bits DyadicAtan.A5) = true /\
  Rabs (B2R (from_bits DyadicAtan.A5) - / 5) <= bpow radix2 (-56).
Proof. coef DyadicAtan.A5. Qed.

Local Lemma at7_b :
  is_finite (from_bits DyadicAtan.A7) = true /\
  Rabs (B2R (from_bits DyadicAtan.A7) - / 7) <= bpow radix2 (-56).
Proof. coef DyadicAtan.A7. Qed.

Local Lemma at9_b :
  is_finite (from_bits DyadicAtan.A9) = true /\
  Rabs (B2R (from_bits DyadicAtan.A9) - / 9) <= bpow radix2 (-56).
Proof. coef DyadicAtan.A9. Qed.

Local Lemma at11_b :
  is_finite (from_bits DyadicAtan.A11) = true /\
  Rabs (B2R (from_bits DyadicAtan.A11) - / 11) <= bpow radix2 (-56).
Proof. coef DyadicAtan.A11. Qed.

Local Lemma at3_b :
  is_finite (from_bits (fst DyadicAtan.A3)) = true /\
  is_finite (from_bits (snd DyadicAtan.A3)) = true /\
  / 3 - bpow radix2 (-54) <= B2R (from_bits (fst DyadicAtan.A3)) <= / 3 /\
  Rabs (B2R (from_bits (snd DyadicAtan.A3))) <= bpow radix2 (-55) /\
  Rabs (B2R (from_bits (fst DyadicAtan.A3)) + B2R (from_bits (snd DyadicAtan.A3)) - / 3)
    <= bpow radix2 (-100).
Proof.
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
lit_R (from_bits (fst DyadicAtan.A3)). lit_R (from_bits (snd DyadicAtan.A3)). num.
split; [lra|]. split; apply Rabs_le; lra.
Qed.

(** A step [x q] or [c - q] of Horner's scheme, with [x] in [[0, Mx]]
    within [dl] of [u] in [[0, Mu]], [q] within [D] of [y] and [c] within
    [G] of [g >= 0], is within [D'] of [u y] or [g - y]: the rounding of
    an exact result of at most [K] adds [2^-53 K + 2^-1075]. The bounds
    [Mx] and [Mu] are separate, as [vh] is at most [2^-14] and only its
    real [v] needs [2^-13]. *)
Local Lemma mul_step :
  forall x q u y Mx Mu Y D dl D',
  is_finite x = true -> is_finite q = true ->
  0 <= B2R x <= Mx -> 0 <= u <= Mu -> Rabs (B2R x - u) <= dl ->
  Rabs (B2R q - y) <= D -> Rabs y <= Y -> Mx * (Y + D) <= 16 ->
  bpow radix2 (-53) * (Mx * (Y + D)) + bpow radix2 (-1075) + Mx * D + dl * Y <= D' ->
  is_finite (mul x q) = true /\ Rabs (B2R (mul x q) - u * y) <= D' /\
  Rabs (u * y) <= Mu * Y.
Proof.
intros x q u y Mx Mu Y D dl D' Fx Fq Hx Hu Hd Hq Hy HYD HD.
assert (Ax : Rabs (B2R x) <= Mx) by (rewrite Rabs_pos_eq; lra).
assert (Au : Rabs u <= Mu) by (rewrite Rabs_pos_eq; lra).
assert (Aq : Rabs (B2R q) <= Y + D).
{ pose proof Hq as Hq'. pose proof Hy as Hy'. apply Rabs_le_inv in Hq', Hy'.
  apply Rabs_le. lra. }
assert (Hm : Rabs (B2R x * B2R q) <= Mx * (Y + D)) by (apply Rabs_mul_le; assumption).
destruct (mul_k x q (Mx * (Y + D)) Fx Fq Hm HYD) as (F & _ & B).
(* [x q - u y = x (q - y) + (x - u) y]. *)
assert (H1 : Rabs (B2R x * (B2R q - y)) <= Mx * D) by (apply Rabs_mul_le; assumption).
assert (H2 : Rabs ((B2R x - u) * y) <= dl * Y) by (apply Rabs_mul_le; assumption).
assert (H3 : Rabs (u * y) <= Mu * Y) by (apply Rabs_mul_le; assumption).
apply Rabs_le_inv in B, H1, H2.
split; [exact F | split; [apply Rabs_le; lra | exact H3]].
Qed.

Local Lemma sub_step :
  forall c q g y Y G D D',
  is_finite c = true -> is_finite q = true ->
  Rabs (B2R c - g) <= G -> Rabs (B2R q - y) <= D -> 0 <= g -> Rabs y <= Y ->
  g + Y + G + D <= 16 ->
  bpow radix2 (-53) * (g + Y + G + D) + bpow radix2 (-1075) + G + D <= D' ->
  is_finite (sub c q) = true /\ Rabs (B2R (sub c q) - (g - y)) <= D' /\
  Rabs (g - y) <= g + Y.
Proof.
intros c q g y Y G D D' Fc Fq Hc Hq Hg Hy HK HD.
apply Rabs_le_inv in Hc, Hq, Hy.
assert (Hm : Rabs (B2R c - B2R q) <= g + Y + G + D) by (apply Rabs_le; lra).
destruct (sub_k c q (g + Y + G + D) Fc Fq Hm HK) as (F & _ & B).
apply Rabs_le_inv in B.
split; [exact F | split; apply Rabs_le; lra].
Qed.

Local Lemma ap_b :
  forall vh v,
  is_finite vh = true -> 0 <= B2R vh <= bpow radix2 (-14) -> 0 <= v <= bpow radix2 (-13) ->
  Rabs (B2R vh - v) <= bpow radix2 (-65) ->
  let a := sub (from_bits DyadicAtan.A5) (mul vh (sub (from_bits DyadicAtan.A7)
             (mul vh (sub (from_bits DyadicAtan.A9) (mul vh (from_bits DyadicAtan.A11)))))) in
  let '(bh, b0) := Fast.fast_two_sum (from_bits (fst DyadicAtan.A3)) (opp (mul vh a)) in
  let bl := add b0 (from_bits (snd DyadicAtan.A3)) in
  is_finite bh = true /\ is_finite bl = true /\ 33 / 100 <= B2R bh <= 34 / 100 /\
  Rabs (B2R bl) <= bpow radix2 (-53) /\
  Rabs (B2R bh + B2R bl - atB v) <= bpow radix2 (-65).
Proof.
intros vh v Fvh Hvh Hv Hd.
unfold Fast.fast_two_sum. cbv beta iota zeta.
pose proof (bpow_gt_0 radix2 (-1075)) as P0.
destruct at11_b as (F11 & B11). destruct at9_b as (F9 & B9).
destruct at7_b as (F7 & B7). destruct at5_b as (F5 & B5).
destruct at3_b as (F3h & F3l & B3h & B3l & B3).
assert (G11 : Rabs (/ 11) <= / 11) by (rewrite Rabs_pos_eq; lra).
assert (G9 : 0 <= / 9) by lra. assert (G7 : 0 <= / 7) by lra. assert (G5 : 0 <= / 5) by lra.
(* Horner's scheme, innermost first: [q1 = vh A11] is within [2^-67] of
   [v/11], [q2 = A9 - q1] within [2^-55] of [1/9 - v/11], and so on, with
   the bound of each exact partial result from the step before. *)
destruct (mul_step vh _ v (/ 11) (bpow radix2 (-14)) (bpow radix2 (-13)) (/ 11)
  (bpow radix2 (-56)) (bpow radix2 (-65)) (bpow radix2 (-67)) Fvh F11 Hvh Hv Hd B11 G11
  ltac:(num; lra) ltac:(num; lra)) as (Fq1 & E1 & W1).
set (q1 := mul vh (from_bits DyadicAtan.A11)) in *.
destruct (sub_step _ q1 (/ 9) _ _ (bpow radix2 (-56)) (bpow radix2 (-67)) (bpow radix2 (-55))
  F9 Fq1 B9 E1 G9 W1 ltac:(num; lra) ltac:(num; lra)) as (Fq2 & E2 & W2).
set (q2 := sub (from_bits DyadicAtan.A9) q1) in *.
destruct (mul_step vh q2 v _ (bpow radix2 (-14)) (bpow radix2 (-13)) _
  (bpow radix2 (-55)) (bpow radix2 (-65)) (bpow radix2 (-67)) Fvh Fq2 Hvh Hv Hd E2 W2
  ltac:(num; lra) ltac:(num; lra)) as (Fq3 & E3 & W3).
set (q3 := mul vh q2) in *.
destruct (sub_step _ q3 (/ 7) _ _ (bpow radix2 (-56)) (bpow radix2 (-67)) (bpow radix2 (-54))
  F7 Fq3 B7 E3 G7 W3 ltac:(num; lra) ltac:(num; lra)) as (Fq4 & E4 & W4).
set (q4 := sub (from_bits DyadicAtan.A7) q3) in *.
destruct (mul_step vh q4 v _ (bpow radix2 (-14)) (bpow radix2 (-13)) _
  (bpow radix2 (-54)) (bpow radix2 (-65)) (bpow radix2 (-66)) Fvh Fq4 Hvh Hv Hd E4 W4
  ltac:(num; lra) ltac:(num; lra)) as (Fq5 & E5 & W5).
set (q5 := mul vh q4) in *.
destruct (sub_step _ q5 (/ 5) _ _ (bpow radix2 (-56)) (bpow radix2 (-66)) (bpow radix2 (-54))
  F5 Fq5 B5 E5 G5 W5 ltac:(num; lra) ltac:(num; lra)) as (Fa & Ea & Wa).
set (a := sub (from_bits DyadicAtan.A5) q5) in *.
destruct (mul_step vh a v _ (bpow radix2 (-14)) (bpow radix2 (-13)) _
  (bpow radix2 (-54)) (bpow radix2 (-65)) (bpow radix2 (-66)) Fvh Fa Hvh Hv Hd Ea Wa
  ltac:(num; lra) ltac:(num; lra)) as (Fm & Em & Wm).
set (m := mul vh a) in *.
destruct (opp_F m Fm) as (Fom & Eom).
set (om := opp m) in *.
set (h := from_bits (fst DyadicAtan.A3)) in *.
set (l := from_bits (snd DyadicAtan.A3)) in *.
(* [m] is at most [2^-13/5 + 2^-66], so below [2^-15]. *)
assert (Am : Rabs (B2R m) <= bpow radix2 (-15)).
{ pose proof Em as E'. pose proof Wm as W'. apply Rabs_le_inv in E', W'.
  apply Rabs_le. revert E' W'. num. intros. lra. }
pose proof Am as Am'. apply Rabs_le_inv in Am'.
(* [bh] rounds [h - m], which is about [1/3]. *)
assert (Hs : Rabs (B2R h + B2R om) <= 34 / 100).
{ rewrite Eom. apply Rabs_le. revert B3h Am'. num. intros. lra. }
destruct (add_kz h om (add h om) (34 / 100) eq_refl F3h Fom Hs ltac:(lra))
  as (Fbh & Ebh & Bbh).
set (bh := add h om) in *.
(* Fast2Sum applies, as [|m| <= 2^-15 <= h], so [b0] is the exact error
   [h - m - bh] (Dekker 1971). *)
assert (Hle : Rabs (B2R om) <= Rabs (B2R h)).
{ rewrite Eom, Rabs_Ropp. rewrite (Rabs_pos_eq (B2R h)) by (revert B3h; num; intros; lra).
  revert B3h Am. num. intros. lra. }
destruct (CancelLanes.fast_two_sum h om bh F3h Fom Hle Fbh Ebh) as (Fb0 & Eb0).
set (b0 := add om (sub h bh)) in *.
(* [bl] rounds [b0 + l], at most [2^-53 34/100 + 2^-55 + 2^-1075]. *)
pose proof B3l as B3l'. apply Rabs_le_inv in B3l'.
assert (Hs2 : Rabs (B2R b0 + B2R l) <= 7 / 10 * bpow radix2 (-53)).
{ apply Rabs_le. rewrite Eb0. revert Bbh B3l'. num. intros. lra. }
destruct (add_kz b0 l (add b0 l) (7 / 10 * bpow radix2 (-53)) eq_refl Fb0 F3l Hs2
  ltac:(num; lra)) as (Fbl & _ & Bbl).
set (bl := add b0 l) in *.
split; [exact Fbh|]. split; [exact Fbl|].
split; [revert B3h Am' Bbh Eom; num; intros; lra|].
split; [pose proof Hs2 as H'; apply Rabs_le_inv in H'; apply Rabs_le; revert H' Bbl; num;
  intros; lra|].
(* [bh + bl - atB v] is [(h + l - 1/3) - (m - v (1/5 - ...))] plus the
   rounding error of [bl]. *)
unfold atB.
pose proof Em as E'. pose proof B3 as B3'. apply Rabs_le_inv in E', B3'.
apply Rabs_le. revert Eb0 Eom E' B3' Bbl. num. intros. lra.
Qed.

(** [u^3] as [wh + wl], with [wh] the rounding of [x vh] and [wh + e1 = x
    vh] exactly (TwoProduct). *)
Local Lemma ap_w :
  forall fma uh ul vh vl,
  is_finite uh = true -> is_finite ul = true -> is_finite vh = true -> is_finite vl = true ->
  bpow radix2 (-82) <= Rabs (B2R uh) <= bpow radix2 (-7) ->
  Rabs (B2R ul) <= bpow radix2 (-53) * Rabs (B2R uh) ->
  0 <= B2R vh ->
  Rabs (B2R vh - B2R uh * B2R uh) <= bpow radix2 (-53) * (B2R uh * B2R uh) ->
  Rabs (B2R vl) <= bpow radix2 (-51) * (B2R uh * B2R uh) ->
  Rabs (B2R vh + B2R vl - (B2R uh + B2R ul) * (B2R uh + B2R ul)) <=
    bpow radix2 (-102) * (B2R uh * B2R uh) ->
  let wh := mul uh vh in
  let wl := add (Generic.two_prod_err fma uh vh wh) (add (mul uh vl) (mul ul vh)) in
  is_finite wh = true /\ is_finite wl = true /\
  (forall b, Generic.two_prod_is_exact b uh vh wh = true) /\
  (1 - bpow radix2 (-51)) * (Rabs (B2R uh) * (B2R uh * B2R uh)) <= Rabs (B2R wh) <=
    (1 + bpow radix2 (-51)) * (Rabs (B2R uh) * (B2R uh * B2R uh)) /\
  Rabs (B2R wl) <= bpow radix2 (-50) * (Rabs (B2R uh) * (B2R uh * B2R uh)) /\
  Rabs (B2R wh + B2R wl -
        (B2R uh + B2R ul) * ((B2R uh + B2R ul) * (B2R uh + B2R ul))) <=
    bpow radix2 (-100) * (Rabs (B2R uh) * (B2R uh * B2R uh)).
Proof.
intros fma uh ul vh vl Fu Fl Fvh Fvl Hx Hy Hvh0 Rvh Bvl Evv. cbv zeta.
pose proof (bpow_gt_0 radix2 (-82)) as P82.
pose proof (bpow_gt_0 radix2 (-1075)) as Peps.
pose proof (Rabs_pos (B2R uh)) as PX.
(* [S = x^2 = X^2] lies in [[2^-164, 2^-14]] and [C = X S] in
   [[2^-246, 2^-21]], so [eps = 2^-1075] is at most [2^-800 C]. *)
assert (ES : B2R uh * B2R uh = Rabs (B2R uh) * Rabs (B2R uh)).
{ rewrite <- Rabs_mult. symmetry. apply Rabs_pos_eq. pose proof (Rle_0_sqr (B2R uh)) as H.
  unfold Rsqr in H. exact H. }
assert (HS : bpow radix2 (-164) <= B2R uh * B2R uh <= bpow radix2 (-14)).
{ rewrite ES. split.
  - replace (bpow radix2 (-164)) with (bpow radix2 (-82) * bpow radix2 (-82))
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; lra.
  - replace (bpow radix2 (-14)) with (bpow radix2 (-7) * bpow radix2 (-7))
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; lra. }
pose proof (bpow_gt_0 radix2 (-164)) as P164.
assert (HC : bpow radix2 (-246) <= Rabs (B2R uh) * (B2R uh * B2R uh) <= bpow radix2 (-21)).
{ split.
  - replace (bpow radix2 (-246)) with (bpow radix2 (-82) * bpow radix2 (-164))
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; lra.
  - replace (bpow radix2 (-21)) with (bpow radix2 (-7) * bpow radix2 (-14))
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; lra. }
pose proof (bpow_gt_0 radix2 (-246)) as P246.
assert (Heps : bpow radix2 (-1075) <=
               bpow radix2 (-800) * (Rabs (B2R uh) * (B2R uh * B2R uh))).
{ apply Rle_trans with (bpow radix2 (-800) * bpow radix2 (-246)).
  - rewrite <- bpow_plus. apply bpow_le. lia.
  - apply Rmult_le_compat_l; [apply bpow_ge_0 | apply HC]. }
(* [vh] is within [2^-53 S] of [S], so [X vh] is within [2^-53 C] of [C]. *)
pose proof Rvh as Rvh'. apply Rabs_le_inv in Rvh'.
assert (HXv : Rabs (B2R uh) * ((1 - bpow radix2 (-53)) * (B2R uh * B2R uh)) <=
              Rabs (B2R uh) * B2R vh <=
              Rabs (B2R uh) * ((1 + bpow radix2 (-53)) * (B2R uh * B2R uh))).
{ split; apply Rmult_le_compat_l; lra. }
assert (Axv : Rabs (B2R uh * B2R vh) = Rabs (B2R uh) * B2R vh)
  by (rewrite Rabs_mult, (Rabs_pos_eq (B2R vh)) by lra; reflexivity).
(* [wh] is [x vh] rounded and [e1 = x vh - wh] exactly (TwoProduct). *)
assert (Hx1 : Rabs (B2R uh) < 1) by (revert Hx; num; intros; lra).
assert (Hv1 : Rabs (B2R vh) < 1).
{ rewrite Rabs_pos_eq by lra. revert Rvh' HS. num. intros. lra. }
assert (Ex : forall b, Generic.two_prod_is_exact b uh vh (mul uh vh) = true).
{ intros b. apply tp_exact; [exact Fu | exact Fvh | | exact Hx1 | exact Hv1].
  rewrite Axv. revert HXv HC. num. intros. lra. }
destruct (two_prod_err_correct fma uh vh Fu Fvh (Ex fma)) as (Fwh & Ewh & _ & Fe1 & Ee1).
set (wh := mul uh vh) in *.
set (e1 := Generic.two_prod_err fma uh vh wh) in *.
assert (Rwh : Rabs (B2R wh - B2R uh * B2R vh) <= bpow radix2 (-53) * Rabs (B2R uh * B2R vh)).
{ rewrite Ewh. apply rn_rel. rewrite Axv. revert HXv HC. num. intros. lra. }
rewrite Axv in Rwh.
(* [|wh|] is within [2^-53 X vh] of [X vh] (triangle inequality). *)
assert (Awh : Rabs (B2R uh) * B2R vh - bpow radix2 (-53) * (Rabs (B2R uh) * B2R vh) <=
              Rabs (B2R wh) <=
              Rabs (B2R uh) * B2R vh + bpow radix2 (-53) * (Rabs (B2R uh) * B2R vh)).
{ rewrite <- Axv in Rwh |- *. split.
  - pose proof (Rabs_triang_inv (B2R uh * B2R vh) (B2R uh * B2R vh - B2R wh)) as T.
    rewrite Rabs_minus_sym in T.
    replace (B2R uh * B2R vh - (B2R uh * B2R vh - B2R wh)) with (B2R wh) in T by ring. lra.
  - pose proof (Rabs_triang (B2R uh * B2R vh) (B2R wh - B2R uh * B2R vh)) as T.
    replace (B2R uh * B2R vh + (B2R wh - B2R uh * B2R vh)) with (B2R wh) in T by ring. lra. }
apply Rabs_le_inv in Rwh.
(* [m1 = RN(x vl)], with [|x vl| <= 2^-51 C]. *)
assert (H1 : Rabs (B2R uh * B2R vl) <=
             Rabs (B2R uh) * (bpow radix2 (-51) * (B2R uh * B2R uh)))
  by (apply Rabs_mul_le; [apply Rle_refl | exact Bvl]).
destruct (mul_kz uh vl (mul uh vl) _ eq_refl Fu Fvl H1 ltac:(revert HC; num; intros; lra))
  as (Fm1 & _ & Bm1).
set (m1 := mul uh vl) in *.
(* [m2 = RN(y vh)], with [|y vh| <= 2^-53 X vh]. *)
assert (H2 : Rabs (B2R ul * B2R vh) <= bpow radix2 (-53) * Rabs (B2R uh) * B2R vh).
{ apply Rabs_mul_le; [exact Hy | rewrite Rabs_pos_eq by lra; apply Rle_refl]. }
destruct (mul_kz ul vh (mul ul vh) _ eq_refl Fl Fvh H2
  ltac:(revert HXv HC; num; intros; lra)) as (Fm2 & _ & Bm2).
set (m2 := mul ul vh) in *.
apply Rabs_le_inv in H1, H2.
(* [p = RN(m1 + m2)], with [|m1 + m2| <= (2^-51 + 2^-53) C (1 + 2^-52)]. *)
assert (Hp : Rabs (B2R m1 + B2R m2) <= bpow radix2 (-50) * (Rabs (B2R uh) * (B2R uh * B2R uh))).
{ apply Rabs_le. revert H1 H2 Bm1 Bm2 HXv Heps HC. num. intros. lra. }
destruct (add_kz m1 m2 (add m1 m2) _ eq_refl Fm1 Fm2 Hp ltac:(revert HC; num; intros; lra))
  as (Fp & _ & Bp).
set (p := add m1 m2) in *.
(* [wl = RN(e1 + p)], with [|e1| <= 2^-53 C (1 + 2^-52)]. *)
assert (Hw : Rabs (B2R e1 + B2R p) <= bpow radix2 (-50) * (Rabs (B2R uh) * (B2R uh * B2R uh))).
{ apply Rabs_le. revert Ee1 Rwh H1 H2 Bm1 Bm2 Bp HXv Heps HC. num. intros. lra. }
destruct (add_kz e1 p (add e1 p) _ eq_refl Fe1 Fp Hw ltac:(revert HC; num; intros; lra))
  as (Fwl & _ & Bwl).
set (wl := add e1 p) in *.
(* The identity [x vh + x vl + y vh - u^3 = u (vh + vl - u^2) - y vl]
   bounds the error by the two products below. *)
assert (Hu : Rabs (B2R uh + B2R ul) <= Rabs (B2R uh) + bpow radix2 (-53) * Rabs (B2R uh))
  by (eapply Rle_trans; [apply Rabs_triang | lra]).
assert (H3 : Rabs ((B2R uh + B2R ul) *
                   (B2R vh + B2R vl - (B2R uh + B2R ul) * (B2R uh + B2R ul))) <=
             (Rabs (B2R uh) + bpow radix2 (-53) * Rabs (B2R uh)) *
             (bpow radix2 (-102) * (B2R uh * B2R uh)))
  by (apply Rabs_mul_le; [exact Hu | exact Evv]).
assert (H4 : Rabs (B2R ul * B2R vl) <=
             bpow radix2 (-53) * Rabs (B2R uh) * (bpow radix2 (-51) * (B2R uh * B2R uh)))
  by (apply Rabs_mul_le; [exact Hy | exact Bvl]).
apply Rabs_le_inv in H3, H4.
split; [exact Fwh |]. split; [exact Fwl |]. split; [exact Ex |].
split; [| split].
- (* [|wh| = X vh (1 +- 2^-53)], and [(1 + 2^-53)^2 <= 1 + 2^-51]. *)
  revert Awh HXv HC. num. intros. split; lra.
- apply Rabs_le. revert Ee1 Rwh H1 H2 Bm1 Bm2 Bp Bwl HXv Heps HC. num. intros. lra.
- (* [wh + wl - u^3 = u (vh + vl - u^2) - y vl] plus the errors of [m1],
     [m2], [p] and [wl]: about [(2^-102 + 2^-104 + 2^-104 + 2^-106 +
     2^-103 + 2^-103) C]. *)
  apply Rabs_le. revert Ee1 H3 H4 Bm1 Bm2 Bp Bwl HXv Heps HC. num. intros. lra.
Qed.

(** The product [ch + cl] of the double-doubles [wh + wl], near [C] in
    magnitude, and [bh + bl], near [1/3]. *)
Local Lemma ap_c :
  forall fma wh wl bh bl C,
  is_finite wh = true -> is_finite wl = true -> is_finite bh = true -> is_finite bl = true ->
  bpow radix2 (-246) <= C <= bpow radix2 (-21) ->
  (1 - bpow radix2 (-51)) * C <= Rabs (B2R wh) <= (1 + bpow radix2 (-51)) * C ->
  Rabs (B2R wl) <= bpow radix2 (-50) * C ->
  33 / 100 <= B2R bh <= 34 / 100 -> Rabs (B2R bl) <= bpow radix2 (-53) ->
  let ch := mul wh bh in
  let cl := add (Generic.two_prod_err fma wh bh ch) (add (mul wh bl) (mul wl bh)) in
  is_finite ch = true /\ is_finite cl = true /\
  (forall b, Generic.two_prod_is_exact b wh bh ch = true) /\
  Rabs (B2R ch) <= 35 / 100 * C /\ Rabs (B2R cl) <= bpow radix2 (-50) * C /\
  Rabs (B2R ch + B2R cl - (B2R wh + B2R wl) * (B2R bh + B2R bl)) <= bpow radix2 (-101) * C.
Proof.
intros fma wh wl bh bl C Fwh Fwl Fbh Fbl HC Hwh Hwl Hbh Hbl. cbv zeta.
pose proof (bpow_gt_0 radix2 (-246)) as P246.
pose proof (bpow_gt_0 radix2 (-1075)) as Peps.
assert (Heps : bpow radix2 (-1075) <= bpow radix2 (-800) * C).
{ apply Rle_trans with (bpow radix2 (-800) * bpow radix2 (-246)).
  - rewrite <- bpow_plus. apply bpow_le. lia.
  - apply Rmult_le_compat_l; [apply bpow_ge_0 | apply HC]. }
assert (Abh : Rabs (B2R bh) = B2R bh) by (apply Rabs_pos_eq; lra).
(* [|wh bh|] lies in [[(1 - 2^-51) C 33/100, (1 + 2^-51) C 34/100]]. *)
assert (Hp : (1 - bpow radix2 (-51)) * C * (33 / 100) <= Rabs (B2R wh * B2R bh) <=
             (1 + bpow radix2 (-51)) * C * (34 / 100)).
{ rewrite Rabs_mult, Abh. split.
  - apply Rmult_le_compat; [revert HC; num; intros; lra | lra | apply Hwh | apply Hbh].
  - apply Rmult_le_compat; [apply Rabs_pos | lra | apply Hwh | apply Hbh]. }
(* [ch] is [wh bh] rounded and [e = wh bh - ch] exactly (TwoProduct). *)
assert (Ex : forall b, Generic.two_prod_is_exact b wh bh (mul wh bh) = true).
{ intros b. apply tp_exact; [exact Fwh | exact Fbh | | |].
  - eapply Rle_trans; [| apply Hp]. revert HC. num. intros. lra.
  - revert Hwh HC. num. intros. lra.
  - rewrite Abh. lra. }
destruct (two_prod_err_correct fma wh bh Fwh Fbh (Ex fma)) as (Fch & _ & _ & Fe & Ee).
destruct (mul_kz wh bh (mul wh bh) _ eq_refl Fwh Fbh (proj2 Hp)
  ltac:(revert HC; num; intros; lra)) as (_ & _ & Bch).
set (ch := mul wh bh) in *.
set (e := Generic.two_prod_err fma wh bh ch) in *.
(* [r1 = RN(wh bl)] and [r2 = RN(wl bh)], about [2^-53 C] and
   [0.34 2^-50 C]. *)
assert (H1 : Rabs (B2R wh * B2R bl) <= (1 + bpow radix2 (-51)) * C * bpow radix2 (-53))
  by (apply Rabs_mul_le; [apply Hwh | exact Hbl]).
destruct (mul_kz wh bl (mul wh bl) _ eq_refl Fwh Fbl H1 ltac:(revert HC; num; intros; lra))
  as (Fr1 & _ & Br1).
set (r1 := mul wh bl) in *.
assert (H2 : Rabs (B2R wl * B2R bh) <= bpow radix2 (-50) * C * (34 / 100))
  by (apply Rabs_mul_le; [exact Hwl | rewrite Abh; apply Hbh]).
destruct (mul_kz wl bh (mul wl bh) _ eq_refl Fwl Fbh H2 ltac:(revert HC; num; intros; lra))
  as (Fr2 & _ & Br2).
set (r2 := mul wl bh) in *.
(* The dropped [wl bl] is at most [2^-103 C]. *)
assert (H3 : Rabs (B2R wl * B2R bl) <= bpow radix2 (-50) * C * bpow radix2 (-53))
  by (apply Rabs_mul_le; [exact Hwl | exact Hbl]).
apply Rabs_le_inv in H1, H2, H3.
(* [p = RN(r1 + r2)], with [|r1 + r2| <= (2^-53 + 0.34 2^-50) C (1 + 2^-50)]. *)
assert (Hp12 : Rabs (B2R r1 + B2R r2) <= bpow radix2 (-51) * C).
{ apply Rabs_le. revert H1 H2 Br1 Br2 Heps HC. num. intros. lra. }
destruct (add_kz r1 r2 (add r1 r2) _ eq_refl Fr1 Fr2 Hp12 ltac:(revert HC; num; intros; lra))
  as (Fp & _ & Bp).
set (p := add r1 r2) in *.
apply Rabs_le_inv in Hp12.
(* [cl = RN(e + p)], with [|e| <= 2^-53 0.34 C (1 + 2^-50)]. *)
assert (Hep : Rabs (B2R e + B2R p) <= bpow radix2 (-50) * C).
{ apply Rabs_le. revert Ee Bch Bp Hp12 Hp Heps HC. num. intros. lra. }
destruct (add_kz e p (add e p) _ eq_refl Fe Fp Hep ltac:(revert HC; num; intros; lra))
  as (Fcl & _ & Bcl).
set (cl := add e p) in *.
apply Rabs_le_inv in Hep.
split; [exact Fch |]. split; [exact Fcl |]. split; [exact Ex |].
split; [| split].
- (* [|ch| <= |wh bh| + 2^-53 |wh bh| + eps]. *)
  assert (Ach : Rabs (B2R ch) <= Rabs (B2R wh * B2R bh) + Rabs (B2R ch - B2R wh * B2R bh)).
  { pose proof (Rabs_triang (B2R wh * B2R bh) (B2R ch - B2R wh * B2R bh)) as T.
    replace (B2R wh * B2R bh + (B2R ch - B2R wh * B2R bh)) with (B2R ch) in T by ring. exact T. }
  assert (Bch' : Rabs (B2R ch - B2R wh * B2R bh) <=
                 bpow radix2 (-53) * ((1 + bpow radix2 (-51)) * C * (34 / 100)) +
                 bpow radix2 (-1075)) by (apply Rabs_le; lra).
  revert Ach Bch' Hp Heps HC. num. intros. lra.
- apply Rabs_le. revert Ee Bch Bp Hp12 Bcl Heps HC. num. intros. lra.
- (* [ch + cl - (wh + wl) (bh + bl)] is the errors of [cl], [p], [r1]
     and [r2] ([e] is exact), minus the dropped [wl bl]: about
     [(2^-103 + 2^-104 + 2^-106 + 0.34 2^-103 + 2^-103) C + 4 eps]. *)
  replace ((B2R wh + B2R wl) * (B2R bh + B2R bl))
    with (B2R wh * B2R bh + B2R wh * B2R bl + B2R wl * B2R bh + B2R wl * B2R bl)
    by ring.
  apply Rabs_le. revert Ee Bcl Bp Br1 Br2 H1 H2 H3 Heps HC. num. intros. lra.
Qed.

(** [x - (ch + cl) + y] as the double-double [rh + rl], with [rh] the
    rounding of [rh + rl] to nearest. *)
Local Lemma ap_final :
  forall uh ul ch cl,
  is_finite uh = true -> is_finite ul = true -> is_finite ch = true -> is_finite cl = true ->
  bpow radix2 (-82) <= Rabs (B2R uh) <= bpow radix2 (-7) ->
  Rabs (B2R ul) <= bpow radix2 (-53) * Rabs (B2R uh) ->
  Rabs (B2R ch) <= bpow radix2 (-15) * Rabs (B2R uh) ->
  Rabs (B2R cl) <= bpow radix2 (-60) * Rabs (B2R uh) ->
  let '(sh, s0) := Fast.fast_two_sum uh (opp ch) in
  let '(rh, rl) := Fast.fast_two_sum sh (sub (add s0 ul) cl) in
  is_finite rh = true /\ is_finite rl = true /\ B2R rh = RN (B2R rh + B2R rl) /\
  Rabs (B2R rh + B2R rl - (B2R uh + B2R ul - B2R ch - B2R cl)) <=
    bpow radix2 (-102) * Rabs (B2R uh).
Proof.
intros uh ul ch cl Fu Fl Fch Fcl Hx Hy Hch Hcl.
unfold Fast.fast_two_sum. cbv beta iota zeta.
pose proof (bpow_gt_0 radix2 (-82)) as P82.
pose proof (bpow_gt_0 radix2 (-1075)) as Peps.
assert (Heps : bpow radix2 (-1075) <= bpow radix2 (-900) * Rabs (B2R uh)).
{ apply Rle_trans with (bpow radix2 (-900) * bpow radix2 (-82)).
  - rewrite <- bpow_plus. apply bpow_le. lia.
  - apply Rmult_le_compat_l; [apply bpow_ge_0 | apply Hx]. }
destruct (opp_F ch Fch) as (Fn & En).
(* [sh = RN(x - ch)], and [s0 = x - ch - sh] exactly (Fast2Sum), with
   [|ch| <= 2^-15 X]. *)
assert (Hs : Rabs (B2R uh + B2R (opp ch)) <= Rabs (B2R uh) + bpow radix2 (-15) * Rabs (B2R uh)).
{ eapply Rle_trans; [apply Rabs_triang |]. rewrite En, Rabs_Ropp. lra. }
destruct (add_kz uh (opp ch) (add uh (opp ch)) _ eq_refl Fu Fn Hs
  ltac:(revert Hx; num; intros; lra)) as (Fsh & Esh & Bsh).
assert (Hle : Rabs (B2R (opp ch)) <= Rabs (B2R uh)).
{ rewrite En, Rabs_Ropp. revert Hch Hx. num. intros. lra. }
destruct (CancelLanes.fast_two_sum uh (opp ch) (add uh (opp ch)) Fu Fn Hle Fsh Esh)
  as (Fs0 & Es0).
rewrite En in Bsh, Es0.
set (sh := add uh (opp ch)) in *.
set (s0 := add (opp ch) (sub uh sh)) in *.
(* [|sh| >= X - |ch| - |sh - (x - ch)| >= X / 2]. *)
assert (Lsh : Rabs (B2R uh) - Rabs (B2R ch) - Rabs (B2R sh - (B2R uh + - B2R ch)) <=
              Rabs (B2R sh)).
{ pose proof (Rabs_triang_inv (B2R uh) (B2R ch)) as T1.
  change (B2R uh - B2R ch) with (B2R uh + - B2R ch) in T1.
  pose proof (Rabs_triang_inv (B2R uh + - B2R ch) (B2R uh + - B2R ch - B2R sh)) as T2.
  replace (B2R uh + - B2R ch - (B2R uh + - B2R ch - B2R sh)) with (B2R sh) in T2 by ring.
  rewrite (Rabs_minus_sym (B2R uh + - B2R ch)) in T2. lra. }
assert (Bsh' : Rabs (B2R sh - (B2R uh + - B2R ch)) <=
               bpow radix2 (-53) * (Rabs (B2R uh) + bpow radix2 (-15) * Rabs (B2R uh)) +
               bpow radix2 (-1075)) by (apply Rabs_le; lra).
(* [t1 = RN(s0 + y)], with [|s0 + y| <= 2^-51 X]. *)
assert (H1 : Rabs (B2R s0 + B2R ul) <= bpow radix2 (-51) * Rabs (B2R uh)).
{ apply Rabs_le_inv in Hy. apply Rabs_le. revert Bsh Es0 Hy Heps Hx. num. intros. lra. }
destruct (add_kz s0 ul (add s0 ul) _ eq_refl Fs0 Fl H1 ltac:(revert Hx; num; intros; lra))
  as (Ft1 & _ & Bt1).
set (t1 := add s0 ul) in *.
apply Rabs_le_inv in H1.
(* [t2 = RN(t1 - cl)], with [|t1 - cl| <= 2^-50 X]. *)
assert (H2 : Rabs (B2R t1 - B2R cl) <= bpow radix2 (-50) * Rabs (B2R uh)).
{ apply Rabs_le_inv in Hcl. apply Rabs_le. revert Bt1 H1 Hcl Heps Hx. num. intros. lra. }
destruct (sub_kz t1 cl (sub t1 cl) _ eq_refl Ft1 Fcl H2 ltac:(revert Hx; num; intros; lra))
  as (Ft2 & Bt2).
set (t2 := sub t1 cl) in *.
apply Rabs_le_inv in H2.
(* [rh = RN(sh + t2)], and [rl = sh + t2 - rh] exactly (Fast2Sum), as
   [|t2| <= 2^-49 X <= X / 2 <= |sh|]. *)
assert (Hr : Rabs (B2R sh + B2R t2) <= 2 * Rabs (B2R uh)).
{ eapply Rle_trans; [apply Rabs_triang |].
  assert (Ash : Rabs (B2R sh) <= Rabs (B2R uh) + Rabs (B2R ch) +
                Rabs (B2R sh - (B2R uh + - B2R ch))).
  { pose proof (Rabs_triang (B2R uh + - B2R ch) (B2R sh - (B2R uh + - B2R ch))) as T.
    replace (B2R uh + - B2R ch + (B2R sh - (B2R uh + - B2R ch))) with (B2R sh) in T by ring.
    pose proof (Rabs_triang (B2R uh) (- B2R ch)) as T'. rewrite Rabs_Ropp in T'. lra. }
  assert (At2 : Rabs (B2R t2) <= bpow radix2 (-49) * Rabs (B2R uh)).
  { apply Rabs_le. revert Bt2 H2 Heps Hx. num. intros. lra. }
  revert Ash At2 Bsh' Hch Heps Hx. num. intros. lra. }
destruct (add_kz sh t2 (add sh t2) _ eq_refl Fsh Ft2 Hr ltac:(revert Hx; num; intros; lra))
  as (Frh & Erh & _).
assert (Hle2 : Rabs (B2R t2) <= Rabs (B2R sh)).
{ assert (At2 : Rabs (B2R t2) <= bpow radix2 (-49) * Rabs (B2R uh)).
  { apply Rabs_le. revert Bt2 H2 Heps Hx. num. intros. lra. }
  revert Lsh Bsh' At2 Hch Heps Hx. num. intros. lra. }
destruct (CancelLanes.fast_two_sum sh t2 (add sh t2) Fsh Ft2 Hle2 Frh Erh) as (Frl & Erl).
set (rh := add sh t2) in *.
set (rl := add t2 (sub sh rh)) in *.
assert (Hsum : B2R rh + B2R rl = B2R sh + B2R t2) by lra.
split; [exact Frh |]. split; [exact Frl |].
split; [rewrite Hsum; exact Erh |].
(* The error is that of [t1] and [t2]: at most [2 (2^-104 X + eps)]. *)
rewrite Hsum. apply Rabs_le. revert Bt1 Bt2 Es0 Heps Hx. num. intros. lra.
Qed.

(** The assembly of [fast_atan_poly_correct] on the reals: [atan u] is [u
    - u^3 B(u^2) + T u^13] with [0 <= T <= 1/13], and the result [r] is [u
    - c], [c] is the product of [w], near [u^3], and [b], near [B(u^2)],
    each within the bounds of the steps above, with [X] the magnitude of
    the high part of [u]. *)
Local Lemma ap_assemble :
  forall u X r c w b T : R,
  bpow radix2 (-82) <= X <= bpow radix2 (-7) ->
  (1 - bpow radix2 (-53)) * X <= Rabs u <= (1 + bpow radix2 (-53)) * X ->
  0 <= T <= / 13 ->
  Rabs (r - (u - c)) <= bpow radix2 (-102) * X ->
  Rabs (c - w * b) <= bpow radix2 (-101) * (X * (X * X)) ->
  Rabs (w - u * (u * u)) <= bpow radix2 (-100) * (X * (X * X)) ->
  Rabs b <= 35 / 100 -> Rabs (b - atB (u * u)) <= bpow radix2 (-65) ->
  Rabs (r - (u - u * (u * u) * atB (u * u) + T * u ^ 13)) <= bpow radix2 (-78) * Rabs u.
Proof.
intros u X r c w b T HX Hu HT Er Ec Ew Hb Eb.
pose proof (bpow_gt_0 radix2 (-82)) as P82.
(* [X^2 <= 2^-14] and [u^2 <= (1 + 2^-53)^2 X^2 <= (1 + 2^-51) 2^-14]. *)
assert (HXX : X * X <= bpow radix2 (-14)).
{ replace (bpow radix2 (-14)) with (bpow radix2 (-7) * bpow radix2 (-7))
    by (rewrite <- bpow_plus; reflexivity).
  apply Rmult_le_compat; lra. }
assert (HC : X * (X * X) <= X * bpow radix2 (-14)) by (apply Rmult_le_compat_l; lra).
assert (Eu : u * u = Rabs u * Rabs u).
{ rewrite <- Rabs_mult. symmetry. apply Rabs_pos_eq. pose proof (Rle_0_sqr u) as H.
  unfold Rsqr in H. exact H. }
assert (Hu2 : Rabs u * Rabs u <=
              ((1 + bpow radix2 (-53)) * X) * ((1 + bpow radix2 (-53)) * X))
  by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | apply Hu | apply Hu]).
assert (Hv : 0 <= u * u <= (1 + bpow radix2 (-51)) * bpow radix2 (-14)).
{ split; [rewrite Eu; apply Rmult_le_pos; apply Rabs_pos |].
  rewrite Eu. revert Hu2 HXX. num. intros. lra. }
(* The error of [b] times [u^3]: [2^-79 (1 + 2^-51) |u|]. *)
assert (H1 : Rabs (u * (u * u) * (b - atB (u * u))) <=
             Rabs u * ((1 + bpow radix2 (-51)) * bpow radix2 (-14)) * bpow radix2 (-65)).
{ apply Rabs_mul_le; [| exact Eb].
  apply Rabs_mul_le; [apply Rle_refl | rewrite Rabs_pos_eq by lra; apply Hv]. }
(* The error of [w] times [b]. *)
assert (H2 : Rabs ((w - u * (u * u)) * b) <=
             bpow radix2 (-100) * (X * (X * X)) * (35 / 100))
  by (apply Rabs_mul_le; [exact Ew | exact Hb]).
(* The truncation: [|T u^13| <= |u| (u^2)^6 / 13 <= 2^-78 |u| / 13]. *)
assert (H6 : (u * u) ^ 6 <= bpow radix2 (-78)).
{ apply Rle_trans with (bpow radix2 (-13) ^ 6).
  - apply pow_incr. split; [apply Hv |]. revert Hv. num. intros. lra.
  - cbn [pow]. rewrite Rmult_1_r, <- !bpow_plus. apply bpow_le. lia. }
assert (H3 : Rabs (T * u ^ 13) <= / 13 * (Rabs u * bpow radix2 (-78))).
{ replace (u ^ 13) with (u * (u * u) ^ 6) by ring.
  apply Rabs_mul_le; [rewrite Rabs_pos_eq by lra; apply HT |].
  rewrite Rabs_mult, (Rabs_pos_eq ((u * u) ^ 6)) by (apply pow_le; apply Hv).
  apply Rmult_le_compat_l; [apply Rabs_pos | exact H6]. }
(* The result's error is the sum of the five. *)
apply Rabs_le_inv in Er, Ec, H1, H2, H3.
apply Rabs_le. revert Er Ec H1 H2 H3 HC Hu HX. num. intros. split; lra.
Qed.

Theorem fast_atan_poly_correct :
  forall fma uh ul,
  is_finite uh = true -> is_finite ul = true ->
  bpow radix2 (-82) <= Rabs (B2R uh) <= bpow radix2 (-7) ->
  Rabs (B2R ul) <= bpow radix2 (-53) * Rabs (B2R uh) ->
  let '(ph, pl) := DyadicAtan.fast_atan_poly fma uh ul in
  is_finite ph = true /\ is_finite pl = true /\ B2R ph = RN (B2R ph + B2R pl) /\
  Rabs (B2R ph + B2R pl - atan (B2R uh + B2R ul)) <= bpow radix2 (-78) * Rabs (B2R uh + B2R ul).
Proof.
intros fma uh ul Fu Fl Hx Hy.
pose proof (bpow_gt_0 radix2 (-82)) as P82.
pose proof (Rabs_pos (B2R uh)) as PX.
(* [u^2] as [vh + vl]. *)
pose proof (ap_v fma uh ul Fu Fl Hx Hy) as Hv. cbv zeta in Hv.
destruct Hv as (Fvh & Fvl & _ & Bvh & Rvh & Bvl & Evh & Evv).
(* [S = x^2 = X^2], and [C = X S] is in [[2^-246, 2^-21]] and at most
   [2^-14 X]. *)
assert (ES : B2R uh * B2R uh = Rabs (B2R uh) * Rabs (B2R uh)).
{ rewrite <- Rabs_mult. symmetry. apply Rabs_pos_eq. pose proof (Rle_0_sqr (B2R uh)) as H.
  unfold Rsqr in H. exact H. }
assert (HS : bpow radix2 (-164) <= B2R uh * B2R uh <= bpow radix2 (-14)).
{ rewrite ES. split.
  - replace (bpow radix2 (-164)) with (bpow radix2 (-82) * bpow radix2 (-82))
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; lra.
  - replace (bpow radix2 (-14)) with (bpow radix2 (-7) * bpow radix2 (-7))
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; lra. }
pose proof (bpow_gt_0 radix2 (-164)) as P164.
assert (HC : bpow radix2 (-246) <= Rabs (B2R uh) * (B2R uh * B2R uh) <= bpow radix2 (-21)).
{ split.
  - replace (bpow radix2 (-246)) with (bpow radix2 (-82) * bpow radix2 (-164))
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; lra.
  - replace (bpow radix2 (-21)) with (bpow radix2 (-7) * bpow radix2 (-14))
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; lra. }
assert (HCX : Rabs (B2R uh) * (B2R uh * B2R uh) <= Rabs (B2R uh) * bpow radix2 (-14))
  by (apply Rmult_le_compat_l; lra).
unfold DyadicAtan.fast_atan_poly. cbv zeta.
set (vh := mul uh uh) in *.
set (vl := add (Generic.two_prod_err fma uh uh vh) (mul DyadicExp.two (mul uh ul))) in *.
(* [B(u^2)] as [bh + bl], with [|vh - u^2| <= 2^-51 S <= 2^-65]. *)
assert (Hd : Rabs (B2R vh - (B2R uh + B2R ul) * (B2R uh + B2R ul)) <= bpow radix2 (-65)).
{ apply Rle_trans with (1 := Evh). revert HS. num. intros. lra. }
assert (Hv0 : 0 <= (B2R uh + B2R ul) * (B2R uh + B2R ul) <= bpow radix2 (-13)).
{ split; [pose proof (Rle_0_sqr (B2R uh + B2R ul)) as H; unfold Rsqr in H; exact H |].
  apply Rabs_le_inv in Hd. revert Hd Bvh. num. intros. lra. }
destruct (Fast.fast_two_sum (from_bits (fst DyadicAtan.A3)) _) as [bh b0] eqn:Eb.
pose proof (ap_b vh _ Fvh Bvh Hv0 Hd) as Hb. cbv zeta in Hb.
rewrite Eb in Hb. cbv beta iota zeta in Hb. cbv beta iota.
destruct Hb as (Fbh & Fbl & Bbh & Bbl & Ebb).
set (bl := add b0 (from_bits (snd DyadicAtan.A3))) in *.
(* [u^3] as [wh + wl]. *)
destruct (ap_w fma uh ul vh vl Fu Fl Fvh Fvl Hx Hy (proj1 Bvh) Rvh Bvl Evv)
  as (Fwh & Fwl & _ & Bwh & Bwl & Ew).
set (wh := mul uh vh) in *.
set (wl := add (Generic.two_prod_err fma uh vh wh) (add (mul uh vl) (mul ul vh))) in *.
(* [u^3 B] as [ch + cl]. *)
destruct (ap_c fma wh wl bh bl _ Fwh Fwl Fbh Fbl HC Bwh Bwl Bbh Bbl)
  as (Fch & Fcl & _ & Bch & Bcl & Ec).
set (ch := mul wh bh) in *.
set (cl := add (Generic.two_prod_err fma wh bh ch) (add (mul wh bl) (mul wl bh))) in *.
(* [x + y - ch - cl] as [rh + rl], with [|ch| <= 0.35 C <= 2^-15 X] and
   [|cl| <= 2^-50 C <= 2^-64 X]. *)
assert (Hch : Rabs (B2R ch) <= bpow radix2 (-15) * Rabs (B2R uh))
  by (revert Bch HCX; num; intros; lra).
assert (Hcl : Rabs (B2R cl) <= bpow radix2 (-60) * Rabs (B2R uh))
  by (revert Bcl HCX PX; num; intros; lra).
pose proof (ap_final uh ul ch cl Fu Fl Fch Fcl Hx Hy Hch Hcl) as Hf.
(* [destruct] abstracts the sums in [Hf] too. *)
destruct (Fast.fast_two_sum uh _) as [sh s0]. cbv beta iota in Hf |- *.
destruct (Fast.fast_two_sum sh _) as [rh rl]. cbv beta iota in Hf |- *.
destruct Hf as (Frh & Frl & Rr & Ef).
(* The Taylor polynomial of [atan] is [u - u^3 B(u^2)], within [u^13/13]
   ([AtanSeries.atan_tail_bounds]). *)
destruct (atan_tail_bounds 6 (B2R uh + B2R ul)) as (T & HT & ET).
change (2 * 6 + 1)%nat with 13%nat in HT, ET.
assert (Hsum : atan_sum 6 (B2R uh + B2R ul) =
               (B2R uh + B2R ul) -
               (B2R uh + B2R ul) * ((B2R uh + B2R ul) * (B2R uh + B2R ul)) *
               atB ((B2R uh + B2R ul) * (B2R uh + B2R ul)))
  by (cbn [atan_sum INR pow Nat.mul Nat.add]; unfold atB; field).
replace (INR 13) with 13 in HT by (cbn [INR]; ring).
assert (HT' : 0 <= T <= / 13) by lra.
replace (atan (B2R uh + B2R ul)) with
  ((B2R uh + B2R ul) -
   (B2R uh + B2R ul) * ((B2R uh + B2R ul) * (B2R uh + B2R ul)) *
   atB ((B2R uh + B2R ul) * (B2R uh + B2R ul)) + T * (B2R uh + B2R ul) ^ 13)
  by (rewrite <- Hsum, ET; ring).
(* [u] is within [2^-53 X] of [x]. *)
assert (Hu : (1 - bpow radix2 (-53)) * Rabs (B2R uh) <= Rabs (B2R uh + B2R ul) <=
             (1 + bpow radix2 (-53)) * Rabs (B2R uh)).
{ split.
  - pose proof (Rabs_triang_inv (B2R uh) (- B2R ul)) as T1.
    rewrite Rabs_Ropp in T1. replace (B2R uh - - B2R ul) with (B2R uh + B2R ul) in T1 by ring.
    lra.
  - pose proof (Rabs_triang (B2R uh) (B2R ul)). lra. }
assert (Ef' : Rabs (B2R rh + B2R rl - ((B2R uh + B2R ul) - (B2R ch + B2R cl))) <=
              bpow radix2 (-102) * Rabs (B2R uh)).
{ replace (B2R uh + B2R ul - (B2R ch + B2R cl)) with
    (B2R uh + B2R ul - B2R ch - B2R cl) by ring. exact Ef. }
rewrite ES in Ec, Ew.
split; [exact Frh |]. split; [exact Frl |]. split; [exact Rr |].
apply (ap_assemble _ (Rabs (B2R uh)) _ _ _ _ T Hx Hu HT' Ef' Ec Ew); [| exact Ebb].
apply Rabs_le_inv in Bbl. apply Rabs_le. revert Bbl Bbh. num. intros. lra.
Qed.

Theorem fast_atan_poly_fma :
  forall uh ul,
  is_finite uh = true -> is_finite ul = true ->
  bpow radix2 (-82) <= Rabs (B2R uh) <= bpow radix2 (-7) ->
  Rabs (B2R ul) <= bpow radix2 (-53) * Rabs (B2R uh) ->
  DyadicAtan.fast_atan_poly true uh ul = DyadicAtan.fast_atan_poly false uh ul.
Proof.
intros uh ul Fu Fl Hx Hy.
(* [vh] and the exactness of [x^2], from [ap_v]. *)
pose proof (ap_v false uh ul Fu Fl Hx Hy) as Hv. cbv zeta in Hv.
destruct Hv as (Fvh & Fvl & Xv & Bvh & Rvh & Bvl & Evh & Evv).
unfold DyadicAtan.fast_atan_poly. cbv zeta.
rewrite (two_prod_err_fma_eq uh uh Fu Fu (Xv true) (Xv false)).
set (vh := mul uh uh) in *.
set (vl := add (Generic.two_prod_err false uh uh vh) (mul DyadicExp.two (mul uh ul))) in *.
(* The exactness of [x vh], from [ap_w]. *)
destruct (ap_w false uh ul vh vl Fu Fl Fvh Fvl Hx Hy (proj1 Bvh) Rvh Bvl Evv)
  as (Fwh & Fwl & Xw & Bwh & Bwl & _).
cbv zeta in Xw.
rewrite (two_prod_err_fma_eq uh vh Fu Fvh (Xw true) (Xw false)).
set (wh := mul uh vh) in *.
set (wl := add (Generic.two_prod_err false uh vh wh) (add (mul uh vl) (mul ul vh))) in *.
(* [bh] and [bl] from [ap_b], with [|vh - u^2| <= 2^-51 S <= 2^-65]. *)
assert (HS : B2R uh * B2R uh <= bpow radix2 (-14)).
{ replace (B2R uh * B2R uh) with (Rabs (B2R uh) * Rabs (B2R uh)).
  - replace (bpow radix2 (-14)) with (bpow radix2 (-7) * bpow radix2 (-7))
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | apply Hx | apply Hx].
  - rewrite <- Rabs_mult. apply Rabs_pos_eq. pose proof (Rle_0_sqr (B2R uh)) as H.
    unfold Rsqr in H. exact H. }
assert (Hd : Rabs (B2R vh - (B2R uh + B2R ul) * (B2R uh + B2R ul)) <= bpow radix2 (-65)).
{ apply Rle_trans with (1 := Evh). revert HS. num. intros. lra. }
assert (Hv0 : 0 <= (B2R uh + B2R ul) * (B2R uh + B2R ul) <= bpow radix2 (-13)).
{ split; [pose proof (Rle_0_sqr (B2R uh + B2R ul)) as H; unfold Rsqr in H; exact H |].
  apply Rabs_le_inv in Hd. revert Hd Bvh. num. intros. lra. }
destruct (Fast.fast_two_sum (from_bits (fst DyadicAtan.A3)) _) as [bh b0] eqn:Eb.
pose proof (ap_b vh _ Fvh Bvh Hv0 Hd) as Hb. cbv zeta in Hb.
rewrite Eb in Hb. cbv beta iota zeta in Hb. cbv beta iota.
destruct Hb as (Fbh & Fbl & Bbh & Bbl & _).
set (bl := add b0 (from_bits (snd DyadicAtan.A3))) in *.
(* The exactness of [wh bh], from [ap_c], with [C = X x^2]. *)
assert (HC : bpow radix2 (-246) <= Rabs (B2R uh) * (B2R uh * B2R uh) <= bpow radix2 (-21)).
{ assert (ES : B2R uh * B2R uh = Rabs (B2R uh) * Rabs (B2R uh)).
  { rewrite <- Rabs_mult. symmetry. apply Rabs_pos_eq. pose proof (Rle_0_sqr (B2R uh)) as H.
    unfold Rsqr in H. exact H. }
  rewrite ES. split.
  - replace (bpow radix2 (-246)) with
      (bpow radix2 (-82) * (bpow radix2 (-82) * bpow radix2 (-82)))
      by (rewrite <- !bpow_plus; reflexivity).
    pose proof (bpow_ge_0 radix2 (-82)).
    apply Rmult_le_compat; [lra | apply Rmult_le_pos; lra | apply Hx |].
    apply Rmult_le_compat; [lra | lra | apply Hx | apply Hx].
  - replace (bpow radix2 (-21)) with
      (bpow radix2 (-7) * (bpow radix2 (-7) * bpow radix2 (-7)))
      by (rewrite <- !bpow_plus; reflexivity).
    apply Rmult_le_compat; [apply Rabs_pos | apply Rmult_le_pos; apply Rabs_pos | apply Hx |].
    apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | apply Hx | apply Hx]. }
destruct (ap_c true wh wl bh bl _ Fwh Fwl Fbh Fbl HC Bwh Bwl Bbh Bbl) as (_ & _ & Xc & _).
cbv zeta in Xc.
rewrite (two_prod_err_fma_eq wh bh Fwh Fbh (Xc true) (Xc false)).
reflexivity.
Qed.
