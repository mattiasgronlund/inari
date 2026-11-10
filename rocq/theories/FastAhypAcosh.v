(** * The fast path of [acosh] before the rounding

    [DyadicLog.fast_acosh] of [Model.v] returns [None] for [x <= 1], and
    otherwise computes [acosh x = ln(x + r)] with [r = sqrt(x^2 - 1)] in
    double-double ([Fast.dd_sqrt], [FastDdSqrt.v]), where [x^2 - 1] is
    exact below [2^26] ([ph - 1] is exact and [|pl| <= |ph - 1|]): as
    [ln(1 + u)] for [u = (x - 1) + r] below [x = 1 + 2^-22]
    ([log1p_small_correct]), as [ln(x + r)] up to [2^26]
    ([fast_ln_dd_correct] with [e0 = 0]), and from [2^26] on as
    [ln 2 + ln(x + RN(-1/(4x)))], since [0 <= (1 - s/2) - sqrt(1 - s) <= s^2/4]
    for [s = 1/x^2]. [fast_acosh_correct] shows that the result is within
    [2^-68] of [acosh x 2^-k], with [1/2 < |h| < 2]. *)

From Stdlib Require Import ZArith Reals Lra Lia Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error Sterbenz.
From Inari Require Import Model Elementary Encoding TwoSum TwoProduct FastRound FastRoundErr
  FastDiv FastDdSqrt FastLogTables FastLogPoly FastLogCore FastLogNorm FastLogFin FastLogDd
  FastExpErr.
From Flocq Require Import Relative.
From Inari Require MulRuTiny CancelLanes.

Open Scope R_scope.

Local Notation format := (generic_format radix2 fexp64).

(** ** Literals *)

Local Lemma one_R : is_finite DyadicExp.one = true /\ B2R DyadicExp.one = 1.
Proof.
split; [vm_compute; reflexivity |].
rewrite <- SF2R_B2SF.
replace (B2SF DyadicExp.one) with (SpecFloat.S754_finite false 4503599627370496 (-52))
  by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

Local Lemma acosh_small_R :
  is_finite DyadicLog.acosh_small = true /\ B2R DyadicLog.acosh_small = bpow radix2 (-22).
Proof.
split; [vm_compute; reflexivity |].
rewrite <- SF2R_B2SF.
replace (B2SF DyadicLog.acosh_small) with (SpecFloat.S754_finite false 4503599627370496 (-74))
  by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

Local Lemma ahyp_large_R :
  is_finite DyadicLog.ahyp_large = true /\ B2R DyadicLog.ahyp_large = bpow radix2 26.
Proof.
split; [vm_compute; reflexivity |].
rewrite <- SF2R_B2SF.
replace (B2SF DyadicLog.ahyp_large) with (SpecFloat.S754_finite false 4503599627370496 (-26))
  by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

Local Lemma neg_quarter_R :
  is_finite DyadicLog.neg_quarter = true /\ B2R DyadicLog.neg_quarter = - / 4.
Proof.
split; [vm_compute; reflexivity |].
rewrite <- SF2R_B2SF.
replace (B2SF DyadicLog.neg_quarter) with (SpecFloat.S754_finite true 4503599627370496 (-54))
  by (vm_compute; reflexivity).
cbn [SF2R cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
rewrite opp_IZR.
change (IZR 4503599627370496) with (bpow radix2 52).
rewrite Ropp_mult_distr_l_reverse, <- bpow_plus. change (bpow radix2 (52 + -54)) with (/ 4).
reflexivity.
Qed.

(** ** Comparisons *)

Local Lemma le_false :
  forall x y, is_finite x = true -> is_finite y = true -> Model.le x y = false -> B2R y < B2R x.
Proof.
intros x y Fx Fy H. unfold Model.le in H. rewrite Bleb_correct in H by assumption.
destruct (Rle_bool_spec (B2R x) (B2R y)); [discriminate | assumption].
Qed.

Local Lemma lt_true :
  forall x y, is_finite x = true -> is_finite y = true -> Model.lt x y = true -> B2R x < B2R y.
Proof.
intros x y Fx Fy H. unfold Model.lt in H. rewrite Bltb_correct in H by assumption.
destruct (Rlt_bool_spec (B2R x) (B2R y)); [assumption | discriminate].
Qed.

Local Lemma lt_false :
  forall x y, is_finite x = true -> is_finite y = true -> Model.lt x y = false -> B2R y <= B2R x.
Proof.
intros x y Fx Fy H. unfold Model.lt in H. rewrite Bltb_correct in H by assumption.
destruct (Rlt_bool_spec (B2R x) (B2R y)); [discriminate | assumption].
Qed.

(** ** Exact steps *)

(** [Fast.fast_two_sum a b] with [|b| <= |a|] and [|a + b| <= MAX] is
    Dekker's FastTwoSum (T. J. Dekker, A floating-point technique for
    extending the available precision, 1971): [s = RN(a + b)] and
    [s + t = a + b] exactly. As [FastLogNorm.fts_exact], up to [MAX]. *)
Local Lemma ac_fts :
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

(** [p - 1] is a [f64] for every [f64] [p] in [[1, 2^53)]: by Sterbenz's
    lemma (P. H. Sterbenz, Floating-point computation, 1974) up to [2], and
    above as an integer multiple of the ulp of [p], below [p]. *)
Local Lemma ac_sub_one :
  forall p, format p -> 1 <= p < bpow radix2 53 -> format (p - 1).
Proof.
intros p Fp Hp.
assert (F1 : format 1).
{ change 1 with (bpow radix2 0). apply generic_format_bpow. unfold FLT_exp. lia. }
destruct (Rle_lt_dec p 2) as [H2 | H2].
{ apply sterbenz; try exact Fp; try exact F1; try lra; typeclasses eauto. }
set (e := cexp radix2 fexp64 p).
assert (Hm : (mag radix2 p <= 53)%Z).
{ apply mag_le_bpow; [lra | rewrite Rabs_pos_eq; lra]. }
assert (He : (e <= 0)%Z) by (unfold e, cexp, FLT_exp; lia).
assert (Ep : p = F2R (Float radix2 (Ztrunc (scaled_mantissa radix2 fexp64 p)) e)) by exact Fp.
assert (E1 : 1 = F2R (Float radix2 (Zpower radix2 (- e)) e)).
{ unfold F2R; cbn [Fnum Fexp]. rewrite IZR_Zpower by lia. rewrite <- bpow_plus.
  replace (- e + e)%Z with 0%Z by lia. reflexivity. }
assert (Ed : p - 1 = F2R (Float radix2 (Ztrunc (scaled_mantissa radix2 fexp64 p)
                                         - Zpower radix2 (- e)) e)).
{ rewrite Ep at 1. rewrite E1 at 1. unfold F2R; cbn [Fnum Fexp]. rewrite minus_IZR. ring. }
rewrite Ed. apply generic_format_F2R. intros _. rewrite <- Ed.
unfold cexp. fold e.
assert (Hl : (mag radix2 (p - 1) <= mag radix2 p)%Z).
{ apply mag_le; [lra | lra]. }
unfold e, cexp, FLT_exp. lia.
Qed.

(** ** Rounding to nearest *)

(** The rounding to nearest of a normal [x] is within [2^-53] of [x]
    relatively to the result (as [FastTrigSC.rn_rel]). *)
Local Lemma rn_rel :
  forall x, bpow radix2 (-1022) <= Rabs x ->
  Rabs (RN x - x) <= bpow radix2 (-53) * Rabs (RN x).
Proof.
intros x Hx.
assert (H : Rabs (RN x - x) <= / 2 * bpow radix2 (-52) * Rabs (RN x))
  by exact (relative_error_N_FLT_round radix2 (-1074) 53 eq_refl
    (fun z => negb (Z.even z)) x Hx).
assert (E : / 2 * bpow radix2 (-52) = bpow radix2 (-53))
  by (cbn [bpow radix_val radix2]; lra).
rewrite E in H. exact H.
Qed.

(** Rounding to nearest is monotone, and leaves a [f64] in place. *)
Local Lemma rn_ge :
  forall a b, format a -> a <= b -> a <= RN b.
Proof.
intros a b Fa H.
rewrite <- (round_generic radix2 fexp64 ZnearestE a Fa) at 1.
apply round_le; [typeclasses eauto .. | exact H].
Qed.

Local Lemma rn_le :
  forall a b, format a -> b <= a -> RN b <= a.
Proof.
intros a b Fa H.
rewrite <- (round_generic radix2 fexp64 ZnearestE a Fa).
apply round_le; [typeclasses eauto .. | exact H].
Qed.

(** ** Logarithms *)

Local Lemma ln_le_mono : forall a b, 0 < a -> a <= b -> ln a <= ln b.
Proof.
intros a b Ha Hab.
destruct (Req_dec a b) as [<- | Hn]; [lra |].
apply Rlt_le, ln_increasing; lra.
Qed.

(** [ln q <= q - 1], from [1 + z <= e^z]. *)
Local Lemma ln_le_sub1 : forall q, 0 < q -> ln q <= q - 1.
Proof.
intros q Hq.
pose proof (exp_ineq1_le (q - 1)) as H.
rewrite <- (ln_exp (q - 1)).
apply ln_le_mono; [exact Hq | lra].
Qed.

(** [1 - 1/q <= ln q], the same applied to [1/q]. *)
Local Lemma ln_ge_sub1 : forall q, 0 < q -> 1 - / q <= ln q.
Proof.
intros q Hq.
pose proof (ln_le_sub1 (/ q) (Rinv_0_lt_compat q Hq)) as H.
rewrite ln_Rinv in H by exact Hq. lra.
Qed.

(** [u/2 <= ln(1 + u)] on [[0, 1]], as [u/(1 + u) <= ln(1 + u)]. *)
Local Lemma ln_half : forall u, 0 <= u <= 1 -> u / 2 <= ln (1 + u).
Proof.
intros u Hu.
pose proof (ln_ge_sub1 (1 + u) ltac:(lra)) as H.
assert (I : / (1 + u) * (1 + u) = 1) by (field; lra).
assert (I0 : 0 < / (1 + u)) by (apply Rinv_0_lt_compat; lra).
nra.
Qed.

(** Two close positive reals have close logarithms: for [|B - A| <= e A]
    and [e <= 1/4], [|ln A - ln B| = |ln(B/A)| <= 2e]. *)
Local Lemma ac_ln_close :
  forall A B e, 0 < A -> Rabs (B - A) <= e * A -> e <= / 4 ->
  Rabs (ln A - ln B) <= 2 * e.
Proof.
intros A B e HA H He.
apply Rabs_le_inv in H.
assert (He0 : 0 <= e) by nra.
set (q := B / A).
assert (Eq : B = A * q) by (unfold q; field; lra).
assert (Hq : 1 - e <= q <= 1 + e).
{ rewrite Eq in H. split; nra. }
assert (Hq0 : 0 < q) by lra.
rewrite Eq, ln_mult by assumption.
pose proof (ln_le_sub1 q Hq0) as L1.
pose proof (ln_ge_sub1 q Hq0) as L2.
assert (I : / q * q = 1) by (field; lra).
assert (I0 : 0 < / q) by (apply Rinv_0_lt_compat; lra).
assert (I1 : / q * (1 - e) <= 1) by nra.
assert (I2 : / q <= 1 + 2 * e) by nra.
apply Rabs_le. lra.
Qed.

(** ** Division *)

(** [x / y] of finite [f64]s with an exact result of at most [MAX] in
    magnitude is finite and rounded to nearest (as [FastDdSqrt.div_e]). *)
Local Lemma ac_div :
  forall x y, is_finite x = true -> is_finite y = true -> B2R y <> 0 ->
  Rabs (B2R x / B2R y) <= MAX ->
  is_finite (div x y) = true /\ B2R (div x y) = RN (B2R x / B2R y).
Proof.
intros x y Fx Fy Hy H.
destruct (RN_below_max _ H) as (Hlt & _).
generalize (@Bdiv_correct 53 1024 _ _ mode_NE x y Hy).
rewrite Rlt_bool_true by exact Hlt.
intros (HR & HF & _).
change (Bdiv mode_NE x y) with (div x y) in HR, HF.
rewrite Fx in HF. split; [exact HF | exact HR].
Qed.

(** ** From [2^26] on *)

(** With [iv = 1/x], [a = x - iv/2] and [r = sqrt(x^2 - 1)],
    [(a - r)(a + r) = iv^2/4] and [a + r >= x], so [0 <= a - r <= iv^3/4]:
    [2(x + RN(-1/(4x)))] is within [2^-78] of [x + r], and
    [acosh x = ln 2 + ln(x + xl)] up to [2^-103]. *)
Local Lemma ac_large :
  forall x xl, is_finite x = true -> bpow radix2 26 <= B2R x ->
  div DyadicLog.neg_quarter x = xl ->
  is_finite xl = true /\ 0 < B2R x /\ Rabs (B2R xl) <= bpow radix2 (-51) * B2R x /\
  B2R x * bpow radix2 1 <= bpow radix2 1025 /\
  bpow radix2 (-20) <= Rabs (Racosh (B2R x)) /\
  Rabs (Racosh (B2R x) - (IZR 1 * ln 2 + ln (B2R x + B2R xl))) <=
    bpow radix2 (-80) * Rabs (Racosh (B2R x)).
Proof.
intros x xl Fx Hx Exl.
destruct neg_quarter_R as [Fq Eq].
pose proof (abs_B2R_lt_emax _ _ x) as Hmax.
cbn [bpow radix_val radix2 Z.opp] in Hx.
assert (B1024 : bpow radix2 1025 = 2 * bpow radix2 1024)
  by (change 1025%Z with (1 + 1024)%Z; rewrite bpow_plus; reflexivity).
assert (B1 : bpow radix2 1 = 2) by reflexivity.
assert (B51 : bpow radix2 (-51) = / 2251799813685248) by reflexivity.
assert (B20 : bpow radix2 (-20) = / 1048576) by reflexivity.
assert (B80 : bpow radix2 (-80) = / 1208925819614629174706176) by reflexivity.
rewrite B1, B1024, B51, B20, B80.
set (X := B2R x) in *.
rewrite Rabs_pos_eq in Hmax by lra.
assert (HX0 : 0 < X) by lra.
set (iv := / X).
assert (Iv : X * iv = 1) by (unfold iv; field; lra).
assert (Iv0 : 0 < iv) by (unfold iv; apply Rinv_0_lt_compat; lra).
assert (Iv1 : iv <= / 67108864) by nra.
assert (Ez : B2R DyadicLog.neg_quarter / X = - (iv / 4)) by (rewrite Eq; unfold iv; field; lra).
assert (Hz : Rabs (B2R DyadicLog.neg_quarter / X) <= MAX).
{ apply FastExpErr.small_le_max. rewrite Ez, Rabs_Ropp, Rabs_pos_eq by lra. lra. }
destruct (ac_div DyadicLog.neg_quarter x Fq Fx (Rgt_not_eq _ _ HX0) Hz) as (Fxl & Exl').
rewrite Exl in Fxl, Exl'. fold X in Exl'. rewrite Ez in Exl'.
pose proof (FastExpErr.rn_err (- (iv / 4))) as Hl.
rewrite <- Exl', Rabs_Ropp, (Rabs_pos_eq (iv / 4)) in Hl by lra.
cbn [bpow radix_val radix2 Z.opp] in Hl.
apply Rabs_le_inv in Hl.
set (XL := B2R xl) in *.
(* [r = sqrt(x^2 - 1)] and [a = x - iv/2] *)
set (r := sqrt (X * X - 1)).
assert (HR2 : r * r = X * X - 1) by (apply sqrt_sqrt; nra).
assert (HR0 : 0 <= r) by apply sqrt_pos.
assert (HR1 : (X - iv) * (X - iv) <= r * r) by nra.
assert (HR3 : X - iv <= r) by nra.
set (a := X - iv / 2).
assert (Ea : (a - r) * (a + r) = iv * iv / 4).
{ transitivity (X * X - X * iv + iv * iv / 4 - r * r); [unfold a; field |].
  rewrite HR2, Iv. field. }
assert (HaR : X <= a + r) by (unfold a; lra).
assert (Hd0 : 0 <= a - r) by nra.
assert (Hd1 : (a - r) * X <= iv * iv / 4) by nra.
assert (Hd2 : a - r <= iv * iv * iv / 4).
{ replace (a - r) with ((a - r) * X * iv) by (rewrite Rmult_assoc, Iv; ring). nra. }
assert (Hiv3 : iv * iv * iv <= / 67108864 * / 67108864 * / 67108864).
{ apply Rmult_le_compat; [nra | lra | | lra]. apply Rmult_le_compat; lra. }
(* [A = x + r] and [B = 2 (x + xl)] *)
assert (HAB : Rabs (2 * (X + XL) - (X + r)) <= / 20282409603651670423947251286016 * (X + r)).
{ apply Rabs_le. unfold a in *. split; nra. }
assert (HA : 2 <= X + r) by lra.
assert (HL2 : / 2 < ln (X + r)).
{ pose proof ln_lt_2. pose proof (ln_le_mono 2 (X + r) ltac:(lra) HA). lra. }
pose proof (ac_ln_close (X + r) (2 * (X + XL)) _ ltac:(lra) HAB ltac:(lra)) as Hc.
rewrite ln_mult in Hc by lra.
unfold Racosh. fold X. fold r.
rewrite (Rabs_pos_eq (ln (X + r))) by lra.
repeat split; try assumption; try lra.
- apply Rabs_le. split; nra.
- replace (ln (X + r) - (IZR 1 * ln 2 + ln (X + XL)))
    with (ln (X + r) - (ln 2 + ln (X + XL))) by ring.
  lra.
Qed.

(** ** Below [2^26]: [x^2 - 1] in double-double *)

Local Lemma format_bpow64 : forall e, (-1074 <= e)%Z -> format (bpow radix2 e).
Proof. intros e He. apply generic_format_bpow. unfold FLT_exp. lia. Qed.

(** [x^2] of [x] in [(1, 2^26)] is between [1] and [2^52], with the
    exponents [TwoProduct] needs for both products. *)
Local Lemma ac_tpe :
  forall fma x, is_finite x = true -> 1 < B2R x < bpow radix2 26 ->
  Generic.two_prod_is_exact fma x x (mul x x) = true.
Proof.
intros fma x Fx Hx.
assert (B26 : bpow radix2 26 = 67108864) by reflexivity.
assert (B52 : bpow radix2 52 = 4503599627370496) by reflexivity.
assert (B53 : bpow radix2 53 = 9007199254740992) by reflexivity.
rewrite B26 in Hx.
destruct (mul_below_max x x Fx Fx) as (Fp & Ep & _).
{ rewrite Rabs_pos_eq by nra. cbn [bpow radix_val radix2 Z.opp]. nra. }
assert (P1 : 1 <= B2R (mul x x)).
{ rewrite Ep. apply rn_ge; [exact (format_bpow64 0 ltac:(lia)) | nra]. }
assert (P2 : B2R (mul x x) <= bpow radix2 52).
{ rewrite Ep. apply rn_le; [exact (format_bpow64 52 ltac:(lia)) | rewrite B52; nra]. }
pose proof (MulRuTiny.exponent_lt (mul x x) 53 Fp ltac:(lia)
  ltac:(rewrite Rabs_pos_eq, B53; lra)) as E1.
pose proof (MulRuTiny.exponent_ge (mul x x) 0 Fp
  ltac:(rewrite Rabs_pos_eq by lra; exact P1)) as E2.
pose proof (MulRuTiny.exponent_lt x 26 Fx ltac:(lia)
  ltac:(rewrite Rabs_pos_eq, B26; lra)) as E3.
unfold Generic.two_prod_is_exact. cbv zeta.
destruct fma; repeat (apply andb_true_intro; split); apply Z.leb_le; lia.
Qed.

(** [(ah, al)] is [x^2 - 1] exactly: [ph = RN(x^2)] is at least
    [RN((1 + 2^-52)^2)], so [|pl| <= 2^-53 ph <= ph - 1], [ph - 1] is exact
    ([ac_sub_one]), and FastTwoSum is exact. *)
Local Lemma ac_sq :
  forall fma x ah al, is_finite x = true -> 1 < B2R x < bpow radix2 26 ->
  Fast.fast_two_sum (sub (mul x x) DyadicExp.one) (Generic.two_prod_err fma x x (mul x x)) =
    (ah, al) ->
  is_finite ah = true /\ is_finite al = true /\ B2R ah + B2R al = B2R x * B2R x - 1 /\
  bpow radix2 (-52) <= B2R ah <= bpow radix2 52 /\
  Rabs (B2R al) <= bpow radix2 (-53) * B2R ah.
Proof.
intros fma x ah al Fx Hx E.
pose proof (ac_tpe fma x Fx Hx) as T.
destruct (two_prod_err_correct fma x x Fx Fx T) as (Fp & Ep & _ & Fe & Ee).
destruct one_R as [F1 E1].
assert (B26 : bpow radix2 26 = 67108864) by reflexivity.
assert (B52 : bpow radix2 52 = 4503599627370496) by reflexivity.
assert (B53 : bpow radix2 53 = 9007199254740992) by reflexivity.
assert (Bm52 : bpow radix2 (-52) = / 4503599627370496) by reflexivity.
assert (Bm53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
assert (Bm1022 : bpow radix2 (-1022) <= / 4503599627370496)
  by (rewrite <- Bm52; apply bpow_le; lia).
rewrite B26 in Hx.
set (X := B2R x) in *.
(* [x >= succ 1 = 1 + 2^-52] *)
assert (HX1 : 1 + / 4503599627370496 <= X).
{ assert (S : succ radix2 fexp64 1 <= X).
  { apply succ_le_lt; [typeclasses eauto | exact (format_bpow64 0 ltac:(lia)) |
      apply generic_format_B2R | lra]. }
  rewrite succ_eq_pos in S by lra.
  replace (ulp radix2 fexp64 1) with (/ 4503599627370496) in S; [lra |].
  change 1 with (bpow radix2 0). rewrite ulp_bpow. reflexivity. }
assert (HX2 : 1 + 2 * / 4503599627370496 <= X * X) by nra.
set (ph := mul x x) in *.
set (pl := Generic.two_prod_err fma x x ph) in *.
assert (Gp : format (B2R ph)) by apply generic_format_B2R.
assert (P1 : 1 <= B2R ph).
{ rewrite Ep. apply rn_ge; [exact (format_bpow64 0 ltac:(lia)) | nra]. }
assert (P2 : B2R ph <= 4503599627370496).
{ rewrite Ep, <- B52. apply rn_le; [exact (format_bpow64 52 ltac:(lia)) | rewrite B52; nra]. }
pose proof (rn_rel (X * X) ltac:(rewrite Rabs_pos_eq by nra; nra)) as Hr.
rewrite <- Ep, Rabs_pos_eq with (x := B2R ph), Bm53 in Hr by lra.
apply Rabs_le_inv in Hr.
(* [ph - 1] is exact *)
assert (Gd : format (B2R ph - 1)) by (apply ac_sub_one; [exact Gp | lra]).
destruct (sub_below_max ph DyadicExp.one Fp F1) as (Fd & Ed & _).
{ rewrite E1, Rabs_pos_eq by lra. cbn [bpow radix_val radix2 Z.opp]. lra. }
rewrite E1, round_generic in Ed by (try typeclasses eauto; exact Gd).
destruct (ac_fts (sub ph DyadicExp.one) pl ah al Fd Fe) as (Fah & Fal & Eah & Eal); try assumption.
{ rewrite Ed, Ee, (Rabs_pos_eq (B2R ph - 1)) by lra. apply Rabs_le. lra. }
{ rewrite Ed, Ee. rewrite Rabs_pos_eq by nra. cbn [bpow radix_val radix2 Z.opp]. nra. }
rewrite Ed, Ee in Eah, Eal.
replace (B2R ph - 1 + (X * X - B2R ph)) with (X * X - 1) in Eah, Eal by ring.
assert (A1 : / 4503599627370496 <= B2R ah).
{ rewrite Eah, <- Bm52. apply rn_ge; [exact (format_bpow64 (-52) ltac:(lia)) | rewrite Bm52; lra]. }
assert (A2 : B2R ah <= 4503599627370496).
{ rewrite Eah, <- B52. apply rn_le; [exact (format_bpow64 52 ltac:(lia)) | rewrite B52; nra]. }
pose proof (rn_rel (X * X - 1) ltac:(rewrite Rabs_pos_eq by nra; nra)) as Ha.
rewrite <- Eah, Rabs_pos_eq with (x := B2R ah) in Ha by lra.
rewrite Bm52, B52, Bm53.
repeat split; try assumption; try lra.
replace (B2R al) with (- (B2R ah - (X * X - 1))) by lra.
rewrite Rabs_Ropp, <- Bm53. exact Ha.
Qed.

(** ** Below [2^26]: [d = x - 1] *)

(** A [f64] above [1] is at least [succ 1 = 1 + 2^-52]. *)
Local Lemma ac_x1 :
  forall x : f64, is_finite x = true -> 1 < B2R x -> 1 + / 4503599627370496 <= B2R x.
Proof.
intros x Fx Hx.
assert (S : succ radix2 fexp64 1 <= B2R x).
{ apply succ_le_lt; [typeclasses eauto | exact (format_bpow64 0 ltac:(lia)) |
    apply generic_format_B2R | lra]. }
rewrite succ_eq_pos in S by lra.
replace (ulp radix2 fexp64 1) with (/ 4503599627370496) in S; [lra |].
change 1 with (bpow radix2 0). rewrite ulp_bpow. reflexivity.
Qed.

(** [x - 1] is exact ([ac_sub_one]). *)
Local Lemma ac_d :
  forall x, is_finite x = true -> 1 < B2R x < bpow radix2 26 ->
  is_finite (sub x DyadicExp.one) = true /\ B2R (sub x DyadicExp.one) = B2R x - 1.
Proof.
intros x Fx Hx.
destruct one_R as [F1 E1].
assert (B26 : bpow radix2 26 = 67108864) by reflexivity.
assert (B53 : bpow radix2 53 = 9007199254740992) by reflexivity.
assert (G : format (B2R x - 1)).
{ apply ac_sub_one; [apply generic_format_B2R | rewrite B53; lra]. }
destruct (sub_below_max x DyadicExp.one Fx F1) as (Fd & Ed & _).
{ rewrite E1, Rabs_pos_eq by lra. cbn [bpow radix_val radix2 Z.opp]. lra. }
rewrite E1, round_generic in Ed by (try typeclasses eauto; exact G).
split; assumption.
Qed.

(** ** Below [x = 1 + 2^-22]: [ln(1 + u)] with [u = d + r] *)

(** [a <= b] from [a^2 <= b^2] and [0 <= b]. *)
Local Lemma le_of_sq : forall a b, 0 <= b -> a * a <= b * b -> a <= b.
Proof. intros a b Hb H. destruct (Rle_dec a 0) as [Ha | Ha]; [lra | nra]. Qed.

(** [r^2 = d(2 + d)] gives [2d <= r] and [2^-26 <= r <= 0.71 2^-10], so
    [d <= rh] and both FastTwoSums are exact; [u = (x - 1) + r] is then
    within [2^-99 u] of [uh + ul], and [ln(1 + u) >= u/2]. *)
Local Lemma ac_small :
  forall x rh rl s w uh ul,
  is_finite x = true -> 1 < B2R x -> B2R x - 1 < bpow radix2 (-22) ->
  is_finite rh = true -> is_finite rl = true -> B2R rh = RN (B2R rh + B2R rl) ->
  Rabs (B2R rh + B2R rl - sqrt (B2R x * B2R x - 1)) <=
    bpow radix2 (-100) * sqrt (B2R x * B2R x - 1) ->
  Fast.fast_two_sum rh (sub x DyadicExp.one) = (s, w) ->
  Fast.fast_two_sum s (add w rl) = (uh, ul) ->
  is_finite uh = true /\ is_finite ul = true /\
  bpow radix2 (-30) <= B2R uh <= bpow radix2 (-10) /\
  Rabs (B2R ul) <= bpow radix2 (-53) * B2R uh /\
  Rabs (Racosh (B2R x) - ln (1 + (B2R uh + B2R ul))) <=
    bpow radix2 (-72) * Rabs (Racosh (B2R x)).
Proof.
intros x rh rl s w uh ul Fx Hx Hd Frh Frl Erh Hr Es Eu.
pose proof (ac_x1 x Fx Hx) as HX1.
assert (Bm1022 : bpow radix2 (-1022) <= / 1267650600228229401496703205376)
  by (apply (Rle_trans _ (bpow radix2 (-100))); [apply bpow_le; lia | right; reflexivity]).
destruct (ac_d x Fx) as (Fd & Ed).
{ split; [lra |]. apply (Rlt_trans _ (bpow radix2 (-22) + 1)); [lra |].
  cbn [bpow radix_val radix2 Z.opp]. lra. }
cbn [bpow radix_val radix2 Z.opp] in Hd, Hr |- *.
set (X := B2R x) in *.
set (r := sqrt (X * X - 1)) in *.
assert (HR2 : r * r = (X - 1) * (2 + (X - 1))) by (unfold r; rewrite sqrt_sqrt by nra; ring).
assert (HR0 : 0 <= r) by apply sqrt_pos.
set (D := X - 1) in *.
assert (ED : D = X - 1) by reflexivity.
clearbody D.
assert (Hr1 : 2 * D <= r) by (apply le_of_sq; [exact HR0 | nra]).
assert (Hr2 : / 67108864 <= r) by (apply le_of_sq; [exact HR0 | nra]).
assert (Hr3 : r <= 71 / 100 * / 1024) by (apply le_of_sq; [lra | nra]).
(* [rh] and [rl] *)
set (Rt := B2R rh + B2R rl) in *.
assert (ERt : Rt = B2R rh + B2R rl) by reflexivity.
apply Rabs_le_inv in Hr.
pose proof (rn_rel Rt ltac:(rewrite Rabs_pos_eq by lra; lra)) as Hrh.
rewrite <- Erh in Hrh.
assert (Hrh0 : 0 <= B2R rh).
{ rewrite Erh. apply rn_ge; [apply generic_format_0 | lra]. }
rewrite (Rabs_pos_eq (B2R rh)) in Hrh by exact Hrh0.
cbn [bpow radix_val radix2 Z.opp] in Hrh.
apply Rabs_le_inv in Hrh.
assert (HDrh : D <= B2R rh) by lra.
(* the first FastTwoSum *)
destruct (ac_fts rh (sub x DyadicExp.one) s w Frh Fd) as (Fs & Fw & Es' & Esw); try assumption.
{ rewrite Ed. rewrite !Rabs_pos_eq by lra. lra. }
{ rewrite Ed. rewrite Rabs_pos_eq by lra.
  cbn [bpow radix_val radix2 Z.opp]. lra. }
rewrite Ed in Es', Esw.
pose proof (rn_rel (B2R rh + D) ltac:(rewrite Rabs_pos_eq by lra; lra)) as Hs.
rewrite <- Es' in Hs.
assert (Hs0 : 0 <= B2R s).
{ rewrite Es'. apply rn_ge; [apply generic_format_0 | lra]. }
rewrite (Rabs_pos_eq (B2R s)) in Hs by exact Hs0.
cbn [bpow radix_val radix2 Z.opp] in Hs.
apply Rabs_le_inv in Hs.
(* [w + rl] and the second FastTwoSum *)
assert (Hz : Rabs (B2R w + B2R rl) <= / 2251799813685248 * B2R s).
{ apply Rabs_le. split; lra. }
destruct (add_below_max w rl Fw Frl) as (Fz & Ez & _).
{ apply (Rle_trans _ _ _ Hz). cbn [bpow radix_val radix2 Z.opp]. lra. }
pose proof (FastExpErr.rn_err (B2R w + B2R rl)) as Hzr.
rewrite <- Ez in Hzr.
cbn [bpow radix_val radix2 Z.opp] in Hzr.
apply Rabs_le_inv in Hzr.
assert (Hz' := Hz). apply Rabs_le_inv in Hz'.
destruct (ac_fts s (add w rl) uh ul Fs Fz) as (Fuh & Ful & Euh & Eul); try assumption.
{ rewrite (Rabs_pos_eq (B2R s)) by exact Hs0. apply Rabs_le. split; lra. }
{ apply Rabs_le. cbn [bpow radix_val radix2 Z.opp]. split; lra. }
(* [U = uh + ul] against [u = d + r] *)
set (U := B2R uh + B2R ul) in *.
assert (EU : U = B2R uh + B2R ul) by reflexivity.
set (u := D + r).
assert (Eu' : u = D + r) by reflexivity.
assert (HU : Rabs (U - u) <= / 633825300114114700748351602688 * u).
{ apply Rabs_le. split; lra. }
assert (Hu : / 67108864 <= u <= 72 / 100 * / 1024) by lra.
assert (HU' := HU). apply Rabs_le_inv in HU'.
rewrite <- Eul in Euh.
pose proof (rn_rel U ltac:(rewrite Rabs_pos_eq by lra; lra)) as Huh.
rewrite <- Euh in Huh.
assert (Huh0 : 0 <= B2R uh).
{ rewrite Euh. apply rn_ge; [apply generic_format_0 | lra]. }
rewrite (Rabs_pos_eq (B2R uh)) in Huh by exact Huh0.
cbn [bpow radix_val radix2 Z.opp] in Huh.
assert (Hul : B2R ul = - (B2R uh - U)) by lra.
apply Rabs_le_inv in Huh.
(* the logarithms *)
assert (EA : X + r = 1 + u) by lra.
unfold Racosh. fold X. fold r. rewrite EA.
pose proof (ln_half u ltac:(lra)) as Hl.
rewrite (Rabs_pos_eq (ln (1 + u))) by lra.
assert (Huu : 0 <= u * u) by nra.
pose proof (ac_ln_close (1 + u) (1 + U) (/ 633825300114114700748351602688 * u)
  ltac:(lra) ltac:(apply Rabs_le; split; lra) ltac:(lra)) as Hc.
repeat split; try assumption; try lra.
rewrite Hul, Rabs_Ropp. apply Rabs_le. lra.
Qed.

(** ** From [x = 1 + 2^-22] to [2^26]: [ln(x + r)] *)

(** [(x - r)(x + r) = 1] with [x + r <= 2^27] gives [x - r >= 2^-27], so
    [rh + rl < x], [rh <= x], and FastTwoSum is exact; [xh + RN(xl + rl)]
    is within [2^-98 (x + r)] of [x + r], and [x + r >= 1 + 2^-11] gives
    [acosh x >= 2^-12]. *)
Local Lemma ac_mid :
  forall x rh rl xh xl,
  is_finite x = true -> bpow radix2 (-22) <= B2R x - 1 -> B2R x < bpow radix2 26 ->
  is_finite rh = true -> is_finite rl = true -> B2R rh = RN (B2R rh + B2R rl) ->
  Rabs (B2R rh + B2R rl - sqrt (B2R x * B2R x - 1)) <=
    bpow radix2 (-100) * sqrt (B2R x * B2R x - 1) ->
  Fast.fast_two_sum x rh = (xh, xl) ->
  is_finite xh = true /\ is_finite (add xl rl) = true /\ 0 < B2R xh /\
  Rabs (B2R (add xl rl)) <= bpow radix2 (-51) * B2R xh /\
  B2R xh * bpow radix2 0 <= bpow radix2 1025 /\
  bpow radix2 (-20) <= Rabs (Racosh (B2R x)) /\
  Rabs (Racosh (B2R x) - (IZR 0 * ln 2 + ln (B2R xh + B2R (add xl rl)))) <=
    bpow radix2 (-80) * Rabs (Racosh (B2R x)).
Proof.
intros x rh rl xh xl Fx Hd Hx Frh Frl Erh Hr E.
assert (Bm1022 : bpow radix2 (-1022) <= / 1267650600228229401496703205376)
  by (apply (Rle_trans _ (bpow radix2 (-100))); [apply bpow_le; lia | right; reflexivity]).
assert (B1025 : 1 <= bpow radix2 1025) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
assert (Gx : format (B2R x)) by apply generic_format_B2R.
cbn [bpow radix_val radix2 Z.opp] in Hd, Hx, Hr |- *.
set (X := B2R x) in *.
set (r := sqrt (X * X - 1)) in *.
assert (HR2 : r * r = X * X - 1) by (unfold r; rewrite sqrt_sqrt by nra; ring).
assert (HR0 : 0 <= r) by apply sqrt_pos.
assert (Er : r = sqrt (X * X - 1)) by reflexivity.
clearbody r.
assert (Hr1 : / 2048 <= r) by (apply le_of_sq; [exact HR0 | nra]).
assert (Hr2 : r <= X) by (apply le_of_sq; [lra | lra]).
assert (Hxr : (X - r) * (X + r) = 1) by (replace ((X - r) * (X + r)) with (X * X - r * r) by ring; lra).
assert (Hxr1 : (X - r) * (X + r) <= (X - r) * 134217728)
  by (apply Rmult_le_compat_l; lra).
(* [rh] and [rl] *)
set (Rt := B2R rh + B2R rl) in *.
assert (ERt : Rt = B2R rh + B2R rl) by reflexivity.
apply Rabs_le_inv in Hr.
assert (Hrh0 : 0 <= B2R rh).
{ rewrite Erh. apply rn_ge; [apply generic_format_0 | lra]. }
assert (Hrh1 : B2R rh <= X).
{ rewrite Erh. apply rn_le; [exact Gx | lra]. }
pose proof (rn_rel Rt ltac:(rewrite Rabs_pos_eq by lra; lra)) as Hrh.
rewrite <- Erh in Hrh.
rewrite (Rabs_pos_eq (B2R rh)) in Hrh by exact Hrh0.
cbn [bpow radix_val radix2 Z.opp] in Hrh.
apply Rabs_le_inv in Hrh.
(* the FastTwoSum *)
destruct (ac_fts x rh xh xl Fx Frh) as (Fxh & Fxl & Exh & Exhl); try assumption.
{ fold X. rewrite !Rabs_pos_eq by lra. lra. }
{ fold X. rewrite Rabs_pos_eq by lra. cbn [bpow radix_val radix2 Z.opp]. lra. }
fold X in Exh, Exhl.
assert (Hxh0 : X <= B2R xh).
{ rewrite Exh. apply rn_ge; [exact Gx | lra]. }
pose proof (rn_rel (X + B2R rh) ltac:(rewrite Rabs_pos_eq by lra; lra)) as Hxh.
rewrite <- Exh in Hxh.
rewrite (Rabs_pos_eq (B2R xh)) in Hxh by lra.
cbn [bpow radix_val radix2 Z.opp] in Hxh.
apply Rabs_le_inv in Hxh.
(* [xl + rl] *)
assert (Hz : Rabs (B2R xl + B2R rl) <= / 4503599627370496 * B2R xh).
{ apply Rabs_le. split; lra. }
destruct (add_below_max xl rl Fxl Frl) as (Fz & Ez & _).
{ apply (Rle_trans _ _ _ Hz). cbn [bpow radix_val radix2 Z.opp]. lra. }
pose proof (FastExpErr.rn_err (B2R xl + B2R rl)) as Hzr.
rewrite <- Ez in Hzr.
cbn [bpow radix_val radix2 Z.opp] in Hzr.
apply Rabs_le_inv in Hzr.
assert (Hz' := Hz). apply Rabs_le_inv in Hz'.
(* [B = xh + RN(xl + rl)] against [A = x + r] *)
set (B := B2R xh + B2R (add xl rl)).
assert (EB : B = B2R xh + B2R (add xl rl)) by reflexivity.
assert (HAB : Rabs (B - (X + r)) <= / 316912650057057350374175801344 * (X + r)).
{ apply Rabs_le. split; lra. }
assert (HA : 1 + / 2048 <= X + r) by lra.
pose proof (ln_half (/ 2048) ltac:(lra)) as Hl0.
pose proof (ln_le_mono (1 + / 2048) (X + r) ltac:(lra) HA) as Hl1.
pose proof (ac_ln_close (X + r) B (/ 316912650057057350374175801344)
  ltac:(lra) HAB ltac:(lra)) as Hc.
unfold Racosh. fold X. rewrite <- Er.
rewrite (Rabs_pos_eq (ln (X + r))) by lra.
replace (IZR 0 * ln 2 + ln B) with (ln B) by ring.
rewrite Rmult_1_r.
repeat split; try assumption; try lra.
apply Rabs_le. lra.
Qed.

Theorem fast_acosh_correct :
  forall fma x h l k,
  is_finite x = true -> 1 <= B2R x ->
  DyadicLog.fast_acosh fma x = Some (h, l, k) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  / 2 < Rabs (B2R h) < 2 /\ (-1021 <= k <= 1022)%Z /\
  Rabs (Racosh (B2R x) * bpow radix2 (- k) - (B2R h + B2R l)) <= bpow radix2 (-68).
Proof.
intros fma x h l k Fx HX.
destruct one_R as [F1 E1].
destruct ahyp_large_R as [FL EL].
destruct acosh_small_R as [FS ES].
unfold DyadicLog.fast_acosh. cbv zeta.
destruct (Model.le x DyadicExp.one) eqn:Ele; [discriminate |].
pose proof (le_false x _ Fx F1 Ele) as HX1. rewrite E1 in HX1.
destruct (Model.ge x DyadicLog.ahyp_large) eqn:Ege.
- (* From [2^26] on: [ln 2 + ln(x + RN(-1/(4x)))]. *)
  pose proof (ge_true x _ Fx FL Ege) as HXL. rewrite EL in HXL.
  destruct (ac_large x (div DyadicLog.neg_quarter x) Fx HXL eq_refl)
    as (Fxl & Px & Hxl & Hm & Hy20 & Herr).
  intros E.
  exact (fast_ln_dd_correct fma x _ 1 _ h l k Fx Fxl Px Hxl ltac:(lia) Hm Hy20 Herr E).
- pose proof (ge_false x _ Fx FL Ege) as HXL. rewrite EL in HXL.
  destruct (Fast.fast_two_sum (sub (mul x x) DyadicExp.one)
    (Generic.two_prod_err fma x x (mul x x))) as [ah al] eqn:Ea. cbv beta iota.
  destruct (ac_sq fma x ah al Fx (conj HX1 HXL) Ea) as (Fah & Fal & Ea' & (Ha1 & Ha2) & Hal).
  destruct (Fast.dd_sqrt fma ah al) as [rh rl] eqn:Er. cbv beta iota.
  (* [ah] in [[2^-52, 2^52]] is inside [dd_sqrt]'s range, and [|al| <= 2^-53 ah]. *)
  destruct (dd_sqrt_correct fma ah al rh rl Fah Fal) as (Frh & Frl & Rrh & Hr).
  { split.
    - apply (Rle_trans _ (bpow radix2 (-52))); [apply bpow_le; lia | exact Ha1].
    - apply (Rle_trans _ (bpow radix2 52)); [exact Ha2 | apply bpow_le; lia]. }
  { apply (Rle_trans _ _ _ Hal). apply Rmult_le_compat_r.
    - pose proof (bpow_gt_0 radix2 (-52)). lra.
    - apply bpow_le; lia. }
  { exact Er. }
  rewrite Ea' in Hr.
  destruct (ac_d x Fx (conj HX1 HXL)) as (Fd & Ed).
  destruct (Model.lt (sub x DyadicExp.one) DyadicLog.acosh_small) eqn:Elt.
  + (* Below [x = 1 + 2^-22]: [ln(1 + u)], [u = (x - 1) + r]. *)
    pose proof (lt_true _ _ Fd FS Elt) as Hd. rewrite Ed, ES in Hd.
    destruct (Fast.fast_two_sum rh (sub x DyadicExp.one)) as [s w] eqn:Es. cbv beta iota.
    destruct (Fast.fast_two_sum s (add w rl)) as [uh ul] eqn:Eu.
    destruct (ac_small x rh rl s w uh ul Fx HX1 Hd Frh Frl Rrh Hr Es Eu)
      as (Fuh & Ful & Bu & Lu & Eu').
    intros E.
    exact (log1p_small_correct fma uh ul _ h l k Fuh Ful Bu Lu Eu' E).
  + (* Up to [2^26]: [ln(x + r)]. *)
    pose proof (lt_false _ _ Fd FS Elt) as Hd. rewrite Ed, ES in Hd.
    destruct (Fast.fast_two_sum x rh) as [xh xl] eqn:Ex.
    destruct (ac_mid x rh rl xh xl Fx Hd HXL Frh Frl Rrh Hr Ex)
      as (Fxh & Fxl & Pxh & Hxl & Hm & Hy20 & Herr).
    intros E.
    exact (fast_ln_dd_correct fma xh (add xl rl) 0 _ h l k Fxh Fxl Pxh Hxl ltac:(lia)
      Hm Hy20 Herr E).
Qed.

Theorem fast_acosh_fma :
  forall x,
  is_finite x = true -> 1 <= B2R x ->
  DyadicLog.fast_acosh true x = DyadicLog.fast_acosh false x.
Proof.
intros x Fx HX.
destruct one_R as [F1 E1].
destruct ahyp_large_R as [FL EL].
destruct acosh_small_R as [FS ES].
unfold DyadicLog.fast_acosh. cbv zeta.
destruct (Model.le x DyadicExp.one) eqn:Ele; [reflexivity |].
pose proof (le_false x _ Fx F1 Ele) as HX1. rewrite E1 in HX1.
destruct (Model.ge x DyadicLog.ahyp_large) eqn:Ege.
- pose proof (ge_true x _ Fx FL Ege) as HXL. rewrite EL in HXL.
  apply fast_ln_dd_fma; [exact Fx | pose proof (bpow_gt_0 radix2 26); lra].
- pose proof (ge_false x _ Fx FL Ege) as HXL. rewrite EL in HXL.
  (* [x^2] is exact either way, so its error is the same [f64]. *)
  rewrite (two_prod_err_fma_eq x x Fx Fx (ac_tpe true x Fx (conj HX1 HXL))
    (ac_tpe false x Fx (conj HX1 HXL))).
  destruct (Fast.fast_two_sum (sub (mul x x) DyadicExp.one)
    (Generic.two_prod_err false x x (mul x x))) as [ah al] eqn:Ea. cbv beta iota.
  destruct (ac_sq false x ah al Fx (conj HX1 HXL) Ea) as (Fah & Fal & Ea' & (Ha1 & Ha2) & Hal).
  assert (Hah : bpow radix2 (-900) <= B2R ah <= bpow radix2 900).
  { split.
    - apply (Rle_trans _ (bpow radix2 (-52))); [apply bpow_le; lia | exact Ha1].
    - apply (Rle_trans _ (bpow radix2 52)); [exact Ha2 | apply bpow_le; lia]. }
  assert (Hal' : Rabs (B2R al) <= bpow radix2 (-52) * B2R ah).
  { apply (Rle_trans _ _ _ Hal). apply Rmult_le_compat_r.
    - pose proof (bpow_gt_0 radix2 (-52)). lra.
    - apply bpow_le; lia. }
  rewrite (dd_sqrt_fma ah al Fah Fal Hah).
  destruct (Fast.dd_sqrt false ah al) as [rh rl] eqn:Er. cbv beta iota.
  destruct (dd_sqrt_correct false ah al rh rl Fah Fal Hah Hal' Er) as (Frh & Frl & Rrh & Hr).
  rewrite Ea' in Hr.
  destruct (ac_d x Fx (conj HX1 HXL)) as (Fd & Ed).
  destruct (Model.lt (sub x DyadicExp.one) DyadicLog.acosh_small) eqn:Elt.
  + pose proof (lt_true _ _ Fd FS Elt) as Hd. rewrite Ed, ES in Hd.
    destruct (Fast.fast_two_sum rh (sub x DyadicExp.one)) as [s w] eqn:Es. cbv beta iota.
    destruct (Fast.fast_two_sum s (add w rl)) as [uh ul] eqn:Eu.
    destruct (ac_small x rh rl s w uh ul Fx HX1 Hd Frh Frl Rrh Hr Es Eu)
      as (Fuh & Ful & Bu & Lu & _).
    apply log1p_small_fma; assumption.
  + pose proof (lt_false _ _ Fd FS Elt) as Hd. rewrite Ed, ES in Hd.
    destruct (Fast.fast_two_sum x rh) as [xh xl] eqn:Ex.
    destruct (ac_mid x rh rl xh xl Fx Hd HXL Frh Frl Rrh Hr Ex) as (Fxh & _ & Pxh & _).
    apply fast_ln_dd_fma; assumption.
Qed.
