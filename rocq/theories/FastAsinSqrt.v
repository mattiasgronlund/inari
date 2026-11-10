(** * The square root of the fast paths of [asin] and [acos]

    [DyadicAtan.fast_sqrt1m t] of [Model.v] is [r = √((1 - t)(1 + t))] in
    double-double, from [t^2] exactly as a pair, [1 - t^2] by [Fast2Sum]
    and [dd_sqrt] of [FastDdSqrt.v]. For [t] in [[2^-27, 1)] it is within
    [2^-99] of [r], relative to it ([fast_sqrt1m_correct]), the same with
    and without an FMA ([sqrt1m_fma]), and in the range [dd_div] takes
    ([sqrt1m_facts]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Sterbenz.
From Inari Require Import Model Mpfr Elementary AtanReal AtanIdent TwoSum TwoProduct DyDriver
  NearF64 NearCells FastRound FastRoundErr FastDiv FastHypPos FastAtanTables FastAtanIdent
  FastAtanCore FastAtanAsm FastDdSqrt.
From Inari Require DyExp DyPown DyAtanTiny DyExpRules FastExpErr MulRuTiny FastLogNorm.
From Inari Require Import FastAsinReal FastAsinAngle.

Open Scope R_scope.

(** Powers of 2 as numerals, for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp].

(** [tp_exact] of [FastAtanPoly.v]: [x * y] is exact as a pair. *)
Local Lemma tp_exact :
  forall b x y, is_finite x = true -> is_finite y = true ->
  bpow radix2 (-900) <= Rabs (B2R x * B2R y) -> Rabs (B2R x) < 1 -> Rabs (B2R y) < 1 ->
  Generic.two_prod_is_exact b x y (mul x y) = true.
Proof.
intros b x y Fx Fy Hl Hx Hy.
assert (Hxy : Rabs (B2R x * B2R y) < 1).
{ rewrite Rabs_mult. pose proof (Rabs_pos (B2R x)). pose proof (Rabs_pos (B2R y)). nra. }
destruct (FastExpErr.mul_k x y (Rabs (B2R x * B2R y)) Fx Fy (Rle_refl _) ltac:(lra))
  as (Fp & _ & Bp).
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

(** A relative error [k] of [M] to [T] gives at most [k] for their
    square roots: [|√M - √T| (√M + √T) = |M - T| <= k T <= k √T (√M + √T)]. *)
Local Lemma sqrt_rel :
  forall M T k, 0 < T -> 0 <= M -> 0 <= k -> Rabs (M - T) <= k * T ->
  Rabs (sqrt M - sqrt T) <= k * sqrt T.
Proof.
intros M T k HT HM Hk H.
pose proof (sqrt_lt_R0 T HT) as Hb.
pose proof (sqrt_positivity M HM) as Ha.
assert (Ea : sqrt M * sqrt M = M) by (apply sqrt_sqrt; exact HM).
assert (Eb : sqrt T * sqrt T = T) by (apply sqrt_sqrt; lra).
set (a := sqrt M) in *. set (b := sqrt T) in *. clearbody a b. subst M T.
apply Rmult_le_reg_r with (a + b); [lra |].
rewrite <- (Rabs_pos_eq (a + b)) at 1 by lra.
rewrite <- Rabs_mult.
replace ((a - b) * (a + b)) with (a * a - b * b) by ring.
apply Rle_trans with (1 := H).
assert (0 <= k * b * a) by (apply Rmult_le_pos; [apply Rmult_le_pos |]; lra).
nra.
Qed.

(** [t^2] is exact as a pair for [t] in [[2^-27, 1)]. *)
Local Lemma sqrt1m_tp :
  forall b t, is_finite t = true -> bpow radix2 (-27) <= B2R t < 1 ->
  Generic.two_prod_is_exact b t t (mul t t) = true.
Proof.
intros b t Ft Ht.
assert (Huu0 : bpow radix2 (-54) <= B2R t * B2R t).
{ replace (bpow radix2 (-54)) with (bpow radix2 (-27) * bpow radix2 (-27))
    by (rewrite <- bpow_plus; reflexivity).
  pose proof (bpow_gt_0 radix2 (-27)). apply Rmult_le_compat; lra. }
pose proof (bpow_gt_0 radix2 (-27)).
apply tp_exact; [exact Ft | exact Ft | | (rewrite Rabs_pos_eq by lra; lra) ..].
rewrite Rabs_pos_eq by nra.
apply Rle_trans with (2 := Huu0). apply bpow_le. lia.
Qed.

(** [m = (mh, ml)], the double-double [1 - t^2] that [fast_sqrt1m] takes
    the square root of, and what [dd_sqrt] needs of it. *)
Local Lemma sqrt1m_m :
  forall fma t s s0 mh ml,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < 1 ->
  Fast.fast_two_sum DyadicExp.one (opp (mul t t)) = (s, s0) ->
  Fast.fast_two_sum s (sub s0 (Generic.two_prod_err fma t t (mul t t))) = (mh, ml) ->
  is_finite mh = true /\ is_finite ml = true /\ B2R mh = RN (B2R mh + B2R ml) /\
  bpow radix2 (-53) <= 1 - B2R t * B2R t /\
  Rabs (B2R mh + B2R ml - (1 - B2R t * B2R t)) <= bpow radix2 (-104) * (1 - B2R t * B2R t) /\
  bpow radix2 (-900) <= B2R mh <= bpow radix2 900 /\
  Rabs (B2R ml) <= bpow radix2 (-52) * B2R mh.
Proof.
intros fma t s s0 mh ml Ft Ht E1 E2.
pose proof (bpow_gt_0 radix2 (-27)) as P27.
pose proof (bpow_gt_0 radix2 (-53)) as P53.
pose proof (bpow_gt_0 radix2 (-54)) as P54.
pose proof (bpow_gt_0 radix2 (-900)) as P900.
assert (K52 : bpow radix2 (-52) = / 4503599627370496) by reflexivity.
assert (K53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
assert (K54 : bpow radix2 (-54) = / 18014398509481984) by reflexivity.
assert (K99 : bpow radix2 (-99) = / 633825300114114700748351602688) by reflexivity.
assert (K100 : bpow radix2 (-100) = / 1267650600228229401496703205376) by reflexivity.
assert (K104 : bpow radix2 (-104) = / 20282409603651670423947251286016) by reflexivity.
assert (K105 : bpow radix2 (-105) = / 40564819207303340847894502572032) by reflexivity.
(* [t <= pred 1 = 1 - 2^-53], so [2^-54 <= t^2 <= (1 - 2^-53)^2]. *)
pose proof (below_one t Ft (proj2 Ht)) as Hu1.
assert (Huu0 : bpow radix2 (-54) <= B2R t * B2R t).
{ replace (bpow radix2 (-54)) with (bpow radix2 (-27) * bpow radix2 (-27))
    by (rewrite <- bpow_plus; reflexivity).
  apply Rmult_le_compat; lra. }
assert (Huu1 : B2R t * B2R t <= (1 - bpow radix2 (-53)) * (1 - bpow radix2 (-53)))
  by (apply Rmult_le_compat; lra).
assert (HT53 : bpow radix2 (-53) <= 1 - B2R t * B2R t)
  by (revert Huu1; rewrite K53; intros; lra).
pose proof (sqrt1m_tp fma t Ft Ht) as Tp.
destruct (two_prod_err_correct fma t t Ft Ft Tp) as (Fp & Ep & _ & Fpe & Epe).
set (p := mul t t) in *. set (pe := Generic.two_prod_err fma t t p) in *.
destruct DyExp.one_B2R as (F1 & Eone).
assert (Fo : is_finite (opp p) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fp).
assert (Eo : B2R (opp p) = - B2R p) by (unfold opp; apply B2R_Bopp).
(* [p = RN(t^2)] is in [[0, 1 - 2^-53]], and [pe = t^2 - p] is at most [2^-53]. *)
assert (Fpo : generic_format radix2 (SpecFloat.fexp 53 1024) (1 - bpow radix2 (-53))).
{ rewrite <- DyExpRules.pred_one. apply generic_format_pred; first [exact format_one | typeclasses eauto]. }
assert (HP0 : 0 <= B2R p).
{ rewrite Ep. apply round_ge_generic; [typeclasses eauto .. | apply generic_format_0 | lra]. }
assert (HP1 : B2R p <= 1 - bpow radix2 (-53)).
{ rewrite Ep. apply round_le_generic; [typeclasses eauto .. | exact Fpo | lra]. }
assert (HE : Rabs (B2R pe) <= bpow radix2 (-53)).
{ rewrite Epe, Ep, Rabs_minus_sym. apply FastHypPos.rn_err; [lia |].
  change (bpow radix2 (-53 + 53)) with 1. rewrite Rabs_pos_eq by lra. lra. }
(* The first [Fast2Sum]: [s + s0 = 1 - p] exactly. *)
assert (H1a : Rabs (B2R (opp p)) <= Rabs (B2R DyadicExp.one)).
{ rewrite Eo, Eone, Rabs_Ropp, Rabs_R1, Rabs_pos_eq by lra. lra. }
assert (H1b : Rabs (B2R DyadicExp.one + B2R (opp p)) <= 2048).
{ rewrite Eo, Eone, Rabs_pos_eq by lra. lra. }
destruct (FastLogNorm.fts_exact DyadicExp.one (opp p) s s0 F1 Fo (or_introl H1a) H1b E1)
  as (Fs & Fs0 & Es & Ess0).
rewrite Eo, Eone in Es, Ess0.
(* The second [Fast2Sum]: [m = mh + ml] within [2^-104] of [1 - t^2]. *)
assert (HM : is_finite mh = true /\ is_finite ml = true /\
             B2R mh = RN (B2R mh + B2R ml) /\
             Rabs (B2R mh + B2R ml - (1 - B2R t * B2R t))
               <= bpow radix2 (-104) * (1 - B2R t * B2R t)).
{ destruct (Rle_or_lt (/ 2) (B2R p)) as [Hh | Hl].
  - (* [1 - p] is a float (Sterbenz): [s = 1 - p], [s0 = 0], [RN(-pe) = -pe]. *)
    assert (Fd : generic_format radix2 (SpecFloat.fexp 53 1024) (1 - B2R p)).
    { apply sterbenz; [typeclasses eauto .. | exact format_one | apply generic_format_B2R | lra]. }
    assert (Es' : B2R s = 1 - B2R p).
    { rewrite Es. replace (1 + - B2R p) with (1 - B2R p) by ring.
      apply round_generic; first [exact Fd | typeclasses eauto]. }
    assert (Es0 : B2R s0 = 0) by lra.
    assert (Hk : Rabs (B2R s0 - B2R pe) <= 1)
      by (rewrite Es0, Rminus_0_l, Rabs_Ropp; revert HE; rewrite K53; intros; lra).
    destruct (FastExpErr.sub_k s0 pe 1 Fs0 Fpe Hk ltac:(lra)) as (Fd' & Ed & _).
    assert (Ed' : B2R (sub s0 pe) = - B2R pe).
    { rewrite Ed, Es0, Rminus_0_l.
      apply round_generic;
        first [apply generic_format_opp; apply generic_format_B2R | typeclasses eauto]. }
    apply Rabs_le_inv in HE.
    assert (Hdle : Rabs (B2R (sub s0 pe)) <= Rabs (B2R s)).
    { rewrite Ed', Es', (Rabs_pos_eq (1 - B2R p)) by lra. apply Rabs_le. lra. }
    assert (Hsum : Rabs (B2R s + B2R (sub s0 pe)) <= 2048).
    { rewrite Ed', Es'. apply Rabs_le. lra. }
    destruct (FastLogNorm.fts_exact s (sub s0 pe) mh ml Fs Fd' (or_introl Hdle) Hsum E2)
      as (Fmh & Fml & Emh & Esum).
    split; [exact Fmh | split; [exact Fml | split]].
    + rewrite Esum. exact Emh.
    + rewrite Esum, Ed', Es', Epe.
      replace (1 - B2R p + - (B2R t * B2R t - B2R p) - (1 - B2R t * B2R t)) with 0 by ring.
      rewrite Rabs_R0. apply Rmult_le_pos; [apply bpow_ge_0 | lra].
  - (* [t^2 < 1/2], so [|pe| <= 2^-54], [s >= 1/2] and [|s0| <= 2^-53]. *)
    assert (Hq : B2R t * B2R t < / 2).
    { destruct (Rlt_or_le (B2R t * B2R t) (/ 2)) as [H | H]; [exact H |].
      exfalso.
      assert (/ 2 <= B2R p)
        by (rewrite Ep; apply round_ge_generic; [typeclasses eauto .. | exact format_half | exact H]).
      lra. }
    assert (HE2 : Rabs (B2R pe) <= bpow radix2 (-54)).
    { rewrite Epe, Ep, Rabs_minus_sym. apply FastHypPos.rn_err; [lia |].
      change (bpow radix2 (-54 + 53)) with (/ 2). rewrite Rabs_pos_eq by lra. lra. }
    assert (Hs1 : / 2 <= B2R s).
    { rewrite Es. apply round_ge_generic; [typeclasses eauto .. | exact format_half | lra]. }
    assert (Hs0 : Rabs (B2R s0) <= bpow radix2 (-53)).
    { replace (B2R s0) with (- (B2R s - (1 + - B2R p))) by lra. rewrite Rabs_Ropp, Es.
      apply FastHypPos.rn_err; [lia |]. change (bpow radix2 (-53 + 53)) with 1.
      rewrite Rabs_pos_eq by lra. lra. }
    assert (Hk : Rabs (B2R s0 - B2R pe) <= bpow radix2 (-52)).
    { apply Rabs_le_inv in HE2. apply Rabs_le_inv in Hs0. apply Rabs_le.
      rewrite K52. rewrite K53 in Hs0. rewrite K54 in HE2. lra. }
    destruct (FastExpErr.sub_k s0 pe (bpow radix2 (-52)) Fs0 Fpe Hk ltac:(rewrite K52; lra))
      as (Fd' & Ed & _).
    (* [RN(s0 - pe)] errs by at most [2^-105]. *)
    assert (Hd : Rabs (B2R (sub s0 pe) - (B2R s0 - B2R pe)) <= bpow radix2 (-105)).
    { rewrite Ed. apply FastHypPos.rn_err; [lia | exact Hk]. }
    apply Rabs_le_inv in Hd. apply Rabs_le_inv in Hk.
    rewrite K52 in Hk. rewrite K105 in Hd.
    assert (Hdle : Rabs (B2R (sub s0 pe)) <= Rabs (B2R s)).
    { rewrite (Rabs_pos_eq (B2R s)) by lra. apply Rabs_le. lra. }
    assert (Hsum : Rabs (B2R s + B2R (sub s0 pe)) <= 2048).
    { apply Rabs_le. split; [lra |].
      assert (B2R s <= 1) by (rewrite Es; apply round_le_generic;
                              [typeclasses eauto .. | exact format_one | lra]).
      lra. }
    destruct (FastLogNorm.fts_exact s (sub s0 pe) mh ml Fs Fd' (or_introl Hdle) Hsum E2)
      as (Fmh & Fml & Emh & Esum).
    split; [exact Fmh | split; [exact Fml | split]].
    + rewrite Esum. exact Emh.
    + (* [m - (1 - t^2) = RN(s0 - pe) - (s0 - pe)], and [1 - t^2 > 1/2]. *)
      rewrite Esum.
      replace (B2R s + B2R (sub s0 pe) - (1 - B2R t * B2R t))
        with (B2R (sub s0 pe) - (B2R s0 - B2R pe)) by (rewrite Epe; lra).
      rewrite K104. apply Rabs_le. lra. }
destruct HM as (Fmh & Fml & Emh & Hmt).
split; [exact Fmh | split; [exact Fml | split; [exact Emh | split; [exact HT53 |]]]].
split; [exact Hmt |].
set (M := B2R mh + B2R ml) in *.
set (T := 1 - B2R t * B2R t) in *.
assert (HT1 : T <= 1 - bpow radix2 (-54)) by (unfold T; lra).
apply Rabs_le_inv in Hmt. rewrite K104 in Hmt.
assert (HM0 : bpow radix2 (-54) <= M <= 1) by (rewrite K54; rewrite K53, K54 in *; lra).
(* [dd_sqrt]'s hypotheses on [m]. *)
assert (Hmh : bpow radix2 (-900) <= B2R mh <= bpow radix2 900).
{ split.
  - rewrite Emh. apply round_ge_generic;
      [typeclasses eauto .. | apply generic_format_FLT_bpow; [easy | lia] |].
    apply Rle_trans with (2 := proj1 HM0). apply bpow_le. lia.
  - pose proof (bpow_le radix2 0 900 ltac:(lia)) as B900.
    change (bpow radix2 0) with 1 in B900.
    apply Rle_trans with (2 := B900). rewrite Emh.
    apply round_le_generic; [typeclasses eauto .. | exact format_one | lra]. }
assert (Hml : Rabs (B2R ml) <= bpow radix2 (-52) * B2R mh).
{ pose proof (low_rel M mh Emh) as Hlow.
  rewrite (Rabs_pos_eq (B2R mh)) in Hlow by lra.
  replace (M - B2R mh) with (B2R ml) in Hlow by (unfold M; ring).
  apply Rle_trans with (bpow radix2 (-53) * B2R mh).
  - apply Hlow. apply Rle_trans with (2 := proj1 Hmh). apply bpow_le. lia.
  - apply Rmult_le_compat_r; [lra | apply bpow_le; lia]. }
split; [exact Hmh | exact Hml].
Qed.

(** [t^2 = p + pe] exactly ([two_prod_err_correct]). [1 - p] by
    [Fast2Sum] is [s + s0] exactly, and [m = (mh, ml)] is [s + RN(s0 -
    pe)] exactly by a second [Fast2Sum] ([FastLogNorm.fts_exact]). If [p
    >= 1/2], [1 - p] is a float (Sterbenz), so [s0 = 0], [RN(-pe) = -pe]
    and [m = 1 - t^2]; else [1 - t^2 > 1/2] and [RN(s0 - pe)] errs by at
    most [2^-105]. So [m] is within [2^-104] of [1 - t^2], relative to
    it, and [dd_sqrt] ([FastDdSqrt.dd_sqrt_correct]) adds [2^-100]. *)
Lemma fast_sqrt1m_correct :
  forall fma t,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < 1 ->
  let '(rh, rl) := DyadicAtan.fast_sqrt1m fma t in
  is_finite rh = true /\ is_finite rl = true /\ B2R rh = RN (B2R rh + B2R rl) /\
  Rabs (B2R rh + B2R rl - sqrt ((1 - B2R t) * (1 + B2R t)))
    <= bpow radix2 (-99) * sqrt ((1 - B2R t) * (1 + B2R t)).
Proof.
intros fma t Ft Ht.
assert (K53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
assert (K99 : bpow radix2 (-99) = / 633825300114114700748351602688) by reflexivity.
assert (K100 : bpow radix2 (-100) = / 1267650600228229401496703205376) by reflexivity.
assert (K104 : bpow radix2 (-104) = / 20282409603651670423947251286016) by reflexivity.
unfold DyadicAtan.fast_sqrt1m. cbv zeta.
set (p := mul t t). set (pe := Generic.two_prod_err fma t t p).
destruct (Fast.fast_two_sum DyadicExp.one (opp p)) as (s, s0) eqn:E1.
destruct (Fast.fast_two_sum s (sub s0 pe)) as (mh, ml) eqn:E2.
destruct (Fast.dd_sqrt fma mh ml) as (sh, sl) eqn:E3.
destruct (sqrt1m_m fma t s s0 mh ml Ft Ht E1 E2) as (Fmh & Fml & Emh & HT53 & Hmt & Hmh & Hml).
destruct (dd_sqrt_correct fma mh ml sh sl Fmh Fml Hmh Hml E3) as (Fsh & Fsl & Esh & Hsq).
split; [exact Fsh | split; [exact Fsl | split; [exact Esh |]]].
replace ((1 - B2R t) * (1 + B2R t)) with (1 - B2R t * B2R t) by ring.
set (M := B2R mh + B2R ml) in *.
set (T := 1 - B2R t * B2R t) in *.
apply Rabs_le_inv in Hmt. rewrite K104 in Hmt. rewrite K53 in HT53.
(* [|√m - √(1 - t^2)| <= 2^-104 √(1 - t^2)], so the total is at most
   [2^-100 (1 + 2^-104) + 2^-104 <= 2^-99], relative to [√(1 - t^2)]. *)
assert (Hr : Rabs (sqrt M - sqrt T) <= bpow radix2 (-104) * sqrt T).
{ apply sqrt_rel; [lra | lra | apply bpow_ge_0 |]. rewrite K104. apply Rabs_le. lra. }
pose proof (sqrt_pos T) as Hb. pose proof (sqrt_pos M) as Ha.
apply Rabs_le_inv in Hsq. apply Rabs_le_inv in Hr.
rewrite K100 in Hsq. rewrite K104 in Hr. rewrite K99.
apply Rabs_le. lra.
Qed.

(** [fast_sqrt1m] gives the same with and without an FMA. *)
Lemma sqrt1m_fma :
  forall t, is_finite t = true -> bpow radix2 (-27) <= B2R t < 1 ->
  DyadicAtan.fast_sqrt1m true t = DyadicAtan.fast_sqrt1m false t.
Proof.
intros t Ft Ht.
unfold DyadicAtan.fast_sqrt1m. cbv zeta.
(* [t^2] is exact as a pair, so its error is the same [f64] either way,
   and so are [m = (mh, ml)]; [dd_sqrt] of it is too. *)
rewrite (two_prod_err_fma_eq t t Ft Ft (sqrt1m_tp true t Ft Ht) (sqrt1m_tp false t Ft Ht)).
destruct (Fast.fast_two_sum DyadicExp.one (opp (mul t t))) as (s, s0) eqn:E1.
cbv beta iota.
destruct (Fast.fast_two_sum s (sub s0 (Generic.two_prod_err false t t (mul t t))))
  as (mh, ml) eqn:E2.
cbv beta iota.
destruct (sqrt1m_m false t s s0 mh ml Ft Ht E1 E2) as (Fmh & Fml & _ & _ & _ & Hmh & _).
apply dd_sqrt_fma; assumption.
Qed.

(** [r = rh + rl] as [dd_div] takes it, a numerator above the split and a
    denominator below it. *)
Lemma sqrt1m_facts :
  forall fma t rh rl,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < 1 ->
  DyadicAtan.fast_sqrt1m fma t = (rh, rl) ->
  is_finite rh = true /\ is_finite rl = true /\
  bpow radix2 (-28) <= B2R rh <= 2 /\ Rabs (B2R rl) <= bpow radix2 (-53) * B2R rh /\
  (B2R t <= 181 / 256 -> / 2 <= B2R rh) /\
  Rabs (B2R rh + B2R rl - sqrt ((1 - B2R t) * (1 + B2R t)))
    <= bpow radix2 (-99) * sqrt ((1 - B2R t) * (1 + B2R t)).
Proof.
intros fma t rh rl Ft Ht Es.
pose proof (fast_sqrt1m_correct fma t Ft Ht) as C.
rewrite Es in C. cbv beta iota in C.
destruct C as (Frh & Frl & Erh & Hr).
destruct (asin_q (B2R t) (conj (proj1 Ht) (below_one t Ft (proj2 Ht))))
  as ((Hr0 & Hr1) & Hr707 & _).
set (r := sqrt ((1 - B2R t) * (1 + B2R t))) in *.
assert (K27 : bpow radix2 (-27) = / 134217728) by reflexivity.
assert (K28 : bpow radix2 (-28) = / 268435456) by reflexivity.
assert (K99 : bpow radix2 (-99) = / 633825300114114700748351602688) by reflexivity.
pose proof (bpow_gt_0 radix2 (-28)) as P28.
(* [rh + rl] is within [2^-99] of [r] in [[2^-27, 1]], relative to it, and
   [rh = RN(rh + rl)] keeps the bounds that are floats. *)
assert (HR : r - / 633825300114114700748351602688 * r <= B2R rh + B2R rl <=
             r + / 633825300114114700748351602688 * r).
{ pose proof Hr as Hr'. apply Rabs_le_inv in Hr'. rewrite K99 in Hr'. lra. }
rewrite K27 in Hr0.
assert (Hlo : bpow radix2 (-28) <= B2R rh).
{ rewrite Erh. apply round_ge_generic;
    [typeclasses eauto .. | apply generic_format_FLT_bpow; [easy | lia] |].
  rewrite K28. lra. }
assert (Hhi : B2R rh <= bpow radix2 1).
{ rewrite Erh. apply round_le_generic;
    [typeclasses eauto .. | apply generic_format_FLT_bpow; [easy | lia] |].
  change (bpow radix2 1) with 2. lra. }
change (bpow radix2 1) with 2 in Hhi.
(* [rl = (rh + rl) - RN(rh + rl)] ([low_rel]). *)
assert (Hl : Rabs (B2R rl) <= bpow radix2 (-53) * B2R rh).
{ pose proof (low_rel (B2R rh + B2R rl) rh Erh) as Hlow.
  rewrite (Rabs_pos_eq (B2R rh)) in Hlow by lra.
  replace (B2R rh + B2R rl - B2R rh) with (B2R rl) in Hlow by ring.
  apply Hlow. apply Rle_trans with (2 := Hlo). apply bpow_le. lia. }
split; [exact Frh | split; [exact Frl | split; [split; [exact Hlo | exact Hhi] |]]].
split; [exact Hl | split; [| exact Hr]].
(* Below the split [r >= 0.707], so [rh + rl > 1/2]. *)
intro L. specialize (Hr707 L). rewrite Erh.
apply round_ge_generic; [typeclasses eauto .. | exact format_half | lra].
Qed.
