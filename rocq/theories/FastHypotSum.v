(** * The sum of squares of the fast path of [hypot]

    For [x] in [1/2, 1) and [y] in [2^-78, x], [x^2 + y^2] in
    double-double as [DyadicRoot.hypot_dd] computes it (the squares and
    their errors by [Generic.two_prod_err], then two [Fast.fast_two_sum]s)
    is a pair [(ah, al)] with [ah] in [1/8, 4], [|al| <= 2^-52 ah] and
    [|ah + al - (x^2 + y^2)| <= 2^-102] ([hypot_sum_sq_correct]). The
    errors of the squares are the same with and without an FMA
    ([hypot_sum_sq_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Relative.
From Inari Require Import Model Encoding TwoSum TwoProduct FastExpErr.
From Inari Require MulRuTiny FastRound FastHypPos CancelLanes.

Open Scope R_scope.

Local Notation format := (generic_format radix2 fexp64).
Local Ltac num := cbn [bpow radix_val radix2 Z.opp].

(** ** Helpers *)

Local Lemma format_bpow64 : forall e, (-1074 <= e)%Z -> format (bpow radix2 e).
Proof. intros e He. apply generic_format_bpow. unfold FLT_exp. lia. Qed.

(** Dekker's FastTwoSum (T. J. Dekker, A floating-point technique for
    extending the available precision, 1971): [s = RN(a + b)] and
    [s + t = a + b] exactly, up to [MAX] (as in [FastAhypAsinh.v]). *)
Local Lemma fts :
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

(** The rounding to nearest of a normal [x] is within [2^-53] of [x]
    relatively to the result (as in [FastAhypAsinh.v]). *)
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

(** The square of [z] in [[2^-78, 1)] is finite and in [[2^-156, 1]], and
    TwoProduct is exact for it with and without an FMA: its exponent is in
    [[-156, 0]], and that of [z] is at most 0. *)
Local Lemma sq_exact :
  forall fma z, is_finite z = true -> bpow radix2 (-78) <= B2R z < 1 ->
  is_finite (mul z z) = true /\ B2R (mul z z) = RN (B2R z * B2R z) /\
  bpow radix2 (-156) <= B2R (mul z z) <= 1 /\
  Generic.two_prod_is_exact fma z z (mul z z) = true.
Proof.
intros fma z Fz Hz.
pose proof (bpow_gt_0 radix2 (-78)) as H0.
pose proof (bpow_gt_0 radix2 (-156)) as H1.
assert (Hlo : bpow radix2 (-156) <= B2R z * B2R z).
{ replace (bpow radix2 (-156)) with (bpow radix2 (-78) * bpow radix2 (-78))
    by (rewrite <- bpow_plus; reflexivity).
  apply Rmult_le_compat; lra. }
assert (Hhi : B2R z * B2R z <= 1)
  by (apply Rle_trans with (1 * 1); [apply Rmult_le_compat; lra | lra]).
assert (Hm : Rabs (B2R z * B2R z) <= MAX)
  by (apply small_le_max; rewrite Rabs_pos_eq; lra).
destruct (mul_below_max z z Fz Fz Hm) as (Fp & Ep & _).
assert (Bp : bpow radix2 (-156) <= B2R (mul z z) <= 1).
{ rewrite Ep. split.
  - apply round_ge_generic; [typeclasses eauto .. | apply format_bpow64; lia | exact Hlo].
  - apply round_le_generic; [typeclasses eauto .. | apply (format_bpow64 0); lia | exact Hhi]. }
assert (Elo : (-156 <= Generic.exponent (mul z z))%Z).
{ apply MulRuTiny.exponent_ge; [exact Fp|]. rewrite Rabs_pos_eq; lra. }
assert (Ehi : (Generic.exponent (mul z z) < 1)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fp | lia |].
  rewrite Rabs_pos_eq by lra. change (bpow radix2 1) with 2. lra. }
assert (Ez : (Generic.exponent z < 1)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fz | lia |].
  rewrite Rabs_pos_eq by lra. change (bpow radix2 1) with 2. lra. }
split; [exact Fp|]. split; [exact Ep|]. split; [exact Bp|].
unfold Generic.two_prod_is_exact. cbv zeta.
destruct fma; repeat (apply andb_true_intro; split); apply Z.leb_le; lia.
Qed.

(** ** The theorems *)

Theorem hypot_sum_sq_correct :
  forall fma x y r2 e2 ah al,
  is_finite x = true -> is_finite y = true ->
  / 2 <= B2R x < 1 -> bpow radix2 (-78) <= B2R y <= B2R x ->
  Fast.fast_two_sum (mul x x) (mul y y) = (r2, e2) ->
  Fast.fast_two_sum r2 (add e2 (add (Generic.two_prod_err fma x x (mul x x))
                                    (Generic.two_prod_err fma y y (mul y y)))) = (ah, al) ->
  is_finite ah = true /\ is_finite al = true /\
  / 8 <= B2R ah <= 4 /\ Rabs (B2R al) <= bpow radix2 (-52) * B2R ah /\
  Rabs (B2R ah + B2R al - (B2R x * B2R x + B2R y * B2R y)) <= bpow radix2 (-102).
Proof.
intros fma x y r2 e2 ah al Fx Fy Hx Hy E1 E2.
pose proof (bpow_gt_0 radix2 (-78)) as H78.
pose proof (bpow_gt_0 radix2 (-156)) as H156.
assert (Hx' : bpow radix2 (-78) <= B2R x < 1) by lra.
assert (Hy' : bpow radix2 (-78) <= B2R y < 1) by lra.
(* The constants, with the powers of 2 as atoms for [lra] below. *)
assert (HM :
  bpow radix2 (-53) + bpow radix2 (-53) = bpow radix2 (-52) /\
  bpow radix2 (-52) + bpow radix2 (-52) + bpow radix2 (-105) <= bpow radix2 (-50) /\
  bpow radix2 (-50) + bpow radix2 (-103) + bpow radix2 (-52) + bpow radix2 (-3)
    <= bpow radix2 (-2) /\
  bpow radix2 (-50) + bpow radix2 (-103) + bpow radix2 (-52) + 2 <= bpow radix2 2 /\
  bpow radix2 (-103) + bpow radix2 (-105) <= bpow radix2 (-102) /\
  bpow radix2 (-53) <= bpow radix2 (-52) /\
  bpow radix2 (-2) = / 4 /\ bpow radix2 (-3) = / 8 /\ bpow radix2 2 = 4 /\
  bpow radix2 (-1022) <= bpow radix2 (-3) /\ bpow radix2 (-50) <= 1 /\
  0 < bpow radix2 (-105) /\ 0 < bpow radix2 (-103) /\ 0 < bpow radix2 (-53) /\
  0 < bpow radix2 (-52) /\ 0 < bpow radix2 (-50) /\ 0 < bpow radix2 (-3))
  by (num; repeat split; lra).
destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & P105 & P103 & P53
  & P52 & P50 & P3).
(* The squares [px = RN(x^2)] in [[1/4, 1]] and [py = RN(y^2)] in
   [[2^-156, px]], and their exact errors [dx] and [dy]. *)
destruct (sq_exact fma x Fx Hx') as (Fpx & Epx & Bpx & Xx).
destruct (sq_exact fma y Fy Hy') as (Fpy & Epy & Bpy & Xy).
destruct (two_prod_err_correct fma x x Fx Fx Xx) as (_ & _ & _ & Fdx & Edx).
destruct (two_prod_err_correct fma y y Fy Fy Xy) as (_ & _ & _ & Fdy & Edy).
set (px := mul x x) in *. set (py := mul y y) in *.
set (dx := Generic.two_prod_err fma x x px) in *.
set (dy := Generic.two_prod_err fma y y py) in *.
assert (Hxx : / 4 <= B2R x * B2R x <= 1).
{ split; [apply Rle_trans with (/ 2 * / 2); [lra|] | apply Rle_trans with (1 * 1); [|lra]];
    apply Rmult_le_compat; lra. }
assert (Hyy : 0 <= B2R y * B2R y <= B2R x * B2R x).
{ split; [apply Rmult_le_pos; lra | apply Rmult_le_compat; lra]. }
assert (Px : bpow radix2 (-2) <= B2R px).
{ rewrite Epx.
  apply round_ge_generic; [typeclasses eauto .. | apply format_bpow64; lia | lra]. }
assert (Pyx : B2R py <= B2R px).
{ rewrite Epx, Epy. apply round_le; [typeclasses eauto .. | lra]. }
assert (Rdx : Rabs (B2R dx) <= bpow radix2 (-53)).
{ rewrite Edx, Epx, Rabs_minus_sym. apply (FastHypPos.rn_err _ (-53)); [lia|].
  rewrite Rabs_pos_eq by lra. exact (proj2 Hxx). }
assert (Rdy : Rabs (B2R dy) <= bpow radix2 (-53)).
{ rewrite Edy, Epy, Rabs_minus_sym. apply (FastHypPos.rn_err _ (-53)); [lia|].
  rewrite Rabs_pos_eq by lra. change (bpow radix2 (-53 + 53)) with 1. lra. }
(* [r2 + e2 = px + py] exactly, [|e2| <= 2^-52]. *)
assert (S1a : Rabs (B2R py) <= Rabs (B2R px)) by (rewrite 2!Rabs_pos_eq; lra).
assert (S1b : Rabs (B2R px + B2R py) <= MAX)
  by (apply small_le_max; rewrite Rabs_pos_eq; lra).
destruct (fts px py r2 e2 Fpx Fpy S1a S1b E1) as (Fr2 & Fe2 & Er2 & Se2).
assert (Re2 : Rabs (B2R e2) <= bpow radix2 (-52)).
{ replace (B2R e2) with (- (RN (B2R px + B2R py) - (B2R px + B2R py))) by lra.
  rewrite Rabs_Ropp. apply (FastHypPos.rn_err _ (-52)); [lia|].
  rewrite Rabs_pos_eq by lra. change (bpow radix2 (-52 + 53)) with 2. lra. }
pose proof (Rabs_le_inv _ _ Re2) as Re2'.
(* [t1 = RN(dx + dy)], within [2^-105] of [dx + dy]. *)
assert (T1a : Rabs (B2R dx + B2R dy) <= bpow radix2 (-52)).
{ apply Rle_trans with (Rabs (B2R dx) + Rabs (B2R dy)); [apply Rabs_triang | lra]. }
assert (T1b : Rabs (B2R dx + B2R dy) <= 16) by lra.
destruct (add_e dx dy Fdx Fdy T1b) as (Ft1 & Et1 & _).
set (t1 := add dx dy) in *.
assert (Rt1 : Rabs (B2R t1 - (B2R dx + B2R dy)) <= bpow radix2 (-105)).
{ rewrite Et1. apply (FastHypPos.rn_err _ (-105)); [lia | exact T1a]. }
(* [dr2 = RN(e2 + t1)], within [2^-103] of [e2 + t1]. *)
assert (D1a : Rabs (B2R e2 + B2R t1) <= bpow radix2 (-50)).
{ assert (Rabs (B2R t1) <= bpow radix2 (-52) + bpow radix2 (-105)).
  { replace (B2R t1) with ((B2R t1 - (B2R dx + B2R dy)) + (B2R dx + B2R dy)) by ring.
    apply Rle_trans with (Rabs (B2R t1 - (B2R dx + B2R dy)) + Rabs (B2R dx + B2R dy));
      [apply Rabs_triang | lra]. }
  apply Rle_trans with (Rabs (B2R e2) + Rabs (B2R t1)); [apply Rabs_triang | lra]. }
assert (D1b : Rabs (B2R e2 + B2R t1) <= 16) by lra.
destruct (add_e e2 t1 Fe2 Ft1 D1b) as (Fdr & Edr & _).
set (dr2 := add e2 t1) in *.
assert (Rdr : Rabs (B2R dr2 - (B2R e2 + B2R t1)) <= bpow radix2 (-103)).
{ rewrite Edr. apply (FastHypPos.rn_err _ (-103)); [lia | exact D1a]. }
assert (Hdr : Rabs (B2R dr2) <= bpow radix2 (-50) + bpow radix2 (-103)).
{ replace (B2R dr2) with ((B2R dr2 - (B2R e2 + B2R t1)) + (B2R e2 + B2R t1)) by ring.
  apply Rle_trans with (Rabs (B2R dr2 - (B2R e2 + B2R t1)) + Rabs (B2R e2 + B2R t1));
    [apply Rabs_triang | lra]. }
pose proof (Rabs_le_inv _ _ Hdr) as Hdr'.
(* [ah + al = r2 + dr2] exactly, with [r2 + dr2] in [[1/8, 4]]. *)
assert (Hr2 : bpow radix2 (-2) - bpow radix2 (-52) <= B2R r2 <= 2 + bpow radix2 (-52))
  by lra.
assert (S2a : Rabs (B2R dr2) <= Rabs (B2R r2))
  by (rewrite (Rabs_pos_eq (B2R r2)) by lra; lra).
assert (Hz : bpow radix2 (-3) <= B2R r2 + B2R dr2 <= bpow radix2 2) by lra.
assert (S2b : Rabs (B2R r2 + B2R dr2) <= MAX)
  by (apply small_le_max; rewrite Rabs_pos_eq; lra).
destruct (fts r2 dr2 ah al Fr2 Fdr S2a S2b E2) as (Fah & Fal & Eah & Sal).
assert (Bah : bpow radix2 (-3) <= B2R ah <= bpow radix2 2).
{ rewrite Eah. split.
  - apply round_ge_generic; [typeclasses eauto .. | apply format_bpow64; lia | lra].
  - apply round_le_generic; [typeclasses eauto .. | apply format_bpow64; lia | lra]. }
(* [al] is the error of rounding [r2 + dr2] to [ah]. *)
assert (Ral : Rabs (B2R al) <= bpow radix2 (-53) * B2R ah).
{ replace (B2R al) with (- (B2R ah - (B2R r2 + B2R dr2))) by lra.
  rewrite Rabs_Ropp.
  pose proof (rn_rel (B2R r2 + B2R dr2)) as R.
  rewrite <- Eah, (Rabs_pos_eq (B2R ah)) in R by lra.
  apply R. rewrite Rabs_pos_eq; lra. }
split; [exact Fah|]. split; [exact Fal|]. split; [lra|]. split.
{ apply Rle_trans with (1 := Ral). apply Rmult_le_compat_r; lra. }
(* [ah + al - (x^2 + y^2)] is the sum of the rounding errors of [dr2] and [t1]. *)
replace (B2R ah + B2R al - (B2R x * B2R x + B2R y * B2R y))
  with ((B2R dr2 - (B2R e2 + B2R t1)) + (B2R t1 - (B2R dx + B2R dy))) by lra.
apply Rle_trans with (Rabs (B2R dr2 - (B2R e2 + B2R t1)) + Rabs (B2R t1 - (B2R dx + B2R dy)));
  [apply Rabs_triang | lra].
Qed.

Theorem hypot_sum_sq_fma :
  forall x y,
  is_finite x = true -> is_finite y = true ->
  / 2 <= B2R x < 1 -> bpow radix2 (-78) <= B2R y <= B2R x ->
  Generic.two_prod_err true x x (mul x x) = Generic.two_prod_err false x x (mul x x) /\
  Generic.two_prod_err true y y (mul y y) = Generic.two_prod_err false y y (mul y y).
Proof.
intros x y Fx Fy Hx Hy.
pose proof (bpow_gt_0 radix2 (-78)) as H78.
assert (Hx' : bpow radix2 (-78) <= B2R x < 1) by lra.
assert (Hy' : bpow radix2 (-78) <= B2R y < 1) by lra.
destruct (sq_exact true x Fx Hx') as (_ & _ & _ & X1).
destruct (sq_exact false x Fx Hx') as (_ & _ & _ & X0).
destruct (sq_exact true y Fy Hy') as (_ & _ & _ & Y1).
destruct (sq_exact false y Fy Hy') as (_ & _ & _ & Y0).
split; apply FastRound.two_prod_err_fma_eq; assumption.
Qed.
