(** * The double-double steps of the Taylor polynomial of [sinh]

    [DyadicExp.fast_sinh_poly] of [Model.v] computes [t^3] as a
    double-double [t3h + t3l] ([sh_t3]), multiplies it by the double-double
    [bh + bl] of [FastSinhHorner.v] into [ch + cl] ([sh_c]), and adds [t]
    by two [fast_two_sum]s ([sh_final]). [FastHypPoly.v] assembles them. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error Relative.
From Inari Require Import Model Mpfr Encoding Elementary TwoSum TwoProduct DyDriver NearF64
  FastRound FastExpErr CancelLanes MulRuTiny.

Open Scope R_scope.

(** ** Helpers (as in [FastCoshPoly.v]) *)

(** Powers of 2 as numerals, for [lra]. *)
Local Ltac num := cbn [bpow radix_val radix2 Z.opp].

(** [add_k] and [mul_k] of [FastExpErr.v] for a named result [z], with the
    error as two inequalities for [lra]. *)
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

(** ** The steps *)

(** [t^2] as [uh] (and [uh + ul] exactly), and [t^3] as the double-double
    [t3h + t3l]. *)
Lemma sh_t3 :
  forall fma t,
  is_finite t = true -> bpow radix2 (-27) <= B2R t < / 4 ->
  let uh := mul t t in
  let ul := Generic.two_prod_err fma t t uh in
  let t3h := mul t uh in
  let t3l := add (Generic.two_prod_err fma t uh t3h) (mul t ul) in
  is_finite uh = true /\ is_finite t3h = true /\ is_finite t3l = true /\
  (forall b, Generic.two_prod_is_exact b t t uh = true /\
             Generic.two_prod_is_exact b t uh t3h = true) /\
  bpow radix2 (-55) <= B2R uh <= / 16 /\
  Rabs (B2R uh - B2R t * B2R t) <= bpow radix2 (-53) * (B2R t * B2R t) /\
  Rabs (B2R t3h - B2R t * (B2R t * B2R t)) <= bpow radix2 (-51) * (B2R t * (B2R t * B2R t)) /\
  Rabs (B2R t3l) <=
    bpow radix2 (-51) * (B2R t * (B2R t * B2R t)) + 3 * bpow radix2 (-1075) /\
  Rabs (B2R t3h + B2R t3l - B2R t * (B2R t * B2R t)) <=
    bpow radix2 (-103) * (B2R t * (B2R t * B2R t)) + 3 * bpow radix2 (-1075).
Proof.
intros fma t Ft Ht. cbv zeta.
pose proof (bpow_gt_0 radix2 (-27)) as P27.
pose proof (bpow_gt_0 radix2 (-54)) as P54.
pose proof (bpow_gt_0 radix2 (-55)) as P55.
pose proof (bpow_gt_0 radix2 (-82)) as P82.
pose proof (bpow_gt_0 radix2 (-1075)) as Peps.
(* [T^2] lies in [[2^-54, 1/16]] and [V = T^3] in [[2^-81, 1/64]]. *)
assert (HU : bpow radix2 (-54) <= B2R t * B2R t <= / 16).
{ split; [| nra].
  replace (bpow radix2 (-54)) with (bpow radix2 (-27) * bpow radix2 (-27))
    by (rewrite <- bpow_plus; reflexivity).
  apply Rmult_le_compat; lra. }
assert (HV : bpow radix2 (-81) <= B2R t * (B2R t * B2R t) <= / 64).
{ split.
  - replace (bpow radix2 (-81)) with (bpow radix2 (-27) * bpow radix2 (-54))
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; [lra | apply bpow_ge_0 | lra | lra].
  - apply Rle_trans with (/ 4 * / 16); [| lra].
    apply Rmult_le_compat; [lra | nra | lra | lra]. }
(* [uh] is [T^2] rounded and [ul = T^2 - uh] exactly (TwoProduct). *)
assert (Ex1 : forall b, Generic.two_prod_is_exact b t t (mul t t) = true).
{ intros b. apply tp_exact; [exact Ft | exact Ft | | |].
  - rewrite Rabs_pos_eq by lra. eapply Rle_trans; [| apply HU]. apply bpow_le. lia.
  - rewrite Rabs_pos_eq by lra. lra.
  - rewrite Rabs_pos_eq by lra. lra. }
destruct (two_prod_err_correct fma t t Ft Ft (Ex1 fma)) as (Fuh & Euh & _ & Ful & Eul).
set (uh := mul t t) in *.
set (ul := Generic.two_prod_err fma t t uh) in *.
(* In the normal range, [uh] is within [2^-53 T^2]; and [uh <= 1/16], a
   float, as rounding is monotone. *)
assert (Ruh : Rabs (B2R uh - B2R t * B2R t) <= bpow radix2 (-53) * (B2R t * B2R t)).
{ assert (H := rn_rel (B2R t * B2R t)).
  rewrite (Rabs_pos_eq (B2R t * B2R t)) in H by lra. rewrite Euh. apply H.
  eapply Rle_trans; [| apply HU]. apply bpow_le. lia. }
assert (Huh : bpow radix2 (-55) <= B2R uh <= / 16).
{ split.
  - apply Rabs_le_inv in Ruh. revert Ruh HU. num. intros. lra.
  - rewrite Euh. apply round_le_generic; [typeclasses eauto .. | | lra].
    change (/ 16) with (bpow radix2 (-4)). apply generic_format_bpow. unfold FLT_exp. lia. }
(* [t3h] is [T uh] rounded and [e1 = T uh - t3h] exactly (TwoProduct). *)
assert (HTuh : bpow radix2 (-82) <= B2R t * B2R uh).
{ replace (bpow radix2 (-82)) with (bpow radix2 (-27) * bpow radix2 (-55))
    by (rewrite <- bpow_plus; reflexivity).
  apply Rmult_le_compat; lra. }
assert (Ex2 : forall b, Generic.two_prod_is_exact b t uh (mul t uh) = true).
{ intros b. apply tp_exact; [exact Ft | exact Fuh | | |].
  - rewrite Rabs_pos_eq by lra. eapply Rle_trans; [| exact HTuh]. apply bpow_le. lia.
  - rewrite Rabs_pos_eq by lra. lra.
  - rewrite Rabs_pos_eq by lra. lra. }
destruct (two_prod_err_correct fma t uh Ft Fuh (Ex2 fma)) as (Ft3h & Et3h & _ & Fe1 & Ee1).
set (t3h := mul t uh) in *.
set (e1 := Generic.two_prod_err fma t uh t3h) in *.
assert (Rt3h : Rabs (B2R t3h - B2R t * B2R uh) <= bpow radix2 (-53) * (B2R t * B2R uh)).
{ assert (H := rn_rel (B2R t * B2R uh)).
  rewrite (Rabs_pos_eq (B2R t * B2R uh)) in H by lra. rewrite Et3h. apply H.
  eapply Rle_trans; [| exact HTuh]. apply bpow_le. lia. }
(* [T ul = T (T^2 - uh)] is at most [2^-53 V]; and [T uh = V - T ul]. *)
assert (HTul : Rabs (B2R t * B2R ul) <= bpow radix2 (-53) * (B2R t * (B2R t * B2R t))).
{ rewrite Eul, Rabs_mult, (Rabs_pos_eq (B2R t)) by lra. rewrite Rabs_minus_sym.
  replace (bpow radix2 (-53) * (B2R t * (B2R t * B2R t)))
    with (B2R t * (bpow radix2 (-53) * (B2R t * B2R t))) by ring.
  apply Rmult_le_compat_l; lra. }
assert (EV : B2R t * B2R uh = B2R t * (B2R t * B2R t) - B2R t * B2R ul)
  by (rewrite Eul; ring).
(* [r = RN(T ul)], within [2^-106 V + eps]. *)
destruct (mul_kz t ul (mul t ul) _ eq_refl Ft Ful HTul ltac:(revert HV; num; intros; lra))
  as (Fr & _ & Br).
set (r := mul t ul) in *.
(* [t3l = RN(e1 + r)], with [|e1 + r| <= 2^-51 V + eps]. *)
apply Rabs_le_inv in Rt3h, HTul.
assert (He1r : Rabs (B2R e1 + B2R r) <=
               bpow radix2 (-51) * (B2R t * (B2R t * B2R t)) + bpow radix2 (-1075)).
{ apply Rabs_le. revert Rt3h HTul Br Ee1 EV HV. num. intros. lra. }
destruct (add_kz e1 r (add e1 r) _ eq_refl Fe1 Fr He1r ltac:(revert HV; num; intros; lra))
  as (Ft3l & _ & Bt3l).
set (t3l := add e1 r) in *.
split; [exact Fuh |]. split; [exact Ft3h |]. split; [exact Ft3l |].
split; [intros b; split; [apply Ex1 | apply Ex2] |].
split; [exact Huh |]. split; [exact Ruh |].
split; [| split].
- (* [t3h - V = (t3h - T uh) - T ul]: [2^-53 (1 + 2^-53) V + 2^-53 V]. *)
  apply Rabs_le. revert Rt3h HTul EV HV. num. intros. lra.
- apply Rabs_le. revert Rt3h HTul Br Ee1 EV HV Bt3l. num. intros. lra.
- (* [t3h + t3l - V = (t3l - (e1 + r)) + (r - T ul)]:
     [2^-104 V + 2^-106 V] and [3 eps]. *)
  apply Rabs_le. revert Br Ee1 EV HV Bt3l. num. intros. lra.
Qed.

(** The product [ch + cl] of the double-doubles [t3h + t3l], near [v], and
    [bh + bl]. *)
Lemma sh_c :
  forall fma t3h t3l bh bl v,
  is_finite t3h = true -> is_finite t3l = true -> is_finite bh = true -> is_finite bl = true ->
  bpow radix2 (-81) <= v <= / 64 ->
  Rabs (B2R t3h - v) <= bpow radix2 (-51) * v ->
  Rabs (B2R t3l) <= bpow radix2 (-51) * v + 3 * bpow radix2 (-1075) ->
  / 8 <= B2R bh <= / 4 -> Rabs (B2R bl) <= bpow radix2 (-53) ->
  let ch := mul t3h bh in
  let cl := add (Generic.two_prod_err fma t3h bh ch) (add (mul t3h bl) (mul t3l bh)) in
  is_finite ch = true /\ is_finite cl = true /\
  (forall b, Generic.two_prod_is_exact b t3h bh ch = true) /\
  Rabs (B2R ch) <= v / 3 /\
  Rabs (B2R cl) <= bpow radix2 (-50) * v + 8 * bpow radix2 (-1075) /\
  Rabs (B2R ch + B2R cl - (B2R t3h + B2R t3l) * (B2R bh + B2R bl)) <=
    bpow radix2 (-101) * v + 8 * bpow radix2 (-1075).
Proof.
intros fma t3h t3l bh bl v Ft3h Ft3l Fbh Fbl Hv Ht3h Ht3l Hbh Hbl. cbv zeta.
pose proof (bpow_gt_0 radix2 (-81)) as P81.
pose proof (bpow_gt_0 radix2 (-82)) as P82.
pose proof (bpow_gt_0 radix2 (-85)) as P85.
pose proof (bpow_gt_0 radix2 (-1075)) as Peps.
apply Rabs_le_inv in Ht3h.
(* [t3h] is within [2^-51 v] of [v], so [t3h bh] lies in
   [[2^-85, v (1 + 2^-51) / 4]]. *)
assert (Hh0 : bpow radix2 (-82) <= B2R t3h) by (revert Ht3h Hv; num; intros; lra).
assert (Hp : bpow radix2 (-85) <= B2R t3h * B2R bh <= v * (1 + bpow radix2 (-51)) * / 4).
{ split.
  - apply Rle_trans with (bpow radix2 (-82) * / 8); [num; lra |].
    apply Rmult_le_compat; [apply bpow_ge_0 | lra | exact Hh0 | lra].
  - apply Rmult_le_compat; [lra | lra | revert Ht3h; num; intros; lra | lra]. }
(* [ch] is [t3h bh] rounded and [e = t3h bh - ch] exactly (TwoProduct). *)
assert (Ex : forall b, Generic.two_prod_is_exact b t3h bh (mul t3h bh) = true).
{ intros b. apply tp_exact; [exact Ft3h | exact Fbh | | |].
  - rewrite Rabs_pos_eq by lra. eapply Rle_trans; [| apply Hp]. apply bpow_le. lia.
  - rewrite Rabs_pos_eq by lra. revert Ht3h Hv. num. intros. lra.
  - rewrite Rabs_pos_eq by lra. lra. }
destruct (two_prod_err_correct fma t3h bh Ft3h Fbh (Ex fma)) as (Fch & _ & _ & Fe & Ee).
assert (Hpk : Rabs (B2R t3h * B2R bh) <= v * (1 + bpow radix2 (-51)) * / 4)
  by (rewrite Rabs_pos_eq by lra; apply Hp).
destruct (mul_kz t3h bh (mul t3h bh) _ eq_refl Ft3h Fbh Hpk ltac:(revert Hv; num; intros; lra))
  as (_ & _ & Bch).
set (ch := mul t3h bh) in *.
set (e := Generic.two_prod_err fma t3h bh ch) in *.
(* [r1 = RN(t3h bl)] and [r2 = RN(t3l bh)], each about [2^-53 v]. *)
assert (H1 : Rabs (B2R t3h * B2R bl) <= v * (1 + bpow radix2 (-51)) * bpow radix2 (-53)).
{ apply Rabs_mul_le; [rewrite Rabs_pos_eq by lra; lra | exact Hbl]. }
destruct (mul_kz t3h bl (mul t3h bl) _ eq_refl Ft3h Fbl H1 ltac:(revert Hv; num; intros; lra))
  as (Fr1 & _ & Br1).
set (r1 := mul t3h bl) in *.
assert (H2 : Rabs (B2R t3l * B2R bh) <=
             (bpow radix2 (-51) * v + 3 * bpow radix2 (-1075)) * / 4).
{ apply Rabs_mul_le; [exact Ht3l | rewrite Rabs_pos_eq by lra; lra]. }
destruct (mul_kz t3l bh (mul t3l bh) _ eq_refl Ft3l Fbh H2 ltac:(revert Hv; num; intros; lra))
  as (Fr2 & _ & Br2).
set (r2 := mul t3l bh) in *.
(* The dropped [t3l bl] is at most [(2^-51 v + 3 eps) 2^-53]. *)
assert (H3 : Rabs (B2R t3l * B2R bl) <=
             (bpow radix2 (-51) * v + 3 * bpow radix2 (-1075)) * bpow radix2 (-53))
  by (apply Rabs_mul_le; [exact Ht3l | exact Hbl]).
apply Rabs_le_inv in H1, H2, H3.
(* [p = RN(r1 + r2)], with [|r1 + r2| <= 2^-51 v + 4 eps]. *)
assert (Hp12 : Rabs (B2R r1 + B2R r2) <= bpow radix2 (-51) * v + 4 * bpow radix2 (-1075)).
{ apply Rabs_le. revert H1 H2 Br1 Br2 Hv. num. intros. lra. }
destruct (add_kz r1 r2 (add r1 r2) _ eq_refl Fr1 Fr2 Hp12 ltac:(revert Hv; num; intros; lra))
  as (Fp & _ & Bp).
set (p := add r1 r2) in *.
apply Rabs_le_inv in Hp12.
(* [cl = RN(e + p)], with [|e| <= 2^-55 v (1 + 2^-51) + eps]. *)
assert (Hep : Rabs (B2R e + B2R p) <= bpow radix2 (-50) * v + 8 * bpow radix2 (-1075)).
{ apply Rabs_le. revert Ee Bch Bp Hp12 Hv. num. intros. lra. }
destruct (add_kz e p (add e p) _ eq_refl Fe Fp Hep ltac:(revert Hv; num; intros; lra))
  as (Fcl & _ & Bcl).
set (cl := add e p) in *.
split; [exact Fch |]. split; [exact Fcl |]. split; [exact Ex |].
split; [| split].
- apply Rabs_le. revert Bch Hp Hv. num. intros. lra.
- apply Rabs_le. revert Ee Bch Bp Hp12 Bcl Hv. num. intros. lra.
- (* [ch + cl - (t3h + t3l) (bh + bl)] is the errors of [cl], [p], [r1]
     and [r2] ([e] is exact), minus the dropped [t3l bl]: about
     [(2^-103 + 2^-104 + 2^-106 + 2^-106 + 2^-104) v + 4 eps]. *)
  replace ((B2R t3h + B2R t3l) * (B2R bh + B2R bl))
    with (B2R t3h * B2R bh + B2R t3h * B2R bl + B2R t3l * B2R bh + B2R t3l * B2R bl)
    by ring.
  apply Rabs_le. revert Ee Bcl Bp Br1 Br2 H1 H3 Hv. num. intros. lra.
Qed.

(** [t + (ch + cl)] as the double-double [rh + rl], with [rh] the rounding
    of [rh + rl] to nearest. *)
Lemma sh_final :
  forall t ch cl,
  is_finite t = true -> is_finite ch = true -> is_finite cl = true ->
  bpow radix2 (-27) <= B2R t < / 4 ->
  Rabs (B2R ch) <= B2R t / 16 -> Rabs (B2R cl) <= bpow radix2 (-50) * B2R t ->
  let '(sh, s0) := Fast.fast_two_sum t ch in
  let '(rh, rl) := Fast.fast_two_sum sh (add s0 cl) in
  is_finite rh = true /\ is_finite rl = true /\ B2R rh = RN (B2R rh + B2R rl) /\
  Rabs (B2R rh + B2R rl - (B2R t + B2R ch + B2R cl)) <= bpow radix2 (-101) * B2R t.
Proof.
intros t ch cl Ft Fch Fcl Ht Hch Hcl.
unfold Fast.fast_two_sum. cbv beta iota zeta.
pose proof (bpow_gt_0 radix2 (-27)) as P27.
apply Rabs_le_inv in Hch, Hcl.
(* [sh = RN(t + ch)], and [s0 = t + ch - sh] exactly (Fast2Sum). *)
assert (Hs : Rabs (B2R t + B2R ch) <= 2 * B2R t) by (apply Rabs_le; lra).
destruct (add_kz t ch (add t ch) _ eq_refl Ft Fch Hs ltac:(lra)) as (Fsh & Esh & Bsh).
assert (Hle : Rabs (B2R ch) <= Rabs (B2R t)).
{ rewrite (Rabs_pos_eq (B2R t)) by lra. apply Rabs_le. lra. }
destruct (CancelLanes.fast_two_sum t ch (add t ch) Ft Fch Hle Fsh Esh) as (Fs0 & Es0).
set (sh := add t ch) in *.
set (s0 := add ch (sub t sh)) in *.
(* [w = RN(s0 + cl)], with [|s0 + cl| <= (2^-52 + 2^-50) T + eps <= 2^-49 T]. *)
assert (Hw : Rabs (B2R s0 + B2R cl) <= bpow radix2 (-49) * B2R t).
{ apply Rabs_le. revert Bsh Hcl P27 Ht. rewrite Es0. num. intros. lra. }
destruct (add_kz s0 cl (add s0 cl) _ eq_refl Fs0 Fcl Hw ltac:(num; lra)) as (Fw & Ew & Bw).
set (w := add s0 cl) in *.
apply Rabs_le_inv in Hw.
(* [rh = RN(sh + w)], and [rl = sh + w - rh] exactly (Fast2Sum). *)
assert (Hr : Rabs (B2R sh + B2R w) <= 2 * B2R t).
{ apply Rabs_le. revert Bsh Bw Hw Hcl P27 Ht. num. intros. lra. }
destruct (add_kz sh w (add sh w) _ eq_refl Fsh Fw Hr ltac:(lra)) as (Frh & Erh & Brh).
assert (Hle2 : Rabs (B2R w) <= Rabs (B2R sh)).
{ revert Bsh Bw Hw Hch P27 Ht. num. intros.
  rewrite (Rabs_pos_eq (B2R sh)) by lra. apply Rabs_le. lra. }
destruct (CancelLanes.fast_two_sum sh w (add sh w) Fsh Fw Hle2 Frh Erh) as (Frl & Erl).
set (rh := add sh w) in *.
set (rl := add w (sub sh rh)) in *.
assert (Hsum : B2R rh + B2R rl = B2R sh + B2R w) by lra.
split; [exact Frh |]. split; [exact Frl |].
split; [rewrite Hsum; exact Erh |].
(* The error is that of [w] alone: at most [2^-102 T + eps]. *)
rewrite Hsum. apply Rabs_le. revert Bw Es0 P27 Ht. num. intros. lra.
Qed.
