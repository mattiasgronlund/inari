(** * The reduction of large arguments of the fast paths of [sin], [cos] and [tan]

    Where [DyadicTrig.fast_reduce_big x] of [Model.v] returns [(n, rh, rl,
    rr)], [x] is finite with [|x| >= 2^16], [n] is in [[0, 8191]] with [n
    mod 2048 <> 0], and there is an integer [N = n] mod 8192 such that [x
    - N π/4096] is at most [π/8192 (1 + 2^-24)] in magnitude and [rh + rl]
    is within [2^-90] of it, with [|rl| <= 2^-37], [|rh| >= 2^-65] and [rr
    = rh + rl] rounded ([fast_reduce_big_correct]); the same with and
    without an FMA ([fast_reduce_big_fma]). [DyadicTrig.fast_reduce_any],
    which [fast_sin], [fast_cos] and [fast_tan] call, gives the bounds of
    [fast_reduce_correct] ([FastTrigReduce.v]) on [rh], [rl], [rr] and
    [x - N π/4096] for an integer [N] equal to [n] modulo 8192, and gives
    [n = 0] only from [fast_reduce] ([fast_reduce_any_correct]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Encoding TwoSum FastTrigTables FastTrigReduce
  FastTrigBigInt FastTrigBigMul FastTrigBigDec FastTrigBigSum.

Open Scope R_scope.

(** [Some a = Some b] gives [a = b], without [injection] on the
    floats of [fast_reduce_big]. *)
Lemma some_eq : forall (A : Type) (a b : A), Some a = Some b -> a = b.
Proof.
intros A a b E. injection E as E. exact E.
Qed.

(** [zh 2^-53] for [zh] in [[-2^52, 2^52)] is in [[-1/2, 1/2 - 2^-53]]. *)
Lemma big_h_bounds :
  forall z, (- 2 ^ 52 <= z < 2 ^ 52)%Z ->
  - / 2 <= IZR z * bpow radix2 (-53) <= / 2 - bpow radix2 (-53).
Proof.
intros z Hz.
assert (Z1 : (-4503599627370496 <= z)%Z) by lia.
assert (Z2 : (z <= 4503599627370495)%Z) by lia.
apply IZR_le in Z1. apply IZR_le in Z2.
cbn [bpow radix_val radix2 Z.opp].
lra.
Qed.

(** [zl 2^-106] for [zl] in [[0, 2^53)] is in [[0, 2^-53)]. *)
Lemma big_l_bounds :
  forall z, (0 <= z < 2 ^ 53)%Z ->
  0 <= IZR z * bpow radix2 (-106) < bpow radix2 (-53).
Proof.
intros z Hz.
assert (Z1 : (0 <= z)%Z) by lia.
assert (Z2 : (z <= 9007199254740991)%Z) by lia.
apply IZR_le in Z1. apply IZR_le in Z2.
cbn [bpow radix_val radix2 Z.opp].
lra.
Qed.

(** The end of [fast_reduce_big] after the sign: where the product [rh +
    rl] of [fh + fl = s (h + l)] passes the test [|rh| >= 2^-65], it is
    within [2^-90] of [s X - s N π/4096] ([big_guard], [big_mul_correct],
    [big_err]). *)
Lemma big_tail :
  forall s X N h l t xr Nr fh fl rh rl,
  (s = 1 \/ s = - 1) -> xr = s * X -> Nr = s * N ->
  is_finite fh = true -> is_finite fl = true ->
  B2R fh = s * h -> B2R fl = s * l ->
  X / (PI / 4096) = N + h + l + t ->
  - / 2 <= h <= / 2 - bpow radix2 (-53) ->
  0 <= l < bpow radix2 (-53) ->
  0 <= t < bpow radix2 (-105) ->
  DyadicTrig.fast_mul false fh fl
    (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)) (from_bits DyadicTrig.U3) =
    (rh, rl) ->
  lt (fabs rh) (from_bits 0x3be0000000000000) = false ->
  is_finite rh = true /\ is_finite rl = true /\ is_finite (add rh rl) = true /\
  Rabs (xr - Nr * (PI / 4096) - (B2R rh + B2R rl)) <= bpow radix2 (-90) /\
  Rabs (xr - Nr * (PI / 4096)) <= PI / 8192 * (1 + bpow radix2 (-24)) /\
  Rabs (B2R rl) <= bpow radix2 (-37) /\ bpow radix2 (-65) <= Rabs (B2R rh).
Proof.
intros s X N h l t xr Nr fh fl rh rl Hs -> -> Ffh Ffl Efh Efl EX Hh Hl Ht M L.
pose proof (bpow_gt_0 radix2 (-53)) as P53.
assert (Bfh : Rabs (B2R fh) <= / 2).
{ rewrite Efh. apply Rabs_le. destruct Hs as [-> | ->]; lra. }
assert (Bfl : Rabs (B2R fl) <= bpow radix2 (-53)).
{ rewrite Efl. apply Rabs_le. destruct Hs as [-> | ->]; lra. }
(* [rh] is [fh uh] rounded, for [fast_mul] of either flag. *)
pose proof M as Mp.
unfold DyadicTrig.fast_mul in Mp. cbv zeta in Mp.
apply pair_equal_spec in Mp as (Ep & _).
rewrite <- Ep in L.
destruct (big_guard fh Ffh Bfh L) as (_ & Hrh).
rewrite Ep in Hrh.
destruct (big_mul_correct fh fl rh rl Ffh Ffl Bfh Bfl M Hrh)
  as (Frh & Frl & Frr & Herr & Hrl).
assert (Herr' : Rabs ((s * h + s * l) * (PI / 4096) - (B2R rh + B2R rl)) <=
                bpow radix2 (-100)).
{ rewrite <- Efh, <- Efl. exact Herr. }
destruct (big_err s X N h l t (B2R rh) (B2R rl) Hs EX Hh Hl Ht Herr') as (E1 & E2).
split; [exact Frh |]. split; [exact Frl |]. split; [exact Frr |].
split; [exact E1 |]. split; [exact E2 |]. split; [exact Hrl | exact Hrh].
Qed.

Theorem fast_reduce_big_correct :
  forall x n rh rl rr,
  DyadicTrig.fast_reduce_big false x = Some (n, rh, rl, rr) ->
  is_finite x = true /\ 65536 <= Rabs (B2R x) /\ (0 <= n < 8192)%Z /\
  (Z.land n 2047 <> 0)%Z /\
  is_finite rh = true /\ is_finite rl = true /\ is_finite rr = true /\ rr = add rh rl /\
  exists N, (N mod 8192 = n)%Z /\
  Rabs (B2R x - IZR N * (PI / 4096) - (B2R rh + B2R rl)) <= bpow radix2 (-90) /\
  Rabs (B2R x - IZR N * (PI / 4096)) <= PI / 8192 * (1 + bpow radix2 (-24)) /\
  Rabs (B2R rl) <= bpow radix2 (-37) /\ bpow radix2 (-65) <= Rabs (B2R rh).
Proof.
intros x n rh rl rr H.
unfold DyadicTrig.fast_reduce_big in H.
pose proof (big_decode x) as D.
cbv zeta in H, D.
(* Name the integers of [fast_reduce_big] as [Model.v] does ([nn] for
   its [n]), in [H] and in the statements of [big_decode] and [big_int]. *)
set (b := Z.land (to_bits x) (2 ^ 63 - 1)%Z) in *.
set (be := Z.shiftr b 52) in *.
set (m := Z.lor (Z.land b (2 ^ 52 - 1)) (2 ^ 52)%Z) in *.
pose proof (big_int m be) as BI. cbv zeta in BI.
set (k := (be - 1011)%Z) in *.
set (p0 := (m * DyadicTrig.big_w k 2)%Z) in *.
set (p1 := (m * DyadicTrig.big_w k 1)%Z) in *.
set (c := (Z.shiftr p0 64 + p1 mod 2 ^ 64)%Z) in *.
set (r1 := (c mod 2 ^ 64)%Z) in *.
set (r2 := ((m * DyadicTrig.big_w k 0 + Z.shiftr p1 64 + Z.shiftr c 64) mod 2 ^ 64)%Z) in *.
set (nn := Z.shiftr ((r2 + 2 ^ 50) mod 2 ^ 64)%Z 51) in *.
set (a0 := Z.lor (Z.shiftl r2 13 mod 2 ^ 64)%Z (Z.shiftr r1 51)) in *.
set (a := if (a0 <? 2 ^ 63)%Z then a0 else (a0 - 2 ^ 64)%Z) in *.
set (zh := Z.shiftr a 11) in *.
set (zl := Z.land (Z.shiftr r1 9) (2 ^ 53 - 1)%Z) in *.
(* The exponent test. *)
destruct (negb ((1039 <=? be) && (be <=? 2046)))%Z eqn:G; [discriminate H |].
apply Bool.negb_false_iff in G.
destruct (D G) as (Fx & Hbe & Hm & Ex & Hx). clear D.
destruct (BI Hm Hbe) as (Hzh & Hzl & N & t & EN & EX & Ht). clear BI.
(* The test of [n mod 2048]. *)
destruct (Z.land nn 2047 =? 0)%Z eqn:Hn; [discriminate H |].
apply Z.eqb_neq in Hn.
clearbody zh zl a a0 nn r2 r1 c p1 p0 k m be b.
assert (Hzh2 : (- 2 ^ 52 <= zh <= 2 ^ 52)%Z) by lia.
destruct (big_fh zh Hzh2) as (Ffh & Efh).
destruct (big_fl zl Hzl) as (Ffl & Efl).
set (fh := mul (DyadicTrig.of_i64 zh) (from_bits 0x3ca0000000000000)) in *.
set (fl := mul (DyadicTrig.of_i64 zl) (from_bits 0x3950000000000000)) in *.
clearbody fh fl.
pose proof (big_h_bounds zh Hzh) as Hh.
pose proof (big_l_bounds zl Hzl) as Hl.
(* The sign: [fh], [fl] and [N] change sign with [x]. *)
destruct (lt x zero) eqn:S; cbv beta iota in H, Ex.
- revert H.
  destruct (DyadicTrig.fast_mul false _ _ _ _) as (p, q) eqn:M.
  cbv beta iota.
  destruct (lt (fabs p) (from_bits 0x3be0000000000000)) eqn:L; [discriminate |].
  intro H. apply some_eq in H.
  apply pair_equal_spec in H as (H & Er).
  apply pair_equal_spec in H as (H & Eql).
  apply pair_equal_spec in H as (En & Ep).
  subst n rh rl rr.
  assert (Hs : - 1 = 1 \/ - 1 = - 1) by (right; reflexivity).
  assert (EN' : IZR (- N) = - 1 * IZR N) by (rewrite opp_IZR; ring).
  assert (Ffo : is_finite (opp fh) = true)
    by (unfold opp; rewrite is_finite_Bopp; exact Ffh).
  assert (Flo : is_finite (opp fl) = true)
    by (unfold opp; rewrite is_finite_Bopp; exact Ffl).
  assert (Efo : B2R (opp fh) = - 1 * (IZR zh * bpow radix2 (-53)))
    by (unfold opp; rewrite B2R_Bopp, Efh; ring).
  assert (Elo : B2R (opp fl) = - 1 * (IZR zl * bpow radix2 (-106)))
    by (unfold opp; rewrite B2R_Bopp, Efl; ring).
  destruct (big_tail _ _ _ _ _ _ _ _ _ _ _ _ Hs Ex EN' Ffo Flo Efo Elo EX Hh Hl Ht M L)
    as (Frh & Frl & Frr & E1 & E2 & Hrl & Hrh).
  pose proof (big_neg_mod N nn EN) as EN2.
  split; [exact Fx |]. split; [exact Hx |].
  split; [rewrite <- EN2; apply Z.mod_pos_bound; lia |].
  split.
  { (* [(-nn) mod 2048 = 0] would give [nn mod 2048 = 0]. *)
    rewrite <- Z.land_assoc. change (Z.land 8191 2047) with 2047%Z.
    change 2047%Z with (Z.ones 11) in Hn |- *.
    rewrite Z.land_ones in Hn |- * by lia.
    intro E. apply Hn.
    rewrite <- (Z.opp_involutive nn). apply Z_mod_zero_opp_full. exact E. }
  split; [exact Frh |]. split; [exact Frl |]. split; [exact Frr |].
  split; [reflexivity |].
  exists (- N)%Z.
  split; [exact EN2 |]. split; [exact E1 |]. split; [exact E2 |].
  split; [exact Hrl | exact Hrh].
- revert H.
  destruct (DyadicTrig.fast_mul false _ _ _ _) as (p, q) eqn:M.
  cbv beta iota.
  destruct (lt (fabs p) (from_bits 0x3be0000000000000)) eqn:L; [discriminate |].
  intro H. apply some_eq in H.
  apply pair_equal_spec in H as (H & Er).
  apply pair_equal_spec in H as (H & Eql).
  apply pair_equal_spec in H as (En & Ep).
  subst n rh rl rr.
  assert (Hs : 1 = 1 \/ 1 = - 1) by (left; reflexivity).
  assert (EN' : IZR N = 1 * IZR N) by ring.
  assert (Efo : B2R fh = 1 * (IZR zh * bpow radix2 (-53))) by (rewrite Efh; ring).
  assert (Elo : B2R fl = 1 * (IZR zl * bpow radix2 (-106))) by (rewrite Efl; ring).
  destruct (big_tail _ _ _ _ _ _ _ _ _ _ _ _ Hs Ex EN' Ffh Ffl Efo Elo EX Hh Hl Ht M L)
    as (Frh & Frl & Frr & E1 & E2 & Hrl & Hrh).
  split; [exact Fx |]. split; [exact Hx |].
  split; [rewrite <- EN; apply Z.mod_pos_bound; lia |].
  split; [exact Hn |].
  split; [exact Frh |]. split; [exact Frl |]. split; [exact Frr |].
  split; [reflexivity |].
  exists N.
  split; [exact EN |]. split; [exact E1 |]. split; [exact E2 |].
  split; [exact Hrl | exact Hrh].
Qed.

(** The end of [fast_reduce_big] after the sign is the same with and
    without an FMA: where the test [|fh uh| < 2^-65] passes, both
    return [None], as [rh] is [fh uh] rounded for either flag, and
    elsewhere [big_mul_fma] gives the same product. *)
Lemma big_fma_tail :
  forall (n : Z) fh fl, is_finite fh = true -> Rabs (B2R fh) <= / 2 ->
  (let '(rh, rl) := DyadicTrig.fast_mul true fh fl
       (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)) (from_bits DyadicTrig.U3) in
   if lt (fabs rh) (from_bits 0x3be0000000000000) then None
   else Some (n, rh, rl, add rh rl)) =
  (let '(rh, rl) := DyadicTrig.fast_mul false fh fl
       (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)) (from_bits DyadicTrig.U3) in
   if lt (fabs rh) (from_bits 0x3be0000000000000) then None
   else Some (n, rh, rl, add rh rl)).
Proof.
intros n fh fl Ffh Bfh.
destruct (lt (fabs (mul fh (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2))))
             (from_bits 0x3be0000000000000)) eqn:L.
- unfold DyadicTrig.fast_mul. cbv beta zeta iota. rewrite L. cbv iota. reflexivity.
- destruct (big_guard fh Ffh Bfh L) as (_ & Hp).
  rewrite (big_mul_fma fh fl Ffh Bfh Hp). reflexivity.
Qed.

Theorem fast_reduce_big_fma :
  forall x, DyadicTrig.fast_reduce_big true x = DyadicTrig.fast_reduce_big false x.
Proof.
intros x.
unfold DyadicTrig.fast_reduce_big.
pose proof (big_decode x) as D.
cbv zeta. cbv zeta in D.
set (b := Z.land (to_bits x) (2 ^ 63 - 1)%Z) in *.
set (be := Z.shiftr b 52) in *.
set (m := Z.lor (Z.land b (2 ^ 52 - 1)) (2 ^ 52)%Z) in *.
pose proof (big_int m be) as BI. cbv zeta in BI.
set (k := (be - 1011)%Z) in *.
set (p0 := (m * DyadicTrig.big_w k 2)%Z) in *.
set (p1 := (m * DyadicTrig.big_w k 1)%Z) in *.
set (c := (Z.shiftr p0 64 + p1 mod 2 ^ 64)%Z) in *.
set (r1 := (c mod 2 ^ 64)%Z) in *.
set (r2 := ((m * DyadicTrig.big_w k 0 + Z.shiftr p1 64 + Z.shiftr c 64) mod 2 ^ 64)%Z) in *.
set (nn := Z.shiftr ((r2 + 2 ^ 50) mod 2 ^ 64)%Z 51) in *.
set (a0 := Z.lor (Z.shiftl r2 13 mod 2 ^ 64)%Z (Z.shiftr r1 51)) in *.
set (a := if (a0 <? 2 ^ 63)%Z then a0 else (a0 - 2 ^ 64)%Z) in *.
set (zh := Z.shiftr a 11) in *.
destruct (negb ((1039 <=? be) && (be <=? 2046)))%Z eqn:G; cbv beta iota; [reflexivity |].
apply Bool.negb_false_iff in G.
destruct (D G) as (_ & Hbe & Hm & _). clear D.
destruct (BI Hm Hbe) as (Hzh & _). clear BI.
destruct (Z.land nn 2047 =? 0)%Z; cbv beta iota; [reflexivity |].
clearbody zh a a0 nn r2 r1 c p1 p0 k m be b.
assert (Hzh2 : (- 2 ^ 52 <= zh <= 2 ^ 52)%Z) by lia.
destruct (big_fh zh Hzh2) as (Ffh & Efh).
set (fh := mul (DyadicTrig.of_i64 zh) (from_bits 0x3ca0000000000000)) in *.
clearbody fh.
assert (Bfh : Rabs (B2R fh) <= / 2).
{ pose proof (big_h_bounds zh Hzh) as Hh.
  pose proof (bpow_gt_0 radix2 (-53)) as P53.
  rewrite Efh. apply Rabs_le. lra. }
destruct (lt x zero); cbv beta iota.
- apply big_fma_tail.
  + unfold opp. rewrite is_finite_Bopp. exact Ffh.
  + unfold opp. rewrite B2R_Bopp, Rabs_Ropp. exact Bfh.
- apply big_fma_tail; assumption.
Qed.

Lemma fast_reduce_any_correct :
  forall x n rh rl rr,
  DyadicTrig.fast_reduce_any false x = Some (n, rh, rl, rr) ->
  (n = 0%Z -> DyadicTrig.fast_reduce x = Some (n, rh, rl, rr)) /\
  is_finite x = true /\
  is_finite rh = true /\ is_finite rl = true /\ is_finite rr = true /\ rr = add rh rl /\
  Rabs (B2R rl) <= bpow radix2 (-37) /\
  (n <> 0%Z -> B2R rh <> 0 -> bpow radix2 (-65) <= Rabs (B2R rh)) /\
  exists N, ((N - n) mod 8192 = 0)%Z /\
  Rabs (B2R x - IZR N * (PI / 4096) - (B2R rh + B2R rl)) <= bpow radix2 (-90) /\
  Rabs (B2R x - IZR N * (PI / 4096)) <= PI / 8192 * (1 + bpow radix2 (-24)).
Proof.
intros x n rh rl rr H.
unfold DyadicTrig.fast_reduce_any in H.
destruct (DyadicTrig.fast_reduce x) as [r |] eqn:R.
- (* [fast_reduce]: [N = n]. *)
  apply some_eq in H. subst r.
  destruct (fast_reduce_correct x n rh rl rr R)
    as (Fx & _ & _ & Frh & Frl & Frr & Err & E1 & E2 & Hrl & Hrh).
  split; [intros _; reflexivity |].
  split; [exact Fx |]. split; [exact Frh |]. split; [exact Frl |].
  split; [exact Frr |]. split; [exact Err |]. split; [exact Hrl |].
  split; [exact Hrh |].
  exists n. rewrite Z.sub_diag.
  split; [reflexivity |]. split; [exact E1 | exact E2].
- (* [fast_reduce_big], whose [n] is not 0. *)
  destruct (fast_reduce_big_correct x n rh rl rr H)
    as (Fx & _ & Hn & Hland & Frh & Frl & Frr & Err & N & EN & E1 & E2 & Hrl & Hrh).
  assert (Hn0 : n <> 0%Z) by (intro E; apply Hland; rewrite E; reflexivity).
  split; [intro E; contradiction |].
  split; [exact Fx |]. split; [exact Frh |]. split; [exact Frl |].
  split; [exact Frr |]. split; [exact Err |]. split; [exact Hrl |].
  split; [intros _ _; exact Hrh |].
  exists N.
  split.
  + rewrite Zminus_mod, EN, (Z.mod_small n 8192) by lia.
    rewrite Z.sub_diag. reflexivity.
  + split; [exact E1 | exact E2].
Qed.

Lemma fast_reduce_any_fma :
  forall x, DyadicTrig.fast_reduce_any true x = DyadicTrig.fast_reduce_any false x.
Proof.
intros x.
unfold DyadicTrig.fast_reduce_any.
destruct (DyadicTrig.fast_reduce x); [reflexivity |].
apply fast_reduce_big_fma.
Qed.
