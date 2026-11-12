(** * The reduction of the fast paths of [sin], [cos] and [tan] near the multiples of π/2 above 2^16

    Where [DyadicTrig.fast_reduce_band_big false x] of [Model.v] returns
    [(n, rh, rl, rr)], [x] is finite with [|x| >= 2^16], [n] is in [[0,
    8191]] with [n mod 2048 = 0], and there is an integer [N = n] mod 8192
    such that ρ = x - N π/4096 is at least 2^-61 in magnitude
    ([km_distance] of [KahanMcDonald.v], as [N π/4096] is a nonzero
    multiple of π/2) and at most π/8192 (1 + 2^-24), [rh + rl] is within a
    relative 2^-74 of ρ, [|rl| <= 2^-24 |rh|] and [rr = rh + rl] rounded
    ([fast_reduce_band_big_correct]): the window of 1/(2π) of
    [fast_reduce_big] ([FastTrigBig.v]) knows the fraction F = x 4096/π
    - N within 2^-126, which is relative at |F| >= 2^-61 4096/π, and [F]
    is normalized before its 106 bits are taken. It is the same with an
    FMA ([fast_reduce_band_big_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Encoding TwoSum FastTrigTables FastTrigReduce
  FastTrigBigInt FastTrigBigMul FastTrigBigDec FastTrigBigSum FastTrigBig KahanMcDonald
  FastTrigBandInt FastTrigBandMul.
From Inari Require Limbs DyConstPi.

Open Scope R_scope.

(* How [band_dist] and [band_tail] are proved.

   band_dist: N = 2048 k ([Z_div_exact_full_2]). k = 0 is impossible:
   then X/u = A 2^-128 + τ < 1/2 + 5 2^-128 gives |X| < 1, but |X| = |x|
   >= 2^16. [km_distance x (sgZ k)], with sgZ = 1 or -1 the integer of sg:
   x - sgZ k π/2 = sg (X - N u), as N u = k π/2. Upper bound: X - N u = u
   (A 2^-128 + τ) and -1/2 <= A 2^-128 + τ < 1/2 + 4 2^-128. |A| >= 2^77:
   u (|A| 2^-128 + 5 2^-128) >= 2^-61 and u <= 202/64/4096 ([band_u]), so
   |A| 2^-128 >= 2^-61/u - 5 2^-128 > 2^-51.

   band_tail (as [big_tail] of FastTrigBig.v): S = 2^-s. [band_f_bounds]
   gives the premises of [band_mul_rel], which gives finite rh, rl, rr,
   |(fh + fl) u - (rh + rl)| <= 2^-110 S and |rl| <= 2^-24 |rh|. fh + fl
   = sg f with f = floor(A 2^s / 2^22) 2^(-106-s), so Φ - f is in [0,
   2^-106 S + 5 2^-128) for Φ = A 2^-128 + τ = (X - N u)/u. xr - Nr u -
   (rh + rl) = sg u (Φ - f) + ((fh + fl) u - (rh + rl)). From S/8 <= |fh|
   and |fl| <= 2^-53 S ([band_f_bounds]), |f| >= S/8.0001, so S <= 8.0001
   |f| <= 8.0001 (|Φ| + 2^-106 S + 5 2^-128), and S <= 8.0002 |Φ| + 41
   2^-128.
     window + floor: u 5 2^-128 <= 2^-75.0 |ρ| (u <= 7.71e-4, |ρ| >= 2^-61);
     normalization: u 2^-106 S <= 2^-102.9 |ρ|;
     product: 2^-110 S <= 2^-96.6 |ρ| (|Φ| = |ρ|/u <= 1305 |ρ|).
     Total <= 2^-74.9 |ρ| <= 2^-74 |ρ|. *)

(** [π/4096] between [201/2^18] and [202/2^18], from the table of π. *)
Local Lemma band_u : 201 / 262144 <= PI / 4096 <= 202 / 262144.
Proof.
pose proof km_pi_lb as Hl.
destruct DyConstPi.PI_bounds as [_ H].
assert (HL : (Limbs.val DyadicConsts.PI + 1 <= 202 * 2 ^ 4216)%Z)
  by (apply Z.leb_le; vm_compute; reflexivity).
apply IZR_le in HL. rewrite plus_IZR, mult_IZR, km_IZR_pow2 in HL by lia.
set (L := IZR (Limbs.val DyadicConsts.PI)) in *.
assert (E : bpow radix2 4216 * bpow radix2 (-4222) = / 64).
{ rewrite <- bpow_plus. reflexivity. }
assert ((L + 1) * bpow radix2 (-4222) <= 202 * bpow radix2 4216 * bpow radix2 (-4222))
  by (apply Rmult_le_compat_r; [apply bpow_ge_0 | lra]).
split; lra.
Qed.

(** [|sg X| = |X|] for [sg = ±1]. *)
Local Lemma band_abs_sg :
  forall sg X, (sg = 1 \/ sg = - 1) -> Rabs (sg * X) = Rabs X.
Proof.
intros sg X [-> | ->].
- rewrite Rmult_1_l. reflexivity.
- replace (-1 * X) with (- X) by ring. apply Rabs_Ropp.
Qed.

Local Lemma band_dist :
  forall (x : f64) sg X (N A : Z) t,
  is_finite x = true -> (sg = 1 \/ sg = - 1) -> B2R x = sg * X ->
  65536 <= Rabs (B2R x) ->
  X / (PI / 4096) = IZR N + IZR A * bpow radix2 (-128) + t ->
  0 <= t < 5 * bpow radix2 (-128) ->
  (- 2 ^ 127 <= A < 2 ^ 127)%Z -> (N mod 2048 = 0)%Z ->
  (2 ^ 77 <= Z.abs A)%Z /\
  bpow radix2 (-61) <= Rabs (X - IZR N * (PI / 4096)) <=
    PI / 8192 * (1 + bpow radix2 (-24)).
Proof.
intros x sg X N A t Fx Hsg Ex Hx EX Ht HA HN.
pose proof band_u as Hu.
pose proof PI_RGT_0 as HP0.
(* [N π/4096 = k π/2] *)
assert (ENk : (N = 2048 * (N / 2048))%Z) by (apply Z_div_exact_full_2; [lia | exact HN]).
set (k := (N / 2048)%Z) in ENk.
assert (EK : IZR N * (PI / 4096) = IZR k * (PI / 2)) by (rewrite ENk, mult_IZR; field).
(* [|x - k' π/2| >= 2^-61] for the integer [k' = sg k], where [k <> 0] *)
assert (HXabs : Rabs (B2R x) = Rabs X) by (rewrite Ex; apply band_abs_sg; exact Hsg).
set (P := IZR A * bpow radix2 (-128) + t).
assert (EP : X - IZR N * (PI / 4096) = PI / 4096 * P).
{ assert (EXu : X = (IZR N + IZR A * bpow radix2 (-128) + t) * (PI / 4096)).
  { rewrite <- EX. field. lra. }
  rewrite EXu. unfold P. ring. }
(* [A 2^-128] is in [[-1/2, 1/2 - 2^-128]] *)
assert (HA1 : - bpow radix2 127 <= IZR A <= bpow radix2 127 - 1).
{ rewrite <- km_IZR_pow2 by lia. split.
  - rewrite <- opp_IZR. apply IZR_le. lia.
  - rewrite <- minus_IZR. apply IZR_le. lia. }
destruct HA1 as [HA1 HA2].
apply (Rmult_le_compat_r (bpow radix2 (-128))) in HA1; [| apply bpow_ge_0].
apply (Rmult_le_compat_r (bpow radix2 (-128))) in HA2; [| apply bpow_ge_0].
assert (HPb : - / 2 <= P <= / 2 + 4 * bpow radix2 (-128)).
{ unfold P. clear - HA1 HA2 Ht. cbn [bpow radix_val radix2] in *. lra. }
assert (HPa : Rabs P <= / 2 + 4 * bpow radix2 (-128)).
{ apply Rabs_le. pose proof (bpow_ge_0 radix2 (-128)). lra. }
assert (HuP : Rabs (X - IZR N * (PI / 4096)) = PI / 4096 * Rabs P).
{ rewrite EP, Rabs_mult, (Rabs_pos_eq (PI / 4096)) by lra. reflexivity. }
assert (HuP1 : PI / 4096 * Rabs P <= 202 / 262144 * Rabs P)
  by (apply Rmult_le_compat_r; [apply Rabs_pos | lra]).
assert (Hk : k <> 0%Z).
{ intro E0.
  assert (HN0 : IZR N = 0) by (rewrite ENk, E0; reflexivity).
  rewrite HN0, Rmult_0_l, Rminus_0_r in EP.
  assert (HX1 : Rabs (B2R x) = PI / 4096 * Rabs P).
  { rewrite HXabs, EP, Rabs_mult, (Rabs_pos_eq (PI / 4096)) by lra. reflexivity. }
  assert (HuP2 : 202 / 262144 * Rabs P <= 202 / 262144 * (/ 2 + 4 * bpow radix2 (-128)))
    by (apply Rmult_le_compat_l; lra).
  clear - Hx HX1 HuP1 HuP2. cbn [bpow radix_val radix2] in *. lra. }
assert (Hd : bpow radix2 (-61) <= Rabs (X - IZR N * (PI / 4096))).
{ rewrite EK. destruct Hsg as [Es | Es]; rewrite Es in Ex.
  - pose proof (km_distance x k Fx Hk) as K.
    rewrite Ex, Rmult_1_l in K. exact K.
  - assert (Hk' : (- k)%Z <> 0%Z) by lia.
    pose proof (km_distance x (- k) Fx Hk') as K.
    replace (B2R x - IZR (- k) * (PI / 2)) with (- (X - IZR k * (PI / 2))) in K
      by (rewrite Ex, opp_IZR; ring).
    rewrite Rabs_Ropp in K. exact K. }
split; [| split; [exact Hd |]].
- (* [|A| < 2^77] would put [|X - N u|] below [2^-61] *)
  destruct (Z_lt_le_dec (Z.abs A) (2 ^ 77)) as [Hl | Hl]; [exfalso | exact Hl].
  assert (HAl : Rabs (IZR A) <= bpow radix2 77 - 1).
  { rewrite <- abs_IZR, <- km_IZR_pow2, <- minus_IZR by lia. apply IZR_le. lia. }
  assert (HAb : Rabs (IZR A * bpow radix2 (-128)) <=
                (bpow radix2 77 - 1) * bpow radix2 (-128)).
  { rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (-128))) by apply bpow_ge_0.
    apply Rmult_le_compat_r; [apply bpow_ge_0 | exact HAl]. }
  assert (HPs : Rabs P <= Rabs (IZR A * bpow radix2 (-128)) + Rabs t)
    by apply Rabs_triang.
  rewrite (Rabs_pos_eq t) in HPs by lra.
  assert (HuP2 : 202 / 262144 * Rabs P <=
                 202 / 262144 * ((bpow radix2 77 - 1) * bpow radix2 (-128) +
                                 5 * bpow radix2 (-128)))
    by (apply Rmult_le_compat_l; lra).
  rewrite HuP in Hd.
  clear - Hd HuP1 HuP2. cbn [bpow radix_val radix2] in *. lra.
- (* [|X - N u| = u |P| <= u/2 (1 + 2^-24)] *)
  rewrite HuP.
  replace (PI / 8192) with (PI / 4096 / 2) by field.
  assert (H2 : / 2 + 4 * bpow radix2 (-128) <= (1 + bpow radix2 (-24)) / 2)
    by (cbn [bpow radix_val radix2]; lra).
  replace (PI / 4096 / 2 * (1 + bpow radix2 (-24)))
    with (PI / 4096 * ((1 + bpow radix2 (-24)) / 2)) by field.
  apply Rmult_le_compat_l; lra.
Qed.

Local Lemma band_tail :
  forall sg X (N A : Z) t (s zh zl : Z) xr Nr (fh fl rh rl : f64),
  (sg = 1 \/ sg = - 1) -> xr = sg * X -> Nr = sg * IZR N ->
  X / (PI / 4096) = IZR N + IZR A * bpow radix2 (-128) + t ->
  0 <= t < 5 * bpow radix2 (-128) ->
  bpow radix2 (-61) <= Rabs (X - IZR N * (PI / 4096)) <=
    PI / 8192 * (1 + bpow radix2 (-24)) ->
  (0 <= s <= 50)%Z ->
  (zh * 2 ^ 53 + zl = A * 2 ^ s / 2 ^ 22)%Z ->
  (2 ^ 51 - 1 <= Z.abs zh <= 2 ^ 52)%Z -> (0 <= zl < 2 ^ 53)%Z ->
  is_finite fh = true -> is_finite fl = true ->
  B2R fh = sg * (IZR zh * bpow radix2 (-53 - s)) ->
  B2R fl = sg * (IZR zl * bpow radix2 (-106 - s)) ->
  DyadicTrig.fast_mul false fh fl
    (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)) (from_bits DyadicTrig.U3) =
    (rh, rl) ->
  is_finite rh = true /\ is_finite rl = true /\ is_finite (add rh rl) = true /\
  bpow radix2 (-61) <= Rabs (xr - Nr * (PI / 4096)) <=
    PI / 8192 * (1 + bpow radix2 (-24)) /\
  Rabs (xr - Nr * (PI / 4096) - (B2R rh + B2R rl)) <=
    bpow radix2 (-74) * Rabs (xr - Nr * (PI / 4096)) /\
  Rabs (B2R rl) <= bpow radix2 (-24) * Rabs (B2R rh).
Proof.
intros sg X N A t s zh zl xr Nr fh fl rh rl Hsg -> -> EX Ht Hd Hs Ez Hzh Hzl
  Ffh Ffl Efh Efl M.
destruct (band_f_bounds sg zh zl s fh fl Hsg Hs Hzh Hzl Efh Efl) as (HS & Bfh & Bfl).
destruct (band_mul_rel _ fh fl rh rl HS Ffh Ffl Bfh Bfl M)
  as (Frh & Frl & Frr & Herr & _ & Hrl).
pose proof band_u as Hu.
pose proof PI_RGT_0 as HP0.
(* [sg X - sg N u = sg (X - N u)] *)
assert (Er : sg * X - sg * IZR N * (PI / 4096) = sg * (X - IZR N * (PI / 4096))) by ring.
rewrite Er, band_abs_sg by exact Hsg.
split; [exact Frh |]. split; [exact Frl |]. split; [exact Frr |].
split; [exact Hd |].
split; [| exact Hrl].
(* [X - N u = u Φ] *)
set (P := IZR A * bpow radix2 (-128) + t).
assert (EP : X - IZR N * (PI / 4096) = PI / 4096 * P).
{ assert (EXu : X = (IZR N + IZR A * bpow radix2 (-128) + t) * (PI / 4096)).
  { rewrite <- EX. field. lra. }
  rewrite EXu. unfold P. ring. }
(* [fh + fl = sg f] for [f = (zh 2^53 + zl) 2^(-106-s)] *)
set (S := bpow radix2 (- s)) in *.
assert (ES53 : bpow radix2 (-53 - s) = bpow radix2 (-53) * S)
  by (unfold S; rewrite <- bpow_plus; f_equal; lia).
assert (ES106 : bpow radix2 (-106 - s) = bpow radix2 (-106) * S)
  by (unfold S; rewrite <- bpow_plus; f_equal; lia).
set (f := IZR zh * bpow radix2 (-53 - s) + IZR zl * bpow radix2 (-106 - s)).
assert (Ef : B2R fh + B2R fl = sg * f) by (rewrite Efh, Efl; unfold f; ring).
(* [A 2^-128 - f = r 2^-128 S] for the remainder [r] of [A 2^s / 2^22] *)
pose proof (Z.div_mod (A * 2 ^ s) (2 ^ 22) ltac:(lia)) as DM.
rewrite <- Ez in DM.
set (r := ((A * 2 ^ s) mod 2 ^ 22)%Z) in DM.
assert (Hr : (0 <= r < 2 ^ 22)%Z) by (apply Z.mod_pos_bound; lia).
assert (K1 : bpow radix2 22 * bpow radix2 53 * bpow radix2 (-128) = bpow radix2 (-53))
  by (rewrite <- !bpow_plus; reflexivity).
assert (K2 : bpow radix2 22 * bpow radix2 (-128) = bpow radix2 (-106))
  by (rewrite <- !bpow_plus; reflexivity).
assert (ED : IZR A * bpow radix2 (-128) - f = IZR r * bpow radix2 (-128) * S).
{ assert (E1 : IZR A = IZR (A * 2 ^ s) * S).
  { rewrite mult_IZR, km_IZR_pow2 by lia. unfold S.
    rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_r. cbn [bpow]. ring. }
  rewrite E1, DM, plus_IZR, mult_IZR, plus_IZR, mult_IZR, !km_IZR_pow2 by lia.
  unfold f. rewrite ES53, ES106, <- K1, <- K2. ring. }
assert (HD : 0 <= IZR A * bpow radix2 (-128) - f <= bpow radix2 (-106) * S).
{ rewrite ED.
  assert (Hr0 : 0 <= IZR r) by (apply IZR_le; lia).
  assert (Hr1 : IZR r <= bpow radix2 22)
    by (rewrite <- km_IZR_pow2 by lia; apply IZR_le; lia).
  pose proof (bpow_ge_0 radix2 (-128)) as P128.
  assert (HS0 : 0 <= S) by (unfold S; apply bpow_ge_0).
  split.
  - apply Rmult_le_pos; [apply Rmult_le_pos |]; assumption.
  - rewrite <- K2. apply Rmult_le_compat_r; [exact HS0 |].
    apply Rmult_le_compat_r; assumption. }
(* [|f| >= (2^-3 - 2^-53) S], from [band_f_bounds] *)
assert (Hf : (bpow radix2 (-3) - bpow radix2 (-53)) * S <= Rabs f).
{ rewrite <- (band_abs_sg sg f Hsg), <- Ef.
  pose proof (Rabs_triang (B2R fh + B2R fl) (- B2R fl)) as T.
  replace (B2R fh + B2R fl + - B2R fl) with (B2R fh) in T by ring.
  rewrite Rabs_Ropp in T. lra. }
(* the error: [sg (X - N u) - (rh + rl) = sg u (Φ - f) + ((fh + fl) u - (rh + rl))] *)
assert (EE : sg * (X - IZR N * (PI / 4096)) - (B2R rh + B2R rl) =
             sg * (PI / 4096 * (P - f)) +
             ((B2R fh + B2R fl) * (PI / 4096) - (B2R rh + B2R rl)))
  by (rewrite EP, Ef; ring).
rewrite EE, EP.
assert (HPf : 0 <= P - f <= bpow radix2 (-106) * S + 5 * bpow radix2 (-128))
  by (unfold P; lra).
assert (HE1 : Rabs (sg * (PI / 4096 * (P - f))) = PI / 4096 * (P - f)).
{ rewrite band_abs_sg by exact Hsg. apply Rabs_pos_eq.
  apply Rmult_le_pos; lra. }
pose proof (Rabs_triang (sg * (PI / 4096 * (P - f)))
              ((B2R fh + B2R fl) * (PI / 4096) - (B2R rh + B2R rl))) as T.
rewrite HE1 in T.
assert (HuP : Rabs (PI / 4096 * P) = PI / 4096 * Rabs P)
  by (rewrite Rabs_mult, (Rabs_pos_eq (PI / 4096)) by lra; reflexivity).
rewrite HuP. rewrite EP, HuP in Hd. destruct Hd as [Hd _].
(* [|f| <= |Φ| + (Φ - f)] *)
assert (HfP : Rabs f <= Rabs P + (P - f)).
{ replace f with (P - (P - f)) at 1 by ring.
  pose proof (Rabs_triang P (- (P - f))) as T2.
  rewrite Rabs_Ropp, (Rabs_pos_eq (P - f)) in T2 by lra. exact T2. }
(* the products with [u], for [lra] *)
set (u := PI / 4096) in *.
assert (Hu0 : 0 <= u) by lra.
assert (F1 : u * (P - f) <= u * (bpow radix2 (-106) * S + 5 * bpow radix2 (-128)))
  by (apply Rmult_le_compat_l; lra).
assert (F2 : u * ((bpow radix2 (-3) - bpow radix2 (-53)) * S) <=
             u * (Rabs P + (bpow radix2 (-106) * S + 5 * bpow radix2 (-128))))
  by (apply Rmult_le_compat_l; lra).
assert (F3 : 201 / 262144 * Rabs P <= u * Rabs P)
  by (apply Rmult_le_compat_r; [apply Rabs_pos | lra]).
assert (F4 : (bpow radix2 (-3) - bpow radix2 (-53)) * S <=
             Rabs P + (bpow radix2 (-106) * S + 5 * bpow radix2 (-128))) by lra.
clearbody u S f P.
clear - T Herr F1 F2 F3 F4 Hd Hu.
cbn [bpow radix_val radix2] in *.
lra.
Qed.

(** The integers of [fast_reduce_band_big] up to [zh] and [zl], named as
    in [Model.v], where both tests pass: [x] is finite with [|x| >=
    2^16], [x = sg X] for the sign [sg] of [x], [X/u = N + A 2^-128 + τ]
    with [N mod 8192 = n] ([band_int]), [X] is at least 2^-61 and at most
    [u/2 (1 + 2^-24)] away from [N u] ([band_dist], as [n mod 2048 = 0]),
    and [zh 2^53 + zl] is [A 2^s / 2^22] rounded down ([band_norm], as
    [|A| >= 2^77] puts [a] at least 2^13 away from 0). *)
Local Lemma band_big_chain :
  forall x,
  let b := Z.land (to_bits x) (2 ^ 63 - 1)%Z in
  let be := Z.shiftr b 52 in
  let m := Z.lor (Z.land b (2 ^ 52 - 1)) (2 ^ 52)%Z in
  let k := (be - 1011)%Z in
  let p0 := (m * DyadicTrig.big_w k 2)%Z in
  let p1 := (m * DyadicTrig.big_w k 1)%Z in
  let c := (Z.shiftr p0 64 + p1 mod 2 ^ 64)%Z in
  let r1 := (c mod 2 ^ 64)%Z in
  let r2 := ((m * DyadicTrig.big_w k 0 + Z.shiftr p1 64 + Z.shiftr c 64) mod 2 ^ 64)%Z in
  let n := Z.shiftr ((r2 + 2 ^ 50) mod 2 ^ 64)%Z 51 in
  let a0 := Z.lor (Z.shiftl r2 13 mod 2 ^ 64)%Z (Z.shiftr r1 51) in
  let a := if (a0 <? 2 ^ 63)%Z then a0 else (a0 - 2 ^ 64)%Z in
  let lo := Z.lor (Z.shiftl r1 13 mod 2 ^ 64)%Z (Z.shiftr (p0 mod 2 ^ 64) 51) in
  let s := (leading_zeros 64 (Z.lxor a (Z.shiftr a 63)) - 1)%Z in
  let t0 := Z.lor (Z.shiftl a0 s mod 2 ^ 64)%Z (Z.shiftr (Z.shiftr lo 1) (63 - s)) in
  let t := if (t0 <? 2 ^ 63)%Z then t0 else (t0 - 2 ^ 64)%Z in
  let v := (Z.shiftl lo s mod 2 ^ 64)%Z in
  let zh := Z.shiftr t 11 in
  let zl := Z.lor (Z.shiftl (Z.land t 2047) 42) (Z.shiftr v 22) in
  ((1039 <=? be) && (be <=? 2046))%Z = true -> Z.land n 2047 = 0%Z ->
  is_finite x = true /\ 65536 <= Rabs (B2R x) /\ (0 <= n < 8192)%Z /\
  (0 <= s <= 50)%Z /\ (- 2 ^ 52 <= zh <= 2 ^ 52)%Z /\
  (2 ^ 51 - 1 <= Z.abs zh <= 2 ^ 52)%Z /\ (0 <= zl < 2 ^ 53)%Z /\
  exists N A tau X,
  (N mod 8192 = n)%Z /\
  B2R x = (if lt x zero then - 1 else 1) * X /\
  X / (PI / 4096) = IZR N + IZR A * bpow radix2 (-128) + tau /\
  0 <= tau < 5 * bpow radix2 (-128) /\
  bpow radix2 (-61) <= Rabs (X - IZR N * (PI / 4096)) <=
    PI / 8192 * (1 + bpow radix2 (-24)) /\
  (zh * 2 ^ 53 + zl = A * 2 ^ s / 2 ^ 22)%Z.
Proof.
intros x. cbv zeta. intros G Hn.
pose proof (big_decode x) as D. cbv zeta in D.
set (b := Z.land (to_bits x) (2 ^ 63 - 1)%Z) in *.
set (be := Z.shiftr b 52) in *.
set (m := Z.lor (Z.land b (2 ^ 52 - 1)) (2 ^ 52)%Z) in *.
pose proof (band_int m be) as BI. cbv zeta in BI.
set (k := (be - 1011)%Z) in *.
set (p0 := (m * DyadicTrig.big_w k 2)%Z) in *.
set (p1 := (m * DyadicTrig.big_w k 1)%Z) in *.
set (c := (Z.shiftr p0 64 + p1 mod 2 ^ 64)%Z) in *.
set (r1 := (c mod 2 ^ 64)%Z) in *.
set (r2 := ((m * DyadicTrig.big_w k 0 + Z.shiftr p1 64 + Z.shiftr c 64) mod 2 ^ 64)%Z) in *.
set (nn := Z.shiftr ((r2 + 2 ^ 50) mod 2 ^ 64)%Z 51) in *.
set (a0 := Z.lor (Z.shiftl r2 13 mod 2 ^ 64)%Z (Z.shiftr r1 51)) in *.
set (lo := Z.lor (Z.shiftl r1 13 mod 2 ^ 64)%Z (Z.shiftr (p0 mod 2 ^ 64) 51)) in *.
destruct (D G) as (Fx & Hbe & Hm & Ex & Hx). clear D.
destruct (BI Hm Hbe) as (Ha0 & Hlo & HA & N & tau & EN & EX & Ht). clear BI.
(* [band_norm]'s lets are [Model.v]'s: name them after [cbv zeta] *)
pose proof (band_norm a0 lo Ha0 Hlo) as BN. cbv zeta in BN.
set (a := if (a0 <? 2 ^ 63)%Z then a0 else (a0 - 2 ^ 64)%Z) in *.
set (s := (leading_zeros 64 (Z.lxor a (Z.shiftr a 63)) - 1)%Z) in *.
set (t0 := Z.lor (Z.shiftl a0 s mod 2 ^ 64)%Z (Z.shiftr (Z.shiftr lo 1) (63 - s))) in *.
set (t := if (t0 <? 2 ^ 63)%Z then t0 else (t0 - 2 ^ 64)%Z) in *.
set (v := (Z.shiftl lo s mod 2 ^ 64)%Z) in *.
set (zh := Z.shiftr t 11) in *.
set (zl := Z.lor (Z.shiftl (Z.land t 2047) 42) (Z.shiftr v 22)) in *.
clearbody zl zh v t t0 s a lo a0 nn r2 r1 c p1 p0 k m be b.
(* [n mod 2048 = 0] gives [N mod 2048 = 0], as 2048 divides 8192 *)
assert (HN : (N mod 2048 = 0)%Z).
{ change 2047%Z with (Z.ones 11) in Hn. rewrite Z.land_ones in Hn by lia.
  change (2 ^ 11)%Z with 2048%Z in Hn.
  rewrite (Znumtheory.Zmod_div_mod 2048 8192 N) by (try lia; exists 4%Z; lia).
  rewrite EN. exact Hn. }
assert (Hsg : (if lt x zero then - 1 else 1) = 1 \/ (if lt x zero then - 1 else 1) = - 1)
  by (destruct (lt x zero); [right | left]; reflexivity).
destruct (band_dist x _ _ N _ tau Fx Hsg Ex Hx EX Ht HA HN) as (HA77 & Hd).
(* [|A| >= 2^77] with [0 <= lo < 2^64] puts [a] at least 2^13 away from 0 *)
assert (Ha : (2 ^ 13 <= a \/ a <= - 2 ^ 13)%Z) by lia.
destruct (BN Ha) as (Hs & _ & Ez & Hzh & Hzh1 & Hzl). clear BN.
split; [exact Fx |]. split; [exact Hx |].
split; [rewrite <- EN; apply Z.mod_pos_bound; lia |].
split; [exact Hs |]. split; [lia |]. split; [lia |]. split; [exact Hzl |].
exists N, (a * 2 ^ 64 + lo)%Z, tau, (IZR m * bpow radix2 (be - 1075)).
split; [exact EN |]. split; [exact Ex |]. split; [exact EX |].
split; [exact Ht |]. split; [exact Hd | exact Ez].
Qed.

Theorem fast_reduce_band_big_correct :
  forall x n rh rl rr,
  DyadicTrig.fast_reduce_band_big false x = Some (n, rh, rl, rr) ->
  is_finite x = true /\ 65536 <= Rabs (B2R x) /\ (0 <= n < 8192)%Z /\ Z.land n 2047 = 0%Z /\
  is_finite rh = true /\ is_finite rl = true /\ is_finite rr = true /\ rr = add rh rl /\
  exists N, (N mod 8192 = n)%Z /\
  bpow radix2 (-61) <= Rabs (B2R x - IZR N * (PI / 4096)) <=
    PI / 8192 * (1 + bpow radix2 (-24)) /\
  Rabs (B2R x - IZR N * (PI / 4096) - (B2R rh + B2R rl)) <=
    bpow radix2 (-74) * Rabs (B2R x - IZR N * (PI / 4096)) /\
  Rabs (B2R rl) <= bpow radix2 (-24) * Rabs (B2R rh).
Proof.
intros x n rh rl rr H.
unfold DyadicTrig.fast_reduce_band_big in H.
pose proof (band_big_chain x) as C.
cbv zeta in H, C.
set (b := Z.land (to_bits x) (2 ^ 63 - 1)%Z) in *.
set (be := Z.shiftr b 52) in *.
set (m := Z.lor (Z.land b (2 ^ 52 - 1)) (2 ^ 52)%Z) in *.
set (k := (be - 1011)%Z) in *.
set (p0 := (m * DyadicTrig.big_w k 2)%Z) in *.
set (p1 := (m * DyadicTrig.big_w k 1)%Z) in *.
set (c := (Z.shiftr p0 64 + p1 mod 2 ^ 64)%Z) in *.
set (r1 := (c mod 2 ^ 64)%Z) in *.
set (r2 := ((m * DyadicTrig.big_w k 0 + Z.shiftr p1 64 + Z.shiftr c 64) mod 2 ^ 64)%Z) in *.
set (nn := Z.shiftr ((r2 + 2 ^ 50) mod 2 ^ 64)%Z 51) in *.
set (a0 := Z.lor (Z.shiftl r2 13 mod 2 ^ 64)%Z (Z.shiftr r1 51)) in *.
set (a := if (a0 <? 2 ^ 63)%Z then a0 else (a0 - 2 ^ 64)%Z) in *.
set (lo := Z.lor (Z.shiftl r1 13 mod 2 ^ 64)%Z (Z.shiftr (p0 mod 2 ^ 64) 51)) in *.
set (s := (leading_zeros 64 (Z.lxor a (Z.shiftr a 63)) - 1)%Z) in *.
set (t0 := Z.lor (Z.shiftl a0 s mod 2 ^ 64)%Z (Z.shiftr (Z.shiftr lo 1) (63 - s))) in *.
set (t := if (t0 <? 2 ^ 63)%Z then t0 else (t0 - 2 ^ 64)%Z) in *.
set (v := (Z.shiftl lo s mod 2 ^ 64)%Z) in *.
set (zh := Z.shiftr t 11) in *.
set (zl := Z.lor (Z.shiftl (Z.land t 2047) 42) (Z.shiftr v 22)) in *.
(* The exponent test and the test of [n mod 2048]. *)
destruct (negb ((1039 <=? be) && (be <=? 2046)))%Z eqn:G; [discriminate H |].
apply Bool.negb_false_iff in G.
destruct (negb (Z.land nn 2047 =? 0))%Z eqn:Hn; [discriminate H |].
apply Bool.negb_false_iff, Z.eqb_eq in Hn.
destruct (C G Hn)
  as (Fx & Hx & Hnn & Hs & Hzh2 & Hzh & Hzl & N & A & tau & X & EN & Ex & EX & Ht & Hd & Ez).
clear C.
clearbody zl zh v t t0 s lo a a0 nn r2 r1 c p1 p0 k m be b.
destruct (band_fh zh s Hs Hzh2) as (Ffh & Efh).
destruct (band_fl zl s Hs Hzl) as (Ffl & Efl).
set (fh := mul (DyadicTrig.of_i64 zh) (from_bits (Z.shiftl (970 - s) 52))) in *.
set (fl := mul (DyadicTrig.of_i64 zl) (from_bits (Z.shiftl (917 - s) 52))) in *.
clearbody fh fl.
(* The sign: [fh], [fl] and [N] change sign with [x]. *)
destruct (lt x zero) eqn:S; cbv beta iota in H, Ex.
- revert H.
  destruct (DyadicTrig.fast_mul false _ _ _ _) as (p, q) eqn:M.
  cbv beta iota.
  intro H. apply some_eq in H.
  apply pair_equal_spec in H as (H & Er).
  apply pair_equal_spec in H as (H & Eql).
  apply pair_equal_spec in H as (En & Ep).
  subst n rh rl rr.
  assert (Hs1 : - 1 = 1 \/ - 1 = - 1) by (right; reflexivity).
  assert (EN' : IZR (- N) = - 1 * IZR N) by (rewrite opp_IZR; ring).
  assert (Ffo : is_finite (opp fh) = true)
    by (unfold opp; rewrite is_finite_Bopp; exact Ffh).
  assert (Flo : is_finite (opp fl) = true)
    by (unfold opp; rewrite is_finite_Bopp; exact Ffl).
  assert (Efo : B2R (opp fh) = - 1 * (IZR zh * bpow radix2 (-53 - s)))
    by (unfold opp; rewrite B2R_Bopp, Efh; ring).
  assert (Elo : B2R (opp fl) = - 1 * (IZR zl * bpow radix2 (-106 - s)))
    by (unfold opp; rewrite B2R_Bopp, Efl; ring).
  destruct (band_tail _ X N A tau s zh zl (B2R x) (IZR (- N)) _ _ p q Hs1 Ex EN' EX Ht Hd
              Hs Ez Hzh Hzl Ffo Flo Efo Elo M)
    as (Frh & Frl & Frr & E1 & E2 & Hrl).
  pose proof (big_neg_mod N nn EN) as EN2.
  split; [exact Fx |]. split; [exact Hx |].
  split; [rewrite <- EN2; apply Z.mod_pos_bound; lia |].
  split.
  { (* [nn mod 2048 = 0] gives [(-nn) mod 2048 = 0]. *)
    rewrite <- Z.land_assoc. change (Z.land 8191 2047) with 2047%Z.
    change 2047%Z with (Z.ones 11) in Hn |- *.
    rewrite Z.land_ones in Hn |- * by lia.
    apply Z_mod_zero_opp_full. exact Hn. }
  split; [exact Frh |]. split; [exact Frl |]. split; [exact Frr |].
  split; [reflexivity |].
  exists (- N)%Z.
  split; [exact EN2 |]. split; [exact E1 |]. split; [exact E2 | exact Hrl].
- revert H.
  destruct (DyadicTrig.fast_mul false _ _ _ _) as (p, q) eqn:M.
  cbv beta iota.
  intro H. apply some_eq in H.
  apply pair_equal_spec in H as (H & Er).
  apply pair_equal_spec in H as (H & Eql).
  apply pair_equal_spec in H as (En & Ep).
  subst n rh rl rr.
  assert (Hs1 : 1 = 1 \/ 1 = - 1) by (left; reflexivity).
  assert (EN' : IZR N = 1 * IZR N) by ring.
  assert (Efo : B2R fh = 1 * (IZR zh * bpow radix2 (-53 - s))) by (rewrite Efh; ring).
  assert (Elo : B2R fl = 1 * (IZR zl * bpow radix2 (-106 - s))) by (rewrite Efl; ring).
  destruct (band_tail _ X N A tau s zh zl (B2R x) (IZR N) _ _ p q Hs1 Ex EN' EX Ht Hd
              Hs Ez Hzh Hzl Ffh Ffl Efo Elo M)
    as (Frh & Frl & Frr & E1 & E2 & Hrl).
  split; [exact Fx |]. split; [exact Hx |]. split; [exact Hnn |]. split; [exact Hn |].
  split; [exact Frh |]. split; [exact Frl |]. split; [exact Frr |].
  split; [reflexivity |].
  exists N.
  split; [exact EN |]. split; [exact E1 |]. split; [exact E2 | exact Hrl].
Qed.

Theorem fast_reduce_band_big_fma :
  forall x, DyadicTrig.fast_reduce_band_big true x = DyadicTrig.fast_reduce_band_big false x.
Proof.
intros x.
unfold DyadicTrig.fast_reduce_band_big.
pose proof (band_big_chain x) as C.
cbv zeta. cbv zeta in C.
set (b := Z.land (to_bits x) (2 ^ 63 - 1)%Z) in *.
set (be := Z.shiftr b 52) in *.
set (m := Z.lor (Z.land b (2 ^ 52 - 1)) (2 ^ 52)%Z) in *.
set (k := (be - 1011)%Z) in *.
set (p0 := (m * DyadicTrig.big_w k 2)%Z) in *.
set (p1 := (m * DyadicTrig.big_w k 1)%Z) in *.
set (c := (Z.shiftr p0 64 + p1 mod 2 ^ 64)%Z) in *.
set (r1 := (c mod 2 ^ 64)%Z) in *.
set (r2 := ((m * DyadicTrig.big_w k 0 + Z.shiftr p1 64 + Z.shiftr c 64) mod 2 ^ 64)%Z) in *.
set (nn := Z.shiftr ((r2 + 2 ^ 50) mod 2 ^ 64)%Z 51) in *.
set (a0 := Z.lor (Z.shiftl r2 13 mod 2 ^ 64)%Z (Z.shiftr r1 51)) in *.
set (a := if (a0 <? 2 ^ 63)%Z then a0 else (a0 - 2 ^ 64)%Z) in *.
set (lo := Z.lor (Z.shiftl r1 13 mod 2 ^ 64)%Z (Z.shiftr (p0 mod 2 ^ 64) 51)) in *.
set (s := (leading_zeros 64 (Z.lxor a (Z.shiftr a 63)) - 1)%Z) in *.
set (t0 := Z.lor (Z.shiftl a0 s mod 2 ^ 64)%Z (Z.shiftr (Z.shiftr lo 1) (63 - s))) in *.
set (t := if (t0 <? 2 ^ 63)%Z then t0 else (t0 - 2 ^ 64)%Z) in *.
set (v := (Z.shiftl lo s mod 2 ^ 64)%Z) in *.
set (zh := Z.shiftr t 11) in *.
set (zl := Z.lor (Z.shiftl (Z.land t 2047) 42) (Z.shiftr v 22)) in *.
(* The two tests return [None] on both sides. *)
destruct (negb ((1039 <=? be) && (be <=? 2046)))%Z eqn:G; cbv beta iota; [reflexivity |].
apply Bool.negb_false_iff in G.
destruct (negb (Z.land nn 2047 =? 0))%Z eqn:Hn; cbv beta iota; [reflexivity |].
apply Bool.negb_false_iff, Z.eqb_eq in Hn.
destruct (C G Hn) as (_ & _ & _ & Hs & Hzh2 & Hzh & Hzl & _). clear C.
clearbody zl zh v t t0 s lo a a0 nn r2 r1 c p1 p0 k m be b.
destruct (band_fh zh s Hs Hzh2) as (Ffh & Efh).
destruct (band_fl zl s Hs Hzl) as (Ffl & Efl).
set (fh := mul (DyadicTrig.of_i64 zh) (from_bits (Z.shiftl (970 - s) 52))) in *.
set (fl := mul (DyadicTrig.of_i64 zl) (from_bits (Z.shiftl (917 - s) 52))) in *.
clearbody fh fl.
(* [band_f_bounds] with [sg = 1] bounds [|fh|], also for [opp fh] *)
assert (Hs1 : 1 = 1 \/ 1 = - 1) by (left; reflexivity).
assert (Efh1 : B2R fh = 1 * (IZR zh * bpow radix2 (-53 - s))) by (rewrite Efh; ring).
assert (Efl1 : B2R fl = 1 * (IZR zl * bpow radix2 (-106 - s))) by (rewrite Efl; ring).
destruct (band_f_bounds 1 zh zl s fh fl Hs1 Hs Hzh Hzl Efh1 Efl1) as (HS & Bfh & _).
destruct (lt x zero); cbv beta iota.
- rewrite (band_mul_fma _ (opp fh) (opp fl) HS).
  + reflexivity.
  + unfold opp. rewrite is_finite_Bopp. exact Ffh.
  + unfold opp. rewrite B2R_Bopp, Rabs_Ropp. exact Bfh.
- rewrite (band_mul_fma _ fh fl HS Ffh Bfh). reflexivity.
Qed.
