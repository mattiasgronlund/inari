(** * The integer part and the error of the reduction of large arguments of the fast paths of [sin], [cos] and [tan]

    For [m] in [[2^52, 2^53)] and [be] in [[1039, 2046]], the integers
    of [DyadicTrig.fast_reduce_big] give an integer [N] with [N mod 8192 =
    n] and the fraction [m 2^(be - 1075) / (π/4096) - N] as [zh 2^-53 + zl
    2^-106] up to less than [2^-105] ([big_int]); [x - N π/4096] is then
    within [2^-90] of [rh + rl] and at most [π/8192 (1 + 2^-24)] in
    magnitude, for either sign of [x] ([big_err]), and the [n] of [-x] is
    [(-n) & 8191] ([big_neg_mod]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core.
From Inari Require Import Model KahanMcDonald FastTrigBigInt.

Open Scope R_scope.

Lemma big_int :
  forall m be, (2 ^ 52 <= m < 2 ^ 53)%Z -> (1039 <= be <= 2046)%Z ->
  let k := (be - 1011)%Z in
  let p0 := (m * DyadicTrig.big_w k 2)%Z in
  let p1 := (m * DyadicTrig.big_w k 1)%Z in
  let c := (Z.shiftr p0 64 + p1 mod 2 ^ 64)%Z in
  let r1 := (c mod 2 ^ 64)%Z in
  let r2 := ((m * DyadicTrig.big_w k 0 + Z.shiftr p1 64 + Z.shiftr c 64) mod 2 ^ 64)%Z in
  let n := Z.shiftr ((r2 + 2 ^ 50) mod 2 ^ 64)%Z 51 in
  let a0 := Z.lor (Z.shiftl r2 13 mod 2 ^ 64)%Z (Z.shiftr r1 51) in
  let a := if (a0 <? 2 ^ 63)%Z then a0 else (a0 - 2 ^ 64)%Z in
  (- 2 ^ 52 <= Z.shiftr a 11 < 2 ^ 52)%Z /\
  (0 <= Z.land (Z.shiftr r1 9) (2 ^ 53 - 1) < 2 ^ 53)%Z /\
  exists (N : Z) (t : R),
  (N mod 8192 = n)%Z /\
  IZR m * bpow radix2 (be - 1075) / (PI / 4096) =
    IZR N + IZR (Z.shiftr a 11) * bpow radix2 (-53) +
    IZR (Z.land (Z.shiftr r1 9) (2 ^ 53 - 1))%Z * bpow radix2 (-106) + t /\
  0 <= t < bpow radix2 (-105).
Proof.
intros m be Hm Hbe k p0 p1 c r1 r2 n a0 a.
assert (Hk : (28 <= k <= 1035)%Z) by (unfold k; lia).
assert (Hsh : (1088 - k = 2099 - be)%Z) by (unfold k; lia).
clearbody k.
destruct (big_w_window k Hk) as [Hw0 [Hw1 [Hw2 HW]]].
rewrite Hsh in HW.
(* [big_frac] at [e = be - 1075] reads the same window: [1024 - e = 1088 - k] *)
destruct (big_frac m (be - 1075)) as [K [t' [HF Ht']]]; [lia | lia |].
replace (1024 - (be - 1075))%Z with (2099 - be)%Z in HF by lia.
set (W := (Z.shiftr inv2pi_val (2099 - be) mod 2 ^ 192)%Z) in HW, HF.
set (R := ((m * W) mod 2 ^ 192)%Z) in HF.
assert (HRb : (0 <= R < 2 ^ 192)%Z) by (apply Z.mod_pos_bound; lia).
(* the two top limbs of [R] are [r2] and [r1] *)
assert (Hm0 : (0 <= m < 2 ^ 53)%Z) by lia.
pose proof (big_prod m _ _ _ Hm0 Hw0 Hw1 Hw2) as HP.
cbv zeta in HP. rewrite HW in HP. destruct HP as [HP1 HP2].
assert (Er1 : r1 = (Z.shiftr R 64 mod 2 ^ 64)%Z) by exact HP1.
assert (Er2 : r2 = Z.shiftr R 128) by exact HP2.
clear HP1 HP2.
clearbody R W.
pose proof (big_split R HRb) as HS. cbv zeta in HS.
rewrite <- Er2, <- Er1 in HS.
destruct HS as [HS1 [HS2 [HS3 HS4]]].
assert (Hn : n = (Z.shiftr (R + 2 ^ 178) 179 mod 8192)%Z) by exact HS1.
assert (HR : (R = Z.shiftr (R + 2 ^ 178) 179 * 2 ^ 179 + Z.shiftr a 11 * 2 ^ 126 +
                  Z.land (Z.shiftr r1 9) (2 ^ 53 - 1) * 2 ^ 73 + R mod 2 ^ 73)%Z)
  by exact HS2.
assert (Hh : (- 2 ^ 52 <= Z.shiftr a 11 < 2 ^ 52)%Z) by exact HS3.
clear HS1 HS2 HS3.
clearbody n a a0 r1 r2 c p1 p0.
assert (Hl : (0 <= R mod 2 ^ 73 < 2 ^ 73)%Z) by (apply Z.mod_pos_bound; lia).
set (N0 := Z.shiftr (R + 2 ^ 178) 179) in *.
set (fh := Z.shiftr a 11) in *.
set (fl := Z.land (Z.shiftr r1 9) (2 ^ 53 - 1)) in *.
set (Rl := (R mod 2 ^ 73)%Z) in *.
clearbody N0 fh fl Rl.
split; [exact Hh |]. split; [exact HS4 |].
(* [N = N0 + 8192 K]; the bits of [R] below [2^73] go into [t] *)
exists (N0 + K * 8192)%Z, (IZR Rl * bpow radix2 (-179) + t').
split; [| split].
- rewrite Z.mod_add by lia. symmetry. exact Hn.
- rewrite HF.
  assert (HRR : IZR R = IZR N0 * bpow radix2 179 + IZR fh * bpow radix2 126 +
                        IZR fl * bpow radix2 73 + IZR Rl).
  { rewrite HR at 1. rewrite !plus_IZR, !mult_IZR, !km_IZR_pow2 by lia. reflexivity. }
  assert (E1 : bpow radix2 179 * bpow radix2 (-179) = 1)
    by (rewrite <- bpow_plus; reflexivity).
  assert (E2 : bpow radix2 126 * bpow radix2 (-179) = bpow radix2 (-53))
    by (rewrite <- bpow_plus; reflexivity).
  assert (E3 : bpow radix2 73 * bpow radix2 (-179) = bpow radix2 (-106))
    by (rewrite <- bpow_plus; reflexivity).
  rewrite HRR, plus_IZR, mult_IZR.
  transitivity (8192 * IZR K + IZR N0 * (bpow radix2 179 * bpow radix2 (-179)) +
                IZR fh * (bpow radix2 126 * bpow radix2 (-179)) +
                IZR fl * (bpow radix2 73 * bpow radix2 (-179)) +
                IZR Rl * bpow radix2 (-179) + t'); [ring |].
  rewrite E1, E2, E3. ring.
- (* [t <= (2^73 - 1) 2^-179 + m 2^-179 < 2^-106 + 2^-126] *)
  assert (HmR : IZR m < bpow radix2 53)
    by (rewrite <- km_IZR_pow2 by lia; apply IZR_lt; lia).
  assert (HlR : 0 <= IZR Rl <= bpow radix2 73 - 1).
  { rewrite <- km_IZR_pow2 by lia. split; [apply IZR_le; lia |].
    rewrite <- minus_IZR. apply IZR_le. lia. }
  destruct Ht' as [Ht0 Ht1].
  clear - HmR HlR Ht0 Ht1.
  cbn [bpow radix_val radix2] in *.
  split; lra.
Qed.

Lemma big_err :
  forall s X N h l t rh rl,
  (s = 1 \/ s = - 1) ->
  X / (PI / 4096) = N + h + l + t ->
  - / 2 <= h <= / 2 - bpow radix2 (-53) ->
  0 <= l < bpow radix2 (-53) ->
  0 <= t < bpow radix2 (-105) ->
  Rabs ((s * h + s * l) * (PI / 4096) - (rh + rl)) <= bpow radix2 (-100) ->
  Rabs (s * X - s * N * (PI / 4096) - (rh + rl)) <= bpow radix2 (-90) /\
  Rabs (s * X - s * N * (PI / 4096)) <= PI / 8192 * (1 + bpow radix2 (-24)).
Proof.
intros s X N h l t rh rl Hs HX Hh Hl Ht Hr.
pose proof PI_RGT_0 as HPI0. pose proof PI_4 as HPI4.
set (u := PI / 4096) in *.
assert (Hu : 0 < u) by (unfold u; lra).
assert (HPu : PI = 4096 * u) by (unfold u; field).
(* [s X - s N u = s (h + l + t) u] *)
assert (EX : X = (N + h + l + t) * u).
{ rewrite <- HX. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. ring. }
clear HX.
(* the products with [u], for [lra] *)
assert (Htu : 0 <= t * u <= bpow radix2 (-105) * u).
{ split; [apply Rmult_le_pos; lra | apply Rmult_le_compat_r; lra]. }
assert (Hlu : 0 <= l * u <= bpow radix2 (-53) * u).
{ split; [apply Rmult_le_pos; lra | apply Rmult_le_compat_r; lra]. }
assert (Hhu : - / 2 * u <= h * u <= (/ 2 - bpow radix2 (-53)) * u).
{ split; apply Rmult_le_compat_r; lra. }
apply Rabs_le_inv in Hr.
clearbody u.
clear Hh Hl Ht.
cbn [bpow radix_val radix2] in *.
destruct Hs as [-> | ->]; rewrite EX; split; apply Rabs_le; split; lra.
Qed.

Lemma big_neg_mod :
  forall N n, (N mod 8192 = n)%Z -> ((- N) mod 8192 = Z.land (- n) 8191)%Z.
Proof.
intros N n <-.
(* [Z.land v 8191 = v mod 2^13], also for negative [v] *)
change 8191%Z with (Z.ones 13).
rewrite Z.land_ones by lia.
change (2 ^ 13)%Z with 8192%Z.
rewrite <- (Z.sub_0_l N), <- (Z.sub_0_l (N mod 8192)).
symmetry. apply Zminus_mod_idemp_r.
Qed.
