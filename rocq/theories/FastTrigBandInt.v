(** * The integers of the reduction of the fast paths of [sin], [cos] and [tan] near the multiples of π/2 above 2^16

    [DyadicTrig.fast_reduce_band_big] of [Model.v] reads the 192 bits of
    the window product of [fast_reduce_big] ([FastTrigBigInt.v]) as [n],
    the 64 bits [a] below it and the 64 bits [lo] below [a]
    ([band_split]). For [m] in [[2^52, 2^53)] and [be] in [[1039, 2046]],
    they give an integer [N] with [N mod 8192 = n] and [m 2^(be - 1075) /
    (π/4096) = N + A 2^-128 + τ], with [A = a 2^64 + lo] and τ in [[0, 5
    2^-128)] ([band_int]). Where [a] is at least 2^13 in magnitude, the
    shift [s] of [fast_reduce_band_big] is at most 50, and [zh 2^53 + zl]
    is [A 2^s / 2^22] rounded down, with [|zh|] in [[2^51, 2^52]]
    ([band_norm]). [FastTrigBandBig.v] uses them. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core.
From Inari Require Import Model Limbs KahanMcDonald FastTrigBigInt.

Open Scope R_scope.

(** [A = a 2^64 + lo], where [a] is the [i64] of the bits [a0] and is at
    least 2^13 in magnitude, times [2^s] for the [s] of
    [fast_reduce_band_big], which is at most 50, is [t 2^64 + v], and
    [zh 2^53 + zl] is it over 2^22 rounded down, with [|zh|] in [[2^51,
    2^52]]: [s] moves the top bit of [a] (of [-a - 1] where [a] is
    negative) to bit 62. *)
Lemma band_norm :
  forall a0 lo, (0 <= a0 < 2 ^ 64)%Z -> (0 <= lo < 2 ^ 64)%Z ->
  let a := if (a0 <? 2 ^ 63)%Z then a0 else (a0 - 2 ^ 64)%Z in
  (2 ^ 13 <= a \/ a <= - 2 ^ 13)%Z ->
  let s := (leading_zeros 64 (Z.lxor a (Z.shiftr a 63)) - 1)%Z in
  let t0 := Z.lor (Z.shiftl a0 s mod 2 ^ 64)%Z (Z.shiftr (Z.shiftr lo 1) (63 - s)) in
  let t := if (t0 <? 2 ^ 63)%Z then t0 else (t0 - 2 ^ 64)%Z in
  let v := (Z.shiftl lo s mod 2 ^ 64)%Z in
  let zh := Z.shiftr t 11 in
  let zl := Z.lor (Z.shiftl (Z.land t 2047) 42) (Z.shiftr v 22) in
  (0 <= s <= 50 /\ (a * 2 ^ 64 + lo) * 2 ^ s = t * 2 ^ 64 + v /\
   zh * 2 ^ 53 + zl = (a * 2 ^ 64 + lo) * 2 ^ s / 2 ^ 22 /\
   - 2 ^ 52 <= zh < 2 ^ 52 /\ 2 ^ 51 <= Z.abs zh /\ 0 <= zl < 2 ^ 53)%Z.
Proof.
intros a0 lo Ha0 Hlo a Ha s t0 t v zh zl.
assert (Ea : a = if (a0 <? 2 ^ 63)%Z then a0 else (a0 - 2 ^ 64)%Z) by reflexivity.
assert (Es : s = (leading_zeros 64 (Z.lxor a (Z.shiftr a 63)) - 1)%Z) by reflexivity.
assert (Et0 : t0 = Z.lor (Z.shiftl a0 s mod 2 ^ 64)%Z (Z.shiftr (Z.shiftr lo 1) (63 - s)))
  by reflexivity.
assert (Et : t = if (t0 <? 2 ^ 63)%Z then t0 else (t0 - 2 ^ 64)%Z) by reflexivity.
assert (Ev : v = (Z.shiftl lo s mod 2 ^ 64)%Z) by reflexivity.
assert (Ezh : zh = Z.shiftr t 11) by reflexivity.
assert (Ezl : zl = Z.lor (Z.shiftl (Z.land t 2047) 42) (Z.shiftr v 22)) by reflexivity.
clearbody a s t0 t v zh zl.
(* [a] is [a0] read as an [i64]: [a0 = a + c 2^64] *)
assert (Hac : exists c, (a0 = a + c * 2 ^ 64 /\ - 2 ^ 63 <= a < 2 ^ 63)%Z).
{ rewrite Ea. destruct (Z.ltb_spec a0 (2 ^ 63)); [exists 0%Z | exists 1%Z]; lia. }
destruct Hac as [c [Ec Hab]].
clear Ea.
(* [a ^ (a >> 63)] is [a] for [a >= 0] and [-a - 1] for [a < 0] *)
set (a' := Z.lxor a (Z.shiftr a 63)) in Es.
assert (Ea' : ((0 <= a /\ a' = a) \/ (a < 0 /\ a' = - a - 1))%Z).
{ unfold a'. destruct (Z.leb_spec 0 a) as [H0 | H0].
  - left. split; [exact H0 |].
    rewrite Z.shiftr_div_pow2, Z.div_small by lia. apply Z.lxor_0_r.
  - right. split; [exact H0 |].
    assert (Hm1 : Z.shiftr a 63 = (- 1)%Z).
    { rewrite Z.shiftr_div_pow2 by lia. symmetry.
      apply (Z.div_unique _ _ _ (a + 2 ^ 63)); [left; lia | lia]. }
    rewrite Hm1, Z.lxor_m1_r, Z.lnot_eq_pred_opp. lia. }
clearbody a'.
(* [s = 62 - L] with [2^L <= a' < 2^(L + 1)] and [L] in [[12, 62]] *)
assert (Ha'p : (2 ^ 12 <= a' < 2 ^ 63)%Z) by lia.
assert (Hl0 : (0 < a')%Z) by lia.
unfold leading_zeros in Es.
destruct (Z.eqb_spec a' 0) as [H0 | _]; [lia |].
set (L := Z.log2 a') in Es.
assert (HL : (2 ^ L <= a' < 2 ^ Z.succ L)%Z) by (apply Z.log2_spec; exact Hl0).
assert (HL0 : (0 <= L)%Z) by (apply Z.log2_nonneg).
assert (HLb : (12 <= L <= 62)%Z).
{ split.
  - destruct (Z.le_gt_cases 12 L) as [H | H]; [exact H |].
    assert (H2 : (2 ^ Z.succ L <= 2 ^ 12)%Z) by (apply Z.pow_le_mono_r; lia). lia.
  - destruct (Z.le_gt_cases L 62) as [H | H]; [exact H |].
    assert (H2 : (2 ^ 63 <= 2 ^ L)%Z) by (apply Z.pow_le_mono_r; lia). lia. }
clearbody L.
assert (Hs : (0 <= s <= 50)%Z) by lia.
split; [exact Hs |].
(* [P = 2^s], [Q = 2^(64 - s)], [X = 2^L] *)
assert (EL : L = (62 - s)%Z) by lia.
subst L.
set (P := (2 ^ s)%Z).
set (Q := (2 ^ (64 - s))%Z).
set (X := (2 ^ (62 - s))%Z) in HL.
assert (HPQ : (P * Q = 2 ^ 64)%Z)
  by (unfold P, Q; rewrite <- Z.pow_add_r by lia; f_equal; lia).
assert (HXP : (X * P = 2 ^ 62)%Z)
  by (unfold P, X; rewrite <- Z.pow_add_r by lia; f_equal; lia).
assert (HX2 : (2 ^ Z.succ (62 - s) = 2 * X)%Z)
  by (unfold X; rewrite Z.pow_succ_r by lia; ring).
rewrite HX2 in HL.
assert (HP : (1 <= P)%Z) by (unfold P; apply (Z.pow_le_mono_r 2 0 s); lia).
assert (HQ : (1 <= Q)%Z) by (unfold Q; apply (Z.pow_le_mono_r 2 0 (64 - s)); lia).
(* [a' P] in [[2^62, 2^63 - P]] *)
assert (HaP : (2 ^ 62 <= a' * P <= 2 ^ 63 - P)%Z).
{ split.
  - rewrite <- HXP. apply Z.mul_le_mono_nonneg_r; lia.
  - assert (H : (a' * P <= (2 * X - 1) * P)%Z) by (apply Z.mul_le_mono_nonneg_r; lia).
    lia. }
(* [t0 = (a0 mod Q) P + lo / Q] *)
assert (Elq : Z.shiftr (Z.shiftr lo 1) (63 - s) = (lo / Q)%Z).
{ rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
  unfold Q. f_equal. rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
assert (Bl : (0 <= lo / Q < P)%Z).
{ split; [apply Z.div_pos; lia |]. apply Z.div_lt_upper_bound; lia. }
assert (Ea0P : (Z.shiftl a0 s mod 2 ^ 64 = (a0 mod Q) * P)%Z).
{ rewrite Z.shiftl_mul_pow2 by lia. fold P. rewrite <- HPQ, (Z.mul_comm P Q).
  apply Z.mul_mod_distr_r; lia. }
rewrite Elq, Ea0P in Et0. unfold P in Et0.
rewrite lor_low in Et0 by (fold P; lia). fold P in Et0.
(* [t0 = T + j 2^64] for [T = a P + lo / Q], which is in [[-2^63, 2^63)],
   so [t], [t0] read as an [i64], is [T] *)
assert (Bm : (0 <= a0 mod Q < Q)%Z) by (apply Z.mod_pos_bound; lia).
assert (Em : (a0 mod Q * P = a * P + (c * P - a0 / Q) * 2 ^ 64)%Z).
{ pose proof (Z.div_mod a0 Q ltac:(lia)) as D.
  replace (a0 mod Q)%Z with (a0 - Q * (a0 / Q))%Z by lia.
  set (d := (a0 / Q)%Z). clearbody d. rewrite Ec, <- HPQ. ring. }
assert (Bm' : (a0 mod Q * P <= 2 ^ 64 - P)%Z).
{ assert (H : (a0 mod Q * P <= (Q - 1) * P)%Z) by (apply Z.mul_le_mono_nonneg_r; lia).
  lia. }
assert (Bm0 : (0 <= a0 mod Q * P)%Z) by lia.
assert (HT : ((2 ^ 62 <= a * P + lo / Q < 2 ^ 63) \/
              (- 2 ^ 63 <= a * P + lo / Q <= - 2 ^ 62 - 1))%Z).
{ destruct Ea' as [[H0 ->] | [H0 Ha1]].
  - left. lia.
  - right. assert (E : (a * P = - (a' * P) - P)%Z) by (rewrite Ha1; ring). lia. }
assert (Ht : (t = a * P + lo / Q)%Z).
{ rewrite Et. set (j := (c * P - a0 / Q)%Z) in Em.
  destruct (Z.ltb_spec t0 (2 ^ 63)); lia. }
clear Et Et0 Em Bm Bm' Bm0 Ec.
(* [v = (lo mod Q) P] and [A 2^s = t 2^64 + v] *)
assert (Ev' : (v = lo mod Q * P)%Z).
{ rewrite Ev, Z.shiftl_mul_pow2 by lia. fold P. rewrite <- HPQ, (Z.mul_comm P Q).
  apply Z.mul_mod_distr_r; lia. }
assert (Bv : (0 <= v < 2 ^ 64)%Z) by (rewrite Ev; apply Z.mod_pos_bound; lia).
assert (Elo : (lo = Q * (lo / Q) + lo mod Q)%Z) by (apply Z.div_mod; lia).
assert (EA : ((a * 2 ^ 64 + lo) * P = t * 2 ^ 64 + v)%Z).
{ rewrite Ht, Ev'. set (dl := (lo / Q)%Z) in *. set (ml := (lo mod Q)%Z) in *.
  clearbody dl ml. rewrite Elo, <- HPQ. ring. }
split; [exact EA |].
(* [zh] and [zl] are the bits of [t 2^42 + v / 2^22] above and below bit 53 *)
assert (Ezh' : (zh = t / 2 ^ 11)%Z) by (rewrite Ezh; apply Z.shiftr_div_pow2; lia).
assert (Bv22 : (0 <= v / 2 ^ 22 < 2 ^ 42)%Z).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
assert (Ezl' : (zl = t mod 2 ^ 11 * 2 ^ 42 + v / 2 ^ 22)%Z).
{ rewrite Ezl. change 2047%Z with (Z.ones 11).
  rewrite Z.land_ones, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  apply lor_low; lia. }
assert (Ediv : ((t * 2 ^ 64 + v) / 2 ^ 22 = t * 2 ^ 42 + v / 2 ^ 22)%Z).
{ replace (t * 2 ^ 64)%Z with (t * 2 ^ 42 * 2 ^ 22)%Z by ring.
  apply Z.div_add_l; lia. }
rewrite EA, Ediv, Ezh', Ezl'.
pose proof (Z.div_mod t (2 ^ 11) ltac:(lia)) as Dt.
pose proof (Z.mod_pos_bound t (2 ^ 11) ltac:(lia)) as Bt.
set (q := (t / 2 ^ 11)%Z) in *. set (r := (t mod 2 ^ 11)%Z) in *.
clearbody q r.
split; [lia |].
lia.
Qed.

(** [x / 2^a] split at bit [b] (as the local [dig] of [FastTrigBigInt.v]) *)
Local Lemma band_dig :
  forall x a b c, (0 <= a)%Z -> (0 <= b)%Z -> c = (a + b)%Z ->
  (x / 2 ^ a = (x / 2 ^ a) mod 2 ^ b + 2 ^ b * (x / 2 ^ c))%Z.
Proof.
intros x a b c Ha Hb ->.
assert (Hb2 : (2 ^ b <> 0)%Z) by (apply Z.pow_nonzero; lia).
rewrite Z.pow_add_r, <- Z.div_div by (try apply Z.pow_pos_nonneg; lia).
pose proof (Z.div_mod (x / 2 ^ a) (2 ^ b) Hb2). lia.
Qed.

(** The 192 bits [R] of the window product, as [big_split] reads them,
    and also the 64 bits [lo] below [a]: [R] is [N0 2^179 + (a 2^64 +
    lo) 2^51] plus its 51 low bits, where [a] reads bits 115 to 178 as an
    [i64] and [lo] is bits 51 to 114, from [r1] and the low limb [R mod
    2^64]. *)
Lemma band_split :
  forall R, (0 <= R < 2 ^ 192)%Z ->
  let r2 := Z.shiftr R 128 in
  let r1 := (Z.shiftr R 64 mod 2 ^ 64)%Z in
  let a0 := Z.lor (Z.shiftl r2 13 mod 2 ^ 64) (Z.shiftr r1 51) in
  let a := if (a0 <? 2 ^ 63)%Z then a0 else (a0 - 2 ^ 64)%Z in
  let lo := Z.lor (Z.shiftl r1 13 mod 2 ^ 64) (Z.shiftr (R mod 2 ^ 64) 51) in
  let N0 := Z.shiftr (R + 2 ^ 178) 179 in
  (Z.shiftr ((r2 + 2 ^ 50) mod 2 ^ 64) 51 = N0 mod 8192 /\
   R = N0 * 2 ^ 179 + (a * 2 ^ 64 + lo) * 2 ^ 51 + R mod 2 ^ 51 /\
   0 <= a0 < 2 ^ 64 /\ 0 <= lo < 2 ^ 64)%Z.
Proof.
intros R HR r2 r1 a0 a lo N0.
assert (Er2 : r2 = (R / 2 ^ 128)%Z)
  by (change r2 with (Z.shiftr R 128); apply Z.shiftr_div_pow2; lia).
assert (Er1 : r1 = ((R / 2 ^ 64) mod 2 ^ 64)%Z)
  by (change r1 with (Z.shiftr R 64 mod 2 ^ 64)%Z; rewrite Z.shiftr_div_pow2 by lia;
      reflexivity).
assert (Ea0 : a0 = Z.lor ((r2 * 2 ^ 13) mod 2 ^ 64) (r1 / 2 ^ 51)).
{ change a0 with (Z.lor (Z.shiftl r2 13 mod 2 ^ 64) (Z.shiftr r1 51)).
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. }
assert (Ea : a = if (a0 <? 2 ^ 63)%Z then a0 else (a0 - 2 ^ 64)%Z) by reflexivity.
assert (Elo : lo = Z.lor ((r1 * 2 ^ 13) mod 2 ^ 64) ((R mod 2 ^ 64) / 2 ^ 51)).
{ change lo with (Z.lor (Z.shiftl r1 13 mod 2 ^ 64) (Z.shiftr (R mod 2 ^ 64) 51)).
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. }
assert (EN0 : N0 = ((R + 2 ^ 178) / 2 ^ 179)%Z)
  by (change N0 with (Z.shiftr (R + 2 ^ 178) 179); apply Z.shiftr_div_pow2; lia).
clearbody r2 r1 a0 a lo N0.
rewrite !Z.shiftr_div_pow2 by lia.
(* The fields of [R] at bits 0, 51, 64, 115, 128, 178 and 179 *)
pose proof (Z.div_mod R (2 ^ 51) ltac:(lia)) as D0.
pose proof (band_dig R 51 13 64 ltac:(lia) ltac:(lia) eq_refl) as D1.
pose proof (band_dig R 64 51 115 ltac:(lia) ltac:(lia) eq_refl) as D2.
pose proof (band_dig R 115 13 128 ltac:(lia) ltac:(lia) eq_refl) as D3.
pose proof (band_dig R 128 50 178 ltac:(lia) ltac:(lia) eq_refl) as D4.
pose proof (band_dig R 178 1 179 ltac:(lia) ltac:(lia) eq_refl) as D5.
pose proof (Z.mod_pos_bound R (2 ^ 51) ltac:(lia)) as B0.
pose proof (Z.mod_pos_bound (R / 2 ^ 51) (2 ^ 13) ltac:(lia)) as B1.
pose proof (Z.mod_pos_bound (R / 2 ^ 64) (2 ^ 51) ltac:(lia)) as B2.
pose proof (Z.mod_pos_bound (R / 2 ^ 115) (2 ^ 13) ltac:(lia)) as B3.
pose proof (Z.mod_pos_bound (R / 2 ^ 128) (2 ^ 50) ltac:(lia)) as B5.
pose proof (Z.mod_pos_bound (R / 2 ^ 178) (2 ^ 1) ltac:(lia)) as B6.
assert (B7 : (0 <= R / 2 ^ 179 < 2 ^ 13)%Z).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
set (g0 := (R mod 2 ^ 51)%Z) in *.
set (g1 := ((R / 2 ^ 51) mod 2 ^ 13)%Z) in *.
set (g2 := ((R / 2 ^ 64) mod 2 ^ 51)%Z) in *.
set (g3 := ((R / 2 ^ 115) mod 2 ^ 13)%Z) in *.
set (g5 := ((R / 2 ^ 128) mod 2 ^ 50)%Z) in *.
set (g6 := ((R / 2 ^ 178) mod 2 ^ 1)%Z) in *.
set (g7 := (R / 2 ^ 179)%Z) in *.
clearbody g0 g1 g2 g3 g5 g6 g7.
(* [r2], [r1], [R mod 2^64], [a0], [a], [lo] and [N0] in fields *)
assert (Er2' : (r2 = g5 + 2 ^ 50 * g6 + 2 ^ 51 * g7)%Z) by lia.
assert (Er1' : (r1 = g2 + 2 ^ 51 * g3)%Z).
{ rewrite Er1. symmetry. apply (Z.mod_unique _ _ (R / 2 ^ 128)); [left; lia | lia]. }
assert (Er0 : (R mod 2 ^ 64 = g0 + 2 ^ 51 * g1)%Z).
{ symmetry. apply (Z.mod_unique _ _ (R / 2 ^ 64)); [left; lia | lia]. }
assert (Ex : ((r2 * 2 ^ 13) mod 2 ^ 64 = (g5 + 2 ^ 50 * g6) * 2 ^ 13)%Z).
{ symmetry. apply (Z.mod_unique _ _ g7); [left; lia | lia]. }
assert (Ey : (r1 / 2 ^ 51 = g3)%Z).
{ symmetry. apply (Z.div_unique _ _ _ g2); [left; lia | lia]. }
assert (Ea0' : (a0 = (g5 + 2 ^ 50 * g6) * 2 ^ 13 + g3)%Z).
{ rewrite Ea0, Ex, Ey. apply lor_low; lia. }
assert (Ea' : (a = g3 + 2 ^ 13 * g5 - 2 ^ 63 * g6)%Z).
{ rewrite Ea. destruct (Z.ltb_spec a0 (2 ^ 63)); cbv iota; lia. }
assert (Ex' : ((r1 * 2 ^ 13) mod 2 ^ 64 = g2 * 2 ^ 13)%Z).
{ symmetry. apply (Z.mod_unique _ _ g3); [left; lia | lia]. }
assert (Ey' : ((R mod 2 ^ 64) / 2 ^ 51 = g1)%Z).
{ rewrite Er0. symmetry. apply (Z.div_unique _ _ _ g0); [left; lia | lia]. }
assert (Elo' : (lo = g2 * 2 ^ 13 + g1)%Z).
{ rewrite Elo, Ex', Ey'. apply lor_low; lia. }
(* [N0] rounds [R / 2^179] to nearest, so it adds bit 178 to the top field. *)
assert (EN : (N0 = g7 + g6)%Z).
{ rewrite EN0. symmetry.
  apply (Z.div_unique _ _ _ (g0 + 2 ^ 51 * g1 + 2 ^ 64 * g2 + 2 ^ 115 * g3
                             + 2 ^ 128 * g5 + 2 ^ 178 * (1 - g6))); [left; lia | lia]. }
rewrite EN, Ea', Elo'.
split; [| split; [lia | split; lia]].
pose proof (Z.div_mod (g7 + g6) 8192 ltac:(lia)) as DN.
pose proof (Z.mod_pos_bound (g7 + g6) 8192 ltac:(lia)) as BN.
assert (Em : ((r2 + 2 ^ 50) mod 2 ^ 64 =
              2 ^ 51 * ((g7 + g6) mod 8192) + (g5 + 2 ^ 50 * (1 - g6)))%Z).
{ symmetry. apply (Z.mod_unique _ _ ((g7 + g6) / 8192)); [left; lia | lia]. }
rewrite Em. symmetry. apply (Z.div_unique _ _ _ (g5 + 2 ^ 50 * (1 - g6))); [left; lia | lia].
Qed.

(** For [m] in [[2^52, 2^53)] and [be] in [[1039, 2046]], the integers of
    [DyadicTrig.fast_reduce_band_big] give an integer [N] with [N mod 8192
    = n] and the fraction [m 2^(be - 1075) / (π/4096) - N] as [A 2^-128]
    up to less than [5 2^-128], with [A = a 2^64 + lo], as [big_int] does
    for the 106 bits of [fast_reduce_big]. The low limb [R mod 2^64] of
    [band_split] is [p0 mod 2^64]. *)
Lemma band_int :
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
  let lo := Z.lor (Z.shiftl r1 13 mod 2 ^ 64)%Z (Z.shiftr (p0 mod 2 ^ 64) 51) in
  (0 <= a0 < 2 ^ 64)%Z /\ (0 <= lo < 2 ^ 64)%Z /\
  (- 2 ^ 127 <= a * 2 ^ 64 + lo < 2 ^ 127)%Z /\
  exists (N : Z) (t : R),
  (N mod 8192 = n)%Z /\
  IZR m * bpow radix2 (be - 1075) / (PI / 4096) =
    IZR N + IZR (a * 2 ^ 64 + lo) * bpow radix2 (-128) + t /\
  0 <= t < 5 * bpow radix2 (-128).
Proof.
intros m be Hm Hbe k p0 p1 c r1 r2 n a0 a lo.
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
(* the three limbs of [R] are [r2], [r1] and [p0 mod 2^64] *)
assert (Hm0 : (0 <= m < 2 ^ 53)%Z) by lia.
pose proof (big_prod m _ _ _ Hm0 Hw0 Hw1 Hw2) as HP.
cbv zeta in HP. rewrite HW in HP. destruct HP as [HP1 HP2].
assert (Er1 : r1 = (Z.shiftr R 64 mod 2 ^ 64)%Z) by exact HP1.
assert (Er2 : r2 = Z.shiftr R 128) by exact HP2.
assert (Er0 : (p0 mod 2 ^ 64 = R mod 2 ^ 64)%Z).
{ change p0 with (m * DyadicTrig.big_w k 2)%Z. unfold R. rewrite <- HW.
  set (w0 := DyadicTrig.big_w k 0). set (w1 := DyadicTrig.big_w k 1).
  set (w2 := DyadicTrig.big_w k 2).
  set (X := (m * (w0 * 2 ^ 128 + w1 * 2 ^ 64 + w2))%Z).
  assert (EX : ((X mod 2 ^ 192) =
                m * w2 + (m * w0 * 2 ^ 64 + m * w1 - 2 ^ 128 * (X / 2 ^ 192)) * 2 ^ 64)%Z).
  { rewrite Z.mod_eq by lia. unfold X at 1. ring. }
  rewrite EX, Z.mod_add by lia. reflexivity. }
clear HP1 HP2.
clearbody R W.
pose proof (band_split R HRb) as HS. cbv zeta in HS.
rewrite <- Er2, <- Er1, <- Er0 in HS.
destruct HS as [HS1 [HS2 [HS3 HS4]]].
assert (Hn : n = (Z.shiftr (R + 2 ^ 178) 179 mod 8192)%Z) by exact HS1.
assert (HR : (R = Z.shiftr (R + 2 ^ 178) 179 * 2 ^ 179 + (a * 2 ^ 64 + lo) * 2 ^ 51
                  + R mod 2 ^ 51)%Z) by exact HS2.
assert (Ha0 : (0 <= a0 < 2 ^ 64)%Z) by exact HS3.
assert (Hlo : (0 <= lo < 2 ^ 64)%Z) by exact HS4.
assert (Ea : a = if (a0 <? 2 ^ 63)%Z then a0 else (a0 - 2 ^ 64)%Z) by reflexivity.
clear HS1 HS2 HS3 HS4.
clearbody n a a0 lo r1 r2 c p1 p0.
assert (Hab : (- 2 ^ 63 <= a < 2 ^ 63)%Z)
  by (rewrite Ea; destruct (Z.ltb_spec a0 (2 ^ 63)); lia).
assert (Hl : (0 <= R mod 2 ^ 51 < 2 ^ 51)%Z) by (apply Z.mod_pos_bound; lia).
set (N0 := Z.shiftr (R + 2 ^ 178) 179) in *.
set (A := (a * 2 ^ 64 + lo)%Z) in *.
set (Rl := (R mod 2 ^ 51)%Z) in *.
assert (HA : (- 2 ^ 127 <= A < 2 ^ 127)%Z) by (unfold A; lia).
clearbody N0 A Rl.
split; [exact Ha0 |]. split; [exact Hlo |]. split; [exact HA |].
(* [N = N0 + 8192 K]; the bits of [R] below [2^51] go into [t] *)
exists (N0 + K * 8192)%Z, (IZR Rl * bpow radix2 (-179) + t').
split; [| split].
- rewrite Z.mod_add by lia. symmetry. exact Hn.
- rewrite HF.
  assert (HRR : IZR R = IZR N0 * bpow radix2 179 + IZR A * bpow radix2 51 + IZR Rl).
  { rewrite HR at 1. rewrite !plus_IZR, !mult_IZR, !km_IZR_pow2 by lia. reflexivity. }
  assert (E1 : bpow radix2 179 * bpow radix2 (-179) = 1)
    by (rewrite <- bpow_plus; reflexivity).
  assert (E2 : bpow radix2 51 * bpow radix2 (-179) = bpow radix2 (-128))
    by (rewrite <- bpow_plus; reflexivity).
  rewrite HRR, plus_IZR, mult_IZR.
  transitivity (8192 * IZR K + IZR N0 * (bpow radix2 179 * bpow radix2 (-179)) +
                IZR A * (bpow radix2 51 * bpow radix2 (-179)) +
                IZR Rl * bpow radix2 (-179) + t'); [ring |].
  rewrite E1, E2. ring.
- (* [t <= (2^51 - 1) 2^-179 + m 2^-179 < 2^-128 + 2^-126] *)
  assert (HmR : IZR m < bpow radix2 53)
    by (rewrite <- km_IZR_pow2 by lia; apply IZR_lt; lia).
  assert (HlR : 0 <= IZR Rl <= bpow radix2 51 - 1).
  { rewrite <- km_IZR_pow2 by lia. split; [apply IZR_le; lia |].
    rewrite <- minus_IZR. apply IZR_le. lia. }
  destruct Ht' as [Ht0 Ht1].
  clear - HmR HlR Ht0 Ht1.
  cbn [bpow radix_val radix2] in *.
  split; lra.
Qed.
