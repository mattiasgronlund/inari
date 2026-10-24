(** * [div1_ru_slow] rounds toward +inf

    [div1_ru_slow x y] is the slow path of [div_ru]. If [x] or [y] is
    zero or not finite, it returns [x / y] rounded to nearest, which then
    does not depend on the rounding mode ([div_special]). Otherwise it
    divides the significands as integers and rounds the quotient with
    [round_up_exact]. It never panics, and its result is [x / y] rounded
    up as [rounds_up_to] describes ([div1_ru_slow_rounds_up]).

    It shifts the significand [my] of [y] into [ny] in [[2^52, 2^53)] and
    that of [x] into [nx] in [[2^126, 2^127)], so that the integer quotient
    [q = nx / ny] is in [[2^73, 2^75)]. With the remainder [rem] and the
    exponent [e] of the quotient, [|x / y| = (q + rem / ny) * 2^e] with
    [0 <= rem / ny < 1], so [|x / y| = q * 2^e] if [rem = 0], and
    [q * 2^e < |x / y| < (q + 1) * 2^e] if not. As [q >= 2^52], the part
    beyond [q * 2^e] is below the last bit of the result, so [rem <> 0]
    serves [round_up_exact] as its sticky bit. *)

From Stdlib Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Spec Decompose RoundUpExact
  SumRoundUp.

(** Where [div1_ru_fast] and [div1_ru_slow] return [x / y] as computed in
    the default rounding mode, it does not depend on the rounding mode. *)
Lemma div_special :
  forall x y,
  negb (Generic.is_finite x && Generic.is_finite y) || eq x zero || eq y zero = true ->
  div x y = Bdiv mode_UP x y.
Proof.
intros x y H.
rewrite !is_finite_eq in H.
unfold div.
(* [Bdiv] looks at the rounding mode only for two finite nonzero
   operands, which [H] excludes. *)
destruct x as [sx|sx| |[|] mx ex Hx], y as [sy|sy| |[|] my ey Hy];
  try discriminate H; reflexivity.
Qed.

(** ** Integer division *)

Open Scope Z_scope.

(** Shifting [m > 0] left by [k - log2 m] bits puts it in
    [[2^k, 2^(k + 1))]. *)
Lemma shl_log2_bounds :
  forall m k, 0 < m -> Z.log2 m <= k ->
  2^k <= m * 2^(k - Z.log2 m) < 2^(k + 1).
Proof.
intros m k Hm Hk.
pose proof (Z.log2_spec m Hm) as Hl.
rewrite <- Z.add_1_r in Hl.
pose proof (Z.log2_nonneg m) as Hl0.
(* [2^k] and [2^(k + 1)] are the bounds on [m] times [2^(k - log2 m)]. *)
assert (E1 : 2^k = 2^(Z.log2 m) * 2^(k - Z.log2 m))
  by (rewrite <- Z.pow_add_r by lia; f_equal; ring).
assert (E2 : 2^(k + 1) = 2^(Z.log2 m + 1) * 2^(k - Z.log2 m))
  by (rewrite <- Z.pow_add_r by lia; f_equal; ring).
assert (Hp : 0 < 2^(k - Z.log2 m)) by (apply Z.pow_pos_nonneg; lia).
rewrite E1, E2. nia.
Qed.

Open Scope R_scope.

(** [a / b = q + rem / b] for the integer quotient [q] and remainder
    [rem] of [a] and [b > 0], with [0 <= rem / b < 1], so [a / b * 2^e] is
    [q * 2^e] if [rem = 0], and strictly between [q * 2^e] and
    [(q + 1) * 2^e] if not. *)
Lemma div_mod_bounds :
  forall a b e, (0 < b)%Z ->
  if negb (a mod b =? 0)%Z then
    F2R (Float radix2 (a / b) e) < IZR a / IZR b * bpow radix2 e
      < F2R (Float radix2 (a / b + 1) e)
  else IZR a / IZR b * bpow radix2 e = F2R (Float radix2 (a / b) e).
Proof.
intros a b e Hb.
pose proof (Z.div_mod a b ltac:(lia)) as Hd.
pose proof (Z.mod_pos_bound a b Hb) as Hr.
set (q := (a / b)%Z) in *. set (r := (a mod b)%Z) in *.
clearbody q r.
assert (HA : IZR a = IZR b * IZR q + IZR r).
{ rewrite <- mult_IZR, <- plus_IZR. f_equal. exact Hd. }
assert (HB : 0 < bpow radix2 e) by apply bpow_gt_0.
assert (Hb' : 0 < IZR b) by (apply IZR_lt; exact Hb).
unfold F2R; cbn [Fnum Fexp].
rewrite plus_IZR.
destruct (Z.eqb_spec r 0) as [H0|H0]; cbn [negb].
- rewrite HA, H0. field. lra.
- assert (Hr' : 0 < IZR r < IZR b) by (split; apply IZR_lt; lia).
  (* [u = a / b], with [q < u < q + 1] as [a = b * q + r] and [0 < r < b]. *)
  set (u := IZR a / IZR b).
  assert (Hu : u * IZR b = IZR a) by (unfold u; field; lra).
  assert (Hq : IZR q < u < IZR q + 1) by (split; nra).
  split; apply Rmult_lt_compat_r; lra.
Qed.

(** [(a * 2^ea) / (b * 2^eb) = a / b * 2^(ea - eb)]. *)
Lemma F2R_div :
  forall a ea b eb, b <> 0%Z ->
  F2R (Float radix2 a ea) / F2R (Float radix2 b eb) =
    IZR a / IZR b * bpow radix2 (ea - eb).
Proof.
intros a ea b eb Hb.
unfold F2R; cbn [Fnum Fexp].
assert (E : bpow radix2 ea = bpow radix2 (ea - eb) * bpow radix2 eb)
  by (rewrite <- bpow_plus; f_equal; ring).
assert (HB : 0 < bpow radix2 eb) by apply bpow_gt_0.
assert (Hb' : IZR b <> 0) by (apply eq_IZR_contrapositive; exact Hb).
rewrite E. field. lra.
Qed.

(** A quotient of [cond_Ropp sx a] and [cond_Ropp sy b] has the sign
    [xorb sx sy] and the magnitude [a / b]. *)
Lemma cond_Ropp_div :
  forall sx sy a b, b <> 0 ->
  cond_Ropp sx a / cond_Ropp sy b = cond_Ropp (xorb sx sy) (a / b).
Proof.
intros sx sy a b Hb.
destruct sx, sy; unfold cond_Ropp; cbn [xorb]; field; exact Hb.
Qed.

(** ** The slow path *)

Theorem div1_ru_slow_rounds_up :
  forall x y,
  negb (Generic.is_finite x && Generic.is_finite y) || eq x zero || eq y zero = false ->
  exists r, Generic.div1_ru_slow x y = Some r /\ rounds_up_to (B2R x / B2R y) r.
Proof.
intros x y Hsp.
unfold Generic.div1_ru_slow. rewrite Hsp.
rewrite !is_finite_eq in Hsp.
apply Bool.orb_false_elim in Hsp as [Hsp Hy0].
apply Bool.orb_false_elim in Hsp as [Hf Hx0].
apply Bool.negb_false_iff, andb_prop in Hf as [Fx Fy].
generalize (decompose_correct x Fx Hx0) (decompose_correct y Fy Hy0).
destruct (Generic.decompose x) as ((sx, mx), ex).
destruct (Generic.decompose y) as ((sy, my), ey).
intros (-> & Hmx & Hex & Hx) (-> & Hmy & Hey & Hy).
(* [leading_zeros 64 m = 63 - log2 m], with [0 <= log2 m <= 52]. *)
rewrite (leading_zeros_pos 64 my), (leading_zeros_pos 64 mx) by lia.
assert (Hly : (0 <= Z.log2 my < 53)%Z).
{ split; [apply Z.log2_nonneg | apply Z.log2_lt_pow2; lia]. }
assert (Hlx : (0 <= Z.log2 mx < 53)%Z).
{ split; [apply Z.log2_nonneg | apply Z.log2_lt_pow2; lia]. }
assert (Hny : (2^52 <= my * 2^(52 - Z.log2 my) < 2^53)%Z)
  by (apply shl_log2_bounds; lia).
assert (Hnx : (2^126 <= mx * 2^(126 - Z.log2 mx) < 2^127)%Z)
  by (apply shl_log2_bounds; lia).
set (ly := Z.log2 my) in *. set (lx := Z.log2 mx) in *.
clearbody ly lx.
(* [ny = my << (lz - 11)] and [ey - (lz - 11)] with [lz - 11 = 52 - ly].
   No shift loses a bit, and no shift amount or exponent overflows. *)
replace (64 - 1 - ly - 11)%Z with (52 - ly)%Z by ring.
rewrite (checked_u_ok 32 (52 - ly)) by lia. cbv beta iota.
rewrite (shl_ok 64 my (52 - ly)) by lia. cbv beta iota.
rewrite (checked_i_ok 32 (52 - ly)) by lia. cbv beta iota.
rewrite (checked_i_ok 32 (ey - (52 - ly))) by lia. cbv beta iota.
(* [nx = mx << (lz + 64 - 1)] and [ex - (lz + 64 - 1)] with
   [lz + 64 - 1 = 126 - lx]. *)
replace (64 - 1 - lx + 64)%Z with (127 - lx)%Z by ring.
rewrite (checked_u_ok 32 (127 - lx)) by lia. cbv beta iota.
rewrite (checked_u_ok 32 (127 - lx - 1)) by lia. cbv beta iota.
replace (127 - lx - 1)%Z with (126 - lx)%Z by ring.
rewrite (shl_ok 128 mx (126 - lx)) by lia. cbv beta iota.
rewrite (checked_i_ok 32 (127 - lx)) by lia. cbv beta iota.
rewrite (checked_i_ok 32 (127 - lx - 1)) by lia. cbv beta iota.
replace (127 - lx - 1)%Z with (126 - lx)%Z by ring.
rewrite (checked_i_ok 32 (ex - (126 - lx))) by lia. cbv beta iota.
(* [ny <> 0], so the division and the remainder do not panic. *)
set (ny := (my * 2^(52 - ly))%Z) in *.
set (nx := (mx * 2^(126 - lx))%Z) in *.
unfold div_u, rem_u.
destruct (Z.eqb_spec ny 0) as [|_]; [lia|]. cbv beta iota.
rewrite (checked_i_ok 32 (ex - (126 - lx) - (ey - (52 - ly)))) by lia.
cbv beta iota.
(* [2^73 <= q < 2^75], as [nx] is in [[2^126, 2^127)] and [ny] in
   [[2^52, 2^53)]. *)
assert (Hq : (2^73 <= nx / ny < 2^75)%Z).
{ split.
  - apply Z.div_le_lower_bound; lia.
  - apply Z.div_lt_upper_bound; lia. }
(* [x / y] has the sign [sx != sy] and the magnitude [nx / ny * 2^e],
   where [e] is the exponent passed to [round_up_exact]. *)
assert (HX : 0 < F2R (Float radix2 mx ex)) by (apply F2R_gt_0; simpl; lia).
assert (HY : 0 < F2R (Float radix2 my ey)) by (apply F2R_gt_0; simpl; lia).
assert (Hv :
  Rlt_bool (B2R x / B2R y) 0 = negb (Bool.eqb (Bsign x) (Bsign y)) /\
  Rabs (B2R x / B2R y) =
    IZR nx / IZR ny * bpow radix2 (ex - (126 - lx) - (ey - (52 - ly)))).
{ rewrite Hx, Hy, cond_Ropp_div by lra.
  destruct (cond_Ropp_pos (xorb (Bsign x) (Bsign y))
    (F2R (Float radix2 mx ex) / F2R (Float radix2 my ey))) as (Hs & Ha).
  { apply Rdiv_lt_0_compat; assumption. }
  rewrite Hs, Ha. split.
  - now destruct (Bsign x), (Bsign y).
  - rewrite <- (F2R_shl mx ex (126 - lx)), <- (F2R_shl my ey (52 - ly))
      by lia.
    apply F2R_div. lia. }
destruct Hv as (Hs & Ha).
apply round_up_exact_correct.
split; [lia|]. split; [lia|]. split; [intros _; lia|]. split; [exact Hs|].
rewrite Ha. apply div_mod_bounds. lia.
Qed.
