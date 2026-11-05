(** * The steps that [format_fixed], [format_sci] and [format_hex] share

    [format_decompose] and [format_exact_dec] give the magnitude of a
    finite nonzero [f64] exactly, as an integer times a power of 2 or 10,
    [format_cut_dec] and [format_cut_bin] cut such a number to a multiple
    of a power of the radix, rounded toward zero or away from it, as
    [round] with [FIX_exp] does, and [round_sign] turns the rounding of a
    bound in its direction into a rounding of its magnitude toward zero or
    away from it, which [format_away] tells. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Spec Decompose.

Open Scope Z_scope.

(** ** Helpers *)

(** Clearing the sign bit of a finite pattern [sign_bit s + c] leaves
    [c]. *)
Lemma land_sign_finite :
  forall s c, 0 <= c < 2047 * 2^52 ->
  Z.land (sign_bit s + c) (2 ^ 63 - 1) = c.
Proof.
intros s c Hc.
change (2 ^ 63 - 1) with (Z.ones 63).
rewrite Z.land_ones by easy.
unfold sign_bit. destruct s; zlia.
Qed.

(** A power of the radix with a nonnegative exponent is the integer
    [beta ^ e]. *)
Lemma bpow_IZR_pow :
  forall (beta : radix) e, 0 <= e -> bpow beta e = IZR (beta ^ e).
Proof. intros beta e He. now rewrite <- IZR_Zpower. Qed.

(** Rounding [n * beta^s], for [n >= 0], to a multiple of [beta^(s + j)]
    toward zero gives the quotient [n / beta^j] times [beta^(s + j)], and
    away from zero it gives one more unless [beta^j] divides [n]. *)
Lemma round_FIX_cut :
  forall (beta : radix) n s j (away : bool), 0 <= n -> 0 <= j ->
  round beta (FIX_exp (s + j)) (if away then Zceil else Zfloor)
    (IZR n * bpow beta s) =
  (IZR (n / beta ^ j + (if away && negb (n mod beta ^ j =? 0) then 1 else 0)) *
   bpow beta (s + j))%R.
Proof.
intros beta n s j away Hn Hj.
assert (Hb : 0 < beta ^ j)
  by (apply Z.pow_pos_nonneg; [apply radix_gt_0 | exact Hj]).
(* The scaled mantissa is [n * beta^s * beta^-(s + j) = n / beta^j]. *)
assert (Hm : (IZR n * bpow beta s * bpow beta (- (s + j)) =
              IZR n / IZR (beta ^ j))%R).
{ rewrite <- bpow_IZR_pow by exact Hj.
  rewrite Rmult_assoc, <- bpow_plus.
  replace (s + - (s + j)) with (- j) by ring.
  now rewrite bpow_opp. }
unfold round, F2R, scaled_mantissa, cexp, FIX_exp. cbn [Fnum Fexp].
rewrite Hm. f_equal. f_equal.
destruct away; cbn [andb].
- destruct (Z.eqb_spec (n mod beta ^ j) 0) as [H0|H0]; cbn [negb].
  + (* [n / beta^j] is an integer, which [Zceil] keeps. *)
    assert (Hq : (IZR n / IZR (beta ^ j) = IZR (n / beta ^ j))%R).
    { rewrite (Z_div_exact_full_2 n (beta ^ j)) at 1 by lia.
      rewrite mult_IZR. field. apply not_0_IZR. lia. }
    rewrite Hq, Zceil_IZR. ring.
  + (* Otherwise [Zceil] is one more than [Zfloor], which is [Z.div]. *)
    rewrite Zceil_floor_neq.
    * rewrite Zfloor_div by lia. reflexivity.
    * rewrite Zfloor_div by lia.
      intros Hq. apply H0.
      assert (Hq' : IZR (n / beta ^ j * beta ^ j) = IZR n).
      { rewrite mult_IZR, Hq. field. apply not_0_IZR. lia. }
      apply eq_IZR in Hq'.
      pose proof (Z.div_mod n (beta ^ j)) as Hd. nia.
- rewrite Zfloor_div by lia. ring.
Qed.

(** ** The steps *)

(** [format_decompose] gives the integral significand and the exponent of
    a finite nonzero float, as [Generic.decompose] does. *)
Lemma format_decompose_correct :
  forall x, is_finite x = true -> eq x zero = false ->
  exists m e, format_decompose x = Some (m, e) /\
  0 < m < 2^53 /\ -1074 <= e <= 971 /\
  B2R x = cond_Ropp (Bsign x) (IZR m * bpow radix2 e)%R.
Proof.
intros x Fx Hz.
destruct (to_bits_finite x Fx) as (c & Hc & Hb).
destruct (from_bits_finite (Bsign x) c Hc) as (_ & _ & Hx).
rewrite <- Hb, from_to_bits in Hx.
(* The pattern 0 is a zero, which [eq] does not tell from [0.0]. *)
assert (Hc0 : c <> 0).
{ intros ->.
  unfold eq in Hz. rewrite Beqb_correct in Hz by easy.
  rewrite Req_bool_true in Hz; [discriminate|].
  rewrite Hx, magnitude_0. change (B2R zero) with 0%R.
  destruct (Bsign x); ring. }
assert (HE : 0 <= c / 2^52 <= 2046) by zlia.
(* [mant c] and [expo c] are the significand and the exponent of the
   value of [c], which [format_decompose] computes. *)
exists (mant c), (expo c).
split; [|split; [|split]].
- unfold format_decompose. cbv zeta.
  rewrite Hb, land_sign_finite, Z.shiftr_div_pow2 by (exact Hc || lia).
  change (Z.shiftl 1 52 - 1) with (Z.ones 52).
  rewrite Z.land_ones by lia.
  change (Z.shiftl 1 52) with (2 ^ 52).
  unfold mant, expo.
  destruct (Z.eqb_spec (c / 2^52) 0) as [H0|H0]; cbv beta iota;
    [|rewrite checked_u_ok by zlia; cbv beta iota].
  (* [be.max(1) as i64] keeps [be.max(1)], which is at most 2046. *)
  all: rewrite (Z.mod_small (Z.max (c / 2^52) 1 + 2^63) (2^64)) by lia.
  all: rewrite Z.add_simpl_r, checked_i_ok by lia.
  all: reflexivity.
- unfold mant. destruct (Z.eqb_spec (c / 2^52) 0); zlia.
- unfold expo. lia.
- rewrite Hx. unfold magnitude, F2R. cbn [Fnum Fexp].
  now destruct (Bsign x).
Qed.

(** [format_exact_dec] gives the magnitude of a finite nonzero float as an
    integer of at most 767 digits times a power of 10. *)
Lemma format_exact_dec_correct :
  forall x, is_finite x = true -> eq x zero = false ->
  exists n s, format_exact_dec x = Some (n, s) /\
  0 < n < 10^767 /\ -1074 <= s <= 0 /\
  B2R x = cond_Ropp (Bsign x) (IZR n * bpow radix10 s)%R.
Proof.
intros x Fx Hz.
destruct (format_decompose_correct x Fx Hz) as (m & e & Hd & Hm & He & Hx).
unfold format_exact_dec. rewrite Hd. cbv beta iota.
destruct (Z.leb_spec 0 e) as [He0|He0].
- (* An integer: [m * 2^e < 2^53 * 2^971 = 2^1024 < 10^767]. *)
  exists (m * 2^e), 0.
  rewrite (Z.mod_small e (2^64)), Z.shiftl_mul_pow2 by lia.
  assert (Hp : 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  assert (Hp' : 2^e <= 2^971) by (apply Z.pow_le_mono_r; lia).
  assert (Hmp : m * 2^e < 2^53 * 2^971).
  { apply Z.lt_le_trans with (2^53 * 2^e).
    - apply Z.mul_lt_mono_pos_r; lia.
    - apply Z.mul_le_mono_nonneg_l; lia. }
  assert (H767 : 2^53 * 2^971 < 10^767) by (vm_compute; reflexivity).
  split; [reflexivity|]. split; [split|split; [lia|]].
  + apply Z.mul_pos_pos; lia.
  + exact (Z.lt_trans _ _ _ Hmp H767).
  + rewrite Hx. f_equal. change (bpow radix10 0) with 1%R.
    rewrite Rmult_1_r, mult_IZR, (bpow_IZR_pow radix2 e) by exact He0.
    reflexivity.
- (* [m * 2^e = m * 5^-e * 10^e], and [m * 5^-e < 2^53 * 5^1074 <
     10^767]. *)
  rewrite checked_i_ok by lia. cbv beta iota.
  rewrite (Z.mod_small (- e) (2^32)) by lia.
  exists (m * 5^(- e)), e.
  assert (Hp : 0 < 5^(- e)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hp' : 5^(- e) <= 5^1074) by (apply Z.pow_le_mono_r; lia).
  assert (Hmp : m * 5^(- e) < 2^53 * 5^1074).
  { apply Z.lt_le_trans with (2^53 * 5^(- e)).
    - apply Z.mul_lt_mono_pos_r; lia.
    - apply Z.mul_le_mono_nonneg_l; lia. }
  assert (H767 : 2^53 * 5^1074 < 10^767) by (vm_compute; reflexivity).
  split; [reflexivity|]. split; [split|split; [lia|]].
  + apply Z.mul_pos_pos; lia.
  + exact (Z.lt_trans _ _ _ Hmp H767).
  + rewrite Hx. f_equal.
    remember (- e) as k eqn:Hk. replace e with (- k) by lia.
    rewrite 2!bpow_opp, 2!bpow_IZR_pow by lia.
    cbn [radix_val radix2 radix10].
    replace (10 ^ k) with (2 ^ k * 5 ^ k) by (rewrite <- Z.pow_mul_l; reflexivity).
    assert (H2 : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    assert (H5 : 0 < 5 ^ k) by (apply Z.pow_pos_nonneg; lia).
    apply Z.lt_neq, not_eq_sym, not_0_IZR in H2.
    apply Z.lt_neq, not_eq_sym, not_0_IZR in H5.
    rewrite 2!mult_IZR. field. split; assumption.
Qed.

(** [format_cut_dec n s t away] is [n * 10^s] rounded to a multiple of
    [10^t], toward zero, or away from zero if [away]; the number itself if
    [t <= s]. *)
Lemma format_cut_dec_correct :
  forall n s t away,
  0 <= n -> -2^62 <= s < 2^62 -> -2^62 <= t < 2^62 -> t - s < 2^32 ->
  exists d, format_cut_dec n s t away = Some (d, Z.max s t) /\ 0 <= d /\
  (IZR d * bpow radix10 (Z.max s t) =
   round radix10 (FIX_exp t) (if away then Zceil else Zfloor)
     (IZR n * bpow radix10 s))%R.
Proof.
intros n s t away Hn Hs Ht Hts.
unfold format_cut_dec.
destruct (Z.leb_spec t s) as [Hle|Hlt].
- (* [n * 10^s = (n * 10^(s - t)) * 10^t] is a multiple of [10^t]
     already. *)
  exists n. rewrite Z.max_l by exact Hle.
  split; [reflexivity|]. split; [exact Hn|].
  assert (Hf : generic_format radix10 (FIX_exp t) (IZR n * bpow radix10 s)).
  { apply generic_format_FIX.
    apply (FIX_spec _ _ _ (Float radix10 (n * 10 ^ (s - t)) t)); [|reflexivity].
    unfold F2R. cbn [Fnum Fexp].
    rewrite mult_IZR.
    replace (IZR (10 ^ (s - t))) with (bpow radix10 (s - t))
      by (apply bpow_IZR_pow; lia).
    rewrite Rmult_assoc, <- bpow_plus.
    now replace (s - t + t) with s by ring. }
  destruct away; cbv iota; symmetry; exact (round_generic _ _ _ _ Hf).
- (* [t - s] fits, and [5^(t - s) << (t - s)] is [10^(t - s)]. *)
  rewrite Z.max_r by lia.
  rewrite checked_i_ok by lia. cbv beta iota.
  rewrite (Z.mod_small (t - s) (2^32)), Z.shiftl_mul_pow2 by lia.
  rewrite <- Z.pow_mul_l. change (5 * 2) with 10.
  assert (Hb : 0 < 10 ^ (t - s)) by (apply Z.pow_pos_nonneg; lia).
  unfold div_u, rem_u. rewrite (proj2 (Z.eqb_neq _ 0)) by lia. cbv beta iota.
  exists (n / 10 ^ (t - s) +
          (if away && negb (n mod 10 ^ (t - s) =? 0) then 1 else 0)).
  split; [|split].
  + destruct (away && negb (n mod 10 ^ (t - s) =? 0));
      [reflexivity | now rewrite Z.add_0_r].
  + assert (0 <= n / 10 ^ (t - s)) by (apply Z.div_pos; lia).
    destruct (away && negb (n mod 10 ^ (t - s) =? 0)); lia.
  + remember (t - s) as j eqn:Hj. replace t with (s + j) by lia.
    rewrite round_FIX_cut by lia. reflexivity.
Qed.

(** [format_cut_bin m j away] is [m] rounded to a multiple of [2^j],
    toward zero, or away from zero if [away], and divided by [2^j]. The
    scale [e] is any power of 2 that [m] is taken times. *)
Lemma format_cut_bin_correct :
  forall m j e away, 0 <= m < 2^64 -> 0 <= j < 64 ->
  exists d, format_cut_bin m j away = Some d /\
  (IZR d * bpow radix2 (e + j) =
   round radix2 (FIX_exp (e + j)) (if away then Zceil else Zfloor)
     (IZR m * bpow radix2 e))%R.
Proof.
intros m j e away Hm Hj.
assert (Hp : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
assert (Hp64 : 2 ^ j < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
exists (m / 2 ^ j + (if away && negb (m mod 2 ^ j =? 0) then 1 else 0)).
split.
- unfold format_cut_bin. rewrite shr_ok by lia. cbv beta iota.
  destruct away; cbn [andb].
  + rewrite shl_ok by lia. cbv beta iota.
    rewrite Z.mul_1_l, checked_u_ok by lia. cbv beta iota.
    (* The mask [(1 << j) - 1] keeps the [j] low bits. *)
    replace (2 ^ j - 1) with (Z.ones j) by (rewrite Z.ones_equiv; lia).
    rewrite Z.land_ones by lia.
    destruct (Z.eqb_spec (m mod 2 ^ j) 0) as [H0|H0]; cbn [negb].
    * now rewrite Z.add_0_r.
    * (* Some low bit is set, so [j >= 1] and [m >> j < 2^63]: the
         increment does not overflow. *)
      assert (Hj1 : 1 <= j).
      { destruct (Z.eq_dec j 0) as [->|]; [|lia].
        now rewrite Z.pow_0_r, Z.mod_1_r in H0. }
      assert (Hp2 : 2 ^ 1 <= 2 ^ j) by (apply Z.pow_le_mono_r; lia).
      assert (Hq : m / 2 ^ j < 2 ^ 63)
        by (apply Z.div_lt_upper_bound; nia).
      assert (0 <= m / 2 ^ j) by (apply Z.div_pos; lia).
      rewrite checked_u_ok by lia. reflexivity.
  + now rewrite Z.add_0_r.
- rewrite round_FIX_cut by lia. reflexivity.
Qed.

(** Rounding [y] or [-y] toward +inf if [up] and toward -inf otherwise is
    rounding the magnitude [y] away from zero or toward it, as
    [format_away] says for the sign [s]. *)
Lemma round_sign :
  forall beta fexp (s up : bool) y,
  round beta fexp (if up then Zceil else Zfloor) (cond_Ropp s y) =
  cond_Ropp s
    (round beta fexp (if negb (Bool.eqb s up) then Zceil else Zfloor) y).
Proof.
intros beta fexp s up y.
destruct s; simpl cond_Ropp.
- (* [round_opp] rounds [-y] as [y] with the opposite rounding, and
     [Zceil] is [- Zfloor (- x)] by its definition. *)
  rewrite round_opp. f_equal. apply round_ext. intros z.
  unfold Zrnd_opp, Zceil. destruct up; simpl.
  + now rewrite Ropp_involutive, Z.opp_involutive.
  + reflexivity.
- now destruct up.
Qed.

(** Rounding with [FLX_exp prec] is rounding with [FIX_exp] at the
    exponent that [FLX_exp prec] gives the number. *)
Lemma round_FLX_FIX :
  forall beta prec rnd y e, e = mag beta y - prec ->
  round beta (FLX_exp prec) rnd y = round beta (FIX_exp e) rnd y.
Proof.
intros beta prec rnd y e He.
unfold round, scaled_mantissa, cexp, FLX_exp, FIX_exp.
now rewrite <- He.
Qed.
