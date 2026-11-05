(** * [format_hex] rounds the bounds of [{:x}]

    [format_hex x p up] is a finite nonzero [x] as the digits [d] of its
    magnitude and the exponent [k] of 2: exactly without a precision
    ([p = None]), rounded to 4 significant bits for [p = Some 0], and
    rounded to [p + 1] significant hex digits for [p = Some p] with
    [p >= 1], toward +inf if [up] and toward -inf otherwise. So they are
    as tight as their directions allow. [src/format/diff_tests.rs] tests
    the text that [src/format.rs] writes from [d] and [k] against MPFR's
    [%Ra], which, with [%.0Ra], adds 1 to the digit of a number of at most
    4 significant bits that it rounds away from zero, though that number
    is exact (see [src/format.rs]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Encoding Spec DivRuSlow FormatCut.

Open Scope Z_scope.

(** ** Powers of 2 and of 16 *)

Lemma IZR_pow2_hex : forall e, 0 <= e -> IZR (2 ^ e) = bpow radix2 e.
Proof. intros e He. exact (IZR_Zpower radix2 e He). Qed.

(** A hex digit is 4 bits: [16^e = 2^(4 e)]. *)
Lemma bpow_radix16 : forall e, bpow radix16 e = bpow radix2 (4 * e).
Proof.
assert (Hp : forall e, 0 <= e -> bpow radix16 e = bpow radix2 (4 * e)).
{ intros e He.
  rewrite <- (IZR_Zpower radix16 e He), <- (IZR_Zpower radix2 (4 * e)) by lia.
  f_equal. change (Zpower radix16 e) with (16 ^ e).
  change (Zpower radix2 (4 * e)) with (2 ^ (4 * e)).
  rewrite Z.pow_mul_r by lia. reflexivity. }
intros e. destruct (Z_le_gt_dec 0 e) as [He|He]; [now apply Hp|].
(* [16^e = 1 / 16^(-e)] for [e < 0]. *)
replace e with (- (- e)) by ring.
rewrite (bpow_opp radix16 (- e)), (Hp (- e)) by lia.
rewrite <- bpow_opp. f_equal. ring.
Qed.

(** Rounding to a multiple of [16^e] is rounding to a multiple of
    [2^(4 e)]. *)
Lemma round_radix16_FIX :
  forall rnd e y,
  round radix16 (FIX_exp e) rnd y = round radix2 (FIX_exp (4 * e)) rnd y.
Proof.
intros rnd e y.
unfold round, scaled_mantissa, cexp, FIX_exp, F2R. cbn [Fnum Fexp].
rewrite !bpow_radix16. now replace (4 * - e) with (- (4 * e)) by ring.
Qed.

(** ** The magnitude of [x] *)

(** [m53 * 2^(ex - 52)] with [2^52 <= m53 < 2^53] is in
    [[2^ex, 2^(ex + 1))]. *)
Lemma hex_bounds :
  forall m53 ex, 2^52 <= m53 < 2^53 ->
  (bpow radix2 ex <= IZR m53 * bpow radix2 (ex - 52) < bpow radix2 (ex + 1))%R.
Proof.
intros m53 ex Hm.
assert (H52 : (bpow radix2 52 <= IZR m53)%R)
  by (rewrite <- IZR_pow2_hex by lia; apply IZR_le; lia).
assert (H53 : (IZR m53 < bpow radix2 53)%R)
  by (rewrite <- IZR_pow2_hex by lia; apply IZR_lt; lia).
pose proof (bpow_gt_0 radix2 (ex - 52)) as Hb.
assert (E1 : bpow radix2 ex = (bpow radix2 52 * bpow radix2 (ex - 52))%R)
  by (rewrite <- bpow_plus; f_equal; ring).
assert (E2 : bpow radix2 (ex + 1) = (bpow radix2 53 * bpow radix2 (ex - 52))%R)
  by (rewrite <- bpow_plus; f_equal; ring).
rewrite E1, E2. split.
- apply Rmult_le_compat_r; lra.
- apply Rmult_lt_compat_r; lra.
Qed.

Lemma hex_nonneg :
  forall m53 ex, 2^52 <= m53 < 2^53 ->
  (0 <= IZR m53 * bpow radix2 (ex - 52))%R.
Proof.
intros m53 ex Hm.
pose proof (hex_bounds m53 ex Hm) as Hb.
pose proof (bpow_gt_0 radix2 ex). lra.
Qed.

(** Its leading bit is the bit [ex] of [x], ... *)
Lemma mag_hex2 :
  forall m53 ex, 2^52 <= m53 < 2^53 ->
  (mag radix2 (IZR m53 * bpow radix2 (ex - 52))%R : Z) = ex + 1.
Proof.
intros m53 ex Hm. apply mag_unique_pos.
replace (ex + 1 - 1) with ex by ring. now apply hex_bounds.
Qed.

(** ... and its leading hex digit is the digit [ex / 4], which holds the
    bits [4 * (ex / 4)] to [4 * (ex / 4) + 3]. *)
Lemma mag_hex16 :
  forall m53 ex, 2^52 <= m53 < 2^53 ->
  (mag radix16 (IZR m53 * bpow radix2 (ex - 52))%R : Z) = ex / 4 + 1.
Proof.
intros m53 ex Hm. apply mag_unique_pos.
rewrite !bpow_radix16.
pose proof (hex_bounds m53 ex Hm) as Hb.
pose proof (Z.div_mod ex 4 ltac:(lia)) as Hd.
pose proof (Z.mod_pos_bound ex 4 ltac:(lia)) as Hr.
pose proof (bpow_le radix2 (4 * (ex / 4 + 1 - 1)) ex ltac:(lia)) as H1.
pose proof (bpow_le radix2 (ex + 1) (4 * (ex / 4 + 1)) ltac:(lia)) as H2.
lra.
Qed.

(** [d14 = m53 * 2^(ex mod 4)] is the 14 hex digits of [x], with the
    point after the first: [d14 * 2^(4 * (ex / 4) - 52)] is [x]. *)
Lemma hex_d14 :
  forall m53 ex,
  (IZR (m53 * 2^(ex mod 4)) * bpow radix2 (4 * (ex / 4) - 52) =
   IZR m53 * bpow radix2 (ex - 52))%R.
Proof.
intros m53 ex.
pose proof (Z.div_mod ex 4 ltac:(lia)) as Hd.
pose proof (Z.mod_pos_bound ex 4 ltac:(lia)) as Hr.
rewrite mult_IZR, IZR_pow2_hex by lia.
rewrite Rmult_assoc, <- bpow_plus. do 2 f_equal. lia.
Qed.

(** [d14] has at most 56 bits, so it fits a [u64] and 14 hex digits. *)
Lemma hex_d14_bounds :
  forall m53 ex, 2^52 <= m53 < 2^53 -> 0 <= m53 * 2^(ex mod 4) < 2^56.
Proof.
intros m53 ex Hm.
pose proof (Z.mod_pos_bound ex 4 ltac:(lia)) as Hr.
assert (H8 : 2^(ex mod 4) <= 2^3) by (apply Z.pow_le_mono_r; lia).
assert (H0 : 0 < 2^(ex mod 4)) by (apply Z.pow_pos_nonneg; lia).
change (2^3) with 8 in H8. change (2^56) with (2^53 * 8). nia.
Qed.

(** The digits of a rounding of a number [y >= 0] are not negative. *)
Lemma digits_nonneg :
  forall beta fexp, Valid_exp fexp ->
  forall (away : bool) d k y, (0 <= y)%R ->
  (IZR d * bpow beta k = round beta fexp (if away then Zceil else Zfloor) y)%R ->
  0 <= d.
Proof.
intros beta fexp Hv away d k y Hy Hd.
assert (H0 : (0 <= round beta fexp (if away then Zceil else Zfloor) y)%R).
{ destruct away.
  - apply (round_ge_generic beta fexp Zceil 0 y); [apply generic_format_0 | exact Hy].
  - apply (round_ge_generic beta fexp Zfloor 0 y); [apply generic_format_0 | exact Hy]. }
rewrite <- Hd in H0.
pose proof (bpow_gt_0 beta k) as Hb.
apply le_IZR. apply Rmult_le_reg_r with (bpow beta k); [exact Hb|]. lra.
Qed.

(** ** What [format_hex] computes *)

(** [format_hex x p up] with [m53 = m * 2^lz] in [[2^52, 2^53)] for the
    [lz = 52 - log2 m] leading zeros of the significand [m] of [x] in 53
    bits, and with [ex = e + 52 - lz], so that [x] is [m53 * 2^(ex - 52)]:
    [cut_bin m53 49] at the exponent [ex - 3] for [Some 0], and the 14 hex
    digits [d14 = m53 * 2^(ex mod 4)] at the exponent [4 * (ex / 4) - 52],
    cut by [4 * (13 - p)] bits for [Some p] with [1 <= p < 13], and kept
    for [None] and for [Some p] with [p >= 13]. *)
Lemma format_hex_cases :
  forall x up, is_finite x = true -> eq x zero = false ->
  exists m53 ex,
  2^52 <= m53 < 2^53 /\ -1074 <= ex <= 1023 /\
  B2R x = cond_Ropp (Bsign x) (IZR m53 * bpow radix2 (ex - 52))%R /\
  format_hex x (Some 0) up =
    (let* d := format_cut_bin m53 49 (format_away x up) in Some (d, ex - 3)) /\
  format_hex x None up = Some (m53 * 2^(ex mod 4), 4 * (ex / 4) - 52) /\
  (forall p, 1 <= p < 13 ->
   format_hex x (Some p) up =
   let* d := format_cut_bin (m53 * 2^(ex mod 4)) (4 * (13 - p))
     (format_away x up) in
   Some (d, 4 * (ex / 4) - 4 * p)) /\
  (forall p, 13 <= p ->
   format_hex x (Some p) up = Some (m53 * 2^(ex mod 4), 4 * (ex / 4) - 52)).
Proof.
intros x up Hx Hz.
destruct (format_decompose_correct x Hx Hz) as (m & e & Hd & Hm & He & Hxr).
assert (Hl : 0 <= Z.log2 m < 53).
{ split; [apply Z.log2_nonneg | apply Z.log2_lt_pow2; lia]. }
pose proof (shl_log2_bounds m 52 ltac:(lia) ltac:(lia)) as Hn.
change (52 + 1) with 53 in Hn.
(* [m * 2^e] is [m53 * 2^(ex - 52)]. *)
assert (Hxr' : B2R x = cond_Ropp (Bsign x)
    (IZR (m * 2^(52 - Z.log2 m)) * bpow radix2 (e + Z.log2 m - 52))%R).
{ rewrite Hxr. f_equal. rewrite mult_IZR, IZR_pow2_hex by lia.
  rewrite Rmult_assoc, <- bpow_plus. do 2 f_equal. ring. }
assert (Hex : -1074 <= e + Z.log2 m <= 1023) by lia.
(* The steps up to [ex] do not overflow: [lz = 52 - log2 m] and the
   shift keeps every bit of [m]. *)
unfold format_hex. rewrite Hd. cbv beta iota zeta.
rewrite (leading_zeros_pos 64 m) by lia.
replace (64 - 1 - Z.log2 m - 11) with (52 - Z.log2 m) by ring.
rewrite (checked_u_ok 32 (52 - Z.log2 m)) by lia. cbv beta iota.
rewrite (shl_ok 64 m (52 - Z.log2 m)) by lia. cbv beta iota.
rewrite (checked_i_ok 64 (e + 52)) by lia. cbv beta iota.
rewrite (checked_i_ok 64 (e + 52 - (52 - Z.log2 m))) by lia. cbv beta iota.
replace (e + 52 - (52 - Z.log2 m)) with (e + Z.log2 m) by ring.
set (m53 := m * 2^(52 - Z.log2 m)) in *.
set (ex := e + Z.log2 m) in *.
clearbody m53 ex.
pose proof (Z.div_mod ex 4 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound ex 4 ltac:(lia)) as Hr.
pose proof (hex_d14_bounds m53 ex Hn) as H14.
(* Nor do the steps to [d14] and [k]. *)
rewrite (shl_ok 64 m53 (ex mod 4)) by lia. cbv beta iota.
rewrite (checked_i_ok 64 (4 * (ex / 4))) by lia. cbv beta iota.
rewrite (checked_i_ok 64 (4 * (ex / 4) - 52)) by lia. cbv beta iota.
exists m53, ex.
split; [exact Hn|]. split; [exact Hex|]. split; [exact Hxr'|].
split; [|split; [|split]].
- rewrite Z.eqb_refl. cbv beta iota.
  destruct (format_cut_bin m53 49 (format_away x up)) as [d|]; [|reflexivity].
  rewrite (checked_i_ok 64 (ex - 3)) by lia. reflexivity.
- reflexivity.
- intros p Hp.
  destruct (Z.eqb_spec p 0) as [|_]; [lia|]. cbv beta iota.
  destruct (Z.ltb_spec p 13) as [_|]; [|lia]. cbv beta iota.
  (* [j = 4 * (13 - p)] of [u32]. *)
  rewrite (Z.mod_small p (2^32)) by lia.
  rewrite (checked_u_ok 32 (13 - p)) by lia. cbv beta iota.
  rewrite (checked_u_ok 32 (4 * (13 - p))) by lia. cbv beta iota.
  destruct (format_cut_bin (m53 * 2^(ex mod 4)) (4 * (13 - p))
    (format_away x up)) as [d|]; [|reflexivity].
  rewrite (checked_i_ok 64 (4 * (ex / 4) - 52 + 4 * (13 - p))) by lia.
  replace (4 * (ex / 4) - 52 + 4 * (13 - p)) with (4 * (ex / 4) - 4 * p)
    by ring.
  reflexivity.
- intros p Hp.
  destruct (Z.eqb_spec p 0) as [|_]; [lia|]. cbv beta iota.
  destruct (Z.ltb_spec p 13) as [|_]; [lia|]. reflexivity.
Qed.

(** ** The theorems *)

(** Without a precision, [{:x}] prints [x] exactly. *)
Theorem format_hex_exact_correct :
  forall x up, is_finite x = true -> eq x zero = false ->
  exists d k, format_hex x None up = Some (d, k) /\ 0 <= d /\
  cond_Ropp (Bsign x) (IZR d * bpow radix2 k)%R = B2R x.
Proof.
intros x up Hx Hz.
destruct (format_hex_cases x up Hx Hz)
  as (m53 & ex & Hm & Hex & Hxr & _ & Hn & _ & _).
exists (m53 * 2^(ex mod 4)), (4 * (ex / 4) - 52).
pose proof (hex_d14_bounds m53 ex Hm) as H14.
split; [exact Hn|]. split; [lia|].
rewrite hex_d14. symmetry. exact Hxr.
Qed.

(** [{:.0x}] prints [x] rounded to 4 bits in its direction: [cut_bin]
    drops the 49 lowest of the 53 bits of [m53]. *)
Theorem format_hex_bin_correct :
  forall x up, is_finite x = true -> eq x zero = false ->
  exists d k, format_hex x (Some 0) up = Some (d, k) /\ 0 <= d /\
  cond_Ropp (Bsign x) (IZR d * bpow radix2 k)%R =
  round radix2 (FLX_exp 4) (if up then Zceil else Zfloor) (B2R x).
Proof.
intros x up Hx Hz.
destruct (format_hex_cases x up Hx Hz)
  as (m53 & ex & Hm & Hex & Hxr & Hb & _ & _ & _).
rewrite Hb.
destruct (format_cut_bin_correct m53 49 (ex - 52) (format_away x up))
  as (d & Hd & Hr); [lia | lia |].
rewrite Hd. cbv beta iota.
exists d, (ex - 3). split; [reflexivity|].
replace (ex - 52 + 49) with (ex - 3) in Hr by ring.
split.
- exact (digits_nonneg _ _ (FIX_exp_valid (ex - 3)) _ _ _ _
    (hex_nonneg m53 ex Hm) Hr).
- (* The magnitude rounds away from zero or toward it, and with 4 bits
     at [mag = ex + 1] the last kept bit is the bit [ex - 3]. *)
  rewrite Hxr, round_sign. f_equal.
  rewrite (round_FLX_FIX radix2 4 _ _ (ex - 3))
    by (rewrite mag_hex2 by lia; ring).
  exact Hr.
Qed.

(** [{:.px}] with [p >= 1] prints [x] rounded to [p + 1] hex digits in its
    direction: [cut_bin] drops the [13 - p] lowest of the 14 hex digits of
    [d14] if [p < 13], and they are all kept otherwise, which is exact. *)
Theorem format_hex_digits_correct :
  forall x p up, is_finite x = true -> eq x zero = false -> 1 <= p < 2^64 ->
  exists d k, format_hex x (Some p) up = Some (d, k) /\ 0 <= d /\
  cond_Ropp (Bsign x) (IZR d * bpow radix2 k)%R =
  round radix16 (FLX_exp (p + 1)) (if up then Zceil else Zfloor) (B2R x).
Proof.
intros x p up Hx Hz Hp.
destruct (format_hex_cases x up Hx Hz)
  as (m53 & ex & Hm & Hex & Hxr & _ & _ & Hlt & Hge).
pose proof (hex_d14_bounds m53 ex Hm) as H14.
destruct (Z_lt_le_dec p 13) as [Hp13|Hp13].
- rewrite (Hlt p) by lia.
  destruct (format_cut_bin_correct (m53 * 2^(ex mod 4)) (4 * (13 - p))
    (4 * (ex / 4) - 52) (format_away x up)) as (d & Hd & Hr); [lia | lia |].
  rewrite Hd. cbv beta iota.
  exists d, (4 * (ex / 4) - 4 * p). split; [reflexivity|].
  rewrite hex_d14 in Hr.
  replace (4 * (ex / 4) - 52 + 4 * (13 - p)) with (4 * (ex / 4) - 4 * p)
    in Hr by ring.
  split.
  + exact (digits_nonneg _ _ (FIX_exp_valid (4 * (ex / 4) - 4 * p)) _ _ _ _
      (hex_nonneg m53 ex Hm) Hr).
  + (* With [p + 1] hex digits at [mag = ex / 4 + 1] in radix 16, the
       last kept digit is the digit [ex / 4 - p], whose lowest bit is the
       bit [4 * (ex / 4) - 4 * p]. *)
    rewrite Hxr, round_sign. f_equal.
    rewrite (round_FLX_FIX radix16 (p + 1) _ _ (ex / 4 - p))
      by (rewrite mag_hex16 by lia; ring).
    rewrite round_radix16_FIX.
    replace (4 * (ex / 4 - p)) with (4 * (ex / 4) - 4 * p) by ring.
    exact Hr.
- rewrite (Hge p) by lia.
  exists (m53 * 2^(ex mod 4)), (4 * (ex / 4) - 52).
  split; [reflexivity|]. split; [lia|].
  rewrite hex_d14, Hxr, round_sign. f_equal.
  (* The 14 hex digits of [d14] are at most [p + 1], so [x] is a number of
     [p + 1] hex digits, which every rounding keeps. *)
  assert (Hprec : Prec_gt_0 (p + 1)) by (unfold Prec_gt_0; lia).
  assert (Hf : generic_format radix16 (FLX_exp (p + 1))
                 (IZR m53 * bpow radix2 (ex - 52))%R).
  { rewrite <- hex_d14. apply generic_format_FLX.
    apply (FLX_spec radix16 (p + 1) _
      (Float radix16 (m53 * 2^(ex mod 4)) (ex / 4 - 13))).
    - unfold F2R. cbn [Fnum Fexp]. rewrite bpow_radix16.
      do 2 f_equal. ring.
    - cbn [Fnum]. rewrite Z.abs_eq by lia.
      apply Z.lt_le_trans with (2^56); [lia|].
      change (2^56) with (Zpower radix16 14). apply Zpower_le. lia. }
  symmetry.
  destruct (negb (Bool.eqb (Bsign x) up));
    (apply round_generic; [typeclasses eauto | exact Hf]).
Qed.
