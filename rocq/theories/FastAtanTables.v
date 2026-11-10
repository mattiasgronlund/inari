(** * The table and constants of the fast path of atan

    [DyadicAtan.ATAN_TABLE] of [Model.v] gives, for [i = 1, ..., 64],
    atan(i/64) in double-double [th + tl] within [2^-104]
    ([fast_atan_table_correct]); entry 0 is not read. [PIO2] is π/2 in
    double-double within [2^-107] ([fast_pio2_correct]), [A3] is 1/3 in
    double-double within [2^-109], and [A5], ..., [A11] are 1/5, ...,
    1/11 rounded to nearest ([fast_atan_consts]).

    Each entry is checked by [vm_compute] on integers, as in
    [FastLogTables.v]. The partial sums of the series of atan at a
    rational [x = a / b >= 0] are computed in integer fixed point with
    [P = 160] fractional bits: the term [j] is the single quotient
    [2^P (-1)^j a^(2j+1) / ((2j+1) b^(2j+1))] of exact integers, rounded
    down in [az_sum false] and up in [az_sum true]. As [x >= 0], the
    remainder of [AtanSeries.atan_tail_bounds] puts atan x between the
    sums of the first [56] and [57] terms ([az_atan_bounds]). For
    [i <= 32] the series is taken at [i/64 <= 1/2]; for [i > 32],
    atan(i/64) = π/4 - atan((64 - i)/(64 + i))
    ([AtanIdent.atan_quarter_minus]), with the series at [(64 - i)/(64 +
    i) <= 31/97] and π from [DyConstPi.PI_bounds]. Both bounds are
    compared at the scale [2^-4224] of π/4. As in [DyConstPi.v], the
    4,224-bit integer behind π stays behind a variable in every lemma
    that a tactic other than [vm_compute] works on.

    The constants: [PIO2] is checked against [PI_bounds] by
    [FastExpTables.dd_close], and each [RN (1 / n)] is the float whose
    significand is the integer nearest to [2^(53 - e) / n], where [2^(e -
    1) <= 1 / n < 2^e] ([rn_lit]). *)

From Stdlib Require Import ZArith Reals Lra Lia List Bool.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model TwoSum Elementary AtanSeries AtanIdent DyConstPi FastExpTables.

Import ListNotations.

Open Scope R_scope.

(** ** Helpers *)

Local Lemma at_pow2 : forall e, (0 <= e)%Z -> IZR (2 ^ e) = bpow radix2 e.
Proof. intros e He. rewrite <- IZR_Zpower by exact He. reflexivity. Qed.

(** [X 2^p <= Y 2^q], checked on integers at the scale [2^E], with the
    power of two first for [vm_compute] *)
Local Lemma at_cmp :
  forall X Y p q E, (E <= p)%Z -> (E <= q)%Z -> (2 ^ (p - E) * X <= 2 ^ (q - E) * Y)%Z ->
  IZR X * bpow radix2 p <= IZR Y * bpow radix2 q.
Proof.
intros X Y p q E Hp Hq H.
apply IZR_le in H. rewrite !mult_IZR, !at_pow2 in H by lia.
apply (Rmult_le_compat_r (bpow radix2 E)) in H; [|apply bpow_ge_0].
replace (bpow radix2 (p - E) * IZR X * bpow radix2 E)
  with (IZR X * (bpow radix2 (p - E) * bpow radix2 E)) in H by ring.
replace (bpow radix2 (q - E) * IZR Y * bpow radix2 E)
  with (IZR Y * (bpow radix2 (q - E) * bpow radix2 E)) in H by ring.
rewrite <- !bpow_plus in H.
replace (p - E + E)%Z with p in H by ring. replace (q - E + E)%Z with q in H by ring.
exact H.
Qed.

Local Lemma at_abs : forall X e, Rabs (IZR X * bpow radix2 e) = IZR (Z.abs X) * bpow radix2 e.
Proof.
intros X e. rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 e)) by apply bpow_ge_0.
rewrite abs_IZR. reflexivity.
Qed.

Local Lemma at_bpow_succ : forall e, bpow radix2 (e + 1) = 2 * bpow radix2 e.
Proof. intros e. rewrite bpow_plus. change (bpow radix2 1) with 2. ring. Qed.

(** [B2R l] of an [f64] literal [l], as [m * 2^e] (as in [FastHypPos.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** Each [bpow radix2 e] of the goal with a closed exponent [e] as a
    literal, then as a constant for [lra] *)
Local Ltac bpow_lit :=
  repeat match goal with
  | |- context [bpow radix2 ?e] =>
      let v := eval vm_compute in e in progress change e with v
  end;
  cbn [bpow radix_val radix2].

(** ** Rounding to nearest of a real *)

(** For [2^(e-1) <= r < 2^e] in the normal range, [RN r] is the
    significand nearest to [r 2^(53-e)], times [2^(e-53)]. *)
Local Lemma rn_lit :
  forall r M e, (-1021 <= e)%Z -> bpow radix2 (e - 1) <= r < bpow radix2 e ->
  Rabs (r * bpow radix2 (53 - e) - IZR M) < / 2 ->
  RN r = IZR M * bpow radix2 (e - 53).
Proof.
intros r M e He Hr HM.
unfold round, scaled_mantissa, cexp.
rewrite (mag_unique_pos radix2 r e Hr).
unfold FLT_exp. rewrite Z.max_l by lia.
unfold F2R. cbn [Fnum Fexp].
rewrite (Znearest_imp _ _ M); [reflexivity|].
replace (- (e - 53))%Z with (53 - e)%Z by ring. exact HM.
Qed.

(** ** The partial sums of atan in integer fixed point *)

(** [x / y] rounded down, or up if [up], for [y > 0] *)
Local Definition at_div (up : bool) (x y : Z) : Z := if up then (- (- x / y))%Z else (x / y)%Z.

(** [y] is above [x] if [up], below it otherwise *)
Local Definition at_dir (up : bool) (x y : R) : Prop := if up then x <= y else y <= x.

Local Lemma at_dir_trans : forall up x y z, at_dir up x y -> at_dir up y z -> at_dir up x z.
Proof. intros [|] x y z; cbn [at_dir]; lra. Qed.

Local Lemma at_dir_eq : forall up x y, x = y -> at_dir up x y.
Proof. intros [|] x y ->; cbn [at_dir]; lra. Qed.

Local Lemma at_dir_plus :
  forall up x y x' y', at_dir up x y -> at_dir up x' y' -> at_dir up (x + x') (y + y').
Proof. intros [|] x y x' y'; cbn [at_dir]; lra. Qed.

Local Lemma at_div_dir :
  forall up x y, (0 < y)%Z -> at_dir up (IZR x / IZR y) (IZR (at_div up x y)).
Proof.
intros up x y Hy.
assert (HY : 0 < IZR y) by (apply IZR_lt; exact Hy).
destruct up; cbn [at_dir at_div]; apply (Rmult_le_reg_r (IZR y)); try exact HY;
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
- pose proof (Z.mul_div_le (- x) y Hy) as H. apply IZR_le in H.
  rewrite mult_IZR, opp_IZR in H. rewrite opp_IZR. lra.
- pose proof (Z.mul_div_le x y Hy) as H. apply IZR_le in H. rewrite mult_IZR in H. lra.
Qed.

(** The term [j] of the series at [a / b], times [2^P]:
    [2^P (-1)^j a^(2j+1) / ((2j+1) b^(2j+1))], rounded down, or up if
    [up] *)
Local Definition az_term (up : bool) (P a b : Z) (j : nat) : Z :=
  at_div up (2 ^ P * (-1) ^ Z.of_nat j * a ^ Z.of_nat (2 * j + 1))
    (Z.of_nat (2 * j + 1) * b ^ Z.of_nat (2 * j + 1)).

(** The sum of the first [n] terms *)
Local Fixpoint az_sum (up : bool) (P a b : Z) (n : nat) : Z :=
  match n with
  | O => 0%Z
  | S m => (az_sum up P a b m + az_term up P a b m)%Z
  end.

Local Lemma az_term_dir :
  forall up P a b j, (0 <= P)%Z -> (0 < b)%Z ->
  at_dir up (bpow radix2 P * ((-1) ^ j * (IZR a / IZR b) ^ (2 * j + 1) / INR (2 * j + 1)))
    (IZR (az_term up P a b j)).
Proof.
intros up P a b j HP Hb.
assert (HB : 0 < IZR b) by (apply IZR_lt; exact Hb).
assert (Hk : (0 < Z.of_nat (2 * j + 1))%Z) by lia.
assert (HK : 0 < IZR (Z.of_nat (2 * j + 1))) by (apply IZR_lt; exact Hk).
assert (Hd : (0 < Z.of_nat (2 * j + 1) * b ^ Z.of_nat (2 * j + 1))%Z)
  by (apply Z.mul_pos_pos; [exact Hk | apply Z.pow_pos_nonneg; lia]).
unfold az_term.
apply at_dir_trans with
  (IZR (2 ^ P * (-1) ^ Z.of_nat j * a ^ Z.of_nat (2 * j + 1)) /
   IZR (Z.of_nat (2 * j + 1) * b ^ Z.of_nat (2 * j + 1))); [| apply at_div_dir; exact Hd].
apply at_dir_eq.
rewrite !mult_IZR, at_pow2 by exact HP. rewrite <- !pow_IZR, INR_IZR_INZ.
assert (HBk : 0 < IZR b ^ (2 * j + 1)) by (apply pow_lt; exact HB).
unfold Rdiv. rewrite Rpow_mult_distr, pow_inv. field.
split; apply Rgt_not_eq; assumption.
Qed.

Local Lemma az_sum_dir :
  forall up P a b n, (0 <= P)%Z -> (0 < b)%Z ->
  at_dir up (bpow radix2 P * atan_sum n (IZR a / IZR b)) (IZR (az_sum up P a b n)).
Proof.
intros up P a b n HP Hb. induction n as [| m IH].
- cbn [atan_sum az_sum]. apply at_dir_eq. ring.
- cbn [atan_sum az_sum]. rewrite plus_IZR, Rmult_plus_distr_l.
  apply at_dir_plus; [exact IH | apply az_term_dir; assumption].
Qed.

(** For [a / b >= 0], atan(a / b) lies between the sums of the first
    [2k] and [2k + 1] terms. *)
Local Lemma az_atan_bounds :
  forall P k a b, (0 <= P)%Z -> (0 <= a)%Z -> (0 < b)%Z ->
  IZR (az_sum false P a b (2 * k)) * bpow radix2 (- P) <= atan (IZR a / IZR b) <=
  IZR (az_sum true P a b (S (2 * k))) * bpow radix2 (- P).
Proof.
intros P k a b HP Ha Hb.
set (x := IZR a / IZR b).
assert (Hx : 0 <= x).
{ unfold x, Rdiv. apply Rmult_le_pos; [apply IZR_le; exact Ha |].
  apply Rlt_le, Rinv_0_lt_compat, IZR_lt. exact Hb. }
destruct (atan_tail_bounds (2 * k) x) as [T [[T0 T1] HT]].
rewrite pow_1_even, Rmult_1_l in HT.
set (p := x ^ (2 * (2 * k) + 1)) in *.
assert (Hp : 0 <= p) by (apply pow_le; exact Hx).
assert (HI : 0 < INR (2 * (2 * k) + 1)) by (apply lt_0_INR; lia).
assert (L : atan_sum (2 * k) x <= atan x).
{ assert (0 <= T * p) by (apply Rmult_le_pos; assumption). lra. }
assert (U : atan x <= atan_sum (S (2 * k)) x).
{ cbn [atan_sum]. rewrite pow_1_even, Rmult_1_l. fold p.
  assert (T * p <= 1 / INR (2 * (2 * k) + 1) * p) by (apply Rmult_le_compat_r; assumption).
  replace (p / INR (2 * (2 * k) + 1)) with (1 / INR (2 * (2 * k) + 1) * p) by (field; lra).
  lra. }
assert (HC : bpow radix2 P * bpow radix2 (- P) = 1).
{ rewrite <- bpow_plus, Z.add_opp_diag_r. reflexivity. }
assert (Hm : 0 <= bpow radix2 (- P)) by apply bpow_ge_0.
pose proof (az_sum_dir false P a b (2 * k) HP Hb) as D1. cbn [at_dir] in D1.
pose proof (az_sum_dir true P a b (S (2 * k)) HP Hb) as D2. cbn [at_dir] in D2.
fold x in D1, D2.
apply (Rmult_le_compat_r _ _ _ Hm) in D1. apply (Rmult_le_compat_r _ _ _ Hm) in D2.
replace (bpow radix2 P * atan_sum (2 * k) x * bpow radix2 (- P))
  with (atan_sum (2 * k) x * (bpow radix2 P * bpow radix2 (- P))) in D1 by ring.
replace (bpow radix2 P * atan_sum (S (2 * k)) x * bpow radix2 (- P))
  with (atan_sum (S (2 * k)) x * (bpow radix2 P * bpow radix2 (- P))) in D2 by ring.
rewrite HC, Rmult_1_r in D1, D2.
split; lra.
Qed.

(** ** The bounds of atan(i/64) *)

(** Half the number of terms *)
Local Definition at_K : nat := 28.

(** The lower and upper bounds of [2^4224 atan(i/64)], for [Pi] the
    integer below [2^4222 π] *)
Local Definition at_lo (Pi i : Z) : Z :=
  if (i <=? 32)%Z then (2 ^ 4064 * az_sum false 160 i 64 (2 * at_K))%Z
  else (Pi - 2 ^ 4064 * az_sum true 160 (64 - i) (64 + i) (S (2 * at_K)))%Z.

Local Definition at_hi (Pi i : Z) : Z :=
  if (i <=? 32)%Z then (2 ^ 4064 * az_sum true 160 i 64 (S (2 * at_K)))%Z
  else (Pi + 1 - 2 ^ 4064 * az_sum false 160 (64 - i) (64 + i) (2 * at_K))%Z.

Local Lemma at_scale :
  forall S, IZR (2 ^ 4064 * S) * bpow radix2 (-4224) = IZR S * bpow radix2 (-160).
Proof.
intros S. rewrite mult_IZR, at_pow2 by lia.
replace (bpow radix2 (-160)) with (bpow radix2 4064 * bpow radix2 (-4224))
  by (rewrite <- bpow_plus; reflexivity).
ring.
Qed.

Local Lemma at_bounds :
  forall Pi i,
  IZR Pi * bpow radix2 (-4222) <= PI < (IZR Pi + 1) * bpow radix2 (-4222) ->
  (1 <= i <= 64)%Z ->
  IZR (at_lo Pi i) * bpow radix2 (-4224) <= atan (IZR i / 64) <=
  IZR (at_hi Pi i) * bpow radix2 (-4224).
Proof.
intros Pi i [HP1 HP2] Hi.
unfold at_lo, at_hi.
destruct (Z.leb_spec i 32) as [Hle | Hgt].
- rewrite !at_scale.
  exact (az_atan_bounds 160 at_K i 64 ltac:(lia) ltac:(lia) ltac:(lia)).
- (* atan(i/64) = π/4 - atan((64 - i)/(64 + i)) *)
  assert (HI : 1 <= IZR i) by (apply IZR_le; lia).
  rewrite (atan_quarter_minus (IZR i / 64)) by lra.
  replace ((1 - IZR i / 64) / (1 + IZR i / 64)) with (IZR (64 - i) / IZR (64 + i))
    by (rewrite minus_IZR, plus_IZR; field; lra).
  destruct (az_atan_bounds 160 at_K (64 - i) (64 + i) ltac:(lia) ltac:(lia) ltac:(lia))
    as [L U].
  change (Z.opp 160) with (-160)%Z in L, U.
  set (A := atan (IZR (64 - i) / IZR (64 + i))) in *.
  rewrite !minus_IZR, !plus_IZR, !Rmult_minus_distr_r, !at_scale.
  assert (E : bpow radix2 (-4222) = 4 * bpow radix2 (-4224)).
  { replace (-4222)%Z with ((-4224 + 1) + 1)%Z by reflexivity.
    rewrite !at_bpow_succ. ring. }
  rewrite E in HP1, HP2.
  split; lra.
Qed.

(** ** The table *)

(** The check of the entry [i >= 1], [(th, tl)] as bits at 160
    fractional bits, each test in the form of [at_cmp] *)
Local Definition at_entry_okb (Pi i : Z) (e : Z * Z) : bool :=
  (i <=? 0)%Z ||
  match fix_of 160 (from_bits (fst e)), fix_of 160 (from_bits (snd e)) with
  | Some H, Some L =>
      (2 ^ 153 * 1 <=? 2 ^ 0 * H)%Z && (2 ^ 0 * (5 * H) <=? 2 ^ 160 * 4)%Z &&
      (2 ^ 53 * Z.abs L <=? 2 ^ 0 * H)%Z &&
      (2 ^ 4064 * (H + L - 2 ^ 56) <=? 2 ^ 0 * at_lo Pi i)%Z &&
      (2 ^ 0 * at_hi Pi i <=? 2 ^ 4064 * (H + L + 2 ^ 56))%Z
  | _, _ => false
  end.

Local Lemma at_entry_correct :
  forall Pi i hb lb,
  IZR Pi * bpow radix2 (-4222) <= PI < (IZR Pi + 1) * bpow radix2 (-4222) ->
  (1 <= i <= 64)%Z -> at_entry_okb Pi i (hb, lb) = true ->
  is_finite (from_bits hb) = true /\ is_finite (from_bits lb) = true /\
  bpow radix2 (-7) <= B2R (from_bits hb) <= 4 / 5 /\
  Rabs (B2R (from_bits lb)) <= bpow radix2 (-53) * B2R (from_bits hb) /\
  Rabs (B2R (from_bits hb) + B2R (from_bits lb) - atan (IZR i / 64)) <= bpow radix2 (-104).
Proof.
intros Pi i hb lb HPi Hi Hok.
pose proof (at_bounds Pi i HPi Hi) as [B1 B2].
unfold at_entry_okb in Hok. cbn [fst snd] in Hok.
rewrite (proj2 (Z.leb_gt i 0)) in Hok by lia. rewrite orb_false_l in Hok.
destruct (fix_of 160 (from_bits hb)) as [H|] eqn:EH; [|discriminate Hok].
destruct (fix_of 160 (from_bits lb)) as [L|] eqn:EL; [|discriminate Hok].
apply fix_of_correct in EH as [Fh Rh]. apply fix_of_correct in EL as [Fl Rl].
change (Z.opp 160) with (-160)%Z in Rh, Rl.
rewrite Rh, Rl.
repeat rewrite andb_true_iff in Hok.
destruct Hok as [[[[H1 H2] H3] H4] H5].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
apply Z.leb_le in H4. apply Z.leb_le in H5.
pose proof (at_cmp 1 H (-7) (-160) (-160) ltac:(lia) ltac:(lia) H1) as K1.
pose proof (at_cmp (5 * H) 4 (-160) 0 (-160) ltac:(lia) ltac:(lia) H2) as K2.
pose proof (at_cmp (Z.abs L) H (-160) (-213) (-213) ltac:(lia) ltac:(lia) H3) as K3.
pose proof (at_cmp _ _ (-160) (-4224) (-4224) ltac:(lia) ltac:(lia) H4) as K4.
pose proof (at_cmp _ _ (-4224) (-160) (-4224) ltac:(lia) ltac:(lia) H5) as K5.
rewrite mult_IZR in K2. change (bpow radix2 0) with 1 in K2.
replace (bpow radix2 (-213)) with (bpow radix2 (-53) * bpow radix2 (-160)) in K3
  by (rewrite <- bpow_plus; reflexivity).
assert (K56 : IZR (2 ^ 56) * bpow radix2 (-160) = bpow radix2 (-104)).
{ rewrite at_pow2, <- bpow_plus by lia. reflexivity. }
rewrite minus_IZR, plus_IZR in K4. rewrite !plus_IZR in K5.
assert (Hb0 : 0 < bpow radix2 (-160)) by apply bpow_gt_0.
split; [exact Fh|]. split; [exact Fl|].
split; [split; lra|].
split.
{ rewrite at_abs. lra. }
apply Rabs_le. split; lra.
Qed.

Local Fixpoint at_all_okb (Pi : Z) (t : list (Z * Z)) (i : Z) : bool :=
  match t with
  | [] => true
  | e :: t => at_entry_okb Pi i e && at_all_okb Pi t (i + 1)
  end.

Local Lemma at_all_okb_nth :
  forall Pi t i0 k, at_all_okb Pi t i0 = true -> (k < length t)%nat ->
  at_entry_okb Pi (i0 + Z.of_nat k) (nth k t (0, 0)%Z) = true.
Proof.
intros Pi t; induction t as [|p t IH]; intros i0 k H Hk; [cbn [length] in Hk; lia|].
cbn [at_all_okb] in H. apply andb_prop in H as [H1 H2].
destruct k as [|k]; cbn [nth].
- replace (i0 + Z.of_nat 0)%Z with i0 by lia. exact H1.
- replace (i0 + Z.of_nat (S k))%Z with ((i0 + 1) + Z.of_nat k)%Z by lia.
  apply IH; [exact H2 | cbn [length] in Hk; lia].
Qed.

(** The check of all 65 entries ([vm_compute]) *)
Local Lemma at_table_ok : at_all_okb (Limbs.val DyadicConsts.PI) DyadicAtan.ATAN_TABLE 0 = true.
Proof. vm_compute. reflexivity. Qed.

Local Lemma at_table_length : length DyadicAtan.ATAN_TABLE = 65%nat.
Proof. vm_compute. reflexivity. Qed.

(** Each entry [i >= 1]: atan(i/64) within [2^-104], with [|tl| <= 2^-53
    th] and [th] between [2^-7] and [4/5]. *)
Theorem fast_atan_table_correct :
  forall i, (1 <= i <= 64)%Z ->
  let '(th, tl) := DyadicAtan.atbl i in
  is_finite th = true /\ is_finite tl = true /\
  bpow radix2 (-7) <= B2R th <= 4 / 5 /\ Rabs (B2R tl) <= bpow radix2 (-53) * B2R th /\
  Rabs (B2R th + B2R tl - atan (IZR i / 64)) <= bpow radix2 (-104).
Proof.
intros i Hi.
pose proof (at_all_okb_nth _ DyadicAtan.ATAN_TABLE 0 (Z.to_nat i) at_table_ok
              ltac:(rewrite at_table_length; lia)) as He.
rewrite Z.add_0_l, Z2Nat.id in He by lia.
unfold DyadicAtan.atbl.
set (p := nth (Z.to_nat i) DyadicAtan.ATAN_TABLE (0, 0)%Z) in He |- *.
clearbody p. destruct p as [hb lb].
revert He. generalize PI_bounds. generalize (Limbs.val DyadicConsts.PI).
intros Pi HPi He.
exact (at_entry_correct Pi i hb lb HPi Hi He).
Qed.

(** ** The constants *)

(** π/2 in double-double. *)
Theorem fast_pio2_correct :
  is_finite (from_bits (fst DyadicAtan.PIO2)) = true /\
  is_finite (from_bits (snd DyadicAtan.PIO2)) = true /\
  B2R (from_bits (fst DyadicAtan.PIO2)) = 884279719003555 / 562949953421312 /\
  Rabs (B2R (from_bits (snd DyadicAtan.PIO2))) <= bpow radix2 (-53) /\
  Rabs (B2R (from_bits (fst DyadicAtan.PIO2)) + B2R (from_bits (snd DyadicAtan.PIO2)) - PI / 2)
    <= bpow radix2 (-107).
Proof.
(* [fix_of] keeps the whole 53-bit significand: [hi = 7074237752028440 2^-52]. *)
assert (EH : fix_of 52 (from_bits (fst DyadicAtan.PIO2)) = Some 7074237752028440%Z)
  by (vm_compute; reflexivity).
assert (EL : fix_of 106 (from_bits (snd DyadicAtan.PIO2)) = Some 4967757600021511%Z)
  by (vm_compute; reflexivity).
apply fix_of_correct in EH as [Fh Rh]. apply fix_of_correct in EL as [Fl Rl].
split; [exact Fh|]. split; [exact Fl|].
split.
{ rewrite Rh. bpow_lit. lra. }
split.
{ rewrite Rl, at_abs.
  rewrite <- (Rmult_1_l (bpow radix2 (-53))).
  apply (at_cmp _ 1 (-106) (-53) (-106)); [lia | lia | apply Z.leb_le; vm_compute; reflexivity]. }
apply (dd_close _ _ 160 (Limbs.val DyadicConsts.PI) (-4223) (-107)).
- vm_compute. reflexivity.
- generalize PI_bounds. generalize (Limbs.val DyadicConsts.PI). intros Pi [H1 H2].
  assert (E : bpow radix2 (-4222) = 2 * bpow radix2 (-4223)).
  { replace (-4222)%Z with (-4223 + 1)%Z by reflexivity. apply at_bpow_succ. }
  rewrite E in H1, H2. split; lra.
Qed.

(** The coefficients of the polynomial of [FastAtanPoly.v]. *)
Theorem fast_atan_consts :
  is_finite (from_bits (fst DyadicAtan.A3)) = true /\
  is_finite (from_bits (snd DyadicAtan.A3)) = true /\
  B2R (from_bits (fst DyadicAtan.A3)) = RN (1 / 3) /\
  Rabs (B2R (from_bits (fst DyadicAtan.A3)) + B2R (from_bits (snd DyadicAtan.A3)) - 1 / 3)
    <= bpow radix2 (-109) /\
  is_finite (from_bits DyadicAtan.A5) = true /\ B2R (from_bits DyadicAtan.A5) = RN (1 / 5) /\
  is_finite (from_bits DyadicAtan.A7) = true /\ B2R (from_bits DyadicAtan.A7) = RN (1 / 7) /\
  is_finite (from_bits DyadicAtan.A9) = true /\ B2R (from_bits DyadicAtan.A9) = RN (1 / 9) /\
  is_finite (from_bits DyadicAtan.A11) = true /\ B2R (from_bits DyadicAtan.A11) = RN (1 / 11).
Proof.
(* Each [RN (1 / n)] by [rn_lit] at [e = mag (1 / n)], and the literal by [lit_B2R]. *)
assert (R3 : B2R (from_bits (fst DyadicAtan.A3)) = RN (1 / 3)).
{ rewrite (rn_lit _ 6004799503160661 (-1)); [lit_B2R; reflexivity | lia | bpow_lit; split; lra |].
  bpow_lit. apply Rabs_def1; lra. }
assert (R5 : B2R (from_bits DyadicAtan.A5) = RN (1 / 5)).
{ rewrite (rn_lit _ 7205759403792794 (-2)); [lit_B2R; reflexivity | lia | bpow_lit; split; lra |].
  bpow_lit. apply Rabs_def1; lra. }
assert (R7 : B2R (from_bits DyadicAtan.A7) = RN (1 / 7)).
{ rewrite (rn_lit _ 5146971002709138 (-2)); [lit_B2R; reflexivity | lia | bpow_lit; split; lra |].
  bpow_lit. apply Rabs_def1; lra. }
assert (R9 : B2R (from_bits DyadicAtan.A9) = RN (1 / 9)).
{ rewrite (rn_lit _ 8006399337547548 (-3)); [lit_B2R; reflexivity | lia | bpow_lit; split; lra |].
  bpow_lit. apply Rabs_def1; lra. }
assert (R11 : B2R (from_bits DyadicAtan.A11) = RN (1 / 11)).
{ rewrite (rn_lit _ 6550690367084358 (-3)); [lit_B2R; reflexivity | lia | bpow_lit; split; lra |].
  bpow_lit. apply Rabs_def1; lra. }
(* [A3] in double-double: [hi + lo - 1/3 = -2^-108 / 3]. *)
assert (E3 : Rabs (B2R (from_bits (fst DyadicAtan.A3)) + B2R (from_bits (snd DyadicAtan.A3)) - 1 / 3)
             <= bpow radix2 (-109)).
{ assert (EH : fix_of 108 (from_bits (fst DyadicAtan.A3)) =
               Some 108172851219475569589585837031424%Z) by (vm_compute; reflexivity).
  assert (EL : fix_of 108 (from_bits (snd DyadicAtan.A3)) = Some 6004799503160661%Z)
    by (vm_compute; reflexivity).
  apply fix_of_correct in EH as [_ Rh]. apply fix_of_correct in EL as [_ Rl].
  rewrite Rh, Rl. bpow_lit. apply Rabs_le. split; lra. }
refine (conj _ (conj _ (conj R3 (conj E3 (conj _ (conj R5 (conj _ (conj R7 (conj _ (conj R9
  (conj _ R11))))))))))); vm_compute; reflexivity.
Qed.
