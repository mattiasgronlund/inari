(** * No finite [f64] is within 2^-61 of a multiple of π/2 other than 0

    The distance from a finite [f64] [x] to a multiple [k π/2], [k <> 0],
    is at least 2^-61 ([km_distance]). Kahan and McDonald's search (J.-M.
    Muller, Elementary Functions, 3rd ed., the chapter on range
    reduction) puts the minimum near 2^-60.9, at 6381956970095103 ×
    2^797; this file proves only the bound 2^-61. The proof needs no
    theory of continued fractions. For [|x| < 1] the distance is above
    [π/2 - 1]. Otherwise [x = m 2^e] with [2^52 <= m < 2^53] and [-52 <=
    e <= 971], and [|x - k π/2| = (π/2) |m α - k|] with [α = 2^(e+1)/π].
    For each [e], [vm_compute] brackets the fractional part of [α] by
    two integers over a power of 2, from the bounds of π of [PI_bounds]
    ([DyConstPi.v]), runs Euclid's algorithm on the bracket for two
    pairs [(q, p)] and [(q', p')] with [|q p' - p q'| = 1], [q' >= 2^53]
    and residues [q α - p] and [q' α - p'] of opposite signs, and checks
    that [|q α - p|] is large enough at both ends of the bracket. Every
    [0 < m < q'] and integer [j] then have [|m α - j| >= |q α - p|], by
    writing [(m, j)] in the basis [(q, p)], [(q', p')].

    As in [DyConstPi.v], the 5,394-bit numbers stay behind definitions
    ([km_tlo], [km_thi]) in every lemma that a tactic other than
    [vm_compute] works on, and in the [Z] products that [vm_compute]
    evaluates, the power of two comes first. *)

From Stdlib Require Import ZArith Reals Lra Lia List Bool.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs DyConstPi.

Open Scope R_scope.

(** ** Helpers *)

Lemma km_IZR_pow2 : forall n, (0 <= n)%Z -> IZR (2 ^ n) = bpow radix2 n.
Proof. intros n Hn. rewrite <- IZR_Zpower by exact Hn. reflexivity. Qed.

(** [|a| <= |a + b|] when [a] and [b] do not have opposite signs. *)
Lemma km_abs_add : forall a b, 0 <= a * b -> Rabs a <= Rabs (a + b).
Proof.
intros a b H.
destruct (Rle_dec 0 a) as [Ha | Ha]; destruct (Rle_dec 0 b) as [Hb | Hb].
- rewrite !Rabs_pos_eq by lra. lra.
- (* [a b >= 0] with [b < 0] leaves [a = 0]. *)
  assert (a = 0) by nra. subst a. rewrite Rabs_R0. apply Rabs_pos.
- assert (b = 0) by nra. subst b. rewrite Rplus_0_r. lra.
- rewrite !Rabs_left by lra. lra.
Qed.

(** ** The unimodular basis *)

(** If [(q, p)] and [(q', p')] are a basis of [Z^2] ([|q p' - p q'| = 1])
    whose residues [q Y - p P] and [q' Y - p' P] do not have the same
    strict sign, every [(m, j)] with [0 < m < q'] has a residue at least
    [|q Y - p P|]. With [D = q p' - p q'], [(m, j) = u (q, p) + v (q', p')]
    for [u = D (m p' - j q')] and [v = D (j q - m p)]. [u = 0] would make
    [m] a multiple of [q'], and [u], [v] of the same strict sign would put
    [m] outside [(0, q')], so [u <> 0] and [u v <= 0]: the two terms of
    [m Y - j P = u r + v r'] then do not cancel, and [|u| >= 1]. ([P = 1]
    is the usual statement for [α = Y]; a general [P] lets [Y] and [P] be
    the window of [α] scaled by a power of 2.) *)
Lemma km_unimodular :
  forall (q p q' p' m j : Z) (Y P : R),
  Z.abs (q * p' - p * q') = 1%Z ->
  (0 <= q)%Z -> (0 < m < q')%Z ->
  (IZR q * Y - IZR p * P) * (IZR q' * Y - IZR p' * P) <= 0 ->
  Rabs (IZR q * Y - IZR p * P) <= Rabs (IZR m * Y - IZR j * P).
Proof.
intros q p q' p' m j Y P Hd Hq Hm Hs.
remember (q * p' - p * q')%Z as D eqn:ED.
assert (HD : (D * D = 1)%Z) by (assert (D = 1 \/ D = -1)%Z as [-> | ->] by lia; reflexivity).
set (u := (D * (m * p' - j * q'))%Z).
set (v := (D * (j * q - m * p))%Z).
assert (Hmq : (u * q + v * q' = m)%Z).
{ transitivity (D * D * m)%Z; [unfold u, v; rewrite ED; ring | rewrite HD; ring]. }
assert (Hjp : (u * p + v * p' = j)%Z).
{ transitivity (D * D * j)%Z; [unfold u, v; rewrite ED; ring | rewrite HD; ring]. }
assert (Hr : IZR m * Y - IZR j * P =
             IZR u * (IZR q * Y - IZR p * P) + IZR v * (IZR q' * Y - IZR p' * P)).
{ rewrite <- Hmq, <- Hjp, !plus_IZR, !mult_IZR. ring. }
clearbody u v.
assert (Huv : ((1 <= u /\ v <= 0) \/ (u <= -1 /\ 0 <= v))%Z).
{ destruct (Z.lt_trichotomy u 0) as [Hu | [Hu | Hu]];
    destruct (Z.lt_trichotomy v 0) as [Hv | [Hv | Hv]]; try lia; subst; nia. }
rewrite Hr.
set (r := IZR q * Y - IZR p * P) in *.
set (r' := IZR q' * Y - IZR p' * P) in *.
clearbody r r'.
assert (Hu : 1 <= Rabs (IZR u)).
{ destruct Huv as [[H1 _] | [H1 _]]; apply IZR_le in H1.
  - rewrite Rabs_pos_eq by lra. lra.
  - rewrite Rabs_left by lra. lra. }
assert (Hp : 0 <= (IZR u * r) * (IZR v * r')).
{ assert (Huv' : IZR u * IZR v <= 0).
  { destruct Huv as [[H1 H2] | [H1 H2]]; apply IZR_le in H1, H2; nra. }
  replace ((IZR u * r) * (IZR v * r')) with ((IZR u * IZR v) * (r * r')) by ring.
  nra. }
apply (Rle_trans _ (Rabs (IZR u * r))); [| exact (km_abs_add _ _ Hp)].
rewrite Rabs_mult.
pose proof (Rabs_pos r). nra.
Qed.

(** ** The checker *)

(** The window: [frac(α)] is bracketed to [2^-km_W]. *)
Definition km_W : Z := 200.

(** [2^km_N / π] is bracketed once; [α 2^km_W = 2^(e + 1 + km_W) / π] is
    it shifted right by [km_N - (e + 1 + km_W) >= 0] for every [e <= 971]. *)
Definition km_N : Z := 1172.

(** Euclid's algorithm on the residues: [(q, p)] and [(q', p')] with
    residues [r = q a - p 2^W] and [r' = q' a - p' 2^W] of opposite signs
    become [(q', p')] and [(q, p) + t (q', p')], [t = |r| / |r'|], until
    [q' >= 2^53]. The checker does not trust it: [km_cert_ok] checks the
    pair it returns. *)
Fixpoint km_euclid (fuel : nat) (q p r q' p' r' : Z) : Z * Z * Z * Z :=
  match fuel with
  | O => (q, p, q', p')
  | S f =>
    if ((2 ^ 53 <=? q') || (r' =? 0))%Z then (q, p, q', p')
    else
      let t := (Z.abs r / Z.abs r')%Z in
      km_euclid f q' p' r' (q + t * q') (p + t * p') (r + t * r')
  end.

(** [201 r >= 2^(km_W - 54)]: with [π >= 201/64] ([km_pi_lb]), a residue
    [r / 2^km_W] of [α] gives a distance [(π/2) r / 2^km_W >= 2^-61]. *)
Definition km_bound_ok (r : Z) : bool := (2 ^ (km_W - 54) <=? 201 * r)%Z.

(** The certificate [(q, p, q', p')] for a bracket [[a, a + d] / 2^km_W]
    of [frac(α)]: [0 <= q], [q' >= 2^53], [|q p' - p q'| = 1], and either
    [q β - p >= 2^(km_W - 54) / 201 / 2^km_W] and [q' β - p' <= 0], or
    the mirror, for every [β] in the bracket (both residues increase with
    [β], so the worse end decides each inequality). *)
Definition km_cert_ok (a d : Z) (c : Z * Z * Z * Z) : bool :=
  let '(q, p, q', p') := c in
  ((0 <=? q) && (2 ^ 53 <=? q') && (Z.abs (q * p' - p * q') =? 1) &&
   ((km_bound_ok (q * a - 2 ^ km_W * p) && (q' * (a + d) - 2 ^ km_W * p' <=? 0)) ||
    (km_bound_ok (2 ^ km_W * p - q * (a + d)) && (0 <=? q' * a - 2 ^ km_W * p'))))%Z.

Definition km_s (e : Z) : Z := (km_N - (e + 1 + km_W))%Z.

(** The check for one exponent [e], given [tlo <= 2^km_N / π <= thi]:
    [α 2^km_W] lies in [[tlo >> s, (thi >> s) + 1]], and its low [km_W]
    bits [a] bracket [frac(α) 2^km_W] up to the integer part. *)
Definition km_okb (tlo thi e : Z) : bool :=
  let lo := Z.shiftr tlo (km_s e) in
  let a := Z.land lo (Z.ones km_W) in
  ((0 <=? km_s e) &&
   km_cert_ok a (Z.shiftr thi (km_s e) + 1 - lo) (km_euclid 128 1 0 a 0 1 (- 2 ^ km_W)))%Z.

(** The bracket of [2^km_N / π] from the table of π *)
Definition km_tlo : Z :=
  (2 ^ (km_N + 4222) / (Limbs.val DyadicConsts.PI + 1))%Z.
Definition km_thi : Z :=
  (2 ^ (km_N + 4222) / Limbs.val DyadicConsts.PI + 1)%Z.

(** The exponents [-52] to [971] *)
Definition km_exps : list Z := map (fun i => Z.of_nat i - 52)%Z (seq 0 1024).

Lemma km_all_true : forallb (km_okb km_tlo km_thi) km_exps = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** ** Soundness of the check *)

Lemma km_cert_sound :
  forall a d c Y,
  km_cert_ok a d c = true ->
  IZR a <= Y <= IZR a + IZR d ->
  forall m j, (0 < m < 2 ^ 53)%Z ->
  bpow radix2 (km_W - 54) <= 201 * Rabs (IZR m * Y - IZR j * bpow radix2 km_W).
Proof.
intros a d [[[q p] q'] p'] Y H [HYl HYh] m j Hm.
unfold km_cert_ok in H.
apply andb_prop in H as [H Hor]. apply andb_prop in H as [H Hdet].
apply andb_prop in H as [Hq Hq'].
apply Z.leb_le in Hq, Hq'. apply Z.eqb_eq in Hdet.
assert (HW : (0 <= km_W)%Z) by (unfold km_W; lia).
assert (HB : IZR (2 ^ (km_W - 54)) = bpow radix2 (km_W - 54))
  by (apply km_IZR_pow2; unfold km_W; lia).
assert (HP : IZR (2 ^ km_W) = bpow radix2 km_W) by (apply km_IZR_pow2; exact HW).
set (P := bpow radix2 km_W) in *.
assert (Hq0 : 0 <= IZR q) by (apply IZR_le; exact Hq).
assert (Hq'0 : 0 <= IZR q').
{ apply IZR_le. assert (0 < 2 ^ 53)%Z by lia. lia. }
(* Both residues increase with [Y]. *)
assert (Hrl : IZR q * IZR a <= IZR q * Y) by (apply Rmult_le_compat_l; lra).
assert (Hrh : IZR q * Y <= IZR q * (IZR a + IZR d)) by (apply Rmult_le_compat_l; lra).
assert (Hr'l : IZR q' * IZR a <= IZR q' * Y) by (apply Rmult_le_compat_l; lra).
assert (Hr'h : IZR q' * Y <= IZR q' * (IZR a + IZR d)) by (apply Rmult_le_compat_l; lra).
assert (Hmq : (0 < m < q')%Z) by lia.
pose proof (bpow_gt_0 radix2 (km_W - 54)) as Hb0.
apply orb_prop in Hor as [Hc | Hc]; apply andb_prop in Hc as [Hb Hs];
  unfold km_bound_ok in Hb; apply Z.leb_le in Hb, Hs; apply IZR_le in Hb, Hs;
  rewrite HB, mult_IZR in Hb;
  rewrite ?minus_IZR, ?mult_IZR, HP in Hb, Hs; rewrite ?plus_IZR in Hb; rewrite ?plus_IZR in Hs.
- (* [q Y - p P >= 2^(km_W - 54) / 201] and [q' Y - p' P <= 0] *)
  assert (Hr : 0 <= IZR q * Y - IZR p * P) by lra.
  assert (Hr' : IZR q' * Y - IZR p' * P <= 0) by lra.
  assert (Hrr : (IZR q * Y - IZR p * P) * (IZR q' * Y - IZR p' * P) <= 0) by nra.
  pose proof (km_unimodular q p q' p' m j Y P Hdet Hq Hmq Hrr) as Hu.
  rewrite (Rabs_pos_eq _ Hr) in Hu. lra.
- (* the mirror *)
  assert (Hr : IZR q * Y - IZR p * P <= 0) by lra.
  assert (Hr' : 0 <= IZR q' * Y - IZR p' * P) by lra.
  assert (Hrr : (IZR q * Y - IZR p * P) * (IZR q' * Y - IZR p' * P) <= 0) by nra.
  pose proof (km_unimodular q p q' p' m j Y P Hdet Hq Hmq Hrr) as Hu.
  rewrite (Rabs_left1 _ Hr) in Hu. lra.
Qed.

(** [tlo <= 2^N / π <= thi] from a bracket [[L, L + 1] 2^-4222] of π *)
Lemma km_t_bounds_gen :
  forall (L N : Z), (0 < L)%Z -> (0 <= N)%Z ->
  IZR L * bpow radix2 (-4222) <= PI < (IZR L + 1) * bpow radix2 (-4222) ->
  IZR (2 ^ (N + 4222) / (L + 1)) <= bpow radix2 N / PI <=
  IZR (2 ^ (N + 4222) / L + 1).
Proof.
intros L N HL HN [H1 H2].
assert (HX0 : (0 <= 2 ^ (N + 4222))%Z) by (apply Z.pow_nonneg; lia).
assert (Hlo : ((L + 1) * (2 ^ (N + 4222) / (L + 1)) <= 2 ^ (N + 4222))%Z)
  by (apply Z.mul_div_le; lia).
assert (Hhi : (2 ^ (N + 4222) < L * (2 ^ (N + 4222) / L + 1))%Z)
  by (rewrite Z.add_1_r; apply Z.mul_succ_div_gt; lia).
assert (Ht0 : (0 <= 2 ^ (N + 4222) / (L + 1))%Z) by (apply Z.div_pos; lia).
assert (Ht1 : (0 <= 2 ^ (N + 4222) / L + 1)%Z)
  by (assert (0 <= 2 ^ (N + 4222) / L)%Z by (apply Z.div_pos; lia); lia).
apply IZR_le in Hlo, Ht0, Ht1. apply IZR_lt in Hhi.
rewrite mult_IZR, plus_IZR in Hlo. rewrite mult_IZR in Hhi.
assert (HX : IZR (2 ^ (N + 4222)) * bpow radix2 (-4222) = bpow radix2 N).
{ rewrite km_IZR_pow2 by lia. rewrite <- bpow_plus. f_equal. lia. }
set (X := IZR (2 ^ (N + 4222))) in *.
set (tl := IZR (2 ^ (N + 4222) / (L + 1))) in *.
set (th := IZR (2 ^ (N + 4222) / L + 1)) in *.
set (b := bpow radix2 (-4222)) in *.
assert (Hb : 0 < b) by apply bpow_gt_0.
pose proof PI_RGT_0 as HPI.
split.
- apply (Rmult_le_reg_r PI); [exact HPI |].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
  assert (tl * PI <= tl * ((IZR L + 1) * b)) by (apply Rmult_le_compat_l; lra).
  assert ((IZR L + 1) * tl * b <= X * b) by (apply Rmult_le_compat_r; lra).
  lra.
- apply (Rmult_le_reg_r PI); [exact HPI |].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
  assert (th * (IZR L * b) <= th * PI) by (apply Rmult_le_compat_l; lra).
  assert (X * b <= IZR L * th * b) by (apply Rmult_le_compat_r; lra).
  lra.
Qed.

Lemma km_L_pos : (0 < Limbs.val DyadicConsts.PI)%Z.
Proof. apply Z.ltb_lt. vm_compute. reflexivity. Qed.

Lemma km_t_bounds : IZR km_tlo <= bpow radix2 km_N / PI <= IZR km_thi.
Proof.
assert (HN : (0 <= km_N)%Z) by (unfold km_N; lia).
exact (km_t_bounds_gen _ km_N km_L_pos HN PI_bounds).
Qed.

(** [π >= 201/64], from the table of π *)
Lemma km_pi_lb : 201 / 64 <= PI.
Proof.
destruct PI_bounds as [H _].
assert (HL : (201 * 2 ^ 4216 <= Limbs.val DyadicConsts.PI)%Z)
  by (apply Z.leb_le; vm_compute; reflexivity).
apply IZR_le in HL. rewrite mult_IZR, km_IZR_pow2 in HL by lia.
set (L := IZR (Limbs.val DyadicConsts.PI)) in *.
assert (E : bpow radix2 4216 * bpow radix2 (-4222) = / 64).
{ rewrite <- bpow_plus. reflexivity. }
assert (201 * bpow radix2 4216 * bpow radix2 (-4222) <= L * bpow radix2 (-4222))
  by (apply Rmult_le_compat_r; [apply bpow_ge_0 | lra]).
lra.
Qed.

(** One exponent: [m 2^e - j π/2 = (π/2) (m α - j)], and [m α - j] is
    [(m Y - (j - m I) 2^km_W) / 2^km_W] for the integer part [I] of
    [α], with [Y] in the bracket [[a, a + d]] of [frac(α) 2^km_W]. *)
Lemma km_okb_sound :
  forall tlo thi e,
  IZR tlo <= bpow radix2 km_N / PI <= IZR thi ->
  km_okb tlo thi e = true ->
  forall m j, (0 < m < 2 ^ 53)%Z ->
  bpow radix2 (-61) <= Rabs (IZR m * bpow radix2 e - IZR j * (PI / 2)).
Proof.
intros tlo thi e [Htl Hth] H m j Hm.
unfold km_okb in H. cbv zeta in H.
apply andb_prop in H as [Hs H]. apply Z.leb_le in Hs.
set (s := km_s e) in *.
set (lo := Z.shiftr tlo s) in *.
set (hi := (Z.shiftr thi s + 1)%Z) in *.
set (a := Z.land lo (Z.ones km_W)) in *.
set (c := km_euclid _ _ _ _ _ _ _) in H.
clearbody c.
assert (HW : (0 <= km_W)%Z) by (unfold km_W; lia).
assert (Hlo : (lo = tlo / 2 ^ s)%Z) by (apply Z.shiftr_div_pow2; exact Hs).
assert (Hhi : (hi = thi / 2 ^ s + 1)%Z)
  by (unfold hi; rewrite Z.shiftr_div_pow2 by exact Hs; reflexivity).
assert (Ha : (a = lo mod 2 ^ km_W)%Z) by (apply Z.land_ones; exact HW).
assert (Hs2 : (0 < 2 ^ s)%Z) by (apply Z.pow_pos_nonneg; lia).
assert (HW2 : (0 < 2 ^ km_W)%Z) by (apply Z.pow_pos_nonneg; lia).
(* [lo 2^s <= tlo] and [thi < hi 2^s] *)
assert (Hlo2 : (2 ^ s * lo <= tlo)%Z) by (rewrite Hlo; apply Z.mul_div_le; exact Hs2).
assert (Hhi2 : (thi < 2 ^ s * hi)%Z)
  by (rewrite Hhi, Z.add_1_r; apply Z.mul_succ_div_gt; exact Hs2).
(* [lo = 2^km_W I + a] *)
set (I := (lo / 2 ^ km_W)%Z).
assert (HlI : (lo = 2 ^ km_W * I + a)%Z) by (rewrite Ha; apply Z.div_mod; lia).
apply IZR_le in Hlo2. apply IZR_lt in Hhi2.
rewrite mult_IZR, km_IZR_pow2 in Hlo2, Hhi2 by exact Hs.
apply (f_equal IZR) in HlI. rewrite plus_IZR, mult_IZR, km_IZR_pow2 in HlI by exact HW.
(* [2^km_N = 2^(e + 1 + km_W) 2^s] *)
assert (HN : bpow radix2 km_N = bpow radix2 (e + 1 + km_W) * bpow radix2 s).
{ rewrite <- bpow_plus. f_equal. unfold s, km_s. lia. }
assert (Hbs : 0 < bpow radix2 s) by apply bpow_gt_0.
set (X := bpow radix2 (e + 1 + km_W) / PI).
assert (HXN : bpow radix2 km_N / PI = X * bpow radix2 s)
  by (unfold X, Rdiv; rewrite HN; ring).
rewrite HXN in Htl, Hth.
assert (HXl : IZR lo <= X).
{ apply (Rmult_le_reg_l (bpow radix2 s)); [exact Hbs | lra]. }
assert (HXh : X <= IZR hi).
{ apply (Rmult_le_reg_l (bpow radix2 s)); [exact Hbs | lra]. }
set (P := bpow radix2 km_W) in *.
set (Y := X - IZR I * P).
assert (HY : IZR a <= Y <= IZR a + IZR (hi - lo)) by (rewrite minus_IZR; unfold Y; lra).
pose proof (km_cert_sound a (hi - lo) c Y H HY m (j - m * I) Hm) as Hc. fold P in Hc.
(* [m Y - (j - m I) P = m X - j P] *)
replace (IZR m * Y - IZR (j - m * I) * P) with (IZR m * X - IZR j * P) in Hc
  by (unfold Y; rewrite minus_IZR, mult_IZR; ring).
assert (HP0 : 0 < P) by apply bpow_gt_0.
pose proof PI_RGT_0 as HPI.
(* [m 2^e - j π/2 = (π / (2 P)) (m X - j P)] *)
assert (He : bpow radix2 (e + 1 + km_W) = 2 * bpow radix2 e * P).
{ unfold P. rewrite !bpow_plus. change (bpow radix2 1) with 2. ring. }
assert (Hx : IZR m * bpow radix2 e - IZR j * (PI / 2) =
             PI / (2 * P) * (IZR m * X - IZR j * P)).
{ unfold X. rewrite He. field. lra. }
rewrite Hx, Rabs_mult, (Rabs_pos_eq (PI / (2 * P))).
2: { apply Rlt_le, Rdiv_lt_0_compat; lra. }
set (Z0 := Rabs (IZR m * X - IZR j * P)) in *.
(* [2^(km_W - 54) = P 2^-54] and [2^-54 = 128 2^-61] *)
assert (HB : bpow radix2 (km_W - 54) = P * bpow radix2 (-54)).
{ unfold P. rewrite <- bpow_plus. f_equal; lia. }
assert (H54 : bpow radix2 (-54) = 128 * bpow radix2 (-61)).
{ change 128 with (bpow radix2 7). rewrite <- bpow_plus. reflexivity. }
rewrite HB, H54 in Hc.
pose proof km_pi_lb as Hpi.
assert (Hb61 : 0 < bpow radix2 (-61)) by apply bpow_gt_0.
set (b := bpow radix2 (-61)) in *.
(* [π / (2 P) Z0 >= π / (2 P) (128 P b / 201) = 64 π b / 201 >= b] *)
assert (HZ : P * (128 * b) / 201 <= Z0) by lra.
assert (H1 : PI / (2 * P) * (P * (128 * b) / 201) <= PI / (2 * P) * Z0).
{ apply Rmult_le_compat_l; [apply Rlt_le, Rdiv_lt_0_compat |]; lra. }
replace (PI / (2 * P) * (P * (128 * b) / 201)) with (64 * PI * b / 201) in H1
  by (field; lra).
assert (H2 : 201 / 64 * b <= PI * b) by (apply Rmult_le_compat_r; lra).
lra.
Qed.

(** ** The distance *)

(** Every exponent of the check *)
Lemma km_core :
  forall e m j, (-52 <= e <= 971)%Z -> (0 < m < 2 ^ 53)%Z ->
  bpow radix2 (-61) <= Rabs (IZR m * bpow radix2 e - IZR j * (PI / 2)).
Proof.
intros e m j He Hm.
apply (km_okb_sound km_tlo km_thi e km_t_bounds); [| exact Hm].
apply (proj1 (forallb_forall _ _) km_all_true).
unfold km_exps. apply in_map_iff. exists (Z.to_nat (e + 52)).
split; [lia | apply in_seq; lia].
Qed.

(** [x = m 2^e > 0] with [m < 2^53]: below 1, [x] is more than [π/2 - 1]
    from every [k π/2] with [k > 0], and every [k < 0] is more than
    [π/2] away. *)
Lemma km_pos :
  forall (m e k : Z), (0 < m < 2 ^ 53)%Z -> (e <= 971)%Z -> k <> 0%Z ->
  bpow radix2 (-61) <= Rabs (IZR m * bpow radix2 e - IZR k * (PI / 2)).
Proof.
intros m e k Hm He9 Hk.
pose proof km_pi_lb as Hpi.
assert (H61 : bpow radix2 (-61) <= bpow radix2 (-2)) by (apply bpow_le; lia).
assert (H2 : bpow radix2 (-2) = / 4) by reflexivity.
assert (Hy0 : 0 <= IZR m * bpow radix2 e).
{ apply Rmult_le_pos; [apply IZR_le; lia | apply bpow_ge_0]. }
destruct (Z_lt_le_dec k 0) as [Hkn | Hkp].
- (* [k <= -1] *)
  assert (Hk1 : IZR k <= -1) by (apply IZR_le; lia).
  assert (IZR k * (PI / 2) <= - (PI / 2)) by nra.
  apply (Rle_trans _ (IZR m * bpow radix2 e - IZR k * (PI / 2))); [lra | apply Rle_abs].
- assert (Hk1 : 1 <= IZR k) by (apply IZR_le; lia).
  assert (PI / 2 <= IZR k * (PI / 2)) by nra.
  destruct (Z_lt_le_dec e (-52)) as [Hes | Hel].
  + (* [x < 2^53 2^-53 = 1] *)
    assert (Hm1 : IZR m < bpow radix2 53)
      by (rewrite <- km_IZR_pow2 by lia; apply IZR_lt; lia).
    assert (He1 : bpow radix2 e <= bpow radix2 (-53)) by (apply bpow_le; lia).
    assert (Hy1 : IZR m * bpow radix2 e < 1).
    { apply (Rle_lt_trans _ (IZR m * bpow radix2 (-53))).
      - apply Rmult_le_compat_l; [apply IZR_le; lia | exact He1].
      - replace 1 with (bpow radix2 53 * bpow radix2 (-53))
          by (rewrite <- bpow_plus; reflexivity).
        apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact Hm1]. }
    apply (Rle_trans _ (- (IZR m * bpow radix2 e - IZR k * (PI / 2))));
      [lra | rewrite <- Rabs_Ropp; apply Rle_abs].
  + apply km_core; lia.
Qed.

(** [m] and [e] of a finite [f64]: [m < 2^53] and [e <= 971] *)
Lemma km_bounded :
  forall m e, SpecFloat.bounded 53 1024 m e = true ->
  (Z.pos m < 2 ^ 53)%Z /\ (e <= 971)%Z.
Proof.
intros m e H.
unfold SpecFloat.bounded, SpecFloat.canonical_mantissa, SpecFloat.fexp,
  SpecFloat.emin in H.
apply andb_prop in H as [H He]. apply Z.leb_le in He. split; [| lia].
apply Z.eqb_eq in H.
rewrite Zpos_digits2_pos in H.
pose proof (Zdigits_correct radix2 (Z.pos m)) as [_ Hd].
assert (Hd53 : (Zdigits radix2 (Z.pos m) <= 53)%Z) by lia.
apply (Z.lt_le_trans _ _ _ Hd).
change (2 ^ 53)%Z with (Zpower radix2 53).
apply Zpower_le. exact Hd53.
Qed.

Theorem km_distance :
  forall (x : f64) (k : Z), is_finite x = true -> k <> 0%Z ->
  bpow radix2 (-61) <= Rabs (B2R x - IZR k * (PI / 2)).
Proof.
intros x k Hx Hk.
destruct x as [s | s | | s m e Hb]; try discriminate Hx.
- (* [|0 - k π/2| >= π/2] *)
  cbn [B2R].
  assert (H61 : bpow radix2 (-61) <= bpow radix2 (-2)) by (apply bpow_le; lia).
  assert (H2 : bpow radix2 (-2) = / 4) by reflexivity.
  pose proof km_pi_lb as Hpi.
  rewrite Rminus_0_l, Rabs_Ropp, Rabs_mult, (Rabs_pos_eq (PI / 2)) by lra.
  rewrite <- abs_IZR.
  assert (1 <= IZR (Z.abs k)) by (apply IZR_le; lia).
  nra.
- destruct (km_bounded m e Hb) as [Hm He].
  cbn [B2R F2R Fnum Fexp].
  destruct s; unfold F2R; cbn [cond_Zopp Fnum Fexp].
  + replace (IZR (- Z.pos m) * bpow radix2 e - IZR k * (PI / 2))
      with (- (IZR (Z.pos m) * bpow radix2 e - IZR (- k) * (PI / 2)))
      by (rewrite !opp_IZR; ring).
    rewrite Rabs_Ropp. apply km_pos; lia.
  + apply km_pos; lia.
Qed.
