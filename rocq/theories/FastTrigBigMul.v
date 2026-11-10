(** * The product of the reduction of large arguments of the fast paths of [sin], [cos] and [tan]

    [U1 + U2] is exact ([big_uh]), and [DyadicTrig.fast_mul] of [fh + fl]
    with [|fh| <= 1/2] and [|fl| <= 2^-53] by [(U1 + U2) + U3] is
    [(fh + fl) π/4096] within 2^-100, with [|rl| <= 2^-37], where [|rh| >=
    2^-65] ([big_mul_correct]), the same with and without an FMA
    ([big_mul_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr TwoSum TwoProduct FastRound FastExpErr FastTrigTables.
From Inari Require Import FastTrigReduce.
From Inari Require MulRuTiny.

Open Scope R_scope.

(** [U1 + U2] is [26353589 2^25 + 8947107 = 884279719003555] times
    [2^-60] ([reduce_lits]), an integer below [2^50] times a power of 2,
    so a float, and the sum is not rounded. *)
Lemma big_uh :
  is_finite (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)) = true /\
  B2R (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)) =
    B2R (from_bits DyadicTrig.U1) + B2R (from_bits DyadicTrig.U2).
Proof.
destruct reduce_lits as (_ & _ & _ & H1 & H2 & _).
assert (F1 : is_finite (from_bits DyadicTrig.U1) = true) by reflexivity.
assert (F2 : is_finite (from_bits DyadicTrig.U2) = true) by reflexivity.
assert (E : B2R (from_bits DyadicTrig.U1) + B2R (from_bits DyadicTrig.U2) =
            IZR 884279719003555 * bpow radix2 (-60)).
{ rewrite H1, H2. cbn [bpow radix_val radix2 Z.opp]. lra. }
destruct (add_k (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2) 1 F1 F2)
  as (F & R & _); [rewrite E; apply Rabs_le; cbn [bpow radix_val radix2 Z.opp]; lra | lra |].
split; [exact F |].
rewrite R, E. apply round_generic; [typeclasses eauto |].
apply grid_format; [lia |].
change (-60 + 53)%Z with (-7)%Z.
apply Rabs_lt. cbn [bpow radix_val radix2 Z.opp]. lra.
Qed.

(** [uh = U1 + U2] is between 2^-11 and 2^-10, and [U3] is a positive
    float of at most 2^-64. *)
Lemma big_u_bounds :
  is_finite (from_bits DyadicTrig.U3) = true /\
  bpow radix2 (-11) <= B2R (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)) <=
    bpow radix2 (-10) /\
  0 < B2R (from_bits DyadicTrig.U3) <= bpow radix2 (-64).
Proof.
destruct reduce_lits as (_ & _ & _ & H1 & H2 & H3).
destruct big_uh as (_ & Euh).
split; [reflexivity |].
rewrite Euh, H1, H2, H3. cbn [bpow radix_val radix2 Z.opp].
split; split; lra.
Qed.

(** [fh uh] is exact in [two_prod_err], with or without an FMA, where
    [|fh| <= 1/2] and [|RN(fh uh)| >= 2^-65]: the exponent of [RN(fh uh)]
    is at least -65, and at most 0 as [|fh uh| <= 2^-11], that of [fh] is
    at most 0, and that of [uh] at most -10. *)
Lemma big_exact :
  forall b fh,
  is_finite fh = true -> Rabs (B2R fh) <= / 2 ->
  bpow radix2 (-65) <=
    Rabs (B2R (mul fh (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)))) ->
  Generic.two_prod_is_exact b fh (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2))
    (mul fh (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2))) = true.
Proof.
intros b fh Ffh Hfh Hp.
destruct big_uh as (Fuh & _).
destruct big_u_bounds as (_ & Buh & _).
set (uh := add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)) in *.
cbn [bpow radix_val radix2 Z.opp] in Buh.
assert (HP : Rabs (B2R fh * B2R uh) <= / 2 * bpow radix2 (-10)).
{ apply Rabs_mul_le; [exact Hfh |]. rewrite Rabs_pos_eq by lra.
  cbn [bpow radix_val radix2 Z.opp]. lra. }
destruct (mul_k fh uh (/ 2 * bpow radix2 (-10)) Ffh Fuh HP) as (Fp & _ & Bp);
  [cbn [bpow radix_val radix2 Z.opp]; lra |].
apply Rabs_le_inv in HP, Bp.
cbn [bpow radix_val radix2 Z.opp] in HP, Bp.
assert (E1 : (-65 <= Generic.exponent (mul fh uh))%Z)
  by (apply MulRuTiny.exponent_ge; assumption).
assert (E2 : (Generic.exponent (mul fh uh) < 1)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fp | lia |].
  apply Rabs_lt. cbn [bpow radix_val radix2 Z.opp]. lra. }
assert (E3 : (Generic.exponent fh < 1)%Z).
{ apply MulRuTiny.exponent_lt; [exact Ffh | lia |].
  cbn [bpow radix_val radix2 Z.opp]. lra. }
assert (E4 : (Generic.exponent uh < -9)%Z).
{ apply MulRuTiny.exponent_lt; [exact Fuh | lia |].
  rewrite Rabs_pos_eq by lra. cbn [bpow radix_val radix2 Z.opp]. lra. }
unfold Generic.two_prod_is_exact. cbv zeta.
destruct b; rewrite ?andb_true_iff, ?Z.leb_le; lia.
Qed.

(** [fast_mul] of [(fh, fl)] and [(uh, U3)]: [rh = RN(fh uh)], and [fh uh
    - rh] is exact ([big_exact], Dekker). Where [Us = uh + U3] is within
    2^-119 of [π/4096] ([fast_trig_consts]), [(fh + fl) π/4096 - (rh +
    rl)] is [(fh + fl) (π/4096 - Us) + fl U3] (at most [2^-119] and
    [2^-117], [fl U3] left out) minus the errors of [fh U3], [fl uh],
    their sum and [rl] (at most about [2^-118], [2^-116], [2^-115] and
    [2^-114]): within [2^-112] in all. [rl] is at most [2^-64] (the
    error of [rh]) plus [2^-65 + 2^-63] and the roundings, below [2^-61]. *)
Lemma big_mul_correct :
  forall fh fl rh rl,
  is_finite fh = true -> is_finite fl = true ->
  Rabs (B2R fh) <= / 2 -> Rabs (B2R fl) <= bpow radix2 (-53) ->
  DyadicTrig.fast_mul false fh fl
    (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)) (from_bits DyadicTrig.U3) =
    (rh, rl) ->
  bpow radix2 (-65) <= Rabs (B2R rh) ->
  is_finite rh = true /\ is_finite rl = true /\ is_finite (add rh rl) = true /\
  Rabs ((B2R fh + B2R fl) * (PI / 4096) - (B2R rh + B2R rl)) <= bpow radix2 (-100) /\
  Rabs (B2R rl) <= bpow radix2 (-37).
Proof.
intros fh fl rh rl Ffh Ffl Hfh Hfl M Hrh.
unfold DyadicTrig.fast_mul in M. cbv zeta in M.
apply pair_equal_spec in M as [Ep Erl]. subst rh rl.
pose proof (big_exact false fh Ffh Hfh Hrh) as Hex.
destruct big_uh as (Fuh & Euh).
destruct big_u_bounds as (Fu3 & Buh & Bu3).
destruct fast_trig_consts as (_ & HU).
rewrite <- Euh in HU.
set (uh := add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)) in *.
set (u3 := from_bits DyadicTrig.U3) in *.
set (u := PI / 4096) in *.
clearbody uh u3 u. clear Euh.
cbn [bpow radix_val radix2 Z.opp] in Buh, Bu3.
(* [p = RN(fh uh)] and [e0 = fh uh - p] exactly. *)
destruct (two_prod_err_correct false fh uh Ffh Fuh Hex) as (Fp & _ & _ & Fe0 & Ee0).
assert (HP : Rabs (B2R fh * B2R uh) <= / 2 * bpow radix2 (-10)).
{ apply Rabs_mul_le; [exact Hfh |]. rewrite Rabs_pos_eq by lra.
  cbn [bpow radix_val radix2 Z.opp]. lra. }
destruct (mul_k fh uh (/ 2 * bpow radix2 (-10)) Ffh Fuh HP) as (_ & _ & Bp);
  [cbn [bpow radix_val radix2 Z.opp]; lra |].
set (p := mul fh uh) in *.
set (e0 := Generic.two_prod_err false fh uh p) in *.
clearbody p e0.
apply Rabs_le_inv in HP, Bp.
cbn [bpow radix_val radix2 Z.opp] in HP, Bp.
(* [m1 = RN(fh U3)], [m2 = RN(fl uh)], [m3 = RN(m1 + m2)], [e = RN(e0 + m3)]. *)
assert (H1b : Rabs (B2R fh * B2R u3) <= / 2 * bpow radix2 (-64)).
{ apply Rabs_mul_le; [exact Hfh |]. rewrite Rabs_pos_eq by lra.
  cbn [bpow radix_val radix2 Z.opp]. lra. }
destruct (mul_k fh u3 (/ 2 * bpow radix2 (-64)) Ffh Fu3 H1b) as (Fm1 & _ & Bm1);
  [cbn [bpow radix_val radix2 Z.opp]; lra |].
assert (H2b : Rabs (B2R fl * B2R uh) <= bpow radix2 (-53) * bpow radix2 (-10)).
{ apply Rabs_mul_le; [exact Hfl |]. rewrite Rabs_pos_eq by lra.
  cbn [bpow radix_val radix2 Z.opp]. lra. }
destruct (mul_k fl uh (bpow radix2 (-53) * bpow radix2 (-10)) Ffl Fuh H2b)
  as (Fm2 & _ & Bm2); [cbn [bpow radix_val radix2 Z.opp]; lra |].
set (m1 := mul fh u3) in *. set (m2 := mul fl uh) in *.
clearbody m1 m2.
apply Rabs_le_inv in H1b, H2b, Bm1, Bm2.
cbn [bpow radix_val radix2 Z.opp] in H1b, H2b, Bm1, Bm2.
destruct (add_k m1 m2 (bpow radix2 (-62)) Fm1 Fm2) as (Fm3 & _ & Bm3);
  [apply Rabs_le; cbn [bpow radix_val radix2 Z.opp]; lra |
   cbn [bpow radix_val radix2 Z.opp]; lra |].
set (m3 := add m1 m2) in *. clearbody m3.
apply Rabs_le_inv in Bm3.
cbn [bpow radix_val radix2 Z.opp] in Bm3.
destruct (add_k e0 m3 (bpow radix2 (-61)) Fe0 Fm3) as (Fe & _ & Be);
  [apply Rabs_le; cbn [bpow radix_val radix2 Z.opp]; lra |
   cbn [bpow radix_val radix2 Z.opp]; lra |].
set (e := add e0 m3) in *. clearbody e.
apply Rabs_le_inv in Be.
cbn [bpow radix_val radix2 Z.opp] in Be.
(* [rh + rl] is far from overflow. *)
destruct (add_k p e 1 Fp Fe) as (Fr & _ & _);
  [apply Rabs_le; lra | lra |].
(* The constants: [(fh + fl) (π/4096 - Us)] and [fl U3]. *)
assert (Hf : Rabs (B2R fh + B2R fl) <= 1).
{ apply Rabs_le_inv in Hfh, Hfl. cbn [bpow radix_val radix2 Z.opp] in Hfl.
  apply Rabs_le. lra. }
pose proof (Rabs_mul_le _ _ _ _ Hf HU) as HD.
assert (Hlu : Rabs (B2R fl * B2R u3) <= bpow radix2 (-53) * bpow radix2 (-64)).
{ apply Rabs_mul_le; [exact Hfl |]. rewrite Rabs_pos_eq by lra.
  cbn [bpow radix_val radix2 Z.opp]. lra. }
apply Rabs_le_inv in HD, Hlu.
cbn [bpow radix_val radix2 Z.opp] in HD, Hlu.
split; [exact Fp |]. split; [exact Fe |]. split; [exact Fr |].
split.
- apply Rabs_le. cbn [bpow radix_val radix2 Z.opp]. split; lra.
- apply Rabs_le. cbn [bpow radix_val radix2 Z.opp]. split; lra.
Qed.

(** The same with an FMA: [fh uh] is exact in [two_prod_err] either way
    ([big_exact]), so its error is the same float. *)
Lemma big_mul_fma :
  forall fh fl,
  is_finite fh = true -> Rabs (B2R fh) <= / 2 ->
  bpow radix2 (-65) <=
    Rabs (B2R (mul fh (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)))) ->
  DyadicTrig.fast_mul true fh fl
    (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)) (from_bits DyadicTrig.U3) =
  DyadicTrig.fast_mul false fh fl
    (add (from_bits DyadicTrig.U1) (from_bits DyadicTrig.U2)) (from_bits DyadicTrig.U3).
Proof.
intros fh fl Ffh Hfh Hp.
destruct big_uh as (Fuh & _).
unfold DyadicTrig.fast_mul. cbv zeta.
rewrite (two_prod_err_fma_eq fh _ Ffh Fuh (big_exact true fh Ffh Hfh Hp)
  (big_exact false fh Ffh Hfh Hp)).
reflexivity.
Qed.
