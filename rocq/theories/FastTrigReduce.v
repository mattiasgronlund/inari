(** * The argument reduction of the fast paths of [sin], [cos] and [tan]

    Where [DyadicTrig.fast_reduce x] of [Model.v] returns [(n, rh, rl,
    rr)], [x] is finite with [|x| < 2^16], [|n| < 2^27], [x - n π/4096] is
    at most [π/8192 (1 + 2^-24)] in magnitude and [rh + rl] is within
    [2^-90] of it, with [|rl| <= 2^-37], [rr = RN(rh + rl)], and [|rh| >=
    2^-65] where [n] and [rh] are not 0 ([fast_reduce_correct]). *)

From Stdlib Require Import ZArith Reals Lra Lia QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Encoding TwoSum TwoProduct FastTrigTables FastExpReduce.
From Inari Require ConstTight.

Open Scope R_scope.

(** ** Helpers *)

(** [lit w H] adds [H : B2R w = n * / d] for the literal [w], with [n] and
    [d] numerals that [lra] reads, as in [FastExpReduce.v]. *)
Local Ltac lit w H :=
  let q := eval vm_compute in (ConstTight.B2Q w) in
  assert (H : B2R w = Q2R q)
    by (rewrite ConstTight.B2Q_correct; f_equal; vm_compute; reflexivity);
  unfold Q2R in H; cbn [Qnum Qden] in H.

(** The constants: [U1] has 25 significant bits and [U2] 24, so that [n
    U1] and [n U2] are floats for [|n| < 2^27]. *)
Lemma reduce_lits :
  B2R (from_bits DyadicTrig.INV) = 5734161139222659 / 4398046511104 /\
  B2R DyadicTrig.shifter = 6755399441055744 /\
  B2R DyadicTrig.limit = 65536 /\
  B2R (from_bits DyadicTrig.U1) = IZR 26353589 * bpow radix2 (-35) /\
  B2R (from_bits DyadicTrig.U2) = IZR 8947107 * bpow radix2 (-60) /\
  B2R (from_bits DyadicTrig.U3) = 4967757600021511 / 166153499473114484112975882535043072.
Proof.
lit (from_bits DyadicTrig.INV) HI.
lit DyadicTrig.shifter HS.
lit DyadicTrig.limit HL.
lit (from_bits DyadicTrig.U1) H1.
lit (from_bits DyadicTrig.U2) H2.
lit (from_bits DyadicTrig.U3) H3.
assert (B35 : bpow radix2 (-35) = / 34359738368) by reflexivity.
assert (B60 : bpow radix2 (-60) = / 1152921504606846976) by reflexivity.
rewrite B35, B60.
repeat split; lra.
Qed.

(** The powers of two that the bounds below use, as numerals. *)
Lemma reduce_bpow :
  bpow radix2 (-7) = / 128 /\ bpow radix2 (-11) = / 2048 /\ bpow radix2 (-12) = / 4096 /\
  bpow radix2 (-24) = / 16777216 /\ bpow radix2 (-26) = / 67108864 /\
  bpow radix2 (-35) = / 34359738368 /\ bpow radix2 (-37) = / 137438953472 /\
  bpow radix2 (-38) = / 274877906944 /\ bpow radix2 (-60) = / 1152921504606846976 /\
  bpow radix2 (-90) = / 1237940039285380274899124224 /\
  bpow radix2 (-91) = / 2475880078570760549798248448 /\
  bpow radix2 (-92) = / 4951760157141521099596496896 /\
  bpow radix2 (-119) = / 664613997892457936451903530140172288 /\
  bpow radix2 27 = 134217728 /\ bpow radix2 52 = 4503599627370496 /\
  bpow radix2 53 = 9007199254740992.
Proof. repeat split; reflexivity. Qed.

(** ** The quotient

    As in [FastExpReduce.fast_exp_reduce], [n] comes from adding and
    subtracting [SHIFTER] = 1.5 * 2^52: [P = RN(x INV)] is below 2^27 in
    magnitude, so [P + SHIFTER] lies in [[2^52, 2^53)], where the floats
    are the integers, and [n] is within 1/2 of [P]. Then [x - n Us], for
    [Us = U1 + U2 + U3], is [x (1 - INV Us) + (x INV - P) Us + (P - n)
    Us], where [|1 - INV Us| < 2^-53]: at most [Us/2 + 2^-26 Us + 2^16
    2^-53]. *)
Lemma reduce_k :
  forall x, is_finite x = true -> Rabs (B2R x) < 65536 ->
  let kf := sub (add (mul x (from_bits DyadicTrig.INV)) DyadicTrig.shifter)
                DyadicTrig.shifter in
  let n := DyadicExp.to_i64 kf in
  is_finite kf = true /\ B2R kf = IZR n /\ (Z.abs n <= 85445659)%Z /\
  Rabs (B2R x - IZR n * (B2R (from_bits DyadicTrig.U1) + B2R (from_bits DyadicTrig.U2) +
                         B2R (from_bits DyadicTrig.U3))) <=
  (B2R (from_bits DyadicTrig.U1) + B2R (from_bits DyadicTrig.U2) +
   B2R (from_bits DyadicTrig.U3)) * (/ 2 + bpow radix2 (-26)) + bpow radix2 (-37).
Proof.
intros x Fx Hx. cbv zeta.
destruct reduce_lits as (HI & HS & _ & H1 & H2 & H3).
destruct reduce_bpow as (_ & _ & _ & _ & B26 & B35 & B37 & _ & B60 & _ & _ & _ & _ & B27 & B52 & B53).
assert (FI : is_finite (from_bits DyadicTrig.INV) = true) by reflexivity.
assert (FS : is_finite DyadicTrig.shifter = true) by reflexivity.
set (I := from_bits DyadicTrig.INV) in *.
set (S := DyadicTrig.shifter) in *.
apply Rabs_lt_inv in Hx.
(* P = RN(x INV) is within 2^-26 of x INV, which is below 2^27 in
   magnitude. *)
assert (HxI : -85445660 <= B2R x * B2R I <= 85445660) by (rewrite HI; lra).
destruct (mul_below_max x I Fx FI) as (FP & HP & _).
{ apply le_MAX, Rabs_le. lra. }
set (P := mul x I) in *.
assert (EP : Rabs (B2R P - B2R x * B2R I) <= bpow radix2 (-26)).
{ rewrite HP. apply (RN_err_le _ 27); [lia | reflexivity |]. apply Rabs_le. rewrite B27. lra. }
rewrite HI, B26 in EP. apply Rabs_le_inv in EP.
(* P + SHIFTER is in [2^52, 2^53), so it rounds to an integer [m]. *)
destruct (add_below_max P S FP FS) as (FU & HU & _).
{ apply le_MAX, Rabs_le. rewrite HS. lra. }
set (U := add P S) in *.
assert (Hv : bpow radix2 52 <= B2R P + B2R S < bpow radix2 53) by (rewrite HS, B52, B53; lra).
rewrite (RN_int _ Hv) in HU.
pose proof (Znearest_half (fun x => negb (Z.even x)) (B2R P + B2R S)) as Hm.
set (m := Znearest (fun x => negb (Z.even x)) (B2R P + B2R S)) in *.
apply Rabs_le_inv in Hm.
(* [kf] is the integer [k = m - SHIFTER], within 1/2 of P. *)
set (k := (m - 6755399441055744)%Z).
assert (Hk : IZR k = B2R U - B2R S) by (unfold k; rewrite minus_IZR, HU, HS; lra).
assert (Hkr : -85445660 < IZR k < 85445660) by lra.
assert (Hk1 : (-85445660 < k < 85445660)%Z) by (split; apply lt_IZR; lra).
destruct (sub_below_max U S FU FS) as (Fkf & Hkf & _).
{ apply le_MAX, Rabs_le. rewrite <- Hk. lra. }
set (kf := sub U S) in *.
assert (Ekf : B2R kf = IZR k).
{ rewrite Hkf, <- Hk. apply round_generic; [typeclasses eauto|]. apply format_int. lia. }
assert (Ek : DyadicExp.to_i64 kf = k) by (apply to_i64_int; [exact Fkf | exact Ekf | lia]).
rewrite Ek.
split; [exact Fkf|]. split; [exact Ekf|]. split; [lia|].
rewrite H1, H2, H3, B26, B35, B37, B60.
apply Rabs_le. lra.
Qed.

(** [Us] is within 2^-119 of [π/4096] ([fast_trig_consts]), so [x - n
    π/4096] is within [|n| 2^-119 <= 2^-92] of [x - n Us], and at most
    [π/8192 (1 + 2^-24)] in magnitude. *)
Lemma reduce_u :
  forall (x : f64) n, (Z.abs n <= 85445659)%Z ->
  Rabs (B2R x - IZR n * (B2R (from_bits DyadicTrig.U1) + B2R (from_bits DyadicTrig.U2) +
                         B2R (from_bits DyadicTrig.U3))) <=
  (B2R (from_bits DyadicTrig.U1) + B2R (from_bits DyadicTrig.U2) +
   B2R (from_bits DyadicTrig.U3)) * (/ 2 + bpow radix2 (-26)) + bpow radix2 (-37) ->
  Rabs (IZR n * (B2R (from_bits DyadicTrig.U1) + B2R (from_bits DyadicTrig.U2) +
                 B2R (from_bits DyadicTrig.U3) - PI / 4096)) <= bpow radix2 (-92) /\
  Rabs (B2R x - IZR n * (PI / 4096)) <= PI / 8192 * (1 + bpow radix2 (-24)).
Proof.
intros x n Hn Hb.
destruct reduce_lits as (_ & _ & _ & H1 & H2 & H3).
destruct reduce_bpow
  as (_ & _ & _ & B24 & B26 & B35 & B37 & _ & B60 & _ & _ & B92 & B119 & B27 & _ & _).
destruct fast_trig_consts as (_ & HU).
replace (PI / 8192) with (PI / 4096 / 2) by field.
set (u := PI / 4096) in *.
set (Us := B2R (from_bits DyadicTrig.U1) + B2R (from_bits DyadicTrig.U2) +
           B2R (from_bits DyadicTrig.U3)) in *.
assert (E : Rabs (IZR n * (Us - u)) <= bpow radix2 (-92)).
{ rewrite Rabs_mult.
  replace (bpow radix2 (-92)) with (bpow radix2 27 * bpow radix2 (-119))
    by (rewrite <- bpow_plus; reflexivity).
  apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | | rewrite Rabs_minus_sym; exact HU].
  rewrite <- abs_IZR, B27. apply IZR_le. lia. }
split; [exact E|].
apply Rabs_le_inv in E. apply Rabs_le_inv in HU. apply Rabs_le_inv in Hb.
unfold Us in *. rewrite H1, H2, H3, B24, B26, B35, B37, B60, B92, B119 in *.
apply Rabs_le. lra.
Qed.

(** ** The exact part [rh]

    An integer [C] times [2^g] is a float if it is below [2^(g + 53)] in
    magnitude. *)
Lemma grid_format :
  forall C g, (-1074 <= g)%Z -> Rabs (IZR C * bpow radix2 g) < bpow radix2 (g + 53) ->
  generic_format radix2 fexp64 (IZR C * bpow radix2 g).
Proof.
intros C g Hg H. apply format_mult; [|exact Hg].
rewrite bpow_plus, Rabs_mult, (Rabs_pos_eq (bpow radix2 g)) in H by apply bpow_ge_0.
rewrite Rmult_comm in H. apply Rmult_lt_reg_l in H; [|apply bpow_gt_0].
rewrite <- abs_IZR in H. change (bpow radix2 53) with (IZR (2 ^ 53)) in H.
apply lt_IZR in H. exact H.
Qed.

(** A multiple of [2^e] is a multiple of [2^g] for [g <= e]. *)
Lemma grid_mult :
  forall M e g, (g <= e)%Z ->
  IZR M * bpow radix2 e = IZR (M * Zpower radix2 (e - g)) * bpow radix2 g.
Proof.
intros M e g H.
rewrite mult_IZR, IZR_Zpower by lia. rewrite Rmult_assoc, <- bpow_plus.
replace (e - g + g)%Z with e by ring. reflexivity.
Qed.

(** [n U1] and [n U2] are floats, and so are [x - n U1] and [x - n U1 - n
    U2], although Sterbenz's lemma does not apply: for [n <> 0], [|x| >=
    Us - B > 2^-12], so for [g = min(cexp x, -60) >= -64], [x], [n U1]
    and [n U2] are multiples of [2^g], and both differences are below
    [2^-7] and below [2^(mag x)] in magnitude, so below [2^(g + 53)]. *)
Lemma reduce_rh :
  forall x kf n, is_finite x = true -> Rabs (B2R x) < 65536 ->
  is_finite kf = true -> B2R kf = IZR n -> (Z.abs n <= 85445659)%Z ->
  Rabs (B2R x - IZR n * (B2R (from_bits DyadicTrig.U1) + B2R (from_bits DyadicTrig.U2) +
                         B2R (from_bits DyadicTrig.U3))) <=
  (B2R (from_bits DyadicTrig.U1) + B2R (from_bits DyadicTrig.U2) +
   B2R (from_bits DyadicTrig.U3)) * (/ 2 + bpow radix2 (-26)) + bpow radix2 (-37) ->
  let rh := sub (sub x (mul kf (from_bits DyadicTrig.U1))) (mul kf (from_bits DyadicTrig.U2)) in
  is_finite rh = true /\
  B2R rh = B2R x - IZR n * (B2R (from_bits DyadicTrig.U1) + B2R (from_bits DyadicTrig.U2)) /\
  (n <> 0%Z -> B2R rh <> 0 -> bpow radix2 (-64) <= Rabs (B2R rh)).
Proof.
intros x kf n Fx Hx Fkf Ekf Hn Hb. cbv zeta.
destruct reduce_lits as (_ & _ & _ & H1 & H2 & H3).
destruct reduce_bpow
  as (B7 & B11 & B12 & _ & B26 & B35 & B37 & _ & B60 & _ & _ & _ & _ & _ & _ & _).
assert (F1 : is_finite (from_bits DyadicTrig.U1) = true) by reflexivity.
assert (F2 : is_finite (from_bits DyadicTrig.U2) = true) by reflexivity.
set (u1 := from_bits DyadicTrig.U1) in *.
set (u2 := from_bits DyadicTrig.U2) in *.
set (u3 := from_bits DyadicTrig.U3) in *.
assert (Hnr : Rabs (IZR n) <= 85445659) by (rewrite <- abs_IZR; apply IZR_le; exact Hn).
apply Rabs_le_inv in Hnr.
pose proof Hx as Hx'. apply Rabs_lt_inv in Hx'.
pose proof Hb as Hb'. rewrite H1, H2, H3, B26, B35, B37, B60 in Hb'. apply Rabs_le_inv in Hb'.
assert (K : generic_format radix2 fexp64 (B2R x - IZR n * B2R u1) /\
            generic_format radix2 fexp64 (B2R x - IZR n * B2R u1 - IZR n * B2R u2) /\
            (n <> 0%Z -> exists g C, (-64 <= g)%Z /\
               B2R x - IZR n * B2R u1 - IZR n * B2R u2 = IZR C * bpow radix2 g)).
{ pose proof (generic_format_B2R _ _ x) as G.
  change (SpecFloat.fexp 53 1024) with fexp64 in G.
  destruct (Z.eq_dec n 0) as [-> | Hn0].
  { replace (B2R x - IZR 0 * B2R u1) with (B2R x) by lra.
    replace (B2R x - IZR 0 * B2R u2) with (B2R x) by lra.
    split; [exact G|]. split; [exact G|]. intros []. reflexivity. }
  (* |x| >= Us - B > 2^-12. *)
  assert (Hx12 : bpow radix2 (-12) <= Rabs (B2R x)).
  { rewrite B12.
    assert (Hn1 : (n <= -1 \/ 1 <= n)%Z) by lia.
    destruct Hn1 as [Hn1 | Hn1]; apply IZR_le in Hn1.
    - rewrite Rabs_left by lra. lra.
    - rewrite Rabs_pos_eq by lra. lra. }
  assert (Hce : (-64 <= cexp radix2 fexp64 (B2R x))%Z).
  { change (-64)%Z with (FLT_exp (-1074) 53 (-11)).
    apply (cexp_ge_bpow radix2 fexp64 (B2R x) (-11)). exact Hx12. }
  assert (Hmag : (-11 <= mag radix2 (B2R x))%Z) by (apply mag_ge_bpow; exact Hx12).
  pose proof (bpow_mag_gt radix2 (B2R x)) as HQ.
  assert (HQ11 : bpow radix2 (-11) <= bpow radix2 (mag radix2 (B2R x))) by (apply bpow_le; lia).
  set (Q := bpow radix2 (mag radix2 (B2R x))) in *.
  apply Rabs_lt_inv in HQ. rewrite B11 in HQ11.
  set (g := Z.min (cexp radix2 fexp64 (B2R x)) (-60)).
  assert (Hg : (-64 <= g <= -60)%Z) by (unfold g; lia).
  (* Below [2^-7] and below [Q] is below [2^(g + 53)]. *)
  assert (Hg53 : forall d, Rabs d < Q -> Rabs d < bpow radix2 (-7) ->
                 Rabs d < bpow radix2 (g + 53)).
  { intros d HdQ Hd7.
    destruct (Z.min_spec (cexp radix2 fexp64 (B2R x)) (-60)) as [[Hlt Heq] | [Hge Heq]];
      unfold g; rewrite Heq.
    - replace (cexp radix2 fexp64 (B2R x) + 53)%Z with (mag radix2 (B2R x) : Z)
        by (unfold cexp, FLT_exp; lia).
      exact HdQ.
    - exact Hd7. }
  (* x, n U1 and n U2 are multiples of [2^g]. *)
  destruct (format_mult_inv _ g G ltac:(unfold g; lia)) as (a & Ha).
  assert (E1 : B2R x - IZR n * B2R u1 =
               IZR (a - n * 26353589 * Zpower radix2 (-35 - g)) * bpow radix2 g).
  { rewrite Ha, H1, <- Rmult_assoc, <- mult_IZR, (grid_mult _ (-35) g) by lia.
    rewrite minus_IZR. ring. }
  assert (E2 : B2R x - IZR n * B2R u1 - IZR n * B2R u2 =
               IZR (a - n * 26353589 * Zpower radix2 (-35 - g)
                      - n * 8947107 * Zpower radix2 (-60 - g)) * bpow radix2 g).
  { rewrite E1, H2, <- Rmult_assoc, <- mult_IZR, (grid_mult _ (-60) g) by lia.
    rewrite (minus_IZR (a - _)). ring. }
  assert (D1 : Rabs (B2R x - IZR n * B2R u1) < Q /\
               Rabs (B2R x - IZR n * B2R u1) < bpow radix2 (-7)).
  { rewrite H1, B35, B7. split; apply Rabs_def1; lra. }
  assert (D2 : Rabs (B2R x - IZR n * B2R u1 - IZR n * B2R u2) < Q /\
               Rabs (B2R x - IZR n * B2R u1 - IZR n * B2R u2) < bpow radix2 (-7)).
  { rewrite H1, H2, B35, B60, B7. split; apply Rabs_def1; lra. }
  destruct D1 as (D1Q & D17). destruct D2 as (D2Q & D27).
  split; [|split].
  - rewrite E1. apply grid_format; [lia|]. rewrite <- E1. apply Hg53; assumption.
  - rewrite E2. apply grid_format; [lia|]. rewrite <- E2. apply Hg53; assumption.
  - intros _. eexists. eexists. split; [|exact E2]. lia. }
destruct K as (G1 & G2 & G3).
(* [n U1] and [n U2] are exact. *)
destruct (mul_below_max kf u1 Fkf F1) as (FM1 & HM1 & _).
{ apply le_MAX, Rabs_le. rewrite Ekf, H1, B35. lra. }
assert (EM1 : B2R (mul kf u1) = IZR n * B2R u1).
{ rewrite HM1, Ekf. apply round_generic; [typeclasses eauto|].
  rewrite H1, <- Rmult_assoc, <- mult_IZR. apply format_mult; lia. }
destruct (mul_below_max kf u2 Fkf F2) as (FM2 & HM2 & _).
{ apply le_MAX, Rabs_le. rewrite Ekf, H2, B60. lra. }
assert (EM2 : B2R (mul kf u2) = IZR n * B2R u2).
{ rewrite HM2, Ekf. apply round_generic; [typeclasses eauto|].
  rewrite H2, <- Rmult_assoc, <- mult_IZR. apply format_mult; lia. }
destruct (sub_below_max x (mul kf u1) Fx FM1) as (Fd1 & Hd1 & _).
{ apply le_MAX, Rabs_le. rewrite EM1, H1, B35. lra. }
assert (Ed1 : B2R (sub x (mul kf u1)) = B2R x - IZR n * B2R u1).
{ rewrite Hd1, EM1. apply round_generic; [typeclasses eauto | exact G1]. }
destruct (sub_below_max (sub x (mul kf u1)) (mul kf u2) Fd1 FM2) as (Frh & Hrh & _).
{ apply le_MAX, Rabs_le. rewrite Ed1, EM2, H1, H2, B35, B60. lra. }
assert (Erh : B2R (sub (sub x (mul kf u1)) (mul kf u2)) =
              B2R x - IZR n * B2R u1 - IZR n * B2R u2).
{ rewrite Hrh, Ed1, EM2. apply round_generic; [typeclasses eauto | exact G2]. }
split; [exact Frh|]. split; [rewrite Erh; ring|].
intros Hn0 Hr. destruct (G3 Hn0) as (g & C & Hg & EC).
rewrite Erh, EC in *.
rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 g)) by apply bpow_ge_0.
assert (HC : (C <> 0)%Z) by (intro HC; apply Hr; rewrite HC; lra).
assert (H1C : 1 <= Rabs (IZR C)) by (rewrite <- abs_IZR; apply IZR_le; lia).
apply Rle_trans with (bpow radix2 g); [apply bpow_le; lia|].
rewrite <- (Rmult_1_l (bpow radix2 g)) at 1.
apply Rmult_le_compat_r; [apply bpow_ge_0 | exact H1C].
Qed.

Theorem fast_reduce_correct :
  forall x n rh rl rr,
  DyadicTrig.fast_reduce x = Some (n, rh, rl, rr) ->
  is_finite x = true /\ Rabs (B2R x) < 65536 /\ (Z.abs n < 2 ^ 27)%Z /\
  is_finite rh = true /\ is_finite rl = true /\ is_finite rr = true /\ rr = add rh rl /\
  Rabs (B2R x - IZR n * (PI / 4096) - (B2R rh + B2R rl)) <= bpow radix2 (-90) /\
  Rabs (B2R x - IZR n * (PI / 4096)) <= PI / 8192 * (1 + bpow radix2 (-24)) /\
  Rabs (B2R rl) <= bpow radix2 (-37) /\
  (n <> 0%Z -> B2R rh <> 0 -> bpow radix2 (-65) <= Rabs (B2R rh)).
Proof.
intros x n rh rl rr H.
unfold DyadicTrig.fast_reduce in H.
destruct (is_nan x || ge (fabs x) DyadicTrig.limit) eqn:G; [discriminate H|].
apply Bool.orb_false_iff in G. destruct G as (Gn & Gl).
(* [x] is finite: an infinity is above the limit, and NaN is NaN. *)
assert (Fx : is_finite x = true).
{ destruct x as [s|s| |s m e B]; try reflexivity; vm_compute in Gn, Gl; discriminate. }
destruct reduce_lits as (_ & _ & HL & H1 & H2 & H3).
assert (Hx : Rabs (B2R x) < 65536).
{ unfold ge, fabs in Gl.
  rewrite Bleb_correct in Gl by (rewrite ?is_finite_Babs; first [exact Fx | reflexivity]).
  rewrite B2R_Babs in Gl.
  destruct (Rle_bool_spec (B2R DyadicTrig.limit) (Rabs (B2R x))); [discriminate Gl|].
  lra. }
cbv beta iota zeta in H.
injection H as En Erh Erl Err. subst n rh rl rr.
pose proof (reduce_k x Fx Hx) as K. cbv zeta in K. destruct K as (Fkf & Ekf & Hn & Hb).
set (kf := sub (add (mul x (from_bits DyadicTrig.INV)) DyadicTrig.shifter)
              DyadicTrig.shifter) in *.
set (n := DyadicExp.to_i64 kf) in *.
destruct (reduce_u x n Hn Hb) as (EU & HU).
pose proof (reduce_rh x kf n Fx Hx Fkf Ekf Hn Hb) as R. cbv zeta in R.
destruct R as (Frh & Erh & Hrh).
set (rh := sub (sub x (mul kf (from_bits DyadicTrig.U1))) (mul kf (from_bits DyadicTrig.U2)))
  in *.
destruct reduce_bpow
  as (_ & _ & _ & _ & B26 & B35 & B37 & B38 & B60 & B90 & B91 & B92 & _ & _ & _ & _).
assert (Hnr : Rabs (IZR n) <= 85445659) by (rewrite <- abs_IZR; apply IZR_le; exact Hn).
apply Rabs_le_inv in Hnr.
(* [n U3] is below [2^-38], so [rl = -RN(n U3)] is within [2^-91] of [-n U3]. *)
assert (F3 : is_finite (from_bits DyadicTrig.U3) = true) by reflexivity.
assert (HnU3 : Rabs (B2R kf * B2R (from_bits DyadicTrig.U3)) <= bpow radix2 (-38)).
{ rewrite Ekf, H3, B38. apply Rabs_le. lra. }
destruct (mul_below_max kf (from_bits DyadicTrig.U3) Fkf F3) as (FM3 & HM3 & _).
{ apply le_MAX. apply Rle_trans with (1 := HnU3). rewrite B38. lra. }
assert (EM3 : Rabs (B2R (mul kf (from_bits DyadicTrig.U3)) -
                    B2R kf * B2R (from_bits DyadicTrig.U3)) <= bpow radix2 (-91)).
{ rewrite HM3. apply (RN_err_le _ (-38)); [lia | reflexivity | exact HnU3]. }
set (rl := opp (mul kf (from_bits DyadicTrig.U3))).
assert (Frl : is_finite rl = true) by (unfold rl, opp; rewrite is_finite_Bopp; exact FM3).
assert (Erl : B2R rl = - B2R (mul kf (from_bits DyadicTrig.U3)))
  by (unfold rl, opp; apply B2R_Bopp).
rewrite Ekf in EM3, HnU3.
apply Rabs_le_inv in EM3. apply Rabs_le_inv in HnU3. apply Rabs_le_inv in EU.
rewrite B38, B91 in *.
assert (Hrl : Rabs (B2R rl) <= bpow radix2 (-37)) by (rewrite Erl, B37; apply Rabs_le; lra).
(* [rh] is below [2^-7] by [Hb], so [rh + rl] is far below [MAX]. *)
pose proof Hx as Hx'. apply Rabs_lt_inv in Hx'.
assert (Frr : is_finite (add rh rl) = true).
{ destruct (add_below_max rh rl Frh Frl) as (F & _); [|exact F].
  apply le_MAX. rewrite Erh, Erl, H1, H2, B35, B60. apply Rabs_le. lra. }
split; [exact Fx|]. split; [exact Hx|].
split; [assert (P27 : (2 ^ 27 = 134217728)%Z) by reflexivity; lia|].
split; [exact Frh|]. split; [exact Frl|]. split; [exact Frr|]. split; [reflexivity|].
split.
{ (* [x - n u - rh - rl = n (Us - u) + (RN(n U3) - n U3)]. *)
  rewrite Erh, Erl, B90. rewrite B92 in EU. apply Rabs_le. lra. }
split; [exact HU|]. split; [exact Hrl|].
intros Hn0 Hr0. apply Rle_trans with (bpow radix2 (-64)); [apply bpow_le; lia|].
exact (Hrh Hn0 Hr0).
Qed.
