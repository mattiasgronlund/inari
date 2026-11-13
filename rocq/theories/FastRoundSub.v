(** * Rounding tests for subnormal results

    [Fast.round_dir_sub] and [Fast.round_near_sub] of [Model.v] are the
    tests of [FastRound.v] for an [e] in [-1085, -1022], where [y 2^e] is
    below [2^-1021] and can be subnormal, so that scaling a rounded [h] by
    [2^e] would round a second time. They round [C + y] once instead, for
    [C = 2^(-1022 - e) >= 1]: the [f64]s in [[C, 2C]] are [g = 2^-52 C]
    apart, which is [2^-1074] in units of [2^-e]. [s + t = C + h] exactly
    by Fast2Sum [Dekker], and the result [(r - C) 2^e] is the [f64] whose
    bits are those of [r] less those of [C]
    ([round_dir_sub_correct], [round_near_sub_correct]). To nearest, [r]
    is [s], or the [f64] after or before [s] where [u = RN(t + l)] is
    beyond [(2^-53 + 2^-67) C] in magnitude ([sub_far_consts]).

    [Dekker] T. J. Dekker, A floating-point technique for extending the
    available precision, Numer. Math. 18 (1971). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error.
From Inari Require Import Model Mpfr Encoding TwoSum TwoProduct DyDriver NearF64 NearCells
  FastRound FastRoundSubBits FastRoundSubCommon.
From Inari Require StepUp DyExpRules.

Open Scope R_scope.

Local Notation G := (generic_format radix2 fexp64).

(** The bits, constants and grid of [FastRoundSubBits.v], and the sum [C
    + h + l] of [FastRoundSubCommon.v], are the steps of both proofs. *)

Theorem round_dir_sub_correct :
  forall h l e up v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < B2R h < 2 -> (-1085 <= e <= -1022)%Z ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  Fast.round_dir_sub h l e up = Some v ->
  rounds up (y * bpow radix2 e) v.
Proof.
intros h l e up v y Fh Fl Hrn Hh He Hy Hv.
destruct (sub_unit_spec e He) as (Fc & Bc & _).
destruct (sub_consts e He) as (F2c & R2c & Fb & Rb & _ & _).
destruct (sub_common h l e y Fh Fl Hrn Hh He Hy) as (Fs & Hk).
unfold Fast.round_dir_sub, Fast.fast_two_sum in Hv; cbv beta iota zeta in Hv.
set (c := Fast.sub_unit e) in *.
set (s := add c h) in *.
set (u := add (add h (sub c s)) l) in *.
set (b := mul c Fast.sub_err) in *.
set (g := bpow radix2 (-1074 - e)) in *.
(* The guard [s < 2C] keeps [s] in the binade of [C], where [s = C + N g]. *)
destruct (ge s (mul Fast.two c)) eqn:G0; [discriminate Hv|].
pose proof (FastRound.ge_false _ _ Fs F2c G0) as Hs2. rewrite R2c in Hs2.
destruct (Hk Hs2) as (Fu & Hy0 & N & HN & Hbits & HD1 & HD2).
apply Rabs_def2 in HD1, HD2.
(* The step from [s] by the sign bit of [u], where [|u| > b], is the one
   that the comparisons [u > b] and [u < -b] choose, and both fail on the
   same [u], as [b >= 0] ([FastRound.dir_step_cases]). *)
assert (Pb : 0 <= B2R b) by (rewrite Rb; unfold g; pose proof (bpow_gt_0 radix2 (-1074 - e)); lra).
assert (E : (if gt (fabs u) b
             then Some (from_bits (to_bits s + Z.b2z up - Z.shiftr (to_bits u) 63))
             else None) =
            (if gt u b then Some (if up then from_bits (to_bits s + 1) else s)
             else if lt u (opp b) then Some (if up then s else from_bits (to_bits s - 1))
             else None)).
{ destruct (FastRound.dir_step_cases u b Fb Pb)
    as [(A & B & C) | [(A & B & C & D) | (A & B & C)]].
  - rewrite A, B, C. cbv beta iota. destruct up.
    + change (Z.b2z true) with 1%Z. rewrite Z.sub_0_r. reflexivity.
    + change (Z.b2z false) with 0%Z. rewrite Z.sub_0_r, Z.add_0_r, from_to_bits.
      reflexivity.
  - rewrite A, B, C, D. cbv beta iota. destruct up.
    + change (Z.b2z true) with 1%Z. rewrite Z.add_simpl_r, from_to_bits. reflexivity.
    + change (Z.b2z false) with 0%Z. rewrite Z.add_0_r. reflexivity.
  - rewrite A, B, C. reflexivity. }
rewrite E in Hv. clear E.
destruct (gt u b) eqn:G1.
- (* [u > b]: [y] is in [(N g, (N + 1) g)], whose ends are [s - C] and its
     successor, the bits of [s] and [s + 1] less those of [C]. *)
  pose proof (FastRound.gt_true _ _ Fu Fb G1) as Hub. rewrite Rb in Hub.
  injection Hv as <-.
  replace (to_bits (if up then from_bits (to_bits s + 1) else s) - to_bits c)%Z
    with (if up then (N + 1)%Z else N).
  2: { destruct up; [rewrite to_from_bits by lia|]; rewrite Hbits, Bc; ring. }
  apply (sub_bracket e N up y); [lia | fold g; lra].
- destruct (lt u (opp b)) eqn:G2; [|discriminate Hv].
  (* [u < -b]: [y] is in [((N - 1) g, N g)], the bits of [s - 1] and [s]
     less those of [C]; [N >= 1] as [y > 0]. *)
  assert (Fob : is_finite (opp b) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fb).
  pose proof (DyExpRules.lt_R _ _ Fu Fob G2) as Hub.
  unfold opp in Hub. rewrite B2R_Bopp, Rb in Hub.
  assert (Hg : 0 < g) by apply bpow_gt_0.
  assert (HN1 : (1 <= N)%Z).
  { destruct (Z_lt_le_dec 0 N) as [HN0|HN0]; [lia|]. exfalso.
    apply IZR_le in HN0. nra. }
  injection Hv as <-.
  replace (to_bits (if up then s else from_bits (to_bits s - 1)) - to_bits c)%Z
    with (if up then (N - 1 + 1)%Z else (N - 1)%Z).
  2: { destruct up; [|rewrite to_from_bits by lia]; rewrite Hbits, Bc; ring. }
  apply (sub_bracket e (N - 1) up y); [lia|]. fold g. rewrite minus_IZR. lra.
Qed.

Theorem round_near_sub_correct :
  forall h l e v y,
  is_finite h = true -> is_finite l = true -> B2R h = RN (B2R h + B2R l) ->
  / 2 < B2R h < 2 -> (-1085 <= e <= -1022)%Z ->
  Rabs (y - (B2R h + B2R l)) <= bpow radix2 (-68) ->
  Fast.round_near_sub h l e = Some v ->
  near_round (y * bpow radix2 e) v.
Proof.
intros h l e v y Fh Fl Hrn Hh He Hy Hv.
destruct (sub_unit_spec e He) as (Fc & Bc & _).
destruct (sub_consts e He) as (F2c & R2c & _ & _ & Fb & Rb).
destruct (sub_far_consts e He) as (Ff & Rf).
destruct (sub_common h l e y Fh Fl Hrn Hh He Hy) as (Fs & Hk).
unfold Fast.round_near_sub, Fast.fast_two_sum in Hv; cbv beta iota zeta in Hv.
set (c := Fast.sub_unit e) in *.
set (s := add c h) in *.
set (u := add (add h (sub c s)) l) in *.
set (b := mul c Fast.sub_near) in *.
set (f := mul c Fast.sub_far) in *.
set (g := bpow radix2 (-1074 - e)) in *.
(* The guard [s < 2C] keeps [s] in the binade of [C], where [s = C + N g]. *)
destruct (ge s (mul Fast.two c)) eqn:G0; [discriminate Hv|].
pose proof (FastRound.ge_false _ _ Fs F2c G0) as Hs2. rewrite R2c in Hs2.
destruct (Hk Hs2) as (Fu & Hy0 & N & HN & Hbits & HD1 & HD2).
apply Rabs_def2 in HD1, HD2.
assert (Fob : is_finite (opp b) = true) by (unfold opp; rewrite is_finite_Bopp; exact Fb).
destruct (lt u b && gt u (opp b)) eqn:G1.
- (* [|u| < g/2 - g/32768] puts [y] within [g/2] of [N g], and the result
     is the [f64] whose bits are those of [s] less those of [C], [N]. *)
  apply andb_prop in G1 as (G1 & G2).
  pose proof (DyExpRules.lt_R _ _ Fu Fb G1) as Hub.
  pose proof (FastRound.gt_true _ _ Fu Fob G2) as Hlb.
  unfold opp in Hlb. rewrite B2R_Bopp in Hlb. rewrite Rb in Hub, Hlb.
  (* [injection Hv] takes 3 s here and over 7 minutes in the arms below, so
     [v] is taken out of the [Some] by conversion. *)
  apply (f_equal (fun o => match o with Some r => r | None => v end)) in Hv.
  change (from_bits (to_bits s - to_bits c) = v) in Hv. subst v.
  replace (to_bits s - to_bits c)%Z with N by (rewrite Hbits, Bc; ring).
  apply (sub_near_grid e N y); [lia | exact Hy0 | apply Rabs_def1; fold g; lra].
- destruct (gt u f) eqn:G2.
  + (* [u > g/2 + g/32768] puts [y] above the midpoint [N g + g/2], and
       below [(N + 1) g], so within [g/2] of [(N + 1) g]: the bits of [s + 1]
       less those of [C]. *)
    pose proof (FastRound.gt_true _ _ Fu Ff G2) as Huf. rewrite Rf in Huf.
    apply (f_equal (fun o => match o with Some r => r | None => v end)) in Hv.
    change (from_bits (to_bits (from_bits (to_bits s + 1)) - to_bits c) = v) in Hv. subst v.
    replace (to_bits (from_bits (to_bits s + 1)) - to_bits c)%Z with (N + 1)%Z.
    2: { rewrite to_from_bits by lia. rewrite Hbits, Bc. ring. }
    apply (sub_near_grid e (N + 1) y); [lia | exact Hy0|].
    apply Rabs_def1; rewrite plus_IZR; fold g; lra.
  + destruct (lt u (opp f)) eqn:G3; [|discriminate Hv].
    (* [u < -(g/2 + g/32768)] puts [y] below the midpoint [N g - g/2], and
       above [(N - 1) g], so within [g/2] of [(N - 1) g]: the bits of [s - 1]
       less those of [C]; [N >= 1] as [y > 0]. *)
    assert (Fof : is_finite (opp f) = true) by (unfold opp; rewrite is_finite_Bopp; exact Ff).
    pose proof (DyExpRules.lt_R _ _ Fu Fof G3) as Huf.
    unfold opp in Huf. rewrite B2R_Bopp, Rf in Huf.
    assert (Hg : 0 < g) by apply bpow_gt_0.
    assert (HN1 : (1 <= N)%Z).
    { destruct (Z_lt_le_dec 0 N) as [HN0|HN0]; [lia|]. exfalso.
      apply IZR_le in HN0. nra. }
    apply (f_equal (fun o => match o with Some r => r | None => v end)) in Hv.
    change (from_bits (to_bits (from_bits (to_bits s - 1)) - to_bits c) = v) in Hv. subst v.
    replace (to_bits (from_bits (to_bits s - 1)) - to_bits c)%Z with (N - 1)%Z.
    2: { rewrite to_from_bits by lia. rewrite Hbits, Bc. ring. }
    apply (sub_near_grid e (N - 1) y); [lia | exact Hy0|].
    apply Rabs_def1; rewrite minus_IZR; fold g; lra.
Qed.
