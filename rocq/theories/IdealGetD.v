(** * The [mpfr_get_d] of the ideal MPFR rounds correctly to an [f64]

    [round_f64_correct]: [round_f64 rnd y] is [y] rounded in the direction
    [rnd] to an [f64], as [mpfr_round] with [f64_format] says, overflow
    included, for every real [y], so [ideal_get_d_ok]: the ideal MPFR
    satisfies [get_d_ok] at every exponent range. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary Mpfr MpfrRound ParseFormat MpfrIdeal.

Open Scope R_scope.

(** The format of the finite [f64]s without the bound above:
    [FLT_exp (-1074) 53]. *)
Local Notation G := (generic_format radix2 (SpecFloat.fexp 53 1024)).

(** A finite [f64] is in [G], and below [2^1024] in magnitude. *)
Lemma f64_format_G :
  forall g, f64_format g -> G g /\ Rabs g < bpow radix2 1024.
Proof.
intros g (w & _ & <-). split.
- exact (generic_format_B2R 53 1024 w).
- exact (abs_B2R_lt_emax 53 1024 w).
Qed.

(** The float of [G] below [2^1024] is [2^1024 - 2^971], the largest
    finite [f64], so every float of [G] below [2^1024] is at most it. *)
Lemma G_le_max :
  forall g, G g -> g < bpow radix2 1024 -> g <= bpow radix2 1024 - bpow radix2 971.
Proof.
intros g Gg Hg.
assert (E : pred radix2 (SpecFloat.fexp 53 1024) (bpow radix2 1024) =
            bpow radix2 1024 - bpow radix2 971)
  by (rewrite pred_bpow; reflexivity).
rewrite <- E. apply pred_ge_gt; [typeclasses eauto | exact Gg | | exact Hg].
apply generic_format_bpow. unfold SpecFloat.fexp, SpecFloat.emin. lia.
Qed.

(** Rounding to [G], to a result that is a finite [f64], is rounding to
    the finite [f64]s, as these are in [G]. *)
Lemma finite_round_ok :
  forall rnd y (z : f64), is_finite z = true -> rnd_pt G rnd y (B2R z) ->
  mpfr_round f64_format rnd y (with_val z).
Proof.
intros rnd y z Fz Hz.
assert (Fx : f64_format (B2R z)) by exact (f64_format_B2R z Fz).
assert (Hpt : rnd_pt f64_format rnd y (B2R z)).
{ destruct rnd; cbn [rnd_pt] in *; destruct Hz as (_ & Hzy & Hext);
    (split; [exact Fx|]); (split; [exact Hzy|]);
    intros g Fg Hg; exact (Hext g (proj1 (f64_format_G g Fg)) Hg). }
destruct (with_val_finite_cases z Fz) as [(s & -> & H0) | (-> & H0)].
- rewrite H0 in Hpt. destruct rnd; exact Hpt.
- destruct rnd; (split; [exact H0 | exact Hpt]).
Qed.

(** [round_f64 rnd y] is the [f64] whose real is [x], [y] rounded to [G]
    in the direction [rnd], if [x] is below [2^1024] in magnitude, and
    otherwise the overflow of [binary_normalize]. As [x] is in [G], the
    rounding that [binary_normalize] does is the identity on it. *)
Lemma round_f64_cases :
  forall rnd y,
  let x := round radix2 (SpecFloat.fexp 53 1024) (round_mode (f64_mode rnd)) y in
  (Rabs x < bpow radix2 1024 /\ is_finite (round_f64 rnd y) = true /\
   B2R (round_f64 rnd y) = x) \/
  (bpow radix2 1024 <= Rabs x /\
   B2SF (round_f64 rnd y) = binary_overflow 53 1024 (f64_mode rnd) (Rlt_bool x 0)).
Proof.
intros rnd y x.
pose proof (binary_normalize_correct 53 1024 _ _ (f64_mode rnd)
  (round_mode (f64_mode rnd) (scaled_mantissa radix2 (SpecFloat.fexp 53 1024) y))
  (cexp radix2 (SpecFloat.fexp 53 1024) y) false) as Hn.
cbv zeta in Hn.
(* [round] is defined as this [F2R], so the argument of [binary_normalize]
   is [x]. *)
change (F2R (Float radix2
               (round_mode (f64_mode rnd) (scaled_mantissa radix2 (SpecFloat.fexp 53 1024) y))
               (cexp radix2 (SpecFloat.fexp 53 1024) y))) with x in Hn.
fold (round_f64 rnd y) in Hn.
assert (Gx : G x) by (apply generic_format_round; typeclasses eauto).
rewrite (round_generic radix2 _ _ x Gx) in Hn.
destruct (Rlt_dec (Rabs x) (bpow radix2 1024)) as [Hlt | Hge].
- rewrite Rlt_bool_true in Hn by exact Hlt.
  destruct Hn as (Hv & Hf & _). left. split; [exact Hlt|]. split; [exact Hf | exact Hv].
- apply Rnot_lt_le in Hge. rewrite Rlt_bool_false in Hn by exact Hge.
  right. split; [exact Hge | exact Hn].
Qed.

(** Below the overflow, [round_f64 rnd y] is [y] rounded to [G], which is a
    finite [f64]. At the overflow, it is an infinity if no finite [f64] is
    on the far side of [y], and otherwise the largest finite [f64] or its
    negation, which is at least (or at most) every finite [f64]. *)
Lemma round_f64_correct :
  forall rnd y, mpfr_round f64_format rnd y (with_val (round_f64 rnd y)).
Proof.
intros rnd y.
assert (Hx : rnd_pt G rnd y
               (round radix2 (SpecFloat.fexp 53 1024) (round_mode (f64_mode rnd)) y)).
{ destruct rnd; cbn [rnd_pt f64_mode round_mode];
    [apply round_DN_pt | apply round_UP_pt]; typeclasses eauto. }
pose proof (round_f64_cases rnd y) as Hc. cbv zeta in Hc.
set (x := round radix2 (SpecFloat.fexp 53 1024) (round_mode (f64_mode rnd)) y) in Hx, Hc.
clearbody x.
destruct Hc as [(_ & Fz & Ez) | (Hb & Ez)].
{ apply finite_round_ok; [exact Fz|]. rewrite Ez. exact Hx. }
(* Overflow: [|x|] is at least [2^1024]. The finite result of the overflow
   is the largest finite [f64] or its negation, of significand [2^53 - 1]
   and exponent [971], so of real [2^1024 - 2^971] in magnitude. *)
assert (HM : F2R (Float radix2 (2 ^ 53 - 1) 971) = bpow radix2 1024 - bpow radix2 971).
{ unfold F2R; cbn [Fnum Fexp]. rewrite minus_IZR.
  change (IZR (2 ^ 53)) with (bpow radix2 53).
  rewrite Rmult_minus_distr_r, <- bpow_plus, Rmult_1_l. reflexivity. }
assert (HM0 : 0 < bpow radix2 971) by apply bpow_gt_0.
assert (HM1 : bpow radix2 971 < bpow radix2 1024) by (apply bpow_lt; lia).
destruct (Rlt_dec x 0) as [Hneg | Hpos].
- rewrite Rlt_bool_true in Ez by exact Hneg.
  rewrite Rabs_left in Hb by exact Hneg.
  destruct rnd; cbn [f64_mode binary_overflow overflow_to_inf negb] in Ez;
    destruct (round_f64 _ y) as [s|s| |s m e H]; cbn [B2SF] in Ez; try discriminate Ez.
  + (* Toward -inf, -inf: a finite [f64] at or below [y] would be at or
       below [x], so at or below [-2^1024]. *)
    injection Ez as ->. cbn [with_val mpfr_round].
    intros g Fg. apply Rnot_le_lt. intros Hg.
    destruct (f64_format_G g Fg) as [Gg Hg1]. apply Rabs_lt_inv in Hg1.
    cbn [rnd_pt] in Hx. destruct Hx as (_ & _ & Hext). pose proof (Hext g Gg Hg). lra.
  + (* Toward +inf, [-MAX]: [y] is at or below [x], so below [-MAX], and
       every finite [f64] is at least [-MAX]. *)
    injection Ez as -> -> ->.
    set (z := B754_finite true _ _ H).
    assert (EB : B2R z = - (bpow radix2 1024 - bpow radix2 971)).
    { rewrite <- HM, <- F2R_Zopp. reflexivity. }
    assert (Fb : f64_format (- (bpow radix2 1024 - bpow radix2 971)))
      by (rewrite <- EB; apply f64_format_B2R; reflexivity).
    change (with_val z) with (MNum (B2R z)). cbn [mpfr_round]. rewrite EB.
    split; [lra|]. cbn [rnd_pt] in Hx. destruct Hx as (_ & Hyx & _).
    split; [exact Fb|]. split; [lra|].
    intros g Fg _. destruct (f64_format_G g Fg) as [Gg Hg1].
    assert (Hg2 : - g <= bpow radix2 1024 - bpow radix2 971).
    { apply G_le_max; [apply generic_format_opp; exact Gg|].
      apply Rabs_lt_inv in Hg1. lra. }
    lra.
- apply Rnot_lt_le in Hpos.
  rewrite Rlt_bool_false in Ez by exact Hpos.
  rewrite Rabs_pos_eq in Hb by exact Hpos.
  destruct rnd; cbn [f64_mode binary_overflow overflow_to_inf negb] in Ez;
    destruct (round_f64 _ y) as [s|s| |s m e H]; cbn [B2SF] in Ez; try discriminate Ez.
  + (* Toward -inf, [MAX]: [y] is at or above [x], so above [MAX], and
       every finite [f64] is at most [MAX]. *)
    injection Ez as -> -> ->.
    set (z := B754_finite false _ _ H).
    assert (EB : B2R z = bpow radix2 1024 - bpow radix2 971).
    { rewrite <- HM. reflexivity. }
    assert (Fb : f64_format (bpow radix2 1024 - bpow radix2 971))
      by (rewrite <- EB; apply f64_format_B2R; reflexivity).
    change (with_val z) with (MNum (B2R z)). cbn [mpfr_round]. rewrite EB.
    split; [lra|]. cbn [rnd_pt] in Hx. destruct Hx as (_ & Hxy & _).
    split; [exact Fb|]. split; [lra|].
    intros g Fg _. destruct (f64_format_G g Fg) as [Gg Hg1].
    apply G_le_max; [exact Gg|]. apply Rabs_lt_inv in Hg1. lra.
  + (* Toward +inf, +inf: a finite [f64] at or above [y] would be at or
       above [x], so at or above [2^1024]. *)
    injection Ez as ->. cbn [with_val mpfr_round].
    intros g Fg. apply Rnot_le_lt. intros Hg.
    destruct (f64_format_G g Fg) as [Gg Hg1]. apply Rabs_lt_inv in Hg1.
    cbn [rnd_pt] in Hx. destruct Hx as (_ & _ & Hext). pose proof (Hext g Gg Hg). lra.
Qed.

Theorem ideal_get_d_ok : forall emin emax a b, get_d_ok emin emax (ideal a b).
Proof.
intros emin emax a b. split; [|split].
- intros rnd y _ _. exact (round_f64_correct rnd y).
- intros rnd s. exists s. reflexivity.
- intros rnd s. reflexivity.
Qed.
