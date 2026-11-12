(** * The fast path of [cbrt]

    [DyadicRoot.fast_cbrt fma x], for a finite nonzero [x], writes
    [|x| = zz 2^(3 e)] with [zz] in [1, 8) from the bits of [x] and
    returns [None] or a double-double [(h, l)] with [h = RN (h + l)]
    within 2^-65 of [Rcbrt |x| 2^-e], for [e] in [-358, 341]
    ([fast_cbrt_correct], from [cbrt_split_bits] and [cbrt_zz_rr] of
    [FastCbrtReduce.v] and [cbrt_step_correct] of [FastCbrtStep.v]).
    [DyadicRoot.fast_cbrt_dir] and [DyadicRoot.fast_cbrt_near] then
    round it with [Fast.round_dir_err] and [Fast.round_near_err], and put
    the sign back ([fast_cbrt_dir_correct], [fast_cbrt_near_correct]).
    With an FMA they return the same ([fast_cbrt_dir_fma],
    [fast_cbrt_near_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Elementary TwoSum DyDriver NearF64 FastCbrtStep.
From Inari Require Import FastCbrtReduce.
From Inari Require FastRoundErr FastSign RoundOpp NearCells RootReal.

Open Scope R_scope.

(** [err_cbrt], [0x3be0000000000000], is 2^-65. *)
Local Lemma err_cbrt_R : B2R DyadicRoot.err_cbrt = bpow radix2 (-65).
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicRoot.err_cbrt) with (SpecFloat.S754_finite false 4503599627370496 (-117))
  by (vm_compute; reflexivity).
cbn [SF2R SpecFloat.cond_Zopp]. unfold F2R; cbn [Fnum Fexp].
change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus. reflexivity.
Qed.

Local Lemma scale_back : forall y e, y = y * bpow radix2 (- e) * bpow radix2 e.
Proof.
intros y e. rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l.
change (bpow radix2 0) with 1. ring.
Qed.

Theorem fast_cbrt_correct :
  forall fma x h l e,
  is_finite x = true -> B2R x <> 0 ->
  DyadicRoot.fast_cbrt fma x = Some (h, l, e) ->
  is_finite h = true /\ is_finite l = true /\ B2R h = RN (B2R h + B2R l) /\
  (-358 <= e <= 341)%Z /\
  Rabs (Rcbrt (Rabs (B2R x)) * bpow radix2 (- e) - (B2R h + B2R l)) <= bpow radix2 (-65).
Proof.
intros fma x h l e Fx Hx0 H.
unfold DyadicRoot.fast_cbrt in H. cbv beta zeta in H.
lazymatch type of H with
| (match ?P with pair _ _ => _ end) = _ => destruct P as [m e0] eqn:EP
end.
cbv beta iota in H.
destruct (cbrt_split_bits x m e0 Fx Hx0 EP) as (Hm & He0 & Hax).
assert (HD : (e0 + 3072 = 3 * ((e0 + 3072) / 3) + (e0 + 3072) mod 3)%Z)
  by (apply Z.div_mod; lia).
assert (HM : (0 <= (e0 + 3072) mod 3 < 3)%Z) by (apply Z.mod_pos_bound; lia).
set (et := ((e0 + 3072) / 3)%Z) in *.
set (i := ((e0 + 3072) mod 3)%Z) in *.
assert (Hi : (0 <= i <= 2)%Z) by lia.
pose proof (cbrt_zz_rr m i Hm Hi) as HZ. cbv zeta in HZ.
destruct HZ as (Fzz & Ezz & Hzz & Frr & Hrr).
lazymatch type of H with
| (match DyadicRoot.cbrt_step ?f ?y ?z ?r with Some _ => _ | None => _ end) = _ =>
  destruct (DyadicRoot.cbrt_step f y z r) as [[h' l']|] eqn:ES; [|discriminate H]
end.
injection H as Eh El Ee. subst h' l' e.
destruct (cbrt_step_correct fma _ _ _ h l Fzz Frr Hzz Hrr ES) as (Fh & Fl & Ehl & Hb).
set (zz := from_bits (Z.lor m 0x3ff0000000000000 + Z.shiftl i 52)%Z) in *.
split; [exact Fh | split; [exact Fl | split; [exact Ehl | split; [lia |]]]].
(* [|x| = (2^52 + m) 2^(e0 - 1075)] and [zz = (2^52 + m) 2^(i - 52)] with
   [e0 + 3072 = 3 et + i], so [|x| = zz 2^(3 (et - 1365))]. *)
assert (HX : Rabs (B2R x) = B2R zz * bpow radix2 (3 * (et - 1365))).
{ rewrite Hax, Ezz, Rmult_assoc, <- bpow_plus.
  replace (i - 52 + 3 * (et - 1365))%Z with (e0 - 1075)%Z by lia. reflexivity. }
(* So the cube root of [|x|] is that of [zz] times [2^(et - 1365)]. *)
assert (HC : Rcbrt (Rabs (B2R x)) = Rcbrt (B2R zz) * bpow radix2 (et - 1365)).
{ apply RootReal.Rcbrt_unique. rewrite HX.
  pose proof (RootReal.Rcbrt_cube (B2R zz)) as Hc.
  set (k := (et - 1365)%Z).
  replace (3 * k)%Z with (k + k + k)%Z by ring.
  rewrite !bpow_plus.
  set (c := Rcbrt (B2R zz)) in *. set (b := bpow radix2 k).
  rewrite <- Hc. ring. }
rewrite HC, Rmult_assoc, <- bpow_plus, Z.add_opp_diag_r.
change (bpow radix2 0) with 1. rewrite Rmult_1_r. exact Hb.
Qed.

Theorem fast_cbrt_dir_correct :
  forall fma x up v,
  is_finite x = true -> B2R x <> 0 ->
  DyadicRoot.fast_cbrt_dir fma x up = Some v ->
  rounds up (Rcbrt (B2R x)) v.
Proof.
intros fma x up v Fx Hx0 H.
unfold DyadicRoot.fast_cbrt_dir in H.
destruct (DyadicRoot.fast_cbrt fma x) as [[[h l] e]|] eqn:E; [|discriminate H].
destruct (Fast.round_dir_err h l e DyadicRoot.err_cbrt (xorb up (lt x zero))) as [r|] eqn:R;
  [|discriminate H].
injection H as <-.
destruct (fast_cbrt_correct fma x h l e Fx Hx0 E) as (Fh & Fl & Ehl & He & Hb).
assert (He' : (-1021 <= e <= 1022)%Z) by lia.
assert (Hp : (55 <= 65 <= 105)%Z) by lia.
pose proof (FastRoundErr.round_dir_err_correct h l e DyadicRoot.err_cbrt 65 _ r _
              Fh Fl Ehl He' Hp err_cbrt_R Hb R) as Hr.
rewrite <- scale_back in Hr.
pose proof (FastSign.lt_zero_R x Fx) as Hs.
destruct (lt x zero).
- (* [x < 0]: [cbrt x = - cbrt (-x)], rounded the other way. *)
  rewrite Rabs_left in Hr by exact Hs.
  rewrite RootReal.Rcbrt_opp in Hr.
  replace (xorb up true) with (negb up) in Hr by (destruct up; reflexivity).
  apply RoundOpp.pown_rnd_opp. exact Hr.
- rewrite Rabs_pos_eq in Hr by exact Hs.
  replace (xorb up false) with up in Hr by (destruct up; reflexivity).
  exact Hr.
Qed.

Theorem fast_cbrt_near_correct :
  forall fma x v,
  is_finite x = true -> B2R x <> 0 ->
  DyadicRoot.fast_cbrt_near fma x = Some v ->
  near_round (Rcbrt (B2R x)) v.
Proof.
intros fma x v Fx Hx0 H.
unfold DyadicRoot.fast_cbrt_near in H.
destruct (DyadicRoot.fast_cbrt fma x) as [[[h l] e]|] eqn:E; [|discriminate H].
destruct (Fast.round_near_err h l e DyadicRoot.err_cbrt) as [r|] eqn:R; [|discriminate H].
injection H as <-.
destruct (fast_cbrt_correct fma x h l e Fx Hx0 E) as (Fh & Fl & Ehl & He & Hb).
assert (He' : (-1021 <= e <= 1022)%Z) by lia.
assert (Hp : (55 <= 65 <= 105)%Z) by lia.
pose proof (FastRoundErr.round_near_err_correct h l e DyadicRoot.err_cbrt 65 r _
              Fh Fl Ehl He' Hp err_cbrt_R Hb R) as Hr.
rewrite <- scale_back in Hr.
pose proof (FastSign.lt_zero_R x Fx) as Hs.
destruct (lt x zero).
- (* [x < 0]: [cbrt x = - cbrt (-x)], and rounding to nearest is odd. *)
  rewrite Rabs_left in Hr by exact Hs.
  rewrite RootReal.Rcbrt_opp in Hr.
  rewrite <- (Ropp_involutive (Rcbrt (B2R x))).
  apply NearCells.near_opp. exact Hr.
- rewrite Rabs_pos_eq in Hr by exact Hs. exact Hr.
Qed.

(** The FMA reaches [fast_cbrt] only through [cbrt_step], whose [zz] is
    in [1, 8) ([cbrt_zz_rr]), where [cbrt_step_fma] applies. *)
Local Lemma fast_cbrt_fma :
  forall x,
  is_finite x = true -> B2R x <> 0 ->
  DyadicRoot.fast_cbrt true x = DyadicRoot.fast_cbrt false x.
Proof.
intros x Fx Hx0.
unfold DyadicRoot.fast_cbrt. cbv beta zeta.
lazymatch goal with
| |- (match ?P with pair _ _ => _ end) = _ => destruct P as [m e0] eqn:EP
end.
cbv beta iota.
destruct (cbrt_split_bits x m e0 Fx Hx0 EP) as (Hm & _ & _).
assert (Hi : (0 <= (e0 + 3072) mod 3 <= 2)%Z)
  by (pose proof (Z.mod_pos_bound (e0 + 3072) 3 ltac:(lia)); lia).
pose proof (cbrt_zz_rr m _ Hm Hi) as HZ. cbv zeta in HZ.
destruct HZ as (Fzz & _ & Hzz & _).
rewrite (cbrt_step_fma _ _ _ Fzz Hzz). reflexivity.
Qed.

Theorem fast_cbrt_dir_fma :
  forall x up,
  is_finite x = true -> B2R x <> 0 ->
  DyadicRoot.fast_cbrt_dir true x up = DyadicRoot.fast_cbrt_dir false x up.
Proof.
intros x up Fx Hx0. unfold DyadicRoot.fast_cbrt_dir.
rewrite (fast_cbrt_fma x Fx Hx0). reflexivity.
Qed.

Theorem fast_cbrt_near_fma :
  forall x,
  is_finite x = true -> B2R x <> 0 ->
  DyadicRoot.fast_cbrt_near true x = DyadicRoot.fast_cbrt_near false x.
Proof.
intros x Fx Hx0. unfold DyadicRoot.fast_cbrt_near.
rewrite (fast_cbrt_fma x Fx Hx0). reflexivity.
Qed.
