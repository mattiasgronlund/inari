(** * The fast path of [hypot]

    [DyadicRoot.fast_hypot] and [DyadicRoot.fast_hypot_near] take
    [big = max(|x|, |y|)] and [small = min(|x|, |y|)], return the rule of
    [FastHypotFar.v] where their biased exponents differ by 27 or more,
    and otherwise round the double-double of [hypot_dd] ([FastHypotDd.v])
    with [Fast.round_dir_err] and [Fast.round_near_err]
    ([fast_hypot_dir_correct], [fast_hypot_near_correct]). With an FMA
    they return the same ([fast_hypot_dir_fma], [fast_hypot_near_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model DyDriver NearF64 FastHypotFar FastHypotDd.
From Inari Require FastRoundErr.

Open Scope R_scope.

(** ** Lemmas *)

(** [B2R] of an [f64] literal, by computation (as in [FastExpEdge.v]). *)
Local Ltac lit_B2R :=
  match goal with |- B2R ?l = _ =>
    rewrite <- (SF2R_B2SF _ _ l);
    let s := eval vm_compute in (B2SF l) in
    replace (B2SF l) with s by (vm_compute; reflexivity);
    cbn [SF2R SpecFloat.cond_Zopp]; unfold F2R; cbn [Fnum Fexp]; rewrite ?opp_IZR end.

(** [ERR_HYPOT] is 2^-98: the significand 2^52 times 2^-150. *)
Local Lemma lit_err_hypot : B2R DyadicRoot.err_hypot = bpow radix2 (-98).
Proof.
lit_B2R. change (IZR 4503599627370496) with (bpow radix2 52). rewrite <- bpow_plus.
reflexivity.
Qed.

(** As in [FastPow.v]. *)
Local Lemma scale_back : forall y e, y = y * bpow radix2 (- e) * bpow radix2 e.
Proof.
intros y e. rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l.
change (bpow radix2 0) with 1. ring.
Qed.

(** [big] and [small] as both functions order them, by [ge] of the
    absolute values as [hypot_odd] does ([DyHypotOdd.v]): finite, with
    [0 < small <= big], and with the sum of the squares of [x] and [y]. *)
Local Lemma order :
  forall x y,
  is_finite x = true -> is_finite y = true -> B2R x <> 0 -> B2R y <> 0 ->
  exists big small,
  (if ge (fabs x) (fabs y) then (fabs x, fabs y) else (fabs y, fabs x)) = (big, small) /\
  is_finite big = true /\ is_finite small = true /\ 0 < B2R small <= B2R big /\
  B2R x * B2R x + B2R y * B2R y = B2R big * B2R big + B2R small * B2R small.
Proof.
intros x y Fx Fy Hx Hy.
assert (Fax : is_finite (fabs x) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fx).
assert (Fay : is_finite (fabs y) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fy).
assert (Rx : B2R (fabs x) = Rabs (B2R x)) by (unfold fabs; apply B2R_Babs).
assert (Ry : B2R (fabs y) = Rabs (B2R y)) by (unfold fabs; apply B2R_Babs).
pose proof (Rabs_pos_lt _ Hx) as Px.
pose proof (Rabs_pos_lt _ Hy) as Py.
(* [r^2 = |r|^2]. *)
assert (Sq : forall r, r * r = Rabs r * Rabs r)
  by (intros r; unfold Rabs; destruct (Rcase_abs r); ring).
(* [ge a b] is [b <= a] for finite [a] and [b]. *)
assert (G : ge (fabs x) (fabs y) = Rle_bool (B2R (fabs y)) (B2R (fabs x)))
  by (unfold ge; apply Bleb_correct; assumption).
rewrite G.
destruct (Rle_bool_spec (B2R (fabs y)) (B2R (fabs x))) as [L | L].
- exists (fabs x), (fabs y).
  split; [reflexivity |]. split; [exact Fax |]. split; [exact Fay |].
  rewrite Rx, Ry in *. split; [lra |].
  rewrite (Sq (B2R x)), (Sq (B2R y)). reflexivity.
- exists (fabs y), (fabs x).
  split; [reflexivity |]. split; [exact Fay |]. split; [exact Fax |].
  rewrite Rx, Ry in *. split; [lra |].
  rewrite (Sq (B2R x)), (Sq (B2R y)). ring.
Qed.

(** ** The theorems *)

Theorem fast_hypot_dir_correct :
  forall fma x y up v,
  is_finite x = true -> is_finite y = true -> B2R x <> 0 -> B2R y <> 0 ->
  DyadicRoot.fast_hypot fma x y up = Some v ->
  rounds up (sqrt (B2R x * B2R x + B2R y * B2R y)) v.
Proof.
intros fma x y up v Fx Fy Hx Hy H.
destruct (order x y Fx Fy Hx Hy) as (big & small & E & Fb & Fs & Hbs & Hsum).
rewrite Hsum.
unfold DyadicRoot.fast_hypot in H. rewrite E in H. cbv beta iota in H.
destruct (27 <=? Z.shiftr (to_bits big) 52 - Z.shiftr (to_bits small) 52)%Z eqn:G.
- (* A gap of 27 or more: the rule of [FastHypotFar.v]. *)
  injection H as <-. apply hypot_far_dir; try assumption. apply Z.leb_le. exact G.
- (* Otherwise [hypot_dd] gives [hypot(big, small) 2^-e] within 2^-98. *)
  destruct (DyadicRoot.hypot_dd fma big small) as [[[h l] e] |] eqn:D; [| discriminate H].
  apply Z.leb_gt in G.
  destruct (hypot_dd_correct fma big small h l e Fb Fs Hbs G D) as (Fh & Fl & Rh & He & Hb).
  rewrite (scale_back (sqrt (B2R big * B2R big + B2R small * B2R small)) e).
  exact (FastRoundErr.round_dir_err_correct h l e DyadicRoot.err_hypot 98 up v _
    Fh Fl Rh He ltac:(lia) lit_err_hypot Hb H).
Qed.

Theorem fast_hypot_near_correct :
  forall fma x y v,
  is_finite x = true -> is_finite y = true -> B2R x <> 0 -> B2R y <> 0 ->
  DyadicRoot.fast_hypot_near fma x y = Some v ->
  near_round (sqrt (B2R x * B2R x + B2R y * B2R y)) v.
Proof.
intros fma x y v Fx Fy Hx Hy H.
destruct (order x y Fx Fy Hx Hy) as (big & small & E & Fb & Fs & Hbs & Hsum).
rewrite Hsum.
unfold DyadicRoot.fast_hypot_near in H. rewrite E in H. cbv beta iota in H.
destruct (27 <=? Z.shiftr (to_bits big) 52 - Z.shiftr (to_bits small) 52)%Z eqn:G.
- (* A gap of 27 or more: the rule of [FastHypotFar.v]. *)
  injection H as <-. apply hypot_far_near; try assumption. apply Z.leb_le. exact G.
- (* Otherwise [hypot_dd] gives [hypot(big, small) 2^-e] within 2^-98. *)
  destruct (DyadicRoot.hypot_dd fma big small) as [[[h l] e] |] eqn:D; [| discriminate H].
  apply Z.leb_gt in G.
  destruct (hypot_dd_correct fma big small h l e Fb Fs Hbs G D) as (Fh & Fl & Rh & He & Hb).
  rewrite (scale_back (sqrt (B2R big * B2R big + B2R small * B2R small)) e).
  exact (FastRoundErr.round_near_err_correct h l e DyadicRoot.err_hypot 98 v _
    Fh Fl Rh He ltac:(lia) lit_err_hypot Hb H).
Qed.

Theorem fast_hypot_dir_fma :
  forall x y up,
  is_finite x = true -> is_finite y = true -> B2R x <> 0 -> B2R y <> 0 ->
  DyadicRoot.fast_hypot true x y up = DyadicRoot.fast_hypot false x y up.
Proof.
intros x y up Fx Fy Hx Hy.
destruct (order x y Fx Fy Hx Hy) as (big & small & E & Fb & Fs & Hbs & _).
unfold DyadicRoot.fast_hypot. rewrite E. cbv beta iota.
(* Only [hypot_dd] depends on the FMA, and the gap of 27 or more skips it. *)
destruct (27 <=? Z.shiftr (to_bits big) 52 - Z.shiftr (to_bits small) 52)%Z eqn:G;
  [reflexivity |].
apply Z.leb_gt in G. rewrite (hypot_dd_fma big small Fb Fs Hbs G). reflexivity.
Qed.

Theorem fast_hypot_near_fma :
  forall x y,
  is_finite x = true -> is_finite y = true -> B2R x <> 0 -> B2R y <> 0 ->
  DyadicRoot.fast_hypot_near true x y = DyadicRoot.fast_hypot_near false x y.
Proof.
intros x y Fx Fy Hx Hy.
destruct (order x y Fx Fy Hx Hy) as (big & small & E & Fb & Fs & Hbs & _).
unfold DyadicRoot.fast_hypot_near. rewrite E. cbv beta iota.
(* Only [hypot_dd] depends on the FMA, and the gap of 27 or more skips it. *)
destruct (27 <=? Z.shiftr (to_bits big) 52 - Z.shiftr (to_bits small) 52)%Z eqn:G;
  [reflexivity |].
apply Z.leb_gt in G. rewrite (hypot_dd_fma big small Fb Fs Hbs G). reflexivity.
Qed.
