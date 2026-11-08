(** * sinh, cosh and tanh in the dyadic kernel

    [sinh_dir], [cosh_dir] and [tanh_dir] of [DyadicExp] in [Model.v]
    apply the rules of [DyHypRules.v], [DySinhTiny.v] and [DyTanhTiny.v]
    where one applies, and otherwise the driver [ziv] to the enclosures of
    [ev_sinh_correct] and the others, as [DyExp.v] does for [exp]:
    [cosh t] and, for [t > 1], [sinh t] from [e^t] and its reciprocal,
    [sinh t] for [t <= 1] as [u (2 - u) / (2 (1 - u))] and [tanh t] as
    [u / (2 - u)] for [u = 1 - e^-t] or [u = 1 - e^-2t], and the odd
    functions from [t = |x|]. [sinh_dir_post] and the others prove, for
    any driver [z] in place of [ziv] ([sinh_dir_with z] and the others)
    and any property [post] that holds of every correct rounding
    ([rounds_post]) and that [z] gives ([driver_post] of [DyDriver.v]),
    that the result has [post] for [sinh], [cosh] and [tanh] of a finite
    [x] and the direction [up]. So with [ziv_strict] the kernel rounds
    correctly where it returns ([sinh_dir_correct] and the others, by
    [ziv_strict_correct]), the Rust returns the same value there
    ([sinh_dir_strict] and the others), and wherever the Rust returns, its
    result is on the side of [up] ([sinh_dir_side] and the others, by
    [ziv_side]). That a rounding test passes by the cap is not
    proved. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Mult_error.
From Inari Require Import Model Mpfr Limbs Elementary ExpReal DyRound DyConv DyOps DyDriver
  DyGrow DyExpCore DyExpRules DyHypRules DySinhTiny DyTanhTiny DyExp.

Open Scope Z_scope.

(** Where [ziv_strict] returns, [Dyadic.ziv] returns the same: the goal
    [<body with ziv_strict> = Some v -> <body with Dyadic.ziv> = Some v]
    of a function of this file, split at its guards, which name neither
    driver. *)
Local Ltac dir_strict :=
  repeat match goal with
  | |- (if ?c then _ else _) = Some _ -> _ => destruct c; [exact (fun h => h)|]
  end;
  apply ziv_strict_ziv.

(** ** Helpers

    [fin_not_nan], [fin_neq_inf], [fin_neq_ninf] and [lt_zero_spec] are
    those of [DyExp.v]. *)

(** If [t > 1.0] is false, the value of [t] is at most 1 ([B2R] is 0 at
    NaN and at -inf). *)
Lemma hyp_gt_one : forall t : f64, gt t DyadicExp.one = false -> (B2R t <= 1)%R.
Proof.
intros t G. destruct (is_finite t) eqn:F.
- unfold gt in G. rewrite Bltb_correct in G; [|reflexivity|exact F].
  rewrite dexp_one_R in G. destruct (Rlt_bool_spec 1 (B2R t)); [discriminate G | lra].
- destruct t as [s|s| |s m e H]; try discriminate F; cbn [B2R]; lra.
Qed.

(** [|x|] *)
Lemma hyp_fabs : forall x : f64, B2R (fabs x) = Rabs (B2R x).
Proof.
intros x. apply B2R_Babs.
Qed.

(** [-2.0] *)
Lemma hyp_m_two_R : B2R DyadicExp.m_two = (-2)%R.
Proof.
rewrite <- SF2R_B2SF.
replace (B2SF DyadicExp.m_two) with (SpecFloat.S754_finite true 4503599627370496 (-51))
  by (vm_compute; reflexivity).
unfold SF2R, F2R. cbn [Fnum Fexp SpecFloat.cond_Zopp].
change (bpow radix2 (-51)) with (/ 2251799813685248)%R.
rewrite opp_IZR. lra.
Qed.

(** [2^-1] and [2^1] *)
Lemma hyp_half : bpow radix2 (-1) = (/ 2)%R.
Proof.
reflexivity.
Qed.

Lemma hyp_two : bpow radix2 1 = 2%R.
Proof.
reflexivity.
Qed.

(** A finite product of [±2.0] and [t] is exact: [±2 t] is in the
    format of [t] shifted by one place, and only an overflow rounds. *)
Lemma hyp_mul_two :
  forall c t : f64,
  (B2R c = 2 \/ B2R c = -2)%R -> is_finite (mul c t) = true ->
  B2R (mul c t) = (B2R c * B2R t)%R.
Proof.
intros c t Hc F.
assert (G : generic_format radix2 (FLT_exp (-1074) 53) (B2R c * B2R t)).
{ assert (G1 : generic_format radix2 (FLT_exp (-1074) 53) (B2R t * bpow radix2 1)).
  { apply mult_bpow_pos_exact_FLT; [apply generic_format_B2R | lia]. }
  rewrite hyp_two in G1.
  destruct Hc as [Hc|Hc]; rewrite Hc.
  - rewrite Rmult_comm. exact G1.
  - replace (-2 * B2R t)%R with (- (B2R t * 2))%R by ring.
    apply generic_format_opp. exact G1. }
pose proof (Bmult_correct 53 1024 _ _ mode_NE c t) as Hm.
change (SpecFloat.fexp 53 1024) with (FLT_exp (-1074) 53) in Hm.
cbn [round_mode] in Hm. rewrite (round_generic _ _ _ _ G) in Hm.
destruct (Rlt_bool_spec (Rabs (B2R c * B2R t)) (bpow radix2 1024)) as [L|L].
- destruct Hm as (Rm & _). exact Rm.
- unfold mul in F. rewrite <- is_finite_SF_B2SF, Hm in F. discriminate F.
Qed.

(** If [exp_encl n x] returns, [x] is finite: it takes [Encl::point(x)]. *)
Lemma hyp_exp_encl_finite :
  forall n x c, level_ok n -> DyadicExp.exp_encl n x = Some c -> is_finite x = true.
Proof.
intros n x c Hn H. unfold DyadicExp.exp_encl in H.
destruct (DyadicExp.to_k (fceil (mul x DyadicExp.log2_e))) as [k|]; [|discriminate H].
destruct (DyadicConsts.ln2 n) as [[h l]|]; [|discriminate H].
destruct (DyadicExp.mul_int n {| Dyadic.en_lo := h; Dyadic.en_hi := h |} k) as [a|];
  [|discriminate H].
destruct (Dyadic.encl_point n x) as [px|] eqn:Ep; [|discriminate H].
exact (proj2 (proj2 (proj2 (proj2 (point_step n x px Hn Ep))))).
Qed.

(** ** The enclosures *)

(** [cosh t = (e^t + 1 / e^t) / 2] *)
Lemma ev_cosh_correct :
  forall t n a,
  level_ok n -> DyadicExp.ev_cosh t n = Some a -> encl_ok n a /\ encl_has a (cosh (B2R t)).
Proof.
intros t n a Hn H. unfold DyadicExp.ev_cosh in H.
destruct (DyadicExp.exp_encl n t) as [e|] eqn:Ee; [|discriminate H].
destruct (Dyadic.encl_point n DyadicExp.one) as [one_e|] eqn:E1; [|discriminate H].
destruct (Dyadic.encl_div n one_e e) as [r|] eqn:Er; [|discriminate H].
destruct (Dyadic.encl_add n e r) as [s|] eqn:Es; [|discriminate H].
cbv beta iota in H.
destruct (exp_encl_correct n t e Hn Ee) as (Oe & Le & He).
destruct (point_has n _ one_e Hn E1) as (O1 & L1 & H1).
destruct (div_step n one_e e r _ _ Hn O1 Oe L1 Le ltac:(lia) ltac:(lia) Er) as (Or & Lr & Hr).
destruct (add_step n e r s _ _ Hn Oe Or Le Lr ltac:(lia) ltac:(lia) Es) as (Os & Ls & Hs).
destruct (shl_step n s (-1) a _ Hn Os Ls ltac:(lia) ltac:(lia) H) as (Oa & _ & Ha).
split; [exact Oa|].
specialize (Ha _ (Hs _ _ He (Hr _ _ H1 He))).
replace (cosh (B2R t))
  with ((exp (B2R t) + B2R DyadicExp.one / exp (B2R t)) * bpow radix2 (-1))%R;
  [exact Ha|].
rewrite dexp_one_R, hyp_half. unfold cosh. rewrite exp_Ropp.
pose proof (exp_pos (B2R t)). field. lra.
Qed.

(** [sinh t = (e^t - 1 / e^t) / 2] for [t > 1], and
    [sinh t = u (2 - u) / (2 (1 - u))] for [u = 1 - e^-t], as
    [u (2 - u) = 1 - e^-2t] and [1 - u = e^-t]; then [sinh (-t) = - sinh t]. *)
Lemma ev_sinh_correct :
  forall x n a,
  level_ok n -> DyadicExp.ev_sinh x n = Some a -> encl_ok n a /\ encl_has a (sinh (B2R x)).
Proof.
intros x n a Hn H. unfold DyadicExp.ev_sinh in H.
set (t := fabs x) in H.
assert (Ht : B2R t = Rabs (B2R x)) by apply hyp_fabs.
destruct (Dyadic.encl_point n DyadicExp.one) as [one_e|] eqn:E1; [|discriminate H].
destruct (point_has n _ one_e Hn E1) as (O1 & L1 & H1).
rewrite dexp_one_R in H1.
(* [s] holds [sinh |x|]. *)
assert (S : forall s,
  (if gt t DyadicExp.one then
     let* e := DyadicExp.exp_encl n t in
     let* r := Dyadic.encl_div n one_e e in
     let* d := Dyadic.encl_sub n e r in
     Dyadic.encl_shl n d (-1)
   else
     let* pt := Dyadic.encl_point n t in
     let* u := DyadicExp.expm1_neg n pt in
     let* two_e := Dyadic.encl_point n DyadicExp.two in
     let* a := Dyadic.encl_sub n two_e u in
     let* num := Dyadic.encl_mul n u a in
     let* b := Dyadic.encl_sub n one_e u in
     let* den := Dyadic.encl_shl n b 1 in
     Dyadic.encl_div n num den) = Some s ->
  encl_ok n s /\ encl_le (2 ^ 50) s /\ encl_has s (sinh (B2R t))).
{ intros s Hs. destruct (gt t DyadicExp.one) eqn:G.
  - destruct (DyadicExp.exp_encl n t) as [e|] eqn:Ee; [|discriminate Hs].
    destruct (Dyadic.encl_div n one_e e) as [r|] eqn:Er; [|discriminate Hs].
    destruct (Dyadic.encl_sub n e r) as [d|] eqn:Ed; [|discriminate Hs].
    cbv beta iota in Hs.
    destruct (exp_encl_correct n t e Hn Ee) as (Oe & Le & He).
    destruct (div_step n one_e e r _ _ Hn O1 Oe L1 Le ltac:(lia) ltac:(lia) Er)
      as (Or & Lr & Hr).
    destruct (sub_step n e r d _ _ Hn Oe Or Le Lr ltac:(lia) ltac:(lia) Ed) as (Od & Ld & Hd).
    destruct (shl_step n d (-1) s _ Hn Od Ld ltac:(lia) ltac:(lia) Hs) as (Os & Ls & Hs').
    split; [exact Os|]. split; [eapply encl_le_mono; [|exact Ls]; lia|].
    specialize (Hs' _ (Hd _ _ He (Hr _ _ H1 He))).
    replace (sinh (B2R t)) with ((exp (B2R t) - 1 / exp (B2R t)) * bpow radix2 (-1))%R;
      [exact Hs'|].
    rewrite hyp_half. unfold sinh. rewrite exp_Ropp.
    pose proof (exp_pos (B2R t)). field. lra.
  - destruct (Dyadic.encl_point n t) as [pt|] eqn:Ep; [|discriminate Hs].
    destruct (DyadicExp.expm1_neg n pt) as [u|] eqn:Eu; [|discriminate Hs].
    destruct (Dyadic.encl_point n DyadicExp.two) as [two_e|] eqn:E2; [|discriminate Hs].
    destruct (Dyadic.encl_sub n two_e u) as [a'|] eqn:Ea; [|discriminate Hs].
    destruct (Dyadic.encl_mul n u a') as [num|] eqn:En; [|discriminate Hs].
    destruct (Dyadic.encl_sub n one_e u) as [b|] eqn:Eb; [|discriminate Hs].
    destruct (Dyadic.encl_shl n b 1) as [den|] eqn:Ed; [|discriminate Hs].
    cbv beta iota in Hs.
    pose proof (hyp_gt_one t G) as Ht1.
    pose proof (Rabs_pos (B2R x)) as Ht0.
    destruct (point_has n t pt Hn Ep) as (Op & Lp & Hp).
    destruct (expm1_neg_correct n pt u (2 ^ 13) (B2R t) Hn Op Lp ltac:(lia) Hp ltac:(lra) Eu)
      as (Ou & Lu & Hu).
    destruct (point_has n _ two_e Hn E2) as (O2 & L2 & H2).
    rewrite dexp_two_R in H2.
    destruct (sub_step n two_e u a' _ _ Hn O2 Ou L2 Lu ltac:(lia) ltac:(lia) Ea)
      as (Oa & La & Ha).
    destruct (mul_step n u a' num _ _ Hn Ou Oa Lu La ltac:(lia) ltac:(lia) En)
      as (On & Ln & Hnum).
    destruct (sub_step n one_e u b _ _ Hn O1 Ou L1 Lu ltac:(lia) ltac:(lia) Eb)
      as (Ob & Lb & Hb).
    destruct (shl_step n b 1 den _ Hn Ob Lb ltac:(lia) ltac:(lia) Ed) as (Od & Ld & Hd).
    destruct (div_step n num den s _ _ Hn On Od Ln Ld ltac:(lia) ltac:(lia) Hs)
      as (Os & Ls & Hs').
    split; [exact Os|]. split; [eapply encl_le_mono; [|exact Ls]; lia|].
    specialize (Hs' _ _ (Hnum _ _ Hu (Ha _ _ H2 Hu)) (Hd _ (Hb _ _ H1 Hu))).
    replace (sinh (B2R t)) with
      ((1 - exp (- B2R t)) * (2 - (1 - exp (- B2R t))) /
       ((1 - (1 - exp (- B2R t))) * bpow radix2 1))%R; [exact Hs'|].
    rewrite hyp_two. unfold sinh. rewrite exp_Ropp.
    pose proof (exp_pos (B2R t)). field. lra. }
destruct (if gt t DyadicExp.one then _ else _) as [s|] eqn:Es in H; [|discriminate H].
cbv beta iota in H. injection H as <-.
destruct (S s Es) as (Os & Ls & Hs).
rewrite Ht in Hs.
destruct (lt_zero_spec x) as (N1 & N2).
destruct (lt x zero) eqn:Lx.
- destruct (neg_step n s _ Hn Os Ls) as (Oa & _ & Ha).
  split; [exact Oa|].
  specialize (Ha _ Hs). rewrite Rabs_left1 in Ha by (apply N1; reflexivity).
  replace (sinh (B2R x)) with (- sinh (- B2R x))%R; [exact Ha|].
  unfold sinh. rewrite Ropp_involutive. field.
- split; [exact Os|].
  rewrite Rabs_pos_eq in Hs by (apply N2; reflexivity). exact Hs.
Qed.

(** [tanh t = u / (2 - u)] for [u = 1 - e^-2t], from [e^-2t] for [t > 1]
    and from [expm1_neg] of [2 t] otherwise; then [tanh (-t) = - tanh t]. *)
Lemma ev_tanh_correct :
  forall x n a,
  level_ok n -> DyadicExp.ev_tanh x n = Some a -> encl_ok n a /\ encl_has a (tanh (B2R x)).
Proof.
intros x n a Hn H. unfold DyadicExp.ev_tanh in H.
set (t := fabs x) in H.
assert (Ht : B2R t = Rabs (B2R x)) by apply hyp_fabs.
pose proof (Rabs_pos (B2R x)) as Ht0.
(* [u] holds [1 - e^-2|x|]. *)
assert (U : forall u,
  (if gt t DyadicExp.one then
     let* one_e := Dyadic.encl_point n DyadicExp.one in
     let* e := DyadicExp.exp_encl n (mul DyadicExp.m_two t) in
     Dyadic.encl_sub n one_e e
   else
     let* p := Dyadic.encl_point n (mul DyadicExp.two t) in
     DyadicExp.expm1_neg n p) = Some u ->
  encl_ok n u /\ encl_le (2 ^ 49) u /\ encl_has u (1 - exp (- (2 * B2R t)))).
{ intros u Hu. destruct (gt t DyadicExp.one) eqn:G.
  - destruct (Dyadic.encl_point n DyadicExp.one) as [one_e|] eqn:E1; [|discriminate Hu].
    destruct (DyadicExp.exp_encl n (mul DyadicExp.m_two t)) as [e|] eqn:Ee; [|discriminate Hu].
    cbv beta iota in Hu.
    destruct (point_has n _ one_e Hn E1) as (O1 & L1 & H1).
    rewrite dexp_one_R in H1.
    destruct (exp_encl_correct n _ e Hn Ee) as (Oe & Le & He).
    rewrite (hyp_mul_two DyadicExp.m_two t), hyp_m_two_R in He;
      [| right; exact hyp_m_two_R | exact (hyp_exp_encl_finite n _ e Hn Ee)].
    destruct (sub_step n one_e e u _ _ Hn O1 Oe L1 Le ltac:(lia) ltac:(lia) Hu)
      as (Ou & Lu & Hu').
    split; [exact Ou|]. split; [eapply encl_le_mono; [|exact Lu]; lia|].
    specialize (Hu' _ _ H1 He).
    replace (- (2 * B2R t))%R with (-2 * B2R t)%R by ring. exact Hu'.
  - destruct (Dyadic.encl_point n (mul DyadicExp.two t)) as [p|] eqn:Ep; [|discriminate Hu].
    cbv beta iota in Hu.
    pose proof (hyp_gt_one t G) as Ht1.
    destruct (point_step n _ p Hn Ep) as (_ & _ & _ & _ & Fp).
    destruct (point_has n _ p Hn Ep) as (Op & Lp & Hp).
    rewrite (hyp_mul_two DyadicExp.two t), dexp_two_R in Hp;
      [| left; exact dexp_two_R | exact Fp].
    destruct (expm1_neg_correct n p u (2 ^ 13) (2 * B2R t) Hn Op Lp ltac:(lia) Hp ltac:(lra) Hu)
      as (Ou & Lu & Hu').
    split; [exact Ou|]. split; [eapply encl_le_mono; [|exact Lu]; lia|]. exact Hu'. }
destruct (if gt t DyadicExp.one then _ else _) as [u|] eqn:Eu in H; [|discriminate H].
cbv beta iota in H.
destruct (U u Eu) as (Ou & Lu & Hu).
destruct (Dyadic.encl_point n DyadicExp.two) as [two_e|] eqn:E2; [|discriminate H].
destruct (Dyadic.encl_sub n two_e u) as [d|] eqn:Ed; [|discriminate H].
destruct (Dyadic.encl_div n u d) as [r|] eqn:Er; [|discriminate H].
cbv beta iota in H. injection H as <-.
destruct (point_has n _ two_e Hn E2) as (O2 & L2 & H2).
rewrite dexp_two_R in H2.
destruct (sub_step n two_e u d _ _ Hn O2 Ou L2 Lu ltac:(lia) ltac:(lia) Ed) as (Od & Ld & Hd).
destruct (div_step n u d r _ _ Hn Ou Od Lu Ld ltac:(lia) ltac:(lia) Er) as (Or & Lr & Hr).
specialize (Hr _ _ Hu (Hd _ _ H2 Hu)).
(* [r] holds [tanh |x|]. *)
replace ((1 - exp (- (2 * B2R t))) / (2 - (1 - exp (- (2 * B2R t)))))%R
  with (tanh (B2R t)) in Hr.
2: { rewrite tanh_eq, exp_Ropp. pose proof (exp_pos (2 * B2R t)). field. lra. }
rewrite Ht in Hr.
destruct (lt_zero_spec x) as (N1 & N2).
destruct (lt x zero) eqn:Lx.
- destruct (neg_step n r _ Hn Or Lr) as (Oa & _ & Ha).
  split; [exact Oa|].
  specialize (Ha _ Hr). rewrite Rabs_left1 in Ha by (apply N1; reflexivity).
  rewrite tanh_odd, Ropp_involutive in Ha. exact Ha.
- split; [exact Or|].
  rewrite Rabs_pos_eq in Hr by (apply N2; reflexivity). exact Hr.
Qed.

(** ** The functions *)

Lemma sinh_dir_post :
  forall z post, rounds_post post -> driver_post z post ->
  forall x up v,
  is_finite x = true -> DyadicExp.sinh_dir_with z x up = Some v ->
  post up (sinh (B2R x)) v.
Proof.
intros z post Hp Hz x up v Fx H. unfold DyadicExp.sinh_dir_with in H.
rewrite (fin_not_nan x Fx), (fin_neq_inf x Fx), (fin_neq_ninf x Fx) in H. cbn [orb] in H.
destruct (ge x (from_bits 0x4086380000000000)) eqn:G1; cbv iota in H.
{ injection H as <-. apply Hp. exact (sinh_overflow_rule x up Fx G1). }
destruct (le x (from_bits 0xc086380000000000)) eqn:G2; cbv iota in H.
{ injection H as <-. apply Hp. exact (sinh_overflow_neg_rule x up Fx G2). }
destruct (lt (fabs x) DyadicExp.tiny_hyp) eqn:G3; cbv iota in H.
{ injection H as <-. apply Hp. exact (sinh_tiny_rule x up Fx G3). }
apply (Hz (DyadicExp.ev_sinh x) up 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_sinh_correct x n a Hn Ha).
Qed.

Theorem sinh_dir_correct :
  forall x up v,
  is_finite x = true -> DyadicExp.sinh_dir_with ziv_strict x up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (sinh (B2R x)) (with_val v).
Proof. exact (sinh_dir_post ziv_strict rounds (fun _ _ _ H => H) ziv_strict_correct). Qed.

Theorem sinh_dir_side :
  forall x up v,
  is_finite x = true -> DyadicExp.sinh_dir x up = Some v ->
  f64_side up (sinh (B2R x)) v.
Proof. exact (sinh_dir_post Dyadic.ziv f64_side rounds_side ziv_side). Qed.

Theorem sinh_dir_strict :
  forall x up v,
  DyadicExp.sinh_dir_with ziv_strict x up = Some v -> DyadicExp.sinh_dir x up = Some v.
Proof.
intros x up v. unfold DyadicExp.sinh_dir, DyadicExp.sinh_dir_with. dir_strict.
Qed.

Lemma cosh_dir_post :
  forall z post, rounds_post post -> driver_post z post ->
  forall x up v,
  is_finite x = true -> DyadicExp.cosh_dir_with z x up = Some v ->
  post up (cosh (B2R x)) v.
Proof.
intros z post Hp Hz x up v Fx H. unfold DyadicExp.cosh_dir_with in H. cbv zeta in H.
assert (Ft : is_finite (fabs x) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fx).
rewrite (fin_not_nan _ Ft), (fin_neq_inf _ Ft) in H. cbn [orb] in H.
destruct (ge (fabs x) (from_bits 0x4086380000000000)) eqn:G1; cbv iota in H.
{ injection H as <-. apply Hp. exact (cosh_overflow_rule x up Fx G1). }
destruct (lt (fabs x) DyadicExp.tiny_hyp) eqn:G3; cbv iota in H.
{ injection H as <-. apply Hp. exact (cosh_tiny_rule x up Fx G3). }
apply (Hz (DyadicExp.ev_cosh (fabs x)) up 1%nat); [|exact H].
intros n a Hn Ha. destruct (ev_cosh_correct _ n a Hn Ha) as (Oa & Ha').
split; [exact Oa|].
rewrite hyp_fabs in Ha'.
destruct (Rle_or_lt 0 (B2R x)) as [P|P].
- rewrite Rabs_pos_eq in Ha' by exact P. exact Ha'.
- rewrite Rabs_left in Ha' by exact P. rewrite cosh_even in Ha'. exact Ha'.
Qed.

Theorem cosh_dir_correct :
  forall x up v,
  is_finite x = true -> DyadicExp.cosh_dir_with ziv_strict x up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (cosh (B2R x)) (with_val v).
Proof. exact (cosh_dir_post ziv_strict rounds (fun _ _ _ H => H) ziv_strict_correct). Qed.

Theorem cosh_dir_side :
  forall x up v,
  is_finite x = true -> DyadicExp.cosh_dir x up = Some v ->
  f64_side up (cosh (B2R x)) v.
Proof. exact (cosh_dir_post Dyadic.ziv f64_side rounds_side ziv_side). Qed.

Theorem cosh_dir_strict :
  forall x up v,
  DyadicExp.cosh_dir_with ziv_strict x up = Some v -> DyadicExp.cosh_dir x up = Some v.
Proof.
intros x up v. unfold DyadicExp.cosh_dir, DyadicExp.cosh_dir_with. cbv zeta. dir_strict.
Qed.

Lemma tanh_dir_post :
  forall z post, rounds_post post -> driver_post z post ->
  forall x up v,
  is_finite x = true -> DyadicExp.tanh_dir_with z x up = Some v ->
  post up (tanh (B2R x)) v.
Proof.
intros z post Hp Hz x up v Fx H. unfold DyadicExp.tanh_dir_with in H.
rewrite (fin_not_nan x Fx), (fin_neq_inf x Fx), (fin_neq_ninf x Fx) in H. cbv iota in H.
destruct (ge x (from_bits 0x4033000000000000)) eqn:G1; cbv iota in H.
{ injection H as <-. apply Hp. exact (tanh_big_rule x up Fx G1). }
destruct (le x (from_bits 0xc033000000000000)) eqn:G2; cbv iota in H.
{ injection H as <-. apply Hp. exact (tanh_big_neg_rule x up Fx G2). }
destruct (lt (fabs x) DyadicExp.tiny_hyp) eqn:G3; cbv iota in H.
{ injection H as <-. apply Hp. exact (tanh_tiny_rule x up Fx G3). }
apply (Hz (DyadicExp.ev_tanh x) up 1%nat); [|exact H].
intros n a Hn Ha. exact (ev_tanh_correct x n a Hn Ha).
Qed.

Theorem tanh_dir_correct :
  forall x up v,
  is_finite x = true -> DyadicExp.tanh_dir_with ziv_strict x up = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) (tanh (B2R x)) (with_val v).
Proof. exact (tanh_dir_post ziv_strict rounds (fun _ _ _ H => H) ziv_strict_correct). Qed.

Theorem tanh_dir_side :
  forall x up v,
  is_finite x = true -> DyadicExp.tanh_dir x up = Some v ->
  f64_side up (tanh (B2R x)) v.
Proof. exact (tanh_dir_post Dyadic.ziv f64_side rounds_side ziv_side). Qed.

Theorem tanh_dir_strict :
  forall x up v,
  DyadicExp.tanh_dir_with ziv_strict x up = Some v -> DyadicExp.tanh_dir x up = Some v.
Proof.
intros x up v. unfold DyadicExp.tanh_dir, DyadicExp.tanh_dir_with. dir_strict.
Qed.
