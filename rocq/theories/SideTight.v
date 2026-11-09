(** * The tightest record beside a record on the correct side

    For a record [p] whose fields satisfy [ContractSide.v], [side_tight p]
    is the record whose field of each function [f] is [f] rounded once
    ([round_f64] of [MpfrIdeal.v]) at the finite arguments in the domain
    of [f], and [p]'s field elsewhere. Its fields satisfy [Contract.v]
    ([exp_tight_c] and the others), as every special value of
    [Contract.v] is at an infinite argument or at a finite one outside
    the domain, where it keeps [p]'s. [p]'s fields are outward of its
    fields ([exp_tight_out] and the others), as a value on the side
    [rnd] of a real is at or beyond the real rounded in the direction
    [rnd], and the two records give the same [quadrant] at every
    argument ([quadrant_tight]), by the signs that [sin_s] and [cos_s]
    ask for. [exp_c_s] and the others check that [ContractSide.v] asks
    no more than [Contract.v]: a record that satisfies [exp_c] satisfies
    [exp_s]. [ContractSide.v] says nothing of the fields of [cbrt] and
    [hypot], whose functions in the kernel return at every argument and
    round correctly at every finite one ([k_cbrt_some], [k_hypot_some],
    [k_cbrt_c] and [k_hypot_c] of [DyPoint.v]), so [side_tight p] keeps
    [p]'s fields of [cbrt] and [hypot]. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr MpfrRound MpfrIdeal IdealGetD Contract
  ContractSide SideDefs.
From Inari Require TrigPieces.

Open Scope R_scope.

(** ** The deciders of the domains *)

Definition dec_real (r : R) : {real_dom r} + {~ real_dom r}.
Proof. left. exact I. Defined.

Definition dec_log (r : R) : {log_dom r} + {~ log_dom r} := Rlt_dec 0 r.

Definition dec_closed (r : R) : {-1 <= r <= 1} + {~ (-1 <= r <= 1)}.
Proof.
destruct (Rle_dec (-1) r) as [H1|H1]; [|right; intros [H _]; exact (H1 H)].
destruct (Rle_dec r 1) as [H2|H2]; [left; split; assumption|right; intros [_ H]; exact (H2 H)].
Defined.

Definition dec_acosh (r : R) : {acosh_dom r} + {~ acosh_dom r} := Rle_dec 1 r.

Definition dec_atanh (r : R) : {atanh_dom r} + {~ atanh_dom r}.
Proof.
unfold atanh_dom.
destruct (Rlt_dec (-1) r) as [H1|H1]; [|right; intros [H _]; exact (H1 H)].
destruct (Rlt_dec r 1) as [H2|H2]; [left; split; assumption|right; intros [_ H]; exact (H2 H)].
Defined.

Definition dec_atan2 (y x : R) : {y <> 0 \/ 0 < x} + {~ (y <> 0 \/ 0 < x)}.
Proof.
destruct (Req_EM_T y 0) as [Hy|Hy]; [|left; left; exact Hy].
destruct (Rlt_dec 0 x) as [Hx|Hx]; [left; right; exact Hx|].
right. intros [H|H]; [exact (H Hy)|exact (Hx H)].
Defined.

Definition dec_pow (r t : R) : {pow_dom r t} + {~ pow_dom r t}.
Proof.
unfold pow_dom.
destruct (Rlt_dec 0 r) as [Hr|Hr]; [left; left; exact Hr|].
destruct (Req_EM_T r 0) as [H0|H0].
- destruct (Rlt_dec 0 t) as [Ht|Ht]; [left; right; split; assumption|].
  right. intros [H|[_ H]]; [exact (Hr H)|exact (Ht H)].
- right. intros [H|[H _]]; [exact (Hr H)|exact (H0 H)].
Defined.

Definition dec_pown (n : Z) (r : R) : {is_i32 n /\ pown_dom n r} + {~ (is_i32 n /\ pown_dom n r)}.
Proof.
unfold is_i32, pown_dom.
destruct (Z_le_dec (- 2 ^ 31) n) as [H1|H1]; [|right; intros [[H _] _]; exact (H1 H)].
destruct (Z_lt_dec n (2 ^ 31)) as [H2|H2]; [|right; intros [[_ H] _]; exact (H2 H)].
destruct (Z_le_dec 0 n) as [H3|H3]; [left; split; [split; assumption|left; exact H3]|].
destruct (Req_EM_T r 0) as [H4|H4]; [|left; split; [split; assumption|right; exact H4]].
right. intros [_ [H|H]]; [exact (H3 H)|exact (H H4)].
Defined.

(** ** The tightened fields and record *)

Definition tight_field (D : R -> Prop) (dec : forall r, {D r} + {~ D r}) (f : R -> R)
    (h : mpfr_rnd -> f64 -> f64) (rnd : mpfr_rnd) (x : f64) : f64 :=
  if is_finite x then if dec (B2R x) then round_f64 rnd (f (B2R x)) else h rnd x
  else h rnd x.

Definition tight_field2 (D : R -> R -> Prop) (dec : forall r t, {D r t} + {~ D r t})
    (f : R -> R -> R) (h : mpfr_rnd -> f64 -> f64 -> f64) (rnd : mpfr_rnd) (x y : f64) : f64 :=
  if is_finite x && is_finite y then
    if dec (B2R x) (B2R y) then round_f64 rnd (f (B2R x) (B2R y)) else h rnd x y
  else h rnd x y.

Definition tight_field_z (h : mpfr_rnd -> f64 -> Z -> f64) (rnd : mpfr_rnd) (x : f64) (n : Z)
    : f64 :=
  if is_finite x then
    if dec_pown n (B2R x) then round_f64 rnd (powerRZ (B2R x) n) else h rnd x n
  else h rnd x n.

(** [tan] is tightened at every finite argument, which is in [tan_dom]
    ([tan_dom_f64] of [TrigPieces.v]). *)
Definition side_tight (p : point) : point := {|
  p_acos := tight_field acos_dom dec_closed acos (p_acos p);
  p_acosh := tight_field acosh_dom dec_acosh Racosh (p_acosh p);
  p_asin := tight_field asin_dom dec_closed asin (p_asin p);
  p_asinh := tight_field real_dom dec_real arcsinh (p_asinh p);
  p_atan := tight_field real_dom dec_real atan (p_atan p);
  p_atan2 := tight_field2 (fun y x => y <> 0 \/ 0 < x) dec_atan2 Ratan2 (p_atan2 p);
  p_atanh := tight_field atanh_dom dec_atanh Ratanh (p_atanh p);
  p_cbrt := p_cbrt p;
  p_cos := tight_field real_dom dec_real cos (p_cos p);
  p_cosh := tight_field real_dom dec_real cosh (p_cosh p);
  p_exp := tight_field real_dom dec_real exp (p_exp p);
  p_exp10 := tight_field real_dom dec_real Rexp10 (p_exp10 p);
  p_exp2 := tight_field real_dom dec_real Rexp2 (p_exp2 p);
  p_hypot := p_hypot p;
  p_ln := tight_field log_dom dec_log ln (p_ln p);
  p_log10 := tight_field log_dom dec_log Rlog10 (p_log10 p);
  p_log2 := tight_field log_dom dec_log Rlog2 (p_log2 p);
  p_pow := tight_field2 pow_dom dec_pow Rpow (p_pow p);
  p_pown := tight_field_z (p_pown p);
  p_sin := tight_field real_dom dec_real sin (p_sin p);
  p_sinh := tight_field real_dom dec_real sinh (p_sinh p);
  p_tan := tight_field real_dom dec_real tan (p_tan p);
  p_tanh := tight_field real_dom dec_real tanh (p_tanh p)
|}.

(** ** A value on the side of a real is outward of its rounding *)

Lemma on_side_outward :
  forall rnd r v, on_side rnd r v -> outward rnd v (round_f64 rnd r).
Proof.
intros rnd r v Hv. right.
pose proof (round_f64_correct rnd r) as Hw.
set (w := round_f64 rnd r) in *. clearbody w.
unfold Model.le.
destruct (is_finite v) eqn:Fv.
- (* [w] is the float nearest [r] on the side [rnd], so it is beyond [v] *)
  assert (Gv := f64_format_B2R v Fv).
  assert (Hv' : match rnd with RNDD => B2R v <= r | RNDU => r <= B2R v end)
    by (destruct v; try discriminate Fv; exact Hv).
  clear Hv.
  destruct (is_finite w) eqn:Fw.
  + pose proof (round_finite_pt _ _ _ _ Fw Hw) as P.
    destruct rnd; destruct P as (_ & _ & P);
      rewrite Bleb_correct by assumption; apply Rle_bool_true; apply P;
      first [exact Gv | exact Hv'].
  + (* an infinite [w] on the side [rnd] says that no float is there *)
    exfalso.
    destruct w as [s|s| |]; try discriminate Fw; destruct rnd; try destruct s;
      cbn [with_val mpfr_round] in Hw; try contradiction;
      specialize (Hw _ Gv); simpl in Hv'; lra.
- (* [v] is the infinity of the side [rnd], beyond every float *)
  destruct v as [s|s| |]; try discriminate Fv; cbn [on_side] in Hv; [|contradiction].
  subst s.
  destruct w as [s|s| |]; destruct rnd; try destruct s;
    cbn [with_val mpfr_round] in Hw; first [reflexivity | contradiction].
Qed.

(** ** Helpers *)

Ltac st_unfold :=
  cbn [side_tight p_acos p_acosh p_asin p_asinh p_atan p_atan2 p_atanh p_cos p_cosh p_exp
    p_exp10 p_exp2 p_ln p_log10 p_log2 p_pow p_pown p_sin p_sinh p_tan p_tanh].

Lemma st_B2R_zero : forall s, B2R (B754_zero s : f64) = 0.
Proof. reflexivity. Qed.

(** A tightened field is the rounding of [f] at the finite arguments in
    [D], and the field it tightens elsewhere. *)
Lemma st_tf_in :
  forall D dec f h rnd (x : f64), is_finite x = true -> D (B2R x) ->
  tight_field D dec f h rnd x = round_f64 rnd (f (B2R x)).
Proof.
intros D dec f h rnd x Fx Dx. unfold tight_field. rewrite Fx.
destruct (dec (B2R x)) as [_|N]; [reflexivity|exfalso; exact (N Dx)].
Qed.

Lemma st_tf_out :
  forall D dec f h rnd (x : f64), (is_finite x = true -> ~ D (B2R x)) ->
  tight_field D dec f h rnd x = h rnd x.
Proof.
intros D dec f h rnd x N. unfold tight_field.
destruct (is_finite x) eqn:Fx; [|reflexivity].
destruct (dec (B2R x)) as [Dx|_]; [exfalso; exact (N eq_refl Dx)|reflexivity].
Qed.

Lemma st_tf2_in :
  forall D dec f h rnd (x y : f64), is_finite x = true -> is_finite y = true ->
  D (B2R x) (B2R y) -> tight_field2 D dec f h rnd x y = round_f64 rnd (f (B2R x) (B2R y)).
Proof.
intros D dec f h rnd x y Fx Fy Dxy. unfold tight_field2. rewrite Fx, Fy. cbn [andb].
destruct (dec (B2R x) (B2R y)) as [_|N]; [reflexivity|exfalso; exact (N Dxy)].
Qed.

(** This one also rewrites a field at an infinite second argument, where
    [tight_field2] does not reduce: [is_finite x && false] is stuck. *)
Lemma st_tf2_out :
  forall D dec f h rnd (x y : f64),
  (is_finite x = true -> is_finite y = true -> ~ D (B2R x) (B2R y)) ->
  tight_field2 D dec f h rnd x y = h rnd x y.
Proof.
intros D dec f h rnd x y N. unfold tight_field2.
destruct (is_finite x) eqn:Fx, (is_finite y) eqn:Fy; cbn [andb]; try reflexivity.
destruct (dec (B2R x) (B2R y)) as [Dxy|_]; [exfalso; exact (N eq_refl eq_refl Dxy)|reflexivity].
Qed.

Lemma st_tfz_in :
  forall h rnd (x : f64) n, is_finite x = true -> is_i32 n -> pown_dom n (B2R x) ->
  tight_field_z h rnd x n = round_f64 rnd (powerRZ (B2R x) n).
Proof.
intros h rnd x n Fx I Dx. unfold tight_field_z. rewrite Fx.
destruct (dec_pown n (B2R x)) as [_|N]; [reflexivity|exfalso; exact (N (conj I Dx))].
Qed.

Lemma st_tfz_out :
  forall h rnd (x : f64) n, (is_finite x = true -> ~ (is_i32 n /\ pown_dom n (B2R x))) ->
  tight_field_z h rnd x n = h rnd x n.
Proof.
intros h rnd x n N. unfold tight_field_z.
destruct (is_finite x) eqn:Fx; [|reflexivity].
destruct (dec_pown n (B2R x)) as [Dx|_]; [exfalso; exact (N eq_refl Dx)|reflexivity].
Qed.

Lemma st_point_correct :
  forall (D D' : R -> Prop) dec f h, (forall r, D' r -> D r) ->
  point_correct D' f (tight_field D dec f h).
Proof.
intros D D' dec f h I rnd x Fx Dx.
rewrite (st_tf_in D dec f h rnd x Fx (I _ Dx)). apply round_f64_correct.
Qed.

Lemma st_point_correct2 :
  forall (D : R -> R -> Prop) dec f h, point_correct2 D f (tight_field2 D dec f h).
Proof.
intros D dec f h rnd x y Fx Fy Dxy.
rewrite (st_tf2_in D dec f h rnd x y Fx Fy Dxy). apply round_f64_correct.
Qed.

(** A field on the side [rnd] is outward of its tightened field. *)
Lemma st_out :
  forall (D D' : R -> Prop) dec f h, point_side D' f h ->
  (forall x : f64, is_finite x = true -> D (B2R x) -> D' (B2R x)) ->
  fld_out h (tight_field D dec f h).
Proof.
intros D D' dec f h S I rnd x. unfold tight_field.
destruct (is_finite x) eqn:Fx; [destruct (dec (B2R x)) as [Dx|_]|];
  [apply on_side_outward; exact (S rnd x Fx (I x Fx Dx)) | left; reflexivity
  | left; reflexivity].
Qed.

Lemma st_out2 :
  forall (D D' : R -> R -> Prop) dec f h, point_side2 D' f h ->
  (forall x y : f64, is_finite x = true -> is_finite y = true ->
   D (B2R x) (B2R y) -> D' (B2R x) (B2R y)) ->
  fld_out2 h (tight_field2 D dec f h).
Proof.
intros D D' dec f h S I rnd x y. unfold tight_field2.
destruct (is_finite x) eqn:Fx, (is_finite y) eqn:Fy; cbn [andb]; try (left; reflexivity).
destruct (dec (B2R x) (B2R y)) as [Dxy|_]; [|left; reflexivity].
apply on_side_outward. exact (S rnd x y Fx Fy (I x y Fx Fy Dxy)).
Qed.

Lemma st_out_z :
  forall h,
  (forall rnd (x : f64) n, is_i32 n -> is_finite x = true -> pown_dom n (B2R x) ->
   on_side rnd (powerRZ (B2R x) n) (h rnd x n)) ->
  fld_out_z h (tight_field_z h).
Proof.
intros h S rnd x n. unfold tight_field_z.
destruct (is_finite x) eqn:Fx; [destruct (dec_pown n (B2R x)) as [[I Dx]|_]|];
  [apply on_side_outward; exact (S rnd x n I Fx Dx) | left; reflexivity | left; reflexivity].
Qed.

(** A correct rounding is on its side ([rounds_side] of [DyDriver.v]). *)
Lemma st_round_side :
  forall rnd r v, mpfr_round f64_format rnd r (with_val v) -> on_side rnd r v.
Proof.
intros rnd r v H.
destruct v as [s|s| |s m e B]; cbn [on_side].
- destruct rnd; cbn [with_val mpfr_round] in H; destruct H as (_ & H & _); exact H.
- destruct rnd, s; cbn [with_val mpfr_round] in H |- *; first [reflexivity | contradiction].
- destruct rnd; cbn [with_val mpfr_round] in H; contradiction.
- destruct rnd; cbn [with_val mpfr_round] in H; destruct H as (_ & _ & H & _); exact H.
Qed.

Lemma st_c_s : forall D f h, point_correct D f h -> point_side D f h.
Proof. intros D f h P rnd x Fx Dx. exact (st_round_side _ _ _ (P rnd x Fx Dx)). Qed.

Lemma st_c_s2 : forall D f h, point_correct2 D f h -> point_side2 D f h.
Proof.
intros D f h P rnd x y Fx Fy Dxy. exact (st_round_side _ _ _ (P rnd x y Fx Fy Dxy)).
Qed.

(** A real rounded down to an [f64] is below 0 exactly when the real is,
    and a real rounded up is above 0 exactly when the real is: 0 is an
    [f64]. *)
Lemma st_dn_neg :
  forall r v, mpfr_round f64_format RNDD r (with_val v) ->
  (Model.lt v Model.zero = true <-> r < 0).
Proof.
intros r v H.
assert (F0 : f64_format 0) by exact (f64_format_B2R (B754_zero false) eq_refl).
destruct v as [s|[|]| |s m e B]; cbn [with_val mpfr_round] in H; try contradiction.
- destruct H as (_ & H & _).
  change (Model.lt (B754_zero s) Model.zero) with false.
  split; [discriminate | intros; lra].
- split; [intros _; exact (H 0 F0) | reflexivity].
- destruct H as (_ & _ & H1 & H2).
  unfold Model.lt. rewrite Bltb_correct by reflexivity.
  set (y := B2R (B754_finite s m e B)) in *. change (B2R Model.zero) with 0.
  destruct (Rlt_bool_spec y 0) as [L|L].
  + split; [intros _ | reflexivity].
    destruct (Rlt_or_le r 0) as [Hr|Hr]; [exact Hr|].
    specialize (H2 0 F0 Hr). lra.
  + split; [discriminate | intros; lra].
Qed.

Lemma st_up_pos :
  forall r v, mpfr_round f64_format RNDU r (with_val v) ->
  (Model.lt Model.zero v = true <-> 0 < r).
Proof.
intros r v H.
assert (F0 : f64_format 0) by exact (f64_format_B2R (B754_zero false) eq_refl).
destruct v as [s|[|]| |s m e B]; cbn [with_val mpfr_round] in H; try contradiction.
- destruct H as (_ & H & _).
  change (Model.lt Model.zero (B754_zero s)) with false.
  split; [discriminate | intros; lra].
- split; [intros _; exact (H 0 F0) | reflexivity].
- destruct H as (_ & _ & H1 & H2).
  unfold Model.lt. rewrite Bltb_correct by reflexivity.
  set (y := B2R (B754_finite s m e B)) in *. change (B2R Model.zero) with 0.
  destruct (Rlt_bool_spec 0 y) as [L|L].
  + split; [intros _ | reflexivity].
    destruct (Rlt_or_le 0 r) as [Hr|Hr]; [exact Hr|].
    specialize (H2 0 F0 Hr). lra.
  + split; [discriminate | intros; lra].
Qed.

Lemma st_bool_iff :
  forall (b c : bool) (P : Prop), (b = true <-> P) -> (c = true <-> P) -> b = c.
Proof.
intros [|] [|] P H1 H2; try reflexivity.
- symmetry. apply H2. apply H1. reflexivity.
- apply H1. apply H2. reflexivity.
Qed.

Ltac st_out_tac :=
  let p := fresh "p" in let H := fresh "H" in
  intros p H; st_unfold;
  first
  [ apply st_out_z; exact (proj1 H)
  | eapply st_out2; [first [exact H | exact (proj1 H)] | intros ? ? ? ? D; exact D]
  | eapply st_out; [first [exact H | exact (proj1 H)] | intros ? ? D; exact D] ].

(** ** The tightened record satisfies [Contract.v] *)

(** The special values: a field of [side_tight p] at an infinite argument,
    or at a finite one outside the domain, is [p]'s. *)
Ltac st_apply_hyp := match goal with R : _ |- _ => solve [apply R; assumption] end.

Ltac st_spec1 :=
  intros;
  rewrite st_tf_out by (let F := fresh in let D := fresh in intros F D;
    first [discriminate F | try unfold log_dom in D; try unfold atanh_dom in D;
      cbn [B2R] in D; lra]);
  st_apply_hyp.

Ltac st_spec2 :=
  intros;
  rewrite st_tf2_out by (let F1 := fresh in let F2 := fresh in let D := fresh in
    intros F1 F2 D; first [discriminate F1 | discriminate F2 | unfold pow_dom in D;
      cbn [B2R] in D; lra]);
  st_apply_hyp.

Ltac st_specz :=
  intros;
  rewrite st_tfz_out by (let F := fresh in let D := fresh in intros F D;
    first [discriminate F | destruct D as [_ [D|D]]; [lia | exact (D eq_refl)]]);
  st_apply_hyp.

Ltac st_c_tac :=
  let p := fresh "p" in let H := fresh "H" in
  intros p H; st_unfold;
  first
  [ apply st_point_correct; intros r Dr; first [exact Dr | exact I]
  | destruct H as [_ H]; split;
    [first [apply st_point_correct; intros r Dr; exact Dr | apply st_point_correct2] |];
    repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end;
    repeat match goal with |- _ /\ _ => split end;
    first [st_spec1 | st_spec2] ].

Lemma acos_tight_c : forall p, acos_s (p_acos p) -> acos_c (p_acos (side_tight p)).
Proof. st_c_tac. Qed.

Lemma acosh_tight_c : forall p, acosh_s (p_acosh p) -> acosh_c (p_acosh (side_tight p)).
Proof. st_c_tac. Qed.

Lemma asin_tight_c : forall p, asin_s (p_asin p) -> asin_c (p_asin (side_tight p)).
Proof. st_c_tac. Qed.

Lemma asinh_tight_c : forall p, asinh_s (p_asinh p) -> asinh_c (p_asinh (side_tight p)).
Proof. st_c_tac. Qed.

Lemma atan_tight_c : forall p, atan_s (p_atan p) -> atan_c (p_atan (side_tight p)).
Proof. st_c_tac. Qed.

Lemma atan2_tight_c : forall p, atan2_s (p_atan2 p) -> atan2_c (p_atan2 (side_tight p)).
Proof. st_c_tac. Qed.

Lemma atanh_tight_c : forall p, atanh_s (p_atanh p) -> atanh_c (p_atanh (side_tight p)).
Proof. st_c_tac. Qed.

Lemma cos_tight_c : forall p, cos_s (p_cos p) -> cos_c (p_cos (side_tight p)).
Proof. st_c_tac. Qed.

Lemma cosh_tight_c : forall p, cosh_s (p_cosh p) -> cosh_c (p_cosh (side_tight p)).
Proof. st_c_tac. Qed.

Lemma exp_tight_c : forall p, exp_s (p_exp p) -> exp_c (p_exp (side_tight p)).
Proof. st_c_tac. Qed.

Lemma exp10_tight_c : forall p, exp10_s (p_exp10 p) -> exp10_c (p_exp10 (side_tight p)).
Proof. st_c_tac. Qed.

Lemma exp2_tight_c : forall p, exp2_s (p_exp2 p) -> exp2_c (p_exp2 (side_tight p)).
Proof. st_c_tac. Qed.

Lemma ln_tight_c : forall p, ln_s (p_ln p) -> ln_c (p_ln (side_tight p)).
Proof. st_c_tac. Qed.

Lemma log10_tight_c : forall p, log10_s (p_log10 p) -> log10_c (p_log10 (side_tight p)).
Proof. st_c_tac. Qed.

Lemma log2_tight_c : forall p, log2_s (p_log2 p) -> log2_c (p_log2 (side_tight p)).
Proof. st_c_tac. Qed.

Lemma pow_tight_c : forall p, pow_s (p_pow p) -> pow_c (p_pow (side_tight p)).
Proof. st_c_tac. Qed.

Lemma pown_tight_c : forall p, pown_s (p_pown p) -> pown_c (p_pown (side_tight p)).
Proof.
intros p (_ & H). st_unfold. split.
- intros rnd x n I Fx D. rewrite (st_tfz_in _ rnd x n Fx I D). apply round_f64_correct.
- repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; st_specz.
Qed.

Lemma sin_tight_c : forall p, sin_s (p_sin p) -> sin_c (p_sin (side_tight p)).
Proof. st_c_tac. Qed.

Lemma sinh_tight_c : forall p, sinh_s (p_sinh p) -> sinh_c (p_sinh (side_tight p)).
Proof. st_c_tac. Qed.

Lemma tan_tight_c : forall p, tan_s (p_tan p) -> tan_c (p_tan (side_tight p)).
Proof. st_c_tac. Qed.

Lemma tanh_tight_c : forall p, tanh_s (p_tanh p) -> tanh_c (p_tanh (side_tight p)).
Proof. st_c_tac. Qed.

(** ** [p]'s fields are outward of the tightened ones *)

Lemma acos_tight_out : forall p, acos_s (p_acos p) -> fld_out (p_acos p) (p_acos (side_tight p)).
Proof. st_out_tac. Qed.

Lemma acosh_tight_out :
  forall p, acosh_s (p_acosh p) -> fld_out (p_acosh p) (p_acosh (side_tight p)).
Proof. st_out_tac. Qed.

Lemma asin_tight_out : forall p, asin_s (p_asin p) -> fld_out (p_asin p) (p_asin (side_tight p)).
Proof. st_out_tac. Qed.

Lemma asinh_tight_out :
  forall p, asinh_s (p_asinh p) -> fld_out (p_asinh p) (p_asinh (side_tight p)).
Proof. st_out_tac. Qed.

Lemma atan_tight_out : forall p, atan_s (p_atan p) -> fld_out (p_atan p) (p_atan (side_tight p)).
Proof. st_out_tac. Qed.

Lemma atan2_tight_out :
  forall p, atan2_s (p_atan2 p) -> fld_out2 (p_atan2 p) (p_atan2 (side_tight p)).
Proof. st_out_tac. Qed.

Lemma atanh_tight_out :
  forall p, atanh_s (p_atanh p) -> fld_out (p_atanh p) (p_atanh (side_tight p)).
Proof. st_out_tac. Qed.

Lemma cos_tight_out : forall p, cos_s (p_cos p) -> fld_out (p_cos p) (p_cos (side_tight p)).
Proof. st_out_tac. Qed.

Lemma cosh_tight_out : forall p, cosh_s (p_cosh p) -> fld_out (p_cosh p) (p_cosh (side_tight p)).
Proof. st_out_tac. Qed.

Lemma exp_tight_out : forall p, exp_s (p_exp p) -> fld_out (p_exp p) (p_exp (side_tight p)).
Proof. st_out_tac. Qed.

Lemma exp10_tight_out :
  forall p, exp10_s (p_exp10 p) -> fld_out (p_exp10 p) (p_exp10 (side_tight p)).
Proof. st_out_tac. Qed.

Lemma exp2_tight_out : forall p, exp2_s (p_exp2 p) -> fld_out (p_exp2 p) (p_exp2 (side_tight p)).
Proof. st_out_tac. Qed.

Lemma ln_tight_out : forall p, ln_s (p_ln p) -> fld_out (p_ln p) (p_ln (side_tight p)).
Proof. st_out_tac. Qed.

Lemma log10_tight_out :
  forall p, log10_s (p_log10 p) -> fld_out (p_log10 p) (p_log10 (side_tight p)).
Proof. st_out_tac. Qed.

Lemma log2_tight_out : forall p, log2_s (p_log2 p) -> fld_out (p_log2 p) (p_log2 (side_tight p)).
Proof. st_out_tac. Qed.

Lemma pow_tight_out : forall p, pow_s (p_pow p) -> fld_out2 (p_pow p) (p_pow (side_tight p)).
Proof. st_out_tac. Qed.

Lemma pown_tight_out : forall p, pown_s (p_pown p) -> fld_out_z (p_pown p) (p_pown (side_tight p)).
Proof. st_out_tac. Qed.

Lemma sin_tight_out : forall p, sin_s (p_sin p) -> fld_out (p_sin p) (p_sin (side_tight p)).
Proof. st_out_tac. Qed.

Lemma sinh_tight_out : forall p, sinh_s (p_sinh p) -> fld_out (p_sinh p) (p_sinh (side_tight p)).
Proof. st_out_tac. Qed.

Lemma tan_tight_out : forall p, tan_s (p_tan p) -> fld_out (p_tan p) (p_tan (side_tight p)).
Proof.
intros p H. st_unfold.
eapply st_out; [exact H | intros x Fx _; exact (TrigPieces.tan_dom_f64 x Fx)].
Qed.

Lemma tanh_tight_out : forall p, tanh_s (p_tanh p) -> fld_out (p_tanh p) (p_tanh (side_tight p)).
Proof. st_out_tac. Qed.

(** ** The same quadrant *)

Lemma quadrant_tight :
  forall p, sin_s (p_sin p) -> cos_s (p_cos p) ->
  forall z, quadrant p z = quadrant (side_tight p) z.
Proof.
intros p [_ Hs] [_ Hc] z. unfold quadrant. cbv zeta. unfold sin_rd, cos_ru. st_unfold.
destruct (is_finite z) eqn:Fz.
- rewrite (st_tf_in real_dom dec_real sin (p_sin p) RNDD z Fz I),
    (st_tf_in real_dom dec_real cos (p_cos p) RNDU z Fz I).
  rewrite (st_bool_iff _ _ _ (Hs z Fz) (st_dn_neg _ _ (round_f64_correct RNDD (sin (B2R z))))),
    (st_bool_iff _ _ _ (Hc z Fz) (st_up_pos _ _ (round_f64_correct RNDU (cos (B2R z))))).
  reflexivity.
- unfold tight_field. rewrite Fz. reflexivity.
Qed.

(** ** [ContractSide.v] asks no more than [Contract.v] *)

Ltac st_c_s_tac :=
  let h := fresh "h" in let H := fresh "H" in let P := fresh "P" in let R := fresh "R" in
  intros h H;
  first
  [ exact (st_c_s _ _ _ H)
  | destruct H as [P R]; split;
    [first [exact (st_c_s _ _ _ P) | exact (st_c_s2 _ _ _ P)] | exact R] ].

Lemma acos_c_s : forall h, acos_c h -> acos_s h.
Proof. st_c_s_tac. Qed.

Lemma acosh_c_s : forall h, acosh_c h -> acosh_s h.
Proof. st_c_s_tac. Qed.

Lemma asin_c_s : forall h, asin_c h -> asin_s h.
Proof. st_c_s_tac. Qed.

Lemma asinh_c_s : forall h, asinh_c h -> asinh_s h.
Proof. st_c_s_tac. Qed.

Lemma atan_c_s : forall h, atan_c h -> atan_s h.
Proof. st_c_s_tac. Qed.

Lemma atan2_c_s : forall h, atan2_c h -> atan2_s h.
Proof. st_c_s_tac. Qed.

Lemma atanh_c_s : forall h, atanh_c h -> atanh_s h.
Proof. st_c_s_tac. Qed.

Lemma cos_c_s : forall h, cos_c h -> cos_s h.
Proof.
intros h H. split; [exact (st_c_s _ _ _ H) |].
intros x Fx. exact (st_up_pos _ _ (H RNDU x Fx I)).
Qed.

Lemma cosh_c_s : forall h, cosh_c h -> cosh_s h.
Proof. st_c_s_tac. Qed.

Lemma exp_c_s : forall h, exp_c h -> exp_s h.
Proof. st_c_s_tac. Qed.

Lemma exp10_c_s : forall h, exp10_c h -> exp10_s h.
Proof. st_c_s_tac. Qed.

Lemma exp2_c_s : forall h, exp2_c h -> exp2_s h.
Proof. st_c_s_tac. Qed.

Lemma ln_c_s : forall h, ln_c h -> ln_s h.
Proof. st_c_s_tac. Qed.

Lemma log10_c_s : forall h, log10_c h -> log10_s h.
Proof. st_c_s_tac. Qed.

Lemma log2_c_s : forall h, log2_c h -> log2_s h.
Proof. st_c_s_tac. Qed.

Lemma pow_c_s : forall h, pow_c h -> pow_s h.
Proof. st_c_s_tac. Qed.

Lemma pown_c_s : forall h, pown_c h -> pown_s h.
Proof.
intros h [P R]. split; [|exact R].
intros rnd x n I Fx D. exact (st_round_side _ _ _ (P rnd x n I Fx D)).
Qed.

Lemma sin_c_s : forall h, sin_c h -> sin_s h.
Proof.
intros h H. split; [exact (st_c_s _ _ _ H) |].
intros x Fx. exact (st_dn_neg _ _ (H RNDD x Fx I)).
Qed.

Lemma sinh_c_s : forall h, sinh_c h -> sinh_s h.
Proof. st_c_s_tac. Qed.

Lemma tan_c_s : forall h, tan_c h -> tan_s h.
Proof. st_c_s_tac. Qed.

Lemma tanh_c_s : forall h, tanh_c h -> tanh_s h.
Proof. st_c_s_tac. Qed.
