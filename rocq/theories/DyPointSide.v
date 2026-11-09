(** * The dyadic kernel's functions with the cap of Ziv's strategy, as a record [point]

    [DyPoint.v] covers the calls of the kernel's functions at which a
    rule settles the result or a rounding test of Ziv's strategy passes.
    [kernel_point_rust] is the record of the functions as the Rust
    computes them, with [Dyadic.ziv] and its cap of 4,096 bits
    ([exp_dir] and the others of [Model.v]), where they return, and the
    result rounded by definition ([round_f64] of [MpfrIdeal.v]) where
    they do not, that is where the Rust panics. Its fields are on the
    correct side ([exp_dir_side] and the others) and take the special
    values of [Contract.v] ([k_exp_rust_s] and the others), and the
    fields of [sin] and [cos] have the signs that [quadrant] reads
    ([sin_dir_sign], [cos_dir_sign] of [DyTrigPos.v]). So the theorems of
    [SideTheorems.v] apply: the elementary functions of [Model.v] with
    the kernel's fields return intervals that contain the image of their
    argument at every argument ([kernel_exp_encloses] and the others).
    For the Rust, that is at every argument at which no call of the
    kernel panics, including those at which no rounding test passes by
    the cap. The intervals need not be the tightest there. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Elementary Mpfr MpfrRound MpfrIdeal IdealGetD Elem Cosh
  Atanh Contract OfPointCore OfPoint OfPointElem PointTheorems DyDriver DyExp DyHyp DyLog DyLogHyp
  DyAtan DyAsin DyTrig DyPowRules DyPown DyPow DyPoint ContractSide SideDefs SideTheorems DyTrigPos
  TrigBranch.

Open Scope R_scope.

Definition kernel_point_rust : point := {|
  p_acos := kernel_field DyadicAtan.acos_dir acos;
  p_acosh := kernel_field DyadicLog.acosh_dir Racosh;
  p_asin := kernel_field DyadicAtan.asin_dir asin;
  p_asinh := kernel_field DyadicLog.asinh_dir arcsinh;
  p_atan := kernel_field DyadicAtan.atan_dir atan;
  p_atan2 := kernel_field2 DyadicAtan.atan2_dir Ratan2;
  p_atanh := kernel_field DyadicLog.atanh_dir Ratanh;
  p_cos := kernel_field DyadicTrig.cos_dir cos;
  p_cosh := kernel_field DyadicExp.cosh_dir cosh;
  p_exp := kernel_field DyadicExp.exp_dir exp;
  p_exp10 := kernel_field DyadicExp.exp10_dir Rexp10;
  p_exp2 := kernel_field DyadicExp.exp2_dir Rexp2;
  p_ln := kernel_field DyadicLog.ln_dir ln;
  p_log10 := kernel_field DyadicLog.log10_dir Rlog10;
  p_log2 := kernel_field DyadicLog.log2_dir Rlog2;
  p_pow := kernel_field2 DyadicPow.pow_dir Rpow;
  p_pown := kernel_field_z DyadicPow.pown_dir powerRZ;
  p_sin := kernel_field DyadicTrig.sin_dir sin;
  p_sinh := kernel_field DyadicExp.sinh_dir sinh;
  p_tan := kernel_field DyadicTrig.tan_dir tan;
  p_tanh := kernel_field DyadicExp.tanh_dir tanh
|}.

(** ** The fields on the correct side

    Where the Rust driver returns, its theorem ([exp_dir_side] and the
    others) puts the result on the side [up_of rnd]; where it does not,
    [round_f64] rounds in the direction [rnd], which is on that side too. *)

(** [f64_side] of [DyDriver.v] in the direction [up_of rnd] is [on_side]
    of [rnd]. *)
Lemma f64_side_on_side : forall rnd r v, f64_side (up_of rnd) r v -> on_side rnd r v.
Proof. intros rnd r v H. destruct rnd, v as [s|s| |s m e B]; exact H. Qed.

(** A rounding in the direction [rnd] is on the side [rnd]. *)
Lemma round_on_side :
  forall rnd r v, mpfr_round f64_format rnd r (with_val v) -> on_side rnd r v.
Proof.
intros rnd r v H. apply f64_side_on_side, rounds_side. unfold rounds. destruct rnd; exact H.
Qed.

Lemma kernel_field_side :
  forall (D : R -> Prop) (dir : f64 -> bool -> option f64) (f : R -> R),
  (forall x up v, is_finite x = true -> D (B2R x) -> dir x up = Some v ->
   f64_side up (f (B2R x)) v) ->
  point_side D f (kernel_field dir f).
Proof.
intros D dir f Hd rnd x Fx Dx. unfold kernel_field.
destruct (dir x (up_of rnd)) as [v|] eqn:E.
- exact (f64_side_on_side rnd _ v (Hd x (up_of rnd) v Fx Dx E)).
- apply round_on_side, round_f64_correct.
Qed.

Lemma kernel_field2_side :
  forall (D : R -> R -> Prop) (dir : f64 -> f64 -> bool -> option f64) (f : R -> R -> R),
  (forall y x up v, is_finite y = true -> is_finite x = true -> D (B2R y) (B2R x) ->
   dir y x up = Some v -> f64_side up (f (B2R y) (B2R x)) v) ->
  point_side2 D f (kernel_field2 dir f).
Proof.
intros D dir f Hd rnd y x Fy Fx Dyx. unfold kernel_field2.
destruct (dir y x (up_of rnd)) as [v|] eqn:E.
- exact (f64_side_on_side rnd _ v (Hd y x (up_of rnd) v Fy Fx Dyx E)).
- apply round_on_side, round_f64_correct.
Qed.

Lemma kernel_field_z_side :
  forall (D : Z -> R -> Prop) (dir : f64 -> Z -> bool -> option f64) (f : R -> Z -> R),
  (forall x n up v, is_i32 n -> is_finite x = true -> D n (B2R x) -> dir x n up = Some v ->
   f64_side up (f (B2R x) n) v) ->
  forall rnd x n, is_i32 n -> is_finite x = true -> D n (B2R x) ->
  on_side rnd (f (B2R x) n) (kernel_field_z dir f rnd x n).
Proof.
intros D dir f Hd rnd x n Hn Fx Dx. unfold kernel_field_z.
destruct (dir x n (up_of rnd)) as [v|] eqn:E.
- exact (f64_side_on_side rnd _ v (Hd x n (up_of rnd) v Hn Fx Dx E)).
- apply round_on_side, round_f64_correct.
Qed.

(** A real of at least -1 rounded down is below 0 exactly when the real
    is: a negative real rounds down to a value below it, and a real of at
    least 0 rounds down to at least 0, as 0 is a float. The rounding is
    finite, as -1 is a float. [qd_sin_neg] of [TrigQuad.v] says the same
    of [sin]. *)
Lemma round_dn_neg :
  forall r (w : f64), -1 <= r -> mpfr_round f64_format RNDD r (with_val w) ->
  (Model.lt w Model.zero = true <-> r < 0).
Proof.
intros r w Hr H.
assert (Fw : is_finite w = true) by exact (tb_rd_finite _ _ H Hr).
destruct (round_finite_pt _ _ _ _ Fw H) as (_ & Hle & Hmax).
assert (F0 : f64_format 0) by (exists Model.zero; split; reflexivity).
unfold Model.lt. rewrite Bltb_correct by first [exact Fw | reflexivity].
change (B2R Model.zero) with 0.
case Rlt_bool_spec; intros Hw; split; intros E; try reflexivity; try discriminate E.
- destruct (Rlt_or_le r 0) as [Hn | Hn]; [exact Hn |].
  specialize (Hmax 0 F0 Hn). lra.
- lra.
Qed.

(** A real of at most 1 rounded up is above 0 exactly when the real is,
    in the same way. *)
Lemma round_up_pos :
  forall r (w : f64), r <= 1 -> mpfr_round f64_format RNDU r (with_val w) ->
  (Model.lt Model.zero w = true <-> 0 < r).
Proof.
intros r w Hr H.
assert (Fw : is_finite w = true) by exact (tb_ru_finite _ _ H Hr).
destruct (round_finite_pt _ _ _ _ Fw H) as (_ & Hge & Hmin).
assert (F0 : f64_format 0) by (exists Model.zero; split; reflexivity).
unfold Model.lt. rewrite Bltb_correct by first [exact Fw | reflexivity].
change (B2R Model.zero) with 0.
case Rlt_bool_spec; intros Hw; split; intros E; try reflexivity; try discriminate E.
- destruct (Rlt_or_le 0 r) as [Hp | Hp]; [exact Hp |].
  specialize (Hmin 0 F0 Hp). lra.
- lra.
Qed.

(** ** The fields satisfy [ContractSide.v]

    The special values: where [exp_dir_with ziv_strict] and the others
    return, the Rust drivers return the same ([exp_dir_strict] and the
    others), so the values that [DyPoint.v] computes for [k_exp_c] and
    the others carry over. *)

Theorem k_exp_rust_s : exp_s (p_exp kernel_point_rust).
Proof.
cbn [p_exp kernel_point_rust].
split; [exact (kernel_field_side _ _ _ (fun x up v Fx _ E => exp_dir_side x up v Fx E)) | split].
- exists false. unfold kernel_field. cbn [up_of].
  rewrite (exp_dir_strict (B754_infinity true) false (B754_zero false))
    by (vm_compute; reflexivity).
  reflexivity.
- unfold kernel_field. cbn [up_of].
  rewrite (exp_dir_strict (B754_infinity false) true (B754_infinity false))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Theorem k_exp2_rust_s : exp2_s (p_exp2 kernel_point_rust).
Proof.
cbn [p_exp2 kernel_point_rust].
split; [exact (kernel_field_side _ _ _ (fun x up v Fx _ E => exp2_dir_side x up v Fx E)) | split].
- exists false. unfold kernel_field. cbn [up_of].
  rewrite (exp2_dir_strict (B754_infinity true) false (B754_zero false))
    by (vm_compute; reflexivity).
  reflexivity.
- unfold kernel_field. cbn [up_of].
  rewrite (exp2_dir_strict (B754_infinity false) true (B754_infinity false))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Theorem k_exp10_rust_s : exp10_s (p_exp10 kernel_point_rust).
Proof.
cbn [p_exp10 kernel_point_rust].
split;
  [exact (kernel_field_side _ _ _ (fun x up v Fx _ E => exp10_dir_side x up v Fx E)) | split].
- exists false. unfold kernel_field. cbn [up_of].
  rewrite (exp10_dir_strict (B754_infinity true) false (B754_zero false))
    by (vm_compute; reflexivity).
  reflexivity.
- unfold kernel_field. cbn [up_of].
  rewrite (exp10_dir_strict (B754_infinity false) true (B754_infinity false))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Theorem k_sinh_rust_s : sinh_s (p_sinh kernel_point_rust).
Proof.
cbn [p_sinh kernel_point_rust].
split; [exact (kernel_field_side _ _ _ (fun x up v Fx _ E => sinh_dir_side x up v Fx E)) | split].
- unfold kernel_field. cbn [up_of].
  rewrite (sinh_dir_strict (B754_infinity true) false (B754_infinity true))
    by (vm_compute; reflexivity).
  reflexivity.
- unfold kernel_field. cbn [up_of].
  rewrite (sinh_dir_strict (B754_infinity false) true (B754_infinity false))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Theorem k_cosh_rust_s : cosh_s (p_cosh kernel_point_rust).
Proof.
cbn [p_cosh kernel_point_rust].
split; [exact (kernel_field_side _ _ _ (fun x up v Fx _ E => cosh_dir_side x up v Fx E)) |].
intros s. unfold kernel_field. cbn [up_of].
rewrite (cosh_dir_strict (B754_infinity s) true (B754_infinity false))
  by (destruct s; vm_compute; reflexivity).
reflexivity.
Qed.

Theorem k_tanh_rust_s : tanh_s (p_tanh kernel_point_rust).
Proof.
cbn [p_tanh kernel_point_rust].
split; [exact (kernel_field_side _ _ _ (fun x up v Fx _ E => tanh_dir_side x up v Fx E)) | split].
- unfold kernel_field. cbn [up_of].
  rewrite (tanh_dir_strict (B754_infinity true) false DyadicExp.m_one)
    by (vm_compute; reflexivity).
  apply m_one_round.
- unfold kernel_field. cbn [up_of].
  rewrite (tanh_dir_strict (B754_infinity false) true DyadicExp.one)
    by (vm_compute; reflexivity).
  apply one_round.
Qed.

Theorem k_ln_rust_s : ln_s (p_ln kernel_point_rust).
Proof.
cbn [p_ln kernel_point_rust].
split; [exact (kernel_field_side _ _ _ ln_dir_side) | split].
- intros s. unfold kernel_field. cbn [up_of].
  rewrite (ln_dir_strict (B754_zero s) false (B754_infinity true))
    by (destruct s; vm_compute; reflexivity).
  reflexivity.
- unfold kernel_field. cbn [up_of].
  rewrite (ln_dir_strict (B754_infinity false) true (B754_infinity false))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Theorem k_log2_rust_s : log2_s (p_log2 kernel_point_rust).
Proof.
cbn [p_log2 kernel_point_rust].
split; [exact (kernel_field_side _ _ _ log2_dir_side) | split].
- intros s. unfold kernel_field. cbn [up_of].
  rewrite (log2_dir_strict (B754_zero s) false (B754_infinity true))
    by (destruct s; vm_compute; reflexivity).
  reflexivity.
- unfold kernel_field. cbn [up_of].
  rewrite (log2_dir_strict (B754_infinity false) true (B754_infinity false))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Theorem k_log10_rust_s : log10_s (p_log10 kernel_point_rust).
Proof.
cbn [p_log10 kernel_point_rust].
split; [exact (kernel_field_side _ _ _ log10_dir_side) | split].
- intros s. unfold kernel_field. cbn [up_of].
  rewrite (log10_dir_strict (B754_zero s) false (B754_infinity true))
    by (destruct s; vm_compute; reflexivity).
  reflexivity.
- unfold kernel_field. cbn [up_of].
  rewrite (log10_dir_strict (B754_infinity false) true (B754_infinity false))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Theorem k_asinh_rust_s : asinh_s (p_asinh kernel_point_rust).
Proof.
cbn [p_asinh kernel_point_rust].
split;
  [exact (kernel_field_side _ _ _ (fun x up v Fx _ E => asinh_dir_side x up v Fx E)) | split].
- unfold kernel_field. cbn [up_of].
  rewrite (asinh_dir_strict (B754_infinity true) false (B754_infinity true))
    by (vm_compute; reflexivity).
  reflexivity.
- unfold kernel_field. cbn [up_of].
  rewrite (asinh_dir_strict (B754_infinity false) true (B754_infinity false))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Theorem k_acosh_rust_s : acosh_s (p_acosh kernel_point_rust).
Proof.
cbn [p_acosh kernel_point_rust].
split; [exact (kernel_field_side _ _ _ acosh_dir_side) |].
unfold kernel_field. cbn [up_of].
rewrite (acosh_dir_strict (B754_infinity false) true (B754_infinity false))
  by (vm_compute; reflexivity).
reflexivity.
Qed.

Theorem k_atanh_rust_s : atanh_s (p_atanh kernel_point_rust).
Proof.
cbn [p_atanh kernel_point_rust].
split; [exact (kernel_field_side _ _ _ atanh_dir_side) | split].
- intros x Fx Hx.
  rewrite (f64_of_value x DyadicExp.m_one (-1) Fx ltac:(vm_compute; reflexivity)
    DyHypRules.hyp_lit_m_one ltac:(lra) Hx).
  unfold kernel_field. cbn [up_of].
  rewrite (atanh_dir_strict DyadicExp.m_one false (B754_infinity true))
    by (vm_compute; reflexivity).
  reflexivity.
- intros x Fx Hx.
  rewrite (f64_of_value x DyadicExp.one 1 Fx ltac:(vm_compute; reflexivity)
    (proj2 one_B2R) ltac:(lra) Hx).
  unfold kernel_field. cbn [up_of].
  rewrite (atanh_dir_strict DyadicExp.one true (B754_infinity false))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Theorem k_atan_rust_s : atan_s (p_atan kernel_point_rust).
Proof.
cbn [p_atan kernel_point_rust].
split; [exact (kernel_field_side _ _ _ (fun x up v Fx _ E => atan_dir_side x up v Fx E)) | split].
- destruct (atan_dir_infinity true false) as (v & E & R).
  unfold kernel_field. cbn [up_of]. rewrite (atan_dir_strict _ _ _ E). exact R.
- destruct (atan_dir_infinity false true) as (v & E & R).
  unfold kernel_field. cbn [up_of]. rewrite (atan_dir_strict _ _ _ E). exact R.
Qed.

Theorem k_asin_rust_s : asin_s (p_asin kernel_point_rust).
Proof. exact (kernel_field_side _ _ _ asin_dir_side). Qed.

Theorem k_acos_rust_s : acos_s (p_acos kernel_point_rust).
Proof. exact (kernel_field_side _ _ _ acos_dir_side). Qed.

Theorem k_atan2_rust_s : atan2_s (p_atan2 kernel_point_rust).
Proof.
cbn [p_atan2 kernel_point_rust].
split; [exact (kernel_field2_side _ _ _ atan2_dir_side) |].
unfold kernel_field2.
split; [| split; [| split; [| split; [| split; [| split]]]]].
- intros rnd y Fy _. destruct (atan2_dir_inf_pos y (up_of rnd) Fy) as [s' E].
  rewrite (atan2_dir_strict _ _ _ _ E). exists s'. reflexivity.
- intros rnd y Fy _. destruct (atan2_dir_inf_pos y (up_of rnd) Fy) as [s' E].
  rewrite (atan2_dir_strict _ _ _ _ E). exists s'. reflexivity.
- intros rnd s. destruct (atan2_dir_inf_pos (B754_zero s) (up_of rnd) eq_refl) as [s' E].
  rewrite (atan2_dir_strict _ _ _ _ E). exists s'. reflexivity.
- intros rnd y Fy Hy. destruct (atan2_dir_inf_neg_pos y (up_of rnd) Fy Hy) as (v & E & R).
  rewrite (atan2_dir_strict _ _ _ _ E). destruct rnd; exact R.
- intros rnd y Fy Hy. destruct (atan2_dir_inf_neg_neg y (up_of rnd) Fy Hy) as (v & E & R).
  rewrite (atan2_dir_strict _ _ _ _ E). destruct rnd; exact R.
- intros rnd x Fx. destruct (atan2_dir_y_inf false x (up_of rnd) Fx) as (v & E & R).
  rewrite (atan2_dir_strict _ _ _ _ E). destruct rnd; exact R.
- intros rnd x Fx. destruct (atan2_dir_y_inf true x (up_of rnd) Fx) as (v & E & R).
  rewrite (atan2_dir_strict _ _ _ _ E). destruct rnd; exact R.
Qed.

(** The Rust [pow_dir] and [pown_dir] return the same [f64] in both
    directions where [ziv_strict]'s do, as at the constant clauses of
    [pow_s] and [pown_s]. *)
Lemma rust_pow_const :
  forall x y v rnd,
  DyadicPow.pow_dir_with ziv_strict x y false = Some v ->
  DyadicPow.pow_dir_with ziv_strict x y true = Some v ->
  kernel_field2 DyadicPow.pow_dir Rpow rnd x y = v.
Proof.
intros x y v rnd Ed Eu. unfold kernel_field2.
destruct rnd; cbn [up_of];
  first [rewrite (pow_dir_strict _ _ _ _ Ed) | rewrite (pow_dir_strict _ _ _ _ Eu)]; reflexivity.
Qed.

Lemma rust_pown_const :
  forall x n v rnd,
  DyadicPow.pown_dir_with ziv_strict x n false = Some v ->
  DyadicPow.pown_dir_with ziv_strict x n true = Some v ->
  kernel_field_z DyadicPow.pown_dir powerRZ rnd x n = v.
Proof.
intros x n v rnd Ed Eu. unfold kernel_field_z.
destruct rnd; cbn [up_of];
  first [rewrite (pown_dir_strict _ _ _ _ Ed) | rewrite (pown_dir_strict _ _ _ _ Eu)];
  reflexivity.
Qed.

Theorem k_pow_rust_s : pow_s (p_pow kernel_point_rust).
Proof.
cbn [p_pow kernel_point_rust].
split; [exact (kernel_field2_side _ _ _ pow_dir_side) |].
split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split;
  [| split; [| split; [| split]]]]]]]]]]]].
- intros rnd y Fy Hy. unfold kernel_field2.
  rewrite (pow_dir_strict _ _ _ _ (pow_dir_zero_neg y (up_of rnd) Fy Hy)). reflexivity.
- intros rnd. apply rust_pow_const; vm_compute; reflexivity.
- intros rnd. exists false. apply rust_pow_const; vm_compute; reflexivity.
- intros rnd s.
  replace (kernel_field2 DyadicPow.pow_dir Rpow rnd (B754_zero false) (B754_zero s))
    with DyadicExp.one; [apply one_round |].
  symmetry. apply rust_pow_const; destruct s; vm_compute; reflexivity.
- intros rnd s.
  replace (kernel_field2 DyadicPow.pow_dir Rpow rnd (B754_infinity false) (B754_zero s))
    with DyadicExp.one; [apply one_round |].
  symmetry. apply rust_pow_const; destruct s; vm_compute; reflexivity.
- intros rnd x s Fx Hx.
  replace (kernel_field2 DyadicPow.pow_dir Rpow rnd x (B754_infinity s))
    with DyadicExp.one; [apply one_round |].
  unfold kernel_field2.
  rewrite (pow_dir_strict _ _ _ _ (pow_dir_one_inf x s (up_of rnd) Fx Hx)). reflexivity.
- intros rnd x Fx Hx. unfold kernel_field2.
  rewrite (pow_dir_strict _ _ _ _ (pow_dir_lt1_inf x true (up_of rnd) Fx Hx)). reflexivity.
- intros rnd x Fx Hx. exists false. unfold kernel_field2.
  rewrite (pow_dir_strict _ _ _ _ (pow_dir_gt1_inf x true (up_of rnd) Fx Hx)). reflexivity.
- intros rnd x Fx Hx. exists false. unfold kernel_field2.
  rewrite (pow_dir_strict _ _ _ _ (pow_dir_lt1_inf x false (up_of rnd) Fx Hx)). reflexivity.
- intros rnd x Fx Hx. unfold kernel_field2.
  rewrite (pow_dir_strict _ _ _ _ (pow_dir_gt1_inf x false (up_of rnd) Fx Hx)). reflexivity.
- intros rnd y Fy Hy. exists false. unfold kernel_field2.
  rewrite (pow_dir_strict _ _ _ _ (pow_dir_inf_neg y (up_of rnd) Fy Hy)). reflexivity.
- intros rnd. exists false. apply rust_pow_const; vm_compute; reflexivity.
- intros rnd y Fy Hy. unfold kernel_field2.
  rewrite (pow_dir_strict _ _ _ _ (pow_dir_inf_pos y (up_of rnd) Fy Hy)). reflexivity.
- intros rnd. apply rust_pow_const; vm_compute; reflexivity.
Qed.

Theorem k_pown_rust_s : pown_s (p_pown kernel_point_rust).
Proof.
cbn [p_pown kernel_point_rust].
split; [exact (kernel_field_z_side _ _ _ pown_dir_side) |].
split; [| split; [| split; [| split; [| split; [| split]]]]].
- intros rnd s n _ Hn He. unfold kernel_field_z.
  rewrite (pown_dir_strict _ _ _ _ (pown_dir_zero_neg ziv_strict s n (up_of rnd) Hn)),
    <- Z.negb_even, He, Bool.andb_false_r.
  reflexivity.
- intros rnd s n _ Hn Ho. unfold kernel_field_z.
  rewrite (pown_dir_strict _ _ _ _ (pown_dir_zero_neg ziv_strict s n (up_of rnd) Hn)), Ho,
    Bool.andb_true_r.
  reflexivity.
- intros rnd n _ Hn. unfold kernel_field_z.
  rewrite (pown_dir_strict _ _ _ _ (pown_dir_inf ziv_strict false n (up_of rnd) ltac:(lia))).
  replace (n <? 0)%Z with true by (symmetry; apply Z.ltb_lt; exact Hn).
  eexists; reflexivity.
- intros rnd.
  replace (kernel_field_z DyadicPow.pown_dir powerRZ rnd (B754_infinity false) 0%Z)
    with DyadicExp.one; [apply one_round |].
  symmetry. apply rust_pown_const; vm_compute; reflexivity.
- intros rnd n _ Hn. unfold kernel_field_z.
  rewrite (pown_dir_strict _ _ _ _ (pown_dir_inf ziv_strict false n (up_of rnd) ltac:(lia))).
  replace (n <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
- intros rnd n _ Hn Ho. unfold kernel_field_z.
  rewrite (pown_dir_strict _ _ _ _ (pown_dir_inf ziv_strict true n (up_of rnd) ltac:(lia))).
  replace (n <? 0)%Z with true by (symmetry; apply Z.ltb_lt; exact Hn).
  eexists; reflexivity.
- intros rnd n _ Hn Ho. unfold kernel_field_z.
  rewrite (pown_dir_strict _ _ _ _ (pown_dir_inf ziv_strict true n (up_of rnd) ltac:(lia))).
  replace (n <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia). rewrite Ho. reflexivity.
Qed.

(** The sign that [quadrant] reads: where [sin_dir] returns, by
    [sin_dir_sign]; where it does not, the field is [sin] rounded down,
    and [sin >= -1]. The same for [cos] rounded up. *)
Theorem k_sin_rust_s : sin_s (p_sin kernel_point_rust).
Proof.
cbn [p_sin kernel_point_rust].
split; [exact (kernel_field_side _ _ _ (fun x up v Fx _ E => sin_dir_side x up v Fx E)) |].
intros x Fx. unfold kernel_field. cbn [up_of].
destruct (DyadicTrig.sin_dir x false) as [v|] eqn:E.
- exact (sin_dir_sign x v Fx E).
- exact (round_dn_neg _ _ (proj1 (SIN_bound _)) (round_f64_correct RNDD _)).
Qed.

Theorem k_cos_rust_s : cos_s (p_cos kernel_point_rust).
Proof.
cbn [p_cos kernel_point_rust].
split; [exact (kernel_field_side _ _ _ (fun x up v Fx _ E => cos_dir_side x up v Fx E)) |].
intros x Fx. unfold kernel_field. cbn [up_of].
destruct (DyadicTrig.cos_dir x true) as [v|] eqn:E.
- exact (cos_dir_sign x v Fx E).
- exact (round_up_pos _ _ (proj2 (COS_bound _)) (round_f64_correct RNDU _)).
Qed.

(** [tan_dir_side] holds at every finite argument, so the domain of [tan]
    is not used. *)
Theorem k_tan_rust_s : tan_s (p_tan kernel_point_rust).
Proof. exact (kernel_field_side _ _ _ (fun x up v Fx _ E => tan_dir_side x up v Fx E)). Qed.

(** ** The elementary functions contain the image *)

Theorem kernel_exp_encloses :
  forall x, valid x -> encloses (image_dom real_dom exp x) (Interval.exp kernel_point_rust x).
Proof.
  exact (exp_encloses_side kernel_point_rust k_exp_rust_s).
Qed.

Theorem kernel_exp2_encloses :
  forall x, valid x -> encloses (image_dom real_dom Rexp2 x) (Interval.exp2 kernel_point_rust x).
Proof.
  exact (exp2_encloses_side kernel_point_rust k_exp2_rust_s).
Qed.

Theorem kernel_exp10_encloses :
  forall x, valid x -> encloses (image_dom real_dom Rexp10 x) (Interval.exp10 kernel_point_rust x).
Proof.
  exact (exp10_encloses_side kernel_point_rust k_exp10_rust_s).
Qed.

Theorem kernel_sinh_encloses :
  forall x, valid x -> encloses (image_dom real_dom sinh x) (Interval.sinh kernel_point_rust x).
Proof.
  exact (sinh_encloses_side kernel_point_rust k_sinh_rust_s).
Qed.

Theorem kernel_tanh_encloses :
  forall x, valid x -> encloses (image_dom real_dom tanh x) (Interval.tanh kernel_point_rust x).
Proof.
  exact (tanh_encloses_side kernel_point_rust k_tanh_rust_s).
Qed.

Theorem kernel_ln_encloses :
  forall x, valid x -> encloses (image_dom log_dom ln x) (Interval.ln kernel_point_rust x).
Proof.
  exact (ln_encloses_side kernel_point_rust k_ln_rust_s).
Qed.

Theorem kernel_log2_encloses :
  forall x, valid x -> encloses (image_dom log_dom Rlog2 x) (Interval.log2 kernel_point_rust x).
Proof.
  exact (log2_encloses_side kernel_point_rust k_log2_rust_s).
Qed.

Theorem kernel_log10_encloses :
  forall x, valid x -> encloses (image_dom log_dom Rlog10 x) (Interval.log10 kernel_point_rust x).
Proof.
  exact (log10_encloses_side kernel_point_rust k_log10_rust_s).
Qed.

Theorem kernel_asinh_encloses :
  forall x, valid x -> encloses (image_dom real_dom arcsinh x) (Interval.asinh kernel_point_rust x).
Proof.
  exact (asinh_encloses_side kernel_point_rust k_asinh_rust_s).
Qed.

Theorem kernel_acosh_encloses :
  forall x, valid x -> encloses (image_dom acosh_dom Racosh x) (Interval.acosh kernel_point_rust x).
Proof.
  exact (acosh_encloses_side kernel_point_rust k_acosh_rust_s).
Qed.

Theorem kernel_atanh_encloses :
  forall x, valid x -> encloses (image_dom atanh_dom Ratanh x) (Interval.atanh kernel_point_rust x).
Proof.
  exact (atanh_encloses_side kernel_point_rust k_atanh_rust_s).
Qed.

Theorem kernel_atan_encloses :
  forall x, valid x -> encloses (image_dom real_dom atan x) (Interval.atan kernel_point_rust x).
Proof.
  exact (atan_encloses_side kernel_point_rust k_atan_rust_s).
Qed.

Theorem kernel_asin_encloses :
  forall x, valid x -> encloses (image_dom asin_dom asin x) (Interval.asin kernel_point_rust x).
Proof.
  exact (asin_encloses_side kernel_point_rust k_asin_rust_s).
Qed.

Theorem kernel_acos_encloses :
  forall x, valid x -> encloses (image_dom acos_dom acos x) (Interval.acos kernel_point_rust x).
Proof.
  exact (acos_encloses_side kernel_point_rust k_acos_rust_s).
Qed.

Theorem kernel_cosh_encloses :
  forall first x, valid x ->
  encloses (image_dom real_dom cosh x) (Interval.cosh kernel_point_rust first x).
Proof.
  exact (cosh_encloses_side kernel_point_rust k_cosh_rust_s).
Qed.

Theorem kernel_atan2_encloses :
  forall y x, valid y -> valid x ->
  exists z, Interval.atan2 kernel_point_rust y x = Some z /\
    encloses (image2_set atan2_dom Ratan2 y x) z.
Proof.
  exact (atan2_encloses_side kernel_point_rust k_atan2_rust_s).
Qed.

Theorem kernel_sin_encloses :
  forall has_fma first x, valid x ->
  exists y, Interval.sin kernel_point_rust has_fma first x = Some y /\
    encloses (image_dom real_dom sin x) y.
Proof.
  exact (sin_encloses_side kernel_point_rust k_sin_rust_s k_cos_rust_s).
Qed.

Theorem kernel_cos_encloses :
  forall has_fma first x, valid x ->
  exists y, Interval.cos kernel_point_rust has_fma first x = Some y /\
    encloses (image_dom real_dom cos x) y.
Proof.
  exact (cos_encloses_side kernel_point_rust k_cos_rust_s k_sin_rust_s).
Qed.

Theorem kernel_tan_encloses :
  forall has_fma x, valid x ->
  exists y, Interval.tan kernel_point_rust has_fma x = Some y /\
    encloses (image_dom tan_dom tan x) y.
Proof.
  exact (tan_encloses_side kernel_point_rust k_tan_rust_s k_sin_rust_s k_cos_rust_s).
Qed.

Theorem kernel_pow_encloses :
  forall first_min first_max x y, valid x -> valid y ->
  encloses (image2_set pow_dom Rpow x y) (Interval.pow kernel_point_rust first_min first_max x y).
Proof.
  exact (pow_encloses_side kernel_point_rust k_pow_rust_s).
Qed.

Theorem kernel_pown_encloses :
  forall n x, is_i32 n -> valid x ->
  exists y, Interval.powi kernel_point_rust n x = Some y /\
    encloses (image_dom (pown_dom n) (fun r => powerRZ r n) x) y.
Proof.
  exact (pown_encloses_side kernel_point_rust k_pown_rust_s).
Qed.
