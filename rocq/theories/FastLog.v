(** * The fast paths of [ln], [log2] and [log10]

    [fast_ln_correct] ([FastLogLn.v]), [fast_log2_correct] and
    [fast_log10_correct] ([FastLogBy.v]) show that [DyadicLog.fast_ln]
    and [DyadicLog.fast_log_by] of [Model.v] return [h + l] within
    [2^-68] of the result scaled by [2^-k], with [1/2 < |h| < 2], so that
    [Fast.round_dir_signed] and [Fast.round_near_signed] of [FastSign.v]
    apply. The result is never 0 except at [x = 1], where
    [DyadicLog.normalize] returns [None] ([fast_ln_one],
    [fast_log2_one]). The theorems [fast_ln_dir_correct] and the others
    prove the fast paths of the three functions in all three roundings,
    and [fast_ln_dir_fma] and the others that an FMA gives the same
    results. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Elementary Encoding TwoSum TwoProduct DyDriver NearF64
  FastRound FastSign FastLogTables FastLogCore FastLogNorm FastLogByProd FastLogLn FastLogBy.

Open Scope R_scope.

(** ** [fast_log_by] with an FMA *)

(** A finite [f64] of value 0 is a zero (as in [FastLogPoly.v]). *)
Local Lemma zero_of_B2R : forall x : f64, is_finite x = true -> B2R x = 0 -> exists s, x = B754_zero s.
Proof.
intros [s|s| |s m e Hb] F H; try discriminate F.
- exists s. reflexivity.
- exfalso. cbn [B2R] in H. apply eq_0_F2R in H. destruct s; simpl in H; discriminate H.
Qed.

(** [B2R l] of an [f64] literal [l], as [m * 2^e], in a hypothesis [H]
    (as [lit_hyp] of [FastExp.v]). *)
Local Ltac lit_hyp l H :=
  let s := eval vm_compute in (B2SF l) in
  assert (H : B2R l = SF2R radix2 s)
    by (rewrite <- (SF2R_B2SF _ _ l); replace (B2SF l) with s by (vm_compute; reflexivity);
        reflexivity);
  cbn [SF2R SpecFloat.cond_Zopp] in H; unfold F2R in H; cbn [Fnum Fexp] in H;
  rewrite ?opp_IZR in H.

(** The only difference an FMA makes in [fast_log_by] is the error term
    of [ph = a_h c_h]. Where [a_h <> 0], it is the same [f64]
    ([by_prod_fma]); where [a_h] is a zero, the hypothesis on the zeros,
    which the two lemmas below check for each constant by computation,
    gives it. *)
Local Lemma by_fma :
  forall x c d, is_finite x = true -> 0 < B2R x ->
  is_finite (from_bits (fst c)) = true -> / 4 <= B2R (from_bits (fst c)) <= 2 ->
  (forall s,
     Generic.two_prod_err true (B754_zero s) (from_bits (fst c))
       (mul (B754_zero s) (from_bits (fst c))) =
     Generic.two_prod_err false (B754_zero s) (from_bits (fst c))
       (mul (B754_zero s) (from_bits (fst c)))) ->
  DyadicLog.fast_log_by true x c d = DyadicLog.fast_log_by false x c d.
Proof.
intros x c d Fx Hx Fch Hch Hz.
pose proof (ln_core_correct false x Fx Hx) as Hc.
pose proof (core_cases false x Fx Hx) as Hk.
unfold DyadicLog.fast_log_by. rewrite (ln_core_fma x Fx Hx).
revert Hc Hk. destruct (DyadicLog.ln_core false x) as [[e ah] al]. cbv beta iota zeta.
intros (Fah & _) (Hah & Hk).
destruct Hk as [(_ & Z0 & _) | (_ & Hlo)].
- destruct (zero_of_B2R ah Fah Z0) as [s ->]. rewrite (Hz s). reflexivity.
- rewrite (by_prod_fma ah (from_bits (fst c)) Fah Fch Hlo Hah Hch). reflexivity.
Qed.

(** [fast_log_by] with an FMA, for [log2] and [log10]. *)
Lemma fast_log2_by_fma :
  forall x, is_finite x = true -> 0 < B2R x ->
  DyadicLog.fast_log_by true x DyadicLog.C2 DyadicLog.ONE =
  DyadicLog.fast_log_by false x DyadicLog.C2 DyadicLog.ONE.
Proof.
intros x Fx Hx. apply (by_fma x _ _ Fx Hx).
- vm_compute. reflexivity.
- lit_hyp (from_bits (fst DyadicLog.C2)) H. rewrite H. cbn [bpow radix_val radix2]. lra.
- intros [|]; vm_compute; reflexivity.
Qed.

Lemma fast_log10_by_fma :
  forall x, is_finite x = true -> 0 < B2R x ->
  DyadicLog.fast_log_by true x DyadicLog.C10 DyadicLog.LG2 =
  DyadicLog.fast_log_by false x DyadicLog.C10 DyadicLog.LG2.
Proof.
intros x Fx Hx. apply (by_fma x _ _ Fx Hx).
- vm_compute. reflexivity.
- lit_hyp (from_bits (fst DyadicLog.C10)) H. rewrite H. cbn [bpow radix_val radix2]. lra.
- intros [|]; vm_compute; reflexivity.
Qed.

(** ** The fast paths in the three roundings *)

(** [r 2^-k 2^k = r]. *)
Local Lemma unscale : forall r k, r * bpow radix2 (- k) * bpow radix2 k = r.
Proof.
intros r k. rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l. cbn [bpow]. ring.
Qed.

Theorem fast_ln_dir_correct :
  forall fma x up v,
  is_finite x = true -> 0 < B2R x -> DyadicLog.fast_ln_dir fma x up = Some v ->
  rounds up (ln (B2R x)) v.
Proof.
intros fma x up v Fx Hx H. unfold DyadicLog.fast_ln_dir in H.
destruct (DyadicLog.fast_ln fma x) as [[[h l] k]|] eqn:E; [|discriminate H].
destruct (fast_ln_correct fma x h l k Fx Hx E) as (Fh & Fl & Hrn & Hh & Hk & Hy).
pose proof (round_dir_signed_correct h l k up v _ Fh Fl Hrn Hh Hk Hy H) as R.
rewrite unscale in R. exact R.
Qed.

Theorem fast_log2_dir_correct :
  forall fma x up v,
  is_finite x = true -> 0 < B2R x -> DyadicLog.fast_log2_dir fma x up = Some v ->
  rounds up (Rlog2 (B2R x)) v.
Proof.
intros fma x up v Fx Hx H. unfold DyadicLog.fast_log2_dir in H.
destruct (DyadicLog.fast_log_by fma x DyadicLog.C2 DyadicLog.ONE) as [[[h l] k]|] eqn:E;
  [|discriminate H].
destruct (fast_log2_correct fma x h l k Fx Hx E) as (Fh & Fl & Hrn & Hh & Hk & Hy).
pose proof (round_dir_signed_correct h l k up v _ Fh Fl Hrn Hh Hk Hy H) as R.
rewrite unscale in R. exact R.
Qed.

Theorem fast_log10_dir_correct :
  forall fma x up v,
  is_finite x = true -> 0 < B2R x -> DyadicLog.fast_log10_dir fma x up = Some v ->
  rounds up (Rlog10 (B2R x)) v.
Proof.
intros fma x up v Fx Hx H. unfold DyadicLog.fast_log10_dir in H.
destruct (DyadicLog.fast_log_by fma x DyadicLog.C10 DyadicLog.LG2) as [[[h l] k]|] eqn:E;
  [|discriminate H].
destruct (fast_log10_correct fma x h l k Fx Hx E) as (Fh & Fl & Hrn & Hh & Hk & Hy).
pose proof (round_dir_signed_correct h l k up v _ Fh Fl Hrn Hh Hk Hy H) as R.
rewrite unscale in R. exact R.
Qed.

Theorem fast_ln_near_correct :
  forall fma x v,
  is_finite x = true -> 0 < B2R x -> DyadicLog.fast_ln_near fma x = Some v ->
  near_round (ln (B2R x)) v.
Proof.
intros fma x v Fx Hx H. unfold DyadicLog.fast_ln_near in H.
destruct (DyadicLog.fast_ln fma x) as [[[h l] k]|] eqn:E; [|discriminate H].
destruct (fast_ln_correct fma x h l k Fx Hx E) as (Fh & Fl & Hrn & Hh & Hk & Hy).
pose proof (round_near_signed_correct h l k v _ Fh Fl Hrn Hh Hk Hy H) as R.
rewrite unscale in R. exact R.
Qed.

Theorem fast_log2_near_correct :
  forall fma x v,
  is_finite x = true -> 0 < B2R x -> DyadicLog.fast_log2_near fma x = Some v ->
  near_round (Rlog2 (B2R x)) v.
Proof.
intros fma x v Fx Hx H. unfold DyadicLog.fast_log2_near in H.
destruct (DyadicLog.fast_log_by fma x DyadicLog.C2 DyadicLog.ONE) as [[[h l] k]|] eqn:E;
  [|discriminate H].
destruct (fast_log2_correct fma x h l k Fx Hx E) as (Fh & Fl & Hrn & Hh & Hk & Hy).
pose proof (round_near_signed_correct h l k v _ Fh Fl Hrn Hh Hk Hy H) as R.
rewrite unscale in R. exact R.
Qed.

Theorem fast_log10_near_correct :
  forall fma x v,
  is_finite x = true -> 0 < B2R x -> DyadicLog.fast_log10_near fma x = Some v ->
  near_round (Rlog10 (B2R x)) v.
Proof.
intros fma x v Fx Hx H. unfold DyadicLog.fast_log10_near in H.
destruct (DyadicLog.fast_log_by fma x DyadicLog.C10 DyadicLog.LG2) as [[[h l] k]|] eqn:E;
  [|discriminate H].
destruct (fast_log10_correct fma x h l k Fx Hx E) as (Fh & Fl & Hrn & Hh & Hk & Hy).
pose proof (round_near_signed_correct h l k v _ Fh Fl Hrn Hh Hk Hy H) as R.
rewrite unscale in R. exact R.
Qed.

(** ** With an FMA, and at 1 *)

Theorem fast_ln_dir_fma :
  forall x up, is_finite x = true -> 0 < B2R x ->
  DyadicLog.fast_ln_dir true x up = DyadicLog.fast_ln_dir false x up.
Proof.
intros x up Fx Hx. unfold DyadicLog.fast_ln_dir, DyadicLog.fast_ln.
rewrite (ln_core_fma x Fx Hx). reflexivity.
Qed.

Theorem fast_log2_dir_fma :
  forall x up, is_finite x = true -> 0 < B2R x ->
  DyadicLog.fast_log2_dir true x up = DyadicLog.fast_log2_dir false x up.
Proof.
intros x up Fx Hx. unfold DyadicLog.fast_log2_dir. rewrite (fast_log2_by_fma x Fx Hx).
reflexivity.
Qed.

Theorem fast_log10_dir_fma :
  forall x up, is_finite x = true -> 0 < B2R x ->
  DyadicLog.fast_log10_dir true x up = DyadicLog.fast_log10_dir false x up.
Proof.
intros x up Fx Hx. unfold DyadicLog.fast_log10_dir. rewrite (fast_log10_by_fma x Fx Hx).
reflexivity.
Qed.

Theorem fast_ln_near_fma :
  forall x, is_finite x = true -> 0 < B2R x ->
  DyadicLog.fast_ln_near true x = DyadicLog.fast_ln_near false x.
Proof.
intros x Fx Hx. unfold DyadicLog.fast_ln_near, DyadicLog.fast_ln.
rewrite (ln_core_fma x Fx Hx). reflexivity.
Qed.

Theorem fast_log2_near_fma :
  forall x, is_finite x = true -> 0 < B2R x ->
  DyadicLog.fast_log2_near true x = DyadicLog.fast_log2_near false x.
Proof.
intros x Fx Hx. unfold DyadicLog.fast_log2_near. rewrite (fast_log2_by_fma x Fx Hx).
reflexivity.
Qed.

Theorem fast_log10_near_fma :
  forall x, is_finite x = true -> 0 < B2R x ->
  DyadicLog.fast_log10_near true x = DyadicLog.fast_log10_near false x.
Proof.
intros x Fx Hx. unfold DyadicLog.fast_log10_near. rewrite (fast_log10_by_fma x Fx Hx).
reflexivity.
Qed.

(** At [x = 1], [ln x = log2 x = 0], and the directed fast paths return
    [None], so that the kernel's exact enclosure settles them. *)
Theorem fast_ln_one :
  forall fma up, DyadicLog.fast_ln_dir fma DyadicExp.one up = None.
Proof.
intros [|] [|]; vm_compute; reflexivity.
Qed.

Theorem fast_log2_one :
  forall fma up, DyadicLog.fast_log2_dir fma DyadicExp.one up = None.
Proof.
intros [|] [|]; vm_compute; reflexivity.
Qed.
