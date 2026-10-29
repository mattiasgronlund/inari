(** * [x / y] and [recip x] of intervals that give [EMPTY], [[0, 0]] or
    [ENTIRE], and [contains(0.0)]

    [x / y] of [Interval]s dispatches on the pair of the classes of its
    arguments ([classify2_pair] in [Classify2.v]):
    - The 19 pairs with [E] on either side or [Z] on the right return
      [EMPTY] ([div_empty]). A real of a [y] in [Z] is 0, which is outside
      the domain of the divisor, so the image is empty.
    - The 5 pairs with [Z] on the left and [M], [N0], [N1], [P0] or [P1] on
      the right return [[0, 0]] ([div_zero]): such a [y] has a real other
      than 0, and [0 / t = 0].
    - The 7 pairs [M × M], [M × N0], [M × P0] and [N0], [N1], [P0], [P1]
      [× M] return [ENTIRE] ([div_entire]). Either [x] has reals of both
      signs and [y] has reals [t <> 0] as close to 0 as asked on one side
      of 0, or [x] has a real [r <> 0] and [y] such reals on both sides. So
      the quotients have no upper and no lower bound, and [ENTIRE] is the
      tightest interval that contains them ([tightest_entire]).
    [recip x] returns [EMPTY] for [E] and [Z], and [ENTIRE] for [M], for
    the same reasons ([recip_empty] and [recip_entire]).

    [DecInterval::recip] and [DecInterval::div] test whether the argument
    or the divisor contains 0 with [Interval::contains(0.0)], which holds
    exactly when 0 is a real of the interval ([contains_zero]). *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer Sign MaxMin DecBinary AddSub
  Classes Classify2 MulZero DivTight DivSets.

Open Scope R_scope.

(** ** [ENTIRE] *)

(** [ENTIRE] is [[+inf; +inf]], whose lanes bound no real. *)
Lemma mem_entire : forall r, mem r Interval.ENTIRE.
Proof.
intros r. split; reflexivity.
Qed.

(** A set with no upper and no lower bound has the tightest interval
    [ENTIRE]. *)
Lemma tightest_entire :
  forall S, (forall m, exists s, S s /\ m <= s) -> (forall m, exists s, S s /\ s <= m) ->
  is_tightest S Interval.ENTIRE.
Proof.
intros S Hup Hlo. split; [|split].
- (* [Bleb -inf +inf] computes to [true], and the bounds are not +inf
     and -inf. *)
  right. split; [reflexivity | split; discriminate].
- intros r _. apply mem_entire.
- (* Every real [r] is between two elements of [S], which [z] contains. *)
  intros z Hz Hs r _.
  destruct (Hup r) as (v & Hv & Hrv). destruct (Hlo r) as (u & Hu & Hur).
  exact (mem_between z u v r Hz (Hs u Hu) (Hs v Hv) (conj Hur Hrv)).
Qed.

(** ** Reals near 0 *)

(** A real [r > 0] divided by a real [t > 0] close enough to 0 exceeds any
    real [m]: [t <= r / (|m| + 1)] gives [r / t >= |m| + 1 > m]. *)
Lemma quot_large :
  forall r m, 0 < r -> exists eps, 0 < eps /\ forall t, 0 < t -> t <= eps -> m <= r / t.
Proof.
intros r m Hr. pose proof (Rabs_pos m) as Hm. pose proof (Rle_abs m) as Hm'.
exists (r / (Rabs m + 1)). split; [apply Rdiv_lt_0_compat; lra|].
intros t Ht Hte.
assert (E1 : r / (Rabs m + 1) * (Rabs m + 1) = r) by (field; lra).
assert (E2 : r / t * t = r) by (field; lra).
assert (H1 : t * (Rabs m + 1) <= r / (Rabs m + 1) * (Rabs m + 1))
  by (apply Rmult_le_compat_r; lra).
(* [(|m| + 1) * t <= r = (r / t) * t], and [t > 0]. *)
assert (H2 : Rabs m + 1 <= r / t).
{ apply (Rmult_le_reg_r t); [exact Ht|]. rewrite E2. lra. }
lra.
Qed.

(** A set [T] with elements above 0 as close to 0 as asked has an element
    [t > 0] with [m <= r / t]. *)
Lemma quot_near0 :
  forall (T : R -> Prop) r m, 0 < r ->
  (forall eps, 0 < eps -> exists t, T t /\ 0 < t /\ t <= eps) ->
  exists t, T t /\ 0 < t /\ m <= r / t.
Proof.
intros T r m Hr HT. destruct (quot_large r m Hr) as (eps & Heps & Hq).
destruct (HT eps Heps) as (t & Ht & Ht0 & Hte).
exists t. split; [exact Ht|]. split; [exact Ht0 | exact (Hq t Ht0 Hte)].
Qed.

(** An interval with 0 and a real above 0 has reals above 0 as close to 0
    as asked, as it holds the reals between them. *)
Lemma near0_pos :
  forall y t1, valid y -> mem 0 y -> mem t1 y -> 0 < t1 ->
  forall eps, 0 < eps -> exists t, mem t y /\ 0 < t /\ t <= eps.
Proof.
intros y t1 Hy H0 H1 Ht1 eps Heps. destruct (Rle_or_lt eps t1) as [He|He].
- exists eps. split; [|split; lra].
  apply (mem_between y 0 t1 eps Hy H0 H1). split; lra.
- exists t1. split; [exact H1 | split; lra].
Qed.

(** The same below 0, with the negated reals. *)
Lemma near0_neg :
  forall y t0, valid y -> mem 0 y -> mem t0 y -> t0 < 0 ->
  forall eps, 0 < eps -> exists t, mem (- t) y /\ 0 < t /\ t <= eps.
Proof.
intros y t0 Hy H0 H1 Ht0 eps Heps. destruct (Rle_or_lt eps (- t0)) as [He|He].
- exists eps. split; [|split; lra].
  apply (mem_between y t0 0 (- eps) Hy H1 H0). split; lra.
- exists (- t0). rewrite Ropp_involutive. split; [exact H1 | split; lra].
Qed.

(** [M] has reals as close to 0 as asked on both sides, as it holds a real
    below 0, one above 0, and so 0. *)
Lemma near_M :
  forall y, valid y -> Interval.classify y = Some CM ->
  (forall eps, 0 < eps -> exists t, mem t y /\ 0 < t /\ t <= eps) /\
  (forall eps, 0 < eps -> exists t, mem (- t) y /\ 0 < t /\ t <= eps).
Proof.
intros y Hy Hc.
destruct (classify_mem y CM Hy Hc) as [(t0 & Ht0 & Ht0n) (t1 & Ht1 & Ht1p)].
assert (H0 : mem 0 y) by (apply (mem_between y t0 t1 0 Hy Ht0 Ht1); split; lra).
split; [exact (near0_pos y t1 Hy H0 Ht1 Ht1p) | exact (near0_neg y t0 Hy H0 Ht0 Ht0n)].
Qed.

(** [P0] has them above 0, and [N0] below 0. *)
Lemma near_P0 :
  forall y, valid y -> Interval.classify y = Some CP0 ->
  forall eps, 0 < eps -> exists t, mem t y /\ 0 < t /\ t <= eps.
Proof.
intros y Hy Hc. destruct (classify_mem y CP0 Hy Hc) as (_ & H0 & t1 & Ht1 & Ht1p).
exact (near0_pos y t1 Hy H0 Ht1 Ht1p).
Qed.

Lemma near_N0 :
  forall y, valid y -> Interval.classify y = Some CN0 ->
  forall eps, 0 < eps -> exists t, mem (- t) y /\ 0 < t /\ t <= eps.
Proof.
intros y Hy Hc. destruct (classify_mem y CN0 Hy Hc) as (_ & H0 & t0 & Ht0 & Ht0n).
exact (near0_neg y t0 Hy H0 Ht0 Ht0n).
Qed.

(** A valid interval whose class is neither [E] nor [Z] holds a real other
    than 0. *)
Lemma classify_nonzero :
  forall y c, valid y -> Interval.classify y = Some c -> c <> CE -> c <> CZ ->
  exists t, mem t y /\ t <> 0.
Proof.
intros y c Hy Hc HE HZ. pose proof (classify_mem y c Hy Hc) as M.
destruct c.
- exfalso. apply HE. reflexivity.
- destruct M as [(t & Ht & Ht0) _]. exists t. split; [exact Ht | lra].
- destruct M as (_ & _ & t & Ht & Ht0). exists t. split; [exact Ht | lra].
- destruct M as [Hneg (t & Ht)]. exists t. split; [exact Ht|].
  pose proof (Hneg t Ht). lra.
- destruct M as (_ & _ & t & Ht & Ht0). exists t. split; [exact Ht | lra].
- destruct M as [Hpos (t & Ht)]. exists t. split; [exact Ht|].
  pose proof (Hpos t Ht). lra.
- exfalso. apply HZ. reflexivity.
Qed.

(** ** Unbounded quotients

    [r / t] for a real [r] of [x] and reals [t] of [y] near 0: it has no
    upper bound if [r] and [t] have the same sign, and no lower bound if
    they have opposite signs. *)

Lemma div_up_pp :
  forall x y r, mem r x -> 0 < r ->
  (forall eps, 0 < eps -> exists t, mem t y /\ 0 < t /\ t <= eps) ->
  forall m, exists s, image2_dom div_dom1 div_dom2 Rdiv x y s /\ m <= s.
Proof.
intros x y r Hr Hr0 NP m.
destruct (quot_near0 (fun t => mem t y) r m Hr0 NP) as (t & Ht & Ht0 & Hm).
exists (r / t). split; [|exact Hm].
exists r, t. split; [exact Hr|]. split; [exact Ht|]. split; [exact I|].
split; [exact (Rgt_not_eq t 0 Ht0) | reflexivity].
Qed.

Lemma div_up_nn :
  forall x y r, mem r x -> r < 0 ->
  (forall eps, 0 < eps -> exists t, mem (- t) y /\ 0 < t /\ t <= eps) ->
  forall m, exists s, image2_dom div_dom1 div_dom2 Rdiv x y s /\ m <= s.
Proof.
intros x y r Hr Hr0 NN m. assert (Hr1 : 0 < - r) by lra.
destruct (quot_near0 (fun t => mem (- t) y) (- r) m Hr1 NN) as (t & Ht & Ht0 & Hm).
(* [r / (-t) = (-r) / t]. *)
assert (E : r / (- t) = (- r) / t) by (field; lra).
exists (r / (- t)). split; [|lra].
exists r, (- t). split; [exact Hr|]. split; [exact Ht|]. split; [exact I|].
split; [exact (Rlt_not_eq (- t) 0 ltac:(lra)) | reflexivity].
Qed.

Lemma div_down_pn :
  forall x y r, mem r x -> 0 < r ->
  (forall eps, 0 < eps -> exists t, mem (- t) y /\ 0 < t /\ t <= eps) ->
  forall m, exists s, image2_dom div_dom1 div_dom2 Rdiv x y s /\ s <= m.
Proof.
intros x y r Hr Hr0 NN m.
destruct (quot_near0 (fun t => mem (- t) y) r (- m) Hr0 NN) as (t & Ht & Ht0 & Hm).
(* [r / (-t) = - (r / t)]. *)
assert (E : r / (- t) = - (r / t)) by (field; lra).
exists (r / (- t)). split; [|lra].
exists r, (- t). split; [exact Hr|]. split; [exact Ht|]. split; [exact I|].
split; [exact (Rlt_not_eq (- t) 0 ltac:(lra)) | reflexivity].
Qed.

Lemma div_down_np :
  forall x y r, mem r x -> r < 0 ->
  (forall eps, 0 < eps -> exists t, mem t y /\ 0 < t /\ t <= eps) ->
  forall m, exists s, image2_dom div_dom1 div_dom2 Rdiv x y s /\ s <= m.
Proof.
intros x y r Hr Hr0 NP m. assert (Hr1 : 0 < - r) by lra.
destruct (quot_near0 (fun t => mem t y) (- r) (- m) Hr1 NP) as (t & Ht & Ht0 & Hm).
(* [(-r) / t = - (r / t)]. *)
assert (E : (- r) / t = - (r / t)) by (field; lra).
exists (r / t). split; [|lra].
exists r, t. split; [exact Hr|]. split; [exact Ht|]. split; [exact I|].
split; [exact (Rgt_not_eq t 0 Ht0) | reflexivity].
Qed.

(** ** [x / y] *)

Lemma div_empty :
  forall has_fma x y cx cy, valid x -> valid y ->
  Interval.classify x = Some cx -> Interval.classify y = Some cy ->
  cx = CE \/ cy = CE \/ cy = CZ ->
  exists z, Interval.div has_fma x y = Some z /\
    is_tightest (image2_dom div_dom1 div_dom2 Rdiv x y) z.
Proof.
intros has_fma x y cx cy Hx Hy Ecx Ecy Hc. exists Interval.EMPTY. split.
- (* Every pair with [E] on either side or [Z] on the right returns
     [EMPTY]. *)
  unfold Interval.div. rewrite (classify2_pair x y cx cy Ecx Ecy).
  destruct Hc as [-> | [-> | ->]]; [destruct cy | destruct cx | destruct cx];
    reflexivity.
- apply tightest_empty. intros u (r & t & Hr & Ht & _ & Ht0 & _).
  unfold div_dom2 in Ht0.
  destruct Hc as [-> | [-> | ->]].
  + exact (classify_mem x CE Hx Ecx r Hr).
  + exact (classify_mem y CE Hy Ecy t Ht).
  + (* The only real of [y] is 0, outside the domain. *)
    apply (classify_mem y CZ Hy Ecy) in Ht. exact (Ht0 Ht).
Qed.

Lemma div_zero :
  forall has_fma x y cy, valid x -> valid y ->
  Interval.classify x = Some CZ -> Interval.classify y = Some cy ->
  cy <> CE -> cy <> CZ ->
  exists z, Interval.div has_fma x y = Some z /\
    is_tightest (image2_dom div_dom1 div_dom2 Rdiv x y) z.
Proof.
intros has_fma x y cy Hx Hy Ecx Ecy HE HZ. exists Interval.zero. split.
- unfold Interval.div. rewrite (classify2_pair x y CZ cy Ecx Ecy).
  destruct cy;
    solve [reflexivity | exfalso; apply HE; reflexivity | exfalso; apply HZ; reflexivity].
- apply (is_tightest_ext (fun s => s = 0)); [|exact zero_tightest].
  (* The image is [{0}]: the numerator is 0, and [y] has a real other
     than 0. *)
  pose proof (classify_mem x CZ Hx Ecx) as Mx.
  destruct (classify_nonzero y cy Hy Ecy HE HZ) as (t & Ht & Ht0).
  intros s. split.
  + intros ->. exists 0, t. split; [apply Mx; reflexivity|]. split; [exact Ht|].
    split; [exact I|]. split; [exact Ht0|]. unfold Rdiv. ring.
  + intros (r & t' & Hr & _ & _ & _ & ->). apply Mx in Hr. subst r.
    unfold Rdiv. ring.
Qed.

Lemma div_entire :
  forall has_fma x y cx cy, valid x -> valid y ->
  Interval.classify x = Some cx -> Interval.classify y = Some cy ->
  (cx = CM /\ (cy = CM \/ cy = CN0 \/ cy = CP0)) \/
  (cy = CM /\ cx <> CE /\ cx <> CZ) ->
  exists z, Interval.div has_fma x y = Some z /\
    is_tightest (image2_dom div_dom1 div_dom2 Rdiv x y) z.
Proof.
intros has_fma x y cx cy Hx Hy Ecx Ecy Hc. exists Interval.ENTIRE. split.
- unfold Interval.div. rewrite (classify2_pair x y cx cy Ecx Ecy).
  destruct Hc as [[-> [-> | [-> | ->]]] | (-> & H1 & H2)]; [| | | destruct cx];
    solve [reflexivity | exfalso; apply H1; reflexivity | exfalso; apply H2; reflexivity].
- destruct Hc as [[-> Hcy] | (-> & H1 & H2)].
  + (* [x] has reals of both signs, and [y] reals near 0 on one side. *)
    destruct (classify_mem x CM Hx Ecx) as [(rn & Hrn & Hrn0) (rp & Hrp & Hrp0)].
    destruct Hcy as [-> | [-> | ->]].
    * destruct (near_M y Hy Ecy) as [NP _]. apply tightest_entire;
        [exact (div_up_pp x y rp Hrp Hrp0 NP) | exact (div_down_np x y rn Hrn Hrn0 NP)].
    * pose proof (near_N0 y Hy Ecy) as NN. apply tightest_entire;
        [exact (div_up_nn x y rn Hrn Hrn0 NN) | exact (div_down_pn x y rp Hrp Hrp0 NN)].
    * pose proof (near_P0 y Hy Ecy) as NP. apply tightest_entire;
        [exact (div_up_pp x y rp Hrp Hrp0 NP) | exact (div_down_np x y rn Hrn Hrn0 NP)].
  + (* [x] has a real [r <> 0], and [y] reals near 0 on both sides. *)
    destruct (classify_nonzero x cx Hx Ecx H1 H2) as (r & Hr & Hr0).
    destruct (near_M y Hy Ecy) as [NP NN].
    destruct (Rdichotomy r 0 Hr0) as [Hn|Hp].
    * apply tightest_entire;
        [exact (div_up_nn x y r Hr Hn NN) | exact (div_down_np x y r Hr Hn NP)].
    * apply tightest_entire;
        [exact (div_up_pp x y r Hr Hp NP) | exact (div_down_pn x y r Hr Hp NN)].
Qed.

(** ** [recip x] *)

Lemma recip_empty :
  forall has_fma x c, valid x -> Interval.classify x = Some c -> c = CE \/ c = CZ ->
  exists z, Interval.recip has_fma x = Some z /\
    is_tightest (image_dom recip_dom Rinv x) z.
Proof.
intros has_fma x c Hx Hc Hce. exists Interval.EMPTY. split.
- unfold Interval.recip. rewrite Hc. destruct Hce as [-> | ->]; reflexivity.
- apply tightest_empty. intros u (r & Hr & Hr0 & _). unfold recip_dom in Hr0.
  destruct Hce as [-> | ->].
  + exact (classify_mem x CE Hx Hc r Hr).
  + (* The only real of [x] is 0, outside the domain. *)
    apply (classify_mem x CZ Hx Hc) in Hr. exact (Hr0 Hr).
Qed.

Lemma recip_entire :
  forall has_fma x, valid x -> Interval.classify x = Some CM ->
  exists z, Interval.recip has_fma x = Some z /\
    is_tightest (image_dom recip_dom Rinv x) z.
Proof.
intros has_fma x Hx Hc. exists Interval.ENTIRE. split.
- unfold Interval.recip. rewrite Hc. reflexivity.
- (* [1 / t] for the reals [t] of [x] near 0 above 0 has no upper bound,
     and below 0 no lower bound. *)
  destruct (near_M x Hx Hc) as [NP NN]. apply tightest_entire.
  + intros m.
    destruct (quot_near0 (fun t => mem t x) 1 m Rlt_0_1 NP) as (t & Ht & Ht0 & Hm).
    assert (E : 1 / t = / t) by (field; lra).
    exists (/ t). split; [|lra].
    exists t. split; [exact Ht|]. split; [exact (Rgt_not_eq t 0 Ht0) | reflexivity].
  + intros m.
    destruct (quot_near0 (fun t => mem (- t) x) 1 (- m) Rlt_0_1 NN)
      as (t & Ht & Ht0 & Hm).
    assert (E : / (- t) = - (1 / t)) by (field; lra).
    exists (/ (- t)). split; [|lra].
    exists (- t). split; [exact Ht|].
    split; [exact (Rlt_not_eq (- t) 0 ltac:(lra)) | reflexivity].
Qed.

(** ** [contains(0.0)] *)

(** [all] of two masks is the [&&] of their booleans. *)
Lemma all_mask :
  forall b0 b1, Generic.all (Generic.mask b0, Generic.mask b1) = b0 && b1.
Proof.
intros [] []; vm_compute; reflexivity.
Qed.

(** [contains(0.0)] compares [-0] with the first lane and [+0] with the
    second: [neg0 (splat zero)] is [[-0; +0]], and [zero] is finite. *)
Lemma contains_zero_lanes :
  forall x, Interval.contains x zero =
    Bleb (B754_zero true) (fst (rep x)) && Bleb (B754_zero false) (snd (rep x)).
Proof.
intros [[x0 x1]]. cbn [rep fst snd].
change (Interval.contains {| rep := (x0, x1) |} zero) with
  (Generic.all (Generic.mask (Bleb (B754_zero true) x0),
                Generic.mask (Bleb (B754_zero false) x1))).
apply all_mask.
Qed.

(** A zero is at most a finite float or +inf [w] exactly when 0 is below
    its bound. *)
Lemma Bleb_zero_lane :
  forall w s, upper_ok w -> Bleb (B754_zero s) w = true <-> below (bound w) 0.
Proof.
intros w s [Fw| ->].
- rewrite Bleb_correct by first [exact Fw | reflexivity].
  rewrite (bound_finite w Fw). cbn [below B2R].
  case Rle_bool_spec; intros H; split; intros H';
    solve [exact H | reflexivity | discriminate H' | lra].
- rewrite bound_inf. cbn [below]. split; intros _; [exact I | destruct s; reflexivity].
Qed.

(** [zero] is the float +0. *)
Lemma contains_zero :
  forall x, valid x -> Interval.contains x zero = true <-> mem 0 x.
Proof.
intros x Hx. rewrite contains_zero_lanes.
pose proof (Bool.andb_true_iff (Bleb (B754_zero true) (fst (rep x)))
  (Bleb (B754_zero false) (snd (rep x)))) as A.
destruct (is_nan (fst (rep x))) eqn:Hn.
- (* An empty [x] has NaN lanes, which no zero is at most. *)
  pose proof (empty_nan x Hx Hn) as E.
  split; [intros H | intros H; destruct (mem_nan x 0 E H)].
  rewrite E in H. vm_compute in H. discriminate H.
- (* Otherwise its lanes are floats or +inf, and 0 is in [x] exactly when
     [-0] is below the first lane and 0 below the second. *)
  destruct (lanes_tight x Hx Hn) as (U0 & U1 & _ & _ & _).
  pose proof (Bleb_zero_lane _ true U0) as L0.
  pose proof (Bleb_zero_lane _ false U1) as L1.
  pose proof (mem_lanes x Hx Hn 0) as M. rewrite Ropp_0 in M.
  tauto.
Qed.
