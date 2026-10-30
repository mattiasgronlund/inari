(** * The argument reduction of [sin], [cos] and [tan] of intervals

    For a nonempty [x = [a, b]], [Interval::cos] computes
    [q_nowrap = (x / PI).floor()] with the proved interval [/]
    ([div_correct] in [Div.v]) and [floor] ([floor_correct] in
    [Integer.v]), and reads its bounds [qa] and [qb]; [sin] and [tan] do
    the same with [FRAC_PI_2]. For [C] that holds [c] ([trig_const]),
    [trig_reduce] gives what the case analyses need of [qa] and [qb]: an
    infinite bound gives an infinite one, and a finite bound an integer
    [k] with [k * c <= a] ([red_lo]), strictly unless [k = 0] because [C]
    is strictly wider than [c], or with [b < (k + 1) * c] ([red_hi]). So
    every real [r] of [x] has [qa <= floor(r / c) <= qb].
    [trig_reduce_exact] gives the exact floors when [q_nowrap] is the hull
    of [floor(r / c)].

    The tests [n == 0.0], [n <= 1.0], [n < 2.0] and so on of
    [n = qb - qa], rounded to nearest, decide the exact difference
    [kb - ka] ([n_small]), as rounding to nearest is monotone and 0 to 5
    are floats; [n] is +inf if [qa] or [qb] is infinite ([n_inf]).
    [rem_euclid_2] and [rem_euclid(4.0)] of an integer [qa] give its
    remainder ([rem_euclid_2_int], [rem_euclid_4_int]). *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer Div PiBounds Sign AddSub AddRu Encoding
  Decompose DecBinary TrigQuot.

Open Scope R_scope.

(** ** [floor(r / c)] *)

Lemma floor_div_bounds :
  forall c r, 0 < c -> Rfloor (r / c) * c <= r < (Rfloor (r / c) + 1) * c.
Proof.
intros c r Hc.
destruct (Rfloor_near (r / c)) as [H1 _].
pose proof (Rfloor_lb (r / c)) as H0.
assert (E : r / c * c = r) by (field; lra).
set (q := r / c) in *. set (f := Rfloor q) in *. clearbody q f.
rewrite <- E.
split; [apply Rmult_le_compat_r | apply Rmult_lt_compat_r]; lra.
Qed.

Lemma floor_div_eq :
  forall c r k, 0 < c -> IZR k * c <= r < (IZR k + 1) * c -> Rfloor (r / c) = IZR k.
Proof.
intros c r k Hc [H1 H2]. apply Rfloor_imp.
assert (E : r / c * c = r) by (field; lra).
set (q := r / c) in *. clearbody q. subst r.
split; [apply (Rmult_le_reg_r c) | apply (Rmult_lt_reg_r c)]; lra.
Qed.

(** ** The bounds of [q_nowrap] *)

(** [qa] for the lower bound [a]. *)
Definition red_lo (c : R) (a qa : f64) : Prop :=
  (a = B754_infinity true /\ qa = B754_infinity true) \/
  (is_finite a = true /\ is_finite qa = true /\
   exists k, B2R qa = IZR k /\ IZR k * c <= B2R a /\
     ((k <> 0)%Z -> IZR k * c < B2R a)).

(** [qb] for the upper bound [b]. *)
Definition red_hi (c : R) (b qb : f64) : Prop :=
  (b = B754_infinity false /\ qb = B754_infinity false) \/
  (is_finite b = true /\ is_finite qb = true /\
   exists k, B2R qb = IZR k /\ B2R b < (IZR k + 1) * c).

(** The bounds of [floor z] are the floors of those of [z]. *)
Lemma rd_floor_inf :
  forall z, Interval.inf_raw (Interval.floor z) = ffloor (Interval.inf_raw z).
Proof.
intros z. unfold Interval.inf_raw. rewrite floor_rep. apply Bopp_involutive.
Qed.

Lemma rd_floor_sup :
  forall z, Interval.sup_raw (Interval.floor z) = ffloor (Interval.sup_raw z).
Proof.
intros z. unfold Interval.sup_raw. now rewrite floor_rep.
Qed.

(** [k = floor(lz)] for the lower bound [lz] of [z], which is at most
    [a / t] for [t] = [c], [lo] and [hi]: so [k * c <= a], and strictly if
    [k <> 0], as [k * c < k * hi <= a] for [k > 0] and
    [k * c < k * lo <= a] for [k < 0]. *)
Lemma rd_lo_arith :
  forall c lo hi a lz k, 1 <= lo -> lo < c -> c < hi ->
  lz <= a / c -> lz <= a / lo -> lz <= a / hi -> IZR k <= lz ->
  IZR k * c <= a /\ ((k <> 0)%Z -> IZR k * c < a).
Proof.
intros c lo hi a lz k H1 H2 H3 Hc Hlo Hhi Hk.
assert (Ec : a / c * c = a) by (field; lra).
assert (Elo : a / lo * lo = a) by (field; lra).
assert (Ehi : a / hi * hi = a) by (field; lra).
set (qc := a / c) in *. set (ql := a / lo) in *. set (qh := a / hi) in *.
clearbody qc ql qh.
split.
- rewrite <- Ec. apply Rmult_le_compat_r; lra.
- intros Nk. destruct (Z.lt_trichotomy k 0) as [Lk|[Ek|Gk]]; [|contradiction|].
  + apply IZR_lt in Lk.
    assert (A : IZR k * lo <= ql * lo) by (apply Rmult_le_compat_r; lra).
    assert (B : IZR k * c < IZR k * lo) by nra.
    lra.
  + apply IZR_lt in Gk.
    assert (A : IZR k * hi <= qh * hi) by (apply Rmult_le_compat_r; lra).
    assert (B : IZR k * c < IZR k * hi) by (apply Rmult_lt_compat_l; lra).
    lra.
Qed.

(** [k = floor(uz)] for the upper bound [uz >= b / c] of [z]: so
    [b <= uz * c < (k + 1) * c]. *)
Lemma rd_hi_arith :
  forall c b uz k, 0 < c -> b / c <= uz -> uz < IZR k + 1 -> b < (IZR k + 1) * c.
Proof.
intros c b uz k Hc Hb Hk.
assert (E : b / c * c = b) by (field; lra).
set (q := b / c) in *. clearbody q. rewrite <- E.
apply (Rle_lt_trans _ (uz * c)); [apply Rmult_le_compat_r | apply Rmult_lt_compat_r]; lra.
Qed.

Theorem trig_reduce :
  forall has_fma C c x, trig_const C c -> valid x -> Interval.is_empty x = false ->
  exists z, Interval.div has_fma x C = Some z /\
    red_lo c (Interval.inf_raw x) (Interval.inf_raw (Interval.floor z)) /\
    red_hi c (Interval.sup_raw x) (Interval.sup_raw (Interval.floor z)).
Proof.
intros has_fma C c x HC Hx Hn.
pose proof HC as (VC & _ & _ & _ & L1 & Llo & Lhi).
destruct (div_correct has_fma x C Hx VC) as (z & Ez & Tz).
exists z. split; [exact Ez|].
destruct (trig_quot_lo C c x z HC Hx Hn Tz) as (Qi & Qf).
destruct (trig_quot_hi C c x z HC Hx Hn Tz) as (Qi' & Qf').
rewrite rd_floor_inf, rd_floor_sup.
destruct (valid_nonempty x Hx Hn) as (La & Ub & _).
split.
- destruct La as [Fa|Ea].
  + right. destruct (Qf Fa) as (Fz & H1 & H2 & H3).
    split; [exact Fa|]. split; [now rewrite ffloor_finite|].
    exists (Zfloor (B2R (Interval.inf_raw z))). split; [apply ffloor_B2R|].
    apply (rd_lo_arith c (B2R (Interval.inf_raw C)) (B2R (Interval.sup_raw C)) _
             (B2R (Interval.inf_raw z))); try assumption.
    apply Zfloor_lb.
  + left. split; [exact Ea|]. rewrite (Qi Ea). reflexivity.
- destruct Ub as [Fb|Eb].
  + right. destruct (Qf' Fb) as (Fz & H1).
    split; [exact Fb|]. split; [now rewrite ffloor_finite|].
    exists (Zfloor (B2R (Interval.sup_raw z))). split; [apply ffloor_B2R|].
    apply (rd_hi_arith c _ (B2R (Interval.sup_raw z))); [lra | exact H1 | apply Zfloor_ub].
  + left. split; [exact Eb|]. rewrite (Qi' Eb). reflexivity.
Qed.

(** ** The exact floors *)

Lemma rd_mem_iff :
  forall x r, valid x -> Interval.is_empty x = false ->
  mem r x <-> in_bounds (bound (Interval.inf_raw x)) (bound (Interval.sup_raw x)) r.
Proof.
intros x r Hx E. destruct (valid_nonempty x Hx E) as (La & Ub & _).
exact (mem_bounds x r La Ub).
Qed.

(** A nonempty interval whose reals are at least [lo] has a finite lower
    bound: otherwise [min(lo - 1, b)] would be in it. A copy of
    [cl_inf_finite] in [ClosedDom.v]. *)
Lemma rd_inf_finite :
  forall x lo, valid x -> Interval.is_empty x = false ->
  (forall r, mem r x -> lo <= r) -> is_finite (Interval.inf_raw x) = true.
Proof.
intros x lo Hx E Hlo.
destruct (valid_nonempty x Hx E) as ([Fa|Ea] & _ & _); [exact Fa|]. exfalso.
set (t := match bound (Interval.sup_raw x) with
          | Some b => Rmin (lo - 1) b | None => lo - 1 end).
assert (Ht : mem t x).
{ apply (rd_mem_iff x t Hx E). unfold Interval.inf_raw. rewrite Ea.
  split; [exact I|]. unfold t.
  destruct (bound (Interval.sup_raw x)); [apply Rmin_r | exact I]. }
apply Hlo in Ht. revert Ht. unfold t.
destruct (bound (Interval.sup_raw x)) as [b|]; intros Ht;
  [pose proof (Rmin_l (lo - 1) b)|]; lra.
Qed.

(** The mirror: a nonempty interval whose reals are at most [hi] has a
    finite upper bound, as otherwise [max(hi + 1, a)] would be in it. *)
Lemma rd_sup_finite :
  forall x hi, valid x -> Interval.is_empty x = false ->
  (forall r, mem r x -> r <= hi) -> is_finite (Interval.sup_raw x) = true.
Proof.
intros x hi Hx E Hhi.
destruct (valid_nonempty x Hx E) as (_ & [Fb|Eb] & _); [exact Fb|]. exfalso.
set (t := match bound (Interval.inf_raw x) with
          | Some a => Rmax (hi + 1) a | None => hi + 1 end).
assert (Ht : mem t x).
{ apply (rd_mem_iff x t Hx E). unfold Interval.sup_raw. rewrite Eb.
  split; [|exact I]. unfold t.
  destruct (bound (Interval.inf_raw x)); [apply Rmax_r | exact I]. }
apply Hhi in Ht. revert Ht. unfold t.
destruct (bound (Interval.inf_raw x)) as [a|]; intros Ht;
  [pose proof (Rmax_l (hi + 1) a)|]; lra.
Qed.

(** A finite lower bound [a] of a nonempty [x] is the least real of [x]. *)
Lemma rd_lo_mem :
  forall x, valid x -> Interval.is_empty x = false ->
  is_finite (Interval.inf_raw x) = true ->
  mem (B2R (Interval.inf_raw x)) x /\ forall r, mem r x -> B2R (Interval.inf_raw x) <= r.
Proof.
intros x Hx E Fa. destruct (valid_nonempty x Hx E) as (_ & _ & O).
assert (Ba : bound (Interval.inf_raw x) = Some (B2R (Interval.inf_raw x)))
  by (unfold bound; now rewrite Fa).
change (opp (fst (rep x))) with (Interval.inf_raw x) in O.
change (snd (rep x)) with (Interval.sup_raw x) in O.
rewrite Ba in O. split.
- apply (rd_mem_iff x _ Hx E). rewrite Ba. split; [apply Rle_refl|].
  unfold ordered in O. destruct (bound (Interval.sup_raw x)); [exact O | exact I].
- intros r Hr. apply (rd_mem_iff x r Hx E) in Hr. rewrite Ba in Hr. exact (proj1 Hr).
Qed.

(** A finite upper bound [b] of a nonempty [x] is the greatest real of [x]. *)
Lemma rd_hi_mem :
  forall x, valid x -> Interval.is_empty x = false ->
  is_finite (Interval.sup_raw x) = true ->
  mem (B2R (Interval.sup_raw x)) x /\ forall r, mem r x -> r <= B2R (Interval.sup_raw x).
Proof.
intros x Hx E Fb. destruct (valid_nonempty x Hx E) as (_ & _ & O).
assert (Bb : bound (Interval.sup_raw x) = Some (B2R (Interval.sup_raw x)))
  by (unfold bound; now rewrite Fb).
change (opp (fst (rep x))) with (Interval.inf_raw x) in O.
change (snd (rep x)) with (Interval.sup_raw x) in O.
rewrite Bb in O. split.
- apply (rd_mem_iff x _ Hx E). rewrite Bb. split; [|apply Rle_refl].
  unfold ordered in O. destruct (bound (Interval.inf_raw x)); [exact O | exact I].
- intros r Hr. apply (rd_mem_iff x r Hx E) in Hr. rewrite Bb in Hr. exact (proj2 Hr).
Qed.

(** [floor(r / c)] is increasing in [r] for [c > 0]. *)
Lemma rd_floor_div_le :
  forall c r s, 0 < c -> r <= s -> Rfloor (r / c) <= Rfloor (s / c).
Proof.
intros c r s Hc H. apply Rfloor_le. unfold Rdiv.
apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact Hc | exact H].
Qed.

Theorem trig_reduce_exact :
  forall has_fma C c x z, trig_const C c -> valid x -> Interval.is_empty x = false ->
  Interval.div has_fma x C = Some z ->
  is_hull (image (fun r => Rfloor (r / c)) x) (Interval.floor z) ->
  (is_finite (Interval.inf_raw x) = true ->
   B2R (Interval.inf_raw (Interval.floor z)) = Rfloor (B2R (Interval.inf_raw x) / c)) /\
  (is_finite (Interval.sup_raw x) = true ->
   B2R (Interval.sup_raw (Interval.floor z)) = Rfloor (B2R (Interval.sup_raw x) / c)).
Proof.
intros has_fma C c x z HC Hx Hn _ [Vf Hf].
assert (Hc : 0 < c) by (destruct HC as (_ & _ & _ & _ & L1 & Llo & _); lra).
(* [floor(r / c)] of a real [r] of [x] is a member of [floor z]. *)
assert (Hm : forall r, mem r x -> mem (Rfloor (r / c)) (Interval.floor z)).
{ intros r Hr. apply Hf. exists (Rfloor (r / c)), (Rfloor (r / c)).
  split; [exists r; split; [exact Hr | reflexivity]|].
  split; [exists r; split; [exact Hr | reflexivity]|]. lra. }
split.
- intros Fa. destruct (rd_lo_mem x Hx Hn Fa) as (Ma & La).
  set (a := B2R (Interval.inf_raw x)) in *. set (m := Rfloor (a / c)).
  (* Every member of [floor z] lies above some [floor(r / c) >= m]. *)
  assert (Lm : forall s, mem s (Interval.floor z) -> m <= s).
  { intros s Hs. apply Hf in Hs. destruct Hs as (u & v & (r & Hr & ->) & _ & Hu & _).
    apply (Rle_trans _ (Rfloor (r / c))); [|exact Hu].
    apply rd_floor_div_le; [exact Hc | exact (La r Hr)]. }
  pose proof (Hm a Ma) as Mm. fold m in Mm.
  pose proof (mem_not_empty _ _ Vf Mm) as Nf.
  pose proof (rd_inf_finite _ m Vf Nf Lm) as Ff.
  destruct (rd_lo_mem _ Vf Nf Ff) as (Mf & Lf).
  apply Rle_antisym; [exact (Lf m Mm) | exact (Lm _ Mf)].
- intros Fb. destruct (rd_hi_mem x Hx Hn Fb) as (Mb & Ub).
  set (b := B2R (Interval.sup_raw x)) in *. set (m := Rfloor (b / c)).
  (* Every member of [floor z] lies below some [floor(r / c) <= m]. *)
  assert (Um : forall s, mem s (Interval.floor z) -> s <= m).
  { intros s Hs. apply Hf in Hs. destruct Hs as (u & v & _ & (r & Hr & ->) & _ & Hv).
    apply (Rle_trans _ (Rfloor (r / c))); [exact Hv|].
    apply rd_floor_div_le; [exact Hc | exact (Ub r Hr)]. }
  pose proof (Hm b Mb) as Mm. fold m in Mm.
  pose proof (mem_not_empty _ _ Vf Mm) as Nf.
  pose proof (rd_sup_finite _ m Vf Nf Um) as Ff.
  destruct (rd_hi_mem _ Vf Nf Ff) as (Mf & Uf).
  apply Rle_antisym; [exact (Um _ Mf) | exact (Uf m Mm)].
Qed.

(** ** [a == b] *)

Lemma rd_beqb_inf_l :
  forall s (a : f64), Beqb (B754_infinity s) a = true -> a = B754_infinity s.
Proof.
intros [|] [[|]|[|]| |[|] m e H]; cbn; easy.
Qed.

Lemma rd_beqb_inf_r :
  forall s (a : f64), Beqb a (B754_infinity s) = true -> a = B754_infinity s.
Proof.
intros [|] [[|]|[|]| |[|] m e H]; cbn; easy.
Qed.

Lemma bounds_eq_finite :
  forall x, valid x -> Interval.is_empty x = false ->
  Model.eq (Interval.inf_raw x) (Interval.sup_raw x) = true ->
  is_finite (Interval.inf_raw x) = true /\ is_finite (Interval.sup_raw x) = true /\
  B2R (Interval.inf_raw x) = B2R (Interval.sup_raw x).
Proof.
intros x Hx Hne E.
destruct (valid_nonempty x Hx Hne) as (Ha & Hb & _).
unfold Interval.inf_raw, Interval.sup_raw, Model.eq in *.
destruct Ha as [Fa|Ea]; [|rewrite Ea in E; apply rd_beqb_inf_l in E;
  rewrite E in Hb; destruct Hb as [Hb|Hb]; discriminate].
destruct Hb as [Fb|Eb]; [|rewrite Eb in E; apply rd_beqb_inf_r in E;
  rewrite E in Fa; discriminate].
split; [exact Fa|]. split; [exact Fb|].
rewrite Beqb_correct in E by assumption.
revert E. case Req_bool_spec; [easy | discriminate].
Qed.

(** For a nonempty [x], [a == b] holds exactly when [x] holds one real. *)
Lemma bounds_eq :
  forall x, valid x -> Interval.is_empty x = false ->
  Model.eq (Interval.inf_raw x) (Interval.sup_raw x) = true <->
  (forall r t, mem r x -> mem t x -> r = t).
Proof.
intros x Hx Hne.
destruct (valid_nonempty x Hx Hne) as (Ha & Hb & Hab).
pose proof (fun r => mem_bounds x r Ha Hb) as Hm.
split.
- intros E r t Hr Ht.
  destruct (bounds_eq_finite x Hx Hne E) as (Fa & Fb & Eab).
  unfold Interval.inf_raw, Interval.sup_raw in *.
  apply Hm in Hr, Ht. unfold bound, in_bounds in Hr, Ht.
  rewrite Fa, Fb in Hr, Ht. lra.
- (* An unbounded [x] holds two different reals. *)
  intros H.
  unfold Interval.inf_raw, Interval.sup_raw, Model.eq in *.
  destruct Ha as [Fa|Ea], Hb as [Fb|Eb].
  + rewrite Beqb_correct by assumption. apply Req_bool_true.
    apply H; apply Hm; unfold bound, in_bounds; rewrite Fa, Fb;
      unfold bound, ordered in Hab; rewrite Fa, Fb in Hab; lra.
  + exfalso. assert (E : B2R (opp (fst (rep x))) = B2R (opp (fst (rep x))) + 1).
    { apply H; apply Hm; unfold bound, in_bounds; rewrite Fa, Eb; cbn; split; trivial; lra. }
    lra.
  + exfalso. assert (E : B2R (snd (rep x)) - 1 = B2R (snd (rep x))).
    { apply H; apply Hm; unfold bound, in_bounds; rewrite Ea, Fb; cbn; split; trivial; lra. }
    lra.
  + exfalso. assert (E : 0 = 1).
    { apply H; apply Hm; unfold bound, in_bounds; rewrite Ea, Eb; cbn; split; trivial. }
    lra.
Qed.

(** ** [n = qb - qa] *)

(** An integer of magnitude at most [2^53] is a float. *)
Lemma rd_int_format :
  forall n, (Z.abs n <= 2^53)%Z -> generic_format radix2 fexp64 (IZR n).
Proof.
intros n Hn.
destruct (Z.eq_dec (Z.abs n) (2^53)) as [E|E].
- assert (P : IZR (2^53) = bpow radix2 53) by (apply (IZR_Zpower radix2); lia).
  assert (Hb : generic_format radix2 fexp64 (bpow radix2 53))
    by (apply generic_format_FLT_bpow; [typeclasses eauto | lia]).
  destruct (Z.abs_spec n) as [[_ A]|[_ A]]; rewrite A in E.
  + rewrite E, P. exact Hb.
  + replace n with (- 2^53)%Z by lia. rewrite opp_IZR, P.
    now apply generic_format_opp.
- apply generic_format_FLT.
  apply FLT_spec with (Float radix2 n 0).
  + unfold F2R; simpl. ring.
  + cbn [Fnum]. simpl Z.pow in *. lia.
  + cbn [Fexp]. lia.
Qed.

Notation rd_RNE := (round radix2 fexp64 ZnearestE).

(** Rounding to nearest keeps the order of a natural number [D] and an
    integer [j] from 0 to 4, as [j - 1] and [j + 1] are floats too. *)
Lemma rd_round_cmp :
  forall D j, (0 <= D)%Z -> (0 <= j <= 4)%Z ->
  Req_bool (rd_RNE (IZR D)) (IZR j) = (D =? j)%Z /\
  Rlt_bool (rd_RNE (IZR D)) (IZR j) = (D <? j)%Z /\
  Rle_bool (rd_RNE (IZR D)) (IZR j) = (D <=? j)%Z.
Proof.
intros D j HD Hj.
assert (Fm : generic_format radix2 fexp64 (IZR (j - 1)))
  by (apply rd_int_format; lia).
assert (Fp : generic_format radix2 fexp64 (IZR (j + 1)))
  by (apply rd_int_format; lia).
assert (Fj : generic_format radix2 fexp64 (IZR j))
  by (apply rd_int_format; lia).
destruct (Z.compare_spec D j) as [->|Hlt|Hgt].
- rewrite (round_generic _ _ _ _ Fj).
  rewrite Req_bool_true, Rlt_bool_false, Rle_bool_true by lra.
  rewrite Z.eqb_refl, Z.ltb_irrefl, Z.leb_refl. auto.
- assert (H : rd_RNE (IZR D) <= IZR (j - 1)).
  { rewrite <- (round_generic _ _ ZnearestE _ Fm).
    apply round_le; [typeclasses eauto..|]. apply IZR_le. lia. }
  rewrite minus_IZR in H.
  rewrite Req_bool_false, Rlt_bool_true, Rle_bool_true by lra.
  destruct (Z.eqb_spec D j), (Z.ltb_spec D j), (Z.leb_spec D j); try lia; auto.
- assert (H : IZR (j + 1) <= rd_RNE (IZR D)).
  { rewrite <- (round_generic _ _ ZnearestE _ Fp).
    apply round_le; [typeclasses eauto..|]. apply IZR_le. lia. }
  rewrite plus_IZR in H.
  rewrite Req_bool_false, Rlt_bool_false, Rle_bool_false by lra.
  destruct (Z.eqb_spec D j), (Z.ltb_spec D j), (Z.leb_spec D j); try lia; auto.
Qed.

Lemma rd_inf_cmp :
  forall f : f64, is_finite f = true ->
  Model.lt (B754_infinity false) f = false /\ Model.le (B754_infinity false) f = false /\
  Model.eq (B754_infinity false) f = false.
Proof.
intros [s|s| |s m e H] F; try discriminate; destruct s; split; try split; reflexivity.
Qed.

Lemma n_small :
  forall qa qb ka kb, is_finite qa = true -> is_finite qb = true ->
  B2R qa = IZR ka -> B2R qb = IZR kb -> (ka <= kb)%Z ->
  let n := Model.sub qb qa in
  Model.eq n Model.zero = (kb - ka =? 0)%Z /\
  forall j, (1 <= j <= 4)%Z ->
    Model.lt n (of_u64 j) = (kb - ka <? j)%Z /\
    Model.le n (of_u64 j) = (kb - ka <=? j)%Z /\
    Model.eq n (of_u64 j) = (kb - ka =? j)%Z.
Proof.
intros qa qb ka kb Fa Fb Ea Eb Hk n.
pose proof (Bminus_correct 53 1024 _ _ mode_NE qb qa Fb Fa) as H.
change (Bminus mode_NE qb qa) with n in H. clearbody n.
rewrite Eb, Ea, <- minus_IZR in H.
change (SpecFloat.fexp 53 1024) with fexp64 in H. cbn [round_mode] in H.
set (D := (kb - ka)%Z) in *.
assert (HD : (0 <= D)%Z) by lia.
assert (Z0 : is_finite Model.zero = true /\ B2R Model.zero = IZR 0) by easy.
revert H. case Rlt_bool_spec; intros Hr H.
- destruct H as (Rn & Fn & _).
  unfold Model.eq, Model.lt, Model.le.
  split.
  + rewrite Beqb_correct by easy. rewrite Rn. now apply rd_round_cmp; [|lia].
  + intros j Hj.
    destruct (of_u64_exact j) as (Fj & _ & Rj); [lia|].
    rewrite Beqb_correct, Bltb_correct, Bleb_correct by easy. rewrite Rn, Rj.
    destruct (rd_round_cmp D j) as (R1 & R2 & R3); [lia..|]. auto.
- (* An overflow: [D] is at least 5, so [qb] is positive, and [n] is
     +inf. *)
  destruct H as (Hn & Hs).
  assert (H5 : (5 <= D)%Z).
  { destruct (Z_lt_le_dec D 5) as [Hl|]; [exfalso|easy].
    destruct (rd_round_cmp D 4) as (_ & _ & R3); [lia..|].
    assert (R4 : rd_RNE (IZR D) <= 4).
    { revert R3. case Rle_bool_spec; [easy|]. destruct (Z.leb_spec D 4); [easy|lia]. }
    assert (R0 : 0 <= rd_RNE (IZR D)).
    { rewrite <- (round_0 radix2 fexp64 ZnearestE).
      apply round_le; [typeclasses eauto..|]. apply IZR_le. lia. }
    revert Hr. rewrite Rabs_pos_eq by exact R0.
    cbn [bpow radix_val radix2 Z.pow_pos]. lra. }
  assert (Sb : Bsign qb = false).
  { destruct (Bsign qb) eqn:Sb; [exfalso|easy].
    apply B2R_Bsign_true in Sb.
    assert (Sa : Bsign qa = false) by (destruct (Bsign qa); easy).
    apply B2R_Bsign_false in Sa.
    rewrite Ea in Sa. rewrite Eb in Sb.
    apply le_IZR in Sa, Sb. lia. }
  rewrite Sb in Hn.
  assert (En : n = B754_infinity false) by (apply B2SF_inj; rewrite Hn; reflexivity).
  subst n.
  split; [destruct (Z.eqb_spec D 0); [lia|reflexivity]|].
  intros j Hj.
  destruct (of_u64_exact j) as (Fj & _ & _); [lia|].
  destruct (rd_inf_cmp _ Fj) as (R1 & R2 & R3). rewrite R1, R2, R3.
  destruct (Z.eqb_spec D j), (Z.ltb_spec D j), (Z.leb_spec D j); try lia; auto.
Qed.

Lemma n_inf :
  forall qa qb, is_nan qa = false -> is_nan qb = false ->
  qa <> B754_infinity false -> qb <> B754_infinity true ->
  qa = B754_infinity true \/ qb = B754_infinity false ->
  Model.sub qb qa = B754_infinity false.
Proof.
intros qa qb Na Nb Ha Hb [->| ->].
- destruct qb as [[|]|[|]| |[|] m e H]; try discriminate; try congruence; reflexivity.
- destruct qa as [[|]|[|]| |[|] m e H]; try discriminate; try congruence; reflexivity.
Qed.

(** ** The remainders *)

(** A finite float with the value 0 is a zero. *)
Lemma rd_zero_of :
  forall x : f64, is_finite x = true -> B2R x = 0 -> exists s, x = B754_zero s.
Proof.
intros [s|s| |s m e H] F E; try discriminate.
- now exists s.
- exfalso. revert E. cbn [B2R]. apply F2R_neq_0. destruct s; discriminate.
Qed.

(** A nonzero integer [k] that is a float is [M * 2^E] with [M] below
    [2^53] in magnitude and [E] above the subnormal exponent -1074, as
    [|k| >= 1]. *)
Lemma rd_int_float :
  forall (x : f64) k, B2R x = IZR k -> (k <> 0)%Z ->
  exists M E, IZR k = IZR M * bpow radix2 E /\ (Z.abs M < 2^53)%Z /\ (-1073 <= E)%Z.
Proof.
intros x k Ex Hk.
destruct (FLT_format_B2R 53 1024 _ x) as [[M E] HR HM HE].
cbn [Fnum Fexp] in HM, HE. unfold SpecFloat.emin in HE.
change (radix2 ^ 53)%Z with (2^53)%Z in HM.
rewrite Ex in HR. unfold F2R in HR. cbn [Fnum Fexp] in HR.
exists M, E. split; [exact HR|]. split; [exact HM|].
destruct (Z.eq_dec E (-1074)) as [->|]; [exfalso|lia].
(* [|k| = |M| * 2^-1074 < 2^-1021] *)
assert (A : IZR (Z.abs k) = IZR (Z.abs M) * bpow radix2 (-1074)).
{ rewrite !abs_IZR, HR, Rabs_mult, (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0.
  reflexivity. }
assert (B : IZR (Z.abs M) <= IZR (2^53)) by (apply IZR_le; lia).
assert (C : 1 <= IZR (Z.abs k)) by (apply IZR_le; lia).
rewrite (IZR_Zpower radix2) in B by lia.
assert (D : IZR (Z.abs M) * bpow radix2 (-1074) <= bpow radix2 53 * bpow radix2 (-1074)).
{ apply Rmult_le_compat_r; [apply bpow_ge_0 | exact B]. }
rewrite <- bpow_plus in D. change (53 + -1074)%Z with (-1021)%Z in D.
assert (F : bpow radix2 (-1021) < 1) by (apply (bpow_lt radix2 _ 0); lia).
lra.
Qed.

(** An odd integer that is a float is below [2^53] in magnitude, as the
    floats from [2^53] on are even. *)
Lemma rd_odd_small :
  forall (x : f64) k, B2R x = IZR k -> Z.even k = false -> (Z.abs k < 2^53)%Z.
Proof.
intros x k Ex Hk.
destruct (rd_int_float x k Ex) as (M & E & HR & HM & HE); [now intros ->|].
destruct (Z_lt_le_dec E 1) as [HE1|HE1].
- (* [|k| = |M| * 2^E <= |M|] *)
  assert (A : IZR (Z.abs k) = IZR (Z.abs M) * bpow radix2 E).
  { rewrite !abs_IZR, HR, Rabs_mult, (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0.
    reflexivity. }
  assert (B : bpow radix2 E <= 1) by (apply (bpow_le radix2 _ 0); lia).
  assert (C : 0 <= IZR (Z.abs M)) by (apply IZR_le; lia).
  assert (D : IZR (Z.abs k) <= IZR (Z.abs M)).
  { rewrite A. rewrite <- (Rmult_1_r (IZR (Z.abs M))) at 2.
    apply Rmult_le_compat_l; assumption. }
  apply le_IZR in D. lia.
- (* [k = M * 2^E] is even. *)
  exfalso.
  assert (A : k = (M * 2^E)%Z).
  { apply eq_IZR. rewrite mult_IZR, (IZR_Zpower radix2) by lia. exact HR. }
  rewrite A, Z.even_mul, Z.even_pow in Hk by lia.
  destruct (Z.even M); discriminate.
Qed.

Lemma rd_Req_bool_IZR :
  forall a b, Req_bool (IZR a) (IZR b) = (a =? b)%Z.
Proof.
intros a b. case Req_bool_spec; intros H; destruct (Z.eqb_spec a b); try easy.
- now apply eq_IZR in H.
- now subst b.
Qed.

Lemma rem_euclid_2_int :
  forall qa k, is_finite qa = true -> B2R qa = IZR k ->
  rem_euclid_2 qa = if Z.even k then Model.zero else of_u64 1.
Proof.
intros qa k Fa Ea.
destruct (Z.eq_dec k 0) as [->|Hk0].
- (* [qa] is a zero. *)
  destruct (rd_zero_of qa Fa Ea) as (s & ->).
  destruct s; vm_compute; reflexivity.
- destruct (of_u64_exact 2) as (F2 & _ & R2); [lia|].
  set (two := of_u64 2) in *.
  (* [qa / 2] is exact, as [k / 2] is a float with the significand of
     [k]. *)
  destruct (rd_int_float qa k Ea Hk0) as (M & E & HR & HM & HE).
  assert (Fh : generic_format radix2 fexp64 (IZR k / 2)).
  { apply generic_format_FLT. apply FLT_spec with (Float radix2 M (E - 1)).
    - unfold F2R; cbn [Fnum Fexp]. rewrite HR. replace (E - 1)%Z with (E + -1)%Z by lia. rewrite bpow_plus.
      change (bpow radix2 (-1)) with (/ 2). field.
    - cbn [Fnum]. exact HM.
    - cbn [Fexp]. lia. }
  assert (Lk : Rabs (IZR k) < bpow radix2 1024)
    by (rewrite <- Ea; apply abs_B2R_lt_emax).
  pose proof (Bdiv_correct 53 1024 _ _ mode_NE qa two) as Hd.
  rewrite R2, Ea in Hd. change (SpecFloat.fexp 53 1024) with fexp64 in Hd.
  cbn [round_mode] in Hd. rewrite (round_generic _ _ _ _ Fh) in Hd.
  rewrite Rlt_bool_true in Hd.
  2: { unfold Rdiv. rewrite Rabs_mult, Rabs_inv, (Rabs_pos_eq 2) by lra. pose proof (Rabs_pos (IZR k)). lra. }
  destruct (Hd ltac:(lra)) as (Rh & Fh' & _). clear Hd.
  change (Bdiv mode_NE qa two) with (div qa two) in Rh, Fh'.
  rewrite Fa in Fh'.
  set (h := div qa two) in *.
  (* [floor(k / 2)] is [k / 2] of integers, rounded toward -inf. *)
  assert (Rf : B2R (ffloor h) = IZR (k / 2)).
  { rewrite ffloor_B2R, Rh. apply Rfloor_imp.
    pose proof (Z.div_mod k 2 ltac:(lia)) as Dk.
    pose proof (Z.mod_pos_bound k 2 ltac:(lia)) as Bk.
    assert (Ek : IZR k = 2 * IZR (k / 2) + IZR (k mod 2)).
    { rewrite Dk at 1. rewrite plus_IZR, mult_IZR. reflexivity. }
    assert (B0 : 0 <= IZR (k mod 2)) by (apply IZR_le; lia).
    assert (B1 : IZR (k mod 2) <= 1) by (apply IZR_le; lia).
    lra. }
  assert (Ff : is_finite (ffloor h) = true) by (rewrite ffloor_finite; exact Fh').
  set (f := ffloor h) in *.
  (* [2 * (k / 2)] is [k] or [k - 1], and it is exact. *)
  assert (Ep : (2 * (k / 2) = k - k mod 2)%Z).
  { pose proof (Z.div_mod k 2 ltac:(lia)). lia. }
  assert (Fp : generic_format radix2 fexp64 (IZR (2 * (k / 2))) /\
    Rabs (IZR (2 * (k / 2))) < bpow radix2 1024).
  { rewrite Zmod_even in Ep. destruct (Z.even k) eqn:Ek.
    - rewrite Ep, Z.sub_0_r, <- Ea. split; [apply generic_format_B2R | apply abs_B2R_lt_emax].
    - pose proof (rd_odd_small qa k Ea Ek) as Hs.
      split; [apply rd_int_format; lia|].
      rewrite <- abs_IZR. apply Rle_lt_trans with (IZR (2^53)); [apply IZR_le; lia|].
      rewrite (IZR_Zpower radix2) by lia. apply bpow_lt. lia. }
  destruct Fp as (Fp & Lp).
  pose proof (Bmult_correct 53 1024 _ _ mode_NE two f) as Hm.
  rewrite R2, Rf, <- mult_IZR in Hm. change (SpecFloat.fexp 53 1024) with fexp64 in Hm.
  cbn [round_mode] in Hm. rewrite (round_generic _ _ _ _ Fp) in Hm.
  rewrite Rlt_bool_true in Hm by exact Lp.
  destruct Hm as (Rm & Fm & _).
  change (Bmult mode_NE two f) with (mul two f) in Rm, Fm.
  rewrite F2, Ff in Fm.
  unfold rem_euclid_2. fold two. fold h. fold f.
  unfold Model.eq. rewrite Beqb_correct by easy. rewrite Rm, Ea, rd_Req_bool_IZR.
  rewrite Zmod_even in Ep.
  destruct (Z.even k); destruct (Z.eqb_spec (2 * (k / 2)) k); try reflexivity; lia.
Qed.

Lemma rd_rem_facts :
  forall k, (k = 4 * Z.quot k 4 + Z.rem k 4 /\ Z.abs (Z.rem k 4) < 4 /\
  k = 4 * (k / 4) + k mod 4 /\ 0 <= k mod 4 < 4)%Z.
Proof.
intros k. split; [apply Z.quot_rem'|]. split; [apply (Z.rem_bound_abs k 4); lia|].
split; [apply Z.div_mod; lia | apply Z.mod_pos_bound; lia].
Qed.

Lemma rd_bpow_1024 : 4 < bpow radix2 1024.
Proof.
cbn [bpow radix_val radix2 Z.pow_pos]. lra.
Qed.

(** [qa % 4.0] is [Z.rem k 4], exactly: [frem] takes the remainder of
    [k * 2^-e] and [4 * 2^-e] for [e = min(ex, -50)], which is that of [k]
    and [4] times [2^-e]. *)
Lemma rd_frem_4 :
  forall qa k, is_finite qa = true -> B2R qa = IZR k -> (k <> 0)%Z ->
  is_finite (frem qa (of_u64 4)) = true /\ B2R (frem qa (of_u64 4)) = IZR (Z.rem k 4).
Proof.
intros qa k Fa Ea Hk0.
assert (B4 : B2SF (of_u64 4) = SpecFloat.S754_finite false 4503599627370496 (-50))
  by (vm_compute; reflexivity).
destruct (of_u64 4) as [| | |s4 m4 e4 H4]; try discriminate B4.
cbn [B2SF] in B4. injection B4 as -> -> ->.
destruct qa as [s|s| |s m e Hb]; try discriminate.
- exfalso. apply Hk0, eq_IZR. rewrite <- Ea. reflexivity.
- unfold frem. cbv beta iota zeta.
  cbn [B2R] in Ea. unfold F2R in Ea. cbn [Fnum Fexp] in Ea.
  set (e' := Z.min e (-50)).
  assert (He' : (e' <= -50 /\ e' <= e)%Z) by lia.
  set (P := (2 ^ (- e'))%Z).
  assert (RP : IZR P = bpow radix2 (- e')) by (apply (IZR_Zpower radix2); lia).
  assert (EN : (cond_Zopp s (Z.pos m) * 2 ^ (e - e') = k * P)%Z).
  { apply eq_IZR. rewrite !mult_IZR, (IZR_Zpower radix2) by lia. rewrite RP, <- Ea.
    replace (e - e')%Z with (e + - e')%Z by lia. rewrite bpow_plus. ring. }
  assert (ED : (Z.pos 4503599627370496 * 2 ^ (-50 - e') = 4 * P)%Z).
  { change (Z.pos 4503599627370496) with (2^52)%Z.
    rewrite <- Z.pow_add_r by lia. replace (52 + (-50 - e'))%Z with (2 + - e')%Z by lia.
    rewrite Z.pow_add_r by lia. reflexivity. }
  rewrite EN, ED, Z.mul_rem_distr_r by (try lia; unfold P; apply Z.pow_nonzero; lia).
  pose proof (binary_normalize_correct 53 1024 _ _ mode_NE (Z.rem k 4 * P) e' s) as H.
  cbv zeta in H. change (SpecFloat.fexp 53 1024) with fexp64 in H. cbn [round_mode] in H.
  assert (E : F2R (Float radix2 (Z.rem k 4 * P) e') = IZR (Z.rem k 4)).
  { unfold F2R. cbn [Fnum Fexp]. rewrite mult_IZR, RP, Rmult_assoc, <- bpow_plus.
    replace (- e' + e')%Z with 0%Z by lia. cbn [bpow]. ring. }
  rewrite E in H.
  pose proof (rd_rem_facts k) as Hr.
  rewrite (round_generic _ _ _ _ (rd_int_format (Z.rem k 4) ltac:(lia))) in H.
  rewrite Rlt_bool_true in H.
  2: { rewrite <- abs_IZR. apply Rle_lt_trans with 4; [|exact rd_bpow_1024].
       apply IZR_le. lia. }
  destruct H as (HR & HF & _). split; assumption.
Qed.

(** [qa.rem_euclid(4.0)] is [k mod 4], exactly. *)
Lemma rd_rem_euclid_4 :
  forall qa k, is_finite qa = true -> B2R qa = IZR k ->
  is_finite (rem_euclid qa (of_u64 4)) = true /\
  B2R (rem_euclid qa (of_u64 4)) = IZR (k mod 4).
Proof.
intros qa k Fa Ea.
destruct (Z.eq_dec k 0) as [->|Hk0].
- destruct (rd_zero_of qa Fa Ea) as (s & ->).
  assert (E : rem_euclid (B754_zero s) (of_u64 4) = B754_zero s)
    by (destruct s; vm_compute; reflexivity).
  rewrite E. split; reflexivity.
- destruct (rd_frem_4 qa k Fa Ea Hk0) as (Fr & Rr).
  destruct (of_u64_exact 4) as (F4 & _ & R4); [lia|].
  pose proof (rd_rem_facts k) as Hk.
  unfold rem_euclid. cbv zeta.
  set (r := frem qa (of_u64 4)) in *.
  unfold Model.lt. rewrite Bltb_correct by easy. rewrite Rr. change (B2R zero) with 0.
  case Rlt_bool_spec; intros Hlt.
  + (* A negative remainder, to which [|4.0|] is added exactly. *)
    apply lt_IZR in Hlt.
    pose proof (Bplus_correct 53 1024 _ _ mode_NE r (fabs (of_u64 4)) Fr) as H.
    unfold fabs in H. rewrite is_finite_Babs, B2R_Babs, R4, Rr in H.
    specialize (H F4).
    rewrite (Rabs_pos_eq 4) in H by lra.
    replace (IZR (Z.rem k 4) + 4) with (IZR (k mod 4)) in H
      by (rewrite <- plus_IZR; f_equal; lia).
    change (SpecFloat.fexp 53 1024) with fexp64 in H. cbn [round_mode] in H.
    rewrite (round_generic _ _ _ _ (rd_int_format (k mod 4) ltac:(lia))) in H.
    rewrite Rlt_bool_true in H.
    2: { rewrite <- abs_IZR. apply Rle_lt_trans with 4; [|exact rd_bpow_1024].
         apply IZR_le. lia. }
    destruct H as (HR & HF & _). split; assumption.
  + apply le_IZR in Hlt. split; [exact Fr|]. rewrite Rr. f_equal. lia.
Qed.

Lemma rem_euclid_4_int :
  forall qa k, is_finite qa = true -> B2R qa = IZR k ->
  let q := rem_euclid qa (of_u64 4) in
  Model.eq q Model.zero = (k mod 4 =? 0)%Z /\
  Model.eq q (of_u64 1) = (k mod 4 =? 1)%Z /\
  Model.eq q (of_u64 2) = (k mod 4 =? 2)%Z /\
  Model.eq q (of_u64 3) = (k mod 4 =? 3)%Z.
Proof.
intros qa k Fa Ea q.
destruct (rd_rem_euclid_4 qa k Fa Ea) as (Fq & Rq).
change (rem_euclid qa (of_u64 4)) with q in Fq, Rq. clearbody q.
destruct (of_u64_exact 1) as (F1 & _ & R1); [lia|].
destruct (of_u64_exact 2) as (F2 & _ & R2); [lia|].
destruct (of_u64_exact 3) as (F3 & _ & R3); [lia|].
unfold Model.eq. rewrite !Beqb_correct by easy.
rewrite Rq, R1, R2, R3. change (B2R zero) with (IZR 0). rewrite !rd_Req_bool_IZR.
auto.
Qed.
