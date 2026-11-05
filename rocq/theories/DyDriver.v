(** * Enclosures and Ziv's strategy

    The operations [encl_*] of [Dyadic] in [Model.v] return enclosures of
    every result of their operation on points of their operands, with
    bounds that are the extreme exact results rounded outward. [ziv]
    returns, if it returns, the real number that every level encloses
    rounded to an [f64] as [mpfr_round] says ([ziv_correct]), which is the
    conclusion of [point_correct] in [Contract.v] for [r = f (B2R x)].
    [None], a panic, is the cap of 4,096 bits or a panic of the
    evaluation. For a real number that is not an [f64], each level passes
    once its enclosure is narrower than a width that depends only on that
    number ([ziv_at_passes]). *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Mpfr Limbs IdealGetD DyRound DyConv DyOps OfPointCore.

Open Scope Z_scope.

(** The format of the finite [f64]s without the bound above, as in
    [IdealGetD.v]. *)
Local Notation G := (generic_format radix2 (SpecFloat.fexp 53 1024)).

Definition encl_ok (n : nat) (a : Dyadic.encl) : Prop :=
  dy_ok n (Dyadic.en_lo a) /\ dy_ok n (Dyadic.en_hi a) /\
  (Dyadic.dy_R (Dyadic.en_lo a) <= Dyadic.dy_R (Dyadic.en_hi a))%R.

Definition encl_small (a : Dyadic.encl) : Prop :=
  exp_small (Dyadic.en_lo a) /\ exp_small (Dyadic.en_hi a).

(** [lo <= r <= hi] *)
Definition encl_has (a : Dyadic.encl) (r : R) : Prop :=
  (Dyadic.dy_R (Dyadic.en_lo a) <= r <= Dyadic.dy_R (Dyadic.en_hi a))%R.

Definition lo_R (a : Dyadic.encl) : R := Dyadic.dy_R (Dyadic.en_lo a).
Definition hi_R (a : Dyadic.encl) : R := Dyadic.dy_R (Dyadic.en_hi a).

(** ** Helpers *)

(** Rounding is monotone, so it commutes with [Rmin] and [Rmax]. *)
Lemma dround_min :
  forall n up r1 r2,
  level_ok n -> dround n up (Rmin r1 r2) = Rmin (dround n up r1) (dround n up r2).
Proof.
  intros n up r1 r2 Hn. unfold Rmin at 1.
  destruct (Rle_dec r1 r2) as [H|H].
  - rewrite Rmin_left; [reflexivity | apply dround_le; assumption].
  - rewrite Rmin_right; [reflexivity | apply dround_le; [exact Hn | lra]].
Qed.

Lemma dround_max :
  forall n up r1 r2,
  level_ok n -> dround n up (Rmax r1 r2) = Rmax (dround n up r1) (dround n up r2).
Proof.
  intros n up r1 r2 Hn. unfold Rmax at 1.
  destruct (Rle_dec r1 r2) as [H|H].
  - rewrite Rmax_right; [reflexivity | apply dround_le; assumption].
  - rewrite Rmax_left; [reflexivity | apply dround_le; [exact Hn | lra]].
Qed.

Lemma dmin_ok :
  forall n x y,
  level_ok n -> dy_ok n x -> dy_ok n y ->
  dy_ok n (Dyadic.dmin n x y) /\
  Dyadic.dy_R (Dyadic.dmin n x y) = Rmin (Dyadic.dy_R x) (Dyadic.dy_R y).
Proof.
  intros n x y Hn Hx Hy.
  destruct (dmin_correct n x y Hn Hx Hy) as [[E|E] V]; split; try exact V; rewrite E; assumption.
Qed.

Lemma dmax_ok :
  forall n x y,
  level_ok n -> dy_ok n x -> dy_ok n y ->
  dy_ok n (Dyadic.dmax n x y) /\
  Dyadic.dy_R (Dyadic.dmax n x y) = Rmax (Dyadic.dy_R x) (Dyadic.dy_R y).
Proof.
  intros n x y Hn Hx Hy.
  destruct (dmax_correct n x y Hn Hx Hy) as [[E|E] V]; split; try exact V; rewrite E; assumption.
Qed.

Lemma between_min_max :
  forall p q z, (p <= z <= q \/ q <= z <= p)%R -> (Rmin p q <= z <= Rmax p q)%R.
Proof.
  intros p q z H. unfold Rmin, Rmax.
  destruct (Rle_dec p q); destruct H; split; lra.
Qed.

(** [x * c] lies between the products of the ends of [[a1, a2]] by [c]. *)
Lemma mul_between_l :
  forall a1 a2 x c,
  (a1 <= x <= a2)%R -> (Rmin (a1 * c) (a2 * c) <= x * c <= Rmax (a1 * c) (a2 * c))%R.
Proof.
  intros a1 a2 x c Hx. apply between_min_max.
  destruct (Rle_dec 0 c); [left | right]; split; nra.
Qed.

(** [a * y] lies between the products of [a] by the ends [b1] and [b2],
    in either order, of an interval that holds [y]. *)
Lemma mul_between_r :
  forall a y b1 b2,
  (b1 <= y <= b2 \/ b2 <= y <= b1)%R ->
  (Rmin (a * b1) (a * b2) <= a * y <= Rmax (a * b1) (a * b2))%R.
Proof.
  intros a y b1 b2 Hy. apply between_min_max.
  destruct (Rle_dec 0 a); destruct Hy; [left | right | right | left]; split; nra.
Qed.

Lemma min4_le :
  forall p1 p2 p3 p4,
  let m := Rmin (Rmin (Rmin p1 p2) p3) p4 in
  (m <= p1 /\ m <= p2 /\ m <= p3 /\ m <= p4)%R.
Proof.
  intros p1 p2 p3 p4 m. unfold m.
  pose proof (Rmin_l (Rmin (Rmin p1 p2) p3) p4). pose proof (Rmin_r (Rmin (Rmin p1 p2) p3) p4).
  pose proof (Rmin_l (Rmin p1 p2) p3). pose proof (Rmin_r (Rmin p1 p2) p3).
  pose proof (Rmin_l p1 p2). pose proof (Rmin_r p1 p2). lra.
Qed.

Lemma max4_ge :
  forall p1 p2 p3 p4,
  let m := Rmax (Rmax (Rmax p1 p2) p3) p4 in
  (p1 <= m /\ p2 <= m /\ p3 <= m /\ p4 <= m)%R.
Proof.
  intros p1 p2 p3 p4 m. unfold m.
  pose proof (Rmax_l (Rmax (Rmax p1 p2) p3) p4). pose proof (Rmax_r (Rmax (Rmax p1 p2) p3) p4).
  pose proof (Rmax_l (Rmax p1 p2) p3). pose proof (Rmax_r (Rmax p1 p2) p3).
  pose proof (Rmax_l p1 p2). pose proof (Rmax_r p1 p2). lra.
Qed.

(** The product of a point of [[a1, a2]] and a point between [b1] and [b2]
    lies between the least and the greatest of the four products of the
    ends, in the order of [Dyadic.encl_mul]. *)
Lemma mul_corners :
  forall a1 a2 b1 b2 x y,
  (a1 <= x <= a2)%R -> (b1 <= y <= b2 \/ b2 <= y <= b1)%R ->
  (Rmin (Rmin (Rmin (a1 * b1) (a1 * b2)) (a2 * b1)) (a2 * b2) <= x * y <=
   Rmax (Rmax (Rmax (a1 * b1) (a1 * b2)) (a2 * b1)) (a2 * b2))%R.
Proof.
  intros a1 a2 b1 b2 x y Hx Hy.
  pose proof (mul_between_l a1 a2 x y Hx) as [L1 U1].
  pose proof (mul_between_r a1 y b1 b2 Hy) as [L2 U2].
  pose proof (mul_between_r a2 y b1 b2 Hy) as [L3 U3].
  pose proof (min4_le (a1 * b1) (a1 * b2) (a2 * b1) (a2 * b2)) as (m1 & m2 & m3 & m4).
  pose proof (max4_ge (a1 * b1) (a1 * b2) (a2 * b1) (a2 * b2)) as (M1 & M2 & M3 & M4).
  cbv zeta in m1, m2, m3, m4, M1, M2, M3, M4.
  split.
  - apply Rle_trans with (2 := L1). apply Rmin_glb.
    + apply Rle_trans with (2 := L2). apply Rmin_glb; assumption.
    + apply Rle_trans with (2 := L3). apply Rmin_glb; assumption.
  - apply Rle_trans with (1 := U1). apply Rmax_lub.
    + apply Rle_trans with (1 := U2). apply Rmax_lub; assumption.
    + apply Rle_trans with (1 := U3). apply Rmax_lub; assumption.
Qed.

(** For [y] in [[b1, b2]], which does not hold 0, [/ y] lies in
    [[/ b2, / b1]]. *)
Lemma div_corners :
  forall b1 b2 y,
  (0 < b1 \/ b2 < 0)%R -> (b1 <= y <= b2)%R -> (/ b2 <= / y <= / b1)%R.
Proof.
  intros b1 b2 y [H|H] Hy.
  - split; apply Rinv_le_contravar; lra.
  - assert (/ - y <= / - b2 /\ / - b1 <= / - y)%R as [A B]
      by (split; apply Rinv_le_contravar; lra).
    rewrite !Rinv_opp in A, B. lra.
Qed.

(** The least of the four corners of an enclosure lies below the
    greatest. *)
Lemma min4_le_max4 :
  forall p1 p2 p3 p4,
  (Rmin (Rmin (Rmin p1 p2) p3) p4 <= Rmax (Rmax (Rmax p1 p2) p3) p4)%R.
Proof.
  intros p1 p2 p3 p4.
  pose proof (min4_le p1 p2 p3 p4) as (m1 & _). pose proof (max4_ge p1 p2 p3 p4) as (M1 & _).
  cbv zeta in m1, M1. lra.
Qed.

(** ** The operations on enclosures *)

Lemma encl_point_correct :
  forall n x,
  level_ok n -> is_finite x = true ->
  exists c,
  Dyadic.encl_point n x = Some c /\ encl_ok n c /\ encl_small c /\
  lo_R c = B2R x /\ hi_R c = B2R x.
Proof.
  intros n x Hn Hx.
  destruct (from_f64_correct n x Hn Hx) as (d & E & Ok & S & V).
  unfold Dyadic.encl_point. rewrite E. cbv beta iota.
  eexists. split; [reflexivity|].
  unfold encl_ok, encl_small, lo_R, hi_R; cbn [Dyadic.en_lo Dyadic.en_hi].
  split; [split; [exact Ok | split; [exact Ok | apply Rle_refl]] |].
  split; [split; exact S |]. split; exact V.
Qed.

Lemma encl_neg_correct :
  forall n a,
  level_ok n -> encl_ok n a -> encl_small a ->
  encl_ok n (Dyadic.encl_neg n a) /\ encl_small (Dyadic.encl_neg n a) /\
  lo_R (Dyadic.encl_neg n a) = (- hi_R a)%R /\ hi_R (Dyadic.encl_neg n a) = (- lo_R a)%R /\
  forall x, encl_has a x -> encl_has (Dyadic.encl_neg n a) (- x).
Proof.
  intros n a Hn (Hla & Hha & Ha) (Sla & Sha).
  destruct (neg_correct n (Dyadic.en_lo a) Hn Hla) as (Oklo & Vlo & Xlo).
  destruct (neg_correct n (Dyadic.en_hi a) Hn Hha) as (Okhi & Vhi & Xhi).
  unfold Dyadic.encl_neg, encl_ok, encl_small, encl_has, lo_R, hi_R, exp_small in *;
    cbn [Dyadic.en_lo Dyadic.en_hi].
  rewrite Vlo, Vhi, Xlo, Xhi.
  split; [split; [exact Okhi | split; [exact Oklo | lra]] |].
  split; [split; assumption |].
  split; [reflexivity | split; [reflexivity |]].
  intros x Hx. lra.
Qed.

Lemma encl_add_correct :
  forall n a b,
  level_ok n -> encl_ok n a -> encl_ok n b -> encl_small a -> encl_small b ->
  exists c,
  Dyadic.encl_add n a b = Some c /\ encl_ok n c /\
  lo_R c = dround n false (lo_R a + lo_R b) /\ hi_R c = dround n true (hi_R a + hi_R b) /\
  forall x y, encl_has a x -> encl_has b y -> encl_has c (x + y).
Proof.
  intros n a b Hn (Hla & Hha & Ha) (Hlb & Hhb & Hb) (Sla & Sha) (Slb & Shb).
  destruct (add_correct n _ _ false Hn Hla Hlb Sla Slb) as (lo & Elo & Oklo & Vlo).
  destruct (add_correct n _ _ true Hn Hha Hhb Sha Shb) as (hi & Ehi & Okhi & Vhi).
  unfold Dyadic.encl_add. rewrite Elo, Ehi. cbv beta iota.
  eexists. split; [reflexivity|].
  unfold encl_ok, encl_has, lo_R, hi_R in *; cbn [Dyadic.en_lo Dyadic.en_hi].
  rewrite Vlo, Vhi.
  pose proof (dround_bounds n (Dyadic.dy_R (Dyadic.en_lo a) + Dyadic.dy_R (Dyadic.en_lo b)) Hn).
  pose proof (dround_bounds n (Dyadic.dy_R (Dyadic.en_hi a) + Dyadic.dy_R (Dyadic.en_hi b)) Hn).
  split; [split; [exact Oklo | split; [exact Okhi | lra]] |].
  split; [reflexivity | split; [reflexivity |]].
  intros x y Hx Hy. lra.
Qed.

Lemma encl_sub_correct :
  forall n a b,
  level_ok n -> encl_ok n a -> encl_ok n b -> encl_small a -> encl_small b ->
  exists c,
  Dyadic.encl_sub n a b = Some c /\ encl_ok n c /\
  lo_R c = dround n false (lo_R a - hi_R b) /\ hi_R c = dround n true (hi_R a - lo_R b) /\
  forall x y, encl_has a x -> encl_has b y -> encl_has c (x - y).
Proof.
  intros n a b Hn (Hla & Hha & Ha) (Hlb & Hhb & Hb) (Sla & Sha) (Slb & Shb).
  destruct (sub_correct n _ _ false Hn Hla Hhb Sla Shb) as (lo & Elo & Oklo & Vlo).
  destruct (sub_correct n _ _ true Hn Hha Hlb Sha Slb) as (hi & Ehi & Okhi & Vhi).
  unfold Dyadic.encl_sub. rewrite Elo, Ehi. cbv beta iota.
  eexists. split; [reflexivity|].
  unfold encl_ok, encl_has, lo_R, hi_R in *; cbn [Dyadic.en_lo Dyadic.en_hi].
  rewrite Vlo, Vhi.
  pose proof (dround_bounds n (Dyadic.dy_R (Dyadic.en_lo a) - Dyadic.dy_R (Dyadic.en_hi b)) Hn).
  pose proof (dround_bounds n (Dyadic.dy_R (Dyadic.en_hi a) - Dyadic.dy_R (Dyadic.en_lo b)) Hn).
  split; [split; [exact Oklo | split; [exact Okhi | lra]] |].
  split; [reflexivity | split; [reflexivity |]].
  intros x y Hx Hy. lra.
Qed.

Lemma encl_mul_correct :
  forall n a b,
  level_ok n -> encl_ok n a -> encl_ok n b -> encl_small a -> encl_small b ->
  exists c,
  Dyadic.encl_mul n a b = Some c /\ encl_ok n c /\
  lo_R c =
  dround n false
    (Rmin (Rmin (Rmin (lo_R a * lo_R b) (lo_R a * hi_R b)) (hi_R a * lo_R b))
       (hi_R a * hi_R b)) /\
  hi_R c =
  dround n true
    (Rmax (Rmax (Rmax (lo_R a * lo_R b) (lo_R a * hi_R b)) (hi_R a * lo_R b))
       (hi_R a * hi_R b)) /\
  forall x y, encl_has a x -> encl_has b y -> encl_has c (x * y).
Proof.
  intros n a b Hn (Hla & Hha & Ha) (Hlb & Hhb & Hb) (Sla & Sha) (Slb & Shb).
  unfold Dyadic.encl_mul. cbv beta iota zeta.
  destruct (negb (Dyadic.dy_neg (Dyadic.en_lo a)) && negb (Dyadic.dy_neg (Dyadic.en_lo b)))%bool
    eqn:Hs.
  - (* Both lower bounds are not negative: the least product is that of the
       lower bounds, and the greatest that of the upper bounds. *)
    apply andb_prop in Hs. destruct Hs as [Na Nb].
    apply Bool.negb_true_iff in Na, Nb.
    pose proof (dy_R_nonneg _ (proj1 Hla) Na) as Pa.
    pose proof (dy_R_nonneg _ (proj1 Hlb) Nb) as Pb.
    destruct (mul_correct n _ _ false Hn Hla Hlb Sla Slb) as (lo & Elo & Oklo & Vlo).
    destruct (mul_correct n _ _ true Hn Hha Hhb Sha Shb) as (hi & Ehi & Okhi & Vhi).
    rewrite Elo, Ehi. cbv beta iota.
    eexists. split; [reflexivity|].
    unfold encl_ok, encl_has, lo_R, hi_R in *; cbn [Dyadic.en_lo Dyadic.en_hi].
    rewrite Vlo, Vhi.
    set (la := Dyadic.dy_R (Dyadic.en_lo a)) in *. set (ha := Dyadic.dy_R (Dyadic.en_hi a)) in *.
    set (lb := Dyadic.dy_R (Dyadic.en_lo b)) in *. set (hb := Dyadic.dy_R (Dyadic.en_hi b)) in *.
    assert (Em : Rmin (Rmin (Rmin (la * lb) (la * hb)) (ha * lb)) (ha * hb) = (la * lb)%R).
    { rewrite (Rmin_left (la * lb) (la * hb)) by nra.
      rewrite (Rmin_left (la * lb) (ha * lb)) by nra.
      apply Rmin_left. nra. }
    assert (EM : Rmax (Rmax (Rmax (la * lb) (la * hb)) (ha * lb)) (ha * hb) = (ha * hb)%R).
    { apply Rmax_right. repeat apply Rmax_lub; nra. }
    pose proof (dround_bounds n (la * lb) Hn). pose proof (dround_bounds n (ha * hb) Hn).
    rewrite Em, EM.
    split; [split; [exact Oklo | split; [exact Okhi | nra]] |].
    split; [reflexivity | split; [reflexivity |]].
    intros x y Hx Hy.
    pose proof (mul_corners la ha lb hb x y Hx (or_introl Hy)) as Hxy.
    rewrite Em, EM in Hxy. lra.
  - destruct (mul_correct n _ _ false Hn Hla Hlb Sla Slb) as (xc & Exc & Okxc & Vxc).
    destruct (mul_correct n _ _ false Hn Hla Hhb Sla Shb) as (xd & Exd & Okxd & Vxd).
    destruct (mul_correct n _ _ false Hn Hha Hlb Sha Slb) as (yc & Eyc & Okyc & Vyc).
    destruct (mul_correct n _ _ false Hn Hha Hhb Sha Shb) as (yd & Eyd & Okyd & Vyd).
    destruct (mul_correct n _ _ true Hn Hla Hlb Sla Slb) as (xc' & Exc' & Okxc' & Vxc').
    destruct (mul_correct n _ _ true Hn Hla Hhb Sla Shb) as (xd' & Exd' & Okxd' & Vxd').
    destruct (mul_correct n _ _ true Hn Hha Hlb Sha Slb) as (yc' & Eyc' & Okyc' & Vyc').
    destruct (mul_correct n _ _ true Hn Hha Hhb Sha Shb) as (yd' & Eyd' & Okyd' & Vyd').
    rewrite Exc, Exd, Eyc, Eyd, Exc', Exd', Eyc', Eyd'. cbv beta iota.
    eexists. split; [reflexivity|].
    destruct (dmin_ok n xc xd Hn Okxc Okxd) as [O1 V1].
    destruct (dmin_ok n _ yc Hn O1 Okyc) as [O2 V2].
    destruct (dmin_ok n _ yd Hn O2 Okyd) as [O3 V3].
    destruct (dmax_ok n xc' xd' Hn Okxc' Okxd') as [P1 W1].
    destruct (dmax_ok n _ yc' Hn P1 Okyc') as [P2 W2].
    destruct (dmax_ok n _ yd' Hn P2 Okyd') as [P3 W3].
    unfold encl_ok, encl_has, lo_R, hi_R in *; cbn [Dyadic.en_lo Dyadic.en_hi].
    rewrite V3, V2, V1, W3, W2, W1, Vxc, Vxd, Vyc, Vyd, Vxc', Vxd', Vyc', Vyd'.
    rewrite <- !dround_min, <- !dround_max by exact Hn.
    set (la := Dyadic.dy_R (Dyadic.en_lo a)) in *. set (ha := Dyadic.dy_R (Dyadic.en_hi a)) in *.
    set (lb := Dyadic.dy_R (Dyadic.en_lo b)) in *. set (hb := Dyadic.dy_R (Dyadic.en_hi b)) in *.
    set (m := Rmin (Rmin (Rmin (la * lb) (la * hb)) (ha * lb)) (ha * hb)).
    set (M := Rmax (Rmax (Rmax (la * lb) (la * hb)) (ha * lb)) (ha * hb)).
    pose proof (dround_bounds n m Hn). pose proof (dround_bounds n M Hn).
    pose proof (min4_le_max4 (la * lb) (la * hb) (ha * lb) (ha * hb)) as Hm. fold m M in Hm.
    split; [split; [exact O3 | split; [exact P3 | lra]] |].
    split; [reflexivity | split; [reflexivity |]].
    intros x y Hx Hy.
    pose proof (mul_corners la ha lb hb x y Hx (or_introl Hy)) as Hxy. fold m M in Hxy. lra.
Qed.

Lemma encl_div_correct :
  forall n a b,
  level_ok n -> encl_ok n a -> encl_ok n b -> encl_small a -> encl_small b ->
  (0 < lo_R b \/ hi_R b < 0)%R ->
  exists c,
  Dyadic.encl_div n a b = Some c /\ encl_ok n c /\
  lo_R c =
  dround n false
    (Rmin (Rmin (Rmin (lo_R a / lo_R b) (lo_R a / hi_R b)) (hi_R a / lo_R b))
       (hi_R a / hi_R b)) /\
  hi_R c =
  dround n true
    (Rmax (Rmax (Rmax (lo_R a / lo_R b) (lo_R a / hi_R b)) (hi_R a / lo_R b))
       (hi_R a / hi_R b)) /\
  forall x y, encl_has a x -> encl_has b y -> encl_has c (x / y).
Proof.
  intros n a b Hn (Hla & Hha & Ha) (Hlb & Hhb & Hb) (Sla & Sha) (Slb & Shb) H0.
  destruct (dy_zero_ok n) as (Hz & Vz & _).
  unfold lo_R, hi_R in H0.
  assert (Nl : Dyadic.dy_R (Dyadic.en_lo b) <> 0%R) by lra.
  assert (Nh : Dyadic.dy_R (Dyadic.en_hi b) <> 0%R) by lra.
  assert (Hg :
    (match Dyadic.cmp n (Dyadic.en_lo b) (Dyadic.dy_zero n) with Gt => true | _ => false end
     || match Dyadic.cmp n (Dyadic.en_hi b) (Dyadic.dy_zero n) with Lt => true | _ => false end)%bool
    = true).
  { rewrite (cmp_correct n _ _ Hn Hlb Hz), (cmp_correct n _ _ Hn Hhb Hz), Vz.
    destruct H0 as [H|H].
    - rewrite (Rcompare_Gt _ _ H). reflexivity.
    - rewrite (Rcompare_Lt _ _ H). destruct (Rcompare _ 0); reflexivity. }
  destruct (div_correct n _ _ false Hn Hla Hlb Sla Slb Nl) as (xc & Exc & Okxc & Vxc).
  destruct (div_correct n _ _ false Hn Hla Hhb Sla Shb Nh) as (xd & Exd & Okxd & Vxd).
  destruct (div_correct n _ _ false Hn Hha Hlb Sha Slb Nl) as (yc & Eyc & Okyc & Vyc).
  destruct (div_correct n _ _ false Hn Hha Hhb Sha Shb Nh) as (yd & Eyd & Okyd & Vyd).
  destruct (div_correct n _ _ true Hn Hla Hlb Sla Slb Nl) as (xc' & Exc' & Okxc' & Vxc').
  destruct (div_correct n _ _ true Hn Hla Hhb Sla Shb Nh) as (xd' & Exd' & Okxd' & Vxd').
  destruct (div_correct n _ _ true Hn Hha Hlb Sha Slb Nl) as (yc' & Eyc' & Okyc' & Vyc').
  destruct (div_correct n _ _ true Hn Hha Hhb Sha Shb Nh) as (yd' & Eyd' & Okyd' & Vyd').
  unfold Dyadic.encl_div. cbv beta iota zeta. rewrite Hg. cbn [negb].
  rewrite Exc, Exd, Eyc, Eyd, Exc', Exd', Eyc', Eyd'. cbv beta iota.
  eexists. split; [reflexivity|].
  destruct (dmin_ok n xc xd Hn Okxc Okxd) as [O1 V1].
  destruct (dmin_ok n _ yc Hn O1 Okyc) as [O2 V2].
  destruct (dmin_ok n _ yd Hn O2 Okyd) as [O3 V3].
  destruct (dmax_ok n xc' xd' Hn Okxc' Okxd') as [P1 W1].
  destruct (dmax_ok n _ yc' Hn P1 Okyc') as [P2 W2].
  destruct (dmax_ok n _ yd' Hn P2 Okyd') as [P3 W3].
  unfold encl_ok, encl_has, lo_R, hi_R in *; cbn [Dyadic.en_lo Dyadic.en_hi].
  rewrite V3, V2, V1, W3, W2, W1, Vxc, Vxd, Vyc, Vyd, Vxc', Vxd', Vyc', Vyd'.
  rewrite <- !dround_min, <- !dround_max by exact Hn.
  set (la := Dyadic.dy_R (Dyadic.en_lo a)) in *. set (ha := Dyadic.dy_R (Dyadic.en_hi a)) in *.
  set (lb := Dyadic.dy_R (Dyadic.en_lo b)) in *. set (hb := Dyadic.dy_R (Dyadic.en_hi b)) in *.
  set (m := Rmin (Rmin (Rmin (la / lb) (la / hb)) (ha / lb)) (ha / hb)).
  set (M := Rmax (Rmax (Rmax (la / lb) (la / hb)) (ha / lb)) (ha / hb)).
  pose proof (dround_bounds n m Hn). pose proof (dround_bounds n M Hn).
  pose proof (min4_le_max4 (la / lb) (la / hb) (ha / lb) (ha / hb)) as Hm. fold m M in Hm.
  split; [split; [exact O3 | split; [exact P3 | lra]] |].
  split; [reflexivity | split; [reflexivity |]].
  intros x y Hx Hy.
  pose proof (div_corners lb hb y H0 Hy) as Hi.
  pose proof (mul_corners la ha (/ lb) (/ hb) x (/ y) Hx (or_intror Hi)) as Hxy.
  unfold Rdiv in m, M. fold m M in Hxy. unfold Rdiv. lra.
Qed.

(** [assert!(..., "division by an enclosure of zero")] *)
Lemma encl_div_zero :
  forall n a b,
  level_ok n -> encl_ok n b -> (lo_R b <= 0 <= hi_R b)%R -> Dyadic.encl_div n a b = None.
Proof.
  intros n a b Hn (Hlb & Hhb & _) (H1 & H2).
  destruct (dy_zero_ok n) as (Hz & Vz & _).
  unfold Dyadic.encl_div. cbv beta iota zeta.
  rewrite (cmp_correct n _ _ Hn Hlb Hz), (cmp_correct n _ _ Hn Hhb Hz), Vz.
  unfold lo_R, hi_R in *.
  destruct (Rcompare_spec (Dyadic.dy_R (Dyadic.en_lo b)) 0); [| | lra];
    destruct (Rcompare_spec (Dyadic.dy_R (Dyadic.en_hi b)) 0); try lra; reflexivity.
Qed.

Lemma encl_sqrt_correct :
  forall n a,
  level_ok n -> encl_ok n a -> encl_small a -> (0 <= hi_R a)%R ->
  exists c,
  Dyadic.encl_sqrt n a = Some c /\ encl_ok n c /\
  lo_R c = dround n false (sqrt (Rmax (lo_R a) 0)) /\ hi_R c = dround n true (sqrt (hi_R a)) /\
  forall x, (0 <= x)%R -> encl_has a x -> encl_has c (sqrt x).
Proof.
  intros n a Hn (Hla & Hha & Ha) (Sla & Sha) H0.
  destruct (dy_zero_ok n) as (Hz & Vz & Sz).
  destruct (dmax_correct n (Dyadic.en_lo a) (Dyadic.dy_zero n) Hn Hla Hz) as [Ed Vd].
  assert (Okd : dy_ok n (Dyadic.dmax n (Dyadic.en_lo a) (Dyadic.dy_zero n)))
    by (destruct Ed as [E|E]; rewrite E; assumption).
  assert (Sd : exp_small (Dyadic.dmax n (Dyadic.en_lo a) (Dyadic.dy_zero n)))
    by (destruct Ed as [E|E]; rewrite E; assumption).
  rewrite Vz in Vd.
  assert (Pd : (0 <= Dyadic.dy_R (Dyadic.dmax n (Dyadic.en_lo a) (Dyadic.dy_zero n)))%R)
    by (rewrite Vd; apply Rmax_r).
  destruct (sqrt_correct n _ false Hn Okd Sd Pd) as (lo & Elo & Oklo & Vlo).
  destruct (sqrt_correct n _ true Hn Hha Sha H0) as (hi & Ehi & Okhi & Vhi).
  unfold Dyadic.encl_sqrt. rewrite Elo, Ehi. cbv beta iota.
  eexists. split; [reflexivity|].
  unfold encl_ok, encl_has, lo_R, hi_R in *; cbn [Dyadic.en_lo Dyadic.en_hi].
  rewrite Vlo, Vhi, Vd.
  set (la := Dyadic.dy_R (Dyadic.en_lo a)) in *. set (ha := Dyadic.dy_R (Dyadic.en_hi a)) in *.
  pose proof (dround_bounds n (sqrt (Rmax la 0)) Hn). pose proof (dround_bounds n (sqrt ha) Hn).
  assert (sqrt (Rmax la 0) <= sqrt ha)%R
    by (apply sqrt_le_1_alt, Rmax_lub; assumption).
  split; [split; [exact Oklo | split; [exact Okhi | lra]] |].
  split; [reflexivity | split; [reflexivity |]].
  intros x Hx0 Hx.
  assert (sqrt (Rmax la 0) <= sqrt x)%R by (apply sqrt_le_1_alt, Rmax_lub; lra).
  assert (sqrt x <= sqrt ha)%R by (apply sqrt_le_1_alt; lra).
  lra.
Qed.

Lemma encl_sqrt_neg :
  forall n a, level_ok n -> encl_ok n a -> (hi_R a < 0)%R -> Dyadic.encl_sqrt n a = None.
Proof.
  intros n a Hn (_ & Hha & _) H.
  unfold Dyadic.encl_sqrt.
  destruct (Dyadic.sqrt n (Dyadic.dmax n (Dyadic.en_lo a) (Dyadic.dy_zero n)) false);
    [|reflexivity].
  rewrite (sqrt_neg n _ true Hn Hha H). reflexivity.
Qed.

Lemma encl_mul_u64_correct :
  forall n a k,
  level_ok n -> encl_ok n a -> encl_small a -> 0 <= k < 2 ^ 64 ->
  exists c,
  Dyadic.encl_mul_u64 n a k = Some c /\ encl_ok n c /\
  lo_R c = dround n false (lo_R a * IZR k) /\ hi_R c = dround n true (hi_R a * IZR k) /\
  forall x, encl_has a x -> encl_has c (x * IZR k).
Proof.
  intros n a k Hn (Hla & Hha & Ha) (Sla & Sha) Hk.
  destruct (mul_u64_correct n _ k false Hn Hla Sla Hk) as (lo & Elo & Oklo & Vlo).
  destruct (mul_u64_correct n _ k true Hn Hha Sha Hk) as (hi & Ehi & Okhi & Vhi).
  unfold Dyadic.encl_mul_u64. rewrite Elo, Ehi. cbv beta iota.
  eexists. split; [reflexivity|].
  unfold encl_ok, encl_has, lo_R, hi_R in *; cbn [Dyadic.en_lo Dyadic.en_hi].
  rewrite Vlo, Vhi.
  assert (K : (0 <= IZR k)%R) by (apply IZR_le; lia).
  set (la := Dyadic.dy_R (Dyadic.en_lo a)) in *. set (ha := Dyadic.dy_R (Dyadic.en_hi a)) in *.
  pose proof (dround_bounds n (la * IZR k) Hn). pose proof (dround_bounds n (ha * IZR k) Hn).
  assert (la * IZR k <= ha * IZR k)%R by (apply Rmult_le_compat_r; assumption).
  split; [split; [exact Oklo | split; [exact Okhi | lra]] |].
  split; [reflexivity | split; [reflexivity |]].
  intros x Hx.
  assert (la * IZR k <= x * IZR k)%R by (apply Rmult_le_compat_r; [exact K | apply Hx]).
  assert (x * IZR k <= ha * IZR k)%R by (apply Rmult_le_compat_r; [exact K | apply Hx]).
  lra.
Qed.

Lemma encl_div_u64_correct :
  forall n a k,
  level_ok n -> encl_ok n a -> encl_small a -> 0 < k < 2 ^ 64 ->
  exists c,
  Dyadic.encl_div_u64 n a k = Some c /\ encl_ok n c /\
  lo_R c = dround n false (lo_R a / IZR k) /\ hi_R c = dround n true (hi_R a / IZR k) /\
  forall x, encl_has a x -> encl_has c (x / IZR k).
Proof.
  intros n a k Hn (Hla & Hha & Ha) (Sla & Sha) Hk.
  destruct (div_u64_correct n _ k false Hn Hla Sla Hk) as (lo & Elo & Oklo & Vlo).
  destruct (div_u64_correct n _ k true Hn Hha Sha Hk) as (hi & Ehi & Okhi & Vhi).
  unfold Dyadic.encl_div_u64. rewrite Elo, Ehi. cbv beta iota.
  eexists. split; [reflexivity|].
  unfold encl_ok, encl_has, lo_R, hi_R in *; cbn [Dyadic.en_lo Dyadic.en_hi].
  rewrite Vlo, Vhi.
  assert (K : (0 <= / IZR k)%R)
    by (apply Rlt_le, Rinv_0_lt_compat, IZR_lt; lia).
  set (la := Dyadic.dy_R (Dyadic.en_lo a)) in *. set (ha := Dyadic.dy_R (Dyadic.en_hi a)) in *.
  pose proof (dround_bounds n (la / IZR k) Hn). pose proof (dround_bounds n (ha / IZR k) Hn).
  assert (la / IZR k <= ha / IZR k)%R by (apply Rmult_le_compat_r; assumption).
  split; [split; [exact Oklo | split; [exact Okhi | lra]] |].
  split; [reflexivity | split; [reflexivity |]].
  intros x Hx.
  assert (la / IZR k <= x / IZR k)%R by (apply Rmult_le_compat_r; [exact K | apply Hx]).
  assert (x / IZR k <= ha / IZR k)%R by (apply Rmult_le_compat_r; [exact K | apply Hx]).
  lra.
Qed.

Lemma encl_shl_correct :
  forall n a k,
  level_ok n -> encl_ok n a -> encl_small a -> - 2 ^ 62 <= k <= 2 ^ 62 ->
  exists c,
  Dyadic.encl_shl n a k = Some c /\ encl_ok n c /\
  lo_R c = (lo_R a * bpow radix2 k)%R /\ hi_R c = (hi_R a * bpow radix2 k)%R /\
  forall x, encl_has a x -> encl_has c (x * bpow radix2 k).
Proof.
  intros n a k Hn (Hla & Hha & Ha) (Sla & Sha) Hk.
  unfold exp_small in Sla, Sha.
  destruct (shl_correct n _ k Hn Hla) as (lo & Elo & Oklo & Vlo); [lia|].
  destruct (shl_correct n _ k Hn Hha) as (hi & Ehi & Okhi & Vhi); [lia|].
  unfold Dyadic.encl_shl. rewrite Elo, Ehi. cbv beta iota.
  eexists. split; [reflexivity|].
  unfold encl_ok, encl_has, lo_R, hi_R in *; cbn [Dyadic.en_lo Dyadic.en_hi].
  rewrite Vlo, Vhi.
  pose proof (bpow_gt_0 radix2 k) as K.
  set (la := Dyadic.dy_R (Dyadic.en_lo a)) in *. set (ha := Dyadic.dy_R (Dyadic.en_hi a)) in *.
  assert (la * bpow radix2 k <= ha * bpow radix2 k)%R by (apply Rmult_le_compat_r; lra).
  split; [split; [exact Oklo | split; [exact Okhi | lra]] |].
  split; [reflexivity | split; [reflexivity |]].
  intros x Hx.
  assert (la * bpow radix2 k <= x * bpow radix2 k)%R by (apply Rmult_le_compat_r; lra).
  assert (x * bpow radix2 k <= ha * bpow radix2 k)%R by (apply Rmult_le_compat_r; lra).
  lra.
Qed.

(** ** Widths: an operation on enclosures adds at most its rounding,
    relative to the extreme exact results, to the widths of its operands
    ([encl_round_width]). *)

Lemma encl_add_width :
  forall n a b c,
  level_ok n -> encl_ok n a -> encl_ok n b -> encl_small a -> encl_small b ->
  Dyadic.encl_add n a b = Some c ->
  (hi_R c - lo_R c <=
   (hi_R a - lo_R a) + (hi_R b - lo_R b)
   + (Rabs (lo_R a + lo_R b) + Rabs (hi_R a + hi_R b)) * bpow radix2 (1 - dprec n))%R.
Proof.
  intros n a b c Hn Ha Hb Sa Sb E.
  destruct (encl_add_correct n a b Hn Ha Hb Sa Sb) as (c' & E' & _ & Vlo & Vhi & _).
  rewrite E in E'. injection E' as <-.
  rewrite Vlo, Vhi.
  destruct Ha as (_ & _ & Ha). destruct Hb as (_ & _ & Hb).
  pose proof (encl_round_width n (lo_R a + lo_R b) (hi_R a + hi_R b) Hn) as W.
  unfold lo_R, hi_R in *. lra.
Qed.

Lemma encl_sub_width :
  forall n a b c,
  level_ok n -> encl_ok n a -> encl_ok n b -> encl_small a -> encl_small b ->
  Dyadic.encl_sub n a b = Some c ->
  (hi_R c - lo_R c <=
   (hi_R a - lo_R a) + (hi_R b - lo_R b)
   + (Rabs (lo_R a - hi_R b) + Rabs (hi_R a - lo_R b)) * bpow radix2 (1 - dprec n))%R.
Proof.
  intros n a b c Hn Ha Hb Sa Sb E.
  destruct (encl_sub_correct n a b Hn Ha Hb Sa Sb) as (c' & E' & _ & Vlo & Vhi & _).
  rewrite E in E'. injection E' as <-.
  rewrite Vlo, Vhi.
  destruct Ha as (_ & _ & Ha). destruct Hb as (_ & _ & Hb).
  pose proof (encl_round_width n (lo_R a - hi_R b) (hi_R a - lo_R b) Hn) as W.
  unfold lo_R, hi_R in *. lra.
Qed.

(** ** Ziv's strategy *)

(** A finite [v] that rounds [r] as [rnd] says is what [mpfr_round]
    asks of [with_val v]. *)
Lemma finite_mpfr_round :
  forall rnd r (v : f64),
  is_finite v = true -> MpfrRound.rnd_pt f64_format rnd r (B2R v) ->
  mpfr_round f64_format rnd r (with_val v).
Proof.
  intros rnd r v Fv H.
  destruct (MpfrIdeal.with_val_finite_cases v Fv) as [(s & E & Z) | (E & NZ)];
    rewrite E; destruct rnd; cbn [mpfr_round MpfrRound.rnd_pt] in *.
  - rewrite <- Z. exact H.
  - rewrite <- Z. exact H.
  - split; assumption.
  - split; assumption.
Qed.

(** An element of [F] that rounds both ends of [[r1, r2]] in the same
    direction rounds every point of it. *)
Lemma rnd_between :
  forall (F : R -> Prop) rnd r1 r2 r y,
  (r1 <= r <= r2)%R -> MpfrRound.rnd_pt F rnd r1 y -> MpfrRound.rnd_pt F rnd r2 y ->
  MpfrRound.rnd_pt F rnd r y.
Proof.
  intros F rnd r1 r2 r y Hr H1 H2.
  destruct rnd; cbn [MpfrRound.rnd_pt] in *.
  - destruct H1 as (Fy & Hy1 & _). destruct H2 as (_ & _ & H2).
    split; [exact Fy | split; [lra |]].
    intros g Fg Hg. apply H2; [exact Fg | lra].
  - destruct H1 as (_ & _ & H1). destruct H2 as (Fy & Hy2 & _).
    split; [exact Fy | split; [lra |]].
    intros g Fg Hg. apply H1; [exact Fg | lra].
Qed.

(** [eq] of two [f64]s that are not NaN: the same real, or the same
    infinity. *)
Lemma beqb_cases :
  forall v1 v2 : f64,
  Model.eq v1 v2 = true ->
  (is_finite v1 = true /\ is_finite v2 = true /\ B2R v1 = B2R v2) \/
  (exists s, v1 = B754_infinity s /\ v2 = B754_infinity s).
Proof.
  intros v1 v2 E.
  destruct (is_finite v1) eqn:F1; destruct (is_finite v2) eqn:F2.
  - left. split; [reflexivity | split; [reflexivity |]].
    unfold Model.eq in E. rewrite Beqb_correct in E by assumption.
    destruct (Req_bool_spec (B2R v1) (B2R v2)); [assumption | discriminate].
  - destruct v1 as [s1|s1| |s1 m1 e1 H1]; try discriminate F1;
      destruct v2 as [s2|s2| |s2 m2 e2 H2]; try discriminate F2;
      try (destruct s1); try (destruct s2); cbv in E; discriminate E.
  - destruct v1 as [s1|s1| |s1 m1 e1 H1]; try discriminate F1;
      destruct v2 as [s2|s2| |s2 m2 e2 H2]; try discriminate F2;
      try (destruct s1); try (destruct s2); cbv in E; discriminate E.
  - destruct v1 as [s1|s1| |s1 m1 e1 H1]; try discriminate F1;
      destruct v2 as [s2|s2| |s2 m2 e2 H2]; try discriminate F2;
      try (destruct s1); try (destruct s2); cbv in E; try discriminate E;
      right; eexists; split; reflexivity.
Qed.

(** The rounding test: if both ends of [[r1, r2]] round to [f64]s that
    [eq] says are equal, every point of it rounds to the first. *)
Lemma round_between :
  forall rnd r1 r2 r v1 v2,
  (r1 <= r <= r2)%R ->
  mpfr_round f64_format rnd r1 (with_val v1) ->
  mpfr_round f64_format rnd r2 (with_val v2) ->
  Model.eq v1 v2 = true -> mpfr_round f64_format rnd r (with_val v1).
Proof.
  intros rnd r1 r2 r v1 v2 Hr R1 R2 E.
  destruct (beqb_cases v1 v2 E) as [(F1 & F2 & Q) | (s & -> & ->)].
  - apply finite_mpfr_round; [exact F1|].
    apply rnd_between with r1 r2; [exact Hr | |].
    + apply MpfrRound.round_finite_pt; assumption.
    + rewrite Q. apply MpfrRound.round_finite_pt; assumption.
  - destruct rnd, s; cbn [with_val mpfr_round] in R1, R2 |- *; try contradiction.
    + intros g Fg. specialize (R2 g Fg). lra.
    + intros g Fg. specialize (R1 g Fg). lra.
Qed.

(** The level of the levels list that returns. *)
Lemma ziv_levels_some :
  forall ev up start levels v,
  Dyadic.ziv_levels ev up start levels = Some v ->
  exists n, In n levels /\ Dyadic.ziv_at ev n up = Some (Some v).
Proof.
  intros ev up start levels v. induction levels as [|n ls IH]; cbn [Dyadic.ziv_levels].
  - discriminate.
  - destruct (start <=? n)%nat.
    + destruct (Dyadic.ziv_at ev n up) as [[x|]|] eqn:E.
      * intros H. injection H as <-. exists n. split; [left; reflexivity | exact E].
      * intros H. destruct (IH H) as (m & Hm & Em). exists m. split; [right; exact Hm | exact Em].
      * discriminate.
    + intros H. destruct (IH H) as (m & Hm & Em). exists m. split; [right; exact Hm | exact Em].
Qed.

(** Rounding [x] and rounding [r] give the same result if no element of
    [F] lies between them. *)
Lemma round_transfer :
  forall (F : R -> Prop) rnd x r m,
  (forall g, F g -> (Rmin x r <= g <= Rmax x r)%R -> False) ->
  mpfr_round F rnd x m -> mpfr_round F rnd r m.
Proof.
  intros F rnd x r m Hno H.
  pose proof (Rmin_l x r). pose proof (Rmin_r x r).
  pose proof (Rmax_l x r). pose proof (Rmax_r x r).
  assert (DN : forall y, Rnd_DN_pt F x y -> Rnd_DN_pt F r y).
  { intros y (Fy & Hyx & Hmax). split; [exact Fy | split].
    - destruct (Rle_dec y r) as [|Hlt]; [assumption|].
      exfalso. apply (Hno y Fy). lra.
    - intros g Fg Hgr. destruct (Rle_dec g x) as [Hgx|Hgx]; [exact (Hmax g Fg Hgx)|].
      exfalso. apply (Hno g Fg). lra. }
  assert (UP : forall y, Rnd_UP_pt F x y -> Rnd_UP_pt F r y).
  { intros y (Fy & Hxy & Hmin). split; [exact Fy | split].
    - destruct (Rle_dec r y) as [|Hlt]; [assumption|].
      exfalso. apply (Hno y Fy). lra.
    - intros g Fg Hrg. destruct (Rle_dec x g) as [Hxg|Hxg]; [exact (Hmin g Fg Hxg)|].
      exfalso. apply (Hno g Fg). lra. }
  destruct rnd, m as [|[]|s|y]; cbn [mpfr_round] in H |- *; try contradiction.
  - intros g Fg. destruct (Rlt_dec r g) as [|Hge]; [assumption|].
    exfalso. apply (Hno g Fg). specialize (H g Fg). lra.
  - apply DN. exact H.
  - split; [apply H | apply DN, H].
  - intros g Fg. destruct (Rlt_dec g r) as [|Hge]; [assumption|].
    exfalso. apply (Hno g Fg). specialize (H g Fg). lra.
  - apply UP. exact H.
  - split; [apply H | apply UP, H].
Qed.

(** Two [f64]s that round the same real in the same direction pass the
    rounding test. *)
Lemma round_same :
  forall rnd r v1 v2,
  mpfr_round f64_format rnd r (with_val v1) -> mpfr_round f64_format rnd r (with_val v2) ->
  Model.eq v1 v2 = true.
Proof.
  intros rnd r v1 v2 R1 R2.
  destruct (mpfr_round_unique _ _ _ _ _ R1 R2) as [E | (s & s' & E1 & E2)].
  - apply with_val_inj in E. subst v2. unfold Model.eq. rewrite Beqb_refl.
    destruct v1; try reflexivity. destruct rnd; contradiction R1.
  - destruct v1; try discriminate E1. destruct v2; try discriminate E2.
    destruct s0, s1; reflexivity.
Qed.

(** A real that is not a finite [f64] is at a positive distance from all
    of them: from the neighbours that round it down and up in [G] if it is
    below [2^1024] in magnitude, and from the largest finite [f64] if
    not. *)
Lemma f64_gap :
  forall r,
  ~ f64_format r ->
  exists d, (0 < d)%R /\ forall g, f64_format g -> (d <= Rabs (g - r))%R.
Proof.
  intros r Hr.
  destruct (Rlt_dec (Rabs r) (bpow radix2 1024)) as [Hs|Hb].
  - assert (HG : ~ G r) by (intros HG; exact (Hr (f64_format_G_lt r HG Hs))).
    pose proof (@round_DN_pt radix2 (SpecFloat.fexp 53 1024) _ r) as (Ga & Har & Hamax).
    pose proof (@round_UP_pt radix2 (SpecFloat.fexp 53 1024) _ r) as (Gb & Hrb & Hbmin).
    set (a := round radix2 (SpecFloat.fexp 53 1024) Zfloor r) in *.
    set (b := round radix2 (SpecFloat.fexp 53 1024) Zceil r) in *.
    assert (a <> r) by (intros E; apply HG; rewrite <- E; exact Ga).
    assert (b <> r) by (intros E; apply HG; rewrite <- E; exact Gb).
    exists (Rmin (r - a) (b - r)). split; [apply Rmin_glb_lt; lra|].
    intros g Fg. destruct (f64_format_G g Fg) as [Gg _].
    pose proof (Rmin_l (r - a) (b - r)). pose proof (Rmin_r (r - a) (b - r)).
    destruct (Rle_dec g r) as [Hgr|Hgr].
    + pose proof (Hamax g Gg Hgr). unfold Rabs. destruct Rcase_abs; lra.
    + pose proof (Hbmin g Gg (Rlt_le _ _ (Rnot_le_lt _ _ Hgr))).
      unfold Rabs. destruct Rcase_abs; lra.
  - exists (bpow radix2 971). split; [apply bpow_gt_0|].
    intros g Fg. destruct (f64_format_G g Fg) as [Gg Hg].
    apply Rabs_def2 in Hg. destruct Hg as [Hg1 Hg2].
    pose proof (G_le_max g Gg Hg1) as M1.
    pose proof (G_le_max (- g) (generic_format_opp _ _ _ Gg) ltac:(lra)) as M2.
    revert Hb. unfold Rabs. destruct (Rcase_abs r); destruct (Rcase_abs (g - r)); intros; lra.
Qed.

(** No element of [F] lies between [x] and [r] if [x] is nearer to [r]
    than all of them. *)
Lemma gap_interval :
  forall (F : R -> Prop) d r x,
  (forall g, F g -> (d <= Rabs (g - r))%R) -> (Rabs (x - r) < d)%R ->
  forall g, F g -> (Rmin x r <= g <= Rmax x r)%R -> False.
Proof.
  intros F d r x Hgap Hx g Fg Hg. specialize (Hgap g Fg).
  revert Hgap Hx Hg. unfold Rmin, Rmax, Rabs.
  destruct (Rle_dec x r); destruct (Rcase_abs (g - r)); destruct (Rcase_abs (x - r)); intros; lra.
Qed.

(** The driver lemma: partial correctness. *)
Lemma ziv_correct :
  forall ev up start r v,
  (forall n a, level_ok n -> ev n = Some a -> encl_ok n a /\ encl_has a r) ->
  Dyadic.ziv ev up start = Some v ->
  mpfr_round f64_format (if up then RNDU else RNDD) r (with_val v).
Proof.
  intros ev up start r v Hev Hz. unfold Dyadic.ziv in Hz.
  destruct (ziv_levels_some _ _ _ _ _ Hz) as (n & Hin & E).
  assert (Hn : level_ok n).
  { unfold level_ok. cbn [In] in Hin.
    repeat (destruct Hin as [<-|Hin]; [lia|]). destruct Hin. }
  unfold Dyadic.ziv_at in E.
  destruct (ev n) as [x|] eqn:Ex; [|discriminate].
  destruct (Hev n x Hn Ex) as ((Hlo & Hhi & _) & Hr).
  destruct (to_f64_correct n (Dyadic.en_lo x) up Hn Hlo) as (v1 & E1 & R1).
  destruct (to_f64_correct n (Dyadic.en_hi x) up Hn Hhi) as (v2 & E2 & R2).
  rewrite E1, E2 in E. cbv beta iota in E.
  destruct (Model.eq v1 v2) eqn:Q; [|discriminate]. injection E as <-.
  exact (round_between _ _ _ _ _ _ Hr R1 R2 Q).
Qed.

(** The termination lemma: a real number that is not a finite [f64],
    such as one beyond [MAX], passes the rounding test in both directions
    at every level at which its enclosure is narrower than a width that
    depends only on the number. *)
Lemma ziv_at_passes :
  forall r,
  ~ f64_format r ->
  exists delta,
  (0 < delta)%R /\
  forall n up ev a,
  level_ok n -> ev n = Some a -> encl_ok n a -> encl_has a r -> (hi_R a - lo_R a < delta)%R ->
  exists v, Dyadic.ziv_at ev n up = Some (Some v).
Proof.
  intros r Hr.
  destruct (f64_gap r Hr) as (d & Hd & Hgap).
  exists d. split; [exact Hd|].
  intros n up ev a Hn Ea (Hlo & Hhi & Hle) (Hr1 & Hr2) Hw.
  unfold lo_R, hi_R in Hw.
  destruct (to_f64_correct n (Dyadic.en_lo a) up Hn Hlo) as (v1 & E1 & R1).
  destruct (to_f64_correct n (Dyadic.en_hi a) up Hn Hhi) as (v2 & E2 & R2).
  unfold Dyadic.ziv_at. rewrite Ea, E1, E2. cbv beta iota.
  apply round_transfer with (r := r) in R1;
    [| apply gap_interval with d; [exact Hgap | unfold Rabs; destruct Rcase_abs; lra]].
  apply round_transfer with (r := r) in R2;
    [| apply gap_interval with d; [exact Hgap | unfold Rabs; destruct Rcase_abs; lra]].
  rewrite (round_same _ _ _ _ R1 R2). eexists. reflexivity.
Qed.
