(** * Outward fields give wider intervals: the monotone functions

    For a record [p] whose field of [f] is outward of that of a record
    [q] ([fld_out] of [SideDefs.v]), the interval function of [f]
    returns for [p] an interval wider than for [q] ([wider]), at every
    argument. These are the functions whose bounds are fields at the
    bounds of the argument, or constants: [exp], [exp2], [exp10],
    [sinh], [tanh], [asinh], [atan] ([mono_inc]), [ln], [log2], [log10]
    ([log_impl]), [acosh], [atanh], [asin], [acos] and [cosh].
    [SideMonoB.v] does [pow], [powi], [atan2], [sin], [cos] and [tan]
    with [wir_wider], [fmin_out] and [fmax_out] below. *)

From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Mpfr SideDefs.

Open Scope R_scope.

(** Comparisons of [f64]s with [Bleb] and [Bltb]. *)

Lemma bleb_not_nan :
  forall x y : f64, Bleb x y = true -> is_nan x = false /\ is_nan y = false.
Proof.
intros [sx|[|]| |sx mx ex Hx] [sy|[|]| |sy my ey Hy] H;
  try (cbn in H; discriminate H); split; reflexivity.
Qed.

Lemma bleb_refl : forall x : f64, is_nan x = false -> Bleb x x = true.
Proof.
intros [sx|[|]| |sx mx ex Hx] N; try discriminate N; try reflexivity;
  rewrite Bleb_correct by reflexivity; apply Rle_bool_true, Rle_refl.
Qed.

(** [Bleb x y] on floats that are not NaN: [x] is -inf, [y] is +inf, or
    both are finite and in order as reals. *)
Lemma bleb_ext :
  forall x y : f64, Bleb x y = true ->
  x = B754_infinity true \/ y = B754_infinity false \/
  (is_finite x = true /\ is_finite y = true /\ B2R x <= B2R y).
Proof.
intros [sx|[|]| |sx mx ex Hx] [sy|[|]| |sy my ey Hy] H;
  try (cbn in H; discriminate H); try (left; reflexivity);
  try (right; left; reflexivity);
  right; right; (split; [reflexivity | split; [reflexivity |]]);
  rewrite Bleb_correct in H by reflexivity;
  revert H; (case Rle_bool_spec; [intros Hv _; exact Hv | discriminate]).
Qed.

(** The converse of [bleb_ext]. *)
Lemma bleb_of :
  forall x y : f64, is_nan x = false -> is_nan y = false ->
  x = B754_infinity true \/ y = B754_infinity false \/
  (is_finite x = true /\ is_finite y = true /\ B2R x <= B2R y) ->
  Bleb x y = true.
Proof.
intros x y Nx Ny [E | [E | (Fx & Fy & L)]].
- subst x. destruct y as [sy|[|]| |sy my ey Hy]; try discriminate Ny; reflexivity.
- subst y. destruct x as [sx|[|]| |sx mx ex Hx]; try discriminate Nx; reflexivity.
- rewrite Bleb_correct by assumption. apply Rle_bool_true, L.
Qed.

Lemma bleb_trans :
  forall x y z : f64, Bleb x y = true -> Bleb y z = true -> Bleb x z = true.
Proof.
intros x y z H1 H2.
destruct (bleb_not_nan x y H1) as [Nx _].
destruct (bleb_not_nan y z H2) as [_ Nz].
apply bleb_of; [exact Nx | exact Nz |].
destruct (bleb_ext x y H1) as [E1 | [E1 | (Fx & Fy & L1)]];
  destruct (bleb_ext y z H2) as [E2 | [E2 | (Fy' & Fz & L2)]];
  try (left; exact E1); try (right; left; exact E2); try (subst y; discriminate).
right; right. split; [exact Fx | split; [exact Fz | lra]].
Qed.

Lemma bltb_bleb : forall x y : f64, Bltb x y = true -> Bleb x y = true.
Proof.
intros x y. unfold Bltb, Bleb, SpecFloat.SFltb, SpecFloat.SFleb.
destruct (SpecFloat.SFcompare _ _) as [[| |]|]; easy.
Qed.

(** [Bltb x y = false] on floats that are not NaN: [y <= x]. *)
Lemma bltb_false_bleb :
  forall x y : f64, is_nan x = false -> is_nan y = false ->
  Bltb x y = false -> Bleb y x = true.
Proof.
intros x y Nx Ny H.
unfold Bltb, SpecFloat.SFltb in H. unfold Bleb, SpecFloat.SFleb.
change (SpecFloat.SFcompare (B2SF x) (B2SF y)) with (Bcompare x y) in H.
change (SpecFloat.SFcompare (B2SF y) (B2SF x)) with (Bcompare y x).
rewrite (Bcompare_swap 53 1024 x y).
destruct (Bcompare x y) as [[| |]|] eqn:E; try reflexivity; try discriminate H.
destruct x as [sx|[|]| |sx mx ex Hx]; try discriminate Nx;
  destruct y as [sy|[|]| |sy my ey Hy]; try discriminate Ny; cbn in E; discriminate E.
Qed.

(** NaN compares as neither smaller nor larger. *)
Lemma bltb_nan_l : forall y : f64, Bltb B754_nan y = false.
Proof. reflexivity. Qed.

Lemma bltb_nan_r : forall x : f64, Bltb x B754_nan = false.
Proof. intros [sx|[|]| |sx mx ex Hx]; reflexivity. Qed.

Lemma nan_eq : forall x : f64, is_nan x = true -> x = B754_nan.
Proof. intros [sx|[|]| |sx mx ex Hx] N; try discriminate N; reflexivity. Qed.

(** A bound outward of one that is not NaN, as [Bleb]. *)
Lemma out_dn :
  forall a' a, outward RNDD a' a -> is_nan a = false -> Bleb a' a = true.
Proof.
intros a' a [E | L] N; [subst a'; apply bleb_refl, N | exact L].
Qed.

Lemma out_up :
  forall b' b, outward RNDU b' b -> is_nan b = false -> Bleb b b' = true.
Proof.
intros b' b [E | L] N; [subst b'; apply bleb_refl, N | exact L].
Qed.

(** A bound outward of NaN is NaN. *)
Lemma out_nan :
  forall rnd a' a, outward rnd a' a -> is_nan a = true -> a' = a.
Proof.
intros rnd a' a [E | L] N; [exact E |].
destruct rnd;
  [destruct (bleb_not_nan _ _ L) as [_ M] | destruct (bleb_not_nan _ _ L) as [M _]];
  congruence.
Qed.

(** [fmin] and [fmax] of floats that are not NaN, in [Bleb] order. *)
Lemma fmin_le :
  forall (first : bool) (x y : f64), is_nan x = false -> is_nan y = false ->
  Bleb (fmin first x y) x = true /\ Bleb (fmin first x y) y = true.
Proof.
intros first x y Nx Ny. unfold fmin, lt.
destruct (Bltb x y) eqn:E1; [split; [apply bleb_refl, Nx | apply bltb_bleb, E1] |].
destruct (Bltb y x) eqn:E2; [split; [apply bltb_bleb, E2 | apply bleb_refl, Ny] |].
destruct first; split.
- apply bleb_refl, Nx.
- apply (bltb_false_bleb y x Ny Nx E2).
- apply (bltb_false_bleb x y Nx Ny E1).
- apply bleb_refl, Ny.
Qed.

Lemma fmax_ge :
  forall (first : bool) (x y : f64), is_nan x = false -> is_nan y = false ->
  Bleb x (fmax first x y) = true /\ Bleb y (fmax first x y) = true.
Proof.
intros first x y Nx Ny. unfold fmax, lt.
destruct (Bltb x y) eqn:E1; [split; [apply bltb_bleb, E1 | apply bleb_refl, Ny] |].
destruct (Bltb y x) eqn:E2; [split; [apply bleb_refl, Nx | apply bltb_bleb, E2] |].
destruct first; split.
- apply bleb_refl, Nx.
- apply (bltb_false_bleb x y Nx Ny E1).
- apply (bltb_false_bleb y x Ny Nx E2).
- apply bleb_refl, Ny.
Qed.

Lemma fmin_cases : forall first x y, fmin first x y = x \/ fmin first x y = y.
Proof.
intros first x y. unfold fmin.
destruct (lt x y); [left; reflexivity |].
destruct (lt y x); [right; reflexivity |].
destruct first; [left | right]; reflexivity.
Qed.

Lemma fmax_cases : forall first x y, fmax first x y = x \/ fmax first x y = y.
Proof.
intros first x y. unfold fmax.
destruct (lt x y); [right; reflexivity |].
destruct (lt y x); [left; reflexivity |].
destruct first; [left | right]; reflexivity.
Qed.

(** An interval whose bounds are outward of those of another is wider. *)
Lemma wir_wider :
  forall a b a' b',
  outward RNDD a' a -> outward RNDU b' b ->
  wider (Interval.with_infsup_raw a' b') (Interval.with_infsup_raw a b).
Proof.
intros a b a' b' Ha Hb.
unfold wider, valid, mem, Interval.with_infsup_raw, Generic.constant, opp.
cbn [rep fst snd]. rewrite !Bopp_involutive, !is_nan_Bopp.
split.
- intros [[Na Nb] | (Hab & Hai & Hbi)].
  + left. rewrite (out_nan _ _ _ Ha Na), (out_nan _ _ _ Hb Nb). split; assumption.
  + right. destruct (bleb_not_nan _ _ Hab) as [Na Nb].
    pose proof (out_dn _ _ Ha Na) as La. pose proof (out_up _ _ Hb Nb) as Lb.
    split; [| split].
    * exact (bleb_trans _ _ _ La (bleb_trans _ _ _ Hab Lb)).
    * intros E. subst a'.
      destruct (bleb_ext _ _ La) as [E | [E | (F & _)]]; try discriminate.
      exact (Hai E).
    * intros E. subst b'.
      destruct (bleb_ext _ _ Lb) as [E | [E | (_ & F & _)]]; try discriminate.
      exact (Hbi E).
- intros r [Lr Ur]. split.
  + destruct Ha as [E | La]; [subst a'; exact Lr |].
    destruct (bleb_ext _ _ La) as [E | [E | (Fa' & Fa & L)]].
    * subst a'. reflexivity.
    * subst a. discriminate Lr.
    * destruct a' as [sa'|sa'| |sa' ma' ea' Ha']; try discriminate Fa';
        destruct a as [sa|sa| |sa ma ea Ha0]; try discriminate Fa; lra.
  + destruct Hb as [E | Lb]; [subst b'; exact Ur |].
    destruct (bleb_ext _ _ Lb) as [E | [E | (Fb & Fb' & L)]].
    * subst b. discriminate Ur.
    * subst b'. reflexivity.
    * destruct b' as [sb'|sb'| |sb' mb' eb' Hb']; try discriminate Fb';
        destruct b as [sb|sb| |sb mb eb Hb0]; try discriminate Fb; lra.
Qed.

(** [fmin] and [fmax] keep bounds outward. *)
Lemma fmin_out :
  forall first a b a' b',
  outward RNDD a' a -> outward RNDD b' b -> outward RNDD (fmin first a' b') (fmin first a b).
Proof.
intros first a b a' b' Ha Hb.
destruct (is_nan a) eqn:Na.
{ rewrite (out_nan _ _ _ Ha Na), (nan_eq a Na). unfold fmin, lt.
  rewrite !bltb_nan_l, !bltb_nan_r. destruct first; [left; reflexivity | exact Hb]. }
destruct (is_nan b) eqn:Nb.
{ rewrite (out_nan _ _ _ Hb Nb), (nan_eq b Nb). unfold fmin, lt.
  rewrite !bltb_nan_l, !bltb_nan_r. destruct first; [exact Ha | left; reflexivity]. }
pose proof (out_dn _ _ Ha Na) as La. pose proof (out_dn _ _ Hb Nb) as Lb.
destruct (bleb_not_nan _ _ La) as [Na' _]. destruct (bleb_not_nan _ _ Lb) as [Nb' _].
destruct (fmin_le first a' b' Na' Nb') as [M1 M2].
right. unfold Model.le.
destruct (fmin_cases first a b) as [E | E]; rewrite E.
- exact (bleb_trans _ _ _ M1 La).
- exact (bleb_trans _ _ _ M2 Lb).
Qed.

Lemma fmax_out :
  forall first a b a' b',
  outward RNDU a' a -> outward RNDU b' b -> outward RNDU (fmax first a' b') (fmax first a b).
Proof.
intros first a b a' b' Ha Hb.
destruct (is_nan a) eqn:Na.
{ rewrite (out_nan _ _ _ Ha Na), (nan_eq a Na). unfold fmax, lt.
  rewrite !bltb_nan_l, !bltb_nan_r. destruct first; [left; reflexivity | exact Hb]. }
destruct (is_nan b) eqn:Nb.
{ rewrite (out_nan _ _ _ Hb Nb), (nan_eq b Nb). unfold fmax, lt.
  rewrite !bltb_nan_l, !bltb_nan_r. destruct first; [exact Ha | left; reflexivity]. }
pose proof (out_up _ _ Ha Na) as La. pose proof (out_up _ _ Hb Nb) as Lb.
destruct (bleb_not_nan _ _ La) as [_ Na']. destruct (bleb_not_nan _ _ Lb) as [_ Nb'].
destruct (fmax_ge first a' b' Na' Nb') as [M1 M2].
right. unfold Model.le.
destruct (fmax_cases first a b) as [E | E]; rewrite E.
- exact (bleb_trans _ _ _ La M1).
- exact (bleb_trans _ _ _ Lb M2).
Qed.

(** The proofs follow the code, as in [SideMonoB.v]: [mono_split p q]
    splits the goal on every [if] and pair [match] whose scrutinee reads
    neither record [p] nor [q], so that both sides take the same branch.
    The leaves are then intervals that do not read the record
    ([wider_refl]), or whose bounds are fields or constants
    ([wir_wider]). *)

Ltac mono_reads_no p q c :=
  lazymatch c with
  | context [p] => fail
  | context [q] => fail
  | _ => idtac
  end.

Ltac mono_split p q :=
  repeat (cbv beta iota zeta delta [fst];
    match goal with
    | |- context [if ?c then _ else _] => mono_reads_no p q c; destruct c
    | |- context [match ?c with (_, _) => _ end] => mono_reads_no p q c; destruct c
    end).

(** A bound of the [p] side outward of the bound of the [q] side: a
    field, or a constant that both sides share. *)
Ltac mono_bound H :=
  lazymatch goal with
  | |- outward _ ?v ?v => left; reflexivity
  | |- _ => apply H
  end.

Ltac mono_leaf H :=
  lazymatch goal with
  | |- wider ?y ?y => apply wider_refl
  | |- wider (Interval.with_infsup_raw _ _) (Interval.with_infsup_raw _ _) =>
      apply wir_wider; mono_bound H
  end.

Lemma exp_wider :
  forall p q, fld_out (p_exp p) (p_exp q) ->
  forall x, wider (Interval.exp p x) (Interval.exp q x).
Proof.
intros p q H x. unfold fld_out in H.
unfold Interval.exp, Interval.mono_inc.
mono_split p q.
all: mono_leaf H.
Qed.

Lemma exp2_wider :
  forall p q, fld_out (p_exp2 p) (p_exp2 q) ->
  forall x, wider (Interval.exp2 p x) (Interval.exp2 q x).
Proof.
intros p q H x. unfold fld_out in H.
unfold Interval.exp2, Interval.mono_inc.
mono_split p q.
all: mono_leaf H.
Qed.

Lemma exp10_wider :
  forall p q, fld_out (p_exp10 p) (p_exp10 q) ->
  forall x, wider (Interval.exp10 p x) (Interval.exp10 q x).
Proof.
intros p q H x. unfold fld_out in H.
unfold Interval.exp10, Interval.mono_inc.
mono_split p q.
all: mono_leaf H.
Qed.

Lemma sinh_wider :
  forall p q, fld_out (p_sinh p) (p_sinh q) ->
  forall x, wider (Interval.sinh p x) (Interval.sinh q x).
Proof.
intros p q H x. unfold fld_out in H.
unfold Interval.sinh, Interval.mono_inc.
mono_split p q.
all: mono_leaf H.
Qed.

Lemma tanh_wider :
  forall p q, fld_out (p_tanh p) (p_tanh q) ->
  forall x, wider (Interval.tanh p x) (Interval.tanh q x).
Proof.
intros p q H x. unfold fld_out in H.
unfold Interval.tanh, Interval.mono_inc.
mono_split p q.
all: mono_leaf H.
Qed.

Lemma cosh_wider :
  forall p q, fld_out (p_cosh p) (p_cosh q) ->
  forall first x, wider (Interval.cosh p first x) (Interval.cosh q first x).
Proof.
intros p q H first x. unfold fld_out in H.
unfold Interval.cosh.
mono_split p q.
all: mono_leaf H.
Qed.

Lemma ln_wider :
  forall p q, fld_out (p_ln p) (p_ln q) ->
  forall x, wider (Interval.ln p x) (Interval.ln q x).
Proof.
intros p q H x. unfold fld_out in H.
unfold Interval.ln, Interval.ln_impl, Interval.log_impl.
mono_split p q.
all: mono_leaf H.
Qed.

Lemma log2_wider :
  forall p q, fld_out (p_log2 p) (p_log2 q) ->
  forall x, wider (Interval.log2 p x) (Interval.log2 q x).
Proof.
intros p q H x. unfold fld_out in H.
unfold Interval.log2, Interval.log2_impl, Interval.log_impl.
mono_split p q.
all: mono_leaf H.
Qed.

Lemma log10_wider :
  forall p q, fld_out (p_log10 p) (p_log10 q) ->
  forall x, wider (Interval.log10 p x) (Interval.log10 q x).
Proof.
intros p q H x. unfold fld_out in H.
unfold Interval.log10, Interval.log10_impl, Interval.log_impl.
mono_split p q.
all: mono_leaf H.
Qed.

Lemma asinh_wider :
  forall p q, fld_out (p_asinh p) (p_asinh q) ->
  forall x, wider (Interval.asinh p x) (Interval.asinh q x).
Proof.
intros p q H x. unfold fld_out in H.
unfold Interval.asinh, Interval.mono_inc.
mono_split p q.
all: mono_leaf H.
Qed.

Lemma acosh_wider :
  forall p q, fld_out (p_acosh p) (p_acosh q) ->
  forall x, wider (Interval.acosh p x) (Interval.acosh q x).
Proof.
intros p q H x. unfold fld_out in H.
unfold Interval.acosh, Interval.acosh_impl.
mono_split p q.
all: mono_leaf H.
Qed.

Lemma atanh_wider :
  forall p q, fld_out (p_atanh p) (p_atanh q) ->
  forall x, wider (Interval.atanh p x) (Interval.atanh q x).
Proof.
intros p q H x. unfold fld_out in H.
unfold Interval.atanh, Interval.atanh_impl.
mono_split p q.
all: mono_leaf H.
Qed.

Lemma atan_wider :
  forall p q, fld_out (p_atan p) (p_atan q) ->
  forall x, wider (Interval.atan p x) (Interval.atan q x).
Proof.
intros p q H x. unfold fld_out in H.
unfold Interval.atan, Interval.mono_inc.
mono_split p q.
all: mono_leaf H.
Qed.

Lemma asin_wider :
  forall p q, fld_out (p_asin p) (p_asin q) ->
  forall x, wider (Interval.asin p x) (Interval.asin q x).
Proof.
intros p q H x. unfold fld_out in H.
unfold Interval.asin, Interval.asin_impl.
mono_split p q.
all: mono_leaf H.
Qed.

Lemma acos_wider :
  forall p q, fld_out (p_acos p) (p_acos q) ->
  forall x, wider (Interval.acos p x) (Interval.acos q x).
Proof.
intros p q H x. unfold fld_out in H.
unfold Interval.acos, Interval.acos_impl.
mono_split p q.
all: mono_leaf H.
Qed.
