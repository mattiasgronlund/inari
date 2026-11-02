(** * [From<DecNInterval> for DecInterval] and [From<NInterval> for Interval]

    For a [DecNInterval] that the grammar can return ([dec_ninterval_ok]),
    [From<DecNInterval>] returns NaI for the decoration [ill], and
    otherwise the tightest interval that contains the reals that the
    literal denotes, with the literal's decoration, except [dac] in place
    of [com] when overflow occurred, that is, the literal is bounded and
    the result is not, as IEEE 1788's textToInterval asks
    ([from_dec_ninterval_correct]). For a [com] literal, that is exactly
    when the conversion of a bound overflowed. [From<NInterval>] returns
    the same interval for an [NInterval] with [ninterval_ok], and
    [from_ninterval_new] shows that [From<DecNInterval>] of
    [DecNInterval::new(x)] is [DecInterval::new] of it, for any MPFR.

    [dn_NAI_ok], [dn_new_ok] and [dn_decorated_ok] show that the step of
    the grammar that decorates a literal gives [dec_ninterval_ok] to what
    it returns for [[nai]], and for a literal whose [NInterval] has
    [ninterval_ok], without a decoration or with one. [dn_decorated_ok]
    also shows that a literal that it accepts keeps its decoration. *)

From Stdlib Require Import ZArith Reals Qreals Lra.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Mpfr MpfrRound ParseRound ParseHull
  Integer DecBinary ValidMake.

Open Scope R_scope.

(** ** The interval and the decoration that [set_dec] receives *)

(** The interval that [From<DecNInterval>] passes to [set_dec]:
    [Interval::try_from] of the rounded bounds, or [Interval::EMPTY]. *)
Definition parse_hull (m : mpfr) (n : NInterval) : Interval :=
  match Interval.try_from (f64_f (number_to_f64 m (ninf n) Inf))
                          (f64_f (number_to_f64 m (nsup n) Sup)) with
  | Some y => y
  | None => Interval.EMPTY
  end.

(** A bound of [n] overflowed. *)
Definition parse_overflow (m : mpfr) (n : NInterval) : bool :=
  f64_overflow (number_to_f64 m (ninf n) Inf) ||
  f64_overflow (number_to_f64 m (nsup n) Sup).

Lemma from_dec_ninterval_eq :
  forall m x,
  DecInterval.from_dec_ninterval m x =
  DecInterval.set_dec (parse_hull m (nx x))
    (if parse_overflow m (nx x) then dec_min (nd x) Dac else nd x).
Proof.
reflexivity.
Qed.

Lemma parse_hull_valid : forall m n, valid (parse_hull m n).
Proof.
intros m n. unfold parse_hull.
destruct (Interval.try_from (f64_f (number_to_f64 m (ninf n) Inf))
                            (f64_f (number_to_f64 m (nsup n) Sup)))
  as [y|] eqn:E.
- exact (try_from_valid _ _ y E).
- exact EMPTY_valid.
Qed.

Lemma parse_hull_empty :
  forall m n, Interval.is_empty (parse_hull m n) = true ->
  parse_hull m n = Interval.EMPTY.
Proof.
intros m n E. exact (valid_empty_eq _ (parse_hull_valid m n) E).
Qed.

(** [d.min(Decoration::Dac)] is [ill] only if [d] is. *)
Lemma dec_min_not_ill :
  forall (o : bool) d, dec_eqb d Ill = false ->
  dec_eqb (if o then dec_min d Dac else d) Ill = false.
Proof.
intros [|] d Hd; [|exact Hd].
destruct d; cbn in Hd |- *; easy.
Qed.

(** Unless the decoration is [ill], the result's interval is
    [parse_hull]: [set_dec] returns [EMPTY] only for an empty interval,
    which is [Interval::EMPTY]. *)
Lemma itv_from_dec :
  forall m x, dec_eqb (nd x) Ill = false ->
  itv (DecInterval.from_dec_ninterval m x) = parse_hull m (nx x).
Proof.
intros m x Hd. rewrite from_dec_ninterval_eq. unfold DecInterval.set_dec.
rewrite (dec_min_not_ill _ _ Hd).
destruct (Interval.is_empty (parse_hull m (nx x))) eqn:E.
- symmetry. exact (parse_hull_empty m (nx x) E).
- match goal with
  | |- context [if dec_eqb ?d Com && ?c then _ else _] =>
      destruct (dec_eqb d Com && c)
  end; reflexivity.
Qed.

(** ** Emptiness and commonness of [parse_hull] *)

(** A real of the literal is in the tightest interval, which is then not
    empty. *)
Lemma parse_hull_nonempty :
  forall m n, parse_ok m -> ninterval_ok n -> (exists r, ninterval_set n r) ->
  Interval.is_empty (parse_hull m n) = false.
Proof.
intros m n Hm Hok (r & Hr).
destruct (bounds_tightest m n Hm Hok) as (_ & Hin & _).
exact (mem_not_empty _ r (parse_hull_valid m n) (Hin r Hr)).
Qed.

(** If the literal holds no real, [Interval::EMPTY] contains it, so by
    tightness every member of [parse_hull] is in [Interval::EMPTY], which
    has none. *)
Lemma parse_hull_of_empty :
  forall m n, parse_ok m -> ninterval_ok n -> (forall r, ~ ninterval_set n r) ->
  parse_hull m n = Interval.EMPTY.
Proof.
intros m n Hm Hok Hno. apply parse_hull_empty.
apply (no_mem_empty _ (parse_hull_valid m n)). intros r Hr.
destruct (bounds_tightest m n Hm Hok) as (_ & _ & Hmin).
apply (mem_nan Interval.EMPTY r eq_refl).
apply (Hmin Interval.EMPTY EMPTY_valid); [|exact Hr].
intros r' Hr'. destruct (Hno r' Hr').
Qed.

(** [overflow] of a rational bound is [f.is_infinite()] of its [f]. *)
Lemma rational_overflow :
  forall m q s,
  f64_overflow (rational_to_f64 m q s) =
  f64_is_infinite (f64_f (rational_to_f64 m q s)).
Proof.
intros m q s. unfold rational_to_f64. cbv zeta.
destruct (mpfr_set_q _ _ _ _ _) as [f t]. cbv beta iota.
destruct (mpfr_subnormalize _ _ _ _ _ _) as [g u].
reflexivity.
Qed.

(** An overflowed bound is infinite, for any MPFR. *)
Lemma overflow_infinite :
  forall m n s, f64_overflow (number_to_f64 m n s) = true ->
  is_finite (f64_f (number_to_f64 m n s)) = false.
Proof.
intros m [|q|] s H; try discriminate H.
cbn [number_to_f64] in H |- *. rewrite rational_overflow in H. revert H.
destruct (f64_f (rational_to_f64 m q s)); cbn; intros H;
  first [discriminate H|reflexivity].
Qed.

(** [Interval::try_from] with a bound that is not finite gives an interval
    that is not common: it rejects a lower bound +inf and an upper bound
    -inf, and in the other cases the lane that holds that bound (the
    lower one negated) is +inf or NaN, which is not [< f64::INFINITY]. *)
Lemma try_from_infinite :
  forall a b y, Interval.try_from a b = Some y ->
  is_finite a = false \/ is_finite b = false ->
  Interval.is_common_interval y = false.
Proof.
intros a b y E Hab. unfold Interval.try_from in E.
match type of E with
| (if ?g then _ else _) = _ => destruct g eqn:G; [|discriminate E]
end.
injection E as <-.
rewrite is_common_interval_lt, infinity_eq.
unfold Interval.with_infsup_raw, Generic.constant. cbn [rep fst snd].
rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in G.
destruct G as [[_ Ha] Hb].
destruct Hab as [H|H].
- apply Bool.andb_false_iff. left.
  destruct a as [[|]|[|]| |sa ma ea Ea]; try discriminate H;
    cbn in Ha |- *; first [reflexivity|discriminate Ha].
- apply Bool.andb_false_iff. right.
  destruct b as [[|]|[|]| |sb mb eb Eb]; try discriminate H;
    cbn in Hb |- *; first [reflexivity|discriminate Hb].
Qed.

(** [Interval::try_from] with finite bounds gives a common interval. *)
Lemma try_from_finite :
  forall a b y, Interval.try_from a b = Some y ->
  is_finite a = true -> is_finite b = true ->
  Interval.is_common_interval y = true.
Proof.
intros a b y E Ha Hb. unfold Interval.try_from in E.
match type of E with
| (if ?g then _ else _) = _ => destruct g; [|discriminate E]
end.
injection E as <-.
apply finite_common; unfold Interval.with_infsup_raw, Generic.constant;
  cbn [rep fst snd]; unfold opp; rewrite ?is_finite_Bopp; assumption.
Qed.

Lemma parse_hull_infinite :
  forall m n,
  is_finite (f64_f (number_to_f64 m (ninf n) Inf)) = false \/
  is_finite (f64_f (number_to_f64 m (nsup n) Sup)) = false ->
  Interval.is_common_interval (parse_hull m n) = false.
Proof.
intros m n H. unfold parse_hull.
destruct (Interval.try_from (f64_f (number_to_f64 m (ninf n) Inf))
                            (f64_f (number_to_f64 m (nsup n) Sup)))
  as [y|] eqn:E.
- exact (try_from_infinite _ _ y E H).
- rewrite is_common_interval_lt, infinity_eq. reflexivity.
Qed.

(** When a bound overflowed, [parse_hull] is not common, for any MPFR. *)
Lemma overflow_not_common :
  forall m n, parse_overflow m n = true ->
  Interval.is_common_interval (parse_hull m n) = false.
Proof.
intros m n H. apply parse_hull_infinite. unfold parse_overflow in H.
apply Bool.orb_true_iff in H.
destruct H as [H|H]; [left|right]; exact (overflow_infinite _ _ _ H).
Qed.

(** A literal that is not common has a bound [NegInfinity] or [Infinity],
    which [number_to_f64] returns as an infinity. *)
Lemma not_common_infinite :
  forall m n, nis_common_interval n = false ->
  is_finite (f64_f (number_to_f64 m (ninf n) Inf)) = false \/
  is_finite (f64_f (number_to_f64 m (nsup n) Sup)) = false.
Proof.
intros m [a b|a] H; cbn [nis_common_interval ninf nsup] in H |- *.
- destruct a as [|qa|]; [left; reflexivity| |left; reflexivity].
  destruct b as [|qb|]; [right; reflexivity|discriminate H|right; reflexivity].
- destruct a as [|qa|]; [left; reflexivity|discriminate H|left; reflexivity].
Qed.

Lemma nis_common_rational :
  forall n, nis_common_interval n = true ->
  (exists q, ninf n = Rational q) /\ (exists q, nsup n = Rational q).
Proof.
intros [a b|a] H; cbn [nis_common_interval ninf nsup] in H |- *.
- destruct a as [|qa|], b as [|qb|]; try discriminate H.
  split; [exists qa|exists qb]; reflexivity.
- destruct a as [|qa|]; try discriminate H. split; exists qa; reflexivity.
Qed.

Lemma common_not_empty :
  forall n, nis_common_interval n = true -> nis_empty n = false.
Proof.
intros [a b|a] H; [|reflexivity].
destruct a, b; cbn in H |- *; first [reflexivity|discriminate H].
Qed.

(** [NInterval::EMPTY] has the bounds +inf and -inf, which
    [Interval::try_from] rejects. *)
Lemma parse_hull_nis_empty :
  forall m n, nis_empty n = true -> parse_hull m n = Interval.EMPTY.
Proof.
intros m [[| |] [| |]|a] H; cbn in H; try discriminate H; reflexivity.
Qed.

Lemma dec_eqb_ill : forall d, dec_eqb d Ill = true -> d = Ill.
Proof.
intros [] H; first [reflexivity|discriminate H].
Qed.

(** ** The decoration that [set_dec] gives *)

(** What [From<DecNInterval>] returns for any [x] whose [nx x] has
    [ninterval_ok], with the decoration as [set_dec] gives it: NaI for
    [ill], and otherwise [trv] if the literal holds no real, and the
    literal's decoration if it holds one, except [dac] in place of [com]
    when the result is not common. *)
Lemma from_dec_ninterval_set_dec :
  forall m x, parse_ok m -> ninterval_ok (nx x) ->
  let y := DecInterval.from_dec_ninterval m x in
  if dec_eqb (nd x) Ill then y = DecInterval.NAI else
  is_tightest (ninterval_set (nx x)) (itv y) /\
  ((forall r, ~ ninterval_set (nx x) r) -> dec y = Trv) /\
  ((exists r, ninterval_set (nx x) r) ->
   dec y = if dec_eqb (nd x) Com && negb (Interval.is_common_interval (itv y))
           then Dac else nd x).
Proof.
intros m x Hm Hok. cbv zeta.
destruct (dec_eqb (nd x) Ill) eqn:Hd; cbv beta iota.
- (* [ill]: [d.min(Dac)] is [ill] too, and [set_dec] returns NaI. *)
  rewrite from_dec_ninterval_eq, (dec_eqb_ill _ Hd).
  destruct (parse_overflow m (nx x)); reflexivity.
- rewrite (itv_from_dec m x Hd). split; [|split].
  + exact (bounds_tightest m (nx x) Hm Hok).
  + intros Hno. rewrite from_dec_ninterval_eq.
    rewrite (parse_hull_of_empty m (nx x) Hm Hok Hno).
    unfold DecInterval.set_dec. rewrite (dec_min_not_ill _ _ Hd).
    reflexivity.
  + intros Hne. rewrite from_dec_ninterval_eq. unfold DecInterval.set_dec.
    rewrite (dec_min_not_ill _ _ Hd).
    rewrite (parse_hull_nonempty m (nx x) Hm Hok Hne).
    destruct (parse_overflow m (nx x)) eqn:Ho.
    * (* An overflowed bound makes the interval not common, and then
         [d.min(Dac)] is what [set_dec] makes of [d]. *)
      rewrite (overflow_not_common m (nx x) Ho).
      destruct (nd x); reflexivity.
    * change (if false then dec_min (nd x) Dac else nd x) with (nd x).
      match goal with
      | |- context [if dec_eqb (nd x) Com && ?c then _ else _] =>
          destruct (dec_eqb (nd x) Com && c)
      end; reflexivity.
Qed.

(** For a common literal with [ninterval_ok] and a decoration other than
    [ill], the result is not common exactly when the conversion of a bound
    overflowed. Without [ninterval_ok], [[2, 1]] would be common, and its
    result [Interval::EMPTY] not common, with no bound overflowed. *)
Lemma from_dec_ninterval_not_common :
  forall m x, parse_ok m -> ninterval_ok (nx x) -> dec_eqb (nd x) Ill = false ->
  nis_common_interval (nx x) = true ->
  (Interval.is_common_interval (itv (DecInterval.from_dec_ninterval m x)) = false <->
   f64_overflow (number_to_f64 m (ninf (nx x)) Inf) ||
   f64_overflow (number_to_f64 m (nsup (nx x)) Sup) = true).
Proof.
intros m x Hm Hok Hd Hc. rewrite (itv_from_dec m x Hd).
change (Interval.is_common_interval (parse_hull m (nx x)) = false <->
        parse_overflow m (nx x) = true).
split; [|exact (overflow_not_common m (nx x))].
intros Hnc. destruct (parse_overflow m (nx x)) eqn:Ho; [reflexivity|exfalso].
(* No bound overflowed, so both are finite, and the interval is not empty:
   [Interval::try_from] succeeded with finite bounds. *)
unfold parse_overflow in Ho. apply Bool.orb_false_iff in Ho.
destruct Ho as [Hoa Hob].
assert (Fin : forall n s, (exists q, n = Rational q) ->
          f64_overflow (number_to_f64 m n s) = false ->
          is_finite (f64_f (number_to_f64 m n s)) = true).
{ intros n s Hq Ho.
  destruct (is_finite (f64_f (number_to_f64 m n s))) eqn:F; [reflexivity|].
  destruct (number_to_f64_correct m n s Hm) as (_ & _ & Hov).
  rewrite (proj2 Hov (conj Hq F)) in Ho. discriminate Ho. }
destruct (nis_common_rational _ Hc) as [Ea Eb].
pose proof (Fin _ Inf Ea Hoa) as Fa. pose proof (Fin _ Sup Eb Hob) as Fb.
destruct (ninterval_ok_set (nx x) Hok (common_not_empty (nx x) Hc)) as (r & Hr).
pose proof (parse_hull_nonempty m (nx x) Hm Hok (ex_intro _ r Hr)) as Hne.
revert Hnc Hne. unfold parse_hull.
destruct (Interval.try_from (f64_f (number_to_f64 m (ninf (nx x)) Inf))
                            (f64_f (number_to_f64 m (nsup (nx x)) Sup)))
  as [y|] eqn:E; intros Hnc Hne.
- change (Interval.is_common_interval y = false) in Hnc.
  rewrite (try_from_finite _ _ y E Fa Fb) in Hnc. discriminate Hnc.
- discriminate Hne.
Qed.

(** ** The theorems *)

(** A literal whose bounds are both [Rational]s denotes a bounded set. *)
Lemma nis_common_bounded :
  forall n, nis_common_interval n = true -> bounded (ninterval_set n).
Proof.
intros n Hc. destruct (nis_common_rational n Hc) as [[qa Ea] [qb Eb]].
(* [qa <= r <= qb] puts [|r|] below [|qa| + |qb|]. *)
exists (Rabs (Q2R qa) + Rabs (Q2R qb)). intros r [Ha Hb].
rewrite Ea in Ha. rewrite Eb in Hb. cbn [above_num below_num] in Ha, Hb.
pose proof (Rle_abs (Q2R qb)) as Hqb. pose proof (Rle_abs (- Q2R qa)) as Hqa.
rewrite Rabs_Ropp in Hqa.
pose proof (Rabs_pos (Q2R qa)). pose proof (Rabs_pos (Q2R qb)).
apply Rabs_le. lra.
Qed.

(** [DecNInterval::NAI], which the grammar returns for [[nai]], has
    [dec_ninterval_ok]: it is [NInterval::EMPTY] decorated [ill]. *)
Lemma dn_NAI_ok : dec_ninterval_ok dn_NAI.
Proof.
unfold dec_ninterval_ok, dn_NAI, n_EMPTY. cbn [nx nd nis_empty].
split; [left; reflexivity|].
split; [intros H; discriminate H|].
split; intros _; [right|]; reflexivity.
Qed.

(** For an [x] with [ninterval_ok], [DecNInterval::new(x)], which the
    grammar returns for a literal [x] without a decoration, has
    [dec_ninterval_ok]. The decoration that [new] gives meets the three
    conjuncts on [nd] for any [x], and the first conjunct is
    [ninterval_ok x] itself. *)
Lemma dn_new_ok : forall x, ninterval_ok x -> dec_ninterval_ok (dn_new x).
Proof.
intros x Hok. unfold dec_ninterval_ok, dn_new. cbv zeta. cbn [nx nd].
split; [exact Hok|].
destruct (nis_empty x), (nis_common_interval x); cbn [negb];
  repeat split; intros H; first [discriminate H|reflexivity|left; reflexivity].
Qed.

(** For an [x] with [ninterval_ok], [DecNInterval::set_dec(x, d)] has
    [dec_ninterval_ok] for every [d]. For [ill] it is NaI, so the proof
    does not need that [decoration] parses no [ill]. For any other [d],
    [set_dec] decorates [NInterval::EMPTY] [trv], and otherwise keeps [x]
    and [d], except that it lowers [com] to [dac] for an [x] that is not
    common. *)
Lemma dn_set_dec_ok :
  forall x d, ninterval_ok x -> dec_ninterval_ok (dn_set_dec x d).
Proof.
intros x d Hok. unfold dn_set_dec.
destruct (dec_eqb d Ill) eqn:Ei; [exact dn_NAI_ok|].
unfold dec_ninterval_ok.
destruct (nis_empty x) eqn:Ee.
- (* [NInterval::EMPTY] is decorated [trv]. *)
  cbn [dn_EMPTY nx nd n_EMPTY nis_empty].
  split; [left; reflexivity|].
  split; [intros H; discriminate H|].
  split; intros H; [left; reflexivity|discriminate H].
- (* Otherwise [x] is kept, so it has [ninterval_ok] and is not
     [NInterval::EMPTY], and the decoration is [dac], or [d], which is not
     [ill], and is [com] only if [x] is common. *)
  destruct (dec_eqb d Com && negb (nis_common_interval x)) eqn:Ec;
    cbn [nx nd]; rewrite Ee; (split; [exact Hok|]).
  + split; [intros H; discriminate H|].
    split; intros H; discriminate H.
  + split; [|split; intros H; [discriminate H|]].
    * intros ->. cbn [dec_eqb discriminant Z.eqb Pos.eqb andb] in Ec.
      destruct (nis_common_interval x); [reflexivity|discriminate Ec].
    * rewrite H in Ei. discriminate Ei.
Qed.

(** What [dn_decorated] returns for a literal [x] with [ninterval_ok] and
    the decoration [d], if it accepts the literal, has [dec_ninterval_ok],
    the decoration [d], and the [NInterval] [x] unless [d] is [ill]. The
    test [xd.d == d] is not needed for [dec_ninterval_ok], which [set_dec]
    alone gives. It is what keeps the literal's decoration: it rejects
    [[1,inf]_com] and [[empty]_dac], which [set_dec] would decorate [dac]
    and [trv]. So for a [d] other than [ill], the literal's own [x] and [d]
    meet [dec_ninterval_ok] if [dn_decorated] accepts the literal. *)
Lemma dn_decorated_ok :
  forall x d y, ninterval_ok x -> dn_decorated x d = Some y ->
  dec_ninterval_ok y /\ nd y = d /\ (d <> Ill -> nx y = x).
Proof.
intros x d y Hok. unfold dn_decorated.
destruct (dec_eqb (nd (dn_set_dec x d)) d) eqn:E; intros H; [|discriminate H].
injection H as <-.
split; [exact (dn_set_dec_ok x d Hok)|].
split.
- (* The test [xd.d == d]. *)
  revert E. generalize (nd (dn_set_dec x d)) as e. intros e E.
  destruct e, d; first [reflexivity|discriminate E].
- (* [set_dec] keeps [x] unless [d] is [ill], as [EMPTY] is
     [NInterval::EMPTY] decorated [trv]. *)
  intros Hd. unfold dn_set_dec.
  destruct (dec_eqb d Ill) eqn:Ei.
  + destruct d; first [discriminate Ei|destruct (Hd eq_refl)].
  + destruct (nis_empty x) eqn:Ee.
    * destruct x as [[| |] [| |]|a]; cbn [nis_empty] in Ee;
        try discriminate Ee; reflexivity.
    * destruct (_ && _); reflexivity.
Qed.

Theorem from_dec_ninterval_correct :
  forall m x, parse_ok m -> dec_ninterval_ok x ->
  let y := DecInterval.from_dec_ninterval m x in
  let overflow :=
    bounded (ninterval_set (nx x)) /\ ~ bounded (fun r => mem r (itv y)) in
  (if dec_eqb (nd x) Ill then y = DecInterval.NAI
   else is_tightest (ninterval_set (nx x)) (itv y)) /\
  (nd x = Com /\ overflow -> dec y = Dac) /\
  (~ (nd x = Com /\ overflow) -> dec y = nd x) /\
  (nd x = Com ->
   (overflow <->
    f64_overflow (number_to_f64 m (ninf (nx x)) Inf) ||
    f64_overflow (number_to_f64 m (nsup (nx x)) Sup) = true)).
Proof.
(* [NInterval::EMPTY] has the lower bound +inf, so it holds no real. *)
assert (Hno : forall n, nis_empty n = true -> forall r, ~ ninterval_set n r).
{ intros n He r [Ha _].
  destruct n as [[| |] b|a]; cbn [nis_empty] in He; try discriminate He.
  exact Ha. }
intros m x Hm (Hok & Hcom & Hemp & _). cbv zeta.
pose proof (from_dec_ninterval_set_dec m x Hm Hok) as Hsd. cbv zeta in Hsd.
pose proof (from_dec_ninterval_not_common m x Hm Hok) as Hnc.
set (y := DecInterval.from_dec_ninterval m x) in *. clearbody y.
destruct x as [n d]. cbn [nx nd] in *.
(* Either the literal holds no real and is decorated [trv] or [ill], or
   it holds a real. *)
assert (Hcase : ((forall r, ~ ninterval_set n r) /\ (d = Trv \/ d = Ill)) \/
                exists r, ninterval_set n r).
{ revert Hemp. destruct (nis_empty n) eqn:He; intros Hemp.
  - left. exact (conj (Hno n He) (Hemp eq_refl)).
  - right. exact (ninterval_ok_set n Hok He). }
destruct d; cbn [dec_eqb discriminant Z.eqb Pos.eqb andb negb] in Hsd |- *.
(* Goals 2-4 are [trv], [def] and [dac]. The result has the literal's
   decoration if the literal holds a real, and [trv] if it holds none,
   which [Hcase] then makes the literal's decoration. *)
2-4: destruct Hsd as (Ht & Htrv & Hd); split; [exact Ht|split; [|split]];
  [ intros [H _]; discriminate H
  | intros _; destruct Hcase as [[Hn [H|H]]|Hr];
      first [discriminate H|exact (Htrv Hn)|exact (Hd Hr)]
  | intros H; discriminate H ].
- (* [ill] gives NaI, and the other conjuncts are about [com]. *)
  split; [exact Hsd|split; [|split]].
  + intros [H _]. discriminate H.
  + intros _. rewrite Hsd. reflexivity.
  + intros H. discriminate H.
- (* [com]: the literal is common, so it is bounded and holds a real,
     which the tightest interval holds too. *)
  pose proof (Hcom eq_refl) as Hc. clear Hcase.
  destruct Hsd as (Ht & _ & Hd). pose proof Ht as (Hv & Hin & _).
  destruct (ninterval_ok_set n Hok (common_not_empty n Hc)) as (r & Hr).
  pose proof (Hd (ex_intro _ r Hr)) as Hdy.
  pose proof (mem_not_empty (itv y) r Hv (Hin r Hr)) as Hne.
  pose proof (nis_common_bounded n Hc) as Hb.
  specialize (Hnc eq_refl Hc).
  revert Hdy Hnc.
  destruct (Interval.is_common_interval (itv y)) eqn:Ec; cbn [negb];
    intros Hdy Hnc.
  + (* A common result is bounded, so no overflow occurred. *)
    pose proof (common_bounded (itv y) Ec) as HbY.
    split; [exact Ht|split; [|split]].
    * intros (_ & _ & HnbY). destruct (HnbY HbY).
    * intros _. exact Hdy.
    * intros _. split.
      -- intros (_ & HnbY). destruct (HnbY HbY).
      -- intros Hf. apply Hnc in Hf. discriminate Hf.
  + (* A nonempty result that is not common is unbounded. *)
    assert (HnbY : ~ bounded (fun r => mem r (itv y))).
    { intros HbY. rewrite (bounded_common (itv y) Hv Hne HbY) in Ec.
      discriminate Ec. }
    split; [exact Ht|split; [|split]].
    * intros _. exact Hdy.
    * intros Hn. exfalso. apply Hn.
      split; [reflexivity|split; [exact Hb|exact HnbY]].
    * intros _. split.
      -- intros _. apply Hnc. reflexivity.
      -- intros _. split; [exact Hb|exact HnbY].
Qed.

Theorem from_ninterval_correct :
  forall m x, parse_ok m -> ninterval_ok x ->
  is_tightest (ninterval_set x) (DecInterval.from_ninterval m x).
Proof.
intros m x Hm Hok. unfold DecInterval.from_ninterval.
assert (Hd : dec_eqb (nd (dn_new x)) Ill = false).
{ unfold dn_new. destruct (nis_empty x), (nis_common_interval x); reflexivity. }
rewrite (itv_from_dec m (dn_new x) Hd).
exact (bounds_tightest m x Hm Hok).
Qed.

(** [set_dec(y, d)] is [DecInterval::new(y)] when [d] is not [ill] and,
    for a nonempty [y], is [com], or [dac] with [y] not common. *)
Lemma set_dec_new :
  forall y d, valid y -> dec_eqb d Ill = false ->
  (Interval.is_empty y = false ->
   d = Com \/ (d = Dac /\ Interval.is_common_interval y = false)) ->
  DecInterval.set_dec y d = DecInterval.new y.
Proof.
intros y d Hy Hd. unfold DecInterval.set_dec, DecInterval.new. rewrite Hd.
destruct (Interval.is_empty y) eqn:E; intros H.
- rewrite (valid_empty_eq y Hy E). reflexivity.
- destruct (H eq_refl) as [-> | [-> Hc]].
  + destruct (Interval.is_common_interval y); reflexivity.
  + rewrite Hc. reflexivity.
Qed.

Theorem from_ninterval_new :
  forall m x,
  DecInterval.from_dec_ninterval m (dn_new x) =
  DecInterval.new (DecInterval.from_ninterval m x).
Proof.
intros m x. unfold DecInterval.from_ninterval.
assert (Hd : dec_eqb (nd (dn_new x)) Ill = false).
{ unfold dn_new. destruct (nis_empty x), (nis_common_interval x); reflexivity. }
rewrite (itv_from_dec m (dn_new x) Hd), from_dec_ninterval_eq.
change (nx (dn_new x)) with x.
apply set_dec_new;
  [apply parse_hull_valid|exact (dec_min_not_ill _ _ Hd)|intros Hne].
change (nd (dn_new x)) with
  (if nis_empty x then Trv else if negb (nis_common_interval x) then Dac else Com).
destruct (nis_empty x) eqn:He.
- (* [NInterval::EMPTY] gives [Interval::EMPTY]. *)
  rewrite (parse_hull_nis_empty m x He) in Hne. discriminate Hne.
- destruct (nis_common_interval x) eqn:Hc; cbn [negb].
  + (* A common literal is [com], and [dac] after an overflow, which makes
       the interval not common. *)
    destruct (parse_overflow m x) eqn:Ho; [right|left; reflexivity].
    split; [reflexivity|exact (overflow_not_common m x Ho)].
  + (* A literal that is not common is [dac], and has an infinite
       bound. *)
    right. split; [now destruct (parse_overflow m x)|].
    exact (parse_hull_infinite m x (not_common_infinite m x Hc)).
Qed.
