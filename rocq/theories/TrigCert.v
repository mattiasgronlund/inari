(** * When the floors of [x / C] are exact, and when [x] is wide

    [Interval::cos], [sin] and [tan] keep the floors [qa] and [qb] of the
    bounds of [x / C] ([trig_reduce] in [TrigReduce.v]) when
    [floors_exact] says that they are the floors of [a / c] and [b / c]
    ([floors_exact_ok]): [qa <= floor(a / c)] already, and
    [floor(a / c) <= floor(sup([a, a] / C))], as [[a, a] / C] contains
    [a / c] ([trig_quot_hi] in [TrigQuot.v]), so the two are equal if
    [floors_exact]'s first test holds; the same for [qb] with
    [inf([b, b] / C)] ([trig_quot_lo]). [cos] and [sin] also keep them
    when [b - a], rounded to nearest, is at least 8, as [x] then holds two
    reals at least [2 * PI] apart ([trig_wide]), or is unbounded. [tan]
    keeps them from 4 on, which [trig_wide] does not cover: with [w = 4]
    it gives two reals only [L <= 3] apart, and [3 < PI]. [tn_sub_wide]
    in [Tan.v] shows that [b - a > PI] then. *)

From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Inari Require Import Model Ieee1788 Integer Div PiBounds Sign DecBinary ClosedDom
  TrigQuot TrigReduce Encoding Decompose MonoInc.

Open Scope R_scope.

(** ** The singleton [[q, q]]

    [[q, q]] of a finite [q] is valid and holds [q]. These are
    [tn_with_valid] and [tn_mem_with] of [Tan.v], which builds after this
    file. *)

Lemma tc_with_valid :
  forall q, is_finite q = true -> valid (Interval.with_infsup_raw q q).
Proof.
intros q Fq. unfold valid, Interval.with_infsup_raw, Generic.constant. cbn [rep].
right. unfold opp. rewrite Bopp_involutive. split; [|split].
- rewrite Bleb_correct by exact Fq. apply Rle_bool_true, Rle_refl.
- destruct q; try discriminate Fq; discriminate.
- destruct q; try discriminate Fq; discriminate.
Qed.

Lemma tc_mem_with :
  forall q, is_finite q = true -> mem (B2R q) (Interval.with_infsup_raw q q).
Proof.
intros q Fq. unfold mem, Interval.with_infsup_raw, Generic.constant. cbn [rep fst snd].
unfold opp. rewrite Bopp_involutive.
destruct q; try discriminate Fq; split; apply Rle_refl.
Qed.

Lemma tc_with_nonempty :
  forall q, is_finite q = true -> Interval.is_empty (Interval.with_infsup_raw q q) = false.
Proof.
intros q Fq. exact (mem_not_empty _ _ (tc_with_valid q Fq) (tc_mem_with q Fq)).
Qed.

Lemma tc_with_inf : forall q, Interval.inf_raw (Interval.with_infsup_raw q q) = q.
Proof.
intros q. unfold Interval.inf_raw, Interval.with_infsup_raw, Generic.constant.
cbn [rep fst]. unfold opp. apply Bopp_involutive.
Qed.

Lemma tc_with_sup : forall q, Interval.sup_raw (Interval.with_infsup_raw q q) = q.
Proof.
reflexivity.
Qed.

(** [ffloor z == q], for finite [z] and [q = k], says that [k] is the
    floor of [z]. *)
Lemma tc_floor_eq :
  forall z q k, is_finite z = true -> is_finite q = true -> B2R q = IZR k ->
  Model.eq (ffloor z) q = true -> Rfloor (B2R z) = IZR k.
Proof.
intros z q k Fz Fq Hq E. unfold Model.eq in E.
rewrite Beqb_correct in E by (rewrite ?ffloor_finite; assumption).
rewrite ffloor_B2R, Hq in E. revert E.
case Req_bool_spec; [intros H _; exact H | discriminate].
Qed.

(** ** [floors_exact] *)

(** If [floors_exact] is true, [ka = floor(sup([a, a] / C))] is at least
    [floor(a / c)], which is above [a / c - 1], and
    [kb = floor(inf([b, b] / C))] is at most [inf([b, b] / C) <= b / c]. *)
Theorem floors_exact_ok :
  forall has_fma C c a b qa qb ka kb, trig_const C c ->
  is_finite a = true -> is_finite b = true ->
  is_finite qa = true -> B2R qa = IZR ka -> is_finite qb = true -> B2R qb = IZR kb ->
  exists e, Interval.floors_exact has_fma a b qa qb C = Some e /\
    (e = true -> B2R a < (IZR ka + 1) * c /\ IZR kb * c <= B2R b).
Proof.
intros has_fma C c a b qa qb ka kb HC Fa Fb Fqa Hqa Fqb Hqb.
pose proof HC as (HCv & _ & _ & _ & H1 & Hlc & _).
assert (Hc0 : 0 < c) by lra.
unfold Interval.floors_exact.
destruct (div_correct has_fma _ C (tc_with_valid a Fa) HCv) as (za & -> & Hza).
assert (Fa' : is_finite (Interval.sup_raw (Interval.with_infsup_raw a a)) = true)
  by (rewrite tc_with_sup; exact Fa).
destruct (proj2 (trig_quot_hi C c _ za HC (tc_with_valid a Fa) (tc_with_nonempty a Fa) Hza)
  Fa') as (Fza & Hza_lb).
rewrite tc_with_sup in Hza_lb.
destruct (Model.eq (ffloor (Interval.sup_raw za)) qa) eqn:E1;
  [|exists false; split; [reflexivity | discriminate]].
destruct (div_correct has_fma _ C (tc_with_valid b Fb) HCv) as (zb & -> & Hzb).
assert (Fb' : is_finite (Interval.inf_raw (Interval.with_infsup_raw b b)) = true)
  by (rewrite tc_with_inf; exact Fb).
destruct (proj2 (trig_quot_lo C c _ zb HC (tc_with_valid b Fb) (tc_with_nonempty b Fb) Hzb)
  Fb') as (Fzb & Hzb_ub & _).
rewrite tc_with_inf in Hzb_ub.
exists (Model.eq (ffloor (Interval.inf_raw zb)) qb). split; [reflexivity|]. intros E2.
pose proof (tc_floor_eq _ qa ka Fza Fqa Hqa E1) as Ka.
pose proof (tc_floor_eq _ qb kb Fzb Fqb Hqb E2) as Kb.
pose proof (Rfloor_le _ _ Hza_lb) as Ha1.
pose proof (Rfloor_near (B2R a / c)) as Ha2.
pose proof (Rfloor_lb (B2R (Interval.inf_raw zb))) as Hb1.
(* [nra] does not see through [/]: name the quotients. *)
assert (Ea : B2R a / c * c = B2R a) by (field; lra).
assert (Eb : B2R b / c * c = B2R b) by (field; lra).
set (ta := B2R a / c) in *. set (tb := B2R b / c) in *. clearbody ta tb.
assert (Ta : ta < IZR ka + 1) by lra.
assert (Tb : IZR kb <= tb) by lra.
split; nra.
Qed.

(** ** [b - a >= w] *)

(** If [b - a], rounded to nearest, is at least the integer [w] from 1 to
    8, then [b - a >= w - 1]: otherwise [0 <= b - a < w - 1], and as [0] and
    [w - 1] are floats, the rounded difference is at most [w - 1] and does
    not overflow. *)
Lemma tc_sub_ge :
  forall a b (w : Z), is_finite a = true -> is_finite b = true -> B2R a <= B2R b ->
  (1 <= w <= 8)%Z -> Model.le (of_u64 w) (Model.sub b a) = true ->
  IZR w - 1 <= B2R b - B2R a.
Proof.
intros a b w Fa Fb Hab Hw Hle.
apply Rnot_lt_le. intros Hlt.
assert (Fw1 : generic_format radix2 fexp64 (IZR w - 1)).
{ rewrite <- minus_IZR. apply rd_int_format. simpl Z.pow. lia. }
assert (Hr1 : round radix2 fexp64 ZnearestE (B2R b - B2R a) <= IZR w - 1).
{ apply round_le_generic; [typeclasses eauto .. | exact Fw1 | lra]. }
assert (Hr0 : 0 <= round radix2 fexp64 ZnearestE (B2R b - B2R a)).
{ apply round_ge_generic; [typeclasses eauto .. | apply generic_format_0 | lra]. }
assert (Hw8 : IZR w <= 8) by (apply IZR_le; lia).
assert (HB : 8 < bpow radix2 1024) by (cbn [bpow radix_val radix2]; lra).
assert (Ht : Rabs (round radix2 fexp64 ZnearestE (B2R b - B2R a)) < bpow radix2 1024)
  by (rewrite Rabs_pos_eq by exact Hr0; lra).
generalize (@Bminus_correct 53 1024 _ _ mode_NE b a Fb Fa).
rewrite Rlt_bool_true by exact Ht.
intros (HS & FS & _).
change (Bminus mode_NE b a) with (Model.sub b a) in HS, FS.
change (round radix2 (SpecFloat.fexp 53 1024) (round_mode mode_NE)) with
  (round radix2 fexp64 ZnearestE) in HS.
assert (Hw53 : (0 <= w <= 2^53)%Z) by (simpl Z.pow; lia).
destruct (of_u64_exact w Hw53) as (Fw & _ & Ew).
unfold Model.le in Hle. rewrite Bleb_correct in Hle by assumption.
rewrite Ew, HS in Hle. revert Hle.
case Rle_bool_spec; [intros H _ | discriminate]. lra.
Qed.

(** If [b - a], rounded to nearest, is at least [w], [x] holds two reals
    at least [L <= w - 1] apart: its bounds if they are finite
    ([tc_sub_ge]), and otherwise a real [r0] of [x] and [r0 -/+ |L|]. *)
Theorem trig_wide :
  forall x (w : Z) (L : R), valid x -> Interval.is_empty x = false ->
  (1 <= w <= 8)%Z -> L <= IZR w - 1 ->
  Model.le (of_u64 w) (Model.sub (Interval.sup_raw x) (Interval.inf_raw x)) = true ->
  exists r t, mem r x /\ mem t x /\ L <= t - r.
Proof.
intros x w L Hx Hn Hw HL Hle.
destruct (nonempty_mem x Hx Hn) as (r0 & Hr0).
pose proof (Rabs_pos L) as HL0. pose proof (RRle_abs L) as HL1.
destruct (valid_nonempty x Hx Hn) as (Ha & Hb & Hord).
destruct Ha as [Fa|Ea]; [destruct Hb as [Fb|Eb]|].
- exists (B2R (opp (fst (rep x)))), (B2R (snd (rep x))).
  split; [exact (mono_mem_inf x Hx Hn Fa)|].
  split; [exact (mono_mem_sup x Hx Hn Fb)|].
  rewrite (bound_finite _ Fa), (bound_finite _ Fb) in Hord. cbn [ordered] in Hord.
  pose proof (tc_sub_ge _ _ w Fa Fb Hord Hw Hle). lra.
- exists r0, (r0 + Rabs L). split; [exact Hr0|]. split; [|lra].
  apply (mono_mem_up x r0); [exact Hr0 | exact Eb | lra].
- exists (r0 - Rabs L), r0. split; [|split; [exact Hr0 | lra]].
  apply (mono_mem_dn x r0); [exact Hr0 | exact Ea | lra].
Qed.
