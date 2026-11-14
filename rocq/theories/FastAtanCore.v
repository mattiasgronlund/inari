(** * The core of the fast path of atan

    [DyadicAtan.fast_atan_core] of [Model.v] computes atan t for a
    double-double [t = th + tl] in [[2^-61, 129/128]]: for [64 th <= 1/2]
    the polynomial of [FastAtanPoly.v] at [t] alone; otherwise, with [i]
    the integer nearest [64 th] and [c = i/64], atan t = atan c + atan u
    with [u = (t - c) / (1 + t c)] ([FastAtanIdent.atan_sub_table]), the
    table of [FastAtanTables.v] for atan c, [dd_div] of [FastDiv.v] for
    [u] (|u| <= 2^-7) and the polynomial for atan u. [th - c] is exact
    (Sterbenz) and [th c] is exact as a pair ([c] has 7 bits). Where it
    returns, it is within [2^-74] of atan t relatively
    ([fast_atan_core_correct]); it returns [None] only where [0 < |t - c|
    < 2^-80]. It returns the same with and without an FMA
    ([fast_atan_core_fma]). *)

From Stdlib Require Import ZArith Reals Lra Lia QArith Qreals.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN Plus_error Mult_error Sterbenz.
From Inari Require Import Model Mpfr Encoding Elementary TwoSum TwoProduct DyDriver NearF64
  FastRound FastRoundErr FastDiv CancelLanes FastHypPos FastAtanTables FastAtanIdent
  FastAtanPoly.
From Inari Require FastExpErr FastExpReduce ConstTight.

Open Scope R_scope.

(** ** Helpers *)

(** [lit w H] adds [H : B2R w = n * / d] for the literal [w], as in
    [FastExpReduce.v]. *)
Local Ltac lit w H :=
  let q := eval vm_compute in (ConstTight.B2Q w) in
  assert (H : B2R w = Q2R q)
    by (rewrite ConstTight.B2Q_correct; f_equal; vm_compute; reflexivity);
  unfold Q2R in H; cbn [Qnum Qden] in H.

(** [Fast.fast_two_sum a b] is exact where [|b| <= |a|] or [a = 0], as in
    [FastLogCore.v]. *)
Lemma lc_fts :
  forall a b s t, is_finite a = true -> is_finite b = true ->
  (Rabs (B2R b) <= Rabs (B2R a) \/ B2R a = 0) -> Rabs (B2R a + B2R b) <= 16 ->
  Fast.fast_two_sum a b = (s, t) ->
  is_finite s = true /\ is_finite t = true /\ B2R s = RN (B2R a + B2R b) /\
  B2R s + B2R t = B2R a + B2R b.
Proof.
intros a b s t Fa Fb Hab H16 E.
unfold Fast.fast_two_sum in E. injection E as <- <-.
destruct (FastExpErr.add_e a b Fa Fb H16) as (Fs & Es & _).
destruct Hab as [Hab | Ha0].
- destruct (fast_two_sum a b (add a b) Fa Fb Hab Fs Es) as [Ft Et].
  do 3 (split; [assumption|]). rewrite Et. ring.
- assert (Es' : B2R (add a b) = B2R b).
  { rewrite Es, Ha0, Rplus_0_l. apply round_generic; [typeclasses eauto|].
    apply generic_format_B2R. }
  assert (Hd16 : Rabs (B2R a - B2R (add a b)) <= 16)
    by (rewrite Es', Ha0, Rminus_0_l, Rabs_Ropp; rewrite Ha0, Rplus_0_l in H16; exact H16).
  destruct (FastExpErr.sub_e a (add a b) Fa Fs Hd16) as (Fd & Ed & _).
  assert (Ed' : B2R (sub a (add a b)) = - B2R b).
  { rewrite Ed, Es', Ha0, Rminus_0_l. apply round_generic; [typeclasses eauto|].
    apply generic_format_opp, generic_format_B2R. }
  assert (Ht16 : Rabs (B2R b + B2R (sub a (add a b))) <= 16)
    by (rewrite Ed', Rplus_opp_r, Rabs_R0; lra).
  destruct (FastExpErr.add_e b (sub a (add a b)) Fb Fd Ht16) as (Ft & Et & _).
  rewrite Ed', Rplus_opp_r, round_0 in Et by typeclasses eauto.
  do 3 (split; [assumption|]). rewrite Es', Et, Ha0. ring.
Qed.

(** The exponent of a finite [f64] below [2^k] is below [k], and that of
    one at least [2^k] at least [k], as in [FastDiv.v]. *)
Lemma exponent_lt :
  forall x k, is_finite x = true -> (-1022 <= k)%Z ->
  Rabs (B2R x) < bpow radix2 k -> (Generic.exponent x < k)%Z.
Proof.
intros x k Fx Hk H.
destruct (Z_lt_le_dec (Generic.exponent x) (-1022)) as [L|L]; [lia|].
pose proof (bpow_exponent_le_abs_B2R x Fx L) as H0.
assert (H1 : bpow radix2 (Generic.exponent x) < bpow radix2 k) by lra.
apply lt_bpow in H1. exact H1.
Qed.

Lemma exponent_ge :
  forall x k, is_finite x = true -> bpow radix2 k <= Rabs (B2R x) ->
  (k <= Generic.exponent x)%Z.
Proof.
intros x k Fx H.
pose proof (abs_B2R_lt_exponent x Fx) as H0.
assert (H1 : bpow radix2 k < bpow radix2 (Generic.exponent x + 1)) by lra.
apply lt_bpow in H1. lia.
Qed.

(** [two_prod_is_exact] holds for products of moderate exponents, as in
    [FastDiv.v]. *)
Lemma two_prod_is_exact_of :
  forall fma x y,
  (-968 <= Generic.exponent (mul x y) <= 1022)%Z ->
  (Generic.exponent x <= 995)%Z -> (Generic.exponent y <= 995)%Z ->
  Generic.two_prod_is_exact fma x y (mul x y) = true.
Proof.
intros fma x y Ep Ex Ey.
destruct fma; cbv beta iota zeta delta [Generic.two_prod_is_exact];
  repeat (apply andb_true_intro; split); apply Z.leb_le; lia.
Qed.

(** The low part of a rounded-to-nearest normal value is within [2^-53] of
    it relatively. *)
Lemma low_rel :
  forall x (h : f64), B2R h = RN x -> bpow radix2 (-1022) <= Rabs (B2R h) ->
  Rabs (x - B2R h) <= bpow radix2 (-53) * Rabs (B2R h).
Proof.
intros x h Hh Hb.
rewrite Hh in *.
rewrite <- Rabs_Ropp, Ropp_minus_distr.
apply Rle_trans with (/ 2 * ulp radix2 fexp64 (RN x)).
{ apply error_le_half_ulp_round; typeclasses eauto. }
assert (Hb' : bpow radix2 (-1074 + 53 - 1) <= Rabs (RN x)) by exact Hb.
pose proof (ulp_FLT_le radix2 (-1074) 53 (RN x) Hb') as U.
assert (B : bpow radix2 (1 - 53) = / 4503599627370496 /\ bpow radix2 (-53) = / 9007199254740992)
  by (split; reflexivity).
destruct B as (B1 & B2). rewrite B1 in U. rewrite B2. lra.
Qed.

(** [eq x zero] tests [x = 0]. *)
Lemma eq_zero_R :
  forall x : f64, is_finite x = true -> eq x zero = true <-> B2R x = 0.
Proof.
intros x Fx.
unfold eq.
rewrite Beqb_correct by first [exact Fx | reflexivity].
change (B2R zero) with 0.
destruct (Req_bool_spec (B2R x) 0) as [H|H]; split; intros; congruence.
Qed.

(** ** The index *)

(** The float [kf] is the integer [i] nearest [64 th], with [0 <= i <=
    64] (the tie at [th = 129/128] goes to the even [SHIFTER + 64]). *)
Lemma core_kf :
  forall th, is_finite th = true -> bpow radix2 (-61) <= B2R th <= 129 / 128 ->
  let kf := sub (add (mul th (from_bits 0x4050000000000000)) DyadicExp.shifter)
    DyadicExp.shifter in
  let i := DyadicExp.to_i64 kf in
  is_finite kf = true /\ B2R kf = IZR i /\ (0 <= i <= 64)%Z /\
  Rabs (64 * B2R th - IZR i) <= / 2.
Proof.
intros th Fth Hth. cbv zeta.
assert (F64 : is_finite (from_bits 0x4050000000000000) = true) by reflexivity.
assert (FS : is_finite DyadicExp.shifter = true) by reflexivity.
lit (from_bits 0x4050000000000000) H64.
lit DyadicExp.shifter HS.
set (W := from_bits 0x4050000000000000) in *.
set (S := DyadicExp.shifter) in *.
assert (B : bpow radix2 52 = 4503599627370496 /\ bpow radix2 53 = 9007199254740992 /\
            bpow radix2 (-61) = / 2305843009213693952 /\ bpow radix2 6 = 64)
  by (repeat split; reflexivity).
destruct B as (B52 & B53 & B61 & B6p).
rewrite B61 in Hth.
(* [64 th] is exact. *)
destruct (mul_below_max th W Fth F64) as (FM & HM & _).
{ apply FastExpReduce.le_MAX, Rabs_le. rewrite H64. lra. }
assert (EM : B2R (mul th W) = 64 * B2R th).
{ rewrite HM, H64.
  replace (B2R th * (64 * / 1)) with (B2R th * bpow radix2 6) by (rewrite B6p; lra).
  rewrite round_generic; [rewrite ?B6p; lra | ..].
  all: try typeclasses eauto.
  - match goal with |- generic_format _ _ ?x =>
      replace x with (B2R th * bpow radix2 6) by (rewrite B6p; lra) end.
    apply mult_bpow_pos_exact_FLT; [apply generic_format_B2R | lia]. }
set (M := mul th W) in *.
(* [64 th + SHIFTER] is in [[2^52, 2^53)], so it rounds to an integer [m]. *)
destruct (add_below_max M S FM FS) as (FU & HU & _).
{ apply FastExpReduce.le_MAX, Rabs_le. rewrite EM, HS. lra. }
set (U := add M S) in *.
assert (Hv : bpow radix2 52 <= B2R M + B2R S < bpow radix2 53)
  by (rewrite EM, HS, B52, B53; lra).
rewrite (FastExpReduce.RN_int _ Hv) in HU.
pose proof (Znearest_half (fun x => negb (Z.even x)) (B2R M + B2R S)) as Hm.
set (m := Znearest (fun x => negb (Z.even x)) (B2R M + B2R S)) in *.
apply Rabs_le_inv in Hm.
set (n := (m - 6755399441055744)%Z).
assert (Hn : IZR n = B2R U - B2R S) by (unfold n; rewrite minus_IZR, HU, HS; lra).
assert (Hnr : Rabs (64 * B2R th - IZR n) <= / 2)
  by (apply Rabs_le; rewrite Hn, HU, <- EM; lra).
assert (Hn0 : (0 <= n)%Z).
{ assert (-1 < n)%Z; [|lia]. apply lt_IZR. apply Rabs_le_inv in Hnr. lra. }
assert (Hn65 : (n <= 65)%Z) by (apply le_IZR; apply Rabs_le_inv in Hnr; lra).
(* [n = 65] only at [64 th = 64.5], a tie, which goes to the even
   [SHIFTER + 64]. *)
assert (Hn64 : (n <= 64)%Z).
{ destruct (Z.eq_dec n 65) as [E|E]; [|lia].
  exfalso.
  assert (Ht : 64 * B2R th = 129 / 2).
  { rewrite E in Hnr. apply Rabs_le_inv in Hnr. lra. }
  assert (Hx : B2R M + B2R S = IZR 6755399441055808 + / 2) by (rewrite EM, HS; lra).
  assert (Hmv : m = 6755399441055808%Z).
  { unfold m. rewrite Hx. unfold Znearest.
    rewrite (Zfloor_imp 6755399441055808) by (rewrite plus_IZR; lra).
    replace (IZR 6755399441055808 + / 2 - IZR 6755399441055808) with (/ 2) by ring.
    rewrite Rcompare_Eq by reflexivity. reflexivity. }
  unfold n in E. lia. }
(* [kf] is [n] exactly. *)
destruct (sub_below_max U S FU FS) as (Fkf & Hkf & _).
{ apply FastExpReduce.le_MAX, Rabs_le. rewrite <- Hn.
  assert (0 <= IZR n <= 64) by (split; apply IZR_le; lia). lra. }
assert (Ekf : B2R (sub U S) = IZR n).
{ rewrite Hkf, <- Hn. apply round_generic; [typeclasses eauto|].
  apply FastExpReduce.format_int. lia. }
set (kf := sub U S) in *.
assert (Ek : DyadicExp.to_i64 kf = n)
  by (apply FastExpReduce.to_i64_int; [exact Fkf | exact Ekf | lia]).
rewrite Ek.
split; [exact Fkf|]. split; [exact Ekf|]. split; [lia | exact Hnr].
Qed.

(** [kf] is the integer [i] nearest [64 th], with [0 <= i <= 64] (the tie
    at [th = 129/128] goes to the even [SHIFTER + 64]), and [c = i/64]
    exactly. *)
Lemma core_index :
  forall th, is_finite th = true -> bpow radix2 (-61) <= B2R th <= 129 / 128 ->
  let kf := sub (add (mul th (from_bits 0x4050000000000000)) DyadicExp.shifter)
    DyadicExp.shifter in
  let i := DyadicExp.to_i64 kf in
  (0 <= i <= 64)%Z /\ Rabs (64 * B2R th - IZR i) <= / 2 /\
  is_finite (mul kf (from_bits 0x3f90000000000000)) = true /\
  B2R (mul kf (from_bits 0x3f90000000000000)) = IZR i / 64 /\
  (i = 0%Z -> B2R th <= bpow radix2 (-7)).
Proof.
intros th Fth Hth.
pose proof (core_kf th Fth Hth) as K. cbv zeta in K |- *.
set (kf := sub (add (mul th (from_bits 0x4050000000000000)) DyadicExp.shifter)
  DyadicExp.shifter) in *.
set (n := DyadicExp.to_i64 kf) in *.
destruct K as (Fkf & Ekf & Hn & Hnr).
assert (F6 : is_finite (from_bits 0x3f90000000000000) = true) by reflexivity.
lit (from_bits 0x3f90000000000000) H6.
set (V := from_bits 0x3f90000000000000) in *.
assert (B6 : bpow radix2 (-6) = / 64) by reflexivity.
assert (B7 : bpow radix2 (-7) = / 128) by reflexivity.
rewrite B7.
(* [c = n/64] exactly. *)
assert (Hnb : 0 <= IZR n <= 64) by (split; apply IZR_le; lia).
destruct (FastExpErr.mul_e kf V Fkf F6) as (Fc & Hc & _).
{ rewrite Ekf, H6. apply Rabs_le. lra. }
assert (Ec : B2R (mul kf V) = IZR n / 64).
{ rewrite Hc, Ekf, H6.
  replace (IZR n * (1 * / 64)) with (IZR n * bpow radix2 (-6)) by (rewrite B6; lra).
  rewrite round_generic; [rewrite ?B6; lra | ..].
  all: try typeclasses eauto.
  match goal with |- generic_format _ _ ?x =>
    replace x with (IZR n * bpow radix2 (-6)) by (rewrite B6; lra) end.
  apply FastExpReduce.format_mult; [|lia].
  apply Z.abs_lt; split; [lia|]. apply Z.le_lt_trans with 64%Z; [lia | reflexivity]. }
split; [lia|]. split; [exact Hnr|]. split; [exact Fc|]. split; [exact Ec|].
intros N0. rewrite N0 in Hnr. apply Rabs_le_inv in Hnr. lra.
Qed.

(** [ks.to_bits() as i32 as i64] of [fast_atan_core] and [fast_atan1] is
    the [i] of [core_index] ([FastExpReduce.shifter_bits]). *)
Lemma core_bits :
  forall th, is_finite th = true -> bpow radix2 (-61) <= B2R th <= 129 / 128 ->
  DyadicExp.low_i32 (to_bits (add (mul th (from_bits 0x4050000000000000)) DyadicExp.shifter)) =
  DyadicExp.to_i64
    (sub (add (mul th (from_bits 0x4050000000000000)) DyadicExp.shifter) DyadicExp.shifter).
Proof.
intros th Fth Hth.
pose proof (core_kf th Fth Hth) as K. cbv zeta in K. destruct K as (Fkf & Ekf & Hi & _).
apply (FastExpReduce.shifter_bits _ _ Fkf Ekf). lia.
Qed.

(** ** The steps *)

(** The table's pairs are rounded to nearest. *)
Lemma table_rn :
  forall i, (1 <= i <= 64)%Z ->
  let '(gh, gl) := DyadicAtan.atbl i in B2R gh = RN (B2R gh + B2R gl).
Proof.
intros i Hi.
(* [add gh gl = gh] for every entry, by computation. *)
assert (A : List.forallb (fun n => let '(gh, gl) := DyadicAtan.atbl (Z.of_nat n) in
  Model.eq (add gh gl) gh) (List.seq 1 64) = true) by (vm_compute; reflexivity).
rewrite List.forallb_forall in A.
specialize (A (Z.to_nat i) ltac:(apply List.in_seq; lia)).
rewrite Z2Nat.id in A by lia.
pose proof (fast_atan_table_correct i Hi) as T.
revert A T. destruct (DyadicAtan.atbl i) as (gh, gl). intros A T.
destruct T as (Fgh & Fgl & Hgh & Hgl & _).
change (bpow radix2 (-7)) with (/ 128) in Hgh.
change (bpow radix2 (-53)) with (/ 9007199254740992) in Hgl.
apply Rabs_le_inv in Hgl.
destruct (FastExpErr.add_e gh gl Fgh Fgl ltac:(apply Rabs_le; lra)) as (Fs & Es & _).
unfold Model.eq in A. rewrite Beqb_correct in A by assumption.
destruct (Req_bool_spec (B2R (add gh gl)) (B2R gh)) as [E|E]; [|discriminate].
rewrite Es in E. symmetry. exact E.
Qed.

(** [th c] is exact as a pair. *)
Lemma core_exact :
  forall fma th c, is_finite th = true -> is_finite c = true ->
  / 128 <= B2R th <= 129 / 128 -> / 64 <= B2R c <= 1 ->
  Generic.two_prod_is_exact fma th c (mul th c) = true.
Proof.
intros fma th c Fth Fc Hth Hc.
assert (P : / 8192 <= B2R th * B2R c <= 129 / 128).
{ split; [|nra]. apply Rle_trans with (/ 128 * / 64); [lra|].
  apply Rmult_le_compat; lra. }
destruct (FastExpErr.mul_e th c Fth Fc ltac:(rewrite Rabs_pos_eq; lra)) as (Fp & Ep & _).
assert (Hp : / 8192 <= B2R (mul th c) <= 2).
{ rewrite Ep. split.
  - change (/ 8192) with (bpow radix2 (-13)).
    apply round_ge_generic;
      [typeclasses eauto .. | | change (bpow radix2 (-13)) with (/ 8192); lra].
    apply generic_format_bpow. unfold FLT_exp. lia.
  - change 2 with (bpow radix2 1).
    apply round_le_generic;
      [typeclasses eauto .. | | change (bpow radix2 1) with 2; lra].
    apply generic_format_bpow. unfold FLT_exp. lia. }
apply two_prod_is_exact_of.
- split.
  + apply exponent_ge; [exact Fp|]. rewrite Rabs_pos_eq by lra.
    apply Rle_trans with (2 := proj1 Hp). change (/ 8192) with (bpow radix2 (-13)).
    apply bpow_le. lia.
  + cut (Generic.exponent (mul th c) < 2)%Z; [lia|].
    apply exponent_lt; [exact Fp | lia |]. rewrite Rabs_pos_eq by lra.
    change (bpow radix2 2) with 4. lra.
- cut (Generic.exponent th < 1)%Z; [lia|].
  apply exponent_lt; [exact Fth | lia |]. rewrite Rabs_pos_eq by lra.
  change (bpow radix2 1) with 2. lra.
- cut (Generic.exponent c < 1)%Z; [lia|].
  apply exponent_lt; [exact Fc | lia |]. rewrite Rabs_pos_eq by lra.
  change (bpow radix2 1) with 2. lra.
Qed.

(** The numerator [t - c]: [th - c] is exact (Sterbenz), and it is a
    multiple of the last bit of [th], above [|tl|] unless it is 0, so
    [fast_two_sum] is exact. Where [nh] is 0, so is [nl]. *)
Lemma core_num :
  forall th tl c n nh nl,
  is_finite th = true -> is_finite tl = true -> is_finite c = true ->
  / 128 <= B2R th <= 129 / 128 -> Rabs (B2R tl) <= bpow radix2 (-53) * B2R th ->
  (1 <= n <= 64)%Z -> Rabs (64 * B2R th - IZR n) <= / 2 -> B2R c = IZR n / 64 ->
  Fast.fast_two_sum (sub th c) tl = (nh, nl) ->
  is_finite nh = true /\ is_finite nl = true /\ B2R nh = RN (B2R th + B2R tl - B2R c) /\
  B2R nh + B2R nl = B2R th + B2R tl - B2R c /\ (B2R nh = 0 -> B2R nl = 0).
Proof.
intros th tl c n nh nl Fth Ftl Fc Hth Htl Hn Hi Ec E.
assert (B53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
assert (Hn' : 1 <= IZR n <= 64) by (split; apply IZR_le; lia).
apply Rabs_le_inv in Hi.
rewrite B53 in Htl. pose proof (Rabs_le_inv _ _ Htl) as Htl'.
(* [th - c] is exact (Sterbenz): [c / 2 <= th <= 2 c] as [n >= 1]. *)
assert (Gd : generic_format radix2 fexp64 (B2R th - B2R c)).
{ apply sterbenz; [typeclasses eauto .. | apply generic_format_B2R | apply generic_format_B2R |].
  rewrite Ec. split; lra. }
destruct (FastExpErr.sub_e th c Fth Fc) as (Fs & Es & _).
{ rewrite Ec. apply Rabs_le. lra. }
assert (Es' : B2R (sub th c) = B2R th - B2R c).
{ rewrite Es. apply round_generic; [typeclasses eauto|]. exact Gd. }
clear Es.
(* With [e] the exponent of the last bit of [th], [th - c] is a multiple
   of [2^e] ([c] is a multiple of [2^-6] and [e <= -51]), and
   [|tl| <= 2^-53 th < 2^e]. *)
set (e := cexp radix2 fexp64 (B2R th)).
assert (Ue : ulp radix2 fexp64 (B2R th) = bpow radix2 e) by (apply ulp_neq_0; lra).
assert (Hb : bpow radix2 (-1074 + 53 - 1) <= Rabs (B2R th)).
{ rewrite Rabs_pos_eq by lra. apply Rle_trans with (bpow radix2 (-7)); [apply bpow_le; lia|].
  change (bpow radix2 (-7)) with (/ 128). lra. }
pose proof (ulp_FLT_le radix2 (-1074) 53 (B2R th) Hb) as U1.
pose proof (ulp_FLT_gt radix2 (-1074) 53 (B2R th)) as U2.
rewrite Ue, Rabs_pos_eq in U1, U2 by lra.
assert (He : (e <= -51)%Z).
{ cut (e < -50)%Z; [lia|]. apply (lt_bpow radix2).
  change (bpow radix2 (1 - 53)) with (/ 4503599627370496) in U1.
  change (bpow radix2 (-50)) with (/ 1125899906842624). lra. }
assert (U2' : B2R th * / 9007199254740992 < bpow radix2 e) by exact U2.
clear U2.
assert (Gth : generic_format radix2 fexp64 (B2R th)) by apply generic_format_B2R.
destruct (FastExpReduce.format_mult_inv (B2R th) e Gth (Z.le_refl _))
  as (a & Ha).
assert (Hc2 : B2R c = IZR (n * Zpower radix2 (-6 - e)) * bpow radix2 e).
{ rewrite Ec, mult_IZR, IZR_Zpower by lia.
  rewrite Rmult_assoc, <- bpow_plus. replace (-6 - e + e)%Z with (-6)%Z by lia.
  change (bpow radix2 (-6)) with (/ 64). unfold Rdiv. reflexivity. }
set (k := (a - n * Zpower radix2 (-6 - e))%Z).
assert (Hd : B2R th - B2R c = IZR k * bpow radix2 e).
{ unfold k. rewrite minus_IZR, Rmult_minus_distr_r, <- Ha, <- Hc2. reflexivity. }
pose proof (bpow_gt_0 radix2 e) as Pe.
assert (Hab : Rabs (B2R tl) <= Rabs (B2R (sub th c)) \/ B2R (sub th c) = 0).
{ rewrite Es', Hd. destruct (Z.eq_dec k 0) as [K0|K0].
  - right. rewrite K0. ring.
  - left. rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 e)) by lra.
    assert (K1 : 1 <= Rabs (IZR k)) by (rewrite <- abs_IZR; apply IZR_le; lia).
    apply Rle_trans with (1 * bpow radix2 e); [lra|].
    apply Rmult_le_compat_r; lra. }
destruct (lc_fts (sub th c) tl nh nl Fs Ftl Hab) as (Fnh & Fnl & Rnh & Enh).
{ rewrite Es'. apply Rabs_le. lra. }
{ exact E. }
rewrite Es' in Rnh, Enh.
do 2 (split; [assumption|]).
split; [rewrite Rnh; f_equal; ring|].
split; [lra|].
(* Where [nh = 0]: [nl = RN (tl + (th - c - 0))] is [RN (th - c + tl) = nh]. *)
intros Z0.
unfold Fast.fast_two_sum in E. injection E as E1 E2.
destruct (FastExpErr.sub_e (sub th c) nh Fs Fnh) as (Fd & Ed & _).
{ rewrite Z0, Rminus_0_r, Es'. apply Rabs_le. lra. }
assert (Ed' : B2R (sub (sub th c) nh) = B2R th - B2R c).
{ rewrite Ed, Z0, Rminus_0_r, Es'. apply round_generic; [typeclasses eauto|]. exact Gd. }
destruct (FastExpErr.add_e tl (sub (sub th c) nh) Ftl Fd) as (_ & Ea & _).
{ rewrite Ed'. apply Rabs_le. lra. }
rewrite <- E2, E1, Ea, Ed', Rplus_comm, <- Rnh. exact Z0.
Qed.

(** Past the test against [2^-80], the numerator is in [dd_div]'s range. *)
Lemma core_nh :
  forall x (nh nl : f64), is_finite nh = true -> B2R nh = RN x -> B2R nh + B2R nl = x ->
  Rabs x <= / 64 -> Model.lt (fabs nh) DyadicAtan.two_m80 = false ->
  bpow radix2 (-80) <= Rabs (B2R nh) <= / 64 /\
  Rabs (B2R nl) <= bpow radix2 (-53) * Rabs (B2R nh).
Proof.
intros x nh nl Fnh Rnh Enh Hx E80.
assert (F80 : is_finite DyadicAtan.two_m80 = true) by reflexivity.
assert (Fa : is_finite (fabs nh) = true) by (unfold fabs; rewrite is_finite_Babs; exact Fnh).
apply lt_false in E80; [|exact Fa|exact F80].
unfold fabs in E80. rewrite B2R_Babs in E80.
lit DyadicAtan.two_m80 V80. rewrite V80 in E80.
assert (H80 : bpow radix2 (-80) <= Rabs (B2R nh)).
{ change (bpow radix2 (-80)) with (/ 1208925819614629174706176). lra. }
assert (Hle : Rabs (B2R nh) <= / 64).
{ rewrite Rnh. apply abs_round_le_generic; [typeclasses eauto .. | | exact Hx].
  change (/ 64) with (bpow radix2 (-6)).
  apply generic_format_bpow. unfold FLT_exp. lia. }
split; [split; assumption|].
replace (B2R nl) with (x - B2R nh) by lra.
apply low_rel; [exact Rnh|].
apply Rle_trans with (2 := H80). apply bpow_le. lia.
Qed.

(** The denominator [1 + t c]. *)
Lemma core_den :
  forall fma th tl c s s0 dh dl,
  is_finite th = true -> is_finite tl = true -> is_finite c = true ->
  / 128 <= B2R th <= 129 / 128 -> Rabs (B2R tl) <= bpow radix2 (-53) * B2R th ->
  / 64 <= B2R c <= 1 ->
  Fast.two_sum DyadicExp.one (mul th c) = (s, s0) ->
  Fast.fast_two_sum s (add s0 (add (Generic.two_prod_err fma th c (mul th c)) (mul tl c)))
    = (dh, dl) ->
  is_finite dh = true /\ is_finite dl = true /\ 1 <= B2R dh <= 41 / 20 /\
  Rabs (B2R dl) <= bpow radix2 (-53) * B2R dh /\
  Rabs (B2R dh + B2R dl - (1 + (B2R th + B2R tl) * B2R c)) <= bpow radix2 (-103).
Proof.
intros fma th tl c s s0 dh dl Fth Ftl Fc Hth Htl Hc ES ED.
pose proof (bpow_gt_0 radix2 (-1075)) as W0.
assert (W1 : bpow radix2 (-1075) <=
  / 1606938044258990275541962092341162602522202993782792835301376).
{ apply Rle_trans with (bpow radix2 (-200)); [apply bpow_le; lia|].
  change (bpow radix2 (-200))
    with (/ 1606938044258990275541962092341162602522202993782792835301376). lra. }
assert (F1 : is_finite DyadicExp.one = true) by (vm_compute; reflexivity).
assert (O1 : B2R DyadicExp.one = 1) by (lit DyadicExp.one HO; lra).
change (bpow radix2 (-53)) with (/ 9007199254740992) in Htl.
pose proof (Rabs_le_inv _ _ Htl) as Htl'.
assert (P : / 8192 <= B2R th * B2R c <= 129 / 128).
{ split; [|nra]. apply Rle_trans with (/ 128 * / 64); [lra|].
  apply Rmult_le_compat; lra. }
(* [p = RN (th c)], and [pe = th c - p] exactly. *)
destruct (two_prod_err_correct fma th c Fth Fc (core_exact fma th c Fth Fc Hth Hc))
  as (Fp & Ep & _ & Fpe & Epe).
pose proof (FastExpErr.rn_err (B2R th * B2R c)) as Ep_err.
rewrite <- Ep, (Rabs_pos_eq (B2R th * B2R c)) in Ep_err by lra.
set (p := mul th c) in *.
set (pe := Generic.two_prod_err fma th c p) in *.
change (bpow radix2 (-53)) with (/ 9007199254740992) in Ep_err.
pose proof (Rabs_le_inv _ _ Ep_err) as Ep'.
(* [s = RN (1 + p)] and [s0 = 1 + p - s]. *)
destruct (FastExpErr.add_e DyadicExp.one p F1 Fp) as (Fs & Es & _).
{ rewrite O1. apply Rabs_le. lra. }
assert (R1 : Rabs (B2R DyadicExp.one) < bpow radix2 1023).
{ rewrite O1, Rabs_R1. apply Rlt_le_trans with 2; [lra|].
  change 2 with (bpow radix2 1). apply bpow_le. lia. }
assert (R2 : Rabs (B2R p) < bpow radix2 1023).
{ apply Rle_lt_trans with 2; [apply Rabs_le; lra|].
  change 2 with (bpow radix2 1). apply bpow_lt. lia. }
pose proof (two_sum_correct DyadicExp.one p F1 Fp R1 R2 Fs) as TS.
rewrite ES in TS. destruct TS as (Sdef & Fs0 & Es0).
rewrite <- Sdef in Fs, Es.
rewrite O1 in Es, Es0.
pose proof (FastExpErr.rn_err (1 + B2R p)) as Es_err.
rewrite <- Es, (Rabs_pos_eq (1 + B2R p)) in Es_err by lra.
change (bpow radix2 (-53)) with (/ 9007199254740992) in Es_err.
pose proof (Rabs_le_inv _ _ Es_err) as Es'.
(* [m = RN (tl c)], [|tl c| <= 2^-53 129/128]. *)
assert (Hm : Rabs (B2R tl * B2R c) <= / 9007199254740992 * (129 / 128)).
{ rewrite Rabs_mult, (Rabs_pos_eq (B2R c)) by lra.
  apply Rle_trans with (Rabs (B2R tl) * 1); [|lra].
  apply Rmult_le_compat_l; [apply Rabs_pos | lra]. }
destruct (FastExpErr.mul_k tl c _ Ftl Fc Hm ltac:(lra)) as (Fm & _ & Em).
change (bpow radix2 (-53)) with (/ 9007199254740992) in Em.
set (m := mul tl c) in *.
pose proof (Rabs_le_inv _ _ Em) as Em'.
pose proof (Rabs_le_inv _ _ Hm) as Hm'.
(* [a1 = RN (pe + m)], [|pe + m| <= 2.02 2^-53]. *)
assert (HK1 : Rabs (B2R pe + B2R m) <= / 9007199254740992 * (101 / 50))
  by (apply Rabs_le; lra).
destruct (FastExpErr.add_k pe m _ Fpe Fm HK1 ltac:(lra)) as (Fa1 & _ & Ea1).
change (bpow radix2 (-53)) with (/ 9007199254740992) in Ea1.
set (a1 := add pe m) in *.
pose proof (Rabs_le_inv _ _ Ea1) as Ea1'.
(* [a2 = RN (s0 + a1)], [|s0 + a1| <= 4.04 2^-53]. *)
assert (HK2 : Rabs (B2R s0 + B2R a1) <= / 9007199254740992 * (101 / 25))
  by (apply Rabs_le; lra).
destruct (FastExpErr.add_k s0 a1 _ Fs0 Fa1 HK2 ltac:(lra)) as (Fa2 & _ & Ea2).
change (bpow radix2 (-53)) with (/ 9007199254740992) in Ea2.
set (a2 := add s0 a1) in *.
pose proof (Rabs_le_inv _ _ Ea2) as Ea2'.
(* [s >= 1 >= |a2|], so the last [fast_two_sum] is exact. *)
destruct (lc_fts s a2 dh dl Fs Fa2) as (Fdh & Fdl & Rdh & Edh).
{ left. rewrite (Rabs_pos_eq (B2R s)) by lra. apply Rabs_le. lra. }
{ apply Rabs_le. lra. }
{ exact ED. }
pose proof (FastExpErr.rn_err (B2R s + B2R a2)) as Edh_err.
rewrite <- Rdh, (Rabs_pos_eq (B2R s + B2R a2)) in Edh_err by lra.
change (bpow radix2 (-53)) with (/ 9007199254740992) in Edh_err.
pose proof (Rabs_le_inv _ _ Edh_err) as Edh'.
assert (Hdh : 1 <= B2R dh <= 41 / 20) by lra.
assert (Hdl : Rabs (B2R dl) <= bpow radix2 (-53) * Rabs (B2R dh)).
{ replace (B2R dl) with (B2R s + B2R a2 - B2R dh) by lra.
  apply low_rel; [exact Rdh|]. rewrite Rabs_pos_eq by lra.
  apply Rle_trans with 1; [|lra]. change 1 with (bpow radix2 0). apply bpow_le. lia. }
rewrite (Rabs_pos_eq (B2R dh)) in Hdl by lra.
change (bpow radix2 (-53)) with (/ 9007199254740992) in Hdl.
do 2 (split; [assumption|]). split; [exact Hdh|].
split.
{ change (bpow radix2 (-53)) with (/ 9007199254740992). lra. }
(* [dh + dl - (1 + t c) = (a2 - (s0 + a1)) + (a1 - (pe + m)) + (m - tl c)]:
   at most (4.04 + 2.02 + 1.01) 2^-106. *)
change (bpow radix2 (-103)) with (/ 10141204801825835211973625643008).
replace ((B2R th + B2R tl) * B2R c) with (B2R th * B2R c + B2R tl * B2R c) by ring.
apply Rabs_le. lra.
Qed.

(** The quotient [u] for a positive numerator. *)
Local Lemma core_q :
  forall fma nh nl dh dl D,
  is_finite nh = true -> is_finite nl = true -> is_finite dh = true -> is_finite dl = true ->
  bpow radix2 (-80) <= B2R nh <= / 64 -> Rabs (B2R nl) <= bpow radix2 (-53) * B2R nh ->
  B2R nh + B2R nl <= / 128 + bpow radix2 (-52) ->
  1 <= B2R dh <= 41 / 20 -> Rabs (B2R dl) <= bpow radix2 (-52) * B2R dh ->
  1 + bpow radix2 (-14) <= D -> Rabs (B2R dh + B2R dl - D) <= bpow radix2 (-103) ->
  let '(qh, ql) := Fast.dd_div fma nh nl dh dl in
  is_finite qh = true /\ is_finite ql = true /\
  bpow radix2 (-82) <= B2R qh <= bpow radix2 (-7) /\
  Rabs (B2R ql) <= bpow radix2 (-53) * B2R qh /\
  0 <= B2R qh + B2R ql <= bpow radix2 (-7) * (1 - bpow radix2 (-16)) /\
  Rabs (B2R qh + B2R ql - (B2R nh + B2R nl) / D) <= bpow radix2 (-97) * (B2R nh + B2R nl).
Proof.
intros fma nh nl dh dl D Fnh Fnl Fdh Fdl HN HL HS Hdh Hdl HD Ed.
assert (K : bpow radix2 (-53) = / 9007199254740992 /\ bpow radix2 (-52) = / 4503599627370496 /\
  bpow radix2 (-80) = / 1208925819614629174706176 /\
  bpow radix2 (-82) = / 4835703278458516698824704 /\
  bpow radix2 (-97) = / 158456325028528675187087900672 /\
  bpow radix2 (-98) = / 316912650057057350374175801344 /\
  bpow radix2 (-103) = / 10141204801825835211973625643008 /\
  bpow radix2 (-7) = / 128 /\ bpow radix2 (-16) = / 65536 /\ bpow radix2 (-14) = / 16384)
  by (repeat split; reflexivity).
destruct K as (K53 & K52 & K80 & K82 & K97 & K98 & K103 & K7 & K16 & K14).
pose proof (bpow_gt_0 radix2 (-80)) as P80.
assert (HL50 : Rabs (B2R nl) <= bpow radix2 (-50) * B2R nh).
{ apply Rle_trans with (1 := HL). apply Rmult_le_compat_r; [lra|]. apply bpow_le. lia. }
pose proof (dd_div_correct fma nh nl dh dl Fnh Fnl Fdh Fdl ltac:(lra) HL50 ltac:(lra) Hdl) as Hq.
destruct (Fast.dd_div fma nh nl dh dl) as [qh ql].
destruct Hq as (Fqh & Fql & Rq & Eq).
do 2 (split; [assumption|]).
rewrite K53 in HL. rewrite K52 in HS, Hdl. rewrite K80 in HN. rewrite K98 in Eq.
rewrite K103 in Ed. rewrite K14 in HD.
set (N := B2R nh + B2R nl) in *.
set (Dp := B2R dh + B2R dl) in *.
set (S := B2R qh + B2R ql) in *.
apply Rabs_le_inv in HL. apply Rabs_le_inv in Hdl. apply Rabs_le_inv in Ed.
assert (HN0 : / 1208925819614629174706176 * (1 - / 9007199254740992) <= N) by (unfold N; lra).
assert (HD0 : 1 + / 16384 - / 10141204801825835211973625643008 <= Dp) by lra.
assert (HD1 : Dp <= 41 / 20 * (1 + / 4503599627370496)).
{ unfold Dp. assert (B2R dh * / 4503599627370496 <= 41 / 20 * / 4503599627370496) by lra.
  lra. }
(* [Q = N / Dp], the exact quotient [dd_div] approximates. *)
set (Q := N / Dp) in *.
assert (HQD : Q * Dp = N) by (unfold Q; field; lra).
assert (Q0 : 0 <= Q).
{ unfold Q, Rdiv. apply Rmult_le_pos; [lra|]. apply Rlt_le, Rinv_0_lt_compat. lra. }
assert (QN : Q <= N).
{ assert (Q * 1 <= Q * Dp) by (apply Rmult_le_compat_l; lra). lra. }
assert (Qhi : Q * (1 + / 16384 - / 10141204801825835211973625643008) <= N).
{ rewrite <- HQD. apply Rmult_le_compat_l; lra. }
assert (Qlo : N <= Q * (41 / 20 * (1 + / 4503599627370496))).
{ rewrite <- HQD. apply Rmult_le_compat_l; lra. }
apply Rabs_le_inv in Eq.
(* [S] is within [2^-98 Q] of [Q], so in [[2^-82, 2^-7 (1 - 2^-16)]]. *)
assert (HS0 : 0 <= S <= / 128 * (1 - / 65536)) by lra.
assert (HS1 : / 4835703278458516698824704 <= S) by lra.
assert (Hqh : bpow radix2 (-82) <= B2R qh <= bpow radix2 (-7)).
{ split; rewrite Rq.
  - apply round_ge_generic; [typeclasses eauto .. | | rewrite K82; lra].
    apply generic_format_bpow. unfold FLT_exp. lia.
  - apply round_le_generic; [typeclasses eauto .. | | rewrite K7; lra].
    apply generic_format_bpow. unfold FLT_exp. lia. }
pose proof (bpow_gt_0 radix2 (-82)) as P82.
split; [exact Hqh|].
split.
{ replace (B2R ql) with (S - B2R qh) by (unfold S; ring).
  rewrite <- (Rabs_pos_eq (B2R qh)) at 2 by lra.
  apply low_rel; [exact Rq|]. rewrite Rabs_pos_eq by lra.
  apply Rle_trans with (2 := proj1 Hqh). apply bpow_le. lia. }
rewrite K7, K16. split; [exact HS0|].
(* [|Q - N / D| <= 2^-103 Q], as [(Q - N / D) D = Q (D - Dp)] and [D >= 1]. *)
set (R := N / D).
assert (HRD : R * D = N) by (unfold R; field; lra).
assert (HX : (Q - R) * D = Q * (D - Dp)) by lra.
assert (HQR : Rabs (Q - R) <= Q * / 10141204801825835211973625643008).
{ apply Rabs_le. clear - HX Q0 HD Ed. split; nra. }
apply Rabs_le_inv in HQR.
rewrite K97. apply Rabs_le. lra.
Qed.

(** [core_den]'s bound on [dl] in the weaker form that [core_u] takes. *)
Local Lemma den_low52 :
  forall dh dl : f64, 1 <= B2R dh <= 41 / 20 ->
  Rabs (B2R dl) <= bpow radix2 (-53) * B2R dh -> Rabs (B2R dl) <= bpow radix2 (-52) * B2R dh.
Proof.
intros dh dl Hdh Hdl. apply Rle_trans with (1 := Hdl).
apply Rmult_le_compat_r; [lra | apply bpow_le; lia].
Qed.

(** The quotient [u] with the sign of the numerator taken out. *)
Local Lemma core_u :
  forall fma nh nl dh dl D uh ul,
  is_finite nh = true -> is_finite nl = true -> is_finite dh = true -> is_finite dl = true ->
  bpow radix2 (-80) <= Rabs (B2R nh) <= / 64 ->
  Rabs (B2R nl) <= bpow radix2 (-53) * Rabs (B2R nh) ->
  Rabs (B2R nh + B2R nl) <= / 128 + bpow radix2 (-52) ->
  1 <= B2R dh <= 41 / 20 -> Rabs (B2R dl) <= bpow radix2 (-52) * B2R dh ->
  1 + bpow radix2 (-14) <= D -> Rabs (B2R dh + B2R dl - D) <= bpow radix2 (-103) ->
  (if Model.gt nh zero then Fast.dd_div fma nh nl dh dl
   else let '(qh, ql) := Fast.dd_div fma (Model.opp nh) (Model.opp nl) dh dl in
     (Model.opp qh, Model.opp ql)) = (uh, ul) ->
  is_finite uh = true /\ is_finite ul = true /\
  bpow radix2 (-82) <= Rabs (B2R uh) <= bpow radix2 (-7) /\
  Rabs (B2R ul) <= bpow radix2 (-53) * Rabs (B2R uh) /\
  Rabs (B2R uh + B2R ul) <= bpow radix2 (-7) * (1 - bpow radix2 (-16)) /\
  Rabs (B2R uh + B2R ul - (B2R nh + B2R nl) / D) <= bpow radix2 (-97) * Rabs (B2R nh + B2R nl).
Proof.
intros fma nh nl dh dl D uh ul Fnh Fnl Fdh Fdl HN HL HS Hdh Hdl HD Ed EU.
assert (F0 : is_finite zero = true) by reflexivity.
pose proof (bpow_gt_0 radix2 (-80)) as P80.
pose proof (bpow_gt_0 radix2 (-82)) as P82.
assert (B53 : bpow radix2 (-53) <= / 2) by (change (/ 2) with (bpow radix2 (-1)); apply bpow_le; lia).
pose proof (bpow_gt_0 radix2 (-53)) as P53.
destruct (Model.gt nh zero) eqn:G.
- apply gt_true in G; [|exact Fnh|exact F0].
  change (B2R zero) with 0 in G.
  rewrite (Rabs_pos_eq (B2R nh)) in HN, HL by lra.
  assert (HL' : B2R nl <= bpow radix2 (-53) * B2R nh /\ - (bpow radix2 (-53) * B2R nh) <= B2R nl)
    by (apply Rabs_le_inv in HL; lra).
  assert (P : 0 <= B2R nh + B2R nl).
  { assert (bpow radix2 (-53) * B2R nh <= / 2 * B2R nh) by (apply Rmult_le_compat_r; lra).
    lra. }
  rewrite (Rabs_pos_eq (B2R nh + B2R nl)) in HS |- * by exact P.
  pose proof (core_q fma nh nl dh dl D Fnh Fnl Fdh Fdl HN HL HS Hdh Hdl HD Ed) as Q.
  cbv beta iota in EU. rewrite EU in Q.
  destruct Q as (Fuh & Ful & Huh & Hul & Hs & He).
  rewrite (Rabs_pos_eq (B2R uh)) by lra.
  do 2 (split; [assumption|]). split; [exact Huh|]. split; [exact Hul|].
  split; [|exact He].
  rewrite Rabs_pos_eq by lra. exact (proj2 Hs).
- apply gt_false in G; [|exact Fnh|exact F0].
  change (B2R zero) with 0 in G.
  rewrite (Rabs_left1 (B2R nh)) in HN, HL by lra.
  assert (HL' : B2R nl <= bpow radix2 (-53) * - B2R nh /\
                - (bpow radix2 (-53) * - B2R nh) <= B2R nl)
    by (apply Rabs_le_inv in HL; lra).
  assert (P : B2R nh + B2R nl <= 0).
  { assert (bpow radix2 (-53) * - B2R nh <= / 2 * - B2R nh) by (apply Rmult_le_compat_r; lra).
    lra. }
  rewrite (Rabs_left1 (B2R nh + B2R nl)) in HS |- * by exact P.
  (* The numerator is negative: [dd_div] runs on [(-nh, -nl)]. *)
  assert (Fo : is_finite (Model.opp nh) = true)
    by (unfold Model.opp; rewrite is_finite_Bopp; exact Fnh).
  assert (Fol : is_finite (Model.opp nl) = true)
    by (unfold Model.opp; rewrite is_finite_Bopp; exact Fnl).
  assert (Eo : B2R (Model.opp nh) = - B2R nh) by (unfold Model.opp; apply B2R_Bopp).
  assert (Eol : B2R (Model.opp nl) = - B2R nl) by (unfold Model.opp; apply B2R_Bopp).
  pose proof (core_q fma (Model.opp nh) (Model.opp nl) dh dl D Fo Fol Fdh Fdl) as Q.
  rewrite Eo, Eol in Q.
  specialize (Q HN ltac:(rewrite Rabs_Ropp; exact HL) ltac:(lra) Hdh Hdl HD Ed).
  cbv beta iota in EU.
  destruct (Fast.dd_div fma (Model.opp nh) (Model.opp nl) dh dl) as [qh ql].
  destruct Q as (Fqh & Fql & Hqh & Hql & Hs & He).
  injection EU as <- <-.
  assert (Fuh : is_finite (Model.opp qh) = true)
    by (unfold Model.opp; rewrite is_finite_Bopp; exact Fqh).
  assert (Ful : is_finite (Model.opp ql) = true)
    by (unfold Model.opp; rewrite is_finite_Bopp; exact Fql).
  assert (Euh : B2R (Model.opp qh) = - B2R qh) by (unfold Model.opp; apply B2R_Bopp).
  assert (Eul : B2R (Model.opp ql) = - B2R ql) by (unfold Model.opp; apply B2R_Bopp).
  rewrite Euh, Eul, !Rabs_Ropp.
  rewrite (Rabs_pos_eq (B2R qh)) by lra.
  do 2 (split; [assumption|]). split; [exact Hqh|]. split; [exact Hql|].
  split.
  + replace (- B2R qh + - B2R ql) with (- (B2R qh + B2R ql)) by ring.
    rewrite Rabs_Ropp, Rabs_pos_eq by lra. exact (proj2 Hs).
  + replace (- B2R qh + - B2R ql - (B2R nh + B2R nl) / D)
      with (- (B2R qh + B2R ql - (- B2R nh + - B2R nl) / D)) by (unfold Rdiv; ring).
    rewrite Rabs_Ropp. replace (- (B2R nh + B2R nl)) with (- B2R nh + - B2R nl) by ring.
    exact He.
Qed.

(** The quotient is the same with and without an FMA. *)
Local Lemma core_u_fma :
  forall nh nl dh dl,
  is_finite nh = true -> is_finite nl = true -> is_finite dh = true -> is_finite dl = true ->
  bpow radix2 (-80) <= Rabs (B2R nh) <= / 64 ->
  Rabs (B2R nl) <= bpow radix2 (-53) * Rabs (B2R nh) ->
  1 <= B2R dh <= 41 / 20 -> Rabs (B2R dl) <= bpow radix2 (-52) * B2R dh ->
  (if Model.gt nh zero then Fast.dd_div true nh nl dh dl
   else let '(qh, ql) := Fast.dd_div true (Model.opp nh) (Model.opp nl) dh dl in
     (Model.opp qh, Model.opp ql)) =
  (if Model.gt nh zero then Fast.dd_div false nh nl dh dl
   else let '(qh, ql) := Fast.dd_div false (Model.opp nh) (Model.opp nl) dh dl in
     (Model.opp qh, Model.opp ql)).
Proof.
intros nh nl dh dl Fnh Fnl Fdh Fdl HN HL HD HE.
assert (F0 : is_finite zero = true) by reflexivity.
assert (B5 : bpow radix2 (-53) <= bpow radix2 (-50)) by (apply bpow_le; lia).
pose proof (bpow_gt_0 radix2 (-80)) as P80.
assert (HD' : / 2 <= B2R dh <= 4) by lra.
destruct (Model.gt nh zero) eqn:G.
- apply gt_true in G; [|exact Fnh|exact F0].
  change (B2R zero) with 0 in G.
  rewrite (Rabs_pos_eq (B2R nh)) in HN, HL by lra.
  apply dd_div_fma; try assumption; [lra|].
  apply Rle_trans with (1 := HL). apply Rmult_le_compat_r; lra.
- apply gt_false in G; [|exact Fnh|exact F0].
  change (B2R zero) with 0 in G.
  rewrite (Rabs_left1 (B2R nh)) in HN, HL by lra.
  (* The numerator is negative: [dd_div] runs on [(-nh, -nl)]. *)
  assert (Fo : is_finite (Model.opp nh) = true)
    by (unfold Model.opp; rewrite is_finite_Bopp; exact Fnh).
  assert (Fol : is_finite (Model.opp nl) = true)
    by (unfold Model.opp; rewrite is_finite_Bopp; exact Fnl).
  assert (Eo : B2R (Model.opp nh) = - B2R nh) by (unfold Model.opp; apply B2R_Bopp).
  assert (Eol : B2R (Model.opp nl) = - B2R nl) by (unfold Model.opp; apply B2R_Bopp).
  assert (E : Fast.dd_div true (Model.opp nh) (Model.opp nl) dh dl =
              Fast.dd_div false (Model.opp nh) (Model.opp nl) dh dl).
  { apply dd_div_fma; try assumption.
    - rewrite Eo. lra.
    - rewrite Eo, Eol, Rabs_Ropp. apply Rle_trans with (1 := HL).
      apply Rmult_le_compat_r; lra. }
  rewrite E. reflexivity.
Qed.

(** The final sum atan c + atan u. *)
Local Lemma core_fin :
  forall gh gl ph pl sh s1 ah al,
  is_finite gh = true -> is_finite gl = true -> is_finite ph = true -> is_finite pl = true ->
  / 128 <= B2R gh <= 4 / 5 -> Rabs (B2R gl) <= bpow radix2 (-53) * B2R gh ->
  B2R ph = RN (B2R ph + B2R pl) -> Rabs (B2R ph + B2R pl) <= / 128 ->
  / 512 <= B2R gh + B2R ph ->
  Fast.fast_two_sum gh ph = (sh, s1) ->
  Fast.fast_two_sum sh (add s1 (add gl pl)) = (ah, al) ->
  is_finite ah = true /\ is_finite al = true /\ B2R ah = RN (B2R ah + B2R al) /\
  Rabs (B2R ah + B2R al - (B2R gh + B2R gl + (B2R ph + B2R pl))) <= bpow radix2 (-104).
Proof.
intros gh gl ph pl sh s1 ah al Fgh Fgl Fph Fpl Hgh Hgl Rph Hp Hsum E1 E2.
pose proof (bpow_gt_0 radix2 (-1075)) as W0.
assert (W1 : bpow radix2 (-1075) <=
  / 1606938044258990275541962092341162602522202993782792835301376).
{ apply Rle_trans with (bpow radix2 (-200)); [apply bpow_le; lia|].
  change (bpow radix2 (-200))
    with (/ 1606938044258990275541962092341162602522202993782792835301376). lra. }
(* [|ph| <= 2^-7 <= gh], so the first [fast_two_sum] is exact. *)
assert (Hph : Rabs (B2R ph) <= / 128).
{ rewrite Rph. apply abs_round_le_generic; [typeclasses eauto .. | | exact Hp].
  change (/ 128) with (bpow radix2 (-7)). apply generic_format_bpow. unfold FLT_exp. lia. }
pose proof (Rabs_le_inv _ _ Hph) as Hph'.
pose proof (Rabs_le_inv _ _ Hp) as Hp'.
destruct (lc_fts gh ph sh s1 Fgh Fph) as (Fsh & Fs1 & Rsh & Es).
{ left. rewrite (Rabs_pos_eq (B2R gh)) by lra. lra. }
{ apply Rabs_le. lra. }
{ exact E1. }
(* [pl] and [s1] are rounding errors. *)
pose proof (FastExpErr.rn_err (B2R ph + B2R pl)) as Epl.
rewrite <- Rph in Epl.
replace (B2R ph - (B2R ph + B2R pl)) with (- B2R pl) in Epl by ring.
rewrite Rabs_Ropp in Epl.
pose proof (FastExpErr.rn_err (B2R gh + B2R ph)) as Es1.
rewrite <- Rsh in Es1.
replace (B2R sh - (B2R gh + B2R ph)) with (- B2R s1) in Es1 by lra.
rewrite Rabs_Ropp, (Rabs_pos_eq (B2R gh + B2R ph)) in Es1 by lra.
change (bpow radix2 (-53)) with (/ 9007199254740992) in Hgl, Epl, Es1.
pose proof (Rabs_le_inv _ _ Hgl) as Hgl'.
pose proof (Rabs_le_inv _ _ Epl) as Epl'.
pose proof (Rabs_le_inv _ _ Es1) as Es1'.
pose proof (Rabs_pos (B2R ph + B2R pl)) as Pp.
(* [e1 = RN (gl + pl)], [|gl + pl| <= 0.81 2^-53]. *)
assert (HK1 : Rabs (B2R gl + B2R pl) <= / 9007199254740992 * (81 / 100))
  by (apply Rabs_le; lra).
destruct (FastExpErr.add_k gl pl _ Fgl Fpl HK1 ltac:(lra)) as (Fe1 & _ & Ee1).
set (e1 := add gl pl) in *.
change (bpow radix2 (-53)) with (/ 9007199254740992) in Ee1.
pose proof (Rabs_le_inv _ _ Ee1) as Ee1'.
(* [e2 = RN (s1 + e1)], [|s1 + e1| <= 1.63 2^-53]. *)
assert (HK2 : Rabs (B2R s1 + B2R e1) <= / 9007199254740992 * (163 / 100))
  by (apply Rabs_le; lra).
destruct (FastExpErr.add_k s1 e1 _ Fs1 Fe1 HK2 ltac:(lra)) as (Fe2 & _ & Ee2).
set (e2 := add s1 e1) in *.
change (bpow radix2 (-53)) with (/ 9007199254740992) in Ee2.
pose proof (Rabs_le_inv _ _ Ee2) as Ee2'.
(* The second [fast_two_sum] is exact: [|e2| <= 2^-51 <= sh]. *)
destruct (lc_fts sh e2 ah al Fsh Fe2) as (Fah & Fal & Rah & Ea).
{ left. rewrite (Rabs_pos_eq (B2R sh)) by lra. apply Rabs_le. lra. }
{ apply Rabs_le. lra. }
{ exact E2. }
do 2 (split; [assumption|]).
split; [rewrite Ea; exact Rah|].
(* The error: [e2 - (s1 + e1) + (e1 - (gl + pl))], at most 2.44 2^-106. *)
rewrite Ea.
change (bpow radix2 (-104)) with (/ 20282409603651670423947251286016).
apply Rabs_le. lra.
Qed.

(** |atan x| <= |x|. *)
Local Lemma atan_abs : forall x, Rabs (atan x) <= Rabs x.
Proof.
intros x. pose proof (atan_lipschitz x 0) as H.
rewrite atan_0, !Rminus_0_r in H. exact H.
Qed.

(** The ranges of [t] and [c] past the index, and the bounds on the
    numerator and the denominator they give. *)
Lemma core_range :
  forall th tl c : f64, bpow radix2 (-61) <= B2R th <= 129 / 128 ->
  Rabs (B2R tl) <= bpow radix2 (-53) * B2R th -> / 64 <= B2R c <= 1 ->
  Rabs (64 * B2R th - 64 * B2R c) <= / 2 ->
  / 128 <= B2R th <= 129 / 128 /\
  Rabs (B2R th + B2R tl - B2R c) <= / 128 + bpow radix2 (-52) /\
  1 + bpow radix2 (-14) <= 1 + (B2R th + B2R tl) * B2R c.
Proof.
intros th tl c Hth Htl Hc Hi.
assert (B : bpow radix2 (-53) = / 9007199254740992 /\ bpow radix2 (-52) = / 4503599627370496 /\
            bpow radix2 (-14) = / 16384) by (repeat split; reflexivity).
destruct B as (B53 & B52 & B14). rewrite B53 in Htl. rewrite B52, B14.
apply Rabs_le_inv in Hi. apply Rabs_le_inv in Htl.
assert (Hth' : / 128 <= B2R th <= 129 / 128) by lra.
assert (P : / 128 * / 64 <= B2R th * B2R c) by (apply Rmult_le_compat; lra).
assert (Q : Rabs (B2R tl * B2R c) <= Rabs (B2R tl)).
{ rewrite Rabs_mult, (Rabs_pos_eq (B2R c)) by lra.
  pose proof (Rabs_pos (B2R tl)). nra. }
apply Rabs_le_inv in Q.
split; [exact Hth'|]. split; [apply Rabs_le; lra|]. nra.
Qed.

(** ** The theorems *)

Theorem fast_atan_core_correct :
  forall fma th tl ah al,
  is_finite th = true -> is_finite tl = true ->
  bpow radix2 (-61) <= B2R th <= 129 / 128 -> Rabs (B2R tl) <= bpow radix2 (-53) * B2R th ->
  DyadicAtan.fast_atan_core fma th tl = Some (ah, al) ->
  is_finite ah = true /\ is_finite al = true /\ B2R ah = RN (B2R ah + B2R al) /\
  Rabs (B2R ah + B2R al - atan (B2R th + B2R tl)) <= bpow radix2 (-74) * atan (B2R th + B2R tl).
Proof.
intros fma th tl ah al Fth Ftl Hth Htl H.
pose proof (core_index th Fth Hth) as HI. cbv zeta in HI.
cbv beta zeta delta [DyadicAtan.fast_atan_core] in H.
rewrite (core_bits th Fth Hth) in H.
set (kf := sub (add (mul th (from_bits 0x4050000000000000)) DyadicExp.shifter)
  DyadicExp.shifter) in H, HI.
set (i := DyadicExp.to_i64 kf) in H, HI.
set (c := mul kf (from_bits 0x3f90000000000000)) in H, HI.
destruct HI as (Hi & Hidx & Fc & Ec & Hi0).
pose proof (bpow_gt_0 radix2 (-61)) as P61.
(* [t] is positive, and atan t >= t / 2. *)
assert (Htl' : Rabs (B2R tl) <= / 9007199254740992 * B2R th)
  by (change (bpow radix2 (-53)) with (/ 9007199254740992) in Htl; exact Htl).
assert (Ht : 0 < B2R th + B2R tl <= 2) by (apply Rabs_le_inv in Htl'; lra).
assert (Hat : (B2R th + B2R tl) / 2 <= atan (B2R th + B2R tl)) by (apply atan_lower; lra).
destruct (Z.eqb_spec i 0) as [I0|I0].
- (* [64 th <= 1/2]: the polynomial alone. *)
  specialize (Hi0 I0).
  assert (R1 : bpow radix2 (-82) <= Rabs (B2R th) <= bpow radix2 (-7)).
  { rewrite Rabs_pos_eq by lra. split; [|exact Hi0].
    apply Rle_trans with (bpow radix2 (-61)); [apply bpow_le; lia | lra]. }
  assert (R2 : Rabs (B2R tl) <= bpow radix2 (-53) * Rabs (B2R th))
    by (rewrite (Rabs_pos_eq (B2R th)) by lra; exact Htl).
  pose proof (fast_atan_poly_correct fma th tl Fth Ftl R1 R2) as P.
  revert H P. destruct (DyadicAtan.fast_atan_poly fma th tl) as (ph, pl). intros H P.
  injection H as <- <-. destruct P as (Fph & Fpl & Rph & Ep).
  do 3 (split; [assumption|]).
  rewrite (Rabs_pos_eq (B2R th + B2R tl)) in Ep by lra.
  apply Rle_trans with (1 := Ep).
  change (bpow radix2 (-78)) with (/ 302231454903657293676544).
  change (bpow radix2 (-74)) with (/ 18889465931478580854784).
  lra.
- (* The table and the reduction. *)
  assert (I1 : (1 <= i <= 64)%Z) by lia.
  assert (Hic : 1 <= IZR i <= 64) by (split; apply IZR_le; lia).
  assert (Hc : / 64 <= B2R c <= 1) by (rewrite Ec; lra).
  destruct (core_range th tl c Hth Htl Hc) as (Hth' & HN & HD).
  { rewrite Ec. replace (64 * (IZR i / 64)) with (IZR i) by field. exact Hidx. }
  pose proof (fast_atan_table_correct i I1) as T.
  pose proof (table_rn i I1) as TR.
  revert H T TR. destruct (DyadicAtan.atbl i) as (gh, gl). intros H T TR.
  destruct T as (Fgh & Fgl & Hgh & Hgl & Eg).
  rewrite <- Ec in Eg.
  change (bpow radix2 (-7)) with (/ 128) in Hgh.
  revert H. destruct (Fast.fast_two_sum (sub th c) tl) as (nh, nl) eqn:EN. intros H.
  destruct (core_num th tl c i nh nl Fth Ftl Fc Hth' Htl I1 Hidx Ec EN)
    as (Fnh & Fnl & Rnh & Enh & Z0).
  revert H. destruct (eq nh zero) eqn:E0; intros H.
  + (* [t = c]: the table alone. *)
    apply (eq_zero_R nh Fnh) in E0. specialize (Z0 E0).
    injection H as <- <-.
    do 2 (split; [assumption|]). split; [exact TR|].
    replace (B2R th + B2R tl) with (B2R c) in * by lra.
    apply Rle_trans with (1 := Eg).
    change (bpow radix2 (-104)) with (/ 20282409603651670423947251286016).
    change (bpow radix2 (-74)) with (/ 18889465931478580854784).
    rewrite Ec in Hat |- *. lra.
  + revert H. destruct (Model.lt (fabs nh) DyadicAtan.two_m80) eqn:E80; intros H;
      [discriminate H|].
    destruct (core_nh (B2R th + B2R tl - B2R c) nh nl Fnh Rnh Enh) as (Hnh & Hnl);
      [|exact E80|].
    { apply Rle_trans with (1 := HN).
      change (bpow radix2 (-52)) with (/ 4503599627370496). lra. }
    revert H. destruct (Fast.two_sum DyadicExp.one (mul th c)) as (s, s0) eqn:ES. intros H.
    revert H.
    destruct (Fast.fast_two_sum s
      (add s0 (add (Generic.two_prod_err fma th c (mul th c)) (mul tl c)))) as (dh, dl) eqn:ED.
    intros H.
    destruct (core_den fma th tl c s s0 dh dl Fth Ftl Fc Hth' Htl Hc ES ED)
      as (Fdh & Fdl & Hdh & Hdl & Ed).
    apply (den_low52 dh dl Hdh) in Hdl.
    set (D := 1 + (B2R th + B2R tl) * B2R c) in *.
    revert H.
    destruct (if Model.gt nh zero then Fast.dd_div fma nh nl dh dl
      else let '(qh, ql) := Fast.dd_div fma (Model.opp nh) (Model.opp nl) dh dl in
        (Model.opp qh, Model.opp ql)) as (uh, ul) eqn:EU.
    intros H.
    rewrite <- Enh in HN.
    destruct (core_u fma nh nl dh dl D uh ul Fnh Fnl Fdh Fdl Hnh Hnl HN Hdh Hdl HD Ed EU)
      as (Fuh & Ful & Huh & Hul & Hu7 & Eu).
    pose proof (fast_atan_poly_correct fma uh ul Fuh Ful Huh Hul) as P.
    revert H P. destruct (DyadicAtan.fast_atan_poly fma uh ul) as (ph, pl). intros H P.
    destruct P as (Fph & Fpl & Rph & Ep).
    revert H. destruct (Fast.fast_two_sum gh ph) as (sh, s1) eqn:ES1. intros H.
    apply (f_equal (fun o => match o with Some v => v | None => (ah, al) end)) in H.
    cbv beta iota in H.
    (* The identity atan t = atan c + atan u and the error terms. *)
    pose proof (atan_sub_table (B2R th + B2R tl) (B2R c)) as Id.
    rewrite <- Enh in Id. fold D in Id.
    specialize (Id ltac:(lra) ltac:(lra)).
    set (u := B2R uh + B2R ul) in *.
    set (q := (B2R nh + B2R nl) / D) in *.
    set (t := B2R th + B2R tl) in *.
    pose proof (atan_abs u) as Au.
    pose proof (atan_lipschitz u q) as L.
    pose proof (FastExpErr.rn_err (B2R ph + B2R pl)) as Epl.
    rewrite <- Rph in Epl.
    replace (B2R ph - (B2R ph + B2R pl)) with (- B2R pl) in Epl by ring.
    rewrite Rabs_Ropp in Epl.
    set (w := bpow radix2 (-1075)) in Epl.
    assert (Hw : 0 < w <= / 1267650600228229401496703205376).
    { unfold w. split; [apply bpow_gt_0|].
      apply Rle_trans with (bpow radix2 (-100)); [apply bpow_le; lia|].
      change (bpow radix2 (-100)) with (/ 1267650600228229401496703205376). lra. }
    clearbody w.
    assert (Ht2 : / 129 <= t).
    { unfold t. apply Rabs_le_inv in Htl'. lra. }
    (* Every error term as a literal multiple of an atom. *)
    change (bpow radix2 (-78)) with (/ 302231454903657293676544) in Ep.
    change (bpow radix2 (-7)) with (/ 128) in Hu7.
    change (bpow radix2 (-16)) with (/ 65536) in Hu7.
    change (bpow radix2 (-97)) with (/ 158456325028528675187087900672) in Eu.
    change (bpow radix2 (-52)) with (/ 4503599627370496) in HN.
    change (bpow radix2 (-53)) with (/ 9007199254740992) in Hgl, Epl.
    change (bpow radix2 (-104)) with (/ 20282409603651670423947251286016) in Eg.
    pose proof (Rabs_le_inv _ _ Ep) as Ep'.
    pose proof (Rabs_le_inv _ _ Au) as Au'.
    pose proof (Rabs_le_inv _ _ Eg) as Eg'.
    pose proof (Rabs_le_inv _ _ Hgl) as Hgl'.
    pose proof (Rabs_le_inv _ _ L) as L'.
    pose proof (Rabs_pos u) as Pu.
    pose proof (Rabs_pos (u - q)) as Puq.
    pose proof (Rabs_pos (B2R nh + B2R nl)) as PN.
    (* [|ph + pl| <= |u| (1 + 2^-78) <= 2^-7]. *)
    assert (Hp : Rabs (B2R ph + B2R pl) <= / 128) by (apply Rabs_le; lra).
    pose proof (Rabs_le_inv _ _ Epl) as Epl'.
    pose proof (Rabs_pos (B2R ph + B2R pl)) as Pp.
    (* [gh + ph] is atan t up to errors far below atan t / 2. *)
    assert (Hsum : / 512 <= B2R gh + B2R ph) by lra.
    destruct (core_fin gh gl ph pl sh s1 ah al Fgh Fgl Fph Fpl Hgh Hgl Rph Hp Hsum ES1 H)
      as (Fah & Fal & Rah & Ea).
    do 3 (split; [assumption|]).
    change (bpow radix2 (-104)) with (/ 20282409603651670423947251286016) in Ea.
    change (bpow radix2 (-74)) with (/ 18889465931478580854784).
    pose proof (Rabs_le_inv _ _ Ea) as Ea'.
    (* The sum: 2^-104 + 2^-104 + 2^-78 |u| + 2^-97 |N| <= 2^-84 <= 2^-74 t / 2. *)
    apply Rabs_le. lra.
Qed.

Theorem fast_atan_core_fma :
  forall th tl,
  is_finite th = true -> is_finite tl = true ->
  bpow radix2 (-61) <= B2R th <= 129 / 128 -> Rabs (B2R tl) <= bpow radix2 (-53) * B2R th ->
  DyadicAtan.fast_atan_core true th tl = DyadicAtan.fast_atan_core false th tl.
Proof.
intros th tl Fth Ftl Hth Htl.
pose proof (core_index th Fth Hth) as HI. cbv zeta in HI.
cbv beta zeta delta [DyadicAtan.fast_atan_core].
rewrite (core_bits th Fth Hth).
set (kf := sub (add (mul th (from_bits 0x4050000000000000)) DyadicExp.shifter)
  DyadicExp.shifter) in HI |- *.
set (i := DyadicExp.to_i64 kf) in HI |- *.
set (c := mul kf (from_bits 0x3f90000000000000)) in HI |- *.
destruct HI as (Hi & Hidx & Fc & Ec & Hi0).
pose proof (bpow_gt_0 radix2 (-61)) as P61.
destruct (Z.eqb i 0) eqn:I0.
- (* The polynomial alone. *)
  apply Z.eqb_eq in I0. specialize (Hi0 I0).
  assert (R1 : bpow radix2 (-82) <= Rabs (B2R th) <= bpow radix2 (-7)).
  { rewrite Rabs_pos_eq by lra. split; [|exact Hi0].
    apply Rle_trans with (bpow radix2 (-61)); [apply bpow_le; lia | lra]. }
  assert (R2 : Rabs (B2R tl) <= bpow radix2 (-53) * Rabs (B2R th))
    by (rewrite (Rabs_pos_eq (B2R th)) by lra; exact Htl).
  rewrite (fast_atan_poly_fma th tl Fth Ftl R1 R2). reflexivity.
- apply Z.eqb_neq in I0.
  assert (I1 : (1 <= i <= 64)%Z) by lia.
  assert (Hic : 1 <= IZR i <= 64) by (split; apply IZR_le; lia).
  assert (Hc : / 64 <= B2R c <= 1) by (rewrite Ec; lra).
  destruct (core_range th tl c Hth Htl Hc) as (Hth' & HN & HD).
  { rewrite Ec. replace (64 * (IZR i / 64)) with (IZR i) by field. exact Hidx. }
  destruct (DyadicAtan.atbl i) as (gh, gl).
  destruct (Fast.fast_two_sum (sub th c) tl) as (nh, nl) eqn:EN.
  destruct (core_num th tl c i nh nl Fth Ftl Fc Hth' Htl I1 Hidx Ec EN)
    as (Fnh & Fnl & Rnh & Enh & _).
  destruct (eq nh zero); [reflexivity|].
  destruct (Model.lt (fabs nh) DyadicAtan.two_m80) eqn:E80; [reflexivity|].
  destruct (core_nh (B2R th + B2R tl - B2R c) nh nl Fnh Rnh Enh) as (Hnh & Hnl);
    [|exact E80|].
  { apply Rle_trans with (1 := HN).
    change (bpow radix2 (-52)) with (/ 4503599627370496). lra. }
  (* [th c] is exact either way, so its error is the same [f64]. *)
  rewrite (two_prod_err_fma_eq th c Fth Fc (core_exact true th c Fth Fc Hth' Hc)
    (core_exact false th c Fth Fc Hth' Hc)).
  destruct (Fast.two_sum DyadicExp.one (mul th c)) as (s, s0) eqn:ES.
  destruct (Fast.fast_two_sum s
    (add s0 (add (Generic.two_prod_err false th c (mul th c)) (mul tl c)))) as (dh, dl) eqn:ED.
  destruct (core_den false th tl c s s0 dh dl Fth Ftl Fc Hth' Htl Hc ES ED)
    as (Fdh & Fdl & Hdh & Hdl & Ed).
  apply (den_low52 dh dl Hdh) in Hdl.
  rewrite (core_u_fma nh nl dh dl Fnh Fnl Fdh Fdl Hnh Hnl Hdh Hdl).
  destruct (if Model.gt nh zero then Fast.dd_div false nh nl dh dl
    else let '(qh, ql) := Fast.dd_div false (Model.opp nh) (Model.opp nl) dh dl in
      (Model.opp qh, Model.opp ql)) as (uh, ul) eqn:EU.
  rewrite <- Enh in HN.
  destruct (core_u false nh nl dh dl _ uh ul Fnh Fnl Fdh Fdl Hnh Hnl HN Hdh Hdl HD Ed EU)
    as (Fuh & Ful & Huh & Hul & _).
  rewrite (fast_atan_poly_fma uh ul Fuh Ful Huh Hul). reflexivity.
Qed.
