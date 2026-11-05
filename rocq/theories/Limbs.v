(** * The loops of [src/limbs.rs]

    Each loop of [Limbs] in [Model.v] computes the operation on integers
    that the comment of its Rust function gives, for limbs that are
    [u64]s ([limbs_ok]). [KnuthStep.v] proves the steps of Algorithm D,
    and [Knuth.v] proves [div_rem]. *)

From Stdlib Require Import ZArith Lia List.
From Inari Require Import Model.

Open Scope Z_scope.

(** Each limb is a [u64]. *)
Definition limbs_ok (x : list Z) : Prop := Forall (fun a => 0 <= a < 2 ^ 64) x.

(** ** Helpers on [Z] *)

Lemma pow64_0 : 2 ^ (64 * Z.of_nat 0) = 1.
Proof. reflexivity. Qed.

Lemma pow64_pos : forall n, 0 < 2 ^ (64 * Z.of_nat n).
Proof. intros n. apply Z.pow_pos_nonneg; lia. Qed.

Lemma pow64_S : forall n, 2 ^ (64 * Z.of_nat (S n)) = 2 ^ 64 * 2 ^ (64 * Z.of_nat n).
Proof.
  intros n. rewrite Nat2Z.inj_succ, <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma pow64_add :
  forall a b, 2 ^ (64 * Z.of_nat (a + b)) = 2 ^ (64 * Z.of_nat a) * 2 ^ (64 * Z.of_nat b).
Proof.
  intros a b. rewrite Nat2Z.inj_add, <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(** The low digit and the rest of [a + B * v], for a digit [a] in base [B]. *)
Lemma mod_split :
  forall a v B C, 0 <= a < B -> 0 < C -> (a + B * v) mod (B * C) = a + B * (v mod C).
Proof.
  intros a v B C Ha HC.
  rewrite Z.rem_mul_r by lia.
  replace (a + B * v) with (a + v * B) by ring.
  rewrite Z.mod_add, Z.div_add by lia.
  rewrite Z.mod_small, Z.div_small by lia.
  reflexivity.
Qed.

Lemma div_split : forall a v B, 0 <= a < B -> (a + B * v) / B = v.
Proof.
  intros a v B Ha.
  replace (a + B * v) with (a + v * B) by ring.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

(** [Z.lor] of disjoint bits is [+]. *)
Lemma lor_low : forall h l s, 0 <= s -> 0 <= l < 2 ^ s -> Z.lor (h * 2 ^ s) l = h * 2 ^ s + l.
Proof.
  intros h l s Hs Hl.
  assert (H : Z.land (h * 2 ^ s) l = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i s) as [Hlt | Hge].
    - rewrite <- Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_spec_low by lia. reflexivity.
    - rewrite <- (Z.mod_small l (2 ^ s)) by lia.
      rewrite Z.mod_pow2_bits_high by lia. apply Bool.andb_false_r. }
  rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor by exact H. reflexivity.
Qed.

(** Bits [s..s + 64] of [W] only depend on its low 128 bits. *)
Lemma mod128_div_mod64 :
  forall W s, 0 <= s <= 64 -> (W mod 2 ^ 128 / 2 ^ s) mod 2 ^ 64 = (W / 2 ^ s) mod 2 ^ 64.
Proof.
  intros W s Hs. apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 64) as [Hlt | Hge].
  - rewrite !Z.mod_pow2_bits_low by lia.
    rewrite !Z.div_pow2_bits by lia.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma checked_u_ok : forall w z, 0 <= z < 2 ^ w -> checked_u w z = Some z.
Proof.
  intros w z H. unfold checked_u.
  replace ((0 <=? z) && (z <? 2 ^ w)) with true; [reflexivity |].
  symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma div_u_ok : forall a b, b <> 0 -> div_u a b = Some (a / b).
Proof.
  intros a b H. unfold div_u. rewrite (proj2 (Z.eqb_neq b 0) H). reflexivity.
Qed.

Lemma rem_u_ok : forall a b, b <> 0 -> rem_u a b = Some (a mod b).
Proof.
  intros a b H. unfold rem_u. rewrite (proj2 (Z.eqb_neq b 0) H). reflexivity.
Qed.

Lemma mod_sub_once : forall x B, B <= x < 2 * B -> x mod B = x - B.
Proof.
  intros x B H. symmetry. apply Z.mod_unique with 1; lia.
Qed.

Lemma mod_add_once : forall x B, - B <= x < 0 -> x mod B = x + B.
Proof.
  intros x B H. symmetry. apply Z.mod_unique with (-1); lia.
Qed.

Lemma b2z_bounds : forall b, 0 <= Z.b2z b <= 1.
Proof. intros []; cbn; lia. Qed.

(** [a.overflowing_add(b)] and [a.overflowing_sub(b)] *)
Lemma ovf_add_spec :
  forall a b t c,
  0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> Limbs.ovf_add a b = (t, c) ->
  0 <= t < 2 ^ 64 /\ a + b = t + 2 ^ 64 * Z.b2z c.
Proof.
  intros a b t c Ha Hb E. unfold Limbs.ovf_add in E.
  apply pair_equal_spec in E as [<- <-].
  destruct (Z.leb_spec (2 ^ 64) (a + b)) as [H | H]; cbn [Z.b2z].
  - rewrite mod_sub_once by lia. lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

Lemma ovf_sub_spec :
  forall a b t c,
  0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> Limbs.ovf_sub a b = (t, c) ->
  0 <= t < 2 ^ 64 /\ a - b = t - 2 ^ 64 * Z.b2z c.
Proof.
  intros a b t c Ha Hb E. unfold Limbs.ovf_sub in E.
  apply pair_equal_spec in E as [<- <-].
  destruct (Z.ltb_spec a b) as [H | H]; cbn [Z.b2z].
  - rewrite mod_add_once by lia. lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

(** ** Lists of limbs *)

Lemma limbs_ok_cons :
  forall a x, limbs_ok (a :: x) <-> 0 <= a < 2 ^ 64 /\ limbs_ok x.
Proof.
  intros a x. unfold limbs_ok. split.
  - intros H. inversion H. auto.
  - intros [Ha Hx]. constructor; auto.
Qed.

Lemma limbs_ok_app : forall x y, limbs_ok x -> limbs_ok y -> limbs_ok (x ++ y).
Proof.
  intros x y Hx Hy. unfold limbs_ok in *. apply Forall_app. split; assumption.
Qed.

Lemma limbs_ok_app_inv : forall x y, limbs_ok (x ++ y) -> limbs_ok x /\ limbs_ok y.
Proof.
  intros x y H. unfold limbs_ok in *. apply Forall_app. exact H.
Qed.

Lemma limbs_ok_repeat0 : forall k, limbs_ok (repeat 0 k).
Proof.
  induction k as [|k IH]; cbn [repeat].
  - constructor.
  - apply limbs_ok_cons. split; [lia | exact IH].
Qed.

Lemma limbs_ok_firstn : forall k x, limbs_ok x -> limbs_ok (firstn k x).
Proof.
  intros k x. revert k. induction x as [|a x IH]; intros k H; destruct k; cbn [firstn].
  - constructor.
  - constructor.
  - constructor.
  - apply limbs_ok_cons in H as [Ha Hx]. apply limbs_ok_cons.
    split; [exact Ha | apply IH; exact Hx].
Qed.

Lemma limbs_ok_skipn : forall k x, limbs_ok x -> limbs_ok (skipn k x).
Proof.
  intros k x. revert k. induction x as [|a x IH]; intros k H; destruct k; cbn [skipn].
  - constructor.
  - constructor.
  - exact H.
  - apply limbs_ok_cons in H as [Ha Hx]. apply IH. exact Hx.
Qed.

Lemma limbs_ok_update :
  forall out i w, limbs_ok out -> limbs_ok w -> limbs_ok (Limbs.update out i w).
Proof.
  intros out i w Hout Hw. unfold Limbs.update.
  apply limbs_ok_app; [apply limbs_ok_firstn; exact Hout |].
  apply limbs_ok_app; [exact Hw | apply limbs_ok_skipn; exact Hout].
Qed.

Lemma limb_bound : forall x i, limbs_ok x -> 0 <= Limbs.limb x i < 2 ^ 64.
Proof.
  intros x i H. unfold Limbs.limb.
  destruct (Nat.lt_ge_cases i (length x)) as [Hi | Hi].
  - unfold limbs_ok in H. rewrite Forall_forall in H. apply H. apply nth_In. exact Hi.
  - rewrite nth_overflow by exact Hi. lia.
Qed.

Lemma limb_cons_S : forall a x i, Limbs.limb (a :: x) (S i) = Limbs.limb x i.
Proof. reflexivity. Qed.

Lemma limb_cons_0 : forall a x, Limbs.limb (a :: x) 0 = a.
Proof. reflexivity. Qed.

Lemma hd_bound : forall x, limbs_ok x -> 0 <= hd 0 x < 2 ^ 64.
Proof.
  intros [|a x] H; cbn [hd].
  - lia.
  - apply limbs_ok_cons in H. tauto.
Qed.

Lemma tl_ok : forall x, limbs_ok x -> limbs_ok (tl x).
Proof.
  intros [|a x] H; cbn [tl].
  - exact H.
  - apply limbs_ok_cons in H. tauto.
Qed.

Lemma val_hd_tl : forall x, Limbs.val x = hd 0 x + 2 ^ 64 * Limbs.val (tl x).
Proof. intros [|a x]; cbn [Limbs.val hd tl]; lia. Qed.

Lemma val_app :
  forall x y,
  Limbs.val (x ++ y) = Limbs.val x + 2 ^ (64 * Z.of_nat (length x)) * Limbs.val y.
Proof.
  induction x as [|a x IH]; intros y; cbn [app Limbs.val length].
  - rewrite pow64_0. ring.
  - rewrite IH, pow64_S. ring.
Qed.

Lemma val_repeat0 : forall k, Limbs.val (repeat 0 k) = 0.
Proof.
  induction k as [|k IH]; cbn [repeat Limbs.val].
  - reflexivity.
  - rewrite IH. ring.
Qed.

Lemma val_bounds :
  forall x, limbs_ok x -> 0 <= Limbs.val x < 2 ^ (64 * Z.of_nat (length x)).
Proof.
  induction x as [|a x IH]; intros H; cbn [Limbs.val length].
  - rewrite pow64_0. lia.
  - apply limbs_ok_cons in H as [Ha Hx].
    specialize (IH Hx). rewrite pow64_S. lia.
Qed.

Lemma val_firstn :
  forall k x, limbs_ok x -> Limbs.val (firstn k x) = Limbs.val x mod 2 ^ (64 * Z.of_nat k).
Proof.
  intros k x. revert k. induction x as [|a x IH]; intros k H; destruct k; cbn [firstn Limbs.val].
  - rewrite pow64_0. reflexivity.
  - rewrite Z.mod_0_l; [reflexivity |]. pose proof (pow64_pos (S k)). lia.
  - rewrite pow64_0, Z.mod_1_r. reflexivity.
  - apply limbs_ok_cons in H as [Ha Hx].
    rewrite IH by exact Hx. rewrite pow64_S, mod_split; [reflexivity | lia | apply pow64_pos].
Qed.

Lemma val_skipn :
  forall k x, limbs_ok x -> Limbs.val (skipn k x) = Limbs.val x / 2 ^ (64 * Z.of_nat k).
Proof.
  intros k x. revert k. induction x as [|a x IH]; intros k H; destruct k; cbn [skipn Limbs.val].
  - rewrite pow64_0. reflexivity.
  - rewrite Z.div_0_l; [reflexivity |]. pose proof (pow64_pos (S k)). lia.
  - rewrite pow64_0, Z.div_1_r. reflexivity.
  - apply limbs_ok_cons in H as [Ha Hx].
    rewrite IH by exact Hx. rewrite pow64_S, <- Z.div_div by (pose proof (pow64_pos k); lia).
    rewrite div_split by lia. reflexivity.
Qed.

Lemma limb0_val : forall l, limbs_ok l -> Limbs.limb l 0 = Limbs.val l mod 2 ^ 64.
Proof.
  intros [|a l] H; cbn [Limbs.val].
  - reflexivity.
  - apply limbs_ok_cons in H as [Ha Hl]. rewrite limb_cons_0.
    replace (a + 2 ^ 64 * Limbs.val l) with (a + Limbs.val l * 2 ^ 64) by ring.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma limb_val :
  forall x i, limbs_ok x -> Limbs.limb x i = Limbs.val x / 2 ^ (64 * Z.of_nat i) mod 2 ^ 64.
Proof.
  intros x i H. rewrite <- val_skipn by exact H.
  assert (E : Limbs.limb x i = Limbs.limb (skipn i x) 0).
  { unfold Limbs.limb. rewrite nth_skipn, Nat.add_0_r. reflexivity. }
  rewrite E. apply limb0_val. apply limbs_ok_skipn. exact H.
Qed.

(** The top limb of a nonempty list. *)
Lemma val_last :
  forall x,
  x <> nil ->
  Limbs.val x =
  Limbs.val (firstn (length x - 1) x)
  + 2 ^ (64 * Z.of_nat (length x - 1)) * Limbs.limb x (length x - 1).
Proof.
  intros x H. destruct (exists_last H) as [x' [a ->]].
  replace (length (x' ++ a :: nil) - 1)%nat with (length x')
    by (rewrite length_app; cbn [length]; lia).
  rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
  unfold Limbs.limb. rewrite nth_middle.
  rewrite val_app. cbn [Limbs.val]. ring.
Qed.

Lemma update_length :
  forall out i w,
  (i + length w <= length out)%nat -> length (Limbs.update out i w) = length out.
Proof.
  intros out i w H. unfold Limbs.update.
  rewrite !length_app, length_firstn, length_skipn. lia.
Qed.

(** A list is its first [k] limbs and the rest. *)
Lemma val_split :
  forall k l,
  (k <= length l)%nat ->
  Limbs.val l = Limbs.val (firstn k l) + 2 ^ (64 * Z.of_nat k) * Limbs.val (skipn k l).
Proof.
  intros k l H. pose proof (val_app (firstn k l) (skipn k l)) as E.
  rewrite firstn_skipn, length_firstn, Nat.min_l in E by exact H. exact E.
Qed.

Lemma val_update :
  forall out i w,
  limbs_ok out -> (i + length w <= length out)%nat ->
  Limbs.val (Limbs.update out i w) =
  Limbs.val out
  + 2 ^ (64 * Z.of_nat i) * (Limbs.val w - Limbs.val (firstn (length w) (skipn i out))).
Proof.
  intros out i w Hout H.
  rewrite (val_split i out) by lia.
  rewrite (val_split (length w) (skipn i out)) by (rewrite length_skipn; lia).
  rewrite skipn_skipn.
  unfold Limbs.update. rewrite !val_app, length_firstn, Nat.min_l by lia.
  rewrite (Nat.add_comm (length w) i). ring.
Qed.

(** [firstn (S k)] adds limb [k]. *)
Lemma val_firstn_S :
  forall k l,
  Limbs.val (firstn (S k) l) = Limbs.val (firstn k l) + 2 ^ (64 * Z.of_nat k) * Limbs.limb l k.
Proof.
  intros k l. revert k. induction l as [|a l IH]; intros k.
  - rewrite !firstn_nil. unfold Limbs.limb. destruct k; cbn [nth Limbs.val]; ring.
  - destruct k as [|k].
    + cbn [firstn Limbs.val]. rewrite pow64_0, limb_cons_0. ring.
    + rewrite !firstn_cons. cbn [Limbs.val]. rewrite IH, limb_cons_S, pow64_S. ring.
Qed.

(** ** The loops *)

Lemma rposition_nonzero_correct :
  forall x,
  limbs_ok x ->
  match Limbs.rposition_nonzero x with
  | None => Limbs.val x = 0
  | Some i =>
      (i < length x)%nat /\ Limbs.limb x i <> 0 /\
      2 ^ (64 * Z.of_nat i) <= Limbs.val x < 2 ^ (64 * Z.of_nat (S i))
  end.
Proof.
  induction x as [|a x IH]; intros H.
  - reflexivity.
  - apply limbs_ok_cons in H as [Ha Hx]. specialize (IH Hx).
    cbn [Limbs.rposition_nonzero].
    revert IH. destruct (Limbs.rposition_nonzero x) as [i |]; intros IH; cbv beta iota in IH.
    + destruct IH as [Hi [Hl [Hlo Hhi]]].
      cbn [length Limbs.val]. rewrite limb_cons_S.
      rewrite (pow64_S (S i)). rewrite (pow64_S i) in *.
      split; [lia |]. split; [exact Hl |]. lia.
    + destruct (Z.eqb_spec a 0) as [Ha0 | Ha0].
      * cbn [Limbs.val]. rewrite IH, Ha0. ring.
      * cbn [length Limbs.val]. rewrite IH, limb_cons_0, pow64_0, pow64_S, pow64_0.
        split; [lia |]. split; [exact Ha0 | lia].
Qed.

Lemma bit_len_correct : forall x, limbs_ok x -> Limbs.bit_len x = nat_bits (Limbs.val x).
Proof.
  intros x H. unfold Limbs.bit_len, nat_bits.
  pose proof (rposition_nonzero_correct x H) as Hr. revert Hr.
  destruct (Limbs.rposition_nonzero x) as [i |]; intros Hr; cbv beta iota in Hr.
  - destruct Hr as [Hi [Ha [Hlo Hhi]]].
    rewrite pow64_S in Hhi.
    pose proof (pow64_pos i) as HQ.
    pose proof (limb_bound x i H) as Hab.
    assert (Ea : Limbs.limb x i = Limbs.val x / 2 ^ (64 * Z.of_nat i)).
    { rewrite limb_val by exact H. apply Z.mod_small.
      split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    assert (Ha0 : 0 < Limbs.limb x i) by lia.
    unfold leading_zeros. rewrite (proj2 (Z.eqb_neq _ 0) Ha).
    rewrite (proj2 (Z.eqb_neq (Limbs.val x) 0)) by lia.
    assert (Hl : Z.log2 (Limbs.val x) = 64 * Z.of_nat i + Z.log2 (Limbs.limb x i)).
    { pose proof (Z.log2_spec _ Ha0) as [Hl1 Hl2].
      pose proof (Z.log2_nonneg (Limbs.limb x i)).
      pose proof (Z.mul_div_le (Limbs.val x) _ HQ) as Hd1.
      pose proof (Z.mul_succ_div_gt (Limbs.val x) _ HQ) as Hd2.
      rewrite <- Ea in Hd1, Hd2.
      apply Z.log2_unique; [lia |].
      rewrite <- Z.add_succ_r, !Z.pow_add_r by lia.
      split.
      - apply Z.le_trans with (2 ^ (64 * Z.of_nat i) * Limbs.limb x i); [| exact Hd1].
        apply Z.mul_le_mono_nonneg_l; lia.
      - apply Z.lt_le_trans with (2 ^ (64 * Z.of_nat i) * Z.succ (Limbs.limb x i));
          [exact Hd2 |].
        apply Z.mul_le_mono_nonneg_l; lia. }
    rewrite Hl. lia.
  - rewrite Hr. reflexivity.
Qed.

(** Comparing [fx + P a] and [fy + P b] for digits [fx, fy < P]. *)
Lemma compare_digit :
  forall P fx fy a b,
  0 < P -> 0 <= fx < P -> 0 <= fy < P ->
  (if negb (a =? b) then Z.compare a b else Z.compare fx fy) =
  Z.compare (fx + P * a) (fy + P * b).
Proof.
  intros P fx fy a b HP Hx Hy.
  destruct (Z.eqb_spec a b) as [Hab | Hab]; cbn [negb].
  - subst b. rewrite !(Z.add_comm _ (P * a)), Z.add_compare_mono_l. reflexivity.
  - destruct (Z.compare_spec a b) as [Hc | Hc | Hc]; symmetry.
    + contradiction.
    + apply Z.compare_lt_iff. assert (P * a + P <= P * b) by nia. lia.
    + apply Z.compare_gt_iff. assert (P * b + P <= P * a) by nia. lia.
Qed.

Lemma cmp_from_correct :
  forall k x y,
  limbs_ok x -> limbs_ok y ->
  Limbs.cmp_from x y k = Z.compare (Limbs.val (firstn k x)) (Limbs.val (firstn k y)).
Proof.
  induction k as [|i IH]; intros x y Hx Hy.
  - reflexivity.
  - cbn [Limbs.cmp_from]. rewrite IH by assumption. rewrite !val_firstn_S.
    rewrite (val_firstn i x Hx), (val_firstn i y Hy).
    pose proof (pow64_pos i) as HP.
    apply compare_digit; [exact HP | apply Z.mod_pos_bound; exact HP |
                          apply Z.mod_pos_bound; exact HP].
Qed.

Lemma cmp_correct :
  forall x y,
  limbs_ok x -> limbs_ok y -> Limbs.cmp x y = Z.compare (Limbs.val x) (Limbs.val y).
Proof.
  intros x y Hx Hy. unfold Limbs.cmp. rewrite cmp_from_correct by assumption.
  rewrite !firstn_all2 by lia. reflexivity.
Qed.

Lemma add_assign_from_correct :
  forall x y c s c',
  limbs_ok x -> limbs_ok y -> (length y <= length x)%nat ->
  Limbs.add_assign_from x y c = (s, c') ->
  limbs_ok s /\ length s = length x /\
  Limbs.val s + Z.b2z c' * 2 ^ (64 * Z.of_nat (length x)) =
  Limbs.val x + Limbs.val y + Z.b2z c.
Proof.
  induction x as [|a x IH]; intros y c s c' Hx Hy Hl E.
  - destruct y as [|b y]; [| cbn [length] in Hl; lia].
    cbn [Limbs.add_assign_from] in E. apply pair_equal_spec in E as [<- <-].
    split; [constructor |]. split; [reflexivity |].
    cbn [Limbs.val length]. rewrite pow64_0. ring.
  - apply limbs_ok_cons in Hx as [Ha Hx].
    cbn [Limbs.add_assign_from] in E.
    destruct (Limbs.ovf_add a (hd 0 y)) as [t1 c1] eqn:E1. cbv beta iota zeta in E.
    destruct (Limbs.ovf_add t1 (Z.b2z c)) as [t2 c2] eqn:E2. cbv beta iota zeta in E.
    destruct (Limbs.add_assign_from x (tl y) (c1 || c2)) as [r cr] eqn:E3.
    cbv beta iota zeta in E.
    apply pair_equal_spec in E as [<- <-].
    pose proof (hd_bound y Hy) as Hhd. pose proof (b2z_bounds c) as Hc.
    apply ovf_add_spec in E1 as [Ht1 E1]; [| lia | lia].
    apply ovf_add_spec in E2 as [Ht2 E2]; [| lia | lia].
    assert (Htl : (length (tl y) <= length x)%nat)
      by (destruct y; cbn [length tl] in *; lia).
    destruct (IH (tl y) (c1 || c2) r cr Hx (tl_ok y Hy) Htl E3) as [Hr [Hrl Hrv]].
    assert (Hb : Z.b2z (c1 || c2) = Z.b2z c1 + Z.b2z c2)
      by (destruct c1, c2; cbn [orb Z.b2z] in *; lia).
    split; [apply limbs_ok_cons; split; assumption |].
    split; [cbn [length]; congruence |].
    cbn [Limbs.val length]. rewrite pow64_S, (val_hd_tl y). lia.
Qed.

Lemma add_assign_correct :
  forall x y s c,
  limbs_ok x -> limbs_ok y -> (length y <= length x)%nat ->
  Limbs.add_assign x y = (s, c) ->
  limbs_ok s /\ length s = length x /\
  Limbs.val s + Z.b2z c * 2 ^ (64 * Z.of_nat (length x)) = Limbs.val x + Limbs.val y.
Proof.
  intros x y s c Hx Hy Hl E. unfold Limbs.add_assign in E.
  destruct (add_assign_from_correct x y false s c Hx Hy Hl E) as [H1 [H2 H3]].
  cbn [Z.b2z] in H3. rewrite Z.add_0_r in H3. auto.
Qed.

Lemma sub_assign_correct :
  forall x y b s c,
  limbs_ok x -> limbs_ok y -> (length y <= length x)%nat ->
  Limbs.sub_assign x y b = (s, c) ->
  limbs_ok s /\ length s = length x /\
  Limbs.val s - Z.b2z c * 2 ^ (64 * Z.of_nat (length x)) =
  Limbs.val x - Limbs.val y - Z.b2z b.
Proof.
  induction x as [|a x IH]; intros y b s c Hx Hy Hl E.
  - destruct y as [|d y]; [| cbn [length] in Hl; lia].
    cbn [Limbs.sub_assign] in E. apply pair_equal_spec in E as [<- <-].
    split; [constructor |]. split; [reflexivity |].
    cbn [Limbs.val length]. rewrite pow64_0. ring.
  - apply limbs_ok_cons in Hx as [Ha Hx].
    cbn [Limbs.sub_assign] in E.
    destruct (Limbs.ovf_sub a (hd 0 y)) as [t1 b1] eqn:E1. cbv beta iota zeta in E.
    destruct (Limbs.ovf_sub t1 (Z.b2z b)) as [t2 b2] eqn:E2. cbv beta iota zeta in E.
    destruct (Limbs.sub_assign x (tl y) (b1 || b2)) as [r br] eqn:E3.
    cbv beta iota zeta in E.
    apply pair_equal_spec in E as [<- <-].
    pose proof (hd_bound y Hy) as Hhd. pose proof (b2z_bounds b) as Hb0.
    apply ovf_sub_spec in E1 as [Ht1 E1]; [| lia | lia].
    apply ovf_sub_spec in E2 as [Ht2 E2]; [| lia | lia].
    assert (Htl : (length (tl y) <= length x)%nat)
      by (destruct y; cbn [length tl] in *; lia).
    destruct (IH (tl y) (b1 || b2) r br Hx (tl_ok y Hy) Htl E3) as [Hr [Hrl Hrv]].
    assert (Hb : Z.b2z (b1 || b2) = Z.b2z b1 + Z.b2z b2)
      by (destruct b1, b2; cbn [orb Z.b2z] in *; lia).
    split; [apply limbs_ok_cons; split; assumption |].
    split; [cbn [length]; congruence |].
    cbn [Limbs.val length]. rewrite pow64_S, (val_hd_tl y). lia.
Qed.

Lemma mul_add_limb_correct :
  forall x m a,
  limbs_ok x -> 0 <= m < 2 ^ 64 -> 0 <= a < 2 ^ 64 ->
  exists s c,
  Limbs.mul_add_limb x m a = Some (s, c) /\ limbs_ok s /\ length s = length x /\
  0 <= c < 2 ^ 64 /\
  Limbs.val s + c * 2 ^ (64 * Z.of_nat (length x)) = Limbs.val x * m + a.
Proof.
  induction x as [|l x IH]; intros m a Hx Hm Ha.
  - exists nil, a. cbn [Limbs.mul_add_limb Limbs.val length]. rewrite pow64_0.
    split; [reflexivity |]. split; [constructor |]. split; [reflexivity |].
    split; [lia | ring].
  - apply limbs_ok_cons in Hx as [Hl Hx].
    assert (Hlm : 0 <= l * m <= (2 ^ 64 - 1) * (2 ^ 64 - 1)).
    { split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]. }
    cbn [Limbs.mul_add_limb].
    remember (l * m + a) as t eqn:Et.
    assert (Ht : 0 <= t < 2 ^ 128) by lia.
    assert (Htd : 0 <= t / 2 ^ 64 < 2 ^ 64).
    { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    rewrite checked_u_ok by exact Ht. cbv beta iota zeta.
    rewrite Z.shiftr_div_pow2 by lia. rewrite (Z.mod_small (t / 2 ^ 64) (2 ^ 64)) by exact Htd.
    destruct (IH m (t / 2 ^ 64) Hx Hm Htd) as [r [c [E [Hr [Hrl [Hc Hv]]]]]].
    rewrite E. cbv beta iota zeta. exists (t mod 2 ^ 64 :: r), c.
    split; [reflexivity |].
    split; [apply limbs_ok_cons; split; [apply Z.mod_pos_bound; lia | exact Hr] |].
    split; [cbn [length]; congruence |].
    split; [exact Hc |].
    cbn [Limbs.val length]. rewrite pow64_S.
    pose proof (Z.div_mod t (2 ^ 64) ltac:(lia)) as Ed.
    lia.
Qed.

Lemma mul_add_row_from_correct :
  forall row y a carry,
  limbs_ok row -> limbs_ok y -> length row = length y ->
  0 <= a < 2 ^ 64 -> 0 <= carry < 2 ^ 64 ->
  exists r c,
  Limbs.mul_add_row_from row y a carry = Some (r, c) /\ limbs_ok r /\
  length r = length row /\ 0 <= c < 2 ^ 64 /\
  Limbs.val r + c * 2 ^ (64 * Z.of_nat (length row)) =
  Limbs.val row + a * Limbs.val y + carry.
Proof.
  induction row as [|o row IH]; intros y a carry Hr Hy Hl Ha Hc.
  - destruct y as [|b y]; [| cbn [length] in Hl; discriminate].
    exists nil, carry. cbn [Limbs.mul_add_row_from Limbs.val length]. rewrite pow64_0.
    split; [reflexivity |]. split; [constructor |]. split; [reflexivity |].
    split; [lia | ring].
  - destruct y as [|b y]; [cbn [length] in Hl; discriminate |].
    apply limbs_ok_cons in Hr as [Ho Hr]. apply limbs_ok_cons in Hy as [Hb Hy].
    cbn [length] in Hl. injection Hl as Hl.
    assert (Hab : 0 <= a * b <= (2 ^ 64 - 1) * (2 ^ 64 - 1)).
    { split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]. }
    cbn [Limbs.mul_add_row_from].
    remember (a * b + o + carry) as t eqn:Et.
    assert (Ht : 0 <= t < 2 ^ 128) by lia.
    assert (Htd : 0 <= t / 2 ^ 64 < 2 ^ 64).
    { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    rewrite checked_u_ok by exact Ht. cbv beta iota zeta.
    rewrite Z.shiftr_div_pow2 by lia.
    destruct (IH y a (t / 2 ^ 64) Hr Hy Hl Ha Htd) as [r [c [E [Hr' [Hrl [Hc' Hv]]]]]].
    rewrite E. cbv beta iota zeta. exists (t mod 2 ^ 64 :: r), c.
    split; [reflexivity |].
    split; [apply limbs_ok_cons; split; [apply Z.mod_pos_bound; lia | exact Hr'] |].
    split; [cbn [length]; congruence |].
    split; [exact Hc' |].
    cbn [Limbs.val length]. rewrite pow64_S.
    pose proof (Z.div_mod t (2 ^ 64) ltac:(lia)) as Ed.
    lia.
Qed.

Lemma mul_add_row_correct :
  forall row y a,
  limbs_ok row -> limbs_ok y -> length row = length y -> 0 <= a < 2 ^ 64 ->
  exists r c,
  Limbs.mul_add_row row y a = Some (r, c) /\ limbs_ok r /\
  length r = length row /\ 0 <= c < 2 ^ 64 /\
  Limbs.val r + c * 2 ^ (64 * Z.of_nat (length row)) = Limbs.val row + a * Limbs.val y.
Proof.
  intros row y a Hr Hy Hl Ha. unfold Limbs.mul_add_row.
  assert (H0 : 0 <= 0 < 2 ^ 64) by lia.
  destruct (mul_add_row_from_correct row y a 0 Hr Hy Hl Ha H0)
    as [r [c [E [Hr' [Hrl [Hc Hv]]]]]].
  rewrite E. cbv beta iota zeta. exists r, (c mod 2 ^ 64).
  rewrite (Z.mod_small c (2 ^ 64)) by exact Hc.
  split; [reflexivity |]. split; [exact Hr' |]. split; [exact Hrl |].
  split; [exact Hc | lia].
Qed.

(** The rows of [mul_into] from limb [length pre] of [x = pre ++ xs] on:
    [out] holds [val pre * val y] so far. *)
Lemma mul_into_from_correct :
  forall xs pre out y,
  limbs_ok xs -> limbs_ok pre -> limbs_ok y -> limbs_ok out ->
  length out = (length pre + length xs + length y)%nat ->
  Limbs.val out = Limbs.val pre * Limbs.val y ->
  exists out',
  Limbs.mul_into_from out xs y (length pre) = Some out' /\ limbs_ok out' /\
  length out' = length out /\ Limbs.val out' = Limbs.val (pre ++ xs) * Limbs.val y.
Proof.
  induction xs as [|a xs IH]; intros pre out y Hxs Hpre Hy Hout Hlen Hval.
  - exists out. cbn [Limbs.mul_into_from]. rewrite app_nil_r. auto.
  - apply limbs_ok_cons in Hxs as [Ha Hxs]. cbn [length] in Hlen.
    cbn [Limbs.mul_into_from].
    assert (Hrow : limbs_ok (firstn (length y) (skipn (length pre) out)))
      by (apply limbs_ok_firstn, limbs_ok_skipn; exact Hout).
    assert (Hrowl : length (firstn (length y) (skipn (length pre) out)) = length y)
      by (rewrite length_firstn, length_skipn; lia).
    destruct (mul_add_row_correct _ y a Hrow Hy Hrowl Ha) as [r [c [E [Hr [Hrl [Hc Hv]]]]]].
    rewrite E. cbv beta iota zeta.
    rewrite Hrowl in Hv.
    (* The limb above the row is still 0: [val out < 2^(64 (length pre + length y))]. *)
    pose proof (val_bounds pre Hpre) as Bp. pose proof (val_bounds y Hy) as By.
    pose proof (val_bounds out Hout) as Bo.
    assert (Hlt : Limbs.val out < 2 ^ (64 * Z.of_nat (length pre + length y))).
    { rewrite pow64_add, Hval. apply Z.mul_lt_mono_nonneg; lia. }
    assert (Htop : Limbs.limb (skipn (length pre) out) (length y) = 0).
    { unfold Limbs.limb. rewrite nth_skipn. fold (Limbs.limb out (length pre + length y)).
      rewrite limb_val by exact Hout. rewrite Z.div_small by lia. reflexivity. }
    assert (Hw : limbs_ok (r ++ c :: nil))
      by (apply limbs_ok_app; [exact Hr | apply limbs_ok_cons; split; [exact Hc | constructor]]).
    assert (Hwl : length (r ++ c :: nil) = S (length y))
      by (rewrite length_app, Hrl, Hrowl; cbn [length]; lia).
    assert (Hfit : (length pre + length (r ++ c :: nil) <= length out)%nat)
      by (rewrite Hwl; lia).
    assert (Hpre' : limbs_ok (pre ++ a :: nil))
      by (apply limbs_ok_app; [exact Hpre | apply limbs_ok_cons; split; [exact Ha | constructor]]).
    assert (Hlen' : length (Limbs.update out (length pre) (r ++ c :: nil)) =
                    (length (pre ++ a :: nil) + length xs + length y)%nat).
    { rewrite update_length by exact Hfit. rewrite length_app. cbn [length]. lia. }
    assert (Hval' : Limbs.val (Limbs.update out (length pre) (r ++ c :: nil)) =
                    Limbs.val (pre ++ a :: nil) * Limbs.val y).
    { rewrite val_update by assumption. rewrite Hwl, val_firstn_S, Htop.
      rewrite !val_app, Hrl, Hrowl. cbn [Limbs.val].
      (* The row adds [a * val y] at limb [length pre]. *)
      assert (Er : Limbs.val r =
                   Limbs.val (firstn (length y) (skipn (length pre) out)) + a * Limbs.val y
                   - c * 2 ^ (64 * Z.of_nat (length y))) by lia.
      rewrite Er, Hval. ring. }
    destruct (IH (pre ++ a :: nil) (Limbs.update out (length pre) (r ++ c :: nil)) y
                 Hxs Hpre' Hy (limbs_ok_update _ _ _ Hout Hw) Hlen' Hval')
      as [out' [E' [Ho' [Hol' Hov']]]].
    replace (S (length pre)) with (length (pre ++ a :: nil))
      by (rewrite length_app; cbn [length]; lia).
    exists out'. split; [exact E' |]. split; [exact Ho' |].
    split; [rewrite Hol'; apply update_length; exact Hfit |].
    rewrite Hov', <- app_assoc. reflexivity.
Qed.

Lemma mul_into_correct :
  forall x y,
  limbs_ok x -> limbs_ok y ->
  exists out,
  Limbs.mul_into (length x + length y) x y = Some out /\ limbs_ok out /\
  length out = (length x + length y)%nat /\ Limbs.val out = Limbs.val x * Limbs.val y.
Proof.
  intros x y Hx Hy. unfold Limbs.mul_into.
  assert (Hl : length (repeat 0 (length x + length y)) =
               (length (@nil Z) + length x + length y)%nat)
    by (rewrite repeat_length; reflexivity).
  assert (Hv : Limbs.val (repeat 0 (length x + length y)) = Limbs.val nil * Limbs.val y)
    by (rewrite val_repeat0; reflexivity).
  destruct (mul_into_from_correct x nil (repeat 0 (length x + length y)) y
              Hx (Forall_nil _) Hy (limbs_ok_repeat0 _) Hl Hv)
    as [out [E [Ho [Hol Hov]]]].
  exists out. split; [exact E |]. split; [exact Ho |].
  rewrite Hol, repeat_length. split; [reflexivity | exact Hov].
Qed.

(** The shifted limbs of [shl_into], with a carry of [s] bits. *)
Lemma shl_limbs_correct :
  forall k x s carry,
  limbs_ok x -> 0 <= s < 64 -> 0 <= carry < 2 ^ s ->
  limbs_ok (Limbs.shl_limbs k x s carry) /\ length (Limbs.shl_limbs k x s carry) = k /\
  Limbs.val (Limbs.shl_limbs k x s carry) = (Limbs.val x * 2 ^ s + carry) mod 2 ^ (64 * Z.of_nat k).
Proof.
  induction k as [|k IH]; intros x s carry Hx Hs Hc.
  - cbn [Limbs.shl_limbs Limbs.val length]. rewrite pow64_0, Z.mod_1_r.
    split; [constructor | auto].
  - cbn [Limbs.shl_limbs Limbs.val length].
    pose proof (hd_bound x Hx) as Hh.
    set (h := hd 0 x) in *.
    assert (Hp : 0 < 2 ^ s < 2 ^ 64)
      by (split; [apply Z.pow_pos_nonneg | apply Z.pow_lt_mono_r]; lia).
    assert (Hps : 2 ^ (64 - s) * 2 ^ s = 2 ^ 64)
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (Hhp : 0 <= h * 2 ^ s < 2 ^ 128).
    { split; [apply Z.mul_nonneg_nonneg; lia |].
      apply Z.lt_le_trans with (2 ^ 64 * 2 ^ 64); [apply Z.mul_lt_mono_nonneg; lia | lia]. }
    rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (h * 2 ^ s)) by exact Hhp.
    rewrite Z.shiftr_div_pow2 by lia.
    assert (Hd : 0 <= h * 2 ^ s / 2 ^ 64 < 2 ^ s).
    { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia |]].
      apply Z.mul_lt_mono_pos_r; lia. }
    rewrite (Z.mod_small (h * 2 ^ s / 2 ^ 64)) by lia.
    (* The low limb [h << s] has [s] low zero bits, where [carry] goes. *)
    assert (Elo : (h * 2 ^ s) mod 2 ^ 64 = h mod 2 ^ (64 - s) * 2 ^ s).
    { rewrite <- Hps. apply Z.mul_mod_distr_r; lia. }
    pose proof (Z.mod_pos_bound h (2 ^ (64 - s)) ltac:(lia)) as Hm.
    rewrite Elo, lor_low by lia.
    assert (HL : 0 <= h mod 2 ^ (64 - s) * 2 ^ s + carry < 2 ^ 64).
    { split; [nia |]. rewrite <- Hps.
      assert (h mod 2 ^ (64 - s) * 2 ^ s <= (2 ^ (64 - s) - 1) * 2 ^ s)
        by (apply Z.mul_le_mono_nonneg_r; lia).
      lia. }
    destruct (IH (tl x) s (h * 2 ^ s / 2 ^ 64) (tl_ok x Hx) Hs Hd) as [Hr [Hrl Hrv]].
    split; [apply limbs_ok_cons; split; [exact HL | exact Hr] |].
    split; [congruence |].
    rewrite Hrv, pow64_S.
    rewrite <- mod_split by (first [exact HL | apply pow64_pos]).
    f_equal.
    pose proof (Z.div_mod (h * 2 ^ s) (2 ^ 64) ltac:(lia)) as Ed. rewrite Elo in Ed.
    rewrite (val_hd_tl x). fold h. lia.
Qed.

Lemma shl_into_correct :
  forall n x sh,
  limbs_ok x -> 0 <= sh ->
  limbs_ok (Limbs.shl_into n x sh) /\ length (Limbs.shl_into n x sh) = n /\
  Limbs.val (Limbs.shl_into n x sh) = Limbs.val x * 2 ^ sh mod 2 ^ (64 * Z.of_nat n).
Proof.
  intros n x sh Hx Hsh. unfold Limbs.shl_into.
  set (j := Nat.min (Z.to_nat (sh / 64)) n).
  assert (Hs : 0 <= sh mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  assert (Hc : 0 <= 0 < 2 ^ (sh mod 64)) by (split; [lia | apply Z.pow_pos_nonneg; lia]).
  destruct (shl_limbs_correct (n - j) x (sh mod 64) 0 Hx Hs Hc) as [Hok [Hlen Hval]].
  assert (Hjn : (j <= n)%nat) by (unfold j; lia).
  split; [apply limbs_ok_app; [apply limbs_ok_repeat0 | exact Hok] |].
  split; [rewrite length_app, repeat_length, Hlen; lia |].
  rewrite val_app, val_repeat0, repeat_length, Hval, Z.add_0_r, Z.add_0_l.
  pose proof (Z.div_mod sh 64 ltac:(lia)) as Esh.
  pose proof (Z.div_pos sh 64 Hsh ltac:(lia)) as Hq.
  destruct (Nat.le_gt_cases (Z.to_nat (sh / 64)) n) as [Hle | Hgt].
  - assert (Hj : Z.of_nat j = sh / 64) by (unfold j; rewrite Nat.min_l by exact Hle; lia).
    rewrite <- Z.mul_mod_distr_l by (pose proof (pow64_pos j); pose proof (pow64_pos (n - j)); lia).
    rewrite <- pow64_add. replace (j + (n - j))%nat with n by lia.
    f_equal.
    replace (2 ^ sh) with (2 ^ (64 * Z.of_nat j) * 2 ^ (sh mod 64))
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    ring.
  - assert (Hj : j = n) by (unfold j; lia).
    rewrite Hj, Nat.sub_diag, pow64_0, Z.mod_1_r, Z.mul_0_r.
    replace (2 ^ sh) with (2 ^ (sh - 64 * Z.of_nat n) * 2 ^ (64 * Z.of_nat n))
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite Z.mul_assoc, Z.mod_mul; [reflexivity |].
    pose proof (pow64_pos n). lia.
Qed.

(** A list whose limb [i] is limb [k + i] of [Y]. *)
Lemma val_map_seq :
  forall (f : nat -> Z) Y k n,
  (forall i, f i = Y / 2 ^ (64 * Z.of_nat i) mod 2 ^ 64) ->
  Limbs.val (map f (seq k n)) = Y / 2 ^ (64 * Z.of_nat k) mod 2 ^ (64 * Z.of_nat n).
Proof.
  intros f Y k n Hf. revert k. induction n as [|n IH]; intros k.
  - cbn [seq map Limbs.val]. rewrite pow64_0, Z.mod_1_r. reflexivity.
  - cbn [seq map Limbs.val]. rewrite IH, Hf.
    rewrite (pow64_S n), (pow64_S k).
    pose proof (pow64_pos k). pose proof (pow64_pos n).
    rewrite Z.rem_mul_r by lia.
    rewrite (Z.mul_comm (2 ^ 64) (2 ^ (64 * Z.of_nat k))), <- Z.div_div by lia.
    reflexivity.
Qed.

Lemma shr_into_correct :
  forall n x sh,
  limbs_ok x -> 0 <= sh ->
  limbs_ok (Limbs.shr_into n x sh) /\ length (Limbs.shr_into n x sh) = n /\
  Limbs.val (Limbs.shr_into n x sh) = Limbs.val x / 2 ^ sh mod 2 ^ (64 * Z.of_nat n).
Proof.
  intros n x sh Hx Hsh. unfold Limbs.shr_into. cbv zeta.
  remember (skipn (Z.to_nat (sh / 64)) x) as x' eqn:Ex'.
  assert (Hx' : limbs_ok x') by (rewrite Ex'; apply limbs_ok_skipn; exact Hx).
  assert (Hs : 0 <= sh mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  remember (sh mod 64) as s eqn:Es.
  assert (H2 : 0 < 2) by lia.
  pose proof (Z.pow_pos_nonneg 2 s H2 (proj1 Hs)) as HS.
  split.
  - unfold limbs_ok. apply Forall_map. apply Forall_forall. intros i _.
    apply Z.mod_pos_bound. lia.
  - split; [rewrite length_map, length_seq; reflexivity |].
    rewrite (val_map_seq _ (Limbs.val x' / 2 ^ s)).
    + rewrite pow64_0, Z.div_1_r. f_equal.
      (* [x'] drops [sh / 64] limbs, and the shift [sh mod 64] more bits. *)
      rewrite Ex', val_skipn by exact Hx.
      assert (Hq : 0 <= sh / 64) by (apply Z.div_pos; lia).
      rewrite Z2Nat.id by exact Hq.
      assert (Hq64 : 0 <= 64 * (sh / 64)) by lia.
      pose proof (Z.pow_pos_nonneg 2 _ H2 Hq64) as HQ.
      rewrite Z.div_div by lia.
      rewrite <- Z.pow_add_r by lia.
      f_equal. f_equal. rewrite Es. symmetry. apply Z.div_mod. lia.
    + intros i. cbv beta.
      pose proof (pow64_pos i) as HP.
      pose proof (limb_bound x' i Hx') as Hl0. pose proof (limb_bound x' (S i) Hx') as Hl1.
      rewrite Z.shiftl_mul_pow2 by lia.
      rewrite (Z.mod_small (Limbs.limb x' (S i) * 2 ^ 64)) by lia.
      rewrite lor_low by lia.
      rewrite Z.shiftr_div_pow2 by lia.
      remember (Limbs.val x' / 2 ^ (64 * Z.of_nat i)) as W eqn:EW.
      assert (E1 : Limbs.limb x' i = W mod 2 ^ 64) by (rewrite EW; apply limb_val; exact Hx').
      assert (E2 : Limbs.limb x' (S i) = W / 2 ^ 64 mod 2 ^ 64).
      { rewrite limb_val by exact Hx'. rewrite pow64_S, EW, Z.div_div by lia.
        rewrite (Z.mul_comm (2 ^ 64)). reflexivity. }
      (* The two limbs are [W mod 2^128]. *)
      assert (E3 : Limbs.limb x' (S i) * 2 ^ 64 + Limbs.limb x' i = W mod 2 ^ 128).
      { rewrite E1, E2. change (2 ^ 128) with (2 ^ 64 * 2 ^ 64).
        rewrite Z.rem_mul_r by lia. ring. }
      rewrite E3, mod128_div_mod64 by lia. f_equal.
      rewrite EW, !Z.div_div by lia. f_equal. ring.
Qed.

Lemma div_rem_limb_from_correct :
  forall x d,
  limbs_ok x -> 0 < d < 2 ^ 64 ->
  exists q r,
  Limbs.div_rem_limb_from x d = Some (q, r) /\ limbs_ok q /\ length q = length x /\
  Limbs.val q = Limbs.val x / d /\ r = Limbs.val x mod d.
Proof.
  induction x as [|a x IH]; intros d Hx Hd.
  - exists nil, 0. cbn [Limbs.div_rem_limb_from Limbs.val length].
    rewrite Z.div_0_l, Z.mod_0_l by lia.
    split; [reflexivity |]. split; [constructor |]. auto.
  - apply limbs_ok_cons in Hx as [Ha Hx].
    destruct (IH d Hx Hd) as [qs [r [E [Hq [Hl [Hv Hr]]]]]].
    cbn [Limbs.div_rem_limb_from]. rewrite E. cbv beta iota zeta.
    assert (Hr0 : 0 <= r < d) by (rewrite Hr; apply Z.mod_pos_bound; lia).
    assert (Et : Z.lor (Z.shiftl r 64 mod 2 ^ 128) a = r * 2 ^ 64 + a).
    { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia. apply lor_low; lia. }
    rewrite Et, div_u_ok, rem_u_ok by lia. cbv beta iota zeta.
    remember (r * 2 ^ 64 + a) as t eqn:Et'.
    (* [r < d] makes the two-limb [t] less than [d 2^64]. *)
    assert (Htd : 0 <= t / d < 2 ^ 64).
    { split; [apply Z.div_pos; lia |]. apply Z.div_lt_upper_bound; lia. }
    rewrite (Z.mod_small (t / d) (2 ^ 64)) by exact Htd.
    exists (t / d :: qs), (t mod d).
    split; [reflexivity |].
    split; [apply limbs_ok_cons; split; [exact Htd | exact Hq] |].
    split; [cbn [length]; congruence |].
    assert (Ex : Limbs.val (a :: x) = 2 ^ 64 * Limbs.val qs * d + t).
    { cbn [Limbs.val]. rewrite Et', Hv, Hr.
      pose proof (Z.div_mod (Limbs.val x) d) as Ed.
      assert (Hd0 : d <> 0) by lia. specialize (Ed Hd0). lia. }
    rewrite Ex, Z.div_add_l by lia.
    rewrite (Z.add_comm (2 ^ 64 * Limbs.val qs * d) t), Z.mod_add by lia.
    cbn [Limbs.val]. split; [ring | reflexivity].
Qed.

Lemma div_rem_limb_correct :
  forall x d,
  limbs_ok x -> 0 < d < 2 ^ 64 ->
  exists q r,
  Limbs.div_rem_limb x d = Some (q, r) /\ limbs_ok q /\ length q = length x /\
  Limbs.val q = Limbs.val x / d /\ r = Limbs.val x mod d.
Proof.
  intros x d Hx Hd. unfold Limbs.div_rem_limb.
  destruct (div_rem_limb_from_correct x d Hx Hd) as [q [r [E [Hq [Hl [Hv Hr]]]]]].
  rewrite E. exists q, (r mod 2 ^ 64).
  assert (Hr0 : 0 <= r < d) by (rewrite Hr; apply Z.mod_pos_bound; lia).
  rewrite Z.mod_small by lia.
  split; [reflexivity |]. auto.
Qed.
