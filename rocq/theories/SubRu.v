(** * [sub_ru] rounds toward +inf

    [sub_ru] and [sub1_ru] add [-y] with the functions that [add_ru] uses,
    so they are IEEE 754 subtraction rounded toward +inf, i.e. Flocq's
    [Bminus mode_UP], including the sign of a zero, overflow, the
    infinities and NaN. They never panic. *)

From Flocq Require Import IEEE754.BinarySingleNaN.
From Inari Require Import Model AddRu.

(** [x - y] is [x + (-y)], including the sign of a zero result, as
    [sub_ru] and [sub1_ru] rely on. Flocq defines [Bminus] by its own
    case analysis, which is that of [Bplus] with the sign of [y] flipped. *)
Lemma Bminus_Bplus_Bopp :
  forall m (x y : f64), Bminus m x y = Bplus m x (Bopp y).
Proof.
intros m [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy]; reflexivity.
Qed.

Theorem sub1_ru_correct :
  forall x y, Generic.sub1_ru x y = Some (Bminus mode_UP x y).
Proof.
intros x y.
unfold Generic.sub1_ru. rewrite Bminus_Bplus_Bopp.
generalize (add1_ru_fast_correct x (opp y)).
destruct (Generic.add1_ru_fast x (opp y)) as (r, ok). cbn [fst snd].
destruct ok.
- intros H. f_equal. now apply H.
- intros _. apply add1_ru_slow_correct.
Qed.

Theorem sub_ru_correct :
  forall x y,
  Generic.sub_ru x y =
    Some (Bminus mode_UP (fst x) (fst y), Bminus mode_UP (snd x) (snd y)).
Proof.
intros x y.
unfold Generic.sub_ru. rewrite add_ru_correct, !Bminus_Bplus_Bopp.
reflexivity.
Qed.
