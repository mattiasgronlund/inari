(** * A model of the parts of [src/simd/generic.rs] that are proved here

    Each definition in [Generic] transcribes the Rust function of the same
    name, line by line, so that the two can be compared side by side. This
    file is the only one that has to be checked against the Rust code; the
    other files prove properties of the definitions here.

    Rust's [f64] is Flocq's IEEE 754 binary64 type, and its [+] and [-] are
    Flocq's [Bplus] and [Bminus] rounded to nearest, ties to even, which is
    the default rounding mode that [generic.rs] relies on. [f64::mul_add]
    is Flocq's [Bfma] in the same mode. A const generic parameter, such as
    [FMA], is an ordinary argument.

    NaN payloads and signs are not modelled: all NaNs are the same value, so
    [opp] keeps a NaN as it is where Rust's unary [-] flips its sign bit.
    The functions modelled here never look at the payload or the sign of a
    NaN, only at the exponent field, which is all ones for every NaN, so
    [to_bits] can give every NaN the bits of one of them.

    Integers are [Z]. In the slow path, every integer operation that panics
    in a debug build when its result does not fit its type returns [None]
    then, and so does a shift by a negative amount or by at least the width
    of the type. A release build would wrap around instead, so a theorem
    that a function returns [Some] covers both kinds of build. Shifting bits
    out to the left does not panic in Rust, so [shl] drops them. Arithmetic
    on the fields of a bit pattern, in [exponent] and [decompose], cannot
    overflow and is not checked. *)

From Stdlib Require Import ZArith.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Flocq Require IEEE754.Binary IEEE754.Bits.

Open Scope Z_scope.
Open Scope bool_scope.

#[global] Instance prec_gt_0_53 : Prec_gt_0 53 := eq_refl.
#[global] Instance prec_lt_emax_53_1024 : Prec_lt_emax 53 1024 := eq_refl.

(** [f64], with 53 bits of precision (including the implicit bit) and
    the infinities at exponent 1024. *)
Definition f64 := binary_float 53 1024.

(** [x + y] and [x - y]. *)
Definition add (x y : f64) : f64 := Bplus mode_NE x y.
Definition sub (x y : f64) : f64 := Bminus mode_NE x y.

(** [x > y] and [x < y], which are false if either is NaN. *)
Definition gt (x y : f64) : bool := Bltb y x.
Definition lt (x y : f64) : bool := Bltb x y.

(** [x == y], which is false if either is NaN, and true for [0.0 == -0.0]. *)
Definition eq (x y : f64) : bool := Beqb x y.

(** [x * y] and [-x]. *)
Definition mul (x y : f64) : f64 := Bmult mode_NE x y.
Definition opp (x : f64) : f64 := Bopp x.

(** [x.mul_add(y, z)], i.e. [x * y + z] with a single rounding to nearest,
    ties to even. *)
Definition mul_add (x y z : f64) : f64 := Bfma mode_NE x y z.

(** [0.0]. *)
Definition zero : f64 := B754_zero false.

(** [k as f64] for a [u64] [k], which rounds to nearest, ties to even. *)
Definition of_u64 (k : Z) : f64 :=
  binary_normalize 53 1024 _ _ mode_NE k 0 false.

(** [x.to_bits()] and [f64::from_bits(b)]. The bit patterns are integers
    instead of [u64], so an addition to one cannot wrap around;
    [Encoding.step_up_no_wrap] shows that those in [step_up] stay in range
    anyway. *)
Definition to_bits (x : f64) : Z :=
  Bits.bits_of_b64 (Binary.BSN2B 53 1024 Bits.default_nan_pl64 x).
Definition from_bits (b : Z) : f64 := Binary.B2BSN 53 1024 (Bits.b64_of_bits b).

(** [f64::INFINITY] and [f64::MIN], i.e. [-MAX]. *)
Definition infinity : f64 := from_bits 0x7ff0000000000000.
Definition min_f64 : f64 := from_bits 0xffefffffffffffff.

(** ** Integers *)

Notation "'let*' p ':=' e1 'in' e2" :=
  (match e1 with Some p => e2 | None => None end)
  (at level 200, p pattern, e1 at level 100, right associativity).

(** The result [z] of an arithmetic operation on unsigned or signed
    integers of [w] bits (e.g. [u128] or [i32]), unless it overflows. *)
Definition checked_u (w z : Z) : option Z :=
  if (0 <=? z) && (z <? 2^w) then Some z else None.
Definition checked_i (w z : Z) : option Z :=
  if (- 2^(w - 1) <=? z) && (z <? 2^(w - 1)) then Some z else None.

(** [a << s] and [a >> s] for an unsigned integer [a] of [w] bits. *)
Definition shl (w a s : Z) : option Z :=
  if (0 <=? s) && (s <? w) then Some (Z.shiftl a s mod 2^w) else None.
Definition shr (w a s : Z) : option Z :=
  if (0 <=? s) && (s <? w) then Some (Z.shiftr a s) else None.

(** [a.leading_zeros()] for an unsigned integer [a] of [w] bits. *)
Definition leading_zeros (w a : Z) : Z :=
  if a =? 0 then w else w - 1 - Z.log2 a.

Module Generic.

(** [fn exponent(x: f64) -> i32] *)
Definition exponent (x : f64) : Z :=
  Z.land (Z.shiftr (to_bits x) 52) 0x7ff - 1023.

(** [fn step_up(x: f64) -> f64] *)
Definition step_up (x : f64) : f64 :=
  let b := to_bits x in
  from_bits (if gt x zero then b + 1 else if lt x zero then b - 1 else 1).

(** [fn two_sum_err(x: f64, y: f64, s: f64) -> f64] *)
Definition two_sum_err (x y s : f64) : f64 :=
  let a := sub s y in
  let b := sub s a in
  add (sub x a) (sub y b).

(** [fn split(x: f64) -> (f64, f64)] *)
Definition split (x : f64) : f64 * f64 :=
  (* [const C: f64 = 134217729.0], i.e. [2^27 + 1], which [of_u64] rounds
     to nearest as the literal is. *)
  let c := of_u64 134217729 in
  let t := mul c x in
  let hi := sub t (sub t x) in
  (hi, sub x hi).

(** [fn two_prod_err<const FMA: bool>(x: f64, y: f64, p: f64) -> f64] *)
Definition two_prod_err (fma : bool) (x y p : f64) : f64 :=
  if fma then mul_add x y (opp p)
  else
    let '(xh, xl) := split x in
    let '(yh, yl) := split y in
    add (add (add (sub (mul xh yh) p) (mul xh yl)) (mul xl yh)) (mul xl yl).

(** [fn two_prod_is_exact<const FMA: bool>(x: f64, y: f64, p: f64) -> bool] *)
Definition two_prod_is_exact (fma : bool) (x y p : f64) : bool :=
  let ep := exponent p in
  if fma then (-968 <=? ep) && (ep <=? 1023)
  else
    (-968 <=? ep) && (ep <=? 1022)
    && (exponent x <=? 995) && (exponent y <=? 995).

(** [fn is_finite(x: f64) -> bool] *)
Definition is_finite (x : f64) : bool := exponent x <? 1024.

(** [fn add1_ru_fast(x: f64, y: f64) -> (f64, bool)] *)
Definition add1_ru_fast (x y : f64) : f64 * bool :=
  let s := add x y in
  let e := two_sum_err x y s in
  let finite := is_finite x && is_finite y in
  let ok :=
    negb finite
    || ((exponent x <=? 1022) && (exponent y <=? 1022) && is_finite s) in
  let r := if finite && gt e zero then step_up s else s in
  (r, ok).

(** [fn mul1_ru_fast<const FMA: bool>(x: f64, y: f64) -> (f64, bool)] *)
Definition mul1_ru_fast (fma : bool) (x y : f64) : f64 * bool :=
  let p := mul x y in
  let e := two_prod_err fma x y p in
  let special := negb (is_finite x && is_finite y) || eq x zero || eq y zero in
  let ok := special || two_prod_is_exact fma x y p in
  let r := if negb special && gt e zero then step_up p else p in
  (r, ok).

(** [fn decompose(x: f64) -> (bool, u64, i32)] *)
Definition decompose (x : f64) : bool * Z * Z :=
  let b := to_bits x in
  let biased := Z.land (Z.shiftr b 52) 0x7ff in
  let frac := Z.land b (Z.shiftl 1 52 - 1) in
  if biased =? 0 then (negb (Z.shiftr b 63 =? 0), frac, -1074)
  else (negb (Z.shiftr b 63 =? 0), Z.lor frac (Z.shiftl 1 52), biased - 1075).

(** [fn pow2(e: i32) -> f64] *)
Definition pow2 (e : Z) : option f64 :=
  if -1022 <=? e then
    let* t := checked_i 32 (e + 1023) in
    (* [(e + 1023) as u64] *)
    let* b := shl 64 (t mod 2^64) 52 in
    Some (from_bits b)
  else
    let* t := checked_i 32 (e + 1074) in
    let* b := shl 64 1 t in
    Some (from_bits b).

(** [fn round_up_exact(neg: bool, m: u128, e: i32, sticky: bool) -> f64] *)
Definition round_up_exact (neg : bool) (m e : Z) (sticky : bool) : option f64 :=
  (* [m.leading_zeros() as i32]: at most 128, so the cast keeps it. *)
  let* top := checked_i 32 (127 - leading_zeros 128 m) in
  let* lead := checked_i 32 (e + top) in
  let* lead52 := checked_i 32 (lead - 52) in
  let lsb := Z.max lead52 (-1074) in
  let* shift := checked_i 32 (lsb - e) in
  let* (kept, lost) :=
    if shift <=? 0 then
      let* ns := checked_i 32 (- shift) in
      let* k := shl 128 m ns in
      Some (k, sticky)
    else if 128 <=? shift then Some (0, true)
    else
      let* k := shr 128 m shift in
      let* p := shl 128 1 shift in
      let* mask := checked_u 128 (p - 1) in
      Some (k, sticky || negb (Z.land m mask =? 0)) in
  let* kept := if lost && negb neg then checked_u 128 (kept + 1) else Some kept in
  (* [kept as u64] *)
  let kept := kept mod 2^64 in
  (* [kept.leading_zeros() as i32]: at most 64, so the cast keeps it. *)
  let* bits := checked_i 32 (64 - leading_zeros 64 kept) in
  (* [lsb + bits] is only evaluated if [kept != 0]. *)
  let* overflow :=
    if negb (kept =? 0) then
      let* t := checked_i 32 (lsb + bits) in
      Some (1024 <? t)
    else Some false in
  if overflow then Some (if neg then min_f64 else infinity)
  else
    let* p := pow2 lsb in
    let mag := mul (of_u64 kept) p in
    Some (if neg then opp mag else mag).

(** [fn sum_round_up(sx: bool, mx: u128, ex: i32, sy: bool, my: u128, ey: i32) -> f64] *)
Definition sum_round_up (sx : bool) (mx ex : Z) (sy : bool) (my ey : Z) : option f64 :=
  let norm m e :=
    let* sh := checked_u 32 (leading_zeros 128 m - 2) in
    let* m' := shl 128 m sh in
    (* [sh as i32]: at most 126, so the cast keeps it. *)
    let* e' := checked_i 32 (e - sh) in
    Some (m', e') in
  let* (mx, ex) := norm mx ex in
  let* (my, ey) := norm my ey in
  (* [match (ex, mx).cmp(&(ey, my))], which compares lexicographically. *)
  let '((sx, mx, ex), (sy, my, ey)) :=
    if (ex <? ey) || ((ex =? ey) && (mx <? my))
    then ((sy, my, ey), (sx, mx, ex))
    else ((sx, mx, ex), (sy, my, ey)) in
  let* ed := checked_i 32 (ex - ey) in
  (* [(ex - ey) as u32] *)
  let d := ed mod 2^32 in
  let* (y, sticky) :=
    if 128 <=? d then Some (0, true)
    else
      let* yd := shr 128 my d in
      let* p := shl 128 1 d in
      let* mask := checked_u 128 (p - 1) in
      Some (yd, negb (Z.land my mask =? 0)) in
  let* m :=
    if Bool.eqb sx sy then checked_u 128 (mx + y)
    else
      let* t := checked_u 128 (mx - y) in
      (* [sticky as u128] *)
      checked_u 128 (t - Z.b2z sticky) in
  if m =? 0 then
    (* [debug_assert!(!sticky)] panics in a debug build. *)
    if sticky then None else Some zero
  else round_up_exact sx m ex sticky.

(** [fn add1_ru_slow(x: f64, y: f64) -> f64] *)
Definition add1_ru_slow (x y : f64) : option f64 :=
  if negb (is_finite x && is_finite y) || eq x zero || eq y zero then
    Some (add x y)
  else
    let '(sx, mx, ex) := decompose x in
    let '(sy, my, ey) := decompose y in
    (* [mx as u128] and [my as u128] keep the values. *)
    sum_round_up sx mx ex sy my ey.

(** [fn mul1_ru_slow(x: f64, y: f64) -> f64] *)
Definition mul1_ru_slow (x y : f64) : option f64 :=
  if negb (is_finite x && is_finite y) || eq x zero || eq y zero then
    Some (mul x y)
  else
    let '(sx, mx, ex) := decompose x in
    let '(sy, my, ey) := decompose y in
    (* [mx as u128] and [my as u128] keep the values. *)
    let* m := checked_u 128 (mx * my) in
    let* e := checked_i 32 (ex + ey) in
    (* [sx != sy] *)
    round_up_exact (negb (Bool.eqb sx sy)) m e false.

(** [F64X2], i.e. [[f64; 2]], with [x[0]] as [fst x] and [x[1]] as [snd x]. *)
Definition F64X2 : Type := f64 * f64.

(** [fn lanewise2(x: F64X2, y: F64X2, fast: impl Fn(f64, f64) -> (f64, bool),
    slow: impl Fn(f64, f64) -> f64) -> F64X2] *)
Definition lanewise2 (x y : F64X2) (fast : f64 -> f64 -> f64 * bool)
    (slow : f64 -> f64 -> option f64) : option F64X2 :=
  let '(r0, ok0) := fast (fst x) (fst y) in
  let '(r1, ok1) := fast (snd x) (snd y) in
  if ok0 && ok1 then Some (r0, r1)
  else
    let* a := if ok0 then Some r0 else slow (fst x) (fst y) in
    let* b := if ok1 then Some r1 else slow (snd x) (snd y) in
    Some (a, b).

(** [pub(crate) fn add_ru(x: F64X2, y: F64X2) -> F64X2] *)
Definition add_ru (x y : F64X2) : option F64X2 :=
  lanewise2 x y add1_ru_fast add1_ru_slow.

(** [pub(super) fn mul_ru_impl<const FMA: bool>(x: F64X2, y: F64X2) -> F64X2] *)
Definition mul_ru_impl (fma : bool) (x y : F64X2) : option F64X2 :=
  lanewise2 x y (mul1_ru_fast fma) mul1_ru_slow.

(** [pub(crate) fn mul_ru(x: F64X2, y: F64X2) -> F64X2], which calls
    [mul_ru_impl::<HAS_FMA>]. [HAS_FMA] depends on the target, so it is an
    argument. *)
Definition mul_ru (has_fma : bool) (x y : F64X2) : option F64X2 :=
  mul_ru_impl has_fma x y.

(** [pub(crate) fn neg(x: F64X2) -> F64X2] *)
Definition neg (x : F64X2) : F64X2 := (opp (fst x), opp (snd x)).

(** [pub(crate) fn sub_ru(x: F64X2, y: F64X2) -> F64X2] *)
Definition sub_ru (x y : F64X2) : option F64X2 := add_ru x (neg y).

(** [pub(crate) fn sub1_ru(x: f64, y: f64) -> f64] *)
Definition sub1_ru (x y : f64) : option f64 :=
  let '(r, ok) := add1_ru_fast x (opp y) in
  if ok then Some r else add1_ru_slow x (opp y).

End Generic.
