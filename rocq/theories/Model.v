(** * A model of the parts of the Rust code that are proved here

    Each definition in [Generic] transcribes the function of the same name
    in [src/simd/generic.rs], line by line, so that the two can be compared
    side by side. The section on intervals at the end does the same for the
    parts of [src/interval.rs], [src/boolean.rs] and [src/integer.rs] that
    [floor], [ceil], [round], [round_ties_even] and [trunc] of intervals
    use. This file is the only one that has
    to be checked against the Rust code, and [Ieee1788.v] the only one that
    has to be checked against IEEE 1788; the other files prove properties
    of the definitions here.

    Rust's [f64] is Flocq's IEEE 754 binary64 type, and its [+], [-], [*]
    and [/] are Flocq's [Bplus], [Bminus], [Bmult] and [Bdiv] rounded to
    nearest, ties to even, which is the default rounding mode that
    [generic.rs] relies on. [f64::mul_add] and [f64::sqrt] are Flocq's
    [Bfma] and [Bsqrt] in the same mode, [f64::floor], [f64::ceil],
    [f64::round] and [f64::trunc] are Flocq's [Bnearbyint] toward -inf,
    toward +inf, to nearest with ties away from zero, and toward zero, and
    [f64::abs] is Flocq's [Babs]. A const generic parameter, such as [FMA],
    is an ordinary argument.

    NaN payloads and signs are not modelled: all NaNs are the same value, so
    [opp] keeps a NaN as it is where Rust's unary [-] flips its sign bit,
    and [to_bits] gives every NaN the bits of one of them. The functions
    modelled here only look at the exponent field of a NaN, which is all
    ones for every NaN, except [add_odd]. It reads the lowest bit of [s],
    which for a NaN is part of the payload, and returns a NaN for a NaN [s]
    whatever that bit is: [e] is then NaN too, so [b + 1] is taken, and
    adding 1 to an even pattern changes only its lowest bit.

    Integers are [Z]. In the slow path, every integer operation that panics
    in a debug build when its result does not fit its type returns [None]
    then, and so does a shift by a negative amount or by at least the width
    of the type. A release build would wrap around instead, so a theorem
    that a function returns [Some] covers both kinds of build. A division
    by zero, which panics in both, returns [None] too. Shifting bits out to
    the left does not panic in Rust, so [shl] drops them. Arithmetic on the
    fields of a bit pattern, in [exponent] and [decompose], cannot overflow
    and is not checked.

    Rocq functions must terminate, so a Rust function that calls itself,
    [sqrt1_rd_impl] and [sqrt1_ru_impl], takes the number of nested calls
    it may make, and returns [None] if it would make more. If it returns
    [Some r] for any number, the Rust function returns [r]. *)

From Stdlib Require Import ZArith Rdefinitions.
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

(** [x / y]. *)
Definition div (x y : f64) : f64 := Bdiv mode_NE x y.

(** [x.sqrt()]. Not [sqrt], which is the square root of a real in Stdlib. *)
Definition fsqrt (x : f64) : f64 := Bsqrt mode_NE x.

(** [x.floor()] and [x.ceil()]: [x] rounded to an integer toward -inf and
    toward +inf, IEEE 754's roundToIntegralTowardNegative and
    roundToIntegralTowardPositive. A zero result has the sign of [x]. *)
Definition ffloor (x : f64) : f64 := Bnearbyint mode_DN x.
Definition fceil (x : f64) : f64 := Bnearbyint mode_UP x.

(** [x.round()] and [x.trunc()]: [x] rounded to the nearest integer with
    ties away from zero, and toward zero, IEEE 754's
    roundToIntegralTiesToAway and roundToIntegralTowardZero. A zero result
    has the sign of [x]. *)
Definition fround (x : f64) : f64 := Bnearbyint mode_NA x.
Definition ftrunc (x : f64) : f64 := Bnearbyint mode_ZR x.

(** [x.abs()], which clears the sign bit. *)
Definition fabs (x : f64) : f64 := Babs x.

(** [x.copysign(y)]: [x] with the sign bit of [y]. The model has no sign
    for a NaN [y] and takes it as positive, which is right only for some
    NaNs; [round_ties_even1], the only caller, never passes a NaN [y]. *)
Definition copysign (x y : f64) : f64 :=
  if Bool.eqb (Bsign x) (Bsign y) then x else opp x.

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

(** [0.5]. *)
Definition half : f64 := from_bits 0x3fe0000000000000.

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

(** [a / b] and [a % b] for unsigned integers [a] and [b]. The quotient
    rounds toward zero, which for [a, b >= 0] is the floor that [Z.div]
    computes. *)
Definition div_u (a b : Z) : option Z := if b =? 0 then None else Some (a / b).
Definition rem_u (a b : Z) : option Z := if b =? 0 then None else Some (a mod b).

Module Generic.

(** [fn exponent(x: f64) -> i32] *)
Definition exponent (x : f64) : Z :=
  Z.land (Z.shiftr (to_bits x) 52) 0x7ff - 1023.

(** [fn step_up(x: f64) -> f64] *)
Definition step_up (x : f64) : f64 :=
  let b := to_bits x in
  from_bits (if gt x zero then b + 1 else if lt x zero then b - 1 else 1).

(** [fn step_down(x: f64) -> f64] *)
Definition step_down (x : f64) : f64 := opp (step_up (opp x)).

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

(** [fn add_odd(x: f64, y: f64) -> f64] *)
Definition add_odd (x y : f64) : f64 :=
  let s := add x y in
  let e := two_sum_err x y s in
  (* [e != 0.0], which is true if [e] is NaN. *)
  if negb (eq e zero) && (Z.land (to_bits s) 1 =? 0) then
    let b := to_bits s in
    (* [(e > 0.0) == (s > 0.0)] *)
    let toward_larger_magnitude := Bool.eqb (gt e zero) (gt s zero) in
    from_bits (if toward_larger_magnitude then b + 1 else b - 1)
  else s.

(** [pub(super) fn mul_add1_rn_emulated(u1: f64, u2: f64, c: f64) -> f64] *)
Definition mul_add1_rn_emulated (u1 u2 c : f64) : f64 :=
  let t1 := add c u1 in
  let t2 := two_sum_err c u1 t1 in
  add t1 (add_odd t2 u2).

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

(** [fn div1_ru_fast<const FMA: bool>(x: f64, y: f64) -> (f64, bool)] *)
Definition div1_ru_fast (fma : bool) (x y : f64) : f64 * bool :=
  let q := div x y in
  let special := negb (is_finite x && is_finite y) || eq x zero || eq y zero in
  let exact :=
    (-1022 <=? exponent q) && (exponent q <=? 1023) && (-967 <=? exponent x) in
  let '(r, ok) :=
    if fma then (mul_add (opp q) y x, special || exact)
    else
      let p := mul q y in
      let dekker :=
        (exponent q <=? 995) && (exponent y <=? 995) && (exponent x <=? 1021) in
      (sub (sub x p) (two_prod_err false q y p), special || (exact && dekker)) in
  (* [r != 0.0 && (r > 0.0) == (y > 0.0)] *)
  let up := negb (eq r zero) && Bool.eqb (gt r zero) (gt y zero) in
  let res := if negb special && up then step_up q else q in
  (res, ok).

(** [fn mul_add1_special(a: f64, b: f64, c: f64) -> f64], which comes after
    the fast paths in [generic.rs], but has to be defined before its use in
    [mul_add1_ru_fast] here. *)
Definition mul_add1_special (a b c : f64) : f64 :=
  if is_finite a && is_finite b && negb (is_finite c) then c
  else add (mul a b) c.

(** [fn mul_add1_ru_fast<const FMA: bool>(a: f64, b: f64, c: f64) -> (f64, bool)] *)
Definition mul_add1_ru_fast (fma : bool) (a b c : f64) : f64 * bool :=
  let u1 := mul a b in
  let u2 := two_prod_err fma a b u1 in
  let r1 := if fma then mul_add a b c else mul_add1_rn_emulated u1 u2 c in
  let alpha1 := add c u2 in
  let alpha2 := two_sum_err c u2 alpha1 in
  let beta1 := add u1 alpha1 in
  let beta2 := two_sum_err u1 alpha1 beta1 in
  let gamma := add (sub beta1 r1) beta2 in
  let err := add gamma alpha2 in
  let special :=
    negb (is_finite a && is_finite b && is_finite c) || eq a zero || eq b zero in
  let not_tiny (x : f64) (e_min : Z) := eq x zero || (e_min <=? exponent x) in
  let ok :=
    special
    || (two_prod_is_exact fma a b u1
        && (exponent u1 <=? 1021)
        && (exponent c <=? 1021)
        && is_finite r1
        && not_tiny r1 (-1022)
        && not_tiny alpha1 (-1021)
        && not_tiny beta1 (-1020)) in
  let r :=
    if special then mul_add1_special a b c
    else if gt err zero then step_up r1
    else r1 in
  (r, ok).

(** [fn sqrt1_fast<const FMA: bool>(x: f64) -> (f64, f64, bool)] *)
Definition sqrt1_fast (fma : bool) (x : f64) : f64 * f64 * bool :=
  let s := fsqrt x in
  let ex := exponent x in
  let '(r, ok) :=
    if fma then (mul_add (opp s) s x, (-966 <=? ex) && (ex <=? 1023))
    else
      let p := mul s s in
      (sub (sub x p) (two_prod_err false s s p), (-966 <=? ex) && (ex <=? 1021)) in
  (s, r, ok).

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

(** [fn div1_ru_slow(x: f64, y: f64) -> f64] *)
Definition div1_ru_slow (x y : f64) : option f64 :=
  if negb (is_finite x && is_finite y) || eq x zero || eq y zero then
    Some (div x y)
  else
    let '(sx, mx, ex) := decompose x in
    let '(sy, my, ey) := decompose y in
    (* [my.leading_zeros()] and [mx.leading_zeros()] are [u32]s. [as i32]
       keeps them, as they are at most 64. *)
    let* sh := checked_u 32 (leading_zeros 64 my - 11) in
    let* ny := shl 64 my sh in
    let* t := checked_i 32 (leading_zeros 64 my - 11) in
    let* ey := checked_i 32 (ey - t) in
    let* t := checked_u 32 (leading_zeros 64 mx + 64) in
    let* sh := checked_u 32 (t - 1) in
    (* [mx as u128] keeps the value. *)
    let* nx := shl 128 mx sh in
    let* t := checked_i 32 (leading_zeros 64 mx + 64) in
    let* t := checked_i 32 (t - 1) in
    let* ex := checked_i 32 (ex - t) in
    (* [ny as u128] keeps the value. *)
    let* q := div_u nx ny in
    let* rem := rem_u nx ny in
    let* e := checked_i 32 (ex - ey) in
    (* [sx != sy] and [rem != 0] *)
    round_up_exact (negb (Bool.eqb sx sy)) q e (negb (rem =? 0)).

(** [fn mul_add1_ru_slow(a: f64, b: f64, c: f64) -> f64] *)
Definition mul_add1_ru_slow (a b c : f64) : option f64 :=
  if negb (is_finite a && is_finite b && is_finite c) || eq a zero || eq b zero then
    Some (mul_add1_special a b c)
  else if eq c zero then mul1_ru_slow a b
  else
    let '(sa, ma, ea) := decompose a in
    let '(sb, mb, eb) := decompose b in
    let '(sc, mc, ec) := decompose c in
    (* [ma as u128], [mb as u128] and [mc as u128] keep the values. *)
    let* m := checked_u 128 (ma * mb) in
    let* e := checked_i 32 (ea + eb) in
    (* [sa != sb] *)
    sum_round_up (negb (Bool.eqb sa sb)) m e sc mc ec.

(** [fn sqrt1_slow(x: f64, f: fn(f64) -> f64) -> f64], where [f] returns an
    [option], as the functions passed for it do here. *)
Definition sqrt1_slow (x : f64) (f : f64 -> option f64) : option f64 :=
  (* The [const]s are evaluated at compile time, rounded to nearest as at
     run time. [18446744073709551616.0] is [2^64], which a literal rounds
     to nearest like [of_u64] does, though it is not a [u64]. *)
  let two_pow_64 := of_u64 (2^64) in
  let two_pow_m64 := div (of_u64 1) two_pow_64 in
  let two_pow_128 := mul two_pow_64 two_pow_64 in
  let two_pow_m128 := div (of_u64 1) two_pow_128 in
  if gt x zero && is_finite x then
    if exponent x <? 0 then
      let* s := f (mul x two_pow_128) in
      Some (mul s two_pow_m64)
    else
      let* s := f (mul x two_pow_m128) in
      Some (mul s two_pow_64)
  else Some (fsqrt x).

(** [fn round_ties_even1(x: f64) -> f64] *)
Definition round_ties_even1 (x : f64) : f64 :=
  (* [4503599627370496.0] is [2^52]. *)
  let two_pow_52 := of_u64 (2^52) in
  if lt (fabs x) two_pow_52 then
    copysign (sub (add (fabs x) two_pow_52) two_pow_52) x
  else x.

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

(** [pub(crate) fn neg0(x: F64X2) -> F64X2] *)
Definition neg0 (x : F64X2) : F64X2 := (opp (fst x), snd x).

(** [pub(crate) fn ceil(x: F64X2) -> F64X2] *)
Definition ceil (x : F64X2) : F64X2 := (fceil (fst x), fceil (snd x)).

(** [pub(crate) fn floor(x: F64X2) -> F64X2] *)
Definition floor (x : F64X2) : F64X2 := (ffloor (fst x), ffloor (snd x)).

(** [pub(crate) fn round(x: F64X2) -> F64X2] *)
Definition round (x : F64X2) : F64X2 := (fround (fst x), fround (snd x)).

(** [pub(crate) fn round_ties_even(x: F64X2) -> F64X2] *)
Definition round_ties_even (x : F64X2) : F64X2 :=
  (round_ties_even1 (fst x), round_ties_even1 (snd x)).

(** [pub(crate) fn trunc(x: F64X2) -> F64X2] *)
Definition trunc (x : F64X2) : F64X2 := (ftrunc (fst x), ftrunc (snd x)).

(** [pub(crate) fn sub_ru(x: F64X2, y: F64X2) -> F64X2] *)
Definition sub_ru (x y : F64X2) : option F64X2 := add_ru x (neg y).

(** [pub(crate) fn sub1_ru(x: f64, y: f64) -> f64] *)
Definition sub1_ru (x y : f64) : option f64 :=
  let '(r, ok) := add1_ru_fast x (opp y) in
  if ok then Some r else add1_ru_slow x (opp y).

(** [pub(super) fn div_ru_impl<const FMA: bool>(x: F64X2, y: F64X2) -> F64X2] *)
Definition div_ru_impl (fma : bool) (x y : F64X2) : option F64X2 :=
  lanewise2 x y (div1_ru_fast fma) div1_ru_slow.

(** [pub(crate) fn div_ru(x: F64X2, y: F64X2) -> F64X2], which calls
    [div_ru_impl::<HAS_FMA>]. *)
Definition div_ru (has_fma : bool) (x y : F64X2) : option F64X2 :=
  div_ru_impl has_fma x y.

(** [pub(super) fn mul_add_ru_impl<const FMA: bool>(x: F64X2, y: F64X2, z: F64X2) -> F64X2] *)
Definition mul_add_ru_impl (fma : bool) (x y z : F64X2) : option F64X2 :=
  let '(r0, ok0) := mul_add1_ru_fast fma (fst x) (fst y) (fst z) in
  let '(r1, ok1) := mul_add1_ru_fast fma (snd x) (snd y) (snd z) in
  if ok0 && ok1 then Some (r0, r1)
  else
    let* a := if ok0 then Some r0 else mul_add1_ru_slow (fst x) (fst y) (fst z) in
    let* b := if ok1 then Some r1 else mul_add1_ru_slow (snd x) (snd y) (snd z) in
    Some (a, b).

(** [pub(crate) fn mul_add_ru(x: F64X2, y: F64X2, z: F64X2) -> F64X2], which
    calls [mul_add_ru_impl::<HAS_FMA>]. *)
Definition mul_add_ru (has_fma : bool) (x y z : F64X2) : option F64X2 :=
  mul_add_ru_impl has_fma x y z.

(** [pub(super) fn sqrt1_rd_impl<const FMA: bool>(x: f64) -> f64], which may
    call itself [n] times through [sqrt1_slow]. *)
Fixpoint sqrt1_rd_impl (n : nat) (fma : bool) (x : f64) : option f64 :=
  let '(s, r, ok) := sqrt1_fast fma x in
  if ok then Some (if lt r zero then step_down s else s)
  else
    match n with
    | O => None
    | S n => sqrt1_slow x (sqrt1_rd_impl n fma)
    end.

(** [pub(super) fn sqrt1_ru_impl<const FMA: bool>(x: f64) -> f64], which may
    call itself [n] times through [sqrt1_slow]. *)
Fixpoint sqrt1_ru_impl (n : nat) (fma : bool) (x : f64) : option f64 :=
  let '(s, r, ok) := sqrt1_fast fma x in
  if ok then Some (if gt r zero then step_up s else s)
  else
    match n with
    | O => None
    | S n => sqrt1_slow x (sqrt1_ru_impl n fma)
    end.

(** [pub(crate) fn sqrt1_rd(x: f64) -> f64] and
    [pub(crate) fn sqrt1_ru(x: f64) -> f64], which call [sqrt1_rd_impl::<HAS_FMA>]
    and [sqrt1_ru_impl::<HAS_FMA>]. They allow one nested call, as
    [sqrt1_slow] scales [x] into the range of the fast path. *)
Definition sqrt1_rd (has_fma : bool) (x : f64) : option f64 :=
  sqrt1_rd_impl 1 has_fma x.
Definition sqrt1_ru (has_fma : bool) (x : f64) : option f64 :=
  sqrt1_ru_impl 1 has_fma x.

(** [pub(crate) fn sqrt_rd_ru(x: F64X2) -> F64X2] *)
Definition sqrt_rd_ru (has_fma : bool) (x : F64X2) : option F64X2 :=
  let* a := sqrt1_rd has_fma (fst x) in
  let* b := sqrt1_ru has_fma (snd x) in
  Some (a, b).

End Generic.

(** ** Intervals

    The parts of [src/interval.rs], [src/boolean.rs] and [src/integer.rs]
    that [Interval::floor], [Interval::ceil], [Interval::round],
    [Interval::round_ties_even], [Interval::trunc] and their decorated
    versions use. Those call the backend's [floor], [ceil], [round],
    [round_ties_even], [trunc] and [neg0], which are the ones in [Generic]
    here. *)

(** [pub struct Interval], whose only field is [rep: F64X2]. *)
Record Interval : Type := { rep : Generic.F64X2 }.

(** The intervals that [rep] can hold, from the comment on
    [struct Interval]: a nonempty interval [[a, b]] is stored as [[-a; b]],
    and an empty one as [[NaN; NaN]]. The bounds are the ones that
    [TryFrom<(f64, f64)>] accepts,
    [a <= b && a != f64::INFINITY && b != f64::NEG_INFINITY], where [<=] is
    Flocq's [Bleb]. So [a] may be -inf, [b] may be +inf, and a zero bound
    may have either sign. *)
Definition valid (x : Interval) : Prop :=
  let '(x0, x1) := rep x in
  (is_nan x0 = true /\ is_nan x1 = true) \/
  (Bleb (opp x0) x1 = true /\ opp x0 <> B754_infinity false /\
   x1 <> B754_infinity true).

(** The real [r] is in [x]: [a <= r <= b], where [a = -inf] and [b = +inf]
    bound no real. A NaN bound excludes every real, so no real is in an
    empty interval. *)
Definition mem (r : R) (x : Interval) : Prop :=
  match opp (fst (rep x)) with
  | B754_infinity s => s = true
  | B754_nan => False
  | a => (B2R a <= r)%R
  end /\
  match snd (rep x) with
  | B754_infinity s => s = false
  | B754_nan => False
  | b => (r <= B2R b)%R
  end.

(** [pub enum Decoration], with the discriminants by which the derived
    [Ord] compares its variants. *)
Inductive Decoration : Type := Ill | Trv | Def | Dac | Com.

Definition discriminant (d : Decoration) : Z :=
  match d with Ill => 0 | Trv => 4 | Def => 8 | Dac => 12 | Com => 16 end.

(** [d == e], and [d.min(e)], which returns [d] if [d <= e] and [e]
    otherwise. *)
Definition dec_eqb (d e : Decoration) : bool := discriminant d =? discriminant e.
Definition dec_min (d e : Decoration) : Decoration :=
  if discriminant d <=? discriminant e then d else e.

(** [pub struct DecInterval], with its fields [x] and [d] as [itv] and
    [dec]. *)
Record DecInterval : Type := { itv : Interval; dec : Decoration }.

Module Interval.

(** [pub const EMPTY: Self], i.e. [[NaN; NaN]]. *)
Definition EMPTY : Interval := {| rep := (B754_nan, B754_nan) |}.

(** [pub(crate) fn inf_raw(self) -> f64] and
    [pub(crate) fn sup_raw(self) -> f64] *)
Definition inf_raw (self : Interval) : f64 := opp (fst (rep self)).
Definition sup_raw (self : Interval) : f64 := snd (rep self).

(** [pub fn is_common_interval(self) -> bool], which computes
    [all(lt(self.rep, splat(f64::INFINITY)))]. [lt] sets every bit of a
    lane where the comparison holds and clears them where it does not, and
    [all] tests that the sign bits of both lanes are set. The model has no
    sign bit for a NaN, so it takes the two comparisons directly. *)
Definition is_common_interval (self : Interval) : bool :=
  lt (fst (rep self)) infinity && lt (snd (rep self)) infinity.

(** [pub fn is_empty(self) -> bool], where [f64::is_nan] is Flocq's
    [is_nan]. *)
Definition is_empty (self : Interval) : bool := is_nan (fst (rep self)).

(** [pub fn is_singleton(self) -> bool] *)
Definition is_singleton (self : Interval) : bool :=
  eq (inf_raw self) (sup_raw self).

(** [pub fn ceil(self) -> Self] *)
Definition ceil (self : Interval) : Interval :=
  let x := Generic.neg0 (rep self) in
  let r := Generic.ceil x in
  {| rep := Generic.neg0 r |}.

(** [pub fn floor(self) -> Self] *)
Definition floor (self : Interval) : Interval :=
  let x := Generic.neg0 (rep self) in
  let r := Generic.floor x in
  {| rep := Generic.neg0 r |}.

(** [pub fn round(self) -> Self] *)
Definition round (self : Interval) : Interval :=
  {| rep := Generic.round (rep self) |}.

(** [pub fn round_ties_even(self) -> Self] *)
Definition round_ties_even (self : Interval) : Interval :=
  {| rep := Generic.round_ties_even (rep self) |}.

(** [pub fn trunc(self) -> Self] *)
Definition trunc (self : Interval) : Interval :=
  {| rep := Generic.trunc (rep self) |}.

End Interval.

Module DecInterval.

(** [pub const EMPTY: Self] and [pub const NAI: Self] *)
Definition EMPTY : DecInterval := {| itv := Interval.EMPTY; dec := Trv |}.
Definition NAI : DecInterval := {| itv := Interval.EMPTY; dec := Ill |}.

(** [pub fn is_nai(self) -> bool] *)
Definition is_nai (self : DecInterval) : bool := dec_eqb (dec self) Ill.

(** [pub(crate) const fn new_unchecked(x: Interval, d: Decoration) -> Self] *)
Definition new_unchecked (x : Interval) (d : Decoration) : DecInterval :=
  {| itv := x; dec := d |}.

(** [pub fn set_dec(x: Interval, d: Decoration) -> Self] *)
Definition set_dec (x : Interval) (d : Decoration) : DecInterval :=
  if dec_eqb d Ill then NAI
  else if Interval.is_empty x then EMPTY
  else if dec_eqb d Com && negb (Interval.is_common_interval x) then
    new_unchecked x Dac
  else new_unchecked x d.

(** The function that [impl_dec!(f, x, y, is_not_com)] in [src/integer.rs]
    defines is [impl_dec Interval.f (fun x y => is_not_com)]. *)
Definition impl_dec (f : Interval -> Interval)
    (is_not_com : Interval -> Interval -> bool) (self : DecInterval) :
    DecInterval :=
  if is_nai self then self
  else
    let x := itv self in
    let y := f x in
    let d :=
      if Interval.is_empty y then Trv
      else if negb (Interval.is_singleton y) then Def
      else if is_not_com x y then Dac
      else Com in
    set_dec y (dec_min d (dec self)).

(** [impl_dec!(ceil, x, y, x.sup_raw() == y.sup_raw())] *)
Definition ceil : DecInterval -> DecInterval :=
  impl_dec Interval.ceil
    (fun x y => eq (Interval.sup_raw x) (Interval.sup_raw y)).

(** [impl_dec!(floor, x, y, x.inf_raw() == y.inf_raw())] *)
Definition floor : DecInterval -> DecInterval :=
  impl_dec Interval.floor
    (fun x y => eq (Interval.inf_raw x) (Interval.inf_raw y)).

(** [impl_dec!(round, x, y, { ... })], whose block is
    [let abs_a = x.inf_raw().abs(); let abs_b = x.sup_raw().abs();
    (abs_a - abs_a.trunc() == 0.5) || (abs_b - abs_b.trunc() == 0.5)] *)
Definition round : DecInterval -> DecInterval :=
  impl_dec Interval.round
    (fun x y =>
       let abs_a := fabs (Interval.inf_raw x) in
       let abs_b := fabs (Interval.sup_raw x) in
       eq (sub abs_a (ftrunc abs_a)) half || eq (sub abs_b (ftrunc abs_b)) half).

(** [impl_dec!(round_ties_even, x, y, { ... })], with the same block as
    [round] *)
Definition round_ties_even : DecInterval -> DecInterval :=
  impl_dec Interval.round_ties_even
    (fun x y =>
       let abs_a := fabs (Interval.inf_raw x) in
       let abs_b := fabs (Interval.sup_raw x) in
       eq (sub abs_a (ftrunc abs_a)) half || eq (sub abs_b (ftrunc abs_b)) half).

(** [impl_dec!(trunc, x, y, (x.inf_raw() != 0.0 && x.inf_raw() == y.inf_raw())
    || (x.sup_raw() != 0.0 && x.sup_raw() == y.sup_raw()))], where [a != b]
    is [!(a == b)] *)
Definition trunc : DecInterval -> DecInterval :=
  impl_dec Interval.trunc
    (fun x y =>
       (negb (eq (Interval.inf_raw x) zero) &&
        eq (Interval.inf_raw x) (Interval.inf_raw y)) ||
       (negb (eq (Interval.sup_raw x) zero) &&
        eq (Interval.sup_raw x) (Interval.sup_raw y))).

End DecInterval.
