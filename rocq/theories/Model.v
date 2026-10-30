(** * A model of the parts of the Rust code that are proved here

    Each definition in [Generic] transcribes the function of the same name
    in [src/simd/generic.rs], line by line, so that the two can be compared
    side by side. The section on intervals at the end does the same for the
    parts of [src/interval.rs], [src/boolean.rs], [src/classify.rs],
    [src/integer.rs], [src/absmax.rs], [src/arith.rs] and [src/basic.rs]
    that [abs], [cancel_minus], [cancel_plus], [ceil], [floor], [max],
    [min], [mul_rev_to_pair], [recip], [round], [round_ties_even], [sign],
    [sqr], [sqrt], [trunc], [neg], [add], [sub], [mul] and [div] of
    intervals use, for each place in
    [src/interval.rs], [src/constants.rs], [src/set_op.rs] and
    [src/bytes.rs] that makes a [DecInterval], and for each place in those
    files and in [src/parse.rs] that makes an [Interval] other than by an
    operation that is not proved here. This file is
    the only one that has to be checked against the Rust code, and
    [Ieee1788.v] the only one that has to be checked against IEEE 1788; the
    other files prove properties of the definitions here.

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

(** [x >= y] and [x <= y], which are false if either is NaN, and true for
    [0.0 >= -0.0] and [0.0 <= -0.0]. *)
Definition ge (x y : f64) : bool := Bleb y x.
Definition le (x y : f64) : bool := Bleb x y.

(** [x == y], which is false if either is NaN, and true for [0.0 == -0.0]. *)
Definition eq (x y : f64) : bool := Beqb x y.

(** [x.partial_cmp(&y)] of [f64]: [None] if either is NaN, and otherwise
    [Some] of how [x] compares to [y], with [Lt], [Eq] and [Gt] for
    [Less], [Equal] and [Greater], [0.0] equal to [-0.0], and -inf and +inf
    below and above every other float. This is Flocq's [Bcompare]. *)
Definition partial_cmp (x y : f64) : option comparison := Bcompare x y.

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

(** [pub(super) fn mul1_ru_slow(x: f64, y: f64) -> f64] *)
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

(** [fn mul1_ru_tiny<const FMA: bool>(x: f64, y: f64) -> f64] *)
Definition mul1_ru_tiny (fma : bool) (x y : f64) : option f64 :=
  (* The [const]s, as in [sqrt1_slow]. *)
  let two_pow_64 := of_u64 (2^64) in
  let two_pow_128 := mul two_pow_64 two_pow_64 in
  let two_pow_m128 := div (of_u64 1) two_pow_128 in
  let p := mul x y in
  let special := negb (is_finite x && is_finite y) || eq x zero || eq y zero in
  if special || (-968 <=? exponent p) then mul1_ru_slow x y
  else if eq p zero then
    (* [p.is_sign_negative()] is [Bsign p], as [p] is not NaN here: [x] and
       [y] are finite. *)
    Some (if Bsign p then p else from_bits 1)
  else
    let '(rs, ok) := mul1_ru_fast fma (mul x two_pow_128) y in
    (* [debug_assert!(ok)] panics in a debug build. *)
    if negb ok then None
    else
      let q := mul rs two_pow_m128 in
      Some (if lt (mul q two_pow_128) rs then step_up q else q).

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

(** [fn max1(x: f64, y: f64) -> f64] and [fn min1(x: f64, y: f64) -> f64],
    where [f64::is_nan] is Flocq's [is_nan]. [to_bits] gives the bit
    patterns of [x] and [y] where they are zeros. *)
Definition max1 (x y : f64) : f64 :=
  if is_nan x then y
  else if is_nan y then x
  else if eq x zero && eq y zero then from_bits (Z.land (to_bits x) (to_bits y))
  else if gt x y then x
  else y.

(** [fn maximum1(x: f64, y: f64) -> f64], where [f64::NAN] is the NaN of
    the model. *)
Definition maximum1 (x y : f64) : f64 :=
  if is_nan x || is_nan y then B754_nan else max1 x y.

Definition min1 (x y : f64) : f64 :=
  if is_nan x then y
  else if is_nan y then x
  else if eq x zero && eq y zero then from_bits (Z.lor (to_bits x) (to_bits y))
  else if lt x y then x
  else y.

(** [fn minimum1(x: f64, y: f64) -> f64] *)
Definition minimum1 (x y : f64) : f64 :=
  if is_nan x || is_nan y then B754_nan else min1 x y.

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
  lanewise2 x y (mul1_ru_fast fma) (mul1_ru_tiny fma).

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

(** [pub(crate) fn max(x: F64X2, y: F64X2) -> F64X2],
    [pub(crate) fn maximum(x: F64X2, y: F64X2) -> F64X2],
    [pub(crate) fn min(x: F64X2, y: F64X2) -> F64X2] and
    [pub(crate) fn minimum(x: F64X2, y: F64X2) -> F64X2] *)
Definition max (x y : F64X2) : F64X2 :=
  (max1 (fst x) (fst y), max1 (snd x) (snd y)).
Definition maximum (x y : F64X2) : F64X2 :=
  (maximum1 (fst x) (fst y), maximum1 (snd x) (snd y)).
Definition min (x y : F64X2) : F64X2 :=
  (min1 (fst x) (fst y), min1 (snd x) (snd y)).
Definition minimum (x y : F64X2) : F64X2 :=
  (minimum1 (fst x) (fst y), minimum1 (snd x) (snd y)).

(** [pub(crate) fn shuffle02(x: F64X2, y: F64X2) -> F64X2],
    [pub(crate) fn shuffle03(x: F64X2, y: F64X2) -> F64X2],
    [pub(crate) fn shuffle13(x: F64X2, y: F64X2) -> F64X2] and
    [pub(crate) fn swap(x: F64X2) -> F64X2] *)
Definition shuffle02 (x y : F64X2) : F64X2 := (fst x, fst y).
Definition shuffle03 (x y : F64X2) : F64X2 := (fst x, snd y).
Definition shuffle13 (x y : F64X2) : F64X2 := (snd x, snd y).
Definition swap (x : F64X2) : F64X2 := (snd x, fst x).

(** [pub(crate) fn add_rn(x: F64X2, y: F64X2) -> F64X2],
    [pub(crate) fn sub_rn(x: F64X2, y: F64X2) -> F64X2] and
    [pub(crate) fn hadd_rn(x: F64X2, y: F64X2) -> F64X2] *)
Definition add_rn (x y : F64X2) : F64X2 := (add (fst x) (fst y), add (snd x) (snd y)).
Definition sub_rn (x y : F64X2) : F64X2 := (sub (fst x) (fst y), sub (snd x) (snd y)).
Definition hadd_rn (x y : F64X2) : F64X2 := (add (fst x) (snd x), add (fst y) (snd y)).

(** [pub(crate) fn extract(x: F64X2) -> [f64; 2]], with the array as a
    pair. *)
Definition extract (x : F64X2) : f64 * f64 := x.

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

(** ** Masks

    A comparison of two [F64X2]s returns a mask, an [F64X2] with every bit
    of a lane set where the comparison holds and clear where it does not.
    A lane with every bit set is a NaN, which [to_bits] gives the bits of
    another NaN, so the model keeps the bit patterns of the lanes of a mask
    instead. *)

(** [fn mask(b: bool) -> f64], as its bit pattern. *)
Definition mask (b : bool) : Z := if b then 2^64 - 1 else 0.

(** [pub(crate) fn splat(x: f64) -> F64X2] *)
Definition splat (x : f64) : F64X2 := (x, x).

(** [pub(crate) fn constant(x: f64, y: f64) -> F64X2] *)
Definition constant (x y : f64) : F64X2 := (x, y).

(** [pub(crate) fn ge(x: F64X2, y: F64X2) -> F64X2],
    [pub(crate) fn gt(x: F64X2, y: F64X2) -> F64X2],
    [pub(crate) fn le(x: F64X2, y: F64X2) -> F64X2] and
    [pub(crate) fn lt(x: F64X2, y: F64X2) -> F64X2], whose results are
    masks. [ge], [gt], [le] and [lt] in the bodies are the comparisons of
    floats at the top of this file, as a [Definition] cannot call
    itself. *)
Definition ge (x y : F64X2) : Z * Z :=
  (mask (ge (fst x) (fst y)), mask (ge (snd x) (snd y))).
Definition gt (x y : F64X2) : Z * Z :=
  (mask (gt (fst x) (fst y)), mask (gt (snd x) (snd y))).
Definition le (x y : F64X2) : Z * Z :=
  (mask (le (fst x) (fst y)), mask (le (snd x) (snd y))).
Definition lt (x y : F64X2) : Z * Z :=
  (mask (lt (fst x) (fst y)), mask (lt (snd x) (snd y))).

(** [pub(crate) fn bitmask(x: F64X2) -> u32] for a mask [x]: the sign bits
    of its lanes. *)
Definition bitmask (x : Z * Z) : Z :=
  Z.lor (Z.shiftr (fst x) 63) (Z.shiftl (Z.shiftr (snd x) 63) 1).

(** [pub(crate) fn all(x: F64X2) -> bool] for a mask [x] *)
Definition all (x : Z * Z) : bool := bitmask x =? 3.

(** [pub(crate) fn and(x: F64X2, y: F64X2) -> F64X2] for a mask [y], and
    [pub(crate) fn or(x: F64X2, y: F64X2) -> F64X2]. [to_bits] gives the bit
    pattern of a lane of [x] or [y] only if it is not NaN. [Interval::sign],
    their only caller, passes no NaN: it calls [and] on [1.0] and [-1.0],
    and [or] on the results, whose lanes are [1.0], [-1.0] or [0.0]. *)
Definition and (x : F64X2) (y : Z * Z) : F64X2 :=
  (from_bits (Z.land (to_bits (fst x)) (fst y)),
   from_bits (Z.land (to_bits (snd x)) (snd y))).
Definition or (x y : F64X2) : F64X2 :=
  (from_bits (Z.lor (to_bits (fst x)) (to_bits (fst y))),
   from_bits (Z.lor (to_bits (snd x)) (to_bits (snd y)))).

End Generic.

(** ** Intervals

    The parts of [src/interval.rs], [src/boolean.rs], [src/classify.rs],
    [src/integer.rs], [src/absmax.rs], [src/arith.rs] and [src/basic.rs]
    that [Interval::abs], [Interval::ceil], [Interval::floor],
    [Interval::max], [Interval::min], [Interval::mul_rev_to_pair],
    [Interval::recip], [Interval::round], [Interval::round_ties_even],
    [Interval::sign], [Interval::sqr], [Interval::sqrt], [Interval::trunc],
    [-x], [x + y], [x - y], [x * y] and [x / y] of intervals, and their
    decorated versions, use. Those call the backend's [floor], [ceil],
    [round], [round_ties_even], [trunc], [neg0], [splat], [constant],
    [ge], [gt], [le], [lt], [all], [bitmask], [and], [or], [max],
    [maximum], [min], [minimum], [shuffle02], [shuffle03], [shuffle13],
    [swap], [add_ru], [mul_ru], [div_ru], [sqrt1_ru] and [sqrt_rd_ru],
    which are the ones in [Generic] here.
    [Interval::max] and [Interval::min] also read the backend's
    [HAS_MAXIMUM], whose value depends on the backend, so it is the
    argument [has_maximum] here.

    For [ComCommon.v], it also transcribes the other places that make a
    [DecInterval]: [new], the constants, [convex_hull] and [intersection],
    [try_from_be_bytes] and its siblings, and [const_dec_interval!].
    [try_from_be_bytes] calls the backend's [constant].

    For [Valid.v], it also transcribes the places that make an [Interval]
    other than the operations above: the condition that [const_interval!]
    asserts, [TryFrom<(f64, f64)>] of [Interval] and of [DecInterval],
    [try_from_be_bytes] and its siblings of [Interval], [convex_hull] and
    [intersection] of [Interval], and the conversions in [src/parse.rs]
    that [FromStr] and [interval_exact!] call. [convex_hull] and
    [intersection] call the backend's [max] and [min]. *)

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

(** [pub(crate) enum IntervalClass], with the variants [E], [M], [N0],
    [N1], [P0], [P1] and [Z] as [CE], [CM], [CN0], [CN1], [CP0], [CP1] and
    [CZ], as [Z] is the type of integers here. *)
Inductive IntervalClass : Type := CE | CM | CN0 | CN1 | CP0 | CP1 | CZ.

(** [unsafe { transmute(c) }] for a [u8] [c] and the result type
    [IntervalClass], whose behaviour is undefined unless [c] is the
    discriminant of a variant. The model returns [None] then, so a theorem
    that a function returns [Some] shows that it is defined. *)
Definition transmute_class (c : Z) : option IntervalClass :=
  if c =? 0 then Some CE
  else if c =? 3 then Some CM
  else if c =? 11 then Some CN0
  else if c =? 9 then Some CN1
  else if c =? 7 then Some CP0
  else if c =? 6 then Some CP1
  else if c =? 15 then Some CZ
  else None.

(** [c as u8] for an [IntervalClass] [c]: its discriminant, the one that
    [transmute_class] maps to [c]. *)
Definition class_discriminant (c : IntervalClass) : Z :=
  match c with
  | CE => 0 | CM => 3 | CN0 => 11 | CN1 => 9 | CP0 => 7 | CP1 => 6 | CZ => 15
  end.

(** [unsafe { transmute(c) }] for a [u8] [c] and the result type
    [IntervalClass2]. [pub(crate) enum IntervalClass2] has a variant [X_Y]
    for each pair of variants [X] and [Y] of [IntervalClass], which the
    model writes as the pair [(X, Y)], e.g. [M_N0] as [(CM, CN0)]. The
    discriminant of [X_Y] is
    [discr!(X, Y) = ((IntervalClass::X as u8) << 4) | IntervalClass::Y as u8].
    Every discriminant of [IntervalClass] is below 16, so the shift drops
    no bits and the [|] adds, which makes it
    [16 * class_discriminant X + class_discriminant Y], whose quotient and
    remainder by 16 are [class_discriminant X] and [class_discriminant Y].
    So [c] is the discriminant of a variant exactly when [c / 16] and
    [c mod 16] are both discriminants of [IntervalClass], and then it is
    that of [(X, Y)] for the [X] and [Y] that [transmute_class] decodes them
    to. Otherwise the behaviour is undefined, and the model returns [None],
    as [transmute_class] does. A [c] of 256 or more, which no [u8] is, gives
    [None] too, as its [c / 16 >= 16] is no discriminant of
    [IntervalClass]. *)
Definition transmute_class2 (c : Z) : option (IntervalClass * IntervalClass) :=
  let* x := transmute_class (c / 16) in
  let* y := transmute_class (c mod 16) in
  Some (x, y).

Module Interval.

(** [pub const EMPTY: Self], i.e. [[NaN; NaN]]. *)
Definition EMPTY : Interval := {| rep := (B754_nan, B754_nan) |}.

(** [const_interval!(a, b)], which [transmute]s [[-(a), b]] into an
    [Interval]. It does not compile unless
    [a <= b && a != f64::INFINITY && b != f64::NEG_INFINITY]. *)
Definition const_interval (a b : f64) : Interval := {| rep := (opp a, b) |}.

(** [$a <= $b && $a != f64::INFINITY && $b != f64::NEG_INFINITY], which
    [const_interval!(a, b)] asserts in a [const], so that it does not
    compile unless this is [true]. Its [&&] gives the same value as Rocq's,
    and [a != b] is [!(a == b)]. *)
Definition const_interval_ok (a b : f64) : bool :=
  le a b && negb (eq a (B754_infinity false)) && negb (eq b (B754_infinity true)).

(** [pub const ENTIRE: Self], i.e.
    [const_interval!(f64::NEG_INFINITY, f64::INFINITY)], where
    [f64::NEG_INFINITY] and [f64::INFINITY] are [B754_infinity true] and
    [B754_infinity false]. *)
Definition ENTIRE : Interval :=
  const_interval (B754_infinity true) (B754_infinity false).

(** [pub(crate) fn with_infsup_raw(a: f64, b: f64) -> Self] *)
Definition with_infsup_raw (a b : f64) : Interval :=
  {| rep := Generic.constant (opp a) b |}.

(** [pub(crate) fn inf_raw(self) -> f64] and
    [pub(crate) fn sup_raw(self) -> f64] *)
Definition inf_raw (self : Interval) : f64 := opp (fst (rep self)).
Definition sup_raw (self : Interval) : f64 := snd (rep self).

(** [fn try_from((a, b): (f64, f64)) -> Result<Self>] of
    [impl TryFrom<(f64, f64)> for Interval], with [Ok(x)] as [Some x] and
    the [Err] as [None]. *)
Definition try_from (a b : f64) : option Interval :=
  if le a b && negb (eq a (B754_infinity false)) && negb (eq b (B754_infinity true))
  then Some (with_infsup_raw a b)
  else None.

(** [pub fn try_from_be_bytes(bytes: [u8; 16]) -> Option<Self>],
    [try_from_le_bytes] and [try_from_ne_bytes] of [Interval], which
    [impl_try_from_bytes!] in [src/bytes.rs] defines. [a] and [b] are the
    floats that [f64::from_be_bytes] and so on decode from [bytes[..8]] and
    [bytes[8..16]], and [0.0] is +0. [a.is_sign_negative()] is Flocq's
    [Bsign a], and [b.is_sign_positive()] is [negb (Bsign b)], which differ
    from Rust only for a NaN, for which [a <= b] is false, so the condition
    is false either way. *)
Definition try_from_bytes (a b : f64) : option Interval :=
  if le a b
     && negb (eq a (B754_infinity false))
     && negb (eq b (B754_infinity true))
     && (negb (eq a zero) || Bsign a)
     && (negb (eq b zero) || negb (Bsign b))
  then Some (with_infsup_raw a b)
  else if eq a (B754_infinity false) && eq b (B754_infinity true) then Some EMPTY
  else None.

(** [fn try_from_ninterval_exact(x: NInterval) -> Result<Self>] in
    [src/parse.rs], with [Ok(x)] as [Some x] and the [Err] as [None]. [a]
    and [b] are the floats [a.f] and [b.f] that [number_to_f64] computes
    from the bounds of [x] with MPFR, and [inexact] is
    [a.inexact || b.inexact]. The model takes them as arguments, and the
    theorems hold for any. [unwrap_or(Self::EMPTY)] is the [match]. *)
Definition try_from_ninterval_exact (a b : f64) (inexact : bool) :
    option Interval :=
  let x := match try_from a b with Some x => x | None => EMPTY end in
  if inexact then None else Some x.

(** [pub fn is_common_interval(self) -> bool] *)
Definition is_common_interval (self : Interval) : bool :=
  Generic.all (Generic.lt (rep self) (Generic.splat infinity)).

(** [pub fn is_empty(self) -> bool], where [f64::is_nan] is Flocq's
    [is_nan]. *)
Definition is_empty (self : Interval) : bool := is_nan (fst (rep self)).

(** [pub fn is_singleton(self) -> bool] *)
Definition is_singleton (self : Interval) : bool :=
  eq (inf_raw self) (sup_raw self).

(** [pub fn contains(self, rhs: f64) -> bool], where [f64::is_finite] is
    Flocq's [is_finite], which is true exactly for the floats that are
    neither infinite nor NaN, as [f64::is_finite] is, and whose [&] on
    [bool]s gives the same value as [&&]. *)
Definition contains (self : Interval) (rhs : f64) : bool :=
  is_finite rhs &&
  Generic.all (Generic.le (Generic.neg0 (Generic.splat rhs)) (rep self)).

(** [pub(crate) fn either_empty(self, rhs: Self) -> bool], whose [|] on
    [bool]s gives the same value as [||]. *)
Definition either_empty (self rhs : Interval) : bool :=
  is_empty self || is_empty rhs.

(** [pub fn convex_hull(self, rhs: Self) -> Self] in [src/set_op.rs]. Each
    [return] is the value of an [if] whose [else] holds the rest of the
    body. *)
Definition convex_hull (self rhs : Interval) : Interval :=
  if is_empty self then rhs
  else if is_empty rhs then self
  else {| rep := Generic.max (rep self) (rep rhs) |}.

(** [pub fn intersection(self, rhs: Self) -> Self] in [src/set_op.rs],
    whose [return] is the value of an [if] whose [else] holds the rest of
    the body *)
Definition intersection (self rhs : Interval) : Interval :=
  if either_empty self rhs then EMPTY
  else
    let i := {| rep := Generic.min (rep self) (rep rhs) |} in
    if gt (inf_raw i) (sup_raw i) then EMPTY else i.

(** [pub(crate) fn classify(self) -> IntervalClass]. The casts
    [bitmask(...) as u8] keep the value, which is below 4, and are left
    out. *)
Definition classify (self : Interval) : option IntervalClass :=
  let zero := Generic.splat zero in
  let ge_zero := Generic.bitmask (Generic.ge (rep self) zero) in
  let le_zero := Generic.bitmask (Generic.le (rep self) zero) in
  let* l := shl 8 le_zero 2 in
  transmute_class (Z.lor l ge_zero).

(** [pub(crate) fn classify2(self, rhs: Self) -> IntervalClass2], where the
    casts [self.classify() as u8] and [rhs.classify() as u8] are
    [class_discriminant]. *)
Definition classify2 (self rhs : Interval) :
    option (IntervalClass * IntervalClass) :=
  let* c1 := classify self in
  let* c2 := classify rhs in
  let* l := shl 8 (class_discriminant c1) 4 in
  transmute_class2 (Z.lor l (class_discriminant c2)).

(** [pub fn abs(self) -> Self] *)
Definition abs (self : Interval) : option Interval :=
  let* c := classify self in
  match c with
  | CE | CP0 | CP1 | CZ => Some self
  | CM =>
      let x := rep self in
      let r := Generic.max x (Generic.swap x) in
      Some {| rep := Generic.shuffle02 (Generic.splat zero) r |}
  | CN0 | CN1 => Some {| rep := Generic.swap (rep self) |}
  end.

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

(** [pub fn max(self, rhs: Self) -> Self]. It branches on the backend's
    [HAS_MAXIMUM], which is [true] in [generic.rs] and [false] in
    [x86_64.rs], so it is the argument [has_maximum], as [HAS_FMA] is for
    [mul]. *)
Definition max (has_maximum : bool) (self rhs : Interval) : Interval :=
  if has_maximum then
    let min := Generic.minimum (rep self) (rep rhs) in
    let max := Generic.maximum (rep self) (rep rhs) in
    {| rep := Generic.shuffle03 min max |}
  else if either_empty self rhs then EMPTY
  else
    let min := Generic.min (rep self) (rep rhs) in
    let max := Generic.max (rep self) (rep rhs) in
    {| rep := Generic.shuffle03 min max |}.

(** [pub fn min(self, rhs: Self) -> Self], with [has_maximum] as for
    [max]. *)
Definition min (has_maximum : bool) (self rhs : Interval) : Interval :=
  if has_maximum then
    let max := Generic.maximum (rep self) (rep rhs) in
    let min := Generic.minimum (rep self) (rep rhs) in
    {| rep := Generic.shuffle03 max min |}
  else if either_empty self rhs then EMPTY
  else
    let max := Generic.max (rep self) (rep rhs) in
    let min := Generic.min (rep self) (rep rhs) in
    {| rep := Generic.shuffle03 max min |}.

(** [pub fn round(self) -> Self] *)
Definition round (self : Interval) : Interval :=
  {| rep := Generic.round (rep self) |}.

(** [pub fn round_ties_even(self) -> Self] *)
Definition round_ties_even (self : Interval) : Interval :=
  {| rep := Generic.round_ties_even (rep self) |}.

(** [pub fn sign(self) -> Self], where [1.0] is [of_u64 1], as in
    [sqrt1_slow], and [-1.0] is [opp] of it, as Rust's [-1.0] negates the
    literal [1.0]. *)
Definition sign (self : Interval) : Interval :=
  if is_empty self then EMPTY
  else
    let zero := Generic.splat zero in
    let gt_zero_mask := Generic.gt (rep self) zero in
    let lt_zero_mask := Generic.lt (rep self) zero in
    let one_or_zero := Generic.and (Generic.splat (of_u64 1)) gt_zero_mask in
    let m_one_or_zero :=
      Generic.and (Generic.splat (opp (of_u64 1))) lt_zero_mask in
    let r := Generic.or one_or_zero m_one_or_zero in
    {| rep := r |}.

(** [pub fn sqrt(self) -> Self]. Its [sqrt1_ru] and [sqrt_rd_ru] call
    [sqrt1_ru_impl::<HAS_FMA>] and [sqrt1_rd_impl::<HAS_FMA>], so
    [has_fma] is an argument, as for [mul]. Each [return] is the value of
    an [if] whose [else] holds the rest of the body, and [0.0] is +0. *)
Definition sqrt (has_fma : bool) (self : Interval) : option Interval :=
  if is_empty self then Some EMPTY
  else
    let a := inf_raw self in
    let b := sup_raw self in
    if lt b zero then Some EMPTY
    else if le a zero then
      let* s := Generic.sqrt1_ru has_fma b in
      Some (with_infsup_raw zero s)
    else
      let* r := Generic.sqrt_rd_ru has_fma (Generic.neg0 (rep self)) in
      Some {| rep := Generic.neg0 r |}.

(** [pub fn trunc(self) -> Self] *)
Definition trunc (self : Interval) : Interval :=
  {| rep := Generic.trunc (rep self) |}.

(** [fn neg(self) -> Self] of [impl Neg for Interval] *)
Definition neg (self : Interval) : Interval :=
  {| rep := Generic.swap (rep self) |}.

(** [fn add(self, rhs: Self) -> Self] of [impl Add for Interval] *)
Definition add (self rhs : Interval) : option Interval :=
  let x := rep self in
  let y := rep rhs in
  let* r := Generic.add_ru x y in
  Some {| rep := r |}.

(** [fn sub(self, rhs: Self) -> Self] of [impl Sub for Interval] *)
Definition sub (self rhs : Interval) : option Interval :=
  let x := rep self in
  let y := Generic.swap (rep rhs) in
  let* r := Generic.add_ru x y in
  Some {| rep := r |}.

(** [pub fn cancel_minus(self, rhs: Self) -> Self], with [0.5] as [half],
    [f64::INFINITY] as [infinity], and [unreachable!()] as [None]. Each
    [return] is the value of an [if] whose [else] holds the rest of the
    body. It comes before [mul], which shadows the [mul] on floats that
    [0.5 * ma] is. *)
Definition cancel_minus (self rhs : Interval) : option Interval :=
  if is_empty self && (is_empty rhs || is_common_interval rhs) then Some EMPTY
  else if negb (is_common_interval self) || is_empty rhs
          || negb (is_common_interval rhs) then Some ENTIRE
  else
    let x := rep self in
    let y := rep rhs in
    let* z := Generic.sub_ru x y in
    let w_rn := Generic.hadd_rn x y in
    let '(wx, wy) := Generic.extract w_rn in
    let '(x, y, w_rn) :=
      if eq wx infinity && eq wy infinity then
        let '(ma, b) := Generic.extract x in
        let '(mc, d) := Generic.extract y in
        let x := Generic.constant (mul half ma) (mul half b) in
        let y := Generic.constant (mul half mc) (mul half d) in
        (x, y, Generic.hadd_rn x y)
      else (x, y, w_rn) in
    let '(wx, wy) := Generic.extract w_rn in
    match partial_cmp wx wy with
    | Some Gt => Some {| rep := z |}
    | Some Lt => Some ENTIRE
    | Some Eq =>
        let hi := Generic.max (Generic.shuffle02 x y) (Generic.shuffle13 x y) in
        let lo := Generic.min (Generic.shuffle02 x y) (Generic.shuffle13 x y) in
        let t := Generic.sub_rn hi w_rn in
        let dw := Generic.add_rn lo t in
        let '(dwx, dwy) := Generic.extract dw in
        if ge dwx dwy then Some {| rep := z |} else Some ENTIRE
    | None => None
    end.

(** [pub fn cancel_plus(self, rhs: Self) -> Self], where [-rhs] is
    [neg rhs]. *)
Definition cancel_plus (self rhs : Interval) : option Interval :=
  cancel_minus self (neg rhs).

(** [pub(crate) fn zero() -> Self]. [zero], [sqr], [mul], the divisions,
    [recip] and [div] come last, as [zero], [mul] and [div] shadow the
    [zero], [mul] and [div] on floats, and [classify], [abs], [sign] and
    [sqrt] above use that [zero]. [sqr] and [div] come after [zero], which
    they call. *)
Definition zero : Interval := {| rep := Generic.splat zero |}.

(** [pub fn sqr(self) -> Self]. Its [mul_ru] calls [mul_ru_impl::<HAS_FMA>],
    so [has_fma] is an argument, as for [mul]. [Self::zero()] is [zero],
    and [0.0] is the float [Model.zero], i.e. +0, which [zero] shadows
    here. *)
Definition sqr (has_fma : bool) (self : Interval) : option Interval :=
  let* c := classify self in
  match c with
  | CE => Some EMPTY
  | CZ => Some zero
  | CM =>
      let x := rep self in
      let* r := Generic.mul_ru has_fma x x in
      let r := Generic.max r (Generic.swap r) in
      Some {| rep := Generic.shuffle02 (Generic.splat Model.zero) r |}
  | CN0 | CN1 =>
      let x := Generic.swap (rep self) in
      let y := Generic.neg0 x in
      let* r := Generic.mul_ru has_fma x y in
      Some {| rep := r |}
  | CP0 | CP1 =>
      let x := rep self in
      let y := Generic.neg0 x in
      let* r := Generic.mul_ru has_fma x y in
      Some {| rep := r |}
  end.

(** [fn mul(self, rhs: Self) -> Self] of [impl Mul for Interval]. Its
    [mul_ru] calls [mul_ru_impl::<HAS_FMA>], and [HAS_FMA] depends on the
    target, so it is an argument, as for [Generic.mul_ru]. The variant
    [X_Y] of [IntervalClass2] is the pair [(X, Y)], as in
    [transmute_class2], and [Self::zero()] is [zero]. *)
Definition mul (has_fma : bool) (self rhs : Interval) : option Interval :=
  let* c := classify2 self rhs in
  match c with
  | (CE, CE) | (CE, CM) | (CE, CN0) | (CE, CN1) | (CE, CP0) | (CE, CP1)
  | (CE, CZ) | (CM, CE) | (CN0, CE) | (CN1, CE) | (CP0, CE) | (CP1, CE)
  | (CZ, CE) =>
      Some EMPTY
  | (CM, CZ) | (CN0, CZ) | (CN1, CZ) | (CP0, CZ) | (CP1, CZ) | (CZ, CM)
  | (CZ, CN0) | (CZ, CN1) | (CZ, CP0) | (CZ, CP1) | (CZ, CZ) =>
      Some zero
  | (CM, CM) =>
      let x := Generic.shuffle02 (rep self) (rep self) in
      let y := Generic.swap (rep rhs) in
      let* xy := Generic.mul_ru has_fma x y in
      let z := Generic.shuffle13 (rep self) (rep self) in
      let w := rep rhs in
      let* zw := Generic.mul_ru has_fma z w in
      let r := Generic.max xy zw in
      Some {| rep := r |}
  | (CM, CN0) | (CM, CN1) =>
      let x := Generic.swap (rep self) in
      let y := Generic.shuffle02 (rep rhs) (rep rhs) in
      let* r := Generic.mul_ru has_fma x y in
      Some {| rep := r |}
  | (CM, CP0) | (CM, CP1) =>
      let x := rep self in
      let y := Generic.shuffle13 (rep rhs) (rep rhs) in
      let* r := Generic.mul_ru has_fma x y in
      Some {| rep := r |}
  | (CN0, CM) | (CN1, CM) =>
      let x := Generic.shuffle02 (rep self) (rep self) in
      let y := Generic.swap (rep rhs) in
      let* r := Generic.mul_ru has_fma x y in
      Some {| rep := r |}
  | (CN0, CN0) | (CN0, CN1) | (CN1, CN0) | (CN1, CN1) =>
      let x := Generic.swap (rep self) in
      let x := Generic.neg0 x in
      let y := Generic.swap (rep rhs) in
      let* r := Generic.mul_ru has_fma x y in
      Some {| rep := r |}
  | (CN0, CP0) | (CN0, CP1) | (CN1, CP0) | (CN1, CP1) =>
      let x := rep self in
      let y := Generic.neg0 (rep rhs) in
      let y := Generic.swap y in
      let* r := Generic.mul_ru has_fma x y in
      Some {| rep := r |}
  | (CP0, CM) | (CP1, CM) =>
      let x := Generic.shuffle13 (rep self) (rep self) in
      let y := rep rhs in
      let* r := Generic.mul_ru has_fma x y in
      Some {| rep := r |}
  | (CP0, CN0) | (CP0, CN1) | (CP1, CN0) | (CP1, CN1) =>
      let x := Generic.neg0 (rep self) in
      let x := Generic.swap x in
      let y := rep rhs in
      let* r := Generic.mul_ru has_fma x y in
      Some {| rep := r |}
  | (CP0, CP0) | (CP0, CP1) | (CP1, CP0) | (CP1, CP1) =>
      let x := rep self in
      let y := Generic.neg0 (rep rhs) in
      let* r := Generic.mul_ru has_fma x y in
      Some {| rep := r |}
  end.

(** [pub(crate) fn div_m_n1(self, rhs: Self) -> Self] and the other
    divisions of [[a, b]] by [[c, d]] in [src/basic.rs], one for each case
    of [div] below. Their [div_ru] calls [div_ru_impl::<HAS_FMA>], so
    [has_fma] is an argument, as for [mul], and [f64::INFINITY] is
    [infinity]. *)
Definition div_m_n1 (has_fma : bool) (self rhs : Interval) : option Interval :=
  let x := Generic.swap (rep self) in
  let y := Generic.swap (rep rhs) in
  let y := Generic.neg0 y in
  let y := Generic.shuffle02 y y in
  let* r := Generic.div_ru has_fma x y in
  Some {| rep := r |}.

(** [pub(crate) fn div_m_p1(self, rhs: Self) -> Self] *)
Definition div_m_p1 (has_fma : bool) (self rhs : Interval) : option Interval :=
  let x := rep self in
  let y := Generic.neg0 (rep rhs) in
  let y := Generic.shuffle02 y y in
  let* r := Generic.div_ru has_fma x y in
  Some {| rep := r |}.

(** [pub(crate) fn div_n_n0(self, rhs: Self) -> Self] *)
Definition div_n_n0 (has_fma : bool) (self rhs : Interval) : option Interval :=
  let x := Generic.swap (rep self) in
  let y := rep rhs in
  let* r := Generic.div_ru has_fma x y in
  Some {| rep := Generic.shuffle02 r (Generic.splat infinity) |}.

(** [pub(crate) fn div_n_n1(self, rhs: Self) -> Self] *)
Definition div_n_n1 (has_fma : bool) (self rhs : Interval) : option Interval :=
  let x := Generic.neg0 (rep self) in
  let x := Generic.swap x in
  let y := rep rhs in
  let* r := Generic.div_ru has_fma x y in
  Some {| rep := r |}.

(** [pub(crate) fn div_n_p0(self, rhs: Self) -> Self] *)
Definition div_n_p0 (has_fma : bool) (self rhs : Interval) : option Interval :=
  let x := rep self in
  let y := rep rhs in
  let* r := Generic.div_ru has_fma x y in
  Some {| rep := Generic.shuffle03 (Generic.splat infinity) r |}.

(** [pub(crate) fn div_n_p1(self, rhs: Self) -> Self] *)
Definition div_n_p1 (has_fma : bool) (self rhs : Interval) : option Interval :=
  let x := rep self in
  let y := Generic.neg0 (rep rhs) in
  let* r := Generic.div_ru has_fma x y in
  Some {| rep := r |}.

(** [pub(crate) fn div_p_n0(self, rhs: Self) -> Self] *)
Definition div_p_n0 (has_fma : bool) (self rhs : Interval) : option Interval :=
  let x := rep self in
  let y := rep rhs in
  let* r := Generic.div_ru has_fma x y in
  Some {| rep := Generic.shuffle02 (Generic.splat infinity) r |}.

(** [pub(crate) fn div_p_n1(self, rhs: Self) -> Self] *)
Definition div_p_n1 (has_fma : bool) (self rhs : Interval) : option Interval :=
  let x := Generic.swap (rep self) in
  let x := Generic.neg0 x in
  let y := Generic.swap (rep rhs) in
  let* r := Generic.div_ru has_fma x y in
  Some {| rep := r |}.

(** [pub(crate) fn div_p_p0(self, rhs: Self) -> Self] *)
Definition div_p_p0 (has_fma : bool) (self rhs : Interval) : option Interval :=
  let x := rep self in
  let y := Generic.swap (rep rhs) in
  let* r := Generic.div_ru has_fma x y in
  Some {| rep := Generic.shuffle02 r (Generic.splat infinity) |}.

(** [pub(crate) fn div_p_p1(self, rhs: Self) -> Self] *)
Definition div_p_p1 (has_fma : bool) (self rhs : Interval) : option Interval :=
  let x := rep self in
  let y := Generic.neg0 (rep rhs) in
  let y := Generic.swap y in
  let* r := Generic.div_ru has_fma x y in
  Some {| rep := r |}.

(** [pub fn recip(self) -> Self], with [has_fma] as for the divisions
    above. [-1.0] is [opp (of_u64 1)], as in [sign]. *)
Definition recip (has_fma : bool) (self : Interval) : option Interval :=
  let* c := classify self in
  match c with
  | CE | CZ => Some EMPTY
  | CM => Some ENTIRE
  | CN0 =>
      let x := Generic.splat (opp (of_u64 1)) in
      let y := rep self in
      let* r := Generic.div_ru has_fma x y in
      Some {| rep := Generic.shuffle02 (Generic.splat infinity) r |}
  | CN1 =>
      let x := Generic.splat (opp (of_u64 1)) in
      let y := Generic.swap (rep self) in
      let* r := Generic.div_ru has_fma x y in
      Some {| rep := r |}
  | CP0 =>
      let x := Generic.splat (opp (of_u64 1)) in
      let y := rep self in
      let* r := Generic.div_ru has_fma x y in
      Some {| rep := Generic.shuffle13 r (Generic.splat infinity) |}
  | CP1 =>
      let x := Generic.splat (opp (of_u64 1)) in
      let y := Generic.swap (rep self) in
      let* r := Generic.div_ru has_fma x y in
      Some {| rep := r |}
  end.

(** [fn div(self, rhs: Self) -> Self] of [impl Div for Interval], with
    [has_fma] as for the divisions above, and the variants of
    [IntervalClass2] and [Self::zero()] as in [mul]. *)
Definition div (has_fma : bool) (self rhs : Interval) : option Interval :=
  let* c := classify2 self rhs in
  match c with
  | (CE, CE) | (CE, CM) | (CE, CN0) | (CE, CN1) | (CE, CP0) | (CE, CP1)
  | (CE, CZ) | (CM, CE) | (CM, CZ) | (CN0, CE) | (CN0, CZ) | (CN1, CE)
  | (CN1, CZ) | (CP0, CE) | (CP0, CZ) | (CP1, CE) | (CP1, CZ) | (CZ, CE)
  | (CZ, CZ) =>
      Some EMPTY
  | (CM, CM) | (CM, CN0) | (CM, CP0) | (CN0, CM) | (CN1, CM) | (CP0, CM)
  | (CP1, CM) =>
      Some ENTIRE
  | (CZ, CM) | (CZ, CN0) | (CZ, CN1) | (CZ, CP0) | (CZ, CP1) => Some zero
  | (CM, CN1) => div_m_n1 has_fma self rhs
  | (CM, CP1) => div_m_p1 has_fma self rhs
  | (CN0, CN0) | (CN1, CN0) => div_n_n0 has_fma self rhs
  | (CN0, CN1) | (CN1, CN1) => div_n_n1 has_fma self rhs
  | (CN0, CP0) | (CN1, CP0) => div_n_p0 has_fma self rhs
  | (CN0, CP1) | (CN1, CP1) => div_n_p1 has_fma self rhs
  | (CP0, CN0) | (CP1, CN0) => div_p_n0 has_fma self rhs
  | (CP0, CN1) | (CP1, CN1) => div_p_n1 has_fma self rhs
  | (CP0, CP0) | (CP1, CP0) => div_p_p0 has_fma self rhs
  | (CP0, CP1) | (CP1, CP1) => div_p_p1 has_fma self rhs
  end.

(** [pub fn mul_rev_to_pair(self, numerator: Self) -> [Self; 2]], with the
    array [[u, v]] as the pair [(u, v)], [has_fma] as for the divisions
    above, the variants of [IntervalClass2] and [Self::zero()] as in [mul],
    and [f64::INFINITY] as [infinity]. *)
Definition mul_rev_to_pair (has_fma : bool) (self numerator : Interval) :
    option (Interval * Interval) :=
  let* c := classify2 numerator self in
  match c with
  | (CE, CE) | (CE, CM) | (CE, CN0) | (CE, CN1) | (CE, CP0) | (CE, CP1)
  | (CE, CZ) | (CM, CE) | (CN0, CE) | (CN1, CE) | (CN1, CZ) | (CP0, CE)
  | (CP1, CE) | (CP1, CZ) | (CZ, CE) =>
      Some (EMPTY, EMPTY)
  | (CM, CZ) | (CN0, CZ) | (CP0, CZ) | (CZ, CZ) | (CM, CM) | (CM, CN0)
  | (CM, CP0) | (CN0, CM) | (CP0, CM) | (CZ, CM) | (CZ, CN0) | (CZ, CP0)
  | (CN0, CN0) | (CN0, CP0) | (CP0, CN0) | (CP0, CP0) =>
      Some (ENTIRE, EMPTY)
  | (CZ, CN1) | (CZ, CP1) => Some (zero, EMPTY)
  | (CN1, CM) =>
      let x := rep numerator in
      let x := Generic.shuffle13 x x in
      let* q := Generic.div_ru has_fma x (rep self) in
      Some ({| rep := Generic.shuffle13 (Generic.splat infinity) q |},
            {| rep := Generic.shuffle02 q (Generic.splat infinity) |})
  | (CP1, CM) =>
      let x := rep numerator in
      let x := Generic.shuffle02 x x in
      let* q := Generic.div_ru has_fma x (rep self) in
      Some ({| rep := Generic.shuffle02 (Generic.splat infinity) q |},
            {| rep := Generic.shuffle13 q (Generic.splat infinity) |})
  | (CM, CN1) => let* z := div_m_n1 has_fma numerator self in Some (z, EMPTY)
  | (CM, CP1) => let* z := div_m_p1 has_fma numerator self in Some (z, EMPTY)
  | (CN1, CN0) => let* z := div_n_n0 has_fma numerator self in Some (z, EMPTY)
  | (CN0, CN1) | (CN1, CN1) =>
      let* z := div_n_n1 has_fma numerator self in Some (z, EMPTY)
  | (CN1, CP0) => let* z := div_n_p0 has_fma numerator self in Some (z, EMPTY)
  | (CN0, CP1) | (CN1, CP1) =>
      let* z := div_n_p1 has_fma numerator self in Some (z, EMPTY)
  | (CP1, CN0) => let* z := div_p_n0 has_fma numerator self in Some (z, EMPTY)
  | (CP0, CN1) | (CP1, CN1) =>
      let* z := div_p_n1 has_fma numerator self in Some (z, EMPTY)
  | (CP1, CP0) => let* z := div_p_p0 has_fma numerator self in Some (z, EMPTY)
  | (CP0, CP1) | (CP1, CP1) =>
      let* z := div_p_p1 has_fma numerator self in Some (z, EMPTY)
  end.

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

(** [pub fn new(x: Interval) -> Self] *)
Definition new (x : Interval) : DecInterval :=
  let d :=
    if Interval.is_empty x then Trv
    else if negb (Interval.is_common_interval x) then Dac
    else Com in
  new_unchecked x d.

(** [fn try_from(x: (f64, f64)) -> Result<Self>] of
    [impl TryFrom<(f64, f64)> for DecInterval], with [Ok] and [Err] as in
    [Interval.try_from], where [x] is the pair [(a, b)]. *)
Definition try_from (a b : f64) : option DecInterval :=
  match Interval.try_from a b with
  | Some x => Some (new x)
  | None => None
  end.

(** [fn from(DecNInterval { x, d }: DecNInterval) -> Self] of
    [impl From<DecNInterval> for DecInterval] in [src/parse.rs], which
    [FromStr] for [DecInterval] calls. [From<NInterval> for Interval],
    which [FromStr] for [Interval] calls, returns the [x] of its result for
    the [d] that [DecNInterval::new] picks. [a] and [b] are the floats
    [a.f] and [b.f] that [number_to_f64] computes from the bounds of [x]
    with MPFR, and [overflow] is [a.overflow || b.overflow]. The model
    takes them as arguments, and the theorems hold for any.
    [unwrap_or(Interval::EMPTY)] is the [match], and [d.min(Decoration::Dac)]
    is [dec_min d Dac]. *)
Definition from_dec_ninterval (a b : f64) (overflow : bool) (d : Decoration) :
    DecInterval :=
  let x :=
    match Interval.try_from a b with Some x => x | None => Interval.EMPTY end in
  let d := if overflow then dec_min d Dac else d in
  set_dec x d.

(** [pub const ENTIRE: Self] *)
Definition ENTIRE : DecInterval := new_unchecked Interval.ENTIRE Dac.

(** A constant that [def_com!(C)] in [src/constants.rs] defines,
    [new_unchecked(Interval::C, Decoration::Com)], where [Interval::C] is
    [const_interval!(a, b)] for two float literals [a] and [b]. *)
Definition def_com (a b : f64) : DecInterval :=
  new_unchecked (Interval.const_interval a b) Com.

(** [pub fn convex_hull(self, rhs: Self) -> Self] and
    [pub fn intersection(self, rhs: Self) -> Self], which [impl_dec!] in
    [src/set_op.rs] defines, where [f] is [Interval::convex_hull] or
    [Interval::intersection]. *)
Definition set_op (f : Interval -> Interval -> Interval)
    (self rhs : DecInterval) : DecInterval :=
  if is_nai self || is_nai rhs then NAI
  else new_unchecked (f (itv self) (itv rhs)) Trv.

(** [impl_dec!(convex_hull)] and [impl_dec!(intersection)] *)
Definition convex_hull : DecInterval -> DecInterval -> DecInterval :=
  set_op Interval.convex_hull.
Definition intersection : DecInterval -> DecInterval -> DecInterval :=
  set_op Interval.intersection.

(** [pub fn try_from_be_bytes(bytes: [u8; 17]) -> Option<Self>],
    [try_from_le_bytes] and [try_from_ne_bytes], which
    [impl_try_from_bytes!] in [src/bytes.rs] defines. [a] and [b] are the
    floats that [f64::from_be_bytes] and so on decode from [bytes[..8]] and
    [bytes[8..16]], and [c] is [bytes[16]]. [return None] from the [match]
    is [let*]. [a.is_sign_negative()] is Flocq's [Bsign a], and
    [b.is_sign_positive()] is [negb (Bsign b)], which differ from Rust only
    for a NaN, for which [a <= b] is false, so the condition is false
    either way. *)
Definition try_from_bytes (a b : f64) (c : Z) : option DecInterval :=
  let* dec :=
    if c =? 0 then Some Ill
    else if c =? 4 then Some Trv
    else if c =? 8 then Some Def
    else if c =? 12 then Some Dac
    else if c =? 16 then Some Com
    else None in
  if le a b
     && negb (eq a (B754_infinity false))
     && negb (eq b (B754_infinity true))
     && (negb (eq a zero) || Bsign a)
     && (negb (eq b zero) || negb (Bsign b))
     && (negb (dec_eqb dec Com) ||
         negb (eq a (B754_infinity true)) && negb (eq b (B754_infinity false)))
  then Some (new_unchecked (Interval.with_infsup_raw a b) dec)
  else if eq a (B754_infinity false) && eq b (B754_infinity true) &&
          dec_eqb dec Trv then Some EMPTY
  else if is_nan a && is_nan b && dec_eqb dec Ill then Some NAI
  else None.

(** [const_dec_interval!(a, b)], which [transmute]s a [#[repr(C)]] struct
    of an [Interval] [x] and a [Decoration] [d] into a [DecInterval], whose
    fields are the same and in the same order. As it calls
    [const_interval!(a, b)], it does not compile unless
    [a <= b && a != f64::INFINITY && b != f64::NEG_INFINITY]. *)
Definition const_dec_interval (a b : f64) : DecInterval :=
  {| itv := Interval.const_interval a b;
     dec := if eq a (B754_infinity true) || eq b (B754_infinity false) then Dac
            else Com |}.

(** [pub fn abs(self) -> Self] *)
Definition abs (self : DecInterval) : option DecInterval :=
  if is_nai self then Some self
  else
    let* x := Interval.abs (itv self) in
    Some (set_dec x (dec self)).

(** [pub fn max(self, rhs: Self) -> Self] and
    [pub fn min(self, rhs: Self) -> Self], where [self.d.min(rhs.d)] is
    [dec_min (dec self) (dec rhs)], with the [has_maximum] of
    [Interval.max] and [Interval.min] as an argument here too *)
Definition max (has_maximum : bool) (self rhs : DecInterval) : DecInterval :=
  if is_nai self then self
  else
    set_dec (Interval.max has_maximum (itv self) (itv rhs))
      (dec_min (dec self) (dec rhs)).
Definition min (has_maximum : bool) (self rhs : DecInterval) : DecInterval :=
  if is_nai self then self
  else
    set_dec (Interval.min has_maximum (itv self) (itv rhs))
      (dec_min (dec self) (dec rhs)).

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

(** [impl_dec!(sign, x, y, x.inf_raw() == 0.0)] *)
Definition sign : DecInterval -> DecInterval :=
  impl_dec Interval.sign (fun x y => eq (Interval.inf_raw x) zero).

(** [pub fn sqr(self) -> Self], where [self.x.sqr()] is
    [Interval.sqr has_fma (itv self)], with the [has_fma] of
    [Interval.sqr] as an argument here too. *)
Definition sqr (has_fma : bool) (self : DecInterval) : option DecInterval :=
  if is_nai self then Some self
  else
    let* x := Interval.sqr has_fma (itv self) in
    Some (set_dec x (dec self)).

(** [pub fn sqrt(self) -> Self], where [self.x.sqrt()] is
    [Interval.sqrt has_fma (itv self)], with the [has_fma] of
    [Interval.sqrt] as an argument here too, and [0.0] is +0. *)
Definition sqrt (has_fma : bool) (self : DecInterval) : option DecInterval :=
  if is_nai self then Some self
  else
    let d := if lt (Interval.inf_raw (itv self)) zero then Trv else dec self in
    let* x := Interval.sqrt has_fma (itv self) in
    Some (set_dec x d).

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

(** [fn neg(self) -> Self] of [impl Neg for DecInterval], where [-self.x]
    is [Interval.neg (itv self)]. [neg], [add], [sub], [mul], [recip] and
    [div] come last, so that the [sub] in [round] and [round_ties_even] is
    still the one on floats, and [mul] and [div] shadow the ones on floats
    in no other definition. *)
Definition neg (self : DecInterval) : DecInterval :=
  if is_nai self then self
  else set_dec (Interval.neg (itv self)) (dec self).

(** [fn add(self, rhs: Self) -> Self] of [impl Add for DecInterval] and
    [fn sub(self, rhs: Self) -> Self] of [impl Sub for DecInterval] *)
Definition add (self rhs : DecInterval) : option DecInterval :=
  if is_nai self || is_nai rhs then Some NAI
  else
    let* x := Interval.add (itv self) (itv rhs) in
    Some (set_dec x (dec_min (dec self) (dec rhs))).
Definition sub (self rhs : DecInterval) : option DecInterval :=
  if is_nai self || is_nai rhs then Some NAI
  else
    let* x := Interval.sub (itv self) (itv rhs) in
    Some (set_dec x (dec_min (dec self) (dec rhs))).

(** [fn mul(self, rhs: Self) -> Self] of [impl Mul for DecInterval], where
    [self.x * rhs.x] is [Interval.mul has_fma (itv self) (itv rhs)], with
    the [has_fma] of [Interval.mul] as an argument here too. *)
Definition mul (has_fma : bool) (self rhs : DecInterval) : option DecInterval :=
  if is_nai self || is_nai rhs then Some NAI
  else
    let* x := Interval.mul has_fma (itv self) (itv rhs) in
    Some (set_dec x (dec_min (dec self) (dec rhs))).

(** [pub fn recip(self) -> Self], where [self.x.recip()] is
    [Interval.recip has_fma (itv self)], with the [has_fma] of
    [Interval.recip] as an argument here too, and [0.0] is +0. *)
Definition recip (has_fma : bool) (self : DecInterval) : option DecInterval :=
  if is_nai self then Some self
  else
    let d := if Interval.contains (itv self) zero then Trv else dec self in
    let* x := Interval.recip has_fma (itv self) in
    Some (set_dec x d).

(** [fn div(self, rhs: Self) -> Self] of [impl Div for DecInterval], where
    [self.x / rhs.x] is [Interval.div has_fma (itv self) (itv rhs)], with
    the [has_fma] of [Interval.div] as an argument here too, and [0.0] is
    +0. *)
Definition div (has_fma : bool) (self rhs : DecInterval) : option DecInterval :=
  if is_nai self || is_nai rhs then Some NAI
  else
    let d :=
      if Interval.contains (itv rhs) zero then Trv
      else dec_min (dec self) (dec rhs) in
    let* x := Interval.div has_fma (itv self) (itv rhs) in
    Some (set_dec x d).

(** [pub fn mul_rev_to_pair(self, numerator: Self) -> [Self; 2]], where
    [self.x.mul_rev_to_pair(numerator.x)] is
    [Interval.mul_rev_to_pair has_fma (itv self) (itv numerator)], with the
    [has_fma] of [Interval.mul_rev_to_pair] as an argument here too, the
    arrays as pairs, as there, [self.d.min(numerator.d)] as
    [dec_min (dec self) (dec numerator)], and [0.0] as +0. *)
Definition mul_rev_to_pair (has_fma : bool) (self numerator : DecInterval) :
    option (DecInterval * DecInterval) :=
  if is_nai self || is_nai numerator then Some (NAI, NAI)
  else
    let* (u, v) := Interval.mul_rev_to_pair has_fma (itv self) (itv numerator) in
    let d :=
      if Interval.contains (itv self) zero then Trv
      else dec_min (dec self) (dec numerator) in
    Some (set_dec u d, set_dec v Trv).

(** [pub fn cancel_minus(self, rhs: Self) -> Self] and
    [pub fn cancel_plus(self, rhs: Self) -> Self], where
    [self.x.cancel_minus(rhs.x)] is
    [Interval.cancel_minus (itv self) (itv rhs)], and the same for
    [cancel_plus]. *)
Definition cancel_minus (self rhs : DecInterval) : option DecInterval :=
  if is_nai self || is_nai rhs then Some NAI
  else
    let* x := Interval.cancel_minus (itv self) (itv rhs) in
    Some (set_dec x Trv).
Definition cancel_plus (self rhs : DecInterval) : option DecInterval :=
  if is_nai self || is_nai rhs then Some NAI
  else
    let* x := Interval.cancel_plus (itv self) (itv rhs) in
    Some (set_dec x Trv).

End DecInterval.
