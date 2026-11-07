(** * A model of the parts of the Rust code that are proved here

    Each definition in [Generic] transcribes the function of the same name
    in [src/simd/generic.rs], line by line, so that the two can be compared
    side by side. The section on intervals at the end, with the one on
    MPFR before it, does the same for the operations of intervals and
    decorated intervals that it lists, the elementary functions among
    them, with the parts of the Rust code outside [generic.rs] that they
    use, for each place in [src/interval.rs],
    [src/interval/dec_interval.rs], [src/constants.rs], [src/set_op.rs]
    and [src/bytes.rs] that makes a [DecInterval], for each place in those
    files and in [src/parse.rs] that makes an [Interval] other than by an
    operation that is not proved here, for the step of the grammar of
    [src/parse.rs] that decorates an interval literal, and for the
    functions of [src/format/digits.rs] that round the bounds that
    [src/format.rs] prints to their digits. The sections [Limbs], [NatLimbs]
    and [Dyadic] do the same for the loops on limbs of [src/limbs.rs], for
    the operations of [Nat] in [src/nat.rs] that those functions of
    [src/parse.rs] and [src/format/digits.rs] call, and for the dyadic
    kernel of [src/dyadic.rs]. This file has to be checked against the Rust
    code, and so do the headers of [ComCommon.v] and [Valid.v], which argue
    from the Rust code that the library makes every [DecInterval] and every
    [Interval] at the places and by the operations transcribed here.
    [Ieee1788.v] and [Elementary.v] are the only files that have to be
    checked against IEEE 1788, [Mpfr.v] has to be checked against the MPFR
    manual, and [Contract.v] has to be checked by reading too: it states
    what the theorems stated for a record [p : point], such as
    [exp_correct_point], assume of its fields. The other files prove
    properties of the definitions in this file, [Ieee1788.v],
    [Elementary.v], [Mpfr.v] and [Contract.v].

    Rust's [f64] is Flocq's IEEE 754 binary64 type, and its [+], [-], [*]
    and [/] are Flocq's [Bplus], [Bminus], [Bmult] and [Bdiv] rounded to
    nearest, ties to even, which is the default rounding mode that
    [generic.rs] relies on. [f64::mul_add] and [f64::sqrt] are Flocq's
    [Bfma] and [Bsqrt] in the same mode, [f64::floor], [f64::ceil],
    [f64::round] and [f64::trunc] are Flocq's [Bnearbyint] toward -inf,
    toward +inf, to nearest with ties away from zero, and toward zero, and
    [f64::abs] is Flocq's [Babs]. Flocq has no remainder, so [%] of [f64]s
    is [frem] below. A const generic parameter, such as [FMA], is an
    ordinary argument.

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
    [Some r] for any number, the Rust function returns [r]. A loop whose
    number of steps no slice bounds, such as the [while] of [knuth_step],
    takes fuel in the same way. *)

From Stdlib Require Import ZArith Rdefinitions List.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From Flocq Require IEEE754.Binary IEEE754.Bits.

Open Scope Z_scope.
Open Scope bool_scope.
Open Scope list_scope.

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
    NaNs; [round_ties_even1] and [DyadicAtan], the only callers, never
    pass a NaN [y]. *)
Definition copysign (x y : f64) : f64 :=
  if Bool.eqb (Bsign x) (Bsign y) then x else opp x.

(** [0.0]. *)
Definition zero : f64 := B754_zero false.

(** [k as f64] for a [u64] [k], which rounds to nearest, ties to even. *)
Definition of_u64 (k : Z) : f64 :=
  binary_normalize 53 1024 _ _ mode_NE k 0 false.

(** [x % y], which is C's [fmod] (LLVM's [frem]): [x - n * y] for [n] the
    integer [x / y] rounded toward zero, computed exactly, as that value is
    always an [f64]. It has the sign of [x], also when it is zero; it is NaN
    if [x] is NaN or an infinity or [y] is NaN or a zero, and [x] if [x] is
    finite and [y] an infinity. For finite [x] and [y], [Z.rem] takes the
    remainder of the significands brought to the smaller exponent [e]; it
    has the sign of the dividend, and [y]'s sign does not matter. *)
Definition frem (x y : f64) : f64 :=
  match x, y with
  | B754_nan, _ | _, B754_nan | B754_infinity _, _ | _, B754_zero _ => B754_nan
  | B754_zero s, _ => B754_zero s
  | B754_finite _ _ _ _, B754_infinity _ => x
  | B754_finite sx mx ex _, B754_finite _ my ey _ =>
      let e := Z.min ex ey in
      let r := Z.rem (cond_Zopp sx (Zpos mx) * 2 ^ (ex - e)) (Zpos my * 2 ^ (ey - e)) in
      binary_normalize 53 1024 _ _ mode_NE r e sx
  end.

(** [x.rem_euclid(y)] of [f64], which the standard library defines as
    [let r = x % y; if r < 0.0 { r + y.abs() } else { r }]. *)
Definition rem_euclid (x y : f64) : f64 :=
  let r := frem x y in
  if lt r zero then add r (fabs y) else r.

(** [x.to_bits()] and [f64::from_bits(b)]. The bit patterns are integers
    instead of [u64], so an addition to one cannot wrap around;
    [Encoding.step_up_no_wrap] shows that those in [step_up] stay in range
    anyway for finite floats, and [Encoding.step_up_if_no_wrap] that those in
    [step_up_if] do for every float. *)
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

(** [fn step_up_if(x: f64, up: bool) -> f64]. [up as u64] is 1 or 0, and
    [b >> 63] of a [u64] is [Z.shiftr] of a nonnegative integer. *)
Definition step_up_if (x : f64) (up : bool) : f64 :=
  let b := to_bits x in
  let u := if up then 1 else 0 in
  from_bits (b - 2 * Z.land u (Z.shiftr b 63) + u).

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
  let r :=
    if negb fma then step_up_if p (negb special && gt e zero)
    else if negb special && gt e zero then step_up p else p in
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

(** [pub(super) fn add1_ru_slow(x: f64, y: f64) -> f64] *)
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

(** [pub(super) fn div1_ru_slow(x: f64, y: f64) -> f64] *)
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

(** [pub(super) fn mul_add1_ru_slow(a: f64, b: f64, c: f64) -> f64] *)
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

(** [pub(crate) fn eq(x: F64X2, y: F64X2) -> F64X2], whose result is a
    mask, with [eq] in the body the comparison of floats at the top of this
    file, as for [ge] above. *)
Definition eq (x y : F64X2) : Z * Z :=
  (mask (eq (fst x) (fst y)), mask (eq (snd x) (snd y))).

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

(** ** Limbs

    The loops of [src/limbs.rs], which [Nat] and the dyadic kernel share.
    A slice of limbs is a [list Z], the least significant limb first,
    holding [val]. A function that writes [out: &mut [u64]] returns its
    new contents, and takes [out.len()] as a [nat] if it reads nothing
    else of [out]. [x.get(i).copied().unwrap_or(0)] is [limb x i], and so
    is [x[i]] for an [i] in bounds: the bounds checks of slices and the
    [usize] arithmetic on lengths and bit counts are not modelled, as
    every range and index is in bounds for the lengths that the callers
    pass. [Ordering] is [comparison]. *)
Module Limbs.

Fixpoint val (x : list Z) : Z :=
  match x with nil => 0 | a :: x' => a + 2 ^ 64 * val x' end.

Definition limb (x : list Z) (i : nat) : Z := nth i x 0.

(** [out[i..i + w.len()] = w] *)
Definition update (out : list Z) (i : nat) (w : list Z) : list Z :=
  firstn i out ++ w ++ skipn (i + length w) out.

(** [a.overflowing_add(b)] and [a.overflowing_sub(b)] of [u64]s *)
Definition ovf_add (a b : Z) : Z * bool := ((a + b) mod 2 ^ 64, 2 ^ 64 <=? a + b).
Definition ovf_sub (a b : Z) : Z * bool := ((a - b) mod 2 ^ 64, a <? b).

(** [x.iter().rposition(|&l| l != 0)] *)
Fixpoint rposition_nonzero (x : list Z) : option nat :=
  match x with
  | nil => None
  | a :: x' =>
      match rposition_nonzero x' with
      | Some i => Some (S i)
      | None => if a =? 0 then None else Some O
      end
  end.

(** [fn bit_len(x: &[u64]) -> u64] *)
Definition bit_len (x : list Z) : Z :=
  match rposition_nonzero x with
  | None => 0
  | Some i => 64 * Z.of_nat i + 64 - leading_zeros 64 (limb x i)
  end.

(** [fn cmp(x: &[u64], y: &[u64]) -> Ordering]: [for i in (0..k).rev()] *)
Fixpoint cmp_from (x y : list Z) (k : nat) : comparison :=
  match k with
  | O => Eq
  | S i =>
      let a := limb x i in
      let b := limb y i in
      if negb (a =? b) then Z.compare a b else cmp_from x y i
  end.

Definition cmp (x y : list Z) : comparison :=
  cmp_from x y (Nat.max (length x) (length y)).

(** [fn add_assign(x: &mut [u64], y: &[u64]) -> bool], where [hd 0] and
    [tl] walk [y] as [limb y i] does. *)
Fixpoint add_assign_from (x y : list Z) (carry : bool) : list Z * bool :=
  match x with
  | nil => (nil, carry)
  | a :: x' =>
      let (t, c1) := ovf_add a (hd 0 y) in
      let (t, c2) := ovf_add t (Z.b2z carry) in
      let (r, c) := add_assign_from x' (tl y) (c1 || c2) in
      (t :: r, c)
  end.

Definition add_assign (x y : list Z) : list Z * bool := add_assign_from x y false.

(** [fn sub_assign(x: &mut [u64], y: &[u64], borrow: bool) -> bool] *)
Fixpoint sub_assign (x y : list Z) (borrow : bool) : list Z * bool :=
  match x with
  | nil => (nil, borrow)
  | a :: x' =>
      let (t, b1) := ovf_sub a (hd 0 y) in
      let (t, b2) := ovf_sub t (Z.b2z borrow) in
      let (r, b) := sub_assign x' (tl y) (b1 || b2) in
      (t :: r, b)
  end.

(** [fn mul_add_limb(x: &mut [u64], m: u64, a: u64) -> u64]. The [u128]
    product and sum are checked as one, as each of them is at most their
    final sum. *)
Fixpoint mul_add_limb (x : list Z) (m carry : Z) : option (list Z * Z) :=
  match x with
  | nil => Some (nil, carry)
  | l :: x' =>
      let* t := checked_u 128 (l * m + carry) in
      (* [t as u64] and [(t >> 64) as u64] *)
      let* (r, c) := mul_add_limb x' m (Z.shiftr t 64 mod 2 ^ 64) in
      Some (t mod 2 ^ 64 :: r, c)
  end.

(** [fn mul_add_row(row: &mut [u64], y: &[u64], a: u64) -> u64]:
    [row.iter_mut().zip(y)] stops at the shorter of the two, and the
    carry is a [u128], returned as a [u64]. *)
Fixpoint mul_add_row_from (row y : list Z) (a carry : Z) : option (list Z * Z) :=
  match row, y with
  | o :: row', b :: y' =>
      let* t := checked_u 128 (a * b + o + carry) in
      let* (r, c) := mul_add_row_from row' y' a (Z.shiftr t 64) in
      Some (t mod 2 ^ 64 :: r, c)
  | _, _ => Some (row, carry)
  end.

Definition mul_add_row (row y : list Z) (a : Z) : option (list Z * Z) :=
  let* (r, c) := mul_add_row_from row y a 0 in Some (r, c mod 2 ^ 64).

(** [fn mul_into(out: &mut [u64], x: &[u64], y: &[u64])] for
    [n = out.len()]: [out.fill(0)], then the row of each limb [x[i]]. *)
Fixpoint mul_into_from (out x y : list Z) (i : nat) : option (list Z) :=
  match x with
  | nil => Some out
  | a :: x' =>
      let row := firstn (length y) (skipn i out) in
      let* (row', top) := mul_add_row row y a in
      mul_into_from (update out i (row' ++ top :: nil)) x' y (S i)
  end.

Definition mul_into (n : nat) (x y : list Z) : option (list Z) :=
  mul_into_from (repeat 0 n) x y 0.

(** [fn shl_into(out: &mut [u64], x: &[u64], sh: u64)] for
    [n = out.len()], where
    [usize::try_from(sh / 64).unwrap_or(usize::MAX).min(out.len())] is
    [Nat.min (Z.to_nat (sh / 64)) n] on any target, and the [u128] shift
    is by [sh % 64 < 64] bits. *)
Fixpoint shl_limbs (k : nat) (x : list Z) (s carry : Z) : list Z :=
  match k with
  | O => nil
  | S k' =>
      let t := Z.shiftl (hd 0 x) s mod 2 ^ 128 in
      Z.lor (t mod 2 ^ 64) carry :: shl_limbs k' (tl x) s (Z.shiftr t 64 mod 2 ^ 64)
  end.

Definition shl_into (n : nat) (x : list Z) (sh : Z) : list Z :=
  let j := Nat.min (Z.to_nat (sh / 64)) n in
  repeat 0 j ++ shl_limbs (n - j) x (sh mod 64) 0.

(** [fn shr_into(out: &mut [u64], x: &[u64], sh: u64)] for
    [n = out.len()], where [x.get(j..).unwrap_or(&[])] is [skipn j x]. *)
Definition shr_into (n : nat) (x : list Z) (sh : Z) : list Z :=
  let x' := skipn (Z.to_nat (sh / 64)) x in
  map (fun i =>
         Z.shiftr (Z.lor (Z.shiftl (limb x' (S i)) 64 mod 2 ^ 128) (limb x' i)) (sh mod 64)
         mod 2 ^ 64)
    (seq 0 n).

(** [fn div_rem_limb(q: &mut [u64], x: &[u64], d: u64) -> u64] for
    [q.len() == x.len()], from the top limb down: the tail first. *)
Fixpoint div_rem_limb_from (x : list Z) (d : Z) : option (list Z * Z) :=
  match x with
  | nil => Some (nil, 0)
  | a :: x' =>
      let* (qs, r) := div_rem_limb_from x' d in
      let t := Z.lor (Z.shiftl r 64 mod 2 ^ 128) a in
      let* q := div_u t d in
      let* r' := rem_u t d in
      Some (q mod 2 ^ 64 :: qs, r')
  end.

Definition div_rem_limb (x : list Z) (d : Z) : option (list Z * Z) :=
  let* (q, r) := div_rem_limb_from x d in Some (q, r mod 2 ^ 64).

(** The loop of D3 in [knuth_step], with fuel: [KnuthStep.v] proves that the
    condition is tested at most 3 times, so [None], out of fuel, does not
    happen. [rhat < B &&] short-circuits: the product is computed only
    for [rhat < 2^64]. *)
Fixpoint knuth_qhat (fuel : nat) (qhat rhat v1 v2 w2 : Z) : option Z :=
  match fuel with
  | O => None
  | S f =>
      if rhat <? 2 ^ 64 then
        let* p := checked_u 128 (qhat * v2) in
        if Z.lor (Z.shiftl rhat 64 mod 2 ^ 128) w2 <? p then
          let* q' := checked_u 128 (qhat - 1) in
          let* r' := checked_u 128 (rhat + v1) in
          knuth_qhat f q' r' v1 v2 w2
        else Some qhat
      else Some qhat
  end.

(** The loop of D4 in [knuth_step]: [w[..n] -= qhat * v]. *)
Fixpoint knuth_submul (w v : list Z) (qhat mc : Z) (borrow : bool)
  : option (list Z * Z * bool) :=
  match w, v with
  | x :: w', y :: v' =>
      let* p := checked_u 128 (qhat * y + mc) in
      let (t, b1) := ovf_sub x (p mod 2 ^ 64) in
      let (t, b2) := ovf_sub t (Z.b2z borrow) in
      let* (r, mc', b') := knuth_submul w' v' qhat (Z.shiftr p 64) (b1 || b2) in
      Some (t :: r, mc', b')
  | _, _ => Some (w, mc, borrow)
  end.

(** [fn knuth_step(w: &mut [u64], v: &[u64]) -> u64] *)
Definition knuth_step (w v : list Z) : option (Z * list Z) :=
  let n := length v in
  let v1 := limb v (n - 1) in
  let v2 := limb v (n - 2) in
  let top := Z.lor (Z.shiftl (limb w n) 64 mod 2 ^ 128) (limb w (n - 1)) in
  let* t := div_u top v1 in
  let qhat := Z.min t (2 ^ 64 - 1) in
  let* qv1 := checked_u 128 (qhat * v1) in
  let* rhat := checked_u 128 (top - qv1) in
  let* qhat := knuth_qhat 3 qhat rhat v1 v2 (limb w (n - 2)) in
  let* (lo, mc, borrow) := knuth_submul (firstn n w) v qhat 0 false in
  let (t, b1) := ovf_sub (limb w n) (mc mod 2 ^ 64) in
  let (t, b2) := ovf_sub t (Z.b2z borrow) in
  if b1 || b2 then
    let* qhat := checked_u 128 (qhat - 1) in
    let (lo', c) := add_assign lo v in
    Some (qhat mod 2 ^ 64, lo' ++ (t + Z.b2z c) mod 2 ^ 64 :: nil)
  else Some (qhat mod 2 ^ 64, lo ++ t :: nil).

(** D2 and D7 of [div_rem_knuth]: step [j] works on [u[j..=j + n]], and
    [q[j]] is consed, so that the list is the least significant first. *)
Fixpoint knuth_loop (k : nat) (u v acc : list Z) : option (list Z * list Z) :=
  match k with
  | O => Some (acc, u)
  | S j =>
      let* (qj, w') := knuth_step (firstn (S (length v)) (skipn j u)) v in
      knuth_loop j (update u j w') v (qj :: acc)
  end.

(** [fn div_rem_knuth(q, r, x: &[u64], d: &[u64], scratch)], returning
    [q] and [r] *)
Definition div_rem_knuth (x d : list Z) : option (list Z * list Z) :=
  let n := length d in
  let s := leading_zeros 64 (limb d (n - 1)) in
  let v := firstn n (shl_into (S n) d s) in
  let u := shl_into (S (length x)) x s in
  let* (q, u') := knuth_loop (S (length x - n)) u v nil in
  Some (q, shr_into n (firstn n u') s).

(** [d.iter().take_while(|&&l| l == 0).count()] *)
Fixpoint zeros_low (d : list Z) : nat :=
  match d with nil => O | a :: d' => if a =? 0 then S (zeros_low d') else O end.

(** [fn div_rem(q, r, x: &[u64], d: &[u64], scratch)], returning [q] and
    [r], for the [q.len() == x.len()] and [r.len() == d.len()] that every
    caller passes. [expect] is [None]. *)
Definition div_rem (x d : list Z) : option (list Z * list Z) :=
  let* n0 := rposition_nonzero d in
  let n := S n0 in
  match cmp x d with
  | Lt => Some (repeat 0 (length x), map (limb x) (seq 0 (length d)))
  | _ =>
      let j := zeros_low d in
      let s0 := firstn j x in
      let s1 := skipn j x in
      let d1 := firstn (n - j) (skipn j d) in
      match d1 with
      | c :: nil =>
          let* (q1, r1) := div_rem_limb s1 c in
          Some (q1 ++ repeat 0 (length x - length s1),
                s0 ++ r1 :: repeat 0 (length d - j - 1))
      | _ =>
          let* (q1, r1) := div_rem_knuth s1 d1 in
          Some (q1 ++ repeat 0 (length x - (length s1 - length d1 + 1)),
                s0 ++ r1 ++ repeat 0 (length d - n))
      end
  end.

End Limbs.

(** ** Nat

    The operations of [Nat] in [src/nat.rs] that [scale] and the
    functions of [src/format/digits.rs] below call. A [Nat] is its limbs,
    with no zero limb at the top. *)
Module NatLimbs.

(** [fn from_limbs(v: Vec<u64>) -> Nat]: the zero limbs at the top go. *)
Fixpoint from_limbs (v : list Z) : list Z :=
  match v with
  | nil => nil
  | a :: v' =>
      match from_limbs v' with
      | nil => if a =? 0 then nil else a :: nil
      | t => a :: t
      end
  end.

(** [Nat::from_u64(x)] *)
Definition from_u64 (x : Z) : list Z := from_limbs (x :: nil).

(** [n.is_zero()] *)
Definition is_zero (n : list Z) : bool := match n with nil => true | _ => false end.

(** [n.bits()] *)
Definition bits (n : list Z) : Z := Limbs.bit_len n.

(** [n.low_u128()]: [limb(0) | limb(1) << 64] *)
Definition low_u128 (n : list Z) : Z :=
  Z.lor (Limbs.limb n 0) (Z.shiftl (Limbs.limb n 1) 64 mod 2 ^ 128).

(** [fn mul_add_u64(&mut self, m: u64, a: u64)] *)
Definition mul_add_u64 (n : list Z) (m a : Z) : option (list Z) :=
  let* (n', c) := Limbs.mul_add_limb n m a in
  Some (if c =? 0 then n' else n' ++ c :: nil).

Fixpoint pow5_loop (k : nat) (p : list Z) : option (list Z) :=
  match k with
  | O => Some p
  | S k' => let* p' := mul_add_u64 p (5 ^ 27) 0 in pow5_loop k' p'
  end.

(** [Nat::pow5(k)], where [Vec::with_capacity] only reserves memory. *)
Definition pow5 (k : Z) : option (list Z) :=
  pow5_loop (Z.to_nat (k / 27)) (5 ^ (k mod 27) :: nil).

(** [n.div_rem(&d)] *)
Definition div_rem (a d : list Z) : option (list Z * list Z) :=
  if is_zero d then None else
  let* (q, r) := Limbs.div_rem a d in
  Some (from_limbs q, from_limbs r).

(** [&x + &y] *)
Definition add (x y : list Z) : list Z :=
  let '(a, b) := if (length y <=? length x)%nat then (x, y) else (y, x) in
  from_limbs (fst (Limbs.add_assign (a ++ 0 :: nil) b)).

(** [&x * &y] *)
Definition mul (x y : list Z) : option (list Z) :=
  let* out := Limbs.mul_into (length x + length y) x y in Some (from_limbs out).

(** [&x << k], where [usize::try_from(k / 64).unwrap()] holds on the
    64-bit targets that [gmp] needs. *)
Definition shl (x : list Z) (k : Z) : list Z :=
  if is_zero x then nil
  else from_limbs (Limbs.shl_into (Z.to_nat (k / 64) + length x + 1) x k).

(** [fn pow10(k: u64) -> Nat], where [u32::try_from(k).unwrap()] is
    checked. *)
Definition pow10 (k : Z) : option (list Z) :=
  let* k32 := checked_u 32 k in
  let* p := pow5 k32 in
  Some (shl p k).

(** [while *self >= pow10(d + 1) { d += 1 }], with fuel. *)
Fixpoint digits10_loop (fuel : nat) (n : list Z) (d : Z) : option Z :=
  match fuel with
  | O => None
  | S f =>
      let* d1 := checked_u 64 (d + 1) in
      let* p := pow10 d1 in
      match Limbs.cmp n p with
      | Lt => Some d
      | _ => digits10_loop f n d1
      end
  end.

(** [n.digits10()]. The fuel, one more than the number of bits, is more
    than the number of steps, as [NatOps.v] proves. *)
Definition digits10 (n : list Z) : option Z :=
  let b := bits n in
  if b =? 0 then Some 0 else
  let* b1 := checked_u 64 (b - 1) in
  let* t := checked_u 128 (b1 * 1233) in
  let* d0 := checked_u 64 (t / 4096) in
  let* d := digits10_loop (S (Z.to_nat b)) n d0 in
  checked_u 64 (d + 1).

(** The limbs of a [Nat] that holds [z >= 0]: the only list of limbs with
    no zero limb at the top that holds it ([NatOps.v]). *)
Fixpoint to_limbs_fuel (f : nat) (z : Z) : list Z :=
  match f with
  | O => nil
  | S f' => if z =? 0 then nil else z mod 2 ^ 64 :: to_limbs_fuel f' (z / 2 ^ 64)
  end.

Definition to_limbs (z : Z) : list Z := to_limbs_fuel (Z.to_nat (Z.log2 z + 1)) z.

(** The operations above on the [Z]s that [Nat]s hold. *)
Definition mul_z (a b : Z) : option Z :=
  let* l := mul (to_limbs a) (to_limbs b) in Some (Limbs.val l).
Definition shl_z (a s : Z) : Z := Limbs.val (shl (to_limbs a) s).
Definition div_rem_z (a b : Z) : option (Z * Z) :=
  let* (q, r) := div_rem (to_limbs a) (to_limbs b) in Some (Limbs.val q, Limbs.val r).
Definition bits_z (a : Z) : Z := bits (to_limbs a).
Definition is_zero_z (a : Z) : bool := is_zero (to_limbs a).
Definition low_u128_z (a : Z) : Z := low_u128 (to_limbs a).
Definition pow5_z (k : Z) : option Z := let* l := pow5 k in Some (Limbs.val l).
Definition add_z (a b : Z) : Z := Limbs.val (add (to_limbs a) (to_limbs b)).
Definition from_u64_z (x : Z) : Z := Limbs.val (from_u64 x).
Definition digits10_z (a : Z) : option Z := digits10 (to_limbs a).

End NatLimbs.

(** ** The dyadic kernel

    The functions of [src/dyadic.rs], for [N] the [nat] [n]. [with_buf]
    is not modelled, nor is the [scratch] of [Limbs.div_rem]: each
    function, here and in [src/limbs.rs], writes every limb of the scratch
    that it reads before it reads it, so the contents of the scratch do
    not matter. *)
Module Dyadic.

(** [struct Dyadic<N> { neg: bool, exp: i64, m: [u64; N] }] and
    [struct Encl<N> { lo, hi }] *)
Record dyadic : Type := { dy_neg : bool; dy_exp : Z; dy_m : list Z }.
Record encl : Type := { en_lo : dyadic; en_hi : dyadic }.

(** The value [(-1)^neg * m * 2^exp] that the comment of [Dyadic] gives. *)
Definition dy_R (x : dyadic) : R :=
  let v := Rmult (IZR (Limbs.val (dy_m x))) (bpow radix2 (dy_exp x)) in
  if dy_neg x then Ropp v else v.

(** [Dyadic::ZERO] *)
Definition dy_zero (n : nat) : dyadic := {| dy_neg := false; dy_exp := 0; dy_m := repeat 0 n |}.

(** [fn low_bits_nonzero(x: &[u64], k: u64) -> bool] *)
Definition low_bits_nonzero (x : list Z) (k : Z) : bool :=
  existsb (fun l => negb (l =? 0)) (firstn (Z.to_nat (k / 64)) x)
  || negb (Z.land (Limbs.limb x (Z.to_nat (k / 64))) (Z.shiftl 1 (k mod 64) - 1) =? 0).

(** [fn round<N>(neg: bool, x: &[u64], e: i64, sticky: bool, up: bool)],
    where [sh] is computed without a check, as it cannot overflow. *)
Definition round (n : nat) (neg : bool) (x : list Z) (e : Z) (sticky up : bool)
  : option dyadic :=
  let l := Limbs.bit_len x in
  if l =? 0 then Some (dy_zero n) else
  let sh := l - 64 * Z.of_nat n in
  let m := if 0 <=? sh then Limbs.shr_into n x sh else Limbs.shl_into n x (- sh) in
  let* exp := checked_i 64 (e + sh) in
  let dropped := sticky || ((0 <? sh) && low_bits_nonzero x sh) in
  if dropped && negb (Bool.eqb up neg) then
    let (m', c) := Limbs.add_assign m (1 :: nil) in
    if c then
      let* exp' := checked_i 64 (exp + 1) in
      Some {| dy_neg := neg; dy_exp := exp'; dy_m := Limbs.update m' (n - 1) (2 ^ 63 :: nil) |}
    else Some {| dy_neg := neg; dy_exp := exp; dy_m := m' |}
  else Some {| dy_neg := neg; dy_exp := exp; dy_m := m |}.

(** [Dyadic::from_f64(x)], where [assert!(x.is_finite())] is [None]. *)
Definition from_f64 (n : nat) (x : f64) : option dyadic :=
  if negb (is_finite x) then None else
  let bits := to_bits x in
  let neg := negb (Z.shiftr bits 63 =? 0) in
  let be := Z.land (Z.shiftr bits 52) 0x7ff in
  let f := Z.land bits (Z.shiftl 1 52 - 1) in
  let '(m, e) := if be =? 0 then (f, -1074) else (Z.lor f (Z.shiftl 1 52), be - 1075) in
  round n neg (m :: nil) e false false.

(** [x.is_zero()], [x.neg()] and [x.shl(k)] *)
Definition is_zero (n : nat) (x : dyadic) : bool := Limbs.limb (dy_m x) (n - 1) =? 0.

Definition neg (n : nat) (x : dyadic) : dyadic :=
  if is_zero n x then x
  else {| dy_neg := negb (dy_neg x); dy_exp := dy_exp x; dy_m := dy_m x |}.

Definition shl (n : nat) (x : dyadic) (k : Z) : option dyadic :=
  if is_zero n x then Some x else
  let* e := checked_i 64 (dy_exp x + k) in
  Some {| dy_neg := dy_neg x; dy_exp := e; dy_m := dy_m x |}.

(** [x.cmp_abs(&y)] *)
Definition cmp_abs (n : nat) (x y : dyadic) : comparison :=
  match is_zero n x, is_zero n y with
  | true, true => Eq
  | true, false => Lt
  | false, true => Gt
  | false, false =>
      match Z.compare (dy_exp x) (dy_exp y) with
      | Eq => Limbs.cmp (dy_m x) (dy_m y)
      | o => o
      end
  end.

(** [a.add(&b, up)] and [a.sub(&b, up)] *)
Definition add (n : nat) (a b : dyadic) (up : bool) : option dyadic :=
  if is_zero n b then Some a else
  if is_zero n a then Some b else
  let '(x, y) := match cmp_abs n a b with Lt => (b, a) | _ => (a, b) end in
  (* [x.exp.wrapping_sub(y.exp) as u64] *)
  let d := (dy_exp x - dy_exp y) mod 2 ^ 64 in
  let* e := checked_i 64 (dy_exp x - 64) in
  let w := 0 :: dy_m x ++ 0 :: nil in
  let '(wy, sticky) :=
    if d <=? 64 then (Limbs.shl_into (S n) (dy_m y) (64 - d), false)
    else (Limbs.shr_into (S n) (dy_m y) (d - 64), low_bits_nonzero (dy_m y) (d - 64)) in
  let w' :=
    if Bool.eqb (dy_neg x) (dy_neg y) then fst (Limbs.add_assign w wy)
    else fst (Limbs.sub_assign w wy sticky) in
  round n (dy_neg x) w' e sticky up.

Definition sub (n : nat) (a b : dyadic) (up : bool) : option dyadic := add n a (neg n b) up.

(** [a.mul(&b, up)] *)
Definition mul (n : nat) (a b : dyadic) (up : bool) : option dyadic :=
  if is_zero n a || is_zero n b then Some (dy_zero n) else
  let* e := checked_i 64 (dy_exp a + dy_exp b) in
  let* w := Limbs.mul_into (2 * n) (dy_m a) (dy_m b) in
  round n (negb (Bool.eqb (dy_neg a) (dy_neg b))) w e false up.

(** [a.mul_u64(k, up)] *)
Definition mul_u64 (n : nat) (a : dyadic) (k : Z) (up : bool) : option dyadic :=
  if is_zero n a || (k =? 0) then Some (dy_zero n) else
  let* (m', c) := Limbs.mul_add_limb (dy_m a) k 0 in
  round n (dy_neg a) (m' ++ c :: nil) (dy_exp a) false up.

(** [a.div_u64(k, up)] *)
Definition div_u64 (n : nat) (a : dyadic) (k : Z) (up : bool) : option dyadic :=
  if k =? 0 then None else
  if is_zero n a then Some (dy_zero n) else
  let* e := checked_i 64 (dy_exp a - 64) in
  let* (q, r) := Limbs.div_rem_limb (0 :: dy_m a) k in
  round n (dy_neg a) q e (negb (r =? 0)) up.

(** [a.div(&b, up)] *)
Definition div (n : nat) (a b : dyadic) (up : bool) : option dyadic :=
  if is_zero n b then None else
  if is_zero n a then Some (dy_zero n) else
  let* e1 := checked_i 64 (dy_exp a - dy_exp b) in
  let* e := checked_i 64 (e1 - 64 * Z.of_nat n) in
  let* (q, r) := Limbs.div_rem (repeat 0 n ++ dy_m a) (dy_m b) in
  round n (negb (Bool.eqb (dy_neg a) (dy_neg b))) q e (existsb (fun l => negb (l =? 0)) r) up.

(** The [loop] of [fn isqrt(s, x, scratch)], with fuel ([DyIsqrt.v] proves
    that the fuel of [isqrt] is enough). [s] and [y] have [n + 1] limbs. *)
Fixpoint isqrt_loop (fuel : nat) (n : nat) (x s : list Z) (first : bool) : option (list Z) :=
  match fuel with
  | O => None
  | S f =>
      let* (q, _) := Limbs.div_rem x s in
      let q' := fst (Limbs.add_assign q s) in
      let y := Limbs.shr_into (S n) q' 1 in
      if negb first && negb (match Limbs.cmp y s with Lt => true | _ => false end) then Some s
      else isqrt_loop f n x y false
  end.

(** [fn isqrt(s, x, scratch)], returning [s], where [l - 63] is checked
    and [t[0] as f64] is [of_u64]. *)
Definition isqrt (n : nat) (x : list Z) : option (list Z) :=
  let* l63 := checked_u 64 (Limbs.bit_len x - 63) in
  let k := l63 / 2 in
  let t := Limbs.shr_into 1 x (2 * k) in
  let c :=
    Z.shiftr
      (Z.lor (Z.land (to_bits (fsqrt (of_u64 (Limbs.limb t 0)))) (Z.shiftl 1 52 - 1))
         (Z.shiftl 1 52))
      21 in
  isqrt_loop (Z.to_nat (Limbs.val x) + 2) n x (Limbs.shl_into (S n) (c :: nil) k) true.

(** [a.sqrt(up)], where [exp.rem_euclid(2)] and [exp.div_euclid(2)] are
    [exp mod 2] and [exp / 2], and the [i64] subtraction, which cannot
    overflow, is checked. *)
Definition sqrt (n : nat) (a : dyadic) (up : bool) : option dyadic :=
  if is_zero n a then Some (dy_zero n) else
  if dy_neg a then None else
  let* e := checked_i 64 (dy_exp a / 2 - 32 * Z.of_nat n) in
  let x := Limbs.shl_into (2 * n + 1) (dy_m a) (64 * Z.of_nat n + dy_exp a mod 2) in
  let* s := isqrt n x in
  let* sq := Limbs.mul_into (2 * n + 2) s s in
  round n false s e (match Limbs.cmp sq x with Eq => false | _ => true end) up.

(** [x.round_up(neg)], where [(b - 128) as i32] keeps the low 32 bits. *)
Definition round_up (n : nat) (x : dyadic) (neg : bool) : option f64 :=
  let* b := checked_i 128 (dy_exp x + 64 * Z.of_nat n) in
  if 1025 <=? b then Some (if neg then min_f64 else infinity) else
  if b <=? -1074 then Some (if neg then B754_zero true else from_bits 1) else
  let lo := if (2 <=? n)%nat then Limbs.limb (dy_m x) (n - 2) else 0 in
  let q := Z.lor (Z.shiftl (Limbs.limb (dy_m x) (n - 1)) 64 mod 2 ^ 128) lo in
  let sticky := existsb (fun l => negb (l =? 0)) (firstn (n - 2) (dy_m x)) in
  let* b128 := checked_i 128 (b - 128) in
  Generic.round_up_exact neg q ((b128 + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) sticky.

(** [x.to_f64(up)] *)
Definition to_f64 (n : nat) (x : dyadic) (up : bool) : option f64 :=
  if is_zero n x then Some zero
  else if up then round_up n x (dy_neg x)
  else let* r := round_up n x (negb (dy_neg x)) in Some (opp r).

(** [x.cmp(&y)] of [impl Ord for Dyadic<N>] *)
Definition sign (n : nat) (x : dyadic) : Z :=
  if is_zero n x then 0 else if dy_neg x then -1 else 1.

Definition cmp (n : nat) (x y : dyadic) : comparison :=
  match Z.compare (sign n x) (sign n y) with
  | Eq => if dy_neg x then cmp_abs n y x else cmp_abs n x y
  | o => o
  end.

(** [x.min(y)] and [x.max(y)] of [Ord]: [min] keeps [x] unless [x > y],
    and [max] takes [y] unless [x > y]. *)
Definition dmin (n : nat) (x y : dyadic) : dyadic := match cmp n x y with Gt => y | _ => x end.
Definition dmax (n : nat) (x y : dyadic) : dyadic := match cmp n x y with Gt => x | _ => y end.

(** The functions of [impl Encl<N>]: [Encl::point(x)], [a.neg()], ... *)
Definition encl_point (n : nat) (x : f64) : option encl :=
  let* d := from_f64 n x in Some {| en_lo := d; en_hi := d |}.

Definition encl_neg (n : nat) (a : encl) : encl :=
  {| en_lo := neg n (en_hi a); en_hi := neg n (en_lo a) |}.

Definition encl_add (n : nat) (a b : encl) : option encl :=
  let* lo := add n (en_lo a) (en_lo b) false in
  let* hi := add n (en_hi a) (en_hi b) true in
  Some {| en_lo := lo; en_hi := hi |}.

Definition encl_sub (n : nat) (a b : encl) : option encl :=
  let* lo := sub n (en_lo a) (en_hi b) false in
  let* hi := sub n (en_hi a) (en_lo b) true in
  Some {| en_lo := lo; en_hi := hi |}.

(** [a.mul(&b)]: two products if neither lower bound is negative, and
    otherwise [x.min(y)] chains in the order of the Rust code. *)
Definition encl_mul (n : nat) (a b : encl) : option encl :=
  let '(x, y, c, d) := (en_lo a, en_hi a, en_lo b, en_hi b) in
  if negb (dy_neg x) && negb (dy_neg c) then
    let* lo := mul n x c false in
    let* hi := mul n y d true in
    Some {| en_lo := lo; en_hi := hi |}
  else
  let* xc := mul n x c false in let* xd := mul n x d false in
  let* yc := mul n y c false in let* yd := mul n y d false in
  let* xc' := mul n x c true in let* xd' := mul n x d true in
  let* yc' := mul n y c true in let* yd' := mul n y d true in
  Some {| en_lo := dmin n (dmin n (dmin n xc xd) yc) yd;
          en_hi := dmax n (dmax n (dmax n xc' xd') yc') yd' |}.

(** [a.div(&b)], where the [assert!] is [None]: two quotients if the lower
    bound of the divisor is not negative, and otherwise [x.min(y)] chains
    in the order of the Rust code. *)
Definition encl_div (n : nat) (a b : encl) : option encl :=
  let '(x, y, c, d) := (en_lo a, en_hi a, en_lo b, en_hi b) in
  if negb ((match cmp n c (dy_zero n) with Gt => true | _ => false end)
           || (match cmp n d (dy_zero n) with Lt => true | _ => false end)) then None else
  if negb (dy_neg c) then
    let* lo := div n x (if dy_neg x then c else d) false in
    let* hi := div n y (if dy_neg y then d else c) true in
    Some {| en_lo := lo; en_hi := hi |}
  else
  let* xc := div n x c false in let* xd := div n x d false in
  let* yc := div n y c false in let* yd := div n y d false in
  let* xc' := div n x c true in let* xd' := div n x d true in
  let* yc' := div n y c true in let* yd' := div n y d true in
  Some {| en_lo := dmin n (dmin n (dmin n xc xd) yc) yd;
          en_hi := dmax n (dmax n (dmax n xc' xd') yc') yd' |}.

Definition encl_sqrt (n : nat) (a : encl) : option encl :=
  let* lo := sqrt n (dmax n (en_lo a) (dy_zero n)) false in
  let* hi := sqrt n (en_hi a) true in
  Some {| en_lo := lo; en_hi := hi |}.

Definition encl_mul_u64 (n : nat) (a : encl) (k : Z) : option encl :=
  let* lo := mul_u64 n (en_lo a) k false in
  let* hi := mul_u64 n (en_hi a) k true in
  Some {| en_lo := lo; en_hi := hi |}.

Definition encl_div_u64 (n : nat) (a : encl) (k : Z) : option encl :=
  let* lo := div_u64 n (en_lo a) k false in
  let* hi := div_u64 n (en_hi a) k true in
  Some {| en_lo := lo; en_hi := hi |}.

Definition encl_shl (n : nat) (a : encl) (k : Z) : option encl :=
  let* lo := shl n (en_lo a) k in
  let* hi := shl n (en_hi a) k in
  Some {| en_lo := lo; en_hi := hi |}.

(** [fn ziv_at<N, E>(f: &E, up: bool) -> Option<f64>], for [ev n] the
    [f.eval::<N>()] of [N = n], [None] where it panics. *)
Definition ziv_at (ev : nat -> option encl) (n : nat) (up : bool) : option (option f64) :=
  let* x := ev n in
  let* lo := to_f64 n (en_lo x) up in
  let* hi := to_f64 n (en_hi x) up in
  Some (if eq lo hi then Some lo else None).

(** [fn ziv<E>(f: &E, up: bool, start: usize) -> f64]: the [panic!] at
    the cap, after the last level, is [None]. *)
Fixpoint ziv_levels (ev : nat -> option encl) (up : bool) (start : nat) (levels : list nat)
  : option f64 :=
  match levels with
  | nil => None
  | n :: ls =>
      if (start <=? n)%nat then
        let* r := ziv_at ev n up in
        match r with Some x => Some x | None => ziv_levels ev up start ls end
      else ziv_levels ev up start ls
  end.

Definition ziv (ev : nat -> option encl) (up : bool) (start : nat) : option f64 :=
  ziv_levels ev up start (1 :: 2 :: 4 :: 8 :: 16 :: 32 :: 64 :: nil)%nat.

End Dyadic.

(** ** ln 2, ln 10 and π for the dyadic kernel

    The tables and [split] of [src/dyadic/consts.rs]. [DyConst.v] proves
    the bounds that the comments of [ln2] and [ln10] state, and
    [DyConstPi.v] that of [pi]. *)
Module DyadicConsts.

Import ListNotations.

(** [const LN2: [u64; 66]], floor(ln 2 * 2^4224), the least significant
    limb first. *)
Definition LN2 : list Z := [
  0xc0b1b31d8a0e23fa; 0x85db6ab03a49bd0d; 0x175eb4afc8daadd8; 0xf07afff3a892374e;
  0x8f6826250dea891e; 0xcecb72f19c38339d; 0x5f6f7cebac9f45ae; 0x6c472096e76115c0;
  0x972cd18bfbbd9d42; 0x0ab111bbbd67c724; 0x473826fda0c238b9; 0x61c1696dd24aaebd;
  0x156e0c292413d5e3; 0x95184460dc4e7487; 0xd7622658901e646a; 0xef2f0ce2d7373958;
  0x2ac5b61cc4e9207c; 0x57339ba2beba7d05; 0x0060e49908391a0c; 0x621363196af50302;
  0x05c128d53d0bd2f9; 0x36e02b20cee886b9; 0x0bbb16faf3d949f2; 0x422183edc9942109;
  0x5e9222b88c66d3c5; 0x61affd446b1ca3cf; 0x268a5c1f9538b982; 0x8d6f5177fbcf0755;
  0xa17293d1228a4ef9; 0x44a02554731cdc8e; 0x96d4e6d330af889b; 0x5570b6c68f969834;
  0x7598a1951ae273ee; 0x4d162db3b365853d; 0x5f50b5185064c18b; 0x078f735d1b2db31b;
  0xae313cdb6c606cb1; 0x955d5179b1e17b9d; 0x0c480a5417350d2c; 0x074db6015cfe7aa3;
  0x6a9c7f8a5e148e82; 0x25669b333564a337; 0x4c1a1e0bd1d6095d; 0xcccc4e659393514c;
  0xc943e732b479cd33; 0x17460775db8990e5; 0x7d2e23de1400b396; 0xee569d6dfc1efa15;
  0x610d30f88fe551a2; 0x07f4ca11fb5bfb90; 0xda2d97c50f3fd5c6; 0x655fa1872f20e3a2;
  0xf5dfa6bd38303248; 0x72ce87b19d6548ca; 0x256fa0ec7657f74b; 0xb9ea9bc3b136603b;
  0x1acbda11317c387e; 0x3e96ca16224ae8c5; 0x27573b291169b825; 0xed2eae35c1382144;
  0x559552fb4afa1b10; 0xe7b876206debac98; 0x8a0d175b8baafa2b; 0x40f343267298b62d;
  0xc9e3b39803f2f6af; 0xb17217f7d1cf79ab].

(** [const LN10: [u64; 66]], floor(ln 10 * 2^4222), the least significant
    limb first. *)
Definition LN10 : list Z := [
  0xfa9d8c598c574502; 0xfb5f06c358ac8f70; 0x8e668aeaba83c7f8; 0xb81c4a5b53d49ea6;
  0x48a93f5f5e3b6eb4; 0xa2d6fe91388e9e3e; 0x4b40ed7a56c6cdcd; 0xc4b83301006bf062;
  0x1be5a9a967fddc57; 0xff3065c40cfceec8; 0x89bf752fb5dfb353; 0x6a36ceccb2d5ae5b;
  0xbc1261c8b3e4daad; 0xdf3ccbb3189da49d; 0xd006f8b4be145a2a; 0x99d6d20ea2defd2b;
  0xb6524dc18c167e86; 0xed69b13dc1a03730; 0xf42c58def8a3c52d; 0xf6ff363db00b6b33;
  0xa0d9c260794a976f; 0x421ef5e0b00410a0; 0xdef85a05eb56323a; 0x8fcd08324a7b32a6;
  0x0a62d18e478f7bd5; 0x4d5e843f20642b97; 0x1f1d366c20663834; 0xbc64ea806e198566;
  0xaa6604a5324ec3dc; 0xb5e4b1c8c0e5a10a; 0x3b70fcda2d732d47; 0x0942617819127a6e;
  0x3982a78ca45ddfc8; 0xef99c8e5f6974f36; 0x4cb0466d61ba648e; 0xad6bfbffd821ba0a;
  0xe38a5700ffde2db1; 0xf77e37604e943960; 0xa949eaaadf69e8a5; 0xe88047f17b0d9b50;
  0x3848c8d25faf1bca; 0x3dfd3c51748e6d6e; 0xaf88486ea9b7401e; 0xf47fa96deb271060;
  0x45765cde268339db; 0xe40bf3cc1e14126a; 0xdb1d28ea57d4fdc0; 0xa47ecb26978c5d4f;
  0x9cd5b42e6a271619; 0xe2478fcaad3aee98; 0x469ea58e9305e981; 0x5b08b057d5ede20f;
  0x8e93368d44789c4f; 0xca67b35b23605085; 0x5161bb49d219c7bb; 0xef66ceb04ab3c6fa;
  0x765aa6c3b0d831fb; 0x782cf8a28a8c911e; 0xfb8f788402e516d6; 0x2c622418410be2da;
  0xcc70cbc02c5f0d68; 0x962f02d7b1a8105c; 0x83c61e8201f02d72; 0xe28fecf9da5df90e;
  0xea56d62b82d30a28; 0x935d8dddaaa8ac16].

(** [fn split<N>(t: &[u64; 66], e: i64, z: u32) -> (Dyadic<N>, Encl<N>)]:
    [m] is [t[66 - N..]] with [m[0] &= u64::MAX << z], and [w] the limbs
    [t[..67 - N]] with [w[66 - N] &= (1 << z) - 1], followed by the zero
    limb [w[67 - N]] that [limbs::add_assign(&mut w[..68 - N], &[1])]
    carries into. *)
Definition split (n : nat) (t : list Z) (e : Z) (z : Z) : option (Dyadic.dyadic * Dyadic.encl) :=
  let top := skipn (66 - n) t in
  let m := Limbs.update top 0 (Z.land (Limbs.limb top 0) (Z.shiftl (2 ^ 64 - 1) z mod 2 ^ 64) :: nil) in
  let h := {| Dyadic.dy_neg := false; Dyadic.dy_exp := e + 64 * Z.of_nat (66 - n); Dyadic.dy_m := m |} in
  let w0 := firstn (67 - n) t in
  let w := Limbs.update w0 (66 - n) (Z.land (Limbs.limb w0 (66 - n)) (Z.shiftl 1 z - 1) :: nil) in
  let* lo := Dyadic.round n false w e false false in
  let w' := fst (Limbs.add_assign (w ++ 0 :: nil) (1 :: nil)) in
  let* hi := Dyadic.round n false w' e false true in
  Some (h, {| Dyadic.en_lo := lo; Dyadic.en_hi := hi |}).

(** [fn ln2<N>()] and [fn ln10<N>()] *)
Definition ln2 (n : nat) : option (Dyadic.dyadic * Dyadic.encl) := split n LN2 (-4224) 12.
Definition ln10 (n : nat) : option (Dyadic.dyadic * Dyadic.encl) := split n LN10 (-4222) 53.

(** [const PI: [u64; 66]], floor(π * 2^4222), the least significant limb
    first. *)
Definition PI : list Z := [
  0xf8ff9406ad9e530e; 0xc9751e763dba37bd; 0xc1d4dcb2602646de; 0x36c3fab4d27c7026;
  0x4df435c934028492; 0x86ffb7dc90a6c08f; 0x93b4ea988d8fddc1; 0xd0069127d5b05aa9;
  0xb81bdd762170481c; 0x1f612970cee2d7af; 0x233ba186515be7ed; 0x99b2964fa090c3a2;
  0x287c59474e6bc05d; 0x2e8efc141fbecaa6; 0xdbbbc2db04de8ef9; 0x2583e9ca2ad44ce8;
  0x1a946834b6150bda; 0x99c327186af4e23c; 0x88719a10bdba5b26; 0x1a723c12a787e6d7;
  0x4b82d120a9210801; 0x43db5bfce0fd108e; 0x08e24fa074e5ab31; 0x770988c0bad946e2;
  0xbbe117577a615d6c; 0x521f2b18177b200c; 0xd87602733ec86a64; 0xf12ffa06d98a0864;
  0xcee3d2261ad2ee6b; 0x1e8c94e04a25619d; 0xabf5ae8cdb0933d7; 0xb3970f85a6e1e4c7;
  0x8aea71575d060c7d; 0xecfb850458dbef0a; 0xa85521abdf1cba64; 0xad33170d04507a33;
  0x15728e5a8aaac42d; 0x15d2261898fa0510; 0x3995497cea956ae5; 0xde2bcbf695581718;
  0xb5c55df06f4c52c9; 0x9b2783a2ec07a28f; 0xe39e772c180e8603; 0x32905e462e36ce3b;
  0xf1746c08ca18217c; 0x670c354e4abc9804; 0x9ed529077096966d; 0x1c62f356208552bb;
  0x83655d23dca3ad96; 0x69163fa8fd24cf5f; 0x98da48361c55d39a; 0xc2007cb8a163bf05;
  0x49286651ece45b3d; 0xae9f24117c4b1fe6; 0xee386bfb5a899fa5; 0x0bff5cb6f406b7ed;
  0xf44c42e9a637ed6b; 0xe485b576625e7ec6; 0x4fe1356d6d51c245; 0x302b0a6df25f1437;
  0xef9519b3cd3a431b; 0x514a08798e3404dd; 0x020bbea63b139b22; 0x29024e088a67cc74;
  0xc4c6628b80dc1cd1; 0xc90fdaa22168c234].

(** [fn pi<N>() -> Encl<N>] *)
Definition pi (n : nat) : option Dyadic.encl :=
  let* (h, l) := split n PI (-4222) 0 in
  Dyadic.encl_add n {| Dyadic.en_lo := h; Dyadic.en_hi := h |} l.

End DyadicConsts.

(** ** The exponential and hyperbolic functions of the dyadic kernel

    The functions of [src/dyadic/exp.rs]: [exp_dir x up] is [exp(x, up)],
    and the same for [exp2], [exp10], [sinh], [cosh] and [tanh], with
    [None] where the Rust function panics: an [assert!] of this file,
    [ziv] at its cap, or any operation of the kernel that panics. The
    [Eval]s are the functions [ev_exp x] and the others of a level [n].
    [DyExpCore.v], [DyExp.v] and [DyHyp.v] prove them, with the rules
    before the loop proved in [DyExpRules.v], [DyHypRules.v],
    [DySinhTiny.v] and [DyTanhTiny.v], and [DyPoint.v] makes a [point] of
    them. *)
Module DyadicExp.

(** The [f64] literals of the file, written with [from_bits]: [1.0],
    [2.0], [-1.0], [-2.0], [f64::NEG_INFINITY], [f64::MAX], [1.0 +
    f64::EPSILON], [1.0 - f64::EPSILON / 2.0], [f64::from_bits(1)], and
    [std::f64::consts::LOG2_E] and [LOG2_10]. *)
Definition one : f64 := from_bits 0x3ff0000000000000.
Definition two : f64 := from_bits 0x4000000000000000.
Definition m_one : f64 := from_bits 0xbff0000000000000.
Definition m_two : f64 := from_bits 0xc000000000000000.
Definition neg_infinity : f64 := from_bits 0xfff0000000000000.
Definition max_f64 : f64 := from_bits 0x7fefffffffffffff.
Definition one_plus_ulp : f64 := from_bits 0x3ff0000000000001.
Definition one_minus_ulp : f64 := from_bits 0x3fefffffffffffff.
Definition min_pos : f64 := from_bits 1.
Definition log2_e : f64 := from_bits 0x3ff71547652b82fe.
Definition log2_10 : f64 := from_bits 0x400a934f0979a371.

(** [TINY_HYP], [TINY_EXP] and [TINY_EXP10]: 2^-26, 2^-54 and 2^-56. *)
Definition tiny_hyp : f64 := from_bits 0x3e50000000000000.
Definition tiny_exp : f64 := from_bits 0x3c90000000000000.
Definition tiny_exp10 : f64 := from_bits 0x3c70000000000000.

(** [POW10[k]], the literal [1e<k>], which is 10^k rounded to nearest. *)
Definition pow10 (k : Z) : f64 := binary_normalize 53 1024 _ _ mode_NE (10 ^ k) 0 false.

(** [c as i64], which saturates, and is 0 for NaN. *)
Definition to_i64 (c : f64) : Z :=
  match c with
  | B754_infinity s => if s then - 2 ^ 63 else 2 ^ 63 - 1
  | _ => Z.max (- 2 ^ 63) (Z.min (2 ^ 63 - 1) (Btrunc c))
  end.

(** [fn params<N>() -> (i64, u64)]: (j, K) *)
Definition params (n : nat) : Z * Z :=
  if Nat.eqb n 1 then (4, 11) else
  if Nat.eqb n 2 then (8, 13) else
  if Nat.eqb n 4 then (12, 18) else
  if Nat.eqb n 8 then (16, 27) else
  if Nat.eqb n 16 then (16, 50) else
  if Nat.eqb n 32 then (16, 95) else (16, 182).

(** The loop of [fn series<N>(s, k)], for [i] from [k] down to 2. *)
Fixpoint series_loop (n : nat) (one_e s : Dyadic.encl) (i : nat) (t : Dyadic.encl)
  : option Dyadic.encl :=
  match i with
  | O | S O => Some t
  | S i' =>
      let* q := Dyadic.encl_mul n s t in
      let* q' := Dyadic.encl_div_u64 n q (Z.of_nat i) in
      let* t' := Dyadic.encl_sub n one_e q' in
      series_loop n one_e s i' t'
  end.

(** [fn series<N>(s: &Encl<N>, k: u64) -> Encl<N>] *)
Definition series (n : nat) (s : Dyadic.encl) (k : Z) : option Dyadic.encl :=
  let* one_e := Dyadic.encl_point n one in
  let* hi := Dyadic.from_f64 n one in
  let* t := series_loop n one_e s (Z.to_nat k) {| Dyadic.en_lo := Dyadic.dy_zero n; Dyadic.en_hi := hi |} in
  Dyadic.encl_mul n s t.

(** The loop [for _ in 0..j { e = e.mul(&e) }] of [exp_neg]. *)
Fixpoint square_loop (n : nat) (j : nat) (e : Dyadic.encl) : option Dyadic.encl :=
  match j with
  | O => Some e
  | S j' => let* e' := Dyadic.encl_mul n e e in square_loop n j' e'
  end.

(** [fn exp_neg<N>(y: &Encl<N>) -> Encl<N>] *)
Definition exp_neg (n : nat) (y : Dyadic.encl) : option Dyadic.encl :=
  let '(j, k) := params n in
  let* one_e := Dyadic.encl_point n one in
  let* s := Dyadic.encl_shl n y (- j) in
  let* u := series n s k in
  let* e := Dyadic.encl_sub n one_e u in
  square_loop n (Z.to_nat j) e.

(** The loop [for _ in 0..j { u = u.mul(&two.sub(&u)) }] of [expm1_neg]. *)
Fixpoint double_loop (n : nat) (two_e : Dyadic.encl) (j : nat) (u : Dyadic.encl)
  : option Dyadic.encl :=
  match j with
  | O => Some u
  | S j' =>
      let* d := Dyadic.encl_sub n two_e u in
      let* u' := Dyadic.encl_mul n u d in
      double_loop n two_e j' u'
  end.

(** [fn expm1_neg<N>(y: &Encl<N>) -> Encl<N>] *)
Definition expm1_neg (n : nat) (y : Dyadic.encl) : option Dyadic.encl :=
  let '(j, k) := params n in
  let* two_e := Dyadic.encl_point n two in
  let* s := Dyadic.encl_shl n y (- j) in
  let* u := series n s k in
  double_loop n two_e (Z.to_nat j) u.

(** [fn to_k(c: f64) -> i64], where the [assert!] is [None]. *)
Definition to_k (c : f64) : option Z :=
  let k := to_i64 c in
  if Z.abs k <=? 2048 then Some k else None.

(** [fn mul_int<N>(a: &Encl<N>, k: i64) -> Encl<N>] *)
Definition mul_int (n : nat) (a : Dyadic.encl) (k : Z) : option Dyadic.encl :=
  let* p := Dyadic.encl_mul_u64 n a (Z.abs k) in
  Some (if k <? 0 then Dyadic.encl_neg n p else p).

(** [fn mul_f64<N>(a: &Encl<N>, x: f64) -> Encl<N>] *)
Definition mul_f64 (n : nat) (a : Dyadic.encl) (x : f64) : option Dyadic.encl :=
  let* px := Dyadic.encl_point n (fabs x) in
  let* p := Dyadic.encl_mul n px a in
  Some (if lt x zero then Dyadic.encl_neg n p else p).

(** [x < y] and [x > y] of [PartialOrd], which compares with [x.cmp(&y)],
    so that [x >= y] is [negb (dy_lt n x y)] and [x <= y] is [negb (dy_gt
    n x y)]. *)
Definition dy_lt (n : nat) (x y : Dyadic.dyadic) : bool :=
  match Dyadic.cmp n x y with Lt => true | _ => false end.
Definition dy_gt (n : nat) (x y : Dyadic.dyadic) : bool :=
  match Dyadic.cmp n x y with Gt => true | _ => false end.

(** [fn scaled<N>(y, k, h, l) -> Encl<N>], where [k + 1], which cannot
    overflow, as [|k| <= 2048], is computed without a check, and the
    [assert!] is [None]. *)
Definition scaled (n : nat) (y : Dyadic.encl) (k : Z) (h : Dyadic.dyadic) (l : Dyadic.encl)
  : option Dyadic.encl :=
  let* (y', k') :=
    if dy_lt n (Dyadic.en_lo y) (Dyadic.dy_zero n) then
      let* y1 := Dyadic.encl_add n y {| Dyadic.en_lo := h; Dyadic.en_hi := h |} in
      let* y2 := Dyadic.encl_add n y1 l in
      Some (y2, k + 1)
    else Some (y, k) in
  let* two_d := Dyadic.from_f64 n two in
  if dy_lt n (Dyadic.en_lo y') (Dyadic.dy_zero n) || dy_gt n (Dyadic.en_hi y') two_d then None else
  let* e := exp_neg n y' in
  Dyadic.encl_shl n e k'.

(** [fn exp_encl<N>(x: f64) -> Encl<N>] *)
Definition exp_encl (n : nat) (x : f64) : option Dyadic.encl :=
  let* k := to_k (fceil (mul x log2_e)) in
  let* (h, l) := DyadicConsts.ln2 n in
  let* a := mul_int n {| Dyadic.en_lo := h; Dyadic.en_hi := h |} k in
  let* px := Dyadic.encl_point n x in
  let* b := Dyadic.encl_sub n a px in
  let* c := mul_int n l k in
  let* y := Dyadic.encl_add n b c in
  scaled n y k h l.

(** The [eval::<N>()] of [Exp(x)], [Exp2(x)], [Exp10(x)], [Cosh(t)],
    [Sinh(x)] and [Tanh(x)]. *)
Definition ev_exp (x : f64) (n : nat) : option Dyadic.encl := exp_encl n x.

Definition ev_exp2 (x : f64) (n : nat) : option Dyadic.encl :=
  let c := fceil x in
  let* m := to_k c in
  let* (h, l) := DyadicConsts.ln2 n in
  let* ln2 := Dyadic.encl_add n {| Dyadic.en_lo := h; Dyadic.en_hi := h |} l in
  let* pc := Dyadic.encl_point n c in
  let* px := Dyadic.encl_point n x in
  let* g := Dyadic.encl_sub n pc px in
  let* y := Dyadic.encl_mul n g ln2 in
  scaled n y m h l.

Definition ev_exp10 (x : f64) (n : nat) : option Dyadic.encl :=
  let* k := to_k (fceil (mul x log2_10)) in
  let* (h2, l2) := DyadicConsts.ln2 n in
  let* (h10, l10) := DyadicConsts.ln10 n in
  let* a := mul_int n {| Dyadic.en_lo := h2; Dyadic.en_hi := h2 |} k in
  let* b := mul_f64 n {| Dyadic.en_lo := h10; Dyadic.en_hi := h10 |} x in
  let* ab := Dyadic.encl_sub n a b in
  let* c := mul_int n l2 k in
  let* d := mul_f64 n l10 x in
  let* cd := Dyadic.encl_sub n c d in
  let* y := Dyadic.encl_add n ab cd in
  scaled n y k h2 l2.

Definition ev_cosh (t : f64) (n : nat) : option Dyadic.encl :=
  let* e := exp_encl n t in
  let* one_e := Dyadic.encl_point n one in
  let* r := Dyadic.encl_div n one_e e in
  let* s := Dyadic.encl_add n e r in
  Dyadic.encl_shl n s (-1).

Definition ev_sinh (x : f64) (n : nat) : option Dyadic.encl :=
  let t := fabs x in
  let* one_e := Dyadic.encl_point n one in
  let* s :=
    if gt t one then
      let* e := exp_encl n t in
      let* r := Dyadic.encl_div n one_e e in
      let* d := Dyadic.encl_sub n e r in
      Dyadic.encl_shl n d (-1)
    else
      let* pt := Dyadic.encl_point n t in
      let* u := expm1_neg n pt in
      let* two_e := Dyadic.encl_point n two in
      let* a := Dyadic.encl_sub n two_e u in
      let* num := Dyadic.encl_mul n u a in
      let* b := Dyadic.encl_sub n one_e u in
      let* den := Dyadic.encl_shl n b 1 in
      Dyadic.encl_div n num den in
  Some (if lt x zero then Dyadic.encl_neg n s else s).

Definition ev_tanh (x : f64) (n : nat) : option Dyadic.encl :=
  let t := fabs x in
  let* u :=
    if gt t one then
      let* one_e := Dyadic.encl_point n one in
      let* e := exp_encl n (mul m_two t) in
      Dyadic.encl_sub n one_e e
    else
      let* p := Dyadic.encl_point n (mul two t) in
      expm1_neg n p in
  let* two_e := Dyadic.encl_point n two in
  let* d := Dyadic.encl_sub n two_e u in
  let* r := Dyadic.encl_div n u d in
  Some (if lt x zero then Dyadic.encl_neg n r else r).

(** [fn overflow(up: bool) -> f64] and [fn underflow(up: bool) -> f64] *)
Definition overflow (up : bool) : f64 := if up then infinity else max_f64.
Definition underflow (up : bool) : f64 := if up then min_pos else zero.

(** [fn near_one(x: f64, up: bool) -> f64] *)
Definition near_one (x : f64) (up : bool) : f64 :=
  if eq x zero then one
  else if gt x zero then (if up then one_plus_ulp else one)
  else if up then one else one_minus_ulp.

(** [fn away(x: f64, up: bool) -> f64] and [fn toward_zero(x: f64, up:
    bool) -> f64] *)
Definition away (x : f64) (up : bool) : f64 :=
  if eq x zero || negb (Bool.eqb (gt x zero) up) then x else from_bits (to_bits x + 1).
Definition toward_zero (x : f64) (up : bool) : f64 :=
  if eq x zero || Bool.eqb (gt x zero) up then x else from_bits (to_bits x - 1).

(** [pub(crate) fn exp(x: f64, up: bool) -> f64] *)
Definition exp_dir (x : f64) (up : bool) : option f64 :=
  if is_nan x || eq x infinity then Some x
  else if eq x neg_infinity then Some zero
  else if ge x (from_bits 0x4086300000000000) (* 710.0 *) then Some (overflow up)
  else if le x (from_bits 0xc087500000000000) (* -746.0 *) then Some (underflow up)
  else if lt (fabs x) tiny_exp then Some (near_one x up)
  else Dyadic.ziv (ev_exp x) up 1.

(** [pub(crate) fn exp2(x: f64, up: bool) -> f64] *)
Definition exp2_dir (x : f64) (up : bool) : option f64 :=
  if is_nan x || eq x infinity then Some x
  else if eq x neg_infinity then Some zero
  else if ge x (from_bits 0x4090000000000000) (* 1024.0 *) then Some (overflow up)
  else if lt x (from_bits 0xc090cc0000000000) (* -1075.0 *) then Some (underflow up)
  else if lt (fabs x) tiny_exp then Some (near_one x up)
  else Dyadic.ziv (ev_exp2 x) up 1.

(** [pub(crate) fn exp10(x: f64, up: bool) -> f64], where
    [(1.0..=22.0).contains(&x)] is [1.0 <= x && x <= 22.0], and [x as
    usize], for such an integer [x], is [to_i64 x]. *)
Definition exp10_dir (x : f64) (up : bool) : option f64 :=
  if is_nan x || eq x infinity then Some x
  else if eq x neg_infinity then Some zero
  else if ge x (from_bits 0x4073500000000000) (* 309.0 *) then Some (overflow up)
  else if le x (from_bits 0xc074400000000000) (* -324.0 *) then Some (underflow up)
  else if lt (fabs x) tiny_exp10 then Some (near_one x up)
  else if le one x && le x (from_bits 0x4036000000000000) (* 22.0 *) && eq x (ffloor x) then
    Some (pow10 (to_i64 x))
  else Dyadic.ziv (ev_exp10 x) up 1.

(** [pub(crate) fn sinh(x: f64, up: bool) -> f64], where [x.is_infinite()]
    is [x == f64::INFINITY || x == f64::NEG_INFINITY]. *)
Definition sinh_dir (x : f64) (up : bool) : option f64 :=
  if is_nan x || (eq x infinity || eq x neg_infinity) then Some x
  else if ge x (from_bits 0x4086380000000000) (* 711.0 *) then Some (overflow up)
  else if le x (from_bits 0xc086380000000000) (* -711.0 *) then Some (opp (overflow (negb up)))
  else if lt (fabs x) tiny_hyp then Some (away x up)
  else Dyadic.ziv (ev_sinh x) up 1.

(** [pub(crate) fn cosh(x: f64, up: bool) -> f64] *)
Definition cosh_dir (x : f64) (up : bool) : option f64 :=
  let t := fabs x in
  if is_nan t || eq t infinity then Some t
  else if ge t (from_bits 0x4086380000000000) (* 711.0 *) then Some (overflow up)
  else if lt t tiny_hyp then Some (near_one t up)
  else Dyadic.ziv (ev_cosh t) up 1.

(** [pub(crate) fn tanh(x: f64, up: bool) -> f64] *)
Definition tanh_dir (x : f64) (up : bool) : option f64 :=
  if is_nan x then Some x
  else if eq x infinity then Some one
  else if eq x neg_infinity then Some m_one
  else if ge x (from_bits 0x4033000000000000) (* 19.0 *) then
    Some (if up then one else one_minus_ulp)
  else if le x (from_bits 0xc033000000000000) (* -19.0 *) then
    Some (if up then opp one_minus_ulp else m_one)
  else if lt (fabs x) tiny_hyp then Some (toward_zero x up)
  else Dyadic.ziv (ev_tanh x) up 1.

End DyadicExp.

(** ** The logarithms and inverse hyperbolic functions of the dyadic kernel

    The functions of [src/dyadic/log.rs]: [ln_dir x up] is [ln(x, up)],
    and the same for [log2], [log10], [asinh], [acosh] and [atanh], with
    [None] where the Rust function panics: an [assert!] of this file,
    [ziv] at its cap, or any operation of the kernel that panics. The
    [Eval]s are the functions [ev_ln x] and the others of a level [n].
    The constants and functions of [src/dyadic/exp.rs] that they use are
    those of [DyadicExp]. [DyLogCore.v], [DyLog.v] and [DyLogHyp.v] prove
    them, with the rules before the loop proved in [DyLogRules.v] and
    [DyLogTiny.v], and [DyPoint.v] makes a [point] of them. *)
Module DyadicLog.

(** The [f64] literals of the file, written with [from_bits]: [0.5],
    [SERIES_MAX] = 0.171875 and [ACOSH_SERIES_MAX] = 1.015625. *)
Definition half : f64 := from_bits 0x3fe0000000000000.
Definition series_max : f64 := from_bits 0x3fc6000000000000.
Definition acosh_series_max : f64 := from_bits 0x3ff0400000000000.

(** [SQRT_HALF], floor(2^64 / √2). *)
Definition sqrt_half : Z := 0xb504f333f9de6484.

(** [fn terms<N>() -> u64] *)
Definition terms (n : nat) : Z := (64 * Z.of_nat n + 10) / 5.

(** The loop [for k in (0..terms::<N>()).rev() { t =
    one.div_u64(2 * k + 1).add(&z.mul(&t)) }] of [atanh_series], for [k]
    from [i - 1] down to 0. *)
Fixpoint series_loop (n : nat) (one_e z : Dyadic.encl) (i : nat) (t : Dyadic.encl)
  : option Dyadic.encl :=
  match i with
  | O => Some t
  | S k =>
      let* q := Dyadic.encl_div_u64 n one_e (2 * Z.of_nat k + 1) in
      let* p := Dyadic.encl_mul n z t in
      let* t' := Dyadic.encl_add n q p in
      series_loop n one_e z k t'
  end.

(** [fn atanh_series<N>(u: &Encl<N>) -> Encl<N>], where the [assert!] is
    [None]. *)
Definition atanh_series (n : nat) (u : Dyadic.encl) : option Dyadic.encl :=
  let* half_d := Dyadic.from_f64 n half in
  if DyadicExp.dy_lt n (Dyadic.en_lo u) (Dyadic.dy_zero n)
     || DyadicExp.dy_gt n (Dyadic.en_hi u) half_d then None else
  let* z := Dyadic.encl_mul n u u in
  let* one_e := Dyadic.encl_point n DyadicExp.one in
  let* two_d := Dyadic.from_f64 n DyadicExp.two in
  let* t :=
    series_loop n one_e z (Z.to_nat (terms n))
      {| Dyadic.en_lo := Dyadic.dy_zero n; Dyadic.en_hi := two_d |} in
  Dyadic.encl_mul n u t.

(** [fn reduce<N>(d: &Dyadic<N>) -> (i64, Encl<N>, bool)], where the
    [assert!]s are [None], the [i128] sum [b], which cannot overflow, is
    computed without a check, and [e as i64], after the check of [e], is
    [e]. *)
Definition reduce (n : nat) (d : Dyadic.dyadic) : option (Z * Dyadic.encl * bool) :=
  if Dyadic.dy_neg d || Dyadic.is_zero n d then None else
  let b := Dyadic.dy_exp d + 64 * Z.of_nat n in
  let e := if sqrt_half <=? Limbs.limb (Dyadic.dy_m d) (n - 1) then b else b - 1 in
  if 2048 <? Z.abs e then None else
  let* m := Dyadic.shl n d (- e) in
  let me := {| Dyadic.en_lo := m; Dyadic.en_hi := m |} in
  let* one_e := Dyadic.encl_point n DyadicExp.one in
  let less := DyadicExp.dy_lt n m (Dyadic.en_lo one_e) in
  let* num := if less then Dyadic.encl_sub n one_e me else Dyadic.encl_sub n me one_e in
  let* den := Dyadic.encl_add n me one_e in
  let* s := Dyadic.encl_div n num den in
  let* a := atanh_series n s in
  let* a2 := Dyadic.encl_shl n a 1 in
  Some (e, a2, less).

(** [fn ln_dy<N>(d: &Dyadic<N>) -> Encl<N>] *)
Definition ln_dy (n : nat) (d : Dyadic.dyadic) : option Dyadic.encl :=
  let* (e, a, less) := reduce n d in
  let* (h, l) := DyadicConsts.ln2 n in
  let* k1 := DyadicExp.mul_int n {| Dyadic.en_lo := h; Dyadic.en_hi := h |} e in
  let* k2 := DyadicExp.mul_int n l e in
  let* k := Dyadic.encl_add n k1 k2 in
  Dyadic.encl_add n k (if less then Dyadic.encl_neg n a else a).

(** [fn ln_encl<N>(a: &Encl<N>) -> Encl<N>] *)
Definition ln_encl (n : nat) (a : Dyadic.encl) : option Dyadic.encl :=
  let* l := ln_dy n (Dyadic.en_lo a) in
  let* w1 := Dyadic.sub n (Dyadic.en_hi a) (Dyadic.en_lo a) true in
  let* w := Dyadic.div n w1 (Dyadic.en_lo a) true in
  let* hi := Dyadic.add n (Dyadic.en_hi l) w true in
  Some {| Dyadic.en_lo := Dyadic.en_lo l; Dyadic.en_hi := hi |}.

(** The [eval::<N>()] of [Ln(x)], [Log2(x)], [Log10(x)], [Asinh(x)],
    [Acosh(x)] and [Atanh(x)]. *)
Definition ev_ln (x : f64) (n : nat) : option Dyadic.encl :=
  let* d := Dyadic.from_f64 n x in
  ln_dy n d.

Definition ev_log2 (x : f64) (n : nat) : option Dyadic.encl :=
  let* d := Dyadic.from_f64 n x in
  let* (e, a, less) := reduce n d in
  let* (h, l) := DyadicConsts.ln2 n in
  let* c := Dyadic.encl_add n {| Dyadic.en_lo := h; Dyadic.en_hi := h |} l in
  let* r := Dyadic.encl_div n a c in
  let* p1 := Dyadic.encl_point n DyadicExp.one in
  let* k := DyadicExp.mul_int n p1 e in
  Dyadic.encl_add n k (if less then Dyadic.encl_neg n r else r).

Definition ev_log10 (x : f64) (n : nat) : option Dyadic.encl :=
  let* (h, l) := DyadicConsts.ln10 n in
  let* d := Dyadic.from_f64 n x in
  let* y := ln_dy n d in
  let* c := Dyadic.encl_add n {| Dyadic.en_lo := h; Dyadic.en_hi := h |} l in
  Dyadic.encl_div n y c.

Definition ev_asinh (x : f64) (n : nat) : option Dyadic.encl :=
  let* t := Dyadic.encl_point n (fabs x) in
  let* one_e := Dyadic.encl_point n DyadicExp.one in
  let* t2 := Dyadic.encl_mul n t t in
  let* c2 := Dyadic.encl_add n one_e t2 in
  let* c := Dyadic.encl_sqrt n c2 in
  let* r :=
    if le (fabs x) series_max then
      let* u := Dyadic.encl_div n t c in
      atanh_series n u
    else
      let* s := Dyadic.encl_add n t c in
      ln_encl n s in
  Some (if lt x zero then Dyadic.encl_neg n r else r).

Definition ev_acosh (x : f64) (n : nat) : option Dyadic.encl :=
  let* px := Dyadic.encl_point n x in
  let* one_e := Dyadic.encl_point n DyadicExp.one in
  let* xm := Dyadic.encl_sub n px one_e in
  let* xp := Dyadic.encl_add n px one_e in
  let* p := Dyadic.encl_mul n xm xp in
  let* r := Dyadic.encl_sqrt n p in
  if le x acosh_series_max then
    let* u := Dyadic.encl_div n r px in
    atanh_series n u
  else
    let* s := Dyadic.encl_add n px r in
    ln_encl n s.

Definition ev_atanh (x : f64) (n : nat) : option Dyadic.encl :=
  let* t := Dyadic.encl_point n (fabs x) in
  let* r :=
    if le (fabs x) series_max then atanh_series n t
    else
      let* one_e := Dyadic.encl_point n DyadicExp.one in
      let* a := Dyadic.encl_add n one_e t in
      let* b := Dyadic.encl_sub n one_e t in
      let* q := Dyadic.encl_div n a b in
      let* l := ln_encl n q in
      Dyadic.encl_shl n l (-1) in
  Some (if lt x zero then Dyadic.encl_neg n r else r).

(** [fn log_rules(x: f64) -> Option<f64>], where [f64::NAN] is the NaN of
    the model. *)
Definition log_rules (x : f64) : option f64 :=
  if is_nan x || eq x infinity then Some x
  else if eq x zero then Some DyadicExp.neg_infinity
  else if lt x zero then Some B754_nan
  else None.

(** [pub(crate) fn ln(x: f64, up: bool) -> f64] *)
Definition ln_dir (x : f64) (up : bool) : option f64 :=
  match log_rules x with Some r => Some r | None => Dyadic.ziv (ev_ln x) up 1 end.

(** [pub(crate) fn log2(x: f64, up: bool) -> f64] *)
Definition log2_dir (x : f64) (up : bool) : option f64 :=
  match log_rules x with Some r => Some r | None => Dyadic.ziv (ev_log2 x) up 1 end.

(** [pub(crate) fn log10(x: f64, up: bool) -> f64], where
    [POW10.iter().position(|&p| p == x)] is the first [k] of [0, ..., 22]
    with [eq (DyadicExp.pow10 k) x], and [k as f64] is [of_u64 k]. *)
Definition log10_dir (x : f64) (up : bool) : option f64 :=
  match log_rules x with
  | Some r => Some r
  | None =>
      match List.find (fun k => eq (DyadicExp.pow10 (Z.of_nat k)) x) (List.seq 0 23) with
      | Some k => Some (of_u64 (Z.of_nat k))
      | None => Dyadic.ziv (ev_log10 x) up 1
      end
  end.

(** [pub(crate) fn asinh(x: f64, up: bool) -> f64], where [x.is_infinite()]
    is [x == f64::INFINITY || x == f64::NEG_INFINITY]. *)
Definition asinh_dir (x : f64) (up : bool) : option f64 :=
  if is_nan x || (eq x infinity || eq x DyadicExp.neg_infinity) then Some x
  else if lt (fabs x) DyadicExp.tiny_hyp then Some (DyadicExp.toward_zero x up)
  else Dyadic.ziv (ev_asinh x) up 1.

(** [pub(crate) fn acosh(x: f64, up: bool) -> f64] *)
Definition acosh_dir (x : f64) (up : bool) : option f64 :=
  if is_nan x || eq x infinity then Some x
  else if lt x DyadicExp.one then Some B754_nan
  else Dyadic.ziv (ev_acosh x) up 1.

(** [pub(crate) fn atanh(x: f64, up: bool) -> f64] *)
Definition atanh_dir (x : f64) (up : bool) : option f64 :=
  let t := fabs x in
  if is_nan x then Some x
  else if gt t DyadicExp.one then Some B754_nan
  else if eq t DyadicExp.one then Some (if gt x zero then infinity else DyadicExp.neg_infinity)
  else if lt t DyadicExp.tiny_hyp then Some (DyadicExp.away x up)
  else Dyadic.ziv (ev_atanh x) up 1.

End DyadicLog.

(** ** The inverse trigonometric functions of the dyadic kernel

    The functions of [src/dyadic/atan.rs]: [atan_dir x up] is [atan(x,
    up)], and the same for [asin] and [acos], and [atan2_dir y x up] is
    [atan2(y, x, up)], with [None] where the Rust function panics: an
    [assert!] of this file, [ziv] at its cap, or any operation of the
    kernel that panics. The [Eval]s are the functions [ev_atan x] and the
    others of a level [n]. The constants and functions of
    [src/dyadic/exp.rs] that they use are those of [DyadicExp], as are
    the literals [1.0] and [f64::NEG_INFINITY], and the literal [0.5] is
    [DyadicLog.half]. [DyAtanCore.v], [DyAtan.v] and [DyAsin.v] prove
    them, with the rules before the loop proved in [DyAtanTiny.v], and
    [DyPoint.v] makes a [point] of them. *)
Module DyadicAtan.

(** The [f64] literals of the file, written with [from_bits]: [T1] =
    0.4140625, [T2] = 2.4140625, [ASIN_SPLIT] = 0.75, [TINY_ASIN] = 2^-27,
    [HUGE_ATAN] = 2^54, and [0.25] and [0.75]. *)
Definition t1 : f64 := from_bits 0x3fda800000000000.
Definition t2 : f64 := from_bits 0x4003500000000000.
Definition asin_split : f64 := from_bits 0x3fe8000000000000.
Definition tiny_asin : f64 := from_bits 0x3e40000000000000.
Definition huge_atan : f64 := from_bits 0x4350000000000000.
Definition quarter : f64 := from_bits 0x3fd0000000000000.
Definition three_quarters : f64 := from_bits 0x3fe8000000000000.

(** [NO_HALVE] = 2^-8. *)
Definition no_halve : f64 := from_bits 0x3f70000000000000.

(** [fn terms<N>(z: &Encl<N>) -> u64], where [-bits - z.hi.exp], which
    is positive there, and [64 * N as u64 + 3 + e], which is below
    [2^64], are computed without a check. *)
Definition terms (n : nat) (z : Dyadic.encl) : Z :=
  if Dyadic.is_zero n (Dyadic.en_hi z) then 1
  else if - (64 * Z.of_nat n) <=? Dyadic.dy_exp (Dyadic.en_hi z) then 14 * Z.of_nat n + 2
  else
    let e := - (64 * Z.of_nat n) - Dyadic.dy_exp (Dyadic.en_hi z) in
    Z.min (14 * Z.of_nat n + 2) ((64 * Z.of_nat n + 3 + e) / e).

(** The loop [for k in (0..n).rev() { t =
    one.div_u64(2 * k + 1).sub(&z.mul(&t)) }] of [series], for [k]
    from [i - 1] down to 0. *)
Fixpoint series_loop (n : nat) (one_e z : Dyadic.encl) (i : nat) (t : Dyadic.encl)
  : option Dyadic.encl :=
  match i with
  | O => Some t
  | S k =>
      let* q := Dyadic.encl_div_u64 n one_e (2 * Z.of_nat k + 1) in
      let* p := Dyadic.encl_mul n z t in
      let* t' := Dyadic.encl_sub n q p in
      series_loop n one_e z k t'
  end.

(** [fn series<N>(v: &Encl<N>) -> Encl<N>] *)
Definition series (n : nat) (v : Dyadic.encl) : option Dyadic.encl :=
  let* one_e := Dyadic.encl_point n DyadicExp.one in
  let* z := Dyadic.encl_mul n v v in
  let* one_d := Dyadic.from_f64 n DyadicExp.one in
  let* hi := Dyadic.div_u64 n one_d (2 * terms n z + 1) true in
  let* t :=
    series_loop n one_e z (Z.to_nat (terms n z))
      {| Dyadic.en_lo := Dyadic.dy_zero n; Dyadic.en_hi := hi |} in
  Dyadic.encl_mul n v t.

(** [fn atan_series<N>(u: &Encl<N>) -> Encl<N>] *)
Definition atan_series (n : nat) (u : Dyadic.encl) : option Dyadic.encl :=
  let* h := Dyadic.from_f64 n no_halve in
  if negb (DyadicExp.dy_gt n (Dyadic.en_hi u) h) then series n u
  else
    let* one_e := Dyadic.encl_point n DyadicExp.one in
    let* u2 := Dyadic.encl_mul n u u in
    let* c2 := Dyadic.encl_add n one_e u2 in
    let* c := Dyadic.encl_sqrt n c2 in
    let* d := Dyadic.encl_add n one_e c in
    let* v := Dyadic.encl_div n u d in
    let* s := series n v in
    Dyadic.encl_shl n s 1.

(** [fn atan_encl<N>(w: &Encl<N>) -> Encl<N>], where the [assert!] is
    [None]. *)
Definition atan_encl (n : nat) (w : Dyadic.encl) : option Dyadic.encl :=
  if Dyadic.dy_neg (Dyadic.en_lo w) then None else
  let* one_e := Dyadic.encl_point n DyadicExp.one in
  let* t1_d := Dyadic.from_f64 n t1 in
  if negb (DyadicExp.dy_gt n (Dyadic.en_hi w) t1_d) then atan_series n w
  else if DyadicExp.dy_lt n (Dyadic.en_hi w) (Dyadic.en_hi one_e) then
    let* a := Dyadic.encl_sub n one_e w in
    let* b := Dyadic.encl_add n one_e w in
    let* u := Dyadic.encl_div n a b in
    let* p := DyadicConsts.pi n in
    let* p4 := Dyadic.encl_shl n p (-2) in
    let* s := atan_series n u in
    Dyadic.encl_sub n p4 s
  else
    let* t2_d := Dyadic.from_f64 n t2 in
    if negb (DyadicExp.dy_gt n (Dyadic.en_lo w) t2_d) then
      let* a := Dyadic.encl_sub n w one_e in
      let* b := Dyadic.encl_add n w one_e in
      let* u := Dyadic.encl_div n a b in
      let* p := DyadicConsts.pi n in
      let* p4 := Dyadic.encl_shl n p (-2) in
      let* s := atan_series n u in
      Dyadic.encl_add n p4 s
    else
      let* p := DyadicConsts.pi n in
      let* p2 := Dyadic.encl_shl n p (-1) in
      let* u := Dyadic.encl_div n one_e w in
      let* s := atan_series n u in
      Dyadic.encl_sub n p2 s.

(** [fn asin_parts<N>(t: f64) -> (Encl<N>, bool)] *)
Definition asin_parts (n : nat) (t : f64) : option (Dyadic.encl * bool) :=
  let* x := Dyadic.encl_point n t in
  let* one_e := Dyadic.encl_point n DyadicExp.one in
  let* a := Dyadic.encl_sub n one_e x in
  let* b := Dyadic.encl_add n one_e x in
  let* p := Dyadic.encl_mul n a b in
  let* r := Dyadic.encl_sqrt n p in
  if le t asin_split then
    let* q := Dyadic.encl_div n x r in
    let* s := atan_encl n q in
    Some (s, true)
  else
    let* q := Dyadic.encl_div n r x in
    let* s := atan_encl n q in
    Some (s, false).

(** The [eval::<N>()] of [PiMul(c)], [Atan(x)], [Atan2(y, x)], [Asin(x)]
    and [Acos(x)], where [x.abs()] is [fabs x]. *)
Definition ev_pi (c : f64) (n : nat) : option Dyadic.encl :=
  let* pc := Dyadic.encl_point n c in
  let* p := DyadicConsts.pi n in
  Dyadic.encl_mul n pc p.

Definition ev_atan (x : f64) (n : nat) : option Dyadic.encl :=
  let* t := Dyadic.encl_point n (fabs x) in
  let* r := atan_encl n t in
  Some (if lt x zero then Dyadic.encl_neg n r else r).

Definition ev_atan2 (y x : f64) (n : nat) : option Dyadic.encl :=
  let* a := Dyadic.encl_point n (fabs y) in
  let* b := Dyadic.encl_point n (fabs x) in
  let* r :=
    if le (fabs y) (fabs x) then
      let* q := Dyadic.encl_div n a b in
      let* t := atan_encl n q in
      if gt x zero then Some t
      else
        let* p := DyadicConsts.pi n in
        Dyadic.encl_sub n p t
    else
      let* q := Dyadic.encl_div n b a in
      let* t := atan_encl n q in
      let* p := DyadicConsts.pi n in
      let* h := Dyadic.encl_shl n p (-1) in
      if gt x zero then Dyadic.encl_sub n h t else Dyadic.encl_add n h t in
  Some (if lt y zero then Dyadic.encl_neg n r else r).

Definition ev_asin (x : f64) (n : nat) : option Dyadic.encl :=
  let* (a, below) := asin_parts n (fabs x) in
  let* r :=
    if below then Some a
    else
      let* p := DyadicConsts.pi n in
      let* h := Dyadic.encl_shl n p (-1) in
      Dyadic.encl_sub n h a in
  Some (if lt x zero then Dyadic.encl_neg n r else r).

Definition ev_acos (x : f64) (n : nat) : option Dyadic.encl :=
  let* (a, below) := asin_parts n (fabs x) in
  let* r :=
    if below then
      let* p := DyadicConsts.pi n in
      let* h := Dyadic.encl_shl n p (-1) in
      Dyadic.encl_sub n h a
    else Some a in
  if lt x zero then
    let* p := DyadicConsts.pi n in
    Dyadic.encl_sub n p r
  else Some r.

(** [fn pi_times(c: f64, up: bool) -> f64] *)
Definition pi_times (c : f64) (up : bool) : option f64 := Dyadic.ziv (ev_pi c) up 1.

(** [fn tiny_quotient(y: f64, x: f64) -> Option<f64>], with [Some None]
    for [None], where [a.exp - b.exp], which cannot overflow, is computed
    without a check. *)
Definition tiny_quotient (y x : f64) : option (option f64) :=
  let* a := Dyadic.from_f64 1 y in
  let* b := Dyadic.from_f64 1 x in
  if -25 <=? Dyadic.dy_exp a - Dyadic.dy_exp b then Some None else
  let* lo := Dyadic.div 1 a b false in
  let* hi := Dyadic.div 1 a b true in
  let* q := Dyadic.to_f64 1 lo false in
  let* q' := Dyadic.to_f64 1 hi true in
  Some (if eq q q' && lt (fabs q) DyadicExp.tiny_hyp then Some q else None).

(** [pub(crate) fn atan(x: f64, up: bool) -> f64] *)
Definition atan_dir (x : f64) (up : bool) : option f64 :=
  if is_nan x then Some x
  else if ge (fabs x) huge_atan then pi_times (copysign DyadicLog.half x) up
  else if lt (fabs x) DyadicExp.tiny_hyp then Some (DyadicExp.toward_zero x up)
  else Dyadic.ziv (ev_atan x) up 1.

(** [pub(crate) fn asin(x: f64, up: bool) -> f64] *)
Definition asin_dir (x : f64) (up : bool) : option f64 :=
  if is_nan x then Some x
  else if gt (fabs x) DyadicExp.one then Some B754_nan
  else if lt (fabs x) tiny_asin then Some (DyadicExp.away x up)
  else Dyadic.ziv (ev_asin x) up 1.

(** [pub(crate) fn acos(x: f64, up: bool) -> f64] *)
Definition acos_dir (x : f64) (up : bool) : option f64 :=
  if is_nan x then Some x
  else if gt (fabs x) DyadicExp.one then Some B754_nan
  else Dyadic.ziv (ev_acos x) up 1.

(** [pub(crate) fn atan2(y: f64, x: f64, up: bool) -> f64], where
    [x.is_sign_positive()] is [negb (Bsign x)], as [x] is not NaN there,
    [y.is_infinite()] is [y == f64::INFINITY || y == f64::NEG_INFINITY],
    and [0.0_f64.copysign(y)] is [copysign zero y]. *)
Definition atan2_dir (y x : f64) (up : bool) : option f64 :=
  if is_nan y || is_nan x then Some B754_nan
  else if eq y zero then
    if negb (Bsign x) then Some y else pi_times (copysign DyadicExp.one y) up
  else if eq y infinity || eq y DyadicExp.neg_infinity then
    let c :=
      if eq x infinity then quarter
      else if eq x DyadicExp.neg_infinity then three_quarters
      else DyadicLog.half in
    pi_times (copysign c y) up
  else if eq x infinity then Some (copysign zero y)
  else if eq x DyadicExp.neg_infinity then pi_times (copysign DyadicExp.one y) up
  else if eq x zero then pi_times (copysign DyadicLog.half y) up
  else
    let* q := if gt x zero then tiny_quotient y x else Some None in
    match q with
    | Some q => Some (DyadicExp.toward_zero q up)
    | None => Dyadic.ziv (ev_atan2 y x) up 1
    end.

End DyadicAtan.

(** ** MPFR

    [src/elementary.rs] computes the bounds of [exp] and the other
    elementary functions with functions of [src/mpfr_calls.rs], which call
    MPFR through [rug] and [gmp_mpfr_sys]. Those functions are the fields
    of the record [point] below, which the elementary functions take as
    their first argument [pt].

    The model leaves MPFR's functions abstract: an MPFR number is an
    [mpfr_t], and the MPFR functions with which [src/mpfr_calls/mpfr.rs]
    computes those bounds, [mpfr::get_d] and the 21 that the uses of
    [mpfr_fn!], [mpfr_fn2!] and [mpfr_fn_si!] there call, are the fields
    of a record [mpfr], of which [mpfr_point] makes the record [point]
    that inari uses. [Mpfr.v] states what the MPFR manual says of them,
    and the theorems stated for MPFR functions [m] assume it of [m]. The
    other functions of [gmp_mpfr_sys::mpfr] that [src/mpfr_calls/mpfr.rs]
    calls are not fields: [assert_thread_safe()], which calls
    [mpfr::buildopt_tls_p], is left out; and [with_parse_range] and
    [round_rational], which call [mpfr::get_emin], [mpfr::get_emax],
    [mpfr::set_emin], [mpfr::set_emax], [mpfr::set_q] and
    [mpfr::subnormalize], and [fmt_bound_mpfr], which prints a bound of an
    interval with [mpfr::asprintf] and [mpfr::free_str], as inari did
    before [src/format/digits.rs], are compiled only for the tests, and are
    not modelled. Outside these, what it does through [rug] is
    [Float::with_val], which is [with_val] below, and the allocation and
    freeing of MPFR numbers, which are left out.

    [Contract.v] states what each field of [point] must do at the level
    of [f64]s; [MpfrPoint.v] shows that [mpfr_point m] does it under
    [Mpfr.v]'s hypotheses, and [PointTheorems.v] proves [exp_correct] and
    the other theorems that its header lists for every record that does
    (as [exp_correct_point] and the others). *)

(** [mpfr::rnd_t::RNDD] and [mpfr::rnd_t::RNDU], rounding toward -inf and
    toward +inf. *)
Inductive mpfr_rnd : Type := RNDD | RNDU.

(** The value of an MPFR number: NaN, an infinity or a zero with its sign,
    [true] for negative as in Flocq, or a real other than 0. [Mpfr.v] says
    which reals an MPFR number of 53 bits holds. NaN payloads are not
    modelled. *)
Inductive mpfr_t : Type :=
  | MNaN
  | MInf (s : bool)
  | MZero (s : bool)
  | MNum (r : R).

(** [Float::with_val(f64::MANTISSA_DIGITS, x)], an MPFR number of 53 bits
    that holds [x] exactly, as every [f64] is an MPFR number of 53 bits if
    MPFR's exponent range contains that of [f64], which [Mpfr.v] assumes.
    It keeps the sign of a zero and the infinities. *)
Definition with_val (x : f64) : mpfr_t :=
  match x with
  | B754_zero s => MZero s
  | B754_infinity s => MInf s
  | B754_nan => MNaN
  | B754_finite _ _ _ _ => MNum (B2R x)
  end.

(** The MPFR functions with which [src/mpfr_calls/mpfr.rs] computes
    bounds; the others that it calls are not fields (see the start of this
    section). The fields are each a function of the rounding direction
    and of the argument: [mpfr_get_d], through [get_d], and [mpfr_acos]
    and the 20 others that the uses of [mpfr_fn!], [mpfr_fn2!] and
    [mpfr_fn_si!] call, of which [mpfr_log] is MPFR's [log].
    [mpfr::f(x.as_raw_mut(), x.as_raw(), rnd)] sets the MPFR number [x] to
    [f rnd x], rounded to the 53 bits of [x], which is both the argument
    and the result. [mpfr_atan2] and [mpfr_pow] take a second MPFR number,
    and [mpfr_pow_si] a [c_long], which is an integer here:
    [mpfr::atan2(x.as_raw_mut(), x.as_raw(), y.as_raw(), rnd)] sets [x] to
    [mpfr_atan2 rnd x y],
    [mpfr::pow(x.as_raw_mut(), x.as_raw(), y.as_raw(), rnd)] to
    [mpfr_pow rnd x y], and
    [mpfr::pow_si(x.as_raw_mut(), x.as_raw(), n, rnd)] to
    [mpfr_pow_si rnd x n]. No field takes MPFR's exponent range, [emin]
    and [emax], as the functions that [mpfr_fn!] and the other macros
    define do not set it, and [Mpfr.v] states what it assumes of them for
    any range that contains that of [f64].

    [ideal] in [MpfrIdeal.v] is a record of this type, which
    [MpfrConsistent.v] shows satisfies those hypotheses, so a change to
    the fields has to be made there too. *)
Record mpfr : Type := {
  mpfr_get_d : mpfr_rnd -> mpfr_t -> f64;
  mpfr_acos : mpfr_rnd -> mpfr_t -> mpfr_t;
  mpfr_acosh : mpfr_rnd -> mpfr_t -> mpfr_t;
  mpfr_asin : mpfr_rnd -> mpfr_t -> mpfr_t;
  mpfr_asinh : mpfr_rnd -> mpfr_t -> mpfr_t;
  mpfr_atan : mpfr_rnd -> mpfr_t -> mpfr_t;
  mpfr_atan2 : mpfr_rnd -> mpfr_t -> mpfr_t -> mpfr_t;
  mpfr_atanh : mpfr_rnd -> mpfr_t -> mpfr_t;
  mpfr_cos : mpfr_rnd -> mpfr_t -> mpfr_t;
  mpfr_cosh : mpfr_rnd -> mpfr_t -> mpfr_t;
  mpfr_exp : mpfr_rnd -> mpfr_t -> mpfr_t;
  mpfr_exp10 : mpfr_rnd -> mpfr_t -> mpfr_t;
  mpfr_exp2 : mpfr_rnd -> mpfr_t -> mpfr_t;
  mpfr_log : mpfr_rnd -> mpfr_t -> mpfr_t;
  mpfr_log10 : mpfr_rnd -> mpfr_t -> mpfr_t;
  mpfr_log2 : mpfr_rnd -> mpfr_t -> mpfr_t;
  mpfr_pow : mpfr_rnd -> mpfr_t -> mpfr_t -> mpfr_t;
  mpfr_pow_si : mpfr_rnd -> mpfr_t -> Z -> mpfr_t;
  mpfr_sin : mpfr_rnd -> mpfr_t -> mpfr_t;
  mpfr_sinh : mpfr_rnd -> mpfr_t -> mpfr_t;
  mpfr_tan : mpfr_rnd -> mpfr_t -> mpfr_t;
  mpfr_tanh : mpfr_rnd -> mpfr_t -> mpfr_t
}.

(** The body [mpfr_fn!(let x = $mpfr_f(x, rnd)); get_d(&x, rnd)] of the
    functions that [mpfr_fn!] defines, for the MPFR function [f]: [x] as
    an MPFR number of 53 bits, set to [f] of it rounded in the direction
    [rnd], and then converted to an [f64] in the same direction by
    [get_d], which calls [mpfr::get_d]. The call of
    [crate::mpfr_calls::assert_thread_safe()] that begins the [let] arm is
    left out: it panics where the linked MPFR is not built thread-safe,
    and does nothing otherwise. *)
Definition mpfr_fn (m : mpfr) (f : mpfr_rnd -> mpfr_t -> mpfr_t)
    (rnd : mpfr_rnd) (x : f64) : f64 :=
  mpfr_get_d m rnd (f rnd (with_val x)).

(** The body [mpfr_fn2!(let x = $mpfr_f(x, y, rnd)); get_d(&x, rnd)] of
    the functions that [mpfr_fn2!] defines, for the MPFR function [f] of
    two numbers: [x] and [y] as MPFR numbers of 53 bits, [x] set to [f] of
    them rounded in the direction [rnd], and then converted to an [f64] in
    the same direction by [get_d]. The call of [assert_thread_safe()] is
    left out, as in [mpfr_fn]. *)
Definition mpfr_fn2 (m : mpfr) (f : mpfr_rnd -> mpfr_t -> mpfr_t -> mpfr_t)
    (rnd : mpfr_rnd) (x y : f64) : f64 :=
  mpfr_get_d m rnd (f rnd (with_val x) (with_val y)).

(** The body [mpfr_fn_si!(let x = $mpfr_f(x, y, rnd)); get_d(&x, rnd)] of
    the functions that [mpfr_fn_si!] defines, for the MPFR function [f] of
    a number and a [c_long], with the [i32] [y] as the integer [n], which
    [y.into()] converts to a [c_long] exactly. The call of
    [assert_thread_safe()] is left out, as in [mpfr_fn]. *)
Definition mpfr_fn_si (m : mpfr) (f : mpfr_rnd -> mpfr_t -> Z -> mpfr_t)
    (rnd : mpfr_rnd) (x : f64) (n : Z) : f64 :=
  mpfr_get_d m rnd (f rnd (with_val x) n).

(** The integers that an [i32] holds. *)
Definition is_i32 (n : Z) : Prop := (- 2 ^ 31 <= n < 2 ^ 31)%Z.

(** The functions that [src/mpfr_calls.rs] gives the elementary functions
    to compute bounds with, each a function of the rounding direction: a
    field [p_f] for each pair of functions [f_rd] and [f_ru] that
    [mpfr_fn!], [mpfr_fn2!] or [mpfr_fn_si!] defines in
    [src/mpfr_calls/mpfr.rs], with [f_rd] as [p_f pt RNDD] and [f_ru] as
    [p_f pt RNDU]. The fields are in the order of the uses of those macros
    there, which is that of the record [mpfr], and are named after the
    Rust functions: [p_ln] is [ln_rd] and [ln_ru], which call MPFR's
    [log], and [p_pown] is [pown_rd] and [pown_ru], which call [pow_si].

    The elementary functions below take such a record as their first
    argument [pt]. [mpfr_point m] is the one that [src/mpfr_calls/mpfr.rs]
    makes of the MPFR functions [m]. [Contract.v] states what each field
    must do at the level of [f64]s; [MpfrPoint.v] shows that
    [mpfr_point m] does it under [Mpfr.v]'s hypotheses, and
    [PointTheorems.v] proves [exp_correct] for every record that does. *)
Record point : Type := {
  p_acos : mpfr_rnd -> f64 -> f64;
  p_acosh : mpfr_rnd -> f64 -> f64;
  p_asin : mpfr_rnd -> f64 -> f64;
  p_asinh : mpfr_rnd -> f64 -> f64;
  p_atan : mpfr_rnd -> f64 -> f64;
  p_atan2 : mpfr_rnd -> f64 -> f64 -> f64;
  p_atanh : mpfr_rnd -> f64 -> f64;
  p_cos : mpfr_rnd -> f64 -> f64;
  p_cosh : mpfr_rnd -> f64 -> f64;
  p_exp : mpfr_rnd -> f64 -> f64;
  p_exp10 : mpfr_rnd -> f64 -> f64;
  p_exp2 : mpfr_rnd -> f64 -> f64;
  p_ln : mpfr_rnd -> f64 -> f64;
  p_log10 : mpfr_rnd -> f64 -> f64;
  p_log2 : mpfr_rnd -> f64 -> f64;
  p_pow : mpfr_rnd -> f64 -> f64 -> f64;
  p_pown : mpfr_rnd -> f64 -> Z -> f64;
  p_sin : mpfr_rnd -> f64 -> f64;
  p_sinh : mpfr_rnd -> f64 -> f64;
  p_tan : mpfr_rnd -> f64 -> f64;
  p_tanh : mpfr_rnd -> f64 -> f64
}.

(** The record [point] that [src/mpfr_calls/mpfr.rs] makes of the MPFR
    functions [m]. [mpfr_fn!(acos, acos_rd, acos_ru)] defines [acos_rd]
    and [acos_ru] as [mpfr_fn m (mpfr_acos m)] in the directions [RNDD]
    and [RNDU], and the other uses of [mpfr_fn!] the same, those of
    [mpfr_fn2!] with [mpfr_fn2] and that of [mpfr_fn_si!] with
    [mpfr_fn_si]. *)
Definition mpfr_point (m : mpfr) : point := {|
  p_acos := mpfr_fn m (mpfr_acos m);
  p_acosh := mpfr_fn m (mpfr_acosh m);
  p_asin := mpfr_fn m (mpfr_asin m);
  p_asinh := mpfr_fn m (mpfr_asinh m);
  p_atan := mpfr_fn m (mpfr_atan m);
  p_atan2 := mpfr_fn2 m (mpfr_atan2 m);
  p_atanh := mpfr_fn m (mpfr_atanh m);
  p_cos := mpfr_fn m (mpfr_cos m);
  p_cosh := mpfr_fn m (mpfr_cosh m);
  p_exp := mpfr_fn m (mpfr_exp m);
  p_exp10 := mpfr_fn m (mpfr_exp10 m);
  p_exp2 := mpfr_fn m (mpfr_exp2 m);
  p_ln := mpfr_fn m (mpfr_log m);
  p_log10 := mpfr_fn m (mpfr_log10 m);
  p_log2 := mpfr_fn m (mpfr_log2 m);
  p_pow := mpfr_fn2 m (mpfr_pow m);
  p_pown := mpfr_fn_si m (mpfr_pow_si m);
  p_sin := mpfr_fn m (mpfr_sin m);
  p_sinh := mpfr_fn m (mpfr_sinh m);
  p_tan := mpfr_fn m (mpfr_tan m);
  p_tanh := mpfr_fn m (mpfr_tanh m)
|}.

(** The theorems about the elementary functions, other than those of
    [PointTheorems.v] and [DyPoint.v], are stated for the MPFR
    functions [m], and apply the functions below to [mpfr_point m], which
    this coercion lets them write as [m]. *)
Coercion mpfr_point : mpfr >-> point.

(** The functions that [mpfr_fn!(acos, acos_rd, acos_ru)] and the other
    uses of [mpfr_fn!], [mpfr_fn2!] and [mpfr_fn_si!] in
    [src/mpfr_calls/mpfr.rs] define. *)
Definition acos_rd (pt : point) := p_acos pt RNDD.
Definition acos_ru (pt : point) := p_acos pt RNDU.
Definition acosh_rd (pt : point) := p_acosh pt RNDD.
Definition acosh_ru (pt : point) := p_acosh pt RNDU.
Definition asin_rd (pt : point) := p_asin pt RNDD.
Definition asin_ru (pt : point) := p_asin pt RNDU.
Definition asinh_rd (pt : point) := p_asinh pt RNDD.
Definition asinh_ru (pt : point) := p_asinh pt RNDU.
Definition atan_rd (pt : point) := p_atan pt RNDD.
Definition atan_ru (pt : point) := p_atan pt RNDU.
Definition atan2_rd (pt : point) := p_atan2 pt RNDD.
Definition atan2_ru (pt : point) := p_atan2 pt RNDU.
Definition atanh_rd (pt : point) := p_atanh pt RNDD.
Definition atanh_ru (pt : point) := p_atanh pt RNDU.
Definition cos_rd (pt : point) := p_cos pt RNDD.
Definition cos_ru (pt : point) := p_cos pt RNDU.
Definition cosh_rd (pt : point) := p_cosh pt RNDD.
Definition cosh_ru (pt : point) := p_cosh pt RNDU.
Definition exp_rd (pt : point) := p_exp pt RNDD.
Definition exp_ru (pt : point) := p_exp pt RNDU.
Definition exp10_rd (pt : point) := p_exp10 pt RNDD.
Definition exp10_ru (pt : point) := p_exp10 pt RNDU.
Definition exp2_rd (pt : point) := p_exp2 pt RNDD.
Definition exp2_ru (pt : point) := p_exp2 pt RNDU.
Definition ln_rd (pt : point) := p_ln pt RNDD.
Definition ln_ru (pt : point) := p_ln pt RNDU.
Definition log10_rd (pt : point) := p_log10 pt RNDD.
Definition log10_ru (pt : point) := p_log10 pt RNDU.
Definition log2_rd (pt : point) := p_log2 pt RNDD.
Definition log2_ru (pt : point) := p_log2 pt RNDU.
Definition pow_rd (pt : point) := p_pow pt RNDD.
Definition pow_ru (pt : point) := p_pow pt RNDU.
Definition pown_rd (pt : point) := p_pown pt RNDD.
Definition pown_ru (pt : point) := p_pown pt RNDU.
Definition sin_rd (pt : point) := p_sin pt RNDD.
Definition sin_ru (pt : point) := p_sin pt RNDU.
Definition sinh_rd (pt : point) := p_sinh pt RNDD.
Definition sinh_ru (pt : point) := p_sinh pt RNDU.
Definition tan_rd (pt : point) := p_tan pt RNDD.
Definition tan_ru (pt : point) := p_tan pt RNDU.
Definition tanh_rd (pt : point) := p_tanh pt RNDD.
Definition tanh_ru (pt : point) := p_tanh pt RNDU.

(** [x.max(y)] of two [f64]s that are not NaN, as [Interval::cosh],
    [Interval::cos], [Interval::pow] and [Interval::sin] call it: the
    larger of the two. If they compare equal, Rust returns either, and
    such floats differ only as +0 and -0, so the argument [first] says
    whether it is [x]. *)
Definition fmax (first : bool) (x y : f64) : f64 :=
  if lt x y then y else if lt y x then x else if first then x else y.

(** [x.min(y)] of two [f64]s that are not NaN, as [Interval::cos],
    [Interval::pow] and [Interval::sin] call it: the smaller of the two,
    and as for [fmax], [first] says which one Rust returns if they compare
    equal. *)
Definition fmin (first : bool) (x y : f64) : f64 :=
  if lt x y then x else if lt y x then y else if first then x else y.

(** [fn rem_euclid_2(x: f64) -> f64] in [src/elementary.rs]. *)
Definition rem_euclid_2 (x : f64) : f64 :=
  if eq (mul (of_u64 2) (ffloor (div x (of_u64 2)))) x then zero else of_u64 1.

(** [fn quadrant(x: f64) -> f64] in [src/elementary.rs], with
    [sin_rd(x) < 0.0] as [lt (sin_rd pt x) zero], [cos_ru(x) > 0.0] as
    [lt zero (cos_ru pt x)], and the [match] on the two as [if]s. *)
Definition quadrant (pt : point) (x : f64) : f64 :=
  let sin_neg := lt (sin_rd pt x) zero in
  let cos_pos := lt zero (cos_ru pt x) in
  if sin_neg then (if cos_pos then of_u64 3 else of_u64 2)
  else (if cos_pos then zero else of_u64 1).

(** [fn quadrants(a: f64, b: f64) -> (f64, f64)] in [src/elementary.rs],
    with [(..).rem_euclid(4.0)] as [rem_euclid _ (of_u64 4)]. *)
Definition quadrants (pt : point) (a b : f64) : f64 * f64 :=
  let qa := quadrant pt a in
  let d := rem_euclid (sub (quadrant pt b) qa) (of_u64 4) in
  let n := if le (sub b a) (add (mul (of_u64 2) d) (of_u64 3)) then d
           else add d (of_u64 4) in
  (qa, n).

(** ** Intervals

    The parts of [src/interval.rs], [src/interval/dec_interval.rs],
    [src/boolean.rs], [src/classify.rs],
    [src/integer.rs], [src/absmax.rs], [src/arith.rs], [src/basic.rs],
    [src/set_op.rs], [src/constants.rs] and [src/elementary.rs] that
    [Interval::abs], [Interval::cancel_minus], [Interval::cancel_plus],
    [Interval::ceil], [Interval::floor], [Interval::max], [Interval::min],
    [Interval::mul_add], [Interval::mul_rev_to_pair], [Interval::recip],
    [Interval::round], [Interval::round_ties_even], [Interval::sign],
    [Interval::sqr], [Interval::sqrt], [Interval::trunc],
    [-x], [x + y], [x - y], [x * y] and [x / y] of intervals, the
    elementary functions [Interval::acos], [Interval::acosh],
    [Interval::asin], [Interval::asinh], [Interval::atan],
    [Interval::atan2], [Interval::atanh], [Interval::cos],
    [Interval::cosh], [Interval::exp], [Interval::exp10],
    [Interval::exp2], [Interval::ln], [Interval::log10], [Interval::log2],
    [Interval::pow], [Interval::powi], [Interval::sin], [Interval::sinh],
    [Interval::tan] and [Interval::tanh], and their decorated versions,
    use. Those call the
    backend's [floor], [ceil], [round], [round_ties_even], [trunc],
    [neg0], [splat], [constant], [extract], [eq], [ge], [gt], [le], [lt],
    [all], [bitmask], [and], [or], [max], [maximum], [min], [minimum],
    [shuffle02], [shuffle03], [shuffle13], [swap], [add_rn], [sub_rn],
    [hadd_rn], [add_ru], [sub_ru], [mul_ru], [div_ru], [mul_add_ru],
    [sqrt1_ru] and [sqrt_rd_ru], which are the ones in [Generic] here.
    The elementary functions also call MPFR, through the functions that
    are the argument [pt] here (see the record [point] above).
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
    [intersection] call the backend's [max] and [min]. The conversions in
    [parse.rs] round the bounds of an interval literal in [number_to_f64]
    and [rational_to_f64], with [Nat]s and the portable backend's
    [round_up_exact], which [Parse*.v] prove correct. *)

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

(** [pub struct DecInterval] in [src/interval/dec_interval.rs], with its
    fields [x] and [d] as [itv] and [dec]. The fields are private to that
    module, and the rest of the library reads them with
    [pub(crate) const fn x(self) -> Interval] and
    [pub(crate) const fn d(self) -> Decoration], which return them, so
    [x()] and [d()] are [itv] and [dec] too. *)
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

(** The types and functions of [src/parse.rs] that turn the bounds of an
    interval literal into [f64]s, and the step of its grammar that
    decorates a literal. The rest of the [nom] grammar of [parse.rs], which
    reads the literal and computes its bounds as exact rationals, is not
    modelled. Each [Nat] of [src/nat.rs], the unsigned integer of
    any width that [parse.rs] computes with, is the [Z] [z >= 0] that it
    holds, with the limbs [NatLimbs.to_limbs z], the only limbs with no
    zero limb at the top that hold [z]. Each of its operations is the loop
    of [NatLimbs] above on those limbs, through the wrapper of [NatLimbs]
    on [Z]s, such as [NatLimbs.mul_z] for [&a * &b]. [NatOps.v] proves what
    each wrapper computes, and that the loops of [NatLimbs] return limbs
    with no zero limb at the top. That the operations of [src/nat.rs] that
    are not modelled, such as [Nat::from_dec], [Nat::from_hex] and [-],
    return such limbs too is checked by reading, not proved. *)

(** [enum InfSup { Inf, Sup }], which says whether a bound is the lower or
    the upper one. [as_rnd_t] is not Rust: it names the direction in which
    the proofs round the bound, toward -inf for [Inf] and toward +inf for
    [Sup]. *)
Inductive InfSup : Type := Inf | Sup.

Definition as_rnd_t (infsup : InfSup) : mpfr_rnd :=
  match infsup with Inf => RNDD | Sup => RNDU end.

(** [struct Rat { neg: bool, num: Nat, den: Nat, e2: i32, e5: i32 }] of
    [src/parse/rat.rs], with its fields as [rat_neg], [rat_num],
    [rat_den], [rat_e2] and [rat_e5], and the value
    [(-1)^neg * num * 2^e2 * 5^e5 / den] that its comment gives it as
    [rat_R]. *)
Record Rat : Type :=
  { rat_neg : bool; rat_num : Z; rat_den : Z; rat_e2 : Z; rat_e5 : Z }.

Definition radix5 : radix := Build_radix 5 eq_refl.

Definition rat_R (x : Rat) : R :=
  let v :=
    Rdiv (Rmult (Rmult (IZR (rat_num x)) (bpow radix2 (rat_e2 x))) (bpow radix5 (rat_e5 x)))
      (IZR (rat_den x)) in
  if rat_neg x then Ropp v else v.

(** What the grammar guarantees of each [Rat] that it makes, which is not
    proved: [den > 0], as the comment of [Rat] says, and [e2] and [e5] are
    [i32]s. [num] and [den] have at most [2^63] bits, which is
    [2^60] bytes, more memory than any machine has. *)
Definition rat_ok (x : Rat) : Prop :=
  0 <= rat_num x < 2 ^ 2 ^ 63 /\ 0 < rat_den x < 2 ^ 2 ^ 63 /\
  - 2 ^ 31 <= rat_e2 x < 2 ^ 31 /\ - 2 ^ 31 <= rat_e5 x < 2 ^ 31.

(** The number of bits of an integer [n >= 0], 0 for 0, which
    [n.bits()] of a [Nat] computes ([NatOps.v]). *)
Definition nat_bits (n : Z) : Z := if n =? 0 then 0 else Z.log2 n + 1.

(** [enum Number { NegInfinity, Rational(Rat), Infinity }], and
    [fn neg(self) -> Self] of [impl Neg for Number], which negates a [Rat]
    by [impl Neg for Rat], flipping [neg]. *)
Inductive Number : Type := NegInfinity | Rational (r : Rat) | Infinity.

Definition number_neg (n : Number) : Number :=
  match n with
  | NegInfinity => Infinity
  | Rational r =>
      Rational {| rat_neg := negb (rat_neg r); rat_num := rat_num r; rat_den := rat_den r;
                  rat_e2 := rat_e2 r; rat_e5 := rat_e5 r |}
  | Infinity => NegInfinity
  end.

(** [a <= b] for [Number]s, by the derived [PartialOrd], which compares
    the variants in the order of their declaration, and two [Rational]s by
    [impl Ord for Rat], which compares their values. That [impl Ord for
    Rat] compares the values is tested, not proved. *)
Definition number_le (a b : Number) : Prop :=
  match a, b with
  | NegInfinity, _ => True
  | Rational p, Rational q => Rle (rat_R p) (rat_R q)
  | Rational _, Infinity => True
  | Infinity, Infinity => True
  | _, _ => False
  end.

(** What the grammar guarantees of a bound: [rat_ok] of a [Rational]. *)
Definition number_ok (n : Number) : Prop :=
  match n with Rational x => rat_ok x | _ => True end.

(** [enum NInterval { InfSup(Number, Number), Point(Number) }], with the
    variants as [NInfSup] and [NPoint], as [InfSup] is the type above, and
    its [fn inf(&self) -> &Number], [fn sup(&self) -> &Number] and
    [fn is_common_interval(&self) -> bool]. *)
Inductive NInterval : Type := NInfSup (a b : Number) | NPoint (a : Number).

(** [const EMPTY: Self] of [NInterval] *)
Definition n_EMPTY : NInterval := NInfSup Infinity NegInfinity.

Definition ninf (x : NInterval) : Number :=
  match x with NInfSup a _ => a | NPoint a => a end.

Definition nsup (x : NInterval) : Number :=
  match x with NInfSup _ b => b | NPoint a => a end.

Definition nis_common_interval (x : NInterval) : bool :=
  match ninf x, nsup x with Rational _, Rational _ => true | _, _ => false end.

(** [x == NInterval::EMPTY], by the derived [PartialEq], where
    [NInterval::EMPTY] is [Self::InfSup(Number::Infinity, Number::NegInfinity)]. *)
Definition nis_empty (x : NInterval) : bool :=
  match x with NInfSup Infinity NegInfinity => true | _ => false end.

(** What the grammar guarantees of the [NInterval]s that it returns,
    which is not proved: [x] is [NInterval::EMPTY], or its lower bound is
    at most its upper bound, the lower bound is not [Infinity] and the
    upper bound is not [NegInfinity]. [infsup_interval] tests the latter
    before it returns [InfSup(a, b)], and the other rules return
    [NInterval::EMPTY], [NInterval::ENTIRE], a [Point] of a [Rational], or,
    in [uncertain_interval], bounds that are [center - radius] or [center],
    and [center + radius] or [center], for a radius that is not negative,
    or [NegInfinity] and [Infinity]. Each bound has [number_ok]. *)
Definition ninterval_ok (x : NInterval) : Prop :=
  (nis_empty x = true \/
   (number_le (ninf x) (nsup x) /\ ninf x <> Infinity /\ nsup x <> NegInfinity)) /\
  number_ok (ninf x) /\ number_ok (nsup x).

(** [struct DecNInterval { x: NInterval, d: Decoration }], with its fields
    as [nx] and [nd]. *)
Record DecNInterval : Type := { nx : NInterval; nd : Decoration }.

(** [const EMPTY: Self] and [const NAI: Self] of [DecNInterval] *)
Definition dn_EMPTY : DecNInterval := {| nx := n_EMPTY; nd := Trv |}.
Definition dn_NAI : DecNInterval := {| nx := n_EMPTY; nd := Ill |}.

(** [fn new(x: NInterval) -> Self] of [DecNInterval] *)
Definition dn_new (x : NInterval) : DecNInterval :=
  let d :=
    if nis_empty x then Trv
    else if negb (nis_common_interval x) then Dac
    else Com in
  {| nx := x; nd := d |}.

(** [fn set_dec(x: NInterval, d: Decoration) -> Self] of [DecNInterval],
    which only the grammar calls. *)
Definition dn_set_dec (x : NInterval) (d : Decoration) : DecNInterval :=
  if dec_eqb d Ill then dn_NAI
  else if nis_empty x then dn_EMPTY
  else if dec_eqb d Com && negb (nis_common_interval x) then
    {| nx := x; nd := Dac |}
  else {| nx := x; nd := d |}.

(** The arm [(Ok(x), Some(d))] of the closure that [decorated_interval]
    passes to [map], for a literal [x] with the decoration [d], with
    [Ok(xd)] as [Some xd] and the [Err] as [None]. *)
Definition dn_decorated (x : NInterval) (d : Decoration) :
    option DecNInterval :=
  let xd := dn_set_dec x d in
  if dec_eqb (nd xd) d then Some xd else None.

(** What the grammar guarantees of each [DecNInterval] [x] that it
    returns: [nx x] has [ninterval_ok], [nd x] is [com] only if both bounds
    of [nx x] are [Rational]s, [NInterval::EMPTY] is decorated only [trv]
    or [ill], and only [NInterval::EMPTY] is decorated [ill].
    [decorated_interval] returns [DecNInterval::NAI] for [[nai]], and for
    a literal whose [NInterval] is [n], [DecNInterval::new(n)] if it has
    no decoration, and if it has the decoration [d], the [y] of
    [dn_decorated n d] if that is [Some y], and otherwise rejects the
    literal. [ParseDec.v] proves [dec_ninterval_ok] of [dn_NAI]
    ([dn_NAI_ok]), and, for an [n] with [ninterval_ok], of [dn_new n]
    ([dn_new_ok]) and of the [y] of a [Some y] that [dn_decorated n d]
    returns ([dn_decorated_ok]). That the [n] of each literal has
    [ninterval_ok], and that the [nom] combinators of [decorated_interval]
    return what is said above, is checked by reading, not proved. *)
Definition dec_ninterval_ok (x : DecNInterval) : Prop :=
  ninterval_ok (nx x) /\
  (nd x = Com -> nis_common_interval (nx x) = true) /\
  (nis_empty (nx x) = true -> nd x = Trv \/ nd x = Ill) /\
  (nd x = Ill -> nis_empty (nx x) = true).

(** [struct F64 { f: f64, inexact: bool, overflow: bool }], with its fields
    as [f64_f], [f64_inexact] and [f64_overflow]. *)
Record F64 : Type := { f64_f : f64; f64_inexact : bool; f64_overflow : bool }.

(** [f64::is_infinite] *)
Definition f64_is_infinite (x : f64) : bool :=
  match x with B754_infinity _ => true | _ => false end.

(** [enum Scaled { Huge, Tiny, Mid(u128, i32, bool) }] *)
Inductive Scaled : Type := Huge | Tiny | Mid (q e : Z) (sticky : bool).

(** [fn scale(x: &Rat) -> Scaled]. The [i128] operations are checked,
    [i128::from] of a [u64] or an [i32] keeps the value, and [as] keeps the
    low bits, as a cast between integers does. [a.bits()],
    [Nat::pow5(k)], [&a * &b], [&a << s], [a.div_rem(&b)], which panics for
    [b = 0], [a.low_u128()] and [a.is_zero()] of [Nat]s are
    [NatLimbs.bits_z a], [NatLimbs.pow5_z k], [NatLimbs.mul_z a b],
    [NatLimbs.shl_z a s], [NatLimbs.div_rem_z a b], [NatLimbs.low_u128_z a]
    and [NatLimbs.is_zero_z a], as the comment of this section says. *)
Definition scale (x : Rat) : option Scaled :=
  let e2 := rat_e2 x in
  let e5 := rat_e5 x in
  let* t := checked_i 128 (NatLimbs.bits_z (rat_num x) - NatLimbs.bits_z (rat_den x)) in
  let* b0 := checked_i 128 (t + e2) in
  let* lohi :=
    if 0 <=? e5 then
      let* lo5 := checked_i 128 (2 * e5) in
      let* hi5 := checked_i 128 (3 * e5) in
      Some (lo5, hi5)
    else
      let* lo5 := checked_i 128 (3 * e5) in
      let* hi5 := checked_i 128 (2 * e5) in
      Some (lo5, hi5) in
  let (lo5, hi5) := lohi in
  let* u := checked_i 128 (b0 + lo5) in
  if 1025 <=? u then Some Huge else
  let* v := checked_i 128 (b0 + hi5) in
  if v <=? -1075 then Some Tiny else
  (* [x.e5.unsigned_abs()] is [Z.abs e5]. *)
  let* p := NatLimbs.pow5_z (Z.abs e5) in
  let* nd :=
    if 0 <=? e5 then
      let* n := NatLimbs.mul_z (rat_num x) p in Some (n, rat_den x)
    else
      let* d := NatLimbs.mul_z (rat_den x) p in Some (rat_num x, d) in
  let (n, d) := nd in
  let* t' := checked_i 128 (NatLimbs.bits_z n - NatLimbs.bits_z d) in
  let* b := checked_i 128 (t' + e2) in
  if 1025 <=? b then Some Huge else
  if b <=? -1075 then Some Tiny else
  let* e := checked_i 128 (b - 56) in
  let* sh := checked_i 128 (e2 - e) in
  let* qr :=
    if 0 <=? sh then
      (* [sh as u64] *)
      let s := sh mod 2 ^ 64 in
      NatLimbs.div_rem_z (NatLimbs.shl_z n s) d
    else
      let* ns := checked_i 128 (- sh) in
      (* [(-sh) as u64] *)
      let s := ns mod 2 ^ 64 in
      NatLimbs.div_rem_z n (NatLimbs.shl_z d s) in
  let (q, r) := qr in
  (* [e as i32], which keeps the low 32 bits of [e] as a two's complement
     [i32]. *)
  let e32 := (e + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31 in
  Some (Mid (NatLimbs.low_u128_z q) e32 (negb (NatLimbs.is_zero_z r))).

(** [fn round_up_scaled(neg: bool, s: &Scaled) -> f64], where
    [f64::MIN], [f64::INFINITY], [-0.0] and [f64::from_bits(1)] are
    [min_f64], [infinity], [B754_zero true] and [from_bits 1]. *)
Definition round_up_scaled (neg : bool) (s : Scaled) : option f64 :=
  match s with
  | Huge => Some (if neg then min_f64 else infinity)
  | Tiny => Some (if neg then B754_zero true else from_bits 1)
  | Mid q e sticky => Generic.round_up_exact neg q e sticky
  end.

(** [fn rational_to_f64(x: &Rat, infsup: InfSup) -> F64], where
    [x.num.is_zero()] is [NatLimbs.is_zero_z (rat_num x)], [0.0] is
    [zero], [-round_up_scaled(..)] is [opp], [up != down] is
    [negb (eq up down)], and [f.is_infinite()] is [f64_is_infinite f]. *)
Definition rational_to_f64 (x : Rat) (infsup : InfSup) : option F64 :=
  if NatLimbs.is_zero_z (rat_num x) then
    Some {| f64_f := zero; f64_inexact := false; f64_overflow := false |}
  else
    let* s := scale x in
    let* up := round_up_scaled (rat_neg x) s in
    let* down := round_up_scaled (negb (rat_neg x)) s in
    let down := opp down in
    let f := match infsup with Inf => down | Sup => up end in
    Some {| f64_f := f; f64_inexact := negb (eq up down); f64_overflow := f64_is_infinite f |}.

(** [fn number_to_f64(n: &Number, infsup: InfSup) -> F64], where
    [f64::NEG_INFINITY] and [f64::INFINITY] are [B754_infinity true] and
    [B754_infinity false]. *)
Definition number_to_f64 (n : Number) (infsup : InfSup) : option F64 :=
  match n with
  | NegInfinity =>
      Some {| f64_f := B754_infinity true; f64_inexact := false; f64_overflow := false |}
  | Rational r => rational_to_f64 r infsup
  | Infinity =>
      Some {| f64_f := B754_infinity false; f64_inexact := false; f64_overflow := false |}
  end.

(** The functions of [src/format/digits.rs] that give the digits of a
    finite nonzero bound of an interval that [src/format.rs] prints,
    rounded in the direction of the bound: [fixed] for [{}] of [Display],
    [sci] for [{:e}] of [LowerExp] and [hex] for [{:x}] of [LowerHex], as an
    integer [d] and an exponent [k] of the radix, 10 or 2. The rest of
    [src/format.rs], which writes the text of [d] and [k] with
    [Nat::to_dec], the point, the zeros, the exponent and the sign, and
    the text of zeros and infinities, is not modelled. As in the section
    above, each [Nat] is the [Z] that it holds, with the limbs
    [NatLimbs.to_limbs] of that [Z], and each of its operations is the loop
    of [NatLimbs] on those limbs, through its wrapper on [Z]s. [usize] is
    [u64], as the feature [gmp] is supported only on 64-bit targets. *)

Definition radix10 : radix := Build_radix 10 eq_refl.
Definition radix16 : radix := Build_radix 16 eq_refl.

(** [fn decompose(x: f64) -> (u64, i64)], where [!(1 << 63)] of a [u64]
    is [2 ^ 63 - 1]. *)
Definition format_decompose (x : f64) : option (Z * Z) :=
  let c := Z.land (to_bits x) (2 ^ 63 - 1) in
  let be := Z.shiftr c 52 in
  let m := Z.land c (Z.shiftl 1 52 - 1) in
  let* m := if be =? 0 then Some m else checked_u 64 (m + Z.shiftl 1 52) in
  (* [be.max(1) as i64] *)
  let b := (Z.max be 1 + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63 in
  let* e := checked_i 64 (b - 1075) in
  Some (m, e).

(** [fn exact_dec(x: f64) -> (Nat, i64)], where [Nat::from_u64(m)],
    [&m << s], [&a * &b] and [Nat::pow5(k)] are [NatLimbs.from_u64_z m],
    [NatLimbs.shl_z m s], [NatLimbs.mul_z a b] and [NatLimbs.pow5_z k]. *)
Definition format_exact_dec (x : f64) : option (Z * Z) :=
  let* (m, e) := format_decompose x in
  let m := NatLimbs.from_u64_z m in
  if 0 <=? e then
    (* [e as u64] *)
    Some (NatLimbs.shl_z m (e mod 2 ^ 64), 0)
  else
    let* ne := checked_i 64 (- e) in
    (* [-e as u32] *)
    let* p := NatLimbs.pow5_z (ne mod 2 ^ 32) in
    let* n := NatLimbs.mul_z m p in
    Some (n, e).

(** [fn away(x: f64, up: bool) -> bool], where [x.is_sign_negative()] is
    [Bsign x], as [x] is not NaN here, and [a != b] is [negb (Bool.eqb a b)]. *)
Definition format_away (x : f64) (up : bool) : bool := negb (Bool.eqb (Bsign x) up).

(** [fn cut_dec(n: Nat, s: i64, t: i64, away: bool) -> (Nat, i64)], where
    [Nat::pow5(k)], [&a << s], [n.div_rem(&b)], which panics for [b = 0],
    [r.is_zero()], [&a + &b] and [Nat::from_u64(x)] are
    [NatLimbs.pow5_z k], [NatLimbs.shl_z a s], [NatLimbs.div_rem_z n b],
    [NatLimbs.is_zero_z r], [NatLimbs.add_z a b] and
    [NatLimbs.from_u64_z x], and [u64::from] keeps the value. *)
Definition format_cut_dec (n s t : Z) (away : bool) : option (Z * Z) :=
  if t <=? s then Some (n, s) else
  let* ts := checked_i 64 (t - s) in
  (* [(t - s) as u32] *)
  let j := ts mod 2 ^ 32 in
  let* p := NatLimbs.pow5_z j in
  let* (q, r) := NatLimbs.div_rem_z n (NatLimbs.shl_z p j) in
  if away && negb (NatLimbs.is_zero_z r) then Some (NatLimbs.add_z q (NatLimbs.from_u64_z 1), t)
  else Some (q, t).

(** [fn fixed(x: f64, p: usize, up: bool) -> (Nat, i64)], where
    [ALL_DIGITS] is 1100. *)
Definition format_fixed (x : f64) (p : Z) (up : bool) : option (Z * Z) :=
  let* (n, s) := format_exact_dec x in
  (* [p.min(ALL_DIGITS) as i64] *)
  let c := (Z.min p 1100 + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63 in
  let* t := checked_i 64 (- c) in
  format_cut_dec n s t (format_away x up).

(** [fn sci(x: f64, p: usize, up: bool) -> (Nat, i64)], where
    [n.digits10()] is [NatLimbs.digits10_z n]. *)
Definition format_sci (x : f64) (p : Z) (up : bool) : option (Z * Z) :=
  let* (n, s) := format_exact_dec x in
  let* dg := NatLimbs.digits10_z n in
  (* [n.digits10() as i64] *)
  let dg := (dg + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63 in
  let* t1 := checked_i 64 (dg + s) in
  let* t2 := checked_i 64 (t1 - 1) in
  (* [p.min(ALL_DIGITS) as i64] *)
  let c := (Z.min p 1100 + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63 in
  let* t := checked_i 64 (t2 - c) in
  format_cut_dec n s t (format_away x up).

(** [fn cut_bin(m: u64, j: u32, away: bool) -> u64] *)
Definition format_cut_bin (m j : Z) (away : bool) : option Z :=
  let* q := shr 64 m j in
  (* [m & ((1 << j) - 1) != 0] is only evaluated if [away]. *)
  let* inexact :=
    if away then
      let* p := shl 64 1 j in
      let* mask := checked_u 64 (p - 1) in
      Some (negb (Z.land m mask =? 0))
    else Some false in
  if inexact then checked_u 64 (q + 1) else Some q.

(** [fn hex(x: f64, p: Option<usize>, up: bool) -> (u64, i64)], where
    [i64::from] keeps the value, and [ex.rem_euclid(4)] and
    [ex.div_euclid(4)] are [ex mod 4] and [ex / 4]. *)
Definition format_hex (x : f64) (p : option Z) (up : bool) : option (Z * Z) :=
  let* (m, e) := format_decompose x in
  let* lz := checked_u 32 (leading_zeros 64 m - 11) in
  let* m53 := shl 64 m lz in
  let* ex1 := checked_i 64 (e + 52) in
  let* ex := checked_i 64 (ex1 - lz) in
  let away := format_away x up in
  if match p with Some p0 => p0 =? 0 | None => false end then
    let* d := format_cut_bin m53 49 away in
    let* k := checked_i 64 (ex - 3) in
    Some (d, k)
  else
    let* d14 := shl 64 m53 (ex mod 4) in
    let* k1 := checked_i 64 (4 * (ex / 4)) in
    let* k := checked_i 64 (k1 - 52) in
    match p with
    | Some p0 =>
        if p0 <? 13 then
          (* [p as u32] *)
          let* j1 := checked_u 32 (13 - p0 mod 2 ^ 32) in
          let* j := checked_u 32 (4 * j1) in
          let* d := format_cut_bin d14 j away in
          let* k' := checked_i 64 (k + j) in
          Some (d, k')
        else Some (d14, k)
    | None => Some (d14, k)
    end.

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

(** The other constants of [Interval] in [src/constants.rs], from [E] to
    [TAU]. Each is [const_interval!(a, b)] for two decimal literals [a] and
    [b], which rustc rounds to the nearest [f64]s. They are given here by
    the bit patterns of those [f64]s, below a comment that gives [a] and
    [b]. The test [tests/model_constants.rs] checks that the definitions
    below are those of these constants, each once, that their bit patterns
    are those of the bounds of the Rust constants, and that [a] and [b] in
    the comment above each round to nearest to them. It reads only a
    definition in the form [Definition C : Interval :=] at the start of a
    line, with [const_interval (from_bits 0x...) (from_bits 0x...).] on the
    next line, right below a comment whose text is
    [pub const C: Self = const_interval!(a, b)] in square brackets, on one
    line or more, so keep each in that form. *)

(** [pub const E: Self = const_interval!(2.718281828459045, 2.7182818284590455)] *)
Definition E : Interval :=
  const_interval (from_bits 0x4005bf0a8b145769) (from_bits 0x4005bf0a8b14576a).

(** [pub const FRAC_1_PI: Self =
    const_interval!(0.31830988618379064, 0.3183098861837907)] *)
Definition FRAC_1_PI : Interval :=
  const_interval (from_bits 0x3fd45f306dc9c882) (from_bits 0x3fd45f306dc9c883).

(** [pub const FRAC_1_SQRT_2: Self =
    const_interval!(0.7071067811865475, 0.7071067811865476)] *)
Definition FRAC_1_SQRT_2 : Interval :=
  const_interval (from_bits 0x3fe6a09e667f3bcc) (from_bits 0x3fe6a09e667f3bcd).

(** [pub const FRAC_2_PI: Self =
    const_interval!(0.6366197723675813, 0.6366197723675814)] *)
Definition FRAC_2_PI : Interval :=
  const_interval (from_bits 0x3fe45f306dc9c882) (from_bits 0x3fe45f306dc9c883).

(** [pub const FRAC_2_SQRT_PI: Self =
    const_interval!(1.1283791670955126, 1.1283791670955128)] *)
Definition FRAC_2_SQRT_PI : Interval :=
  const_interval (from_bits 0x3ff20dd750429b6d) (from_bits 0x3ff20dd750429b6e).

(** [pub const FRAC_PI_2: Self =
    const_interval!(1.5707963267948966, 1.5707963267948968)] *)
Definition FRAC_PI_2 : Interval :=
  const_interval (from_bits 0x3ff921fb54442d18) (from_bits 0x3ff921fb54442d19).

(** [pub const FRAC_PI_3: Self =
    const_interval!(1.0471975511965976, 1.0471975511965979)] *)
Definition FRAC_PI_3 : Interval :=
  const_interval (from_bits 0x3ff0c152382d7365) (from_bits 0x3ff0c152382d7366).

(** [pub const FRAC_PI_4: Self =
    const_interval!(0.7853981633974483, 0.7853981633974484)] *)
Definition FRAC_PI_4 : Interval :=
  const_interval (from_bits 0x3fe921fb54442d18) (from_bits 0x3fe921fb54442d19).

(** [pub const FRAC_PI_6: Self =
    const_interval!(0.5235987755982988, 0.5235987755982989)] *)
Definition FRAC_PI_6 : Interval :=
  const_interval (from_bits 0x3fe0c152382d7365) (from_bits 0x3fe0c152382d7366).

(** [pub const FRAC_PI_8: Self =
    const_interval!(0.39269908169872414, 0.3926990816987242)] *)
Definition FRAC_PI_8 : Interval :=
  const_interval (from_bits 0x3fd921fb54442d18) (from_bits 0x3fd921fb54442d19).

(** [pub const LN_10: Self = const_interval!(2.3025850929940455, 2.302585092994046)] *)
Definition LN_10 : Interval :=
  const_interval (from_bits 0x40026bb1bbb55515) (from_bits 0x40026bb1bbb55516).

(** [pub const LN_2: Self = const_interval!(0.6931471805599453, 0.6931471805599454)] *)
Definition LN_2 : Interval :=
  const_interval (from_bits 0x3fe62e42fefa39ef) (from_bits 0x3fe62e42fefa39f0).

(** [pub const LOG10_2: Self =
    const_interval!(0.30102999566398114, 0.3010299956639812)] *)
Definition LOG10_2 : Interval :=
  const_interval (from_bits 0x3fd34413509f79fe) (from_bits 0x3fd34413509f79ff).

(** [pub const LOG10_E: Self =
    const_interval!(0.4342944819032518, 0.43429448190325187)] *)
Definition LOG10_E : Interval :=
  const_interval (from_bits 0x3fdbcb7b1526e50e) (from_bits 0x3fdbcb7b1526e50f).

(** [pub const LOG2_10: Self =
    const_interval!(3.321928094887362, 3.3219280948873626)] *)
Definition LOG2_10 : Interval :=
  const_interval (from_bits 0x400a934f0979a371) (from_bits 0x400a934f0979a372).

(** [pub const LOG2_E: Self =
    const_interval!(1.4426950408889634, 1.4426950408889636)] *)
Definition LOG2_E : Interval :=
  const_interval (from_bits 0x3ff71547652b82fe) (from_bits 0x3ff71547652b82ff).

(** [pub const PI: Self = const_interval!(3.141592653589793, 3.1415926535897936)] *)
Definition PI : Interval :=
  const_interval (from_bits 0x400921fb54442d18) (from_bits 0x400921fb54442d19).

(** [pub const SQRT_2: Self = const_interval!(1.414213562373095, 1.4142135623730951)] *)
Definition SQRT_2 : Interval :=
  const_interval (from_bits 0x3ff6a09e667f3bcc) (from_bits 0x3ff6a09e667f3bcd).

(** [pub const TAU: Self = const_interval!(6.283185307179586, 6.283185307179587)] *)
Definition TAU : Interval :=
  const_interval (from_bits 0x401921fb54442d18) (from_bits 0x401921fb54442d19).

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
    [src/parse.rs], with [Ok(x)] as [Some (Some x)], the [Err] as
    [Some None], and a panic as [None].
    [unwrap_or(Self::EMPTY)] is the [match]. *)
Definition try_from_ninterval_exact (x : NInterval) : option (option Interval) :=
  let* a := number_to_f64 (ninf x) Inf in
  let* b := number_to_f64 (nsup x) Sup in
  let x := match try_from (f64_f a) (f64_f b) with Some x => x | None => EMPTY end in
  Some (if f64_inexact a || f64_inexact b then None else Some x).

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

(** [pub fn interior(self, rhs: Self) -> bool] in [src/boolean.rs], whose
    [||] and [&&] give the same values as Rocq's. *)
Definition interior (self rhs : Interval) : bool :=
  let l :=
    is_empty self || lt (sup_raw self) (sup_raw rhs) ||
    Generic.all
      (Generic.eq (Generic.shuffle13 (rep self) (rep rhs)) (Generic.splat infinity)) in
  let r :=
    is_empty self || lt (inf_raw rhs) (inf_raw self) ||
    Generic.all
      (Generic.eq (Generic.shuffle02 (rep self) (rep rhs)) (Generic.splat infinity)) in
  l && r.

(** [pub fn subset(self, rhs: Self) -> bool] in [src/boolean.rs], whose [|]
    on [bool]s gives the same value as [||]. *)
Definition subset (self rhs : Interval) : bool :=
  is_empty self || Generic.all (Generic.le (rep self) (rep rhs)).

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

(** [pub(crate) fn zero() -> Self]. [zero], [sqr], [mul], [mul_add], the
    divisions, [recip] and [div] come last, as [zero], [mul], [mul_add] and
    [div] shadow the [zero], [mul], [mul_add] and [div] on floats, and
    [classify], [abs], [sign] and [sqrt] above use that [zero]. [sqr] and
    [div] come after [zero], which they call. *)
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

(** [pub fn mul_add(self, rhs: Self, addend: Self) -> Self] in
    [src/basic.rs]. Its [mul_add_ru] calls [mul_add_ru_impl::<HAS_FMA>], so
    [has_fma] is an argument, as for [mul], and the variants of
    [IntervalClass2] are as in [mul]. The [return] is the value of an [if]
    whose [else] holds the rest of the body. *)
Definition mul_add (has_fma : bool) (self rhs addend : Interval) : option Interval :=
  if is_empty addend then Some EMPTY
  else
    let* c := classify2 self rhs in
    match c with
    | (CE, CE) | (CE, CM) | (CE, CN0) | (CE, CN1) | (CE, CP0) | (CE, CP1)
    | (CE, CZ) | (CM, CE) | (CN0, CE) | (CN1, CE) | (CP0, CE) | (CP1, CE)
    | (CZ, CE) =>
        Some EMPTY
    | (CM, CZ) | (CN0, CZ) | (CN1, CZ) | (CP0, CZ) | (CP1, CZ) | (CZ, CM)
    | (CZ, CN0) | (CZ, CN1) | (CZ, CP0) | (CZ, CP1) | (CZ, CZ) =>
        Some addend
    | (CM, CM) =>
        let x := Generic.shuffle02 (rep self) (rep self) in
        let y := Generic.swap (rep rhs) in
        let* xy := Generic.mul_add_ru has_fma x y (rep addend) in
        let z := Generic.shuffle13 (rep self) (rep self) in
        let w := rep rhs in
        let* zw := Generic.mul_add_ru has_fma z w (rep addend) in
        let r := Generic.max xy zw in
        Some {| rep := r |}
    | (CM, CN0) | (CM, CN1) =>
        let x := Generic.swap (rep self) in
        let y := Generic.shuffle02 (rep rhs) (rep rhs) in
        let* r := Generic.mul_add_ru has_fma x y (rep addend) in
        Some {| rep := r |}
    | (CM, CP0) | (CM, CP1) =>
        let x := rep self in
        let y := Generic.shuffle13 (rep rhs) (rep rhs) in
        let* r := Generic.mul_add_ru has_fma x y (rep addend) in
        Some {| rep := r |}
    | (CN0, CM) | (CN1, CM) =>
        let x := Generic.shuffle02 (rep self) (rep self) in
        let y := Generic.swap (rep rhs) in
        let* r := Generic.mul_add_ru has_fma x y (rep addend) in
        Some {| rep := r |}
    | (CN0, CN0) | (CN0, CN1) | (CN1, CN0) | (CN1, CN1) =>
        let x := Generic.swap (rep self) in
        let x := Generic.neg0 x in
        let y := Generic.swap (rep rhs) in
        let* r := Generic.mul_add_ru has_fma x y (rep addend) in
        Some {| rep := r |}
    | (CN0, CP0) | (CN0, CP1) | (CN1, CP0) | (CN1, CP1) =>
        let x := rep self in
        let y := Generic.neg0 (rep rhs) in
        let y := Generic.swap y in
        let* r := Generic.mul_add_ru has_fma x y (rep addend) in
        Some {| rep := r |}
    | (CP0, CM) | (CP1, CM) =>
        let x := Generic.shuffle13 (rep self) (rep self) in
        let y := rep rhs in
        let* r := Generic.mul_add_ru has_fma x y (rep addend) in
        Some {| rep := r |}
    | (CP0, CN0) | (CP0, CN1) | (CP1, CN0) | (CP1, CN1) =>
        let x := Generic.neg0 (rep self) in
        let x := Generic.swap x in
        let y := rep rhs in
        let* r := Generic.mul_add_ru has_fma x y (rep addend) in
        Some {| rep := r |}
    | (CP0, CP0) | (CP0, CP1) | (CP1, CP0) | (CP1, CP1) =>
        let x := rep self in
        let y := Generic.neg0 (rep rhs) in
        let* r := Generic.mul_add_ru has_fma x y (rep addend) in
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

(** *** The elementary functions of [src/elementary.rs]

    [pt] gives the functions of [src/mpfr_calls.rs] that compute bounds
    (see the record [point]), [-1.0] is [opp (of_u64 1)], as in [sign],
    and [0.0] is
    the float [Model.zero], i.e. +0, which [zero] shadows here. *)

(** The functions [$f_impl] and [$f] that [impl_log!] defines, for its
    [$f_rd] and [$f_ru] as [f_rd] and [f_ru].
    [const_interval!(0.0, f64::INFINITY)] is
    [const_interval Model.zero (B754_infinity false)], and the
    [return] is the value of an [if] whose [else] holds the rest of the
    body. [$f] returns the first element of the pair that [$f_impl]
    returns. *)
Definition log_impl (f_rd f_ru : f64 -> f64) (self : Interval) :
    Interval * Decoration :=
  let DOM := const_interval Model.zero (B754_infinity false) in
  let x := intersection self DOM in
  let a := inf_raw x in
  let b := sup_raw x in
  if is_empty x || le b Model.zero then (EMPTY, Trv)
  else
    let y := with_infsup_raw (f_rd a) (f_ru b) in
    let d := if interior self DOM then Com else Trv in
    (y, d).

(** The function [$f] that [impl_mono_inc!] defines, for its [$f_rd] and
    [$f_ru] as [f_rd] and [f_ru]. The [return] is the value of an [if]
    whose [else] holds the rest of the body. *)
Definition mono_inc (f_rd f_ru : f64 -> f64) (self : Interval) : Interval :=
  if is_empty self then self
  else with_infsup_raw (f_rd (inf_raw self)) (f_ru (sup_raw self)).

(** [fn acos_impl(self) -> (Self, Decoration)] and
    [pub fn acos(self) -> Self], with [return] as in [log_impl]. *)
Definition acos_impl (pt : point) (self : Interval) : Interval * Decoration :=
  let DOM := const_interval (opp (of_u64 1)) (of_u64 1) in
  let x := intersection self DOM in
  if is_empty x then (x, Trv)
  else
    let y := with_infsup_raw (acos_rd pt (sup_raw x)) (acos_ru pt (inf_raw x)) in
    let d := if subset self DOM then Com else Trv in
    (y, d).
Definition acos (pt : point) (self : Interval) : Interval := fst (acos_impl pt self).

(** [fn acosh_impl(self) -> (Self, Decoration)] and
    [pub fn acosh(self) -> Self], with [f64::INFINITY] as
    [B754_infinity false] and [return] as in [log_impl]. *)
Definition acosh_impl (pt : point) (self : Interval) : Interval * Decoration :=
  let DOM := const_interval (of_u64 1) (B754_infinity false) in
  let x := intersection self DOM in
  if is_empty x then (x, Trv)
  else
    let y := with_infsup_raw (acosh_rd pt (inf_raw x)) (acosh_ru pt (sup_raw x)) in
    let d := if subset self DOM then Com else Trv in
    (y, d).
Definition acosh (pt : point) (self : Interval) : Interval := fst (acosh_impl pt self).

(** [fn asin_impl(self) -> (Self, Decoration)] and
    [pub fn asin(self) -> Self], with [return] as in [log_impl]. *)
Definition asin_impl (pt : point) (self : Interval) : Interval * Decoration :=
  let DOM := const_interval (opp (of_u64 1)) (of_u64 1) in
  let x := intersection self DOM in
  if is_empty x then (x, Trv)
  else
    let y := with_infsup_raw (asin_rd pt (inf_raw x)) (asin_ru pt (sup_raw x)) in
    let d := if subset self DOM then Com else Trv in
    (y, d).
Definition asin (pt : point) (self : Interval) : Interval := fst (asin_impl pt self).

(** [impl_mono_inc!(asinh, asinh_rd, asinh_ru)] and
    [impl_mono_inc!(atan, atan_rd, atan_ru)] *)
Definition asinh (pt : point) : Interval -> Interval :=
  mono_inc (asinh_rd pt) (asinh_ru pt).
Definition atan (pt : point) : Interval -> Interval :=
  mono_inc (atan_rd pt) (atan_ru pt).

(** [fn atan2_impl(self, rhs: Self) -> (Self, Decoration)] and
    [pub fn atan2(self, rhs: Self) -> Self]. [(x, y) = (rhs, self)], so the
    class of [rhs] comes first in [x.classify2(y)], which returns an
    [option], as these do too. The arms are in the order of the Rust code.
    [0.0] is the float [Model.zero], i.e. +0, [Self::zero()] is [zero],
    [-Self::PI.sup_raw()] is [opp (sup_raw PI)], and [-Self::FRAC_PI_2] is
    [neg FRAC_PI_2]. *)
Definition atan2_impl (pt : point) (self rhs : Interval) :
    option (Interval * Decoration) :=
  let x := rhs in
  let y := self in
  let a := inf_raw x in
  let b := sup_raw x in
  let c := inf_raw y in
  let d := sup_raw y in
  let* cl := classify2 x y in
  Some
    match cl with
    | (CE, CE) | (CE, CM) | (CE, CN0) | (CE, CN1) | (CE, CP0) | (CE, CP1)
    | (CE, CZ) | (CM, CE) | (CN0, CE) | (CN1, CE) | (CP0, CE) | (CP1, CE)
    | (CZ, CE) | (CZ, CZ) =>
        (EMPTY, Trv)
    | (CM, CM) | (CM, CN0) | (CN0, CM) | (CN0, CN0) =>
        (with_infsup_raw (opp (sup_raw PI)) (sup_raw PI), Trv)
    (* First quadrant *)
    | (CP0, CP0) => (with_infsup_raw Model.zero (sup_raw FRAC_PI_2), Trv)
    | (CP0, CP1) | (CP1, CP0) | (CP1, CP1) | (CP1, CZ) | (CZ, CP1) =>
        (with_infsup_raw (atan2_rd pt c b) (atan2_ru pt d a), Com)
    (* First & second quadrant *)
    | (CM, CP0) | (CM, CZ) => (with_infsup_raw Model.zero (sup_raw PI), Trv)
    | (CM, CP1) => (with_infsup_raw (atan2_rd pt c b) (atan2_ru pt c a), Com)
    (* Second quadrant *)
    | (CN0, CP0) => (with_infsup_raw (inf_raw FRAC_PI_2) (sup_raw PI), Trv)
    | (CN0, CP1) | (CN1, CP1) =>
        (with_infsup_raw (atan2_rd pt d b) (atan2_ru pt c a), Com)
    | (CN1, CP0) => (with_infsup_raw (atan2_rd pt d b) (sup_raw PI), Dac)
    (* Second & third quadrant *)
    | (CN1, CM) | (CN1, CN0) =>
        (with_infsup_raw (opp (sup_raw PI)) (sup_raw PI), Def)
    (* Third quadrant *)
    | (CN0, CN1) | (CN1, CN1) =>
        (with_infsup_raw (atan2_rd pt d a) (atan2_ru pt c b), Com)
    (* Third & fourth quadrant *)
    | (CM, CN1) => (with_infsup_raw (atan2_rd pt d a) (atan2_ru pt d b), Com)
    (* Fourth quadrant *)
    | (CP0, CN0) => (with_infsup_raw (opp (sup_raw FRAC_PI_2)) Model.zero, Trv)
    | (CP0, CN1) | (CP1, CN0) | (CP1, CN1) | (CZ, CN1) =>
        (with_infsup_raw (atan2_rd pt c a) (atan2_ru pt d b), Com)
    (* Fourth & first quadrant *)
    | (CP0, CM) | (CZ, CM) =>
        (with_infsup_raw (opp (sup_raw FRAC_PI_2)) (sup_raw FRAC_PI_2), Trv)
    | (CP1, CM) => (with_infsup_raw (atan2_rd pt c a) (atan2_ru pt d a), Com)
    (* X axis *)
    | (CN0, CZ) => (PI, Trv)
    | (CN1, CZ) => (PI, Dac)
    | (CP0, CZ) => (zero, Trv)
    (* Y axis *)
    | (CZ, CN0) => (neg FRAC_PI_2, Trv)
    | (CZ, CP0) => (FRAC_PI_2, Trv)
    end.
Definition atan2 (pt : point) (self rhs : Interval) : option Interval :=
  let* p := atan2_impl pt self rhs in
  Some (fst p).

(** [fn atanh_impl(self) -> (Self, Decoration)] and
    [pub fn atanh(self) -> Self], with [return] as in [log_impl]. *)
Definition atanh_impl (pt : point) (self : Interval) : Interval * Decoration :=
  let DOM := const_interval (opp (of_u64 1)) (of_u64 1) in
  let x := intersection self DOM in
  let a := inf_raw x in
  let b := sup_raw x in
  if is_empty x || le b (opp (of_u64 1)) || ge a (of_u64 1) then (EMPTY, Trv)
  else
    let y := with_infsup_raw (atanh_rd pt a) (atanh_ru pt b) in
    let d := if interior self DOM then Com else Trv in
    (y, d).
Definition atanh (pt : point) (self : Interval) : Interval := fst (atanh_impl pt self).

(** [fn floors_exact(a: f64, b: f64, qa: f64, qb: f64, c: Interval) ->
    bool] in [src/elementary.rs]. Its [/] is [div], so [has_fma] is an
    argument and the result an [option], [f64::floor] is [ffloor], and
    Rust's [&&] does not evaluate its right side, with the second [div],
    when the left one is false. *)
Definition floors_exact (has_fma : bool) (a b qa qb : f64) (c : Interval) :
    option bool :=
  let* za := div has_fma (with_infsup_raw a a) c in
  if Model.eq (ffloor (sup_raw za)) qa then
    let* zb := div has_fma (with_infsup_raw b b) c in
    Some (Model.eq (ffloor (inf_raw zb)) qb)
  else Some false.

(** [pub fn cos(self) -> Self]. Its [self / Self::PI] is [div] and its
    [(..).floor()] is [floor] of intervals, so [has_fma] is an argument, as
    for [div], and the result is an [option], [None] where [div] would be.
    [x.max(y)] and [x.min(y)] are [fmax first x y] and [fmin first x y],
    which pick the same argument only if the two compare equal; there is at
    most one such call on each path, so one [first] covers every choice
    Rust may make. [a == b], [n == 0.0] and the like are [Model.eq],
    [n <= 1.0] is [Model.le], [qb - qa] is [Model.sub], [0.0] is
    [Model.zero], [1.0] is [of_u64 1] and [-1.0] is [opp (of_u64 1)]
    ([Model.] avoids the [sub] and [zero] of intervals). [return] is as in
    [log_impl]. The [(q, n)] that the branches test is the one above if
    [exact] holds, and otherwise one from [quadrants], as in Rust: [b - a >= 8.0]
    is [Model.le (of_u64 8) (Model.sub b a)], [(qa / 2.0).floor()] is
    [ffloor (Model.div qa (of_u64 2))], [qa % 2.0] is
    [frem qa (of_u64 2)], and Rust's [||] does not evaluate
    [floors_exact], whose [div]s make it an [option], when a test before it
    holds, so it is under an [if]. *)
Definition cos (pt : point) (has_fma first : bool) (self : Interval) :
    option Interval :=
  if is_empty self then Some self
  else
    let a := inf_raw self in
    let b := sup_raw self in
    let* q_nowrap0 := div has_fma self PI in
    let q_nowrap := floor q_nowrap0 in
    let qa := inf_raw q_nowrap in
    let qb := sup_raw q_nowrap in
    let n := if Model.eq a b then Model.zero else Model.sub qb qa in
    let q := rem_euclid_2 qa in
    let* exact :=
      if Model.eq n Model.zero || Model.le (of_u64 8) (Model.sub b a) then Some true
      else floors_exact has_fma a b qa qb PI in
    let '(q, n) :=
      if exact then (q, n)
      else
        let '(qa, n) := quadrants pt a b in
        (ffloor (Model.div qa (of_u64 2)),
         ffloor (Model.div (Model.add (frem qa (of_u64 2)) n) (of_u64 2))) in
    if Model.eq n Model.zero then
      if Model.eq q Model.zero then Some (with_infsup_raw (cos_rd pt b) (cos_ru pt a))
      else Some (with_infsup_raw (cos_rd pt a) (cos_ru pt b))
    else if Model.le n (of_u64 1) then
      if Model.eq q Model.zero then
        Some (with_infsup_raw (opp (of_u64 1)) (fmax first (cos_ru pt a) (cos_ru pt b)))
      else Some (with_infsup_raw (fmin first (cos_rd pt a) (cos_rd pt b)) (of_u64 1))
    else Some (const_interval (opp (of_u64 1)) (of_u64 1)).

(** [pub fn cosh(self) -> Self], with [1.0] as [of_u64 1],
    [(-a).max(b)] as [fmax first (opp a) b], where [-a] and [b] are not
    NaN, and [return] as in [log_impl]. *)
Definition cosh (pt : point) (first : bool) (self : Interval) : Interval :=
  if is_empty self then self
  else
    let a := inf_raw self in
    let b := sup_raw self in
    if lt b Model.zero then with_infsup_raw (cosh_rd pt b) (cosh_ru pt a)
    else if gt a Model.zero then with_infsup_raw (cosh_rd pt a) (cosh_ru pt b)
    else with_infsup_raw (of_u64 1) (cosh_ru pt (fmax first (opp a) b)).

(** [impl_mono_inc!(exp, exp_rd, exp_ru)] and those for [exp10] and
    [exp2] *)
Definition exp (pt : point) : Interval -> Interval := mono_inc (exp_rd pt) (exp_ru pt).
Definition exp10 (pt : point) : Interval -> Interval :=
  mono_inc (exp10_rd pt) (exp10_ru pt).
Definition exp2 (pt : point) : Interval -> Interval :=
  mono_inc (exp2_rd pt) (exp2_ru pt).

(** [impl_log!(ln, ln_impl, ln_rd, ln_ru)] and those for [log10] and
    [log2] *)
Definition ln_impl (pt : point) : Interval -> Interval * Decoration :=
  log_impl (ln_rd pt) (ln_ru pt).
Definition ln (pt : point) (self : Interval) : Interval := fst (ln_impl pt self).
Definition log10_impl (pt : point) : Interval -> Interval * Decoration :=
  log_impl (log10_rd pt) (log10_ru pt).
Definition log10 (pt : point) (self : Interval) : Interval := fst (log10_impl pt self).
Definition log2_impl (pt : point) : Interval -> Interval * Decoration :=
  log_impl (log2_rd pt) (log2_ru pt).
Definition log2 (pt : point) (self : Interval) : Interval := fst (log2_impl pt self).

(** [fn pow_impl(self, rhs: Self) -> (Self, Decoration)] and
    [pub fn pow(self, rhs: Self) -> Self]. [DOM] is
    [const_interval!(0.0, f64::INFINITY)], [0.0] and [1.0] are the floats
    [Model.zero], i.e. +0, and [of_u64 1], and [Self::zero()] is [zero].
    Each [return] is the value of an [if] whose [else] holds the rest of
    the body. [z_ad.min(z_bc)] and [z_ac.max(z_bd)] are [fmin first_min]
    and [fmax first_max], with one argument each, as they are two calls
    on the same path. *)
Definition pow_impl (pt : point) (first_min first_max : bool) (self rhs : Interval) :
    Interval * Decoration :=
  let DOM := const_interval Model.zero (B754_infinity false) in
  let x := intersection self DOM in
  if either_empty x rhs then (EMPTY, Trv)
  else
    let a := inf_raw x in
    let b := sup_raw x in
    let c := inf_raw rhs in
    let d := sup_raw rhs in
    if Model.le d Model.zero then
      if Model.eq b Model.zero then (EMPTY, Trv)
      else
        let dec := if interior self DOM then Com else Trv in
        if Model.lt b (of_u64 1) then
          (with_infsup_raw (pow_rd pt b d) (pow_ru pt a c), dec)
        else if Model.gt a (of_u64 1) then
          (with_infsup_raw (pow_rd pt b c) (pow_ru pt a d), dec)
        else (with_infsup_raw (pow_rd pt b c) (pow_ru pt a c), dec)
    else if Model.gt c Model.zero then
      let dec := if subset self DOM then Com else Trv in
      if Model.lt b (of_u64 1) then
        (with_infsup_raw (pow_rd pt a d) (pow_ru pt b c), dec)
      else if Model.gt a (of_u64 1) then
        (with_infsup_raw (pow_rd pt a c) (pow_ru pt b d), dec)
      else (with_infsup_raw (pow_rd pt a d) (pow_ru pt b d), dec)
    else if Model.eq b Model.zero then (zero, Trv)
    else
      let z_ac := pow_ru pt a c in
      let z_ad := pow_rd pt a d in
      let z_bc := pow_rd pt b c in
      let z_bd := pow_ru pt b d in
      let dec := if interior self DOM then Com else Trv in
      (with_infsup_raw (fmin first_min z_ad z_bc) (fmax first_max z_ac z_bd), dec).
Definition pow (pt : point) (first_min first_max : bool) (self rhs : Interval) :
    Interval :=
  fst (pow_impl pt first_min first_max self rhs).

(** [fn powi_impl(self, rhs: i32) -> (Self, Decoration)] and
    [pub fn powi(self, rhs: i32) -> Self], with [rhs] as the integer [n],
    [rhs < 0] as [Z.ltb n 0] and [rhs % 2 == 0] as [Z.rem n 2 =? 0], since
    Rust's [%] on integers rounds the quotient toward zero, as [Z.rem]
    does. [abs] returns an [option], so these do too. [0.0] and [-0.0]
    are the floats [Model.zero] and [opp Model.zero], and the assignments
    to [a] and [b] are [let]s. Each [return] is the value of an [if] whose
    [else] holds the rest of the body. *)
Definition powi_impl (pt : point) (n : Z) (self : Interval) :
    option (Interval * Decoration) :=
  if is_empty self then Some (self, Trv)
  else
    let a := inf_raw self in
    let b := sup_raw self in
    if Z.ltb n 0 then
      let d := if Model.le a Model.zero && Model.ge b Model.zero then Trv else Com in
      if Model.eq a Model.zero && Model.eq b Model.zero then Some (EMPTY, d)
      else if Z.eqb (Z.rem n 2) 0 then
        let* abs := abs self in
        Some (with_infsup_raw (pown_rd pt (sup_raw abs) n) (pown_ru pt (inf_raw abs) n), d)
      else if Model.lt a Model.zero && Model.gt b Model.zero then Some (ENTIRE, d)
      else
        let a := if Model.eq a Model.zero then Model.zero else a in
        let b := if Model.eq b Model.zero then opp Model.zero else b in
        Some (with_infsup_raw (pown_rd pt b n) (pown_ru pt a n), d)
    else if Z.eqb (Z.rem n 2) 0 then
      let* abs := abs self in
      Some (with_infsup_raw (pown_rd pt (inf_raw abs) n) (pown_ru pt (sup_raw abs) n), Com)
    else Some (with_infsup_raw (pown_rd pt a n) (pown_ru pt b n), Com).
Definition powi (pt : point) (n : Z) (self : Interval) : option Interval :=
  let* p := powi_impl pt n self in
  Some (fst p).

(** [pub fn sin(self) -> Self], written as [cos] is, with
    [qa.rem_euclid(4.0)] as [rem_euclid qa (of_u64 4)] and [n < 1.0] as
    [Model.lt]. Rust's [&&] binds tighter than its [||], as Rocq's do. *)
Definition sin (pt : point) (has_fma first : bool) (self : Interval) :
    option Interval :=
  if is_empty self then Some self
  else
    let a := inf_raw self in
    let b := sup_raw self in
    let* q_nowrap0 := div has_fma self FRAC_PI_2 in
    let q_nowrap := floor q_nowrap0 in
    let qa := inf_raw q_nowrap in
    let qb := sup_raw q_nowrap in
    let n := if Model.eq a b then Model.zero else Model.sub qb qa in
    let q := rem_euclid qa (of_u64 4) in
    let* exact :=
      if Model.eq n Model.zero || Model.le (of_u64 8) (Model.sub b a) then Some true
      else floors_exact has_fma a b qa qb FRAC_PI_2 in
    let '(q, n) := if exact then (q, n) else quadrants pt a b in
    if Model.eq q Model.zero && Model.lt n (of_u64 1)
       || Model.eq q (of_u64 3) && Model.lt n (of_u64 2) then
      Some (with_infsup_raw (sin_rd pt a) (sin_ru pt b))
    else if Model.eq q (of_u64 1) && Model.lt n (of_u64 2)
            || Model.eq q (of_u64 2) && Model.lt n (of_u64 1) then
      Some (with_infsup_raw (sin_rd pt b) (sin_ru pt a))
    else if Model.eq q Model.zero && Model.lt n (of_u64 3)
            || Model.eq q (of_u64 3) && Model.lt n (of_u64 4) then
      Some (with_infsup_raw (fmin first (sin_rd pt a) (sin_rd pt b)) (of_u64 1))
    else if Model.eq q (of_u64 1) && Model.lt n (of_u64 4)
            || Model.eq q (of_u64 2) && Model.lt n (of_u64 3) then
      Some (with_infsup_raw (opp (of_u64 1)) (fmax first (sin_ru pt a) (sin_ru pt b)))
    else Some (const_interval (opp (of_u64 1)) (of_u64 1)).

(** [impl_mono_inc!(sinh, sinh_rd, sinh_ru)] *)
Definition sinh (pt : point) : Interval -> Interval :=
  mono_inc (sinh_rd pt) (sinh_ru pt).

(** [fn tan_impl(self) -> (Self, Decoration)] and [pub fn tan(self) ->
    Self], written as [cos] and [sin] are. *)
Definition tan_impl (pt : point) (has_fma : bool) (self : Interval) :
    option (Interval * Decoration) :=
  if is_empty self then Some (self, Trv)
  else
    let a := inf_raw self in
    let b := sup_raw self in
    let* q_nowrap0 := div has_fma self FRAC_PI_2 in
    let q_nowrap := floor q_nowrap0 in
    let qa := inf_raw q_nowrap in
    let qb := sup_raw q_nowrap in
    let n := if Model.eq a b then Model.zero else Model.sub qb qa in
    let q := rem_euclid_2 qa in
    let* exact :=
      if Model.eq n Model.zero || Model.le (of_u64 4) (Model.sub b a) then Some true
      else floors_exact has_fma a b qa qb FRAC_PI_2 in
    let '(q, n) :=
      if exact then (q, n)
      else
        let '(qa, n) := quadrants pt a b in
        (frem qa (of_u64 2), n) in
    if Model.eq q Model.zero && Model.lt n (of_u64 1)
       || Model.eq q (of_u64 1) && Model.lt n (of_u64 2) then
      Some (with_infsup_raw (tan_rd pt a) (tan_ru pt b), Com)
    else Some (ENTIRE, Trv).
Definition tan (pt : point) (has_fma : bool) (self : Interval) : option Interval :=
  let* p := tan_impl pt has_fma self in
  Some (fst p).

(** [impl_mono_inc!(tanh, tanh_rd, tanh_ru)] *)
Definition tanh (pt : point) : Interval -> Interval :=
  mono_inc (tanh_rd pt) (tanh_ru pt).

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
    [FromStr] for [DecInterval] calls, with the argument as [x] and its
    fields as [nx x] and [nd x]. [unwrap_or(Interval::EMPTY)] is the
    [match], and [d.min(Decoration::Dac)] is [dec_min (nd x) Dac]. [None]
    is a panic. *)
Definition from_dec_ninterval (x : DecNInterval) : option DecInterval :=
  let* a := number_to_f64 (ninf (nx x)) Inf in
  let* b := number_to_f64 (nsup (nx x)) Sup in
  let y :=
    match Interval.try_from (f64_f a) (f64_f b) with
    | Some y => y
    | None => Interval.EMPTY
    end in
  let d := if f64_overflow a || f64_overflow b then dec_min (nd x) Dac else nd x in
  Some (set_dec y d).

(** [fn from(x: NInterval) -> Self] of [impl From<NInterval> for Interval]
    in [src/parse.rs], which [FromStr] for [Interval] calls:
    [DecInterval::from(DecNInterval::new(x)).x()]. [None] is a panic. *)
Definition from_ninterval (x : NInterval) : option Interval :=
  let* y := from_dec_ninterval (dn_new x) in
  Some (itv y).

(** [pub const ENTIRE: Self] *)
Definition ENTIRE : DecInterval := new_unchecked Interval.ENTIRE Dac.

(** A constant that [def_com!(C)] in [src/constants.rs] defines,
    [new_unchecked(Interval::C, Decoration::Com)], where [Interval::C] is
    [const_interval!(a, b)] for two float literals [a] and [b]. Whatever
    made [Interval::C], [def_com!(C)] compiles only if it passes the
    assertion [def_com_ok] below, and then it is [const_interval a b] for
    finite floats [a] and [b] ([def_com_ok_bounds] in [ComCommon.v]). *)
Definition def_com (a b : f64) : DecInterval :=
  new_unchecked (Interval.const_interval a b) Com.

(** [f64::NEG_INFINITY < -na && -na <= b && b < f64::INFINITY] for the
    lanes [[na; b]] of [Interval::C], which [def_com!(C)] [transmute]s into
    an array and asserts in a [const], so that it does not compile unless
    this is [true]. Its [&&] gives the same value as Rocq's. *)
Definition def_com_ok (x : Interval) : bool :=
  let (na, b) := rep x in
  lt (B754_infinity true) (opp na) && le (opp na) b && lt b (B754_infinity false).

(** [def_com!(E)] to [def_com!(TAU)] in [src/constants.rs]:
    [pub const C: Self = { const _: () = { ... }; Self::new_unchecked(Interval::C, Decoration::Com) }]
    for each constant [C] of [Interval] other than [EMPTY] and [ENTIRE],
    where the [const] item asserts [def_com_ok Interval.C] and makes no
    interval. Each is [def_com a b], up to unfolding, where [Interval.C] is
    [const_interval a b]. *)
Definition E : DecInterval := new_unchecked Interval.E Com.
Definition FRAC_1_PI : DecInterval := new_unchecked Interval.FRAC_1_PI Com.
Definition FRAC_1_SQRT_2 : DecInterval := new_unchecked Interval.FRAC_1_SQRT_2 Com.
Definition FRAC_2_PI : DecInterval := new_unchecked Interval.FRAC_2_PI Com.
Definition FRAC_2_SQRT_PI : DecInterval := new_unchecked Interval.FRAC_2_SQRT_PI Com.
Definition FRAC_PI_2 : DecInterval := new_unchecked Interval.FRAC_PI_2 Com.
Definition FRAC_PI_3 : DecInterval := new_unchecked Interval.FRAC_PI_3 Com.
Definition FRAC_PI_4 : DecInterval := new_unchecked Interval.FRAC_PI_4 Com.
Definition FRAC_PI_6 : DecInterval := new_unchecked Interval.FRAC_PI_6 Com.
Definition FRAC_PI_8 : DecInterval := new_unchecked Interval.FRAC_PI_8 Com.
Definition LN_10 : DecInterval := new_unchecked Interval.LN_10 Com.
Definition LN_2 : DecInterval := new_unchecked Interval.LN_2 Com.
Definition LOG10_2 : DecInterval := new_unchecked Interval.LOG10_2 Com.
Definition LOG10_E : DecInterval := new_unchecked Interval.LOG10_E Com.
Definition LOG2_10 : DecInterval := new_unchecked Interval.LOG2_10 Com.
Definition LOG2_E : DecInterval := new_unchecked Interval.LOG2_E Com.
Definition PI : DecInterval := new_unchecked Interval.PI Com.
Definition SQRT_2 : DecInterval := new_unchecked Interval.SQRT_2 Com.
Definition TAU : DecInterval := new_unchecked Interval.TAU Com.

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
    [pub fn min(self, rhs: Self) -> Self], where [self.d().min(rhs.d())] is
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

(** [pub fn sqr(self) -> Self], where [self.x().sqr()] is
    [Interval.sqr has_fma (itv self)], with the [has_fma] of
    [Interval.sqr] as an argument here too. *)
Definition sqr (has_fma : bool) (self : DecInterval) : option DecInterval :=
  if is_nai self then Some self
  else
    let* x := Interval.sqr has_fma (itv self) in
    Some (set_dec x (dec self)).

(** [pub fn sqrt(self) -> Self], where [self.x().sqrt()] is
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

(** [fn neg(self) -> Self] of [impl Neg for DecInterval], where [-self.x()]
    is [Interval.neg (itv self)]. [neg], [add], [sub], [mul], [mul_add],
    [recip] and [div] come last, so that the [sub] in [round] and
    [round_ties_even] is still the one on floats, and [mul], [mul_add] and
    [div] shadow the ones on floats in no other definition. *)
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
    [self.x() * rhs.x()] is [Interval.mul has_fma (itv self) (itv rhs)], with
    the [has_fma] of [Interval.mul] as an argument here too. *)
Definition mul (has_fma : bool) (self rhs : DecInterval) : option DecInterval :=
  if is_nai self || is_nai rhs then Some NAI
  else
    let* x := Interval.mul has_fma (itv self) (itv rhs) in
    Some (set_dec x (dec_min (dec self) (dec rhs))).

(** [pub fn mul_add(self, rhs: Self, addend: Self) -> Self], where
    [self.x().mul_add(rhs.x(), addend.x())] is
    [Interval.mul_add has_fma (itv self) (itv rhs) (itv addend)], with the
    [has_fma] of [Interval.mul_add] as an argument here too, and
    [self.d().min(rhs.d().min(addend.d()))] is
    [dec_min (dec self) (dec_min (dec rhs) (dec addend))]. *)
Definition mul_add (has_fma : bool) (self rhs addend : DecInterval) :
    option DecInterval :=
  if is_nai self || is_nai rhs || is_nai addend then Some NAI
  else
    let* x := Interval.mul_add has_fma (itv self) (itv rhs) (itv addend) in
    Some (set_dec x (dec_min (dec self) (dec_min (dec rhs) (dec addend)))).

(** [pub fn recip(self) -> Self], where [self.x().recip()] is
    [Interval.recip has_fma (itv self)], with the [has_fma] of
    [Interval.recip] as an argument here too, and [0.0] is +0. *)
Definition recip (has_fma : bool) (self : DecInterval) : option DecInterval :=
  if is_nai self then Some self
  else
    let d := if Interval.contains (itv self) zero then Trv else dec self in
    let* x := Interval.recip has_fma (itv self) in
    Some (set_dec x d).

(** [fn div(self, rhs: Self) -> Self] of [impl Div for DecInterval], where
    [self.x() / rhs.x()] is [Interval.div has_fma (itv self) (itv rhs)], with
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
    [self.x().mul_rev_to_pair(numerator.x())] is
    [Interval.mul_rev_to_pair has_fma (itv self) (itv numerator)], with the
    [has_fma] of [Interval.mul_rev_to_pair] as an argument here too, the
    arrays as pairs, as there, [self.d().min(numerator.d())] as
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
    [self.x().cancel_minus(rhs.x())] is
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

(** *** The elementary functions of [src/elementary.rs] *)

(** The function [$f] that [impl_dec!($f)] in [src/elementary.rs] defines,
    for [Interval::$f] as [f]. Unlike [impl_dec] above, which is the macro
    of [src/integer.rs], it does not test for NaI: [set_dec] returns NaI
    for the decoration [Ill]. *)
Definition elem_dec (f : Interval -> Interval) (self : DecInterval) :
    DecInterval :=
  set_dec (f (itv self)) (dec self).

(** The function [$f] that [impl_dec!($f, $f_impl)] in
    [src/elementary.rs] defines, for [Interval::$f_impl] as [f_impl]. *)
Definition elem_dec_impl (f_impl : Interval -> Interval * Decoration)
    (self : DecInterval) : DecInterval :=
  let '(y, d) := f_impl (itv self) in
  set_dec y (dec_min (dec self) d).

(** [impl_dec!(acos, acos_impl)] and the other uses of [impl_dec!] in
    [src/elementary.rs], but those for [cos], [sin] and [tan], which are
    after [cosh]. [pt] is as in [Interval], and [first] in [cosh] is that of
    [Interval.cosh]. *)
Definition acos (pt : point) := elem_dec_impl (Interval.acos_impl pt).
Definition acosh (pt : point) := elem_dec_impl (Interval.acosh_impl pt).
Definition asin (pt : point) := elem_dec_impl (Interval.asin_impl pt).
Definition asinh (pt : point) := elem_dec (Interval.asinh pt).
Definition atan (pt : point) := elem_dec (Interval.atan pt).
Definition atanh (pt : point) := elem_dec_impl (Interval.atanh_impl pt).
Definition cosh (pt : point) (first : bool) := elem_dec (Interval.cosh pt first).

(** [impl_dec!(cos)], [impl_dec!(sin)] and [impl_dec!(tan, tan_impl)], as
    [elem_dec] and [elem_dec_impl] but for interval functions that return
    an [option], with [has_fma] and [first] those of [Interval.cos] and
    [Interval.sin]. *)
Definition cos (pt : point) (has_fma first : bool) (self : DecInterval) :
    option DecInterval :=
  let* y := Interval.cos pt has_fma first (itv self) in
  Some (set_dec y (dec self)).
Definition sin (pt : point) (has_fma first : bool) (self : DecInterval) :
    option DecInterval :=
  let* y := Interval.sin pt has_fma first (itv self) in
  Some (set_dec y (dec self)).
Definition tan (pt : point) (has_fma : bool) (self : DecInterval) :
    option DecInterval :=
  let* p := Interval.tan_impl pt has_fma (itv self) in
  Some (set_dec (fst p) (dec_min (dec self) (snd p))).

Definition exp (pt : point) := elem_dec (Interval.exp pt).
Definition exp10 (pt : point) := elem_dec (Interval.exp10 pt).
Definition exp2 (pt : point) := elem_dec (Interval.exp2 pt).
Definition ln (pt : point) := elem_dec_impl (Interval.ln_impl pt).
Definition log10 (pt : point) := elem_dec_impl (Interval.log10_impl pt).
Definition log2 (pt : point) := elem_dec_impl (Interval.log2_impl pt).

(** The function [$f] that [impl_dec2!($f, $f_impl)] in
    [src/elementary.rs] defines, for [Interval::$f_impl] as [f_impl]. Like
    [elem_dec_impl], it does not test for NaI. *)
Definition elem_dec2_impl (f_impl : Interval -> Interval -> Interval * Decoration)
    (self rhs : DecInterval) : DecInterval :=
  let '(z, d) := f_impl (itv self) (itv rhs) in
  set_dec z (dec_min (dec self) (dec_min (dec rhs) d)).

(** [impl_dec2!(atan2, atan2_impl)], as [elem_dec2_impl] but for
    [Interval.atan2_impl], which returns an [option]. *)
Definition atan2 (pt : point) (self rhs : DecInterval) : option DecInterval :=
  let* p := Interval.atan2_impl pt (itv self) (itv rhs) in
  Some (set_dec (fst p) (dec_min (dec self) (dec_min (dec rhs) (snd p)))).

(** [impl_dec2!(pow, pow_impl)], with [first_min] and [first_max] those
    of [Interval.pow_impl]. *)
Definition pow (pt : point) (first_min first_max : bool) :=
  elem_dec2_impl (Interval.pow_impl pt first_min first_max).

(** [pub fn powi(self, rhs: i32) -> Self], with [rhs] as the integer [n],
    and an [option] as [Interval.powi_impl] returns one. *)
Definition powi (pt : point) (n : Z) (self : DecInterval) : option DecInterval :=
  let* p := Interval.powi_impl pt n (itv self) in
  Some (set_dec (fst p) (dec_min (dec self) (snd p))).
Definition sinh (pt : point) := elem_dec (Interval.sinh pt).
Definition tanh (pt : point) := elem_dec (Interval.tanh pt).

End DecInterval.
