# Proofs of the portable backend

Machine-checked proofs, in [Rocq](https://rocq-prover.org) with the [Flocq](https://flocq.gitlabpages.inria.fr) library, that parts of [`src/simd/generic.rs`](../src/simd/generic.rs) round correctly, and that `abs`, `floor`, `ceil`, `max`, `min`, `recip`, `round`, `round_ties_even`, `sign`, `sqr`, `sqrt`, `trunc`, `-x`, `x + y`, `x - y`, `x * y` and `x / y` of intervals and decorated intervals, built on it, return what IEEE 1788 asks of them, that every decorated interval that the library makes is `com` only if its interval is nonempty and bounded, and that every interval that the library's constructors make, or that these operations, `convex_hull` and `intersection` compute from such intervals, is `valid`.

## What is proved

`add_ru_correct` in [`AddRu.v`](theories/AddRu.v):

```coq
Theorem add_ru_correct : forall x y,
  Generic.add_ru x y =
    Some (Bplus mode_UP (fst x) (fst y), Bplus mode_UP (snd x) (snd y)).
```

For all inputs, both lanes of `add_ru` are IEEE 754 binary64 addition rounded toward +∞. This includes the sign of a zero result, overflow, the infinities and NaN. The specification `Bplus mode_UP` is Flocq's. With the modelling choices below, `Some` also means that `add_ru` does not panic.

It follows from the theorems for the two paths that `lanewise2` chooses between:

```coq
Theorem add1_ru_fast_correct : forall x y,
  snd (Generic.add1_ru_fast x y) = true ->
  fst (Generic.add1_ru_fast x y) = Bplus mode_UP x y.

Theorem add1_ru_slow_correct : forall x y,
  Generic.add1_ru_slow x y = Some (Bplus mode_UP x y).
```

`sub_ru_correct` and `sub1_ru_correct` in [`SubRu.v`](theories/SubRu.v) do the same for subtraction rounded toward +∞, Flocq's `Bminus mode_UP`:

```coq
Theorem sub_ru_correct : forall x y,
  Generic.sub_ru x y =
    Some (Bminus mode_UP (fst x) (fst y), Bminus mode_UP (snd x) (snd y)).

Theorem sub1_ru_correct : forall x y,
  Generic.sub1_ru x y = Some (Bminus mode_UP x y).
```

`sub_ru` and `sub1_ru` add `-y` with the functions above. Flocq defines `Bminus` by its own case analysis, and `Bminus_Bplus_Bopp` shows that it agrees with `Bplus` of `Bopp y`.

`mul_ru_correct` in [`MulRu.v`](theories/MulRu.v) does the same for multiplication rounded toward +∞, Flocq's `Bmult mode_UP`, both with an FMA and without one:

```coq
Theorem mul_ru_correct : forall has_fma x y,
  Generic.mul_ru has_fma x y =
    Some (Bmult mode_UP (fst x) (fst y), Bmult mode_UP (snd x) (snd y)).

Theorem mul1_ru_fast_correct : forall fma x y,
  snd (Generic.mul1_ru_fast fma x y) = true ->
  fst (Generic.mul1_ru_fast fma x y) = Bmult mode_UP x y.

Theorem mul1_ru_tiny_correct : forall fma x y,
  Generic.mul1_ru_tiny fma x y = Some (Bmult mode_UP x y).

Theorem mul1_ru_slow_correct : forall x y,
  Generic.mul1_ru_slow x y = Some (Bmult mode_UP x y).
```

`has_fma` is `HAS_FMA`, which depends on the target. With an FMA, `two_prod_err` computes the error of the product with `mul_add`, and without one with Dekker's TwoProduct. The fast path accepts `x` and `y` if either is zero or not finite, and otherwise only if `RN(x * y)` is at least `2^-968` in magnitude and finite, and without an FMA also below `2^1023`, with both factors below `2^996`. `lanewise2` sends the lanes that it rejects, whose `x` and `y` are finite and nonzero, to `mul1_ru_tiny`. For finite, nonzero `x` and `y` with `|RN(x * y)| < 2^-968`, `mul1_ru_tiny` returns `2^-1074` or -0 by the sign of `RN(x * y)` if that is zero, and otherwise scales `x` by `2^128`, rounds the scaled product upward on the fast path, which accepts it with either value of `FMA`, and rounds that divided by `2^128` upward. That is `x * y` rounded upward, as rounding upward twice through the scaled product is rounding upward once (`RU_scaled` in [`MulRuTiny.v`](theories/MulRuTiny.v)). The theorem also shows that the `debug_assert!` that the fast path accepts the scaled product never fails. Every other input goes to `mul1_ru_slow`, which multiplies the significands as integers and rounds the product with `round_up_exact`. `mul_ru_impl_correct` states the same for `mul_ru_impl::<FMA>`, which the differential tests call with both values of `FMA`.

`div_ru_correct` in [`DivRu.v`](theories/DivRu.v) does the same for division rounded toward +∞, Flocq's `Bdiv mode_UP`, including division by zero, both with an FMA and without one:

```coq
Theorem div_ru_correct : forall has_fma x y,
  Generic.div_ru has_fma x y =
    Some (Bdiv mode_UP (fst x) (fst y), Bdiv mode_UP (snd x) (snd y)).

Theorem div1_ru_fast_correct : forall fma x y,
  snd (Generic.div1_ru_fast fma x y) = true ->
  fst (Generic.div1_ru_fast fma x y) = Bdiv mode_UP x y.

Theorem div1_ru_slow_correct : forall x y,
  Generic.div1_ru_slow x y = Some (Bdiv mode_UP x y).
```

The fast path computes `q = RN(x / y)` and the remainder `r = x - q * y`, and steps `q` up if `r` is nonzero and has the sign of `y`, which is exactly when `q < x / y`. If `x` or `y` is zero or not finite, `q` is already the result. Otherwise the fast path is valid only if `q` is normal and `|x| >= 2^-967`, so that `r` is a float. Where it is valid, the code computes `r` exactly, with `mul_add`, or without an FMA with Dekker's TwoProduct and Sterbenz's lemma. The slow path divides the significands as integers and rounds the quotient with `round_up_exact`, with a nonzero remainder as the sticky bit. `div_ru_impl_correct` states the same for `div_ru_impl::<FMA>`.

`sqrt_rd_ru_correct` in [`SqrtRdRu.v`](theories/SqrtRdRu.v) does the same for the square root, rounded toward -∞ in the first lane and toward +∞ in the second, Flocq's `Bsqrt mode_DN` and `Bsqrt mode_UP`, both with an FMA and without one:

```coq
Theorem sqrt_rd_ru_correct : forall has_fma x,
  Generic.sqrt_rd_ru has_fma x = Some (Bsqrt mode_DN (fst x), Bsqrt mode_UP (snd x)).

Theorem sqrt1_rd_correct : forall has_fma x,
  Generic.sqrt1_rd has_fma x = Some (Bsqrt mode_DN x).

Theorem sqrt1_ru_correct : forall has_fma x,
  Generic.sqrt1_ru has_fma x = Some (Bsqrt mode_UP x).
```

`sqrt1_fast` computes `s = RN(√x)` and the remainder `r = x - s * s`. `sqrt1_rd_impl` steps `s` down if `r < 0`, and `sqrt1_ru_impl` steps it up if `r > 0`. `sqrt1_fast` accepts `x` if `-966 <= exponent(x) <= 1023`, or `<= 1021` without an FMA. For a positive `x`, `r` is then a float, and the code computes it exactly, as for division. For a negative `x`, `s`, `r` and the result are NaN. `sqrt1_slow` scales any other positive finite `x` into that range by `2^128` or `2^-128`, and the rounded square root of the scaled input back by `2^-64` or `2^64`, all exactly. For ±0, ±∞, NaN and the other negative numbers, it returns `x.sqrt()`, which does not depend on the rounding mode. `sqrt1_rd_impl_correct` and `sqrt1_ru_impl_correct` state the same for `sqrt1_rd_impl::<FMA>` and `sqrt1_ru_impl::<FMA>` whenever their models may make a nested call through `sqrt1_slow`: one is always enough.

`mul_add_ru_correct` in [`MulAddRu.v`](theories/MulAddRu.v) does the same for the fused multiply-add rounded toward +∞, Flocq's `Bfma mode_UP`, both with an FMA and without one:

```coq
Theorem mul_add_ru_correct : forall has_fma x y z,
  Generic.mul_add_ru has_fma x y z =
    Some (Bfma mode_UP (fst x) (fst y) (fst z),
          Bfma mode_UP (snd x) (snd y) (snd z)).

Theorem mul_add1_ru_fast_correct : forall fma a b c,
  snd (Generic.mul_add1_ru_fast fma a b c) = true ->
  fst (Generic.mul_add1_ru_fast fma a b c) = Bfma mode_UP a b c.

Theorem mul_add1_ru_slow_correct : forall a b c,
  Generic.mul_add1_ru_slow a b c = Some (Bfma mode_UP a b c).
```

The fast path computes `r1 = RN(a * b + c)`, with `mul_add`, or without an FMA with `mul_add1_rn_emulated`, and the sign of its error with ErrFma [BM11] (see `generic.rs`), and steps `r1` up if the error is positive. If an input is not finite, or `a` or `b` is zero, both paths return `mul_add1_special(a, b, c)`, which computes `a * b + c` rounded to nearest, the same as toward +∞ for these inputs. Otherwise, if `c` is zero, the slow path rounds `a * b` with `mul1_ru_slow`. If not, it adds the exact product of the significands to `c` and rounds the sum with `sum_round_up`, as `add1_ru_slow` does for two floats. `lanewise2` takes only two arguments, so `mul_add_ru_impl` chooses between the paths itself, in the same way. `mul_add_ru_impl_correct` states the same for `mul_add_ru_impl::<FMA>`.

`floor_correct` in [`Integer.v`](theories/Integer.v) shows that `Interval::floor` returns the tightest interval that contains the image of its argument under `floor`, and `dec_floor_correct` that `DecInterval::floor` decorates it with the decoration that IEEE 1788 asks for:

```coq
Theorem floor_correct : forall x,
  valid x -> is_hull (image Rfloor x) (Interval.floor x).

Theorem dec_floor_correct : forall x, valid (itv x) ->
  if DecInterval.is_nai x then DecInterval.floor x = x
  else
    is_hull (image Rfloor (itv x)) (itv (DecInterval.floor x)) /\
    exists d, strongest d Rfloor (itv x) /\
      dec (DecInterval.floor x) = dec_min d (dec x).
```

`ceil_correct` and `dec_ceil_correct` state the same for `ceil`, with `Rceil`. `valid x` says that `x` is empty or `[a, b]` with `a <= b`, `a != +∞` and `b != -∞`, the bounds that `TryFrom<(f64, f64)>` accepts. `is_hull s y` says that the reals in `y` are exactly those between two elements of `s`, so no interval with `f64` bounds that contains `s` is smaller. `strongest d f x` says that the property of the decoration `d` holds for `f` on `x`, and that of no stronger decoration does. The result is decorated with the minimum of `d` and the decoration of `x`. A NaI is returned unchanged. The properties are those of IEEE 1788, with Stdlib's `continuity_pt` and `continue_in` for continuity, so where `floor` and `ceil` are continuous is proved, not assumed.

`Interval::floor` and `Interval::ceil` negate the first lane of `[-a; b]`, round both lanes in the same direction, and negate the first lane back. Section `Round` proves for any such rounding of floats that keeps ±∞ and NaN, is nondecreasing on the reals and moves a real by less than 1, that this gives the hull of the image, and that `impl_dec!` decorates it correctly if the decoration that it picks with `is_singleton` and its test `is_not_com` is the strongest one. `floor` is discontinuous exactly at the integers. If `floor(a) = floor(b)` for a bounded `[a, b]`, the restriction of `floor` to `[a, b]` is constant, and `floor` is continuous at each point of `[a, b]` unless `a` is an integer, which is the test `x.inf_raw() == y.inf_raw()`. For `ceil`, the test is on `b` instead.

`round_correct` and `dec_round_correct` in [`Round.v`](theories/Round.v) state the same for `round`, with `Rround`, and `round_ties_even_correct` and `dec_round_ties_even_correct` for `round_ties_even`, with `Rround_ties_even`. `trunc_correct` and `dec_trunc_correct` in [`Trunc.v`](theories/Trunc.v) state it for `trunc`, with `Rtrunc`. These are IEEE 1788's `roundTiesToAway`, `roundTiesToEven` and `trunc`, defined in [`Ieee1788.v`](theories/Ieee1788.v) with Flocq's `ZnearestA`, `ZnearestE` and `Ztrunc`.

`Interval::round`, `Interval::round_ties_even` and `Interval::trunc` round both lanes of `[-a; b]` as they are, without `neg0`. This gives the same result as negating the first lane, rounding it and negating it back, because the three roundings are odd on every float, signed zeros included: `round(-a) = -round(a)`. They also keep ±∞ and NaN, are nondecreasing on the reals and move a real by less than 1, so Section `Round` applies to them too.

`round` and `round_ties_even` are discontinuous exactly at the reals halfway between two integers, whichever way they break a tie. If `round(a) = round(b)` for a bounded `[a, b]`, the restriction of `round` to `[a, b]` is constant, and `round` is continuous at each point of `[a, b]` unless `a` or `b` is halfway between two integers. The test for that is `|a| - trunc(|a|) == 0.5`, and the same for `b`. Its subtraction is exact, as `trunc(|a|)` is 0 if `|a| < 1`, and otherwise between `|a| / 2` and `|a|`, so that Sterbenz's lemma applies (`is_half_test` in [`Nearest.v`](theories/Nearest.v)). The same holds for `round_ties_even`. `trunc` is discontinuous exactly at the nonzero integers. If `trunc(a) = trunc(b)` for a bounded `[a, b]`, `trunc` is continuous at each point of `[a, b]` unless `a` or `b` is a nonzero integer, which is the test `(x.inf_raw() != 0.0 && x.inf_raw() == y.inf_raw()) || (x.sup_raw() != 0.0 && x.sup_raw() == y.sup_raw())`.

`sign_correct` and `dec_sign_correct` in [`Sign.v`](theories/Sign.v) state the same for `sign`, with `Rsign`, which is -1 below 0, 0 at 0 and 1 above it, except that `dec_sign_correct` has one more hypothesis:

```coq
Theorem dec_sign_correct :
  forall x, valid (itv x) ->
  com_common x ->
  if DecInterval.is_nai x then DecInterval.sign x = x
  else
    is_hull (image Rsign (itv x)) (itv (DecInterval.sign x)) /\
    exists d, strongest d Rsign (itv x) /\
      dec (DecInterval.sign x) = dec_min d (dec x).
```

`Interval::sign` compares both lanes of `[-a; b]` with 0. It keeps `1.0` in the lanes above 0 and `-1.0` in those below, by `and`ing the constants with the masks of `gt` and `lt`, and combines the two with `or`, which leaves `0.0` in a lane that is neither. So each lane holds its own sign, `sign(-a) = -sign(a)` in the first and `sign(b)` in the second, and the result is `[sign(a), sign(b)]`. As `sign` is nondecreasing, that is the hull of the image. An infinite bound gives -1 or 1, which `sign` takes on the reals far enough out. `sign` is discontinuous exactly at 0. If `sign(a) = sign(b)` for a bounded `[a, b]`, the restriction of `sign` to `[a, b]` is constant, and `sign` is continuous at each point of `[a, b]` unless 0 is in it. With `sign(a) = sign(b)`, that is only `[0, 0]`, so the test is `x.inf_raw() == 0.0`.

The extra hypothesis, `com_common x`, says that `x` is `com` only if its interval is common, which every `DecInterval` that the library makes is (`ComCommon.v`, below). Unlike the roundings above, `sign` maps an unbounded interval on which it is constant, such as `[1, +∞]`, to a singleton, `[1, 1]`, for which `impl_dec!` picks `com`, where IEEE 1788 asks for `dac`, as `com` needs a bounded argument. Under the hypothesis, the decoration of `x` is not `com` there, and its minimum with `com` is the same as with `dac`.

`abs_correct` and `dec_abs_correct` in [`Abs.v`](theories/Abs.v) state the same for `abs`, with Stdlib's `Rabs`. `Interval::abs` matches on `classify`, which `transmute`s a `u8` into an `IntervalClass`. That is undefined behaviour unless the `u8` is the discriminant of a variant, and the model returns `None` then, so the theorems also state that the result is `Some`:

```coq
Theorem classify_defined :
  forall x, valid x -> exists c, Interval.classify x = Some c.

Theorem abs_correct :
  forall x, valid x ->
  exists y, Interval.abs x = Some y /\ is_hull (image Rabs x) y.
```

`classify` compares both lanes of `[-a; b]` with 0 by `ge` and `le`, and packs the four results into a code. Every comparison with NaN is false, so the empty interval gives 0, the code of `E`. Otherwise each lane is above, below or equal to 0. Of the nine combinations, six are the codes of the other variants, and the other three mean `a > b`, which `valid` rules out. `abs` returns `[a, b]` itself if `0 <= a`, the lanes swapped, `[-b, -a]`, if `a < 0` and `b <= 0`, and `[0, max(-a, b)]` if `a < 0 < b`, where neither lane is NaN or zero, so `max1` returns the larger. Each is the image of `[a, b]`. `abs` is continuous, and its result is bounded exactly when its argument is, so the strongest decoration is `trv` for the empty interval, `com` for a nonempty bounded one and `dac` for an unbounded one. `set_dec` returns `trv` for the empty interval, and otherwise keeps the decoration of the argument, except that it lowers `com` to `dac` for an unbounded result. That is the minimum of the strongest decoration and that of the argument in every case. So, unlike `dec_sign_correct`, `dec_abs_correct` has no extra hypothesis.

`max_correct` and `min_correct` in [`MaxMin.v`](theories/MaxMin.v) state the same for `max` and `min`, with Stdlib's `Rmax` and `Rmin`, and with `image2 f x y`, the image of the box `x × y` under `f`, in [`Ieee1788.v`](theories/Ieee1788.v):

```coq
Theorem max_correct :
  forall has_maximum x y, valid x -> valid y ->
  is_hull (image2 Rmax x y) (Interval.max has_maximum x y).
```

`has_maximum` is `HAS_MAXIMUM`, which depends on the backend. With `HAS_MAXIMUM` true, `Interval::max` of `[a, b]` and `[c, d]` takes `minimum` of the first lanes and `maximum` of the second, `[min(-a, -c); max(b, d)]`, which is `[max(a, c), max(b, d)]`. `Interval::min` takes `maximum` of the first lanes and `minimum` of the second. These return NaN in a lane where either argument is NaN, so an empty argument gives the empty interval, the hull of the empty image. Otherwise both lanes of each argument are finite or +∞, and on those `max1` and `min1` are `Rmax` and `Rmin`, with +∞ above every real. Two zeros give a zero of either sign, which is 0 either way. `max(r, t) <= s` exactly when `r <= s` and `t <= s`, and `s <= max(r, t)` exactly when `s <= r` or `s <= t`. So some point of the image is at most `s` exactly when `max(a, c) <= s`, and some point is at least `s` exactly when `s <= max(b, d)`, which makes `[max(a, c), max(b, d)]` the hull, and dually for `min`. An infinite bound needs no separate case. With `HAS_MAXIMUM` false, `Interval::max` and `Interval::min` return the empty interval if `either_empty`, and otherwise take `min` and `max` of the lanes where the other branch takes `minimum` and `maximum`. On lanes that are not NaN, `min1` and `max1` are `minimum1` and `maximum1`, so for valid arguments both branches return the same interval, lane for lane (`max_branches` and `min_branches` in `MaxMin.v`), and the theorems hold for either value.

`dec_max_correct` and `dec_min_correct` in [`DecMaxMin.v`](theories/DecMaxMin.v) state the decorations, with the extra hypothesis of `dec_sign_correct` for each argument:

```coq
Theorem dec_max_correct :
  forall has_maximum x y, valid (itv x) -> valid (itv y) ->
  com_common x ->
  com_common y ->
  if DecInterval.is_nai x then DecInterval.max has_maximum x y = x
  else if DecInterval.is_nai y then
    DecInterval.max has_maximum x y = DecInterval.NAI
  else
    is_hull (image2 Rmax (itv x) (itv y)) (itv (DecInterval.max has_maximum x y)) /\
    exists d,
      strongest2 d Rmax (itv x) (itv y) (itv (DecInterval.max has_maximum x y)) /\
      dec (DecInterval.max has_maximum x y) = dec_min d (dec_min (dec x) (dec y)).
```

A NaI first argument is returned unchanged, and a NaI second argument gives NaI. `strongest2` is `strongest` for a function of two reals, with the box `x × y` in place of `x` and continuity in R² in place of continuity in R. Its last argument is the computed interval, which `com` asks to be bounded (see "What is assumed"). The result is decorated with the minimum of `d` and the decorations of both arguments. `max` and `min` are continuous on R² and bounded on every bounded box, so the strongest decoration is `trv` if either argument is empty, `com` if both are nonempty and bounded, and `dac` otherwise. `set_dec_correct` in [`DecBinary.v`](theories/DecBinary.v) proves the rest once, for any function of two reals that is continuous on R², and for any result that is the tightest interval that contains the image (`is_tightest` below), as a hull is. It shows that `set_dec` of that result and the minimum `e` of the decorations of two `valid` arguments, neither of them NaI, keeps the result and decorates it with the minimum of `d` and `e`, if `e` is `com` only when a nonempty box with a bounded image is bounded. Section `Binary` in `DecMaxMin.v` applies it to any interval operation that returns the hull of the image, under the hypotheses of `dec_max_correct`.

The hypotheses are needed for the same reason as in `dec_sign_correct`: the hull of the image of an unbounded box can be common, as in `max([-∞, 1], [0, 2]) = [0, 2]`, and `set_dec` would keep `com` there if both arguments were `com`, where IEEE 1788 asks for `dac`.

`neg_correct` and `dec_neg_correct` in [`Neg.v`](theories/Neg.v) state the same as `floor_correct` and `dec_floor_correct` for `-x`, with Stdlib's `Ropp`. `Interval::neg` swaps the lanes of `[-a; b]` into `[b; -a]`, which stores `[-b, -a]`, the image of `[a, b]`, and computes nothing. Negation is continuous, and its result is bounded exactly when its argument is, so as for `abs`, `dec_neg_correct` has no extra hypothesis.

`add_correct` and `sub_correct` in [`AddSub.v`](theories/AddSub.v) show that `x + y` and `x - y` of intervals return the tightest interval that contains the image of the box `x × y` under Stdlib's `Rplus` and `Rminus`, and `dec_add_correct` and `dec_sub_correct` that the decorated versions decorate it as IEEE 1788 asks:

```coq
Theorem add_correct :
  forall x y, valid x -> valid y ->
  exists z, Interval.add x y = Some z /\ is_tightest (image2 Rplus x y) z.

Theorem dec_add_correct :
  forall x y, valid (itv x) -> valid (itv y) ->
  exists z, DecInterval.add x y = Some z /\
    if DecInterval.is_nai x || DecInterval.is_nai y then z = DecInterval.NAI
    else
      is_tightest (image2 Rplus (itv x) (itv y)) (itv z) /\
      exists d, strongest2 d Rplus (itv x) (itv y) (itv z) /\
        dec z = dec_min d (dec_min (dec x) (dec y)).
```

The image of `[a, b] × [c, d]` under `+` is `[a + c, b + d]`, whose bounds need not be floats, so the result is not its hull. `is_tightest s y` says that `y` is `valid`, contains `s`, and is contained in every `valid` interval that contains `s`. `Some` means that `add_ru` does not panic, as in `add_ru_correct`. `Interval::add` adds `[-a; b]` and `[-c; d]` with `add_ru`, which gives `[RU(-a - c); RU(b + d)]`. `add_lane` shows that `Bplus mode_UP` of two lanes that are finite or +∞ is the least float or +∞ at or above their sum: the sum rounded up if that does not overflow, +∞ if the sum overflows above, and `-f64::MAX` if it overflows below, as every float is at least `-f64::MAX`. A lane that is +∞ gives +∞. An empty argument gives NaN in both lanes, the empty interval. `Interval::sub` swaps the lanes of `y` first, so `x - y` is `x + (-y)`, and `sub_correct` follows from `add_correct` and `Neg.v`.

Unlike `max` and `min`, `+` and `-` need no hypothesis on the decorations of the arguments: if a nonempty box has a bounded image under `+`, the box is bounded, as `|r| <= |r + t| + |t|` for a `t` in `y`, and the same holds for `-`. But a sum can overflow where the image is bounded: `[f64::MAX, f64::MAX] + [f64::MAX, f64::MAX]` is `[f64::MAX, +∞]`, for which the strongest decoration is `dac`, as `com` asks for a bounded computed interval. This is why `strongest2` takes the computed interval.

`mul_correct` in [`Mul.v`](theories/Mul.v) shows that `x * y` of intervals returns the tightest interval that contains the image of the box `x × y` under Stdlib's `Rmult`, and `dec_mul_correct` that the decorated version decorates it as IEEE 1788 asks, with the extra hypothesis of `dec_max_correct` for each argument:

```coq
Theorem mul_correct :
  forall has_fma x y, valid x -> valid y ->
  exists z, Interval.mul has_fma x y = Some z /\ is_tightest (image2 Rmult x y) z.

Theorem dec_mul_correct :
  forall has_fma x y, valid (itv x) -> valid (itv y) ->
  com_common x ->
  com_common y ->
  exists z, DecInterval.mul has_fma x y = Some z /\
    if DecInterval.is_nai x || DecInterval.is_nai y then z = DecInterval.NAI
    else
      is_tightest (image2 Rmult (itv x) (itv y)) (itv z) /\
      exists d, strongest2 d Rmult (itv x) (itv y) (itv z) /\
        dec z = dec_min d (dec_min (dec x) (dec y)).
```

`has_fma` is the `HAS_FMA` that `mul_ru`, which `Interval::mul` calls, passes to `mul_ru_impl`, as in `mul_ru_correct`, and the theorems hold for both of its values. `Some` means that the `transmute`s in `classify` and `classify2` get the discriminant of a variant, and that `mul_ru` does not panic.

`Interval::mul` matches on `classify2`, which packs the classes of both arguments into one `u8` and `transmute`s it into an `IntervalClass2`, whose variant `X_Y` stands for the pair of classes `X` and `Y`. `classify2_pair` in [`Classify2.v`](theories/Classify2.v) shows that this gives the pair of the classes of the arguments whenever `classify` is defined on both, which `classify_defined` shows for `valid` intervals. The classes are `E`, the empty interval, `Z`, `[0, 0]`, `M`, `[a, b]` with `a < 0 < b`, `N0` and `N1`, with `a < b = 0` and `b < 0`, and `P0` and `P1`, with `0 = a < b` and `0 < a` (`classify_mem` in [`Classes.v`](theories/Classes.v)). `Interval::mul` takes the same branch for `N0` and `N1`, written `N` below, and for `P0` and `P1`, written `P`. `mul_correct` splits on the pair of classes and applies a lemma for each case: `mul_empty` and `mul_zero` in [`MulZero.v`](theories/MulZero.v) if a class is `E` or `Z`, `mul_MM` in [`MulMM.v`](theories/MulMM.v) if both are `M`, `mul_MN`, `mul_MP`, `mul_NM` and `mul_PM` in [`MulMRow.v`](theories/MulMRow.v) if one is, and `mul_NN`, `mul_NP`, `mul_PN` and `mul_PP` in [`MulNP.v`](theories/MulNP.v) if neither is. An empty argument gives the empty interval, as the image of a box with an empty side is empty. `[0, 0]` and a nonempty argument, in either order, give `Interval::zero()`, which holds `[+0; +0]`, i.e. `[0, 0]`, the tightest interval that contains the image `{0}`.

In the other cases, `tightest_lanes` in `AddSub.v` shows, as for `+`, that the result is the tightest interval if its second lane is the least float or +∞ at or above the largest product `r * t` of a real `r` of `x` and a real `t` of `y`, or +∞ if there is none, and its first lane the least at or above the largest negated product `-(r * t)`. `classify_lanes` in `Classes.v` shows what the class of a `valid` interval says about its lanes `[-a; b]`. [`MulTight.v`](theories/MulTight.v) shows which product of reals of two sets is the largest. [`MulLane.v`](theories/MulLane.v) shows that `Bmult mode_UP` of two lanes that are both finite, or both above 0, is the least float or +∞ at or above their product (`mul_lane_finite`, `mul_lane_pos`), where +∞ times a lane above 0 is +∞, and that `max1` of two such results is the least at or above the larger product (`max_least_lane`). `mul_ru` computes `Bmult mode_UP` in each lane (`mul_ru_correct`).

- `M × M`: the reals of each argument have both signs. The largest product is the larger of `(-a) * (-c)` and `b * d`, and the largest negated product the larger of `(-a) * d` and `b * (-c)` (`tight_mult_mixed`), all four products of two lanes above 0. `Interval::mul` computes the four with `mul_ru`, and takes `max` of the two in each lane.
- `M × N`, `M × P`, `N × M` and `P × M`: as `-(r * t) = (-r) * t = r * (-t)` and `r * t = (-r) * (-t)`, the largest product and the largest negated product are each the largest product of reals or negated reals of `x` and `y`, picked so that the factor from the argument in `N` or `P` is at least 0. That is the product of two lanes above 0 (`tight_mult_pos_r`, `tight_mult_pos_l`), which `Interval::mul` picks with `swap`, `shuffle02` and `shuffle13`.
- `N × N`, `N × P`, `P × N` and `P × P`: the reals of each argument have one sign, so `r * t` is `p * q` or `-(p * q)`, where `p` and `q` are the reals of `x` and `y`, or their negations, whichever are at least 0 (`image2_mult_opp_l`, `image2_mult_opp_r` and `image2_mult_opp_lr`). The largest `p * q` is the product of two lanes above 0 (`tight_mult_pos_r`). The largest `-(p * q)` is `-(m * n)` for the least `p` and `q`, `m` and `n` (`tight_mult_min`), which two finite lanes hold as `-m` and `-n`. `Interval::mul` negates one of them with `neg0`, so that their product is `-(m * n)`.

`Rmult_continuous` in `Mul.v` shows that `*` is continuous on R², so `set_dec_correct` in `DecBinary.v` gives the decorations if `e` is `com` only when a nonempty box with a bounded image is bounded. For `+` this holds whatever `e` is, but not for `*`: `[0, 0] × [1, +∞]` has the bounded image `{0}`. `[0, 0] * [1, +∞]` is `[0, 0]`, and `set_dec` would keep `com` there if both arguments were `com`, where IEEE 1788 asks for `dac`, as `com` needs a bounded box. So `dec_mul_correct` has the extra hypothesis of `dec_max_correct`, under which `[1, +∞]` is not `com`.

[`ComCommon.v`](theories/ComCommon.v) shows that this hypothesis of `dec_sign_correct`, `dec_max_correct`, `dec_min_correct` and `dec_mul_correct`, and of `dec_recip_correct` and `dec_div_correct` below, holds for every `DecInterval` that the library makes:

```coq
Definition com_common (x : DecInterval) : Prop :=
  dec x = Com -> Interval.is_common_interval (itv x) = true.
```

It proves `com_common` for each place that makes a `DecInterval`. The fields of `DecInterval` are `pub(crate)`, so only the library can make one with a struct expression, and the only such expression is the body of `new_unchecked`. The only `transmute` into a `DecInterval` is the one in `const_dec_interval!`, and no code assigns to a field. Anything else that returns a `DecInterval` returns one that it was given, or one made by these. The callers of `new_unchecked` are:

- `DecInterval::new`, which picks `com` only for a common interval (`new_com_common`).
- `set_dec`, which keeps `com` only for a common interval and lowers it to `dac` otherwise (`set_dec_com_common`). The theorem holds for any interval and decoration, so it covers every caller, such as `x * y`.
- The constants `EMPTY`, `NAI` and `ENTIRE`, which are `trv`, `ill` and `dac` (`constants_com_common`), and those that `def_com!` decorates `com`, whose bounds are finite (`def_com_com_common`).
- `convex_hull` and `intersection`, which return NaI or a `trv` interval (`set_op_com_common`).
- `try_from_be_bytes`, `try_from_le_bytes` and `try_from_ne_bytes`, which accept `com` only for bounds `a <= b` where `a` is not -∞ and `b` is not +∞ (`try_from_bytes_com_common`). `a <= b` excludes NaN, and then `a` = +∞ would force `b` = +∞, and `b` = -∞ would force `a` = -∞, so both bounds are finite.

`const_dec_interval!(a, b)` picks `com` only if `a` is not -∞ and `b` is not +∞, and does not compile unless `a <= b`, which makes both bounds finite too (`const_dec_interval_com_common`).

`sqrt_correct` in [`Sqrt.v`](theories/Sqrt.v) shows that `Interval::sqrt` returns the tightest interval that contains the image of its argument under the square root, which is defined only on `[0, +∞)`, and `dec_sqrt_correct` that `DecInterval::sqrt` decorates it as IEEE 1788 asks:

```coq
Theorem sqrt_correct :
  forall has_fma x, valid x ->
  exists y, Interval.sqrt has_fma x = Some y /\
    is_tightest (image_dom sqrt_dom sqrt x) y.

Theorem dec_sqrt_correct :
  forall has_fma x, valid (itv x) ->
  exists y, DecInterval.sqrt has_fma x = Some y /\
    if DecInterval.is_nai x then y = x
    else
      is_tightest (image_dom sqrt_dom sqrt (itv x)) (itv y) /\
      exists d, strongest_dom sqrt_dom d sqrt (itv x) (itv y) /\
        dec y = dec_min d (dec x).
```

`sqrt_dom` is the domain `[0, +∞)`, and `image_dom sqrt_dom sqrt x` the image of the reals of `x` in it under Stdlib's `sqrt`, so the image of `[-1, 1]` is `[0, 1]`. Stdlib's `sqrt` returns 0 below 0, but those values are not used. `strongest_dom` is `strongest` for a function with a domain, and takes the computed interval, as `strongest2` does. `has_fma` is the `HAS_FMA` that `sqrt1_ru` and `sqrt_rd_ru` pass to `sqrt1_ru_impl` and `sqrt1_rd_impl`, and the theorems hold for both of its values. `Some` means that `sqrt1_ru` and `sqrt_rd_ru` return, as in `sqrt_rd_ru_correct`.

The image of a nonempty `[a, b]` is empty if `b < 0`, and otherwise holds the reals between `√max(a, 0)` and `√b`, with no upper bound if `b` is +∞ (`sqrt_image`). As for `+`, those bounds need not be floats, so the result is the tightest interval rather than the hull, and `tightest_lanes` in `AddSub.v` reduces it to the lanes. `Interval::sqrt` returns the empty interval if `x` is empty or `b < 0`. Otherwise, if `a <= 0`, it stores `[-0; sqrt1_ru(b)]`, i.e. `[0, sqrt1_ru(b)]`, and if `a > 0`, `neg0` turns `[-a; b]` into `[a; b]`, `sqrt_rd_ru` takes the square root of the first lane rounded down and of the second rounded up, and `neg0` turns the result back. These are Flocq's `Bsqrt mode_DN` and `Bsqrt mode_UP` (`sqrt1_ru_correct`, `sqrt_rd_ru_correct`). The square root of a finite float at least 0 is below `2^512`, so it stays finite when rounded up or down. So the second lane is `√b` rounded up, or +∞ if `b` is, the least float or +∞ at or above `√b`, and the first lane, `-0` or `-RD(√a)`, is the least float at or above `-√max(a, 0)`.

IEEE 1788 counts `sqrt` as continuous at each point of its domain, 0 included, so continuity is relative to the domain. The strongest decoration is `trv` if `x` is empty or has a real below 0, which, for a nonempty `x`, is when `a < 0`, `com` if `0 <= a` and `b` is finite, and `dac` if `0 <= a` and `b` is +∞, as `com` needs a bounded `x`. `DecInterval::sqrt` passes `trv` to `set_dec` if `a < 0`, and the decoration of `x` otherwise. `set_dec` returns the empty interval, decorated `trv`, for an empty result. Otherwise it keeps the decoration that it gets, except that it lowers `com` to `dac` for a result that is not common, which, if `0 <= a`, is when `b` is +∞. In each case, that is the minimum of the strongest decoration and that of `x`. So, unlike `dec_mul_correct`, `dec_sqrt_correct` has no `com_common` hypothesis: where `set_dec` gets the decoration of a nonempty `x`, the result is common exactly when `x` is bounded.

`sqr_correct` and `dec_sqr_correct` in [`Sqr.v`](theories/Sqr.v) state the same for `sqr`, whose point function is Stdlib's `Rsqr`, `r * r`:

```coq
Theorem sqr_correct :
  forall has_fma x, valid x ->
  exists y, Interval.sqr has_fma x = Some y /\
    is_tightest (image_dom sqr_dom Rsqr x) y.

Theorem dec_sqr_correct :
  forall has_fma x, valid (itv x) ->
  exists y, DecInterval.sqr has_fma x = Some y /\
    if DecInterval.is_nai x then y = x
    else
      is_tightest (image_dom sqr_dom Rsqr (itv x)) (itv y) /\
      exists d, strongest_dom sqr_dom d Rsqr (itv x) (itv y) /\
        dec y = dec_min d (dec x).
```

`sqr` is defined on all of R, so `sqr_dom` holds for every real. It is stated with `image_dom` and `strongest_dom` rather than with `strongest`, because `strongest` asks for `com` that the image be bounded, where the standard and `strongest_dom` ask it of the computed interval, and a square can overflow where the image is bounded: `[f64::MAX, f64::MAX]` squared is `[f64::MAX, +∞]`, which `DecInterval::sqr` decorates `dac`. As for `+`, the bounds of the image need not be floats, so the result is the tightest interval rather than the hull. `has_fma` is the `HAS_FMA` that `mul_ru`, which `Interval::sqr` calls, passes to `mul_ru_impl`, and the theorems hold for both of its values. `Some` means that the `transmute` in `classify` gets the discriminant of a variant, and that `mul_ru` does not panic.

`Interval::sqr` matches on `classify`. An empty `x` gives the empty interval, and `[0, 0]` gives `Interval::zero()`. In `N0` and `N1`, and in `P0` and `P1`, the reals of `x` have one sign, so their squares are those of the elements of a set `A` of reals at least 0: the negations of the reals of `x` in `N0` and `N1`, and the reals themselves in `P0` and `P1`. `A` holds every real between two of its elements, so these squares are the products of two elements of `A` (`squares_products`), and `mul_fin_pos` in `MulNP.v`, which proves `N × N` and `P × P` of `x * y`, applies with `A` as both sets. `Interval::sqr` computes `[RU(b * (-b)); RU((-a) * (-a))]` in `N0` and `N1`, and `[RU((-a) * a); RU(b * b)]` in `P0` and `P1`: the first lane is the negated square of the least element of `A`, rounded up, and the second the square of the largest. In `M`, 0 is in `x`, so the least square is 0, which the first lane holds as +0. A product `r * t` of two reals of `x` is at most `r * r` or `t * t`, so the largest square is the largest such product (`tight_cofinal` in `MulTight.v`), which `tight_mult_mixed` gives as the larger of `(-a) * (-a)` and `b * b`. There is none if `a` or `b` is infinite. The second lane, `max1(RU((-a) * (-a)), RU(b * b))`, is the least float or +∞ at or above it (`mul_lane_pos` and `max_least_lane`).

`Rsqr_continuous` in `Sqr.v` shows that `sqr` is continuous at each real. The strongest decoration is `trv` if `x` is empty, `com` if `x` is nonempty and the result is common, and `dac` otherwise. `com` also asks for a bounded `x`, but a common result comes only from a bounded `x`, as a real `r` with `r * r <= m` has `|r| <= 1 + m`. `DecInterval::sqr` passes the decoration of `x` to `set_dec`, which returns the empty interval, decorated `trv`, for an empty result, and otherwise keeps that decoration, except that it lowers `com` to `dac` for a result that is not common. That is the minimum of the strongest decoration and that of `x`. So, like `dec_sqrt_correct`, `dec_sqr_correct` has no `com_common` hypothesis.

`recip_correct` in [`Recip.v`](theories/Recip.v) shows that `Interval::recip` returns the tightest interval that contains the image of its argument under `1 / r`, which is defined only for `r` other than 0, and `dec_recip_correct` that `DecInterval::recip` decorates it as IEEE 1788 asks. `div_correct` and `dec_div_correct` in [`Div.v`](theories/Div.v) state the same for `x / y`, which is defined only where the divisor is not 0. The decorated versions have the hypothesis `com_common` of `dec_mul_correct`, for each argument:

```coq
Theorem recip_correct :
  forall has_fma x, valid x ->
  exists z, Interval.recip has_fma x = Some z /\
    is_tightest (image_dom recip_dom Rinv x) z.

Theorem dec_recip_correct :
  forall has_fma x, valid (itv x) -> com_common x ->
  exists y, DecInterval.recip has_fma x = Some y /\
    if DecInterval.is_nai x then y = x
    else
      is_tightest (image_dom recip_dom Rinv (itv x)) (itv y) /\
      exists d, strongest_dom recip_dom d Rinv (itv x) (itv y) /\
        dec y = dec_min d (dec x).

Theorem div_correct :
  forall has_fma x y, valid x -> valid y ->
  exists z, Interval.div has_fma x y = Some z /\
    is_tightest (image2_dom div_dom1 div_dom2 Rdiv x y) z.

Theorem dec_div_correct :
  forall has_fma x y, valid (itv x) -> valid (itv y) ->
  com_common x ->
  com_common y ->
  exists z, DecInterval.div has_fma x y = Some z /\
    if DecInterval.is_nai x || DecInterval.is_nai y then z = DecInterval.NAI
    else
      is_tightest (image2_dom div_dom1 div_dom2 Rdiv (itv x) (itv y)) (itv z) /\
      exists d, strongest2_dom div_dom1 div_dom2 d Rdiv (itv x) (itv y) (itv z) /\
        dec z = dec_min d (dec_min (dec x) (dec y)).
```

`recip_dom` holds for the reals other than 0, and `image_dom recip_dom Rinv x` is the image of those reals of `x` under Stdlib's `Rinv`. `image2_dom` and `strongest2_dom` are `image_dom` and `strongest_dom` for a function of two reals whose domain is a product `D1 × D2`, here `div_dom1`, which holds for every real, and `div_dom2`, which holds for the reals other than 0. So the image of `[1, 2] × [0, 1]` under `/` is `[1, +∞)`. Stdlib's `Rinv` and `Rdiv` return 0 for a divisor 0, but those values are not used. `has_fma` is the `HAS_FMA` that `div_ru`, which `Interval::recip` and `Interval::div` call, passes to `div_ru_impl`, as in `div_ru_correct`, and the theorems hold for both of its values. `Some` means that the `transmute`s in `classify` and `classify2` get the discriminant of a variant, and that `div_ru` does not panic.

Unlike a set of products, a set of quotients of reals of two intervals need not have a largest or a least element: `recip([-∞, -1])` is `[-1, 0)`, whose least upper bound 0 is not in it, and `[1, 2] / [1, +∞]` is `(0, 2]`, whose greatest lower bound 0 is not in it. So the lanes of the result hold least upper bounds. `tightest_lanes_lub` in [`DivTight.v`](theories/DivTight.v) is `tightest_lanes` with `lub`, the least upper bound of a set or none if the set has no upper bound, in place of `tight`: the result is the tightest interval if its second lane is the least float or +∞ at or above the least upper bound of the image, and its first lane the least at or above that of the negated image (`lane_ok`).

`Interval::div` matches on `classify2`, as `Interval::mul` does, and `div_correct` splits on the 49 pairs of classes:

- The 19 pairs with an empty argument, or with `y` in `Z`, give the empty interval (`div_empty` in [`DivZero.v`](theories/DivZero.v)). The only real of `[0, 0]` is outside the domain of the divisor, so the image is empty.
- The 5 pairs with `x` in `Z` and `y` in `M`, `N0`, `N1`, `P0` or `P1` give `Interval::zero()` (`div_zero`), as such a `y` has a real `t` other than 0, and `0 / t = 0`.
- The 7 pairs `M × M`, `M × N0`, `M × P0`, `N0 × M`, `N1 × M`, `P0 × M` and `P1 × M` give `ENTIRE` (`div_entire`). In each, either `x` has reals of both signs and `y` has reals other than 0 as close to 0 as asked on one side of 0, or `x` has a real other than 0 and `y` such reals on both sides. So the image has no upper and no lower bound, and `ENTIRE` is the tightest interval that contains it (`tightest_entire`).
- The other 18 pairs call the ten helpers from `div_m_n1` to `div_p_p1` in `src/basic.rs`, and the lemmas from `div_MN1` to `div_PP1` in [`DivCases.v`](theories/DivCases.v) prove them, one per helper. `Interval::div` takes the same branch for `N0` and `N1` on the left, written `N`, and for `P0` and `P1`, written `P`.

`Interval::recip` matches on `classify`. `E` and `Z` give the empty interval and `M` gives `ENTIRE`, as for `/` (`recip_empty` and `recip_entire` in `DivZero.v`), and `recip_N0`, `recip_N1`, `recip_P0` and `recip_P1` in `DivCases.v` prove the other four classes.

In the cases that `DivCases.v` proves, the reals of the divisor are all at least 0 or all at most 0, and [`DivSets.v`](theories/DivSets.v) writes the image and the negated image as sets of quotients `quot U Q`, of a numerator in a set `U` and a denominator in a set `Q` of reals above 0. If the reals of `y` are at least 0, the numerators are the reals of `x` for the image and their negations for the negated image, as `-(r / t) = (-r) / t`, and the denominators are the reals of `y` other than 0. If they are at most 0, `r / t = (-r) / (-t)` swaps the two sets of numerators, and the denominators are the negations of the reals of `y` other than 0 (`div_image_P` and `div_image_N`). For `recip`, the numerators are `{1}` and `{-1}` (`recip_image_P` and `recip_image_N`). `DivTight.v` gives the least upper bound of `quot U Q` in three forms, and [`DivLane.v`](theories/DivLane.v) shows that the lane that `Interval::div` or `Interval::recip` computes for it is the least float or +∞ at or above it:

- (a) `U` has an element above 0 and a largest element `m`, or no upper bound, and `Q` has a least element `n`: the largest quotient is `m / n`, or there is none (`quot_tight_a`). The lane is `Bdiv mode_UP` of a lane above 0 and a float above 0, where +∞ divided by such a float is +∞ (`div_lane_pos`), or of their negations, which gives the same quotient (`div_lane_neg`).
- (b) `U` has an element above 0, and `Q` has elements as close to 0 as asked: the quotients have no upper bound (`quot_unbounded`), and the lane is +∞ (`div_lane_inf`).
- (c) `U` has a largest element `m <= 0`, and `Q` has a largest element `v` or no upper bound: the least upper bound is `m / v`, or 0 if `Q` has no upper bound (`quot_lub_c`). It is not in the set if `m < 0` and `Q` has no upper bound. The lane is `Bdiv mode_UP` of a float at most 0 and a lane above 0, where a float divided by +∞ is a zero, whose value is 0 (`div_lane_nonpos`).

What the class of each argument says about these sets is in `DivSets.v` (`xset_M`, `xset_N`, `xset_P`, `yset_P1`, `yset_P0`, `yset_N1` and `yset_N0`), and the header of `DivCases.v` lists the form of each lane in each case.

`Rinv_continuous` in `Recip.v` and `Rdiv_continuous` in `Div.v` show that `1 / r` is continuous at each `r` other than 0, and `r / t` at each `(r, t)` with `t` other than 0. The strongest decoration is `trv` if an argument is empty, or if 0 is in `x` for `recip` or in `y` for `/`, as `def` asks for a nonempty subset of the domain. Otherwise it is `com` if the arguments are bounded and the result is common, and `dac` if not. `DecInterval::recip` passes `trv` to `set_dec` if `x.contains(0.0)`, and `DecInterval::div` if `y.contains(0.0)`, which holds exactly when 0 is a real of the interval (`contains_zero` in `DivZero.v`). Otherwise they pass the decoration of `x`, or the minimum of those of `x` and `y`. As for `x * y`, a common result can come from an unbounded argument: `recip([1, +∞])` is `[0, 1]` and `[1, 2] / [1, +∞]` is `[0, 2]`. `set_dec` would keep `com` there if the arguments were `com`, where IEEE 1788 asks for `dac`. So `dec_recip_correct` and `dec_div_correct` have the `com_common` hypothesis.

[`Valid.v`](theories/Valid.v) shows that the hypothesis `valid` of the theorems above holds for every interval that is made by the library's constructors, or computed from such intervals by the operations proved here, any number of times:

```coq
Theorem made_valid :
  (forall x, made x -> valid x) /\ (forall d, dmade d -> valid (itv d)).
```

`made` and `dmade` are inductive predicates on `Interval` and `DecInterval`. Each of their constructors is a place in the library that makes a value other than by an operation, or a proved operation, whose arguments must be `made` or `dmade`. The places that make an `Interval` are `EMPTY`, `const_interval!`, which `ENTIRE` and the other constants of `Interval` are, `zero()`, `TryFrom<(f64, f64)>`, `try_from_be_bytes` and its siblings, `try_from_ninterval_exact`, which `interval_exact!` calls, and the interval of a `dmade` decorated interval, which `DecInterval::interval` and `From<NInterval>`, which `FromStr` calls, return. Those that make a `DecInterval` are the constants `EMPTY`, `NAI` and `ENTIRE`, those that `def_com!` makes, `const_dec_interval!`, `new`, `set_dec`, `TryFrom<(f64, f64)>`, `try_from_be_bytes` and its siblings, and `From<DecNInterval>`, which `FromStr` calls. The operations are those above, on `Interval` and on `DecInterval`, and `convex_hull` and `intersection`. A model that returns an `option`, such as that of `x + y`, gives a `made` value for each `Some` that it returns, and the theorems above show that it returns `Some` for `valid` arguments (for `x * y`, `recip` and `x / y` of decorated intervals, also given `com_common`, which `ComCommon.v` proves for every decorated interval), so the value that the Rust function returns is `made`. Each step can take either value of `has_fma` and `has_maximum`, so `made_valid` holds whatever values a target gives them. `made` has no constructor for an operation that is not proved here, such as `exp` or `mul_add`, so `made_valid` does not show that its results, or the intervals computed from them, are `valid` (see "What is not proved yet").

The proof is by induction on `made` and `dmade` together, with a theorem for each of their constructors:

- [`ValidMake.v`](theories/ValidMake.v): the places that make a value other than by an operation. `TryFrom<(f64, f64)>`, and `try_from_be_bytes` and its siblings, call `with_infsup_raw` only for bounds `a <= b` where `a` is not +∞ and `b` is not -∞, which is what `valid` asks for. `const_interval!` does not compile unless its bounds pass the same test (`const_interval_ok`). `EMPTY` holds `[NaN; NaN]`, and `zero()` holds `[+0; +0]`, i.e. `[0, 0]`. `try_from_ninterval_exact` returns an `Err`, or `Ok` of what `TryFrom<(f64, f64)>` returns or of `EMPTY`, and `From<DecNInterval>` returns `set_dec` of one of these. `new` and `set_dec` keep the interval that they get or hold `Interval::EMPTY`, and the other places that make a `DecInterval` hold one of the intervals above.
- [`ValidOps.v`](theories/ValidOps.v): the proved operations on intervals. `is_hull` and `is_tightest`, which the theorems above conclude of the result, include `valid`, so `floor_valid` takes it out of `floor_correct`, and so on.
- [`ValidSetOp.v`](theories/ValidSetOp.v): `convex_hull_valid` and `intersection_valid`. Both return the empty interval, or the other argument for `convex_hull`, if an argument is empty. Otherwise, `convex_hull` of `[a, b]` and `[c, d]` takes `max` of both lanes, `[max(-a, -c); max(b, d)]`, i.e. `[min(a, c), max(b, d)]`, whose bounds are ordered, as `min(a, c) <= a <= b <= max(b, d)`. `intersection` takes `min` of both lanes, `[max(a, c), min(b, d)]`, and returns the empty interval if the lower bound is above the upper one. On lanes that are finite or +∞, `max1` and `min1` are `Rmax` and `Rmin`, with +∞ above every real, and return such a lane (`max1_bound` and `min1_bound` in `MaxMin.v`), so neither result has a lower bound +∞ or an upper bound -∞.
- [`ValidDecOps.v`](theories/ValidDecOps.v): the proved operations on decorated intervals. Each returns an argument, NaI, or `set_dec` of what the operation on their intervals returns, except `convex_hull` and `intersection`, which return NaI or that interval decorated `trv`.

On the way, the other files prove:

- [`Encoding.v`](theories/Encoding.v): `is_finite_eq`, i.e. `is_finite` agrees with Flocq's, `abs_B2R_lt_exponent`, i.e. `|x| < 2^(exponent(x) + 1)`, and `bpow_exponent_le_abs_B2R`, i.e. `2^exponent(x) <= |x|` if `x` is normal. `step_up_Bsucc` shows that `step_up` is Flocq's `Bsucc` (IEEE 754 `nextUp`) on finite floats.
- [`TwoSum.v`](theories/TwoSum.v): `two_sum_err_correct`. If `|x|, |y| < 2^1023` and `x + y` is finite, `two_sum_err` computes the exact error `(x + y) - s` without overflowing. It uses Flocq's proof of TwoSum (`Pff2Flocq.TwoSum_correct`), which allows underflow.
- [`StepUp.v`](theories/StepUp.v): `step_up_rounds_up`. If `p = RN(z)` is nonzero and `e = z - p` exactly, then `if e > 0 { step_up(p) } else { p }` is `z` rounded toward +∞, including the sign of the result and overflow. `mul1_ru_fast_correct` relies on this. `step_up_rounds_up_iff` is the same with any `up` that is true exactly when `p < z` in place of `e > 0`.
- [`TwoProduct.v`](theories/TwoProduct.v): `two_prod_err_correct`. If `two_prod_is_exact` holds for `p = x * y`, then `p` is finite and nonzero, and `two_prod_err` computes the exact error `x * y - p` without overflowing, with or without an FMA. It uses Flocq's `mult_error_FLT` for the FMA, and Boldo's proofs of Veltkamp's `split` and Dekker's TwoProduct (`Pff2Flocq.Veltkamp`, `Pff2Flocq.Dekker`) without one. They hold with subnormals, but `mult_error_FLT` and `Dekker` need `|x * y| >= 2^-969`, which `two_prod_is_exact` ensures by checking `|p| >= 2^-968`.
- [`MulRuTiny.v`](theories/MulRuTiny.v): the steps of `mul1_ru_tiny_correct` that are about real numbers and single floats. `RU_scaled`: rounding `z * 2^128` upward, multiplying it by `2^-128` and rounding the result upward rounds `z` upward, for every real `z`, as Flocq's `round` has no overflow (`mul1_ru_tiny` uses it where nothing overflows). `step_up_rounds_up_iff0` is `step_up_rounds_up_iff` for a nonzero `w` and a `q = RN(w)` that may be zero, provided that a zero `q` has the sign of `w`. `zero_rule_rounds_up`: if `p = RN(z)` is a zero with the sign of a nonzero `z`, then `z` rounded upward is `p` if `z < 0`, and `2^-1074`, whose bit pattern is 1, if `z > 0`. `rounds_up_to_ext` shows that whether a float is `z` rounded upward depends on `z` only through `RU(z)` and the sign of `z`. The other lemmas bound magnitudes and exponents, such as `RN_nonzero_ge` (if `RN(z)` is nonzero, `|z| >= 2^-1075`), give the results of `*` and `Bmult mode_UP` where the exact product is at most `2^1023` in magnitude, or give the values of the constants `2^128` and `2^-128`.
- [`Decompose.v`](theories/Decompose.v): `decompose_correct`, i.e. `decompose` gives the sign, the integral significand and the exponent of a finite nonzero float. `pow2_correct`, i.e. `pow2(e)` is `2^e` for `e ∈ [-1074, 1023]`. `of_u64_exact`, i.e. `k as f64` is exact for `k <= 2^53`. `add_special`: where `add1_ru_slow` returns `x + y`, rounding to nearest gives the same result as toward +∞.
- [`RoundUpExact.v`](theories/RoundUpExact.v): `round_up_exact_correct`. `round_up_exact(neg, m, e, sticky)` rounds `(-1)^neg * (m + δ) * 2^e` toward +∞, under the precondition `round_up_exact_pre` in [`Spec.v`](theories/Spec.v), which bounds `m` and `e` and requires `m >= 2^52` if `sticky`.
- [`SumRoundUp.v`](theories/SumRoundUp.v): `sum_round_up_reduce`. For significands in `(0, 2^106)` and exponents in `[-2^19, 2^19]`, `sum_round_up` returns +0 if the sum is zero, and otherwise calls `round_up_exact` with arguments that meet its precondition.
- [`DivRemainder.v`](theories/DivRemainder.v): `div_remainder`. If `q = RN(x / y)`, `|q| >= 2^-1022` and `|x| >= 2^-967`, the remainder `x - q * y` is a float, and `|x - q * y| <= 2^-52 |x|`. This is a case of [BD03] (see `generic.rs`) for binary64, with subnormals. Flocq proves it only without them (`div_error_FLX`).
- [`DivRuFast.v`](theories/DivRuFast.v): `div_exact`, i.e. the exponent checks in `div1_ru_fast` imply the hypotheses of `div_remainder`. Given its conclusions, `div_fma_remainder` and `div_dekker_remainder` show that `(-q).mul_add(y, x)`, and `(x - p) - two_prod_err(q, y, p)` with `p = q * y`, compute `x - q * y` exactly without overflowing, the latter if `div1_ru_fast`'s checks for Dekker's TwoProduct hold.
- [`DivRuSlow.v`](theories/DivRuSlow.v): `div1_ru_slow_rounds_up`. If `x` and `y` are finite and nonzero, `div1_ru_slow` does not panic and returns `x / y` rounded toward +∞, as it calls `round_up_exact` with arguments that meet its precondition. `div_special`: where `div1_ru_slow` returns `x / y`, the rounding mode does not matter.
- [`SqrtRem.v`](theories/SqrtRem.v): `sqrt_rem_format`. If `x >= 2^-966`, the remainder `x - RN(√x)^2` is a float. This is a case of [BD03] for the square root, with subnormals. Flocq proves it only without them (`sqrt_error_FLX_N`). `sqrt_rem_sign`: the sign of `x - s * s` tells whether `s` is below or above `√x`.
- [`SqrtFast.v`](theories/SqrtFast.v): `sqrt1_fast_rem`. If `sqrt1_fast` accepts a positive `x` and the remainder is a float, then `s = RN(√x)` is positive, and `r` is `x - s * s` exactly, computed without overflowing.
- [`SqrtSlow.v`](theories/SqrtSlow.v): `sqrt1_slow_correct`. If `f` returns `Bsqrt m y` for every `y` that `sqrt1_fast` accepts, `sqrt1_slow x f` returns `Bsqrt m x`, for any rounding mode `m`. `round_scale`: rounding a normal number commutes with a scaling by a power of two that keeps it normal.
- [`AddOdd.v`](theories/AddOdd.v): `add_odd_correct`. If `|x|, |y| < 2^1023` and `RN(x + y)` is finite, `add_odd(x, y)` is `x + y` rounded to odd [BM08] (see `generic.rs`).
- [`EmulatedFma.v`](theories/EmulatedFma.v): `mul_add1_rn_emulated_correct`. Where the fast path of `mul_add_ru` is valid without an FMA and does not return `mul_add1_special(a, b, c)`, `mul_add1_rn_emulated` returns `Bfma mode_NE a b c`, the FMA rounded to nearest, including the sign of a zero. The algorithm is [BM08, Algorithm 1], and the proof follows that of [BM08, Theorem 4], using Flocq's `round_N_odd`. Of the checks in `mul_add1_ru_fast`, the proof uses only `two_prod_is_exact` and the bounds on `exponent(u1)` and `exponent(c)`. The `not_tiny` checks are ErrFma's.
- [`MulAddRuFast.v`](theories/MulAddRuFast.v): `mul_add1_ru_fast_rounds_up`. If `r1 = Bfma mode_NE a b c`, and the fast path is valid and does not return `mul_add1_special(a, b, c)`, its result is `a * b + c` rounded toward +∞. It uses Flocq's proof of ErrFma (`Pff2Flocq.ErrFMA_correct`), whose underflow hypotheses `two_prod_is_exact` and the `not_tiny` checks ensure.
- [`MulAddRuSlow.v`](theories/MulAddRuSlow.v): `mul_add1_ru_slow_correct` above. `mul_add1_special_correct`: where the fast and slow paths return `mul_add1_special(a, b, c)`, rounding to nearest gives the same result as toward +∞.
- [`RoundTiesEven.v`](theories/RoundTiesEven.v): `round_ties_even1_correct`, i.e. `round_ties_even1`, which `round_ties_even` calls on each lane, is Flocq's `Bnearbyint mode_NE`, IEEE 754's roundToIntegralTiesToEven, including the sign of a zero result, the infinities and NaN. For `|x| < 2^52`, `|x| + 2^52` is in `[2^52, 2^53)`, where the ulp is 1, so the addition rounds `|x|` to an integer, ties to even. Subtracting `2^52` is exact, and `copysign` gives the result the sign of `x`, which is right because rounding to nearest, ties to even, is odd.
- [`Nearest.v`](theories/Nearest.v): what `round` and `round_ties_even` share, proved once for any way of breaking a tie. `Rnearest_le` and `Rnearest_near`: rounding to the nearest integer is nondecreasing and moves a real by less than 1. `nearest_strongest`: on an interval with bounds `a` and `b`, the strongest decoration is `com` if both are finite, round to the same integer and neither is halfway between two integers, `dac` if one of them is halfway instead, and `def` otherwise. `is_half_test`: for a finite `a`, `|a| - trunc(|a|) == 0.5` holds exactly when `a` is halfway between two integers.
- [`Classify2.v`](theories/Classify2.v): `classify2_pair`. If `classify` returns `c1` for `x` and `c2` for `y`, `classify2` returns `(c1, c2)`. Every discriminant of an `IntervalClass` is below 16, so the shift by 4 drops no bits, and `transmute_class2` decodes the two nibbles back into the two classes.
- [`Classes.v`](theories/Classes.v): `classify_lanes` and `classify_mem`, what each class says about the lanes of a `valid` interval and about its reals. In `M`, both lanes are above 0, a positive float or +∞ (`pos_lane` in `AddSub.v`). In `N0` and `N1`, the first lane is above 0, and the second is finite and 0 or below 0, and in `P0` and `P1` the other way round. In `Z`, both lanes are finite and 0, and in `E`, both are NaN.
- [`MulLane.v`](theories/MulLane.v): `mul_lane_finite`. `Bmult mode_UP` of two finite lanes is the least float or +∞ at or above their product: the product rounded up if that does not overflow, +∞ if it overflows above, and `-f64::MAX` if it overflows below, as `add_lane` shows for a sum. `mul_lane_pos`: the same for two lanes above 0, where the product is +∞ if either lane is (`umult` in `AddSub.v`). `max_least_lane`: if two lanes are the least floats or +∞ at or above two upper bounds, their `max1` is the least at or above the larger bound.
- [`MulTight.v`](theories/MulTight.v): the largest product of an element of a set of reals `A` and one of a set `B`, with the largest element of a set, or +∞ if there is none, as in `tight` in `AddSub.v`. `tight_Some`: a set has the largest element `m` exactly when `m` is in it and every element is at most `m`. `tight_mult_pos_r` and `tight_mult_pos_l`: if the elements of `B`, or those of `A`, are at least 0, and `A` and `B` each have an element above 0, the largest product is the product of the largest elements, or +∞ if either is. `tight_mult_min`: if the least elements `a` and `c` of `A` and `B` are at least 0, the largest negated product is `-(a * c)`. `tight_mult_mixed`: if `A` and `B` each have elements below and above 0, the largest product is the larger of the product of the largest negations and the product of the largest elements. `image2_mult_opp_l`, `image2_mult_opp_r` and `image2_mult_opp_lr`: the negated products of reals of `x` and `y` are the products with the factor from `x`, or that from `y`, negated, and the products are those with both negated, as `-(r * t) = (-r) * t = r * (-t)` and `r * t = (-r) * (-t)`.
- [`MulZero.v`](theories/MulZero.v): `mul_empty` and `mul_zero` above. `zero_tightest`: `Interval::zero()`, `[+0; +0]`, holds exactly the real 0, as its lower bound is `-(+0)`, and so is the tightest interval that contains `{0}`.
- [`MulMM.v`](theories/MulMM.v): `mul_MM` above.
- [`MulMRow.v`](theories/MulMRow.v): `mul_MN`, `mul_MP`, `mul_NM` and `mul_PM` above. `mul_M_lanes`, `mul_N_lanes` and `mul_P_lanes` collect what the proofs need of each class, so that the tightness arguments treat `N0` and `N1`, and `P0` and `P1`, alike.
- [`MulNP.v`](theories/MulNP.v): `mul_NN`, `mul_NP`, `mul_PN` and `mul_PP` above. `mul_NN_eq`, `mul_NP_eq`, `mul_PN_eq` and `mul_PP_eq` give the lanes that `Interval::mul` returns, as `Bmult mode_UP` of two lanes each. `mul_fin_pos` and `mul_pos_fin` put a lane rounded up from two finite lanes and one from two lanes above 0 together into the tightest interval. A bound that is 0 may be stored as +0 or -0, which need no cases of their own, as both are finite with the value 0.
- [`DivTight.v`](theories/DivTight.v): `tightest_lanes_lub`, `quot_tight_a`, `quot_unbounded` and `quot_lub_c` above. `tight_lub`: a largest element, or none for a set with no upper bound, is a least upper bound in the sense of `lub`.
- [`DivLane.v`](theories/DivLane.v): `div_lane_pos`, `div_lane_neg`, `div_lane_inf` and `div_lane_nonpos` above. `div_lane_finite`: `Bdiv mode_UP` of two finite lanes, the second not 0, is the least float or +∞ at or above their quotient, as `mul_lane_finite` shows for a product.
- [`DivSets.v`](theories/DivSets.v): `div_image_P`, `div_image_N`, `recip_image_P` and `recip_image_N` above, and the sets of numerators and denominators of each class. `div_tightest_P`, `div_tightest_N`, `recip_tightest_P` and `recip_tightest_N` put the rewritten image together with `tightest_lanes_lub`.
- [`DivZero.v`](theories/DivZero.v): `div_empty`, `div_zero`, `div_entire`, `recip_empty`, `recip_entire` and `contains_zero` above. `tightest_entire`: `ENTIRE` is the tightest interval that contains a set with no upper and no lower bound.
- [`DivCases.v`](theories/DivCases.v): the lemmas from `div_MN1` to `div_PP1`, and `recip_N0`, `recip_N1`, `recip_P0` and `recip_P1` above. `div_MN1_eq` and the other lemmas named `_eq` give the lanes that each helper and each branch of `Interval::recip` returns, as `Bdiv mode_UP` of two lanes, or +∞.

## What is assumed

[`Model.v`](theories/Model.v) transcribes the Rust functions line by line. It is the only file that has to be checked against the Rust code by reading, and it has to be updated whenever those functions change. Its modelling choices:

- `f64` is Flocq's binary64, and Rust's `+`, `-` and `/` are Flocq's `Bplus`, `Bminus` and `Bdiv` rounded to nearest, ties to even. `generic.rs` relies on this default rounding mode. `f64::mul_add` is Flocq's `Bfma` in the same mode, with a single rounding, as Rust specifies it whether or not the target has an FMA instruction. `f64::sqrt` is Flocq's `Bsqrt`, also rounded to nearest, ties to even.
- NaN payloads and signs are not modelled: all NaNs are the same value, so `Bopp` keeps a NaN as it is where Rust's unary `-` flips its sign bit. The functions modelled here only read the exponent field of a NaN, which is all ones for every NaN, except `add_odd`. It reads the lowest bit of `s`, which for a NaN is part of the payload, but returns a NaN for a NaN `s` either way.
- Bit patterns are integers rather than `u64`, so `b + 1` and `b - 1` in `step_up` cannot wrap around. `step_up_no_wrap` in `Encoding.v` shows that for finite floats they stay in the range of `u64`, so they don't wrap around (or panic) in Rust either. The same holds for ±∞ and NaN, but is not proved: `b + 1` is only computed if `x > 0`, so the sign bit of `b` is clear, and `b - 1` only if `x < 0`, so it is set.
- The other integer types, `u128`, `u64`, `u32` and `i32`, are integers too. In the slow path and in `mul1_ru_tiny`, every operation that panics in a debug build returns `None`: one whose result does not fit its type, a shift by a negative amount or by at least the width of the type, and the `debug_assert!`s in `sum_round_up` and `mul1_ru_tiny`. A release build would wrap around instead, so a theorem that a function returns `Some` covers both kinds of build. The integer `/` and `%` in `div1_ru_slow` return `None` for a zero divisor, which panics in both kinds of build. Arithmetic on the fields of a bit pattern, in `exponent` and `decompose`, cannot overflow and is not checked.
- Casts that could change a value reduce it modulo the size of the target type, as Rust does: `(e + 1023) as u64`, `kept as u64` and `(ex - ey) as u32`. Casts that keep the value are left out: those of the 11-bit exponent field in `exponent` and `decompose`, and, each with a comment, the `leading_zeros() as i32` casts, `sh as i32` and the `as u128` casts of significands.
- `kept as f64` is Flocq's `binary_normalize` rounded to nearest, ties to even, like Rust's conversion from `u64`. A float literal is the same conversion of its value: Rust rounds a literal to nearest too, and the ones used, `134217729.0` (`2^27 + 1`) in `split`, `1.0` and `18446744073709551616.0` (`2^64`) in `sqrt1_slow` and `mul1_ru_tiny`, `1.0` in `Interval::sign`, and `4503599627370496.0` (`2^52`) in `round_ties_even1`, are exact. `-1.0` in `Interval::sign` and `Interval::recip` is the negation of the literal `1.0`, as Rust parses it. The `const`s in `sqrt1_slow`, `mul1_ru_tiny` and `round_ties_even1` are evaluated at compile time, rounded to nearest as at run time. `0.5` in `impl_dec!(round, ...)` and `impl_dec!(round_ties_even, ...)` is given by its bit pattern, and `0.0` in `max1`, `min1`, `classify`, `Interval::abs`, `Interval::sign`, `Interval::sqr`, `Interval::sqrt`, `Interval::zero`, `impl_dec!(sign, ...)`, `impl_dec!(trunc, ...)`, `DecInterval::sqrt`, `DecInterval::recip` and `DecInterval::div` is +0. `*` is Flocq's `Bmult` rounded to nearest, ties to even, and unary `-` is `Bopp`.
- `F64X2` is a pair, and `lanewise2` takes the two paths as functions. `sqrt1_slow` takes `f` as a function too, one that returns an `option` like the models passed for it.
- `sqrt1_rd_impl` and `sqrt1_ru_impl` call themselves through `sqrt1_slow`. Rocq functions must terminate, so the models take the number of nested calls they may make and return `None` if they would make more. `sqrt1_rd` and `sqrt1_ru` allow one. A result `Some r` means that the Rust function returns `r`.
- A const generic parameter, such as `FMA`, is an ordinary argument. So is `HAS_FMA`, which `mul_ru`, `div_ru`, `mul_add_ru`, `sqrt1_rd` and `sqrt1_ru` pass for it, as its value depends on the target. `Interval::mul` and `Interval::sqr`, which call `mul_ru`, `Interval::sqrt`, which calls `sqrt1_ru` and `sqrt_rd_ru`, `Interval::recip`, `Interval::div` and its ten helpers, which call `div_ru`, and their decorated versions take it as the argument `has_fma`.
- `f64::floor`, `f64::ceil`, `f64::round` and `f64::trunc` are Flocq's `Bnearbyint` toward -∞, toward +∞, to nearest with ties away from zero, and toward zero, IEEE 754's roundToIntegralTowardNegative, roundToIntegralTowardPositive, roundToIntegralTiesToAway and roundToIntegralTowardZero. `f64::abs` is Flocq's `Babs`. `f64::is_finite` in `Interval::contains` is Flocq's `is_finite`, which is false exactly for the infinities and NaN, as `f64::is_finite` is, and its `&` of two `bool`s is `&&`, which gives the same value. `x.copysign(y)` is `x` if `x` and `y` have the same sign, and `-x` otherwise. As NaNs have no sign in the model, it takes a NaN `y` as positive, but `round_ties_even1`, its only caller, never passes a NaN for `y`. `p.is_sign_negative()` in `mul1_ru_tiny` is Flocq's `Bsign p`, which differs from it only for a NaN, and `p = x * y` is not NaN there, as `x` and `y` are finite.
- `Interval` is a record of its `rep`, and `DecInterval` of an `Interval` and a `Decoration`, whose variants compare by their discriminants, as the derived `Ord` does. `valid` states the form of `rep` from the comment on `struct Interval`, with the bounds that `TryFrom<(f64, f64)>` accepts. The theorems assume that their argument is `valid`, which `made_valid` in `Valid.v` proves for the intervals that the constructors make and the proved operations compute from them, but not for the others (see "What is not proved yet").
- A comparison of two `F64X2`s, such as `lt`, returns a mask, whose lanes have every bit set where the comparison holds and every bit clear where it does not. A lane with every bit set is a NaN, which `to_bits` would give the bits of another NaN, so the model keeps the bit patterns of the lanes of a mask instead. `all` and `bitmask` take these bit patterns, and so does `and` as its second argument. `and` reads the lanes of its first argument with `to_bits`, and `or` those of both of its arguments, which gives their bits only if they are not NaN. `Interval::sign`, their only caller, passes no NaN: it calls `and` on `1.0` and `-1.0`, and `or` on the results, whose lanes are `1.0`, `-1.0` or `0.0`.
- `max1` and `min1` read `to_bits` only of two zeros, whose bit patterns the model gives exactly. `f64::NAN` in `maximum1` and `minimum1` is the model's only NaN.
- `unsafe { transmute(c) }` in `classify`, from a `u8` to an `IntervalClass`, is `transmute_class`, which returns `None` unless `c` is the discriminant of a variant, as the behaviour is undefined then. The variants `E`, `M`, `N0`, `N1`, `P0`, `P1` and `Z` are `CE`, `CM` and so on, as `Z` is the type of integers. The casts `bitmask(...) as u8` keep the value, which is below 4, and are left out, and `|` of two `bool`s in `either_empty` is `||`, which gives the same value. `transmute` in `classify2`, from a `u8` to an `IntervalClass2`, is `transmute_class2`, which returns `None` unless `c / 16` and `c % 16` are both discriminants of `IntervalClass`, and otherwise the pair of the variants that `transmute_class` decodes them to, written `(CM, CN0)` for the variant `M_N0` and so on. That is the variant with discriminant `c`, as every discriminant of `IntervalClass` is below 16. The casts `c as u8` of an `IntervalClass` in `classify2` are `class_discriminant`.
- `HAS_MAXIMUM` depends on the backend: it is `true` in `generic.rs` and `false` in `x86_64.rs`. So `Interval::max`, `Interval::min` and their decorated versions take it as the argument `has_maximum`, as for `HAS_FMA`, and the theorems hold for either value. The branch for `false` calls `either_empty` and the backend's `max` and `min`, which are the portable backend's here, as every backend function in the model is.
- The places that make a `DecInterval`, for `ComCommon.v`, are the ones listed above. That is checked by reading: `git grep -n 'new_unchecked\|transmute' -- src` finds the callers of `new_unchecked` and the `transmute`s, `git grep -nE '(Self|DecInterval) *\{' -- src` finds no struct expression of `DecInterval` other than the one in `new_unchecked`, the other `unsafe` code outside `src/simd` only calls MPFR and GMP, and nothing assigns to the fields `x` and `d`. The constants that `def_com!` decorates `com` are `const_interval!(a, b)` for decimal literals `a` and `b` between 0.3 and 6.3, which Rust rounds to finite floats. `try_from_be_bytes` and its siblings take the floats `a` and `b` that `f64::from_be_bytes` and so on decode, which the model leaves out, as the theorem holds for any. Their `a.is_sign_negative()` is Flocq's `Bsign a` and `b.is_sign_positive()` its negation, which differ from Rust only for a NaN, where `a <= b` already makes the condition false. The `transmute` in `const_dec_interval!` puts an `Interval` and a `Decoration` into the fields of a `DecInterval`, as both structs are `#[repr(C)]` with the same fields in the same order. `f64::NEG_INFINITY` and `f64::INFINITY` are `B754_infinity true` and `B754_infinity false`.
- The places that make an `Interval`, for `Valid.v`, are the ones listed there and the operations. That is checked by reading. The field `rep` of `Interval` is `pub(crate)`, so only the library can make an `Interval` with a struct expression. `git grep -nE '\brep *:' -- src ':!src/simd'` finds every struct expression of `Interval`, as none uses the shorthand `{ rep }` (`git grep -nE '\{ *rep *[,}]' -- src` finds nothing), and `git grep -n 'with_infsup_raw\|transmute' -- src ':!src/simd'` finds the calls of `with_infsup_raw` and the `transmute`s, of which those in `Interval::EMPTY` and `const_interval!` make an `Interval`. As for `ComCommon.v`, the other `unsafe` code outside `src/simd` only calls MPFR and GMP, and the backends in `src/simd` make no `Interval`. Nothing assigns to `rep` (`git grep -nE '\.rep *=[^=]' -- src ':!src/simd'` finds nothing), and `x += y` and the other compound assignments assign what an operation returns. Each struct expression and each call of `with_infsup_raw` is in one of those places, in a proved operation, or in an operation that is not proved: a function in `src/elementary.rs`, `mul_rev_to_pair`, `cancel_minus` or `mul_add`. The places that make a `DecInterval` are those of `ComCommon.v`, above, and `DecInterval::interval` returns the interval of one. A `Result` is an `option`, with `Ok(x)` as `Some x` and the `Err` as `None`. `const_interval_ok` is the condition that `const_interval!` asserts in a `const`, so that a use of the macro compiles only if it is true. `From<DecNInterval>` and `try_from_ninterval_exact` take as arguments the floats `a.f` and `b.f` that `number_to_f64` computes with MPFR from the bounds that `FromStr` parses, and whether one of them overflowed or is inexact, so MPFR is not modelled, and the theorems hold for any values of these.

[`Ieee1788.v`](theories/Ieee1788.v) states what IEEE Std 1788-2015 asks of an interval version of a function: the hull of the image (`is_hull`), or the tightest interval that contains it (`is_tightest`) where its bounds need not be floats, and the properties of the decorations. It is the only file that has to be checked against the standard by reading. For `com`, the standard asks for the computed interval to be bounded. `p`, for functions of one real, asks for the image instead. `is_hull_bounded` in `Integer.v` shows that the two are the same for a hull, which each function stated with `p` returns. `p2`, for functions of two reals, asks for the computed interval, as the standard does, as `x + y` can overflow where the image is bounded. Stdlib's `continuity_pt` and `continue_in` are for functions of one real, so for functions of two, `Ieee1788.v` defines continuity on R² itself, by ε and δ with the norm `max(|r|, |t|)` (`continue_in2`, `continuity2_pt`). It also defines the image of a box (`image2`) and the decorations of a function of two reals (`p2`, `strongest2`). For a function of one real that is defined only on a set of reals, its domain, such as `sqrt` on `[0, +∞)` (`sqrt_dom`), it defines the image of the reals of an interval that are in the domain (`image_dom`) and the decorations (`p_dom`, `strongest_dom`). `def`, `dac` and `com` ask for the interval to be a nonempty subset of the domain, and `com` for continuity at each of its points relative to the domain, as IEEE 1788 counts `sqrt` as continuous at 0. For `com`, `p_dom`, like `p2`, asks for the computed interval to be bounded. `sqr` is stated with these too, with the domain `sqr_dom`, which is all of R, because a square can overflow where the image is bounded, and so is `recip`, with the domain `recip_dom`, the reals other than 0. For a function of two reals whose domain is a product `D1 × D2` of two sets of reals, such as `/` on `div_dom1 × div_dom2`, i.e. R × (R ∖ {0}), it defines the image of the points of a box that are in the domain (`image2_dom`) and the decorations (`p2_dom`, `strongest2_dom`), as `image_dom`, `p_dom` and `strongest_dom` do for one real. A box is a nonempty subset of such a domain exactly when each of its sides is a nonempty subset of the matching factor, and `continue_in2` already takes a product of two sets, so `p2_dom` can state continuity relative to the domain as it states continuity relative to a box. A product suffices for `/`.

The theorems depend on four axioms. Three come from Stdlib's real numbers: `sig_forall_dec`, `sig_not_dec` and `functional_extensionality_dep`. The fourth is excluded middle (`classic`), which Flocq uses. `make` fails if [`Assumptions.v`](Assumptions.v) finds any other axiom, e.g. a proof left `Admitted`.

## What is not proved yet

- The SIMD backends that vectorize the same algorithm, such as `src/simd/x86_64/lanewise.rs` and `src/simd/wasm32.rs`. If the fast path rejects either lane, `mul_ru` of the `fma`, `sse42` and `wasm32` backends calls `mul_ru_tiny`, which rounds a product below `2^-968` as `mul1_ru_tiny` does, but differs from it in three ways. It computes the fast path's result, the result for a zero `RN(x * y)` and the result through the scaled product in both lanes, and selects one in each lane, where `mul1_ru_tiny` computes only the one that its lane needs. It tells the sign of a zero `RN(x * y)` by comparing its bit pattern with that of +0 as signed integers. And it does not choose the lanes by the exponent of `RN(x * y)`, as `mul1_ru_tiny` does: it accepts a rejected lane if `RN(x * y)` is zero or `two_prod_is_exact` holds for the scaled product, which it checks at run time, and otherwise has the portable backend's `mul_ru` recompute both lanes.
- The other backends' versions of the functions that `abs`, `floor`, `ceil`, `max`, `min`, `recip`, `round`, `round_ties_even`, `sign`, `sqr`, `sqrt`, `trunc`, `-x`, `x + y`, `x - y`, `x * y`, `x / y`, `convex_hull` and `intersection` of intervals, `TryFrom<(f64, f64)>`, and `try_from_be_bytes` and its siblings, call: `floor`, `ceil`, `round`, `round_ties_even`, `trunc` and `neg0`, such as `_mm_floor_pd` on x86-64, `splat`, `gt`, `lt`, `and` and `or` in `sign`, `ge`, `le`, `bitmask`, `splat`, `max`, `swap` and `shuffle02` in `abs` and `classify`, `max`, `maximum`, `min`, `minimum` and `shuffle03` in `max` and `min`, `swap` in `-x` and `x - y`, `add_ru` in `x + y` and `x - y`, `max`, `mul_ru`, `neg0`, `shuffle02`, `shuffle13`, `splat` and `swap` in `x * y`, all but `shuffle13` also in `sqr`, `sqrt1_ru`, `sqrt_rd_ru` and `neg0` in `sqrt`, `div_ru`, `neg0`, `shuffle02`, `shuffle03`, `splat` and `swap` in `x / y`, `div_ru`, `shuffle02`, `shuffle13`, `splat` and `swap` in `recip`, `le`, `all`, `neg0` and `splat` in `contains`, which the decorated `recip` and `x / y` call, `lt`, `all`, `splat`, `extract0` and `extract1` in `is_empty`, `is_singleton`, `is_common_interval`, `inf_raw` and `sup_raw`, `max` in `convex_hull`, `min` in `intersection`, and `constant` in `with_infsup_raw`, which `sqrt`, `TryFrom<(f64, f64)>`, and `try_from_be_bytes` and its siblings call. The roundings are meant to be the same IEEE 754 operations in every backend, but the theorems are proved only for the portable backend's.
- That the intervals that the operations that are not proved here return are `valid`: those of `mul_rev_to_pair`, `cancel_minus`, `cancel_plus` and `mul_add`, those of the functions in `src/elementary.rs`, such as `exp` and `sin`, which compute their bounds with MPFR, and those of their decorated versions. `made` has no constructor for these, so `made_valid` does not cover their results, or the intervals computed from them, directly or through other operations, and the theorems above assume that such an interval is `valid`.
- Every other operation, such as `mul_rev_to_pair` or `cancel_minus` of intervals.

## Building

You need Rocq 9.1, its Stdlib and Flocq 4.2.2. With [opam](https://opam.ocaml.org):

```bash
opam repo add rocq-released https://coq.inria.fr/opam/released
opam install rocq-core.9.1.1 rocq-stdlib.9.0.0 coq-flocq.4.2.2
make -C rocq
```

You can also use Docker, as CI does ([`ci-rocq.yml`](../.github/workflows/ci-rocq.yml)). The container's user (uid 1000) must be able to write to `rocq/`.

```bash
docker run --rm -v "$PWD/rocq:/w" -w /w rocq/rocq-prover:9.1 \
  bash -c 'opam install -y coq-flocq.4.2.2 && make'
```

Warnings are errors. `make clean` removes the build outputs.
