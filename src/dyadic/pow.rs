// The powers x^y for an `f64` y and x^n for an `i32` n with the dyadic kernel, each rounded to
// an `f64` toward +∞ if `up` and toward -∞ otherwise, and, as `pow_near` and `pown_near`, to
// nearest, ties to even, as MPFR rounds them but for x^y at x < 0 (below; `src/dyadic.rs`
// says what `ziv` and `ziv_near` return at their caps). `src/mpfr_calls/kernel.rs` makes the
// first the `pow_rd`, `pow_ru`, `pown_rd` and `pown_ru` that `src/elementary.rs` calls,
// `src/cr.rs` makes both the `pow_rn`, `pow_rd`, `pow_ru`, `powi_rn`, `powi_rd` and `powi_ru`
// of `inari::cr`, with MPFR's values of x^y at x < 0, and the tests on 64-bit Linux and macOS
// compare them with those of MPFR, `src/mpfr_calls/mpfr.rs`.
//
// Each function first settles some arguments by rules: NaN, the zeros and the infinities, the
// zero exponents, x = 1 for x^y, and, from bounds on the exponents of the arguments, some of
// the arguments whose results overflow, are below 2^-1074 or, for x^y, are within an ulp of 1,
// all as MPFR gives them. The others of these go on to `ziv`. x^y for a finite x < 0, or for
// x = -∞, is NaN here, where MPFR gives (-1)^y |x|^y at an integer y: `Interval::pow` passes
// x >= 0 or x = -0 only. Ziv's strategy cannot settle an argument whose result is an `f64`
// unless an enclosure has that `f64` as its bound in the direction of the rounding (the header
// of `src/dyadic/exp.rs` says why). x^y is an `f64` at many arguments, and `exact` finds each
// of them before the loop, from the odd parts of x and y, in integers. x^n is an `f64` only
// where binary powering of the exact x rounds nothing, so the loop settles those at its first
// level. x^y at an integer y from -2^31 to 2^31 - 1 that `exact` leaves is computed as x^n for
// n = y, as binary powering took fewer instructions than the logarithm and the exponential of
// `Pow` on each set of such y counted (cachegrind); `mpfr_pow` also passes an integer y below
// 2^256 in magnitude to `mpfr_pow_z`, which computes x^y by multiplications. `ziv` computes
// the rest from an `Eval`, at a first level that grows with the bits that the evaluation
// loses.
//
// The functions rounded to nearest have the same rules, with the bounds at which the results
// overflow, are less than half an ulp from 1 or are at most 2^-1075, whose tie goes to +0, and
// `exact_near` in place of `exact`. Rounded to nearest, Ziv's strategy cannot settle an
// argument whose result is the midpoint of two adjacent `f64`s unless the midpoint is a bound
// of an enclosure, as in an exact one, since the two bounds of an enclosure that holds it
// strictly inside round to different `f64`s. `exact_near` finds the arguments of x^y whose
// results are `f64`s or such midpoints, q 2^e for an odd q < 2^54 and e >= -1075, as `exact`
// finds the `f64`s, and x^n at such a midpoint is again binary powering that rounds nothing,
// which the loop settles at its first level.
//
// x^y = e^t for t = y ln x, for x > 0. The evaluation takes ln x = e ln 2 + σ a for the
// (e, a, less) of `reduce` of `src/dyadic/log.rs`, with σ = -1 if `less` and 1 otherwise, and
// e^t = 2^k e^-w for w = k ln 2 - t = (k - y e) ln 2 - σ y a and an integer k near t / ln 2, as
// `scaled` of `src/dyadic/exp.rs` takes it. y e is exact, as y has 53 bits and |e| < 2^11, so
// that when e is large the bits of k and y e cancel exactly, and w loses about the bits of
// |y a| + 1 rather than of |t|. x^n is binary powering of the exact x for n > 0, and the
// quotient of 1 by it for n < 0. Its relative error grows with |n|, about a bit per squaring.
// Every product is of enclosures of nonnegative numbers but those of `Pow`, and every quotient
// is by an enclosure of positive numbers.
//
// x^y and x^n try a fast path in double-double before `ziv` and `ziv_near` (`fast_pow_dir` and
// `fast_pow_near`): `pow` and `pow_near` after `exact` and `exact_near` and after the integer y
// that they pass to x^n, and `pown_pos` and `pown_pos_near` after their two rules, at y = n.
// It computes ln x as lh + ll within 17/16 2^-79 |ln x| (`ln_acc` of `src/dyadic/log.rs`),
// t = y ln x as th + tl within 3/4 2^-69 of it, with th = RN(y lh) and the error of that
// product, which is exact there, and e^t by `fast_exp` of `src/dyadic/exp.rs`, as h + l with
// x^y 2^-e within 2^-67 of it, and rounds that with the tests of `src/dyadic/fast.rs` at 2^-67
// (`round_dir_err` and `round_near_err`). Where th is out of the range of `fast_exp` or a test
// fails, the function calls `ziv` or `ziv_near` as before. The x^y that are `f64`s do not
// reach the fast path, as `exact` and `exact_near` settle them first, and neither do, in
// `pow_near`, the midpoints, which `exact_near` settles. At an x^n that is an `f64`, the
// directed test fails, as it passes only where the scaled result lies strictly between two
// adjacent `f64`s, and the loop settles x^n at its first level as above. Where the fast path
// returns, it returns the correct rounding, at these arguments too.
//
// `rocq/theories/Model.v` transcribes each function of this file except the tests, so it has
// to be updated along with them. `rocq/theories/DyPow.v` and `rocq/theories/DyPown.v` prove
// that `pow` and `pown`, at finite arguments in their domains (`pow_dom` and `pown_dom` of
// `rocq/theories/Elementary.v`) and where they do not panic, return values on the side of
// x^y and x^n that the rounding is on, and, where a rule or `exact` settles the arguments, the
// fast path returns or a rounding test of `ziv` passes, x^y and x^n rounded as `mpfr_round` in
// `rocq/theories/Mpfr.v` says. `DyPow.v` builds on `rocq/theories/DyPowRules.v` for the
// rules, `rocq/theories/DyPowCore.v` for `Pow`, `rocq/theories/DyPowExact.v` and
// `rocq/theories/DyPowArith.v` for `exact`, `DyPown.v` for the integer y that `pow` passes
// to x^n, and `rocq/theories/FastPow.v` for the fast path. `DyPown.v` proves the rules of x^n
// and binary powering. `FastPow.v` proves that the fast path returns x^y rounded, with and
// without an FMA, from `rocq/theories/FastPowLn.v` for `ln_acc`, `rocq/theories/FastPowMul.v`
// for t and `rocq/theories/FastExpCore.v` for `fast_exp`. These files also show that
// `exact` finds every argument that reaches it whose exact result is an `f64`, and that both
// functions return that `f64` at every finite argument whose exact result is one, with x > 0
// for x^y and x other than 0 for x^n. `rocq/theories/DyPowNear.v` proves that `pow_near` and
// `pown_near`, at finite arguments in their domains, where a rule or `exact_near` settles the
// arguments, the fast path returns or a rounding test of `ziv_near` passes, return x^y and x^n
// rounded to nearest as `near_round` in `rocq/theories/NearF64.v` says, from the same
// enclosures and bounds, the cells of `rocq/theories/NearCells.v` and
// `rocq/theories/DyPowNearExact.v` for `exact_near`. `DyPowNearExact.v` also shows that
// `exact_near` finds every argument that reaches it whose x^y is an `f64` or a midpoint, and
// `DyPowNear.v` that `pow_near` returns the rounding to nearest at every finite x > 0 whose x^y
// is one. That x^n at a midpoint is settled at the first level is not proved: the tests check
// its value, which the step of `ziv_near` at the cap would also give. That a test passes by the
// cap of `ziv` or of `ziv_near` at the other arguments is not proved, nor that the evaluations
// do not panic.

use super::{
    consts::ln2,
    exp::{fast_exp, mul_f64, mul_int, near_one, overflow, scaled, underflow, ERR67},
    fast::{round_dir_err, round_near_err},
    log::{ln_acc, reduce},
    round, ziv, ziv_near, Dyadic, Encl, Eval,
};
use crate::simd::{two_prod_err, HAS_FMA};
use std::f64::consts::LOG2_E;

#[cfg(test)]
mod tests;

// The first level of `ziv` is 2 rather than 1 from about these many bits lost by the
// evaluation of x^y, and for |n| from 2 to the power of this for x^n. Any level gives the same
// results. Of the values from 4 to 12 counted (all but 7 for x^y and 5 for x^n), these took the
// fewest instructions (cachegrind), summed over random sets of the arguments that reach `ziv`:
// for x^y, |y ln x| from 100 to 745, x next to 1, integer y, arguments next to an exact case,
// and log-uniform x and y; for x^n, n = ±17, |n| up to 40, and |n| log-uniform up to 2^31.
// `pow` has passed an integer y from -2^31 to 2^31 - 1 to x^n since. The set of integer y
// took the same instructions at every value counted from 6 to 12, and the other sets of x^y
// alone took more at 4 and 5 than at 6, so that without it the value for x^y still took the
// fewest.
const POW_START_BITS: i64 = 10;
const POWN_START_BITS: u32 = 9;

// (m, e) for a finite nonzero x, with |x| = m 2^e and an odd m, from the bits of x.
fn odd_parts(x: f64) -> (u64, i64) {
    let bits = x.to_bits();
    let be = ((bits >> 52) & 0x7ff) as i64;
    let f = bits & ((1 << 52) - 1);
    // |x| = f 2^-1074 for a subnormal number, and (2^52 + f) 2^(be - 1075) otherwise.
    let (m, e) = if be == 0 {
        (f, -1074)
    } else {
        (f | (1 << 52), be - 1075)
    };
    let z = m.trailing_zeros();
    (m >> z, e + i64::from(z))
}

// floor(log2 |x|) for a finite nonzero x: 2^g <= |x| < 2^(g + 1).
fn expo(x: f64) -> i64 {
    let (m, e) = odd_parts(x);
    e + 63 - i64::from(m.leading_zeros())
}

// floor(log2 v) for v >= 1, without `ilog2`, which needs a Rust after the MSRV.
fn ilog2(v: i64) -> i64 {
    63 - i64::from((v as u64).leading_zeros())
}

// The integer A with 2^A <= |ln x| < 2^(A + 3), for a finite x > 0 other than 1. For x in
// [2^g, 2^(g + 1)), ln x is in [g ln 2, (g + 1) ln 2], with ln 2 in (1/2, 1). Near 1, x - 1 is
// exact (Sterbenz's lemma), and |x - 1| / 2 <= |ln x| <= 2 |x - 1| for x in [1/2, 2), from
// 1 - 1/x <= ln x <= x - 1.
fn ln_expo(x: f64) -> i64 {
    let g = expo(x);
    if g >= 1 {
        ilog2(g) - 1
    } else if g <= -2 {
        ilog2(-g - 1) - 1
    } else {
        expo(x - 1.0) - 1
    }
}

// Whether the finite y is an odd integer: its odd part is at 2^0.
pub(crate) fn is_odd_integer(y: f64) -> bool {
    y != 0.0 && odd_parts(y).1 == 0
}

// r^p for an odd r >= 3, if it is below 2^53.
fn small_power(r: u64, p: u64) -> Option<u64> {
    let mut q = 1;
    for _ in 0..p {
        let t = u128::from(q) * u128::from(r);
        if t >= 1 << 53 {
            return None;
        }
        q = t as u64;
    }
    Some(q)
}

// x^y if it is an `f64`, for a finite x > 0 other than 1 and a finite y != 0, and `None`
// otherwise. For x = mx 2^ex and |y| = p / 2^k with odd mx, and an odd p if k > 0, x^y is an
// `f64` only if x is the 2^k-th power of a dyadic number r = mr 2^er, so that mr^(2^k) = mx
// and 2^k er = ex, and r^(±p) is one, which for y < 0 needs mr = 1. A 2^k-th root of mx is k
// square roots, each of which has to be an integer, as an integer that is the square of a
// rational is the square of an integer. A square root below 2^27 is exact in `f64`.
fn exact(x: f64, y: f64) -> Option<f64> {
    let (mut mx, mut ex) = odd_parts(x);
    let (my, ey) = odd_parts(y);
    // |y| >= 2^12 makes |ex y| >= 2^12 for mx = 1, as ex != 0, and mx^|y| >= 3^4096 > 2^53
    // otherwise.
    if ey > 11 {
        return None;
    }
    let (p, k) = if ey >= 0 { (my << ey, 0) } else { (my, -ey) };
    for _ in 0..k {
        let s = (mx as f64).sqrt() as u64;
        if ex % 2 != 0 || s * s != mx {
            return None;
        }
        mx = s;
        ex /= 2;
    }
    // x^y = mr^±p 2^(±p er) for the mr and er that are now mx and ex.
    let q = if mx == 1 {
        1
    } else if y < 0.0 {
        return None;
    } else {
        small_power(mx, p)?
    };
    let e = i128::from(ex) * i128::from(p);
    let e = if y < 0.0 { -e } else { e };
    // q 2^e is an `f64` if q < 2^53, which holds, and its least bit and its top bit are in
    // range.
    let top = e + i128::from(63 - q.leading_zeros());
    if e < -1074 || top > 1023 {
        return None;
    }
    Some(Dyadic::<1>::from_f64(q as f64).shl(e as i64).to_f64(false))
}

// r^p for an odd r >= 3, if it is below 2^54, as `small_power` with the bound of `exact_near`.
fn small_power_near(r: u64, p: u64) -> Option<u64> {
    let mut q = 1;
    for _ in 0..p {
        let t = u128::from(q) * u128::from(r);
        if t >= 1 << 54 {
            return None;
        }
        q = t as u64;
    }
    Some(q)
}

// x^y rounded to nearest, ties to even, if x^y is an `f64` or the midpoint of two adjacent
// `f64`s, for a finite x > 0 other than 1 and a finite y != 0, and `None` otherwise. As in
// `exact`, whose argument this repeats, but a midpoint is q 2^e for an odd q < 2^54 and
// e >= -1075, so that the bound on the power is 2^54 and the least exponent -1075.
fn exact_near(x: f64, y: f64) -> Option<f64> {
    let (mut mx, mut ex) = odd_parts(x);
    let (my, ey) = odd_parts(y);
    // |y| >= 2^12 makes |ex y| >= 2^12 for mx = 1, as ex != 0, and mx^|y| >= 3^4096 > 2^54
    // otherwise.
    if ey > 11 {
        return None;
    }
    let (p, k) = if ey >= 0 { (my << ey, 0) } else { (my, -ey) };
    for _ in 0..k {
        let s = (mx as f64).sqrt() as u64;
        if ex % 2 != 0 || s * s != mx {
            return None;
        }
        mx = s;
        ex /= 2;
    }
    // x^y = mr^±p 2^(±p er) for the mr and er that are now mx and ex.
    let q = if mx == 1 {
        1
    } else if y < 0.0 {
        return None;
    } else {
        small_power_near(mx, p)?
    };
    let e = i128::from(ex) * i128::from(p);
    let e = if y < 0.0 { -e } else { e };
    // q 2^e is a midpoint or an `f64` if q < 2^54, which holds, and its least bit and its top
    // bit are in range.
    let top = e + i128::from(63 - q.leading_zeros());
    if e < -1075 || top > 1023 {
        return None;
    }
    // q 2^e is exact in one limb.
    let d: Dyadic<1> = round(false, &[q], e as i64, false, false);
    Some(d.to_f64_near())
}

// x^y = 2^k e^-w for a finite x > 0 and a finite y, as the header says, for |y ln x| < 2^13.
struct Pow(f64, f64);

impl Eval for Pow {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let (x, y) = (self.0, self.1);
        let (e, a, less) = reduce(&Dyadic::from_f64(x));
        // k = ceil(t / ln 2) up to the rounding of the estimate, which only has to be within
        // about 1 of it, as `scaled` takes w in [-ln 2, 2 - ln 2].
        let r = a.hi.to_f64(true) * LOG2_E;
        let c = y * (e as f64 + if less { -r } else { r });
        let k = to_k(c.ceil());
        let (h, l) = ln2::<N>();
        let z = Encl::point(k as f64).sub(&mul_int(&Encl::point(y), e));
        let zl = z.mul(&Encl { lo: h, hi: h }.add(&l));
        let ya = mul_f64(&a, y);
        let w = if less { zl.add(&ya) } else { zl.sub(&ya) };
        scaled(w, k, &h, &l)
    }
}

// The integer `c`, the ceiling that `Pow` takes. The rules before the loop keep |t| below
// 2^13, and so |c| below about 12,000, and this check keeps the proofs from having to show it.
fn to_k(c: f64) -> i64 {
    let k = c as i64;
    assert!(k.unsigned_abs() <= 1 << 14, "reduction out of range");
    k
}

// x^y = e^(y ln x) for a finite x > 0, as (h, l, e) with x^y 2^-e within 2^-67 of h + l,
// h = RN(h + l), 1/2 < h < 2 and e in [-1021, 1022], from t = y ln x in double-double and
// `fast_exp`, or `None` where t is out of the range of `fast_exp`. ln x is lh + ll within
// 17/16 2^-79 |ln x| (`ln_acc`), y lh is exact as th + `two_prod_err`, and so t = th + tl is
// within about 2^-69.4 of y ln x where |th| <= 709. `rocq/theories/FastPow.v` proves it, for
// 2^-60 <= |y ln x|, and for x = 1 and |y| <= 2^900, where t = 0 (`fast_pow_correct`).
fn fast_pow(x: f64, y: f64) -> Option<(f64, f64, i64)> {
    let (lh, ll) = ln_acc(x);
    let th = y * lh;
    let tl = two_prod_err::<HAS_FMA>(y, lh, th) + y * ll;
    fast_exp(th, tl)
}

// x^y rounded toward +∞ if `up` and toward -∞ otherwise, and to nearest, by the fast path, or
// `None` where its rounding test fails or y ln x is out of its range.
// `rocq/theories/FastPow.v` proves that they return those roundings (`fast_pow_dir_correct`
// and `fast_pow_near_correct`), and the same with and without an FMA (`fast_pow_dir_fma` and
// `fast_pow_near_fma`), with the hypotheses of `fast_pow_correct`.
fn fast_pow_dir(x: f64, y: f64, up: bool) -> Option<f64> {
    let (h, l, e) = fast_pow(x, y)?;
    round_dir_err(h, l, e, ERR67, up)
}

fn fast_pow_near(x: f64, y: f64) -> Option<f64> {
    let (h, l, e) = fast_pow(x, y)?;
    round_near_err(h, l, e, ERR67)
}

/// x^y rounded toward +∞ if `up` and toward -∞ otherwise, and NaN for a finite x < 0 and for
/// x = -∞, as the header says.
pub(crate) fn pow(x: f64, y: f64, up: bool) -> f64 {
    if y == 0.0 {
        1.0
    } else if x.is_nan() {
        x
    } else if y.is_nan() {
        if x == 1.0 {
            1.0
        } else {
            y
        }
    } else if x < 0.0 {
        f64::NAN
    } else if x == 1.0 {
        1.0
    } else if y.is_infinite() {
        // |x| < 1 or x > 1, where x is ±0 or positive.
        if (x > 1.0) == (y > 0.0) {
            f64::INFINITY
        } else {
            0.0
        }
    } else if x == 0.0 {
        // ±0 or ±∞, negative for x = -0 and an odd integer y.
        let r = if y < 0.0 { f64::INFINITY } else { 0.0 };
        if x.is_sign_negative() && is_odd_integer(y) {
            -r
        } else {
            r
        }
    } else if x == f64::INFINITY {
        if y > 0.0 {
            x
        } else {
            0.0
        }
    } else {
        // 2^s <= |y ln x| < 2^(s + 4), and x^y = e^(y ln x) is above 1 if y ln x > 0.
        let ey = expo(y);
        let s = ey + ln_expo(x);
        let above = (y > 0.0) == (x > 1.0);
        if s >= 10 {
            // |y ln x| >= 1024 > 1025 ln 2.
            if above {
                overflow(up)
            } else {
                underflow(up)
            }
        } else if s <= -58 {
            // |y ln x| < 2^-54, as exp's rule near 0.
            near_one(if above { 1.0 } else { -1.0 }, up)
        } else if let Some(v) = exact(x, y) {
            v
        } else if f64::from(y as i32) == y {
            // An integer y from -2^31 to 2^31 - 1: `y as i32` saturates, so that a y outside
            // that range or not an integer fails the test. Binary powering takes at most
            // 2 log2 |y| products of enclosures, and a quotient for y < 0, where `Pow`
            // evaluates a logarithm and an exponential, as the header says.
            pown_pos(x, y as i32, up)
        } else if let Some(v) = fast_pow_dir(x, y, up) {
            v
        } else {
            // The evaluation loses about the bits of |y a| + 1, and |y a| <= min(|t|, |y| / 2).
            let start = if ey.min(s + 4) >= POW_START_BITS {
                2
            } else {
                1
            };
            ziv(&Pow(x, y), up, start)
        }
    }
}

/// x^y rounded to nearest, ties to even, and NaN for a finite x < 0 and for x = -∞, as `pow`
/// takes them.
pub(crate) fn pow_near(x: f64, y: f64) -> f64 {
    if y == 0.0 {
        1.0
    } else if x.is_nan() {
        x
    } else if y.is_nan() {
        if x == 1.0 {
            1.0
        } else {
            y
        }
    } else if x < 0.0 {
        f64::NAN
    } else if x == 1.0 {
        1.0
    } else if y.is_infinite() {
        // |x| < 1 or x > 1, where x is ±0 or positive.
        if (x > 1.0) == (y > 0.0) {
            f64::INFINITY
        } else {
            0.0
        }
    } else if x == 0.0 {
        // ±0 or ±∞, negative for x = -0 and an odd integer y.
        let r = if y < 0.0 { f64::INFINITY } else { 0.0 };
        if x.is_sign_negative() && is_odd_integer(y) {
            -r
        } else {
            r
        }
    } else if x == f64::INFINITY {
        if y > 0.0 {
            x
        } else {
            0.0
        }
    } else {
        // 2^s <= |y ln x| < 2^(s + 4), and x^y = e^(y ln x) is above 1 if y ln x > 0.
        let ey = expo(y);
        let s = ey + ln_expo(x);
        let above = (y > 0.0) == (x > 1.0);
        if s >= 10 {
            // |y ln x| >= 1024 > 1025 ln 2.
            if above {
                f64::INFINITY
            } else {
                0.0
            }
        } else if s <= -58 {
            // |y ln x| < 2^-54, as the rule of `exp_near` near 0.
            1.0
        } else if let Some(v) = exact_near(x, y) {
            // The midpoints among them, which an enclosure settles only if they are one of its
            // bounds.
            v
        } else if f64::from(y as i32) == y {
            // An integer y from -2^31 to 2^31 - 1, as in `pow`.
            pown_pos_near(x, y as i32)
        } else if let Some(v) = fast_pow_near(x, y) {
            v
        } else {
            let start = if ey.min(s + 4) >= POW_START_BITS {
                2
            } else {
                1
            };
            ziv_near(&Pow(x, y), start)
        }
    }
}

// x^|n| for an enclosure of positive numbers x and n >= 1, by binary powering:
// x^n = (x^2)^(n / 2) times x for an odd n.
fn powi<const N: usize>(x: &Encl<N>, n: u32) -> Encl<N> {
    if n == 1 {
        *x
    } else {
        let r = powi(&x.mul(x), n / 2);
        if n % 2 == 1 {
            x.mul(&r)
        } else {
            r
        }
    }
}

// x^n for a finite x > 0 and n != 0.
struct Pown(f64, i32);

impl Eval for Pown {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let p = powi(&Encl::point(self.0), self.1.unsigned_abs());
        if self.1 < 0 {
            Encl::point(1.0).div(&p)
        } else {
            p
        }
    }
}

// x^n rounded toward +∞ if `up` and toward -∞ otherwise, for a finite x > 0 and n != 0. For
// x in [2^g, 2^(g + 1)), x^n is in [2^(g n), 2^((g + 1) n)) for n > 0, and in
// (2^((g + 1) n), 2^(g n)] for n < 0. |g n| < 2^42, so that the exponents of the kernel stay
// in range.
fn pown_pos(x: f64, n: i32, up: bool) -> f64 {
    let (g, n64) = (expo(x), i64::from(n));
    let (lo, hi) = if n > 0 {
        (g * n64, (g + 1) * n64)
    } else {
        ((g + 1) * n64, g * n64)
    };
    if lo >= 1024 {
        overflow(up)
    } else if hi <= -1075 {
        underflow(up)
    } else if let Some(v) = fast_pow_dir(x, f64::from(n), up) {
        v
    } else {
        let start = if n.unsigned_abs() >= 1 << POWN_START_BITS {
            2
        } else {
            1
        };
        ziv(&Pown(x, n), up, start)
    }
}

// x^n rounded to nearest, ties to even, for a finite x > 0 and n != 0, with the bounds of
// `pown_pos`.
fn pown_pos_near(x: f64, n: i32) -> f64 {
    let (g, n64) = (expo(x), i64::from(n));
    let (lo, hi) = if n > 0 {
        (g * n64, (g + 1) * n64)
    } else {
        ((g + 1) * n64, g * n64)
    };
    if lo >= 1024 {
        f64::INFINITY
    } else if hi <= -1075 {
        // x^n <= 2^-1075, whose tie goes to +0.
        0.0
    } else if let Some(v) = fast_pow_near(x, f64::from(n)) {
        v
    } else {
        let start = if n.unsigned_abs() >= 1 << POWN_START_BITS {
            2
        } else {
            1
        };
        ziv_near(&Pown(x, n), start)
    }
}

/// x^n rounded toward +∞ if `up` and toward -∞ otherwise.
pub(crate) fn pown(x: f64, n: i32, up: bool) -> f64 {
    if n == 0 {
        1.0
    } else if x.is_nan() {
        x
    } else if x == 0.0 || x.is_infinite() {
        // A zero or an infinity, negative for x < 0 or x = -0 and an odd n.
        let r = if (x == 0.0) == (n < 0) {
            f64::INFINITY
        } else {
            0.0
        };
        if x.is_sign_negative() && n % 2 != 0 {
            -r
        } else {
            r
        }
    } else if x < 0.0 && n % 2 != 0 {
        // (-x)^n rounded toward +∞ is -(x^n rounded toward -∞), and the other way round.
        -pown_pos(-x, n, !up)
    } else {
        pown_pos(x.abs(), n, up)
    }
}

/// x^n rounded to nearest, ties to even.
pub(crate) fn pown_near(x: f64, n: i32) -> f64 {
    if n == 0 {
        1.0
    } else if x.is_nan() {
        x
    } else if x == 0.0 || x.is_infinite() {
        // A zero or an infinity, negative for x < 0 or x = -0 and an odd n.
        let r = if (x == 0.0) == (n < 0) {
            f64::INFINITY
        } else {
            0.0
        };
        if x.is_sign_negative() && n % 2 != 0 {
            -r
        } else {
            r
        }
    } else if x < 0.0 && n % 2 != 0 {
        // Rounding to nearest is symmetric.
        -pown_pos_near(-x, n)
    } else {
        pown_pos_near(x.abs(), n)
    }
}
