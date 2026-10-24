// A portable backend that does not depend on the dynamic rounding mode.
//
// Every operation that rounds upward (or downward) is computed in the default
// rounding mode (round-to-nearest, ties-to-even) and then corrected: the exact
// error of the rounded result is obtained with an error-free transformation, and
// if the exact result is above (below) the rounded one, the result is moved up
// (down) by one ulp. This relies only on IEEE 754 round-to-nearest arithmetic, so
// the floating-point environment must not be changed by the caller.
//
// Each error-free transformation is only valid under some no-underflow and
// no-overflow hypotheses. The fast paths check them lane by lane with integer
// comparisons of the exponents, and lanes that fail are recomputed by a slow path
// that uses exact integer arithmetic.
//
// References:
//
// - [Knuth] D. E. Knuth, The Art of Computer Programming, Vol. 2, 3rd ed., 1998,
//   Section 4.2.2, Theorem B (TwoSum).
// - [Dekker] T. J. Dekker, A floating-point technique for extending the available
//   precision, Numer. Math. 18 (1971) (Veltkamp splitting and TwoProduct).
// - [Boldo06] S. Boldo, Pitfalls of a full floating-point proof: example on the
//   formal proof of the Veltkamp/Dekker algorithms, IJCAR 2006 (TwoProduct is
//   exact if e_a + e_b >= e_min + p - 1 and nothing overflows).
// - [BD03] S. Boldo and M. Daumas, Representable correcting terms for possibly
//   underflowing floating point operations, ARITH 16, 2003 (the remainders of
//   division and square root are representable).
// - [BGM17] S. Boldo, S. Graillat and J.-M. Muller, On the robustness of the 2Sum
//   and Fast2Sum algorithms, ACM TOMS 44(1), 2017 (TwoSum is exact even if
//   underflow occurs).
// - [BM08] S. Boldo and G. Melquiond, Emulation of a FMA and correctly rounded
//   sums: proved algorithms using rounding to odd, IEEE TC 57(4), 2008.
// - [BM11] S. Boldo and J.-M. Muller, Exact and approximated error of the FMA,
//   IEEE TC 60(2), 2011.

use std::cmp::Ordering;

pub(crate) const HAS_MAXIMUM: bool = true;

pub(crate) type F64X2 = [f64; 2];

cfg_if::cfg_if! {
    // Whether `f64::mul_add` compiles to a single hardware instruction.
    // On other targets it is a (correct but slow) software routine, and
    // Dekker's algorithm is used instead.
    if #[cfg(any(
        all(any(target_arch = "x86", target_arch = "x86_64"), target_feature = "fma"),
        target_arch = "aarch64",
        all(any(target_arch = "riscv32", target_arch = "riscv64"), target_feature = "d"),
        target_arch = "powerpc64",
        target_arch = "s390x",
    ))] {
        const HAS_FMA: bool = true;
    } else {
        const HAS_FMA: bool = false;
    }
}

pub(crate) fn abs(x: F64X2) -> F64X2 {
    [x[0].abs(), x[1].abs()]
}

/// `add_rn([x0, x1], [y0, y1]) = [x0 + y0, x1 + y1]` rounded to nearest.
pub(crate) fn add_rn(x: F64X2, y: F64X2) -> F64X2 {
    [x[0] + y[0], x[1] + y[1]]
}

/// `add_ru([x0, x1], [y0, y1]) = [x0 + y0, x1 + y1]` rounded toward +∞.
pub(crate) fn add_ru(x: F64X2, y: F64X2) -> F64X2 {
    lanewise2(x, y, add1_ru_fast, add1_ru_slow)
}

pub(crate) fn all(x: F64X2) -> bool {
    bitmask(x) == 3
}

pub(crate) fn and(x: F64X2, y: F64X2) -> F64X2 {
    [
        f64::from_bits(x[0].to_bits() & y[0].to_bits()),
        f64::from_bits(x[1].to_bits() & y[1].to_bits()),
    ]
}

pub(crate) fn any(x: F64X2) -> bool {
    bitmask(x) != 0
}

pub(crate) fn bitmask(x: F64X2) -> u32 {
    (x[0].to_bits() >> 63) as u32 | ((x[1].to_bits() >> 63) as u32) << 1
}

pub(crate) fn ceil(x: F64X2) -> F64X2 {
    [x[0].ceil(), x[1].ceil()]
}

pub(crate) fn constant(x: f64, y: f64) -> F64X2 {
    [x, y]
}

/// `div_ru([x0, x1], [y0, y1]) = [x0 / y0, x1 / y1]` rounded toward +∞.
pub(crate) fn div_ru(x: F64X2, y: F64X2) -> F64X2 {
    div_ru_impl::<HAS_FMA>(x, y)
}

pub(crate) fn eq(x: F64X2, y: F64X2) -> F64X2 {
    [mask(x[0] == y[0]), mask(x[1] == y[1])]
}

pub(crate) fn extract(x: F64X2) -> [f64; 2] {
    x
}

pub(crate) fn extract0(x: F64X2) -> f64 {
    x[0]
}

pub(crate) fn extract1(x: F64X2) -> f64 {
    x[1]
}

pub(crate) fn floor(x: F64X2) -> F64X2 {
    [x[0].floor(), x[1].floor()]
}

pub(crate) fn ge(x: F64X2, y: F64X2) -> F64X2 {
    [mask(x[0] >= y[0]), mask(x[1] >= y[1])]
}

pub(crate) fn gt(x: F64X2, y: F64X2) -> F64X2 {
    [mask(x[0] > y[0]), mask(x[1] > y[1])]
}

/// `hadd_rn([x0, x1], [y0, y1]) = [x0 + x1, y0 + y1]` rounded to nearest.
pub(crate) fn hadd_rn(x: F64X2, y: F64X2) -> F64X2 {
    [x[0] + x[1], y[0] + y[1]]
}

pub(crate) fn le(x: F64X2, y: F64X2) -> F64X2 {
    [mask(x[0] <= y[0]), mask(x[1] <= y[1])]
}

pub(crate) fn lt(x: F64X2, y: F64X2) -> F64X2 {
    [mask(x[0] < y[0]), mask(x[1] < y[1])]
}

// The vector version of the `maximumNumber` operation defined in IEEE 754-2019,
// which does not propagate NaNs. Same as `vmaxnmq_f64` on AArch64.
pub(crate) fn max(x: F64X2, y: F64X2) -> F64X2 {
    [max1(x[0], y[0]), max1(x[1], y[1])]
}

// The vector version of the `maximum` operation defined in IEEE 754-2019,
// which propagates NaNs. Same as `vmaxq_f64` on AArch64.
pub(crate) fn maximum(x: F64X2, y: F64X2) -> F64X2 {
    [maximum1(x[0], y[0]), maximum1(x[1], y[1])]
}

pub(crate) fn min(x: F64X2, y: F64X2) -> F64X2 {
    [min1(x[0], y[0]), min1(x[1], y[1])]
}

pub(crate) fn minimum(x: F64X2, y: F64X2) -> F64X2 {
    [minimum1(x[0], y[0]), minimum1(x[1], y[1])]
}

/// `mul_add_ru([x0, x1], [y0, y1], [z0, z1]) = [x0 * y0 + z0, x1 * y1 + z1]`
/// rounded toward +∞ (with a single rounding).
pub(crate) fn mul_add_ru(x: F64X2, y: F64X2, z: F64X2) -> F64X2 {
    mul_add_ru_impl::<HAS_FMA>(x, y, z)
}

/// `mul_ru([x0, x1], [y0, y1]) = [x0 * y0, x1 * y1]` rounded toward +∞.
pub(crate) fn mul_ru(x: F64X2, y: F64X2) -> F64X2 {
    mul_ru_impl::<HAS_FMA>(x, y)
}

// `rocq/theories/Model.v` transcribes this function for the proof of `sub_ru`.
pub(crate) fn neg(x: F64X2) -> F64X2 {
    [-x[0], -x[1]]
}

/// `neg0([x0, x1]) = [-x0, x1]`
pub(crate) fn neg0(x: F64X2) -> F64X2 {
    [-x[0], x[1]]
}

pub(crate) fn or(x: F64X2, y: F64X2) -> F64X2 {
    [
        f64::from_bits(x[0].to_bits() | y[0].to_bits()),
        f64::from_bits(x[1].to_bits() | y[1].to_bits()),
    ]
}

pub(crate) fn round(x: F64X2) -> F64X2 {
    [x[0].round(), x[1].round()]
}

pub(crate) fn round_ties_even(x: F64X2) -> F64X2 {
    [round_ties_even1(x[0]), round_ties_even1(x[1])]
}

/// `shuffle02([x0, x1], [x2, x3]) = [x0, x2]`
pub(crate) fn shuffle02(x: F64X2, y: F64X2) -> F64X2 {
    [x[0], y[0]]
}

/// `shuffle03([x0, x1], [x2, x3]) = [x0, x3]`
pub(crate) fn shuffle03(x: F64X2, y: F64X2) -> F64X2 {
    [x[0], y[1]]
}

/// `shuffle13([x0, x1], [x2, x3]) = [x1, x3]`
pub(crate) fn shuffle13(x: F64X2, y: F64X2) -> F64X2 {
    [x[1], y[1]]
}

pub(crate) fn splat(x: f64) -> F64X2 {
    [x, x]
}

/// `sqrt_rd_ru([x0, x1]) = [√x0, √x1]`, the first rounded toward -∞ and the
/// second toward +∞.
pub(crate) fn sqrt_rd_ru(x: F64X2) -> F64X2 {
    [sqrt1_rd(x[0]), sqrt1_ru(x[1])]
}

/// `sqrt1_rd(x) = √x` rounded toward -∞.
pub(crate) fn sqrt1_rd(x: f64) -> f64 {
    sqrt1_rd_impl::<HAS_FMA>(x)
}

/// `sqrt1_ru(x) = √x` rounded toward +∞.
pub(crate) fn sqrt1_ru(x: f64) -> f64 {
    sqrt1_ru_impl::<HAS_FMA>(x)
}

/// `sub_rn([x0, x1], [y0, y1]) = [x0 - y0, x1 - y1]` rounded to nearest.
pub(crate) fn sub_rn(x: F64X2, y: F64X2) -> F64X2 {
    [x[0] - y[0], x[1] - y[1]]
}

/// `sub_ru([x0, x1], [y0, y1]) = [x0 - y0, x1 - y1]` rounded toward +∞.
pub(crate) fn sub_ru(x: F64X2, y: F64X2) -> F64X2 {
    // x - y is defined as x + (-y) by IEEE 754, including the signs of zeros.
    // Proved correct in `rocq/theories/SubRu.v`. `rocq/theories/Model.v` transcribes
    // this function, so it has to be updated along with it.
    add_ru(x, neg(y))
}

/// `sub1_ru(x, y) = x - y` rounded toward +∞.
pub(crate) fn sub1_ru(x: f64, y: f64) -> f64 {
    // Proved correct in `rocq/theories/SubRu.v`. `rocq/theories/Model.v` transcribes
    // this function, so it has to be updated along with it.
    let (r, ok) = add1_ru_fast(x, -y);
    if ok {
        r
    } else {
        add1_ru_slow(x, -y)
    }
}

pub(crate) fn swap(x: F64X2) -> F64X2 {
    [x[1], x[0]]
}

pub(crate) fn trunc(x: F64X2) -> F64X2 {
    [x[0].trunc(), x[1].trunc()]
}

// The implementations below take `FMA` as a parameter, so that the variant for
// targets without FMA can be tested on targets with it. `FMA` must be false on
// targets where `f64::mul_add` is not a hardware instruction, as it would be
// slow, but it would still be correct.

pub(super) fn div_ru_impl<const FMA: bool>(x: F64X2, y: F64X2) -> F64X2 {
    lanewise2(x, y, div1_ru_fast::<FMA>, div1_ru_slow)
}

pub(super) fn mul_add_ru_impl<const FMA: bool>(x: F64X2, y: F64X2, z: F64X2) -> F64X2 {
    let (r0, ok0) = mul_add1_ru_fast::<FMA>(x[0], y[0], z[0]);
    let (r1, ok1) = mul_add1_ru_fast::<FMA>(x[1], y[1], z[1]);
    if ok0 && ok1 {
        [r0, r1]
    } else {
        [
            if ok0 {
                r0
            } else {
                mul_add1_ru_slow(x[0], y[0], z[0])
            },
            if ok1 {
                r1
            } else {
                mul_add1_ru_slow(x[1], y[1], z[1])
            },
        ]
    }
}

pub(super) fn mul_ru_impl<const FMA: bool>(x: F64X2, y: F64X2) -> F64X2 {
    lanewise2(x, y, mul1_ru_fast::<FMA>, mul1_ru_slow)
}

pub(super) fn sqrt1_rd_impl<const FMA: bool>(x: f64) -> f64 {
    let (s, r, ok) = sqrt1_fast::<FMA>(x);
    if ok {
        // √x < s ⟺ x - s² < 0. Then s > 0, and the result is its predecessor.
        if r < 0.0 {
            step_down(s)
        } else {
            s
        }
    } else {
        sqrt1_slow(x, sqrt1_rd_impl::<FMA>)
    }
}

pub(super) fn sqrt1_ru_impl<const FMA: bool>(x: f64) -> f64 {
    let (s, r, ok) = sqrt1_fast::<FMA>(x);
    if ok {
        // √x > s ⟺ x - s² > 0.
        if r > 0.0 {
            step_up(s)
        } else {
            s
        }
    } else {
        sqrt1_slow(x, sqrt1_ru_impl::<FMA>)
    }
}

// Applies `fast` to each lane, and falls back to `slow` for the lanes where the
// fast path is not valid. The common case is a single, well-predicted branch.
// `rocq/theories/Model.v` transcribes this function for the proofs of `add_ru` and
// `mul_ru`.
fn lanewise2(
    x: F64X2,
    y: F64X2,
    fast: impl Fn(f64, f64) -> (f64, bool),
    slow: impl Fn(f64, f64) -> f64,
) -> F64X2 {
    let (r0, ok0) = fast(x[0], y[0]);
    let (r1, ok1) = fast(x[1], y[1]);
    if ok0 && ok1 {
        [r0, r1]
    } else {
        [
            if ok0 { r0 } else { slow(x[0], y[0]) },
            if ok1 { r1 } else { slow(x[1], y[1]) },
        ]
    }
}

fn mask(b: bool) -> f64 {
    f64::from_bits(if b { !0 } else { 0 })
}

fn max1(x: f64, y: f64) -> f64 {
    if x.is_nan() {
        y
    } else if y.is_nan() {
        x
    } else if x == 0.0 && y == 0.0 {
        // max(-0, +0) = +0: the sign bit is set only if both are set.
        f64::from_bits(x.to_bits() & y.to_bits())
    } else if x > y {
        x
    } else {
        y
    }
}

fn maximum1(x: f64, y: f64) -> f64 {
    if x.is_nan() || y.is_nan() {
        f64::NAN
    } else {
        max1(x, y)
    }
}

fn min1(x: f64, y: f64) -> f64 {
    if x.is_nan() {
        y
    } else if y.is_nan() {
        x
    } else if x == 0.0 && y == 0.0 {
        // min(-0, +0) = -0: the sign bit is set if either is set.
        f64::from_bits(x.to_bits() | y.to_bits())
    } else if x < y {
        x
    } else {
        y
    }
}

fn minimum1(x: f64, y: f64) -> f64 {
    if x.is_nan() || y.is_nan() {
        f64::NAN
    } else {
        min1(x, y)
    }
}

fn round_ties_even1(x: f64) -> f64 {
    // 2^52: every f64 of magnitude >= 2^52 is an integer.
    const TWO_POW_52: f64 = 4503599627370496.0;
    if x.abs() < TWO_POW_52 {
        // |x| + 2^52 is in [2^52, 2^53), where the ulp is 1, so the addition
        // rounds |x| to an integer, ties to even. Subtracting 2^52 is exact.
        // `copysign` restores the sign, including that of zero (e.g., -0.3 ↦ -0).
        ((x.abs() + TWO_POW_52) - TWO_POW_52).copysign(x)
    } else {
        // Integers, ±∞ and NaN.
        x
    }
}

// Error-free transformations and helpers.

// The unbiased exponent of x: floor(log2(|x|)) if x is normal, -1023 if x is zero
// or subnormal, and 1024 if x is infinite or NaN.
fn exponent(x: f64) -> i32 {
    ((x.to_bits() >> 52) & 0x7ff) as i32 - 1023
}

/// Returns the successor of x, which must be finite.
/// This is `nextUp` of IEEE 754 (`f64::next_up` needs Rust 1.86).
fn step_up(x: f64) -> f64 {
    // The bit patterns of the finite floats of one sign are consecutive integers,
    // so moving toward +∞ means incrementing the magnitude if x > 0, and
    // decrementing it if x < 0. MAX steps to +∞, -2^-1074 steps to -0, and ±0 to
    // 2^-1074. The fast paths also step zeros that underflowed, but then discard
    // the result.
    let b = x.to_bits();
    f64::from_bits(if x > 0.0 {
        b + 1
    } else if x < 0.0 {
        b - 1
    } else {
        1
    })
}

/// Returns the predecessor of x, which must be finite.
fn step_down(x: f64) -> f64 {
    -step_up(-x)
}

/// Returns the error e = (x + y) - s, where s = RN(x + y). [Knuth]
///
/// e is exact as long as no intermediate computation overflows, even if underflow
/// occurs [BGM17]. No overflow can occur if |x|, |y| < 2^1023 and s is finite:
/// then |s - y| <= |x| + ulp(s)/2 and |s - a'| <= |y| + |x - a'| stay below MAX.
/// Otherwise s - y can overflow: for x = -MAX and y = 3 * 2^970, x + y is a tie
/// that rounds to s = -(MAX - 2^971), and s - y = -(MAX + 2^970) rounds to -∞.
fn two_sum_err(x: f64, y: f64, s: f64) -> f64 {
    let a = s - y;
    let b = s - a;
    (x - a) + (y - b)
}

/// Splits x into x_hi + x_lo, each with at most 26 significant bits. [Dekker]
///
/// Requires |x| < 2^996, so that `C * x` does not overflow.
fn split(x: f64) -> (f64, f64) {
    // 2^27 + 1.
    const C: f64 = 134217729.0;
    let t = C * x;
    let hi = t - (t - x);
    (hi, x - hi)
}

/// Returns the error e = x * y - p, where p = RN(x * y).
///
/// e is exact if e_x + e_y >= -970, where e_x and e_y are the exponents of the
/// (normalized or subnormal) representations of x and y, and nothing overflows
/// [BM11, Section 2.3], [Boldo06]. Since |x * y| < 2^(e_x + e_y + 2), the first
/// condition holds if |p| >= 2^-968. Dekker's variant additionally requires
/// |x|, |y| < 2^996 (for `split`) and |p| < 2^1023 (so that x_hi * y_hi, which
/// may exceed |x * y| by a factor of 1 + 2^-25, does not overflow).
fn two_prod_err<const FMA: bool>(x: f64, y: f64, p: f64) -> f64 {
    if FMA {
        x.mul_add(y, -p)
    } else {
        let (xh, xl) = split(x);
        let (yh, yl) = split(y);
        ((xh * yh - p) + xh * yl + xl * yh) + xl * yl
    }
}

// Whether `two_prod_err::<FMA>(x, y, x * y)` is exact. See `two_prod_err`.
fn two_prod_is_exact<const FMA: bool>(x: f64, y: f64, p: f64) -> bool {
    let ep = exponent(p);
    if FMA {
        (-968..=1023).contains(&ep)
    } else {
        (-968..=1022).contains(&ep) && exponent(x) <= 995 && exponent(y) <= 995
    }
}

fn is_finite(x: f64) -> bool {
    exponent(x) < 1024
}

// Returns RN(x + y) rounded to odd instead: if x + y is not representable, the
// neighbor of it whose integral significand is odd. [BM08, Section III]
fn add_odd(x: f64, y: f64) -> f64 {
    let s = x + y;
    let e = two_sum_err(x, y, s);
    if e != 0.0 && s.to_bits() & 1 == 0 {
        // s is inexact, so it is nonzero, and x + y lies strictly between s and
        // its neighbor on the side of e, whose bit pattern is odd (patterns of
        // adjacent floats of the same sign differ by one).
        let b = s.to_bits();
        let toward_larger_magnitude = (e > 0.0) == (s > 0.0);
        f64::from_bits(if toward_larger_magnitude {
            b + 1
        } else {
            b - 1
        })
    } else {
        s
    }
}

/// Returns RN(a * b + c), given (u1, u2) = TwoProduct(a, b), without an FMA.
/// [BM08, Algorithm 1 and Theorem 4]:
///
///   (t1, t2) = TwoSum(c, u1)
///   v = RO(t2 + u2)
///   r = RN(t1 + v)
///
/// gives r = RN(a * b + c), provided that u2 is the exact error of u1 and nothing
/// overflows. RO is rounding to odd; with RN instead, r would be double rounded.
pub(super) fn mul_add1_rn_emulated(u1: f64, u2: f64, c: f64) -> f64 {
    let t1 = c + u1;
    let t2 = two_sum_err(c, u1, t1);
    t1 + add_odd(t2, u2)
}

// Fast paths. Each returns the result and whether it is valid.

// Proved correct in `rocq/theories/AddRu.v`. `rocq/theories/Model.v` transcribes this
// function and the ones it calls, so it has to be updated along with them.
fn add1_ru_fast(x: f64, y: f64) -> (f64, bool) {
    let s = x + y;
    let e = two_sum_err(x, y, s);
    let finite = is_finite(x) && is_finite(y);
    // If x or y is ±∞ or NaN, s is the exact result (±∞ or NaN).
    // Otherwise, e is exact if |x|, |y| < 2^1023 and s is finite (see `two_sum_err`).
    // If s overflows, the slow path decides between +∞ and -MAX.
    let ok = !finite || (exponent(x) <= 1022 && exponent(y) <= 1022 && is_finite(s));
    // If e > 0, then s is inexact and thus nonzero.
    // If e = 0, the sum is exact, and the sign of a zero sum is the same in both
    // rounding modes, except toward -∞ (x + (-x) = +0).
    let r = if finite && e > 0.0 { step_up(s) } else { s };
    (r, ok)
}

// Proved correct in `rocq/theories/MulRu.v` for both values of `FMA`.
// `rocq/theories/Model.v` transcribes this function and the ones it calls, so it has to
// be updated along with them.
fn mul1_ru_fast<const FMA: bool>(x: f64, y: f64) -> (f64, bool) {
    let p = x * y;
    let e = two_prod_err::<FMA>(x, y, p);
    // If x or y is ±0, ±∞ or NaN, p is the exact result (with the exact sign).
    let special = !(is_finite(x) && is_finite(y)) || x == 0.0 || y == 0.0;
    // Otherwise, p underflows or overflows unless the checks pass: the slow path
    // handles both.
    let ok = special || two_prod_is_exact::<FMA>(x, y, p);
    let r = if !special && e > 0.0 { step_up(p) } else { p };
    (r, ok)
}

fn div1_ru_fast<const FMA: bool>(x: f64, y: f64) -> (f64, bool) {
    let q = x / y;
    // If x or y is ±0, ±∞ or NaN, q is the exact result: ±0, ±∞ (including x/±0
    // for x ≠ 0) or NaN.
    let special = !(is_finite(x) && is_finite(y)) || x == 0.0 || y == 0.0;
    // Otherwise, the remainder r = x - q * y is a floating-point number [BD03] if
    // q is normal and e_q + e_y >= -970. Since |q * y| >= |x| / (1 + 2^-52) and
    // |q * y| < 2^(e_q + e_y + 2), the latter holds if |x| >= 2^-967.
    let exact = (-1022..=1023).contains(&exponent(q)) && exponent(x) >= -967;
    let (r, ok) = if FMA {
        // r is representable, so the FMA computes it exactly.
        ((-q).mul_add(y, x), special || exact)
    } else {
        // (p, e) = TwoProduct(q, y), then r = (x - p) - e. x - p is exact by
        // Sterbenz's lemma, as p = RN(q * y) is within a factor 2 of x. The last
        // subtraction is exact as r is representable. TwoProduct needs
        // |q|, |y| < 2^996 and |p| < 2^1023; the last holds if |x| < 2^1022.
        let p = q * y;
        let dekker = exponent(q) <= 995 && exponent(y) <= 995 && exponent(x) <= 1021;
        (
            (x - p) - two_prod_err::<false>(q, y, p),
            special || exact && dekker,
        )
    };
    // x / y > q ⟺ r / y > 0.
    let up = r != 0.0 && (r > 0.0) == (y > 0.0);
    let res = if !special && up { step_up(q) } else { q };
    (res, ok)
}

fn mul_add1_ru_fast<const FMA: bool>(a: f64, b: f64, c: f64) -> (f64, bool) {
    // Algorithm ErrFma [BM11, Algorithm 4 and Theorem 2]:
    //
    //   r1 = RN(a * b + c)
    //   (u1, u2) = TwoProduct(a, b)
    //   (α1, α2) = TwoSum(c, u2)
    //   (β1, β2) = TwoSum(u1, α1)
    //   γ = RN(RN(β1 - r1) + β2)
    //
    // Then a * b + c = r1 + γ + α2 exactly, provided that nothing overflows and
    //
    //   - r1 = 0 or r1 is normal,
    //   - u1 = 0 or |u1| >= 2^-1021,
    //   - α1 = 0 or |α1| >= 2^-1021,
    //   - β1 = 0 or |β1| >= 2^-1020,
    //   - u2 is the exact error of u1 (see `two_prod_err`).
    //
    // The error of r1 is γ + α2, whose sign is that of RN(γ + α2), since the sum
    // of two floats rounds to zero only if it is exactly zero.
    let u1 = a * b;
    let u2 = two_prod_err::<FMA>(a, b, u1);
    let r1 = if FMA {
        a.mul_add(b, c)
    } else {
        mul_add1_rn_emulated(u1, u2, c)
    };
    let alpha1 = c + u2;
    let alpha2 = two_sum_err(c, u2, alpha1);
    let beta1 = u1 + alpha1;
    let beta2 = two_sum_err(u1, alpha1, beta1);
    let gamma = (beta1 - r1) + beta2;
    let err = gamma + alpha2;

    // Cases where a or b is ±0, or any input is ±∞ or NaN (see `mul_add1_special`).
    let special = !(is_finite(a) && is_finite(b) && is_finite(c)) || a == 0.0 || b == 0.0;
    // The `not_tiny` checks are the underflow hypotheses of [BM11, Theorem 2].
    // `differential_tests` reaches each of them, and dropping them causes no
    // mismatch there. A likely reason is that if TwoProduct is exact, all values
    // are multiples of 2^-1074, and so a sum of them below 2^-1021 is exact. That
    // is not a proof, so they are kept.
    let not_tiny = |x: f64, e_min: i32| x == 0.0 || exponent(x) >= e_min;
    // No overflow: if |u1|, |c| < 2^1022, then |α1|, |β1| < 2^1023 and each TwoSum
    // is exact (see `two_sum_err`). If r1 overflows, the slow path decides between
    // +∞ and -MAX.
    let ok = special
        || two_prod_is_exact::<FMA>(a, b, u1)
            && exponent(u1) <= 1021
            && exponent(c) <= 1021
            && is_finite(r1)
            && not_tiny(r1, -1022)
            && not_tiny(alpha1, -1021)
            && not_tiny(beta1, -1020);
    let r = if special {
        // The emulated r1 can be NaN in these cases, as TwoSum does not handle ±∞.
        mul_add1_special(a, b, c)
    } else if err > 0.0 {
        // r1 is inexact and thus nonzero.
        step_up(r1)
    } else {
        r1
    };
    (r, ok)
}

// Returns (s, r, ok), where s = RN(√x) and r has the sign of x - s².
fn sqrt1_fast<const FMA: bool>(x: f64) -> (f64, f64, bool) {
    let s = x.sqrt();
    // x - s² is representable if 2 e_s >= -970 [BD03], which holds if x >= 2^-966.
    // The check also excludes ±0, +∞ and NaN, but not negative numbers, for which
    // s and r are NaN, and NaN is returned.
    let ex = exponent(x);
    let (r, ok) = if FMA {
        ((-s).mul_add(s, x), (-966..=1023).contains(&ex))
    } else {
        // x - p is exact by Sterbenz's lemma, and so is the last subtraction.
        // s < 2^512, so `split` does not overflow, but p = RN(s²) and s_hi²
        // do if x is close to MAX, hence x < 2^1022.
        let p = s * s;
        (
            (x - p) - two_prod_err::<false>(s, s, p),
            (-966..=1021).contains(&ex),
        )
    };
    (s, r, ok)
}

// Slow paths.

// Proved correct in `rocq/theories/AddRu.v`, as is `add_ru`. `rocq/theories/Model.v`
// transcribes this function and the ones it calls, `lanewise2` and `add_ru`, so it
// has to be updated along with them.
#[cold]
fn add1_ru_slow(x: f64, y: f64) -> f64 {
    if !(is_finite(x) && is_finite(y)) || x == 0.0 || y == 0.0 {
        // Exact: ±∞, NaN, x, y, or a sum of zeros (see `add1_ru_fast`).
        return x + y;
    }
    let (sx, mx, ex) = decompose(x);
    let (sy, my, ey) = decompose(y);
    sum_round_up(sx, mx as u128, ex, sy, my as u128, ey)
}

// Proved correct in `rocq/theories/MulRu.v`, as is `mul_ru`. `rocq/theories/Model.v`
// transcribes this function and the ones it calls, `mul_ru_impl` and `mul_ru`, so it
// has to be updated along with them.
#[cold]
fn mul1_ru_slow(x: f64, y: f64) -> f64 {
    if !(is_finite(x) && is_finite(y)) || x == 0.0 || y == 0.0 {
        return x * y;
    }
    let (sx, mx, ex) = decompose(x);
    let (sy, my, ey) = decompose(y);
    round_up_exact(sx != sy, mx as u128 * my as u128, ex + ey, false)
}

#[cold]
fn div1_ru_slow(x: f64, y: f64) -> f64 {
    if !(is_finite(x) && is_finite(y)) || x == 0.0 || y == 0.0 {
        return x / y;
    }
    let (sx, mx, ex) = decompose(x);
    let (sy, my, ey) = decompose(y);
    // Normalize my to [2^52, 2^53) and mx to [2^126, 2^127), so that the integer
    // quotient has at least 74 bits, more than the 54 needed for rounding.
    let ny = my << (my.leading_zeros() - 11);
    let ey = ey - (my.leading_zeros() as i32 - 11);
    let nx = (mx as u128) << (mx.leading_zeros() + 64 - 1);
    let ex = ex - (mx.leading_zeros() as i32 + 64 - 1);
    let q = nx / ny as u128;
    let rem = nx % ny as u128;
    // x / y lies strictly between q and q + 1 (in units of 2^(ex - ey)) iff rem ≠ 0.
    round_up_exact(sx != sy, q, ex - ey, rem != 0)
}

// Returns a * b + c (exactly) where a or b is ±0, or any input is ±∞ or NaN.
fn mul_add1_special(a: f64, b: f64, c: f64) -> f64 {
    if is_finite(a) && is_finite(b) && !is_finite(c) {
        // a * b is finite, even though RN(a * b) may overflow.
        c
    } else {
        // a * b is an exact ±0, ±∞ or NaN, and adding c to it is exact. The sign
        // of a zero result follows the rules for addition, which are the same for
        // rounding to nearest and toward +∞. This is not contracted into an FMA.
        a * b + c
    }
}

#[cold]
fn mul_add1_ru_slow(a: f64, b: f64, c: f64) -> f64 {
    if !(is_finite(a) && is_finite(b) && is_finite(c)) || a == 0.0 || b == 0.0 {
        return mul_add1_special(a, b, c);
    }
    if c == 0.0 {
        // a * b is nonzero, so a * b + (±0) = a * b.
        return mul1_ru_slow(a, b);
    }
    let (sa, ma, ea) = decompose(a);
    let (sb, mb, eb) = decompose(b);
    let (sc, mc, ec) = decompose(c);
    sum_round_up(
        sa != sb,
        ma as u128 * mb as u128,
        ea + eb,
        sc,
        mc as u128,
        ec,
    )
}

// Computes √x for x that `sqrt1_fast` rejects, using `f` for positive numbers,
// which are scaled into the range of the fast path.
#[cold]
fn sqrt1_slow(x: f64, f: fn(f64) -> f64) -> f64 {
    // Powers of two, so the divisions are exact.
    const TWO_POW_64: f64 = 18446744073709551616.0;
    const TWO_POW_M64: f64 = 1.0 / TWO_POW_64;
    const TWO_POW_128: f64 = TWO_POW_64 * TWO_POW_64;
    const TWO_POW_M128: f64 = 1.0 / TWO_POW_128;
    if x > 0.0 && is_finite(x) {
        if exponent(x) < 0 {
            // x < 2^-966. Scaling by 2^128 is exact and gives x >= 2^-946, which
            // the fast path accepts. The result is >= 2^-473, so scaling it back
            // by 2^-64 is exact too (>= 2^-537, normal), and commutes with the
            // rounding.
            f(x * TWO_POW_128) * TWO_POW_M64
        } else {
            // x >= 2^1022 (Dekker's variant only). Scaling by 2^-128 is exact,
            // and so is scaling the result (< 2^448) back by 2^64.
            f(x * TWO_POW_M128) * TWO_POW_64
        }
    } else {
        // Exact: ±0 (√-0 = -0), +∞ and NaN (including √x for x < 0).
        x.sqrt()
    }
}

// Returns (sign, m, e) such that x = (-1)^sign * m * 2^e, where x is finite and
// nonzero.
fn decompose(x: f64) -> (bool, u64, i32) {
    let b = x.to_bits();
    let biased = ((b >> 52) & 0x7ff) as i32;
    let frac = b & ((1 << 52) - 1);
    if biased == 0 {
        // Subnormal.
        (b >> 63 != 0, frac, -1074)
    } else {
        (b >> 63 != 0, frac | (1 << 52), biased - 1075)
    }
}

// Returns (-1)^sx * mx * 2^ex + (-1)^sy * my * 2^ey rounded toward +∞, where
// mx, my ∈ [1, 2^106).
fn sum_round_up(sx: bool, mx: u128, ex: i32, sy: bool, my: u128, ey: i32) -> f64 {
    // Normalize both significands to [2^125, 2^126).
    let norm = |m: u128, e: i32| {
        let sh = m.leading_zeros() - 2;
        (m << sh, e - sh as i32)
    };
    let (mx, ex) = norm(mx, ex);
    let (my, ey) = norm(my, ey);
    // Order by magnitude: X is the larger one.
    let ((sx, mx, ex), (sy, my, ey)) = match (ex, mx).cmp(&(ey, my)) {
        Ordering::Less => ((sy, my, ey), (sx, mx, ex)),
        _ => ((sx, mx, ex), (sy, my, ey)),
    };
    // Align Y to X's exponent. The bits shifted out of Y are replaced by a sticky
    // bit: Y = (y + δ) * 2^ex with an integer y and 0 <= δ < 1, δ > 0 iff sticky.
    let d = (ex - ey) as u32;
    let (y, sticky) = if d >= 128 {
        (0, true)
    } else {
        (my >> d, my & ((1 << d) - 1) != 0)
    };
    let m = if sx == sy {
        // (mx + y + δ) * 2^ex. mx + y < 2^127.
        mx + y
    } else {
        // (mx - y - δ) * 2^ex = (mx - y - 1 + (1 - δ)) * 2^ex if δ > 0, where
        // 0 < 1 - δ < 1. Since X is the larger, mx - y - δ >= 0.
        mx - y - sticky as u128
    };
    if m == 0 {
        // Exact cancellation, which gives +0 in all rounding modes but toward -∞.
        // m = 0 with sticky set is impossible: the inputs have at most 106
        // significant bits, so after normalization the lowest 20 bits of my are
        // zero, and sticky implies d > 20, hence y < 2^105 and m > 2^124.
        debug_assert!(!sticky);
        return 0.0;
    }
    round_up_exact(sx, m, ex, sticky)
}

// Returns (-1)^neg * (m + δ) * 2^e rounded toward +∞, where m > 0, and
// 0 < δ < 1 if sticky, otherwise δ = 0. If sticky, m must be at least 2^52, so
// that δ * 2^e is below the last bit of the result.
fn round_up_exact(neg: bool, m: u128, e: i32, sticky: bool) -> f64 {
    let top = 127 - m.leading_zeros() as i32;
    // The exponent of the leading bit of the result, and that of its last bit,
    // which is fixed at -1074 for subnormal numbers.
    let lead = e + top;
    let lsb = (lead - 52).max(-1074);
    let shift = lsb - e;
    // The magnitude is (kept + f) * 2^lsb with 0 <= f < 1, f > 0 iff lost.
    let (mut kept, lost) = if shift <= 0 {
        // m has at most 53 significant bits (above 2^lsb). If sticky, m >= 2^52
        // makes shift = 0, so δ * 2^e is below 2^e = 2^lsb and still lost.
        (m << -shift, sticky)
    } else if shift >= 128 {
        (0, true)
    } else {
        (m >> shift, sticky || m & ((1 << shift) - 1) != 0)
    };
    // Rounding toward +∞ increases positive magnitudes and truncates negative ones.
    // A tiny negative number rounds to -0.
    if lost && !neg {
        kept += 1;
    }
    // kept <= 2^53. Carrying into bit 53 gives a power of two, which is still
    // exactly representable.
    let kept = kept as u64;
    let bits = 64 - kept.leading_zeros() as i32;
    if kept != 0 && lsb + bits > 1024 {
        // The magnitude is > MAX. Rounding toward +∞ gives +∞ for a positive
        // number, and -MAX for a negative one, which is finite.
        return if neg { f64::MIN } else { f64::INFINITY };
    }
    // Exact: kept < 2^54 and the result is representable.
    let mag = kept as f64 * pow2(lsb);
    if neg {
        -mag
    } else {
        mag
    }
}

// Returns 2^e for e ∈ [-1074, 1023].
fn pow2(e: i32) -> f64 {
    if e >= -1022 {
        f64::from_bits(((e + 1023) as u64) << 52)
    } else {
        f64::from_bits(1 << (e + 1074))
    }
}
