// The lane-wise port of the generic backend (see `generic.rs`) to `__m128d`,
// used by `sse42`, which computes the rounding toward +∞ explicitly instead of
// switching MXCSR.
//
// What is here does not depend on how TwoProduct is computed: the fast paths
// that involve no product, and the helpers they are built from. Those that do
// involve one stay in `sse42.rs`, because Dekker's algorithm and an FMA need
// different hypotheses. A backend for a target that has an FMA can therefore
// share this module unchanged.
//
// Masks have all bits of a lane set for true, and none for false.

use super::{add_rn, all, and, constant, eq, extract, gt, lt, neg, or, sub_rn, xor, F64X2};
use crate::simd::generic;
use std::arch::x86_64::*;

/// `add_ru([x0, x1], [y0, y1]) = [x0 + y0, x1 + y1]` rounded toward +∞.
pub(crate) fn add_ru(x: F64X2, y: F64X2) -> F64X2 {
    // See `generic::add1_ru_fast`.
    let s = add_rn(x, y);
    let e = two_sum_err(x, y, s);
    let finite = and(is_finite(x), is_finite(y));
    let ok = or(
        not(finite),
        and(
            and(exponent_le(x, 1022), exponent_le(y, 1022)),
            is_finite(s),
        ),
    );
    let up = and(finite, gt(e, zero()));
    or_generic(ok, select(up, step_up(s), s), || {
        generic::add_ru(extract(x), extract(y))
    })
}

/// `sqrt1_ru(x) = √x` rounded toward +∞.
pub(crate) fn sqrt1_ru(x: f64) -> f64 {
    generic::sqrt1_ru(x)
}

/// `sub_ru([x0, x1], [y0, y1]) = [x0 - y0, x1 - y1]` rounded toward +∞.
pub(crate) fn sub_ru(x: F64X2, y: F64X2) -> F64X2 {
    // x - y is defined as x + (-y) by IEEE 754, including the signs of zeros.
    add_ru(x, neg(y))
}

/// `sub1_ru(x, y) = x - y` rounded toward +∞.
pub(crate) fn sub1_ru(x: f64, y: f64) -> f64 {
    generic::sub1_ru(x, y)
}

// The square root with the rounding mode switched, as an independent reference
// for `sqrt1_rd` and `sqrt1_ru` in the differential tests. The legacy encodings
// are used, as `sse42` has no AVX; under AVX they only cost a transition
// penalty, which does not matter for a reference.
#[cfg(test)]
macro_rules! impl_sqrt1_round {
    ($f:ident, rd) => {
        impl_sqrt1_round!($f, "16256"); // _MM_ROUND_DOWN | _MM_MASK_MASK
    };

    ($f:ident, ru) => {
        impl_sqrt1_round!($f, "24448"); // _MM_ROUND_UP | _MM_MASK_MASK
    };

    ($f:ident, $mxcsr:literal) => {
        pub(crate) fn $f(mut x: f64) -> f64 {
            unsafe {
                std::arch::asm!(
                    "push {rax}", // Same as "sub rsp, 8", but does not modify flags.
                    "stmxcsr [rsp]",
                    concat!("mov dword ptr [rsp + 4], ", $mxcsr),
                    "ldmxcsr [rsp + 4]",
                    "sqrtsd {x}, {x}",
                    "ldmxcsr [rsp]",
                    "pop {rax}", // Same as "add rsp, 8", but does not modify flags.
                    x = inout(xmm_reg) x,
                    rax = out(reg) _, // Any 64-bit general-purpose register.
                    options(pure, nomem, preserves_flags)
                );
            }
            x
        }
    };
}

#[cfg(test)]
impl_sqrt1_round!(sqrt1_rd_mxcsr, rd);
#[cfg(test)]
impl_sqrt1_round!(sqrt1_ru_mxcsr, ru);

// Lane-wise versions of the helpers of the generic backend.

pub(super) fn zero() -> F64X2 {
    unsafe { _mm_setzero_pd() }
}

/// The mask of lane 0 alone.
pub(super) fn lane0() -> F64X2 {
    unsafe { _mm_castsi128_pd(_mm_set_epi64x(0, -1)) }
}

/// `mul_rn([x0, x1], [y0, y1]) = [x0 * y0, x1 * y1]` rounded to nearest.
pub(super) fn mul_rn(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_mul_pd(x, y) }
}

/// `div_rn([x0, x1], [y0, y1]) = [x0 / y0, x1 / y1]` rounded to nearest.
pub(super) fn div_rn(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_div_pd(x, y) }
}

/// `sqrt_rn([x0, x1]) = [√x0, √x1]` rounded to nearest.
pub(super) fn sqrt_rn(x: F64X2) -> F64X2 {
    unsafe { _mm_sqrt_pd(x) }
}

/// `select(m, x, y)` takes the lanes of x where m is set, and those of y elsewhere.
/// Unlike wasm's `v128_bitselect`, this reads only the sign bit of each lane of
/// m, so m must be all ones or all zeros per lane, as every mask here is.
pub(super) fn select(m: F64X2, x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_blendv_pd(y, x, m) }
}

/// `andnot(x, y) = x & !y`, the opposite argument order to `_mm_andnot_pd`.
pub(super) fn andnot(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_andnot_pd(y, x) }
}

pub(super) fn not(x: F64X2) -> F64X2 {
    xor(x, splat_i64(-1))
}

// Operations on the lanes as 64-bit integers.

pub(super) fn splat_i64(x: i64) -> F64X2 {
    unsafe { _mm_castsi128_pd(_mm_set1_epi64x(x)) }
}

pub(super) fn add_i64(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_castsi128_pd(_mm_add_epi64(_mm_castpd_si128(x), _mm_castpd_si128(y))) }
}

pub(super) fn sub_i64(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_castsi128_pd(_mm_sub_epi64(_mm_castpd_si128(x), _mm_castpd_si128(y))) }
}

pub(super) fn gt_i64(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { _mm_castsi128_pd(_mm_cmpgt_epi64(_mm_castpd_si128(x), _mm_castpd_si128(y))) }
}

// Returns `r` if the fast path is valid in both lanes (`ok`), and otherwise the
// result of the generic backend, which recomputes the lanes that are not.
pub(super) fn or_generic(ok: F64X2, r: F64X2, generic: impl FnOnce() -> [f64; 2]) -> F64X2 {
    // Every lane of `ok` is all ones or all zeros, so its sign bit says which.
    if all(ok) {
        r
    } else {
        let [r0, r1] = generic();
        constant(r0, r1)
    }
}

// The unbiased exponents of the lanes of x as i64 lanes: floor(log2(|x|)) if x
// is normal, -1023 if x is zero or subnormal, and 1024 if x is infinite or NaN.
fn exponent(x: F64X2) -> F64X2 {
    let biased = unsafe { _mm_castsi128_pd(_mm_srli_epi64::<52>(_mm_castpd_si128(x))) };
    sub_i64(and(biased, splat_i64(0x7ff)), splat_i64(1023))
}

// The lanes where exponent(x) <= hi. SSE has no 64-bit `<=`, so `hi + 1 > e` is
// compared instead; every bound used here is far from overflowing.
pub(super) fn exponent_le(x: F64X2, hi: i64) -> F64X2 {
    gt_i64(splat_i64(hi + 1), exponent(x))
}

// The lanes where exponent(x) > hi.
pub(super) fn exponent_gt(x: F64X2, hi: i64) -> F64X2 {
    gt_i64(exponent(x), splat_i64(hi))
}

// The lanes where lo <= exponent(x) <= hi, as strict comparisons like `exponent_le`.
pub(super) fn exponent_in(x: F64X2, lo: i64, hi: i64) -> F64X2 {
    let e = exponent(x);
    and(gt_i64(e, splat_i64(lo - 1)), gt_i64(splat_i64(hi + 1), e))
}

pub(super) fn is_finite(x: F64X2) -> F64X2 {
    exponent_le(x, 1023)
}

// The lanes where x or y is ±0, ±∞ or NaN, for which the product and the
// quotient in the default rounding mode are exact.
pub(super) fn is_special(x: F64X2, y: F64X2) -> F64X2 {
    or(
        not(and(is_finite(x), is_finite(y))),
        or(eq(x, zero()), eq(y, zero())),
    )
}

/// Returns the successors of the lanes of x that are finite. See `generic::step_up`.
pub(super) fn step_up(x: F64X2) -> F64X2 {
    // The masks are -1 as integers: subtracting the mask of x > 0 increments the
    // bit pattern, and adding that of x < 0 decrements it.
    let b = add_i64(sub_i64(x, gt(x, zero())), lt(x, zero()));
    select(eq(x, zero()), splat_i64(1), b)
}

/// Returns the error e = (x + y) - s, where s = RN(x + y). See `generic::two_sum_err`.
pub(super) fn two_sum_err(x: F64X2, y: F64X2, s: F64X2) -> F64X2 {
    let a = sub_rn(s, y);
    let b = sub_rn(s, a);
    add_rn(sub_rn(x, a), sub_rn(y, b))
}
