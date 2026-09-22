use std::arch::{asm, x86_64::*};

macro_rules! impl_op_round {
    ($t:ty, $f:ident ($x:ident $(,$y:ident)*), $inst:literal, rd) => {
        impl_op_round!($t, $f ($x $(,$y)*), $inst, "16256"); // _MM_ROUND_DOWN | _MM_MASK_MASK
    };

    ($t:ty, $f:ident ($x:ident $(,$y:ident)*), $inst:literal, ru) => {
        impl_op_round!($t, $f ($x $(,$y)*), $inst, "24448"); // _MM_ROUND_UP | _MM_MASK_MASK
    };

    ($t:ty, $f:ident ($x:ident $(,$y:ident)*), $inst:literal, $mxcsr:literal) => {
        pub(crate) fn $f(mut $x: $t, $($y: $t,)*) -> $t {
            unsafe {
                asm!(
                    "push {rax}", // Same as "sub rsp, 8", but does not modify flags.
                    "vstmxcsr [rsp]",
                    concat!("mov dword ptr [rsp + 4], ", $mxcsr),
                    "vldmxcsr [rsp + 4]",
                    $inst,
                    "vldmxcsr [rsp]",
                    "pop {rax}", // Same as "add rsp, 8", but does not modify flags.
                    $x = inout(xmm_reg) $x,
                    $($y = in(xmm_reg) $y,)*
                    rax = out(reg) _, // Any 64-bit general-purpose register.
                    options(pure, nomem, preserves_flags)
                );
            }
            $x
        }
    };
}

// Correcting the square root rounded to nearest, as the generic backend does, is
// faster than switching the rounding mode around `vsqrtsd` (see BENCHMARKS.md).
// FMA is always available here.

/// `sqrt1_rd(x) = √x` rounded toward -∞.
pub(crate) fn sqrt1_rd(x: f64) -> f64 {
    crate::simd::generic::sqrt1_rd_impl::<true>(x)
}

/// `sqrt1_ru(x) = √x` rounded toward +∞.
pub(crate) fn sqrt1_ru(x: f64) -> f64 {
    crate::simd::generic::sqrt1_ru_impl::<true>(x)
}

/// `sqrt_rd_ru([x0, x1]) = [√x0, √x1]`, the first rounded toward -∞ and the
/// second toward +∞.
pub(crate) fn sqrt_rd_ru(x: super::F64X2) -> super::F64X2 {
    // The lane-wise form of `generic::sqrt1_fast` with an FMA, correcting the
    // two lanes in opposite directions.
    unsafe {
        let s = _mm_sqrt_pd(x);
        // x - s² is representable, so the FMA computes it exactly.
        let r = _mm_fnmadd_pd(s, s, x);
        // The remainder is representable if 2^-966 <= x < 2^1024, which also
        // excludes ±0, +∞ and NaN, but not negative numbers: for those, s and r
        // are NaN, the comparisons below are false, and NaN is returned.
        let e = _mm_sub_epi64(
            _mm_and_si128(
                _mm_srli_epi64(_mm_castpd_si128(x), 52),
                _mm_set1_epi64x(0x7ff),
            ),
            _mm_set1_epi64x(1023),
        );
        let ok = _mm_and_si128(
            _mm_cmpgt_epi64(e, _mm_set1_epi64x(-967)),
            _mm_cmpgt_epi64(_mm_set1_epi64x(1024), e),
        );
        if _mm_movemask_pd(_mm_castsi128_pd(ok)) != 3 {
            return sqrt_rd_ru_slow(x);
        }
        // √x < s ⟺ x - s² < 0, and then the result is the predecessor of s.
        // Lane 0 rounds toward -∞, lane 1 toward +∞. Where a lane is corrected,
        // s >= 2^-483, so stepping is incrementing or decrementing its bits.
        let zero = _mm_setzero_pd();
        let lane0 = _mm_castsi128_pd(_mm_set_epi64x(0, -1));
        let down = _mm_and_pd(_mm_cmplt_pd(r, zero), lane0);
        let up = _mm_andnot_pd(lane0, _mm_cmpgt_pd(r, zero));
        let b = _mm_castpd_si128(s);
        _mm_castsi128_pd(_mm_sub_epi64(
            _mm_add_epi64(b, _mm_castpd_si128(down)),
            _mm_castpd_si128(up),
        ))
    }
}

// Kept out of line: inlining two scalar square roots into `sqrt_rd_ru` makes it
// too large to inline into its callers (see BENCHMARKS.md).
#[cold]
fn sqrt_rd_ru_slow(x: super::F64X2) -> super::F64X2 {
    let [x0, x1] = super::extract(x);
    super::constant(sqrt1_rd(x0), sqrt1_ru(x1))
}

// The square root with the rounding mode switched, as an independent reference
// for `sqrt1_rd` and `sqrt1_ru` in the differential tests.
#[cfg(test)]
impl_op_round!(f64, sqrt1_rd_mxcsr(x), "vsqrtsd {x}, {x}, {x}", rd);
#[cfg(test)]
impl_op_round!(f64, sqrt1_ru_mxcsr(x), "vsqrtsd {x}, {x}, {x}", ru);
impl_op_round!(f64, sub1_ru(x, y), "vsubsd {x}, {x}, {y}", ru);
impl_op_round!(super::F64X2, add_ru(x, y), "vaddpd {x}, {x}, {y}", ru);
impl_op_round!(super::F64X2, sub_ru(x, y), "vsubpd {x}, {x}, {y}", ru);
impl_op_round!(super::F64X2, mul_ru(x, y), "vmulpd {x}, {x}, {y}", ru);
impl_op_round!(super::F64X2, div_ru(x, y), "vdivpd {x}, {x}, {y}", ru);
impl_op_round!(
    super::F64X2,
    mul_add_ru(x, y, z),
    "vfmadd213pd {x}, {y}, {z}",
    ru
);
