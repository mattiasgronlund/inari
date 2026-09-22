use std::arch::asm;

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
