//! The SIMD primitives, exposed for the benchmarks in `bench/`.
//! This module is not part of the public API and may change at any time.

use crate::simd;

#[derive(Clone, Copy)]
pub struct F64X2(simd::F64X2);

pub fn constant(x: f64, y: f64) -> F64X2 {
    F64X2(simd::constant(x, y))
}

pub fn extract(x: F64X2) -> [f64; 2] {
    simd::extract(x.0)
}

pub fn add_ru(x: F64X2, y: F64X2) -> F64X2 {
    F64X2(simd::add_ru(x.0, y.0))
}

pub fn div_ru(x: F64X2, y: F64X2) -> F64X2 {
    F64X2(simd::div_ru(x.0, y.0))
}

pub fn mul_add_ru(x: F64X2, y: F64X2, z: F64X2) -> F64X2 {
    F64X2(simd::mul_add_ru(x.0, y.0, z.0))
}

pub fn mul_ru(x: F64X2, y: F64X2) -> F64X2 {
    F64X2(simd::mul_ru(x.0, y.0))
}

pub fn sqrt1_ru(x: f64) -> f64 {
    simd::sqrt1_ru(x)
}
