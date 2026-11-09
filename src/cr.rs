//! Correctly rounded `f64` functions.
//!
//! The elementary functions of an `f64` (of two for `atan2`, `hypot` and `pow`, and of an `f64`
//! and an `i32` for `powi`), each in three roundings: to nearest with ties to even (`_rn`),
//! toward -∞ (`_rd`) and toward +∞ (`_ru`). At the zeros, the infinities and outside the
//! domains, they give the values of MPFR. A NaN argument gives a NaN, whose bits are not
//! specified, but for pow(1, y), pow(x, ±0) and powi(x, 0), which are 1 at every x and y, NaNs
//! among them, and hypot(±∞, y) and hypot(x, ±∞), which are +∞, as in MPFR. `pow` takes
//! MPFR's values at a finite x < 0 and at x = -∞, as C99 does: (-1)^y |x|^y at an integer y,
//! |x|^y at y = ±∞ and, for x = -∞, at any other y, and NaN at any other y for a finite x, with
//! pow(-1, ±∞) = 1.
//!
//! Each function but `cbrt`, `hypot` and `sqrt` settles some arguments by rules, and at the
//! others computes enclosures of its result of increasing precision, up to 4,096 bits, until
//! both bounds of one round to the same `f64`, which is then the correctly rounded result
//! (Ziv's strategy). If none does by that cap, it returns the rounding of a bound of the last
//! enclosure, which is on the correct side of the result for `_rd` and `_ru` but is not known
//! to be correctly rounded. No known input reaches the cap: none of the 9,949,560
//! hard-to-round arguments that CORE-MATH lists for them does, nor any of a million random
//! arguments of each function but `powi`, in each of the three roundings. `cbrt` and `hypot`
//! do not use Ziv's strategy and have no cap: they compute the integer part of their result
//! scaled by a power of two, and whether the scaled result is above it, from an exact integer
//! cube or square root. `sqrt_rn` is `f64::sqrt`, and `sqrt_rd` and `sqrt_ru` are the square
//! roots toward -∞ and +∞ of the backend of the interval arithmetic. The tests on 64-bit Linux
//! and macOS compare the functions with MPFR in all three roundings, and the Rocq proofs in the
//! repository's `rocq/` directory show the results at finite arguments in the domains
//! correctly rounded wherever a rule or a rounding test settles them, and those of `cbrt`,
//! `hypot` and `sqrt` at every finite argument, x >= 0 for `sqrt`, with no such condition (for
//! `sqrt_rd` and `sqrt_ru`, as the portable backend computes them, which the backends of x86-64
//! without AVX-512F and of wasm32 call too).
//!
//! ```
//! use inari::cr;
//! assert_eq!(cr::exp_rn(0.0), 1.0);
//! assert!(cr::sin_rd(1.0) < cr::sin_ru(1.0));
//! assert_eq!(cr::pow_rn(-2.0, 3.0), -8.0);
//! ```

// The functions of the dyadic kernel of `src/dyadic.rs`: `dyadic::<f>(x, up)` rounded toward
// +∞ if `up` and toward -∞ otherwise, and `dyadic::<f>_near(x)` rounded to nearest.
use crate::dyadic;

// `$rn`, `$rd` and `$ru`: the function `$f` of the kernel rounded to nearest, toward -∞ and
// toward +∞, with `$v` its value in the docs.
macro_rules! cr_fn {
    ($f:ident, $near:ident, $rn:ident, $rd:ident, $ru:ident, $v:literal) => {
        #[doc = concat!("`", stringify!($rn), "(x) = ", $v, "` rounded to nearest, ties to even.")]
        pub fn $rn(x: f64) -> f64 {
            dyadic::$near(x)
        }

        #[doc = concat!("`", stringify!($rd), "(x) = ", $v, "` rounded toward -∞.")]
        pub fn $rd(x: f64) -> f64 {
            dyadic::$f(x, false)
        }

        #[doc = concat!("`", stringify!($ru), "(x) = ", $v, "` rounded toward +∞.")]
        pub fn $ru(x: f64) -> f64 {
            dyadic::$f(x, true)
        }
    };
}

cr_fn!(exp, exp_near, exp_rn, exp_rd, exp_ru, "e^x");
cr_fn!(exp2, exp2_near, exp2_rn, exp2_rd, exp2_ru, "2^x");
cr_fn!(exp10, exp10_near, exp10_rn, exp10_rd, exp10_ru, "10^x");
cr_fn!(ln, ln_near, ln_rn, ln_rd, ln_ru, "ln x");
cr_fn!(log2, log2_near, log2_rn, log2_rd, log2_ru, "log2 x");
cr_fn!(log10, log10_near, log10_rn, log10_rd, log10_ru, "log10 x");
cr_fn!(sinh, sinh_near, sinh_rn, sinh_rd, sinh_ru, "sinh x");
cr_fn!(cosh, cosh_near, cosh_rn, cosh_rd, cosh_ru, "cosh x");
cr_fn!(tanh, tanh_near, tanh_rn, tanh_rd, tanh_ru, "tanh x");
cr_fn!(asinh, asinh_near, asinh_rn, asinh_rd, asinh_ru, "asinh x");
cr_fn!(acosh, acosh_near, acosh_rn, acosh_rd, acosh_ru, "acosh x");
cr_fn!(atanh, atanh_near, atanh_rn, atanh_rd, atanh_ru, "atanh x");
cr_fn!(sin, sin_near, sin_rn, sin_rd, sin_ru, "sin x");
cr_fn!(cos, cos_near, cos_rn, cos_rd, cos_ru, "cos x");
cr_fn!(tan, tan_near, tan_rn, tan_rd, tan_ru, "tan x");
cr_fn!(asin, asin_near, asin_rn, asin_rd, asin_ru, "asin x");
cr_fn!(acos, acos_near, acos_rn, acos_rd, acos_ru, "acos x");
cr_fn!(atan, atan_near, atan_rn, atan_rd, atan_ru, "atan x");
cr_fn!(cbrt, cbrt_near, cbrt_rn, cbrt_rd, cbrt_ru, "∛x");

/// `atan2_rn(y, x) = atan2(y, x)` rounded to nearest, ties to even.
pub fn atan2_rn(y: f64, x: f64) -> f64 {
    dyadic::atan2_near(y, x)
}

/// `atan2_rd(y, x) = atan2(y, x)` rounded toward -∞.
pub fn atan2_rd(y: f64, x: f64) -> f64 {
    dyadic::atan2(y, x, false)
}

/// `atan2_ru(y, x) = atan2(y, x)` rounded toward +∞.
pub fn atan2_ru(y: f64, x: f64) -> f64 {
    dyadic::atan2(y, x, true)
}

/// `hypot_rn(x, y) = √(x^2 + y^2)` rounded to nearest, ties to even.
pub fn hypot_rn(x: f64, y: f64) -> f64 {
    dyadic::hypot_near(x, y)
}

/// `hypot_rd(x, y) = √(x^2 + y^2)` rounded toward -∞.
pub fn hypot_rd(x: f64, y: f64) -> f64 {
    dyadic::hypot(x, y, false)
}

/// `hypot_ru(x, y) = √(x^2 + y^2)` rounded toward +∞.
pub fn hypot_ru(x: f64, y: f64) -> f64 {
    dyadic::hypot(x, y, true)
}

/// `sqrt_rn(x) = √x` rounded to nearest, ties to even.
pub fn sqrt_rn(x: f64) -> f64 {
    x.sqrt()
}

/// `sqrt_rd(x) = √x` rounded toward -∞.
pub fn sqrt_rd(x: f64) -> f64 {
    crate::simd::sqrt1_rd(x)
}

/// `sqrt_ru(x) = √x` rounded toward +∞.
pub fn sqrt_ru(x: f64) -> f64 {
    crate::simd::sqrt1_ru(x)
}

/// `pow_rn(x, y) = x^y` rounded to nearest, ties to even.
pub fn pow_rn(x: f64, y: f64) -> f64 {
    pow_near_signed(x, y)
}

/// `pow_rd(x, y) = x^y` rounded toward -∞.
pub fn pow_rd(x: f64, y: f64) -> f64 {
    pow_dir(x, y, false)
}

/// `pow_ru(x, y) = x^y` rounded toward +∞.
pub fn pow_ru(x: f64, y: f64) -> f64 {
    pow_dir(x, y, true)
}

/// `powi_rn(x, n) = x^n` rounded to nearest, ties to even.
pub fn powi_rn(x: f64, n: i32) -> f64 {
    dyadic::pown_near(x, n)
}

/// `powi_rd(x, n) = x^n` rounded toward -∞.
pub fn powi_rd(x: f64, n: i32) -> f64 {
    dyadic::pown(x, n, false)
}

/// `powi_ru(x, n) = x^n` rounded toward +∞.
pub fn powi_ru(x: f64, n: i32) -> f64 {
    dyadic::pown(x, n, true)
}

// x^y rounded toward +∞ if `up` and toward -∞ otherwise, with the values that C99 (Annex F)
// and MPFR give at a finite x < 0 and at x = -∞: (-1)^y |x|^y at an integer y, |x|^y at an
// infinite y and for x = -∞ at any other y, and NaN at any other y for a finite x.
// `dyadic::pow` takes the other arguments, -0 among them, and gives NaN at these. A NaN y
// goes to `dyadic::pow` too, as pow(-1, NaN) is NaN, unlike pow(1, NaN).
// `rocq/theories/Model.v` transcribes this function and `pow_near_signed`, and
// `rocq/theories/CrPow.v` proves that, at finite arguments, they return x^y rounded as the
// function of the kernel that they call, at x < 0 and an integer y (`cr_pow_dir_neg` and
// `cr_pow_near_neg`) and in the domain of `dyadic::pow` (`cr_pow_dir_dom` and
// `cr_pow_near_dom`), where a rule or a rounding test settles them. The other functions of
// this file call a function of the kernel and nothing else, whose proofs they inherit, but for
// `sqrt_rn`, `sqrt_rd` and `sqrt_ru`, which call `f64::sqrt` and the backend's `sqrt1_rd` and
// `sqrt1_ru`, and which `rocq/theories/CrRoot.v` proves for the portable backend.
fn pow_dir(x: f64, y: f64, up: bool) -> f64 {
    if x < 0.0 && !y.is_nan() {
        if dyadic::is_odd_integer(y) {
            // -(|x|^y) rounded toward +∞ is -(|x|^y rounded toward -∞), and the other way
            // round.
            -dyadic::pow(-x, y, !up)
        } else if y == y.floor() || x == f64::NEG_INFINITY {
            dyadic::pow(-x, y, up)
        } else {
            f64::NAN
        }
    } else {
        dyadic::pow(x, y, up)
    }
}

// x^y rounded to nearest, ties to even, with the values of `pow_dir` at a finite x < 0 and at
// x = -∞.
fn pow_near_signed(x: f64, y: f64) -> f64 {
    if x < 0.0 && !y.is_nan() {
        if dyadic::is_odd_integer(y) {
            // Rounding to nearest is symmetric.
            -dyadic::pow_near(-x, y)
        } else if y == y.floor() || x == f64::NEG_INFINITY {
            dyadic::pow_near(-x, y)
        } else {
            f64::NAN
        }
    } else {
        dyadic::pow_near(x, y)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn special_cases() {
        assert_eq!(exp_rn(0.0), 1.0);
        assert_eq!(exp10_rn(23.0).to_bits(), 0x44b5_2d02_c7e1_4af6);
        assert_eq!(exp10_rn(23.0), 1e23);
        assert_eq!(exp2_rn(-1075.0).to_bits(), 0);
        assert_eq!(exp2_rn(-1074.0), f64::from_bits(1));
        assert_eq!(tanh_rn(19.0), 1.0 - f64::EPSILON / 2.0);
        assert_eq!(tanh_rn(20.0), 1.0);
        assert_eq!(pow_rn(-2.0, 3.0), -8.0);
        assert_eq!(pow_rd(-2.0, 3.0), -8.0);
        assert!(pow_rd(-2.0, 0.5).is_nan());
        assert_eq!(
            pow_ru(f64::NEG_INFINITY, -3.0).to_bits(),
            (-0.0f64).to_bits()
        );
        assert_eq!(pow_rn(f64::NEG_INFINITY, 3.0), f64::NEG_INFINITY);
        assert_eq!(pow_rn(f64::NEG_INFINITY, 0.5), f64::INFINITY);
        assert_eq!(pow_rn(-1.0, f64::INFINITY), 1.0);
        assert!(pow_rn(-1.0, f64::NAN).is_nan());
        assert_eq!(
            powi_rn(-(2.0f64.powi(-5)), 215).to_bits(),
            (-0.0f64).to_bits()
        );
        assert_eq!(sin_rd(1.0), dyadic::sin(1.0, false));
        assert_eq!(sin_ru(1.0), dyadic::sin(1.0, true));
    }

    // The zeros that the nearest functions give at the arguments where their values are 0.
    #[test]
    fn exact_zeros() {
        for (v, name) in [
            (ln_rn(1.0), "ln"),
            (log2_rn(1.0), "log2"),
            (log10_rn(1.0), "log10"),
            (acosh_rn(1.0), "acosh"),
            (acos_rn(1.0), "acos"),
            (sin_rn(0.0), "sin"),
            (atan2_rn(0.0, 1.0), "atan2"),
        ] {
            assert_eq!(v.to_bits(), 0, "{name}");
        }
        assert_eq!(sin_rn(-0.0).to_bits(), (-0.0f64).to_bits());
    }

    // Results at a midpoint: 3^34 = 16677181699666569 is odd and in [2^53, 2^54), so it rounds
    // to its even neighbour 16677181699666568, which pow(3, 34) and powi(3, 34) give, and
    // pow(81, 8.5) = 3^34, which `exact_near` settles.
    #[test]
    fn midpoints() {
        assert_eq!(pow_rn(3.0, 34.0), 16677181699666568.0);
        assert_eq!(pow_rn(81.0, 8.5), 16677181699666568.0);
        assert_eq!(powi_rn(3.0, 34), 16677181699666568.0);
    }

    // The functions against MPFR, on 64-bit Linux and macOS, where the tests have MPFR: each
    // of the three roundings gives the `f64` that MPFR gives in that rounding, bit for bit, or
    // a NaN where MPFR gives one, at special arguments, at the thresholds of the kernel and the
    // `f64`s next to them, and at a seeded random sample. MPFR's nearest roundings are those of
    // `mpfr_near!` in `src/mpfr_calls/mpfr.rs`, all three roundings of cbrt, hypot and sqrt are
    // those of its `mpfr_once!`, and `powi_<r>` is checked against its `pown_<r>`.
    #[cfg(all(
        target_pointer_width = "64",
        any(target_os = "linux", target_os = "macos")
    ))]
    mod mpfr {
        use super::*;
        use crate::mpfr_calls::mpfr as oracle;
        use rug::Float;

        mod hard_cases;

        type F = fn(f64) -> f64;

        // Each function of one `f64` by name, in its three roundings, then MPFR's.
        const UNARY: [(&str, [F; 3], [F; 3]); 20] = [
            (
                "exp",
                [exp_rn, exp_rd, exp_ru],
                [oracle::exp_rn, oracle::exp_rd, oracle::exp_ru],
            ),
            (
                "exp2",
                [exp2_rn, exp2_rd, exp2_ru],
                [oracle::exp2_rn, oracle::exp2_rd, oracle::exp2_ru],
            ),
            (
                "exp10",
                [exp10_rn, exp10_rd, exp10_ru],
                [oracle::exp10_rn, oracle::exp10_rd, oracle::exp10_ru],
            ),
            (
                "ln",
                [ln_rn, ln_rd, ln_ru],
                [oracle::ln_rn, oracle::ln_rd, oracle::ln_ru],
            ),
            (
                "log2",
                [log2_rn, log2_rd, log2_ru],
                [oracle::log2_rn, oracle::log2_rd, oracle::log2_ru],
            ),
            (
                "log10",
                [log10_rn, log10_rd, log10_ru],
                [oracle::log10_rn, oracle::log10_rd, oracle::log10_ru],
            ),
            (
                "sinh",
                [sinh_rn, sinh_rd, sinh_ru],
                [oracle::sinh_rn, oracle::sinh_rd, oracle::sinh_ru],
            ),
            (
                "cosh",
                [cosh_rn, cosh_rd, cosh_ru],
                [oracle::cosh_rn, oracle::cosh_rd, oracle::cosh_ru],
            ),
            (
                "tanh",
                [tanh_rn, tanh_rd, tanh_ru],
                [oracle::tanh_rn, oracle::tanh_rd, oracle::tanh_ru],
            ),
            (
                "asinh",
                [asinh_rn, asinh_rd, asinh_ru],
                [oracle::asinh_rn, oracle::asinh_rd, oracle::asinh_ru],
            ),
            (
                "acosh",
                [acosh_rn, acosh_rd, acosh_ru],
                [oracle::acosh_rn, oracle::acosh_rd, oracle::acosh_ru],
            ),
            (
                "atanh",
                [atanh_rn, atanh_rd, atanh_ru],
                [oracle::atanh_rn, oracle::atanh_rd, oracle::atanh_ru],
            ),
            (
                "sin",
                [sin_rn, sin_rd, sin_ru],
                [oracle::sin_rn, oracle::sin_rd, oracle::sin_ru],
            ),
            (
                "cos",
                [cos_rn, cos_rd, cos_ru],
                [oracle::cos_rn, oracle::cos_rd, oracle::cos_ru],
            ),
            (
                "tan",
                [tan_rn, tan_rd, tan_ru],
                [oracle::tan_rn, oracle::tan_rd, oracle::tan_ru],
            ),
            (
                "asin",
                [asin_rn, asin_rd, asin_ru],
                [oracle::asin_rn, oracle::asin_rd, oracle::asin_ru],
            ),
            (
                "acos",
                [acos_rn, acos_rd, acos_ru],
                [oracle::acos_rn, oracle::acos_rd, oracle::acos_ru],
            ),
            (
                "atan",
                [atan_rn, atan_rd, atan_ru],
                [oracle::atan_rn, oracle::atan_rd, oracle::atan_ru],
            ),
            (
                "cbrt",
                [cbrt_rn, cbrt_rd, cbrt_ru],
                [oracle::cbrt_rn, oracle::cbrt_rd, oracle::cbrt_ru],
            ),
            (
                "sqrt",
                [sqrt_rn, sqrt_rd, sqrt_ru],
                [oracle::sqrt_rn, oracle::sqrt_rd, oracle::sqrt_ru],
            ),
        ];

        // The number of random arguments (pairs of arguments for atan2, hypot, pow and powi)
        // for each function.
        const SAMPLES: usize = 10000;

        // SplitMix64, as `Rng` in `src/dyadic/tests.rs`.
        struct Rng(u64);

        impl Rng {
            fn next(&mut self) -> u64 {
                self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
                let mut z = self.0;
                z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                z ^ (z >> 31)
            }

            fn below(&mut self, n: u64) -> u64 {
                self.next() % n
            }

            // A normal `f64` of either sign with a random mantissa and its exponent in
            // [lo, hi], within [-1022, 1023].
            fn scaled(&mut self, lo: i64, hi: i64) -> f64 {
                let e = lo + self.below((hi - lo + 1) as u64) as i64;
                let sign = self.below(2) << 63;
                f64::from_bits(sign | ((1023 + e) as u64) << 52 | self.next() >> 12)
            }

            // A number in [0, 1).
            fn unit(&mut self) -> f64 {
                (self.next() >> 11) as f64 / 2f64.powi(53)
            }

            // An argument of a function of one `f64`: any `f64`, one near ±1 (the edges of the
            // domains of atanh, asin and acos, and the zero of ln), one of any exponent, an
            // integer or half an integer, one with 300 <= |x| < 1080, where exp, exp2 and exp10
            // overflow or give subnormals, or most often one in [2^-60, 2^12), where the
            // thresholds of the kernel lie.
            fn arg(&mut self) -> f64 {
                let sign = if self.below(2) == 0 { 1.0 } else { -1.0 };
                match self.below(9) {
                    0 => f64::from_bits(self.next()),
                    1 => sign * (1.0 + self.scaled(-60, -1)),
                    2 => self.scaled(-1022, 1023),
                    3 => (self.below(129) as f64 - 64.0) / 2.0,
                    4 => sign * (300.0 + 780.0 * self.unit()),
                    _ => self.scaled(-60, 11),
                }
            }

            // An exponent y of pow: an integer in [-200, 200], half an odd integer, an integer
            // of 2^52 or more, odd or even, or else a random argument.
            fn exponent(&mut self) -> f64 {
                match self.below(6) {
                    0 | 1 => self.below(401) as f64 - 200.0,
                    2 => (2.0 * self.below(401) as f64 - 401.0) / 2.0,
                    3 => self.scaled(52, 63),
                    _ => self.arg(),
                }
            }

            // An integer exponent n of powi: most often one in [-300, 300], or any `i32`.
            fn int_exponent(&mut self) -> i32 {
                if self.below(4) == 0 {
                    self.next() as i32
                } else {
                    self.below(601) as i32 - 300
                }
            }

            // `v` or -`v`, each as likely.
            fn signed(&mut self, v: f64) -> f64 {
                if self.below(2) == 0 {
                    v
                } else {
                    -v
                }
            }

            // `x` and `y` with random signs, in a random order.
            fn pair(&mut self, x: f64, y: f64) -> (f64, f64) {
                let (x, y) = (self.signed(x), self.signed(y));
                if self.below(2) == 0 {
                    (x, y)
                } else {
                    (y, x)
                }
            }

            // A subnormal `f64` or a zero, of either sign, with fewer significant bits at
            // random, so that its exponent is spread over those of the subnormals.
            fn subnormal(&mut self) -> f64 {
                let v = f64::from_bits(self.next() >> (12 + self.below(52)));
                self.signed(v)
            }
        }

        // 2^k as an `f64`, from its bits, for -1074 <= k <= 1023.
        fn pow2(k: i64) -> f64 {
            if k >= -1022 {
                f64::from_bits(((1023 + k) as u64) << 52)
            } else {
                f64::from_bits(1 << (k + 1074))
            }
        }

        // The finite `f64`s whose bits are within `k` of those of `v`: for a finite v > 0, `v`
        // and the `k` `f64`s on each side of it that are not below 0 or above MAX.
        fn within(v: f64, k: u64) -> impl Iterator<Item = f64> {
            let b = v.to_bits();
            (b.saturating_sub(k)..=b + k)
                .map(f64::from_bits)
                .filter(|w| w.is_finite())
        }

        // The index of the function `name` in `UNARY`.
        fn index(name: &str) -> usize {
            UNARY.iter().position(|&(n, _, _)| n == name).unwrap()
        }

        // Whether `a` and `b` are the same `f64`, bit for bit, or both NaNs.
        fn same(a: f64, b: f64) -> bool {
            a.to_bits() == b.to_bits() || a.is_nan() && b.is_nan()
        }

        // Records in `errs` where `got`, the three roundings of the function `name` at `args`,
        // differ from `want`, MPFR's, after checking that MPFR's nearest rounding is one of its
        // directed ones.
        fn compare(errs: &mut Vec<String>, name: &str, args: &str, got: [f64; 3], want: [f64; 3]) {
            assert!(
                same(want[0], want[1]) || same(want[0], want[2]),
                "MPFR's {name}_rn({args}) = {:e} is neither its _rd {:e} nor its _ru {:e}",
                want[0],
                want[1],
                want[2]
            );
            for (r, (got, want)) in ["rn", "rd", "ru"].iter().zip(got.iter().zip(want)) {
                if !same(*got, want) {
                    errs.push(format!("{name}_{r}({args}) = {got:e} != MPFR's {want:e}"));
                }
            }
        }

        // Fails with the first 50 entries of `errs` if there are any.
        fn report(errs: Vec<String>) {
            assert!(
                errs.is_empty(),
                "{} mismatches with MPFR:\n{}",
                errs.len(),
                errs[..errs.len().min(50)].join("\n")
            );
        }

        fn check_unary(errs: &mut Vec<String>, i: usize, x: f64) {
            let (name, cr, mpfr) = UNARY[i];
            let args = format!("{x:e}");
            compare(errs, name, &args, cr.map(|f| f(x)), mpfr.map(|f| f(x)));
        }

        fn check_atan2(errs: &mut Vec<String>, y: f64, x: f64) {
            compare(
                errs,
                "atan2",
                &format!("{y:e}, {x:e}"),
                [atan2_rn(y, x), atan2_rd(y, x), atan2_ru(y, x)],
                [
                    oracle::atan2_rn(y, x),
                    oracle::atan2_rd(y, x),
                    oracle::atan2_ru(y, x),
                ],
            );
        }

        fn check_hypot(errs: &mut Vec<String>, x: f64, y: f64) {
            compare(
                errs,
                "hypot",
                &format!("{x:e}, {y:e}"),
                [hypot_rn(x, y), hypot_rd(x, y), hypot_ru(x, y)],
                [
                    oracle::hypot_rn(x, y),
                    oracle::hypot_rd(x, y),
                    oracle::hypot_ru(x, y),
                ],
            );
        }

        fn check_pow(errs: &mut Vec<String>, x: f64, y: f64) {
            compare(
                errs,
                "pow",
                &format!("{x:e}, {y:e}"),
                [pow_rn(x, y), pow_rd(x, y), pow_ru(x, y)],
                [
                    oracle::pow_rn(x, y),
                    oracle::pow_rd(x, y),
                    oracle::pow_ru(x, y),
                ],
            );
        }

        fn check_powi(errs: &mut Vec<String>, x: f64, n: i32) {
            compare(
                errs,
                "powi",
                &format!("{x:e}, {n}"),
                [powi_rn(x, n), powi_rd(x, n), powi_ru(x, n)],
                [
                    oracle::pown_rn(x, n),
                    oracle::pown_rd(x, n),
                    oracle::pown_ru(x, n),
                ],
            );
        }

        // `v` and, if it is finite and not 0, the finite `f64`s next to it.
        fn around(v: f64) -> Vec<f64> {
            if v == 0.0 || !v.is_finite() {
                return vec![v];
            }
            let b = v.to_bits();
            let mut vs = vec![f64::from_bits(b - 1), v];
            if v.abs() < f64::MAX {
                vs.push(f64::from_bits(b + 1));
            }
            vs
        }

        // Special arguments of the functions of one `f64`, of both signs, each with the `f64`s
        // next to it: the zeros, the infinities and a NaN, ±1, where the domains of atanh,
        // asin, acos and acosh end, the least and greatest `f64`s, the thresholds of the kernel
        // (the `f64` constants of `src/dyadic/exp.rs`, `log.rs`, `atan.rs` and `trig.rs`, and
        // 2^-56, 2^-14 and 2^-13), multiples of π, the arguments near which exp, exp2, exp10,
        // sinh and cosh overflow or give subnormals or 0, and near which tanh gives 1, and large
        // arguments of sin, cos and tan.
        fn special_args() -> Vec<f64> {
            use std::f64::consts::{FRAC_PI_2, FRAC_PI_4, PI};
            let bases = [
                0.0,
                f64::INFINITY,
                f64::NAN,
                1.0,
                0.5,
                2.0,
                3.0,
                10.0,
                0.1,
                f64::from_bits(1),
                f64::MIN_POSITIVE,
                f64::MAX,
                2f64.powi(-56),
                2f64.powi(-54),
                2f64.powi(-27),
                2f64.powi(-26),
                2f64.powi(-14),
                2f64.powi(-13),
                2f64.powi(-8),
                0.171875,
                0.75,
                0.78515625,
                1.015625,
                2f64.powi(53),
                2f64.powi(54),
                2f64.powi(63),
                FRAC_PI_4,
                FRAC_PI_2,
                PI,
                2.0 * PI,
                709.782712893384,
                -708.3964185322641,
                -745.1332191019411,
                -745.1332191019412,
                1024.0,
                -1022.0,
                -1074.0,
                -1074.5,
                -1075.0,
                -1075.5,
                308.25471555991675,
                -307.6526555685888,
                -323.3062153431158,
                -324.0,
                710.4758600739439,
                19.0,
                19.061547465398498,
                20.0,
                22.0,
                1e22,
                1e300,
                2f64.powi(1023),
            ];
            let mut args = vec![];
            for v in bases {
                for w in around(v) {
                    args.push(w);
                    args.push(-w);
                }
            }
            args
        }

        // Special arguments x of pow and powi, and y and x of atan2, of both signs, without the
        // `f64`s next to them: the zeros, the infinities and a NaN, ±1 and the `f64`s next to
        // 1, the least and greatest `f64`s, powers of 3 and of 2, and some others.
        fn special_bases() -> Vec<f64> {
            let mut xs = vec![];
            for v in [
                0.0,
                f64::INFINITY,
                f64::NAN,
                1.0,
                1.0 - f64::EPSILON / 2.0,
                1.0 + f64::EPSILON,
                0.5,
                2.0,
                3.0,
                9.0,
                81.0,
                0.1,
                f64::from_bits(1),
                f64::MIN_POSITIVE,
                f64::MAX,
                2f64.powi(-54),
                2f64.powi(-27),
                2f64.powi(-5),
                2f64.powi(54),
                1e300,
            ] {
                xs.push(v);
                xs.push(-v);
            }
            xs
        }

        // Special exponents y of pow, of both signs: the zeros, the infinities and a NaN, small
        // integers, halves of odd integers and other fractions, the exponents at which a power
        // of 2 or 3 is a tie, is exact, overflows or gives subnormals, and integers that an
        // `f64` holds that are odd, even, or too large for an `i32`.
        fn special_pow_exponents() -> Vec<f64> {
            let mut ys = vec![];
            for v in [
                0.0,
                f64::INFINITY,
                f64::NAN,
                1.0,
                2.0,
                3.0,
                0.5,
                1.5,
                2.5,
                0.25,
                1.0 / 3.0,
                8.5,
                17.0,
                34.0,
                215.0,
                1023.0,
                1024.0,
                1074.0,
                1075.0,
                2f64.powi(31),
                2f64.powi(52) + 1.0,
                2f64.powi(53),
                2f64.powi(53) + 2.0,
                2f64.powi(63),
                1e300,
            ] {
                ys.push(v);
                ys.push(-v);
            }
            ys
        }

        const SPECIAL_POWI_EXPONENTS: [i32; 26] = [
            0,
            1,
            -1,
            2,
            -2,
            3,
            -3,
            17,
            34,
            -34,
            215,
            -215,
            1023,
            1024,
            -1024,
            1074,
            -1074,
            1075,
            -1075,
            1 << 30,
            -(1 << 30),
            i32::MAX - 1,
            i32::MAX,
            i32::MIN + 1,
            i32::MIN,
            53,
        ];

        #[test]
        fn unary_special() {
            let mut errs = vec![];
            let args = special_args();
            for i in 0..UNARY.len() {
                for &x in &args {
                    check_unary(&mut errs, i, x);
                }
            }
            report(errs);
        }

        #[test]
        fn unary_random() {
            let mut errs = vec![];
            let mut rng = Rng(1);
            for i in 0..UNARY.len() {
                for _ in 0..SAMPLES {
                    let x = rng.arg();
                    check_unary(&mut errs, i, x);
                }
            }
            report(errs);
        }

        #[test]
        fn atan2_special_and_random() {
            let mut errs = vec![];
            let xs = special_bases();
            for &y in &xs {
                for &x in &xs {
                    check_atan2(&mut errs, y, x);
                }
            }
            let mut rng = Rng(2);
            for _ in 0..SAMPLES {
                let (y, x) = (rng.arg(), rng.arg());
                check_atan2(&mut errs, y, x);
            }
            report(errs);
        }

        // pow at every pair of special arguments, finite x < 0 and x = -∞ among them, with
        // integer and other y, and at random pairs, half of them with x < 0.
        #[test]
        fn pow_special_and_random() {
            let mut errs = vec![];
            let ys = special_pow_exponents();
            for &x in &special_bases() {
                for &y in &ys {
                    check_pow(&mut errs, x, y);
                }
            }
            let mut rng = Rng(3);
            for _ in 0..SAMPLES {
                let (x, y) = (rng.arg(), rng.exponent());
                check_pow(&mut errs, x, y);
            }
            report(errs);
        }

        #[test]
        fn powi_special_and_random() {
            let mut errs = vec![];
            for &x in &special_bases() {
                for n in SPECIAL_POWI_EXPONENTS {
                    check_powi(&mut errs, x, n);
                }
            }
            let mut rng = Rng(4);
            for _ in 0..SAMPLES {
                let (x, n) = (rng.arg(), rng.int_exponent());
                check_powi(&mut errs, x, n);
            }
            report(errs);
        }

        // cbrt at the cubes x = y^3 of the `f64`s y = r 2^a with r odd and r^3 < 2^51, of both
        // signs, where cbrt x = y is exact, and at the two `f64`s on each side of them, and at
        // random subnormals. The special arguments and random ones are in `unary_special` and
        // `unary_random`.
        #[test]
        fn cbrt_cubes_and_subnormals() {
            let mut errs = vec![];
            let i = index("cbrt");
            let mut rng = Rng(6);
            for _ in 0..SAMPLES / 10 {
                // r < 2^17 and -1074 <= 3 a <= 972, so that y and x are `f64`s.
                let r = rng.next() >> (63 - rng.below(17)) | 1;
                let a = rng.below(683) as i64 - 358;
                let (y, x) = (r as f64 * pow2(a), (r * r * r) as f64 * pow2(3 * a));
                for (y, x) in [(y, x), (-y, -x)] {
                    let got = [cbrt_rn(x), cbrt_rd(x), cbrt_ru(x)];
                    assert_eq!(got.map(f64::to_bits), [y.to_bits(); 3], "cbrt({x:e})");
                }
                for w in within(x, 2) {
                    check_unary(&mut errs, i, w);
                    check_unary(&mut errs, i, -w);
                }
            }
            for _ in 0..SAMPLES {
                let x = rng.subnormal();
                check_unary(&mut errs, i, x);
            }
            report(errs);
        }

        // sqrt where MPFR gives a zero or a NaN: √-0 = -0, as for `sqrt_rd`, and √x = NaN at
        // x < 0, as for `sqrt_ru`, in each rounding; at the squares x = y^2 of the `f64`s
        // y = r 2^a with r odd and r < 2^26, where √x = y is exact, and at the `f64`s next to
        // them; and at random subnormals.
        #[test]
        fn sqrt_special_squares_and_subnormals() {
            let i = index("sqrt");
            let (_, cr, mpfr) = UNARY[i];
            for (r, (f, g)) in ["rn", "rd", "ru"].iter().zip(cr.iter().zip(mpfr)) {
                let z = (-0.0f64).to_bits();
                assert_eq!(
                    (f(-0.0).to_bits(), g(-0.0).to_bits()),
                    (z, z),
                    "sqrt_{r}(-0)"
                );
                for x in [-f64::from_bits(1), -1.0, -f64::MAX, f64::NEG_INFINITY] {
                    assert!(f(x).is_nan() && g(x).is_nan(), "sqrt_{r}({x:e})");
                }
            }
            let mut errs = vec![];
            let mut rng = Rng(7);
            for _ in 0..SAMPLES / 10 {
                // r < 2^26 and -1074 <= 2 a <= 970, so that y and x are `f64`s.
                let r = rng.next() >> (63 - rng.below(26)) | 1;
                let a = rng.below(1023) as i64 - 537;
                let (y, x) = (r as f64 * pow2(a), (r * r) as f64 * pow2(2 * a));
                let got = [sqrt_rn(x), sqrt_rd(x), sqrt_ru(x)];
                assert_eq!(got.map(f64::to_bits), [y.to_bits(); 3], "sqrt({x:e})");
                for w in around(x) {
                    check_unary(&mut errs, i, w);
                }
            }
            for _ in 0..SAMPLES {
                let x = rng.subnormal();
                check_unary(&mut errs, i, x);
            }
            report(errs);
        }

        // hypot at every pair of special arguments, and its values where MPFR gives +∞ at a
        // NaN: hypot(±∞, NaN) = hypot(NaN, ±∞) = +∞ in each rounding.
        #[test]
        fn hypot_special() {
            for (x, y) in [
                (f64::INFINITY, f64::NAN),
                (f64::NEG_INFINITY, f64::NAN),
                (f64::NAN, f64::NEG_INFINITY),
            ] {
                let got = [hypot_rn(x, y), hypot_rd(x, y), hypot_ru(x, y)];
                let want = [
                    oracle::hypot_rn(x, y),
                    oracle::hypot_rd(x, y),
                    oracle::hypot_ru(x, y),
                ];
                assert_eq!((got, want), ([f64::INFINITY; 3], [f64::INFINITY; 3]));
            }
            let mut errs = vec![];
            let args = special_args();
            for &x in &args {
                for &y in &args {
                    check_hypot(&mut errs, x, y);
                }
            }
            report(errs);
        }

        // hypot at random pairs, with random signs and in a random order: log-uniform, uniform
        // in [0, 1), random arguments of the functions of one `f64`, a random gap g in [0, 60]
        // between the exponents of x and y, and y = x 2^-g and the `f64`s next to it for g in
        // [25, 29], around the gap 27 from which `hypot_odd` in `src/dyadic/root.rs` takes the
        // result from x alone.
        #[test]
        fn hypot_random() {
            let mut errs = vec![];
            let mut rng = Rng(8);
            for _ in 0..SAMPLES {
                let (x, y) = match rng.below(5) {
                    0 => (rng.scaled(-1022, 1023), rng.scaled(-1022, 1023)),
                    1 => (rng.unit(), rng.unit()),
                    2 => (rng.arg(), rng.arg()),
                    3 => {
                        let g = rng.below(61) as i64;
                        let e = rng.below(1986) as i64 - 962;
                        (rng.scaled(e, e), rng.scaled(e - g, e - g))
                    }
                    _ => {
                        let x = rng.scaled(-990, 1023);
                        let y = x * pow2(-25 - rng.below(5) as i64);
                        (x, f64::from_bits(y.to_bits() + rng.below(3) - 1))
                    }
                };
                let (x, y) = rng.pair(x, y);
                check_hypot(&mut errs, x, y);
            }
            report(errs);
        }

        // hypot at the cut of `hypot_odd` in `src/dyadic/root.rs`, a gap of 27 between the
        // exponents of |x| >= |y|: x at the ends of a binade 2^e and y at the ends of the binade
        // 2^(e - g), for g in [25, 29], each with the `f64`s next to them, so that the gaps 23
        // to 31 occur, with subnormal y for e = -1000.
        #[test]
        fn hypot_cut() {
            let mut errs = vec![];
            for e in [-1000, -60, -1, 0, 1, 52, 500, 1000] {
                for g in 25..=29 {
                    for x in [pow2(e), pow2(e + 1)].into_iter().flat_map(around) {
                        for y in [pow2(e - g), pow2(e - g + 1)].into_iter().flat_map(around) {
                            check_hypot(&mut errs, x, y);
                            check_hypot(&mut errs, -y, x);
                        }
                    }
                }
            }
            report(errs);
        }

        // A Pythagorean triple (a, b, c), a^2 + b^2 = c^2, with c odd in [2^53, 2^54) and the
        // legs a and b `f64`s, so that hypot(a, b) = c is midway between the `f64`s c - 1 and
        // c + 1: a = d (m^2 - n^2), b = 2 d m n and c = d (m^2 + n^2) for m > n > 0 of
        // opposite parity and d = 1 or 3. a is odd, so it is an `f64` only below 2^53, and b is
        // even and below 2^54. m^2 + n^2 is 1 modulo 4, so the tie goes to nearest to c - 1,
        // whose significand (c - 1) / 2 is even, at d = 1, and to c + 1 at d = 3. A third of
        // them have d = 1 and m = n + e with e odd and small, which gives gaps up to 26 between
        // the exponents of a and b.
        fn triple(rng: &mut Rng) -> (u64, u64, u64) {
            loop {
                let (m, n, d) = match rng.below(3) {
                    0 => {
                        let m = (1 << 26) + rng.below(1 << 26);
                        (m, 1 + rng.below(m - 1), 1)
                    }
                    1 => {
                        let n = (1 << 26) + rng.below(1 << 25);
                        let bits = rng.below(20);
                        let e = rng.below(1 << bits);
                        (n + 2 * e + 1, n, 1)
                    }
                    _ => {
                        // d = 3 needs 2^53 / 3 <= m^2 + n^2 < 2^54 / 3, so m near 2^26.
                        let m = (3 << 24) + rng.below(1 << 25);
                        (m, 1 + rng.below(m - 1), 3)
                    }
                };
                let (a, b, c) = (d * (m * m - n * n), d * 2 * m * n, d * (m * m + n * n));
                if (m + n) % 2 == 1 && (1 << 53..1 << 54).contains(&c) && a < 1 << 53 {
                    return (a, b, c);
                }
            }
        }

        // hypot at the midpoints of `triple`, scaled by 2^k for k in [-1074, 970], where the
        // shorter leg can be subnormal at k = -1074 (the longer one is at least 2^52.5 2^k),
        // and at the `f64`s next to a and b, with random signs and in a random order. At the
        // triple itself, `hypot_rd` and `hypot_ru` give the `f64`s (c - 1) 2^k and (c + 1) 2^k
        // on each side of it, and `hypot_rn` the one of them with an even significand, as for
        // hypot(134217729, 9007199388958720) = 2^53 + 2^27 + 1, whose tie goes down, and
        // hypot(4222124449333245, 10133099463573504) = 10977524293042179, which is 3 (m^2 + n^2)
        // for m = 3 2^24 and n = 2^25 + 1 and whose tie goes up.
        #[test]
        fn hypot_midpoints() {
            let (a, b) = (134217729.0, 9007199388958720.0);
            let got = [hypot_rn(a, b), hypot_rd(a, b), hypot_ru(a, b)];
            assert_eq!(got, [b, b, 9007199388958722.0]);
            let (a, b) = (4222124449333245.0, 10133099463573504.0);
            let (lo, hi) = (10977524293042178.0, 10977524293042180.0);
            let got = [hypot_rn(a, b), hypot_rd(a, b), hypot_ru(a, b)];
            assert_eq!(got, [hi, lo, hi]);
            let mut errs = vec![];
            let mut ups = 0;
            let mut rng = Rng(9);
            for i in 0..SAMPLES / 10 {
                let (a, b, c) = triple(&mut rng);
                let k = match i % 4 {
                    0 => -1074,
                    1 => 970,
                    _ => rng.below(2045) as i64 - 1074,
                };
                let s = pow2(k);
                let (a, b) = (a as f64 * s, b as f64 * s);
                let (lo, hi) = ((c - 1) as f64 * s, (c + 1) as f64 * s);
                let even = if (c - 1) % 4 == 0 {
                    lo
                } else {
                    ups += 1;
                    hi
                };
                let got = [hypot_rn(a, b), hypot_rd(a, b), hypot_ru(a, b)];
                assert_eq!(got, [even, lo, hi], "hypot({a:e}, {b:e})");
                for x in around(a) {
                    for y in around(b) {
                        let (x, y) = rng.pair(x, y);
                        check_hypot(&mut errs, x, y);
                    }
                }
            }
            assert!(ups > SAMPLES / 100, "{ups} ties up");
            report(errs);
        }

        // hypot at pairs of subnormals or zeros, and at a subnormal and a small normal `f64`;
        // hypot(2^-1074, 2^-1074) = 2^-1074 √2 rounds to 2^-1074 toward -∞ and to nearest,
        // and to 2^-1073 toward +∞.
        #[test]
        fn hypot_subnormal() {
            let t = f64::from_bits(1);
            let got = [hypot_rn(t, -t), hypot_rd(-t, t), hypot_ru(t, t)];
            assert_eq!(got, [t, t, 2.0 * t]);
            let mut errs = vec![];
            let mut rng = Rng(10);
            for _ in 0..SAMPLES {
                let x = rng.subnormal();
                let y = if rng.below(2) == 0 {
                    rng.subnormal()
                } else {
                    rng.scaled(-1022, -990)
                };
                check_hypot(&mut errs, x, y);
            }
            report(errs);
        }

        // hypot near overflow: at ±MAX twice, where the result is above 2^1024; at MAX and 1,
        // where it is above MAX by less than an ulp, so that `hypot_ru` gives +∞; at MAX and y
        // near 2^997.5, where the result crosses 2^1024 - 2^970, above which it rounds to +∞
        // to nearest; at x and y near MAX / √2, where it is near MAX; and at random pairs of
        // large `f64`s.
        #[test]
        fn hypot_max() {
            use std::f64::consts::{FRAC_1_SQRT_2, SQRT_2};
            let max = f64::MAX;
            let got = [hypot_rn(max, 1.0), hypot_rd(max, 1.0), hypot_ru(max, 1.0)];
            assert_eq!(got, [max, max, f64::INFINITY]);
            let mut errs = vec![];
            for (x, y) in [(max, max), (-max, max), (max, 1.0)] {
                check_hypot(&mut errs, x, y);
            }
            for y in within(SQRT_2 * pow2(997), 16) {
                check_hypot(&mut errs, max, y);
                check_hypot(&mut errs, -y, -max);
            }
            for x in within(max * FRAC_1_SQRT_2, 4) {
                for y in within(max * FRAC_1_SQRT_2, 4) {
                    check_hypot(&mut errs, x, -y);
                }
            }
            let mut rng = Rng(11);
            for _ in 0..SAMPLES {
                let (x, y) = (rng.scaled(1015, 1023), rng.scaled(900, 1023));
                let (x, y) = rng.pair(x, y);
                check_hypot(&mut errs, x, y);
            }
            report(errs);
        }

        // The nearest roundings of `mpfr_near!` round once below `f64::MIN_POSITIVE`: at the
        // tie 2^-1075 between 0 and the least subnormal 2^-1074, to the even 0, and at random
        // x at which 2^x and e^x are subnormal, below 2^-1075 or just above
        // `f64::MIN_POSITIVE`, to what `Float::to_f64` (`mpfr::get_d` rounded to nearest)
        // gives from 2^x and e^x at 256 bits, which keeps a value off a midpoint of the
        // subnormals on its side unless it is within 2^-256 of the midpoint, relatively.
        #[test]
        fn oracle_rounds_once() {
            assert_eq!(oracle::exp2_rn(-1075.0).to_bits(), 0);
            assert_eq!(oracle::exp2_rn(-1074.5).to_bits(), 1);
            assert_eq!(oracle::exp2_rn(-1074.0).to_bits(), 1);
            assert_eq!(oracle::pow_rn(0.5, 1075.0).to_bits(), 0);
            assert_eq!(oracle::pown_rn(-2.0, -1075).to_bits(), (-0.0f64).to_bits());
            assert_eq!(oracle::pown_rn(2.0, -1074).to_bits(), 1);
            let mut rng = Rng(5);
            for _ in 0..SAMPLES {
                // In (-1076, -1022] and (-746, -708].
                let u = rng.unit();
                let (x2, xe) = (-1022.0 - 54.0 * u, -708.0 - 38.0 * u);
                let want2 = Float::with_val(256, x2).exp2().to_f64();
                let wante = Float::with_val(256, xe).exp().to_f64();
                assert_eq!(
                    oracle::exp2_rn(x2).to_bits(),
                    want2.to_bits(),
                    "exp2({x2:e})"
                );
                assert_eq!(oracle::exp_rn(xe).to_bits(), wante.to_bits(), "exp({xe:e})");
            }
        }
    }
}
