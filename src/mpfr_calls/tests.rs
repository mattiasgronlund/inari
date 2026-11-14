// The two backends of `src/mpfr_calls.rs` against each other: each `<f>_rd` and `<f>_ru` of
// `src/mpfr_calls/kernel.rs`, which the library uses, against the one of the same name in
// `src/mpfr_calls/mpfr.rs`, bit for bit, and the elementary functions of `src/elementary.rs`
// against the bounds that the MPFR backend gives.
//
// The `seam_` tests call the 46 functions of both backends directly: on structured arguments
// (the zeros, the infinities, NaN, subnormals, integers, halves, the ends of the domains and
// the thresholds of the rules of the kernel, huge and tiny numbers, and the `f64`s next to
// each), on pairs of them for `atan2`, `hypot` and `pow`, and with special exponents for
// `pown`, and on random arguments: any 64 bits, a uniform biased exponent (log-uniform), and
// arguments in the range where each function is not settled by a rule, and for `cbrt` and
// `hypot` exact results and the `f64`s next to them, results midway between two `f64`s, gaps
// between the exponents of the arguments of `hypot` near the one from which a rule settles
// it, overflow and subnormals. The `intervals_` tests compute each of the 23 elementary
// functions of `Interval` and of `DecInterval` with each backend on random intervals, through
// the switch `with_mpfr` below, which `mpfr_in_tests!` of `src/mpfr_calls/kernel.rs` reads.
// `soak`, which is ignored, runs the random `seam_` cases with a seed and a count from the
// environment.
//
// Results are compared by their bits, so that the sign of a zero counts, and two NaNs are
// equal whatever their bits. A panic of either backend is a mismatch too. Each mismatch is a
// bug of the kernel (or of MPFR): its arguments go into `regressions()` of the tests of the
// family of the function in `src/dyadic/`, as AGENTS.md says, and a mismatch of intervals
// also prints the mismatches of the functions of the seam at the bounds of its arguments.
//
// The tests also record, in each case of a function of the seam, the levels of Ziv's strategy
// that the kernel used, which `ziv_level` of `src/dyadic.rs` gives: the level at which it
// returned, 1, 2, 4, 8, 16 or 32 limbs, 64 at the cap, or none where the kernel settled the
// case without `ziv`, by a rule or as a special case, and how many rounding tests failed before
// it. A case counts as retried if one did. `pow` and `pown` start Ziv's strategy at 2 limbs for
// large exponents (`src/dyadic/pow.rs`), so that a case of theirs can reach level 2 without a
// retry. `cbrt` and `hypot` never call `ziv` (`src/dyadic/root.rs`), so each of their cases is
// at none.
// `soak` prints, for each function, how many cases returned at each level and how many of
// those were retried, and then the cases past level 1: all of them if there are at most `KEPT`
// (100), and otherwise at most `SHOWN` (20) of those at the two highest levels that they
// reached, the highest level first and the retried cases first at each level.
// `src/dyadic/exp/tests/levels.rs` and the other `levels.rs` force each level with `ziv_at`.

use super::{kernel, mpfr};
use crate::{dyadic, DecInterval, Decoration, Interval};
use std::{
    cell::Cell,
    f64::consts::{FRAC_PI_2, FRAC_PI_4, PI, SQRT_2},
    panic::{catch_unwind, AssertUnwindSafe},
    thread,
    time::{Instant, SystemTime, UNIX_EPOCH},
};

thread_local! {
    // Whether the functions of `src/mpfr_calls/kernel.rs` return the results of the MPFR
    // backend on this thread, and how many times they have.
    static MPFR: Cell<(bool, u64)> = const { Cell::new((false, 0)) };
}

// Whether the functions of `src/mpfr_calls/kernel.rs` return the results of the MPFR backend
// on this thread, which `mpfr_in_tests!` there asks, counting the calls that do.
pub(super) fn use_mpfr() -> bool {
    MPFR.with(|m| {
        let (on, n) = m.get();
        if on {
            m.set((on, n + 1));
        }
        on
    })
}

// The number of calls of the functions of `src/mpfr_calls/kernel.rs` on this thread that have
// returned the results of the MPFR backend.
fn mpfr_count() -> u64 {
    MPFR.with(|m| m.get().1)
}

// `f()`, with the functions of `src/mpfr_calls/kernel.rs` returning the results of the MPFR
// backend on this thread while it runs. They return the kernel's again when `f` returns or
// panics.
fn with_mpfr<T>(f: impl FnOnce() -> T) -> T {
    struct Off;
    impl Drop for Off {
        fn drop(&mut self) {
            MPFR.with(|m| m.set((false, m.get().1)));
        }
    }
    MPFR.with(|m| m.set((true, m.get().1)));
    let _off = Off;
    f()
}

type F1 = fn(f64) -> f64;
type F2 = fn(f64, f64) -> f64;
type Fi = fn(f64, i32) -> f64;

// `(name, [rd, ru] of the kernel backend, [rd, ru] of the MPFR backend)` for each function `$f`
// of one `f64`.
macro_rules! unary {
    ($($f:ident, $f_rd:ident, $f_ru:ident;)*) => {
        [$((
            stringify!($f),
            [kernel::$f_rd as F1, kernel::$f_ru],
            [mpfr::$f_rd as F1, mpfr::$f_ru],
        )),*]
    };
}

// The 19 functions of one `f64` of the seam.
const UNARY: [(&str, [F1; 2], [F1; 2]); 19] = unary! {
    acos, acos_rd, acos_ru;
    acosh, acosh_rd, acosh_ru;
    asin, asin_rd, asin_ru;
    asinh, asinh_rd, asinh_ru;
    atan, atan_rd, atan_ru;
    atanh, atanh_rd, atanh_ru;
    cbrt, cbrt_rd, cbrt_ru;
    cos, cos_rd, cos_ru;
    cosh, cosh_rd, cosh_ru;
    exp, exp_rd, exp_ru;
    exp10, exp10_rd, exp10_ru;
    exp2, exp2_rd, exp2_ru;
    ln, ln_rd, ln_ru;
    log10, log10_rd, log10_ru;
    log2, log2_rd, log2_ru;
    sin, sin_rd, sin_ru;
    sinh, sinh_rd, sinh_ru;
    tan, tan_rd, tan_ru;
    tanh, tanh_rd, tanh_ru;
};

// The 3 functions of two `f64`s of the seam, with their arguments in the order of the seam:
// `atan2_rd(y, x)`, `pow_rd(x, y)` and `hypot_rd(x, y)`.
const ATAN2: usize = 0;
const POW: usize = 1;
const HYPOT: usize = 2;
const BINARY: [(&str, [F2; 2], [F2; 2]); 3] = [
    (
        "atan2",
        [kernel::atan2_rd, kernel::atan2_ru],
        [mpfr::atan2_rd, mpfr::atan2_ru],
    ),
    (
        "pow",
        [kernel::pow_rd, kernel::pow_ru],
        [mpfr::pow_rd, mpfr::pow_ru],
    ),
    (
        "hypot",
        [kernel::hypot_rd, kernel::hypot_ru],
        [mpfr::hypot_rd, mpfr::hypot_ru],
    ),
];

// `pown_rd` and `pown_ru` of the kernel backend and of the MPFR backend.
const POWN: ([Fi; 2], [Fi; 2]) = (
    [kernel::pown_rd, kernel::pown_ru],
    [mpfr::pown_rd, mpfr::pown_ru],
);

const DIRECTIONS: [&str; 2] = ["rd", "ru"];

type I1 = fn(Interval) -> Interval;
type D1 = fn(DecInterval) -> DecInterval;

// `(name of the function of the seam that it calls, Interval::$f, DecInterval::$f)` for each
// elementary function `$f` of one interval.
macro_rules! interval_unary {
    ($($f:ident,)*) => {
        [$((stringify!($f), Interval::$f as I1, DecInterval::$f as D1)),*]
    };
}

// The 19 elementary functions of one interval. The other 4 are `atan2`, `hypot`, `pow` and
// `powi`.
const INTERVAL_UNARY: [(&str, I1, D1); 19] = interval_unary! {
    acos, acosh, asin, asinh, atan, atanh, cbrt, cos, cosh, exp, exp10, exp2, ln, log10, log2,
    sin, sinh, tan, tanh,
};

// The exponents of `pown` that the structured cases take, with every argument: the ends of
// the range of `i32`, 0, ±1, small ones, and those near the exponents at which x^n of an
// `f64` overflows or underflows.
const EXPONENTS: [i32; 26] = [
    i32::MIN,
    i32::MIN + 1,
    -1075,
    -1074,
    -1024,
    -1023,
    -64,
    -53,
    -4,
    -3,
    -2,
    -1,
    0,
    1,
    2,
    3,
    4,
    5,
    53,
    64,
    1023,
    1024,
    1074,
    1075,
    i32::MAX - 1,
    i32::MAX,
];

// The `f64` after `x` toward +∞, and NaN and +∞ themselves. `f64::next_up` came with Rust
// 1.86, after the MSRV of the time, 1.65.
fn next_up(x: f64) -> f64 {
    if x.is_nan() || x == f64::INFINITY {
        x
    } else if x == 0.0 {
        f64::from_bits(1)
    } else if x > 0.0 {
        f64::from_bits(x.to_bits() + 1)
    } else {
        f64::from_bits(x.to_bits() - 1)
    }
}

// The `f64` before `x` toward -∞, and NaN and -∞ themselves.
fn next_down(x: f64) -> f64 {
    -next_up(-x)
}

// The structured arguments: those that the header names, and the `f64`s on each side of each,
// all of both signs. The constants beyond 10 are the thresholds of the rules of the kernel
// that the tests of its families take, such as 709.782712893384, about ln(f64::MAX).
fn structured() -> Vec<f64> {
    let base = [
        0.0,
        f64::INFINITY,
        f64::NAN,
        // 2^-1074 and 2^-1073.
        5e-324,
        1e-323,
        // The greatest subnormal, the least normal number, and some tiny ones.
        f64::from_bits(0x000f_ffff_ffff_ffff),
        f64::MIN_POSITIVE,
        1e-300,
        // 2^-60, 2^-27 and 2^-26, where the rules for tiny arguments end.
        8.673_617_379_884_035e-19,
        7.450_580_596_923_828e-9,
        1.490_116_119_384_765_6e-8,
        f64::EPSILON / 4.0,
        f64::EPSILON,
        0.25,
        0.5,
        0.75,
        1.0,
        1.25,
        1.5,
        2.0,
        2.5,
        3.0,
        4.0,
        7.5,
        10.0,
        18.714_973_875_118_524,
        19.0,
        22.0,
        100.0,
        308.254_715_559_916_75,
        309.0,
        323.306_215_343_115_8,
        324.0,
        709.782_712_893_384,
        710.0,
        710.475_860_073_944,
        711.0,
        744.440_071_921_381_2,
        745.133_219_101_941_2,
        746.0,
        1022.0,
        1024.0,
        1074.0,
        1075.0,
        1e6,
        // 2^52, 2^53, 2^63 and 2^64, from which on every `f64` is an integer or even.
        4_503_599_627_370_496.0,
        9_007_199_254_740_992.0,
        9_223_372_036_854_775_808.0,
        18_446_744_073_709_551_616.0,
        1e22,
        1e300,
        f64::MAX,
        FRAC_PI_4,
        FRAC_PI_2,
        PI,
        2.0 * PI,
    ];
    let mut v: Vec<f64> = Vec::new();
    for x in base {
        for y in [next_down(x), x, next_up(x)] {
            for z in [y, -y] {
                if !v.iter().any(|w| w.to_bits() == z.to_bits()) {
                    v.push(z);
                }
            }
        }
    }
    v
}

// SplitMix64, as `Rng` of `src/dyadic/tests.rs`, which `src/dyadic.rs` keeps to itself.
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

    fn pick<T: Copy>(&mut self, v: &[T]) -> T {
        v[self.below(v.len() as u64) as usize]
    }

    // `x` or `-x`, each half the time.
    fn signed(&mut self, x: f64) -> f64 {
        if self.next() & 1 == 0 {
            x
        } else {
            -x
        }
    }

    // A uniform `f64` in [a, b]: a + (b - a) u, for u uniform among the multiples of 2^-53
    // in [0, 1).
    fn uniform(&mut self, a: f64, b: f64) -> f64 {
        a + (b - a) * ((self.next() >> 11) as f64 / 9_007_199_254_740_992.0)
    }

    // Any `f64`, NaN and the infinities included: 64 random bits.
    fn bits(&mut self) -> f64 {
        f64::from_bits(self.next())
    }

    // A finite `f64` of either sign whose biased exponent is uniform in [0, 2046], so that its
    // magnitude is about log-uniform, from the subnormals to `f64::MAX`.
    fn log_uniform(&mut self) -> f64 {
        let sign = self.next() & (1 << 63);
        let e = self.below(2047);
        f64::from_bits(sign | e << 52 | self.next() >> 12)
    }

    // A positive `f64` in [2^lo, 2^hi) whose exponent is uniform in [lo, hi), for
    // -1022 <= lo < hi <= 1024.
    fn magnitude(&mut self, lo: i32, hi: i32) -> f64 {
        let e = lo + self.below((hi - lo) as u64) as i32;
        f64::from_bits(((e + 1023) as u64) << 52 | self.next() >> 12)
    }

    // `x` moved by up to 4 `f64`s toward either side.
    fn near(&mut self, x: f64) -> f64 {
        let k = self.below(9) as i32 - 4;
        let mut y = x;
        for _ in 0..k.abs() {
            y = if k > 0 { next_up(y) } else { next_down(y) };
        }
        y
    }

    // `x` moved by up to 8 `f64`s toward +∞.
    fn above(&mut self, x: f64) -> f64 {
        let mut y = x;
        for _ in 0..self.below(9) {
            y = next_up(y);
        }
        y
    }
}

// 2^e, for -1074 <= e <= 1023.
fn pow2(e: i32) -> f64 {
    if e >= -1022 {
        f64::from_bits(((e + 1023) as u64) << 52)
    } else {
        f64::from_bits(1 << (e + 1074))
    }
}

// An argument of the function `name` of one `f64` in the range where the rules of the kernel do
// not settle it, or at the ends of its domain, and for `cbrt` one at which its result is exact,
// or next to one.
fn focused(rng: &mut Rng, name: &str) -> f64 {
    let k = rng.below(4);
    match name {
        "acos" | "asin" | "atanh" => match k {
            0 => rng.uniform(-1.0, 1.0),
            1 => {
                let one = rng.signed(1.0);
                rng.near(one)
            }
            2 => {
                let t = rng.magnitude(-60, -1);
                rng.signed(1.0 - t)
            }
            _ => {
                let t = rng.magnitude(-60, 0);
                rng.signed(t)
            }
        },
        "acosh" => match k {
            0 => rng.near(1.0),
            1 => 1.0 + rng.magnitude(-60, 0),
            _ => rng.magnitude(0, 1024),
        },
        "ln" | "log2" | "log10" => match k {
            0 => rng.near(1.0),
            1 => {
                let t = rng.magnitude(-60, -1);
                1.0 + rng.signed(t)
            }
            2 => f64::from_bits(rng.below(1 << 52)),
            _ => rng.magnitude(-1022, 1024),
        },
        "exp" => rng.uniform(-746.0, 710.0),
        "exp2" => rng.uniform(-1076.0, 1025.0),
        "exp10" => rng.uniform(-325.0, 309.0),
        "sinh" | "cosh" if k == 0 => {
            let t = rng.magnitude(-60, 0);
            rng.signed(t)
        }
        "sinh" | "cosh" => rng.uniform(-711.0, 711.0),
        "tanh" if k == 0 => {
            let t = rng.magnitude(-60, 0);
            rng.signed(t)
        }
        "tanh" => rng.uniform(-20.0, 20.0),
        "sin" | "cos" | "tan" => match k {
            0 => rng.uniform(-10.0, 10.0),
            // Near a multiple of π/2, where the result or the reduced argument is small.
            1 => {
                let n = rng.below(1 << 20) as f64;
                let x = rng.signed(n * FRAC_PI_2);
                rng.near(x)
            }
            _ => {
                let t = rng.magnitude(-30, 1024);
                rng.signed(t)
            }
        },
        "cbrt" => {
            let x = match k {
                // A perfect cube n^3 2^(3e), whose cube root n 2^e is exact, or an `f64` next to
                // one. n^3 <= 2^51, and -1074 <= 3e <= 972, so that the cube is an `f64`, from
                // the subnormals to near `f64::MAX`.
                0 | 1 => {
                    let bits = 1 + rng.below(17);
                    let n = 1 + rng.below(1 << bits);
                    let e = rng.below(683) as i32 - 358;
                    let c = (n * n * n) as f64 * pow2(3 * e);
                    if k == 0 {
                        c
                    } else {
                        rng.near(c)
                    }
                }
                // A subnormal.
                2 => f64::from_bits(rng.below(1 << 52)),
                _ => rng.magnitude(-1022, 1024),
            };
            rng.signed(x)
        }
        _ => {
            let t = rng.magnitude(-60, 60);
            rng.signed(t)
        }
    }
}

// A random argument of the function `name` of one `f64`: any bits, log-uniform, or focused.
fn arg(rng: &mut Rng, name: &str) -> f64 {
    match rng.below(8) {
        0 => rng.bits(),
        1 | 2 => rng.log_uniform(),
        _ => focused(rng, name),
    }
}

// A random pair of arguments of `atan2(y, x)`: each any bits, log-uniform, a structured one or
// of a moderate magnitude, and sometimes y near ±x, where atan2 is near an odd multiple of π/4.
fn atan2_args(rng: &mut Rng, structured: &[f64]) -> (f64, f64) {
    let one = |rng: &mut Rng| match rng.below(6) {
        0 => rng.bits(),
        1 => rng.log_uniform(),
        2 => rng.pick(structured),
        _ => {
            let t = rng.magnitude(-60, 60);
            rng.signed(t)
        }
    };
    let x = one(rng);
    let y = if rng.below(8) == 0 {
        let s = rng.signed(x);
        rng.near(s)
    } else {
        one(rng)
    };
    (y, x)
}

// A random pair of arguments of `pow(x, y)`: x mostly positive and of a moderate magnitude or
// near 1, and y an integer, a half-integer or of a moderate magnitude, each also any bits or
// log-uniform.
fn pow_args(rng: &mut Rng) -> (f64, f64) {
    let x = match rng.below(8) {
        0 => rng.bits(),
        1 => rng.log_uniform(),
        2 => rng.near(1.0),
        3 => {
            let t = rng.magnitude(-60, -1);
            1.0 + rng.signed(t)
        }
        4 => -rng.magnitude(-60, 60),
        _ => rng.magnitude(-60, 60),
    };
    let y = match rng.below(8) {
        0 => rng.bits(),
        1 => rng.log_uniform(),
        2 => rng.below(201) as f64 - 100.0,
        3 => rng.below(201) as f64 - 100.5,
        4 | 5 => rng.uniform(-60.0, 60.0),
        _ => {
            let t = rng.magnitude(-60, 60);
            rng.signed(t)
        }
    };
    (x, y)
}

// A random pair of arguments of `hypot(x, y)`, each of either sign and in either order: each
// any bits, log-uniform or structured; a Pythagorean triple, whose result is exact; the
// exponents of |x| and |y| apart by about 27, the gap from which the kernel takes the larger
// argument's significand (`hypot_odd` of `src/dyadic/root.rs`), or by about 54; near
// `f64::MAX`, `f64::MAX / √2` or `f64::MAX / 2`, where hypot overflows or nearly does; or both
// subnormal.
fn hypot_args(rng: &mut Rng, structured: &[f64]) -> (f64, f64) {
    let one = |rng: &mut Rng| match rng.below(3) {
        0 => rng.bits(),
        1 => rng.log_uniform(),
        _ => rng.pick(structured),
    };
    let (x, y) = match rng.below(8) {
        0 | 1 => (one(rng), one(rng)),
        // A small triple, or one of Euclid's (m^2 - n^2, 2 m n, m^2 + n^2) with
        // 0 < n < m <= 2^26, so that each number is an integer below 2^53, times 2^e, with
        // -1074 <= e <= 970, so that the three stay exact and finite.
        2 => {
            let (a, b) = match rng.below(2) {
                0 => rng.pick(&[(3, 4), (5, 12), (8, 15), (20, 21)]),
                _ => {
                    let bits = 2 + rng.below(25);
                    let m = 2 + rng.below((1 << bits) - 1);
                    let n = 1 + rng.below(m - 1);
                    (m * m - n * n, 2 * m * n)
                }
            };
            let s = pow2(rng.below(2045) as i32 - 1074);
            (a as f64 * s, b as f64 * s)
        }
        // The triples (2 m + 1, 2 m (m + 1), 2 m (m + 1) + 1) with 2^26 <= m < 2^26.5, whose
        // result is an odd integer in [2^53, 2^54), so that times 2^e it is midway between two
        // `f64`s, as hypot(134217729, 9007199388958720) = 9007199388958721 of
        // `src/dyadic/root.rs` (m = 2^26). The legs are integers below 2^54, the larger one
        // even, so `f64`s.
        3 => {
            let m = (1 << 26) + rng.below(27_797_401);
            let e = rng.below(1940) as i32 - 970;
            (
                (2 * m + 1) as f64 * pow2(e),
                (2 * m * (m + 1)) as f64 * pow2(e),
            )
        }
        // Exponents apart by g, for g near 27 or 54.
        4 | 5 => {
            let g = rng.pick(&[27, 54]) + rng.below(5) as i32 - 2;
            let e = rng.below(1800) as i32 - 900;
            (rng.magnitude(e, e + 1), rng.magnitude(e - g, e - g + 1))
        }
        // Two of these big numbers, or one of them and an argument from `one`, each moved by up
        // to 4 `f64`s (`f64::MAX` moved up is +∞).
        6 => {
            let big = [f64::MAX, f64::MAX / SQRT_2, f64::MAX / 2.0];
            let x = rng.pick(&big);
            let y = match rng.below(3) {
                0 => one(rng),
                _ => rng.pick(&big),
            };
            (rng.near(x), rng.near(y))
        }
        _ => (
            f64::from_bits(rng.below(1 << 52)),
            f64::from_bits(rng.below(1 << 52)),
        ),
    };
    let (x, y) = (rng.signed(x), rng.signed(y));
    if rng.below(2) == 0 {
        (x, y)
    } else {
        (y, x)
    }
}

// A random pair of arguments of `pown(x, n)`: x as an argument of `pow`, and n small, one of
// `EXPONENTS` or any `i32`.
fn pown_args(rng: &mut Rng) -> (f64, i32) {
    let (x, _) = pow_args(rng);
    let x = rng.signed(x);
    let n = match rng.below(4) {
        0 => rng.next() as i32,
        1 => rng.pick(&EXPONENTS),
        _ => rng.below(81) as i32 - 40,
    };
    (x, n)
}

// What the tests compare: bit for bit, but two NaNs or two empty intervals are equal whatever
// their bits.
trait Bits: Copy {
    fn same(self, other: Self) -> bool;
    fn show(self) -> String;
}

impl Bits for f64 {
    fn same(self, other: Self) -> bool {
        self.to_bits() == other.to_bits() || self.is_nan() && other.is_nan()
    }

    fn show(self) -> String {
        format!("{:e} ({:#018x})", self, self.to_bits())
    }
}

impl Bits for Interval {
    fn same(self, other: Self) -> bool {
        if self.is_empty() || other.is_empty() {
            self.is_empty() && other.is_empty()
        } else {
            self.inf_raw().same(other.inf_raw()) && self.sup_raw().same(other.sup_raw())
        }
    }

    fn show(self) -> String {
        if self.is_empty() {
            String::from("[empty]")
        } else {
            format!("[{:e}, {:e}]", self.inf_raw(), self.sup_raw())
        }
    }
}

impl Bits for DecInterval {
    fn same(self, other: Self) -> bool {
        self.decoration() == other.decoration()
            && match (self.interval(), other.interval()) {
                (Some(x), Some(y)) => x.same(y),
                (x, y) => x.is_none() && y.is_none(),
            }
    }

    fn show(self) -> String {
        match self.interval() {
            Some(x) => format!("{}_{:?}", x.show(), self.decoration()),
            None => String::from("[nai]"),
        }
    }
}

// The levels of Ziv's strategy at which the kernel can return, as `dyadic::ziv_level` gives
// them: 0 where it did not call `ziv`, and otherwise the number of limbs.
const LEVELS: [usize; 8] = [0, 1, 2, 4, 8, 16, 32, 64];

// How many cases past level 1 `Levels` keeps at each level, so that it keeps all of them for a
// function that has at most this many.
const KEPT: usize = 100;

// How many cases past level 1 `soak` prints for a function that has more than `KEPT`.
const SHOWN: usize = 20;

// The name of the level `LEVELS[j]`.
fn level_name(j: usize) -> String {
    match LEVELS[j] {
        0 => String::from("none"),
        64 => String::from("cap"),
        n => n.to_string(),
    }
}

// How many cases of the function `name` the kernel returned at each of `LEVELS`, how many of
// those were retried, that is, a rounding test failed in them, and the first `KEPT` cases at
// each level past 1 that were retried and the first `KEPT` that were not, each with the number
// of tests that failed in it and its arguments as a mismatch prints them.
struct Levels {
    name: &'static str,
    counts: [u64; 8],
    retried: [u64; 8],
    cases: [[Vec<(usize, String)>; 2]; 8],
}

impl Levels {
    fn new(name: &'static str) -> Self {
        Self {
            name,
            counts: [0; 8],
            retried: [0; 8],
            cases: Default::default(),
        }
    }

    // Records that the kernel returned at `level` after `failed` failed rounding tests in the
    // case that `what` prints.
    fn record(&mut self, (level, failed): (usize, usize), what: impl FnOnce() -> String) {
        let j = LEVELS.iter().position(|&l| l == level).unwrap();
        self.counts[j] += 1;
        if failed > 0 {
            self.retried[j] += 1;
        }
        // `cases[j][0]` keeps the retried cases and `cases[j][1]` the others, which `print`
        // shows after them.
        let cases = &mut self.cases[j][usize::from(failed == 0)];
        if level > 1 && cases.len() < KEPT {
            cases.push((failed, what()));
        }
    }

    // Prints the counts, and the cases past level 1, as the header says.
    fn print(&self) {
        let counts: Vec<String> = (0..LEVELS.len())
            .map(|j| match self.retried[j] {
                0 => format!("{} {}", level_name(j), self.counts[j]),
                r => format!("{} {} ({} retried)", level_name(j), self.counts[j], r),
            })
            .collect();
        println!(
            "soak: {}: {} cases by level: {}",
            self.name,
            self.counts.iter().sum::<u64>(),
            counts.join(", ")
        );
        // The levels past 1 that the cases reached, the highest first.
        let reached: Vec<usize> = (0..LEVELS.len())
            .rev()
            .filter(|&j| LEVELS[j] > 1 && self.counts[j] > 0)
            .collect();
        let past_1: u64 = reached.iter().map(|&j| self.counts[j]).sum();
        if past_1 == 0 {
            return;
        }
        // Each level keeps `KEPT` cases of each kind, so that all of them are kept if
        // `past_1 <= KEPT`.
        let (shown, limit) = if past_1 <= KEPT as u64 {
            println!("soak: {}: the {} cases past level 1:", self.name, past_1);
            (&reached[..], KEPT)
        } else {
            let top = &reached[..reached.len().min(2)];
            let names: Vec<String> = top.iter().map(|&j| level_name(j)).collect();
            println!(
                "soak: {}: {} cases past level 1, of which at most {} at level{} {}:",
                self.name,
                past_1,
                SHOWN,
                if top.len() > 1 { "s" } else { "" },
                names.join(" and ")
            );
            (top, SHOWN)
        };
        let cases = shown.iter().flat_map(|&j| {
            let cases = self.cases[j].iter().flatten();
            cases.map(move |(failed, c)| (j, failed, c))
        });
        for (j, failed, c) in cases.take(limit) {
            let s = if *failed == 1 { "" } else { "s" };
            println!(
                "soak:   level {}, {} failed test{}: {}",
                level_name(j),
                failed,
                s,
                c
            );
        }
    }
}

// `f()`, a call of the kernel backend, with the levels that the kernel used in it, as
// `dyadic::ziv_level` gives them, set in `level`, which stays `(0, 0)` if `f` panics.
fn at_level<T>(level: &Cell<(usize, usize)>, f: impl FnOnce() -> T) -> T {
    dyadic::reset_ziv_level();
    let x = f();
    level.set(dyadic::ziv_level());
    x
}

// The comparisons of a test, and the mismatches among them, each as a line with the arguments,
// whose numbers parse back to the same `f64`s, and both results, and for each function of the
// seam that it compares, the levels at which the kernel returned.
struct Mismatches {
    compared: u64,
    lines: Vec<String>,
    levels: Vec<Levels>,
}

impl Mismatches {
    fn new() -> Self {
        Self {
            compared: 0,
            lines: Vec::new(),
            levels: Vec::new(),
        }
    }

    // Records the levels that the kernel used, as `dyadic::ziv_level` gives them, in the case of
    // the function of the seam `name` that `what` prints.
    fn level(&mut self, name: &'static str, level: (usize, usize), what: impl FnOnce() -> String) {
        let l = match self.levels.iter().position(|l| l.name == name) {
            Some(j) => &mut self.levels[j],
            None => {
                self.levels.push(Levels::new(name));
                self.levels.last_mut().unwrap()
            }
        };
        l.record(level, what);
    }

    // Compares `kernel()` with `mpfr()`, the same function at the arguments that `what`
    // prints, and records a mismatch if they differ or either panics.
    fn compare<T: Bits>(
        &mut self,
        what: impl FnOnce() -> String,
        kernel: impl FnOnce() -> T,
        mpfr: impl FnOnce() -> T,
    ) -> bool {
        self.compared += 1;
        let k = catch_unwind(AssertUnwindSafe(kernel));
        let m = catch_unwind(AssertUnwindSafe(mpfr));
        let same = match (&k, &m) {
            (Ok(k), Ok(m)) => k.same(*m),
            _ => false,
        };
        if !same {
            let show = |r: thread::Result<T>| match r {
                Ok(x) => x.show(),
                Err(_) => String::from("a panic"),
            };
            let line = format!("{}: kernel {}, MPFR {}", what(), show(k), show(m));
            self.lines.push(line);
        }
        same
    }

    // Each function of the seam at the arguments: `UNARY[i]`, `BINARY[i]`, `pown`.
    fn unary(&mut self, i: usize, x: f64) {
        let (name, k, m) = UNARY[i];
        for d in 0..2 {
            let what = || format!("{}_{}({:e})", name, DIRECTIONS[d], x);
            let level = Cell::new((0, 0));
            self.compare(what, || at_level(&level, || k[d](x)), || m[d](x));
            self.level(name, level.get(), what);
        }
    }

    fn binary(&mut self, i: usize, x: f64, y: f64) {
        // The kernel's `pow` is NaN for x < 0, as `src/dyadic/pow.rs` says, where MPFR differs
        // at an integer y. `Interval::pow` never passes such an x, as the tests of
        // `src/dyadic/pow/tests.rs` say too.
        if i == POW && x < 0.0 {
            return;
        }
        let (name, k, m) = BINARY[i];
        for d in 0..2 {
            let what = || format!("{}_{}({:e}, {:e})", name, DIRECTIONS[d], x, y);
            let level = Cell::new((0, 0));
            self.compare(what, || at_level(&level, || k[d](x, y)), || m[d](x, y));
            self.level(name, level.get(), what);
        }
    }

    fn pown(&mut self, x: f64, n: i32) {
        let (k, m) = POWN;
        for d in 0..2 {
            let what = || format!("pown_{}({:e}, {})", DIRECTIONS[d], x, n);
            let level = Cell::new((0, 0));
            self.compare(what, || at_level(&level, || k[d](x, n)), || m[d](x, n));
            self.level("pown", level.get(), what);
        }
    }

    // Panics with every mismatch, if there is one.
    fn assert_none(self, test: &str) {
        assert!(
            self.lines.is_empty(),
            "{}: {} mismatches in {} comparisons:\n{}",
            test,
            self.lines.len(),
            self.compared,
            self.lines.join("\n")
        );
    }
}

// The index in `UNARY` of the function `name`.
fn index(name: &str) -> usize {
    UNARY.iter().position(|(n, _, _)| *n == name).unwrap()
}

// The number of random cases per function, which can be set with `INARI_SEAM_N`.
fn n_cases() -> u64 {
    std::env::var("INARI_SEAM_N")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(if cfg!(debug_assertions) { 200 } else { 5_000 })
}

// The random numbers of the generator numbered `gen`, which `INARI_SEAM_SEED` changes.
fn rng(gen: u64) -> Rng {
    let seed = std::env::var("INARI_SEAM_SEED")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(0);
    Rng(seed.wrapping_add(gen << 32))
}

#[test]
fn seam_structured() {
    let v = structured();
    let mut m = Mismatches::new();
    for i in 0..UNARY.len() {
        for &x in &v {
            m.unary(i, x);
        }
    }
    for i in 0..BINARY.len() {
        for &x in &v {
            for &y in &v {
                m.binary(i, x, y);
            }
        }
    }
    for &x in &v {
        for n in EXPONENTS {
            m.pown(x, n);
        }
    }
    m.assert_none("seam_structured");
}

// `n` random cases of the function `UNARY[i]`.
fn random_unary(m: &mut Mismatches, rng: &mut Rng, i: usize, n: u64) {
    for _ in 0..n {
        let x = arg(rng, UNARY[i].0);
        m.unary(i, x);
    }
}

// `n` random cases of `atan2`, `pow`, `pown` and `hypot`.
fn random_binary(m: &mut Mismatches, rng: &mut Rng, structured: &[f64], n: u64) {
    for _ in 0..n {
        let (y, x) = atan2_args(rng, structured);
        m.binary(ATAN2, y, x);
        let (x, y) = pow_args(rng);
        m.binary(POW, x, y);
        let (x, n) = pown_args(rng);
        m.pown(x, n);
        let (x, y) = hypot_args(rng, structured);
        m.binary(HYPOT, x, y);
    }
}

#[test]
fn seam_random_unary() {
    let mut m = Mismatches::new();
    for i in 0..UNARY.len() {
        random_unary(&mut m, &mut rng(i as u64), i, n_cases());
    }
    m.assert_none("seam_random_unary");
}

#[test]
fn seam_random_binary() {
    let mut m = Mismatches::new();
    random_binary(&mut m, &mut rng(100), &structured(), n_cases());
    m.assert_none("seam_random_binary");
}

// A random interval of arguments from `arg`: empty, entire, half-bounded, a point, a few
// `f64`s wide, or the hull of two arguments.
fn interval(rng: &mut Rng, mut arg: impl FnMut(&mut Rng) -> f64) -> Interval {
    loop {
        let a = arg(rng);
        let (a, b) = match rng.below(16) {
            0 => return Interval::EMPTY,
            1 => return Interval::ENTIRE,
            2 => (a, f64::INFINITY),
            3 => (f64::NEG_INFINITY, a),
            4 | 5 => (a, a),
            6 | 7 => (a, rng.above(a)),
            _ => {
                let b = arg(rng);
                (a.min(b), a.max(b))
            }
        };
        if let Ok(x) = Interval::try_from((a, b)) {
            return x;
        }
    }
}

// `x` with a random decoration, or NaI.
fn decorated(rng: &mut Rng, x: Interval) -> DecInterval {
    use Decoration::*;
    if rng.below(32) == 0 {
        DecInterval::NAI
    } else {
        DecInterval::set_dec(x, rng.pick(&[Com, Dac, Def, Trv]))
    }
}

// An argument of the function `name` of the seam for an interval: mostly one from `arg`, and
// sometimes a structured one.
fn bound(rng: &mut Rng, name: &str, structured: &[f64]) -> f64 {
    if rng.below(4) == 0 {
        rng.pick(structured)
    } else {
        arg(rng, name)
    }
}

// Compares `f(x)` of each backend, for `f` the elementary function `INTERVAL_UNARY[i]` and its
// decorated version at `x` with a random decoration. On a mismatch, it also compares the
// functions of the seam that `f` calls at the bounds of `x`: for `sin`, `cos` and `tan`, also
// `sin` and `cos`, which `quadrant` in `src/elementary.rs` calls.
fn interval_unary(m: &mut Mismatches, rng: &mut Rng, i: usize, x: Interval) {
    let (name, f, g) = INTERVAL_UNARY[i];
    let what = || format!("Interval::{}({})", name, x.show());
    let mut same = m.compare(what, || f(x), || with_mpfr(|| f(x)));
    let dx = decorated(rng, x);
    let what = || format!("DecInterval::{}({})", name, dx.show());
    same &= m.compare(what, || g(dx), || with_mpfr(|| g(dx)));
    if !same && !x.is_empty() {
        let names: &[&str] = match name {
            "sin" | "cos" | "tan" => &["sin", "cos", "tan"],
            // Not `&[name]`: Rust 1.65 frees that temporary at the end of the `let`.
            _ => std::slice::from_ref(&name),
        };
        for name in names {
            m.unary(index(name), x.inf_raw());
            m.unary(index(name), x.sup_raw());
        }
    }
}

#[test]
fn intervals_unary() {
    let v = structured();
    let mut m = Mismatches::new();
    let before = mpfr_count();
    for (i, &(name, _, _)) in INTERVAL_UNARY.iter().enumerate() {
        let mut rng = rng(200 + i as u64);
        for _ in 0..n_cases() / 5 {
            let x = interval(&mut rng, |rng| bound(rng, name, &v));
            interval_unary(&mut m, &mut rng, i, x);
        }
    }
    // The switch reached the MPFR backend.
    assert!(mpfr_count() > before);
    m.assert_none("intervals_unary");
}

#[test]
fn intervals_binary() {
    let v = structured();
    let mut m = Mismatches::new();
    let before = mpfr_count();
    let mut rng = rng(300);
    for _ in 0..n_cases() / 5 {
        // atan2(y, x).
        let y = interval(&mut rng, |rng| atan2_args(rng, &v).0);
        let x = interval(&mut rng, |rng| atan2_args(rng, &v).1);
        let what = || format!("Interval::atan2({}, {})", y.show(), x.show());
        let mut same = m.compare(what, || y.atan2(x), || with_mpfr(|| y.atan2(x)));
        let (dy, dx) = (decorated(&mut rng, y), decorated(&mut rng, x));
        let what = || format!("DecInterval::atan2({}, {})", dy.show(), dx.show());
        same &= m.compare(what, || dy.atan2(dx), || with_mpfr(|| dy.atan2(dx)));
        if !same && !y.is_empty() && !x.is_empty() {
            for b in [y.inf_raw(), y.sup_raw()] {
                for a in [x.inf_raw(), x.sup_raw()] {
                    m.binary(ATAN2, b, a);
                }
            }
        }

        // pow(x, y), with y sometimes a point, at which `Interval::pow` takes other branches.
        let x = interval(&mut rng, |rng| pow_args(rng).0);
        let y = if rng.below(4) == 0 {
            let (_, y) = pow_args(&mut rng);
            Interval::try_from((y, y)).unwrap_or(Interval::EMPTY)
        } else {
            interval(&mut rng, |rng| pow_args(rng).1)
        };
        let what = || format!("Interval::pow({}, {})", x.show(), y.show());
        let mut same = m.compare(what, || x.pow(y), || with_mpfr(|| x.pow(y)));
        let (dx, dy) = (decorated(&mut rng, x), decorated(&mut rng, y));
        let what = || format!("DecInterval::pow({}, {})", dx.show(), dy.show());
        same &= m.compare(what, || dx.pow(dy), || with_mpfr(|| dx.pow(dy)));
        if !same && !x.is_empty() && !y.is_empty() {
            for a in [x.inf_raw(), x.sup_raw()] {
                for b in [y.inf_raw(), y.sup_raw()] {
                    m.binary(POW, a, b);
                }
            }
        }

        // powi(x, n).
        let (_, n) = pown_args(&mut rng);
        let x = interval(&mut rng, |rng| pown_args(rng).0);
        let what = || format!("Interval::powi({}, {})", x.show(), n);
        let mut same = m.compare(what, || x.powi(n), || with_mpfr(|| x.powi(n)));
        let dx = decorated(&mut rng, x);
        let what = || format!("DecInterval::powi({}, {})", dx.show(), n);
        same &= m.compare(what, || dx.powi(n), || with_mpfr(|| dx.powi(n)));
        if !same && !x.is_empty() {
            m.pown(x.inf_raw(), n);
            m.pown(x.sup_raw(), n);
        }

        // hypot(x, y), with x and y sometimes the points of one pair of `hypot_args`, so that
        // its triples and gaps reach the intervals too.
        let (x, y) = if rng.below(4) == 0 {
            let (a, b) = hypot_args(&mut rng, &v);
            let point = |a: f64| Interval::try_from((a, a)).unwrap_or(Interval::EMPTY);
            (point(a), point(b))
        } else {
            (
                interval(&mut rng, |rng| hypot_args(rng, &v).0),
                interval(&mut rng, |rng| hypot_args(rng, &v).1),
            )
        };
        let what = || format!("Interval::hypot({}, {})", x.show(), y.show());
        let mut same = m.compare(what, || x.hypot(y), || with_mpfr(|| x.hypot(y)));
        let (dx, dy) = (decorated(&mut rng, x), decorated(&mut rng, y));
        let what = || format!("DecInterval::hypot({}, {})", dx.show(), dy.show());
        same &= m.compare(what, || dx.hypot(dy), || with_mpfr(|| dx.hypot(dy)));
        if !same && !x.is_empty() && !y.is_empty() {
            // `Interval::hypot` calls `hypot_rd` at the lower bounds of |x| and |y|, and
            // `hypot_ru` at their upper bounds.
            let (x, y) = (x.abs(), y.abs());
            m.binary(HYPOT, x.inf_raw(), y.inf_raw());
            m.binary(HYPOT, x.sup_raw(), y.sup_raw());
        }
    }
    assert!(mpfr_count() > before);
    m.assert_none("intervals_binary");
}

// The switch reaches the MPFR backend for each of the 46 functions while `with_mpfr` runs, and
// only then.
#[test]
fn switch_reaches_mpfr() {
    let calls = |f: &dyn Fn() -> f64| {
        let before = mpfr_count();
        f();
        mpfr_count() - before
    };
    for (_, k, _) in UNARY {
        for f in k {
            assert_eq!(calls(&|| f(0.5)), 0);
            assert_eq!(calls(&|| with_mpfr(|| f(0.5))), 1);
        }
    }
    for (_, k, _) in BINARY {
        for f in k {
            assert_eq!(calls(&|| f(0.5, 0.5)), 0);
            assert_eq!(calls(&|| with_mpfr(|| f(0.5, 0.5))), 1);
        }
    }
    for f in POWN.0 {
        assert_eq!(calls(&|| f(0.5, 3)), 0);
        assert_eq!(calls(&|| with_mpfr(|| f(0.5, 3))), 1);
    }
    // And it is off again after a panic.
    let _ = catch_unwind(|| with_mpfr(|| -> f64 { panic!("in with_mpfr") }));
    assert!(!use_mpfr());
}

// The levels that the kernel used, as the tests record them: none for a case that a rule or
// the fast path of `exp`, `sin` or `pown` settles, the first level for most of the others, such
// as `sin` with the fast path off, a retry for a case that `soak` found past level 1, which the
// fast path settles and the kernel reaches only with the fast path off, and level 2 without a
// retry for `pown` of a large exponent, which starts at 2 limbs, with the fast path off. The
// MPFR backend does not call `ziv`.
#[test]
fn ziv_levels_recorded() {
    let levels = |f: &dyn Fn() -> f64| {
        let level = Cell::new((1, 1));
        at_level(&level, f);
        level.get()
    };
    assert_eq!(levels(&|| kernel::exp_rd(0.0)), (0, 0));
    assert_eq!(levels(&|| kernel::exp_rd(0.5)), (0, 0));
    assert_eq!(levels(&|| kernel::sin_rd(0.5)), (0, 0));
    dyadic::set_fast_path(false);
    let first = levels(&|| kernel::sin_rd(0.5));
    dyadic::set_fast_path(true);
    assert_eq!(first, (1, 0));
    assert_eq!(levels(&|| kernel::exp_rd(1.276253168049783e2)), (0, 0));
    dyadic::set_fast_path(false);
    let retry = levels(&|| kernel::exp_rd(1.276253168049783e2));
    let pown = levels(&|| kernel::pown_rd(1.5, 1000));
    dyadic::set_fast_path(true);
    assert_eq!(retry, (2, 1));
    assert_eq!(pown, (2, 0));
    assert_eq!(levels(&|| kernel::pown_rd(1.5, 1000)), (0, 0));
    assert_eq!(levels(&|| mpfr::exp_rd(1.276253168049783e2)), (0, 0));
}

// The random cases of `seam_random_unary` and `seam_random_binary`, `INARI_SOAK_COUNT` of each
// (default 1,000,000), from the seed `INARI_SOAK_SEED` (default: from the clock, and printed),
// with each function on a thread of its own, which prints the levels at which the kernel
// returned, as the header says. Run it with
// `cargo test --release --lib mpfr_calls::tests::soak -- --ignored --nocapture`.
#[test]
#[ignore]
fn soak() {
    let env = |name: &str| std::env::var(name).ok().and_then(|s| s.parse::<u64>().ok());
    let n = env("INARI_SOAK_COUNT").unwrap_or(1_000_000);
    let seed = env("INARI_SOAK_SEED").unwrap_or_else(|| {
        let t = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();
        t.as_secs() ^ u64::from(t.subsec_nanos())
    });
    println!("soak: INARI_SOAK_SEED={} INARI_SOAK_COUNT={}", seed, n);
    let v = structured();
    let rng = |gen: u64| Rng(seed.wrapping_add(gen << 32));
    let lines: Vec<String> = thread::scope(|s| {
        let mut threads = Vec::new();
        for (i, &(name, _, _)) in UNARY.iter().enumerate() {
            threads.push(s.spawn(move || {
                let start = Instant::now();
                let mut m = Mismatches::new();
                random_unary(&mut m, &mut rng(i as u64), i, n);
                (name, start.elapsed(), m)
            }));
        }
        threads.push(s.spawn(|| {
            let start = Instant::now();
            let mut m = Mismatches::new();
            random_binary(&mut m, &mut rng(100), &v, n);
            ("atan2, pow, pown, hypot", start.elapsed(), m)
        }));
        threads
            .into_iter()
            .flat_map(|t| {
                let (name, time, m) = t.join().unwrap();
                println!(
                    "soak: {}: {} comparisons, {} mismatches, {:.1} s",
                    name,
                    m.compared,
                    m.lines.len(),
                    time.as_secs_f64()
                );
                for l in &m.levels {
                    l.print();
                }
                m.lines
            })
            .collect()
    });
    assert!(
        lines.is_empty(),
        "soak (INARI_SOAK_SEED={}): {} mismatches:\n{}",
        seed,
        lines.len(),
        lines.join("\n")
    );
}
