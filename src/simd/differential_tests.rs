// Compares the rounding functions of the generic backend bit for bit with the
// backend of the target: on x86-64 with AVX-512F, the hardware backend
// (`avx512f`), which rounds with embedded rounding; otherwise (`fma`, `sse42`
// and, on wasm32, `wasm32`), the backend that vectorizes the fast paths of the
// generic one, and is compared with it.
// Both the FMA and the Dekker (no FMA) variants of the generic backend are tested.
// On wasm32, `f64::mul_add` is a software routine, but still correctly rounded.
// NaNs compare equal regardless of their sign and payload, which inari does not
// depend on (x86 returns a negative default NaN, the generic backend does not).
//
// The number of random cases per generator can be set with `INARI_DIFF_N`.
// Run with `--nocapture` to see the number of cases and mismatches.

use super::generic;
use std::fmt::Write;

cfg_if::cfg_if! {
    // `fma` and `sse42` take their square root from the generic backend, so it
    // is compared with the one that switches the rounding mode instead.
    if #[cfg(target_feature = "avx512f")] {
        use super::{sqrt1_rd as hw_sqrt1_rd, sqrt1_ru as hw_sqrt1_ru};
    } else if #[cfg(target_arch = "x86_64")] {
        use super::{sqrt1_rd_mxcsr as hw_sqrt1_rd, sqrt1_ru_mxcsr as hw_sqrt1_ru};
    }
}

struct Rng(u64);

impl Rng {
    // SplitMix64.
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

    fn sign(&mut self, x: f64) -> f64 {
        if self.next() & 1 == 0 {
            x
        } else {
            -x
        }
    }

    // A float with the given unbiased exponent (clamped to the subnormal range at
    // the bottom) and a random significand, which is sometimes short, so that
    // exact results and halfway cases are frequent.
    fn with_exponent(&mut self, e: i32) -> f64 {
        let mut frac = self.next() & ((1 << 52) - 1);
        match self.below(4) {
            0 => frac &= !((1 << self.below(53)) - 1),
            1 => frac |= (1 << self.below(53)) - 1,
            _ => (),
        }
        let biased = (e + 1023).clamp(0, 2046) as u64;
        self.sign(f64::from_bits(biased << 52 | frac))
    }

    fn any(&mut self) -> f64 {
        match self.below(32) {
            0 => {
                let x = SPECIAL[self.below(SPECIAL.len() as u64) as usize];
                self.sign(x)
            }
            1 => self.with_exponent(-1023),
            2 => {
                let e = BOUNDARY_EXPONENTS[self.below(BOUNDARY_EXPONENTS.len() as u64) as usize];
                let e = e + self.below(5) as i32 - 2;
                self.with_exponent(e)
            }
            _ => {
                let e = self.below(2047) as i32 - 1023;
                self.with_exponent(e)
            }
        }
    }

    // A random exponent that makes x ∘ y land near an interesting range.
    fn exponent_near_boundary(&mut self) -> i32 {
        let e = BOUNDARY_EXPONENTS[self.below(BOUNDARY_EXPONENTS.len() as u64) as usize];
        e + self.below(9) as i32 - 4
    }

    // Moves x by a few ulps, keeping its sign. The magnitude stops at zero, and
    // may go from MAX to ∞.
    fn nudge(&mut self, x: f64) -> f64 {
        if !x.is_finite() {
            return x;
        }
        let k = self.below(5) as i64 - 2;
        let m = (x.abs().to_bits() as i64 + k).max(0) as u64;
        f64::from_bits(m).copysign(x)
    }
}

const SPECIAL: [f64; 9] = [
    0.0,
    f64::INFINITY,
    f64::NAN,
    f64::MAX,
    f64::MIN_POSITIVE,
    5e-324, // 2^-1074
    1.0,
    2.225073858507201e-308, // The largest subnormal number.
    1.3407807929942596e154, // 2^512
];

// Exponents around the thresholds of the fast paths and of the format. Below
// 2^-1075, a product rounds to ±0, which `mul_ru_tiny` in the `fma`, `sse42` and
// `wasm32` backends and `generic::mul1_ru_tiny` handle separately.
const BOUNDARY_EXPONENTS: [i32; 15] = [
    -1075, -1074, -1022, -1021, -1020, -970, -968, -967, -966, 0, 995, 996, 1021, 1022, 1023,
];

// The unbiased exponent of x (-1023 for zero and subnormal numbers).
fn exponent(x: f64) -> i32 {
    ((x.to_bits() >> 52) & 0x7ff) as i32 - 1023
}

fn same(x: f64, y: f64) -> bool {
    x.is_nan() && y.is_nan() || x.to_bits() == y.to_bits()
}

#[derive(Default)]
struct Report {
    cases: u64,
    mismatches: u64,
    examples: String,
}

impl Report {
    fn check(&mut self, name: &str, args: &[f64], expected: f64, actual: f64) {
        self.cases += 1;
        if !same(expected, actual) {
            self.mismatches += 1;
            if self.mismatches <= 10 {
                writeln!(
                    self.examples,
                    "{}{:?}: expected {:e} ({:#x}), got {:e} ({:#x})",
                    name,
                    args,
                    expected,
                    expected.to_bits(),
                    actual,
                    actual.to_bits()
                )
                .unwrap();
            }
        }
    }
}

type HwUnary = fn(super::F64X2) -> super::F64X2;
type HwBinary = fn(super::F64X2, super::F64X2) -> super::F64X2;
type HwTernary = fn(super::F64X2, super::F64X2, super::F64X2) -> super::F64X2;
type Unary = fn(generic::F64X2) -> generic::F64X2;
type Binary = fn(generic::F64X2, generic::F64X2) -> generic::F64X2;
type Ternary = fn(generic::F64X2, generic::F64X2, generic::F64X2) -> generic::F64X2;
type Unary1 = fn(f64) -> f64;

fn binary_ops() -> Vec<(&'static str, HwBinary, Binary)> {
    vec![
        ("add_ru", super::add_ru, generic::add_ru),
        ("sub_ru", super::sub_ru, generic::sub_ru),
        ("sub1_ru", sub1_ru_as_binary, sub1_ru_as_binary_generic),
        ("mul_ru/fma", super::mul_ru, generic::mul_ru_impl::<true>),
        (
            "mul_ru/dekker",
            super::mul_ru,
            generic::mul_ru_impl::<false>,
        ),
        ("div_ru/fma", super::div_ru, generic::div_ru_impl::<true>),
        (
            "div_ru/dekker",
            super::div_ru,
            generic::div_ru_impl::<false>,
        ),
    ]
}

fn sub1_ru_as_binary(x: super::F64X2, y: super::F64X2) -> super::F64X2 {
    let (x, y) = (super::extract(x), super::extract(y));
    super::constant(super::sub1_ru(x[0], y[0]), super::sub1_ru(x[1], y[1]))
}

fn sub1_ru_as_binary_generic(x: generic::F64X2, y: generic::F64X2) -> generic::F64X2 {
    [generic::sub1_ru(x[0], y[0]), generic::sub1_ru(x[1], y[1])]
}

fn ternary_ops() -> Vec<(&'static str, HwTernary, Ternary)> {
    let mul_add_ru: HwTernary = super::mul_add_ru;
    vec![
        (
            "mul_add_ru/fma",
            mul_add_ru,
            generic::mul_add_ru_impl::<true>,
        ),
        (
            "mul_add_ru/dekker",
            mul_add_ru,
            generic::mul_add_ru_impl::<false>,
        ),
    ]
}

fn unary_ops() -> Vec<(&'static str, HwUnary, Unary)> {
    vec![("sqrt_rd_ru", super::sqrt_rd_ru, sqrt_rd_ru_reference)]
}

// An independent reference for `sqrt_rd_ru`: on x86-64, the square root with the
// rounding mode switched; on wasm32, the generic backend, whose fast paths the
// `wasm32` one vectorizes.
#[cfg(target_arch = "x86_64")]
fn sqrt_rd_ru_reference(x: generic::F64X2) -> generic::F64X2 {
    [hw_sqrt1_rd(x[0]), hw_sqrt1_ru(x[1])]
}

#[cfg(target_arch = "wasm32")]
fn sqrt_rd_ru_reference(x: generic::F64X2) -> generic::F64X2 {
    generic::sqrt_rd_ru(x)
}

// `wasm32` takes its scalar square root from the generic backend, so there is
// nothing to compare it with.
#[cfg(target_arch = "wasm32")]
fn unary1_ops() -> Vec<(&'static str, Unary1, Unary1)> {
    vec![]
}

#[cfg(target_arch = "x86_64")]
fn unary1_ops() -> Vec<(&'static str, Unary1, Unary1)> {
    vec![
        ("sqrt1_ru/fma", hw_sqrt1_ru, generic::sqrt1_ru_impl::<true>),
        (
            "sqrt1_ru/dekker",
            hw_sqrt1_ru,
            generic::sqrt1_ru_impl::<false>,
        ),
        ("sqrt1_rd/fma", hw_sqrt1_rd, generic::sqrt1_rd_impl::<true>),
        (
            "sqrt1_rd/dekker",
            hw_sqrt1_rd,
            generic::sqrt1_rd_impl::<false>,
        ),
    ]
}

fn check_unary(r: &mut Report, name: &str, hw: HwUnary, f: Unary, a: [f64; 2]) {
    let expected = super::extract(hw(super::constant(a[0], a[1])));
    let actual = f(a);
    for i in 0..2 {
        // Both lanes of the argument are reported: the lanes are rounded in
        // opposite directions, so a mismatch depends on which one this is.
        r.check(name, &a, expected[i], actual[i]);
    }
}

fn check_binary(r: &mut Report, name: &str, hw: HwBinary, f: Binary, a: [f64; 2], b: [f64; 2]) {
    let expected = super::extract(hw(super::constant(a[0], a[1]), super::constant(b[0], b[1])));
    let actual = f(a, b);
    for i in 0..2 {
        r.check(name, &[a[i], b[i]], expected[i], actual[i]);
    }
}

fn check_ternary(
    r: &mut Report,
    name: &str,
    hw: HwTernary,
    f: Ternary,
    a: [f64; 2],
    b: [f64; 2],
    c: [f64; 2],
) {
    let expected = super::extract(hw(
        super::constant(a[0], a[1]),
        super::constant(b[0], b[1]),
        super::constant(c[0], c[1]),
    ));
    let actual = f(a, b, c);
    for i in 0..2 {
        r.check(name, &[a[i], b[i], c[i]], expected[i], actual[i]);
    }
}

fn random_cases() -> u64 {
    std::env::var("INARI_DIFF_N")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(if cfg!(debug_assertions) {
            20_000
        } else {
            1_000_000
        })
}

// A pair (x, y) for an operation `name`, drawn from one of several distributions.
fn random_pair(rng: &mut Rng, name: &str) -> (f64, f64) {
    let x = rng.any();
    let y = match rng.below(5) {
        0 => rng.any(),
        4 if name.starts_with("add") || name.starts_with("sub") => {
            // x near ±MAX and y a small multiple of half an ulp of MAX (2^970), so
            // that x + y is often a tie in the top binade (see `adversarial`).
            let max = rng.sign(f64::MAX);
            let x = rng.nudge(max);
            let k = rng.below(8) as f64 + 1.0;
            let y = rng.sign(k * 2f64.powi(970));
            return (x, y);
        }
        4 => rng.any(),
        1 => {
            // Make the result land near a boundary: for multiplication, choose
            // e_y = t - e_x; for division, e_y = e_x - t.
            let t = rng.exponent_near_boundary();
            let ex = exponent(x);
            if name.starts_with("div") {
                rng.with_exponent(ex - t)
            } else {
                rng.with_exponent(t - ex)
            }
        }
        2 => {
            if name.starts_with("div") {
                // x = q * y (rounded) gives exact and near-exact quotients.
                let y = rng.any();
                return (rng.nudge(x * y), y);
            } else if name.starts_with("mul") {
                // A product near or below 2^-968, where `mul_ru_tiny` and
                // `generic::mul1_ru_tiny` take over: e_x from -1023 (subnormal) to
                // 110, and e_y = t - e_x for t from -1080 to -960. Two nonzero
                // floats whose product is below 2^-968 are below 2^106, which both
                // rely on. Both scale x alone, so the factors are swapped half the
                // time.
                let ex = rng.below(1134) as i32 - 1023;
                let x = rng.with_exponent(ex);
                let t = rng.below(121) as i32 - 1080;
                // `with_exponent` stops at -1023, so y is drawn 2^200 higher and
                // scaled down. Where e_y < -1022, that rounds it to a multiple of
                // 2^-1074, and where e_y < -1075 (about 5% of the draws), to ±0.
                let y = rng.with_exponent(t - ex + 200) * 2f64.powi(-200);
                return if rng.below(2) == 0 { (x, y) } else { (y, x) };
            } else {
                // Cancellation: y ≈ -x (for add) or y ≈ x (for sub).
                let y = rng.nudge(x);
                if name.starts_with("add") {
                    -y
                } else {
                    y
                }
            }
        }
        _ => {
            // Operands a few binades apart.
            let ex = exponent(x);
            let e = ex - rng.below(120) as i32;
            rng.with_exponent(e)
        }
    };
    (x, y)
}

// An argument for the square root: anything, or an exact square and its
// neighbors, where the correction by the sign of the remainder is decided by a
// single ulp.
fn random_sqrt_arg(rng: &mut Rng) -> f64 {
    match rng.below(2) {
        0 => rng.any(),
        _ => {
            let s = rng.any().abs();
            rng.nudge(s * s)
        }
    }
}

fn random_triple(rng: &mut Rng) -> (f64, f64, f64) {
    if rng.below(8) == 0 {
        return tiny_triple(rng);
    }
    let a = rng.any();
    let b = match rng.below(2) {
        0 => rng.any(),
        _ => {
            let t = rng.exponent_near_boundary();
            rng.with_exponent(t - exponent(a))
        }
    };
    let p = a * b;
    let c = match rng.below(5) {
        0 => rng.any(),
        // Cancellation, including exact zeros and tiny results.
        1 => rng.nudge(-p),
        // c below the rounding error of a * b.
        2 => {
            let e = exponent(p) - rng.below(120) as i32;
            rng.with_exponent(e)
        }
        // c near the error term of a * b.
        3 => -(a.mul_add(b, -p)) * (rng.below(3) as f64),
        _ => {
            let e = rng.exponent_near_boundary();
            rng.with_exponent(e)
        }
    };
    (a, b, c)
}

// A triple for the underflow hypotheses of ErrFma (see `mul_add1_ru_fast`): a * b
// just above 2^-968, where TwoProduct is still exact, so that its error u2 is
// around 2^-1021 or smaller, and c ≈ -a * b (r1 tiny) or c ≈ -u2 (α1 tiny).
// β1 = u1 + α1 is a multiple of 2^-1020 unless u1 = ±2^-968, in which case
// α1 = ∓(2^-968 - 2^-1021) gives β1 = ±2^-1021.
fn tiny_triple(rng: &mut Rng) -> (f64, f64, f64) {
    // e_a <= 50 keeps b normal.
    let ea = rng.below(951) as i32 - 900;
    let a = rng.with_exponent(ea);
    let b = if rng.below(4) == 0 {
        2f64.powi(-968) / a
    } else {
        let eb = -968 + rng.below(8) as i32 - ea;
        rng.with_exponent(eb)
    };
    let p = a * b;
    let u2 = a.mul_add(b, -p);
    let c = match rng.below(3) {
        0 => -p,
        1 => rng.nudge(-p),
        _ => rng.nudge(-u2),
    };
    (a, b, c)
}

// 2^e, for e from -1074 to 1023.
fn pow2(e: i32) -> f64 {
    if e >= -1022 {
        f64::from_bits(((e + 1023) as u64) << 52)
    } else {
        f64::from_bits(1 << (e + 1074))
    }
}

// Hand-picked values: signed zeros, the smallest and largest subnormals, the
// fast-path thresholds, halfway cases (1 ± 2^-27, 1 + 2^-53), values whose
// splitting overflows (>= 2^996), and ±MAX, ±∞ and NaN, with their neighbors.
fn adversarial(with_neighbors: bool) -> Vec<f64> {
    let p = pow2;
    let mut v = vec![
        0.0,
        p(-1074),
        p(-1073),
        3.0 * p(-1074),
        p(-1022) - p(-1074),
        p(-1022),
        p(-1021),
        p(-1020),
        p(-970),
        p(-969),
        p(-968),
        p(-967),
        p(-966),
        p(-537),
        p(-511),
        p(-483),
        p(-54),
        p(-53),
        0.5,
        1.0,
        1.0 + p(-52),
        1.0 - p(-53),
        1.0 + p(-27),
        1.0 - p(-27),
        1.0 + p(-53),
        1.5,
        2.0,
        3.0,
        1.0 / 3.0,
        10.0,
        p(52),
        p(53),
        p(511),
        p(512),
        f64::MAX.sqrt(),
        p(995),
        p(996),
        // Half an ulp of MAX and three times it: -MAX + 3 * 2^970 is a tie that
        // rounds away from zero, after which TwoSum's s - y overflows.
        p(970),
        3.0 * p(970),
        p(1021),
        p(1022),
        p(1023),
        f64::MAX,
        f64::INFINITY,
        f64::NAN,
    ];
    if with_neighbors {
        let mut w = vec![];
        for &x in &v {
            w.push(x);
            if x.is_finite() && x != 0.0 {
                w.push(f64::from_bits(x.to_bits() + 1));
                w.push(f64::from_bits(x.to_bits() - 1));
            }
        }
        v = w;
    }
    let negated: Vec<f64> = v.iter().map(|x| -x).collect();
    v.extend(negated);
    v
}

// x * y = -(2^-1075 + 2^-1128), as 3y = 1/2 + 2^-54 (y is the float above
// RN(1/6)). Scaled by 2^128, it rounds up to rs = -2^-947, and rs / 2^128 =
// -2^-1075 is a tie, which rounds to q = -0, the result.
fn mul_ru_tie() -> (f64, f64) {
    (-3.0 * pow2(-1074), f64::from_bits(0x3fc5_5555_5555_5556))
}

// Single cases that a backend once got wrong, that a comment gives as the reason
// for a check, or that a test chose by hand for one step of an algorithm, as the
// operation (named as in `binary_ops` and the other lists, without the variant
// after a `/`) and its arguments. Each comment says why the case is here (what
// it broke or would break, or the step it exercises) and where it was found.
// Every mismatch that a random test or a fuzzer finds goes here, so that it
// stays tested when the random draw or `adversarial` changes. `differential`
// checks these cases against the generic backend on every backend that it tests.
// Except under AVX-512F, the backend under test mostly computes with the
// algorithm of the generic one, so a mistake they share goes unnoticed there;
// `mul_ru_tiny_generic` therefore also checks the cases of `mul_ru` against
// `generic::mul1_ru_slow`.
fn regressions() -> Vec<(&'static str, Vec<f64>)> {
    let p = pow2;
    let tie = mul_ru_tie();
    vec![
        // -MAX + 3 * 2^970 is a tie that rounds away from zero, to
        // s = -(MAX - 2^971), and TwoSum's s - y = -(MAX + 2^970) then overflows,
        // which makes its error NaN. Without their check |x|, |y| < 2^1023, the
        // fast paths of `add_ru` would return s, an ulp below the result. Given
        // in `generic::two_sum_err` since 559d2e5 and in `adversarial` since
        // df2e1f8; not known to have failed. With its negation, as the rounding
        // is directed, and as a difference, by `sub_ru` and `sub1_ru`. Except
        // under AVX-512F, the backend under test hands these cases to the generic
        // one, so there they check only that its own fast path, if it has one,
        // rejects them.
        ("add_ru", vec![-f64::MAX, 3.0 * p(970)]),
        ("add_ru", vec![f64::MAX, -3.0 * p(970)]),
        ("sub_ru", vec![-f64::MAX, -3.0 * p(970)]),
        ("sub1_ru", vec![-f64::MAX, -3.0 * p(970)]),
        // RN(a * b) overflows and c is the opposite infinity, so a * b + c = c,
        // while RN(a * b) + c is NaN. `generic::mul_add1_special` returns c for
        // that reason, as does the `special_r` of `mul_add_ru` in `sse42` and
        // `wasm32`, and so did that of `fma::mul_add_ru` from 469f00b until
        // a6650cb removed it, as the FMA alone gives c there. Not known to have
        // failed. With its negation.
        ("mul_add_ru", vec![f64::MAX, 2.0, f64::NEG_INFINITY]),
        ("mul_add_ru", vec![-f64::MAX, 2.0, f64::INFINITY]),
        // `mul_ru_tie`: rs / 2^128 is a tie, -2^-1075, and rounds to the result,
        // -0. Chosen by hand for `generic::mul1_ru_tiny` in 6fa4f83, which got
        // it right.
        ("mul_ru", vec![tie.0, tie.1]),
    ]
}

// The operation of `name`: the part before any `/`. The part after it names a
// variant of the generic backend.
fn operation(name: &str) -> &str {
    name.split('/').next().unwrap()
}

// The arguments of the cases of `regressions` for the operation of `name`, which
// takes `arity` arguments.
fn regression_cases(name: &str, arity: usize) -> Vec<Vec<f64>> {
    let mut cases = vec![];
    for (op, args) in regressions() {
        if op == operation(name) {
            assert_eq!(args.len(), arity, "{}{:?}", op, args);
            cases.push(args);
        }
    }
    cases
}

// The cases of `regression_cases`, each in both lanes, next to itself and next
// to 1s, an ordinary case: the arguments of lane 0 and of lane 1.
fn regression_lanes(name: &str, arity: usize) -> Vec<(Vec<f64>, Vec<f64>)> {
    let ones = vec![1.0; arity];
    let mut lanes = vec![];
    for args in regression_cases(name, arity) {
        lanes.push((args.clone(), args.clone()));
        lanes.push((args.clone(), ones.clone()));
        lanes.push((ones.clone(), args));
    }
    lanes
}

#[test]
fn differential() {
    let n = random_cases();
    let mut rng = Rng(0x1788_2015);
    let mut summary = String::new();
    let mut total_mismatches = 0;

    // A case of `regressions` whose operation is not compared here would be
    // skipped without notice.
    let names: Vec<&str> = binary_ops()
        .iter()
        .map(|op| op.0)
        .chain(ternary_ops().iter().map(|op| op.0))
        .chain(unary_ops().iter().map(|op| op.0))
        .chain(unary1_ops().iter().map(|op| op.0))
        .collect();
    for (op, args) in regressions() {
        let compared = names.iter().any(|&name| operation(name) == op);
        assert!(compared, "nothing compares {}{:?}", op, args);
    }

    for (name, hw, gen) in binary_ops() {
        let mut r = Report::default();
        let v = adversarial(true);
        for (i, &x) in v.iter().enumerate() {
            for (j, &y) in v.iter().enumerate() {
                // Pair each case with another one in the other lane.
                let (x1, y1) = (v[(i + 7) % v.len()], v[(j + 13) % v.len()]);
                check_binary(&mut r, name, hw, gen, [x, x1], [y, y1]);
            }
        }
        for (l0, l1) in regression_lanes(name, 2) {
            check_binary(&mut r, name, hw, gen, [l0[0], l1[0]], [l0[1], l1[1]]);
        }
        for _ in 0..n {
            let (x0, y0) = random_pair(&mut rng, name);
            let (x1, y1) = random_pair(&mut rng, name);
            check_binary(&mut r, name, hw, gen, [x0, x1], [y0, y1]);
        }
        writeln!(
            summary,
            "{:18} {:>10} cases, {} mismatches",
            name, r.cases, r.mismatches
        )
        .unwrap();
        summary += &r.examples;
        total_mismatches += r.mismatches;
    }

    for (name, hw, gen) in ternary_ops() {
        let mut r = Report::default();
        let v = adversarial(false);
        for (i, &a) in v.iter().enumerate() {
            for &b in &v {
                for (k, &c) in v.iter().enumerate() {
                    let (a1, b1, c1) = (v[(i + 5) % v.len()], 1.0, v[(k + 3) % v.len()]);
                    check_ternary(&mut r, name, hw, gen, [a, a1], [b, b1], [c, c1]);
                }
            }
        }
        for (l0, l1) in regression_lanes(name, 3) {
            let (a, b, c) = ([l0[0], l1[0]], [l0[1], l1[1]], [l0[2], l1[2]]);
            check_ternary(&mut r, name, hw, gen, a, b, c);
        }
        for _ in 0..n {
            let (a0, b0, c0) = random_triple(&mut rng);
            let (a1, b1, c1) = random_triple(&mut rng);
            check_ternary(&mut r, name, hw, gen, [a0, a1], [b0, b1], [c0, c1]);
        }
        writeln!(
            summary,
            "{:18} {:>10} cases, {} mismatches",
            name, r.cases, r.mismatches
        )
        .unwrap();
        summary += &r.examples;
        total_mismatches += r.mismatches;
    }

    for (name, hw, gen) in unary_ops() {
        let mut r = Report::default();
        let v = adversarial(true);
        // Every ordered pair, so that each value is seen in both lanes, and the
        // fallback taken by one lane alone is exercised.
        for &x in &v {
            for &y in &v {
                check_unary(&mut r, name, hw, gen, [x, y]);
            }
        }
        for (l0, l1) in regression_lanes(name, 1) {
            check_unary(&mut r, name, hw, gen, [l0[0], l1[0]]);
        }
        for _ in 0..n {
            let x0 = random_sqrt_arg(&mut rng);
            let x1 = random_sqrt_arg(&mut rng);
            check_unary(&mut r, name, hw, gen, [x0, x1]);
        }
        writeln!(
            summary,
            "{:18} {:>10} cases, {} mismatches",
            name, r.cases, r.mismatches
        )
        .unwrap();
        summary += &r.examples;
        total_mismatches += r.mismatches;
    }

    for (name, hw, gen) in unary1_ops() {
        let mut r = Report::default();
        for &x in &adversarial(true) {
            r.check(name, &[x], hw(x), gen(x));
        }
        for args in regression_cases(name, 1) {
            r.check(name, &args, hw(args[0]), gen(args[0]));
        }
        for _ in 0..n {
            let x = random_sqrt_arg(&mut rng);
            r.check(name, &[x], hw(x), gen(x));
        }
        writeln!(
            summary,
            "{:18} {:>10} cases, {} mismatches",
            name, r.cases, r.mismatches
        )
        .unwrap();
        summary += &r.examples;
        total_mismatches += r.mismatches;
    }

    println!("{}", summary);
    assert_eq!(total_mismatches, 0, "\n{}", summary);
}

// `generic::mul_ru_impl`, with and without an FMA, against
// `generic::mul1_ru_slow`, which `mul_ru` called for every lane that its fast
// path rejects until `mul1_ru_tiny` took over the products below 2^-968, and
// which `rocq/theories/MulRu.v` proves correct for all inputs. Except under
// AVX-512F, `differential` compares the generic backend with SIMD backends that
// round tiny products with the algorithm of `mul1_ru_tiny`, so a mistake in the
// algorithm they share could go unnoticed there.
#[test]
fn mul_ru_tiny_generic() {
    let n = random_cases();
    let mut rng = Rng(3);
    let mut summary = String::new();
    let mut total_mismatches = 0;

    // The result of `mul_ru_tie`, worked out by hand. The tie is also checked
    // against the oracle below, as one of `regressions`.
    let tie = mul_ru_tie();
    assert!(same(generic::mul1_ru_slow(tie.0, tie.1), -0.0));

    // Products near or below 2^-968, with their sign flips and swapped factors.
    let mut pairs = vec![
        // p = RN(x * y) is ±0, so the result follows from the sign of p:
        // 2^-1075 (a tie), just below it, and 2^-2148.
        (pow2(-1074), 0.5),
        (pow2(-1074), 0.5 - pow2(-54)),
        (pow2(-1074), pow2(-1074)),
        // p = ±2^-1074, and the result is 2^-1074 or -0.
        (pow2(-1074), 0.5 + pow2(-53)),
        (1.0 / 3.0, 3.0 * pow2(-1074)),
        (pow2(-537), pow2(-537) - pow2(-590)),
        // Subnormal results: exact, then inexact.
        (pow2(-537), pow2(-537)),
        (1.0 + pow2(-52), pow2(-1050)),
        (1.5, 3.0 * pow2(-1074)),
        (pow2(-1022) - pow2(-1074), 0.5),
        // Around 2^-968. x * 5 = 2^-968 * (1 - 3 * 2^-55) rounds to nearest to the
        // float below 2^-968, and up to 2^-968.
        ((((1u64 << 55) - 3) / 5) as f64 * pow2(-1023), 5.0),
        (pow2(-968) - pow2(-1021), 1.0 - pow2(-53)),
        (pow2(-968) - pow2(-1021), 1.0),
        (pow2(-968), 1.0 - pow2(-53)),
        (pow2(-968), 1.0),
        // The largest factor of a nonzero product below 2^-968, where
        // (x * 2^128) * y is close to 2^-840, and the next float, where the
        // product is 2^-968.
        (pow2(-1074), pow2(106) - pow2(53)),
        (pow2(-1074), pow2(106)),
        // An ordinary product, which the fast path takes, for the other lane.
        (1.0, 3.0),
    ];
    // And the cases of `regressions` for `mul_ru`, such as the tie.
    pairs.extend(regression_cases("mul_ru", 2).iter().map(|v| (v[0], v[1])));
    let mut cases = vec![];
    for (x, y) in pairs {
        for (x, y) in [(x, y), (y, x)] {
            cases.extend([(x, y), (-x, y), (x, -y), (-x, -y)]);
        }
    }

    let variants: [(&str, Binary); 2] = [
        ("mul_ru_tiny/fma", generic::mul_ru_impl::<true>),
        ("mul_ru_tiny/dekker", generic::mul_ru_impl::<false>),
    ];
    for (name, f) in variants {
        let mut r = Report::default();
        // The lanes with finite, nonzero factors and |RN(x * y)| < 2^-968: those
        // that `mul1_ru_tiny` rounds itself rather than with `mul1_ru_slow`.
        let mut tiny = 0;
        let mut check = |x: [f64; 2], y: [f64; 2]| {
            let actual = f(x, y);
            for i in 0..2 {
                let (x, y) = (x[i], y[i]);
                let finite = x.is_finite() && y.is_finite();
                if finite && x != 0.0 && y != 0.0 && exponent(x * y) < -968 {
                    tiny += 1;
                }
                r.check(name, &[x, y], generic::mul1_ru_slow(x, y), actual[i]);
            }
        };
        // Each case in both lanes, next to every other one.
        for &(x0, y0) in &cases {
            for &(x1, y1) in &cases {
                check([x0, x1], [y0, y1]);
            }
        }
        let v = adversarial(true);
        for (i, &x) in v.iter().enumerate() {
            for (j, &y) in v.iter().enumerate() {
                // Pair each case with another one in the other lane.
                let (x1, y1) = (v[(i + 7) % v.len()], v[(j + 13) % v.len()]);
                check([x, x1], [y, y1]);
            }
        }
        for _ in 0..n {
            let (x0, y0) = random_pair(&mut rng, "mul");
            let (x1, y1) = random_pair(&mut rng, "mul");
            check([x0, x1], [y0, y1]);
        }
        writeln!(
            summary,
            "{:18} {:>10} cases ({} tiny), {} mismatches",
            name, r.cases, tiny, r.mismatches
        )
        .unwrap();
        summary += &r.examples;
        total_mismatches += r.mismatches;
    }

    println!("{}", summary);
    assert_eq!(total_mismatches, 0, "\n{}", summary);
}

#[test]
fn round_ties_even() {
    let mut rng = Rng(1);
    let mut r = Report::default();
    let mut inputs = adversarial(true);
    inputs.extend([0.5, 1.5, 2.5, -2.5, 4503599627370495.5, -0.3]);
    for _ in 0..random_cases() {
        let e = rng.below(60) as i32 - 5;
        inputs.push(rng.with_exponent(e));
    }
    for &x in &inputs {
        let expected = super::extract0(super::round_ties_even(super::splat(x)));
        let actual = generic::round_ties_even([x, x])[0];
        r.check("round_ties_even", &[x], expected, actual);
    }
    assert_eq!(r.mismatches, 0, "\n{}", r.examples);
}

// The FMA emulation of the Dekker variant against `f64::mul_add`. `differential`
// cannot catch a double-rounded r1 in `mul_add_ru`: it is still one of the two
// floats around a * b + c, and the correction by the sign of the error then gives
// the right result anyway.
#[test]
fn mul_add_rn_emulated() {
    let mut rng = Rng(2);
    let mut r = Report::default();
    let p = |e: i32| 2f64.powi(e);
    // a * b = 1 - 2^-54 is halfway between 1 - 2^-53 and 1, and c breaks the tie,
    // which rounding t2 + u2 to nearest would lose.
    let mut inputs = vec![
        (1.0 + p(-27), 1.0 - p(-27), -p(-150)),
        (1.0 + p(-27), 1.0 - p(-27), p(-150)),
        (-(1.0 + p(-27)), 1.0 - p(-27), p(-150)),
    ];
    for _ in 0..random_cases() {
        inputs.push(random_triple(&mut rng));
    }
    for (a, b, c) in inputs {
        let u1 = a * b;
        let u2 = a.mul_add(b, -u1);
        // The hypotheses: TwoProduct is exact and nothing overflows.
        let valid = (-968..=1021).contains(&exponent(u1))
            && exponent(c) <= 1021
            && a.mul_add(b, c).is_finite();
        if valid {
            let actual = generic::mul_add1_rn_emulated(u1, u2, c);
            r.check("mul_add1_rn_emulated", &[a, b, c], a.mul_add(b, c), actual);
        }
    }
    println!(
        "mul_add1_rn_emulated: {} cases, {} mismatches",
        r.cases, r.mismatches
    );
    assert_eq!(r.mismatches, 0, "\n{}", r.examples);
}
