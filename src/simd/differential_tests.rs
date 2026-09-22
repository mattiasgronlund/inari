// Compares the rounding functions of the generic backend bit for bit with the
// hardware backend (`avx_fma` or `avx512f`), which switches the rounding mode.
// Both the FMA and the Dekker (no FMA) variants of the generic backend are tested.
// NaNs compare equal regardless of their sign and payload, which inari does not
// depend on (x86 returns a negative default NaN, the generic backend does not).
//
// The number of random cases per generator can be set with `INARI_DIFF_N`.
// Run with `--nocapture` to see the number of cases and mismatches.

use super::generic;
use std::fmt::Write;

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

// Exponents around the thresholds of the fast paths and of the format.
const BOUNDARY_EXPONENTS: [i32; 14] = [
    -1074, -1022, -1021, -1020, -970, -968, -967, -966, 0, 995, 996, 1021, 1022, 1023,
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

type HwBinary = fn(super::F64X2, super::F64X2) -> super::F64X2;
type HwTernary = fn(super::F64X2, super::F64X2, super::F64X2) -> super::F64X2;
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

fn unary_ops() -> Vec<(&'static str, Unary1, Unary1)> {
    vec![
        (
            "sqrt1_ru/fma",
            super::sqrt1_ru,
            generic::sqrt1_ru_impl::<true>,
        ),
        (
            "sqrt1_ru/dekker",
            super::sqrt1_ru,
            generic::sqrt1_ru_impl::<false>,
        ),
        (
            "sqrt1_rd/fma",
            super::sqrt1_rd,
            generic::sqrt1_rd_impl::<true>,
        ),
        (
            "sqrt1_rd/dekker",
            super::sqrt1_rd,
            generic::sqrt1_rd_impl::<false>,
        ),
    ]
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
                rng.any()
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

// Hand-picked values: signed zeros, the smallest and largest subnormals, the
// fast-path thresholds, halfway cases (1 ± 2^-27, 1 + 2^-53), values whose
// splitting overflows (>= 2^996), and ±MAX, ±∞ and NaN, with their neighbors.
fn adversarial(with_neighbors: bool) -> Vec<f64> {
    let p = |e: i32| {
        if e >= -1022 {
            f64::from_bits(((e + 1023) as u64) << 52)
        } else {
            f64::from_bits(1 << (e + 1074))
        }
    };
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

#[test]
fn differential() {
    let n = random_cases();
    let mut rng = Rng(0x1788_2015);
    let mut summary = String::new();
    let mut total_mismatches = 0;

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
        for &x in &adversarial(true) {
            r.check(name, &[x], hw(x), gen(x));
        }
        for _ in 0..n {
            let x = match rng.below(2) {
                0 => rng.any(),
                _ => {
                    // Exact squares and their neighbors.
                    let s = rng.any().abs();
                    rng.nudge(s * s)
                }
            };
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
