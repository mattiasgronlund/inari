// Tests of the roots of the dyadic kernel, on every platform, against an exact oracle of their
// own. At an argument where the root is r >= 0, the results lo toward -∞, hi toward +∞ and n to
// nearest are right if lo <= r <= hi, with lo = hi exactly when r is an `f64` and hi the `f64`
// after lo otherwise, and if n is lo or hi as r is below or above their midpoint, the one with
// an even significand when r is the midpoint (`check_root`). The oracle decides each of these
// comparisons in integers, with arithmetic of its own (`Nat`), not with `crate::limbs`, whose
// results it checks: r^3 = |x| for cbrt, whose value at -x is -cbrt x, and r^2 = x^2 + y^2 for
// hypot, so lo, hi and the midpoint compare with r as their cubes or squares compare with those,
// each an integer times a power of two. +∞ stands for 2^1024 there, whose significand is even,
// so that a root from 2^1024 - 2^970, the midpoint of MAX and 2^1024, on has to round to +∞ to
// nearest, as `near_round` in `rocq/theories/NearF64.v` says.
//
// The generators: random arguments, log-uniform and uniform in (-1, 1); every binade of cbrt;
// exact cubes and their neighbours; scaled Pythagorean triples, whose hypotenuses are exact or
// midpoints, and their neighbours; both sides of the cut of hypot at a gap of 27; results at the
// overflow threshold; and subnormal arguments. `src/cr.rs` compares the functions with MPFR.

use super::*;
use crate::dyadic::tests::Rng;
use std::cmp::Ordering;

// A natural number, as digits in base 2^32 from the least significant, with no zero digit at
// the top, so that 0 has none.
#[derive(Clone, Debug)]
struct Nat(Vec<u32>);

impl Nat {
    fn new(n: u64) -> Nat {
        Nat(vec![n as u32, (n >> 32) as u32]).trimmed()
    }

    fn trimmed(mut self) -> Nat {
        while self.0.last() == Some(&0) {
            self.0.pop();
        }
        self
    }

    fn plus(&self, other: &Nat) -> Nat {
        let digit = |a: &Nat, i: usize| u64::from(a.0.get(i).copied().unwrap_or(0));
        let n = self.0.len().max(other.0.len());
        let (mut r, mut carry) = (Vec::with_capacity(n + 1), 0);
        for i in 0..n {
            let t = digit(self, i) + digit(other, i) + carry;
            r.push(t as u32);
            carry = t >> 32;
        }
        r.push(carry as u32);
        Nat(r).trimmed()
    }

    // Schoolbook multiplication. Each step is at most (2^32 - 1)^2 + 2 (2^32 - 1) = 2^64 - 1.
    fn times(&self, other: &Nat) -> Nat {
        let mut r = vec![0; self.0.len() + other.0.len()];
        for (i, &a) in self.0.iter().enumerate() {
            let mut carry = 0;
            for (j, &b) in other.0.iter().enumerate() {
                let t = u64::from(a) * u64::from(b) + u64::from(r[i + j]) + carry;
                r[i + j] = t as u32;
                carry = t >> 32;
            }
            r[i + other.0.len()] = carry as u32;
        }
        Nat(r).trimmed()
    }

    // self 2^k.
    fn shifted(&self, k: u64) -> Nat {
        let mut r = vec![0; (k / 32) as usize];
        let mut carry = 0;
        for &d in &self.0 {
            let t = u64::from(d) << (k % 32);
            r.push(t as u32 | carry);
            carry = (t >> 32) as u32;
        }
        r.push(carry);
        Nat(r).trimmed()
    }

    fn compare(&self, other: &Nat) -> Ordering {
        let (a, b) = (self.0.iter().rev(), other.0.iter().rev());
        self.0.len().cmp(&other.0.len()).then_with(|| a.cmp(b))
    }
}

// The number m 2^e.
#[derive(Clone, Debug)]
struct Num {
    m: Nat,
    e: i64,
}

impl Num {
    // The value of an `f64` v >= +0 from its bits, and 2^1024 for v = +∞.
    fn of(v: f64) -> Num {
        assert!(v.is_sign_positive() && !v.is_nan(), "{:e}", v);
        if v == f64::INFINITY {
            return Num {
                m: Nat::new(1),
                e: 1024,
            };
        }
        let (field, fraction) = ((v.to_bits() >> 52) as i64, v.to_bits() & ((1 << 52) - 1));
        if field == 0 {
            Num {
                m: Nat::new(fraction),
                e: -1074,
            }
        } else {
            Num {
                m: Nat::new(fraction | (1 << 52)),
                e: field - 1075,
            }
        }
    }

    // The two numbers as integers times 2^e, at the lower of their exponents e.
    fn aligned(&self, other: &Num) -> (Nat, Nat, i64) {
        let e = self.e.min(other.e);
        let a = self.m.shifted((self.e - e) as u64);
        (a, other.m.shifted((other.e - e) as u64), e)
    }

    fn plus(&self, other: &Num) -> Num {
        let (a, b, e) = self.aligned(other);
        Num { m: a.plus(&b), e }
    }

    fn half(self) -> Num {
        Num {
            m: self.m,
            e: self.e - 1,
        }
    }

    fn pow(&self, k: u32) -> Num {
        let mut m = Nat::new(1);
        for _ in 0..k {
            m = m.times(&self.m);
        }
        Num {
            m,
            e: self.e * i64::from(k),
        }
    }

    fn compare(&self, other: &Num) -> Ordering {
        let (a, b, _) = self.aligned(other);
        a.compare(&b)
    }
}

// Checks `lo`, `hi` and `near` as a root r >= 0 rounded toward -∞, toward +∞ and to nearest,
// ties to even, where r^k = `power`, as the header says. Returns whether r is the midpoint of
// lo and hi.
fn check_root(what: &str, k: u32, power: &Num, lo: f64, hi: f64, near: f64) -> bool {
    for v in [lo, hi, near] {
        assert!(v.is_sign_positive() && !v.is_nan(), "{}: {:e}", what, v);
    }
    assert!(lo.is_finite(), "{}: {:e} toward -∞", what, lo);
    let below = Num::of(lo).pow(k).compare(power);
    if lo.to_bits() == hi.to_bits() {
        assert_eq!(
            below,
            Ordering::Equal,
            "{}: {:e} in both directions, but the root is not an f64",
            what,
            lo
        );
        assert_eq!(
            near.to_bits(),
            lo.to_bits(),
            "{}: {:e} to nearest, {:e} in both directions",
            what,
            near,
            lo
        );
        return false;
    }
    assert_eq!(
        below,
        Ordering::Less,
        "{}: {:e} toward -∞ and {:e} toward +∞",
        what,
        lo,
        hi
    );
    // Positive `f64`s that are adjacent, +∞ after MAX included, have adjacent bits.
    assert_eq!(
        hi.to_bits(),
        lo.to_bits() + 1,
        "{}: {:e} and {:e} are not adjacent",
        what,
        lo,
        hi
    );
    // hypot reaches √2 MAX > 2^1024, so +∞ above MAX is checked only by lo < r.
    if hi.is_finite() {
        assert_eq!(
            Num::of(hi).pow(k).compare(power),
            Ordering::Greater,
            "{}: {:e} toward +∞ is not above the root",
            what,
            hi
        );
    }
    let mid = Num::of(lo).plus(&Num::of(hi)).half();
    let (want, tie) = match mid.pow(k).compare(power) {
        Ordering::Less => (hi, false),
        Ordering::Greater => (lo, false),
        // The bits of a positive `f64` end in its significand's, and +∞ has an even one.
        Ordering::Equal => (if lo.to_bits() % 2 == 0 { lo } else { hi }, true),
    };
    assert_eq!(
        near.to_bits(),
        want.to_bits(),
        "{}: {:e} to nearest instead of {:e}",
        what,
        near,
        want
    );
    tie
}

// Checks cbrt at `x` in both directions and to nearest: ±∞ and NaN at ±∞ and NaN, the sign of
// `x` otherwise, and the roundings of cbrt |x| as the header says, where -cbrt x = cbrt(-x)
// swaps the directions at x < 0. cbrt has no midpoints (`src/dyadic/root.rs`).
fn check_cbrt(x: f64) {
    let (lo, hi, near) = (cbrt(x, false), cbrt(x, true), cbrt_near(x));
    let what = format!("cbrt({:e})", x);
    if !x.is_finite() {
        for v in [lo, hi, near] {
            let ok = if x.is_nan() { v.is_nan() } else { v == x };
            assert!(ok, "{}: {:e}", what, v);
        }
        return;
    }
    for v in [lo, hi, near] {
        assert_eq!(
            v.is_sign_negative(),
            x.is_sign_negative(),
            "{}: {:e}",
            what,
            v
        );
    }
    let tie = if x.is_sign_negative() {
        check_root(&what, 3, &Num::of(-x), -hi, -lo, -near)
    } else {
        check_root(&what, 3, &Num::of(x), lo, hi, near)
    };
    assert!(!tie, "{}: a midpoint", what);
}

// Checks hypot at (x, y) in both directions and to nearest: +∞ if `x` or `y` is infinite, NaN
// otherwise if one is NaN, and the roundings of √(x^2 + y^2) as the header says. Returns
// whether the root is a midpoint.
fn check_hypot(x: f64, y: f64) -> bool {
    let (lo, hi, near) = (hypot(x, y, false), hypot(x, y, true), hypot_near(x, y));
    let what = format!("hypot({:e}, {:e})", x, y);
    if !x.is_finite() || !y.is_finite() {
        let inf = x.is_infinite() || y.is_infinite();
        for v in [lo, hi, near] {
            let ok = if inf { v == f64::INFINITY } else { v.is_nan() };
            assert!(ok, "{}: {:e}", what, v);
        }
        return false;
    }
    let power = Num::of(x.abs()).pow(2).plus(&Num::of(y.abs()).pow(2));
    check_root(&what, 2, &power, lo, hi, near)
}

// The `f64` after `x` toward +∞, for `x` below +∞. `f64::next_up` needs a Rust after the MSRV.
fn next_up(x: f64) -> f64 {
    if x == 0.0 {
        f64::from_bits(1)
    } else if x > 0.0 {
        f64::from_bits(x.to_bits() + 1)
    } else {
        f64::from_bits(x.to_bits() - 1)
    }
}

// The `f64` before `x` toward -∞, for `x` above -∞.
fn next_down(x: f64) -> f64 {
    -next_up(-x)
}

// 2^n, for n in [-1074, 1023].
fn pow2(n: i64) -> f64 {
    if n < -1022 {
        f64::from_bits(1 << (n + 1074))
    } else {
        f64::from_bits(u64::try_from(n + 1023).unwrap() << 52)
    }
}

// `x` and the `k` `f64`s on each side of it, for a finite `x`.
fn around(x: f64, k: usize) -> Vec<f64> {
    let (mut a, mut b) = (x, x);
    let mut v = vec![x];
    for _ in 0..k {
        a = next_down(a);
        b = next_up(b);
        v.push(a);
        v.push(b);
    }
    v
}

// A random `f64` log-uniform over (0, MAX]: its bits are uniform.
fn log_uniform(rng: &mut Rng) -> f64 {
    f64::from_bits(rng.below(0x7fef_ffff_ffff_ffff) + 1)
}

// A random `f64` uniform over (-1, 1), a multiple of 2^-53.
fn uniform(rng: &mut Rng) -> f64 {
    (rng.below((1 << 54) - 1) as i64 - ((1 << 53) - 1)) as f64 / 9_007_199_254_740_992.0
}

// -1 or 1 at random.
fn sign(rng: &mut Rng) -> f64 {
    if rng.below(2) == 0 {
        -1.0
    } else {
        1.0
    }
}

// Arguments on which mismatches were found, as `("cbrt", x, "")` or `("hypot", x, y)`, each
// with what it broke and where it was found.
fn regressions() -> Vec<(&'static str, &'static str, &'static str)> {
    vec![]
}

#[test]
fn regressions_hold() {
    for (name, x, y) in regressions() {
        let x: f64 = x.parse().unwrap();
        if name == "cbrt" {
            check_cbrt(x);
        } else {
            check_hypot(x, y.parse().unwrap());
        }
    }
}

// The arithmetic of the oracle against `u128`, and the values it gives to `f64`s.
#[test]
fn oracle() {
    let value = |n: &Nat| {
        assert!(n.0.len() <= 4);
        n.0.iter().rev().fold(0, |a, &d| (a << 32) | u128::from(d))
    };
    let mut rng = Rng(83);
    for _ in 0..10_000 {
        let (a, b) = (rng.next() >> rng.below(64), rng.next() >> rng.below(64));
        let (na, nb) = (Nat::new(a), Nat::new(b));
        assert_eq!(value(&na.plus(&nb)), u128::from(a) + u128::from(b));
        assert_eq!(value(&na.times(&nb)), u128::from(a) * u128::from(b));
        let k = rng.below(65);
        assert_eq!(value(&na.shifted(k)), u128::from(a) << k);
        assert_eq!(na.compare(&nb), a.cmp(&b));
    }
    let num = |m: u64, e: i64| Num { m: Nat::new(m), e };
    for (v, want) in [
        (0.0, num(0, 0)),
        (f64::from_bits(1), num(1, -1074)),
        (f64::MIN_POSITIVE, num(1, -1022)),
        (0.75, num(3, -2)),
        (f64::MAX, num((1 << 53) - 1, 971)),
        (f64::INFINITY, num(1, 1024)),
    ] {
        assert_eq!(Num::of(v).compare(&want), Ordering::Equal, "{:e}", v);
        let below = if v == 0.0 {
            Ordering::Less
        } else {
            Ordering::Greater
        };
        assert_eq!(Num::of(v).compare(&num(1, -1075)), below, "{:e}", v);
    }
    // (1 + 2) / 2 = 1.5, whose cube is 27 / 8.
    let mid = num(1, 0).plus(&num(1, 1)).half();
    assert_eq!(mid.pow(3).compare(&num(27, -3)), Ordering::Equal);
    assert_eq!(mid.pow(3).compare(&num(13, -2)), Ordering::Greater);
}

#[test]
fn smoke() {
    for (x, r) in [(27.0, 3.0), (-8.0, -2.0), (1.0, 1.0), (0.125, 0.5)] {
        assert_eq!(cbrt(x, false), r);
        assert_eq!(cbrt(x, true), r);
        assert_eq!(cbrt_near(x), r);
    }
    assert_eq!(cbrt(2.0, false).to_bits() + 1, cbrt(2.0, true).to_bits());
    // A midpoint: 2^53 + 2^27 + 1, whose tie goes to the even 2^53 + 2^27.
    let (x, y) = (134_217_729.0, 9_007_199_388_958_720.0);
    assert_eq!(hypot(x, y, false), 9_007_199_388_958_720.0);
    assert_eq!(hypot(x, y, true), 9_007_199_388_958_722.0);
    assert_eq!(hypot_near(x, y), 9_007_199_388_958_720.0);
    assert_eq!(hypot(3.0, 4.0, false), 5.0);
    assert_eq!(hypot(3.0, 4.0, true), 5.0);
    let tiny = f64::from_bits(1);
    assert_eq!(hypot(tiny, tiny, false), tiny);
    assert_eq!(hypot(tiny, tiny, true), f64::from_bits(2));
    assert_eq!(hypot_near(tiny, tiny), tiny);
    assert_eq!(hypot(f64::MAX, f64::MAX, false), f64::MAX);
    assert_eq!(hypot(f64::MAX, f64::MAX, true), f64::INFINITY);
    assert_eq!(hypot_near(f64::MAX, f64::MAX), f64::INFINITY);
}

// The zeros, the infinities, NaN and the ends of the finite range, and every pair of them.
#[test]
fn special_values() {
    let special = [
        0.0,
        f64::from_bits(1),
        f64::from_bits((1 << 52) - 1),
        f64::MIN_POSITIVE,
        1.0,
        f64::MAX,
        f64::INFINITY,
        f64::NAN,
    ];
    for &x in &special {
        check_cbrt(x);
        check_cbrt(-x);
        for &y in &special {
            for (x, y) in [(x, y), (-x, y), (x, -y), (-x, -y)] {
                check_hypot(x, y);
            }
        }
    }
    assert_eq!(hypot(-0.0, -0.0, false).to_bits(), 0);
    assert_eq!(hypot_near(-3.0, -0.0), 3.0);
    assert_eq!(hypot(f64::NAN, -f64::INFINITY, false), f64::INFINITY);
}

// Random arguments: log-uniform over (0, MAX] with a random sign, and uniform in (-1, 1).
#[test]
fn random() {
    let mut rng = Rng(83);
    for _ in 0..10_000 {
        let x = log_uniform(&mut rng) * sign(&mut rng);
        check_cbrt(x);
        check_cbrt(uniform(&mut rng));
        let (x, y) = (log_uniform(&mut rng), log_uniform(&mut rng));
        check_hypot(x * sign(&mut rng), y * sign(&mut rng));
        check_hypot(uniform(&mut rng), uniform(&mut rng));
    }
}

// Random pairs with a gap of g in [0, 60] binades: x log-uniform and y with the exponent field
// of x minus g and random bits below it, subnormal if that field is 0.
#[test]
fn random_gaps() {
    let mut rng = Rng(8301);
    for _ in 0..20_000 {
        let x = log_uniform(&mut rng);
        let field = (x.to_bits() >> 52).saturating_sub(rng.below(61));
        let y = f64::from_bits((field << 52) | rng.below(1 << 52));
        let (x, y) = (x * sign(&mut rng), y * sign(&mut rng));
        check_hypot(x, y);
        check_hypot(y, x);
    }
}

// Every binade of cbrt, which takes the exponent modulo 3 apart: at each exponent field, with
// the least and the greatest significand and random ones, at both signs.
#[test]
fn cbrt_every_binade() {
    let mut rng = Rng(8302);
    for field in 0..2047 {
        for fraction in [
            0,
            1,
            (1 << 52) - 1,
            rng.below(1 << 52),
            rng.below(1 << 52),
            rng.below(1 << 52),
        ] {
            let x = f64::from_bits((field << 52) | fraction);
            check_cbrt(x);
            check_cbrt(-x);
        }
    }
}

// The exact cubes x = y^3 of y = r 2^a with r odd and r^3 < 2^53, and x = r^3 2^(3 a) a finite
// `f64`, so that 3 a >= -1074, and the 2 `f64`s on each side of them.
#[test]
fn cbrt_cubes() {
    let mut rng = Rng(8303);
    for _ in 0..5_000 {
        // 208063^3 < 2^53 <= 208064^3.
        let r = 2 * rng.below(104_032) + 1;
        let cube = r * r * r;
        let bits = i64::from(64 - cube.leading_zeros());
        // The top bit of x is 2^(bits - 1 + 3 a), at most 2^1023.
        let a = -358 + rng.below(u64::try_from((1024 - bits) / 3 + 359).unwrap()) as i64;
        let (x, y) = (cube as f64 * pow2(3 * a), r as f64 * pow2(a));
        for s in [-1.0, 1.0] {
            let x = s * x;
            assert_eq!(cbrt(x, false), s * y, "cbrt({:e})", x);
            assert_eq!(cbrt(x, true), s * y, "cbrt({:e})", x);
            for x in around(x, 2) {
                check_cbrt(x);
            }
        }
    }
}

// Whether the integer `v` < 2^54 is an `f64`.
fn is_f64(v: u64) -> bool {
    v < 1 << 53 || v % 2 == 0
}

// Scaled Pythagorean triples: legs t (m^2 - n^2) and 2 t m n and hypotenuse c = t (m^2 + n^2)
// for m > n > 0 and t = 1 or 3, the legs `f64`s and c < 2^54, scaled by 2^k with k in
// [-1074, 970] (and so often subnormal legs) and the `f64` on each side of each leg. c 2^k is
// the exact result if c is an `f64`, and otherwise c is odd in [2^53, 2^54), so that m and n
// have opposite parities, and c 2^k is the midpoint of (c - 1) 2^k toward -∞ and (c + 1) 2^k
// toward +∞, with an even significand (c ± 1) / 2 to nearest: (c - 1) / 2 at t = 1, as
// m^2 + n^2 is then 1 modulo 4, and (c + 1) / 2 at t = 3. The triples are drawn from four
// shapes: m in [2^26, 2^27) and n below it, mostly midpoints at gaps of a few binades; m = n + d
// with d odd below 2^20 and n in [2^26, 2^26.5), midpoints whose short leg (2 n + d) d gives
// gaps up to 26, as in `smoke`; m below 2^25 + 2, under a random power of two, exact results;
// and t = 3 with m in [3 2^24, 5 2^24), midpoints whose ties go up.
#[test]
fn hypot_triples() {
    let mut rng = Rng(8304);
    let (mut exact, mut midpoints, mut ups) = (0, 0, 0);
    while exact + midpoints < 6_000 {
        let (m, n, t) = match rng.below(4) {
            0 => {
                let m = (1 << 26) + rng.below(1 << 26);
                (m, 1 + rng.below(m - 1), 1)
            }
            1 => {
                let (n, bits) = ((1 << 26) + rng.below(27_797_401), rng.below(20));
                (n + 2 * rng.below(1 << bits) + 1, n, 1)
            }
            2 => {
                let bits = rng.below(26);
                let m = 2 + rng.below(1 << bits);
                (m, 1 + rng.below(m - 1), 1)
            }
            _ => {
                let m = (3 << 24) + rng.below(1 << 25);
                (m, 1 + rng.below(m - 1), 3)
            }
        };
        let (a, b, c) = (t * (m * m - n * n), 2 * t * m * n, t * (m * m + n * n));
        if !(c < 1 << 54 && is_f64(a) && is_f64(b)) {
            continue;
        }
        let k = match rng.below(4) {
            0 => -1074 + rng.below(64) as i64,
            1 => 970 - rng.below(64) as i64,
            _ => -1074 + rng.below(2045) as i64,
        };
        let (mut x, mut y) = (a as f64 * pow2(k), b as f64 * pow2(k));
        if rng.below(2) == 0 {
            std::mem::swap(&mut x, &mut y);
        }
        let (x, y) = (x * sign(&mut rng), y * sign(&mut rng));
        let what = format!("hypot({:e}, {:e})", x, y);
        let tie = check_hypot(x, y);
        let (lo, hi, near) = (hypot(x, y, false), hypot(x, y, true), hypot_near(x, y));
        if is_f64(c) {
            exact += 1;
            let r = c as f64 * pow2(k);
            assert!(!tie && lo == r && hi == r, "{}", what);
        } else {
            midpoints += 1;
            let (down, up) = ((c - 1) as f64 * pow2(k), (c + 1) as f64 * pow2(k));
            let even = if (c - 1) % 4 == 0 {
                down
            } else {
                ups += 1;
                up
            };
            assert!(tie && lo == down && hi == up && near == even, "{}", what);
        }
        for x in around(x, 1) {
            for y in around(y, 1) {
                check_hypot(x, y);
            }
        }
    }
    assert!(
        exact > 1_000 && midpoints > 2_000 && ups > 100,
        "{} {} {}",
        exact,
        midpoints,
        ups
    );
}

// The cut of hypot (`hypot_odd`): pairs of |x| >= |y| whose gap, the binade of x minus that of
// y, is g = 26, 27 and 28, and the `f64` on each side of each, with random signs. y = x 2^-g;
// random significands; y as near the next binade as it gets, after a power of two x, where
// hypot(x, y) - x is nearest to half an ulp of x; and subnormal y.
#[test]
fn hypot_cut() {
    let mut rng = Rng(8305);
    for g in 26..=28 {
        for _ in 0..1_000 {
            let field = g + 1 + rng.below(2046 - g);
            let fractions = [0, (1 << 52) - 1, rng.below(1 << 52)];
            let fx = fractions[rng.below(3) as usize];
            let fy = [fx, fractions[rng.below(3) as usize]][rng.below(2) as usize];
            let x = f64::from_bits((field << 52) | fx);
            let y = f64::from_bits(((field - g) << 52) | fy);
            let e = field as i64 - 1023;
            let tiny = f64::from_bits(1 + rng.below((1 << 52) - 1));
            let pairs = [
                (x, x * pow2(-(g as i64))),
                (x, y),
                (pow2(e), next_down(pow2(e + 1 - g as i64))),
                (tiny * pow2(g as i64), tiny),
            ];
            for (x, y) in pairs {
                for x in around(x * sign(&mut rng), 1) {
                    for y in around(y * sign(&mut rng), 1) {
                        check_hypot(x, y);
                        check_hypot(y, x);
                    }
                }
            }
        }
    }
}

// Results at the overflow threshold: hypot(t, t) for t near MAX / √2, and hypot(x, y) for x at
// MAX and the two `f64`s below it and y near 2^997.5, 2^997 and 2^998, whose results cross
// 2^1024 - 2^970, where nearest turns from MAX to +∞, and MAX, where the directions turn.
#[test]
fn hypot_overflow() {
    for x in around(f64::MAX / std::f64::consts::SQRT_2, 3) {
        for y in around(f64::MAX / std::f64::consts::SQRT_2, 3) {
            check_hypot(x, y);
        }
    }
    let mut ys = around(std::f64::consts::SQRT_2 * pow2(997), 4);
    let nears: Vec<f64> = ys.iter().map(|&y| hypot_near(f64::MAX, y)).collect();
    assert!(nears.contains(&f64::MAX) && nears.contains(&f64::INFINITY));
    ys.extend(around(pow2(997), 2));
    ys.extend(around(pow2(998), 2));
    ys.extend([1.0, f64::MAX / 2.0, next_down(f64::MAX), f64::MAX]);
    for x in [
        f64::MAX,
        next_down(f64::MAX),
        next_down(next_down(f64::MAX)),
    ] {
        for &y in &ys {
            for (x, y) in [(x, y), (y, x), (-x, y), (x, -y)] {
                check_hypot(x, y);
            }
        }
    }
}

// Subnormal arguments: all pairs of i 2^-1074 and j 2^-1074 for i, j <= 40, random pairs below
// 2^-1020, and the cube roots of i 2^-1074 for i <= 1000 and of random subnormals.
#[test]
fn subnormals() {
    for i in 0..=40 {
        for j in 0..=40 {
            check_hypot(f64::from_bits(i), f64::from_bits(j));
        }
    }
    for i in 0..=1_000 {
        check_cbrt(f64::from_bits(i));
        check_cbrt(-f64::from_bits(i));
    }
    let mut rng = Rng(8306);
    for _ in 0..5_000 {
        let x = f64::from_bits(rng.below(1 << 54)) * sign(&mut rng);
        let y = f64::from_bits(rng.below(1 << 54)) * sign(&mut rng);
        check_hypot(x, y);
        check_cbrt(f64::from_bits(rng.below(1 << 52)) * sign(&mut rng));
    }
}
