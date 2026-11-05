// The rational numbers that the grammar of `src/parse.rs` makes of the bounds of an interval
// literal, and their comparison by value.
//
// The exponents of a literal can be as large as `i32::MAX` in magnitude, so a comparison
// cannot multiply out the powers of 5 of each side: `5^600000000` has 1.4 * 10^9 bits.
// `cmp_abs` first decides from the numbers of bits and the exponents alone. Only when the two
// magnitudes are within a factor of 2^6 of each other does it need the power of 5 of the
// difference of the exponents, which it computes exactly where the two can be equal, and bounds
// with more and more bits of otherwise.

use crate::nat::Nat;
use std::cmp::Ordering;

/// `(-1)^neg * num * 2^e2 * 5^e5 / den`, with `den > 0`.
#[derive(Clone, Debug)]
pub(super) struct Rat {
    // `rocq/theories/Model.v` transcribes this struct as the record `Rat`, with each `Nat` as
    // the integer that it holds, for the proofs of the conversions of `src/parse.rs`, so it has
    // to be updated along with them.
    pub(super) neg: bool,
    pub(super) num: Nat,
    pub(super) den: Nat,
    pub(super) e2: i32,
    pub(super) e5: i32,
}

impl Rat {
    /// `self + y` for a `y` with the same `den`, `e2` and `e5` as `self`.
    pub(super) fn add_same_scale(&self, y: &Rat) -> Rat {
        debug_assert!(self.den == y.den && self.e2 == y.e2 && self.e5 == y.e5);
        let (neg, num) = if self.neg == y.neg {
            (self.neg, &self.num + &y.num)
        } else if self.num >= y.num {
            (self.neg, &self.num - &y.num)
        } else {
            (y.neg, &y.num - &self.num)
        };
        Rat {
            neg,
            num,
            den: self.den.clone(),
            e2: self.e2,
            e5: self.e5,
        }
    }

    /// -1, 0 or 1 as `self` is negative, zero or positive.
    fn sign(&self) -> i32 {
        if self.num.is_zero() {
            0
        } else if self.neg {
            -1
        } else {
            1
        }
    }
}

impl std::ops::Neg for Rat {
    type Output = Self;

    fn neg(self) -> Self {
        // `rocq/theories/Model.v` transcribes this function in `number_neg`, so it has to be
        // updated along with it.
        Rat {
            neg: !self.neg,
            ..self
        }
    }
}

// `floor(log2(5) * 2^64)`, which `log2_5_constants` below checks with MPFR. log2(5) is
// irrational, so `LOG2_5_LO < log2(5) * 2^64 < LOG2_5_HI`.
const LOG2_5_LO: u128 = 0x2_5269_e12f_346e_2bf9;
const LOG2_5_HI: u128 = LOG2_5_LO + 1;

// Integers `lo` and `hi` with `lo <= m * log2(5) <= hi` and `hi - lo <= 2`.
fn log2_5_bounds(m: u32) -> (i128, i128) {
    let m = u128::from(m);
    // m * LOG2_5_HI + 2^64 - 1 < 2^32 * 2^66 + 2^64 fits a `u128`. `>> 64` rounds down, and
    // adding 2^64 - 1 first rounds up. As m * (LOG2_5_HI - LOG2_5_LO) = m < 2^64, the two
    // bounds are less than 1 apart before they are rounded, so at most 2 apart after.
    let lo = (m * LOG2_5_LO) >> 64;
    let hi = (m * LOG2_5_HI + u128::from(u64::MAX)) >> 64;
    // Both are below 2^35.
    (lo as i128, hi as i128)
}

/// `|x|` against `|y|`, for nonzero `x` and `y`.
fn cmp_abs(x: &Rat, y: &Rat) -> Ordering {
    cmp_abs_with(x, y, false)
}

// `cmp_abs(x, y)`. If `loop_only`, `cmp_pow5` bounds every power of 5 but 5^0 with its loop,
// which lets the tests reach the loop with small numbers.
fn cmp_abs_with(x: &Rat, y: &Rat, loop_only: bool) -> Ordering {
    let bits = |n: &Nat| i128::from(n.bits());
    // A nonzero `n` of `b` bits has b - 1 <= log2(n) < b, so log2(num / den) is in
    // (bits(num) - bits(den) - 1, bits(num) - bits(den) + 1), and log2|x| - log2|y| is in
    // (c - 2 + a5 * log2(5), c + 2 + a5 * log2(5)) for a5 = x.e5 - y.e5 and this `c`.
    let c = bits(&x.num) - bits(&x.den) - bits(&y.num) + bits(&y.den) + i128::from(x.e2)
        - i128::from(y.e2);
    let a = x.e5.abs_diff(y.e5);
    let (lo, hi) = log2_5_bounds(a);
    let (lo5, hi5) = if x.e5 >= y.e5 { (lo, hi) } else { (-hi, -lo) };
    if c - 2 + lo5 >= 0 {
        return Ordering::Greater;
    }
    if c + 2 + hi5 <= 0 {
        return Ordering::Less;
    }
    // Otherwise log2|x| - log2|y| is in (-6, 6), as hi5 - lo5 <= 2. Times
    // x.den * y.den * 2^-y.e2 * 5^-min(x.e5, y.e5), and for X = `xx` and Y = `yy`, |x| against
    // |y| is X * 5^a5 * 2^b against Y for a5 >= 0, and X * 2^b against Y * 5^-a5 for a5 < 0.
    let xx = &x.num * &y.den;
    let yy = &y.num * &x.den;
    let b = i128::from(x.e2) - i128::from(y.e2);
    if x.e5 >= y.e5 {
        cmp_pow5(&xx, a, b, &yy, loop_only)
    } else {
        cmp_pow5(&yy, a, -b, &xx, loop_only).reverse()
    }
}

// `x * 5^a * 2^b` against `y`, for nonzero `x` and `y`.
fn cmp_pow5(x: &Nat, a: u32, b: i128, y: &Nat, loop_only: bool) -> Ordering {
    // If the two are equal, 5^a divides `y`, as 5 and 2 are coprime, so 5^a <= y < 2^bits(y)
    // and a < bits(y). Up to this limit, which is above that, 5^a is computed exactly, in time
    // quadratic in the bits of `x` and `y`.
    let limit = if loop_only {
        0
    } else {
        x.bits() + y.bits() + 4096
    };
    if u64::from(a) <= limit {
        return cmp_shifted(&(x * &Nat::pow5(a)), b, y);
    }
    // Above it, the two differ unless `loop_only` lowered it, so bounds of 5^a decide once they
    // are close enough to it. Each pass doubles their bits, and at the latest once `p` reaches
    // the bits of 5^a, no step of `pow5_bound` cuts any bits off, and the lower bound is 5^a.
    let mut p = 128;
    loop {
        let (lo, k, exact) = pow5_bound(a, p, false);
        let o = cmp_shifted(&(x * &lo), b + k, y);
        if exact || o == Ordering::Greater {
            return o;
        }
        let (hi, k, _) = pow5_bound(a, p, true);
        if cmp_shifted(&(x * &hi), b + k, y) == Ordering::Less {
            return Ordering::Less;
        }
        p *= 2;
    }
}

// `(m, k, exact)` with `m * 2^k <= 5^a`, or `m * 2^k >= 5^a` if `up`, where `m` has at most
// `p + 1` bits, and `exact` is true exactly when `m * 2^k = 5^a`.
fn pow5_bound(a: u32, p: u64, up: bool) -> (Nat, i128, bool) {
    // Binary powering from the top bit of `a` down, where each step cuts `m` to its top `p`
    // bits, rounded down, or up if `up`. Squares and products of lower (upper) bounds of
    // positive numbers are lower (upper) bounds of theirs.
    let one = Nat::from_u64(1);
    let five = Nat::from_u64(5);
    let mut m = one.clone();
    let mut k: i128 = 0;
    let mut exact = true;
    for i in (0..32 - a.leading_zeros()).rev() {
        m = &m * &m;
        k *= 2;
        if (a >> i) & 1 == 1 {
            m = &m * &five;
        }
        let s = m.bits().saturating_sub(p);
        if s > 0 {
            // `Nat` has no right shift: m = q * 2^s + r with 0 <= r < 2^s.
            let (q, r) = m.div_rem(&(&one << s));
            exact &= r.is_zero();
            m = if up && !r.is_zero() { &q + &one } else { q };
            k += i128::from(s);
        }
    }
    (m, k, exact)
}

// `x * 2^e` against `y`, for nonzero `x` and `y`.
fn cmp_shifted(x: &Nat, e: i128, y: &Nat) -> Ordering {
    // 2^(bits(n) - 1) <= n < 2^bits(n) for a nonzero `n`, so different numbers of bits
    // decide. Otherwise, `e = bits(y) - bits(x)`, and the shift is at most as wide as `x` or
    // `y`.
    let bx = i128::from(x.bits()) + e;
    let by = i128::from(y.bits());
    match bx.cmp(&by) {
        Ordering::Equal if e >= 0 => (x << e as u64).cmp(y),
        Ordering::Equal => x.cmp(&(y << (-e) as u64)),
        o => o,
    }
}

impl Ord for Rat {
    fn cmp(&self, other: &Self) -> Ordering {
        let (s, t) = (self.sign(), other.sign());
        if s != t || s == 0 {
            s.cmp(&t)
        } else if s > 0 {
            cmp_abs(self, other)
        } else {
            cmp_abs(other, self)
        }
    }
}

impl PartialOrd for Rat {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Rat {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Rat {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Interval;
    use gmp_mpfr_sys::mpfr;
    use rug::{
        float::Round,
        integer::Order,
        ops::{DivAssignRound, MulAssignRound, PowAssignRound},
        Float, Integer, Rational,
    };
    use std::cmp::Ordering::*;

    struct Rng(u64);

    impl Rng {
        // SplitMix64, as in `src/simd/differential_tests.rs`.
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

        // An integer in [-max, max].
        fn exp(&mut self, max: u32) -> i32 {
            let max = i64::from(max);
            i32::try_from(self.below(2 * max as u64 + 1) as i64 - max).unwrap()
        }

        // A positive integer of at most `max_bits` bits, whose limbs are often 0 or all ones.
        fn int(&mut self, max_bits: u32) -> Integer {
            let bits = self.below(u64::from(max_bits)) as u32 + 1;
            let limbs: Vec<u64> = (0..(bits + 63) / 64)
                .map(|_| match self.below(4) {
                    0 => 0,
                    1 => u64::MAX,
                    _ => self.next(),
                })
                .collect();
            let mut n = Integer::from_digits(&limbs, Order::Lsf);
            n.keep_bits_mut(bits);
            if n == 0 {
                n = Integer::from(1);
            }
            n
        }
    }

    // The number of random cases, which can be set with `INARI_PARSE_N`.
    fn n_cases() -> u64 {
        std::env::var("INARI_PARSE_N")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(if cfg!(debug_assertions) {
                1_000
            } else {
                10_000
            })
    }

    // The random numbers of the test numbered `test`, which the seed `INARI_PARSE_SEED`
    // changes. Without it, they are those of `Rng(test)`.
    fn rng(test: u64) -> Rng {
        let seed = std::env::var("INARI_PARSE_SEED")
            .ok()
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(0);
        Rng(seed.wrapping_add(test))
    }

    // The fields of a `Rat` but `neg`, with its numbers as `rug` integers.
    #[derive(Clone, Debug)]
    struct R {
        num: Integer,
        den: Integer,
        e2: i32,
        e5: i32,
    }

    impl R {
        fn rat(&self, neg: bool) -> Rat {
            let nat = |n: &Integer| Nat::from_hex(&format!("{:x}", n));
            Rat {
                neg,
                num: nat(&self.num),
                den: nat(&self.den),
                e2: self.e2,
                e5: self.e5,
            }
        }

        // The value of `self`, exactly.
        fn value(&self) -> Rational {
            let p = Integer::from(Integer::u_pow_u(5, self.e5.unsigned_abs()));
            let (n, d) = if self.e5 >= 0 {
                (Integer::from(&self.num * &p), self.den.clone())
            } else {
                (self.num.clone(), Integer::from(&self.den * &p))
            };
            Rational::from((n, d)) << self.e2
        }

        // `prec`-bit MPFR numbers that bound `self` from below and above. Call it in
        // `wide_range`, so that they neither overflow nor underflow.
        fn bounds(&self, prec: u32) -> (Float, Float) {
            let bound = |r: Round| {
                // Each step rounds a bound of a positive number in the direction `r`.
                let mut f = Float::with_val(prec, 5);
                f.pow_assign_round(self.e5, r);
                f.mul_assign_round(&self.num, r);
                f.div_assign_round(&self.den, r);
                f <<= self.e2;
                f
            };
            (bound(Round::Down), bound(Round::Up))
        }

        fn hex(m: Integer, e2: i32) -> R {
            R {
                num: m,
                den: Integer::from(1),
                e2,
                e5: 0,
            }
        }
    }

    // `f()` in MPFR's widest exponent range.
    fn wide_range<T>(f: impl FnOnce() -> T) -> T {
        let (emin, emax) = unsafe { (mpfr::get_emin(), mpfr::get_emax()) };
        unsafe {
            mpfr::set_emin(mpfr::get_emin_min());
            mpfr::set_emax(mpfr::get_emax_max());
        }
        let x = f();
        unsafe {
            mpfr::set_emin(emin);
            mpfr::set_emax(emax);
        }
        x
    }

    // `x` against `y` by `cmp_abs`, by `cmp_abs` with the loop in place of the exact path, and by
    // `Rat`'s `Ord` with each sign, where `want` is `x` against `y`.
    fn check(x: &R, y: &R, want: Ordering) {
        let (a, b) = (x.rat(false), y.rat(false));
        assert_eq!(cmp_abs(&a, &b), want, "{:?} {:?}", x, y);
        assert_eq!(cmp_abs(&b, &a), want.reverse(), "{:?} {:?}", y, x);
        assert_eq!(cmp_abs_with(&a, &b, true), want, "loop: {:?} {:?}", x, y);
        for (sx, sy) in [(false, false), (false, true), (true, false), (true, true)] {
            let w = match (sx, sy) {
                (false, false) => want,
                (true, true) => want.reverse(),
                (false, true) => Greater,
                (true, false) => Less,
            };
            let (a, b) = (x.rat(sx), y.rat(sy));
            assert_eq!(a.cmp(&b), w, "{} {:?} {} {:?}", sx, x, sy, y);
            assert_eq!(a == b, w == Equal);
        }
    }

    // Whether the interval literal `s` is accepted.
    fn accepted(s: &str) -> bool {
        s.parse::<Interval>().is_ok()
    }

    #[test]
    fn log2_5_constants() {
        // log2(5) rounded down and up to 256 bits bound it, and their products with 2^64 both
        // round down to `LOG2_5_LO`.
        for r in [Round::Down, Round::Up] {
            let mut l = Float::with_val(256, 5);
            l.log2_round(r);
            l <<= 64;
            assert_eq!(l.to_integer_round(Round::Down).unwrap().0, LOG2_5_LO);
        }
        for m in [0, 1, 2, 3, 1000, 600_000_000, u32::MAX - 1, u32::MAX] {
            let (lo, hi) = log2_5_bounds(m);
            // A lower and an upper bound of m * log2(5).
            let bound = |r: Round| {
                let mut l = Float::with_val(256, 5);
                l.log2_round(r);
                l.mul_assign_round(m, r);
                l
            };
            assert!(lo <= bound(Round::Down) && bound(Round::Up) <= hi, "{}", m);
            assert!(hi - lo <= 2);
        }
    }

    #[test]
    fn zeros_and_signs() {
        let zero = |neg, e| Rat {
            neg,
            num: Nat::from_u64(0),
            den: Nat::from_u64(3),
            e2: e,
            e5: e,
        };
        let one = R {
            num: Integer::from(1),
            den: Integer::from(1),
            e2: -999_999_999,
            e5: -999_999_999,
        };
        assert_eq!(zero(false, 5), zero(true, -999_999_999));
        assert!(zero(true, 0) < one.rat(false));
        assert!(zero(false, 0) > one.rat(true));
    }

    // Random numbers with small exponents against their exact values.
    #[test]
    fn random_against_exact() {
        let mut rng = rng(1);
        let n = n_cases();
        for _ in 0..n {
            let max_e = if rng.below(8) == 0 { 2000 } else { 200 };
            let random = |rng: &mut Rng| {
                let e2 = rng.exp(max_e);
                R {
                    num: rng.int(300),
                    den: if rng.below(2) == 0 {
                        Integer::from(1)
                    } else {
                        rng.int(200)
                    },
                    e2,
                    // As the grammar makes them, and others.
                    e5: match rng.below(3) {
                        0 => 0,
                        1 => e2,
                        _ => rng.exp(max_e),
                    },
                }
            };
            let x = random(&mut rng);
            let y = if rng.below(4) == 0 {
                random(&mut rng)
            } else {
                // The value of `x`, written otherwise: a power of 5 and a power of 2 moved
                // between the numbers and the exponents, and another factor into both numbers.
                let mut y = x.clone();
                let bound = if rng.below(8) == 0 { 1500 } else { 40 };
                let j = rng.below(bound) as u32;
                let p5 = Integer::from(Integer::u_pow_u(5, j));
                match rng.below(3) {
                    0 => {
                        y.num *= p5;
                        y.e5 -= j as i32;
                    }
                    1 => {
                        y.den *= p5;
                        y.e5 += j as i32;
                    }
                    _ => (),
                }
                let j = rng.below(100) as u32;
                match rng.below(3) {
                    0 => {
                        y.num <<= j;
                        y.e2 -= j as i32;
                    }
                    1 => {
                        y.den <<= j;
                        y.e2 += j as i32;
                    }
                    _ => (),
                }
                if rng.below(2) == 0 {
                    let t = rng.int(100);
                    y.num *= &t;
                    y.den *= &t;
                }
                // And next to it.
                match rng.below(4) {
                    0 => y.num += 1,
                    1 if y.num > 1 => y.num -= 1,
                    _ => (),
                }
                y
            };
            check(&x, &y, x.value().cmp(&y.value()));
        }
        eprintln!("parse::rat random_against_exact: {} cases", n);
    }

    // Random numbers with exponents up to `i32::MAX` in magnitude, and close to each other,
    // against MPFR's bounds of them.
    #[test]
    fn random_huge_against_mpfr() {
        let mut rng = rng(2);
        let mut decided = 0;
        let n = n_cases() / 10;
        for _ in 0..n {
            let random = |rng: &mut Rng| R {
                num: rng.int(200),
                den: if rng.below(2) == 0 {
                    Integer::from(1)
                } else {
                    rng.int(100)
                },
                e2: rng.exp(i32::MAX as u32),
                e5: match rng.below(3) {
                    0 => 0,
                    _ => rng.exp(i32::MAX as u32),
                },
            };
            let x = random(&mut rng);
            let mut y = random(&mut rng);
            if rng.below(2) == 0 {
                y.e5 = x.e5.saturating_add(rng.exp(500_000_000));
            }
            // Move `y` to within a few binades of `x`, if its exponent `e2` allows that.
            let log2 = |r: &R| {
                f64::from(r.num.significant_bits()) - f64::from(r.den.significant_bits())
                    + f64::from(r.e2)
                    + f64::from(r.e5) * 5f64.log2()
            };
            let e2 = f64::from(y.e2) + log2(&x) - log2(&y) + f64::from(rng.exp(8));
            if let Ok(e2) = i32::try_from(e2 as i64) {
                y.e2 = e2;
            }
            let want = wide_range(|| {
                let (xl, xh) = x.bounds(256);
                let (yl, yh) = y.bounds(256);
                if xl > yh {
                    Some(Greater)
                } else if xh < yl {
                    Some(Less)
                } else {
                    None
                }
            });
            if let Some(want) = want {
                check(&x, &y, want);
                decided += 1;
            }
        }
        assert!(decided >= n * 9 / 10, "{} of {}", decided, n);
        eprintln!(
            "parse::rat random_huge_against_mpfr: {} cases, {} decided",
            n, decided
        );
    }

    // `d * 10^k` against hexadecimal numbers at it and next to it, at exponents `k` up to
    // 6.4 * 10^8 in magnitude, as `Rat`s and in interval literals. A `k` above about
    // 6.46 * 10^8 in magnitude would make the binary exponent of `d * 10^k` too large for
    // `to_integer_exp`, which panics beyond `i32`.
    #[test]
    fn dec_against_hex() {
        const PREC: u32 = 192;
        let mut rng = rng(3);
        let mut ks = vec![
            640_000_000,
            -640_000_000,
            600_000_000,
            -600_000_000,
            -27,
            -20,
            -1,
            0,
            1,
            22,
            23,
            308,
            -323,
            -1000,
        ];
        for _ in 0..n_cases() / 1000 {
            ks.push(rng.exp(640_000_000));
        }
        // 5^27 = 7450580596923828125 makes `d * 10^k` a dyadic number for k >= -27.
        let ds = [1, 3, 7, 123_456_789, 7_450_580_596_923_828_125, u64::MAX];
        let mut literals = Vec::new();
        let mut ties = 0;
        for &k in &ks {
            for &d in &ds {
                let dec = R {
                    num: Integer::from(d),
                    den: Integer::from(1),
                    e2: k,
                    e5: k,
                };
                let cases = wide_range(|| {
                    let (lo, hi) = dec.bounds(PREC);
                    let (m, j) = lo.to_integer_exp().unwrap();
                    let mut cases = Vec::new();
                    // `m * 2^j` has `PREC` bits, and its top 64 or 128 bits.
                    for t in [0, PREC - 128, PREC - 64] {
                        let m = Integer::from(&m >> t);
                        for delta in [-1, 0, 1, 2] {
                            let h = Integer::from(&m + delta);
                            let h_val = Float::with_val(PREC + 1, &h) << (j + t as i32);
                            // `lo < d * 10^k < hi` unless they are equal.
                            let want = if lo == hi {
                                h_val.partial_cmp(&lo).unwrap()
                            } else if h_val <= lo {
                                Less
                            } else if h_val >= hi {
                                Greater
                            } else {
                                continue;
                            };
                            cases.push((R::hex(h, j + t as i32), want));
                        }
                    }
                    cases
                });
                for (hex, want) in cases {
                    check(&hex, &dec, want);
                    ties += usize::from(want == Equal);
                    let h = format!("0x{:x}p{}", hex.num, hex.e2);
                    literals.push((format!("{}e{}", d, k), h, want));
                }
            }
        }
        assert!(ties > 0);
        eprintln!(
            "parse::rat dec_against_hex: {} exponents, {} cases, {} ties",
            ks.len(),
            literals.len(),
            ties
        );
        for (d, h, want) in literals {
            let lit = |a: &str, b: &str| format!("[{}, {}]", a, b);
            assert_eq!(accepted(&lit(&h, &d)), want != Greater, "{} {}", h, d);
            assert_eq!(accepted(&lit(&d, &h)), want != Less, "{} {}", d, h);
            let neg = |s: &str| format!("-{}", s);
            assert_eq!(accepted(&lit(&neg(&d), &neg(&h))), want != Greater);
        }
    }

    #[test]
    fn literal_verdicts() {
        // 10^-999999999 against 2 * 10^-999999999, which need no power of 5.
        assert!(!accepted("[2e-999999999, 1e-999999999]"));
        assert!(accepted("[1e-999999999, 2e-999999999]"));
        assert!(accepted("[10e-999999999, 1e-999999998]"));
        assert!(accepted("[1e-999999998, 10e-999999999]"));
        assert!(!accepted(
            "[10000000000000000000001e-999999999, 1e-999999977]"
        ));
        assert!(accepted("[1e600000000, 1e600000000]"));
        assert!(accepted("[1e-600000000, 1e600000000]"));
        assert!(!accepted("[1e600000000, 1e-600000000]"));
        // 10^-600000000 is about 2^-1993156856.93.
        assert!(!accepted("[1e-600000000, 0x1p-1993156913]"));
        assert!(accepted("[0x1p-1993156913, 1e-600000000]"));
        assert!(!accepted("[1e-600000000, 0x1p-1993156857]"));
        assert!(accepted("[0x1p-1993156857, 1e-600000000]"));
        assert!(accepted("[1e-600000000, 0x1p-1993156856]"));
        assert!(!accepted("[0x1p-1993156856, 1e-600000000]"));
        assert!(accepted("[-1e-600000000, -0x1p-1993156857]"));
        assert!(!accepted("[-0x1p-1993156857, -1e-600000000]"));
        // 5^20 * 10^-20 = 2^-20.
        assert!(accepted("[0x1p-20, 95367431640625e-20]"));
        assert!(accepted("[95367431640625e-20, 0x1p-20]"));
        assert!(!accepted("[95367431640626e-20, 0x1p-20]"));
        assert!(accepted("[1e-2147483648, 0x1p-2147483648]"));
        assert!(!accepted("[0x1p-2147483648, 1e-2147483648]"));
        assert!(accepted("[0x1p2147483647, 1e2147483647]"));
        assert!(!accepted("[1e2147483647, 0x1p2147483647]"));
        assert!(accepted("[3333333333333333e-16, 1/3]"));
        assert!(!accepted("[1/3, 3333333333333333e-16]"));
        assert!(accepted("[1/3, 0x0.55555555555555555556p0]"));
        assert!(!accepted("[1/3, 0x0.55555555555555555555p0]"));
        assert!(!accepted("[1/3, 1e-999999999]"));
    }
}
