// Compares `rational_to_f64` of `src/parse.rs` with MPFR, through `round_rational` of
// `src/mpfr_calls/mpfr.rs`, the MPFR calls with which inari rounded a rational to an `f64`
// before it had its own rounding: `f` by its bits, so that the sign of zero counts, `inexact`
// and `overflow`, in both directions, on random rationals of up to about 4000 bits, on exact
// `f64`s, midpoints and numbers just beside them, written as decimal, hexadecimal and `p/q`
// literals give them, on subnormal numbers, on exponents up to `i32::MAX` and down to
// `i32::MIN`, and on zeros of both signs. The literals also go through the grammar, and MPFR
// gets their values as `literal_case` reads them, without the grammar.
// `huge_exponents_end_to_end`, which times literals whose exponents are huge from end to end,
// needs no MPFR, so it is in `mod tests` of `src/parse.rs`, which also runs where the tests
// have no MPFR.
//
// Uncertain literals such as `-1.25?3ue-7` go through `FromStr` of `Interval` and
// `DecInterval` and `Interval::_try_from_str_exact` from end to end. `uncertain_oracle` reads
// them without the grammar and makes their bounds from the definition of the uncertain form in
// §12.11.4 c of the draft P1788/D9.5, with `Rational`s, and MPFR rounds them; the bounds are
// compared by their bits, along with the decorations and the kinds of the errors. The oracle
// takes the syntax as given, and the generator writes only literals that the grammar accepts,
// apart from the decoration `_ill`, so the rejections compared are those for the decoration
// and the exponent.
//
// MPFR has to be given the exact value, whose numerator and denominator have together about
// |e2| + 2.32 |e5| bits more than `num` and `den`, for the exponents `e2` of 2 and `e5` of 5:
// too many for exponents near the ends of `i32`. Where an estimate of log2|x| is above
// 1100, |x| > 2^1024, and where it is below -1200, 0 < |x| < 2^-1075. Then x and ±2^1100 or
// ±2^-1200 of the same sign round to the same `f64`s in both directions, inexactly, so MPFR
// gets ±2^1100 or ±2^-1200 instead. The estimate is off by far less than the 76 and 125 to
// spare.
//
// The number of random cases per generator can be set with `INARI_PARSE_N`, and the cases
// changed with the seed `INARI_PARSE_SEED`. Run with `--nocapture` to see the numbers of
// cases.

use super::{number, parse_number, rational_to_f64, InfSup, Nat, Number, Rat};
use crate::{
    mpfr_calls::mpfr::round_rational, DecInterval, Decoration, Interval, IntervalErrorKind,
};
use gmp_mpfr_sys::mpfr::rnd_t;
use rug::{integer::Order, Integer, Rational};
use std::{cmp::Ordering, f64::consts::LOG2_10};

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

    fn coin(&mut self) -> bool {
        self.next() & 1 == 1
    }

    // An integer in `lo..=hi`.
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + self.below((hi - lo + 1) as u64) as i64
    }

    // A number of bits from 1 to `max`, often small.
    fn bits(&mut self, max: u32) -> u32 {
        let max = match self.below(4) {
            0 => max.min(64),
            1 => max.min(200),
            _ => max,
        };
        1 + self.below(u64::from(max)) as u32
    }

    // A number of exactly `bits` bits: often 2^(bits - 1), 2^bits - 1, 2^(bits - 1) + 1 or
    // one with few bits set, so that the quotient and the remainder of `scale` hit their
    // edges.
    fn int(&mut self, bits: u32) -> Integer {
        if bits == 0 {
            return Integer::new();
        }
        let top = Integer::from(1) << (bits - 1);
        match self.below(8) {
            0 => top,
            1 => (top << 1u32) - 1u32,
            2 => top + 1u32,
            3 => {
                let mut x = top;
                for _ in 0..self.below(4) {
                    x.set_bit(self.below(u64::from(bits)) as u32, true);
                }
                x
            }
            _ => {
                let limbs: Vec<u64> = (0..(bits + 63) / 64).map(|_| self.next()).collect();
                let mut x = Integer::from_digits(&limbs, Order::Lsf);
                x.keep_bits_mut(bits);
                x.set_bit(bits - 1, true);
                x
            }
        }
    }

    // A binary logarithm to aim a value at: around the top of the range of `f64`, its
    // subnormal numbers or `f64::MIN_POSITIVE`, anywhere in it, or far out of it.
    fn target(&mut self) -> i64 {
        match self.below(8) {
            0 => self.range(1015, 1035),
            1 => self.range(-1090, -1065),
            2 => self.range(-1030, -1015),
            3 => self.range(-5000, 5000),
            _ => self.range(-1150, 1100),
        }
    }

    // The bits of a positive finite `f64`: often one at an edge of the range or a subnormal
    // number.
    fn float_bits(&mut self) -> u64 {
        match self.below(16) {
            0 => f64::MAX.to_bits(),
            1 => f64::MAX.to_bits() - 1,
            2 => f64::MIN_POSITIVE.to_bits(),
            3 => f64::MIN_POSITIVE.to_bits() - 1,
            4 => self.range(1, 2) as u64,
            5 => 1f64.to_bits(),
            6 => (self.range(1, 2046) as u64) << 52,
            7 | 8 => self.subnormal_bits(),
            _ => self.range(1, f64::MAX.to_bits() as i64) as u64,
        }
    }

    // The bits of a positive subnormal number, or of one of the smallest normal numbers.
    fn subnormal_bits(&mut self) -> u64 {
        match self.below(4) {
            0 => self.range(1, 64) as u64,
            1 => (1 << 52) - self.range(0, 64) as u64,
            _ => self.range(1, (1 << 52) + 2) as u64,
        }
    }

    // `n * 2^e` for the `f64` `m * 2^e` of `(m, e)`, or a number beside it: `(m ± 1/2) * 2^e`,
    // a number a little above or below it, or `(m ± 1) * 2^e`. These are the midpoints between
    // it and the next `f64` either way and the next `f64`s, of which the one above `f64::MAX`
    // is 2^1024, except below a power of two above `f64::MIN_POSITIVE`, where `(m - 1/2) * 2^e`
    // is the previous `f64` and `(m - 1) * 2^e` the one before it, and below 2^-1074, where
    // `(m - 1) * 2^e` would be 0 and the `f64` itself is taken instead.
    fn near(&mut self, (m, e): (u64, i64)) -> (Integer, i64) {
        let m = Integer::from(m);
        match self.below(7) {
            0 => (m, e),
            1 => ((m << 1u32) + 1u32, e - 1),
            2 => ((m << 1u32) - 1u32, e - 1),
            3 => {
                let j = self.range(1, 300);
                ((m << j as u32) + 1u32, e - j)
            }
            4 => {
                let j = self.range(1, 300);
                ((m << j as u32) - 1u32, e - j)
            }
            5 => (m + 1u32, e),
            _ if m > 1 => (m - 1u32, e),
            _ => (m, e),
        }
    }

    // `(-1)^neg * n * 2^e`, for a positive `n`, as a hexadecimal, `p/q` or decimal literal
    // gives it to `rational_to_f64`. The decimal is sometimes changed in its last digit,
    // cut to a few digits or put halfway between two of its last digits, as the bounds of an
    // uncertain literal are.
    fn dyadic_case(&mut self, neg: bool, n: Integer, e: i64) -> Case {
        match self.below(4) {
            0 => {
                // Hexadecimal, sometimes with zeros at the end.
                let s = self.range(0, 8);
                Case::new(neg, n << s as u32, Integer::from(1), e - s, 0)
            }
            1 => {
                // `p/q`, with a common factor.
                let b = self.bits(200);
                let q = self.int(b);
                if e >= 0 {
                    Case::new(neg, (n << e as u32) * &q, q, 0, 0)
                } else {
                    let d = Integer::from(&q << (-e) as u32);
                    Case::new(neg, n * q, d, 0, 0)
                }
            }
            _ => {
                let (d, k) = decimal_of(n, e);
                let (num, den, k) = match self.below(4) {
                    0 => {
                        let j = self.range(0, 3);
                        (d * pow(10, j), Integer::from(1), k - j)
                    }
                    1 => {
                        let j = self.range(1, 30);
                        let d = d * pow(10, j);
                        let d = if self.coin() { d + 1u32 } else { d - 1u32 };
                        (d, Integer::from(1), k - j)
                    }
                    2 => {
                        let len = d.to_string().len() as i64;
                        let s = self.range(1, 40);
                        if len > s {
                            let d = d / pow(10, len - s) + self.range(0, 1) as u32;
                            (d, Integer::from(1), k + len - s)
                        } else {
                            (d, Integer::from(1), k)
                        }
                    }
                    _ => {
                        let d = d << 1u32;
                        let d = if self.coin() { d + 1u32 } else { d - 1u32 };
                        (d, Integer::from(2), k)
                    }
                };
                Case::new(neg, num, den, k, k)
            }
        }
    }

    // `n` decimal digits: often all zeros, all nines, a one or a five and zeros, or with
    // leading zeros.
    fn dec_digits(&mut self, n: usize) -> String {
        let mut s: String = (0..n)
            .map(|_| char::from(b'0' + self.below(10) as u8))
            .collect();
        match self.below(8) {
            0 => s = "0".repeat(n),
            1 => s = "9".repeat(n),
            2 => s = ["1", "5"][self.below(2) as usize].to_owned() + &"0".repeat(n - 1),
            3 => {
                let z = self.below(n as u64) as usize;
                s.replace_range(..z, &"0".repeat(z));
            }
            _ => (),
        }
        s
    }

    // An uncertain literal `m?r` `u` `e k`, as §12.11.4 c of the draft P1788/D9.5 defines it,
    // with a sign or none, and its letters in either case. The center `m` has 1 to 40 digits
    // and a point anywhere or none, or is an `f64` rounded to 1 to 40 significant digits, or
    // to 741 to 801, which is exact unless the `f64` needs more (it can need up to 767). The
    // radius is half an ulp, 0 to 40 digits of ulps, about as many ulps as the digits of `m`,
    // so that a bound is 0 or an ulp from it, or unbounded, on both sides or one. An `f64`
    // center keeps its own exponent. Otherwise the exponent is none, is small, puts the
    // larger of `m` and `r` ulps near `f64::MAX`, `f64::MIN_POSITIVE` or the smallest
    // subnormal number, is anywhere in the range of `i32` or at its ends, or does not fit an
    // `i32`. A quarter of the literals have a decoration, some of them not a valid one.
    fn uncertain(&mut self) -> String {
        let sign = ["", "+", "-"][self.below(3) as usize];
        let (m, float_k) = if self.below(4) == 0 {
            let x = f64::from_bits(self.float_bits());
            // Up to 767 significant digits are needed for the exact decimal of an `f64`.
            let p = if self.below(16) == 0 {
                self.range(740, 800)
            } else {
                self.range(0, 39)
            };
            let s = format!("{:.*e}", p as usize, x);
            let (m, k) = s.split_once('e').unwrap();
            (m.to_owned(), Some(k.parse::<i64>().unwrap()))
        } else {
            let n = self.range(1, 40) as usize;
            let digits = self.dec_digits(n);
            if self.below(4) == 0 {
                (digits, None)
            } else {
                let j = self.range(0, n as i64) as usize;
                (format!("{}.{}", &digits[..j], &digits[j..]), None)
            }
        };
        let center = m.replace('.', "");
        let radius = match self.below(8) {
            0 | 1 => String::new(),
            2 => "?".to_owned(),
            3 => "0".repeat(self.range(1, 3) as usize),
            4 => self.range(1, 20).to_string(),
            5 => {
                let n = self.range(1, 40) as usize;
                self.dec_digits(n)
            }
            6 => {
                let c = center.parse::<Integer>().unwrap() + self.range(-1, 1);
                c.max(Integer::new()).to_string()
            }
            _ => format!("00{}", self.range(0, 999)),
        };
        let dir = ["", "", "u", "d", "U", "D"][self.below(6) as usize];
        // m and r ulps, where r is written in digits, are below 10^(top + 1), and the larger
        // of them is at least 10^top unless it is 0.
        let digits_after_point = m.split_once('.').map_or(0, |(_, f)| f.len()) as i64;
        let significant = |s: &str| s.trim_start_matches('0').len().max(1) as i64;
        let r = if radius.starts_with(|c: char| c.is_ascii_digit()) {
            significant(&radius)
        } else {
            0
        };
        let top = significant(&center).max(r) - 1 - digits_after_point;
        let k = match float_k {
            Some(k) => Some(Integer::from(k)),
            None => match self.below(8) {
                0 => None,
                1 => Some(Integer::from(self.range(-30, 30))),
                2 | 3 => {
                    let t = [308, -308, -324][self.below(3) as usize];
                    Some(Integer::from(t - top + self.range(-2, 2)))
                }
                4 => Some(Integer::from(self.range(-400, 400))),
                5 => Some(Integer::from(if self.coin() {
                    i64::from(i32::MAX) - self.range(0, 50)
                } else {
                    // `k` minus the digits after the point can be below `i32::MIN`.
                    i64::from(i32::MIN) + self.range(0, 50)
                })),
                6 => Some(Integer::from(
                    self.range(i64::from(i32::MIN), i64::from(i32::MAX)),
                )),
                _ => Some(match self.below(3) {
                    0 => Integer::from(i32::MAX) + self.range(1, 1000),
                    1 => Integer::from(i32::MIN) - self.range(1, 1000),
                    _ => {
                        let n = self.range(11, 30) as usize;
                        let k = self.dec_digits(n).parse::<Integer>().unwrap();
                        if self.coin() {
                            -k
                        } else {
                            k
                        }
                    }
                }),
            },
        };
        let exp = match k {
            None => String::new(),
            Some(k) => {
                let e = ["e", "E"][self.below(2) as usize];
                let sign = match k.cmp0() {
                    Ordering::Less => "-",
                    // `-0` is an integer literal too.
                    Ordering::Equal => ["", "+", "-"][self.below(3) as usize],
                    Ordering::Greater => ["", "+"][self.below(2) as usize],
                };
                let zeros = if self.below(4) == 0 { "00" } else { "" };
                format!("{}{}{}{}", e, sign, zeros, k.abs())
            }
        };
        let dec = if self.below(4) == 0 {
            ["_com", "_dac", "_def", "_trv", "_ill", "_COM", "_Dac"][self.below(7) as usize]
        } else {
            ""
        };
        format!("{}{}?{}{}{}{}", sign, m, radius, dir, exp, dec)
    }
}

// The number of random cases per generator, which can be set with `INARI_PARSE_N`.
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

// The random numbers of the generator numbered `gen`, which `INARI_PARSE_SEED` changes.
fn rng(gen: u64) -> Rng {
    let seed = std::env::var("INARI_PARSE_SEED")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(0);
    Rng(seed.wrapping_add(gen << 32))
}

// `b^k` for `k >= 0`.
fn pow(b: u32, k: i64) -> Integer {
    Integer::from(Integer::u_pow_u(b, u32::try_from(k).unwrap()))
}

// `(m, e)` of the positive finite `f64` `x = m * 2^e`, with `m < 2^53`.
fn float_parts(x: f64) -> (u64, i64) {
    let bits = x.to_bits();
    let frac = bits & ((1 << 52) - 1);
    match (bits >> 52) as i64 {
        0 => (frac, -1074),
        exp => (frac | 1 << 52, exp - 1075),
    }
}

// `(d, k)` of the decimal `d * 10^k` that equals `n * 2^e`: `10^k = 2^k * 5^k`.
fn decimal_of(n: Integer, e: i64) -> (Integer, i64) {
    if e >= 0 {
        (n << e as u32, 0)
    } else {
        (n * pow(5, -e), e)
    }
}

// The rational `(-1)^neg * num * 2^e2 * 5^e5 / den`, with `den > 0`, as the `Rat` that
// `rational_to_f64` gets and as the integers of which the oracle makes its value.
#[derive(Debug)]
struct Case {
    neg: bool,
    num: Integer,
    den: Integer,
    e2: i32,
    e5: i32,
}

impl Case {
    fn new(neg: bool, num: Integer, den: Integer, e2: i64, e5: i64) -> Self {
        assert!(num >= 0 && den > 0);
        Self {
            neg,
            num,
            den,
            e2: i32::try_from(e2).unwrap(),
            e5: i32::try_from(e5).unwrap(),
        }
    }

    fn rat(&self) -> Rat {
        let nat = |x: &Integer| Nat::from_hex(&format!("{:x}", x));
        Rat {
            neg: self.neg,
            num: nat(&self.num),
            den: nat(&self.den),
            e2: self.e2,
            e5: self.e5,
        }
    }
}

// `f` by its bits, `inexact` and `overflow`.
type Outcome = (u64, bool, bool);

fn ours(x: &Rat, infsup: InfSup) -> Outcome {
    let r = rational_to_f64(x, infsup);
    (r.f.to_bits(), r.inexact, r.overflow)
}

// log2(5) = log2(10) - 1, and the subtraction is exact.
const LOG2_5: f64 = LOG2_10 - 1.0;

// log2(x) of a positive `x`, off by less than 2^-40 for `x` below 2^4096, which every `x`
// here is.
fn log2(x: &Integer) -> f64 {
    // The top 64 bits as a float, times a power of two.
    let s = x.significant_bits().saturating_sub(64);
    Integer::from(x >> s).to_f64().log2() + f64::from(s)
}

// What `rational_to_f64` has to return for `c`, by MPFR, as `rational_to_f64` computed it
// before it had its own rounding: `f` and the ternary value of `round_rational`, `inexact`
// when that is nonzero and `overflow` when `f` is infinite. MPFR gets the value of `c`, or
// ±2^1100 or ±2^-1200 as the comment at the top says.
fn oracle(c: &Case, infsup: InfSup) -> Outcome {
    let abs = if c.num == 0 {
        Rational::new()
    } else {
        let est = log2(&c.num) - log2(&c.den) + f64::from(c.e2) + f64::from(c.e5) * LOG2_5;
        if est > 1100.0 {
            Rational::from(Integer::from(1) << 1100u32)
        } else if est < -1200.0 {
            Rational::from((Integer::from(1), Integer::from(1) << 1200u32))
        } else {
            exact(c)
        }
    };
    let r = if c.neg { -abs } else { abs };
    let rnd = match infsup {
        InfSup::Inf => rnd_t::RNDD,
        InfSup::Sup => rnd_t::RNDU,
    };
    let (_, t, f) = round_rational(&r, rnd, |_, _| ());
    (f.to_bits(), t != 0, f.is_infinite())
}

// `|c|`, exactly.
fn exact(c: &Case) -> Rational {
    // Inside the window of `oracle`, the generators keep the exponents small.
    assert!(
        c.e2.unsigned_abs() <= 1 << 20 && c.e5.unsigned_abs() <= 1 << 20,
        "{:?}",
        c
    );
    let (mut n, mut d) = (c.num.clone(), c.den.clone());
    let p5 = pow(5, i64::from(c.e5.unsigned_abs()));
    if c.e5 >= 0 {
        n *= p5;
    } else {
        d *= p5;
    }
    if c.e2 >= 0 {
        n <<= c.e2.unsigned_abs();
    } else {
        d <<= c.e2.unsigned_abs();
    }
    Rational::from((n, d))
}

const BOTH: [InfSup; 2] = [InfSup::Inf, InfSup::Sup];

// Adds to `report` each direction in which `rational_to_f64` of `c` and the oracle differ.
fn check(c: &Case, report: &mut Vec<String>) {
    let x = c.rat();
    for infsup in BOTH {
        let (a, b) = (ours(&x, infsup), oracle(c, infsup));
        if a != b {
            report.push(format!("{:?} {:?}: ours {:?}, MPFR {:?}", c, infsup, a, b));
        }
    }
}

// The `Rat` that the grammar makes of the number literal `s`.
fn grammar_rat(s: &str) -> Rat {
    match number(s) {
        Ok(("", n)) => match parse_number(n) {
            Ok(Number::Rational(x)) => x,
            r => panic!("{}: {:?}", s, r),
        },
        _ => panic!("{}: not a number literal", s),
    }
}

// The `Case` of the decimal, hexadecimal or `p/q` literal `s`, which can have a sign, read
// without the grammar of `src/parse.rs`, for the oracle.
fn literal_case(s: &str) -> Case {
    let (neg, s) = match s.strip_prefix('-') {
        Some(t) => (true, t),
        None => (false, s.strip_prefix('+').unwrap_or(s)),
    };
    let s = s.to_ascii_lowercase();
    // The digits before and after the point of `m`, as one number, and how many come after.
    let digits = |m: &str, radix: i32| {
        let (int, frac) = m.split_once('.').unwrap_or((m, ""));
        let n = Integer::from_str_radix(&[int, frac].concat(), radix).unwrap();
        (n, frac.len() as i64)
    };
    if let Some((p, q)) = s.split_once('/') {
        Case::new(neg, p.parse().unwrap(), q.parse().unwrap(), 0, 0)
    } else if let Some(h) = s.strip_prefix("0x") {
        let (m, e) = h.split_once('p').unwrap();
        let (n, f) = digits(m, 16);
        let e2 = e.parse::<i64>().unwrap() - 4 * f;
        Case::new(neg, n, Integer::from(1), e2, 0)
    } else {
        let (m, e) = s.split_once('e').unwrap_or((&s, "0"));
        let (n, f) = digits(m, 10);
        let k = e.parse::<i64>().unwrap() - f;
        Case::new(neg, n, Integer::from(1), k, k)
    }
}

// Adds to `report` each direction in which `rational_to_f64` of the `Rat` that the grammar
// makes of the number literal `s` and the oracle of `literal_case(s)` differ.
fn check_literal(s: &str, report: &mut Vec<String>) {
    let x = grammar_rat(s);
    let c = literal_case(s);
    for infsup in BOTH {
        let (a, b) = (ours(&x, infsup), oracle(&c, infsup));
        if a != b {
            report.push(format!("{} {:?}: ours {:?}, MPFR {:?}", s, infsup, a, b));
        }
    }
}

// The uncertain literal `m?r` `u` `e k`, which can have a sign and a decoration after `_`,
// read without the grammar of `src/parse.rs`, as §12.11.3 and §12.11.4 c of the draft
// P1788/D9.5 define its interval: ulp(m) is 10^-d for the `d` digits after the point of `m`,
// the radius is half an ulp for `?` alone, `r` ulps for `?r` and unbounded for `??`, `d` and
// `u` keep only the lower and the upper side of the radius, and the exponent multiplies the
// whole interval by 10^k. Letters can be in either case (§12.11.1).
struct Uncertain {
    // The bounds before the interval is multiplied by 10^k, `None` where they are infinite.
    lo: Option<Rational>,
    hi: Option<Rational>,
    digits_after_point: usize,
    k: Integer,
    dec: Option<String>,
}

fn uncertain_case(s: &str) -> Uncertain {
    let s = s.to_ascii_lowercase();
    let (s, dec) = match s.split_once('_') {
        Some((s, d)) => (s, Some(d.to_owned())),
        None => (&s[..], None),
    };
    let (neg, s) = match s.strip_prefix('-') {
        Some(t) => (true, t),
        None => (false, s.strip_prefix('+').unwrap_or(s)),
    };
    let (m, s) = s.split_once('?').unwrap();
    let (int, frac) = m.split_once('.').unwrap_or((m, ""));
    let ulp = Rational::from((Integer::from(1), pow(10, frac.len() as i64)));
    // The value of the digits and the point of `m` (§12.11.2 a).
    let m = Rational::from([int, frac].concat().parse::<Integer>().unwrap()) * &ulp;
    let m = if neg { -m } else { m };
    let (radius, s) = match s.strip_prefix('?') {
        Some(s) => (None, s),
        None => {
            let n = s.bytes().take_while(u8::is_ascii_digit).count();
            let r = if n == 0 {
                Rational::from((1, 2))
            } else {
                Rational::from(s[..n].parse::<Integer>().unwrap())
            };
            (Some(r * &ulp), &s[n..])
        }
    };
    let (down, up, s) = if let Some(s) = s.strip_prefix('d') {
        (true, false, s)
    } else if let Some(s) = s.strip_prefix('u') {
        (false, true, s)
    } else {
        (true, true, s)
    };
    let k = match s.strip_prefix('e') {
        Some(k) => k.parse::<Integer>().unwrap(),
        None => {
            assert!(s.is_empty(), "{}", s);
            Integer::new()
        }
    };
    let lo = match (down, &radius) {
        (false, _) => Some(m.clone()),
        (true, Some(r)) => Some(Rational::from(&m - r)),
        (true, None) => None,
    };
    let hi = match (up, &radius) {
        (false, _) => Some(m),
        (true, Some(r)) => Some(m + r),
        (true, None) => None,
    };
    Uncertain {
        lo,
        hi,
        digits_after_point: frac.len(),
        k,
        dec,
    }
}

// The bits of the bounds of `x`, so that -0 and +0 differ.
fn bits(x: Interval) -> (u64, u64) {
    (x.inf_raw().to_bits(), x.sup_raw().to_bits())
}

// What `FromStr` of `Interval`, `Interval::_try_from_str_exact` and `FromStr` of `DecInterval`
// return for a literal: the bits of the bounds and, for `DecInterval`, the decoration, or the
// kind of the error.
#[derive(Debug, PartialEq)]
struct Parsed {
    bare: Result<(u64, u64), IntervalErrorKind>,
    exact: Result<(u64, u64), IntervalErrorKind>,
    dec: Result<(u64, u64, Decoration), IntervalErrorKind>,
}

impl Parsed {
    fn of(s: &str) -> Self {
        let dec = |x: DecInterval| {
            let (a, b) = bits(x.interval().unwrap_or_else(|| panic!("{}: NaI", s)));
            (a, b, x.decoration())
        };
        Self {
            bare: s.parse().map(bits).map_err(|e| e.kind()),
            exact: Interval::_try_from_str_exact(s)
                .map(bits)
                .map_err(|e| e.kind()),
            dec: s.parse().map(dec).map_err(|e| e.kind()),
        }
    }

    // Every parser rejects the literal: `FromStr` of `DecInterval` with `kind`, and `FromStr`
    // of `Interval` and `Interval::_try_from_str_exact` with `kind` too, or with
    // `UndefinedOperation` if the literal has a decoration, as they reject every literal with
    // one.
    fn rejected(has_dec: bool, kind: IntervalErrorKind) -> Self {
        let bare = if has_dec {
            IntervalErrorKind::UndefinedOperation
        } else {
            kind
        };
        Self {
            bare: Err(bare),
            exact: Err(bare),
            dec: Err(kind),
        }
    }
}

// What the parsers have to return for the uncertain literal `s`: `uncertain_case(s)`
// multiplied by 10^k, its bounds rounded by `oracle` toward -∞ and +∞, which takes 10^k as
// 2^k * 5^k and gives MPFR ±2^1100 or ±2^-1200 in place of a bound whose estimated log2 is
// above 1100 or below -1200, as the comment at the top says. It is decorated `com` if it is
// bounded and `dac` otherwise, as newDec does (§11.5.1), or with its decoration, of which
// `com` is only for a bounded one (§11.4), and `dac` in place of `com` if a bound overflowed
// (§12.12.7), by the clauses of the draft P1788/D9.5. `FromStr` of `Interval` and
// `Interval::_try_from_str_exact` reject every literal with a decoration, and
// `_try_from_str_exact` also one with an inexact bound.
fn uncertain_oracle(s: &str) -> Parsed {
    use Decoration::*;
    use IntervalErrorKind::*;

    let u = uncertain_case(s);
    // `ill` is not the decoration of a literal (§12.11.5 c).
    let dec = match u.dec.as_deref() {
        None => None,
        Some("com") => Some(Com),
        Some("dac") => Some(Dac),
        Some("def") => Some(Def),
        Some("trv") => Some(Trv),
        Some(_) => return Parsed::rejected(true, UndefinedOperation),
    };
    // Item b.3 of `src/_docs/conformance.md`: an exponent that does not fit an `i32`, or
    // impractically many digits after the point, which this test reads as so many that `k`
    // minus their number does not fit an `i32`, is `PossiblyUndefinedOperation`.
    let d = i32::try_from(u.digits_after_point).unwrap();
    let k = match u.k.to_i32().filter(|k| k.checked_sub(d).is_some()) {
        Some(k) => i64::from(k),
        None => return Parsed::rejected(dec.is_some(), PossiblyUndefinedOperation),
    };
    // The bound `b * 10^k`, rounded, and whether that is exact.
    let round = |b: &Option<Rational>, infsup: InfSup| match b {
        None => match infsup {
            InfSup::Inf => (f64::NEG_INFINITY, true),
            InfSup::Sup => (f64::INFINITY, true),
        },
        Some(b) => {
            let neg = b.cmp0() == Ordering::Less;
            let num = Integer::from(b.numer().abs_ref());
            let c = Case::new(neg, num, b.denom().clone(), k, k);
            let (f, inexact, _) = oracle(&c, infsup);
            (f64::from_bits(f), !inexact)
        }
    };
    let (a, a_exact) = round(&u.lo, InfSup::Inf);
    let (b, b_exact) = round(&u.hi, InfSup::Sup);
    let bounded = u.lo.is_some() && u.hi.is_some();
    let d = match dec {
        None if bounded => Com,
        None => Dac,
        Some(Com) if !bounded => return Parsed::rejected(true, UndefinedOperation),
        Some(d) => d,
    };
    let d = if d == Com && (a.is_infinite() || b.is_infinite()) {
        Dac
    } else {
        d
    };
    let x = (a.to_bits(), b.to_bits());
    Parsed {
        bare: if dec.is_some() {
            Err(UndefinedOperation)
        } else {
            Ok(x)
        },
        exact: if dec.is_some() || !(a_exact && b_exact) {
            Err(UndefinedOperation)
        } else {
            Ok(x)
        },
        dec: Ok((x.0, x.1, d)),
    }
}

// Adds to `report` how the parsers and `uncertain_oracle` differ on the uncertain literal
// `s`, if they do, and returns what the oracle says.
fn check_uncertain(s: &str, report: &mut Vec<String>) -> Parsed {
    let (ours, want) = (Parsed::of(s), uncertain_oracle(s));
    if ours != want {
        report.push(format!("{}: ours {:?}, oracle {:?}", s, ours, want));
    }
    want
}

// Runs the generator `gen` numbered `n` for `n_cases()` cases, and fails with the first
// mismatches if there are any.
fn run(name: &str, n: u64, mut gen: impl FnMut(&mut Rng, &mut Vec<String>)) {
    let mut rng = rng(n);
    let seed = rng.0;
    let cases = n_cases();
    let mut report = Vec::new();
    for _ in 0..cases {
        gen(&mut rng, &mut report);
    }
    eprintln!("parse::diff_tests {}: {} cases", name, cases);
    assert!(
        report.is_empty(),
        "{}: {} mismatches with the seed {}, the first:\n{}",
        name,
        report.len(),
        seed,
        report[..report.len().min(10)].join("\n")
    );
}

// Number literals for which `check_literal` found a mismatch, and uncertain literals for which
// `check_uncertain` found one, each with what it broke and where it was found. In the style of
// `regressions()` in `src/simd/differential_tests.rs`, which takes the arguments of SIMD
// operations and is compiled only on x86_64 and on wasm32 with `simd128`, without
// `force-generic`, so not on aarch64, where these tests run too.
fn regressions() -> Vec<&'static str> {
    vec![]
}

#[test]
fn regressions_against_mpfr() {
    let mut report = Vec::new();
    for s in regressions() {
        if s.contains('?') {
            check_uncertain(s, &mut report);
        } else {
            check_literal(s, &mut report);
        }
    }
    assert!(report.is_empty(), "{}", report.join("\n"));
}

#[test]
fn random_rationals() {
    run("random_rationals", 1, |rng, report| {
        let neg = rng.coin();
        let num = if rng.below(32) == 0 {
            Integer::new()
        } else {
            let b = rng.bits(4000);
            rng.int(b)
        };
        let b = rng.bits(4000);
        let den = rng.int(b);
        let t = rng.target();
        let b = i64::from(num.significant_bits()) - i64::from(den.significant_bits());
        // As a decimal literal gives it, a hexadecimal one, a `p/q` one, or with any
        // exponents of two and five.
        let (e2, e5) = match rng.below(4) {
            0 => {
                let k = ((t - b) as f64 / LOG2_10).round() as i64;
                (k, k)
            }
            1 => (t - b, 0),
            2 => (0, 0),
            _ => {
                let e5 = rng.range(-3000, 3000);
                (t - b - (e5 as f64 * LOG2_5).round() as i64, e5)
            }
        };
        check(&Case::new(neg, num, den, e2, e5), report);
    });
}

#[test]
fn near_floats() {
    run("near_floats", 2, |rng, report| {
        let neg = rng.coin();
        let p = float_parts(f64::from_bits(rng.float_bits()));
        let (n, e) = rng.near(p);
        let c = rng.dyadic_case(neg, n, e);
        check(&c, report);
    });
}

#[test]
fn subnormals() {
    run("subnormals", 3, |rng, report| {
        let neg = rng.coin();
        let bits = rng.subnormal_bits();
        let (n, e) = rng.near(float_parts(f64::from_bits(bits)));
        let c = rng.dyadic_case(neg, n, e);
        check(&c, report);
    });
}

#[test]
fn huge_exponents() {
    run("huge_exponents", 4, |rng, report| {
        let k = match rng.below(6) {
            0 => i64::from(i32::MAX),
            1 => i64::from(i32::MIN),
            2 => i64::from(i32::MAX) - rng.range(0, 1000),
            3 => i64::from(i32::MIN) + rng.range(0, 1000),
            4 => rng.range(i64::from(i32::MIN), i64::from(i32::MAX)),
            _ => {
                let k = rng.range(1300, 1 << 20);
                if rng.coin() {
                    k
                } else {
                    -k
                }
            }
        };
        let b = rng.bits(4000);
        let num = rng.int(b);
        let den = if rng.coin() {
            Integer::from(1)
        } else {
            let b = rng.bits(4000);
            rng.int(b)
        };
        // As a decimal or a hexadecimal literal gives it, or a power of five alone.
        let (e2, e5) = match rng.below(3) {
            0 => (k, k),
            1 => (k, 0),
            _ => (0, k),
        };
        check(&Case::new(rng.coin(), num, den, e2, e5), report);
    });
}

#[test]
fn zeros() {
    run("zeros", 5, |rng, report| {
        let b = rng.bits(4000);
        let den = rng.int(b);
        let e2 = rng.range(i64::from(i32::MIN), i64::from(i32::MAX));
        let e5 = match rng.below(3) {
            0 => e2,
            1 => 0,
            _ => rng.range(i64::from(i32::MIN), i64::from(i32::MAX)),
        };
        let c = Case::new(rng.coin(), Integer::new(), den, e2, e5);
        // 0 is +0 and exact, whatever its sign and exponents, as `mpfr_set_q` makes it.
        for infsup in BOTH {
            assert_eq!(ours(&c.rat(), infsup), (0, false, false), "{:?}", c);
        }
        check(&c, report);
    });
}

#[test]
fn literals() {
    run("literals", 6, |rng, report| {
        let sign = ["", "+", "-"][rng.below(3) as usize];
        let x = f64::from_bits(rng.float_bits());
        let (m, e) = float_parts(x);
        let s = match rng.below(6) {
            // The shortest decimal that rounds to `x` to nearest.
            0 => format!("{}{:e}", sign, x),
            1 => format!("{}{:.*e}", sign, rng.below(40) as usize, x),
            // Up to 767 significant digits are needed for the exact decimal of an `f64`.
            2 => format!("{}{:.*e}", sign, rng.range(740, 800) as usize, x),
            3 => format!("{}0x{:x}p{}", sign, m, e),
            4 => {
                let b = rng.bits(300);
                let n = rng.int(b);
                let b = rng.bits(300);
                format!("{}{}/{}", sign, n, rng.int(b))
            }
            // Digits with an exponent anywhere in the range of `i32`.
            _ => {
                let b = rng.bits(1000);
                let n = rng.int(b);
                let k = rng.range(i64::from(i32::MIN), i64::from(i32::MAX));
                if rng.coin() {
                    format!("{}{}e{}", sign, n, k)
                } else {
                    format!("{}0x{:x}p{}", sign, n, k)
                }
            }
        };
        check_literal(&s, report);
    });
}

#[test]
fn uncertain_literals() {
    // How many literals were rejected, had an infinite bound, had one without `??`, which only
    // an overflow gives (a `??u` or `??d` literal whose finite bound overflowed is not
    // counted), or were exact.
    let mut counts = [0u64; 4];
    run("uncertain_literals", 7, |rng, report| {
        let s = rng.uncertain();
        let want = check_uncertain(&s, report);
        match want.dec {
            Err(_) => counts[0] += 1,
            Ok((a, b, _)) => {
                let (a, b) = (f64::from_bits(a), f64::from_bits(b));
                if a.is_infinite() || b.is_infinite() {
                    counts[1] += 1;
                    if !s.contains("??") {
                        counts[2] += 1;
                    }
                }
            }
        }
        if want.exact.is_ok() {
            counts[3] += 1;
        }
    });
    eprintln!(
        "parse::diff_tests uncertain_literals: {} rejected, {} with an infinite bound, \
         {} overflowed without `??`, {} exact",
        counts[0], counts[1], counts[2], counts[3]
    );
}

// A bound of an uncertain literal, worked out by hand for `uncertain_oracle_examples`.
enum Bound {
    // -∞ or +∞, from the radius `??`, which is exact.
    Inf,
    // A decimal, which has to be rounded outward to the closest `f64`, or to an infinity
    // beyond `f64::MAX`, and is exact if it is that `f64`.
    Q(Rational),
    // A decimal whose power of ten is too large for `dec` to build, and the `f64` to which it
    // rounds, inexactly.
    Far(f64),
}

// `n * 10^k` as a `Bound`.
fn dec(n: i64, k: i64) -> Bound {
    let p = pow(10, k.abs());
    let (n, d) = if k >= 0 {
        (n * p, Integer::from(1))
    } else {
        (Integer::from(n), p)
    };
    Bound::Q(Rational::from((n, d)))
}

// What `FromStr` of `DecInterval` has to return for an uncertain literal, by hand.
enum Want {
    // An error of this kind.
    Rejected(IntervalErrorKind),
    // The bounds and the decoration.
    Accepted(Bound, Bound, Decoration),
}

// Whether `f` is `x` rounded toward +∞ if `up` and toward -∞ otherwise: the closest `f64` on
// that side of `x`, or an infinity if there is none. A zero has the sign of `x`, and is +0 if
// `x` is 0, as `signs_of_zero` asserts of `oracle`.
fn is_rounded(x: &Rational, f: f64, up: bool) -> bool {
    let q = |f: f64| Rational::from_f64(f).unwrap();
    // `x` rounded up is `-x` rounded down, negated.
    let (y, g) = if up {
        (Rational::from(-x), -f)
    } else {
        (x.clone(), f)
    };
    // Whether `g` is the largest `f64` at most `y`, or -∞ if there is none.
    let down = if g == f64::NEG_INFINITY {
        y < q(f64::MIN)
    } else if g.is_finite() {
        let next = if g == 0.0 {
            f64::from_bits(1)
        } else if g > 0.0 {
            f64::from_bits(g.to_bits() + 1)
        } else {
            f64::from_bits(g.to_bits() - 1)
        };
        q(g) <= y && (g == f64::MAX || y < q(next))
    } else {
        false
    };
    down && (f != 0.0 || f.is_sign_negative() == (x.cmp0() == Ordering::Less))
}

// Checks the bound `f` that `uncertain_oracle` makes of the literal `s` against `want`, and
// returns whether `f` is exact.
fn check_bound(s: &str, want: &Bound, f: f64, up: bool) -> bool {
    match want {
        Bound::Inf => {
            let inf = if up { f64::INFINITY } else { f64::NEG_INFINITY };
            assert_eq!(f, inf, "{}", s);
            true
        }
        Bound::Q(x) => {
            assert!(is_rounded(x, f, up), "{}: {:e} for {}", s, f, x);
            f.is_finite() && Rational::from_f64(f).unwrap() == *x
        }
        Bound::Far(g) => {
            assert_eq!(f.to_bits(), g.to_bits(), "{}: {:e}", s, f);
            false
        }
    }
}

// Uncertain literals and their values, worked out by hand from §12.11.1, §12.11.3,
// §12.11.4 c, §11.4, §11.5.1, §12.11.5 c and §12.12.7 of the draft P1788/D9.5 (whose clause
// numbers can differ from the published standard), and from item b.3 of
// `src/_docs/conformance.md`. ulp(m) is 10^-d for the d digits after the point of m
// (§12.11.3), and the value of `m?r` `u` `e k` is 10^k times [m - r ulps, m + r ulps], with
// half an ulp for no r, with m as the lower bound for `u` and as the upper bound for `d`, and
// with -∞ and +∞ in place of m - r ulps and m + r ulps for `??` (§12.11.4 c).
// Without a decoration, it is `com` if it is bounded and `dac` otherwise, as newDec makes it
// (§11.5.1). A decoration has to be `com`, `dac`, `def` or `trv` (§12.11.5 c), and `com` only
// for a bounded interval (§11.4). If a bound of a `com` interval overflows to an infinity,
// the result is `dac` (§12.12.7).
fn uncertain_examples() -> Vec<(&'static str, Want)> {
    use Bound::*;
    use Decoration::*;
    use IntervalErrorKind::*;
    use Want::*;

    let (max, inf, tiny) = (f64::MAX, f64::INFINITY, f64::from_bits(1));
    vec![
        // d = 2: [3.56 - 0.01, 3.56 + 0.01].
        ("3.56?1", Accepted(dec(355, -2), dec(357, -2), Com)),
        // 10^2 times the above, so exact.
        ("3.56?1e2", Accepted(dec(355, 0), dec(357, 0), Com)),
        // Half an ulp, 0.005.
        ("3.56?", Accepted(dec(3555, -3), dec(3565, -3), Com)),
        // d = 0: ulp = 1, so [-10 - 0.5, -10 + 0.5].
        ("-10?", Accepted(dec(-105, -1), dec(-95, -1), Com)),
        ("-10?u", Accepted(dec(-10, 0), dec(-95, -1), Com)),
        // Letters in either case (§12.11.1): [7 - 0.5, 7].
        ("7?D", Accepted(dec(65, -1), dec(7, 0), Com)),
        ("-10?12", Accepted(dec(-22, 0), dec(2, 0), Com)),
        // d = 3: [3.560, 3.560 + 0.002].
        ("3.560?2u", Accepted(dec(3560, -3), dec(3562, -3), Com)),
        // d = 2: [-0.75 - 0.25, -0.75].
        ("-0.75?25d", Accepted(dec(-1, 0), dec(-75, -2), Com)),
        // d = 1: [2.5 - 0.3, 2.5].
        ("2.5?3D", Accepted(dec(22, -1), dec(25, -1), Com)),
        // 10 * [1.5 - 0.5, 1.5 + 0.5].
        ("1.5?5E1", Accepted(dec(10, 0), dec(20, 0), Com)),
        // 10^-1 * [0.5 - 0.05, 0.5 + 0.05].
        ("+.5?e-1", Accepted(dec(45, -3), dec(55, -3), Com)),
        // `12.` has d = 0 (§12.11.3): 10^-2 * [12 - 3, 12 + 3].
        ("12.?3e-002", Accepted(dec(9, -2), dec(15, -2), Com)),
        // The radius 0.
        ("3.56?0", Accepted(dec(356, -2), dec(356, -2), Com)),
        ("-0.125?000e3", Accepted(dec(-125, 0), dec(-125, 0), Com)),
        ("-0.0?0", Accepted(dec(0, 0), dec(0, 0), Com)),
        // 10^-400 * [0.5, 1.5] lies between 0 and 2^-1074 > 4 * 10^-324: rounded outward to
        // [+0, 2^-1074]. Underflow keeps `com`.
        ("1?e-400", Accepted(dec(5, -401), dec(15, -401), Com)),
        // Infinite bounds.
        ("-10??u", Accepted(dec(-10, 0), Inf, Dac)),
        ("-10??", Accepted(Inf, Inf, Dac)),
        ("1.5??De3", Accepted(Inf, dec(1500, 0), Dac)),
        ("5??_trv", Accepted(Inf, Inf, Trv)),
        ("5??u_dac", Accepted(dec(5, 0), Inf, Dac)),
        // Decorations.
        ("3.56?1_com", Accepted(dec(355, -2), dec(357, -2), Com)),
        ("3.56?1_DEF", Accepted(dec(355, -2), dec(357, -2), Def)),
        // Overflow: 10^308 * [1.5, 2.5], above f64::MAX < 1.8 * 10^308 at the top.
        ("2?e308", Accepted(dec(15, 307), dec(25, 307), Dac)),
        ("2?e308_com", Accepted(dec(15, 307), dec(25, 307), Dac)),
        // Only `com` becomes `dac`.
        ("2?e308_def", Accepted(dec(15, 307), dec(25, 307), Def)),
        // 10^308 * [-2, -1.5].
        ("-2?ue308", Accepted(dec(-2, 308), dec(-15, 307), Dac)),
        // 10^2147483647 * [0.5, 1.5], both above f64::MAX.
        ("1?e2147483647", Accepted(Far(max), Far(inf), Dac)),
        // 10^-2147483648 * [4.5, 5.5], both between 0 and 2^-1074.
        ("5?e-2147483648", Accepted(Far(0.0), Far(tiny), Com)),
        ("-5?e-2147483648", Accepted(Far(-tiny), Far(-0.0), Com)),
        // k - d = -2147483648 fits an `i32`: 10^-2147483647 * [0.45, 0.55].
        ("0.5?e-2147483647", Accepted(Far(0.0), Far(tiny), Com)),
        // Item b.3 of `src/_docs/conformance.md`: an exponent that does not fit an `i32`, or
        // k - d that does not (this test's reading of "impractically many digits after the
        // decimal point").
        ("0.5?e-2147483648", Rejected(PossiblyUndefinedOperation)),
        ("1?e2147483648", Rejected(PossiblyUndefinedOperation)),
        ("1?e-2147483649", Rejected(PossiblyUndefinedOperation)),
        ("1?e2147483648_dac", Rejected(PossiblyUndefinedOperation)),
        // `com` for an unbounded interval (§11.4), and `ill` (§12.11.5 c).
        ("5??_com", Rejected(UndefinedOperation)),
        ("5??d_COM", Rejected(UndefinedOperation)),
        ("1?_ill", Rejected(UndefinedOperation)),
    ]
}

#[test]
fn uncertain_oracle_examples() {
    use IntervalErrorKind::*;

    for (s, want) in uncertain_examples() {
        let got = uncertain_oracle(s);
        // `FromStr` of `Interval` and `Interval::_try_from_str_exact` reject every literal
        // with a decoration.
        let has_dec = s.contains('_');
        match want {
            Want::Rejected(kind) => {
                let bare = Err(if has_dec { UndefinedOperation } else { kind });
                assert_eq!(got.bare, bare, "{}", s);
                assert_eq!(got.exact, bare, "{}", s);
                assert_eq!(got.dec, Err(kind), "{}", s);
            }
            Want::Accepted(lo, hi, d) => {
                let (a, b, got_d) = got.dec.unwrap_or_else(|e| panic!("{}: {:?}", s, e));
                let (a_f, b_f) = (f64::from_bits(a), f64::from_bits(b));
                let a_exact = check_bound(s, &lo, a_f, false);
                let b_exact = check_bound(s, &hi, b_f, true);
                assert_eq!(got_d, d, "{}", s);
                let undefined = Err(UndefinedOperation);
                let x = if has_dec { undefined } else { Ok((a, b)) };
                assert_eq!(got.bare, x, "{}", s);
                // `_try_from_str_exact` also rejects a literal with an inexact bound.
                let exact = if a_exact && b_exact { x } else { undefined };
                assert_eq!(got.exact, exact, "{}", s);
            }
        }
    }
}

#[test]
fn uncertain_examples_end_to_end() {
    // The parsers against `uncertain_oracle`, on the literals of `uncertain_examples()`, which
    // `uncertain_oracle_examples` checks the oracle on.
    let mut report = Vec::new();
    for (s, _) in uncertain_examples() {
        check_uncertain(s, &mut report);
    }
    assert!(report.is_empty(), "{}", report.join("\n"));
}

#[test]
fn signs_of_zero() {
    let tiny = f64::from_bits(1);
    // A negative number above -2^-1074 rounds up to -0, as MPFR rounds it, and a positive one
    // below 2^-1074 rounds down to +0.
    for s in [
        "-0x1p-1075",
        "-0x1p-1200",
        "-0x1.fffffffffffffffp-1075",
        "-1e-400",
        "-1/2",
        "-1e-2147483648",
        "-0x1p-2147483648",
    ] {
        let s = if s == "-1/2" {
            // -2^-1075 as `p/q`.
            format!("-1/{}", Integer::from(1) << 1075)
        } else {
            s.to_owned()
        };
        let (x, c) = (grammar_rat(&s), literal_case(&s));
        let up = (0x8000_0000_0000_0000, true, false);
        let down = ((-tiny).to_bits(), true, false);
        assert_eq!(ours(&x, InfSup::Sup), up, "{}", s);
        assert_eq!(oracle(&c, InfSup::Sup), up, "{}", s);
        assert_eq!(ours(&x, InfSup::Inf), down, "{}", s);
        assert_eq!(oracle(&c, InfSup::Inf), down, "{}", s);
        let (x, c) = (grammar_rat(&s[1..]), literal_case(&s[1..]));
        let up = (tiny.to_bits(), true, false);
        let down = (0, true, false);
        assert_eq!(ours(&x, InfSup::Sup), up, "{}", s);
        assert_eq!(oracle(&c, InfSup::Sup), up, "{}", s);
        assert_eq!(ours(&x, InfSup::Inf), down, "{}", s);
        assert_eq!(oracle(&c, InfSup::Inf), down, "{}", s);
    }
    // 0 is +0 and exact, as `mpfr_set_q` makes it, also when the literal has a minus sign.
    for s in [
        "-0",
        "-0e-2147483648",
        "-0x0p2147483647",
        "-0/7",
        "0",
        "+0.0",
    ] {
        let (x, c) = (grammar_rat(s), literal_case(s));
        for infsup in BOTH {
            assert_eq!(ours(&x, infsup), (0, false, false), "{}", s);
            assert_eq!(oracle(&c, infsup), (0, false, false), "{}", s);
        }
    }
}

#[test]
fn edges() {
    // The edges of the range of `f64` and their neighbours, in both directions, against
    // MPFR, as decimal, hexadecimal and `p/q` literals.
    let mut report = Vec::new();
    let max = (1u64 << 53) - 1;
    for (m, e) in [
        (max, 971i64),
        (1, 1024),
        ((1 << 54) - 1, 970),
        ((1 << 53) + 1, 971),
        (1, -1074),
        (1, -1075),
        (3, -1076),
        (1, -1076),
        (1, -1022),
        ((1 << 52) - 1, -1074),
        ((1 << 53) - 1, -1075),
        ((1 << 53) + 1, -1075),
        (1, 0),
        ((1 << 54) + 1, -54),
        ((1 << 54) - 1, -54),
    ] {
        for sign in ["", "-"] {
            let n = Integer::from(m);
            let p = Integer::from(1) << e.unsigned_abs() as u32;
            let (d, k) = decimal_of(n.clone(), e);
            for s in [
                format!("{}0x{:x}p{}", sign, m, e),
                format!("{}{}e{}", sign, d, k),
                if e >= 0 {
                    format!("{}{}/1", sign, n * p)
                } else {
                    format!("{}{}/{}", sign, n, p)
                },
            ] {
                check_literal(&s, &mut report);
            }
        }
    }
    assert!(report.is_empty(), "{}", report.join("\n"));
}
