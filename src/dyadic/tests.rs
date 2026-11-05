// Tests of the dyadic kernel. With `gmp`, each operation is compared with MPFR through `rug` at
// the same precision, where it has to give the same number, and Ziv's strategy with MPFR's
// rounding of the same real number to an `f64`. Without it, the tests check identities that
// hold exactly, and roundings to `f64` that are known.

use super::*;

pub(super) struct Rng(u64);

impl Rng {
    // SplitMix64.
    pub(super) fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    pub(super) fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    // A limb that is often 0, 1, 2^63 or all ones, to make carries and borrows run across
    // limbs.
    fn limb(&mut self) -> u64 {
        match self.below(8) {
            0 => 0,
            1 => 1,
            2 => 1 << 63,
            3 | 4 => u64::MAX,
            _ => self.next(),
        }
    }

    // The mantissa of a nonzero `Dyadic<N>`.
    fn mantissa<const N: usize>(&mut self) -> [u64; N] {
        let mut m = [0; N];
        for l in &mut m {
            *l = self.limb();
        }
        m[N - 1] |= 1 << 63;
        m
    }

    // A `Dyadic<N>`, sometimes 0, with an exponent in [-e, e].
    pub(super) fn dyadic<const N: usize>(&mut self, e: i64) -> Dyadic<N> {
        if self.below(16) == 0 {
            return Dyadic::ZERO;
        }
        let m = self.mantissa();
        let neg = self.below(2) == 0;
        let exp = self.below(2 * e as u64 + 1) as i64 - e;
        Dyadic { neg, exp, m }
    }

    // A `Dyadic<N>`, sometimes 0, whose square is exact at p bits: the low 32 N bits of its
    // mantissa are 0.
    fn root<const N: usize>(&mut self) -> Dyadic<N> {
        let mut x = self.dyadic::<N>(300);
        for l in &mut x.m[..N / 2] {
            *l = 0;
        }
        if N % 2 == 1 {
            x.m[N / 2] &= u64::MAX << 32;
        }
        x
    }
}

// The number of random cases, which can be set with `INARI_DYADIC_N`. There are fewer at the
// higher precisions, where each costs more.
pub(super) fn n_cases<const N: usize>() -> u64 {
    let n = std::env::var("INARI_DYADIC_N")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(if cfg!(debug_assertions) { 300 } else { 3_000 });
    n * 8 / (N as u64 + 7)
}

// `x` is normalized.
pub(super) fn check_normal<const N: usize>(x: &Dyadic<N>) {
    if x.is_zero() {
        assert_eq!(*x, Dyadic::ZERO, "not normalized: {:?}", x);
    } else {
        assert!(x.m[N - 1] >> 63 == 1, "not normalized: {:?}", x);
    }
}

// Toy evaluations for Ziv's strategy, built from the operations on enclosures alone.

// sqrt(x), for x >= 0.
struct Sqrt(f64);

impl Eval for Sqrt {
    fn eval<const N: usize>(&self) -> Encl<N> {
        Encl::point(self.0).sqrt()
    }
}

// x / 3 + y.
struct ThirdPlus(f64, f64);

impl Eval for ThirdPlus {
    fn eval<const N: usize>(&self) -> Encl<N> {
        Encl::point(self.0).div_u64(3).add(&Encl::point(self.1))
    }
}

// e^-x for 0 < x <= 1, by the series of (-x)^k / k!. Its terms decrease in magnitude and
// alternate in sign, so the sum of the terms not added is between -t and t for the first of
// them, t. The sum stops at a term below 2^-(p + 8).
struct ExpNeg(f64);

impl Eval for ExpNeg {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let x = Encl::point(self.0);
        let small = Dyadic::from_f64(1.0).shl(-64 * N as i64 - 8);
        let mut sum = Encl::point(1.0);
        let mut term = sum;
        let mut k = 1;
        loop {
            // x^k / k!
            term = term.mul(&x).div_u64(k);
            if term.hi <= small {
                return sum.add(&Encl {
                    lo: term.hi.neg(),
                    hi: term.hi,
                });
            }
            sum = if k % 2 == 1 {
                sum.sub(&term)
            } else {
                sum.add(&term)
            };
            k += 1;
        }
    }
}

// f * 2^k.
struct Scaled<E>(E, i64);

impl<E: Eval> Eval for Scaled<E> {
    fn eval<const N: usize>(&self) -> Encl<N> {
        self.0.eval::<N>().shl(self.1)
    }
}

// -f.
struct Neg<E>(E);

impl<E: Eval> Eval for Neg<E> {
    fn eval<const N: usize>(&self) -> Encl<N> {
        self.0.eval::<N>().neg()
    }
}

// An enclosure that never narrows: [0, 1], from 1 - 1 + [0, 1].
struct Wide;

impl Eval for Wide {
    fn eval<const N: usize>(&self) -> Encl<N> {
        Encl::point(1.0).sub(&Encl::point(1.0)).add(&Encl {
            lo: Dyadic::ZERO,
            hi: Dyadic::from_f64(1.0),
        })
    }
}

// `ziv_at::<N>`, which either fails or gives `want`, and whether it passed.
fn passes_at<const N: usize, E: Eval>(f: &E, up: bool, want: f64) -> bool {
    match ziv_at::<N, E>(f, up) {
        None => false,
        Some(x) => {
            // `==`, as the sign of a zero is free.
            assert!(x == want, "{} at {} limbs: {} != {}", up, N, x, want);
            true
        }
    }
}

// Ziv's strategy on `f` gives `want` from each start, and each level either fails or gives
// `want`. Returns the levels that pass.
fn check_ziv<E: Eval>(f: &E, up: bool, want: f64) -> Vec<usize> {
    let mut levels = Vec::new();
    for start in [1, 2, 4, 8, 16, 32, 64] {
        let x = ziv(f, up, start);
        assert!(x == want, "{} from {} limbs: {} != {}", up, start, x, want);
    }
    macro_rules! levels {
        ($($n:literal),*) => {
            $(
                if passes_at::<$n, E>(f, up, want) {
                    levels.push($n);
                }
            )*
        };
    }
    levels!(1, 2, 4, 8, 16, 32, 64);
    levels
}

#[cfg(feature = "gmp")]
mod mpfr {
    use super::*;
    use rug::{float::Round, integer::Order, Float, Integer};

    // The value of `x` at its precision, which holds it exactly.
    fn float<const N: usize>(x: &Dyadic<N>) -> Float {
        let mut f = Float::with_val(64 * N as u32, Integer::from_digits(&x.m, Order::Lsf));
        if x.neg {
            f = -f;
        }
        f <<= i32::try_from(x.exp).unwrap();
        f
    }

    fn rnd(up: bool) -> Round {
        if up {
            Round::Up
        } else {
            Round::Down
        }
    }

    // `x` is normalized and is `y`, which MPFR rounded at the precision of `x`.
    fn check<const N: usize>(x: &Dyadic<N>, y: &Float, what: &str) {
        check_normal(x);
        assert_eq!(float(x), *y, "{}: {:?}", what, x);
    }

    // `x` rounds to an `f64` as MPFR rounds it.
    fn check_to_f64<const N: usize>(x: &Dyadic<N>, up: bool) {
        let want = float(x).to_f64_round(rnd(up));
        assert_eq!(x.to_f64(up).to_bits(), want.to_bits(), "{:?} {}", x, up);
    }

    // Every operation on `a`, `b` and `k`, in both directions.
    fn check_case<const N: usize>(a: &Dyadic<N>, b: &Dyadic<N>, k: u64) {
        let p = 64 * N as u32;
        let (fa, fb) = (float(a), float(b));
        for up in [false, true] {
            let r = rnd(up);
            let what = format!("{:?} {:?} {} {}", a, b, k, up);
            check(
                &a.add(b, up),
                &Float::with_val_round(p, &fa + &fb, r).0,
                &what,
            );
            check(
                &a.sub(b, up),
                &Float::with_val_round(p, &fa - &fb, r).0,
                &what,
            );
            check(
                &a.mul(b, up),
                &Float::with_val_round(p, &fa * &fb, r).0,
                &what,
            );
            check(
                &a.mul_u64(k, up),
                &Float::with_val_round(p, &fa * Integer::from(k), r).0,
                &what,
            );
            check(
                &a.div_u64(k, up),
                &Float::with_val_round(p, &fa / Integer::from(k), r).0,
                &what,
            );
            if !b.is_zero() {
                check(
                    &a.div(b, up),
                    &Float::with_val_round(p, &fa / &fb, r).0,
                    &what,
                );
            }
            for x in [a, b] {
                let x = Dyadic { neg: false, ..*x };
                check(
                    &x.sqrt(up),
                    &Float::with_val_round(p, float(&x).sqrt_ref(), r).0,
                    &what,
                );
            }
            check_to_f64(a, up);
            check_to_f64(b, up);
        }
        assert_eq!(a.cmp(b), fa.partial_cmp(&fb).unwrap(), "{:?} {:?}", a, b);
    }

    // Two numbers whose sum cancels most of its bits: `b = -a` with its low limbs replaced, or,
    // across a power of two, |a| = 2^(p - 1) + low limbs and
    // |b| = (2^p - 2^(64 j) + low limbs) / 2.
    fn cancelling<const N: usize>(rng: &mut Rng) -> (Dyadic<N>, Dyadic<N>) {
        let j = rng.below(N as u64 + 1) as usize;
        let mut a = Dyadic {
            neg: rng.below(2) == 0,
            exp: rng.below(9) as i64 - 4,
            m: rng.mantissa(),
        };
        let mut b = Dyadic { neg: !a.neg, ..a };
        if rng.below(2) == 0 {
            for l in &mut b.m[..j] {
                *l = rng.limb();
            }
        } else {
            a.m[j..].fill(0);
            b.m[j..].fill(u64::MAX);
            b.exp -= 1;
        }
        a.m[N - 1] |= 1 << 63;
        b.m[N - 1] |= 1 << 63;
        (a, b)
    }

    fn ops<const N: usize>(rng: &mut Rng) {
        let p = 64 * N as i64;
        for _ in 0..n_cases::<N>() {
            let (a, b): (Dyadic<N>, _) = match rng.below(4) {
                0 => (rng.dyadic(4), rng.dyadic(4)),
                1 => (rng.dyadic(300), rng.dyadic(300)),
                // Exponents often further apart than p, where all of the smaller number is
                // below the last bit of the result.
                2 => (rng.dyadic(3 * p), rng.dyadic(3 * p)),
                _ => cancelling(rng),
            };
            let k = match rng.below(4) {
                0 => 1,
                1 => u64::MAX,
                _ => rng.next() | 1,
            };
            check_case(&a, &b, k);
            // A perfect square, and its neighbor that differs in the last bit.
            let x = rng.root::<N>();
            let xx = x.mul(&x, false);
            assert_eq!(xx, x.mul(&x, true), "{:?}", x);
            let abs = Dyadic { neg: false, ..x };
            for up in [false, true] {
                assert_eq!(xx.sqrt(up), abs, "{:?}", x);
            }
            if !xx.is_zero() {
                let mut y = xx;
                y.m[0] ^= 1;
                check_case(&xx, &y, k);
            }
            // Rounding to `f64` near the ends of its range: |f| < 2^1200.
            if !a.is_zero() {
                let f = Dyadic {
                    exp: rng.below(2400) as i64 - 1200 - p,
                    ..a
                };
                check_to_f64(&f, false);
                check_to_f64(&f, true);
            }
        }
    }

    #[test]
    fn ops_against_mpfr() {
        ops::<1>(&mut Rng(1));
        ops::<2>(&mut Rng(2));
        ops::<3>(&mut Rng(3));
        ops::<4>(&mut Rng(4));
        ops::<8>(&mut Rng(8));
        ops::<16>(&mut Rng(16));
        ops::<32>(&mut Rng(32));
        ops::<64>(&mut Rng(64));
    }

    // A number as `(neg, exp, m)`.
    type Number = (bool, i64, &'static [u64]);

    // Operands on which an operation and MPFR differed, as `(N, a, b, k)`, each with what it
    // broke and where it was found. `check_case` runs every operation on them, in both
    // directions.
    fn regressions() -> Vec<(usize, [Number; 2], u64)> {
        vec![]
    }

    fn dyadic<const N: usize>((neg, exp, m): Number) -> Dyadic<N> {
        Dyadic {
            neg,
            exp,
            m: m.try_into().unwrap(),
        }
    }

    #[test]
    fn regressions_against_mpfr() {
        for (n, [a, b], k) in regressions() {
            match n {
                1 => check_case::<1>(&dyadic(a), &dyadic(b), k),
                2 => check_case::<2>(&dyadic(a), &dyadic(b), k),
                3 => check_case::<3>(&dyadic(a), &dyadic(b), k),
                4 => check_case::<4>(&dyadic(a), &dyadic(b), k),
                8 => check_case::<8>(&dyadic(a), &dyadic(b), k),
                16 => check_case::<16>(&dyadic(a), &dyadic(b), k),
                32 => check_case::<32>(&dyadic(a), &dyadic(b), k),
                64 => check_case::<64>(&dyadic(a), &dyadic(b), k),
                _ => panic!("no test at {} limbs", n),
            }
        }
    }

    // MPFR's precision for the numbers that the toy evaluations enclose, above that of the
    // last level. Rounding a number toward ±∞ at it, and then to an `f64` in the same
    // direction, rounds it to an `f64` in that direction, as each `f64` is a number at it.
    const PREC: u32 = 8192;

    // The value of each toy evaluation, rounded by MPFR at the precision `prec` in the
    // direction `r`.
    trait Value {
        fn value(&self, prec: u32, r: Round) -> Float;
    }

    impl Value for Sqrt {
        fn value(&self, prec: u32, r: Round) -> Float {
            Float::with_val_round(prec, Float::with_val(53, self.0).sqrt_ref(), r).0
        }
    }

    impl Value for ThirdPlus {
        fn value(&self, prec: u32, r: Round) -> Float {
            // x + 3 y is exact at 2,200 bits, as x and y are multiples of 2^-1074 below
            // 2^1024.
            let mut s = Float::with_val(2200, self.1);
            s *= 3;
            s += self.0;
            Float::with_val_round(prec, &s / 3u32, r).0
        }
    }

    impl Value for ExpNeg {
        fn value(&self, prec: u32, r: Round) -> Float {
            Float::with_val_round(prec, Float::with_val(53, -self.0).exp_ref(), r).0
        }
    }

    impl<E: Value> Value for Scaled<E> {
        fn value(&self, prec: u32, r: Round) -> Float {
            self.0.value(prec, r) << i32::try_from(self.1).unwrap()
        }
    }

    impl<E: Value> Value for Neg<E> {
        fn value(&self, prec: u32, r: Round) -> Float {
            let r = if r == Round::Up {
                Round::Down
            } else {
                Round::Up
            };
            -self.0.value(prec, r)
        }
    }

    // The enclosure of `f` at `N` limbs holds its value. If `single`, which says that it is
    // the value rounded once in each direction, its bounds are MPFR's roundings at p bits.
    fn check_level<const N: usize, E: Eval + Value>(f: &E, single: bool, what: &str) {
        let x = f.eval::<N>();
        check_normal(&x.lo);
        check_normal(&x.hi);
        assert!(
            float(&x.lo) <= f.value(PREC, Round::Down),
            "{} {:?}",
            what,
            x
        );
        assert!(f.value(PREC, Round::Up) <= float(&x.hi), "{} {:?}", what, x);
        if single {
            let p = 64 * N as u32;
            check(&x.lo, &f.value(p, Round::Down), what);
            check(&x.hi, &f.value(p, Round::Up), what);
        }
    }

    // Ziv's strategy on `f` gives MPFR's rounding of its value, each level's enclosure holds
    // the value, and Ziv's strategy first passes at `first[0]` limbs rounding toward -∞ and at
    // `first[1]` limbs rounding toward +∞.
    fn check_eval<E: Eval + Value>(f: &E, single: bool, first: [usize; 2], what: &str) {
        for up in [false, true] {
            let r = rnd(up);
            let want = f.value(PREC, r).to_f64_round(r);
            let levels = check_ziv(f, up, want);
            assert_eq!(
                levels.first(),
                Some(&first[usize::from(up)]),
                "{} {}: {:?}",
                what,
                up,
                levels
            );
        }
        check_level::<1, E>(f, single, what);
        check_level::<2, E>(f, single, what);
        check_level::<4, E>(f, single, what);
        check_level::<8, E>(f, single, what);
        check_level::<16, E>(f, single, what);
        check_level::<32, E>(f, single, what);
        check_level::<64, E>(f, single, what);
    }

    #[test]
    fn ziv_against_mpfr() {
        let tiny = 5e-324;
        // Ordinary numbers.
        check_eval(&Sqrt(2.0), true, [1, 1], "sqrt(2)");
        check_eval(&Sqrt(0.1), true, [1, 1], "sqrt(0.1)");
        check_eval(&Sqrt(tiny), true, [1, 1], "sqrt(MIN)");
        check_eval(&Sqrt(f64::MAX), true, [1, 1], "sqrt(MAX)");
        check_eval(&ThirdPlus(1.0, 0.1), false, [1, 1], "1 / 3 + 0.1");
        check_eval(&ExpNeg(0.5), false, [1, 1], "e^-0.5");
        check_eval(&ExpNeg(1.0), false, [1, 1], "e^-1");
        // At the ends of the range of `f64`: subnormal numbers, numbers below the least of
        // them, MAX, and beyond MAX.
        for k in [-1022, -1074, -1075, -1080, -2000, 1023, 1024, 2000] {
            let what = format!("sqrt(2) * 2^{}", k);
            check_eval(&Scaled(Sqrt(2.0), k), true, [1, 1], &what);
            check_eval(&Neg(Scaled(Sqrt(2.0), k)), true, [1, 1], &what);
        }
        check_eval(&ThirdPlus(tiny, 0.0), false, [1, 1], "MIN / 3");
        check_eval(
            &ThirdPlus(7.0 * tiny, -tiny),
            false,
            [1, 1],
            "7 MIN / 3 - MIN",
        );
        check_eval(
            &ThirdPlus(f64::MAX, f64::MAX),
            false,
            [1, 1],
            "MAX / 3 + MAX",
        );
        // Numbers just beside an `f64`, whose enclosures hold it in one direction until the
        // precision is high enough: 1 + 2^-200 at 256 bits, 1e300 - 2.5 / 3 at 1,024 bits,
        // and MAX + 2^-1000 / 3 and MAX + 1 / 3 at 2,048 bits.
        let f = ThirdPlus(3.0 * 2f64.powi(-200), 1.0);
        check_eval(&f, false, [1, 4], "1 + 2^-200");
        check_eval(&ThirdPlus(-2.5, 1e300), false, [16, 1], "-2.5 / 3 + 1e300");
        let f = ThirdPlus(2f64.powi(-1000), f64::MAX);
        check_eval(&f, false, [1, 32], "MAX + 2^-1000 / 3");
        let f = Neg(ThirdPlus(1.0, f64::MAX));
        check_eval(&f, false, [32, 1], "-(1 / 3 + MAX)");
    }

    // hi - lo, exactly.
    fn width<const N: usize>(x: &Encl<N>) -> Float {
        // Both bounds are multiples of 2^e, for the lower exponent e of the nonzero ones, and
        // below 2^(e + d + p) for the difference d of their exponents, so that their difference
        // fits in d + p + 1 bits.
        let d = if x.lo.is_zero() || x.hi.is_zero() {
            0
        } else {
            x.lo.exp.abs_diff(x.hi.exp)
        };
        let prec = 64 * N as u32 + u32::try_from(d).unwrap() + 1;
        let (w, o) = Float::with_val_round(prec, &float(&x.hi) - &float(&x.lo), Round::Down);
        assert_eq!(o, std::cmp::Ordering::Equal);
        w
    }

    fn widths<E: Eval>(f: &E) -> [Float; 7] {
        [
            width(&f.eval::<1>()),
            width(&f.eval::<2>()),
            width(&f.eval::<4>()),
            width(&f.eval::<8>()),
            width(&f.eval::<16>()),
            width(&f.eval::<32>()),
            width(&f.eval::<64>()),
        ]
    }

    // Each doubling of the precision at least halves the width of the enclosures.
    #[test]
    fn width_halves() {
        for (what, w) in [
            ("sqrt(2)", widths(&Sqrt(2.0))),
            ("sqrt(0.1)", widths(&Sqrt(0.1))),
            ("1 / 3 + 0.1", widths(&ThirdPlus(1.0, 0.1))),
            ("MAX / 3 + MAX", widths(&ThirdPlus(f64::MAX, f64::MAX))),
            ("e^-0.5", widths(&ExpNeg(0.5))),
            ("e^-1", widths(&ExpNeg(1.0))),
            ("sqrt(2) * 2^-1080", widths(&Scaled(Sqrt(2.0), -1080))),
        ] {
            assert!(w[0] > 0, "{}", what);
            for i in 1..w.len() {
                assert!(w[i].clone() << 1 <= w[i - 1], "{} at level {}", what, i);
            }
        }
    }

    // The width lemmas of `rocq/theories/DyRound.v` and `rocq/theories/DyDriver.v` on sqrt(x)
    // and x / 3 + y at `N` limbs: `dround_width` for the rounding of a number, RU(r) - RD(r) <=
    // |r| 2^(1 - p), and `encl_add_width` for a sum of enclosures. Each bound is computed
    // rounded up, at p + 64 bits or more, which makes it larger by less than a relative
    // 2^-(p + 62).
    fn width_bounds<const N: usize>(x: f64, y: f64) {
        let p = 64 * N as u32;
        let ulp = 1 - p as i32;
        let w = width(&Encl::<N>::point(x).sqrt());
        let r = Float::with_val_round(p + 64, Float::with_val(53, x).sqrt_ref(), Round::Up).0;
        assert!(w <= r << ulp, "sqrt({}) at {} limbs", x, N);
        let t = Encl::<N>::point(x).div_u64(3);
        let wt = width(&t);
        let r = Float::with_val_round(p + 64, Float::with_val(53, x) / 3u32, Round::Up).0;
        assert!(wt <= r.abs() << ulp, "{} / 3 at {} limbs", x, N);
        let s = t.add(&Encl::point(y));
        assert_eq!(s, ThirdPlus(x, y).eval::<N>());
        // The sums of the bounds of x / 3 and of y are exact at p + 2,300 bits, as both are
        // multiples of 2^(-1076 - p) below 2^1024.
        let prec = p + 2300;
        let y = Float::with_val(53, y);
        let lo = Float::with_val(prec, &float(&t.lo) + &y);
        let hi = Float::with_val(prec, &float(&t.hi) + &y);
        let r = Float::with_val_round(prec, &lo.abs() + &hi.abs(), Round::Up).0 << ulp;
        let bound = Float::with_val_round(prec, &wt + &r, Round::Up).0;
        assert!(width(&s) <= bound, "{} / 3 + {} at {} limbs", x, y, N);
    }

    #[test]
    fn width_within_bounds() {
        for (x, y) in [
            (2.0, 0.1),
            (0.1, -0.1),
            (1.0, -1.0 / 3.0),
            (5e-324, 0.0),
            (f64::MAX, f64::MAX),
        ] {
            width_bounds::<1>(x, y);
            width_bounds::<2>(x, y);
            width_bounds::<4>(x, y);
            width_bounds::<8>(x, y);
            width_bounds::<16>(x, y);
            width_bounds::<32>(x, y);
            width_bounds::<64>(x, y);
        }
    }
}

// Exact identities, which the tests without `gmp` check.
fn identities<const N: usize>(rng: &mut Rng) {
    for _ in 0..n_cases::<N>() {
        let (a, b) = (rng.dyadic::<N>(300), rng.dyadic::<N>(300));
        // down <= up always.
        for (lo, hi) in [
            (a.add(&b, false), a.add(&b, true)),
            (a.mul(&b, false), a.mul(&b, true)),
            (a.mul_u64(3, false), a.mul_u64(3, true)),
            (a.div_u64(3, false), a.div_u64(3, true)),
        ] {
            check_normal(&lo);
            check_normal(&hi);
            assert!(lo <= hi, "{:?} {:?}", a, b);
        }
        let two = Dyadic::<N>::from_f64(2.0);
        assert_eq!(a.mul(&two, false), a.shl(1));
        assert_eq!(a.shl(1).div(&two, true), a);
        // a - a = 0, and the square root of an exact square.
        assert_eq!(a.sub(&a, true), Dyadic::ZERO);
        let x = rng.root::<N>();
        let xx = x.mul(&x, false);
        assert_eq!(xx, x.mul(&x, true), "{:?}", x);
        let abs = Dyadic { neg: false, ..x };
        assert_eq!(xx.sqrt(false), abs);
        assert_eq!(xx.sqrt(true), abs);
    }
}

#[test]
fn exact_identities() {
    identities::<1>(&mut Rng(11));
    identities::<2>(&mut Rng(12));
    identities::<3>(&mut Rng(13));
    identities::<5>(&mut Rng(15));
    identities::<16>(&mut Rng(16));
    identities::<64>(&mut Rng(64));
}

#[test]
fn f64_round_trip() {
    for x in [0.0, -0.0, 1.0, -3.5, f64::MAX, f64::MIN, 5e-324, -2.2e-308] {
        let d = Dyadic::<2>::from_f64(x);
        check_normal(&d);
        assert_eq!(d.to_f64(false), x);
        assert_eq!(d.to_f64(true), x);
    }
}

// sqrt(2) + 1/3.
struct Sqrt2Third;

impl Eval for Sqrt2Third {
    fn eval<const N: usize>(&self) -> Encl<N> {
        let third = Encl::point(1.0).div_u64(3);
        Encl::point(2.0).sqrt().add(&third)
    }
}

#[test]
fn ziv_rounds() {
    let (lo, hi) = (ziv(&Sqrt2Third, false, 1), ziv(&Sqrt2Third, true, 2));
    assert_eq!(f64::from_bits(lo.to_bits() + 1), hi);
    assert!(lo < 2f64.sqrt() + 1.0 / 3.0 + 1e-15);
    assert_eq!(ziv_at::<64, _>(&Sqrt2Third, true), Some(hi));
    // e^-0.5 is not an `f64`, so its roundings are neighbors, and the `f64` nearest to it is
    // one of them.
    let (lo, hi) = (ziv(&ExpNeg(0.5), false, 1), ziv(&ExpNeg(0.5), true, 1));
    assert_eq!(f64::from_bits(lo.to_bits() + 1), hi);
    assert!([lo, hi].contains(&(-0.5f64).exp()));
    let e = Encl::<2>::point(-1.5);
    let e = e.mul(&e.neg()).div(&e).shl(-1).mul_u64(4);
    assert_eq!((e.lo.to_f64(false), e.hi.to_f64(true)), (3.0, 3.0));
    assert_eq!(e.hi.max(e.lo).min(e.lo), e.lo);
}

// Roundings to `f64` that are known without MPFR, among them at the ends of its range.
#[test]
fn ziv_known_roundings() {
    let min = 5e-324;
    // 1 + 2^-200, whose enclosures hold 1 until 256 bits, where the sum is exact. Rounding
    // toward -∞ gives 1 from any of them.
    let f = ThirdPlus(3.0 * 2f64.powi(-200), 1.0);
    assert_eq!(check_ziv(&f, false, 1.0), [1, 2, 4, 8, 16, 32, 64]);
    assert_eq!(check_ziv(&f, true, 1.0 + f64::EPSILON), [4, 8, 16, 32, 64]);
    for up in [false, true] {
        assert_eq!(check_ziv(&Sqrt(4.0), up, 2.0), [1, 2, 4, 8, 16, 32, 64]);
    }
    let f = Scaled(Sqrt(2.0), -1074);
    check_ziv(&f, false, min);
    check_ziv(&f, true, 2.0 * min);
    let f = Scaled(Sqrt(2.0), -1080);
    check_ziv(&f, false, 0.0);
    check_ziv(&f, true, min);
    let f = Neg(Scaled(Sqrt(2.0), -1080));
    check_ziv(&f, false, -min);
    assert!(ziv(&f, true, 1).is_sign_negative());
    let f = Scaled(Sqrt(2.0), 1024);
    check_ziv(&f, false, f64::MAX);
    check_ziv(&f, true, f64::INFINITY);
    let f = Neg(Scaled(Sqrt(2.0), 1024));
    check_ziv(&f, false, f64::NEG_INFINITY);
    check_ziv(&f, true, f64::MIN);
}

#[test]
#[should_panic(expected = "the working precision reached its cap of 4096 bits")]
fn ziv_panics_at_the_cap() {
    ziv(&Wide, true, 1);
}
