// Tests of the powers of the dyadic kernel next to `f64`s whose powers are known: x next to a
// power of 2 with an integer y or n, and y = ±1/2 at the square of an `f64` and the `f64`s
// next to it, through `check_pow` and `check_pown` of `tests.rs`.
//
// Where the binomial series or a bound on a square root gives the roundings of a result, the
// tests also assert them with `check_rounding`, so that they check results in both feature
// sets, not only against MPFR. Below, u = 2^-52 and h = 2^-53 are the gaps between the `f64`s
// in [1, 2) and in [1/2, 1).

use super::*;

// v 2^s for a normal v > 0, if it is normal, from the bits of v: then it is exact.
fn times_pow2(v: f64, s: i64) -> Option<f64> {
    let be = i64::try_from(v.to_bits() >> 52).unwrap() + s;
    if (1..=2046).contains(&be) {
        let f = v.to_bits() & ((1 << 52) - 1);
        Some(f64::from_bits(f | u64::try_from(be).unwrap() << 52))
    } else {
        None
    }
}

// The roundings toward -∞ and toward +∞ of (1 + u)^y if `above`, and of (1 - h)^y otherwise,
// for an integer y != 0, where the binomial series gives them. Each `f64` operation here is
// exact: the products are integers below 2^28 times u or h, and the sums are multiples of u in
// [1, 2) or of h in [1/2, 1).
fn series(above: bool, y: i64) -> Option<(f64, f64)> {
    let (u, h) = (f64::EPSILON, f64::EPSILON / 2.0);
    let n = y.abs() as f64;
    if y == 1 {
        let x = if above { 1.0 + u } else { 1.0 - h };
        return Some((x, x));
    }
    match (above, y > 0) {
        // (1 + u)^n = 1 + nu + T with T = sum over k >= 2 of C(n, k) u^k. T > 0 for n >= 2,
        // and the term of k + 1 is that of k times (n - k) u / (k + 1) < 2^-26, so that
        // T < C(n, 2) u^2 (1 + 2^-25) < n^2 2^-105 (1 + 2^-25) <= 2^-53 (1 + 2^-25) < u for
        // n <= 2^26: x^n lies strictly between 1 + nu and 1 + (n + 1)u, in [1, 2).
        (true, true) if y <= 1 << 26 => Some((1.0 + n * u, 1.0 + (n + 1.0) * u)),
        // (1 + u)^-n = 1 - nu + T with T = sum over k >= 2 of (-1)^k C(n + k - 1, k) u^k,
        // whose terms fall by (n + k) u / (k + 1) < 1, so that 0 < T < C(n + 1, 2) u^2 =
        // n (n + 1) 2^-105 < h for n (n + 1) < 2^52: x^-n lies strictly between 1 - 2nh and
        // 1 - (2n - 1)h, in [1/2, 1).
        (true, false) if -y < 1 << 26 => Some((1.0 - 2.0 * n * h, 1.0 - (2.0 * n - 1.0) * h)),
        // (1 - h)^n = 1 - nh + T with T = sum over k >= 2 of (-1)^k C(n, k) h^k, whose terms
        // fall by (n - k) h / (k + 1) < 1, so that 0 < T <= C(n, 2) h^2 = n (n - 1) 2^-107 < h
        // for n (n - 1) < 2^54, which holds for n <= 2^27: x^n lies strictly between 1 - nh
        // and 1 - (n - 1)h, in [1/2, 1).
        (false, true) if y <= 1 << 27 => Some((1.0 - n * h, 1.0 - (n - 1.0) * h)),
        // (1 - h)^-n = 1 + nh + T with T = sum over k >= 2 of C(n + k - 1, k) h^k > 0, whose
        // terms fall by (n + k) h / (k + 1) < 2^-27, so that T < C(n + 1, 2) h^2 (1 + 2^-26) =
        // n (n + 1) 2^-107 (1 + 2^-26) <= 2^-55 (1 + 2^-26)^2 < h for n <= 2^26. For an even n,
        // 1 + nh is the `f64` 1 + (n / 2)u; for an odd n, it is the midpoint between 1 +
        // floor(n / 2)u and the `f64` after it. Either way x^-n lies strictly between
        // 1 + floor(n / 2)u and the next `f64`, 1 + (floor(n / 2) + 1)u, in [1, 2).
        (false, false) if -y <= 1 << 26 => {
            let d = 1.0 + (n / 2.0).floor() * u;
            Some((d, d + u))
        }
        _ => None,
    }
}

// Checks that `lo` and `hi` are `want` = (d, u): the roundings of a result toward -∞ and +∞.
fn check_bounds(what: &str, lo: f64, hi: f64, (d, u): (f64, f64)) {
    check_rounding(what, lo, hi, "D", d);
    check_rounding(what, lo, hi, "U", u);
}

// Checks x^y with `check_pow`, and x^n and (-x)^n with `check_pown` for n = y if y is an
// `i32`. Where `want` gives the roundings of x^y, it asserts them, for x^y and x^n, and for
// (-x)^n, which is x^n for an even n, and -(x^n) for an odd n, whose roundings are those of x^n
// negated and swapped.
fn check_near(x: f64, y: i64, want: Option<(f64, f64)>) {
    // |y| <= 2^52 + 1, so that y is an `f64`.
    let yf = y as f64;
    check_pow(x, yf);
    if let Some(want) = want {
        let what = format!("pow({:e}, {:e})", x, yf);
        check_bounds(&what, pow(x, yf, false), pow(x, yf, true), want);
    }
    if let Ok(n) = i32::try_from(y) {
        check_pown(x, n);
        check_pown(-x, n);
        if let Some((d, u)) = want {
            let what = format!("pown({:e}, {})", x, n);
            check_bounds(&what, pown(x, n, false), pown(x, n, true), (d, u));
            let neg = if n % 2 == 0 { (d, u) } else { (-u, -d) };
            let what = format!("pown({:e}, {})", -x, n);
            check_bounds(&what, pown(-x, n, false), pown(-x, n, true), neg);
        }
    }
}

// x = next_up(2^e) = 2^e (1 + u) for e in [-1022, 1023], and x = next_down(2^e) = 2^e (1 - h)
// for e in [-1021, 1024], with an integer y = ±n for n in [1, 40] and 2^j - 1, 2^j and 2^j + 1
// for j in [6, 52], also as pown for an n that is an `i32`. e takes every value for n <= 40, and
// otherwise some fixed values and those next to q / y for q in {1023, -1022, -1074}, where x^y
// crosses 2^1024, 2^-1022 and 2^-1074. x^y = 2^(e y) (1 + u)^y or 2^(e y) (1 - h)^y, and where
// `series` gives the roundings of the second factor, those of x^y are them times 2^(e y), where
// these are normal: the scaling then keeps them adjacent `f64`s (or equal, for y = 1).
#[test]
fn next_to_powers_of_two() {
    let mut ns: Vec<i64> = (1..=40).collect();
    for j in 6..=52 {
        ns.extend([(1 << j) - 1, 1 << j, (1 << j) + 1]);
    }
    for above in [true, false] {
        let (first, last) = if above { (-1022, 1023) } else { (-1021, 1024) };
        for &n in &ns {
            for y in [n, -n] {
                let mut es = vec![
                    first,
                    first + 1,
                    -1000,
                    -512,
                    -511,
                    -100,
                    -2,
                    -1,
                    0,
                    1,
                    2,
                    100,
                    511,
                    512,
                    1000,
                    last - 1,
                    last,
                ];
                for q in [1023, -1022, -1074] {
                    let t = i64::div_euclid(q, y);
                    es.extend(t - 1..=t + 2);
                }
                if n <= 40 {
                    es.extend(first..=last);
                }
                es.retain(|e| (first..=last).contains(e));
                es.sort_unstable();
                es.dedup();
                for e in es {
                    // The bits of 2^e, which are those of +∞ for e = 1024, and the `f64` next
                    // to it from its bits.
                    let bits = u64::try_from(e + 1023).unwrap() << 52;
                    let x = f64::from_bits(if above { bits + 1 } else { bits - 1 });
                    let s = e * y;
                    let want =
                        series(above, y).and_then(|(d, u)| times_pow2(d, s).zip(times_pow2(u, s)));
                    check_near(x, y, want);
                }
            }
        }
    }
}

// Checks x^y with `check_pow`, and asserts its roundings with `check_rounding(.., rnd, want)`.
fn check_root(x: f64, y: f64, rnd: &str, want: f64) {
    check_pow(x, y);
    let what = format!("pow({:e}, {:e})", x, y);
    check_rounding(&what, pow(x, y, false), pow(x, y, true), rnd, want);
}

// x^(1/2) and x^(-1/2) at x = r^2 and the `f64`s next to it, for r = m 2^j with an odd m,
// m^2 < 2^53 and 2^g <= r < 2^(g + 1): m in [1, 15], 99, 255, 4097, 2^26 ± 1, 94906265 (the
// greatest odd m with m^2 < 2^53) and some random odd m below it, at each g in {-510, -100, -1,
// 0, 1, 10, 511}. Below, ulp(r) = 2^(g - 52), and next_up(r) = r + ulp(r).
#[test]
fn square_roots() {
    let mut rng = Rng(7805);
    let mut ms: Vec<u64> = (1..=15).step_by(2).collect();
    ms.extend([99, 255, 4097, (1 << 26) - 1, (1 << 26) + 1, 94_906_265]);
    for _ in 0..8 {
        ms.push(2 * rng.below(47_453_133) + 1);
    }
    for &m in &ms {
        assert!(m % 2 == 1 && m * m < 1 << 53, "{}", m);
        for g in [-510, -100, -1, 0, 1, 10, 511] {
            // m < 2^27 and 2^-536 <= 2^j <= 2^511, so that r is an `f64`, and so is
            // r^2 = m^2 2^(2j), as m^2 < 2^53 and 2^-1020 <= r^2 < 2^1024.
            let r = m as f64 * pow2(g - expo(m as f64));
            let x = r * r;
            assert_eq!(expo(r), g);
            check_root(x, 0.5, "E", r);
            // next_up(x) = x + d with d = 2^(expo(x) - 52) <= 2^(2g - 51), as expo(x) <= 2g + 1,
            // so that r < sqrt(x + d) < r + d / (2r) <= r + 2^(g - 52) = next_up(r), as r >= 2^g.
            check_root(next_up(x), 0.5, "W", r);
            // next_down(x) = x - d' with d' = d, or d' = d / 2 = 2^(2g - 53) for m = 1, where
            // x = 2^(2g). As d' <= 2^-52 x, r - sqrt(x - d') = d' / (r + sqrt(x - d')) <=
            // d' / (2r) (1 + 2^-52). For m = 1, that is 2^(g - 54) (1 + 2^-52) < 2^(g - 53),
            // which is r - next_down(r). For m > 1, r is not a power of 2, so that
            // r - next_down(r) = 2^(g - 52), and r >= 2^(expo(x) / 2) gives
            // d' / (2r) <= 2^(expo(x) / 2 - 53) <= 2^(g - 52) / √2. Either way, sqrt(x - d')
            // lies strictly between next_down(r) and r.
            check_root(next_down(x), 0.5, "W", next_down(r));
            // x^(-1/2) = 1 / r, which is 2^-g for m = 1, and not an `f64` otherwise.
            if m == 1 {
                check_root(x, -0.5, "E", pow2(-g));
            } else {
                check_pow(x, -0.5);
            }
            check_pow(next_up(x), -0.5);
            check_pow(next_down(x), -0.5);
        }
    }
}
