// Tests of the powers of the dyadic kernel at the thresholds of the rules that `pow.rs` applies
// before Ziv's strategy, at the ends of the one that takes an integer y from -2^31 to 2^31 - 1
// to `pown_pos` rather than to the loop of `Pow`, and next to 1, through `check_pow` and
// `check_pown` of `tests.rs`.
//
// Where a bound on a result gives its roundings, the tests also assert them with
// `check_rounding`, so that they check results on every platform, not only against MPFR.

use super::*;
use crate::dyadic::ziv_at;

// ln x for a finite x > 0, through `ln_1p` in [1/2, 2], where x - 1 is exact (Sterbenz's
// lemma), so that the relative error is a few ulps next to 1 too.
fn ln(x: f64) -> f64 {
    if (0.5..=2.0).contains(&x) {
        (x - 1.0).ln_1p()
    } else {
        x.ln()
    }
}

// The `want` of `check_rounding(.., "W", want)` for e^t, from an estimate of t with a relative
// error below 2^-40, where a bound gives it. ln 2^1024 = 709.7827, ln 2^-1074 = -744.4401 and
// ln 2^-1073 = -743.7469 (to 4 places), so that e^t is above 2^1024 for t > 709.8, in
// (0, 2^-1074) for t < -744.5 and in (2^-1074, 2^-1073) for t in (-744.43, -743.76). For
// 0 < |t| < 2^-53, e^t is in (1, 1 + 2^-52) for t > 0, and in (1 - 2^-53, 1) for t < 0, as
// e^t < 1 + 2t and e^t > 1 + t; |t| < 2^-54 leaves room for the error of the estimate.
fn bounded(t: f64) -> Option<f64> {
    if t > 709.8 {
        Some(f64::MAX)
    } else if t < -744.5 {
        Some(0.0)
    } else if t > -744.43 && t < -743.76 {
        Some(pow2(-1074))
    } else if t > 0.0 && t < pow2(-54) {
        Some(1.0)
    } else if t < 0.0 && t > -pow2(-54) {
        Some(1.0 - f64::EPSILON / 2.0)
    } else {
        None
    }
}

// Checks x^y for a finite x > 0 as `check_pow` does, and its roundings where `bounded` gives
// them from y ln x.
fn check_pow_bounded(x: f64, y: f64) {
    check_pow(x, y);
    if let Some(want) = bounded(y * ln(x)) {
        let what = format!("pow({:e}, {:e})", x, y);
        check_rounding(&what, pow(x, y, false), pow(x, y, true), "W", want);
    }
}

// Checks x^n and (-x)^n for a finite x > 0 as `check_pown` does, and their roundings where
// `bounded` gives them from n ln x. (-x)^n = -(x^n) for an odd n, whose roundings are those
// of x^n negated and swapped, so that (-x)^n is in (-next_up(want), -want).
fn check_pown_bounded(x: f64, n: i32) {
    check_pown(x, n);
    check_pown(-x, n);
    if let Some(want) = bounded(f64::from(n) * ln(x)) {
        let what = format!("pown({:e}, {})", x, n);
        check_rounding(&what, pown(x, n, false), pown(x, n, true), "W", want);
        let neg = if n % 2 == 0 { want } else { -next_up(want) };
        let what = format!("pown({:e}, {})", -x, n);
        check_rounding(&what, pown(-x, n, false), pown(-x, n, true), "W", neg);
    }
}

// The x at the ends of the binades of x and of `ln_expo(x)`: for each g at which ilog2(g) or
// ilog2(-g - 1) of `ln_expo` changes, 2^g and the greatest `f64` below 2^(g + 1). In [1/2, 2),
// where `ln_expo` takes expo(x - 1), 1 ± 2^-j and their neighbours away from 1.
fn binade_ends() -> Vec<f64> {
    let mut xs = vec![];
    for j in 0..=10 {
        let p = 1 << j;
        for g in [p - 1, p, -p, -p - 1] {
            if (-1074..=1023).contains(&g) && g != 0 && g != -1 {
                xs.push(pow2(g));
                xs.push(if g == 1023 {
                    f64::MAX
                } else {
                    next_down(pow2(g + 1))
                });
            }
        }
    }
    for j in [1, 2, 3, 10, 26, 51, 52] {
        let x = 1.0 + pow2(-j);
        xs.extend([x, next_down(x)]);
    }
    for j in [1, 2, 3, 10, 26, 52, 53] {
        let x = 1.0 - pow2(-j);
        xs.extend([x, next_up(x), next_down(x)]);
    }
    xs.retain(|&x| x != 1.0);
    xs
}

// The roundings of 2^q for an integer q, as (rounding, want) of `check_rounding`.
fn power_of_two(q: i64) -> (&'static str, f64) {
    if q >= 1024 {
        ("W", f64::MAX)
    } else if q <= -1075 {
        ("W", 0.0)
    } else {
        ("E", pow2(q))
    }
}

// The rules of `pow` at their thresholds, the results next to the overflow and underflow
// thresholds and in the subnormals, and the rules of `pown` at theirs.
#[test]
fn rules_at_thresholds() {
    let xs = binade_ends();
    for &x in &xs {
        // 2^A <= |ln x| < 2^(A + 3), as `ln_expo` says. Each bound holds with a factor of more
        // than 1.38 to spare (2 ln 2 for g >= 1), far above the error of `ln`.
        let a = ln_expo(x);
        let l = ln(x).abs();
        assert!(pow2(a) <= l && l < pow2(a + 3), "ln_expo({:e}) = {}", x, a);
        // `pow` takes |y ln x| >= 2^10 for s = expo(y) + A >= 10, and < 2^-54 for s <= -58,
        // so that y = ±2^(s - A) and its neighbours are on both sides of each threshold.
        for s in [9, 10, -58, -57] {
            for &y in &around(pow2(s - a), 2) {
                check_pow_bounded(x, y);
                check_pow_bounded(x, -y);
            }
        }
        // x^y near 2^q for q at and next to the ends of the range, through y = q / log2 x and
        // its neighbours, whose x^y are on both sides of 2^q.
        for q in [1024.0, 1023.5, -1022.0, -1050.3, -1074.0, -1074.5, -1075.0] {
            for &y in &around(q / x.log2(), 3) {
                check_pow_bounded(x, y);
            }
        }
        // x^n for n next to those at which `pown` takes g n or (g + 1) n beyond 1024 or -1075,
        // for x in [2^g, 2^(g + 1)), and next to the ends of the range.
        let g = expo(x);
        for b in [g, g + 1] {
            for q in [1024, 1023, -1074, -1075] {
                if b != 0 {
                    for n in q / b - 2..=q / b + 2 {
                        if n != 0 {
                            check_pown_bounded(x, i32::try_from(n).unwrap());
                        }
                    }
                }
            }
        }
    }
    // 2^q at x = 2^g and y = q / g where that is an `f64`: an integer, or g = ±2^j.
    for g in (-1074..=1023i64).filter(|&g| g != 0) {
        for q in [1025, 1024, 1023, -1022, -1023, -1074, -1075, -1076] {
            if q % g == 0 || g.unsigned_abs().is_power_of_two() {
                let (x, y) = (pow2(g), q as f64 / g as f64);
                let (rnd, want) = power_of_two(q);
                let what = format!("pow({:e}, {:e})", x, y);
                check_rounding(&what, pow(x, y, false), pow(x, y, true), rnd, want);
                for &y in &around(y, 1) {
                    check_pow_bounded(x, y);
                }
            }
        }
    }
    // x^y for y next to 1 at the ends of the range and in the subnormals. x^1 = x. For a
    // subnormal x = m 2^-1074 with m <= 2^30, x^(1 - 2^-53) = x e^(2^-53 |ln x|) is in
    // (x, x + 2^-1074) and x^(1 + 2^-52) = x e^(-2^-52 |ln x|) in (x - 2^-1074, x), as
    // |ln x| < 745 and m 745 2^-52 < 1. MAX^(1 + 2^-52) = MAX e^(2^-52 ln MAX) is above
    // MAX (1 + 1.5e-13), and so above 2^1024 = MAX / (1 - 2^-53).
    let below_one = next_down(1.0);
    let above_one = next_up(1.0);
    for m in [1, 2, 3, 1000, (1 << 30) - 1, 1 << 30] {
        let x = f64::from_bits(m);
        check_pow(x, below_one);
        check_pow(x, above_one);
        let what = format!("pow({:e}, 1 - 2^-53)", x);
        let (lo, hi) = (pow(x, below_one, false), pow(x, below_one, true));
        check_rounding(&what, lo, hi, "W", x);
        let what = format!("pow({:e}, 1 + 2^-52)", x);
        let (lo, hi) = (pow(x, above_one, false), pow(x, above_one, true));
        check_rounding(&what, lo, hi, "W", next_down(x));
    }
    let (lo, hi) = (
        pow(f64::MAX, above_one, false),
        pow(f64::MAX, above_one, true),
    );
    check_rounding("pow(MAX, 1 + 2^-52)", lo, hi, "W", f64::MAX);
    let ends = [
        f64::from_bits(1),
        f64::from_bits(3),
        f64::from_bits((1 << 30) - 1),
        f64::from_bits((1 << 52) - 1),
        f64::MIN_POSITIVE,
        next_up(f64::MIN_POSITIVE),
        pow2(-1000),
        next_down(f64::MAX),
        f64::MAX,
    ];
    for x in ends {
        let what = format!("pow({:e}, 1)", x);
        check_rounding(&what, pow(x, 1.0, false), pow(x, 1.0, true), "E", x);
        for &y in &around(1.0, 3) {
            check_pow_bounded(x, y);
        }
    }
}

// x^y and x^n for the x next to 1, x = 1 + k 2^-52 and 1 - k 2^-53 with k in 1..=8, where
// |y ln x| reaches 745 only for |y| above 2^58.
#[test]
fn near_one() {
    let (u, h) = (pow2(-52), pow2(-53));
    for k in 1..=8 {
        let k = f64::from(k);
        for x in [1.0 + k * u, 1.0 - k * h] {
            // y = ±t / ln x and its neighbours, so that y ln x is next to ±t: at the overflow
            // and underflow thresholds (e^709.8 is above 2^1024, e^-744.4 in
            // (2^-1074, 2^-1073) and e^-745.2 below 2^-1074), at ±1 and near 0. `bounded`
            // gives the roundings at ±745.2, ±744.4 and ±2^-56, and at 709.8 where y ln x is
            // above it, but not at ±1, -709.8 or ±2^-50, where a y one ulp away moves y ln x
            // across a rounding.
            let l = ln(x);
            for t in [745.2, 744.4, 709.8, 1.0, pow2(-50), pow2(-56)] {
                for &y in &around(t / l, 1) {
                    check_pow_bounded(x, y);
                    check_pow_bounded(x, -y);
                }
            }
            // y = ±2^j with j >= 52, where |y ln x| >= 2^(j - 53): `bounded` gives the
            // roundings for j >= 63, where |y ln x| >= 1024.
            for j in 52..=1023 {
                check_pow_bounded(x, pow2(j));
                check_pow_bounded(x, -pow2(j));
            }
            for n in [i32::MAX, i32::MIN, 1 << 30, -(1 << 30), 1 << 20, -(1 << 20)] {
                check_pown_bounded(x, n);
            }
        }
        // (1 + v)^n for n = ±2^20 and v = k 2^-52 or -k 2^-53 is 1 + n v plus a tail below
        // (n v)^2 = k^2 2^-64 <= 2^-58 in magnitude: positive for n > 0, v > 0 and n < 0,
        // v < 0, where every term is; and positive for the other two, whose terms alternate
        // in sign and decrease from n v. So the result is in (1 + n v, 1 + n v + 2^-58), and
        // 1 + n v and the `f64` after it (2^-53 or 2^-52 later) are its roundings. As n is
        // even, (-x)^n = x^n.
        let n = 1 << 20;
        let cases = [
            (1.0 + k * u, n, 1.0 + k * pow2(-32)),
            (1.0 + k * u, -n, 1.0 - k * pow2(-32)),
            (1.0 - k * h, n, 1.0 - k * pow2(-33)),
            (1.0 - k * h, -n, 1.0 + k * pow2(-33)),
        ];
        for (x, n, want) in cases {
            let y = f64::from(n);
            check_pow(x, y);
            let what = format!("pow({:e}, {})", x, n);
            check_rounding(&what, pow(x, y, false), pow(x, y, true), "W", want);
            for x in [x, -x] {
                let what = format!("pown({:e}, {})", x, n);
                check_rounding(&what, pown(x, n, false), pown(x, n, true), "W", want);
            }
        }
    }
}

// m 2^s in two steps, as 2^1024 is not an `f64`: exact where m 2^(s / 2) and m 2^s are normal.
fn times_pow2(m: f64, s: i64) -> f64 {
    m * pow2(s / 2) * pow2(s - s / 2)
}

// Checks that `d` and `up` are the roundings toward -∞ and toward +∞ of x^n, as pow(x, n),
// pown(x, n) and pown(-x, n), whose roundings for an odd n are -up and -d, and checks the
// three as `check_pow` and `check_pown` do.
fn check_known(x: f64, n: i32, d: f64, up: f64) {
    let y = f64::from(n);
    let what = format!("pow({:e}, {})", x, n);
    let (lo, hi) = (pow(x, y, false), pow(x, y, true));
    check_rounding(&what, lo, hi, "D", d);
    check_rounding(&what, lo, hi, "U", up);
    let neg = if n % 2 == 0 { (d, up) } else { (-up, -d) };
    for (x, (d, up)) in [(x, (d, up)), (-x, neg)] {
        let what = format!("pown({:e}, {})", x, n);
        let (lo, hi) = (pown(x, n, false), pown(x, n, true));
        check_rounding(&what, lo, hi, "D", d);
        check_rounding(&what, lo, hi, "U", up);
        check_pown(x, n);
    }
    check_pow(x, y);
}

// x^n for n = 2 and 3 at x = 2^e (1 + k v), the `f64` k ulps above 2^e for v = 2^-52 and
// below it for v = -2^-53, whose roundings the binomial expansion gives: (1 + k v)^n is
// 1 + n k v + r, where r is above 0, and below the ulp of 1 + n k v (2^-52 for v > 0, 2^-53
// for v < 0) for k up to the K of each family. So 1 + n k v and the `f64` after it, times
// 2^(n e), are the roundings of x^n, for the e at which x and x^n are normal.
#[test]
fn known_roundings() {
    let (u, h) = (pow2(-52), pow2(-53));
    // The largest k at which r is below the ulp, asserted at K and K + 1:
    // (a) n = 2, v > 0: r = k^2 u^2 < u iff k^2 < 2^52;
    // (b) n = 3, v > 0: r = 3 k^2 u^2 + k^3 u^3 < u iff 3 k^2 2^52 + k^3 < 2^104;
    // (c) n = 2, v < 0: r = k^2 h^2 < h iff k^2 < 2^53;
    // (d) n = 3, v < 0: r = 3 k^2 h^2 - k^3 h^3 < h iff 3 k^2 2^53 - k^3 < 2^106,
    // with u = 2^-52 and h = 2^-53. r > 0 in (d) as k h < 3.
    type Holds = fn(u128) -> bool;
    let below: [(u32, Holds); 4] = [
        ((1 << 26) - 1, |k| k * k < 1 << 52),
        (38_745_320, |k| 3 * k * k * (1 << 52) + k * k * k < 1 << 104),
        (94_906_265, |k| k * k < 1 << 53),
        (54_794_158, |k| 3 * k * k * (1 << 53) - k * k * k < 1 << 106),
    ];
    for (big_k, holds) in below {
        let k = u128::from(big_k);
        assert!(holds(k) && !holds(k + 1), "K = {}", big_k);
    }
    // (n, v, the ulp of 1 + n k v, K, and the least and greatest e at which x^n is normal for
    // every k: 2^(n e) (1 + n k v) >= 2^-1022 and 2^(n e) (1 + n k v + r) < 2^1024).
    let families = [
        (2, u, u, below[0].0, -511, 511),
        (3, u, u, below[1].0, -340, 341),
        (2, -h, h, below[2].0, -510, 512),
        (3, -h, h, below[3].0, -340, 341),
    ];
    let mut rng = Rng(7803);
    for (n, v, ulp, big_k, lo, hi) in families {
        // The ends of k and e, and random (k, e).
        let mut cases = vec![];
        for k in [1, 2, 3, 1000, 1 << 20, big_k - 1, big_k] {
            for e in [lo, lo + 1, -1, 0, 1, hi - 1, hi] {
                cases.push((k, e));
            }
        }
        for _ in 0..1000 {
            let k = u32::try_from(rng.below(u64::from(big_k))).unwrap() + 1;
            let e = lo + i64::try_from(rng.below(u64::try_from(hi - lo + 1).unwrap())).unwrap();
            cases.push((k, e));
        }
        for (k, e) in cases {
            let k = f64::from(k);
            let d = 1.0 + f64::from(n) * k * v;
            let x = times_pow2(1.0 + k * v, e);
            let s = i64::from(n) * e;
            check_known(x, n, times_pow2(d, s), times_pow2(d + ulp, s));
        }
    }
    // At k = 2^26 in (a), r = 2^-52 is the ulp, so that x^2 = 2^(2 e) (1 + (2 k + 1) 2^-52).
    let k = pow2(26);
    for e in [-511, -1, 0, 1, 511] {
        let x = times_pow2(1.0 + k * u, e);
        let want = times_pow2(1.0 + (2.0 * k + 1.0) * u, 2 * e);
        check_known(x, 2, want, want);
    }
}

// Whether `pow` takes a finite y to `pown_pos` after its rules and `exact`, by the test of
// `pow.rs`: `y as i32` saturates, so that only an integer y from -2^31 to 2^31 - 1 passes.
fn routed(y: f64) -> bool {
    f64::from(y as i32) == y
}

// x^y for integers y up to the ends of the route and past them: on every platform, `pow` gives
// what `pown` gives wherever the test of the route passes, whether the route, `exact` or a rule
// settles the arguments, and where the tests have MPFR, what MPFR gives at every y.
#[test]
fn integer_route() {
    // The ends of the route pass the test, and the integers next to them outside it fail it,
    // as 1/2 does.
    assert!(routed(2147483647.0) && routed(-2147483648.0));
    for y in [2147483648.0, 2147483649.0, -2147483649.0, 0.5] {
        assert!(!routed(y), "{:e} passes", y);
    }
    // y = ±(2^j - 1), ±2^j and ±(2^j + 1) for j up to 31, at and next to each power of two,
    // so that binary powering squares from 0 to 31 times. Of those at and next to the ends of
    // the route, where neither a rule nor `exact` settles x^y, 2^31 - 1, -(2^31 - 1) and -2^31
    // take it, and 2^31, 2^31 + 1 and -2^31 - 1 the loop of `Pow`.
    let mut ys = vec![];
    for j in 0..=31 {
        let p = pow2(j);
        for y in [p - 1.0, p, p + 1.0] {
            if y != 0.0 {
                ys.extend([y, -y]);
            }
        }
    }
    let (u, h) = (pow2(-52), pow2(-53));
    // x at k ulps from 1, where |y ln x| < 2^-17 for every |y| < 2^32, so that no rule
    // settles x^y, nor `exact` but at y = 1, and binary powering squares up to 31 times. 1/2
    // and 2, whose x^y = 2^±y `exact` settles where it is an `f64`, so that the route takes
    // only the y at which it is at least 2^1024 or below 2^-1074. 3 and 1.5, whose x^y is an
    // `f64` only for y from 0 to 33 (3^33 < 2^53 < 3^34), so that the route takes every other
    // y below the bound of the rule s >= 10 of `pow` (|y| = 2^11 for 3 and 2^12 for 1.5),
    // past the overflow and underflow thresholds too.
    let mut xs = vec![0.5, 2.0, 3.0, 1.5];
    for k in 1..=4 {
        let k = f64::from(k);
        xs.extend([1.0 + k * u, 1.0 - k * h]);
    }
    // And x = 2^(q / y), at which x^y is next to 2^q where x is normal: below 2^-1074 and at
    // it, at the least normal `f64`, below 2^1024, and between. x is +∞ for y = -1 and
    // q <= -1074, where the rules of both functions give 0.
    let qs = [
        -1074.5, -1074.0, -1022.0, -500.0, -1.0, 1.0, 500.0, 1023.0, 1023.9,
    ];
    for &y in &ys {
        let near = qs.iter().map(|q| (q / y).exp2());
        for x in xs.iter().copied().chain(near) {
            if routed(y) {
                for up in [false, true] {
                    let (a, b) = (pow(x, y, up), pown(x, y as i32, up));
                    assert!(
                        a.to_bits() == b.to_bits(),
                        "pow({:e}, {:e}) = {:e} but pown gives {:e}, up = {}",
                        x,
                        y,
                        a,
                        b,
                        up
                    );
                }
            }
            check_pow(x, y);
        }
    }
}

// x^34 at x = 3: 3^34 = 16677181699666569 is above 2^53, so that `exact` leaves pow(3, 34) to
// the route, and odd, so that it is the midpoint of the `f64`s 16677181699666568 and
// 16677181699666570 (2 apart there), its roundings toward -∞ and toward +∞. Binary powering
// takes the products 3^2, 3^4, 3^8, 3^16, 3^32 and 3^2 3^32, each below 2^64 and so exact at
// one limb, where `ziv_at` then settles both directions.
#[test]
fn three_to_the_34() {
    let (d, u) = (16677181699666568.0, 16677181699666570.0);
    check_known(3.0, 34, d, u);
    for (up, want) in [(false, d), (true, u)] {
        let r = ziv_at::<1, _>(&Pown(3.0, 34), up);
        assert_eq!(r, Some(want), "3^34 at one limb, up = {}", up);
    }
}
